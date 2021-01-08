use codec::{Decode, Encode};
use core::fmt::Debug;
use frame_support::{
	decl_error, decl_module, decl_storage,
	dispatch::DispatchError,
	ensure,
	traits::{Currency, ExistenceRequirement, Get, Time, WithdrawReason},
	weights::Weight,
};
use frame_system::{ensure_root, ensure_signed};
use sp_core::U256;
use sp_io::hashing::keccak_256;
use sp_runtime::{traits::Verify, AccountId32, MultiSignature};
use sp_std::convert::TryFrom;

mod default_weights;

pub trait WeightInfo {
	fn deposit_escrow() -> Weight;
	fn deposit_penalty() -> Weight;
	fn unlock_deposits() -> Weight;
	fn lock_deposits() -> Weight;
	fn withdraw() -> Weight;
	fn withdraw_to() -> Weight;
	fn redeem() -> Weight;
	fn set_unlock_duration() -> Weight;
}

pub trait Trait: frame_system::Trait {
	type Currency: Currency<Self::AccountId>;
	type WeightInfo: WeightInfo;
	type Time: Time;
}

type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;
type TicketOf<T> = Ticket<<T as frame_system::Trait>::AccountId, BalanceOf<T>, Timestamp<T>>;
type Timestamp<T> = <<T as Trait>::Time as Time>::Moment;

#[derive(Encode, Decode, Clone, Eq, PartialEq, Debug, Default)]
pub struct Deposit<Balance, Timestamp> {
	/// Balance of a user's escrow
	pub escrow: Balance,
	/// Balance of a user's penalty
	pub penalty: Balance,

	/// Block number at which the user can withdraw their balance
	pub unlock_at: Timestamp,
}

#[derive(Encode, Decode, Clone, Eq, PartialEq, Debug)]
pub struct Ticket<AccountId, Balance, Timestamp> {
	/// Adress of the ticket sender
	pub sender: AccountId,
	/// Adress of the ticket receiver
	pub receiver: AccountId,
	/// The value of a winning ticket
	pub face_value: Balance,
	/// The chance of a winning ticket
	pub win_prob: U256,
	/// The time that the ticket is valid until
	pub expiration: Timestamp,
	/// Hash of receiver's random value
	pub receiver_rand_hash: [u8; 32],
	/// Sender's ticket counter
	pub sender_nonce: u32,
}

decl_error! {
	pub enum Error for Module<T: Trait> {
		/// Cannot deposit while unlocking
		DepositWhileUnlocking,
		/// There is nothing to withdraw
		NothingToWithdraw,
		/// Unlock already in progress
		UnlockAlreadyInProgress,
		/// Not unlocking, cannot lock
		NotUnlocking,
		/// The deposit is not unlocked
		DepositNotUnlocked,
		/// The unlock period is not yet complete
		UnlockPeriodNotComplete,
		/// Ticket has expired
		ExpiredTicket,
		/// Ticket has already been redeemed
		TicketAlreadyRedeemed,
		/// Hash of receiver_rand doesn't match receiver_rand_hash
		HashesDontMatch,
		/// Ticket doesn't have a valid signature
		InvalidSignature,
		/// Ticket is not a winning one
		TicketNotAWinner,
		/// Ticket sender has insufficient funds to pay out
		InsufficientFunds,
	}
}

decl_storage! {
	trait Store for Module<T: Trait> as SyloTicketing {
		/// Mapping of user deposits to their address
		pub Deposits get(fn deposits): map hasher(blake2_128_concat) T::AccountId => Deposit<BalanceOf<T>, Timestamp<T>>;

		/// Mapping of ticket hashes, used to check if a ticket has been redeemed
		pub UsedTickets get(fn used_tickets): map hasher(blake2_128_concat) [u8; 32] => bool;

		/// The unlock duration that a user is required to wait after unlocking their deposit til they can withdraw them
		pub UnlockDuration get(fn unlock_duration): <<T as Trait>::Time as Time>::Moment = (7 * 24 * 60 * 60 * 1_000u32).into();
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		#[weight = T::WeightInfo::deposit_escrow()]
		pub fn deposit_escrow(origin, amount: BalanceOf<T>) {
			let account = ensure_signed(origin)?;
			let mut deposit = <Deposits<T>>::get(&account);
			ensure!(deposit.unlock_at == (0 as u32).into(), Error::<T>::DepositWhileUnlocking);

			T::Currency::withdraw(&account, amount, WithdrawReason::Fee.into(), ExistenceRequirement::KeepAlive)?;
			deposit.escrow += amount;
			<Deposits<T>>::insert(&account, deposit);
		}

		#[weight = T::WeightInfo::deposit_penalty()]
		pub fn deposit_penalty(origin, amount: BalanceOf<T>) {
			let account = ensure_signed(origin)?;
			let mut deposit = <Deposits<T>>::get(&account);
			ensure!(deposit.unlock_at == (0 as u32).into(), Error::<T>::DepositWhileUnlocking);

			T::Currency::withdraw(&account, amount, WithdrawReason::Fee.into(), ExistenceRequirement::KeepAlive)?;
			deposit.penalty += amount;
			<Deposits<T>>::insert(&account, deposit);
		}

		#[weight = T::WeightInfo::unlock_deposits()]
		pub fn unlock_deposits(origin) {
			let account = ensure_signed(origin)?;
			let mut deposit = <Deposits<T>>::get(&account);
			ensure!(deposit.escrow > (0 as u32).into() || deposit.penalty > (0 as u32).into(), Error::<T>::NothingToWithdraw);
			ensure!(deposit.unlock_at == (0 as u32).into(), Error::<T>::UnlockAlreadyInProgress);

			deposit.unlock_at = T::Time::now() + <UnlockDuration<T>>::get();
			<Deposits<T>>::insert(&account, deposit)
		}

		#[weight = T::WeightInfo::lock_deposits()]
		pub fn lock_deposits(origin) {
			let account = ensure_signed(origin)?;
			let mut deposit = <Deposits<T>>::get(&account);
			ensure!(deposit.unlock_at != (0 as u32).into(), Error::<T>::NotUnlocking);

			deposit.unlock_at = (0 as u32).into();
			<Deposits<T>>::insert(account, deposit)
		}

		#[weight = T::WeightInfo::withdraw()]
		pub fn withdraw(origin) {
			let account = ensure_signed(origin)?;
			withdraw_to::<T>(account)?;
		}

		/// Complete the withdrawal process and remove the assets
		#[weight = T::WeightInfo::withdraw_to()]
		pub fn withdraw_to(origin, account: T::AccountId) {
			let _ = ensure_signed(origin)?;
			withdraw_to::<T>(account)?;
		}

		#[weight = T::WeightInfo::redeem()]
		pub fn redeem(origin, ticket: Ticket<<T as frame_system::Trait>::AccountId, BalanceOf<T>, Timestamp<T>>, receiver_rand: U256, sig: MultiSignature) {
			let _ = ensure_signed(origin)?;
			let hash = get_ticket_hash::<T>(&ticket);
			ensure_valid_winning_ticket::<T>(&ticket, &hash, receiver_rand, sig)?;

			let mut deposit = <Deposits<T>>::get(&ticket.sender);

			ensure!(deposit.escrow + deposit.penalty >= ticket.face_value, Error::<T>::InsufficientFunds);

			UsedTickets::insert(&hash, true);

			if ticket.face_value > deposit.escrow {
				let penalty_amount = ticket.face_value - deposit.escrow;
				deposit.escrow = (0 as u32).into();
				deposit.penalty -= penalty_amount;
			} else {
				deposit.escrow = deposit.escrow - ticket.face_value;
			}

			T::Currency::deposit_into_existing(&ticket.receiver, ticket.face_value)?;
			<Deposits<T>>::insert(&ticket.sender, deposit);
		}

		#[weight = T::WeightInfo::set_unlock_duration()]
		pub fn set_unlock_duration(origin, unlock_duration: <<T as Trait>::Time as Time>::Moment) {
			ensure_root(origin)?;
			<UnlockDuration<T>>::put(unlock_duration)
		}
	}
}

fn withdraw_to<T: Trait>(account: T::AccountId) -> Result<(), DispatchError> {
	let mut deposit = <Deposits<T>>::get(&account);
	ensure!(deposit.unlock_at > (0 as u32).into(), Error::<T>::DepositNotUnlocked);
	ensure!(deposit.unlock_at < T::Time::now(), Error::<T>::UnlockPeriodNotComplete);

	let amount: BalanceOf<T> = deposit.escrow + deposit.penalty;

	// Set values to 0
	deposit.escrow = (0 as u32).into();
	deposit.penalty = (0 as u32).into();

	// Relock so if more funds are deposited they may be unlocked again
	deposit.unlock_at = (0 as u32).into();

	T::Currency::deposit_into_existing(&account, amount)?;
	<Deposits<T>>::insert(&account, deposit);
	Ok(())
}

pub fn get_ticket_hash<T: Trait>(ticket: &TicketOf<T>) -> [u8; 32] {
	keccak_256(ticket.encode().as_ref())
}

pub fn ensure_valid_winning_ticket<T: Trait>(
	ticket: &TicketOf<T>,
	ticket_hash: &[u8; 32],
	receiver_rand: U256,
	sig: MultiSignature,
) -> Result<(), DispatchError> {
	ensure!(
		ticket.expiration == (0 as u32).into() || ticket.expiration >= T::Time::now(),
		Error::<T>::ExpiredTicket
	);
	ensure!(!UsedTickets::get(ticket_hash), Error::<T>::TicketAlreadyRedeemed);
	ensure!(
		keccak_256(receiver_rand.encode().as_ref()) == ticket.receiver_rand_hash,
		Error::<T>::HashesDontMatch
	);

	// Verify that the signature given is from the ticket sender
	ensure!(
		is_valid_signature::<T>(&sig, ticket_hash, &ticket.sender),
		Error::<T>::InvalidSignature
	);
	// Check if the ticket is a winning ticket
	ensure!(
		U256::from_big_endian(&keccak_256((sig, receiver_rand).encode().as_ref())) < ticket.win_prob,
		Error::<T>::TicketNotAWinner
	);

	Ok(())
}

pub fn is_valid_signature<T: Trait>(sig: &MultiSignature, ticket_hash: &[u8], account: &T::AccountId) -> bool {
	if let Ok(account_id) = AccountId32::try_from(account.encode().as_ref()) {
		return sig.verify(ticket_hash, &account_id);
	}
	false
}

#[cfg(test)]
mod test {
	use super::*;
	use crate::mock::Test as MockTest;
	use frame_support::{impl_outer_origin, parameter_types};
	use pallet_balances::Module as BalanceModule;
	use pallet_timestamp::Module as TimeModule;
	use sp_core::{crypto::AccountId32, ecdsa, ed25519, sr25519, Pair};
	use sp_runtime::{traits::IdentifyAccount, MultiSigner};

	#[derive(Clone, Eq, PartialEq)]
	pub struct Test;

	macro_rules! copy_type_def {
		($type_ident:ident) => {
			type $type_ident = <MockTest as frame_system::Trait>::$type_ident;
		};
	}

	impl frame_system::Trait for Test {
		type AccountId = AccountId32;
		type Origin = Origin;
		type Lookup = sp_runtime::traits::IdentityLookup<Self::AccountId>;
		copy_type_def!(BaseCallFilter);
		copy_type_def!(Index);
		copy_type_def!(BlockNumber);
		copy_type_def!(Hash);
		copy_type_def!(Hashing);
		copy_type_def!(Header);
		copy_type_def!(Event);
		copy_type_def!(BlockHashCount);
		copy_type_def!(MaximumBlockWeight);
		copy_type_def!(DbWeight);
		copy_type_def!(BlockExecutionWeight);
		copy_type_def!(Call);
		copy_type_def!(ExtrinsicBaseWeight);
		copy_type_def!(MaximumExtrinsicWeight);
		copy_type_def!(MaximumBlockLength);
		copy_type_def!(AvailableBlockRatio);
		copy_type_def!(Version);
		copy_type_def!(PalletInfo);
		copy_type_def!(AccountData);
		copy_type_def!(OnNewAccount);
		copy_type_def!(OnKilledAccount);
		copy_type_def!(SystemWeightInfo);
	}

	impl_outer_origin! {
		pub enum Origin for Test where system = frame_system {}
	}

	impl Trait for Test {
		type Currency = BalanceModule<Test>;
		type WeightInfo = ();
		type Time = TimeModule<Test>;
	}

	parameter_types! {
		pub const ExistentialDeposit: u64 = 1;
		pub const MinimumPeriod: u64 = 5;
	}
	impl pallet_balances::Trait for Test {
		type Balance = u64;
		type Event = <Self as frame_system::Trait>::Event;
		type DustRemoval = ();
		type ExistentialDeposit = ExistentialDeposit;
		type AccountStore = frame_system::Module<Self>;
		type MaxLocks = ();
		type WeightInfo = ();
	}
	impl pallet_timestamp::Trait for Test {
		type Moment = u64;
		type OnTimestampSet = ();
		type MinimumPeriod = MinimumPeriod;
		type WeightInfo = ();
	}

	type Ticketing = Module<Test>;
	type Balance = BalanceModule<Test>;
	type Time = TimeModule<Test>;

	fn alice() -> AccountId32 {
		<ed25519::Pair as Pair>::from_string("//Alice", None)
			.expect("Could not create Alice keychain pair")
			.public()
			.into()
	}

	fn bob() -> AccountId32 {
		<ed25519::Pair as Pair>::from_string("//Bob", None)
			.expect("Could not create Bob keychain pair")
			.public()
			.into()
	}

	fn execute<F: Fn()>(execute: F) {
		sp_io::TestExternalities::from(frame_system::GenesisConfig::default().build_storage::<Test>().unwrap())
			.execute_with(execute)
	}

	#[test]
	pub fn test_deposit_into_escrow() {
		let alice = alice();
		execute(|| {
			// Alice has an initial balance of 1000
			Balance::make_free_balance_be(&alice, 1_000);

			// Deposit 100 into the escrow
			Ticketing::deposit_escrow(Origin::signed(alice.clone()), 100).expect("Failed to deposit into escrow");

			assert_eq!(Balance::free_balance(alice.clone()), 900);
			assert_eq!(<Deposits<Test>>::get(alice.clone()).escrow, 100);
		})
	}

	#[test]
	pub fn test_deposit_into_escrow_not_enough_balance() {
		let alice = alice();
		execute(|| {
			// Alice has an initial balance of 1000
			Balance::make_free_balance_be(&alice, 1_000);

			// Try depositing 10,000 into the escrow
			Ticketing::deposit_escrow(Origin::signed(alice.clone()), 10_000)
				.expect_err("There shouldn't have been enough funds in the balance");

			// Ensure nothing has been changed
			assert_eq!(Balance::free_balance(alice.clone()), 1_000);
			assert_eq!(<Deposits<Test>>::get(alice.clone()).escrow, 0);
		})
	}

	#[test]
	pub fn test_deposit_into_penalty() {
		let alice = alice();
		execute(|| {
			// Alice has an initial balance of 1000
			Balance::make_free_balance_be(&alice, 1_000);

			// Deposit 100 into the penalty
			Ticketing::deposit_penalty(Origin::signed(alice.clone()), 100).expect("Failed to deposit into penalty");

			assert_eq!(Balance::free_balance(alice.clone()), 900);
			assert_eq!(<Deposits<Test>>::get(alice.clone()).penalty, 100);
		})
	}

	#[test]
	pub fn test_deposit_into_penalty_not_enough_balance() {
		let alice = alice();
		execute(|| {
			// Alice has an initial balance of 1,000
			Balance::make_free_balance_be(&alice, 1_000);

			// Try depositing 10,000 into the escrow
			Ticketing::deposit_penalty(Origin::signed(alice.clone()), 10_000)
				.expect_err("There shouldn't have been enough funds in the balance");

			// Ensure nothing has been changed
			assert_eq!(Balance::free_balance(alice.clone()), 1_000);
			assert_eq!(<Deposits<Test>>::get(alice.clone()).penalty, 0);
		})
	}

	#[test]
	pub fn test_unlock_deposits_and_withdraw() {
		let alice = alice();
		execute(|| {
			// We'd almost never start at 0
			Time::set_timestamp(1_000);

			// Alice now has a balance of 800, 150 in the escrow, and 50 in the penalty
			setup_deposit();

			// The deposit should be locked
			assert_eq!(<Deposits<Test>>::get(alice.clone()).unlock_at, 0);

			// We now wish to unlock these deposits
			Ticketing::unlock_deposits(Origin::signed(alice.clone())).expect("Failed to unlock the deposit");
			// The unlock period is now set to Now + UnlockDuration
			assert_eq!(
				<Deposits<Test>>::get(alice.clone()).unlock_at - Time::now(),
				<UnlockDuration<Test>>::get()
			);

			// Move 1,000 after the unlock duration
			Time::set_timestamp((1_000 + <UnlockDuration<Test>>::get() + 1_000).into());

			Ticketing::withdraw(Origin::signed(alice.clone())).expect("Failed to withdraw funds from deposit");

			assert_eq!(Balance::free_balance(alice.clone()), 1_000);
			let deposit = <Deposits<Test>>::get(alice.clone());
			assert_eq!(deposit.escrow, 0);
			assert_eq!(deposit.penalty, 0);
		})
	}

	#[test]
	pub fn test_unlock_deposits_and_withdraw_early() {
		let alice = alice();
		execute(|| {
			Time::set_timestamp(1_000);
			setup_deposit();
			Ticketing::unlock_deposits(Origin::signed(alice.clone())).expect("Failed to unlock the deposit");
			Time::set_timestamp(2_000);

			Ticketing::withdraw(Origin::signed(alice.clone()))
				.expect_err("Funds should not be withdrawable until the unlock duration has passed");

			// Nothing should have changed
			let deposit = <Deposits<Test>>::get(alice.clone());
			assert_eq!(deposit.escrow, 150);
			assert_eq!(deposit.penalty, 50);
			assert_eq!(Balance::free_balance(alice.clone()), 800);
		})
	}

	#[test]
	pub fn test_unlock_deposit_twice() {
		let alice = alice();
		execute(|| {
			Time::set_timestamp(1_000);
			setup_deposit();

			Ticketing::unlock_deposits(Origin::signed(alice.clone())).expect("Failed to unlock deposit");
			Ticketing::unlock_deposits(Origin::signed(alice.clone()))
				.expect_err("Should not be able to unlock deposits twice");
		})
	}

	#[test]
	pub fn test_lock_deposit() {
		let alice = alice();
		execute(|| {
			Time::set_timestamp(1_000);
			setup_deposit();

			Ticketing::unlock_deposits(Origin::signed(alice.clone())).expect("Failed to unlock deposit");
			Time::set_timestamp(2_000);
			Ticketing::lock_deposits(Origin::signed(alice.clone())).expect("Failed to lock deposit");

			assert_eq!(<Deposits<Test>>::get(alice.clone()).unlock_at, 0);
		})
	}

	fn setup_deposit() {
		let alice = alice();
		// Alice has an iniital balance of 1,000
		Balance::make_free_balance_be(&alice, 1_000);
		// 150 is deposited into the escrow and 50 into the penalty
		Ticketing::deposit_escrow(Origin::signed(alice.clone()), 150).expect("Failed to deposit into the escrow");
		Ticketing::deposit_penalty(Origin::signed(alice.clone()), 50).expect("Failed to deposit into the penalty");
	}

	#[test]
	fn test_redeem_ed25519() {
		let keychain = <ed25519::Pair as Pair>::from_string("//Alice", None)
			.expect("Could not create ED25519 Alice keychain pair");
		test_redeem(keychain.public(), keychain);
	}

	// // This test is not deterministic as SR25519 produces non-deterministic signatures.
	// // Therefore it fails randomly and so is not included as part of the test suite.
	// #[test]
	// fn test_redeem_sr25519() {
	// 	let keychain = <sr25519::Pair as Pair>::from_string("//Alice", None)
	// 		.expect("Could not create SR25519 Alice keychain pair");
	// 	test_redeem(keychain.public(), keychain);
	// }

	#[test]
	fn test_redeem_ecdsa() {
		let keychain =
			<ecdsa::Pair as Pair>::from_string("//Alice", None).expect("Could not create ECDSA Alice keychain pair");
		test_redeem(MultiSigner::from(keychain.public()).into_account(), keychain);
	}

	fn test_redeem<A, P>(sender: A, sender_pair: P)
	where
		A: Into<AccountId32>,
		P: Pair,
		P::Signature: Into<MultiSignature>,
	{
		test_redeem_with(
			sender,
			sender_pair,
			None,
			|sender, receiver| {
				// 150 into escrow, 50 into penalty, 800 left in balance
				Balance::make_free_balance_be(&sender, 1_000);
				Ticketing::deposit_escrow(Origin::signed(sender.clone()), 150)
					.expect("Failed to deposit into the escrow");
				Ticketing::deposit_penalty(Origin::signed(sender.clone()), 50)
					.expect("Failed to deposit into the penalty");
				// Bob also gets 1,000
				Balance::make_free_balance_be(&receiver, 1_000);
			},
			|result, sender, receiver| {
				result.expect("The ticket should have won");

				let deposit = <Deposits<Test>>::get(&sender);
				assert_eq!(deposit.escrow, 50);
				assert_eq!(deposit.penalty, 50);
				assert_eq!(Balance::free_balance(&receiver), 1_100);
			},
		)
	}

	#[test]
	fn test_redeem_insufficient_funds() {
		let keychain = <ed25519::Pair as Pair>::from_string("//Alice", None)
			.expect("Could not create ED25519 Alice keychain pair");
		let alice: AccountId32 = keychain.public().into();

		test_redeem_with(
			alice,
			keychain,
			None,
			|alice, bob| {
				Balance::make_free_balance_be(&alice, 1_000);
				Ticketing::deposit_escrow(Origin::signed(alice.clone()), 10).expect("Could not deposit into escrow");
				Ticketing::deposit_penalty(Origin::signed(alice.clone()), 5).expect("Could not deposit into penalty");
				Balance::make_free_balance_be(&bob, 1_000);
			},
			|result, _, _| {
				result.expect_err("Alice doesn't have enough in the deposits");
			},
		);
	}

	#[test]
	fn test_redeem_funds_taken_from_penalty() {
		let keychain = <ed25519::Pair as Pair>::from_string("//Alice", None)
			.expect("Could not create ED25519 Alice keychain pair");
		let alice: AccountId32 = keychain.public().into();

		test_redeem_with(
			alice,
			keychain,
			None,
			|alice, bob| {
				Balance::make_free_balance_be(&alice, 1_000);
				Ticketing::deposit_escrow(Origin::signed(alice.clone()), 50).expect("Could not deposit into escrow");
				Ticketing::deposit_penalty(Origin::signed(alice.clone()), 100).expect("Could not deposit into penalty");
				Balance::make_free_balance_be(&bob, 1_000);
			},
			|result, sender, receiver| {
				result.expect("Ticket should have been redeemed");
				let deposit = <Deposits<Test>>::get(&sender);
				assert_eq!(Balance::free_balance(&receiver), 1_100);
				assert_eq!(deposit.escrow, 0);
				assert_eq!(deposit.penalty, 50);
			},
		);
	}

	#[test]
	fn test_redeem_losing_ticket() {
		let keychain = <ed25519::Pair as Pair>::from_string("//Alice", None)
			.expect("Could not create ED25519 Alice keychain pair");
		let alice: AccountId32 = keychain.public().into();

		// Winning probability is 10%
		test_redeem_with(
			alice,
			keychain,
			Some(U256::max_value() / 10),
			|alice, _| {
				Balance::make_free_balance_be(&alice, 1_000);
				Ticketing::deposit_escrow(Origin::signed(alice.clone()), 100).expect("Couldn't deposit into escrow");
				Ticketing::deposit_penalty(Origin::signed(alice.clone()), 50).expect("Couldn't deposit into penalty");
			},
			|result, _, bob| {
				result.expect_err("This is meant to be a losing ticket");
				assert_eq!(Balance::free_balance(&bob), 0);
			},
		)
	}

	/// Test the ticket redemption process.
	///
	/// Uses the setup and result handling hooks provided.
	/// The ticket will have the winning probability specified or 80% if it isn't specified.
	fn test_redeem_with<A, P, S, R>(
		sender: A,
		sender_pair: P,
		win_prob: Option<U256>,
		setup_function: S,
		result_handle: R,
	) where
		A: Into<AccountId32>,
		P: Pair,
		P::Signature: Into<MultiSignature>,
		S: Fn(AccountId32, AccountId32),
		R: Fn(Result<(), DispatchError>, AccountId32, AccountId32),
	{
		let sender = sender.into();
		let bob = bob();

		execute(|| {
			Time::set_timestamp(1_000);

			setup_function(sender.clone(), bob.clone());

			let receiver_rand = U256::from(1234);
			let receiver_rand_hash = keccak_256(receiver_rand.encode().as_ref());
			let ticket = Ticket {
				sender: sender.clone(),
				receiver: bob.clone(),
				face_value: 100,
				win_prob: win_prob.unwrap_or_else(|| U256::max_value() / 100 * 80),
				expiration: 2_000,
				receiver_rand_hash,
				sender_nonce: 111,
			};
			let ticket_hash = keccak_256(ticket.encode().as_ref());
			let sig = sender_pair.sign(&ticket_hash).into();
			let result = Ticketing::redeem(Origin::signed(bob.clone()), ticket, receiver_rand, sig);

			result_handle(result, sender.clone(), bob.clone());
		})
	}

	#[test]
	fn test_redeem_twice() {
		let keychain = <ed25519::Pair as Pair>::from_string("//Alice", None)
			.expect("Could not create ED25519 Alice keychain pair");
		let alice: AccountId32 = keychain.public().into();
		let bob = bob();
		execute(|| {
			Time::set_timestamp(1_000);

			Balance::make_free_balance_be(&alice, 1_000);
			Ticketing::deposit_escrow(Origin::signed(alice.clone()), 150).expect("Failed to deposit into the escrow");
			Ticketing::deposit_penalty(Origin::signed(alice.clone()), 50).expect("Failed to deposit into the penalty");
			Balance::make_free_balance_be(&bob, 1_000);

			let receiver_rand = U256::from(1234);
			let receiver_rand_hash = keccak_256(receiver_rand.encode().as_ref());
			let ticket = Ticket {
				sender: alice.clone(),
				receiver: bob.clone(),
				face_value: 100,
				win_prob: U256::max_value() / 100 * 80,
				expiration: 2_000,
				receiver_rand_hash,
				sender_nonce: 111,
			};
			let ticket_hash = keccak_256(ticket.encode().as_ref());
			let sig: MultiSignature = keychain.sign(&ticket_hash).into();

			Ticketing::redeem(Origin::signed(bob.clone()), ticket.clone(), receiver_rand, sig.clone())
				.expect("Ticket should have been a winning ticket");

			Time::set_timestamp(1_500);

			Ticketing::redeem(Origin::signed(bob.clone()), ticket, receiver_rand, sig)
				.expect_err("This ticket cannot be redeemed twice");
		})
	}

	#[test]
	fn test_redeem_invalid_signature() {
		let keychain1 = <ed25519::Pair as Pair>::from_string("//Alice", None)
			.expect("Could not create ED25519 Alice keychain pair");
		let alice: AccountId32 = keychain1.public().into();
		let keychain2 =
			<ed25519::Pair as Pair>::from_string("//Bob", None).expect("Could not create ED25519 Alice keychain pair");
		let bob: AccountId32 = keychain2.public().into();

		execute(|| {
			Time::set_timestamp(1_000);

			Balance::make_free_balance_be(&alice, 1_000);
			Ticketing::deposit_escrow(Origin::signed(alice.clone()), 150).expect("Failed to deposit into the escrow");
			Ticketing::deposit_penalty(Origin::signed(alice.clone()), 50).expect("Failed to deposit into the penalty");
			Balance::make_free_balance_be(&bob, 1_000);

			let receiver_rand = U256::from(1234);
			let receiver_rand_hash = keccak_256(receiver_rand.encode().as_ref());
			let ticket = Ticket {
				sender: alice.clone(),
				receiver: bob.clone(),
				face_value: 100,
				win_prob: U256::max_value() / 100 * 80,
				expiration: 2_000,
				receiver_rand_hash,
				sender_nonce: 111,
			};
			let ticket_hash = keccak_256(ticket.encode().as_ref());
			let sig: MultiSignature = keychain2.sign(&ticket_hash).into(); // The receiver should not be signing the message

			Ticketing::redeem(Origin::signed(bob.clone()), ticket.clone(), receiver_rand, sig.clone())
				.expect_err("Ticket should have had the wrong signature");
		})
	}
}
