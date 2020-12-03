use frame_support::{decl_error, decl_module, decl_storage, ensure, traits::{WithdrawReason, Currency, ExistenceRequirement, Time}};
use frame_system::ensure_signed;
use codec::{Decode, Encode};
use sp_io::hashing::{keccak_256};
use sp_core::U256;
use sp_runtime::{DispatchError};

// TODO: set this to a sensible value
const UNLOCK_DURATION: u32 = 0;

type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;
type Timestamp<T> = <<T as Trait>::Time as Time>::Moment;
type Hash = [u8; 32];

#[derive(Encode, Decode, Default, Debug)]
pub struct Stake<AccountId, Balance> {
	amount : Balance , // Amount of the stake

    left_amount: Balance, // Value of the stake on left branch
	right_amount: Balance, // Value of the stake on the right branch
	
	stakee: AccountId, // Address of peer that offers sevices

    parent: Hash, // Hash of parent 
    left : Hash, // Hash of left child 
    right : Hash, // Hash of right child 
}

#[derive(Encode, Decode, Default, Debug)]
pub struct Unlock<Balance, Timestamp> {
	amount: Balance, // Amount of stake unlocking
    unlock_at: Timestamp, // Block number stake becomes withdrawable
}

decl_storage! {
	trait Store for Module<T: Trait> as SyloDirectory {
		// Stakers (map hash -> stake)
		pub Stakes get(fn stakes): map hasher(blake2_128_concat) Hash => Stake<T::AccountId, BalanceOf<T>>;

		// Stakees (map accountid -> balance)
		pub Stakees get(fn stakees): map hasher(blake2_128_concat) T::AccountId => BalanceOf<T>;

		// Unlockings (map hash -> unlock)
		pub Unlockings get(fn unlockings): map hasher(blake2_128_concat) Hash => Unlock<BalanceOf<T>, Timestamp<T>>;
		
		// Root (hash)
		pub Root get(fn root): Hash;
	}
}

pub trait Trait: frame_system::Trait {
    type Currency: Currency<Self::AccountId>;
    type Time: Time;
    //type WeightInfo: WeightInfo;
}

decl_error! {
	pub enum Error for Module<T: Trait> {
		/// An address must stake above zero tokens
		ZeroStake,
		/// Cannot re-stake while funds are unlocking
		StakeWhileUnlocking,
		/// Only one stake allowed per address
		AlreadyStaking,
		/// The address is not staking
		NotStaking,
		/// The unlock period has not been exhausted
		UnlockPeriodNonExhasted,
		/// Attempt to unlock more than what is staking
		InsufficientStakeBalance,
		/// Nonexisting key
		KeyDoesNotExist,
		/// Unlock amount insuffient to the amount you're trying to relock
		RelockAmount,
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin, system = frame_system {

		// Add a stake to the directory
		#[weight = 0]
		fn add_stake(origin, amount: BalanceOf<T>, stakee: T::AccountId) -> Result<(), DispatchError>{
			ensure!(amount != (0 as u32).into(), Error::<T>::ZeroStake);

			let staker = ensure_signed(origin)?;
			let key = Self::get_key(staker.clone(), stakee.clone());

			// Stake does not exist, create a stake (assumption that a zero stake indiacates that it does not exist)
			if <Stakes<T>>::get(key).amount == (0 as u32).into() {

				let mut parent = Root::get();
				
				// Check if root (parent) exists and fetch it, otherwise None
				let current_stake_key = parent;
				let mut current_stake = <Stakes<T>>::get(current_stake_key);

				//println!("parent: {:?}", parent);
				while !(parent == [0u8; 32]) { 
					let next: Hash;
					//println!("current stake: {:?}", current_stake);
					if current_stake.left_amount < current_stake.right_amount {
						next = current_stake.left;
					} else {
						next = current_stake.right;
					}

					if next == [0u8; 32]  {
						break;
					}

					parent = next;
					current_stake = <Stakes<T>>::get(parent);
				}

				Self::set_child(current_stake_key, [0u8; 32], key);

				// Create a stake and insert it into directory
				let mut stake = <Stakes<T>>::get(key);
				stake.parent = parent;
				stake.stakee = stakee.clone();

				<Stakes<T>>::insert(key, stake); // insert it into directory
			}

			// Now that the key for the stake is defined fetch it, or if it was already defined fetch it
			let mut stake = <Stakes<T>>::get(&key);

			// Set the root if it's the first stake
			//println!("{:?}", stake.parent);
			if stake.parent == [0u8; 32] { 
				Root::put(key);
			}

			Self::update_stake_amount(key, key, amount, false);
			T::Currency::withdraw(&staker, amount, WithdrawReason::Fee.into(), ExistenceRequirement::KeepAlive)?;

			Ok(())
		}


		#[weight = 0]
		fn unlock_stake(origin, amount: BalanceOf<T>, address: T::AccountId) {
			let staker = ensure_signed(origin)?;
			let stake_key = Self::get_key(staker, address);
			let mut stake = <Stakes<T>>::get(&stake_key);

			ensure!(stake.amount > (0 as u32).into(), Error::<T>::ZeroStake);
			ensure!(stake.amount >= amount, Error::<T>::InsufficientStakeBalance);

			// Remove the balance from the stake
			Self::update_stake_amount(stake_key, stake_key, amount, true);

			//Stake has been withdrawn now update the tree
			if stake.amount == (0 as u32).into() {
				let mut child : Hash;
				if stake.left_amount > stake.right_amount {
					child = stake.left;
				} else {
					child = stake.right;
				}

				let parent_key = stake.parent;
				let mut parent = <Stakes<T>>::get(parent_key);

				if child == [0u8; 32] {
					Self::set_child(stake_key, stake_key, [0u8; 32]);

					// The only staker is removed, reset root
					if stake.parent == [0u8; 32] {
						Root::set([0u8; 32]);	
					}
				} else {

					let current_key = child;
					let mut current = <Stakes<T>>::get(current_key);

					loop {
						let next : Hash;
						if current.left_amount > current.right_amount {
							next = current.left;
						} else {
							next = current.right;
						}

						if next == [0u8; 32] {
							break;
						}

						child = next;
						current = <Stakes<T>>::get(next);
					}

					let current_parent = current.parent;
					Self::set_child(parent_key, stake_key, child);
					current.parent = stake.parent;


					// update the children of current to be that of what the removed stake was
					if current_parent != stake_key {

						// Move the children of stake to current
						Self::fixl(stake_key, child, current_key);
						Self::fixr(stake_key, child, current_key);

						// Place stake where current was and
						stake.parent = current_parent; // set parent
						Self::set_child(current_parent, current_parent, stake_key); // set parents child

						// Unstake (take away from stake)amount
						Self::apply_stake_change(stake_key, stake_key, current.amount, current.parent);

						Self::set_child(current_parent, stake_key, [0u8; 32]);
					}
					else if stake.left == child {
						Self::fixr(stake_key, child, current_key);
					}
					else {
						Self::fixl(stake_key, child, current_key);
					}

					if current.parent == [0u8; 32] {
						Root::put(child);
					}
				}

				// Now that the node is unlinked from any other nodes we can remove it.
				<Stakes<T>>::remove(stake_key);

				// If not hit then it gives a default value for Unlock struct
				let mut unlock = <Unlockings<T>>::get(stake_key);
				let unlock_at = T::Time::now() + UNLOCK_DURATION.into();

				if unlock.unlock_at < unlock_at {
					unlock.unlock_at = unlock_at;
				}

				unlock.amount += amount;
				<Unlockings<T>>::insert(stake_key, unlock);
			}
		}


		#[weight = 0]
		fn unstake(origin, stakee: T::AccountId) {
			let staker = ensure_signed(origin)?;
			let key = Self::get_key(staker.clone(), stakee);
			let unlock = <Unlockings<T>>::get(key);

			ensure!(unlock.unlock_at <T::Time::now(), Error::<T>::UnlockPeriodNonExhasted);
			ensure!(unlock.amount > (0 as u32).into(), Error::<T>::ZeroStake);

			let amount = unlock.amount;
			<Unlockings<T>>::remove(key);
			T::Currency::deposit_into_existing(&staker, amount);
		}
		

		// Reverse unlocking a certain amount of stake to restake unlock
		#[weight = 0]
		fn lock_stake(origin, amount: BalanceOf<T>, stakee: T::AccountId) {
			let staker = ensure_signed(origin)?;
			let key = Self::get_key(staker, stakee);

			Self::pull_unlocking(key, amount);
			Self::update_stake_amount(key, key, amount, false);
		}

		// Assumes that point is some random u128
	}
}

impl<T: Trait> Module<T> {
	fn get_key(staker: T::AccountId, stakee: T::AccountId) -> Hash {
		let mut vec_bytes = staker.encode();
		vec_bytes.append(&mut stakee.encode());
		keccak_256(vec_bytes.as_slice())
	}

	// set the child for a given stake 
	//	key: stake to replace child
	// 	old_key: key to replace
	// 	new_key: key to replace old key
	fn set_child(key: Hash, old_key : Hash, new_key: Hash) {
		let mut stake = <Stakes<T>>::get(key);
		if stake.left == old_key {
			stake.left = new_key;
		} else {
			stake.right = new_key
		}

		<Stakes<T>>::insert(key, stake);
	}

	// update the value that a stake holds
	//	key: key of stake to update
	//	stake_key: key of the first stake to updat 
	//	amount: amount to change the stake tree by	
	fn update_stake_amount(key: Hash, stake_key: Hash, amount: BalanceOf<T>, flag: bool) {

		let mut stake = <Stakes<T>>::get(stake_key);

		// XXX: Edit stake amount, flag for + or -
		if !flag {
			stake.amount += amount;
		} else {
			stake.amount -= amount;
		}

		// Insert stakee amount into tree and update stake
		<Stakes<T>>::insert(stake_key, &stake);
		<Stakees<T>>::insert(stake.stakee, amount);

		// Apply edit stake amount to tree
		Self::apply_stake_change(key, stake_key, amount, [0u8; 32]);
	}


	fn apply_stake_change(key: Hash, child_key: Hash, amount: BalanceOf<T>, root_: Hash) {
		let parent_key = <Stakes<T>>::get(child_key).parent;

		if parent_key == root_ {
			// we are at the root, there's nothing left ot update
			return;
		}

		let mut parent = <Stakes<T>>::get(parent_key);

		if parent.left == key {
			parent.left_amount += amount;
		} else {
			parent.right_amount += amount;
		}

		<Stakes<T>>::insert(parent_key, parent);

		return Self::apply_stake_change(parent_key, parent_key, amount, root_);
	}

	fn fixl(stake_key: Hash, current_key: Hash, current: Hash) {

		// fetch the stake
		let stake = <Stakes<T>>::get(stake_key);

		if stake.left == [0u8; 32] {
			return;
		}

		let mut stake_left = <Stakes<T>>::get(stake.left);
		stake_left.parent = current_key;

		let mut current = <Stakes<T>>::get(current_key);

		current.left = stake.left;
		current.left_amount = stake.left_amount;

		// update k/v
		<Stakes<T>>::insert(current_key, current);
		<Stakes<T>>::insert(stake.left, stake_left);
	}

	fn fixr(stake_key: Hash, current_key: Hash, current: Hash) {

		// fetch the stake
		let stake = <Stakes<T>>::get(stake_key);

		if stake.right== [0u8; 32] {
			return;
		}

		let mut stake_right = <Stakes<T>>::get(stake.right);
		stake_right.parent = current_key;

		let mut current = <Stakes<T>>::get(current_key);

		current.right = stake.right;
		current.right_amount = stake.right_amount;

		// update k/v
		<Stakes<T>>::insert(current_key, current);
		<Stakes<T>>::insert(stake.right, stake_right);
	}

	// todo: update error types
	fn pull_unlocking(key: Hash, amount: BalanceOf<T>) -> Result<(), Error<T>> {
		if key == [0u8; 32] {
			return Err(Error::<T>::UnlockPeriodNonExhasted);
		}
		let mut unlock = <Unlockings<T>>::get(key);

		// Lock period has not completed
		if T::Time::now() < unlock.unlock_at {
			return Err(Error::<T>::UnlockPeriodNonExhasted);
		}

		// Remove if locking whole unlock
		if amount == unlock.amount {
			<Unlockings<T>>::remove(key);
		} else {
			ensure!(unlock.amount >= amount, Error::<T>::RelockAmount);
			unlock.amount -= amount;
			<Unlockings<T>>::insert(key, unlock);
		}
		Ok(())
	}


	// Select a stake weighted node
	// fn scan(point: U256) -> Hash {
	// 	if Root::get() == [0u8; 32] {
	// 		return [0u8; 32];
	// 	}

	// 	//let expectedValue = U256::from(Self::get_total_stake()) * point / U256::max_value();

	// 	return [0u8; 32];
	// }

	// Retrieve the total stake weight
	// fn get_total_stake() -> BalanceOf<T> {
	// 	// empty root nothing staking
	// 	if !Root::exists() {
	// 		return (0 as u32).into();
	// 	}
	// 	else {
	// 		let root_stake = <Stakes<T>>::get(Root::get());
	// 		root_stake.amount + root_stake.left_amount + root_stake.right_amount
	// 	}
	// }
}

#[cfg(test)]
mod test {
	use super::*;
	use crate::mock::Test as MockTest;
	use frame_support::{impl_outer_origin, parameter_types};
	use pallet_balances::Module as BalanceModule;
	use pallet_timestamp::Module as TimeModule;
	use sp_core::{crypto::AccountId32, ecdsa, ed25519, Pair, sr25519};
	use sp_runtime::{MultiSigner, traits::IdentifyAccount};

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
		//type WeightInfo = ();
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

	type Directory = Module<Test>;
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
			.expect("Could not create Alice keychain pair")
			.public()
			.into()
	}

	fn execute<F: Fn()>(execute: F) {
		sp_io::TestExternalities::from(
			frame_system::GenesisConfig::default()
				.build_storage::<Test>()
				.unwrap()
		).execute_with(execute)
	}

	#[test]
	pub fn test_create_stake() {
		let alice = alice();
		execute(|| {
			// Alice has an initial balance of 1000
			Balance::make_free_balance_be(&alice, 1_000);

			// Deposit 100 into the escrow
			Directory::add_stake(Origin::signed(alice.clone()), 100, alice.clone())
				.expect("Failed to create a stake");

			assert_eq!(Balance::free_balance(alice.clone()), 900);
			//assert_eq!(<Stakes<Test>>::get().amount, 100);
		})
	}

	#[test]
	pub fn test_unlock_stake() {
		let alice = alice();
		let bob = bob();
		execute(|| {
			// Alice has an initial balance of 1000
			Balance::make_free_balance_be(&alice, 1_000);
			Balance::make_free_balance_be(&bob, 1_000);
			// Alice stakes with bob as stakee
			let stake_key = Directory::get_key(alice.clone(), bob.clone());
			Directory::add_stake(Origin::signed(alice.clone()), 100, bob.clone())
				.expect("Failed to create a stake");

			assert_eq!(Balance::free_balance(alice.clone()), 900);
			assert_eq!(<Stakes<Test>>::get(stake_key).amount, 100);

			Directory::unlock_stake(Origin::signed(alice.clone()), 50, bob.clone());
			println!("unlockings: {:?}", <Unlockings<Test>>::get(stake_key));
		})
	}
}