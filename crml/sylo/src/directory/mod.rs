use frame_support::{decl_error, decl_module, decl_storage, ensure, traits::{WithdrawReason, Currency, ExistenceRequirement, Time}, weights::Weight};
use frame_system::ensure_signed;
use codec::{Decode, Encode};
use sp_io::hashing::{keccak_256};
use sp_core::U256;
use sp_runtime::{DispatchError};
//frame_support::debug::native::debug!("called by {:?}", who);

// TODO: set this to a sensible value
const UNLOCK_DURATION: u32 = 5;
const EMPTY_HASH : [u8; 32] = [0u8; 32];

mod default_weights;

pub trait WeightInfo {
	fn add_stake() -> Weight;
	fn unlock_stake() -> Weight;
	fn unstake() -> Weight;
	fn lock_stake() -> Weight;
}

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
    type WeightInfo: WeightInfo;
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
		#[weight = T::WeightInfo::add_stake()]
		fn add_stake(origin, amount: BalanceOf<T>, stakee: T::AccountId) -> Result<(), DispatchError> {
			ensure!(amount != (0 as u32).into(), Error::<T>::ZeroStake);


			let staker = ensure_signed(origin)?;
			let key = Self::get_key(staker.clone(), stakee.clone());

			// Stake does not exist, create a stake (assumption that a zero stake indiacates that it does not exist)
			if <Stakes<T>>::get(key).amount == (0 as u32).into() {

				let mut parent_key = Root::get();
				
				// Check if root (parent) exists and fetch it, otherwise None
				let mut current_stake_key = parent_key;
				let mut current_stake = <Stakes<T>>::get(current_stake_key);

				//println!("parent: {:?}", parent);
				while !(parent_key == [0u8; 32]) { 
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

					parent_key = next;
					current_stake_key = parent_key;
					current_stake = <Stakes<T>>::get(current_stake_key);
				}

				Self::set_child(current_stake_key, [0u8; 32], key);

				// Create a stake and insert it into directory
				let mut stake = <Stakes<T>>::get(key);
				stake.parent = parent_key;
				stake.stakee = stakee.clone();

				// println!("=== ADDING STAKE ===");
				// println!("STAKEE: {:?}", stake.stakee.clone());
				// println!("KEY : {:?}", key.clone());
				// println!("LEFT: {:?}", stake.left.clone());
				// println!("RIGHT: {:?}", stake.right.clone());
				// println!("AMOUNT : {:?}", stake.amount.clone());
				<Stakes<T>>::insert(key, stake); // insert it into directory
			}

			// Now that the key for the stake is defined fetch it, or if it was already defined fetch it
			let stake = <Stakes<T>>::get(&key);

			// Set the root if it's the first stake
			//println!("{:?}", stake.parent);
			if stake.parent == [0u8; 32] { 
				Root::put(key);
			}

			Self::update_stake_amount(key, amount, false);
			T::Currency::withdraw(&staker, amount, WithdrawReason::Fee.into(), ExistenceRequirement::KeepAlive)?;

			Ok(())
		}


		#[weight = T::WeightInfo::unlock_stake()]
		fn unlock_stake(origin, amount: BalanceOf<T>, stakee: T::AccountId) {
			let staker = ensure_signed(origin)?;
			let stake_key = Self::get_key(staker, stakee);
			let mut stake = <Stakes<T>>::get(&stake_key);

			ensure!(stake.amount > (0 as u32).into(), Error::<T>::ZeroStake);
			ensure!(stake.amount >= amount, Error::<T>::InsufficientStakeBalance);

			// Remove the balance from the stake
			Self::update_stake_amount(stake_key, amount, true);
			stake = <Stakes<T>>::get(&stake_key); // Update the stake that has changed above

			//Stake has been withdrawn now update the tree
			if stake.amount == (0 as u32).into() {
				println!("======== STAKE WITHDRAWN COMPLETELY =-======");
				let mut child_key : Hash;
				if stake.left_amount > stake.right_amount {
					child_key = stake.left;
				} else {
					child_key = stake.right;
				}

				let parent_key = stake.parent;
				//let parent = <Stakes<T>>::get(parent_key);

				if child_key == [0u8; 32] {
					Self::set_child(parent_key, stake_key, [0u8; 32]);

					// The only staker is removed, reset root
					if stake.parent == [0u8; 32] {
						Root::set([0u8; 32]);	
					}
				} else {
					let current_key = child_key;
					let mut current = <Stakes<T>>::get(current_key);

					loop {
						let next_key : Hash;
						if current.left_amount > current.right_amount {
							next_key = current.left;
						} else {
							next_key = current.right;
						}

						if next_key == [0u8; 32] {
							break;
						}

						child_key = next_key;
						current = <Stakes<T>>::get(next_key);
					}

					let current_parent = current.parent;
					Self::set_child(parent_key, stake_key, child_key);
					current.parent = stake.parent;
					<Stakes<T>>::insert(current_key, &current);

					// update the children of current to be that of what the removed stake was
					if current_parent != stake_key {

						// Move the children of stake to current
						Self::fixl(stake_key, child_key);
						Self::fixr(stake_key, child_key);

						// Place stake where current was and
						stake.parent = current_parent; // set parent
						<Stakes<T>>::insert(stake_key, stake);

						Self::set_child(current_parent, current_parent, stake_key); // set parents child

						// Unstake (take away from stake)amount
						Self::apply_stake_change(stake_key, current.amount, current.parent, true);

						Self::set_child(current_parent, stake_key, [0u8; 32]);
					}
					else if stake.left == child_key {
						Self::fixr(stake_key, child_key);
					}
					else {
						Self::fixl(stake_key, child_key);
					}

					if current.parent == [0u8; 32] {
						Root::put(child_key);
					}
				}

				// Now that the node is unlinked from any other nodes we can remove it.
				<Stakes<T>>::remove(stake_key);
			}
				// If not hit then it gives a default value for Unlock struct
			let mut unlock = <Unlockings<T>>::get(stake_key);
			let unlock_at = T::Time::now() + UNLOCK_DURATION.into();

			if unlock.unlock_at < unlock_at {
				unlock.unlock_at = unlock_at;
			}

			unlock.amount += amount;
			<Unlockings<T>>::insert(stake_key, unlock);
			//frame_support::debug::native::debug!("key (func) {:?}", &stake_key);
		}


		#[weight = T::WeightInfo::unstake()]
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
		#[weight = T::WeightInfo::lock_stake()]
		fn lock_stake(origin, amount: BalanceOf<T>, stakee: T::AccountId) {
			let staker = ensure_signed(origin)?;
			let key = Self::get_key(staker, stakee);

			Self::pull_unlocking(key, amount);
			Self::update_stake_amount(key, amount, false);
		}
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
	fn set_child(stake_key: Hash, old_key : Hash, new_key: Hash) {
		let mut stake = <Stakes<T>>::get(stake_key);
		if stake.left == old_key {
			stake.left = new_key;
		} else {
			stake.right = new_key
		}

		<Stakes<T>>::insert(stake_key, stake);
	}

	// update the value that a stake holds
	//	key: key of stake to update
	//	stake_key: key of the first stake to updat 
	//	amount: amount to change the stake tree by	
	fn update_stake_amount(stake_key: Hash, amount: BalanceOf<T>, flag: bool) {

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
		Self::apply_stake_change(stake_key, amount, [0u8; 32], flag);
	}


	fn apply_stake_change(stake_key: Hash, amount: BalanceOf<T>, root_: Hash, flag: bool) {
		let parent_key = <Stakes<T>>::get(stake_key).parent;

		if parent_key == root_ {
			// we are at the root, there's nothing left ot update
			return;
		}

		let mut parent = <Stakes<T>>::get(parent_key);

		// XXX obviously you don't want to do it like this dummy
		if !flag {
			if parent.left == stake_key {
				parent.left_amount += amount;
			} else {
				parent.right_amount += amount;
			}
		} else {
			if parent.left == stake_key {
				parent.left_amount -= amount;
			} else {
				parent.right_amount -= amount;
			}
		}

		<Stakes<T>>::insert(parent_key, parent);

		return Self::apply_stake_change(parent_key, amount, root_, flag);
	}

	fn fixl(stake_key: Hash, current_key: Hash) {

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

	fn fixr(stake_key: Hash, current_key: Hash) {

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
	fn pull_unlocking(unlock_key: Hash, amount: BalanceOf<T>) -> Result<(), Error<T>> {
		if unlock_key == [0u8; 32] {
			return Err(Error::<T>::UnlockPeriodNonExhasted);
		}
		let mut unlock = <Unlockings<T>>::get(unlock_key);

		// Remove if locking whole unlock
		if amount == unlock.amount {
			<Unlockings<T>>::remove(unlock_key);
		} else {
			ensure!(unlock.amount >= amount, Error::<T>::RelockAmount);
			unlock.amount -= amount;
			<Unlockings<T>>::insert(unlock_key, unlock);
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
	fn get_total_stake() -> BalanceOf<T> {
		// empty root nothing staking
		if !Root::exists() {
			return (0 as u32).into();
		}
		else {
			let root_stake = <Stakes<T>>::get(Root::get());
			root_stake.amount + root_stake.left_amount + root_stake.right_amount
		}
	}
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
			.expect("Could not create Bob keychain pair")
			.public()
			.into()
	}

	fn charlie() -> AccountId32 {
		<ed25519::Pair as Pair>::from_string("//Charlie", None)
			.expect("Could not create Charlie keychain pair")
			.public()
			.into()
	}

	fn dave() -> AccountId32 {
		<ed25519::Pair as Pair>::from_string("//Dave", None)
			.expect("Could not create Dave keychain pair")
			.public()
			.into()
	}

	fn eve() -> AccountId32 {
		<ed25519::Pair as Pair>::from_string("//Eve", None)
			.expect("Could not create Eve keychain pair")
			.public()
			.into()
	}

	fn ferdie() -> AccountId32 {
		<ed25519::Pair as Pair>::from_string("//Ferdie", None)
			.expect("Could not create Ferdie keychain pair")
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
	pub fn test_basic_create_stake() {
		let a = alice();
		execute(|| {
			// Alice has an initial balance of 1000
			Balance::make_free_balance_be(&a, 1_000);

			// Deposit 100 into the escrow
			Directory::add_stake(Origin::signed(a.clone()), 100, a.clone())
				.expect("Failed to create a stake");

			// Stake amount is withdrawn from Alice's account
			assert_eq!(Balance::free_balance(a.clone()), 900);

			let key = Directory::get_key(a.clone(), a.clone());
			let stake = <Stakes<Test>>::get(key);

			// First stake in tree, should be assigned as root
			assert_eq!(key, Root::get()); 
			assert_eq!(stake.parent, [0u8; 32]);

			assert_eq!(stake.amount, 100);
			assert_eq!(stake.left_amount, 0);
			assert_eq!(stake.right_amount, 0);

			// Stake was delegated to Alice
			assert_eq!(stake.stakee, a.clone()); 

			// Only stake in tree, thus has no children
			assert_eq!(stake.left, [0u8; 32]); 
			assert_eq!(stake.right, [0u8; 32]);

			// Stake is recorded in stakees
			let stakee_balance = <Stakees<Test>>::get(a.clone());
			assert_eq!(stakee_balance, 100);
		})
	}

	#[test]
	pub fn test_basic_unstake() {
		let a = alice();
		execute(|| {
			// Alice has an initial balance of 1000
			Balance::make_free_balance_be(&a, 1_000);

			let key = Directory::get_key(a.clone(), a.clone());
			// Deposit 100 into the escrow
			Directory::add_stake(Origin::signed(a.clone()), 500, a.clone())
				.expect("Failed to create a stake");

			// Stake amount is withdrawn from Alice's account
			assert_eq!(Balance::free_balance(a.clone()), 500);

			// Unlock part of stake
			Directory::unlock_stake(Origin::signed(a.clone()), 250, a.clone());

			// Check unlocking
			let unlocking = <Unlockings<Test>>::get(key);
			assert_eq!(unlocking.amount, 250);
			assert_eq!(unlocking.unlock_at, 5);

			// Check stake
			let stake = <Stakes<Test>>::get(key);
			assert_eq!(stake.amount, 250);

			// Set time past stake unlock period
			Time::set_timestamp(10); 

			// Unstake
			Directory::unstake(Origin::signed(a.clone()), a.clone());
			assert_eq!(Balance::free_balance(a.clone()), 750);
		})
	}

	#[test]
	pub fn test_basic_relock_stake() {
		let a = alice();
		execute(|| {
			// Alice has an initial balance of 1000
			Balance::make_free_balance_be(&a, 1_000);

			let key = Directory::get_key(a.clone(), a.clone());
			// Deposit 100 into the escrow
			Directory::add_stake(Origin::signed(a.clone()), 500, a.clone())
				.expect("Failed to create a stake");

			// Stake amount is withdrawn from Alice's account
			assert_eq!(Balance::free_balance(a.clone()), 500);

			// Unlock part of stake
			Directory::unlock_stake(Origin::signed(a.clone()), 250, a.clone());

			// Check unlocking
			let mut unlocking = <Unlockings<Test>>::get(key);
			assert_eq!(unlocking.amount, 250);
			assert_eq!(unlocking.unlock_at, 5);

			// Check stake
			let mut stake = <Stakes<Test>>::get(key);
			assert_eq!(stake.amount, 250);
			
			// Relock part of the stake
			Directory::lock_stake(Origin::signed(a.clone()), 125, a.clone());

			// Recheck unlocking
			unlocking = <Unlockings<Test>>::get(key);
			assert_eq!(unlocking.amount, 125);
			assert_eq!(unlocking.unlock_at, 5);

			// Recheck stake
			stake = <Stakes<Test>>::get(key);
			assert_eq!(stake.amount, 375);
		})
	}

	#[test]
	pub fn test_stake_tree() {
		let a = alice();
		let b = bob();
		let c = charlie();
		let d = dave();
		let e = eve();
		let f = ferdie();
		execute(|| {
			Balance::make_free_balance_be(&a, 1_000);
			Balance::make_free_balance_be(&b, 1_000);
			Balance::make_free_balance_be(&c, 1_000);
			Balance::make_free_balance_be(&d, 1_000);
			Balance::make_free_balance_be(&e, 1_000);
			Balance::make_free_balance_be(&f, 1_000);

			// Create stakes
			Directory::add_stake(Origin::signed(a.clone()), 500, a.clone())
				.expect("Failed to create a stake");
			Directory::add_stake(Origin::signed(b.clone()), 400, b.clone())
				.expect("Failed to create a stake");
			Directory::add_stake(Origin::signed(c.clone()), 300, c.clone())
				.expect("Failed to create a stake");
			Directory::add_stake(Origin::signed(d.clone()), 200, d.clone())
				.expect("Failed to create a stake");
			Directory::add_stake(Origin::signed(e.clone()), 100, e.clone())
				.expect("Failed to create a stake");
			Directory::add_stake(Origin::signed(f.clone()), 50, f.clone())
				.expect("Failed to create a stake");

			// Keys for stakes
			let a_key = Directory::get_key(a.clone(), a.clone());
			let b_key = Directory::get_key(b.clone(), b.clone());
			let c_key = Directory::get_key(c.clone(), c.clone());
			let d_key = Directory::get_key(d.clone(), d.clone());
			let e_key = Directory::get_key(e.clone(), e.clone());
			let f_key = Directory::get_key(f.clone(), f.clone());

			println!("alice stake : {:?}", a_key);
			println!("bob stake : {:?}", b_key);
			println!("charlie stake : {:?}", c_key);
			println!("dave stake : {:?}", d_key);
			println!("eve stake : {:?}", e_key);
			println!("ferdie stake : {:?}", f_key);

			// Fetch stakes
			let mut a_stake = <Stakes<Test>>::get(a_key);
			let mut b_stake = <Stakes<Test>>::get(b_key);
			let mut c_stake = <Stakes<Test>>::get(c_key);
			let mut d_stake = <Stakes<Test>>::get(d_key);
			let mut e_stake = <Stakes<Test>>::get(e_key);
			let mut f_stake = <Stakes<Test>>::get(f_key);

			// Verify tree structure
			assert_eq!(Directory::get_total_stake(), 1_550);

			assert_eq!(Root::get(), a_key);
			assert_eq!(a_stake.amount, 500);
			assert_eq!(a_stake.stakee, a.clone());
			assert_eq!(a_stake.parent, [0u8; 32]);
			assert_eq!(a_stake.left, b_key);
			assert_eq!(a_stake.left_amount, 500);
			assert_eq!(a_stake.right_amount, 550);
			assert_eq!(<Stakees<Test>>::get(a.clone()), 500);

			assert_eq!(b_stake.amount, 400);
			assert_eq!(b_stake.stakee, b.clone());
			assert_eq!(b_stake.parent, a_key);
			assert_eq!(b_stake.left, e_key);
			assert_eq!(b_stake.left_amount, 100);
			assert_eq!(b_stake.right, [0u8; 32]);
			assert_eq!(b_stake.right_amount, 0);

			assert_eq!(c_stake.amount, 300);
			assert_eq!(c_stake.stakee, c.clone());
			assert_eq!(c_stake.parent, a_key);
			assert_eq!(c_stake.left, d_key);
			assert_eq!(c_stake.left_amount, 200);
			assert_eq!(c_stake.right, f_key);
			assert_eq!(c_stake.right_amount, 50);

			assert_eq!(d_stake.amount, 200);
			assert_eq!(d_stake.stakee, d.clone());
			assert_eq!(d_stake.parent, c_key);
			assert_eq!(d_stake.left, EMPTY_HASH);
			assert_eq!(d_stake.left_amount, 0);
			assert_eq!(d_stake.right, EMPTY_HASH);
			assert_eq!(d_stake.right_amount, 0);

			assert_eq!(e_stake.amount, 100);
			assert_eq!(e_stake.stakee, e.clone());
			assert_eq!(e_stake.parent, b_key);
			assert_eq!(e_stake.left, EMPTY_HASH);
			assert_eq!(e_stake.left_amount, 0);
			assert_eq!(e_stake.right, EMPTY_HASH);
			assert_eq!(e_stake.right_amount, 0);

			assert_eq!(f_stake.amount, 50);
			assert_eq!(f_stake.stakee, f.clone());
			assert_eq!(f_stake.parent, c_key);
			assert_eq!(f_stake.left, EMPTY_HASH);
			assert_eq!(f_stake.left_amount, 0);
			assert_eq!(f_stake.right, EMPTY_HASH);
			assert_eq!(f_stake.right_amount, 0);

			// Remove a non leaf, non root node
			Directory::unlock_stake(Origin::signed(c.clone()), 300, c.clone());
			Time::set_timestamp(30); 
			Directory::unstake(Origin::signed(c.clone()), c.clone());
			assert_eq!(Directory::get_total_stake(), 1_250);

			// Refetch stakes
			a_stake = <Stakes<Test>>::get(a_key);
			b_stake = <Stakes<Test>>::get(b_key);
			c_stake = <Stakes<Test>>::get(c_key);
			d_stake = <Stakes<Test>>::get(d_key);
			e_stake = <Stakes<Test>>::get(e_key);
			f_stake = <Stakes<Test>>::get(f_key);

			// Verify tree integrity
			assert_eq!(Root::get(), a_key);
			assert_eq!(a_stake.amount, 500);
			assert_eq!(a_stake.stakee, a.clone());
			assert_eq!(a_stake.parent, [0u8; 32]);
			assert_eq!(a_stake.left, b_key);
			assert_eq!(a_stake.left_amount, 500);
			assert_eq!(a_stake.right_amount, 250);

			assert_eq!(b_stake.amount, 400);
			assert_eq!(b_stake.stakee, b.clone());
			assert_eq!(b_stake.parent, a_key);
			assert_eq!(b_stake.left, e_key);
			assert_eq!(b_stake.left_amount, 100);
			assert_eq!(b_stake.right, [0u8; 32]);
			assert_eq!(b_stake.right_amount, 0);

			assert_eq!(c_stake.amount, 0);
			// assert_eq!(c_stake.stakee, EMPTY_HASH);
			assert_eq!(c_stake.parent, EMPTY_HASH);
			assert_eq!(c_stake.left, EMPTY_HASH);
			assert_eq!(c_stake.left_amount, 0);
			assert_eq!(c_stake.right, EMPTY_HASH);
			assert_eq!(c_stake.right_amount, 0);

			assert_eq!(d_stake.amount, 200);
			assert_eq!(d_stake.stakee, d.clone());
			assert_eq!(d_stake.parent, a_key);
			assert_eq!(d_stake.left, EMPTY_HASH);
			assert_eq!(d_stake.left_amount, 0);
			assert_eq!(d_stake.right, f_key);
			assert_eq!(d_stake.right_amount, 50);

			assert_eq!(e_stake.amount, 100);
			assert_eq!(e_stake.stakee, e.clone());
			assert_eq!(e_stake.parent, b_key);
			assert_eq!(e_stake.left, EMPTY_HASH);
			assert_eq!(e_stake.left_amount, 0);
			assert_eq!(e_stake.right, EMPTY_HASH);
			assert_eq!(e_stake.right_amount, 0);

			assert_eq!(f_stake.amount, 50);
			assert_eq!(f_stake.stakee, f.clone());
			assert_eq!(f_stake.parent, d_key);
			assert_eq!(f_stake.left, EMPTY_HASH);
			assert_eq!(f_stake.left_amount, 0);
			assert_eq!(f_stake.right, EMPTY_HASH);
			assert_eq!(f_stake.right_amount, 0);

			// Remove a root node
			Directory::unlock_stake(Origin::signed(a.clone()), 500, a.clone());
			Time::set_timestamp(40); 
			Directory::unstake(Origin::signed(a.clone()), a.clone());
			assert_eq!(Directory::get_total_stake(), 750);

			// Refetch stakes
			a_stake = <Stakes<Test>>::get(a_key);
			b_stake = <Stakes<Test>>::get(b_key);
			c_stake = <Stakes<Test>>::get(c_key);
			d_stake = <Stakes<Test>>::get(d_key);
			e_stake = <Stakes<Test>>::get(e_key);
			f_stake = <Stakes<Test>>::get(f_key);

			println!("alice stake : {:?}", a_key);
			println!("bob stake : {:?}", b_key);
			println!("charlie stake : {:?}", c_key);
			println!("dave stake : {:?}", d_key);
			println!("eve stake : {:?}", e_key);
			println!("ferdie stake : {:?}", f_key);

			// Remove a leaf node




		})
	}


	// #[test]
	// pub fn test_stake_tree() {
	// 	let alice = alice();
	// 	let bob = bob();
	// 	let charlie = charlie();
	// 	let dave = dave();

	// 	execute(|| {
	// 		Balance::make_free_balance_be(&alice, 1_000);
	// 		Balance::make_free_balance_be(&bob, 1_000);
	// 		Balance::make_free_balance_be(&charlie, 1_000);
	// 		Balance::make_free_balance_be(&dave, 1_000);


	// 		Directory::add_stake(Origin::signed(alice.clone()), 500, alice.clone())
	// 			.expect("Failed to create a stake");
	// 		Directory::add_stake(Origin::signed(bob.clone()), 300, bob.clone())
	// 			.expect("Failed to create a stake");
	// 		Directory::add_stake(Origin::signed(charlie.clone()), 200, charlie.clone())
	// 			.expect("Failed to create a stake");
	// 		Directory::add_stake(Origin::signed(dave.clone()), 100, dave.clone())
	// 			.expect("Failed to create a stake");

	// 		let alice_key = Directory::get_key(alice.clone(), alice.clone());
	// 		let bob_key = Directory::get_key(bob.clone(), bob.clone());
	// 		let charlie_key = Directory::get_key(charlie.clone(), charlie.clone());
	// 		let dave_key = Directory::get_key(dave.clone(), dave.clone());

	// 		let mut alice_stake = <Stakes<Test>>::get(alice_key);
	// 		let mut bob_stake = <Stakes<Test>>::get(bob_key);
	// 		let mut charlie_stake = <Stakes<Test>>::get(charlie_key);
	// 		let mut dave_stake = <Stakes<Test>>::get(dave_key);
                       
	// 		//         Alice      
	// 		//           /\       
	// 		//          /  \      
	// 		//         /    \     
	// 		//        v      v    
	// 		//      Bob   Charlie 
	// 		//      /\       /\   
	// 		//     /  \     /  \  
	// 		//    v    v   /    \ 
	// 		//            v      v
	// 		//          Dave      

	// 		assert_eq!(Directory::get_total_stake(), 1100);

	// 		// Verify tree structure
	// 		assert_eq!(alice_stake.parent, [0u8; 32]);
	// 		assert_eq!(alice_stake.left, bob_key);
	// 		assert_eq!(alice_stake.right, charlie_key);

	// 		assert_eq!(bob_stake.parent, alice_key); 
	// 		assert_eq!(bob_stake.left, [0u8; 32]);
	// 		assert_eq!(bob_stake.right, [0u8; 32]);

	// 		assert_eq!(charlie_stake.parent, alice_key); 
	// 		assert_eq!(charlie_stake.left, dave_key);
	// 		assert_eq!(charlie_stake.right, [0u8; 32]);

	// 		assert_eq!(dave_stake.parent, charlie_key); 
	// 		assert_eq!(dave_stake.left, [0u8; 32]);
	// 		assert_eq!(dave_stake.right, [0u8; 32]);

	// 		println!("======= TREE CREATION OK ======");

	// 		// Verify that stakes have been withdrawn from account
	// 		assert_eq!(Balance::free_balance(alice.clone()), 500);
	// 		assert_eq!(Balance::free_balance(bob.clone()), 700);
	// 		assert_eq!(Balance::free_balance(charlie.clone()), 800);
	// 		assert_eq!(Balance::free_balance(dave.clone()), 900);


	// 		// ==== Start unlocking stake ==== 

	// 		// Remove leaf node
	// 		println!("======= REMOVING LEAF ======");
	// 		Directory::unlock_stake(Origin::signed(dave.clone()), 100, dave.clone());
	// 		Directory::unstake(Origin::signed(dave.clone()), dave.clone());

	// 		alice_stake = <Stakes<Test>>::get(alice_key);
	// 		bob_stake = <Stakes<Test>>::get(bob_key);
	// 		charlie_stake = <Stakes<Test>>::get(charlie_key);
	// 		dave_stake = <Stakes<Test>>::get(dave_key);

	// 		println!("alice stake : {:?}", alice_key);
	// 		println!("bob stake : {:?}", bob_key);
	// 		println!("charlie stake : {:?}", charlie_key);
	// 		println!("dave stake : {:?}", dave_key);

	// 		println!("alice stake true : {:?}", alice_stake);
	// 		println!("bob stake true : {:?}", bob_stake);
	// 		println!("charlie stake true : {:?}", charlie_stake);
	// 		println!("dave stake true : {:?}", dave_stake);

	// 		// Verify tree structure
	// 		assert_eq!(alice_stake.parent, [0u8; 32]);
	// 		assert_eq!(alice_stake.left, bob_key);
	// 		assert_eq!(alice_stake.right, charlie_key);

	// 		assert_eq!(bob_stake.parent, alice_key); 
	// 		assert_eq!(bob_stake.left, [0u8; 32]);
	// 		assert_eq!(bob_stake.right, [0u8; 32]);

	// 		assert_eq!(charlie_stake.parent, alice_key); 
	// 		assert_eq!(charlie_stake.left, [0u8; 32]);
	// 		assert_eq!(charlie_stake.right, [0u8; 32]);

	// 		// Stake should no longer exist
	// 		assert_eq!(dave_stake.parent, [0u8; 32]); 
	// 		assert_eq!(dave_stake.left, [0u8; 32]);
	// 		assert_eq!(dave_stake.right, [0u8; 32]);

	// 		println!("======= REMOVING LEAF OK ======");

	// 		//         Alice      
	// 		//           /\       
	// 		//          /  \      
	// 		//         /    \     
	// 		//        v      v    
	// 		//      Bob   Charlie 

	// 		// Completely unstake (root)
	// 		Directory::unlock_stake(Origin::signed(alice.clone()), 500, alice.clone());
	// 		Time::set_timestamp(10); 
	// 		Directory::unstake(Origin::signed(alice.clone()), alice.clone());
	// 		println!("Root: {:?}", Root::get());
	// 		//assert_eq!(Directory::get_total_stake(), 600);

	// 		alice_stake = <Stakes<Test>>::get(alice_key);
	// 		bob_stake = <Stakes<Test>>::get(bob_key);
	// 		charlie_stake = <Stakes<Test>>::get(charlie_key);
	// 		dave_stake = <Stakes<Test>>::get(dave_key);

	// 		println!("alice stake : {:?}", alice_key);
	// 		println!("bob stake : {:?}", bob_key);
	// 		println!("charlie stake : {:?}", charlie_key);
	// 		println!("dave stake : {:?}", dave_key);

	// 		println!("alice stake true : {:?}", alice_stake);
	// 		println!("bob stake true : {:?}", bob_stake);
	// 		println!("charlie stake true : {:?}", charlie_stake);
	// 		println!("dave stake true : {:?}", dave_stake);

				
	// 		// Remove middle left node
				
	// 	})
	// }

	#[test]
	pub fn update_stake() {
		let alice = alice();
		execute(|| {
			// Everyone at 1000 balance
			Balance::make_free_balance_be(&alice, 1_000);
		})
	}



	#[test]
	pub fn test_unstake() {
		let alice = alice();
		let bob = bob();
		execute(|| {
			Time::set_timestamp(0); // Initialize time.

			Balance::make_free_balance_be(&alice, 1_000);
			Balance::make_free_balance_be(&bob, 1_000);

			// Alice stakes with bob as stakee
			let key = Directory::get_key(alice.clone(), bob.clone());
			Directory::add_stake(Origin::signed(alice.clone()), 100, bob.clone())
				.expect("Failed to create a stake");

			assert_eq!(Balance::free_balance(alice.clone()), 900);
			assert_eq!(<Stakes<Test>>::get(key).amount, 100);

			// Unlock tokens that were staked
			Directory::unlock_stake(Origin::signed(alice.clone()), 50, bob.clone());

			// check unlock amount
			let unlock = <Unlockings<Test>>::get(key);
			assert_eq!(unlock.amount, 50);
			assert_eq!(unlock.unlock_at, 5);

			// Attempt to withdraw unlock before unlock_at period passed
			Directory::unstake(Origin::signed(alice.clone()), bob.clone())
				.expect_err("Should not be able to withdraw an unlock before unlock period expired");

			// Set time past unlock period and withdraw unlock
			Time::set_timestamp(10); 
			Directory::unstake(Origin::signed(alice.clone()), bob.clone());

			// Check that unlock is withdrawn (and removed from k/v store) and that balances are correct
			assert_eq!(<Unlockings<Test>>::contains_key(key), false);
			assert_eq!(Balance::free_balance(alice.clone()), 950);


			// check that stake is updated
			assert_eq!(<Stakes<Test>>::get(key).amount, 50);
		})
	}
}