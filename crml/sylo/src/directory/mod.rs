use codec::{Decode, Encode};
use frame_support::{
	decl_error, decl_module, decl_storage, ensure,
	traits::{Currency, ExistenceRequirement, Time, WithdrawReason},
	weights::Weight,
};
use frame_system::ensure_signed;
use sp_io::hashing::keccak_256;
use sp_runtime::{traits::Bounded, DispatchResult};
use sp_arithmetic::Permill;

// TODO: Set unlock duration to a sensible value
const UNLOCK_DURATION: u32 = 5;
const EMPTY_HASH: [u8; 32] = [0u8; 32];

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

#[derive(Encode, Decode, Default, Debug, Clone)]
pub struct Stake<AccountId, Balance> {
	amount: Balance, // Amount of the stake

	left_amount: Balance,  // Value of the stake on left branch
	right_amount: Balance, // Value of the stake on the right branch

	stakee: AccountId, // Address of peer that offers sevices

	parent: Hash, // Hash of parent
	left: Hash,   // Hash of left child
	right: Hash,  // Hash of right child
}

#[derive(Encode, Decode, Default, Debug)]
pub struct Unlock<Balance, Timestamp> {
	amount: Balance,      // Amount of stake unlocking
	unlock_at: Timestamp, // Block number stake becomes withdrawable
}

decl_storage! {
	trait Store for Module<T: Trait> as SyloDirectory {
		pub Stakes get(fn stakes): map hasher(blake2_128_concat) Hash => Stake<T::AccountId, BalanceOf<T>>;
		pub Stakees get(fn stakees): map hasher(blake2_128_concat) T::AccountId => BalanceOf<T>;
		pub Unlockings get(fn unlockings): map hasher(blake2_128_concat) Hash => Unlock<BalanceOf<T>, Timestamp<T>>;
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
		/// The unlock period has not been exhausted
		UnlockPeriodNonExhasted,
		/// Attempt to unlock more than what is staking
		InsufficientStakeBalance,
		/// Nonexisting key
		KeyDoesNotExist,
		/// Unlock amount insuffient to the amount you're trying to relock
		RelockAmount,
		/// Scan staker not found
		NoStakes,
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin, system = frame_system {

		// Add a stake to the directory
		#[weight = T::WeightInfo::add_stake()]
		fn add_stake(origin, amount: BalanceOf<T>, stakee: T::AccountId) -> DispatchResult {
			ensure!(amount != (0 as u32).into(), Error::<T>::ZeroStake);

			let staker = ensure_signed(origin)?;
			let key = Self::get_key(staker.clone(), stakee.clone());

			// Stake does not exist, create a stake
			if <Stakes<T>>::get(key).amount == (0 as u32).into() {

				let mut parent_key = Root::get();

				// Check if root (parent) exists and fetch it
				let mut current_stake_key = parent_key;
				let mut current_stake = <Stakes<T>>::get(current_stake_key);

				while parent_key != EMPTY_HASH {
					let next: Hash;
					if current_stake.left_amount < current_stake.right_amount {
						next = current_stake.left;
					} else {
						next = current_stake.right;
					}

					if next == EMPTY_HASH  {
						break;
					}

					parent_key = next;
					current_stake_key = parent_key;
					current_stake = <Stakes<T>>::get(current_stake_key);
				}

				Self::set_child(current_stake_key, EMPTY_HASH, key);

				// Create a stake and insert it into directory
				let mut stake = <Stakes<T>>::get(key);
				stake.parent = parent_key;
				stake.stakee = stakee.clone();
				<Stakes<T>>::insert(key, stake);
			}

			// Now that the key for the stake is defined fetch it, or if it was already defined fetch it
			let stake = <Stakes<T>>::get(&key);

			// Set the root if it's the first stake
			if stake.parent == EMPTY_HASH {
				Root::put(key);
			}

			Self::update_stake_amount(key, amount, false);
			T::Currency::withdraw(&staker, amount, WithdrawReason::Fee.into(), ExistenceRequirement::KeepAlive)?;

			Ok(())
		}


		// Unlock a stake from the directory
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
				let mut child_key : Hash;
				if stake.left_amount > stake.right_amount {
					child_key = stake.left;
				} else {
					child_key = stake.right;
				}

				let parent_key = stake.parent;

				if child_key == EMPTY_HASH {
					Self::set_child(parent_key, stake_key, EMPTY_HASH);

					// The only staker is removed, reset root
					if stake.parent == EMPTY_HASH {
						Root::set(EMPTY_HASH);
					}
				} else {
					let mut current_key = child_key;
					let mut current = <Stakes<T>>::get(current_key);

					loop {
						let next_key : Hash;
						if current.left_amount > current.right_amount {
							next_key = current.left;
						} else {
							next_key = current.right;
						}

						if next_key == EMPTY_HASH {
							break;
						}

						child_key = next_key;
						current_key = child_key;
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

						// Refetch stake after above changes
						current = <Stakes<T>>::get(current_key);
						stake = <Stakes<T>>::get(stake_key);

						// Place stake where current was and...
						stake.parent = current_parent; // ... set parent...
						<Stakes<T>>::insert(stake_key, stake.clone());
						Self::set_child(current_parent, child_key, stake_key); // ...set parents' child

						// Unstake amount
						Self::apply_stake_change(stake_key, current.amount, current.parent, true);
						current = <Stakes<T>>::get(current_key);

						Self::set_child(current_parent, stake_key, EMPTY_HASH);
					}
					else if stake.left == child_key {
						Self::fixr(stake_key, child_key);
					}
					else {
						Self::fixl(stake_key, child_key);
					}

					if current.parent == EMPTY_HASH {
						Root::put(child_key);
					}
				}

				// Now that the node is unlinked from any other nodes we can remove it.
				<Stakes<T>>::remove(stake_key);
			}

			// Create unlock
			let mut unlock = <Unlockings<T>>::get(stake_key);
			let unlock_at = T::Time::now() + UNLOCK_DURATION.into();

			if unlock.unlock_at < unlock_at {
				unlock.unlock_at = unlock_at;
			}

			unlock.amount += amount;
			<Unlockings<T>>::insert(stake_key, unlock);
		}


		// Retrieve funds from an unlock
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

		// Relock an unlock to restake
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
	// Key for the stake/unlock
	fn get_key(staker: T::AccountId, stakee: T::AccountId) -> Hash {
		let mut vec_bytes = staker.encode();
		vec_bytes.append(&mut stakee.encode());
		keccak_256(vec_bytes.as_slice())
	}

	// Replace a child for a stake
	fn set_child(stake_key: Hash, old_key: Hash, new_key: Hash) {
		let mut stake = <Stakes<T>>::get(stake_key);
		if stake.left == old_key {
			stake.left = new_key;
		} else {
			stake.right = new_key
		}

		<Stakes<T>>::insert(stake_key, stake);
	}

	// Update the value that a stake holds, apply change to rest of tree directory
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
		<Stakees<T>>::insert(stake.stakee, stake.amount);

		// Apply edit stake amount to tree
		Self::apply_stake_change(stake_key, amount, EMPTY_HASH, flag);
	}

	// Change the weight of a stake and apply to the whole the tree
	fn apply_stake_change(stake_key: Hash, amount: BalanceOf<T>, root: Hash, flag: bool) {
		let parent_key = <Stakes<T>>::get(stake_key).parent;

		if parent_key == root {
			// We are at the root, there's nothing left to update
			return;
		}

		let mut parent = <Stakes<T>>::get(parent_key);

		// XXX: Find a better way to create a negative balance
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

		return Self::apply_stake_change(parent_key, amount, root, flag);
	}

	// Fix the left children of a stake to the left children of another stake
	fn fixl(stake_key: Hash, current_key: Hash) {
		// fetch the stake
		let stake = <Stakes<T>>::get(stake_key);

		if stake.left == EMPTY_HASH {
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

	// Fix the right children of a stake to the right children of another stake
	fn fixr(stake_key: Hash, current_key: Hash) {
		// fetch the stake
		let stake = <Stakes<T>>::get(stake_key);

		if stake.right == EMPTY_HASH {
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

	// Relock an unlocked stake
	// todo: update error types
	fn pull_unlocking(unlock_key: Hash, amount: BalanceOf<T>) -> Result<(), Error<T>> {
		if unlock_key == EMPTY_HASH {
			return Err(Error::<T>::KeyDoesNotExist);
		}
		let mut unlock = <Unlockings<T>>::get(unlock_key);

		// Remove unlock if relocking whole amount
		if amount == unlock.amount {
			<Unlockings<T>>::remove(unlock_key);
		} else {
			ensure!(unlock.amount >= amount, Error::<T>::RelockAmount);
			unlock.amount -= amount;
			<Unlockings<T>>::insert(unlock_key, unlock);
		}
		Ok(())
	}

	// Scan the stake directory, select a node
	pub fn scan(point: BalanceOf<T>) -> Result<T::AccountId, Error<T>> {
		ensure!(Root::get() != EMPTY_HASH, Error::<T>::NoStakes);
		let mut expected_val = Permill::from_rational_approximation(point, BalanceOf::<T>::max_value()).mul_floor(Self::get_total_stake());
		let mut current = Root::get();

		loop {
			let stake = <Stakes<T>>::get(current);
			if expected_val < stake.left_amount {
				current = stake.left;
				continue;
			}

			expected_val -= stake.left_amount;

			if expected_val <= stake.amount {
				return Ok(stake.stakee);
			}

			expected_val -= stake.amount;
			current = stake.right;
		}
	}

	// Retrieve the total stake weight of the directory
	fn get_total_stake() -> BalanceOf<T> {
		if !Root::exists() {
			return (0 as u32).into();
		} else {
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
		sp_io::TestExternalities::from(frame_system::GenesisConfig::default().build_storage::<Test>().unwrap())
			.execute_with(execute)
	}

	#[test]
	pub fn test_basic_create_stake() {
		let a = alice();
		execute(|| {
			// Alice has an initial balance of 1000
			Balance::make_free_balance_be(&a, 1_000);

			// Deposit 100 into the escrow
			Directory::add_stake(Origin::signed(a.clone()), 100, a.clone()).expect("Failed to create a stake");

			// Stake amount is withdrawn from Alice's account
			assert_eq!(Balance::free_balance(a.clone()), 900);

			let key = Directory::get_key(a.clone(), a.clone());
			let stake = <Stakes<Test>>::get(key);

			// First stake in tree, should be assigned as root
			assert_eq!(key, Root::get());
			assert_eq!(stake.parent, EMPTY_HASH);
			assert_eq!(stake.amount, 100);
			assert_eq!(stake.left_amount, 0);
			assert_eq!(stake.right_amount, 0);

			// Stake was delegated to Alice
			assert_eq!(stake.stakee, a.clone());

			// Only stake in tree, thus has no children
			assert_eq!(stake.left, EMPTY_HASH);
			assert_eq!(stake.right, EMPTY_HASH);

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
			Directory::add_stake(Origin::signed(a.clone()), 500, a.clone()).expect("Failed to create a stake");

			// Retrieve and verify stake
			let mut a_stake = <Stakes<Test>>::get(key);
			assert_eq!(a_stake.amount, 500);
			assert_eq!(a_stake.stakee, a.clone());
			assert_eq!(a_stake.parent, EMPTY_HASH);
			assert_eq!(a_stake.left, EMPTY_HASH);
			assert_eq!(a_stake.left_amount, 0);
			assert_eq!(a_stake.right, EMPTY_HASH);
			assert_eq!(a_stake.right_amount, 0);

			// Check stakee balance
			let stakee_balance = <Stakees<Test>>::get(a.clone());
			assert_eq!(stakee_balance, 500);

			// Stake amount is withdrawn from Alice's account
			assert_eq!(Balance::free_balance(a.clone()), 500);

			// Unlock part of stake
			Directory::unlock_stake(Origin::signed(a.clone()), 250, a.clone());

			// Check unlocking
			let unlocking = <Unlockings<Test>>::get(key);
			assert_eq!(unlocking.amount, 250);
			assert_eq!(unlocking.unlock_at, 5);

			// Check stake
			a_stake = <Stakes<Test>>::get(key);
			assert_eq!(a_stake.amount, 250);

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
			Directory::add_stake(Origin::signed(a.clone()), 500, a.clone()).expect("Failed to create a stake");

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
	pub fn test_stake_tree_stake_unstake() {
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

			// Create slightly complex stake directory
			Directory::add_stake(Origin::signed(a.clone()), 500, a.clone()).expect("Failed to create a stake");
			Directory::add_stake(Origin::signed(b.clone()), 400, b.clone()).expect("Failed to create a stake");
			Directory::add_stake(Origin::signed(c.clone()), 300, c.clone()).expect("Failed to create a stake");
			Directory::add_stake(Origin::signed(d.clone()), 200, d.clone()).expect("Failed to create a stake");
			Directory::add_stake(Origin::signed(e.clone()), 100, e.clone()).expect("Failed to create a stake");
			Directory::add_stake(Origin::signed(f.clone()), 50, f.clone()).expect("Failed to create a stake");

			// Keys for stakes
			let a_key = Directory::get_key(a.clone(), a.clone());
			let b_key = Directory::get_key(b.clone(), b.clone());
			let c_key = Directory::get_key(c.clone(), c.clone());
			let d_key = Directory::get_key(d.clone(), d.clone());
			let e_key = Directory::get_key(e.clone(), e.clone());
			let f_key = Directory::get_key(f.clone(), f.clone());

			// Fetch stakes
			let mut a_stake = <Stakes<Test>>::get(a_key);
			let mut b_stake = <Stakes<Test>>::get(b_key);
			let mut c_stake = <Stakes<Test>>::get(c_key);
			let mut d_stake = <Stakes<Test>>::get(d_key);
			let mut e_stake = <Stakes<Test>>::get(e_key);
			let mut f_stake = <Stakes<Test>>::get(f_key);

			// Fetch stakes
			let mut a_stakee = <Stakees<Test>>::get(a.clone());
			let mut b_stakee = <Stakees<Test>>::get(b.clone());
			let mut c_stakee = <Stakees<Test>>::get(c.clone());
			let mut d_stakee = <Stakees<Test>>::get(d.clone());
			let mut e_stakee = <Stakees<Test>>::get(e.clone());
			let mut f_stakee = <Stakees<Test>>::get(f.clone());

			// Verify tree structure
			assert_eq!(Directory::get_total_stake(), 1_550);
			assert_eq!(Root::get(), a_key);

			assert_eq!(a_stake.amount, 500);
			assert_eq!(a_stake.stakee, a.clone());
			assert_eq!(a_stake.parent, EMPTY_HASH);
			assert_eq!(a_stake.left, b_key);
			assert_eq!(a_stake.left_amount, 500);
			assert_eq!(a_stake.right, c_key);
			assert_eq!(a_stake.right_amount, 550);

			assert_eq!(b_stake.amount, 400);
			assert_eq!(b_stake.stakee, b.clone());
			assert_eq!(b_stake.parent, a_key);
			assert_eq!(b_stake.left, e_key);
			assert_eq!(b_stake.left_amount, 100);
			assert_eq!(b_stake.right, EMPTY_HASH);
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

			// Verify stakees
			assert_eq!(a_stakee, 500);
			assert_eq!(b_stakee, 400);
			assert_eq!(c_stakee, 300);
			assert_eq!(d_stakee, 200);
			assert_eq!(e_stakee, 100);
			assert_eq!(f_stakee, 50);

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

			// Refetch stakees
			a_stakee = <Stakees<Test>>::get(a.clone());
			b_stakee = <Stakees<Test>>::get(b.clone());
			c_stakee = <Stakees<Test>>::get(c.clone());
			d_stakee = <Stakees<Test>>::get(d.clone());
			e_stakee = <Stakees<Test>>::get(e.clone());
			f_stakee = <Stakees<Test>>::get(f.clone());

			// Verify tree integrity
			assert_eq!(Root::get(), a_key);
			assert_eq!(a_stake.amount, 500);
			assert_eq!(a_stake.stakee, a.clone());
			assert_eq!(a_stake.parent, EMPTY_HASH);
			assert_eq!(a_stake.left, b_key);
			assert_eq!(a_stake.left_amount, 500);
			assert_eq!(a_stake.right, d_key);
			assert_eq!(a_stake.right_amount, 250);

			assert_eq!(b_stake.amount, 400);
			assert_eq!(b_stake.stakee, b.clone());
			assert_eq!(b_stake.parent, a_key);
			assert_eq!(b_stake.left, e_key);
			assert_eq!(b_stake.left_amount, 100);
			assert_eq!(b_stake.right, EMPTY_HASH);
			assert_eq!(b_stake.right_amount, 0);

			assert_eq!(c_stake.amount, 0);
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

			// Verify stakees
			assert_eq!(a_stakee, 500);
			assert_eq!(b_stakee, 400);
			assert_eq!(c_stakee, 0);
			assert_eq!(d_stakee, 200);
			assert_eq!(e_stakee, 100);
			assert_eq!(f_stakee, 50);

			// Remove a leaf node
			Directory::unlock_stake(Origin::signed(f.clone()), 50, f.clone());
			Time::set_timestamp(50);
			Directory::unstake(Origin::signed(f.clone()), f.clone());
			assert_eq!(Directory::get_total_stake(), 1200);

			// Refetch stakes
			a_stake = <Stakes<Test>>::get(a_key);
			b_stake = <Stakes<Test>>::get(b_key);
			c_stake = <Stakes<Test>>::get(c_key);
			d_stake = <Stakes<Test>>::get(d_key);
			e_stake = <Stakes<Test>>::get(e_key);
			f_stake = <Stakes<Test>>::get(f_key);

			// Refetch stakees
			a_stakee = <Stakees<Test>>::get(a.clone());
			b_stakee = <Stakees<Test>>::get(b.clone());
			c_stakee = <Stakees<Test>>::get(c.clone());
			d_stakee = <Stakees<Test>>::get(d.clone());
			e_stakee = <Stakees<Test>>::get(e.clone());
			f_stakee = <Stakees<Test>>::get(f.clone());

			// Verify tree
			assert_eq!(Root::get(), a_key);
			assert_eq!(a_stake.amount, 500);
			assert_eq!(a_stake.stakee, a.clone());
			assert_eq!(a_stake.parent, EMPTY_HASH);
			assert_eq!(a_stake.left, b_key);
			assert_eq!(a_stake.left_amount, 500);
			assert_eq!(a_stake.right_amount, 200);

			assert_eq!(b_stake.amount, 400);
			assert_eq!(b_stake.stakee, b.clone());
			assert_eq!(b_stake.parent, a_key);
			assert_eq!(b_stake.left, e_key);
			assert_eq!(b_stake.left_amount, 100);
			assert_eq!(b_stake.right, EMPTY_HASH);
			assert_eq!(b_stake.right_amount, 0);

			assert_eq!(d_stake.amount, 200);
			assert_eq!(d_stake.stakee, d.clone());
			assert_eq!(d_stake.parent, a_key);
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

			assert_eq!(f_stake.amount, 0);
			assert_eq!(f_stake.parent, EMPTY_HASH);
			assert_eq!(f_stake.left, EMPTY_HASH);
			assert_eq!(f_stake.left_amount, 0);
			assert_eq!(f_stake.right, EMPTY_HASH);
			assert_eq!(f_stake.right_amount, 0);

			// Verify stakees
			assert_eq!(a_stakee, 500);
			assert_eq!(b_stakee, 400);
			assert_eq!(c_stakee, 0);
			assert_eq!(d_stakee, 200);
			assert_eq!(e_stakee, 100);
			assert_eq!(f_stakee, 0);

			// Remove a root node
			Directory::unlock_stake(Origin::signed(a.clone()), 500, a.clone());
			Time::set_timestamp(100);
			Directory::unstake(Origin::signed(a.clone()), a.clone());
			assert_eq!(Directory::get_total_stake(), 700);

			// Refetch stakes
			a_stake = <Stakes<Test>>::get(a_key);
			b_stake = <Stakes<Test>>::get(b_key);
			c_stake = <Stakes<Test>>::get(c_key);
			d_stake = <Stakes<Test>>::get(d_key);
			e_stake = <Stakes<Test>>::get(e_key);
			f_stake = <Stakes<Test>>::get(f_key);

			// Refetch stakees
			a_stakee = <Stakees<Test>>::get(a.clone());
			b_stakee = <Stakees<Test>>::get(b.clone());
			c_stakee = <Stakees<Test>>::get(c.clone());
			d_stakee = <Stakees<Test>>::get(d.clone());
			e_stakee = <Stakees<Test>>::get(e.clone());
			f_stakee = <Stakees<Test>>::get(f.clone());

			// Verify tree
			assert_eq!(Root::get(), e_key);
			assert_eq!(a_stake.amount, 0);
			assert_eq!(a_stake.parent, EMPTY_HASH);
			assert_eq!(a_stake.left, EMPTY_HASH);
			assert_eq!(a_stake.left_amount, 0);
			assert_eq!(a_stake.right_amount, 0);

			assert_eq!(b_stake.amount, 400);
			assert_eq!(b_stake.stakee, b.clone());
			assert_eq!(b_stake.parent, e_key);
			assert_eq!(b_stake.left, EMPTY_HASH);
			assert_eq!(b_stake.left_amount, 0);
			assert_eq!(b_stake.right, EMPTY_HASH);
			assert_eq!(b_stake.right_amount, 0);

			assert_eq!(d_stake.amount, 200);
			assert_eq!(d_stake.stakee, d.clone());
			assert_eq!(d_stake.parent, e_key);
			assert_eq!(d_stake.left, EMPTY_HASH);
			assert_eq!(d_stake.left_amount, 0);
			assert_eq!(d_stake.right, EMPTY_HASH);
			assert_eq!(d_stake.right_amount, 0);

			assert_eq!(e_stake.amount, 100);
			assert_eq!(e_stake.stakee, e.clone());
			assert_eq!(e_stake.parent, EMPTY_HASH);
			assert_eq!(e_stake.left, b_key);
			assert_eq!(e_stake.left_amount, 400);
			assert_eq!(e_stake.right, d_key);
			assert_eq!(e_stake.right_amount, 200);

			assert_eq!(f_stake.amount, 0);
			assert_eq!(f_stake.parent, EMPTY_HASH);
			assert_eq!(f_stake.left, EMPTY_HASH);
			assert_eq!(f_stake.left_amount, 0);
			assert_eq!(f_stake.right, EMPTY_HASH);
			assert_eq!(f_stake.right_amount, 0);

			// Verify stakees
			assert_eq!(a_stakee, 0);
			assert_eq!(b_stakee, 400);
			assert_eq!(c_stakee, 0);
			assert_eq!(d_stakee, 200);
			assert_eq!(e_stakee, 100);
			assert_eq!(f_stakee, 0);
		})
	}

	#[test]
	pub fn test_update_stake() {
		let a = alice();
		execute(|| {
			Balance::make_free_balance_be(&a, 1_000);

			// Add a stake
			let key = Directory::get_key(a.clone(), a.clone());
			Directory::add_stake(Origin::signed(a.clone()), 100, a.clone()).expect("Failed to create a stake");

			assert_eq!(Balance::free_balance(a.clone()), 900);
			assert_eq!(<Stakes<Test>>::get(key).amount, 100);

			// Add an additional amount to stake
			Directory::add_stake(Origin::signed(a.clone()), 100, a.clone()).expect("Failed to create a stake");

			assert_eq!(Balance::free_balance(a.clone()), 800);
			assert_eq!(<Stakes<Test>>::get(key).amount, 200);
		})
	}

	#[test]
	pub fn test_unstake() {
		let a = alice();
		let b = bob();
		execute(|| {
			Time::set_timestamp(0); // Initialize time.

			Balance::make_free_balance_be(&a, 1_000);
			Balance::make_free_balance_be(&b, 1_000);

			// Alice stakes with bob as stakee
			let key = Directory::get_key(a.clone(), b.clone());
			Directory::add_stake(Origin::signed(a.clone()), 100, b.clone()).expect("Failed to create a stake");

			assert_eq!(Balance::free_balance(a.clone()), 900);
			assert_eq!(<Stakes<Test>>::get(key).amount, 100);

			// Unlock tokens that were staked
			Directory::unlock_stake(Origin::signed(a.clone()), 50, b.clone());

			// check unlock amount
			let unlock = <Unlockings<Test>>::get(key);
			assert_eq!(unlock.amount, 50);
			assert_eq!(unlock.unlock_at, 5);

			// Attempt to withdraw unlock before unlock_at period passed
			Directory::unstake(Origin::signed(a.clone()), b.clone())
				.expect_err("Should not be able to withdraw an unlock before unlock period expired");

			// Set time past unlock period and withdraw unlock
			Time::set_timestamp(10);
			Directory::unstake(Origin::signed(a.clone()), b.clone());

			// Check that unlock is withdrawn and removed and that balances is restored
			assert_eq!(<Unlockings<Test>>::contains_key(key), false);
			assert_eq!(Balance::free_balance(a.clone()), 950);

			// check that stake is updated
			assert_eq!(<Stakes<Test>>::get(key).amount, 50);
		})
	}

	#[test]
	pub fn test_scan() {
		let a = alice();
		let b = bob();
		execute(|| {
			Time::set_timestamp(0); // Initialize time.

			Balance::make_free_balance_be(&a, 1_000);
			Balance::make_free_balance_be(&b, 1_000);

			// Alice stakes with bob as stakee
			let a_key = Directory::get_key(a.clone(), a.clone());
			Directory::add_stake(Origin::signed(a.clone()), 1, a.clone()).expect("Failed to create a stake");

			let b_key = Directory::get_key(b.clone(), b.clone());
			Directory::add_stake(Origin::signed(b.clone()), 1, b.clone()).expect("Failed to create a stake");

			assert_eq!(Directory::get_total_stake(), 2);

			let selected_1 = Directory::scan(BalanceOf::<Test>::max_value());
			assert_eq!(selected_1.unwrap(), a.clone());

			let selected_0 = Directory::scan((0 as u32).into());
			assert_eq!(selected_0.unwrap(), b.clone());
		})
	}
}
