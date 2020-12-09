use frame_support::{decl_error, decl_module, decl_storage, ensure, traits::{WithdrawReason, Currency, ExistenceRequirement, Time}, weights::Weight};
use frame_system::ensure_signed;
use codec::{Decode, Encode};
use sp_io::hashing::{keccak_256};
use sp_core::U256;
use sp_runtime::{DispatchError};
//frame_support::debug::native::debug!("called by {:?}", who);

const UNLOCK_DURATION: u32 = 5;
const EMPTY_HASH : [u8; 32] = [0u8; 32];

mod default_weights;

pub trait WeightInfo {
<<<<<<< Updated upstream
	fn add_node() -> Weight;
=======
	fn push() -> Weight;
	fn pull() -> Weight;
	fn take() -> Weight;
>>>>>>> Stashed changes
}

type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;
type Timestamp<T> = <<T as Trait>::Time as Time>::Moment;
type Hash = [u8; 32];

#[derive(Encode, Decode, Default, Debug, Clone)]
pub struct Primary {
	value: Hash,
}

#[derive(Encode, Decode, Default, Debug)]
<<<<<<< Updated upstream
pub struct SumTree {
	amount : u128,

    left_amount: u128, 
	right_amount: u128,
	
    parent: Hash,
    left : Hash,
    right : Hash,
}

#[derive(Encode, Decode, Default, Debug)]
pub struct Unlock {
	amount: u128,
    unlock_at: u128,
=======
pub struct Stakee<Balance> {
	amount : Balance,
}

#[derive(Encode, Decode, Default, Clone, Debug)]
pub struct Stake<AccountId, Balance, Timestamp> {
    before: Balance,
	after: Balance,

	amount: Balance ,
	delay: Timestamp,

	stakee: AccountId,

    parent: Hash,
    left: Primary,
    right: Primary,
}

#[derive(Encode, Decode, Default, Debug)]
pub struct Pending<AccountId, Balance, Timestamp> {
	amount: Balance, // Amount of stake unlocking
	stakee: AccountId,
	expire: Timestamp, // Block number stake becomes withdrawable

>>>>>>> Stashed changes
}

decl_storage! {
	trait Store for Module<T: Trait> as SyloDirectory {
		// Stakers (map hash -> stake)
<<<<<<< Updated upstream
		pub Stakes get(fn stakes): map hasher(blake2_128_concat) Hash => SumTree;

		// Unlockings (map hash -> unlock)
		pub Unlockings get(fn unlockings): map hasher(blake2_128_concat) Hash => Unlock;
=======
		pub Stakes get(fn stakes): map hasher(blake2_128_concat) Hash => Stake<T::AccountId, BalanceOf<T>, Timestamp<T>>;

		// Stakees (map accountid -> balance)
		pub Stakees get(fn stakees): map hasher(blake2_128_concat) T::AccountId => Stakee<BalanceOf<T>>;

		// Unlockings (map hash -> unlock)
		pub Pendings get(fn pendings): map hasher(blake2_128_concat) Hash => Pending<T::AccountId, BalanceOf<T>, Timestamp<T>>;
>>>>>>> Stashed changes
		
		// Root (hash)
		pub Root get(fn root): Primary;
	}
}

pub trait Trait: frame_system::Trait {
    type Currency: Currency<Self::AccountId>;
    type Time: Time;
    type WeightInfo: WeightInfo;
}

decl_error! {
	pub enum Error for Module<T: Trait> {
		InvalidAmount,
<<<<<<< Updated upstream

=======
		NotExpired,
>>>>>>> Stashed changes
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin, system = frame_system {
		#[weight = T::WeightInfo::add_node()]
		fn add_node(origin, amount: u128) {
			// Sanity checks
			ensure!(amount >= 0, Error::<T>::InvalidAmount);
			
			// Fetch staker and key material
			let address = ensure_signed(origin)?;
			let key = Self::get_key(address.clone(), address.clone());

<<<<<<< Updated upstream
			let mut node: SumTree = Stakes::get(key);
			node.amount += amount;
			
			let mut current_node: SumTree = Root::get()
			// Search the tree for a place to insert
			while current_node.amount > amount {
				current_node = current_node.right
			}


		}

		// Swap the children in a node
		#[weight = 0] 
		fn swap_children(key: Hash) {
			node : SumTree = Stakes::get(key);
			buffer : SumTree = node.left;
			buffer_amount : u128 = node.left_amount;
			node.left = node.right;
			node.left = node.right_amount;
			node.right = buffer;
			node.right_amount = buffer_amount;
			Stakes::insert(key, node);
		}







=======
		// Add a stake, transfer balance
		#[weight = T::WeightInfo::push()]
		fn push(origin, stakee: T::AccountId, amount: BalanceOf<T>) {
			let staker = ensure_signed(origin)?;
			Self::more(staker.clone(), stakee, amount);
			T::Currency::withdraw(&staker, amount, WithdrawReason::Fee.into(), ExistenceRequirement::KeepAlive)?;
		} 

		// Unlock a pulling
		#[weight = T::WeightInfo::pull()]
		fn pull(origin, stakee: T::AccountId, amount: BalanceOf<T>) {
			let staker = ensure_signed(origin)?;
			let key = &mut Self::key(staker.clone(), stakee.clone());
			let mut stake = <Stakes<T>>::get(key.clone());

			ensure!(stake.amount != (0 as u32).into(), Error::<T>::InvalidAmount);
			ensure!(stake.amount >= amount, Error::<T>::InvalidAmount);

			Self::lift(key, amount, stakee, true); // take AWAY

			if stake.amount == (0 as u32).into() {
				let mut pivot: Primary = Self::turn(key, stake.clone());
				let child;
				if stake.before > stake.after {
					child = stake.left.clone();
				}
				else {
					child = stake.right.clone();
				}

				if Self::nope(child.clone()) {
					Self::kill(&mut pivot.clone())
				}
				else {
					let mut last: Primary = child;
					let mut location: Hash = Self::name(last.clone());
					let mut current = <Stakes<T>>::get(location);

					loop {
						let next;
						if current.before > current.after {
							next = current.left.clone();
						}
						else {
							next = current.right.clone();
						}

						if Self::nope(next.clone()) {
							break;
						}

						last = next.clone();
						location = Self::name(last.clone());
						current = <Stakes<T>>::get(location);
					}

					let direct = current.parent;
					pivot.value = last.value; // copy
					
					current.parent = stake.parent;
					<Stakes<T>>::insert(location, current.clone());

					if direct != key.clone() {
						Self::fixr(key.clone(), location, location);
						Self::fixl(key.clone(), location, location);

						stake.parent = direct;
						last.value = key.clone();
						Self::step(key, amount, current.parent, true); // take away
						Self::kill(&mut last);
					}
					else if Self::name(stake.left) == location {
						Self::fixr(key.clone(), location, location);
					}
					else {
						Self::fixr(key.clone(), location, location);
					}
				}

				<Stakes<T>>::remove(key.clone());
			}

			let expire = T::Time::now() + UNLOCK_DURATION.into();
			let mut pending = <Pendings<T>>::get(key.clone());
			if pending.expire < expire {
				pending.expire = expire;
			}

			pending.amount += amount;
			<Pendings<T>>::insert(key, pending);
		}

		// Unlock a pulling
		#[weight = T::WeightInfo::take()]
		fn take(origin, stakee: T::AccountId, amount: BalanceOf<T>) {
			let staker = ensure_signed(origin)?;
			Self::pend(staker.clone(), stakee, amount);
			T::Currency::deposit_into_existing(&staker, amount);
>>>>>>> Stashed changes
		}
	}
}

impl<T: Trait> Module<T> {

	// The weight of the stakee in the stakee map
	fn heft(stakee : T::AccountId) -> BalanceOf<T> {
		<Stakees<T>>::get(stakee).amount
	}

	// Unwrap value of primary 
	fn name(primary: Primary) -> Hash {
		primary.value
	}

	// Key for a primary
	fn key(staker: T::AccountId, stakee: T::AccountId) -> Hash {
		let mut vec_bytes = staker.encode();
		vec_bytes.append(&mut stakee.encode());
		keccak_256(vec_bytes.as_slice())
	}
<<<<<<< Updated upstream
=======

	// Overwrite the primary from one hash to another
	fn copy(primary: &mut Primary, other: Primary) {
		primary.value = other.value;
	}

	// 'Nullify' the value of a primary
	fn kill(primary: &mut Primary) {
		primary.value = EMPTY_HASH;
	}

	// Is this primary 'null'?
	fn nope(primary: Primary) -> bool {
		primary.value == EMPTY_HASH
	}

	// Total weight of left + right + amount of root stake
	fn have() -> BalanceOf<T> {
		if Self::nope(Root::get()) {
			return (0 as u32).into();
		}

		let stake = <Stakes<T>>::get(Self::name(Root::get()));
		stake.before + stake.after + stake.amount
	}

	// Select the node that matches the provided key (when the key isn't found select right)
	fn turn(key: &mut Hash, stake: Stake<T::AccountId, BalanceOf<T>, Timestamp<T>>) -> Primary {
		if stake.parent == EMPTY_HASH {
			return Root::get();
		}
		let parent = <Stakes<T>>::get(stake.parent);
		if &mut Self::name(parent.left.clone()) == key {
			return parent.left;
		} else {
			return parent.right;
		}
	}

	fn step(key: &mut Hash, amount: BalanceOf<T>, root: Hash, flag: bool) {
		let stake = <Stakes<T>>::get(key.clone());
		while stake.parent != root {
			let parent_key: Hash = stake.parent;
			let mut parent_stake = <Stakes<T>>::get(parent_key);
			if &mut Self::name(parent_stake.left.clone()) == key {
				if flag {
					parent_stake.before -= amount;
				} else {
					parent_stake.before += amount;
				}
			} else {
				if flag {
					parent_stake.after -= amount;
				} else {
					parent_stake.after += amount;
				}
			}
			<Stakes<T>>::insert(parent_key, parent_stake);	
			*key = parent_key;
		}
		
	}

	// Lift the amoutn of a node on local and global, then step that amount up the tree
	fn lift(key: &mut Hash, amount: BalanceOf<T>, stakee_key: T::AccountId, flag: bool) {
		let mut stake = <Stakes<T>>::get(key.clone());
		let mut local = stake.amount;
		if flag {
			local -= amount;
		} else {
			local += amount;
		}
		stake.amount = local;
		<Stakes<T>>::insert(key.clone(), stake);

		let mut stakee = <Stakees<T>>::get(stakee_key.clone());
		if flag {
			stakee.amount -= amount;
		} else {
			stakee.amount += amount;
		}

		<Stakees<T>>::insert(stakee_key, stakee);
		Self::step(key, amount, EMPTY_HASH, false);
	}

	fn more(staker: T::AccountId, stakee: T::AccountId, amount: BalanceOf<T>) -> Result<(), DispatchError>{
		let key = Self::key(staker.clone(), stakee.clone());
		let mut stake = <Stakes<T>>::get(key);

		if stake.amount == (0 as u32).into() {
			ensure!(amount != (0 as u32).into(), Error::<T>::InvalidAmount);
			let mut parent = EMPTY_HASH;
			let mut primary = Root::get();

			while !Self::nope(primary.clone()) {
				parent = Self::name(primary.clone());
				let current = <Stakes<T>>::get(parent);
				if current.before < current.after {
					primary = current.left;
				} else {
					primary = current.right;
				}
			}

			stake.parent = parent;
			stake.stakee = stakee.clone();
			<Stakes<T>>::insert(key, stake); //update

			primary.value = key; //Self::copy(primary, staker, stakee);
		}

		Self::lift(&mut key.clone(), amount, stakee.clone(), false);
		Ok(())
	}

	fn pend(staker: T::AccountId , stakee: T::AccountId, amount: BalanceOf<T>) -> Result<(), DispatchError> {
		//let pending = <Pendings<T>>::get();
		let key = Self::key(staker.clone(), stakee.clone());
		let mut pending = <Pendings<T>>::get(key);
		ensure!(pending.expire <= (T::Time::now() + UNLOCK_DURATION.into()), Error::<T>::NotExpired);
		ensure!(stakee == pending.stakee, Error::<T>::NotExpired);

		// Whole stake is being removed
		if pending.amount == amount {
			<Pendings<T>>::remove(key);
		} else {
			// TODO error types
			ensure!(pending.amount > amount, Error::<T>::NotExpired);
			pending.amount -= amount;
			<Pendings<T>>::insert(key, pending);
		}
		Ok(())
	}

	fn stop(staker: T::AccountId, stakee: T::AccountId, amount: BalanceOf<T>) {
		Self::pend(staker.clone(), stakee.clone(), amount.clone());
		Self::more(staker, stakee, amount);
	}

	fn fixr(stake_key: Hash, location: Hash, current_key: Hash) {
		let stake = <Stakes<T>>::get(stake_key);
		if Self::nope(stake.right.clone()) {
			return
		}
		let mut current = <Stakes<T>>::get(current_key);
		let stake_right_key = Self::name(stake.right.clone());
		let mut stake_right = <Stakes<T>>::get(stake_right_key);
		stake_right.parent = location;
		current.right = stake.right; // copy
		current.after = stake.after;

		<Stakes<T>>::insert(stake_right_key, stake_right);
		<Stakes<T>>::insert(current_key, current);
	}

	fn fixl(stake_key: Hash, location: Hash, current_key: Hash) {
		let stake = <Stakes<T>>::get(stake_key);
		if Self::nope(stake.left.clone()) {
			return
		}
		let mut current = <Stakes<T>>::get(current_key);
		let stake_left_key = Self::name(stake.left.clone());
		let mut stake_left = <Stakes<T>>::get(stake_left_key);
		stake_left.parent = location;
		current.left = stake.left; // copy
		current.before = stake.before;

		<Stakes<T>>::insert(stake_left_key, stake_left);
		<Stakes<T>>::insert(current_key, current);
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
			Directory::push(Origin::signed(a.clone()), a.clone(), 100)
				.expect("Failed to create a stake");

			// Stake amount is withdrawn from Alice's account
			assert_eq!(Balance::free_balance(a.clone()), 900);

			let key = Directory::key(a.clone(), a.clone());
			let stake = <Stakes<Test>>::get(key);

			// First stake in tree, should be assigned as root
			assert_eq!(key, Directory::name(Root::get())); 
			assert_eq!(stake.parent, EMPTY_HASH);

			assert_eq!(stake.amount, 100);
			assert_eq!(stake.before , 0);
			assert_eq!(stake.after , 0);

			// Stake was delegated to Alice
			assert_eq!(stake.stakee, a.clone()); 

			// Only stake in tree, thus has no children
			assert_eq!(Directory::name(stake.left), EMPTY_HASH); 
			assert_eq!(Directory::name(stake.right), EMPTY_HASH); 

			// Stake is recorded in stakees
			let stakee_balance = <Stakees<Test>>::get(a.clone()).amount;
			assert_eq!(stakee_balance, 100);
		})
	}

	#[test]
	pub fn test_basic_unstake() {
		let a = alice();
		execute(|| {
			// Alice has an initial balance of 1000
			Balance::make_free_balance_be(&a, 1_000);

			let key = Directory::key(a.clone(), a.clone());
			// Deposit 100 into the escrow
			Directory::push(Origin::signed(a.clone()), a.clone(), 500)
				.expect("Failed to create a stake");

			// Stake amount is withdrawn from Alice's account
			assert_eq!(Balance::free_balance(a.clone()), 500);

			// Unlock part of stake
			Directory::pull(Origin::signed(a.clone()), a.clone(), 250);

			// Check unlocking
			let unlocking = <Pendings<Test>>::get(key);
			assert_eq!(unlocking.amount, 250);
			assert_eq!(unlocking.expire, 5);

			// Check stake
			let stake = <Stakes<Test>>::get(key);
			assert_eq!(stake.amount, 250);

			// Set time past stake unlock period
			Time::set_timestamp(10); 

			// Unstake
			Directory::take(Origin::signed(a.clone()), a.clone(), 250);
			assert_eq!(Balance::free_balance(a.clone()), 750);
		})
	}


>>>>>>> Stashed changes
}