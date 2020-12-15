use frame_support::{decl_error, decl_module, decl_storage, ensure, traits::{WithdrawReason, Currency, ExistenceRequirement, Time}, weights::Weight};
use frame_system::{ensure_root, ensure_signed};
use codec::{Decode, Encode};
use sp_io::hashing::{keccak_256};
use sp_runtime::{DispatchError, traits::Bounded};
use sp_std::vec::Vec;

type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;
type Timestamp<T> = <<T as Trait>::Time as Time>::Moment;

pub trait Trait: frame_system::Trait {
    type Currency: Currency<Self::AccountId>;
    type Time: Time;
    type WeightInfo: WeightInfo;
}

mod default_weights;
pub trait WeightInfo {
	fn add_vendor() -> Weight;
}

#[derive(Encode, Decode, Default, Debug, Clone)]
pub struct Transaction<Balance, Timestamp> {
	amount: Balance, // Funds
	last_transferred: Timestamp, // Time at which funds were last transferred
}

decl_storage! {
	trait Store for Module<T: Trait> as SyloSmartMoney {
		pub ExpirationDuration get(fn expirationduration): Timestamp<T>;
		pub Vendors get(fn vendors): map hasher(blake2_128_concat) T::AccountId => ();
		pub Transactions get(fn transactions): map hasher(blake2_128_concat) T::AccountId => Vec<Transaction<BalanceOf<T>, Timestamp<T>>>;
	}
}


decl_error! {
	pub enum Error for Module<T: Trait> {
		/// Invalid vendor recipient
		VendorNotWhitelisted,
		/// Not enough unexpired funds
		InsufficientUnexpiredFunds,
		/// RemovedIncorrectFunds
		RemovedIncorrectFunds,
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin, system = frame_system {

		// Add a vendor to the whitelist
		#[weight = T::WeightInfo::add_vendor()]
		fn add_vendor(origin, vendor: T::AccountId) {
			ensure_root(origin)?;
			<Vendors<T>>::insert(vendor, ());
		}

		// Remove a vendor from the whitelist
		#[weight = T::WeightInfo::add_vendor()]
		fn remove_vendor(origin, vendor: T::AccountId) {
			ensure_root(origin)?;
			<Vendors<T>>::remove(vendor);
		}

		// Create a recorded transaction
		#[weight = T::WeightInfo::add_vendor()]
		fn transfer(origin, to: T::AccountId, amount: BalanceOf<T>) {
			let from = ensure_signed(origin)?;
			ensure!(<Vendors<T>>::contains_key(to.clone()), Error::<T>::VendorNotWhitelisted);

			// Runtime module transaction
			Self::remove_funds(from.clone(), amount)?;
			Self::add_funds(to.clone(), amount)?;

			// Chain transaction
			T::Currency::transfer(&from, &to, amount,ExistenceRequirement::KeepAlive)?;
		}

		// Faucet allowing root to fund accounts
		#[weight = T::WeightInfo::add_vendor()]
		fn faucet(origin, account: T::AccountId, amount: BalanceOf<T>) {
			ensure_root(origin)?;

			Self::add_funds(account.clone(), amount)?;
			T::Currency::deposit_into_existing(&account, amount)?;
			
		}

		// Set expiration period at which after all funds are locked
		#[weight = T::WeightInfo::add_vendor()]
		fn set_expiration(origin, expiration_duration: Timestamp<T>) {
			ensure_root(origin)?;
			<ExpirationDuration<T>>::put(expiration_duration);
		}

	}
}

impl<T: Trait> Module<T> {

	// Add funds to an account
	pub fn add_funds(account: T::AccountId, amount: BalanceOf<T>) -> Result<(), Error<T>> {
		let mut tx_set = <Transactions<T>>::get(&account);
		tx_set.push(Transaction::<BalanceOf<T>, Timestamp<T>> {
			amount: amount,
			last_transferred: T::Time::now(),
		});
		tx_set.sort_by(|a, b| a.last_transferred.cmp(&b.last_transferred));
		<Transactions<T>>::insert(account, tx_set);
		Ok(())

	}

	// Removes funds from account
	pub fn remove_funds(account: T::AccountId, amount: BalanceOf<T>) -> Result<(), Error<T>> {
		// Fetch total unexpired funds to ensure funds can be removed
		let unexpired_funds = Self::total_unexpired_funds(account.clone());
		ensure!(unexpired_funds >= amount, Error::<T>::InsufficientUnexpiredFunds);

		let mut current_removed = BalanceOf::<T>::from(0 as u32);
		let mut tx_set = <Transactions<T>>::get(account.clone());
		let now = T::Time::now();
		for mut tx in tx_set.iter_mut() {
			// Transaction has expired
			if tx.last_transferred + <ExpirationDuration<T>>::get() < now { 
				continue;
			} else {
				if (amount - current_removed) > tx.amount { // complete drain transaction
					current_removed += tx.amount;
					tx.amount = BalanceOf::<T>::from(0 as u32);
				} else { // partial drain transaction (last)
					let remaining = amount - current_removed;
					tx.amount -= remaining; 
					current_removed += remaining;
					break;
				}
			}
		}

		ensure!(current_removed == amount, Error::<T>::RemovedIncorrectFunds);
		<Transactions<T>>::insert(account, tx_set);
		Ok(())	

	}

	// Total funds expired and unexpired 
	pub fn total_funds(account: T::AccountId) -> BalanceOf<T> {
		let mut acc = <BalanceOf<T>>::from(0 as u32);
		for tx in <Transactions<T>>::get(account) {
				acc += tx.amount
		}
		acc
	}

	// Total unexpired funds
	pub fn total_unexpired_funds(account: T::AccountId) -> BalanceOf<T> {
		let mut acc = <BalanceOf<T>>::from(0 as u32);
		let now = T::Time::now();
		for tx in <Transactions<T>>::get(account) {
			if tx.last_transferred + <ExpirationDuration<T>>::get() > now {
				acc += tx.amount
			}
		}
		acc
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

	type SmartMoney = Module<Test>;
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
		sp_io::TestExternalities::from(
			frame_system::GenesisConfig::default()
				.build_storage::<Test>()
				.unwrap()
		).execute_with(execute)
	}

	#[test]
	pub fn test_add_vendor() {
		let a = alice();
		let b = bob();
		execute(|| {
			// Add with root
			SmartMoney::add_vendor(Origin::root(), a.clone())
				.expect("Could not add vendor using privileged root");
			assert_eq!(<Vendors<Test>>::contains_key(a.clone()), true);

			// Attempt to add without root
			SmartMoney::add_vendor(Origin::signed(b.clone()),  b.clone())
				.expect_err("Added vendor without priviledged root");
			assert_eq!(<Vendors<Test>>::contains_key(b.clone()), false);
		})
	}

	#[test]
	pub fn test_remove_vendor() {
		let a = alice();
		execute(|| {
			// Add vendor 
			SmartMoney::add_vendor(Origin::root(), a.clone())
				.expect("Could not add vendor using privileged root");
			assert_eq!(<Vendors<Test>>::contains_key(a.clone()), true);

			// Attempt to remove without root
			SmartMoney::remove_vendor(Origin::signed(a.clone()), a.clone())
				.expect_err("Removed vendor without priviledged root");
			assert_eq!(<Vendors<Test>>::contains_key(a.clone()), true);

			// Remove with root
			SmartMoney::remove_vendor(Origin::root(), a.clone())
				.expect("Could not remove vendor using privileged root");
			assert_eq!(<Vendors<Test>>::contains_key(a.clone()), false);
		})
	}

	#[test]
	pub fn test_add_and_remove() {
		let a = alice();
		execute(|| {

			let now = Time::now();
			<ExpirationDuration<Test>>::put(5);
			Time::set_timestamp(0);
			// Expired funds
			SmartMoney::add_funds(a.clone(), 1);
			SmartMoney::add_funds(a.clone(), 2);
			SmartMoney::add_funds(a.clone(), 3);
			// Unexpired funds
			Time::set_timestamp(10);
			SmartMoney::add_funds(a.clone(), 4);
			SmartMoney::add_funds(a.clone(), 5);
			SmartMoney::add_funds(a.clone(), 6);


			SmartMoney::remove_funds(a.clone(), 4);
			assert_eq!(SmartMoney::total_unexpired_funds(a.clone()), BalanceOf::<Test>::from(11 as u32));
			assert_eq!(SmartMoney::total_funds(a.clone()), BalanceOf::<Test>::from(17 as u32));

			//Attempt to remove more unexpired than account has
			SmartMoney::remove_funds(a.clone(), 12).expect_err("Removed more funds than account has");

			// Remove all funds
			SmartMoney::remove_funds(a.clone(), 11);
			assert_eq!(SmartMoney::total_unexpired_funds(a.clone()), BalanceOf::<Test>::from(0 as u32));
			assert_eq!(SmartMoney::total_funds(a.clone()), BalanceOf::<Test>::from(6 as u32));

		})
	}

	#[test]
	pub fn test_total_unexpired_and_expired() {
		let a = alice();
		execute(|| {

			let now = Time::now();
			<ExpirationDuration<Test>>::put(5);
			Time::set_timestamp(0);
			// Expired funds
			SmartMoney::add_funds(a.clone(), 1);
			SmartMoney::add_funds(a.clone(), 2);
			SmartMoney::add_funds(a.clone(), 3);
			// Unexpired funds
			Time::set_timestamp(10);
			SmartMoney::add_funds(a.clone(), 4);
			SmartMoney::add_funds(a.clone(), 5);
			SmartMoney::add_funds(a.clone(), 6);

			assert_eq!(SmartMoney::total_unexpired_funds(a.clone()), BalanceOf::<Test>::from(15 as u32));
			assert_eq!(SmartMoney::total_funds(a.clone()), BalanceOf::<Test>::from(21 as u32));
		})
	}

	#[test]
	pub fn test_transfer() {
		let a = alice();
		let b = bob();
		execute(|| {

			// Add a vendor
			SmartMoney::add_vendor(Origin::root(), b.clone())
				.expect("Could not add vendor using privileged root");
			assert_eq!(<Vendors<Test>>::contains_key(b.clone()), true);

			let now = Time::now();
			<ExpirationDuration<Test>>::put(5);
			Time::set_timestamp(0);
			// Expired funds Alice
			SmartMoney::add_funds(a.clone(), 1);
			SmartMoney::add_funds(a.clone(), 2);
			SmartMoney::add_funds(a.clone(), 3);
			// Expired funds Bob 
			SmartMoney::add_funds(b.clone(), 1);
			SmartMoney::add_funds(b.clone(), 2);
			SmartMoney::add_funds(b.clone(), 3);

			Time::set_timestamp(10);
			// Unexpired funds Alice
			SmartMoney::add_funds(a.clone(), 4);
			SmartMoney::add_funds(a.clone(), 5);
			SmartMoney::add_funds(a.clone(), 6);
			// Unexpired funds Bob
			SmartMoney::add_funds(b.clone(), 4);
			SmartMoney::add_funds(b.clone(), 5);
			SmartMoney::add_funds(b.clone(), 6);

			// Attempt to transfer more than avaliable
			SmartMoney::transfer(Origin::signed(a.clone()), b.clone(), 20)
				.expect_err("Transfered a balance greater than what was avaliable");

			assert_eq!(SmartMoney::total_unexpired_funds(a.clone()), BalanceOf::<Test>::from(15 as u32));
			assert_eq!(SmartMoney::total_funds(a.clone()), BalanceOf::<Test>::from(21 as u32));
			assert_eq!(SmartMoney::total_unexpired_funds(b.clone()), BalanceOf::<Test>::from(15 as u32));
			assert_eq!(SmartMoney::total_funds(b.clone()), BalanceOf::<Test>::from(21 as u32));

			// Normal transaction with registered vendor
			SmartMoney::transfer(Origin::signed(a.clone()), b.clone(), 5);

			assert_eq!(SmartMoney::total_unexpired_funds(a.clone()), BalanceOf::<Test>::from(10 as u32));
			assert_eq!(SmartMoney::total_funds(a.clone()), BalanceOf::<Test>::from(16 as u32));
			assert_eq!(SmartMoney::total_unexpired_funds(b.clone()), BalanceOf::<Test>::from(20 as u32));
			assert_eq!(SmartMoney::total_funds(b.clone()), BalanceOf::<Test>::from(26 as u32));
		})
	}

}