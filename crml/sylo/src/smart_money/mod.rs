use codec::{Decode, Encode};
use frame_support::{
	decl_error, decl_module, decl_storage, ensure,
	traits::{Currency, ExistenceRequirement, Time, WithdrawReason},
	weights::Weight,
};
use frame_system::{ensure_root, ensure_signed};
use sp_io::hashing::keccak_256;
use sp_runtime::{traits::Bounded, DispatchError};
use sp_std::vec::Vec;
//use prml_support::MultiCurrencyAccounting;

//cennzx
use core::convert::TryFrom;
use frame_support::{decl_event, Parameter, StorageDoubleMap};
use prml_support::MultiCurrencyAccounting;
use sp_runtime::{
	traits::{AtLeast32BitUnsigned, Member, One, Saturating, Zero},
	DispatchResult, SaturatedConversion,
};
use sp_std::prelude::*;

// Default constants
// const DEFAULT_EXPIRATION_DURATION: u8 = 5;
// const DEFAULT_ASSET_ID: u8 = CENTRAPAY_ASSET_ID;

/// Alias for the multi-currency provided balance type
type BalanceOf<T> = <<T as Trait>::MultiCurrency as MultiCurrencyAccounting>::Balance;
type Timestamp<T> = <<T as Trait>::Time as Time>::Moment;

pub trait Trait: frame_system::Trait {
	/// Currency (single spending)
	//type Currency: Currency<Self::AccountId>;
	/// Timestamps
	type Time: Time;
	/// Weight of operation
	type WeightInfo: WeightInfo;
	/// Type for identifying assets
	type AssetId: Parameter + Member + AtLeast32BitUnsigned + Default + Copy + Into<u64>;
	/// Something which can provide multi currency asset management
	type MultiCurrency: MultiCurrencyAccounting<AccountId = Self::AccountId, CurrencyId = Self::AssetId>;
}

mod default_weights;
pub trait WeightInfo {
	fn add_vendor() -> Weight;
	fn remove_vendor() -> Weight;
	fn transfer() -> Weight;
	fn mint() -> Weight;
	fn set_expiration() -> Weight;
	fn add_asset() -> Weight;
	fn remove_asset() -> Weight;
}

#[derive(Encode, Decode, Default, Debug, Clone)]
pub struct Transaction<Balance, Timestamp, AssetId> {
	amount: Balance,             // Funds
	last_transferred: Timestamp, // Time at which funds were last transferred
	asset_id: AssetId,           // Asset that was used in the transaction
}

decl_storage! {
	trait Store for Module<T: Trait> as SyloSmartMoney {
		// Whitelisted AssetIds
		pub Assets get(fn assets): map hasher(blake2_128_concat) T::AssetId => ();
		// Delay period during which funds are spendable, after which funds are softlocked
		pub ExpirationDuration get(fn expirationduration): map hasher(blake2_128_concat) T::AssetId => Timestamp<T>;
		// Whitelisted vendors
		pub Vendors get(fn vendors): map hasher(blake2_128_concat) T::AccountId => ();
		// Tracking account transactions
		pub Transactions get(fn transactions): map hasher(blake2_128_concat) T::AccountId => Vec<Transaction<BalanceOf<T>, Timestamp<T>, T::AssetId>>;
	}
}

decl_error! {
	pub enum Error for Module<T: Trait> {
		/// Invalid vendor recipient
		VendorNotWhitelisted,
		/// Not enough unexpired funds
		InsufficientUnexpiredFunds,
		/// RemovedIncorrectFunds (DEV)
		RemovedIncorrectFunds,
		/// Invalid spending asset
		AssetNotWhitelisted,
		/// Transaction failed
		TransactionFailed,
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
		#[weight = T::WeightInfo::remove_vendor()]
		fn remove_vendor(origin, vendor: T::AccountId) {
			ensure_root(origin)?;
			<Vendors<T>>::remove(vendor);
		}

		// Create a recorded transaction
		#[weight = T::WeightInfo::transfer()]
		fn transfer(origin, to: T::AccountId, asset_id: T::AssetId, amount: BalanceOf<T>) {
			let from = ensure_signed(origin)?;
			ensure!(<Vendors<T>>::contains_key(to.clone()), Error::<T>::VendorNotWhitelisted);

			// Runtime module transaction
			Self::remove_funds(from.clone(), asset_id, amount)?;
			Self::add_funds(to.clone(), asset_id, amount)?;

			// Chain transaction
			T::MultiCurrency::transfer(&from, &to, Some(asset_id), amount, ExistenceRequirement::KeepAlive);
		}

		// Add a spendable asset
		#[weight = T::WeightInfo::add_asset()]
		fn add_asset(origin, asset_id: T::AssetId) {
			ensure_root(origin)?;
			<Assets<T>>::insert(asset_id, ());
		}

		// Add a spendable asset
		#[weight = T::WeightInfo::remove_asset()]
		fn remove_asset(origin, asset_id: T::AssetId) {
			ensure_root(origin)?;
			<Assets<T>>::remove(asset_id);
		}

		// Mint funds to account using root
		#[weight = T::WeightInfo::mint()]
		fn mint(origin, account: T::AccountId, asset_id: T::AssetId, amount: BalanceOf<T>) {
			ensure_root(origin)?;
			Self::add_funds(account.clone(), asset_id, amount)?;
		}

		// Set expiration period at which after all funds are locked
		#[weight = T::WeightInfo::set_expiration()]
		fn set_expiration(origin, asset_id: T::AssetId, expiration_duration: Timestamp<T>) {
			ensure_root(origin)?;
			<ExpirationDuration<T>>::insert(asset_id, expiration_duration);
		}
	}
}

impl<T: Trait> Module<T> {
	// Add funds to an account
	pub fn add_funds(account: T::AccountId, asset_id: T::AssetId, amount: BalanceOf<T>) -> DispatchResult {
		ensure!(
			<Assets<T>>::contains_key(asset_id) == true,
			Error::<T>::AssetNotWhitelisted
		);
		let mut tx_set = <Transactions<T>>::get(&account);
		tx_set.push(Transaction::<BalanceOf<T>, Timestamp<T>, T::AssetId> {
			amount: amount,
			last_transferred: T::Time::now(),
			asset_id: asset_id,
		});
		tx_set.sort_by(|a, b| a.last_transferred.cmp(&b.last_transferred));
		<Transactions<T>>::insert(account.clone(), tx_set);
		T::MultiCurrency::deposit_into_existing(&account, Some(asset_id), amount)
			.map_err(|_| Error::<T>::TransactionFailed)?;
		Ok(())
	}

	// Removes funds from account
	pub fn remove_funds(account: T::AccountId, asset_id: T::AssetId, amount: BalanceOf<T>) -> DispatchResult {
		// Fetch total unexpired funds to ensure funds can be removed
		ensure!(
			<Assets<T>>::contains_key(asset_id) == true,
			Error::<T>::AssetNotWhitelisted
		);
		let unexpired_funds = Self::total_unexpired_funds(account.clone(), asset_id)?;
		ensure!(unexpired_funds >= amount, Error::<T>::InsufficientUnexpiredFunds);

		let mut current_removed = BalanceOf::<T>::from(0 as u32);
		let mut tx_set = <Transactions<T>>::get(account.clone());
		let now = T::Time::now();
		for mut tx in tx_set.iter_mut() {
			// Transaction has expired
			if tx.last_transferred + <ExpirationDuration<T>>::get(asset_id) < now {
				continue;
			} else {
				if (amount - current_removed) > tx.amount {
					// Completely drain transaction
					current_removed += tx.amount;
					tx.amount = BalanceOf::<T>::from(0 as u32);
				} else {
					// Partially drain transaction
					let remaining = amount - current_removed;
					tx.amount -= remaining;
					current_removed += remaining;
					break;
				}
			}
		}

		ensure!(current_removed == amount, Error::<T>::RemovedIncorrectFunds);
		<Transactions<T>>::insert(account.clone(), tx_set);
		T::MultiCurrency::withdraw(
			&account,
			Some(asset_id),
			amount,
			WithdrawReason::Fee.into(),
			ExistenceRequirement::KeepAlive,
		)
		.map_err(|_| Error::<T>::TransactionFailed)?;
		Ok(())
	}

	// Total funds expired and unexpired
	pub fn total_funds(account: T::AccountId, asset_id: T::AssetId) -> Result<BalanceOf<T>, Error<T>> {
		ensure!(
			<Assets<T>>::contains_key(asset_id) == true,
			Error::<T>::AssetNotWhitelisted
		);
		Ok(<Transactions<T>>::get(account)
			.into_iter()
			.fold(<BalanceOf<T>>::from(0u32), |acc, tx| {
				if tx.asset_id == asset_id {
					acc + tx.amount
				} else {
					acc
				}
			}))
	}

	// Total unexpired funds
	pub fn total_unexpired_funds(account: T::AccountId, asset_id: T::AssetId) -> Result<BalanceOf<T>, Error<T>> {
		ensure!(
			<Assets<T>>::contains_key(asset_id) == true,
			Error::<T>::AssetNotWhitelisted
		);
		let now = T::Time::now();
		Ok(<Transactions<T>>::get(account)
			.into_iter()
			.fold(<BalanceOf<T>>::from(0u32), |acc, tx| {
				if (tx.last_transferred + <ExpirationDuration<T>>::get(asset_id) > now) && (tx.asset_id == asset_id) {
					acc + tx.amount
				} else {
					acc
				}
			}))
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
	// use cennznet_primitives::types::{Balance};

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

	impl prml_generic_asset::Trait for Test {
		type AssetId = u32;
		type Balance = u128;
		type WeightInfo = ();
		type Event = ();
	}

	impl Trait for Test {
		type WeightInfo = ();
		type Time = TimeModule<Test>;
		type AssetId = u32;
		type MultiCurrency = prml_generic_asset::Module<Self>;
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
		sp_io::TestExternalities::from(frame_system::GenesisConfig::default().build_storage::<Test>().unwrap())
			.execute_with(execute)
	}

	#[test]
	pub fn test_multicurrency() {
		let a = alice();
		let b = bob();
		let core_asset_id: u32 = 1;

		execute(|| {
			// Whitelist Asset
			SmartMoney::add_asset(Origin::root(), core_asset_id);

			// Set expiration for asset
			SmartMoney::set_expiration(Origin::root(), core_asset_id, 500);

			// Add funds
			SmartMoney::add_funds(a.clone(), core_asset_id, <BalanceOf<Test>>::from(1000u32));

			// Add a vendor
			SmartMoney::add_vendor(Origin::root(), b.clone()).expect("Could not add vendor using privileged root");
			assert_eq!(<Vendors<Test>>::contains_key(b.clone()), true);

			// Transfer custom currency from the vendor
			SmartMoney::transfer(
				Origin::signed(a.clone()),
				b.clone(),
				core_asset_id,
				<BalanceOf<Test>>::from(100 as u32),
			);
			assert_eq!(SmartMoney::total_funds(a.clone(), core_asset_id).unwrap(), <BalanceOf<Test>>::from(900u32));
		})
	}
}
