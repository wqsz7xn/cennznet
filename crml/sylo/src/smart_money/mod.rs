use frame_support::{decl_error, decl_module, decl_storage, ensure, traits::{WithdrawReason, Currency, ExistenceRequirement, Time}, weights::Weight};
use frame_system::{ensure_root, ensure_signed};
use codec::{Decode, Encode};
use sp_io::hashing::{keccak_256};
use sp_runtime::{DispatchError, traits::Bounded};

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
	expires: Timestamp, // Time which funds expire
}

decl_storage! {
	trait Store for Module<T: Trait> as SyloSmartMoney {
		pub Vendors get(fn vendors): map hasher(blake2_128_concat) T::AccountId => ();
		pub Transactions get(fn transactions): map hasher(blake2_128_concat) T::AccountId => Vec<Transaction<BalanceOf<T>, Timestamp<T>>>;
	}
}


decl_error! {
	pub enum Error for Module<T: Trait> {
		/// Invalid vendor recipient
		VendorNotWhitelisted,
		/// Not enough unexpired funds
		InsufficientFunds,
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
		fn create_transaction(origin, to: T::AccountId, amount: BalanceOf<T>) {
			let from = ensure_signed(origin)?;
			ensure!(<Vendors<T>>::contains_key(to), Error::<T>::VendorNotWhitelisted);
			let tx_set = <Vendors<T>>::get(from);
			Self::remove(from, amount);
			//Self::insert(to, amount);
			// tx onchain now
		}

		// Total spendable unexpired funds
		#[weight = T::WeightInfo::add_vendor()]
		fn total_unexpired(origin, account: T::AccountId) -> BalanceOf<T> {
			let acc = <BalanceOf<T>>::from(0);
			for tx in <Transactions<T>>::get(account){
				acc += tx.amount
			}
			acc
		}
	}
}

impl<T: Trait> Module<T> {

	// Removes funds from account
	pub fn remove(account: T::AccountId, amount: BalanceOf<T>) -> Result<(), Error<T>> {
		// Fetch total unexpired funds to ensure funds can be removed
		let acc = <BalanceOf<T>>::from(0);
		let now = T::Time::now();
		let mut tx_set: Vec<Transaction<BalanceOf<T>, Timestamp<T>>> = <Transactions<T>>::get(account);
		for tx in <Transactions<T>>::get(account){
			if tx.expires >= now {
				acc += tx.amount;
			}
			if acc >= amount {
				break;
			}
		}

		ensure!(acc >= amount, Error::<T>::InsufficientFunds);
		// Prioritise useage of expiring funds first
		tx_set.sort_by(|a, b| a.expires.cmp(&b.expires));
		Ok(())	


	}


	pub fn add() {

	}

}