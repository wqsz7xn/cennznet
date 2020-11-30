use frame_support::{decl_error, decl_module, decl_storage, ensure, traits::WithdrawReason, traits::{Currency, ExistenceRequirement, Time}};
use frame_system::ensure_signed;
use codec::{Decode, Encode};

const UNLOCK_DURATION: u32 = 100;

// struct Stake<AccountId, Balance, Timestamp> {
//     amount : Balance , //amount of the stake
//     leftAmount: Balance, // value of the stake on left branch
//     rightAmount: Balance, // value of the stake on the right branch
//     stakee: AccountId, // address of peer that offers to stake
//     parent: Box<Stake>,
//     left: Box<Stake>, // left children
//     right: Box<Stake>, // right children
// }
//
// struct Unlock {
//     amount: u128, // amoutn of stake unlocking
//     unlockAt: u128 // block num stake becomes withdrawable
// }
//
// decl_storage! {
// 	trait Store for Module<T: Trait> as SyloDirectory {
// 	    // stakes
// 		pub Stake get(fn stakes): map hasher(blake2_128_concat) T::AccountId => Vec<u8>;
//
// 		// stakees
// 		pub Stake get(fn stakees): map hasher(blake2_128_concat) T::AccountId => Vec<u8>;
//
//         //unlockings
//         pub Stake get(fn stakees): map hasher(blake2_128_concat) T::AccountId => Vec<u8>;
// 	}
// }

// pub trait Trait: frame_system::Trait {
//     type AssetId: Parameter + Member + BaseArithmetic + Default + Copy;
//     type Currency: Currency<Self::AccountId> + Send + Sync;
//     // type WeightInfo: WeightInfo;
// }

type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;
type Timestamp<T> = <<T as Trait>::Time as Time>::Moment;

pub trait Trait: frame_system::Trait {
    type Currency: Currency<Self::AccountId>;
    type Time: Time;
    //type WeightInfo: WeightInfo;
}


#[derive(Encode, Decode, Default)]
pub struct Stake<Balance, Timestamp> {
    amount: Balance,
    unlock_at : Timestamp, // Block number funds are unlocked from stake
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
		CannotUnlock,
	}
}

decl_storage! {
	trait Store for Module<T: Trait> as SyloDirectory {
		pub Stakes get(fn stakes): map hasher(blake2_128_concat) T::AccountId => Stake<BalanceOf<T>, Timestamp<T>>;
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin, system = frame_system {
		#[weight = 0]
		fn add_stake(origin, amount: BalanceOf<T>) {
			let address = ensure_signed(origin)?;
			// Check that the node is not already staking
			ensure!(!<Stakes<T>>::contains_key(&address), Error::<T>::AlreadyStaking);

			//Remove funds from account
			T::Currency::withdraw(&address, amount, WithdrawReason::Fee.into(), ExistenceRequirement::KeepAlive)?;

			// Calculate lock period and create stake
			let unlock_at = T::Time::now() + UNLOCK_DURATION.into();
			let stake = Stake {amount, unlock_at};
			<Stakes<T>>::insert(address, stake);
		}

		#[weight = 0]
		fn get_stake(origin) {
            let address = ensure_signed(origin)?;
			ensure!(<Stakes<T>>::contains_key(&address), Error::<T>::NotStaking);
            <Stakes<T>>::get(address);
		}

		#[weight = 0]
		fn unstake(origin) {
			let address = ensure_signed(origin)?;
			ensure!(<Stakes<T>>::contains_key(&address), Error::<T>::NotStaking);
			let Stake {amount, unlock_at} = <Stakes<T>>::get(&address);
			ensure!(T::Time::now() >= unlock_at, Error::<T>::CannotUnlock); // Ensure unlock period exhausted
			T::Currency::deposit_into_existing(&address, amount);
			<Stakes<T>>::remove(&address);
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::mock::{ExtBuilder, Origin, Test};
	use frame_support::assert_ok;
	use frame_system::RawOrigin;
	use sp_runtime::DispatchError::Other;

	type Directory = Module<Test>;

	impl Trait for Test {
		type WeightInfo = ();
	}

	#[test]
	fn create_stake() {
		ExtBuilder::default().build().execute_with(|| {
		});
	}

	#[test]
	fn withdraw_stake() {

	}

	#[test]
	fn withdraw_before_unlock() {

	}

	#[test]
	fn multiple_stakes() {

	}

	#[test]
	fn stake_insufficient_balance() {

	}
}