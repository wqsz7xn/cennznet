// TODO: find appropriate types for balances and addresses
use frame_support::{decl_error, decl_module, decl_storage, ensure, traits::WithdrawReason, traits::{Currency, ExistenceRequirement, Time}};
use frame_system::ensure_signed;
use codec::{Decode, Encode};
const UNLOCK_DURATION: u128 = 100;

// struct Stake {
//     amount : u128, //amount of the stake
//     leftAmount: u128, // value of the stake on left branch
//     rightAmount: u128, // value of the stake on the right branch
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
	}
}

decl_storage! {
	trait Store for Module<T: Trait> as SyloDirectory {
	    // stakes
		pub Stakes get(fn stakes): map hasher(blake2_128_concat) T::AccountId => Stake<BalanceOf<T>, Timestamp<T>>;
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin, system = frame_system {
		#[weight = 0]
		fn add_stake_for(origin, amount: BalanceOf<T>) {
			let address = ensure_signed(origin)?;
			let unlock_at = T::Time::now();
			let stake = Stake {amount, unlock_at};
			<Stakes<T>>::insert(address, stake);
		}

		#[weight = 0]
		fn get_stake(origin) {
            let address = ensure_signed(origin)?;
            <Stakes<T>>::get(address);
		}

		#[weight = 0]
		fn unstake_to(origin) {
            let address = ensure_signed(origin)?;
            <Stakes<T>>::take(address);
		}
	}
}

