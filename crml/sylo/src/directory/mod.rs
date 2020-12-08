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
	fn add_node() -> Weight;
}

type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;
type Timestamp<T> = <<T as Trait>::Time as Time>::Moment;
type Hash = [u8; 32];

#[derive(Encode, Decode, Default, Debug)]
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
}

decl_storage! {
	trait Store for Module<T: Trait> as SyloDirectory {
		// Stakers (map hash -> stake)
		pub Stakes get(fn stakes): map hasher(blake2_128_concat) Hash => SumTree;

		// Unlockings (map hash -> unlock)
		pub Unlockings get(fn unlockings): map hasher(blake2_128_concat) Hash => Unlock;
		
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
		InvalidAmount,

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







		}
	}
}

impl<T: Trait> Module<T> {
	fn get_key(staker: T::AccountId, stakee: T::AccountId) -> Hash {
		let mut vec_bytes = staker.encode();
		vec_bytes.append(&mut stakee.encode());
		keccak_256(vec_bytes.as_slice())
	}
}