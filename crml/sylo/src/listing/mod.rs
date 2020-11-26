use frame_support::{decl_error, decl_module, decl_storage, dispatch::Vec, ensure, weights::Weight};
use frame_system::ensure_signed;

// Listing
decl_storage! {
	trait Store for Module<T: Trait> as SyloListing {
		pub Listing get(fn values): map hasher(blake2_128_concat) T::AccountId => Vec<u8>;
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin, system = frame_system {
		#[weight = 0]
		fn put_value(origin, key: T::AccountId, value: Vec<u8>) {
			ensure_signed(origin)?;
			Self::put(key, value)
		}

        #[weight = 0]
		fn get_value(origin, key: T::AccountId) {
			ensure_signed(origin)?;
			Self::get(key)
		}

        #[weight = 0]
		fn delete_keyvalue(origin, key: T:: AccountId) {
		    Self::delete(key)
		}
	}
}

pub trait Trait: frame_system::Trait {
    //type WeightInfo: WeightInfo;
}

impl<T: Trait> Module<T> {
    pub fn put(key: T::AccountId, value: Vec<u8>) {
        <Listing<T>>::insert(key, value);
    }

    pub fn get(key : T::AccountId) {
        <Listing<T>>::get(key);
    }

    pub fn delete(key: T::AccountId) {
        <Listing<T>>::take(key);
    }
}

