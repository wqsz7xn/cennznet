use frame_support::{
	decl_module, decl_storage, weights::Weight
};
use frame_system::ensure_signed;
use sp_std::prelude::Vec;

mod default_weights;

type MultiAddress = Vec<u8>;

pub trait WeightInfo {
	fn set_listing() -> Weight;
}

decl_storage! {
	trait Store for Module<T: Trait> as SyloListing {
		pub Listings get(fn values): map hasher(blake2_128_concat) T::AccountId => MultiAddress;
	}
}

pub trait Trait: frame_system::Trait {
	type WeightInfo: WeightInfo;
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin, system = frame_system {
		#[weight = T::WeightInfo::set_listing()]
		fn set_listing(origin, key: T::AccountId, multiaddr: MultiAddress) {
			ensure_signed(origin)?;
			<Listings<T>>::insert(key, multiaddr);
		}
	}
}

impl<T: Trait> Module<T> {
	pub fn get_listing(key: T::AccountId) -> MultiAddress {
		<Listings<T>>::get(key)
	}
}
