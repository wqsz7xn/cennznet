use frame_support::weights::Weight;

impl crate::smart_money::WeightInfo for () {
	fn add_vendor() -> Weight {
		0
	}
	fn remove_vendor() -> Weight {
		0
	}
	fn transfer() -> Weight {
		0
	}
	fn mint() -> Weight {
		0
	}
	fn set_expiration() -> Weight {
		0
	}
	fn add_asset() -> Weight {
		0
	}
	fn remove_asset() -> Weight {
		0
	}
}