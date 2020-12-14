use frame_support::weights::Weight;

impl crate::smart_money::WeightInfo for () {
	fn add_vendor() -> Weight {
		0
	}
}