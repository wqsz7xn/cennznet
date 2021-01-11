use frame_support::weights::Weight;

impl crate::listing::WeightInfo for () {
	fn set_listing() -> Weight {
		0
	}
}
