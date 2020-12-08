use frame_support::weights::Weight;

impl crate::directory::WeightInfo for () {
	fn add_node() -> Weight {
		0
	}
}