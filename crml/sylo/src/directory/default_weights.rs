use frame_support::weights::Weight;

impl crate::directory::WeightInfo for () {
<<<<<<< Updated upstream
	fn add_node() -> Weight {
=======
	fn push() -> Weight {
		0
	}
	fn pull() -> Weight {
		0
	}
	fn take() -> Weight {
>>>>>>> Stashed changes
		0
	}
}