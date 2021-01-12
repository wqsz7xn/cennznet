use frame_support::weights::Weight;

impl crate::directory::WeightInfo for () {
	fn add_stake() -> Weight {
		0
	}
	fn unlock_stake() -> Weight {
		0
	}
	fn unstake() -> Weight {
		0
	}
	fn lock_stake() -> Weight {
		0
	}
}
