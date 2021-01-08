use frame_support::weights::Weight;

impl crate::ticketing::WeightInfo for () {
	fn deposit_escrow() -> Weight {
		0
	}
	fn deposit_penalty() -> Weight {
		0
	}
	fn unlock_deposits() -> Weight {
		0
	}
	fn lock_deposits() -> Weight {
		0
	}
	fn withdraw() -> Weight {
		0
	}
	fn withdraw_to() -> Weight {
		0
	}
	fn redeem() -> Weight {
		0
	}
	fn set_unlock_duration() -> Weight {
		0
	}
}
