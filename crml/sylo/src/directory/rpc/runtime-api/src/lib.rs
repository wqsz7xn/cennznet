#![cfg_attr(not(feature = "std"), no_std)]

use codec::Codec;
use sp_arithmetic::traits::BaseArithmetic;

sp_api::decl_runtime_apis! {
	/// The RPC API to interact with CENNZX Spot Exchange
	pub trait SyloDirectoryApi<Balance, AccountId> where
		Balance: Codec + BaseArithmetic,
		AccountId: Codec,
	{
		/// Scan the stake directory and select a weighted node
		fn scan(point: Balance) -> Result<AccountId, ()>;
	}
}