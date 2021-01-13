#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Codec, Decode, Encode};
use sp_arithmetic::traits::BaseArithmetic;
use sp_runtime::RuntimeDebug;

/// A result of querying the Sylo directory
#[derive(Eq, PartialEq, Encode, Decode, RuntimeDebug)]
pub enum SyloDirectoryResult<AccountId> {
	/// The query returned successfully.
	Success(AccountId),
	/// There was an issue querying the API
	Error,
}

sp_api::decl_runtime_apis! {
	/// The RPC API to interact with Sylo stake tree
	pub trait SyloDirectoryApi<Balance, AccountId> where
		Balance: Codec + BaseArithmetic,
		AccountId: Codec,
	{
		/// Scan the stake directory and select a weighted node
		fn scan(point: Balance) -> SyloDirectoryResult<AccountId>;
	}
}
