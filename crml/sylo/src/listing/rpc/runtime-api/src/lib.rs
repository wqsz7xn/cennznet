#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Codec, Decode, Encode};
use sp_arithmetic::traits::BaseArithmetic;
use sp_runtime::RuntimeDebug;
use sp_std::prelude::Vec;

/// A result of querying the Sylo listing
#[derive(Eq, PartialEq, Encode, Decode, RuntimeDebug)]
pub enum SyloListingResult {
	/// The query returned successfully.
	Success(Vec<u8>),
	/// There was an issue querying the API
	Error,
}

sp_api::decl_runtime_apis! {
	/// The RPC API to interact with Sylo listing module
	pub trait SyloListingApi<AccountId> where
		AccountId: Codec,
	{
		/// Fetch the Listing asociated with the key
		fn get_listing(key: AccountId) -> SyloListingResult;
	}
}
