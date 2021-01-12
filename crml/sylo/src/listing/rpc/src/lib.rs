use std::{convert::TryInto, sync::Arc};

use codec::Codec;
use jsonrpc_core::{Error as RpcError, ErrorCode, Result};
use jsonrpc_derive::rpc;
use sp_api::ProvideRuntimeApi;
use sp_arithmetic::traits::{BaseArithmetic, SaturatedConversion};
use sp_blockchain::HeaderBackend;
use sp_runtime::{generic::BlockId, traits::Block as BlockT};
pub use crml_sylo_listing_rpc_runtime_api::{self as runtime_api, SyloListingApi as SyloListingRuntimeApi, SyloListingResult};

type MultiAddress = sp_std::prelude::Vec<u8>;

/// Contracts RPC methods.
#[rpc]
pub trait SyloListingApi<AccountId> {
	#[rpc(name = "syloListing_get_listing")]
	fn get_listing(&self, key: AccountId) -> Result<MultiAddress>;
}

/// An implementation of Sylo directory specific RPC methods.
pub struct SyloListing<C, T> {
	client: Arc<C>,
	_marker: std::marker::PhantomData<T>,
}

impl<C, T> SyloListing<C, T> {
	/// Create new Sylo directory client
	pub fn new(client: Arc<C>) -> Self {
		SyloListing {
			client,
			_marker: Default::default(),
		}
	}
}

/// Error type of this RPC api.
pub enum Error {
	/// The call to runtime failed.
	Runtime,
}

impl From<Error> for i64 {
	fn from(e: Error) -> i64 {
		match e {
			Error::Runtime => 1,
		}
	}
}

impl<C, Block, AccountId> SyloListingApi<AccountId> for SyloListing<C, Block>
where
	Block: BlockT,
	C: Send + Sync + 'static + ProvideRuntimeApi<Block> + HeaderBackend<Block>,
	C::Api: SyloListingRuntimeApi<Block, AccountId>,
	AccountId: Codec,
{
	fn get_listing(&self, key: AccountId) -> Result<MultiAddress> {
		let api = self.client.runtime_api();
		let best = self.client.info().best_hash;
		let at = BlockId::hash(best);

		let result = api
			.get_listing(&at, key) 
			.map_err(|e| RpcError {
				code: ErrorCode::ServerError(Error::Runtime.into()),
				message: "Unable to query scan.".into(),
				data: Some(format!("{:?}", e).into()),
			})?;
		match result {
			SyloListingResult::Success(acc) => Ok(acc),
			SyloListingResult::Error => Err(RpcError {
				code: ErrorCode::ServerError(Error::Runtime.into()),
				message: "Runtime error".into(),
				data: Some("".into()),
			}),
		}
	}
}