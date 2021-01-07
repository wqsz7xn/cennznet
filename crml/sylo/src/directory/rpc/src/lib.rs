use std::{convert::TryInto, sync::Arc};

use codec::Codec;
use jsonrpc_core::{Error as RpcError, ErrorCode, Result};
use jsonrpc_derive::rpc;
use sp_api::ProvideRuntimeApi;
use sp_arithmetic::traits::{BaseArithmetic, SaturatedConversion};
use sp_blockchain::HeaderBackend;
use sp_runtime::{generic::BlockId, traits::Block as BlockT};

pub use crml_sylo_directory_rpc_runtime_api::{self as runtime_api, SyloDirectoryApi as SyloDirectoryRuntimeApi, SyloDirectoryResult};

/// Contracts RPC methods.
#[rpc]
pub trait SyloDirectoryApi<Balance, AccountId> {
	#[rpc(name = "syloDirectory_scan")]
	fn scan(&self, point: Balance) -> Result<AccountId>;
}

/// An implementation of Sylo directory specific RPC methods.
pub struct SyloDirectory<C, T> {
	client: Arc<C>,
	_marker: std::marker::PhantomData<T>,
}

impl<C, T> SyloDirectory<C, T> {
	/// Create new Sylo directory client
	pub fn new(client: Arc<C>) -> Self {
		SyloDirectory {
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

impl<C, Block, Balance, AccountId> SyloDirectoryApi<Balance, AccountId> for SyloDirectory<C, Block>
where
	Block: BlockT,
	C: Send + Sync + 'static + ProvideRuntimeApi<Block> + HeaderBackend<Block>,
	C::Api: SyloDirectoryRuntimeApi<Block, Balance, AccountId>,
	Balance: Codec + BaseArithmetic,
	AccountId: Codec,
{
	fn scan(&self, point: Balance) -> Result<AccountId> {
		let api = self.client.runtime_api();
		let best = self.client.info().best_hash;
		let at = BlockId::hash(best);

		// XXX: Just to satisfy type tetris.
		// Hardcoded errors
		let result = api
			.scan(&at, point) 
			.map_err(|e| RpcError {
				code: ErrorCode::ServerError(Error::Runtime.into()),
				message: "Unable to query scan.".into(),
				data: Some(format!("{:?}", e).into()),
			})?;
		match result {
			SyloDirectoryResult::Success(acc) => Ok(acc),
			SyloDirectoryResult::Error => Err(RpcError {
				code: ErrorCode::ServerError(Error::Runtime.into()),
				message: "Runtime error".into(),
				data: Some("".into()),
			}),
		}
	}
}