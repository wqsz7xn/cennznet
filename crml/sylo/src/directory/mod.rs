use frame_support::{decl_error, decl_module, decl_storage, dispatch::DispatchResult, ensure, traits::{WithdrawReason, Currency, ExistenceRequirement, Time}};
use frame_system::ensure_signed;
use codec::{Decode, Encode};
use sp_io::hashing::{keccak_256};

const UNLOCK_DURATION: u32 = 100;

type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;
type Timestamp<T> = <<T as Trait>::Time as Time>::Moment;

#[derive(Encode, Decode, Default)]
pub struct Stake<AccountId, Balance> {
	amount : Balance , //amount of the stake

    left_amount: Balance, // value of the stake on left branch
	right_amount: Balance, // value of the stake on the right branch
	
	stakee: AccountId,

    parent: Option<[u8; 32]>, // hash of parent 
    left : Option<[u8; 32]>, // hash of parent 
    right : Option<[u8; 32]>, // hash of parent 
}

#[derive(Encode, Decode, Default)]
pub struct Unlock<Balance, Timestamp> {
	amount: Balance, // amount of stake unlocking
    unlock_at: Timestamp, // block num stake becomes withdrawable
}

decl_storage! {
	trait Store for Module<T: Trait> as SyloDirectory {
		// Stakers
		pub Stakes get(fn stakes): map hasher(blake2_128_concat) [u8; 32] => Stake<T::AccountId, BalanceOf<T>>;

		// Stakees
		pub Stakees get(fn stakees): map hasher(blake2_128_concat) T::AccountId => BalanceOf<T>;

		// Unlockings
		pub Unlockings get(fn unlockings): map hasher(blake2_128_concat) [u8; 32] => Unlock<BalanceOf<T>, Timestamp<T>>;
		
		// Root 
		pub Root get(fn root): [u8; 32];
	}
}

pub trait Trait: frame_system::Trait {
    type Currency: Currency<Self::AccountId>;
    type Time: Time;
    //type WeightInfo: WeightInfo;
}

decl_error! {
	pub enum Error for Module<T: Trait> {
		/// An address must stake above zero tokens
		ZeroStake,
		/// Cannot re-stake while funds are unlocking
		StakeWhileUnlocking,
		/// Only one stake allowed per address
		AlreadyStaking,
		/// The address is not staking
		NotStaking,
		/// The unlock period has not been exhausted
		CannotUnlock,
		/// Attempt to unlock more than what is staking
		InsufficientStakeBalance,
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin, system = frame_system {
		#[weight = 0]
		fn add_stake(origin, amount: BalanceOf<T>, stakee: T::AccountId) {
			ensure!(amount != (0 as u32).into(), Error::<T>::ZeroStake);
			let staker = ensure_signed(origin)?;
			let key = Self::get_key(staker.clone(), stakee.clone());
			if !<Stakes<T>>::contains_key(&key) {
				let mut parent : Option<[u8; 32]> = Some(<Root>::get());
				let mut current : Stake<T::AccountId, BalanceOf<T>> = <Stakes<T>>::get(parent.unwrap());
				while parent.is_some() {
					let next;
					if current.left_amount < current.right_amount {
						next = current.left;
					} else {
						next = current.right;
					}

					if next.is_none() {
						break;
					}

					parent = next;
					current = <Stakes<T>>::get(next.unwrap());
				}

				Self::set_child(&mut current, None, Some(key));

				// Create a stake
				let mut stake = Stake::<T::AccountId, BalanceOf<T>>::default();
				stake.parent = parent;
				stake.stakee = stakee.clone();
				<Stakes<T>>::insert(key, stake);

			}

			// Now that the key for the stake is defined fetch it, or if it was already defined fetch it
			let mut stake = <Stakes<T>>::get(&key);
			// Set the root
			if stake.parent.is_none() { 
				<Root>::put(key);
			}

			Self::update_stake_amount(Some(key), &mut stake, amount);

			T::Currency::transfer(&staker, &stakee, amount, ExistenceRequirement::KeepAlive);
		}


		#[weight = 0]
		fn unlock_stake(origin, amount: BalanceOf<T>, address: T::AccountId) {
			let staker = ensure_signed(origin)?;
			let key = Self::get_key(staker, address);
			let mut stake = <Stakes<T>>::get(&key);

			ensure!(stake.amount > (0 as u32).into(), Error::<T>::ZeroStake);
			ensure!(stake.amount >= amount, Error::<T>::InsufficientStakeBalance);

			Self::update_stake_amount(Some(key), &mut stake, amount);

			//Stake has been withdrawn now update the tree
			if stake.amount == (0 as u32).into() {
				let mut child : Option<[u8; 32]>;
				if stake.left_amount > stake.right_amount {
					child = stake.left;
				} else {
					child = stake.right;
				}

				let mut parent = <Stakes<T>>::get(stake.parent.unwrap());

				if child.is_none() {
					Self::set_child(&mut stake, Some(key), None);

					// The nly staker is removed, reset root
					if stake.parent.is_none() {
						<Root>::set([0u8; 32]);	
					}
				} else {
					let mut current = <Stakes<T>>::get(child.unwrap());

					loop {
						let next : Option<[u8; 32]>;
						if current.left_amount > current.right_amount {
							next = current.left;
						} else {
							next = current.right;
						}
						if next.is_none() {
							break;
						}

						child = next;
						current = <Stakes<T>>::get(next.unwrap());
					}

					let current_parent = current.parent;
					Self::set_child(&mut parent, Some(key), child);
					current.parent = stake.parent;


					// update the children of current to be that of what the removed stake was
					if current_parent.unwrap() != key {

						// Move the children of stake to current
						Self::fixl(&stake, child, &mut current);
						Self::fixl(&stake, child, &mut current);

						// Place stake where current was and
						stake.parent = current_parent; // set parent
						Self::set_child(&mut <Stakes<T>>::get(current_parent.unwrap()), current_parent, Some(key)); // set parents child

						// Unstake amount
						//Self::apply_stake_change(Some(key), &mut stake, current.amount.saturating_sub(current.amount), current.parent);

						Self::set_child(&mut <Stakes<T>>::get(current_parent.unwrap()), Some(key), None);
					}
					else if stake.left == child {
						Self::fixr(&stake, child, &mut current);
					}
					else {
						Self::fixl(&stake, child, &mut current);
					}
				}

				// Now that the node is unlinked from any other nodes we can remove it.
				<Stakes<T>>::remove(key);

				// XXX: You should be adding a unlock here
				let mut unlock = <Unlockings<T>>::get(key);
				let unlock_at = T::Time::now() + UNLOCK_DURATION.into();

				if unlock.unlock_at < unlock_at {
					unlock.unlock_at = unlock_at;
				}

				unlock.amount += amount;
			}
		}

		// Reverse unlocking a certain amount of stake 
		#[weight = 0]
		fn lock_stake(origin, amount: BalanceOf<T>, stakee: T::AccountId) {
			let staker = ensure_signed(origin)?;
			let key = Self::get_key(staker, stakee);
		}

		// Stop the unlocking of a certain amount of funds
		// #[weight = 0]
		// fn pull_unlocking() {
		// }

		// #[weight = 0]
		// fn add_stake(origin, amount: BalanceOf<T>) {
		// 	ensure!(amount != (0 as u32).into(), Error::<T>::ZeroStake);
		// 	let address = ensure_signed(origin)?;

		// 	// New stake
		// 	if !<Stakes<T>>::contains_key(&address) {
		// 		let parent = Some(<Root<T>>::get());
		// 		let current = <Stakes<T>>::get(&address);
		// 		while parent.is_some() {
		// 			let next;
		// 			if current.left_amount < current.right_amount {
		// 				next = current.left;
		// 			}
		// 			else {
		// 				next = current.right;
		// 			}

		// 			if(next.is_none()) {
		// 				break;
		// 			}

		// 			parent = next;
		// 			current = <Stakes<T>>::get(&address);

		// 		}
		// 	}
		// }

		//fn unlockStake(origin, amount: BalanceOf<T>, )




		// #[weight = 0]
		// fn add_stake(origin, amount: BalanceOf<T>) {
		// 	let address = ensure_signed(origin)?;
		// 	// Check that the node is not already staking
		// 	ensure!(!<Stakes<T>>::contains_key(&address), Error::<T>::AlreadyStaking);

		// 	//Remove funds from account
			// T::Currency::withdraw(&address, amount, WithdrawReason::Fee.into(), ExistenceRequirement::KeepAlive)?;

		// 	// Calculate lock period and create stake
		// 	let unlock_at = T::Time::now() + UNLOCK_DURATION.into();
		// 	let stake = Stake {amount, unlock_at};
		// 	<Stakes<T>>::insert(address, stake);
		// }

		// #[weight = 0]
		// fn get_stake(origin) {
        //     let address = ensure_signed(origin)?;
		// 	ensure!(<Stakes<T>>::contains_key(&address), Error::<T>::NotStaking);
        //     <Stakes<T>>::get(address);
		// }

		// #[weight = 0]
		// fn unstake(origin) {
		// 	let address = ensure_signed(origin)?;
		// 	ensure!(<Stakes<T>>::contains_key(&address), Error::<T>::NotStaking);
		// 	let Stake {amount, unlock_at} = <Stakes<T>>::get(&address);
		// 	ensure!(T::Time::now() >= unlock_at, Error::<T>::CannotUnlock); // Ensure unlock period exhausted
		// 	T::Currency::deposit_into_existing(&address, amount);
		// 	<Stakes<T>>::remove(&address);
		// }
	}
}

impl<T: Trait> Module<T> {
	fn get_key(staker: T::AccountId, stakee: T::AccountId) -> [u8; 32] {
		let mut vec_bytes = staker.encode();
		vec_bytes.append(&mut stakee.encode());
		keccak_256(vec_bytes.as_slice())
	}

	fn set_child(stake: &mut Stake<T::AccountId, BalanceOf<T>>, old_key : Option<[u8; 32]>, new_key: Option<[u8; 32]>) {
		if stake.left == old_key {
			stake.left = new_key;
		} else {
			stake.right = new_key
		}
	}

	fn update_stake_amount(key: Option<[u8; 32]>, stake: &mut Stake<T::AccountId, BalanceOf<T>>, amount: BalanceOf<T>) {
		stake.amount += amount;
		<Stakees<T>>::insert(&stake.stakee, amount);

		Self::apply_stake_change(key, stake, amount, None);
	}


	fn apply_stake_change(key: Option<[u8; 32]>, stake: &mut Stake<T::AccountId, BalanceOf<T>>, amount: BalanceOf<T>, root_: Option<[u8; 32]>) {
		let parent_key: Option<[u8; 32]> = stake.parent;
		if parent_key == root_ || parent_key == None {
			// we are at root, there is nothing left to update
			return
		}

		let mut parent: Stake<T::AccountId, BalanceOf<T>> = <Stakes<T>>::get(parent_key.unwrap());
		if parent.left == key {
			parent.left_amount += amount;
		} else {
			parent.right_amount+= amount;
		}

		return Self::apply_stake_change(parent_key, &mut parent, amount, root_);
	}

	fn fixl(stake: &Stake<T::AccountId, BalanceOf<T>>, current_key: Option<[u8; 32]>, current: &mut Stake<T::AccountId, BalanceOf<T>>) {
		if stake.left.is_none() {
			return;
		}

		<Stakes<T>>::get(stake.left.unwrap()).parent = current_key;
		current.left= stake.left;
		current.left_amount = stake.left_amount;
	}

	fn fixr(stake: &Stake<T::AccountId, BalanceOf<T>>, current_key: Option<[u8; 32]>, current: &mut Stake<T::AccountId, BalanceOf<T>>) {
		if stake.left.is_none() {
			return;
		}

		<Stakes<T>>::get(stake.right.unwrap()).parent = current_key;
		current.right = stake.right;
		current.right_amount = stake.right_amount;
	}
}