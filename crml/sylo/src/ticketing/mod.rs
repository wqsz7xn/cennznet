use codec::{Decode, Encode};
use frame_support::{decl_error, decl_module, decl_storage, dispatch::DispatchError, ensure, traits::WithdrawReason, traits::{Currency, ExistenceRequirement, Time}, weights::Weight};
use frame_system::ensure_signed;
use sp_core::U256;
use sp_io::hashing::keccak_256;
use sp_runtime::{AccountId32, MultiSignature, traits::Verify};
use sp_std::convert::TryFrom;
use core::fmt::Debug;

mod default_weights;

const UNLOCK_DURATION: u32 = 7 * 24 * 60 * 60 * 1000; // A week

pub trait WeightInfo {
    fn deposit_escrow() -> Weight;
    fn deposit_penalty() -> Weight;
    fn unlock_deposits() -> Weight;
    fn lock_deposits() -> Weight;
    fn withdraw() -> Weight;
    fn withdraw_to() -> Weight;
    fn redeem() -> Weight;
}

pub trait Trait: frame_system::Trait {
    type Currency: Currency<Self::AccountId>;
    type WeightInfo: WeightInfo;
    type Time: Time;
}
 
type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;
type TicketOf<T> = Ticket<<T as frame_system::Trait>::AccountId, BalanceOf<T>, Timestamp<T>>;
type Timestamp<T> = <<T as Trait>::Time as Time>::Moment;

#[derive(Encode, Decode, Clone, Eq, PartialEq, Debug, Default)]
pub struct Deposit<Balance, Timestamp> {
    /// Balance of a user's escrow
    pub escrow: Balance,
    /// Balance of a user's penalty
    pub penalty: Balance,

    /// Block number at which the user can withdraw their balance
    pub unlock_at: Timestamp,
}

#[derive(Encode, Decode, Clone, Eq, PartialEq, Debug)]
pub struct Ticket<AccountId, Balance, Timestamp> {
    /// Adress of the ticket sender
    pub sender: AccountId,
    /// Adress of the ticket receiver
    pub receiver: AccountId,
    /// The value of a winning ticket
    pub face_value: Balance,
    /// The chance of a winning ticket
    pub win_prob: U256,
    /// The time that the ticket is valid until
    pub expiration: Timestamp,
    /// Hash of receiver's random value
    pub receiver_rand_hash: [u8; 32],
    /// Sender's ticket counter
    pub sender_nonce: u32,
} 

decl_error! {
    pub enum Error for Module<T: Trait> {
        /// Cannot deposit while unlocking
        DepositWhileUnlocking,
        /// There is nothing to withdraw
        NothingToWithdraw,
        /// Unlock already in progress
        UnlockAlreadyInProgress,
        /// Not unlocking, cannot lock
        NotUnlocking,
        /// The deposit is not unlocked
        DepositNotUnlocked,
        /// The unlock period is not yet complete
        UnlockPeriodNotComplete,
        /// Ticket has expired
        ExpiredTicket,
        /// Ticket has already been redeemed
        TicketAlreadyRedeemed,
        /// Hash of receiver_rand doesn't match receiver_rand_hash
        HashesDontMatch,
        /// Ticket doesn't have a valid signature
        InvalidSignature,
        /// Ticket is not a winning one
        TicketNotAWinner,
        /// Ticket sender has insufficient funds to pay out
        InsufficientFunds,
    }
}

decl_storage! {
    trait Store for Module<T: Trait> as SyloTicketing {
        /// Mapping of user deposits to their address
        pub Deposits get(fn deposits): map hasher(blake2_128_concat) T::AccountId => Deposit<BalanceOf<T>, Timestamp<T>>;

        /// Mapping of ticket hashes, used to check if a ticket has been redeemed
        pub UsedTickets get(fn used_tickets): map hasher(blake2_128_concat) [u8; 32] => bool;
    }
}

decl_module! {
    pub struct Module<T: Trait> for enum Call where origin: T::Origin {
        #[weight = T::WeightInfo::deposit_escrow()]
        pub fn deposit_escrow(origin, amount: BalanceOf<T>) {
            let account = ensure_signed(origin)?;
            let deposit = <Deposits<T>>::get(&account);
            ensure!(deposit.unlock_at == (0 as u32).into(), Error::<T>::DepositWhileUnlocking);

            T::Currency::withdraw(&account, amount, WithdrawReason::Fee.into(), ExistenceRequirement::KeepAlive)?;
            <Deposits<T>>::mutate(&account, |ref mut deposit| {
                deposit.escrow += amount;
            });
        }

        #[weight = T::WeightInfo::deposit_penalty()]
        pub fn deposit_penalty(origin, amount: BalanceOf<T>) {
            let account = ensure_signed(origin)?;
            let deposit = <Deposits<T>>::get(&account);
            ensure!(deposit.unlock_at == (0 as u32).into(), Error::<T>::DepositWhileUnlocking);

            T::Currency::withdraw(&account, amount, WithdrawReason::Fee.into(), ExistenceRequirement::KeepAlive)?;
            <Deposits<T>>::mutate(&account, |ref mut deposit| {
                deposit.penalty += amount;
            });
        }

        #[weight = T::WeightInfo::unlock_deposits()]
        pub fn unlock_deposits(origin) {
            let account = ensure_signed(origin)?;
            let deposit = <Deposits<T>>::get(&account);
            ensure!(deposit.escrow > (0 as u32).into() || deposit.penalty > (0 as u32).into(), Error::<T>::NothingToWithdraw);
            ensure!(deposit.unlock_at == (0 as u32).into(), Error::<T>::UnlockAlreadyInProgress);

            <Deposits<T>>::mutate(&account, |ref mut deposit| {
                deposit.unlock_at = T::Time::now() + UNLOCK_DURATION.into();
            })
        }

        #[weight = T::WeightInfo::lock_deposits()]
        pub fn lock_deposits(origin) {
            let account = ensure_signed(origin)?;
            let deposit = <Deposits<T>>::get(&account);
            ensure!(deposit.unlock_at != (0 as u32).into(), Error::<T>::NotUnlocking);

            <Deposits<T>>::mutate(account, |ref mut deposit| {
                deposit.unlock_at = (0 as u32).into();
            })
        }

        #[weight = T::WeightInfo::withdraw()]
        pub fn withdraw(origin) {
            let account = ensure_signed(origin)?;
            withdraw_to::<T>(account)?;
        }
        
        /// Complete the withdrawal process and remove the assets
        #[weight = T::WeightInfo::withdraw_to()]
        pub fn withdraw_to(origin, account: T::AccountId) {
            let _ = ensure_signed(origin)?;
            withdraw_to::<T>(account)?;
        }

        #[weight = T::WeightInfo::redeem()]
        pub fn redeem(origin, ticket: TicketOf<T>, receiver_rand: U256, sig: MultiSignature) {
            let hash = get_ticket_hash::<T>(&ticket);
            ensure_valid_winning_ticket::<T>(&ticket, &hash, receiver_rand, sig)?;

            let deposit = <Deposits<T>>::get(&ticket.sender);

            ensure!(deposit.escrow + deposit.penalty >= ticket.face_value, Error::<T>::InsufficientFunds);

            UsedTickets::insert(&hash, true);

            if ticket.face_value > deposit.escrow {
                let penalty_amount = ticket.face_value - deposit.escrow;
                <Deposits<T>>::mutate(&ticket.sender, |deposit| {
                    deposit.escrow = (0 as u32).into();
                    deposit.penalty -= penalty_amount;
                })
            } else {
                <Deposits<T>>::mutate(&ticket.sender, |deposit| {
                    deposit.escrow = deposit.escrow - ticket.face_value;
                })
            }

            T::Currency::deposit_into_existing(&ticket.receiver, ticket.face_value)?;
        }
    }
}

fn withdraw_to<T: Trait>(account: T::AccountId) -> Result<(), DispatchError> {
    let mut deposit = <Deposits<T>>::get(&account);
    ensure!(deposit.unlock_at > (0 as u32).into(), Error::<T>::DepositNotUnlocked);
    ensure!(deposit.unlock_at < T::Time::now(), Error::<T>::UnlockPeriodNotComplete);

    let amount: BalanceOf<T> = deposit.escrow + deposit.penalty;

    // Set values to 0
    deposit.escrow = (0 as u32).into();
    deposit.penalty = (0 as u32).into();

    // Relock so if more funds are deposited they may be unlocked again
    deposit.unlock_at = (0 as u32).into();

    T::Currency::deposit_into_existing(&account, amount)?;
    <Deposits<T>>::insert(&account, deposit);
    Ok(())
}

pub fn get_ticket_hash<T: Trait>(ticket: &TicketOf<T>) -> [u8; 32] {
    keccak_256(ticket.encode().as_ref())
}

pub fn ensure_valid_winning_ticket<T: Trait>(ticket: &TicketOf<T>, ticket_hash: &[u8; 32], receiver_rand: U256, sig: MultiSignature) -> Result<(), DispatchError> {
    ensure!(ticket.expiration == (0 as u32).into() || ticket.expiration >= T::Time::now(), Error::<T>::ExpiredTicket);
    ensure!(!UsedTickets::get(ticket_hash), Error::<T>::TicketAlreadyRedeemed);
    ensure!(keccak_256(receiver_rand.encode().as_ref()) == ticket.receiver_rand_hash, Error::<T>::HashesDontMatch);

    // Verify that the signature given is from the ticket sender
    ensure!(is_valid_signature::<T>(&sig, ticket_hash, &ticket.sender), Error::<T>::InvalidSignature);
    // Check if the ticket is a winning ticket
    ensure!(U256::from_big_endian(&keccak_256((sig, receiver_rand).encode().as_ref())) < ticket.win_prob, Error::<T>::TicketNotAWinner);

    Ok(())
}

pub fn is_valid_signature<T: Trait>(sig: &MultiSignature, ticket_hash: &[u8], account: &T::AccountId) -> bool {
    if let Ok(account_id) = AccountId32::try_from(account.encode().as_ref()) {
        return sig.verify(ticket_hash, &account_id)
    }
    false
}
