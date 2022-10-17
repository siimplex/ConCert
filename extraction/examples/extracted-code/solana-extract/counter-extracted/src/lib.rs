#![allow(dead_code)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(unused_variables)]

use borsh::{BorshDeserialize, BorshSerialize};
use bumpalo::Bump;
use solana_program::{
    account_info::AccountInfo, clock::Clock, entrypoint, entrypoint::ProgramResult,
    program::invoke, program_error::ProgramError, pubkey::Pubkey, rent::Rent, sysvar::Sysvar,
};
// use concert_std::{ActionBody, SpecialCallBody};
use core::marker::PhantomData;
use std::rc::Rc;
use std::slice::Iter;
pub struct SerializedValue<'a>(&'a Vec<u8>);

#[derive(Clone)]
pub enum SpecialCallBody<'a> {
    TransferOwnership(AccountInfo<'a>, AccountInfo<'a>, AccountInfo<'a>), /* old_owner, account, new_owner */
    CheckRentExempt(AccountInfo<'a>), /* account                       */
  }
  
  #[derive(Clone)]
  pub enum ActionBody<'a> {
    Transfer(AccountInfo<'a>, AccountInfo<'a>, u64), /* from, to, amount  */
    Call(AccountInfo<'a>, &'a SerializedValue<'a>),  /* to, message */
    SpecialCall(AccountInfo<'a>, &'a SpecialCallBody<'a>), /* to, body    */
  }

  fn __nat_succ(x: u64) -> u64 {
    x.checked_add(1).unwrap()
}

macro_rules! __nat_elim {
  ($zcase:expr, $pred:ident, $scase:expr, $val:expr) => {{
    let v = $val;
    if v == 0 {
      $zcase
    } else {
      let $pred = v - 1;
      $scase
    }
  }};
}

macro_rules! __andb {
  ($b1:expr, $b2:expr) => {
    $b1 && $b2
  };
}
macro_rules! __orb {
  ($b1:expr, $b2:expr) => {
    $b1 || $b2
  };
}

fn __pos_onebit(x: u64) -> u64 {
  x.checked_mul(2).unwrap() + 1
}

fn __pos_zerobit(x: u64) -> u64 {
  x.checked_mul(2).unwrap()
}

macro_rules! __pos_elim {
  ($p:ident, $onebcase:expr, $p2:ident, $zerobcase:expr, $onecase:expr, $val:expr) => {{
    let n = $val;
    if n == 1 {
      $onecase
    } else if (n & 1) == 0 {
      let $p2 = n >> 1;
      $zerobcase
    } else {
      let $p = n >> 1;
      $onebcase
        }
    }};
}

fn __Z_frompos(z: u64) -> i64 {
    use std::convert::TryFrom;

    i64::try_from(z).unwrap()
}

fn __Z_fromneg(z: u64) -> i64 {
  use std::convert::TryFrom;
  
  i64::try_from(z).unwrap().checked_neg().unwrap()
}

macro_rules! __Z_elim {
  ($zero_case:expr, $p:ident, $pos_case:expr, $p2:ident, $neg_case:expr, $val:expr) => {{
    let n = $val;
    if n == 0 {
      $zero_case
    } else if n < 0 {
      let $p2 = n.unsigned_abs();
      $neg_case
    } else {
      let $p = n as u64;
      $pos_case
    }
  }};
}

fn __N_frompos(z: u64) -> u64 {
  z
}

macro_rules! __N_elim {
  ($zero_case:expr, $p:ident, $pos_case:expr, $val:expr) => {{
    let $p = $val;
    if $p == 0 {
      $zero_case
    } else {
      $pos_case
    }
  }};
}

type __pair<A, B> = (A, B);

macro_rules! __pair_elim {
  ($fst:ident, $snd:ident, $body:expr, $p:expr) => {{
    let ($fst, $snd) = $p;
    $body
  }};
}

fn __mk_pair<A: Copy, B: Copy>(a: A, b: B) -> __pair<A, B> {
  (a, b)
}

fn hint_app<TArg, TRet>(f: &dyn Fn(TArg) -> TRet) -> &dyn Fn(TArg) -> TRet {
  f
}

#[derive(Debug, PartialEq, Eq)]
enum ProcessError {
  DeserialMsg,
  DeserialOldState,
  SerialNewState,
  ConvertActions, // Cannot convert ConCert actions to Concordium actions
    Error,
}

impl From<ProcessError> for ProgramError {
    fn from(e: ProcessError) -> Self {
        ProgramError::Custom(e as u32)
    }
}

type Address<'a> = solana_program::pubkey::Pubkey;

type SliceAccountInformation<'ac> = &'ac [AccountInfo<'ac>];

#[derive(Clone, BorshSerialize, BorshDeserialize, PartialEq)]
pub enum Chain<'a> {
    build_chain(PhantomData<&'a ()>, u64, u64, u64),
}

#[derive(Clone, BorshSerialize, BorshDeserialize, PartialEq)]
pub enum ContractInstruction<'a> {
    Init(PhantomData<&'a ()>, i64),
    Inc(PhantomData<&'a ()>, i64),
    Dec(PhantomData<&'a ()>, i64),
}

#[derive(Clone, BorshSerialize, BorshDeserialize, PartialEq)]
pub enum State<'a> {
    build_state(PhantomData<&'a ()>, i64, bool, Address<'a>),
}

impl<'a> State<'a> {
    pub fn deserialize(input: &[u8], _arena: &'a bumpalo::Bump) -> Result<State<'a>, ProgramError> {
        let result: State = State::try_from_slice(input).unwrap();
        Ok(result)
    }
}

impl<'a> ContractInstruction<'a> {
    pub fn deserialize(
        input: &[u8],
        _arena: &'a bumpalo::Bump,
    ) -> Result<ContractInstruction<'a>, ProgramError> {
        let result: ContractInstruction = ContractInstruction::try_from_slice(input).unwrap();
        Ok(result)
    }
}

impl<'a> Chain<'a> {
    pub fn deserialize(input: &[u8], _arena: &'a bumpalo::Bump) -> Result<Chain<'a>, ProgramError> {
        let result: Chain = Chain::try_from_slice(input).unwrap();
        Ok(result)
    }
}

use bumpalo::collections::Vec as BumpVec;

struct Program<'a> {
    __accounts: Vec<AccountInfo<'a>>,
    __alloc: bumpalo::Bump,
    __program_id: Pubkey,
}

impl<'a> Program<'a> {
    fn new(accounts: Vec<AccountInfo<'a>>, key: Pubkey) -> Self {
        Program {
            __accounts: accounts,
            __alloc: bumpalo::Bump::new(),
            __program_id: key,

        }
    }

    fn alloc<T>(&'a self, t: T) -> &'a T {
        self.__alloc.alloc(t)
    }

    fn closure<TArg, TRet>(&'a self, F: impl Fn(TArg) -> TRet + 'a) -> &'a dyn Fn(TArg) -> TRet {
        self.__alloc.alloc(F)
    }

    fn new_iter<A>(&'a self) -> &'a dyn Fn(&[A]) -> Iter<'_, A> {
        self.alloc(move |l| l.iter())
    }

    fn iter_next2(
        &'a self,
    ) -> impl Fn(
        SliceAccountInformation<'a>,
    ) -> &'a dyn Fn(&mut usize) -> Result<&'a AccountInfo<'a>, ProgramError> {
        move |slc: SliceAccountInformation| {
            self.alloc(move |index| {
                let item = slc.get(*index).ok_or(ProgramError::AccountBorrowFailed);
                *index += 1;
                item
            })
        }
    }

    fn deser_data_account(
        &'a self,
    ) -> impl Fn(()) -> &'a dyn Fn(&'a AccountInfo) -> Result<State<'a>, ProgramError> {
        move |_| {
            self.alloc(move |v| match State::try_from_slice(&v.data.borrow()) {
                Ok(val) => Ok(val),
                Err(_) => Err(ProgramError::BorshIoError(String::from(
                    "Deserialization error",
                ))),
            })
        }
    }

    fn get_account_address(&'a self) -> &'a dyn Fn(&'a AccountInfo<'a>) -> Pubkey {
        self.alloc(move |acc| *acc.key)
    }

    fn ser_data_account<T: BorshSerialize>(
        &'a self,
    ) -> impl Fn(()) -> &'a dyn Fn(&'a T) -> &'a dyn Fn(&'a AccountInfo<'a>) -> Result<(), ProgramError>
    {
        move |_| {
            self.alloc(move |v| {
                self.alloc(move |acc| {
                    match (*v).serialize(&mut &mut (*acc).data.borrow_mut()[..]) {
                        Ok(_) => Ok(()),
                        Err(_) => Err(ProgramError::BorshIoError(String::from(
                            "Serialization error",
                        ))),
                    }
                })
            })
        }
    }

    fn counter_init(
        &'a self,
        accounts: SliceAccountInformation<'a>,
        init_value: i64,
    ) -> Result<(), ProgramError> {
        let mut index = 0;
        match self.iter_next2()(accounts)(&mut index) {
            Ok(t) => match self.iter_next2()(accounts)(&mut index) {
                Ok(t2) => match self.deser_data_account()(())(t2) {
                    Ok(t3) => {
                        let initialized_state = self.alloc(State::build_state(
                            PhantomData,
                            init_value,
                            true,
                            self.get_account_address()(t),
                        ));
                        match self.ser_data_account()(())(initialized_state)(t2) {
                            Ok(t4) => Ok(()),
                            Err(e) => Err(e),
                        }
                    }
                    Err(e) => Err(e),
                },
                Err(e) => Err(e),
            },
            Err(e) => Err(e),
        }
    }
    fn counter_init__curried(
        &'a self,
    ) -> &'a dyn Fn(SliceAccountInformation<'a>) -> &'a dyn Fn(i64) -> Result<(), ProgramError>
    {
        self.closure(move |accounts| {
            self.closure(move |init_value| self.counter_init(accounts, init_value))
        })
    }

    fn counter(&'a self, accounts: SliceAccountInformation<'a>) -> Result<(), ProgramError> {
        let mut index = 0;
        match self.iter_next2()(accounts)(&mut index) {
            Ok(t) => self.counter_init(accounts, 0),
            Err(e) => Err(e),
        }
    }
    fn counter__curried(
        &'a self,
    ) -> &'a dyn Fn(SliceAccountInformation<'a>) -> Result<(), ProgramError> {
        self.closure(move |accounts| self.counter(accounts))
    }

    fn counter_process(
        &'a self,
        chain: &'a Chain<'a>,
        accounts: &'a [AccountInfo<'a>],
        inst: Option<&'a ContractInstruction<'a>>,
    ) -> Result<(), ProgramError> {
        match inst {
            Some(m) => self.counter(accounts),
            None => Err(ProgramError::InvalidInstructionData),
        }
    }
    fn counter_process__curried(
        &'a self,
    ) -> &'a dyn Fn(
        &'a Chain<'a>,
    ) -> &'a dyn Fn(
        SliceAccountInformation<'a>,
    ) -> &'a dyn Fn(
        Option<&'a ContractInstruction<'a>>,
    ) -> Result<(), ProgramError> {
        self.closure(move |chain| {
            self.closure(move |accounts| {
                self.closure(move |inst| self.counter_process(chain, accounts, inst))
            })
        })
    }

    fn convert_special_action(
        &'a self,
        to_account: &AccountInfo<'a>,
        body: &SpecialCallBody<'a>,
    ) -> Result<(), ProgramError> {
        let cbody =
            if let SpecialCallBody::TransferOwnership(old_owner, owned_account, new_owner) = body {
                let (pda, _nonce) = Pubkey::find_program_address(&[b"Counter"], &self.__program_id);

                let owner_change_ix = spl_token::instruction::set_authority(
                    to_account.key,
                    owned_account.key,
                    Some(&pda),
                    spl_token::instruction::AuthorityType::AccountOwner,
                    old_owner.key,
                    &[&old_owner.key],
                )?;

                invoke(
                    &owner_change_ix,
                    &[owned_account.clone(), old_owner.clone(), to_account.clone()],
                )?;
            } else if let SpecialCallBody::CheckRentExempt(account_checked) = body {
                let rent = &Rent::from_account_info(to_account)?;
                if !rent.is_exempt(account_checked.lamports(), account_checked.data_len()) {
                    return Err(ProcessError::Error.into());
                }
            } else {
                return Err(ProcessError::ConvertActions.into());
            };
        Ok(())
    }

    fn convert_action(&'a self, act: &ActionBody<'a>) -> Result<(), ProgramError> {
        let cact = if let ActionBody::Transfer(donator_account, receiver_account, amount) = act {
            if **donator_account.try_borrow_mut_lamports()? >= *amount {
                **receiver_account.try_borrow_mut_lamports()? += amount;
                **donator_account.try_borrow_mut_lamports()? -= amount;
            } else {
                return Err(ProcessError::Error.into());
            };
        } else if let ActionBody::SpecialCall(to, body) = act {
            return self.convert_special_action(to, body);
        } else {
            return Err(ProcessError::ConvertActions.into());
        };
        Ok(())
    }

    // fn counter_process2(&'a self, chain: &'a Chain<'a>, accounts: &[AccountInfo], inst: Option<&'a ContractInstruction<'a>>) -> Result<(), ProgramError> {
    //   Ok(())
    // }
}

fn process_instruction<'a>(
    program_id: &Pubkey,
    accounts: &'a [AccountInfo<'a>],
    instruction_data: &[u8],
) -> ProgramResult {
    let prg = Program::new(accounts.to_vec(), *program_id);    

    let msg: ContractInstruction =
        match <ContractInstruction>::deserialize(instruction_data, &prg.__alloc) {
            Ok(m) => m,
            Err(_) => return Err(ProcessError::DeserialMsg.into()),
        };
    let cchain = Chain::build_chain(
        PhantomData,
        0, // No chain height
        Clock::get().unwrap().unix_timestamp as u64,
        0, // No finalized height
    );
    prg.counter_process(&cchain, &prg.__accounts[..], Some(&msg));
    Ok(())
}
entrypoint!(process_instruction);