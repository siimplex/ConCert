
#![allow(dead_code)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(unused_variables)]

use solana_program::{
  account_info::AccountInfo,
  clock::Clock,
  entrypoint,
  entrypoint::ProgramResult,
  program_error::ProgramError,
  pubkey::Pubkey,
  rent::Rent,
  sysvar::Sysvar,
  program::invoke,
};
use borsh::{BorshSerialize, BorshDeserialize};
use concert_std::{ActionBody, SpecialCallBody};
use core::marker::PhantomData;

fn __nat_succ(x: u64) -> u64 {
  x.checked_add(1).unwrap()
}

macro_rules! __nat_elim {
    ($zcase:expr, $pred:ident, $scase:expr, $val:expr) => {
        { let v = $val;
        if v == 0 { $zcase } else { let $pred = v - 1; $scase } }
    }
}

macro_rules! __andb { ($b1:expr, $b2:expr) => { $b1 && $b2 } }
macro_rules! __orb { ($b1:expr, $b2:expr) => { $b1 || $b2 } }

fn __pos_onebit(x: u64) -> u64 {
  x.checked_mul(2).unwrap() + 1
}

fn __pos_zerobit(x: u64) -> u64 {
  x.checked_mul(2).unwrap()
}

macro_rules! __pos_elim {
    ($p:ident, $onebcase:expr, $p2:ident, $zerobcase:expr, $onecase:expr, $val:expr) => {
        {
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
        }
    }
}

fn __Z_frompos(z: u64) -> i64 {
  use std::convert::TryFrom;

  i64::try_from(z).unwrap()
}

fn __Z_fromneg(z : u64) -> i64 {
  use std::convert::TryFrom;

  i64::try_from(z).unwrap().checked_neg().unwrap()
}

macro_rules! __Z_elim {
    ($zero_case:expr, $p:ident, $pos_case:expr, $p2:ident, $neg_case:expr, $val:expr) => {
        {
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
        }
    }
}

fn __N_frompos(z: u64) -> u64 {
  z
}

macro_rules! __N_elim {
    ($zero_case:expr, $p:ident, $pos_case:expr, $val:expr) => {
        { let $p = $val; if $p == 0 { $zero_case } else { $pos_case } }
    }
}

type __pair<A, B> = (A, B);

macro_rules! __pair_elim {
    ($fst:ident, $snd:ident, $body:expr, $p:expr) => {
        { let ($fst, $snd) = $p; $body }
    }
}

fn __mk_pair<A: Copy, B: Copy>(a: A, b: B) -> __pair<A, B> { (a, b) }

fn hint_app<TArg, TRet>(f: &dyn Fn(TArg) -> TRet) -> &dyn Fn(TArg) -> TRet {
  f
}



#[derive(Debug, PartialEq, Eq)]
enum ProcessError {
    DeserialMsg,
    DeserialOldState,
    SerialNewState,
    ConvertActions, // Cannot convert ConCert actions to Concordium actions
    Error
}

impl From<ProcessError> for ProgramError {
    fn from(e: ProcessError) -> Self {
        ProgramError::Custom(e as u32)
    }
}


type Address<'a> = solana_program::pubkey::Pubkey;

type SliceAccountInformation<'a> = &'a[AccountInfo<'a>];

#[derive(Clone, BorshSerialize, BorshDeserialize, PartialEq)]
pub enum Chain<'a> {
  build_chain(PhantomData<&'a ()>, u64, u64, u64)
}

#[derive(Clone, BorshSerialize, BorshDeserialize, PartialEq)]
pub enum ContractInstruction<'a> {
  Init(PhantomData<&'a ()>, i64),
  Inc(PhantomData<&'a ()>, i64),
  Dec(PhantomData<&'a ()>, i64)
}

#[derive(Clone, BorshSerialize, BorshDeserialize, PartialEq)]
pub enum State<'a> {
  build_state(PhantomData<&'a ()>, i64, bool, Address<'a>)
}

struct Program {
  __alloc: bumpalo::Bump,__program_id : solana_program::pubkey::Pubkey,
}

impl<'a> Program {
fn new(key : Pubkey) -> Self {
  Program {
    __alloc: bumpalo::Bump::new(),__program_id : key,
  }
}

fn alloc<T>(&self, t: T) -> & T {
  self.__alloc.alloc(t)
}

fn closure<TArg, TRet>(&'a self, F: impl Fn(TArg) -> TRet + 'a) -> &'a dyn Fn(TArg) -> TRet {
  self.__alloc.alloc(F)
}


fn convert_special_action(&'a self, to_account: &AccountInfo<'a>, body: &SpecialCallBody<'a>) -> Result<(), ProgramError> {
  let cbody =
    if let SpecialCallBody::TransferOwnership(old_owner, owned_account, new_owner) = body {
        let (pda, _nonce) = Pubkey::find_program_address(&[b"contract"], &self.__program_id);

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
            &[
                *owned_account.clone(),
                *old_owner.clone(),
                to_account.clone(),
            ],
        )?;
    } else if let SpecialCallBody:: CheckRentExempt(account_checked) = body {
        let rent = &Rent::from_account_info(to_account)?;
            if !rent.is_exempt(account_checked.lamports(), account_checked.data_len()) {
                return Err(ProcessError::Error.into())
            }
    } else {
        return Err(ProcessError::ConvertActions.into())
    };
  Ok(())
}

fn convert_action(&'a self, act: &ActionBody<'a>) -> Result<(), ProgramError> {
  let cact =
      if let ActionBody::Transfer(donator_account, receiver_account, amount) = act {
          if **donator_account.try_borrow_mut_lamports()? >= *amount as u64 {
              **receiver_account.try_borrow_mut_lamports()? += *amount as u64;
              **donator_account.try_borrow_mut_lamports()? -= *amount as u64;
          } else {
              return Err(ProcessError::Error.into())
          };
      } else if let ActionBody::SpecialCall(to, body) = act {
          return self.convert_special_action(to, body)
      } else {
          return Err(ProcessError::ConvertActions.into())
      };
      Ok(())
}

fn next_account<'t>(&'t self) -> impl (Fn(SliceAccountInformation<'a>) -> &'t dyn Fn(i64) -> Result<&'a AccountInfo<'a>, ProgramError>) + 't where 'a: 't, { move |slc: SliceAccountInformation| { self.alloc(move |index| { slc.get(index as usize).ok_or(ProgramError::AccountBorrowFailed) }) }}

fn deser_data_account(&'a self) -> impl Fn(()) -> &'a dyn Fn(&'a AccountInfo) -> Result<State<'a>, ProgramError> { move |_| { self.alloc(move |v| { match State::try_from_slice(&v.data.borrow()) { Ok(val) => Ok(val), Err(_) => Err(ProgramError::BorshIoError(String::from("Deserialization error")))}})}}

fn counter_init(&'a self, owner_address: Address<'a>, init_value: i64) -> &'a State<'a> {
  self.alloc(
    State::build_state(
      PhantomData,
      init_value,
      false,
      owner_address))
}
fn counter_init__curried(&'a self) -> &'a dyn Fn(Address<'a>) -> &'a dyn Fn(i64) -> &'a State<'a> {
  self.closure(move |owner_address| {
    self.closure(move |init_value| {
      self.counter_init(
        owner_address,
        init_value)
    })
  })
}

fn get_account_owner_address<'ai>(&'a self) -> &'a dyn Fn(&'ai AccountInfo<'ai>) -> Pubkey { self.alloc(move |acc| *acc.owner) }

fn ltb(&'a self, a: i64, b: i64) -> bool { a < b }
fn ltb__curried(&'a self) -> &'a dyn Fn(i64) -> &'a dyn Fn(i64) -> bool {
  self.closure(move |x| {
    self.closure(move |y| {
      self.ltb(
        x,
        y)
    })
  })
}

fn add(&'a self, a: i64, b: i64) -> i64 { a.checked_add(b).unwrap() }
fn add__curried(&'a self) -> &'a dyn Fn(i64) -> &'a dyn Fn(i64) -> i64 {
  self.closure(move |x| {
    self.closure(move |y| {
      self.add(
        x,
        y)
    })
  })
}

fn count(&'a self, s: &'a State<'a>) -> i64 {
  match s {
    &State::build_state(_, count2, active, owner) => {
      count2
    },
  }
}
fn count__curried(&'a self) -> &'a dyn Fn(&'a State<'a>) -> i64 {
  self.closure(move |s| {
    self.count(
      s)
  })
}

fn owner(&'a self, s: &'a State<'a>) -> Address<'a> {
  match s {
    &State::build_state(_, count2, active, owner2) => {
      owner2
    },
  }
}
fn owner__curried(&'a self) -> &'a dyn Fn(&'a State<'a>) -> Address<'a> {
  self.closure(move |s| {
    self.owner(
      s)
  })
}

fn increment(&'a self, n: i64, st: &'a State<'a>) -> &'a State<'a> {
  self.alloc(
    State::build_state(
      PhantomData,
      self.add(
        self.count(
          st),
        n),
      true,
      self.owner(
        st)))
}
fn increment__curried(&'a self) -> &'a dyn Fn(i64) -> &'a dyn Fn(&'a State<'a>) -> &'a State<'a> {
  self.closure(move |n| {
    self.closure(move |st| {
      self.increment(
        n,
        st)
    })
  })
}

fn sub(&'a self, a: i64, b: i64) -> i64 { a.checked_sub(b).unwrap() }
fn sub__curried(&'a self) -> &'a dyn Fn(i64) -> &'a dyn Fn(i64) -> i64 {
  self.closure(move |m| {
    self.closure(move |n| {
      self.sub(
        m,
        n)
    })
  })
}

fn decrement(&'a self, n: i64, st: &'a State<'a>) -> &'a State<'a> {
  self.alloc(
    State::build_state(
      PhantomData,
      self.sub(
        self.count(
          st),
        n),
      true,
      self.owner(
        st)))
}
fn decrement__curried(&'a self) -> &'a dyn Fn(i64) -> &'a dyn Fn(&'a State<'a>) -> &'a State<'a> {
  self.closure(move |n| {
    self.closure(move |st| {
      self.decrement(
        n,
        st)
    })
  })
}

fn ser_data_account<'ai, T : BorshSerialize>(&'a self) -> impl Fn(()) -> &'a dyn Fn(&'a T) -> &'a dyn Fn(&'ai AccountInfo<'ai>) -> Result<(), ProgramError> { move |_| { self.alloc( move |v| self.alloc( move |acc| { match (*v).serialize(&mut &mut (*acc).data.borrow_mut()[..]) { Ok(_) => Ok(()), Err(_) => Err(ProgramError::BorshIoError(String::from("Serialization error")))}}))}}

fn counter(&'a self, accounts: SliceAccountInformation<'a>, inst: &'a ContractInstruction<'a>) -> Result<(), ProgramError> {
  let index =
    0;
  match self.next_account()(
          accounts)(
          index) {
    Ok(t) => {
      let index2 =
        __Z_frompos(
          1);
      match self.next_account()(
              accounts)(
              index2) {
        Ok(t2) => {
          match self.deser_data_account()(
                  ())(
                  t) {
            Ok(state) => {
              let new_state =
                match inst {
                  &ContractInstruction::Init(_, i) => {
                    Some(
                      self.counter_init(
                        self.get_account_owner_address()(
                          t2),
                        i))
                  },
                  &ContractInstruction::Inc(_, i) => {
                    match self.ltb(
                            0,
                            i) {
                      true => {
                        Some(
                          self.increment(
                            i,
                            state))
                      },
                      false => {
                        None
                      },
                    }
                  },
                  &ContractInstruction::Dec(_, i) => {
                    match self.ltb(
                            0,
                            i) {
                      true => {
                        Some(
                          self.decrement(
                            i,
                            state))
                      },
                      false => {
                        None
                      },
                    }
                  },
                };
              match new_state {
                Some(st) => {
                  match self.ser_data_account()(
                          ())(
                          st)(
                          t) {
                    Ok(t3) => {
                      Ok(
                        ())
                    },
                    Err(e) => {
                      Err(
                        e)
                    },
                  }
                },
                None => {
                  Err(
                    ProgramError::InvalidAccountData)
                },
              }
            },
            Err(e) => {
              Err(
                e)
            },
          }
        },
        Err(e) => {
          Err(
            e)
        },
      }
    },
    Err(e) => {
      Err(
        e)
    },
  }
}
fn counter__curried(&'a self) -> &'a dyn Fn(SliceAccountInformation<'a>) -> &'a dyn Fn(&'a ContractInstruction<'a>) -> Result<(), ProgramError> {
  self.closure(move |accounts| {
    self.closure(move |inst| {
      self.counter(
        accounts,
        inst)
    })
  })
}

fn counter_process(&'a self, chain: &'a Chain<'a>, accounts: SliceAccountInformation<'a>, inst: Option<&'a ContractInstruction<'a>>) -> Result<(), ProgramError> {
  match inst {
    Some(m) => {
      self.counter(
        accounts,
        m)
    },
    None => {
      Err(
        ProgramError::InvalidInstructionData)
    },
  }
}
fn counter_process__curried(&'a self) -> &'a dyn Fn(&'a Chain<'a>) -> &'a dyn Fn(SliceAccountInformation<'a>) -> &'a dyn Fn(Option<&'a ContractInstruction<'a>>) -> Result<(), ProgramError> {
  self.closure(move |chain| {
    self.closure(move |accounts| {
      self.closure(move |inst| {
        self.counter_process(
          chain,
          accounts,
          inst)
      })
    })
  })
}
}
fn process_instruction<'ai>(
    program_id: &Pubkey,
    accounts: SliceAccountInformation<'ai>,
    instruction_data: &[u8],
) -> ProgramResult {
    let prg = Program::new(*program_id);
    let msg : ContractInstruction = 
        match ContractInstruction::try_from_slice(instruction_data) {
            Ok(m) => m,
            Err(_) => return Err(ProcessError::DeserialMsg.into())
        };
    let cchain =
        Chain::build_chain(
            PhantomData,
            0, // No chain height
            Clock::get().unwrap().unix_timestamp as u64,
            0 // No finalized height
        );
    prg.counter_process(&cchain, accounts, Some(&msg))
}
entrypoint!(process_instruction);
