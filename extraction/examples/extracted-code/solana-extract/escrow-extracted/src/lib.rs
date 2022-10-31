
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

type Amount<'a> = i64;

type SliceAccountInformation<'a> = &'a[AccountInfo<'a>];

#[derive(Clone, BorshSerialize, BorshDeserialize, PartialEq)]
pub enum Chain<'a> {
  build_chain(PhantomData<&'a ()>, u64, u64, u64)
}

#[derive(Clone, BorshSerialize, BorshDeserialize, PartialEq)]
pub enum ContractInstruction<'a> {
  init_escrow(PhantomData<&'a ()>, Address<'a>, Amount<'a>),
  commit_money(PhantomData<&'a ()>),
  confirm_item_received(PhantomData<&'a ()>),
  withdraw(PhantomData<&'a ()>)
}

#[derive(Clone, BorshSerialize, BorshDeserialize, PartialEq)]
pub enum NextStep<'a> {
  buyer_commit(PhantomData<&'a ()>),
  buyer_confirm(PhantomData<&'a ()>),
  withdrawals(PhantomData<&'a ()>),
  no_next_step(PhantomData<&'a ()>)
}

#[derive(Clone, BorshSerialize, BorshDeserialize, PartialEq)]
pub enum State<'a> {
  build_state(PhantomData<&'a ()>, u64, &'a NextStep<'a>, Address<'a>, Address<'a>, Amount<'a>, Amount<'a>, Amount<'a>)
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

fn get_account_is_signer<'ai>(&'a self) -> &'a dyn Fn(&'ai AccountInfo<'ai>) -> bool { self.alloc(move |acc| acc.is_signer) }

fn exec_act(&'a self) -> &'a dyn Fn(ActionBody<'a>) -> Result<(), ProgramError> { self.alloc(move |act|self.convert_action(&act)) }

fn current_slot(&'a self, c: &'a Chain<'a>) -> u64 {
  match c {
    &Chain::build_chain(_, chain_height, current_slot2, finalized_height) => {
      current_slot2
    },
  }
}
fn current_slot__curried(&'a self) -> &'a dyn Fn(&'a Chain<'a>) -> u64 {
  self.closure(move |c| {
    self.current_slot(
      c)
  })
}

fn get_account_address<'ai>(&'a self) -> &'a dyn Fn(&'ai AccountInfo<'ai>) -> Pubkey { self.alloc(move |acc| *acc.key) }

fn ser_data_account<'ai, T : BorshSerialize>(&'a self) -> impl Fn(()) -> &'a dyn Fn(&'a T) -> &'a dyn Fn(&'ai AccountInfo<'ai>) -> Result<(), ProgramError> { move |_| { self.alloc( move |v| self.alloc( move |acc| { match (*v).serialize(&mut &mut (*acc).data.borrow_mut()[..]) { Ok(_) => Ok(()), Err(_) => Err(ProgramError::BorshIoError(String::from("Serialization error")))}}))}}

fn mul(&'a self, a: i64, b: i64) -> i64 { a.checked_mul(b).unwrap() }
fn mul__curried(&'a self) -> &'a dyn Fn(i64) -> &'a dyn Fn(i64) -> i64 {
  self.closure(move |x| {
    self.closure(move |y| {
      self.mul(
        x,
        y)
    })
  })
}

fn gtb(&'a self, a: i64, b: i64) -> bool { a > b }
fn gtb__curried(&'a self) -> &'a dyn Fn(i64) -> &'a dyn Fn(i64) -> bool {
  self.closure(move |x| {
    self.closure(move |y| {
      self.gtb(
        x,
        y)
    })
  })
}

fn get_account_balance(&'a self) -> &'a dyn Fn(&'a AccountInfo<'a>) -> i64 { self.alloc(move |acc| **acc.lamports.borrow() as i64) }

fn init(&'a self, chain: &'a Chain<'a>, accounts: SliceAccountInformation<'a>, buyer: Address<'a>, item_price: Amount<'a>) -> Result<(), ProgramError> {
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
          match match self.get_account_is_signer()(
                        t) {
                  true => {
                    Ok(
                      ())
                  },
                  false => {
                    Err(
                      ProgramError::MissingRequiredSignature)
                  },
                } {
            Ok(t3) => {
              match self.exec_act()(
                      ActionBody::SpecialCall(
                        t2,
                        SpecialCallBody::CheckRentExempt(
                          t2))) {
                Ok(t4) => {
                  let init_state =
                    self.alloc(
                      State::build_state(
                        PhantomData,
                        self.current_slot(
                          chain),
                        self.alloc(
                          NextStep::buyer_commit(
                            PhantomData)),
                        self.get_account_address()(
                          t),
                        buyer,
                        0,
                        0,
                        item_price));
                  match self.ser_data_account()(
                          ())(
                          init_state)(
                          t2) {
                    Ok(t5) => {
                      let expected =
                        self.mul(
                          item_price,
                          __Z_frompos(
                            __pos_zerobit(
                              1)));
                      match match self.gtb(
                                    self.get_account_balance()(
                                      t),
                                    expected) {
                              true => {
                                Ok(
                                  ())
                              },
                              false => {
                                Err(
                                  ProgramError::InsufficientFunds)
                              },
                            } {
                        Ok(t6) => {
                          match self.exec_act()(
                                  ActionBody::Transfer(
                                    t,
                                    t2,
                                    expected)) {
                            Ok(t7) => {
                              Ok(
                                ())
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
    },
    Err(e) => {
      Err(
        e)
    },
  }
}
fn init__curried(&'a self) -> &'a dyn Fn(&'a Chain<'a>) -> &'a dyn Fn(SliceAccountInformation<'a>) -> &'a dyn Fn(Address<'a>) -> &'a dyn Fn(Amount<'a>) -> Result<(), ProgramError> {
  self.closure(move |chain| {
    self.closure(move |accounts| {
      self.closure(move |buyer| {
        self.closure(move |item_price| {
          self.init(
            chain,
            accounts,
            buyer,
            item_price)
        })
      })
    })
  })
}

fn deser_data_account(&'a self) -> impl Fn(()) -> &'a dyn Fn(&'a AccountInfo) -> Result<State<'a>, ProgramError> { move |_| { self.alloc(move |v| { match State::try_from_slice(&v.data.borrow()) { Ok(val) => Ok(val), Err(_) => Err(ProgramError::BorshIoError(String::from("Deserialization error")))}})}}

fn address_eqb(&'a self) -> impl Fn(solana_program::pubkey::Pubkey) -> &'a dyn Fn(solana_program::pubkey::Pubkey) -> bool { move |a| self.alloc(move |b| a == b) }

fn buyer(&'a self, s: &'a State<'a>) -> Address<'a> {
  match s {
    &State::build_state(_, last_action, next_step, seller, buyer2, seller_withdrawable, buyer_withdrawable, expected_amount) => {
      buyer2
    },
  }
}
fn buyer__curried(&'a self) -> &'a dyn Fn(&'a State<'a>) -> Address<'a> {
  self.closure(move |s| {
    self.buyer(
      s)
  })
}

fn next_step(&'a self, s: &'a State<'a>) -> &'a NextStep<'a> {
  match s {
    &State::build_state(_, last_action, next_step2, seller, buyer2, seller_withdrawable, buyer_withdrawable, expected_amount) => {
      next_step2
    },
  }
}
fn next_step__curried(&'a self) -> &'a dyn Fn(&'a State<'a>) -> &'a NextStep<'a> {
  self.closure(move |s| {
    self.next_step(
      s)
  })
}

fn expected_amount(&'a self, s: &'a State<'a>) -> Amount<'a> {
  match s {
    &State::build_state(_, last_action, next_step2, seller, buyer2, seller_withdrawable, buyer_withdrawable, expected_amount2) => {
      expected_amount2
    },
  }
}
fn expected_amount__curried(&'a self) -> &'a dyn Fn(&'a State<'a>) -> Amount<'a> {
  self.closure(move |s| {
    self.expected_amount(
      s)
  })
}

fn last_action(&'a self, s: &'a State<'a>) -> u64 {
  match s {
    &State::build_state(_, last_action2, next_step2, seller, buyer2, seller_withdrawable, buyer_withdrawable, expected_amount2) => {
      last_action2
    },
  }
}
fn last_action__curried(&'a self) -> &'a dyn Fn(&'a State<'a>) -> u64 {
  self.closure(move |s| {
    self.last_action(
      s)
  })
}

fn seller(&'a self, s: &'a State<'a>) -> Address<'a> {
  match s {
    &State::build_state(_, last_action2, next_step2, seller2, buyer2, seller_withdrawable, buyer_withdrawable, expected_amount2) => {
      seller2
    },
  }
}
fn seller__curried(&'a self) -> &'a dyn Fn(&'a State<'a>) -> Address<'a> {
  self.closure(move |s| {
    self.seller(
      s)
  })
}

fn seller_withdrawable(&'a self, s: &'a State<'a>) -> Amount<'a> {
  match s {
    &State::build_state(_, last_action2, next_step2, seller2, buyer2, seller_withdrawable2, buyer_withdrawable, expected_amount2) => {
      seller_withdrawable2
    },
  }
}
fn seller_withdrawable__curried(&'a self) -> &'a dyn Fn(&'a State<'a>) -> Amount<'a> {
  self.closure(move |s| {
    self.seller_withdrawable(
      s)
  })
}

fn buyer_withdrawable(&'a self, s: &'a State<'a>) -> Amount<'a> {
  match s {
    &State::build_state(_, last_action2, next_step2, seller2, buyer2, seller_withdrawable2, buyer_withdrawable2, expected_amount2) => {
      buyer_withdrawable2
    },
  }
}
fn buyer_withdrawable__curried(&'a self) -> &'a dyn Fn(&'a State<'a>) -> Amount<'a> {
  self.closure(move |s| {
    self.buyer_withdrawable(
      s)
  })
}

fn set_State_next_step(&'a self, f: &'a dyn Fn(&'a NextStep<'a>) -> &'a NextStep<'a>, r: &'a State<'a>) -> &'a State<'a> {
  self.alloc(
    State::build_state(
      PhantomData,
      self.last_action(
        r),
      hint_app(f)(self.next_step(
                    r)),
      self.seller(
        r),
      self.buyer(
        r),
      self.seller_withdrawable(
        r),
      self.buyer_withdrawable(
        r),
      self.expected_amount(
        r)))
}
fn set_State_next_step__curried(&'a self) -> &'a dyn Fn(&'a dyn Fn(&'a NextStep<'a>) -> &'a NextStep<'a>) -> &'a dyn Fn(&'a State<'a>) -> &'a State<'a> {
  self.closure(move |f| {
    self.closure(move |r| {
      self.set_State_next_step(
        f,
        r)
    })
  })
}

fn buyer_commits(&'a self, accounts: SliceAccountInformation<'a>) -> Result<(), ProgramError> {
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
                  t2) {
            Ok(t3) => {
              match match self.address_eqb()(
                            self.buyer(
                              t3))(
                            self.get_account_address()(
                              t)) {
                      true => {
                        Ok(
                          ())
                      },
                      false => {
                        Err(
                          ProgramError::InvalidAccountData)
                      },
                    } {
                Ok(t4) => {
                  match match self.next_step(
                                t3) {
                          &NextStep::buyer_commit(_) => {
                            Ok(
                              ())
                          },
                          &NextStep::buyer_confirm(_) => {
                            Err(
                              ProgramError::InvalidInstructionData)
                          },
                          &NextStep::withdrawals(_) => {
                            Err(
                              ProgramError::InvalidInstructionData)
                          },
                          &NextStep::no_next_step(_) => {
                            Err(
                              ProgramError::InvalidInstructionData)
                          },
                        } {
                    Ok(t5) => {
                      let expected =
                        self.mul(
                          self.expected_amount(
                            t3),
                          __Z_frompos(
                            __pos_zerobit(
                              1)));
                      match match self.gtb(
                                    self.get_account_balance()(
                                      t),
                                    expected) {
                              true => {
                                Ok(
                                  ())
                              },
                              false => {
                                Err(
                                  ProgramError::InsufficientFunds)
                              },
                            } {
                        Ok(t6) => {
                          let new_state =
                            self.set_State_next_step(
                              self.closure(move |x| {
                                self.alloc(
                                  NextStep::buyer_confirm(
                                    PhantomData))
                              }),
                              t3);
                          match self.ser_data_account()(
                                  ())(
                                  new_state)(
                                  t2) {
                            Ok(t7) => {
                              match self.exec_act()(
                                      ActionBody::Transfer(
                                        t,
                                        t2,
                                        expected)) {
                                Ok(t8) => {
                                  Ok(
                                    ())
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
fn buyer_commits__curried(&'a self) -> &'a dyn Fn(SliceAccountInformation<'a>) -> Result<(), ProgramError> {
  self.closure(move |accounts| {
    self.buyer_commits(
      accounts)
  })
}

fn set_State_seller_withdrawable(&'a self, f: &'a dyn Fn(Amount<'a>) -> Amount<'a>, r: &'a State<'a>) -> &'a State<'a> {
  self.alloc(
    State::build_state(
      PhantomData,
      self.last_action(
        r),
      self.next_step(
        r),
      self.seller(
        r),
      self.buyer(
        r),
      hint_app(f)(self.seller_withdrawable(
                    r)),
      self.buyer_withdrawable(
        r),
      self.expected_amount(
        r)))
}
fn set_State_seller_withdrawable__curried(&'a self) -> &'a dyn Fn(&'a dyn Fn(Amount<'a>) -> Amount<'a>) -> &'a dyn Fn(&'a State<'a>) -> &'a State<'a> {
  self.closure(move |f| {
    self.closure(move |r| {
      self.set_State_seller_withdrawable(
        f,
        r)
    })
  })
}

fn set_State_buyer_withdrawable(&'a self, f: &'a dyn Fn(Amount<'a>) -> Amount<'a>, r: &'a State<'a>) -> &'a State<'a> {
  self.alloc(
    State::build_state(
      PhantomData,
      self.last_action(
        r),
      self.next_step(
        r),
      self.seller(
        r),
      self.buyer(
        r),
      self.seller_withdrawable(
        r),
      hint_app(f)(self.buyer_withdrawable(
                    r)),
      self.expected_amount(
        r)))
}
fn set_State_buyer_withdrawable__curried(&'a self) -> &'a dyn Fn(&'a dyn Fn(Amount<'a>) -> Amount<'a>) -> &'a dyn Fn(&'a State<'a>) -> &'a State<'a> {
  self.closure(move |f| {
    self.closure(move |r| {
      self.set_State_buyer_withdrawable(
        f,
        r)
    })
  })
}

fn confirm_received(&'a self, accounts: SliceAccountInformation<'a>) -> Result<(), ProgramError> {
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
                  t2) {
            Ok(t3) => {
              match match self.address_eqb()(
                            self.buyer(
                              t3))(
                            self.get_account_address()(
                              t)) {
                      true => {
                        Ok(
                          ())
                      },
                      false => {
                        Err(
                          ProgramError::InvalidAccountData)
                      },
                    } {
                Ok(t4) => {
                  match match self.next_step(
                                t3) {
                          &NextStep::buyer_commit(_) => {
                            Err(
                              ProgramError::InvalidInstructionData)
                          },
                          &NextStep::buyer_confirm(_) => {
                            Ok(
                              ())
                          },
                          &NextStep::withdrawals(_) => {
                            Err(
                              ProgramError::InvalidInstructionData)
                          },
                          &NextStep::no_next_step(_) => {
                            Err(
                              ProgramError::InvalidInstructionData)
                          },
                        } {
                    Ok(t5) => {
                      let new_state =
                        self.set_State_seller_withdrawable(
                          self.closure(move |x| {
                            self.mul(
                              self.expected_amount(
                                t3),
                              __Z_frompos(
                                __pos_onebit(
                                  1)))
                          }),
                          self.set_State_buyer_withdrawable(
                            self.closure(move |x| {
                              self.expected_amount(
                                t3)
                            }),
                            self.set_State_next_step(
                              self.closure(move |x| {
                                self.alloc(
                                  NextStep::withdrawals(
                                    PhantomData))
                              }),
                              t3)));
                      match self.ser_data_account()(
                              ())(
                              new_state)(
                              t2) {
                        Ok(t6) => {
                          Ok(
                            ())
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
fn confirm_received__curried(&'a self) -> &'a dyn Fn(SliceAccountInformation<'a>) -> Result<(), ProgramError> {
  self.closure(move |accounts| {
    self.confirm_received(
      accounts)
  })
}

fn ltb(&'a self, a: u64, b: u64) -> bool { a < b }
fn ltb__curried(&'a self) -> &'a dyn Fn(u64) -> &'a dyn Fn(u64) -> bool {
  self.closure(move |n| {
    self.closure(move |m| {
      self.ltb(
        n,
        m)
    })
  })
}

fn add(&'a self, a: u64, b: u64) -> u64 { a.checked_add(b).unwrap() }
fn add__curried(&'a self) -> &'a dyn Fn(u64) -> &'a dyn Fn(u64) -> u64 {
  self.closure(move |n| {
    self.closure(move |m| {
      self.add(
        n,
        m)
    })
  })
}

fn andb(&'a self, b1: bool, b2: bool) -> bool {
  match b1 {
    true => {
      b2
    },
    false => {
      false
    },
  }
}
fn andb__curried(&'a self) -> &'a dyn Fn(bool) -> &'a dyn Fn(bool) -> bool {
  self.closure(move |b1| {
    self.closure(move |b2| {
      self.andb(
        b1,
        b2)
    })
  })
}

fn eqb(&'a self, a: i64, b: i64) -> bool { a == b }
fn eqb__curried(&'a self) -> &'a dyn Fn(i64) -> &'a dyn Fn(i64) -> bool {
  self.closure(move |x| {
    self.closure(move |y| {
      self.eqb(
        x,
        y)
    })
  })
}

fn withdraw_money(&'a self, chain: &'a Chain<'a>, accounts: SliceAccountInformation<'a>) -> Result<(), ProgramError> {
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
                  t2) {
            Ok(t3) => {
              let from_address =
                self.get_account_address()(
                  t);
              match self.next_step(
                      t3) {
                &NextStep::buyer_commit(_) => {
                  match match self.ltb(
                                self.add(
                                  self.last_action(
                                    t3),
                                  __nat_succ(
                                    __nat_succ(
                                      __nat_succ(
                                        __nat_succ(
                                          __nat_succ(
                                            __nat_succ(
                                              __nat_succ(
                                                __nat_succ(
                                                  __nat_succ(
                                                    __nat_succ(
                                                      __nat_succ(
                                                        __nat_succ(
                                                          __nat_succ(
                                                            __nat_succ(
                                                              __nat_succ(
                                                                __nat_succ(
                                                                  __nat_succ(
                                                                    __nat_succ(
                                                                      __nat_succ(
                                                                        __nat_succ(
                                                                          __nat_succ(
                                                                            __nat_succ(
                                                                              __nat_succ(
                                                                                __nat_succ(
                                                                                  __nat_succ(
                                                                                    __nat_succ(
                                                                                      __nat_succ(
                                                                                        __nat_succ(
                                                                                          __nat_succ(
                                                                                            __nat_succ(
                                                                                              __nat_succ(
                                                                                                __nat_succ(
                                                                                                  __nat_succ(
                                                                                                    __nat_succ(
                                                                                                      __nat_succ(
                                                                                                        __nat_succ(
                                                                                                          __nat_succ(
                                                                                                            __nat_succ(
                                                                                                              __nat_succ(
                                                                                                                __nat_succ(
                                                                                                                  __nat_succ(
                                                                                                                    __nat_succ(
                                                                                                                      __nat_succ(
                                                                                                                        __nat_succ(
                                                                                                                          __nat_succ(
                                                                                                                            __nat_succ(
                                                                                                                              __nat_succ(
                                                                                                                                __nat_succ(
                                                                                                                                  __nat_succ(
                                                                                                                                    __nat_succ(
                                                                                                                                      0))))))))))))))))))))))))))))))))))))))))))))))))))),
                                self.current_slot(
                                  chain)) {
                          true => {
                            Err(
                              ProgramError::InvalidInstructionData)
                          },
                          false => {
                            Ok(
                              ())
                          },
                        } {
                    Ok(t4) => {
                      match match self.address_eqb()(
                                    from_address)(
                                    self.seller(
                                      t3)) {
                              true => {
                                Ok(
                                  ())
                              },
                              false => {
                                Err(
                                  ProgramError::InvalidAccountData)
                              },
                            } {
                        Ok(t5) => {
                          let new_state =
                            self.set_State_next_step(
                              self.closure(move |x| {
                                self.alloc(
                                  NextStep::no_next_step(
                                    PhantomData))
                              }),
                              t3);
                          let expected =
                            self.mul(
                              self.expected_amount(
                                t3),
                              __Z_frompos(
                                __pos_zerobit(
                                  1)));
                          match self.exec_act()(
                                  ActionBody::Transfer(
                                    t2,
                                    t,
                                    expected)) {
                            Ok(t6) => {
                              match self.ser_data_account()(
                                      ())(
                                      new_state)(
                                      t2) {
                                Ok(t7) => {
                                  Ok(
                                    ())
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
                    },
                    Err(e) => {
                      Err(
                        e)
                    },
                  }
                },
                &NextStep::buyer_confirm(_) => {
                  Err(
                    ProgramError::InvalidInstructionData)
                },
                &NextStep::withdrawals(_) => {
                  match match self.address_eqb()(
                                from_address)(
                                self.buyer(
                                  t3)) {
                          true => {
                            Ok(
                              __mk_pair(
                                self.buyer_withdrawable(
                                  t3),
                                self.set_State_buyer_withdrawable(
                                  self.closure(move |x| {
                                    0
                                  }),
                                  t3)))
                          },
                          false => {
                            match self.address_eqb()(
                                    from_address)(
                                    self.seller(
                                      t3)) {
                              true => {
                                Ok(
                                  __mk_pair(
                                    self.seller_withdrawable(
                                      t3),
                                    self.set_State_seller_withdrawable(
                                      self.closure(move |x| {
                                        0
                                      }),
                                      t3)))
                              },
                              false => {
                                Err(
                                  ProgramError::InvalidAccountData)
                              },
                            }
                          },
                        } {
                    Ok(t4) => {
                      __pair_elim!(
                        to_pay, new_state, {
                          match match self.gtb(
                                        to_pay,
                                        0) {
                                  true => {
                                    Ok(
                                      ())
                                  },
                                  false => {
                                    Err(
                                      ProgramError::InvalidInstructionData)
                                  },
                                } {
                            Ok(t5) => {
                              let new_state2 =
                                match self.andb(
                                        self.eqb(
                                          self.buyer_withdrawable(
                                            new_state),
                                          0),
                                        self.eqb(
                                          self.seller_withdrawable(
                                            new_state),
                                          0)) {
                                  true => {
                                    self.set_State_next_step(
                                      self.closure(move |x| {
                                        self.alloc(
                                          NextStep::no_next_step(
                                            PhantomData))
                                      }),
                                      new_state)
                                  },
                                  false => {
                                    new_state
                                  },
                                };
                              match self.exec_act()(
                                      ActionBody::Transfer(
                                        t2,
                                        t,
                                        to_pay)) {
                                Ok(t6) => {
                                  match self.ser_data_account()(
                                          ())(
                                          new_state2)(
                                          t2) {
                                    Ok(t7) => {
                                      Ok(
                                        ())
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
                        },
                        t4)
                    },
                    Err(e) => {
                      Err(
                        e)
                    },
                  }
                },
                &NextStep::no_next_step(_) => {
                  Err(
                    ProgramError::InvalidInstructionData)
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
fn withdraw_money__curried(&'a self) -> &'a dyn Fn(&'a Chain<'a>) -> &'a dyn Fn(SliceAccountInformation<'a>) -> Result<(), ProgramError> {
  self.closure(move |chain| {
    self.closure(move |accounts| {
      self.withdraw_money(
        chain,
        accounts)
    })
  })
}

fn escrow_process(&'a self, chain: &'a Chain<'a>, accounts: SliceAccountInformation<'a>, inst: Option<&'a ContractInstruction<'a>>) -> Result<(), ProgramError> {
  match inst {
    Some(c) => {
      match c {
        &ContractInstruction::init_escrow(_, buyer_address, item_price) => {
          self.init(
            chain,
            accounts,
            buyer_address,
            item_price)
        },
        &ContractInstruction::commit_money(_) => {
          self.buyer_commits(
            accounts)
        },
        &ContractInstruction::confirm_item_received(_) => {
          self.confirm_received(
            accounts)
        },
        &ContractInstruction::withdraw(_) => {
          self.withdraw_money(
            chain,
            accounts)
        },
      }
    },
    None => {
      Err(
        ProgramError::InvalidInstructionData)
    },
  }
}
fn escrow_process__curried(&'a self) -> &'a dyn Fn(&'a Chain<'a>) -> &'a dyn Fn(SliceAccountInformation<'a>) -> &'a dyn Fn(Option<&'a ContractInstruction<'a>>) -> Result<(), ProgramError> {
  self.closure(move |chain| {
    self.closure(move |accounts| {
      self.closure(move |inst| {
        self.escrow_process(
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
    prg.escrow_process(&cchain, accounts, Some(&msg))
}
entrypoint!(process_instruction);
