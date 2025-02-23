From MetaCoq Require Import utils.
From MetaCoq.Template Require Import All.
From MetaCoq.Template Require Import Kernames.
From ConCert.Utils Require Import StringExtra.
From ConCert.Execution Require Import BlockchainSolanav2.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ProgramError.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import Extraction.
From ConCert.Extraction Require Import RustExtract.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import SpecializeAll.
From ConCert.Extraction Require Import PrettyPrinterMonad.
From ConCert.Extraction Require Import Printing.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import Utils.

Module SolanaRemap.

Definition lookup_const (TT : list (kername * string)) (name : kername): option string :=
  match find (fun '(key, _) => eq_kername key name) TT with
  | Some (_, val) => Some val
  | None => None
  end.

Definition remap_arith : list (kername * string) := Eval compute in
  [  remap <%% BinPosDef.Pos.add %%> "fn ##name##(&'a self, a: u64, b: u64) -> u64 { a.checked_add(b).unwrap() }"
   ; remap <%% BinPosDef.Pos.succ %%> "fn ##name##(&'a self, a: u64) -> u64 { a.checked_add(1).unwrap() }"
   ; remap <%% Z.add %%> "fn ##name##(&'a self, a: i64, b: i64) -> i64 { a.checked_add(b).unwrap() }"
   ; remap <%% Z.sub %%> "fn ##name##(&'a self, a: i64, b: i64) -> i64 { a.checked_sub(b).unwrap() }"
   ; remap <%% Z.mul %%> "fn ##name##(&'a self, a: i64, b: i64) -> i64 { a.checked_mul(b).unwrap() }"
   ; remap <%% BinIntDef.Z.even %%> "fn ##name##(&'a self, a: i64) -> bool { a.checked_rem(2).unwrap() == 0 }"
   ; remap <%% BinIntDef.Z.odd %%> "fn ##name##(&'a self, a: i64) -> bool { a.checked_rem(2).unwrap() != 0 }"
   ; remap <%% Z.eqb %%> "fn ##name##(&'a self, a: i64, b: i64) -> bool { a == b }"
   ; remap <%% Z.leb %%> "fn ##name##(&'a self, a: i64, b: i64) -> bool { a <= b }"
   ; remap <%% Z.ltb %%> "fn ##name##(&'a self, a: i64, b: i64) -> bool { a < b }"
   ; remap <%% Z.gtb %%> "fn ##name##(&'a self, a: i64, b: i64) -> bool { a > b }"
   ; remap <%% Nat.add %%> "fn ##name##(&'a self, a: u64, b: u64) -> u64 { a.checked_add(b).unwrap() }"
   ; remap <%% Nat.leb %%> "fn ##name##(&'a self, a: u64, b: u64) -> bool { a <= b }"
   ; remap <%% Nat.ltb %%> "fn ##name##(&'a self, a: u64, b: u64) -> bool { a < b }"].

Definition remap_blockchain_consts : list (kername * string) :=
  [remap <! @Address !> "type ##name##<'a> = solana_program::pubkey::Pubkey;"
  (* Ideally we would have two impls here for performance, but Rust does not support this.
     https://github.com/rust-lang/rust/issues/62223 *)
   ; remap <! @address_eqb !>
          "fn ##name##(&'a self) -> impl Fn(solana_program::pubkey::Pubkey) -> &'a dyn Fn(solana_program::pubkey::Pubkey) -> bool { move |a| self.alloc(move |b| a == b) }" 
   ; remap <! @SliceAccountInformation !> "type ##name##<'a> = &'a[AccountInfo<'a>];"
  ].

Definition remap_aux_consts : list (kername * string) := 
  [ 
  remap <! @next_account !> "fn ##name##<'t>(&'t self) -> impl (Fn(SliceAccountInformation<'a>) -> &'t dyn Fn(i64) -> Result<&'a AccountInfo<'a>, ProgramError>) + 't where 'a: 't, { move |slc: SliceAccountInformation| { self.alloc(move |index| { slc.get(index as usize).ok_or(ProgramError::AccountBorrowFailed) }) }}"

  ; remap <! @deser_data_account !> "fn deser_data_account(&'a self) -> impl Fn(()) -> &'a dyn Fn(&'a AccountInfo) -> Result<State<'a>, ProgramError> { move |_| { self.alloc(move |v| { match State::try_from_slice(&v.data.borrow()) { Ok(val) => Ok(val), Err(_) => Err(ProgramError::BorshIoError(String::from(""Deserialization error"")))}})}}"
  ; remap <! @deser_data !> "fn ##name##<T : BorshDeserialize>(&'a self) -> impl Fn(()) -> &'a dyn Fn(std::rc::Rc<std::cell::RefCell<&'a mut [u8]>>) -> Result<T, ProgramError> { move |_| { self.alloc(move |v| { match T::try_from_slice(*v.borrow()) { Ok(val) => Ok(val), Err(_) => Err(ProgramError::BorshIoError(String::from(""Deserialization error"")))}})}}"
  ; remap <! @ser_data !> "fn ##name##<W : std::io::Write, T : BorshSerialize>(&'a self) -> impl Fn(&'a T) -> &'a dyn Fn(&mut W) -> Result<(), ProgramError> { move |v| self.alloc( move |out| { match v.serialize(out) { Ok(_) => Ok(()), Err(_) => Err(ProgramError::BorshIoError(String::from(""Serialization error"")))}})}"
  ; remap <! @ser_data_account !> "fn ser_data_account<'ai, T : BorshSerialize>(&'a self) -> impl Fn(()) -> &'a dyn Fn(&'a T) -> &'a dyn Fn(&'ai AccountInfo<'ai>) -> Result<(), ProgramError> { move |_| { self.alloc( move |v| self.alloc( move |acc| { match (*v).serialize(&mut &mut (*acc).data.borrow_mut()[..]) { Ok(_) => Ok(()), Err(_) => Err(ProgramError::BorshIoError(String::from(""Serialization error"")))}}))}}"
  ; remap <! @exec_act !> "fn ##name##(&'a self) -> &'a dyn Fn(ActionBody<'a>) -> Result<(), ProgramError> { self.alloc(move |act|self.convert_action(&act)) }"
  ] 
.

Definition remap_account_operations : list (kername * string) :=
  [
    remap <! @get_account_address !> "fn ##name##<'ai>(&'a self) -> &'a dyn Fn(&'ai AccountInfo<'ai>) -> Pubkey { self.alloc(move |acc| *acc.key) }";
    remap <! @get_account_state !> "fn ##name##<'ai>(&'a self) -> &'a dyn Fn(&'ai AccountInfo<'ai>) -> &std::rc::Rc<std::cell::RefCell<&'a mut [u8]>> { self.alloc(move |acc| &acc.data) }";
    remap <! @get_account_balance !> "fn ##name##(&'a self) -> &'a dyn Fn(&'a AccountInfo<'a>) -> i64 { self.alloc(move |acc| **acc.lamports.borrow() as i64) }";
    remap <! @get_account_owner_address !> "fn ##name##<'ai>(&'a self) -> &'a dyn Fn(&'ai AccountInfo<'ai>) -> Pubkey { self.alloc(move |acc| *acc.owner) }";
    remap <! @get_account_is_signer !> "fn ##name##<'ai>(&'a self) -> &'a dyn Fn(&'ai AccountInfo<'ai>) -> bool { self.alloc(move |acc| acc.is_signer) }";
    remap <! @get_account_is_writable !> "fn ##name##<'ai>(&'a self) -> &'a dyn Fn(&'ai AccountInfo<'ai>) -> bool { self.alloc(move |acc| acc.is_writable) }";
    remap <! @get_account_is_executable !> "fn ##name##<'ai>(&'a self) -> &'a dyn Fn(&'ai AccountInfo<'ai>) -> bool { self.alloc(move |acc| acc.is_executable) }"
  ].

Definition remap_inline_bool_ops := Eval compute in
      [ remap <%% andb %%> "__andb!"
      ; remap <%% orb %%> "__orb!"].

Definition remap_nat : remapped_inductive:=
  {| re_ind_name := "u64";
     re_ind_ctors := ["0"; "__nat_succ"];
     re_ind_match := Some "__nat_elim!" |}.

Definition remap_positive : remapped_inductive :=
  {| re_ind_name := "u64";
     re_ind_ctors := ["__pos_onebit"; "__pos_zerobit"; "1"];
     re_ind_match := Some "__pos_elim!"
  |}.

Definition remap_Z : remapped_inductive :=
  {| re_ind_name := "i64";
     re_ind_ctors := ["0"; "__Z_frompos"; "__Z_fromneg"];
     re_ind_match := Some "__Z_elim!";
  |}.

Definition remap_bool : remapped_inductive :=
  {| re_ind_name := "bool";
     re_ind_ctors := ["true"; "false"];
     re_ind_match := None
  |}.

Definition remap_pair : remapped_inductive :=
  {| re_ind_name := "__pair";
     re_ind_ctors := ["__mk_pair"];
     re_ind_match := Some "__pair_elim!"
  |}.

Definition remap_option : remapped_inductive :=
  {| re_ind_name := "Option";
     re_ind_ctors := ["Some"; "None"];
     re_ind_match := None
  |}.

Definition remap_result : remapped_inductive :=
  {| re_ind_name := "Result";
     re_ind_ctors := ["Ok"; "Err"];
     re_ind_match := None
  |}.

Definition remap_unit : remapped_inductive :=
  {| re_ind_name := "()";
     re_ind_ctors := ["()"];
     re_ind_match := None
  |}.

Definition remap_string : remapped_inductive :=
  {| re_ind_name := "&'a String";
     re_ind_ctors := [];
     re_ind_match := None |}.

Definition remap_std_types :=
  [ (<! nat !>, remap_nat)
  ; (<! positive !>, remap_positive)
  ; (<! Z !>,  remap_Z)
  ; (<! bool !>, remap_bool)
  ; (<! prod !>, remap_pair)
  ; (<! option !>, remap_option)
  ; (<! Execution.ResultMonad.result !>, remap_result)
  ; (<! unit !>, remap_unit)
  ; (<! string !>, remap_string) ].

Definition remap_SerializedValue : remapped_inductive :=
  {| re_ind_name := "&'a SerializedValue<'a>";
     re_ind_ctors := ["__SerializedValue__Is__Opaque"];
     re_ind_match := None |}.

Definition remap_WrappedActionBody : remapped_inductive :=
  {| re_ind_name := "ActionBody<'a>";
     re_ind_ctors := ["ActionBody::Transfer"; "ActionBody::Call"; "__Deploy__Is__Not__Supported"; "ActionBody::SpecialCall"];
     re_ind_match := None |}.

Definition remap_SpecialCallBody : remapped_inductive := 
  {| re_ind_name := "SpecialCallBody<'a>";
     re_ind_ctors := ["SpecialCallBody::TransferOwnership"; "SpecialCallBody::CheckRentExempt"; "SpecialCallBody::CheckTokenOwner"];  
     re_ind_match := None |}.

Definition remap_ProgramError : remapped_inductive :=
  {| re_ind_name := "ProgramError";
     re_ind_ctors := ["ProgramError::Custom"; "ProgramError::InvalidArgument"; "ProgramError::InvalidInstructionData";
    "ProgramError::InvalidAccountData"; "ProgramError::AccountDataTooSmall"; "ProgramError::InsufficientFunds";
    "ProgramError::IncorrectProgramId"; "ProgramError::MissingRequiredSignature"; "ProgramError::AccountAlreadyInitialized";
    "ProgramError::UninitializedAccount"; "ProgramError::NotEnoughAccountKeys"; "ProgramError::AccountBorrowFailed";
    "ProgramError::MaxSeedLengthExceeded"; "ProgramError::InvalidSeeds"; "ProgramError::BorshIoError";
    "ProgramError::AccountNotRentExempt"; "ProgramError::UnsupportedSysvar"; "ProgramError::IllegalOwner";
    "ProgramError::MaxAccountsDataSizeExceeded"; "ProgramError::InvalidRealloc" ];
     re_ind_match := None |}.

Definition remap_blockchain_inductives : list (inductive * remapped_inductive) :=
  [ (<! Serializable.SerializedValue !>, remap_SerializedValue);
    (<! @WrappedActionBody !>, remap_WrappedActionBody);
    (<! @SpecialCallBody !>, remap_SpecialCallBody); 
    (<! @ProgramError !>, remap_ProgramError)
  ].


Definition ignored_concert :=
  Eval compute in 
    [
      <%% @Monads.Monad %%>
    ; <%% @AccountInformation %%>
    ; <%% @SerializedValue %%>
    ; <%% @Serializable %%>
    ; <%% @RecordSet.SetterFromGetter %%>
    ].

Definition lookup_inductive
           (TT_inductives : list (inductive * remapped_inductive))
           (ind : inductive) : option remapped_inductive :=
  match find (fun '(key, _) => eq_inductive key ind) TT_inductives with
  | Some (_, val) => Some val
  | None => None
  end.

Definition build_remaps
           (TT_const : list (kername * string))
           (TT_const_inline : list (kername * string))
           (TT_inductives : list (inductive * remapped_inductive))
  : remaps :=
  {| remap_inductive := lookup_inductive TT_inductives;
     remap_constant := lookup_const TT_const;
     remap_inline_constant := lookup_const TT_const_inline; |}.

End SolanaRemap.

Module SolanaPreamble.

Instance solana_extract_preamble : Preamble :=
{| top_preamble := [
"#![allow(dead_code)]";
"#![allow(non_camel_case_types)]";
"#![allow(non_snake_case)]";
"#![allow(unused_variables)]";
"";
"use solana_program::{";
"  account_info::AccountInfo,";
"  clock::Clock,";
"  entrypoint,";
"  entrypoint::ProgramResult,";
"  program_error::ProgramError,";
"  pubkey::Pubkey,";
"  rent::Rent,";
"  sysvar::Sysvar,";
"  program::invoke,";
"};";
"use borsh::{BorshSerialize, BorshDeserialize};";
"use concert_std::{ActionBody, SpecialCallBody};";
"use core::marker::PhantomData;";
""; 
"fn __nat_succ(x: u64) -> u64 {";
"  x.checked_add(1).unwrap()";
"}";
"";
"macro_rules! __nat_elim {";
"    ($zcase:expr, $pred:ident, $scase:expr, $val:expr) => {";
"        { let v = $val;";
"        if v == 0 { $zcase } else { let $pred = v - 1; $scase } }";
"    }";
"}";
"";
"macro_rules! __andb { ($b1:expr, $b2:expr) => { $b1 && $b2 } }";
"macro_rules! __orb { ($b1:expr, $b2:expr) => { $b1 || $b2 } }";
"";
"fn __pos_onebit(x: u64) -> u64 {";
"  x.checked_mul(2).unwrap() + 1";
"}";
"";
"fn __pos_zerobit(x: u64) -> u64 {";
"  x.checked_mul(2).unwrap()";
"}";
"";
"macro_rules! __pos_elim {";
"    ($p:ident, $onebcase:expr, $p2:ident, $zerobcase:expr, $onecase:expr, $val:expr) => {";
"        {";
"            let n = $val;";
"            if n == 1 {";
"                $onecase";
"            } else if (n & 1) == 0 {";
"                let $p2 = n >> 1;";
"                $zerobcase";
"            } else {";
"                let $p = n >> 1;";
"                $onebcase";
"            }";
"        }";
"    }";
"}";
"";
"fn __Z_frompos(z: u64) -> i64 {";
"  use std::convert::TryFrom;";
"";
"  i64::try_from(z).unwrap()";
"}";
"";
"fn __Z_fromneg(z : u64) -> i64 {";
"  use std::convert::TryFrom;";
"";
"  i64::try_from(z).unwrap().checked_neg().unwrap()";
"}";
"";
"macro_rules! __Z_elim {";
"    ($zero_case:expr, $p:ident, $pos_case:expr, $p2:ident, $neg_case:expr, $val:expr) => {";
"        {";
"            let n = $val;";
"            if n == 0 {";
"                $zero_case";
"            } else if n < 0 {";
"                let $p2 = n.unsigned_abs();";
"                $neg_case";
"            } else {";
"                let $p = n as u64;";
"                $pos_case";
"            }";
"        }";
"    }";
"}";
"";
"fn __N_frompos(z: u64) -> u64 {";
"  z";
"}";
"";
"macro_rules! __N_elim {";
"    ($zero_case:expr, $p:ident, $pos_case:expr, $val:expr) => {";
"        { let $p = $val; if $p == 0 { $zero_case } else { $pos_case } }";
"    }";
"}";
"";
"type __pair<A, B> = (A, B);";
"";
"macro_rules! __pair_elim {";
"    ($fst:ident, $snd:ident, $body:expr, $p:expr) => {";
"        { let ($fst, $snd) = $p; $body }";
"    }";
"}";
"";
"fn __mk_pair<A: Copy, B: Copy>(a: A, b: B) -> __pair<A, B> { (a, b) }";
"";
"fn hint_app<TArg, TRet>(f: &dyn Fn(TArg) -> TRet) -> &dyn Fn(TArg) -> TRet {";
"  f";
"}";
"";
"";
"";
"#[derive(Debug, PartialEq, Eq)]";
"enum ProcessError {";
"    DeserialMsg,";
"    DeserialOldState,";
"    SerialNewState,";
"    ConvertActions, // Cannot convert ConCert actions to Concordium actions";
"    Error";
"}";
"";
"impl From<ProcessError> for ProgramError {";
"    fn from(e: ProcessError) -> Self {";
"        ProgramError::Custom(e as u32)";
"    }";
"}";
""
];
program_preamble := [
"fn alloc<T>(&self, t: T) -> & T {";
"  self.__alloc.alloc(t)";
"}";
"";
"fn closure<TArg, TRet>(&'a self, F: impl Fn(TArg) -> TRet + 'a) -> &'a dyn Fn(TArg) -> TRet {";
"  self.__alloc.alloc(F)";
"}";
"";
"";
"fn convert_special_action(&'a self, to_account: &AccountInfo<'a>, body: &SpecialCallBody<'a>) -> Result<(), ProgramError> {";
"  let cbody =";
"    if let SpecialCallBody::TransferOwnership(old_owner, owned_account, new_owner) = body {";
"        let (pda, _nonce) = Pubkey::find_program_address(&[b""contract""], &self.__program_id);";
"";
"        let owner_change_ix = spl_token::instruction::set_authority(";
"            to_account.key,"; (* Token Program Id *)
"            owned_account.key,"; (* Account which ownership will be changed *)
"            Some(&pda),";
"            spl_token::instruction::AuthorityType::AccountOwner,";
"            old_owner.key,"; (* Account current owner *)
"            &[&old_owner.key],";
"        )?;";
"";
"        invoke(";
"            &owner_change_ix,";
"            &[";
"                *owned_account.clone(),";
"                *old_owner.clone(),";
"                to_account.clone(),";
"            ],";
"        )?;";
"    } else if let SpecialCallBody:: CheckRentExempt(account_checked) = body {";
"        let rent = &Rent::from_account_info(to_account)?;";
"            if !rent.is_exempt(account_checked.lamports(), account_checked.data_len()) {";
"                return Err(ProcessError::Error.into())";
"            }";
"    } else {";
"        return Err(ProcessError::ConvertActions.into())";
"    };";
"  Ok(())";
"}";
"";
"fn convert_action(&'a self, act: &ActionBody<'a>) -> Result<(), ProgramError> {";
"  let cact =";
"      if let ActionBody::Transfer(donator_account, receiver_account, amount) = act {";
"          if **donator_account.try_borrow_mut_lamports()? >= *amount as u64 {";
"              **receiver_account.try_borrow_mut_lamports()? += *amount as u64;";
"              **donator_account.try_borrow_mut_lamports()? -= *amount as u64;";
"          } else {";
"              return Err(ProcessError::Error.into())";
"          };"; 
"      } else if let ActionBody::SpecialCall(to, body) = act {";
"          return self.convert_special_action(to, body)";
"      } else {";
"          return Err(ProcessError::ConvertActions.into())";
"      };";
"      Ok(())";
"}" ] |}.

End SolanaPreamble.

Import SolanaRemap.

Record SolanaMod (process_type : Type) :=
  { solana_contract_name : string;
    solana_process : process_type;
    solana_extra : list ({T : Type & T}); }.

Arguments solana_contract_name {_}.
Arguments solana_process {_}.
Arguments solana_extra {_}.

Definition get_fn_arg_type (Σ : Ex.global_env) (fn_name : kername) (n : nat)
  : result Ex.box_type string :=
  match Ex.lookup_env Σ fn_name with
  | Some (Ex.ConstantDecl cb) =>
    match decompose_TArr cb.(Ex.cst_type).2 with
    | (tys, _) => result_of_option (nth_error tys n)
                                  ("No argument at position " ++ string_of_nat n)
    end
  | _ => Err "Init declaration must be a constant in the global environment"
  end.

Definition specialize_extract_template_env
           (params : extract_template_env_params)
           (Σ : global_env)
           (seeds : KernameSet.t)
           (ignore : kername -> bool) : result ExAst.global_env string :=
  extract_template_env_general SpecializeAll.specialize_consec_env
       params
       Σ
       seeds
       ignore.

Section SolanaPrinting.

  Context `{RustPrintConfig}.

  Definition extract_lines
             (seeds : KernameSet.t)
             (Σ : global_env)
             (remaps : remaps)
             (params : extract_template_env_params) : result (list string) string :=
    let should_ignore kn :=
        if contains kn ignored_concert then true else
        if remap_inductive remaps (mkInd kn 0) then true else
        if remap_constant remaps kn then true else
        if remap_inline_constant remaps kn then true else false in
    Σ <- specialize_extract_template_env params Σ seeds should_ignore;;
    let attrs _ := "#[derive(Clone, BorshSerialize, BorshDeserialize, PartialEq)]" in
    let p := print_program Σ remaps attrs in
    '(_, s) <- timed "Printing" (fun _ => finish_print_lines p);;
    ret s.

  Open Scope string.

  Definition custom_errors_wrapper (contract_name : string) :=
    <$
      "impl From<" ++ contract_name ++ "Error<'_>> for ProgramError {";
      "    fn from(e: " ++ contract_name ++ "Error) -> Self {";
      "        ProgramError::Custom(e as u32)";
      "    }";
      "}" $>.

  Definition process_instruction_wrapper (process_name : kername) := 
    <$
      "fn process_instruction<'ai>(";
      "    program_id: &Pubkey,";
      "    accounts: SliceAccountInformation<'ai>,";
      "    instruction_data: &[u8],";
      ") -> ProgramResult {";
      "    let prg = Program::new(*program_id);";
      "    let msg : ContractInstruction = ";
      "        match ContractInstruction::try_from_slice(instruction_data) {";
      "            Ok(m) => m,";
      "            Err(_) => return Err(ProcessError::DeserialMsg.into())";
      "        };";
      "    let cchain ="; 
      "        " ++ RustExtract.ty_const_global_ident_of_kername <%% Chain %%> ++ "::build_chain(";
      "            PhantomData,";
      "            0, // No chain height";
      "            Clock::get().unwrap().unix_timestamp as u64,";
      "            0 // No finalized height";
      "        );";
      "    prg." ++ RustExtract.const_global_ident_of_kername process_name ++ "(&cchain, accounts, Some(&msg))";
      "}" ;
      "entrypoint!(process_instruction);" $>.

Definition list_name : string :=
    RustExtract.ty_const_global_ident_of_kername <%% list %%>.

Definition print_lines (lines : list string) : TemplateMonad unit :=
    monad_iter tmMsg lines.

Definition solana_extraction
           {process_type : Type}
           (m : SolanaMod process_type)
           (remaps : remaps)
           (should_inline : kername -> bool) : TemplateMonad _ :=
  process_tm <- tmEval cbn m.(solana_process);;
  '(Σ,_) <- tmQuoteRecTransp (process_tm) false ;;
  process_nm <- extract_def_name m.(solana_process);;
  extra <- monad_map extract_def_name_exists m.(solana_extra);;
  let overridden_masks kn :=
      if eq_kername kn process_nm then
        Some []
      else
        None in
  let seeds := KernameSetProp.of_list (process_nm :: extra) in
  let params := extract_rust_within_coq overridden_masks should_inline in
  Σ <- run_transforms Σ params;;
  res <- tmEval lazy (extract_lines seeds Σ remaps params);;
  match res with
  | Ok lines =>
    let process_wrapper := process_instruction_wrapper process_nm in
    let custom_errors := custom_errors_wrapper m.(solana_contract_name) in
    print_lines (lines ++ [(* ""; custom_errors; ""; (convert_special_action m.(solana_contract_name)); ""; convert_actions; ""; *) process_wrapper])
  | Err e => tmFail e
  end. 

End SolanaPrinting.

Module DefaultPrintConfig.

  Definition RustConfig : RustPrintConfig :=
    {| term_box_symbol := "()";
       type_box_symbol := "()";
       any_type_symbol := "()";
       print_full_names := true |}.

End DefaultPrintConfig.
