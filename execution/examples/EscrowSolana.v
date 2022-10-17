From Coq Require Import List.
From Coq Require Import Bool.
From Coq Require Import ZArith.
From Coq Require Import Permutation.
From Coq Require Import Psatz.
From ConCert.Execution Require Import ProgramError.
From ConCert.Execution Require Import BlockchainSolanav2.
From ConCert.Execution Require Import CommonSolana.
From ConCert.Execution Require Import Extras.
From ConCert.Execution Require Import Monads.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import RecordUpdate.

Import ListNotations.
Import RecordSetNotations.


Section EscrowSolana.
Context {Base : ChainBase}.
Context {AccountGetters : AccountGetters}.
Context {HelperTypes : ChainHelpers}.

Set Nonrecursive Elimination Schemes.

Inductive NextStep :=
(* Waiting for buyer to commit itemvalue * 2 *)
| buyer_commit
(* Waiting for buyer to confirm item received *)
| buyer_confirm
(* Waiting for buyer and seller to withdraw their funds. *)
| withdrawals
(* No next step, sale is done. *)
| no_next_step.

Record State :=
  build_state {
      last_action : nat;
      next_step : NextStep;
(*       is_initialized : bool; *)
      seller : Address;
      buyer : Address;
      seller_withdrawable : Amount;
      buyer_withdrawable : Amount;
      expected_amount : Amount;
    }.

MetaCoq Run (make_setters State).

Inductive ContractInstruction :=
| init_escrow (buyer : Address) (item_price : Amount)
| commit_money
| confirm_item_received
| withdraw.

Global Instance NextStep_serializable : Serializable NextStep :=
  Derive Serializable NextStep_rect<buyer_commit, buyer_confirm, withdrawals, no_next_step>.

Global Instance State_serializable : Serializable State :=
  Derive Serializable State_rect<build_state>.

Global Instance ContractInstruction_serializable : Serializable ContractInstruction :=
  Derive Serializable ContractInstruction_rect<init_escrow, commit_money, confirm_item_received, withdraw>.

Open Scope Z.

Definition init (chain : Chain) (accounts : SliceAccountInformation) (buyer : Address) (item_price : Amount) : result unit ProgramError :=
  let index := 0 in 
  do seller_account <- next_account accounts index;
  let index := 1 in
  do escrow_account <- next_account accounts index;
  
  do if get_account_is_signer seller_account then Ok tt else Err MissingRequiredSignature;
  
  (* Check rent escrow *)
  do (exec_act (wact_special_call escrow_account (check_rent_exempt escrow_account)));

  let init_state := 
    (build_state 
      (current_slot chain) 
      buyer_commit 
      (get_account_address seller_account) 
      buyer 
      0 0 item_price
    ) in 
  
  do ser_data_account init_state escrow_account;

  let expected := item_price * 2 in
  do if (get_account_balance seller_account >? expected) then Ok tt else Err InsufficientFunds;

  (* Seller Transfer Money *)
  do (exec_act (wact_transfer seller_account escrow_account expected));

  Ok tt.

Definition buyer_commits (chain : Chain) (accounts : SliceAccountInformation) : result unit ProgramError :=
  let index := 0 in 
  do buyer_account <- next_account accounts index;
  let index := 1 in
  do escrow_account <- next_account accounts index;

  do state <- deser_data_account State escrow_account;

  do if (buyer state =? get_account_address buyer_account)%address then Ok tt else Err InvalidAccountData;

  do match next_step state with
    | buyer_commit => Ok tt
    | _ => Err InvalidInstructionData
  end;

  let expected := (expected_amount state) * 2 in
  do if (get_account_balance buyer_account >? expected) then Ok tt else Err InsufficientFunds;

  let new_state := state<|next_step := buyer_confirm|> in

  do ser_data_account new_state escrow_account;

  (* Seller Transfer Money *)
  do (exec_act (wact_transfer buyer_account escrow_account expected));

  Ok tt.

Definition confirm_received (chain : Chain) (accounts : SliceAccountInformation) : result unit ProgramError :=
  let index := 0 in 
  do buyer_account <- next_account accounts index;
  let index := 1 in
  do escrow_account <- next_account accounts index;

  do state <- deser_data_account State escrow_account;

  do if (buyer state =? get_account_address buyer_account)%address then Ok tt else Err InvalidAccountData;

  do match next_step state with
    | buyer_confirm => Ok tt
    | _ => Err InvalidInstructionData
  end;

  let new_state := state<|next_step := withdrawals|>
                        <|buyer_withdrawable := expected_amount state|>
                        <|seller_withdrawable := (expected_amount state) * 3|> in

  do ser_data_account new_state escrow_account;

  Ok tt.


Definition withdraw_money (chain : Chain) (accounts : SliceAccountInformation) : result unit ProgramError := 
  let index := 0 in 
  do withdrawer_account <- next_account accounts index;
  let index := 1 in
  do escrow_account <- next_account accounts index;
  
  do state <- deser_data_account State escrow_account;
  let from_address := get_account_address withdrawer_account in

  match next_step state with
    | withdrawals => 

       do '(to_pay, new_state) <-
       match from_address =? buyer state, from_address =? seller state with
       | true, _ => Ok (buyer_withdrawable state, state<|buyer_withdrawable := 0|>)
       | _, true => Ok (seller_withdrawable state, state<|seller_withdrawable := 0|>)
       | _, _ => Err InvalidAccountData
       end%address; 

       do if to_pay >? 0 then Ok tt else Err InvalidInstructionData;

       let new_state :=
           if (buyer_withdrawable new_state =? 0) && (seller_withdrawable new_state =? 0)
           then new_state<|next_step := no_next_step|>
           else new_state in 

       do (exec_act (wact_transfer escrow_account withdrawer_account to_pay));

       do ser_data_account new_state escrow_account; 
       Ok tt

    | buyer_commit => 

       do if (last_action state + 50 <? current_slot chain)%nat then Err InvalidInstructionData else Ok tt;
       do if (from_address =? seller state)%address then Ok tt else Err InvalidAccountData;
    
       let new_state := state<|next_step := no_next_step|> in
       let expected := (expected_amount state) * 2 in
       do (exec_act (wact_transfer escrow_account withdrawer_account expected));
       do ser_data_account new_state escrow_account;

       Ok tt
    | _ => Err InvalidInstructionData
  end.


Definition escrow_process (chain : Chain) (accounts : SliceAccountInformation) (inst : option ContractInstruction) : result unit ProgramError :=
  match inst with
    | Some (init_escrow buyer_address item_price) => init chain accounts buyer_address item_price
    | Some commit_money => buyer_commits chain accounts 
    | Some confirm_item_received => confirm_received chain accounts
    | Some withdraw => withdraw_money chain accounts
    | _ => Err InvalidInstructionData
  end.

Definition contract : Contract ContractInstruction State :=
  build_contract escrow_process.

End EscrowSolana.
