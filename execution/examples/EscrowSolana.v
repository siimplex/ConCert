(* This file defines a simple escrow contract based on the "safe remote
purchase" example in Solidity's docs. This contract allows a seller to sell an
item in a trustless setting assuming economically rational actors. With the
premise that the seller wants to sell an item for 1 ETH, the contract works in
the following way:

1. The seller deploys the contract and commits 2 ETH.
2. The buyer commits 2 ETH before the deadline.
3. The seller hands over the item (outside of the smart contract).
4. The buyer confirms he has received the item. He gets 1 ETH back
while the seller gets 3 ETH back.

If the buyer does not commit the funds, the seller gets his money back after the
deadline. The economic rationality shows up in our assumption that the seller
will confirm he has received the item to get his own funds back. *)

From Coq Require Import List.
From Coq Require Import Bool.
From Coq Require Import ZArith.
From Coq Require Import Permutation.
From Coq Require Import Psatz.
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
Import AccountInformationEqb.

Section EscrowSolana.
Context `{Base : ChainBase}.

Parameter NullAccount : AccountInformation.

Set Nonrecursive Elimination Schemes.

Record Setup :=
  build_setup {
      setup_buyer : Address;
    }.

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
      seller : Address;
      buyer : Address;
      seller_withdrawable : Amount;
      buyer_withdrawable : Amount;
      is_initialized : bool;
    }.

Inductive MsgType :=
| init_escrow
| commit_money
| confirm_item_received
| withdraw.

Record Msg :=
  build_message {
    instruction : option MsgType;
    setup : option SerializedValue;
    amount : option SerializedValue;
  }.

Inductive EscrowError :=
| InvalidInstruction
| InvalidAmount
| InvalidAccounts. 

Definition return_test (chain : Chain) (accounts : list AccountInformation) (setup : Setup) :
  result unit ProgramError :=
  if true then Err AccountAlreadyInitialized else Err (Custom InvalidInstruction).

MetaCoq Run (make_setters State).
MetaCoq Run (make_setters Msg).

Global Instance Setup_serializable : Serializable Setup :=
  Derive Serializable Setup_rect<build_setup>.

Global Instance NextStep_serializable : Serializable NextStep :=
  Derive Serializable NextStep_rect<buyer_commit, buyer_confirm, withdrawals, no_next_step>.

Global Instance State_serializable : Serializable State :=
  Derive Serializable State_rect<build_state>.

Global Instance MsgType_serializable : Serializable MsgType :=
  Derive Serializable MsgType_rect<init_escrow, commit_money, confirm_item_received, withdraw>.

Global Instance Msg_serializable : Serializable Msg :=
  Derive Serializable Msg_rect<build_message>.

Open Scope Z.

Definition next_account (n : nat) (accounts : list AccountInformation) (default : AccountInformation) : AccountInformation :=
  let seller_account := (nth n accounts default) in
  seller_account.

Definition check_account (account null_account : AccountInformation) : result bool ProgramError :=
  if (account =? null_account)%accountinfo then Err (Custom InvalidAccounts) else Ok true.

Definition escrow_init (chain : Chain) (accounts : list AccountInformation) (setup : Setup)
  : result unit ProgramError :=
  let buyer_address := setup_buyer setup in

  let seller_account := (next_account 0 accounts NullAccount) in
  do check_account seller_account NullAccount;
  let temp_token_account := (next_account 1 accounts NullAccount) in
  do check_account temp_token_account NullAccount;
  let token_to_receive_account := (next_account 2 accounts NullAccount) in
  do check_account token_to_receive_account NullAccount; 
  let escrow_account := (next_account 3 accounts NullAccount) in
  do check_account escrow_account NullAccount;
  let rent_sysvar_account := (next_account 4 accounts NullAccount) in
  do check_account rent_sysvar_account NullAccount;
  let token_program_account := (next_account 5 accounts NullAccount) in
  do check_account token_program_account NullAccount;

  do if (account_is_signer seller_account) then Ok true else Err (Custom InvalidAccounts);
  do if ((account_owner_address seller_account) =? (account_address token_program_account))%address then Ok true else Err IncorrectProgramId;

  let act1 := act_special_call (account_address rent_sysvar_account) (check_rent_exempt (account_address escrow_account)) in
  do match simulate_action act1 with
      | Ok _ => Ok true
      | Err _ => Err (Custom InvalidInstruction)
  end;

  let escrow_account_deserialize_state := ((@deserialize State _) (account_state escrow_account)) in  
  do match escrow_account_deserialize_state with 
      | Some st => if (is_initialized st) then Err AccountAlreadyInitialized else Ok true
      | None => Ok true
  end;

  let act2 := act_special_call (account_address token_program_account)
          (transfer_ownership (account_address seller_account) (account_address token_to_receive_account) (account_address token_program_account)) in
  do match simulate_action act2 with
      | Ok _ => Ok true
      | Err _ => Err (Custom InvalidInstruction)
  end;

  let initialized_state := (build_state
      (current_slot chain)
      buyer_commit
      (account_address seller_account)
      buyer_address
      0 0 true)
  in
              
  let escrow_account := escrow_account<|account_state := ((@serialize State _) initialized_state)|> in 

  let seller_account_balance := (account_balance temp_token_account) in
  do if (buyer_address =? (account_address seller_account))%address then Err (Custom InvalidAccounts) else Ok true;
  do if seller_account_balance =? 0 then Err (Custom InvalidAmount) else Ok true;
  do if Z.even seller_account_balance then Ok true else Err (Custom InvalidAmount);

  Ok tt.



Definition escrow_commit_money (chain : Chain) (accounts : list AccountInformation) (amount : Amount) : result (list ActionBody) EscrowError :=
  let buyer_account_opt := (nth_error accounts 0) in
  let temp_token_account_opt := (nth_error accounts 1) in
  let token_to_receive_account_opt := (nth_error accounts 2) in
  let escrow_account_opt := (nth_error accounts 3) in
  let rent_sysvar_account_opt := (nth_error accounts 4) in
  let token_program_account_opt := (nth_error accounts 5) in

  match buyer_account_opt with
  | Some buyer_account =>
        match temp_token_account_opt with
        | Some temp_token_account =>
              match token_to_receive_account_opt with
              | Some token_to_receive_account =>
                  match escrow_account_opt with
                  | Some escrow_account =>
                      match rent_sysvar_account_opt with
                      | Some rent_sysvar_account =>
                          match token_program_account_opt with
                          | Some token_program_account =>
                              let escrow_account_deserialize_state := ((@deserialize State _) (account_state escrow_account)) in
                              match escrow_account_deserialize_state with 
                                | Some st => 
                                    do if (is_initialized st) then Ok tt else Err ProgramError;
                                    do if (buyer st =? account_address buyer_account)%address then Ok tt else Err InvalidAccounts;

                                    let expected := amount * 2 in
                                    do if (account_balance buyer_account >=? expected) then Ok tt else Err InvalidAmount;

                                    let state := st<|next_step := buyer_confirm|>
                                                   <|last_action := current_slot chain|> in
                                    
                                    (* escrow_account<|account_state := (@serialize State _) initialized_state|>; *)

                                    Ok ([])
                                  | None => Err InvalidAccounts
                                end
                          | None => Err InvalidAccounts
                          end
                      | None => Err InvalidAccounts
                    end
                  | None => Err InvalidAccounts
                  end
              | None => Err InvalidAccounts
              end
        | None => Err InvalidAccounts
        end
  | None => Err InvalidAccounts
  end.

Definition escrow_confirm_item_received (chain : Chain) (accounts : list AccountInformation) (amount : Amount) : result (list ActionBody) EscrowError :=
  let buyer_account_opt := (nth_error accounts 0) in
  let temp_token_account_opt := (nth_error accounts 1) in
  let token_to_receive_account_opt := (nth_error accounts 2) in
  let escrow_account_opt := (nth_error accounts 3) in
  let rent_sysvar_account_opt := (nth_error accounts 4) in
  let token_program_account_opt := (nth_error accounts 5) in

  match buyer_account_opt with
  | Some buyer_account =>
        match temp_token_account_opt with
        | Some temp_token_account =>
              match token_to_receive_account_opt with
              | Some token_to_receive_account =>
                  match escrow_account_opt with
                  | Some escrow_account =>
                      match rent_sysvar_account_opt with
                      | Some rent_sysvar_account =>
                          match token_program_account_opt with
                          | Some token_program_account =>
                              let escrow_account_deserialize_state := ((@deserialize State _) (account_state escrow_account)) in
                              match escrow_account_deserialize_state with 
                                | Some st => 
                                    do if (is_initialized st) then Ok tt else Err ProgramError;
                                    do if (buyer st =? account_address buyer_account)%address then Ok tt else Err InvalidAccounts;

                                    let state := st<|next_step := withdrawals|>
                                                   <|buyer_withdrawable := amount|>
                                                   <|seller_withdrawable := amount * 3|> in
                                    
                                    (* escrow_account<|account_state := (@serialize State _) initialized_state|>; *)

                                    Ok ([])
                                  | None => Err InvalidAccounts
                                end
                          | None => Err InvalidAccounts
                          end
                      | None => Err InvalidAccounts
                    end
                  | None => Err InvalidAccounts
                  end
              | None => Err InvalidAccounts
              end
        | None => Err InvalidAccounts
        end
  | None => Err InvalidAccounts
  end.

Definition escrow_withdraw (chain : Chain) (accounts : list AccountInformation) (amount : Amount) : result (list ActionBody) EscrowError :=
  let participant_account_opt := (nth_error accounts 0) in
  let temp_token_account_opt := (nth_error accounts 1) in
  let token_to_receive_account_opt := (nth_error accounts 2) in
  let escrow_account_opt := (nth_error accounts 3) in
  let rent_sysvar_account_opt := (nth_error accounts 4) in
  let token_program_account_opt := (nth_error accounts 5) in

  match participant_account_opt with
  | Some participant_account =>
        match temp_token_account_opt with
        | Some temp_token_account =>
              match token_to_receive_account_opt with
              | Some token_to_receive_account =>
                  match escrow_account_opt with
                  | Some escrow_account =>
                      match rent_sysvar_account_opt with
                      | Some rent_sysvar_account =>
                          match token_program_account_opt with
                          | Some token_program_account =>
                              let escrow_account_deserialize_state := ((@deserialize State _) (account_state escrow_account)) in
                              match escrow_account_deserialize_state with 
                                | Some st => 
                                    do if (is_initialized st) then Ok tt else Err ProgramError;

                                    match next_step st with 
                                    | buyer_commit =>
                                      do if (last_action st + 50 <? current_slot chain)%nat then Err ProgramError else Ok tt;
                                      do if ((account_address participant_account) =? seller st)%address then Ok tt else Err InvalidAccounts;
                                      let balance := account_balance escrow_account in
                                      (* state<|next_step := no_next_step|> *)
                                      Ok ([act_transfer (seller st) balance])
                                    | _ =>

                                      do '(to_pay, new_state) <-
                                         match (account_address participant_account) =? (buyer st), 
                                               (account_address participant_account) =? (seller st) with
                                         | true, _ => Ok (buyer_withdrawable st, st<|buyer_withdrawable := 0|>)
                                         | _, true => Ok (seller_withdrawable st, st<|seller_withdrawable := 0|>)
                                         | _, _ => Err ProgramError
                                         end%address;
                                      
                                    
                                      do if to_pay >? 0 then Ok tt else Err ProgramError;
                                      let new_state :=
                                          if (buyer_withdrawable new_state =? 0) && (seller_withdrawable new_state =? 0)
                                          then new_state<|next_step := no_next_step|>
                                          else new_state in

                                      (* escrow_account<|account_state := (@serialize State _) new_state|>; *)

                                      Ok ([act_transfer (account_address participant_account) 0])
                                    end
                                  | None => Err InvalidAccounts
                                end
                          | None => Err InvalidAccounts
                          end
                      | None => Err InvalidAccounts
                    end
                  | None => Err InvalidAccounts
                  end
              | None => Err InvalidAccounts
              end
        | None => Err InvalidAccounts
        end
  | None => Err InvalidAccounts
  end.

Definition process (chain : Chain) (accounts : list AccountInformation) (msg : option Msg) : result (list ActionBody) EscrowError :=
    (* TODO: Setup should come inside of the MSG *)
    match msg with
    | Some message =>
        match instruction message with
        | Some init_escrow =>
            match setup message with
            | Some ser_setup => 
                match ((@deserialize Setup _) ser_setup) with 
                | Some setup =>
                    escrow_init chain accounts setup
                | None => Err ProgramError
                end
            | None => Err ProgramError
            end 
        | Some commit_money => 
            match amount message with
            | Some ser_amount => 
              match ((@deserialize Amount _) ser_amount) with 
              | Some amount =>
                  escrow_commit_money chain accounts amount
              | None => Err ProgramError
              end
            | None => Err ProgramError
            end 
        | Some confirm_item_received =>
            match amount message with
            | Some ser_amount => 
              match ((@deserialize Amount _) ser_amount) with 
              | Some amount =>
                escrow_confirm_item_received chain accounts amount
              | None => Err ProgramError
              end
            | None => Err ProgramError
            end 
        | Some withdraw =>
            match amount message with
           | Some ser_amount => 
             match ((@deserialize Amount _) ser_amount) with 
              | Some amount =>
                  escrow_withdraw chain accounts amount
            | None => Err ProgramError
            end
            | None => Err ProgramError
            end
        | None => Err ProgramError
        end
    | None => Err InvalidInstruction
    end.

Definition contract : Contract Msg State :=
  build_contract process.

Section Theories.
  Lemma no_self_calls bstate caddr :
    reachable bstate ->
    env_contracts bstate caddr = Some (Escrow.contract : WeakContract) ->
    Forall (fun abody => match abody with
                         | act_transfer to _ => (to =? caddr)%address = false
                         | _ => False
                         end) (outgoing_acts bstate caddr).
  Proof.
    contract_induction; intros; cbn in *; auto.
    - now inversion IH.
    - apply Forall_app; split; try tauto.
      clear IH.
      unfold receive in receive_some.
      destruct_match as [[]|] in receive_some; try congruence.
      + destruct_match in receive_some; try congruence.
        destruct_match in receive_some; cbn in *; try congruence.
        destruct_match in receive_some; cbn in *; try congruence.
        inversion_clear receive_some; auto.
      + destruct_match in receive_some; try congruence.
        destruct_match in receive_some; cbn in *; try congruence.
        destruct_match in receive_some; cbn in *; try congruence.
        inversion_clear receive_some; auto.
      + destruct_match in receive_some; try congruence.
        * destruct_match in receive_some; cbn in *; try congruence.
          destruct_match in receive_some; cbn in *; try congruence.
          destruct (address_eqb_spec (ctx_from ctx) (seller prev_state)) as
              [<-|]; cbn in *; try congruence.
          inversion_clear receive_some.
          constructor; try constructor.
          apply address_eq_ne; auto.
        * destruct_match in receive_some; cbn in *; try congruence.
          destruct_match in receive_some; cbn in *; try congruence.
          destruct_match in receive_some.
          destruct_match in receive_some; cbn in *; try congruence.
          inversion_clear receive_some.
          constructor; try constructor.
          apply address_eq_ne; auto.
    - inversion_clear IH as [|? ? head_not_me tail_not_me].
      apply Forall_app; split; auto; clear tail_not_me.
      destruct head; try contradiction.
      destruct action_facts as [? [? ?]].
      destruct_address_eq; congruence.
    - now rewrite <- perm.
    - instantiate (DeployFacts := fun _ _ => True).
      instantiate (CallFacts := fun _ _ _ _ => True).
      instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
      unset_all; subst; cbn in *.
      destruct_chain_step; auto.
      destruct_action_eval; auto.
  Qed.

  Definition txs_to (to : Address) (txs : list Tx) : list Tx :=
    filter (fun tx => (tx_to tx =? to)%address) txs.

  Arguments txs_to : simpl never.

  Lemma txs_to_cons addr tx txs :
    txs_to addr (tx :: txs) =
    if (tx_to tx =? addr)%address then
      tx :: txs_to addr txs
    else
      txs_to addr txs.
  Proof. reflexivity. Qed.

  Definition txs_from (from : Address) (txs : list Tx) : list Tx :=
    filter (fun tx => (tx_from tx =? from)%address) txs.

  Arguments txs_from : simpl never.

  Lemma txs_from_cons addr tx txs :
    txs_from addr (tx :: txs) =
    if (tx_from tx =? addr)%address then
      tx :: txs_from addr txs
    else
      txs_from addr txs.
  Proof. reflexivity. Qed.

  Local Open Scope bool.
  Definition buyer_confirmed (inc_calls : list (ContractCallInfo Msg)) buyer :=
    existsb (fun call => (call_from call =? buyer)%address &&
                         match call_msg call with
                         | Some confirm_item_received => true
                         | _ => false
                         end) inc_calls.

  Definition transfer_acts_to addr acts :=
    filter (fun a => match a with
                     | act_transfer to _ => (to =? addr)%address
                     | _ => false
                     end) acts.

  Arguments transfer_acts_to : simpl never.

  Lemma transfer_acts_to_cons addr act acts :
    transfer_acts_to addr (act :: acts) =
    if match act with
       | act_transfer to _ => (to =? addr)%address
       | _ => false
       end
    then
      act :: transfer_acts_to addr acts
    else
      transfer_acts_to addr acts.
  Proof. reflexivity. Qed.

  Definition money_to
             {bstate_from bstate_to}
             (trace : ChainTrace bstate_from bstate_to)
             caddr addr :=
    sumZ tx_amount (txs_to addr (outgoing_txs trace caddr)) +
    sumZ act_body_amount (transfer_acts_to addr (outgoing_acts bstate_to caddr)).

  Lemma escrow_correct_strong bstate caddr (trace : ChainTrace empty_state bstate) :
    env_contracts bstate caddr = Some (Escrow.contract : WeakContract) ->
    exists (cstate : State)
           (depinfo : DeploymentInfo Setup)
           (inc_calls : list (ContractCallInfo Msg)),
      deployment_info Setup trace caddr = Some depinfo /\
      contract_state bstate caddr = Some cstate /\
      incoming_calls Msg trace caddr = Some inc_calls /\
      let item_worth := deployment_amount depinfo / 2 in
      let seller_addr := deployment_from depinfo in
      let buyer_addr := setup_buyer (deployment_setup depinfo) in
      deployment_amount depinfo = 2 * item_worth /\
      item_worth > 0 /\
      seller cstate = seller_addr /\
      buyer cstate = buyer_addr /\
      buyer_addr <> seller_addr /\
      forallb (fun act => match act with
                         | act_transfer _ _ => true
                         | _ => false
                         end) (outgoing_acts bstate caddr) = true /\
      match next_step cstate with
      | buyer_commit =>
        env_account_balances bstate caddr = 2 * item_worth /\
        outgoing_acts bstate caddr = [] /\
        outgoing_txs trace caddr = [] /\
        inc_calls = []

      | buyer_confirm =>
        env_account_balances bstate caddr = 4 * item_worth /\
        outgoing_acts bstate caddr = [] /\
        outgoing_txs trace caddr = [] /\
        exists origin, inc_calls = [build_call_info origin buyer_addr (2 * item_worth) (Some commit_money)]

      | withdrawals =>
        buyer_confirmed inc_calls buyer_addr = true /\
        (exists origin, filter (fun c => negb (call_amount c =? 0)%Z ) inc_calls =
        [build_call_info origin buyer_addr (2 * item_worth) (Some commit_money)]) /\
        money_to trace caddr seller_addr + seller_withdrawable cstate = 3 * item_worth /\
        money_to trace caddr buyer_addr + buyer_withdrawable cstate = 1 * item_worth

      | no_next_step =>
        buyer_confirmed inc_calls buyer_addr = true /\
        (exists origin, filter (fun c => negb (call_amount c =? 0)%Z) inc_calls =
        [build_call_info origin buyer_addr (2 * item_worth) (Some commit_money)]) /\
        money_to trace caddr seller_addr = 3 * item_worth /\
        money_to trace caddr buyer_addr = 1 * item_worth \/

        (exists origin, inc_calls = [build_call_info origin seller_addr 0 (Some withdraw)]) /\
        money_to trace caddr seller_addr = 2 * item_worth /\
        money_to trace caddr buyer_addr = 0
      end.
  Proof.
    unfold money_to.
    contract_induction; cbn in *; intros.
    - (* New block *)
      auto.
    - (* Deployment *)
      unfold Escrow.init in *.
      destruct (address_eqb_spec (setup_buyer setup) (ctx_from ctx));
        cbn in *; try congruence.
      destruct (ctx_amount ctx =? 0) eqn:amount_some; cbn in *; try congruence.
      destruct (Z.even (ctx_amount ctx)) eqn:amount_even; cbn in *; try congruence.
      inversion init_some; subst; clear init_some.
      cbn.
      assert (2 * (ctx_amount ctx / 2) > 0 -> ctx_amount ctx / 2 > 0) by lia.
      enough (2 * (ctx_amount ctx / 2) > 0 /\
              ctx_amount ctx = 2 * (ctx_amount ctx / 2)) by tauto.
      assert (ctx_amount ctx mod 2 = 0).
      {
        rewrite Zeven_mod in amount_even.
        unfold Zeq_bool in *.
        destruct_match eqn:amount_mod_2 in amount_even; try congruence; auto.
        destruct (Z.compare_spec (ctx_amount ctx mod 2) 0); auto; try congruence.
      }
      rewrite <- (Z_div_exact_2 (ctx_amount ctx) 2) by (auto; lia).
      split; auto.
      instantiate (DeployFacts := fun _ ctx => ctx_amount ctx >= 0);
        subst DeployFacts; cbn in *.
      apply Z.eqb_neq in amount_some.
      lia.
    - (* Transfer from contract to someone *)
      repeat rewrite txs_to_cons.
      do 5 (split; try tauto).
      destruct IH as [_ [_ [_ [<- [_ [only_transfers IH]]]]]].
      apply andb_prop in only_transfers.
      split; try tauto.
      destruct only_transfers as [is_transfer _].
      destruct out_act; try congruence.
      destruct tx_act_match as [<- [<- _]].
      repeat rewrite transfer_acts_to_cons in *.
      destruct (next_step cstate).
      + intuition congruence.
      + intuition congruence.
      + (* Transfer while next_step is withdraw; so seller or buyer withdrew *)
        do 2 (split; try tauto).
        destruct IH as [_ [_ [? ?]]].
        destruct_address_eq; cbn in *; lia.
      + (* Transfer while next_step is no_next_step; action moved from queue to txs *)
        destruct IH as [IH | IH]; [left|right].
        * do 2 (split; try tauto).
          destruct IH as [_ [? ?]].
          destruct_address_eq; cbn in *; lia.
        * split; try tauto.
          destruct IH as [_ ?].
          destruct_address_eq; cbn in *; lia.
    - (* Call from someone else *)
      do 2 (split; try tauto).
      unfold Escrow.receive in *.
      set (item_worth := deployment_amount dep_info / 2) in *.
      destruct msg as [[| |]|].
      + (* Some commit_money *)
        destruct (next_step prev_state); try congruence.
        destruct (address_eqb_spec (ctx_from ctx) (buyer prev_state)) as [->|];
          cbn in *; try congruence.
        destruct (ctx_amount ctx =? _) eqn:proper_amount in receive_some;
          cbn in *; try congruence.
        inversion_clear receive_some.
        cbn.
        do 4 (split; try tauto).
        destruct IH as [deployed_even [_ [_ [-> [_ [_ [balance_eq [-> [-> ->]]]]]]]]].
        apply Z.eqb_eq in proper_amount.
        rewrite balance_eq in proper_amount.
        rewrite proper_amount.
        replace (ctx_contract_balance _) with (2 * item_worth + 2 * item_worth / 2 * 2) by lia.
        rewrite <- Z.mul_comm.
        rewrite Z.div_mul by lia.
        repeat split;eauto.
        lia.
      + (* Some confirm_item_received *)
        destruct_match in receive_some; cbn in *; try congruence.
        destruct (address_eqb_spec (ctx_from ctx) (buyer prev_state)) as [->|];
          cbn in *; try congruence.
        destruct (ctx_amount ctx =? 0) eqn:zero_amount in receive_some;
          cbn in *; try congruence.
        inversion_clear receive_some.
        cbn.
        do 4 (split; try tauto).
        destruct IH as [deployed_even [? [<- [<- [_ [_ [balance_eq [-> [-> H]]]]]]]]].
        destruct H as [origin Hcalls].
        rewrite Hcalls.
        rewrite address_eq_refl.
        cbn.
        split; auto.
        unfold txs_to, transfer_acts_to; cbn.
        apply Z.eqb_eq in zero_amount.
        rewrite zero_amount in *.
        replace (ctx_contract_balance _) with (4 * item_worth) in * by lia.
        rewrite (Z.mul_comm 4).
        rewrite Z.div_mul by lia.
        destruct (Z.eqb_spec (2 * item_worth) 0); cbn in *; try lia.
        repeat split; eauto;lia.
      + (* Some withdraw. Can be sent while next_step is either
           commit_money or withdrawals. *)
        destruct_match eqn:prev_next_step in receive_some;
          cbn -[Nat.ltb] in *; try congruence.
        * (* next_step was commit_money, so seller is withdrawing money
          because buyer did not commit anything. *)
          destruct (ctx_amount ctx =? 0) eqn:zero_amount in receive_some;
            cbn -[Nat.ltb] in *; try congruence.
          apply Z.eqb_eq in zero_amount.
          rewrite zero_amount in *.
          destruct_match in receive_some; cbn in *; try congruence.
          destruct (address_eqb_spec (ctx_from ctx) (seller prev_state))
            as [->|]; cbn in *; try congruence.
          inversion_clear receive_some; cbn.
          do 4 (split; try tauto).
          (* In this case we go to no_next_step state without buyer having confirmed anything *)
          right.
          destruct IH as [_ [_ [<- [_ [? [_ [? [-> [-> ->]]]]]]]]].
          unfold txs_to, transfer_acts_to.
          cbn.
          rewrite address_eq_refl, address_eq_ne by auto.
          cbn.
          split; eauto; lia.
        * (* next_step was withdrawals, so either seller or buyer is withdrawing money.
             This might put us into next_step = no_next_step. *)
          destruct (ctx_amount ctx =? 0) eqn:zero_amount in receive_some;
            cbn -[Nat.ltb] in *; try congruence.
          apply Z.eqb_eq in zero_amount.
          rewrite zero_amount in *.
          destruct (address_eqb_spec (ctx_from ctx) (buyer prev_state))
            as [->|]; [|destruct (address_eqb_spec (ctx_from ctx) (seller prev_state))
                         as [->|]; cbn in *; try congruence].
          -- (* Buyer withdrawing *)
            cbn in *.
            destruct_match in receive_some; cbn in *; try congruence.
            inversion_clear receive_some; cbn.
            apply and_assoc; split; [destruct_match; tauto|].
            do 2 (split; try tauto).
            destruct (Z.eqb_spec (seller_withdrawable prev_state) 0) as [seller_done|].
            ++ (* No one has more to withdrew, next_step is no_next_step now, so establish
                  final IH. Since we got here from withdrawal we will be in left case. *)
              rewrite seller_done in *.
              left.
              repeat rewrite transfer_acts_to_cons.
              fold (buyer_confirmed prev_inc_calls
                                    (setup_buyer (deployment_setup dep_info))).
              destruct IH as [_ [_ [<- [-> [? [_ [-> [[? ->] [? ?]]]]]]]]].
              rewrite address_eq_refl.
              rewrite address_eq_ne by assumption.
              cbn.
              do 2 (split; [eauto|]).
              lia.
            ++ (* Seller still has more to withdraw, next_step is still withdrawals *)
              cbn.
              rewrite prev_next_step.
              repeat rewrite transfer_acts_to_cons.
              fold (buyer_confirmed prev_inc_calls
                                    (setup_buyer (deployment_setup dep_info))).
              destruct IH as [_ [_ [<- [-> [? [_ [-> [[? ->] [? ?]]]]]]]]].
              rewrite address_eq_refl.
              rewrite address_eq_ne by assumption.
              cbn.
              do 2 (split; eauto).
              lia.
          -- (* Seller withdrawing. Todo: generalize and clean up. *)
            cbn in *.
            destruct_match in receive_some; cbn in *; try congruence.
            inversion_clear receive_some; cbn.
            apply and_assoc; split; [destruct_match; tauto|].
            do 2 (split; try tauto).
            destruct (Z.eqb_spec (buyer_withdrawable prev_state) 0) as [buyer_done|].
            ++ (* No one has more to withdrew, next_step is no_next_step now, so establish
                  final IH. Since we got here from withdrawal we will be in left case. *)
              rewrite buyer_done in *.
              left.
              repeat rewrite transfer_acts_to_cons.
              fold (buyer_confirmed prev_inc_calls
                                    (setup_buyer (deployment_setup dep_info))).
              destruct IH as [_ [_ [<- [<- [? [_ [-> [[? ->] [? ?]]]]]]]]].
              rewrite address_eq_refl.
              rewrite address_eq_ne by auto.
              cbn.
              do 2 (split; eauto).
              lia.
            ++ (* Buyer still has more to withdraw, next_step is still withdrawals *)
              cbn.
              rewrite prev_next_step.
              repeat rewrite transfer_acts_to_cons.
              fold (buyer_confirmed prev_inc_calls
                                    (setup_buyer (deployment_setup dep_info))).
              destruct IH as [_ [_ [<- [<- [? [_ [-> [[? ->] [? ?]]]]]]]]].
              rewrite address_eq_refl.
              rewrite address_eq_ne by auto.
              cbn.
              do 2 (split; eauto).
              lia.
      + (* None *)
        congruence.
    - (* Self call *)
      instantiate (CallFacts := fun _ ctx _ _ => ctx_from ctx <> ctx_contract_address ctx);
        subst CallFacts; cbn in *; congruence.
    - (* Permuting queue *)
      do 5 (split; try tauto).
      split.
      + now rewrite <- perm.
      + assert (out_queue = [] -> out_queue' = [])
          by (intros ->; now apply Permutation_nil).
        unfold transfer_acts_to in *.
        repeat rewrite sumZ_filter in *.
        destruct (next_step cstate); try tauto.
        * now rewrite <- perm.
        * destruct IH as [_ [_ [_ [_ [_ [_ [IH | IH]]]]]]];
            [left|right]; rewrite <- perm; auto.
    - instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
      unset_all; subst; cbn in *.
      destruct_chain_step; auto.
      destruct_action_eval; auto.
      intros.
      pose proof (no_self_calls bstate_from to_addr ltac:(assumption) ltac:(assumption))
           as all.
      unfold outgoing_acts in *.
      rewrite queue_prev in *.
      subst act; cbn in all.
      destruct_address_eq; cbn in *; auto.
      inversion_clear all as [|? ? hd _].
      destruct msg.
      + contradiction.
      + rewrite address_eq_refl in hd.
        congruence.
  Qed.

  Definition net_balance_effect
             {bstate_from bstate_to : ChainState}
             (trace : ChainTrace bstate_from bstate_to)
             (caddr addr : Address) : Amount :=
    sumZ tx_amount (txs_to addr (outgoing_txs trace caddr))
    - sumZ tx_amount (txs_from addr (incoming_txs trace caddr)).

  (* Our main assumption is that the escrow will always finish due to
  economically rational actors. We do not formalize this. *)
  Definition is_escrow_finished cstate :=
    match next_step cstate with
    | no_next_step => true
    | _ => false
    end.

  (* The functional correctness of the Escrow, under the assumption that the
  escrow finishes due to rational actors. *)
  Corollary escrow_correct
            {ChainBuilder : ChainBuilderType}
            prev new header acts :
    builder_add_block prev header acts = Ok new ->
    let trace := builder_trace new in
    forall caddr,
      env_contracts new caddr = Some (Escrow.contract : WeakContract) ->
      exists (depinfo : DeploymentInfo Setup)
             (cstate : State)
             (inc_calls : list (ContractCallInfo Msg)),
        deployment_info Setup trace caddr = Some depinfo /\
        contract_state new caddr = Some cstate /\
        incoming_calls Msg trace caddr = Some inc_calls /\
        let item_worth := deployment_amount depinfo / 2 in
        let seller := deployment_from depinfo in
        let buyer := setup_buyer (deployment_setup depinfo) in
        is_escrow_finished cstate = true ->
        (buyer_confirmed inc_calls buyer = true /\
         net_balance_effect trace caddr seller = item_worth /\
         net_balance_effect trace caddr buyer = -item_worth \/

         buyer_confirmed inc_calls buyer = false /\
         net_balance_effect trace caddr seller = 0 /\
         net_balance_effect trace caddr buyer = 0).
  Proof.
    intros after_add trace caddr escrow_at_caddr.
    cbn in *.
    pose proof (escrow_correct_strong _ caddr trace escrow_at_caddr) as general.
    cbn in general.
    destruct general as
        [cstate [depinfo [inc_calls [? [? [? [? [? [? [? [? [_ IH]]]]]]]]]]]].
    exists depinfo, cstate, inc_calls.
    do 3 (split; [tauto|]).
    intros is_finished.
    unfold is_escrow_finished in *.
    destruct (next_step cstate); try congruence; clear is_finished.
    unfold net_balance_effect, money_to.
    assert (inc_txs:
              forall addr,
                sumZ tx_amount (txs_from addr (incoming_txs trace caddr)) =
                sumZ (fun '(a, b, c) => c)
                     (filter (fun '(from, _, _) => (from =? addr)%address)
                             (map (fun tx => (tx_from tx, tx_to tx, tx_amount tx))
                                  (incoming_txs trace caddr)))).
    {
      intros addr.
      induction (incoming_txs trace caddr) as [|hd tl IH'].
      - reflexivity.
      - rewrite txs_from_cons.
        cbn.
        destruct_address_eq; cbn in *; rewrite IH'; reflexivity.
    }

    repeat rewrite inc_txs; clear inc_txs.
    rewrite (incoming_txs_contract caddr _ trace _ depinfo _ inc_calls) by assumption.
    repeat rewrite filter_app, sumZ_app.
    cbn.
    rewrite address_eq_refl.
    rewrite address_eq_ne by auto.
    cbn.
    rewrite 2!filter_map, 2!sumZ_map.

    set (buyer_addr := setup_buyer (deployment_setup depinfo)) in *.
    set (seller_addr := deployment_from depinfo) in *.

    unfold money_to, transfer_acts_to in IH.
    cbn in IH.

    change (fun a => call_amount a) with (@call_amount _ Msg).

    destruct IH as [IH | IH]; [left|right].
    - split; [tauto|].
      destruct IH as [_ [[origin HH] ?]].
      remember (build_call_info _ _ _ (Some commit_money)) as commitment.
      assert (Hsum :
                forall f,
                  sumZ call_amount (filter f inc_calls) =
                  sumZ call_amount (filter f [commitment])).
      {
        intros f.
        rewrite <- HH.
        clear -inc_calls.
        induction inc_calls as [|hd tl IH']; auto.
        cbn.
        destruct (Z.eqb_spec (call_amount hd) 0) as [zero_amount|].
        - cbn.
          destruct (f hd); cbn; try rewrite zero_amount; rewrite IH'; auto.
        - cbn.
          destruct (f hd); cbn; rewrite IH'; auto.
      }

      rewrite 2!Hsum; clear Hsum; subst commitment; cbn in *.
      rewrite address_eq_refl, address_eq_ne by auto.
      cbn.
      split; lia.
    - destruct IH as [[? ->] IH].
      cbn.
      rewrite address_eq_refl, address_eq_ne by auto.
      cbn.
      split; [auto|].
      split; lia.
  Qed.

End Theories.

End EscrowSolana.
