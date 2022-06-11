(** Properties and tactics related to two communicating contracts *)

From ConCert.Utils Require Import Automation.
From ConCert.Execution Require Import BlockchainSolana.
From ConCert.Execution Require Import Serializable.
From Coq Require Import List.
Import ListNotations.

Ltac trace_induction :=
  match goal with
  | trace : ChainTrace empty_state ?bstate |- _ =>
    cbn;
    remember empty_state;
    induction trace as [| * IH step];
    match goal with
    | H : ?x = empty_state |- _ => subst x
    end;
    [try discriminate |
    destruct_chain_step; try (destruct_action_eval; try destruct_special_body_eval);
    match goal with
    | env_eq : EnvironmentEquiv _ _ |- _ => try rewrite env_eq in *; try setoid_rewrite env_eq
    end;
    repeat (specialize (IH ltac:(auto)))]; auto
  end.

Section InterContractCommunication.
Context {BaseTypes : ChainBase}.

Definition txCallTo (addr : Address) (tx : Tx) : bool :=
  match tx.(tx_body) with
  | tx_call _ => (tx.(tx_to) =? addr)%address
  | _ => false
  end.

Definition actTo (addr : Address) (act : ActionBody) : bool :=
  match act with
  | act_transfer to _ => (to =? addr)%address
  | act_call to _ => (to =? addr)%address
  | _ => false
  end.

Definition callFrom {Msg : Type} (addr : Address) (call_info : ContractCallInfo Msg) : bool :=
  (call_info.(call_from) =? addr)%address.

Lemma deployed_incoming_calls_typed : forall bstate caddr {Setup Msg State : Type}
          `{Serializable Msg}
          `{Serializable State}
          `{Serializable Setup}
          {contract : Contract Msg State Setup}
          (trace : ChainTrace empty_state bstate),
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  exists inc_calls,
    incoming_calls Msg trace caddr = Some inc_calls.
Proof.
  intros * deployed.
  trace_induction; cbn in *.
  - (* Contract deployment *)
    destruct_address_eq; eauto.
    now rewrite undeployed_contract_no_in_calls.
  - (* Contract call *)
    destruct IH as [? IH].
    rewrite IH.
    clear IH.
    destruct (address_eqb_spec caddr to_addr) as [<-|];
      try rewrite ?address_eq_refl, ?address_eq_ne; eauto.
    subst.
    rewrite deployed in deployed_state.
    inversion deployed_state.
    subst. clear deployed_state.
    apply wc_receive_strong in new_acts_eq as
      (prev_state' & msg' & new_state' & serialize_prev_state & msg_ser & serialize_new_state & receive_some).
    cbn in receive_some.
    destruct msg';
      try rewrite msg_ser; eauto.
    cbn in msg_ser.
    destruct msg; eauto.
    + destruct prev_state'; try rewrite msg_ser; eauto;
      destruct prev_state; (try rewrite msg_ser; eauto); eauto.
    + destruct prev_state; (try rewrite msg_ser; eauto); eauto.
Qed.

Lemma undeployed_contract_no_state : forall bstate caddr (trace : ChainTrace empty_state bstate),
  env_contracts bstate caddr = None ->
  env_contract_states bstate caddr = None.
Proof.
  intros * trace not_deployed.
  trace_induction; cbn in *;
    now destruct_address_eq.
Qed.

Lemma no_outgoing_txs_to_undeployed_contract : forall bstate caddrA caddrB
          (trace : ChainTrace empty_state bstate)
          {Msg State Setup : Type}
          `{Serializable Msg}
          `{Serializable State}
          `{Serializable Setup}
          {contract : Contract Msg State Setup},
  env_contracts bstate caddrA = Some (contract : WeakContract) ->
  env_contracts bstate caddrB = None ->
    filter (txCallTo caddrB) (outgoing_txs trace caddrA) = [].
Proof.
  intros * deployedA not_deployedB.
  trace_induction;
    repeat (cbn in *; destruct_address_eq); try easy; subst;
    eapply undeployed_contract_no_out_txs in not_deployed; auto;
    unfold outgoing_txs in not_deployed;
    (try now rewrite not_deployed); easy.
Qed.

Lemma no_incoming_calls_from_undeployed_contract : forall bstate caddrA caddrB
          (trace : ChainTrace empty_state bstate)
          {Msg State Setup : Type}
          `{Serializable Msg}
          `{Serializable State}
          `{Serializable Setup}
          {contract : Contract Msg State Setup},
  env_contracts bstate caddrA = None ->
  address_is_contract caddrA = true ->
  env_contracts bstate caddrB = Some (contract : WeakContract) ->
  exists inc_calls,
    incoming_calls Msg trace caddrB = Some inc_calls /\
    filter (callFrom caddrA) inc_calls = [].
Proof.
  intros * not_deployedA A_is_contract deployedB.
  trace_induction; cbn in *;
    destruct_address_eq; subst; try easy.
  - now rewrite undeployed_contract_no_in_calls by auto.
  - rewrite deployedB in deployed_state.
    inversion deployed_state.
    subst. clear deployed_state.
    apply wc_receive_strong in new_acts_eq as
      (prev_state' & msg' & new_state' & serialize_prev_state & msg_ser & serialize_new_state & receive_some).
    cbn in receive_some.
    destruct IH as (? & calls & ?).
    apply undeployed_contract_no_out_queue in not_deployedA; try easy.
    rewrite queue_prev in not_deployedA.
    destruct msg';
      [cbn in msg_ser; destruct msg; try easy|].
    destruct prev_state.  
      + setoid_rewrite msg_ser;
        rewrite calls;
        eexists;
        split; eauto;
        unfold callFrom; cbn;
        destruct_address_eq; auto;
        subst;
        apply Forall_inv in not_deployedA;
        now rewrite address_eq_refl in not_deployedA.
      + rewrite calls;
        eexists;
        split; eauto;
        unfold callFrom; cbn;
        destruct_address_eq; auto;
        subst;
        apply Forall_inv in not_deployedA;
        now rewrite address_eq_refl in not_deployedA.
      + destruct prev_state. 
        * setoid_rewrite msg_ser;
          rewrite calls;
          eexists;
          split; eauto;
          unfold callFrom; cbn;
          destruct_address_eq; auto;
          subst;
          apply Forall_inv in not_deployedA;
          now rewrite address_eq_refl in not_deployedA.
        * rewrite calls;
          eexists;
          split; eauto;
          unfold callFrom; cbn;
          destruct_address_eq; auto;
          subst;
          apply Forall_inv in not_deployedA;
          now rewrite address_eq_refl in not_deployedA.
       + destruct prev_state. 
        * easy.
        * rewrite calls;
          eexists;
          split; eauto;
          unfold callFrom; cbn;
          destruct_address_eq; auto;
          subst;
          apply Forall_inv in not_deployedA;
          now rewrite address_eq_refl in not_deployedA.
Qed.

Definition contract_call_info_to_tx `{X : Type} `{Serializable X} (caddr : Address) (call_info : ContractCallInfo X) : Tx :=
  let body :=
    match call_info.(call_msg) with
    | Some (msg) => tx_call (Some (serialize msg))
    | None => tx_call None
    end in
  {|
    tx_origin := call_info.(call_origin);
    tx_from := call_info.(call_from);
    tx_to := caddr;
    tx_amount := call_info.(call_amount);
    tx_body := body
  |}.

Definition tx_to_contract_call_info `{X : Type} `{Serializable X} (tx : Tx) : option (ContractCallInfo X) :=
  match tx.(tx_body) with
  | tx_call None => Some
    {|
      call_origin := tx.(tx_origin);
      call_from := tx.(tx_from);
      call_amount := tx.(tx_amount);
      call_msg := None
    |}
  | tx_call (Some m) => Some
    {|
      call_origin := tx.(tx_origin);
      call_from := tx.(tx_from);
      call_amount := tx.(tx_amount);
      call_msg := @deserialize X _ m
    |}
  | _ => None
  end.

(* J> TODO: Fix naming again *)
Lemma incomming_eq_outgoing : forall bstate caddrA caddrB
          (trace : ChainTrace empty_state bstate)
          {MsgA MsgB StateA StateB SetupA SetupB : Type}
          `{Serializable MsgA} `{Serializable StateA} `{Serializable SetupA}
          `{Serializable MsgB} `{Serializable StateB} `{Serializable SetupB}
          {contractA : Contract MsgA StateA SetupA}
          {contractB : Contract MsgB StateB SetupB},
  (forall x (y : MsgB), deserialize x = Some y -> x = serialize y) ->
  env_contracts bstate caddrA = Some (contractA : WeakContract) ->
  env_contracts bstate caddrB = Some (contractB : WeakContract) ->
  exists inc_calls,
    incoming_calls MsgB trace caddrB = Some inc_calls /\
    (filter (txCallTo caddrB) (outgoing_txs trace caddrA)) =
    map (contract_call_info_to_tx caddrB) (filter (callFrom caddrA) inc_calls).
Proof.
  intros * deserialize_right_inverse deployedA deployedB.
  trace_induction; cbn in *.
  - destruct_address_eq; auto.
  - destruct_address_eq; auto; subst;
      try (apply MCOption.some_inj in deployedA; subst);
      try (apply MCOption.some_inj in deployedB; rewrite deployedB in *; clear deployedB);
      try (rewrite undeployed_contract_no_in_calls by auto);
      try (eapply undeployed_contract_no_out_txs in not_deployed as no_txs; eauto;
            unfold outgoing_txs in no_txs; rewrite no_txs); cbn;
      try (eapply no_outgoing_txs_to_undeployed_contract in not_deployed as no_txs; cycle -1; eauto;
            unfold outgoing_txs in no_txs; rewrite no_txs);
      try (eapply no_incoming_calls_from_undeployed_contract in not_deployed; eauto;
        destruct not_deployed as (calls & inc_calls_eq & calls_eq);
        exists calls; now rewrite inc_calls_eq, calls_eq);
      try now exists [].
      + eexists.
        split; try easy; cbn in *.
        try (eapply no_outgoing_txs_to_undeployed_contract in act_eq as no_txs1; cycle -1; eauto).
      + eexists.
        split; try easy; cbn in *.
        try (eapply no_outgoing_txs_to_undeployed_contract in act_eq as no_txs1; cycle -1; eauto).
  - destruct_address_eq; subst; auto.
    + rewrite deployedB in deployed_state.
      inversion deployed_state.
      subst. clear deployed_state.
      apply wc_receive_strong in new_acts_eq as
        (prev_state' & msg' & new_state' & serialize_prev_state & msg_ser & serialize_new_state & process_some).
      cbn in process_some.
      destruct IH as (? & calls & IH).
      destruct msg';
        [cbn in msg_ser; destruct msg; try easy|];
        destruct prev_state;
        try setoid_rewrite msg_ser.
      * rewrite calls;
        eexists;
        split; eauto.
        unfold callFrom in *; cbn.
        rewrite !address_eq_refl.
        cbn.
        rewrite <- IH.
        unfold contract_call_info_to_tx. cbn.
        do 4 f_equal. easy.
      * rewrite calls;
        eexists;
        split; eauto.
        unfold callFrom in *; cbn.
        rewrite !address_eq_refl.
        cbn.
        rewrite <- IH.
        unfold contract_call_info_to_tx. cbn.
        do 4 f_equal. 
      * rewrite calls;
        eexists;
        split; eauto.
        unfold callFrom in *; cbn.
        rewrite !address_eq_refl.
        cbn.
        rewrite <- IH.
        unfold contract_call_info_to_tx. cbn.
        do 4 f_equal. easy.
      * rewrite calls;
        eexists;
        split; eauto.
        unfold callFrom in *; cbn.
        rewrite !address_eq_refl.
        cbn.
        rewrite <- IH.
        unfold contract_call_info_to_tx. cbn.
        do 4 f_equal.
      * rewrite calls;
        eexists;
        split; eauto.
        unfold callFrom in *; cbn.
        easy.
        unfold callFrom in *; cbn.
        rewrite !address_eq_refl.
        easy.
      * rewrite calls;
        eexists;
        split; eauto.
        unfold callFrom in *; cbn.
        rewrite !address_eq_refl.
        cbn.
        rewrite <- IH.
        unfold contract_call_info_to_tx. cbn.
        do 4 f_equal.
    + rewrite deployedB in deployed_state.
      inversion deployed_state.
      subst. clear deployed_state.
      apply wc_receive_strong in new_acts_eq as
        (prev_state' & msg' & new_state' & serialize_prev_state & msg_ser & serialize_new_state & process_some).
      cbn in process_some.
      destruct IH as (? & calls & ?).
      destruct msg';
        [cbn in msg_ser; destruct msg; try easy|].
        destruct prev_state;
        try setoid_rewrite msg_ser.
        * rewrite calls;
          eexists;
          split; eauto;
          unfold callFrom; cbn;
          now destruct_address_eq.
        * rewrite calls;
          eexists;
          split; eauto;
          unfold callFrom; cbn;
          now destruct_address_eq.
        * destruct prev_state.
          ** rewrite msg_ser. 
             rewrite calls;
             eexists;
             split; eauto;
             unfold callFrom; cbn;
             now destruct_address_eq.
          ** rewrite msg_ser. 
             rewrite calls;
             eexists;
             split; eauto;
             unfold callFrom; cbn;
             now destruct_address_eq.
        * destruct prev_state.
          ** easy. 
          ** rewrite calls;
             eexists;
             split; eauto;
             unfold callFrom; cbn;
             now destruct_address_eq.
    + cbn.
      now rewrite address_eq_ne.
  - destruct_address_eq; auto; subst.
    Unshelve. easy.
Qed.
End InterContractCommunication.
