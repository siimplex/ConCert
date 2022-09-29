From Coq Require Import Lia.
From Coq Require Import List.
From Coq Require Import Logic.Decidable.
From Coq Require Import ZArith.
Import ListNotations.
From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Execution Require Import BlockchainSolanav2.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ResultMonad.

Section BuildUtils.
Context {BaseTypes : ChainBase}.

(* The empty state is always reachable *)
Lemma reachable_empty_state :
  reachable empty_state.
Proof.
  repeat constructor.
Qed.

(* Transitivity property of reachable and ChainTrace *)
Lemma reachable_trans from to :
  reachable from -> ChainTrace from to -> reachable to.
Proof.
  intros [].
  constructor.
  now eapply ChainedList.clist_app.
Qed.

(* Transitivity property of reachable and ChainStep *)
Lemma reachable_step from to :
  reachable from -> ChainStep from to -> reachable to.
Proof.
  intros [].
  now do 2 econstructor.
Qed.

(* If a state is reachable then the finalized_height cannot be larger than the chain_height *)
Lemma finalized_heigh_chain_height bstate :
  reachable bstate ->
  finalized_height bstate < S (chain_height bstate).
Proof.
  intros [trace].
  remember empty_state.
  induction trace as [ | Heq from to trace IH step ]; subst.
  - auto.
  - destruct_chain_step;
    try (destruct_action_eval; try destruct_special_body_eval);
    try rewrite_environment_equiv;
    auto.
    + now inversion valid_header.
Qed.

(* If a state is reachable and contract state is stored on an address 
    then that address must also have some contract deployed to it *)
Lemma contract_states_deployed to (addr : Address) (state : SerializedValue) :
  reachable to ->
  env_contract_states to addr = Some state ->
  exists wc, env_contracts to addr = Some wc.
Proof.
  intros [trace].
  remember empty_state.
  induction trace as [ | Heq from to trace IH step ];
    subst; intros.
  - discriminate.
  - destruct_chain_step;
      only 2: (destruct_action_eval; try destruct_special_body_eval);
      try rewrite_environment_equiv;
      try (setoid_rewrite env_eq; cbn in *;
      destruct_address_eq; now subst).
Qed.

(* If a state is reachable and contract state is stored on an address 
    then that address must be a contract address *)
Lemma contract_states_addr_format to (addr : Address) (state : SerializedValue) :
  reachable to ->
  env_contract_states to addr = Some state ->
  address_is_contract addr = true.
Proof.
  intros ? deployed_state.
  apply contract_states_deployed in deployed_state as []; auto.
  now eapply contract_addr_format.
Qed.

Hint Resolve reachable_empty_state
             reachable_trans
             reachable_step : core.

(* A state `to` is reachable through `mid` if `mid` is reachable and there exists a trace
    from `mid` to `to`. This captures that there is a valid execution ending up in `to`
    and going through the state `mid` at some point *)
Definition reachable_through mid to := reachable mid /\ inhabited (ChainTrace mid to).

(* A state is always reachable through itself *)
Lemma reachable_through_refl : forall bstate,
  reachable bstate -> reachable_through bstate bstate.
Proof.
  intros bstate reach.
  split; auto.
  do 2 constructor.
Qed.

(* Transitivity property of reachable_through and ChainStep *)
Lemma reachable_through_trans' : forall from mid to,
  reachable_through from mid -> ChainStep mid to -> reachable_through from to.
Proof.
  intros * [reach [trace]] step.
  repeat (econstructor; eauto).
Qed.

(* Transitivity property of reachable_through *)
Lemma reachable_through_trans : forall from mid to,
  reachable_through from mid -> reachable_through mid to -> reachable_through from to.
Proof.
  intros * [[trace_from] [trace_mid]] [_ [trace_to]].
  do 2 constructor.
  assumption.
  now eapply ChainedList.clist_app.
Qed.

(* Reachable_through can also be constructed from ChainStep instead of a
   ChainTrace since a ChainTrace can be constructed from a ChainStep *)
Lemma reachable_through_step : forall from to,
  reachable from -> ChainStep from to -> reachable_through from to.
Proof.
  intros * reach_from step.
  apply reachable_through_refl in reach_from.
  now eapply reachable_through_trans'.
Qed.

(* Any ChainState that is reachable through another ChainState is reachable *)
Lemma reachable_through_reachable : forall from to,
  reachable_through from to -> reachable to.
Proof.
  intros * [[trace_from] [trace_to]].
  constructor.
  now eapply ChainedList.clist_app.
Qed.

Hint Resolve reachable_through_refl
             reachable_through_trans'
             reachable_through_trans
             reachable_through_step
             reachable_through_reachable : core.


(* If a state has a contract deployed to some addr then any other state
    reachable through the first state must also have the same contract
    deployed to the same addr *)
Lemma reachable_through_contract_deployed : forall from to addr wc,
  reachable_through from to -> env_contracts from addr = Some wc ->
    env_contracts to addr = Some wc.
Proof.
  intros * [reach [trace]] deployed.
  induction trace as [ | from mid to trace IH step ].
  - assumption.
  - destruct_chain_step;
      only 2: (destruct_action_eval; try destruct_special_body_eval);
      rewrite_environment_equiv; cbn;
      destruct_address_eq; subst; try easy.
    now rewrite IH in not_deployed by assumption.
Qed.

(* J> TODO: Make this proof shorter, naming is messed as well *)
(* If a state has a contract state on some addr then any other state
    reachable through the first state must also have the some contracts
    state on the same addr *)
Lemma reachable_through_contract_state : forall from to addr cstate,
  reachable_through from to -> env_contract_states from addr = Some cstate ->
    exists new_cstate, env_contract_states to addr = Some new_cstate.
Proof.
  intros * [reachable [trace]] deployed_state.
  generalize dependent cstate.
  induction trace as [ | from mid to trace IH step ];
    intros cstate deployed_state.
  - now eexists.
  - destruct_chain_step;
      only 2: (destruct_action_eval; try destruct_special_body_eval);
      try rewrite_environment_equiv;
      cbn in *;
      (try (setoid_rewrite env_eq);
      cbn in *;
      destruct_address_eq; now subst).
Qed.

(* If a state is reachable through another state then it cannot have a lower chain height *)
Lemma reachable_through_chain_height : forall from to,
  reachable_through from to -> from.(chain_height) <= to.(chain_height).
Proof.
  intros * [reachable [trace]].
  induction trace as [ | from mid to trace IH step ].
  - apply le_refl.
  - destruct_chain_step;
    try (destruct_action_eval; try destruct_special_body_eval);
    rewrite_environment_equiv; cbn; auto.
    + now inversion valid_header.
Qed.

(* If a state is reachable through another state then it cannot have a lower current slot *)
Lemma reachable_through_current_slot : forall from to,
  reachable_through from to -> from.(current_slot) <= to.(current_slot).
Proof.
  intros * [reachable [trace]].
  induction trace as [ | from mid to trace IH step ].
  - apply le_refl.
  - destruct_chain_step;
    try (destruct_action_eval; try destruct_special_body_eval);
    rewrite_environment_equiv; cbn; auto.
    + now inversion valid_header.
Qed.

(* If a state is reachable through another state then it cannot have a lower finalized height *)
Lemma reachable_through_finalized_height : forall from to,
  reachable_through from to -> from.(finalized_height) <= to.(finalized_height).
Proof.
  intros * [reachable [trace]].
  induction trace as [ | from mid to trace IH step ].
  - apply le_refl.
  - destruct_chain_step;
    try (destruct_action_eval; try destruct_special_body_eval);
    rewrite_environment_equiv; cbn; auto.
    + now inversion valid_header.
Qed.

(* Initial contract balance will always be positive in reachable states *)
Lemma deployment_amount_nonnegative : forall
                                      bstate caddr dep_info
                                      (trace : ChainTrace empty_state bstate),
  deployment_info trace caddr = Some dep_info ->
  (0 <= dep_info.(deployment_amount))%Z.
Proof.
  intros * deployment_info_some.
  remember empty_state.
  induction trace; subst.
  - discriminate.
  - destruct_chain_step; auto.
    destruct_action_eval; auto.
    cbn in deployment_info_some.
    destruct_address_eq; auto.
    inversion_clear deployment_info_some. cbn.
    apply Z.ge_le. rewrite amount_nonnegative. easy. 
Qed.

(* Print wc_process. *)

Definition receiver_can_receive_transfer (bstate : ChainState) act_body :=
  match act_body with
  | act_transfer to _ => address_is_contract to = false \/
    (exists wc,
      env_contracts bstate to = Some wc /\
      forall (bstate_new : ChainState) (accs : SliceAccountInformation),
           wc_process wc bstate_new accs None = (ResultMonad.Ok tt))
  | _ => True
  end.

(* This axiom states that for any reachable state and any contract it is
    decidable wether or there is an address where the contract can be deployed to.
   This is not provable in general with the assumption ChainBase makes about
    addresses and the function address_is_contract. However this should be
    provable in any sensible instance of ChainBase *)
Axiom deployable_address_decidable : forall bstate wc accounts msg act_from amount,
  reachable bstate ->
  decidable (exists addr, address_is_contract addr = true 
            /\ env_contracts bstate addr = None
            /\ wc_process wc
                  (transfer_balance act_from addr amount bstate)
                  accounts
                  msg = ResultMonad.Ok tt).

Ltac action_not_decidable :=
  right; intro;
  match goal with
  | H : exists bstate new_acts, inhabited (ActionEvaluation _ _ bstate new_acts) |- False =>
    destruct H as [bstate_new [new_acts [action_evaluation]]];
    destruct_action_eval; try congruence
  end; repeat
  match goal with
  | H : {| act_origin := _; act_from := _; act_body := _ |} = {| act_origin := _; act_from := _; act_body := match ?msg with | Some _ => _ | None =>_ end |} |- False =>
    destruct msg
  | H : {| act_origin := _; act_from := _; act_body := _ |} = {| act_origin := _; act_from := _; act_body := _ |} |- False =>
    inversion H; subst; clear H
  end.

Ltac action_decidable :=
  left; do 2 eexists; constructor;
  match goal with
  | H : wc_process _ _ (Some _) _ ?m = Some _ |- _ => eapply (eval_call _ _ _ _ _ _ m)
  | H : wc_process _ _ None _ = Some _ |- _ => eapply eval_deploy
  | H : context [act_transfer _ _] |- _ => eapply eval_transfer
  end;
  eauto; try now constructor.

Ltac rewrite_balance :=
  match goal with
  | H := context [if (_ =? ?to)%address then _ else _ ],
    H2 : Environment |- _ =>
    assert (new_to_balance_eq : env_account_balances H2 to = H);
    [ try rewrite_environment_equiv; cbn; unfold H; destruct_address_eq; try congruence; lia |
    now rewrite <- new_to_balance_eq in *]
  end.

(* J> TODO: Fix this proof *)
(* For any reachable state and an action it is decidable if it is
    possible to evaluate the action in the state *)
Open Scope Z_scope.
Lemma action_evaluation_decidable : forall bstate act,
  reachable bstate ->
  decidable (exists bstate' new_acts, inhabited (ActionEvaluation bstate act bstate' new_acts)).
Proof.
  intros * reach.
  destruct act eqn:Hact.
  destruct act_body. 
  - (destruct (amount >=? 0) eqn:amount_positive;
    [destruct (amount <=? env_account_balances bstate act_from) eqn:balance |
      action_not_decidable; now rewrite Z.geb_leb, Z.leb_gt in amount_positive (* Eliminate cases where amount is negative *)];
    [| action_not_decidable; now rewrite Z.leb_gt in balance ]). (* Eliminate cases where sender does not have enough balance *)
  try (destruct (address_is_contract to) eqn:to_is_contract;
    [destruct (env_contracts bstate to) eqn:to_contract;
    [destruct (env_contract_states bstate to) eqn:contract_state |] |]);
  try now action_not_decidable. (* Eliminate cases with obvious contradictions *)
  all : rewrite Z.geb_leb, <- Zge_is_le_bool in amount_positive.
  all : rewrite Z.leb_le in balance.
    + action_decidable. Admitted. 
(*   - (* act_body = act_transfer to amount *)
    pose (new_to_balance := if (address_eqb act_from to)
                         then (env_account_balances bstate to)
                         else (env_account_balances bstate to) + amount).
    destruct (wc_receive w
        (transfer_balance act_from to amount bstate)
        (build_ctx act_origin act_from to new_to_balance amount)
        s None) eqn:receive.
    + (* Case: act_transfer is evaluable by eval_call *)
      destruct p.
      pose (bstate' := (set_contract_state to s0
                       (transfer_balance act_from to amount bstate))).
      action_decidable.
      rewrite_balance.
    + (* Case: act_transfer is not evaluable by eval_call
          because wc_receive returned None *)
      action_not_decidable.
      rewrite_balance.
  - (* act_body = act_transfer to amount *)
    (* Case: act_transfer is evaluable by eval_transfer *)
    pose (bstate' := (transfer_balance act_from to amount bstate)).
    action_decidable.
  - (* act_body = act_call to amount msg *)
    pose (new_to_balance := if (address_eqb act_from to)
                         then (env_account_balances bstate to)
                         else (env_account_balances bstate to) + amount).
    destruct (wc_receive w
        (transfer_balance act_from to amount bstate)
        (build_ctx act_origin act_from to new_to_balance amount)
        s (Some msg)) eqn:receive.
    + (* Case: act_call is evaluable by eval_call *)
      destruct p.
      pose (bstate' := (set_contract_state to s0
                       (transfer_balance act_from to amount bstate))).
      action_decidable.
      rewrite_balance.
    + (* Case: act_call is not evaluable by eval_call
          because wc_receive returned None *)
      action_not_decidable.
      rewrite_balance.
  - (* act_body = act_call to amount msg *)
    (* Case: contradiction *)
    action_not_decidable.
    now apply contract_addr_format in deployed; auto.
  - (* act_body = act_deploy amount c setup *)
    apply deployable_address_decidable
      with (wc:=c) (setup:=setup) (act_origin:=act_origin)
      (act_from:=act_from) (amount:=amount)
      in reach.
    destruct reach as [[to [state [to_is_contract_addr [to_not_deployed init]]]] | no_deployable_addr].
    + (* Case: act_deploy is evaluable by eval_deploy *)
      pose (bstate' := (set_contract_state to state
                       (add_contract to c
                       (transfer_balance act_from to amount bstate)))).
      action_decidable.
    + (* Case: act_deploy is not evaluable by eval_deploy
          because no there is no available contract address
          that this contract can be deployed to *)
      action_not_decidable.
      apply no_deployable_addr.
      eauto.
Qed. *)
Close Scope Z_scope.

(* Property stating that an action does not produce any new action when evaluated *)
Definition produces_no_new_acts act : Prop :=
  forall bstate bstate' new_acts, ActionEvaluation bstate act bstate' new_acts -> new_acts = [].

(* Property on a ChainState queue stating all actions are from accounts and produces
    no new actions when evaluated. This ensures that the queue can be emptied successfully *)
Definition emptyable queue : Prop :=
  Forall act_is_from_account queue /\
  Forall produces_no_new_acts queue.

(* An empty queue is always emptyable *)
Lemma empty_queue_is_emptyable : emptyable [].
Proof.
  now constructor.
Qed.

(* A subset of a emptyable queu is also emptyable *)
Lemma emptyable_cons : forall x l,
  emptyable (x :: l) -> emptyable l.
Proof.
  intros * [acts_from_account no_new_acts].
  apply Forall_inv_tail in acts_from_account.
  now apply Forall_inv_tail in no_new_acts.
Qed.

(* For any reachable state it is possible to empty the chain_state_queue
    if the queue only contains action that satisfy the following
    1) the action is from a user and not a contract
    2) the action does not produce any actions when evaluated
   For any property that holds on the starting state this also hold on
    the state with an empty queue if it can be proven that the property
    holds after evaluating any action.
*)
Lemma empty_queue : forall bstate (P : ChainState -> Prop),
  reachable bstate ->
  emptyable (chain_state_queue bstate) ->
  P bstate ->
  (forall (bstate bstate' : ChainState) act acts, reachable bstate -> reachable bstate' -> P bstate ->
    chain_state_queue bstate = act :: acts -> chain_state_queue bstate' = acts ->
    (inhabited (ActionEvaluation bstate act bstate' []) \/ EnvironmentEquiv bstate bstate') -> P bstate' ) ->
    exists bstate', reachable_through bstate bstate' /\ P bstate' /\ (chain_state_queue bstate') = [].
Proof.
  intros * reach [acts_from_account no_new_acts].
  remember (chain_state_queue bstate) as queue.
  generalize dependent bstate.
  induction queue; intros bstate reach Hqueue_eq HP HP_preserved.
  - (* Case: queue is already empty, thus we are already done *)
    now eexists.
  - (* Case: queue contains at least one action, 
        thus we need to either discard or evaluate it *)
    apply list.Forall_cons_1 in acts_from_account as [act_from_a acts_from_account].
    apply list.Forall_cons_1 in no_new_acts as [no_new_acts_from_a no_new_acts].
    edestruct action_evaluation_decidable as
      [[mid_env [new_acts [action_evaluation]]] | no_action_evaluation]; eauto.
    + (* Case: the action is evaluable *)
      pose (build_chain_state mid_env (new_acts ++ queue)) as mid.
      assert (step : ChainStep bstate mid) by (now eapply step_action).
      apply no_new_acts_from_a in action_evaluation as new_acts_eq; subst.
      eapply HP_preserved with (bstate' := mid) in HP; eauto.
      apply IHqueue in HP as [to [reachable_through [P_to queue_to]]]; subst; eauto.
      now exists to.
    + (* Case: the action not is evaluable *)
      pose (bstate<| chain_state_queue := queue |>) as mid.
      assert (step : ChainStep bstate mid).
      { eapply step_action_invalid; try easy.
        intros. apply no_action_evaluation.
        now do 2 eexists.
      }
      apply reachable_step in step as reachable_mid; eauto.
      apply IHqueue in reachable_mid as [to [reachable_through [P_to queue_to]]]; eauto.
      exists to.
      intuition.
      eauto.
      eapply (HP_preserved bstate mid); eauto.
      now right.
Qed.

(* wc_process and contract process are equivalent *)
Lemma wc_process_to_process : forall {Msg State : Type}
                                    `{Serializable Msg}
                                    `{Serializable State}
                                    (contract : Contract Msg State)
                                    chain accounts msg result,
  contract.(process) chain accounts (Some msg) = result <->
  wc_process contract chain accounts (Some ((@serialize Msg _) msg)) = result.
Proof.
  split; intros process_some.
  - cbn. Admitted. (* easy. 
    rewrite !deserialize_serialize, process_some.
  - apply wc_process_strong in process_some.
    cbn in *.
    rewrite deserialize_serialize in process_some.
    cbn in *. destruct process_some.
    destruct x; easy.
Qed. *)


(* wc_init and contract init are equivalent *)
(* Lemma wc_init_to_init : forall {Msg State Setup : Type}
                               `{Serializable Msg}
                               `{Serializable State}
                               `{Serializable Setup}
                               (contract : Contract Msg State Setup)
                               chain accounts cstate msg,
  contract.(process) chain accounts None (Some msg) = Some (cstate, []) <->
  wc_process contract chain accounts None (Some ((@serialize Msg _) msg)) = Some (((@serialize State _) cstate), []).
Proof.
  split; intros process_some.
  - cbn.
    now rewrite deserialize_serialize, process_some.
  - apply wc_receive_strong in process_some as
      (state_strong & msg_strong & serialize_state & serialize_state2 & serialize_result).
    destruct state_strong eqn: Hstate. cbn in *.
    + inversion serialize_state2.
    + destruct msg_strong eqn: Hmsg. cbn in *. subst.
      * destruct serialize_result as [serialize_msg]. 
        destruct H2 as [serialize_result process_some]. 
        apply serialize_injective in serialize_result. subst.
        rewrite deserialize_serialize in serialize_msg. subst.
        now inversion serialize_msg.
      * destruct serialize_result as [serialize_msg]. 
        destruct H2 as [serialize_result process_some]. 
        apply serialize_injective in serialize_result. subst.
        now inversion serialize_msg.   
Qed. *)

Open Scope Z_scope.
(* Lemma showing that there exists a future ChainState with an added block *)
Lemma add_block : forall bstate reward creator acts slot_incr,
  reachable bstate ->
  chain_state_queue bstate = [] ->
  address_is_contract creator = false ->
  reward >= 0->
  (slot_incr > 0)%nat ->
  Forall act_is_from_account acts ->
  Forall act_origin_is_eq_from acts ->
    (exists bstate',
       reachable_through bstate bstate'
    /\ chain_state_queue bstate' = acts
    /\ EnvironmentEquiv
        bstate'
        (add_new_block_to_env {| block_height := S (chain_height bstate);
          block_slot := current_slot bstate + slot_incr;
          block_finalized_height := finalized_height bstate;
          block_creator := creator;
          block_reward := reward; |} bstate)).
Proof.
  intros * reach queue creator_not_contract
    reward_positive slot_incr_positive
    acts_from_accounts origins_from_accounts.
  pose (header :=
    {| block_height := S (chain_height bstate);
       block_slot := current_slot bstate + slot_incr;
       block_finalized_height := finalized_height bstate;
       block_creator := creator;
       block_reward := reward; |}).
  pose (bstate_with_acts := (bstate<|chain_state_queue := acts|>
                                   <|chain_state_env := add_new_block_to_env header bstate|>)).
  assert (step_with_acts : ChainStep bstate bstate_with_acts).
  { eapply step_block; try easy.
    - constructor; try easy.
      + cbn. lia.
      + split; try (cbn; lia). cbn.
        now apply finalized_heigh_chain_height.
  }
  exists bstate_with_acts.
  split; eauto.
  split; eauto.
  constructor; try reflexivity.
Qed.

(* Lemma showing that there exists a future ChainState with the
    same contract states where the current slot is <slot> *)
Lemma forward_time_exact : forall bstate reward creator slot,
  reachable bstate ->
  chain_state_queue bstate = [] ->
  address_is_contract creator = false ->
  reward >= 0 ->
  (current_slot bstate < slot)%nat ->
    (exists bstate' header,
       reachable_through bstate bstate'
    /\ IsValidNextBlock header bstate
    /\ (slot = current_slot bstate')%nat
    /\ chain_state_queue bstate' = []
    /\ EnvironmentEquiv
        bstate'
        (add_new_block_to_env header bstate)).
Proof.
  intros bstate reward creator slot reach queue
    creator_not_contract reward_positive slot_not_hit.
  eapply add_block with (slot_incr := (slot - current_slot bstate)%nat) in reach as new_block; try easy.
  destruct new_block as [bstate_with_act [reach' [queue' env_eq]]].
  do 2 eexists.
  split; eauto.
  do 3 try split; only 9: apply env_eq; eauto; cbn; try lia.
  - now apply finalized_heigh_chain_height.
  - rewrite_environment_equiv. cbn. lia.
Qed.

(* Lemma showing that there exists a future ChainState with the
    same contract states where the current slot is at least <slot> *)
Lemma forward_time : forall bstate reward creator slot,
  reachable bstate ->
  chain_state_queue bstate = [] ->
  address_is_contract creator = false ->
  reward >= 0 ->
    (exists bstate' header,
       reachable_through bstate bstate'
    /\ IsValidNextBlock header bstate
    /\ (slot <= current_slot bstate')%nat
    /\ chain_state_queue bstate' = []
    /\ EnvironmentEquiv
        bstate'
        (add_new_block_to_env header bstate)).
Proof.
  intros * reach queue creator_not_contract reward_positive.
  destruct (slot - current_slot bstate)%nat eqn:slot_hit.
  - eapply add_block with (slot_incr := 1%nat) in reach as new_block; try easy.
    destruct new_block as [bstate_with_act [reach' [queue' env_eq]]].
    do 2 eexists.
    split; eauto.
    do 3 try split; only 9: apply env_eq; eauto; cbn; try lia.
    + now apply finalized_heigh_chain_height.
    + apply NPeano.Nat.sub_0_le in slot_hit.
      rewrite_environment_equiv. cbn. lia.
  - specialize forward_time_exact with (slot := slot) as
      (bstate' & header & reach' & header_valid & slot_hit' & queue' & env_eq);
      try easy.
    do 2 eexists.
    split; eauto.
    intuition.
Qed.

(* Lemma showing that there exists a future ChainState
    where the contract call is evaluated *)
Lemma evaluate_action : forall {Setup Msg State : Type}
                              `{Serializable Msg}
                              `{Serializable State}
                               (contract : Contract Msg State)
                               bstate origin from caddr amount msg acts new_acts
                               cstate new_cstate accounts,
  reachable bstate ->
  chain_state_queue bstate = {| act_from := from;
                                act_origin := origin;
                                act_body := act_call caddr ((@serialize Msg _) msg) |} :: acts ->
  amount >= 0 ->
  env_account_balances bstate from >= amount ->
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  env_contract_states bstate caddr = Some ((@serialize State _) cstate) ->
  BlockchainSolanav2.process contract (transfer_balance from caddr amount bstate)
                     accounts
                     (Some msg) = (Ok tt) ->
    (exists bstate',
       reachable_through bstate bstate'
    /\ env_contract_states bstate' caddr = Some ((@serialize State _) new_cstate)
    /\ chain_state_queue bstate' = (map (build_act origin caddr) new_acts) ++ acts
    /\ EnvironmentEquiv
        bstate'
        (set_contract_state caddr ((@serialize State _) new_cstate) (transfer_balance from caddr amount bstate))).
Proof.
  intros type.
  intros * reach queue amount_nonnegative enough_balance%Z.ge_le
    deployed deployed_state process_some.
  pose (new_to_balance := if (address_eqb from caddr)
                         then (env_account_balances bstate caddr)
                         else (env_account_balances bstate caddr) + amount).
  pose (bstate' := (bstate<|chain_state_queue := (map (build_act origin caddr) new_acts) ++ acts|>
                          <|chain_state_env := set_contract_state caddr ((@serialize State _) new_cstate)
                                                  (transfer_balance from caddr amount bstate)|>)).
  assert (new_to_balance_eq : env_account_balances bstate' caddr = new_to_balance).
  (cbn; destruct_address_eq); try easy.
  all: swap 1 3.
(*   all: swap 2 3. *)

  assert (step : ChainStep bstate bstate').
  - eapply step_action; eauto.
    eapply eval_call with (msg0:= Some ((@serialize Msg _) msg)); eauto.
    + apply wc_process_to_process in process_some. cbn in *.
    (* + constructor; reflexivity.
  - exists bstate'.
    split; eauto.
    repeat split; eauto.
    cbn.
    now destruct_address_eq.
  - cbn in *. destruct (from =? caddr)%address; try easy.
    unfold new_to_balance. assert (0 = amount); try easy. *)
    Admitted.
(* Qed. *)

(* Lemma showing that there exists a future ChainState
    where the transfer action is evaluated *)
Lemma evaluate_transfer : forall bstate origin from to origin_acc from_acc to_acc amount acts,
  reachable bstate ->
  chain_state_queue bstate = {| act_from := from;
                                act_origin := origin;
                                act_body := act_transfer to amount |} :: acts ->
  amount >= 0 ->
  env_account_balances bstate from >= amount ->
  account_address origin_acc = origin ->
  account_address from_acc = from ->
  account_address to_acc = to ->
  address_is_contract to = false ->
    (exists bstate',
       reachable_through bstate bstate'
    /\ chain_state_queue bstate' = acts
    /\ EnvironmentEquiv
        bstate'
        (transfer_balance from to amount bstate)).
Proof.
  intros * reach queue amount_nonnegative enough_balance%Z.ge_le origin_acc_eq from_acc_eq to_acc_eq to_not_contract.
  pose (bstate' := (bstate<|chain_state_queue := acts|>
                          <|chain_state_env := (transfer_balance from to amount bstate)|>)).
  assert (step : ChainStep bstate bstate').
  - eapply step_action with (new_acts := []); eauto.
    eapply eval_transfer. 
    + eauto. 
    + eauto.
    + exact origin_acc_eq.
    + eauto.
    + eauto.
    + eauto.
    + eauto.
    + constructor; reflexivity.
    + auto.
  - eexists bstate'.
    split; eauto.
    repeat split; eauto.
Qed.

(* Lemma showing that if an action in the queue is invalid then
    there exists a future ChainState witht the same environment
    where that action is discarded *)
Lemma discard_invalid_action : forall bstate act acts,
  reachable bstate ->
  chain_state_queue bstate = act :: acts ->
  act_is_from_account act ->
  (forall (bstate0 : Environment) (new_acts : list Action), ActionEvaluation bstate act bstate0 new_acts -> False) ->
    (exists bstate',
       reachable_through bstate bstate'
    /\ chain_state_queue bstate' = acts
    /\ EnvironmentEquiv
        bstate'
        bstate).
Proof.
  intros * reach queue act_from_account no_action_evaluation.
  pose (bstate' := (bstate<|chain_state_queue := acts|>)).
  assert (step : ChainStep bstate bstate').
  - eapply step_action_invalid; eauto.
    constructor; reflexivity.
  - eexists bstate'.
    split; eauto.
    repeat split; eauto.
Qed.

(* Lemma showing that for any permutation of the queue there
    exists a future ChainState witht the same environment
    end the queue permuted *)
Lemma permute_queue : forall bstate acts acts_permuted,
  reachable bstate ->
  chain_state_queue bstate = acts ->
  Permutation.Permutation acts acts_permuted ->
    (exists bstate',
       reachable_through bstate bstate'
    /\ chain_state_queue bstate' = acts_permuted
    /\ EnvironmentEquiv
        bstate'
        bstate).
Proof.
  intros * reach queue perm.
  pose (bstate' := (bstate<|chain_state_queue := acts_permuted|>)).
  assert (step : ChainStep bstate bstate').
  - eapply step_permute.
    + econstructor; eauto.
    + now rewrite queue.
  - eexists bstate'.
    split; eauto.
    repeat split; eauto.
Qed.

(* Lemma showing that there exists a future ChainState
    where the contract is deployed *)
Lemma deploy_contract : forall {Msg State : Type}
                              `{Serializable Msg}
                              `{Serializable State}
                               (contract : Contract Msg State)
                               bstate origin from owner caddr amount accounts acts msg cstate result,
  reachable bstate ->
  chain_state_queue bstate = {| act_from := from;
                                act_origin := origin;
                                act_body := act_deploy contract |} :: acts ->
  amount >= 0 ->
  env_account_balances bstate from >= amount ->
  address_is_contract caddr = true ->
  env_contracts bstate caddr = None ->
  env_account_owners bstate caddr = Some owner ->
  BlockchainSolanav2.process contract
        bstate
        accounts
        (Some msg) = Ok result ->
    (exists bstate' (trace : ChainTrace empty_state bstate'),
       reachable_through bstate bstate'
    /\ env_contracts bstate' caddr = Some (contract : WeakContract)
    /\ env_contract_states bstate' caddr = Some ((@serialize State _) cstate)
    /\ env_account_owners bstate' caddr = Some owner
    /\ deployment_info trace caddr = Some (build_deployment_info origin from amount)
    /\ chain_state_queue bstate' = acts
    /\ EnvironmentEquiv
        bstate'
        (set_contract_state caddr ((@serialize State _) cstate)
        (add_contract caddr contract bstate))).
Proof.
  intros * reach queue amount_nonnegative enough_balance%Z.ge_le
    caddr_is_contract not_deployed caddr_owner process_some.
  pose (bstate' := (bstate<|chain_state_queue := acts|>
                          <|chain_state_env :=
                            (set_contract_state caddr ((@serialize State _) cstate)
                            (add_contract caddr contract bstate))|>)).
  assert (step : ChainStep bstate bstate').
  - eapply step_action with (new_acts := []); eauto.
    eapply eval_deploy; eauto.
    + apply wc_process_to_process in process_some. Admitted. 
      (* rewrite <- enough_balance. apply Z.ge_le. easy.
    + apply wc_process_to_process in process_some. 
    + constructor; try reflexivity. 
  - exists bstate'.
    destruct reach as [trace].
    exists (ChainedList.snoc trace step).
    split; eauto.
    repeat split; eauto;
    try (cbn; now destruct_address_eq).
    cbn. destruct_chain_step; try congruence.
    + (destruct_action_eval; try destruct_special_body_eval);
        try congruence; cbn in *; subst; rewrite queue in queue_prev; inversion queue_prev; subst.
      * destruct_address_eq.
        (* J> TODO: fix this subgoal, the rest of this proof is working *)
        Admitted.
     (* -- rewrite deserialize_serialize.
        -- inversion new_acts_eq.
           cbn in contracts_eq.
           specialize (contracts_eq caddr).
           now rewrite address_eq_refl, address_eq_ne in contracts_eq.
      * now destruct prev_state.
    + exfalso. eapply no_eval.
      rewrite queue in queue_prev.
      inversion queue_prev.
      eapply eval_deploy; eauto.
      * now apply wc_init_to_init in init_some.
      * now constructor.
    + rewrite <- env_eq in not_deployed.
      cbn in not_deployed.
      now destruct_address_eq.
Qed. *) *)
Close Scope Z_scope.

Lemma step_reachable_through_exists : forall from mid (P : ChainState -> Prop),
  reachable_through from mid ->
  (exists to : ChainState, reachable_through mid to /\ P to) ->
  (exists to : ChainState, reachable_through from to /\ P to).
Proof.
  intros * reach [to [reach_ HP]].
  now exists to.
Qed.

End BuildUtils.

Global Hint Resolve reachable_through_refl
             reachable_through_trans'
             reachable_through_trans
             reachable_through_step
             reachable_through_reachable : core.

Global Hint Resolve reachable_through_refl
             reachable_through_trans'
             reachable_through_trans
             reachable_through_step
             reachable_through_reachable : core.

Local Ltac update_fix term1 term2 H H_orig H' :=
  match H with
  | context G [ term1 ] =>
    let x := context G [ term2 ] in
      update_fix term1 term2 x H_orig H'
  | _ =>
    let h := fresh "H" in
      assert H; [H' | clear H_orig; rename h into H_orig]
  end.

(* Replaces all occurrences of <term1> with <term2> in hypothesis <H>
    using tactic <H'> to prove the old hypothesis implies the updated *)
Local Ltac update_ term1 term2 H H' :=
  match type of H with
  | context G [ term1 ] =>
    let x := context G [ term2 ] in
      update_fix term1 term2 x H H'
  end.

Tactic Notation "update" constr(t1) "with" constr(t2) "in" hyp(H) := update_ t1 t2 H ltac:(try (cbn; easy)).
Tactic Notation "update" constr(t1) "with" constr(t2) "in" hyp(H) "by" tactic(G) := update_ t1 t2 H G.
Tactic Notation "update" constr(t2) "in" hyp(H) := let t1 := type of H in update_ t1 t2 H ltac:(try (cbn; easy)).
Tactic Notation "update" constr(t2) "in" hyp(H) "by" tactic(G) := let t1 := type of H in update_ t1 t2 H G.

Local Ltac only_on_match tac :=
  match goal with
  | |- exists bstate', reachable_through ?bstate bstate' /\ _ => tac
  | |- _ => idtac
  end.

Local Ltac update_chainstate bstate1 bstate2 :=
  match goal with
  | H : reachable bstate1 |- _ => clear H
  | H : chain_state_queue bstate1 = _ |- _ => clear H
  | H : IsValidNextBlock _ bstate1.(chain_state_env).(env_chain) |- _ => clear H
  | H : reachable_through bstate1 bstate2 |- _ =>
      update (reachable bstate2) in H
  | H : env_contracts bstate1.(chain_state_env) _ = Some _ |- _ =>
      update bstate1 with bstate2 in H by (now rewrite_environment_equiv)
  | H : env_contract_states bstate1.(chain_state_env) _ = Some _ |- _ =>
      update bstate1 with bstate2 in H by (now rewrite_environment_equiv)
  | H : context [ bstate1 ] |- _ =>
    match type of H with
    | EnvironmentEquiv _ _ => fail 1
    | _ => update bstate1 with bstate2 in H by (try (rewrite_environment_equiv;cbn; easy))
    end
  end;
  only_on_match ltac:(progress update_chainstate bstate1 bstate2).

(* Tactic for updating goal and all occurences of an old ChainState
    after adding a future ChainState to the environment. *)
Ltac update_all :=
  match goal with
  | Hreach : reachable_through ?bstate1 ?bstate2,
    Henv_eq : EnvironmentEquiv ?bstate2.(chain_state_env) (add_new_block_to_env ?header ?bstate1.(chain_state_env)) |-
    exists bstate3, reachable_through ?bstate1 bstate3 /\ _ =>
      apply (step_reachable_through_exists bstate1 bstate2); auto;
      update_chainstate bstate1 bstate2;
      only_on_match ltac:(
        clear Henv_eq;
        (try clear dependent header);
        clear dependent bstate1)
  | Hreach : reachable_through ?bstate1 ?bstate2,
    Henv_eq : EnvironmentEquiv ?bstate2.(chain_state_env) _ |-
    exists bstate3, reachable_through ?bstate1 bstate3 /\ _ =>
      apply (step_reachable_through_exists bstate1 bstate2); auto;
      update_chainstate bstate1 bstate2;
      only_on_match ltac:(
        clear Henv_eq;
        clear dependent bstate1)
  | Hreach : reachable_through ?bstate1 ?bstate2 |-
    exists bstate3, reachable_through ?bstate1 bstate3 /\ _ =>
      apply (step_reachable_through_exists bstate1 bstate2); auto;
      update (reachable bstate2) in Hreach;
      only_on_match ltac:(clear dependent bstate1)
  end.

Ltac forward_time slot_ :=
  let new_bstate := fresh "bstate" in
  let new_header := fresh "header" in
  let new_header_valid := fresh "header_valid" in
  let new_reach := fresh "reach" in
  let new_queue := fresh "queue" in
  let new_env_eq := fresh "env_eq" in
  let new_slot_hit := fresh "slot_hit" in
  match goal with
  | Hqueue : (chain_state_queue ?bstate) = [],
    Hreach : reachable ?bstate |-
    exists bstate', reachable_through ?bstate bstate' /\ _ =>
      specialize (forward_time bstate) with (slot := slot_)
        as [new_bstate [new_header [new_reach [new_header_valid [new_slot_hit [new_queue new_env_eq]]]]]]
  end.

Ltac forward_time_exact slot_ :=
  let new_bstate := fresh "bstate" in
  let new_header := fresh "header" in
  let new_header_valid := fresh "header_valid" in
  let new_reach := fresh "reach" in
  let new_queue := fresh "queue" in
  let new_env_eq := fresh "env_eq" in
  let new_slot_hit := fresh "slot_hit" in
  match goal with
  | Hqueue : (chain_state_queue ?bstate) = [],
    Hreach : reachable ?bstate |-
    exists bstate', reachable_through ?bstate bstate' /\ _ =>
      specialize (forward_time_exact bstate) with (slot := slot_)
        as [new_bstate [new_header [new_reach [new_header_valid [new_slot_hit [new_queue new_env_eq]]]]]]
  end.

Ltac add_block acts_ slot_ :=
  let new_bstate := fresh "bstate" in
  let new_reach := fresh "reach" in
  let new_queue := fresh "queue" in
  let new_env_eq := fresh "env_eq" in
  match goal with
  | Hqueue : (chain_state_queue ?bstate) = [],
    Hreach : reachable ?bstate |-
    exists bstate', reachable_through ?bstate bstate' /\ _ =>
      specialize add_block with (acts:=acts_) (slot_incr:=slot_)
        as [new_bstate [new_reach [new_queue new_env_eq]]];
      [apply Hreach | apply Hqueue| | | | | |]
  end.

Ltac evaluate_action contract_ :=
  let new_bstate := fresh "bstate" in
  let new_reach := fresh "reach" in
  let new_deployed_state := fresh "deployed_state" in
  let new_queue := fresh "queue" in
  let new_env_eq := fresh "env_eq" in
  match goal with
  | Hqueue : (chain_state_queue ?bstate) = _,
    Hreach : reachable ?bstate |-
    exists bstate', reachable_through ?bstate bstate' /\ _ =>
      specialize (evaluate_action contract_) as
        [new_bstate [new_reach [new_deployed_state [new_queue new_env_eq]]]];
      [apply Hreach | rewrite Hqueue | | | | | | ]
  end.

Ltac evaluate_transfer :=
  let new_bstate := fresh "bstate" in
  let new_reach := fresh "reach" in
  let new_queue := fresh "queue" in
  let new_env_eq := fresh "env_eq" in
  match goal with
  | Hqueue : (chain_state_queue ?bstate) = _,
    Hreach : reachable ?bstate |-
    exists bstate', reachable_through ?bstate bstate' /\ _ =>
      specialize evaluate_transfer as
        [new_bstate [new_reach [new_queue new_env_eq]]];
      [apply Hreach | rewrite Hqueue | | | | ]
  end.

Ltac discard_invalid_action :=
  let new_bstate := fresh "bstate" in
  let new_reach := fresh "reach" in
  let new_queue := fresh "queue" in
  let new_env_eq := fresh "env_eq" in
  match goal with
  | Hqueue : (chain_state_queue ?bstate) = _,
    Hreach : reachable ?bstate |-
    exists bstate', reachable_through ?bstate bstate' /\ _ =>
      specialize discard_invalid_action as
        [new_bstate [new_reach [new_queue new_env_eq]]];
      [apply Hreach | rewrite Hqueue | | | ]
  end.

Ltac empty_queue H :=
  let new_bstate := fresh "bstate" in
  let new_reach := fresh "reach" in
  let new_queue := fresh "queue" in
  let temp_H := fresh "H" in
  let temp_eval := fresh "eval" in
   match goal with
  | Hempty : emptyable (chain_state_queue ?bstate),
    Hreach : reachable ?bstate |-
    exists bstate', reachable_through ?bstate bstate' /\ _ =>
      pattern (bstate) in H;
      match type of H with
      | ?f bstate =>
        specialize (empty_queue bstate f) as
          [new_bstate [new_reach [temp_H new_queue]]];
        [apply Hreach | apply Hempty | apply H |
        clear H;
        intros ?bstate_from ?bstate_to ?act ?acts ?reach_from ?reach_to
          H ?queue_from ?queue_to [[temp_eval] | ?env_eq];
          only 1: destruct_action_eval |
        clear H; rename temp_H into H]
      end
  end.

Ltac deploy_contract contract_ :=
  let new_bstate := fresh "bstate" in
  let new_reach := fresh "reach" in
  let new_deployed_state := fresh "deployed_state" in
  let new_contract_deployed := fresh "contract_deployed" in
  let new_queue := fresh "queue" in
  let new_env_eq := fresh "env_eq" in
  let new_cstate := fresh "cstate" in
  let contract_not_deployed := fresh "trace" in
  let deploy_info := fresh "deploy_info" in
  match goal with
  | Hqueue : (chain_state_queue ?bstate) = _,
    Hreach : reachable ?bstate,
    Haddress : address_is_contract ?caddr = true,
    Hdeployed : env_contracts ?bstate.(chain_state_env) ?caddr = None |-
    exists bstate', reachable_through ?bstate bstate' /\ _ =>
      specialize (deploy_contract contract_) as
        (new_bstate & trace & new_reach & new_contract_deployed &
          new_deployed_state & deploy_info & new_queue & new_env_eq);
      [apply Hreach | rewrite Hqueue | | |
       apply Haddress | apply Hdeployed | |
       clear Haddress Hdeployed;
       match type of new_deployed_state with
       | env_contract_states _ _ = Some ((@serialize _ _) ?state) => remember state as new_cstate
       end
       ]
  end.
