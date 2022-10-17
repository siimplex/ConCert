(** * Counter - Solana Version *)

From Coq Require Import Morphisms.
From Coq Require Import ZArith.
From Coq Require Import List.
From Coq Require Import Basics.
From ConCert.Utils Require Import Automation.
From ConCert.Execution Require Import Extras.
From ConCert.Execution Require Import Monads.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import ProgramError.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import BlockchainSolanav2.
From ConCert.Utils Require Import RecordUpdate.

Import ListNotations.
Import RecordSetNotations.

Open Scope Z.

(** ** Definition *)
Section CounterSolana.

  (** Enabling recursors for records allows for deriving [Serializable] instances. *)
  Set Nonrecursive Elimination Schemes.

  (** The definitions in this section are generalized over the [ChainBase] that specifies the type of addresses and which properties such a type must have *)
  Context {BaseTypes : ChainBase}.
  Context {AccountGetters : AccountGetters}.
  Context {HelperTypes : ChainHelpers}.

  (** The state is a current counter value and the owner's address *)
  Record State :=
    build_state { 
      count : Z ;
      active : bool ;
      owner : Address 
    }.

  MetaCoq Run (make_setters State).

  (** The contract has 3 kinds of messages: initialize, increment or decrement by some number *)
  Inductive ContractInstruction :=
  | Init (i : Z)
  | Inc (i : Z)
  | Dec (i : Z).

   (** Deriving the [Serializable] instances for the state and for the messages *)
  Global Instance State_serializable : Serializable State :=
    Derive Serializable State_rect<build_state>.

  Global Instance ContractInstruction_serializable : Serializable ContractInstruction :=
    Derive Serializable ContractInstruction_rect<Init, Inc, Dec>.

(** Since a contract is essentially a state transition function, we isolate
      the functionality corresponding to each kind of message into step functions *)
  Definition counter_init (owner_address : Address) (init_value : Z)
    : State :=
     {| count := init_value;
        active := false;
         owner := owner_address |}.
    (* let index:= 0 in
    do counter_owner_account <- next_account accounts index; 
    let index := 1 in
    do counter_account <- next_account accounts index;
        
    do counter_account_deser_state <- deser_data_account State counter_account;
    
    let initialized_state := (build_state init_value true (get_account_address counter_owner_account)) in
    ser_data_account initialized_state counter_account *)

 Definition increment (n : Z) (st : State) : State :=
    {| count := st.(count) + n ;
       active := true ;
       owner := st.(owner) |}.

  Definition decrement (n : Z) (st : State) : State :=
    {| count := st.(count) - n ;
       active := true ;
       owner := st.(owner) |}.

  (** The main functionality of the contract.
      Dispatches on a message, validates the input and calls the step functions *)
  Definition counter (accounts : SliceAccountInformation) (inst : ContractInstruction) : result unit ProgramError :=
    let index := 0 in 
    do counter_account <- next_account accounts index;
    let index := 1 in 
    do counter_owner_account <- next_account accounts index;

    match  deser_data_account State counter_account with 
    | Ok state =>
       let new_state := match inst with
                          | Init i => Some (counter_init (get_account_owner_address counter_owner_account) i)
                          | Inc i  => if (0 <? i) then Some (increment i state) else None
                          | Dec i  => if (0 <? i) then Some (decrement i state) else None
                        end in
       match new_state with
       | Some st => 
         do ser_data_account st counter_account;
         Ok tt
       | None => Err InvalidAccountData
       end
    | Err e => Err e
     end.
  
(** The "entry point" of the contract. Dispatches on a message and calls [counter]. *)
  Definition counter_process (chain : Chain) (accounts : SliceAccountInformation) (inst : option ContractInstruction) 
    : result unit ProgramError :=
     match inst with
     | Some m => counter accounts m
     | None => Err InvalidInstructionData
     end.

  (** The counter contract *)
  Definition counter_contract : Contract ContractInstruction State :=
    build_contract counter_process.

End CounterSolana.
(* 
(** ** Functional properties *)
Section FunctionalProperties.

  Import Lia.

  Context {BaseTypes : ChainBase}.
  Context {AccountGetters : AccountGetters}.
  Context {HelperTypes : ChainHelpers}.
  
  Context {Env : Environment}.

  (** *** Specification *)

  (** If the counter call succeeds and returns [next_state] then,
      depending on a message, it either increments or decrements
      by the number sent in the corresponding message *)
  Lemma counter_correct {accounts other_accs counter_acc prev_state next_state inst} :
    accounts = counter_acc :: other_accs ->
    contract_state Env (account_address counter_acc) = Some prev_state ->
    counter accounts inst = Ok tt ->
    contract_state Env (account_address counter_acc) = Some next_state ->
    match inst with
    | Inc n => prev_state.(count) < next_state.(count)
               /\ next_state.(count) = prev_state.(count) + n
    | Dec n => prev_state.(count) > next_state.(count)
               /\ next_state.(count) = prev_state.(count) - n
    | Init n => next_state.(count) = n
    end.
  Proof. 
    intros account_list counter_prev process_ok counter_next.
    all : destruct inst;cbn in *;unfold increment,decrement in *.
(*     + cbn in *. apply account_state_updated_after_process. *)
    all: swap 1 2.
    + destruct (0 <? i) eqn:Hz. destruct process_ok; split; auto.
(*     all : destruct (0 <? i) eqn:Hz;inversion H;cbn in *. *)
      - inversion.
    all : rewrite Z.ltb_lt in *;split;auto;lia.
  Qed.

(* account_state_updated_after_process *)
End FunctionalProperties.

(** ** Safety properties *)

(** Safety properties are stated for all states reachable from the initial state. *)
Section SafetyProperties.

Context {BaseTypes : ChainBase}.

(** Converting a message to a number. Note that the decrements are negative. *)
Definition opt_msg_to_number (msg : option Msg) :=
  match msg with
  | Some (Inc i) => i
  | Some (Dec i) => - i
  | _ => 0
  end.

Open Scope program_scope.

Import Lia.

Lemma receive_produces_no_calls {chain ctx cstate msg new_cstate} acts :
  counter_receive chain ctx cstate msg = Some (new_cstate, acts) ->
  acts = [].
Proof.
  intros receive_some.
  destruct msg as [msg | ];try discriminate; cbn in *.
  destruct (counter _ _) as [[? ?] | ] eqn:Hreceive;try inversion receive_some;subst; cbn in *;auto.
Qed.

(** The sum of all increment/decrement messages sent to the contract. *)
Definition sum_inc_dec (l : list (ContractCallInfo Msg)) :=
  sumZ (opt_msg_to_number ∘ call_msg) l.

(** We state the following safety property: for all reachable states (i.e. at any point in time after deployment), the state of the counter is equal to the initial value plus the sum of all successful increment and decrement messages sent to the contract.

 We use a special induction principle [contract_induction] that takes care of the boilerplate and exposes the cases in the convenient form. The [tag] variable in the context contains a hint what is expected to be done in each case. *)
Lemma counter_safe block_state counter_addr
      (trace : ChainTrace empty_state block_state) :
  env_contracts block_state counter_addr = Some (counter_contract : WeakContract) ->
  exists cstate call_info deploy_info,
    incoming_calls Msg trace counter_addr = Some call_info
    /\ contract_state block_state counter_addr = Some cstate
    /\ deployment_info _ trace counter_addr = Some deploy_info
    /\ let init_val := deploy_info.(deployment_setup) in
      init_val + sum_inc_dec call_info = cstate.(count).
Proof.
  contract_induction; intros; cbn in *; auto.
  + (* deployment *)
    inversion init_some;subst;clear init_some;cbn in *. lia.
  + (* contract call *)
    destruct msg as [msg|];try discriminate;cbn in *.
    destruct (counter _ _) as [cstate|] eqn:counter_some;inversion receive_some;subst.
    (* NOTE: we use the functional correctness here *)
    specialize (counter_correct counter_some) as Cspec.
    destruct msg;intuition;unfold sum_inc_dec in *;lia.
  + (* contract self-call *)
    (* NOTE: we know that the self-call is not possible because [counter_receive]
       always returns an empty list of actions. We instantiate the [CallFacts]
       predicate with the assumption that the from-address is not equal to the
       contract address. We will be asked to prove this goal later. *)
    instantiate (CallFacts := fun _ ctx _ _ => ctx_from ctx <> ctx_contract_address ctx);
      subst CallFacts; cbn in *; congruence.
  + (* we asked to prove additional assumptions we might have made.
     Since we instantiated only [CallFacts], we instantiate other assumptions
     with a trivial proposition *)
    instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
    instantiate (DeployFacts := fun _ _ => True).
    unset_all;subst;cbn in *.
    destruct_chain_step; auto.
    destruct_action_eval; auto.
    cbn. intros cstate Hc Hstate.
    (* we use the fact that [counter_receive] doesn't return any actions *)
    assert ((outgoing_acts bstate_from to_addr) = []) as Hempty.
    { apply lift_outgoing_acts_nil with (contract := counter_contract);eauto.
      intros. eapply (receive_produces_no_calls (chain:=chain) (ctx:=ctx));eauto. apply H. }
    unfold outgoing_acts in *. rewrite queue_prev in *.
    subst act;cbn in Hempty. 
    now destruct_address_eq.
Qed.
End SafetyProperties.

 *)