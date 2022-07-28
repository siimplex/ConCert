(** * Counter - Solana Version *)

From Coq Require Import Morphisms.
From Coq Require Import ZArith.
From Coq Require Import List.
From Coq Require Import Basics.
From ConCert.Utils Require Import Automation.
From ConCert.Execution Require Import Extras.
From ConCert.Execution Require Import Monads.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import BlockchainSolanav2.
From ConCert.Utils Require Import RecordUpdate.

Import ListNotations.
Import BlockchainHelpers.
Import RecordSetNotations.

Open Scope Z.

(** ** Definition *)
Section CounterSolana.

  (** Enabling recursors for records allows for deriving [Serializable] instances. *)
  Set Nonrecursive Elimination Schemes.

  (** The definitions in this section are generalized over the [ChainBase] that specifies the type of addresses and which properties such a type must have *)
  Context {BaseTypes : ChainBase}.

(*   Parameter NullAccount : AccountInformation. *)

  (** The state is a current counter value and the owner's address *)
  Record State :=
    build_state { 
      count : Z ;
      active : bool ;
      owner : Address 
    }.

(*   Inductive CounterError :=
  | Error1
  | Error2 
  | Error3.  *)

  (** The contract has 3 kinds of messages: initialize, increment or decrement by some number *)
  Inductive Msg :=
  | Init (i : Z)
  | Inc (i : Z)
  | Dec (i : Z).

   (** Deriving the [Serializable] instances for the state and for the messages *)
  Global Instance State_serializable : Serializable State :=
    Derive Serializable State_rect<build_state>.

  Global Instance Msg_serializable : Serializable Msg :=
    Derive Serializable Msg_rect<Init, Inc, Dec>.

(*   Global Instance CounterError_serializable : Serializable CounterError :=
    Derive Serializable CounterError_rect<Error1, Error2, Error3>. *)
(** Since a contract is essentially a state transition function, we isolate
      the functionality corresponding to each kind of message into step functions *)
  Definition counter_init (accounts : list AccountInformation) (init_value : Z)
    : result unit ProgramError :=
    let it := it_from_list accounts in 
    do counter_owner_account <- it_next it; 
    do counter_account <- it_next it;
    
    do counter_account_deserialize_state <- deserialize_data State (account_state counter_account);
(*     let counter_account_deserialize_state := ((@deserialize State _) (account_state counter_account)) in   *)
    
    let initialized_state := (build_state init_value true (account_address counter_owner_account)) in
    do serialize_data initialized_state counter_account;
(*     let counter_account := counter_account<|account_state := ((@serialize State _) initialized_state)|> in  *)
    
    ret tt. 


(*   (** Since a contract is essentially a state transition function, we isolate
      the functionality corresponding to each kind of message into step functions *)
  Definition counter_init (accounts : list AccountInformation) (init_value : Z)
    : result unit ProgramError :=
    let counter_owner_account := (next_account 0 accounts NullAccount) in
    do check_account counter_owner_account NullAccount;
    let counter_account := (next_account 1 accounts NullAccount) in
    do check_account counter_account NullAccount;
    
    let counter_account_deserialize_state := ((@deserialize State _) (account_state counter_account)) in  
    
    let initialized_state := (build_state init_value true (account_address counter_owner_account)) in
    let counter_account := counter_account<|account_state := ((@serialize State _) initialized_state)|> in 
    
    Ok tt.  *)

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
  Definition counter (accounts : list AccountInformation) (msg : Msg) : result unit ProgramError :=
    let it := it_from_list accounts in 
    do counter_account <- it_next it;

    let counter_account_deserialize_state := deserialize_data State (account_state counter_account) in
(*     let counter_account_deserialize_state := ((@deserialize State _) (account_state counter_account)) in   *)

    match counter_account_deserialize_state with 
    | Ok state =>
       let new_state := match msg with
                          | Inc i => if (0 <? i) then Some (increment i state) else None
                          | Dec i => if (0 <? i) then Some (decrement i state) else None
                          | _     => Some state
                        end in
       match new_state with
       | Some st => 
         do serialize_data st counter_account;
(*          let counter_account := counter_account<|account_state := ((@serialize State _) st)|> in  *)
         Ok tt
       | None => Err InvalidAccountData
       end
    | Err _ =>
       match msg with
       | Init i => counter_init accounts i
       | _      => Err InvalidInstructionData
       end
    end.


(*   (** The main functionality of the contract.
      Dispatches on a message, validates the input and calls the step functions *)
  Definition counter (accounts : list AccountInformation) (msg : Msg) : result unit ProgramError :=
    let counter_account := (next_account 0 accounts NullAccount) in
    do check_account counter_account NullAccount;

    let counter_account_deserialize_state := ((@deserialize State _) (account_state counter_account)) in  
    match counter_account_deserialize_state with 
    | Some state =>
       let new_state := match msg with
                          | Inc i => if (0 <? i) then Some (increment i state) else None
                          | Dec i => if (0 <? i) then Some (decrement i state) else None
                          | _     => Some state
                        end in
       match new_state with
       | Some st => 
         let counter_account := counter_account<|account_state := ((@serialize State _) st)|> in 
         Ok tt
       | None => Err InvalidAccountData
       end
    | None =>
       match msg with
       | Init i => counter_init accounts i
       | _      => Err InvalidInstructionData
       end
    end.
 *)
  (** The "entry point" of the contract. Dispatches on a message and calls [counter]. *)
  Definition counter_process (chain : Chain) (accounts : list AccountInformation) (msg : option Msg) 
    : result unit ProgramError :=
     match msg with
     | Some m => counter accounts m
     | None => Err InvalidInstructionData
     end.

  (** The counter contract *)
  Definition counter_contract : Contract Msg State :=
    build_contract counter_process.

End CounterSolana.
(* 
(** ** Functional properties *)
Section FunctionalProperties.

  Import Lia.

  Context {BaseTypes : ChainBase}.

  (** *** Specification *)

  (** If the counter call succeeds and returns [next_state] then,
      depending on a message, it either increments or decrements
      by the number sent in the corresponding message *)
  Lemma counter_correct {prev_state next_state msg} :
  counter prev_state msg = Some next_state ->
  match msg with
  | Inc n => prev_state.(count) < next_state.(count)
             /\ next_state.(count) = prev_state.(count) + n
  | Dec n => prev_state.(count) > next_state.(count)
             /\ next_state.(count) = prev_state.(count) - n
  end.
  Proof.
    intros H.
    all : destruct msg;cbn in *;unfold increment,decrement in *.
    all : destruct (0 <? i) eqn:Hz;inversion H;cbn in *.
    all : rewrite Z.ltb_lt in *;split;auto;lia.
  Qed.

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
