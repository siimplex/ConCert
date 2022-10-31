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
  Lemma counter_correct {accounts other_accs counter_acc} (inst : ContractInstruction) (prev_state next_state : State) :
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
    destruct inst.
    + cbn in *. destruct (env_contract_states Env (account_address counter_acc)).
      - destruct (next_account accounts 0); auto.
        * destruct (next_account accounts 1); auto.
          ** destruct (deser_data_account State t); auto.
    Admitted.
(*   Qed. *)
End FunctionalProperties.
