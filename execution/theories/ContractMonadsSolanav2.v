From Coq Require Import FunctionalExtensionality.
From Coq Require Import List.
From ConCert.Execution Require Import BlockchainSolanav2.
From ConCert.Execution Require Import Monads.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
Import ListNotations.

Section ContractMonadsSolana.
Context `{ChainBase}.

Definition ContractReader (T : Type) : Type :=
  Chain -> SliceAccountInformation -> (Chain * SliceAccountInformation * T).

Definition run_contract_reader
           {T : Type}
           (chain : Chain) (accounts : SliceAccountInformation)
           (m : ContractReader T) : T :=
  let '(_, _, result) := m chain accounts in result.

Global Instance contract_reader_monad : Monad ContractReader :=
  {| ret _ x chain accounts := (chain, accounts, x);
     bind _ _ prev f chain accounts :=
       let '(chain, accounts, res) := prev chain accounts in
       f res chain accounts; |}. 

Global Instance contract_reader_laws : MonadLaws contract_reader_monad.
Proof.
  constructor.
  - reflexivity.
  - intros; cbn.
    repeat (apply functional_extensionality; intros).
    destruct (t _ _) as [[? ?] ?]; auto.
  - intros; cbn.
    repeat (apply functional_extensionality; intros).
    destruct (t _ _) as [[? ?] ?]; auto.
Qed.

Definition ContractProcesser (Msg State T : Type) : Type :=
  Chain -> SliceAccountInformation -> option Msg -> list ActionBody ->
  (Chain * SliceAccountInformation * option Msg * list ActionBody * option T).

Global Instance contract_processer_monad (Msg State : Type) : Monad (ContractProcesser Msg State) :=
  {| ret _ x chain accounts msg acts := (chain, accounts, msg, acts, Some x);
     bind _ _ prev f chain accounts msg acts :=
       let '(chain, accounts, msg, acts, res) := prev chain accounts msg acts in
       match res with
       | Some res => f res chain accounts msg acts
       | None => (chain, accounts, msg, acts, None)
       end; |}.

Definition run_contract_processer
           {Msg State T : Type}
           (m : ContractProcesser Msg State T)
           (chain : Chain) (accounts : SliceAccountInformation) (msg : option Msg) : option (T * list ActionBody) :=
  let '(_, _, _, acts, result) := m chain accounts msg [] in
  option_map (fun result => (result, acts)) result.

Global Arguments run_contract_processer {_ _ _} _ /.


Global Instance contract_processer_laws
       (Msg State : Type) : MonadLaws (contract_processer_monad Msg State).
Proof.
  constructor.
  - reflexivity.
  - intros; cbn.
    repeat (apply functional_extensionality; intros).
    destruct (t _ _ _ _) as [[[[[? ?] ?] ?] ?] []]; auto.
  - intros; cbn.
    repeat (apply functional_extensionality; intros).
    destruct (t _ _ _ _) as [[[[[? ?] ?] ?] ?] []]; auto.
Qed.


Global Instance contract_reader_to_processer
       {Msg State : Type} : MonadTrans (ContractProcesser Msg State) ContractReader :=
  {| lift _ (reader : ContractReader _) chain accounts msg acts :=
       let '(chain, accounts, res) := reader chain accounts in
       (chain, accounts, msg, acts, Some res) |}.

Global Instance option_to_contract_processer
       {Msg State : Type} : MonadTrans (ContractProcesser Msg State) option :=
  {| lift _ (opt : option _) chain accounts msg acts := (chain, accounts, msg, acts, opt) |}.

Definition chain_height : ContractReader nat :=
  fun chain accounts => (chain, accounts, chain_height chain).

Definition current_slot : ContractReader nat :=
  fun chain accounts => (chain, accounts, current_slot chain).

Definition finalized_height : ContractReader nat :=
  fun chain accounts => (chain, accounts, finalized_height chain).

Definition deployment_setup {Msg State : Type}
  : ContractProcesser Msg State Msg :=
  fun chain accounts msg acts => (chain, accounts, msg, acts, msg).

Definition reject_deployment {Msg State : Type}
  : ContractProcesser Msg State State :=
  fun chain accounts msg acts => (chain, accounts, msg, acts, None).

Definition accept_deployment
           {Msg State : Type} (state : State) : ContractProcesser Msg State State :=
  ret state.

Definition call_msg
           {Msg State Setup : Type} : ContractProcesser Msg State (option Msg) :=
  fun chain accounts msg acts => (chain, accounts, msg, acts, Some msg).

Definition queue
           {Msg State : Type} (act : ActionBody) : ContractProcesser Msg State unit :=
  fun chain accounts msg acts => (chain, accounts, msg, acts ++ [act], Some tt).

Definition reject_call
           {Msg State : Type} : ContractProcesser Msg State unit :=
  fun chain accounts msg acts => (chain, accounts, msg, [], None).

Definition accept_call
           {Msg State : Type} (new_state : State) : ContractProcesser Msg State unit :=
  fun chain accounts msg acts => (chain, accounts, msg, acts, Some tt).

Definition build_contract
           {Msg State : Type}
           `{Serializable Msg} `{Serializable State}
           (process : ContractProcesser Msg State unit) : Contract Msg State :=
  {| process := (run_contract_processer process); |}.

End ContractMonadsSolana.
