From Coq Require Import FunctionalExtensionality.
From Coq Require Import List.
From ConCert.Execution Require Import BlockchainSolana.
From ConCert.Execution Require Import Monads.
From ConCert.Execution Require Import Serializable.
Import ListNotations.

Section ContractMonadsSolana.
Context `{ChainBase}.

Definition ContractReader (T : Type) : Type :=
  Chain -> list AccountInfo -> (Chain * list AccountInfo * T).

Definition run_contract_reader
           {T : Type}
           (chain : Chain) (accounts : list AccountInfo)
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

Definition ContractProcesser (Msg State Setup T : Type) : Type :=
  Chain -> list AccountInfo -> option State -> option Msg -> list ActionBody ->
  (Chain * list AccountInfo * option State * option Msg * list ActionBody * option T).

Global Instance contract_processer_monad (Msg State Setup : Type) : Monad (ContractProcesser Msg State Setup) :=
  {| ret _ x chain accounts state msg acts := (chain, accounts, state, msg, acts, Some x);
     bind _ _ prev f chain accounts state msg acts :=
       let '(chain, accounts, state, msg, acts, res) := prev chain accounts state msg acts in
       match res with
       | Some res => f res chain accounts state msg acts
       | None => (chain, accounts, state, msg, acts, None)
       end; |}.

Definition run_contract_processer
           {Msg State Setup T : Type}
           (m : ContractProcesser Msg State Setup T)
           (chain : Chain) (accounts : list AccountInfo) (state : option State) (msg : option Msg) : option (T * list ActionBody) :=
  let '(_, _, _, _, acts, result) := m chain accounts state msg [] in
  option_map (fun result => (result, acts)) result.

Global Arguments run_contract_processer {_ _ _ _} _ /.


Global Instance contract_processer_laws
       (Msg State Setup : Type) : MonadLaws (contract_processer_monad Msg State Setup).
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
       {Msg State Setup : Type} : MonadTrans (ContractProcesser Msg State Setup) ContractReader :=
  {| lift _ (reader : ContractReader _) chain accounts state msg acts :=
       let '(chain, accounts, res) := reader chain accounts in
       (chain, accounts, state, msg, acts, Some res) |}.

Global Instance option_to_contract_processer
       {Msg State Setup : Type} : MonadTrans (ContractProcesser Msg State Setup) option :=
  {| lift _ (opt : option _) chain accounts state msg acts := (chain, accounts, state, msg, acts, opt) |}.

Definition chain_height : ContractReader nat :=
  fun chain accounts => (chain, accounts, chain_height chain).

Definition current_slot : ContractReader nat :=
  fun chain accounts => (chain, accounts, current_slot chain).

Definition finalized_height : ContractReader nat :=
  fun chain accounts => (chain, accounts, finalized_height chain).

Definition deployment_setup {Msg State Setup : Type}
  : ContractProcesser Msg State Setup Msg :=
  fun chain accounts state msg acts => (chain, accounts, state, msg, acts, msg).

Definition reject_deployment {Msg State Setup : Type}
  : ContractProcesser Msg State Setup State :=
  fun chain accounts state msg acts => (chain, accounts, state, msg, acts, None).

Definition accept_deployment
           {Msg State Setup : Type} (state : State) : ContractProcesser Msg State Setup State :=
  ret state.

Definition call_msg
           {Msg State Setup : Type} : ContractProcesser Msg State Setup (option Msg) :=
  fun chain accounts state msg acts => (chain, accounts, state, msg, acts, Some msg).

Definition my_state
           {Msg State Setup : Type} : ContractProcesser Msg State State State :=
  fun chain accounts state msg acts => (chain, accounts, state, msg, acts, state).

Definition queue
           {Msg State Setup : Type} (act : ActionBody) : ContractProcesser Msg State Setup unit :=
  fun chain accounts state msg acts => (chain, accounts, state, msg, acts ++ [act], Some tt).

Definition reject_call
           {Msg State Setup : Type} : ContractProcesser Msg State Setup State :=
  fun chain accounts state msg acts => (chain, accounts, state, msg, [], None).

Definition accept_call
           {Msg State Setup : Type} (new_state : State) : ContractProcesser Msg State Setup State :=
  fun chain accounts state msg acts => (chain, accounts, state, msg, acts, Some new_state).

Definition build_contract
           {Msg State Setup : Type}
           `{Serializable Msg} `{Serializable State} `{Serializable Setup}
           (process : ContractProcesser Msg State Setup State) : Contract Msg State Setup :=
  {| process := (run_contract_processer process); |}.

End ContractMonadsSolana.
