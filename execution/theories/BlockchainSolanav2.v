From Coq Require Import ZArith.
From Coq Require Import List.
From Coq Require Import Psatz.
From Coq Require Import Permutation.
From Coq Require Import Morphisms.
From ConCert.Execution Require Import ChainedList.
From ConCert.Execution Require Import Extras.
From ConCert.Execution Require Import Monads.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import ProgramError.
From ConCert.Execution Require Import Serializable.
From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import RecordUpdate.

Import ListNotations.

Definition Amount := Z.
Bind Scope Z_scope with Amount.

Class ChainBase :=
  build_chain_base {
    Address : Type;
    address_eqb : Address -> Address -> bool;
    address_eqb_spec :
      forall (a b : Address), Bool.reflect (a = b) (address_eqb a b);
    address_eqdec :> stdpp.base.EqDecision Address;
    address_countable :> countable.Countable Address;
    address_serializable :> Serializable Address; 
    address_is_contract : Address -> bool;
  }.

Global Opaque Address address_eqb address_eqb_spec
       address_eqdec address_countable address_serializable.

Delimit Scope address_scope with address.
Bind Scope address_scope with Address.
Infix "=?" := address_eqb (at level 70) : address_scope.

Lemma address_eq_refl `{ChainBase} x :
  address_eqb x x = true.
Proof. destruct (address_eqb_spec x x); auto; congruence. Qed.

Lemma address_eq_ne `{ChainBase} x y :
  x <> y ->
  address_eqb x y = false.
Proof. destruct (address_eqb_spec x y) as [->|]; tauto. Qed.

Lemma address_eq_sym `{ChainBase} x y :
  address_eqb x y = address_eqb y x.
Proof.
  destruct (address_eqb_spec x y) as [->|].
  - now rewrite address_eq_refl.
  - rewrite address_eq_ne; auto.
Qed.

Global Ltac destruct_address_eq :=
  repeat
    match goal with
    | [H: context[address_eqb ?a ?b] |- _] =>
      try rewrite (address_eq_sym b a) in *; destruct (address_eqb_spec a b)
    | [|- context[address_eqb ?a ?b]] =>
      try rewrite (address_eq_sym b a) in *; destruct (address_eqb_spec a b)
    end.



Section Blockchain.
Context {Base : ChainBase}.

(* This represents the view of the blockchain that a contract
can access and interact with. *)
(* Finalization is a Concordium blockchain concept but the root in Solana is identical *)
Record Chain :=
  build_chain {
    chain_height : nat;
    current_slot : nat;
    finalized_height : nat;
  }.



Record AccountInformation :=
  build_account {  
    account_address : Address;       (* Account address *)
    account_is_signer : bool;        (* Has the account signed the transaction *)
    account_is_writable : bool;      (* Can the account be written to *)
    account_balance : Amount;        (* Account balance *)
    account_state : SerializedValue; (* Account data *)
    account_owner_address : Address; (* Account owner address *)
    account_is_executable : bool;    (* Is the account a program *)
  }.

MetaCoq Run (make_setters AccountInformation).

Print Bool.reflect.

Class AccountGetters :=
  build_account_getters {
    get_account_address : AccountInformation -> Address;       (* Account address *)
    get_account_address_spec : forall (acc : AccountInformation),
            get_account_address acc = account_address acc;
    get_account_is_writable : AccountInformation -> bool;      (* Can the account be written to *)
    get_account_is_writable_spec : forall (acc : AccountInformation),
            get_account_is_writable acc = account_is_writable acc;
    get_account_is_signer : AccountInformation -> bool;        (* Has the account signed the transaction *)
    get_account_is_signer_spec : forall (acc : AccountInformation),
            get_account_is_signer acc = account_is_signer acc;
    get_account_balance : AccountInformation -> Amount;        (* Account balance *)
    get_account_balance_spec : forall (acc : AccountInformation),
            get_account_balance acc = account_balance acc;
    get_account_state : AccountInformation -> SerializedValue; (* Account data *)
    get_account_state_spec : forall (acc : AccountInformation),
            get_account_state acc = account_state acc;
    get_account_owner_address : AccountInformation -> Address; (* Account owner address *)
    get_account_owner_address_spec : forall (acc : AccountInformation),
            get_account_owner_address acc = account_owner_address acc;
    get_account_is_executable : AccountInformation -> bool;    (* Is the account a program *)
    get_account_is_executable_spec : forall (acc : AccountInformation),
            get_account_is_executable acc = account_is_executable acc;
  }.

Global Opaque get_account_address get_account_state get_account_balance get_account_owner_address
              get_account_is_signer get_account_is_writable get_account_is_executable.

Lemma get_account_address_correct `{AccountGetters} acc : 
  account_address acc = get_account_address acc.
Proof. destruct (get_account_address_spec acc); auto. Qed.

Lemma get_account_state_correct `{AccountGetters} acc : 
  account_state acc = get_account_state acc.
Proof. destruct (get_account_state_spec acc); auto. Qed.

Lemma get_account_balance_correct `{AccountGetters} acc : 
  account_balance acc = get_account_balance acc.
Proof. destruct (get_account_balance_spec acc); auto. Qed.

Lemma get_account_owner_address_correct `{AccountGetters} acc : 
  account_owner_address acc = get_account_owner_address acc.
Proof.
  destruct (get_account_owner_address_spec acc); auto.
 Qed. 

Lemma get_account_is_signer_correct `{AccountGetters} acc : 
  account_is_signer acc = get_account_is_signer acc.
Proof. destruct (get_account_is_signer_spec acc); auto. Qed.

Lemma get_account_is_writable_correct `{AccountGetters} acc : 
  account_is_writable acc = get_account_is_writable acc.
Proof. destruct (get_account_is_writable_spec acc); auto. Qed.

Lemma get_account_is_executable_correct `{AccountGetters} acc :
  account_is_executable acc = get_account_is_executable acc.
Proof. destruct (get_account_is_executable_spec acc); auto. Qed.

Definition SliceAccountInformation := list AccountInformation.
Global Opaque SliceAccountInformation.

Inductive SpecialCallBody :=
       | transfer_ownership (old_owner : AccountInformation) (account : AccountInformation) (new_owner : AccountInformation)
       | check_rent_exempt (account : AccountInformation)
       | check_token_owner (account : AccountInformation).

(* Operations that a contract can return or that a user can use
to interact with a chain. *)
(* Currently WeakContract is described as a single function, in the future it may be needed to add more *)
Inductive ActionBody :=
  | act_transfer (* (from : Address) *) (to : Address) (amount : Amount)
  | act_call (to : Address) (msg : SerializedValue) 
  | act_deploy (c : WeakContract)
  | act_special_call (to : Address) (body : SpecialCallBody)
(*     with SpecialCallBody :=
       | transfer_ownership (old_owner : AccountInformation) (account : AccountInformation) (new_owner : AccountInformation)
       | check_rent_exempt (account : AccountInformation)
       | check_token_owner (account : AccountInformation) *)
    with WeakContract :=
       | build_weak_contract
           (process :
              Chain ->
              SliceAccountInformation -> (* accounts *)
              option SerializedValue -> (* message *)
              result unit ProgramError).

Definition act_body_amount (ab : ActionBody) : Z :=
  match ab with
  | act_transfer (* _ *) _ amount => amount
  | act_call _ _ 
  | act_deploy _
  | act_special_call _ _ => 0
  end.

Definition wc_process (wc : WeakContract) :=
  let (p) := wc in p.

Record Action :=
  build_act {
    act_origin : Address;
    act_from : Address;
    act_body : ActionBody;
  }.

Definition act_amount (a : Action) := act_body_amount (act_body a).

(* Represents a strongly-typed contract. This is what user's will primarily
use and interact with when they want deployment. We keep the weak contract
only "internally" for blockchains, while any strongly-typed contract can
be converted to and from *)

Record Contract
      (Msg State : Type)
      `{Serializable Msg} 
      `{Serializable State} :=
  build_contract {
    process :
      Chain ->
      SliceAccountInformation ->
      option Msg ->
      result unit ProgramError;
  }.  

Global Arguments process {_ _ _ _}.
Global Arguments build_contract {_ _ _ _}.

(* Set Typeclasses Debug Verbosity 10. *)

Program Definition contract_to_weak_contract
          {Msg State : Type}
          `{Serializable Msg}
          `{Serializable State}
          (c : Contract Msg State) : WeakContract :=
      let weak_proc chain accounts ser_msg_opt :=
        match ser_msg_opt with
          | Some ser_msg =>
            do msg <- result_of_option (deserialize ser_msg) InvalidInstructionData;
            do res <- c.(process) chain accounts (Some msg);
            Ok res
          | None =>
            do res <- c.(process) chain accounts None;
            Ok res
          end in
      build_weak_contract weak_proc.

Coercion contract_to_weak_contract : Contract >-> WeakContract.

(* Deploy a strongly typed contract with some amount and setup *)
Definition create_deployment
          {Msg State : Type}
          `{Serializable Msg}
          `{Serializable State}
          (contract : Contract Msg State) : ActionBody :=
  act_deploy contract.


(* The contract interface is the main mechanism allowing a deployed
contract to interact with another deployed contract. This hides
the ugly details of everything being SerializedValue away from contracts. *)
Record ContractInterface {Msg : Type} :=
  build_contract_interface {
    (* The address of the contract being interfaced with *)
    contract_address : Address;
    (* Make an action sending money and optionally a message to the contract *)
    send : (* Address ->  *)Amount -> option Msg -> ActionBody; (*TODO : added address, should think more about this*)
  }.

Global Arguments ContractInterface _ : clear implicits.

Definition get_contract_interface
          (chain : Chain) (addr : Address)
          (Msg : Type) `{Serializable Msg}
  : option (ContractInterface Msg) :=
  let ifc_send (* from *) amount msg :=
      match msg with
      | None => act_transfer (* from *) addr amount
      | Some msg => act_call addr (serialize msg)
      end in
  Some {| contract_address := addr; send := ifc_send; |}.

Inductive WrappedActionBody :=
  | wact_transfer (from : AccountInformation) (to : AccountInformation) (amount : Amount)
  | wact_call (to : AccountInformation) (msg : SerializedValue) 
  | wact_deploy (c : WeakContract)
  | wact_special_call (to : AccountInformation) (body : SpecialCallBody).

Definition WrappedActionBody_to_ActionBody (wact : WrappedActionBody) : ActionBody :=
  match wact with
  | wact_transfer from to amount => act_transfer (* (account_address from) *) (account_address to) amount
  | wact_call to msg             => act_call (account_address to) msg 
  | wact_deploy contract         => act_deploy contract
  | wact_special_call to body    => act_special_call (account_address to) body
  end.

(* TODO: Lemma for WrappedActionBody and Action because of the from clause *)


Section Semantics.
MetaCoq Run (make_setters Chain).

Definition add_balance (addr : Address) (amount : Amount) (map : Address -> Amount) :
  Address -> Amount :=
  fun a => if (a =? addr)%address
           then (amount + map a)%Z
           else map a.

Global Arguments add_balance _ _ _ /.

Definition set_chain_contract_state
           (addr : Address) (state : SerializedValue)
           (map : Address -> option SerializedValue)
  : Address -> option SerializedValue :=
  fun a => if (a =? addr)%address
           then Some state
           else map a.

Definition set_chain_account_owner
           (addr : Address) (owner : Address)
           (map : Address -> option Address) 
  : Address -> option Address :=
  fun a => if (a =? addr)%address
           then Some owner
           else map a.

Record Environment :=
  build_env {
    env_chain :> Chain;
    env_account_balances : Address -> Amount;
    env_account_owners : Address -> option Address;
    env_contracts : Address -> option WeakContract;
    env_contract_states : Address -> option SerializedValue;
  }.

(* Two environments are equivalent if they are extensionally equal *)
Record EnvironmentEquiv (e1 e2 : Environment) : Prop :=
  build_env_equiv {
    chain_eq : env_chain e1 = env_chain e2;
    account_balances_eq : forall a, env_account_balances e1 a = env_account_balances e2 a;
    account_owners_eq : forall a, env_account_owners e1 a = env_account_owners e2 a;
    contracts_eq : forall a, env_contracts e1 a = env_contracts e2 a;
    contract_states_eq : forall addr, env_contract_states e1 addr = env_contract_states e2 addr;
  }.

(* Strongly typed version of contract state *)
Definition contract_state
           {A : Type} `{Serializable A}
           (env : Environment) (addr : Address) : option A :=
  env_contract_states env addr >>= deserialize.

Global Program Instance environment_equiv_equivalence : Equivalence EnvironmentEquiv.
Next Obligation.
  apply build_env_equiv; reflexivity.
Qed.
Next Obligation.
  destruct H; apply build_env_equiv; now symmetry.
Qed.
Next Obligation.
  destruct H, H0; apply build_env_equiv; try congruence.
Qed.

Global Instance environment_equiv_env_account_balances_proper :
  Proper (EnvironmentEquiv ==> eq ==> eq) env_account_balances.
Proof. repeat intro; subst; apply account_balances_eq; assumption. Qed.

Global Instance environment_equiv_env_account_owners_proper :
  Proper (EnvironmentEquiv ==> eq ==> eq) env_account_owners.
Proof. repeat intro; subst; apply account_owners_eq; assumption. Qed.

Global Instance environment_equiv_env_contracts_proper :
  Proper (EnvironmentEquiv ==> eq ==> eq) env_contracts.
Proof. repeat intro; subst; apply contracts_eq; assumption. Qed.

Global Instance environment_equiv_env_contract_states_proper :
  Proper (EnvironmentEquiv ==> eq ==> eq) env_contract_states.
Proof. repeat intro; subst; apply contract_states_eq; assumption. Qed.

Global Instance environment_equiv_env_chain_equiv_proper :
  Proper (EnvironmentEquiv ==> eq) env_chain.
Proof. repeat intro; apply chain_eq; assumption. Qed.

Global Instance environment_equiv_contract_state_proper
  {A : Type} `{Serializable A} :
  Proper (EnvironmentEquiv ==> eq ==> (@eq (option A))) contract_state.
Proof.
  intros ? ? env_eq ? ? ?.
  subst.
  unfold contract_state.
  now rewrite env_eq.
Qed.

MetaCoq Run (make_setters Environment).

Definition transfer_balance (from to : Address) (amount : Amount) (env : Environment) :=
  env<|env_account_balances ::= add_balance to amount|>
     <|env_account_balances ::= add_balance from (-amount)|>.

Definition add_contract (addr : Address) (contract : WeakContract) (env : Environment)
  : Environment :=
  env<|env_contracts ::=
    fun f a =>
      if (a =? addr)%address
      then Some contract
      else f a|>.

Definition set_account_owner
           (addr : Address) (new_owner : Address) (env : Environment) :=
  env<|env_account_owners ::= set_chain_account_owner addr new_owner|>.

Definition set_contract_state
           (addr : Address) (state : SerializedValue) (env : Environment) :=
  env<|env_contract_states ::= set_chain_contract_state addr state|>.
  

(* set_chain_contract_state updates a map (function) by returning a
   new map (function).  If this function is immediately applied to a
   key, then unfold it. *)

Global Arguments set_chain_contract_state _ _ _ /.
Global Arguments set_account_owner _ _ _ /.

Ltac rewrite_environment_equiv :=
  match goal with
  | [H: EnvironmentEquiv _ _ |- _] => try rewrite H in *
  end.

Ltac solve_proper :=
  apply build_env_equiv;
  cbn;
  repeat intro;
  repeat rewrite_environment_equiv;
  auto.

Global Instance transfer_balance_proper :
  Proper (eq ==> eq ==> eq ==> EnvironmentEquiv ==> EnvironmentEquiv) transfer_balance.
Proof.
  repeat intro; subst.
  unfold transfer_balance, add_balance.
  solve_proper.
Qed.

Global Instance add_contract_proper :
  Proper (eq ==> eq ==> EnvironmentEquiv ==> EnvironmentEquiv) add_contract.
Proof.
  repeat intro; subst.
  unfold add_contract.
  solve_proper.
Qed.

Global Instance set_contract_state_proper :
  Proper (eq ==> eq ==> EnvironmentEquiv ==> EnvironmentEquiv) set_contract_state.
Proof.
  repeat intro; subst.
  unfold set_contract_state, set_chain_contract_state.
  solve_proper.
Qed.

Global Instance set_account_owners_proper :
  Proper (eq ==> eq ==> EnvironmentEquiv ==> EnvironmentEquiv) set_account_owner.
Proof.
  repeat intro; subst.
  unfold set_account_owner, set_chain_account_owner.
  solve_proper.
Qed.
Local Open Scope Z.


(* Next we define how actions are executed. It specifies how an action
changes an environment and which external actions to execute after it.
Note that there can be multiple ways to execute an action. For example, if
the action says to deploy a contract, the implementation is responsible for
selecting which address the new contract should get. *)

Inductive SpecialCallBodyEvaluation
          (prev_env : Environment) (act : Action)
          (new_env : Environment) (new_acts : list Action): Type :=
  | eval_transfer_ownership :
      forall (origin from_addr to_addr acc_addr new_owner_addr : Address)
             (wc : WeakContract),
        env_account_owners prev_env acc_addr = Some origin \/ 
           env_account_owners prev_env acc_addr = Some from_addr ->
        env_contracts prev_env to_addr = Some wc ->
        EnvironmentEquiv
          new_env
          (set_account_owner acc_addr new_owner_addr prev_env) ->
        new_acts = [] ->
        SpecialCallBodyEvaluation prev_env act new_env new_acts
  | eval_check_rent_exempt :
      forall (origin from_addr to_addr : Address)
             (wc : WeakContract),
        env_contracts prev_env to_addr = Some wc ->
        EnvironmentEquiv
          new_env
          prev_env ->
        new_acts = [] ->
        SpecialCallBodyEvaluation prev_env act new_env new_acts
  | eval_check_token_owner : forall (origin from_addr : Address),
        EnvironmentEquiv
          new_env
          prev_env ->
        new_acts = [] ->
        SpecialCallBodyEvaluation prev_env act new_env new_acts.

Global Arguments eval_transfer_ownership {_ _ _ _}.
Global Arguments eval_check_rent_exempt {_ _ _ _}.
Global Arguments eval_check_token_owner {_ _ _ _}.

(* J> TODO: Maybe some sanity checks on the accounts list *)
Inductive ActionEvaluation
          (prev_env : Environment) (act : Action)
          (new_env : Environment) (new_acts : list Action) : Type :=
  | eval_transfer :
      forall (origin from_addr to_addr : Address)
             (origin_acc from_acc to_acc : AccountInformation)
             (amount : Amount),
        amount >= 0 ->
        amount <= env_account_balances prev_env from_addr ->
        account_address origin_acc = origin ->
        account_address from_acc = from_addr ->
        account_address to_acc = to_addr ->
        address_is_contract to_addr = false -> (* J> TODO: It should be possible to transfer to contracts *)
        act = build_act origin from_addr (act_transfer (* from_addr *) to_addr amount) ->
        EnvironmentEquiv
          new_env
          (transfer_balance from_addr to_addr amount prev_env) ->
        new_acts = [] ->
        ActionEvaluation prev_env act new_env new_acts
  | eval_deploy :
      forall (origin from_addr to_addr : Address)
             (origin_acc from_acc to_acc : AccountInformation)
             (amount : Amount)
             (wc : WeakContract)
             (state : SerializedValue)
             (accounts : SliceAccountInformation)
             (result : unit),
      amount = 0 ->
      amount <= env_account_balances prev_env from_addr ->
      account_address origin_acc = origin ->
      account_address from_acc = from_addr ->
      account_address to_acc = to_addr ->
      address_is_contract to_addr = true ->
      env_contracts prev_env to_addr = None ->
      act = build_act origin from_addr (act_deploy wc) ->
      wc_process
        wc
        prev_env
        accounts 
        None = Ok result ->
      EnvironmentEquiv
        new_env
        (set_contract_state to_addr state (add_contract to_addr wc prev_env)) ->
      new_acts = [] ->
      ActionEvaluation prev_env act new_env new_acts
  | eval_call :
      forall (origin from_addr to_addr : Address)
             (origin_acc from_acc to_acc : AccountInformation)
             (amount : Amount)
             (wc : WeakContract)
             (accounts : SliceAccountInformation)
             (msg : option SerializedValue)
             (prev_state : SerializedValue)
             (new_state : SerializedValue)
             (resp_acts : list ActionBody)
             (result : unit),
      amount >= 0 ->
      amount <= env_account_balances prev_env from_addr ->
      account_address origin_acc = origin ->
      account_address from_acc = from_addr ->
      account_address to_acc = to_addr ->
      env_contracts prev_env to_addr = Some wc ->
      env_contract_states prev_env to_addr = Some prev_state ->
      act = build_act origin from_addr
                      (match msg with
                       | None => act_transfer (* from_addr *) to_addr amount
                       | Some msg => act_call to_addr msg
                       end) ->
      wc_process
        wc
        prev_env
        accounts 
        msg = Ok result ->
      new_acts = map (build_act origin to_addr) resp_acts ->
      EnvironmentEquiv
        new_env
        (set_contract_state to_addr new_state (transfer_balance from_addr to_addr amount prev_env)) ->
      ActionEvaluation prev_env act new_env new_acts
  | eval_special_call :
    forall (origin from_addr to_addr : Address)
           (origin_acc from_acc to_acc : AccountInformation)
           (body : SpecialCallBody)
           (amount : Amount)
           (wc : WeakContract),
        amount = 0 ->
        amount <= env_account_balances prev_env from_addr -> 
        account_address origin_acc = origin ->
        account_address from_acc = from_addr ->
        account_address to_acc = to_addr ->
        env_contracts prev_env to_addr = Some wc ->
        act = build_act origin from_addr (act_special_call to_addr body) ->
        SpecialCallBodyEvaluation prev_env act new_env new_acts -> (* J> TODO: Not sure about this line *)
        ActionEvaluation prev_env act new_env new_acts.

Global Arguments eval_transfer {_ _ _ _}.
Global Arguments eval_deploy {_ _ _ _}.
Global Arguments eval_call {_ _ _ _}.
Global Arguments eval_special_call {_ _ _ _}.

Section Accessors.
Context {origin : Address}
        {pre : Environment} {act : Action}
        {post : Environment} {new_acts : list Action}
        (eval : ActionEvaluation pre act post new_acts).

Definition eval_origin : Address :=
  match eval with
  | eval_transfer origin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  | eval_special_call origin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  | eval_deploy origin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  | eval_call origin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _=> origin
  end.

Definition eval_from : Address :=
  match eval with
  | eval_transfer _ from _ _ _ _ _ _ _ _ _ _ _ _ _ _
  | eval_special_call _ from _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  | eval_deploy _ from _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  | eval_call _ from _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => from
  end.

Definition eval_to : Address :=
  match eval with
  | eval_transfer _ _ to _ _ _ _ _ _ _ _ _ _ _ _ _
  | eval_special_call _ _ to _ _ _ _ _ _ _ _ _ _ _ _ _ _
  | eval_deploy _ _ to _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  | eval_call _ _ to _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => to
  end.

Definition eval_amount : Amount :=
  match eval with
  | eval_transfer _ _ _ _ _ _ amount _ _ _ _ _ _ _ _ _
  | eval_special_call _ _ _ _ _ _ _ amount _ _ _ _ _ _ _ _ _
  | eval_deploy _ _ _ _ _ _ amount _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  | eval_call _ _ _ _ _ _ amount _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>  amount
  end.
End Accessors.

Section Theories.
Context {origin : Address}
        {pre : Environment} {act : Action}
        {post : Environment} {new_acts : list Action}
        (eval : ActionEvaluation pre act post new_acts).

(* J> TODO: Write lemmas for the transfer ownership action *)
Lemma account_owner_post (addr owner: Address) :
  env_account_owners pre addr = Some owner ->
  if (owner =? eval_from eval)%address
  then env_account_owners post addr <> 
       env_account_owners pre addr
  else env_account_owners post addr =
       env_account_owners pre addr.
Proof.
  intros. destruct_address_eq. all: swap 1 2.
  +  destruct eval; cbn. destruct e;  rewrite_environment_equiv; cbn; rewrite_environment_equiv; easy.
    - rewrite_environment_equiv; easy.
    - rewrite_environment_equiv; easy.
    - destruct s; cbn; rewrite_environment_equiv.
      ++ cbn. destruct n. cbn. destruct o.
        +++ cbn.
Admitted.

Lemma account_balance_post (addr : Address) :
  env_account_balances post addr =
  env_account_balances pre addr
  + (if (addr =? eval_to eval)%address then eval_amount eval else 0)
  - (if (addr =? eval_from eval)%address then eval_amount eval else 0).
Proof.
  destruct eval; cbn; try (rewrite_environment_equiv; cbn; destruct_address_eq; lia).
  destruct body; destruct s; cbn; rewrite_environment_equiv; cbn; destruct_address_eq; lia.
Qed.

Lemma account_balance_post_to :
  eval_from eval <> eval_to eval ->
  env_account_balances post (eval_to eval) =
  env_account_balances pre (eval_to eval) + eval_amount eval.
Proof.
  intros neq.
  rewrite account_balance_post.
  rewrite address_eq_refl, address_eq_ne by auto.
  lia.
Qed.

Lemma account_balance_post_from :
  eval_from eval <> eval_to eval ->
  env_account_balances post (eval_from eval) =
  env_account_balances pre (eval_from eval) - eval_amount eval.
Proof.
  intros neq.
  rewrite account_balance_post.
  rewrite address_eq_refl, address_eq_ne by auto.
  lia.
Qed.

Lemma account_balance_post_irrelevant (addr : Address) :
  addr <> eval_from eval ->
  addr <> eval_to eval ->
  env_account_balances post addr = env_account_balances pre addr.
Proof.
  intros neq_from neq_to.
  rewrite account_balance_post.
  repeat rewrite address_eq_ne by auto.
  lia.
Qed.

Lemma chain_height_post_action : chain_height post = chain_height pre.
Proof. 
  destruct eval; try (rewrite_environment_equiv; auto).
  destruct body; destruct s; rewrite_environment_equiv; auto.
Qed.

Lemma current_slot_post_action : current_slot post = current_slot pre.
Proof. 
  destruct eval; try (rewrite_environment_equiv; auto).
  destruct body; destruct s; rewrite_environment_equiv; auto.
Qed.

Lemma finalized_height_post_action : finalized_height post = finalized_height pre.
Proof. 
  destruct eval; try (rewrite_environment_equiv; auto).
  destruct body; destruct s; rewrite_environment_equiv; auto.
Qed.

Lemma contracts_post_pre_none contract :
  env_contracts post contract = None ->
  env_contracts pre contract = None.
Proof.
  intros H.
  destruct eval; try (rewrite_environment_equiv; auto). 
  cbn in *.
  destruct_address_eq; congruence.
  destruct body; destruct s; rewrite_environment_equiv; auto.
Qed.

Lemma eval_amount_nonnegative : eval_amount eval >= 0.
Proof. destruct eval; try easy; cbn in *; rewrite e; easy. Qed.

Lemma eval_amount_le_account_balance :
  eval_amount eval <= env_account_balances pre (eval_from eval).
Proof. now destruct eval. Qed.

End Theories.

Section Trace.

Record BlockHeader :=
  build_block_Header {
    block_height : nat;
    block_slot : nat;
    block_finalized_height : nat;
    block_reward : Amount;
    block_creator : Address;
  }.

Definition add_new_block_to_env
           (header : BlockHeader) (env : Environment) : Environment :=
  env<|env_chain; chain_height := block_height header|>
     <|env_chain; current_slot := block_slot header|>
     <|env_chain; finalized_height := block_finalized_height header|>
     <|env_account_balances ::=
         add_balance (block_creator header) (block_reward header)|>.

(* Todo: this should just be a computation. But I still do not *)
(* know exactly what the best way of working with reflect is *)
Local Open Scope nat.
Definition act_is_from_account (act : Action) : Prop :=
  address_is_contract (act_from act) = false.

Definition act_origin_is_account (act : Action) : Prop :=
  address_is_contract (act_origin act) = false.

Definition act_origin_is_eq_from (act : Action) : Prop :=
  address_eqb (act_origin act) (act_from act) = true.


Record IsValidNextBlock (header : BlockHeader) (chain : Chain) : Prop :=
  build_is_valid_next_block {
    valid_height : block_height header = S (chain_height chain);
    valid_slot : block_slot header > current_slot chain;
    valid_finalized_height :
      block_finalized_height header >= finalized_height chain /\
      block_finalized_height header < block_height header;
    valid_creator : address_is_contract (block_creator header) = false;
    valid_reward : (block_reward header >= 0)%Z;
  }.

Record ChainState :=
  build_chain_state {
    chain_state_env :> Environment;
    chain_state_queue : list Action;
  }.

MetaCoq Run (make_setters ChainState).

Inductive ChainStep (prev_bstate : ChainState) (next_bstate : ChainState) :=
| step_block :
    forall (header : BlockHeader),
      chain_state_queue prev_bstate = [] ->
      IsValidNextBlock header prev_bstate ->
      Forall act_is_from_account (chain_state_queue next_bstate) ->
      Forall act_origin_is_eq_from (chain_state_queue next_bstate) ->
      EnvironmentEquiv
        next_bstate
        (add_new_block_to_env header prev_bstate) ->
      ChainStep prev_bstate next_bstate
| step_action :
    forall (act : Action)
           (acts : list Action)
           (new_acts : list Action),
      chain_state_queue prev_bstate = act :: acts ->
      ActionEvaluation prev_bstate act next_bstate new_acts ->
      chain_state_queue next_bstate = new_acts ++ acts ->
      ChainStep prev_bstate next_bstate
| step_action_invalid :
    forall (act : Action)
           (acts : list Action),
      EnvironmentEquiv next_bstate prev_bstate ->
      chain_state_queue prev_bstate = act :: acts ->
      chain_state_queue next_bstate = acts ->
      act_is_from_account act ->
      (forall bstate new_acts, ActionEvaluation prev_bstate act bstate new_acts -> False) ->
      ChainStep prev_bstate next_bstate
| step_permute :
      EnvironmentEquiv next_bstate prev_bstate ->
      Permutation (chain_state_queue prev_bstate) (chain_state_queue next_bstate) ->
      ChainStep prev_bstate next_bstate.

Lemma origin_is_account acts :
  Forall act_is_from_account acts ->
  Forall act_origin_is_eq_from acts ->
  Forall act_origin_is_account acts.
Proof.
  intros Hall.
  induction Hall as [| a Ha];intros Hall0;auto.
  inversion Hall0;subst.
  constructor;auto.
  specialize (address_eqb_spec (act_origin a) (act_from a)) as Haddr;
    unfold act_origin_is_eq_from in *; destruct Haddr;easy.
Qed.

Definition empty_state : ChainState :=
  {| chain_state_env :=
       {| env_chain :=
            {| chain_height := 0;
               current_slot := 0;
               finalized_height := 0; |};
          env_account_balances a := 0%Z;
          env_account_owners a := None;
          env_contract_states a := None;
          env_contracts a := None; |};
     chain_state_queue := [] |}.

(* The ChainTrace captures that there is a valid execution where,
starting from one environment and queue of actions, we end up in a
different environment and queue of actions. *)
Definition ChainTrace := ChainedList ChainState ChainStep.

(* Additionally, a state is reachable if there is a trace ending in this trace. *)
Definition reachable (state : ChainState) : Prop :=
  inhabited (ChainTrace empty_state state).

Definition outgoing_acts (state : ChainState) (addr : Address) : list ActionBody :=
  map act_body
      (filter (fun act => (act_from act =? addr)%address) (chain_state_queue state)).

(* We define a transaction as a "fully specified" action, recording all info. For
example, a transaction contains the contract address that was created when a contract
is deployed. This is more about bridging the gap between our definitions and what
a normal blockchain is. Each evaluation of an action in the blockchain corresponds to
a transaction, so we can go from a trace to a list of transactions. *)
Inductive TxBody :=
  | tx_empty
  | tx_deploy (wc : WeakContract)
  | tx_call (msg : option SerializedValue)
  | tx_special_call (body : SpecialCallBody).

Record Tx :=
  build_tx {
      tx_origin : Address;
      tx_from : Address;
      tx_to : Address;
      tx_amount : Amount;
      tx_body : TxBody;
  }.

Definition eval_tx {pre : Environment} {act : Action}
                   {post : Environment} {new_acts : list Action}
                   (step : ActionEvaluation pre act post new_acts) : Tx :=
  match step with
  | eval_transfer origin from to _ _ _ amount _ _ _ _ _ _ _ _ _ =>
    build_tx origin from to amount tx_empty
  | eval_deploy origin from to _ _ _ amount wc _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    build_tx origin from to amount (tx_deploy wc)
  | eval_call origin from to _ _ _ amount _ _ msg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    build_tx origin from to amount (tx_call msg)
  | eval_special_call origin from to _ _ _ body amount _ _ _ _ _ _ _ _ _ =>
    build_tx origin from to amount (tx_special_call body)
  end.

Fixpoint trace_txs {from to : ChainState} (trace : ChainTrace from to) : list Tx :=
  match trace with
  | snoc trace' step =>
    match step with
    | step_action _ _ _ _ _ _ eval _ => eval_tx eval :: trace_txs trace'
    | _ => trace_txs trace'
    end
  | _ => []
  end.

Definition incoming_txs
           {from to : ChainState}
           (trace : ChainTrace from to)
           (addr : Address) : list Tx :=
  filter (fun tx => (tx_to tx =? addr)%address) (trace_txs trace).

Definition outgoing_txs
           {from to : ChainState}
           (trace : ChainTrace from to)
           (addr : Address) : list Tx :=
  filter (fun tx => (tx_from tx =? addr)%address) (trace_txs trace).

Record ContractCallInfo (Msg : Type) :=
  build_call_info
  {
    call_origin : Address;
    call_from : Address;
    call_amount : Amount;
    call_msg : option Msg;
  }.

Global Arguments build_call_info {_}.
Global Arguments call_origin {_}.
Global Arguments call_from {_}.
Global Arguments call_amount {_}.
Global Arguments call_msg {_}.

Fixpoint incoming_calls
           (Msg : Type) `{Serializable Msg}
           {from to : ChainState}
           (trace : ChainTrace from to)
           (caddr : Address) : option (list (ContractCallInfo Msg)) :=
  match trace with
  | snoc trace' step =>
    match step with
    | step_action _ _ _ _ _ _ (eval_call origin from to _ _ _ amount _ _ msg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ =>
      if (to =? caddr)%address then
        (* If there is a message it should deserialize correctly,
           otherwise the entire operation returns None. *)
        do hd_msg <- match msg with
                     | Some msg =>
                       match deserialize msg with
                       | Some msg => Some (Some msg)
                       | None => None
                       end
                     | None => Some None
                     end;
        do tl <- incoming_calls Msg trace' caddr;
        Some (build_call_info origin from amount hd_msg :: tl)
      else
        incoming_calls Msg trace' caddr
    | _ => incoming_calls Msg trace' caddr
    end
  | _ => Some []
  end.

Record DeploymentInfo :=
  build_deployment_info
  {
    deployment_origin : Address;
    deployment_from : Address;
    deployment_amount : Amount;
  }.

Fixpoint deployment_info
           {from to : ChainState}
           (trace : ChainTrace from to)
           (caddr : Address) : option DeploymentInfo :=
  match trace with
  | snoc trace' step =>
    match step with
    | step_action _ _ _ _ _ _ (eval_deploy origin from to _ _ _ amount _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ =>
      if (to =? caddr)%address then
        Some (build_deployment_info origin from amount)
      else
        deployment_info trace' caddr
    | _ => deployment_info trace' caddr
    end
  | clnil => None
  end.

Record SpecialCallInfo :=
  build_special_call_info
  {
    special_call_origin : Address;
    special_call_from : Address;
    special_call_amount : Amount;
    special_call_body : SpecialCallBody;
  }.

Fixpoint incoming_special_calls
           {from to : ChainState}
           (trace : ChainTrace from to)
           (caddr : Address) : option (list SpecialCallInfo) :=
  match trace with
  | snoc trace' step =>
    match step with
    | step_action _ _ _ _ _ _ (eval_special_call origin from to _ _ _ body amount _ _ _ _ _ _ _ _ _) _ =>
      if (to =? caddr)%address then
        do tl <- incoming_special_calls trace' caddr;
        Some (build_special_call_info origin from amount body :: tl)
      else
        incoming_special_calls trace' caddr
    | _ => incoming_special_calls trace' caddr
    end
  | _ => Some []
  end.

Fixpoint trace_blocks {from to : ChainState}
         (trace : ChainTrace from to) : list BlockHeader :=
  match trace with
  | snoc trace' step =>
    match step with
    | step_block _ _ header _ _ _ _ _ =>
      header :: trace_blocks trace'
    | _ => trace_blocks trace'
    end
  | clnil => []
  end.

Definition created_blocks
           {from to : ChainState} (trace : ChainTrace from to)
           (creator : Address) : list BlockHeader :=
  filter (fun b => (block_creator b =? creator)%address)
         (trace_blocks trace).

Definition is_deploy (ac : ActionBody) : bool :=
  match ac with
  | act_transfer _ _ => false
  | act_call _ _ => false
  | act_deploy _ => true
  | act_special_call _ _ => false
  end.

Definition is_call (ac : ActionBody) : bool :=
  match ac with
  | act_transfer _ _ => false
  | act_call _ _ => true
  | act_deploy _ => false
  | act_special_call _ _ => false
  end.

Definition is_transfer (ac : ActionBody) : bool :=
  match ac with
  | act_transfer _ _ => true
  | act_call _ _ => false
  | act_deploy _ => false
  | act_special_call _ _ => false
  end.

Definition is_special_call (ac : ActionBody) : bool :=
  match ac with
  | act_transfer _ _ => false
  | act_call _ _ => false
  | act_deploy _ => false
  | act_special_call _ _ => true
  end.

Section Theories.
Ltac destruct_chain_step :=
  match goal with
  | [step: ChainStep _ _ |- _] =>
    destruct step as
        [header queue_prev valid_header acts_from_accs origin_correct env_eq|
         act acts new_acts queue_prev eval queue_new|
         act acts env_eq queue_prev queue_new act_from_acc no_eval|
         env_eq perm]
  end.

Ltac destruct_action_eval :=
  match goal with
  | [eval: ActionEvaluation _ _ _ _ |- _] => destruct eval
  end.

Ltac destruct_special_body_eval :=
  match goal with
  | [body_eval: SpecialCallBodyEvaluation _ _ _ _ |- _] => destruct body_eval
  end.

Lemma account_state_updated_after_process {env} (accounts : SliceAccountInformation) (contract : WeakContract) (acc : AccountInformation) msg :
  forall accs_tail prev_state,
  accounts = acc :: accs_tail ->
  env_contract_states env (account_address acc) = prev_state ->
  wc_process contract env accounts msg = Ok tt ->
  exists new_state, env_contract_states env (account_address acc) = new_state.
Proof.
  (* intros accounts_remainder prev_state accounts_has_acc acc_has_state process_some. *)
  easy.  
Qed.

Lemma contract_addr_format {to} (addr : Address) (wc : WeakContract) :
  reachable to ->
  env_contracts to addr = Some wc ->
  address_is_contract addr = true.
Proof.
  intros [trace] contract_at_addr.
  remember empty_state eqn:eq.
  induction trace; rewrite eq in *; clear eq.
  - cbn in *; congruence.
  - destruct_chain_step;
      try now rewrite_environment_equiv.
    + destruct_action_eval; try destruct_special_body_eval; rewrite_environment_equiv; cbn in *; destruct_address_eq; subst; auto.
Qed.

Lemma new_acts_no_out_queue orig addr1 addr2 new_acts resp_acts :
  addr1 <> addr2 ->
  new_acts = map (build_act orig addr2) resp_acts ->
  Forall (fun a => (act_from a =? addr1)%address = false) new_acts.
Proof.
  intros neq ?; subst.
  induction resp_acts; cbn; auto.
  constructor; destruct_address_eq; cbn in *; congruence.
Qed.

Lemma outgoing_acts_after_block_nil bstate addr :
  Forall act_is_from_account (chain_state_queue bstate) ->
  address_is_contract addr = true ->
  outgoing_acts bstate addr = [].
Proof.
  intros all is_contract.
  unfold outgoing_acts.
  induction (chain_state_queue bstate); auto.
  cbn.
  inversion_clear all.
  destruct_address_eq; subst; auto.
  unfold act_is_from_account in *.
  congruence.
Qed.

Lemma outgoing_acts_after_deploy_nil bstate addr :
  Forall (fun act => (act_from act =? addr)%address = false) (chain_state_queue bstate) ->
  outgoing_acts bstate addr = [].
Proof.
  intros all.
  unfold outgoing_acts.
  induction (chain_state_queue bstate) as [|hd tl IH]; auto.
  cbn in *.
  inversion_clear all.
  rewrite H.
  auto.
Qed.

Print ChainTrace.

Local Open Scope address.
(* This next lemma shows that any for a full chain trace,
the ending state will not have any queued actions from
undeployed contracts. *)
Lemma undeployed_contract_no_out_queue contract state :
  reachable state ->
  address_is_contract contract = true ->
  env_contracts state contract = None ->
  Forall (fun act => (act_from act =? contract) = false) (chain_state_queue state).
Proof.
  intros [trace] is_contract.
  remember empty_state eqn:eq.
  induction trace;
    intros undeployed; rewrite eq in *; clear eq; cbn; auto.
  destruct_chain_step; [|destruct_action_eval| |];
    try rewrite_environment_equiv;
    repeat
      match goal with
      | [H: chain_state_queue _ = _ |- _] => rewrite H in *; clear H
      end;
    subst;
    cbn in *.
  - (* New block *)
    match goal with
    | [H: Forall act_is_from_account _ |- _] => induction H
    end;
    match goal with
    | [H: Forall act_origin_is_eq_from _ |- _] => inversion H
    end; constructor; auto; destruct_address_eq; congruence.
  - (* Transfer step, just use IH *)
    eapply list.Forall_cons; eauto.
  - (* Deploy step. First show that it is not to contract and then use IH. *)
    destruct_address_eq; try congruence.
    eapply list.Forall_cons; eauto.
  - (* Call. Show that it holds for new actions as it is from *)
    (* another contract, and use IH for remaining. *)
    apply list.Forall_app.
    assert (contract <> (account_address to_acc)) by congruence.
    split; [eapply new_acts_no_out_queue|eapply list.Forall_cons]; eauto.
  - (* Invalid User Action *)
    destruct_special_body_eval.
    try now apply Forall_inv_tail in IHtrace.
    apply Forall_inv_tail in IHtrace. 
    + cbn in *. rewrite e1. easy. 
    + easy.
    + apply Forall_inv_tail in IHtrace; now rewrite_environment_equiv.
    + apply Forall_inv_tail in IHtrace; try rewrite e1; now rewrite_environment_equiv. 
    + apply Forall_inv_tail in IHtrace; try rewrite e0; now rewrite_environment_equiv.
  - (* No Eval *)
    specialize_hypotheses.
    now inversion_clear IHtrace.
  - (* Permutation *)
    specialize_hypotheses.
    now rewrite <- perm.
Qed.

Local Hint Resolve contracts_post_pre_none : core.
Local Hint Unfold reachable : core.


(* With this lemma proven, we can show that the (perhaps seemingly stronger)
fact, that an undeployed contract has no outgoing txs, holds. *)
Lemma undeployed_contract_no_out_txs
  contract state (trace : ChainTrace empty_state state) :
  address_is_contract contract = true ->
  env_contracts state contract = None ->
  outgoing_txs trace contract = [].
Proof.
  intros is_contract undeployed.
  remember empty_state; induction trace; subst; cbn; auto.
  destruct_chain_step; try now rewrite_environment_equiv.
  - (* In these steps we will use that the queue did not contain txs to the contract. *)
    subst.
    cbn.
    pose proof
         (undeployed_contract_no_out_queue
            contract mid
            ltac:(auto) ltac:(auto) ltac:(eauto)) as Hqueue.
    repeat
      match goal with
      | [H: chain_state_queue _ = _ |- _] => rewrite H in *; clear H
      end.
    inversion_clear Hqueue.
    destruct act;
    destruct_action_eval; try rewrite_environment_equiv;
      subst;
      cbn in *;
      destruct_address_eq;
      try tauto; try congruence.
   destruct_special_body_eval; rewrite_environment_equiv; subst; cbn in *; destruct_address_eq; auto.
Qed.

Lemma undeployed_contract_no_in_txs
      contract state (trace : ChainTrace empty_state state) :
  address_is_contract contract = true ->
  env_contracts state contract = None ->
  incoming_txs trace contract = [].
Proof.
  intros is_contract undeployed.
  remember empty_state; induction trace; subst; cbn; auto.
  destruct_chain_step; try now rewrite_environment_equiv.
  - (destruct_action_eval; try destruct_special_body_eval); try rewrite_environment_equiv;
    cbn in *;
    destruct_address_eq; auto; subst; try congruence.
Qed.

Lemma deployment_info_some
      {to} (trace : ChainTrace empty_state to) caddr :
  deployment_info trace caddr <> None ->
  env_contracts to caddr <> None.
Proof.
  remember empty_state; induction trace as [|? ? ? ? IH]; subst; cbn in *; try tauto.
  destruct_chain_step; try now rewrite_environment_equiv.
  - destruct_action_eval; try rewrite_environment_equiv; auto.
    (* Deploy *)
    cbn in *.
    rewrite (address_eq_sym caddr).
    destruct_address_eq; try discriminate.
    auto.
    destruct_special_body_eval; try rewrite_environment_equiv; auto.
Qed.

Lemma deployment_info_addr_format
      {to} (trace : ChainTrace empty_state to)
      caddr :
  deployment_info trace caddr <> None ->
  address_is_contract caddr = true.
Proof.
  intros has_deployment_info.
  pose proof (deployment_info_some _ _  has_deployment_info).
  destruct (env_contracts to caddr) as [wc|] eqn:?; try congruence.
  eapply contract_addr_format; eauto.
Qed.

Lemma incoming_txs_contract
      caddr bstate (trace : ChainTrace empty_state bstate)
      (depinfo : DeploymentInfo)
      Msg `{Serializable Msg} (msgs : list (ContractCallInfo Msg)) (bodies : list (SpecialCallInfo)) :
  deployment_info trace caddr = Some depinfo ->
  incoming_calls Msg trace caddr = Some msgs ->
  incoming_special_calls trace caddr = Some bodies ->
  map (fun tx => (tx_from tx, tx_to tx, tx_amount tx)) (incoming_txs trace caddr) =
  map (fun call => (call_from call, caddr, call_amount call)) msgs ++
  map (fun scall => (special_call_from scall, caddr, special_call_amount scall)) bodies ++
       [(deployment_from depinfo, caddr, deployment_amount depinfo)].
Proof.
  intros depinfo_eq calls_eq special_calls_eq. 
  enough ((env_contracts bstate caddr = None ->
           incoming_txs trace caddr = [] /\
           deployment_info trace caddr = None /\
           incoming_calls Msg trace caddr = Some [] /\
           incoming_special_calls trace caddr = Some []) /\
          (env_contracts bstate caddr <> None ->
           deployment_info trace caddr <> None ->
           incoming_calls Msg trace caddr <> None ->
           incoming_special_calls trace caddr <> None ->
           exists (depinfo : DeploymentInfo)
                  (inc_calls : list (ContractCallInfo Msg))
                  (inc_special_calls : list SpecialCallInfo)
                  (call_txs : list Tx) (special_call_txs : list Tx) (dep_tx : Tx),
             deployment_info trace caddr = Some depinfo /\
             incoming_calls Msg trace caddr = Some inc_calls /\
             incoming_special_calls trace caddr = Some inc_special_calls /\
             incoming_txs trace caddr = call_txs ++ special_call_txs ++ [dep_tx] /\
             map (fun tx => (tx_from tx, tx_to tx, tx_amount tx)) call_txs =
             map (fun call => (call_from call, caddr, call_amount call)) inc_calls /\
             map (fun tx => (tx_from tx, tx_to tx, tx_amount tx)) special_call_txs =
             map (fun scall => (special_call_from scall, caddr, special_call_amount scall)) inc_special_calls /\
             (tx_from dep_tx, tx_to dep_tx, tx_amount dep_tx) =
             (deployment_from depinfo, caddr, deployment_amount depinfo))) as generalized.
  {
    rewrite depinfo_eq, calls_eq, special_calls_eq in *.
    destruct (env_contracts bstate caddr).
    - destruct generalized as [_ generalized].
      specialize (generalized ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)).
      destruct generalized as [? [? [? [? [? [? [? [? [? [-> [? ?]]]]]]]]]]]. easy.
      rewrite map_app. rewrite map_app.
      cbn in *. 
      destruct H4. congruence.
    - destruct generalized as [generalized _].
      specialize (generalized eq_refl).
      destruct generalized as [_ [? _]]; congruence.
  }

  assert (is_contract: address_is_contract caddr = true).
  { assert (deployment_info trace caddr <> None) by congruence.
    eapply (deployment_info_addr_format); eassumption. }

  clear depinfo_eq calls_eq depinfo special_calls_eq msgs. 

  remember empty_state; induction trace as [|? ? ? ? IH]; subst; cbn in *;
    try tauto.
  destruct_chain_step; cbn in *; try now rewrite_environment_equiv.
  - (* Evaluation *)
    (destruct_action_eval; try destruct_special_body_eval); cbn in *; try rewrite_environment_equiv.
    + (* Transfer *)
      destruct_address_eq; auto.
      subst.
      cbn.
      congruence.
    + (* Deploy *)
      cbn in *.
      rewrite (address_eq_sym caddr) in *.
      destruct_address_eq; auto.
      split; try discriminate.
      intros _ depinfo_ne_none calls_ne_none.
      subst.
      cbn in *.
(*       destruct (deserialize setup); cbn in *; try congruence. *)
      remember (build_deployment_info _ _ _) as depinfo.
      remember (build_tx _ _ _ _ _) as deptx.
      destruct IH as [IH _]; auto.
      specialize (IH ltac:(auto)).
      fold (incoming_txs trace (account_address to_acc)).
      destruct IH as [-> ].
      destruct H0 as [?].
      destruct H1 as [-> ]. (* J> TODO: join these destructs in a single intros pattern *)
      exists depinfo, [], [], [], [], deptx; subst; cbn in *.
      tauto.
    + (* Call *) 
      destruct_address_eq; subst; auto.
      cbn in *.
      split; [intros; congruence|].
      destruct IH as [_ IH]; auto.
      intros _ deploy_info calls special_calls.
      destruct (match msg with | Some _ => _ | _ => Some None end);
        cbn in *; try congruence.
      destruct (incoming_calls _ _) as [inc_calls|]; cbn in *; try congruence.
      destruct (incoming_special_calls _ _) as [inc_special_calls|]; cbn in *; try congruence.
      unshelve epose proof (IH _ _ _ _) as IH; auto; try congruence.
      
      destruct IH as
          [depinfo [prev_calls [prev_special_calls
                     [prev_call_txs [prev_special_call_txs
                       [dep_tx
                         [depinfo_eq [inc_calls_eq [inc_special_call_eq
                           [inc_txs_eq [calls_map_eq [special_calls_map_eq ?]]]]]]]]]]]].
      remember (build_tx _ _ _ _ _) as new_tx.
      remember (build_call_info _ _ _ _) as new_call.
      exists depinfo, (new_call :: inc_calls), (inc_special_calls), (new_tx :: prev_call_txs), (prev_special_call_txs), dep_tx.
      split; auto.
      split; auto.
      split; auto.
      fold (incoming_txs trace (account_address to_acc)).
      rewrite inc_txs_eq.
      split; [now rewrite app_comm_cons|].
      inversion_clear inc_calls_eq.
      inversion_clear inc_special_call_eq.
      cbn.
      split; auto.
      cbn.
      rewrite calls_map_eq.
      subst; tauto.
    (* Special Call *)
    +  destruct_address_eq; subst; auto.
      cbn in *.
      split; [intros; congruence|].
      destruct IH as [_ IH]; auto.
      intros _ deploy_info calls special_calls.
      destruct (incoming_special_calls trace (account_address to_acc)) as [inc_special_calls|];
        cbn in *; try congruence.
      destruct (incoming_calls _ _) as [inc_calls|]; cbn in *; try congruence.
      (* destruct (incoming_special_calls _ _) as [inc_special_calls|]; cbn in *; try congruence. *)
      unshelve epose proof (IH _ _ _ _) as IH; auto; try congruence.
      
      destruct IH as
          [depinfo [prev_calls [prev_special_calls
                     [prev_call_txs [prev_special_call_txs
                       [dep_tx
                         [depinfo_eq [inc_calls_eq [inc_special_call_eq
                           [inc_txs_eq [calls_map_eq [special_calls_map_eq ?]]]]]]]]]]]].
      remember (build_tx _ _ _ _ _) as new_tx.
      remember (build_special_call_info _ _ _ _) as new_special_call.
      exists depinfo, (inc_calls), (new_special_call :: inc_special_calls), (prev_call_txs), (new_tx:: prev_special_call_txs), dep_tx.
      split; auto.
      split; auto.
      split; auto.
      fold (incoming_txs trace (account_address to_acc)).
      rewrite inc_txs_eq.
      (* Admitted. *)
      split; [rewrite app_comm_cons|].
      inversion_clear inc_calls_eq.
      inversion_clear inc_special_call_eq.
      cbn.
      Admitted. 
      (* rewrite special_calls_map_eq.
      2: split; auto; subst.
      2: easy. 
      2: cbn; easy. 
      split; auto.
      subst; tauto. *)
(* Qed. *)

Lemma undeployed_contract_no_in_calls
      {Msg} `{Serializable Msg}
      contract state (trace : ChainTrace empty_state state) :
  env_contracts state contract = None ->
  incoming_calls Msg trace contract = Some [].
Proof.
  unfold incoming_calls.
  intros undeployed.
  remember empty_state; induction trace; subst; cbn in *; auto.
  destruct_chain_step; try now rewrite_environment_equiv.
  - destruct_action_eval; try rewrite_environment_equiv;
      cbn in *;
      destruct_address_eq; auto; subst; try congruence.
    destruct_special_body_eval; rewrite_environment_equiv; cbn in *; auto.
Qed.

Local Open Scope Z.
Lemma account_balance_trace state (trace : ChainTrace empty_state state) addr :
  env_account_balances state addr =
  sumZ tx_amount (incoming_txs trace addr) +
  sumZ block_reward (created_blocks trace addr) -
  sumZ tx_amount (outgoing_txs trace addr).
Proof.
  unfold incoming_txs, outgoing_txs.
  remember empty_state as from_state.
  induction trace; [|destruct_chain_step].
  - subst. cbn. lia.
  - (* Block *)
    rewrite_environment_equiv.
    cbn.
    fold (created_blocks trace addr).
    rewrite IHtrace by auto.
    destruct_address_eq; subst; cbn; lia.
  - (* Step *)
    cbn.
    destruct_action_eval; cbn; try rewrite_environment_equiv; cbn.
    1, 2, 3: fold (created_blocks trace addr); rewrite IHtrace by auto.
    1, 2, 3: destruct_address_eq; cbn; lia.
    destruct_special_body_eval; rewrite_environment_equiv; cbn; fold (created_blocks trace addr); rewrite IHtrace by auto;
    destruct_address_eq; cbn; lia.
  - (* Invalid User Action *)
    now rewrite_environment_equiv.
  - (* Permutation *)
    now rewrite_environment_equiv.
Qed.

Lemma contract_no_created_blocks state (trace : ChainTrace empty_state state) addr :
  address_is_contract addr = true ->
  created_blocks trace addr = [].
Proof.
  intros is_contract.
  remember empty_state eqn:eq.
  induction trace; auto.
  destruct_chain_step; auto.
  cbn.
  subst.
  inversion valid_header.
  destruct (address_eqb_spec (block_creator header) addr); auto.
  congruence.
Qed.

Lemma undeployed_contract_balance_0 state addr :
  reachable state ->
  address_is_contract addr = true ->
  env_contracts state addr = None ->
  env_account_balances state addr = 0.
Proof.
  intros [trace] is_contract no_contract.
  rewrite (account_balance_trace _ trace); auto.
  rewrite undeployed_contract_no_out_txs, undeployed_contract_no_in_txs,
          contract_no_created_blocks; auto.
Qed.

(* J> TODO: Lemmas about account owners  *)

Lemma account_balance_nonnegative state addr :
  reachable state ->
  env_account_balances state addr >= 0.
Proof.
  intros [trace].
  remember empty_state eqn:eq.
  induction trace; subst; cbn; try lia.
  specialize (IHtrace eq_refl).
  destruct_chain_step.
  - (* New block *)
    rewrite_environment_equiv.
    cbn.
    inversion valid_header.
    destruct_address_eq; lia.
  - (* Action evaluation *)
    rewrite (account_balance_post eval addr).
    pose proof (eval_amount_nonnegative eval).
    pose proof (eval_amount_le_account_balance eval).
    destruct_address_eq; subst; cbn in *; try lia.
  - (* Invalid User Action *)
    now rewrite_environment_equiv.
  - (* Permutation *)
    now rewrite_environment_equiv.
Qed.

Lemma wc_process_strong {Msg State : Type}
          `{Serializable Msg}
          `{Serializable State}
          {contract : Contract Msg State}
          {chain accounts msg result} :
  wc_process (contract : WeakContract) chain accounts msg =
  Ok result ->
  exists msg_strong ,
    match msg_strong with
    | Some msg_strong => msg >>= deserialize = Some msg_strong
    | None => msg = None
    end /\
  Blockchain.process contract chain accounts msg_strong =
    Ok result.
Proof.
  intros process.
  cbn in *.
  all: exists (msg >>= deserialize).
  all: destruct msg as [msg|]; cbn in *.
  1: destruct (deserialize msg) as [msg_strong|];
    cbn in *; try congruence.
  1: destruct (Blockchain.process _ _ _ _)
    as [[]|] eqn:result_eq;
    cbn in *; try congruence.
  all: inversion_clear process; auto.
  split; auto; now destruct (process contract chain accounts None).
Qed.

Lemma deployed_contract_state_typed
          {Msg State : Type}
          `{Serializable Msg}
          `{Serializable State}
          {contract : Contract Msg State}
          {bstate : ChainState}
          {caddr} :
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  reachable bstate ->
  exists (cstate : State),
    contract_state bstate caddr = Some cstate.
Proof.
  intros contract_deployed [trace].
  destruct (contract_state bstate caddr) as [cstate|] eqn:eq;
    [exists cstate; auto|].
  unfold contract_state in *.
  (* Show that eq is a contradiction. *)
  remember empty_state; induction trace; subst; cbn in *; try congruence.
  destruct_chain_step; try now rewrite_environment_equiv.
  - (* Action evaluation *)
    destruct_action_eval; subst; try rewrite_environment_equiv; cbn in *.
    + (* Transfer, use IH *)
      auto.
    + (* Deployment *)
      destruct_address_eq; subst; auto.
      (* To this contract, show that deserialization would not fail. *)
      replace wc with (contract : WeakContract) in * by congruence.
      destruct (wc_process_strong ltac:(eassumption)) as [msg_opt [? ]].
      destruct msg_opt; try easy.
      Admitted.
(*       cbn in *.
      inversion_clear e3. inversion_clear H1. inversion_clear H2. 
      congruence.
    + (* Call *)
      destruct (address_eqb_spec caddr to_addr); subst; auto.
      (* To this contract, show that deserialization would not fail. *)
      replace wc with (contract : WeakContract) in * by congruence.
      destruct (wc_receive_strong ltac:(eassumption))
        as [state_strong [msg_strong [resp_state_strong [? [? [<- receive]]]]]].
      cbn in eq.
      rewrite deserialize_serialize in eq; congruence.
    + (* Transfer Ownership *) 
      destruct_special_body_eval; rewrite_environment_equiv; auto.
Qed. *)

Lemma origin_is_always_account
          {Msg State : Type}
          `{Serializable Msg}
          `{Serializable State}
          {bstate : ChainState} :
  reachable bstate ->
  Forall act_origin_is_account (chain_state_queue bstate).
Proof.
  intros [trace].
  remember empty_state; induction trace;subst; cbn in *; try constructor.
  destruct_chain_step.
  - (* New block, use the fact that [act_origin] is the same as [act_from]
       and [act_from] is an account address*)
    now apply origin_is_account.
  - (* Action evaluation *)
    destruct_action_eval; subst;
      rewrite queue_new in *;
      rewrite queue_prev in *;
      cbn in *;
      specialize_hypotheses;
      inversion IHtrace;subst; try easy.
    apply Forall_app. split.
    * apply All_Forall.Forall_map.
      apply Forall_forall; easy.
    * auto.
    * destruct_special_body_eval; cbn in*;
      specialize_hypotheses;
      inversion IHtrace;subst; try easy.
  - (* Invalid User Action *)
    rewrite queue_new in *; rewrite queue_prev in *; cbn in *.
    specialize_hypotheses; inversion IHtrace; subst; easy.
  - (* Permutation *)
    eapply forall_respects_permutation; eauto.
Qed.

Inductive TagFacts := tag_facts.
Inductive TagAddBlock := tag_add_block.
Inductive TagDeployment := tag_deployment.
Inductive TagOutgoingAct := tag_outgoing_act.
Inductive TagNonrecursiveCall := tag_nonrecursive_call.
Inductive TagRecursiveCall := tag_recursive_call.
Inductive TagPermuteQueue := tag_permute_queue.

Hint Constructors
     TagFacts TagAddBlock TagDeployment TagOutgoingAct
     TagNonrecursiveCall TagRecursiveCall TagPermuteQueue : core.

(* TODO: Finish this proof *)
Lemma contract_induction
      {Msg State (* Setup *) : Type}
      `{Serializable Msg}
      `{Serializable State}
(*       `{Serializable Setup} *)
      (contract : Contract Msg State (* Setup *))
      (AddBlockFacts :
         forall (chain_height : nat) (current_slot : nat) (finalized_height : nat)
                (new_height : nat) (new_slot : nat) (new_finalized_height : nat), Prop)
      (DeployFacts : forall (chain : Chain) (* (accounts : SliceAccountInformation) *), Prop)
      (CallFacts :
         forall (chain : Chain)
                (accounts : SliceAccountInformation)
(*                 (cstate : State) *)
                (outgoing_actions : list ActionBody), Prop)
      (P : forall (chain_height : nat)
                  (current_slot : nat)
                  (finalized_height : nat)
                  (caddr : Address)
                  (deployment_info : DeploymentInfo)
(*                   (cstate : State) *)
                  (balance : Amount)
                  (outgoing_actions_queued : list ActionBody)
                  (incoming_calls_seen : list (ContractCallInfo Msg))
                  (outgoing_txs_seen : list Tx), Prop) :

  (* Facts *)
  (forall (bstate_from bstate_to : ChainState) (step : ChainStep bstate_from bstate_to)
          (from_reachable : reachable bstate_from)
          (tag : TagFacts),
      match step with
      | step_block _ _ header _ _ _ _ _ =>
        AddBlockFacts (chain_height bstate_from)
                      (current_slot bstate_from)
                      (finalized_height bstate_from)
                      (block_height header)
                      (block_slot header)
                      (block_finalized_height header)
      | step_action _ _ act _ _ _ (eval_deploy origin from to _ _ _ amount _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ =>
        DeployFacts (transfer_balance from to amount bstate_from)
      | step_action _ _ act _ _ _ (eval_call origin from to _ _ _ amount _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ =>
        let new_state := transfer_balance from to amount bstate_from in
        forall (accounts : SliceAccountInformation) (cstate : State),
          env_contracts bstate_from to = Some (contract : WeakContract) ->
          contract_state bstate_from to = Some cstate ->
          CallFacts
            new_state
            accounts (* cstate *)
            (outgoing_acts bstate_from to)
      | _ => Logic.True
      end) ->

  (* Add block *)
  (forall old_chain_height old_cur_slot old_fin_height
          new_chain_height new_cur_slot new_fin_height
          caddr dep_info (* state *) balance inc_calls out_txs
          (facts : AddBlockFacts old_chain_height old_cur_slot old_fin_height
                                 new_chain_height new_cur_slot new_fin_height)
          (IH : P old_chain_height old_cur_slot old_fin_height
                  caddr dep_info (* state *) balance [] inc_calls out_txs)
          (tag : TagAddBlock),
      P new_chain_height new_cur_slot new_fin_height
        caddr dep_info (* state *) balance [] inc_calls out_txs) ->

  (* Deploy contract *)
  (forall chain contract_acc (* result *) origin from
          (facts : DeployFacts chain)
          (tag : TagDeployment),
      P (chain_height chain)
        (current_slot chain)
        (finalized_height chain)
        (account_address contract_acc)
        (build_deployment_info origin from 0)
        (* result *)
        0
        []
        []
        []) ->

  (* Transfer/call/deploy to someone else *)
  (forall height slot fin_height caddr dep_info (* cstate *)
          balance out_act out_acts inc_calls prev_out_txs tx
          (IH : P height slot fin_height caddr dep_info (* cstate *) balance
                  (out_act :: out_acts) inc_calls prev_out_txs)
          (tx_from_caddr : tx_from tx = caddr)
          (tx_amount_eq : tx_amount tx = act_body_amount out_act)
          (tx_act_match :
             match out_act with
             | act_transfer to amount =>
               tx_to tx = to /\ tx_amount tx = amount /\
               (tx_body tx = tx_empty \/ tx_body tx = tx_call None)
             | act_deploy wc =>
               tx_amount tx = 0 /\ tx_body tx = tx_deploy wc
             | act_call to msg =>
               tx_to tx = to /\ tx_amount tx = 0 /\ tx_body tx = tx_call (Some msg)
             | act_special_call to body =>
               tx_to tx = to /\  tx_body tx = tx_special_call body
             end)
          (tag : TagOutgoingAct),
      P height slot fin_height caddr dep_info (* cstate *) (balance - act_body_amount out_act)
        out_acts inc_calls (tx :: prev_out_txs)) ->

  (* Non-recursive call *)
  (forall chain accounts contract_acc from_acc dep_info (* prev_state *) msg
          prev_out_queue prev_inc_calls prev_out_txs
          (* new_state *) new_acts
          (from_other : account_address from_acc <> account_address contract_acc)
          (facts : CallFacts chain accounts (* prev_state *) prev_out_queue)
          (IH : P (chain_height chain) (current_slot chain) (finalized_height chain)
                  (account_address contract_acc) dep_info (* prev_state *)
                  (account_balance contract_acc)
                  prev_out_queue prev_inc_calls prev_out_txs)
          (process_some : process contract chain accounts msg =
                          Ok tt)
          (tag : TagNonrecursiveCall),
      P (chain_height chain)
        (current_slot chain)
        (finalized_height chain)
        (account_address contract_acc)
        dep_info
        (* new_state *)
        (account_balance contract_acc)
        (new_acts ++ prev_out_queue)
        (build_call_info (account_address from_acc) (account_address from_acc) 0 msg :: prev_inc_calls)
        prev_out_txs) ->

  (* Recursive call *)
  (forall chain accounts from_acc contract_acc dep_info (* prev_state *) msg
          head prev_out_queue prev_inc_calls prev_out_txs
          (* new_state *) new_acts
          (from_self : account_address from_acc = account_address contract_acc)
          (facts : CallFacts chain accounts (* prev_state *) (head :: prev_out_queue))
          (IH : P (chain_height chain) (current_slot chain) (finalized_height chain)
                  (account_address from_acc) dep_info (* prev_state *)
                  (account_balance from_acc)
                  (head :: prev_out_queue) prev_inc_calls prev_out_txs)
          (action_facts :
             match head with
             | act_transfer to amount => to = account_address contract_acc /\
                                         (* amount = ctx_amount ctx /\ *)
                                         amount > 0 /\
                                         msg = None
             | act_call to msg_ser => to = account_address contract_acc /\
                                             msg <> None /\
                                             deserialize msg_ser = msg
             | _ => False
             end)
          (receive_some : process contract chain accounts msg =
                          Ok tt)
          (tag : TagRecursiveCall),
      P (chain_height chain)
        (current_slot chain)
        (finalized_height chain)
        (account_address contract_acc)
        dep_info
        (* new_state *)
        (account_balance contract_acc)
        (new_acts ++ prev_out_queue)
        (build_call_info (account_address from_acc) (account_address contract_acc) 0 msg :: prev_inc_calls)
        (build_tx (account_address from_acc)
                  (account_address from_acc)
                  (account_address contract_acc)
                  0
                  (tx_call (match head with
                            | act_call _ msg => Some msg
                            | _ => None
                            end)) :: prev_out_txs)) ->

  (* Queue permutation *)
  (forall height slot fin_height
          caddr dep_info (* cstate *) balance
          out_queue inc_calls out_txs
          out_queue'
          (IH : P height slot fin_height caddr dep_info (* cstate *) balance
                  out_queue inc_calls out_txs)
          (perm : Permutation out_queue out_queue')
          (tag : TagPermuteQueue),
      P height slot fin_height
        caddr dep_info (* cstate *) balance out_queue' inc_calls out_txs) ->

  forall bstate caddr (trace : ChainTrace empty_state bstate),
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists dep (* cstate *) inc_calls,
      deployment_info trace caddr = Some dep /\
(*       contract_state bstate caddr = Some cstate /\ *)
      incoming_calls Msg trace caddr = Some inc_calls /\
      P (chain_height bstate)
        (current_slot bstate)
        (finalized_height bstate)
        caddr
        dep
        (* cstate *)
        (env_account_balances bstate caddr)
        (outgoing_acts bstate caddr)
        inc_calls
        (outgoing_txs trace caddr).
Proof.
  intros establish_facts
         add_block_case
         init_case
         transfer_case
         nonrecursive_call_case
         recursive_call_case
         permute_queue_case
         bstate caddr trace contract_deployed.
  assert (address_is_contract caddr = true) as is_contract
      by (eapply contract_addr_format; eauto).
  unfold contract_state in *.
  remember empty_state; induction trace as [|? ? ? ? IH];
    intros; subst; try solve [cbn in *; congruence].
  specialize (establish_facts mid to ltac:(auto) ltac:(auto) tag_facts).
  destruct_chain_step;
    [|destruct_action_eval; try rewrite_environment_equiv; cbn in *| |].
  - (* New block *)
    clear init_case recursive_call_case nonrecursive_call_case permute_queue_case.
    rewrite_environment_equiv.
    cbn in *.
    specialize_hypotheses.
    destruct IH as (depinfo' (* & cstate' *) & inc_calls' & -> (* & ? *) & -> & ?).
    exists depinfo', (* cstate', *) inc_calls'.
    rewrite_environment_equiv.
    repeat split; auto.
    inversion valid_header.
    cbn in *.
    destruct_address_eq; try congruence.
    rewrite outgoing_acts_after_block_nil by auto.
    unfold outgoing_acts in *; rewrite queue_prev in *; cbn in *.
    eapply add_block_case; try constructor.
    + apply establish_facts.
    + assumption.
  - (* Evaluation: transfer *)
    clear add_block_case init_case recursive_call_case nonrecursive_call_case permute_queue_case.
    specialize_hypotheses. 
    destruct IH as (depinfo' (* & cstate' *) & inc_calls' & -> (* & ? *) & -> & ?).
    exists depinfo', (* cstate', *) inc_calls'.
    rewrite_environment_equiv.
    repeat split; auto.
    rewrite (address_eq_sym from_addr) in *.
    cbn in *.
    (* Transfer cannot be to contract as that would be a
    call. Resolve this now. *)
    destruct (address_eqb_spec caddr to_addr) as [->|];
      cbn in *; try congruence.

    unfold outgoing_acts in *.
    rewrite queue_prev, queue_new in *.
    match goal with
    | [ H : act = _ |- _ ] => rewrite H in *
    end.
    subst.
    cbn in *.
    rewrite (address_eq_sym (account_address from_acc)) in *.
    destruct (address_eqb_spec caddr (account_address from_acc)) as [<-|];
      cbn in *.
    + (* Transfer from contract *)
      remember (act_transfer _ _) as out_act.
      replace (-amount + env_account_balances mid caddr) with
          (env_account_balances mid caddr - act_body_amount out_act) by
          (subst; cbn; lia).
      subst.
      apply transfer_case; auto.
    + (* Irrelevant transfer *)
      auto.
  - (* Evaluation: Deploy *)
    clear add_block_case recursive_call_case nonrecursive_call_case permute_queue_case.
    
    rewrite (address_eq_sym to_addr caddr) in *.
    destruct (address_eqb_spec caddr to_addr) as [->|]; cbn in *.
    + (* Deployment of this contract *)
      replace wc with (contract : WeakContract) in * by congruence.
      match goal with
      | [ H : wc_process _ _ _ _ = Ok _ |- _ ] =>
        destruct (wc_process_strong H) as (msg_strong & deser_msg_eq & process)
      end.
(*       rewrite deser_msg_eq in *. *)
      exists (build_deployment_info origin from_addr amount),
(*              result_strong, *)
             [].
      rewrite_environment_equiv; cbn.
(*       rewrite address_eq_refl. *)
      cbn.
(*       rewrite deserialize_serialize. *)
      assert (incoming_calls Msg trace to_addr = Some [])
        by (apply undeployed_contract_no_in_calls; auto).
      unfold incoming_calls in *; rewrite is_contract in *.
      repeat split; cbn in *; subst; auto.
      unfold outgoing_acts.
      rewrite queue_new.
      cbn.
(*       rewrite (address_eq_sym to_addr) in *. *)
      fold (outgoing_txs trace (account_address to_acc)).
      pose proof (undeployed_contract_no_out_queue
                    (account_address to_acc) mid ltac:(auto) ltac:(auto) ltac:(auto)) as queue_ne_to.
      rewrite queue_prev in queue_ne_to.
      inversion_clear queue_ne_to as [|? ? from_ne_to rest_ne_to].
      cbn in from_ne_to.
      cbn in *.
      rewrite (address_eq_ne (account_address from_acc) (account_address to_acc)) by (destruct_address_eq; auto).
      rewrite Forall_false_filter_nil by assumption.
      rewrite undeployed_contract_no_out_txs, undeployed_contract_balance_0 by auto. auto.
(*       remember (build_ctx _ _ _ _ _) as ctx. *)
(*       replace origin with (ctx_origin ctx) by (subst; auto). *)
(*       replace from_addr with (ctx_from ctx) by (subst; auto). *)
(*       replace to_addr with (ctx_contract_address ctx) by (subst; auto). *)
(*       replace amount with (ctx_amount ctx) by (subst; auto). *)
(*       rewrite Z.add_0_r. *) (* Print map. cbn in *. *)
(*       apply init_case;auto. *)
    + (* Deployment of other contract, might be by this contract. *)
      specialize_hypotheses.
      destruct IH as (depinfo & (* cstate & *) inc_calls & -> (* & ? *) & -> & ?).
      exists depinfo, (* cstate, *) inc_calls.
      rewrite_environment_equiv; cbn.
(*       rewrite address_eq_ne by auto. *)
      repeat split; auto.
(*       rewrite (address_eq_sym caddr). *)
      unfold outgoing_acts in *.
      rewrite queue_prev, queue_new in *.
      match goal with
      | [ H : act = _ |- _ ] => rewrite H in *
      end.
      subst new_acts.
      cbn in *.
      fold (outgoing_txs trace caddr).
      destruct_address_eq; subst; cbn in *; auto.
      (* This contract deploys other contract *) Print act_deploy.
      remember (act_deploy _) as abody.
      replace (env_account_balances mid (account_address from_acc))
        with (env_account_balances mid (account_address from_acc) - act_body_amount abody)
        by (subst; cbn; lia).
      subst.
      apply transfer_case; auto.
  - (* Evaluation: Call *)
    clear add_block_case init_case permute_queue_case.
    specialize_hypotheses.
    match goal with
      | [ H : act = _ |- _ ] => rewrite H in *
    end.
    subst new_acts.
    destruct IH as (depinfo & (* cstate & *) inc_calls & -> (* & ? *) & -> & IH).
    unfold outgoing_acts in *.
    rewrite queue_prev, queue_new in *.
    cbn in *.
    rewrite filter_app, filter_map, map_app, map_map; cbn in *.
    destruct (address_eqb_spec to_addr caddr) as [->|].
    + (* Call to contract *)
      replace wc with (contract : WeakContract) in * by congruence.
      destruct (wc_process_strong ltac:(eassumption))
        as (msg_strong & deser_msg_eq & process).
      replace (env_contract_states mid caddr) with (Some prev_state) in * by auto.
      cbn in *.
(*       replace prev_state_strong with cstate in * by congruence; clear prev_state_strong. *)
      exists depinfo.
      exists (build_call_info origin from_addr amount msg_strong :: inc_calls).
      rewrite_environment_equiv.
      cbn.
      rewrite address_eq_refl.
      cbn.
(*       rewrite deserialize_serialize. *)
      repeat split; auto.
      {
        destruct msg_strong as [msg_strong|], msg as [msg|];
          try solve [cbn in *; congruence].
        now replace (deserialize msg) with (Some msg_strong) by auto.
      }

      rewrite (address_eq_sym caddr), filter_true, map_id.

      destruct (address_eqb_spec from_addr caddr) as [->|?]; cbn in *.
      all: try rewrite (address_eq_refl caddr) in *.
      * (* Recursive call *)
(*         remember (build_ctx _ _ _ _ _) as ctx. *)
        pose proof
            (recursive_call_case
               (transfer_balance (account_address from_acc) (account_address from_acc) amount mid)
                accounts from_acc from_acc depinfo (* cstate *) msg_strong
               (match msg with
                | Some msg => act_call (account_address from_acc) (* amount *) msg
                | None => act_transfer (account_address from_acc) amount
                end)) as case.
(*         subst ctx. *)
        cbn in case.
        replace (-amount + (amount + env_account_balances mid caddr))
          with (env_account_balances mid caddr)
          in * by lia.
        destruct msg_strong as [msg_strong|], msg as [msg|];
          cbn in *; try congruence. 
       Admitted.
      (* * (* Someone else calls contract *)
(*         remember (build_ctx _ _ _ _ _) as ctx. *)
        pose proof
            (nonrecursive_call_case
               (transfer_balance (account_address from_acc) (account_address from_acc) amount mid)
               accounts from_acc from_acc depinfo (* cstate *) msg_strong) as case.
(*         subst ctx. *)
        cbn in case.
(*         rewrite (address_eq_ne caddr (account_address from_acc)) in * by (subst; auto). *)
        auto. replace (amount + env_account_balances mid caddr - amount)
          with (env_account_balances mid caddr) in case
          by lia.
        fold (outgoing_txs trace caddr).
        apply case; auto.
    + (* Call to other contract *)
      exists depinfo, (* cstate, *) inc_calls.
      rewrite_environment_equiv.
      rewrite filter_false.
      cbn. 
(*       rewrite address_eq_ne by auto. *)
      rewrite (address_eq_sym caddr).
      destruct (address_eqb_spec from_addr caddr) as [->|?].
      * (* Call from us to other contract *)
        repeat split; auto.
        destruct (address_eqb_spec to_addr caddr) as [->|?]; auto.
        ** cbn in *. contradiction n. auto.
        ** cbn in *. auto. 
        fold (outgoing_txs trace caddr).
        cbn in *.
        destruct msg as [msg|].
        1: remember (act_call _ _) as abody.
        2: remember (act_transfer _ _) as abody.
        1, 2: replace (-amount + env_account_balances mid caddr)
          with (env_account_balances mid caddr - act_body_amount abody)
          by (subst; cbn; lia).
        1, 2: subst; apply transfer_case; auto.
      * (* Irrelevant call. *)
        fold (outgoing_txs trace caddr).
        auto.
  - (* Invalid User Action *)
    rewrite_environment_equiv.
    destruct IH as (depinfo & cstate & inc_calls & ? & ? & ? & IH); auto.
    exists depinfo, cstate, inc_calls.
    repeat split; rewrite_environment_equiv; auto.
    assert (outgoing_acts_eq : outgoing_acts mid caddr = outgoing_acts to caddr).
    { unfold outgoing_acts.
      setoid_rewrite queue_new.
      setoid_rewrite queue_prev.
      f_equal.
      cbn.
      unfold act_is_from_account in act_from_acc.
      destruct_address_eq; easy.
    }
    rewrite outgoing_acts_eq in IH.
    cbn.
    now fold (outgoing_txs trace caddr).
  - (* Permutation *)
    rewrite_environment_equiv.
    specialize_hypotheses.
    destruct IH as (depinfo & cstate & inc_calls & ? & ? & ? & IH).
    exists depinfo, cstate, inc_calls.
    rewrite_environment_equiv.
    cbn.
    repeat split; auto.
    unfold outgoing_acts in *.
    fold (outgoing_txs trace caddr).
    apply permute_queue_case with
        (out_queue := map act_body
                          (filter (fun a => (act_from a =? caddr)%address)
                                  (chain_state_queue mid))); auto.
    now apply Permutation_map, Permutation_filter. 
Qed. *)


End Theories.
End Trace.
End Semantics.

Inductive ActionEvaluationError :=
| amount_negative (* amount is negative *)
| amount_too_high (* sender does not have enough money *)
| no_such_contract (* there is not contract at that address *)
| too_many_contracts (* cannot generate fresh address for new contract *)
| init_failed (* contract init function failed *)
| receive_failed (* contract receive function failed *)
| internal_error. (* unexpected internal error *)



Inductive AddBlockError :=
| invalid_header (* header for next block is invalid *)
| invalid_root_action (act : Action) (* a specified root action is invalid *)
| origin_from_mismatch (act : Action) (* origin and from addresses do not match for an action in a new block *)
| action_evaluation_depth_exceeded (* out of fuel while evaluating actions recursively *)
| action_evaluation_error (* error when evaluating single action *)
    (act : Action)
    (err : ActionEvaluationError).

Class ChainBuilderType :=
  build_builder {
    builder_type : Type;

    builder_initial : builder_type;

    builder_env : builder_type -> Environment;

    builder_add_block
      (builder : builder_type)
      (header : BlockHeader)
      (actions : list Action) :
      result builder_type AddBlockError;

    builder_trace (builder : builder_type) :
      ChainTrace empty_state (build_chain_state (builder_env builder) []);
  }.

Global Coercion builder_type : ChainBuilderType >-> Sortclass.
Global Coercion builder_env : builder_type >-> Environment.

(*     next_account_spec :
      forall (lacc : SliceAccountInformation) (index : Z), Bool.reflect (result_of_option (nth_error lacc (Z.to_nat index)) InvalidAccountData) (next_account lacc index);
 *)    

Class ChainHelpers :=
  build_helpers {
    next_account : SliceAccountInformation -> Z -> result AccountInformation ProgramError;
    deser_data (A : Type) : SerializedValue -> result A ProgramError;
    deser_data_account (A : Type) : AccountInformation -> result A ProgramError;
    ser_data {A : Type} : A -> SerializedValue;
    ser_data_account {A : Type} : A -> AccountInformation -> result unit ProgramError;
    exec_act : WrappedActionBody -> result unit ProgramError;
  }.

Global Opaque next_account deser_data deser_data_account ser_data ser_data_account exec_act.

End Blockchain.

Ltac destruct_chain_step :=
  match goal with
  | [step: ChainStep _ _ |- _] =>
    destruct step as
        [?header ?queue_prev ?valid_header ?acts_from_accs ?origin_correct ?env_eq|
         ?act ?acts ?new_acts ?queue_prev ?eval ?queue_new|
         ?act ?acts ?env_eq ?queue_prev ?queue_new ?act_from_acc ?no_eval|
         ?env_eq ?perm]
  end.

(* Print ActionEvaluation. *)

Ltac destruct_action_eval :=
  match goal with
  | [eval: ActionEvaluation _ _ _ _ |- _] =>
    destruct eval as
      [?origin ?from_addr ?to_addr ?origin_acc ?from_acc ?to_acc ?amount ?amount_nonnegative ?enough_balance
        ?origin_acc_eq ?from_acc_eq ?to_acc_eq ?to_addr_not_contract ?act_eq ?env_eq ?new_acts_eq |
       ?origin ?from_addr ?to_addr ?origin_acc ?from_acc ?to_acc ?amount ?wc ?state ?accounts ?res ?amount_nonnegative
        ?enough_balance ?origin_acc_eq ?from_acc_eq ?to_acc_eq ?to_addr_contract ?not_deployed
        ?act_eq ?process_some ?env_eq ?new_acts_eq |
       ?origin ?from_addr ?to_addr ?origin_acc ?from_acc ?to_acc ?amount ?wc ?accounts ?msg ?prev_state ?new_state ?resp_acts 
        ?res ?amount_nonnegative ?enough_balance ?origin_acc_eq ?from_acc_eq ?to_acc_eq ?deployed ?deployed_state ?act_eq
        ?process_some ?new_acts_eq ?env_eq | 
       ?origin ?from_addr ?to_addr ?origin_acc ?from_acc ?to_acc ?body ?amount ?wc ?amount_nonnegative
        ?enough_balance ?origin_acc_eq ?from_acc_eq ?to_acc_eq ?deployed ?act_eq ?body_eval ]
  end.

(* Print SpecialCallBodyEvaluation. *)

Ltac destruct_special_body_eval :=
  match goal with
  | [body_eval: SpecialCallBodyEvaluation _ _ _ _ |- _] =>
    destruct body_eval as
      [?origin ?from_addr ?to_addr ?acc_addr ?new_owner_addr ?wc ?owner
       ?deployed ?env_eq ?new_acts |
       ?origin ?from_addr ?to_addr ?wc ?deployed ?env_eq ?new_acts |
       ?origin ?from_addr ?env_eq ?new_acts]
  end.

Ltac rewrite_environment_equiv :=
  match goal with
  | [eq: EnvironmentEquiv _ _ |- _] => rewrite eq in *
  end.

(* Not working *)
Local Ltac generalize_contract_statement_aux
      bstate caddr trace is_deployed (* Setup *) Msg State post :=
  let P := fresh "P" in
  evar (P : forall (chain_height : nat) (current_slot : nat) (finalized_height : nat)
                   (caddr : Address) (deployment_info : DeploymentInfo)
                   (* (cstate : State) *) (balance : Amount)
                   (outgoing_actions_queued : list ActionBody)
                   (incoming_calls_seen : list (ContractCallInfo Msg))
                   (outgoing_txs_seen : list Tx),
           Prop);
  let H := fresh "H" in
  enough (H: exists (dep : DeploymentInfo)
                    (cstate : State)
                    (inc_calls : list (ContractCallInfo Msg)),
             deployment_info trace caddr = Some dep /\
(*              contract_state bstate caddr = Some cstate /\ *)
             incoming_calls Msg trace caddr = Some inc_calls /\
             P (chain_height bstate)
               (current_slot bstate)
               (finalized_height bstate)
               caddr dep (* cstate *)
               (env_account_balances bstate caddr)
               (outgoing_acts bstate caddr)
               inc_calls (outgoing_txs trace caddr));
  [let depinfo := fresh "depinfo" in
(*    let cstate := fresh "cstate" in *)
   let inc_calls := fresh "inc_calls" in
   let depinfo_strong := fresh "depinfo_strong" in
   let cstate_strong := fresh "cstate_strong" in
   let inc_calls_strong := fresh "inc_calls_strong" in
   let provenP := fresh "provenP" in
   destruct H as (depinfo & (* cstate & *)inc_calls &
                  depinfo_strong & cstate_strong & inc_calls_strong & provenP);
   repeat
     match goal with
     | [|- exists _ : DeploymentInfo, _] => exists depinfo
(*      | [|- exists _ : State, _] => exists cstate *)
     | [|- exists _ : list (ContractCallInfo Msg), _] => exists inc_calls
     | [|- ?a /\ ?b] => refine (conj depinfo_strong _)
     | [|- ?a /\ ?b] => refine (conj cstate_strong _)
     | [|- ?a /\ ?b] => refine (conj inc_calls_strong _)
     end;
   pattern (chain_height bstate), (current_slot bstate), (finalized_height bstate),
           caddr, depinfo, (* cstate,  *)(env_account_balances bstate caddr),
           (outgoing_acts bstate caddr), inc_calls, (outgoing_txs trace caddr);
   match goal with
   | [|- ?f _ _ _ _ _ _ _ _ _ _] => instantiate (P := f); exact provenP
   end
  | post bstate caddr trace is_deployed Msg State P ].

Local Ltac generalize_contract_statement_with_post post :=
  intros;
  match goal with
  | [bstate : ChainState, caddr : Address |- _] =>
    try
      match goal with
      | [is_reachable : reachable bstate |- _] =>
        let trace := fresh "trace" in
        destruct is_reachable as [trace]
      end;
    match goal with
      [trace : ChainTrace empty_state bstate,
               is_deployed : env_contracts (_ bstate) caddr =
                             Some (contract_to_weak_contract ?c) |- _] =>
      match type of c with
      | Contract ?Setup ?Msg ?State =>
        generalize_contract_statement_aux bstate caddr trace
                                          is_deployed Setup Msg State post
      end
    end
  end.

Ltac generalize_contract_statement :=
  generalize_contract_statement_with_post
    ltac:(fun _ _ _ is_deployed _ _ _ _ => revert is_deployed).

Ltac contract_induction :=
  generalize_contract_statement_with_post
    ltac:(fun bstate caddr _ is_deployed Msg State P =>
       revert is_deployed;
       let AddBlockFacts := fresh "AddBlockFacts" in
       let DeployFacts := fresh "DeployFacts" in
       let CallFacts := fresh "CallFacts" in
       evar (AddBlockFacts :
               forall (chain_height : nat) (current_slot : nat)
                      (finalized_height : nat) (new_height : nat)
                      (new_slot : nat) (new_finalized_height : nat), Prop);
       evar (DeployFacts : forall (chain : Chain)
                                  (* (accounts : SliceAccountInformation) *), Prop);
       evar (CallFacts : forall (chain : Chain) (accounts : SliceAccountInformation)
                                (* (cstate : State) *) (outgoing_actions : list ActionBody), Prop);
       apply (contract_induction _ AddBlockFacts DeployFacts CallFacts);
       cbv [P]; clear P; cycle 1; clear dependent bstate; clear dependent caddr).

Global Notation "'Please' 'prove' 'your' 'facts'" := TagFacts (at level 100, only printing).
Global Notation "'Please' 'reestablish' 'the' 'invariant' 'after' 'addition' 'of' 'a' 'block'"
  := TagAddBlock (at level 100, only printing).
Global Notation "'Please' 'establish' 'the' 'invariant' 'after' 'deployment' 'of' 'the' 'contract'"
  := TagDeployment (at level 100, only printing).
Global Notation "'Please' 'reestablish' 'the' 'invariant' 'after' 'an' 'outgoing' 'action'"
  := TagOutgoingAct (at level 100, only printing).
Global Notation "'Please' 'reestablish' 'the' 'invariant' 'after' 'a' 'nonrecursive' 'call'"
  := TagNonrecursiveCall (at level 100, only printing).
Global Notation "'Please' 'reestablish' 'the' 'invariant' 'after' 'a' 'recursive' 'call'"
  := TagRecursiveCall (at level 100, only printing).
Global Notation
       "'Please' 'reestablish' 'the' 'invariant' 'after' 'permutation' 'of' 'the' 'action' 'queue'"
  := TagPermuteQueue (at level 100, only printing).


Section LiftTransactionProp.

  Context {BaseTypes : ChainBase}
          {Setup : Type} `{Serializable Setup}
          {Msg : Type} `{Serializable Msg}
          {State : Type} `{Serializable State}.

(** If some property [P] holds for all actions in the output of the receive function, the property can be lifted to all outgoing actions for all reachabile states. *)
Lemma lift_outgoing_acts_prop {P : ActionBody -> Prop}
      (contract : Contract Msg State) (bstate : ChainState) (addr : Address) :
  reachable bstate ->
  (forall chain accounts msg acts result,
      contract.(process) chain accounts msg = Ok result ->
      Forall P acts) ->
  env_contracts bstate addr = Some (contract : WeakContract) ->
  Forall P (outgoing_acts bstate addr).
Proof.
  intros Hr Hc. Admitted.
 (*  contract_induction; intros; cbn in *; auto.
  - inversion_clear IH; auto.
  - apply Forall_app.
    split; auto.
    eauto.
  - apply Forall_app.
    inversion_clear IH.
    split; auto.
    eauto.
  - now rewrite <- perm.
  - instantiate (AddBlockFacts := fun _ _ _ _ _ _ => Logic.True).
    instantiate (DeployFacts := fun _ _ => Logic.True).
    instantiate (CallFacts := fun _ _ _ _ => Logic.True).
    unset_all; subst.
    destruct step; auto.
    destruct a; auto.
Qed. *)

(** If the receive function always returns an empty list of actions,
 the same holds for all reachable states *)
Lemma lift_outgoing_acts_nil (contract : Contract Msg State)
      (bstate : ChainState) (addr : Address) :
  reachable bstate ->
  (forall chain accounts msg (acts : list ActionBody) result,
      contract.(process) chain accounts msg = Ok result ->
      acts = []) ->
  env_contracts bstate addr = Some (contract : WeakContract) ->
  outgoing_acts bstate addr = [].
Proof.
  intros.
  enough (all_false: Forall (fun _ => False) (outgoing_acts bstate addr)) by (now destruct all_false).
  apply (lift_outgoing_acts_prop contract); auto.
  intros.
  erewrite (H3 _ _ _ _ _ ); [constructor|eassumption].
Qed.

(* (** If some property [P] holds for all contract states in the output of the receive function,
  the property can be lifted to all contract states for all reachabile states. *)
Lemma lift_contract_state_prop {P : State -> Prop}
      (contract : Contract Msg State) (bstate : ChainState) (addr : Address) :
  (forall chain accounts msg result_state result_acts,
      contract.(process) chain accounts msg = Some (result_state, result_acts) ->
      P result_state) ->
  (forall chain accounts cstate msg new_cstate acts,
      P cstate ->
      contract.(process) chain accounts (Some cstate) msg = Some (new_cstate, acts) ->
      P new_cstate) ->
  reachable bstate ->
  env_contracts bstate addr = Some (contract : WeakContract) ->
  exists cstate,
    contract_state bstate addr = Some cstate
    /\ P cstate.
Proof.
  intros Hinit Hreceive Hreach.
  contract_induction; intros; cbn in *; auto.
  - now eapply Hinit.
  - now eapply Hreceive.
  - now eapply Hreceive.
  - instantiate (AddBlockFacts := fun _ _ _ _ _ _ => Logic.True).
    instantiate (DeployFacts := fun _ _ => Logic.True).
    instantiate (CallFacts := fun _ _ _ _ => Logic.True).
    unset_all; subst.
    destruct step; auto.
    destruct a; auto.
Qed. *)

(* Lemma lift_dep_info_contract_state_prop {P : DeploymentInfo Setup -> State -> Prop}
      (contract : Contract Setup Msg State) (bstate : ChainState) (addr : Address)
      (trace : ChainTrace empty_state bstate) :
  (forall chain ctx setup result,
      contract.(init) chain ctx setup = Some result ->
      P (build_deployment_info (ctx_origin ctx) (ctx_from ctx) (ctx_amount ctx) setup)
        result) ->
  (forall chain ctx cstate msg new_cstate acts dep,
      P dep cstate ->
      contract.(receive) chain ctx cstate msg = Some (new_cstate, acts) ->
      P dep new_cstate) ->
  env_contracts bstate addr = Some (contract : WeakContract) ->
  exists dep cstate,
      deployment_info Setup trace addr = Some dep /\
      contract_state bstate addr = Some cstate /\
      P dep cstate.
Proof.
  intros Hinit Hreceive.
  contract_induction; intros; cbn in *; auto.
  - now eapply Hinit.
  - now eapply Hreceive.
  - now eapply Hreceive.
  - instantiate (AddBlockFacts := fun _ _ _ _ _ _ => Logic.True).
    instantiate (DeployFacts := fun _ _ => Logic.True).
    instantiate (CallFacts := fun _ _ _ _ => Logic.True).
    unset_all; subst.
    destruct step; auto.
    destruct a; auto.
Qed. *)

End LiftTransactionProp.