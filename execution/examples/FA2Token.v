From Coq Require Import List.
From Coq Require Import Program.Basics.
From Coq Require Import ZArith.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Extras.
From ConCert.Execution Require Import Monads.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution.Examples Require Import Common.

Import ListNotations.
Import RecordSetNotations.

Notation "f 'o' g" := (compose f g) (at level 50).


Require Import FA2Interface.

Section FA2Token.
Context {BaseTypes : ChainBase}.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.
Open Scope N_scope.

(* Any contract that wants to receive callback messages from the FA2 contract
   should have this type as its Msg type. The contract may have other endpoints,
   as composed in the 'other_msg' constructor *)
Inductive FA2ReceiverMsg {Msg' : Type} `{Serializable Msg'} :=
  | receive_balance_of_param : list balance_of_response -> FA2ReceiverMsg
  | receive_total_supply_param : list total_supply_response -> FA2ReceiverMsg
  | receive_metadata_callback : list token_metadata -> FA2ReceiverMsg
  | receive_is_operator : is_operator_response  -> FA2ReceiverMsg
  | receive_permissions_descriptor : permissions_descriptor -> FA2ReceiverMsg
  | other_msg : Msg' -> FA2ReceiverMsg.

(* Transfer hook contracts of the FA2 Contract should use this type as their Msg type *)
Inductive FA2TransferHook {Msg : Type} `{Serializable Msg} :=
  | transfer_hook : transfer_descriptor_param -> FA2TransferHook
  | hook_other_msg : Msg -> FA2TransferHook.

(* The FA2 Endpoints. *)
Inductive Msg :=
  | msg_transfer : list transfer -> Msg
  | msg_set_transfer_hook : set_hook_param -> Msg
  | msg_receive_hook_transfer : transfer_descriptor_param -> Msg
  | msg_balance_of : balance_of_param -> Msg
  | msg_total_supply : total_supply_param -> Msg
  | msg_token_metadata : token_metadata_param -> Msg
  | msg_permissions_descriptor : callback permissions_descriptor -> Msg
  | msg_update_operators : list update_operator -> Msg
  | msg_is_operator : is_operator_param -> Msg
  | msg_create_tokens : token_id -> Msg.

Record TokenLedger :=
  build_token_ledger {
    fungible : bool;
    balances : FMap Address N
}.

Record State :=
  build_state {
    fa2_owner          : Address;
    assets             : FMap token_id TokenLedger;
    operators          : FMap Address (FMap Address operator_tokens);
    permission_policy  : permissions_descriptor;
    tokens             : FMap token_id token_metadata;
    transfer_hook_addr : option Address;
  }.

Record Setup :=
  build_setup {
    setup_total_supply        : list (token_id * N);
    setup_tokens              : FMap token_id token_metadata;
    initial_permission_policy : permissions_descriptor;
    transfer_hook_addr_       : option Address;
  }.

MetaCoq Run (make_setters TokenLedger).
MetaCoq Run (make_setters State).
MetaCoq Run (make_setters Setup).

Section Serialization.

Global Instance setup_serializable : Serializable Setup :=
  Derive Serializable Setup_rect <build_setup>.

Global Instance FA2ReceiverMsg_serializable {Msg : Type} `{serMsg : Serializable Msg} : Serializable (@FA2ReceiverMsg Msg serMsg) :=
  Derive Serializable (@FA2ReceiverMsg_rect Msg serMsg) <
    (@receive_balance_of_param Msg serMsg),
    (@receive_total_supply_param Msg serMsg),
    (@receive_metadata_callback Msg serMsg),
    (@receive_is_operator Msg serMsg),
    (@receive_permissions_descriptor Msg serMsg),
    (@other_msg Msg serMsg)>.

Global Instance FA2TransferHook_serializable {Msg : Type} `{serMsg : Serializable Msg} : Serializable (@FA2TransferHook Msg serMsg) :=
  Derive Serializable (@FA2TransferHook_rect Msg serMsg) <
    (@transfer_hook  Msg serMsg),
    (@hook_other_msg Msg serMsg)>.

Global Instance callback_permissions_descriptor_serializable : Serializable (callback permissions_descriptor) := callback_serializable.

Global Instance msg_serializable : Serializable Msg :=
  Derive Serializable Msg_rect <
    msg_transfer,
    msg_set_transfer_hook,
    msg_receive_hook_transfer,
    msg_balance_of,
    msg_total_supply,
    msg_token_metadata,
    msg_permissions_descriptor,
    msg_update_operators,
    msg_is_operator,
    msg_create_tokens>.

Global Instance TokenLedger_serializable : Serializable TokenLedger :=
  Derive Serializable TokenLedger_rect <build_token_ledger>.

Global Instance state_serializable : Serializable State :=
  Derive Serializable State_rect <build_state>.

End Serialization.


Definition address_balance (token_id : token_id)
                           (addr : Address)
                           (state : State) : N :=
  match FMap.find token_id state.(assets) with
  | Some ledger => with_default 0%N (FMap.find addr ledger.(balances))
  | None => 0%N
  end.

Definition address_has_sufficient_asset_balance (token_id : token_id)
                                                (owner : Address)
                                                (transaction_amount : N)
                                                (state : State)
                                                : option unit :=

  if transaction_amount <=? address_balance token_id owner state
  then Some tt
  else None.

Definition policy_disallows_operator_transfer (policy : permissions_descriptor) : bool :=
  match policy.(descr_operator) with
  | operator_transfer_permitted => false
  | operator_transfer_denied => true
  end.

Definition policy_disallows_self_transfer (policy : permissions_descriptor) : bool :=
  match policy.(descr_self) with
  | self_transfer_permitted => false
  | self_transfer_denied => true
  end .

Definition get_owner_operator_tokens (owner operator : Address)
                                     (state : State)
                                     : option operator_tokens :=
  do operator_tokens <- FMap.find owner state.(operators) ;
  FMap.find operator operator_tokens.

(* Executes a single transfer by returning a new state, if successful. *)
Definition try_single_transfer (caller : Address)
                               (params : transfer)
                               (state : State)
                               : option State :=
  do ledger <- FMap.find params.(transfer_token_id) state.(assets) ;
  let current_owner_balance := address_balance params.(transfer_token_id) params.(from_) state in
  let new_balances := FMap.add params.(from_) (current_owner_balance - params.(amount)) ledger.(balances) in
  let new_balances := FMap.partial_alter (fun balance => Some ((with_default 0 balance) + params.(amount))) params.(to_) new_balances in
  let new_ledger := ledger<|balances := new_balances|> in
  Some (state<|assets ::= FMap.add params.(transfer_token_id) new_ledger|>).

Definition transfer_check_permissions (caller : Address)
                                      (params : transfer)
                                      (policy : permissions_descriptor)
                                      (state : State)
                                      : option unit :=
  (* check for sufficient permissions *)
  do _ <- address_has_sufficient_asset_balance params.(transfer_token_id) params.(from_) params.(amount) state ;
  (* only allow transfers of known token_ids *)
  do _ <- FMap.find params.(transfer_token_id) state.(tokens) ;
  (* if caller is owner of transfer, then check policy if self_transfer is allowed *)
  if (address_eqb caller params.(from_))
  then
    throwIf (policy_disallows_self_transfer policy)
  else
    (* check if policy allows operator transfer *)
    do _ <- throwIf (policy_disallows_operator_transfer policy) ;
    do operators_map <- FMap.find params.(from_) state.(operators) ;
    do op_tokens <- FMap.find caller operators_map ;
    (* check if operator has permission to transfer the given token_id type *)
    match op_tokens with
    | all_tokens => Some tt
    | some_tokens token_ids => if (existsb (fun id => id =? params.(transfer_token_id)) token_ids)
                               then Some tt
                               else None
    end.

(* Executes all transfers in a batch operation and returns a new state if *all*
   transfers were successful. *)
Definition try_transfer (caller : Address)
                        (transfers : list transfer)
                        (state : State)
                        : option State :=
  let check_transfer_iterator state_opt params :=
    do state <- state_opt ;
    do _ <- transfer_check_permissions caller params state.(permission_policy) state;
    try_single_transfer caller params state in
  (* returns the new state if all transfers *can* succeed, otherwise returns None *)
  fold_left check_transfer_iterator transfers (Some state).

(* Forwards the transfer to the hook to approve/reject *)
Definition call_transfer_hook (caller : Address)
                              (caddr : Address)
                              (transfer_hook_addr : Address)
                              (transfers : list transfer)
                              (state : State)
                              : ActionBody :=
  let mk_transfer_descr tr := {|
    transfer_descr_from_ := (tr.(from_));
    transfer_descr_to_ := (tr.(to_));
    transfer_descr_token_id := tr.(transfer_token_id);
    transfer_descr_amount := tr.(amount);
    |} in
  let transfer_decr_param := {|
    transfer_descr_fa2 := caddr;
    transfer_descr_batch := map mk_transfer_descr transfers;
    transfer_descr_operator := caller;
    |} in
  act_call transfer_hook_addr 0%Z (serialize (transfer_hook transfer_decr_param)).

Definition group_transfer_descriptors (params : list transfer_descriptor)
                    : list (list transfer_descriptor) :=
  let trx_map := fold_right (fun trx trx_map =>
  match FMap.find trx.(transfer_descr_from_) trx_map with
  | Some trxs => FMap.add trx.(transfer_descr_from_) (trx :: trxs) trx_map
  | None => FMap.add trx.(transfer_descr_from_) [trx] trx_map
  end
  ) FMap.empty params in
  FMap.values trx_map.

(* Handles incoming transfers:
   - if the contract has a transfer_hook, then it uses the hook
   - otherwise it checks & performs the transfers now *)
Definition handle_transfer (caller : Address)
                           (caddr : Address)
                           (transfers : list transfer)
                           (state : State)
                           : option(State * list ActionBody) :=
  match state.(transfer_hook_addr) with
  (* send call transfer hook (approved transfers will be received in the msg_receive_hook_transfer endpoint) *)
  | Some transfer_hook_addr =>
    let call_hook_act := call_transfer_hook caller caddr transfer_hook_addr transfers state in
    Some (state, [call_hook_act])
  (* if no hook is attached, send transfer message to self, and notify senders of transfer *)
  | None =>
    let mk_transfer_descr tr := {|
      transfer_descr_from_ := tr.(from_);
      transfer_descr_to_ := tr.(to_);
      transfer_descr_token_id := tr.(transfer_token_id);
      transfer_descr_amount := tr.(amount);
    |} in
    let mk_transfer_decr_param batch := {|
      transfer_descr_fa2 := caddr;
      transfer_descr_batch := batch;
      transfer_descr_operator := caller;
    |} in
    let transfer_decr_param := mk_transfer_decr_param (map mk_transfer_descr transfers) in
    let is_from_contract descriptors := existsb (fun descr => address_is_contract descr.(transfer_descr_from_)) descriptors in
    let trx_descriptors_grouped := (group_transfer_descriptors (map mk_transfer_descr transfers)) in
    let self_transfer_act := act_call caddr 0%Z (serialize (msg_receive_hook_transfer transfer_decr_param)) in

    (* let mk_sender_hook_act descr_param := act_call descr_param.(transfer_descr_operator) 0%Z (@serialize _ _ (tokens_sent descr_param)) in *)
    let mk_sender_hook_act trx :=
      match trx.(sender_callback_addr) with
      | Some callback_addr =>
        let descr := mk_transfer_decr_param [mk_transfer_descr trx] in
        Some (act_call callback_addr 0%Z (@serialize fa2_token_sender _ (tokens_sent descr)))
      | None => None
      end in
    let sender_hook_acts := fold_right (fun act_opt acc =>
      match act_opt with
      | Some act => act :: acc
      | None => acc
      end
    ) [] (map mk_sender_hook_act transfers) in
    (* If no sender callbacks need to be made, just perform transfers now *)
    if Nat.eqb (length sender_hook_acts) 0%nat then
      option_map (fun new_state => (new_state, [])) (try_transfer caller transfers state)
    else
      (* Notice that sender hooks are invoked before the transfer *)
      Some (state, sender_hook_acts ++ [self_transfer_act])
  end.

Open Scope bool_scope.
Definition mk_transfer_from_decr descr :=
{|
  from_ := descr.(transfer_descr_from_);
  to_ := descr.(transfer_descr_to_);
  transfer_token_id := descr.(transfer_descr_token_id);
  amount := descr.(transfer_descr_amount);
  sender_callback_addr := None (* Some param.(transfer_descr_operator) *)
|}.

Definition handle_transfer_hook_receive (caller : Address)
                                        (param : transfer_descriptor_param)
                                        (self_addr : Address)
                                        (state : State)
                                        : option State :=
  (* check if caller is current hook or self - only hook or self is allowed to call this endpoint *)
  do _ <- if (match state.(transfer_hook_addr) with
          | Some hook_addr => ((address_eqb caller hook_addr) || (address_eqb caller self_addr))
          | None => (address_eqb caller self_addr)
          end)
          then Some tt
          else None  ;
  let transfers := map mk_transfer_from_decr param.(transfer_descr_batch) in
  try_transfer param.(transfer_descr_operator) transfers state.
Close Scope bool_scope.

(* create a 'balance_of' action to send to the callback address *)
Definition get_balance_of_callback (param : balance_of_param)
                                   (state : State)
                                   : ActionBody :=
  let bal_req_iterator (bal_req : balance_of_request) :=
    let owner_bal := address_balance bal_req.(bal_req_token_id) bal_req.(owner) state in
    Build_balance_of_response bal_req owner_bal in
  let responses := map bal_req_iterator param.(bal_requests) in
  let response_msg := serialize (receive_balance_of_param responses) in
  act_call param.(bal_callback) 0%Z response_msg .

(* create a 'total_supply' action to send to the callback address *)
Definition get_total_supply_callback (param : total_supply_param)
                                     (state : State)
                                     : ActionBody :=
  let token_id_balance (token_id : token_id) : N :=
    match FMap.find token_id state.(assets) with
    | Some ledger => fold_left N.add (FMap.values ledger.(balances)) 0%N
    | None => 0%N
    end in
  let mk_response (token_id : token_id) : total_supply_response := Build_total_supply_response token_id (token_id_balance token_id) in
  let responses := map mk_response param.(supply_param_token_ids) in
  let response_msg := serialize (receive_total_supply_param responses) in
  act_call param.(supply_param_callback) 0%Z response_msg.

(* Updates operators if policy allows it, and if the caller is the owner. *)
Definition update_operators (caller : Address)
                            (updates : list update_operator)
                            (state : State)
                            : option State :=
  (* If policy doesn't allow operator transfer, then this operation fails *)
  do _ <- throwIf (policy_disallows_operator_transfer state.(permission_policy)) ;
  let exec_add params (state_opt : option State) : option State :=
    do state_ <- state_opt ;
    (* only the owner of the token is allowed to update their operators *)
    if (negb (address_eqb caller params.(op_param_owner)))
    then None
    else
      let operator_tokens : FMap Address operator_tokens := with_default FMap.empty (FMap.find caller state_.(operators)) in
      (* Add new operator *)
      let operator_tokens := FMap.add params.(op_param_operator) params.(op_param_tokens) operator_tokens in
      Some (state_<| operators ::= FMap.add caller operator_tokens |>) in
  let exec_update state_ op := match op with
                               | add_operator params => exec_add params state_
                               | remove_operator params => exec_add params state_
                               end in
  (fold_left exec_update updates (Some state)).

Definition operator_tokens_eqb (a b : operator_tokens) : bool :=
  match (a, b) with
  | (all_tokens, all_tokens) => true
  | (some_tokens a', some_tokens b') =>
    let fix my_list_eqb l1 l2 :=
      match (l1, l2) with
      | (x :: l1, y :: l2) => if x =? y
                              then my_list_eqb l1 l2
                              else false
      | ([], []) => true
      | _ => false
      end in my_list_eqb a' b'
  | _ => false
  end.

Definition get_is_operator_response_callback (params : is_operator_param)
                                             (state : State)
                                             : option (State * list ActionBody) :=
  (* if policy doesn't allow operator transfers, then this operation will fail *)
  do _ <- throwIf (policy_disallows_operator_transfer state.(permission_policy)) ;
  let operator_params := params.(is_operator_operator) in
  let operator_tokens_opt := get_owner_operator_tokens operator_params.(op_param_owner) operator_params.(op_param_operator) in
  let is_operator_result := match operator_tokens_opt state with
                            (* check if operator_tokens from the params and from the state are equal *)
                            | Some op_tokens => operator_tokens_eqb op_tokens operator_params.(op_param_tokens)
                            | None => false
                            end in
  let response : is_operator_response := {| operator := operator_params; is_operator := is_operator_result |} in
  let act := act_call params.(is_operator_callback) 0%Z (serialize (receive_is_operator response)) in
  Some (state, [act]).

Definition get_permissions_descriptor_callback (caller : Address) (state : State) : ActionBody :=
  let response := serialize (receive_permissions_descriptor state.(permission_policy)) in
  act_call caller 0%Z response.

Definition try_set_transfer_hook (caller : Address)
                                 (params : set_hook_param)
                                 (state : State)
                                 : option State :=
  (* only owner can set transfer hook *)
  do _ <- throwIf (negb (address_eqb caller state.(fa2_owner))) ;
  Some (state<| transfer_hook_addr :=  Some params.(hook_addr)|>
             <| permission_policy  := params.(hook_permissions_descriptor) |>).

Definition get_token_metadata_callback (param : token_metadata_param)
                                       (state : State)
                                       : ActionBody :=
  let token_ids := param.(metadata_token_ids) in
  let state_tokens := state.(tokens) in
  let metadata_list : list token_metadata := fold_right (fun id acc =>
      match FMap.find id state_tokens with
      | Some metadata => metadata :: acc
      | None => acc
      end
    ) [] token_ids in
  let response := serialize (receive_metadata_callback metadata_list) in
  act_call param.(metadata_callback) 0%Z response.

(* creates some tokens with a fixed exchange ratio of 1:100 *)
Definition try_create_tokens (caller : Address)
                             (amount : Amount)
                             (tokenid : token_id)
                             (state : State)
                             : option State :=
  let exchange_rate := 100%Z in
  do ledger <- FMap.find tokenid state.(assets) ;
  (* only allow amounts > 0 *)
  do _ <- throwIf (Z.leb amount 0%Z) ;
  let amount := Z.to_N (amount * exchange_rate) in
  let caller_bal := with_default 0 (FMap.find caller ledger.(balances)) in
  let new_balances := FMap.add caller (caller_bal + amount) ledger.(balances) in
  let new_ledger := ledger<| balances := new_balances |> in
  Some (state<| assets ::=  FMap.add tokenid new_ledger |>).


Open Scope Z_scope.
Definition receive (chain : Chain)
                    (ctx : ContractCallContext)
                   (state : State)
                   (maybe_msg : option Msg)
                   : option (State * list ActionBody) :=
  let sender := ctx.(ctx_from) in
  let caddr := ctx.(ctx_contract_address) in
  let without_actions := option_map (fun new_state => (new_state, [])) in
  let without_statechange acts := Some (state, acts) in
  (* Only 'create_token' messages are allowed to carry money *)
  if ctx.(ctx_amount) >? 0
  then match maybe_msg with
  | Some (msg_create_tokens tokenid) => without_actions (try_create_tokens sender ctx.(ctx_amount) tokenid state)
  | _ => None
  end
  else match maybe_msg with
  | Some (msg_transfer transfers) => handle_transfer sender caddr transfers state
  | Some (msg_receive_hook_transfer param) => without_actions (handle_transfer_hook_receive sender param caddr state)
  | Some (msg_is_operator params) => get_is_operator_response_callback params state
  | Some (msg_balance_of params) => without_statechange [get_balance_of_callback params state]
  | Some (msg_total_supply params) => without_statechange [get_total_supply_callback params state]
  | Some (msg_permissions_descriptor _) => without_statechange [get_permissions_descriptor_callback sender state]
  | Some (msg_token_metadata param) => without_statechange [get_token_metadata_callback param state]
  | Some (msg_update_operators updates) => without_actions (update_operators sender updates state)
  | Some (msg_set_transfer_hook params) => without_actions (try_set_transfer_hook sender params state)
  | _ => None
  end.

Definition map_values_FMap {A B C: Type}
                      `{countable.Countable A}
                      `{base.EqDecision A}
                       (f : B -> C)
                       (m : FMap A B)
                       : FMap A C :=
  let l := FMap.elements m in
  let mapped_l := List.map (fun '(a, b) => (a, f b)) l in
  FMap.of_list mapped_l.

Definition init (chain : Chain)
                (ctx : ContractCallContext)
                (setup : Setup) : option State :=
  (* setup ledgers with empty balance for each initial token id *)
  let assets' := map_values_FMap (fun _ =>
    build_token_ledger false FMap.empty
  ) setup.(setup_tokens) in
  Some {| permission_policy := setup.(initial_permission_policy);
          fa2_owner := ctx.(ctx_from);
          transfer_hook_addr := setup.(transfer_hook_addr_);
          assets := assets';
          operators := FMap.empty;
          tokens := setup.(setup_tokens) |}.

Definition contract : Contract Setup Msg State :=
  build_contract init receive.

End FA2Token.
