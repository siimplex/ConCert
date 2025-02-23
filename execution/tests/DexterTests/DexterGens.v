From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Containers.
From ConCert.Execution.Examples Require Import FA2Token.
From ConCert.Execution.QCTests Require Import Dexter.

From QuickChick Require Import QuickChick. Import QcNotation.
From ConCert.Execution.QCTests Require Import TestUtils.
From ConCert.Execution.QCTests Require Import TraceGens.
From ConCert.Execution.QCTests Require Import DexterPrinters.
From Coq Require Import ZArith List. Import ListNotations.
(* For monad notations *)
From ExtLib.Structures Require Import Monads.
Import MonadNotation. Open Scope monad_scope.

Module Type DexterTestsInfo.
  Parameter fa2_contract_addr : Address.
  Parameter dexter_contract_addr : Address.
  Parameter exploit_contract_addr : Address.
  Parameter gAccountAddress : G Address.
  Parameter gAccountAddrWithout : list Address -> GOpt Address.
End DexterTestsInfo.

Module DexterGens (Info : DexterTestsInfo).
Import Info.

Arguments SerializedValue : clear implicits.
Arguments deserialize : clear implicits.
Arguments serialize : clear implicits.


(* --------------------- FA2 Contract Generators --------------------- *)
Section DexterContractGens.

Definition gTokensToExchange (balance : N) : G (option N) :=
  if N.eqb 0%N balance
  then returnGen None
  else
    amount <- choose (0%N, balance) ;;
    returnGenSome amount.

Definition gTokenExchange  (state : FA2Token.State) : G (option (Address * Dexter.Msg)):=
  let has_balance p :=
    let ledger := snd p in
    0 <? FMap.size ledger.(balances) in
  '(tokenid, ledger) <-  (sampleFMapOpt_filter state.(assets) has_balance) ;;
  let has_tokens p := N.ltb 0 (snd p) in
  '(addr, nr_tokens) <- sampleFMapOpt_filter ledger.(balances) has_tokens ;;
  tokens_to_exchange <- gTokensToExchange nr_tokens ;;
  let exchange_msg := {|
    exchange_owner := addr;
    exchange_token_id := tokenid;
    tokens_sold := tokens_to_exchange;
    callback_addr := exploit_contract_addr;
  |} in
  returnGenSome (addr, other_msg (Dexter.tokens_to_asset exchange_msg))
.

Definition liftOptGen {A : Type} (g : G A) : GOpt A :=
  a <- g ;;
  returnGenSome a.

Definition gAddTokensToReserve (env : Environment)
                               (state : FA2Token.State)
                               : GOpt (Address * Amount * Dexter.Msg) :=
  tokenid <- liftM fst (sampleFMapOpt state.(assets)) ;;
  caller <- liftOptGen gAccountAddress ;;
  amount <- liftOptGen (choose (0%Z, env.(env_account_balances) caller)) ;;
  returnGenSome (caller, amount, (other_msg (add_to_tokens_reserve tokenid))).

(* NOTE: all call considered top-level calls (from users) *)
Definition gDexterAction (env : Environment) : GOpt Action :=
  let mk_call caller_addr amount msg :=
    returnGenSome {|
      act_origin := caller_addr;
      act_from := caller_addr;
      act_body := act_call dexter_contract_addr amount (serialize Dexter.Msg _ msg)
    |} in
  fa2_state <- returnGen (get_contract_state FA2Token.State env fa2_contract_addr) ;;
  backtrack [
   (1, '(caller, amount, msg) <- gAddTokensToReserve env fa2_state ;;
        mk_call caller amount msg
    ) ;
    (2, caller <- gAccountAddrWithout [fa2_contract_addr; dexter_contract_addr] ;;
        '(_, msg) <- gTokenExchange fa2_state ;;
        mk_call caller 0%Z msg
    )
  ].

End DexterContractGens.

Definition gDexterChain max_acts_per_block cb length :=
  gChain cb (fun e _ => gDexterAction e) length 1 max_acts_per_block.

(* the '1' fixes nr of actions per block to 1 *)
Definition token_reachableFrom max_acts_per_block cb pf : Checker :=
  reachableFrom_chaintrace cb (gDexterChain max_acts_per_block) pf.

Definition token_reachableFrom_implies_reachable
           {A} length max_acts_per_block cb (pf1 : ChainState -> option A) pf2 : Checker :=
  reachableFrom_implies_chaintracePropSized length cb (gDexterChain max_acts_per_block) pf1 pf2.

End DexterGens.

Module DummyTestInfo <: DexterTestsInfo.
  Definition fa2_contract_addr := zero_address.
  Definition dexter_contract_addr := zero_address.
  Definition exploit_contract_addr := zero_address.
  Definition gAccountAddress := returnGen zero_address.
  Definition gAccountAddrWithout (w : list Address) := returnGenSome zero_address.
End DummyTestInfo.
Module MG := DexterGens DummyTestInfo. Import MG.
