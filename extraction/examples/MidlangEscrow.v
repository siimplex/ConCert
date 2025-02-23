From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import ElmExtract.
From ConCert.Extraction Require Import Extraction.
From ConCert.Extraction Require Import Inlining.
From ConCert.Extraction Require Import SpecializeChainBase.
From ConCert.Extraction Require Import PrettyPrinterMonad.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Execution.Examples Require Import Escrow.
From MetaCoq.Template Require Import Kernames.
From MetaCoq.Template Require Import All.
From Coq Require Import List.
From Coq Require Import String.

Import MonadNotation.
Open Scope string.

Instance EscrowMidlangBoxes : ElmPrintConfig :=
  {| term_box_symbol := "()";
     type_box_symbol := "()";
     any_type_symbol := "()";
     false_elim_def := "false_rec ()";
     print_full_names := true; (* full names to avoid clashes*)|}.

Definition TT_escrow : list (kername * string) :=
  [    remap <%% bool %%> "Bool"
     ; remap <%% @Address %%> "Int"].

Definition midlang_translation_map :=
  Eval compute in
        [(<%% @current_slot %%>, "current_slot");
        (<%% @address_eqb %%>, "Order.eq");
        (<%% @ctx_from %%>, "ctx_from");
        (<%% @ctx_contract_address %%>, "ctx_contract_address");
        (<%% @ctx_contract_balance %%>, "ctx_contract_balance");
        (<%% @ctx_amount %%>, "ctx_amount");
        (<%% @Chain %%>, "ConCertChain");
        (<%% @ContractCallContext %%>, "ConCertCallContext");
        (<%% @ConCert.Execution.Blockchain.ActionBody %%>, "ConCertAction");
        (<%% @ChainBase %%>, "ChainBaseWTF");
        (<%% @Amount %%>,"Z" )].

Definition midlang_escrow_translate (name : kername) : option string :=
  match find (fun '(key, _) => eq_kername key name) (TT_escrow ++ midlang_translation_map) with
  | Some (_, val) => Some val
  | None => None
  end.

Axiom extraction_chain_base : ChainBase.
Existing Instance extraction_chain_base.

MetaCoq Run (p <- tmQuoteRecTransp Escrow.receive false ;;
             tmDefinition "escrow_env" p.1).

Open Scope bool.
Definition should_inline kn :=
  eq_kername kn <%% @Monads.bind %%>
  || eq_kername kn <%% Monads.Monad_option %%>
  || if String.index 0 "setter_from_getter" (string_of_kername kn) then true else false.

Definition ignored_concert_types :=
  Eval compute in
        [<%% @ActionBody %%>;
         <%% @Address %%>;
         <%% @Amount %%>;
         <%% @ChainBase %%>;
         <%% @Chain %%>;
         <%% @ContractCallContext %%>;
         <%% @SerializedValue %%>;
         <%% @RecordSet.SetterFromGetter %%>].

Print ignored_concert_types.

Definition extract_template_env_specialize
           (params : extract_template_env_params)
           (Σ : T.global_env)
           (seeds : KernameSet.t)
           (ignore : kername -> bool) : result ExAst.global_env string :=
  let Σ := SafeTemplateChecker.fix_global_env_universes Σ in
  let Σ := T2P.trans_global_decls Σ in
  Σ <- specialize_ChainBase_env Σ ;;
  wfΣ <- check_wf_env_func params Σ;;
  extract_pcuic_env (pcuic_args params) Σ wfΣ seeds ignore.

Definition extract_params :=
  {| check_wf_env_func := check_wf_env_func extract_within_coq;
     template_transforms := [];
     pcuic_args :=
       {| optimize_prop_discr := true;
          extract_transforms := [Optimize.dearg_transform (fun _ => None) true true true true true;
                                 Inlining.transform should_inline] |} |}.

Definition escrow_extract :=
  Eval vm_compute in
  extract_template_env_specialize
    extract_params
    escrow_env
    (KernameSet.singleton <%% @Escrow.receive %%>)
     (fun kn => contains kn (ignored_concert_types
                           ++ map fst midlang_translation_map
                           ++ map fst TT_escrow)).

Print escrow_extract.

Definition midlang_prelude :=
  ["import Basics exposing (..)";
  "import Blockchain exposing (..)";
  "import Bool exposing (..)";
  "import Int exposing (..)";
  "import Maybe exposing (..)";
  "import Order exposing (..)";
  "import Transaction exposing (..)";
  "import Tuple exposing (..)";
  "";
  "-- some dummy definitions (will be remapped properly in the future)";
  "type AccountAddress = Int";
  "type ConCertAction = Act_transfer Int Z";
  "type ConCertCallContext = CCtx Unit";
  "type ConCertChain = CChain Unit";
  "ctx_from ctx = 0";
  "ctx_contract_address _ = 0";
  "ctx_contract_balance _ = (Zpos (XO XH))";
  "ctx_amount ctx = (Zpos (XO XH))";
  "current_slot _ = O"].

Definition escrow_result :=
  Eval vm_compute in
    (env <- escrow_extract;;
     '(_, lines) <- finish_print_lines (print_env env midlang_escrow_translate);;
     ret lines).

Definition result :=
  match escrow_result with
  | Ok l => monad_map tmMsg (midlang_prelude ++ l)
  | Err err => tmFail err
  end.

Redirect "examples/extracted-code/midlang-extract/MidlangEscrow.midlang" MetaCoq Run result.
