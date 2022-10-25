From ConCert.Execution.Examples Require Import Escrow.
From ConCert.Execution.Examples Require Import EscrowSolana.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import ConcordiumExtract.
From ConCert.Extraction Require Import SolanaExtract.
From ConCert.Extraction Require Import RustExtract.
From Coq Require Import Bool.
From Coq Require Import String.
From MetaCoq.Template Require Import All.


Definition ESCROW_MODULE_SOLANA : SolanaMod _ :=
  {| solana_contract_name := "Escrow";
     solana_process := @ConCert.Execution.Examples.EscrowSolana.escrow_process;
     solana_extra := []; |}.

Definition ESCROW_MODULE : ConcordiumMod _ _ :=
  {| concmd_contract_name := "escrow"%string;
     concmd_init := @Escrow.init;
     concmd_receive := @Escrow.receive;
     concmd_extra := []; |}.

(* Definition should_inline kn :=
  eq_kername kn <%% @Monads.bind %%>
  || eq_kername kn <%% Monads.Monad_option %%>
  || if String.index 0 "setter_from_getter" (string_of_kername kn) then true else false. *)

Definition should_inline kn :=
  eq_kername kn <%% @Monads.bind %%>
  || eq_kername kn <%% @ProgramError.Monad_result_error %%>
  || if String.index 0 "setter_from_getter" (string_of_kername kn) then true else false
  || eq_kername <%% bool_rec %%> kn
  || eq_kername <%% bool_rect %%> kn.

(* NOTE: it is important to declare a priting config, otherwise MetaCoq evaluation tries to normalise a term with an unresolved instance and runs out of memory. *)
Instance RustConfig : RustPrintConfig :=
    {| term_box_symbol := "()";
       type_box_symbol := "()";
       any_type_symbol := "()";
       print_full_names := false |}.

Redirect "/home/johnny/Documents/Tese/ConCert/extraction/examples/extracted-code/solana-extract/escrow.rs"
MetaCoq Run (solana_extraction
               ESCROW_MODULE_SOLANA
               (SolanaRemap.build_remaps
                  (SolanaRemap.remap_arith ++ SolanaRemap.remap_blockchain_consts ++ SolanaRemap.remap_aux_consts ++ SolanaRemap.remap_account_operations)
                  []
                  (SolanaRemap.remap_blockchain_inductives
                     ++ SolanaRemap.remap_std_types))
               should_inline).

(* Redirect "/home/johnny/Documents/Tese/ConCert/extraction/examples/extracted-code/concordium-extract/escrow.rs"
MetaCoq Run (concordium_extraction
               ESCROW_MODULE
               (ConcordiumRemap.build_remaps
                  (ConcordiumRemap.remap_arith
                     ++ ConcordiumRemap.remap_blockchain_consts)
                  ConcordiumRemap.remap_inline_bool_ops
                  (ConcordiumRemap.remap_std_types
                     ++ ConcordiumRemap.remap_blockchain_inductives))
               should_inline). *)
