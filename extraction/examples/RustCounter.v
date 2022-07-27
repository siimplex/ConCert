From ConCert.Execution.Examples Require Counter.
From ConCert.Execution.Examples Require CounterSolana.
From ConCert.Extraction Require Import ConcordiumExtract.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import SolanaExtract.
From ConCert.Extraction Require Import RustExtract.
From Coq Require Import Bool.
From Coq Require Import String.
From MetaCoq.Template Require Import All.

Open Scope string.

Definition COUNTER_MODULE1 : SolanaMod _ :=
  {| solana_contract_name := "Counter";
     solana_process := @ConCert.Execution.Examples.CounterSolana.counter_process;
     solana_extra := []; |}.

Definition COUNTER_MODULE : ConcordiumMod _ _ :=
  {| concmd_contract_name := "counter";
     concmd_init := @ConCert.Execution.Examples.Counter.counter_init;
     concmd_receive := @ConCert.Execution.Examples.Counter.counter_receive;
     concmd_extra := []; |}.

(* NOTE: it is important to declare a priting config, otherwise MetaCoq evaluation tries to normalise a term with an unresolved instance and runs out of memory. *)
Instance RustConfig : RustPrintConfig :=
    {| term_box_symbol := "()";
       type_box_symbol := "()";
       any_type_symbol := "()";
       print_full_names := false |}.

Redirect "/home/johnny/Documents/Tese/ConCert/extraction/examples/extracted-code/solana-extract/counterv2.rs"

MetaCoq Run (solana_extraction
               COUNTER_MODULE1
               (SolanaRemap.build_remaps
                  (SolanaRemap.remap_arith ++ SolanaRemap.remap_blockchain_consts (* ++ SolanaRemap.remap_aux_consts *))
                  []
                  (SolanaRemap.remap_blockchain_inductives
                     ++ SolanaRemap.remap_std_types))
               (fun kn => eq_kername <%% bool_rec %%> kn
                          || eq_kername <%% bool_rect %%> kn)).

Redirect "/home/johnny/Documents/Tese/ConCert/extraction/examples/extracted-code/concordium-extract/counterv2.rs"

MetaCoq Run (concordium_extraction
               COUNTER_MODULE
               (ConcordiumRemap.build_remaps
                  (ConcordiumRemap.remap_arith ++ ConcordiumRemap.remap_blockchain_consts)
                  []
                  (ConcordiumRemap.remap_blockchain_inductives
                     ++ ConcordiumRemap.remap_std_types))
               (fun kn => eq_kername <%% bool_rec %%> kn
                          || eq_kername <%% bool_rect %%> kn)).
