From ConCert.Extraction Require Import SpecializeAccountOpsSolana.
From ConCert.Extraction Require Import SpecializeChainHelpersSolana.
From ConCert.Extraction Require Import SpecializeChainBaseSolana.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import ResultMonad.
From MetaCoq.PCUIC Require Import PCUICAst.
From MetaCoq.PCUIC Require Import PCUICAstUtils.

Definition contains (n : kername) : list kername -> bool :=
    existsb (eq_kername n).

Definition specialize_consec_env (Σ : global_env) : result global_env string :=
  Σrev <- SpecializeChainBaseSolana.specialize_env_rev (List.rev Σ);;
  let Σ := (List.rev Σrev) in
  Σrev <- SpecializeAccountOpsSolana.specialize_env_rev (List.rev Σ);;
  let Σ := (List.rev Σrev) in
  Σrev <- SpecializeChainHelpersSolana.specialize_env_rev (List.rev Σ);;
  ret (List.rev Σrev).