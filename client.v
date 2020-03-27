From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import gset gmap excl agree frac.
From iris.heap_lang.lib Require Export lock.
From iris.heap_lang.lib Require Import par.
From iris.bi.lib Require Import fractional.
Require Import clh_lock.


Definition read  : expr :=
    λ: "l" "k" ,
    let: "p" := init_proc #() in
    request "l" "p";;
    let: "v" := !"k" in
    grant "p";;
    "v".


Definition simple_client : expr :=
    let: "r" := ref #42 in
    let: "lock" := init_lock #()in
    (read "lock" "r") ||| (read "lock" "r").


Section proof.
Local Set Default Proof Using All.
 Context `{!heapG Σ, !lockedG Σ, !stateG Σ, !spawnG Σ} (N : namespace).



Lemma read_spec l γ3 k:
  {{{isLock N  l (k ↦ #42) γ3}}}
    read #l #k
  {{{ v, RET v;  ⌜v = #42⌝ }}}.
Proof.
  iIntros (ϕ) "#HLock Hcont".
  wp_pures.
  wp_bind (init_proc _)%E.
  wp_apply (init_proc_spec N (k ↦ #42)%I γ3).
  { done. }
  iIntros (p) "HProc".
  iDestruct "HProc" as ( γ1 γ2 γ1' γ2') "HProc".
  wp_pures.
  wp_apply (request_spec N l _ (k ↦ #42)%I γ1 γ2 γ3 γ1' γ2' with "[HProc]").
  { iFrame "#".  iFrame. }
  iIntros "HPost".
  iDestruct "HPost" as (γ1'' γ2'') "[HProc [HL HR]]".
  wp_pures.
  wp_load.
  wp_pures.
  wp_apply( grant_spec N _ (k ↦ #42)%I γ1 γ2 γ3 γ1'' γ2'' with "[-Hcont]").
  {iFrame. }
  iIntros "HProc".
  wp_pures.
  iApply "Hcont".
  eauto.
Qed.


Lemma simple_spec :
  {{{True}}}simple_client {{{p, RET p; ⌜p=(#42, #42)%V ⌝}}}.
Proof.
      iIntros (ϕ) "_ Hcont".
      rewrite /simple_client.
      wp_alloc r as "H".
      wp_let.
      wp_bind (init_lock _ )%E.
      wp_apply (init_lock_spec N (r ↦ #42)%I with "[-Hcont]").
      eauto with iFrame.
      iIntros (l) "HLock".
      iDestruct "HLock" as (γ3) "#HLock".
      wp_pures.
      iApply (wp_par (λ v , ⌜v=#42⌝)%I (λ v , ⌜v=#42⌝)%I).
      - iApply (read_spec).
        {iFrame "#". }
        iNext.
        iIntros (v) "H".
        iFrame.
      - iApply (read_spec).
        {iFrame "#". }
        iNext.
        iIntros (v) "H".
        iFrame.
      - iIntros (v1 v2) "[-> ->]".
        iNext.
        iApply "Hcont".
        eauto.
Qed.

