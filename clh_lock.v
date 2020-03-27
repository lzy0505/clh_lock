From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import gset gmap excl agree frac.
From iris.heap_lang.lib Require Export lock.
From iris.bi.lib Require Import fractional.

Set Default Proof Using "Type".
Import uPred.

(** Implementation of CLH lock in Heaplang. *)
Definition init_lock : val :=
  λ: "" ,
     let: "L" := ref #0 in
     "L" <- ref #false;;
     "L". (* GRANTED, lock is free*)

Definition init_proc :val :=
  λ: "",
  let: "t" := ref #0 in
  let: "R" := ref "t" in
  let: "W" := ref "t" in
  let: "P" := ("R","W") in
  (Fst "P") <- ref #false;;
  "P".

Definition grant : val :=
  λ:  "P", !(Fst "P") <- #false;;
          (Fst "P")<- !(Snd "P").

Definition spin : val :=
  rec: "spin" "watch" :=
    if: !"watch" = #false then #() (* loop until (P.watch->state = GRANTED)*)
                      else "spin" "watch".

Definition FAS : val :=
  rec: "FAS" "x" "newv" :=
    let: "oldv" := !"x" in
    let: "p" :=  CmpXchg "x" "oldv" "newv" in
    if: (Snd "p") then (Fst "p")
    else "FAS" "x" "newv".

Definition request : val :=
  λ: "L" "P" ,
    !(Fst "P") <- #true;; (* *P.myreq.state= PENDING *)
    (Snd "P") <- FAS "L" !(Fst "P");;
    spin !(Snd "P").

(** The CMRAs we need. *)
Class issuedG Σ :=
  issue_G :> inG Σ (exclR ZO).
Definition issuedΣ : gFunctors :=
  #[ GFunctor (exclR ZO)].

Instance subG_issuedΣ {Σ} : subG issuedΣ Σ → issuedG Σ.
Proof. solve_inG. Qed.

Class lockedG Σ :=
  locked_G :> inG Σ (exclR ZO).
Definition lockedΣ : gFunctors :=
  #[ GFunctor (exclR ZO)].

Instance subG_lockedΣ {Σ} : subG lockedΣ Σ → lockedG Σ.
Proof. solve_inG. Qed.

Definition stateUR  : cmraT :=
  (prodR fracR (agreeR (leibnizO bool))).

Class stateG Σ :=
  state_G :> inG Σ stateUR.
Definition stateΣ : gFunctors :=
  #[ GFunctor stateUR].

Instance subG_stateΣ {Σ} : subG stateΣ Σ → stateG Σ.
Proof. solve_inG. Qed.

Section proof.

  Context `{!heapG Σ, !issuedG Σ, !lockedG Σ, !stateG Σ} (N : namespace).

(* ISSUED is not duplicable. Only the thread that has ISSUED can spin on the corresponding node. It is allocated when init isProc.*)
Definition ISSUED γ : iProp Σ := (own γ (Excl 0))%I.
Lemma issued_exclusive (γ : gname) : ISSUED γ  -∗ ISSUED γ  -∗ False.
Proof.
  iDestruct 1 as  "H1". iDestruct 1 as  "H2".
  iDestruct (own_valid_2 with "H1 H2") as %[].
Qed.

(* LOCKED is not duplicable. Thread get it after acquairing the lock and give it back when releasing. It is allocated when init isLock*)
Definition LOCKED γ : iProp Σ := (own γ (Excl 1))%I.
Lemma locked_exclusive (γ : gname) : LOCKED γ -∗ LOCKED γ -∗ False.
Proof.
  iDestruct 1 as  "H1". iDestruct 1 as  "H2".
  iDestruct (own_valid_2 with "H1 H2") as %[].
Qed.

(* Abstract state. The value of b indicates the real value of the node. The definition is same as the one used for modular counter(with minor modification). *)
Definition newstate (q:Qp) (b:bool):stateUR := (q, to_agree (b : leibnizO bool)).

Notation "γ ⤇[ q ] b" := (own γ ( newstate q  b))
                             (at level 20, q at level 50, format "γ ⤇[ q ] b") : bi_scope.
Notation "γ ⤇½ b" := (own γ (newstate (1/2) b))
                         (at level 20, format "γ ⤇½  b") : bi_scope.


Definition Locked γ1 γ3: iProp Σ := (LOCKED γ3 ∗ γ1 ⤇[1/2] false)%I.

Global Instance makeElem_fractional γ m:  Fractional(λ q, γ ⤇[ q ] m)%I.
Proof.
  intros p q. rewrite /newstate.
  rewrite -own_op; f_equiv.
  split; first done.
    by rewrite /= agree_idemp.
Qed.

Global Instance makeElem_as_fractional γ m q:
  AsFractional (own γ (newstate q m)) (λ q, γ ⤇[q] m)%I q.
Proof.
  split. done. apply _.
Qed.

Global Instance makeElem_Exclusive m: Exclusive (newstate 1 m).
Proof.
  intros [y ?] [H _]. apply (exclusive_l _ _ H).
Qed.

Lemma makeElem_op p q n: newstate p n ⋅ newstate q n ≡ newstate (p + q) n.
Proof.
  rewrite /newstate; split; first done.
    by rewrite /= agree_idemp.
Qed.

Lemma makeElem_eq γ p q (n m : bool): γ ⤇[p] n -∗ γ ⤇[q] m -∗ ⌜n = m⌝.
Proof.
  iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2") as %HValid.
  destruct HValid as [_ H2].
  iIntros "!%"; by apply agree_op_invL'.
Qed.

Lemma makeElem_entail γ p q (n m : bool): γ ⤇[p] n -∗ γ ⤇[q] m -∗ γ ⤇[p + q] n.
Proof.
  iIntros "H1 H2".
  iDestruct (makeElem_eq with "H1 H2") as %->.
  iCombine "H1" "H2" as "H".
    by rewrite makeElem_op.
Qed.

Lemma makeElem_update γ (n m k : bool): γ ⤇½ n -∗ γ ⤇½ m ==∗ γ ⤇[1] k.
Proof.
  iIntros "H1 H2".
  iDestruct (makeElem_entail with "H1 H2") as "H".
  rewrite Qp_div_2.
  iApply (own_update with "H"); by apply cmra_update_exclusive.
Qed.

Lemma dummy: (1/2 + 1/2 + 1/2 = 3/2)%Qp.
Proof.
  apply (bool_decide_unpack _).
  by compute.
Qed.

Lemma invalidST γ:  γ⤇[3 / 2]false -∗ False.
Proof.
  iIntros "H".
  iDestruct (own_valid with "H") as %[[] _].
  eauto.
Qed.


(** Specifications for CLH lock *)
Definition nodeInv l R γ1 γ2 γ3: iProp Σ:=
  ∃ (m :bool), l ↦ #m ∗ γ1 ⤇[1/2] m ∗( ⌜m= true⌝
                                ∨ ⌜ m= false ⌝ ∗ ISSUED γ2
                                ∨ ⌜ m= false ⌝ ∗ Locked γ1 γ3 ∗ R ).


Definition isProc p (n:bool) R γ1 γ2 γ3 γ1' γ2' : iProp Σ:=
  ∃(req watch l1 l2 :loc)  , ⌜p = (#req, #watch)%V ⌝ ∗ req ↦ #l1 ∗ watch ↦ #l2  ∗ γ1 ⤇[1/2] n ∗ inv (N.@ "node") (nodeInv l1 R γ1 γ2 γ3) ∗
      (⌜n= false ⌝  ∨ ⌜n=true⌝  ∗ inv (N.@"node") (nodeInv l2 R γ1' γ2' γ3) ).

Definition lockInv l R γ3: iProp Σ:=
  ∃(k:loc) γ1 γ2, l ↦ #k ∗ ISSUED γ2  ∗ inv (N.@ "node") (nodeInv k R γ1 γ2 γ3).

Definition isLock l R γ3 : iProp Σ:=
   inv (N .@ "lock") (lockInv l R γ3 ).

Lemma init_lock_spec (R: iProp Σ) :
  {{{R}}}init_lock #() {{{l, RET #l; ∃ γ3, isLock l R γ3 }}}.
Proof.
  iIntros (ϕ) "HR Hcont".
  rewrite -wp_fupd.
  wp_lam.
  wp_alloc l as "Hlpt".
  wp_pures.
  wp_alloc k as "Hkpt".
(**  iDestruct "Hpt" as (t) "Hlpt". *)
  wp_store.
  iMod (own_alloc (Excl 1)) as (γ3) "HL".
  {done. }
  iMod (own_alloc (Excl 0)) as (γ2) "HIS".
  {done. }
  iMod (own_alloc (newstate 1 false)) as (γ1) "[HST1 HST2]".
  {done. }
  iMod (inv_alloc (N .@ "node") _ (nodeInv k R γ1 γ2 γ3 ) with "[-Hcont Hlpt HIS]") as "Hinv".
  {iNext. iExists false.  eauto with iFrame. }
  iApply "Hcont".
  rewrite /isLock.
  iExists γ3.
  iMod (inv_alloc (N .@ "lock") _ (lockInv l R γ3) with "[Hlpt Hinv HIS]").
  {iNext. iExists k,γ1, γ2. iFrame. }
  iModIntro.
  iFrame.
Qed.

Lemma init_proc_spec R γ3 :
  {{{True }}}
    init_proc #()
    {{{p, RET p; ∃ γ1 γ2 γ1' γ2', isProc p false R γ1 γ2 γ3 γ1' γ2'}}}.
Proof.
  iIntros (ϕ) "_ Hcont".
  rewrite -wp_fupd.
  wp_lam.
  wp_alloc k.
  wp_alloc req as "Hreq".
  wp_let.
  wp_alloc watch as "Hwatch".
  wp_let.
  wp_pures.
  wp_alloc l1 as "Hl1pt".
  wp_proj;wp_store.
  iMod (own_alloc (Excl 0)) as (γ2) "HIS".
  {done. }
  iMod (own_alloc (newstate 1 false)) as (γ1) "[HST1 HST2]".
  {done. }
  iMod (inv_alloc (N .@ "node") _ (nodeInv l1 R γ1 γ2 γ3) with "[-Hcont HST1 Hreq Hwatch]") as "Hinv".
  {iNext. iExists false.  eauto with iFrame. }
  iApply "Hcont".
  iExists γ1, γ2, γ3, γ1.
  iModIntro.
  iFrame.
  iExists req, watch, l1, k.
  eauto with iFrame.
Qed.

Lemma spin_spec (k:loc) R γ1 γ2 γ3 :
  {{{ inv (N.@"node") (nodeInv k R γ1 γ2 γ3) ∗ ISSUED γ2}}}
    spin #k
    {{{RET #(); inv (N.@"node") (nodeInv k R γ1 γ2 γ3) ∗  Locked γ1 γ3∗ R}}}.
Proof.
  iIntros (ϕ) "[#Hnode HIS] Hcont".
  iLöb as "IH".
  wp_lam.
  wp_bind (! _)%E.
  iInv (N .@ "node") as (b) "(>Hkpt & >HST1 & [>% |[[>% >HISS] | [>% [>HL HR]]]])" "Hclose".
  - destruct b.
    * wp_load. (* false case *)
      iMod ("Hclose" with "[Hkpt HST1]") as "_".
      {iNext. iExists true.  eauto with iFrame. }
      iModIntro.
      wp_op;wp_if_false.
      iApply ("IH" with "HIS Hcont").
    * discriminate H.
  - iDestruct (issued_exclusive with "HIS HISS") as %[].
  - destruct b.
    * discriminate H.
    * wp_load.
      iMod ("Hclose" with "[Hkpt HIS HST1]") as "_".
      {iNext. iExists false.  eauto with iFrame. }
      iModIntro.
      wp_op;wp_if_true.
      iApply "Hcont".
      eauto with iFrame.
Qed.

(* Fetch-and-store operation(atomic) *)
Lemma FAS_spec l l1 R γ1 γ2 γ3:
  {{{isLock l R γ3 ∗ ISSUED γ2 ∗ inv (N.@"node") (nodeInv l1 R γ1 γ2 γ3) }}}
    FAS #l #l1
    {{{k, RET #k; ∃ γ1' γ2', ISSUED γ2' ∗ inv (N.@"node") (nodeInv k R γ1' γ2' γ3)}}}.
Proof.
  iIntros (ϕ) "[#Hlkinv [Hl1IS #Hnodeinv]] Hcont".
  iLöb as "IH".
  rewrite /isLock.
  wp_lam.
  wp_let.
  wp_bind (! _)%E.
  iInv (N .@ "lock") as (k γ1' γ2') "(>Hlpt & >HkIS & #Hknode)" "Hclose".
  wp_load.
  iMod ("Hclose" with "[Hlpt HkIS Hknode]") as "_".
  {iNext. iExists k ,γ1', γ2'. iFrame. iFrame "#". }
  iModIntro.
  wp_let.
  wp_bind (CmpXchg _ _ _)%E.
  iInv (N .@ "lock") as (k' γ1'' γ2'') "(>Hlpt & Hk'IS & #Hk'node)" "Hclose".
  destruct (decide (k = k')) as [->|Hneq].
  + (* FAS succ case*)
    wp_cmpxchg_suc.
    iMod("Hclose" with "[Hlpt Hl1IS Hnodeinv]") as "_".
    { iNext. iExists l1, γ1, γ2. iFrame. iFrame "#". }
    iModIntro.
    wp_let;wp_proj;wp_if_true;wp_proj.
    iApply "Hcont".
    eauto with iFrame.
  + wp_cmpxchg_fail.
    iMod("Hclose" with "[Hlpt Hk'IS Hknode]") as "_".
    { iNext. iExists k', γ1'', γ2''. iFrame. iFrame "#". }
    iModIntro.
    wp_let;wp_proj;wp_if_false.
    iApply ("IH" with "Hl1IS Hcont").
Qed.

Lemma request_spec l p R γ1 γ2 γ3 γ1' γ2':
  {{{isProc p false R γ1 γ2 γ3 γ1' γ2'∗ isLock l R γ3}}}
    request #l p
    {{{RET #(); ∃ γ1'' γ2'', isProc p true R γ1 γ2 γ3 γ1'' γ2'' ∗ Locked γ1'' γ3 ∗ R}}}.
Proof.
   iIntros (ϕ) "(Hpc & #Hlkinv) Hcont".
   iDestruct "Hpc" as (req watch l1 l2) "(-> & Hreq & Hwatch & HST1 & #Hpcinv & [Hdisj1| Hdisj2] )".
   - rewrite /isLock.
     rewrite /lockInv.
     wp_lam; wp_let;wp_proj;wp_load.
     wp_bind (_ <- _)%E.
     iInv (N .@ "node") as (b) "(>Hl1pt & >HST2 & [>% |[[>% >HIS] | [>% [>[HL HST3] HR]]]])" "Hclose".
     + destruct b.
       * iDestruct (makeElem_eq with "HST1 HST2") as %H'.
         discriminate H'.
       * discriminate H.
     + destruct b.
        * iDestruct (makeElem_eq with "HST1 HST2") as %H'.
         discriminate H'.
        * wp_store.
          iMod (makeElem_update _ _ _ true with "HST1 HST2") as "[HST1 HST2]".
          iMod ("Hclose" with "[Hl1pt HST2]") as "_".
          {iNext. iExists true. eauto with iFrame. }
          iModIntro.
          wp_seq;wp_proj;wp_load.
          wp_bind (FAS _ _)%E.
          (*FAS*)
          iApply (FAS_spec l l1 R γ1 γ2 γ3  with "[Hlkinv HIS Hpcinv]").
          {iFrame. rewrite /isLock. iFrame "#". }
          iNext.
          iIntros (k') "HPostFAS".
          iDestruct "HPostFAS" as (γ1'' γ2'') "[Hk'IS #Hk'node]".
          (* Spin *)
          wp_proj;wp_store;wp_proj;wp_load.
          iApply (spin_spec k' R γ1'' γ2'' γ3 with "[Hk'node Hk'IS]").
          { iFrame. iFrame "#". }
          iNext. iIntros "[_ [HL HSTk']]".
          iApply "Hcont".
          iFrame.
          rewrite /isProc.
          iExists γ1'', γ2''.
          iFrame.
          iExists req, watch, l1, k'.
          iFrame "#".
          eauto with iFrame.
     + iDestruct (makeElem_entail with "HST1 HST2") as "HSTT".
       iDestruct (makeElem_entail with "HSTT HST3") as "H".
       rewrite dummy.
       iDestruct (invalidST with "H") as %[].
   - iDestruct "Hdisj2" as "[% _]".
     discriminate H.
Qed.

Lemma grant_spec p R γ1 γ2 γ3 γ1' γ2':
  {{{isProc p true R γ1 γ2 γ3 γ1' γ2' ∗ Locked γ1' γ3 ∗ R}}}
    grant p
    {{{RET #(); isProc p false R γ1' γ2' γ3 γ1' γ2'}}}.
Proof.
  iIntros (ϕ) "(Hpc & [[HL HST] HR]) Hcont".
  iDestruct "Hpc" as (req watch l1 l2) "(-> & Hreq & Hwatch & HST1 & #Hpcinv & [%| Hdisj2] )".
  - discriminate H.
  - wp_lam;wp_proj;wp_load.
    wp_bind (_ <- _)%E.
    iInv (N .@ "node") as (b) "(>Hl1pt & >HST2 & [>% |[[>% >HIS] | [>% [[>HLL >HST3] _]]]])" "Hclose".
    + destruct b.
      * wp_store.
        iMod (makeElem_update _ _ _ false with "HST1 HST2") as "[HST1 HST2]".
        iMod("Hclose" with "[Hl1pt HST1 HST2 HL HR]") as "_".
        { iNext. iExists false. eauto with iFrame. }
        iModIntro.
        wp_seq.
        wp_proj;wp_load;wp_proj.
        wp_store.
        iApply ("Hcont").
        iExists req, watch, l2, l2.
        iDestruct "Hdisj2" as "(_ & #Hl2node)".
        eauto with iFrame.
      * discriminate H.
    + destruct b.
      * discriminate H.
      * iDestruct (makeElem_eq with "HST1 HST2") as %H'.
        discriminate H'.
    + iDestruct (locked_exclusive with "HL HLL") as%[].
Qed.

End proof.



