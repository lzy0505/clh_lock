From iris.algebra Require Import auth list agree frac.
From iris.program_logic Require Import adequacy ectxi_language.
From iris_examples.logrel.F_mu_ref_conc Require Import soundness_binary.
From iris_examples.logrel.F_mu_ref_conc.examples Require Import lock.
From iris_examples.logrel.F_mu_ref_conc.examples.stack Require Import
  CGF_stack CGL_stack stack_rules.
From iris.proofmode Require Import tactics.

Definition stackN : namespace := nroot .@ "stack".


Section Stack_refinement.
  Context `{heapIG Σ, cfgSG Σ, inG Σ (authR stackUR), inG Σ stateUR}.
  Notation D := (prodO valO valO -n> iPropO Σ).
  Implicit Types Δ : listO D.



  Lemma CGL_CGF_counter_refinement :
    [] ⊨ CGL_stack ≤log≤ CGF_stack : TForall (TProd
           (TArrow (TVar 0) TUnit)
           (TArrow TUnit (TSum TUnit (TVar 0)))).
  Proof.
    iIntros (Δ [|] ?) "#[Hspec HΓ]"; iIntros (j K) "Hj"; last first.
    { iDestruct (interp_env_length with "HΓ") as %[=]. }
    iClear "HΓ".
    iAsimpl.
    iApply wp_value.
    iExists (TLamV _); iFrame "Hj".
    clear j K. iAlways. iIntros (τi) "%". iIntros (j K) "Hj /=".
    (** evaluate newlock and create stack *)
    (* L *)
    iApply wp_pure_step_later; auto;iNext;iAsimpl.
    iApply (wp_bind (fill [LetInCtx _])).
    iApply wp_newlock;first done;iNext;iIntros (lL) "HlL";iAsimpl.
    iApply wp_pure_step_later; first done; iNext;iAsimpl.
    iApply (wp_bind (fill [AllocCtx; LetInCtx _])).
    iApply wp_alloc;first done;iNext;iIntros (istkL) "HistkL";iAsimpl.
    iApply (wp_bind (fill [LetInCtx _])).
    iApply wp_alloc;first done;iNext;iIntros (stkL) "HstkL";iAsimpl.
    iApply wp_pure_step_later; auto; iNext; iAsimpl.
    (* F *)
    iMod (do_step_pure _ j K with "[$Hj]") as "Hj"; eauto.
    iMod (steps_newlock _ j (LetInCtx _ :: K)  with "[$Hj]") as (lF) "[Hj HlF]"; eauto;simpl.
    iMod (do_step_pure with "[$Hj]") as "Hj"; eauto;iAsimpl.
    iMod (step_alloc  _ j (LetInCtx _ :: K) with "[$Hj]") as (stkF) "[Hj HstkF]"; eauto;simpl.
    iMod (do_step_pure with "[$Hj]") as "Hj"; eauto;iAsimpl.
    (** alloc invariant*)
    iMod (own_alloc (● (∅ : stackUR))) as (γ) "Hemp"; first by apply auth_auth_valid.
    set (istkG := StackG _ _ γ).
    change γ with (@stack_name _ istkG).
    change H1 with (@stack_inG _ istkG).
    clearbody istkG. clear γ H1.
    (*?*)
    iAssert (@stack_owns _ istkG _ ∅) with "[Hemp]" as "Hoe".
    { rewrite /stack_owns big_sepM_empty fmap_empty. iFrame "Hemp"; trivial. }
    (*?*)
    iMod (stack_owns_alloc with "[$Hoe $HistkL]") as "[Hoe Hls]".
    iAssert (StackLink τi (LocV istkL, FoldV (InjLV UnitV))) with "[Hls]" as "HLKL".
    { rewrite StackLink_unfold.
      iExists _, _. iSplitR; simpl; trivial.
      iFrame "Hls". iLeft. iSplit; trivial. }
    iMod (own_alloc (newstate 1 istkL)) as (γ) "[Hγ1 Hγ2]";first done.
    iAssert ((∃ istkL v h b, (stack_owns h)
                         ∗ stkF ↦ₛ v
                         ∗ stkL ↦ᵢ (LocV istkL) ∗ γ ⤇[1/2] istkL
                         ∗ StackLink τi (LocV istkL, v)
                         ∗ lF ↦ₛ (#♭v false)
                         ∗ lL ↦ᵢ (#♭v b) ∗ ( ⌜b = true ⌝ ∨ ⌜b = false ⌝ ∗ γ ⤇[1/2] istkL)
             )%I) with "[Hoe HstkL HstkF HLKL HlF HlL Hγ1 Hγ2]" as "Hinv".
    { iExists istkL, _, _, false. iFrame "Hoe HstkL HstkF HLKL HlF HlL".  iFrame. iRight. iFrame. done. }
    iMod (inv_alloc stackN with "[Hinv]") as "#Hinv"; [iNext; iExact "Hinv"|].
    Opaque stack_owns.
    (** split into push and pop*)
    iApply wp_value.
    iExists (PairV (CGF_locked_pushV _ _)
                (CGF_locked_popV _ _)).
    simpl.
    rewrite CGF_locked_push_of_val CGF_locked_pop_of_val.
    iFrame "Hj".
    iExists (_, _), (_, _); iSplit; eauto.
    iSplit; iAlways; clear j K.
    - (* push *)
      iIntros ( [v1 v2] ) "#Hrel". iIntros (j K) "Hj /=".
      (* L *)
      iApply wp_pure_step_later; auto;iNext;iAsimpl.
      iApply (wp_bind (fill [SeqCtx _])).
      (* acquire*)
      Transparent acquire.
      rewrite /acquire.
      iLöb as "Hlob".
      iApply wp_pure_step_later; auto;iNext;iAsimpl.
      iApply (wp_bind (fill [IfCtx _ _])).
      (* open invariant *)
      iInv stackN as (istk2 v h b) "(Hoe & HstkF &  HstkL & Hγ & HLKL & HlF & >HlL & [> ->|[> -> Hγ2]])" "Hclose".
      + iApply (wp_cas_fail with "HlL"); auto; iNext; iIntros "HlL";iAsimpl.
        iMod ("Hclose" with "[-Hj]") as "_".
        { iNext. iExists istk2, _, _,true. iFrame. iLeft; done. }
        iModIntro.
        iApply wp_pure_step_later; auto; iNext; iAsimpl.
        iApply "Hlob".
        iFrame.
      + iApply (wp_cas_suc with "HlL"); auto; iNext; iIntros "HlL";iAsimpl.
        iMod ("Hclose" with "[-Hj Hγ]") as "_".
        { iNext. iExists istk2, _, _,true. iFrame. iLeft;done. }
        iModIntro.
        iApply wp_pure_step_later; auto; iNext; iAsimpl.
        iApply wp_value;iAsimpl.
        iClear "Hlob".
        clear v h.
        (* acquire succ! *)
        iApply wp_pure_step_later; auto; iNext; iAsimpl.
        iApply (wp_bind (fill [LetInCtx _])).
        rewrite CGL_push_folding;iAsimpl.
        iApply wp_pure_step_later; auto; iNext; iAsimpl.
        iApply (wp_bind (fill [LetInCtx _])).
        (* open invariant *)
        iInv stackN as (istk2' v h b) "(Hoe & HstkF &  HstkL & Hγ1 & HLKL & HlF & >HlL & Hbool)" "Hclose".
        iApply (wp_load with "HstkL"); iNext; iIntros "HstkL".
        iDestruct (makeElem_eq with "Hγ Hγ1") as %<-.
        iMod ("Hclose" with "[-Hj Hγ]") as "_".
        { iNext. iExists _, _, _,_. iFrame. }
        iModIntro;iAsimpl.
        clear  h b.
        iApply wp_pure_step_later; auto; iNext; iAsimpl.
        iApply (wp_bind (fill [StoreRCtx  (LocV _)])).
        iApply wp_alloc;first done;iNext;iIntros (tmp) "HtmpL";iAsimpl.
        iInv stackN as (istk2'' v' h b) "(Hoe & HstkF &  HstkL & Hγ1 & HLKL & HlF & >HlL & Hbool)" "Hclose".
        iApply (wp_store with "HstkL"); iNext; iIntros "HstkL".
        iDestruct (makeElem_eq with "Hγ Hγ1") as %<-.
        iMod (makeElem_update _ _ _ tmp with "Hγ Hγ1") as "[Hγ Hγ1]".
        (* F *)
        iMod (steps_CGF_locked_push _ j K with "[Hj HlF HstkF]")
            as "[Hj [HstkF HlF]]"; first solve_ndisj.
        { rewrite CGF_locked_push_of_val. by iFrame "Hspec HstkF Hj". }
        iMod (stack_owns_alloc with "[$Hoe $HtmpL]") as "[Hoe HtmpL]".
        iDestruct "Hbool" as "[-> |[-> Hγ2]]".
        * (*b=true, release succ*)
          iMod ("Hclose" with "[-Hj  Hγ]") as "_".
        { iNext. iExists tmp,(FoldV (InjRV (PairV v2 v'))) , _,_. iFrame. iSplitL. do 2 rewrite StackLink_unfold. rewrite -StackLink_unfold. iExists tmp, _.  iFrame "HtmpL". simpl.  iSplitR. done. iRight. iExists v1,(LocV istk2),v2, v', istk2. iFrame "#". eauto. iLeft. done. }
        clear v v' h istk2.
        iApply (wp_bind (fill [LetInCtx _])).
        iModIntro.
        iApply wp_value;iAsimpl.
        iApply wp_pure_step_later; auto; simpl; iNext;iAsimpl.
        iApply (wp_bind (fill [SeqCtx _])).
        (** release *)
        Transparent release.
        rewrite /release.
        iApply wp_pure_step_later; auto; simpl; iNext.
        iInv stackN as (istk2 v h b) "(Hoe & HstkF &  HstkL & >Hγ1 & HLKL & HlF & >HlL & Hbool)" "Hclose".
        iDestruct (makeElem_eq with "Hγ Hγ1") as %<-.
        iApply (wp_store with "HlL");iNext;iIntros "HlL".
        iMod ("Hclose" with "[-Hj]") as "_".
        { iNext. iExists _, _, _,_. iFrame. iRight. iFrame. done. }
        iModIntro.
        iApply wp_pure_step_later; auto; simpl; iNext.
        iApply wp_value. iExists UnitV. iFrame. done.
        * (*b=false, FALSE*)
          iDestruct (makeElem_eq with "Hγ Hγ2") as %<-.
          iDestruct (makeElem_entail with "Hγ1 Hγ2") as "Hγγ".
          iDestruct (makeElem_entail with "Hγγ Hγ") as "Hγ".
          rewrite dummy.
          iDestruct (invalid with "Hγ") as %[].
    - (* pop *)
      iIntros ( ? [-> ->] ); simpl. iIntros (j K) "Hj /=".
      (* L *)
      iApply wp_pure_step_later; auto;iNext;iAsimpl.
      iApply (wp_bind (fill [SeqCtx _])).
      (* acquire*)
      iLöb as "Hlob".
      iApply wp_pure_step_later; auto;iNext;iAsimpl.
      iApply (wp_bind (fill [IfCtx _ _])).
      iInv stackN as (istk2 v h b) "(Hoe & HstkF &  HstkL & Hγ & HLKL & HlF & >HlL & [> ->|[> -> Hγ2]])" "Hclose".
      + iApply (wp_cas_fail with "HlL"); auto; iNext; iIntros "HlL";iAsimpl.
        iMod ("Hclose" with "[-Hj]") as "_".
        { iNext. iExists istk2, _, _,true. iFrame. iLeft; done. }
        iModIntro.
        iApply wp_pure_step_later; auto; iNext; iAsimpl.
        iApply "Hlob".
        iFrame.
      + iApply (wp_cas_suc with "HlL"); auto; iNext; iIntros "HlL";iAsimpl.
        iMod ("Hclose" with "[-Hj Hγ]") as "_".
        { iNext. iExists istk2, _, _,true. iFrame. iLeft;done. }
        iModIntro.
        iApply wp_pure_step_later; auto; iNext; iAsimpl.
        iApply wp_value;iAsimpl.
        iClear "Hlob".
        clear v h.
        (* acquire succ! *)
        iApply wp_pure_step_later; auto; iNext; iAsimpl.
        iApply (wp_bind (fill [LetInCtx _])).
        rewrite CGL_pop_folding;iAsimpl.
        iApply wp_pure_step_later; auto; iNext; iAsimpl.
        iApply (wp_bind (fill [LetInCtx _])).
        iInv stackN as (istk2' v h b) "(Hoe & HstkF &  HstkL & Hγ1 & HLKL & HlF & >HlL & Hbool)" "Hclose".
        iApply (wp_load with "HstkL"); iNext; iIntros "HstkL".
        iDestruct (makeElem_eq with "Hγ Hγ1") as %<-.
        iMod ("Hclose" with "[-Hj Hγ]") as "_".
        { iNext. iExists _, _, _,_. iFrame. }
        iModIntro;iAsimpl.
        clear  h b v.
        iApply wp_pure_step_later; auto; iNext; iAsimpl.
        iApply (wp_bind (fill [CaseCtx _ _])).
        iInv stackN as (istk2' v h b) "(Hoe & HstkF &  HstkL & >Hγ1 & #HLKLinv & HlF & >HlL & Hbool)" "Hclose".
        iDestruct (makeElem_eq with "Hγ Hγ1") as %<-.
        rewrite StackLink_unfold.
        iPoseProof "HLKLinv" as (istk2' tmp) "[>%  [>HistkL [>[% %]|H2]]]"; simplify_eq /=;
        iClear "HLKLinv".
        * (* stack is empty *)
        iDestruct (stack_owns_later_open_close with "Hoe HistkL") as "[>HistkL' Hoe]".
        iApply (wp_load with "HistkL'"); iNext; iIntros "HistkL'";iAsimpl.
        (* F *)
        rewrite CGF_locked_pop_of_val.
        iMod (steps_CGF_locked_pop_fail with "[$Hspec $HstkF $HlF $Hj]")
             as "[Hj [HstkF HlF]]"; first solve_ndisj.
        (* L *)
        iMod ("Hclose" with "[-Hj Hγ]") as "_".
        { iNext. iExists _, _, _,_.  iFrame. iSplitL. by iApply ("Hoe" with "HistkL'").  rewrite StackLink_unfold.  iExists istk2',_. eauto. }
        iModIntro;iAsimpl.
        clear  h b.
        iApply wp_pure_step_later; auto; iNext; iAsimpl.
        iApply wp_value;iAsimpl.
        iApply wp_pure_step_later; auto; iNext; iAsimpl.
        iApply (wp_bind (fill [SeqCtx _])).
        (* release *)
        iApply wp_pure_step_later; auto; simpl; iNext.
        iInv stackN as (istk2 v h b) "(Hoe & HstkF &  HstkL & >Hγ1 & HLKL & HlF & >HlL & Hbool)" "Hclose".
        iDestruct (makeElem_eq with "Hγ Hγ1") as %<-.
        iApply (wp_store with "HlL");iNext;iIntros "HlL".
        iMod ("Hclose" with "[-Hj]") as "_".
        { iNext. iExists _, _, _,_. iFrame. iRight. iFrame. done. }
        iModIntro.
        iApply wp_pure_step_later; auto; simpl; iNext.
        iApply wp_value. iExists (InjLV UnitV). iFrame. iLeft. iExists (UnitV, UnitV).  eauto 10.
        * (* stack is not empty *)
          iDestruct (stack_owns_later_open_close with "Hoe HistkL") as "[>HistkL' Hoe]".
          iApply (wp_load with "HistkL'"); iNext; iIntros "HistkL'";iAsimpl.
          iDestruct "H2" as (v1 stkL' v2 stkF' stkL'v) "(% & % & % & ? & HLKL')".
          simplify_eq /=.
          iMod ("Hclose" with "[-Hj Hγ]") as "_".
          { iNext. iExists _, _, _,_. iFrame. iSplitL. iApply ("Hoe" with "HistkL'"). do 2 rewrite StackLink_unfold. rewrite -StackLink_unfold. iExists istk2', (InjRV (PairV v1 (FoldV (LocV stkL'v)))). iFrame "#".  iSplitR. eauto.  iRight. iExists v1, (LocV stkL'v), v2, stkF', stkL'v. simpl. iFrame"#". done. }
          clear h b.
          iModIntro.
          iApply wp_pure_step_later; auto; simpl; iNext.
          iApply (wp_bind (fill [UnfoldCtx; StoreRCtx (LocV stkL); SeqCtx _])).
          iApply wp_pure_step_later; auto; simpl; iNext.
          iApply wp_value;iAsimpl.
          iApply (wp_bind (fill [StoreRCtx (LocV stkL); SeqCtx _])).
          iApply wp_pure_step_later; auto; simpl; iNext.
          iApply wp_value;iAsimpl.
          iApply (wp_bind (fill [SeqCtx _])).
          iInv stackN as (istk2 v h b) "(Hoe & HstkF &  >HstkL & >Hγ1 & HLKL & HlF & >HlL & Hbool)" "Hclose".
          iDestruct (makeElem_eq with "Hγ Hγ1") as %->.
          iApply (wp_store with "HstkL");iNext;iIntros "HstkL".
          do 2 rewrite StackLink_unfold. rewrite -StackLink_unfold.
          iPoseProof "HLKL" as (istk2' tmp) "[Heq [HistkL' [[% %]|H2]]]".
          -- (* empty *)simpl. iDestruct "Heq" as %[=].
             rewrite -H6.
             iDestruct (stack_mapstos_agree with "[HistkL HistkL']") as %?;
                                                                          first (iSplit; [iExact "HistkL"| iExact "HistkL'"]).
             rewrite H1 in H5.
             discriminate.
          -- simpl. iDestruct "Heq" as %[=].
             rewrite -H4.
             iDestruct (stack_mapstos_agree with "[HistkL HistkL']") as %?;
                                                                          first (iSplit; [iExact "HistkL"| iExact "HistkL'"]).

             simplify_eq /=.
             iClear "HLKL'".
             iDestruct "H2" as (v1' stkL'' v2' stkF'' stkL''v) "(% & % & % & #Hrel & HLKL')".
             simplify_eq /=.
             (* F *)
             rewrite CGF_locked_pop_of_val.
             iMod (steps_CGF_locked_pop_suc _ j K with "[$Hspec $HstkF $HlF $Hj]") as "[Hj [HstkF HlF]]"; first solve_ndisj.

             iMod (makeElem_update _ _ _ stkL''v with "Hγ Hγ1") as "[Hγ Hγ1]".
             iDestruct "Hbool" as "[-> |[-> Hγ2]]".
             ++ (*b=true, release succ*)
               iMod ("Hclose" with "[-Hj Hγ]") as "_".
               {iNext. iExists stkL''v, stkF'', h, true.  iFrame . iLeft. done. }
               clear h.
               iModIntro.
               iApply wp_pure_step_later; auto; simpl; iNext.
               iApply (wp_bind (fill [InjRCtx ])).
               iApply wp_pure_step_later; auto; simpl; iNext.
               iApply wp_value;iAsimpl.
               iApply wp_value;iAsimpl.
               iApply wp_pure_step_later; auto; simpl; iNext.
               iApply (wp_bind (fill [SeqCtx _ ])).
               (* release *)
               iApply wp_pure_step_later; auto; simpl; iNext.
               iInv stackN as (istk2 v h b) "(Hoe & HstkF &  HstkL & >Hγ1 & HLKL & HlF & >HlL & Hbool)" "Hclose".
               iDestruct (makeElem_eq with "Hγ Hγ1") as %<-.
               iApply (wp_store with "HlL");iNext;iIntros "HlL".
               iMod ("Hclose" with "[-Hj]") as "_".
               { iNext. iExists _, _, _,_. iFrame. iRight. iFrame. done. }
               iModIntro.
               iApply wp_pure_step_later; auto; simpl; iNext.
               iApply wp_value. iExists (InjRV v2'). iFrame. iRight. iExists (v1', v2').  eauto 10.
             ++ (*b=false, FALSE*)
               iDestruct (makeElem_eq with "Hγ Hγ2") as %<-.
               iDestruct (makeElem_entail with "Hγ1 Hγ2") as "Hγγ".
               iDestruct (makeElem_entail with "Hγγ Hγ") as "Hγ".
               rewrite dummy.
               iDestruct (invalid with "Hγ") as %[].
Qed.
