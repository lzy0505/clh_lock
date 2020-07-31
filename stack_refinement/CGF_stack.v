From iris.proofmode Require Import tactics.
From iris_examples.logrel.F_mu_ref_conc Require Import examples.lock.
Import uPred.

Definition CGF_StackType τ :=
  TRec (TSum TUnit (TProd τ.[ren (+1)] (TVar 0))).

(* Coarse-grained push *)
Definition CGF_push (st : expr) : expr :=
  Lam (Store (st.[ren (+1)]) (Fold (InjR (Pair (Var 0) (Load st.[ren (+ 1)]))))).

Definition CGF_locked_push (st l : expr) := with_lock (CGF_push st) l.
Definition CGF_locked_pushV (st l : expr) : val := with_lockV (CGF_push st) l.

Definition CGF_pop (st : expr) : expr :=
  Lam (Case (Unfold (Load st.[ren (+ 1)]))
            (InjL Unit)
            (
              Seq
                (Store st.[ren (+ 2)] (Snd (Var 0)))
                (InjR (Fst (Var 0)))
            )
      ).

Definition CGF_locked_pop (st l : expr) := with_lock (CGF_pop st) l.
Definition CGF_locked_popV (st l : expr) : val := with_lockV (CGF_pop st) l.

Definition CGF_stack_body (st l : expr) : expr :=
 (Pair (CGF_locked_push st l) (CGF_locked_pop st l)).

Definition CGF_stack : expr :=
  TLam (
      LetIn
        newlock
        (LetIn
           (Alloc (Fold (InjL Unit)))
           (CGF_stack_body (Var 0) (Var 1)))).

Section CGF_Stack.
  Context `{heapIG Σ, cfgSG Σ}.

  Lemma CGF_push_type st Γ τ :
    typed Γ st (Tref (CGF_StackType τ)) →
    typed Γ (CGF_push st) (TArrow τ TUnit).
  Proof.
    intros H1. repeat econstructor.
    eapply (context_weakening [_]); eauto.
    repeat constructor; asimpl; trivial.
    eapply (context_weakening [_]); eauto.
  Qed.

  Lemma steps_CGF_push E j K st v w :
    nclose specN ⊆ E →
    spec_ctx ∗ st ↦ₛ v ∗ j ⤇ fill K (App (CGF_push (Loc st)) (of_val w))
    ⊢ |={E}=> j ⤇ fill K Unit ∗ st ↦ₛ FoldV (InjRV (PairV w v)).
  Proof.
    intros HNE. iIntros "[#Hspec [Hx Hj]]". unfold CGF_push.
    iMod (do_step_pure with "[$Hj]") as "Hj"; eauto.
    iAsimpl.
    iMod (step_load _ j (PairRCtx _ :: InjRCtx :: FoldCtx :: StoreRCtx (LocV _) :: K)
            with "[$Hj $Hx]") as "[Hj Hx]"; eauto.
    simpl.
    iMod (step_store _ j K with "[$Hj $Hx]") as "[Hj Hx]"; eauto.
    { rewrite /= !to_of_val //. }
    iModIntro. by iFrame.
  Qed.

  Lemma CGF_push_subst (st : expr) f : (CGF_push st).[f] = CGF_push st.[f].
  Proof. unfold CGF_push; asimpl; trivial. Qed.

  Hint Rewrite CGF_push_subst : autosubst.

  Typeclasses Opaque CGF_push.
  Global Opaque CGF_push.

  Lemma CGF_locked_push_to_val st l :
    to_val (CGF_locked_push st l) = Some (CGF_locked_pushV st l).
  Proof. trivial. Qed.

  Lemma CGF_locked_push_of_val st l :
    of_val (CGF_locked_pushV st l) = CGF_locked_push st l.
  Proof. trivial. Qed.

  Global Opaque CGF_locked_pushV.
  Lemma CGF_locked_push_type st l Γ τ :
    typed Γ st (Tref (CGF_StackType τ)) →
    typed Γ l LockType →
    typed Γ (CGF_locked_push st l) (TArrow τ TUnit).
  Proof.
    intros H1 H2. repeat econstructor.
    eapply with_lock_type; auto using CGF_push_type.
  Qed.

  Lemma steps_CGF_locked_push E j K st w v l :
    nclose specN ⊆ E →
    spec_ctx ∗ st ↦ₛ v ∗ l ↦ₛ (#♭v false)
      ∗ j ⤇ fill K (App (CGF_locked_push (Loc st) (Loc l)) (of_val w))
    ⊢ |={E}=> j ⤇ fill K Unit ∗ st ↦ₛ FoldV (InjRV (PairV w v)) ∗ l ↦ₛ (#♭v false).
  Proof.
    intros HNE. iIntros "[#Hspec [Hx [Hl Hj]]]". unfold CGF_locked_push.
    iMod (steps_with_lock _ _ _ _ _ (st ↦ₛ v)%I _ UnitV with "[$Hj $Hx $Hl]")
      as "Hj"; auto.
    iIntros (K') "[#Hspec Hxj]".
    iApply steps_CGF_push; first done. by iFrame.
  Qed.

  Lemma CGF_locked_push_subst (st l : expr) f :
    (CGF_locked_push st l).[f] = CGF_locked_push st.[f] l.[f].
  Proof. by rewrite /CGF_locked_push; asimpl. Qed.

  Hint Rewrite CGF_locked_push_subst : autosubst.

  Typeclasses Opaque CGF_locked_push.
  Global Opaque CGF_locked_push.

  (* Coarse-grained pop *)
  Lemma CGF_pop_type st Γ τ :
    typed Γ st (Tref (CGF_StackType τ)) →
    typed Γ (CGF_pop st) (TArrow TUnit (TSum TUnit τ)).
  Proof.
    intros H1.
    econstructor.
    eapply (Case_typed _ _ _ _ TUnit); eauto using typed.
    - replace (TSum TUnit (TProd τ (CGF_StackType τ))) with
          ((TSum TUnit (TProd τ.[ren (+1)] (TVar 0))).[(CGF_StackType τ)/])
        by (by asimpl).
      repeat econstructor.
      eapply (context_weakening [_]); eauto.
    - econstructor; eauto using typed.
      econstructor; eauto using typed.
      eapply (context_weakening [_; _]); eauto.
  Qed.

  Lemma CGF_pop_subst (st : expr) f :
    (CGF_pop st).[f] = CGF_pop st.[f].
  Proof. by rewrite /CGF_pop; asimpl. Qed.

  Hint Rewrite CGF_pop_subst : autosubst.

Lemma steps_CGF_pop_suc E j K st v w :
    nclose specN ⊆ E →
    spec_ctx ∗ st ↦ₛ FoldV (InjRV (PairV w v)) ∗
               j ⤇ fill K (App (CGF_pop (Loc st)) Unit)
      ⊢ |={E}=> j ⤇ fill K (InjR (of_val w)) ∗ st ↦ₛ v.
  Proof.
    intros HNE. iIntros "[#Hspec [Hx Hj]]". unfold CGF_pop.
    iMod (do_step_pure with "[$Hj]") as "Hj"; eauto.
    iAsimpl.
    iMod (step_load _ _ (UnfoldCtx :: CaseCtx _ _ :: K)  with "[$Hj $Hx]")
      as "[Hj Hx]"; eauto.
    simpl.
    iMod (do_step_pure _ _ (CaseCtx _ _ :: K) with "[$Hj]") as "Hj"; eauto.
    simpl.
    iMod (do_step_pure with "[$Hj]") as "Hj"; eauto.
    iAsimpl.
    iMod (do_step_pure _ _ (StoreRCtx (LocV _) :: SeqCtx _ :: K)
            with "[$Hj]") as "Hj"; eauto.
    simpl.
    iMod (step_store _ j (SeqCtx _ :: K) with "[$Hj $Hx]") as "[Hj Hx]";
      eauto using to_of_val.
    simpl.
    iMod (do_step_pure with "[$Hj]") as "Hj"; eauto.
    iMod (do_step_pure _ _ (InjRCtx :: K) with "[$Hj]") as "Hj"; eauto.
    simpl.
    by iFrame "Hj Hx".
  Qed.

  Lemma steps_CGF_pop_fail E j K st :
    nclose specN ⊆ E →
    spec_ctx ∗ st ↦ₛ FoldV (InjLV UnitV) ∗
               j ⤇ fill K (App (CGF_pop (Loc st)) Unit)
      ⊢ |={E}=> j ⤇ fill K (InjL Unit) ∗ st ↦ₛ FoldV (InjLV UnitV).
  Proof.
    iIntros (HNE) "[#Hspec [Hx Hj]]". unfold CGF_pop.
    iMod (do_step_pure with "[$Hj]") as "Hj"; eauto.
    iAsimpl.
    iMod (step_load _ j (UnfoldCtx :: CaseCtx _ _ :: K)
                    _ _ _ with "[$Hj $Hx]") as "[Hj Hx]"; eauto.
    iMod (do_step_pure _ _ (CaseCtx _ _ :: K) with "[$Hj]") as "Hj"; eauto.
    simpl.
    iMod (do_step_pure with "[$Hj]") as "Hj"; eauto.
    by iFrame "Hj Hx"; trivial.
  Qed.

  Typeclasses Opaque CGF_pop.
  Global Opaque CGF_pop.

  Lemma CGF_locked_pop_to_val st l :
    to_val (CGF_locked_pop st l) = Some (CGF_locked_popV st l).
  Proof. trivial. Qed.

  Lemma CGF_locked_pop_of_val st l :
    of_val (CGF_locked_popV st l) = CGF_locked_pop st l.
  Proof. trivial. Qed.

  Global Opaque CGF_locked_popV.

  Lemma CGF_locked_pop_type st l Γ τ :
    typed Γ st (Tref (CGF_StackType τ)) →
    typed Γ l LockType →
    typed Γ (CGF_locked_pop st l) (TArrow TUnit (TSum TUnit τ)).
  Proof.
    intros H1 H2. repeat econstructor.
    eapply with_lock_type; auto using CGF_pop_type.
  Qed.

  Lemma CGF_locked_pop_subst (st l : expr) f :
    (CGF_locked_pop st l).[f] = CGF_locked_pop st.[f] l.[f].
  Proof. by rewrite /CGF_locked_pop; asimpl. Qed.

  Hint Rewrite CGF_locked_pop_subst : autosubst.


 Lemma steps_CGF_locked_pop_suc E j K st v w l :
    nclose specN ⊆ E →
    spec_ctx ∗ st ↦ₛ FoldV (InjRV (PairV w v)) ∗ l ↦ₛ (#♭v false)
               ∗ j ⤇ fill K (App (CGF_locked_pop (Loc st) (Loc l)) Unit)
      ⊢ |={E}=> j ⤇ fill K (InjR (of_val w)) ∗ st ↦ₛ v ∗ l ↦ₛ (#♭v false).
  Proof.
    iIntros (HNE) "[#Hspec [Hx [Hl Hj]]]". unfold CGF_locked_pop.
    iMod (steps_with_lock _ _ _ _ _ (st ↦ₛ FoldV (InjRV (PairV w v)))%I
                          _ (InjRV w) UnitV
            with "[$Hj $Hx $Hl]") as "Hj"; eauto.
    iIntros (K') "[#Hspec Hxj]".
    iApply steps_CGF_pop_suc; eauto.
  Qed.

  Lemma steps_CGF_locked_pop_fail E j K st l :
    nclose specN ⊆ E →
    spec_ctx ∗ st ↦ₛ FoldV (InjLV UnitV) ∗ l ↦ₛ (#♭v false)
               ∗ j ⤇ fill K (App (CGF_locked_pop (Loc st) (Loc l)) Unit)
      ⊢ |={E}=> j ⤇ fill K (InjL Unit) ∗ st ↦ₛ FoldV (InjLV UnitV) ∗ l ↦ₛ (#♭v false).
  Proof.
    iIntros (HNE) "[#Hspec [Hx [Hl Hj]]]". unfold CGF_locked_pop.
    iMod (steps_with_lock _ _ _ _ _ (st ↦ₛ FoldV (InjLV UnitV))%I _
                          (InjLV UnitV) UnitV
          with "[$Hj $Hx $Hl]") as "Hj"; eauto.
    iIntros (K') "[#Hspec Hxj] /=".
      iApply steps_CGF_pop_fail; eauto.
  Qed.


  Typeclasses Opaque CGF_locked_pop.
  Global Opaque CGF_locked_pop.

  Lemma CGF_stack_body_type st l Γ τ :
    typed Γ st (Tref (CGF_StackType τ)) →
    typed Γ l LockType →
    typed Γ (CGF_stack_body st l)
          (TProd (TArrow τ TUnit) (TArrow TUnit (TSum TUnit τ))) .
  Proof.
    intros H1 H2.
    repeat (econstructor; eauto using CGF_locked_push_type,
                          CGF_locked_pop_type).
  Qed.

  Lemma CGF_stack_body_subst (st l : expr) f :
    (CGF_stack_body st l).[f] = CGF_stack_body st.[f] l.[f].
  Proof. by unfold CGF_stack_body; asimpl. Qed.

  Hint Rewrite CGF_stack_body_subst : autosubst.

  Lemma CGF_stack_type Γ :
    typed Γ CGF_stack
          (TForall
             (TProd
                (TArrow (TVar 0) TUnit)
                (TArrow TUnit (TSum TUnit (TVar 0)))
             )
          ).
  Proof.
    repeat econstructor;
      eauto 10 using newlock_type, CGF_locked_push_type, CGF_locked_pop_type, typed.
    asimpl; repeat constructor.
  Qed.

  Lemma CGF_stack_closed f : CGF_stack.[f] = CGF_stack.
  Proof. by unfold CGF_stack; asimpl. Qed.

End CGF_Stack.

Hint Rewrite CGF_push_subst : autosubst.
Hint Rewrite CGF_locked_push_subst : autosubst.
Hint Rewrite CGF_locked_pop_subst : autosubst.
Hint Rewrite CGF_pop_subst : autosubst.
Hint Rewrite CGF_locked_pop_subst : autosubst.
Hint Rewrite CGF_stack_body_subst : autosubst.
Hint Rewrite CGF_stack_closed : autosubst.
