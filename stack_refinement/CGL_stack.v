From iris.proofmode Require Import tactics.
From iris_examples.logrel.F_mu_ref_conc Require Import examples.lock.
Import uPred.

Definition CGL_StackType τ :=
  TRec (Tref (TSum TUnit (TProd τ.[ren (+1)] (TVar 0)))).
Definition CGL_Stack_Ref_Type τ :=
  Tref (TSum TUnit (TProd τ (CGL_StackType τ))).


(* Coarse-grained push *)
Definition CGL_push (st : expr) : expr :=
  Lam (LetIn (Load (st.[ren (+1)]))
             (Store (st.[ren (+2)])
                    (Alloc (InjR (Pair (Var 1) (Fold (Var 0))))))
      ).

Definition CGL_locked_push (st l : expr) := with_lock (CGL_push st) l.
Definition CGL_locked_pushV (st l : expr) : val := with_lockV (CGL_push st) l.

Definition CGL_pop (st : expr) : expr :=
  Lam (LetIn (Load (st.[ren (+1)]))
             (Case (Load (Var 0))
                   (InjL Unit)
                   (
                     Seq
                       (Store st.[ren (+ 3)] (Unfold (Snd (Var 0))))
                       (InjR (Fst (Var 0)))
                   )
             )
      ).

Definition CGL_locked_pop (st l : expr) := with_lock (CGL_pop st) l.
Definition CGL_locked_popV (st l : expr) : val := with_lockV (CGL_pop st) l.

Definition CGL_stack_body (st l : expr) : expr :=
 (Pair (CGL_locked_push st l) (CGL_locked_pop st l)).

Definition CGL_stack : expr :=
  TLam (
      LetIn
        newlock
        (LetIn
           (Alloc (Alloc (InjL Unit)))
           (CGL_stack_body (Var 0) (Var 1)))).

Section CGL_Stack.
  Context `{heapIG Σ, cfgSG Σ}.
(* add lock?*)
  Lemma CGL_push_folding (st : expr) :
    CGL_push st =
    Lam (LetIn (Load (st.[ren (+1)]))
               (Store (st.[ren (+2)])
                      (Alloc (InjR (Pair (Var 1) (Fold (Var 0))))))
        ).
  Proof. trivial. Qed.


  Lemma CGL_push_type st Γ τ :
    typed Γ st (Tref (CGL_Stack_Ref_Type τ)) →
    typed Γ (CGL_push st) (TArrow τ TUnit).
  Proof.
    intros ?.
    do 2 econstructor.
    { econstructor. eapply (context_weakening [_]). eauto. }
    econstructor; eauto using typed.
    - eapply (context_weakening [_; _]); eauto.
    - repeat econstructor. by asimpl.
  Qed.

  Lemma CGL_push_subst (st : expr) f : (CGL_push st).[f] = CGL_push st.[f].
  Proof. unfold CGL_push; asimpl; trivial. Qed.

  Hint Rewrite CGL_push_subst : autosubst.

  Typeclasses Opaque CGL_push.
  Global Opaque CGL_push.

  Lemma CGL_locked_push_to_val st l :
    to_val (CGL_locked_push st l) = Some (CGL_locked_pushV st l).
  Proof. trivial. Qed.

  Lemma CGL_locked_push_of_val st l :
    of_val (CGL_locked_pushV st l) = CGL_locked_push st l.
  Proof. trivial. Qed.

  Global Opaque CGL_locked_pushV.
  Lemma CGL_locked_push_type st l Γ τ :
    typed Γ st (Tref (CGL_Stack_Ref_Type τ)) →
    typed Γ l LockType →
    typed Γ (CGL_locked_push st l) (TArrow τ TUnit).
  Proof.
    intros H1 H2.
    eapply with_lock_type; auto using CGL_push_type.
  Qed.

  Lemma CGL_locked_push_subst (st l : expr) f :
    (CGL_locked_push st l).[f] = CGL_locked_push st.[f] l.[f].
  Proof. by rewrite /CGL_locked_push; asimpl. Qed.

  Hint Rewrite CGL_locked_push_subst : autosubst.

  Typeclasses Opaque CGL_locked_push.
  Global Opaque CGL_locked_push.

  (* Coarse-grained pop *)

Lemma CGL_pop_folding (st : expr) :
    CGL_pop st =
    Lam (LetIn (Load (st.[ren (+1)]))
             (Case (Load (Var 0))
                   (InjL Unit)
                   (
                     Seq
                       (Store st.[ren (+ 3)] (Unfold (Snd (Var 0))))
                       (InjR (Fst (Var 0)))
                   )
             )
      ).
  Proof. trivial. Qed.


  Lemma CGL_pop_type st Γ τ :
    typed Γ st (Tref (CGL_Stack_Ref_Type τ)) →
    typed Γ (CGL_pop st) (TArrow TUnit (TSum TUnit τ)).
  Proof.
    intros H1.
    econstructor.
    eapply (LetIn_typed _ _ _ _ _); eauto using typed.
    - econstructor.
      eapply (context_weakening [_]); eauto.
    - eapply (Case_typed _ _ _ _ _); eauto using typed.
      repeat econstructor.
      eapply (context_weakening [_; _; _]); eauto.
      by asimpl.
 Qed.

  Lemma CGL_pop_subst (st : expr) f :
    (CGL_pop st).[f] = CGL_pop st.[f].
  Proof. by rewrite /CGL_pop; asimpl. Qed.

  Hint Rewrite CGL_pop_subst : autosubst.


  Typeclasses Opaque CGL_pop.
  Global Opaque CGL_pop.

  Lemma CGL_locked_pop_to_val st l :
    to_val (CGL_locked_pop st l) = Some (CGL_locked_popV st l).
  Proof. trivial. Qed.

  Lemma CGL_locked_pop_of_val st l :
    of_val (CGL_locked_popV st l) = CGL_locked_pop st l.
  Proof. trivial. Qed.

  Global Opaque CGL_locked_popV.

  Lemma CGL_locked_pop_type st l Γ τ :
    typed Γ st (Tref (CGL_Stack_Ref_Type τ)) →
    typed Γ l LockType →
    typed Γ (CGL_locked_pop st l) (TArrow TUnit (TSum TUnit τ)).
  Proof.
    intros H1 H2.
    eapply with_lock_type; auto using CGL_pop_type.
  Qed.

  Lemma CGL_locked_pop_subst (st l : expr) f :
    (CGL_locked_pop st l).[f] = CGL_locked_pop st.[f] l.[f].
  Proof. by rewrite /CGL_locked_pop; asimpl. Qed.

  Hint Rewrite CGL_locked_pop_subst : autosubst.

  Typeclasses Opaque CGL_locked_pop.
  Global Opaque CGL_locked_pop.

  Lemma CGL_stack_body_type st l Γ τ :
    typed Γ st (Tref (CGL_Stack_Ref_Type τ)) →
    typed Γ l LockType →
    typed Γ (CGL_stack_body st l)
          (TProd (TArrow τ TUnit) (TArrow TUnit (TSum TUnit τ))) .
  Proof.
    intros H1 H2.
    repeat (econstructor; eauto using CGL_locked_push_type,
                          CGL_locked_pop_type).
  Qed.

  Lemma CGL_stack_body_subst (st l : expr) f :
    (CGL_stack_body st l).[f] = CGL_stack_body st.[f] l.[f].
  Proof. by unfold CGL_stack_body; asimpl. Qed.

  Hint Rewrite CGL_stack_body_subst : autosubst.

  Lemma CGL_stack_type Γ :
    typed Γ CGL_stack
          (TForall
             (TProd
                (TArrow (TVar 0) TUnit)
                (TArrow TUnit (TSum TUnit (TVar 0)))
             )
          ).
  Proof.
    repeat econstructor;
      eauto 15 using newlock_type, CGL_locked_push_type, CGL_locked_pop_type, typed.
  Qed.

  Lemma CGL_stack_closed f : CGL_stack.[f] = CGL_stack.
  Proof. by unfold CGL_stack; asimpl. Qed.

End CGL_Stack.

Hint Rewrite CGL_push_subst : autosubst.
Hint Rewrite CGL_locked_push_subst : autosubst.
Hint Rewrite CGL_locked_pop_subst : autosubst.
Hint Rewrite CGL_pop_subst : autosubst.
Hint Rewrite CGL_locked_pop_subst : autosubst.
Hint Rewrite CGL_stack_body_subst : autosubst.
Hint Rewrite CGL_stack_closed : autosubst.
