From SymCoreTheory Require Import SymCore ConCore.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.
Open Scope string_scope.

Section NegationWasUnsatisfiable.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}
  {reduce_prim_solvable_law : ReducePrimSolvable}.

Definition OldIteContains : Prop :=
  forall σ S ec et ef e_c,
    contains σ S (EIf ec et ef) e_c ->
    contains σ S (reduce_prim op_ite (ec :: et :: ef :: nil)) e_c.

Definition ArmsDenoteIteContains : Prop :=
  forall σ S ec et ef pt pf e_c,
    denotes S et pt -> denotes S ef pf ->
    contains σ S (EIf ec et ef) e_c ->
    contains σ S (reduce_prim op_ite (ec :: et :: ef :: nil)) e_c.

Definition guard : expr := EVar "x".
Definition symbolic_guard : symvars := only "x".
Definition truth_model : valuation := fun _ => lit_true.
Definition literal_model (l : lit) : valuation := fun _ => l.

Lemma guard_denotes : denotes symbolic_guard guard (PCVar "x").
Proof.
  intros Γ Hfree. unfold guard. simpl.
  rewrite (Hfree "x" (only_self "x")). reflexivity.
Qed.

Lemma truth_model_takes_then : models_cond truth_model symbolic_guard guard.
Proof. exists (PCVar "x"). split; [exact guard_denotes | reflexivity]. Qed.

Lemma literal_model_takes_else : forall l,
  prim_value op_not (l :: nil) = lit_true ->
  models_not_cond (literal_model l) symbolic_guard guard.
Proof. intros l Hl. exists (PCVar "x"). split; [exact guard_denotes | exact Hl]. Qed.

Definition solver_ite (et ef : expr) : expr := reduce_prim op_ite (guard :: et :: ef :: nil).

Lemma solver_ite_solvable : forall et ef,
  Solvable · et -> Solvable · ef -> Solvable · (solver_ite et ef).
Proof.
  intros et ef Ht Hf. apply reduce_prim_solvable.
  apply Forall_cons; [apply Solvable_Var; reflexivity |].
  apply Forall_cons; [exact Ht | apply Forall_cons; [exact Hf | apply Forall_nil]].
Qed.

Lemma solvable_instance_of_variable : forall σ S R w,
  Solvable · R -> contains σ S R (EVar w) -> R = EVar w.
Proof.
  intros σ S R w Hs Hc. inversion Hc; subst; try reflexivity; inversion Hs.
Qed.

Theorem old_ite_contains_refutes_negation :
  OldIteContains -> forall l, prim_value op_not (l :: nil) <> lit_true.
Proof.
  intros Hold l Hnot.
  assert (Hs : Solvable · (solver_ite (EVar "y") (EVar "z")))
    by (apply solver_ite_solvable; apply Solvable_Var; reflexivity).
  assert (Hy : contains truth_model symbolic_guard (solver_ite (EVar "y") (EVar "z")) (EVar "y")).
  { apply Hold. apply Cont_If_True; [exact truth_model_takes_then | apply Cont_Var_Bound; reflexivity]. }
  assert (Hz : contains (literal_model l) symbolic_guard (solver_ite (EVar "y") (EVar "z")) (EVar "z")).
  { apply Hold. apply Cont_If_False;
      [exact (literal_model_takes_else l Hnot) | apply Cont_Var_Bound; reflexivity]. }
  pose proof (solvable_instance_of_variable _ _ _ _ Hs Hy) as Ey.
  pose proof (solvable_instance_of_variable _ _ _ _ Hs Hz) as Ez.
  rewrite Ey in Ez. discriminate Ez.
Qed.

Definition and_arm : expr := EApp (EApp (EPrimOp op_and) guard) guard.
Definition not_arm : expr := EApp (EPrimOp op_not) guard.

Lemma and_arm_denotes : denotes symbolic_guard and_arm (PCPrim op_and (PCVar "x" :: PCVar "x" :: nil)).
Proof.
  intros Γ Hfree. unfold and_arm, guard. simpl.
  rewrite (Hfree "x" (only_self "x")). reflexivity.
Qed.

Lemma not_arm_denotes : denotes symbolic_guard not_arm (PCPrim op_not (PCVar "x" :: nil)).
Proof.
  intros Γ Hfree. unfold not_arm, guard. simpl.
  rewrite (Hfree "x" (only_self "x")). reflexivity.
Qed.

Lemma solvable_instance_head : forall σ S R f c,
  Solvable · R -> contains σ S R (EApp f c) ->
  exists Rf Rc, R = EApp Rf Rc /\ Solvable · Rf /\ contains σ S Rf f.
Proof.
  intros σ S R f c Hs Hc. inversion Hc; subst; try (inversion Hs; fail).
  inversion Hs; subst. eexists _, _. split; [reflexivity | split; eassumption].
Qed.

Lemma solvable_instance_of_primop : forall σ S R p,
  Solvable · R -> contains σ S R (EPrimOp p) -> R = EPrimOp p.
Proof.
  intros σ S R p Hs Hc. inversion Hc; subst; try reflexivity; inversion Hs.
Qed.

Theorem arms_denote_ite_contains_refutes_negation :
  ArmsDenoteIteContains -> forall l, prim_value op_not (l :: nil) <> lit_true.
Proof.
  intros Harms l Hnot.
  assert (Hs : Solvable · (solver_ite and_arm not_arm)).
  { apply solver_ite_solvable; repeat constructor. }
  assert (Hand : contains truth_model symbolic_guard (solver_ite and_arm not_arm)
                   (EApp (EApp (EPrimOp op_and) (ELit lit_true)) (ELit lit_true))).
  { eapply Harms; [exact and_arm_denotes | exact not_arm_denotes |].
    apply Cont_If_True; [exact truth_model_takes_then |].
    repeat apply Cont_App; try apply Cont_PrimOp; apply (Cont_Var_Sym truth_model); reflexivity. }
  assert (Hnot_c : contains (literal_model l) symbolic_guard (solver_ite and_arm not_arm)
                     (EApp (EPrimOp op_not) (ELit l))).
  { eapply Harms; [exact and_arm_denotes | exact not_arm_denotes |].
    apply Cont_If_False; [exact (literal_model_takes_else l Hnot) |].
    apply Cont_App; [apply Cont_PrimOp | apply (Cont_Var_Sym (literal_model l)); reflexivity]. }
  destruct (solvable_instance_head _ _ _ _ _ Hs Hand) as [R1 [C1 [ER1 [Hs1 Hc1]]]].
  destruct (solvable_instance_head _ _ _ _ _ Hs1 Hc1) as [R2 [C2 [ER2 [Hs2 Hc2]]]].
  destruct (solvable_instance_head _ _ _ _ _ Hs Hnot_c) as [R3 [C3 [ER3 [Hs3 Hc3]]]].
  rewrite ER1 in ER3. injection ER3 as ER3 _. subst R3.
  rewrite ER2 in Hs3, Hc3.
  pose proof (solvable_instance_of_primop _ _ _ _ Hs3 Hc3) as Eop. discriminate Eop.
Qed.

End NegationWasUnsatisfiable.

Print Assumptions old_ite_contains_refutes_negation.
Print Assumptions arms_denote_ite_contains_refutes_negation.
