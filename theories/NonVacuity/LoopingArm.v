From SymCoreTheory Require Export NonVacuity.SoundnessInstances.
From SymCoreTheory Require Import Completeness.Completeness.
From Stdlib Require Import Strings.String Lists.List Lia.
Import ListNotations.
Open Scope string_scope.

Definition loop_alts : list alt := [Alt "True" [] (ELit true)].
Definition loop_guard (c : expr) : expr := ite_expr c (ECon "True") ω.
Definition loop_sym : expr := ECase (loop_guard (ESym sym_s)) loop_alts.
Definition loop_con (σ : valuation) : expr := ECase (loop_guard (ELit (σ sym_s))) loop_alts.

Lemma loop_contains : forall σ, contains_expr σ loop_sym (loop_con σ).
Proof. intros σ. repeat constructor. Qed.

Lemma loop_concore : forall σ, concore_expr (loop_con σ).
Proof. intros σ. repeat constructor. Qed.

Lemma loop_con_run : forall σ, σ sym_s = true ->
  EmptyEnv ⊢ᶜ loop_con σ ⇓ᶜ VPrim (PLit true).
Proof.
  intros σ Hs. unfold loop_con. rewrite Hs.
  eapply Eval_Case.
  - unfold loop_guard, ite_expr. run_ite_spine.
    + constructor. constructor.
    + refine (Select_True _ _ _ _ _ _). constructor. constructor.
  - cbn. eapply Fold_Con; [reflexivity | constructor].
Qed.

Definition loop_sym_value : value := VIf (PSym sym_s) (VPrim (PLit true)) (VBot BOutOfFuel).

Lemma loop_sym_runs_out_of_fuel : forall n, 5 <= n ->
  eval (Fin n) pc_true EmptyEnv loop_sym loop_sym_value.
Proof.
  intros n Hn. do 5 (destruct n as [| n]; [lia |]).
  eapply eval_equal_value; [eapply Eval_Case |].
  - unfold loop_guard, ite_expr. run_ite_spine.
    + constructor. constructor.
    + apply Select_Sym; [reflexivity | constructor; constructor | constructor; apply omega_out_of_fuel].
  - cbn. eapply Fold_If; [eapply Fold_Con; [reflexivity | constructor] | constructor].
  - reflexivity.
Qed.

Theorem loop_budget_total : budget_total pc_true EmptyEnv loop_sym.
Proof.
  exists 5. intros n Hn. exists loop_sym_value. exact (loop_sym_runs_out_of_fuel n Hn).
Qed.

Theorem loop_completeness : forall σ, σ sym_s = true ->
  exists h, forall n, h <= n ->
    exists v_s, eval (Fin n) pc_true EmptyEnv loop_sym v_s /\
      contains_val σ v_s (VPrim (PLit true)).
Proof.
  intros σ Hs.
  exact (concore_completeness_budget pc_true EmptyEnv EmptyEnv σ loop_sym (loop_con σ)
    (VPrim (PLit true)) (models_pc_true σ) (Contains_Empty σ) (loop_contains σ)
    (loop_concore σ) Concrete_Empty loop_budget_total (loop_con_run σ Hs)).
Qed.

Theorem loop_completeness_value : forall σ, σ sym_s = true ->
  contains_val σ loop_sym_value (VPrim (PLit true)).
Proof.
  intros σ Hs. apply Contains_VIfT; [exact Hs | repeat constructor].
Qed.
