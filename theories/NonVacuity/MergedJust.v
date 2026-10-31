From SymCoreTheory Require Export NonVacuity.SoundnessInstances.
From SymCoreTheory Require Import ConCore.Determinism.
From Stdlib Require Import Strings.String Lists.List Lia.
Import ListNotations.
Open Scope string_scope.

Definition just_field_var : var := "z".
Definition just_of (e : expr) : expr := EApp (ECon "Just") e.
Definition just_scrutinee (c : expr) : expr :=
  ite_expr c (just_of (ELit true)) (just_of (ELit false)).
Definition just_field_alts : list alt := [Alt "Just" [just_field_var] (EVar just_field_var)].
Definition just_field_case (c : expr) : expr := ECase (just_scrutinee c) just_field_alts.

Definition just_field_sym : expr := just_field_case (ESym sym_s).
Definition just_field_con (σ : valuation) : expr := just_field_case (ELit (σ sym_s)).

Definition then_field : thunk := TSusp EmptyEnv (ELit true).
Definition else_field : thunk := TSusp EmptyEnv (ELit false).
Definition merged_field : thunk := TIf (PSym sym_s) then_field else_field.
Definition merged_just : value := VCon "Just" [merged_field].
Definition just_field_value : value := VPrim (PApp PIte (PSym sym_s :: PLit true :: PLit false :: nil)).

Lemma just_leaves_merge :
  ite (PSym sym_s) (VCon "Just" [then_field]) (VCon "Just" [else_field]) = merged_just.
Proof. reflexivity. Qed.

Lemma just_scrutinee_merges :
  eval Inf pc_true EmptyEnv (just_scrutinee (ESym sym_s)) merged_just.
Proof.
  eapply eval_equal_value; [unfold just_scrutinee, ite_expr; run_ite_spine |].
  - constructor. constructor.
  - eapply Select_Sym;
      [reflexivity | constructor; eapply Eval_App; constructor
      | constructor; eapply Eval_App; constructor].
  - reflexivity.
Qed.

Lemma merged_just_is_whnf : merge merged_just = merged_just.
Proof. reflexivity. Qed.

Lemma just_field_sym_run : eval Inf pc_true EmptyEnv just_field_sym just_field_value.
Proof.
  eapply Eval_Case; [exact just_scrutinee_merges |].
  rewrite merged_just_is_whnf. eapply Fold_Con; [reflexivity |].
  eapply eval_equal_value.
  - eapply Eval_Var; [reflexivity |]. eapply Force_If; constructor; constructor.
  - reflexivity.
Qed.

Lemma just_field_con_run : forall σ,
  EmptyEnv ⊢ᶜ just_field_con σ ⇓ᶜ VPrim (PLit (σ sym_s)).
Proof.
  intros σ. unfold just_field_con, just_field_case.
  destruct (σ sym_s); eapply Eval_Case;
    try (unfold just_scrutinee, ite_expr; run_ite_spine; [constructor; constructor |]).
  - refine (Select_True _ _ _ _ _ _). constructor. eapply Eval_App; constructor.
  - cbn. eapply Fold_Con; [reflexivity |]. eapply Eval_Var; [reflexivity | constructor; constructor].
  - apply Select_False; [discriminate | constructor; eapply Eval_App; constructor].
  - cbn. eapply Fold_Con; [reflexivity |]. eapply Eval_Var; [reflexivity | constructor; constructor].
Qed.

Lemma just_field_contains : forall σ, contains_expr σ just_field_sym (just_field_con σ).
Proof. intros σ. repeat constructor. Qed.

Lemma just_field_concore : forall σ, concore_expr (just_field_con σ).
Proof. intros σ. repeat constructor. Qed.

Theorem merged_just_soundness : forall σ,
  exists v_c, EmptyEnv ⊢ᶜ just_field_con σ ⇓ᶜ v_c /\
    contains_val σ just_field_value v_c /\ v_c = VPrim (PLit (σ sym_s)).
Proof.
  intros σ.
  destruct (concore_soundness pc_true EmptyEnv EmptyEnv σ just_field_sym (just_field_con σ)
    just_field_value (models_pc_true σ) (Contains_Empty σ) (just_field_contains σ)
    (just_field_concore σ) Concrete_Empty just_field_sym_run) as [v_c [Hrun Hrel]].
  exists v_c. split; [exact Hrun | split; [exact Hrel |]].
  exact (concore_eval_deterministic EmptyEnv (just_field_con σ) v_c (VPrim (PLit (σ sym_s)))
    Concrete_Empty (just_field_concore σ) Hrun (just_field_con_run σ)).
Qed.
