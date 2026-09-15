From SymCoreTheory Require Import SymCore ConCore.
From Stdlib Require Import Strings.String Lists.List Lia.
Import ListNotations.
Open Scope string_scope.

Section BranchApplication.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : ConCoreLaws}.

Definition guard_var : var := "x".

Definition picked_alts : list alt :=
  Alt "T" nil (ELam "y" (EVar "y")) :: Alt "F" nil (ELam "z" (EVar "z")) :: nil.

Definition symbolic_scrutinee : expr := EIf (EVar guard_var) (ECon "T") (ECon "F").

Definition symbolic_branch_application (l : lit) : expr :=
  EApp (ECase symbolic_scrutinee picked_alts) (ELit l).

Definition concrete_branch_application (l : lit) : expr :=
  EApp (ECase (ECon "T") picked_alts) (ELit l).

Definition branch_application_value (l : lit) : expr :=
  EIf (EVar guard_var) (ELit l) (ELit l).

Definition guard_symvars : symvars := fun v => String.eqb v guard_var.

Lemma branch_application_evaluates : forall Φ l,
  sat Φ = true ->
  sat (Φ ∧ PCVar guard_var) = true ->
  sat (Φ ∧ ¬ PCVar guard_var) = true ->
  Φ ; · ⊢ symbolic_branch_application l ⇓ branch_application_value l.
Proof.
  intros Φ l Hsat Hthen Helse.
  unfold symbolic_branch_application.
  eapply Eval_AppSpine.
  - apply Comp_Case.
  - eapply Eval_Case.
    + eapply Eval_If.
      * apply Eval_SymVar. reflexivity.
      * reflexivity.
      * exact (Eval_Con Unlimited _ _ (ECon "T") "T" nil eq_refl).
      * exact (Eval_Con Unlimited _ _ (ECon "F") "F" nil eq_refl).
    + cbn. eapply FoldAlts_If.
      * reflexivity.
      * eapply FoldAlts_Con; [reflexivity | reflexivity | apply Eval_Lam].
      * eapply FoldAlts_Con; [reflexivity | reflexivity | apply Eval_Lam].
  - eapply Eval_AppIf; [reflexivity |].
    cbn. eapply Eval_If.
    + apply Eval_SymVar. reflexivity.
    + reflexivity.
    + apply Eval_AppAbs. eapply Eval_Var; [reflexivity |]. apply Eval_Lit.
    + apply Eval_AppAbs. eapply Eval_Var; [reflexivity |]. apply Eval_Lit.
Qed.

Lemma branch_application_value_contains_literal : forall σ l,
  σ ⊨ PCVar guard_var ->
  contains σ guard_symvars (branch_application_value l) (ELit l).
Proof.
  intros σ l Hσ.
  apply Cont_If_True; [| apply Cont_Lit].
  exists (PCVar guard_var). split; [| exact Hσ].
  intros Γ Hfree. cbn. rewrite (Hfree guard_var eq_refl). reflexivity.
Qed.

Lemma concrete_branch_application_evaluates : forall l,
  ⊢ᶜ concrete_branch_application l ⇓ᶜ ELit l.
Proof.
  intros l. unfold eval_con, concrete_branch_application.
  eapply Eval_AppSpine.
  - apply Comp_Case.
  - eapply Eval_Case.
    + exact (Eval_Con Unlimited _ _ (ECon "T") "T" nil eq_refl).
    + cbn. eapply FoldAlts_Con; [reflexivity | reflexivity | apply Eval_Lam].
  - cbn. apply Eval_AppAbs. eapply Eval_Var; [reflexivity |]. apply Eval_Lit.
Qed.

Theorem branch_application_regression : forall Φ σ l,
  sat Φ = true ->
  sat (Φ ∧ PCVar guard_var) = true ->
  sat (Φ ∧ ¬ PCVar guard_var) = true ->
  σ ⊨ PCVar guard_var ->
  (exists v, Φ ; · ⊢ symbolic_branch_application l ⇓ v /\
             contains σ guard_symvars v (ELit l)) /\
  ⊢ᶜ concrete_branch_application l ⇓ᶜ ELit l.
Proof.
  intros Φ σ l Hsat Hthen Helse Hσ. split.
  - exists (branch_application_value l). split.
    + exact (branch_application_evaluates Φ l Hsat Hthen Helse).
    + exact (branch_application_value_contains_literal σ l Hσ).
  - exact (concrete_branch_application_evaluates l).
Qed.

End BranchApplication.
