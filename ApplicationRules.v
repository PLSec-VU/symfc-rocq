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

Section OutOfFuel.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : ConCoreLaws}.

Lemma out_of_fuel_not_concore : ~ concore_expr (EBot BOutOfFuel).
Proof. intros H. inversion H. Qed.

Lemma out_of_fuel_contains_nothing_concrete : forall σ S e_c,
  concore_expr e_c -> ~ contains σ S (EBot BOutOfFuel) e_c.
Proof.
  intros σ S e_c Hcon Hcont.
  inversion Hcont; subst.
  - exact (out_of_fuel_not_concore Hcon).
  - match goal with
    | [ H : unspool_app (EBot _) [] = _ |- _ ] => discriminate H
    end.
Qed.

Lemma concrete_evaluation_never_out_of_fuel : forall Γ e,
  concrete_env Γ -> concore_expr e -> ~ Γ ⊢ᶜ e ⇓ᶜ EBot BOutOfFuel.
Proof.
  intros Γ e Henv Hcon Heval.
  exact (out_of_fuel_not_concore (concore_eval_closed Γ e (EBot BOutOfFuel) Henv Hcon Heval)).
Qed.

End OutOfFuel.

Section RuleDisjointness.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : ConCoreLaws}.

Lemma comp_excludes_closure : forall Γ Γ' x b, ~ Comp Γ (EThunk Γ' (ELam x b)).
Proof. intros Γ Γ' x b H. inversion H; subst. discriminate. Qed.

Lemma comp_excludes_cast : forall Γ e γ, ~ Comp Γ (ECast e γ).
Proof. intros Γ e γ H. inversion H. Qed.

Lemma comp_excludes_branch : forall Γ ec et ef, ~ Comp Γ (EIf ec et ef).
Proof. intros Γ ec et ef H. inversion H. Qed.

Lemma comp_excludes_bottom : forall Γ b, ~ Comp Γ (EBot b).
Proof. intros Γ b H. inversion H. Qed.

Lemma comp_excludes_whole_spine_head : forall Γ e,
  has_whole_spine_rule (spine_head e) = true -> ~ Comp Γ e.
Proof.
  intros Γ e Hhead Hcomp.
  destruct Hcomp; simpl in *; congruence.
Qed.

Lemma spine_head_of_unspool : forall e h args,
  unspool_app e [] = (h, args) -> spine_head e = h.
Proof.
  intros e h args Hu.
  rewrite <- (fst_unspool_app e []). rewrite Hu. reflexivity.
Qed.

Lemma comp_excludes_con_spine : forall Γ e d args,
  unspool_app e [] = (ECon d, args) -> ~ Comp Γ e.
Proof.
  intros Γ e d args Hu. apply comp_excludes_whole_spine_head.
  rewrite (spine_head_of_unspool e _ args Hu). reflexivity.
Qed.

Lemma comp_excludes_prim_spine : forall Γ e p args,
  unspool_app e [] = (EPrimOp p, args) -> ~ Comp Γ e.
Proof.
  intros Γ e p args Hu. apply comp_excludes_whole_spine_head.
  rewrite (spine_head_of_unspool e _ args Hu). reflexivity.
Qed.

Lemma comp_excludes_branch_spine : forall Γ e ec et ef args,
  unspool_app e [] = (EIf ec et ef, args) -> ~ Comp Γ e.
Proof.
  intros Γ e ec et ef args Hu. apply comp_excludes_whole_spine_head.
  rewrite (spine_head_of_unspool e _ args Hu). reflexivity.
Qed.

Definition app_if_fires (e : expr) : Prop :=
  exists e1 e2 ec et ef args,
    e = EApp e1 e2 /\ unspool_app (EApp e1 e2) [] = (EIf ec et ef, args).

Definition app_prim_fires (e : expr) : Prop :=
  exists e1 e2 p args,
    e = EApp e1 e2 /\ unspool_app (EApp e1 e2) [] = (EPrimOp p, args) /\
    length args = primop_arity p.

Definition con_fires (e : expr) : Prop :=
  exists d args, unspool_app e [] = (ECon d, args).

Lemma app_if_never_overlaps_app_prim : forall e,
  ~ (app_if_fires e /\ app_prim_fires e).
Proof.
  intros e [Hif Hprim].
  destruct Hif as (e1 & e2 & ec & et & ef & args & He & Hu_if).
  destruct Hprim as (f1 & f2 & p & pargs & He' & Hu_prim & _).
  subst e. injection He' as <- <-. congruence.
Qed.

Lemma app_if_never_overlaps_con : forall e,
  ~ (app_if_fires e /\ con_fires e).
Proof.
  intros e [Hif Hcon].
  destruct Hif as (e1 & e2 & ec & et & ef & args & He & Hu_if).
  destruct Hcon as (d & cargs & Hu_con).
  subst e. congruence.
Qed.

End RuleDisjointness.
