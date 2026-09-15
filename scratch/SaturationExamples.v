From SymCoreTheory Require Import SymCore ConCore Model Saturation.
From Stdlib Require Import Strings.String Lists.List Lia.
Import ListNotations.
Open Scope string_scope.

Definition tt : @expr model_sorts := ELit true.
Definition partial_and : @expr model_sorts := EApp (EPrimOp PAnd) tt.
Definition apply_to_true : @expr model_sorts := ELam "f" (EApp (EVar "f") tt).
Definition partial_program : @expr model_sorts := EApp apply_to_true partial_and.
Definition eta_and : @expr model_sorts := ELam "y" (EApp (EApp (EPrimOp PAnd) tt) (EVar "y")).
Definition eta_program : @expr model_sorts := EApp apply_to_true eta_and.

Lemma partial_program_not_saturated : ~ saturated partial_program.
Proof. intros [_ [H _]]. discriminate H. Qed.

Lemma eta_program_saturated : saturated eta_program.
Proof. repeat split. Qed.

Lemma eta_program_evaluates_under : forall Φ, Φ ; · ⊢ eta_program ⇓ tt.
Proof.
  intros Φ. unfold eta_program, apply_to_true, eta_and.
  eapply Eval_AppSpine; [apply Comp_Lam | apply Eval_Lam |].
  apply Eval_AppAbs.
  eapply Eval_AppSpine; [apply Comp_Var; discriminate | eapply Eval_Var; [reflexivity | apply Eval_Lam] |].
  apply Eval_AppAbs.
  change (dec Unlimited) with (@Live Unlimited).
  rewrite <- (eq_refl : @reduce_prim model_sorts model_solver PAnd (tt :: tt :: nil) = tt).
  eapply Eval_AppPrim; [reflexivity | reflexivity |].
  constructor; [apply Eval_Lit |].
  constructor; [eapply Eval_Var; [reflexivity | apply Eval_Lit] | constructor].
Qed.

Lemma eta_program_budget_total : forall Φ, budget_total Φ · eta_program.
Proof.
  intros Φ. apply budget_total_of_terminating. exists tt. apply eta_program_evaluates_under.
Qed.

Ltac no_rule_applies :=
  match goal with
  | [ Hu : unspool_app _ _ = (ECon _, _) |- _ ] => simpl in Hu; discriminate Hu
  | [ Hu : unspool_app _ _ = (EIf _ _ _, _) |- _ ] => simpl in Hu; discriminate Hu
  | [ Hu : unspool_app _ _ = (EPrimOp _, _), Hl : length _ = primop_arity _ |- _ ] =>
      simpl in Hu; injection Hu as <- <-; discriminate Hl
  | [ Hu : unspool_app _ _ = (EPrimOp _, _) |- _ ] => simpl in Hu; discriminate Hu
  | [ Hc : Comp _ (EPrimOp _) |- _ ] => inversion Hc
  | [ Hc : Comp _ (EThunk _ (ELam _ _)) |- _ ] => inversion Hc; discriminate
  | [ Hs : sat _ = false |- _ ] => discriminate Hs
  | [ Hl : lookup_env _ _ = None |- _ ] => discriminate Hl
  end.

Definition f_env : @environment model_sorts := extend_env · "f" · partial_and.

Lemma partial_and_no_value_live : forall k Φ Γ v, ~ eval (Fin (S k)) Φ Γ partial_and v.
Proof.
  intros k Φ Γ v H. unfold partial_and in H. simpl in H.
  inversion H; subst; no_rule_applies.
Qed.

Lemma var_f_no_value : forall k Φ v, ~ eval (Fin (S (S k))) Φ f_env (EVar "f") v.
Proof.
  intros k Φ v H. simpl in H.
  inversion H; subst; try no_rule_applies.
  simpl in *. match goal with [ Hl : Some _ = Some _ |- _ ] => injection Hl as <- <- end.
  eapply partial_and_no_value_live. eassumption.
Qed.

Lemma body_no_value : forall k Φ v,
  ~ eval (Fin (S (S (S k)))) Φ f_env (EApp (EVar "f") tt) v.
Proof.
  intros k Φ v H. simpl in H.
  inversion H; subst; try no_rule_applies.
  exact (var_f_no_value k Φ _ ltac:(eassumption)).
Qed.

Lemma closure_app_no_value : forall k Φ v,
  ~ eval (Fin (S (S (S (S k))))) Φ · (EApp (EThunk · (ELam "f" (EApp (EVar "f") tt))) partial_and) v.
Proof.
  intros k Φ v H. simpl in H.
  inversion H; subst; try no_rule_applies.
  exact (body_no_value k Φ v ltac:(eassumption)).
Qed.

Lemma partial_program_no_value : forall k Φ v,
  ~ eval (Fin (S (S (S (S (S k)))))) Φ · partial_program v.
Proof.
  intros k Φ v H. unfold partial_program, apply_to_true in H. simpl in H.
  inversion H; subst; try no_rule_applies.
  match goal with
  | [ Hl : eval _ _ _ (ELam _ _) ?ef, Happ : eval _ _ _ (EApp ?ef _) _ |- _ ] =>
      simpl in Hl; inversion Hl; subst; try no_rule_applies;
      exact (closure_app_no_value k Φ v Happ)
  end.
Qed.

Definition x_var : @expr model_sorts := EVar "x".
Definition partial_branch : @expr model_sorts := EIf x_var tt partial_program.
Definition eta_branch : @expr model_sorts := EIf x_var tt eta_program.

Lemma partial_branch_not_saturated : ~ saturated partial_branch.
Proof. intros [_ [_ H]]. exact (partial_program_not_saturated H). Qed.

Lemma eta_branch_saturated : saturated eta_branch.
Proof. repeat split. Qed.

Lemma partial_branch_no_value : forall k Φ v,
  ~ eval (Fin (S (S (S (S (S (S k))))))) Φ · partial_branch v.
Proof.
  intros k Φ v H. unfold partial_branch in H. simpl in H.
  inversion H; subst; try no_rule_applies.
  exact (partial_program_no_value k _ _ ltac:(eassumption)).
Qed.

Theorem partial_branch_not_budget_total : forall Φ, ~ budget_total Φ · partial_branch.
Proof.
  intros Φ [h Hh].
  destruct (Hh (S (S (S (S (S (S h)))))) ltac:(lia)) as [v Hv].
  exact (partial_branch_no_value h Φ v Hv).
Qed.

Theorem eta_branch_evaluates : forall Φ, Φ ; · ⊢ eta_branch ⇓ EIf x_var tt tt.
Proof.
  intros Φ. unfold eta_branch.
  eapply Eval_If; [apply Eval_SymVar; reflexivity | reflexivity | apply Eval_Lit |].
  apply eta_program_evaluates_under.
Qed.

Theorem eta_branch_budget_total : forall Φ, budget_total Φ · eta_branch.
Proof.
  intros Φ. apply budget_total_of_terminating. exists (EIf x_var tt tt).
  apply eta_branch_evaluates.
Qed.
