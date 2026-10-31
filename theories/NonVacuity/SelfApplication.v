From SymCoreTheory Require Export Completeness.Statement.
From Stdlib Require Import Strings.String Lists.List Lia.
Import ListNotations.
Open Scope string_scope.

Section SelfApplication.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.

Definition self_var : var := "x".
Definition self_body : expr := EApp (EVar self_var) (EVar self_var).
Definition self_fun : expr := ELam self_var self_body.
Definition ω : expr := EApp self_fun self_fun.

Definition ite_expr (c a b : expr) : expr := EApp (EApp (EApp (EPrimOp op_ite) c) a) b.

Lemma eval_equal_value : forall f Φ Γ e v v',
  eval f Φ Γ e v -> v = v' -> eval f Φ Γ e v'.
Proof. intros f Φ Γ e v v' H <-. exact H. Qed.

Lemma budget_total_of_unlimited_run : forall Φ Γ e v,
  eval Inf Φ Γ e v -> budget_total Φ Γ e.
Proof.
  intros Φ Γ e v H. destruct (eval_inf_has_budget Φ Γ e v H) as [h Hh].
  exists h. intros n Hn. exists v. exact (Hh n Hn).
Qed.

Definition self_var_resolves (Γ : env) : Prop :=
  forall m Φ, eval (Fin m) Φ Γ (EVar self_var) (VBot BOutOfFuel) \/
    exists Γ0, eval (Fin m) Φ Γ (EVar self_var) (VClos Γ0 self_var self_body).

Lemma self_var_resolves_fun : forall Γ,
  self_var_resolves (ExtendEnv self_var (TSusp Γ self_fun) Γ).
Proof.
  intros Γ [| [| m]] Φ.
  - left. constructor.
  - left. eapply Eval_Var; [reflexivity |]. constructor. constructor.
  - right. exists Γ. eapply Eval_Var; [reflexivity |]. constructor. constructor.
Qed.

Lemma self_var_resolves_step : forall Γ Γ0, self_var_resolves Γ ->
  self_var_resolves (ExtendEnv self_var (TSusp Γ (EVar self_var)) Γ0).
Proof.
  intros Γ Γ0 HΓ [| m] Φ.
  - left. constructor.
  - destruct (HΓ m Φ) as [H | [Γ1 H]]; [left | right; exists Γ1];
      eapply Eval_Var; try reflexivity; constructor; exact H.
Qed.

Lemma self_body_out_of_fuel : forall n Φ Γ, self_var_resolves Γ ->
  eval (Fin n) Φ Γ self_body (VBot BOutOfFuel).
Proof.
  induction n as [| n IH]; intros Φ Γ HΓ.
  - constructor.
  - destruct (HΓ n Φ) as [H | [Γ0 H]]; eapply Eval_App; try exact H.
    + constructor.
    + constructor. apply IH. apply self_var_resolves_step. exact HΓ.
Qed.

Lemma omega_out_of_fuel : forall n Φ Γ, eval (Fin n) Φ Γ ω (VBot BOutOfFuel).
Proof.
  intros [| [| n]] Φ Γ.
  - constructor.
  - eapply Eval_App; constructor.
  - eapply Eval_App; [constructor |]. constructor.
    apply self_body_out_of_fuel. apply self_var_resolves_fun.
Qed.

Theorem self_app_budget_total : forall Φ Γ, budget_total Φ Γ ω.
Proof.
  intros Φ Γ. exists 0. intros n _. exists (VBot BOutOfFuel). apply omega_out_of_fuel.
Qed.

Inductive self_chain : env -> Prop :=
  | Chain_Fun : self_chain (ExtendEnv self_var (TSusp EmptyEnv self_fun) EmptyEnv)
  | Chain_Step : forall Γ, self_chain Γ ->
      self_chain (ExtendEnv self_var (TSusp Γ (EVar self_var)) EmptyEnv).

Lemma pc_true_never_pruned : sat pc_true = false -> False.
Proof. rewrite sat_pc_true. discriminate. Qed.

Definition self_closure : value := VClos EmptyEnv self_var self_body.

Lemma self_fun_value : forall v, eval Inf pc_true EmptyEnv self_fun v -> v = self_closure.
Proof.
  intros v H. inversion H; subst; [reflexivity | exfalso; apply pc_true_never_pruned; assumption].
Qed.

Lemma self_chain_var : forall Γ v, self_chain Γ ->
  eval Inf pc_true Γ (EVar self_var) v -> v = self_closure.
Proof.
  intros Γ v HΓ. revert v. induction HΓ as [| Γ HΓ IH]; intros v H;
    inversion H as [f Φ Γ' x t w Hlook Hforce | | | | | | | | | | | | f Φ Γ' e Hpruned |];
    subst; try (exfalso; apply pc_true_never_pruned; assumption);
    simpl in Hlook; injection Hlook as <-; simpl in Hforce; inversion Hforce; subst.
  - apply self_fun_value. assumption.
  - apply IH. assumption.
Qed.

Definition diverges_eval f Φ Γ e (v : value) : Prop :=
  f = Inf -> Φ = pc_true -> e = self_body -> self_chain Γ -> False.
Definition diverges_apply g Φ Γ vf e (v : value) : Prop :=
  g = Inf -> Φ = pc_true -> vf = self_closure -> e = EVar self_var -> self_chain Γ -> False.

Lemma self_chain_diverges : forall f Φ Γ e v, eval f Φ Γ e v -> diverges_eval f Φ Γ e v.
Proof.
  apply (eval_mut_ind diverges_eval diverges_apply
    (fun _ _ _ _ _ => True) (fun _ _ _ _ => True)
    (fun _ _ _ _ _ _ => True) (fun _ _ _ _ _ _ => True));
    unfold diverges_eval, diverges_apply; intros; try exact I; try discriminate.
  - match goal with
    | Hf : Live _ = Inf, He : EApp _ _ = self_body, Happ : _ -> _ -> _ = self_closure -> _ |- _ =>
        injection Hf as ->; unfold self_body in He; injection He as -> ->; subst;
        eapply Happ; try reflexivity; [eapply self_chain_var; eassumption | assumption]
    end.
  - subst. apply pc_true_never_pruned. assumption.
  - match goal with
    | Hc : VClos _ _ _ = self_closure, IH : _ -> _ -> _ = self_body -> _ |- _ =>
        unfold self_closure in Hc; injection Hc as -> -> ->; subst;
        apply IH; try reflexivity; apply Chain_Step; assumption
    end.
Qed.

Theorem self_app_no_value : ~ exists v, EmptyEnv ⊢ᶜ ω ⇓ᶜ v.
Proof.
  intros [v H].
  inversion H as [| | | | | f Φ Γ ef ea vf w Hfun Happ | | | | | | | f Φ Γ e Hpruned |];
    subst; [| apply pc_true_never_pruned; assumption].
  apply self_fun_value in Hfun. subst vf.
  inversion Happ; subst.
  eapply self_chain_diverges; try eassumption; try reflexivity. apply Chain_Fun.
Qed.

End SelfApplication.

Ltac ite_arity_fits := rewrite ?op_ite_arity; cbn; lia.

Ltac run_ite_spine :=
  eapply Eval_App;
  [ eapply Eval_App;
    [ eapply Eval_App;
      [ constructor; apply Prim_Partial; ite_arity_fits
      | apply Apply_Prim; apply Prim_Partial; ite_arity_fits ]
    | apply Apply_Prim; apply Prim_Partial; ite_arity_fits ]
  | apply Apply_Prim; eapply Prim_Ite ].
