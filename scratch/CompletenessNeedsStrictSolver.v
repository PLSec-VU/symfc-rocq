From SymCoreTheory Require Import SymCore ConCore Completeness Model.
From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat Lia.
Import ListNotations.
Open Scope string_scope.

Definition guard_var : var := "y".
Definition guard : expr := EVar guard_var.

Fixpoint loop_bound (L : nat) (w : expr) : nat :=
  match w with
  | EIf _ a _ => S (Nat.max (L + 2) (loop_bound (S L) a + 2))
  | _ => 0
  end.

Definition stack_height (w : expr) : nat := loop_bound 0 w + 3.

Fixpoint stack (c : expr) (k : nat) (t : expr) : expr :=
  match k with
  | O => t
  | S k' => EIf c (stack c k' t) t
  end.

Fixpoint stacking_cast (e : expr) (γ : coercion) : expr :=
  match e with
  | EIf c a b => EIf c (stack c (stack_height b) (stacking_cast a γ)) (stacking_cast b γ)
  | _ => e
  end.

Definition stacking_solver : SymCoreSolver :=
  Build_SymCoreSolver
    model_sat (PCLit true) eq_refl model_reduce_prim
    stacking_cast keep_coercion keep_type.

#[local] Existing Instance stacking_solver | 0.

Lemma stack_contains : forall σ S c t x k,
  models_cond σ S c -> contains σ S t x -> contains σ S (stack c k t) x.
Proof.
  intros σ S c t x k Hc Ht. induction k as [| k IH]; simpl; [exact Ht |].
  apply Cont_If_True; assumption.
Qed.

#[local] Instance stacking_cast_concore : CastExprConcore.
Proof.
  intros e γ H. destruct e; simpl; try exact H.
  exfalso. eapply not_concore_if. exact H.
Qed.

#[local] Instance stacking_cast_contains : CastExprContains.
Proof.
  intros σ S es ec γ H.
  induction H; simpl; try (constructor; assumption).
  - destruct ec; try discriminate. eapply Cont_Thunk_Outer; eassumption.
  - apply Cont_If_True; [assumption |]. apply stack_contains; assumption.
  - destruct (cont_denote_is_app es p args H H1) as [f [a Hfa]]. subst es.
    eapply Cont_Denote; eassumption.
Qed.

Lemma stack_scoped : forall L c k t, scoped L c -> scoped L t -> scoped L (stack c k t).
Proof. intros L c k t Hc Ht. induction k; simpl; [exact Ht | apply Scoped_If; assumption]. Qed.

#[local] Instance stacking_cast_scoped : CastExprScoped.
Proof.
  intros e γ H. change (scoped nil (stacking_cast e γ)). unfold closed_term in H.
  induction e; try exact H.
  inversion H; subst. simpl.
  apply Scoped_If; [assumption | apply stack_scoped; [assumption | apply IHe2; assumption] |].
  apply IHe3. assumption.
Qed.

#[local] Instance stacking_laws : ConCoreLaws.
Proof.
  exact (@concore_laws model_sorts stacking_solver
    model_reduce_prim_solvable model_reduce_prim_saturated
    model_reduce_prim_concore stacking_cast_concore
    model_reduce_prim_scoped stacking_cast_scoped
    model_models_sat model_prim_value_and
    model_reduce_prim_contains model_reduce_prim_denote model_reduce_prim_ground_value
    stacking_cast_contains
    model_subst_coerc_contains_env model_subst_type_contains_env).
Qed.

Definition Sg : symvars := fun v => String.eqb v guard_var.
Definition sig : valuation := fun v => if String.eqb v guard_var then true else false.
Definition wild_cast : coercion := MkCoercion (TyCon tt) (TyCon tt) RoleNominal.
Definition diverging_untaken_arm : expr := ECast self_app wild_cast.
Definition quarantine_sym : expr := EIf guard (ELit true) diverging_untaken_arm.
Definition quarantine_con : expr := ELit true.

Lemma sig_models_guard : @models model_sorts sig (PCVar guard_var).
Proof. unfold models. cbn. reflexivity. Qed.

Lemma guard_models_cond : models_cond sig Sg guard.
Proof.
  exists (PCVar guard_var). split; [| exact sig_models_guard].
  intros Γ Hfree. cbn. rewrite (Hfree guard_var eq_refl). reflexivity.
Qed.

Lemma quarantine_contains : contains sig Sg quarantine_sym quarantine_con.
Proof.
  apply Cont_If_True; [apply guard_models_cond | apply Cont_Lit].
Qed.

Lemma quarantine_con_concore : concore_expr quarantine_con.
Proof. apply Con_Lit. Qed.

Lemma quarantine_env : contains_env sig Sg · ·.
Proof. apply Cont_Env_Empty. Qed.

Lemma sig_models_pc_true : @models model_sorts sig (@pc_true model_sorts stacking_solver).
Proof. unfold models. cbn. reflexivity. Qed.

Lemma quarantine_concrete :
  @eval_con model_sorts stacking_solver · quarantine_con (ELit true).
Proof. apply Eval_Lit. Qed.

Lemma quarantine_value_at_fuel : forall n,
  exists v, @eval model_sorts stacking_solver (Fin (S (S n))) pc_true · quarantine_sym v
            /\ contains sig Sg v (ELit true).
Proof.
  intros n.
  destruct (self_app_has_value_at_every_budget n (pc_true ∧ ¬ PCVar guard_var) ·)
    as [sv Hsv].
  eexists. split.
  - unfold quarantine_sym, diverging_untaken_arm.
    eapply Eval_If.
    + apply Eval_SymVar. reflexivity.
    + cbn. reflexivity.
    + cbn. apply Eval_Lit.
    + cbn. apply Eval_Cast. cbn. exact Hsv.
  - apply Cont_If_True; [apply guard_models_cond | apply Cont_Lit].
Qed.

Lemma quarantine_budget_total :
  @budget_total model_sorts stacking_solver pc_true · quarantine_sym.
Proof.
  exists 2. intros n Hn. destruct n as [| [| m]]; try lia.
  destruct (quarantine_value_at_fuel m) as [v [Hv _]].
  exists v. exact Hv.
Qed.

Theorem finding2_not_a_counterexample :
  sig ⊨ pc_true /\
  contains_env sig Sg · · /\
  contains sig Sg quarantine_sym quarantine_con /\
  concore_expr quarantine_con /\
  budget_total pc_true · quarantine_sym /\
  (· ⊢ᶜ quarantine_con ⇓ᶜ ELit true) /\
  (exists h, forall n, (h <= n)%nat ->
     exists v_sym, eval (Fin n) pc_true · quarantine_sym v_sym /\
                   contains sig Sg v_sym (ELit true)).
Proof.
  refine (conj sig_models_pc_true (conj quarantine_env (conj quarantine_contains
          (conj quarantine_con_concore (conj quarantine_budget_total
          (conj quarantine_concrete _)))))).
  exists 2. intros n Hn. destruct n as [| [| m]]; try lia.
  apply quarantine_value_at_fuel.
Qed.

Print Assumptions finding2_not_a_counterexample.

Definition CastExprBranch {sorts : SymCoreSorts} {solver : SymCoreSolver} : Prop :=
  forall ec et ef γ, cast_expr (EIf ec et ef) γ = EIf ec (cast_expr et γ) (cast_expr ef γ).

Theorem stacking_cast_violates_cast_expr_branch : ~ @CastExprBranch model_sorts stacking_solver.
Proof.
  intros H.
  pose proof (H guard (ELit true) (ELit true) wild_cast) as E.
  vm_compute in E. discriminate E.
Qed.

Print Assumptions stacking_cast_violates_cast_expr_branch.
