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

Section BoundedDeterminism.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : ConCoreLaws}.

Definition tainted_field_var : var := "z".

Definition identity_lam : expr := ELam "y" (EVar "y").

Definition tainted_env : environment :=
  ExtendEnv tainted_field_var (MkClosure · (EBot BOutOfFuel)) ·.

Definition tainted_closure : expr := EThunk tainted_env identity_lam.

Definition spent_scrutinee (γ : coercion) (l : lit) : expr :=
  ECast (EThunk · (EThunk · (ELit l))) γ.

Definition branch_alts (l : lit) : list alt :=
  Alt "A" nil (ELit l) :: Alt "B" nil (ELit l) :: nil.

Definition tainted_body (γ : coercion) (l : lit) : expr :=
  ECase (ECast identity_lam γ) (branch_alts l).

Definition tainted_program (γ : coercion) (l : lit) : expr :=
  ECase (spent_scrutinee γ l) (Alt "D" (tainted_field_var :: nil) (tainted_body γ l) :: nil).

Definition tainted_fuel : nat := 4.

Definition CastsSpentBottomToField (γ : coercion) : Prop :=
  cast_expr (EBot BOutOfFuel) γ = EApp (ECon "D") (EBot BOutOfFuel).

Definition CastsTaintedClosureToBranch (γ : coercion) : Prop :=
  cast_expr tainted_closure γ = EIf (EVar guard_var) (ECon "A") (ECon "B").

Lemma tainted_program_concore : forall γ l, concore_expr (tainted_program γ l).
Proof. intros γ l. repeat constructor. Qed.

Lemma tainted_closure_not_concore : ~ concore_expr tainted_closure.
Proof.
  unfold tainted_closure, tainted_env. intros H. inversion H; subst.
  match goal with
  | [ Henv : concrete_env (ExtendEnv _ _ _) |- _ ] => inversion Henv; subst
  end.
  match goal with
  | [ Hbot : concore_expr (EBot BOutOfFuel) |- _ ] => exact (out_of_fuel_not_concore Hbot)
  end.
Qed.

Lemma contains_thunk_concrete_env : forall σ S es ec,
  contains σ S es ec -> forall Γc e, ec = EThunk Γc e -> concrete_env Γc.
Proof.
  intros σ S es ec H.
  induction H; intros Γ0 e0 Heq; try discriminate Heq; eauto.
  injection Heq as <- <-. eapply contains_env_concrete. eassumption.
Qed.

Lemma tainted_closure_contains_nothing : forall σ S es,
  ~ contains σ S es tainted_closure.
Proof.
  intros σ S es H.
  apply tainted_closure_not_concore.
  pose proof (contains_thunk_concrete_env σ S es tainted_closure H tainted_env identity_lam eq_refl) as Henv.
  constructor; [exact Henv | repeat constructor].
Qed.

Lemma tainted_program_value : forall γ l,
  CastsSpentBottomToField γ ->
  CastsTaintedClosureToBranch γ ->
  forall arm, eval (Fin 2) (pc_true ∧ PCVar guard_var) tainted_env (ELit l) arm ->
  eval (Fin tainted_fuel) pc_true · (tainted_program γ l)
    (EIf (EVar guard_var) arm (ELit l)).
Proof.
  intros γ l Hfield Hbranch arm Harm.
  unfold tainted_program, tainted_fuel.
  eapply Eval_Case with (es' := cast_expr (EBot BOutOfFuel) γ).
  - apply Eval_Cast. apply Eval_Thunk. apply Eval_Thunk. apply Eval_OutOfFuel.
  - rewrite Hfield. cbn.
    eapply FoldAlts_Con; [reflexivity | reflexivity |].
    cbn. unfold tainted_body.
    eapply Eval_Case with (es' := cast_expr tainted_closure γ).
    + apply Eval_Cast. apply Eval_Lam.
    + rewrite Hbranch. cbn.
      eapply FoldAlts_If; [reflexivity | |].
      * eapply FoldAlts_Con; [reflexivity | reflexivity | exact Harm].
      * eapply FoldAlts_Con; [reflexivity | reflexivity | apply Eval_Lit].
Qed.

Theorem bounded_concrete_determinism_fails : forall γ,
  CastsSpentBottomToField γ ->
  CastsTaintedClosureToBranch γ ->
  sat (pc_true ∧ PCVar guard_var) = false ->
  exists n e v1 v2,
    concore_expr e /\
    eval (Fin n) pc_true · e v1 /\
    eval (Fin n) pc_true · e v2 /\
    v1 <> v2.
Proof.
  intros γ Hfield Hbranch Hunsat. set (l := lit_true).
  exists tainted_fuel, (tainted_program γ l),
    (EIf (EVar guard_var) (ELit l) (ELit l)),
    (EIf (EVar guard_var) (EBot BUnreachable) (ELit l)).
  split; [apply tainted_program_concore |].
  split; [apply tainted_program_value; [exact Hfield | exact Hbranch | apply Eval_Lit] |].
  split; [apply tainted_program_value; [exact Hfield | exact Hbranch | apply Eval_Prune; exact Hunsat] |].
  discriminate.
Qed.

Corollary bounded_concrete_determinism_not_provable : forall γ,
  CastsSpentBottomToField γ ->
  CastsTaintedClosureToBranch γ ->
  sat (pc_true ∧ PCVar guard_var) = false ->
  ~ (forall n Γ e v1 v2,
       concrete_env Γ -> concore_expr e ->
       eval (Fin n) pc_true Γ e v1 -> eval (Fin n) pc_true Γ e v2 -> v1 = v2).
Proof.
  intros γ Hfield Hbranch Hunsat Hdet.
  destruct (bounded_concrete_determinism_fails γ Hfield Hbranch Hunsat)
    as (n & e & v1 & v2 & Hcon & H1 & H2 & Hneq).
  exact (Hneq (Hdet n · e v1 v2 CEnv_Empty Hcon H1 H2)).
Qed.

Lemma spent_field_contains_itself : forall σ S,
  contains σ S (EApp (ECon "D") (EBot BOutOfFuel)) (EApp (ECon "D") (EBot BOutOfFuel)).
Proof. intros σ S. repeat constructor. Qed.

Definition tainted_alts (γ : coercion) : list alt :=
  Alt "C" nil (tainted_program γ lit_true) :: nil.

Corollary bounded_concrete_fold_alts_determinism_not_provable : forall γ,
  CastsSpentBottomToField γ ->
  CastsTaintedClosureToBranch γ ->
  sat (pc_true ∧ PCVar guard_var) = false ->
  ~ (forall n Γ e alts r1 r2,
       concrete_env Γ -> concore_expr e -> Forall concore_alt alts ->
       fold_alts (Fin n) pc_true Γ e alts r1 ->
       fold_alts (Fin n) pc_true Γ e alts r2 -> r1 = r2).
Proof.
  intros γ Hfield Hbranch Hunsat Hdet.
  assert (Halts : Forall concore_alt (tainted_alts γ))
    by (repeat constructor).
  assert (Hneq : EIf (EVar guard_var) (ELit lit_true) (ELit lit_true) <>
                 EIf (EVar guard_var) (EBot BUnreachable) (ELit lit_true))
    by discriminate.
  apply Hneq.
  apply (Hdet tainted_fuel · (ECon "C") (tainted_alts γ)); [constructor | constructor | exact Halts | |].
  - eapply FoldAlts_Con; [reflexivity | reflexivity |].
    apply tainted_program_value; [exact Hfield | exact Hbranch | apply Eval_Lit].
  - eapply FoldAlts_Con; [reflexivity | reflexivity |].
    apply tainted_program_value; [exact Hfield | exact Hbranch | apply Eval_Prune; exact Hunsat].
Qed.

End BoundedDeterminism.

