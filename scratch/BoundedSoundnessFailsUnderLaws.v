From SymCoreTheory Require Import SymCore ConCore CostLaws Completeness Model.
From Stdlib Require Import Strings.String Lists.List Lia.
Import ListNotations.
Open Scope string_scope.

Fixpoint bot_cast (e : @expr model_sorts) : @expr model_sorts :=
  match e with
  | EBot BOutOfFuel => ELit true
  | EIf c t f => EIf c (bot_cast t) (bot_cast f)
  | _ => e
  end.

Definition bot_cast_expr (e : @expr model_sorts) (γ : coercion) : @expr model_sorts := bot_cast e.

Definition bot_solver : @SymCoreSolver model_sorts :=
  Build_SymCoreSolver
    model_sat (PCLit true) eq_refl model_reduce_prim
    bot_cast_expr keep_coercion keep_type.

Lemma bot_cast_concore : forall e, @concore_expr model_sorts e -> bot_cast e = e.
Proof.
  intros e H. destruct e; try reflexivity.
  - inversion H.
  - destruct b; try reflexivity. inversion H.
Qed.

Fixpoint bot_cast_scoped (e : @expr model_sorts) {struct e} :
  forall L, scoped L e -> scoped L (bot_cast e).
Proof.
  intros L H. destruct e; simpl; try exact H.
  - inversion H; subst. apply Scoped_If; [assumption | apply bot_cast_scoped; assumption | apply bot_cast_scoped; assumption].
  - destruct b; try exact H. apply Scoped_Lit.
Qed.

Fixpoint bot_cast_contains_k (es : @expr model_sorts) {struct es} :
  forall σ S k ec, contains_k σ S k es ec -> contains_k σ S k (bot_cast es) (bot_cast ec).
Proof.
  intros σ S k ec H. destruct es; simpl.
  - pose proof H as H0. inversion H0; subst; simpl; exact H.
  - pose proof H as H0. inversion H0; subst; simpl; exact H.
  - pose proof H as H0. inversion H0; subst; simpl; exact H.
  - pose proof H as H0. inversion H0; subst; simpl; exact H.
  - pose proof H as H0. inversion H0; subst; simpl; exact H.
  - pose proof H as H0. inversion H0; subst; simpl; exact H.
  - pose proof H as H0. inversion H0; subst; simpl; exact H.
  - pose proof H as H0. inversion H0; subst; simpl; exact H.
  - pose proof H as H0. inversion H0; subst; simpl; exact H.
  - pose proof H as H0. inversion H0; subst; simpl; exact H.
  - inversion H; subst.
    + apply ContK_If_True; [assumption | apply bot_cast_contains_k; assumption].
    + apply ContK_If_False; [assumption | apply bot_cast_contains_k; assumption].
    + match goal with [ Hu : unspool_app (EIf _ _ _) _ = _ |- _ ] => discriminate Hu end.
  - pose proof H as H0. inversion H0; subst; simpl.
    + destruct b; simpl; try exact H. apply ContK_Lit.
    + match goal with [ Hu : unspool_app (EBot _) _ = _ |- _ ] => discriminate Hu end.
  - pose proof H as H0. inversion H0; subst; simpl.
    + exact H.
    + destruct ec; try discriminate; simpl; exact H.
    + match goal with [ Hu : unspool_app (EThunk _ _) _ = _ |- _ ] => discriminate Hu end.
Qed.

Fixpoint bot_cast_contains (es : @expr model_sorts) {struct es} :
  forall σ S ec, contains σ S es ec -> contains σ S (bot_cast es) (bot_cast ec).
Proof.
  intros σ S ec H. destruct es; simpl.
  - pose proof H as H0. inversion H0; subst; simpl; exact H.
  - pose proof H as H0. inversion H0; subst; simpl; exact H.
  - pose proof H as H0. inversion H0; subst; simpl; exact H.
  - pose proof H as H0. inversion H0; subst; simpl; exact H.
  - pose proof H as H0. inversion H0; subst; simpl; exact H.
  - pose proof H as H0. inversion H0; subst; simpl; exact H.
  - pose proof H as H0. inversion H0; subst; simpl; exact H.
  - pose proof H as H0. inversion H0; subst; simpl; exact H.
  - pose proof H as H0. inversion H0; subst; simpl; exact H.
  - pose proof H as H0. inversion H0; subst; simpl; exact H.
  - inversion H; subst.
    + apply Cont_If_True; [assumption | apply bot_cast_contains; assumption].
    + apply Cont_If_False; [assumption | apply bot_cast_contains; assumption].
    + match goal with [ Hu : unspool_app (EIf _ _ _) _ = _ |- _ ] => discriminate Hu end.
  - pose proof H as H0. inversion H0; subst; simpl.
    + destruct b; simpl; try exact H. apply Cont_Lit.
    + match goal with [ Hu : unspool_app (EBot _) _ = _ |- _ ] => discriminate Hu end.
  - pose proof H as H0. inversion H0; subst; simpl.
    + exact H.
    + destruct ec; try discriminate; simpl; exact H.
    + match goal with [ Hu : unspool_app (EThunk _ _) _ = _ |- _ ] => discriminate Hu end.
Qed.

Definition bot_cost_laws : @SymFCCostLaws model_sorts bot_solver.
Proof.
  constructor; [constructor | |].
  - exact model_reduce_prim_solvable.
  - exact model_reduce_prim_saturated.
  - exact model_reduce_prim_concore.
  - intros e γ H. unfold cast_expr; simpl; unfold bot_cast_expr. rewrite (bot_cast_concore e H). exact H.
  - exact model_reduce_prim_scoped.
  - intros e γ H. exact (bot_cast_scoped e nil H).
  - exact model_models_sat.
  - exact model_prim_value_and.
  - exact model_reduce_prim_contains.
  - exact model_reduce_prim_denote.
  - exact model_reduce_prim_ground_value.
  - intros σ S es ec γ H. exact (bot_cast_contains es σ S ec H).
  - exact model_subst_coerc_contains_env.
  - exact model_subst_type_contains_env.
  - intros σ S k es ec γ H. exact (bot_cast_contains_k es σ S k ec H).
  - exact model_reduce_prim_contains_k.
Qed.

Definition BoundedSoundnessForLiterals {sorts : SymCoreSorts} {solver : SymCoreSolver} : Prop :=
  forall n Φ Γs Γc σ S e_s e_c l,
    σ ⊨ Φ ->
    contains_env σ S Γs Γc ->
    contains σ S e_s e_c ->
    concore_expr e_c ->
    closed_program Γc e_c ->
    eval (Fin n) Φ Γs e_s (ELit l) ->
    exists v_c, Γc ⊢ᶜ e_c ⇓ᶜ v_c /\ contains σ S (ELit l) v_c.

Definition some_coercion : coercion := MkCoercion (TyCon tt) (TyCon tt) RoleRepresentational.
Definition cast_loop : @expr model_sorts := ECast self_app some_coercion.

Theorem lawful_solver_breaks_bounded_soundness :
  @SymFCCostLaws model_sorts bot_solver /\ ~ @BoundedSoundnessForLiterals model_sorts bot_solver.
Proof.
  split; [exact bot_cost_laws |].
  intros Hbs.
  assert (Hrun : @eval model_sorts bot_solver (Fin 2) (PCLit true) · cast_loop (ELit true)).
  { unfold cast_loop.
    change (@ELit model_sorts true) with (@cast_expr model_sorts bot_solver (EBot BOutOfFuel) some_coercion).
    apply (@Eval_Cast model_sorts bot_solver (Remaining 1)).
    eapply (@Eval_AppSpine model_sorts bot_solver (Remaining 0)).
    - apply self_app_fun_comp.
    - apply Eval_OutOfFuel.
    - apply Eval_OutOfFuel. }
  assert (Hcont : @contains model_sorts (fun _ => false) (fun _ => false) cast_loop cast_loop).
  { unfold cast_loop, self_app, self_app_fun, self_app_body, self_app_var.
    repeat (first [apply Cont_Cast | apply Cont_App | apply Cont_Lam; [reflexivity|] | apply Cont_Var_Bound; reflexivity]). }
  assert (Hcl : closed_program · cast_loop).
  { unfold cast_loop, self_app, self_app_fun, self_app_body, self_app_var.
    split; [apply Scoped_Env_Empty |]. simpl.
    repeat (first [apply Scoped_Cast | apply Scoped_App | apply Scoped_Lam | apply Scoped_Var; simpl; auto]). }
  assert (Hcon : concore_expr cast_loop) by (repeat constructor).
  unfold BoundedSoundnessForLiterals in Hbs.
  destruct (Hbs 2 (@PCLit model_sorts true) · · (fun _ => false) (fun _ => false) cast_loop cast_loop _
              eq_refl (Cont_Env_Empty _ _) Hcont Hcon Hcl Hrun) as [v [Hv _]].
  unfold eval_con, cast_loop in Hv.
  inversion Hv; subst;
    try match goal with [ Hu : unspool_app _ _ = _ |- _ ] => discriminate Hu end;
    try match goal with [ Hs : sat _ = false |- _ ] => discriminate Hs end.
  all: match goal with
  | [ Hl : eval _ _ _ _ _ |- _ ] => exact (@self_app_diverges model_sorts bot_solver _ _ _ eq_refl Hl)
  end.
Qed.


Print Assumptions lawful_solver_breaks_bounded_soundness.
