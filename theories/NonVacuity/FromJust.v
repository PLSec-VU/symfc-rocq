From SymCoreTheory Require Export NonVacuity.SoundnessInstances.
From SymCoreTheory Require Import Completeness.Completeness.
From Stdlib Require Import Strings.String Lists.List Lia.
Import ListNotations.
Open Scope string_scope.

Definition sym_y : var := "y".
Definition maybe_var : var := "m".
Definition field_var : var := "z".

Definition just_sym_thunk : thunk := TSusp EmptyEnv (EApp (ECon "Just") (ESym sym_y)).
Definition maybe_thunk : thunk :=
  TIf (PSym sym_s) (TSusp EmptyEnv (ECon "Nothing")) just_sym_thunk.
Definition just_con_thunk (σ : valuation) : thunk :=
  TSusp EmptyEnv (EApp (ECon "Just") (ELit (σ sym_y))).

Definition from_just_error : expr := EBot (BRaise (ECon "Nothing")).
Definition from_just_alts : list alt :=
  Alt "Nothing" [] from_just_error :: Alt "Just" [field_var] (EVar field_var) :: nil.
Definition from_just : expr := ECase (EVar maybe_var) from_just_alts.
Definition negated_from_just : expr := EApp (EPrimOp PNot) from_just.

Definition maybe_env_sym : env := ExtendEnv maybe_var maybe_thunk EmptyEnv.
Definition maybe_env_con (σ : valuation) : env :=
  ExtendEnv maybe_var (just_con_thunk σ) EmptyEnv.

Definition negated_from_just_value : value :=
  VIf (PSym sym_s) (VBot (BRaise (ECon "Nothing"))) (VPrim (PApp PNot (PSym sym_y :: nil))).

Lemma negated_from_just_sym_run :
  eval Inf pc_true maybe_env_sym negated_from_just negated_from_just_value.
Proof.
  eapply eval_equal_value.
  - eapply Eval_App; [constructor; apply Prim_Partial; cbn; lia |].
    apply Apply_Prim. apply Prim_Reduce; [discriminate | reflexivity | constructor; [| constructor]].
    constructor. eapply Eval_Case.
    + eapply Eval_Var; [reflexivity |].
      eapply Force_If; [constructor; constructor | constructor; eapply Eval_App; constructor].
    + cbn. eapply Fold_If.
      * eapply Fold_Con; [reflexivity | constructor].
      * eapply Fold_Con; [reflexivity |]. eapply Eval_Var; [reflexivity | constructor; constructor].
  - reflexivity.
Qed.

Theorem from_just_budget_total : budget_total pc_true maybe_env_sym negated_from_just.
Proof. exact (budget_total_of_unlimited_run _ _ _ _ negated_from_just_sym_run). Qed.

Lemma negated_from_just_con_run : forall σ,
  maybe_env_con σ ⊢ᶜ negated_from_just ⇓ᶜ VPrim (PLit (negb (σ sym_y))).
Proof.
  intros σ.
  eapply eval_equal_value.
  - eapply Eval_App; [constructor; apply Prim_Partial; cbn; lia |].
    apply Apply_Prim. apply Prim_Reduce; [discriminate | reflexivity | constructor; [| constructor]].
    constructor. eapply Eval_Case.
    + eapply Eval_Var; [reflexivity |]. constructor. eapply Eval_App; constructor.
    + cbn. eapply Fold_Con; [reflexivity |]. eapply Eval_Var; [reflexivity | constructor; constructor].
  - reflexivity.
Qed.

Lemma maybe_env_contains : forall σ, σ sym_s = false ->
  contains_env σ maybe_env_sym (maybe_env_con σ).
Proof.
  intros σ Hs. constructor; [| constructor].
  apply Contains_TIfF; [unfold models; simpl; rewrite Hs; reflexivity |].
  repeat constructor.
Qed.

Lemma negated_from_just_contains : forall σ,
  contains_expr σ negated_from_just negated_from_just.
Proof. intros σ. repeat constructor. Qed.

Lemma negated_from_just_concore : concore_expr negated_from_just.
Proof. repeat constructor. Qed.

Lemma maybe_env_concrete : forall σ, concrete_env (maybe_env_con σ).
Proof. intros σ. repeat constructor. Qed.

Theorem from_just_complete : forall σ, σ sym_s = false ->
  exists h, forall n, h <= n ->
    exists v_s, eval (Fin n) pc_true maybe_env_sym negated_from_just v_s /\
      contains_val σ v_s (VPrim (PLit (negb (σ sym_y)))).
Proof.
  intros σ Hs.
  exact (concore_completeness_budget pc_true maybe_env_sym (maybe_env_con σ) σ
    negated_from_just negated_from_just (VPrim (PLit (negb (σ sym_y))))
    (models_pc_true σ) (maybe_env_contains σ Hs) (negated_from_just_contains σ)
    negated_from_just_concore (maybe_env_concrete σ) from_just_budget_total
    (negated_from_just_con_run σ)).
Qed.

Theorem partial_prim_is_lazy :
  eval (Fin 3) pc_true EmptyEnv (EApp (EPrimOp PAnd) ω) (VPartial PAnd [TSusp EmptyEnv ω]).
Proof.
  eapply Eval_App.
  - constructor. apply Prim_Partial. cbn. lia.
  - apply Apply_Prim. apply Prim_Partial. cbn. lia.
Qed.

Theorem missing_field_is_undefined :
  eval (Fin 3) pc_true EmptyEnv (ECase (ECon "Just") [Alt "Just" ["z"] (EVar "z")])
    (VBot BUndefined).
Proof.
  eapply Eval_Case.
  - constructor.
  - cbn. eapply Fold_Con; [reflexivity |]. eapply Eval_Var; [reflexivity | constructor; constructor].
Qed.
