From SymCoreTheory Require Export Model.Model NonVacuity.SelfApplication.
From SymCoreTheory Require Import ConCore.Determinism.
From Stdlib Require Import Strings.String Lists.List Lia.
Import ListNotations.
Open Scope string_scope.

Definition sym_s : var := "s".
Definition branch_var : var := "b".

Theorem soundness_on_symbol : forall σ,
  exists v_c, EmptyEnv ⊢ᶜ ELit (σ sym_s) ⇓ᶜ v_c /\
    contains_val σ (VPrim (PSym sym_s)) v_c /\ v_c = VPrim (PLit (σ sym_s)).
Proof.
  intros σ.
  destruct (concore_soundness pc_true EmptyEnv EmptyEnv σ (ESym sym_s) (ELit (σ sym_s))
    (VPrim (PSym sym_s))) as [v_c [Hrun Hrel]];
    [apply models_pc_true | constructor | apply Contains_ESymLit | constructor
    | constructor | constructor |].
  exists v_c. split; [exact Hrun | split; [exact Hrel |]].
  eapply concore_eval_deterministic; [constructor | constructor | exact Hrun | constructor].
Qed.

Definition branch_thunk : thunk :=
  TIf (PSym sym_s) (TSusp EmptyEnv (ELit true)) (TSusp EmptyEnv (ELit false)).
Definition branch_env_sym : env := ExtendEnv branch_var branch_thunk EmptyEnv.
Definition branch_env_con (σ : valuation) : env :=
  ExtendEnv branch_var (TSusp EmptyEnv (ELit (σ sym_s))) EmptyEnv.
Definition branch_value : value := VPrim (PApp PIte (PSym sym_s :: PLit true :: PLit false :: nil)).

Lemma branch_env_contains : forall σ, contains_env σ branch_env_sym (branch_env_con σ).
Proof.
  intros σ. unfold branch_env_sym, branch_env_con, branch_thunk.
  constructor; [| constructor].
  destruct (σ sym_s) eqn:Hs.
  - apply Contains_TIfT; [exact Hs |]. repeat constructor.
  - apply Contains_TIfF; [unfold models; simpl; rewrite Hs; reflexivity |]. repeat constructor.
Qed.

Lemma branch_env_concrete : forall σ, concrete_env (branch_env_con σ).
Proof. intros σ. repeat constructor. Qed.

Lemma branch_symbolic_run : eval Inf pc_true branch_env_sym (EVar branch_var) branch_value.
Proof.
  eapply eval_equal_value.
  - eapply Eval_Var; [reflexivity |]. constructor; repeat constructor.
  - reflexivity.
Qed.

Theorem soundness_on_branch_binding : forall σ,
  exists v_c, branch_env_con σ ⊢ᶜ EVar branch_var ⇓ᶜ v_c /\
    contains_val σ branch_value v_c /\ v_c = VPrim (PLit (σ sym_s)).
Proof.
  intros σ.
  destruct (concore_soundness pc_true branch_env_sym (branch_env_con σ) σ
    (EVar branch_var) (EVar branch_var) branch_value) as [v_c [Hrun Hrel]];
    [apply models_pc_true | apply branch_env_contains | constructor | constructor
    | apply branch_env_concrete | exact branch_symbolic_run |].
  exists v_c. split; [exact Hrun | split; [exact Hrel |]].
  eapply concore_eval_deterministic;
    [apply branch_env_concrete | constructor | exact Hrun |].
  eapply Eval_Var; [reflexivity |]. repeat constructor.
Qed.

Definition not_sym : expr := EApp (EPrimOp PNot) (ESym sym_s).
Definition not_con (σ : valuation) : expr := EApp (EPrimOp PNot) (ELit (σ sym_s)).
Definition not_sym_value : value := VPrim (PApp PNot [PSym sym_s]).

Lemma not_sym_run : eval Inf pc_true EmptyEnv not_sym not_sym_value.
Proof.
  eapply eval_equal_value.
  - eapply Eval_App.
    + constructor. apply Prim_Partial. cbn. lia.
    + apply Apply_Prim. apply Prim_Reduce.
      * discriminate.
      * reflexivity.
      * (constructor; [constructor; constructor | constructor]).
  - reflexivity.
Qed.

Lemma not_con_run : forall σ,
  eval Inf pc_true EmptyEnv (not_con σ) (VPrim (PLit (negb (σ sym_s)))).
Proof.
  intros σ. eapply eval_equal_value.
  - eapply Eval_App.
    + constructor. apply Prim_Partial. cbn. lia.
    + apply Apply_Prim. apply Prim_Reduce;
        [discriminate | reflexivity | constructor; [constructor; constructor | constructor]].
  - reflexivity.
Qed.

Lemma not_contains : forall σ, contains_expr σ not_sym (not_con σ).
Proof. intros σ. repeat constructor. Qed.
Lemma not_concore : forall σ, concore_expr (not_con σ).
Proof. intros σ. repeat constructor. Qed.

Theorem soundness_on_computing_primitive : forall σ,
  exists v_c, EmptyEnv ⊢ᶜ not_con σ ⇓ᶜ v_c /\
    contains_val σ not_sym_value v_c /\ v_c = VPrim (PLit (negb (σ sym_s))).
Proof.
  intros σ.
  destruct (concore_soundness pc_true EmptyEnv EmptyEnv σ not_sym (not_con σ) not_sym_value)
    as [v_c [Hrun Hrel]];
    [apply models_pc_true | constructor | apply not_contains | apply not_concore
    | constructor | exact not_sym_run |].
  exists v_c. split; [exact Hrun | split; [exact Hrel |]].
  eapply concore_eval_deterministic;
    [constructor | apply not_concore | exact Hrun | apply not_con_run].
Qed.

Theorem instances_distinguish : forall σ,
  ~ contains_val σ (VPrim (PLit true)) (VPrim (PLit false)).
Proof.
  intros σ H. inversion H as [ps pc Hp | | | | | | | | |]; subst. inversion Hp.
Qed.
