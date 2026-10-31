From SymCoreTheory Require Export NonVacuity.SoundnessInstances.
From SymCoreTheory Require Import ConCore.Determinism Completeness.Completeness.
From Stdlib Require Import Strings.String Lists.List Lia.
Import ListNotations.
Open Scope string_scope.

Definition sym_s1 : var := "s1".
Definition sym_s2 : var := "s2".

Definition and_expr (a b : expr) : expr := EApp (EApp (EPrimOp PAnd) a) b.
Definition yes_thunk : thunk := TSusp EmptyEnv (ECon "Yes").
Definition no_thunk : thunk := TSusp EmptyEnv (ECon "No").

Definition branch_sym : expr := ite_expr (and_expr (ESym sym_s1) (ESym sym_s2)) (ECon "Yes") (ECon "No").
Definition branch_con (σ : valuation) : expr :=
  ite_expr (and_expr (ELit (σ sym_s1)) (ELit (σ sym_s2))) (ECon "Yes") (ECon "No").

Definition runtime_guard : prim := PApp PAnd (PSym sym_s1 :: PSym sym_s2 :: nil).
Definition runtime_branch_value : value := VIf runtime_guard (VCon "Yes" []) (VCon "No" []).

Ltac run_and_spine :=
  eapply Eval_App;
  [ eapply Eval_App;
    [ constructor; apply Prim_Partial; cbn; lia
    | apply Apply_Prim; apply Prim_Partial; cbn; lia ]
  | apply Apply_Prim; apply Prim_Reduce;
    [ discriminate | reflexivity
    | constructor; [constructor; constructor | constructor; [constructor; constructor | constructor]] ] ].

Lemma runtime_guard_selects_symbolically :
  select Inf pc_true (VPrim runtime_guard) yes_thunk no_thunk
    (ite runtime_guard (VCon "Yes" []) (VCon "No" [])).
Proof.
  eapply Select_Sym; [reflexivity | constructor; constructor | constructor; constructor].
Qed.

Lemma branch_sym_run : eval Inf pc_true EmptyEnv branch_sym runtime_branch_value.
Proof.
  eapply eval_equal_value; [unfold branch_sym, ite_expr, and_expr; run_ite_spine |].
  - constructor. run_and_spine.
  - exact runtime_guard_selects_symbolically.
  - reflexivity.
Qed.

Lemma branch_contains : forall σ, contains_expr σ branch_sym (branch_con σ).
Proof. intros σ. repeat constructor. Qed.

Lemma branch_concore : forall σ, concore_expr (branch_con σ).
Proof. intros σ. repeat constructor. Qed.

Section TrueThenFalse.
Variable σ : valuation.
Hypothesis first_true : σ sym_s1 = true.
Hypothesis second_false : σ sym_s2 = false.

Lemma branch_con_run : EmptyEnv ⊢ᶜ branch_con σ ⇓ᶜ VCon "No" [].
Proof.
  unfold branch_con, ite_expr, and_expr. rewrite first_true, second_false. run_ite_spine.
  - constructor. run_and_spine.
  - cbn. apply Select_False; [discriminate | constructor; constructor].
Qed.

Lemma runtime_branch_contains_no : contains_val σ runtime_branch_value (VCon "No" []).
Proof.
  apply Contains_VIfF; [| repeat constructor].
  unfold models. simpl. rewrite first_true, second_false. reflexivity.
Qed.

Theorem runtime_branch_soundness :
  exists v_c, EmptyEnv ⊢ᶜ branch_con σ ⇓ᶜ v_c /\
    contains_val σ runtime_branch_value v_c /\ v_c = VCon "No" [].
Proof.
  destruct (concore_soundness pc_true EmptyEnv EmptyEnv σ branch_sym (branch_con σ)
    runtime_branch_value) as [v_c [Hrun Hrel]];
    [apply models_pc_true | constructor | apply branch_contains | apply branch_concore
    | constructor | exact branch_sym_run |].
  exists v_c. split; [exact Hrun | split; [exact Hrel |]].
  eapply concore_eval_deterministic;
    [constructor | apply branch_concore | exact Hrun | exact branch_con_run].
Qed.

Theorem runtime_branch_completeness :
  exists h, forall n, h <= n ->
    exists v_s, eval (Fin n) pc_true EmptyEnv branch_sym v_s /\
      contains_val σ v_s (VCon "No" []).
Proof.
  exact (concore_completeness_budget pc_true EmptyEnv EmptyEnv σ branch_sym (branch_con σ)
    (VCon "No" []) (models_pc_true σ) (Contains_Empty σ) (branch_contains σ)
    (branch_concore σ) Concrete_Empty
    (budget_total_of_unlimited_run _ _ _ _ branch_sym_run) branch_con_run).
Qed.

End TrueThenFalse.

