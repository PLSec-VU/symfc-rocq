From SymCoreTheory Require Export NonVacuity.SelfApplication.
From Stdlib Require Import Strings.String Lists.List Lia Arith.PeanoNat Bool.Bool.
Import ListNotations.

Section ConCore.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}
  {reduce_prim_solvable_law : ReducePrimSolvable}
  {reduce_prim_saturated_law : ReducePrimSaturated}
  {reduce_prim_concore_law : ReducePrimConcore} {cast_expr_concore_law : CastExprConcore}
  {reduce_prim_scoped_law : ReducePrimScoped} {cast_expr_scoped_law : CastExprScoped}
  {models_sat_law : ModelsSat} {prim_value_and_law : PrimValueAnd}.
Context {reduce_prim_contains_law : ReducePrimContains}
  {reduce_prim_denote_law : ReducePrimDenote}
  {reduce_prim_ground_value_law : ReducePrimGroundValue}.
Context {cast_expr_contains_law : CastExprContains}.
Context {reduce_prim_ite_wellformed_law : ReducePrimIteWellformed}.
Context {subst_coerc_contains_env_law : SubstCoercContainsEnv}
  {subst_type_contains_env_law : SubstTypeContainsEnv}.
(** ========================================================================= *)
(** NonVacuity: what the statement actually says                              *)
(** ========================================================================= *)

(**
  Six facts that show the soundness theorem is not empty:

  (a) a free symbolic variable is genuinely instantiated to its value under
      the model, and the soundness theorem has real instances that use it;
  (b) a branch whose condition mentions a free symbolic variable DOES have a
      concretion;
  (c) Rule Prune does not kill every branch;
  (d) reduce_prim is not forced to be a constant function on literals, and
      the assumption that would force it is identified;
  (e) the relation is DISCRIMINATING: different literals, different
      constructors and different shapes stay unrelated, a symbolic SMT term
      has exactly one literal concretion, and a closed SMT term is related to
      nothing but itself, so non-vacuity is not bought with triviality;
  (f) a primitive that really computes a function which is neither constant
      nor the identity lives inside the axiom set, and the soundness theorem
      applies to a program that uses it.

  No new axiom is introduced by any of this. (e) and (f) use only the three
  declared in Soundness/Instance.v and Soundness/Alignment.v (prim_value, reduce_prim_denote and
  reduce_prim_ground_value), and (f) keeps its computing primitive in Section
  variables so that nothing is assumed globally.
*)

Section NonVacuity.

Definition only (x : var) : symvars := fun y => if string_dec y x then true else false.

Lemma only_self : forall x, only x x = true.
Proof. intros x. unfold only. destruct (string_dec x x); congruence. Qed.

(* ================= (a) symbolic variables are instantiated ============== *)

Corollary symvar_instantiated : forall σ x,
  contains σ (only x) (EVar x) (ELit (σ x)).
Proof. intros. apply Cont_Var_Sym. apply only_self. Qed.

Corollary symvar_instantiated_uniquely : forall σ S x ec,
  S x = true -> contains σ S (EVar x) ec -> ec = ELit (σ x).
Proof. intros. eapply contains_var_sym; eassumption. Qed.

Corollary soundness_applies_to_symvar : forall σ S x,
  σ ⊨ pc_true -> S x = true ->
  exists v_con, · ⊢ᶜ ELit (σ x) ⇓ᶜ v_con /\ contains σ S (EVar x) v_con.
Proof.
  intros σ S x Hmod Hx.
  apply (concore_soundness pc_true · · σ S (EVar x) (ELit (σ x)) (EVar x)).
  - exact Hmod.
  - apply Cont_Env_Empty.
  - apply Cont_Var_Sym. exact Hx.
  - apply Con_Lit.
  - split; [apply Scoped_Env_Empty | apply Scoped_Lit].
  - split; [apply SymScoped_Env_Empty | apply SymScoped_Var; right; exact Hx].
  - apply Eval_SymVar. reflexivity.
Qed.

Definition symprim (p : primop) (a : expr) (l : lit) : expr :=
  EApp (EApp (EPrimOp p) a) (ELit l).

Corollary soundness_on_symbolic_primop : forall σ S p x l,
  σ ⊨ pc_true -> S x = true -> primop_arity p = 2%nat ->
  exists v_con,
    eval_con · (symprim p (ELit (σ x)) l) v_con /\
    contains σ S (reduce_prim p (EVar x :: ELit l :: nil)) v_con.
Proof.
  intros σ S p x l Hmod Hx Har.
  apply (concore_soundness pc_true · · σ S
           (symprim p (EVar x) l) (symprim p (ELit (σ x)) l)
           (reduce_prim p (EVar x :: ELit l :: nil))).
  - exact Hmod.
  - apply Cont_Env_Empty.
  - apply Cont_App; [apply Cont_App; [apply Cont_PrimOp |] | apply Cont_Lit].
    apply Cont_Var_Sym. exact Hx.
  - apply Con_App; [apply Con_App; [apply Con_PrimOp | apply Con_Lit] | apply Con_Lit].
  - split; [apply Scoped_Env_Empty | repeat constructor].
  - split; [apply SymScoped_Env_Empty |].
    apply SymScoped_App; [apply SymScoped_App; [apply SymScoped_PrimOp |] | apply SymScoped_Lit].
    apply SymScoped_Var. right. exact Hx.
  - unfold symprim. eapply Eval_AppPrim.
    + reflexivity.
    + simpl. rewrite Har. reflexivity.
    + constructor; [apply Eval_SymVar; reflexivity |].
      constructor; [apply Eval_Lit | constructor].
Qed.

(* ============== (b) symbolic branches have concretions ================== *)

Definition symcond (p : primop) (x : var) (l : lit) : expr :=
  EApp (EApp (EPrimOp p) (EVar x)) (ELit l).

Lemma symcond_is_formula : forall p x l Γ,
  lookup_env Γ x = None ->
  expr_to_pc Γ (symcond p x l) = Some (PCPrim p (PCVar x :: PCLit l :: nil)).
Proof.
  intros p x l Γ Hnone. unfold symcond. simpl. rewrite Hnone. reflexivity.
Qed.

(** The condition of a symbolic branch denotes its formula precisely when the
    variable it tests is one of the symbolic variables. *)
Lemma symcond_denotes : forall S p x l,
  S x = true -> denotes S (symcond p x l) (PCPrim p (PCVar x :: PCLit l :: nil)).
Proof.
  intros S p x l Hx Γ Hfree. apply symcond_is_formula. apply Hfree. exact Hx.
Qed.

Corollary symbolic_branch_has_concretion : forall σ S p x l lt lf,
  S x = true ->
  σ ⊨ (PCPrim p (PCVar x :: PCLit l :: nil)) ->
  contains σ S (EIf (symcond p x l) (ELit lt) (ELit lf)) (ELit lt).
Proof.
  intros σ S p x l lt lf Hx Hmod.
  apply Cont_If_True; [| apply Cont_Lit].
  apply (proj2 (models_cond_denotes σ S (symcond p x l)
                  (PCPrim p (PCVar x :: PCLit l :: nil)) (symcond_denotes S p x l Hx))).
  exact Hmod.
Qed.

(** The one premise that cannot be dispensed with is non-degeneracy of the SMT
    theory: some model must satisfy some atom. *)
Corollary soundness_not_vacuous_on_symbolic_branch :
  (exists σ p x l, σ ⊨ (PCPrim p (PCVar x :: PCLit l :: nil))) ->
  ~ (forall σ S p x l et ef ec, ~ contains σ S (EIf (symcond p x l) et ef) ec).
Proof.
  intros [σ [p [x [l Hmod]]]] Hvac.
  apply (Hvac σ (only x) p x l (ELit l) (ELit l) (ELit l)).
  apply symbolic_branch_has_concretion; [apply only_self | exact Hmod].
Qed.

Corollary symbolic_branch_condition_is_judgeable : forall σ S p x l,
  S x = true ->
  (models_cond σ S (symcond p x l) <-> σ ⊨ (PCPrim p (PCVar x :: PCLit l :: nil))).
Proof.
  intros σ S p x l Hx. apply models_cond_denotes. apply symcond_denotes. exact Hx.
Qed.

(* ==================== (c) the Prune attack is dead ====================== *)

Corollary prune_attack_blocked : forall Φ σ,
  σ ⊨ Φ -> sat Φ = false -> False.
Proof.
  intros Φ σ Hmod Hunsat. apply models_sat in Hmod. congruence.
Qed.

Corollary prune_does_not_kill_branches :
  (exists Φ, sat Φ = false) ->
  forall σ S p x l lt lf,
    S x = true ->
    σ ⊨ (PCPrim p (PCVar x :: PCLit l :: nil)) ->
    contains σ S (EIf (symcond p x l) (ELit lt) (ELit lf)) (ELit lt).
Proof.
  intros _ σ S p x l lt lf Hx Hmod.
  apply symbolic_branch_has_concretion; assumption.
Qed.

(* ============ (d) reduce_prim is not forced to be constant ============== *)

Corollary contains_not_rigid_on_solvable : forall σ : valuation,
  ~ (forall S Γ es ec, Solvable Γ es -> contains σ S es ec -> es = ec).
Proof.
  intros σ Hrigid.
  specialize (Hrigid (only "x") · (EVar "x") (ELit (σ "x"))
                     (Solvable_Var · "x" eq_refl)
                     (Cont_Var_Sym σ (only "x") "x" (only_self "x"))).
  discriminate.
Qed.

(** The collapse is attributable exactly to the UNCONDITIONAL form of
    reduce_prim_solvable, which this development does not assume. *)
Corollary unconditional_solvable_forces_constancy :
  (forall Γ p args, Solvable Γ (reduce_prim p args)) ->
  forall σ S σ' S' p c l1 l2,
    models_cond σ S c ->
    models_not_cond σ' S' c ->
    reduce_prim p [ELit l1] = reduce_prim p [ELit l2].
Proof.
  intros Hall σ S σ' S' p c l1 l2 Htrue Hfalse.
  assert (H1 : reduce_prim p [EIf c (ELit l1) (ELit l2)] = reduce_prim p [ELit l1]).
  { eapply (ground_solvable_contains_eq σ S).
    - apply reduce_prim_contains; [repeat constructor | constructor; [| constructor]].
      apply Cont_If_True; [exact Htrue | apply Cont_Lit].
    - intros Γ. apply Hall. }
  assert (H2 : reduce_prim p [EIf c (ELit l1) (ELit l2)] = reduce_prim p [ELit l2]).
  { eapply (ground_solvable_contains_eq σ' S').
    - apply reduce_prim_contains; [repeat constructor | constructor; [| constructor]].
      apply Cont_If_False; [exact Hfalse | apply Cont_Lit].
    - intros Γ. apply Hall. }
  rewrite <- H1, H2. reflexivity.
Qed.

Section ReducePrimNotConstant.
  Variable p : primop.
  Variables l1 l2 : lit.
  Hypothesis Hdistinct : reduce_prim p [ELit l1] <> reduce_prim p [ELit l2].

  Corollary distinct_images_survive_resolvable_conditions :
    forall σ S c,
      models_cond σ S c ->
      contains σ S (reduce_prim p [EIf c (ELit l1) (ELit l2)]) (reduce_prim p [ELit l1]).
  Proof.
    intros σ S c Hc. apply reduce_prim_contains; [repeat constructor | constructor; [| constructor]].
    apply Cont_If_True; [exact Hc | apply Cont_Lit].
  Qed.

  (** models_cond is a definition, not an abstract judgement, so a caller
      discharges the branch premise from a model of the condition's own
      formula and nothing else. *)
  Corollary distinct_images_survive_symbolic_conditions :
    forall σ q x l,
      σ ⊨ (PCPrim q (PCVar x :: PCLit l :: nil)) ->
      contains σ (only x)
        (reduce_prim p [EIf (symcond q x l) (ELit l1) (ELit l2)])
        (reduce_prim p [ELit l1]).
  Proof.
    intros σ q x l Hmod.
    apply distinct_images_survive_resolvable_conditions.
    apply (proj2 (symbolic_branch_condition_is_judgeable σ (only x) q x l (only_self x))).
    exact Hmod.
  Qed.

  Corollary old_axiom_refutes_distinct_images :
    (forall Γ q args, Solvable Γ (reduce_prim q args)) ->
    forall σ S σ' S' c, models_cond σ S c -> models_not_cond σ' S' c -> False.
  Proof.
    intros Hall σ S σ' S' c Ht Hf. apply Hdistinct.
    eapply unconditional_solvable_forces_constancy; eassumption.
  Qed.
End ReducePrimNotConstant.

(* ============ (e) the relation is still discriminating ================= *)

(**
  The mirror-image failure of vacuity is triviality. A relation that held of
  every pair would make the soundness theorem say nothing, exactly as a
  relation that holds of no pair does. The facts below stop that.
*)

(** Two different literals are NOT related. *)
Corollary distinct_literals_not_contained : forall σ S l1 l2,
  l1 <> l2 -> ~ contains σ S (ELit l1) (ELit l2).
Proof.
  intros σ S l1 l2 Hne Hcont.
  apply contains_lit_inv in Hcont. injection Hcont as Hcont. congruence.
Qed.

(** Two different data constructors are NOT related. *)
Corollary distinct_constructors_not_contained : forall σ S d1 d2,
  d1 <> d2 -> ~ contains σ S (ECon d1) (ECon d2).
Proof.
  intros σ S d1 d2 Hne Hcont.
  apply contains_con_inv in Hcont. injection Hcont as Hcont. congruence.
Qed.

(** Shapes are not mixed. A function, a constructor and a bottom are none of
    them concretised by a literal, and a literal is not concretised by a
    function. *)
Corollary lambda_not_contained_by_literal : forall σ S x body l,
  ~ contains σ S (ELam x body) (ELit l).
Proof.
  intros σ S x body l Hcont.
  apply contains_lam_inv in Hcont as [bodyc [Heq _]]. discriminate.
Qed.

Corollary constructor_not_contained_by_literal : forall σ S d l,
  ~ contains σ S (ECon d) (ELit l).
Proof.
  intros σ S d l Hcont. apply contains_con_inv in Hcont. discriminate.
Qed.

Corollary bottom_not_contained_by_literal : forall σ S b l,
  ~ contains σ S (EBot b) (ELit l).
Proof.
  intros σ S b l Hcont. inversion Hcont; subst; kill_denote.
Qed.

Corollary literal_not_contained_by_lambda : forall σ S l x body,
  ~ contains σ S (ELit l) (ELam x body).
Proof.
  intros σ S l x body Hcont. apply contains_lit_inv in Hcont. discriminate.
Qed.

(** Cont_Denote relates a symbolic SMT term to ONE literal, the one it
    denotes: `contains` is a function on the SMT fragment. *)
Corollary smt_concretion_determined : forall σ S es l1 l2,
  denote σ S es l1 -> contains σ S es (ELit l2) -> l1 = l2.
Proof.
  intros σ S es l1 l2 Hden Hcont.
  inversion Hcont; subst.
  - destruct (denote_var_inv σ S x l1 Hden) as [_ Hl1]. congruence.
  - symmetry. exact (denote_lit_inv σ S l2 l1 Hden).
  - discriminate.
  - destruct Hden as [pc [Hd _]].
    specialize (Hd · (sym_free_env_empty S)). simpl in Hd. discriminate.
  - destruct Hden as [pc [Hd _]].
    specialize (Hd · (sym_free_env_empty S)). simpl in Hd. discriminate.
  - match goal with
    | [ Hden2 : denote σ S es l2 |- _ ] =>
        exact (denote_functional σ S es l1 l2 Hden Hden2)
    end.
Qed.

Corollary wrong_value_not_contained : forall σ S es l1 l2,
  denote σ S es l1 -> l1 <> l2 -> ~ contains σ S es (ELit l2).
Proof.
  intros σ S es l1 l2 Hden Hne Hcont.
  exact (Hne (smt_concretion_determined σ S es l1 l2 Hden Hcont)).
Qed.

(* ======= (f) a primitive that computes, and soundness applied to it ===== *)

(**
  Everything below is hypothetical in the Section's variables, so it adds no
  assumption to the development. It shows that a reducer which really computes
  a function that is NEITHER constant NOR the identity sits inside the axiom
  set instead of contradicting it.

  The load-bearing step is computing_primitive_concretion: the concretion is
  derived from Cont_Denote, without appealing to reduce_prim_contains at all.
*)
Section ComputingPrimitive.
  Variable psucc : primop.
  Variable succ : lit -> lit.

  Hypothesis Hsucc_arity : primop_arity psucc = 1%nat.
  Hypothesis Hsucc_value : forall l, prim_value psucc [l] = succ l.
  Hypothesis Hsucc_computes : forall l, reduce_prim psucc [ELit l] = ELit (succ l).
  Hypothesis Hsucc_residual : forall x,
    reduce_prim psucc [EVar x] = EApp (EPrimOp psucc) (EVar x).

  Variables lc1 lc2 lid : lit.
  Hypothesis Hsucc_not_constant : succ lc1 <> succ lc2.
  Hypothesis Hsucc_not_identity : succ lid <> lid.

  Definition symsucc (x : var) : expr := EApp (EPrimOp psucc) (EVar x).

  Lemma symsucc_denotes : forall σ x,
    denote σ (only x) (symsucc x) (succ (σ x)).
  Proof.
    intros σ x. exists (PCPrim psucc [PCVar x]). split.
    - intros Γ Hfree. unfold symsucc. simpl.
      rewrite (Hfree x (only_self x)). reflexivity.
    - simpl. apply Hsucc_value.
  Qed.

  (** The concretion, as a theorem about `contains` rather than an
      assumption. *)
  Corollary computing_primitive_concretion : forall σ x,
    contains σ (only x) (reduce_prim psucc [EVar x])
                        (reduce_prim psucc [ELit (σ x)]).
  Proof.
    intros σ x. rewrite Hsucc_residual, Hsucc_computes.
    apply (Cont_Denote σ (only x) (symsucc x) psucc [EVar x] (succ (σ x))).
    - reflexivity.
    - simpl. rewrite Hsucc_arity. reflexivity.
    - reflexivity.
    - apply symsucc_denotes.
  Qed.

  (** The symbolic run leaves a residual application; the concrete run
      computes. *)
  Lemma symsucc_symbolic_run : forall x,
    pc_true ; · ⊢ symsucc x ⇓ EApp (EPrimOp psucc) (EVar x).
  Proof.
    intros x. rewrite <- Hsucc_residual. unfold symsucc.
    eapply Eval_AppPrim.
    - reflexivity.
    - simpl. rewrite Hsucc_arity. reflexivity.
    - constructor; [apply Eval_SymVar; reflexivity | constructor].
  Qed.

  Lemma symsucc_concrete_run : forall l,
    · ⊢ᶜ EApp (EPrimOp psucc) (ELit l) ⇓ᶜ ELit (succ l).
  Proof.
    intros l. unfold eval_con. rewrite <- Hsucc_computes.
    eapply Eval_AppPrim.
    - reflexivity.
    - simpl. rewrite Hsucc_arity. reflexivity.
    - constructor; [apply Eval_Lit | constructor].
  Qed.

  (** Soundness applies to a whole program that uses the computing
      primitive on a symbolic input. *)
  Corollary soundness_on_computing_primitive : forall σ x,
    σ ⊨ pc_true ->
    exists v_con,
      · ⊢ᶜ EApp (EPrimOp psucc) (ELit (σ x)) ⇓ᶜ v_con /\
      contains σ (only x) (reduce_prim psucc [EVar x]) v_con.
  Proof.
    intros σ x Hmod.
    apply (concore_soundness pc_true · · σ (only x)
             (symsucc x) (EApp (EPrimOp psucc) (ELit (σ x)))
             (reduce_prim psucc [EVar x])).
    - exact Hmod.
    - apply Cont_Env_Empty.
    - apply Cont_App; [apply Cont_PrimOp | apply Cont_Var_Sym; apply only_self].
    - apply Con_App; [apply Con_PrimOp | apply Con_Lit].
    - split; [apply Scoped_Env_Empty | repeat constructor].
    - split; [apply SymScoped_Env_Empty |].
      apply SymScoped_App; [apply SymScoped_PrimOp |].
      apply SymScoped_Var. right. apply only_self.
    - rewrite Hsucc_residual. apply symsucc_symbolic_run.
  Qed.

  (** And the value it is related to is the computed one, not some frozen
      term: reduce_prim psucc [EVar x] is related to ELit (succ (σ x)). *)
  Corollary computing_primitive_value : forall σ x,
    contains σ (only x) (reduce_prim psucc [EVar x]) (ELit (succ (σ x))).
  Proof.
    intros σ x. rewrite <- Hsucc_computes.
    exact (computing_primitive_concretion σ x).
  Qed.

  (** succ is neither constant nor the identity. *)
  Corollary computing_primitive_refutes_old_verdict :
    ~ ((exists l0, forall l, succ l = l0) \/ (forall l, succ l = l)).
  Proof.
    intros [[l0 Hconst] | Hid].
    - apply Hsucc_not_constant. rewrite (Hconst lc1), (Hconst lc2). reflexivity.
    - apply Hsucc_not_identity. apply Hid.
  Qed.
End ComputingPrimitive.

(* ================ (g) a model takes an else-branch ====================== *)

Section ElseBranch.
  Variable l_else : lit.
  Hypothesis negation_holds : prim_value op_not (l_else :: nil) = lit_true.

  Definition else_model : valuation := fun _ => l_else.
  Definition branch_var : var := "x".
  Definition branch_on_x (et ef : expr) : expr := EIf (EVar branch_var) et ef.

  Lemma else_model_refutes_x : models_not_cond else_model (only branch_var) (EVar branch_var).
  Proof.
    exists (PCVar branch_var). split; [| exact negation_holds].
    intros Γ Hfree. simpl. rewrite (Hfree branch_var (only_self branch_var)). reflexivity.
  Qed.

  Corollary else_branch_instance : forall lt lf,
    contains else_model (only branch_var) (branch_on_x (ELit lt) (ELit lf)) (ELit lf).
  Proof. intros lt lf. apply Cont_If_False; [exact else_model_refutes_x | apply Cont_Lit]. Qed.

  Definition truth_alts (lt lf : lit) : list alt :=
    Alt "T" nil (ELit lt) :: Alt "F" nil (ELit lf) :: nil.
  Definition symbolic_match (lt lf : lit) : expr :=
    ECase (branch_on_x (ECon "T") (ECon "F")) (truth_alts lt lf).
  Definition else_match (lt lf : lit) : expr := ECase (ECon "F") (truth_alts lt lf).

  Lemma symbolic_match_runs : forall Φ lt lf,
    Φ ; · ⊢ symbolic_match lt lf ⇓ branch_on_x (ELit lt) (ELit lf).
  Proof.
    intros Φ lt lf. unfold symbolic_match, branch_on_x.
    eapply Eval_Case.
    - eapply Eval_If with (pc_c := PCVar branch_var);
        [apply Eval_SymVar; reflexivity | reflexivity
        | apply eval_nullary_con | apply eval_nullary_con].
    - simpl. eapply FoldAlts_If; [reflexivity | |];
        (eapply FoldAlts_Con; [reflexivity | reflexivity | apply Eval_Lit]).
  Qed.

  Lemma symbolic_match_contains_else_match : forall lt lf,
    contains else_model (only branch_var) (symbolic_match lt lf) (else_match lt lf).
  Proof.
    intros lt lf. apply Cont_Case.
    - apply Cont_If_False; [exact else_model_refutes_x | apply Cont_Con].
    - repeat constructor.
  Qed.

  Lemma else_match_concore : forall lt lf, concore_expr (else_match lt lf).
  Proof. intros lt lf. repeat constructor. Qed.

  Lemma else_model_satisfies_negated_guard : else_model ⊨ (¬ PCVar branch_var).
  Proof. exact negation_holds. Qed.

  Corollary soundness_takes_else_branch : forall lt lf,
    exists v_con,
      · ⊢ᶜ else_match lt lf ⇓ᶜ v_con /\
      contains else_model (only branch_var) (branch_on_x (ELit lt) (ELit lf)) v_con.
  Proof.
    intros lt lf.
    apply (concore_soundness (¬ PCVar branch_var) · · else_model (only branch_var)
             (symbolic_match lt lf) (else_match lt lf)).
    - exact else_model_satisfies_negated_guard.
    - apply Cont_Env_Empty.
    - apply symbolic_match_contains_else_match.
    - apply else_match_concore.
    - split; [apply Scoped_Env_Empty | repeat constructor].
    - split; [apply SymScoped_Env_Empty |].
      apply SymScoped_Case; [| repeat constructor].
      apply SymScoped_If; [| apply SymScoped_Con | apply SymScoped_Con].
      apply SymScoped_Var. right. apply only_self.
    - apply symbolic_match_runs.
  Qed.

  Lemma else_match_reads_else_arm : forall lt lf, · ⊢ᶜ else_match lt lf ⇓ᶜ ELit lf.
  Proof.
    intros lt lf. unfold eval_con, else_match.
    eapply Eval_Case; [apply eval_nullary_con |].
    simpl. eapply FoldAlts_Con; [reflexivity | reflexivity | apply Eval_Lit].
  Qed.
End ElseBranch.

End NonVacuity.
End ConCore.

(** ========================================================================= *)
(** What the model shows                                                      *)
(** ========================================================================= *)

Theorem model_negation_is_satisfiable : prim_value op_not (false :: nil) = lit_true.
Proof. reflexivity. Qed.

Corollary some_literal_satisfies_negation :
  ~ (forall l : lit, prim_value op_not (l :: nil) <> lit_true).
Proof. intros H. exact (H false model_negation_is_satisfiable). Qed.

Theorem model_soundness_takes_else_branch :
  exists v_con,
    ⊢ᶜ else_match true false ⇓ᶜ v_con /\
    contains (else_model false) (only branch_var) (branch_on_x (ELit true) (ELit false)) v_con.
Proof. exact (soundness_takes_else_branch false model_negation_is_satisfiable true false). Qed.

Corollary model_else_branch_value : forall v,
  ⊢ᶜ else_match true false ⇓ᶜ v -> v = ELit false.
Proof.
  intros v Hv.
  exact (concore_eval_deterministic_top _ _ _ (else_match_concore true false)
           ltac:(repeat constructor) Hv (else_match_reads_else_arm true false)).
Qed.

Theorem model_soundness_on_negation : forall σ x,
  σ ⊨ pc_true ->
  exists v_con,
    ⊢ᶜ EApp (EPrimOp PNot) (ELit (σ x)) ⇓ᶜ v_con /\
    contains σ (only x) (reduce_prim PNot (EVar x :: nil)) v_con.
Proof.
  exact (soundness_on_computing_primitive PNot eq_refl (fun x => eq_refl)).
Qed.

