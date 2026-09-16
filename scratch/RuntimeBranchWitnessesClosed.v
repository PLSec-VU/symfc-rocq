From SymCoreTheory Require Import SymCore ConCore CostLaws Completeness Model.
From Stdlib Require Import Strings.String Lists.List Bool.Bool Lia.
Import ListNotations.
Open Scope string_scope.

Definition wcoercion : coercion := MkCoercion (TyCon tt) (TyCon tt) RoleRepresentational.

Definition true_alternative : @expr model_sorts := ECon "A".
Definition false_alternative : @expr model_sorts := ECon "B".
Definition boolean_alternatives : list (@alt model_sorts) :=
  Alt dcon_true nil true_alternative :: Alt dcon_false nil false_alternative :: nil.

Lemma app_mentions_left : forall (f a : @expr model_sorts),
  mentions_out_of_fuel f = true -> mentions_out_of_fuel (EApp f a) = true.
Proof. intros f a H. simpl. rewrite H. reflexivity. Qed.

Lemma app_mentions_right : forall (f a : @expr model_sorts),
  mentions_out_of_fuel a = true -> mentions_out_of_fuel (EApp f a) = true.
Proof. intros f a H. simpl. rewrite H. apply orb_true_r. Qed.

Definition negate_cast (e : @expr model_sorts) (γ : coercion) : @expr model_sorts :=
  EApp (EPrimOp PNot) e.

Definition negate_solver : @SymCoreSolver model_sorts :=
  Build_SymCoreSolver model_sat (PCLit true) eq_refl model_reduce_prim
    negate_cast keep_coercion keep_type.

Definition negate_cost_laws : @SymFCCostLaws model_sorts negate_solver.
Proof.
  constructor; [constructor | |].
  - exact model_reduce_prim_solvable.
  - exact model_reduce_prim_saturated.
  - exact model_reduce_prim_concore.
  - intros e γ H. repeat constructor. exact H.
  - exact model_reduce_prim_scoped.
  - intros S L e γ H. apply SymScoped_App; [apply SymScoped_PrimOp | exact H].
  - exact model_reduce_prim_keeps_out_of_fuel.
  - intros e γ H. exact (app_mentions_right (EPrimOp PNot) e H).
  - exact model_models_sat.
  - exact model_prim_value_and.
  - exact model_reduce_prim_contains.
  - exact model_reduce_prim_denote.
  - exact model_reduce_prim_ground_value.
  - intros σ S es ec γ H. apply Cont_App; [apply Cont_PrimOp | exact H].
  - exact model_reduce_prim_ite_wellformed.
  - exact model_subst_coerc_contains_env.
  - exact model_subst_type_contains_env.
  - intros σ S k es ec γ H. change k with (0 + k)%nat.
    apply ContK_App; [apply ContK_PrimOp | exact H].
  - exact model_reduce_prim_contains_k.
Qed.

Definition apply_true_cast (e : @expr model_sorts) (γ : coercion) : @expr model_sorts :=
  EApp e (ELit true).

Definition apply_true_solver : @SymCoreSolver model_sorts :=
  Build_SymCoreSolver model_sat (PCLit true) eq_refl model_reduce_prim
    apply_true_cast keep_coercion keep_type.

Definition apply_true_cost_laws : @SymFCCostLaws model_sorts apply_true_solver.
Proof.
  constructor; [constructor | |].
  - exact model_reduce_prim_solvable.
  - exact model_reduce_prim_saturated.
  - exact model_reduce_prim_concore.
  - intros e γ H. repeat constructor. exact H.
  - exact model_reduce_prim_scoped.
  - intros S L e γ H. apply SymScoped_App; [exact H | apply SymScoped_Lit].
  - exact model_reduce_prim_keeps_out_of_fuel.
  - intros e γ H. exact (app_mentions_left e (ELit true) H).
  - exact model_models_sat.
  - exact model_prim_value_and.
  - exact model_reduce_prim_contains.
  - exact model_reduce_prim_denote.
  - exact model_reduce_prim_ground_value.
  - intros σ S es ec γ H. apply Cont_App; [exact H | apply Cont_Lit].
  - exact model_reduce_prim_ite_wellformed.
  - exact model_subst_coerc_contains_env.
  - exact model_subst_type_contains_env.
  - intros σ S k es ec γ H. replace k with (k + 0)%nat by lia.
    apply ContK_App; [exact H | apply ContK_Lit].
  - exact model_reduce_prim_contains_k.
Qed.

Section NegatingCast.
#[local] Existing Instance negate_solver | 0.

Definition negated_true_program : @expr model_sorts :=
  ECase (ECast (ELit true) wcoercion) boolean_alternatives.

Lemma negated_true_is_a_ground_formula :
  expr_to_pc · (cast_expr (@ELit model_sorts true) wcoercion)
  = Some (PCPrim PNot (PCLit true :: nil))
  /\ pc_has_var (PCPrim PNot (@PCLit model_sorts true :: nil)) = false
  /\ truth_constructor (pc_closed_value (PCPrim PNot (@PCLit model_sorts true :: nil)))
     = dcon_false.
Proof. repeat split; reflexivity. Qed.

Lemma negated_true_folds_to_the_false_alternative : forall Φ Γ,
  fold_alts Inf Φ Γ (merge Γ (cast_expr (@ELit model_sorts true) wcoercion))
    boolean_alternatives false_alternative.
Proof.
  intros Φ Γ.
  eapply FoldAlts_GroundFormula; [reflexivity | reflexivity |].
  eapply FoldAlts_Con; [reflexivity | reflexivity |].
  exact (Eval_Con Unlimited Φ _ (ECon "B") "B" nil eq_refl).
Qed.

Theorem a_ground_formula_scrutinee_agrees_with_its_instance :
  @SymFCCostLaws model_sorts negate_solver
  /\ (forall Φ, eval Inf Φ · negated_true_program false_alternative)
  /\ (· ⊢ᶜ negated_true_program ⇓ᶜ false_alternative)
  /\ false_alternative <> true_alternative.
Proof.
  split; [exact negate_cost_laws |].
  assert (Hrun : forall Φ, eval Inf Φ · negated_true_program false_alternative).
  { intros Φ. unfold negated_true_program.
    eapply Eval_Case; [apply Eval_Cast; apply Eval_Lit |].
    apply negated_true_folds_to_the_false_alternative. }
  split; [exact Hrun |].
  split; [exact (Hrun pc_true) | discriminate].
Qed.

Definition guard_var : var := "x".
Definition branch_value : @expr model_sorts :=
  EIf (EVar guard_var) (ELit true) (ELit false).
Definition branch_under_a_primitive : @expr model_sorts :=
  EApp (EPrimOp PNot) branch_value.
Definition branch_cast_program : @expr model_sorts :=
  ECase (ECast branch_value wcoercion) boolean_alternatives.

Lemma branch_under_a_primitive_reads_as_no_formula :
  expr_to_pc · branch_under_a_primitive = None
  /\ is_op_app branch_under_a_primitive = true.
Proof. split; reflexivity. Qed.

Lemma branch_under_a_primitive_does_not_fold : forall Φ alts r,
  ~ fold_alts Inf Φ · (merge · branch_under_a_primitive) alts r.
Proof.
  intros Φ alts r H.
  change (merge · branch_under_a_primitive) with branch_under_a_primitive in H.
  inversion H; subst; try discriminate;
    match goal with
    | [ Hp : expr_to_pc _ _ = Some _ |- _ ] => cbn in Hp; discriminate Hp
    | [ Hop : is_op_app _ = false |- _ ] => cbn in Hop; discriminate Hop
    end.
Qed.

Lemma branch_value_is_its_own_value : forall Φ v,
  eval Inf Φ · branch_value v -> v = branch_value.
Proof.
  intros Φ v H. unfold branch_value in H.
  inversion H; subst.
  - match goal with [ Hu : unspool_app _ nil = _ |- _ ] => cbn in Hu; discriminate Hu end.
  - unfold branch_value.
    assert (Hsat : forall Ψ, @sat model_sorts negate_solver Ψ = true) by reflexivity.
    match goal with
    | [ Hg : eval _ _ _ (EVar guard_var) _ |- _ ] =>
        destruct (eval_var_inv _ _ _ _ (Hsat _) Hg) as [[Γ' [e' [Hl _]]] | [_ Heq]];
        [discriminate Hl | subst]
    end.
    match goal with
    | [ Ht : eval _ _ _ (ELit true) _ |- _ ] => rewrite (eval_lit_same _ _ _ _ (Hsat _) Ht) end.
    match goal with
    | [ Hf : eval _ _ _ (ELit false) _ |- _ ] => rewrite (eval_lit_same _ _ _ _ (Hsat _) Hf) end.
    reflexivity.
  - match goal with [ Hs : sat _ = false |- _ ] => discriminate Hs end.
Qed.

Theorem a_branch_inside_a_primitive_is_stuck :
  (forall Φ, eval Inf Φ · (ECast branch_value wcoercion) branch_under_a_primitive)
  /\ (forall Φ v, ~ eval Inf Φ · branch_cast_program v).
Proof.
  split.
  { intros Φ.
    change branch_under_a_primitive with (cast_expr branch_value wcoercion).
    apply Eval_Cast.
    eapply Eval_If with (pc_c := PCVar guard_var);
      [apply Eval_SymVar; reflexivity | reflexivity | apply Eval_Lit | apply Eval_Lit]. }
  intros Φ v H. unfold branch_cast_program in H.
  inversion H; subst.
  - match goal with [ Hu : unspool_app _ nil = _ |- _ ] => cbn in Hu; discriminate Hu end.
  - match goal with [ Hs : eval _ _ _ (ECast _ _) _ |- _ ] => inversion Hs; subst end.
    + match goal with [ Hu : unspool_app (ECast _ _) nil = _ |- _ ] =>
        cbn in Hu; discriminate Hu end.
    + match goal with
      | [ Hb : eval _ _ _ branch_value _, Hfold : fold_alts _ _ _ _ _ _ |- _ ] =>
          rewrite (branch_value_is_its_own_value _ _ Hb) in Hfold;
          exact (branch_under_a_primitive_does_not_fold _ _ _ Hfold)
      end.
    + match goal with [ Hsat : sat _ = false |- _ ] => discriminate Hsat end.
  - match goal with [ Hs : sat _ = false |- _ ] => discriminate Hs end.
Qed.

End NegatingCast.

Section ApplyingCast.
#[local] Existing Instance apply_true_solver | 0.

Definition other_var : var := "y".
Definition and_of_two_vars : @expr model_sorts :=
  EApp (EApp (EPrimOp PAnd) (EVar guard_var)) (EVar other_var).
Definition over_applied_and : @expr model_sorts :=
  EApp and_of_two_vars (ELit true).
Definition and_cast_program : @expr model_sorts :=
  ECase (ECast and_of_two_vars wcoercion) boolean_alternatives.

Lemma over_applied_and_has_a_wrong_arity :
  expr_to_pc · over_applied_and
  = Some (PCPrim PAnd (PCVar guard_var :: PCVar other_var :: PCLit true :: nil))
  /\ pc_arities_ok
       (PCPrim PAnd (@PCVar model_sorts guard_var :: PCVar other_var :: PCLit true :: nil))
     = false
  /\ pc_has_var
       (PCPrim PAnd (@PCVar model_sorts guard_var :: PCVar other_var :: PCLit true :: nil))
     = true.
Proof. repeat split; reflexivity. Qed.

Lemma over_applied_and_does_not_fold : forall Φ alts r,
  ~ fold_alts Inf Φ · (merge · over_applied_and) alts r.
Proof.
  intros Φ alts r H.
  change (merge · over_applied_and) with over_applied_and in H.
  inversion H; subst; try discriminate;
    match goal with
    | [ Hp : expr_to_pc _ _ = Some _, Hv : pc_has_var _ = false |- _ ] =>
        cbn in Hp; injection Hp as <-; cbn in Hv; discriminate Hv
    | [ Hp : expr_to_pc _ _ = Some _, Ha : pc_arities_ok _ = true |- _ ] =>
        cbn in Hp; injection Hp as <-; cbn in Ha; discriminate Ha
    | [ Hop : is_op_app _ = false |- _ ] => cbn in Hop; discriminate Hop
    end.
Qed.

Lemma and_of_two_vars_is_its_own_value : forall Φ v,
  eval Inf Φ · and_of_two_vars v -> v = and_of_two_vars.
Proof.
  intros Φ v H. unfold and_of_two_vars in H.
  inversion H; subst.
  - match goal with [ Hu : unspool_app _ nil = (ECon _, _) |- _ ] =>
      cbn in Hu; discriminate Hu end.
  - match goal with [ Hc : Comp _ _ |- _ ] =>
      pose proof (comp_not_op_app _ _ Hc) as Hop; cbn in Hop; discriminate Hop end.
  - match goal with [ Hu : unspool_app _ nil = (EPrimOp _, _) |- _ ] =>
      cbn in Hu; injection Hu as Hp Ha end.
    subst.
    match goal with [ Hf : Forall2 _ _ _ |- _ ] =>
      inversion Hf as [| ? v1 ? r1 Hv1 H1r]; subst;
      inversion H1r as [| ? v2 ? r2 Hv2 H2r]; subst;
      inversion H2r; subst end.
    assert (Hsat : forall Ψ, @sat model_sorts apply_true_solver Ψ = true) by reflexivity.
    destruct (eval_var_inv _ _ _ _ (Hsat _) Hv1) as [[Γ1 [e1 [Hl1 _]]] | [_ Heq1]];
      [discriminate Hl1 |].
    destruct (eval_var_inv _ _ _ _ (Hsat _) Hv2) as [[Γ2 [e2 [Hl2 _]]] | [_ Heq2]];
      [discriminate Hl2 |].
    rewrite Heq1, Heq2. reflexivity.
  - match goal with [ Hu : unspool_app _ nil = (EIf _ _ _, _) |- _ ] =>
      cbn in Hu; discriminate Hu end.
  - match goal with [ Hs : sat _ = false |- _ ] => discriminate Hs end.
Qed.

Theorem a_wrong_arity_formula_is_stuck :
  @SymFCCostLaws model_sorts apply_true_solver
  /\ (forall Φ, eval Inf Φ · (ECast and_of_two_vars wcoercion) over_applied_and)
  /\ (forall Φ v, ~ eval Inf Φ · and_cast_program v).
Proof.
  split; [exact apply_true_cost_laws |].
  split.
  { intros Φ.
    change over_applied_and with (cast_expr and_of_two_vars wcoercion).
    apply Eval_Cast.
    change (eval Inf Φ · and_of_two_vars
              (reduce_prim PAnd (EVar guard_var :: EVar other_var :: nil))).
    eapply Eval_AppPrim; [reflexivity | reflexivity |].
    constructor; [apply Eval_SymVar; reflexivity |].
    constructor; [apply Eval_SymVar; reflexivity | constructor]. }
  intros Φ v H. unfold and_cast_program in H.
  inversion H; subst.
  - match goal with [ Hu : unspool_app _ nil = _ |- _ ] => cbn in Hu; discriminate Hu end.
  - match goal with [ Hs : eval _ _ _ (ECast _ _) _ |- _ ] => inversion Hs; subst end.
    + match goal with [ Hu : unspool_app (ECast _ _) nil = _ |- _ ] =>
        cbn in Hu; discriminate Hu end.
    + match goal with
      | [ Hb : eval _ _ _ and_of_two_vars _, Hfold : fold_alts _ _ _ _ _ _ |- _ ] =>
          rewrite (and_of_two_vars_is_its_own_value _ _ Hb) in Hfold;
          exact (over_applied_and_does_not_fold _ _ _ Hfold)
      end.
    + match goal with [ Hsat : sat _ = false |- _ ] => discriminate Hsat end.
  - match goal with [ Hs : sat _ = false |- _ ] => discriminate Hs end.
Qed.

End ApplyingCast.

Section MergedBranch.
#[local] Existing Instance model_solver | 0.

Definition mixed_branch : @expr model_sorts :=
  EIf (EVar guard_var) (ELit true) (EVar other_var).
Definition mixed_branch_program : @expr model_sorts :=
  ECase mixed_branch boolean_alternatives.
Definition concrete_branch_program : @expr model_sorts :=
  ECase (ELit true) boolean_alternatives.

Definition guard_only : symvars := fun v => if string_dec v guard_var then true else false.
Definition both_symbolic : symvars :=
  fun v => if string_dec v guard_var then true
           else if string_dec v other_var then true else false.
Definition guard_true : valuation :=
  fun v => if string_dec v guard_var then true else false.

Theorem a_free_untaken_arm_is_not_a_symbolic_program :
  ~ symbolic_program guard_only · mixed_branch_program.
Proof.
  intros [_ Hsc].
  unfold mixed_branch_program, mixed_branch in Hsc.
  inversion Hsc as [| | | | | | L es alts Hes _ | | | | | |]; subst.
  inversion Hes as [| | | | | | | | | | L1 ec et ef _ _ Hef | |]; subst.
  inversion Hef as [L2 y Hy | | | | | | | | | | | |]; subst.
  destruct Hy as [Hy | Hy]; [destruct Hy | discriminate Hy].
Qed.

Definition merged_mixed_branch : @expr model_sorts :=
  EApp (EApp (EApp (EPrimOp PIte) (EVar guard_var)) (ELit true)) (EVar other_var).

Lemma mixed_branch_merges_to_a_formula :
  merge · mixed_branch = merged_mixed_branch.
Proof. reflexivity. Qed.

Theorem a_symbolic_untaken_arm_agrees_with_its_instance :
  symbolic_program both_symbolic · mixed_branch_program
  /\ contains guard_true both_symbolic mixed_branch_program concrete_branch_program
  /\ eval Inf pc_true · mixed_branch_program
       (EIf merged_mixed_branch true_alternative false_alternative)
  /\ (· ⊢ᶜ concrete_branch_program ⇓ᶜ true_alternative)
  /\ contains guard_true both_symbolic
       (EIf merged_mixed_branch true_alternative false_alternative) true_alternative.
Proof.
  assert (Hmerged : models_cond guard_true both_symbolic merged_mixed_branch).
  { exists (@PCPrim model_sorts PIte
              (PCVar guard_var :: @PCLit model_sorts true :: PCVar other_var :: nil)).
    split; [| reflexivity].
    intros Γ Hfree. cbn.
    rewrite (Hfree guard_var eq_refl), (Hfree other_var eq_refl). reflexivity. }
  split.
  { split; [constructor |].
    apply SymScoped_Case; [| repeat constructor].
    apply SymScoped_If; [| constructor |];
      apply SymScoped_Var; right; reflexivity. }
  split.
  { apply Cont_Case; [| repeat constructor].
    apply Cont_If_True; [| apply Cont_Lit].
    exists (PCVar guard_var). split; [| reflexivity].
    intros Γ Hfree. cbn. rewrite (Hfree guard_var eq_refl). reflexivity. }
  split.
  { unfold mixed_branch_program.
    eapply Eval_Case.
    - eapply Eval_If with (pc_c := PCVar guard_var);
        [apply Eval_SymVar; reflexivity | reflexivity | apply Eval_Lit
         | apply Eval_SymVar; reflexivity].
    - change (merge · (EIf (EVar guard_var) (@ELit model_sorts true) (EVar other_var)))
        with merged_mixed_branch.
      eapply FoldAlts_SymbolicFormula; [reflexivity | reflexivity | reflexivity | |].
      + eapply FoldAlts_Con; [reflexivity | reflexivity |].
        exact (Eval_Con Unlimited _ · (ECon "A") "A" nil eq_refl).
      + eapply FoldAlts_Con; [reflexivity | reflexivity |].
        exact (Eval_Con Unlimited _ · (ECon "B") "B" nil eq_refl). }
  split.
  { unfold eval_con, concrete_branch_program.
    eapply Eval_Case; [apply Eval_Lit |].
    change (merge · (@ELit model_sorts true)) with (@ELit model_sorts true).
    eapply FoldAlts_GroundFormula; [reflexivity | reflexivity |].
    eapply FoldAlts_Con; [reflexivity | reflexivity |].
    exact (Eval_Con Unlimited _ · (ECon "A") "A" nil eq_refl). }
  apply Cont_If_True; [exact Hmerged | apply Cont_Con].
Qed.

End MergedBranch.

Print Assumptions a_ground_formula_scrutinee_agrees_with_its_instance.
Print Assumptions a_branch_inside_a_primitive_is_stuck.
Print Assumptions a_wrong_arity_formula_is_stuck.
Print Assumptions a_free_untaken_arm_is_not_a_symbolic_program.
Print Assumptions a_symbolic_untaken_arm_agrees_with_its_instance.
