From SymCoreTheory Require Import SymCore ConCore CostLaws Completeness Model.
From Stdlib Require Import Strings.String Lists.List Bool.Bool Lia.
Import ListNotations.
Open Scope string_scope.

Definition negate_cast (e : @expr model_sorts) (γ : coercion) : @expr model_sorts :=
  EApp (EPrimOp PNot) e.

Definition apply_true_cast (e : @expr model_sorts) (γ : coercion) : @expr model_sorts :=
  EApp e (ELit true).

Lemma app_mentions_left : forall (f a : @expr model_sorts),
  mentions_out_of_fuel f = true -> mentions_out_of_fuel (EApp f a) = true.
Proof. intros f a H. simpl. rewrite H. reflexivity. Qed.

Lemma app_mentions_right : forall (f a : @expr model_sorts),
  mentions_out_of_fuel a = true -> mentions_out_of_fuel (EApp f a) = true.
Proof. intros f a H. simpl. rewrite H. apply orb_true_r. Qed.

Definition negate_solver : @SymCoreSolver model_sorts :=
  Build_SymCoreSolver model_sat (PCLit true) eq_refl model_reduce_prim
    negate_cast keep_coercion keep_type.

Definition apply_true_solver : @SymCoreSolver model_sorts :=
  Build_SymCoreSolver model_sat (PCLit true) eq_refl model_reduce_prim
    apply_true_cast keep_coercion keep_type.

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

Definition a_coercion : coercion := MkCoercion (TyCon tt) (TyCon tt) RoleRepresentational.

Definition cast_true : @expr model_sorts := ECast (ELit true) a_coercion.
Definition negated_true : @expr model_sorts := EApp (EPrimOp PNot) (ELit true).

Theorem negating_cast_gives_closed_formula_scrutinee :
  @SymFCCostLaws model_sorts negate_solver
  /\ @eval model_sorts negate_solver Inf (PCLit true) · cast_true negated_true
  /\ expr_to_pc · negated_true = Some (PCPrim PNot (PCLit true :: nil))
  /\ concore_expr negated_true.
Proof.
  split; [exact negate_cost_laws |]. split; [| split; [reflexivity | repeat constructor]].
  change negated_true with (@cast_expr model_sorts negate_solver (ELit true) a_coercion).
  apply Eval_Cast. apply Eval_Lit.
Qed.

Definition and_xy : @expr model_sorts := EApp (EApp (EPrimOp PAnd) (EVar "x")) (EVar "y").
Definition and_tf : @expr model_sorts := EApp (EApp (EPrimOp PAnd) (ELit true)) (ELit false).
Definition sym_xy : symvars := fun v => if string_dec v "x" then true else if string_dec v "y" then true else false.
Definition x_true_y_false : valuation := fun v => if string_dec v "x" then true else false.

Theorem applying_cast_splits_formula_from_its_instance :
  @SymFCCostLaws model_sorts apply_true_solver
  /\ contains x_true_y_false sym_xy (ECast and_xy a_coercion) (ECast and_tf a_coercion)
  /\ @eval model_sorts apply_true_solver Inf (PCLit true) · (ECast and_xy a_coercion) (EApp and_xy (ELit true))
  /\ @eval model_sorts apply_true_solver Inf (PCLit true) · (ECast and_tf a_coercion) (EApp (ELit false) (ELit true))
  /\ @expr_to_pc model_sorts · (EApp and_xy (ELit true)) = Some (PCPrim PAnd (PCVar "x" :: PCVar "y" :: PCLit true :: nil))
  /\ @expr_to_pc model_sorts · (EApp (ELit false) (ELit true)) = None.
Proof.
  split; [exact apply_true_cost_laws |].
  split.
  { unfold and_xy, and_tf. apply Cont_Cast. repeat apply Cont_App; try apply Cont_PrimOp.
    - change true with (x_true_y_false "x"). apply Cont_Var_Sym. reflexivity.
    - change false with (x_true_y_false "y"). apply Cont_Var_Sym. reflexivity. }
  split.
  { change (@EApp model_sorts and_xy (@ELit model_sorts true)) with (@cast_expr model_sorts apply_true_solver and_xy a_coercion).
    apply Eval_Cast.
    change (@eval model_sorts apply_true_solver Inf (PCLit true) · and_xy
              (@reduce_prim model_sorts apply_true_solver PAnd (EVar "x" :: EVar "y" :: nil))).
    eapply Eval_AppPrim; [reflexivity | reflexivity |].
    repeat constructor. }
  split.
  { change (@EApp model_sorts (@ELit model_sorts false) (@ELit model_sorts true)) with (@cast_expr model_sorts apply_true_solver (ELit false) a_coercion).
    apply Eval_Cast.
    change (@eval model_sorts apply_true_solver Inf (PCLit true) · and_tf
              (@reduce_prim model_sorts apply_true_solver PAnd (ELit true :: ELit false :: nil))).
    eapply Eval_AppPrim; [reflexivity | reflexivity |].
    repeat constructor. }
  split; reflexivity.
Qed.
