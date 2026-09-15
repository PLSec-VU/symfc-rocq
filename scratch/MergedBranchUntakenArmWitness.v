From SymCoreTheory Require Import SymCore ConCore CostLaws Completeness Model.
From Stdlib Require Import Strings.String Lists.List Lia.
Import ListNotations.
Open Scope string_scope.

Section ApprovedCalculus.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.
Variables dcon_true dcon_false : dcon.

Fixpoint pc_has_var (pc : path_condition) : bool :=
  match pc with
  | PCVar _ => true
  | PCLit _ => false
  | PCPrim _ args => existsb pc_has_var args
  end.

Fixpoint pc_arities_ok (pc : path_condition) : bool :=
  match pc with
  | PCVar _ | PCLit _ => true
  | PCPrim p args => Nat.eqb (length args) (primop_arity p) && forallb pc_arities_ok args
  end.

Definition pc_ground_value (pc : path_condition) : lit := pc_value (fun _ => lit_true) pc.

Definition truth_constructor (l : lit) : dcon :=
  if lit_eq_dec l lit_true then dcon_true else dcon_false.

Inductive eval_a : fuel -> path_condition -> environment -> expr -> expr -> Prop :=
  | EvalA_Var : forall f Φ Γ x Γ' e e',
      lookup_env Γ x = Some (Γ', e) -> eval_a (dec f) Φ Γ' e e' -> eval_a (Live f) Φ Γ (EVar x) e'
  | EvalA_SymVar : forall f Φ Γ x,
      lookup_env Γ x = None -> eval_a (Live f) Φ Γ (EVar x) (EVar x)
  | EvalA_Lit : forall f Φ Γ l, eval_a (Live f) Φ Γ (ELit l) (ELit l)
  | EvalA_Con : forall f Φ Γ e d args,
      unspool_app e [] = (ECon d, args) ->
      eval_a (Live f) Φ Γ e (make_con_app d (map (delay Γ) args))
  | EvalA_Cast : forall f Φ Γ e γ e',
      eval_a (dec f) Φ Γ e e' -> eval_a (Live f) Φ Γ (ECast e γ) (cast_expr e' γ)
  | EvalA_AppAbs : forall f Φ Γ Γ' x eb ea eb',
      eval_a (dec f) Φ (extend_env Γ' x Γ ea) eb eb' ->
      eval_a (Live f) Φ Γ (EApp (EThunk Γ' (ELam x eb)) ea) eb'
  | EvalA_AppSpine : forall f Φ Γ ef ea ef' er,
      Comp Γ ef -> eval_a (dec f) Φ Γ ef ef' -> eval_a (dec f) Φ Γ (EApp ef' ea) er ->
      eval_a (Live f) Φ Γ (EApp ef ea) er
  | EvalA_Bot : forall f Φ Γ b, eval_a (Live f) Φ Γ (EBot b) (EBot b)
  | EvalA_AppPrim : forall f Φ Γ ef ea p args args',
      unspool_app (EApp ef ea) [] = (EPrimOp p, args) ->
      length args = primop_arity p ->
      Forall2 (eval_a (dec f) Φ Γ) args args' ->
      eval_a (Live f) Φ Γ (EApp ef ea) (reduce_prim p args')
  | EvalA_Lam : forall f Φ Γ x e, eval_a (Live f) Φ Γ (ELam x e) (EThunk Γ (ELam x e))
  | EvalA_AppCast : forall f Φ Γ ef γ ea γ_a γ_r er,
      decomp_coerc_arrow γ = Some (γ_a, γ_r) ->
      eval_a (dec f) Φ Γ (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r) er ->
      eval_a (Live f) Φ Γ (EApp (ECast ef γ) ea) er
  | EvalA_AppIf : forall f Φ Γ e1 e2 ec et ef args er,
      unspool_app (EApp e1 e2) [] = (EIf ec et ef, args) ->
      eval_a (dec f) Φ Γ (EIf ec (fold_left EApp args et) (fold_left EApp args ef)) er ->
      eval_a (Live f) Φ Γ (EApp e1 e2) er
  | EvalA_AppBot : forall f Φ Γ b ea, eval_a (Live f) Φ Γ (EApp (EBot b) ea) (EBot b)
  | EvalA_Case : forall f Φ Γ es alts es' er,
      eval_a (dec f) Φ Γ es es' -> fold_alts_a (dec f) Φ Γ (merge Γ es') alts er ->
      eval_a (Live f) Φ Γ (ECase es alts) er
  | EvalA_If : forall f Φ Γ ec et ef ec' et' ef' pc_c,
      eval_a (dec f) Φ Γ ec ec' -> expr_to_pc Γ ec' = Some pc_c ->
      eval_a (dec f) (Φ ∧ pc_c) Γ et et' -> eval_a (dec f) (Φ ∧ ¬ pc_c) Γ ef ef' ->
      eval_a (Live f) Φ Γ (EIf ec et ef) (EIf ec' et' ef')
  | EvalA_Coercion : forall f Φ Γ γ, eval_a (Live f) Φ Γ (ECoercion γ) (ECoercion (subst_coerc Γ γ))
  | EvalA_Prune : forall f Φ Γ e, sat Φ = false -> eval_a (Live f) Φ Γ e (EBot BUnreachable)
  | EvalA_Type : forall f Φ Γ τ, eval_a (Live f) Φ Γ (EType τ) (EType (subst_type Γ τ))
  | EvalA_Thunk : forall f Φ Γ Γ' e e',
      eval_a (dec f) Φ Γ' e e' -> eval_a (Live f) Φ Γ (EThunk Γ' e) e'
  | EvalA_OutOfFuel : forall Φ Γ e, eval_a Spent Φ Γ e (EBot BOutOfFuel)

with fold_alts_a : fuel -> path_condition -> environment -> expr -> list alt -> expr -> Prop :=
  | FoldAltsA_If : forall f Φ Γ ec et ef alts et' ef' pc_c,
      expr_to_pc Γ ec = Some pc_c ->
      fold_alts_a f (Φ ∧ pc_c) Γ et alts et' -> fold_alts_a f (Φ ∧ ¬ pc_c) Γ ef alts ef' ->
      fold_alts_a f Φ Γ (EIf ec et ef) alts (EIf ec et' ef')
  | FoldAltsA_IfFail : forall f Φ Γ ec et ef alts,
      expr_to_pc Γ ec = None -> fold_alts_a f Φ Γ (EIf ec et ef) alts (EBot BUndefined)
  | FoldAltsA_Con : forall f Φ Γ e d ea xs ep alts er,
      decompose_con_app e = Some (d, ea) -> find_alt d alts = Some (xs, ep) ->
      eval_a f Φ (extend_env_multi Γ xs ea Γ) ep er -> fold_alts_a f Φ Γ e alts er
  | FoldAltsA_Bot : forall f Φ Γ b alts, fold_alts_a f Φ Γ (EBot b) alts (EBot b)
  | FoldAltsA_GroundFormula : forall f Φ Γ e pc alts r,
      expr_to_pc Γ e = Some pc -> pc_has_var pc = false ->
      fold_alts_a f Φ Γ (ECon (truth_constructor (pc_ground_value pc))) alts r ->
      fold_alts_a f Φ Γ e alts r
  | FoldAltsA_SymbolicFormula : forall f Φ Γ e pc alts r1 r2,
      expr_to_pc Γ e = Some pc -> pc_has_var pc = true -> pc_arities_ok pc = true ->
      fold_alts_a f (Φ ∧ pc) Γ (ECon dcon_true) alts r1 ->
      fold_alts_a f (Φ ∧ ¬ pc) Γ (ECon dcon_false) alts r2 ->
      fold_alts_a f Φ Γ e alts (EIf e r1 r2)
  | FoldAltsA_Otherwise : forall f Φ Γ e alts,
      expr_to_pc Γ e = None ->
      is_op_app e = false ->
      is_if (fst (unspool_app e [])) = false ->
      (match decompose_con_app e with
       | Some (d, _) => find_alt d alts = None
       | None => True
       end) ->
      is_bot e = false ->
      fold_alts_a f Φ Γ e alts (EBot BUndefined).

Definition approved_soundness : Prop :=
  forall Φ Γs Γc σ S e_sym e_con v_sym,
    σ ⊨ Φ ->
    contains_env σ S Γs Γc ->
    contains σ S e_sym e_con ->
    concore_expr e_con ->
    closed_program Γc e_con ->
    eval_a Inf Φ Γs e_sym v_sym ->
    exists v_con, eval_a Inf pc_true Γc e_con v_con /\ contains σ S v_sym v_con.

End ApprovedCalculus.

Definition approved_eval := @eval_a model_sorts model_solver "True" "False".

Definition untaken_arm_scrutinee : @expr model_sorts :=
  EIf (EVar "x") (@ELit model_sorts true) (EVar "y").

Definition merged_scrutinee : @expr model_sorts :=
  EApp (EApp (EApp (@EPrimOp model_sorts PIte) (EVar "x")) (@ELit model_sorts true)) (EVar "y").

Definition merged_formula : @path_condition model_sorts :=
  PCPrim PIte (PCVar "x" :: @PCLit model_sorts true :: PCVar "y" :: nil).

Definition true_false_alts : list (@alt model_sorts) :=
  Alt "True" nil (@ELit model_sorts false) :: Alt "False" nil (@ELit model_sorts true) :: nil.

Definition symbolic_program : @expr model_sorts := ECase untaken_arm_scrutinee true_false_alts.

Definition concrete_program : @expr model_sorts := ECase (@ELit model_sorts true) true_false_alts.

Definition only_x : symvars := fun v => if string_dec v "x" then true else false.
Definition all_true : @valuation model_sorts := fun _ => true.

Definition symbolic_result : @expr model_sorts :=
  EIf merged_scrutinee (@ELit model_sorts false) (@ELit model_sorts true).

Lemma merge_turns_branch_into_ite_formula :
  @merge model_sorts model_solver · untaken_arm_scrutinee = merged_scrutinee.
Proof. reflexivity. Qed.

Lemma merged_scrutinee_is_symbolic_formula :
  @expr_to_pc model_sorts · merged_scrutinee = Some merged_formula
  /\ pc_has_var merged_formula = true
  /\ pc_arities_ok merged_formula = true.
Proof. repeat split. Qed.

Lemma symbolic_run_builds_branch :
  approved_eval Inf (@PCLit model_sorts true) · symbolic_program symbolic_result.
Proof.
  unfold approved_eval, symbolic_program.
  apply (EvalA_Case _ _ Unlimited (@PCLit model_sorts true) · _ _ untaken_arm_scrutinee).
  - unfold untaken_arm_scrutinee.
    eapply EvalA_If;
      [apply EvalA_SymVar; reflexivity | reflexivity | apply EvalA_Lit | apply EvalA_SymVar; reflexivity].
  - rewrite merge_turns_branch_into_ite_formula. unfold symbolic_result.
    apply (FoldAltsA_SymbolicFormula _ _ _ _ _ _ merged_formula); try reflexivity.
    + eapply FoldAltsA_Con; [reflexivity | reflexivity | apply EvalA_Lit].
    + eapply FoldAltsA_Con; [reflexivity | reflexivity | apply EvalA_Lit].
Qed.

Lemma concrete_run_gives_false :
  approved_eval Inf (@PCLit model_sorts true) · concrete_program (@ELit model_sorts false).
Proof.
  unfold approved_eval, concrete_program.
  apply (EvalA_Case _ _ Unlimited (@PCLit model_sorts true) · _ _ (@ELit model_sorts true)).
  - apply EvalA_Lit.
  - apply (FoldAltsA_GroundFormula _ _ _ _ _ _ (@PCLit model_sorts true)); try reflexivity.
    eapply FoldAltsA_Con; [reflexivity | reflexivity | apply EvalA_Lit].
Qed.

Definition binds_y : @environment model_sorts :=
  ExtendEnv "y" (MkClosure · (EBot BUndefined)) ·.

Lemma binds_y_is_sym_free : sym_free_env only_x binds_y.
Proof.
  intros z Hz. unfold binds_y. simpl.
  destruct (string_dec z "y") as [Heq | Hne]; [subst z; discriminate Hz | reflexivity].
Qed.

Lemma merged_scrutinee_denotes_nothing : forall pc,
  ~ denotes only_x merged_scrutinee pc.
Proof.
  intros pc Hden. specialize (Hden binds_y binds_y_is_sym_free). discriminate Hden.
Qed.

Lemma symbolic_result_has_no_instance : forall v,
  ~ @contains model_sorts all_true only_x symbolic_result v.
Proof.
  intros v H. unfold symbolic_result in H.
  inversion H as [| | | | | | | | | | | | | | ec et ef etc Hcond | ec et ef efc Hcond | es p args l Hun];
    subst.
  - destruct Hcond as [pc [Hden _]]. exact (merged_scrutinee_denotes_nothing pc Hden).
  - destruct Hcond as [pc [Hden _]]. exact (merged_scrutinee_denotes_nothing pc Hden).
  - discriminate Hun.
Qed.

Lemma symbolic_contains_concrete :
  @contains model_sorts all_true only_x symbolic_program concrete_program.
Proof.
  apply Cont_Case.
  - unfold untaken_arm_scrutinee. apply Cont_If_True; [| apply Cont_Lit].
    exists (PCVar "x"). split; [| reflexivity].
    intros Γ Hfree. simpl. rewrite (Hfree "x" eq_refl). reflexivity.
  - repeat constructor.
Qed.

Lemma model_prim_value_not : forall l : @lit model_sorts,
  prim_value op_not (l :: nil) = lit_true <-> l <> lit_true.
Proof. intros l. destruct l; simpl; split; congruence. Qed.

Theorem approved_design_breaks_soundness_in_the_model :
  @SymFCCostLaws model_sorts model_solver
  /\ (forall l : @lit model_sorts, prim_value op_not (l :: nil) = lit_true <-> l <> lit_true)
  /\ ~ @approved_soundness model_sorts model_solver "True" "False".
Proof.
  split; [exact model_symfc_cost_laws |]. split; [exact model_prim_value_not |].
  intros Hsound.
  destruct (Hsound (@PCLit model_sorts true) · · all_true only_x symbolic_program concrete_program
              symbolic_result) as [v [_ Hcont]].
  - reflexivity.
  - apply Cont_Env_Empty.
  - exact symbolic_contains_concrete.
  - repeat constructor.
  - split; [apply Scoped_Env_Empty | repeat constructor].
  - exact symbolic_run_builds_branch.
  - exact (symbolic_result_has_no_instance v Hcont).
Qed.

Print Assumptions approved_design_breaks_soundness_in_the_model.
