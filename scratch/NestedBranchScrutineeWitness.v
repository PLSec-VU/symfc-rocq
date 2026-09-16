From SymCoreTheory Require Import SymCore ConCore CostLaws Completeness Model.
From Stdlib Require Import Strings.String Lists.List Bool.Bool Lia.
Import ListNotations.
Open Scope string_scope.

Section ProposedCalculus.
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

Inductive eval_p : fuel -> path_condition -> environment -> expr -> expr -> Prop :=
  | EvalP_Var : forall f Φ Γ x Γ' e e',
      lookup_env Γ x = Some (Γ', e) -> eval_p (dec f) Φ Γ' e e' -> eval_p (Live f) Φ Γ (EVar x) e'
  | EvalP_SymVar : forall f Φ Γ x,
      lookup_env Γ x = None -> eval_p (Live f) Φ Γ (EVar x) (EVar x)
  | EvalP_Lit : forall f Φ Γ l, eval_p (Live f) Φ Γ (ELit l) (ELit l)
  | EvalP_Con : forall f Φ Γ e d args,
      unspool_app e [] = (ECon d, args) ->
      eval_p (Live f) Φ Γ e (make_con_app d (map (delay Γ) args))
  | EvalP_Cast : forall f Φ Γ e γ e',
      eval_p (dec f) Φ Γ e e' -> eval_p (Live f) Φ Γ (ECast e γ) (cast_expr e' γ)
  | EvalP_AppAbs : forall f Φ Γ Γ' x eb ea eb',
      eval_p (dec f) Φ (extend_env Γ' x Γ ea) eb eb' ->
      eval_p (Live f) Φ Γ (EApp (EThunk Γ' (ELam x eb)) ea) eb'
  | EvalP_AppSpine : forall f Φ Γ ef ea ef' er,
      Comp Γ ef -> eval_p (dec f) Φ Γ ef ef' -> eval_p (dec f) Φ Γ (EApp ef' ea) er ->
      eval_p (Live f) Φ Γ (EApp ef ea) er
  | EvalP_Bot : forall f Φ Γ b, eval_p (Live f) Φ Γ (EBot b) (EBot b)
  | EvalP_AppPrim : forall f Φ Γ ef ea p args args',
      unspool_app (EApp ef ea) [] = (EPrimOp p, args) ->
      length args = primop_arity p ->
      Forall2 (eval_p (dec f) Φ Γ) args args' ->
      eval_p (Live f) Φ Γ (EApp ef ea) (reduce_prim p args')
  | EvalP_Lam : forall f Φ Γ x e, eval_p (Live f) Φ Γ (ELam x e) (EThunk Γ (ELam x e))
  | EvalP_AppCast : forall f Φ Γ ef γ ea γ_a γ_r er,
      decomp_coerc_arrow γ = Some (γ_a, γ_r) ->
      eval_p (dec f) Φ Γ (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r) er ->
      eval_p (Live f) Φ Γ (EApp (ECast ef γ) ea) er
  | EvalP_AppIf : forall f Φ Γ e1 e2 ec et ef args er,
      unspool_app (EApp e1 e2) [] = (EIf ec et ef, args) ->
      eval_p (dec f) Φ Γ (EIf ec (fold_left EApp args et) (fold_left EApp args ef)) er ->
      eval_p (Live f) Φ Γ (EApp e1 e2) er
  | EvalP_AppBot : forall f Φ Γ b ea, eval_p (Live f) Φ Γ (EApp (EBot b) ea) (EBot b)
  | EvalP_Case : forall f Φ Γ es alts es' er,
      eval_p (dec f) Φ Γ es es' -> fold_alts_p (dec f) Φ Γ (merge Γ es') alts er ->
      eval_p (Live f) Φ Γ (ECase es alts) er
  | EvalP_If : forall f Φ Γ ec et ef ec' et' ef' pc_c,
      eval_p (dec f) Φ Γ ec ec' -> expr_to_pc Γ ec' = Some pc_c ->
      eval_p (dec f) (Φ ∧ pc_c) Γ et et' -> eval_p (dec f) (Φ ∧ ¬ pc_c) Γ ef ef' ->
      eval_p (Live f) Φ Γ (EIf ec et ef) (EIf ec' et' ef')
  | EvalP_Coercion : forall f Φ Γ γ, eval_p (Live f) Φ Γ (ECoercion γ) (ECoercion (subst_coerc Γ γ))
  | EvalP_Prune : forall f Φ Γ e, sat Φ = false -> eval_p (Live f) Φ Γ e (EBot BUnreachable)
  | EvalP_Type : forall f Φ Γ τ, eval_p (Live f) Φ Γ (EType τ) (EType (subst_type Γ τ))
  | EvalP_Thunk : forall f Φ Γ Γ' e e',
      eval_p (dec f) Φ Γ' e e' -> eval_p (Live f) Φ Γ (EThunk Γ' e) e'
  | EvalP_OutOfFuel : forall Φ Γ e, eval_p Spent Φ Γ e (EBot BOutOfFuel)

with fold_alts_p : fuel -> path_condition -> environment -> expr -> list alt -> expr -> Prop :=
  | FoldAltsP_If : forall f Φ Γ ec et ef alts et' ef' pc_c,
      expr_to_pc Γ ec = Some pc_c ->
      fold_alts_p f (Φ ∧ pc_c) Γ et alts et' -> fold_alts_p f (Φ ∧ ¬ pc_c) Γ ef alts ef' ->
      fold_alts_p f Φ Γ (EIf ec et ef) alts (EIf ec et' ef')
  | FoldAltsP_IfFail : forall f Φ Γ ec et ef alts,
      expr_to_pc Γ ec = None -> fold_alts_p f Φ Γ (EIf ec et ef) alts (EBot BUndefined)
  | FoldAltsP_Con : forall f Φ Γ e d ea xs ep alts er,
      decompose_con_app e = Some (d, ea) -> find_alt d alts = Some (xs, ep) ->
      eval_p f Φ (extend_env_multi Γ xs ea Γ) ep er -> fold_alts_p f Φ Γ e alts er
  | FoldAltsP_Bot : forall f Φ Γ b alts, fold_alts_p f Φ Γ (EBot b) alts (EBot b)
  | FoldAltsP_GroundFormula : forall f Φ Γ e pc alts r,
      expr_to_pc Γ e = Some pc -> pc_has_var pc = false ->
      fold_alts_p f Φ Γ (ECon (truth_constructor (pc_ground_value pc))) alts r ->
      fold_alts_p f Φ Γ e alts r
  | FoldAltsP_SymbolicFormula : forall f Φ Γ e pc alts r1 r2,
      expr_to_pc Γ e = Some pc -> pc_has_var pc = true -> pc_arities_ok pc = true ->
      fold_alts_p f (Φ ∧ pc) Γ (ECon dcon_true) alts r1 ->
      fold_alts_p f (Φ ∧ ¬ pc) Γ (ECon dcon_false) alts r2 ->
      fold_alts_p f Φ Γ e alts (EIf e r1 r2)
  | FoldAltsP_Otherwise : forall f Φ Γ e alts,
      expr_to_pc Γ e = None ->
      is_if (fst (unspool_app e [])) = false ->
      (match decompose_con_app e with
       | Some (d, _) => find_alt d alts = None
       | None => True
       end) ->
      is_bot e = false ->
      fold_alts_p f Φ Γ e alts (EBot BUndefined).

Definition proposed_soundness : Prop :=
  forall Φ Γs Γc σ S e_sym e_con v_sym,
    σ ⊨ Φ ->
    contains_env σ S Γs Γc ->
    contains σ S e_sym e_con ->
    concore_expr e_con ->
    closed_program Γc e_con ->
    eval_p Inf Φ Γs e_sym v_sym ->
    exists v_con, eval_p Inf pc_true Γc e_con v_con /\ contains σ S v_sym v_con.

End ProposedCalculus.

Definition negate_cast (e : @expr model_sorts) (γ : coercion) : @expr model_sorts :=
  EApp (@EPrimOp model_sorts PNot) e.

Lemma app_mentions_right : forall (f a : @expr model_sorts),
  mentions_out_of_fuel a = true -> mentions_out_of_fuel (EApp f a) = true.
Proof. intros f a H. simpl. rewrite H. apply orb_true_r. Qed.

Definition negate_solver : @SymCoreSolver model_sorts :=
  Build_SymCoreSolver model_sat (@PCLit model_sorts true) eq_refl model_reduce_prim
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

Lemma model_prim_value_not : forall l : @lit model_sorts,
  prim_value op_not (l :: nil) = lit_true <-> l <> lit_true.
Proof. intros l. destruct l; simpl; split; congruence. Qed.

Definition a_coercion : coercion := MkCoercion (TyCon tt) (TyCon tt) RoleRepresentational.

Definition guard_branch : @expr model_sorts := EIf (EVar "x") (@ELit model_sorts true) (@ELit model_sorts false).

Definition true_false_alts : list (@alt model_sorts) :=
  Alt "True" nil (@ELit model_sorts false) :: Alt "False" nil (@ELit model_sorts true) :: nil.

Definition symbolic_program : @expr model_sorts :=
  ECase (ECast guard_branch a_coercion) true_false_alts.

Definition concrete_program : @expr model_sorts :=
  ECase (ECast (@ELit model_sorts true) a_coercion) true_false_alts.

Definition only_x : symvars := fun v => if string_dec v "x" then true else false.
Definition all_true : @valuation model_sorts := fun _ => true.

Definition proposed_eval := @eval_p model_sorts negate_solver "True" "False".
Definition proposed_fold := @fold_alts_p model_sorts negate_solver "True" "False".

Lemma symbolic_run_gives_undefined :
  proposed_eval Inf (@PCLit model_sorts true) · symbolic_program (EBot BUndefined).
Proof.
  unfold proposed_eval, symbolic_program.
  apply (EvalP_Case _ _ Unlimited (@PCLit model_sorts true) · _ _
           (EApp (@EPrimOp model_sorts PNot) guard_branch)).
  - change (EApp (@EPrimOp model_sorts PNot) guard_branch)
      with (@cast_expr model_sorts negate_solver guard_branch a_coercion).
    apply EvalP_Cast. unfold guard_branch.
    eapply EvalP_If; [apply EvalP_SymVar; reflexivity | reflexivity | apply EvalP_Lit | apply EvalP_Lit].
  - apply FoldAltsP_Otherwise; reflexivity || exact I.
Qed.

Lemma symbolic_scrutinee_has_no_formula :
  @expr_to_pc model_sorts · (EApp (@EPrimOp model_sorts PNot) guard_branch) = None.
Proof. reflexivity. Qed.

Lemma concrete_scrutinee_is_ground_formula :
  @expr_to_pc model_sorts · (EApp (@EPrimOp model_sorts PNot) (@ELit model_sorts true)) = Some (@PCPrim model_sorts PNot (@PCLit model_sorts true :: nil))
  /\ pc_has_var (@PCPrim model_sorts PNot (@PCLit model_sorts true :: nil)) = false
  /\ truth_constructor "True" "False" (pc_ground_value (@PCPrim model_sorts PNot (@PCLit model_sorts true :: nil))) = "False".
Proof. repeat split. Qed.

Ltac drop_prune :=
  match goal with
  | [ H : sat _ = false |- _ ] => exfalso; change (true = false) in H; discriminate H
  end.

Lemma concrete_run_gives_true : forall v,
  proposed_eval Inf (@PCLit model_sorts true) · concrete_program v -> v = @ELit model_sorts true.
Proof.
  intros v Hrun. unfold proposed_eval, concrete_program in Hrun.
  inversion Hrun; subst; try drop_prune; try no_con_head.
  match goal with
  | [ Hs : eval_p _ _ (dec _) _ _ _ _, Hf : fold_alts_p _ _ _ _ _ _ _ _ |- _ ] =>
      rename Hs into Hscrut; rename Hf into Hfold
  end.
  simpl in Hscrut.
  inversion Hscrut; subst; try drop_prune; try no_con_head.
  match goal with
  | [ Hl : eval_p _ _ _ _ _ (ELit _) _ |- _ ] => rename Hl into Hlit
  end.
  inversion Hlit; subst; try drop_prune; try no_con_head.
  simpl in Hfold. unfold negate_cast in Hfold.
  inversion Hfold as [ | | | | ? ? ? ? pc ? ? Hpc Hground Hinner | ? ? ? ? pc ? ? ? Hpc Hvar | ];
    subst; try discriminate;
    simpl in Hpc; injection Hpc as Hpc; subst pc; [| discriminate Hvar].
  inversion Hinner as [ | | ? ? ? ? d ea xs ep ? ? Hdec Hfind Hbody | | | | ];
    subst; try discriminate.
  compute in Hdec. injection Hdec as Hd Hea. subst d ea.
  compute in Hfind. injection Hfind as Hxs Hep. subst xs ep.
  inversion Hbody; subst; try drop_prune; try no_con_head; reflexivity.
Qed.

Lemma undefined_does_not_contain_true :
  ~ @contains model_sorts all_true only_x (EBot BUndefined) (@ELit model_sorts true).
Proof.
  intros H. inversion H; subst.
  match goal with [ Hun : unspool_app _ _ = _ |- _ ] => simpl in Hun; discriminate Hun end.
Qed.

Lemma symbolic_contains_concrete :
  @contains model_sorts all_true only_x symbolic_program concrete_program.
Proof.
  apply Cont_Case.
  - apply Cont_Cast. apply Cont_If_True; [| apply Cont_Lit].
    exists (PCVar "x"). split; [| reflexivity].
    intros Γ Hfree. simpl. rewrite (Hfree "x" eq_refl). reflexivity.
  - repeat constructor.
Qed.

Theorem proposed_design_breaks_soundness :
  @SymFCCostLaws model_sorts negate_solver
  /\ (forall l : @lit model_sorts, prim_value op_not (l :: nil) = lit_true <-> l <> lit_true)
  /\ ~ @proposed_soundness model_sorts negate_solver "True" "False".
Proof.
  split; [exact negate_cost_laws |]. split; [exact model_prim_value_not |].
  intros Hsound.
  destruct (Hsound (@PCLit model_sorts true) · · all_true only_x symbolic_program concrete_program
              (EBot BUndefined)) as [v [Hrun Hcont]].
  - reflexivity.
  - apply Cont_Env_Empty.
  - exact symbolic_contains_concrete.
  - repeat constructor.
  - split; [apply Scoped_Env_Empty | repeat constructor].
  - exact symbolic_run_gives_undefined.
  - apply concrete_run_gives_true in Hrun. subst v.
    exact (undefined_does_not_contain_true Hcont).
Qed.

Print Assumptions proposed_design_breaks_soundness.
