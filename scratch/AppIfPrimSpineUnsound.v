From SymCoreTheory Require Import SymCore ConCore Model.
From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat.
Import ListNotations.

Definition is_con (e : expr) : bool :=
  match e with
  | ECon _ => true
  | _ => false
  end.

Fixpoint has_con_arg (e : expr) : bool :=
  match e with
  | EApp f a => is_con a || has_con_arg f
  | _ => false
  end.

Definition result_con : dcon := "Result"%string.

Definition answer_con_arg (e : expr) : expr :=
  if has_con_arg e then ECon result_con else e.

Fixpoint answer_leaves (e : expr) : expr :=
  match e with
  | EIf c t f => EIf c (answer_leaves t) (answer_leaves f)
  | _ => answer_con_arg e
  end.

Definition con_reduce_prim (p : model_primop) (args : list expr) : expr :=
  answer_leaves (model_reduce_prim p args).

Definition con_solver : SymCoreSolver :=
  Build_SymCoreSolver
    model_sat (PCLit true) eq_refl con_reduce_prim
    erase_cast keep_coercion keep_type.

Lemma answer_leaves_not_if : forall e, is_if e = false -> answer_leaves e = answer_con_arg e.
Proof. intros e H. destruct e; simpl in *; try reflexivity. discriminate. Qed.

Lemma expr_to_pc_no_con_arg : forall Γ e pc,
  expr_to_pc Γ e = Some pc -> has_con_arg e = false.
Proof.
  intros Γ e. induction e; intros pc H; simpl in *; try reflexivity.
  destruct (expr_to_pc Γ e1) as [[| | p args]|] eqn:E1; try discriminate.
  destruct (expr_to_pc Γ e2) as [pca|] eqn:E2; try discriminate.
  rewrite (IHe1 _ eq_refl).
  destruct e2; simpl in E2 |- *; try reflexivity. discriminate.
Qed.

Lemma answer_leaves_of_pc : forall Γ e pc,
  expr_to_pc Γ e = Some pc -> answer_leaves e = e.
Proof.
  intros Γ e pc H.
  assert (Hif : is_if e = false) by (destruct e; simpl in *; try reflexivity; discriminate).
  rewrite (answer_leaves_not_if e Hif). unfold answer_con_arg.
  rewrite (expr_to_pc_no_con_arg Γ e pc H). reflexivity.
Qed.

Lemma answer_leaves_of_denote : forall σ S e l, denote σ S e l -> answer_leaves e = e.
Proof.
  intros σ S e l [pc [Hd _]].
  exact (answer_leaves_of_pc · e pc (Hd · (sym_free_env_empty S))).
Qed.

Lemma solvable_no_con_arg : forall Γ e, Solvable Γ e -> has_con_arg e = false.
Proof.
  intros Γ e H. induction H as [| | | f a Hop Hf IHf Ha IHa]; try reflexivity.
  simpl. rewrite IHf. destruct a; inversion Ha; reflexivity.
Qed.

Lemma answer_leaves_of_solvable : forall Γ e, Solvable Γ e -> answer_leaves e = e.
Proof.
  intros Γ e H.
  assert (Hif : is_if e = false) by (destruct H; reflexivity).
  rewrite (answer_leaves_not_if e Hif). unfold answer_con_arg.
  rewrite (solvable_no_con_arg Γ e H). reflexivity.
Qed.

Lemma contains_keeps_not_if : forall σ S es ec,
  contains σ S es ec -> is_if es = false -> is_if ec = false.
Proof.
  intros σ S es ec H Hif. destruct H; simpl in *; try reflexivity; try discriminate.
  all: match goal with
    | [ Ht : is_thunk ?e = true |- _ ] => destruct e; try discriminate Ht; reflexivity
    end.
Qed.

Lemma contains_keeps_is_con : forall σ S es ec,
  contains σ S es ec -> is_if es = false -> is_con ec = is_con es.
Proof.
  intros σ S es ec H Hif. destruct H; simpl in *; try reflexivity; try discriminate.
  all: match goal with
    | [ Ht : is_thunk ?e = true |- _ ] => destruct e; try discriminate Ht; reflexivity
    | [ Hu : unspool_app ?e _ = _, Hg : smt_ground ?e = false |- _ ] =>
        destruct (cont_denote_is_app _ _ _ Hu Hg) as [? [? ->]]; reflexivity
    end.
Qed.

Lemma contains_flat_con_arg : forall σ S es ec,
  contains σ S es ec -> flat es = true -> has_con_arg ec = has_con_arg es.
Proof.
  intros σ S es ec H. induction H; intros Hflat; simpl in *; try reflexivity; try discriminate.
  - apply andb_prop in Hflat as [Hf Ha].
    rewrite (contains_keeps_is_con σ S a_s a_c H0 (flat_not_if a_s Ha)), (IHcontains1 Hf).
    reflexivity.
  - destruct ec; try discriminate; reflexivity.
  - symmetry. destruct H2 as [pc [Hd _]].
    exact (expr_to_pc_no_con_arg · es pc (Hd · (sym_free_env_empty S))).
Qed.

Lemma answer_con_arg_contains : forall σ S L X,
  contains σ S L X -> flat L = true ->
  contains σ S (answer_con_arg L) (answer_con_arg X).
Proof.
  intros σ S L X Hc Hf. unfold answer_con_arg.
  rewrite (contains_flat_con_arg σ S L X Hc Hf).
  destruct (has_con_arg L); [apply Cont_Con | exact Hc].
Qed.

Lemma picks_answer_leaves : forall σ S T L,
  picks σ S T L -> picks σ S (answer_leaves T) (answer_con_arg L).
Proof.
  intros σ S T L H. induction H as [e Hif | c t f L Hm Hp IH | c t f L Hm Hp IH].
  - rewrite (answer_leaves_not_if e Hif). apply picks_leaf.
    unfold answer_con_arg. destruct (has_con_arg e); [reflexivity | exact Hif].
  - apply picks_then; assumption.
  - apply picks_else; assumption.
Qed.

Lemma flat_fold_leaf : forall L, flat L = true -> flat (fold_leaf L) = true.
Proof. intros L H. unfold fold_leaf. destruct (smt_ground L); [reflexivity | exact H]. Qed.

Instance con_reduce_prim_contains : @ReducePrimContains model_sorts con_solver.
Proof.
  intros σ S p args_s args_c HF.
  change (contains σ S (con_reduce_prim p args_s) (con_reduce_prim p args_c)).
  unfold con_reduce_prim, model_reduce_prim. rewrite <- (Forall2_length HF).
  destruct (Nat.eqb (length args_s) (model_arity p)) eqn:Hlen; [| apply Cont_Lit].
  apply Nat.eqb_eq in Hlen.
  assert (Hc : contains σ S (op_spine p args_s) (op_spine p args_c))
    by (apply contains_fold_left_app; [exact HF | apply Cont_PrimOp]).
  rewrite (lift_flat _ (contains_flat_instance σ S _ _ Hc)),
          (fold_leaves_not_if _ (op_spine_not_if p args_c)).
  destruct (lift_picks σ S _ _ Hc) as [L [Hp [HcL HfL]]].
  rewrite (answer_leaves_not_if _ (fold_leaf_not_if _ (op_spine_not_if p args_c))).
  apply (picks_contains σ S _ (answer_con_arg (fold_leaf L)));
    [apply picks_answer_leaves; apply picks_fold_leaves; exact Hp |].
  apply answer_con_arg_contains; [| exact (flat_fold_leaf L HfL)].
  apply (leaf_contains σ S p L); [| exact HcL | exact HfL].
  rewrite <- Hlen. exact (picks_leaves σ S _ _ _ Hp (leaves_lift_spine p args_s)).
Qed.

Instance con_reduce_prim_denote : @ReducePrimDenote model_sorts con_solver.
Proof.
  intros σ S p args ls HF.
  pose proof (@model_reduce_prim_denote σ S p args ls HF) as H.
  change (denote σ S (model_reduce_prim p args) (prim_value p ls)) in H.
  change (denote σ S (con_reduce_prim p args) (prim_value p ls)).
  unfold con_reduce_prim. rewrite (answer_leaves_of_denote σ S _ _ H). exact H.
Qed.

Instance con_reduce_prim_ground_value : @ReducePrimGroundValue model_sorts con_solver.
Proof.
  intros p args H.
  change (smt_ground (con_reduce_prim p args) = true) in H.
  change (exists l, con_reduce_prim p args = ELit l).
  unfold con_reduce_prim in *.
  destruct (is_if (model_reduce_prim p args)) eqn:Hif.
  - destruct (model_reduce_prim p args); simpl in Hif, H; discriminate.
  - rewrite (answer_leaves_not_if _ Hif) in *. unfold answer_con_arg in *.
    destruct (has_con_arg (model_reduce_prim p args)); [discriminate H |].
    exact (@model_reduce_prim_ground_value p args H).
Qed.

Instance con_reduce_prim_saturated : @ReducePrimSaturated model_sorts con_solver.
Proof.
  intros p args p0 args0 H.
  change (unspool_app (con_reduce_prim p args) nil = (EPrimOp p0, args0)) in H.
  unfold con_reduce_prim in H.
  destruct (is_if (model_reduce_prim p args)) eqn:Hif.
  - destruct (model_reduce_prim p args); simpl in Hif, H; discriminate.
  - rewrite (answer_leaves_not_if _ Hif) in H. unfold answer_con_arg in H.
    destruct (has_con_arg (model_reduce_prim p args)); [discriminate H |].
    exact (@model_reduce_prim_saturated p args p0 args0 H).
Qed.

Instance con_reduce_prim_solvable : @ReducePrimSolvable model_sorts con_solver.
Proof.
  intros Γ p args HF.
  pose proof (@model_reduce_prim_solvable Γ p args HF) as H.
  change (Solvable Γ (model_reduce_prim p args)) in H.
  change (Solvable Γ (con_reduce_prim p args)).
  unfold con_reduce_prim. rewrite (answer_leaves_of_solvable Γ _ H). exact H.
Qed.

Instance con_reduce_prim_concore : @ReducePrimConcore model_sorts con_solver.
Proof.
  intros p args HF.
  pose proof (@model_reduce_prim_concore p args HF) as H.
  change (concore_expr (model_reduce_prim p args)) in H.
  change (concore_expr (con_reduce_prim p args)).
  unfold con_reduce_prim.
  rewrite (answer_leaves_not_if _ (concore_not_if _ H)). unfold answer_con_arg.
  destruct (has_con_arg (model_reduce_prim p args)); [apply Con_Con | exact H].
Qed.

Instance con_reduce_prim_ite_contains : @ReducePrimIteContains model_sorts con_solver.
Proof.
  intros σ S ec et ef pt pf l Ht Hf Hc.
  pose proof (@model_reduce_prim_ite_contains σ S ec et ef pt pf l Ht Hf Hc) as H.
  change (contains σ S (model_reduce_prim op_ite (ec :: et :: ef :: nil)) (ELit l)) in H.
  change (contains σ S (con_reduce_prim op_ite (ec :: et :: ef :: nil)) (ELit l)).
  destruct (contains_if_inv σ S ec et ef (ELit l) Hc) as [[[pc [Hdc _]] _] | [[pc [Hdc _]] _]];
  assert (Hden : denote σ S (model_reduce_prim op_ite (ec :: et :: ef :: nil))
                   (prim_value op_ite (pc_value σ pc :: pc_value σ pt :: pc_value σ pf :: nil)))
    by (apply (@model_reduce_prim_denote σ S op_ite);
        apply Forall2_cons; [exists pc; split; [exact Hdc | reflexivity] |];
        apply Forall2_cons; [exists pt; split; [exact Ht | reflexivity] |];
        apply Forall2_cons; [exists pf; split; [exact Hf | reflexivity] |];
        apply Forall2_nil);
  unfold con_reduce_prim; rewrite (answer_leaves_of_denote σ S _ _ Hden); exact H.
Qed.

Instance con_laws : @ConCoreLaws model_sorts con_solver.
Proof.
  constructor.
  - exact con_reduce_prim_solvable.
  - exact con_reduce_prim_saturated.
  - exact con_reduce_prim_concore.
  - exact model_cast_expr_concore.
  - exact model_models_sat.
  - exact model_prim_value_and.
  - exact con_reduce_prim_contains.
  - exact con_reduce_prim_denote.
  - exact con_reduce_prim_ground_value.
  - exact con_reduce_prim_ite_contains.
  - exact model_cast_expr_contains.
  - exact model_subst_coerc_contains_env.
  - exact model_subst_type_contains_env.
Qed.

(* The whole-spine counterexample. Rule App-If once pushed ONE argument into
   the arms of a branch, and Rule App-Spine then applied the resulting
   branch to the next argument. Under that rule the symbolic program below
   had a value: (not D) reduced by Rule App-Prim to the constructor Result,
   and the branch of two Result constructors then took true by Rule Con.
   The concrete program (not D) true has no value, because not takes one
   argument and gets two. OldSymbolicValue states that the symbolic program
   has a value, and app_if_breaks_soundness shows that this refutes
   soundness. Rule App-If now pushes the whole spine into the arms, so the
   arms are (not D true), which is as stuck as the concrete program:
   symbolic_program_has_no_value. *)

Definition guard_var : var := "x"%string.
Definition branch_operator : expr := EIf (EVar guard_var) (EPrimOp PNot) (EPrimOp PNot).
Definition field_con : expr := ECon "D"%string.
Definition symbolic_program : expr := EApp (EApp branch_operator field_con) (ELit true).
Definition concrete_program : expr := EApp (EApp (EPrimOp PNot) field_con) (ELit true).
Definition branch_symvars : symvars := fun y => String.eqb y guard_var.
Definition branch_model : valuation := fun _ => true.

Definition OldSymbolicValue : Prop :=
  exists v, @eval model_sorts con_solver Inf (PCLit true) · symbolic_program v.

Lemma negation_of_field_is_a_constructor :
  con_reduce_prim PNot (field_con :: nil) = ECon result_con.
Proof. reflexivity. Qed.

Lemma over_applied_negation_is_stuck : forall Φ Γ v,
  ~ @eval model_sorts con_solver Inf Φ Γ concrete_program v.
Proof.
  intros Φ Γ v H. unfold concrete_program, field_con in H.
  inversion H; subst.
  - match goal with Hu : unspool_app _ _ = (ECon _, _) |- _ => simpl in Hu; discriminate Hu end.
  - match goal with Hc : Comp _ _ |- _ => inversion Hc as [| | | | ? ? Hh]; simpl in Hh; discriminate Hh end.
  - match goal with Hu : unspool_app _ _ = (EPrimOp _, _), Hl : length _ = _ |- _ =>
      simpl in Hu; injection Hu as <- <-; simpl in Hl; discriminate Hl end.
  - match goal with Hu : unspool_app _ _ = (EIf _ _ _, _) |- _ => simpl in Hu; discriminate Hu end.
  - match goal with Hs : sat _ = false |- _ => discriminate Hs end.
Qed.

Lemma concrete_program_is_stuck :
  forall v, ~ @eval model_sorts con_solver Inf (PCLit true) · concrete_program v.
Proof. intros v. apply over_applied_negation_is_stuck. Qed.

Lemma symbolic_program_contains_concrete_program :
  contains branch_model branch_symvars symbolic_program concrete_program.
Proof.
  apply Cont_App; [apply Cont_App; [| apply Cont_Con] | apply Cont_Lit].
  apply Cont_If_True; [| apply Cont_PrimOp].
  exists (PCVar guard_var). split; [| reflexivity].
  intros Γ Hfree. simpl. rewrite (Hfree guard_var eq_refl). reflexivity.
Qed.

Lemma concrete_program_concore : concore_expr concrete_program.
Proof. repeat constructor. Qed.

Theorem app_if_breaks_soundness :
  OldSymbolicValue ->
  ~ (forall Φ Γs Γc σ S e_sym e_con v_sym,
       σ ⊨ Φ ->
       contains_env σ S Γs Γc ->
       contains σ S e_sym e_con ->
       concore_expr e_con ->
       @eval model_sorts con_solver Inf Φ Γs e_sym v_sym ->
       exists v_con,
         @eval model_sorts con_solver Inf (PCLit true) Γc e_con v_con /\
         contains σ S v_sym v_con).
Proof.
  intros [v_sym Hv] Hsound.
  assert (Hm : @models model_sorts branch_model (PCLit true)) by reflexivity.
  destruct (Hsound _ · · branch_model branch_symvars symbolic_program concrete_program
              v_sym Hm (Cont_Env_Empty _ _) symbolic_program_contains_concrete_program
              concrete_program_concore Hv) as [v_con [Hc _]].
  exact (concrete_program_is_stuck v_con Hc).
Qed.

Theorem symbolic_program_has_no_value : ~ OldSymbolicValue.
Proof.
  intros [v H]. unfold symbolic_program, branch_operator, field_con in H.
  inversion H; subst.
  - match goal with Hu : unspool_app _ _ = (ECon _, _) |- _ => simpl in Hu; discriminate Hu end.
  - match goal with Hc : Comp _ _ |- _ => inversion Hc as [| | | | ? ? Hh]; simpl in Hh; discriminate Hh end.
  - match goal with Hu : unspool_app _ _ = (EPrimOp _, _) |- _ => simpl in Hu; discriminate Hu end.
  - match goal with Hu : unspool_app _ _ = (EIf _ _ _, _) |- _ =>
      simpl in Hu; injection Hu as <- <- <- <- end.
    match goal with
    | [ Hi : eval _ _ _ (EIf _ _ _) _ |- _ ] => inversion Hi; subst
    end.
    + match goal with Hu : unspool_app _ _ = (ECon _, _) |- _ => simpl in Hu; discriminate Hu end.
    + match goal with
      | [ Ht : eval _ (PCLit true ∧ _) _ _ _ |- _ ] =>
          exact (over_applied_negation_is_stuck _ _ _ Ht)
      end.
    + match goal with Hs : sat _ = false |- _ => discriminate Hs end.
  - match goal with Hs : sat _ = false |- _ => discriminate Hs end.
Qed.

Print Assumptions app_if_breaks_soundness.
Print Assumptions symbolic_program_has_no_value.

(* The double-thunk counterexample. Under the one-argument Rule App-If, the
   program (if x then D else D) l1 l2 ran Rule Con twice on each arm: once
   for D l1 and once more for the result applied to l2. The second run
   wrapped the first field again, so the symbolic value held the field
   (·, (·, l1)) where the concrete value holds (·, l1). OldThunkInversion is
   the reading of contains that had no Cont_Thunk_Outer, and under it the
   double-thunk value does not contain the concrete value. Rule App-If now
   runs Rule Con once per arm, and double_thunk_regression shows the value
   it computes. *)

Section DoubleThunk.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.

Definition OldThunkInversion (σ : valuation) (S : symvars) : Prop :=
  forall Γs es ec,
    contains σ S (EThunk Γs es) ec ->
    exists Γc ec', ec = EThunk Γc ec' /\ contains_env σ S Γs Γc /\ contains σ S es ec'.

Definition double_thunk_program (x : var) (d : dcon) (l1 l2 : lit) : expr :=
  EApp (EApp (EIf (EVar x) (ECon d) (ECon d)) (ELit l1)) (ELit l2).

Definition double_thunk_concrete (d : dcon) (l1 l2 : lit) : expr :=
  EApp (EApp (ECon d) (ELit l1)) (ELit l2).

Definition double_thunk_con_value (d : dcon) (l1 l2 : lit) : expr :=
  EApp (EApp (ECon d) (EThunk · (ELit l1))) (EThunk · (ELit l2)).

Definition double_thunk_old_value (x : var) (d : dcon) (l1 l2 : lit) : expr :=
  EIf (EVar x)
    (EApp (EApp (ECon d) (EThunk · (EThunk · (ELit l1)))) (EThunk · (ELit l2)))
    (EApp (EApp (ECon d) (EThunk · (EThunk · (ELit l1)))) (EThunk · (ELit l2))).

Lemma double_thunk_concrete_value : forall d l1 l2,
  · ⊢ᶜ double_thunk_concrete d l1 l2 ⇓ᶜ double_thunk_con_value d l1 l2.
Proof.
  intros d l1 l2.
  exact (Eval_Con Unlimited pc_true · (double_thunk_concrete d l1 l2) d
           (ELit l1 :: ELit l2 :: nil) eq_refl).
Qed.

Lemma double_thunk_old_value_misses : forall σ S x d l1 l2,
  OldThunkInversion σ S ->
  ~ contains σ S (double_thunk_old_value x d l1 l2) (double_thunk_con_value d l1 l2).
Proof.
  intros σ S x d l1 l2 Hold Hc.
  assert (Harm : contains σ S
            (EApp (EApp (ECon d) (EThunk · (EThunk · (ELit l1)))) (EThunk · (ELit l2)))
            (double_thunk_con_value d l1 l2))
    by (inversion Hc; subst; assumption).
  inversion Harm as [| | | | | | | | f_s a_s f_c a_c Hf Ha | | | | | | | | ]; subst.
  inversion Hf as [| | | | | | | | f_s' a_s' f_c' a_c' Hf' Ha' | | | | | | | | ]; subst.
  destruct (Hold · _ _ Ha') as [Γc [ec' [Heq [_ Hinner]]]].
  injection Heq as <- <-.
  inversion Hinner; discriminate.
Qed.

Theorem double_thunk_regression : forall Φ σ S x d l1 l2,
  models_cond σ S (EVar x) ->
  exists v_sym,
    Φ ; · ⊢ double_thunk_program x d l1 l2 ⇓ v_sym
    /\ · ⊢ᶜ double_thunk_concrete d l1 l2 ⇓ᶜ double_thunk_con_value d l1 l2
    /\ contains σ S v_sym (double_thunk_con_value d l1 l2).
Proof.
  intros Φ σ S x d l1 l2 Hx.
  exists (EIf (EVar x) (double_thunk_con_value d l1 l2) (double_thunk_con_value d l1 l2)).
  split; [| split; [apply double_thunk_concrete_value |]].
  - eapply Eval_AppIf; [reflexivity |].
    eapply Eval_If with (pc_c := PCVar x).
    + apply Eval_SymVar. reflexivity.
    + reflexivity.
    + exact (Eval_Con Unlimited _ · (double_thunk_concrete d l1 l2) d (ELit l1 :: ELit l2 :: nil) eq_refl).
    + exact (Eval_Con Unlimited _ · (double_thunk_concrete d l1 l2) d (ELit l1 :: ELit l2 :: nil) eq_refl).
  - apply Cont_If_True; [exact Hx |].
    repeat apply Cont_App; try apply Cont_Con;
      apply Cont_Thunk; [apply Cont_Env_Empty | apply Cont_Lit | apply Cont_Env_Empty | apply Cont_Lit].
Qed.

End DoubleThunk.

Print Assumptions double_thunk_regression.
