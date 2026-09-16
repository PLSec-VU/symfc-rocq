From SymCoreTheory Require Export SymCore.Syntax.
From Stdlib Require Import Strings.String Lists.List ZArith.ZArith Bool.Bool Arith.PeanoNat Lia.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Section SymCore.
Context {sorts : SymCoreSorts}.

(** Convert a solvable expression into a path condition formula *)
Fixpoint expr_to_pc (Γ : environment) (e : expr) : option path_condition :=
  match e with
  | EVar x =>
      match lookup_env Γ x with
      | None => Some (PCVar x)
      | Some _ => None
      end
  | ELit l => Some (PCLit l)
  | EPrimOp p => Some (PCPrim p [])
  | EApp f a =>
      match expr_to_pc Γ f, expr_to_pc Γ a with
      | Some (PCPrim p args), Some pca => Some (PCPrim p (args ++ [pca]))
      | _, _ => None
      end
  | _ => None
  end.

(** ========================================================================= *)
(** Application Spine & Primitive / Cast Helpers (§3.2)                       *)
(** ========================================================================= *)

(** Unspool application spine into head expression and arguments: e.g. D e1 ... en *)
Fixpoint unspool_app (e : expr) (args : list expr) : (expr * list expr) :=
  match e with
  | EApp f a => unspool_app f (a :: args)
  | _ => (e, args)
  end.

Class SymCoreSolver : Type := {

(** SMT satisfiability oracle SAT(Φ) (Fig. 3, Rule Prune); a parameter from the SMT solver *)
sat : path_condition -> bool;

(** Canonical trivially satisfiable path condition (Top / True) *)
pc_true : path_condition;
sat_pc_true : sat pc_true = true;

(** Theory-specific primitive reduction: reduce-prim(⊗ e⃗) (Fig. 3, Rule App-Prim); a parameter from the SMT solver *)
reduce_prim : primop -> list expr -> expr;

(** Cast simplification: cast(e, γ) (Fig. 3, Rule Cast) *)
cast_expr : expr -> coercion -> expr;

(** Type and Coercion substitution under environment Γ (Fig. 3, Rules Type and Coercion) *)
subst_coerc : environment -> coercion -> coercion;
subst_type : environment -> type_fc -> type_fc
}.

Context {solver : SymCoreSolver}.

(** ========================================================================= *)
(** Solvable and Computation Definitions in Prop (§3.2)                       *)
(** ========================================================================= *)

(** Helper: checks if the head of an expression is a primitive operation *)
Fixpoint is_op_app (e : expr) : bool :=
  match e with
  | EPrimOp _ => true
  | EApp f _ => is_op_app f
  | _ => false
  end.

(** Helper: checks if the head of an application spine is a data constructor *)
Fixpoint is_con_app (e : expr) : bool :=
  match e with
  | ECon _ => true
  | EApp f _ => is_con_app f
  | _ => false
  end.

(** A spine has one head, so it cannot be headed by both a primitive
    operation and a data constructor *)
Lemma op_app_not_con_app : forall e,
  is_op_app e = true -> is_con_app e = false.
Proof.
  induction e; intros H; simpl in H; simpl; try discriminate; try reflexivity.
  apply IHe1. exact H.
Qed.

(** Unspooling to a constructor head is exactly is_con_app *)
Lemma unspool_is_con_app : forall e args d args0,
  unspool_app e args = (ECon d, args0) ->
  is_con_app e = true.
Proof.
  induction e; intros args d0 args0 H; simpl in H; try discriminate.
  - reflexivity.
  - simpl. eapply IHe1. exact H.
Qed.

Inductive Solvable (Γ : environment) : expr -> Prop :=
  | Solvable_Lit : forall l,
      Solvable Γ (ELit l)
  | Solvable_Var : forall x,
      lookup_env Γ x = None ->
      Solvable Γ (EVar x)
  | Solvable_PrimOp : forall p,
      Solvable Γ (EPrimOp p)
  | Solvable_AppPrim : forall f a,
      is_op_app (EApp f a) = true ->
      Solvable Γ f ->
      Solvable Γ a ->
      Solvable Γ (EApp f a).

Fixpoint spine_head (e : expr) : expr :=
  match e with
  | EApp f _ => spine_head f
  | _ => e
  end.

Definition has_whole_spine_rule (e : expr) : bool :=
  match e with
  | ECon _ | EPrimOp _ | EIf _ _ _ => true
  | _ => false
  end.

Definition is_lam (e : expr) : bool :=
  match e with
  | ELam _ _ => true
  | _ => false
  end.

Inductive Comp (Γ : environment) : expr -> Prop :=
  | Comp_Var : forall x,
      lookup_env Γ x <> None ->
      Comp Γ (EVar x)
  | Comp_Lam : forall x body,
      Comp Γ (ELam x body)
  | Comp_Case : forall es alts,
      Comp Γ (ECase es alts)
  | Comp_Thunk : forall Γ' e,
      is_lam e = false ->
      Comp Γ (EThunk Γ' e)
  | Comp_App : forall ef ea,
      has_whole_spine_rule (spine_head (EApp ef ea)) = false ->
      Comp Γ (EApp ef ea).

End SymCore.

(** Closes the Eval_Con case of an inversion on an expression
    whose spine head is visibly not a data constructor. *)
Ltac no_con_head :=
  match goal with
  | [ H : unspool_app _ _ = (ECon _, _) |- _ ] => simpl in H; discriminate H
  end.

Section SymCore.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.

(** ------------------------------------------------------------------------- *)
(** expr_to_pc Reads a Formula Off the Syntax Alone                           *)
(** ------------------------------------------------------------------------- *)

(**
  An environment can only make expr_to_pc FAIL, by capturing a variable that
  would otherwise be symbolic. It can never change which formula comes out.
  So a Some-result is a property of the expression alone, and the empty
  environment is the most permissive environment.
*)
Lemma expr_to_pc_functional : forall e Γ1 Γ2 pc1 pc2,
  expr_to_pc Γ1 e = Some pc1 -> expr_to_pc Γ2 e = Some pc2 -> pc1 = pc2.
Proof.
  induction e; intros Γ1 Γ2 pc1 pc2 H1 H2; simpl in *;
    try discriminate; try (injection H1 as ?; injection H2 as ?; congruence).
  - destruct (lookup_env Γ1 v); [discriminate|].
    destruct (lookup_env Γ2 v); [discriminate|].
    injection H1 as ?; injection H2 as ?; congruence.
  - destruct (expr_to_pc Γ1 e1) as [q1|] eqn:E1; [|discriminate].
    destruct (expr_to_pc Γ2 e1) as [q1'|] eqn:E1'; [|discriminate].
    destruct (expr_to_pc Γ1 e2) as [q2|] eqn:E2; [|destruct q1; discriminate].
    destruct (expr_to_pc Γ2 e2) as [q2'|] eqn:E2'; [|destruct q1'; discriminate].
    assert (q1 = q1') by eauto. assert (q2 = q2') by eauto. subst.
    destruct q1'; try discriminate.
    injection H1 as ?; injection H2 as ?; congruence.
Qed.

Lemma expr_to_pc_op_app : forall e Γ pc,
  is_op_app e = true -> expr_to_pc Γ e = Some pc ->
  exists p args, pc = PCPrim p args.
Proof.
  induction e; intros Γ pc Hop Hpc; simpl in *; try discriminate.
  - injection Hpc as ?; subst. eauto.
  - destruct (expr_to_pc Γ e1) as [q1|] eqn:E1; [|discriminate].
    destruct (expr_to_pc Γ e2) as [q2|] eqn:E2; [|destruct q1; discriminate].
    destruct q1; try discriminate. injection Hpc as ?; subst. eauto.
Qed.

(** ========================================================================= *)
(** Decision Functions (Fixpoints) for Solvable and Computations              *)
(** ========================================================================= *)

(** Solvable is decidable *)
Fixpoint solvable_dec (Γ : environment) (e : expr) : {Solvable Γ e} + {~ Solvable Γ e}.
Proof.
  destruct e.
  - destruct (lookup_env Γ v) eqn:Heq.
    + right. intros H. inversion H. rewrite Heq in H1. discriminate.
    + left. apply Solvable_Var. assumption.
  - left. apply Solvable_Lit.
  - left. apply Solvable_PrimOp.
  - right. intros H. inversion H.
  - destruct (is_op_app (EApp e1 e2)) eqn:Hop.
    + destruct (solvable_dec Γ e1) as [S1 | N1].
      * destruct (solvable_dec Γ e2) as [S2 | N2].
        -- left. apply Solvable_AppPrim; auto.
        -- right. intros H. inversion H; subst. apply N2; auto.
      * right. intros H. inversion H; subst. apply N1; auto.
    + right. intros H. inversion H; subst. congruence.
  - right. intros H. inversion H.
  - right. intros H. inversion H.
  - right. intros H. inversion H.
  - right. intros H. inversion H.
  - right. intros H. inversion H.
  - right. intros H. inversion H.
  - right. intros H. inversion H.
  - right. intros H. inversion H.
Defined.

(** Helper inversion lemmas on Solvable *)
Lemma solvable_not_cast : forall Γ e γ, ~ Solvable Γ (ECast e γ).
Proof. intros Γ e γ H. inversion H. Qed.

(** A solvable term is an SMT term, so the head of its spine is never a data
    constructor *)
Lemma solvable_not_con_app : forall Γ e,
  Solvable Γ e -> is_con_app e = false.
Proof.
  intros Γ e H. induction H as [l | x Hx | p | f a Hop Hf IHf Ha IHa]; simpl;
    try reflexivity.
  exact IHf.
Qed.

Lemma solvable_unspool_not_if : forall Γ e args ec et ef args0,
  Solvable Γ e -> unspool_app e args = (EIf ec et ef, args0) -> False.
Proof.
  intros Γ e args ec et ef args0 Hs. revert args.
  induction Hs as [l | x Hx | p | f a Hop Hf IHf Ha IHa]; intros args H;
    simpl in H; try discriminate.
  exact (IHf _ H).
Qed.

Lemma spine_head_without_whole_rule : forall e,
  has_whole_spine_rule (spine_head e) = false ->
  is_con_app e = false /\ is_op_app e = false.
Proof.
  induction e; simpl; intros H; try discriminate; try (split; reflexivity).
  exact (IHe1 H).
Qed.

Lemma fst_unspool_app : forall e args, fst (unspool_app e args) = spine_head e.
Proof. induction e; intros args; simpl; try reflexivity. apply IHe1. Qed.

Lemma comp_not_con_app : forall Γ e, Comp Γ e -> is_con_app e = false.
Proof.
  intros Γ e Hc. destruct Hc as [| | | | ef ea Hhead]; try reflexivity.
  exact (proj1 (spine_head_without_whole_rule _ Hhead)).
Qed.

Lemma comp_not_op_app : forall Γ e, Comp Γ e -> is_op_app e = false.
Proof.
  intros Γ e Hc. destruct Hc as [| | | | ef ea Hhead]; try reflexivity.
  exact (proj2 (spine_head_without_whole_rule _ Hhead)).
Qed.

Lemma comp_not_solvable : forall Γ e, Comp Γ e -> ~ Solvable Γ e.
Proof.
  intros Γ e Hc Hs.
  pose proof (comp_not_op_app Γ e Hc) as Hop.
  destruct Hc; inversion Hs; subst; congruence.
Qed.

(** Helper: path-condition convertible primitive application is an operator application *)
Lemma expr_to_pc_prim_is_op_app : forall Γ e p args,
  expr_to_pc Γ e = Some (PCPrim p args) ->
  is_op_app e = true.
Proof.
  intros Γ e.
  induction e; intros p' args' H; simpl in *; try discriminate.
  - destruct (lookup_env Γ v); discriminate.
  - reflexivity.
  - destruct (expr_to_pc Γ e1) eqn:He1; try discriminate.
    destruct p; try discriminate.
    destruct (expr_to_pc Γ e2) eqn:He2; try discriminate.
    inversion H; subst.
    eapply (IHe1 p' l). reflexivity.
Qed.

(** Any expression that successfully converts to a path condition is Solvable *)
Lemma expr_to_pc_solvable : forall Γ e pc,
  expr_to_pc Γ e = Some pc -> Solvable Γ e.
Proof.
  intros Γ e.
  induction e; intros pc Hpc; simpl in Hpc; try discriminate.
  - (* EVar *)
    destruct (lookup_env Γ v) eqn:Heq; [discriminate |].
    inversion Hpc; subst.
    apply Solvable_Var. assumption.
  - (* ELit *)
    inversion Hpc; subst.
    apply Solvable_Lit.
  - (* EPrimOp *)
    inversion Hpc; subst.
    apply Solvable_PrimOp.
  - (* EApp *)
    destruct (expr_to_pc Γ e1) eqn:He1; try discriminate.
    destruct p as [vx | vl | op args]; try discriminate.
    destruct (expr_to_pc Γ e2) eqn:He2; try discriminate.
    inversion Hpc; subst.
    apply Solvable_AppPrim.
    + simpl. eapply (expr_to_pc_prim_is_op_app Γ e1 op args He1).
    + apply (IHe1 (PCPrim op args) eq_refl).
    + apply (IHe2 p eq_refl).
Qed.

(** Solvable is exactly expr_to_pc's domain: expr_to_pc_solvable above is one
    direction, and since only capture can make expr_to_pc fail, anything
    solvable in any environment has a formula in the empty environment. *)
Lemma solvable_expr_to_pc : forall Γ e,
  Solvable Γ e -> exists pc, expr_to_pc · e = Some pc.
Proof.
  intros Γ e H. induction H as [l | x Hx | p | f a Hop Hf IHf Ha IHa]; simpl.
  - eauto.
  - eauto.
  - eauto.
  - destruct IHf as [pcf Ef]. destruct IHa as [pca Ea]. simpl in Hop.
    destruct (expr_to_pc_op_app f · pcf Hop Ef) as [p [args Hpcf]]. subst.
    rewrite Ef, Ea. eauto.
Qed.

(** ========================================================================= *)
(** Pattern Matching and Branch Folding: fold-alts (§3.2)                    *)
(** ========================================================================= *)

(** Helper predicate identifying if-then-else expressions *)
Definition is_if (e : expr) : bool :=
  match e with
  | EIf _ _ _ => true
  | _ => false
  end.

(** Helper predicate identifying bottom values *)
Definition is_bot (e : expr) : bool :=
  match e with
  | EBot _ => true
  | _ => false
  end.

(** Helper predicate identifying casts *)
Definition is_cast (e : expr) : bool :=
  match e with
  | ECast _ _ => true
  | _ => false
  end.

Definition is_thunk (e : expr) : bool :=
  match e with
  | EThunk _ _ => true
  | _ => false
  end.

(** Lookup a matching constructor alternative in a branch list: find(D, a⃗) *)
Fixpoint find_alt (d : dcon) (alts : list alt) : option (list var * expr) :=
  match alts with
  | [] => None
  | Alt d' xs ep :: rest =>
      if string_dec d d' then Some (xs, ep) else find_alt d rest
  end.

(** Decompose constructor application into constructor name and argument list: D e⃗a *)
Definition decompose_con_app (e : expr) : option (dcon * list expr) :=
  match unspool_app e [] with
  | (ECon d, args) => Some (d, args)
  | _ => None
  end.

(** The head of a spine is the expression itself when the expression is not an
    application, so a spine whose head is not a branch is not a branch. *)
Lemma is_if_false_of_spine_head : forall e,
  is_if (fst (unspool_app e [])) = false -> is_if e = false.
Proof.
  intros e H. destruct e; simpl in H |- *; try reflexivity. discriminate H.
Qed.

(** Construct curried constructor application from constructor name and argument list *)
Definition make_con_app (d : dcon) (args : list expr) : expr :=
  fold_left EApp args (ECon d).

Definition delay (Γ : environment) (e : expr) : expr :=
  match e with
  | EThunk _ _ => e
  | _ => EThunk Γ e
  end.

Lemma delay_thunk : forall Γ e, is_thunk e = true -> delay Γ e = e.
Proof. intros Γ e H. destruct e; try discriminate H. reflexivity. Qed.

Lemma delay_not_thunk : forall Γ e, is_thunk e = false -> delay Γ e = EThunk Γ e.
Proof. intros Γ e H. destruct e; try discriminate H; reflexivity. Qed.

Lemma unspool_fold_left_app : forall args h acc,
  unspool_app (fold_left EApp args h) acc = unspool_app h (args ++ acc).
Proof.
  induction args as [| a tl IH]; intros h acc; simpl; [reflexivity |].
  rewrite IH. reflexivity.
Qed.

End SymCore.
