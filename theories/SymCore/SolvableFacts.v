From SymCoreTheory Require Export SymCore.Eval.
From Stdlib Require Import Strings.String Lists.List ZArith.ZArith Bool.Bool Arith.PeanoNat Lia.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Section SymCore.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.

(** ------------------------------------------------------------------------- *)
(** Free Variables and Well-Formed Environments                               *)
(** ------------------------------------------------------------------------- *)

(** Domain (bound variables) of an environment *)
Fixpoint dom_env (Γ : environment) : list var :=
  match Γ with
  | · => []
  | ExtendEnv x _ rest => x :: dom_env rest
  end.

(** ------------------------------------------------------------------------- *)
(** Solvable Results of Primitives (§3.2)                                     *)
(** ------------------------------------------------------------------------- *)

(**
  Primitive reduction produces a solvable expression WHEN ITS ARGUMENTS ARE
  THEMSELVES SOLVABLE (§3.2, SMT contract - Axiom 2).

  The hypothesis is essential and was missing. Solvable admits no EIf, so an
  unconditional version would say that reduce-prim of a *branching* argument
  is still a plain SMT term - i.e. that the theory solver silently erases the
  branch. Worse, it is stated for EVERY Γ, and Solvable_Var demands the
  variable be unbound in Γ, so an unconditional version would force the result
  to mention no variable at all: reduce-prim's range would be ground terms.
  unconditional_solvable_forces_constancy in NonVacuity/SoundnessInstances.v
  turns that into the
  collapse it is: with reduce_prim_contains, an unconditional version forces
  reduce_prim to be a CONSTANT function on literals as soon as any condition
  is resolvable (1+1 = 1+2).

  With the hypothesis, a primitive applied to plain SMT arguments still yields
  a plain SMT term, while a primitive applied to an argument that still
  branches is left free to distribute over that branch and return an EIf.
*)
Class ReducePrimSolvable : Prop :=
reduce_prim_solvable : forall Γ p args,
  Forall (Solvable Γ) args ->
  Solvable Γ (reduce_prim p args).

Context {reduce_prim_solvable_law : ReducePrimSolvable}.

(**
  SMT terms are always fully-formed application trees: an SMT solver has no
  notion of a "partially applied" or "over-applied" operator, so whenever
  reduce_prim's result unspools to an operator head, that operator is
  applied to exactly as many arguments as its arity demands (§3.1, SMT
  contract - Axiom 3). This is what makes over-application of an
  already-saturated primitive (Rule App-Prim never fires on it) get stuck
  rather than silently re-reducing with the wrong number of arguments.
*)
Class ReducePrimSaturated : Prop :=
reduce_prim_saturated : forall p args p0 args0,
  unspool_app (reduce_prim p args) [] = (EPrimOp p0, args0) ->
  length args0 = primop_arity p0.

Context {reduce_prim_saturated_law : ReducePrimSaturated}.

(** Unspooling an application spine preserves the operator head property *)
Lemma unspool_is_op_app : forall e args p args0,
  unspool_app e args = (EPrimOp p, args0) ->
  is_op_app e = true.
Proof.
  induction e; intros args op args0 H; simpl in *; try discriminate.
  - injection H as ? ?; subst. reflexivity.
  - apply IHe1 in H. exact H.
Qed.

(** Unspooling with an extra accumulator only ever appends to the argument
    list already found for the empty accumulator; the head is unchanged *)
Lemma unspool_app_shift : forall (e : expr) (L acc : list expr) (head : expr) (args : list expr),
  unspool_app e L = (head, args) ->
  unspool_app e (L ++ acc)%list = (head, (args ++ acc)%list).
Proof.
  induction e; intros L acc head args H; simpl in *;
  try (injection H as ? ?; subst; reflexivity).
  apply IHe1 with (L := e2 :: L). exact H.
Qed.

(** An operator-headed application spine always unspools to a primitive head *)
Lemma is_op_app_unspool : forall e,
  is_op_app e = true ->
  exists p args, unspool_app e [] = (EPrimOp p, args).
Proof.
  induction e; intros H; simpl in H; try discriminate.
  - exists p, []. reflexivity.
  - destruct (IHe1 H) as [p [args Heq]].
    apply (unspool_app_shift e1 [] [e2] (EPrimOp p) args) in Heq.
    simpl in Heq. exists p, (args ++ [e2])%list. exact Heq.
Qed.

(**
  A saturated (arity-matching) primitive-operator result can never itself be
  applied to a further argument: Rule App-Prim demands the combined spine's
  argument count match the operator's arity exactly (§3.1, arity), so one
  argument too many gets stuck, and no other rule can fire on a solvable
  operator application.
*)
(** Every argument of a solvable operator spine is itself solvable *)
Lemma solvable_spine_args : forall Γ e,
  Solvable Γ e ->
  forall L p args,
    Forall (Solvable Γ) L ->
    unspool_app e L = (EPrimOp p, args) ->
    Forall (Solvable Γ) args.
Proof.
  induction 1; intros L p0 args0 HL Hunspool; simpl in Hunspool;
    try (injection Hunspool as ? ?; subst; assumption);
    try discriminate.
  eapply IHSolvable1; [| exact Hunspool].
  constructor; assumption.
Qed.

(**
  Solvable terms reduce to solvable terms: a literal and a symbolic variable
  are already values, a bare operator is stuck, and an operator spine reduces
  by Rule App-Prim, whose arguments are solvable by solvable_spine_args and
  so reduce to solvable results - which is exactly the hypothesis the
  repaired reduce_prim_solvable needs.

  Written as a Fixpoint on the derivation rather than by `induction` because
  Rule App-Prim needs the statement for every argument of its
  Forall2 (eval (dec f) Φ Γ) args args', which Coq's auto-derived induction
  principle does not supply.

  Unlimited budget only, which is why the fuel comes in as k0 with a k0 = Inf
  premise instead of being left free. At Fin 0 Rule Out-Of-Fuel takes the
  solvable literal ELit l to EBot BOutOfFuel, and no rule of Solvable accepts
  a bottom. The premise is what lets the out-of-fuel case close by
  discriminate.
*)
Fixpoint solvable_eval_solvable (k0 : fuel) (Φ : path_condition) (Γ : environment) (e v : expr)
  (Heval : eval k0 Φ Γ e v) {struct Heval} :
  k0 = Inf -> sat Φ = true -> Solvable Γ e -> Solvable Γ v.
Proof.
  destruct Heval as
    [ k Φ Γ x Γ' e e' Hlookup Heval_x
    | k Φ Γ x Hnone
    | k Φ Γ l
    | k Φ Γ e d args Hunspool
    | k Φ Γ e γ e' Heval_e
    | k Φ Γ Γ' x eb ea eb' Heval_b
    | k Φ Γ ef ea ef' er Hcomp Heval_f Heval_app2
    | k Φ Γ b
    | k Φ Γ ef ea p args args' Hunspool Harity Hargs
    | k Φ Γ x e
    | k Φ Γ ef γ ea γ_a γ_r er Hdecomp Heval_pushed
    | k Φ Γ e1 e2 ec et ef args er Hunspool_if Heval_arms
    | k Φ Γ b ea
    | k Φ Γ es alts es' er Heval_es Hfold
    | k Φ Γ ec et ef ec' et' ef' pc_c Heval_c Hpc Heval_t Heval_f
    | k Φ Γ γ
    | k Φ Γ e Hunsat
    | k Φ Γ τ
    | k Φ Γ Γ' e e' Heval_t
    | Φ Γ e
    ]; intros Hk0 Hsat Hsolv; try (injection Hk0 as Hk0; subst k).
  - (* Eval_Var: a bound variable is not solvable *)
    inversion Hsolv; subst. rewrite Hlookup in H0. discriminate.
  - (* Eval_SymVar *) exact Hsolv.
  - (* Eval_Lit *) exact Hsolv.
  - (* Eval_Con: a solvable head is never a constructor *)
    exfalso. apply unspool_is_con_app in Hunspool.
    rewrite (solvable_not_con_app Γ e Hsolv) in Hunspool. discriminate.
  - (* Eval_Cast *) inversion Hsolv.
  - (* Eval_AppAbs: a closure is not solvable *)
    inversion Hsolv as [| | | f a Hop Hsf Hsa]; subst. inversion Hsf.
  - (* Eval_AppSpine: a solvable head is not a computation *)
    exfalso. apply (comp_not_solvable _ _ Hcomp).
    inversion Hsolv as [| | | f a Hop Hsf Hsa]; subst. exact Hsf.
  - (* Eval_Bot *) inversion Hsolv.
  - (* Eval_AppPrim *)
    assert (Hsargs : Forall (Solvable Γ) args)
      by (eapply solvable_spine_args; [exact Hsolv | constructor | exact Hunspool]).
    apply reduce_prim_solvable.
    clear Hunspool Harity Hsolv.
    induction Hargs as [| a a' args_tl args'_tl Ha Hargs_tl IH].
    + constructor.
    + inversion Hsargs as [| a0 tl0 Hsa Hstl]; subst.
      constructor.
      * exact (solvable_eval_solvable Inf Φ Γ a a' Ha eq_refl Hsat Hsa).
      * exact (IH Hstl).
  - (* Eval_Lam *) inversion Hsolv.
  - (* Eval_AppCast: a cast is not solvable *)
    inversion Hsolv as [| | | f a Hop Hsf Hsa]; subst. inversion Hsf.
  - (* Eval_AppIf: a branch is not solvable *)
    exfalso. exact (solvable_unspool_not_if _ _ _ _ _ _ _ Hsolv Hunspool_if).
  - (* Eval_AppBot: a bottom is not solvable *)
    inversion Hsolv as [| | | f a Hop Hsf Hsa]; subst. inversion Hsf.
  - (* Eval_Case *) inversion Hsolv.
  - (* Eval_If *) inversion Hsolv.
  - (* Eval_Coercion *) inversion Hsolv.
  - (* Eval_Prune *) rewrite Hsat in Hunsat. discriminate.
  - (* Eval_Type *) inversion Hsolv.
  - (* Eval_Thunk *) inversion Hsolv.
  - (* Eval_OutOfFuel *) discriminate Hk0.
Qed.

End SymCore.
