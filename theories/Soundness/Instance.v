From SymCoreTheory Require Export ConCore.Determinism.
From Stdlib Require Import Strings.String Lists.List Lia Arith.PeanoNat.
Import ListNotations.

Section ConCore.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}
  {reduce_prim_solvable_law : ReducePrimSolvable}
  {reduce_prim_saturated_law : ReducePrimSaturated}.
Context {reduce_prim_concore_law : ReducePrimConcore}.
Context {cast_expr_concore_law : CastExprConcore}.
Context {reduce_prim_scoped_law : ReducePrimScoped} {cast_expr_scoped_law : CastExprScoped}.
Context {reduce_prim_keeps_out_of_fuel_law : ReducePrimKeepsOutOfFuel}
  {cast_expr_keeps_out_of_fuel_law : CastExprKeepsOutOfFuel}.
(** ========================================================================= *)
(** SMT Valuations and Concrete Instantiation                                 *)
(** ========================================================================= *)

(**
  A model returned by the solver assigns every symbolic variable a value of
  its sort, and the values of an SMT sort are exactly the literals. Three
  things force the range to be lit rather than expr:

  - concore_expr (σ x) is required, or Cont_Var_Sym would inject a symbolic
    branch into a supposedly concrete term;
  - σ x must be its own value, because Rule Sym-Var reduces the symbolic
    EVar x to EVar x, so the concrete run of σ x must land on something that
    EVar x still contains;
  - σ x must be neither an application nor a constructor, or "case x of ..."
    would match concretely while going undefined symbolically
    (FoldAlts_Otherwise), which breaks soundness outright.

  Literals satisfy all three, and nothing weaker does.
*)

(**
  The symbolic variables of a run: the SMT-level unknowns the symbolic
  execution is parametric in. The set is FIXED for a whole derivation.

  It is a fixed set and not the evaluation environment Γ, because "x is
  symbolic" has to mean the same thing everywhere in one derivation and it
  does not if it is read off Γ. Rule Var evaluates a closure body in the
  STORED environment Γ' while the surrounding judgement lives in the AMBIENT
  environment Γ, and SymCore's environments are raw association lists with no
  freshness discipline. A variable can therefore be unbound, hence symbolic,
  in Γ' and bound in Γ, so concretion indexed by Γ has no sound transport
  across Rule Var.

  A fixed symvars makes concretion environment independent. The freshness
  discipline lives inside `contains` and `contains_env`, which require every
  binder in a related term or environment to be non-symbolic, so the soundness
  statement needs no freshness hypothesis of its own.
*)

(** An environment respects S when it binds no symbolic variable. Derivable
    from contains_env (see contains_env_sym_free), never assumed. *)
Definition sym_free_env (S : symvars) (Γ : environment) : Prop :=
  forall x, S x = true -> lookup_env Γ x = None.

Lemma sym_free_env_empty : forall S, sym_free_env S ·.
Proof. intros S x _. reflexivity. Qed.

(** ------------------------------------------------------------------------- *)
(** The SMT Value of a Formula                                                *)
(** ------------------------------------------------------------------------- *)

(**
  A model satisfies a formula exactly when the formula's SMT value under that
  model is the true literal.

  A path condition had two independent readings here while `models` was a
  Parameter: the verdict (⊨) and the value (pc_value), with nothing tying
  them together. Symbolic evaluation preserves the value - that is
  eval_denote in Soundness/Alignment.v - so a verdict that did not follow the value
  could not be transported across an evaluation step, and eval_models_cond
  and eval_models_not_cond had to be assumed. Reading the verdict off the
  value closes that gap: both are now lemmas (Soundness/Alignment.v), and what is
  assumed instead is prim_value_and below, one equation about how the solver
  reads its own conjunction.
*)
Definition models (σ : valuation) (Φ : path_condition) : Prop :=
  pc_value σ Φ = lit_true.

End ConCore.

Notation "σ '⊨' Φ" := (models σ Φ) (at level 70, no associativity).

Section ConCore.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}
  {reduce_prim_solvable_law : ReducePrimSolvable}
  {reduce_prim_saturated_law : ReducePrimSaturated}
  {reduce_prim_concore_law : ReducePrimConcore} {cast_expr_concore_law : CastExprConcore}.

(** `sat` reports satisfiability, so a formula with a model is satisfiable.
    This is the one fact left relating the model to the `sat` oracle, and it
    stays assumed: `sat` is the solver and nothing here computes it. *)
Class ModelsSat : Prop :=
models_sat : forall σ Φ,
  σ ⊨ Φ -> sat Φ = true.

(** The SMT theory reads op_and as conjunction against the true literal. *)
Class PrimValueAnd : Prop :=
prim_value_and : forall l1 l2,
  prim_value op_and (l1 :: l2 :: nil) = lit_true <-> l1 = lit_true /\ l2 = lit_true.

Context {models_sat_law : ModelsSat} {prim_value_and_law : PrimValueAnd}.

(** The SMT theory reads ∧ as conjunction. *)
Lemma models_and_iff : forall σ Φ1 Φ2,
  σ ⊨ (Φ1 ∧ Φ2) <-> σ ⊨ Φ1 /\ σ ⊨ Φ2.
Proof. intros σ Φ1 Φ2. unfold models, pc_and. simpl. apply prim_value_and. Qed.

(** The verdict depends only on the value, because it is read off the value. *)
Lemma pc_value_sound : forall σ pc1 pc2,
  pc_value σ pc1 = pc_value σ pc2 -> σ ⊨ pc1 -> σ ⊨ pc2.
Proof. unfold models. congruence. Qed.

(**
  e denotes the formula pc: read in any environment that binds no symbolic
  variable, e converts to pc.

  The S parameter is not decoration. expr_to_pc Γ (EVar x) is None exactly
  when Γ binds x, so "e denotes a path-condition formula" is stable only if
  the variables of e are known not to be bound. Quantifying over every
  sym-free environment, rather than fixing the empty one, is what makes the
  judgement scope independent. Fixing the empty environment would allow a
  condition whose variables the ambient environment captures, and
  eval_models_cond would then force models to be empty on variable atoms; see
  the note on eval_models_cond in Soundness/Alignment.v.
*)
Definition denotes (S : symvars) (e : expr) (pc : path_condition) : Prop :=
  forall Γ, sym_free_env S Γ -> expr_to_pc Γ e = Some pc.

(** The SMT solver judges a condition true (resp. false) exactly when the
    condition denotes a formula and the model satisfies it (resp. its
    negation). *)
Definition models_cond (σ : valuation) (S : symvars) (e : expr) : Prop :=
  exists pc, denotes S e pc /\ σ ⊨ pc.

Definition models_not_cond (σ : valuation) (S : symvars) (e : expr) : Prop :=
  exists pc, denotes S e pc /\ σ ⊨ (¬ pc).

(** A judged condition agrees with whatever formula any environment reads off
    it, because expr_to_pc's Some-result does not depend on the environment. *)
Lemma models_cond_pc : forall σ S Γ e pc,
  expr_to_pc Γ e = Some pc -> models_cond σ S e -> σ ⊨ pc.
Proof.
  intros σ S Γ e pc He [pc' [Hden Hmod]].
  rewrite (expr_to_pc_functional e Γ · pc pc' He (Hden · (sym_free_env_empty S))).
  exact Hmod.
Qed.

Lemma models_not_cond_pc : forall σ S Γ e pc,
  expr_to_pc Γ e = Some pc -> models_not_cond σ S e -> σ ⊨ (¬ pc).
Proof.
  intros σ S Γ e pc He [pc' [Hden Hmod]].
  rewrite (expr_to_pc_functional e Γ · pc pc' He (Hden · (sym_free_env_empty S))).
  exact Hmod.
Qed.

Lemma models_cond_denotes : forall σ S e pc,
  denotes S e pc -> (models_cond σ S e <-> σ ⊨ pc).
Proof.
  intros σ S e pc Hden. split.
  - intros H. exact (models_cond_pc σ S · e pc (Hden · (sym_free_env_empty S)) H).
  - intros H. exists pc. split; assumption.
Qed.

Lemma models_not_cond_denotes : forall σ S e pc,
  denotes S e pc -> (models_not_cond σ S e <-> σ ⊨ (¬ pc)).
Proof.
  intros σ S e pc Hden. split.
  - intros H. exact (models_not_cond_pc σ S · e pc (Hden · (sym_free_env_empty S)) H).
  - intros H. exists pc. split; assumption.
Qed.

Lemma models_cond_total : forall σ S Γ e,
  sym_free_env S Γ ->
  models_cond σ S e \/ models_not_cond σ S e ->
  exists pc, expr_to_pc Γ e = Some pc.
Proof.
  intros σ S Γ e Hfree [[pc [Hden _]] | [pc [Hden _]]];
    exists pc; apply Hden; exact Hfree.
Qed.

(** ------------------------------------------------------------------------- *)
(** The SMT Value of a Term                                                   *)
(** ------------------------------------------------------------------------- *)

(**
  e has SMT value l under σ: e reads off a formula in every scope that does
  not capture it, and the model gives that formula the value l. Building on
  `denotes` instead of a second evaluator keeps the scoping discipline of S,
  and ties the notion to the formulas the solver is actually asked about.
*)
Definition denote (σ : valuation) (S : symvars) (e : expr) (l : lit) : Prop :=
  exists pc, denotes S e pc /\ pc_value σ pc = l.

Lemma denote_functional : forall σ S e l1 l2,
  denote σ S e l1 -> denote σ S e l2 -> l1 = l2.
Proof.
  intros σ S e l1 l2 [pc1 [Hd1 Hv1]] [pc2 [Hd2 Hv2]].
  rewrite <- Hv1, <- Hv2.
  rewrite (expr_to_pc_functional e · · pc1 pc2
             (Hd1 · (sym_free_env_empty S)) (Hd2 · (sym_free_env_empty S))).
  reflexivity.
Qed.

Lemma denote_lit : forall σ S l, denote σ S (ELit l) l.
Proof. intros σ S l. exists (PCLit l). split; [intros Γ _; reflexivity | reflexivity]. Qed.

Lemma denote_lit_inv : forall σ S l m, denote σ S (ELit l) m -> l = m.
Proof.
  intros σ S l m H. symmetry.
  exact (denote_functional σ S (ELit l) m l H (denote_lit σ S l)).
Qed.

Lemma denote_var_inv : forall σ S x l, denote σ S (EVar x) l -> S x = true /\ l = σ x.
Proof.
  intros σ S x l [pc [Hden Hval]].
  assert (Hpc : expr_to_pc · (EVar x) = Some pc) by (apply Hden; apply sym_free_env_empty).
  simpl in Hpc. injection Hpc as Hpc. subst pc.
  simpl in Hval. split; [| symmetry; exact Hval].
  destruct (S x) eqn:Hsx; [reflexivity | exfalso].
  assert (Hcapture : expr_to_pc (ExtendEnv x (MkClosure · (EBot BUndefined)) ·) (EVar x)
                     = Some (PCVar x)).
  { apply Hden. intros y Hy. simpl.
    destruct (string_dec y x) as [Heq | Hne]; [subst; congruence | reflexivity]. }
  simpl in Hcapture. destruct (string_dec x x); [discriminate | congruence].
Qed.

(**
  A closed SMT term: built from literals and saturated-or-not primitive
  applications, with no variable anywhere. Instantiation by a model does
  nothing to such a term, which is why the semantic rule below excludes it.
*)
Fixpoint smt_ground (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EPrimOp _ => true
  | EApp f a => is_op_app f && smt_ground f && smt_ground a
  | _ => false
  end.

Lemma smt_ground_solvable : forall e Γ, smt_ground e = true -> Solvable Γ e.
Proof.
  induction e; intros Γ H; simpl in H; try discriminate.
  - apply Solvable_Lit.
  - apply Solvable_PrimOp.
  - apply andb_prop in H as [H12 H2]. apply andb_prop in H12 as [Hop H1].
    apply Solvable_AppPrim; [exact Hop | apply IHe1; exact H1 | apply IHe2; exact H2].
Qed.

Lemma solvable_everywhere_smt_ground : forall e,
  (forall Γ, Solvable Γ e) -> smt_ground e = true.
Proof.
  induction e; intros Hall;
    try (exfalso; specialize (Hall ·); inversion Hall; fail).
  - exfalso. specialize (Hall (ExtendEnv v (MkClosure · (EBot BUndefined)) ·)).
    inversion Hall as [| y Hnone | |]; subst. simpl in Hnone.
    destruct (string_dec v v); [discriminate | congruence].
  - reflexivity.
  - reflexivity.
  - assert (Hop : is_op_app e1 = true)
      by (specialize (Hall ·); inversion Hall as [| | | f a Hop Hf Ha]; exact Hop).
    assert (H1 : forall Γ, Solvable Γ e1)
      by (intros Γ; specialize (Hall Γ); inversion Hall; assumption).
    assert (H2 : forall Γ, Solvable Γ e2)
      by (intros Γ; specialize (Hall Γ); inversion Hall; assumption).
    simpl. rewrite Hop. rewrite (IHe1 H1), (IHe2 H2). reflexivity.
Qed.

(**
  Concretion: contains σ S e_sym e_con says that, under the SMT model σ and
  with S as the symbolic variables, the concrete term e_con is the instance
  of the symbolic term e_sym - each free symbolic variable replaced by its
  value under σ, and each symbolic branch resolved to the branch σ selects.

  Every binder occurring in a related term is required to be non-symbolic
  (S x = false). That is the freshness discipline that makes "symbolic
  variable" well defined; see the comment on symvars.
*)
Inductive contains (σ : valuation) (S : symvars) : expr -> expr -> Prop :=
  | Cont_Var_Bound : forall x,
      S x = false ->
      contains σ S (EVar x) (EVar x)

  | Cont_Var_Sym : forall x,
      S x = true ->
      contains σ S (EVar x) (ELit (σ x))

  | Cont_Lit : forall l,
      contains σ S (ELit l) (ELit l)
  | Cont_PrimOp : forall p,
      contains σ S (EPrimOp p) (EPrimOp p)
  | Cont_Con : forall d,
      contains σ S (ECon d) (ECon d)
  | Cont_Coercion : forall γ,
      contains σ S (ECoercion γ) (ECoercion γ)
  | Cont_Type : forall τ,
      contains σ S (EType τ) (EType τ)
  | Cont_Bot : forall b,
      contains σ S (EBot b) (EBot b)

  (** Structural congruence *)
  | Cont_App : forall f_s a_s f_c a_c,
      contains σ S f_s f_c ->
      contains σ S a_s a_c ->
      contains σ S (EApp f_s a_s) (EApp f_c a_c)
  | Cont_Lam : forall x bodys bodyc,
      S x = false ->
      contains σ S bodys bodyc ->
      contains σ S (ELam x bodys) (ELam x bodyc)
  | Cont_Thunk : forall Γs Γc es ec,
      contains_env σ S Γs Γc ->
      contains σ S es ec ->
      contains σ S (EThunk Γs es) (EThunk Γc ec)
  | Cont_Thunk_Outer : forall Γs Γc es ec,
      contains_env σ S Γs Γc ->
      contains σ S es ec ->
      is_thunk ec = true ->
      contains σ S (EThunk Γs es) ec
  | Cont_Cast : forall es ec γ,
      contains σ S es ec ->
      contains σ S (ECast es γ) (ECast ec γ)
  | Cont_Case : forall ess esc altss altsc,
      contains σ S ess esc ->
      Forall2 (contains_alt σ S) altss altsc ->
      contains σ S (ECase ess altss) (ECase esc altsc)

  (** Branch resolution: along model σ, exactly one branch is active *)
  | Cont_If_True : forall ec et ef etc,
      models_cond σ S ec ->
      contains σ S et etc ->
      contains σ S (EIf ec et ef) etc
  | Cont_If_False : forall ec et ef efc,
      models_not_cond σ S ec ->
      contains σ S ef efc ->
      contains σ S (EIf ec et ef) efc

  (**
    The SMT fragment is related semantically, not syntactically: a residual
    symbolic SMT term is concretized by the literal it denotes under σ.

    The premises say exactly when this rule is needed. The term must be a
    SATURATED application of a primitive operation, the only shape whose
    concrete instance the syntax does not already fix. The term must also NOT
    be closed (smt_ground es = false), because a closed SMT term mentions no
    variable, so instantiation does nothing to it and the structural rules
    already relate it to itself.

    The concrete side is a literal because the concrete run has no symbolic
    variables left: every SMT term it holds is closed, and the solver's
    reducer delivers its value.
  *)
  | Cont_Denote : forall es p args l,
      unspool_app es [] = (EPrimOp p, args) ->
      length args = primop_arity p ->
      smt_ground es = false ->
      denote σ S es l ->
      contains σ S es (ELit l)

with contains_alt (σ : valuation) (S : symvars) : alt -> alt -> Prop :=
  | Cont_Alt : forall d xs eps epc,
      Forall (fun x => S x = false) xs ->
      contains σ S eps epc ->
      contains_alt σ S (Alt d xs eps) (Alt d xs epc)

with contains_env (σ : valuation) (S : symvars) : environment -> environment -> Prop :=
  | Cont_Env_Empty :
      contains_env σ S · ·
  | Cont_Env_Extend : forall x Γs Γc es ec rest_s rest_c,
      S x = false ->
      contains_env σ S Γs Γc ->
      contains σ S es ec ->
      concore_expr ec ->
      contains_env σ S rest_s rest_c ->
      contains_env σ S (ExtendEnv x (MkClosure Γs es) rest_s)
                       (ExtendEnv x (MkClosure Γc ec) rest_c).

(** Cont_Denote only ever fires on an application: its head must be a
    primitive operation, and a bare primitive operation is closed. *)
Lemma cont_denote_is_app : forall es p args,
  unspool_app es [] = (EPrimOp p, args) ->
  smt_ground es = false ->
  exists f a, es = EApp f a.
Proof.
  intros es p args Hun Hg. destruct es; simpl in Hun; try discriminate Hun.
  - simpl in Hg. discriminate Hg.
  - exists es1, es2. reflexivity.
Qed.

End ConCore.

Ltac kill_denote :=
  match goal with
  | [ Hun : unspool_app ?e (@nil expr) = (EPrimOp _, _),
      Hg : smt_ground ?e = false |- _ ] =>
      destruct (cont_denote_is_app e _ _ Hun Hg) as [? [? ?]]; discriminate
  end.

Notation instantiates := contains.
Notation instantiates_alt := contains_alt.
Notation instantiates_env := contains_env.
