(** ========================================================================= *)
(** ConCore: Concrete Subset Calculus of SymCore                              *)
(**                                                                           *)
(** POPL Revision: Soundness and Completeness of Symbolic Execution           *)
(**                                                                           *)
(** Rather than introducing a separate AST and an inductive simulation        *)
(** relation (contains), ConCore is formalized directly as an inductive       *)
(** syntactic restriction (subset) of SymCore:                                *)
(** 1. Removal of symbolic branching (EIf).                                  *)
(** 2. Source-level programs also exclude runtime closures (EClos).           *)
(** ========================================================================= *)

From SymCoreTheory Require Import SymCore.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
Import ListNotations.

(** ========================================================================= *)
(** 1. Syntactic Restriction: ConCore as an Inductive Subset of SymCore       *)
(** ========================================================================= *)

(** ConCore expressions: System FC syntax with runtime closures, but
    strictly excluding symbolic branching (EIf). *)
Inductive concore_expr : expr -> Prop :=
  | Con_Var : forall x, concore_expr (EVar x)
  | Con_Lit : forall l, concore_expr (ELit l)
  | Con_PrimOp : forall p, concore_expr (EPrimOp p)
  | Con_Con : forall d, concore_expr (ECon d)
  | Con_App : forall f a, concore_expr f -> concore_expr a -> concore_expr (EApp f a)
  | Con_Lam : forall x body, concore_expr body -> concore_expr (ELam x body)
  | Con_Clos : forall Γ x body, concrete_env Γ -> concore_expr body -> concore_expr (EClos Γ x body)
  | Con_Case : forall es alts, concore_expr es -> Forall concore_alt alts -> concore_expr (ECase es alts)
  | Con_Cast : forall e γ, concore_expr e -> concore_expr (ECast e γ)
  | Con_Coercion : forall γ, concore_expr (ECoercion γ)
  | Con_Type : forall τ, concore_expr (EType τ)
  | Con_Bot_Undefined : concore_expr (EBot BUndefined)
  | Con_Bot_Unreachable : concore_expr (EBot BUnreachable)
  | Con_Bot_Raise : forall e, concore_expr e -> concore_expr (EBot (BRaise e))

with concore_alt : alt -> Prop :=
  | Con_Alt : forall d xs ep, concore_expr ep -> concore_alt (Alt d xs ep)

with concrete_env : environment -> Prop :=
  | CEnv_Empty : concrete_env ·
  | CEnv_Extend : forall x Γ' e rest,
      concore_expr e ->
      concrete_env Γ' ->
      concrete_env rest ->
      concrete_env (ExtendEnv x (MkClosure Γ' e) rest).

(** Source System FC expressions: pure AST prior to execution,
    excluding both runtime closures (EClos) and symbolic branching (EIf). *)
Inductive source_expr : expr -> Prop :=
  | Src_Var : forall x, source_expr (EVar x)
  | Src_Lit : forall l, source_expr (ELit l)
  | Src_PrimOp : forall p, source_expr (EPrimOp p)
  | Src_Con : forall d, source_expr (ECon d)
  | Src_App : forall f a, source_expr f -> source_expr a -> source_expr (EApp f a)
  | Src_Lam : forall x body, source_expr body -> source_expr (ELam x body)
  | Src_Case : forall es alts, source_expr es -> Forall source_alt alts -> source_expr (ECase es alts)
  | Src_Cast : forall e γ, source_expr e -> source_expr (ECast e γ)
  | Src_Coercion : forall γ, source_expr (ECoercion γ)
  | Src_Type : forall τ, source_expr (EType τ)
  | Src_Bot_Undefined : source_expr (EBot BUndefined)
  | Src_Bot_Unreachable : source_expr (EBot BUnreachable)
  | Src_Bot_Raise : forall e, source_expr e -> source_expr (EBot (BRaise e))

with source_alt : alt -> Prop :=
  | Src_Alt : forall d xs ep, source_expr ep -> source_alt (Alt d xs ep).

(** ========================================================================= *)
(** 2. Inversion Lemmas                                                        *)
(** ========================================================================= *)

Lemma not_concore_if : forall ec et ef, ~ concore_expr (EIf ec et ef).
Proof.
  intros ec et ef H.
  inversion H.
Qed.

Lemma not_source_clos : forall Γ x body, ~ source_expr (EClos Γ x body).
Proof.
  intros Γ x body H.
  inversion H.
Qed.

Lemma not_source_if : forall ec et ef, ~ source_expr (EIf ec et ef).
Proof.
  intros ec et ef H.
  inversion H.
Qed.

(** ========================================================================= *)
(** 3. Subterm Preservation Lemmas for Source Expressions                     *)
(** ========================================================================= *)

Lemma source_expr_app_l : forall f a, source_expr (EApp f a) -> source_expr f.
Proof.
  intros f a H. inversion H; subst. assumption.
Qed.

Lemma source_expr_app_r : forall f a, source_expr (EApp f a) -> source_expr a.
Proof.
  intros f a H. inversion H; subst. assumption.
Qed.

Lemma source_expr_lam : forall x body, source_expr (ELam x body) -> source_expr body.
Proof.
  intros x body H. inversion H; subst. assumption.
Qed.

Lemma source_expr_cast : forall e γ, source_expr (ECast e γ) -> source_expr e.
Proof.
  intros e γ H. inversion H; subst. assumption.
Qed.

Lemma source_expr_case_es : forall es alts, source_expr (ECase es alts) -> source_expr es.
Proof.
  intros es alts H. inversion H; subst. assumption.
Qed.

(** ========================================================================= *)
(** 4. Subterm Preservation Lemmas for ConCore Expressions                    *)
(** ========================================================================= *)

Lemma concore_expr_app_l : forall f a, concore_expr (EApp f a) -> concore_expr f.
Proof.
  intros f a H. inversion H; subst. assumption.
Qed.

Lemma concore_expr_app_r : forall f a, concore_expr (EApp f a) -> concore_expr a.
Proof.
  intros f a H. inversion H; subst. assumption.
Qed.

Lemma concore_expr_lam : forall x body, concore_expr (ELam x body) -> concore_expr body.
Proof.
  intros x body H. inversion H; subst. assumption.
Qed.

Lemma concore_expr_clos : forall Γ x body, concore_expr (EClos Γ x body) -> concore_expr body.
Proof.
  intros Γ x body H. inversion H; subst. assumption.
Qed.

Lemma concore_expr_clos_env : forall Γ x body, concore_expr (EClos Γ x body) -> concrete_env Γ.
Proof.
  intros Γ x body H. inversion H; subst. assumption.
Qed.

Lemma concore_expr_cast : forall e γ, concore_expr (ECast e γ) -> concore_expr e.
Proof.
  intros e γ H. inversion H; subst. assumption.
Qed.

Lemma concore_expr_case_es : forall es alts, concore_expr (ECase es alts) -> concore_expr es.
Proof.
  intros es alts H. inversion H; subst. assumption.
Qed.

(** ========================================================================= *)
(** 5. Source Expressions Embed into ConCore Expressions                      *)
(** ========================================================================= *)

Fixpoint source_expr_to_concore (e : expr) (H : source_expr e) : concore_expr e
with source_alt_to_concore (a : alt) (H : source_alt a) : concore_alt a.
Proof.
  - destruct H.
    + constructor.
    + constructor.
    + constructor.
    + constructor.
    + constructor; [apply source_expr_to_concore; assumption | apply source_expr_to_concore; assumption].
    + constructor. apply source_expr_to_concore. assumption.
    + constructor; [apply source_expr_to_concore; assumption |].
      induction H0.
      * constructor.
      * constructor; [apply source_alt_to_concore; assumption | apply IHForall].
    + constructor. apply source_expr_to_concore. assumption.
    + constructor.
    + constructor.
    + constructor.
    + constructor.
    + constructor. apply source_expr_to_concore. assumption.
  - destruct H.
    constructor. apply source_expr_to_concore. assumption.
Defined.

Corollary source_is_concore : forall e,
  source_expr e -> concore_expr e.
Proof.
  intros e H. apply source_expr_to_concore. assumption.
Qed.

(** ========================================================================= *)
(** 6. Concrete Contexts: Environments without Symbolic Variables              *)
(** ========================================================================= *)

(**
  In SymCore, any variable x with lookup_env Γ x = None is treated as an
  uninterpreted symbolic variable (Axiom Solvable_Var).
  In ConCore, concrete evaluation requires that all variables accessed in an
  expression are concrete (bound in the environment), so that no symbolic
  variables are present.
*)

(** A variable x is concrete (bound) in environment Γ *)
Definition is_concrete_var (Γ : environment) (x : var) : Prop :=
  exists Γ' e, lookup_env Γ x = Some (Γ', e).

(** An expression e is evaluated in a concrete context (Γ, e) if none of its
    free variables are symbolic (i.e. every free variable is bound in Γ). *)
Definition concrete_context (Γ : environment) (e : expr) : Prop :=
  forall x, In x (fv e) -> is_concrete_var Γ x.

(** Closed expressions contain no free variables at all *)
Definition closed_expr (e : expr) : Prop :=
  forall x, ~ In x (fv e).

(** Note: concrete_env is defined mutually with concore_expr in Section 1. *)

(** ========================================================================= *)
(** 7. Properties of Concrete Contexts                                         *)
(** ========================================================================= *)

(** A symbolic variable (unbound in Γ) is never in a concrete context *)
Lemma sym_var_not_concrete_context : forall Γ x,
  lookup_env Γ x = None ->
  ~ concrete_context Γ (EVar x).
Proof.
  intros Γ x Hlookup Hctx.
  unfold concrete_context, is_concrete_var in Hctx.
  destruct (Hctx x (or_introl eq_refl)) as [Γ' [e Heq]].
  rewrite Hlookup in Heq. discriminate.
Qed.

(** A bound variable is in a concrete context *)
Lemma bound_var_concrete_context : forall Γ x Γ' e,
  lookup_env Γ x = Some (Γ', e) ->
  concrete_context Γ (EVar x).
Proof.
  intros Γ x Γ' e Hlookup y [Heq | Hfalse].
  - subst. exists Γ', e. assumption.
  - contradiction.
Qed.

(** In the empty environment, concrete_context is equivalent to closed_expr *)
Lemma concrete_context_empty_closed : forall e,
  concrete_context · e <-> closed_expr e.
Proof.
  split.
  - intros Hctx x Hin.
    destruct (Hctx x Hin) as [Γ' [e' Heq]].
    simpl in Heq. discriminate.
  - intros Hclosed x Hin.
    exfalso. apply (Hclosed x Hin).
Qed.

(** Concrete context distributes over applications *)
Lemma concrete_context_app : forall Γ f a,
  concrete_context Γ (EApp f a) <->
  concrete_context Γ f /\ concrete_context Γ a.
Proof.
  intros Γ f a. unfold concrete_context. simpl.
  split.
  - intros H. split; intros x Hin; apply H; apply in_or_app; [left | right]; assumption.
  - intros [Hf Ha] x Hin. apply in_app_or in Hin as [Hinf | Hina]; auto.
Qed.

Lemma concrete_context_app_l : forall Γ f a,
  concrete_context Γ (EApp f a) -> concrete_context Γ f.
Proof.
  intros Γ f a H.
  apply (concrete_context_app Γ f a) in H as [Hf _]. exact Hf.
Qed.

Lemma concrete_context_app_r : forall Γ f a,
  concrete_context Γ (EApp f a) -> concrete_context Γ a.
Proof.
  intros Γ f a H.
  apply (concrete_context_app Γ f a) in H as [_ Ha]. exact Ha.
Qed.

(** Concrete context for casts *)
Lemma concrete_context_cast : forall Γ e γ,
  concrete_context Γ (ECast e γ) <-> concrete_context Γ e.
Proof.
  intros Γ e γ. unfold concrete_context. simpl. reflexivity.
Qed.

(** Extending the environment preserves bound variables *)
Lemma is_concrete_var_extend : forall Γ x y Γ' e,
  is_concrete_var Γ y ->
  is_concrete_var (extend_env Γ x Γ' e) y.
Proof.
  intros Γ x y Γ' e [Γ0 [e0 Hlookup]].
  unfold is_concrete_var, extend_env. simpl.
  destruct (string_dec y x).
  - subst. exists Γ', e. reflexivity.
  - exists Γ0, e0. assumption.
Qed.

(** The newly extended variable is always concrete in the extended environment *)
Lemma is_concrete_var_extend_self : forall Γ x Γ' e,
  is_concrete_var (extend_env Γ x Γ' e) x.
Proof.
  intros Γ x Γ' e. unfold is_concrete_var, extend_env. simpl.
  destruct (string_dec x x) as [_ | Hneq].
  - exists Γ', e. reflexivity.
  - exfalso. apply Hneq. reflexivity.
Qed.

(** Helper: membership in remove *)
Lemma in_remove_helper : forall x y l,
  In y l -> y <> x -> In y (remove string_dec x l).
Proof.
  intros x y l. induction l as [| a tl IH]; intros Hin Hneq; [inversion Hin |].
  simpl. destruct (string_dec x a).
  - subst. destruct Hin; [subst; contradiction | auto].
  - destruct Hin; [subst; left; reflexivity | right; auto].
Qed.

(** Lambda body has a concrete context under the extended environment *)
Lemma concrete_context_lam_extend : forall Γ x body Γ' ea,
  concrete_context Γ (ELam x body) ->
  concrete_context (extend_env Γ x Γ' ea) body.
Proof.
  intros Γ x body Γ' ea Hctx y Hin.
  destruct (string_dec y x).
  - subst. apply is_concrete_var_extend_self.
  - apply is_concrete_var_extend.
    apply Hctx. simpl.
    apply in_remove_helper; auto.
Qed.

(** ========================================================================= *)
(** 8. Concrete Evaluation Semantics and Preservation                         *)
(** ========================================================================= *)

(** Concrete evaluation is SymCore evaluation under the canonical trivial path condition pc_true *)
Definition eval_con (Γ : environment) (e : expr) (v : expr) : Prop :=
  eval Inf pc_true Γ e v.

(** Notation for concrete big-step reduction: Γ ⊢ᶜ e ⇓ᶜ v *)
Notation "Γ '⊢ᶜ' e '⇓ᶜ' v" := (eval_con Γ e v) (at level 70, no associativity).
Notation "'⊢ᶜ' e '⇓ᶜ' v" := (eval_con · e v) (at level 70, no associativity).

(** ------------------------------------------------------------------------- *)
(** 8.1 SMT & Grisette Solver Behaviors for Concrete Evaluation               *)
(** ------------------------------------------------------------------------- *)

(** SMT solver & Grisette evaluation behaviors:
    1. Primitive operations reduce to concrete terms in ConCore.
    2. State merging on a ConCore term preserves ConCore syntax.
    3. Coercion casts preserve ConCore syntax. *)
(**
  Primitive reduction stays inside ConCore WHEN ITS ARGUMENTS DO. The
  hypothesis matters: concore_expr excludes EIf, so an unconditional version
  would say the theory solver never returns a branch - not even when an
  argument is itself a branch. That is precisely the erasure that the
  repaired reduce_prim_solvable in SymCore.v is there to permit.
*)
Axiom reduce_prim_concore : forall p args,
  Forall concore_expr args ->
  concore_expr (reduce_prim p args).

Axiom merge_concore : forall e,
  concore_expr e ->
  concore_expr (merge e).

Axiom cast_expr_concore : forall e γ,
  concore_expr e ->
  concore_expr (cast_expr e γ).

(**
  REMOVED: Axiom cast_expr_eval_app.

    forall Φ Γ eb eb' γ ea v,
      Φ; Γ ⊢ eb ⇓ eb' ->
      Φ; Γ ⊢ EApp (cast_expr eb' γ) ea ⇓ v ->
      Φ; Γ ⊢ EApp (ECast eb γ) ea ⇓ v

  It was not a fact about the solver at all. It was a RULE of the judgement,
  written as an assumption, and the rules could not derive a single instance
  of it (Section 12.5). Two things were wrong with that. It was invisible in
  Figure 3, so the calculus on paper was not the calculus in the proofs; and
  because it said nothing about the coercion, it also handed an arrow cast
  the value that Rule App-Cast denies it, which is one of the two reasons
  concrete evaluation was not deterministic.

  It is gone, and nothing replaced it. Rule App-Spine now refuses every cast
  operator, which leaves the shape stuck on the symbolic and the concrete
  side at once, so soundness never needs the step. Section 12.5 tells the
  whole story.
*)

(** ------------------------------------------------------------------------- *)
(** 8.2 Mutual Induction Scheme for Big-Step Semantics                        *)
(** ------------------------------------------------------------------------- *)

Scheme eval_mut := Induction for eval Sort Prop
with fold_alts_mut := Induction for fold_alts Sort Prop.
Combined Scheme eval_fold_alts_mut from eval_mut, fold_alts_mut.

(** ------------------------------------------------------------------------- *)
(** 8.3 Inversion and Preservation Helpers                                    *)
(** ------------------------------------------------------------------------- *)

Lemma lookup_env_concrete : forall Γ x Γ' e,
  concrete_env Γ ->
  lookup_env Γ x = Some (Γ', e) ->
  concrete_env Γ' /\ concore_expr e.
Proof.
  induction 1; intros Hlook.
  - simpl in Hlook. discriminate.
  - simpl in Hlook.
    destruct (string_dec x x0).
    + inversion Hlook; subst. split; assumption.
    + apply IHconcrete_env2. assumption.
Qed.

Lemma concrete_env_extend : forall Γ x Γ' e,
  concrete_env Γ ->
  concrete_env Γ' ->
  concore_expr e ->
  concrete_env (extend_env Γ x Γ' e).
Proof.
  intros Γ x Γ' e HΓ HΓ' He.
  constructor; assumption.
Qed.

Lemma concrete_env_extend_multi : forall xs ea Γ Γ_arg,
  concrete_env Γ ->
  concrete_env Γ_arg ->
  Forall concore_expr ea ->
  concrete_env (extend_env_multi Γ xs ea Γ_arg).
Proof.
  induction xs as [| x xs' IH]; intros ea Γ Γ_arg HΓ HΓ_arg Hea.
  - simpl. assumption.
  - destruct ea as [| a ea'].
    + simpl. assumption.
    + simpl. apply concrete_env_extend.
      * apply IH; [assumption | assumption | inversion Hea; subst; assumption].
      * assumption.
      * inversion Hea; subst; assumption.
Qed.

Lemma unspool_app_concore : forall e acc head args,
  unspool_app e acc = (head, args) ->
  concore_expr e ->
  Forall concore_expr acc ->
  concore_expr head /\ Forall concore_expr args.
Proof.
  induction e; intros acc head args Hunspool Hcon Hacc; simpl in Hunspool;
  try (inversion Hunspool; subst; split; [assumption | assumption]).
  apply IHe1 with (acc := e2 :: acc); [assumption | |].
  - inversion Hcon; subst; assumption.
  - constructor; [inversion Hcon; subst; assumption | assumption].
Qed.

Lemma decompose_con_app_concore : forall e d ea,
  decompose_con_app e = Some (d, ea) ->
  concore_expr e ->
  Forall concore_expr ea.
Proof.
  intros e d ea Hdec Hcon.
  unfold decompose_con_app in Hdec.
  remember (unspool_app e []) as res.
  destruct res as [head args].
  destruct head; try discriminate.
  inversion Hdec; subst.
  assert (Hargs := unspool_app_concore e [] (ECon d) ea (eq_sym Heqres) Hcon (Forall_nil _)).
  destruct Hargs as [_ Hforall]. exact Hforall.
Qed.

Lemma find_alt_concore : forall d alts xs ep,
  find_alt d alts = Some (xs, ep) ->
  Forall concore_alt alts ->
  concore_expr ep.
Proof.
  intros d alts. induction alts as [| a alts' IH]; intros xs ep Hfind Hforall.
  - simpl in Hfind. discriminate.
  - simpl in Hfind. inversion Hforall; subst.
    destruct a as [d' xs' ep'].
    inversion H1; subst.
    destruct (string_dec d d').
    + inversion Hfind; subst. assumption.
    + apply IH with (xs := xs); assumption.
Qed.

(** ------------------------------------------------------------------------- *)
(** 8.4 ConCore Closure under Evaluation (Syntactic Stability)                *)
(** ------------------------------------------------------------------------- *)

(**
  ConCore closure under evaluation, as a pair of mutually recursive fixpoints
  rather than by the auto-derived mutual induction scheme. Rule App-Prim needs
  the statement for every argument of its Forall2 (eval (dec f) Φ Γ) args args'
  in order to feed the repaired (argument-conditional) reduce_prim_concore, and
  the derived scheme supplies no induction hypothesis under a Forall2.

  The statement holds at every fuel, so it takes the fuel as a parameter and
  asks nothing of it. Rule Out-Of-Fuel answers EBot BUndefined, and that is a
  ConCore expression, so the case closes with the same constructor as Rule
  Bot. Nothing here needs the budget to be unlimited.
*)
Fixpoint concore_eval_closed_fix (f0 : fuel) (Φ : path_condition) (Γ : environment) (e v : expr)
  (Heval : eval f0 Φ Γ e v) {struct Heval} :
  sat Φ = true -> concrete_env Γ -> concore_expr e -> concore_expr v
with concore_fold_closed_fix (f0 : fuel) (Φ : path_condition) (Γ : environment) (e : expr)
  (alts : list alt) (er : expr)
  (Hfold : fold_alts f0 Φ Γ e alts er) {struct Hfold} :
  sat Φ = true -> concrete_env Γ -> concore_expr e -> Forall concore_alt alts -> concore_expr er.
Proof.
{
  destruct Heval as
    [ k Φ Γ x Γ' e e' Hlook Heval_x
    | k Φ Γ x Hnone
    | k Φ Γ l
    | k Φ Γ d
    | k Φ Γ e γ e' Heval_e
    | k Φ Γ Γ' x eb ea eb' Heval_b
    | k Φ Γ ef ea ef' er Hnotwhnf Hguard Heval_f Heval_app2
    | k Φ Γ b
    | k Φ Γ ef ea p args args' Hunspool Harity Hargs
    | k Φ Γ x e
    | k Φ Γ ef γ ea γ_a γ_r er Hdecomp Heval_pushed
    | k Φ Γ b ea
    | k Φ Γ es alts es' er Heval_es Hfold
    | k Φ Γ ec et ef ec' et' ef' pc_c Heval_c Hpc Heval_t Heval_f
    | k Φ Γ γ
    | k Φ Γ e Hunsat
    | k Φ Γ τ
    | Φ Γ e
    ]; intros Hsat Henv Hcon.
  - (* Eval_Var *)
    destruct (lookup_env_concrete Γ x Γ' e Henv Hlook) as [Henv' He].
    exact (concore_eval_closed_fix (dec k) Φ Γ' e e' Heval_x Hsat Henv' He).
  - (* Eval_SymVar *) exact Hcon.
  - (* Eval_Lit *) constructor.
  - (* Eval_Con *) constructor.
  - (* Eval_Cast *)
    apply cast_expr_concore.
    apply (concore_eval_closed_fix (dec k) Φ Γ e e' Heval_e Hsat Henv).
    inversion Hcon; subst; assumption.
  - (* Eval_AppAbs *)
    inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | ]; subst.
    inversion Hf as [| | | | | | Γ0 x0 body Henv' Hbody | | | | | | | ]; subst.
    apply (concore_eval_closed_fix (dec k) Φ (extend_env Γ' x Γ ea) eb eb' Heval_b Hsat).
    + apply concrete_env_extend; assumption.
    + assumption.
  - (* Eval_AppSpine *)
    inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | ]; subst.
    apply (concore_eval_closed_fix (dec k) Φ Γ (EApp ef' ea) er Heval_app2 Hsat Henv).
    apply Con_App; [| assumption].
    exact (concore_eval_closed_fix (dec k) Φ Γ ef ef' Heval_f Hsat Henv Hf).
  - (* Eval_Bot *) exact Hcon.
  - (* Eval_AppPrim *)
    assert (Hcon_args : Forall concore_expr args).
    { destruct (unspool_app_concore (EApp ef ea) [] (EPrimOp p) args Hunspool Hcon
                 (Forall_nil _)) as [_ Hforall]. exact Hforall. }
    apply reduce_prim_concore.
    clear Hunspool Harity Hcon.
    induction Hargs as [| a a' args_tl args'_tl Ha Hargs_tl IH].
    + constructor.
    + inversion Hcon_args as [| a0 tl0 Hcon_a Hcon_tl]; subst.
      constructor.
      * exact (concore_eval_closed_fix (dec k) Φ Γ a a' Ha Hsat Henv Hcon_a).
      * exact (IH Hcon_tl).
  - (* Eval_Lam *)
    constructor; [assumption |].
    inversion Hcon; subst; assumption.
  - (* Eval_AppCast *)
    inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | ]; subst.
    inversion Hf as [| | | | | | | | e γ0 He | | | | | ]; subst.
    apply (concore_eval_closed_fix (dec k) Φ Γ (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r)
             er Heval_pushed Hsat Henv).
    apply Con_Cast. apply Con_App; [assumption | apply Con_Cast; assumption].
  - (* Eval_AppBot *)
    inversion Hcon; subst. assumption.
  - (* Eval_Case *)
    inversion Hcon as [| | | | | | | es0 alts0 Hcon_es Hcon_alts | | | | | | ]; subst.
    apply (concore_fold_closed_fix (dec k) Φ Γ (merge es') alts er Hfold Hsat Henv);
      [| assumption].
    apply merge_concore.
    exact (concore_eval_closed_fix (dec k) Φ Γ es es' Heval_es Hsat Henv Hcon_es).
  - (* Eval_If *)
    exfalso. apply (not_concore_if ec et ef). assumption.
  - (* Eval_Coercion *) constructor.
  - (* Eval_Prune *) constructor.
  - (* Eval_Type *) constructor.
  - (* Eval_OutOfFuel *) constructor.
}
{
  destruct Hfold as
    [ k Φ Γ ec et ef alts et' ef' pc_c Hpc Hfold_t Hfold_f
    | k Φ Γ ec et ef alts Hpc_none
    | k Φ Γ e d ea xs ep alts er Hdec Halt Heval_ep
    | k Φ Γ b alts
    | k Φ Γ e alts Hnotif Hnoalt Hnotbot
    ]; intros Hsat Henv Hcon Halts.
  - exfalso. apply (not_concore_if ec et ef). assumption.
  - exfalso. apply (not_concore_if ec et ef). assumption.
  - (* FoldAlts_Con *)
    assert (Hea : Forall concore_expr ea).
    { apply decompose_con_app_concore with (e := e) (d := d); assumption. }
    assert (Hep : concore_expr ep).
    { apply find_alt_concore with (d := d) (alts := alts) (xs := xs); assumption. }
    apply (concore_eval_closed_fix (dec k) Φ (extend_env_multi Γ xs ea Γ) ep er Heval_ep Hsat);
      [| assumption].
    apply concrete_env_extend_multi; assumption.
  - (* FoldAlts_Bot *) exact Hcon.
  - (* FoldAlts_Otherwise *) constructor.
}
Qed.

Lemma concore_eval_closed_mut :
  (forall Φ Γ e v (Heval : Φ; Γ ⊢ e ⇓ v),
     Φ = pc_true -> concrete_env Γ -> concore_expr e -> concore_expr v) /\
  (forall Φ Γ e alts er (Hfold : fold_alts Inf Φ Γ e alts er),
     Φ = pc_true -> concrete_env Γ -> concore_expr e -> Forall concore_alt alts -> concore_expr er).
Proof.
  split.
  - intros Φ Γ e v Heval Heq. subst Φ.
    exact (concore_eval_closed_fix Inf pc_true Γ e v Heval sat_pc_true).
  - intros Φ Γ e alts er Hfold Heq. subst Φ.
    exact (concore_fold_closed_fix Inf pc_true Γ e alts er Hfold sat_pc_true).
Qed.

(** ConCore Closure under Evaluation:
    Concrete evaluation in a concrete environment never escapes ConCore. *)
Lemma concore_eval_closed : forall Γ e v,
  concrete_env Γ ->
  concore_expr e ->
  Γ ⊢ᶜ e ⇓ᶜ v ->
  concore_expr v.
Proof.
  intros Γ e v Henv Hcon Heval.
  unfold eval_con in Heval.
  destruct concore_eval_closed_mut as [Heval_closed _].
  apply Heval_closed with (Φ := pc_true) (Γ := Γ) (e := e); auto.
Qed.

(** Closed ConCore expressions evaluate to ConCore values *)
Corollary concore_eval_closed_top : forall e v,
  concore_expr e ->
  ⊢ᶜ e ⇓ᶜ v ->
  concore_expr v.
Proof.
  intros e v Hcon Heval.
  apply (concore_eval_closed · e v); auto.
  constructor.
Qed.

(** Closed Source System FC expressions evaluate to ConCore values *)
Corollary source_eval_closed : forall e v,
  source_expr e ->
  ⊢ᶜ e ⇓ᶜ v ->
  concore_expr v.
Proof.
  intros e v Hsrc Heval.
  apply (concore_eval_closed_top e v); auto.
  apply source_is_concore. assumption.
Qed.

(** ========================================================================= *)
(** 9. SMT Valuations and Concrete Instantiation                               *)
(** ========================================================================= *)

(**
  An SMT valuation σ maps symbolic variables to concrete terms.
  Under valuation σ and path condition Φ:
  1. Symbolic variables are instantiated to concrete values: σ(x).
  2. Symbolic branching (EIf ec et ef) collapses to the single feasible
     branch according to whether σ ⊨ ec or σ ⊨ ¬ec.
  3. The resulting expression e_con contains no EIf and belongs to ConCore.
*)

(** SMT valuation mapping symbolic variable names to concrete expressions *)
(**
  SMT valuation: a model returned by the solver assigns every symbolic
  variable a value of its sort, and the values of an SMT sort are exactly the
  literals. The old type var -> expr was too generous, in three ways that all
  matter for soundness:

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
Definition valuation : Type := var -> lit.

(**
  The symbolic variables of a run: the SMT-level unknowns the symbolic
  execution is parametric in. FIXED for a whole derivation.

  Why a fixed set and not the evaluation environment Γ. "x is symbolic" has
  to mean the same thing everywhere in one derivation, and in SymCore it does
  not if it is read off Γ. Rule Var evaluates a closure body in the STORED
  environment Γ' but the surrounding judgement lives in the AMBIENT
  environment Γ, and SymCore's environments are raw association lists with no
  freshness discipline, so a variable can be unbound (hence symbolic) in Γ'
  and bound in Γ. dev/probe1.v exhibits exactly that: Γ binds x to the
  closure (∅, y) and also binds y, so the value y of that closure is symbolic
  where it is produced and captured where it is used. Indexing concretion by
  Γ therefore has no sound transport across Rule Var.

  Indexing by a fixed symvars instead makes concretion environment
  independent, and the freshness discipline SymCore lacks is recovered where
  it belongs: every binder in a term or environment related by `contains` is
  required to be non-symbolic. That requirement lives inside `contains` and
  `contains_env`, so the soundness statement needs no extra hypothesis of its
  own.
*)
Definition symvars : Type := var -> bool.

(** An environment respects S when it binds no symbolic variable. Derivable
    from contains_env (see contains_env_sym_free), never assumed. *)
Definition sym_free_env (S : symvars) (Γ : environment) : Prop :=
  forall x, S x = true -> lookup_env Γ x = None.

Lemma sym_free_env_empty : forall S, sym_free_env S ·.
Proof. intros S x _. reflexivity. Qed.

Parameter models : valuation -> path_condition -> Prop.

Notation "σ '⊨' Φ" := (models σ Φ) (at level 70, no associativity).

(** A satisfiable model implies SMT satisfiability *)
Axiom models_sat : forall σ Φ,
  σ ⊨ Φ -> sat Φ = true.

(** SMT solver semantics: valuation satisfies conjunction iff it satisfies both conjuncts *)
Axiom models_and_iff : forall σ Φ1 Φ2,
  σ ⊨ (Φ1 ∧ Φ2) <-> σ ⊨ Φ1 /\ σ ⊨ Φ2.

(**
  SMT solver evaluation on boolean conditions, RELATIVE TO THE SYMBOLIC
  VARIABLES the condition may mention.

  The S parameter is not decoration. expr_to_pc Γ (EVar x) is None exactly
  when Γ binds x, so "e denotes a path-condition formula" is only stable if
  the variables of e are known not to be bound. The previous models_cond had
  no such parameter and its totality axiom quantified over EVERY Γ; since one
  can always exhibit a Γ that binds x, that made models_cond σ e refutable
  for ANY e mentioning a variable - which is to say, for exactly the
  conditions symbolic execution exists to reason about.
*)
(**
  e denotes the formula pc: read in any environment that binds no symbolic
  variable, e converts to pc. Quantifying over those environments rather than
  fixing one is what makes the judgement scope independent, and it is the
  reason S appears. Dropping S and reading e in the empty environment alone
  would admit a condition whose variables the ambient environment captures,
  and eval_models_cond then forces models to be empty on variable atoms; see
  the note on eval_models_cond below.
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

(** Conversely, a denoted condition is judged exactly as its formula is. *)
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

(** Whenever the SMT solver can judge a condition's truth value at all, that
    condition is expressible as a path-condition formula in every environment
    that binds none of the symbolic variables: expr_to_pc never fails on a
    judgeable condition read in a scope that does not capture it. *)
Lemma models_cond_total : forall σ S Γ e,
  sym_free_env S Γ ->
  models_cond σ S e \/ models_not_cond σ S e ->
  exists pc, expr_to_pc Γ e = Some pc.
Proof.
  intros σ S Γ e Hfree [[pc [Hden _]] | [pc [Hden _]]];
    exists pc; apply Hden; exact Hfree.
Qed.

(** A condition the solver can judge, read in a scope that does not capture
    it, is solvable there. This is what rules out every evaluation rule
    except App-Prim in eval_models_cond below. *)
Lemma models_cond_solvable : forall σ S Γ e,
  sym_free_env S Γ -> models_cond σ S e \/ models_not_cond σ S e -> Solvable Γ e.
Proof.
  intros σ S Γ e Hfree Hj.
  destruct (models_cond_total σ S Γ e Hfree Hj) as [pc Hpc].
  eapply expr_to_pc_solvable. exact Hpc.
Qed.

(** ------------------------------------------------------------------------- *)
(** 9.0 The SMT Value of a Term                                               *)
(** ------------------------------------------------------------------------- *)

(**
  The SMT theory's own reading of a primitive operation: the literal the
  solver gives to that operation applied to literal arguments. It is external
  to this development in exactly the way lit and primop already are, and it
  is the only new opaque constant the repair needs.
*)
Parameter prim_value : primop -> list lit -> lit.

(** The value a model gives to a path-condition formula. *)
Fixpoint pc_value (σ : valuation) (pc : path_condition) : lit :=
  match pc with
  | PCVar x => σ x
  | PCLit l => l
  | PCPrim p args => prim_value p (map (pc_value σ) args)
  end.

(**
  e has SMT value l under σ: e reads off a formula in every scope that does
  not capture it, and the model gives that formula the value l. Reusing
  `denotes` rather than introducing a second evaluator keeps the scoping
  discipline of S, and keeps the new notion tied to the formulas the solver
  is actually asked about.
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

Lemma denote_symvar : forall σ S x, S x = true -> denote σ S (EVar x) (σ x).
Proof.
  intros σ S x Hx. exists (PCVar x). split; [| reflexivity].
  intros Γ Hfree. simpl. rewrite (Hfree x Hx). reflexivity.
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
  (** A non-symbolic variable stands for itself on both sides *)
  | Cont_Var_Bound : forall x,
      S x = false ->
      contains σ S (EVar x) (EVar x)

  (** A symbolic variable is instantiated to its value under σ *)
  | Cont_Var_Sym : forall x,
      S x = true ->
      contains σ S (EVar x) (ELit (σ x))

  (** Literals, Primitives, Constructors, Coercions, Types, Bottoms *)
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
  | Cont_Clos : forall Γs Γc x bodys bodyc,
      S x = false ->
      contains_env σ S Γs Γc ->
      contains σ S bodys bodyc ->
      contains σ S (EClos Γs x bodys) (EClos Γc x bodyc)
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

    The premises say exactly when the semantic rule is needed. The term must
    be a SATURATED application of a primitive operation, because that is the
    only shape whose concrete instance is not already fixed by the syntax: a
    literal is its own instance, a symbolic variable goes to its value under
    σ by Cont_Var_Sym, and a bare primitive operation is a function, not a
    value of SMT sort. The term must also NOT be closed (smt_ground es =
    false): a closed SMT term mentions no variable, so instantiation does
    nothing to it and the structural rules already relate it to itself.

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

Ltac kill_denote :=
  match goal with
  | [ Hun : unspool_app ?e (@nil expr) = (EPrimOp _, _),
      Hg : smt_ground ?e = false |- _ ] =>
      destruct (cont_denote_is_app e _ _ Hun Hg) as [? [? ?]]; discriminate
  end.

(** Aliases for compatibility *)
Notation instantiates := contains.
Notation instantiates_alt := contains_alt.
Notation instantiates_env := contains_env.

(** An environment matched by concretion binds no symbolic variable. This is
    the scoping fact that makes models_cond_total applicable; it is PROVED
    from contains_env, not assumed. *)
Lemma contains_env_sym_free : forall σ S Γs Γc,
  contains_env σ S Γs Γc -> sym_free_env S Γs /\ sym_free_env S Γc.
Proof.
  intros σ S Γs Γc H.
  induction H as [| x Γs Γc es ec rest_s rest_c Hx Henv IHenv Hcont Hcon Hrest IHrest].
  - split; intros y Hy; reflexivity.
  - destruct IHrest as [IHs IHc]. split; intros y Hy; simpl;
      destruct (string_dec y x) as [Heq | Hneq];
      [ subst; rewrite Hx in Hy; discriminate | apply IHs; exact Hy
      | subst; rewrite Hx in Hy; discriminate | apply IHc; exact Hy ].
Qed.

(** Concretion matches environment domains exactly *)
Lemma contains_env_lookup_none : forall σ S Γs Γc x,
  contains_env σ S Γs Γc ->
  lookup_env Γs x = None ->
  lookup_env Γc x = None.
Proof.
  intros σ S Γs Γc x H.
  induction H as [| y Γs' Γc' es ec rest_s rest_c Hy Henv IHenv Hcont Hcon Hrest IHrest];
    intros Hnone.
  - reflexivity.
  - simpl in *. destruct (string_dec x y); [discriminate | apply IHrest; exact Hnone].
Qed.

(** ------------------------------------------------------------------------- *)
(** 9.0 SMT and Coercion Solver Behaviors on Concretion                       *)
(** ------------------------------------------------------------------------- *)

(** SMT solver behavior: primitive operations preserve concretion *)
Axiom reduce_prim_contains : forall σ S p args_s args_c,
  Forall2 (contains σ S) args_s args_c ->
  contains σ S (reduce_prim p args_s) (reduce_prim p args_c).

(**
  SMT solver behavior: reducing a primitive application preserves its SMT
  value. This is the correctness statement for the external reducer, and it
  is what lets the reducer COMPUTE. The old development had no such contract,
  so the only way a reduced term could stay related to its concrete
  counterpart was to be syntactically the same term, which is why
  reduce_prim was forced never to compute.
*)
Axiom reduce_prim_denote : forall σ S p args ls,
  Forall2 (denote σ S) args ls ->
  denote σ S (reduce_prim p args) (prim_value p ls).

(**
  SMT solver behavior: when the reducer's answer mentions no variable, it is
  a value. A closed SMT term is a number the solver already knows, and a
  reducer that returned an unevaluated closed application would simply have
  stopped early. This is the one direction in which "reduce_prim computes" is
  an assumption rather than a permission.
*)
Axiom reduce_prim_ground_value : forall p args,
  smt_ground (reduce_prim p args) = true ->
  exists l, reduce_prim p args = ELit l.

(** Grisette state merging soundness (Lemma A.4 in the paper) *)
Axiom merge_contains : forall σ S es ec,
  contains σ S es ec ->
  contains σ S (merge es) ec.

(** Coercion cast simplification preserves concretion (Lemma A.5 in the paper) *)
Axiom cast_expr_contains : forall σ S es ec γ,
  contains σ S es ec ->
  contains σ S (cast_expr es γ) (cast_expr ec γ).

(**
  SMT condition truth preservation across evaluation, FOR MODELS OF THE PATH
  CONDITION THE EVALUATION RAN UNDER.

  The hypothesis σ ⊨ Φ is what makes this an assumption about the solver
  rather than a falsehood. Rule Prune lets any expression reduce to
  EBot BUnreachable whenever sat Φ = false, and EBot has no path-condition
  formula, so without tying σ to Φ this axiom said that every condition
  becomes unjudgeable as soon as ONE unsatisfiable path condition exists -
  which in turn made every symbolic branch unconcretisable. With σ ⊨ Φ,
  models_sat gives sat Φ = true and Rule Prune cannot fire.

  The hypothesis sym_free_env S Γ is load bearing for the same reason, and
  only became so when models_cond stopped being abstract. Without it, take Γ
  binding x and evaluate the condition x by Rule Var to EBot BUndefined,
  which denotes no formula: the axiom would then prove that no model
  satisfies the atom x, that is, it would empty out models on variables and
  make the whole non-vacuity suite of §11 hollow. See
  eval_models_cond_residue below for what is left once the hypothesis is
  present: exactly one rule, App-Prim. So what these two now assume, beyond
  what is proved, is that reduce_prim preserves both the denotation of a
  condition and its truth under the model - an SMT solver property, which is
  what reduce_prim is.
*)
Axiom eval_models_cond : forall Φ Γ S ec ec' σ,
  σ ⊨ Φ -> sym_free_env S Γ ->
  Φ ; Γ ⊢ ec ⇓ ec' -> models_cond σ S ec -> models_cond σ S ec'.

Axiom eval_models_not_cond : forall Φ Γ S ec ec' σ,
  σ ⊨ Φ -> sym_free_env S Γ ->
  Φ ; Γ ⊢ ec ⇓ ec' -> models_not_cond σ S ec -> models_not_cond σ S ec'.

(**
  Taking apart a derivation that is fixed at the unlimited budget.

  `inversion` on a hypothesis of the form eval Inf ... already drops Rule
  Out-Of-Fuel, because that rule writes Fin 0 in its conclusion and Fin 0
  cannot unify with Inf. `destruct` and `induction` do not: they first
  generalise the fuel index into a variable, so Rule Out-Of-Fuel comes back as
  a case and every recursive premise arrives at dec f instead of Inf.

  The two tactics below keep the index. They name it, remember the equation
  that says the name is Inf, and use that equation to kill the out-of-fuel
  case. Use them for any lemma that is true only at the unlimited budget.
*)
Ltac inf_induction H :=
  let k := fresh "kf" in
  let Hk := fresh "Hkf" in
  remember Inf as k eqn:Hk in H;
  induction H; try discriminate Hk; subst.

Ltac inf_destruct H :=
  let k := fresh "kf" in
  let Hk := fresh "Hkf" in
  remember Inf as k eqn:Hk in H;
  revert Hk; destruct H; intro Hk; try discriminate Hk; subst.

(** The residue of the two axioms above: under their own hypotheses, an
    evaluation step out of a judgeable condition either changes nothing or is
    a single application of Rule App-Prim. Every other rule is excluded, by
    solvability or by Rule Prune being unreachable under a model.

    Unlimited budget only: at Fin 0 Rule Out-Of-Fuel answers EBot BUndefined,
    which is neither the condition itself nor a primitive reduction. *)
Lemma eval_models_cond_residue : forall Φ Γ S ec ec' σ,
  σ ⊨ Φ -> sym_free_env S Γ -> Φ ; Γ ⊢ ec ⇓ ec' ->
  models_cond σ S ec \/ models_not_cond σ S ec ->
  ec' = ec
  \/ (exists p args args',
        unspool_app ec [] = (EPrimOp p, args)
        /\ length args = primop_arity p
        /\ Forall2 (eval Inf Φ Γ) args args'
        /\ ec' = reduce_prim p args').
Proof.
  intros Φ Γ S ec ec' σ Hmod Hfree Heval Hj.
  assert (Hsolv : Solvable Γ ec) by (eapply models_cond_solvable; eassumption).
  inf_destruct Heval; try (exfalso; inversion Hsolv; fail).
  - exfalso. inversion Hsolv as [| y Hnone | |]; subst. congruence.
  - left; reflexivity.
  - left; reflexivity.
  - exfalso. inversion Hsolv as [| | | f a Hop Hf Ha]; subst. discriminate.
  - exfalso. inversion Hsolv as [| | | f a Hop Hf Ha]; subst.
    apply H. apply Whnf_Solvable. exact Hf.
  - right. exists p, args, args'. repeat split; assumption.
  - exfalso. inversion Hsolv as [| | | f a Hop Hf Ha]; subst. discriminate.
  - exfalso. inversion Hsolv as [| | | f a Hop Hf Ha]; subst. discriminate.
  - exfalso. apply models_sat in Hmod. congruence.
Qed.


(** Substitution on coercions and types preserves concretion under matched environments *)
Axiom subst_coerc_contains_env : forall σ S Γs Γc γ,
  contains_env σ S Γs Γc ->
  contains σ S (ECoercion (subst_coerc Γs γ)) (ECoercion (subst_coerc Γc γ)).

Axiom subst_type_contains_env : forall σ S Γs Γc τ,
  contains_env σ S Γs Γc ->
  contains σ S (EType (subst_type Γs τ)) (EType (subst_type Γc τ)).

(**
  eval_prim_args_sound and fold_alts_contains used to be axioms here. Both are
  now proved (see concore_soundness_fix / concore_soundness_fold_fix below):
  the missing ingredient was not an external SMT/Grisette fact but a
  strengthened induction principle that threads soundness through the
  Forall2 argument list of Eval_AppPrim and the mutual eval/fold_alts
  recursion, which Coq's auto-derived scheme does not provide on its own.
*)

(** ------------------------------------------------------------------------- *)
(** 9.1 Proven Lemmas on SMT Models, Inversion, and Contexts                 *)
(** ------------------------------------------------------------------------- *)

(** 9.1.1 Logical Properties of SMT Models *)

Lemma models_and : forall σ Φ1 Φ2,
  σ ⊨ Φ1 -> σ ⊨ Φ2 -> σ ⊨ (Φ1 ∧ Φ2).
Proof.
  intros σ Φ1 Φ2 H1 H2. apply models_and_iff. split; assumption.
Qed.

Lemma models_and_l : forall σ Φ1 Φ2, σ ⊨ (Φ1 ∧ Φ2) -> σ ⊨ Φ1.
Proof.
  intros σ Φ1 Φ2 H. apply models_and_iff in H. destruct H; assumption.
Qed.

Lemma models_and_r : forall σ Φ1 Φ2, σ ⊨ (Φ1 ∧ Φ2) -> σ ⊨ Φ2.
Proof.
  intros σ Φ1 Φ2 H. apply models_and_iff in H. destruct H; assumption.
Qed.

(** 9.1.2 Environment and Closure Context Lemmas *)

(** Matched symbolic environments have concrete concretion environments *)
Lemma contains_env_concrete : forall σ S Γs Γc,
  contains_env σ S Γs Γc -> concrete_env Γc.
Proof.
  intros σ S Γs Γc H.
  induction H; [constructor | constructor; assumption].
Qed.

(** Bound variables in the environment cannot be replaced by symbolic valuation *)
Lemma contains_var_bound : forall σ S Γs x Γ's es ec,
  sym_free_env S Γs ->
  lookup_env Γs x = Some (Γ's, es) ->
  contains σ S (EVar x) ec ->
  ec = EVar x.
Proof.
  intros σ S Γs x Γ's es ec Hfree Hlook Hcont.
  inversion Hcont; subst; [reflexivity | | kill_denote].
  match goal with
  | [ HS : S x = true |- _ ] =>
      specialize (Hfree x HS); rewrite Hlook in Hfree; discriminate
  end.
Qed.

(** Dually: a symbolic variable is instantiated to its value under σ, and to
    nothing else. This is the rule that makes the theorem say something about
    genuinely symbolic programs. *)
Lemma contains_var_sym : forall σ S x ec,
  S x = true ->
  contains σ S (EVar x) ec ->
  ec = ELit (σ x).
Proof.
  intros σ S x ec Hsym Hcont.
  inversion Hcont; subst; [congruence | congruence | kill_denote].
Qed.

(** Environment lookup preserves concore_expr *)
Lemma lookup_env_concore : forall σ S Γs Γc x Γ's es Γ'c ec,
  contains_env σ S Γs Γc ->
  lookup_env Γs x = Some (Γ's, es) ->
  lookup_env Γc x = Some (Γ'c, ec) ->
  concore_expr ec.
Proof.
  intros σ S Γs Γc x Γ's es Γ'c ec Henv.
  revert Γ's es Γ'c ec.
  induction Henv; intros Γ's es' Γ'c ec' Hlooks Hlookc.
  - simpl in Hlooks. discriminate.
  - simpl in Hlooks, Hlookc.
    destruct (String.string_dec x x0).
    + inversion Hlooks; inversion Hlookc; subst.
      assumption.
    + apply IHHenv2 with (Γ's := Γ's) (es := es') (Γ'c := Γ'c) (ec := ec'); assumption.
Qed.

(** 9.1.3 Concretion Inversion and Lookup Properties *)

Lemma contains_lookup_env : forall σ S Γs Γc x Γ's es,
  contains_env σ S Γs Γc ->
  lookup_env Γs x = Some (Γ's, es) ->
  exists Γ'c ec,
    lookup_env Γc x = Some (Γ'c, ec) /\
    contains_env σ S Γ's Γ'c /\
    contains σ S es ec.
Proof.
  intros σ S Γs Γc x Γ's es Henv.
  revert Γ's es.
  induction Henv; intros Γ's es' Hlook.
  - simpl in Hlook. discriminate.
  - simpl in Hlook. simpl.
    destruct (String.string_dec x x0).
    + inversion Hlook; subst.
      exists Γc, ec. split; [reflexivity |].
      split; assumption.
    + apply IHHenv2. assumption.
Qed.

Lemma contains_lit_inv : forall σ S l ec,
  contains σ S (ELit l) ec -> ec = ELit l.
Proof.
  intros σ S l ec H. inversion H; subst; [reflexivity | kill_denote].
Qed.

Lemma contains_con_inv : forall σ S d ec,
  contains σ S (ECon d) ec -> ec = ECon d.
Proof.
  intros σ S d ec H. inversion H; subst; [reflexivity | kill_denote].
Qed.

Lemma contains_primop_inv : forall σ S p ec,
  contains σ S (EPrimOp p) ec -> ec = EPrimOp p.
Proof.
  intros σ S p ec H. inversion H; subst; [reflexivity | kill_denote].
Qed.

Lemma contains_lam_inv : forall σ S x body ec,
  contains σ S (ELam x body) ec ->
  exists bodyc, ec = ELam x bodyc /\ S x = false /\ contains σ S body bodyc.
Proof.
  intros σ S x body ec H. inversion H; subst; [| kill_denote].
  exists bodyc. split; [reflexivity | split; assumption].
Qed.

Lemma contains_clos_inv : forall σ S Γs x body ec,
  contains σ S (EClos Γs x body) ec ->
  exists Γc bodyc, ec = EClos Γc x bodyc /\ S x = false /\
    contains_env σ S Γs Γc /\
    contains σ S body bodyc.
Proof.
  intros σ S Γs x body ec H. inversion H; subst; [| kill_denote].
  exists Γc, bodyc. split; [reflexivity | auto].
Qed.

(**
  An application is the one shape the semantic rule can also produce, so the
  inversion is now a disjunction. The second alternative carries Solvable Γ fs,
  which is what every caller uses to rule it out: a cast, a closure or a
  bottom in function position is not solvable, and neither is a function that
  Rule App-Spine has just declared not to be in WHNF.
*)
Lemma contains_app_inv : forall σ S Γ fs as_ ec,
  sym_free_env S Γ ->
  contains σ S (EApp fs as_) ec ->
  (exists fc ac, ec = EApp fc ac /\ contains σ S fs fc /\ contains σ S as_ ac)
  \/ (Solvable Γ fs /\ exists p args l,
        unspool_app (EApp fs as_) [] = (EPrimOp p, args) /\
        length args = primop_arity p /\
        smt_ground (EApp fs as_) = false /\
        denote σ S (EApp fs as_) l /\
        ec = ELit l).
Proof.
  intros σ S Γ fs as_ ec Hfree H. inversion H; subst.
  - left. exists f_c, a_c. split; [reflexivity | auto].
  - right.
    match goal with
    | [ Hden : denote σ S (EApp fs as_) ?l |- _ ] =>
        assert (Hsolv : Solvable Γ (EApp fs as_));
          [ destruct Hden as [pc [Hd _]];
            exact (expr_to_pc_solvable Γ (EApp fs as_) pc (Hd Γ Hfree))
          | ]
    end.
    inversion Hsolv as [| | | f a Hop Hf Ha]; subst.
    split; [exact Hf |].
    eexists; eexists; eexists.
    split; [eassumption |]. split; [eassumption |]. split; [eassumption |].
    split; [eassumption | reflexivity].
Qed.

Lemma contains_cast_inv : forall σ S es γ ec,
  contains σ S (ECast es γ) ec ->
  exists ec', ec = ECast ec' γ /\ contains σ S es ec'.
Proof.
  intros σ S es γ ec H. inversion H; subst; [| kill_denote].
  exists ec0. split; [reflexivity | assumption].
Qed.

Lemma contains_case_inv : forall σ S ess altss ec,
  contains σ S (ECase ess altss) ec ->
  exists esc altsc, ec = ECase esc altsc /\ contains σ S ess esc
    /\ Forall2 (contains_alt σ S) altss altsc.
Proof.
  intros σ S ess altss ec H. inversion H; subst; [| kill_denote].
  exists esc, altsc. split; [reflexivity | auto].
Qed.

(** 9.1.4 Proven Semantic Simulation Lemmas *)

(** Higher-order coercion pushing simulation (Proven Lemma using Rule Eval_AppCast) *)
Lemma eval_app_cast_sound : forall Φ Γs Γc σ S ef γ ea γ_a γ_r er e_con,
  σ ⊨ Φ ->
  contains_env σ S Γs Γc ->
  contains σ S (EApp (ECast ef γ) ea) e_con ->
  concore_expr e_con ->
  decomp_coerc_arrow γ = Some (γ_a, γ_r) ->
  Φ ; Γs ⊢ ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r ⇓ er ->
  (forall (Γc : environment) (σ : valuation) (e_con : expr),
    σ ⊨ Φ ->
    contains_env σ S Γs Γc ->
    contains σ S (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r) e_con ->
    concore_expr e_con ->
    exists v_con : expr,
      Γc ⊢ᶜ e_con ⇓ᶜ v_con /\ contains σ S er v_con) ->
  exists v_con,
    Γc ⊢ᶜ e_con ⇓ᶜ v_con /\ contains σ S er v_con.
Proof.
  intros Φ Γs Γc σ S ef γ ea γ_a γ_r er e_con Hmod Henv Hcont Hcon Hdecomp Heval_pushed_s IH.
  assert (Hfree : sym_free_env S Γs)
    by (destruct (contains_env_sym_free σ S Γs Γc Henv) as [Hf _]; exact Hf).
  destruct (contains_app_inv σ S Γs (ECast ef γ) ea e_con Hfree Hcont) as
    [[fc [ac [Heq [Hcont_f Hcont_a]]]] | [Hsolv _]];
    [subst e_con | exfalso; exact (solvable_not_cast Γs ef γ Hsolv)].
  apply contains_cast_inv in Hcont_f as [efc [Heq_fc Hcont_ef]]; subst fc.
  inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | ]; subst.
  inversion Hf as [| | | | | | | | efc0 γ0 Hcon_ef | | | | | ]; subst.
  assert (Hcont_pushed : contains σ S (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r)
                                   (ECast (EApp efc (ECast ac (sym_coerc γ_a))) γ_r)).
  { constructor. constructor; [assumption | constructor; assumption]. }
  assert (Hcon_pushed : concore_expr (ECast (EApp efc (ECast ac (sym_coerc γ_a))) γ_r)).
  { constructor. constructor; [assumption | constructor; assumption]. }
  destruct (IH Γc σ (ECast (EApp efc (ECast ac (sym_coerc γ_a))) γ_r) Hmod Henv Hcont_pushed Hcon_pushed) as [v_con [Heval_pushed Hcont_v]].
  exists v_con.
  split; [| exact Hcont_v].
  unfold eval_con in *.
  eapply Eval_AppCast; eassumption.
Qed.

Lemma eval_lit_con : forall Γ l v,
  eval Inf pc_true Γ (ELit l) v -> v = ELit l.
Proof.
  intros Γ l v Heval.
  inversion Heval; subst.
  - reflexivity.
  - rewrite sat_pc_true in H. discriminate.
Qed.

Lemma eval_con_con : forall Γ d v,
  eval Inf pc_true Γ (ECon d) v -> v = ECon d.
Proof.
  intros Γ d v Heval.
  inversion Heval; subst.
  - reflexivity.
  - rewrite sat_pc_true in H. discriminate.
Qed.

Lemma eval_bot_con : forall Γ b v,
  eval Inf pc_true Γ (EBot b) v -> v = EBot b.
Proof.
  intros Γ b v Heval.
  inversion Heval; subst.
  - reflexivity.
  - rewrite sat_pc_true in H. discriminate.
Qed.

Lemma eval_clos_false : forall Γ env x body v,
  eval Inf pc_true Γ (EClos env x body) v -> False.
Proof.
  intros Γ env x body v Heval.
  inversion Heval; subst.
  rewrite sat_pc_true in H. discriminate.
Qed.

(** A variable in WHNF is unbound, hence symbolic, hence its own value.
    (This replaces the former eval_evar_whnf_false, which claimed such a
    variable could not reduce at all. That claim was only true because
    SymCore had no Rule Sym-Var; with Rule Sym-Var it is false.) *)
Lemma eval_evar_whnf_same : forall Γ x v,
  eval Inf pc_true Γ (EVar x) v -> Whnf Γ (EVar x) -> v = EVar x.
Proof.
  intros Γ x v Heval Hwhnf.
  inversion Hwhnf as [e Hsolv | | | | | | | ]; subst.
  inversion Hsolv as [| x0 Hnone | |]; subst.
  destruct (eval_var_inv pc_true Γ x v sat_pc_true Heval)
    as [[Γ' [e' [Hlook _]]] | [_ Heq]].
  - rewrite Hnone in Hlook. discriminate.
  - exact Heq.
Qed.

Lemma eval_primop_false : forall Γ p v,
  eval Inf pc_true Γ (EPrimOp p) v -> False.
Proof.
  intros Γ p v Heval.
  inversion Heval; subst.
  rewrite sat_pc_true in H. discriminate.
Qed.

Lemma eval_coercion_con : forall Γ γ v,
  eval Inf pc_true Γ (ECoercion γ) v -> v = ECoercion (subst_coerc Γ γ).
Proof.
  intros Γ γ v Heval.
  inversion Heval; subst.
  - reflexivity.
  - rewrite sat_pc_true in H. discriminate.
Qed.

Lemma eval_type_con : forall Γ τ v,
  eval Inf pc_true Γ (EType τ) v -> v = EType (subst_type Γ τ).
Proof.
  intros Γ τ v Heval.
  inversion Heval; subst.
  - rewrite sat_pc_true in H. discriminate.
  - reflexivity.
Qed.

Lemma eval_app_coercion_false : forall Γ γ a v,
  eval Inf pc_true Γ (EApp (ECoercion γ) a) v -> False.
Proof.
  intros Γ γ a v Heval.
  inversion Heval; subst.
  - apply H1. apply Whnf_Coercion.
  - match goal with
    | [ H : unspool_app (EApp _ _) [] = _ |- _ ] =>
        simpl in H; discriminate
    end.
  - rewrite sat_pc_true in H. discriminate.
Qed.

Lemma eval_app_type_false : forall Γ τ a v,
  eval Inf pc_true Γ (EApp (EType τ) a) v -> False.
Proof.
  intros Γ τ a v Heval.
  inversion Heval; subst.
  - apply H1. apply Whnf_Type.
  - match goal with
    | [ H : unspool_app (EApp _ _) [] = _ |- _ ] =>
        simpl in H; discriminate
    end.
  - rewrite sat_pc_true in H. discriminate.
Qed.

Lemma eval_app_lit_false : forall Γ l a v,
  eval Inf pc_true Γ (EApp (ELit l) a) v -> False.
Proof.
  intros Γ l a v Heval.
  inversion Heval; subst.
  - apply H1. apply Whnf_Solvable. apply Solvable_Lit.
  - match goal with
    | [ H : unspool_app (EApp _ _) [] = _ |- _ ] =>
        simpl in H; discriminate
    end.
  - rewrite sat_pc_true in H. discriminate.
Qed.

Lemma eval_app_con_false : forall Γ d a v,
  eval Inf pc_true Γ (EApp (ECon d) a) v -> False.
Proof.
  intros Γ d a v Heval.
  inversion Heval; subst.
  - apply H1. apply Whnf_Con.
  - match goal with
    | [ H : unspool_app (EApp _ _) [] = _ |- _ ] =>
        simpl in H; discriminate
    end.
  - rewrite sat_pc_true in H. discriminate.
Qed.

Lemma not_whnf_case : forall Γ es alts,
  ~ Whnf Γ (ECase es alts).
Proof.
  intros Γ es alts Hw.
  inversion Hw; subst.
  inversion H.
Qed.

Lemma not_op_app_not_whnf : forall Γ f a,
  is_op_app (EApp f a) = false ->
  ~ Whnf Γ (EApp f a).
Proof.
  intros Γ f a Hnop Hw.
  inversion Hw as [e Hsolv | | | | | | | ]; subst.
  inversion Hsolv as [| | | f' a' Hop Hsf Hsa]; subst.
  rewrite Hop in Hnop. discriminate.
Qed.

(** A branch stays a branch: only Rule If applies to one, and it rebuilds a
    branch. Rule Prune is the other candidate and the path condition holds. *)
Lemma eval_preserves_if : forall Φ Γ e v,
  Φ ; Γ ⊢ e ⇓ v ->
  sat Φ = true ->
  is_if e = true ->
  is_if v = true.
Proof.
  intros Φ Γ e v Heval Hsat Hif.
  destruct e; try discriminate.
  inversion Heval; subst; [reflexivity | rewrite Hsat in *; discriminate].
Qed.

(**
  An application whose operator is a branch has no value at all. Rule
  App-Spine is the only rule that could give it one, and it puts the value
  of the branch - another branch - back in operator position, so no
  derivation ever ends.

  Unlimited budget only, so the proof goes by inf_induction. "No derivation
  ever ends" is exactly what a finite budget breaks: at Fin 0 Rule
  Out-Of-Fuel ends it with EBot BUndefined.
*)
Lemma eval_app_if_false : forall Φ Γ e v,
  Φ ; Γ ⊢ e ⇓ v ->
  sat Φ = true ->
  forall ef ea, e = EApp ef ea -> is_if ef = true -> False.
Proof.
  intros Φ Γ e v Heval. inf_induction Heval;
    intros Hsat f0 a0 Heq Hif; try discriminate.
  - (* Eval_AppAbs *) injection Heq as Hf Ha. subst f0. discriminate.
  - (* Eval_AppSpine *)
    injection Heq as Hf Ha. subst f0 a0.
    apply (IHHeval2 eq_refl Hsat ef' ea eq_refl).
    exact (eval_preserves_if Φ Γ ef ef' Heval1 Hsat Hif).
  - (* Eval_AppPrim *)
    injection Heq as Hf Ha. subst f0 a0.
    destruct ef; try discriminate;
      simpl in H; injection H as Hh _; discriminate.
  - (* Eval_AppCast *) injection Heq as Hf Ha. subst f0. discriminate.
  - (* Eval_AppBot *) injection Heq as Hf Ha. subst f0. discriminate.
  - (* Eval_Prune *) rewrite Hsat in H. discriminate.
Qed.

(**
  Concretion does not invent a cast. Every rule of the relation keeps the
  head constructor, and the two rules that do not - a symbolic variable and
  an SMT term both go to a literal - cannot start from a cast. The one rule
  that changes the shape is branch resolution, which is why the operator
  must not be a branch.
*)
Lemma contains_is_cast : forall σ S es ec,
  contains σ S es ec ->
  is_if es = false ->
  is_cast ec = is_cast es.
Proof.
  intros σ S es ec Hcont Hif.
  inversion Hcont; subst; simpl in *; try reflexivity; try discriminate.
  destruct es; simpl in *; try reflexivity.
  injection H as Hh _. discriminate.
Qed.

Lemma eval_con_app_whnf : forall Γc fc ac v_f v_con,
  concore_expr fc ->
  Whnf Γc fc ->
  is_op_app fc = false ->
  is_cast fc = false ->
  pc_true ; Γc ⊢ fc ⇓ v_f ->
  pc_true ; Γc ⊢ EApp v_f ac ⇓ v_con ->
  pc_true ; Γc ⊢ EApp fc ac ⇓ v_con.
Proof.
  intros Γc fc ac v_f v_con Hcon Hwhnf Hnop Hnocast Heval_f Heval_app.
  destruct fc.
  - assert (Heqv : v_f = EVar v) by (eapply eval_evar_whnf_same; eassumption).
    subst v_f. exact Heval_app.
  - apply eval_lit_con in Heval_f; subst.
    exfalso. apply (eval_app_lit_false _ _ _ _ Heval_app).
  - exfalso. eapply eval_primop_false; eassumption.
  - apply eval_con_con in Heval_f; subst.
    exfalso. apply (eval_app_con_false _ _ _ _ Heval_app).
  - exfalso. apply (not_op_app_not_whnf Γc fc1 fc2 Hnop Hwhnf).
  - apply not_whnf_lam in Hwhnf. contradiction.
  - exfalso. eapply eval_clos_false; eassumption.
  - apply not_whnf_case in Hwhnf. contradiction.
  - (* a cast operator: the concretion of a non-cast is never a cast *)
    discriminate Hnocast.
  - apply eval_coercion_con in Heval_f; subst.
    exfalso. apply (eval_app_coercion_false _ _ _ _ Heval_app).
  - apply eval_type_con in Heval_f; subst.
    exfalso. apply (eval_app_type_false _ _ _ _ Heval_app).
  - inversion Hcon.
  - apply eval_bot_con in Heval_f; subst. exact Heval_app.
Qed.

(** An operator spine in WHNF is solvable *)
Lemma whnf_op_app_solvable : forall Γ f a,
  Whnf Γ (EApp f a) -> Solvable Γ (EApp f a).
Proof.
  intros Γ f a Hwhnf. inversion Hwhnf; subst; assumption.
Qed.

(**
  A saturated operator spine reduces by Rule App-Prim, and its reduced
  arguments are still solvable. The second conjunct is what feeds the
  repaired (argument-conditional) reduce_prim_solvable.
*)
Lemma eval_app_primop_head : forall Φ Γ f a v,
  sat Φ = true ->
  Whnf Γ (EApp f a) ->
  is_op_app (EApp f a) = true ->
  eval Inf Φ Γ (EApp f a) v ->
  exists p args', v = reduce_prim p args' /\ Forall (Solvable Γ) args'.
Proof.
  intros Φ Γ f a v Hsat Hwhnf Hop Heval.
  assert (Hsolv : Solvable Γ (EApp f a)) by (apply whnf_op_app_solvable; assumption).
  inversion Heval; subst.
  - simpl in Hop. discriminate.
  - (* Eval_AppSpine *)
    exfalso.
    inversion Hsolv as [| | | f0 a0 Hop0 Hsf Hsa]; subst.
    match goal with
    | [ Hnw : ~ Whnf Γ f |- _ ] => apply Hnw; apply Whnf_Solvable; exact Hsf
    end.
  - (* Eval_AppPrim *)
    exists p, args'. split; [reflexivity |].
    assert (Hsargs : Forall (Solvable Γ) args)
      by (eapply solvable_spine_args; [exact Hsolv | constructor | eassumption]).
    match goal with
    | [ HF : Forall2 (eval _ Φ Γ) args args' |- _ ] =>
        clear -HF Hsargs Hsat;
        induction HF as [| a0 a0' tl tl' Ha Htl IH];
        [ constructor
        | inversion Hsargs as [| b0 btl Hsa Hstl]; subst;
          constructor;
          [ exact (solvable_eval_solvable Inf Φ Γ a0 a0' Ha eq_refl Hsat Hsa)
          | exact (IH Hstl) ] ]
    end.
  - simpl in Hop. discriminate.
  - simpl in Hop. discriminate.
  - rewrite Hsat in H. discriminate.
Qed.

Lemma eval_app_spine_sound : forall Φ Γs Γc σ S ef ea ef' er e_con,
  σ ⊨ Φ ->
  contains_env σ S Γs Γc ->
  contains σ S (EApp ef ea) e_con ->
  concore_expr e_con ->
  ~ Whnf Γs ef ->
  is_cast ef = false ->
  Φ ; Γs ⊢ ef ⇓ ef' ->
  Φ ; Γs ⊢ EApp ef' ea ⇓ er ->
  (forall (Γc : environment) (σ : valuation) (e_con : expr),
    σ ⊨ Φ ->
    contains_env σ S Γs Γc ->
    contains σ S ef e_con ->
    concore_expr e_con ->
    exists v_con : expr,
      Γc ⊢ᶜ e_con ⇓ᶜ v_con /\ contains σ S ef' v_con) ->
  (forall (Γc : environment) (σ : valuation) (e_con : expr),
    σ ⊨ Φ ->
    contains_env σ S Γs Γc ->
    contains σ S (EApp ef' ea) e_con ->
    concore_expr e_con ->
    exists v_con : expr,
      Γc ⊢ᶜ e_con ⇓ᶜ v_con /\ contains σ S er v_con) ->
  exists v_con,
    Γc ⊢ᶜ e_con ⇓ᶜ v_con /\ contains σ S er v_con.
Proof.
  intros Φ Γs Γc σ S ef ea ef' er e_con Hmod Henv Hcont Hcon Hnotwhnf Hnocast Heval1 Heval2 IH1 IH2.
  assert (Hsat : sat Φ = true) by (eapply models_sat; eassumption).
  assert (Hnotif : is_if ef = false).
  { destruct (is_if ef) eqn:Hif; [| reflexivity].
    exfalso. apply (eval_app_if_false Φ Γs (EApp ef' ea) er Heval2 Hsat ef' ea eq_refl).
    exact (eval_preserves_if Φ Γs ef ef' Heval1 Hsat Hif). }
  assert (Hfree : sym_free_env S Γs)
    by (destruct (contains_env_sym_free σ S Γs Γc Henv) as [Hf _]; exact Hf).
  destruct (contains_app_inv σ S Γs ef ea e_con Hfree Hcont) as
    [[fc [ac [Heq [Hcont_f Hcont_a]]]] | [Hsolv _]];
    [subst e_con | exfalso; exact (Hnotwhnf (Whnf_Solvable Γs ef Hsolv))].
  inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | ]; subst.
  destruct (IH1 Γc σ fc Hmod Henv Hcont_f Hf) as [v_f [Heval_f Hcont_vf]].
  assert (Henv_c : concrete_env Γc) by (eapply contains_env_concrete; eassumption).
  assert (Hcon_vf : concore_expr v_f) by (eapply concore_eval_closed; [exact Henv_c | exact Hf | exact Heval_f]).
  assert (Hcont_app2 : contains σ S (EApp ef' ea) (EApp v_f ac)) by (constructor; assumption).
  assert (Hcon_app2 : concore_expr (EApp v_f ac)) by (apply Con_App; assumption).
  destruct (IH2 Γc σ (EApp v_f ac) Hmod Henv Hcont_app2 Hcon_app2) as [v_con [Heval_app2 Hcont_er]].
  exists v_con. split; [| exact Hcont_er].
  assert (Hnocast_c : is_cast fc = false)
    by (rewrite (contains_is_cast σ S ef fc Hcont_f Hnotif); exact Hnocast).
  unfold eval_con in *.
  destruct (whnf_dec Γc fc) as [Hwhnf_c | Hnot_whnf_c].
  - destruct (is_op_app fc) eqn:Hop.
    + destruct fc; try discriminate.
      * simpl in Hop. exfalso. eapply eval_primop_false; eassumption.
      * exfalso.
        eapply eval_app_primop_head in Heval_f as [p [args' [Heq Hsargs]]]; [| exact sat_pc_true | exact Hwhnf_c | exact Hop].
        subst v_f.
        eapply reduce_prim_app_false; [exact Hsargs | exact Heval_app2].
    + eapply eval_con_app_whnf; eassumption.
  - eapply Eval_AppSpine;
      [exact Hnot_whnf_c | exact Hnocast_c | exact Heval_f | exact Heval_app2].
Qed.

(** ------------------------------------------------------------------------- *)
(** 9.2 Symbolic Evaluation Preserves the SMT Value                           *)
(** ------------------------------------------------------------------------- *)

(** The formula of an application splits into the formula of the operator
    spine and the formula of the last argument, in every scope at once. *)
Lemma denotes_app_inv : forall S e1 e2 pc,
  denotes S (EApp e1 e2) pc ->
  exists p pcs pa,
    pc = PCPrim p (pcs ++ [pa]) /\ denotes S e1 (PCPrim p pcs) /\ denotes S e2 pa.
Proof.
  intros S e1 e2 pc Hden.
  pose proof (Hden · (sym_free_env_empty S)) as H0. simpl in H0.
  destruct (expr_to_pc · e1) as [pc1 |] eqn:E1; [| discriminate].
  destruct pc1 as [x | l | p q1];
    try (destruct (expr_to_pc · e2); discriminate).
  destruct (expr_to_pc · e2) as [pa |] eqn:E2; [| discriminate].
  injection H0 as H0. subst pc.
  exists p, q1, pa. split; [reflexivity | split];
    intros Γ Hfree; specialize (Hden Γ Hfree); simpl in Hden;
    destruct (expr_to_pc Γ e1) as [pc1' |] eqn:E1'; try discriminate;
    destruct pc1' as [x' | l' | p' q'];
      try (destruct (expr_to_pc Γ e2); discriminate);
    destruct (expr_to_pc Γ e2) as [pa' |] eqn:E2'; try discriminate.
  - rewrite (expr_to_pc_functional e1 Γ · (PCPrim p' q') (PCPrim p q1) E1' E1).
    reflexivity.
  - rewrite (expr_to_pc_functional e2 Γ · pa' pa E2' E2). reflexivity.
Qed.

(** A term whose formula is a primitive application is an operator spine, and
    its arguments carry the formula's arguments pointwise. *)
Lemma denotes_unspool : forall e S pop pcs qop eargs,
  denotes S e (PCPrim pop pcs) ->
  unspool_app e [] = (EPrimOp qop, eargs) ->
  pop = qop /\ Forall2 (denotes S) eargs pcs.
Proof.
  induction e; intros S pop pcs qop eargs Hden Hun;
    try (pose proof (Hden · (sym_free_env_empty S)) as H0; simpl in H0;
         discriminate H0).
  - pose proof (Hden · (sym_free_env_empty S)) as H0. simpl in H0.
    injection H0 as H0. subst pcs. simpl in Hun. injection Hun as Hq Hargs.
    subst. split; [reflexivity | constructor].
  - destruct (denotes_app_inv S e1 e2 (PCPrim pop pcs) Hden)
      as [p1 [pcs1 [pa [Heq [Hden1 Hden2]]]]].
    injection Heq as Hp Hpcs. subst p1 pcs.
    assert (Hop : is_op_app e1 = true).
    { pose proof (Hden1 · (sym_free_env_empty S)) as H1.
      exact (expr_to_pc_prim_is_op_app · e1 pop pcs1 H1). }
    destruct (is_op_app_unspool e1 Hop) as [p2 [args2 Hun2]].
    pose proof (unspool_app_shift e1 [] [e2] (EPrimOp p2) args2 Hun2) as Hun2'.
    simpl in Hun2'. simpl in Hun. rewrite Hun2' in Hun.
    injection Hun as Hq Hargs. subst qop eargs.
    destruct (IHe1 S pop pcs1 p2 args2 Hden1 Hun2) as [Hpp Hall].
    split; [exact Hpp |].
    apply Forall2_app; [exact Hall | constructor; [exact Hden2 | constructor]].
Qed.

Ltac denote_absurd :=
  exfalso;
  match goal with
  | [ H : denote _ ?S _ _ |- _ ] =>
      let pc := fresh "pc" in let Hd := fresh "Hd" in
      destruct H as [pc [Hd _]];
      specialize (Hd · (sym_free_env_empty S)); simpl in Hd; discriminate Hd
  end.

(**
  Symbolic evaluation of an SMT term preserves its SMT value. This is PROVED,
  not assumed: every evaluation rule except App-Prim is excluded by the shape
  of a denoting term (or, for Rule Prune, by the model of the path
  condition), and App-Prim is exactly reduce_prim_denote applied to arguments
  the recursion has already handled.

  It is a Fixpoint rather than an induction because App-Prim needs the result
  for every argument in its Forall2, which Coq's derived induction principle
  does not strengthen.

  Unlimited budget only, hence the k0 = Inf premise. At Fin 0 Rule
  Out-Of-Fuel answers EBot BUndefined, and expr_to_pc reads no formula off a
  bottom, so the answer denotes nothing.
*)
Fixpoint eval_denote_fix (k0 : fuel) (Φ : path_condition) (Γ : environment) (e e' : expr)
  (Heval : eval k0 Φ Γ e e') {struct Heval} :
  k0 = Inf ->
  forall σ S l,
    σ ⊨ Φ ->
    sym_free_env S Γ ->
    denote σ S e l ->
    denote σ S e' l.
Proof.
  destruct Heval as
    [ kv Φ Γ x Γ' eb eb' Hlookup Heval_x
    | kv Φ Γ x Hnone
    | kv Φ Γ l0
    | kv Φ Γ d
    | kv Φ Γ eb γ eb' Heval_e
    | kv Φ Γ Γ' x eb ea eb' Heval_b
    | kv Φ Γ ef ea ef' er Hnotwhnf Hnoarrow Heval_f Heval_app2
    | kv Φ Γ b
    | kv Φ Γ ef ea p eargs eargs' Hunspool Harity Hargs
    | kv Φ Γ x eb
    | kv Φ Γ ef γ ea γ_a γ_r er Hdecomp Heval_pushed
    | kv Φ Γ b ea
    | kv Φ Γ es alts es' er Heval_es Hfold
    | kv Φ Γ ec et ef ec' et' ef' pc_c Heval_c Hpc Heval_t Heval_f
    | kv Φ Γ γ
    | kv Φ Γ eb Hunsat
    | kv Φ Γ τ
    | Φ Γ eb
    ]; intros Hk0; try discriminate Hk0; subst kv; intros σ S l Hmod Hfree Hden;
    try denote_absurd.
  - (* Eval_Var: a denoting variable is symbolic, so Γ cannot bind it *)
    exfalso. destruct (denote_var_inv σ S x l Hden) as [Hsx _].
    specialize (Hfree x Hsx). rewrite Hlookup in Hfree. discriminate.
  - (* Eval_SymVar *) exact Hden.
  - (* Eval_Lit *) exact Hden.
  - (* Eval_AppSpine: a denoting spine has a solvable, hence WHNF, operator *)
    exfalso. apply Hnotwhnf. apply Whnf_Solvable.
    destruct Hden as [pc [Hd _]].
    pose proof (expr_to_pc_solvable Γ (EApp ef ea) pc (Hd Γ Hfree)) as Hsolv.
    inversion Hsolv as [| | | f a Hop Hf Ha]; subst. exact Hf.
  - (* Eval_AppPrim *)
    destruct Hden as [pc [Hdenotes Hval]].
    assert (Hop : is_op_app (EApp ef ea) = true)
      by (eapply unspool_is_op_app; exact Hunspool).
    destruct (expr_to_pc_op_app (EApp ef ea) · pc Hop
                (Hdenotes · (sym_free_env_empty S))) as [p1 [pcs Hpc]].
    subst pc.
    destruct (denotes_unspool (EApp ef ea) S p1 pcs p eargs Hdenotes Hunspool)
      as [Hp1 Hpcs]. subst p1.
    assert (Hres : Forall2 (denote σ S) eargs' (map (pc_value σ) pcs)).
    { clear Hunspool Harity Hval Hop Hdenotes.
      revert pcs Hpcs.
      induction Hargs as [| a a' atl atl' Ha Htl IHtl]; intros pcs Hpcs.
      - inversion Hpcs; subst. constructor.
      - inversion Hpcs as [| a0 pc0 atl0 pctl Hden_a Hden_tl]; subst.
        simpl. constructor.
        + exact (eval_denote_fix Inf Φ Γ a a' Ha eq_refl σ S (pc_value σ pc0) Hmod Hfree
                   (ex_intro _ pc0 (conj Hden_a eq_refl))).
        + exact (IHtl pctl Hden_tl). }
    rewrite <- Hval. simpl.
    exact (reduce_prim_denote σ S p eargs' (map (pc_value σ) pcs) Hres).
  - (* Eval_Prune: unreachable under a model of the path condition *)
    exfalso. apply models_sat in Hmod. rewrite Hunsat in Hmod. discriminate.
Qed.

Lemma eval_denote : forall Φ Γ σ S e e' l,
  σ ⊨ Φ ->
  sym_free_env S Γ ->
  Φ ; Γ ⊢ e ⇓ e' ->
  denote σ S e l ->
  denote σ S e' l.
Proof.
  intros Φ Γ σ S e e' l Hmod Hfree Heval Hden.
  exact (eval_denote_fix Inf Φ Γ e e' Heval eq_refl σ S l Hmod Hfree Hden).
Qed.

(** ========================================================================= *)
(** 10. Soundness and Completeness of Symbolic Execution                      *)
(** ========================================================================= *)

(**
  Soundness (Rebuttal Formulation):
  For any concrete expression e_con that is contained in a symbolic expression
  e_sym under valuation σ ⊨ Φ, its concrete reduction is contained in the
  symbolic reduction of e_sym.

  Proved as a pair of mutually recursive fixpoints rather than by plain
  induction on the `eval`/`fold_alts` derivation: the Eval_AppPrim case
  needs soundness for every argument in its Forall2 (eval Inf Φ Γ) args args',
  and Eval_Case/FoldAlts_Con need it for the nested eval buried inside
  fold_alts - neither is covered by Coq's auto-derived induction principle
  for a mutually-recursive family, which only strengthens direct recursive
  occurrences, not ones nested inside a Forall2 or the sibling relation.
  Recursing through those manually (via `induction` on the embedded Forall2
  / fold_alts proof, calling back into the very fixpoint being defined) is
  what used to be papered over by the eval_prim_args_sound and
  fold_alts_contains axioms.

  Unlimited budget only, hence the k0 = Inf premise on both fixpoints. The
  conclusion asks for a CONCRETE value that the symbolic value contains, and
  concrete evaluation has no budget of its own: it is fixed at Inf by
  eval_con. At Fin 0 the symbolic side answers EBot BUndefined, which
  contains only a concrete EBot BUndefined, and the concrete expression need
  not reduce to that. Giving the concrete side a budget as well is a later
  stage, not this one.
*)

(** `contains` commutes with `unspool_app`, threading an existing pointwise
    correspondence on the accumulator through the same accumulator on both
    sides. This is what earlier let eval_app_spine_sound derive an arity
    contradiction, and is the structural core of eval_prim_args_sound. *)
(**
  The accumulator must be non-empty and the spine saturated. Both premises
  say the same thing: the term being unspooled is a PROPER SUB-SPINE of a
  saturated application, hence under-applied, hence not itself a value of
  SMT sort, hence not something Cont_Denote could have collapsed to a
  literal. Rule App-Prim, the only caller, supplies both.
*)
Lemma contains_unspool_primop : forall σ S e_sym e_con,
  contains σ S e_sym e_con ->
  forall L_s L_c,
    Forall2 (contains σ S) L_s L_c ->
    L_s <> [] ->
    forall p args,
      unspool_app e_sym L_s = (EPrimOp p, args) ->
      length args = primop_arity p ->
      exists args_c,
        unspool_app e_con L_c = (EPrimOp p, args_c) /\
        Forall2 (contains σ S) args args_c.
Proof.
  induction 1; intros L_s L_c HL Hne p0 args0 Hunspool Harity; simpl in Hunspool;
    try discriminate.
  - injection Hunspool as ? ?; subst.
    exists L_c. split; [reflexivity | exact HL].
  - apply IHcontains1 with (L_s := a_s :: L_s) (L_c := a_c :: L_c);
      [constructor; assumption | discriminate | exact Hunspool | exact Harity].
  - exfalso.
    match goal with
    | [ Hun0 : unspool_app ?e (@nil expr) = (EPrimOp ?q, ?qargs),
        Har0 : length ?qargs = primop_arity ?q |- _ ] =>
        apply (unspool_app_shift e [] L_s) in Hun0; simpl in Hun0;
        rewrite Hun0 in Hunspool; inversion Hunspool; subst;
        rewrite length_app, Har0 in Harity;
        destruct L_s as [| z zs]; [apply Hne; reflexivity | simpl in Harity; lia]
    end.
Qed.

(** Same fact, specialized to a data-constructor head instead of a primitive
    operator - needed for FoldAlts_Con's "the pattern matched" case. *)
Lemma contains_unspool_con : forall σ S e_sym e_con,
  contains σ S e_sym e_con ->
  forall L_s L_c,
    Forall2 (contains σ S) L_s L_c ->
    forall d args,
      unspool_app e_sym L_s = (ECon d, args) ->
      exists args_c,
        unspool_app e_con L_c = (ECon d, args_c) /\
        Forall2 (contains σ S) args args_c.
Proof.
  induction 1; intros L_s L_c HL d0 args0 Hunspool; simpl in Hunspool;
    try discriminate.
  - injection Hunspool as ? ?; subst.
    exists L_c. split; [reflexivity | exact HL].
  - apply IHcontains1 with (L_s := a_s :: L_s) (L_c := a_c :: L_c).
    + constructor; assumption.
    + exact Hunspool.
  - exfalso.
    match goal with
    | [ Hun0 : unspool_app ?e (@nil expr) = (EPrimOp ?q, ?qargs) |- _ ] =>
        apply (unspool_app_shift e [] L_s) in Hun0; simpl in Hun0;
        rewrite Hun0 in Hunspool; discriminate Hunspool
    end.
Qed.

(** Fully general version: whatever head the spine settles on (as long as
    it is not itself an unresolved branch), `contains` relates it to the
    matching head on the concrete side. Needed for FoldAlts_Otherwise's
    "the scrutinee is not this constructor" (negative) case, where the
    target head isn't known in advance.

    The Cont_Var_Sym case is exactly why σ must send a variable to a LITERAL:
    a literal does not unspool further, so the concrete head is the literal
    itself and `contains` still relates the two heads. If σ x could be an
    application or a constructor, the concrete spine would have a different
    head from the symbolic one, and this lemma - with it soundness of Rule
    Case - would fail. *)
Lemma contains_unspool_general : forall σ S e_sym e_con,
  contains σ S e_sym e_con ->
  forall L_s L_c,
    Forall2 (contains σ S) L_s L_c ->
    forall hd hargs,
      unspool_app e_sym L_s = (hd, hargs) ->
      is_if hd = false ->
      (exists head_c args_c,
         unspool_app e_con L_c = (head_c, args_c) /\
         contains σ S hd head_c /\
         Forall2 (contains σ S) hargs args_c)
      \/ (exists l args_c, unspool_app e_con L_c = (ELit l, args_c)).
Proof.
  induction 1; intros L_s L_c HL hd hargs Hunspool Hif; simpl in Hunspool;
    try (left; injection Hunspool as ? ?; subst;
         eexists; exists L_c;
         split; [reflexivity | split; [solve [constructor; assumption] | exact HL]]).
  - (* Cont_App *)
    apply IHcontains1 with (L_s := a_s :: L_s) (L_c := a_c :: L_c).
    + constructor; assumption.
    + exact Hunspool.
    + exact Hif.
  - (* Cont_If_True *) injection Hunspool as ? ?; subst. simpl in Hif. discriminate.
  - (* Cont_If_False *) injection Hunspool as ? ?; subst. simpl in Hif. discriminate.
  - (* Cont_Denote *) right. exists l, L_c. reflexivity.
Qed.

(** `find_alt` looks up alternatives by tag only, and `contains_alt`
    preserves tags exactly, so a symbolic match hit corresponds to a
    concrete match hit on the same tag. *)
Lemma find_alt_contains_alt : forall σ S alts altsc d xs ep,
  Forall2 (contains_alt σ S) alts altsc ->
  find_alt d alts = Some (xs, ep) ->
  exists epc, find_alt d altsc = Some (xs, epc)
    /\ Forall (fun x => S x = false) xs
    /\ contains σ S ep epc.
Proof.
  intros σ S alts altsc d xs ep H.
  induction H as [| a ac alts' altsc' Ha Hrest IH]; intros Hfind.
  - simpl in Hfind; discriminate.
  - simpl in Hfind. destruct a as [d' xs' ep'].
    inversion Ha as [d'' xs'' eps epc Hxs Hcont_ep]; subst.
    simpl. destruct (string_dec d d').
    + inversion Hfind; subst. exists epc. split; [reflexivity | split; assumption].
    + apply IH; assumption.
Qed.

(** Dually, a symbolic match miss is also a concrete match miss. *)
Lemma find_alt_none_contains_alt : forall σ S alts altsc d,
  Forall2 (contains_alt σ S) alts altsc ->
  find_alt d alts = None ->
  find_alt d altsc = None.
Proof.
  intros σ S alts altsc d H.
  induction H as [| a ac alts' altsc' Ha Hrest IH]; intros Hfind.
  - reflexivity.
  - simpl in Hfind. destruct a as [d' xs' ep'].
    inversion Ha as [d'' xs'' eps epc Hxs Hcont_ep]; subst.
    simpl. destruct (string_dec d d'); [discriminate | apply IH; assumption].
Qed.

(** extend_env_multi extended pointwise by contains, argument list by
    argument list, preserves contains_env - needed for FoldAlts_Con's
    pattern body evaluation under the bound constructor arguments. *)
Lemma contains_env_extend_multi : forall σ S xs args_s args_c Γs Γc Γarg_s Γarg_c,
  Forall (fun x => S x = false) xs ->
  contains_env σ S Γs Γc ->
  contains_env σ S Γarg_s Γarg_c ->
  Forall2 (contains σ S) args_s args_c ->
  Forall concore_expr args_c ->
  contains_env σ S (extend_env_multi Γs xs args_s Γarg_s) (extend_env_multi Γc xs args_c Γarg_c).
Proof.
  induction xs as [| x xs' IH];
    intros args_s args_c Γs Γc Γarg_s Γarg_c Hxs Henv Hargenv Hargs Hconcore.
  - simpl. exact Henv.
  - inversion Hxs as [| x0 xs0 Hx Hxs' ]; subst.
    destruct args_s as [| a args_s']; destruct args_c as [| ac args_c'];
      try (inversion Hargs; fail).
    + simpl. exact Henv.
    + simpl. inversion Hargs as [| a0 ac0 args_s'0 args_c'0 Hcont_a Hargs' Heq1 Heq2]; subst.
      inversion Hconcore as [| ac1 args_c'1 Hcon_a Hconcore' ]; subst.
      apply Cont_Env_Extend.
      * exact Hx.
      * exact Hargenv.
      * exact Hcont_a.
      * exact Hcon_a.
      * apply IH; assumption.
Qed.

Fixpoint concore_soundness_fix (k0 : fuel) (Φ : path_condition) (Γs : environment) (e_sym v_sym : expr)
  (Heval : eval k0 Φ Γs e_sym v_sym) {struct Heval} :
  k0 = Inf ->
  forall Γc σ S e_con,
    σ ⊨ Φ ->
    contains_env σ S Γs Γc ->
    contains σ S e_sym e_con ->
    concore_expr e_con ->
    exists v_con,
      Γc ⊢ᶜ e_con ⇓ᶜ v_con /\
      contains σ S v_sym v_con
with concore_soundness_fold_fix (k0 : fuel) (Φ : path_condition) (Γs : environment) (escrut : expr) (alts : list alt) (er : expr)
  (Hfold : fold_alts k0 Φ Γs escrut alts er) {struct Hfold} :
  k0 = Inf ->
  forall Γc σ S esc altsc,
    σ ⊨ Φ ->
    contains_env σ S Γs Γc ->
    concore_expr esc ->
    Forall concore_alt altsc ->
    (exists vc_s, Γc ⊢ᶜ esc ⇓ᶜ vc_s /\ contains σ S escrut vc_s) ->
    Forall2 (contains_alt σ S) alts altsc ->
    exists v_con,
      Γc ⊢ᶜ ECase esc altsc ⇓ᶜ v_con /\ contains σ S er v_con.
Proof.
{
  destruct Heval as
    [ kv Φ Γ x Γ' e e' Hlookup Heval_x
    | kv Φ Γ x Hnone
    | kv Φ Γ l
    | kv Φ Γ d
    | kv Φ Γ e γ e' Heval_e
    | kv Φ Γ Γ' x eb ea eb' Heval_b
    | kv Φ Γ ef ea ef' er Hnotwhnf Hnoarrow Heval_f Heval_app2
    | kv Φ Γ b
    | kv Φ Γ ef ea p args args' Hunspool Harity Hargs
    | kv Φ Γ x e
    | kv Φ Γ ef γ ea γ_a γ_r er Hdecomp Heval_pushed
    | kv Φ Γ b ea
    | kv Φ Γ es alts es' er Heval_es Hfold
    | kv Φ Γ ec et ef ec' et' ef' pc_c Heval_c Hpc Heval_t Heval_f
    | kv Φ Γ γ
    | kv Φ Γ e Hunsat
    | kv Φ Γ τ
    | Φ Γ e
    ]; intros Hk0; try discriminate Hk0; subst kv; intros Γc σ S e_con Hmod Henv Hcont Hcon.
  - (* Eval_Var *)
    assert (Hfree : sym_free_env S Γ)
      by (destruct (contains_env_sym_free σ S Γ Γc Henv) as [Hf _]; exact Hf).
    assert (Heq : e_con = EVar x) by (eapply contains_var_bound; eassumption).
    subst e_con.
    destruct (contains_lookup_env σ S Γ Γc x Γ' e Henv Hlookup) as [Γ'c [ec [Hlookc [Henv' Hcont']]]].
    assert (Hcon' : concore_expr ec) by (apply (lookup_env_concore σ S Γ Γc x Γ' e Γ'c ec Henv Hlookup Hlookc)).
    destruct (concore_soundness_fix Inf Φ Γ' e e' Heval_x eq_refl Γ'c σ S ec Hmod Henv' Hcont' Hcon') as [v_con [Hevalc Hcont_v]].
    exists v_con. split; [| exact Hcont_v].
    unfold eval_con. eapply Eval_Var; eassumption.
  - (* Eval_SymVar: an unbound variable is its own value. Either it is one of
       the symbolic variables, and σ sends it to a literal, which is its own
       value concretely; or it is not, and it stands for itself on both
       sides - the concrete environment leaves it unbound too. *)
    destruct (S x) eqn:Hsx.
    + assert (Heq : e_con = ELit (σ x)) by (eapply contains_var_sym; eassumption).
      subst e_con.
      exists (ELit (σ x)). split.
      * unfold eval_con. apply Eval_Lit.
      * apply Cont_Var_Sym. exact Hsx.
    + assert (Heq : e_con = EVar x).
      { inversion Hcont; subst; [congruence | congruence | kill_denote]. }
      subst e_con.
      exists (EVar x). split.
      * unfold eval_con. apply Eval_SymVar.
        eapply contains_env_lookup_none; eassumption.
      * apply Cont_Var_Bound. exact Hsx.
  - (* Eval_Lit *)
    apply contains_lit_inv in Hcont; subst.
    exists (ELit l). split; [apply Eval_Lit | apply Cont_Lit].
  - (* Eval_Con *)
    apply contains_con_inv in Hcont; subst.
    exists (ECon d). split; [apply Eval_Con | apply Cont_Con].
  - (* Eval_Cast *)
    apply contains_cast_inv in Hcont as [ec [Heq Hcont_e]]; subst.
    inversion Hcon as [| | | | | | | | ec0 γ0 Hcon_e | | | | | ]; subst.
    destruct (concore_soundness_fix Inf Φ Γ e e' Heval_e eq_refl Γc σ S ec Hmod Henv Hcont_e Hcon_e) as [vc [Hevalc Hcont_v]].
    exists (cast_expr vc γ). split; [unfold eval_con; apply Eval_Cast; exact Hevalc | apply cast_expr_contains; exact Hcont_v].
  - (* Eval_AppAbs *)
    assert (Hfree : sym_free_env S Γ)
      by (destruct (contains_env_sym_free σ S Γ Γc Henv) as [Hf _]; exact Hf).
    destruct (contains_app_inv σ S Γ (EClos Γ' x eb) ea e_con Hfree Hcont) as
      [[fc [ac [Heq [Hcont_f Hcont_a]]]] | [Hsolv _]];
      [subst e_con | exfalso; inversion Hsolv].
    apply contains_clos_inv in Hcont_f as [Γ'c [ebc [Heq_f [Hsx [Henv_clos Hcont_b]]]]]; subst.
    inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | ]; subst.
    inversion Hf as [| | | | | | Γ0 x0 body Henv_clos_c Hcon_b | | | | | | | ]; subst.
    assert (Henv_ext : contains_env σ S (ExtendEnv x (MkClosure Γ ea) Γ') (ExtendEnv x (MkClosure Γc ac) Γ'c)).
    { apply Cont_Env_Extend; assumption. }
    destruct (concore_soundness_fix Inf Φ (extend_env Γ' x Γ ea) eb eb' Heval_b eq_refl
                (ExtendEnv x (MkClosure Γc ac) Γ'c) σ S ebc Hmod Henv_ext Hcont_b Hcon_b)
      as [v_con [Heval_b' Hcont_v]].
    exists v_con. split; [| exact Hcont_v].
    unfold eval_con. apply Eval_AppAbs. exact Heval_b'.
  - (* Eval_AppSpine *)
    eapply eval_app_spine_sound; try eassumption.
    + intros Γc0 σ0 e_con0 Hmod0 Henv0 Hcont0 Hcon0.
      exact (concore_soundness_fix Inf Φ Γ ef ef' Heval_f eq_refl Γc0 σ0 S e_con0 Hmod0 Henv0 Hcont0 Hcon0).
    + intros Γc0 σ0 e_con0 Hmod0 Henv0 Hcont0 Hcon0.
      exact (concore_soundness_fix Inf Φ Γ (EApp ef' ea) er Heval_app2 eq_refl Γc0 σ0 S e_con0 Hmod0 Henv0 Hcont0 Hcon0).
  - (* Eval_Bot *)
    inversion Hcont; subst; [| kill_denote].
    exists (EBot b). split; [apply Eval_Bot | apply Cont_Bot].
  - (* Eval_AppPrim *)
    assert (Hfree : sym_free_env S Γ)
      by (destruct (contains_env_sym_free σ S Γ Γc Henv) as [Hf _]; exact Hf).
    assert (Hfree_c : sym_free_env S Γc)
      by (destruct (contains_env_sym_free σ S Γ Γc Henv) as [_ Hf]; exact Hf).
    destruct (contains_app_inv σ S Γ ef ea e_con Hfree Hcont) as
      [[fc [ac [Heq [Hcont_f Hcont_a]]]] |
       [Hsolv_f [p0 [args0 [lv [Hun0 [Har0 [Hg0 [Hden0 Heq]]]]]]]]];
      subst e_con;
      [| (* the concrete side is the literal the symbolic spine denotes *)
         rewrite Hunspool in Hun0; injection Hun0 as Hp0 Hargs0; subst p0 args0;
         exists (ELit lv); split; [unfold eval_con; apply Eval_Lit |];
         assert (Hden' : denote σ S (reduce_prim p args') lv)
           by (eapply eval_denote;
               [ exact Hmod | exact Hfree
               | eapply Eval_AppPrim; [exact Hunspool | exact Harity | exact Hargs]
               | exact Hden0 ]);
         assert (Hsolv_r : Solvable Γc (reduce_prim p args'))
           by (destruct Hden' as [pcr [Hdr _]];
               exact (expr_to_pc_solvable Γc _ pcr (Hdr Γc Hfree_c)));
         remember (reduce_prim p args') as rt eqn:Hrt;
         destruct Hsolv_r as [l0 | y Hy | q | f a Hop Hf Ha];
         [ rewrite <- (denote_lit_inv σ S l0 lv Hden'); apply Cont_Lit
         | destruct (denote_var_inv σ S y lv Hden') as [Hsy Hlv];
           rewrite Hlv; apply Cont_Var_Sym; exact Hsy
         | exfalso;
           destruct (reduce_prim_ground_value p args'
                       (ltac:(rewrite <- Hrt; reflexivity))) as [l1 Hl1];
           rewrite <- Hrt in Hl1; discriminate Hl1
         | destruct (smt_ground (EApp f a)) eqn:Hg;
           [ exfalso;
             destruct (reduce_prim_ground_value p args'
                         (ltac:(rewrite <- Hrt; exact Hg))) as [l1 Hl1];
             rewrite <- Hrt in Hl1; discriminate Hl1
           | destruct (is_op_app_unspool (EApp f a) Hop) as [q [qargs Hunq]];
             apply (Cont_Denote σ S (EApp f a) q qargs lv Hunq);
             [ eapply reduce_prim_saturated; rewrite Hrt in Hunq; exact Hunq
             | exact Hg | exact Hden' ] ] ] ].
    assert (Hcont_full : contains σ S (EApp ef ea) (EApp fc ac)) by (constructor; assumption).
    inversion Hcon as [| | | | fc0 ac0 Hcon_f Hcon_a | | | | | | | | | ]; subst.
    assert (HL : Forall2 (contains σ S) [ea] [ac])
      by (constructor; [exact Hcont_a | constructor]).
    assert (Hne : [ea] <> (@nil expr)) by discriminate.
    assert (Hunspool_c : exists args_c, unspool_app (EApp fc ac) [] = (EPrimOp p, args_c) /\ Forall2 (contains σ S) args args_c).
    { apply (contains_unspool_primop σ S ef fc Hcont_f [ea] [ac] HL Hne p args
               Hunspool Harity). }
    destruct Hunspool_c as [args_c [Hunspool_c Hcont_args]].
    assert (Hconcore_args_c : Forall concore_expr args_c).
    { eapply unspool_app_concore; [exact Hunspool_c | constructor; assumption | constructor]. }
    assert (Hstep : exists args_c', Forall2 (eval Inf pc_true Γc) args_c args_c' /\ Forall2 (contains σ S) args' args_c').
    { clear Hunspool Harity Hunspool_c Hcont_full.
      revert args_c Hcont_args Hconcore_args_c.
      induction Hargs as [| a a' args_tl args'_tl Ha Hargs_tl IHargs];
        intros args_c Hcont_args Hconcore_args_c.
      - inversion Hcont_args; subst.
        exists []. split; constructor.
      - inversion Hcont_args as [| a0 ac1 args_tl0 args_c_tl Hcont_a1 Hcont_tl Heqa Heqargs]; subst.
        inversion Hconcore_args_c as [| ac2 args_c_tl2 Hcon_a1 Hcon_tl]; subst.
        destruct (concore_soundness_fix Inf Φ Γ a a' Ha eq_refl Γc σ S ac1 Hmod Henv Hcont_a1 Hcon_a1)
          as [v_a [Heval_a Hcont_va]].
        destruct (IHargs args_c_tl Hcont_tl Hcon_tl) as [args_c'_tl [Heval_tl Hcont_tl']].
        exists (v_a :: args_c'_tl). split; constructor; assumption.
    }
    destruct Hstep as [args_c' [Heval_args_c Hcont_args']].
    exists (reduce_prim p args_c').
    split.
    + unfold eval_con. eapply Eval_AppPrim.
      * exact Hunspool_c.
      * assert (Hlen : length args_c = length args) by (symmetry; eapply Forall2_length; exact Hcont_args).
        rewrite Hlen. exact Harity.
      * exact Heval_args_c.
    + apply reduce_prim_contains. exact Hcont_args'.
  - (* Eval_Lam *)
    apply contains_lam_inv in Hcont as [bodyc [Heq [Hsx Hcont_body]]]; subst.
    exists (EClos Γc x bodyc). split; [apply Eval_Lam | constructor; assumption].
  - (* Eval_AppCast *)
    eapply eval_app_cast_sound; try eassumption.
    intros Γc0 σ0 e_con0 Hmod0 Henv0 Hcont0 Hcon0.
    exact (concore_soundness_fix Inf Φ Γ (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r) er Heval_pushed eq_refl Γc0 σ0 S e_con0 Hmod0 Henv0 Hcont0 Hcon0).
  - (* Eval_AppBot *)
    assert (Hfree : sym_free_env S Γ)
      by (destruct (contains_env_sym_free σ S Γ Γc Henv) as [Hf _]; exact Hf).
    destruct (contains_app_inv σ S Γ (EBot b) ea e_con Hfree Hcont) as
      [[fc [ac [Heq [Hcont_f Hcont_a]]]] | [Hsolv _]];
      [subst e_con | exfalso; inversion Hsolv].
    inversion Hcont_f; subst; [| kill_denote].
    exists (EBot b). split; [apply Eval_AppBot | constructor].
  - (* Eval_Case *)
    apply contains_case_inv in Hcont as [esc [altsc [Heq [Hcont_es Hcont_alts]]]]; subst.
    inversion Hcon as [| | | | | | | es0 alts0 Hcon_es Hcon_alts | | | | | | ]; subst.
    destruct (concore_soundness_fix Inf Φ Γ es es' Heval_es eq_refl Γc σ S esc Hmod Henv Hcont_es Hcon_es) as [vc_s [Heval_esc Hcont_vs]].
    assert (Hcont_merge : contains σ S (merge es') vc_s) by (apply merge_contains; exact Hcont_vs).
    destruct (concore_soundness_fold_fix Inf Φ Γ (merge es') alts er Hfold eq_refl Γc σ S esc altsc Hmod Henv Hcon_es Hcon_alts
                (ex_intro _ vc_s (conj Heval_esc Hcont_merge)) Hcont_alts) as [v_con [Heval_case Hcont_er]].
    exists v_con. split; assumption.
  - (* Eval_If *)
    assert (Hfree : sym_free_env S Γ)
      by (destruct (contains_env_sym_free σ S Γ Γc Henv) as [Hf _]; exact Hf).
    inversion Hcont; subst.
    + assert (Hcond' : models_cond σ S ec')
        by (apply eval_models_cond with (Φ:=Φ)(Γ:=Γ)(ec:=ec); assumption).
      assert (Hpc_mod : σ ⊨ pc_c) by (apply (models_cond_pc σ S Γ ec' pc_c Hpc); exact Hcond').
      assert (Hmod_and : σ ⊨ (Φ ∧ pc_c)) by (apply models_and; assumption).
      destruct (concore_soundness_fix Inf (Φ ∧ pc_c) Γ et et' Heval_t eq_refl Γc σ S e_con Hmod_and Henv H4 Hcon) as [v_con [Hevalc' Hcont_v]].
      exists v_con. split; [exact Hevalc' |]. apply Cont_If_True; [exact Hcond' | exact Hcont_v].
    + assert (Hncond' : models_not_cond σ S ec')
        by (apply eval_models_not_cond with (Φ:=Φ)(Γ:=Γ)(ec:=ec); assumption).
      assert (Hpc_mod : σ ⊨ (¬ pc_c)) by (apply (models_not_cond_pc σ S Γ ec' pc_c Hpc); exact Hncond').
      assert (Hmod_and : σ ⊨ (Φ ∧ ¬ pc_c)) by (apply models_and; assumption).
      destruct (concore_soundness_fix Inf (Φ ∧ ¬ pc_c) Γ ef ef' Heval_f eq_refl Γc σ S e_con Hmod_and Henv H4 Hcon) as [v_con [Hevalc' Hcont_v]].
      exists v_con. split; [exact Hevalc' |]. apply Cont_If_False; [exact Hncond' | exact Hcont_v].
    + kill_denote.
  - (* Eval_Coercion *)
    inversion Hcont; subst; [| kill_denote].
    exists (ECoercion (subst_coerc Γc γ)).
    split; [apply Eval_Coercion | apply subst_coerc_contains_env; assumption].
  - (* Eval_Prune *)
    apply models_sat in Hmod. rewrite Hunsat in Hmod. discriminate.
  - (* Eval_Type *)
    inversion Hcont; subst; [| kill_denote].
    exists (EType (subst_type Γc τ)).
    split; [apply Eval_Type | apply subst_type_contains_env; assumption].
}
{
  destruct Hfold as
    [ kv Φ Γ ec et ef alts et' ef' pc_c Hpc Hfold_t Hfold_f
    | kv Φ Γ ec et ef alts Hpc_none
    | kv Φ Γ e d ea xs ep alts er Hdec Halt Heval_ep
    | kv Φ Γ b alts
    | kv Φ Γ e alts Hnotif Hnoalt Hnotbot
    ]; intros Hk0; subst kv; intros Γc σ S esc altsc Hmod Henv Hcon_esc Hcon_altsc Hvc Halts.
  - (* FoldAlts_If *)
    destruct Hvc as [vc_s [Heval_esc Hcont_vs]].
    inversion Hcont_vs; subst.
    + assert (Hpc_mod : σ ⊨ pc_c) by (apply (models_cond_pc σ S Γ ec pc_c Hpc); assumption).
      assert (Hmod_and : σ ⊨ (Φ ∧ pc_c)) by (apply models_and; assumption).
      destruct (concore_soundness_fold_fix Inf (Φ ∧ pc_c) Γ et alts et' Hfold_t eq_refl Γc σ S esc altsc Hmod_and Henv Hcon_esc Hcon_altsc
                  (ex_intro _ vc_s (conj Heval_esc H4)) Halts) as [v_con [Heval_case Hcont_er]].
      exists v_con. split; [exact Heval_case | apply Cont_If_True; assumption].
    + assert (Hpc_mod : σ ⊨ (¬ pc_c)) by (apply (models_not_cond_pc σ S Γ ec pc_c Hpc); assumption).
      assert (Hmod_and : σ ⊨ (Φ ∧ ¬ pc_c)) by (apply models_and; assumption).
      destruct (concore_soundness_fold_fix Inf (Φ ∧ ¬ pc_c) Γ ef alts ef' Hfold_f eq_refl Γc σ S esc altsc Hmod_and Henv Hcon_esc Hcon_altsc
                  (ex_intro _ vc_s (conj Heval_esc H4)) Halts) as [v_con [Heval_case Hcont_er]].
      exists v_con. split; [exact Heval_case | apply Cont_If_False; assumption].
    + kill_denote.
  - (* FoldAlts_IfFail *)
    destruct Hvc as [vc_s [Heval_esc Hcont_vs]].
    assert (Hfree : sym_free_env S Γ)
      by (destruct (contains_env_sym_free σ S Γ Γc Henv) as [Hf _]; exact Hf).
    inversion Hcont_vs; subst.
    + exfalso.
      destruct (models_cond_total σ S Γ ec Hfree (or_introl H3)) as [pc Hpc_some].
      rewrite Hpc_none in Hpc_some. discriminate.
    + exfalso.
      destruct (models_cond_total σ S Γ ec Hfree (or_intror H3)) as [pc Hpc_some].
      rewrite Hpc_none in Hpc_some. discriminate.
    + kill_denote.
  - (* FoldAlts_Con *)
    destruct Hvc as [vc_s [Heval_esc Hcont_vs]].
    assert (Hunspool_e : unspool_app e [] = (ECon d, ea)).
    { unfold decompose_con_app in Hdec.
      destruct (unspool_app e []) as [h a0] eqn:Hu.
      destruct h; try discriminate.
      inversion Hdec; subst; reflexivity. }
    assert (Hunspool_vcs : exists ea_c, unspool_app vc_s [] = (ECon d, ea_c) /\ Forall2 (contains σ S) ea ea_c).
    { apply (contains_unspool_con σ S e vc_s Hcont_vs [] [] (Forall2_nil _) d ea Hunspool_e). }
    destruct Hunspool_vcs as [ea_c [Hunspool_vcs Hcont_ea]].
    assert (Hdec_vcs : decompose_con_app vc_s = Some (d, ea_c)).
    { unfold decompose_con_app. rewrite Hunspool_vcs. reflexivity. }
    destruct (find_alt_contains_alt σ S alts altsc d xs ep Halts Halt) as [ep_c [Halt_c [Hxs Hcont_ep]]].
    assert (Henv_concrete : concrete_env Γc) by (eapply contains_env_concrete; exact Henv).
    assert (Hcon_vcs : concore_expr vc_s) by (eapply concore_eval_closed; [exact Henv_concrete | exact Hcon_esc | exact Heval_esc]).
    assert (Hconcore_ea_c : Forall concore_expr ea_c).
    { eapply unspool_app_concore; [exact Hunspool_vcs | exact Hcon_vcs | constructor]. }
    assert (Hcon_ep_c : concore_expr ep_c) by (eapply find_alt_concore; [exact Halt_c | exact Hcon_altsc]).
    assert (Henv_ext : contains_env σ S (extend_env_multi Γ xs ea Γ) (extend_env_multi Γc xs ea_c Γc)).
    { apply contains_env_extend_multi; assumption. }
    destruct (concore_soundness_fix Inf Φ (extend_env_multi Γ xs ea Γ) ep er Heval_ep eq_refl
                (extend_env_multi Γc xs ea_c Γc) σ S ep_c Hmod Henv_ext Hcont_ep Hcon_ep_c)
      as [v_con [Heval_ep_c Hcont_er]].
    exists v_con. split; [| exact Hcont_er].
    unfold eval_con. eapply Eval_Case.
    + exact Heval_esc.
    + apply merge_fold_alts_equiv.
      eapply FoldAlts_Con; [exact Hdec_vcs | exact Halt_c | exact Heval_ep_c].
  - (* FoldAlts_Bot *)
    destruct Hvc as [vc_s [Heval_esc Hcont_vs]].
    inversion Hcont_vs; subst; [| kill_denote].
    exists (EBot b). split; [| apply Cont_Bot].
    unfold eval_con. eapply Eval_Case.
    + exact Heval_esc.
    + apply merge_fold_alts_equiv. apply FoldAlts_Bot.
  - (* FoldAlts_Otherwise *)
    destruct Hvc as [vc_s [Heval_esc Hcont_vs]].
    assert (Hrec : fold_alts Inf Φ Γ e alts (EBot BUndefined)) by (eapply FoldAlts_Otherwise; eassumption).
    assert (Hno_nested := fold_alts_no_nested_if Φ Γ e alts (EBot BUndefined) Hrec).
    destruct (unspool_app e []) as [head args] eqn:Hunspool_e.
    assert (Hif_head : is_if head = false).
    { destruct (is_if head) eqn:Hcase; [| reflexivity].
      specialize (Hno_nested head args eq_refl Hcase). subst head.
      rewrite Hnotif in Hcase. discriminate. }
    assert (Hfacts :
      (match decompose_con_app vc_s with
       | Some (d, _) => find_alt d altsc = None
       | None => True
       end)
      /\ is_bot vc_s = false /\ is_if vc_s = false).
    { destruct (contains_unspool_general σ S e vc_s Hcont_vs [] [] (Forall2_nil _) head args Hunspool_e Hif_head)
        as [[head_c [args_c [Hunspool_vcs [Hcont_head Hcont_args]]]]
           | [lv [args_c Hunspool_vcs]]].
      - split; [| split].
        + unfold decompose_con_app. rewrite Hunspool_vcs.
          destruct head_c eqn:Hheadc; try exact I.
          inversion Hcont_head; subst; try (simpl in Hif_head; discriminate).
          assert (Hdeco_e : decompose_con_app e = Some (d, args)) by (unfold decompose_con_app; rewrite Hunspool_e; reflexivity).
          rewrite Hdeco_e in Hnoalt.
          exact (find_alt_none_contains_alt σ S alts altsc d Halts Hnoalt).
        + destruct (is_bot vc_s) eqn:Hbc; [| reflexivity].
          exfalso. destruct vc_s; simpl in Hbc; try discriminate.
          inversion Hcont_vs; subst; discriminate.
        + destruct (is_if vc_s) eqn:Hic; [| reflexivity].
          exfalso. destruct vc_s; simpl in Hic; try discriminate.
          inversion Hcont_vs; subst; discriminate.
      - (* the scrutinee concretised to an SMT value, which matches no
           constructor alternative, exactly as the symbolic side did *)
        split; [| split].
        + unfold decompose_con_app. rewrite Hunspool_vcs. exact I.
        + destruct (is_bot vc_s) eqn:Hbc; [| reflexivity].
          exfalso. destruct vc_s; simpl in Hbc; discriminate.
        + destruct (is_if vc_s) eqn:Hic; [| reflexivity].
          exfalso. destruct vc_s; simpl in Hic; discriminate.
    }
    destruct Hfacts as [Hnoalt_c [Hnotbot_c Hnotif_c]].
    exists (EBot BUndefined). split; [| apply Cont_Bot].
    unfold eval_con. eapply Eval_Case.
    + exact Heval_esc.
    + apply merge_fold_alts_equiv.
      apply FoldAlts_Otherwise; assumption.
}
Qed.

(**
  The conclusion is existential: SOME concrete value matches the symbolic
  one. The statement is left that way here.

  The stronger reading,
    forall v_con, Γc ⊢ᶜ e_con ⇓ᶜ v_con -> contains σ S v_sym v_con,
  now follows for the terms the theorem is about, because Section 12.4
  proves concrete evaluation deterministic on them: e_con is a ConCore
  expression by hypothesis, and Γc is a ConCore environment by
  contains_env_concrete, so e_con has at most one value and the existential
  one is it. Deriving it costs nothing but is not done here, to keep the
  theorem as it was stated.
*)
Theorem concore_soundness : forall Φ Γs Γc σ S e_sym e_con v_sym,
  σ ⊨ Φ ->
  contains_env σ S Γs Γc ->
  contains σ S e_sym e_con ->
  concore_expr e_con ->
  Φ ; Γs ⊢ e_sym ⇓ v_sym ->
  exists v_con,
    Γc ⊢ᶜ e_con ⇓ᶜ v_con /\
    contains σ S v_sym v_con.
Proof.
  intros Φ Γs Γc σ S e_sym e_con v_sym Hmod Henv Hcont Hcon Heval.
  exact (concore_soundness_fix Inf Φ Γs e_sym v_sym Heval eq_refl Γc σ S e_con Hmod Henv Hcont Hcon).
Qed.


(** Top-level Soundness for whole programs starting from · *)
Corollary concore_soundness_top : forall Φ σ S e_sym e_con v_sym,
  σ ⊨ Φ ->
  contains σ S e_sym e_con ->
  concore_expr e_con ->
  Φ ; · ⊢ e_sym ⇓ v_sym ->
  exists v_con,
    ⊢ᶜ e_con ⇓ᶜ v_con /\
    contains σ S v_sym v_con.
Proof.
  intros Φ σ S e_sym e_con v_sym Hmod Hcont Hcon Heval.
  apply (concore_soundness Φ · · σ S e_sym e_con v_sym); auto.
  apply Cont_Env_Empty.
Qed.


(**
  The other half of this section, completeness, is in Section 13. It is
  stated there and not here because its proof needs Section 12: a concrete
  program has at most one value, and that is what identifies the value
  soundness produces with the value completeness is handed.
*)

(** ========================================================================= *)
(** 11. NonVacuity: what the repaired statement actually says                 *)
(** ========================================================================= *)

(**
  Six facts that the pre-repair development could not prove, and in three
  cases actively refuted (see scratch/Audit.v, scratch/prim.v,
  scratch/prim2.v):

  (a) a free symbolic variable is genuinely instantiated to its value under
      the model, and the soundness theorem has real instances that use it;
  (b) a branch whose condition mentions a free symbolic variable DOES have a
      concretion - the exact negation of soundness_vacuous_on_symbolic_branch;
  (c) Rule Prune no longer kills every branch;
  (d) reduce_prim is not forced to be a constant function on literals, and
      the collapse is attributable exactly to the axiom that was weakened;
  (e) the relation is still DISCRIMINATING: different literals, different
      constructors and different shapes stay unrelated, a symbolic SMT term
      has exactly one literal concretion, and a closed SMT term is related to
      nothing but itself - so the repair did not buy non-vacuity with
      triviality;
  (f) a primitive that really computes a function which is neither constant
      nor the identity now lives inside the axiom set, and the soundness
      theorem applies to a program that uses it.

  No new axiom is introduced by any of this: (e) and (f) use only the three
  declared in Sections 9.0 and 9.1 (prim_value, reduce_prim_denote and
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

(** The exact negation of scratch/Audit.v's soundness_vacuous_on_symbolic_branch,
    modulo the one premise that cannot be dispensed with: that the SMT theory
    is non-degenerate, i.e. some model satisfies some atom. The audit theorem
    needed no such premise because it refuted the condition for EVERY model. *)
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

Lemma ground_solvable_contains_eq : forall σ S es ec,
  contains σ S es ec ->
  (forall Γ, Solvable Γ es) ->
  es = ec.
Proof.
  induction 1; intros Hall;
    try reflexivity;
    try (exfalso;
         specialize (Hall ·); inversion Hall; fail).
  - (* Cont_Var_Sym *)
    exfalso.
    specialize (Hall (ExtendEnv x (MkClosure · (EBot BUndefined)) ·)).
    inversion Hall as [| x0 Hnone | |]; subst.
    simpl in Hnone. destruct (string_dec x x); [discriminate | congruence].
  - (* Cont_App *)
    assert (Hf : forall Γ, Solvable Γ f_s)
      by (intros Γ; specialize (Hall Γ); inversion Hall; assumption).
    assert (Ha : forall Γ, Solvable Γ a_s)
      by (intros Γ; specialize (Hall Γ); inversion Hall; assumption).
    rewrite (IHcontains1 Hf), (IHcontains2 Ha). reflexivity.
  - (* Cont_Denote: excluded, the semantic rule never fires on a closed term *)
    exfalso.
    match goal with
    | [ Hg : smt_ground ?t = false |- _ ] =>
        rewrite (solvable_everywhere_smt_ground t Hall) in Hg; discriminate Hg
    end.
Qed.

(** The collapse is attributable exactly to the UNCONDITIONAL form of
    reduce_prim_solvable, which this development no longer assumes. *)
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
    - apply reduce_prim_contains. constructor; [| constructor].
      apply Cont_If_True; [exact Htrue | apply Cont_Lit].
    - intros Γ. apply Hall. }
  assert (H2 : reduce_prim p [EIf c (ELit l1) (ELit l2)] = reduce_prim p [ELit l2]).
  { eapply (ground_solvable_contains_eq σ' S').
    - apply reduce_prim_contains. constructor; [| constructor].
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
    intros σ S c Hc. apply reduce_prim_contains. constructor; [| constructor].
    apply Cont_If_True; [exact Hc | apply Cont_Lit].
  Qed.

  (** The branch premise is no longer an abstract judgement nobody can
      discharge. models_cond is a definition now, so a caller supplies it
      from a model of the condition's own formula and nothing else. *)
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
  relation that held of no pair did. The facts below are what stop that.
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

(** The semantic rule relates a symbolic SMT term to ONE literal, the one it
    denotes. This is the exact sense in which `contains` became semantic
    rather than permissive: it is still a function on the SMT fragment. *)
Corollary smt_concretion_determined : forall σ S es l1 l2,
  denote σ S es l1 -> contains σ S es (ELit l2) -> l1 = l2.
Proof.
  intros σ S es l1 l2 Hden Hcont.
  inversion Hcont; subst.
  - destruct (denote_var_inv σ S x l1 Hden) as [_ Hl1]. congruence.
  - symmetry. exact (denote_lit_inv σ S l2 l1 Hden).
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

(** On CLOSED SMT terms the relation is still plain syntactic equality: the
    semantic rule never fires where there is no symbolic variable to
    instantiate. *)
Corollary closed_smt_term_is_rigid : forall σ S es ec,
  smt_ground es = true -> contains σ S es ec -> es = ec.
Proof.
  intros σ S es ec Hg Hcont.
  exact (ground_solvable_contains_eq σ S es ec Hcont
           (fun Γ => smt_ground_solvable es Γ Hg)).
Qed.

(* ======= (f) a primitive that computes, and soundness applied to it ===== *)

(**
  The positive counterpart of reduce_prim_cannot_compute. Everything below is
  hypothetical in the Section's variables, so it adds no assumption to the
  development; what it shows is that a reducer which really computes a
  function that is NEITHER constant NOR the identity now sits inside the
  axiom set instead of contradicting it.

  The load-bearing step is computing_primitive_concretion: the instance of
  reduce_prim_contains that used to force reduce_prim to be constant or the
  identity is now DERIVED from Cont_Denote, without appealing to
  reduce_prim_contains at all.
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

  (** The concretion the old axiom demanded, now available as a theorem of
      the repaired relation. *)
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

  (** succ is neither constant nor the identity, which is exactly the
      conclusion the pre-repair development could force on it. *)
  Corollary computing_primitive_refutes_old_verdict :
    ~ ((exists l0, forall l, succ l = l0) \/ (forall l, succ l = l)).
  Proof.
    intros [[l0 Hconst] | Hid].
    - apply Hsucc_not_constant. rewrite (Hconst lc1), (Hconst lc2). reflexivity.
    - apply Hsucc_not_identity. apply Hid.
  Qed.
End ComputingPrimitive.

End NonVacuity.

(** ========================================================================= *)
(** 12. How Far Concrete Evaluation Is Deterministic                          *)
(** ========================================================================= *)

(**
  Concrete evaluation runs at the satisfiable path condition pc_true, so
  Rule Prune cannot fire at the root. Two rule overlaps used to survive that
  and give the same concrete expression two values. One of them is gone.

  Overlap 1, which REMAINS, is Rule Prune inside Rule If. Rule If evaluates
  the branches under Φ ∧ pc_c and Φ ∧ ¬pc_c, not under Φ. One of those is
  unsatisfiable whenever the branch is dead, which is the only reason Rule
  Prune exists. Section 12.1 refutes the unrestricted statement with it.

  Overlap 2 was Rule App-Cast against Rule App-Spine. A cast whose body is
  not in WHNF is itself not in WHNF, so both rules applied to the same
  application, and they gave the function different arguments. Rule
  App-Spine now refuses EVERY cast operator, so the two no longer meet.
  Section 12.3 records what that costs and what it buys.

  Rule App-Spine against Rule App-Prim is NOT a third overlap. Section 12.2
  proves the two can never apply to the same expression.

  What is left is deterministic, and Section 12.4 proves it: a ConCore
  expression in a ConCore environment has at most one value. Section 12.4
  also shows why the environment has to be ConCore too, by putting a dead
  branch in it and running Section 12.1 again.
*)

Definition ConEvalDeterministic : Prop :=
  forall Γ e v1 v2, Γ ⊢ᶜ e ⇓ᶜ v1 -> Γ ⊢ᶜ e ⇓ᶜ v2 -> v1 = v2.

(** ------------------------------------------------------------------------- *)
(** 12.1 Overlap 1: a dead branch has two values                              *)
(** ------------------------------------------------------------------------- *)

(**
  Take a guard that is already a value and whose formula is pc. If the guard
  cannot hold, the then-branch is evaluated under an unsatisfiable path
  condition. There Rule Prune gives ∅ and Rule Bot gives ?, so the whole
  conditional has two values.
*)
Lemma infeasible_branch_breaks_con_determinism : forall Γ ec pc,
  pc_true ; Γ ⊢ ec ⇓ ec ->
  expr_to_pc Γ ec = Some pc ->
  sat (pc_true ∧ pc) = false ->
  ~ ConEvalDeterministic.
Proof.
  intros Γ ec pc Hec Hpc Hunsat Hdet.
  assert (H1 : Γ ⊢ᶜ EIf ec (EBot BUndefined) (EBot BUndefined)
                 ⇓ᶜ EIf ec (EBot BUndefined) (EBot BUndefined))
    by (unfold eval_con;
        eapply Eval_If; [exact Hec | exact Hpc | apply Eval_Bot | apply Eval_Bot]).
  assert (H2 : Γ ⊢ᶜ EIf ec (EBot BUndefined) (EBot BUndefined)
                 ⇓ᶜ EIf ec (EBot BUnreachable) (EBot BUndefined))
    by (unfold eval_con;
        eapply Eval_If;
        [exact Hec | exact Hpc | apply Eval_Prune; exact Hunsat | apply Eval_Bot]).
  specialize (Hdet _ _ _ _ H1 H2). discriminate.
Qed.

(** A symbolic variable is the smallest guard that meets those conditions. *)
Corollary unsatisfiable_guard_breaks_con_determinism : forall x,
  sat (pc_true ∧ PCVar x) = false ->
  ~ ConEvalDeterministic.
Proof.
  intros x Hunsat.
  eapply infeasible_branch_breaks_con_determinism with (Γ := ·) (ec := EVar x).
  - apply Eval_SymVar. reflexivity.
  - reflexivity.
  - exact Hunsat.
Qed.

(** ------------------------------------------------------------------------- *)
(** 12.2 Rule App-Spine and Rule App-Prim never overlap                       *)
(** ------------------------------------------------------------------------- *)

(** unspool_app only appends to its accumulator. *)
Lemma unspool_app_acc : forall e acc,
  unspool_app e acc = (fst (unspool_app e []), snd (unspool_app e []) ++ acc).
Proof.
  induction e; intro acc; simpl; try reflexivity.
  rewrite (IHe1 (e2 :: acc)). rewrite (IHe1 [e2]). simpl.
  rewrite <- app_assoc. reflexivity.
Qed.

Lemma unspool_app_split : forall e acc h args,
  unspool_app e acc = (h, args) ->
  exists args0, unspool_app e [] = (h, args0) /\ args = args0 ++ acc.
Proof.
  intros e acc h args H. rewrite unspool_app_acc in H.
  exists (snd (unspool_app e [])).
  injection H as Hh Hargs. split.
  - rewrite <- Hh. apply surjective_pairing.
  - symmetry. assumption.
Qed.

(**
  An operator spine that evaluates carries at least as many arguments as the
  primitive needs. An under-applied primitive spine therefore has no value at
  all: the only rule that could give it one is Rule App-Prim, and that rule
  demands a saturated spine.

  Unlimited budget only, so the proof goes by inf_induction. Rule App-Prim is
  the only rule at Inf, but at Fin 0 Rule Out-Of-Fuel gives an under-applied
  spine a value too, and it asks nothing about arity.
*)
Lemma eval_prim_spine_saturated : forall Φ Γ e v,
  Φ ; Γ ⊢ e ⇓ v ->
  sat Φ = true ->
  forall p args, unspool_app e [] = (EPrimOp p, args) ->
  primop_arity p <= length args.
Proof.
  intros Φ Γ e v Heval. inf_induction Heval;
    intros Hsat p0 args0 Hun; simpl in Hun; try discriminate.
  - destruct (unspool_app_split ef [ea] (EPrimOp p0) args0 Hun) as [a1 [Hu1 Heq]].
    specialize (IHHeval1 eq_refl Hsat p0 a1 Hu1). subst args0.
    rewrite length_app. simpl. lia.
  - simpl in H. rewrite H in Hun. injection Hun as Hh Hl; subst. lia.
  - rewrite Hsat in H. discriminate.
Qed.

(**
  In a saturated primitive application the operator is one argument short, so
  by the previous lemma the operator has no value. Rule App-Spine needs a
  value for the operator, so it cannot fire here.
*)
Lemma prim_operator_has_no_value : forall Φ Γ ef ea p args ef',
  sat Φ = true ->
  unspool_app (EApp ef ea) [] = (EPrimOp p, args) ->
  length args = primop_arity p ->
  ~ (Φ ; Γ ⊢ ef ⇓ ef').
Proof.
  intros Φ Γ ef ea p args ef' Hsat Hun Hlen Heval.
  simpl in Hun.
  destruct (unspool_app_split ef [ea] (EPrimOp p) args Hun) as [a1 [Hu1 Heq]].
  pose proof (eval_prim_spine_saturated Φ Γ ef ef' Heval Hsat p a1 Hu1) as Hge.
  subst args. rewrite length_app in Hlen. simpl in Hlen. lia.
Qed.

(** Wherever Rule App-Prim applies, the premises of Rule App-Spine cannot all
    hold. The two rules are disjoint, so they are not a source of ambiguity. *)
Lemma app_spine_never_overlaps_app_prim : forall Φ Γ ef ea p args,
  sat Φ = true ->
  unspool_app (EApp ef ea) [] = (EPrimOp p, args) ->
  length args = primop_arity p ->
  ~ (exists ef' er,
       ~ Whnf Γ ef /\ Φ ; Γ ⊢ ef ⇓ ef' /\ Φ ; Γ ⊢ EApp ef' ea ⇓ er).
Proof.
  intros Φ Γ ef ea p args Hsat Hun Hlen [ef' [er [_ [Heval _]]]].
  exact (prim_operator_has_no_value Φ Γ ef ea p args ef' Hsat Hun Hlen Heval).
Qed.

(** ------------------------------------------------------------------------- *)
(** 12.3 Overlap 2: Rule App-Cast against Rule App-Spine                      *)
(** ------------------------------------------------------------------------- *)

Lemma not_whnf_cast_lam : forall Γ x body γ,
  ~ Whnf Γ (ECast (ELam x body) γ).
Proof.
  intros Γ x body γ H. inversion H; subst.
  - inversion H0.
  - apply (not_whnf_lam Γ x body). assumption.
Qed.

Definition arrow_coercion : coercion :=
  MkCoercion (TyArrow (TyVar "a") (TyVar "b"))
             (TyArrow (TyVar "c") (TyVar "d"))
             RoleRepresentational.

Definition arrow_dom : coercion :=
  MkCoercion (TyVar "a") (TyVar "c") RoleRepresentational.

Definition arrow_cod : coercion :=
  MkCoercion (TyVar "b") (TyVar "d") RoleRepresentational.

Lemma decomp_arrow_coercion :
  decomp_coerc_arrow arrow_coercion = Some (arrow_dom, arrow_cod).
Proof. reflexivity. Qed.

(** The body stores its argument in a closure, so the value records which
    argument the caller passed. *)
Definition capture_body : expr := ELam "z" (EVar "x").
Definition coerced_operator : expr := ECast (ELam "x" capture_body) arrow_coercion.
Definition plain_operand : expr := ECon "D".
Definition coerced_operand : expr := ECast plain_operand (sym_coerc arrow_dom).

Section CastedApplication.

(**
  The one thing assumed here: a cast on a closure is erased. That is what a
  representational coercion means at run time, and total erasure,
  cast_expr e γ = e, satisfies it. The corollary after this section draws
  that consequence.
*)
Variable closure_cast_erased :
  forall Γ0 x body γ, cast_expr (EClos Γ0 x body) γ = EClos Γ0 x body.

(**
  Rule App-Spine used to strip the cast first, which handed the function the
  plain argument and gave the term a second value. It cannot do that any
  more: its new premise refuses every cast operator, and this operator is a
  cast.
*)
Lemma app_spine_refuses_the_coerced_operator :
  is_cast coerced_operator = true.
Proof. reflexivity. Qed.

Lemma no_app_spine_derivation_here : forall ef' er,
  ~ (~ Whnf · coerced_operator /\
     is_cast coerced_operator = false /\
     pc_true ; · ⊢ coerced_operator ⇓ ef' /\
     pc_true ; · ⊢ EApp ef' plain_operand ⇓ er).
Proof.
  intros ef' er [_ [Hguard _]].
  rewrite app_spine_refuses_the_coerced_operator in Hguard. discriminate.
Qed.

(** Rule App-Cast pushes the coercion into the argument first, so the same
    function gets a cast argument. *)
Lemma casted_application_by_app_cast :
  · ⊢ᶜ EApp coerced_operator plain_operand
     ⇓ᶜ EClos (extend_env · "x" · coerced_operand) "z" (EVar "x").
Proof.
  unfold eval_con.
  eapply Eval_AppCast with (γ_a := arrow_dom) (γ_r := arrow_cod).
  - apply decomp_arrow_coercion.
  - rewrite <- (closure_cast_erased (extend_env · "x" · coerced_operand)
                                    "z" (EVar "x") arrow_cod).
    apply Eval_Cast.
    eapply Eval_AppSpine with (ef' := EClos · "x" capture_body).
    + apply not_whnf_lam.
    + reflexivity.
    + apply Eval_Lam.
    + apply Eval_AppAbs. apply Eval_Lam.
Qed.

(**
  REMOVED, and this is the point of the repair:

    cast_overlap_breaks_con_determinism : ~ ConEvalDeterministic
    erased_coercions_break_con_determinism

  Both were proved by pitting the App-Spine value against the App-Cast value
  of this one term. The App-Spine value is gone, so neither statement can be
  proved that way any more, and Section 12.4 proves the opposite: this term
  has exactly one value. Section 12.1 still refutes ConEvalDeterministic, by
  a dead branch, so the unrestricted statement is still false; what changed
  is that casts are no longer a second reason for it.
*)

End CastedApplication.

(** ------------------------------------------------------------------------- *)
(** 12.4 ConCore programs have at most one value                              *)
(** ------------------------------------------------------------------------- *)

(**
  What survives of determinism once Rule App-Spine refuses a cast operator.

  The statement below is the one that matters for soundness: a ConCore
  expression, run in an environment that binds only ConCore expressions, has
  at most one value. Both hypotheses are needed.

  concore_expr excludes EIf, which is what keeps Rule Prune out of the way:
  Rule Prune fires only under an unsatisfiable path condition, the run
  starts at pc_true, and the only rule that changes the path condition is
  Rule If.

  concrete_env excludes it from the environment too. Without that, Rule Var
  walks into whatever the environment holds, a branch included, and Section
  12.1 comes back through the back door. The refutation at the end of this
  section is that door, spelled out.

  Everything else is rule disjointness, and the proof is one case per rule
  of the second derivation. The interesting rows:

    App-Spine against App-Cast   : the new guard settles it.
    App-Spine against App-Prim   : Section 12.2 settles it.
    App-Spine against App-Abs    : a closure is a value.
    App-Spine against App-Bot    : a bottom is a value.

  There is no longer a row for Rule App-Cast-Opaque, because there is no
  longer such a rule. Where it used to fire, nothing fires:
  eval_app_cast_opaque_stuck below says so.
*)

Ltac prune_absurd :=
  match goal with
  | [ Hs : sat ?F = true, Hu : sat ?F = false |- _ ] => rewrite Hs in Hu; discriminate
  end.

(** One inversion lemma per shape of the term being evaluated. Each one says
    which rule the second derivation must have used, and carries its
    premises out. *)

Lemma eval_var_bound_inv : forall Φ Γ x Γ' e0 v,
  sat Φ = true ->
  lookup_env Γ x = Some (Γ', e0) ->
  Φ ; Γ ⊢ EVar x ⇓ v ->
  Φ ; Γ' ⊢ e0 ⇓ v.
Proof.
  intros Φ Γ x Γ' e0 v Hsat Hlook Heval.
  inversion Heval; subst; try prune_absurd.
  - match goal with
    | [ H : lookup_env Γ x = Some (?G, ?E) |- _ ] =>
        assert (Heq : Some (G, E) = Some (Γ', e0)) by (rewrite <- H; exact Hlook)
    end.
    injection Heq as Hg He. subst. assumption.
  - congruence.
Qed.

Lemma eval_var_free_inv : forall Φ Γ x v,
  sat Φ = true ->
  lookup_env Γ x = None ->
  Φ ; Γ ⊢ EVar x ⇓ v ->
  v = EVar x.
Proof.
  intros Φ Γ x v Hsat Hlook Heval.
  inversion Heval; subst; try prune_absurd; [congruence | reflexivity].
Qed.

Lemma eval_lit_inv : forall Φ Γ l v,
  sat Φ = true -> Φ ; Γ ⊢ ELit l ⇓ v -> v = ELit l.
Proof.
  intros Φ Γ l v Hsat Heval.
  inversion Heval; subst; try prune_absurd; reflexivity.
Qed.

Lemma eval_con_inv : forall Φ Γ d v,
  sat Φ = true -> Φ ; Γ ⊢ ECon d ⇓ v -> v = ECon d.
Proof.
  intros Φ Γ d v Hsat Heval.
  inversion Heval; subst; try prune_absurd; reflexivity.
Qed.

Lemma eval_bot_inv : forall Φ Γ b v,
  sat Φ = true -> Φ ; Γ ⊢ EBot b ⇓ v -> v = EBot b.
Proof.
  intros Φ Γ b v Hsat Heval.
  inversion Heval; subst; try prune_absurd; reflexivity.
Qed.

Lemma eval_lam_inv : forall Φ Γ x e0 v,
  sat Φ = true -> Φ ; Γ ⊢ ELam x e0 ⇓ v -> v = EClos Γ x e0.
Proof.
  intros Φ Γ x e0 v Hsat Heval.
  inversion Heval; subst; try prune_absurd; reflexivity.
Qed.

Lemma eval_coercion_inv : forall Φ Γ γ v,
  sat Φ = true -> Φ ; Γ ⊢ ECoercion γ ⇓ v -> v = ECoercion (subst_coerc Γ γ).
Proof.
  intros Φ Γ γ v Hsat Heval.
  inversion Heval; subst; try prune_absurd; reflexivity.
Qed.

Lemma eval_type_inv : forall Φ Γ τ v,
  sat Φ = true -> Φ ; Γ ⊢ EType τ ⇓ v -> v = EType (subst_type Γ τ).
Proof.
  intros Φ Γ τ v Hsat Heval.
  inversion Heval; subst; try prune_absurd; reflexivity.
Qed.

Lemma eval_cast_inv : forall Φ Γ e0 γ v,
  sat Φ = true ->
  Φ ; Γ ⊢ ECast e0 γ ⇓ v ->
  exists e', Φ ; Γ ⊢ e0 ⇓ e' /\ v = cast_expr e' γ.
Proof.
  intros Φ Γ e0 γ v Hsat Heval.
  inversion Heval; subst; try prune_absurd.
  eexists. split; [eassumption | reflexivity].
Qed.

Lemma eval_case_inv : forall Φ Γ es alts v,
  sat Φ = true ->
  Φ ; Γ ⊢ ECase es alts ⇓ v ->
  exists es', Φ ; Γ ⊢ es ⇓ es' /\ fold_alts Inf Φ Γ (merge es') alts v.
Proof.
  intros Φ Γ es alts v Hsat Heval.
  inversion Heval; subst; try prune_absurd.
  eexists. split; eassumption.
Qed.

Lemma eval_app_clos_inv : forall Φ Γ Γ' x eb ea v,
  sat Φ = true ->
  Φ ; Γ ⊢ EApp (EClos Γ' x eb) ea ⇓ v ->
  Φ ; extend_env Γ' x Γ ea ⊢ eb ⇓ v.
Proof.
  intros Φ Γ Γ' x eb ea v Hsat Heval.
  inversion Heval; subst; try prune_absurd.
  - assumption.
  - exfalso. match goal with
    | [ H : ~ Whnf Γ (EClos Γ' x eb) |- _ ] => apply H; apply Whnf_Clos
    end.
  - match goal with
    | [ H : unspool_app (EApp (EClos Γ' x eb) ea) [] = _ |- _ ] =>
        simpl in H; injection H as Hh _; discriminate
    end.
Qed.

Lemma eval_app_bot_inv : forall Φ Γ b ea v,
  sat Φ = true ->
  Φ ; Γ ⊢ EApp (EBot b) ea ⇓ v ->
  v = EBot b.
Proof.
  intros Φ Γ b ea v Hsat Heval.
  inversion Heval; subst; try prune_absurd.
  - exfalso. match goal with
    | [ H : ~ Whnf Γ (EBot b) |- _ ] => apply H; apply Whnf_Bot
    end.
  - match goal with
    | [ H : unspool_app (EApp (EBot b) ea) [] = _ |- _ ] =>
        simpl in H; injection H as Hh _; discriminate
    end.
  - reflexivity.
Qed.

Lemma eval_app_cast_arrow_inv : forall Φ Γ eb γ γ_a γ_r ea v,
  sat Φ = true ->
  decomp_coerc_arrow γ = Some (γ_a, γ_r) ->
  Φ ; Γ ⊢ EApp (ECast eb γ) ea ⇓ v ->
  Φ ; Γ ⊢ ECast (EApp eb (ECast ea (sym_coerc γ_a))) γ_r ⇓ v.
Proof.
  intros Φ Γ eb γ γ_a γ_r ea v Hsat Hdec Heval.
  inversion Heval; subst; try prune_absurd.
  - exfalso. match goal with
    | [ H : is_cast (ECast eb γ) = false |- _ ] => discriminate H
    end.
  - match goal with
    | [ H : unspool_app (EApp (ECast eb γ) ea) [] = _ |- _ ] =>
        simpl in H; injection H as Hh _; discriminate
    end.
  - match goal with
    | [ H : decomp_coerc_arrow γ = Some (?A, ?R) |- _ ] =>
        assert (Heq : Some (A, R) = Some (γ_a, γ_r)) by (rewrite <- H; exact Hdec)
    end.
    injection Heq as Ha Hr. subst. assumption.
Qed.

(**
  Applying a cast whose coercion is not an arrow: NO rule reaches this
  shape, so the term has no value at all. Rule App-Cast needs the coercion
  to split, Rule App-Spine refuses every cast operator, and the other three
  application rules each want a different operator. The shape is stuck, and
  it is stuck whether or not the body under the cast is a value - see
  Section 12.5.
*)
Lemma eval_app_cast_opaque_stuck : forall Φ Γ eb γ ea v,
  sat Φ = true ->
  decomp_coerc_arrow γ = None ->
  Φ ; Γ ⊢ EApp (ECast eb γ) ea ⇓ v ->
  False.
Proof.
  intros Φ Γ eb γ ea v Hsat Hdec Heval.
  inversion Heval; subst; try prune_absurd.
  - match goal with
    | [ H : is_cast (ECast eb γ) = false |- _ ] => discriminate H
    end.
  - match goal with
    | [ H : unspool_app (EApp (ECast eb γ) ea) [] = _ |- _ ] =>
        simpl in H; injection H as Hh _; discriminate
    end.
  - match goal with
    | [ H : decomp_coerc_arrow γ = Some _ |- _ ] => rewrite Hdec in H; discriminate
    end.
Qed.

(** Rule App-Spine keeps its own premises: no other rule can fire where it
    fires, given that the operator already has a value. *)
Lemma eval_app_spine_inv : forall Φ Γ ef ea ef0 v,
  sat Φ = true ->
  ~ Whnf Γ ef ->
  is_cast ef = false ->
  Φ ; Γ ⊢ ef ⇓ ef0 ->
  Φ ; Γ ⊢ EApp ef ea ⇓ v ->
  exists ef', Φ ; Γ ⊢ ef ⇓ ef' /\ Φ ; Γ ⊢ EApp ef' ea ⇓ v.
Proof.
  intros Φ Γ ef ea ef0 v Hsat Hnw Hguard Heval0 Heval.
  inversion Heval; subst; try prune_absurd.
  - exfalso. apply Hnw. apply Whnf_Clos.
  - eexists. split; eassumption.
  - exfalso. match goal with
    | [ Hu : unspool_app (EApp ef ea) [] = (EPrimOp ?p, ?args),
        Hl : Datatypes.length ?args = primop_arity ?p |- _ ] =>
        exact (prim_operator_has_no_value Φ Γ ef ea p args ef0 Hsat Hu Hl Heval0)
    end.
  - exfalso. discriminate Hguard.
  - exfalso. apply Hnw. apply Whnf_Bot.
Qed.

Lemma eval_app_prim_inv : forall Φ Γ ef ea p args v,
  sat Φ = true ->
  unspool_app (EApp ef ea) [] = (EPrimOp p, args) ->
  Datatypes.length args = primop_arity p ->
  Φ ; Γ ⊢ EApp ef ea ⇓ v ->
  exists args', Forall2 (eval Inf Φ Γ) args args' /\ v = reduce_prim p args'.
Proof.
  intros Φ Γ ef ea p args v Hsat Hun Hlen Heval.
  inversion Heval; subst; try prune_absurd.
  - simpl in Hun. injection Hun as Hh _. discriminate.
  - exfalso. match goal with
    | [ He : eval _ Φ Γ ef ?ef' |- _ ] =>
        exact (prim_operator_has_no_value Φ Γ ef ea p args ef' Hsat Hun Hlen He)
    end.
  - match goal with
    | [ H : unspool_app (EApp ef ea) [] = (EPrimOp ?q, ?qargs) |- _ ] =>
        assert (Heq : (EPrimOp q, qargs) = (EPrimOp p, args)) by (rewrite <- H; exact Hun)
    end.
    injection Heq as Hp Hargs. subst.
    eexists. split; [eassumption | reflexivity].
  - simpl in Hun. injection Hun as Hh _. discriminate.
  - simpl in Hun. injection Hun as Hh _. discriminate.
Qed.

Lemma fold_alts_con_inv : forall f Φ Γ e d ea xs ep alts r,
  decompose_con_app e = Some (d, ea) ->
  find_alt d alts = Some (xs, ep) ->
  fold_alts f Φ Γ e alts r ->
  eval (dec f) Φ (extend_env_multi Γ xs ea Γ) ep r.
Proof.
  intros f Φ Γ e d ea xs ep alts r Hdec Hfind Hfold.
  inversion Hfold; subst; unfold decompose_con_app in Hdec; simpl in Hdec;
    try discriminate.
  - match goal with
    | [ H : decompose_con_app e = Some (?D, ?EA) |- _ ] =>
        unfold decompose_con_app in H;
        assert (Heq : Some (D, EA) = Some (d, ea)) by (rewrite <- H; exact Hdec)
    end.
    injection Heq as Hd Hea. subst.
    match goal with
    | [ H : find_alt d alts = Some (?XS, ?EP) |- _ ] =>
        assert (Heq2 : Some (XS, EP) = Some (xs, ep)) by (rewrite <- H; exact Hfind)
    end.
    injection Heq2 as Hxs Hep. subst. assumption.
  - match goal with
    | [ H : match decompose_con_app ?E with _ => _ end |- _ ] =>
        unfold decompose_con_app in H; rewrite Hdec in H; congruence
    end.
Qed.

Lemma fold_alts_bot_inv : forall f Φ Γ b alts r,
  fold_alts f Φ Γ (EBot b) alts r -> r = EBot b.
Proof.
  intros f Φ Γ b alts r Hfold.
  inversion Hfold; subst; try reflexivity; try discriminate.
Qed.

Lemma fold_alts_otherwise_inv : forall f Φ Γ e alts r,
  is_if e = false ->
  (match decompose_con_app e with
   | Some (d, _) => find_alt d alts = None
   | None => True
   end) ->
  is_bot e = false ->
  fold_alts f Φ Γ e alts r ->
  r = EBot BUndefined.
Proof.
  intros f Φ Γ e alts r Hif Hno Hbot Hfold.
  inversion Hfold; subst; simpl in *; try discriminate; try reflexivity.
  - exfalso. match goal with
    | [ Hd : decompose_con_app e = Some (?D, ?EA),
        Hf : find_alt ?D alts = Some _ |- _ ] =>
        rewrite Hd in Hno; rewrite Hno in Hf; discriminate
    end.
Qed.

(**
  Determinism itself, as a pair of mutually recursive fixpoints, for the
  same reason as concore_eval_closed_fix: Rule App-Prim needs the statement
  for every argument of its Forall2, and the derived induction scheme
  supplies no induction hypothesis there.

  The recursion runs on the FIRST derivation. The second one is taken apart
  by the inversion lemmas above, so nothing depends on its shape.

  Unlimited budget only, hence the k0 = Inf premise. Determinism is what a
  finite budget costs: at Fin 0 the literal ELit l reduces both to itself by
  Rule Lit and to EBot BUndefined by Rule Out-Of-Fuel.
*)
Fixpoint eval_det_fix (k0 : fuel) (Φ : path_condition) (Γ : environment) (e v1 : expr)
  (Heval : eval k0 Φ Γ e v1) {struct Heval} :
  k0 = Inf ->
  forall v2, sat Φ = true -> concrete_env Γ -> concore_expr e ->
    Φ; Γ ⊢ e ⇓ v2 -> v1 = v2
with fold_alts_det_fix (k0 : fuel) (Φ : path_condition) (Γ : environment) (e : expr)
  (alts : list alt) (r1 : expr) (Hfold : fold_alts k0 Φ Γ e alts r1) {struct Hfold} :
  k0 = Inf ->
  forall r2, sat Φ = true -> concrete_env Γ -> concore_expr e ->
    Forall concore_alt alts -> fold_alts Inf Φ Γ e alts r2 -> r1 = r2.
Proof.
{
  destruct Heval as
    [ kv Φ Γ x Γ' e0 e' Hlook Heval_x
    | kv Φ Γ x Hnone
    | kv Φ Γ l
    | kv Φ Γ d
    | kv Φ Γ e0 γ e' Heval_e
    | kv Φ Γ Γ' x eb ea eb' Heval_b
    | kv Φ Γ ef ea ef' er Hnotwhnf Hnoarrow Heval_f Heval_app2
    | kv Φ Γ b
    | kv Φ Γ ef ea p args args' Hunspool Harity Hargs
    | kv Φ Γ x e0
    | kv Φ Γ ef γ ea γ_a γ_r er Hdecomp Heval_pushed
    | kv Φ Γ b ea
    | kv Φ Γ es alts es' er Heval_es Hfold
    | kv Φ Γ ec et ef ec' et' ef' pc_c Heval_c Hpc Heval_t Heval_ff
    | kv Φ Γ γ
    | kv Φ Γ e0 Hunsat
    | kv Φ Γ τ
    | Φ Γ e0
    ]; intros Hk0; try discriminate Hk0; subst kv; intros v2 Hsat Henv Hcon H2.
  - (* Rule Var *)
    destruct (lookup_env_concrete Γ x Γ' e0 Henv Hlook) as [Henv' He].
    exact (eval_det_fix Inf Φ Γ' e0 e' Heval_x eq_refl v2 Hsat Henv' He
             (eval_var_bound_inv Φ Γ x Γ' e0 v2 Hsat Hlook H2)).
  - (* Rule Sym-Var *) symmetry. exact (eval_var_free_inv Φ Γ x v2 Hsat Hnone H2).
  - (* Rule Lit *) symmetry. exact (eval_lit_inv Φ Γ l v2 Hsat H2).
  - (* Rule Con *) symmetry. exact (eval_con_inv Φ Γ d v2 Hsat H2).
  - (* Rule Cast *)
    destruct (eval_cast_inv Φ Γ e0 γ v2 Hsat H2) as [e2' [He2 Heq]]. subst v2.
    f_equal.
    exact (eval_det_fix Inf Φ Γ e0 e' Heval_e eq_refl e2' Hsat Henv
             (concore_expr_cast e0 γ Hcon) He2).
  - (* Rule App-Abs *)
    pose proof (concore_expr_app_l _ _ Hcon) as Hclos.
    pose proof (concore_expr_app_r _ _ Hcon) as Hea.
    exact (eval_det_fix Inf Φ (extend_env Γ' x Γ ea) eb eb' Heval_b eq_refl v2 Hsat
             (concrete_env_extend Γ' x Γ ea (concore_expr_clos_env _ _ _ Hclos) Henv Hea)
             (concore_expr_clos _ _ _ Hclos)
             (eval_app_clos_inv Φ Γ Γ' x eb ea v2 Hsat H2)).
  - (* Rule App-Spine *)
    pose proof (concore_expr_app_l _ _ Hcon) as Hcf.
    pose proof (concore_expr_app_r _ _ Hcon) as Hca.
    destruct (eval_app_spine_inv Φ Γ ef ea ef' v2 Hsat Hnotwhnf Hnoarrow Heval_f H2)
      as [ef2 [Hef2 Happ2]].
    assert (Heqf : ef' = ef2)
      by exact (eval_det_fix Inf Φ Γ ef ef' Heval_f eq_refl ef2 Hsat Henv Hcf Hef2).
    subst ef2.
    exact (eval_det_fix Inf Φ Γ (EApp ef' ea) er Heval_app2 eq_refl v2 Hsat Henv
             (Con_App ef' ea (concore_eval_closed_fix Inf Φ Γ ef ef' Heval_f Hsat Henv Hcf) Hca)
             Happ2).
  - (* Rule Bot *) symmetry. exact (eval_bot_inv Φ Γ b v2 Hsat H2).
  - (* Rule App-Prim *)
    assert (Hcon_args : Forall concore_expr args).
    { destruct (unspool_app_concore (EApp ef ea) [] (EPrimOp p) args Hunspool Hcon
                 (Forall_nil _)) as [_ Hforall]. exact Hforall. }
    destruct (eval_app_prim_inv Φ Γ ef ea p args v2 Hsat Hunspool Harity H2)
      as [args2 [Hargs2 Heq]]. subst v2.
    f_equal.
    clear Hunspool Harity Hcon H2.
    revert args2 Hargs2 Hcon_args.
    induction Hargs as [| a0 a0' tl tl' Ha0 Htl IH]; intros args2 Hargs2 Hcon_args;
      inversion Hargs2 as [| b0 b0' tl2 tl2' Hb0 Htl2]; subst.
    + reflexivity.
    + inversion Hcon_args as [| c0 ctl Hc0 Hctl]; subst.
      f_equal.
      * exact (eval_det_fix Inf Φ Γ a0 a0' Ha0 eq_refl b0' Hsat Henv Hc0 Hb0).
      * exact (IH tl2' Htl2 Hctl).
  - (* Rule Lam *) symmetry. exact (eval_lam_inv Φ Γ x e0 v2 Hsat H2).
  - (* Rule App-Cast *)
    pose proof (concore_expr_app_l _ _ Hcon) as Hcast.
    pose proof (concore_expr_app_r _ _ Hcon) as Hea.
    exact (eval_det_fix Inf Φ Γ (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r) er
             Heval_pushed eq_refl v2 Hsat Henv
             (Con_Cast _ γ_r (Con_App _ _ (concore_expr_cast _ _ Hcast)
                                          (Con_Cast _ _ Hea)))
             (eval_app_cast_arrow_inv Φ Γ ef γ γ_a γ_r ea v2 Hsat Hdecomp H2)).
  - (* Rule App-Bot *) symmetry. exact (eval_app_bot_inv Φ Γ b ea v2 Hsat H2).
  - (* Rule Case *)
    destruct (eval_case_inv Φ Γ es alts v2 Hsat H2) as [es2 [Hes2 Hfold2]].
    assert (Hces : concore_expr es) by exact (concore_expr_case_es es alts Hcon).
    assert (Halts : Forall concore_alt alts) by (inversion Hcon; subst; assumption).
    assert (Heq : es' = es2)
      by exact (eval_det_fix Inf Φ Γ es es' Heval_es eq_refl es2 Hsat Henv Hces Hes2).
    subst es2.
    exact (fold_alts_det_fix Inf Φ Γ (merge es') alts er Hfold eq_refl v2 Hsat Henv
             (merge_concore es' (concore_eval_closed_fix Inf Φ Γ es es' Heval_es Hsat Henv Hces))
             Halts Hfold2).
  - (* Rule If: a ConCore expression is never a branch *)
    exfalso. exact (not_concore_if ec et ef Hcon).
  - (* Rule Coercion *) symmetry. exact (eval_coercion_inv Φ Γ γ v2 Hsat H2).
  - (* Rule Prune: the path condition holds *)
    exfalso. rewrite Hsat in Hunsat. discriminate.
  - (* Rule Type *) symmetry. exact (eval_type_inv Φ Γ τ v2 Hsat H2).
}
{
  destruct Hfold as
    [ kv Φ Γ ec et ef alts et' ef' pc_c Hpc Hfold_t Hfold_f
    | kv Φ Γ ec et ef alts Hpc_none
    | kv Φ Γ e0 d ea xs ep alts er Hdec Halt Heval_ep
    | kv Φ Γ b alts
    | kv Φ Γ e0 alts Hnotif Hnoalt Hnotbot
    ]; intros Hk0; subst kv; intros r2 Hsat Henv Hcon Halts H2.
  - exfalso. exact (not_concore_if ec et ef Hcon).
  - exfalso. exact (not_concore_if ec et ef Hcon).
  - (* a constructor alternative matches *)
    assert (Hea : Forall concore_expr ea)
      by exact (decompose_con_app_concore e0 d ea Hdec Hcon).
    assert (Hep : concore_expr ep)
      by exact (find_alt_concore d alts xs ep Halt Halts).
    exact (eval_det_fix Inf Φ (extend_env_multi Γ xs ea Γ) ep er Heval_ep eq_refl r2 Hsat
             (concrete_env_extend_multi xs ea Γ Γ Henv Henv Hea) Hep
             (fold_alts_con_inv Inf Φ Γ e0 d ea xs ep alts r2 Hdec Halt H2)).
  - (* a bottom scrutinee *) symmetry. exact (fold_alts_bot_inv Inf Φ Γ b alts r2 H2).
  - (* no alternative matches *)
    symmetry.
    exact (fold_alts_otherwise_inv Inf Φ Γ e0 alts r2 Hnotif Hnoalt Hnotbot H2).
}
Qed.

(** A ConCore program run in a ConCore environment has at most one value. *)
Lemma concore_eval_deterministic : forall Γ e v1 v2,
  concrete_env Γ ->
  concore_expr e ->
  Γ ⊢ᶜ e ⇓ᶜ v1 ->
  Γ ⊢ᶜ e ⇓ᶜ v2 ->
  v1 = v2.
Proof.
  intros Γ e v1 v2 Henv Hcon H1 H2.
  exact (eval_det_fix Inf pc_true Γ e v1 H1 eq_refl v2 sat_pc_true Henv Hcon H2).
Qed.

(** A whole program starts in the empty environment, which is ConCore, so
    the program's value is unique outright. *)
Corollary concore_eval_deterministic_top : forall e v1 v2,
  concore_expr e -> ⊢ᶜ e ⇓ᶜ v1 -> ⊢ᶜ e ⇓ᶜ v2 -> v1 = v2.
Proof.
  intros e v1 v2 Hcon H1 H2.
  exact (concore_eval_deterministic · e v1 v2 CEnv_Empty Hcon H1 H2).
Qed.

(** The term of Section 12.3 now has exactly one value, the one Rule
    App-Cast gives it. The App-Spine value it used to have as well was the
    coercion being dropped on the floor. *)
Corollary casted_application_value_unique :
  (forall Γ0 x body γ, cast_expr (EClos Γ0 x body) γ = EClos Γ0 x body) ->
  forall v, · ⊢ᶜ EApp coerced_operator plain_operand ⇓ᶜ v ->
  v = EClos (extend_env · "x" · coerced_operand) "z" (EVar "x").
Proof.
  intros Herase v Hv.
  apply (concore_eval_deterministic_top (EApp coerced_operator plain_operand));
    [| exact Hv | exact (casted_application_by_app_cast Herase)].
  apply Con_App; [| apply Con_Con].
  apply Con_Cast. apply Con_Lam. apply Con_Lam. apply Con_Var.
Qed.

(**
  The environment hypothesis of concore_eval_deterministic cannot be
  dropped. Restricting the EXPRESSION to ConCore is not enough, because a
  ConCore expression can be a variable and nothing so far says what the
  environment binds it to. Bind it to a branch whose guard cannot hold and
  Section 12.1 runs again, one Rule Var deeper.
*)
Definition ConcoreEvalDeterministic : Prop :=
  forall Γ e v1 v2, concore_expr e ->
    Γ ⊢ᶜ e ⇓ᶜ v1 -> Γ ⊢ᶜ e ⇓ᶜ v2 -> v1 = v2.

Lemma env_branch_breaks_concore_determinism : forall Γ0 ec pc (x : var),
  pc_true ; Γ0 ⊢ ec ⇓ ec ->
  expr_to_pc Γ0 ec = Some pc ->
  sat (pc_true ∧ pc) = false ->
  ~ ConcoreEvalDeterministic.
Proof.
  intros Γ0 ec pc x Hec Hpc Hunsat Hdet.
  assert (Hlook : lookup_env (extend_env · x Γ0
                    (EIf ec (EBot BUndefined) (EBot BUndefined))) x
                  = Some (Γ0, EIf ec (EBot BUndefined) (EBot BUndefined))).
  { simpl. destruct (string_dec x x); [reflexivity | congruence]. }
  assert (H1 : extend_env · x Γ0 (EIf ec (EBot BUndefined) (EBot BUndefined))
                 ⊢ᶜ EVar x ⇓ᶜ EIf ec (EBot BUndefined) (EBot BUndefined)).
  { unfold eval_con. eapply Eval_Var; [exact Hlook |].
    eapply Eval_If; [exact Hec | exact Hpc | apply Eval_Bot | apply Eval_Bot]. }
  assert (H2 : extend_env · x Γ0 (EIf ec (EBot BUndefined) (EBot BUndefined))
                 ⊢ᶜ EVar x ⇓ᶜ EIf ec (EBot BUnreachable) (EBot BUndefined)).
  { unfold eval_con. eapply Eval_Var; [exact Hlook |].
    eapply Eval_If;
      [exact Hec | exact Hpc | apply Eval_Prune; exact Hunsat | apply Eval_Bot]. }
  specialize (Hdet _ _ _ _ (Con_Var x) H1 H2). discriminate.
Qed.

(** The smallest such binding uses a symbolic variable as the guard. *)
Corollary unsatisfiable_guard_in_environment_breaks_concore_determinism :
  forall (x y : var),
  sat (pc_true ∧ PCVar y) = false ->
  ~ ConcoreEvalDeterministic.
Proof.
  intros x y Hunsat.
  apply (env_branch_breaks_concore_determinism · (EVar y) (PCVar y) x).
  - apply Eval_SymVar. reflexivity.
  - reflexivity.
  - exact Hunsat.
Qed.

(** ------------------------------------------------------------------------- *)
(** 12.5 What replaced Rule App-Cast-Opaque                                   *)
(** ------------------------------------------------------------------------- *)

(**
  This section used to argue that Rule App-Cast-Opaque had to be a rule.
  That argument is superseded. Here is the history, the hole the old
  argument found, and the guard that closes it instead.

  ConCore.v first ASSUMED the rule rather than stating it:

    Axiom cast_expr_eval_app : forall Φ Γ eb eb' γ ea v,
      Φ; Γ ⊢ eb ⇓ eb' ->
      Φ; Γ ⊢ EApp (cast_expr eb' γ) ea ⇓ v ->
      Φ; Γ ⊢ EApp (ECast eb γ) ea ⇓ v.

  The assumption was then written out as Rule App-Cast-Opaque in SymCore.v.
  The reason given was this. Soundness must replay every symbolic step on
  the concrete side. Rule App-Spine at the time refused only an operator
  whose coercion splits into an arrow, so it accepted a cast operator whose
  coercion does not split, PROVIDED the operator was not yet a value. The
  concrete operator is the same cast with the same coercion - concretion
  does not turn a cast into anything else - but it need not still be a
  non-value: being a value is not preserved by concretion, as
  whnf_not_preserved_by_concretion below shows. So the concrete run could
  arrive at "apply a VALUE carrying a coercion that does not split", where
  Rule App-Cast wants a coercion that splits and Rule App-Spine wants an
  operator that is not a value. The concrete run would be stuck while the
  symbolic run walked on, and soundness would be false. Rule
  App-Cast-Opaque was the patch for that gap.

  The gap was real. The patch was not the only one, and not the right one.
  The gap opened because Rule App-Spine's guard tested the COERCION, so the
  two sides could disagree about whether the rule applied - the symbolic
  side allowed the step, the concrete side did not. Rule App-Spine now
  tests the OPERATOR instead: it refuses every cast, value or not. The two
  sides can no longer disagree, because the test no longer mentions
  anything that concretion can change.

  Three facts carry the replacement, and all three are proved above.

  1. eval_app_cast_opaque_stuck. On the shape "(e ⊲ γ) ea with γ not an
     arrow", no rule fires at all. Symbolically at any satisfiable path
     condition, and so concretely at pc_true as well. Both sides are stuck,
     together. Soundness never has to replay the step, because there is no
     step on either side.

  2. contains_is_cast. If the symbolic operator is not a cast and not a
     branch, the concrete operator is not a cast either. So a Rule
     App-Spine step on the symbolic side always meets a non-cast operator
     on the concrete side, and Rule App-Spine's own guard is satisfied
     there too.

  3. eval_app_if_false. An application whose operator is a branch has no
     value. That is what excludes the one concretion rule that changes the
     shape of a term, and it is why fact 2 may assume the operator is not a
     branch. The corollary just below packages facts 2 and 3 into the exact
     step eval_app_spine_sound takes.

  What this costs is stated honestly: a program whose operator evaluates to
  a cast with a non-arrow coercion now has no value. That is deliberate.
  Such a term applies something whose coercion does not split, which is
  applying a non-function, and System FC rejects it at type-check time.
  This judgement has no typing rules, so it gets stuck there rather than
  inventing an answer. scratch/OpaqueCastOperatorReachable.v holds the
  witness program and records which of its claims flipped.
*)

(**
  The load-bearing step of eval_app_spine_sound, on its own. When the
  symbolic side takes Rule App-Spine, the concrete operator passes Rule
  App-Spine's guard as well.
*)
Corollary app_spine_concrete_operator_is_not_a_cast :
  forall Φ Γs σ S ef ea ef' er fc,
  sat Φ = true ->
  is_cast ef = false ->
  contains σ S ef fc ->
  Φ ; Γs ⊢ ef ⇓ ef' ->
  Φ ; Γs ⊢ EApp ef' ea ⇓ er ->
  is_cast fc = false.
Proof.
  intros Φ Γs σ S ef ea ef' er fc Hsat Hnocast Hcont Heval1 Heval2.
  assert (Hnotif : is_if ef = false).
  { destruct (is_if ef) eqn:Hif; [| reflexivity].
    exfalso. apply (eval_app_if_false Φ Γs (EApp ef' ea) er Heval2 Hsat ef' ea eq_refl).
    exact (eval_preserves_if Φ Γs ef ef' Heval1 Hsat Hif). }
  rewrite (contains_is_cast σ S ef fc Hcont Hnotif). exact Hnocast.
Qed.
Lemma whnf_not_preserved_by_concretion : forall σ S Γs Γc p ec l,
  models_cond σ S ec ->
  contains σ S (EApp (EPrimOp p) (EIf ec (ELit l) (ELit l)))
               (EApp (EPrimOp p) (ELit l))
  /\ ~ Whnf Γs (EApp (EPrimOp p) (EIf ec (ELit l) (ELit l)))
  /\ Whnf Γc (EApp (EPrimOp p) (ELit l)).
Proof.
  intros σ S Γs Γc p ec l Hmc. split; [| split].
  - apply Cont_App; [apply Cont_PrimOp |].
    apply Cont_If_True; [exact Hmc | apply Cont_Lit].
  - intro Hw. inversion Hw as [e0 Hsolv | | | | | | | ]; subst.
    inversion Hsolv as [| | | f a Hop Hf Ha]; subst.
    inversion Ha.
  - apply Whnf_Solvable. apply Solvable_AppPrim;
      [reflexivity | apply Solvable_PrimOp | apply Solvable_Lit].
Qed.

(** ========================================================================= *)
(** 13. Completeness of Symbolic Execution                                    *)
(** ========================================================================= *)

(**
  Completeness is the converse of Section 10: whenever the concrete run
  delivers a value, the symbolic run delivers one that matches it.

  It is stated here rather than next to concore_soundness because its proof
  needs concore_eval_deterministic from Section 12. A concrete program has at
  most one value, and that is what lets the value soundness produces be
  identified with the value the theorem is handed.

  WHY A BUDGET IS IN THE STATEMENT. Rule If asks for a derivation of BOTH
  arms, while the concrete run exercises one. The symbolic execution never
  consults the model, so it cannot skip the arm the model does not take. If
  that arm loops forever, the unlimited budget has no derivation for it and
  Rule If cannot fire at all - the whole symbolic run is blocked by a piece
  of the program the concrete run never entered. A finite budget unblocks it:
  the loop drives the budget to zero, Rule Out-Of-Fuel answers, and Rule If
  gets its second premise. scratch/DivergenceNeedsFuel.v is the worked
  counterexample, and Section 14 below repeats it against this theorem.

  WHY A BUDGET IS NOT ENOUGH. A budget rescues an arm that LOOPS. It does not
  rescue an arm that is STUCK, because a stuck term has no derivation at any
  positive budget either, and at budget zero the whole program truncates
  instead. scratch/CompletenessNeedsFuel.v proves this. So completeness is
  stated for programs with no stuck subterm, and the predicate no_stuck below
  is what says that.
*)

(** ------------------------------------------------------------------------- *)
(** 13.1 Budget-Total Terms                                                   *)
(** ------------------------------------------------------------------------- *)

(**
  A term is budget-total when, from some budget on, every budget gives it a
  value. The value may change with the budget, and that is the point: the
  arm the model does not take is never inspected, so any answer will do.

  Three kinds of term are budget-total.
  - A term that terminates. eval_inf_has_budget turns its unlimited-budget
    derivation into one at every budget from its height on; see
    budget_total_of_terminating below.
  - A term that loops. self_app_has_value_at_every_budget in SymCore.v
    Section 10.5 proves it for the self-application loop: the budget runs out
    and Rule Out-Of-Fuel answers.
  - Nothing else. A stuck term has no value at any positive budget, which is
    what completeness_rejects_a_stuck_arm in Section 14 shows.

  The threshold h is a refinement of the plainer "forall n, exists v". The
  plainer form is stronger, so assuming it would make the theorem weaker, and
  it would exclude terms that merely need room to finish. A term that needs
  four steps has no value at a budget of three, and that is not stuckness.
*)
Definition budget_total (Φ : path_condition) (Γ : environment) (e : expr) : Prop :=
  exists h, forall n, (h <= n)%nat -> exists v, eval (Fin n) Φ Γ e v.

Lemma budget_total_of_terminating : forall Φ Γ e,
  (exists v, Φ ; Γ ⊢ e ⇓ v) -> budget_total Φ Γ e.
Proof.
  intros Φ Γ e [v Hv].
  destruct (eval_inf_has_budget Φ Γ e v Hv) as [h Hh].
  exists h. intros n Hn. exists v. apply Hh. exact Hn.
Qed.

(** ------------------------------------------------------------------------- *)
(** 13.2 The No-Stuck-Subterm Hypothesis                                      *)
(** ------------------------------------------------------------------------- *)

(**
  no_stuck σ S Φ Γ e_sym e_con says: along the path the model σ takes through
  the branches of e_sym, nothing is stuck.

  The predicate walks down the branches of e_sym. At each branch it asks for
  three things, and at the bottom it asks for one.

  At a branch (Rules NS_Then and NS_Else):
  - the guard has ONE value ec' at every budget, so the formula Rule If reads
    off the guard does not depend on the budget. It has to be one value: the
    arms below are evaluated under Φ ∧ pc, and a formula that changed with
    the budget would change the path condition the recursion runs under.
  - the model reads the guard's value the same way it reads the guard. This
    is what eval_models_cond assumes of the solver at the unlimited budget;
    here it is asked for directly, because the guard is evaluated at a finite
    budget and that axiom does not reach there.
  - the arm the model does NOT take is budget-total. This is the whole point
    of the budget, and the only place the predicate tolerates a loop.

  At the bottom (Rule NS_Leaf): the term is not a branch, it is the
  concretion's counterpart, and it has a value at the unlimited budget. That
  last clause is the no-stuck condition proper. It says only that a value
  exists; which value it is, and that it matches the concrete run, is what
  the theorem proves.

  WHY THE PREDICATE MENTIONS e_con. It has to know which arm the model takes,
  because only the other arm may loop. The verdict is models_cond σ S ec for
  one arm and models_not_cond σ S ec for the other, and this development
  cannot prove those two are exclusive: models is a Parameter and the only
  facts about it are models_sat and models_and_iff, neither of which forbids
  a model from satisfying both a formula and its negation. So the branch the
  predicate descends into cannot be read off the symbolic side alone, and the
  concretion is what picks it. no_stuck_contains below shows the cost is
  nothing: the predicate already implies the concretion it mentions.
*)
Inductive no_stuck (σ : valuation) (S : symvars)
  : path_condition -> environment -> expr -> expr -> Prop :=
  | NS_Leaf : forall Φ Γ e e_con,
      is_if e = false ->
      contains σ S e e_con ->
      (exists v, Φ ; Γ ⊢ e ⇓ v) ->
      no_stuck σ S Φ Γ e e_con
  | NS_Then : forall Φ Γ ec et ef ec' pc e_con,
      (forall n, eval (Fin n) Φ Γ ec ec') ->
      models_cond σ S ec ->
      models_cond σ S ec' ->
      expr_to_pc Γ ec' = Some pc ->
      budget_total (Φ ∧ ¬ pc) Γ ef ->
      no_stuck σ S (Φ ∧ pc) Γ et e_con ->
      no_stuck σ S Φ Γ (EIf ec et ef) e_con
  | NS_Else : forall Φ Γ ec et ef ec' pc e_con,
      (forall n, eval (Fin n) Φ Γ ec ec') ->
      models_not_cond σ S ec ->
      models_not_cond σ S ec' ->
      expr_to_pc Γ ec' = Some pc ->
      budget_total (Φ ∧ pc) Γ et ->
      no_stuck σ S (Φ ∧ ¬ pc) Γ ef e_con ->
      no_stuck σ S Φ Γ (EIf ec et ef) e_con.

(** The hypothesis already carries the concretion it is stated against. *)
Lemma no_stuck_contains : forall σ S Φ Γ e e_con,
  no_stuck σ S Φ Γ e e_con -> contains σ S e e_con.
Proof.
  intros σ S Φ Γ e e_con H. induction H.
  - assumption.
  - apply Cont_If_True; assumption.
  - apply Cont_If_False; assumption.
Qed.

(** ------------------------------------------------------------------------- *)
(** 13.3 Completeness, Upward Closed in the Budget                            *)
(** ------------------------------------------------------------------------- *)

(**
  The statement is upward closed on purpose. "Some budget works" does not
  survive the induction, for the same reason it did not survive the induction
  in eval_fin_of_inf_fix: a bigger budget is not always safe, so the only
  claim a branch can pass up to the branch above is "every budget from here
  on works". Rule If then combines the two budgets its premises report with
  max and spends one more on itself.

  The value found at budget n is allowed to depend on n. It has to be: the
  arm the model skips answers something different at every budget, and that
  answer sits inside the value. What does not depend on n is the concretion:
  Rule Cont_If_True never looks at the arm it did not take, so whatever the
  skipped arm answered, the value still matches the concrete one.

  Where the budget comes from at the bottom. The leaf has an unlimited-budget
  derivation, so concore_soundness gives it a concrete value, and
  concore_eval_deterministic identifies that value with the one the theorem
  was handed - a concrete program has at most one. eval_inf_has_budget then
  turns the leaf's unlimited-budget derivation into a finite one, and its
  threshold is the budget the whole recursion is built on.
*)
Lemma completeness_upward : forall σ S Φ Γs e_sym e_con,
  no_stuck σ S Φ Γs e_sym e_con ->
  forall Γc v_con,
    σ ⊨ Φ ->
    contains_env σ S Γs Γc ->
    concore_expr e_con ->
    Γc ⊢ᶜ e_con ⇓ᶜ v_con ->
    exists h, forall n, (h <= n)%nat ->
      exists v_sym, eval (Fin n) Φ Γs e_sym v_sym /\ contains σ S v_sym v_con.
Proof.
  intros σ S Φ Γs e_sym e_con H.
  induction H as
    [ Φ Γ e e_con Hnotif Hcont [v Hv]
    | Φ Γ ec et ef ec' pc e_con Hguard Hmc Hmc' Hpc Htot Hns IH
    | Φ Γ ec et ef ec' pc e_con Hguard Hmnc Hmnc' Hpc Htot Hns IH ];
    intros Γc v_con Hmod Henv Hcon Hevalc.
  - (* the leaf: soundness carries the concrete run back, determinism pins the value *)
    destruct (concore_soundness Φ Γ Γc σ S e e_con v Hmod Henv Hcont Hcon Hv)
      as [v_con' [Hec Hcv]].
    assert (Hcenv : concrete_env Γc) by (eapply contains_env_concrete; exact Henv).
    assert (Heqv : v_con' = v_con)
      by (eapply concore_eval_deterministic; eassumption).
    subst v_con'.
    destruct (eval_inf_has_budget Φ Γ e v Hv) as [h Hh].
    exists h. intros n Hn. exists v. split; [apply Hh; exact Hn | exact Hcv].
  - (* the model takes the then-arm; the else-arm only has to answer something *)
    assert (Hpcmod : σ ⊨ pc) by (eapply models_cond_pc; eassumption).
    assert (Hmod_and : σ ⊨ (Φ ∧ pc)) by (apply models_and; assumption).
    destruct (IH Γc v_con Hmod_and Henv Hcon Hevalc) as [h1 Hh1].
    destruct Htot as [h2 Hh2].
    exists (Datatypes.S (Nat.max h1 h2)). intros n Hn. destruct n as [| m]; [lia |].
    destruct (Hh1 m ltac:(lia)) as [et' [Het' Hcet']].
    destruct (Hh2 m ltac:(lia)) as [ef' Hef'].
    exists (EIf ec' et' ef'). split.
    + eapply Eval_If;
        [ simpl; apply Hguard | exact Hpc | simpl; exact Het' | simpl; exact Hef' ].
    + apply Cont_If_True; [exact Hmc' | exact Hcet'].
  - (* the model takes the else-arm *)
    assert (Hpcmod : σ ⊨ (¬ pc)) by (eapply models_not_cond_pc; eassumption).
    assert (Hmod_and : σ ⊨ (Φ ∧ ¬ pc)) by (apply models_and; assumption).
    destruct (IH Γc v_con Hmod_and Henv Hcon Hevalc) as [h1 Hh1].
    destruct Htot as [h2 Hh2].
    exists (Datatypes.S (Nat.max h1 h2)). intros n Hn. destruct n as [| m]; [lia |].
    destruct (Hh1 m ltac:(lia)) as [ef' [Hef' Hcef']].
    destruct (Hh2 m ltac:(lia)) as [et' Het'].
    exists (EIf ec' et' ef'). split.
    + eapply Eval_If;
        [ simpl; apply Hguard | exact Hpc | simpl; exact Het' | simpl; exact Hef' ].
    + apply Cont_If_False; [exact Hmnc' | exact Hcef'].
Qed.

(**
  Completeness of symbolic execution.

  The concretion hypothesis is listed even though no_stuck_contains derives
  it from the no-stuck hypothesis. It is what the theorem is about, and
  leaving it out would hide the statement inside a predicate.
*)
Theorem concore_completeness : forall Φ Γs Γc σ S e_sym e_con v_con,
  σ ⊨ Φ ->
  contains_env σ S Γs Γc ->
  contains σ S e_sym e_con ->
  concore_expr e_con ->
  no_stuck σ S Φ Γs e_sym e_con ->
  Γc ⊢ᶜ e_con ⇓ᶜ v_con ->
  exists k v_sym, eval (Fin k) Φ Γs e_sym v_sym /\ contains σ S v_sym v_con.
Proof.
  intros Φ Γs Γc σ S e_sym e_con v_con Hmod Henv Hcont Hcon Hns Hevalc.
  destruct (completeness_upward σ S Φ Γs e_sym e_con Hns Γc v_con Hmod Henv Hcon Hevalc)
    as [h Hh].
  destruct (Hh h ltac:(lia)) as [v_sym [Heval Hcv]].
  exists h, v_sym. split; assumption.
Qed.

(** Top-level completeness for whole programs starting from · *)
Corollary concore_completeness_top : forall Φ σ S e_sym e_con v_con,
  σ ⊨ Φ ->
  contains σ S e_sym e_con ->
  concore_expr e_con ->
  no_stuck σ S Φ · e_sym e_con ->
  ⊢ᶜ e_con ⇓ᶜ v_con ->
  exists k v_sym, eval (Fin k) Φ · e_sym v_sym /\ contains σ S v_sym v_con.
Proof.
  intros Φ σ S e_sym e_con v_con Hmod Hcont Hcon Hns Hevalc.
  eapply concore_completeness; try eassumption. apply Cont_Env_Empty.
Qed.

(** ========================================================================= *)
(** 14. NonVacuity of Completeness                                            *)
(** ========================================================================= *)

(**
  Section 11 exists because the development once carried a theorem whose
  hypotheses nothing satisfied. Completeness gets the same treatment. Three
  things are shown, on one program and with no new axiom.

  (a) The no-stuck hypothesis is SATISFIABLE, and not on a toy: the program
      is a symbolic branch whose untaken arm is the self-application loop, a
      term with no unlimited-budget value at all (self_app_diverges).
  (b) Completeness really applies to it. Every hypothesis is discharged, a
      budget is exhibited, and the whole program is shown to have no
      unlimited-budget value - so the finite budget is not decoration.
  (c) The hypothesis is NOT true of everything. Replace the looping arm by
      the stuck arm of scratch/CompletenessNeedsFuel.v and the predicate has
      no derivation.

  The section takes the model, the symbolic variables and the guard as
  variables, exactly as Section 11 does, so nothing here is assumed globally.
*)

Lemma app_lit_no_value_inf : forall Ψ Γ l a v,
  sat Ψ = true -> Ψ ; Γ ⊢ EApp (ELit l) a ⇓ v -> False.
Proof.
  intros Ψ Γ l a v Hsat Heval.
  inversion Heval; subst; try discriminate.
  - match goal with [ H : ~ Whnf _ (ELit _) |- _ ] =>
      apply H; apply Whnf_Solvable; apply Solvable_Lit end.
  - congruence.
Qed.

(** The same at a positive budget. Rule Out-Of-Fuel fires at Fin 0 only, so
    it cannot rescue the stuck application here. *)
Lemma app_lit_no_value_fin : forall k Ψ Γ l a v,
  sat Ψ = true -> eval (Fin (Datatypes.S k)) Ψ Γ (EApp (ELit l) a) v -> False.
Proof.
  intros k Ψ Γ l a v Hsat Heval.
  inversion Heval; subst; try discriminate.
  - match goal with [ H : ~ Whnf _ (ELit _) |- _ ] =>
      apply H; apply Whnf_Solvable; apply Solvable_Lit end.
  - congruence.
Qed.

Lemma eval_symvar_fin_same : forall k Ψ Γ x v,
  lookup_env Γ x = None -> sat Ψ = true ->
  eval (Fin (Datatypes.S k)) Ψ Γ (EVar x) v -> v = EVar x.
Proof.
  intros k Ψ Γ x v Hnone Hsat Heval.
  inversion Heval; subst; [congruence | reflexivity | congruence].
Qed.

Section CompletenessNonVacuity.

  Variables (Φ : path_condition) (σ : valuation) (Sv : symvars).
  Variables (x : var) (l l' : lit).

  (** x is one of the symbolic variables, the model satisfies the atom x and
      the ambient path condition, and the branch the model does not take is
      feasible. The last one is what keeps Rule Prune from answering for the
      untaken arm and making the exercise trivial. *)
  Hypothesis Hsx : Sv x = true.
  Hypothesis Hmodx : σ ⊨ (PCVar x).
  Hypothesis HmodPhi : σ ⊨ Φ.
  Hypothesis Hfeas : sat (Φ ∧ ¬ PCVar x) = true.

  Lemma guard_denotes : denotes Sv (EVar x) (PCVar x).
  Proof. intros Γ Hfree. simpl. rewrite (Hfree x Hsx). reflexivity. Qed.

  Lemma guard_judged : models_cond σ Sv (EVar x).
  Proof. exists (PCVar x). split; [exact guard_denotes | exact Hmodx]. Qed.

  (** if x then l' else (loop) *)
  Definition live_branch : expr := EIf (EVar x) (ELit l') self_app.

  (* ============ (a) the hypothesis holds of a looping program ============ *)

  Lemma witness_arm_diverges : forall v, ~ ((Φ ∧ ¬ PCVar x) ; · ⊢ self_app ⇓ v).
  Proof. intros v. apply self_app_diverges. exact Hfeas. Qed.

  Lemma witness_no_stuck : no_stuck σ Sv Φ · live_branch (ELit l').
  Proof.
    eapply NS_Then with (ec' := EVar x) (pc := PCVar x).
    - intros n. apply Eval_SymVar. reflexivity.
    - exact guard_judged.
    - exact guard_judged.
    - reflexivity.
    - exists 0%nat. intros n _. apply self_app_has_value_at_every_budget.
    - apply NS_Leaf; [reflexivity | apply Cont_Lit | exists (ELit l'); apply Eval_Lit].
  Qed.

  (* ================= (b) completeness applies to it ====================== *)

  Corollary witness_completeness_instance :
    exists k v_sym, eval (Fin k) Φ · live_branch v_sym /\ contains σ Sv v_sym (ELit l').
  Proof.
    eapply concore_completeness_top with (e_con := ELit l').
    - exact HmodPhi.
    - apply Cont_If_True; [exact guard_judged | apply Cont_Lit].
    - apply Con_Lit.
    - exact witness_no_stuck.
    - apply Eval_Lit.
  Qed.

  (** The budget the recursion computes here is one, and this is what it
      derives: the taken arm reaches its literal, the looping arm runs the
      budget to zero and Rule Out-Of-Fuel answers, and the concretion never
      looks at that answer. *)
  Lemma witness_budget_is_one :
    eval (Fin 1) Φ · live_branch (EIf (EVar x) (ELit l') (EBot BUndefined))
    /\ contains σ Sv (EIf (EVar x) (ELit l') (EBot BUndefined)) (ELit l').
  Proof.
    split.
    - eapply Eval_If with (pc_c := PCVar x).
      + apply Eval_SymVar. reflexivity.
      + reflexivity.
      + apply Eval_Lit.
      + apply Eval_OutOfFuel.
    - apply Cont_If_True; [exact guard_judged | apply Cont_Lit].
  Qed.

  (** And every budget works, which is what completeness_upward claims. The
      value changes with the budget; the concretion does not. *)
  Lemma witness_every_budget : forall n,
    exists v, eval (Fin n) Φ · live_branch v /\ contains σ Sv v (ELit l').
  Proof.
    intros n. destruct n as [| m].
    - destruct (self_app_has_value_at_every_budget 0%nat (Φ ∧ ¬ PCVar x) ·) as [vf Hvf].
      exists (EIf (EVar x) (ELit l') vf). split.
      + eapply Eval_If with (pc_c := PCVar x);
          [apply Eval_SymVar; reflexivity | reflexivity | apply Eval_Lit | exact Hvf].
      + apply Cont_If_True; [exact guard_judged | apply Cont_Lit].
    - destruct (self_app_has_value_at_every_budget m (Φ ∧ ¬ PCVar x) ·) as [vf Hvf].
      exists (EIf (EVar x) (ELit l') vf). split.
      + eapply Eval_If with (pc_c := PCVar x);
          [apply Eval_SymVar; reflexivity | reflexivity | apply Eval_Lit | exact Hvf].
      + apply Cont_If_True; [exact guard_judged | apply Cont_Lit].
  Qed.

  (** The budget is not decoration: at the unlimited budget this program has
      no value at all, because Rule If cannot get past the looping arm. So
      the finite budget in the theorem is carrying the whole statement here. *)
  Lemma witness_has_no_unlimited_value : ~ (exists v, Φ ; · ⊢ live_branch ⇓ v).
  Proof.
    assert (HsatPhi : sat Φ = true) by (apply models_sat with (σ := σ); exact HmodPhi).
    intros [v Hv]. unfold live_branch in Hv.
    inversion Hv as [| | | | | | | | | | | | | kf Φ0 Γ0 ec0 et0 ef0 ec' et' ef' pc_c
                       Hc Hpc Ht Hf | | kf Φ0 Γ0 e0 Hunsat | |]; subst.
    - assert (Hec : ec' = EVar x)
        by (inversion Hc; subst; [discriminate | reflexivity | congruence]).
      subst ec'. simpl in Hpc. injection Hpc as Hpc. subst pc_c.
      exact (self_app_diverges (Φ ∧ ¬ PCVar x) · ef' Hfeas Hf).
    - congruence.
  Qed.

  (* ============ (c) the hypothesis rejects a stuck arm =================== *)

  (** The counterexample of scratch/CompletenessNeedsFuel.v. Applying a
      literal is stuck: no rule matches it, and Rule Prune cannot fire while
      the branch is feasible. *)
  Definition stuck_arm : expr := EApp (ELit l) (ELit l).
  Definition stuck_branch : expr := EIf (EVar x) (ELit l') stuck_arm.

  Lemma completeness_rejects_a_stuck_arm :
    ~ no_stuck σ Sv Φ · stuck_branch (ELit l').
  Proof.
    assert (HsatPhi : sat Φ = true) by (apply models_sat with (σ := σ); exact HmodPhi).
    intros H. inversion H as
      [ Φ0 Γ0 e0 ec0 Hnotif Hcont Hval
      | Φ0 Γ0 ec0 et0 ef0 ec' pc e_con Hguard Hmc Hmc' Hpc Htot Hns
      | Φ0 Γ0 ec0 et0 ef0 ec' pc e_con Hguard Hmnc Hmnc' Hpc Htot Hns ]; subst.
    - discriminate Hnotif.
    - (* the model takes the literal arm, so the stuck arm must be budget-total *)
      assert (Hec : ec' = EVar x)
        by (eapply eval_symvar_fin_same with (k := 0%nat) (Γ := ·);
            [reflexivity | exact HsatPhi | apply (Hguard 1%nat)]).
      subst ec'. simpl in Hpc. injection Hpc as Hpc. subst pc.
      destruct Htot as [h Hh].
      destruct (Hh (Datatypes.S h) ltac:(lia)) as [v Hv].
      eapply app_lit_no_value_fin; [exact Hfeas | exact Hv].
    - (* the model takes the stuck arm, so it must have an unlimited-budget value *)
      assert (Hec : ec' = EVar x)
        by (eapply eval_symvar_fin_same with (k := 0%nat) (Γ := ·);
            [reflexivity | exact HsatPhi | apply (Hguard 1%nat)]).
      subst ec'. simpl in Hpc. injection Hpc as Hpc. subst pc.
      inversion Hns as [ Φ1 Γ1 e1 ec1 Hnotif1 Hcont1 [v Hv] | | ]; subst.
      + eapply app_lit_no_value_inf; [exact Hfeas | exact Hv].
  Qed.

End CompletenessNonVacuity.
