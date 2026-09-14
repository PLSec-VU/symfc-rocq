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
  | CEnv_Empty : concrete_env EmptyEnv
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
  concrete_context EmptyEnv e <-> closed_expr e.
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
  eval pc_true Γ e v.

(** Notation for concrete big-step reduction: Γ ⊢ᶜ e ⇓ᶜ v *)
Notation "Γ '⊢ᶜ' e '⇓ᶜ' v" := (eval_con Γ e v) (at level 70, no associativity).
Notation "'⊢ᶜ' e '⇓ᶜ' v" := (eval_con EmptyEnv e v) (at level 70, no associativity).

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

Axiom cast_expr_eval_app : forall Φ Γ eb eb' γ ea v,
  eval Φ Γ eb eb' ->
  eval Φ Γ (EApp (cast_expr eb' γ) ea) v ->
  eval Φ Γ (EApp (ECast eb γ) ea) v.

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
  the statement for every argument of its Forall2 (eval Φ Γ) args args' in
  order to feed the repaired (argument-conditional) reduce_prim_concore, and
  the derived scheme supplies no induction hypothesis under a Forall2.
*)
Fixpoint concore_eval_closed_fix (Φ : path_condition) (Γ : environment) (e v : expr)
  (Heval : Φ; Γ ⊢ e ⇓ v) {struct Heval} :
  sat Φ = true -> concrete_env Γ -> concore_expr e -> concore_expr v
with concore_fold_closed_fix (Φ : path_condition) (Γ : environment) (e : expr)
  (alts : list alt) (er : expr)
  (Hfold : fold_alts Φ Γ e alts er) {struct Hfold} :
  sat Φ = true -> concrete_env Γ -> concore_expr e -> Forall concore_alt alts -> concore_expr er.
Proof.
{
  destruct Heval as
    [ Φ Γ x Γ' e e' Hlook Heval_x
    | Φ Γ x Hnone
    | Φ Γ l
    | Φ Γ d
    | Φ Γ e γ e' Heval_e
    | Φ Γ Γ' x eb ea eb' Heval_b
    | Φ Γ ef ea ef' er Hnotwhnf Heval_f Heval_app2
    | Φ Γ b
    | Φ Γ ef ea p args args' Hunspool Harity Hargs
    | Φ Γ x e
    | Φ Γ ef γ ea γ_a γ_r er Hdecomp Heval_pushed
    | Φ Γ b ea
    | Φ Γ es alts es' er Heval_es Hfold
    | Φ Γ ec et ef ec' et' ef' pc_c Heval_c Hpc Heval_t Heval_f
    | Φ Γ γ
    | Φ Γ e Hunsat
    | Φ Γ τ
    ]; intros Hsat Henv Hcon.
  - (* Eval_Var *)
    destruct (lookup_env_concrete Γ x Γ' e Henv Hlook) as [Henv' He].
    exact (concore_eval_closed_fix Φ Γ' e e' Heval_x Hsat Henv' He).
  - (* Eval_SymVar *) exact Hcon.
  - (* Eval_Lit *) constructor.
  - (* Eval_Con *) constructor.
  - (* Eval_Cast *)
    apply cast_expr_concore.
    apply (concore_eval_closed_fix Φ Γ e e' Heval_e Hsat Henv).
    inversion Hcon; subst; assumption.
  - (* Eval_AppAbs *)
    inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | ]; subst.
    inversion Hf as [| | | | | | Γ0 x0 body Henv' Hbody | | | | | | | ]; subst.
    apply (concore_eval_closed_fix Φ (extend_env Γ' x Γ ea) eb eb' Heval_b Hsat).
    + apply concrete_env_extend; assumption.
    + assumption.
  - (* Eval_AppSpine *)
    inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | ]; subst.
    apply (concore_eval_closed_fix Φ Γ (EApp ef' ea) er Heval_app2 Hsat Henv).
    apply Con_App; [| assumption].
    exact (concore_eval_closed_fix Φ Γ ef ef' Heval_f Hsat Henv Hf).
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
      * exact (concore_eval_closed_fix Φ Γ a a' Ha Hsat Henv Hcon_a).
      * exact (IH Hcon_tl).
  - (* Eval_Lam *)
    constructor; [assumption |].
    inversion Hcon; subst; assumption.
  - (* Eval_AppCast *)
    inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | ]; subst.
    inversion Hf as [| | | | | | | | e γ0 He | | | | | ]; subst.
    apply (concore_eval_closed_fix Φ Γ (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r)
             er Heval_pushed Hsat Henv).
    apply Con_Cast. apply Con_App; [assumption | apply Con_Cast; assumption].
  - (* Eval_AppBot *)
    inversion Hcon; subst. assumption.
  - (* Eval_Case *)
    inversion Hcon as [| | | | | | | es0 alts0 Hcon_es Hcon_alts | | | | | | ]; subst.
    apply (concore_fold_closed_fix Φ Γ (merge es') alts er Hfold Hsat Henv);
      [| assumption].
    apply merge_concore.
    exact (concore_eval_closed_fix Φ Γ es es' Heval_es Hsat Henv Hcon_es).
  - (* Eval_If *)
    exfalso. apply (not_concore_if ec et ef). assumption.
  - (* Eval_Coercion *) constructor.
  - (* Eval_Prune *) constructor.
  - (* Eval_Type *) constructor.
}
{
  destruct Hfold as
    [ Φ Γ ec et ef alts et' ef' pc_c Hpc Hfold_t Hfold_f
    | Φ Γ ec et ef alts Hpc_none
    | Φ Γ e d ea xs ep alts er Hdec Halt Heval_ep
    | Φ Γ b alts
    | Φ Γ e alts Hnotif Hnoalt Hnotbot
    ]; intros Hsat Henv Hcon Halts.
  - exfalso. apply (not_concore_if ec et ef). assumption.
  - exfalso. apply (not_concore_if ec et ef). assumption.
  - (* FoldAlts_Con *)
    assert (Hea : Forall concore_expr ea).
    { apply decompose_con_app_concore with (e := e) (d := d); assumption. }
    assert (Hep : concore_expr ep).
    { apply find_alt_concore with (d := d) (alts := alts) (xs := xs); assumption. }
    apply (concore_eval_closed_fix Φ (extend_env_multi Γ xs ea Γ) ep er Heval_ep Hsat);
      [| assumption].
    apply concrete_env_extend_multi; assumption.
  - (* FoldAlts_Bot *) exact Hcon.
  - (* FoldAlts_Otherwise *) constructor.
}
Qed.

Theorem concore_eval_closed_mut :
  (forall Φ Γ e v (Heval : Φ; Γ ⊢ e ⇓ v),
     Φ = pc_true -> concrete_env Γ -> concore_expr e -> concore_expr v) /\
  (forall Φ Γ e alts er (Hfold : fold_alts Φ Γ e alts er),
     Φ = pc_true -> concrete_env Γ -> concore_expr e -> Forall concore_alt alts -> concore_expr er).
Proof.
  split.
  - intros Φ Γ e v Heval Heq. subst Φ.
    exact (concore_eval_closed_fix pc_true Γ e v Heval sat_pc_true).
  - intros Φ Γ e alts er Hfold Heq. subst Φ.
    exact (concore_fold_closed_fix pc_true Γ e alts er Hfold sat_pc_true).
Qed.

(** ConCore Closure under Evaluation:
    Concrete evaluation in a concrete environment never escapes ConCore. *)
Theorem concore_eval_closed : forall Γ e v,
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
  apply (concore_eval_closed EmptyEnv e v); auto.
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
Parameter models_cond : valuation -> symvars -> expr -> Prop.
Parameter models_not_cond : valuation -> symvars -> expr -> Prop.

Axiom models_cond_pc : forall σ S Γ e pc,
  expr_to_pc Γ e = Some pc ->
  (models_cond σ S e <-> σ ⊨ pc).

Axiom models_not_cond_pc : forall σ S Γ e pc,
  expr_to_pc Γ e = Some pc ->
  (models_not_cond σ S e <-> σ ⊨ (¬ pc)).

(** Whenever the SMT solver can judge a condition's truth value at all, that
    condition is expressible as a path-condition formula in every environment
    that binds none of the symbolic variables: expr_to_pc never fails on a
    judgeable condition read in a scope that does not capture it. *)
Axiom models_cond_total : forall σ S Γ e,
  sym_free_env S Γ ->
  models_cond σ S e \/ models_not_cond σ S e ->
  exists pc, expr_to_pc Γ e = Some pc.

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

with contains_alt (σ : valuation) (S : symvars) : alt -> alt -> Prop :=
  | Cont_Alt : forall d xs eps epc,
      Forall (fun x => S x = false) xs ->
      contains σ S eps epc ->
      contains_alt σ S (Alt d xs eps) (Alt d xs epc)

with contains_env (σ : valuation) (S : symvars) : environment -> environment -> Prop :=
  | Cont_Env_Empty :
      contains_env σ S EmptyEnv EmptyEnv
  | Cont_Env_Extend : forall x Γs Γc es ec rest_s rest_c,
      S x = false ->
      contains_env σ S Γs Γc ->
      contains σ S es ec ->
      concore_expr ec ->
      contains_env σ S rest_s rest_c ->
      contains_env σ S (ExtendEnv x (MkClosure Γs es) rest_s)
                       (ExtendEnv x (MkClosure Γc ec) rest_c).

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
*)
Axiom eval_models_cond : forall Φ Γ S ec ec' σ,
  σ ⊨ Φ ->
  Φ ; Γ ⊢ ec ⇓ ec' -> models_cond σ S ec -> models_cond σ S ec'.

Axiom eval_models_not_cond : forall Φ Γ S ec ec' σ,
  σ ⊨ Φ ->
  Φ ; Γ ⊢ ec ⇓ ec' -> models_not_cond σ S ec -> models_not_cond σ S ec'.


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
  inversion Hcont; subst; [reflexivity |].
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
  inversion Hcont; subst; congruence.
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
  intros σ S l ec H. inversion H; subst; reflexivity.
Qed.

Lemma contains_con_inv : forall σ S d ec,
  contains σ S (ECon d) ec -> ec = ECon d.
Proof.
  intros σ S d ec H. inversion H; subst; reflexivity.
Qed.

Lemma contains_primop_inv : forall σ S p ec,
  contains σ S (EPrimOp p) ec -> ec = EPrimOp p.
Proof.
  intros σ S p ec H. inversion H; subst; reflexivity.
Qed.

Lemma contains_lam_inv : forall σ S x body ec,
  contains σ S (ELam x body) ec ->
  exists bodyc, ec = ELam x bodyc /\ S x = false /\ contains σ S body bodyc.
Proof.
  intros σ S x body ec H. inversion H; subst.
  exists bodyc. split; [reflexivity | split; assumption].
Qed.

Lemma contains_clos_inv : forall σ S Γs x body ec,
  contains σ S (EClos Γs x body) ec ->
  exists Γc bodyc, ec = EClos Γc x bodyc /\ S x = false /\
    contains_env σ S Γs Γc /\
    contains σ S body bodyc.
Proof.
  intros σ S Γs x body ec H. inversion H; subst.
  exists Γc, bodyc. split; [reflexivity | auto].
Qed.

Lemma contains_app_inv : forall σ S fs as_ ec,
  contains σ S (EApp fs as_) ec ->
  exists fc ac, ec = EApp fc ac /\ contains σ S fs fc /\ contains σ S as_ ac.
Proof.
  intros σ S fs as_ ec H. inversion H; subst.
  exists f_c, a_c. split; [reflexivity | auto].
Qed.

Lemma contains_cast_inv : forall σ S es γ ec,
  contains σ S (ECast es γ) ec ->
  exists ec', ec = ECast ec' γ /\ contains σ S es ec'.
Proof.
  intros σ S es γ ec H. inversion H; subst.
  exists ec0. split; [reflexivity | assumption].
Qed.

Lemma contains_case_inv : forall σ S ess altss ec,
  contains σ S (ECase ess altss) ec ->
  exists esc altsc, ec = ECase esc altsc /\ contains σ S ess esc
    /\ Forall2 (contains_alt σ S) altss altsc.
Proof.
  intros σ S ess altss ec H. inversion H; subst.
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
  apply contains_app_inv in Hcont as [fc [ac [Heq [Hcont_f Hcont_a]]]]; subst e_con.
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
  eval pc_true Γ (ELit l) v -> v = ELit l.
Proof.
  intros Γ l v Heval.
  inversion Heval; subst.
  - reflexivity.
  - rewrite sat_pc_true in H. discriminate.
Qed.

Lemma eval_con_con : forall Γ d v,
  eval pc_true Γ (ECon d) v -> v = ECon d.
Proof.
  intros Γ d v Heval.
  inversion Heval; subst.
  - reflexivity.
  - rewrite sat_pc_true in H. discriminate.
Qed.

Lemma eval_bot_con : forall Γ b v,
  eval pc_true Γ (EBot b) v -> v = EBot b.
Proof.
  intros Γ b v Heval.
  inversion Heval; subst.
  - reflexivity.
  - rewrite sat_pc_true in H. discriminate.
Qed.

Lemma eval_clos_false : forall Γ env x body v,
  eval pc_true Γ (EClos env x body) v -> False.
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
  eval pc_true Γ (EVar x) v -> Whnf Γ (EVar x) -> v = EVar x.
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
  eval pc_true Γ (EPrimOp p) v -> False.
Proof.
  intros Γ p v Heval.
  inversion Heval; subst.
  rewrite sat_pc_true in H. discriminate.
Qed.

Lemma eval_coercion_con : forall Γ γ v,
  eval pc_true Γ (ECoercion γ) v -> v = ECoercion (subst_coerc Γ γ).
Proof.
  intros Γ γ v Heval.
  inversion Heval; subst.
  - reflexivity.
  - rewrite sat_pc_true in H. discriminate.
Qed.

Lemma eval_type_con : forall Γ τ v,
  eval pc_true Γ (EType τ) v -> v = EType (subst_type Γ τ).
Proof.
  intros Γ τ v Heval.
  inversion Heval; subst.
  - rewrite sat_pc_true in H. discriminate.
  - reflexivity.
Qed.

Lemma eval_app_coercion_false : forall Γ γ a v,
  eval pc_true Γ (EApp (ECoercion γ) a) v -> False.
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
  eval pc_true Γ (EApp (EType τ) a) v -> False.
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
  eval pc_true Γ (EApp (ELit l) a) v -> False.
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
  eval pc_true Γ (EApp (ECon d) a) v -> False.
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

Lemma eval_con_app_whnf : forall Γc fc ac v_f v_con,
  concore_expr fc ->
  Whnf Γc fc ->
  is_op_app fc = false ->
  pc_true ; Γc ⊢ fc ⇓ v_f ->
  pc_true ; Γc ⊢ EApp v_f ac ⇓ v_con ->
  pc_true ; Γc ⊢ EApp fc ac ⇓ v_con.
Proof.
  intros Γc fc ac v_f v_con Hcon Hwhnf Hnop Heval_f Heval_app.
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
  - inversion Heval_f; subst.
    + eapply cast_expr_eval_app; eassumption.
    + rewrite sat_pc_true in H. discriminate.
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
  eval Φ Γ (EApp f a) v ->
  exists p args', v = reduce_prim p args' /\ Forall (Solvable Γ) args'.
Proof.
  intros Φ Γ f a v Hsat Hwhnf Hop Heval.
  assert (Hsolv : Solvable Γ (EApp f a)) by (apply whnf_op_app_solvable; assumption).
  inversion Heval; subst.
  - simpl in Hop. discriminate.
  - (* Eval_AppSpine *)
    inversion Hwhnf; subst; try discriminate.
    inversion H; subst; try discriminate.
    apply Whnf_Solvable in H5.
    contradiction.
  - (* Eval_AppPrim *)
    exists p, args'. split; [reflexivity |].
    assert (Hsargs : Forall (Solvable Γ) args)
      by (eapply solvable_spine_args; [exact Hsolv | constructor | eassumption]).
    match goal with
    | [ HF : Forall2 (eval Φ Γ) args args' |- _ ] =>
        clear -HF Hsargs Hsat;
        induction HF as [| a0 a0' tl tl' Ha Htl IH];
        [ constructor
        | inversion Hsargs as [| b0 btl Hsa Hstl]; subst;
          constructor;
          [ exact (solvable_eval_solvable Φ Γ a0 a0' Ha Hsat Hsa)
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
  intros Φ Γs Γc σ S ef ea ef' er e_con Hmod Henv Hcont Hcon Hnotwhnf Heval1 Heval2 IH1 IH2.
  apply contains_app_inv in Hcont as [fc [ac [Heq [Hcont_f Hcont_a]]]]; subst e_con.
  inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | ]; subst.
  destruct (IH1 Γc σ fc Hmod Henv Hcont_f Hf) as [v_f [Heval_f Hcont_vf]].
  assert (Henv_c : concrete_env Γc) by (eapply contains_env_concrete; eassumption).
  assert (Hcon_vf : concore_expr v_f) by (eapply concore_eval_closed; [exact Henv_c | exact Hf | exact Heval_f]).
  assert (Hcont_app2 : contains σ S (EApp ef' ea) (EApp v_f ac)) by (constructor; assumption).
  assert (Hcon_app2 : concore_expr (EApp v_f ac)) by (apply Con_App; assumption).
  destruct (IH2 Γc σ (EApp v_f ac) Hmod Henv Hcont_app2 Hcon_app2) as [v_con [Heval_app2 Hcont_er]].
  exists v_con. split; [| exact Hcont_er].
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
  - eapply Eval_AppSpine; [exact Hnot_whnf_c | exact Heval_f | exact Heval_app2].
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
  needs soundness for every argument in its Forall2 (eval Φ Γ) args args',
  and Eval_Case/FoldAlts_Con need it for the nested eval buried inside
  fold_alts - neither is covered by Coq's auto-derived induction principle
  for a mutually-recursive family, which only strengthens direct recursive
  occurrences, not ones nested inside a Forall2 or the sibling relation.
  Recursing through those manually (via `induction` on the embedded Forall2
  / fold_alts proof, calling back into the very fixpoint being defined) is
  what used to be papered over by the eval_prim_args_sound and
  fold_alts_contains axioms.
*)

(** `contains` commutes with `unspool_app`, threading an existing pointwise
    correspondence on the accumulator through the same accumulator on both
    sides. This is what earlier let eval_app_spine_sound derive an arity
    contradiction, and is the structural core of eval_prim_args_sound. *)
Lemma contains_unspool_primop : forall σ S e_sym e_con,
  contains σ S e_sym e_con ->
  forall L_s L_c,
    Forall2 (contains σ S) L_s L_c ->
    forall p args,
      unspool_app e_sym L_s = (EPrimOp p, args) ->
      exists args_c,
        unspool_app e_con L_c = (EPrimOp p, args_c) /\
        Forall2 (contains σ S) args args_c.
Proof.
  induction 1; intros L_s L_c HL p0 args0 Hunspool; simpl in Hunspool;
    try discriminate.
  - injection Hunspool as ? ?; subst.
    exists L_c. split; [reflexivity | exact HL].
  - apply IHcontains1 with (L_s := a_s :: L_s) (L_c := a_c :: L_c).
    + constructor; assumption.
    + exact Hunspool.
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
    forall head args,
      unspool_app e_sym L_s = (head, args) ->
      is_if head = false ->
      exists head_c args_c,
        unspool_app e_con L_c = (head_c, args_c) /\
        contains σ S head head_c /\
        Forall2 (contains σ S) args args_c.
Proof.
  induction 1; intros L_s L_c HL head args Hunspool Hif; simpl in Hunspool;
    try (injection Hunspool as ? ?; subst;
         eexists; exists L_c;
         split; [reflexivity | split; [solve [constructor; assumption] | exact HL]]).
  - (* Cont_App *)
    apply IHcontains1 with (L_s := a_s :: L_s) (L_c := a_c :: L_c).
    + constructor; assumption.
    + exact Hunspool.
    + exact Hif.
  - (* Cont_If_True *) injection Hunspool as ? ?; subst. simpl in Hif. discriminate.
  - (* Cont_If_False *) injection Hunspool as ? ?; subst. simpl in Hif. discriminate.
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

Fixpoint concore_soundness_fix (Φ : path_condition) (Γs : environment) (e_sym v_sym : expr)
  (Heval : Φ ; Γs ⊢ e_sym ⇓ v_sym) {struct Heval} :
  forall Γc σ S e_con,
    σ ⊨ Φ ->
    contains_env σ S Γs Γc ->
    contains σ S e_sym e_con ->
    concore_expr e_con ->
    exists v_con,
      Γc ⊢ᶜ e_con ⇓ᶜ v_con /\
      contains σ S v_sym v_con
with concore_soundness_fold_fix (Φ : path_condition) (Γs : environment) (escrut : expr) (alts : list alt) (er : expr)
  (Hfold : fold_alts Φ Γs escrut alts er) {struct Hfold} :
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
    [ Φ Γ x Γ' e e' Hlookup Heval_x
    | Φ Γ x Hnone
    | Φ Γ l
    | Φ Γ d
    | Φ Γ e γ e' Heval_e
    | Φ Γ Γ' x eb ea eb' Heval_b
    | Φ Γ ef ea ef' er Hnotwhnf Heval_f Heval_app2
    | Φ Γ b
    | Φ Γ ef ea p args args' Hunspool Harity Hargs
    | Φ Γ x e
    | Φ Γ ef γ ea γ_a γ_r er Hdecomp Heval_pushed
    | Φ Γ b ea
    | Φ Γ es alts es' er Heval_es Hfold
    | Φ Γ ec et ef ec' et' ef' pc_c Heval_c Hpc Heval_t Heval_f
    | Φ Γ γ
    | Φ Γ e Hunsat
    | Φ Γ τ
    ]; intros Γc σ S e_con Hmod Henv Hcont Hcon.
  - (* Eval_Var *)
    assert (Hfree : sym_free_env S Γ)
      by (destruct (contains_env_sym_free σ S Γ Γc Henv) as [Hf _]; exact Hf).
    assert (Heq : e_con = EVar x) by (eapply contains_var_bound; eassumption).
    subst e_con.
    destruct (contains_lookup_env σ S Γ Γc x Γ' e Henv Hlookup) as [Γ'c [ec [Hlookc [Henv' Hcont']]]].
    assert (Hcon' : concore_expr ec) by (apply (lookup_env_concore σ S Γ Γc x Γ' e Γ'c ec Henv Hlookup Hlookc)).
    destruct (concore_soundness_fix Φ Γ' e e' Heval_x Γ'c σ S ec Hmod Henv' Hcont' Hcon') as [v_con [Hevalc Hcont_v]].
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
      { inversion Hcont; subst; congruence. }
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
    destruct (concore_soundness_fix Φ Γ e e' Heval_e Γc σ S ec Hmod Henv Hcont_e Hcon_e) as [vc [Hevalc Hcont_v]].
    exists (cast_expr vc γ). split; [unfold eval_con; apply Eval_Cast; exact Hevalc | apply cast_expr_contains; exact Hcont_v].
  - (* Eval_AppAbs *)
    apply contains_app_inv in Hcont as [fc [ac [Heq [Hcont_f Hcont_a]]]]; subst.
    apply contains_clos_inv in Hcont_f as [Γ'c [ebc [Heq_f [Hsx [Henv_clos Hcont_b]]]]]; subst.
    inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | ]; subst.
    inversion Hf as [| | | | | | Γ0 x0 body Henv_clos_c Hcon_b | | | | | | | ]; subst.
    assert (Henv_ext : contains_env σ S (ExtendEnv x (MkClosure Γ ea) Γ') (ExtendEnv x (MkClosure Γc ac) Γ'c)).
    { apply Cont_Env_Extend; assumption. }
    destruct (concore_soundness_fix Φ (extend_env Γ' x Γ ea) eb eb' Heval_b
                (ExtendEnv x (MkClosure Γc ac) Γ'c) σ S ebc Hmod Henv_ext Hcont_b Hcon_b)
      as [v_con [Heval_b' Hcont_v]].
    exists v_con. split; [| exact Hcont_v].
    unfold eval_con. apply Eval_AppAbs. exact Heval_b'.
  - (* Eval_AppSpine *)
    eapply eval_app_spine_sound; try eassumption.
    + intros Γc0 σ0 e_con0 Hmod0 Henv0 Hcont0 Hcon0.
      exact (concore_soundness_fix Φ Γ ef ef' Heval_f Γc0 σ0 S e_con0 Hmod0 Henv0 Hcont0 Hcon0).
    + intros Γc0 σ0 e_con0 Hmod0 Henv0 Hcont0 Hcon0.
      exact (concore_soundness_fix Φ Γ (EApp ef' ea) er Heval_app2 Γc0 σ0 S e_con0 Hmod0 Henv0 Hcont0 Hcon0).
  - (* Eval_Bot *)
    inversion Hcont; subst.
    exists (EBot b). split; [apply Eval_Bot | apply Cont_Bot].
  - (* Eval_AppPrim *)
    apply contains_app_inv in Hcont as [fc [ac [Heq [Hcont_f Hcont_a]]]]; subst e_con.
    assert (Hcont_full : contains σ S (EApp ef ea) (EApp fc ac)) by (constructor; assumption).
    inversion Hcon as [| | | | fc0 ac0 Hcon_f Hcon_a | | | | | | | | | ]; subst.
    assert (Hunspool_c : exists args_c, unspool_app (EApp fc ac) [] = (EPrimOp p, args_c) /\ Forall2 (contains σ S) args args_c).
    { apply (contains_unspool_primop σ S (EApp ef ea) (EApp fc ac) Hcont_full [] [] (Forall2_nil _) p args Hunspool). }
    destruct Hunspool_c as [args_c [Hunspool_c Hcont_args]].
    assert (Hconcore_args_c : Forall concore_expr args_c).
    { eapply unspool_app_concore; [exact Hunspool_c | constructor; assumption | constructor]. }
    assert (Hstep : exists args_c', Forall2 (eval pc_true Γc) args_c args_c' /\ Forall2 (contains σ S) args' args_c').
    { clear Hunspool Harity Hunspool_c Hcont_full.
      revert args_c Hcont_args Hconcore_args_c.
      induction Hargs as [| a a' args_tl args'_tl Ha Hargs_tl IHargs];
        intros args_c Hcont_args Hconcore_args_c.
      - inversion Hcont_args; subst.
        exists []. split; constructor.
      - inversion Hcont_args as [| a0 ac1 args_tl0 args_c_tl Hcont_a1 Hcont_tl Heqa Heqargs]; subst.
        inversion Hconcore_args_c as [| ac2 args_c_tl2 Hcon_a1 Hcon_tl]; subst.
        destruct (concore_soundness_fix Φ Γ a a' Ha Γc σ S ac1 Hmod Henv Hcont_a1 Hcon_a1)
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
    exact (concore_soundness_fix Φ Γ (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r) er Heval_pushed Γc0 σ0 S e_con0 Hmod0 Henv0 Hcont0 Hcon0).
  - (* Eval_AppBot *)
    apply contains_app_inv in Hcont as [fc [ac [Heq [Hcont_f Hcont_a]]]]; subst.
    inversion Hcont_f; subst.
    exists (EBot b). split; [apply Eval_AppBot | constructor].
  - (* Eval_Case *)
    apply contains_case_inv in Hcont as [esc [altsc [Heq [Hcont_es Hcont_alts]]]]; subst.
    inversion Hcon as [| | | | | | | es0 alts0 Hcon_es Hcon_alts | | | | | | ]; subst.
    destruct (concore_soundness_fix Φ Γ es es' Heval_es Γc σ S esc Hmod Henv Hcont_es Hcon_es) as [vc_s [Heval_esc Hcont_vs]].
    assert (Hcont_merge : contains σ S (merge es') vc_s) by (apply merge_contains; exact Hcont_vs).
    destruct (concore_soundness_fold_fix Φ Γ (merge es') alts er Hfold Γc σ S esc altsc Hmod Henv Hcon_es Hcon_alts
                (ex_intro _ vc_s (conj Heval_esc Hcont_merge)) Hcont_alts) as [v_con [Heval_case Hcont_er]].
    exists v_con. split; assumption.
  - (* Eval_If *)
    inversion Hcont; subst.
    + assert (Hcond' : models_cond σ S ec')
        by (apply eval_models_cond with (Φ:=Φ)(Γ:=Γ)(ec:=ec); assumption).
      assert (Hpc_mod : σ ⊨ pc_c) by (apply (models_cond_pc σ S Γ ec' pc_c Hpc); exact Hcond').
      assert (Hmod_and : σ ⊨ (Φ ∧ pc_c)) by (apply models_and; assumption).
      destruct (concore_soundness_fix (Φ ∧ pc_c) Γ et et' Heval_t Γc σ S e_con Hmod_and Henv H4 Hcon) as [v_con [Hevalc' Hcont_v]].
      exists v_con. split; [exact Hevalc' |]. apply Cont_If_True; [exact Hcond' | exact Hcont_v].
    + assert (Hncond' : models_not_cond σ S ec')
        by (apply eval_models_not_cond with (Φ:=Φ)(Γ:=Γ)(ec:=ec); assumption).
      assert (Hpc_mod : σ ⊨ (¬ pc_c)) by (apply (models_not_cond_pc σ S Γ ec' pc_c Hpc); exact Hncond').
      assert (Hmod_and : σ ⊨ (Φ ∧ ¬ pc_c)) by (apply models_and; assumption).
      destruct (concore_soundness_fix (Φ ∧ ¬ pc_c) Γ ef ef' Heval_f Γc σ S e_con Hmod_and Henv H4 Hcon) as [v_con [Hevalc' Hcont_v]].
      exists v_con. split; [exact Hevalc' |]. apply Cont_If_False; [exact Hncond' | exact Hcont_v].
  - (* Eval_Coercion *)
    inversion Hcont; subst.
    exists (ECoercion (subst_coerc Γc γ)).
    split; [apply Eval_Coercion | apply subst_coerc_contains_env; assumption].
  - (* Eval_Prune *)
    apply models_sat in Hmod. rewrite Hunsat in Hmod. discriminate.
  - (* Eval_Type *)
    inversion Hcont; subst.
    exists (EType (subst_type Γc τ)).
    split; [apply Eval_Type | apply subst_type_contains_env; assumption].
}
{
  destruct Hfold as
    [ Φ Γ ec et ef alts et' ef' pc_c Hpc Hfold_t Hfold_f
    | Φ Γ ec et ef alts Hpc_none
    | Φ Γ e d ea xs ep alts er Hdec Halt Heval_ep
    | Φ Γ b alts
    | Φ Γ e alts Hnotif Hnoalt Hnotbot
    ]; intros Γc σ S esc altsc Hmod Henv Hcon_esc Hcon_altsc Hvc Halts.
  - (* FoldAlts_If *)
    destruct Hvc as [vc_s [Heval_esc Hcont_vs]].
    inversion Hcont_vs; subst.
    + assert (Hpc_mod : σ ⊨ pc_c) by (apply (models_cond_pc σ S Γ ec pc_c Hpc); assumption).
      assert (Hmod_and : σ ⊨ (Φ ∧ pc_c)) by (apply models_and; assumption).
      destruct (concore_soundness_fold_fix (Φ ∧ pc_c) Γ et alts et' Hfold_t Γc σ S esc altsc Hmod_and Henv Hcon_esc Hcon_altsc
                  (ex_intro _ vc_s (conj Heval_esc H4)) Halts) as [v_con [Heval_case Hcont_er]].
      exists v_con. split; [exact Heval_case | apply Cont_If_True; assumption].
    + assert (Hpc_mod : σ ⊨ (¬ pc_c)) by (apply (models_not_cond_pc σ S Γ ec pc_c Hpc); assumption).
      assert (Hmod_and : σ ⊨ (Φ ∧ ¬ pc_c)) by (apply models_and; assumption).
      destruct (concore_soundness_fold_fix (Φ ∧ ¬ pc_c) Γ ef alts ef' Hfold_f Γc σ S esc altsc Hmod_and Henv Hcon_esc Hcon_altsc
                  (ex_intro _ vc_s (conj Heval_esc H4)) Halts) as [v_con [Heval_case Hcont_er]].
      exists v_con. split; [exact Heval_case | apply Cont_If_False; assumption].
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
    destruct (concore_soundness_fix Φ (extend_env_multi Γ xs ea Γ) ep er Heval_ep
                (extend_env_multi Γc xs ea_c Γc) σ S ep_c Hmod Henv_ext Hcont_ep Hcon_ep_c)
      as [v_con [Heval_ep_c Hcont_er]].
    exists v_con. split; [| exact Hcont_er].
    unfold eval_con. eapply Eval_Case.
    + exact Heval_esc.
    + apply merge_fold_alts_equiv.
      eapply FoldAlts_Con; [exact Hdec_vcs | exact Halt_c | exact Heval_ep_c].
  - (* FoldAlts_Bot *)
    destruct Hvc as [vc_s [Heval_esc Hcont_vs]].
    inversion Hcont_vs; subst.
    exists (EBot b). split; [| apply Cont_Bot].
    unfold eval_con. eapply Eval_Case.
    + exact Heval_esc.
    + apply merge_fold_alts_equiv. apply FoldAlts_Bot.
  - (* FoldAlts_Otherwise *)
    destruct Hvc as [vc_s [Heval_esc Hcont_vs]].
    assert (Hrec : fold_alts Φ Γ e alts (EBot BUndefined)) by (eapply FoldAlts_Otherwise; eassumption).
    assert (Hno_nested := fold_alts_no_nested_if Φ Γ e alts (EBot BUndefined) Hrec).
    destruct (unspool_app e []) as [head args] eqn:Hunspool_e.
    assert (Hif_head : is_if head = false).
    { destruct (is_if head) eqn:Hcase; [| reflexivity].
      specialize (Hno_nested head args eq_refl Hcase). subst head.
      rewrite Hnotif in Hcase. discriminate. }
    destruct (contains_unspool_general σ S e vc_s Hcont_vs [] [] (Forall2_nil _) head args Hunspool_e Hif_head)
      as [head_c [args_c [Hunspool_vcs [Hcont_head Hcont_args]]]].
    assert (Hnoalt_c : match decompose_con_app vc_s with Some (d,_) => find_alt d altsc = None | None => True end).
    { unfold decompose_con_app. rewrite Hunspool_vcs.
      destruct head_c eqn:Hheadc; try exact I.
      inversion Hcont_head; subst; try (simpl in Hif_head; discriminate).
      assert (Hdeco_e : decompose_con_app e = Some (d, args)) by (unfold decompose_con_app; rewrite Hunspool_e; reflexivity).
      rewrite Hdeco_e in Hnoalt.
      exact (find_alt_none_contains_alt σ S alts altsc d Halts Hnoalt).
    }
    assert (Hnotbot_c : is_bot vc_s = false).
    { destruct (is_bot vc_s) eqn:Hbc; [| reflexivity].
      exfalso.
      destruct vc_s; simpl in Hbc; try discriminate.
      inversion Hcont_vs; subst; discriminate.
    }
    assert (Hnotif_c : is_if vc_s = false).
    { destruct (is_if vc_s) eqn:Hic; [| reflexivity].
      exfalso.
      destruct vc_s; simpl in Hic; try discriminate.
      inversion Hcont_vs; subst; discriminate.
    }
    exists (EBot BUndefined). split; [| apply Cont_Bot].
    unfold eval_con. eapply Eval_Case.
    + exact Heval_esc.
    + apply merge_fold_alts_equiv.
      apply FoldAlts_Otherwise; assumption.
}
Qed.

(**
  NOT DONE: determinism (the "exists v_con" weakness).

  The conclusion is still existential. Strengthening it to
    forall v_con, Γc ⊢ᶜ e_con ⇓ᶜ v_con -> contains σ S v_sym v_con
  needs concrete evaluation to be deterministic, and eval is NOT proved
  deterministic here - SymCore.v only has fold_alts_deterministic_given_eval,
  which ASSUMES it. Determinism is not obviously true either: Rule App-Spine
  and Rule App-Prim can both apply to the same application (App-Spine only
  requires the head not to be in WHNF, which does not exclude a spine whose
  head is a partially applied operator), so a determinism proof would first
  need those two rules to be made disjoint. That is a change to the operational
  semantics, not to this file, and it is left undone.
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
  exact (concore_soundness_fix Φ Γs e_sym v_sym Heval Γc σ S e_con Hmod Henv Hcont Hcon).
Qed.


(** Top-level Soundness for whole programs starting from EmptyEnv *)
Theorem concore_soundness_top : forall Φ σ S e_sym e_con v_sym,
  σ ⊨ Φ ->
  contains σ S e_sym e_con ->
  concore_expr e_con ->
  Φ ; EmptyEnv ⊢ e_sym ⇓ v_sym ->
  exists v_con,
    ⊢ᶜ e_con ⇓ᶜ v_con /\
    contains σ S v_sym v_con.
Proof.
  intros Φ σ S e_sym e_con v_sym Hmod Hcont Hcon Heval.
  apply (concore_soundness Φ EmptyEnv EmptyEnv σ S e_sym e_con v_sym); auto.
  apply Cont_Env_Empty.
Qed.


(** ========================================================================= *)
(** 11. NonVacuity: what the repaired statement actually says                 *)
(** ========================================================================= *)

(**
  Four facts that the pre-repair development could not prove, and in three
  cases actively refuted (see scratch/Audit.v, scratch/prim.v,
  scratch/prim2.v):

  (a) a free symbolic variable is genuinely instantiated to its value under
      the model, and the soundness theorem has real instances that use it;
  (b) a branch whose condition mentions a free symbolic variable DOES have a
      concretion - the exact negation of soundness_vacuous_on_symbolic_branch;
  (c) Rule Prune no longer kills every branch;
  (d) reduce_prim is not forced to be a constant function on literals, and
      the collapse is attributable exactly to the axiom that was weakened.

  No new axiom is introduced by any of this.
*)

Section NonVacuity.

Definition only (x : var) : symvars := fun y => if string_dec y x then true else false.

Lemma only_self : forall x, only x x = true.
Proof. intros x. unfold only. destruct (string_dec x x); congruence. Qed.

(* ================= (a) symbolic variables are instantiated ============== *)

Theorem symvar_instantiated : forall σ x,
  contains σ (only x) (EVar x) (ELit (σ x)).
Proof. intros. apply Cont_Var_Sym. apply only_self. Qed.

Theorem symvar_instantiated_uniquely : forall σ S x ec,
  S x = true -> contains σ S (EVar x) ec -> ec = ELit (σ x).
Proof. intros. eapply contains_var_sym; eassumption. Qed.

Theorem soundness_applies_to_symvar : forall σ S x,
  σ ⊨ pc_true -> S x = true ->
  exists v_con, EmptyEnv ⊢ᶜ ELit (σ x) ⇓ᶜ v_con /\ contains σ S (EVar x) v_con.
Proof.
  intros σ S x Hmod Hx.
  apply (concore_soundness pc_true EmptyEnv EmptyEnv σ S (EVar x) (ELit (σ x)) (EVar x)).
  - exact Hmod.
  - apply Cont_Env_Empty.
  - apply Cont_Var_Sym. exact Hx.
  - apply Con_Lit.
  - apply Eval_SymVar. reflexivity.
Qed.

Definition symprim (p : primop) (a : expr) (l : lit) : expr :=
  EApp (EApp (EPrimOp p) a) (ELit l).

Theorem soundness_on_symbolic_primop : forall σ S p x l,
  σ ⊨ pc_true -> S x = true -> primop_arity p = 2%nat ->
  exists v_con,
    eval_con EmptyEnv (symprim p (ELit (σ x)) l) v_con /\
    contains σ S (reduce_prim p (EVar x :: ELit l :: nil)) v_con.
Proof.
  intros σ S p x l Hmod Hx Har.
  apply (concore_soundness pc_true EmptyEnv EmptyEnv σ S
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

Theorem symbolic_branch_has_concretion : forall σ S p x l lt lf,
  σ ⊨ (PCPrim p (PCVar x :: PCLit l :: nil)) ->
  contains σ S (EIf (symcond p x l) (ELit lt) (ELit lf)) (ELit lt).
Proof.
  intros σ S p x l lt lf Hmod.
  apply Cont_If_True; [| apply Cont_Lit].
  apply (models_cond_pc σ S EmptyEnv (symcond p x l) (PCPrim p (PCVar x :: PCLit l :: nil))).
  - apply symcond_is_formula. reflexivity.
  - exact Hmod.
Qed.

(** The exact negation of scratch/Audit.v's soundness_vacuous_on_symbolic_branch,
    modulo the one premise that cannot be dispensed with: that the SMT theory
    is non-degenerate, i.e. some model satisfies some atom. The audit theorem
    needed no such premise because it refuted the condition for EVERY model. *)
Theorem soundness_not_vacuous_on_symbolic_branch :
  (exists σ p x l, σ ⊨ (PCPrim p (PCVar x :: PCLit l :: nil))) ->
  ~ (forall σ S p x l et ef ec, ~ contains σ S (EIf (symcond p x l) et ef) ec).
Proof.
  intros [σ [p [x [l Hmod]]]] Hvac.
  apply (Hvac σ (only x) p x l (ELit l) (ELit l) (ELit l)).
  apply symbolic_branch_has_concretion. exact Hmod.
Qed.

Theorem symbolic_branch_condition_is_judgeable : forall σ S p x l,
  models_cond σ S (symcond p x l) <-> σ ⊨ (PCPrim p (PCVar x :: PCLit l :: nil)).
Proof.
  intros. apply (models_cond_pc σ S EmptyEnv).
  apply symcond_is_formula. reflexivity.
Qed.

(* ==================== (c) the Prune attack is dead ====================== *)

Theorem prune_attack_blocked : forall Φ σ,
  σ ⊨ Φ -> sat Φ = false -> False.
Proof.
  intros Φ σ Hmod Hunsat. apply models_sat in Hmod. congruence.
Qed.

Theorem prune_does_not_kill_branches :
  (exists Φ, sat Φ = false) ->
  forall σ S p x l lt lf,
    σ ⊨ (PCPrim p (PCVar x :: PCLit l :: nil)) ->
    contains σ S (EIf (symcond p x l) (ELit lt) (ELit lf)) (ELit lt).
Proof.
  intros _ σ S p x l lt lf Hmod. apply symbolic_branch_has_concretion. exact Hmod.
Qed.

(* ============ (d) reduce_prim is not forced to be constant ============== *)

Theorem contains_not_rigid_on_solvable : forall σ : valuation,
  ~ (forall S Γ es ec, Solvable Γ es -> contains σ S es ec -> es = ec).
Proof.
  intros σ Hrigid.
  specialize (Hrigid (only "x") EmptyEnv (EVar "x") (ELit (σ "x"))
                     (Solvable_Var EmptyEnv "x" eq_refl)
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
         specialize (Hall EmptyEnv); inversion Hall; fail).
  - (* Cont_Var_Sym *)
    exfalso.
    specialize (Hall (ExtendEnv x (MkClosure EmptyEnv (EBot BUndefined)) EmptyEnv)).
    inversion Hall as [| x0 Hnone | |]; subst.
    simpl in Hnone. destruct (string_dec x x); [discriminate | congruence].
  - (* Cont_App *)
    assert (Hf : forall Γ, Solvable Γ f_s)
      by (intros Γ; specialize (Hall Γ); inversion Hall; assumption).
    assert (Ha : forall Γ, Solvable Γ a_s)
      by (intros Γ; specialize (Hall Γ); inversion Hall; assumption).
    rewrite (IHcontains1 Hf), (IHcontains2 Ha). reflexivity.
Qed.

(** The collapse is attributable exactly to the UNCONDITIONAL form of
    reduce_prim_solvable, which this development no longer assumes. *)
Theorem unconditional_solvable_forces_constancy :
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

  Theorem distinct_images_survive_resolvable_conditions :
    forall σ S c,
      models_cond σ S c ->
      contains σ S (reduce_prim p [EIf c (ELit l1) (ELit l2)]) (reduce_prim p [ELit l1]).
  Proof.
    intros σ S c Hc. apply reduce_prim_contains. constructor; [| constructor].
    apply Cont_If_True; [exact Hc | apply Cont_Lit].
  Qed.

  Theorem old_axiom_refutes_distinct_images :
    (forall Γ q args, Solvable Γ (reduce_prim q args)) ->
    forall σ S σ' S' c, models_cond σ S c -> models_not_cond σ' S' c -> False.
  Proof.
    intros Hall σ S σ' S' c Ht Hf. apply Hdistinct.
    eapply unconditional_solvable_forces_constancy; eassumption.
  Qed.
End ReducePrimNotConstant.
End NonVacuity.
