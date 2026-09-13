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
  | Con_Clos : forall Γ x body, concore_expr body -> concore_expr (EClos Γ x body)
  | Con_Case : forall es alts, concore_expr es -> Forall concore_alt alts -> concore_expr (ECase es alts)
  | Con_Cast : forall e γ, concore_expr e -> concore_expr (ECast e γ)
  | Con_Coercion : forall γ, concore_expr (ECoercion γ)
  | Con_Type : forall τ, concore_expr (EType τ)
  | Con_Bot_Undefined : concore_expr (EBot BUndefined)
  | Con_Bot_Unreachable : concore_expr (EBot BUnreachable)
  | Con_Bot_Raise : forall e, concore_expr e -> concore_expr (EBot (BRaise e))

with concore_alt : alt -> Prop :=
  | Con_Alt : forall d xs ep, concore_expr ep -> concore_alt (Alt d xs ep).

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

(** An environment Γ is concrete if all expressions stored in its closures
    are themselves ConCore expressions *)
Inductive concrete_env : environment -> Prop :=
  | CEnv_Empty : concrete_env EmptyEnv
  | CEnv_Extend : forall x Γ' e rest,
      concore_expr e ->
      concrete_env Γ' ->
      concrete_env rest ->
      concrete_env (ExtendEnv x (MkClosure Γ' e) rest).

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
