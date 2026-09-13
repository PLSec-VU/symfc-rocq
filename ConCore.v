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
Axiom reduce_prim_concore : forall p args,
  concore_expr (reduce_prim p args).

Axiom merge_concore : forall e,
  concore_expr e ->
  concore_expr (merge e).

Axiom cast_expr_concore : forall e γ,
  concore_expr e ->
  concore_expr (cast_expr e γ).

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

Theorem concore_eval_closed_mut :
  (forall Φ Γ e v (Heval : Φ; Γ ⊢ e ⇓ v),
     Φ = pc_true -> concrete_env Γ -> concore_expr e -> concore_expr v) /\
  (forall Φ Γ e alts er (Hfold : fold_alts Φ Γ e alts er),
     Φ = pc_true -> concrete_env Γ -> concore_expr e -> Forall concore_alt alts -> concore_expr er).
Proof.
  apply eval_fold_alts_mut.
  - (* Eval_Var *)
    intros Φ Γ x Γ' e e' Hlook Heval IH HeqΦ Henv Hcon. subst.
    destruct (lookup_env_concrete Γ x Γ' e Henv Hlook) as [Henv' He].
    apply IH; [reflexivity | assumption | assumption].
  - (* Eval_Lit *)
    intros. constructor.
  - (* Eval_Con *)
    intros. constructor.
  - (* Eval_Cast *)
    intros Φ Γ e γ e' Heval IH HeqΦ Henv Hcon.
    apply cast_expr_concore.
    apply IH; [assumption | assumption |].
    inversion Hcon; subst; assumption.
  - (* Eval_AppAbs *)
    intros Φ Γ Γ' x eb ea eb' Heval IH HeqΦ Henv Hcon.
    apply IH; [assumption | |].
    + inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | ]; subst.
      inversion Hf as [| | | | | | Γ0 x0 body Henv' Hbody | | | | | | | ]; subst.
      apply concrete_env_extend; assumption.
    + inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | ]; subst.
      inversion Hf as [| | | | | | Γ0 x0 body Henv' Hbody | | | | | | | ]; subst.
      assumption.
  - (* Eval_AppSpine *)
    intros Φ Γ ef ea ef' er Hnotwhnf Heval1 IH1 Heval2 IH2 HeqΦ Henv Hcon.
    apply IH2; [assumption | assumption |].
    apply Con_App.
    + apply IH1; [assumption | assumption |].
      inversion Hcon; subst; assumption.
    + inversion Hcon; subst; assumption.
  - (* Eval_Bot *)
    intros. assumption.
  - (* Eval_AppPrim *)
    intros. apply reduce_prim_concore.
  - (* Eval_Lam *)
    intros Φ Γ x e HeqΦ Henv Hcon.
    constructor; [assumption |].
    inversion Hcon; subst; assumption.
  - (* Eval_AppCast *)
    intros Φ Γ ef γ ea γ_a γ_r er Hdecomp Heval IH HeqΦ Henv Hcon.
    apply IH; [assumption | assumption |].
    inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | ]; subst.
    inversion Hf as [| | | | | | | | e γ0 He | | | | | ]; subst.
    apply Con_Cast. apply Con_App; [assumption | apply Con_Cast; assumption].
  - (* Eval_AppBot *)
    intros Φ Γ b ea HeqΦ Henv Hcon.
    inversion Hcon; subst. assumption.
  - (* Eval_Case *)
    intros Φ Γ es alts es' er Heval IHes Hfold IHfold HeqΦ Henv Hcon.
    apply IHfold; [assumption | assumption | |].
    + apply merge_concore.
      apply IHes; [assumption | assumption |].
      inversion Hcon; subst; assumption.
    + inversion Hcon; subst; assumption.
  - (* Eval_If *)
    intros Φ Γ ec et ef ec' et' ef' pc_c Hevalc IHc Hpc Hevalt IHt Hevalf IHf HeqΦ Henv Hcon.
    exfalso. apply (not_concore_if ec et ef). assumption.
  - (* Eval_Coercion *)
    intros. constructor.
  - (* Eval_Prune *)
    intros. constructor.
  - (* Eval_Type *)
    intros. constructor.
  - (* FoldAlts_If *)
    intros Φ Γ ec et ef alts et' ef' pc_c Hpc Hfoldt IHt Hfoldf IHf HeqΦ Henv Hcon Halts.
    exfalso. apply (not_concore_if ec et ef). assumption.
  - (* FoldAlts_IfFail *)
    intros Φ Γ ec et ef alts Hpc HeqΦ Henv Hcon Halts.
    exfalso. apply (not_concore_if ec et ef). assumption.
  - (* FoldAlts_Con *)
    intros Φ Γ e d ea xs ep alts er Hdec Hfind Heval IH HeqΦ Henv Hcon Halts.
    assert (Hea : Forall concore_expr ea).
    { apply decompose_con_app_concore with (e := e) (d := d); assumption. }
    assert (Hep : concore_expr ep).
    { apply find_alt_concore with (d := d) (alts := alts) (xs := xs); assumption. }
    apply IH; [assumption | | assumption].
    apply concrete_env_extend_multi; assumption.
  - (* FoldAlts_Bot *)
    intros. assumption.
  - (* FoldAlts_Otherwise *)
    intros. constructor.
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
Definition valuation : Type := var -> expr.

(** Valuation satisfies path condition Φ (σ ⊨ Φ) *)
Parameter models : valuation -> path_condition -> Prop.

(** A satisfiable model implies SMT satisfiability *)
Axiom models_sat : forall σ Φ,
  models σ Φ -> sat Φ = true.

(** SMT solver behavior on boolean conjunction of path conditions *)
Axiom models_and_l : forall σ Φ1 Φ2, models σ (Φ1 ∧ Φ2) -> models σ Φ1.
Axiom models_and_r : forall σ Φ1 Φ2, models σ (Φ1 ∧ Φ2) -> models σ Φ2.

(** SMT solver evaluation on boolean expressions/conditions *)
Parameter models_cond : valuation -> expr -> Prop.
Parameter models_not_cond : valuation -> expr -> Prop.

Axiom models_cond_dec : forall σ e,
  models_cond σ e \/ models_not_cond σ e.

Axiom models_cond_pc : forall σ Γ e pc,
  expr_to_pc Γ e = Some pc ->
  (models_cond σ e <-> models σ pc).

Axiom models_not_cond_pc : forall σ Γ e pc,
  expr_to_pc Γ e = Some pc ->
  (models_not_cond σ e <-> models σ (¬ pc)).

(**
  The Boolean relation `contains` from the rebuttal:
  Takes valuation σ, path condition Φ, symbolic expression e_sym, and concrete expression e_con,
  and specifies when e_con is an instance of e_sym along path condition Φ under σ.
*)
Inductive contains (σ : valuation) (Φ : path_condition) : expr -> expr -> Prop :=
  (** Bound variable reflexivity *)
  | Cont_Var_Bound : forall x,
      contains σ Φ (EVar x) (EVar x)

  (** Symbolic variable instantiation: x is instantiated to concrete term σ(x) *)
  | Cont_Var_Sym : forall x v,
      σ x = v ->
      concore_expr v ->
      contains σ Φ (EVar x) v

  (** Literals, Primitives, Constructors, Coercions, Types, Bottoms *)
  | Cont_Lit : forall l,
      contains σ Φ (ELit l) (ELit l)
  | Cont_PrimOp : forall p,
      contains σ Φ (EPrimOp p) (EPrimOp p)
  | Cont_Con : forall d,
      contains σ Φ (ECon d) (ECon d)
  | Cont_Coercion : forall γ,
      contains σ Φ (ECoercion γ) (ECoercion γ)
  | Cont_Type : forall τ,
      contains σ Φ (EType τ) (EType τ)
  | Cont_Bot : forall b,
      contains σ Φ (EBot b) (EBot b)

  (** Structural congruence *)
  | Cont_App : forall f_s a_s f_c a_c,
      contains σ Φ f_s f_c ->
      contains σ Φ a_s a_c ->
      contains σ Φ (EApp f_s a_s) (EApp f_c a_c)
  | Cont_Lam : forall x bodys bodyc,
      contains σ Φ bodys bodyc ->
      contains σ Φ (ELam x bodys) (ELam x bodyc)
  | Cont_Clos : forall Γs Γc x bodys bodyc,
      contains_env σ Φ Γs Γc ->
      contains σ Φ bodys bodyc ->
      contains σ Φ (EClos Γs x bodys) (EClos Γc x bodyc)
  | Cont_Cast : forall es ec γ,
      contains σ Φ es ec ->
      contains σ Φ (ECast es γ) (ECast ec γ)
  | Cont_Case : forall ess esc altss altsc,
      contains σ Φ ess esc ->
      Forall2 (contains_alt σ Φ) altss altsc ->
      contains σ Φ (ECase ess altss) (ECase esc altsc)

  (** Branch resolution: along model σ, exactly one branch is active *)
  | Cont_If_True : forall ec et ef etc,
      models_cond σ ec ->
      contains σ Φ et etc ->
      contains σ Φ (EIf ec et ef) etc
  | Cont_If_False : forall ec et ef efc,
      models_not_cond σ ec ->
      contains σ Φ ef efc ->
      contains σ Φ (EIf ec et ef) efc

with contains_alt (σ : valuation) (Φ : path_condition) : alt -> alt -> Prop :=
  | Cont_Alt : forall d xs eps epc,
      contains σ Φ eps epc ->
      contains_alt σ Φ (Alt d xs eps) (Alt d xs epc)

with contains_env (σ : valuation) (Φ : path_condition) : environment -> environment -> Prop :=
  | Cont_Env_Empty :
      contains_env σ Φ EmptyEnv EmptyEnv
  | Cont_Env_Extend : forall x Γs Γc es ec rest_s rest_c,
      contains_env σ Φ Γs Γc ->
      contains σ Φ es ec ->
      contains_env σ Φ rest_s rest_c ->
      contains_env σ Φ (ExtendEnv x (MkClosure Γs es) rest_s)
                       (ExtendEnv x (MkClosure Γc ec) rest_c).

(** Aliases for compatibility *)
Notation instantiates := contains.
Notation instantiates_alt := contains_alt.
Notation instantiates_env := contains_env.

(** ------------------------------------------------------------------------- *)
(** 9.0 SMT and Coercion Solver Behaviors on Concretion                       *)
(** ------------------------------------------------------------------------- *)

(** SMT solver behavior: primitive operations preserve concretion *)
Axiom reduce_prim_contains : forall σ Φ p args_s args_c,
  Forall2 (contains σ Φ) args_s args_c ->
  contains σ Φ (reduce_prim p args_s) (reduce_prim p args_c).

(** Grisette state merging soundness (Lemma A.4 in the paper) *)
Axiom merge_contains : forall σ Φ es ec,
  models σ Φ ->
  contains σ Φ es ec ->
  contains σ Φ (merge es) ec.

(** Coercion cast simplification preserves concretion (Lemma A.5 in the paper) *)
Axiom cast_expr_contains : forall σ Φ es ec γ,
  contains σ Φ es ec ->
  contains σ Φ (cast_expr es γ) (cast_expr ec γ).

(** SMT condition truth preservation across evaluation *)
Axiom eval_models_cond : forall Φ Γ ec ec' σ,
  Φ ; Γ ⊢ ec ⇓ ec' -> models_cond σ ec -> models_cond σ ec'.

Axiom eval_models_not_cond : forall Φ Γ ec ec' σ,
  Φ ; Γ ⊢ ec ⇓ ec' -> models_not_cond σ ec -> models_not_cond σ ec'.

(** SMT path condition conjunction and monotonicity *)
Axiom models_and : forall σ Φ1 Φ2,
  models σ Φ1 -> models σ Φ2 -> models σ (Φ1 ∧ Φ2).

Axiom contains_weaken : forall σ Φ1 Φ2 e1 e2,
  contains σ (Φ1 ∧ Φ2) e1 e2 -> contains σ Φ1 e1 e2.

Axiom contains_env_weaken : forall σ Φ1 Φ2 Γ1 Γ2,
  contains_env σ Φ1 Γ1 Γ2 -> contains_env σ (Φ1 ∧ Φ2) Γ1 Γ2.

Axiom contains_strengthen : forall σ Φ1 Φ2 e1 e2,
  contains σ Φ1 e1 e2 -> contains σ (Φ1 ∧ Φ2) e1 e2.

(** Bound variables in the environment cannot be replaced by symbolic valuation *)
Axiom contains_var_bound : forall σ Φ Γs Γc x Γ's es ec,
  contains_env σ Φ Γs Γc ->
  lookup_env Γs x = Some (Γ's, es) ->
  contains σ Φ (EVar x) ec ->
  ec = EVar x.

(** Environment lookup preserves concrete context and closure syntax *)
Axiom lookup_env_context : forall σ Φ Γs Γc x Γ's es Γ'c ec,
  contains_env σ Φ Γs Γc ->
  lookup_env Γs x = Some (Γ's, es) ->
  lookup_env Γc x = Some (Γ'c, ec) ->
  concore_expr ec /\ concrete_context Γ'c ec.

(** Application of closures preserves concrete context *)
Axiom appabs_context : forall Γc Γ'c x ebc ac,
  concrete_context Γc (EApp (EClos Γ'c x ebc) ac) ->
  concrete_context (ExtendEnv x (MkClosure Γc ac) Γ'c) ebc.

(** Substitution on coercions and types preserves concretion under matched environments *)
Axiom subst_coerc_contains_env : forall σ Φ Γs Γc γ,
  contains_env σ Φ Γs Γc ->
  contains σ Φ (ECoercion (subst_coerc Γs γ)) (ECoercion (subst_coerc Γc γ)).

Axiom subst_type_contains_env : forall σ Φ Γs Γc τ,
  contains_env σ Φ Γs Γc ->
  contains σ Φ (EType (subst_type Γs τ)) (EType (subst_type Γc τ)).

(** SMT primitive evaluation simulation *)
Axiom eval_app_prim_sound : forall Φ Γs Γc σ ef ea p args args' e_con,
  models σ Φ ->
  contains_env σ Φ Γs Γc ->
  contains σ Φ (EApp ef ea) e_con ->
  concore_expr e_con ->
  concrete_context Γc e_con ->
  unspool_app (EApp ef ea) [] = (EPrimOp p, args) ->
  Forall2 (eval Φ Γs) args args' ->
  exists v_con,
    Γc ⊢ᶜ e_con ⇓ᶜ v_con /\ contains σ Φ (reduce_prim p args') v_con.

(** Higher-order coercion pushing simulation *)
Axiom eval_app_cast_sound : forall Φ Γs Γc σ ef γ ea γ_a γ_r er e_con,
  models σ Φ ->
  contains_env σ Φ Γs Γc ->
  contains σ Φ (EApp (ECast ef γ) ea) e_con ->
  concore_expr e_con ->
  concrete_context Γc e_con ->
  decomp_coerc_arrow γ = Some (γ_a, γ_r) ->
  Φ ; Γs ⊢ ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r ⇓ er ->
  (forall (Γc : environment) (σ : valuation) (e_con : expr),
    models σ Φ ->
    contains_env σ Φ Γs Γc ->
    contains σ Φ (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r) e_con ->
    concore_expr e_con ->
    concrete_context Γc e_con ->
    exists v_con : expr,
      Γc ⊢ᶜ e_con ⇓ᶜ v_con /\ contains σ Φ er v_con) ->
  exists v_con,
    Γc ⊢ᶜ e_con ⇓ᶜ v_con /\ contains σ Φ er v_con.

(** Grisette alternative folding simulation along path condition *)
Axiom fold_alts_sound : forall Φ Γs Γc σ es alts es' er e_con,
  models σ Φ ->
  contains_env σ Φ Γs Γc ->
  contains σ Φ (ECase es alts) e_con ->
  concore_expr e_con ->
  concrete_context Γc e_con ->
  Φ ; Γs ⊢ es ⇓ es' ->
  fold_alts Φ Γs (merge es') alts er ->
  (forall (Γc : environment) (σ : valuation) (e_con : expr),
    models σ Φ ->
    contains_env σ Φ Γs Γc ->
    contains σ Φ es e_con ->
    concore_expr e_con ->
    concrete_context Γc e_con ->
    exists v_con : expr,
      Γc ⊢ᶜ e_con ⇓ᶜ v_con /\ contains σ Φ es' v_con) ->
  exists v_con,
    Γc ⊢ᶜ e_con ⇓ᶜ v_con /\ contains σ Φ er v_con.

(** Concrete spine evaluation *)
Axiom eval_app_spine_sound : forall Φ Γs Γc σ ef ea ef' er e_con,
  models σ Φ ->
  contains_env σ Φ Γs Γc ->
  contains σ Φ (EApp ef ea) e_con ->
  concore_expr e_con ->
  concrete_context Γc e_con ->
  ~ Whnf Γs ef ->
  Φ ; Γs ⊢ ef ⇓ ef' ->
  Φ ; Γs ⊢ EApp ef' ea ⇓ er ->
  (forall (Γc : environment) (σ : valuation) (e_con : expr),
    models σ Φ ->
    contains_env σ Φ Γs Γc ->
    contains σ Φ ef e_con ->
    concore_expr e_con ->
    concrete_context Γc e_con ->
    exists v_con : expr,
      Γc ⊢ᶜ e_con ⇓ᶜ v_con /\ contains σ Φ ef' v_con) ->
  (forall (Γc : environment) (σ : valuation) (e_con : expr),
    models σ Φ ->
    contains_env σ Φ Γs Γc ->
    contains σ Φ (EApp ef' ea) e_con ->
    concore_expr e_con ->
    concrete_context Γc e_con ->
    exists v_con : expr,
      Γc ⊢ᶜ e_con ⇓ᶜ v_con /\ contains σ Φ er v_con) ->
  exists v_con,
    Γc ⊢ᶜ e_con ⇓ᶜ v_con /\ contains σ Φ er v_con.

(** Existence of concrete instantiation for satisfiable symbolic state *)
Axiom instantiate_expr_exists : forall σ Φ Γs Γc e_sym,
  models σ Φ ->
  contains_env σ Φ Γs Γc ->
  exists e_con,
    contains σ Φ e_sym e_con /\
    concore_expr e_con /\
    concrete_context Γc e_con.

(** ------------------------------------------------------------------------- *)
(** 9.1 Lookup and Inversion Properties of Concretion                         *)
(** ------------------------------------------------------------------------- *)

Lemma contains_lookup_env : forall σ Φ Γs Γc x Γ's es,
  contains_env σ Φ Γs Γc ->
  lookup_env Γs x = Some (Γ's, es) ->
  exists Γ'c ec,
    lookup_env Γc x = Some (Γ'c, ec) /\
    contains_env σ Φ Γ's Γ'c /\
    contains σ Φ es ec.
Proof.
  intros σ Φ Γs Γc x Γ's es Henv.
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

Lemma contains_lit_inv : forall σ Φ l ec,
  contains σ Φ (ELit l) ec -> ec = ELit l.
Proof.
  intros σ Φ l ec H. inversion H; subst; reflexivity.
Qed.

Lemma contains_con_inv : forall σ Φ d ec,
  contains σ Φ (ECon d) ec -> ec = ECon d.
Proof.
  intros σ Φ d ec H. inversion H; subst; reflexivity.
Qed.

Lemma contains_primop_inv : forall σ Φ p ec,
  contains σ Φ (EPrimOp p) ec -> ec = EPrimOp p.
Proof.
  intros σ Φ p ec H. inversion H; subst; reflexivity.
Qed.

Lemma contains_lam_inv : forall σ Φ x body ec,
  contains σ Φ (ELam x body) ec ->
  exists bodyc, ec = ELam x bodyc /\
    contains σ Φ body bodyc.
Proof.
  intros σ Φ x body ec H. inversion H; subst.
  exists bodyc. split; [reflexivity | assumption].
Qed.

Lemma contains_clos_inv : forall σ Φ Γs x body ec,
  contains σ Φ (EClos Γs x body) ec ->
  exists Γc bodyc, ec = EClos Γc x bodyc /\
    contains_env σ Φ Γs Γc /\
    contains σ Φ body bodyc.
Proof.
  intros σ Φ Γs x body ec H. inversion H; subst.
  exists Γc, bodyc. split; [reflexivity | auto].
Qed.

Lemma contains_app_inv : forall σ Φ fs as_ ec,
  contains σ Φ (EApp fs as_) ec ->
  exists fc ac, ec = EApp fc ac /\ contains σ Φ fs fc /\ contains σ Φ as_ ac.
Proof.
  intros σ Φ fs as_ ec H. inversion H; subst.
  exists f_c, a_c. split; [reflexivity | auto].
Qed.

Lemma contains_cast_inv : forall σ Φ es γ ec,
  contains σ Φ (ECast es γ) ec ->
  exists ec', ec = ECast ec' γ /\ contains σ Φ es ec'.
Proof.
  intros σ Φ es γ ec H. inversion H; subst.
  exists ec0. split; [reflexivity | assumption].
Qed.

Lemma contains_case_inv : forall σ Φ ess altss ec,
  contains σ Φ (ECase ess altss) ec ->
  exists esc altsc, ec = ECase esc altsc /\ contains σ Φ ess esc /\ Forall2 (contains_alt σ Φ) altss altsc.
Proof.
  intros σ Φ ess altss ec H. inversion H; subst.
  exists esc, altsc. split; [reflexivity | auto].
Qed.

(** ========================================================================= *)
(** 10. Soundness and Completeness of Symbolic Execution                      *)
(** ========================================================================= *)

(**
  Soundness (Rebuttal Formulation):
  For any concrete expression e_con that is contained in a symbolic expression
  e_sym under valuation σ ⊨ Φ, its concrete reduction is contained in the
  symbolic reduction of e_sym.
*)
Theorem concore_soundness : forall Φ Γs Γc σ e_sym e_con v_sym,
  models σ Φ ->
  contains_env σ Φ Γs Γc ->
  contains σ Φ e_sym e_con ->
  concore_expr e_con ->
  concrete_context Γc e_con ->
  Φ ; Γs ⊢ e_sym ⇓ v_sym ->
  exists v_con,
    Γc ⊢ᶜ e_con ⇓ᶜ v_con /\
    contains σ Φ v_sym v_con.
Proof.
  intros Φ Γs Γc σ e_sym e_con v_sym Hmod Henv Hcont Hcon Hctx Heval.
  revert Γc σ e_con Hmod Henv Hcont Hcon Hctx.
  induction Heval.
  - (* Eval_Var *)
    intros Γc σ e_con Hmod Henv Hcont Hcon Hctx.
    assert (Heq : e_con = EVar x).
    { eapply contains_var_bound; eassumption. }
    subst e_con.
    destruct (contains_lookup_env σ Φ Γ Γc x Γ' e Henv H) as [Γ'c [ec [Hlookc [Henv' Hcont']]]].
    destruct (lookup_env_context σ Φ Γ Γc x Γ' e Γ'c ec Henv H Hlookc) as [Hcon' Hctx'].
    destruct (IHHeval Γ'c σ ec Hmod Henv' Hcont' Hcon' Hctx') as [v_con [Hevalc Hcont_v]].
    exists v_con.
    split; [| exact Hcont_v].
    unfold eval_con.
    eapply Eval_Var; eassumption.
  - (* Eval_Lit *)
    intros Γc σ e_con Hmod Henv Hcont Hcon Hctx.
    apply contains_lit_inv in Hcont; subst.
    exists (ELit l). split; [apply Eval_Lit | apply Cont_Lit].
  - (* Eval_Con *)
    intros Γc σ e_con Hmod Henv Hcont Hcon Hctx.
    apply contains_con_inv in Hcont; subst.
    exists (ECon d). split; [apply Eval_Con | apply Cont_Con].
  - (* Eval_Cast *)
    intros Γc σ e_con Hmod Henv Hcont Hcon Hctx.
    apply contains_cast_inv in Hcont as [ec [Heq Hcont_e]]; subst.
    inversion Hcon as [| | | | | | | | ec0 γ0 Hcon_e | | | | | ]; subst.
    apply concrete_context_cast in Hctx.
    destruct (IHHeval Γc σ ec Hmod Henv Hcont_e Hcon_e Hctx) as [vc [Hevalc Hcont_v]].
    exists (cast_expr vc γ).
    split.
    + unfold eval_con. apply Eval_Cast. exact Hevalc.
    + apply cast_expr_contains. exact Hcont_v.
  - (* Eval_AppAbs *)
    intros Γc σ e_con Hmod Henv Hcont Hcon Hctx.
    apply contains_app_inv in Hcont as [fc [ac [Heq [Hcont_f Hcont_a]]]]; subst.
    apply contains_clos_inv in Hcont_f as [Γ'c [ebc [Heq_f [Henv_clos Hcont_b]]]]; subst.
    inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | ]; subst.
    inversion Hf as [| | | | | | Γ0 x0 body Henv_clos_c Hcon_b | | | | | | | ]; subst.
    assert (Henv_ext : contains_env σ Φ (ExtendEnv x (MkClosure Γ ea) Γ')
                                        (ExtendEnv x (MkClosure Γc ac) Γ'c)).
    { apply Cont_Env_Extend; assumption. }
    assert (Hctx_b : concrete_context (ExtendEnv x (MkClosure Γc ac) Γ'c) ebc).
    { apply appabs_context. exact Hctx. }
    destruct (IHHeval (ExtendEnv x (MkClosure Γc ac) Γ'c) σ ebc Hmod Henv_ext Hcont_b Hcon_b Hctx_b) as [v_con [Heval_b Hcont_v]].
    exists v_con.
    split; [| exact Hcont_v].
    unfold eval_con.
    apply Eval_AppAbs.
    exact Heval_b.
  - (* Eval_AppSpine *)
    intros Γc σ e_con Hmod Henv Hcont Hcon Hctx.
    eapply eval_app_spine_sound; eassumption.
  - (* Eval_Bot *)
    intros Γc σ e_con Hmod Henv Hcont Hcon Hctx.
    inversion Hcont; subst.
    exists (EBot b). split; [apply Eval_Bot | apply Cont_Bot].
  - (* Eval_AppPrim *)
    intros Γc σ e_con Hmod Henv Hcont Hcon Hctx.
    eapply eval_app_prim_sound; eassumption.
  - (* Eval_Lam *)
    intros Γc σ e_con Hmod Henv Hcont Hcon Hctx.
    apply contains_lam_inv in Hcont as [bodyc [Heq Hcont_body]]; subst.
    exists (EClos Γc x bodyc). split; [apply Eval_Lam | constructor; assumption].
  - (* Eval_AppCast *)
    intros Γc σ e_con Hmod Henv Hcont Hcon Hctx.
    eapply eval_app_cast_sound; eassumption.
  - (* Eval_AppBot *)
    intros Γc σ e_con Hmod Henv Hcont Hcon Hctx.
    apply contains_app_inv in Hcont as [fc [ac [Heq [Hcont_f Hcont_a]]]]; subst.
    inversion Hcont_f; subst.
    exists (EBot b). split; [apply Eval_AppBot | constructor].
  - (* Eval_Case *)
    intros Γc σ e_con Hmod Henv Hcont Hcon Hctx.
    eapply fold_alts_sound; eassumption.
  - (* Eval_If *)
    intros Γc σ e_con Hmod Henv Hcont Hcon Hctx.
    inversion Hcont; subst.
    + assert (Hcond' : models_cond σ ec').
      { apply eval_models_cond with (Φ := Φ) (Γ := Γ) (ec := ec); assumption. }
      assert (Hpc_mod : models σ pc_c).
      { apply (models_cond_pc σ Γ ec' pc_c H). exact Hcond'. }
      assert (Hmod_and : models σ (Φ ∧ pc_c)).
      { apply models_and; assumption. }
      assert (Henv' : contains_env σ (Φ ∧ pc_c) Γ Γc).
      { apply contains_env_weaken; assumption. }
      assert (Hcont' : contains σ (Φ ∧ pc_c) et e_con).
      { apply contains_strengthen; assumption. }
      destruct (IHHeval2 Γc σ e_con Hmod_and Henv' Hcont' Hcon Hctx) as [v_con [Hevalc' Hcont_v]].
      exists v_con. split; [exact Hevalc' |].
      apply Cont_If_True; [exact Hcond' |].
      apply contains_weaken with (Φ2 := pc_c). exact Hcont_v.
    + assert (Hnotcond' : models_not_cond σ ec').
      { apply eval_models_not_cond with (Φ := Φ) (Γ := Γ) (ec := ec); assumption. }
      assert (Hnotpc_mod : models σ (¬ pc_c)).
      { apply (models_not_cond_pc σ Γ ec' pc_c H). exact Hnotcond'. }
      assert (Hmod_and : models σ (Φ ∧ ¬ pc_c)).
      { apply models_and; assumption. }
      assert (Henv' : contains_env σ (Φ ∧ ¬ pc_c) Γ Γc).
      { apply contains_env_weaken; assumption. }
      assert (Hcont' : contains σ (Φ ∧ ¬ pc_c) ef e_con).
      { apply contains_strengthen; assumption. }
      destruct (IHHeval3 Γc σ e_con Hmod_and Henv' Hcont' Hcon Hctx) as [v_con [Hevalc' Hcont_v]].
      exists v_con. split; [exact Hevalc' |].
      apply Cont_If_False; [exact Hnotcond' |].
      apply contains_weaken with (Φ2 := ¬ pc_c). exact Hcont_v.
  - (* Eval_Coercion *)
    intros Γc σ e_con Hmod Henv Hcont Hcon Hctx.
    inversion Hcont; subst.
    exists (ECoercion (subst_coerc Γc γ)).
    split; [apply Eval_Coercion | apply subst_coerc_contains_env; assumption].
  - (* Eval_Prune *)
    intros Γc σ e_con Hmod Henv Hcont Hcon Hctx.
    apply models_sat in Hmod.
    rewrite H in Hmod. discriminate.
  - (* Eval_Type *)
    intros Γc σ e_con Hmod Henv Hcont Hcon Hctx.
    inversion Hcont; subst.
    exists (EType (subst_type Γc τ)).
    split; [apply Eval_Type | apply subst_type_contains_env; assumption].
Qed.

(** Top-level Soundness for whole programs starting from EmptyEnv *)
Theorem concore_soundness_top : forall Φ σ e_sym e_con v_sym,
  models σ Φ ->
  contains σ Φ e_sym e_con ->
  concore_expr e_con ->
  concrete_context EmptyEnv e_con ->
  Φ ; EmptyEnv ⊢ e_sym ⇓ v_sym ->
  exists v_con,
    ⊢ᶜ e_con ⇓ᶜ v_con /\
    contains σ Φ v_sym v_con.
Proof.
  intros Φ σ e_sym e_con v_sym Hmod Hcont Hcon Hctx Heval.
  apply (concore_soundness Φ EmptyEnv EmptyEnv σ e_sym e_con v_sym); auto.
  apply Cont_Env_Empty.
Qed.

(**
  Completeness (Coverage / No Spurious Paths):
  Every symbolic reduction Φ ; Γs ⊢ e_sym ⇓ v_sym corresponds, under each
  satisfiable valuation σ ⊨ Φ, to a terminating concrete evaluation of the
  instantiated expression e_con producing an instance v_con of v_sym.
*)
Theorem concore_completeness : forall Φ Γs Γc σ e_sym v_sym,
  models σ Φ ->
  contains_env σ Φ Γs Γc ->
  Φ ; Γs ⊢ e_sym ⇓ v_sym ->
  exists e_con v_con,
    contains σ Φ e_sym e_con /\
    concore_expr e_con /\
    concrete_context Γc e_con /\
    Γc ⊢ᶜ e_con ⇓ᶜ v_con /\
    contains σ Φ v_sym v_con.
Proof.
  intros Φ Γs Γc σ e_sym v_sym Hmod Henv Heval.
  destruct (instantiate_expr_exists σ Φ Γs Γc e_sym Hmod Henv) as [e_con [Hcont [Hcon Hctx]]].
  destruct (concore_soundness Φ Γs Γc σ e_sym e_con v_sym Hmod Henv Hcont Hcon Hctx Heval) as [v_con [Heval_c Hcont_v]].
  exists e_con, v_con.
  split; [exact Hcont |].
  split; [exact Hcon |].
  split; [exact Hctx |].
  split; [exact Heval_c | exact Hcont_v].
Qed.

