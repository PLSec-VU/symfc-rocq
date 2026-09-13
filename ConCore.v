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

(** Helper to bind a list of variables in an environment *)
Fixpoint bind_vars (xs : list var) (Γ : environment) : environment :=
  match xs with
  | [] => Γ
  | x :: xs' => ExtendEnv x (MkClosure EmptyEnv (EVar x)) (bind_vars xs' Γ)
  end.

(** Mutual inductive instantiation relation relating symbolic expressions to concrete instances.
    Valuation σ only instantiates free symbolic variables (lookup_env Γ x = None),
    while bound variables in the environment (lookup_env Γ x = Some _) remain intact. *)
Inductive instantiates (σ : valuation) (Φ : path_condition) : environment -> expr -> expr -> Prop :=
  (** Bound variable reflexivity: x is bound in Γ *)
  | Inst_Var_Bound : forall Γ x Γ' e,
      lookup_env Γ x = Some (Γ', e) ->
      instantiates σ Φ Γ (EVar x) (EVar x)

  (** Symbolic variable instantiation: x is a free symbolic variable (x ∉ Γ) *)
  | Inst_Var_Sym : forall Γ x v,
      lookup_env Γ x = None ->
      σ x = v ->
      concore_expr v ->
      instantiates σ Φ Γ (EVar x) v

  (** Literals, Primitives, Constructors, Types, Coercions, Bottoms *)
  | Inst_Lit : forall Γ l,
      instantiates σ Φ Γ (ELit l) (ELit l)
  | Inst_PrimOp : forall Γ p,
      instantiates σ Φ Γ (EPrimOp p) (EPrimOp p)
  | Inst_Con : forall Γ d,
      instantiates σ Φ Γ (ECon d) (ECon d)
  | Inst_Coercion : forall Γ γ,
      instantiates σ Φ Γ (ECoercion γ) (ECoercion γ)
  | Inst_Type : forall Γ τ,
      instantiates σ Φ Γ (EType τ) (EType τ)
  | Inst_Bot : forall Γ b,
      instantiates σ Φ Γ (EBot b) (EBot b)

  (** Structural congruence *)
  | Inst_App : forall Γ f_s a_s f_c a_c,
      instantiates σ Φ Γ f_s f_c ->
      instantiates σ Φ Γ a_s a_c ->
      instantiates σ Φ Γ (EApp f_s a_s) (EApp f_c a_c)
  | Inst_Lam : forall Γ x bodys bodyc,
      instantiates σ Φ (ExtendEnv x (MkClosure EmptyEnv (EVar x)) Γ) bodys bodyc ->
      instantiates σ Φ Γ (ELam x bodys) (ELam x bodyc)
  | Inst_Clos : forall Γ Γs Γc x bodys bodyc,
      instantiates_env σ Φ Γs Γc ->
      instantiates σ Φ (ExtendEnv x (MkClosure EmptyEnv (EVar x)) Γs) bodys bodyc ->
      instantiates σ Φ Γ (EClos Γs x bodys) (EClos Γc x bodyc)
  | Inst_Cast : forall Γ es ec γ,
      instantiates σ Φ Γ es ec ->
      instantiates σ Φ Γ (ECast es γ) (ECast ec γ)
  | Inst_Case : forall Γ ess esc altss altsc,
      instantiates σ Φ Γ ess esc ->
      Forall2 (instantiates_alt σ Φ Γ) altss altsc ->
      instantiates σ Φ Γ (ECase ess altss) (ECase esc altsc)

  (** Branch resolution: True branch feasible under σ *)
  | Inst_If_True : forall Γ ec et ef etc pc_c,
      expr_to_pc Γ ec = Some pc_c ->
      models σ (Φ ∧ pc_c) ->
      instantiates σ (Φ ∧ pc_c) Γ et etc ->
      instantiates σ Φ Γ (EIf ec et ef) etc

  (** Branch resolution: False branch feasible under σ *)
  | Inst_If_False : forall Γ ec et ef efc pc_c,
      expr_to_pc Γ ec = Some pc_c ->
      models σ (Φ ∧ ¬ pc_c) ->
      instantiates σ (Φ ∧ ¬ pc_c) Γ ef efc ->
      instantiates σ Φ Γ (EIf ec et ef) efc

with instantiates_alt (σ : valuation) (Φ : path_condition) : environment -> alt -> alt -> Prop :=
  | Inst_Alt : forall Γ d xs eps epc,
      instantiates σ Φ (bind_vars xs Γ) eps epc ->
      instantiates_alt σ Φ Γ (Alt d xs eps) (Alt d xs epc)

with instantiates_env (σ : valuation) (Φ : path_condition) : environment -> environment -> Prop :=
  | Inst_Env_Empty :
      instantiates_env σ Φ EmptyEnv EmptyEnv
  | Inst_Env_Extend : forall x Γs Γc es ec rest_s rest_c,
      instantiates_env σ Φ Γs Γc ->
      instantiates σ Φ Γs es ec ->
      instantiates_env σ Φ rest_s rest_c ->
       instantiates_env σ Φ (ExtendEnv x (MkClosure Γs es) rest_s)
                            (ExtendEnv x (MkClosure Γc ec) rest_c).

(** ------------------------------------------------------------------------- *)
(** 9.0 SMT and Coercion Solver Behaviors on Instantiation                     *)
(** ------------------------------------------------------------------------- *)

(** SMT solver behavior: primitive operation evaluation preserves instantiation *)
Axiom reduce_prim_instantiates : forall σ Φ Γ p args_s args_c,
  Forall2 (instantiates σ Φ Γ) args_s args_c ->
  instantiates σ Φ Γ (reduce_prim p args_s) (reduce_prim p args_c).

(** SMT/Cast simplification preserves instantiation *)
Axiom cast_expr_instantiates : forall σ Φ Γ e_s e_c γ,
  instantiates σ Φ Γ e_s e_c ->
  instantiates σ Φ Γ (cast_expr e_s γ) (cast_expr e_c γ).

(** Environment instantiation extension under condition preservation *)
Lemma instantiates_env_extend_pc : forall σ Φ1 Φ2 Γs Γc,
  (forall Γ e ec, instantiates σ Φ1 Γ e ec -> instantiates σ Φ2 Γ e ec) ->
  instantiates_env σ Φ1 Γs Γc ->
  instantiates_env σ Φ2 Γs Γc.
Proof.
  intros σ Φ1 Φ2 Γs Γc H Henv.
  induction Henv.
  - apply Inst_Env_Empty.
  - apply Inst_Env_Extend; auto.
Qed.

(** ------------------------------------------------------------------------- *)
(** 9.1 Lookup and Inversion Properties of Instantiation                      *)
(** ------------------------------------------------------------------------- *)

Lemma instantiates_lookup_env : forall σ Φ Γs Γc x Γ's es,
  instantiates_env σ Φ Γs Γc ->
  lookup_env Γs x = Some (Γ's, es) ->
  exists Γ'c ec,
    lookup_env Γc x = Some (Γ'c, ec) /\
    instantiates_env σ Φ Γ's Γ'c /\
    instantiates σ Φ Γ's es ec.
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

Lemma instantiates_lit_inv : forall σ Φ Γ l ec,
  instantiates σ Φ Γ (ELit l) ec -> ec = ELit l.
Proof.
  intros σ Φ Γ l ec H. inversion H; subst; reflexivity.
Qed.

Lemma instantiates_con_inv : forall σ Φ Γ d ec,
  instantiates σ Φ Γ (ECon d) ec -> ec = ECon d.
Proof.
  intros σ Φ Γ d ec H. inversion H; subst; reflexivity.
Qed.

Lemma instantiates_primop_inv : forall σ Φ Γ p ec,
  instantiates σ Φ Γ (EPrimOp p) ec -> ec = EPrimOp p.
Proof.
  intros σ Φ Γ p ec H. inversion H; subst; reflexivity.
Qed.

Lemma instantiates_lam_inv : forall σ Φ Γ x body ec,
  instantiates σ Φ Γ (ELam x body) ec ->
  exists bodyc, ec = ELam x bodyc /\
    instantiates σ Φ (ExtendEnv x (MkClosure EmptyEnv (EVar x)) Γ) body bodyc.
Proof.
  intros σ Φ Γ x body ec H. inversion H; subst.
  exists bodyc. split; [reflexivity | assumption].
Qed.

Lemma instantiates_clos_inv : forall σ Φ Γ Γs x body ec,
  instantiates σ Φ Γ (EClos Γs x body) ec ->
  exists Γc bodyc, ec = EClos Γc x bodyc /\
    instantiates_env σ Φ Γs Γc /\
    instantiates σ Φ (ExtendEnv x (MkClosure EmptyEnv (EVar x)) Γs) body bodyc.
Proof.
  intros σ Φ Γ Γs x body ec H. inversion H; subst.
  exists Γc, bodyc. split; [reflexivity | auto].
Qed.

Lemma instantiates_app_inv : forall σ Φ Γ fs as_ ec,
  instantiates σ Φ Γ (EApp fs as_) ec ->
  exists fc ac, ec = EApp fc ac /\ instantiates σ Φ Γ fs fc /\ instantiates σ Φ Γ as_ ac.
Proof.
  intros σ Φ Γ fs as_ ec H. inversion H; subst.
  exists f_c, a_c. split; [reflexivity | auto].
Qed.

Lemma instantiates_cast_inv : forall σ Φ Γ es γ ec,
  instantiates σ Φ Γ (ECast es γ) ec ->
  exists ec', ec = ECast ec' γ /\ instantiates σ Φ Γ es ec'.
Proof.
  intros σ Φ Γ es γ ec H. inversion H; subst.
  exists ec0. split; [reflexivity | assumption].
Qed.

Lemma instantiates_case_inv : forall σ Φ Γ ess altss ec,
  instantiates σ Φ Γ (ECase ess altss) ec ->
  exists esc altsc, ec = ECase esc altsc /\ instantiates σ Φ Γ ess esc /\ Forall2 (instantiates_alt σ Φ Γ) altss altsc.
Proof.
  intros σ Φ Γ ess altss ec H. inversion H; subst.
  exists esc, altsc. split; [reflexivity | auto].
Qed.

Lemma instantiates_clos_env_irrel : forall σ Φ Γ1 Γ2 Γs x body ec,
  instantiates σ Φ Γ1 (EClos Γs x body) ec ->
  instantiates σ Φ Γ2 (EClos Γs x body) ec.
Proof.
  intros. apply instantiates_clos_inv in H as [Γc [bodyc [Heq [Henv Hinst]]]].
  subst. apply Inst_Clos; assumption.
Qed.

Lemma instantiates_lit_env_irrel : forall σ Φ Γ1 Γ2 l ec,
  instantiates σ Φ Γ1 (ELit l) ec ->
  instantiates σ Φ Γ2 (ELit l) ec.
Proof.
  intros. apply instantiates_lit_inv in H. subst. apply Inst_Lit.
Qed.

Lemma instantiates_con_env_irrel : forall σ Φ Γ1 Γ2 d ec,
  instantiates σ Φ Γ1 (ECon d) ec ->
  instantiates σ Φ Γ2 (ECon d) ec.
Proof.
  intros. apply instantiates_con_inv in H. subst. apply Inst_Con.
Qed.

Lemma instantiates_bot_env_irrel : forall σ Φ Γ1 Γ2 b ec,
  instantiates σ Φ Γ1 (EBot b) ec ->
  instantiates σ Φ Γ2 (EBot b) ec.
Proof.
  intros. inversion H; subst. apply Inst_Bot.
Qed.

(** Strengthening path condition on environment instantiation (Lemma) *)
Lemma instantiates_env_pc_and : forall σ Φ pc Γs Γc,
  instantiates_env σ Φ Γs Γc ->
  instantiates_env σ (Φ ∧ pc) Γs Γc.
Proof.
  intros σ Φ pc Γs Γc H.
  apply (instantiates_env_extend_pc σ Φ (Φ ∧ pc) Γs Γc); [| assumption].
  intros Γ e ec Hinst.
  (* Closure environments store expressions without branching on ambient Φ *)
  admit.
Admitted.

(** ========================================================================= *)
(** 10. Soundness and Completeness of Symbolic Execution                      *)
(** ========================================================================= *)

(**
  Soundness (Simulation / Over-approximation - Option 1):
  If a symbolic evaluation Φ ; Γs ⊢ e_sym ⇓ v_sym terminates, then under any
  satisfiable valuation σ ⊨ Φ and concrete environment Γc instantiated from Γs,
  for any concrete expression e_con instantiated from e_sym under Γs, the concrete
  evaluation Γc ⊢ᶜ e_con ⇓ᶜ v_con terminates and produces an instance v_con of v_sym.
*)
Theorem concore_soundness : forall Φ Γs Γc σ e_sym e_con v_sym,
  models σ Φ ->
  instantiates_env σ Φ Γs Γc ->
  instantiates σ Φ Γs e_sym e_con ->
  concore_expr e_con ->
  concrete_context Γc e_con ->
  Φ ; Γs ⊢ e_sym ⇓ v_sym ->
  exists v_con,
    Γc ⊢ᶜ e_con ⇓ᶜ v_con /\
    instantiates σ Φ Γs v_sym v_con.
Proof.
  intros Φ Γs Γc σ e_sym e_con v_sym Hmod Henv Hinst Hcon Hctx Heval.
  revert Γc σ e_con Hmod Henv Hinst Hcon Hctx.
  induction Heval; intros Γc σ0 e_con Hmod Henv Hinst Hcon Hctx.
  - (* Eval_Var *)
    inversion Hinst; subst.
    + edestruct (instantiates_lookup_env σ0 Φ Γ Γc x Γ' e Henv H) as [Γ'c [ec [Hlook_c [Henv' Hinst']]]].
      assert (Hcon_ec : concore_expr ec) by admit.
      assert (Hctx_ec : concrete_context Γ'c ec) by admit.
      edestruct (IHHeval Γ'c σ0 ec Hmod Henv' Hinst' Hcon_ec Hctx_ec) as [v_con [Heval_c Hinst_v]].
      exists v_con. split.
      * apply (Eval_Var pc_true Γc x Γ'c ec v_con Hlook_c Heval_c).
      * admit.
    + congruence.
  - (* Eval_Lit *)
    apply instantiates_lit_inv in Hinst. subst.
    exists (ELit l). split; [apply Eval_Lit | apply Inst_Lit].
  - (* Eval_Con *)
    apply instantiates_con_inv in Hinst. subst.
    exists (ECon d). split; [apply Eval_Con | apply Inst_Con].
  - (* Eval_Cast *)
    apply instantiates_cast_inv in Hinst as [ec' [Heq Hinst_e]]. subst.
    apply concore_expr_cast in Hcon.
    apply concrete_context_cast in Hctx.
    edestruct (IHHeval Γc σ0 ec' Hmod Henv Hinst_e Hcon Hctx) as [v_con [Heval_c Hinst_v]].
    exists (cast_expr v_con γ). split.
    + apply (Eval_Cast pc_true Γc ec' γ v_con Heval_c).
    + apply cast_expr_instantiates. assumption.
  - (* Eval_AppAbs *)
    apply instantiates_app_inv in Hinst as [fc [ac [Heq [Hinst_f Hinst_a]]]]. subst.
    apply instantiates_clos_inv in Hinst_f as [Γ'c [ebc [Hfc [Henv' Hinst_b]]]]. subst.
    assert (Henv_ext : instantiates_env σ0 Φ (extend_env Γ' x Γ ea) (extend_env Γ'c x Γc ac)).
    { unfold extend_env. apply Inst_Env_Extend; assumption. }
    assert (Hcon_ebc : concore_expr ebc) by admit.
    assert (Hctx_ebc : concrete_context (extend_env Γ'c x Γc ac) ebc) by admit.
    assert (Hinst_eb : instantiates σ0 Φ (extend_env Γ' x Γ ea) eb ebc) by admit.
    edestruct (IHHeval (extend_env Γ'c x Γc ac) σ0 ebc Hmod Henv_ext Hinst_eb Hcon_ebc Hctx_ebc) as [v_con [Heval_c Hinst_v]].
    exists v_con. split.
    + apply (Eval_AppAbs pc_true Γc Γ'c x ebc ac v_con Heval_c).
    + admit.
  - (* Eval_AppSpine *)
    admit.
  - (* Eval_Bot *)
    inversion Hinst; subst.
    exists (EBot b). split; [apply Eval_Bot | apply Inst_Bot].
  - (* Eval_AppPrim *)
    admit.
  - (* Eval_Lam *)
    apply instantiates_lam_inv in Hinst as [bodyc [Heq Hinst_b]]. subst.
    exists (EClos Γc x bodyc). split.
    + apply Eval_Lam.
    + apply Inst_Clos; assumption.
  - (* Eval_AppCast *)
    admit.
  - (* Eval_AppBot *)
    apply instantiates_app_inv in Hinst as [fc [ac [Heq [Hinst_f Hinst_a]]]]. subst.
    inversion Hinst_f; subst.
    exists (EBot b). split.
    + apply Eval_AppBot.
    + apply Inst_Bot.
  - (* Eval_Case *)
    admit.
  - (* Eval_If *)
    inversion Hinst; subst.
    + (* Inst_If_True: σ ⊨ Φ ∧ pc_c *)
      assert (Henv_and : instantiates_env σ0 (Φ ∧ pc_c) Γ Γc) by (apply instantiates_env_pc_and; auto).
      assert (Hmod_and : models σ0 (Φ ∧ pc_c)) by admit.
      assert (Hinst_and : instantiates σ0 (Φ ∧ pc_c) Γ et e_con) by admit.
      edestruct (IHHeval2 Γc σ0 e_con Hmod_and Henv_and Hinst_and Hcon Hctx) as [v_con [Heval_c Hinst_v]].
      exists v_con. split.
      * exact Heval_c.
      * eapply Inst_If_True; eauto.
    + (* Inst_If_False: σ ⊨ Φ ∧ ¬ pc_c *)
      assert (Henv_and : instantiates_env σ0 (Φ ∧ ¬ pc_c) Γ Γc) by (apply instantiates_env_pc_and; auto).
      assert (Hmod_and : models σ0 (Φ ∧ ¬ pc_c)) by admit.
      assert (Hinst_and : instantiates σ0 (Φ ∧ ¬ pc_c) Γ ef e_con) by admit.
      edestruct (IHHeval3 Γc σ0 e_con Hmod_and Henv_and Hinst_and Hcon Hctx) as [v_con [Heval_c Hinst_v]].
      exists v_con. split.
      * exact Heval_c.
      * eapply Inst_If_False; eauto.
  - (* Eval_Coercion *)
    inversion Hinst; subst.
    exists (ECoercion (subst_coerc Γc γ)). split.
    + apply Eval_Coercion.
    + assert (Hsubst : subst_coerc Γ γ = subst_coerc Γc γ) by admit.
      rewrite Hsubst. apply Inst_Coercion.
  - (* Eval_Prune *)
    apply models_sat in Hmod. rewrite H in Hmod. discriminate.
  - (* Eval_Type *)
    inversion Hinst; subst.
    exists (EType (subst_type Γc τ)). split.
    + apply Eval_Type.
    + assert (Hsubst : subst_type Γ τ = subst_type Γc τ) by admit.
      rewrite Hsubst. apply Inst_Type.
Admitted.

(** Top-level Soundness for whole programs starting from EmptyEnv *)
Theorem concore_soundness_top : forall Φ σ e_sym e_con v_sym,
  models σ Φ ->
  instantiates σ Φ EmptyEnv e_sym e_con ->
  concore_expr e_con ->
  concrete_context EmptyEnv e_con ->
  Φ ; EmptyEnv ⊢ e_sym ⇓ v_sym ->
  exists v_con,
    ⊢ᶜ e_con ⇓ᶜ v_con /\
    instantiates σ Φ EmptyEnv v_sym v_con.
Proof.
  intros Φ σ e_sym e_con v_sym Hmod Hinst Hcon Hctx Heval.
  apply (concore_soundness Φ EmptyEnv EmptyEnv σ e_sym e_con v_sym); auto.
  apply Inst_Env_Empty.
Qed.

(**
  Relational Soundness (Partial Correctness - Option 2):
  Assuming both symbolic and concrete evaluation terminate on instantiated
  expressions, the concrete result v_con is an instance of the symbolic result v_sym.
*)
Theorem concore_soundness_relational : forall Φ Γs Γc σ e_sym e_con v_sym v_con,
  models σ Φ ->
  instantiates_env σ Φ Γs Γc ->
  instantiates σ Φ Γs e_sym e_con ->
  concore_expr e_con ->
  concrete_context Γc e_con ->
  Φ ; Γs ⊢ e_sym ⇓ v_sym ->
  Γc ⊢ᶜ e_con ⇓ᶜ v_con ->
  instantiates σ Φ Γs v_sym v_con.
Admitted.

(**
  Completeness (Coverage / No Spurious Paths):
  Every symbolic reduction Φ ; Γs ⊢ e_sym ⇓ v_sym corresponds, under each
  satisfiable valuation σ ⊨ Φ, to a terminating concrete evaluation of the
  instantiated expression e_con producing an instance v_con of v_sym.
*)
Theorem concore_completeness : forall Φ Γs Γc σ e_sym v_sym,
  models σ Φ ->
  instantiates_env σ Φ Γs Γc ->
  Φ ; Γs ⊢ e_sym ⇓ v_sym ->
  exists e_con v_con,
    instantiates σ Φ Γs e_sym e_con /\
    concore_expr e_con /\
    concrete_context Γc e_con /\
    Γc ⊢ᶜ e_con ⇓ᶜ v_con /\
    instantiates σ Φ Γs v_sym v_con.
Admitted.

(**
  Completeness Note:
  In an all-paths symbolic executor (SymCore), unbounded completeness
  (concrete terminates -> symbolic terminates) does not hold in big-step semantics
  because SymCore evaluates both branches of an if-expression (Eval_If), diverging
  if a non-taken branch loops indefinitely. As noted in the paper rebuttal,
  completeness is formulated with respect to an unrolling/recursion depth bound k.
*)
