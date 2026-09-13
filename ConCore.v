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
(** 8.4 ConCore Subject Reduction (Preservation)                              *)
(** ------------------------------------------------------------------------- *)

Theorem concore_preservation_mut :
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

(** ConCore Preservation (Subject Reduction):
    Concrete evaluation in a concrete environment produces a ConCore value. *)
Theorem concore_preservation : forall Γ e v,
  concrete_env Γ ->
  concore_expr e ->
  Γ ⊢ᶜ e ⇓ᶜ v ->
  concore_expr v.
Proof.
  intros Γ e v Henv Hcon Heval.
  unfold eval_con in Heval.
  destruct concore_preservation_mut as [Heval_pres _].
  apply Heval_pres with (Φ := pc_true) (Γ := Γ) (e := e); auto.
Qed.

(** Closed ConCore expressions evaluate to ConCore values *)
Corollary concore_preservation_closed : forall e v,
  concore_expr e ->
  ⊢ᶜ e ⇓ᶜ v ->
  concore_expr v.
Proof.
  intros e v Hcon Heval.
  apply (concore_preservation EmptyEnv e v); auto.
  constructor.
Qed.

(** Closed Source System FC expressions evaluate to ConCore values *)
Corollary source_preservation_closed : forall e v,
  source_expr e ->
  ⊢ᶜ e ⇓ᶜ v ->
  concore_expr v.
Proof.
  intros e v Hsrc Heval.
  apply (concore_preservation_closed e v); auto.
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

(** Mutual inductive instantiation relation relating symbolic expressions to concrete instances *)
Inductive instantiates (σ : valuation) (Φ : path_condition) : expr -> expr -> Prop :=
  (** Bound variable reflexivity *)
  | Inst_Var_Bound : forall x,
      instantiates σ Φ (EVar x) (EVar x)

  (** Symbolic variable instantiation via valuation σ *)
  | Inst_Var_Sym : forall x v,
      σ x = v ->
      concore_expr v ->
      instantiates σ Φ (EVar x) v

  (** Literals, Primitives, Constructors, Types, Coercions, Bottoms *)
  | Inst_Lit : forall l,
      instantiates σ Φ (ELit l) (ELit l)
  | Inst_PrimOp : forall p,
      instantiates σ Φ (EPrimOp p) (EPrimOp p)
  | Inst_Con : forall d,
      instantiates σ Φ (ECon d) (ECon d)
  | Inst_Coercion : forall γ,
      instantiates σ Φ (ECoercion γ) (ECoercion γ)
  | Inst_Type : forall τ,
      instantiates σ Φ (EType τ) (EType τ)
  | Inst_Bot : forall b,
      instantiates σ Φ (EBot b) (EBot b)

  (** Structural congruence *)
  | Inst_App : forall f_s a_s f_c a_c,
      instantiates σ Φ f_s f_c ->
      instantiates σ Φ a_s a_c ->
      instantiates σ Φ (EApp f_s a_s) (EApp f_c a_c)
  | Inst_Lam : forall x bodys bodyc,
      instantiates σ Φ bodys bodyc ->
      instantiates σ Φ (ELam x bodys) (ELam x bodyc)
  | Inst_Clos : forall Γs Γc x bodys bodyc,
      instantiates_env σ Φ Γs Γc ->
      instantiates σ Φ bodys bodyc ->
      instantiates σ Φ (EClos Γs x bodys) (EClos Γc x bodyc)
  | Inst_Cast : forall es ec γ,
      instantiates σ Φ es ec ->
      instantiates σ Φ (ECast es γ) (ECast ec γ)
  | Inst_Case : forall ess esc altss altsc,
      instantiates σ Φ ess esc ->
      Forall2 (instantiates_alt σ Φ) altss altsc ->
      instantiates σ Φ (ECase ess altss) (ECase esc altsc)

  (** Branch resolution: True branch feasible under σ *)
  | Inst_If_True : forall ec et ef etc pc_c,
      expr_to_pc EmptyEnv ec = Some pc_c ->
      models σ (Φ ∧ pc_c) ->
      instantiates σ (Φ ∧ pc_c) et etc ->
      instantiates σ Φ (EIf ec et ef) etc

  (** Branch resolution: False branch feasible under σ *)
  | Inst_If_False : forall ec et ef efc pc_c,
      expr_to_pc EmptyEnv ec = Some pc_c ->
      models σ (Φ ∧ ¬ pc_c) ->
      instantiates σ (Φ ∧ ¬ pc_c) ef efc ->
      instantiates σ Φ (EIf ec et ef) efc

with instantiates_alt (σ : valuation) (Φ : path_condition) : alt -> alt -> Prop :=
  | Inst_Alt : forall d xs eps epc,
      instantiates σ Φ eps epc ->
      instantiates_alt σ Φ (Alt d xs eps) (Alt d xs epc)

with instantiates_env (σ : valuation) (Φ : path_condition) : environment -> environment -> Prop :=
  | Inst_Env_Empty :
      instantiates_env σ Φ EmptyEnv EmptyEnv
  | Inst_Env_Extend : forall x Γs Γc es ec rest_s rest_c,
      instantiates_env σ Φ Γs Γc ->
      instantiates σ Φ es ec ->
      instantiates_env σ Φ rest_s rest_c ->
      instantiates_env σ Φ (ExtendEnv x (MkClosure Γs es) rest_s)
                           (ExtendEnv x (MkClosure Γc ec) rest_c).

(** ========================================================================= *)
(** 10. Soundness and Completeness of Symbolic Execution                      *)
(** ========================================================================= *)

(**
  Soundness (Simulation / Over-approximation):
  For any concrete expression e_con that is an instance of symbolic expression e_sym
  under valuation σ and path condition Φ, its concrete reduction is an instance of
  the symbolic reduction of e_sym.
*)
Theorem concore_soundness : forall Φ Γs Γc σ e_sym e_con v_con,
  models σ Φ ->
  instantiates_env σ Φ Γs Γc ->
  instantiates σ Φ e_sym e_con ->
  concore_expr e_con ->
  concrete_context Γc e_con ->
  Γc ⊢ᶜ e_con ⇓ᶜ v_con ->
  exists v_sym,
    Φ ; Γs ⊢ e_sym ⇓ v_sym /\
    instantiates σ Φ v_sym v_con.
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
    instantiates σ Φ e_sym e_con /\
    concore_expr e_con /\
    concrete_context Γc e_con /\
    Γc ⊢ᶜ e_con ⇓ᶜ v_con /\
    instantiates σ Φ v_sym v_con.
Admitted.
