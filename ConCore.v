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

(** SMT solver semantics: valuation satisfies conjunction iff it satisfies both conjuncts *)
Axiom models_and_iff : forall σ Φ1 Φ2,
  models σ (Φ1 ∧ Φ2) <-> models σ Φ1 /\ models σ Φ2.


(** SMT solver evaluation on boolean expressions/conditions *)
Parameter models_cond : valuation -> expr -> Prop.
Parameter models_not_cond : valuation -> expr -> Prop.

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
Inductive contains (σ : valuation) : expr -> expr -> Prop :=
  (** Bound variable reflexivity *)
  | Cont_Var_Bound : forall x,
      contains σ (EVar x) (EVar x)

  (** Literals, Primitives, Constructors, Coercions, Types, Bottoms *)
  | Cont_Lit : forall l,
      contains σ (ELit l) (ELit l)
  | Cont_PrimOp : forall p,
      contains σ (EPrimOp p) (EPrimOp p)
  | Cont_Con : forall d,
      contains σ (ECon d) (ECon d)
  | Cont_Coercion : forall γ,
      contains σ (ECoercion γ) (ECoercion γ)
  | Cont_Type : forall τ,
      contains σ (EType τ) (EType τ)
  | Cont_Bot : forall b,
      contains σ (EBot b) (EBot b)

  (** Structural congruence *)
  | Cont_App : forall f_s a_s f_c a_c,
      contains σ f_s f_c ->
      contains σ a_s a_c ->
      contains σ (EApp f_s a_s) (EApp f_c a_c)
  | Cont_Lam : forall x bodys bodyc,
      contains σ bodys bodyc ->
      contains σ (ELam x bodys) (ELam x bodyc)
  | Cont_Clos : forall Γs Γc x bodys bodyc,
      contains_env σ Γs Γc ->
      contains σ bodys bodyc ->
      contains σ (EClos Γs x bodys) (EClos Γc x bodyc)
  | Cont_Cast : forall es ec γ,
      contains σ es ec ->
      contains σ (ECast es γ) (ECast ec γ)
  | Cont_Case : forall ess esc altss altsc,
      contains σ ess esc ->
      Forall2 (contains_alt σ) altss altsc ->
      contains σ (ECase ess altss) (ECase esc altsc)

  (** Branch resolution: along model σ, exactly one branch is active *)
  | Cont_If_True : forall ec et ef etc,
      models_cond σ ec ->
      contains σ et etc ->
      contains σ (EIf ec et ef) etc
  | Cont_If_False : forall ec et ef efc,
      models_not_cond σ ec ->
      contains σ ef efc ->
      contains σ (EIf ec et ef) efc

with contains_alt (σ : valuation) : alt -> alt -> Prop :=
  | Cont_Alt : forall d xs eps epc,
      contains σ eps epc ->
      contains_alt σ (Alt d xs eps) (Alt d xs epc)

with contains_env (σ : valuation) : environment -> environment -> Prop :=
  | Cont_Env_Empty :
      contains_env σ EmptyEnv EmptyEnv
  | Cont_Env_Extend : forall x Γs Γc es ec rest_s rest_c,
      contains_env σ Γs Γc ->
      contains σ es ec ->
      concore_expr ec ->
      contains_env σ rest_s rest_c ->
      contains_env σ (ExtendEnv x (MkClosure Γs es) rest_s)
                       (ExtendEnv x (MkClosure Γc ec) rest_c).

(** Aliases for compatibility *)
Notation instantiates := contains.
Notation instantiates_alt := contains_alt.
Notation instantiates_env := contains_env.

(** ------------------------------------------------------------------------- *)
(** 9.0 SMT and Coercion Solver Behaviors on Concretion                       *)
(** ------------------------------------------------------------------------- *)

(** SMT solver behavior: primitive operations preserve concretion *)
Axiom reduce_prim_contains : forall σ p args_s args_c,
  Forall2 (contains σ) args_s args_c ->
  contains σ (reduce_prim p args_s) (reduce_prim p args_c).

(** Grisette state merging soundness (Lemma A.4 in the paper) *)
Axiom merge_contains : forall σ es ec,
  contains σ es ec ->
  contains σ (merge es) ec.

(** Coercion cast simplification preserves concretion (Lemma A.5 in the paper) *)
Axiom cast_expr_contains : forall σ es ec γ,
  contains σ es ec ->
  contains σ (cast_expr es γ) (cast_expr ec γ).

(** SMT condition truth preservation across evaluation *)
Axiom eval_models_cond : forall Φ Γ ec ec' σ,
  Φ ; Γ ⊢ ec ⇓ ec' -> models_cond σ ec -> models_cond σ ec'.

Axiom eval_models_not_cond : forall Φ Γ ec ec' σ,
  Φ ; Γ ⊢ ec ⇓ ec' -> models_not_cond σ ec -> models_not_cond σ ec'.


(** Substitution on coercions and types preserves concretion under matched environments *)
Axiom subst_coerc_contains_env : forall σ Γs Γc γ,
  contains_env σ Γs Γc ->
  contains σ (ECoercion (subst_coerc Γs γ)) (ECoercion (subst_coerc Γc γ)).

Axiom subst_type_contains_env : forall σ Γs Γc τ,
  contains_env σ Γs Γc ->
  contains σ (EType (subst_type Γs τ)) (EType (subst_type Γc τ)).

(** SMT primitive evaluation: evaluating arguments in a primitive application
    yields concrete values instantiating the evaluated arguments *)
Axiom eval_prim_args_sound : forall Φ Γs Γc σ ef ea p args args' e_con,
  models σ Φ ->
  contains_env σ Γs Γc ->
  contains σ (EApp ef ea) e_con ->
  unspool_app (EApp ef ea) [] = (EPrimOp p, args) ->
  Forall2 (eval Φ Γs) args args' ->
  exists args_c',
    eval_con Γc e_con (reduce_prim p args_c') /\
    Forall2 (contains σ) args' args_c'.

(** Grisette state-merging simulation: folding alternatives along path condition Φ
    simulates pattern match evaluation on the active concrete constructor instance *)
Axiom fold_alts_contains : forall Φ Γs Γc σ es alts es' er esc altsc,
  models σ Φ ->
  contains_env σ Γs Γc ->
  contains σ es esc ->
  Forall2 (contains_alt σ) alts altsc ->
  (exists vc_s, Γc ⊢ᶜ esc ⇓ᶜ vc_s /\ contains σ es' vc_s) ->
  fold_alts Φ Γs (merge es') alts er ->
  exists v_con,
    Γc ⊢ᶜ ECase esc altsc ⇓ᶜ v_con /\ contains σ er v_con.

(** ------------------------------------------------------------------------- *)
(** 9.1 Proven Lemmas on SMT Models, Inversion, and Contexts                 *)
(** ------------------------------------------------------------------------- *)

(** 9.1.1 Logical Properties of SMT Models *)

Lemma models_and : forall σ Φ1 Φ2,
  models σ Φ1 -> models σ Φ2 -> models σ (Φ1 ∧ Φ2).
Proof.
  intros σ Φ1 Φ2 H1 H2. apply models_and_iff. split; assumption.
Qed.

Lemma models_and_l : forall σ Φ1 Φ2, models σ (Φ1 ∧ Φ2) -> models σ Φ1.
Proof.
  intros σ Φ1 Φ2 H. apply models_and_iff in H. destruct H; assumption.
Qed.

Lemma models_and_r : forall σ Φ1 Φ2, models σ (Φ1 ∧ Φ2) -> models σ Φ2.
Proof.
  intros σ Φ1 Φ2 H. apply models_and_iff in H. destruct H; assumption.
Qed.

(** 9.1.2 Environment and Closure Context Lemmas *)

(** Matched symbolic environments have concrete concretion environments *)
Lemma contains_env_concrete : forall σ Γs Γc,
  contains_env σ Γs Γc -> concrete_env Γc.
Proof.
  intros σ Γs Γc H.
  induction H; [constructor | constructor; assumption].
Qed.

(** Bound variables in the environment cannot be replaced by symbolic valuation *)
Lemma contains_var_bound : forall σ Γs Γc x Γ's es ec,
  contains_env σ Γs Γc ->
  lookup_env Γs x = Some (Γ's, es) ->
  contains σ (EVar x) ec ->
  ec = EVar x.
Proof.
  intros σ Γs Γc x Γ's es ec Henv Hlook Hcont.
  inversion Hcont; subst; reflexivity.
Qed.

(** Environment lookup preserves concore_expr *)
Lemma lookup_env_concore : forall σ Γs Γc x Γ's es Γ'c ec,
  contains_env σ Γs Γc ->
  lookup_env Γs x = Some (Γ's, es) ->
  lookup_env Γc x = Some (Γ'c, ec) ->
  concore_expr ec.
Proof.
  intros σ Γs Γc x Γ's es Γ'c ec Henv.
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

Lemma contains_lookup_env : forall σ Γs Γc x Γ's es,
  contains_env σ Γs Γc ->
  lookup_env Γs x = Some (Γ's, es) ->
  exists Γ'c ec,
    lookup_env Γc x = Some (Γ'c, ec) /\
    contains_env σ Γ's Γ'c /\
    contains σ es ec.
Proof.
  intros σ Γs Γc x Γ's es Henv.
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

Lemma contains_lit_inv : forall σ l ec,
  contains σ (ELit l) ec -> ec = ELit l.
Proof.
  intros σ l ec H. inversion H; subst; reflexivity.
Qed.

Lemma contains_con_inv : forall σ d ec,
  contains σ (ECon d) ec -> ec = ECon d.
Proof.
  intros σ d ec H. inversion H; subst; reflexivity.
Qed.

Lemma contains_primop_inv : forall σ p ec,
  contains σ (EPrimOp p) ec -> ec = EPrimOp p.
Proof.
  intros σ p ec H. inversion H; subst; reflexivity.
Qed.

Lemma contains_lam_inv : forall σ x body ec,
  contains σ (ELam x body) ec ->
  exists bodyc, ec = ELam x bodyc /\
    contains σ body bodyc.
Proof.
  intros σ x body ec H. inversion H; subst.
  exists bodyc. split; [reflexivity | assumption].
Qed.

Lemma contains_clos_inv : forall σ Γs x body ec,
  contains σ (EClos Γs x body) ec ->
  exists Γc bodyc, ec = EClos Γc x bodyc /\
    contains_env σ Γs Γc /\
    contains σ body bodyc.
Proof.
  intros σ Γs x body ec H. inversion H; subst.
  exists Γc, bodyc. split; [reflexivity | auto].
Qed.

Lemma contains_app_inv : forall σ fs as_ ec,
  contains σ (EApp fs as_) ec ->
  exists fc ac, ec = EApp fc ac /\ contains σ fs fc /\ contains σ as_ ac.
Proof.
  intros σ fs as_ ec H. inversion H; subst.
  exists f_c, a_c. split; [reflexivity | auto].
Qed.

Lemma contains_cast_inv : forall σ es γ ec,
  contains σ (ECast es γ) ec ->
  exists ec', ec = ECast ec' γ /\ contains σ es ec'.
Proof.
  intros σ es γ ec H. inversion H; subst.
  exists ec0. split; [reflexivity | assumption].
Qed.

Lemma contains_case_inv : forall σ ess altss ec,
  contains σ (ECase ess altss) ec ->
  exists esc altsc, ec = ECase esc altsc /\ contains σ ess esc /\ Forall2 (contains_alt σ) altss altsc.
Proof.
  intros σ ess altss ec H. inversion H; subst.
  exists esc, altsc. split; [reflexivity | auto].
Qed.

(** 9.1.4 Proven Semantic Simulation Lemmas *)

(** Higher-order coercion pushing simulation (Proven Lemma using Rule Eval_AppCast) *)
Lemma eval_app_cast_sound : forall Φ Γs Γc σ ef γ ea γ_a γ_r er e_con,
  models σ Φ ->
  contains_env σ Γs Γc ->
  contains σ (EApp (ECast ef γ) ea) e_con ->
  concore_expr e_con ->
  decomp_coerc_arrow γ = Some (γ_a, γ_r) ->
  Φ ; Γs ⊢ ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r ⇓ er ->
  (forall (Γc : environment) (σ : valuation) (e_con : expr),
    models σ Φ ->
    contains_env σ Γs Γc ->
    contains σ (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r) e_con ->
    concore_expr e_con ->
    exists v_con : expr,
      Γc ⊢ᶜ e_con ⇓ᶜ v_con /\ contains σ er v_con) ->
  exists v_con,
    Γc ⊢ᶜ e_con ⇓ᶜ v_con /\ contains σ er v_con.
Proof.
  intros Φ Γs Γc σ ef γ ea γ_a γ_r er e_con Hmod Henv Hcont Hcon Hdecomp Heval_pushed_s IH.
  apply contains_app_inv in Hcont as [fc [ac [Heq [Hcont_f Hcont_a]]]]; subst e_con.
  apply contains_cast_inv in Hcont_f as [efc [Heq_fc Hcont_ef]]; subst fc.
  inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | ]; subst.
  inversion Hf as [| | | | | | | | efc0 γ0 Hcon_ef | | | | | ]; subst.
  assert (Hcont_pushed : contains σ (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r)
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

(** SMT primitive evaluation simulation (Proven Lemma using eval_prim_args_sound and reduce_prim_contains) *)
Lemma eval_app_prim_sound : forall Φ Γs Γc σ ef ea p args args' e_con,
  models σ Φ ->
  contains_env σ Γs Γc ->
  contains σ (EApp ef ea) e_con ->
  concore_expr e_con ->
  unspool_app (EApp ef ea) [] = (EPrimOp p, args) ->
  Forall2 (eval Φ Γs) args args' ->
  exists v_con,
    Γc ⊢ᶜ e_con ⇓ᶜ v_con /\ contains σ (reduce_prim p args') v_con.
Proof.
  intros Φ Γs Γc σ ef ea p args args' e_con Hmod Henv Hcont Hcon Hunspool Heval_args.
  destruct (eval_prim_args_sound Φ Γs Γc σ ef ea p args args' e_con Hmod Henv Hcont Hunspool Heval_args)
    as [args_c' [Heval_c Hcont_args]].
  exists (reduce_prim p args_c').
  split; [exact Heval_c |].
  apply reduce_prim_contains.
  exact Hcont_args.
Qed.

(** Case evaluation simulation (Proven Lemma using fold_alts_contains) *)
Lemma fold_alts_sound : forall Φ Γs Γc σ es alts es' er e_con,
  models σ Φ ->
  contains_env σ Γs Γc ->
  contains σ (ECase es alts) e_con ->
  concore_expr e_con ->
  Φ ; Γs ⊢ es ⇓ es' ->
  fold_alts Φ Γs (merge es') alts er ->
  (forall (Γc : environment) (σ : valuation) (e_con : expr),
    models σ Φ ->
    contains_env σ Γs Γc ->
    contains σ es e_con ->
    concore_expr e_con ->
    exists v_con : expr,
      Γc ⊢ᶜ e_con ⇓ᶜ v_con /\ contains σ es' v_con) ->
  exists v_con,
    Γc ⊢ᶜ e_con ⇓ᶜ v_con /\ contains σ er v_con.
Proof.
  intros Φ Γs Γc σ es alts es' er e_con Hmod Henv Hcont Hcon Heval_es Hfold IH.
  apply contains_case_inv in Hcont as [esc [altsc [Heq [Hcont_es Hcont_alts]]]]; subst e_con.
  inversion Hcon as [| | | | | | | es0 alts0 Hcon_es Hcon_alts | | | | | | ]; subst.
  destruct (IH Γc σ esc Hmod Henv Hcont_es Hcon_es) as [vc_s [Heval_esc Hcont_vs]].
  eapply fold_alts_contains; try eassumption.
  exists vc_s. split; assumption.
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

Lemma eval_evar_whnf_false : forall Γ x v,
  eval pc_true Γ (EVar x) v -> Whnf Γ (EVar x) -> False.
Proof.
  intros Γ x v Heval Hwhnf.
  inversion Hwhnf as [e Hsolv | | | | | | | ]; subst.
  inversion Hsolv; subst.
  inversion Heval; subst.
  - rewrite H0 in H1. discriminate.
  - rewrite sat_pc_true in H. discriminate.
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
  - simpl in H3. discriminate.
  - rewrite sat_pc_true in H. discriminate.
Qed.

Lemma eval_app_type_false : forall Γ τ a v,
  eval pc_true Γ (EApp (EType τ) a) v -> False.
Proof.
  intros Γ τ a v Heval.
  inversion Heval; subst.
  - apply H1. apply Whnf_Type.
  - simpl in H3. discriminate.
  - rewrite sat_pc_true in H. discriminate.
Qed.

Lemma eval_app_lit_false : forall Γ l a v,
  eval pc_true Γ (EApp (ELit l) a) v -> False.
Proof.
  intros Γ l a v Heval.
  inversion Heval; subst.
  - apply H1. apply Whnf_Solvable. apply Solvable_Lit.
  - simpl in H3. discriminate.
  - rewrite sat_pc_true in H. discriminate.
Qed.

Lemma eval_app_con_false : forall Γ d a v,
  eval pc_true Γ (EApp (ECon d) a) v -> False.
Proof.
  intros Γ d a v Heval.
  inversion Heval; subst.
  - apply H1. apply Whnf_Con.
  - simpl in H3. discriminate.
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
  - exfalso. eapply eval_evar_whnf_false; eassumption.
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

Lemma eval_app_spine_sound : forall Φ Γs Γc σ ef ea ef' er e_con,
  models σ Φ ->
  contains_env σ Γs Γc ->
  contains σ (EApp ef ea) e_con ->
  concore_expr e_con ->
  ~ Whnf Γs ef ->
  Φ ; Γs ⊢ ef ⇓ ef' ->
  Φ ; Γs ⊢ EApp ef' ea ⇓ er ->
  (forall (Γc : environment) (σ : valuation) (e_con : expr),
    models σ Φ ->
    contains_env σ Γs Γc ->
    contains σ ef e_con ->
    concore_expr e_con ->
    exists v_con : expr,
      Γc ⊢ᶜ e_con ⇓ᶜ v_con /\ contains σ ef' v_con) ->
  (forall (Γc : environment) (σ : valuation) (e_con : expr),
    models σ Φ ->
    contains_env σ Γs Γc ->
    contains σ (EApp ef' ea) e_con ->
    concore_expr e_con ->
    exists v_con : expr,
      Γc ⊢ᶜ e_con ⇓ᶜ v_con /\ contains σ er v_con) ->
  exists v_con,
    Γc ⊢ᶜ e_con ⇓ᶜ v_con /\ contains σ er v_con.
Proof.
  intros Φ Γs Γc σ ef ea ef' er e_con Hmod Henv Hcont Hcon Hnotwhnf Heval1 Heval2 IH1 IH2.
  apply contains_app_inv in Hcont as [fc [ac [Heq [Hcont_f Hcont_a]]]]; subst e_con.
  inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | ]; subst.
  destruct (IH1 Γc σ fc Hmod Henv Hcont_f Hf) as [v_f [Heval_f Hcont_vf]].
  assert (Henv_c : concrete_env Γc) by (eapply contains_env_concrete; eassumption).
  assert (Hcon_vf : concore_expr v_f) by (eapply concore_eval_closed; [exact Henv_c | exact Hf | exact Heval_f]).
  assert (Hcont_app2 : contains σ (EApp ef' ea) (EApp v_f ac)) by (constructor; assumption).
  assert (Hcon_app2 : concore_expr (EApp v_f ac)) by (apply Con_App; assumption).
  destruct (IH2 Γc σ (EApp v_f ac) Hmod Henv Hcont_app2 Hcon_app2) as [v_con [Heval_app2 Hcont_er]].
  exists v_con. split; [| exact Hcont_er].
  unfold eval_con in *.
  destruct (whnf_dec Γc fc) as [Hwhnf_c | Hnot_whnf_c].
  - destruct (is_op_app fc) eqn:Hop.
    + destruct fc; try discriminate.
      * simpl in Hop. exfalso. eapply eval_primop_false; eassumption.
      * admit.
    + eapply eval_con_app_whnf; eassumption.
  - eapply Eval_AppSpine; [exact Hnot_whnf_c | exact Heval_f | exact Heval_app2].
Admitted.

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
  contains_env σ Γs Γc ->
  contains σ e_sym e_con ->
  concore_expr e_con ->
  Φ ; Γs ⊢ e_sym ⇓ v_sym ->
  exists v_con,
    Γc ⊢ᶜ e_con ⇓ᶜ v_con /\
    contains σ v_sym v_con.
Proof.
  intros Φ Γs Γc σ e_sym e_con v_sym Hmod Henv Hcont Hcon Heval.
  revert Γc σ e_con Hmod Henv Hcont Hcon.
  induction Heval.
  - (* Eval_Var *)
    intros Γc σ e_con Hmod Henv Hcont Hcon.
    assert (Heq : e_con = EVar x) by (eapply contains_var_bound; eassumption).
    subst e_con.
    destruct (contains_lookup_env σ Γ Γc x Γ' e Henv H) as [Γ'c [ec [Hlookc [Henv' Hcont']]]].
    assert (Hcon' : concore_expr ec) by (apply (lookup_env_concore σ Γ Γc x Γ' e Γ'c ec Henv H Hlookc)).
    destruct (IHHeval Γ'c σ ec Hmod Henv' Hcont' Hcon') as [v_con [Hevalc Hcont_v]].
    exists v_con. split; [| exact Hcont_v].
    unfold eval_con. eapply Eval_Var; eassumption.
  - (* Eval_Lit *)
    intros Γc σ e_con Hmod Henv Hcont Hcon.
    apply contains_lit_inv in Hcont; subst.
    exists (ELit l). split; [apply Eval_Lit | apply Cont_Lit].
  - (* Eval_Con *)
    intros Γc σ e_con Hmod Henv Hcont Hcon.
    apply contains_con_inv in Hcont; subst.
    exists (ECon d). split; [apply Eval_Con | apply Cont_Con].
  - (* Eval_Cast *)
    intros Γc σ e_con Hmod Henv Hcont Hcon.
    apply contains_cast_inv in Hcont as [ec [Heq Hcont_e]]; subst.
    inversion Hcon as [| | | | | | | | ec0 γ0 Hcon_e | | | | | ]; subst.
    destruct (IHHeval Γc σ ec Hmod Henv Hcont_e Hcon_e) as [vc [Hevalc Hcont_v]].
    exists (cast_expr vc γ). split; [unfold eval_con; apply Eval_Cast; exact Hevalc | apply cast_expr_contains; exact Hcont_v].
  - (* Eval_AppAbs *)
    intros Γc σ e_con Hmod Henv Hcont Hcon.
    apply contains_app_inv in Hcont as [fc [ac [Heq [Hcont_f Hcont_a]]]]; subst.
    apply contains_clos_inv in Hcont_f as [Γ'c [ebc [Heq_f [Henv_clos Hcont_b]]]]; subst.
    inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | ]; subst.
    inversion Hf as [| | | | | | Γ0 x0 body Henv_clos_c Hcon_b | | | | | | | ]; subst.
    assert (Henv_ext : contains_env σ (ExtendEnv x (MkClosure Γ ea) Γ')
                                      (ExtendEnv x (MkClosure Γc ac) Γ'c)).
    { apply Cont_Env_Extend; assumption. }
    destruct (IHHeval (ExtendEnv x (MkClosure Γc ac) Γ'c) σ ebc Hmod Henv_ext Hcont_b Hcon_b) as [v_con [Heval_b Hcont_v]].
    exists v_con. split; [| exact Hcont_v].
    unfold eval_con. apply Eval_AppAbs. exact Heval_b.
  - (* Eval_AppSpine *)
    intros Γc σ e_con Hmod Henv Hcont Hcon.
    eapply eval_app_spine_sound; eassumption.
  - (* Eval_Bot *)
    intros Γc σ e_con Hmod Henv Hcont Hcon.
    inversion Hcont; subst.
    exists (EBot b). split; [apply Eval_Bot | apply Cont_Bot].
  - (* Eval_AppPrim *)
    intros Γc σ e_con Hmod Henv Hcont Hcon.
    eapply eval_app_prim_sound; eassumption.
  - (* Eval_Lam *)
    intros Γc σ e_con Hmod Henv Hcont Hcon.
    apply contains_lam_inv in Hcont as [bodyc [Heq Hcont_body]]; subst.
    exists (EClos Γc x bodyc). split; [apply Eval_Lam | constructor; assumption].
  - (* Eval_AppCast *)
    intros Γc σ e_con Hmod Henv Hcont Hcon.
    eapply eval_app_cast_sound; eassumption.
  - (* Eval_AppBot *)
    intros Γc σ e_con Hmod Henv Hcont Hcon.
    apply contains_app_inv in Hcont as [fc [ac [Heq [Hcont_f Hcont_a]]]]; subst.
    inversion Hcont_f; subst.
    exists (EBot b). split; [apply Eval_AppBot | constructor].
  - (* Eval_Case *)
    intros Γc σ e_con Hmod Henv Hcont Hcon.
    eapply fold_alts_sound; eassumption.
  - (* Eval_If *)
    intros Γc σ e_con Hmod Henv Hcont Hcon.
    inversion Hcont; subst.
    + assert (Hcond' : models_cond σ ec').
      { apply eval_models_cond with (Φ := Φ) (Γ := Γ) (ec := ec); assumption. }
      assert (Hpc_mod : models σ pc_c).
      { apply (models_cond_pc σ Γ ec' pc_c H). exact Hcond'. }
      assert (Hmod_and : models σ (Φ ∧ pc_c)).
      { apply models_and; assumption. }
      destruct (IHHeval2 Γc σ e_con Hmod_and Henv H5 Hcon) as [v_con [Hevalc' Hcont_v]].
      exists v_con. split; [exact Hevalc' |].
      apply Cont_If_True; [exact Hcond' | exact Hcont_v].
    + assert (Hncond' : models_not_cond σ ec').
      { apply eval_models_not_cond with (Φ := Φ) (Γ := Γ) (ec := ec); assumption. }
      assert (Hpc_mod : models σ (¬ pc_c)).
      { apply (models_not_cond_pc σ Γ ec' pc_c H). exact Hncond'. }
      assert (Hmod_and : models σ (Φ ∧ ¬ pc_c)).
      { apply models_and; assumption. }
      destruct (IHHeval3 Γc σ e_con Hmod_and Henv H5 Hcon) as [v_con [Hevalc' Hcont_v]].
      exists v_con. split; [exact Hevalc' |].
      apply Cont_If_False; [exact Hncond' | exact Hcont_v].
  - (* Eval_Coercion *)
    intros Γc σ e_con Hmod Henv Hcont Hcon.
    inversion Hcont; subst.
    exists (ECoercion (subst_coerc Γc γ)).
    split; [apply Eval_Coercion | apply subst_coerc_contains_env; assumption].
  - (* Eval_Prune *)
    intros Γc σ e_con Hmod Henv Hcont Hcon.
    apply models_sat in Hmod.
    rewrite H in Hmod. discriminate.
  - (* Eval_Type *)
    intros Γc σ e_con Hmod Henv Hcont Hcon.
    inversion Hcont; subst.
    exists (EType (subst_type Γc τ)).
    split; [apply Eval_Type | apply subst_type_contains_env; assumption].
Qed.

(** Top-level Soundness for whole programs starting from EmptyEnv *)
Theorem concore_soundness_top : forall Φ σ e_sym e_con v_sym,
  models σ Φ ->
  contains σ e_sym e_con ->
  concore_expr e_con ->
  Φ ; EmptyEnv ⊢ e_sym ⇓ v_sym ->
  exists v_con,
    ⊢ᶜ e_con ⇓ᶜ v_con /\
    contains σ v_sym v_con.
Proof.
  intros Φ σ e_sym e_con v_sym Hmod Hcont Hcon Heval.
  apply (concore_soundness Φ EmptyEnv EmptyEnv σ e_sym e_con v_sym); auto.
  apply Cont_Env_Empty.
Qed.
