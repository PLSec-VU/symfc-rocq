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
From Stdlib Require Import Arith.PeanoNat.
Import ListNotations.

(** ========================================================================= *)
(** 1. Syntactic Restriction: ConCore as an Inductive Subset of SymCore       *)
(** ========================================================================= *)

(** ConCore expressions: System FC syntax with runtime closures and thunks,
    but strictly excluding symbolic branching (EIf). *)
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
  | Con_Thunk : forall Γ e, concrete_env Γ -> concore_expr e -> concore_expr (EThunk Γ e)

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
    excluding runtime closures (EClos), runtime thunks (EThunk) and symbolic
    branching (EIf). *)
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
  SymCore treats a variable that Γ does not bind as an uninterpreted symbolic
  variable (Axiom Solvable_Var). ConCore requires every variable an expression
  reads to be bound, so no symbolic variable is left.
*)

Definition is_concrete_var (Γ : environment) (x : var) : Prop :=
  exists Γ' e, lookup_env Γ x = Some (Γ', e).

Definition concrete_context (Γ : environment) (e : expr) : Prop :=
  forall x, In x (fv e) -> is_concrete_var Γ x.

Definition closed_expr (e : expr) : Prop :=
  forall x, ~ In x (fv e).

(** Note: concrete_env is defined mutually with concore_expr in Section 1. *)

(** ========================================================================= *)
(** 7. Properties of Concrete Contexts                                         *)
(** ========================================================================= *)

Lemma sym_var_not_concrete_context : forall Γ x,
  lookup_env Γ x = None ->
  ~ concrete_context Γ (EVar x).
Proof.
  intros Γ x Hlookup Hctx.
  unfold concrete_context, is_concrete_var in Hctx.
  destruct (Hctx x (or_introl eq_refl)) as [Γ' [e Heq]].
  rewrite Hlookup in Heq. discriminate.
Qed.

Lemma bound_var_concrete_context : forall Γ x Γ' e,
  lookup_env Γ x = Some (Γ', e) ->
  concrete_context Γ (EVar x).
Proof.
  intros Γ x Γ' e Hlookup y [Heq | Hfalse].
  - subst. exists Γ', e. assumption.
  - contradiction.
Qed.

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

Lemma concrete_context_cast : forall Γ e γ,
  concrete_context Γ (ECast e γ) <-> concrete_context Γ e.
Proof.
  intros Γ e γ. unfold concrete_context. simpl. reflexivity.
Qed.

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

Lemma is_concrete_var_extend_self : forall Γ x Γ' e,
  is_concrete_var (extend_env Γ x Γ' e) x.
Proof.
  intros Γ x Γ' e. unfold is_concrete_var, extend_env. simpl.
  destruct (string_dec x x) as [_ | Hneq].
  - exists Γ', e. reflexivity.
  - exfalso. apply Hneq. reflexivity.
Qed.

Lemma in_remove_helper : forall x y l,
  In y l -> y <> x -> In y (remove string_dec x l).
Proof.
  intros x y l. induction l as [| a tl IH]; intros Hin Hneq; [inversion Hin |].
  simpl. destruct (string_dec x a).
  - subst. destruct Hin; [subst; contradiction | auto].
  - destruct Hin; [subst; left; reflexivity | right; auto].
Qed.

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

Definition eval_con (Γ : environment) (e : expr) (v : expr) : Prop :=
  eval Inf pc_true Γ e v.

Notation "Γ '⊢ᶜ' e '⇓ᶜ' v" := (eval_con Γ e v) (at level 70, no associativity).
Notation "'⊢ᶜ' e '⇓ᶜ' v" := (eval_con · e v) (at level 70, no associativity).

(** ------------------------------------------------------------------------- *)
(** 8.1 SMT & Grisette Solver Behaviors for Concrete Evaluation               *)
(** ------------------------------------------------------------------------- *)

(**
  The theory solver, state merging and coercion casts are external to this
  development. The three assumptions below say that none of them introduces a
  symbolic branch, so a ConCore term stays in ConCore.

  Primitive reduction stays inside ConCore only WHEN ITS ARGUMENTS DO.
  concore_expr excludes EIf, so an unconditional version would say the theory
  solver never returns a branch, not even when an argument is itself a branch.
*)
Axiom reduce_prim_concore : forall p args,
  Forall concore_expr args ->
  concore_expr (reduce_prim p args).

(**
  State merging does nothing to a concrete term.

  This used to be an assumption about Grisette. It is now a one-line
  consequence of the definition: merge only ever changes a branch, and
  concore_expr has no branch, so merge hands a ConCore term straight back.
*)
Lemma concore_not_if : forall e, concore_expr e -> is_if e = false.
Proof.
  intros e H. destruct e; try reflexivity.
  exfalso. exact (not_concore_if _ _ _ H).
Qed.

Lemma merge_concore_id : forall Γ e, concore_expr e -> merge Γ e = e.
Proof.
  intros Γ e H. apply merge_not_if. apply concore_not_if. exact H.
Qed.

Lemma merge_concore : forall Γ e,
  concore_expr e ->
  concore_expr (merge Γ e).
Proof.
  intros Γ e H. rewrite (merge_concore_id Γ e H). exact H.
Qed.

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
    + simpl. apply concrete_env_extend; [apply IH; auto | assumption | constructor].
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

Lemma concore_fold_left_app : forall args h,
  Forall concore_expr args ->
  concore_expr h ->
  concore_expr (fold_left EApp args h).
Proof.
  induction args as [| a tl IH]; intros h Hargs Hh; simpl; [exact Hh |].
  inversion Hargs; subst. apply IH; [assumption | apply Con_App; assumption].
Qed.

Lemma concore_con_value : forall Γ d args,
  concrete_env Γ ->
  Forall concore_expr args ->
  concore_expr (make_con_app d (map (EThunk Γ) args)).
Proof.
  intros Γ d args HΓ Hargs. apply concore_fold_left_app; [| apply Con_Con].
  induction Hargs; simpl; constructor; [apply Con_Thunk |]; assumption.
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
  A pair of mutually recursive fixpoints, not the auto-derived mutual
  induction scheme. Rule App-Prim needs the statement for every argument of
  its Forall2 (eval (dec f) Φ Γ) args args' in order to feed the
  argument-conditional reduce_prim_concore, and the derived scheme supplies no
  induction hypothesis under a Forall2.

  The statement holds at every fuel, so it takes the fuel as a parameter and
  asks nothing of it. Rule Out-Of-Fuel answers EBot BUndefined, which is a
  ConCore expression.
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
    | k Φ Γ econ d args Hunspool_con
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
    | k Φ Γ Γ' e e' Heval_t
    | Φ Γ e
    ]; intros Hsat Henv Hcon.
  - (* Eval_Var *)
    destruct (lookup_env_concrete Γ x Γ' e Henv Hlook) as [Henv' He].
    exact (concore_eval_closed_fix (dec k) Φ Γ' e e' Heval_x Hsat Henv' He).
  - (* Eval_SymVar *) exact Hcon.
  - (* Eval_Lit *) constructor.
  - (* Eval_Con *)
    apply concore_con_value; [exact Henv |].
    exact (proj2 (unspool_app_concore econ [] (ECon d) args Hunspool_con Hcon (Forall_nil _))).
  - (* Eval_Cast *)
    apply cast_expr_concore.
    apply (concore_eval_closed_fix (dec k) Φ Γ e e' Heval_e Hsat Henv).
    inversion Hcon; subst; assumption.
  - (* Eval_AppAbs *)
    inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | | ]; subst.
    inversion Hf as [| | | | | | Γ0 x0 body Henv' Hbody | | | | | | | | ]; subst.
    apply (concore_eval_closed_fix (dec k) Φ (extend_env Γ' x Γ ea) eb eb' Heval_b Hsat).
    + apply concrete_env_extend; assumption.
    + assumption.
  - (* Eval_AppSpine *)
    inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | | ]; subst.
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
    inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | | ]; subst.
    inversion Hf as [| | | | | | | | e γ0 He | | | | | | ]; subst.
    apply (concore_eval_closed_fix (dec k) Φ Γ (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r)
             er Heval_pushed Hsat Henv).
    apply Con_Cast. apply Con_App; [assumption | apply Con_Cast; assumption].
  - (* Eval_AppBot *)
    inversion Hcon; subst. assumption.
  - (* Eval_Case *)
    inversion Hcon as [| | | | | | | es0 alts0 Hcon_es Hcon_alts | | | | | | | ]; subst.
    apply (concore_fold_closed_fix (dec k) Φ Γ (merge Γ es') alts er Hfold Hsat Henv);
      [| assumption].
    apply merge_concore.
    exact (concore_eval_closed_fix (dec k) Φ Γ es es' Heval_es Hsat Henv Hcon_es).
  - (* Eval_If *)
    exfalso. apply (not_concore_if ec et ef). assumption.
  - (* Eval_Coercion *) constructor.
  - (* Eval_Prune *) constructor.
  - (* Eval_Type *) constructor.
  - (* Eval_Thunk *)
    inversion Hcon as [| | | | | | | | | | | | | | Γ0 e0 Henv' He]; subst.
    exact (concore_eval_closed_fix (dec k) Φ Γ' e e' Heval_t Hsat Henv' He).
  - (* Eval_OutOfFuel *) constructor.
}
{
  destruct Hfold as
    [ k Φ Γ ec et ef alts et' ef' pc_c Hpc Hfold_t Hfold_f
    | k Φ Γ ec et ef alts Hpc_none
    | k Φ Γ e d ea xs ep alts er Hdec Halt Heval_ep
    | k Φ Γ b alts
    | k Φ Γ e alts Hnothead Hnoalt Hnotbot
    ]; intros Hsat Henv Hcon Halts.
  - exfalso. apply (not_concore_if ec et ef). assumption.
  - exfalso. apply (not_concore_if ec et ef). assumption.
  - (* FoldAlts_Con *)
    assert (Hea : Forall concore_expr ea).
    { apply decompose_con_app_concore with (e := e) (d := d); assumption. }
    assert (Hep : concore_expr ep).
    { apply find_alt_concore with (d := d) (alts := alts) (xs := xs); assumption. }
    apply (concore_eval_closed_fix k Φ (extend_env_multi Γ xs ea Γ) ep er Heval_ep Hsat);
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

Corollary concore_eval_closed_top : forall e v,
  concore_expr e ->
  ⊢ᶜ e ⇓ᶜ v ->
  concore_expr v.
Proof.
  intros e v Hcon Heval.
  apply (concore_eval_closed · e v); auto.
  constructor.
Qed.

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

Definition valuation : Type := var -> lit.

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
  statement needs no extra hypothesis of its own.
*)
Definition symvars : Type := var -> bool.

(** An environment respects S when it binds no symbolic variable. Derivable
    from contains_env (see contains_env_sym_free), never assumed. *)
Definition sym_free_env (S : symvars) (Γ : environment) : Prop :=
  forall x, S x = true -> lookup_env Γ x = None.

Lemma sym_free_env_empty : forall S, sym_free_env S ·.
Proof. intros S x _. reflexivity. Qed.

(** ------------------------------------------------------------------------- *)
(** 9.0 The SMT Value of a Formula                                            *)
(** ------------------------------------------------------------------------- *)

(**
  The SMT theory's own reading of a primitive operation: the literal the
  solver gives to that operation applied to literal arguments. It is external
  to this development in exactly the way lit and primop already are.
*)
Parameter prim_value : primop -> list lit -> lit.

(** The literal the SMT theory reads as truth. External in the same way. *)
Parameter lit_true : lit.

Fixpoint pc_value (σ : valuation) (pc : path_condition) : lit :=
  match pc with
  | PCVar x => σ x
  | PCLit l => l
  | PCPrim p args => prim_value p (map (pc_value σ) args)
  end.

(**
  A model satisfies a formula exactly when the formula's SMT value under that
  model is the true literal.

  A path condition had two independent readings here while `models` was a
  Parameter: the verdict (⊨) and the value (pc_value), with nothing tying
  them together. Symbolic evaluation preserves the value - that is
  eval_denote in Section 9.2 - so a verdict that did not follow the value
  could not be transported across an evaluation step, and eval_models_cond
  and eval_models_not_cond had to be assumed. Reading the verdict off the
  value closes that gap: both are now lemmas (Section 9.2), and what is
  assumed instead is prim_value_and below, one equation about how the solver
  reads its own conjunction.
*)
Definition models (σ : valuation) (Φ : path_condition) : Prop :=
  pc_value σ Φ = lit_true.

Notation "σ '⊨' Φ" := (models σ Φ) (at level 70, no associativity).

(** `sat` reports satisfiability, so a formula with a model is satisfiable.
    This is the one fact left relating the model to the `sat` oracle, and it
    stays assumed: `sat` is the solver and nothing here computes it. *)
Axiom models_sat : forall σ Φ,
  σ ⊨ Φ -> sat Φ = true.

(** The SMT theory reads op_and as conjunction against the true literal. *)
Axiom prim_value_and : forall l1 l2,
  prim_value op_and (l1 :: l2 :: nil) = lit_true <-> l1 = lit_true /\ l2 = lit_true.

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
  the note on eval_models_cond in Section 9.2.
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

(** This is what rules out every evaluation rule except App-Prim in
    eval_models_cond_residue below. *)
Lemma models_cond_solvable : forall σ S Γ e,
  sym_free_env S Γ -> models_cond σ S e \/ models_not_cond σ S e -> Solvable Γ e.
Proof.
  intros σ S Γ e Hfree Hj.
  destruct (models_cond_total σ S Γ e Hfree Hj) as [pc Hpc].
  eapply expr_to_pc_solvable. exact Hpc.
Qed.

(** ------------------------------------------------------------------------- *)
(** 9.0.1 The SMT Value of a Term                                             *)
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
  | Cont_Clos : forall Γs Γc x bodys bodyc,
      S x = false ->
      contains_env σ S Γs Γc ->
      contains σ S bodys bodyc ->
      contains σ S (EClos Γs x bodys) (EClos Γc x bodyc)
  | Cont_Thunk : forall Γs Γc es ec,
      contains_env σ S Γs Γc ->
      contains σ S es ec ->
      contains σ S (EThunk Γs es) (EThunk Γc ec)
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

Ltac kill_denote :=
  match goal with
  | [ Hun : unspool_app ?e (@nil expr) = (EPrimOp _, _),
      Hg : smt_ground ?e = false |- _ ] =>
      destruct (cont_denote_is_app e _ _ Hun Hg) as [? [? ?]]; discriminate
  end.

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
  value. This is the correctness statement for the external reducer, and it is
  what lets the reducer COMPUTE. Without it, a reduced term could stay related
  to its concrete counterpart only by being syntactically the same term, so
  reduce_prim would be forced never to compute.
*)
Axiom reduce_prim_denote : forall σ S p args ls,
  Forall2 (denote σ S) args ls ->
  denote σ S (reduce_prim p args) (prim_value p ls).

(**
  SMT solver behavior: when the reducer's answer mentions no variable, it is
  a value. A closed SMT term is a number the solver already knows, and a
  reducer that returned an unevaluated closed application would simply have
  stopped early.
*)
Axiom reduce_prim_ground_value : forall p args,
  smt_ground (reduce_prim p args) = true ->
  exists l, reduce_prim p args = ELit l.

(**
  SMT solver behaviour: the solver's if-then-else term has the instances the
  evaluator's branch has.

  READ THIS ONE CAREFULLY - it is the only assumption merge adds.

  Section 3.3's second merge clause replaces a branch between two solvable
  arms by reduce_prim op_ite [ec; et; ef], an SMT term. From that point the
  branch is the solver's to resolve, and nothing else in this development can
  say what the solver does with it: reduce_prim is opaque, and neither
  reduce_prim_contains (which relates a reduced term to the reduction of its
  concrete arguments) nor reduce_prim_denote (which is about SMT values) says
  anything about a term the model must resolve to one arm.

  So this is a statement about reduce_prim at op_ite, not a statement about
  merge: whatever the reducer builds from a condition and two arms, a model
  reads it the way it reads a branch. A solver whose ite disagreed with the
  evaluator's branch would be a wrong solver. Merge is what makes the
  question come up; it is not what the assumption is about.
*)
Axiom reduce_prim_ite_contains : forall σ S ec et ef e_c,
  contains σ S (EIf ec et ef) e_c ->
  contains σ S (reduce_prim op_ite (ec :: et :: ef :: nil)) e_c.

(** Grisette state merging soundness (Lemma A.4 in the paper) is now the
    lemma merge_contains in Section 9.3, proved from the definition of merge. *)

(** Coercion cast simplification preserves concretion (Lemma A.5 in the paper) *)
Axiom cast_expr_contains : forall σ S es ec γ,
  contains σ S es ec ->
  contains σ S (cast_expr es γ) (cast_expr ec γ).

(**
  Taking apart a derivation that is fixed at the unlimited budget.

  `inversion` on a hypothesis of the form eval Inf ... already drops Rule
  Out-Of-Fuel, because that rule writes Spent in its conclusion and Spent
  cannot unify with Inf. `destruct` and `induction` do not: they first
  generalise the fuel index into a variable, so Rule Out-Of-Fuel comes back as
  a case and every recursive premise arrives at dec f instead of Inf.

  The two tactics below keep the index. They name it, remember the equation
  that says the name is Inf, use that equation to kill the out-of-fuel case,
  and inject it to fix f at Unlimited in every other case. Use them for any
  lemma that is true only at the unlimited budget.
*)
Ltac inf_induction H :=
  let k := fresh "kf" in
  let Hk := fresh "Hkf" in
  remember Inf as k eqn:Hk in H;
  induction H; try discriminate Hk; try (injection Hk as Hk); subst.

Ltac inf_destruct H :=
  let k := fresh "kf" in
  let Hk := fresh "Hkf" in
  remember Inf as k eqn:Hk in H;
  revert Hk; destruct H; intro Hk; try discriminate Hk; try (injection Hk as Hk); subst.

(** Every rule other than App-Prim is excluded here, by solvability or by Rule
    Prune being unreachable under a model.

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
  - exfalso. apply unspool_is_con_app in H.
    rewrite (solvable_not_con_app Γ e Hsolv) in H. discriminate.
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

Lemma contains_env_concrete : forall σ S Γs Γc,
  contains_env σ S Γs Γc -> concrete_env Γc.
Proof.
  intros σ S Γs Γc H.
  induction H; [constructor | constructor; assumption].
Qed.

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

(** This is what makes the theorem say something about genuinely symbolic
    programs. *)
Lemma contains_var_sym : forall σ S x ec,
  S x = true ->
  contains σ S (EVar x) ec ->
  ec = ELit (σ x).
Proof.
  intros σ S x ec Hsym Hcont.
  inversion Hcont; subst; [congruence | congruence | kill_denote].
Qed.

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
  An application is the one shape Cont_Denote can also produce, so the
  inversion is a disjunction. The second alternative carries Solvable Γ fs,
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
  inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | | ]; subst.
  inversion Hf as [| | | | | | | | efc0 γ0 Hcon_ef | | | | | | ]; subst.
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
  - no_con_head.
  - rewrite sat_pc_true in H0. discriminate.
Qed.

Lemma eval_con_con : forall Γ d v,
  eval Inf pc_true Γ (ECon d) v -> v = ECon d.
Proof.
  intros Γ d v Heval. exact (eval_con_same pc_true Γ d v sat_pc_true Heval).
Qed.

Lemma eval_bot_con : forall Γ b v,
  eval Inf pc_true Γ (EBot b) v -> v = EBot b.
Proof.
  intros Γ b v Heval.
  inversion Heval; subst.
  - no_con_head.
  - reflexivity.
  - rewrite sat_pc_true in H0. discriminate.
Qed.

Lemma eval_clos_false : forall Γ env x body v,
  eval Inf pc_true Γ (EClos env x body) v -> False.
Proof.
  intros Γ env x body v Heval.
  inversion Heval; subst.
  - no_con_head.
  - rewrite sat_pc_true in H0. discriminate.
Qed.

(** A variable in WHNF is unbound, hence symbolic, hence its own value. Rule
    Sym-Var is what gives it that value. *)
Lemma eval_evar_whnf_same : forall Γ x v,
  eval Inf pc_true Γ (EVar x) v -> Whnf Γ (EVar x) -> v = EVar x.
Proof.
  intros Γ x v Heval Hwhnf.
  inversion Hwhnf as [e Hsolv | | | | | | | ]; subst; [| no_con_head].
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
  - no_con_head.
  - rewrite sat_pc_true in H0. discriminate.
Qed.

Lemma eval_coercion_con : forall Γ γ v,
  eval Inf pc_true Γ (ECoercion γ) v -> v = ECoercion (subst_coerc Γ γ).
Proof.
  intros Γ γ v Heval.
  inversion Heval; subst.
  - no_con_head.
  - reflexivity.
  - rewrite sat_pc_true in H0. discriminate.
Qed.

Lemma eval_type_con : forall Γ τ v,
  eval Inf pc_true Γ (EType τ) v -> v = EType (subst_type Γ τ).
Proof.
  intros Γ τ v Heval.
  inversion Heval; subst.
  - no_con_head.
  - rewrite sat_pc_true in H0. discriminate.
  - reflexivity.
Qed.

Lemma eval_app_coercion_false : forall Γ γ a v,
  eval Inf pc_true Γ (EApp (ECoercion γ) a) v -> False.
Proof.
  intros Γ γ a v Heval.
  inversion Heval; subst.
  - no_con_head.
  - apply H2. apply Whnf_Coercion.
  - match goal with
    | [ H : unspool_app (EApp _ _) [] = _ |- _ ] =>
        simpl in H; discriminate
    end.
  - rewrite sat_pc_true in H0. discriminate.
Qed.

Lemma eval_app_type_false : forall Γ τ a v,
  eval Inf pc_true Γ (EApp (EType τ) a) v -> False.
Proof.
  intros Γ τ a v Heval.
  inversion Heval; subst.
  - no_con_head.
  - apply H2. apply Whnf_Type.
  - match goal with
    | [ H : unspool_app (EApp _ _) [] = _ |- _ ] =>
        simpl in H; discriminate
    end.
  - rewrite sat_pc_true in H0. discriminate.
Qed.

Lemma eval_app_lit_false : forall Γ l a v,
  eval Inf pc_true Γ (EApp (ELit l) a) v -> False.
Proof.
  intros Γ l a v Heval.
  inversion Heval; subst.
  - no_con_head.
  - apply H2. apply Whnf_Solvable. apply Solvable_Lit.
  - match goal with
    | [ H : unspool_app (EApp _ _) [] = _ |- _ ] =>
        simpl in H; discriminate
    end.
  - rewrite sat_pc_true in H0. discriminate.
Qed.

Lemma not_whnf_case : forall Γ es alts,
  ~ Whnf Γ (ECase es alts).
Proof.
  intros Γ es alts Hw.
  inversion Hw; subst; [| no_con_head].
  match goal with [ Hs : Solvable _ _ |- _ ] => inversion Hs end.
Qed.

(** An application is a value only when its spine head is a primitive
    operation or a data constructor. *)
Lemma not_op_app_not_whnf : forall Γ f a,
  is_op_app (EApp f a) = false ->
  is_con_app (EApp f a) = false ->
  ~ Whnf Γ (EApp f a).
Proof.
  intros Γ f a Hnop Hncon Hw.
  inversion Hw as [e Hsolv | e d args Hu | | | | | | ]; subst.
  - inversion Hsolv as [| | | f' a' Hop Hsf Hsa]; subst.
    rewrite Hop in Hnop. discriminate.
  - apply unspool_is_con_app in Hu. rewrite Hu in Hncon. discriminate.
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
  inversion Heval; subst; [no_con_head | reflexivity | rewrite Hsat in *; discriminate].
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
  - (* Eval_Con: a branch in operator position is not a constructor head *)
    subst. destruct f0; try discriminate Hif.
    match goal with
    | [ Hu : unspool_app _ _ = (ECon _, _) |- _ ] => simpl in Hu; discriminate Hu
    end.
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

Lemma unspool_app_head_of_app : forall e a,
  fst (unspool_app (EApp e a) []) = fst (unspool_app e []).
Proof.
  intros e a. simpl. destruct (unspool_app e []) as [h args] eqn:Hu.
  pose proof (unspool_app_shift e [] [a] h args Hu) as Hshift. simpl in Hshift.
  rewrite Hshift. reflexivity.
Qed.

Lemma eval_spine_if_head_false : forall Φ Γ e v,
  Φ ; Γ ⊢ e ⇓ v ->
  sat Φ = true ->
  is_if e = false ->
  is_if (fst (unspool_app e [])) = true ->
  False.
Proof.
  intros Φ Γ e v Heval. inf_induction Heval; intros Hsat Hnif Hhead;
    try (simpl in Hhead; discriminate Hhead).
  - match goal with
    | [ Hu : unspool_app _ [] = (ECon _, _) |- _ ] => rewrite Hu in Hhead; discriminate Hhead
    end.
  - rewrite unspool_app_head_of_app in Hhead.
    destruct (is_if ef) eqn:Hif.
    + apply (IHHeval2 eq_refl Hsat eq_refl).
      rewrite unspool_app_head_of_app.
      pose proof (eval_preserves_if Φ Γ ef ef' Heval1 Hsat Hif) as Hif'.
      destruct ef'; try discriminate Hif'. reflexivity.
    + exact (IHHeval1 eq_refl Hsat eq_refl Hhead).
  - match goal with
    | [ Hu : unspool_app _ [] = (EPrimOp _, _) |- _ ] => rewrite Hu in Hhead; discriminate Hhead
    end.
  - discriminate Hnif.
  - congruence.
Qed.

Lemma contains_con_app_origin : forall σ S es ec,
  contains σ S es ec ->
  is_con_app ec = true ->
  is_con_app es = true \/ is_if (fst (unspool_app es [])) = true.
Proof.
  induction 1; intros Hc; simpl in Hc; try discriminate Hc.
  - left. reflexivity.
  - rewrite unspool_app_head_of_app.
    destruct (IHcontains1 Hc) as [Hs | Hs]; [left | right]; exact Hs.
  - right. reflexivity.
  - right. reflexivity.
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
  is_con_app fc = false ->
  is_cast fc = false ->
  pc_true ; Γc ⊢ fc ⇓ v_f ->
  pc_true ; Γc ⊢ EApp v_f ac ⇓ v_con ->
  pc_true ; Γc ⊢ EApp fc ac ⇓ v_con.
Proof.
  intros Γc fc ac v_f v_con Hcon Hwhnf Hnop Hncon Hnocast Heval_f Heval_app.
  destruct fc.
  - assert (Heqv : v_f = EVar v) by (eapply eval_evar_whnf_same; eassumption).
    subst v_f. exact Heval_app.
  - apply eval_lit_con in Heval_f; subst.
    exfalso. apply (eval_app_lit_false _ _ _ _ Heval_app).
  - exfalso. eapply eval_primop_false; eassumption.
  - discriminate Hncon.
  - exfalso. apply (not_op_app_not_whnf Γc fc1 fc2 Hnop Hncon Hwhnf).
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
  - exfalso. exact (not_whnf_thunk _ _ _ Hwhnf).
Qed.

Lemma whnf_op_app_solvable : forall Γ f a,
  is_op_app (EApp f a) = true ->
  Whnf Γ (EApp f a) -> Solvable Γ (EApp f a).
Proof.
  intros Γ f a Hop Hwhnf.
  inversion Hwhnf as [e Hsolv | e d args Hu | | | | | | ]; subst.
  - exact Hsolv.
  - exfalso. apply unspool_is_con_app in Hu.
    rewrite (op_app_not_con_app _ Hop) in Hu. discriminate.
Qed.

(**
  A saturated operator spine reduces by Rule App-Prim, and its reduced
  arguments are still solvable. The second conjunct is what feeds the
  argument-conditional reduce_prim_solvable.
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
  - (* Eval_Con: an operator spine has no constructor head *)
    exfalso.
    match goal with
    | [ Hu : unspool_app _ _ = (ECon _, _) |- _ ] =>
        apply unspool_is_con_app in Hu;
        rewrite (op_app_not_con_app _ Hop) in Hu; discriminate
    end.
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
  - rewrite Hsat in H0. discriminate.
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
  inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | | ]; subst.
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
    + assert (Hncon_c : is_con_app fc = false).
      { destruct (is_con_app fc) eqn:Hc; [exfalso | reflexivity].
        destruct (contains_con_app_origin σ S ef fc Hcont_f Hc) as [Hcs | Hhead].
        - apply Hnotwhnf. destruct (is_con_app_unspool ef Hcs) as [d [args Hu]].
          exact (Whnf_Con Γs ef d args Hu).
        - exact (eval_spine_if_head_false Φ Γs ef ef' Heval1 Hsat Hnotif Hhead). }
      eapply eval_con_app_whnf; eassumption.
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
  Symbolic evaluation of an SMT term preserves its SMT value. Every rule
  except App-Prim is excluded by the shape of a denoting term, or, for Rule
  Prune, by the model of the path condition. App-Prim is reduce_prim_denote
  applied to arguments the recursion has already handled.

  It is a Fixpoint rather than an induction because App-Prim needs the result
  for every argument in its Forall2, which Coq's derived induction principle
  does not strengthen.

  Unlimited budget only, hence the k0 = Inf premise. At Fin 0 Rule Out-Of-Fuel
  answers EBot BUndefined, and expr_to_pc reads no formula off a bottom, so
  the answer denotes nothing.
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
    | kv Φ Γ econ d args Hunspool_con
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
    | kv Φ Γ Γ' eb eb' Heval_t
    | Φ Γ eb
    ]; intros Hk0; try discriminate Hk0; injection Hk0 as Hk0; subst kv; intros σ S l Hmod Hfree Hden;
    try denote_absurd.
  - (* Eval_Var: a denoting variable is symbolic, so Γ cannot bind it *)
    exfalso. destruct (denote_var_inv σ S x l Hden) as [Hsx _].
    specialize (Hfree x Hsx). rewrite Hlookup in Hfree. discriminate.
  - (* Eval_SymVar *) exact Hden.
  - (* Eval_Lit *) exact Hden.
  - (* Eval_Con: a denoting term is solvable, so its head is not a constructor *)
    exfalso. destruct Hden as [pc [Hd _]].
    pose proof (expr_to_pc_solvable Γ econ pc (Hd Γ Hfree)) as Hsolv.
    apply unspool_is_con_app in Hunspool_con.
    rewrite (solvable_not_con_app Γ econ Hsolv) in Hunspool_con. discriminate.
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

(**
  SMT condition truth preservation across evaluation, FOR MODELS OF THE PATH
  CONDITION THE EVALUATION RAN UNDER.

  Both hypotheses are needed, and each one blocks a rule that would otherwise
  make the statement false.

  σ ⊨ Φ: Rule Prune lets any expression reduce to EBot BUnreachable whenever
  sat Φ = false, and EBot denotes no path-condition formula. Untied from Φ,
  the statement would say that every condition becomes unjudgeable as soon as
  ONE unsatisfiable path condition exists, and no symbolic branch could then
  be concretised. Under σ ⊨ Φ, models_sat gives sat Φ = true and Rule Prune
  cannot fire.

  sym_free_env S Γ: without it, take Γ binding x and evaluate the condition x
  by Rule Var to EBot BUndefined, which denotes no formula. The statement
  would then prove that no model satisfies the atom x, emptying out models on
  variables and making the non-vacuity suite of §11 hollow. See
  scratch/EvalModelsCondVerdict.v, which proves both collapses.

  Both were assumed until the verdict was defined from the value. Now the
  existence half is eval_denote above, and the verdict half is pc_value_sound
  in Section 9.0, which holds because ⊨ is read off pc_value.
*)
Lemma eval_models_cond : forall Φ Γ S ec ec' σ,
  σ ⊨ Φ -> sym_free_env S Γ ->
  Φ ; Γ ⊢ ec ⇓ ec' -> models_cond σ S ec -> models_cond σ S ec'.
Proof.
  intros Φ Γ S ec ec' σ Hmod Hfree Heval [pc [Hden Hsat]].
  destruct (eval_denote Φ Γ σ S ec ec' (pc_value σ pc) Hmod Hfree Heval
              (ex_intro _ pc (conj Hden eq_refl))) as [pc' [Hden' Hval']].
  exists pc'. split; [exact Hden' | exact (pc_value_sound σ pc pc' (eq_sym Hval') Hsat)].
Qed.

(** The negated form needs nothing about op_not: ¬ is the primitive
    application op_not, so equal values give equal values under it. *)
Lemma eval_models_not_cond : forall Φ Γ S ec ec' σ,
  σ ⊨ Φ -> sym_free_env S Γ ->
  Φ ; Γ ⊢ ec ⇓ ec' -> models_not_cond σ S ec -> models_not_cond σ S ec'.
Proof.
  intros Φ Γ S ec ec' σ Hmod Hfree Heval [pc [Hden Hsat]].
  destruct (eval_denote Φ Γ σ S ec ec' (pc_value σ pc) Hmod Hfree Heval
              (ex_intro _ pc (conj Hden eq_refl))) as [pc' [Hden' Hval']].
  exists pc'. split; [exact Hden' |].
  apply (pc_value_sound σ (¬ pc) (¬ pc')); [| exact Hsat].
  unfold pc_not. simpl. rewrite Hval'. reflexivity.
Qed.

(** ========================================================================= *)
(** 10. Soundness and Completeness of Symbolic Execution                      *)
(** ========================================================================= *)

(**
  Proved as a pair of mutually recursive fixpoints rather than by plain
  induction on the `eval`/`fold_alts` derivation. The Eval_AppPrim case needs
  soundness for every argument in its Forall2 (eval Inf Φ Γ) args args', and
  Eval_Case/FoldAlts_Con need it for the nested eval buried inside fold_alts.
  Coq's auto-derived induction principle for a mutually-recursive family
  covers neither: it strengthens only direct recursive occurrences, not ones
  nested inside a Forall2 or the sibling relation. The fixpoints recurse
  through those by hand, by induction on the embedded Forall2 or fold_alts
  proof, calling back into the fixpoint being defined.

  Unlimited budget only, hence the k0 = Inf premise on both fixpoints. The
  conclusion asks for a CONCRETE value that the symbolic value contains, and
  concrete evaluation has no budget of its own: it is fixed at Inf by
  eval_con. At Fin 0 the symbolic side answers EBot BUndefined, which
  contains only a concrete EBot BUndefined, and the concrete expression need
  not reduce to that.
*)

(** `contains` commutes with `unspool_app`, threading an existing pointwise
    correspondence on the accumulator through the same accumulator on both
    sides. This is the structural core of the App-Prim case of soundness. *)
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

(** ------------------------------------------------------------------------- *)
(** 9.3 Merging Never Loses an Instance (§3.3)                                *)
(** ------------------------------------------------------------------------- *)

(**
  Every concrete term the unmerged branch stands for, the merged term stands
  for too. This is the paper's Lemma A.4, and it is now proved from Section
  8.1's definition of merge instead of assumed.

  The proof is one case per clause of the merge table. The shape is always
  the same: the model picks an arm, the clause's result agrees with that arm
  on the head, and the branch that is left inside the result is resolved by
  the same model the same way.
*)

(** A branch is related to a concrete term by resolving it, never by
    denotation: a branch is not a primitive application. *)
Lemma contains_if_inv : forall σ S ec et ef e_c,
  contains σ S (EIf ec et ef) e_c ->
  (models_cond σ S ec /\ contains σ S et e_c) \/
  (models_not_cond σ S ec /\ contains σ S ef e_c).
Proof.
  intros σ S ec et ef e_c H. inversion H; subst.
  - left; split; assumption.
  - right; split; assumption.
  - simpl in *. discriminate.
Qed.

(** Concretion is a congruence for application spines *)
Lemma contains_fold_left_app : forall σ S l1 l2 h1 h2,
  Forall2 (contains σ S) l1 l2 ->
  contains σ S h1 h2 ->
  contains σ S (fold_left EApp l1 h1) (fold_left EApp l2 h2).
Proof.
  intros σ S l1 l2 h1 h2 HF. revert h1 h2.
  induction HF as [| x y l l' Hxy HF IH]; intros h1 h2 Hh; simpl.
  - exact Hh.
  - apply IH. apply Cont_App; assumption.
Qed.

(** Pushing one condition into matching argument lists keeps every argument
    related to the concrete argument the model chose *)
Lemma zip_if_contains_true : forall σ S ec a1 a2 args_c,
  models_cond σ S ec ->
  length a1 = length a2 ->
  Forall2 (contains σ S) a1 args_c ->
  Forall2 (contains σ S) (zip_if ec a1 a2) args_c.
Proof.
  intros σ S ec a1 a2 args_c Hmc Hlen HF. revert a2 Hlen.
  induction HF as [| x y l l' Hxy HF IH]; intros a2 Hlen.
  - destruct a2; simpl; constructor.
  - destruct a2 as [| z zs]; [discriminate |]. simpl.
    constructor; [apply Cont_If_True; assumption | apply IH; simpl in Hlen; auto].
Qed.

Lemma zip_if_contains_false : forall σ S ec a1 a2 args_c,
  models_not_cond σ S ec ->
  length a1 = length a2 ->
  Forall2 (contains σ S) a2 args_c ->
  Forall2 (contains σ S) (zip_if ec a1 a2) args_c.
Proof.
  intros σ S ec a1 a2 args_c Hmc Hlen HF. revert a1 Hlen.
  induction HF as [| x y l l' Hxy HF IH]; intros a1 Hlen.
  - destruct a1; simpl; constructor.
  - destruct a1 as [| z zs]; [discriminate |]. simpl.
    constructor; [apply Cont_If_False; assumption | apply IH; simpl in Hlen; auto].
Qed.

(** Closes the Cont_Denote case of an inversion on a term whose spine head is
    visibly not a primitive operation *)
Ltac kill_den :=
  match goal with
  | [ H : unspool_app _ _ = (EPrimOp _, _) |- _ ] => simpl in H; discriminate H
  end.

(** The four clauses that merge two identical or matching value forms *)
Ltac merge_leaf_rest et ef Hc Hcases :=
  destruct et; destruct ef; simpl; try exact Hc;
  [ destruct (String.eqb _ _) eqn:Hx; [| exact Hc];
    apply String.eqb_eq in Hx; subst;
    destruct Hcases as [[Hmc Hct]|[Hmc Hcf]];
    [ inversion Hct; subst; [| kill_den];
      apply Cont_Lam; [assumption | apply Cont_If_True; assumption]
    | inversion Hcf; subst; [| kill_den];
      apply Cont_Lam; [assumption | apply Cont_If_False; assumption] ]
  | destruct (dec_eqb coercion_eq_dec _ _) eqn:Hx; [| exact Hc];
    apply dec_eqb_eq in Hx; subst;
    destruct Hcases as [[Hmc Hct]|[Hmc Hcf]];
    [ inversion Hct; subst; [| kill_den] | inversion Hcf; subst; [| kill_den] ];
    apply Cont_Coercion
  | destruct (dec_eqb type_fc_eq_dec _ _) eqn:Hx; [| exact Hc];
    apply dec_eqb_eq in Hx; subst;
    destruct Hcases as [[Hmc Hct]|[Hmc Hcf]];
    [ inversion Hct; subst; [| kill_den] | inversion Hcf; subst; [| kill_den] ];
    apply Cont_Type
  | destruct (bottom_eqb _ _) eqn:Hx; [| exact Hc];
    apply bottom_eqb_eq in Hx; subst;
    destruct Hcases as [[Hmc Hct]|[Hmc Hcf]];
    [ inversion Hct; subst; [| kill_den] | inversion Hcf; subst; [| kill_den] ];
    apply Cont_Bot ].

Lemma ite_leaf_contains : forall σ S Γ ec et ef e_c,
  contains σ S (EIf ec et ef) e_c -> contains σ S (ite_leaf Γ ec et ef) e_c.
Proof.
  intros σ S Γ ec et ef e_c Hc.
  assert (Hcases := contains_if_inv σ S ec et ef e_c Hc).
  unfold ite_leaf.
  destruct (decompose_con_app et) as [[d1 a1]|] eqn:E1;
  destruct (decompose_con_app ef) as [[d2 a2]|] eqn:E2.
  - (* both arms are constructor spines *)
    destruct (andb (String.eqb d1 d2) (Nat.eqb (length a1) (length a2))) eqn:Hg;
      [| exact Hc].
    apply andb_prop in Hg as [Hd Hl].
    apply String.eqb_eq in Hd. apply Nat.eqb_eq in Hl. subst d2.
    assert (Hu1 := decompose_con_app_unspool et d1 a1 E1).
    assert (Hu2 := decompose_con_app_unspool ef d1 a2 E2).
    destruct Hcases as [[Hmc Hct] | [Hmc Hcf]].
    + destruct (contains_unspool_con σ S et e_c Hct [] [] (Forall2_nil _) d1 a1 Hu1)
        as [args_c [Huc HFa]].
      rewrite <- (unspool_make_con_app e_c d1 args_c Huc).
      unfold make_con_app. apply contains_fold_left_app; [| apply Cont_Con].
      apply zip_if_contains_true; assumption.
    + destruct (contains_unspool_con σ S ef e_c Hcf [] [] (Forall2_nil _) d1 a2 Hu2)
        as [args_c [Huc HFa]].
      rewrite <- (unspool_make_con_app e_c d1 args_c Huc).
      unfold make_con_app. apply contains_fold_left_app; [| apply Cont_Con].
      apply zip_if_contains_false; assumption.
  - destruct (solvable_dec Γ et); [destruct (solvable_dec Γ ef) |].
    + apply reduce_prim_ite_contains. exact Hc.
    + exact Hc.
    + merge_leaf_rest et ef Hc Hcases.
  - destruct (solvable_dec Γ et); [destruct (solvable_dec Γ ef) |].
    + apply reduce_prim_ite_contains. exact Hc.
    + exact Hc.
    + merge_leaf_rest et ef Hc Hcases.
  - destruct (solvable_dec Γ et); [destruct (solvable_dec Γ ef) |].
    + apply reduce_prim_ite_contains. exact Hc.
    + exact Hc.
    + merge_leaf_rest et ef Hc Hcases.
Qed.

Lemma ite_contains : forall σ S Γ et ec ef e_c,
  contains σ S (EIf ec et ef) e_c -> contains σ S (ite Γ ec et ef) e_c.
Proof.
  intros σ S Γ et. induction et; intros ec ef e_c Hc;
    try (rewrite ite_leaf_of by (left; reflexivity);
         apply ite_leaf_contains; exact Hc).
  destruct ef; try (rewrite ite_leaf_of by (right; reflexivity);
                    apply ite_leaf_contains; exact Hc).
  rewrite ite_cast.
  destruct (dec_eqb coercion_eq_dec c c0) eqn:Hx; [| exact Hc].
  apply dec_eqb_eq in Hx. subst c0.
  destruct (contains_if_inv σ S ec (ECast et c) (ECast ef c) e_c Hc)
    as [[Hmc Hct]|[Hmc Hcf]].
  - inversion Hct; subst; [| kill_den].
    apply Cont_Cast. apply IHet. apply Cont_If_True; assumption.
  - inversion Hcf; subst; [| kill_den].
    apply Cont_Cast. apply IHet. apply Cont_If_False; assumption.
Qed.

Lemma merge_contains : forall σ S Γ es ec,
  contains σ S es ec ->
  contains σ S (merge Γ es) ec.
Proof.
  intros σ S Γ es ec H. destruct es; simpl; try exact H.
  apply ite_contains. exact H.
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
    + simpl. apply Cont_Env_Extend;
        [exact Hx | exact Hargenv | apply Cont_Bot | constructor | apply IH; auto].
    + simpl. inversion Hargs as [| a0 ac0 args_s'0 args_c'0 Hcont_a Hargs' Heq1 Heq2]; subst.
      inversion Hconcore as [| ac1 args_c'1 Hcon_a Hconcore' ]; subst.
      apply Cont_Env_Extend.
      * exact Hx.
      * exact Hargenv.
      * exact Hcont_a.
      * exact Hcon_a.
      * apply IH; assumption.
Qed.

Lemma contains_con_value : forall σ S Γs Γc d args_s args_c,
  contains_env σ S Γs Γc ->
  Forall2 (contains σ S) args_s args_c ->
  contains σ S (make_con_app d (map (EThunk Γs) args_s))
               (make_con_app d (map (EThunk Γc) args_c)).
Proof.
  intros σ S Γs Γc d args_s args_c Henv Hargs.
  unfold make_con_app. apply contains_fold_left_app; [| apply Cont_Con].
  induction Hargs; simpl; constructor; [apply Cont_Thunk |]; assumption.
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
    | kv Φ Γ esp d args Hunspool_con
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
    | kv Φ Γ Γ' e e' Heval_t
    | Φ Γ e
    ]; intros Hk0; try discriminate Hk0; injection Hk0 as Hk0; subst kv; intros Γc σ S e_con Hmod Henv Hcont Hcon.
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
  - (* Eval_Con: concretion keeps the constructor at the head of the spine
       and relates the fields one by one *)
    assert (Hnil : Forall2 (contains σ S) [] []) by constructor.
    destruct (contains_unspool_con σ S esp e_con Hcont [] [] Hnil d args Hunspool_con)
      as [args_c [Hunspool_c Hargs_c]].
    exists (make_con_app d (map (EThunk Γc) args_c)). split.
    + unfold eval_con. exact (Eval_Con Unlimited pc_true Γc e_con d args_c Hunspool_c).
    + exact (contains_con_value σ S Γ Γc d args args_c Henv Hargs_c).
  - (* Eval_Cast *)
    apply contains_cast_inv in Hcont as [ec [Heq Hcont_e]]; subst.
    inversion Hcon as [| | | | | | | | ec0 γ0 Hcon_e | | | | | | ]; subst.
    destruct (concore_soundness_fix Inf Φ Γ e e' Heval_e eq_refl Γc σ S ec Hmod Henv Hcont_e Hcon_e) as [vc [Hevalc Hcont_v]].
    exists (cast_expr vc γ). split; [unfold eval_con; apply Eval_Cast; exact Hevalc | apply cast_expr_contains; exact Hcont_v].
  - (* Eval_AppAbs *)
    assert (Hfree : sym_free_env S Γ)
      by (destruct (contains_env_sym_free σ S Γ Γc Henv) as [Hf _]; exact Hf).
    destruct (contains_app_inv σ S Γ (EClos Γ' x eb) ea e_con Hfree Hcont) as
      [[fc [ac [Heq [Hcont_f Hcont_a]]]] | [Hsolv _]];
      [subst e_con | exfalso; inversion Hsolv].
    apply contains_clos_inv in Hcont_f as [Γ'c [ebc [Heq_f [Hsx [Henv_clos Hcont_b]]]]]; subst.
    inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | | ]; subst.
    inversion Hf as [| | | | | | Γ0 x0 body Henv_clos_c Hcon_b | | | | | | | | ]; subst.
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
    inversion Hcon as [| | | | fc0 ac0 Hcon_f Hcon_a | | | | | | | | | | ]; subst.
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
    inversion Hcon as [| | | | | | | es0 alts0 Hcon_es Hcon_alts | | | | | | | ]; subst.
    destruct (concore_soundness_fix Inf Φ Γ es es' Heval_es eq_refl Γc σ S esc Hmod Henv Hcont_es Hcon_es) as [vc_s [Heval_esc Hcont_vs]].
    assert (Hcont_merge : contains σ S (merge Γ es') vc_s) by (apply merge_contains; exact Hcont_vs).
    destruct (concore_soundness_fold_fix Inf Φ Γ (merge Γ es') alts er Hfold eq_refl Γc σ S esc altsc Hmod Henv Hcon_es Hcon_alts
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
  - (* Eval_Thunk *)
    inversion Hcont as [| | | | | | | | | | | Γs0 Γ'c es0 ec Henv' Hcont_e | | | | | ];
      subst; [| kill_denote].
    inversion Hcon as [| | | | | | | | | | | | | | Γ0 e0 Henv_c He_c]; subst.
    destruct (concore_soundness_fix Inf Φ Γ' e e' Heval_t eq_refl Γ'c σ S ec
                Hmod Henv' Hcont_e He_c) as [v_con [Hevalc Hcont_v]].
    exists v_con. split; [| exact Hcont_v].
    unfold eval_con. apply Eval_Thunk. exact Hevalc.
}
{
  destruct Hfold as
    [ kv Φ Γ ec et ef alts et' ef' pc_c Hpc Hfold_t Hfold_f
    | kv Φ Γ ec et ef alts Hpc_none
    | kv Φ Γ e d ea xs ep alts er Hdec Halt Heval_ep
    | kv Φ Γ b alts
    | kv Φ Γ e alts Hnothead Hnoalt Hnotbot
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
    + (* The concrete scrutinee value is a ConCore term, so it carries no
         branch and merge returns it unchanged. *)
      rewrite (merge_concore_id Γc vc_s Hcon_vcs).
      eapply FoldAlts_Con; [exact Hdec_vcs | exact Halt_c | exact Heval_ep_c].
  - (* FoldAlts_Bot *)
    destruct Hvc as [vc_s [Heval_esc Hcont_vs]].
    inversion Hcont_vs; subst; [| kill_denote].
    exists (EBot b). split; [| apply Cont_Bot].
    unfold eval_con. eapply Eval_Case.
    + exact Heval_esc.
    + rewrite (merge_not_if Γc (EBot b) eq_refl). apply FoldAlts_Bot.
  - (* FoldAlts_Otherwise *)
    destruct Hvc as [vc_s [Heval_esc Hcont_vs]].
    destruct (unspool_app e []) as [head args] eqn:Hunspool_e.
    assert (Hif_head : is_if head = false).
    { simpl in Hnothead. exact Hnothead. }
    assert (Hfacts :
      (match decompose_con_app vc_s with
       | Some (d, _) => find_alt d altsc = None
       | None => True
       end)
      /\ is_bot vc_s = false /\ is_if (fst (unspool_app vc_s [])) = false).
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
          inversion Hcont_vs; subst; try discriminate;
            simpl in Hunspool_e; injection Hunspool_e as Hh Ha; subst; discriminate.
        + assert (Hif_head_c : is_if head_c = false).
          { inversion Hcont_head; subst; try reflexivity;
              simpl in Hif_head; discriminate. }
          rewrite Hunspool_vcs. simpl. exact Hif_head_c.
      - (* the scrutinee concretised to an SMT value, which matches no
           constructor alternative, exactly as the symbolic side did *)
        split; [| split].
        + unfold decompose_con_app. rewrite Hunspool_vcs. exact I.
        + destruct (is_bot vc_s) eqn:Hbc; [| reflexivity].
          exfalso. destruct vc_s; simpl in Hbc; discriminate.
        + rewrite Hunspool_vcs. reflexivity.
    }
    destruct Hfacts as [Hnoalt_c [Hnotbot_c Hnothead_c]].
    exists (EBot BUndefined). split; [| apply Cont_Bot].
    unfold eval_con. eapply Eval_Case.
    + exact Heval_esc.
    + (* The spine head of the concrete scrutinee value is not a branch, so
         neither is the value, and merge returns it unchanged. *)
      rewrite (merge_not_if Γc vc_s (is_if_false_of_spine_head vc_s Hnothead_c)).
      apply FoldAlts_Otherwise; assumption.
}
Qed.

(**
  The conclusion is existential: SOME concrete value matches the symbolic one.

  The stronger reading,
    forall v_con, Γc ⊢ᶜ e_con ⇓ᶜ v_con -> contains σ S v_sym v_con,
  follows for the terms the theorem is about, because Section 12.4 proves
  concrete evaluation deterministic on them: e_con is a ConCore expression by
  hypothesis, and Γc is a ConCore environment by contains_env_concrete, so
  e_con has at most one value and the existential one is it.
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
  The other half of this section, completeness, is in Section 13. Its proof
  needs Section 12: a concrete program has at most one value, and that is what
  identifies the value soundness produces with the value completeness is
  handed.
*)

(** ========================================================================= *)
(** 11. NonVacuity: what the statement actually says                          *)
(** ========================================================================= *)

(**
  Six facts that show the soundness theorem is not empty:

  (a) a free symbolic variable is genuinely instantiated to its value under
      the model, and the soundness theorem has real instances that use it;
  (b) a branch whose condition mentions a free symbolic variable DOES have a
      concretion;
  (c) Rule Prune does not kill every branch;
  (d) reduce_prim is not forced to be a constant function on literals, and
      the assumption that would force it is identified;
  (e) the relation is DISCRIMINATING: different literals, different
      constructors and different shapes stay unrelated, a symbolic SMT term
      has exactly one literal concretion, and a closed SMT term is related to
      nothing but itself, so non-vacuity is not bought with triviality;
  (f) a primitive that really computes a function which is neither constant
      nor the identity lives inside the axiom set, and the soundness theorem
      applies to a program that uses it.

  No new axiom is introduced by any of this. (e) and (f) use only the three
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

(** The one premise that cannot be dispensed with is non-degeneracy of the SMT
    theory: some model must satisfy some atom. *)
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
    reduce_prim_solvable, which this development does not assume. *)
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

  (** models_cond is a definition, not an abstract judgement, so a caller
      discharges the branch premise from a model of the condition's own
      formula and nothing else. *)
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
  relation that holds of no pair does. The facts below stop that.
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

(** Cont_Denote relates a symbolic SMT term to ONE literal, the one it
    denotes: `contains` is a function on the SMT fragment. *)
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

(** On CLOSED SMT terms the relation is plain syntactic equality: Cont_Denote
    never fires where there is no symbolic variable to instantiate. *)
Corollary closed_smt_term_is_rigid : forall σ S es ec,
  smt_ground es = true -> contains σ S es ec -> es = ec.
Proof.
  intros σ S es ec Hg Hcont.
  exact (ground_solvable_contains_eq σ S es ec Hcont
           (fun Γ => smt_ground_solvable es Γ Hg)).
Qed.

(* ======= (f) a primitive that computes, and soundness applied to it ===== *)

(**
  Everything below is hypothetical in the Section's variables, so it adds no
  assumption to the development. It shows that a reducer which really computes
  a function that is NEITHER constant NOR the identity sits inside the axiom
  set instead of contradicting it.

  The load-bearing step is computing_primitive_concretion: the concretion is
  derived from Cont_Denote, without appealing to reduce_prim_contains at all.
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

  (** The concretion, as a theorem about `contains` rather than an
      assumption. *)
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

  (** succ is neither constant nor the identity. *)
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
  Concrete evaluation runs at the satisfiable path condition pc_true, so Rule
  Prune cannot fire at the root. One rule overlap survives that and gives the
  same concrete expression two values: Rule Prune inside Rule If. Rule If
  evaluates the branches under Φ ∧ pc_c and Φ ∧ ¬pc_c, not under Φ. One of
  those is unsatisfiable whenever the branch is dead, which is the only reason
  Rule Prune exists. Section 12.1 refutes the unrestricted statement with it.

  Rule App-Cast and Rule App-Spine do not overlap: Rule App-Spine refuses
  EVERY cast operator. Section 12.3 records what that costs and what it buys.

  Rule App-Spine and Rule App-Prim do not overlap either. Section 12.2 proves
  the two can never apply to the same expression.

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
  - (* Eval_Con: a spine has a single head *)
    match goal with
    | [ Hc : unspool_app _ _ = (ECon _, _) |- _ ] => rewrite Hc in Hun; discriminate
    end.
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
  - no_con_head.
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
  Rule App-Spine cannot strip the cast and hand the function the plain
  argument: its premise refuses every cast operator, and this operator is a
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

End CastedApplication.

(** ------------------------------------------------------------------------- *)
(** 12.4 ConCore programs have at most one value                              *)
(** ------------------------------------------------------------------------- *)

(**
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

    App-Spine against App-Cast   : App-Spine's cast guard settles it.
    App-Spine against App-Prim   : Section 12.2 settles it.
    App-Spine against App-Abs    : a closure is a value.
    App-Spine against App-Bot    : a bottom is a value.
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
  inversion Heval; subst; try prune_absurd; try no_con_head.
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
  inversion Heval; subst; try prune_absurd; try no_con_head; [congruence | reflexivity].
Qed.

Lemma eval_lit_inv : forall Φ Γ l v,
  sat Φ = true -> Φ ; Γ ⊢ ELit l ⇓ v -> v = ELit l.
Proof.
  intros Φ Γ l v Hsat Heval.
  inversion Heval; subst; try prune_absurd; try no_con_head; reflexivity.
Qed.

Lemma eval_con_inv : forall Φ Γ d v,
  sat Φ = true -> Φ ; Γ ⊢ ECon d ⇓ v -> v = ECon d.
Proof.
  intros Φ Γ d v Hsat Heval. exact (eval_con_same Φ Γ d v Hsat Heval).
Qed.

Lemma eval_bot_inv : forall Φ Γ b v,
  sat Φ = true -> Φ ; Γ ⊢ EBot b ⇓ v -> v = EBot b.
Proof.
  intros Φ Γ b v Hsat Heval.
  inversion Heval; subst; try prune_absurd; try no_con_head; reflexivity.
Qed.

Lemma eval_lam_inv : forall Φ Γ x e0 v,
  sat Φ = true -> Φ ; Γ ⊢ ELam x e0 ⇓ v -> v = EClos Γ x e0.
Proof.
  intros Φ Γ x e0 v Hsat Heval.
  inversion Heval; subst; try prune_absurd; try no_con_head; reflexivity.
Qed.

Lemma eval_coercion_inv : forall Φ Γ γ v,
  sat Φ = true -> Φ ; Γ ⊢ ECoercion γ ⇓ v -> v = ECoercion (subst_coerc Γ γ).
Proof.
  intros Φ Γ γ v Hsat Heval.
  inversion Heval; subst; try prune_absurd; try no_con_head; reflexivity.
Qed.

Lemma eval_type_inv : forall Φ Γ τ v,
  sat Φ = true -> Φ ; Γ ⊢ EType τ ⇓ v -> v = EType (subst_type Γ τ).
Proof.
  intros Φ Γ τ v Hsat Heval.
  inversion Heval; subst; try prune_absurd; try no_con_head; reflexivity.
Qed.

Lemma eval_thunk_inv : forall Φ Γ Γ' e0 v,
  sat Φ = true -> Φ ; Γ ⊢ EThunk Γ' e0 ⇓ v -> Φ ; Γ' ⊢ e0 ⇓ v.
Proof.
  intros Φ Γ Γ' e0 v Hsat Heval.
  inversion Heval; subst; try prune_absurd; try no_con_head; assumption.
Qed.

Lemma eval_cast_inv : forall Φ Γ e0 γ v,
  sat Φ = true ->
  Φ ; Γ ⊢ ECast e0 γ ⇓ v ->
  exists e', Φ ; Γ ⊢ e0 ⇓ e' /\ v = cast_expr e' γ.
Proof.
  intros Φ Γ e0 γ v Hsat Heval.
  inversion Heval; subst; try prune_absurd; try no_con_head.
  eexists. split; [eassumption | reflexivity].
Qed.

Lemma eval_case_inv : forall Φ Γ es alts v,
  sat Φ = true ->
  Φ ; Γ ⊢ ECase es alts ⇓ v ->
  exists es', Φ ; Γ ⊢ es ⇓ es' /\ fold_alts Inf Φ Γ (merge Γ es') alts v.
Proof.
  intros Φ Γ es alts v Hsat Heval.
  inversion Heval; subst; try prune_absurd; try no_con_head.
  eexists. split; eassumption.
Qed.

Lemma eval_app_clos_inv : forall Φ Γ Γ' x eb ea v,
  sat Φ = true ->
  Φ ; Γ ⊢ EApp (EClos Γ' x eb) ea ⇓ v ->
  Φ ; extend_env Γ' x Γ ea ⊢ eb ⇓ v.
Proof.
  intros Φ Γ Γ' x eb ea v Hsat Heval.
  inversion Heval; subst; try prune_absurd; try no_con_head.
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
  inversion Heval; subst; try prune_absurd; try no_con_head.
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
  inversion Heval; subst; try prune_absurd; try no_con_head.
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
  inversion Heval; subst; try prune_absurd; try no_con_head.
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
  inversion Heval; subst; try prune_absurd; try no_con_head.
  - (* Eval_Con: the operator of a constructor spine is already a value *)
    exfalso. apply Hnw.
    match goal with
    | [ Hu : unspool_app (EApp ef ea) [] = (ECon _, _) |- _ ] =>
        simpl in Hu;
        destruct (is_con_app_unspool ef (unspool_is_con_app ef [ea] _ _ Hu))
          as [d0 [args0 Hu0]];
        exact (Whnf_Con Γ ef d0 args0 Hu0)
    end.
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
  inversion Heval; subst; try prune_absurd; try no_con_head.
  - (* Eval_Con: a spine has a single head *)
    match goal with
    | [ Hc : unspool_app _ _ = (ECon _, _) |- _ ] => rewrite Hun in Hc; discriminate
    end.
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
  eval f Φ (extend_env_multi Γ xs ea Γ) ep r.
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

  Unlimited budget only, hence the k0 = Inf premise. A finite budget breaks
  one step of the argument: Section 12.2 separates Rule App-Spine from Rule
  App-Prim because the operator of a saturated primitive spine has no value,
  and at Fin 0 Rule Out-Of-Fuel gives it one.
  bounded_determinism_decides_reduce_prim below is the consequence.
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
    | kv Φ Γ esp d args_con Hunspool_con
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
    | kv Φ Γ Γ' e0 e' Heval_t
    | Φ Γ e0
    ]; intros Hk0; try discriminate Hk0; injection Hk0 as Hk0; subst kv; intros v2 Hsat Henv Hcon H2.
  - (* Rule Var *)
    destruct (lookup_env_concrete Γ x Γ' e0 Henv Hlook) as [Henv' He].
    exact (eval_det_fix Inf Φ Γ' e0 e' Heval_x eq_refl v2 Hsat Henv' He
             (eval_var_bound_inv Φ Γ x Γ' e0 v2 Hsat Hlook H2)).
  - (* Rule Sym-Var *) symmetry. exact (eval_var_free_inv Φ Γ x v2 Hsat Hnone H2).
  - (* Rule Lit *) symmetry. exact (eval_lit_inv Φ Γ l v2 Hsat H2).
  - (* Rule Con *) symmetry.
    exact (eval_con_spine_same Φ Γ esp d args_con v2 Hsat Hunspool_con H2).
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
    exact (fold_alts_det_fix Inf Φ Γ (merge Γ es') alts er Hfold eq_refl v2 Hsat Henv
             (merge_concore Γ es' (concore_eval_closed_fix Inf Φ Γ es es' Heval_es Hsat Henv Hces))
             Halts Hfold2).
  - (* Rule If: a ConCore expression is never a branch *)
    exfalso. exact (not_concore_if ec et ef Hcon).
  - (* Rule Coercion *) symmetry. exact (eval_coercion_inv Φ Γ γ v2 Hsat H2).
  - (* Rule Prune: the path condition holds *)
    exfalso. rewrite Hsat in Hunsat. discriminate.
  - (* Rule Type *) symmetry. exact (eval_type_inv Φ Γ τ v2 Hsat H2).
  - (* Rule Thunk *)
    inversion Hcon as [| | | | | | | | | | | | | | Γ0 e1 Henv' He]; subst.
    exact (eval_det_fix Inf Φ Γ' e0 e' Heval_t eq_refl v2 Hsat Henv' He
             (eval_thunk_inv Φ Γ Γ' e0 v2 Hsat H2)).
}
{
  destruct Hfold as
    [ kv Φ Γ ec et ef alts et' ef' pc_c Hpc Hfold_t Hfold_f
    | kv Φ Γ ec et ef alts Hpc_none
    | kv Φ Γ e0 d ea xs ep alts er Hdec Halt Heval_ep
    | kv Φ Γ b alts
    | kv Φ Γ e0 alts Hnothead Hnoalt Hnotbot
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
    exact (fold_alts_otherwise_inv Inf Φ Γ e0 alts r2
             (is_if_false_of_spine_head e0 Hnothead) Hnoalt Hnotbot H2).
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

(**
  Determinism at every finite budget is not provable here. The operator of
  the saturated spine below is not a value, because its first argument is a
  lambda. At Fin 1 Rule App-Spine runs the operator at Fin 0, gets the
  undefined value, and answers undefined. Rule App-Prim runs the arguments at
  Fin 0 instead and answers reduce_prim of three undefined values. So
  determinism at every budget would fix what the solver returns for those
  arguments, which no axiom here says.
*)
Definition prim_spine_arg : expr := ELam "y" (EVar "y").
Definition prim_spine_operator : expr :=
  EApp (EApp (EPrimOp op_ite) prim_spine_arg) prim_spine_arg.
Definition prim_spine : expr := EApp prim_spine_operator prim_spine_arg.
Definition undefined_args : list expr :=
  EBot BUndefined :: EBot BUndefined :: EBot BUndefined :: nil.

Lemma prim_spine_concore : concore_expr prim_spine.
Proof. unfold prim_spine, prim_spine_operator, prim_spine_arg. repeat constructor. Qed.

Lemma prim_spine_operator_not_whnf : forall Γ, ~ Whnf Γ prim_spine_operator.
Proof.
  intros Γ Hw. unfold prim_spine_operator, prim_spine_arg in Hw.
  inversion Hw; subst; [| no_con_head].
  match goal with [ Hs : Solvable _ _ |- _ ] => inversion Hs; subst end.
  match goal with [ Hs : Solvable _ (ELam _ _) |- _ ] => inversion Hs end.
Qed.

Lemma prim_spine_by_app_spine :
  eval (Fin 1) pc_true · prim_spine (EBot BUndefined).
Proof.
  unfold prim_spine. eapply Eval_AppSpine with (ef' := EBot BUndefined).
  - apply prim_spine_operator_not_whnf.
  - reflexivity.
  - apply Eval_OutOfFuel.
  - apply Eval_OutOfFuel.
Qed.

Lemma prim_spine_by_app_prim :
  eval (Fin 1) pc_true · prim_spine (reduce_prim op_ite undefined_args).
Proof.
  unfold prim_spine, prim_spine_operator. eapply Eval_AppPrim.
  - reflexivity.
  - rewrite op_ite_arity. reflexivity.
  - unfold undefined_args. repeat constructor.
Qed.

Lemma bounded_determinism_decides_reduce_prim :
  (forall n Γ e v1 v2, concrete_env Γ -> concore_expr e ->
     eval (Fin n) pc_true Γ e v1 -> eval (Fin n) pc_true Γ e v2 -> v1 = v2) ->
  reduce_prim op_ite undefined_args = EBot BUndefined.
Proof.
  intros Hdet.
  exact (Hdet 1%nat · prim_spine _ _ CEnv_Empty prim_spine_concore
           prim_spine_by_app_prim prim_spine_by_app_spine).
Qed.

(** The term of Section 12.3 has exactly one value, the one Rule App-Cast
    gives it. *)
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
(** 12.5 Applying a cast whose coercion does not split                        *)
(** ------------------------------------------------------------------------- *)

(**
  Applying a cast whose coercion does not split is stuck on the symbolic side
  and on the concrete side at once, so soundness never has to replay the step.
  Three lemmas above establish that: eval_app_cast_opaque_stuck,
  contains_is_cast and eval_app_if_false. The corollary just below packages
  the last two into the step eval_app_spine_sound takes.

  Rule App-Spine's guard tests the OPERATOR and not its coercion: it refuses
  every cast, value or not. A guard on the coercion would let the two sides
  disagree about whether the rule applies, because concretion can turn a
  non-value into a value, as whnf_not_preserved_by_concretion below shows,
  while leaving the coercion alone.

  The cost: a program whose operator evaluates to a cast with a non-arrow
  coercion has no value. Such a term applies something whose coercion does not
  split, which is applying a non-function, and System FC rejects it at
  type-check time. This judgement has no typing rules, so it gets stuck rather
  than inventing an answer. scratch/OpaqueCastOperatorReachable.v holds the
  witness program.
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
  - intro Hw. inversion Hw as [e0 Hsolv | | | | | | | ]; subst; [| no_con_head].
    inversion Hsolv as [| | | f a Hop Hf Ha]; subst.
    inversion Ha.
  - apply Whnf_Solvable. apply Solvable_AppPrim;
      [reflexivity | apply Solvable_PrimOp | apply Solvable_Lit].
Qed.

(** ------------------------------------------------------------------------- *)
(** 12.6 A constructor with a field, built, matched and read                  *)
(** ------------------------------------------------------------------------- *)

(**
  Rule Con gives a value to a whole application spine, so a constructor
  carrying fields is a value. The section below runs one all the way
  through: it builds Just l, matches it against the alternative Just y, and
  reads the field back out of the environment the match binds.

  Note where the field goes. Rule Con does not evaluate the argument; it
  pairs it with the environment it was written in. fold-alts binds that
  thunk to y, and the literal is read only when Rule Var reaches the thunk
  through y and Rule Thunk forces it.
*)
Section AppliedConstructorMatches.

  Variable l : lit.

  Definition just : expr := EApp (ECon "Just") (ELit l).
  Definition just_alts : list alt := [Alt "Just" ["y"] (EVar "y")].
  Definition just_value (Γ : environment) : expr := EApp (ECon "Just") (EThunk Γ (ELit l)).

  Lemma just_unspools : unspool_app just [] = (ECon "Just", [ELit l]).
  Proof. reflexivity. Qed.

  Lemma just_is_a_value : forall Γ, Whnf Γ just.
  Proof. intros Γ. exact (Whnf_Con Γ just "Just" [ELit l] just_unspools). Qed.

  Lemma just_evaluates : forall Γ, pc_true ; Γ ⊢ just ⇓ just_value Γ.
  Proof.
    intros Γ. exact (Eval_Con Unlimited pc_true Γ just "Just" [ELit l] just_unspools).
  Qed.

  Lemma just_is_concore : concore_expr just.
  Proof. apply Con_App; [apply Con_Con | apply Con_Lit]. Qed.

  (** case (Just l) of Just y -> y  reduces to l *)
  Lemma just_field_read_back : forall Γ,
    pc_true ; Γ ⊢ ECase just just_alts ⇓ ELit l.
  Proof.
    intros Γ.
    eapply Eval_Case; [apply just_evaluates |].
    rewrite (merge_not_if Γ (just_value Γ) eq_refl).
    eapply FoldAlts_Con with (d := "Just") (ea := [EThunk Γ (ELit l)]) (xs := ["y"])
                             (ep := EVar "y").
    - reflexivity.
    - simpl. destruct (string_dec "Just" "Just"); [reflexivity | congruence].
    - simpl. eapply Eval_Var.
      + unfold extend_env. simpl.
        destruct (string_dec "y" "y"); [reflexivity | congruence].
      + simpl. apply Eval_Thunk. apply Eval_Lit.
  Qed.

End AppliedConstructorMatches.

(** ------------------------------------------------------------------------- *)
(** 12.7 Constructor fields are read in the scope they were written in        *)
(** ------------------------------------------------------------------------- *)

(**
  The program case (λy. D y) A of D z -> z builds D y under the binding
  y = A and reads the field back through z, outside the scope of y. Rule Con
  pairs the field y with the environment that binds it, so the program reads
  A. Wrapping it in an outer binding y = B changes nothing, because the
  field never looks at the environment of the case.

  Before Rule Con kept the environment, the first program returned the free
  variable y and the second returned B.
*)
Section FieldsAreLexical.

  Definition field_builder : expr := ELam "y" (EApp (ECon "D") (EVar "y")).
  Definition field_reader : expr :=
    ECase (EApp field_builder (ECon "A")) (Alt "D" ("z" :: nil) (EVar "z") :: nil).
  Definition shadowed_field_reader : expr := EApp (ELam "y" field_reader) (ECon "B").

  Lemma field_reader_concore : concore_expr field_reader.
  Proof. repeat constructor. Qed.

  Lemma shadowed_field_reader_concore : concore_expr shadowed_field_reader.
  Proof. repeat constructor. Qed.

  Lemma field_reader_in : forall Γ,
    Γ ⊢ᶜ field_reader ⇓ᶜ ECon "A".
  Proof.
    intros Γ. unfold eval_con, field_reader.
    eapply Eval_Case.
    - eapply Eval_AppSpine; [apply not_whnf_lam | reflexivity | apply Eval_Lam |].
      apply Eval_AppAbs. eapply Eval_Con. reflexivity.
    - simpl. eapply FoldAlts_Con; [reflexivity | reflexivity |].
      simpl. eapply Eval_Var; [reflexivity |].
      apply Eval_Thunk. eapply Eval_Var; [reflexivity |].
      apply eval_nullary_con.
  Qed.

  Theorem field_reader_reads_lexically : ⊢ᶜ field_reader ⇓ᶜ ECon "A".
  Proof. apply field_reader_in. Qed.

  Theorem shadowed_field_reader_reads_lexically :
    ⊢ᶜ shadowed_field_reader ⇓ᶜ ECon "A".
  Proof.
    unfold eval_con, shadowed_field_reader.
    eapply Eval_AppSpine; [apply not_whnf_lam | reflexivity | apply Eval_Lam |].
    apply Eval_AppAbs. apply field_reader_in.
  Qed.

  Corollary field_reader_value_is_A : forall v,
    ⊢ᶜ field_reader ⇓ᶜ v -> v = ECon "A".
  Proof.
    intros v Hv.
    exact (concore_eval_deterministic_top field_reader v (ECon "A")
             field_reader_concore Hv field_reader_reads_lexically).
  Qed.

  Corollary shadowed_field_reader_value_is_A : forall v,
    ⊢ᶜ shadowed_field_reader ⇓ᶜ v -> v = ECon "A".
  Proof.
    intros v Hv.
    exact (concore_eval_deterministic_top shadowed_field_reader v (ECon "A")
             shadowed_field_reader_concore Hv shadowed_field_reader_reads_lexically).
  Qed.

  Corollary field_reader_no_free_variable : forall x,
    ~ (⊢ᶜ field_reader ⇓ᶜ EVar x).
  Proof. intros x Hv. discriminate (field_reader_value_is_A _ Hv). Qed.

  Corollary field_reader_not_B : ~ (⊢ᶜ field_reader ⇓ᶜ ECon "B").
  Proof. intros Hv. discriminate (field_reader_value_is_A _ Hv). Qed.

  Corollary shadowed_field_reader_no_free_variable : forall x,
    ~ (⊢ᶜ shadowed_field_reader ⇓ᶜ EVar x).
  Proof. intros x Hv. discriminate (shadowed_field_reader_value_is_A _ Hv). Qed.

  Corollary shadowed_field_reader_not_B : ~ (⊢ᶜ shadowed_field_reader ⇓ᶜ ECon "B").
  Proof. intros Hv. discriminate (shadowed_field_reader_value_is_A _ Hv). Qed.

End FieldsAreLexical.

(** ------------------------------------------------------------------------- *)
(** 12.8 A pattern variable with no field reads the undefined value           *)
(** ------------------------------------------------------------------------- *)

Section PatternLongerThanConstructor.

  Definition fieldless_reader : expr :=
    ECase (ECon "D") (Alt "D" ("z" :: nil) (EVar "z") :: nil).

  Lemma fieldless_reader_concore : concore_expr fieldless_reader.
  Proof. repeat constructor. Qed.

  Theorem fieldless_reader_is_undefined : ⊢ᶜ fieldless_reader ⇓ᶜ EBot BUndefined.
  Proof.
    unfold eval_con, fieldless_reader.
    eapply Eval_Case; [apply eval_nullary_con |].
    simpl. eapply FoldAlts_Con; [reflexivity | reflexivity |].
    simpl. eapply Eval_Var; [reflexivity | apply Eval_Bot].
  Qed.

  Corollary fieldless_reader_no_free_variable : forall x,
    ~ (⊢ᶜ fieldless_reader ⇓ᶜ EVar x).
  Proof.
    intros x Hv.
    discriminate (concore_eval_deterministic_top fieldless_reader _ _
                    fieldless_reader_concore Hv fieldless_reader_is_undefined).
  Qed.

End PatternLongerThanConstructor.

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
  stated for programs with no stuck subterm, and the predicate progressive below
  is what says that.

  WHAT THE HYPOTHESIS DOES NOT HAVE TO SAY. A leaf that calls no solver - no
  branch, no case, no cast, no primitive operation - is not stuck whenever
  its concretion has a value, and the theorem already asks for that value.
  Section 13.2 proves it, and the leaf clause of progressive asks for nothing
  else in that case. Only a leaf that does call the solver still has to be
  handed a value, because no property of a term survives merge, cast_expr or
  reduce_prim; Section 13.2 says where each of the three blocks the proof.
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
(** 13.2 Solver-Free Leaves Prove Their Own Progress                          *)
(** ------------------------------------------------------------------------- *)

(**
  A leaf of the branch tree needs no hypothesis at all when it makes no call
  to the solver. This section proves that, and Section 13.3 uses it to weaken
  the leaf clause of the no-stuck hypothesis.

  A term is SOLVER-FREE when it holds none of the four shapes whose value
  comes from an axiom instead of from a rule: EIf, the symbolic branch;
  ECase, which folds through merge; ECast, which reduces through cast_expr;
  and EPrimOp, which reduces through reduce_prim. What is left is the
  applicative core - variables, literals, constructors, lambdas, closures,
  thunks, applications, coercions, types and bottoms - which is straight-line
  code.

  On that core completeness DELIVERS convergence instead of assuming it. If
  the concrete run of the concretion has a value, then the symbolic run has
  one too, and the two match. So a solver-free leaf that got stuck would drag
  its concretion down with it, and the concrete run in the theorem's
  hypothesis would have no value to offer.

  HOW IT IS PROVED. By structural recursion on the CONCRETE derivation. Every
  rule the concrete run uses is answered by the same rule on the symbolic
  side. The shape of the concrete term fixes the shape of the symbolic one,
  because the only rules of concretion that change a term's shape are the two
  branch rules, which need an EIf, and the SMT rule Cont_Denote, which needs
  a primitive operation at the head of the spine. A solver-free term has
  neither.

  WHY THE OTHER THREE SHAPES ARE LEFT OUT. Each of them hands the term to an
  opaque function - merge, cast_expr or reduce_prim - and no axiom says the
  answer is solver-free again, so the recursion has nothing left to stand on
  past that point. ECase is worse still. Rule Case folds the alternatives
  over merge es', and concretion relates merge es' to the concrete scrutinee
  value, NOT to merge of that value. The axiom merge_fold_alts_equiv trades a
  fold over merge e for a fold over e, but what it returns is a fresh
  derivation: it is not a subterm of the derivation the recursion is taking
  apart, and it carries no height, so recursion on the height of a derivation
  is blocked in the same place as structural recursion. Only a fact saying
  that concretion survives merge ON THE CONCRETE SIDE would close that gap,
  and this development has no such fact and does not assume one.
*)

Inductive solver_free : expr -> Prop :=
  | SF_Var : forall x, solver_free (EVar x)
  | SF_Lit : forall l, solver_free (ELit l)
  | SF_Con : forall d, solver_free (ECon d)
  | SF_App : forall f a, solver_free f -> solver_free a -> solver_free (EApp f a)
  | SF_Lam : forall x body, solver_free body -> solver_free (ELam x body)
  | SF_Clos : forall Γ x body,
      solver_free_env Γ -> solver_free body -> solver_free (EClos Γ x body)
  | SF_Coercion : forall γ, solver_free (ECoercion γ)
  | SF_Type : forall τ, solver_free (EType τ)
  | SF_Bot_Undefined : solver_free (EBot BUndefined)
  | SF_Bot_Unreachable : solver_free (EBot BUnreachable)
  | SF_Bot_Raise : forall e, solver_free e -> solver_free (EBot (BRaise e))
  | SF_Thunk : forall Γ e,
      solver_free_env Γ -> solver_free e -> solver_free (EThunk Γ e)

with solver_free_env : environment -> Prop :=
  | SFEnv_Empty : solver_free_env ·
  | SFEnv_Extend : forall x Γ' e rest,
      solver_free e ->
      solver_free_env Γ' ->
      solver_free_env rest ->
      solver_free_env (ExtendEnv x (MkClosure Γ' e) rest).

Scheme solver_free_mut := Induction for solver_free Sort Prop
with solver_free_env_mut := Induction for solver_free_env Sort Prop.

Scheme contains_mut := Induction for contains Sort Prop
with contains_alt_mut := Induction for contains_alt Sort Prop
with contains_env_mut := Induction for contains_env Sort Prop.

(** A solver-free term is a ConCore term: it has no EIf anywhere, and every
    environment it carries is concrete. *)
Lemma solver_free_concore_mut :
  (forall e (H : solver_free e), concore_expr e)
  /\ (forall Γ (H : solver_free_env Γ), concrete_env Γ).
Proof.
  split.
  - apply (solver_free_mut (fun e _ => concore_expr e) (fun Γ _ => concrete_env Γ));
      intros; constructor; assumption.
  - apply (solver_free_env_mut (fun e _ => concore_expr e) (fun Γ _ => concrete_env Γ));
      intros; constructor; assumption.
Qed.

Lemma solver_free_concore : forall e, solver_free e -> concore_expr e.
Proof. apply solver_free_concore_mut. Qed.

Ltac sf_apply :=
  repeat match goal with
  | [ H : solver_free ?e -> solver_free ?f |- solver_free ?f ] => apply H
  | [ H : solver_free_env ?e -> solver_free_env ?f |- solver_free_env ?f ] => apply H
  end; assumption.

Ltac sf_case :=
  intros;
  try match goal with
      | [ H : solver_free _ |- _ ] => inversion H; subst
      | [ H : solver_free_env _ |- _ ] => inversion H; subst
      end;
  try assumption; try (constructor; sf_apply).

(** Concretion keeps a term inside the solver-free fragment. A symbolic
    variable goes to a literal and a residual SMT term goes to a literal;
    everything else keeps its shape. *)
Lemma contains_preserves_solver_free_mut :
  (forall σ S es ec, contains σ S es ec -> solver_free es -> solver_free ec)
  /\ (forall σ S Γs Γc, contains_env σ S Γs Γc -> solver_free_env Γs -> solver_free_env Γc).
Proof.
  split; intros σ S.
  - apply (contains_mut σ S
             (fun es ec _ => solver_free es -> solver_free ec)
             (fun a ac _ => True)
             (fun Γs Γc _ => solver_free_env Γs -> solver_free_env Γc));
      try sf_case.
  - apply (contains_env_mut σ S
             (fun es ec _ => solver_free es -> solver_free ec)
             (fun a ac _ => True)
             (fun Γs Γc _ => solver_free_env Γs -> solver_free_env Γc));
      try sf_case.
Qed.

Lemma contains_solver_free : forall σ S es ec,
  contains σ S es ec -> solver_free es -> solver_free ec.
Proof. apply contains_preserves_solver_free_mut. Qed.

(** A solver-free term has no primitive operation at the head of its spine,
    so Rule App-Prim and the SMT rule of concretion cannot fire on it. *)
Lemma solver_free_is_op_app : forall e, solver_free e -> is_op_app e = false.
Proof.
  intros e H. induction H; simpl; try reflexivity. assumption.
Qed.

Lemma solver_free_no_primop_head : forall e p args,
  solver_free e -> unspool_app e [] = (EPrimOp p, args) -> False.
Proof.
  intros e p args Hsf Hun.
  apply unspool_is_op_app in Hun.
  rewrite (solver_free_is_op_app e Hsf) in Hun. discriminate.
Qed.

Lemma solver_free_is_cast : forall e, solver_free e -> is_cast e = false.
Proof. intros e H. destruct H; reflexivity. Qed.

(** Concretion matches environment domains exactly. The direction proved in
    Section 9 reads the symbolic side; this one reads the concrete side. *)
Lemma contains_env_lookup_none_rev : forall σ S Γs Γc x,
  contains_env σ S Γs Γc ->
  lookup_env Γc x = None ->
  lookup_env Γs x = None.
Proof.
  intros σ S Γs Γc x H.
  induction H as [| y Γs' Γc' es ec rest_s rest_c Hy Henv IHenv Hcont Hcon Hrest IHrest];
    intros Hnone.
  - reflexivity.
  - simpl in *. destruct (string_dec x y); [discriminate | apply IHrest; exact Hnone].
Qed.

Lemma contains_env_lookup_rev : forall σ S Γs Γc x Γ'c ec,
  contains_env σ S Γs Γc ->
  lookup_env Γc x = Some (Γ'c, ec) ->
  exists Γ's es,
    lookup_env Γs x = Some (Γ's, es)
    /\ contains_env σ S Γ's Γ'c
    /\ contains σ S es ec.
Proof.
  intros σ S Γs Γc x Γ'c ec H.
  induction H as [| y Γs0 Γc0 es0 ec0 rest_s rest_c Hy Henv IHenv Hcont Hcon Hrest IHrest];
    intros Hlook.
  - simpl in Hlook. discriminate.
  - simpl in *. destruct (string_dec x y) as [Heq | Hne].
    + injection Hlook as Hg He. subst.
      exists Γs0, es0. split; [reflexivity | split; assumption].
    + destruct (IHrest Hlook) as [Γ's [es [Hl [He Hc]]]].
      exists Γ's, es. split; [exact Hl | split; assumption].
Qed.

Lemma solver_free_env_lookup : forall Γ x Γ' e,
  solver_free_env Γ ->
  lookup_env Γ x = Some (Γ', e) ->
  solver_free_env Γ' /\ solver_free e.
Proof.
  intros Γ x Γ' e H.
  induction H as [| y Γ0 e0 rest He0 HΓ0 IHΓ0 Hrest IHrest]; intros Hlook.
  - simpl in Hlook. discriminate.
  - simpl in Hlook. destruct (string_dec x y) as [Heq | Hne].
    + injection Hlook as Hg He. subst. split; assumption.
    + apply IHrest. exact Hlook.
Qed.

(** A solver-free term that is already a value on the symbolic side has a
    value for its concretion too. Rule App-Spine needs this: the rule fires
    only on an operator that is NOT a value, and it is the concrete run that
    reports that. *)
Lemma whnf_contains_solver_free : forall σ S Γs Γc es ec,
  contains_env σ S Γs Γc ->
  contains σ S es ec ->
  solver_free es ->
  Whnf Γs es ->
  Whnf Γc ec.
Proof.
  intros σ S Γs Γc es ec Henv Hcont Hsf Hwhnf.
  destruct Hwhnf as [e Hsolv | esp d cargs Hu | b | Γd x body | γ | τ | eb γ Hwb
                    | ec0 et ef Hsc Hwt Hwf].
  - destruct Hsolv as [l | x Hnone | p | f a Hop Hf Ha].
    + apply contains_lit_inv in Hcont. subst. apply Whnf_Solvable. apply Solvable_Lit.
    + inversion Hcont; subst.
      * apply Whnf_Solvable. apply Solvable_Var.
        eapply contains_env_lookup_none; eassumption.
      * apply Whnf_Solvable. apply Solvable_Lit.
      * kill_denote.
    + inversion Hsf.
    + exfalso. inversion Hsf as [| | | f0 a0 Hsf_f Hsf_a | | | | | | | |]; subst.
      simpl in Hop. rewrite (solver_free_is_op_app f Hsf_f) in Hop. discriminate.
  - (* the concrete spine carries the same constructor at its head *)
    assert (Hnil : Forall2 (contains σ S) [] []) by constructor.
    destruct (contains_unspool_con σ S esp ec Hcont [] [] Hnil d cargs Hu)
      as [args_c [Hu_c _]].
    exact (Whnf_Con Γc ec d args_c Hu_c).
  - inversion Hcont; subst; [apply Whnf_Bot | kill_denote].
  - apply contains_clos_inv in Hcont as [Γc0 [bodyc [Heq [Hsx [Henv0 Hcb]]]]]. subst.
    apply Whnf_Clos.
  - inversion Hcont; subst; [apply Whnf_Coercion | kill_denote].
  - inversion Hcont; subst; [apply Whnf_Type | kill_denote].
  - inversion Hsf.
  - inversion Hsf.
Qed.

(** Kill a case in which the symbolic term would have to be a branch, a case,
    a cast or a primitive operation. *)
Ltac not_solver_free :=
  exfalso;
  match goal with
  | [ H : solver_free (EIf _ _ _) |- _ ] => inversion H
  | [ H : solver_free (ECase _ _) |- _ ] => inversion H
  | [ H : solver_free (ECast _ _) |- _ ] => inversion H
  | [ H : solver_free (EPrimOp _) |- _ ] => inversion H
  end.

(** Inversion of concretion read from the CONCRETE side. Section 9 inverts it
    from the symbolic side; the recursion below walks the concrete derivation
    and so needs the other direction. *)
Lemma contains_clos_rev : forall σ S fs Γc x bc,
  contains σ S fs (EClos Γc x bc) ->
  solver_free fs ->
  exists Γs bs,
    fs = EClos Γs x bs /\ S x = false
    /\ contains_env σ S Γs Γc /\ contains σ S bs bc.
Proof.
  intros σ S fs Γc x bc Hcont Hsf.
  inversion Hcont; subst; try not_solver_free.
  eexists; eexists. split; [reflexivity | split; [assumption | split; assumption]].
Qed.

(** A constructor head read off the CONCRETE side. The two rules of
    concretion that move a constructor to the head of a spine both need a
    branch, and a solver-free term has none. *)
Lemma contains_con_app_rev : forall σ S e_sym e_con,
  contains σ S e_sym e_con ->
  solver_free e_sym ->
  is_con_app e_con = true ->
  is_con_app e_sym = true.
Proof.
  induction 1; intros Hsf Hc; simpl in Hc; simpl;
    try discriminate; try reflexivity.
  - (* Cont_App *)
    apply IHcontains1; [| exact Hc].
    inversion Hsf as [ | | | f0 a0 Hsf_f Hsf_a | | | | | | | | ]; subst. exact Hsf_f.
  - (* Cont_If_True *) inversion Hsf.
  - (* Cont_If_False *) inversion Hsf.
Qed.

Lemma solver_free_unspool_args : forall e acc h args,
  solver_free e ->
  Forall solver_free acc ->
  unspool_app e acc = (h, args) ->
  Forall solver_free args.
Proof.
  induction e; intros acc h args Hsf Hacc Hu; simpl in Hu;
    try (injection Hu as _ <-; exact Hacc).
  inversion Hsf; subst.
  apply (IHe1 (e2 :: acc) h args); [assumption | constructor; assumption | exact Hu].
Qed.

Lemma solver_free_con_value : forall Γ d args,
  solver_free_env Γ ->
  Forall solver_free args ->
  solver_free (make_con_app d (map (EThunk Γ) args)).
Proof.
  intros Γ d args HΓ Hargs. unfold make_con_app.
  assert (Hthunks : Forall solver_free (map (EThunk Γ) args)).
  { induction Hargs; simpl; constructor; [apply SF_Thunk |]; assumption. }
  generalize (SF_Con d). generalize (ECon d).
  induction Hthunks as [| a tl Ha Htl IH]; intros h Hh; simpl; [exact Hh |].
  apply IH. apply SF_App; assumption.
Qed.

(**
  Completeness on the solver-free fragment, by structural recursion on the
  concrete derivation.

  The budget plays no part here. The symbolic run answers at the unlimited
  budget, because a solver-free term holds no branch, and a branch is the
  only reason the symbolic run ever has to visit a piece of the program the
  concrete run skipped.

  The recursion also reports that the symbolic value is solver-free again.
  Rule App-Spine is what needs that: it evaluates the operator and then
  applies the result, so the value it computed is the next term the recursion
  is handed.
*)
Fixpoint solver_free_completeness_fix (k0 : fuel) (Ψ : path_condition) (Γc : environment)
  (e_con v_con : expr) (Heval : eval k0 Ψ Γc e_con v_con) {struct Heval} :
  k0 = Inf -> sat Ψ = true ->
  forall Φ Γs σ S e_sym,
    σ ⊨ Φ ->
    contains_env σ S Γs Γc ->
    contains σ S e_sym e_con ->
    solver_free e_sym ->
    solver_free_env Γs ->
    exists v_sym,
      eval Inf Φ Γs e_sym v_sym /\ contains σ S v_sym v_con /\ solver_free v_sym.
Proof.
  destruct Heval as
    [ kv Ψ0 Γ0 x Γ' e0 e' Hlookup Hev_x
    | kv Ψ0 Γ0 x Hnone
    | kv Ψ0 Γ0 l
    | kv Ψ0 Γ0 espc d args_c Hunspool_con
    | kv Ψ0 Γ0 e0 γ e' Hev_e
    | kv Ψ0 Γ0 Γ' x eb ea eb' Hev_b
    | kv Ψ0 Γ0 ef ea ef' er Hnotwhnf Hnocast Hev_f Hev_app2
    | kv Ψ0 Γ0 b
    | kv Ψ0 Γ0 ef ea p args args' Hunspool Harity Hargs
    | kv Ψ0 Γ0 x e0
    | kv Ψ0 Γ0 ef γ ea γ_a γ_r er Hdecomp Hev_pushed
    | kv Ψ0 Γ0 b ea
    | kv Ψ0 Γ0 es alts es' er Hev_es Hfold
    | kv Ψ0 Γ0 ec et ef ec' et' ef' pc_c Hev_c Hpc Hev_t Hev_f
    | kv Ψ0 Γ0 γ
    | kv Ψ0 Γ0 e0 Hunsat
    | kv Ψ0 Γ0 τ
    | kv Ψ0 Γ0 Γ' e0 e' Hev_t
    | Ψ0 Γ0 e0
    ]; intros Hk0 Hsat; try discriminate Hk0; injection Hk0 as Hk0; subst kv;
    intros Φ Γs σ S e_sym Hmod Henv Hcont Hsf Hsfenv.
  - (* Rule Var *)
    inversion Hcont; subst; try not_solver_free.
    destruct (contains_env_lookup_rev σ S Γs Γ0 x Γ' e0 Henv Hlookup)
      as [Γ's [es [Hlooks [Henv' Hcont']]]].
    destruct (solver_free_env_lookup Γs x Γ's es Hsfenv Hlooks) as [Hsfenv' Hsfes].
    destruct (solver_free_completeness_fix Inf Ψ0 Γ' e0 e' Hev_x eq_refl Hsat
                Φ Γ's σ S es Hmod Henv' Hcont' Hsfes Hsfenv')
      as [v_sym [Hev [Hcv Hsfv]]].
    exists v_sym. split; [| split; assumption].
    eapply Eval_Var; [exact Hlooks | exact Hev].
  - (* Rule Sym-Var *)
    inversion Hcont; subst; try not_solver_free.
    exists (EVar x). split; [| split].
    + apply Eval_SymVar. eapply contains_env_lookup_none_rev; eassumption.
    + apply Cont_Var_Bound. assumption.
    + apply SF_Var.
  - (* Rule Lit: the symbolic side is the literal itself, a symbolic variable
       the model sends to it, or a residual SMT term - and the last one has a
       primitive operation at its head, so it is not solver-free *)
    inversion Hcont as
      [ | y Hsy Heqs Heqc | l0 Heqs Heqc | | | | | | | | | | | | | | es p args l0 Hun Har Hg Hden ];
      subst; try not_solver_free.
    + exists (EVar y). split; [| split].
      * apply Eval_SymVar.
        destruct (contains_env_sym_free σ S Γs Γ0 Henv) as [Hfree _].
        apply Hfree. assumption.
      * apply Cont_Var_Sym. assumption.
      * apply SF_Var.
    + exists (ELit l). split; [apply Eval_Lit | split; [apply Cont_Lit | apply SF_Lit]].
    + exfalso. eapply solver_free_no_primop_head; eassumption.
  - (* Rule Con: the concrete spine has a constructor at its head, so the
       symbolic one does too, with fields related one by one *)
    assert (Hccon : is_con_app e_sym = true).
    { eapply contains_con_app_rev; [exact Hcont | exact Hsf |].
      eapply unspool_is_con_app. exact Hunspool_con. }
    destruct (is_con_app_unspool e_sym Hccon) as [d0 [args0 Hu0]].
    destruct (contains_unspool_con σ S e_sym espc Hcont [] [] (Forall2_nil _) d0 args0 Hu0)
      as [args_c' [Hu_c Hargs]].
    rewrite Hunspool_con in Hu_c. injection Hu_c as <- <-.
    exists (make_con_app d (map (EThunk Γs) args0)). split; [| split].
    + exact (Eval_Con Unlimited Φ Γs e_sym d args0 Hu0).
    + exact (contains_con_value σ S Γs Γ0 d args0 args_c Henv Hargs).
    + apply solver_free_con_value; [exact Hsfenv |].
      exact (solver_free_unspool_args e_sym [] _ _ Hsf (Forall_nil _) Hu0).
  - (* Rule Cast: a cast is not solver-free *)
    inversion Hcont; subst; try not_solver_free.
  - (* Rule App-Abs *)
    inversion Hcont as [ | | | | | | | | fs as_ fc ac Hcont_f Hcont_a | | | | | | | | ];
      subst; try not_solver_free.
    inversion Hsf as [ | | | fs0 as0 Hsf_f Hsf_a | | | | | | | | ]; subst.
    destruct (contains_clos_rev σ S fs Γ' x eb Hcont_f Hsf_f)
      as [Γ's [ebs [Heqf [Hsx [Henv_clos Hcont_b]]]]]. subst fs.
    inversion Hsf_f as [ | | | | | Γ's0 x0 b0 Hsf_env' Hsf_ebs | | | | | | ]; subst.
    assert (Henv_ext : contains_env σ S (extend_env Γ's x Γs as_) (extend_env Γ' x Γ0 ea)).
    { apply Cont_Env_Extend; try assumption.
      apply solver_free_concore. eapply contains_solver_free; eassumption. }
    assert (Hsfenv_ext : solver_free_env (extend_env Γ's x Γs as_))
      by (apply SFEnv_Extend; assumption).
    destruct (solver_free_completeness_fix Inf Ψ0 (extend_env Γ' x Γ0 ea) eb eb'
                Hev_b eq_refl Hsat Φ (extend_env Γ's x Γs as_) σ S ebs
                Hmod Henv_ext Hcont_b Hsf_ebs Hsfenv_ext)
      as [v_sym [Hev [Hcv Hsfv]]].
    exists v_sym. split; [| split; assumption].
    apply Eval_AppAbs. exact Hev.
  - (* Rule App-Spine *)
    inversion Hcont as [ | | | | | | | | fs as_ fc ac Hcont_f Hcont_a | | | | | | | | ];
      subst; try not_solver_free.
    inversion Hsf as [ | | | fs0 as0 Hsf_f Hsf_a | | | | | | | | ]; subst.
    destruct (solver_free_completeness_fix Inf Ψ0 Γ0 ef ef' Hev_f eq_refl Hsat
                Φ Γs σ S fs Hmod Henv Hcont_f Hsf_f Hsfenv)
      as [fs' [Hev_fs [Hcv_f Hsf_fs']]].
    assert (Hcont2 : contains σ S (EApp fs' as_) (EApp ef' ea))
      by (apply Cont_App; assumption).
    assert (Hsf2 : solver_free (EApp fs' as_)) by (apply SF_App; assumption).
    destruct (solver_free_completeness_fix Inf Ψ0 Γ0 (EApp ef' ea) er Hev_app2
                eq_refl Hsat Φ Γs σ S (EApp fs' as_) Hmod Henv Hcont2 Hsf2 Hsfenv)
      as [v_sym [Hev2 [Hcv Hsfv]]].
    exists v_sym. split; [| split; assumption].
    eapply Eval_AppSpine.
    + intros Hw. apply Hnotwhnf.
      eapply whnf_contains_solver_free; eassumption.
    + apply solver_free_is_cast. assumption.
    + exact Hev_fs.
    + exact Hev2.
  - (* Rule Bot *)
    inversion Hcont; subst; try not_solver_free.
    exists (EBot b). split; [apply Eval_Bot | split; [apply Cont_Bot | assumption]].
  - (* Rule App-Prim: the spine has a primitive operation at its head *)
    exfalso.
    eapply solver_free_no_primop_head;
      [ eapply contains_solver_free; eassumption | exact Hunspool ].
  - (* Rule Lam *)
    inversion Hcont; subst; try not_solver_free.
    inversion Hsf; subst.
    eexists. split; [apply Eval_Lam | split].
    + apply Cont_Clos; assumption.
    + apply SF_Clos; assumption.
  - (* Rule App-Cast: a cast operator is not solver-free *)
    inversion Hcont as [ | | | | | | | | fs as_ fc ac Hcont_f Hcont_a | | | | | | | | ];
      subst; try not_solver_free.
    inversion Hsf as [ | | | fs0 as0 Hsf_f Hsf_a | | | | | | | | ]; subst.
    inversion Hcont_f; subst; try not_solver_free.
  - (* Rule App-Bot *)
    inversion Hcont as [ | | | | | | | | fs as_ fc ac Hcont_f Hcont_a | | | | | | | | ];
      subst; try not_solver_free.
    inversion Hsf as [ | | | fs0 as0 Hsf_f Hsf_a | | | | | | | | ]; subst.
    inversion Hcont_f; subst; try not_solver_free.
    exists (EBot b). split; [apply Eval_AppBot | split; [apply Cont_Bot | assumption]].
  - (* Rule Case: a case is not solver-free *)
    inversion Hcont; subst; try not_solver_free.
  - (* Rule If: a branch is not solver-free *)
    inversion Hcont; subst; try not_solver_free.
  - (* Rule Coercion *)
    inversion Hcont; subst; try not_solver_free.
    exists (ECoercion (subst_coerc Γs γ)). split; [apply Eval_Coercion | split].
    + apply subst_coerc_contains_env. assumption.
    + apply SF_Coercion.
  - (* Rule Prune: the path condition of the concrete run is satisfiable *)
    rewrite Hunsat in Hsat. discriminate.
  - (* Rule Type *)
    inversion Hcont; subst; try not_solver_free.
    exists (EType (subst_type Γs τ)). split; [apply Eval_Type | split].
    + apply subst_type_contains_env. assumption.
    + apply SF_Type.
  - (* Rule Thunk *)
    inversion Hcont as [| | | | | | | | | | | Γs' Γc' es ec Henv' Hcont_e | | | | | ];
      subst; try not_solver_free.
    inversion Hsf as [| | | | | | | | | | | Γs0 es0 Hsfenv' Hsf_es]; subst.
    destruct (solver_free_completeness_fix Inf Ψ0 Γ' e0 e' Hev_t eq_refl Hsat
                Φ Γs' σ S es Hmod Henv' Hcont_e Hsf_es Hsfenv')
      as [v_sym [Hev [Hcv Hsfv]]].
    exists v_sym. split; [| split; assumption].
    apply Eval_Thunk. exact Hev.
Qed.

(**
  Completeness on the solver-free fragment. This is the lemma the leaf clause
  of progressive leans on: a solver-free leaf whose concretion has a concrete
  value has a symbolic value, so it is not stuck.
*)
Lemma solver_free_completeness : forall Φ Γs Γc σ S e_sym e_con v_con,
  σ ⊨ Φ ->
  contains_env σ S Γs Γc ->
  contains σ S e_sym e_con ->
  solver_free e_sym ->
  solver_free_env Γs ->
  Γc ⊢ᶜ e_con ⇓ᶜ v_con ->
  exists v_sym, Φ ; Γs ⊢ e_sym ⇓ v_sym /\ contains σ S v_sym v_con.
Proof.
  intros Φ Γs Γc σ S e_sym e_con v_con Hmod Henv Hcont Hsf Hsfenv Hevalc.
  destruct (solver_free_completeness_fix Inf pc_true Γc e_con v_con Hevalc eq_refl
              sat_pc_true Φ Γs σ S e_sym Hmod Henv Hcont Hsf Hsfenv)
    as [v_sym [Hev [Hcv Hsfv]]].
  exists v_sym. split; assumption.
Qed.

(**
  What the leaf clause of progressive asks for. Either the leaf makes no solver
  call, and then the concrete run in the theorem's hypothesis already says it
  is not stuck (solver_free_completeness above); or the leaf does make one,
  and then the only handle this development has on it is a value at the
  unlimited budget.

  The first alternative is what makes the hypothesis weaker than it was.
  Straight-line code used to have to be shown to converge, which is what
  completeness is for. Now it is shown to be straight-line code, and the
  convergence comes out of the proof.
*)
Definition leaf_progressive (Φ : path_condition) (Γ : environment) (e : expr) : Prop :=
  (solver_free e /\ solver_free_env Γ) \/ (exists v, Φ ; Γ ⊢ e ⇓ v).

Lemma leaf_progressive_of_terminating : forall Φ Γ e,
  (exists v, Φ ; Γ ⊢ e ⇓ v) -> leaf_progressive Φ Γ e.
Proof. intros Φ Γ e Hv. right. exact Hv. Qed.

Lemma leaf_progressive_of_solver_free : forall Φ Γ e,
  solver_free e -> solver_free_env Γ -> leaf_progressive Φ Γ e.
Proof. intros Φ Γ e Hsf Henv. left. split; assumption. Qed.

(** A leaf that satisfies the clause, and whose concretion the concrete run
    answers, has a symbolic value. This is the leaf case of the proof below,
    pulled out so that what the clause buys is visible on its own. *)
Lemma leaf_progressive_converges : forall Φ Γs Γc σ S e e_con v_con,
  σ ⊨ Φ ->
  contains_env σ S Γs Γc ->
  contains σ S e e_con ->
  Γc ⊢ᶜ e_con ⇓ᶜ v_con ->
  leaf_progressive Φ Γs e ->
  exists v, Φ ; Γs ⊢ e ⇓ v.
Proof.
  intros Φ Γs Γc σ S e e_con v_con Hmod Henv Hcont Hevalc [[Hsf Hsfenv] | Hv].
  - destruct (solver_free_completeness Φ Γs Γc σ S e e_con v_con
                Hmod Henv Hcont Hsf Hsfenv Hevalc) as [v [Hev _]].
    exists v. exact Hev.
  - exact Hv.
Qed.

(**
  Why the leaf clause cannot simply drop its last premise for every leaf
  whose top node is not a branch.

  is_if e = false says only that the TOP of the leaf is not a branch. A
  branch further down is still a branch, and concretion resolves it: the
  concrete side keeps the arm the model takes and never looks at the other
  one. The program below is the counterexample. Its operator is a branch
  whose untaken arm is a stuck application, so the whole application has no
  value at all - eval_app_if_false in Section 10 says an application whose
  operator is a branch is stuck outright - while its concretion is an
  ordinary redex that the concrete run answers.

  So a leaf clause that asked for nothing, or that asked only for
  is_if e = false, would be false. What the clause asks instead is that the
  leaf calls no solver, and a branch anywhere inside it is a solver call.
*)
Section BranchAtTheTopIsNotEnough.

  Variables (σ : valuation) (S : symvars) (x y : var) (l : lit).

  Hypothesis Hsx : S x = true.
  Hypothesis Hmodx : σ ⊨ (PCVar x).
  Hypothesis Hsy : S y = false.

  Definition hidden_branch : expr :=
    EApp (EIf (EVar x) (ELam y (EVar y)) (EApp (ELit l) (ELit l))) (ELit l).

  Definition hidden_branch_con : expr := EApp (ELam y (EVar y)) (ELit l).

  Lemma hidden_branch_not_if : is_if hidden_branch = false.
  Proof. reflexivity. Qed.

  Lemma hidden_branch_contains : contains σ S hidden_branch hidden_branch_con.
  Proof.
    apply Cont_App; [| apply Cont_Lit].
    apply Cont_If_True.
    - exists (PCVar x). split; [| exact Hmodx].
      intros Γ Hfree. simpl. rewrite (Hfree x Hsx). reflexivity.
    - apply Cont_Lam; [exact Hsy | apply Cont_Var_Bound; exact Hsy].
  Qed.

  Lemma hidden_branch_con_concore : concore_expr hidden_branch_con.
  Proof. apply Con_App; [apply Con_Lam; apply Con_Var | apply Con_Lit]. Qed.

  Lemma hidden_branch_con_converges : ⊢ᶜ hidden_branch_con ⇓ᶜ ELit l.
  Proof.
    unfold hidden_branch_con, eval_con.
    eapply Eval_AppSpine.
    - intros Hw. inversion Hw as [e0 Hsolv | | | | | | | ]; subst; [| no_con_head].
      inversion Hsolv.
    - reflexivity.
    - apply Eval_Lam.
    - apply Eval_AppAbs. eapply Eval_Var.
      + simpl. destruct (string_dec y y); [reflexivity | congruence].
      + apply Eval_Lit.
  Qed.

  Lemma hidden_branch_has_no_value : forall Φ Γ v,
    sat Φ = true -> ~ (Φ ; Γ ⊢ hidden_branch ⇓ v).
  Proof.
    intros Φ Γ v Hsat Hev.
    eapply eval_app_if_false; [exact Hev | exact Hsat | reflexivity | reflexivity].
  Qed.

End BranchAtTheTopIsNotEnough.

(** ------------------------------------------------------------------------- *)
(** 13.3 The No-Stuck-Subterm Hypothesis                                      *)
(** ------------------------------------------------------------------------- *)

(**
  progressive σ S Φ Γ e_sym e_con says: along the path the model σ takes through
  the branches of e_sym, nothing is stuck.

  The predicate walks down the branches of e_sym. At each branch it asks for
  three things, and at the bottom it asks for one.

  At a branch (Rules Prog_Then and Prog_Else):
  - the guard has ONE value ec' at every budget from some threshold on, so
    the formula Rule If reads off the guard does not depend on the budget. It
    has to be one value: the arms below are evaluated under Φ ∧ pc, and a
    formula that changed with the budget would change the path condition the
    recursion runs under. It cannot be every budget: at Fin 0 the guard has
    only the undefined value, and no formula reads off that.
  - the model reads the guard's value the same way it reads the guard. This
    is what eval_models_cond proves at the unlimited budget; here it is asked
    for directly, because the guard is evaluated at a finite budget and that
    lemma does not reach there.
  - the arm the model does NOT take is budget-total. This is the whole point
    of the budget, and the only place the predicate tolerates a loop.

  At the bottom (Rule Prog_Leaf): the term is not a branch, it is the
  concretion's counterpart, and it is not stuck. leaf_progressive in Section
  13.2 is what says the last part, and it offers two ways to say it. Either
  the leaf makes no call to the solver - no branch, no case, no cast, no
  primitive operation - and then it is not stuck for free, because the
  concrete run the theorem is handed already proves that
  (solver_free_completeness). Or the leaf does call the solver, and then all
  this development can ask of it is a value at the unlimited budget.

  THE SECOND ALTERNATIVE STILL SAYS "CONVERGES", AND THAT IS TOO MUCH. It is
  what is left after the first alternative has taken the straight-line code
  away. Section 13.2 says exactly which step blocks the rest: merge, and the
  two other opaque solver functions, over which no syntactic property of a
  term survives.

  WHY THE PREDICATE MENTIONS e_con. It has to know which arm the model takes,
  because only the other arm may loop. The verdict is models_cond σ S ec for
  one arm and models_not_cond σ S ec for the other, and this development
  cannot prove those two are exclusive. σ ⊨ pc is pc_value σ pc = lit_true
  and σ ⊨ ¬ pc is prim_value op_not (pc_value σ pc :: nil) = lit_true, and
  nothing here is assumed about prim_value op_not, so both can hold at once.
  Ruling that out would need one more equation about the solver's negation,
  which this development deliberately does not add. So the branch the
  predicate descends into cannot be read off the symbolic side alone, and the
  concretion is what picks it. progressive_contains below shows the cost is
  nothing: the predicate already implies the concretion it mentions.
*)
Inductive progressive (σ : valuation) (S : symvars)
  : path_condition -> environment -> expr -> expr -> Prop :=
  | Prog_Leaf : forall Φ Γ e e_con,
      is_if e = false ->
      contains σ S e e_con ->
      leaf_progressive Φ Γ e ->
      progressive σ S Φ Γ e e_con
  | Prog_Then : forall Φ Γ ec et ef ec' pc e_con,
      (exists h, forall n, (h <= n)%nat -> eval (Fin n) Φ Γ ec ec') ->
      models_cond σ S ec ->
      models_cond σ S ec' ->
      expr_to_pc Γ ec' = Some pc ->
      budget_total (Φ ∧ ¬ pc) Γ ef ->
      progressive σ S (Φ ∧ pc) Γ et e_con ->
      progressive σ S Φ Γ (EIf ec et ef) e_con
  | Prog_Else : forall Φ Γ ec et ef ec' pc e_con,
      (exists h, forall n, (h <= n)%nat -> eval (Fin n) Φ Γ ec ec') ->
      models_not_cond σ S ec ->
      models_not_cond σ S ec' ->
      expr_to_pc Γ ec' = Some pc ->
      budget_total (Φ ∧ pc) Γ et ->
      progressive σ S (Φ ∧ ¬ pc) Γ ef e_con ->
      progressive σ S Φ Γ (EIf ec et ef) e_con.

(** The hypothesis already carries the concretion it is stated against. *)
Lemma progressive_contains : forall σ S Φ Γ e e_con,
  progressive σ S Φ Γ e e_con -> contains σ S e e_con.
Proof.
  intros σ S Φ Γ e e_con H. induction H.
  - assumption.
  - apply Cont_If_True; assumption.
  - apply Cont_If_False; assumption.
Qed.

(**
  The leaf clause this predicate used to carry asked the leaf for a value at
  the unlimited budget. It is still a rule of the predicate, derived rather
  than assumed, so nothing that satisfied the old hypothesis fails the new
  one: the hypothesis of the completeness theorem only got weaker.
*)
Lemma Prog_Leaf_converging : forall σ S Φ Γ e e_con,
  is_if e = false ->
  contains σ S e e_con ->
  (exists v, Φ ; Γ ⊢ e ⇓ v) ->
  progressive σ S Φ Γ e e_con.
Proof.
  intros σ S Φ Γ e e_con Hnotif Hcont Hv.
  apply Prog_Leaf; [exact Hnotif | exact Hcont | apply leaf_progressive_of_terminating; exact Hv].
Qed.

(** ------------------------------------------------------------------------- *)
(** 13.4 Completeness, Upward Closed in the Budget                            *)
(** ------------------------------------------------------------------------- *)

(**
  The statement is upward closed on purpose. "Some budget works" does not
  survive the induction, for the same reason it did not survive the induction
  in eval_fin_of_inf_fix: a bigger budget is not always safe, so the only
  claim a branch can pass up to the branch above is "every budget from here
  on works". Rule If then combines the three budgets its premises report -
  the guard, the taken arm and the untaken arm - with max and spends one more
  on itself.

  The value found at budget n is allowed to depend on n. It has to be: the
  arm the model skips answers something different at every budget, and that
  answer sits inside the value. What does not depend on n is the concretion:
  Rule Cont_If_True never looks at the arm it did not take, so whatever the
  skipped arm answered, the value still matches the concrete one.

  Where the budget comes from at the bottom. The leaf has an unlimited-budget
  derivation - it was assumed to have one, or, for straight-line code, the
  concrete run gives it one through leaf_progressive_converges. Then
  concore_soundness gives it a concrete value, and
  concore_eval_deterministic identifies that value with the one the theorem
  was handed - a concrete program has at most one. eval_inf_has_budget then
  turns the leaf's unlimited-budget derivation into a finite one, and its
  threshold is the budget the whole recursion is built on.
*)
Lemma completeness_upward : forall σ S Φ Γs e_sym e_con,
  progressive σ S Φ Γs e_sym e_con ->
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
    [ Φ Γ e e_con Hnotif Hcont Hleaf
    | Φ Γ ec et ef ec' pc e_con Hguard Hmc Hmc' Hpc Htot Hns IH
    | Φ Γ ec et ef ec' pc e_con Hguard Hmnc Hmnc' Hpc Htot Hns IH ];
    intros Γc v_con Hmod Henv Hcon Hevalc.
  - (* the leaf: soundness carries the concrete run back, determinism pins the value *)
    destruct (leaf_progressive_converges Φ Γ Γc σ S e e_con v_con
                Hmod Henv Hcont Hevalc Hleaf) as [v Hv].
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
    destruct Hguard as [h0 Hh0].
    exists (Datatypes.S (Nat.max h0 (Nat.max h1 h2))). intros n Hn. destruct n as [| m]; [lia |].
    destruct (Hh1 m ltac:(lia)) as [et' [Het' Hcet']].
    destruct (Hh2 m ltac:(lia)) as [ef' Hef'].
    exists (EIf ec' et' ef'). split.
    + eapply Eval_If;
        [ simpl; apply Hh0; lia | exact Hpc | simpl; exact Het' | simpl; exact Hef' ].
    + apply Cont_If_True; [exact Hmc' | exact Hcet'].
  - (* the model takes the else-arm *)
    assert (Hpcmod : σ ⊨ (¬ pc)) by (eapply models_not_cond_pc; eassumption).
    assert (Hmod_and : σ ⊨ (Φ ∧ ¬ pc)) by (apply models_and; assumption).
    destruct (IH Γc v_con Hmod_and Henv Hcon Hevalc) as [h1 Hh1].
    destruct Htot as [h2 Hh2].
    destruct Hguard as [h0 Hh0].
    exists (Datatypes.S (Nat.max h0 (Nat.max h1 h2))). intros n Hn. destruct n as [| m]; [lia |].
    destruct (Hh1 m ltac:(lia)) as [ef' [Hef' Hcef']].
    destruct (Hh2 m ltac:(lia)) as [et' Het'].
    exists (EIf ec' et' ef'). split.
    + eapply Eval_If;
        [ simpl; apply Hh0; lia | exact Hpc | simpl; exact Het' | simpl; exact Hef' ].
    + apply Cont_If_False; [exact Hmnc' | exact Hcef'].
Qed.

(**
  Completeness of symbolic execution.

  The concretion hypothesis is listed even though progressive_contains derives
  it from the no-stuck hypothesis. It is what the theorem is about, and
  leaving it out would hide the statement inside a predicate.
*)
Theorem concore_completeness : forall Φ Γs Γc σ S e_sym e_con v_con,
  σ ⊨ Φ ->
  contains_env σ S Γs Γc ->
  contains σ S e_sym e_con ->
  concore_expr e_con ->
  progressive σ S Φ Γs e_sym e_con ->
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
  progressive σ S Φ · e_sym e_con ->
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
      no derivation. Since the leaf clause was weakened, the reason has moved:
      see the note on stuck_arm_has_no_concrete_value at the end of the
      section for where it moved to, and why the theorem is still not saying
      anything about a stuck program.

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
  inversion Heval; subst; [congruence | reflexivity | no_con_head | congruence].
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

  Lemma witness_progressive : progressive σ Sv Φ · live_branch (ELit l').
  Proof.
    eapply Prog_Then with (ec' := EVar x) (pc := PCVar x).
    - exists 1%nat. intros n Hn. destruct n as [| m]; [lia |]. apply Eval_SymVar. reflexivity.
    - exact guard_judged.
    - exact guard_judged.
    - reflexivity.
    - exists 0%nat. intros n _. apply self_app_has_value_at_every_budget.
    - apply Prog_Leaf; [reflexivity | apply Cont_Lit |].
      apply leaf_progressive_of_terminating. exists (ELit l'). apply Eval_Lit.
  Qed.

  (** The same witness through the other half of the leaf clause. The literal
      makes no call to the solver, so nothing about it has to be shown. *)
  Lemma witness_progressive_solver_free : progressive σ Sv Φ · live_branch (ELit l').
  Proof.
    eapply Prog_Then with (ec' := EVar x) (pc := PCVar x).
    - exists 1%nat. intros n Hn. destruct n as [| m]; [lia |]. apply Eval_SymVar. reflexivity.
    - exact guard_judged.
    - exact guard_judged.
    - reflexivity.
    - exists 0%nat. intros n _. apply self_app_has_value_at_every_budget.
    - apply Prog_Leaf; [reflexivity | apply Cont_Lit |].
      apply leaf_progressive_of_solver_free; [apply SF_Lit | apply SFEnv_Empty].
  Qed.

  (* ================= (b) completeness applies to it ====================== *)

  Corollary witness_completeness_instance :
    exists k v_sym, eval (Fin k) Φ · live_branch v_sym /\ contains σ Sv v_sym (ELit l').
  Proof.
    eapply concore_completeness_top with (e_con := ELit l').
    - exact HmodPhi.
    - apply Cont_If_True; [exact guard_judged | apply Cont_Lit].
    - apply Con_Lit.
    - exact witness_progressive.
    - apply Eval_Lit.
  Qed.

  (** The budget the recursion computes here is two, and this is what it
      derives: Rule If spends one level, the guard and the taken arm spend the
      second one on a rule that finishes, and the looping arm spends it on
      Rule App-Spine, whose premises then answer by Rule Out-Of-Fuel. The
      concretion never looks at that answer. *)
  Lemma witness_budget_is_two :
    eval (Fin 2) Φ · live_branch (EIf (EVar x) (ELit l') (EBot BUndefined))
    /\ contains σ Sv (EIf (EVar x) (ELit l') (EBot BUndefined)) (ELit l').
  Proof.
    split.
    - eapply Eval_If with (pc_c := PCVar x).
      + apply Eval_SymVar. reflexivity.
      + reflexivity.
      + apply Eval_Lit.
      + unfold self_app. eapply Eval_AppSpine with (ef' := EBot BUndefined);
          [apply self_app_fun_not_whnf | reflexivity | apply Eval_OutOfFuel
          | apply Eval_OutOfFuel].
    - apply Cont_If_True; [exact guard_judged | apply Cont_Lit].
  Qed.

  (** And every budget from two on works, which is what completeness_upward
      claims. The value changes with the budget; the concretion does not. *)
  Lemma witness_every_budget : forall n, (2 <= n)%nat ->
    exists v, eval (Fin n) Φ · live_branch v /\ contains σ Sv v (ELit l').
  Proof.
    intros n Hn. destruct n as [| [| m]]; [lia | lia |].
    destruct (self_app_has_value_at_every_budget (Datatypes.S m) (Φ ∧ ¬ PCVar x) ·)
      as [vf Hvf].
    exists (EIf (EVar x) (ELit l') vf). split.
    - eapply Eval_If with (pc_c := PCVar x);
        [apply Eval_SymVar; reflexivity | reflexivity | apply Eval_Lit | exact Hvf].
    - apply Cont_If_True; [exact guard_judged | apply Cont_Lit].
  Qed.

  (** Below two the bound is too tight. At Fin 0 the whole program answers
      undefined, and at Fin 1 Rule If has its premises at Fin 0, where the
      guard has no formula to read. *)
  Lemma witness_budget_below_two_misses : forall n v,
    (n < 2)%nat -> eval (Fin n) Φ · live_branch v -> ~ contains σ Sv v (ELit l').
  Proof.
    intros n v Hn Hv. destruct n as [| [| m]]; [| | lia].
    - inversion Hv; subst. intros Hc. inversion Hc; subst; kill_denote.
    - exfalso. unfold live_branch in Hv. inversion Hv; subst.
      + no_con_head.
      + match goal with
        | [ Hc : eval _ _ _ (EVar x) ?c, Hp : expr_to_pc _ ?c = Some _ |- _ ] =>
            inversion Hc; subst; simpl in Hp; discriminate Hp
        end.
      + rewrite (models_sat σ Φ HmodPhi) in *. discriminate.
  Qed.

  (** The budget is not decoration: at the unlimited budget this program has
      no value at all, because Rule If cannot get past the looping arm. So
      the finite budget in the theorem is carrying the whole statement here. *)
  Lemma witness_has_no_unlimited_value : ~ (exists v, Φ ; · ⊢ live_branch ⇓ v).
  Proof.
    assert (HsatPhi : sat Φ = true) by (apply models_sat with (σ := σ); exact HmodPhi).
    intros [v Hv]. unfold live_branch in Hv.
    inversion Hv as [| | | | | | | | | | | | | kf Φ0 Γ0 ec0 et0 ef0 ec' et' ef' pc_c
                       Hc Hpc Ht Hf | | kf Φ0 Γ0 e0 Hunsat | | |]; subst.
    - no_con_head.
    - assert (Hec : ec' = EVar x)
        by (inversion Hc; subst; [discriminate | reflexivity | no_con_head | congruence]).
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
    ~ progressive σ Sv Φ · stuck_branch (ELit l').
  Proof.
    assert (HsatPhi : sat Φ = true) by (apply models_sat with (σ := σ); exact HmodPhi).
    intros H. inversion H as
      [ Φ0 Γ0 e0 ec0 Hnotif Hcont Hval
      | Φ0 Γ0 ec0 et0 ef0 ec' pc e_con Hguard Hmc Hmc' Hpc Htot Hns
      | Φ0 Γ0 ec0 et0 ef0 ec' pc e_con Hguard Hmnc Hmnc' Hpc Htot Hns ]; subst.
    - discriminate Hnotif.
    - (* the model takes the literal arm, so the stuck arm must be budget-total *)
      destruct Hguard as [hg Hg].
      assert (Hec : ec' = EVar x)
        by (eapply eval_symvar_fin_same with (k := hg) (Γ := ·);
            [reflexivity | exact HsatPhi | apply (Hg (Datatypes.S hg)); lia]).
      subst ec'. simpl in Hpc. injection Hpc as Hpc. subst pc.
      destruct Htot as [h Hh].
      destruct (Hh (Datatypes.S h) ltac:(lia)) as [v Hv].
      eapply app_lit_no_value_fin; [exact Hfeas | exact Hv].
    - (* the model takes the stuck arm, so the stuck arm is the leaf, and the
         leaf has to be the concretion's counterpart. The other arm's literal
         is the concretion here, and applying a literal is not a literal. *)
      destruct Hguard as [hg Hg].
      assert (Hec : ec' = EVar x)
        by (eapply eval_symvar_fin_same with (k := hg) (Γ := ·);
            [reflexivity | exact HsatPhi | apply (Hg (Datatypes.S hg)); lia]).
      subst ec'. simpl in Hpc. injection Hpc as Hpc. subst pc.
      inversion Hns as [ Φ1 Γ1 e1 ec1 Hnotif1 Hcont1 Hleaf | | ]; subst.
      + unfold stuck_arm in Hcont1. inversion Hcont1; subst.
        match goal with
        | [ Hun : unspool_app _ (@nil expr) = (EPrimOp _, _) |- _ ] =>
            simpl in Hun; discriminate Hun
        end.
  Qed.

  (**
    Where the weight moved.

    The stuck arm used to be refused because the leaf clause demanded a value
    and this arm has none. The leaf clause no longer demands one of code that
    calls no solver, and this arm calls none, so the refusal above now comes
    from the concretion instead: the leaf must be the counterpart of the
    concrete term the theorem runs, and this leaf is not.

    Nothing is lost, because the concrete run is the other place the same
    fact is written down. A stuck arm that IS its own concretion does satisfy
    the predicate now - and then completeness says nothing about it, because
    its concrete run has no value either, which is the lemma below. That is
    the whole point of the weakening: for straight-line code, "not stuck" is
    something the concrete run already says, so the hypothesis should not ask
    for it a second time.
  *)
  Lemma stuck_arm_has_no_concrete_value : forall v, ~ (⊢ᶜ stuck_arm ⇓ᶜ v).
  Proof.
    intros v Hv. unfold stuck_arm, eval_con in Hv.
    eapply app_lit_no_value_inf; [apply sat_pc_true | exact Hv].
  Qed.

End CompletenessNonVacuity.
