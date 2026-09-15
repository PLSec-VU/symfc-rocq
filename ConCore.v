(** ========================================================================= *)
(** ConCore: Concrete Subset Calculus of SymCore                              *)
(**                                                                           *)
(** POPL Revision: Soundness and Completeness of Symbolic Execution           *)
(**                                                                           *)
(** Rather than introducing a separate AST and an inductive simulation        *)
(** relation (contains), ConCore is formalized directly as an inductive       *)
(** syntactic restriction (subset) of SymCore:                                *)
(** 1. Removal of symbolic branching (EIf).                                  *)
(** 2. Source-level programs also exclude runtime thunks (EThunk).           *)
(** ========================================================================= *)

From SymCoreTheory Require Import SymCore.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.PeanoNat.
Import ListNotations.

Section ConCore.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}
  {reduce_prim_solvable_law : ReducePrimSolvable}
  {reduce_prim_saturated_law : ReducePrimSaturated}.

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
    excluding runtime thunks (EThunk), which include lambda closures, and
    symbolic branching (EIf). *)
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

Lemma not_source_thunk : forall Γ e, ~ source_expr (EThunk Γ e).
Proof.
  intros Γ e H.
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

Lemma concore_expr_thunk : forall Γ e, concore_expr (EThunk Γ e) -> concore_expr e.
Proof.
  intros Γ e H. inversion H; subst. assumption.
Qed.

Lemma concore_expr_thunk_env : forall Γ e, concore_expr (EThunk Γ e) -> concrete_env Γ.
Proof.
  intros Γ e H. inversion H; subst. assumption.
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
(** 6. Closed Programs                                                         *)
(** ========================================================================= *)

(**
  SymCore treats a variable that Γ does not bind as a symbolic variable (Rule
  Sym-Var). A concrete program has no symbolic variable: every variable it
  reads is bound by a binder of the term or by the environment it runs in.
*)

Inductive scoped : list var -> expr -> Prop :=
  | Scoped_Var : forall L x, In x L -> scoped L (EVar x)
  | Scoped_Lit : forall L l, scoped L (ELit l)
  | Scoped_PrimOp : forall L p, scoped L (EPrimOp p)
  | Scoped_Con : forall L d, scoped L (ECon d)
  | Scoped_App : forall L f a, scoped L f -> scoped L a -> scoped L (EApp f a)
  | Scoped_Lam : forall L x body, scoped (x :: L) body -> scoped L (ELam x body)
  | Scoped_Case : forall L es alts,
      scoped L es -> Forall (scoped_alt L) alts -> scoped L (ECase es alts)
  | Scoped_Cast : forall L e γ, scoped L e -> scoped L (ECast e γ)
  | Scoped_Coercion : forall L γ, scoped L (ECoercion γ)
  | Scoped_Type : forall L τ, scoped L (EType τ)
  | Scoped_If : forall L ec et ef,
      scoped L ec -> scoped L et -> scoped L ef -> scoped L (EIf ec et ef)
  | Scoped_Bot : forall L b, scoped L (EBot b)
  | Scoped_Thunk : forall L Γ e,
      scoped_env Γ -> scoped (dom_env Γ) e -> scoped L (EThunk Γ e)

with scoped_alt : list var -> alt -> Prop :=
  | Scoped_Alt : forall L d xs ep, scoped (xs ++ L) ep -> scoped_alt L (Alt d xs ep)

with scoped_env : environment -> Prop :=
  | Scoped_Env_Empty : scoped_env ·
  | Scoped_Env_Extend : forall x Γ e rest,
      scoped_env Γ -> scoped (dom_env Γ) e -> scoped_env rest ->
      scoped_env (ExtendEnv x (MkClosure Γ e) rest).

Definition closed_term (e : expr) : Prop := scoped nil e.

Definition closed_program (Γ : environment) (e : expr) : Prop :=
  scoped_env Γ /\ scoped (dom_env Γ) e.

(** ------------------------------------------------------------------------- *)
(** Symbolic scoping: every free variable is bound or symbolic                 *)
(** ------------------------------------------------------------------------- *)

(**
  The symbolic analogue of scoped. A free variable is allowed when it is bound
  (In x L) OR when it is one of the symbolic variables (S x = true). Everything
  else mirrors scoped. This is what a symbolic program keeps: it has no junk
  free variable, only bound variables and the SMT unknowns. Unlike scoped, a
  symbolic branch EIf is allowed, because symbolic evaluation builds branches.
*)
Inductive sym_scoped (S : symvars) : list var -> expr -> Prop :=
  | SymScoped_Var : forall L x, In x L \/ S x = true -> sym_scoped S L (EVar x)
  | SymScoped_Lit : forall L l, sym_scoped S L (ELit l)
  | SymScoped_PrimOp : forall L p, sym_scoped S L (EPrimOp p)
  | SymScoped_Con : forall L d, sym_scoped S L (ECon d)
  | SymScoped_App : forall L f a, sym_scoped S L f -> sym_scoped S L a -> sym_scoped S L (EApp f a)
  | SymScoped_Lam : forall L x body, sym_scoped S (x :: L) body -> sym_scoped S L (ELam x body)
  | SymScoped_Case : forall L es alts,
      sym_scoped S L es -> Forall (sym_scoped_alt S L) alts -> sym_scoped S L (ECase es alts)
  | SymScoped_Cast : forall L e γ, sym_scoped S L e -> sym_scoped S L (ECast e γ)
  | SymScoped_Coercion : forall L γ, sym_scoped S L (ECoercion γ)
  | SymScoped_Type : forall L τ, sym_scoped S L (EType τ)
  | SymScoped_If : forall L ec et ef,
      sym_scoped S L ec -> sym_scoped S L et -> sym_scoped S L ef -> sym_scoped S L (EIf ec et ef)
  | SymScoped_Bot : forall L b, sym_scoped S L (EBot b)
  | SymScoped_Thunk : forall L Γ e,
      sym_scoped_env S Γ -> sym_scoped S (dom_env Γ) e -> sym_scoped S L (EThunk Γ e)

with sym_scoped_alt (S : symvars) : list var -> alt -> Prop :=
  | SymScoped_Alt : forall L d xs ep, sym_scoped S (xs ++ L) ep -> sym_scoped_alt S L (Alt d xs ep)

with sym_scoped_env (S : symvars) : environment -> Prop :=
  | SymScoped_Env_Empty : sym_scoped_env S ·
  | SymScoped_Env_Extend : forall x Γ e rest,
      sym_scoped_env S Γ -> sym_scoped S (dom_env Γ) e -> sym_scoped_env S rest ->
      sym_scoped_env S (ExtendEnv x (MkClosure Γ e) rest).

Definition symbolic_program (S : symvars) (Γ : environment) (e : expr) : Prop :=
  sym_scoped_env S Γ /\ sym_scoped S (dom_env Γ) e.

(** With no symbolic variable, symbolic scoping is ordinary scoping. This is
    what lets the closed-input scope laws come out of the open ones. *)
Definition no_symvars : symvars := fun _ => false.

Fixpoint sym_scoped_no_symvars L e (H : sym_scoped no_symvars L e) {struct H} : scoped L e
with sym_scoped_alt_no_symvars L a (H : sym_scoped_alt no_symvars L a) {struct H} : scoped_alt L a
with sym_scoped_env_no_symvars Γ (H : sym_scoped_env no_symvars Γ) {struct H} : scoped_env Γ.
Proof.
  - destruct H as [L x Hx | | | | L f a Hf Ha | L x body Hb | L es alts Hes Halts
                  | L e γ He | | | L ec et ef Hc Ht Hff | | L Γ e HΓ He].
    + apply Scoped_Var. destruct Hx as [Hx | Hx]; [exact Hx | discriminate Hx].
    + apply Scoped_Lit.
    + apply Scoped_PrimOp.
    + apply Scoped_Con.
    + apply Scoped_App; [exact (sym_scoped_no_symvars _ _ Hf) | exact (sym_scoped_no_symvars _ _ Ha)].
    + apply Scoped_Lam. exact (sym_scoped_no_symvars _ _ Hb).
    + apply Scoped_Case; [exact (sym_scoped_no_symvars _ _ Hes) |].
      induction Halts as [| a0 alts0 Ha0 _ IH]; constructor;
        [exact (sym_scoped_alt_no_symvars _ _ Ha0) | exact IH].
    + apply Scoped_Cast. exact (sym_scoped_no_symvars _ _ He).
    + apply Scoped_Coercion.
    + apply Scoped_Type.
    + apply Scoped_If; [exact (sym_scoped_no_symvars _ _ Hc) | exact (sym_scoped_no_symvars _ _ Ht)
                       | exact (sym_scoped_no_symvars _ _ Hff)].
    + apply Scoped_Bot.
    + apply Scoped_Thunk; [exact (sym_scoped_env_no_symvars _ HΓ) | exact (sym_scoped_no_symvars _ _ He)].
  - destruct H as [L d xs ep Hep]. apply Scoped_Alt. exact (sym_scoped_no_symvars _ _ Hep).
  - destruct H as [| x Γ e rest HΓ He Hrest].
    + apply Scoped_Env_Empty.
    + apply Scoped_Env_Extend;
        [exact (sym_scoped_env_no_symvars _ HΓ) | exact (sym_scoped_no_symvars _ _ He)
        | exact (sym_scoped_env_no_symvars _ Hrest)].
Qed.

Fixpoint scoped_no_symvars L e (H : scoped L e) {struct H} : sym_scoped no_symvars L e
with scoped_alt_no_symvars L a (H : scoped_alt L a) {struct H} : sym_scoped_alt no_symvars L a
with scoped_env_no_symvars Γ (H : scoped_env Γ) {struct H} : sym_scoped_env no_symvars Γ.
Proof.
  - destruct H as [L x Hx | | | | L f a Hf Ha | L x body Hb | L es alts Hes Halts
                  | L e γ He | | | L ec et ef Hc Ht Hff | | L Γ e HΓ He].
    + apply SymScoped_Var. left. exact Hx.
    + apply SymScoped_Lit.
    + apply SymScoped_PrimOp.
    + apply SymScoped_Con.
    + apply SymScoped_App; [exact (scoped_no_symvars _ _ Hf) | exact (scoped_no_symvars _ _ Ha)].
    + apply SymScoped_Lam. exact (scoped_no_symvars _ _ Hb).
    + apply SymScoped_Case; [exact (scoped_no_symvars _ _ Hes) |].
      induction Halts as [| a0 alts0 Ha0 _ IH]; constructor;
        [exact (scoped_alt_no_symvars _ _ Ha0) | exact IH].
    + apply SymScoped_Cast. exact (scoped_no_symvars _ _ He).
    + apply SymScoped_Coercion.
    + apply SymScoped_Type.
    + apply SymScoped_If; [exact (scoped_no_symvars _ _ Hc) | exact (scoped_no_symvars _ _ Ht)
                          | exact (scoped_no_symvars _ _ Hff)].
    + apply SymScoped_Bot.
    + apply SymScoped_Thunk; [exact (scoped_env_no_symvars _ HΓ) | exact (scoped_no_symvars _ _ He)].
  - destruct H as [L d xs ep Hep]. apply SymScoped_Alt. exact (scoped_no_symvars _ _ Hep).
  - destruct H as [| x Γ e rest HΓ He Hrest].
    + apply SymScoped_Env_Empty.
    + apply SymScoped_Env_Extend;
        [exact (scoped_env_no_symvars _ HΓ) | exact (scoped_no_symvars _ _ He)
        | exact (scoped_env_no_symvars _ Hrest)].
Qed.

(** ========================================================================= *)
(** 7. Properties of Closed Programs                                           *)
(** ========================================================================= *)

Fixpoint scoped_weaken L L' e (H : scoped L e) {struct H} : incl L L' -> scoped L' e
with scoped_alt_weaken L L' a (H : scoped_alt L a) {struct H} : incl L L' -> scoped_alt L' a.
Proof.
  - destruct H as [L x Hx | L l | L p | L d | L f a Hf Ha | L x body Hb | L es alts Hes Halts
                  | L e γ He | L γ | L τ | L ec et ef Hc Ht Hf | L b
                  | L Γ e HΓ He];
      intros Hi.
    + apply Scoped_Var. exact (Hi x Hx).
    + apply Scoped_Lit.
    + apply Scoped_PrimOp.
    + apply Scoped_Con.
    + apply Scoped_App; [exact (scoped_weaken _ _ _ Hf Hi) | exact (scoped_weaken _ _ _ Ha Hi)].
    + apply Scoped_Lam. apply (scoped_weaken _ _ _ Hb).
      intros y [Hy | Hy]; [left; exact Hy | right; exact (Hi y Hy)].
    + apply Scoped_Case; [exact (scoped_weaken _ _ _ Hes Hi) |].
      clear Hes. induction Halts as [| a0 alts0 Ha0 _ IH]; constructor;
        [exact (scoped_alt_weaken _ _ _ Ha0 Hi) | exact IH].
    + apply Scoped_Cast. exact (scoped_weaken _ _ _ He Hi).
    + apply Scoped_Coercion.
    + apply Scoped_Type.
    + apply Scoped_If; [exact (scoped_weaken _ _ _ Hc Hi) | exact (scoped_weaken _ _ _ Ht Hi)
                       | exact (scoped_weaken _ _ _ Hf Hi)].
    + apply Scoped_Bot.
    + apply Scoped_Thunk; assumption.
  - destruct H as [L d xs ep Hep]. intros Hi.
    apply Scoped_Alt. apply (scoped_weaken _ _ _ Hep).
    intros y Hy. apply in_app_or in Hy as [Hy | Hy]; apply in_or_app; [left; exact Hy | right; exact (Hi y Hy)].
Qed.

Lemma closed_term_scoped : forall L e, closed_term e -> scoped L e.
Proof. intros L e H. apply (scoped_weaken nil L e H). intros y []. Qed.

Lemma scoped_thunk_any : forall L L' Γ e, scoped L (EThunk Γ e) -> scoped L' (EThunk Γ e).
Proof. intros L L' Γ e H. inversion H; subst. apply Scoped_Thunk; assumption. Qed.

Lemma lookup_env_in_dom : forall Γ x Γ' e, lookup_env Γ x = Some (Γ', e) -> In x (dom_env Γ).
Proof.
  induction Γ as [| y [Γ0 e0] rest IH]; intros x Γ' e H; simpl in H; [discriminate |].
  simpl. destruct (string_dec x y) as [-> | _]; [left; reflexivity | right; exact (IH _ _ _ H)].
Qed.

Lemma in_dom_lookup_env : forall Γ x, In x (dom_env Γ) -> lookup_env Γ x <> None.
Proof.
  induction Γ as [| y [Γ0 e0] rest IH]; intros x H; simpl in H; [contradiction |].
  simpl. destruct (string_dec x y) as [_ | Hne]; [discriminate |].
  destruct H as [-> | H]; [congruence | exact (IH x H)].
Qed.

Lemma lookup_env_scoped : forall Γ x Γ' e,
  scoped_env Γ -> lookup_env Γ x = Some (Γ', e) -> scoped_env Γ' /\ scoped (dom_env Γ') e.
Proof.
  intros Γ x Γ' e H. induction H as [| y Γ0 e0 rest H0 IH0 He0 Hrest IH]; intros Hl;
    simpl in Hl; [discriminate |].
  destruct (string_dec x y); [injection Hl as <- <-; split; assumption | exact (IH Hl)].
Qed.

Lemma unspool_app_scoped : forall L e acc head args,
  unspool_app e acc = (head, args) ->
  scoped L e -> Forall (scoped L) acc ->
  scoped L head /\ Forall (scoped L) args.
Proof.
  intros L. induction e; intros acc head args Hu He Hacc; simpl in Hu;
    try (injection Hu as <- <-; split; assumption).
  inversion He; subst.
  apply (IHe1 (e2 :: acc)); [exact Hu | assumption | constructor; assumption].
Qed.

Lemma scoped_fold_left_app : forall L args h,
  Forall (scoped L) args -> scoped L h -> scoped L (fold_left EApp args h).
Proof.
  intros L args. induction args as [| a tl IH]; intros h Hargs Hh; simpl; [exact Hh |].
  inversion Hargs; subst. apply IH; [assumption | apply Scoped_App; assumption].
Qed.

Lemma scoped_con_value : forall L Γ d args,
  scoped_env Γ -> Forall (scoped (dom_env Γ)) args ->
  scoped L (make_con_app d (map (delay Γ) args)).
Proof.
  intros L Γ d args HΓ Hargs. apply scoped_fold_left_app; [| apply Scoped_Con].
  induction Hargs as [| a tl Ha _ IH]; simpl; constructor; [| exact IH].
  destruct a; try (apply Scoped_Thunk; assumption).
  exact (scoped_thunk_any _ _ _ _ Ha).
Qed.

Lemma dom_env_extend_multi : forall xs ea Γ Γa,
  dom_env (extend_env_multi Γ xs ea Γa) = xs ++ dom_env Γ.
Proof.
  induction xs as [| x xs IH]; intros ea Γ Γa; [reflexivity |].
  destruct ea as [| a ea]; simpl; rewrite IH; reflexivity.
Qed.

Lemma scoped_env_extend_multi : forall xs ea Γ Γa,
  scoped_env Γ -> scoped_env Γa -> Forall (scoped (dom_env Γa)) ea ->
  scoped_env (extend_env_multi Γ xs ea Γa).
Proof.
  induction xs as [| x xs IH]; intros ea Γ Γa HΓ HΓa Hea; [exact HΓ |].
  destruct ea as [| a ea]; simpl.
  - apply Scoped_Env_Extend; [exact HΓa | apply Scoped_Bot | apply IH; auto].
  - inversion Hea; subst.
    apply Scoped_Env_Extend; [exact HΓa | assumption | apply IH; auto].
Qed.

Lemma find_alt_scoped : forall L d alts xs ep,
  Forall (scoped_alt L) alts -> find_alt d alts = Some (xs, ep) -> scoped (xs ++ L) ep.
Proof.
  intros L d alts xs ep H. induction H as [| [d' xs' ep'] alts Ha _ IH]; intros Hf;
    simpl in Hf; [discriminate |].
  destruct (string_dec d d'); [injection Hf as <- <-; inversion Ha; subst; assumption | exact (IH Hf)].
Qed.

Lemma closed_term_lits : forall ls, Forall closed_term (map ELit ls).
Proof. induction ls as [| l ls IH]; constructor; [apply Scoped_Lit | exact IH]. Qed.

Lemma closed_program_app_l : forall Γ f a, closed_program Γ (EApp f a) -> closed_program Γ f.
Proof. intros Γ f a [HΓ H]. inversion H; subst. split; assumption. Qed.

Lemma closed_program_app_r : forall Γ f a, closed_program Γ (EApp f a) -> closed_program Γ a.
Proof. intros Γ f a [HΓ H]. inversion H; subst. split; assumption. Qed.

Lemma closed_program_cast : forall Γ e γ, closed_program Γ (ECast e γ) -> closed_program Γ e.
Proof. intros Γ e γ [HΓ H]. inversion H; subst. split; assumption. Qed.

Lemma closed_program_thunk : forall Γ Γ' e, closed_program Γ (EThunk Γ' e) -> closed_program Γ' e.
Proof. intros Γ Γ' e [_ H]. inversion H; subst. split; assumption. Qed.

Lemma closed_program_case_es : forall Γ es alts,
  closed_program Γ (ECase es alts) -> closed_program Γ es.
Proof. intros Γ es alts [HΓ H]. inversion H; subst. split; assumption. Qed.

Lemma closed_program_case_alts : forall Γ es alts,
  closed_program Γ (ECase es alts) -> Forall (scoped_alt (dom_env Γ)) alts.
Proof. intros Γ es alts [_ H]. inversion H; subst. assumption. Qed.

Lemma closed_program_abs : forall Γ Γ' x eb ea,
  closed_program Γ (EApp (EThunk Γ' (ELam x eb)) ea) -> closed_program (extend_env Γ' x Γ ea) eb.
Proof.
  intros Γ Γ' x eb ea [HΓ H]. inversion H as [| | | | L f a Hf Ha | | | | | | | |]; subst.
  inversion Hf as [| | | | | | | | | | | | L1 Γ1 e1 HΓ' Hlam]; subst.
  inversion Hlam as [| | | | | L2 x2 b2 Hb | | | | | | |]; subst.
  split; [apply Scoped_Env_Extend; assumption | exact Hb].
Qed.

Lemma closed_program_push : forall Γ ef γ ea γ_a γ_r,
  closed_program Γ (EApp (ECast ef γ) ea) ->
  closed_program Γ (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r).
Proof.
  intros Γ ef γ ea γ_a γ_r [HΓ H]. inversion H as [| | | | L f a Hf Ha | | | | | | | |]; subst.
  inversion Hf; subst.
  split; [exact HΓ |]. apply Scoped_Cast. apply Scoped_App; [assumption | apply Scoped_Cast; assumption].
Qed.

Lemma closed_program_fold_con : forall Γ e d ea alts xs ep,
  scoped_env Γ -> closed_term e -> Forall (scoped_alt (dom_env Γ)) alts ->
  decompose_con_app e = Some (d, ea) -> find_alt d alts = Some (xs, ep) ->
  closed_program (extend_env_multi Γ xs ea Γ) ep.
Proof.
  intros Γ e d ea alts xs ep HΓ He Halts Hd Hf. split.
  - apply scoped_env_extend_multi; [exact HΓ | exact HΓ |].
    pose proof (proj2 (unspool_app_scoped nil e [] (ECon d) ea (decompose_con_app_unspool e d ea Hd)
                         He (Forall_nil _))) as Hea.
    eapply Forall_impl; [| exact Hea]. intros a Ha. exact (closed_term_scoped _ a Ha).
  - rewrite dom_env_extend_multi. exact (find_alt_scoped _ d alts xs ep Halts Hf).
Qed.

(** ========================================================================= *)
(** 8. Concrete Evaluation Semantics and Preservation                         *)
(** ========================================================================= *)

Definition eval_con (Γ : environment) (e : expr) (v : expr) : Prop :=
  eval Inf pc_true Γ e v.

End ConCore.

Notation "Γ '⊢ᶜ' e '⇓ᶜ' v" := (eval_con Γ e v) (at level 70, no associativity).
Notation "'⊢ᶜ' e '⇓ᶜ' v" := (eval_con · e v) (at level 70, no associativity).

Section ConCore.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}
  {reduce_prim_solvable_law : ReducePrimSolvable}
  {reduce_prim_saturated_law : ReducePrimSaturated}.

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
Class ReducePrimConcore : Prop :=
reduce_prim_concore : forall p args,
  Forall concore_expr args ->
  concore_expr (reduce_prim p args).

Context {reduce_prim_concore_law : ReducePrimConcore}.

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

Class CastExprConcore : Prop :=
cast_expr_concore : forall e γ,
  concore_expr e ->
  concore_expr (cast_expr e γ).

Context {cast_expr_concore_law : CastExprConcore}.

(** The scope laws, in the open form the symbolic side needs: scoped input
    gives scoped output, for a fixed set of symbolic variables S and binder
    list L. A real reducer and a real cast add no variable, so a variable of
    the result was already a variable of an argument, hence bound or symbolic.
    The closed-input form (used by the concrete side) is the special case with
    no symbolic variable. *)
Class ReducePrimScoped : Prop :=
reduce_prim_scoped : forall S L p args,
  Forall (sym_scoped S L) args ->
  sym_scoped S L (reduce_prim p args).

Class CastExprScoped : Prop :=
cast_expr_scoped : forall S L e γ,
  sym_scoped S L e ->
  sym_scoped S L (cast_expr e γ).

Context {reduce_prim_scoped_law : ReducePrimScoped} {cast_expr_scoped_law : CastExprScoped}.

(** The closed-input forms, derived from the open laws with no symbolic
    variable. These keep the concrete-side proofs unchanged. *)
Lemma reduce_prim_scoped_closed : forall p args,
  Forall closed_term args -> closed_term (reduce_prim p args).
Proof.
  intros p args H. apply sym_scoped_no_symvars.
  apply reduce_prim_scoped.
  eapply Forall_impl; [| exact H]. intros a Ha. apply scoped_no_symvars. exact Ha.
Qed.

Lemma cast_expr_scoped_closed : forall e γ,
  closed_term e -> closed_term (cast_expr e γ).
Proof.
  intros e γ H. apply sym_scoped_no_symvars.
  apply cast_expr_scoped. apply scoped_no_symvars. exact H.
Qed.

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
  concore_expr (make_con_app d (map (delay Γ) args)).
Proof.
  intros Γ d args HΓ Hargs. apply concore_fold_left_app; [| apply Con_Con].
  induction Hargs as [| a tl Ha Htl IH]; simpl; constructor; [| exact IH].
  destruct a; try (apply Con_Thunk; assumption). exact Ha.
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

(** A closed term whose formula conversion succeeds mentions no variable: a
    scoped variable is captured by the environment, so expr_to_pc returns None
    on it, and a formula is built only from literals and primitive applications
    of variable-free parts. *)
Lemma expr_to_pc_scoped_no_var : forall Γ e pc,
  scoped (dom_env Γ) e ->
  expr_to_pc Γ e = Some pc ->
  pc_has_var pc = false.
Proof.
  intros Γ e. induction e; intros pc Hsc Hpc; simpl in Hpc; try discriminate.
  - inversion Hsc; subst.
    match goal with [ Hin : In v (dom_env Γ) |- _ ] =>
      pose proof (in_dom_lookup_env Γ v Hin) as Hne end.
    destruct (lookup_env Γ v); [discriminate | congruence].
  - injection Hpc as <-. reflexivity.
  - injection Hpc as <-. reflexivity.
  - inversion Hsc as [| | | | L f a Hscf Hsca | | | | | | | |]; subst.
    destruct (expr_to_pc Γ e1) as [pc1|] eqn:E1; [| discriminate].
    destruct pc1 as [x|l|q qs]; try (destruct (expr_to_pc Γ e2); discriminate).
    destruct (expr_to_pc Γ e2) as [pc2|] eqn:E2; [| discriminate].
    injection Hpc as <-. simpl. rewrite existsb_app. simpl.
    pose proof (IHe1 (PCPrim q qs) Hscf eq_refl) as Hf1. simpl in Hf1.
    pose proof (IHe2 pc2 Hsca eq_refl) as Hf2.
    rewrite Hf1, Hf2. reflexivity.
Qed.

(**
  A pair of mutually recursive fixpoints, not the auto-derived mutual
  induction scheme. Rule App-Prim needs the statement for every argument of
  its Forall2 (eval (dec f) Φ Γ) args args' in order to feed the
  argument-conditional reduce_prim laws, and the derived scheme supplies no
  induction hypothesis under a Forall2.

  The result is a closed ConCore value. It carries both facts at once, because
  a case whose scrutinee is a boolean formula with a variable would build a
  runtime branch (Rule FoldAlts_SymbolicFormula), which is not a ConCore term;
  closedness rules that case out, since a closed formula mentions no variable.
  So closedness is what keeps a concrete run inside ConCore.

  The statement holds at the unlimited budget only, which is why the fuel
  comes in as f0 with an f0 = Inf premise. Rule Out-Of-Fuel answers
  EBot BOutOfFuel, and no ConCore expression is that bottom.
*)
Fixpoint concore_eval_closed_fix (f0 : fuel) (Φ : path_condition) (Γ : environment) (e v : expr)
  (Heval : eval f0 Φ Γ e v) {struct Heval} :
  f0 = Inf -> sat Φ = true -> concrete_env Γ -> concore_expr e -> closed_program Γ e ->
  concore_expr v /\ closed_term v
with concore_fold_closed_fix (f0 : fuel) (Φ : path_condition) (Γ : environment) (e : expr)
  (alts : list alt) (er : expr)
  (Hfold : fold_alts f0 Φ Γ e alts er) {struct Hfold} :
  f0 = Inf -> sat Φ = true -> concrete_env Γ -> concore_expr e -> Forall concore_alt alts ->
  scoped_env Γ -> closed_term e -> Forall (scoped_alt (dom_env Γ)) alts ->
  concore_expr er /\ closed_term er.
Proof.
{
  destruct Heval as
    [ k Φ Γ x Γ' e e' Hlook Heval_x
    | k Φ Γ x Hnone
    | k Φ Γ l
    | k Φ Γ econ d args Hunspool_con
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
    ]; intros Hk0 Hsat Henv Hcon [HΓ Hsc]; try (injection Hk0 as Hk0; subst).
  - (* Eval_Var *)
    destruct (lookup_env_concrete Γ x Γ' e Henv Hlook) as [Henv' He].
    destruct (lookup_env_scoped Γ x Γ' e HΓ Hlook) as [HΓ' Hsc'].
    exact (concore_eval_closed_fix Inf Φ Γ' e e' Heval_x eq_refl Hsat Henv' He (conj HΓ' Hsc')).
  - (* Eval_SymVar: impossible in a closed program *)
    exfalso. inversion Hsc; subst.
    match goal with [Hi : In x _ |- _] => exact (in_dom_lookup_env Γ x Hi Hnone) end.
  - (* Eval_Lit *) split; [apply Con_Lit | apply Scoped_Lit].
  - (* Eval_Con *)
    destruct (unspool_app_concore econ [] (ECon d) args Hunspool_con Hcon (Forall_nil _)) as [_ Hcon_args].
    destruct (unspool_app_scoped _ econ [] (ECon d) args Hunspool_con Hsc (Forall_nil _)) as [_ Hsc_args].
    split; [exact (concore_con_value Γ d args Henv Hcon_args)
           | exact (scoped_con_value nil Γ d args HΓ Hsc_args)].
  - (* Eval_Cast *)
    inversion Hcon; subst. inversion Hsc; subst.
    match goal with [Hc : concore_expr e, Hs : scoped _ e |- _] =>
      destruct (concore_eval_closed_fix Inf Φ Γ e e' Heval_e eq_refl Hsat Henv Hc (conj HΓ Hs))
        as [Hcv Hsv] end.
    split; [apply cast_expr_concore; exact Hcv | apply cast_expr_scoped_closed; exact Hsv].
  - (* Eval_AppAbs *)
    inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | ]; subst.
    inversion Hf as [| | | | | | | | | | | | | Γ0 e0 Henv' Hlam]; subst.
    inversion Hlam as [| | | | | x0 body Hbody | | | | | | | | ]; subst.
    inversion Hsc as [| | | | L0 f0 a0 Hscf Hsca | | | | | | | |]; subst.
    inversion Hscf as [| | | | | | | | | | | | L1 Γ1 e1 HΓ' Hsclam]; subst.
    inversion Hsclam as [| | | | | L2 x2 b2 Hscb | | | | | | |]; subst.
    apply (concore_eval_closed_fix Inf Φ (extend_env Γ' x Γ ea) eb eb' Heval_b eq_refl Hsat).
    + apply concrete_env_extend; assumption.
    + assumption.
    + split; [apply Scoped_Env_Extend; assumption | exact Hscb].
  - (* Eval_AppSpine *)
    inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | ]; subst.
    inversion Hsc as [| | | | L0 f0 a0 Hscf Hsca | | | | | | | |]; subst.
    destruct (concore_eval_closed_fix Inf Φ Γ ef ef' Heval_f eq_refl Hsat Henv Hf (conj HΓ Hscf))
      as [Hcf' Hsf'].
    apply (concore_eval_closed_fix Inf Φ Γ (EApp ef' ea) er Heval_app2 eq_refl Hsat Henv).
    + apply Con_App; assumption.
    + split; [exact HΓ | apply Scoped_App; [apply closed_term_scoped; exact Hsf' | exact Hsca]].
  - (* Eval_Bot *) split; [exact Hcon | apply Scoped_Bot].
  - (* Eval_AppPrim *)
    destruct (unspool_app_concore (EApp ef ea) [] (EPrimOp p) args Hunspool Hcon (Forall_nil _))
      as [_ Hcon_args].
    destruct (unspool_app_scoped _ (EApp ef ea) [] (EPrimOp p) args Hunspool Hsc (Forall_nil _))
      as [_ Hsc_args].
    assert (Hres : Forall concore_expr args' /\ Forall closed_term args').
    { clear Hunspool Harity Hcon Hsc.
      revert Hcon_args Hsc_args.
      induction Hargs as [| a a' tl tl' Ha Htl IH]; intros Hcon_args Hsc_args.
      - split; constructor.
      - inversion Hcon_args as [| a0 tl0 Hcon_a Hcon_tl]; subst.
        inversion Hsc_args as [| a1 tl1 Hsc_a Hsc_tl]; subst.
        destruct (concore_eval_closed_fix Inf Φ Γ a a' Ha eq_refl Hsat Henv Hcon_a (conj HΓ Hsc_a))
          as [Hca Hsa].
        destruct (IH Hcon_tl Hsc_tl) as [Hct Hst].
        split; constructor; assumption. }
    destruct Hres as [Hcon' Hsc'].
    split; [apply reduce_prim_concore; exact Hcon' | apply reduce_prim_scoped_closed; exact Hsc'].
  - (* Eval_Lam *) split; [apply Con_Thunk; assumption | apply Scoped_Thunk; assumption].
  - (* Eval_AppCast *)
    inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | ]; subst.
    inversion Hf as [| | | | | | | e γ0 He | | | | | | ]; subst.
    inversion Hsc as [| | | | L0 f0 a0 Hscf Hsca | | | | | | | |]; subst.
    inversion Hscf as [| | | | | | | L1 e1 γ1 Hsce | | | | |]; subst.
    apply (concore_eval_closed_fix Inf Φ Γ (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r)
             er Heval_pushed eq_refl Hsat Henv).
    + apply Con_Cast. apply Con_App; [assumption | apply Con_Cast; assumption].
    + split; [exact HΓ |].
      apply Scoped_Cast. apply Scoped_App; [assumption | apply Scoped_Cast; assumption].
  - (* Eval_AppIf: a ConCore spine has no branch head *)
    exfalso. apply (not_concore_if ec et ef).
    exact (proj1 (unspool_app_concore _ [] _ args Hunspool_if Hcon (Forall_nil _))).
  - (* Eval_AppBot *)
    inversion Hcon; subst. split; [assumption | apply Scoped_Bot].
  - (* Eval_Case *)
    inversion Hcon as [| | | | | | es0 alts0 Hcon_es Hcon_alts | | | | | | | ]; subst.
    inversion Hsc as [| | | | | | L0 es1 alts1 Hsc_es Hsc_alts | | | | | |]; subst.
    destruct (concore_eval_closed_fix Inf Φ Γ es es' Heval_es eq_refl Hsat Henv Hcon_es (conj HΓ Hsc_es))
      as [Hcon_es' Hsc_es'].
    rewrite (merge_concore_id Γ es' Hcon_es') in Hfold.
    exact (concore_fold_closed_fix Inf Φ Γ es' alts er Hfold eq_refl Hsat Henv Hcon_es' Hcon_alts
             HΓ Hsc_es' Hsc_alts).
  - (* Eval_If: a ConCore expression is never a branch *)
    exfalso. apply (not_concore_if ec et ef). assumption.
  - (* Eval_Coercion *) split; [apply Con_Coercion | apply Scoped_Coercion].
  - (* Eval_Prune *) split; [apply Con_Bot_Unreachable | apply Scoped_Bot].
  - (* Eval_Type *) split; [apply Con_Type | apply Scoped_Type].
  - (* Eval_Thunk *)
    inversion Hcon as [| | | | | | | | | | | | | Γ0 e0 Henv' He]; subst.
    inversion Hsc as [| | | | | | | | | | | | L1 Γ1 e1 HΓ' Hsce]; subst.
    exact (concore_eval_closed_fix Inf Φ Γ' e e' Heval_t eq_refl Hsat Henv' He (conj HΓ' Hsce)).
  - (* Eval_OutOfFuel *) discriminate Hk0.
}
{
  destruct Hfold as
    [ k Φ Γ ec et ef alts et' ef' pc_c Hpc Hfold_t Hfold_f
    | k Φ Γ ec et ef alts Hpc_none
    | k Φ Γ e d ea xs ep alts er Hdec Halt Heval_ep
    | k Φ Γ b alts
    | k Φ Γ e pc alts r Hpc Hvar Hrec
    | k Φ Γ e pc alts r1 r2 Hpc Hvar Har Hf1 Hf2
    | k Φ Γ e alts Hpcnone Hop Hnothead Hnoalt Hnotbot
    ]; intros Hk0 Hsat Henv Hcon Halts HΓ Hsc Hsc_alts; subst k.
  - exfalso. apply (not_concore_if ec et ef). assumption.
  - exfalso. apply (not_concore_if ec et ef). assumption.
  - (* FoldAlts_Con *)
    assert (Hea : Forall concore_expr ea).
    { apply decompose_con_app_concore with (e := e) (d := d); assumption. }
    assert (Hep : concore_expr ep).
    { apply find_alt_concore with (d := d) (alts := alts) (xs := xs); assumption. }
    assert (Hsc_ea : Forall closed_term ea).
    { exact (proj2 (unspool_app_scoped nil e [] (ECon d) ea (decompose_con_app_unspool e d ea Hdec)
                      Hsc (Forall_nil _))). }
    apply (concore_eval_closed_fix Inf Φ (extend_env_multi Γ xs ea Γ) ep er Heval_ep eq_refl Hsat).
    + apply concrete_env_extend_multi; assumption.
    + exact Hep.
    + split.
      * apply scoped_env_extend_multi; [exact HΓ | exact HΓ |].
        eapply Forall_impl; [| exact Hsc_ea]. intros a Ha. exact (closed_term_scoped _ a Ha).
      * rewrite dom_env_extend_multi. exact (find_alt_scoped _ d alts xs ep Hsc_alts Halt).
  - (* FoldAlts_Bot *) split; [exact Hcon | apply Scoped_Bot].
  - (* FoldAlts_GroundFormula *)
    exact (concore_fold_closed_fix Inf Φ Γ (ECon (truth_constructor (pc_closed_value pc))) alts r
             Hrec eq_refl Hsat Henv (Con_Con _) Halts HΓ (Scoped_Con nil _) Hsc_alts).
  - (* FoldAlts_SymbolicFormula: a closed scrutinee's formula has no variable *)
    exfalso.
    pose proof (expr_to_pc_scoped_no_var Γ e pc (closed_term_scoped (dom_env Γ) e Hsc) Hpc) as Hnv.
    rewrite Hnv in Hvar. discriminate.
  - (* FoldAlts_Otherwise *) split; [apply Con_Bot_Undefined | apply Scoped_Bot].
}
Qed.

(** A closed ConCore program evaluates to a ConCore value. *)
Lemma concore_eval_closed : forall Γ e v,
  concrete_env Γ -> concore_expr e -> closed_program Γ e ->
  Γ ⊢ᶜ e ⇓ᶜ v ->
  concore_expr v.
Proof.
  intros Γ e v Henv Hcon Hcl Heval.
  exact (proj1 (concore_eval_closed_fix Inf pc_true Γ e v Heval eq_refl sat_pc_true Henv Hcon Hcl)).
Qed.

(** A closed ConCore program evaluates to a closed value. *)
Lemma closed_eval : forall Γ e v,
  concrete_env Γ -> concore_expr e -> closed_program Γ e ->
  Γ ⊢ᶜ e ⇓ᶜ v ->
  closed_term v.
Proof.
  intros Γ e v Henv Hcon Hcl Heval.
  exact (proj2 (concore_eval_closed_fix Inf pc_true Γ e v Heval eq_refl sat_pc_true Henv Hcon Hcl)).
Qed.

(** ------------------------------------------------------------------------- *)
(** Symbolic scoping is preserved by evaluation                                *)
(** ------------------------------------------------------------------------- *)

Fixpoint sym_scoped_weaken S L L' e (H : sym_scoped S L e) {struct H} : incl L L' -> sym_scoped S L' e
with sym_scoped_alt_weaken S L L' a (H : sym_scoped_alt S L a) {struct H} : incl L L' -> sym_scoped_alt S L' a.
Proof.
  - destruct H as [L x Hx | L l | L p | L d | L f a Hf Ha | L x body Hb | L es alts Hes Halts
                  | L e γ He | L γ | L τ | L ec et ef Hc Ht Hff | L b
                  | L Γ e HΓ He];
      intros Hi.
    + apply SymScoped_Var. destruct Hx as [Hx | Hx]; [left; exact (Hi x Hx) | right; exact Hx].
    + apply SymScoped_Lit.
    + apply SymScoped_PrimOp.
    + apply SymScoped_Con.
    + apply SymScoped_App; [exact (sym_scoped_weaken _ _ _ _ Hf Hi) | exact (sym_scoped_weaken _ _ _ _ Ha Hi)].
    + apply SymScoped_Lam. apply (sym_scoped_weaken _ _ _ _ Hb).
      intros y [Hy | Hy]; [left; exact Hy | right; exact (Hi y Hy)].
    + apply SymScoped_Case; [exact (sym_scoped_weaken _ _ _ _ Hes Hi) |].
      clear Hes. induction Halts as [| a0 alts0 Ha0 _ IH]; constructor;
        [exact (sym_scoped_alt_weaken _ _ _ _ Ha0 Hi) | exact IH].
    + apply SymScoped_Cast. exact (sym_scoped_weaken _ _ _ _ He Hi).
    + apply SymScoped_Coercion.
    + apply SymScoped_Type.
    + apply SymScoped_If; [exact (sym_scoped_weaken _ _ _ _ Hc Hi) | exact (sym_scoped_weaken _ _ _ _ Ht Hi)
                          | exact (sym_scoped_weaken _ _ _ _ Hff Hi)].
    + apply SymScoped_Bot.
    + apply SymScoped_Thunk; assumption.
  - destruct H as [L d xs ep Hep]. intros Hi.
    apply SymScoped_Alt. apply (sym_scoped_weaken _ _ _ _ Hep).
    intros y Hy. apply in_app_or in Hy as [Hy | Hy]; apply in_or_app; [left; exact Hy | right; exact (Hi y Hy)].
Qed.

Lemma sym_scoped_nil_any : forall S L e, sym_scoped S nil e -> sym_scoped S L e.
Proof. intros S L e H. apply (sym_scoped_weaken S nil L e H). intros y []. Qed.

Lemma sym_scoped_thunk_any : forall S L L' Γ e,
  sym_scoped S L (EThunk Γ e) -> sym_scoped S L' (EThunk Γ e).
Proof. intros S L L' Γ e H. inversion H; subst. apply SymScoped_Thunk; assumption. Qed.

Lemma sym_lookup_env_scoped : forall S Γ x Γ' e,
  sym_scoped_env S Γ -> lookup_env Γ x = Some (Γ', e) ->
  sym_scoped_env S Γ' /\ sym_scoped S (dom_env Γ') e.
Proof.
  intros S Γ x Γ' e H. induction H as [| y Γ0 e0 rest H0 IH0 He0 Hrest IH]; intros Hl;
    simpl in Hl; [discriminate |].
  destruct (string_dec x y); [injection Hl as <- <-; split; assumption | exact (IH Hl)].
Qed.

Lemma sym_unspool_app_scoped : forall S L e acc head args,
  unspool_app e acc = (head, args) ->
  sym_scoped S L e -> Forall (sym_scoped S L) acc ->
  sym_scoped S L head /\ Forall (sym_scoped S L) args.
Proof.
  intros S L. induction e; intros acc head args Hu He Hacc; simpl in Hu;
    try (injection Hu as <- <-; split; assumption).
  inversion He; subst.
  apply (IHe1 (e2 :: acc)); [exact Hu | assumption | constructor; assumption].
Qed.

Lemma sym_scoped_fold_left_app : forall S L args h,
  Forall (sym_scoped S L) args -> sym_scoped S L h -> sym_scoped S L (fold_left EApp args h).
Proof.
  intros S L args. induction args as [| a tl IH]; intros h Hargs Hh; simpl; [exact Hh |].
  inversion Hargs; subst. apply IH; [assumption | apply SymScoped_App; assumption].
Qed.

Lemma sym_scoped_con_value : forall S L Γ d args,
  sym_scoped_env S Γ -> Forall (sym_scoped S (dom_env Γ)) args ->
  sym_scoped S L (make_con_app d (map (delay Γ) args)).
Proof.
  intros S L Γ d args HΓ Hargs. apply sym_scoped_fold_left_app; [| apply SymScoped_Con].
  induction Hargs as [| a tl Ha _ IH]; simpl; constructor; [| exact IH].
  destruct a; try (apply SymScoped_Thunk; assumption).
  exact (sym_scoped_thunk_any _ _ _ _ _ Ha).
Qed.

Lemma sym_scoped_env_extend_multi : forall S xs ea Γ Γa,
  sym_scoped_env S Γ -> sym_scoped_env S Γa -> Forall (sym_scoped S (dom_env Γa)) ea ->
  sym_scoped_env S (extend_env_multi Γ xs ea Γa).
Proof.
  induction xs as [| x xs IH]; intros ea Γ Γa HΓ HΓa Hea; [exact HΓ |].
  destruct ea as [| a ea]; simpl.
  - apply SymScoped_Env_Extend; [exact HΓa | apply SymScoped_Bot | apply IH; auto].
  - inversion Hea; subst.
    apply SymScoped_Env_Extend; [exact HΓa | assumption | apply IH; auto].
Qed.

Lemma sym_find_alt_scoped : forall S L d alts xs ep,
  Forall (sym_scoped_alt S L) alts -> find_alt d alts = Some (xs, ep) -> sym_scoped S (xs ++ L) ep.
Proof.
  intros S L d alts xs ep H. induction H as [| [d' xs' ep'] alts Ha _ IH]; intros Hf;
    simpl in Hf; [discriminate |].
  destruct (string_dec d d'); [injection Hf as <- <-; inversion Ha; subst; assumption | exact (IH Hf)].
Qed.

Lemma zip_if_sym_scoped : forall S ec a1 a2,
  sym_scoped S nil ec -> Forall (sym_scoped S nil) a1 -> Forall (sym_scoped S nil) a2 ->
  Forall (sym_scoped S nil) (zip_if ec a1 a2).
Proof.
  intros S ec a1. induction a1 as [| x xs IH]; intros a2 Hec H1 H2; simpl; [constructor |].
  destruct a2 as [| y ys]; simpl; [constructor |].
  inversion H1; subst. inversion H2; subst.
  constructor; [apply SymScoped_If; assumption | apply IH; assumption].
Qed.

Lemma ite_leaf_sym_scoped : forall S Γ ec et ef,
  sym_scoped S nil ec -> sym_scoped S nil et -> sym_scoped S nil ef ->
  sym_scoped S nil (ite_leaf Γ ec et ef).
Proof.
  intros S Γ ec et ef Hec Het Hef. unfold ite_leaf.
  assert (Hrest : sym_scoped S nil
    (if solvable_dec Γ et then
       if solvable_dec Γ ef then reduce_prim op_ite (ec :: et :: ef :: nil) else EIf ec et ef
     else
       match et, ef with
       | EThunk Γ1 (ELam x1 b1), EThunk Γ2 (ELam x2 b2) =>
           if andb (env_eqb Γ1 Γ2) (String.eqb x1 x2)
           then EThunk Γ1 (ELam x1 (EIf ec b1 b2)) else EIf ec et ef
       | EBot b1, EBot b2 => if bottom_eqb b1 b2 then EBot b1 else EIf ec et ef
       | EType τ1, EType τ2 => if dec_eqb type_fc_eq_dec τ1 τ2 then EType τ1 else EIf ec et ef
       | ECoercion γ1, ECoercion γ2 => if dec_eqb coercion_eq_dec γ1 γ2 then ECoercion γ1 else EIf ec et ef
       | _, _ => EIf ec et ef
       end)).
  { destruct (solvable_dec Γ et) as [|]; [destruct (solvable_dec Γ ef) as [|] |].
    - apply (reduce_prim_scoped S nil). repeat (constructor; try assumption).
    - apply SymScoped_If; assumption.
    - destruct et as [ | | | | | | | | γ1 | τ1 | | b1 | Γ1 tbody];
        try (apply SymScoped_If; assumption).
      + (* et = ECoercion γ1 *)
        destruct ef; try (apply SymScoped_If; assumption).
        destruct (dec_eqb coercion_eq_dec γ1 c); [exact Het | apply SymScoped_If; assumption].
      + (* et = EType τ1 *)
        destruct ef; try (apply SymScoped_If; assumption).
        destruct (dec_eqb type_fc_eq_dec τ1 t); [exact Het | apply SymScoped_If; assumption].
      + (* et = EBot b1 *)
        destruct ef; try (apply SymScoped_If; assumption).
        destruct (bottom_eqb b1 b); [exact Het | apply SymScoped_If; assumption].
      + (* et = EThunk Γ1 tbody *)
        destruct tbody as [ | | | | | x1 body1 | | | | | | | ];
          try (apply SymScoped_If; assumption).
        destruct ef as [ | | | | | | | | | | | | Γ2 tbody2 ];
          try (apply SymScoped_If; assumption).
        destruct tbody2 as [ | | | | | x2 body2 | | | | | | | ];
          try (apply SymScoped_If; assumption).
        destruct (env_eqb Γ1 Γ2 && String.eqb x1 x2)%bool eqn:Hx; [| apply SymScoped_If; assumption].
        apply andb_prop in Hx as [Hxe Hxx]. apply env_eqb_eq in Hxe. apply String.eqb_eq in Hxx.
        subst Γ2 x2.
        inversion Het as [| | | | | | | | | | | | L1 Γ1' e1 HΓ1 Hb1]; subst.
        inversion Hb1 as [| | | | | L2 x2' body2' Hbody1 | | | | | | |]; subst.
        inversion Hef as [| | | | | | | | | | | | L3 Γ3 e3 HΓ3 Hb3]; subst.
        inversion Hb3 as [| | | | | L4 x4 body4 Hbody2 | | | | | | |]; subst.
        apply SymScoped_Thunk; [exact HΓ1 |].
        apply SymScoped_Lam. apply SymScoped_If;
          [apply sym_scoped_nil_any; exact Hec | exact Hbody1 | exact Hbody2]. }
  destruct (decompose_con_app et) as [[d1 a1]|] eqn:E1;
  destruct (decompose_con_app ef) as [[d2 a2]|] eqn:E2; try exact Hrest.
  destruct (andb (String.eqb d1 d2) (Nat.eqb (length a1) (length a2)));
    [| apply SymScoped_If; assumption].
  apply sym_scoped_fold_left_app; [| apply SymScoped_Con].
  apply zip_if_sym_scoped; [exact Hec | |].
  - exact (proj2 (sym_unspool_app_scoped S nil et [] (ECon d1) a1
             (decompose_con_app_unspool _ _ _ E1) Het (Forall_nil _))).
  - exact (proj2 (sym_unspool_app_scoped S nil ef [] (ECon d2) a2
             (decompose_con_app_unspool _ _ _ E2) Hef (Forall_nil _))).
Qed.

Fixpoint ite_sym_scoped (S : symvars) (Γ : environment) (ec et ef : expr) {struct et} :
  sym_scoped S nil ec -> sym_scoped S nil et -> sym_scoped S nil ef ->
  sym_scoped S nil (ite Γ ec et ef).
Proof.
  intros Hec Het Hef.
  destruct et; try (rewrite ite_leaf_of by (left; reflexivity); apply ite_leaf_sym_scoped; assumption).
  destruct ef; try (rewrite ite_leaf_of by (right; reflexivity); apply ite_leaf_sym_scoped; assumption).
  rewrite ite_cast.
  destruct (dec_eqb coercion_eq_dec c c0); [| apply SymScoped_If; assumption].
  inversion Het as [| | | | | | | L1 e1 γ1 Hsce | | | | |]; subst.
  inversion Hef as [| | | | | | | L2 e2 γ2 Hscf | | | | |]; subst.
  apply SymScoped_Cast. exact (ite_sym_scoped S Γ ec et ef Hec Hsce Hscf).
Qed.

(**
  Symbolic evaluation and branch folding keep a program symbolic. Because every
  bottom is symbolic, this holds at any budget, and needs no path condition
  hypothesis: Rule Prune and Rule Out-Of-Fuel both answer a bottom, which is
  symbolic. Rule App-If and the two boolean-formula fold clauses build branches,
  which the symbolic scoping allows.
*)
Fixpoint sym_eval_scoped_fix (f0 : fuel) (Φ : path_condition) (Γ : environment) (e v : expr)
  (Heval : eval f0 Φ Γ e v) {struct Heval} :
  forall S, sym_scoped_env S Γ -> sym_scoped S (dom_env Γ) e -> sym_scoped S nil v
with sym_fold_scoped_fix (f0 : fuel) (Φ : path_condition) (Γ : environment) (e : expr)
  (alts : list alt) (er : expr)
  (Hfold : fold_alts f0 Φ Γ e alts er) {struct Hfold} :
  forall S, sym_scoped_env S Γ -> sym_scoped S nil e -> Forall (sym_scoped_alt S (dom_env Γ)) alts ->
  sym_scoped S nil er.
Proof.
{
  destruct Heval as
    [ k Φ Γ x Γ' e e' Hlook Heval_x
    | k Φ Γ x Hnone
    | k Φ Γ l
    | k Φ Γ econ d args Hunspool_con
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
    ]; intros S HΓ Hsc.
  - (* Var *)
    destruct (sym_lookup_env_scoped S Γ x Γ' e HΓ Hlook) as [HΓ' Hsc'].
    exact (sym_eval_scoped_fix _ _ _ _ _ Heval_x S HΓ' Hsc').
  - (* Sym-Var *)
    inversion Hsc as [L0 x0 Hx | | | | | | | | | | | |]; subst.
    apply SymScoped_Var. right.
    destruct Hx as [Hin | Hx]; [exfalso; exact (in_dom_lookup_env Γ x Hin Hnone) | exact Hx].
  - (* Lit *) apply SymScoped_Lit.
  - (* Con *)
    destruct (sym_unspool_app_scoped S (dom_env Γ) econ [] (ECon d) args Hunspool_con Hsc (Forall_nil _))
      as [_ Hargs].
    exact (sym_scoped_con_value S nil Γ d args HΓ Hargs).
  - (* Cast *)
    inversion Hsc as [| | | | | | | L1 e1 γ1 Hsce | | | | |]; subst.
    apply (cast_expr_scoped S nil). exact (sym_eval_scoped_fix _ _ _ _ _ Heval_e S HΓ Hsce).
  - (* App-Abs *)
    inversion Hsc as [| | | | L0 f0 a0 Hscf Hsca | | | | | | | |]; subst.
    inversion Hscf as [| | | | | | | | | | | | L1 Γ1 e1 HΓ' Hsclam]; subst.
    inversion Hsclam as [| | | | | L2 x2 b2 Hscb | | | | | | |]; subst.
    apply (sym_eval_scoped_fix _ _ _ _ _ Heval_b S).
    + apply SymScoped_Env_Extend; assumption.
    + exact Hscb.
  - (* App-Spine *)
    inversion Hsc as [| | | | L0 f0 a0 Hscf Hsca | | | | | | | |]; subst.
    apply (sym_eval_scoped_fix _ _ _ _ _ Heval_app2 S HΓ).
    apply SymScoped_App; [apply sym_scoped_nil_any;
      exact (sym_eval_scoped_fix _ _ _ _ _ Heval_f S HΓ Hscf) | exact Hsca].
  - (* Bot *) apply SymScoped_Bot.
  - (* App-Prim *)
    destruct (sym_unspool_app_scoped S (dom_env Γ) (EApp ef ea) [] (EPrimOp p) args Hunspool Hsc
                (Forall_nil _)) as [_ Hsc_args].
    apply (reduce_prim_scoped S nil).
    clear Hunspool Harity Hsc.
    revert Hsc_args. induction Hargs as [| a a' tl tl' Ha Htl IH]; intros Hsc_args.
    + constructor.
    + inversion Hsc_args as [| a1 tl1 Hsc_a Hsc_tl]; subst.
      constructor;
        [apply sym_scoped_nil_any; exact (sym_eval_scoped_fix _ _ _ _ _ Ha S HΓ Hsc_a)
        | exact (IH Hsc_tl)].
  - (* Lam *) apply SymScoped_Thunk; assumption.
  - (* App-Cast *)
    inversion Hsc as [| | | | L0 f0 a0 Hscf Hsca | | | | | | | |]; subst.
    inversion Hscf as [| | | | | | | L1 e1 γ1 Hsce | | | | |]; subst.
    apply (sym_eval_scoped_fix _ _ _ _ _ Heval_pushed S HΓ).
    apply SymScoped_Cast. apply SymScoped_App; [assumption | apply SymScoped_Cast; assumption].
  - (* App-If *)
    destruct (sym_unspool_app_scoped S (dom_env Γ) (EApp e1 e2) [] (EIf ec et ef) args Hunspool_if Hsc
                (Forall_nil _)) as [Hif Hargs].
    inversion Hif as [| | | | | | | | | | L1 ec1 et1 ef1 Hscc Hsct Hscf | |]; subst.
    apply (sym_eval_scoped_fix _ _ _ _ _ Heval_arms S HΓ).
    apply SymScoped_If;
      [exact Hscc
      | apply sym_scoped_fold_left_app; assumption
      | apply sym_scoped_fold_left_app; assumption].
  - (* App-Bot *) inversion Hsc; subst. apply SymScoped_Bot.
  - (* Case *)
    inversion Hsc as [| | | | | | L0 es1 alts1 Hsc_es Hsc_alts | | | | | |]; subst.
    pose proof (sym_eval_scoped_fix _ _ _ _ _ Heval_es S HΓ Hsc_es) as Hsc_es'.
    apply (sym_fold_scoped_fix _ _ _ _ _ _ Hfold S HΓ).
    + destruct es' as [ | | | | | | | | | | vc vt vf | | ]; simpl; try exact Hsc_es'.
      inversion Hsc_es' as [| | | | | | | | | | L1 vc1 vt1 vf1 Hvc Hvt Hvf | |]; subst.
      apply ite_sym_scoped; assumption.
    + exact Hsc_alts.
  - (* If *)
    inversion Hsc as [| | | | | | | | | | L1 ec1 et1 ef1 Hscc Hsct Hscf | |]; subst.
    apply SymScoped_If;
      [apply sym_scoped_nil_any; exact (sym_eval_scoped_fix _ _ _ _ _ Heval_c S HΓ Hscc)
      | apply sym_scoped_nil_any; exact (sym_eval_scoped_fix _ _ _ _ _ Heval_t S HΓ Hsct)
      | apply sym_scoped_nil_any; exact (sym_eval_scoped_fix _ _ _ _ _ Heval_f S HΓ Hscf)].
  - (* Coercion *) apply SymScoped_Coercion.
  - (* Prune *) apply SymScoped_Bot.
  - (* Type *) apply SymScoped_Type.
  - (* Thunk *)
    inversion Hsc as [| | | | | | | | | | | | L1 Γ1 e1 HΓ' Hsce]; subst.
    exact (sym_eval_scoped_fix _ _ _ _ _ Heval_t S HΓ' Hsce).
  - (* Out-Of-Fuel *) apply SymScoped_Bot.
}
{
  destruct Hfold as
    [ k Φ Γ ec et ef alts et' ef' pc_c Hpc Hfold_t Hfold_f
    | k Φ Γ ec et ef alts Hpc_none
    | k Φ Γ e d ea xs ep alts er Hdec Halt Heval_ep
    | k Φ Γ b alts
    | k Φ Γ e pc alts r Hpc Hvar Hrec
    | k Φ Γ e pc alts r1 r2 Hpc Hvar Har Hf1 Hf2
    | k Φ Γ e alts Hpcnone Hop Hnothead Hnoalt Hnotbot
    ]; intros S HΓ Hsc Halts.
  - (* FoldAlts_If *)
    inversion Hsc as [| | | | | | | | | | L1 ec1 et1 ef1 Hscc Hsct Hscf | |]; subst.
    apply SymScoped_If;
      [exact Hscc
      | exact (sym_fold_scoped_fix _ _ _ _ _ _ Hfold_t S HΓ Hsct Halts)
      | exact (sym_fold_scoped_fix _ _ _ _ _ _ Hfold_f S HΓ Hscf Halts)].
  - (* FoldAlts_IfFail *) apply SymScoped_Bot.
  - (* FoldAlts_Con *)
    assert (Hea : Forall (sym_scoped S (dom_env Γ)) ea).
    { pose proof (proj2 (sym_unspool_app_scoped S nil e [] (ECon d) ea
                    (decompose_con_app_unspool e d ea Hdec) Hsc (Forall_nil _))) as H0.
      eapply Forall_impl; [| exact H0]. intros a Ha. apply sym_scoped_nil_any. exact Ha. }
    apply (sym_eval_scoped_fix _ _ _ _ _ Heval_ep S).
    + apply sym_scoped_env_extend_multi; [exact HΓ | exact HΓ | exact Hea].
    + rewrite dom_env_extend_multi. exact (sym_find_alt_scoped S (dom_env Γ) d alts xs ep Halts Halt).
  - (* FoldAlts_Bot *) apply SymScoped_Bot.
  - (* FoldAlts_GroundFormula *)
    exact (sym_fold_scoped_fix _ _ _ _ _ _ Hrec S HΓ (SymScoped_Con S nil _) Halts).
  - (* FoldAlts_SymbolicFormula *)
    apply SymScoped_If;
      [exact Hsc
      | exact (sym_fold_scoped_fix _ _ _ _ _ _ Hf1 S HΓ (SymScoped_Con S nil _) Halts)
      | exact (sym_fold_scoped_fix _ _ _ _ _ _ Hf2 S HΓ (SymScoped_Con S nil _) Halts)].
  - (* FoldAlts_Otherwise *) apply SymScoped_Bot.
}
Qed.

Lemma sym_eval_scoped : forall S Φ Γ e v,
  symbolic_program S Γ e -> Φ; Γ ⊢ e ⇓ v -> sym_scoped S nil v.
Proof.
  intros S Φ Γ e v [HΓ Hsc] Heval.
  exact (sym_eval_scoped_fix Inf Φ Γ e v Heval S HΓ Hsc).
Qed.

Definition closed_instance (Γ : environment) (e : expr) : Prop :=
  closed_program Γ e \/ (is_thunk e = true /\ closed_term e).

Lemma closed_instance_program : forall Γ e,
  closed_instance Γ e -> is_thunk e = false -> closed_program Γ e.
Proof. intros Γ e [H | [H _]] Ht; [exact H | congruence]. Qed.

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
(** 9.0 The SMT Value of a Formula                                            *)
(** ------------------------------------------------------------------------- *)

(** prim_value, pc_value and lit_true are in SymCore.v. *)

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

Section ConCore.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}
  {reduce_prim_solvable_law : ReducePrimSolvable}
  {reduce_prim_saturated_law : ReducePrimSaturated}
  {reduce_prim_concore_law : ReducePrimConcore} {cast_expr_concore_law : CastExprConcore}
  {reduce_prim_scoped_law : ReducePrimScoped} {cast_expr_scoped_law : CastExprScoped}
  {models_sat_law : ModelsSat} {prim_value_and_law : PrimValueAnd}.

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

(** SMT solver behavior: primitive operations preserve concretion of closed
    concrete arguments *)
Class ReducePrimContains : Prop :=
reduce_prim_contains : forall σ S p args_s args_c,
  Forall closed_term args_c ->
  Forall2 (contains σ S) args_s args_c ->
  contains σ S (reduce_prim p args_s) (reduce_prim p args_c).

(**
  SMT solver behavior: reducing a primitive application preserves its SMT
  value. This is the correctness statement for the external reducer, and it is
  what lets the reducer COMPUTE. Without it, a reduced term could stay related
  to its concrete counterpart only by being syntactically the same term, so
  reduce_prim would be forced never to compute.
*)
Class ReducePrimDenote : Prop :=
reduce_prim_denote : forall σ S p args ls,
  Forall2 (denote σ S) args ls ->
  denote σ S (reduce_prim p args) (prim_value p ls).

(**
  SMT solver behavior: when the reducer's answer mentions no variable, it is
  a value. A closed SMT term is a number the solver already knows, and a
  reducer that returned an unevaluated closed application would simply have
  stopped early.
*)
Class ReducePrimGroundValue : Prop :=
reduce_prim_ground_value : forall p args,
  smt_ground (reduce_prim p args) = true ->
  exists l, reduce_prim p args = ELit l.

Context {reduce_prim_contains_law : ReducePrimContains}
  {reduce_prim_denote_law : ReducePrimDenote}
  {reduce_prim_ground_value_law : ReducePrimGroundValue}.

(** Grisette state merging soundness (Lemma A.4 in the paper) is now the
    lemma merge_contains in Section 9.3, proved from the definition of merge. *)

(** Coercion cast simplification preserves concretion (Lemma A.5 in the paper) *)
Class CastExprContains : Prop :=
cast_expr_contains : forall σ S es ec γ,
  contains σ S es ec ->
  contains σ S (cast_expr es γ) (cast_expr ec γ).

Context {cast_expr_contains_law : CastExprContains}.

(** Every rule other than App-Prim is excluded here, by solvability or by Rule
    Prune being unreachable under a model.

    Unlimited budget only: at Fin 0 Rule Out-Of-Fuel answers EBot BOutOfFuel,

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
    exact (comp_not_solvable _ _ H Hf).
  - right. exists p, args, args'. repeat split; assumption.
  - exfalso. inversion Hsolv as [| | | f a Hop Hf Ha]; subst. discriminate.
  - exfalso.
    match goal with
    | [ Hu : unspool_app (EApp _ _) _ = (EIf _ _ _, _) |- _ ] =>
        exact (solvable_unspool_not_if _ _ _ _ _ _ _ Hsolv Hu)
    end.
  - exfalso. inversion Hsolv as [| | | f a Hop Hf Ha]; subst. discriminate.
  - exfalso. apply models_sat in Hmod. congruence.
Qed.


(** Substitution on coercions and types preserves concretion under matched environments *)
Class SubstCoercContainsEnv : Prop :=
subst_coerc_contains_env : forall σ S Γs Γc γ,
  contains_env σ S Γs Γc ->
  contains σ S (ECoercion (subst_coerc Γs γ)) (ECoercion (subst_coerc Γc γ)).

Class SubstTypeContainsEnv : Prop :=
subst_type_contains_env : forall σ S Γs Γc τ,
  contains_env σ S Γs Γc ->
  contains σ S (EType (subst_type Γs τ)) (EType (subst_type Γc τ)).

Context {subst_coerc_contains_env_law : SubstCoercContainsEnv}
  {subst_type_contains_env_law : SubstTypeContainsEnv}.

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

Lemma contains_thunk_inv : forall σ S Γs es ec,
  contains σ S (EThunk Γs es) ec ->
  (exists Γc ec', ec = EThunk Γc ec' /\ contains_env σ S Γs Γc /\ contains σ S es ec')
  \/ (exists Γc, contains_env σ S Γs Γc /\ contains σ S es ec /\ is_thunk ec = true).
Proof.
  intros σ S Γs es ec H. inversion H; subst; [left | right | kill_denote].
  - exists Γc, ec0. split; [reflexivity | auto].
  - exists Γc. auto.
Qed.

Lemma contains_clos_inv : forall σ S Γs x body ec,
  contains σ S (EThunk Γs (ELam x body)) ec ->
  exists Γc bodyc, ec = EThunk Γc (ELam x bodyc) /\ S x = false /\
    contains_env σ S Γs Γc /\
    contains σ S body bodyc.
Proof.
  intros σ S Γs x body ec H.
  destruct (contains_thunk_inv σ S Γs (ELam x body) ec H)
    as [[Γc [ec' [Heq [Henv Hlam]]]] | [Γc [Henv [Hlam Hthunk]]]].
  - destruct (contains_lam_inv σ S x body ec' Hlam) as [bodyc [Heq' [Hx Hbody]]].
    subst. exists Γc, bodyc. auto.
  - destruct (contains_lam_inv σ S x body ec Hlam) as [bodyc [Heq' _]].
    subst. discriminate Hthunk.
Qed.

(**
  An application is the one shape Cont_Denote can also produce, so the
  inversion is a disjunction. The second alternative carries Solvable Γ fs,
  which is what every caller uses to rule it out: a cast, a closure or a
  bottom in function position is not solvable, and neither is a function that
  Rule App-Spine has just declared a computation.

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
  closed_instance Γc e_con ->
  decomp_coerc_arrow γ = Some (γ_a, γ_r) ->
  Φ ; Γs ⊢ ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r ⇓ er ->
  (forall (Γc : environment) (σ : valuation) (e_con : expr),
    σ ⊨ Φ ->
    contains_env σ S Γs Γc ->
    contains σ S (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r) e_con ->
    concore_expr e_con ->
    closed_instance Γc e_con ->
    exists v_con : expr,
      Γc ⊢ᶜ e_con ⇓ᶜ v_con /\ contains σ S er v_con) ->
  exists v_con,
    Γc ⊢ᶜ e_con ⇓ᶜ v_con /\ contains σ S er v_con.
Proof.
  intros Φ Γs Γc σ S ef γ ea γ_a γ_r er e_con Hmod Henv Hcont Hcon Hcl Hdecomp Heval_pushed_s IH.
  assert (Hfree : sym_free_env S Γs)
    by (destruct (contains_env_sym_free σ S Γs Γc Henv) as [Hf _]; exact Hf).
  destruct (contains_app_inv σ S Γs (ECast ef γ) ea e_con Hfree Hcont) as
    [[fc [ac [Heq [Hcont_f Hcont_a]]]] | [Hsolv _]];
    [subst e_con | exfalso; exact (solvable_not_cast Γs ef γ Hsolv)].
  apply contains_cast_inv in Hcont_f as [efc [Heq_fc Hcont_ef]]; subst fc.
  inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | ]; subst.
  inversion Hf as [| | | | | | | efc0 γ0 Hcon_ef | | | | | | ]; subst.
  assert (Hcont_pushed : contains σ S (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r)
                                   (ECast (EApp efc (ECast ac (sym_coerc γ_a))) γ_r)).
  { constructor. constructor; [assumption | constructor; assumption]. }
  assert (Hcon_pushed : concore_expr (ECast (EApp efc (ECast ac (sym_coerc γ_a))) γ_r)).
  { constructor. constructor; [assumption | constructor; assumption]. }
  destruct (closed_instance_program Γc _ Hcl eq_refl) as [HΓc Hsc].
  inversion Hsc as [| | | | L0 f0 a0 Hscf Hsca | | | | | | | |]; subst.
  inversion Hscf as [| | | | | | | L1 e1 γ1 Hsce | | | | |]; subst.
  assert (Hcl_pushed : closed_instance Γc (ECast (EApp efc (ECast ac (sym_coerc γ_a))) γ_r)).
  { left. split; [exact HΓc |].
    apply Scoped_Cast. apply Scoped_App; [assumption | apply Scoped_Cast; assumption]. }
  destruct (IH Γc σ (ECast (EApp efc (ECast ac (sym_coerc γ_a))) γ_r) Hmod Henv Hcont_pushed Hcon_pushed Hcl_pushed) as [v_con [Heval_pushed Hcont_v]].
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
  - match goal with [ H : Comp _ _ |- _ ] => inversion H end.
  - match goal with
    | [ H : unspool_app (EApp _ _) [] = _ |- _ ] =>
        simpl in H; discriminate
    end.
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
  - match goal with [ H : Comp _ _ |- _ ] => inversion H end.
  - match goal with
    | [ H : unspool_app (EApp _ _) [] = _ |- _ ] =>
        simpl in H; discriminate
    end.
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
  - match goal with [ H : Comp _ _ |- _ ] => inversion H end.
  - match goal with
    | [ H : unspool_app (EApp _ _) [] = _ |- _ ] =>
        simpl in H; discriminate
    end.
  - match goal with
    | [ H : unspool_app (EApp _ _) [] = _ |- _ ] =>
        simpl in H; discriminate
    end.
  - rewrite sat_pc_true in H0. discriminate.
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
  all: match goal with
    | [ Ht : is_thunk ?e = true |- _ ] => destruct e; try discriminate Ht; reflexivity
    | [ Hun : unspool_app ?e [] = (EPrimOp _, _), Hg : smt_ground ?e = false |- _ ] =>
        destruct (cont_denote_is_app _ _ _ Hun Hg) as [? [? ->]]; reflexivity
    end.
Qed.

Lemma spine_head_contains : forall σ S es ec,
  contains σ S es ec ->
  has_whole_spine_rule (spine_head es) = false ->
  has_whole_spine_rule (spine_head ec) = false.
Proof.
  intros σ S es ec H. induction H; intros Hh; simpl in *; try reflexivity; try discriminate Hh.
  - exact (IHcontains1 Hh).
  - destruct ec; try discriminate; reflexivity.
Qed.

Lemma comp_contains : forall σ S Γs Γc ef efc,
  contains_env σ S Γs Γc ->
  contains σ S ef efc ->
  Comp Γs ef ->
  Comp Γc efc \/ exists Γ' x body, efc = EThunk Γ' (ELam x body).
Proof.
  intros σ S Γs Γc ef efc Henv Hcont Hcomp.
  destruct Hcomp as [x Hbound | x body | es alts | Γ' e Hnotlam | f a Hhead].
  - left.
    destruct (lookup_env Γs x) as [[Γ's es] |] eqn:Hlook; [| congruence].
    destruct (contains_env_sym_free σ S Γs Γc Henv) as [Hfree _].
    rewrite (contains_var_bound σ S Γs x Γ's es efc Hfree Hlook Hcont).
    destruct (contains_lookup_env σ S Γs Γc x Γ's es Henv Hlook) as [Γ'c [ec [Hlookc _]]].
    apply Comp_Var. rewrite Hlookc. discriminate.
  - left. apply contains_lam_inv in Hcont as [bodyc [-> _]]. apply Comp_Lam.
  - left. apply contains_case_inv in Hcont as [esc [altsc [-> _]]]. apply Comp_Case.
  - destruct (contains_thunk_inv σ S Γ' e efc Hcont)
      as [[Γc' [ec' [-> _]]] | [_ [_ [_ Hthunk]]]].
    + destruct (is_lam ec') eqn:Hlam.
      * right. destruct ec'; try discriminate Hlam. eexists; eexists; eexists; reflexivity.
      * left. apply Comp_Thunk. exact Hlam.
    + destruct efc; try discriminate Hthunk.
      destruct (is_lam efc) eqn:Hlam.
      * right. destruct efc; try discriminate Hlam. eexists; eexists; eexists; reflexivity.
      * left. apply Comp_Thunk. exact Hlam.
  - left. inversion Hcont; subst.
    + apply Comp_App. exact (spine_head_contains σ S _ _ Hcont Hhead).
    + exfalso.
      match goal with
      | [ Hu : unspool_app (EApp f a) [] = (EPrimOp _, _) |- _ ] =>
          rewrite <- (fst_unspool_app (EApp f a) []), Hu in Hhead; discriminate Hhead
      end.
Qed.

Lemma eval_app_spine_sound : forall Φ Γs Γc σ S ef ea ef' er e_con,
  σ ⊨ Φ ->
  contains_env σ S Γs Γc ->
  contains σ S (EApp ef ea) e_con ->
  concore_expr e_con ->
  closed_instance Γc e_con ->
  Comp Γs ef ->
  (forall (Γc : environment) (e_con : expr),
    contains_env σ S Γs Γc ->
    contains σ S ef e_con ->
    concore_expr e_con ->
    closed_instance Γc e_con ->
    exists v_con : expr,
      Γc ⊢ᶜ e_con ⇓ᶜ v_con /\ contains σ S ef' v_con) ->
  (forall (Γc : environment) (e_con : expr),
    contains_env σ S Γs Γc ->
    contains σ S (EApp ef' ea) e_con ->
    concore_expr e_con ->
    closed_instance Γc e_con ->
    exists v_con : expr,
      Γc ⊢ᶜ e_con ⇓ᶜ v_con /\ contains σ S er v_con) ->
  exists v_con,
    Γc ⊢ᶜ e_con ⇓ᶜ v_con /\ contains σ S er v_con.
Proof.
  intros Φ Γs Γc σ S ef ea ef' er e_con Hmod Henv Hcont Hcon Hcl Hcomp IH1 IH2.
  assert (Hfree : sym_free_env S Γs)
    by (destruct (contains_env_sym_free σ S Γs Γc Henv) as [Hf _]; exact Hf).
  destruct (contains_app_inv σ S Γs ef ea e_con Hfree Hcont) as
    [[fc [ac [Heq [Hcont_f Hcont_a]]]] | [Hsolv _]];
    [subst e_con | exfalso; exact (comp_not_solvable Γs ef Hcomp Hsolv)].
  inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | ]; subst.
  destruct (closed_instance_program Γc _ Hcl eq_refl) as [HΓc Hsc].
  inversion Hsc as [| | | | L0 f0 a0 Hscf Hsca | | | | | | | |]; subst.
  destruct (IH1 Γc fc Henv Hcont_f Hf (or_introl (conj HΓc Hscf))) as [v_f [Heval_f Hcont_vf]].
  destruct (comp_contains σ S Γs Γc ef fc Henv Hcont_f Hcomp)
    as [Hcomp_c | [Γ' [x [body ->]]]].
  - assert (Henv_c : concrete_env Γc) by (eapply contains_env_concrete; eassumption).
    assert (Hcon_vf : concore_expr v_f)
      by (eapply concore_eval_closed; [exact Henv_c | exact Hf | exact (conj HΓc Hscf) | exact Heval_f]).
    assert (Hsc_vf : closed_term v_f)
      by (eapply closed_eval; [exact Henv_c | exact Hf | exact (conj HΓc Hscf) | exact Heval_f]).
    destruct (IH2 Γc (EApp v_f ac) Henv (Cont_App σ S ef' ea v_f ac Hcont_vf Hcont_a)
                (Con_App v_f ac Hcon_vf Ha)
                (or_introl (conj HΓc (Scoped_App _ _ _ (closed_term_scoped _ _ Hsc_vf) Hsca))))
      as [v_con [Heval_app2 Hcont_er]].
    exists v_con. split; [| exact Hcont_er].
    exact (Eval_AppSpine Unlimited pc_true Γc fc ac v_f v_con Hcomp_c Heval_f Heval_app2).
  - unfold eval_con in Heval_f.
    apply (eval_closure_same pc_true Γc Γ' x body v_f sat_pc_true) in Heval_f. subst v_f.
    exact (IH2 Γc _ Henv (Cont_App σ S ef' ea _ ac Hcont_vf Hcont_a) Hcon Hcl).
Qed.

Lemma contains_delay : forall σ S Γs Γc e_s e_c,
  contains_env σ S Γs Γc ->
  contains σ S e_s e_c ->
  contains σ S (delay Γs e_s) (delay Γc e_c).
Proof.
  intros σ S Γs Γc e_s e_c Henv Hcont.
  destruct (is_thunk e_s) eqn:Hs; destruct (is_thunk e_c) eqn:Hc.
  - rewrite (delay_thunk Γs e_s Hs), (delay_thunk Γc e_c Hc). exact Hcont.
  - exfalso. destruct e_s; try discriminate Hs.
    destruct (contains_thunk_inv σ S _ _ e_c Hcont)
      as [[Γ1 [e1 [Heq _]]] | [_ [_ [_ Ht]]]]; [subst e_c; discriminate Hc | congruence].
  - rewrite (delay_not_thunk Γs e_s Hs), (delay_thunk Γc e_c Hc).
    exact (Cont_Thunk_Outer σ S Γs Γc e_s e_c Henv Hcont Hc).
  - rewrite (delay_not_thunk Γs e_s Hs), (delay_not_thunk Γc e_c Hc).
    exact (Cont_Thunk σ S Γs Γc e_s e_c Henv Hcont).
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
  answers EBot BOutOfFuel, and expr_to_pc reads no formula off a bottom, so
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
    | kv Φ Γ ef ea ef' er Hcomp Heval_f Heval_app2
    | kv Φ Γ b
    | kv Φ Γ ef ea p eargs eargs' Hunspool Harity Hargs
    | kv Φ Γ x eb
    | kv Φ Γ ef γ ea γ_a γ_r er Hdecomp Heval_pushed
    | kv Φ Γ e1 e2 ec et ef args er Hunspool_if Heval_arms
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
  - (* Eval_AppSpine: a denoting spine has a solvable operator, which is not a computation *)
    exfalso. apply (comp_not_solvable _ _ Hcomp).
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
  - exfalso. destruct Hden as [pc [Hd _]].
    exact (solvable_unspool_not_if _ _ _ _ _ _ _
             (expr_to_pc_solvable Γ (EApp e1 e2) pc (Hd Γ Hfree)) Hunspool_if).
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
  eval_con. At Fin 0 the symbolic side answers EBot BOutOfFuel, which
  contains only a concrete EBot BOutOfFuel, and no concrete expression
  reduces to that.
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
(** 9.3 What Merging Keeps of an Instance (§3.3)                              *)
(** ------------------------------------------------------------------------- *)

(**
  Every concrete term the unmerged branch stands for, the merged term stands
  for too, with one exception: the SMT clause. Of its term and the instance
  only this is known: both are scrutinees that no alternative matches. That is the paper's Lemma A.4 in the form that has a model, proved
  from Section 8.1's definition of merge.

  The proof is one case per clause of the merge table. The shape is always
  the same: the model picks an arm, the clause's result agrees with that arm
  on the head, and the branch that is left inside the result is resolved by
  the same model the same way.
*)

Definition inert_scrutinee (e : expr) : Prop :=
  is_if (fst (unspool_app e [])) = false /\ decompose_con_app e = None /\ is_bot e = false.

Lemma spine_head_app : forall f a,
  fst (unspool_app (EApp f a) []) = fst (unspool_app f []).
Proof.
  intros f a. simpl. destruct (unspool_app f []) as [h args] eqn:Hu.
  pose proof (unspool_app_shift f [] [a] h args Hu) as Hshift. simpl in Hshift.
  rewrite Hshift. reflexivity.
Qed.

Lemma decompose_con_app_none : forall e,
  is_con_app e = false -> decompose_con_app e = None.
Proof.
  intros e H. destruct (decompose_con_app e) as [[d args] |] eqn:Hd; [| reflexivity].
  apply decompose_con_app_unspool, unspool_is_con_app in Hd. congruence.
Qed.

Lemma inert_not_if : forall e, inert_scrutinee e -> is_if e = false.
Proof. intros e [Hh _]. exact (is_if_false_of_spine_head e Hh). Qed.

Lemma inert_app : forall f a,
  inert_scrutinee f -> is_con_app f = false -> inert_scrutinee (EApp f a).
Proof.
  intros f a [Hh _] Hc. split; [| split].
  - rewrite spine_head_app. exact Hh.
  - apply decompose_con_app_none. exact Hc.
  - reflexivity.
Qed.

Lemma inert_cast : forall e γ, inert_scrutinee (ECast e γ).
Proof. intros e γ. repeat split. Qed.

Lemma solvable_inert : forall Γ e, Solvable Γ e -> inert_scrutinee e.
Proof.
  intros Γ e H. induction H as [l | x Hx | p | f a Hop Hf IHf Ha IHa];
    try (repeat split; fail).
  apply inert_app; [exact IHf | exact (solvable_not_con_app Γ f Hf)].
Qed.

Lemma contains_is_con_app_false : forall σ S Γ e c,
  Solvable Γ e -> contains σ S e c -> is_con_app c = false.
Proof.
  intros σ S Γ e c H. revert c.
  induction H as [l | x Hx | p | f a Hop Hf IHf Ha IHa]; intros c Hc;
    inversion Hc; subst; try reflexivity.
  simpl. apply IHf. assumption.
Qed.

Lemma contains_solvable_inert : forall σ S Γ e c,
  Solvable Γ e -> contains σ S e c -> inert_scrutinee c.
Proof.
  intros σ S Γ e c H. revert c.
  induction H as [l | x Hx | p | f a Hop Hf IHf Ha IHa]; intros c Hc;
    inversion Hc; subst; try (repeat split; fail).
  apply inert_app; [apply IHf; assumption |].
  eapply contains_is_con_app_false; [exact Hf | eassumption].
Qed.

(** A cast scrutinee is not a formula and not a primitive application, so both
    Rule Case sides fold it to undefined. *)
Lemma is_cast_facts : forall e, is_cast e = true ->
  expr_to_pc · e = None /\ is_op_app e = false /\
  is_if (fst (unspool_app e [])) = false /\ decompose_con_app e = None /\ is_bot e = false.
Proof.
  intros e H. destruct e; simpl in H; try discriminate.
  repeat split; reflexivity.
Qed.

Lemma fold_alts_cast_undefined : forall f Φ Γ e alts r,
  is_cast e = true -> fold_alts f Φ Γ e alts r -> r = EBot BUndefined.
Proof.
  intros f Φ Γ e alts r Hc Hfold.
  destruct (is_cast_facts e Hc) as [_ [Hop [Hh [Hd Hb]]]].
  assert (Hpc : expr_to_pc Γ e = None) by (destruct e; simpl in Hc; try discriminate; reflexivity).
  apply (fold_alts_otherwise_same f Φ Γ e alts r Hpc Hop
           (is_if_false_of_spine_head e Hh)); [rewrite Hd; exact I | exact Hb | exact Hfold].
Qed.

Lemma fold_alts_cast_undefined_intro : forall f Φ Γ e alts,
  is_cast e = true -> fold_alts f Φ Γ e alts (EBot BUndefined).
Proof.
  intros f Φ Γ e alts Hc.
  assert (Hpc : expr_to_pc Γ e = None) by (destruct e; simpl in Hc; try discriminate; reflexivity).
  destruct (is_cast_facts e Hc) as [_ [Hop [Hh [Hd Hb]]]].
  apply FoldAlts_Otherwise; [exact Hpc | exact Hop | exact Hh | rewrite Hd; exact I | exact Hb].
Qed.

Lemma solvable_in_empty_env : forall Γ e, Solvable Γ e -> Solvable · e.
Proof.
  intros Γ e H. destruct (solvable_expr_to_pc Γ e H) as [pc Hpc].
  exact (expr_to_pc_solvable · e pc Hpc).
Qed.

Lemma denotes_solvable : forall S e pc, denotes S e pc -> Solvable · e.
Proof.
  intros S e pc H. exact (expr_to_pc_solvable · e pc (H · (sym_free_env_empty S))).
Qed.

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

Lemma contains_spine_if : forall σ S e_sym e_con,
  contains σ S e_sym e_con ->
  forall L_s L_c,
    Forall2 (contains σ S) L_s L_c ->
    forall ec et ef args,
      unspool_app e_sym L_s = (EIf ec et ef, args) ->
      exists head_c args_c,
        fold_left EApp L_c e_con = fold_left EApp args_c head_c /\
        contains σ S (EIf ec et ef) head_c /\
        Forall2 (contains σ S) args args_c.
Proof.
  induction 1; intros L_s L_c HL ec0 et0 ef0 args0 Hunspool; simpl in Hunspool;
    try discriminate Hunspool.
  - exact (IHcontains1 (a_s :: L_s) (a_c :: L_c) (Forall2_cons _ _ H0 HL) _ _ _ _ Hunspool).
  - injection Hunspool as Hc Ht Hf Hargs. subst.
    exists etc, L_c. split; [reflexivity | split; [apply Cont_If_True; assumption | exact HL]].
  - injection Hunspool as Hc Ht Hf Hargs. subst.
    exists efc, L_c. split; [reflexivity | split; [apply Cont_If_False; assumption | exact HL]].
  - exfalso.
    match goal with
    | [ Hun0 : unspool_app ?e (@nil expr) = (EPrimOp ?q, ?qargs) |- _ ] =>
        apply (unspool_app_shift e [] L_s) in Hun0; simpl in Hun0;
        rewrite Hun0 in Hunspool; discriminate Hunspool
    end.
Qed.

Lemma contains_app_if_spine : forall σ S e1 e2 ec et ef args e_con,
  contains σ S (EApp e1 e2) e_con ->
  unspool_app (EApp e1 e2) [] = (EIf ec et ef, args) ->
  contains σ S (EIf ec (fold_left EApp args et) (fold_left EApp args ef)) e_con.
Proof.
  intros σ S e1 e2 ec et ef args e_con Hcont Hunspool.
  destruct (contains_spine_if σ S _ _ Hcont [] [] (Forall2_nil _) ec et ef args Hunspool)
    as [head_c [args_c [Heq [Hhead Hargs]]]].
  simpl in Heq. rewrite Heq.
  destruct (contains_if_inv σ S ec et ef head_c Hhead) as [[Hc Ht] | [Hc Hf]].
  - apply Cont_If_True; [exact Hc | apply contains_fold_left_app; assumption].
  - apply Cont_If_False; [exact Hc | apply contains_fold_left_app; assumption].
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

Lemma ite_leaf_clos_contains : forall σ S Γ ec Γ1 e1 Γ2 e2 e_c,
  contains σ S (EIf ec (EThunk Γ1 e1) (EThunk Γ2 e2)) e_c ->
  contains σ S (ite_leaf Γ ec (EThunk Γ1 e1) (EThunk Γ2 e2)) e_c.
Proof.
  intros σ S Γ ec Γ1 e1 Γ2 e2 e_c Hc.
  unfold ite_leaf. simpl.
  destruct e1 as [| | | | | x1 b1 | | | | | | | ]; try exact Hc.
  destruct e2 as [| | | | | x2 b2 | | | | | | | ]; try exact Hc.
  destruct (env_eqb Γ1 Γ2 && String.eqb x1 x2)%bool eqn:Hx; [| exact Hc].
  apply andb_prop in Hx as [Hxe Hxx].
  apply env_eqb_eq in Hxe. apply String.eqb_eq in Hxx. subst Γ2 x2.
  destruct (contains_if_inv σ S ec _ _ e_c Hc) as [[Hmc Hct] | [Hmc Hcf]].
  - destruct (contains_clos_inv σ S Γ1 x1 b1 e_c Hct) as [Γc [bc [Heq [Hsx [Henv Hb]]]]].
    subst e_c. apply Cont_Thunk; [exact Henv |].
    apply Cont_Lam; [exact Hsx | apply Cont_If_True; assumption].
  - destruct (contains_clos_inv σ S Γ1 x1 b2 e_c Hcf) as [Γc [bc [Heq [Hsx [Henv Hb]]]]].
    subst e_c. apply Cont_Thunk; [exact Henv |].
    apply Cont_Lam; [exact Hsx | apply Cont_If_False; assumption].
Qed.

(** The four clauses that merge two identical or matching value forms, the
    lambda closures last *)


Ltac merge_leaf_rest et ef Hc Hcases :=
  destruct et; destruct ef; simpl; try exact Hc;
  try exact (ite_leaf_clos_contains _ _ · _ _ _ _ _ _ Hc);
  try (match goal with |- contains _ _ (match ?b with _ => _ end) _ => destruct b; exact Hc end);
  [ destruct (dec_eqb coercion_eq_dec _ _) eqn:Hx; [| exact Hc];
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


Fixpoint esize (e : expr) : nat :=
  match e with
  | EApp f a => 1 + esize f + esize a
  | _ => 1
  end.

(** A symbolic term with only symbolic variables reads the same formula in
    every environment that binds no symbolic variable. *)
Lemma sym_scoped_nil_expr_to_pc : forall S Γ e pc,
  sym_scoped S nil e -> sym_free_env S Γ ->
  expr_to_pc · e = Some pc -> expr_to_pc Γ e = Some pc.
Proof.
  intros S Γ e. induction e; intros pc Hsc Hfree Hpc; simpl in Hpc; try discriminate.
  - inversion Hsc as [L0 x0 Hx | | | | | | | | | | | |]; subst.
    destruct Hx as [[] | Hx]. simpl. rewrite (Hfree v Hx). exact Hpc.
  - exact Hpc.
  - exact Hpc.
  - inversion Hsc as [| | | | L0 f a Hscf Hsca | | | | | | | |]; subst.
    simpl in Hpc |- *.
    destruct (expr_to_pc · e1) as [pc1|] eqn:E1; [| discriminate].
    destruct pc1 as [x|l|q qs]; try (destruct (expr_to_pc · e2); discriminate).
    destruct (expr_to_pc · e2) as [pc2|] eqn:E2; [| discriminate].
    rewrite (IHe1 (PCPrim q qs) Hscf Hfree eq_refl), (IHe2 pc2 Hsca Hfree eq_refl). exact Hpc.
Qed.

Lemma sym_solvable_denotes : forall S e,
  sym_scoped S nil e -> Solvable · e -> exists pc, denotes S e pc /\ expr_to_pc · e = Some pc.
Proof.
  intros S e Hsc Hsolv.
  destruct (solvable_expr_to_pc · e Hsolv) as [pc Hpc].
  exists pc. split; [| exact Hpc].
  intros Γ Hfree. exact (sym_scoped_nil_expr_to_pc S Γ e pc Hsc Hfree Hpc).
Qed.

Lemma denotes_op_fold : forall S args pcs h qhead qacc,
  Forall2 (denotes S) args pcs ->
  denotes S h (PCPrim qhead qacc) ->
  denotes S (fold_left EApp args h) (PCPrim qhead (qacc ++ pcs)).
Proof.
  intros S args pcs h qhead qacc H. revert h qacc.
  induction H as [| a pa args pcs Ha Hargs IH]; intros h qacc Hh.
  - rewrite app_nil_r. exact Hh.
  - simpl. replace (qacc ++ pa :: pcs) with ((qacc ++ pa :: nil) ++ pcs)
      by (rewrite <- app_assoc; reflexivity).
    apply IH. intros Γ Hfree. simpl. rewrite (Hh Γ Hfree), (Ha Γ Hfree). reflexivity.
Qed.

Lemma unspool_esize : forall e acc head args arg,
  unspool_app e acc = (head, args) -> In arg args ->
  In arg acc \/ esize arg < esize e.
Proof.
  induction e; intros acc head args arg Hu Hin; simpl in Hu;
    try (injection Hu as <- <-; left; exact Hin).
  destruct (IHe1 (e2 :: acc) head args arg Hu Hin) as [Hin2 | Hlt].
  - destruct Hin2 as [-> | Hin2]; [right; simpl; lia | left; exact Hin2].
  - right; simpl; lia.
Qed.

(**
  The key lemma. A well-formed boolean formula (correct arities) and its
  concrete instance read the same SMT value under the model. This is what
  lines up Rule Case's two sides: the symbolic scrutinee folds by its value,
  and the concrete scrutinee, a variable-free formula, folds by the same value.
*)
Lemma wellformed_contains_denote : forall n σ S es ec pc,
  esize es <= n ->
  contains σ S es ec -> denotes S es pc -> pc_arities_ok pc = true ->
  denote σ S ec (pc_value σ pc).
Proof.
  induction n as [| n IH]; intros σ S es ec pc Hn Hc Hden Har.
  - destruct es; simpl in Hn; lia.
  - pose proof (Hden · (sym_free_env_empty S)) as Hpc0.
    destruct es as [ x | l | p | d | f a | | | | | | | | ];
      simpl in Hpc0; try discriminate Hpc0.
    + (* EVar x *)
      injection Hpc0 as <-.
      inversion Hc; subst.
      * (* Cont_Var_Bound: S x = false contradicts denotes *)
        exfalso.
        match goal with [ Hxf : S x = false |- _ ] =>
          assert (Hfree : sym_free_env S (ExtendEnv x (MkClosure · (EBot BUndefined)) ·))
            by (intros y Hy; simpl; destruct (string_dec y x) as [->|];
                [rewrite Hxf in Hy; discriminate | reflexivity]);
          pose proof (Hden _ Hfree) as Hcap; simpl in Hcap;
          destruct (string_dec x x); [discriminate Hcap | congruence] end.
      * (* Cont_Var_Sym: ec = ELit (σ x) *)
        simpl. apply denote_lit.
      * (* Cont_Denote: impossible for a variable *) kill_denote.
    + (* ELit l *)
      injection Hpc0 as <-. apply contains_lit_inv in Hc. subst ec. apply denote_lit.
    + (* EPrimOp p *)
      injection Hpc0 as <-. apply contains_primop_inv in Hc. subst ec.
      simpl. exists (PCPrim p nil). split; [intros Γ _; reflexivity | reflexivity].
    + (* EApp f a *)
      assert (Hsolv : Solvable · (EApp f a)) by (eapply denotes_solvable; exact Hden).
      assert (Hop : is_op_app (EApp f a) = true)
        by (inversion Hsolv as [ | | | f0 a0 Hop Hf Ha]; exact Hop).
      destruct (is_op_app_unspool (EApp f a) Hop) as [q [args Hunspool_es]].
      destruct (expr_to_pc_op_app (EApp f a) · pc Hop Hpc0) as [q0 [pcs Hpceq]]. subst pc.
      destruct (denotes_unspool (EApp f a) S q0 pcs q args Hden Hunspool_es) as [Hq Hargs_den].
      subst q0.
      simpl in Har. apply andb_prop in Har as [Hlen_ar Har_args].
      apply Nat.eqb_eq in Hlen_ar.
      assert (Hlen : length args = primop_arity q)
        by (rewrite (Forall2_length Hargs_den); exact Hlen_ar).
      inversion Hc as [ | | | | | | | | fs as_ f_c a_c Hcf Hca | | | | | | | | es0 p0 args0 lv0 Hun0 Har0 Hg0 Hd0 ];
        subst.
      * (* Cont_App: read the whole saturated spine of ec *)
        destruct (contains_unspool_primop σ S f f_c Hcf (a :: nil) (a_c :: nil)
                    (Forall2_cons a a_c Hca (Forall2_nil _)) ltac:(discriminate) q args
                    Hunspool_es Hlen) as [args_c [Hunspool_ec Hargs_c]].
        assert (Hsizes : Forall (fun arg => esize arg < esize (EApp f a)) args).
        { apply Forall_forall. intros arg Hin.
          destruct (unspool_esize (EApp f a) [] (EPrimOp q) args arg Hunspool_es Hin)
            as [[] | Hlt]. exact Hlt. }
        assert (Hpairs : Forall2 (fun ac pcarg => denote σ S ac (pc_value σ pcarg)) args_c pcs).
        { clear Hunspool_ec Hc Hcf Hca Hunspool_es Hlen_ar Hlen Hden Hpc0.
          revert pcs Hargs_den Har_args Hsizes.
          induction Hargs_c as [| arg ac0 args1 argsc1 Hca0 Hcrest IHc];
            intros pcs Hargs_den Har_args Hsizes.
          - inversion Hargs_den; subst. constructor.
          - inversion Hargs_den as [| a1 pc1 args2 pcs1 Hda Hdrest]; subst.
            inversion Hsizes as [| a2 tl2 Hsz Hsztl]; subst.
            simpl in Har_args. apply andb_prop in Har_args as [Har1 Harrest].
            constructor.
            + apply (IH σ S arg ac0 pc1); [lia | exact Hca0 | exact Hda | exact Har1].
            + apply IHc; assumption. }
        assert (Hec_eq : EApp f_c a_c = fold_left EApp args_c (EPrimOp q))
          by (symmetry; apply (unspool_fold_left (EApp f_c a_c) [] (EPrimOp q) args_c Hunspool_ec)).
        assert (Hexpcs : exists pcs', Forall2 (denotes S) args_c pcs'
                         /\ map (pc_value σ) pcs' = map (pc_value σ) pcs).
        { clear -Hpairs. induction Hpairs as [| ac pcarg args_c0 pcs0 [pc' [Hd' Hv']] _ [pcs'' [Hds Hvs]]].
          - exists nil. split; [constructor | reflexivity].
          - exists (pc' :: pcs''). split; [constructor; assumption |].
            simpl. rewrite Hv', Hvs. reflexivity. }
        destruct Hexpcs as [pcs' [Hds Hvs]].
        exists (PCPrim q pcs'). split.
        -- rewrite Hec_eq.
           apply (denotes_op_fold S args_c pcs' (EPrimOp q) q nil Hds).
           intros Γ _; reflexivity.
        -- simpl. change (prim_value q (map (pc_value σ) pcs') = prim_value q (map (pc_value σ) pcs)).
           rewrite Hvs. reflexivity.
      * (* Cont_Denote: ec = ELit lv0 *)
        assert (Hden_es : denote σ S (EApp f a) (pc_value σ (PCPrim q pcs)))
          by (exists (PCPrim q pcs); split; [exact Hden | reflexivity]).
        pose proof (denote_functional σ S (EApp f a) lv0 (pc_value σ (PCPrim q pcs)) Hd0 Hden_es) as He.
        rewrite He. apply denote_lit.
Qed.

(**
  What merge keeps of an instance. Merging a branch either keeps the concrete
  instance directly (contains), or turns two solvable arms into an SMT
  if-then-else formula that reads the same value as the concrete instance
  (smt_ite_kept), or wraps the merged branch in a cast, which both sides fold
  to undefined (merge_ite_cast).
*)
Definition smt_ite_kept (σ : valuation) (S : symvars) (m e_c : expr) : Prop :=
  exists ec et ef,
    m = reduce_prim op_ite (ec :: et :: ef :: nil) /\
    sym_scoped S nil ec /\ sym_scoped S nil et /\ sym_scoped S nil ef /\
    Solvable · ec /\ Solvable · et /\ Solvable · ef /\
    contains σ S (EIf ec et ef) e_c.

Definition merge_keeps (σ : valuation) (S : symvars) (m e_c : expr) : Prop :=
  contains σ S m e_c \/ smt_ite_kept σ S m e_c \/ (is_cast m = true /\ is_cast e_c = true).

Lemma smt_ite_prove : forall σ S Γ ec et ef e_c,
  sym_scoped S nil ec -> sym_scoped S nil et -> sym_scoped S nil ef ->
  Solvable Γ et -> Solvable Γ ef ->
  contains σ S (EIf ec et ef) e_c ->
  smt_ite_kept σ S (reduce_prim op_ite (ec :: et :: ef :: nil)) e_c.
Proof.
  intros σ S Γ ec et ef e_c Hscc Hsct Hscf Ht Hf Hc.
  assert (Hec : Solvable · ec).
  { destruct (contains_if_inv σ S ec et ef e_c Hc) as [[[pc [Hd _]] _] | [[pc [Hd _]] _]];
      exact (denotes_solvable S ec pc Hd). }
  exists ec, et, ef.
  split; [reflexivity |].
  split; [exact Hscc |]. split; [exact Hsct |]. split; [exact Hscf |].
  split; [exact Hec |].
  split; [exact (solvable_in_empty_env Γ et Ht) |].
  split; [exact (solvable_in_empty_env Γ ef Hf) | exact Hc].
Qed.

Lemma ite_leaf_contains : forall σ S Γ ec et ef e_c,
  sym_scoped S nil ec -> sym_scoped S nil et -> sym_scoped S nil ef ->
  contains σ S (EIf ec et ef) e_c -> merge_keeps σ S (ite_leaf Γ ec et ef) e_c.
Proof.
  intros σ S Γ ec et ef e_c Hscc Hsct Hscf Hc.
  assert (Hcases := contains_if_inv σ S ec et ef e_c Hc).
  unfold merge_keeps, ite_leaf.
  destruct (decompose_con_app et) as [[d1 a1]|] eqn:E1;
  destruct (decompose_con_app ef) as [[d2 a2]|] eqn:E2.
  - left.
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
  - destruct (solvable_dec Γ et) as [Ht |]; [destruct (solvable_dec Γ ef) as [Hf |] |].
    + right. left. exact (smt_ite_prove σ S Γ ec et ef e_c Hscc Hsct Hscf Ht Hf Hc).
    + left. exact Hc.
    + left. merge_leaf_rest et ef Hc Hcases.
  - destruct (solvable_dec Γ et) as [Ht |]; [destruct (solvable_dec Γ ef) as [Hf |] |].
    + right. left. exact (smt_ite_prove σ S Γ ec et ef e_c Hscc Hsct Hscf Ht Hf Hc).
    + left. exact Hc.
    + left. merge_leaf_rest et ef Hc Hcases.
  - destruct (solvable_dec Γ et) as [Ht |]; [destruct (solvable_dec Γ ef) as [Hf |] |].
    + right. left. exact (smt_ite_prove σ S Γ ec et ef e_c Hscc Hsct Hscf Ht Hf Hc).
    + left. exact Hc.
    + left. merge_leaf_rest et ef Hc Hcases.
Qed.

Lemma ite_contains : forall σ S Γ et ec ef e_c,
  sym_scoped S nil ec -> sym_scoped S nil et -> sym_scoped S nil ef ->
  contains σ S (EIf ec et ef) e_c -> merge_keeps σ S (ite Γ ec et ef) e_c.
Proof.
  intros σ S Γ et. induction et; intros ec ef e_c Hscc Hsct Hscf Hc;
    try (rewrite ite_leaf_of by (left; reflexivity);
         apply ite_leaf_contains; assumption).
  destruct ef; try (rewrite ite_leaf_of by (right; reflexivity);
                    apply ite_leaf_contains; assumption).
  rewrite ite_cast. unfold merge_keeps.
  destruct (dec_eqb coercion_eq_dec c c0) eqn:Hx; [| left; exact Hc].
  apply dec_eqb_eq in Hx. subst c0.
  right. right. split; [reflexivity |].
  destruct (contains_if_inv σ S ec (ECast et c) (ECast ef c) e_c Hc) as [[_ Hcast]|[_ Hcast]];
    destruct (contains_cast_inv σ S _ c e_c Hcast) as [ec' [-> _]]; reflexivity.
Qed.

Lemma merge_contains : forall σ S Γ es ec,
  sym_scoped S nil es ->
  contains σ S es ec ->
  merge_keeps σ S (merge Γ es) ec.
Proof.
  intros σ S Γ es ec Hsc H. destruct es; simpl; try (left; exact H).
  inversion Hsc as [| | | | | | | | | | L1 ec1 et1 ef1 Hscc Hsct Hscf | |]; subst.
  apply ite_contains; assumption.
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
  - left. injection Hunspool as <- <-. exists ec, L_c.
    split; [destruct ec; try discriminate; reflexivity |].
    split; [eapply Cont_Thunk_Outer; eassumption | exact HL].
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
  contains σ S (make_con_app d (map (delay Γs) args_s))
               (make_con_app d (map (delay Γc) args_c)).
Proof.
  intros σ S Γs Γc d args_s args_c Henv Hargs.
  unfold make_con_app. apply contains_fold_left_app; [| apply Cont_Con].
  induction Hargs; simpl; constructor; [apply contains_delay |]; assumption.
Qed.

Fixpoint concore_soundness_fix (k0 : fuel) (Φ : path_condition) (Γs : environment) (e_sym v_sym : expr)
  (Heval : eval k0 Φ Γs e_sym v_sym) {struct Heval} :
  k0 = Inf ->
  forall Γc σ S e_con,
    σ ⊨ Φ ->
    contains_env σ S Γs Γc ->
    contains σ S e_sym e_con ->
    concore_expr e_con ->
    closed_instance Γc e_con ->
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
    closed_program Γc esc ->
    Forall (scoped_alt (dom_env Γc)) altsc ->
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
    | kv Φ Γ ef ea ef' er Hcomp Heval_f Heval_app2
    | kv Φ Γ b
    | kv Φ Γ ef ea p args args' Hunspool Harity Hargs
    | kv Φ Γ x e
    | kv Φ Γ ef γ ea γ_a γ_r er Hdecomp Heval_pushed
    | kv Φ Γ e1 e2 ec et ef args er Hunspool_if Heval_arms
    | kv Φ Γ b ea
    | kv Φ Γ es alts es' er Heval_es Hfold
    | kv Φ Γ ec et ef ec' et' ef' pc_c Heval_c Hpc Heval_t Heval_f
    | kv Φ Γ γ
    | kv Φ Γ e Hunsat
    | kv Φ Γ τ
    | kv Φ Γ Γ' e e' Heval_t
    | Φ Γ e
    ]; intros Hk0; try discriminate Hk0; injection Hk0 as Hk0; subst kv; intros Γc σ S e_con Hmod Henv Hcont Hcon Hcl.
  - (* Eval_Var *)
    assert (Hfree : sym_free_env S Γ)
      by (destruct (contains_env_sym_free σ S Γ Γc Henv) as [Hf _]; exact Hf).
    assert (Heq : e_con = EVar x) by (eapply contains_var_bound; eassumption).
    subst e_con.
    destruct (contains_lookup_env σ S Γ Γc x Γ' e Henv Hlookup) as [Γ'c [ec [Hlookc [Henv' Hcont']]]].
    assert (Hcon' : concore_expr ec) by (apply (lookup_env_concore σ S Γ Γc x Γ' e Γ'c ec Henv Hlookup Hlookc)).
    destruct (closed_instance_program Γc (EVar x) Hcl eq_refl) as [HΓc _].
    destruct (lookup_env_scoped Γc x Γ'c ec HΓc Hlookc) as [HΓ'c Hsc'].
    destruct (concore_soundness_fix Inf Φ Γ' e e' Heval_x eq_refl Γ'c σ S ec Hmod Henv' Hcont' Hcon'
                (or_introl (conj HΓ'c Hsc'))) as [v_con [Hevalc Hcont_v]].
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
    destruct (contains_unspool_con σ S esp e_con Hcont [] [] (Forall2_nil _) d args Hunspool_con)
      as [args_c [Hunspool_c Hargs_c]].
    exists (make_con_app d (map (delay Γc) args_c)). split.
    + unfold eval_con. exact (Eval_Con Unlimited pc_true Γc e_con d args_c Hunspool_c).
    + exact (contains_con_value σ S Γ Γc d args args_c Henv Hargs_c).
  - (* Eval_Cast *)
    apply contains_cast_inv in Hcont as [ec [Heq Hcont_e]]; subst.
    inversion Hcon as [| | | | | | | ec0 γ0 Hcon_e | | | | | | ]; subst.
    destruct (closed_instance_program Γc _ Hcl eq_refl) as [HΓc Hsc].
    inversion Hsc as [| | | | | | | L1 e1 γ1 Hsce | | | | |]; subst.
    destruct (concore_soundness_fix Inf Φ Γ e e' Heval_e eq_refl Γc σ S ec Hmod Henv Hcont_e Hcon_e
                (or_introl (conj HΓc Hsce))) as [vc [Hevalc Hcont_v]].
    exists (cast_expr vc γ). split; [unfold eval_con; apply Eval_Cast; exact Hevalc | apply cast_expr_contains; exact Hcont_v].
  - (* Eval_AppAbs *)
    assert (Hfree : sym_free_env S Γ)
      by (destruct (contains_env_sym_free σ S Γ Γc Henv) as [Hf _]; exact Hf).
    destruct (contains_app_inv σ S Γ (EThunk Γ' (ELam x eb)) ea e_con Hfree Hcont) as
      [[fc [ac [Heq [Hcont_f Hcont_a]]]] | [Hsolv _]];
      [subst e_con | exfalso; inversion Hsolv].
    apply contains_clos_inv in Hcont_f as [Γ'c [ebc [Heq_f [Hsx [Henv_clos Hcont_b]]]]]; subst.
    inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | ]; subst.
    inversion Hf as [| | | | | | | | | | | | | Γ0 e0 Henv_clos_c Hcon_lam]; subst.
    inversion Hcon_lam as [| | | | | x0 body Hcon_b | | | | | | | | ]; subst.
    destruct (closed_instance_program Γc _ Hcl eq_refl) as [HΓc Hsc].
    inversion Hsc as [| | | | L0 f0 a0 Hscf Hsca | | | | | | | |]; subst.
    inversion Hscf as [| | | | | | | | | | | | L1 Γ1 e1 HΓ'c Hsclam]; subst.
    inversion Hsclam as [| | | | | L2 x2 b2 Hscb | | | | | | |]; subst.
    assert (Henv_ext : contains_env σ S (ExtendEnv x (MkClosure Γ ea) Γ') (ExtendEnv x (MkClosure Γc ac) Γ'c)).
    { apply Cont_Env_Extend; assumption. }
    destruct (concore_soundness_fix Inf Φ (extend_env Γ' x Γ ea) eb eb' Heval_b eq_refl
                (ExtendEnv x (MkClosure Γc ac) Γ'c) σ S ebc Hmod Henv_ext Hcont_b Hcon_b
                (or_introl (conj (Scoped_Env_Extend x Γc ac Γ'c HΓc Hsca HΓ'c) Hscb)))
      as [v_con [Heval_b' Hcont_v]].
    exists v_con. split; [| exact Hcont_v].
    unfold eval_con. apply Eval_AppAbs. exact Heval_b'.
  - (* Eval_AppSpine *)
    apply (eval_app_spine_sound Φ Γ Γc σ S ef ea ef' er e_con Hmod Henv Hcont Hcon Hcl Hcomp).
    + intros Γc0 e_con0 Henv0 Hcont0 Hcon0 Hcl0.
      exact (concore_soundness_fix Inf Φ Γ ef ef' Heval_f eq_refl Γc0 σ S e_con0 Hmod Henv0 Hcont0 Hcon0 Hcl0).
    + intros Γc0 e_con0 Henv0 Hcont0 Hcon0 Hcl0.
      exact (concore_soundness_fix Inf Φ Γ (EApp ef' ea) er Heval_app2 eq_refl Γc0 σ S e_con0 Hmod Henv0 Hcont0 Hcon0 Hcl0).
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
      [| rewrite Hunspool in Hun0; injection Hun0 as Hp0 Hargs0; subst p0 args0;
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
    inversion Hcon as [| | | | fc0 ac0 Hcon_f Hcon_a | | | | | | | | | ]; subst.
    destruct (closed_instance_program Γc _ Hcl eq_refl) as [HΓc Hsc].
    inversion Hsc as [| | | | L0 f0 a0 Hscf Hsca | | | | | | | |]; subst.
    assert (Henv_c : concrete_env Γc) by (eapply contains_env_concrete; exact Henv).
    assert (HL : Forall2 (contains σ S) [ea] [ac])
      by (constructor; [exact Hcont_a | constructor]).
    assert (Hne : [ea] <> (@nil expr)) by discriminate.
    destruct (contains_unspool_primop σ S ef fc Hcont_f [ea] [ac] HL Hne p args
               Hunspool Harity) as [args_c [Hunspool_c Hcont_args]].
    assert (Hconcore_args_c : Forall concore_expr args_c).
    { eapply unspool_app_concore; [exact Hunspool_c | exact Hcon_f | constructor; [exact Hcon_a | constructor]]. }
    assert (Hsc_args_c : Forall (scoped (dom_env Γc)) args_c).
    { eapply unspool_app_scoped; [exact Hunspool_c | exact Hscf | constructor; [exact Hsca | constructor]]. }
    assert (Hstep : exists args_c', Forall2 (eval Inf pc_true Γc) args_c args_c'
                    /\ Forall2 (contains σ S) args' args_c' /\ Forall closed_term args_c').
    { clear Hunspool Harity Hunspool_c.
      revert args_c Hcont_args Hconcore_args_c Hsc_args_c.
      induction Hargs as [| a a' args_tl args'_tl Ha Hargs_tl IHargs];
        intros args_c Hcont_args Hconcore_args_c Hsc_args_c.
      - inversion Hcont_args; subst.
        exists []. split; [constructor | split; constructor].
      - inversion Hcont_args as [| a0 ac1 args_tl0 args_c_tl Hcont_a1 Hcont_tl Heqa Heqargs]; subst.
        inversion Hconcore_args_c as [| ac2 args_c_tl2 Hcon_a1 Hcon_tl]; subst.
        inversion Hsc_args_c as [| ac3 args_c_tl3 Hsc_a1 Hsc_tl]; subst.
        destruct (concore_soundness_fix Inf Φ Γ a a' Ha eq_refl Γc σ S ac1 Hmod Henv Hcont_a1 Hcon_a1
                    (or_introl (conj HΓc Hsc_a1)))
          as [v_a [Heval_a Hcont_va]].
        destruct (IHargs args_c_tl Hcont_tl Hcon_tl Hsc_tl) as [args_c'_tl [Heval_tl [Hcont_tl' Hcl_tl]]].
        exists (v_a :: args_c'_tl).
        split; [constructor; assumption | split; [constructor; assumption | constructor; [| exact Hcl_tl]]].
        exact (closed_eval Γc ac1 v_a Henv_c Hcon_a1 (conj HΓc Hsc_a1) Heval_a).
    }
    destruct Hstep as [args_c' [Heval_args_c [Hcont_args' Hcl_args']]].
    exists (reduce_prim p args_c').
    split.
    + unfold eval_con. eapply Eval_AppPrim.
      * exact Hunspool_c.
      * assert (Hlen : length args_c = length args) by (symmetry; eapply Forall2_length; exact Hcont_args).
        rewrite Hlen. exact Harity.
      * exact Heval_args_c.
    + apply reduce_prim_contains; [exact Hcl_args' | exact Hcont_args'].
  - (* Eval_Lam *)
    apply contains_lam_inv in Hcont as [bodyc [Heq [Hsx Hcont_body]]]; subst.
    exists (EThunk Γc (ELam x bodyc)).
    split; [apply Eval_Lam | apply Cont_Thunk; [exact Henv | apply Cont_Lam; assumption]].
  - (* Eval_AppCast *)
    eapply eval_app_cast_sound; try eassumption.
    intros Γc0 σ0 e_con0 Hmod0 Henv0 Hcont0 Hcon0 Hcl0.
    exact (concore_soundness_fix Inf Φ Γ (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r) er Heval_pushed eq_refl Γc0 σ0 S e_con0 Hmod0 Henv0 Hcont0 Hcon0 Hcl0).
  - (* Eval_AppIf *)
    exact (concore_soundness_fix Inf Φ Γ _ er Heval_arms eq_refl Γc σ S e_con Hmod Henv
             (contains_app_if_spine σ S e1 e2 ec et ef args e_con Hcont Hunspool_if) Hcon Hcl).
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
    inversion Hcon as [| | | | | | es0 alts0 Hcon_es Hcon_alts | | | | | | | ]; subst.
    destruct (closed_instance_program Γc _ Hcl eq_refl) as [HΓc Hsc].
    inversion Hsc as [| | | | | | L0 es1 alts1 Hsc_es Hsc_alts | | | | | |]; subst.
    destruct (concore_soundness_fix Inf Φ Γ es es' Heval_es eq_refl Γc σ S esc Hmod Henv Hcont_es Hcon_es
                (or_introl (conj HΓc Hsc_es))) as [vc_s [Heval_esc Hcont_vs]].
    destruct (merge_contains σ S Γ es' vc_s Hcont_vs) as [Hcont_merge | [Hinert_s Hinert_c]].
    + destruct (concore_soundness_fold_fix Inf Φ Γ (merge Γ es') alts er Hfold eq_refl Γc σ S esc altsc Hmod Henv Hcon_es Hcon_alts
                  (conj HΓc Hsc_es) Hsc_alts
                  (ex_intro _ vc_s (conj Heval_esc Hcont_merge)) Hcont_alts) as [v_con [Heval_case Hcont_er]].
      exists v_con. split; assumption.
    + rewrite (fold_alts_inert _ _ _ _ _ er Hinert_s Hfold).
      exists (EBot BUndefined). split; [| apply Cont_Bot].
      unfold eval_con. eapply Eval_Case; [exact Heval_esc |].
      rewrite (merge_not_if Γc vc_s (inert_not_if vc_s Hinert_c)).
      apply fold_alts_inert_undefined. exact Hinert_c.
  - (* Eval_If *)
    assert (Hfree : sym_free_env S Γ)
      by (destruct (contains_env_sym_free σ S Γ Γc Henv) as [Hf _]; exact Hf).
    inversion Hcont; subst.
    + assert (Hcond' : models_cond σ S ec')
        by (apply eval_models_cond with (Φ:=Φ)(Γ:=Γ)(ec:=ec); assumption).
      assert (Hpc_mod : σ ⊨ pc_c) by (apply (models_cond_pc σ S Γ ec' pc_c Hpc); exact Hcond').
      assert (Hmod_and : σ ⊨ (Φ ∧ pc_c)) by (apply models_and; assumption).
      destruct (concore_soundness_fix Inf (Φ ∧ pc_c) Γ et et' Heval_t eq_refl Γc σ S e_con Hmod_and Henv H4 Hcon Hcl) as [v_con [Hevalc' Hcont_v]].
      exists v_con. split; [exact Hevalc' |]. apply Cont_If_True; [exact Hcond' | exact Hcont_v].
    + assert (Hncond' : models_not_cond σ S ec')
        by (apply eval_models_not_cond with (Φ:=Φ)(Γ:=Γ)(ec:=ec); assumption).
      assert (Hpc_mod : σ ⊨ (¬ pc_c)) by (apply (models_not_cond_pc σ S Γ ec' pc_c Hpc); exact Hncond').
      assert (Hmod_and : σ ⊨ (Φ ∧ ¬ pc_c)) by (apply models_and; assumption).
      destruct (concore_soundness_fix Inf (Φ ∧ ¬ pc_c) Γ ef ef' Heval_f eq_refl Γc σ S e_con Hmod_and Henv H4 Hcon Hcl) as [v_con [Hevalc' Hcont_v]].
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
    destruct (contains_thunk_inv σ S Γ' e e_con Hcont)
      as [[Γ'c [ec [Heq [Henv' Hcont_e]]]] | [Γ'c [Henv' [Hcont_e Hthunk]]]].
    + subst e_con.
      inversion Hcon as [| | | | | | | | | | | | | Γ0 e0 Henv_c He_c]; subst.
      assert (Hcl' : closed_instance Γ'c ec).
      { left. destruct Hcl as [[_ Hs] | [_ Hs]]; inversion Hs; subst; split; assumption. }
      destruct (concore_soundness_fix Inf Φ Γ' e e' Heval_t eq_refl Γ'c σ S ec
                  Hmod Henv' Hcont_e He_c Hcl') as [v_con [Hevalc Hcont_v]].
      exists v_con. split; [| exact Hcont_v].
      unfold eval_con. apply Eval_Thunk. exact Hevalc.
    + assert (Hcl' : closed_instance Γ'c e_con).
      { right. split; [exact Hthunk |].
        destruct Hcl as [[_ Hs] | [_ Hs]]; [| exact Hs].
        destruct e_con; try discriminate Hthunk. exact (scoped_thunk_any _ _ _ _ Hs). }
      destruct (concore_soundness_fix Inf Φ Γ' e e' Heval_t eq_refl Γ'c σ S e_con
                  Hmod Henv' Hcont_e Hcon Hcl') as [v_con [Hevalc Hcont_v]].
      exists v_con. split; [| exact Hcont_v].
      destruct e_con; try discriminate Hthunk.
      unfold eval_con in *. exact (eval_thunk_ambient_env Inf pc_true Γ'c Γc _ _ _ Hevalc).
}
{
  destruct Hfold as
    [ kv Φ Γ ec et ef alts et' ef' pc_c Hpc Hfold_t Hfold_f
    | kv Φ Γ ec et ef alts Hpc_none
    | kv Φ Γ e d ea xs ep alts er Hdec Halt Heval_ep
    | kv Φ Γ b alts
    | kv Φ Γ e alts Hnothead Hnoalt Hnotbot
    ]; intros Hk0; subst kv; intros Γc σ S esc altsc Hmod Henv Hcon_esc Hcon_altsc Hcl_esc Hsc_altsc Hvc Halts.
  - (* FoldAlts_If *)
    destruct Hvc as [vc_s [Heval_esc Hcont_vs]].
    inversion Hcont_vs; subst.
    + assert (Hpc_mod : σ ⊨ pc_c) by (apply (models_cond_pc σ S Γ ec pc_c Hpc); assumption).
      assert (Hmod_and : σ ⊨ (Φ ∧ pc_c)) by (apply models_and; assumption).
      destruct (concore_soundness_fold_fix Inf (Φ ∧ pc_c) Γ et alts et' Hfold_t eq_refl Γc σ S esc altsc Hmod_and Henv Hcon_esc Hcon_altsc Hcl_esc Hsc_altsc
                  (ex_intro _ vc_s (conj Heval_esc H4)) Halts) as [v_con [Heval_case Hcont_er]].
      exists v_con. split; [exact Heval_case | apply Cont_If_True; assumption].
    + assert (Hpc_mod : σ ⊨ (¬ pc_c)) by (apply (models_not_cond_pc σ S Γ ec pc_c Hpc); assumption).
      assert (Hmod_and : σ ⊨ (Φ ∧ ¬ pc_c)) by (apply models_and; assumption).
      destruct (concore_soundness_fold_fix Inf (Φ ∧ ¬ pc_c) Γ ef alts ef' Hfold_f eq_refl Γc σ S esc altsc Hmod_and Henv Hcon_esc Hcon_altsc Hcl_esc Hsc_altsc
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
    destruct Hcl_esc as [HΓc Hsc_esc].
    assert (Hcl_vcs : closed_term vc_s)
      by exact (closed_eval Γc esc vc_s Henv_concrete Hcon_esc (conj HΓc Hsc_esc) Heval_esc).
    assert (Hcl_ext : closed_instance (extend_env_multi Γc xs ea_c Γc) ep_c).
    { left. split.
      - apply scoped_env_extend_multi; [exact HΓc | exact HΓc |].
        pose proof (proj2 (unspool_app_scoped nil vc_s [] (ECon d) ea_c Hunspool_vcs Hcl_vcs (Forall_nil _))) as Hea.
        eapply Forall_impl; [| exact Hea]. intros a Ha. exact (closed_term_scoped _ a Ha).
      - rewrite dom_env_extend_multi. exact (find_alt_scoped _ d altsc xs ep_c Hsc_altsc Halt_c). }
    assert (Henv_ext : contains_env σ S (extend_env_multi Γ xs ea Γ) (extend_env_multi Γc xs ea_c Γc)).
    { apply contains_env_extend_multi; assumption. }
    destruct (concore_soundness_fix Inf Φ (extend_env_multi Γ xs ea Γ) ep er Heval_ep eq_refl
                (extend_env_multi Γc xs ea_c Γc) σ S ep_c Hmod Henv_ext Hcont_ep Hcon_ep_c Hcl_ext)
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
          { inversion Hcont_head; subst; try reflexivity; try (simpl in Hif_head; discriminate).
            match goal with
            | [ Ht : is_thunk ?e = true |- _ ] => destruct e; try discriminate Ht; reflexivity
            end. }
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
  closed_program Γc e_con ->
  Φ ; Γs ⊢ e_sym ⇓ v_sym ->
  exists v_con,
    Γc ⊢ᶜ e_con ⇓ᶜ v_con /\
    contains σ S v_sym v_con.
Proof.
  intros Φ Γs Γc σ S e_sym e_con v_sym Hmod Henv Hcont Hcon Hcl Heval.
  exact (concore_soundness_fix Inf Φ Γs e_sym v_sym Heval eq_refl Γc σ S e_con Hmod Henv Hcont Hcon
           (or_introl Hcl)).
Qed.


(** Top-level Soundness for whole programs starting from · *)
Corollary concore_soundness_top : forall Φ σ S e_sym e_con v_sym,
  σ ⊨ Φ ->
  contains σ S e_sym e_con ->
  concore_expr e_con ->
  closed_term e_con ->
  Φ ; · ⊢ e_sym ⇓ v_sym ->
  exists v_con,
    ⊢ᶜ e_con ⇓ᶜ v_con /\
    contains σ S v_sym v_con.
Proof.
  intros Φ σ S e_sym e_con v_sym Hmod Hcont Hcon Hcl Heval.
  apply (concore_soundness Φ · · σ S e_sym e_con v_sym); auto.
  - apply Cont_Env_Empty.
  - exact (conj Scoped_Env_Empty Hcl).
Qed.

Theorem branch_on_bound_variable_has_no_instance : forall σ S x t f e_con,
  ~ contains σ S (ELam x (EIf (EVar x) t f)) e_con.
Proof.
  intros σ S x t f e_con H.
  inversion H as [| | | | | | | | | y bodys bodyc Hx Hbody | | | | | | | es p args l Hu];
    subst; [| discriminate Hu].
  set (binds_x := ExtendEnv x (MkClosure · (EBot BUndefined)) ·).
  assert (Hfree : sym_free_env S binds_x).
  { intros y Hy. simpl. destruct (string_dec y x) as [-> | _];
      [rewrite Hx in Hy; discriminate Hy | reflexivity]. }
  destruct (contains_if_inv σ S _ _ _ _ Hbody) as [[[pc [Hden _]] _] | [[pc [Hden _]] _]];
    specialize (Hden binds_x Hfree); simpl in Hden;
    destruct (string_dec x x); congruence.
Qed.


(**
  The other half of this section, completeness, is in Completeness.v. Its
  proof needs the cost laws of CostLaws.v, and this file does not state them.
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
  - split; [apply Scoped_Env_Empty | apply Scoped_Lit].
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
  - split; [apply Scoped_Env_Empty | repeat constructor].
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
    - apply reduce_prim_contains; [repeat constructor | constructor; [| constructor]].
      apply Cont_If_True; [exact Htrue | apply Cont_Lit].
    - intros Γ. apply Hall. }
  assert (H2 : reduce_prim p [EIf c (ELit l1) (ELit l2)] = reduce_prim p [ELit l2]).
  { eapply (ground_solvable_contains_eq σ' S').
    - apply reduce_prim_contains; [repeat constructor | constructor; [| constructor]].
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
    intros σ S c Hc. apply reduce_prim_contains; [repeat constructor | constructor; [| constructor]].
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
  - discriminate.
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
    - split; [apply Scoped_Env_Empty | repeat constructor].
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

(* ================ (g) a model takes an else-branch ====================== *)

Section ElseBranch.
  Variable l_else : lit.
  Hypothesis negation_holds : prim_value op_not (l_else :: nil) = lit_true.

  Definition else_model : valuation := fun _ => l_else.
  Definition branch_var : var := "x".
  Definition branch_on_x (et ef : expr) : expr := EIf (EVar branch_var) et ef.

  Lemma else_model_refutes_x : models_not_cond else_model (only branch_var) (EVar branch_var).
  Proof.
    exists (PCVar branch_var). split; [| exact negation_holds].
    intros Γ Hfree. simpl. rewrite (Hfree branch_var (only_self branch_var)). reflexivity.
  Qed.

  Corollary else_branch_instance : forall lt lf,
    contains else_model (only branch_var) (branch_on_x (ELit lt) (ELit lf)) (ELit lf).
  Proof. intros lt lf. apply Cont_If_False; [exact else_model_refutes_x | apply Cont_Lit]. Qed.

  Definition truth_alts (lt lf : lit) : list alt :=
    Alt "T" nil (ELit lt) :: Alt "F" nil (ELit lf) :: nil.
  Definition symbolic_match (lt lf : lit) : expr :=
    ECase (branch_on_x (ECon "T") (ECon "F")) (truth_alts lt lf).
  Definition else_match (lt lf : lit) : expr := ECase (ECon "F") (truth_alts lt lf).

  Lemma symbolic_match_runs : forall Φ lt lf,
    Φ ; · ⊢ symbolic_match lt lf ⇓ branch_on_x (ELit lt) (ELit lf).
  Proof.
    intros Φ lt lf. unfold symbolic_match, branch_on_x.
    eapply Eval_Case.
    - eapply Eval_If with (pc_c := PCVar branch_var);
        [apply Eval_SymVar; reflexivity | reflexivity
        | apply eval_nullary_con | apply eval_nullary_con].
    - simpl. eapply FoldAlts_If; [reflexivity | |];
        (eapply FoldAlts_Con; [reflexivity | reflexivity | apply Eval_Lit]).
  Qed.

  Lemma symbolic_match_contains_else_match : forall lt lf,
    contains else_model (only branch_var) (symbolic_match lt lf) (else_match lt lf).
  Proof.
    intros lt lf. apply Cont_Case.
    - apply Cont_If_False; [exact else_model_refutes_x | apply Cont_Con].
    - repeat constructor.
  Qed.

  Lemma else_match_concore : forall lt lf, concore_expr (else_match lt lf).
  Proof. intros lt lf. repeat constructor. Qed.

  Lemma else_model_satisfies_negated_guard : else_model ⊨ (¬ PCVar branch_var).
  Proof. exact negation_holds. Qed.

  Corollary soundness_takes_else_branch : forall lt lf,
    exists v_con,
      · ⊢ᶜ else_match lt lf ⇓ᶜ v_con /\
      contains else_model (only branch_var) (branch_on_x (ELit lt) (ELit lf)) v_con.
  Proof.
    intros lt lf.
    apply (concore_soundness (¬ PCVar branch_var) · · else_model (only branch_var)
             (symbolic_match lt lf) (else_match lt lf)).
    - exact else_model_satisfies_negated_guard.
    - apply Cont_Env_Empty.
    - apply symbolic_match_contains_else_match.
    - apply else_match_concore.
    - split; [apply Scoped_Env_Empty | repeat constructor].
    - apply symbolic_match_runs.
  Qed.

  Lemma else_match_reads_else_arm : forall lt lf, · ⊢ᶜ else_match lt lf ⇓ᶜ ELit lf.
  Proof.
    intros lt lf. unfold eval_con, else_match.
    eapply Eval_Case; [apply eval_nullary_con |].
    simpl. eapply FoldAlts_Con; [reflexivity | reflexivity | apply Eval_Lit].
  Qed.
End ElseBranch.

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
  - match goal with
    | [ Hu : unspool_app (EApp _ _) [] = (EIf _ _ _, _) |- _ ] =>
        simpl in Hu; rewrite Hu in Hun; discriminate Hun
    end.
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
       Comp Γ ef /\ Φ ; Γ ⊢ ef ⇓ ef' /\ Φ ; Γ ⊢ EApp ef' ea ⇓ er).
Proof.
  intros Φ Γ ef ea p args Hsat Hun Hlen [ef' [er [_ [Heval _]]]].
  exact (prim_operator_has_no_value Φ Γ ef ea p args ef' Hsat Hun Hlen Heval).
Qed.

(** ------------------------------------------------------------------------- *)
(** 12.3 Overlap 2: Rule App-Cast against Rule App-Spine                      *)
(** ------------------------------------------------------------------------- *)


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
  forall Γ0 x body γ, cast_expr (EThunk Γ0 (ELam x body)) γ = EThunk Γ0 (ELam x body).

(**
  Rule App-Spine cannot strip the cast and hand the function the plain
  argument: its premise asks for a computation, and a cast is not one.
*)
Lemma app_spine_refuses_the_coerced_operator :
  ~ Comp · coerced_operator.
Proof. intros H. inversion H. Qed.

Lemma no_app_spine_derivation_here : forall ef' er,
  ~ (Comp · coerced_operator /\
     pc_true ; · ⊢ coerced_operator ⇓ ef' /\
     pc_true ; · ⊢ EApp ef' plain_operand ⇓ er).
Proof.
  intros ef' er [Hcomp _].
  exact (app_spine_refuses_the_coerced_operator Hcomp).
Qed.

(** Rule App-Cast pushes the coercion into the argument first, so the same
    function gets a cast argument. *)
Lemma casted_application_by_app_cast :
  · ⊢ᶜ EApp coerced_operator plain_operand
     ⇓ᶜ EThunk (extend_env · "x" · coerced_operand) (ELam "z" (EVar "x")).
Proof.
  unfold eval_con.
  eapply Eval_AppCast with (γ_a := arrow_dom) (γ_r := arrow_cod).
  - apply decomp_arrow_coercion.
  - rewrite <- (closure_cast_erased (extend_env · "x" · coerced_operand)
                                    "z" (EVar "x") arrow_cod).
    apply Eval_Cast.
    eapply Eval_AppSpine with (ef' := EThunk · (ELam "x" capture_body)).
    + apply Comp_Lam.
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

    App-Spine against App-Cast   : a cast is not a computation.
    App-Spine against App-Prim   : a computation has no primitive spine head.
    App-Spine against App-If     : a computation has no branch spine head.
    App-Spine against App-Abs    : a closure is not a computation.
    App-Spine against App-Bot    : a bottom is not a computation.
*)

Ltac prune_absurd :=
  match goal with
  | [ Hs : sat ?F = true, Hu : sat ?F = false |- _ ] => rewrite Hs in Hu; discriminate
  end.

Lemma comp_spine_head : forall Γ ef ea h args,
  Comp Γ ef ->
  unspool_app (EApp ef ea) [] = (h, args) ->
  has_whole_spine_rule h = false.
Proof.
  intros Γ ef ea h args Hcomp Hu.
  replace h with (fst (unspool_app (EApp ef ea) [])) by (rewrite Hu; reflexivity).
  rewrite fst_unspool_app. simpl.
  destruct Hcomp; simpl in *; try reflexivity; assumption.
Qed.

Ltac app_rule_absurd :=
  first
  [ prune_absurd
  | no_con_head
  | match goal with
    | [ H : Comp _ _ |- _ ] => solve [inversion H; subst; simpl in *; discriminate]
    end
  | match goal with
    | [ Hc : Comp _ ?f, Hu : unspool_app (EApp ?f _) [] = (_, _) |- _ ] =>
        solve [pose proof (comp_spine_head _ _ _ _ _ Hc Hu) as Hw; simpl in Hw; discriminate Hw]
    end
  | match goal with
    | [ H : unspool_app (EApp _ _) [] = _ |- _ ] => solve [simpl in H; discriminate H]
    end
  | match goal with
    | [ H1 : unspool_app ?e ?a = _, H2 : unspool_app ?e ?a = _ |- _ ] =>
        solve [rewrite H1 in H2; discriminate H2]
    end ].

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
  sat Φ = true -> Φ ; Γ ⊢ ELam x e0 ⇓ v -> v = EThunk Γ (ELam x e0).
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
  Φ ; Γ ⊢ EApp (EThunk Γ' (ELam x eb)) ea ⇓ v ->
  Φ ; extend_env Γ' x Γ ea ⊢ eb ⇓ v.
Proof.
  intros Φ Γ Γ' x eb ea v Hsat Heval.
  inversion Heval; subst; try app_rule_absurd.
  assumption.
Qed.

Lemma eval_app_bot_inv : forall Φ Γ b ea v,
  sat Φ = true ->
  Φ ; Γ ⊢ EApp (EBot b) ea ⇓ v ->
  v = EBot b.
Proof.
  intros Φ Γ b ea v Hsat Heval.
  inversion Heval; subst; try app_rule_absurd.
  reflexivity.
Qed.

Lemma eval_app_cast_arrow_inv : forall Φ Γ eb γ γ_a γ_r ea v,
  sat Φ = true ->
  decomp_coerc_arrow γ = Some (γ_a, γ_r) ->
  Φ ; Γ ⊢ EApp (ECast eb γ) ea ⇓ v ->
  Φ ; Γ ⊢ ECast (EApp eb (ECast ea (sym_coerc γ_a))) γ_r ⇓ v.
Proof.
  intros Φ Γ eb γ γ_a γ_r ea v Hsat Hdec Heval.
  inversion Heval; subst; try app_rule_absurd.
  match goal with
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
  inversion Heval; subst; try app_rule_absurd.
  match goal with
  | [ H : decomp_coerc_arrow γ = Some _ |- _ ] => rewrite Hdec in H; discriminate
  end.
Qed.

(** Rule App-Spine keeps its own premises: no other rule can fire where it
    fires, given that the operator already has a value. *)
Lemma eval_app_spine_inv : forall Φ Γ ef ea v,
  sat Φ = true ->
  Comp Γ ef ->
  Φ ; Γ ⊢ EApp ef ea ⇓ v ->
  exists ef', Φ ; Γ ⊢ ef ⇓ ef' /\ Φ ; Γ ⊢ EApp ef' ea ⇓ v.
Proof.
  intros Φ Γ ef ea v Hsat Hcomp Heval.
  inversion Heval; subst; try app_rule_absurd.
  eexists. split; eassumption.
Qed.

Lemma eval_app_prim_inv : forall Φ Γ ef ea p args v,
  sat Φ = true ->
  unspool_app (EApp ef ea) [] = (EPrimOp p, args) ->
  Datatypes.length args = primop_arity p ->
  Φ ; Γ ⊢ EApp ef ea ⇓ v ->
  exists args', Forall2 (eval Inf Φ Γ) args args' /\ v = reduce_prim p args'.
Proof.
  intros Φ Γ ef ea p args v Hsat Hun Hlen Heval.
  inversion Heval; subst; try app_rule_absurd.
  match goal with
  | [ H : unspool_app (EApp ef ea) [] = (EPrimOp ?q, ?qargs) |- _ ] =>
      assert (Heq : (EPrimOp q, qargs) = (EPrimOp p, args)) by (rewrite <- H; exact Hun)
  end.
  injection Heq as Hp Hargs. subst.
  eexists. split; [eassumption | reflexivity].
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

  Unlimited budget only, hence the k0 = Inf premise. Rule App-Spine no
  longer fires on a primitive spine, because Comp excludes it, so the old
  overlap with Rule App-Prim at Fin 0 is gone. A finite budget still breaks
  the argument in a different step. At a finite budget a value can be
  EBot BOutOfFuel, which is not ConCore, so concore_eval_closed_fix does not
  apply. The laws fix cast_expr and reduce_prim only on ConCore input and on
  input that contains relates, and a closure over an out-of-fuel binding is
  neither. So the laws allow cast_expr to turn such a closure into a branch,
  and Rule Prune can then answer its dead arm while Rule Lit answers the
  same arm. ApplicationRules.v states this as
  bounded_concrete_determinism_fails and
  bounded_concrete_determinism_not_provable.
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
    | kv Φ Γ ef ea ef' er Hcomp Heval_f Heval_app2
    | kv Φ Γ b
    | kv Φ Γ ef ea p args args' Hunspool Harity Hargs
    | kv Φ Γ x e0
    | kv Φ Γ ef γ ea γ_a γ_r er Hdecomp Heval_pushed
    | kv Φ Γ e1 e2 ec et ef args er Hunspool_if Heval_arms
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
             (concrete_env_extend Γ' x Γ ea (concore_expr_thunk_env _ _ Hclos) Henv Hea)
             (concore_expr_lam _ _ (concore_expr_thunk _ _ Hclos))
             (eval_app_clos_inv Φ Γ Γ' x eb ea v2 Hsat H2)).
  - (* Rule App-Spine *)
    pose proof (concore_expr_app_l _ _ Hcon) as Hcf.
    pose proof (concore_expr_app_r _ _ Hcon) as Hca.
    destruct (eval_app_spine_inv Φ Γ ef ea v2 Hsat Hcomp H2)
      as [ef2 [Hef2 Happ2]].
    assert (Heqf : ef' = ef2)
      by exact (eval_det_fix Inf Φ Γ ef ef' Heval_f eq_refl ef2 Hsat Henv Hcf Hef2).
    subst ef2.
    exact (eval_det_fix Inf Φ Γ (EApp ef' ea) er Heval_app2 eq_refl v2 Hsat Henv
             (Con_App ef' ea (concore_eval_closed_fix Inf Φ Γ ef ef' Heval_f eq_refl Hsat Henv Hcf) Hca)
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
  - (* Rule App-If: a ConCore expression has no branch at its spine head *)
    exfalso.
    destruct (unspool_app_concore (EApp e1 e2) [] _ args Hunspool_if Hcon (Forall_nil _))
      as [Hhead _].
    exact (not_concore_if ec et ef Hhead).
  - (* Rule App-Bot *) symmetry. exact (eval_app_bot_inv Φ Γ b ea v2 Hsat H2).
  - (* Rule Case *)
    destruct (eval_case_inv Φ Γ es alts v2 Hsat H2) as [es2 [Hes2 Hfold2]].
    assert (Hces : concore_expr es) by exact (concore_expr_case_es es alts Hcon).
    assert (Halts : Forall concore_alt alts) by (inversion Hcon; subst; assumption).
    assert (Heq : es' = es2)
      by exact (eval_det_fix Inf Φ Γ es es' Heval_es eq_refl es2 Hsat Henv Hces Hes2).
    subst es2.
    exact (fold_alts_det_fix Inf Φ Γ (merge Γ es') alts er Hfold eq_refl v2 Hsat Henv
             (merge_concore Γ es' (concore_eval_closed_fix Inf Φ Γ es es' Heval_es eq_refl Hsat Henv Hces))
             Halts Hfold2).
  - (* Rule If: a ConCore expression is never a branch *)
    exfalso. exact (not_concore_if ec et ef Hcon).
  - (* Rule Coercion *) symmetry. exact (eval_coercion_inv Φ Γ γ v2 Hsat H2).
  - (* Rule Prune: the path condition holds *)
    exfalso. rewrite Hsat in Hunsat. discriminate.
  - (* Rule Type *) symmetry. exact (eval_type_inv Φ Γ τ v2 Hsat H2).
  - (* Rule Thunk *)
    inversion Hcon as [| | | | | | | | | | | | | Γ0 e1 Henv' He]; subst.
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

Theorem symbolic_results_share_the_instance : forall Φ Γs Γc σ S e_sym e_con v1 v2,
  σ ⊨ Φ ->
  contains_env σ S Γs Γc ->
  contains σ S e_sym e_con ->
  concore_expr e_con ->
  closed_program Γc e_con ->
  Φ ; Γs ⊢ e_sym ⇓ v1 ->
  Φ ; Γs ⊢ e_sym ⇓ v2 ->
  exists v_con,
    Γc ⊢ᶜ e_con ⇓ᶜ v_con /\ contains σ S v1 v_con /\ contains σ S v2 v_con.
Proof.
  intros Φ Γs Γc σ S e_sym e_con v1 v2 Hmod Henv Hcont Hcon Hcl H1 H2.
  destruct (concore_soundness Φ Γs Γc σ S e_sym e_con v1 Hmod Henv Hcont Hcon Hcl H1)
    as [c1 [Hc1 Hk1]].
  destruct (concore_soundness Φ Γs Γc σ S e_sym e_con v2 Hmod Henv Hcont Hcon Hcl H2)
    as [c2 [Hc2 Hk2]].
  pose proof (concore_eval_deterministic Γc e_con c1 c2
                (contains_env_concrete σ S Γs Γc Henv) Hcon Hc1 Hc2) as Hsame.
  subst c2. exists c1. repeat split; assumption.
Qed.



(** The term of Section 12.3 has exactly one value, the one Rule App-Cast
    gives it. *)
Corollary casted_application_value_unique :
  (forall Γ0 x body γ, cast_expr (EThunk Γ0 (ELam x body)) γ = EThunk Γ0 (ELam x body)) ->
  forall v, · ⊢ᶜ EApp coerced_operator plain_operand ⇓ᶜ v ->
  v = EThunk (extend_env · "x" · coerced_operand) (ELam "z" (EVar "x")).
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
  eval_app_cast_opaque_stuck shows it for every operator under the cast, and
  app_spine_concrete_operator_is_not_a_cast shows that Rule App-Spine does not
  reach the shape on the concrete side either.

  Rule App-Spine asks for a computation, and a cast is never one. A condition
  that asks whether the operator is a value would let the two sides disagree
  about whether the rule applies, because concretion can turn a computation
  into a value, as comp_not_preserved_by_concretion below shows.

  The cost: a program whose operator evaluates to a cast with a non-arrow
  coercion has no value. Such a term applies something whose coercion does not
  split, which is applying a non-function, and System FC rejects it at
  type-check time. This judgement has no typing rules, so it gets stuck rather
  than inventing an answer. scratch/OpaqueCastOperatorReachable.v holds the
  witness program.
*)
Corollary app_spine_concrete_operator_is_not_a_cast : forall σ S Γs Γc ef fc,
  contains_env σ S Γs Γc ->
  contains σ S ef fc ->
  Comp Γs ef ->
  is_cast fc = false.
Proof.
  intros σ S Γs Γc ef fc Henv Hcont Hcomp.
  destruct (comp_contains σ S Γs Γc ef fc Henv Hcont Hcomp) as [Hc | [Γ' [x [body ->]]]].
  - destruct Hc; reflexivity.
  - reflexivity.
Qed.

Lemma comp_not_preserved_by_concretion : forall σ S Γs Γc ec x l,
  models_cond σ S ec ->
  S x = false ->
  contains σ S (EThunk · (EIf ec (ELam x (ELit l)) (ELam x (ELit l))))
               (EThunk · (ELam x (ELit l)))
  /\ Comp Γs (EThunk · (EIf ec (ELam x (ELit l)) (ELam x (ELit l))))
  /\ ~ Comp Γc (EThunk · (ELam x (ELit l))).
Proof.
  intros σ S Γs Γc ec x l Hmc Hx. split; [| split].
  - apply Cont_Thunk; [apply Cont_Env_Empty |].
    apply Cont_If_True; [exact Hmc | apply Cont_Lam; [exact Hx | apply Cont_Lit]].
  - apply Comp_Thunk. reflexivity.
  - intros Hc. inversion Hc as [| | | Γ' e Hlam |]. discriminate Hlam.
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

  Lemma just_value_evaluates_to_itself : forall Γ Γ',
    pc_true ; Γ' ⊢ just_value Γ ⇓ just_value Γ.
  Proof.
    intros Γ Γ'.
    exact (Eval_Con Unlimited pc_true Γ' (just_value Γ) "Just" [EThunk Γ (ELit l)] eq_refl).
  Qed.

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
    - eapply Eval_AppSpine; [apply Comp_Lam | apply Eval_Lam |].
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
    eapply Eval_AppSpine; [apply Comp_Lam | apply Eval_Lam |].
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
(** 13. Budget-Total Terms                                                    *)
(** ========================================================================= *)

(**
  A term is budget-total when every budget from some point on gives it a
  value. The value may change with the budget.

  A term that terminates is budget-total: budget_total_of_terminating below
  proves it. A term that loops can be budget-total:
  self_app_has_value_at_every_budget in SymCore.v proves it for the
  self-application loop. A stuck term is not budget-total: it has no value at
  a positive budget. app_lit_no_value_fin below proves this for an
  application of a literal.

  Completeness is proved in Completeness.v. It takes budget_total as a
  hypothesis and assumes the cost laws of CostLaws.v.
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

Scheme contains_mut := Induction for contains Sort Prop
with contains_alt_mut := Induction for contains_alt Sort Prop
with contains_env_mut := Induction for contains_env Sort Prop.

Lemma app_lit_no_value_inf : forall Ψ Γ l a v,
  sat Ψ = true -> Ψ ; Γ ⊢ EApp (ELit l) a ⇓ v -> False.
Proof.
  intros Ψ Γ l a v Hsat Heval.
  inversion Heval; subst; app_rule_absurd.
Qed.

(** The same at a positive budget. Rule Out-Of-Fuel fires at Fin 0 only, so
    it cannot rescue the stuck application here. *)
Lemma app_lit_no_value_fin : forall k Ψ Γ l a v,
  sat Ψ = true -> eval (Fin (Datatypes.S k)) Ψ Γ (EApp (ELit l) a) v -> False.
Proof.
  intros k Ψ Γ l a v Hsat Heval.
  inversion Heval; subst; app_rule_absurd.
Qed.

Lemma eval_symvar_fin_same : forall k Ψ Γ x v,
  lookup_env Γ x = None -> sat Ψ = true ->
  eval (Fin (Datatypes.S k)) Ψ Γ (EVar x) v -> v = EVar x.
Proof.
  intros k Ψ Γ x v Hnone Hsat Heval.
  inversion Heval; subst; [congruence | reflexivity | no_con_head | congruence].
Qed.

End ConCore.

(** All laws at once, for developments that take every law as context. *)
Inductive ConCoreLaws {sorts : SymCoreSorts} {solver : SymCoreSolver} : Prop :=
  concore_laws :
    ReducePrimSolvable -> ReducePrimSaturated ->
    ReducePrimConcore -> CastExprConcore ->
    ReducePrimScoped -> CastExprScoped ->
    ModelsSat -> PrimValueAnd ->
    ReducePrimContains -> ReducePrimDenote -> ReducePrimGroundValue ->
    CastExprContains ->
    SubstCoercContainsEnv -> SubstTypeContainsEnv ->
    ConCoreLaws.

Existing Class ConCoreLaws.

#[export] Instance reduce_prim_solvable_of_laws `{laws : ConCoreLaws} : ReducePrimSolvable.
Proof. destruct laws; assumption. Qed.
#[export] Instance reduce_prim_saturated_of_laws `{laws : ConCoreLaws} : ReducePrimSaturated.
Proof. destruct laws; assumption. Qed.
#[export] Instance reduce_prim_concore_of_laws `{laws : ConCoreLaws} : ReducePrimConcore.
Proof. destruct laws; assumption. Qed.
#[export] Instance cast_expr_concore_of_laws `{laws : ConCoreLaws} : CastExprConcore.
Proof. destruct laws; assumption. Qed.
#[export] Instance reduce_prim_scoped_of_laws `{laws : ConCoreLaws} : ReducePrimScoped.
Proof. destruct laws; assumption. Qed.
#[export] Instance cast_expr_scoped_of_laws `{laws : ConCoreLaws} : CastExprScoped.
Proof. destruct laws; assumption. Qed.
#[export] Instance models_sat_of_laws `{laws : ConCoreLaws} : ModelsSat.
Proof. destruct laws; assumption. Qed.
#[export] Instance prim_value_and_of_laws `{laws : ConCoreLaws} : PrimValueAnd.
Proof. destruct laws; assumption. Qed.
#[export] Instance reduce_prim_contains_of_laws `{laws : ConCoreLaws} : ReducePrimContains.
Proof. destruct laws; assumption. Qed.
#[export] Instance reduce_prim_denote_of_laws `{laws : ConCoreLaws} : ReducePrimDenote.
Proof. destruct laws; assumption. Qed.
#[export] Instance reduce_prim_ground_value_of_laws `{laws : ConCoreLaws} : ReducePrimGroundValue.
Proof. destruct laws; assumption. Qed.
#[export] Instance cast_expr_contains_of_laws `{laws : ConCoreLaws} : CastExprContains.
Proof. destruct laws; assumption. Qed.
#[export] Instance subst_coerc_contains_env_of_laws `{laws : ConCoreLaws} : SubstCoercContainsEnv.
Proof. destruct laws; assumption. Qed.
#[export] Instance subst_type_contains_env_of_laws `{laws : ConCoreLaws} : SubstTypeContainsEnv.
Proof. destruct laws; assumption. Qed.
