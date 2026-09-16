From SymCoreTheory Require Export SymCore.Budget.
From Stdlib Require Import Strings.String Lists.List Lia Arith.PeanoNat.
Import ListNotations.

Section ConCore.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}
  {reduce_prim_solvable_law : ReducePrimSolvable}
  {reduce_prim_saturated_law : ReducePrimSaturated}.

(** ========================================================================= *)
(** Syntactic Restriction: ConCore as an Inductive Subset of SymCore          *)
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

(** ========================================================================= *)
(** Inversion Lemmas                                                          *)
(** ========================================================================= *)

Lemma not_concore_if : forall ec et ef, ~ concore_expr (EIf ec et ef).
Proof.
  intros ec et ef H.
  inversion H.
Qed.

(** ========================================================================= *)
(** Subterm Preservation Lemmas for ConCore Expressions                       *)
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
(** Closed Programs                                                           *)
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
(** Symbolic scoping: every free variable is bound or symbolic                *)
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
(** Properties of Closed Programs                                             *)
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
(** Concrete Evaluation Semantics and Preservation                            *)
(** ========================================================================= *)

Definition eval_con (Γ : environment) (e : expr) (v : expr) : Prop :=
  eval Inf pc_true Γ e v.

End ConCore.

Notation "Γ '⊢ᶜ' e '⇓ᶜ' v" := (eval_con Γ e v) (at level 70, no associativity).
Notation "'⊢ᶜ' e '⇓ᶜ' v" := (eval_con · e v) (at level 70, no associativity).
