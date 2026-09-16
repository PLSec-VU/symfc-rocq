From SymCoreTheory Require Export ConCore.Programs.
From Stdlib Require Import Strings.String Lists.List Lia Arith.PeanoNat.
Import ListNotations.

Section ConCore.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}
  {reduce_prim_solvable_law : ReducePrimSolvable}
  {reduce_prim_saturated_law : ReducePrimSaturated}.

(** ------------------------------------------------------------------------- *)
(** SMT & Grisette Solver Behaviors for Concrete Evaluation                   *)
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

Class ReducePrimKeepsOutOfFuel : Prop :=
reduce_prim_keeps_out_of_fuel : forall p args,
  length args = primop_arity p ->
  existsb mentions_out_of_fuel args = true ->
  mentions_out_of_fuel (reduce_prim p args) = true.

Class CastExprKeepsOutOfFuel : Prop :=
cast_expr_keeps_out_of_fuel : forall e γ,
  mentions_out_of_fuel e = true ->
  mentions_out_of_fuel (cast_expr e γ) = true.

Context {reduce_prim_keeps_out_of_fuel_law : ReducePrimKeepsOutOfFuel}
  {cast_expr_keeps_out_of_fuel_law : CastExprKeepsOutOfFuel}.

(** ------------------------------------------------------------------------- *)
(** Inversion and Preservation Helpers                                        *)
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
(** ConCore Closure under Evaluation (Syntactic Stability)                    *)
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
(** Symbolic scoping is preserved by evaluation                               *)
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

Definition closed_instance (Γ : environment) (e : expr) : Prop :=
  closed_program Γ e \/ (is_thunk e = true /\ closed_term e).

Lemma closed_instance_program : forall Γ e,
  closed_instance Γ e -> is_thunk e = false -> closed_program Γ e.
Proof. intros Γ e [H | [H _]] Ht; [exact H | congruence]. Qed.

End ConCore.
