From SymCoreTheory Require Import SymCore ConCore.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
Import ListNotations.

Section Scratch.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}
  {reduce_prim_solvable_law : ReducePrimSolvable}
  {reduce_prim_saturated_law : ReducePrimSaturated}
  {reduce_prim_scoped_law : ReducePrimScoped}
  {cast_expr_scoped_law : CastExprScoped}.

(* ==========================================================================
   The proposed restriction on concore_expr IS preserved by evaluation, and
   the proof needs no new contract on cast_expr.

   This is the half of the exercise that works. The restriction says: an
   operator that is a cast carries a coercion that splits into an arrow.
   The worry was cast_expr: it is abstract, so nothing stops it from
   returning a cast whose coercion does not split, and Rule App-Spine puts
   the operator's value back in operator position.

   The worry does not bite HERE, because the restriction is about operator
   position only. A bare cast with any coercion is still a ConCore
   expression; only an application whose operator is such a cast is not. So
   the proof carries a second predicate, concore_relaxed, that tolerates
   exactly the terms evaluation creates in flight - one application, under
   any stack of casts, whose operator is an arbitrary ConCore expression -
   and still CONCLUDES the strict predicate.

   The three hypotheses below are the three contracts ConCore.v already
   assumes about the abstract solver functions, re-stated for the stricter
   predicate. They are the same statements, not new ones; they say more only
   because the predicate they mention says more.

   What this file does NOT show: that Rule App-Cast-Opaque can be deleted.
   See OpaqueCastOperatorReachable.v, which shows this restriction does not
   pay for the deletion. The rule has since been deleted anyway, by a
   different payment: Rule App-Spine now refuses every cast operator, so the
   shape the rule covered is stuck on the symbolic and the concrete side
   alike, and it still refuses every cast operator now that it asks for a
   computation. OpaqueCastOperatorStuck.v proves that. The result below is
   unaffected - it never mentioned the rule - and the case for
   App-Cast-Opaque that used to sit in its own branch of the fixpoint is
   simply gone.
   ========================================================================== *)

Definition opaque_cast_operator (e : expr) : bool :=
  match e with
  | ECast _ γ =>
      match decomp_coerc_arrow γ with
      | Some _ => false
      | None => true
      end
  | _ => false
  end.

(* ConCore.v's concore_expr, with the operator restriction added to Con_App. *)
Inductive concore_expr : expr -> Prop :=
  | Con_Var : forall x, concore_expr (EVar x)
  | Con_Lit : forall l, concore_expr (ELit l)
  | Con_PrimOp : forall p, concore_expr (EPrimOp p)
  | Con_Con : forall d, concore_expr (ECon d)
  | Con_App : forall f a,
      concore_expr f -> concore_expr a ->
      opaque_cast_operator f = false ->
      concore_expr (EApp f a)
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

(* The terms evaluation holds in flight. Rule App-Spine puts the operator's
   value in operator position (Rel_App); Rule App-Cast rebuilds the
   application under the result coercion (Rel_Cast). Neither shape is a
   written program, and the predicate below is the smallest one that covers
   both while still concluding the strict predicate on values. *)
Inductive concore_relaxed : expr -> Prop :=
  | Rel_Exact : forall e, concore_expr e -> concore_relaxed e
  | Rel_App : forall f a, concore_expr f -> concore_expr a -> concore_relaxed (EApp f a)
  | Rel_Cast : forall e γ, concore_relaxed e -> concore_relaxed (ECast e γ).

Lemma not_concore_if : forall ec et ef, ~ concore_expr (EIf ec et ef).
Proof.
  intros ec et ef H.
  inversion H.
Qed.

Lemma relaxed_app_inv : forall f a,
  concore_relaxed (EApp f a) -> concore_expr f /\ concore_expr a.
Proof.
  intros f a H.
  inversion H as [e0 Hc | f0 a0 Hf Ha | e0 γ0 Hr]; subst.
  - split; inversion Hc; subst; assumption.
  - split; assumption.
Qed.

Lemma relaxed_cast_inv : forall e γ,
  concore_relaxed (ECast e γ) -> concore_relaxed e.
Proof.
  intros e γ H.
  inversion H as [e0 Hc | f0 a0 Hf Ha | e0 γ0 Hr]; subst.
  - apply Rel_Exact. inversion Hc; subst; assumption.
  - assumption.
Qed.

Lemma relaxed_plain : forall e,
  concore_relaxed e ->
  match e with
  | EApp _ _ => True
  | ECast _ _ => True
  | _ => concore_expr e
  end.
Proof.
  intros e H. destruct H as [e0 Hc | f a Hf Ha | e0 γ Hr].
  - destruct e0; try exact I; assumption.
  - exact I.
  - exact I.
Qed.

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

Lemma concore_con_value : forall Γ d args,
  concrete_env Γ ->
  Forall concore_expr args ->
  concore_expr (make_con_app d (map (delay Γ) args)).
Proof.
  intros Γ d args HΓ Hargs. unfold make_con_app.
  assert (Hthunks : Forall concore_expr (map (delay Γ) args)).
  { induction Hargs as [| a tl Ha Htl IH]; simpl; constructor; [| exact IH].
    destruct (is_thunk a) eqn:Ht.
    - rewrite (delay_thunk Γ a Ht). exact Ha.
    - rewrite (delay_not_thunk Γ a Ht). apply Con_Thunk; assumption. }
  assert (Hhead : concore_expr (ECon d) /\ opaque_cast_operator (ECon d) = false)
    by (split; [apply Con_Con | reflexivity]).
  revert Hhead. generalize (ECon d).
  induction Hthunks as [| a tl Ha Htl IH]; intros h [Hh Hop]; simpl; [exact Hh |].
  apply IH. split; [apply Con_App; assumption | reflexivity].
Qed.

Lemma merge_scoped_closed : forall Γ e, closed_term e -> closed_term (merge Γ e).
Proof.
  intros Γ e H.
  apply sym_scoped_no_symvars.
  assert (Hs : sym_scoped no_symvars nil e) by (apply scoped_no_symvars; exact H).
  destruct e as [ | | | | | | | | | | vc vt vf | | ]; simpl; try exact Hs.
  inversion Hs as [| | | | | | | | | | L2 vc2 vt2 vf2 Hvc Hvt Hvf | |]; subst.
  apply ite_sym_scoped; assumption.
Qed.

Section AbstractSolverContracts.

(* The contracts ConCore.v uses, read against the stricter predicate. No
   further contract is used anywhere below - in particular, nothing is
   assumed about the SHAPE of cast_expr's result.

   merge_concore is no longer one of ConCore.v's assumptions: merge is a
   definition now, so ConCore.v proves it. It is restated here as a
   hypothesis only to keep this section self-contained. *)
Hypothesis reduce_prim_concore : forall p args,
  Forall concore_expr args ->
  concore_expr (reduce_prim p args).

Hypothesis merge_concore : forall Γ e,
  concore_expr e ->
  concore_expr (merge Γ e).

Hypothesis cast_expr_concore : forall e γ,
  concore_expr e ->
  concore_expr (cast_expr e γ).

Fixpoint concore_eval_closed_fix (f0 : fuel) (Φ : path_condition) (Γ : environment) (e v : expr)
  (Heval : eval f0 Φ Γ e v) {struct Heval} :
  f0 = Inf -> sat Φ = true -> concrete_env Γ -> concore_relaxed e -> closed_program Γ e ->
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
    | k Φ Γ esp d args Hunspool_con
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
    exact (concore_eval_closed_fix Inf Φ Γ' e e' Heval_x eq_refl Hsat Henv'
             (Rel_Exact e He) (conj HΓ' Hsc')).
  - (* Eval_SymVar: impossible in a closed program *)
    exfalso. inversion Hsc; subst.
    match goal with [Hi : In x _ |- _] => exact (in_dom_lookup_env Γ x Hi Hnone) end.
  - (* Eval_Lit *) split; [constructor | apply Scoped_Lit].
  - (* Eval_Con *)
    destruct (unspool_app_scoped _ esp [] (ECon d) args Hunspool_con Hsc (Forall_nil _))
      as [_ Hsc_args].
    split; [| exact (scoped_con_value nil Γ d args HΓ Hsc_args)].
    apply concore_con_value; [exact Henv |].
    inversion Hcon as [e0 Hc | f a Hf Ha | e0 γ Hr]; subst.
    + exact (proj2 (unspool_app_concore _ [] _ _ Hunspool_con Hc (Forall_nil _))).
    + simpl in Hunspool_con.
      exact (proj2 (unspool_app_concore f [a] _ _ Hunspool_con Hf
                      (Forall_cons a Ha (Forall_nil _)))).
    + no_con_head.
  - (* Eval_Cast *)
    inversion Hsc as [| | | | | | | L1 e1 γ1 Hsce | | | | |]; subst.
    destruct (concore_eval_closed_fix Inf Φ Γ e e' Heval_e eq_refl Hsat Henv
                (relaxed_cast_inv e γ Hcon) (conj HΓ Hsce)) as [Hcv Hsv].
    split; [apply cast_expr_concore; exact Hcv | apply cast_expr_scoped_closed; exact Hsv].
  - (* Eval_AppAbs *)
    destruct (relaxed_app_inv _ _ Hcon) as [Hf Ha].
    inversion Hf as [| | | | | | | | | | | | | Γ0 e0 Henv' Hlam]; subst.
    inversion Hlam as [| | | | | x0 body Hbody | | | | | | | | ]; subst.
    inversion Hsc as [| | | | L0 f0 a0 Hscf Hsca | | | | | | | |]; subst.
    inversion Hscf as [| | | | | | | | | | | | L1 Γ1 e1 HΓ' Hsclam]; subst.
    inversion Hsclam as [| | | | | L2 x2 b2 Hscb | | | | | | |]; subst.
    apply (concore_eval_closed_fix Inf Φ (extend_env Γ' x Γ ea) eb eb' Heval_b eq_refl Hsat).
    + apply concrete_env_extend; assumption.
    + apply Rel_Exact; assumption.
    + split; [apply Scoped_Env_Extend; assumption | exact Hscb].
  - (* Eval_AppSpine: the operator's value goes back in operator position,
       and nothing is known about its shape. Rel_App is what absorbs that. *)
    destruct (relaxed_app_inv _ _ Hcon) as [Hf Ha].
    inversion Hsc as [| | | | L0 f0 a0 Hscf Hsca | | | | | | | |]; subst.
    destruct (concore_eval_closed_fix Inf Φ Γ ef ef' Heval_f eq_refl Hsat Henv
                (Rel_Exact ef Hf) (conj HΓ Hscf)) as [Hcf' Hsf'].
    apply (concore_eval_closed_fix Inf Φ Γ (EApp ef' ea) er Heval_app2 eq_refl Hsat Henv).
    + apply Rel_App; [exact Hcf' | exact Ha].
    + split; [exact HΓ | apply Scoped_App; [apply closed_term_scoped; exact Hsf' | exact Hsca]].
  - (* Eval_Bot *)
    split; [exact (relaxed_plain (EBot b) Hcon) | apply Scoped_Bot].
  - (* Eval_AppPrim *)
    destruct (relaxed_app_inv _ _ Hcon) as [Hf Ha].
    assert (Hcon_args : Forall concore_expr args).
    { simpl in Hunspool.
      destruct (unspool_app_concore ef [ea] (EPrimOp p) args Hunspool Hf
                 (Forall_cons ea Ha (Forall_nil _))) as [_ Hforall]. exact Hforall. }
    assert (Hsc_args : Forall (scoped (dom_env Γ)) args).
    { destruct (unspool_app_scoped _ (EApp ef ea) [] (EPrimOp p) args Hunspool Hsc
                 (Forall_nil _)) as [_ Hforall]. exact Hforall. }
    assert (Hres : Forall concore_expr args' /\ Forall closed_term args').
    { clear Hunspool Harity Hcon Hf Ha.
      revert Hcon_args Hsc_args.
      induction Hargs as [| a a' args_tl args'_tl Ha0 Hargs_tl IH]; intros Hcon_args Hsc_args.
      - split; constructor.
      - inversion Hcon_args as [| a0 tl0 Hcon_a Hcon_tl]; subst.
        inversion Hsc_args as [| a1 tl1 Hsc_a Hsc_tl]; subst.
        destruct (concore_eval_closed_fix Inf Φ Γ a a' Ha0 eq_refl Hsat Henv
                    (Rel_Exact a Hcon_a) (conj HΓ Hsc_a)) as [Hca Hsa].
        destruct (IH Hcon_tl Hsc_tl) as [Hct Hst].
        split; constructor; assumption. }
    destruct Hres as [Hcon' Hsc'].
    split; [apply reduce_prim_concore; exact Hcon' | apply reduce_prim_scoped_closed; exact Hsc'].
  - (* Eval_Lam *)
    inversion Hsc as [| | | | | L2 x2 b2 Hscb | | | | | | |]; subst.
    split; [apply Con_Thunk; [assumption | exact (relaxed_plain (ELam x e) Hcon)]
           | apply Scoped_Thunk; [exact HΓ | apply Scoped_Lam; exact Hscb]].
  - (* Eval_AppCast: the pushed term is an application under a cast, and its
       operator is whatever was under the arrow cast. Rel_Cast of Rel_App. *)
    destruct (relaxed_app_inv _ _ Hcon) as [Hf Ha].
    inversion Hf as [| | | | | | | e0 γ0 He | | | | | | ]; subst.
    inversion Hsc as [| | | | L0 f0 a0 Hscf Hsca | | | | | | | |]; subst.
    inversion Hscf as [| | | | | | | L1 e1 γ1 Hsce | | | | |]; subst.
    apply (concore_eval_closed_fix Inf Φ Γ (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r)
             er Heval_pushed eq_refl Hsat Henv).
    + apply Rel_Cast. apply Rel_App; [exact He | apply Con_Cast; exact Ha].
    + split; [exact HΓ |].
      apply Scoped_Cast. apply Scoped_App; [assumption | apply Scoped_Cast; assumption].
  - (* Eval_AppIf: a ConCore spine has no branch at its head *)
    exfalso.
    destruct (relaxed_app_inv _ _ Hcon) as [Hf Ha].
    simpl in Hunspool_if.
    destruct (unspool_app_concore e1 [e2] _ args Hunspool_if Hf
                (Forall_cons e2 Ha (Forall_nil _))) as [Hhead _].
    exact (not_concore_if ec et ef Hhead).
  - (* Eval_AppBot *)
    destruct (relaxed_app_inv _ _ Hcon) as [Hf Ha].
    inversion Hsc as [| | | | L0 f0 a0 Hscf Hsca | | | | | | | |]; subst.
    split; [exact Hf | apply Scoped_Bot].
  - (* Eval_Case *)
    pose proof (relaxed_plain (ECase es alts) Hcon) as Hc.
    inversion Hc as [| | | | | | es0 alts0 Hcon_es Hcon_alts | | | | | | | ]; subst.
    inversion Hsc as [| | | | | | L0 es1 alts1 Hsc_es Hsc_alts | | | | | |]; subst.
    destruct (concore_eval_closed_fix Inf Φ Γ es es' Heval_es eq_refl Hsat Henv
                (Rel_Exact es Hcon_es) (conj HΓ Hsc_es)) as [Hcon_es' Hsc_es'].
    apply (concore_fold_closed_fix Inf Φ Γ (merge Γ es') alts er Hfold eq_refl Hsat Henv);
      [apply merge_concore; exact Hcon_es' | exact Hcon_alts | exact HΓ | | exact Hsc_alts].
    exact (merge_scoped_closed Γ es' Hsc_es').
  - (* Eval_If *)
    exfalso. apply (not_concore_if ec et ef).
    exact (relaxed_plain (EIf ec et ef) Hcon).
  - (* Eval_Coercion *) split; [constructor | apply Scoped_Coercion].
  - (* Eval_Prune *) split; [constructor | apply Scoped_Bot].
  - (* Eval_Type *) split; [constructor | apply Scoped_Type].
  - (* Eval_Thunk *)
    pose proof (relaxed_plain (EThunk Γ' e) Hcon) as Hc.
    inversion Hc as [| | | | | | | | | | | | | Γ0 e0 Henv' He]; subst.
    inversion Hsc as [| | | | | | | | | | | | L1 Γ1 e1 HΓ' Hsce]; subst.
    exact (concore_eval_closed_fix Inf Φ Γ' e e' Heval_t eq_refl Hsat Henv'
             (Rel_Exact e He) (conj HΓ' Hsce)).
  - (* Eval_OutOfFuel: the budget gives up with EBot BOutOfFuel, which no
       ConCore expression is, so the statement is about the unlimited budget *)
    discriminate Hk0.
}
{
  destruct Hfold as
    [ k Φ Γ ec et ef alts et' ef' pc_c Hpc Hfold_t Hfold_f
    | k Φ Γ ec et ef alts Hpc_none
    | k Φ Γ e d ea xs ep alts er Hdec Halt Heval_ep
    | k Φ Γ b alts
    | k Φ Γ e pc alts r Hpc Hvar Hrec
    | k Φ Γ e pc alts r1 r2 Hpc Hvar Har Hf1 Hf2
    | k Φ Γ e alts Hpcnone Hop Hnotif Hnoalt Hnotbot
    ]; intros Hk0 Hsat Henv Hcon Halts HΓ Hsc Hsc_alts; subst k.
  - exfalso. apply (not_concore_if ec et ef). assumption.
  - exfalso. apply (not_concore_if ec et ef). assumption.
  - (* FoldAlts_Con *)
    assert (Hea : Forall concore_expr ea).
    { apply decompose_con_app_concore with (e := e) (d := d); assumption. }
    assert (Hep : concore_expr ep).
    { apply find_alt_concore with (d := d) (alts := alts) (xs := xs); assumption. }
    assert (Hsc_ea : Forall closed_term ea).
    { exact (proj2 (unspool_app_scoped nil e [] (ECon d) ea
                      (decompose_con_app_unspool e d ea Hdec) Hsc (Forall_nil _))). }
    apply (concore_eval_closed_fix Inf Φ (extend_env_multi Γ xs ea Γ) ep er Heval_ep eq_refl Hsat).
    + apply concrete_env_extend_multi; assumption.
    + apply Rel_Exact; assumption.
    + split.
      * apply scoped_env_extend_multi; [exact HΓ | exact HΓ |].
        eapply Forall_impl; [| exact Hsc_ea]. intros a Ha. exact (closed_term_scoped _ a Ha).
      * rewrite dom_env_extend_multi. exact (find_alt_scoped _ d alts xs ep Hsc_alts Halt).
  - (* FoldAlts_Bot *) split; [exact Hcon | apply Scoped_Bot].
  - (* FoldAlts_GroundFormula *)
    exact (concore_fold_closed_fix Inf Φ Γ (ECon (truth_constructor (pc_closed_value pc))) alts r
             Hrec eq_refl Hsat Henv (Con_Con _) Halts HΓ (Scoped_Con nil _) Hsc_alts).
  - (* FoldAlts_SymbolicFormula: a closed scrutinee's formula has no variable,
       so this rule never fires on a concrete run *)
    exfalso.
    pose proof (expr_to_pc_scoped_no_var Γ e pc (closed_term_scoped (dom_env Γ) e Hsc) Hpc) as Hnv.
    rewrite Hnv in Hvar. discriminate.
  - (* FoldAlts_Otherwise *) split; [constructor | apply Scoped_Bot].
}
Qed.

(* Preservation in the shape ConCore.v states it: a ConCore program under
   the stricter predicate evaluates to a value under the stricter
   predicate. *)
Lemma concore_eval_closed : forall Γ e v,
  concrete_env Γ ->
  concore_expr e ->
  closed_program Γ e ->
  pc_true ; Γ ⊢ e ⇓ v ->
  concore_expr v.
Proof.
  intros Γ e v Henv Hcon Hcl Heval.
  exact (proj1 (concore_eval_closed_fix Inf pc_true Γ e v Heval eq_refl sat_pc_true Henv
                  (Rel_Exact e Hcon) Hcl)).
Qed.

(* And the restriction means what it was meant to mean. *)
Lemma concore_app_cast_operator_is_an_arrow : forall eb γ a,
  concore_expr (EApp (ECast eb γ) a) ->
  exists γ_a γ_r, decomp_coerc_arrow γ = Some (γ_a, γ_r).
Proof.
  intros eb γ a H.
  inversion H as [| | | | f a0 Hf Ha Hop | | | | | | | | | ]; subst.
  simpl in Hop.
  destruct (decomp_coerc_arrow γ) as [[γ_a γ_r] |] eqn:Hd.
  - exists γ_a, γ_r. reflexivity.
  - discriminate.
Qed.

End AbstractSolverContracts.

(* ==========================================================================
   A note on the syntactic test

   decomp_coerc_arrow tests for TyArrow on both sides of the coercion. The
   justification for the restriction is a typing one: if (e |> γ) a is well
   typed in System FC then e |> γ has a function type, so the target of γ is
   a function type, and by consistency so is its source.

   "Has a function type" and "is syntactically a TyArrow" are the same thing
   here only because SymCore's type syntax is TyVar | TyCon | TyArrow |
   TyApp with no type families and no type synonyms: nothing but TyArrow can
   denote a function type, and a TyApp head is a TyCon or a TyVar, neither
   of which reduces. Add type families, and a TyApp could stand for a
   function type while failing this test, and a well typed program would be
   rejected. As the syntax stands, it cannot.
   ========================================================================== *)

End Scratch.
