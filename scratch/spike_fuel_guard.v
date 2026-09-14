(* SPIKE (throwaway): does the guard checker accept the mutually recursive
   fixpoints over eval/fold_alts once the relation is indexed by fuel and the
   recursive premises sit at (dec f)?

   Part A: the truly fuel-polymorphic version of the smallest pair, with NO
   "k0 = Inf" crutch, so the out-of-fuel case is a real case.
   Part B: the out-of-fuel rule is reachable, and Inf is not.
   Part C: a deliberately non-structural variant, to prove the guard checker
   is actually running here. *)
Require Import SymCoreTheory.SymCore.
Require Import SymCoreTheory.ConCore.
Require Import Coq.Lists.List.
Import ListNotations.

(** Part A *)
Fixpoint poly_eval_closed (k0 : fuel) (Φ : path_condition) (Γ : environment) (e v : expr)
  (Heval : eval k0 Φ Γ e v) {struct Heval} :
  sat Φ = true -> concrete_env Γ -> concore_expr e -> concore_expr v
with poly_fold_closed (k0 : fuel) (Φ : path_condition) (Γ : environment) (e : expr)
  (alts : list alt) (er : expr)
  (Hfold : fold_alts k0 Φ Γ e alts er) {struct Hfold} :
  sat Φ = true -> concrete_env Γ -> concore_expr e -> Forall concore_alt alts -> concore_expr er.
Proof.
{
  destruct Heval as
    [ k Φ Γ x Γ' e e' Hlook Heval_x
    | k Φ Γ x Hnone
    | k Φ Γ l
    | k Φ Γ d
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
    | Φ Γ e
    ]; intros Hsat Henv Hcon.
  - (* Eval_Var *)
    destruct (lookup_env_concrete Γ x Γ' e Henv Hlook) as [Henv' He].
    exact (poly_eval_closed (dec k) Φ Γ' e e' Heval_x Hsat Henv' He).
  - (* Eval_SymVar *) exact Hcon.
  - (* Eval_Lit *) constructor.
  - (* Eval_Con *) constructor.
  - (* Eval_Cast *)
    apply cast_expr_concore.
    apply (poly_eval_closed (dec k) Φ Γ e e' Heval_e Hsat Henv).
    inversion Hcon; subst; assumption.
  - (* Eval_AppAbs *)
    inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | ]; subst.
    inversion Hf as [| | | | | | Γ0 x0 body Henv' Hbody | | | | | | | ]; subst.
    apply (poly_eval_closed (dec k) Φ (extend_env Γ' x Γ ea) eb eb' Heval_b Hsat).
    + apply concrete_env_extend; assumption.
    + assumption.
  - (* Eval_AppSpine *)
    inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | ]; subst.
    apply (poly_eval_closed (dec k) Φ Γ (EApp ef' ea) er Heval_app2 Hsat Henv).
    apply Con_App; [| assumption].
    exact (poly_eval_closed (dec k) Φ Γ ef ef' Heval_f Hsat Henv Hf).
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
      * exact (poly_eval_closed (dec k) Φ Γ a a' Ha Hsat Henv Hcon_a).
      * exact (IH Hcon_tl).
  - (* Eval_Lam *)
    constructor; [assumption |].
    inversion Hcon; subst; assumption.
  - (* Eval_AppCast *)
    inversion Hcon as [| | | | f a Hf Ha | | | | | | | | | ]; subst.
    inversion Hf as [| | | | | | | | e γ0 He | | | | | ]; subst.
    apply (poly_eval_closed (dec k) Φ Γ (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r)
             er Heval_pushed Hsat Henv).
    apply Con_Cast. apply Con_App; [assumption | apply Con_Cast; assumption].
  - (* Eval_AppBot *)
    inversion Hcon; subst. assumption.
  - (* Eval_Case *)
    inversion Hcon as [| | | | | | | es0 alts0 Hcon_es Hcon_alts | | | | | | ]; subst.
    apply (poly_fold_closed (dec k) Φ Γ (merge es') alts er Hfold Hsat Henv);
      [| assumption].
    apply merge_concore.
    exact (poly_eval_closed (dec k) Φ Γ es es' Heval_es Hsat Henv Hcon_es).
  - (* Eval_If *)
    exfalso. apply (not_concore_if ec et ef). assumption.
  - (* Eval_Coercion *) constructor.
  - (* Eval_Prune *) constructor.
  - (* Eval_Type *) constructor.
  - (* Eval_OutOfFuel *) constructor.
}
{
  destruct Hfold as
    [ k Φ Γ ec et ef alts et' ef' pc_c Hpc Hfold_t Hfold_f
    | k Φ Γ ec et ef alts Hpc_none
    | k Φ Γ e d ea xs ep alts er Hdec Halt Heval_ep
    | k Φ Γ b alts
    | k Φ Γ e alts Hnotif Hnoalt Hnotbot
    ]; intros Hsat Henv Hcon Halts.
  - exfalso. apply (not_concore_if ec et ef). assumption.
  - exfalso. apply (not_concore_if ec et ef). assumption.
  - (* FoldAlts_Con *)
    assert (Hea : Forall concore_expr ea).
    { apply decompose_con_app_concore with (e := e) (d := d); assumption. }
    assert (Hep : concore_expr ep).
    { apply find_alt_concore with (d := d) (alts := alts) (xs := xs); assumption. }
    apply (poly_eval_closed (dec k) Φ (extend_env_multi Γ xs ea Γ) ep er Heval_ep Hsat);
      [| assumption].
    apply concrete_env_extend_multi; assumption.
  - (* FoldAlts_Bot *) exact Hcon.
  - (* FoldAlts_Otherwise *) constructor.
}
Qed.

(** Part B: Fin 0 really does carry an out-of-fuel derivation, and Inf does not
    admit one, so "eval Inf" is the old relation unchanged. *)
Example out_of_fuel_reachable : forall l,
  eval (Fin 0) pc_true · (ELit l) (EBot BUndefined).
Proof. intros l. apply Eval_OutOfFuel. Qed.

Example dec_Inf_is_Inf : dec Inf = Inf.
Proof. reflexivity. Qed.

Example inf_prunes_out_of_fuel : forall Γ l v,
  eval Inf pc_true Γ (ELit l) v -> v = ELit l.
Proof.
  intros Γ l v H.
  (* one goal from Eval_Lit and one from Eval_Prune; the out-of-fuel case is
     dropped by inversion because Fin 0 cannot unify with Inf *)
  inversion H; subst.
  - reflexivity.
  - rewrite sat_pc_true in H0. discriminate.
Qed.

(** Part C: control.  The same shape, but recursing on a NON-subterm, is
    rejected - so the acceptances above are real guard-checker acceptances. *)
Fail Fixpoint guard_control (k0 : fuel) (Φ : path_condition) (Γ : environment)
  (e v : expr) (Heval : eval k0 Φ Γ e v) {struct Heval} :
  sat Φ = true -> concrete_env Γ -> concore_expr e -> concore_expr v :=
  fun Hsat Henv Hcon => guard_control k0 Φ Γ e v Heval Hsat Henv Hcon.

Print Assumptions poly_eval_closed.
