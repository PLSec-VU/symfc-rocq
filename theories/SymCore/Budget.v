From SymCoreTheory Require Export SymCore.Inversion.
From Stdlib Require Import Strings.String Lists.List ZArith.ZArith Bool.Bool Arith.PeanoNat Lia.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Section SymCore.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.
Context {reduce_prim_solvable_law : ReducePrimSolvable}.
Context {reduce_prim_saturated_law : ReducePrimSaturated}.
(** ------------------------------------------------------------------------- *)
(** The Unlimited Budget against a Finite Budget (§3.2)                       *)
(** ------------------------------------------------------------------------- *)

(**
  This file carries two judgements: eval Inf, the unlimited budget, and
  eval (Fin n), a bound of n levels of rules. This section says how the two
  relate, and closes with what the bound rules out.

  The bridge, first. Every derivation at the unlimited budget is reproduced
  at some finite budget. The budget that works is the height of the
  derivation: every rule of eval needs a live fuel for itself, its premises
  run one level lower, and fold_alts spends nothing.

  The proof below carries more than the bridge asks for. It produces a
  threshold h and shows that EVERY budget at or above h reproduces the
  derivation. The weaker form, "some budget works", does not survive the
  induction. Rule App-Spine has two recursive premises, and the budgets they
  report back need not be equal. Only an upward-closed statement lets the
  rule keep the larger of the two. Rule App-Prim asks for the same thing over
  a whole list: its Forall2 must run all its arguments at one budget. The
  inner induction on the Forall2 folds the argument thresholds together with
  max as it walks the list, so no separate list-maximum lemma is needed.

  The proof is a pair of mutually recursive fixpoints on the derivation, for
  the same reason as concore_eval_closed_fix in ConCore/Preservation.v: the derived mutual
  induction scheme supplies no hypothesis under the Forall2 of Rule App-Prim.

  The fuel comes in as f0 with an f0 = Inf premise instead of being left
  free, because destruct on the index brings Rule Out-Of-Fuel back as a case.
  The premise is what discharges it.
*)
Fixpoint eval_fin_of_inf_fix (f0 : fuel) (Φ : path_condition) (Γ : environment) (e v : expr)
  (Heval : eval f0 Φ Γ e v) {struct Heval} :
  f0 = Inf -> exists h, forall n, (h <= n)%nat -> eval (Fin n) Φ Γ e v
with fold_alts_fin_of_inf_fix (f0 : fuel) (Φ : path_condition) (Γ : environment) (e : expr)
  (alts : list alt) (er : expr)
  (Hfold : fold_alts f0 Φ Γ e alts er) {struct Hfold} :
  f0 = Inf -> exists h, forall n, (h <= n)%nat -> fold_alts (Fin n) Φ Γ e alts er.
Proof.
{
  destruct Heval as
    [ k Φ Γ x Γ' e e' Hlook Heval_x
    | k Φ Γ x Hnone
    | k Φ Γ l
    | k Φ Γ e d args Hunspool
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
    ]; intros Hk0; try (injection Hk0 as Hk0; subst k).
  - (* Eval_Var *)
    destruct (eval_fin_of_inf_fix Inf Φ Γ' e e' Heval_x eq_refl) as [h Hh].
    exists (S h). intros n Hn. destruct n as [| m]; [lia |].
    eapply Eval_Var; [exact Hlook |]. simpl. apply Hh. lia.
  - (* Eval_SymVar *)
    exists 1%nat. intros n Hn. destruct n as [| m]; [lia |]. apply Eval_SymVar. exact Hnone.
  - (* Eval_Lit *)
    exists 1%nat. intros n Hn. destruct n as [| m]; [lia |]. apply Eval_Lit.
  - (* Eval_Con *)
    exists 1%nat. intros n Hn. destruct n as [| m]; [lia |]. eapply Eval_Con. exact Hunspool.
  - (* Eval_Cast *)
    destruct (eval_fin_of_inf_fix Inf Φ Γ e e' Heval_e eq_refl) as [h Hh].
    exists (S h). intros n Hn. destruct n as [| m]; [lia |].
    apply Eval_Cast. simpl. apply Hh. lia.
  - (* Eval_AppAbs *)
    destruct (eval_fin_of_inf_fix Inf Φ (extend_env Γ' x Γ ea) eb eb' Heval_b eq_refl)
      as [h Hh].
    exists (S h). intros n Hn. destruct n as [| m]; [lia |].
    apply Eval_AppAbs. simpl. apply Hh. lia.
  - (* Eval_AppSpine *)
    destruct (eval_fin_of_inf_fix Inf Φ Γ ef ef' Heval_f eq_refl) as [h1 Hh1].
    destruct (eval_fin_of_inf_fix Inf Φ Γ (EApp ef' ea) er Heval_app2 eq_refl) as [h2 Hh2].
    exists (S (Nat.max h1 h2)). intros n Hn. destruct n as [| m]; [lia |].
    eapply Eval_AppSpine.
    + exact Hcomp.
    + simpl. apply Hh1. lia.
    + simpl. apply Hh2. lia.
  - (* Eval_Bot *)
    exists 1%nat. intros n Hn. destruct n as [| m]; [lia |]. apply Eval_Bot.
  - (* Eval_AppPrim *)
    assert (Hbound : exists h, forall n, (h <= n)%nat -> Forall2 (eval (Fin n) Φ Γ) args args').
    { clear Hunspool Harity.
      induction Hargs as [| a a' tl tl' Ha Htl IH].
      - exists 0%nat. intros n _. constructor.
      - destruct IH as [h2 Hh2].
        destruct (eval_fin_of_inf_fix Inf Φ Γ a a' Ha eq_refl) as [h1 Hh1].
        exists (Nat.max h1 h2). intros n Hn. constructor.
        + apply Hh1. lia.
        + apply Hh2. lia. }
    destruct Hbound as [h Hh].
    exists (S h). intros n Hn. destruct n as [| m]; [lia |].
    eapply Eval_AppPrim; [exact Hunspool | exact Harity |]. simpl. apply Hh. lia.
  - (* Eval_Lam *)
    exists 1%nat. intros n Hn. destruct n as [| m]; [lia |]. apply Eval_Lam.
  - (* Eval_AppCast *)
    destruct (eval_fin_of_inf_fix Inf Φ Γ
                (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r) er Heval_pushed eq_refl)
      as [h Hh].
    exists (S h). intros n Hn. destruct n as [| m]; [lia |].
    eapply Eval_AppCast; [exact Hdecomp |]. simpl. apply Hh. lia.
  - (* Eval_AppIf *)
    destruct (eval_fin_of_inf_fix Inf Φ Γ
                (EIf ec (fold_left EApp args et) (fold_left EApp args ef)) er Heval_arms eq_refl)
      as [h Hh].
    exists (S h). intros n Hn. destruct n as [| m]; [lia |].
    eapply Eval_AppIf; [exact Hunspool_if |]. simpl. apply Hh. lia.
  - (* Eval_AppBot *)
    exists 1%nat. intros n Hn. destruct n as [| m]; [lia |]. apply Eval_AppBot.
  - (* Eval_Case *)
    destruct (eval_fin_of_inf_fix Inf Φ Γ es es' Heval_es eq_refl) as [h1 Hh1].
    destruct (fold_alts_fin_of_inf_fix Inf Φ Γ (merge Γ es') alts er Hfold eq_refl) as [h2 Hh2].
    exists (S (Nat.max h1 h2)). intros n Hn. destruct n as [| m]; [lia |].
    eapply Eval_Case.
    + simpl. apply Hh1. lia.
    + simpl. apply Hh2. lia.
  - (* Eval_If *)
    destruct (eval_fin_of_inf_fix Inf Φ Γ ec ec' Heval_c eq_refl) as [h1 Hh1].
    destruct (eval_fin_of_inf_fix Inf (Φ ∧ pc_c) Γ et et' Heval_t eq_refl) as [h2 Hh2].
    destruct (eval_fin_of_inf_fix Inf (Φ ∧ ¬ pc_c) Γ ef ef' Heval_f eq_refl) as [h3 Hh3].
    exists (S (Nat.max h1 (Nat.max h2 h3))). intros n Hn. destruct n as [| m]; [lia |].
    eapply Eval_If.
    + simpl. apply Hh1. lia.
    + exact Hpc.
    + simpl. apply Hh2. lia.
    + simpl. apply Hh3. lia.
  - (* Eval_Coercion *)
    exists 1%nat. intros n Hn. destruct n as [| m]; [lia |]. apply Eval_Coercion.
  - (* Eval_Prune *)
    exists 1%nat. intros n Hn. destruct n as [| m]; [lia |]. apply Eval_Prune. exact Hunsat.
  - (* Eval_Type *)
    exists 1%nat. intros n Hn. destruct n as [| m]; [lia |]. apply Eval_Type.
  - (* Eval_Thunk *)
    destruct (eval_fin_of_inf_fix Inf Φ Γ' e e' Heval_t eq_refl) as [h Hh].
    exists (S h). intros n Hn. destruct n as [| m]; [lia |].
    apply Eval_Thunk. simpl. apply Hh. lia.
  - (* Eval_OutOfFuel *)
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
    ]; intros Hk0; subst k.
  - (* FoldAlts_If *)
    destruct (fold_alts_fin_of_inf_fix Inf (Φ ∧ pc_c) Γ et alts et' Hfold_t eq_refl)
      as [h1 Hh1].
    destruct (fold_alts_fin_of_inf_fix Inf (Φ ∧ ¬ pc_c) Γ ef alts ef' Hfold_f eq_refl)
      as [h2 Hh2].
    exists (Nat.max h1 h2). intros n Hn.
    eapply FoldAlts_If.
    + exact Hpc.
    + simpl. apply Hh1. lia.
    + simpl. apply Hh2. lia.
  - (* FoldAlts_IfFail *)
    exists 0%nat. intros n _. apply FoldAlts_IfFail. exact Hpc_none.
  - (* FoldAlts_Con *)
    destruct (eval_fin_of_inf_fix Inf Φ (extend_env_multi Γ xs ea Γ) ep er Heval_ep eq_refl)
      as [h Hh].
    exists h. intros n Hn.
    eapply FoldAlts_Con; [exact Hdec | exact Halt |]. simpl. apply Hh. lia.
  - (* FoldAlts_Bot *)
    exists 0%nat. intros n _. apply FoldAlts_Bot.
  - (* FoldAlts_GroundFormula *)
    destruct (fold_alts_fin_of_inf_fix Inf Φ Γ
                (ECon (truth_constructor (pc_closed_value pc))) alts r Hrec eq_refl) as [h Hh].
    exists h. intros n Hn.
    eapply FoldAlts_GroundFormula; [exact Hpc | exact Hvar | apply Hh; lia].
  - (* FoldAlts_SymbolicFormula *)
    destruct (fold_alts_fin_of_inf_fix Inf (Φ ∧ pc) Γ (ECon dcon_true) alts r1 Hf1 eq_refl)
      as [h1 Hh1].
    destruct (fold_alts_fin_of_inf_fix Inf (Φ ∧ ¬ pc) Γ (ECon dcon_false) alts r2 Hf2 eq_refl)
      as [h2 Hh2].
    exists (Nat.max h1 h2). intros n Hn.
    eapply FoldAlts_SymbolicFormula;
      [exact Hpc | exact Hvar | exact Har | apply Hh1; lia | apply Hh2; lia].
  - (* FoldAlts_Otherwise *)
    exists 0%nat. intros n _. apply FoldAlts_Otherwise; assumption.
}
Qed.

(** An unbounded derivation has a budget from which on every budget works. *)
Lemma eval_inf_has_budget : forall Φ Γ e v,
  Φ ; Γ ⊢ e ⇓ v ->
  exists h, forall n, (h <= n)%nat -> eval (Fin n) Φ Γ e v.
Proof.
  intros Φ Γ e v Heval. exact (eval_fin_of_inf_fix Inf Φ Γ e v Heval eq_refl).
Qed.

End SymCore.
