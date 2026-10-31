From SymCoreTheory Require Export SymCore.Inversion.
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
Import ListNotations.

Section SymCore.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.

Definition from_some_budget (R : fuel -> Prop) : Prop :=
  exists h, forall n, h <= n -> R (Fin n).

Definition budget_eval f Φ Γ e v : Prop :=
  f = Inf -> from_some_budget (fun g => eval g Φ Γ e v).
Definition budget_apply g Φ Γ vf e v : Prop :=
  g = Inf -> from_some_budget (fun g' => apply g' Φ Γ vf e v).
Definition budget_prim g Φ op ts v : Prop :=
  g = Inf -> from_some_budget (fun g' => prim_app g' Φ op ts v).
Definition budget_force g Φ t v : Prop :=
  g = Inf -> from_some_budget (fun g' => force g' Φ t v).
Definition budget_select g Φ c tthen telse v : Prop :=
  g = Inf -> from_some_budget (fun g' => select g' Φ c tthen telse v).
Definition budget_fold g Φ Γ vs alts v : Prop :=
  g = Inf -> from_some_budget (fun g' => fold_alts g' Φ Γ vs alts v).

Lemma forces_have_budget : forall Φ ts vs,
  Forall2 (budget_force Inf Φ) ts vs ->
  from_some_budget (fun g => Forall2 (force g Φ) ts vs).
Proof.
  intros Φ ts vs Hall. induction Hall as [| t v ts' vs' Ht _ [h2 Hh2]].
  - exists 0. intros n _. constructor.
  - destruct (Ht eq_refl) as [h1 Hh1].
    exists (Nat.max h1 h2). intros n Hn. constructor.
    + apply Hh1. lia.
    + apply Hh2. lia.
Qed.

Ltac enter_budget_case :=
  unfold budget_eval, budget_apply, budget_prim, budget_force, budget_select, budget_fold;
  intros;
  match goal with
  | Hfuel : Spent = Inf |- _ => discriminate Hfuel
  | Hfuel : Live _ = Inf |- _ => injection Hfuel as ->
  | Hfuel : ?g = Inf |- _ => subst g
  end;
  simpl dec in *;
  repeat match goal with
  | IH : Inf = Inf -> from_some_budget _ |- _ => destruct (IH eq_refl) as [?h ?Hh]; clear IH
  end;
  unfold from_some_budget in *.

Ltac lift_premise :=
  match goal with
  | Hh : forall n, _ <= n -> _ |- _ => apply Hh; lia
  end.

Ltac budget_leaf rule :=
  first
    [ exists 1; intros [| n] Hn; [lia |]; eapply rule; eassumption
    | exists 0; intros n _; eapply rule; eassumption ].

Lemma inf_has_budget_mutual :
  (forall f Φ Γ e v, eval f Φ Γ e v -> budget_eval f Φ Γ e v) /\
  (forall g Φ Γ vf e v, apply g Φ Γ vf e v -> budget_apply g Φ Γ vf e v) /\
  (forall g Φ op ts v, prim_app g Φ op ts v -> budget_prim g Φ op ts v) /\
  (forall g Φ t v, force g Φ t v -> budget_force g Φ t v) /\
  (forall g Φ c tthen telse v, select g Φ c tthen telse v -> budget_select g Φ c tthen telse v) /\
  (forall g Φ Γ vs alts v, fold_alts g Φ Γ vs alts v -> budget_fold g Φ Γ vs alts v).
Proof.
  apply (eval_mut_ind budget_eval budget_apply budget_prim budget_force budget_select
    budget_fold).
  - enter_budget_case.
    exists (S h). intros [| n] Hn; [lia |]. eapply Eval_Var; [eassumption | lift_premise].
  - enter_budget_case. budget_leaf Eval_Lit.
  - enter_budget_case. budget_leaf Eval_Sym.
  - enter_budget_case. budget_leaf Eval_Con.
  - enter_budget_case.
    exists (S h). intros [| n] Hn; [lia |]. eapply Eval_Prim. lift_premise.
  - enter_budget_case.
    exists (S (h + h0)). intros [| n] Hn; [lia |]. eapply Eval_App; lift_premise.
  - enter_budget_case. budget_leaf Eval_Lam.
  - enter_budget_case.
    exists (S h). intros [| n] Hn; [lia |]. eapply Eval_Cast. lift_premise.
  - enter_budget_case. budget_leaf Eval_Bot.
  - enter_budget_case.
    exists (S (h + h0)). intros [| n] Hn; [lia |]. eapply Eval_Case; lift_premise.
  - enter_budget_case. budget_leaf Eval_Coercion.
  - enter_budget_case. budget_leaf Eval_Type.
  - enter_budget_case. budget_leaf Eval_Prune.
  - enter_budget_case.
  - enter_budget_case. budget_leaf Apply_Con.
  - enter_budget_case.
    exists h. intros n Hn. eapply Apply_Clos. lift_premise.
  - enter_budget_case.
    exists h. intros n Hn. eapply Apply_Prim. lift_premise.
  - enter_budget_case.
    exists h. intros n Hn. eapply Apply_Cast; [eassumption | lift_premise].
  - enter_budget_case. budget_leaf Apply_Bot.
  - enter_budget_case.
    exists (h + h0). intros n Hn. eapply Apply_If; lift_premise.
  - enter_budget_case. budget_leaf Prim_Partial.
  - enter_budget_case.
    exists (h + h0). intros n Hn. eapply Prim_Ite; lift_premise.
  - enter_budget_case.
    match goal with
    | Hall : Forall2 _ _ _ |- _ => destruct (forces_have_budget _ _ _ Hall) as [h Hh]
    end.
    exists h. intros n Hn. eapply Prim_Reduce; [eassumption | eassumption | lift_premise].
  - enter_budget_case.
    exists h. intros n Hn. eapply Force_Susp. lift_premise.
  - enter_budget_case.
    exists (h + h0). intros n Hn. eapply Force_If; lift_premise.
  - enter_budget_case.
    exists h. intros n Hn. eapply Select_True. lift_premise.
  - enter_budget_case.
    exists h. intros n Hn. eapply Select_False; [eassumption | lift_premise].
  - enter_budget_case.
    exists (h + h0). intros n Hn. eapply Select_Sym; [eassumption | lift_premise ..].
  - enter_budget_case. budget_leaf Select_Bot.
  - enter_budget_case.
    exists (h + h0). intros n Hn. eapply Select_If; lift_premise.
  - enter_budget_case.
    exists h. intros n Hn. eapply Fold_Con; [eassumption | lift_premise].
  - enter_budget_case. budget_leaf Fold_Bot.
  - enter_budget_case.
    exists (h + h0). intros n Hn. eapply Fold_If; lift_premise.
  - enter_budget_case. budget_leaf Fold_Otherwise.
Qed.

Lemma eval_inf_has_budget : forall Φ Γ e v,
  Φ ; Γ ⊢ e ⇓ v -> exists h, forall n, h <= n -> eval (Fin n) Φ Γ e v.
Proof.
  intros Φ Γ e v Heval. exact (proj1 inf_has_budget_mutual _ _ _ _ _ Heval eq_refl).
Qed.

Lemma apply_inf_has_budget : forall Φ Γ vf e v,
  apply Inf Φ Γ vf e v -> exists h, forall n, h <= n -> apply (Fin n) Φ Γ vf e v.
Proof.
  intros Φ Γ vf e v Happ.
  exact (proj1 (proj2 inf_has_budget_mutual) _ _ _ _ _ _ Happ eq_refl).
Qed.

Lemma prim_app_inf_has_budget : forall Φ op ts v,
  prim_app Inf Φ op ts v -> exists h, forall n, h <= n -> prim_app (Fin n) Φ op ts v.
Proof.
  intros Φ op ts v Hprim.
  exact (proj1 (proj2 (proj2 inf_has_budget_mutual)) _ _ _ _ _ Hprim eq_refl).
Qed.

Lemma force_inf_has_budget : forall Φ t v,
  force Inf Φ t v -> exists h, forall n, h <= n -> force (Fin n) Φ t v.
Proof.
  intros Φ t v Hforce.
  exact (proj1 (proj2 (proj2 (proj2 inf_has_budget_mutual))) _ _ _ _ Hforce eq_refl).
Qed.

Lemma select_inf_has_budget : forall Φ c tthen telse v,
  select Inf Φ c tthen telse v ->
  exists h, forall n, h <= n -> select (Fin n) Φ c tthen telse v.
Proof.
  intros Φ c tthen telse v Hselect.
  exact (proj1 (proj2 (proj2 (proj2 (proj2 inf_has_budget_mutual))))
    _ _ _ _ _ _ Hselect eq_refl).
Qed.

Lemma fold_alts_inf_has_budget : forall Φ Γ vs alts v,
  fold_alts Inf Φ Γ vs alts v ->
  exists h, forall n, h <= n -> fold_alts (Fin n) Φ Γ vs alts v.
Proof.
  intros Φ Γ vs alts v Hfold.
  exact (proj2 (proj2 (proj2 (proj2 (proj2 inf_has_budget_mutual))))
    _ _ _ _ _ _ Hfold eq_refl).
Qed.

End SymCore.
