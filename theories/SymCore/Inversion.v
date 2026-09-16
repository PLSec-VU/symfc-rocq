From SymCoreTheory Require Export SymCore.SolvableFacts.
From Stdlib Require Import Strings.String Lists.List ZArith.ZArith Bool.Bool Arith.PeanoNat Lia.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Section SymCore.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.
Context {reduce_prim_solvable_law : ReducePrimSolvable}.
Context {reduce_prim_saturated_law : ReducePrimSaturated}.
(** ------------------------------------------------------------------------- *)
(** Determinism of Evaluation (§3.2)                                          *)
(** ------------------------------------------------------------------------- *)

(** Branch folding on bottom always preserves the bottom value *)
Lemma fold_alts_bot_same : forall f Φ Γ b alts r,
  fold_alts f Φ Γ (EBot b) alts r ->
  r = EBot b.
Proof.
  intros f Φ Γ b alts r Hfold.
  inversion Hfold; subst; try reflexivity;
    try (match goal with
         | [ H : expr_to_pc _ (EBot _) = Some _ |- _ ] => simpl in H; discriminate
         | [ H : decompose_con_app (EBot _) = Some _ |- _ ] =>
             unfold decompose_con_app in H; simpl in H; discriminate
         | [ H : is_bot (EBot _) = false |- _ ] => discriminate H
         end).
Qed.

Lemma eval_nullary_con : forall f Φ Γ d, eval (Live f) Φ Γ (ECon d) (ECon d).
Proof. intros f Φ Γ d. exact (Eval_Con f Φ Γ (ECon d) d [] eq_refl). Qed.

(** Evaluation of constructors under a satisfiable path condition *)
Lemma eval_con_same : forall Φ Γ d v,
  sat Φ = true ->
  Φ ; Γ ⊢ ECon d ⇓ v ->
  v = ECon d.
Proof.
  intros Φ Γ d v Hsat Heval.
  inversion Heval; subst.
  - match goal with
    | [ Hu : unspool_app (ECon d) [] = (ECon _, _) |- _ ] =>
        simpl in Hu; injection Hu as <- <-; reflexivity
    end.
  - rewrite Hsat in H0; discriminate.
Qed.

(** A constructor spine has one value, the one Rule Con builds: every other
    application rule wants a different head. *)
Lemma eval_con_spine_same : forall Φ Γ e d args v,
  sat Φ = true ->
  unspool_app e [] = (ECon d, args) ->
  Φ ; Γ ⊢ e ⇓ v ->
  v = make_con_app d (map (delay Γ) args).
Proof.
  intros Φ Γ e d args v Hsat Hu Heval.
  destruct e; simpl in Hu; try discriminate.
  - (* ECon *)
    injection Hu as ? ?; subst.
    exact (eval_con_same Φ Γ d v Hsat Heval).
  - (* EApp *)
    inversion Heval; subst.
    + match goal with
      | [ Hu2 : unspool_app (EApp _ _) [] = (ECon _, _) |- _ ] =>
          simpl in Hu2; rewrite Hu in Hu2; injection Hu2 as <- <-; reflexivity
      end.
    + simpl in Hu; discriminate.
    + match goal with
      | [ Hc : Comp _ e1 |- _ ] =>
          pose proof (unspool_is_con_app e1 [e2] d args Hu) as Hcon;
          rewrite (comp_not_con_app _ _ Hc) in Hcon; discriminate Hcon
      end.
    + match goal with
      | [ Hp : unspool_app (EApp _ _) [] = (EPrimOp _, _) |- _ ] =>
          simpl in Hp; rewrite Hu in Hp; discriminate
      end.
    + simpl in Hu; discriminate.
    + match goal with
      | [ Hp : unspool_app (EApp _ _) [] = (EIf _ _ _, _) |- _ ] =>
          simpl in Hp; rewrite Hu in Hp; discriminate
      end.
    + simpl in Hu; discriminate.
    + rewrite Hsat in *; discriminate.
Qed.

(** Evaluation of lambdas under a satisfiable path condition *)
Lemma eval_lam_same : forall Φ Γ x body v,
  sat Φ = true ->
  Φ ; Γ ⊢ ELam x body ⇓ v ->
  v = EThunk Γ (ELam x body).
Proof.
  intros Φ Γ x body v Hsat Heval.
  inversion Heval; subst.
  - no_con_head.
  - reflexivity.
  - rewrite Hsat in H0; discriminate.
Qed.

Lemma eval_thunk_ambient_env : forall k Φ Γ1 Γ2 Γ' e v,
  eval k Φ Γ1 (EThunk Γ' e) v -> eval k Φ Γ2 (EThunk Γ' e) v.
Proof.
  intros k Φ Γ1 Γ2 Γ' e v Heval.
  inversion Heval; subst.
  - no_con_head.
  - apply Eval_Prune. assumption.
  - apply Eval_Thunk. assumption.
  - apply Eval_OutOfFuel.
Qed.

Lemma eval_closure_same : forall Φ Γ Γ' x body v,
  sat Φ = true ->
  Φ ; Γ ⊢ EThunk Γ' (ELam x body) ⇓ v ->
  v = EThunk Γ' (ELam x body).
Proof.
  intros Φ Γ Γ' x body v Hsat Heval.
  inversion Heval; subst.
  - no_con_head.
  - rewrite Hsat in H0; discriminate.
  - eapply eval_lam_same; eassumption.
Qed.

(** Inversion of variable evaluation under a satisfiable path condition:
    a bound variable reduces to the reduct of its closure, an unbound
    (symbolic) one reduces to itself. *)
Lemma eval_var_inv : forall Φ Γ x v,
  sat Φ = true ->
  Φ ; Γ ⊢ EVar x ⇓ v ->
  (exists Γ' e, lookup_env Γ x = Some (Γ', e) /\ Φ ; Γ' ⊢ e ⇓ v)
  \/ (lookup_env Γ x = None /\ v = EVar x).
Proof.
  intros Φ Γ x v Hsat Heval.
  inversion Heval; subst.
  - left. exists Γ', e. split; [assumption | assumption].
  - right. split; [assumption | reflexivity].
  - no_con_head.
  - rewrite Hsat in H0; discriminate.
Qed.

(** A bound variable's evaluation still inverts to its closure alone *)
Lemma eval_var_bound_inv : forall Φ Γ x v Γ' e,
  sat Φ = true ->
  lookup_env Γ x = Some (Γ', e) ->
  Φ ; Γ ⊢ EVar x ⇓ v ->
  Φ ; Γ' ⊢ e ⇓ v.
Proof.
  intros Φ Γ x v Γ' e Hsat Hlook Heval.
  destruct (eval_var_inv Φ Γ x v Hsat Heval) as [[Γ'' [e'' [Hlook'' Hev'']]] | [Hnone Heq]].
  - rewrite Hlook in Hlook''. injection Hlook'' as ? ?; subst. assumption.
  - rewrite Hlook in Hnone. discriminate.
Qed.

(** Inversion of cast evaluation under a satisfiable path condition *)
Lemma eval_cast_inv : forall Φ Γ e γ v,
  sat Φ = true ->
  Φ ; Γ ⊢ ECast e γ ⇓ v ->
  exists e',
    Φ ; Γ ⊢ e ⇓ e' /\
    v = cast_expr e' γ.
Proof.
  intros Φ Γ e γ v Hsat Heval.
  inversion Heval; subst.
  - no_con_head.
  - exists e'. split; [assumption | reflexivity].
  - rewrite Hsat in H0; discriminate.
Qed.

(** Inversion of case evaluation under a satisfiable path condition *)
Lemma eval_case_inv : forall Φ Γ es alts v,
  sat Φ = true ->
  Φ ; Γ ⊢ ECase es alts ⇓ v ->
  exists es',
    Φ ; Γ ⊢ es ⇓ es' /\
    fold_alts Inf Φ Γ (merge Γ es') alts v.
Proof.
  intros Φ Γ es alts v Hsat Heval.
  inversion Heval; subst.
  - no_con_head.
  - exists es'. split; [assumption | assumption].
  - rewrite Hsat in H0; discriminate.
Qed.

(** Inversion of if-then-else evaluation under a satisfiable path condition *)
Lemma eval_if_inv : forall Φ Γ ec et ef v,
  sat Φ = true ->
  Φ ; Γ ⊢ EIf ec et ef ⇓ v ->
  exists ec' et' ef' pc_c,
    Φ ; Γ ⊢ ec ⇓ ec' /\
    expr_to_pc Γ ec' = Some pc_c /\
    (Φ ∧ pc_c) ; Γ ⊢ et ⇓ et' /\
    (Φ ∧ ¬ pc_c) ; Γ ⊢ ef ⇓ ef' /\
    v = EIf ec' et' ef'.
Proof.
  intros Φ Γ ec et ef v Hsat Heval.
  inversion Heval; subst.
  - no_con_head.
  - exists ec', et', ef', pc_c. split; [assumption|].
    split; [assumption|]. split; [assumption|].
    split; [assumption|reflexivity].
  - rewrite Hsat in H0; discriminate.
Qed.

(** Inversion for fold_alts on if-expressions with valid path condition *)
Lemma fold_alts_if_some_inv : forall f Φ Γ ec et ef alts r pc_c,
  expr_to_pc Γ ec = Some pc_c ->
  fold_alts f Φ Γ (EIf ec et ef) alts r ->
  exists et' ef',
    r = EIf ec et' ef' /\
    fold_alts f (Φ ∧ pc_c) Γ et alts et' /\
    fold_alts f (Φ ∧ ¬ pc_c) Γ ef alts ef'.
Proof.
  intros f Φ Γ ec et ef alts r pc_c Hpc Hfold.
  inversion Hfold; subst;
    try (match goal with
         | [ H : expr_to_pc _ (EIf _ _ _) = Some _ |- _ ] => simpl in H; discriminate
         | [ H : expr_to_pc _ ec = None |- _ ] => rewrite H in Hpc; discriminate
         | [ H : decompose_con_app (EIf _ _ _) = Some _ |- _ ] =>
             unfold decompose_con_app in H; simpl in H; discriminate
         | [ H : is_if (fst (unspool_app (EIf _ _ _) [])) = false |- _ ] =>
             simpl in H; discriminate
         end).
  match goal with [ H : expr_to_pc _ ec = Some _ |- _ ] => rewrite H in Hpc end.
  inversion Hpc; subst. eauto.
Qed.

(** Inversion for fold_alts on matching constructor patterns *)
Lemma fold_alts_con_inv : forall f Φ Γ e alts r d ea xs ep,
  decompose_con_app e = Some (d, ea) ->
  find_alt d alts = Some (xs, ep) ->
  is_if e = false ->
  is_bot e = false ->
  fold_alts f Φ Γ e alts r ->
  eval f Φ (extend_env_multi Γ xs ea Γ) ep r.
Proof.
  intros f Φ Γ e alts r d ea xs ep Hdec Halt Hnot_if Hnot_bot Hfold.
  inversion Hfold; subst;
    try (simpl in Hnot_if; discriminate);
    try (simpl in Hnot_bot; discriminate);
    try (match goal with
         | [ H : expr_to_pc _ e = Some _ |- _ ] =>
             exfalso; apply decompose_con_app_unspool in Hdec;
             apply unspool_is_con_app in Hdec;
             rewrite (solvable_not_con_app _ e (expr_to_pc_solvable _ e _ H)) in Hdec;
             discriminate Hdec
         | [ H : match decompose_con_app e with _ => _ end |- _ ] =>
             rewrite Hdec in H; rewrite Halt in H; discriminate
         end).
  match goal with [ H : decompose_con_app e = Some _ |- _ ] => rewrite H in Hdec end.
  inversion Hdec; subst.
  match goal with [ H : find_alt _ _ = Some _ |- _ ] => rewrite H in Halt end.
  inversion Halt; subst. assumption.
Qed.

(** Inversion for fold_alts on non-matching fallback expressions. The extra
    premises pin the scrutinee to Rule FoldAlts_Otherwise's own domain: it is
    neither a boolean formula (expr_to_pc = None) nor a primitive application
    (is_op_app = false), so the two new formula clauses cannot have fired. *)
Lemma fold_alts_otherwise_same : forall f Φ Γ e alts r,
  expr_to_pc Γ e = None ->
  is_op_app e = false ->
  is_if e = false ->
  (match decompose_con_app e with
   | Some (d, _) => find_alt d alts = None
   | None => True
   end) ->
  is_bot e = false ->
  fold_alts f Φ Γ e alts r ->
  r = EBot BUndefined.
Proof.
  intros f Φ Γ e alts r Hpc_none Hop Hnot_if Hno_alt Hnot_bot Hfold.
  inversion Hfold; subst; try reflexivity;
    try (simpl in Hnot_if; discriminate);
    try (simpl in Hnot_bot; discriminate);
    match goal with
    | [ H : expr_to_pc _ e = Some _ |- _ ] => rewrite H in Hpc_none; discriminate
    | [ H : decompose_con_app e = Some _ |- _ ] =>
        rewrite H in Hno_alt;
        match goal with [ Hf : find_alt _ _ = Some _ |- _ ] => rewrite Hf in Hno_alt; discriminate end
    end.
Qed.

(** Inversion for fold_alts on a boolean formula with no variable: the fold
    reduces to a match on the True or False constructor. *)
Lemma fold_alts_ground_formula_inv : forall f Φ Γ e pc alts r,
  expr_to_pc Γ e = Some pc -> pc_has_var pc = false ->
  fold_alts f Φ Γ e alts r ->
  fold_alts f Φ Γ (ECon (truth_constructor (pc_closed_value pc))) alts r.
Proof.
  intros f Φ Γ e pc alts r Hpc Hvar Hfold.
  pose proof (expr_to_pc_solvable Γ e pc Hpc) as Hsolv.
  inversion Hfold; subst;
    try (exfalso; inversion Hsolv; fail);
    try (match goal with
         | [ H : decompose_con_app e = Some _ |- _ ] =>
             exfalso; apply decompose_con_app_unspool in H;
             apply unspool_is_con_app in H;
             rewrite (solvable_not_con_app _ e Hsolv) in H; discriminate
         | [ H : expr_to_pc _ e = None |- _ ] => rewrite H in Hpc; discriminate
         | [ H : expr_to_pc _ e = Some ?pc0, Hv : pc_has_var ?pc0 = true |- _ ] =>
             rewrite (expr_to_pc_functional e _ _ pc0 pc H Hpc) in Hv;
             rewrite Hvar in Hv; discriminate
         end).
  match goal with
  | [ H : expr_to_pc _ e = Some ?pc0,
      Hrec : fold_alts _ _ _ (ECon (truth_constructor (pc_closed_value ?pc0))) _ _ |- _ ] =>
      rewrite (expr_to_pc_functional e _ _ pc pc0 Hpc H); exact Hrec
  end.
Qed.

(** Inversion for fold_alts on a boolean formula with a variable and correct
    arities: the fold is a runtime branch of the two folded alternatives. *)
Lemma fold_alts_symbolic_formula_inv : forall f Φ Γ e pc alts r,
  expr_to_pc Γ e = Some pc -> pc_has_var pc = true -> pc_arities_ok pc = true ->
  fold_alts f Φ Γ e alts r ->
  exists r1 r2, r = EIf e r1 r2 /\
    fold_alts f (Φ ∧ pc) Γ (ECon dcon_true) alts r1 /\
    fold_alts f (Φ ∧ ¬ pc) Γ (ECon dcon_false) alts r2.
Proof.
  intros f Φ Γ e pc alts r Hpc Hvar Har Hfold.
  pose proof (expr_to_pc_solvable Γ e pc Hpc) as Hsolv.
  inversion Hfold; subst;
    try (exfalso; inversion Hsolv; fail);
    try (match goal with
         | [ H : decompose_con_app e = Some _ |- _ ] =>
             exfalso; apply decompose_con_app_unspool in H;
             apply unspool_is_con_app in H;
             rewrite (solvable_not_con_app _ e Hsolv) in H; discriminate
         | [ H : expr_to_pc _ e = None |- _ ] => rewrite H in Hpc; discriminate
         | [ H : expr_to_pc _ e = Some ?pc0, Hv : pc_has_var ?pc0 = false |- _ ] =>
             exfalso; rewrite (expr_to_pc_functional e _ _ pc0 pc H Hpc) in Hv;
             rewrite Hvar in Hv; discriminate
         end).
  match goal with
  | [ H : expr_to_pc _ e = Some ?pc0,
      Hf1 : fold_alts _ _ _ (ECon dcon_true) _ ?r1,
      Hf2 : fold_alts _ _ _ (ECon dcon_false) _ ?r2 |- _ ] =>
      rewrite (expr_to_pc_functional e _ _ pc pc0 Hpc H);
      exists r1, r2; split; [reflexivity | split; assumption]
  end.
Qed.

Lemma decompose_con_app_none : forall e,
  is_con_app e = false -> decompose_con_app e = None.
Proof.
  intros e H. destruct (decompose_con_app e) as [[d args] |] eqn:Hd; [| reflexivity].
  apply decompose_con_app_unspool, unspool_is_con_app in Hd. congruence.
Qed.
End SymCore.
