From SymCoreTheory Require Import SymCore ConCore.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

Ltac prune_absurd :=
  match goal with
  | [ Hs : sat ?F = true, Hu : sat ?F = false |- _ ] => rewrite Hs in Hu; discriminate
  end.

(* ---------- inversion lemmas, one per value shape ---------- *)

Lemma eval_var_bound_inv : forall Φ Γ x Γ' e0 v,
  sat Φ = true ->
  lookup_env Γ x = Some (Γ', e0) ->
  Φ ; Γ ⊢ EVar x ⇓ v ->
  Φ ; Γ' ⊢ e0 ⇓ v.
Proof.
  intros Φ Γ x Γ' e0 v Hsat Hlook Heval.
  inversion Heval; subst; try prune_absurd.
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
  inversion Heval; subst; try prune_absurd; [congruence | reflexivity].
Qed.

Lemma eval_lit_inv : forall Φ Γ l v,
  sat Φ = true -> Φ ; Γ ⊢ ELit l ⇓ v -> v = ELit l.
Proof. intros Φ Γ l v Hsat Heval. inversion Heval; subst; try prune_absurd; reflexivity. Qed.

Lemma eval_con_inv : forall Φ Γ d v,
  sat Φ = true -> Φ ; Γ ⊢ ECon d ⇓ v -> v = ECon d.
Proof. intros Φ Γ d v Hsat Heval. inversion Heval; subst; try prune_absurd; reflexivity. Qed.

Lemma eval_bot_inv : forall Φ Γ b v,
  sat Φ = true -> Φ ; Γ ⊢ EBot b ⇓ v -> v = EBot b.
Proof. intros Φ Γ b v Hsat Heval. inversion Heval; subst; try prune_absurd; reflexivity. Qed.

Lemma eval_lam_inv : forall Φ Γ x e0 v,
  sat Φ = true -> Φ ; Γ ⊢ ELam x e0 ⇓ v -> v = EClos Γ x e0.
Proof. intros Φ Γ x e0 v Hsat Heval. inversion Heval; subst; try prune_absurd; reflexivity. Qed.

Lemma eval_coercion_inv : forall Φ Γ γ v,
  sat Φ = true -> Φ ; Γ ⊢ ECoercion γ ⇓ v -> v = ECoercion (subst_coerc Γ γ).
Proof. intros Φ Γ γ v Hsat Heval. inversion Heval; subst; try prune_absurd; reflexivity. Qed.

Lemma eval_type_inv : forall Φ Γ τ v,
  sat Φ = true -> Φ ; Γ ⊢ EType τ ⇓ v -> v = EType (subst_type Γ τ).
Proof. intros Φ Γ τ v Hsat Heval. inversion Heval; subst; try prune_absurd; reflexivity. Qed.

Lemma eval_cast_inv : forall Φ Γ e0 γ v,
  sat Φ = true ->
  Φ ; Γ ⊢ ECast e0 γ ⇓ v ->
  exists e', Φ ; Γ ⊢ e0 ⇓ e' /\ v = cast_expr e' γ.
Proof.
  intros Φ Γ e0 γ v Hsat Heval.
  inversion Heval; subst; try prune_absurd.
  eexists. split; [eassumption | reflexivity].
Qed.

Lemma eval_case_inv : forall Φ Γ es alts v,
  sat Φ = true ->
  Φ ; Γ ⊢ ECase es alts ⇓ v ->
  exists es', Φ ; Γ ⊢ es ⇓ es' /\ fold_alts Φ Γ (merge es') alts v.
Proof.
  intros Φ Γ es alts v Hsat Heval.
  inversion Heval; subst; try prune_absurd.
  eexists. split; eassumption.
Qed.

Lemma eval_app_clos_inv : forall Φ Γ Γ' x eb ea v,
  sat Φ = true ->
  Φ ; Γ ⊢ EApp (EClos Γ' x eb) ea ⇓ v ->
  Φ ; extend_env Γ' x Γ ea ⊢ eb ⇓ v.
Proof.
  intros Φ Γ Γ' x eb ea v Hsat Heval.
  inversion Heval; subst; try prune_absurd.
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
  inversion Heval; subst; try prune_absurd.
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
  inversion Heval; subst; try prune_absurd.
  - exfalso. match goal with
    | [ H : cast_arrow_operator (ECast eb γ) = false |- _ ] =>
        simpl in H; rewrite Hdec in H; discriminate
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

Lemma eval_app_spine_inv : forall Φ Γ ef ea ef0 v,
  sat Φ = true ->
  ~ Whnf Γ ef ->
  cast_arrow_operator ef = false ->
  Φ ; Γ ⊢ ef ⇓ ef0 ->
  Φ ; Γ ⊢ EApp ef ea ⇓ v ->
  exists ef', Φ ; Γ ⊢ ef ⇓ ef' /\ Φ ; Γ ⊢ EApp ef' ea ⇓ v.
Proof.
  intros Φ Γ ef ea ef0 v Hsat Hnw Hguard Heval0 Heval.
  inversion Heval; subst; try prune_absurd.
  - exfalso. apply Hnw. apply Whnf_Clos.
  - eexists. split; eassumption.
  - exfalso. match goal with
    | [ Hu : unspool_app (EApp ef ea) [] = (EPrimOp ?p, ?args),
        Hl : Datatypes.length ?args = primop_arity ?p |- _ ] =>
        exact (prim_operator_has_no_value Φ Γ ef ea p args ef0 Hsat Hu Hl Heval0)
    end.
  - exfalso. simpl in Hguard.
    match goal with
    | [ H : decomp_coerc_arrow ?g = Some _ |- _ ] => rewrite H in Hguard; discriminate
    end.
  - exfalso. apply Hnw. apply Whnf_Bot.
Qed.

Lemma eval_app_prim_inv : forall Φ Γ ef ea p args v,
  sat Φ = true ->
  unspool_app (EApp ef ea) [] = (EPrimOp p, args) ->
  Datatypes.length args = primop_arity p ->
  Φ ; Γ ⊢ EApp ef ea ⇓ v ->
  exists args', Forall2 (eval Φ Γ) args args' /\ v = reduce_prim p args'.
Proof.
  intros Φ Γ ef ea p args v Hsat Hun Hlen Heval.
  inversion Heval; subst; try prune_absurd.
  - simpl in Hun. injection Hun as Hh _. discriminate.
  - exfalso. match goal with
    | [ He : Φ ; Γ ⊢ ef ⇓ ?ef' |- _ ] =>
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

Lemma fold_alts_con_inv : forall Φ Γ e d ea xs ep alts r,
  decompose_con_app e = Some (d, ea) ->
  find_alt d alts = Some (xs, ep) ->
  fold_alts Φ Γ e alts r ->
  Φ ; extend_env_multi Γ xs ea Γ ⊢ ep ⇓ r.
Proof.
  intros Φ Γ e d ea xs ep alts r Hdec Hfind Hfold.
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

Lemma fold_alts_bot_inv : forall Φ Γ b alts r,
  fold_alts Φ Γ (EBot b) alts r -> r = EBot b.
Proof.
  intros Φ Γ b alts r Hfold.
  inversion Hfold; subst; try reflexivity; try discriminate.
Qed.

Lemma fold_alts_otherwise_inv : forall Φ Γ e alts r,
  is_if e = false ->
  (match decompose_con_app e with
   | Some (d, _) => find_alt d alts = None
   | None => True
   end) ->
  is_bot e = false ->
  fold_alts Φ Γ e alts r ->
  r = EBot BUndefined.
Proof.
  intros Φ Γ e alts r Hif Hno Hbot Hfold.
  inversion Hfold; subst; simpl in *; try discriminate; try reflexivity.
  - exfalso. match goal with
    | [ Hd : decompose_con_app e = Some (?D, ?EA),
        Hf : find_alt ?D alts = Some _ |- _ ] =>
        rewrite Hd in Hno; rewrite Hno in Hf; discriminate
    end.
Qed.

(* ---------- determinism ---------- *)

Fixpoint eval_det_fix (Φ : path_condition) (Γ : environment) (e v1 : expr)
  (Heval : Φ; Γ ⊢ e ⇓ v1) {struct Heval} :
  forall v2, sat Φ = true -> concrete_env Γ -> concore_expr e ->
    Φ; Γ ⊢ e ⇓ v2 -> v1 = v2
with fold_alts_det_fix (Φ : path_condition) (Γ : environment) (e : expr)
  (alts : list alt) (r1 : expr) (Hfold : fold_alts Φ Γ e alts r1) {struct Hfold} :
  forall r2, sat Φ = true -> concrete_env Γ -> concore_expr e ->
    Forall concore_alt alts -> fold_alts Φ Γ e alts r2 -> r1 = r2.
Proof.
{
  destruct Heval as
    [ Φ Γ x Γ' e0 e' Hlook Heval_x
    | Φ Γ x Hnone
    | Φ Γ l
    | Φ Γ d
    | Φ Γ e0 γ e' Heval_e
    | Φ Γ Γ' x eb ea eb' Heval_b
    | Φ Γ ef ea ef' er Hnotwhnf Hnoarrow Heval_f Heval_app2
    | Φ Γ b
    | Φ Γ ef ea p args args' Hunspool Harity Hargs
    | Φ Γ x e0
    | Φ Γ ef γ ea γ_a γ_r er Hdecomp Heval_pushed
    | Φ Γ b ea
    | Φ Γ es alts es' er Heval_es Hfold
    | Φ Γ ec et ef ec' et' ef' pc_c Heval_c Hpc Heval_t Heval_ff
    | Φ Γ γ
    | Φ Γ e0 Hunsat
    | Φ Γ τ
    ]; intros v2 Hsat Henv Hcon H2.
  - (* Eval_Var *)
    destruct (lookup_env_concrete Γ x Γ' e0 Henv Hlook) as [Henv' He].
    exact (eval_det_fix Φ Γ' e0 e' Heval_x v2 Hsat Henv' He
             (eval_var_bound_inv Φ Γ x Γ' e0 v2 Hsat Hlook H2)).
  - (* Eval_SymVar *) symmetry. exact (eval_var_free_inv Φ Γ x v2 Hsat Hnone H2).
  - (* Eval_Lit *) symmetry. exact (eval_lit_inv Φ Γ l v2 Hsat H2).
  - (* Eval_Con *) symmetry. exact (eval_con_inv Φ Γ d v2 Hsat H2).
  - (* Eval_Cast *)
    destruct (eval_cast_inv Φ Γ e0 γ v2 Hsat H2) as [e2' [He2 Heq]]. subst v2.
    f_equal.
    exact (eval_det_fix Φ Γ e0 e' Heval_e e2' Hsat Henv
             (concore_expr_cast e0 γ Hcon) He2).
  - (* Eval_AppAbs *)
    pose proof (concore_expr_app_l _ _ Hcon) as Hclos.
    pose proof (concore_expr_app_r _ _ Hcon) as Hea.
    exact (eval_det_fix Φ (extend_env Γ' x Γ ea) eb eb' Heval_b v2 Hsat
             (concrete_env_extend Γ' x Γ ea (concore_expr_clos_env _ _ _ Hclos) Henv Hea)
             (concore_expr_clos _ _ _ Hclos)
             (eval_app_clos_inv Φ Γ Γ' x eb ea v2 Hsat H2)).
  - (* Eval_AppSpine *)
    pose proof (concore_expr_app_l _ _ Hcon) as Hcf.
    pose proof (concore_expr_app_r _ _ Hcon) as Hca.
    destruct (eval_app_spine_inv Φ Γ ef ea ef' v2 Hsat Hnotwhnf Hnoarrow Heval_f H2)
      as [ef2 [Hef2 Happ2]].
    assert (Heqf : ef' = ef2)
      by exact (eval_det_fix Φ Γ ef ef' Heval_f ef2 Hsat Henv Hcf Hef2).
    subst ef2.
    exact (eval_det_fix Φ Γ (EApp ef' ea) er Heval_app2 v2 Hsat Henv
             (Con_App ef' ea (concore_eval_closed_fix Φ Γ ef ef' Heval_f Hsat Henv Hcf) Hca)
             Happ2).
  - (* Eval_Bot *) symmetry. exact (eval_bot_inv Φ Γ b v2 Hsat H2).
  - (* Eval_AppPrim *)
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
      * exact (eval_det_fix Φ Γ a0 a0' Ha0 b0' Hsat Henv Hc0 Hb0).
      * exact (IH tl2' Htl2 Hctl).
  - (* Eval_Lam *) symmetry. exact (eval_lam_inv Φ Γ x e0 v2 Hsat H2).
  - (* Eval_AppCast *)
    pose proof (concore_expr_app_l _ _ Hcon) as Hcast.
    pose proof (concore_expr_app_r _ _ Hcon) as Hea.
    exact (eval_det_fix Φ Γ (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r) er
             Heval_pushed v2 Hsat Henv
             (Con_Cast _ γ_r (Con_App _ _ (concore_expr_cast _ _ Hcast)
                                          (Con_Cast _ _ Hea)))
             (eval_app_cast_arrow_inv Φ Γ ef γ γ_a γ_r ea v2 Hsat Hdecomp H2)).
  - (* Eval_AppBot *) symmetry. exact (eval_app_bot_inv Φ Γ b ea v2 Hsat H2).
  - (* Eval_Case *)
    destruct (eval_case_inv Φ Γ es alts v2 Hsat H2) as [es2 [Hes2 Hfold2]].
    assert (Hces : concore_expr es) by exact (concore_expr_case_es es alts Hcon).
    assert (Halts : Forall concore_alt alts) by (inversion Hcon; subst; assumption).
    assert (Heq : es' = es2)
      by exact (eval_det_fix Φ Γ es es' Heval_es es2 Hsat Henv Hces Hes2).
    subst es2.
    exact (fold_alts_det_fix Φ Γ (merge es') alts er Hfold v2 Hsat Henv
             (merge_concore es' (concore_eval_closed_fix Φ Γ es es' Heval_es Hsat Henv Hces))
             Halts Hfold2).
  - (* Eval_If *) exfalso. exact (not_concore_if ec et ef Hcon).
  - (* Eval_Coercion *) symmetry. exact (eval_coercion_inv Φ Γ γ v2 Hsat H2).
  - (* Eval_Prune *) exfalso. rewrite Hsat in Hunsat. discriminate.
  - (* Eval_Type *) symmetry. exact (eval_type_inv Φ Γ τ v2 Hsat H2).
}
{
  destruct Hfold as
    [ Φ Γ ec et ef alts et' ef' pc_c Hpc Hfold_t Hfold_f
    | Φ Γ ec et ef alts Hpc_none
    | Φ Γ e0 d ea xs ep alts er Hdec Halt Heval_ep
    | Φ Γ b alts
    | Φ Γ e0 alts Hnotif Hnoalt Hnotbot
    ]; intros r2 Hsat Henv Hcon Halts H2.
  - exfalso. exact (not_concore_if ec et ef Hcon).
  - exfalso. exact (not_concore_if ec et ef Hcon).
  - (* FoldAlts_Con *)
    assert (Hea : Forall concore_expr ea)
      by exact (decompose_con_app_concore e0 d ea Hdec Hcon).
    assert (Hep : concore_expr ep)
      by exact (find_alt_concore d alts xs ep Halt Halts).
    exact (eval_det_fix Φ (extend_env_multi Γ xs ea Γ) ep er Heval_ep r2 Hsat
             (concrete_env_extend_multi xs ea Γ Γ Henv Henv Hea) Hep
             (fold_alts_con_inv Φ Γ e0 d ea xs ep alts r2 Hdec Halt H2)).
  - (* FoldAlts_Bot *) symmetry. exact (fold_alts_bot_inv Φ Γ b alts r2 H2).
  - (* FoldAlts_Otherwise *)
    symmetry.
    exact (fold_alts_otherwise_inv Φ Γ e0 alts r2 Hnotif Hnoalt Hnotbot H2).
}
Qed.

Definition ConcoreEvalDeterministic : Prop :=
  forall Γ e v1 v2, concore_expr e ->
    Γ ⊢ᶜ e ⇓ᶜ v1 -> Γ ⊢ᶜ e ⇓ᶜ v2 -> v1 = v2.

Lemma concore_eval_deterministic : forall Γ e v1 v2,
  concrete_env Γ ->
  concore_expr e ->
  Γ ⊢ᶜ e ⇓ᶜ v1 ->
  Γ ⊢ᶜ e ⇓ᶜ v2 ->
  v1 = v2.
Proof.
  intros Γ e v1 v2 Henv Hcon H1 H2.
  exact (eval_det_fix pc_true Γ e v1 H1 v2 sat_pc_true Henv Hcon H2).
Qed.

Corollary concore_eval_deterministic_top : forall e v1 v2,
  concore_expr e -> ⊢ᶜ e ⇓ᶜ v1 -> ⊢ᶜ e ⇓ᶜ v2 -> v1 = v2.
Proof.
  intros e v1 v2 Hcon H1 H2.
  exact (concore_eval_deterministic · e v1 v2 CEnv_Empty Hcon H1 H2).
Qed.

(* The environment hypothesis cannot be dropped: a ConCore expression is a
   variable, and nothing says the environment binds it to a ConCore
   expression. Bind it to a branch and Section 12.1 comes back. *)
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
