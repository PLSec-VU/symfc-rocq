From SymCoreTheory Require Export Model.Model.
From Stdlib Require Import Strings.String Lists.List ZArith.ZArith Bool.Bool Arith.PeanoNat Lia.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Section SymCore.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.
Context {reduce_prim_solvable_law : ReducePrimSolvable}.
Context {reduce_prim_saturated_law : ReducePrimSaturated}.
(**
  The bridge does not run backwards. A finite budget answers terms that the
  unlimited budget never answers, so the two judgements are not the same
  relation and no later proof may treat them as one.

  The witness is the self-application below. It is not stuck: the rules do apply to it,
  and each turn of the loop lands in the same shape one environment deeper.
  The unlimited budget therefore runs forever and delivers nothing, while
  every finite budget stops the loop and delivers a value.

  The environment is what makes the argument work. Each turn binds f again,
  and the new binding is not the lambda but the name f read back in the
  previous environment. So after n turns the name resolves through a chain of
  n indirections. ResolvesToSelfApp is that chain, and SelfAppState lists the
  four shapes the loop passes through.
*)
Definition self_app_var : var := "f".
Definition self_app_body : expr := EApp (EVar self_app_var) (EVar self_app_var).
Definition self_app_fun : expr := ELam self_app_var self_app_body.
Definition self_app : expr := EApp self_app_fun self_app_fun.

Lemma self_app_fun_comp : forall Γ, Comp Γ self_app_fun.
Proof. intros Γ. apply Comp_Lam. Qed.

Lemma eval_self_app_fun : forall Φ Γ v,
  sat Φ = true -> Φ ; Γ ⊢ self_app_fun ⇓ v -> v = EThunk Γ self_app_fun.
Proof.
  intros Φ Γ v Hsat H. inversion H; subst; [no_con_head | reflexivity | congruence].
Qed.

(** The chain of indirections that still ends at the loop lambda. *)
Inductive ResolvesToSelfApp : environment -> Prop :=
  | RSA_Lam : forall Γ Γ0,
      lookup_env Γ self_app_var = Some (Γ0, self_app_fun) ->
      ResolvesToSelfApp Γ
  | RSA_Indirect : forall Γ Γ0,
      lookup_env Γ self_app_var = Some (Γ0, EVar self_app_var) ->
      ResolvesToSelfApp Γ0 ->
      ResolvesToSelfApp Γ.

Lemma self_app_extend_fun : forall Γ0 Γ,
  ResolvesToSelfApp (extend_env Γ0 self_app_var Γ self_app_fun).
Proof.
  intros Γ0 Γ. eapply RSA_Lam. unfold extend_env. simpl.
  destruct (string_dec self_app_var self_app_var); [reflexivity | contradiction].
Qed.

Lemma self_app_extend_var : forall Γ0 Γ,
  ResolvesToSelfApp Γ ->
  ResolvesToSelfApp (extend_env Γ0 self_app_var Γ (EVar self_app_var)).
Proof.
  intros Γ0 Γ H. eapply RSA_Indirect; [| exact H]. unfold extend_env. simpl.
  destruct (string_dec self_app_var self_app_var); [reflexivity | contradiction].
Qed.

Lemma self_app_var_comp : forall Γ,
  ResolvesToSelfApp Γ -> Comp Γ (EVar self_app_var).
Proof.
  intros Γ HR. apply Comp_Var. destruct HR; congruence.
Qed.

Lemma eval_self_app_var : forall Φ Γ,
  ResolvesToSelfApp Γ ->
  sat Φ = true ->
  forall v, Φ ; Γ ⊢ EVar self_app_var ⇓ v ->
  exists Γ0, v = EThunk Γ0 self_app_fun.
Proof.
  intros Φ Γ HR Hsat. induction HR.
  - intros v Hev. inversion Hev; subst.
    + rewrite H in H2. injection H2 as ? ?; subst.
      eexists. eapply eval_self_app_fun; [exact Hsat | eassumption].
    + congruence.
    + no_con_head.
    + congruence.
  - intros v Hev. inversion Hev; subst.
    + rewrite H in H2. injection H2 as ? ?; subst. apply IHHR. eassumption.
    + congruence.
    + no_con_head.
    + congruence.
Qed.

(** The four shapes the loop passes through. *)
Inductive SelfAppState : environment -> expr -> Prop :=
  | SA_Self : forall Γ,
      SelfAppState Γ self_app
  | SA_ClosFun : forall Γ Γ0,
      SelfAppState Γ (EApp (EThunk Γ0 self_app_fun) self_app_fun)
  | SA_Var : forall Γ,
      ResolvesToSelfApp Γ ->
      SelfAppState Γ self_app_body
  | SA_ClosVar : forall Γ Γ0,
      ResolvesToSelfApp Γ ->
      SelfAppState Γ (EApp (EThunk Γ0 self_app_fun) (EVar self_app_var)).

(** Every step out of a loop shape lands in a loop shape, so an unbounded
    derivation can never bottom out. The induction is on the derivation, not
    on the term. It keeps the index, so that Rule Out-Of-Fuel stays out. *)
Lemma self_app_has_no_value : forall Φ Γ e v,
  Φ ; Γ ⊢ e ⇓ v -> sat Φ = true -> SelfAppState Γ e -> False.
Proof.
  intros Φ Γ e v H.
  remember Inf as kf eqn:Hkf in H.
  induction H; try discriminate Hkf; try (injection Hkf as Hkf); subst;
    intros Hsat HL;
    try (inversion HL; unfold self_app, self_app_body, self_app_fun in *; discriminate).
  - (* Rule Con: no loop shape has a constructor at the head of its spine *)
    inversion HL; subst;
      match goal with
      | [ Hu : unspool_app _ _ = (ECon _, _) |- _ ] => discriminate Hu
      end.
  - (* Rule App-Abs *)
    inversion HL; subst.
    + apply IHeval; [reflexivity | exact Hsat | apply SA_Var; apply self_app_extend_fun].
    + apply IHeval; [reflexivity | exact Hsat |].
      apply SA_Var. apply self_app_extend_var. assumption.
  - (* Rule App-Spine *)
    inversion HL; subst.
    + assert (Hef : ef' = EThunk Γ self_app_fun)
        by (apply (eval_self_app_fun Φ Γ ef' Hsat); assumption).
      subst ef'. apply IHeval2; [reflexivity | exact Hsat | apply SA_ClosFun].
    + match goal with [ Hc : Comp _ (EThunk _ _) |- _ ] => inversion Hc; discriminate end.
    + match goal with
      | [ HR : ResolvesToSelfApp Γ, He : eval _ Φ Γ (EVar self_app_var) ef' |- _ ] =>
          destruct (eval_self_app_var Φ Γ HR Hsat ef' He) as [Γ0 Hef]; subst ef';
          apply IHeval2; [reflexivity | exact Hsat | apply SA_ClosVar; exact HR]
      end.
    + match goal with [ Hc : Comp _ (EThunk _ _) |- _ ] => inversion Hc; discriminate end.
  - (* Rule App-Prim *)
    inversion HL; subst; unfold self_app, self_app_body, self_app_fun in H; simpl in H;
      injection H as ? ?; discriminate.
  - inversion HL; subst;
      match goal with
      | [ Hu : unspool_app _ _ = (EIf _ _ _, _) |- _ ] =>
          unfold self_app, self_app_body, self_app_fun in Hu; simpl in Hu; discriminate Hu
      end.
  - (* Rule Prune *)
    congruence.
Qed.

Lemma self_app_diverges : forall Φ Γ v,
  sat Φ = true -> ~ (Φ ; Γ ⊢ self_app ⇓ v).
Proof.
  intros Φ Γ v Hsat H.
  eapply self_app_has_no_value; [exact H | exact Hsat | apply SA_Self].
Qed.

(** Reading f at a finite budget either runs out of budget or delivers the
    loop closure, whatever the length of the chain. *)
Lemma self_app_var_value_bounded : forall Γ,
  ResolvesToSelfApp Γ ->
  forall k Ψ, exists v,
    eval (Fin k) Ψ Γ (EVar self_app_var) v
    /\ (v = EBot BOutOfFuel \/ exists Γ0, v = EThunk Γ0 self_app_fun).
Proof.
  intros Γ HR. induction HR as [Γa Γb Hl | Γa Γb Hl HR IH];
    intros k Ψ; destruct k as [| k].
  - exists (EBot BOutOfFuel). split; [apply Eval_OutOfFuel | left; reflexivity].
  - destruct k as [| k].
    + exists (EBot BOutOfFuel).
      split; [eapply Eval_Var; [exact Hl | apply Eval_OutOfFuel] | left; reflexivity].
    + exists (EThunk Γb self_app_fun). split.
      * eapply Eval_Var; [exact Hl |]. simpl. unfold self_app_fun. apply Eval_Lam.
      * right. exists Γb. reflexivity.
  - exists (EBot BOutOfFuel). split; [apply Eval_OutOfFuel | left; reflexivity].
  - destruct (IH k Ψ) as [v [Hv Hshape]].
    exists v. split; [eapply Eval_Var; [exact Hl | exact Hv] | exact Hshape].
Qed.

(** Every loop shape has a value at every finite budget. The loop never
    blocks, it only stops, so a budget always delivers a derivation where the
    unlimited judgement delivers none. *)
Lemma self_app_state_has_value_at_every_budget : forall k Ψ Γ e,
  SelfAppState Γ e -> exists v, eval (Fin k) Ψ Γ e v.
Proof.
  induction k as [| k IH]; intros Ψ Γ e HL.
  - exists (EBot BOutOfFuel). apply Eval_OutOfFuel.
  - inversion HL; subst.
    + destruct k as [| k].
      * exists (EBot BOutOfFuel). unfold self_app.
        eapply Eval_AppSpine with (ef' := EBot BOutOfFuel);
          [apply self_app_fun_comp | apply Eval_OutOfFuel
          | apply Eval_OutOfFuel].
      * destruct (IH Ψ Γ (EApp (EThunk Γ self_app_fun) self_app_fun)
                   (SA_ClosFun Γ Γ)) as [v Hv].
        exists v. unfold self_app.
        eapply Eval_AppSpine with (ef' := EThunk Γ self_app_fun).
        -- apply self_app_fun_comp.
        -- simpl. unfold self_app_fun. apply Eval_Lam.
        -- simpl. exact Hv.
    + destruct (IH Ψ (extend_env Γ1 self_app_var Γ self_app_fun) self_app_body
                 (SA_Var _ (self_app_extend_fun Γ1 Γ))) as [v Hv].
      exists v. apply Eval_AppAbs. simpl. exact Hv.
    + destruct (self_app_var_value_bounded Γ H k Ψ) as [vf [Hvf [Hbot | [Γ0 Hclos]]]].
      * subst vf. exists (EBot BOutOfFuel). unfold self_app_body.
        eapply Eval_AppSpine with (ef' := EBot BOutOfFuel).
        -- apply self_app_var_comp. exact H.
        -- simpl. exact Hvf.
        -- destruct k as [| k]; [apply Eval_OutOfFuel | apply Eval_AppBot].
      * subst vf.
        destruct (IH Ψ Γ (EApp (EThunk Γ0 self_app_fun) (EVar self_app_var))
                   (SA_ClosVar Γ Γ0 H)) as [v Hv].
        exists v. unfold self_app_body.
        eapply Eval_AppSpine with (ef' := EThunk Γ0 self_app_fun).
        -- apply self_app_var_comp. exact H.
        -- simpl. exact Hvf.
        -- simpl. exact Hv.
    + destruct (IH Ψ (extend_env Γ1 self_app_var Γ (EVar self_app_var)) self_app_body
                 (SA_Var _ (self_app_extend_var Γ1 Γ H))) as [v Hv].
      exists v. apply Eval_AppAbs. simpl. exact Hv.
Qed.

Corollary self_app_has_value_at_every_budget : forall k Ψ Γ,
  exists v, eval (Fin k) Ψ Γ self_app v.
Proof.
  intros k Ψ Γ.
  apply (self_app_state_has_value_at_every_budget k Ψ Γ self_app (SA_Self Γ)).
Qed.

End SymCore.
