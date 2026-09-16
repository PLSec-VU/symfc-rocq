From SymCoreTheory Require Export Completeness.Cost.
From Stdlib Require Import Bool.Bool Arith.Wf_nat Strings.String Lists.List Lia Arith.PeanoNat.
Import ListNotations.

Section SymReach.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : ConCoreLaws}.

Inductive sym_state : Type :=
  | SEval : environment -> expr -> sym_state
  | SFold : environment -> expr -> list alt -> sym_state.

Inductive sym_step : path_condition -> sym_state -> path_condition -> sym_state -> Prop :=
  | SymStep_Var : forall Φ Γ x Γ' e,
      lookup_env Γ x = Some (Γ', e) -> sym_step Φ (SEval Γ (EVar x)) Φ (SEval Γ' e)
  | SymStep_Cast : forall Φ Γ e γ, sym_step Φ (SEval Γ (ECast e γ)) Φ (SEval Γ e)
  | SymStep_AppAbs : forall Φ Γ Γ' x eb ea,
      sym_step Φ (SEval Γ (EApp (EThunk Γ' (ELam x eb)) ea)) Φ (SEval (extend_env Γ' x Γ ea) eb)
  | SymStep_AppFun : forall Φ Γ ef ea,
      sym_step Φ (SEval Γ (EApp ef ea)) Φ (SEval Γ ef)
  | SymStep_AppValue : forall Φ Γ ef ea ef' n,
      eval (Fin n) Φ Γ ef ef' -> sym_step Φ (SEval Γ (EApp ef ea)) Φ (SEval Γ (EApp ef' ea))
  | SymStep_AppArg : forall Φ Γ e h args a,
      unspool_app e nil = (h, args) -> In a args -> sym_step Φ (SEval Γ e) Φ (SEval Γ a)
  | SymStep_AppCast : forall Φ Γ ef γ ea γ_a γ_r,
      sym_step Φ (SEval Γ (EApp (ECast ef γ) ea)) Φ
               (SEval Γ (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r))
  | SymStep_AppIf : forall Φ Γ e1 e2 ec et ef args,
      unspool_app (EApp e1 e2) nil = (EIf ec et ef, args) ->
      sym_step Φ (SEval Γ (EApp e1 e2)) Φ
               (SEval Γ (EIf ec (fold_left EApp args et) (fold_left EApp args ef)))
  | SymStep_Thunk : forall Φ Γ Γ' e, sym_step Φ (SEval Γ (EThunk Γ' e)) Φ (SEval Γ' e)
  | SymStep_IfGuard : forall Φ Γ ec et ef, sym_step Φ (SEval Γ (EIf ec et ef)) Φ (SEval Γ ec)
  | SymStep_IfTrue : forall Φ Γ ec et ef pc,
      sym_step Φ (SEval Γ (EIf ec et ef)) (Φ ∧ pc) (SEval Γ et)
  | SymStep_IfFalse : forall Φ Γ ec et ef pc,
      sym_step Φ (SEval Γ (EIf ec et ef)) (Φ ∧ ¬ pc) (SEval Γ ef)
  | SymStep_CaseScrut : forall Φ Γ es alts, sym_step Φ (SEval Γ (ECase es alts)) Φ (SEval Γ es)
  | SymStep_CaseFold : forall Φ Γ es alts es' n,
      eval (Fin n) Φ Γ es es' ->
      sym_step Φ (SEval Γ (ECase es alts)) Φ (SFold Γ (merge Γ es') alts)
  | SymStep_FoldIfTrue : forall Φ Γ ec et ef alts pc,
      sym_step Φ (SFold Γ (EIf ec et ef) alts) (Φ ∧ pc) (SFold Γ et alts)
  | SymStep_FoldIfFalse : forall Φ Γ ec et ef alts pc,
      sym_step Φ (SFold Γ (EIf ec et ef) alts) (Φ ∧ ¬ pc) (SFold Γ ef alts)
  | SymStep_FoldCon : forall Φ Γ m alts d ea xs ep,
      decompose_con_app m = Some (d, ea) -> find_alt d alts = Some (xs, ep) ->
      sym_step Φ (SFold Γ m alts) Φ (SEval (extend_env_multi Γ xs ea Γ) ep)
  | SymStep_FoldGround : forall Φ Γ m alts d,
      sym_step Φ (SFold Γ m alts) Φ (SFold Γ (ECon d) alts)
  | SymStep_FoldTrue : forall Φ Γ m alts pc,
      sym_step Φ (SFold Γ m alts) (Φ ∧ pc) (SFold Γ (ECon dcon_true) alts)
  | SymStep_FoldFalse : forall Φ Γ m alts pc,
      sym_step Φ (SFold Γ m alts) (Φ ∧ ¬ pc) (SFold Γ (ECon dcon_false) alts).

Definition sym_state_scoped (S : symvars) (st : sym_state) : Prop :=
  match st with
  | SEval Γ e => sym_scoped_env S Γ /\ sym_scoped S (dom_env Γ) e
  | SFold Γ m alts =>
      sym_scoped_env S Γ /\ sym_scoped S nil m /\ Forall (sym_scoped_alt S (dom_env Γ)) alts
  end.

Lemma sym_step_scoped : forall S Φ st Φ' st',
  sym_state_scoped S st -> sym_step Φ st Φ' st' -> sym_state_scoped S st'.
Proof.
  intros S Φ st Φ' st' Hsc Hstep. destruct Hstep; simpl in *.
  - destruct Hsc as [HΓ Hsc].
    exact (sym_lookup_env_scoped S Γ x Γ' e HΓ H).
  - destruct Hsc as [HΓ Hsc]. inversion Hsc; subst. split; assumption.
  - destruct Hsc as [HΓ Hsc].
    inversion Hsc as [| | | | L0 f0 a0 Hscf Hsca | | | | | | | |]; subst.
    inversion Hscf as [| | | | | | | | | | | | L1 Γ1 e1 HΓ' Hsclam]; subst.
    inversion Hsclam as [| | | | | L2 x2 b2 Hscb | | | | | | |]; subst.
    split; [apply SymScoped_Env_Extend; assumption | exact Hscb].
  - destruct Hsc as [HΓ Hsc]. inversion Hsc; subst. split; assumption.
  - destruct Hsc as [HΓ Hsc].
    inversion Hsc as [| | | | L0 f0 a0 Hscf Hsca | | | | | | | |]; subst.
    split; [exact HΓ |].
    apply SymScoped_App; [apply sym_scoped_nil_any;
      exact (sym_eval_scoped_fix _ _ _ _ _ H S HΓ Hscf) | exact Hsca].
  - destruct Hsc as [HΓ Hsc]. split; [exact HΓ |].
    destruct (sym_unspool_app_scoped S (dom_env Γ) e [] h args H Hsc (Forall_nil _)) as [_ Hargs].
    rewrite Forall_forall in Hargs. exact (Hargs a H0).
  - destruct Hsc as [HΓ Hsc].
    inversion Hsc as [| | | | L0 f0 a0 Hscf Hsca | | | | | | | |]; subst.
    inversion Hscf as [| | | | | | | L1 e1 γ1 Hsce | | | | |]; subst.
    split; [exact HΓ |].
    apply SymScoped_Cast. apply SymScoped_App; [assumption | apply SymScoped_Cast; assumption].
  - destruct Hsc as [HΓ Hsc]. split; [exact HΓ |].
    destruct (sym_unspool_app_scoped S (dom_env Γ) (EApp e1 e2) [] (EIf ec et ef) args H Hsc
                (Forall_nil _)) as [Hif Hargs].
    inversion Hif as [| | | | | | | | | | L1 ec1 et1 ef1 Hscc Hsct Hscf | |]; subst.
    apply SymScoped_If;
      [exact Hscc | apply sym_scoped_fold_left_app; assumption
       | apply sym_scoped_fold_left_app; assumption].
  - destruct Hsc as [HΓ Hsc].
    inversion Hsc as [| | | | | | | | | | | | L1 Γ1 e1 HΓ' Hsce]; subst. split; assumption.
  - destruct Hsc as [HΓ Hsc]. inversion Hsc; subst. split; assumption.
  - destruct Hsc as [HΓ Hsc]. inversion Hsc; subst. split; assumption.
  - destruct Hsc as [HΓ Hsc]. inversion Hsc; subst. split; assumption.
  - destruct Hsc as [HΓ Hsc]. inversion Hsc; subst. split; assumption.
  - destruct Hsc as [HΓ Hsc].
    inversion Hsc as [| | | | | | L0 es1 alts1 Hsc_es Hsc_alts | | | | | |]; subst.
    pose proof (sym_eval_scoped_fix _ _ _ _ _ H S HΓ Hsc_es) as Hsc_es'.
    split; [exact HΓ |]. split; [| exact Hsc_alts].
    destruct es' as [ | | | | | | | | | | vc vt vf | | ]; simpl; try exact Hsc_es'.
    inversion Hsc_es' as [| | | | | | | | | | L1 vc1 vt1 vf1 Hvc Hvt Hvf | |]; subst.
    apply ite_sym_scoped; assumption.
  - destruct Hsc as [HΓ [Hm Halts]]. inversion Hm; subst. split; [exact HΓ | split; assumption].
  - destruct Hsc as [HΓ [Hm Halts]]. inversion Hm; subst. split; [exact HΓ | split; assumption].
  - destruct Hsc as [HΓ [Hm Halts]].
    assert (Hea : Forall (sym_scoped S (dom_env Γ)) ea).
    { pose proof (proj2 (sym_unspool_app_scoped S nil m [] (ECon d) ea
                    (decompose_con_app_unspool m d ea H) Hm (Forall_nil _))) as H1.
      eapply Forall_impl; [| exact H1]. intros a Ha. apply sym_scoped_nil_any. exact Ha. }
    split.
    + apply sym_scoped_env_extend_multi; [exact HΓ | exact HΓ | exact Hea].
    + rewrite dom_env_extend_multi.
      exact (sym_find_alt_scoped S (dom_env Γ) d alts xs ep Halts H0).
  - destruct Hsc as [HΓ [Hm Halts]]. split; [exact HΓ | split; [apply SymScoped_Con | exact Halts]].
  - destruct Hsc as [HΓ [Hm Halts]]. split; [exact HΓ | split; [apply SymScoped_Con | exact Halts]].
  - destruct Hsc as [HΓ [Hm Halts]]. split; [exact HΓ | split; [apply SymScoped_Con | exact Halts]].
Qed.

Inductive sym_reach : path_condition -> sym_state -> path_condition -> sym_state -> Prop :=
  | SymReach_Refl : forall Φ st, sym_reach Φ st Φ st
  | SymReach_Step : forall Φ st Φ1 st1 Φ2 st2,
      sym_step Φ st Φ1 st1 -> sym_reach Φ1 st1 Φ2 st2 -> sym_reach Φ st Φ2 st2.

Definition smt_terms_bounded (bs : nat) (Φ : path_condition) (Γ : environment) (e : expr) : Prop :=
  forall Φ' Γ' e' n v,
    sym_reach Φ (SEval Γ e) Φ' (SEval Γ' e') ->
    eval (Fin n) Φ' Γ' e' v ->
    smt_size (merge Γ' v) <= bs.

Definition smt_bounded_run (Φ : path_condition) (Γ : environment) (e : expr) : Prop :=
  exists bs, smt_terms_bounded bs Φ Γ e.

Definition sym_ok (S : symvars) (bs : nat) (Φ : path_condition) (st : sym_state) : Prop :=
  forall Φ' st', sym_reach Φ st Φ' st' ->
    sym_state_scoped S st' /\
    (forall Γ' e' n v, st' = SEval Γ' e' -> eval (Fin n) Φ' Γ' e' v ->
       smt_size (merge Γ' v) <= bs).

Lemma sym_ok_step : forall S bs Φ st Φ' st',
  sym_ok S bs Φ st -> sym_step Φ st Φ' st' -> sym_ok S bs Φ' st'.
Proof.
  intros S bs Φ st Φ' st' H Hstep Φ2 st2 Hreach.
  exact (H Φ2 st2 (SymReach_Step Φ st Φ' st' Φ2 st2 Hstep Hreach)).
Qed.

Lemma sym_ok_scoped : forall S bs Φ st, sym_ok S bs Φ st -> sym_state_scoped S st.
Proof. intros S bs Φ st H. exact (proj1 (H Φ st (SymReach_Refl Φ st))). Qed.

Lemma sym_ok_value_bound : forall S bs Φ Γ e n v,
  sym_ok S bs Φ (SEval Γ e) -> eval (Fin n) Φ Γ e v -> smt_size (merge Γ v) <= bs.
Proof.
  intros S bs Φ Γ e n v H Hev.
  exact (proj2 (H Φ (SEval Γ e) (SymReach_Refl Φ (SEval Γ e))) Γ e n v eq_refl Hev).
Qed.

Lemma sym_ok_intro : forall S bs Φ Γ e,
  symbolic_program S Γ e -> smt_terms_bounded bs Φ Γ e -> sym_ok S bs Φ (SEval Γ e).
Proof.
  intros S bs Φ Γ e [HΓ Hsc] Hb Φ' st' Hreach.
  assert (Hsc0 : sym_state_scoped S (SEval Γ e)) by (split; assumption).
  split.
  - clear Hb. revert Hsc0. induction Hreach as [| Φ0 st0 Φ1 st1 Φ2 st2 Hstep Hreach IH];
      intros Hsc0; [exact Hsc0 |].
    exact (IH (sym_step_scoped S Φ0 st0 Φ1 st1 Hsc0 Hstep)).
  - intros Γ' e' n v -> Hev. exact (Hb Φ' Γ' e' n v Hreach Hev).
Qed.

End SymReach.
