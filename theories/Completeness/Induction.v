From SymCoreTheory Require Export Completeness.SmtCost.
From Stdlib Require Import Bool.Bool Arith.Wf_nat Strings.String Lists.List Lia Arith.PeanoNat.
Import ListNotations.

Section Peel.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : SymFCCostLaws}.
Context (σ : valuation) (S : symvars).

Definition good_at (A : environment -> Prop) (e_c v_c : expr) (bk be bs : nat) : Prop :=
  exists h K, forall Γc Φ Γs e_s k kenv n v_s,
    A Γc -> k <= bk -> kenv <= be -> σ ⊨ Φ ->
    contains_env_k σ S kenv Γs Γc -> contains_k σ S k e_s e_c ->
    sym_ok S bs Φ (SEval Γs e_s) ->
    h <= n -> eval (Fin n) Φ Γs e_s v_s ->
    exists k', k' <= K /\ contains_k σ S k' v_s v_c.

Definition core_at (A : environment -> Prop) (e_c v_c : expr) (bk be bs : nat) : Prop :=
  exists h K, forall Γc Φ Γs e_s k kenv n v_s,
    A Γc -> k <= bk -> kenv <= be -> σ ⊨ Φ ->
    contains_env_k σ S kenv Γs Γc -> contains_k σ S k e_s e_c ->
    sym_ok S bs Φ (SEval Γs e_s) ->
    is_if (fst (unspool_app e_s [])) = false ->
    h <= n -> eval (Fin n) Φ Γs e_s v_s ->
    exists k', k' <= K /\ contains_k σ S k' v_s v_c.

Definition good (A : environment -> Prop) (e_c v_c : expr) : Prop :=
  forall bk be bs, good_at A e_c v_c bk be bs.

Lemma guard_true : forall Φ Γ g g' pc n,
  σ ⊨ Φ -> sym_free_env S Γ -> models_cond σ S g -> smt_size g < n ->
  eval (Fin n) Φ Γ g g' -> expr_to_pc Γ g' = Some pc ->
  σ ⊨ (Φ ∧ pc) /\ smt_size g' <= 2 * smt_size g /\ models_cond σ S g'.
Proof.
  intros Φ Γ g g' pc n Hm Hf Hc Hs Hev Hpc.
  destruct Hc as [pc0 [Hd Hv]].
  destruct (smt_eval_fin σ S Φ Γ n g g' (pc_value σ pc0) Hm Hf Hs
              (ex_intro _ pc0 (conj Hd eq_refl)) Hev) as [Hinf [Hsz _]].
  assert (Hc' : models_cond σ S g') by
    (eapply eval_models_cond; [exact Hm | exact Hf | exact Hinf | exists pc0; split; assumption]).
  split; [| split; assumption].
  apply models_and_iff. split; [exact Hm |]. exact (models_cond_pc σ S Γ g' pc Hpc Hc').
Qed.

Lemma guard_false : forall Φ Γ g g' pc n,
  σ ⊨ Φ -> sym_free_env S Γ -> models_not_cond σ S g -> smt_size g < n ->
  eval (Fin n) Φ Γ g g' -> expr_to_pc Γ g' = Some pc ->
  σ ⊨ (Φ ∧ ¬ pc) /\ smt_size g' <= 2 * smt_size g /\ models_not_cond σ S g'.
Proof.
  intros Φ Γ g g' pc n Hm Hf Hc Hs Hev Hpc.
  destruct Hc as [pc0 [Hd Hv]].
  destruct (smt_eval_fin σ S Φ Γ n g g' (pc_value σ pc0) Hm Hf Hs
              (ex_intro _ pc0 (conj Hd eq_refl)) Hev) as [Hinf [Hsz _]].
  assert (Hc' : models_not_cond σ S g') by
    (eapply eval_models_not_cond; [exact Hm | exact Hf | exact Hinf | exists pc0; split; assumption]).
  split; [| split; assumption].
  apply models_and_iff. split; [exact Hm |]. exact (models_not_cond_pc σ S Γ g' pc Hpc Hc').
Qed.

Lemma if_step_true : forall Φ Γ g t f v n,
  σ ⊨ Φ -> sym_free_env S Γ -> models_cond σ S g -> smt_size g < n ->
  eval (Fin (Datatypes.S n)) Φ Γ (EIf g t f) v ->
  exists g' t' f' pc, v = EIf g' t' f' /\ eval (Fin n) (Φ ∧ pc) Γ t t' /\
    σ ⊨ (Φ ∧ pc) /\ smt_size g' <= 2 * smt_size g /\ models_cond σ S g'.
Proof.
  intros Φ Γ g t f v n Hm Hf Hc Hs Hev.
  inversion Hev; subst; try sym_absurd; change (dec (Remaining n)) with (Fin n) in *.
  match goal with
  | [ Hg : eval _ _ _ g ?g0, Hpc : expr_to_pc _ ?g0 = Some ?pc0 |- _ ] =>
      destruct (guard_true Φ Γ g g0 pc0 n Hm Hf Hc Hs Hg Hpc) as [Hm' [Hsz Hc']]
  end.
  do 4 eexists. split; [reflexivity |]. split; [eassumption |].
  split; [exact Hm' | split; assumption].
Qed.

Lemma if_step_false : forall Φ Γ g t f v n,
  σ ⊨ Φ -> sym_free_env S Γ -> models_not_cond σ S g -> smt_size g < n ->
  eval (Fin (Datatypes.S n)) Φ Γ (EIf g t f) v ->
  exists g' t' f' pc, v = EIf g' t' f' /\ eval (Fin n) (Φ ∧ ¬ pc) Γ f f' /\
    σ ⊨ (Φ ∧ ¬ pc) /\ smt_size g' <= 2 * smt_size g /\ models_not_cond σ S g'.
Proof.
  intros Φ Γ g t f v n Hm Hf Hc Hs Hev.
  inversion Hev; subst; try sym_absurd; change (dec (Remaining n)) with (Fin n) in *.
  match goal with
  | [ Hg : eval _ _ _ g ?g0, Hpc : expr_to_pc _ ?g0 = Some ?pc0 |- _ ] =>
      destruct (guard_false Φ Γ g g0 pc0 n Hm Hf Hc Hs Hg Hpc) as [Hm' [Hsz Hc']]
  end.
  do 4 eexists. split; [reflexivity |]. split; [eassumption |].
  split; [exact Hm' | split; assumption].
Qed.

Lemma app_if_step : forall Φ Γ e1 e2 g t f args v n,
  σ ⊨ Φ ->
  unspool_app (EApp e1 e2) [] = (EIf g t f, args) ->
  eval (Fin (Datatypes.S n)) Φ Γ (EApp e1 e2) v ->
  eval (Fin n) Φ Γ (EIf g (fold_left EApp args t) (fold_left EApp args f)) v.
Proof.
  intros Φ Γ e1 e2 g t f args v n Hm Hu Hev.
  inversion Hev; subst; try sym_absurd; change (dec (Remaining n)) with (Fin n) in *.
  match goal with
  | [ Hu' : unspool_app (EApp e1 e2) [] = (EIf _ _ _, _), Hr : eval _ _ _ (EIf _ _ _) v |- _ ] =>
      rewrite Hu in Hu'; injection Hu' as <- <- <- <-; exact Hr
  end.
Qed.

Lemma good_at_of_core : forall A e_c v_c,
  (forall bk be bs, (forall bk', bk' < bk -> forall be' bs', good_at A e_c v_c bk' be' bs') ->
     core_at A e_c v_c bk be bs) ->
  good A e_c v_c.
Proof.
  intros A e_c v_c Hcore bk. induction bk as [bk IH] using lt_wf_ind. intros be bs.
  destruct (Hcore bk be bs IH) as [hc [Kc Hc]].
  assert (Hprev : exists h1 K1, forall Γc Φ Γs e_s k kenv n v_s,
    A Γc -> k < bk -> kenv <= be -> σ ⊨ Φ ->
    contains_env_k σ S kenv Γs Γc -> contains_k σ S k e_s e_c ->
    sym_ok S bs Φ (SEval Γs e_s) ->
    h1 <= n -> eval (Fin n) Φ Γs e_s v_s ->
    exists k', k' <= K1 /\ contains_k σ S k' v_s v_c).
  { destruct bk as [| bk'].
    - exists 0, 0. intros. lia.
    - destruct (IH bk' ltac:(lia) be bs) as [h1 [K1 H1]].
      exists h1, K1. intros Γc0 Φ0 Γs0 e0 k0 ke0 n0 v0 HA0 Hk0 Hke0 Hm0 He0 Hc0 Hok0 Hn0 Hev0.
      exact (H1 Γc0 Φ0 Γs0 e0 k0 ke0 n0 v0 HA0 ltac:(lia) Hke0 Hm0 He0 Hc0 Hok0 Hn0 Hev0). }
  destruct Hprev as [h1 [K1 H1]].
  exists (2 + bk + hc + h1), (1 + 2 * bk + Kc + K1).
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hok Hn Hev.
  pose proof (contains_env_k_sym_free _ _ _ _ _ Henv) as Hfree.
  destruct (is_if (fst (unspool_app e_s []))) eqn:Hif.
  2: { destruct (Hc Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hok Hif ltac:(lia) Hev)
         as [k' [Hk' Hc']].
       exists k'. split; [lia | exact Hc']. }
  destruct n as [| n]; [lia |].
  destruct e_s; simpl in Hif; try discriminate Hif.
  - change (unspool_app e_s1 [e_s2]) with (unspool_app (EApp e_s1 e_s2) []) in Hif.
    destruct (unspool_app (EApp e_s1 e_s2) []) as [hd args] eqn:Hu.
    simpl in Hif. destruct hd; simpl in Hif; try discriminate Hif.
    pose proof (app_if_step Φ Γs _ _ _ _ _ _ _ n Hm Hu Hev) as Hev1.
    pose proof (sym_ok_step S bs Φ _ Φ _ Hok (SymStep_AppIf Φ Γs e_s1 e_s2 _ _ _ args Hu)) as Hok1.
    destruct n as [| n]; [lia |].
    destruct (contains_k_app_if_spine σ S k _ _ _ _ _ args e_c Hcont Hu)
      as [k0 [Hk0 [[Hmc Harm] | [Hmc Harm]]]].
    + destruct (if_step_true Φ Γs _ _ _ v_s n Hm Hfree Hmc ltac:(lia) Hev1)
        as [g' [t' [f' [pc [-> [Ht [Hm' [Hsz Hc']]]]]]]].
      destruct (H1 Γc _ Γs _ k0 kenv n t' HA ltac:(lia) Hkenv Hm' Henv Harm
                  (sym_ok_step S bs Φ _ _ _ Hok1 (SymStep_IfTrue Φ Γs _ _ _ pc)) ltac:(lia) Ht)
        as [k' [Hk' Hc'']].
      exists (1 + smt_size g' + k'). split; [lia | apply ContK_If_True; assumption].
    + destruct (if_step_false Φ Γs _ _ _ v_s n Hm Hfree Hmc ltac:(lia) Hev1)
        as [g' [t' [f' [pc [-> [Ht [Hm' [Hsz Hc']]]]]]]].
      destruct (H1 Γc _ Γs _ k0 kenv n f' HA ltac:(lia) Hkenv Hm' Henv Harm
                  (sym_ok_step S bs Φ _ _ _ Hok1 (SymStep_IfFalse Φ Γs _ _ _ pc)) ltac:(lia) Ht)
        as [k' [Hk' Hc'']].
      exists (1 + smt_size g' + k'). split; [lia | apply ContK_If_False; assumption].
  - destruct (contains_k_if_inv σ S k _ _ _ e_c Hcont) as [k0 [Hk0 [[Hmc Harm] | [Hmc Harm]]]].
    + destruct (if_step_true Φ Γs _ _ _ v_s n Hm Hfree Hmc ltac:(lia) Hev)
        as [g' [t' [f' [pc [-> [Ht [Hm' [Hsz Hc']]]]]]]].
      destruct (H1 Γc _ Γs _ k0 kenv n t' HA ltac:(lia) Hkenv Hm' Henv Harm
                  (sym_ok_step S bs Φ _ _ _ Hok (SymStep_IfTrue Φ Γs _ _ _ pc)) ltac:(lia) Ht)
        as [k' [Hk' Hc'']].
      exists (1 + smt_size g' + k'). split; [lia | apply ContK_If_True; assumption].
    + destruct (if_step_false Φ Γs _ _ _ v_s n Hm Hfree Hmc ltac:(lia) Hev)
        as [g' [t' [f' [pc [-> [Ht [Hm' [Hsz Hc']]]]]]]].
      destruct (H1 Γc _ Γs _ k0 kenv n f' HA ltac:(lia) Hkenv Hm' Henv Harm
                  (sym_ok_step S bs Φ _ _ _ Hok (SymStep_IfFalse Φ Γs _ _ _ pc)) ltac:(lia) Ht)
        as [k' [Hk' Hc'']].
      exists (1 + smt_size g' + k'). split; [lia | apply ContK_If_False; assumption].
Qed.

End Peel.

Section NestedInduction.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.

Variables (P : fuel -> path_condition -> environment -> expr -> expr -> Prop)
          (Q : fuel -> path_condition -> environment -> expr -> list alt -> expr -> Prop).

Hypothesis HVar : forall f Φ Γ x Γ' e e',
  lookup_env Γ x = Some (Γ', e) -> eval (dec f) Φ Γ' e e' -> P (dec f) Φ Γ' e e' ->
  P (Live f) Φ Γ (EVar x) e'.
Hypothesis HSymVar : forall f Φ Γ x,
  lookup_env Γ x = None -> P (Live f) Φ Γ (EVar x) (EVar x).
Hypothesis HLit : forall f Φ Γ l, P (Live f) Φ Γ (ELit l) (ELit l).
Hypothesis HCon : forall f Φ Γ e d args,
  unspool_app e [] = (ECon d, args) ->
  P (Live f) Φ Γ e (make_con_app d (map (delay Γ) args)).
Hypothesis HCast : forall f Φ Γ e γ e',
  eval (dec f) Φ Γ e e' -> P (dec f) Φ Γ e e' ->
  P (Live f) Φ Γ (ECast e γ) (cast_expr e' γ).
Hypothesis HAppAbs : forall f Φ Γ Γ' x eb ea eb',
  eval (dec f) Φ (extend_env Γ' x Γ ea) eb eb' -> P (dec f) Φ (extend_env Γ' x Γ ea) eb eb' ->
  P (Live f) Φ Γ (EApp (EThunk Γ' (ELam x eb)) ea) eb'.
Hypothesis HAppSpine : forall f Φ Γ ef ea ef' er,
  Comp Γ ef ->
  eval (dec f) Φ Γ ef ef' -> P (dec f) Φ Γ ef ef' ->
  eval (dec f) Φ Γ (EApp ef' ea) er -> P (dec f) Φ Γ (EApp ef' ea) er ->
  P (Live f) Φ Γ (EApp ef ea) er.
Hypothesis HBot : forall f Φ Γ b, P (Live f) Φ Γ (EBot b) (EBot b).
Hypothesis HAppPrim : forall f Φ Γ ef ea p args args',
  unspool_app (EApp ef ea) [] = (EPrimOp p, args) ->
  length args = primop_arity p ->
  Forall2 (fun a a' => eval (dec f) Φ Γ a a' /\ P (dec f) Φ Γ a a') args args' ->
  P (Live f) Φ Γ (EApp ef ea) (reduce_prim p args').
Hypothesis HLam : forall f Φ Γ x e, P (Live f) Φ Γ (ELam x e) (EThunk Γ (ELam x e)).
Hypothesis HAppCast : forall f Φ Γ ef γ ea γ_a γ_r er,
  decomp_coerc_arrow γ = Some (γ_a, γ_r) ->
  eval (dec f) Φ Γ (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r) er ->
  P (dec f) Φ Γ (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r) er ->
  P (Live f) Φ Γ (EApp (ECast ef γ) ea) er.
Hypothesis HAppIf : forall f Φ Γ e1 e2 ec et ef args er,
  unspool_app (EApp e1 e2) [] = (EIf ec et ef, args) ->
  eval (dec f) Φ Γ (EIf ec (fold_left EApp args et) (fold_left EApp args ef)) er ->
  P (dec f) Φ Γ (EIf ec (fold_left EApp args et) (fold_left EApp args ef)) er ->
  P (Live f) Φ Γ (EApp e1 e2) er.
Hypothesis HAppBot : forall f Φ Γ b ea, P (Live f) Φ Γ (EApp (EBot b) ea) (EBot b).
Hypothesis HCase : forall f Φ Γ es alts es' er,
  eval (dec f) Φ Γ es es' -> P (dec f) Φ Γ es es' ->
  fold_alts (dec f) Φ Γ (merge Γ es') alts er -> Q (dec f) Φ Γ (merge Γ es') alts er ->
  P (Live f) Φ Γ (ECase es alts) er.
Hypothesis HIf : forall f Φ Γ ec et ef ec' et' ef' pc_c,
  eval (dec f) Φ Γ ec ec' -> P (dec f) Φ Γ ec ec' ->
  expr_to_pc Γ ec' = Some pc_c ->
  eval (dec f) (Φ ∧ pc_c) Γ et et' -> P (dec f) (Φ ∧ pc_c) Γ et et' ->
  eval (dec f) (Φ ∧ ¬ pc_c) Γ ef ef' -> P (dec f) (Φ ∧ ¬ pc_c) Γ ef ef' ->
  P (Live f) Φ Γ (EIf ec et ef) (EIf ec' et' ef').
Hypothesis HCoercion : forall f Φ Γ γ, P (Live f) Φ Γ (ECoercion γ) (ECoercion (subst_coerc Γ γ)).
Hypothesis HPrune : forall f Φ Γ e, sat Φ = false -> P (Live f) Φ Γ e (EBot BUnreachable).
Hypothesis HType : forall f Φ Γ τ, P (Live f) Φ Γ (EType τ) (EType (subst_type Γ τ)).
Hypothesis HThunk : forall f Φ Γ Γ' e e',
  eval (dec f) Φ Γ' e e' -> P (dec f) Φ Γ' e e' -> P (Live f) Φ Γ (EThunk Γ' e) e'.
Hypothesis HOutOfFuel : forall Φ Γ e, P Spent Φ Γ e (EBot BOutOfFuel).

Hypothesis HFIf : forall f Φ Γ ec et ef alts et' ef' pc_c,
  expr_to_pc Γ ec = Some pc_c ->
  fold_alts f (Φ ∧ pc_c) Γ et alts et' -> Q f (Φ ∧ pc_c) Γ et alts et' ->
  fold_alts f (Φ ∧ ¬ pc_c) Γ ef alts ef' -> Q f (Φ ∧ ¬ pc_c) Γ ef alts ef' ->
  Q f Φ Γ (EIf ec et ef) alts (EIf ec et' ef').
Hypothesis HFIfFail : forall f Φ Γ ec et ef alts,
  expr_to_pc Γ ec = None -> Q f Φ Γ (EIf ec et ef) alts (EBot BUndefined).
Hypothesis HFCon : forall f Φ Γ e d ea xs ep alts er,
  decompose_con_app e = Some (d, ea) ->
  find_alt d alts = Some (xs, ep) ->
  eval f Φ (extend_env_multi Γ xs ea Γ) ep er -> P f Φ (extend_env_multi Γ xs ea Γ) ep er ->
  Q f Φ Γ e alts er.
Hypothesis HFBot : forall f Φ Γ b alts, Q f Φ Γ (EBot b) alts (EBot b).
Hypothesis HFGroundFormula : forall f Φ Γ e pc alts r,
  expr_to_pc Γ e = Some pc ->
  pc_has_var pc = false ->
  fold_alts f Φ Γ (ECon (truth_constructor (pc_closed_value pc))) alts r ->
  Q f Φ Γ (ECon (truth_constructor (pc_closed_value pc))) alts r ->
  Q f Φ Γ e alts r.
Hypothesis HFSymbolicFormula : forall f Φ Γ e pc alts r1 r2,
  expr_to_pc Γ e = Some pc ->
  pc_has_var pc = true ->
  pc_arities_ok pc = true ->
  fold_alts f (Φ ∧ pc) Γ (ECon dcon_true) alts r1 ->
  Q f (Φ ∧ pc) Γ (ECon dcon_true) alts r1 ->
  fold_alts f (Φ ∧ ¬ pc) Γ (ECon dcon_false) alts r2 ->
  Q f (Φ ∧ ¬ pc) Γ (ECon dcon_false) alts r2 ->
  Q f Φ Γ e alts (EIf e r1 r2).
Hypothesis HFOtherwise : forall f Φ Γ e alts,
  expr_to_pc Γ e = None ->
  is_op_app e = false ->
  is_if (fst (unspool_app e [])) = false ->
  (match decompose_con_app e with
   | Some (d, _) => find_alt d alts = None
   | None => True
   end) ->
  is_bot e = false ->
  Q f Φ Γ e alts (EBot BUndefined).

Fixpoint eval_nested_ind f Φ Γ e v (H : eval f Φ Γ e v) {struct H} : P f Φ Γ e v :=
  match H in eval f Φ Γ e v return P f Φ Γ e v with
  | Eval_Var f Φ Γ x Γ' e e' Hl He => HVar f Φ Γ x Γ' e e' Hl He (eval_nested_ind _ _ _ _ _ He)
  | Eval_SymVar f Φ Γ x Hl => HSymVar f Φ Γ x Hl
  | Eval_Lit f Φ Γ l => HLit f Φ Γ l
  | Eval_Con f Φ Γ e d args Hu => HCon f Φ Γ e d args Hu
  | Eval_Cast f Φ Γ e γ e' He => HCast f Φ Γ e γ e' He (eval_nested_ind _ _ _ _ _ He)
  | Eval_AppAbs f Φ Γ Γ' x eb ea eb' He =>
      HAppAbs f Φ Γ Γ' x eb ea eb' He (eval_nested_ind _ _ _ _ _ He)
  | Eval_AppSpine f Φ Γ ef ea ef' er Hc H1 H2 =>
      HAppSpine f Φ Γ ef ea ef' er Hc H1 (eval_nested_ind _ _ _ _ _ H1)
        H2 (eval_nested_ind _ _ _ _ _ H2)
  | Eval_Bot f Φ Γ b => HBot f Φ Γ b
  | Eval_AppPrim f Φ Γ ef ea p args args' Hu Hl HF =>
      HAppPrim f Φ Γ ef ea p args args' Hu Hl
        ((fix go l l' (HF0 : Forall2 (eval (dec f) Φ Γ) l l') {struct HF0} :
            Forall2 (fun a a' => eval (dec f) Φ Γ a a' /\ P (dec f) Φ Γ a a') l l' :=
            match HF0 in Forall2 _ l l'
              return Forall2 (fun a a' => eval (dec f) Φ Γ a a' /\ P (dec f) Φ Γ a a') l l' with
            | @Forall2_nil _ _ _ => Forall2_nil _
            | @Forall2_cons _ _ _ a a' l0 l0' Ha HF1 =>
                Forall2_cons a a' (conj Ha (eval_nested_ind _ _ _ _ _ Ha)) (go l0 l0' HF1)
            end) args args' HF)
  | Eval_Lam f Φ Γ x e => HLam f Φ Γ x e
  | Eval_AppCast f Φ Γ ef γ ea γ_a γ_r er Hd He =>
      HAppCast f Φ Γ ef γ ea γ_a γ_r er Hd He (eval_nested_ind _ _ _ _ _ He)
  | Eval_AppIf f Φ Γ e1 e2 ec et ef args er Hu He =>
      HAppIf f Φ Γ e1 e2 ec et ef args er Hu He (eval_nested_ind _ _ _ _ _ He)
  | Eval_AppBot f Φ Γ b ea => HAppBot f Φ Γ b ea
  | Eval_Case f Φ Γ es alts es' er He Hf =>
      HCase f Φ Γ es alts es' er He (eval_nested_ind _ _ _ _ _ He) Hf (fold_nested_ind _ _ _ _ _ _ Hf)
  | Eval_If f Φ Γ ec et ef ec' et' ef' pc_c Hc Hp Ht Hf =>
      HIf f Φ Γ ec et ef ec' et' ef' pc_c Hc (eval_nested_ind _ _ _ _ _ Hc) Hp
        Ht (eval_nested_ind _ _ _ _ _ Ht) Hf (eval_nested_ind _ _ _ _ _ Hf)
  | Eval_Coercion f Φ Γ γ => HCoercion f Φ Γ γ
  | Eval_Prune f Φ Γ e Hs => HPrune f Φ Γ e Hs
  | Eval_Type f Φ Γ τ => HType f Φ Γ τ
  | Eval_Thunk f Φ Γ Γ' e e' He => HThunk f Φ Γ Γ' e e' He (eval_nested_ind _ _ _ _ _ He)
  | Eval_OutOfFuel Φ Γ e => HOutOfFuel Φ Γ e
  end
with fold_nested_ind f Φ Γ e alts v (H : fold_alts f Φ Γ e alts v) {struct H} : Q f Φ Γ e alts v :=
  match H in fold_alts f Φ Γ e alts v return Q f Φ Γ e alts v with
  | FoldAlts_If f Φ Γ ec et ef alts et' ef' pc_c Hp Ht Hf =>
      HFIf f Φ Γ ec et ef alts et' ef' pc_c Hp Ht (fold_nested_ind _ _ _ _ _ _ Ht)
        Hf (fold_nested_ind _ _ _ _ _ _ Hf)
  | FoldAlts_IfFail f Φ Γ ec et ef alts Hp => HFIfFail f Φ Γ ec et ef alts Hp
  | FoldAlts_Con f Φ Γ e d ea xs ep alts er Hd Hf He =>
      HFCon f Φ Γ e d ea xs ep alts er Hd Hf He (eval_nested_ind _ _ _ _ _ He)
  | FoldAlts_Bot f Φ Γ b alts => HFBot f Φ Γ b alts
  | FoldAlts_GroundFormula f Φ Γ e pc alts r Hp Hv Hr =>
      HFGroundFormula f Φ Γ e pc alts r Hp Hv Hr (fold_nested_ind _ _ _ _ _ _ Hr)
  | FoldAlts_SymbolicFormula f Φ Γ e pc alts r1 r2 Hp Hv Ha H1 H2 =>
      HFSymbolicFormula f Φ Γ e pc alts r1 r2 Hp Hv Ha
        H1 (fold_nested_ind _ _ _ _ _ _ H1) H2 (fold_nested_ind _ _ _ _ _ _ H2)
  | FoldAlts_Otherwise f Φ Γ e alts H1 H2 H3 H4 H5 =>
      HFOtherwise f Φ Γ e alts H1 H2 H3 H4 H5
  end.

End NestedInduction.

Section FoldPeel.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : SymFCCostLaws}.
Context (σ : valuation) (S : symvars).

Definition fgood_at (A : environment -> Prop) (esc : expr) (altsc : list alt) (v_c : expr)
  (bk be bs bm : nat) : Prop :=
  exists h K, forall Γc Φ Γs m altss k ks kenv n v_s,
    A Γc -> k <= bk -> kenv <= be -> list_sum ks <= be -> σ ⊨ Φ ->
    contains_env_k σ S kenv Γs Γc -> merge_keeps_k σ S k m esc ->
    Forall3 (contains_alt_k σ S) ks altss altsc ->
    smt_size m <= bm -> sym_ok S bs Φ (SFold Γs m altss) ->
    h <= n -> fold_alts (Fin n) Φ Γs m altss v_s ->
    exists k', k' <= K /\ contains_k σ S k' v_s v_c.

Definition fcore_at (A : environment -> Prop) (esc : expr) (altsc : list alt) (v_c : expr)
  (bk be bs bm : nat) : Prop :=
  exists h K, forall Γc Φ Γs m altss k ks kenv n v_s,
    A Γc -> k <= bk -> kenv <= be -> list_sum ks <= be -> σ ⊨ Φ ->
    contains_env_k σ S kenv Γs Γc -> merge_keeps_k σ S k m esc ->
    Forall3 (contains_alt_k σ S) ks altss altsc ->
    smt_size m <= bm -> sym_ok S bs Φ (SFold Γs m altss) ->
    is_if (fst (unspool_app m [])) = false ->
    h <= n -> fold_alts (Fin n) Φ Γs m altss v_s ->
    exists k', k' <= K /\ contains_k σ S k' v_s v_c.

Definition fgood (A : environment -> Prop) (esc : expr) (altsc : list alt) (v_c : expr) : Prop :=
  forall bk be bs bm, fgood_at A esc altsc v_c bk be bs bm.

Lemma models_cond_expr_to_pc : forall Γ g,
  sym_free_env S Γ -> models_cond σ S g \/ models_not_cond σ S g ->
  exists pc, expr_to_pc Γ g = Some pc.
Proof. intros Γ g Hf Hj. exact (models_cond_total σ S Γ g Hf Hj). Qed.

Lemma solvable_head_not_if : forall Γ e,
  Solvable Γ e -> is_if (fst (unspool_app e [])) = false.
Proof.
  intros Γ e Hs. destruct (unspool_app e []) as [hd args] eqn:Hu.
  simpl. destruct hd; try reflexivity.
  exfalso. exact (solvable_unspool_not_if Γ e [] _ _ _ _ Hs Hu).
Qed.

Lemma merge_keeps_k_head_not_if : forall k m esc,
  merge_keeps_k σ S k m esc ->
  (exists k', k' <= (1 + field_count esc) * k /\ contains_k σ S k' m esc)
  \/ is_if (fst (unspool_app m [])) = false.
Proof.
  intros k m esc [[k' [Hk' Hc]] | [Hsmt | [Hc _]]].
  - left. exists k'. split; assumption.
  - right. exact (solvable_head_not_if · m (smt_ite_kept_solvable σ S m esc
                    (smt_ite_kept_k_erase σ S k m esc Hsmt))).
  - right. destruct (is_cast_facts m Hc) as [_ [_ [Hh _]]]. exact Hh.
Qed.

Definition fpeel_at (A : environment -> Prop) (esc : expr) (altsc : list alt) (v_c : expr)
  (bk be bs : nat) : Prop :=
  exists h K, forall Γc Φ Γs m altss k ks kenv n v_s,
    A Γc -> k <= bk -> kenv <= be -> list_sum ks <= be -> σ ⊨ Φ ->
    contains_env_k σ S kenv Γs Γc -> contains_k σ S k m esc ->
    Forall3 (contains_alt_k σ S) ks altss altsc ->
    sym_ok S bs Φ (SFold Γs m altss) ->
    h <= n -> fold_alts (Fin n) Φ Γs m altss v_s ->
    exists k', k' <= K /\ contains_k σ S k' v_s v_c.

Lemma fpeel_of_core : forall A esc altsc v_c,
  (forall bk be bs bm, fcore_at A esc altsc v_c bk be bs bm) ->
  forall bk be bs, fpeel_at A esc altsc v_c bk be bs.
Proof.
  intros A esc altsc v_c Hcore bk. induction bk as [bk IH] using lt_wf_ind. intros be bs.
  destruct (Hcore bk be bs (bk + smt_size esc)) as [hc [Kc Hc]].
  assert (Hprev : exists h1 K1, forall Γc Φ Γs m altss k ks kenv n v_s,
    A Γc -> k < bk -> kenv <= be -> list_sum ks <= be -> σ ⊨ Φ ->
    contains_env_k σ S kenv Γs Γc -> contains_k σ S k m esc ->
    Forall3 (contains_alt_k σ S) ks altss altsc ->
    sym_ok S bs Φ (SFold Γs m altss) ->
    h1 <= n -> fold_alts (Fin n) Φ Γs m altss v_s ->
    exists k', k' <= K1 /\ contains_k σ S k' v_s v_c).
  { destruct bk as [| bk'].
    - exists 0, 0. intros. lia.
    - destruct (IH bk' ltac:(lia) be bs) as [h1 [K1 H1]].
      exists h1, K1.
      intros Γc0 Φ0 Γs0 m0 al0 k0 ks0 ke0 n0 v0 HA0 Hk0 Hke0 Hks0 Hm0 He0 Hc0 Ha0 Hok0 Hn0 Hev0.
      exact (H1 Γc0 Φ0 Γs0 m0 al0 k0 ks0 ke0 n0 v0 HA0 ltac:(lia) Hke0 Hks0 Hm0 He0 Hc0 Ha0 Hok0
               Hn0 Hev0). }
  destruct Hprev as [h1 [K1 H1]].
  exists (hc + h1), (1 + bk + Kc + K1).
  intros Γc Φ Γs m altss k ks kenv n v_s HA Hk Hkenv Hks Hm Henv Hcont Halts Hok Hn Hev.
  pose proof (contains_env_k_sym_free _ _ _ _ _ Henv) as Hfree.
  pose proof (smt_size_contains_k σ S k m esc Hcont) as Hszm.
  destruct (is_if (fst (unspool_app m []))) eqn:Hif.
  2: { destruct (Hc Γc Φ Γs m altss k ks kenv n v_s HA Hk Hkenv Hks Hm Henv
                   (merge_keeps_k_same σ S k m esc Hcont) Halts
                   ltac:(lia) Hok Hif
                   ltac:(lia) Hev) as [k' [Hk' Hc']].
       exists k'. split; [lia | exact Hc']. }
  destruct m; simpl in Hif; try discriminate Hif.
  - exfalso.
    change (unspool_app m1 [m2]) with (unspool_app (EApp m1 m2) []) in Hif.
    destruct (unspool_app (EApp m1 m2) []) as [hd args] eqn:Hu.
    simpl in Hif. destruct hd; simpl in Hif; try discriminate Hif.
    inversion Hev; subst.
    + match goal with [ Hd : decompose_con_app _ = Some _ |- _ ] =>
        unfold decompose_con_app in Hd; rewrite Hu in Hd; discriminate Hd end.
    + match goal with [ Hp : expr_to_pc _ (EApp _ _) = Some _ |- _ ] =>
        exact (solvable_unspool_not_if Γs (EApp m1 m2) [] _ _ _ _
                 (expr_to_pc_solvable Γs _ _ Hp) Hu) end.
    + match goal with [ Hp : expr_to_pc _ (EApp _ _) = Some _ |- _ ] =>
        exact (solvable_unspool_not_if Γs (EApp m1 m2) [] _ _ _ _
                 (expr_to_pc_solvable Γs _ _ Hp) Hu) end.
    + match goal with [ Hi : is_if (fst (unspool_app _ _)) = false |- _ ] =>
        rewrite Hu in Hi; simpl in Hi; discriminate Hi end.
  - destruct (contains_k_if_inv σ S k _ _ _ esc Hcont) as [k0 [Hk0 [[Hmc Harm] | [Hmc Harm]]]].
    + inversion Hev; subst.
      * match goal with [ Hp : expr_to_pc _ m1 = Some ?pc, Ht : fold_alts _ (Φ ∧ ?pc) _ m2 _ ?t' |- _ ] =>
          assert (Hm' : σ ⊨ (Φ ∧ pc))
            by (apply models_and_iff; split; [exact Hm | exact (models_cond_pc σ S Γs m1 pc Hp Hmc)]);
          destruct (H1 Γc _ Γs m2 altss k0 ks kenv n t' HA ltac:(lia) Hkenv Hks Hm' Henv Harm Halts
                      (sym_ok_step S bs Φ _ _ _ Hok (SymStep_FoldIfTrue Φ Γs m1 m2 m3 altss pc))
                      ltac:(lia) Ht) as [k' [Hk' Hc']];
          exists (1 + smt_size m1 + k'); split; [lia | apply ContK_If_True; assumption]
        end.
      * exfalso. destruct (models_cond_expr_to_pc Γs m1 Hfree (or_introl Hmc)) as [pc Hpc]. congruence.
      * exfalso. match goal with [ Hd : decompose_con_app _ = Some _ |- _ ] => discriminate Hd end.
      * exfalso. match goal with [ Hp : expr_to_pc _ (EIf _ _ _) = Some _ |- _ ] =>
          simpl in Hp; discriminate Hp end.
      * exfalso. match goal with [ Hp : expr_to_pc _ (EIf _ _ _) = Some _ |- _ ] =>
          simpl in Hp; discriminate Hp end.
      * exfalso. match goal with [ Hi : is_if _ = false |- _ ] => discriminate Hi end.
    + inversion Hev; subst.
      * match goal with [ Hp : expr_to_pc _ m1 = Some ?pc, Ht : fold_alts _ (Φ ∧ ¬ ?pc) _ m3 _ ?t' |- _ ] =>
          assert (Hm' : σ ⊨ (Φ ∧ ¬ pc))
            by (apply models_and_iff; split; [exact Hm | exact (models_not_cond_pc σ S Γs m1 pc Hp Hmc)]);
          destruct (H1 Γc _ Γs m3 altss k0 ks kenv n t' HA ltac:(lia) Hkenv Hks Hm' Henv Harm Halts
                      (sym_ok_step S bs Φ _ _ _ Hok (SymStep_FoldIfFalse Φ Γs m1 m2 m3 altss pc))
                      ltac:(lia) Ht) as [k' [Hk' Hc']];
          exists (1 + smt_size m1 + k'); split; [lia | apply ContK_If_False; assumption]
        end.
      * exfalso. destruct (models_cond_expr_to_pc Γs m1 Hfree (or_intror Hmc)) as [pc Hpc]. congruence.
      * exfalso. match goal with [ Hd : decompose_con_app _ = Some _ |- _ ] => discriminate Hd end.
      * exfalso. match goal with [ Hp : expr_to_pc _ (EIf _ _ _) = Some _ |- _ ] =>
          simpl in Hp; discriminate Hp end.
      * exfalso. match goal with [ Hp : expr_to_pc _ (EIf _ _ _) = Some _ |- _ ] =>
          simpl in Hp; discriminate Hp end.
      * exfalso. match goal with [ Hi : is_if _ = false |- _ ] => discriminate Hi end.
Qed.

Lemma fgood_of_core : forall A esc altsc v_c,
  (forall bk be bs bm, fcore_at A esc altsc v_c bk be bs bm) -> fgood A esc altsc v_c.
Proof.
  intros A esc altsc v_c Hcore bk be bs bm.
  destruct (Hcore bk be bs bm) as [hc [Kc Hc]].
  destruct (fpeel_of_core A esc altsc v_c Hcore ((1 + field_count esc) * bk) be bs)
    as [hp [Kp Hp]].
  exists (hc + hp), (Kc + Kp).
  intros Γc Φ Γs m altss k ks kenv n v_s HA Hk Hkenv Hks Hm Henv Hmk Halts Hsz Hok Hn Hev.
  destruct (merge_keeps_k_head_not_if k m esc Hmk) as [[k0 [Hk0 Hc0]] | Hif].
  - destruct (Hp Γc Φ Γs m altss k0 ks kenv n v_s HA ltac:(nia) Hkenv Hks Hm Henv Hc0 Halts Hok
                ltac:(lia) Hev) as [k' [Hk' Hc']].
    exists k'. split; [lia | exact Hc'].
  - destruct (Hc Γc Φ Γs m altss k ks kenv n v_s HA Hk Hkenv Hks Hm Henv Hmk Halts Hsz Hok Hif
                ltac:(lia) Hev) as [k' [Hk' Hc']].
    exists k'. split; [lia | exact Hc'].
Qed.

End FoldPeel.
