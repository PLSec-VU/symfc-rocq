From SymCoreTheory Require Import SymCore ConCore CostLaws.
From Stdlib Require Import Bool.Bool Arith.Wf_nat.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.PeanoNat.
Import ListNotations.

Section Completeness.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : ConCoreLaws}.

Definition target_completeness : Prop :=
  forall Φ Γs Γc σ S e_sym e_con v_con,
    σ ⊨ Φ ->
    contains_env σ S Γs Γc ->
    contains σ S e_sym e_con ->
    concore_expr e_con ->
    closed_program Γc e_con ->
    budget_total Φ Γs e_sym ->
    Γc ⊢ᶜ e_con ⇓ᶜ v_con ->
    exists h, forall n, (h <= n)%nat ->
      exists v_sym, eval (Fin n) Φ Γs e_sym v_sym /\ contains σ S v_sym v_con.

Definition forall_form_lemma : Prop :=
  forall Γc e_con v_con,
    Γc ⊢ᶜ e_con ⇓ᶜ v_con ->
    forall Φ Γs σ S e_sym,
      σ ⊨ Φ ->
      contains_env σ S Γs Γc ->
      contains σ S e_sym e_con ->
      concore_expr e_con ->
      closed_program Γc e_con ->
      exists h, forall n, (h <= n)%nat ->
        forall v_sym, eval (Fin n) Φ Γs e_sym v_sym -> contains σ S v_sym v_con.

Definition existential_corollary : Prop :=
  forall Φ Γs Γc σ S e_sym e_con v_con,
    σ ⊨ Φ ->
    contains_env σ S Γs Γc ->
    contains σ S e_sym e_con ->
    concore_expr e_con ->
    closed_program Γc e_con ->
    budget_total Φ Γs e_sym ->
    Γc ⊢ᶜ e_con ⇓ᶜ v_con ->
    exists k v_sym, eval (Fin k) Φ Γs e_sym v_sym /\ contains σ S v_sym v_con.

Lemma existential_corollary_of_target :
  target_completeness -> existential_corollary.
Proof.
  intros Htarget Φ Γs Γc σ S e_sym e_con v_con Hmod Henv Hcont Hcon Hcl Hbud Hevalc.
  destruct (Htarget Φ Γs Γc σ S e_sym e_con v_con Hmod Henv Hcont Hcon Hcl Hbud Hevalc)
    as [h Hh].
  destruct (Hh h ltac:(lia)) as [v_sym [Heval Hcv]].
  exists h, v_sym. split; assumption.
Qed.

Section BudgetTotalIsNecessary.
  Variables (Φ : path_condition) (σ : valuation) (S : symvars).
  Variables (x : var) (l l' : lit).

  Hypothesis Hsat  : sat Φ = true.
  Hypothesis Hfeas : sat (Φ ∧ ¬ PCVar x) = true.
  Hypothesis Hsx   : S x = true.
  Hypothesis Hmodx : σ ⊨ PCVar x.

  Definition necessity_stuck_arm : expr := EApp (ELit l) (ELit l).
  Definition necessity_program : expr := EIf (EVar x) (ELit l') necessity_stuck_arm.

  Lemma necessity_no_value_at_large_budget : forall k v,
    ~ eval (Fin (Datatypes.S (Datatypes.S k))) Φ · necessity_program v.
  Proof.
    intros k v Hv. unfold necessity_program in Hv.
    inversion Hv as [| | | | | | | | | | | | | | kf Φ0 Γ0 ec0 et0 ef0 ec' et' ef' pc_c
                       Hc Hpc Ht Hf | | kf Φ0 Γ0 e0 Hunsat | | |]; subst.
    - no_con_head.
    - assert (Hec : ec' = EVar x)
        by (eapply eval_symvar_fin_same with (k := k) (Γ := ·);
            [reflexivity | exact Hsat | exact Hc]).
      subst ec'. simpl in Hpc. injection Hpc as Hpc. subst pc_c.
      unfold necessity_stuck_arm in Hf.
      eapply app_lit_no_value_fin; [exact Hfeas | exact Hf].
    - rewrite Hsat in Hunsat. discriminate.
  Qed.

  Theorem budget_total_fails_on_stuck_arm : ~ budget_total Φ · necessity_program.
  Proof.
    intros [h Hh].
    destruct (Hh (Datatypes.S (Datatypes.S h)) ltac:(lia)) as [v Hv].
    exact (necessity_no_value_at_large_budget h v Hv).
  Qed.

  Theorem stuck_arm_concrete_instance_terminates :
    · ⊢ᶜ ELit l' ⇓ᶜ ELit l' /\ contains σ S necessity_program (ELit l').
  Proof.
    split.
    - apply Eval_Lit.
    - apply Cont_If_True; [| apply Cont_Lit].
      exists (PCVar x). split; [| exact Hmodx].
      intros Γ Hfree. simpl. rewrite (Hfree x Hsx). reflexivity.
  Qed.

End BudgetTotalIsNecessary.

Section LoopingArmUnderCase.
  Variables (Φ : path_condition) (σ : valuation) (S : symvars).
  Variables (x : var) (l' : lit).

  Hypothesis HmodPhi : σ ⊨ Φ.
  Hypothesis Hsx     : S x = true.
  Hypothesis Hmodx   : σ ⊨ PCVar x.
  Hypothesis Hsf     : S self_app_var = false.

  Definition case_alts : list alt :=
    Alt "T" [] (ELit l') :: Alt "F" [] self_app :: nil.
  Definition case_sym : expr := ECase (EIf (EVar x) (ECon "T") (ECon "F")) case_alts.
  Definition case_con : expr := ECase (ECon "T") case_alts.

  Lemma case_guard_cond : models_cond σ S (EVar x).
  Proof.
    exists (PCVar x). split; [| exact Hmodx].
    intros Γ Hfree. simpl. rewrite (Hfree x Hsx). reflexivity.
  Qed.

  Lemma case_alts_contains : Forall2 (contains_alt σ S) case_alts case_alts.
  Proof.
    apply Forall2_cons; [| apply Forall2_cons; [| apply Forall2_nil]].
    - apply Cont_Alt; [apply Forall_nil | apply Cont_Lit].
    - apply Cont_Alt; [apply Forall_nil |].
      unfold self_app, self_app_fun, self_app_body.
      apply Cont_App; (apply Cont_Lam; [exact Hsf |]);
        (apply Cont_App; apply Cont_Var_Bound; exact Hsf).
  Qed.

  Lemma case_contains : contains σ S case_sym case_con.
  Proof.
    apply Cont_Case; [| exact case_alts_contains].
    apply Cont_If_True; [exact case_guard_cond | apply Cont_Con].
  Qed.

  Lemma case_con_concore : concore_expr case_con.
  Proof.
    apply Con_Case; [apply Con_Con |].
    apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
    - apply Con_Alt. apply Con_Lit.
    - apply Con_Alt. unfold self_app, self_app_fun, self_app_body.
      apply Con_App; apply Con_Lam; apply Con_App; apply Con_Var.
  Qed.

  Lemma case_con_converges : Φ ; · ⊢ case_con ⇓ (ELit l').
  Proof.
    unfold case_con.
    eapply Eval_Case.
    - eapply Eval_Con. reflexivity.
    - simpl. eapply FoldAlts_Con.
      + reflexivity.
      + simpl. destruct (string_dec "T" "T"); [reflexivity | congruence].
      + simpl. apply Eval_Lit.
  Qed.

  Lemma case_budget_total : budget_total Φ · case_sym.
  Proof.
    exists 3%nat. intros n Hn. destruct n as [| [| [| m]]]; [lia | lia | lia |].
    destruct (self_app_has_value_at_every_budget (Datatypes.S (Datatypes.S m))
                (Φ ∧ ¬ PCVar x) ·) as [vf Hvf].
    exists (EIf (EVar x) (ELit l') vf).
    unfold case_sym.
    eapply Eval_Case.
    - eapply Eval_If with (pc_c := PCVar x).
      + apply Eval_SymVar. reflexivity.
      + reflexivity.
      + eapply Eval_Con. reflexivity.
      + eapply Eval_Con. reflexivity.
    - simpl. eapply FoldAlts_If.
      + reflexivity.
      + simpl. eapply FoldAlts_Con.
        * reflexivity.
        * simpl. destruct (string_dec "T" "T"); [reflexivity | congruence].
        * simpl. apply Eval_Lit.
      + simpl. eapply FoldAlts_Con.
        * reflexivity.
        * simpl. destruct (string_dec "F" "T"); [congruence |].
          simpl. destruct (string_dec "F" "F"); [reflexivity | congruence].
        * simpl. exact Hvf.
  Qed.

  Theorem case_target_conclusion :
    exists h, forall n, (h <= n)%nat ->
      exists v_sym, eval (Fin n) Φ · case_sym v_sym /\ contains σ S v_sym (ELit l').
  Proof.
    exists 3%nat. intros n Hn. destruct n as [| [| [| m]]]; [lia | lia | lia |].
    destruct (self_app_has_value_at_every_budget (Datatypes.S (Datatypes.S m))
                (Φ ∧ ¬ PCVar x) ·) as [vf Hvf].
    exists (EIf (EVar x) (ELit l') vf). split.
    - unfold case_sym.
      eapply Eval_Case.
      + eapply Eval_If with (pc_c := PCVar x).
        * apply Eval_SymVar. reflexivity.
        * reflexivity.
        * eapply Eval_Con. reflexivity.
        * eapply Eval_Con. reflexivity.
      + simpl. eapply FoldAlts_If.
        * reflexivity.
        * simpl. eapply FoldAlts_Con.
          -- reflexivity.
          -- simpl. destruct (string_dec "T" "T"); [reflexivity | congruence].
          -- simpl. apply Eval_Lit.
        * simpl. eapply FoldAlts_Con.
          -- reflexivity.
          -- simpl. destruct (string_dec "F" "T"); [congruence |].
             simpl. destruct (string_dec "F" "F"); [reflexivity | congruence].
          -- simpl. exact Hvf.
    - apply Cont_If_True; [exact case_guard_cond | apply Cont_Lit].
  Qed.

End LoopingArmUnderCase.

Section AppliedCaseWithBranchScrutinee.
  Variables (Φ : path_condition) (σ : valuation) (S : symvars).
  Variables (x : var) (la : lit).

  Hypothesis HmodPhi : σ ⊨ Φ.
  Hypothesis Hsx     : S x = true.
  Hypothesis Hmodx   : σ ⊨ PCVar x.
  Hypothesis Hsy     : S "y" = false.
  Hypothesis Hsz     : S "z" = false.

  Definition app_alts : list alt :=
    Alt "T" [] (ELam "y" (EVar "y")) :: Alt "F" [] (ELam "z" (EVar "z")) :: nil.
  Definition app_case : expr := ECase (EIf (EVar x) (ECon "T") (ECon "F")) app_alts.
  Definition app_sym : expr := EApp app_case (ELit la).
  Definition app_case_con : expr := ECase (ECon "T") app_alts.
  Definition app_con : expr := EApp app_case_con (ELit la).

  Lemma app_guard_cond : models_cond σ S (EVar x).
  Proof.
    exists (PCVar x). split; [| exact Hmodx].
    intros Γ Hfree. simpl. rewrite (Hfree x Hsx). reflexivity.
  Qed.

  Lemma app_alts_contains : Forall2 (contains_alt σ S) app_alts app_alts.
  Proof.
    apply Forall2_cons; [| apply Forall2_cons; [| apply Forall2_nil]].
    - apply Cont_Alt; [apply Forall_nil |].
      apply Cont_Lam; [exact Hsy | apply Cont_Var_Bound; exact Hsy].
    - apply Cont_Alt; [apply Forall_nil |].
      apply Cont_Lam; [exact Hsz | apply Cont_Var_Bound; exact Hsz].
  Qed.

  Lemma app_contains : contains σ S app_sym app_con.
  Proof.
    apply Cont_App; [| apply Cont_Lit].
    apply Cont_Case; [| exact app_alts_contains].
    apply Cont_If_True; [exact app_guard_cond | apply Cont_Con].
  Qed.

  Lemma app_con_concore : concore_expr app_con.
  Proof.
    apply Con_App; [| apply Con_Lit].
    apply Con_Case; [apply Con_Con |].
    apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]];
      apply Con_Alt; apply Con_Lam; apply Con_Var.
  Qed.

  Lemma app_con_converges : Φ ; · ⊢ app_con ⇓ (ELit la).
  Proof.
    unfold app_con, app_case_con.
    eapply Eval_AppSpine.
    - apply Comp_Case.
    - eapply Eval_Case.
      + eapply Eval_Con. reflexivity.
      + simpl. eapply FoldAlts_Con.
        * reflexivity.
        * simpl. destruct (string_dec "T" "T"); [reflexivity | congruence].
        * simpl. apply Eval_Lam.
    - eapply Eval_AppAbs. simpl.
      eapply Eval_Var.
      + simpl. destruct (string_dec "y" "y"); [reflexivity | congruence].
      + apply Eval_Lit.
  Qed.

  Lemma app_sym_converges : Φ ; · ⊢ app_sym ⇓ (EIf (EVar x) (ELit la) (ELit la)).
  Proof.
    unfold app_sym, app_case.
    eapply Eval_AppSpine.
    - apply Comp_Case.
    - eapply Eval_Case.
      + eapply Eval_If with (pc_c := PCVar x).
        * apply Eval_SymVar. reflexivity.
        * reflexivity.
        * eapply Eval_Con. reflexivity.
        * eapply Eval_Con. reflexivity.
      + simpl. eapply FoldAlts_If.
        * reflexivity.
        * simpl. eapply FoldAlts_Con.
          -- reflexivity.
          -- simpl. destruct (string_dec "T" "T"); [reflexivity | congruence].
          -- simpl. apply Eval_Lam.
        * simpl. eapply FoldAlts_Con.
          -- reflexivity.
          -- simpl. destruct (string_dec "F" "T"); [congruence |].
             simpl. destruct (string_dec "F" "F"); [reflexivity | congruence].
          -- simpl. apply Eval_Lam.
    - eapply Eval_AppIf.
      + reflexivity.
      + simpl. eapply Eval_If with (pc_c := PCVar x).
        * apply Eval_SymVar. reflexivity.
        * reflexivity.
        * eapply Eval_AppAbs. simpl. eapply Eval_Var.
          -- simpl. destruct (string_dec "y" "y"); [reflexivity | congruence].
          -- apply Eval_Lit.
        * eapply Eval_AppAbs. simpl. eapply Eval_Var.
          -- simpl. destruct (string_dec "z" "z"); [reflexivity | congruence].
          -- apply Eval_Lit.
  Qed.

  Lemma app_budget_total : budget_total Φ · app_sym.
  Proof.
    apply budget_total_of_terminating. exists (EIf (EVar x) (ELit la) (ELit la)).
    exact app_sym_converges.
  Qed.

  Theorem app_target_conclusion :
    exists h, forall n, (h <= n)%nat ->
      exists v_sym, eval (Fin n) Φ · app_sym v_sym /\ contains σ S v_sym (ELit la).
  Proof.
    destruct (eval_inf_has_budget Φ · app_sym (EIf (EVar x) (ELit la) (ELit la))
                app_sym_converges) as [h Hh].
    exists h. intros n Hn. exists (EIf (EVar x) (ELit la) (ELit la)). split.
    - apply Hh. exact Hn.
    - apply Cont_If_True; [exact app_guard_cond | apply Cont_Lit].
  Qed.

End AppliedCaseWithBranchScrutinee.

End Completeness.

Section CostBasics.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : SymFCCostLaws}.

Lemma contains_env_k_sym_free : forall σ S k Γs Γc,
  contains_env_k σ S k Γs Γc -> sym_free_env S Γs.
Proof.
  intros σ S k Γs Γc H.
  exact (proj1 (contains_env_sym_free σ S Γs Γc (contains_env_k_erase _ _ _ _ _ H))).
Qed.

Lemma contains_env_k_concrete : forall σ S k Γs Γc,
  contains_env_k σ S k Γs Γc -> concrete_env Γc.
Proof.
  intros σ S k Γs Γc H.
  exact (contains_env_concrete σ S Γs Γc (contains_env_k_erase _ _ _ _ _ H)).
Qed.

Lemma contains_env_k_lookup : forall σ S k Γs Γc x Γs' es,
  contains_env_k σ S k Γs Γc ->
  lookup_env Γs x = Some (Γs', es) ->
  exists Γc' ec k1 k2,
    lookup_env Γc x = Some (Γc', ec) /\ contains_env_k σ S k1 Γs' Γc' /\
    contains_k σ S k2 es ec /\ k1 <= k /\ k2 <= k.
Proof.
  intros σ S k Γs Γc x Γs' es H. revert Γs' es.
  induction H as [| kenv ke krest y Γ1 Γ2 e1 e2 r1 r2 Hy Henv _ He Hc Hrest IH];
    intros Γs' es Hl; simpl in Hl; [discriminate |].
  simpl. destruct (string_dec x y).
  - injection Hl as <- <-. exists Γ2, e2, kenv, ke. repeat split; try assumption; lia.
  - destruct (IH Γs' es Hl) as [Γc' [ec [k1 [k2 [Hlc [H1 [H2 [Hk1 Hk2]]]]]]]].
    exists Γc', ec, k1, k2. repeat split; try assumption; lia.
Qed.

Lemma delay_contains_k : forall σ S kenv k Γs Γc es ec,
  contains_env_k σ S kenv Γs Γc ->
  contains_k σ S k es ec ->
  exists k', k' <= 1 + kenv + k /\ contains_k σ S k' (delay Γs es) (delay Γc ec).
Proof.
  intros σ S kenv k Γs Γc es ec Henv Hc.
  destruct (is_thunk es) eqn:Hs; destruct (is_thunk ec) eqn:Hcc.
  - rewrite (delay_thunk Γs es Hs), (delay_thunk Γc ec Hcc). exists k. split; [lia | exact Hc].
  - exfalso. destruct es; try discriminate Hs.
    inversion Hc; subst; simpl in *; congruence.
  - rewrite (delay_not_thunk Γs es Hs), (delay_thunk Γc ec Hcc).
    exists (1 + kenv + k). split; [lia |]. exact (ContK_Thunk_Outer σ S kenv k Γs Γc es ec Henv Hc Hcc).
  - rewrite (delay_not_thunk Γs es Hs), (delay_not_thunk Γc ec Hcc).
    exists (kenv + k). split; [lia |]. apply ContK_Thunk; assumption.
Qed.

Lemma delay_map_contains_k : forall σ S kenv Γs Γc ks args_s args_c,
  contains_env_k σ S kenv Γs Γc ->
  Forall3 (contains_k σ S) ks args_s args_c ->
  exists ks', list_sum ks' <= length ks * (1 + kenv) + list_sum ks /\
    Forall3 (contains_k σ S) ks' (map (delay Γs) args_s) (map (delay Γc) args_c).
Proof.
  intros σ S kenv Γs Γc ks args_s args_c Henv HF.
  induction HF as [| k a_s a_c ks l1 l2 Ha _ IH].
  - exists nil. split; [simpl; lia | constructor].
  - destruct IH as [ks' [Hs HF']].
    destruct (delay_contains_k σ S kenv k Γs Γc a_s a_c Henv Ha) as [k' [Hk' Hd]].
    exists (k' :: ks'). split; [simpl in *; lia | constructor; assumption].
Qed.

Lemma contains_k_spine_if : forall σ S k e_sym e_con,
  contains_k σ S k e_sym e_con ->
  forall ks L_s L_c,
    Forall3 (contains_k σ S) ks L_s L_c ->
    forall ec et ef args,
      unspool_app e_sym L_s = (EIf ec et ef, args) ->
      exists kh ks' head_c args_c,
        fold_left EApp L_c e_con = fold_left EApp args_c head_c /\
        contains_k σ S kh (EIf ec et ef) head_c /\
        Forall3 (contains_k σ S) ks' args args_c /\
        kh + list_sum ks' = k + list_sum ks.
Proof.
  induction 1; intros kl L_s L_c HL ec0 et0 ef0 args0 Hunspool; simpl in Hunspool;
    try discriminate Hunspool.
  - destruct (IHcontains_k1 (ka :: kl) (a_s :: L_s) (a_c :: L_c)
                (Forall3_cons _ _ _ _ _ _ _ H0 HL) _ _ _ _ Hunspool)
      as [kh [ks' [hc [ac [Heq [Hh [HF Hs]]]]]]].
    exists kh, ks', hc, ac. split; [exact Heq | split; [exact Hh | split; [exact HF | simpl in Hs; lia]]].
  - injection Hunspool as Hc Ht Hf Hargs. subst.
    exists (1 + smt_size ec0 + k), kl, etc, L_c.
    split; [reflexivity | split; [apply ContK_If_True; assumption | split; [exact HL | lia]]].
  - injection Hunspool as Hc Ht Hf Hargs. subst.
    exists (1 + smt_size ec0 + k), kl, efc, L_c.
    split; [reflexivity | split; [apply ContK_If_False; assumption | split; [exact HL | lia]]].
  - exfalso.
    apply (unspool_app_shift es [] L_s) in H. simpl in H.
    rewrite H in Hunspool. discriminate Hunspool.
Qed.

Lemma contains_k_app_if_spine : forall σ S k e1 e2 ec et ef args e_con,
  contains_k σ S k (EApp e1 e2) e_con ->
  unspool_app (EApp e1 e2) [] = (EIf ec et ef, args) ->
  exists k0, k = 1 + smt_size ec + k0 /\
    ((models_cond σ S ec /\ contains_k σ S k0 (fold_left EApp args et) e_con) \/
     (models_not_cond σ S ec /\ contains_k σ S k0 (fold_left EApp args ef) e_con)).
Proof.
  intros σ S k e1 e2 ec et ef args e_con Hc Hu.
  destruct (contains_k_spine_if σ S k _ _ Hc nil nil nil (Forall3_nil _) ec et ef args Hu)
    as [kh [ks' [hc [ac [Heq [Hh [HF Hs]]]]]]].
  simpl in Heq, Hs. rewrite Heq.
  destruct (contains_k_if_inv σ S kh ec et ef hc Hh) as [k0 [-> [[Hm Ht] | [Hm Hf]]]].
  - exists (k0 + list_sum ks'). split; [lia |]. left. split; [exact Hm |].
    exact (contains_k_fold_left_app σ S ks' _ _ k0 _ _ HF Ht).
  - exists (k0 + list_sum ks'). split; [lia |]. right. split; [exact Hm |].
    exact (contains_k_fold_left_app σ S ks' _ _ k0 _ _ HF Hf).
Qed.

End CostBasics.

Section SmtCost.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : SymFCCostLaws}.

Lemma unspool_smt_size : forall e L h args,
  unspool_app e L = (h, args) ->
  smt_size e + list_sum (map smt_size L) + length L =
  smt_size h + list_sum (map smt_size args) + length args.
Proof.
  induction e; intros L h args Hu; simpl in Hu;
    try (injection Hu as <- <-; reflexivity).
  apply IHe1 in Hu. simpl in *. lia.
Qed.

Lemma prim_slack_literals : forall ls,
  prim_slack (map ELit ls) = 1 + length ls + length ls.
Proof.
  intros ls. unfold prim_slack. rewrite length_map.
  assert (H : list_sum (map ground_size (map ELit ls)) = length ls).
  { induction ls as [| l ls IH]; simpl; [reflexivity |]. rewrite IH. reflexivity. }
  rewrite H. reflexivity.
Qed.

Lemma reduce_prim_literals_literal : forall p ls,
  exists l0, reduce_prim p (map ELit ls) = ELit l0.
Proof.
  intros p ls.
  apply reduce_prim_ground_value.
  apply solvable_everywhere_smt_ground. intros Γ.
  set (σ0 := fun _ : var => lit_true).
  set (S0 := fun _ : var => false).
  assert (Hargs : Forall2 (denote σ0 S0) (map ELit ls) ls).
  { induction ls as [| l ls IH]; simpl; constructor; [apply denote_lit | exact IH]. }
  destruct (reduce_prim_denote σ0 S0 p (map ELit ls) ls Hargs) as [pc [Hden _]].
  apply (expr_to_pc_solvable Γ _ pc). apply Hden.
  intros x Hx. discriminate Hx.
Qed.

Lemma solvable_value_contains_k : forall σ S Γ v l p args,
  Solvable Γ v ->
  denote σ S v l ->
  (v = ELit l \/ (exists x, v = EVar x) \/ v = reduce_prim p args) ->
  exists kv, kv <= smt_size v /\ contains_k σ S kv v (ELit l).
Proof.
  intros σ S Γ v l p args Hs Hden Hshape.
  destruct (smt_ground v) eqn:Hg.
  - exists 0. split; [lia |].
    destruct Hshape as [-> | [[x ->] | Hr]]; [apply ContK_Lit | simpl in Hg; discriminate |].
    rewrite Hr in Hg. destruct (reduce_prim_ground_value p args Hg) as [l' Hl'].
    rewrite Hr, Hl' in *. rewrite (denote_lit_inv σ S l' l Hden). apply ContK_Lit.
  - inversion Hs as [l' | x Hx | p0 | f a Hop Hf Ha]; subst.
    + simpl in Hg. discriminate.
    + destruct (denote_var_inv σ S x l Hden) as [Hsx ->].
      exists 0. split; [lia |]. apply ContK_Var_Sym. exact Hsx.
    + simpl in Hg. discriminate.
    + destruct (is_op_app_unspool (EApp f a) Hop) as [p0 [args0 Hu]].
      exists (smt_size (EApp f a)). split; [lia |].
      destruct Hshape as [Heq | [[x Heq] | Hr]]; try discriminate Heq.
      apply ContK_Denote with (p := p0) (args := args0); [exact Hu | | exact Hg | exact Hden].
      rewrite Hr in Hu. exact (reduce_prim_saturated p args p0 args0 Hu).
Qed.

Lemma denote_unspool_args : forall σ S e l p args,
  denote σ S e l -> unspool_app e [] = (EPrimOp p, args) ->
  exists ls, Forall2 (denote σ S) args ls.
Proof.
  intros σ S e l p args [pc [Hden _]] Hu.
  destruct e; simpl in Hu; try discriminate Hu.
  - injection Hu as _ <-. exists nil. constructor.
  - destruct (denotes_app_inv S e1 e2 pc Hden) as [p1 [pcs1 [pa [-> _]]]].
    destruct (denotes_unspool (EApp e1 e2) S p1 (pcs1 ++ [pa]) p args Hden Hu) as [_ HF].
    exists (map (pc_value σ) (pcs1 ++ [pa])).
    clear Hu Hden. induction HF; simpl; constructor; [| exact IHHF].
    exists y. split; [exact H | reflexivity].
Qed.

Definition smt_good σ S Φ Γ (e v : expr) (l : lit) : Prop :=
  eval Inf Φ Γ e v /\ smt_size v <= 2 * smt_size e /\
  exists kv, kv <= 2 * smt_size e /\ contains_k σ S kv v (ELit l).

Lemma smt_args_eval : forall σ S Φ Γ n args args' ls,
  (forall e v l, smt_size e < n -> denote σ S e l -> eval (Fin n) Φ Γ e v -> smt_good σ S Φ Γ e v l) ->
  Forall (fun a => smt_size a < n) args ->
  Forall2 (denote σ S) args ls ->
  Forall2 (eval (Fin n) Φ Γ) args args' ->
  Forall2 (eval Inf Φ Γ) args args' /\
  exists ks, Forall3 (contains_k σ S) ks args' (map ELit ls) /\
    list_sum ks <= 2 * list_sum (map smt_size args).
Proof.
  intros σ S Φ Γ n args args' ls IH Hsz Hden Hev. revert ls Hden Hsz.
  induction Hev as [| a a' l1 l2 Ha _ IHl]; intros ls Hden Hsz.
  - inversion Hden; subst. split; [constructor | exists nil; split; [constructor | simpl; lia]].
  - inversion Hden as [| a0 l0 l1' ls' Hd Hds]; subst.
    inversion Hsz as [| a1 l1'' Hs Hss]; subst.
    destruct (IH a a' l0 Hs Hd Ha) as [Hinf [_ [kv [Hkv Hc]]]].
    destruct (IHl ls' Hds Hss) as [Hinfs [ks [HF Hks]]].
    split; [constructor; assumption |].
    exists (kv :: ks). split; [constructor; assumption | simpl; lia].
Qed.

Lemma unspool_args_smaller : forall e p args,
  unspool_app e [] = (EPrimOp p, args) ->
  smt_size e = 1 + list_sum (map smt_size args) + length args.
Proof.
  intros e p args Hu. apply unspool_smt_size in Hu. simpl in Hu. lia.
Qed.

Lemma list_sum_map_le : forall (f : expr -> nat) l a,
  In a l -> f a <= list_sum (map f l).
Proof.
  intros f l a Hin. induction l as [| b l IH]; [destruct Hin |].
  destruct Hin as [-> | Hin]; simpl; [lia | specialize (IH Hin); lia].
Qed.

Lemma smt_eval_fin : forall σ S Φ Γ n e v l,
  σ ⊨ Φ -> sym_free_env S Γ -> smt_size e < n -> denote σ S e l ->
  eval (Fin n) Φ Γ e v -> smt_good σ S Φ Γ e v l.
Proof.
  intros σ S Φ Γ n. induction n as [| n IHn]; intros e v l Hmod Hfree Hsz Hden Hev; [lia |].
  assert (Hsolv : Solvable Γ e).
  { destruct Hden as [pc [Hd _]]. exact (expr_to_pc_solvable Γ e pc (Hd Γ Hfree)). }
  inversion Hev; subst;
    try solve [exfalso; inversion Hsolv; subst; simpl in *; congruence].
  - match goal with [Hn : lookup_env _ _ = None |- _] =>
      split; [apply Eval_SymVar; exact Hn | split; [simpl; lia |]] end.
    destruct (denote_var_inv σ S x l Hden) as [Hsx ->].
    exists 0. split; [lia | apply ContK_Var_Sym; exact Hsx].
  - rewrite <- (denote_lit_inv σ S l0 l Hden).
    split; [apply Eval_Lit | split; [simpl; lia | exists 0; split; [lia | apply ContK_Lit]]].
  - exfalso.
    match goal with [Hu : unspool_app _ _ = (ECon _, _) |- _] => apply unspool_is_con_app in Hu end.
    rewrite (solvable_not_con_app Γ e Hsolv) in *. discriminate.
  - exfalso. inversion Hsolv; subst.
    match goal with [Hc : Comp _ ?f, Hs : Solvable _ ?f |- _] => exact (comp_not_solvable _ _ Hc Hs) end.
  - match goal with
    | [ Hu : unspool_app (EApp ef ea) [] = (EPrimOp p, ?a),
        Hl : length ?a = primop_arity p,
        Hargs : Forall2 _ ?a args' |- _ ] => rename a into args; rename Hu into Hun;
                                             rename Hargs into Hev_args
    end.
    destruct (denote_unspool_args σ S _ l p args Hden Hun) as [ls Hls].
    pose proof (unspool_args_smaller _ _ _ Hun) as Hse.
    assert (Hsizes : Forall (fun a => smt_size a < n) args).
    { apply Forall_forall. intros a Ha.
      pose proof (list_sum_map_le smt_size args a Ha). lia. }
    change (dec (Remaining n)) with (Fin n) in Hev_args.
    destruct (smt_args_eval σ S Φ Γ n args args' ls
                (fun e v l Hs Hd Hv => IHn e v l Hmod Hfree Hs Hd Hv) Hsizes Hls Hev_args)
      as [Hinf [ks [HF Hks]]].
    assert (Hevinf : eval Inf Φ Γ (EApp ef ea) (reduce_prim p args'))
      by (eapply Eval_AppPrim; eassumption).
    split; [exact Hevinf |].
    destruct (reduce_prim_contains_k σ S p ks args' (map ELit ls) (closed_term_lits ls) HF) as [k' [Hk' Hc']].
    destruct (reduce_prim_literals_literal p ls) as [l0 Hl0]. rewrite Hl0 in Hc'.
    pose proof (smt_size_contains_k _ _ _ _ _ Hc') as Hsv. simpl in Hsv.
    rewrite prim_slack_literals in Hk'.
    pose proof (Forall2_length Hls) as Hlen.
    assert (Hsize : smt_size (reduce_prim p args') <= 2 * smt_size (EApp ef ea)) by lia.
    split; [exact Hsize |].
    pose proof (eval_denote Φ Γ σ S _ _ l Hmod Hfree Hevinf Hden) as Hden'.
    pose proof (solvable_eval_solvable Inf Φ Γ _ _ Hevinf eq_refl (models_sat σ Φ Hmod) Hsolv) as Hsv'.
    destruct (solvable_value_contains_k σ S Γ _ l p args' Hsv' Hden'
                (or_intror (or_intror eq_refl))) as [kv [Hkv Hcv]].
    exists kv. split; [lia | exact Hcv].
  - exfalso.
    match goal with
    | [ Hu : unspool_app (EApp _ _) _ = (EIf _ _ _, _) |- _ ] =>
        exact (solvable_unspool_not_if _ _ _ _ _ _ _ Hsolv Hu)
    end.
  - exfalso. apply models_sat in Hmod. congruence.
Qed.

End SmtCost.

Ltac sym_absurd :=
  first
  [ match goal with [ Hs : sat _ = false, Hm : models _ _ |- _ ] =>
      apply models_sat in Hm; congruence end
  | match goal with [ H : unspool_app _ _ = _ |- _ ] => simpl in H; discriminate H end
  | congruence
  | match goal with [ Hc : Comp _ ?f, Hu : unspool_app (EApp ?f ?a) nil = _ |- _ ] =>
      pose proof (comp_spine_head _ _ _ _ _ Hc Hu) as Hsh; simpl in *; discriminate end
  | match goal with [ Hc : Comp _ _ |- _ ] => inversion Hc; subst; simpl in *; discriminate end ].

Section Peel.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : SymFCCostLaws}.
Context (σ : valuation) (S : symvars).

Definition good_at (A : environment -> Prop) (e_c v_c : expr) (bk be : nat) : Prop :=
  exists h K, forall Γc Φ Γs e_s k kenv n v_s,
    A Γc -> k <= bk -> kenv <= be -> σ ⊨ Φ ->
    contains_env_k σ S kenv Γs Γc -> contains_k σ S k e_s e_c ->
    h <= n -> eval (Fin n) Φ Γs e_s v_s ->
    exists k', k' <= K /\ contains_k σ S k' v_s v_c.

Definition core_at (A : environment -> Prop) (e_c v_c : expr) (bk be : nat) : Prop :=
  exists h K, forall Γc Φ Γs e_s k kenv n v_s,
    A Γc -> k <= bk -> kenv <= be -> σ ⊨ Φ ->
    contains_env_k σ S kenv Γs Γc -> contains_k σ S k e_s e_c ->
    is_if (fst (unspool_app e_s [])) = false ->
    h <= n -> eval (Fin n) Φ Γs e_s v_s ->
    exists k', k' <= K /\ contains_k σ S k' v_s v_c.

Definition good (A : environment -> Prop) (e_c v_c : expr) : Prop :=
  forall bk be, good_at A e_c v_c bk be.

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
  (forall bk be, (forall bk', bk' < bk -> forall be', good_at A e_c v_c bk' be') ->
     core_at A e_c v_c bk be) ->
  good A e_c v_c.
Proof.
  intros A e_c v_c Hcore bk. induction bk as [bk IH] using lt_wf_ind. intros be.
  destruct (Hcore bk be IH) as [hc [Kc Hc]].
  assert (Hprev : exists h1 K1, forall Γc Φ Γs e_s k kenv n v_s,
    A Γc -> k < bk -> kenv <= be -> σ ⊨ Φ ->
    contains_env_k σ S kenv Γs Γc -> contains_k σ S k e_s e_c ->
    h1 <= n -> eval (Fin n) Φ Γs e_s v_s ->
    exists k', k' <= K1 /\ contains_k σ S k' v_s v_c).
  { destruct bk as [| bk'].
    - exists 0, 0. intros. lia.
    - destruct (IH bk' ltac:(lia) be) as [h1 [K1 H1]].
      exists h1, K1. intros Γc0 Φ0 Γs0 e0 k0 ke0 n0 v0 HA0 Hk0 Hke0 Hm0 He0 Hc0 Hn0 Hev0.
      exact (H1 Γc0 Φ0 Γs0 e0 k0 ke0 n0 v0 HA0 ltac:(lia) Hke0 Hm0 He0 Hc0 Hn0 Hev0). }
  destruct Hprev as [h1 [K1 H1]].
  exists (2 + bk + hc + h1), (1 + 2 * bk + Kc + K1).
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hn Hev.
  pose proof (contains_env_k_sym_free _ _ _ _ _ Henv) as Hfree.
  destruct (is_if (fst (unspool_app e_s []))) eqn:Hif.
  2: { destruct (Hc Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hif ltac:(lia) Hev)
         as [k' [Hk' Hc']].
       exists k'. split; [lia | exact Hc']. }
  destruct n as [| n]; [lia |].
  destruct e_s; simpl in Hif; try discriminate Hif.
  - change (unspool_app e_s1 [e_s2]) with (unspool_app (EApp e_s1 e_s2) []) in Hif.
    destruct (unspool_app (EApp e_s1 e_s2) []) as [hd args] eqn:Hu.
    simpl in Hif. destruct hd; simpl in Hif; try discriminate Hif.
    pose proof (app_if_step Φ Γs _ _ _ _ _ _ _ n Hm Hu Hev) as Hev1.
    destruct n as [| n]; [lia |].
    destruct (contains_k_app_if_spine σ S k _ _ _ _ _ args e_c Hcont Hu)
      as [k0 [Hk0 [[Hmc Harm] | [Hmc Harm]]]].
    + destruct (if_step_true Φ Γs _ _ _ v_s n Hm Hfree Hmc ltac:(lia) Hev1)
        as [g' [t' [f' [pc [-> [Ht [Hm' [Hsz Hc']]]]]]]].
      destruct (H1 Γc _ Γs _ k0 kenv n t' HA ltac:(lia) Hkenv Hm' Henv Harm ltac:(lia) Ht)
        as [k' [Hk' Hc'']].
      exists (1 + smt_size g' + k'). split; [lia | apply ContK_If_True; assumption].
    + destruct (if_step_false Φ Γs _ _ _ v_s n Hm Hfree Hmc ltac:(lia) Hev1)
        as [g' [t' [f' [pc [-> [Ht [Hm' [Hsz Hc']]]]]]]].
      destruct (H1 Γc _ Γs _ k0 kenv n f' HA ltac:(lia) Hkenv Hm' Henv Harm ltac:(lia) Ht)
        as [k' [Hk' Hc'']].
      exists (1 + smt_size g' + k'). split; [lia | apply ContK_If_False; assumption].
  - destruct (contains_k_if_inv σ S k _ _ _ e_c Hcont) as [k0 [Hk0 [[Hmc Harm] | [Hmc Harm]]]].
    + destruct (if_step_true Φ Γs _ _ _ v_s n Hm Hfree Hmc ltac:(lia) Hev)
        as [g' [t' [f' [pc [-> [Ht [Hm' [Hsz Hc']]]]]]]].
      destruct (H1 Γc _ Γs _ k0 kenv n t' HA ltac:(lia) Hkenv Hm' Henv Harm ltac:(lia) Ht)
        as [k' [Hk' Hc'']].
      exists (1 + smt_size g' + k'). split; [lia | apply ContK_If_True; assumption].
    + destruct (if_step_false Φ Γs _ _ _ v_s n Hm Hfree Hmc ltac:(lia) Hev)
        as [g' [t' [f' [pc [-> [Ht [Hm' [Hsz Hc']]]]]]]].
      destruct (H1 Γc _ Γs _ k0 kenv n f' HA ltac:(lia) Hkenv Hm' Henv Harm ltac:(lia) Ht)
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
Hypothesis HFOtherwise : forall f Φ Γ e alts,
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
  | FoldAlts_Otherwise f Φ Γ e alts H1 H2 H3 => HFOtherwise f Φ Γ e alts H1 H2 H3
  end.

End NestedInduction.

Section FoldPeel.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : SymFCCostLaws}.
Context (σ : valuation) (S : symvars).

Definition fgood_at (A : environment -> Prop) (esc : expr) (altsc : list alt) (v_c : expr)
  (bk be : nat) : Prop :=
  exists h K, forall Γc Φ Γs m altss k ks kenv n v_s,
    A Γc -> k <= bk -> kenv <= be -> list_sum ks <= be -> σ ⊨ Φ ->
    contains_env_k σ S kenv Γs Γc -> contains_k σ S k m esc ->
    Forall3 (contains_alt_k σ S) ks altss altsc ->
    h <= n -> fold_alts (Fin n) Φ Γs m altss v_s ->
    exists k', k' <= K /\ contains_k σ S k' v_s v_c.

Definition fcore_at (A : environment -> Prop) (esc : expr) (altsc : list alt) (v_c : expr)
  (bk be : nat) : Prop :=
  exists h K, forall Γc Φ Γs m altss k ks kenv n v_s,
    A Γc -> k <= bk -> kenv <= be -> list_sum ks <= be -> σ ⊨ Φ ->
    contains_env_k σ S kenv Γs Γc -> contains_k σ S k m esc ->
    Forall3 (contains_alt_k σ S) ks altss altsc ->
    is_if (fst (unspool_app m [])) = false ->
    h <= n -> fold_alts (Fin n) Φ Γs m altss v_s ->
    exists k', k' <= K /\ contains_k σ S k' v_s v_c.

Definition fgood (A : environment -> Prop) (esc : expr) (altsc : list alt) (v_c : expr) : Prop :=
  forall bk be, fgood_at A esc altsc v_c bk be.

Lemma models_cond_expr_to_pc : forall Γ g,
  sym_free_env S Γ -> models_cond σ S g \/ models_not_cond σ S g ->
  exists pc, expr_to_pc Γ g = Some pc.
Proof. intros Γ g Hf Hj. exact (models_cond_total σ S Γ g Hf Hj). Qed.

Lemma fgood_of_core : forall A esc altsc v_c,
  (forall bk be, (forall bk', bk' < bk -> forall be', fgood_at A esc altsc v_c bk' be') ->
     fcore_at A esc altsc v_c bk be) ->
  fgood A esc altsc v_c.
Proof.
  intros A esc altsc v_c Hcore bk. induction bk as [bk IH] using lt_wf_ind. intros be.
  destruct (Hcore bk be IH) as [hc [Kc Hc]].
  assert (Hprev : exists h1 K1, forall Γc Φ Γs m altss k ks kenv n v_s,
    A Γc -> k < bk -> kenv <= be -> list_sum ks <= be -> σ ⊨ Φ ->
    contains_env_k σ S kenv Γs Γc -> contains_k σ S k m esc ->
    Forall3 (contains_alt_k σ S) ks altss altsc ->
    h1 <= n -> fold_alts (Fin n) Φ Γs m altss v_s ->
    exists k', k' <= K1 /\ contains_k σ S k' v_s v_c).
  { destruct bk as [| bk'].
    - exists 0, 0. intros. lia.
    - destruct (IH bk' ltac:(lia) be) as [h1 [K1 H1]].
      exists h1, K1. intros Γc0 Φ0 Γs0 m0 al0 k0 ks0 ke0 n0 v0 HA0 Hk0 Hke0 Hks0 Hm0 He0 Hc0 Ha0 Hn0 Hev0.
      exact (H1 Γc0 Φ0 Γs0 m0 al0 k0 ks0 ke0 n0 v0 HA0 ltac:(lia) Hke0 Hks0 Hm0 He0 Hc0 Ha0 Hn0 Hev0). }
  destruct Hprev as [h1 [K1 H1]].
  exists (hc + h1), (1 + bk + Kc + K1).
  intros Γc Φ Γs m altss k ks kenv n v_s HA Hk Hkenv Hks Hm Henv Hcont Halts Hn Hev.
  pose proof (contains_env_k_sym_free _ _ _ _ _ Henv) as Hfree.
  destruct (is_if (fst (unspool_app m []))) eqn:Hif.
  2: { destruct (Hc Γc Φ Γs m altss k ks kenv n v_s HA Hk Hkenv Hks Hm Henv Hcont Halts Hif
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
    + match goal with [ Hi : is_if (fst (unspool_app _ _)) = false |- _ ] =>
        rewrite Hu in Hi; simpl in Hi; discriminate Hi end.
  - destruct (contains_k_if_inv σ S k _ _ _ esc Hcont) as [k0 [Hk0 [[Hmc Harm] | [Hmc Harm]]]].
    + inversion Hev; subst.
      * match goal with [ Hp : expr_to_pc _ m1 = Some ?pc, Ht : fold_alts _ (Φ ∧ ?pc) _ m2 _ ?t' |- _ ] =>
          assert (Hm' : σ ⊨ (Φ ∧ pc))
            by (apply models_and_iff; split; [exact Hm | exact (models_cond_pc σ S Γs m1 pc Hp Hmc)]);
          destruct (H1 Γc _ Γs m2 altss k0 ks kenv n t' HA ltac:(lia) Hkenv Hks Hm' Henv Harm Halts
                      ltac:(lia) Ht) as [k' [Hk' Hc']];
          exists (1 + smt_size m1 + k'); split; [lia | apply ContK_If_True; assumption]
        end.
      * exfalso. destruct (models_cond_expr_to_pc Γs m1 Hfree (or_introl Hmc)) as [pc Hpc]. congruence.
      * exfalso. match goal with [ Hd : decompose_con_app _ = Some _ |- _ ] => discriminate Hd end.
      * exfalso. match goal with [ Hi : is_if _ = false |- _ ] => discriminate Hi end.
    + inversion Hev; subst.
      * match goal with [ Hp : expr_to_pc _ m1 = Some ?pc, Ht : fold_alts _ (Φ ∧ ¬ ?pc) _ m3 _ ?t' |- _ ] =>
          assert (Hm' : σ ⊨ (Φ ∧ ¬ pc))
            by (apply models_and_iff; split; [exact Hm | exact (models_not_cond_pc σ S Γs m1 pc Hp Hmc)]);
          destruct (H1 Γc _ Γs m3 altss k0 ks kenv n t' HA ltac:(lia) Hkenv Hks Hm' Henv Harm Halts
                      ltac:(lia) Ht) as [k' [Hk' Hc']];
          exists (1 + smt_size m1 + k'); split; [lia | apply ContK_If_False; assumption]
        end.
      * exfalso. destruct (models_cond_expr_to_pc Γs m1 Hfree (or_intror Hmc)) as [pc Hpc]. congruence.
      * exfalso. match goal with [ Hd : decompose_con_app _ = Some _ |- _ ] => discriminate Hd end.
      * exfalso. match goal with [ Hi : is_if _ = false |- _ ] => discriminate Hi end.
Qed.

End FoldPeel.

Section Closures.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : SymFCCostLaws}.
Context (σ : valuation) (S : symvars).

Inductive clos_tree (C : expr) : nat -> expr -> Prop :=
  | CT_Leaf : forall k Γ x e,
      contains_k σ S k (EThunk Γ (ELam x e)) C -> clos_tree C k (EThunk Γ (ELam x e))
  | CT_True : forall k g t f,
      models_cond σ S g -> clos_tree C k t -> clos_tree C (1 + smt_size g + k) (EIf g t f)
  | CT_False : forall k g t f,
      models_not_cond σ S g -> clos_tree C k f -> clos_tree C (1 + smt_size g + k) (EIf g t f).

Lemma lam_body_value : forall Γc x ec bk be, exists h K,
  forall Φ Γs es k kenv n v,
    k <= bk -> kenv <= be -> σ ⊨ Φ ->
    contains_env_k σ S kenv Γs Γc -> contains_k σ S k es (ELam x ec) ->
    h <= n -> eval (Fin n) Φ Γs es v ->
    exists k', k' <= K /\ clos_tree (EThunk Γc (ELam x ec)) k' v.
Proof.
  intros Γc x ec bk. induction bk as [bk IH] using lt_wf_ind. intros be.
  assert (Hprev : exists h1 K1, forall Φ Γs es k kenv n v,
    k < bk -> kenv <= be -> σ ⊨ Φ ->
    contains_env_k σ S kenv Γs Γc -> contains_k σ S k es (ELam x ec) ->
    h1 <= n -> eval (Fin n) Φ Γs es v ->
    exists k', k' <= K1 /\ clos_tree (EThunk Γc (ELam x ec)) k' v).
  { destruct bk as [| bk'].
    - exists 0, 0. intros. lia.
    - destruct (IH bk' ltac:(lia) be) as [h1 [K1 H1]].
      exists h1, K1. intros Φ0 Γs0 es0 k0 ke0 n0 v0 Hk0 Hke0 Hm0 He0 Hc0 Hn0 Hev0.
      exact (H1 Φ0 Γs0 es0 k0 ke0 n0 v0 ltac:(lia) Hke0 Hm0 He0 Hc0 Hn0 Hev0). }
  destruct Hprev as [h1 [K1 H1]].
  exists (2 + bk + h1), (1 + be + 2 * bk + K1).
  intros Φ Γs es k kenv n v Hk Hkenv Hm Henv Hcont Hn Hev.
  pose proof (contains_env_k_sym_free _ _ _ _ _ Henv) as Hfree.
  destruct n as [| n]; [lia |].
  inversion Hcont; subst; try (match goal with [ Ht : is_thunk _ = true |- _ ] => simpl in Ht; discriminate Ht end).
  - inversion Hev; subst; try sym_absurd.
    exists (kenv + k). split; [lia |].
    apply CT_Leaf. apply ContK_Thunk; [exact Henv | apply ContK_Lam; assumption].
  - destruct (if_step_true σ S Φ Γs _ _ _ v n Hm Hfree ltac:(eassumption) ltac:(lia) Hev)
      as [g' [t' [f' [pc [-> [Ht [Hm' [Hsz Hc']]]]]]]].
    destruct (H1 _ Γs _ k0 kenv n t' ltac:(lia) Hkenv Hm' Henv ltac:(eassumption) ltac:(lia) Ht)
      as [k' [Hk' Hct]].
    exists (1 + smt_size g' + k'). split; [lia | apply CT_True; assumption].
  - destruct (if_step_false σ S Φ Γs _ _ _ v n Hm Hfree ltac:(eassumption) ltac:(lia) Hev)
      as [g' [t' [f' [pc [-> [Ht [Hm' [Hsz Hc']]]]]]]].
    destruct (H1 _ Γs _ k0 kenv n f' ltac:(lia) Hkenv Hm' Henv ltac:(eassumption) ltac:(lia) Ht)
      as [k' [Hk' Hct]].
    exists (1 + smt_size g' + k'). split; [lia | apply CT_False; assumption].
Qed.

Lemma clos_value : forall Γc x ec bk, exists h K,
  forall Φ Γs es k n v,
    k <= bk -> σ ⊨ Φ -> sym_free_env S Γs ->
    contains_k σ S k es (EThunk Γc (ELam x ec)) ->
    h <= n -> eval (Fin n) Φ Γs es v ->
    exists k', k' <= K /\ clos_tree (EThunk Γc (ELam x ec)) k' v.
Proof.
  intros Γc x ec bk. induction bk as [bk IH] using lt_wf_ind.
  assert (Hprev : exists h1 K1, forall Φ Γs es k n v,
    k < bk -> σ ⊨ Φ -> sym_free_env S Γs ->
    contains_k σ S k es (EThunk Γc (ELam x ec)) ->
    h1 <= n -> eval (Fin n) Φ Γs es v ->
    exists k', k' <= K1 /\ clos_tree (EThunk Γc (ELam x ec)) k' v).
  { destruct bk as [| bk'].
    - exists 0, 0. intros. lia.
    - destruct (IH bk' ltac:(lia)) as [h1 [K1 H1]].
      exists h1, K1. intros Φ0 Γs0 es0 k0 n0 v0 Hk0 Hm0 Hf0 Hc0 Hn0 Hev0.
      exact (H1 Φ0 Γs0 es0 k0 n0 v0 ltac:(lia) Hm0 Hf0 Hc0 Hn0 Hev0). }
  destruct Hprev as [h1 [K1 H1]].
  destruct (lam_body_value Γc x ec bk bk) as [hl [Kl Hl]].
  exists (2 + bk + h1 + hl), (1 + 2 * bk + K1 + Kl).
  intros Φ Γs es k n v Hk Hm Hfree Hcont Hn Hev.
  destruct n as [| n]; [lia |].
  inversion Hcont; subst.
  - inversion Hev; subst; try sym_absurd.
    change (dec (Remaining n)) with (Fin n) in *.
    match goal with
    | [ He : contains_env_k _ _ ?ke ?G _, Hb : contains_k _ _ ?kb ?b (ELam _ _),
        Hv : eval (Fin n) _ ?G ?b v |- _ ] =>
        destruct (Hl Φ G b kb ke n v ltac:(lia) ltac:(lia) Hm He Hb ltac:(lia) Hv) as [k' [Hk' Hct]]
    end.
    exists k'. split; [lia | exact Hct].
  - inversion Hev; subst; try sym_absurd.
    change (dec (Remaining n)) with (Fin n) in *.
    match goal with
    | [ He : contains_env_k _ _ ?ke ?G _, Hb : contains_k _ _ ?kb ?b (EThunk _ _),
        Hv : eval (Fin n) _ ?G ?b v |- _ ] =>
        destruct (H1 Φ G b kb n v ltac:(lia) Hm (contains_env_k_sym_free _ _ _ _ _ He) Hb ltac:(lia) Hv)
          as [k' [Hk' Hct]]
    end.
    exists k'. split; [lia | exact Hct].
  - destruct (if_step_true σ S Φ Γs _ _ _ v n Hm Hfree ltac:(eassumption) ltac:(lia) Hev)
      as [g' [t' [f' [pc [-> [Ht [Hm' [Hsz Hc']]]]]]]].
    destruct (H1 _ Γs _ k0 n t' ltac:(lia) Hm' Hfree ltac:(eassumption) ltac:(lia) Ht)
      as [k' [Hk' Hct]].
    exists (1 + smt_size g' + k'). split; [lia | apply CT_True; assumption].
  - destruct (if_step_false σ S Φ Γs _ _ _ v n Hm Hfree ltac:(eassumption) ltac:(lia) Hev)
      as [g' [t' [f' [pc [-> [Ht [Hm' [Hsz Hc']]]]]]]].
    destruct (H1 _ Γs _ k0 n f' ltac:(lia) Hm' Hfree ltac:(eassumption) ltac:(lia) Ht)
      as [k' [Hk' Hct]].
    exists (1 + smt_size g' + k'). split; [lia | apply CT_False; assumption].
Qed.

Lemma clos_tree_contains : forall C k m, clos_tree C k m -> contains_k σ S k m C.
Proof.
  intros C k m H. induction H.
  - assumption.
  - apply ContK_If_True; assumption.
  - apply ContK_If_False; assumption.
Qed.

Section AppAbs.
Variables (Γc0 Γc' : environment) (x : var) (eb ea v_c : expr).
Hypothesis Hbody : good σ S (eq (extend_env Γc' x Γc0 ea)) eb v_c.
Hypothesis Hea : concore_expr ea.

Lemma app_abs_tree : forall bk be, exists h K,
  forall Φ Γs f a kf ka kenv n v_s,
    kf <= bk -> ka <= be -> kenv <= be -> σ ⊨ Φ ->
    contains_env_k σ S kenv Γs Γc0 ->
    clos_tree (EThunk Γc' (ELam x eb)) kf f -> contains_k σ S ka a ea ->
    h <= n -> eval (Fin n) Φ Γs (EApp f a) v_s ->
    exists k', k' <= K /\ contains_k σ S k' v_s v_c.
Proof.
  intros bk. induction bk as [bk IH] using lt_wf_ind. intros be.
  assert (Hprev : exists h1 K1, forall Φ Γs f a kf ka kenv n v_s,
    kf < bk -> ka <= be -> kenv <= be -> σ ⊨ Φ ->
    contains_env_k σ S kenv Γs Γc0 ->
    clos_tree (EThunk Γc' (ELam x eb)) kf f -> contains_k σ S ka a ea ->
    h1 <= n -> eval (Fin n) Φ Γs (EApp f a) v_s ->
    exists k', k' <= K1 /\ contains_k σ S k' v_s v_c).
  { destruct bk as [| bk'].
    - exists 0, 0. intros. lia.
    - destruct (IH bk' ltac:(lia) be) as [h1 [K1 H1]].
      exists h1, K1. intros Φ0 Γs0 f0 a0 kf0 ka0 ke0 n0 v0 Hkf0 Hka0 Hke0 Hm0 He0 Ht0 Ha0 Hn0 Hev0.
      exact (H1 Φ0 Γs0 f0 a0 kf0 ka0 ke0 n0 v0 ltac:(lia) Hka0 Hke0 Hm0 He0 Ht0 Ha0 Hn0 Hev0). }
  destruct Hprev as [h1 [K1 H1]].
  destruct (Hbody bk (be + be + bk)) as [h0 [K0 H0]].
  exists (2 + bk + h0 + h1), (1 + 2 * bk + K0 + K1).
  intros Φ Γs f a kf ka kenv n v_s Hkf Hka Hkenv Hm Henv Htree Ha Hn Hev.
  pose proof (contains_env_k_sym_free _ _ _ _ _ Henv) as Hfree.
  destruct n as [| n]; [lia |].
  inversion Htree; subst.
  - match goal with [ Hc : contains_k _ _ _ (EThunk _ (ELam _ _)) _ |- _ ] =>
      destruct (contains_k_clos_inv σ S _ _ _ _ _ Hc)
        as [Γc2 [bodyc [kenv1 [kb [Heq [Hsx [Henv1 [Hb Hkk]]]]]]]] end.
    injection Heq as <- <- <-.
    inversion Hev; subst; try sym_absurd.
    change (dec (Remaining n)) with (Fin n) in *.
    match goal with [ Hv : eval (Fin n) Φ (extend_env _ _ _ _) _ v_s |- _ ] => rename Hv into Hbody_ev end.
    assert (Hext : contains_env_k σ S (kenv + ka + kenv1)
                     (extend_env Γ x Γs a) (extend_env Γc' x Γc0 ea)).
    { unfold extend_env. apply ContK_Env_Extend; assumption. }
    destruct (H0 _ Φ _ _ kb (kenv + ka + kenv1) n v_s eq_refl ltac:(lia) ltac:(lia) Hm Hext Hb
                ltac:(lia) Hbody_ev) as [k' [Hk' Hc']].
    exists k'. split; [lia | exact Hc'].
  - assert (Hu : unspool_app (EApp (EIf g t f0) a) [] = (EIf g t f0, [a])) by reflexivity.
    pose proof (app_if_step σ Φ Γs _ _ _ _ _ _ _ n Hm Hu Hev) as Hev1. simpl in Hev1.
    destruct n as [| n]; [lia |].
    destruct (if_step_true σ S Φ Γs _ _ _ v_s n Hm Hfree ltac:(eassumption) ltac:(lia) Hev1)
      as [g' [t' [f' [pc [-> [Ht [Hm' [Hsz Hc']]]]]]]].
    destruct (H1 _ Γs t a k ka kenv n t' ltac:(lia) Hka Hkenv Hm' Henv ltac:(eassumption) Ha
                ltac:(lia) Ht) as [k' [Hk' Hct]].
    exists (1 + smt_size g' + k'). split; [lia | apply ContK_If_True; assumption].
  - assert (Hu : unspool_app (EApp (EIf g t f0) a) [] = (EIf g t f0, [a])) by reflexivity.
    pose proof (app_if_step σ Φ Γs _ _ _ _ _ _ _ n Hm Hu Hev) as Hev1. simpl in Hev1.
    destruct n as [| n]; [lia |].
    destruct (if_step_false σ S Φ Γs _ _ _ v_s n Hm Hfree ltac:(eassumption) ltac:(lia) Hev1)
      as [g' [t' [f' [pc [-> [Ht [Hm' [Hsz Hc']]]]]]]].
    destruct (H1 _ Γs f0 a k ka kenv n f' ltac:(lia) Hka Hkenv Hm' Henv ltac:(eassumption) Ha
                ltac:(lia) Ht) as [k' [Hk' Hct]].
    exists (1 + smt_size g' + k'). split; [lia | apply ContK_If_False; assumption].
Qed.

Lemma app_abs_core : forall bk be,
  core_at σ S (eq Γc0) (EApp (EThunk Γc' (ELam x eb)) ea) v_c bk be.
Proof.
  intros bk be.
  destruct (clos_value Γc' x eb bk) as [hc [Kc Hc]].
  destruct (app_abs_tree (bk + Kc) (be + bk)) as [hL [KL HL]].
  exists (1 + hc + hL), KL.
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hif Hn Hev. subst Γc.
  pose proof (contains_env_k_sym_free _ _ _ _ _ Henv) as Hfree.
  destruct n as [| n]; [lia |].
  inversion Hcont; subst; try (simpl in Hif; discriminate Hif);
    try (match goal with [ Ht : is_thunk _ = true |- _ ] => simpl in Ht; discriminate Ht end).
  match goal with [ Hf : contains_k _ _ ?kf ?f (EThunk _ _), Ha : contains_k _ _ ?ka ?a ea |- _ ] =>
    rename Hf into Hfc; rename Ha into Hac; rename f into fs; rename a into as_;
    rename kf into kfs; rename ka into kas end.
  destruct fs; try (inversion Hfc; fail); try (simpl in Hif; discriminate Hif).
  inversion Hev; subst; try sym_absurd.
  - exact (HL Φ Γs _ as_ kfs kas kenv (Datatypes.S n) v_s ltac:(lia) ltac:(lia) ltac:(lia) Hm Henv
             (CT_Leaf _ _ _ _ _ Hfc) Hac ltac:(lia) Hev).
  - change (dec (Remaining n)) with (Fin n) in *.
    match goal with
    | [ H1 : eval (Fin n) Φ Γs (EThunk _ _) ?f', H2 : eval (Fin n) Φ Γs (EApp ?f' as_) v_s |- _ ] =>
        destruct (Hc Φ Γs _ kfs n f' ltac:(lia) Hm Hfree Hfc ltac:(lia) H1) as [k' [Hk' Ht']];
        exact (HL Φ Γs f' as_ k' kas kenv n v_s ltac:(lia) ltac:(lia) ltac:(lia) Hm Henv Ht' Hac
                 ltac:(lia) H2)
    end.
Qed.

End AppAbs.

End Closures.

Ltac cont_absurd Hif :=
  first
  [ simpl in Hif; discriminate Hif
  | match goal with [ Ht : is_thunk _ = true |- _ ] => simpl in Ht; discriminate Ht end
  | match goal with [ Hu : unspool_app _ _ = _ |- _ ] => simpl in Hu; discriminate Hu end ].

Section SimpleCores.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : SymFCCostLaws}.
Context (σ : valuation) (S : symvars).

Lemma var_core : forall Γc0 x Γc' e0 v bk be,
  lookup_env Γc0 x = Some (Γc', e0) ->
  good σ S (eq Γc') e0 v ->
  core_at σ S (eq Γc0) (EVar x) v bk be.
Proof.
  intros Γc0 x Γc' e0 v bk be Hl IH.
  destruct (IH be be) as [h0 [K0 H0]].
  exists (1 + h0), K0.
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hif Hn Hev. subst Γc.
  destruct n as [| n]; [lia |].
  inversion Hcont; subst; try cont_absurd Hif.
  inversion Hev; subst; try sym_absurd.
  - change (dec (Remaining n)) with (Fin n) in *.
    match goal with [ Hls : lookup_env Γs x = Some (?G, ?b), Hb : eval (Fin n) Φ ?G ?b v_s |- _ ] =>
      destruct (contains_env_k_lookup σ S kenv Γs Γc0 x G b Henv Hls)
        as [Gc [ec [k1 [k2 [Hlc [Hce1 [Hce2 [Hk1 Hk2]]]]]]]];
      rewrite Hl in Hlc; injection Hlc as HG He; subst Gc ec;
      exact (H0 Γc' Φ G b k2 k1 n v_s eq_refl ltac:(lia) ltac:(lia) Hm Hce1 Hce2 ltac:(lia) Hb)
    end.
  - exfalso.
    match goal with [ Hls : lookup_env Γs x = None |- _ ] =>
      pose proof (contains_env_lookup_none σ S Γs Γc0 x (contains_env_k_erase _ _ _ _ _ Henv) Hls) as Hc
    end.
    congruence.
Qed.

Lemma symvar_core : forall Γc0 x bk be,
  lookup_env Γc0 x = None ->
  core_at σ S (eq Γc0) (EVar x) (EVar x) bk be.
Proof.
  intros Γc0 x bk be Hl.
  exists 1, 0.
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hif Hn Hev. subst Γc.
  destruct n as [| n]; [lia |].
  inversion Hcont; subst; try cont_absurd Hif.
  inversion Hev; subst; try sym_absurd.
  - exfalso.
    match goal with [ Hls : lookup_env Γs x = Some (?G, ?b) |- _ ] =>
      destruct (contains_env_k_lookup σ S kenv Γs Γc0 x G b Henv Hls)
        as [Gc [ec [k1 [k2 [Hlc _]]]]]
    end.
    congruence.
  - exists 0. split; [lia | apply ContK_Var_Bound; assumption].
Qed.

Lemma lit_core : forall Γc0 l bk be,
  core_at σ S (eq Γc0) (ELit l) (ELit l) bk be.
Proof.
  intros Γc0 l bk be.
  exists (1 + bk), (2 * bk).
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hif Hn Hev. subst Γc.
  pose proof (contains_env_k_sym_free _ _ _ _ _ Henv) as Hfree.
  inversion Hcont; subst; try cont_absurd Hif.
  - destruct n as [| n]; [lia |].
    inversion Hev; subst; try sym_absurd.
    + exfalso.
      match goal with [ Hls : lookup_env Γs ?y = Some _, Hsy : S ?y = true |- _ ] =>
        rewrite (Hfree y Hsy) in Hls; discriminate Hls end.
    + exists 0. split; [lia | apply ContK_Var_Sym; assumption].
  - destruct n as [| n]; [lia |].
    inversion Hev; subst; try sym_absurd.
    exists 0. split; [lia | apply ContK_Lit].
  - match goal with [ Hd : denote σ S e_s l |- _ ] =>
      destruct (smt_eval_fin σ S Φ Γs n e_s v_s l Hm Hfree ltac:(lia) Hd Hev)
        as [_ [_ [kv [Hkv Hc]]]]
    end.
    exists kv. split; [lia | exact Hc].
Qed.

Lemma lam_core : forall Γc0 x e bk be,
  core_at σ S (eq Γc0) (ELam x e) (EThunk Γc0 (ELam x e)) bk be.
Proof.
  intros Γc0 x e bk be.
  exists 1, (be + bk).
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hif Hn Hev. subst Γc.
  destruct n as [| n]; [lia |].
  inversion Hcont; subst; try cont_absurd Hif.
  inversion Hev; subst; try sym_absurd.
  exists (kenv + k). split; [lia |].
  apply ContK_Thunk; [exact Henv | apply ContK_Lam; assumption].
Qed.

Lemma bot_core : forall Γc0 b bk be,
  core_at σ S (eq Γc0) (EBot b) (EBot b) bk be.
Proof.
  intros Γc0 b bk be.
  exists 1, 0.
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hif Hn Hev. subst Γc.
  destruct n as [| n]; [lia |].
  inversion Hcont; subst; try cont_absurd Hif.
  inversion Hev; subst; try sym_absurd.
  exists 0. split; [lia | apply ContK_Bot].
Qed.

Lemma contains_coercion_eq : forall a b, contains σ S (ECoercion a) (ECoercion b) -> a = b.
Proof. intros a b H. inversion H; subst; try reflexivity; simpl in *; discriminate. Qed.

Lemma contains_type_eq : forall a b, contains σ S (EType a) (EType b) -> a = b.
Proof. intros a b H. inversion H; subst; try reflexivity; simpl in *; discriminate. Qed.

Lemma coercion_core : forall Γc0 γ bk be,
  core_at σ S (eq Γc0) (ECoercion γ) (ECoercion (subst_coerc Γc0 γ)) bk be.
Proof.
  intros Γc0 γ bk be.
  exists 1, 0.
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hif Hn Hev. subst Γc.
  destruct n as [| n]; [lia |].
  inversion Hcont; subst; try cont_absurd Hif.
  inversion Hev; subst; try sym_absurd.
  rewrite (contains_coercion_eq _ _
             (subst_coerc_contains_env σ S Γs Γc0 γ (contains_env_k_erase _ _ _ _ _ Henv))).
  exists 0. split; [lia | apply ContK_Coercion].
Qed.

Lemma type_core : forall Γc0 τ bk be,
  core_at σ S (eq Γc0) (EType τ) (EType (subst_type Γc0 τ)) bk be.
Proof.
  intros Γc0 τ bk be.
  exists 1, 0.
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hif Hn Hev. subst Γc.
  destruct n as [| n]; [lia |].
  inversion Hcont; subst; try cont_absurd Hif.
  inversion Hev; subst; try sym_absurd.
  rewrite (contains_type_eq _ _
             (subst_type_contains_env σ S Γs Γc0 τ (contains_env_k_erase _ _ _ _ _ Henv))).
  exists 0. split; [lia | apply ContK_Type].
Qed.

Lemma app_bot_core : forall Γc0 b c2 bk be,
  core_at σ S (eq Γc0) (EApp (EBot b) c2) (EBot b) bk be.
Proof.
  intros Γc0 b c2 bk be.
  exists 1, 0.
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hif Hn Hev. subst Γc.
  destruct n as [| n]; [lia |].
  inversion Hcont; subst; try cont_absurd Hif.
  match goal with [ Hf : contains_k _ _ _ ?f (EBot b) |- _ ] =>
    inversion Hf; subst; try cont_absurd Hif end.
  inversion Hev; subst; try sym_absurd.
  exists 0. split; [lia | apply ContK_Bot].
Qed.

Lemma cast_core : forall Γc0 c γ c' bk be,
  good σ S (eq Γc0) c c' ->
  core_at σ S (eq Γc0) (ECast c γ) (cast_expr c' γ) bk be.
Proof.
  intros Γc0 c γ c' bk be IH.
  destruct (IH bk be) as [h0 [K0 H0]].
  exists (1 + h0), K0.
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hif Hn Hev. subst Γc.
  destruct n as [| n]; [lia |].
  inversion Hcont; subst; try cont_absurd Hif.
  inversion Hev; subst; try sym_absurd.
  change (dec (Remaining n)) with (Fin n) in *.
  match goal with [ Hc : contains_k _ _ k ?es c, Hv : eval (Fin n) Φ Γs ?es ?es' |- _ ] =>
    destruct (H0 Γc0 Φ Γs es k kenv n es' eq_refl Hk Hkenv Hm Henv Hc ltac:(lia) Hv)
      as [k' [Hk' Hc']];
    exists k'; split; [exact Hk' | apply cast_expr_contains_k; exact Hc']
  end.
Qed.

Lemma app_cast_core : forall Γc0 c γ c2 γ_a γ_r v bk be,
  decomp_coerc_arrow γ = Some (γ_a, γ_r) ->
  good σ S (eq Γc0) (ECast (EApp c (ECast c2 (sym_coerc γ_a))) γ_r) v ->
  core_at σ S (eq Γc0) (EApp (ECast c γ) c2) v bk be.
Proof.
  intros Γc0 c γ c2 γ_a γ_r v bk be Hd IH.
  destruct (IH bk be) as [h0 [K0 H0]].
  exists (1 + h0), K0.
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hif Hn Hev. subst Γc.
  destruct n as [| n]; [lia |].
  inversion Hcont; subst; try cont_absurd Hif.
  match goal with [ Hf : contains_k _ _ _ ?f (ECast c γ) |- _ ] =>
    inversion Hf; subst; try cont_absurd Hif end.
  inversion Hev; subst; try sym_absurd.
  change (dec (Remaining n)) with (Fin n) in *.
  match goal with
  | [ Hd' : decomp_coerc_arrow γ = Some _, Hv : eval (Fin n) Φ Γs _ v_s,
      Hfs : contains_k _ _ ?kf ?fs c, Has : contains_k _ _ ?ka ?as0 c2 |- _ ] =>
      rewrite Hd in Hd'; injection Hd' as <- <-;
      exact (H0 Γc0 Φ Γs _ (kf + ka) kenv n v_s eq_refl Hk Hkenv Hm Henv
               (ContK_Cast _ _ _ _ _ γ_r (ContK_App _ _ _ _ _ _ _ _ Hfs (ContK_Cast _ _ _ _ _ _ Has)))
               ltac:(lia) Hv)
  end.
Qed.

End SimpleCores.

Section SpineCores.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : SymFCCostLaws}.
Context (σ : valuation) (S : symvars).

Definition rigid_head (h : expr) : bool :=
  match h with
  | ECon _ | EPrimOp _ => true
  | _ => false
  end.

Lemma contains_k_unspool_rigid_rev : forall k e_s e_c,
  contains_k σ S k e_s e_c ->
  forall kl Ls Lc h args_c,
    Forall3 (contains_k σ S) kl Ls Lc ->
    unspool_app e_c Lc = (h, args_c) ->
    rigid_head h = true ->
    is_if (fst (unspool_app e_s Ls)) = false ->
    exists args_s ks,
      unspool_app e_s Ls = (h, args_s) /\ Forall3 (contains_k σ S) ks args_s args_c /\
      list_sum ks = k + list_sum kl.
Proof.
  induction 1; intros kl Ls Lc h args_c HL Hu Hr Hif; simpl in Hu, Hif |- *;
    try (injection Hu as <- <-; simpl in Hr; discriminate Hr).
  - injection Hu as <- <-. exists Ls, kl. split; [reflexivity | split; [exact HL | reflexivity]].
  - injection Hu as <- <-. exists Ls, kl. split; [reflexivity | split; [exact HL | reflexivity]].
  - destruct (IHcontains_k1 (ka :: kl) (a_s :: Ls) (a_c :: Lc) h args_c
                (Forall3_cons _ _ _ _ _ _ _ H0 HL) Hu Hr Hif) as [args_s [ks [Hus [HF Hs]]]].
    exists args_s, ks. split; [exact Hus | split; [exact HF | simpl in Hs; lia]].
  - destruct ec; simpl in H1; try discriminate H1.
    simpl in Hu. injection Hu as <- <-. simpl in Hr. discriminate Hr.
  - discriminate Hif.
  - discriminate Hif.
Qed.

Lemma find_alt_contains_alt_k_rev : forall ks altss altsc d xs epc,
  Forall3 (contains_alt_k σ S) ks altss altsc ->
  find_alt d altsc = Some (xs, epc) ->
  exists eps kp, find_alt d altss = Some (xs, eps) /\ Forall (fun x => S x = false) xs /\
    contains_k σ S kp eps epc /\ kp <= list_sum ks.
Proof.
  intros ks altss altsc d xs epc HF. revert xs epc.
  induction HF as [| k a_s a_c ks la lc Ha _ IH]; intros xs epc Hf; simpl in Hf; [discriminate |].
  inversion Ha as [k0 d0 xs0 eps epc0 Hxs Hb]; subst. simpl.
  destruct (string_dec d d0).
  - injection Hf as <- <-. exists eps, k. repeat split; try assumption. simpl. lia.
  - destruct (IH xs epc Hf) as [eps' [kp [H1 [H2 [H3 H4]]]]].
    exists eps', kp. repeat split; try assumption. simpl. lia.
Qed.

Lemma extend_env_multi_contains_k : forall xs kΓ ka ks Γs Γc Γas Γac args_s args_c,
  Forall (fun x => S x = false) xs ->
  contains_env_k σ S kΓ Γs Γc ->
  contains_env_k σ S ka Γas Γac ->
  Forall3 (contains_k σ S) ks args_s args_c ->
  Forall concore_expr args_c ->
  exists k', k' <= kΓ + length xs * (ka + list_sum ks) /\
    contains_env_k σ S k' (extend_env_multi Γs xs args_s Γas) (extend_env_multi Γc xs args_c Γac).
Proof.
  induction xs as [| x xs IH]; intros kΓ ka ks Γs Γc Γas Γac args_s args_c Hxs HΓ Ha HF Hcon.
  - exists kΓ. split; [lia | exact HΓ].
  - inversion Hxs as [| x0 xs0 Hx Hxs']; subst.
    destruct HF as [| k a_s a_c ks' l1 l2 Hac HF'].
    + destruct (IH kΓ ka nil Γs Γc Γas Γac nil nil Hxs' HΓ Ha (Forall3_nil _) Hcon) as [k' [Hk' Hc']].
      exists (ka + 0 + k'). split; [simpl in *; nia |].
      simpl. unfold extend_env. apply ContK_Env_Extend;
        [exact Hx | exact Ha | apply ContK_Bot | constructor | exact Hc'].
    + inversion Hcon as [| c0 cs Hc0 Hcs]; subst.
      destruct (IH kΓ ka ks' Γs Γc Γas Γac l1 l2 Hxs' HΓ Ha HF' Hcs) as [k' [Hk' Hc']].
      exists (ka + k + k'). split; [simpl in *; nia |].
      simpl. unfold extend_env. apply ContK_Env_Extend; assumption.
Qed.

Lemma spine_head_rev : forall k f c,
  contains_k σ S k f c ->
  is_if (spine_head f) = false ->
  has_whole_spine_rule (spine_head c) = false ->
  (forall l, spine_head c <> ELit l) ->
  has_whole_spine_rule (spine_head f) = false.
Proof.
  induction 1; intros Hif Hw Hl; simpl in *; try reflexivity; try discriminate.
  - exact (IHcontains_k1 Hif Hw Hl).
  - exfalso. exact (Hl l eq_refl).
Qed.

Lemma comp_k_rev : forall kenv k Γs Γc f c,
  contains_env_k σ S kenv Γs Γc ->
  contains_k σ S k f c ->
  Comp Γc c ->
  is_if (spine_head f) = false ->
  (forall l, spine_head c <> ELit l) ->
  Comp Γs f.
Proof.
  intros kenv k Γs Γc f c Henv Hc Hcomp Hif Hl.
  destruct Hcomp as [x Hbound | x body | es alts | Γ' e Hnotlam | ef ea Hhead].
  - inversion Hc; subst; simpl in Hif; try discriminate Hif;
      try (match goal with [ Ht : is_thunk _ = true |- _ ] => simpl in Ht; discriminate Ht end).
    apply Comp_Var. intros Hnone. apply Hbound.
    exact (contains_env_lookup_none σ S Γs Γc x (contains_env_k_erase _ _ _ _ _ Henv) Hnone).
  - inversion Hc; subst; simpl in Hif; try discriminate Hif;
      try (match goal with [ Ht : is_thunk _ = true |- _ ] => simpl in Ht; discriminate Ht end). apply Comp_Lam.
  - inversion Hc; subst; simpl in Hif; try discriminate Hif;
      try (match goal with [ Ht : is_thunk _ = true |- _ ] => simpl in Ht; discriminate Ht end). apply Comp_Case.
  - inversion Hc; subst; simpl in Hif; try discriminate Hif;
      try (match goal with [ Ht : is_thunk _ = true |- _ ] => simpl in Ht; discriminate Ht end).
    + apply Comp_Thunk.
      match goal with [ Hb : contains_k _ _ _ ?b e |- is_lam ?b = false ] =>
        destruct b; try reflexivity; inversion Hb; subst; simpl in Hnotlam; discriminate end.
    + apply Comp_Thunk.
      match goal with [ Hb : contains_k _ _ _ ?b (EThunk Γ' e) |- is_lam ?b = false ] =>
        destruct b; try reflexivity; inversion Hb end.
  - inversion Hc; subst; simpl in Hif; try discriminate Hif;
      try (match goal with [ Ht : is_thunk _ = true |- _ ] => simpl in Ht; discriminate Ht end).
    apply Comp_App. exact (spine_head_rev _ _ _ Hc Hif Hhead Hl).
Qed.

Lemma eval_spine_head_lit : forall f Φ Γ e v,
  eval f Φ Γ e v -> f = Inf -> Φ = pc_true ->
  forall l, spine_head e = ELit l -> e = ELit l.
Proof.
  intros f Φ Γ e v H. induction H; intros Hf HΦ l0 Hl; try discriminate Hf; subst;
    simpl in Hl; try exact Hl; try discriminate Hl;
    try (rewrite sat_pc_true in *; discriminate).
  - rewrite <- (fst_unspool_app e []) in Hl.
    match goal with [ Hu : unspool_app e [] = _ |- _ ] => rewrite Hu in Hl end.
    discriminate Hl.
  - injection Hf as Hf. subst f.
    specialize (IHeval1 eq_refl eq_refl l0 Hl). subst ef. inversion H.
  - pose proof (fst_unspool_app (EApp ef ea) []) as Hs.
    match goal with [ Hu : unspool_app (EApp ef ea) [] = _ |- _ ] => rewrite Hu in Hs end.
    simpl in Hs. rewrite Hl in Hs. discriminate Hs.
  - pose proof (fst_unspool_app (EApp e1 e2) []) as Hs.
    match goal with [ Hu : unspool_app (EApp e1 e2) [] = _ |- _ ] => rewrite Hu in Hs end.
    simpl in Hs. rewrite Hl in Hs. discriminate Hs.
Qed.

End SpineCores.

Section MoreCores.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : SymFCCostLaws}.
Context (σ : valuation) (S : symvars).

Lemma good_weaken : forall (A A' : environment -> Prop) e v,
  (forall Γ, A' Γ -> A Γ) -> good σ S A e v -> good σ S A' e v.
Proof.
  intros A A' e v Himp Hg bk be.
  destruct (Hg bk be) as [h [K H]]. exists h, K.
  intros Γc Φ Γs e_s k kenv n v_s HA. exact (H Γc Φ Γs e_s k kenv n v_s (Himp Γc HA)).
Qed.

Lemma thunk_good : forall Γ' e v,
  good σ S (eq Γ') e v -> good σ S (fun _ => True) (EThunk Γ' e) v.
Proof.
  intros Γ' e v Hbody. apply good_at_of_core. intros bk be IH.
  destruct (Hbody bk bk) as [h0 [K0 H0]].
  assert (Hprev : exists h1 K1, forall Γc Φ Γs e_s k kenv n v_s,
    k < bk -> kenv < bk -> σ ⊨ Φ ->
    contains_env_k σ S kenv Γs Γc -> contains_k σ S k e_s (EThunk Γ' e) ->
    h1 <= n -> eval (Fin n) Φ Γs e_s v_s ->
    exists k', k' <= K1 /\ contains_k σ S k' v_s v).
  { destruct bk as [| bk'].
    - exists 0, 0. intros. lia.
    - destruct (IH bk' ltac:(lia) bk') as [h1 [K1 H1]].
      exists h1, K1. intros Γc0 Φ0 Γs0 e0 k0 ke0 n0 v0 Hk0 Hke0 Hm0 He0 Hc0 Hn0 Hev0.
      exact (H1 Γc0 Φ0 Γs0 e0 k0 ke0 n0 v0 I ltac:(lia) ltac:(lia) Hm0 He0 Hc0 Hn0 Hev0). }
  destruct Hprev as [h1 [K1 H1]].
  exists (1 + h0 + h1), (K0 + K1).
  intros Γc Φ Γs e_s k kenv n v_s _ Hk Hkenv Hm Henv Hcont Hif Hn Hev.
  destruct n as [| n]; [lia |].
  inversion Hcont; subst; try cont_absurd Hif.
  - inversion Hev; subst; try sym_absurd.
    change (dec (Remaining n)) with (Fin n) in *.
    match goal with
    | [ He : contains_env_k _ _ ?ke ?G Γ', Hb : contains_k _ _ ?kb ?b e,
        Hv : eval (Fin n) Φ ?G ?b v_s |- _ ] =>
        destruct (H0 Γ' Φ G b kb ke n v_s eq_refl ltac:(lia) ltac:(lia) Hm He Hb ltac:(lia) Hv)
          as [k' [Hk' Hc']]
    end.
    exists k'. split; [lia | exact Hc'].
  - inversion Hev; subst; try sym_absurd.
    change (dec (Remaining n)) with (Fin n) in *.
    match goal with
    | [ He : contains_env_k _ _ ?ke ?G ?Gc, Hb : contains_k _ _ ?kb ?b (EThunk Γ' e),
        Hv : eval (Fin n) Φ ?G ?b v_s |- _ ] =>
        destruct (H1 Gc Φ G b kb ke n v_s ltac:(lia) ltac:(lia) Hm He Hb ltac:(lia) Hv)
          as [k' [Hk' Hc']]
    end.
    exists k'. split; [lia | exact Hc'].
Qed.

Lemma con_core : forall Γc0 e_c d args_c bk be,
  unspool_app e_c [] = (ECon d, args_c) ->
  core_at σ S (eq Γc0) e_c (make_con_app d (map (delay Γc0) args_c)) bk be.
Proof.
  intros Γc0 e_c d args_c bk be Hu.
  exists 1, (length args_c * (1 + be) + bk).
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hif Hn Hev. subst Γc.
  destruct n as [| n]; [lia |].
  destruct (contains_k_unspool_rigid_rev σ S k e_s e_c Hcont nil nil nil (ECon d) args_c
              (Forall3_nil _) Hu eq_refl Hif) as [args_s [ks [Hus [HF Hs]]]].
  simpl in Hs.
  assert (Hv : v_s = make_con_app d (map (delay Γs) args_s)).
  { inversion Hev; subst; sym_absurd. }
  subst v_s.
  destruct (delay_map_contains_k σ S kenv Γs Γc0 ks args_s args_c Henv HF) as [ks' [Hks' HF']].
  exists (0 + list_sum ks'). split.
  - pose proof (forall3_length_left_right _ _ _ _ _ _ _ HF) as Hlen. rewrite <- Hlen. nia.
  - unfold make_con_app. exact (contains_k_fold_left_app σ S ks' _ _ 0 _ _ HF' (ContK_Con σ S d)).
Qed.

Lemma args_good : forall Γc0 args_c args_c',
  Forall2 (fun a a' => good σ S (eq Γc0) a a') args_c args_c' ->
  forall bk be, exists h K, forall Φ Γs ks args_s args_s' kenv n,
    list_sum ks <= bk -> kenv <= be -> σ ⊨ Φ ->
    contains_env_k σ S kenv Γs Γc0 ->
    Forall3 (contains_k σ S) ks args_s args_c ->
    h <= n -> Forall2 (eval (Fin n) Φ Γs) args_s args_s' ->
    exists ks', Forall3 (contains_k σ S) ks' args_s' args_c' /\ list_sum ks' <= K.
Proof.
  intros Γc0 args_c args_c' HG bk be.
  induction HG as [| a a' l l' Ha _ IH].
  - exists 0, 0. intros Φ Γs ks args_s args_s' kenv n _ _ _ _ HF _ HE.
    inversion HF; subst. inversion HE; subst. exists nil. split; [constructor | simpl; lia].
  - destruct IH as [h1 [K1 H1]]. destruct (Ha bk be) as [h0 [K0 H0]].
    exists (h0 + h1), (K0 + K1).
    intros Φ Γs ks args_s args_s' kenv n Hks Hkenv Hm Henv HF Hn HE.
    inversion HF as [| k0 as0 ac0 ks0 las lac Hc0 HF0]; subst.
    inversion HE as [| x x' lx lx' Hx HE0]; subst.
    simpl in Hks.
    destruct (H0 Γc0 Φ Γs as0 k0 kenv n x' eq_refl ltac:(lia) Hkenv Hm Henv Hc0 ltac:(lia) Hx)
      as [k' [Hk' Hc']].
    destruct (H1 Φ Γs ks0 las lx' kenv n ltac:(lia) Hkenv Hm Henv HF0 ltac:(lia) HE0)
      as [ks' [HF' Hks']].
    exists (k' :: ks'). split; [constructor; assumption | simpl; lia].
Qed.

Lemma app_prim_core : forall Γc0 c1 c2 p args_c args_c' bk be,
  unspool_app (EApp c1 c2) [] = (EPrimOp p, args_c) ->
  Forall closed_term args_c' ->
  Forall2 (fun a a' => good σ S (eq Γc0) a a') args_c args_c' ->
  core_at σ S (eq Γc0) (EApp c1 c2) (reduce_prim p args_c') bk be.
Proof.
  intros Γc0 c1 c2 p args_c args_c' bk be Hu Hcl HG.
  destruct (args_good Γc0 args_c args_c' HG bk be) as [h0 [K0 H0]].
  exists (1 + h0), (K0 + prim_slack args_c').
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hif Hn Hev. subst Γc.
  destruct n as [| n]; [lia |].
  destruct (contains_k_unspool_rigid_rev σ S k e_s _ Hcont nil nil nil (EPrimOp p) args_c
              (Forall3_nil _) Hu eq_refl Hif) as [args_s [ks [Hus [HF Hs]]]].
  simpl in Hs.
  inversion Hev; subst; try sym_absurd.
  change (dec (Remaining n)) with (Fin n) in *.
  match goal with [ H2 : unspool_app _ [] = (EPrimOp _, _), HE : Forall2 _ _ ?a' |- _ ] =>
    rewrite Hus in H2; injection H2 as <- <-;
    destruct (H0 Φ Γs ks args_s a' kenv n ltac:(lia) Hkenv Hm Henv HF ltac:(lia) HE)
      as [ks' [HF' Hks']]
  end.
  destruct (reduce_prim_contains_k σ S p ks' _ args_c' Hcl HF') as [k' [Hk' Hc']].
  exists k'. split; [lia | exact Hc'].
Qed.

Lemma app_spine_core : forall Γc0 c1 c2 c1' v bk be,
  Comp Γc0 c1 ->
  (forall l, spine_head c1 <> ELit l) ->
  good σ S (eq Γc0) c1 c1' ->
  good σ S (eq Γc0) (EApp c1' c2) v ->
  core_at σ S (eq Γc0) (EApp c1 c2) v bk be.
Proof.
  intros Γc0 c1 c2 c1' v bk be Hcomp Hl IH1 IH2.
  destruct (IH1 bk be) as [h1 [K1 H1]].
  destruct (IH2 (K1 + bk) be) as [h2 [K2 H2]].
  exists (1 + h1 + h2), K2.
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hif Hn Hev. subst Γc.
  destruct n as [| n]; [lia |].
  inversion Hcont; subst; try cont_absurd Hif.
  match goal with [ Hf : contains_k _ _ ?kf ?f c1, Ha : contains_k _ _ ?ka ?a c2 |- _ ] =>
    rename Hf into Hfc; rename Ha into Hac; rename f into fs; rename a into as_;
    rename kf into kfs; rename ka into kas end.
  assert (Hif' : is_if (spine_head fs) = false).
  { rewrite (fst_unspool_app _ []) in Hif. simpl in Hif. exact Hif. }
  pose proof (comp_k_rev σ S kenv kfs Γs Γc0 fs c1 Henv Hfc Hcomp Hif' Hl) as Hcs.
  inversion Hev; subst; try sym_absurd.
  change (dec (Remaining n)) with (Fin n) in *.
  match goal with
  | [ Hv1 : eval (Fin n) Φ Γs fs ?f', Hv2 : eval (Fin n) Φ Γs (EApp ?f' as_) v_s |- _ ] =>
      destruct (H1 Γc0 Φ Γs fs kfs kenv n f' eq_refl ltac:(lia) Hkenv Hm Henv Hfc ltac:(lia) Hv1)
        as [k' [Hk' Hc']];
      exact (H2 Γc0 Φ Γs (EApp f' as_) (k' + kas) kenv n v_s eq_refl ltac:(lia) Hkenv Hm Henv
               (ContK_App _ _ _ _ _ _ _ _ Hc' Hac) ltac:(lia) Hv2)
  end.
Qed.

End MoreCores.

Section CaseCores.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : SymFCCostLaws}.
Context (σ : valuation) (S : symvars).

Lemma case_core : forall Γc0 esc altsc esc' v bk be,
  good σ S (eq Γc0) esc esc' ->
  fgood σ S (eq Γc0) esc' altsc v ->
  (inert_scrutinee esc' -> v = EBot BUndefined) ->
  core_at σ S (eq Γc0) (ECase esc altsc) v bk be.
Proof.
  intros Γc0 esc altsc esc' v bk be IH1 IHF Hinert.
  destruct (IH1 bk be) as [h1 [K1 H1]].
  destruct (IHF ((1 + field_count esc') * K1) (be + bk)) as [hF [KF HF]].
  exists (1 + h1 + hF), KF.
  intros Γc Φ Γs e_s k kenv n v_s HA Hk Hkenv Hm Henv Hcont Hif Hn Hev. subst Γc.
  destruct n as [| n]; [lia |].
  inversion Hcont; subst; try cont_absurd Hif.
  inversion Hev; subst; try sym_absurd.
  change (dec (Remaining n)) with (Fin n) in *.
  match goal with
  | [ Hc : contains_k _ _ ?k1 ?ess esc, Ha : Forall3 _ ?ks ?altss altsc,
      Hv : eval (Fin n) Φ Γs ?ess ?ess', Hf : fold_alts (Fin n) Φ Γs (merge Γs ?ess') ?altss v_s |- _ ] =>
      destruct (H1 Γc0 Φ Γs ess k1 kenv n ess' eq_refl ltac:(lia) Hkenv Hm Henv Hc ltac:(lia) Hv)
        as [k' [Hk' Hc']];
      destruct (merge_contains_k σ S Γs k' ess' esc' Hc') as [[k'' [Hk'' Hm'']] | [Hi1 Hi2]];
      [ exact (HF Γc0 Φ Γs (merge Γs ess') altss k'' ks kenv n v_s eq_refl ltac:(nia) ltac:(lia)
                 ltac:(lia) Hm Henv Hm'' Ha ltac:(lia) Hf)
      | rewrite (Hinert Hi2), (fold_alts_inert _ _ _ _ _ _ Hi1 Hf);
        exists 0; split; [lia | apply ContK_Bot] ]
  end.
Qed.

Lemma fcon_core : forall Γc0 esc d ea_c xs epc altsc v bk be,
  decompose_con_app esc = Some (d, ea_c) ->
  find_alt d altsc = Some (xs, epc) ->
  Forall concore_expr ea_c ->
  good σ S (eq (extend_env_multi Γc0 xs ea_c Γc0)) epc v ->
  fcore_at σ S (eq Γc0) esc altsc v bk be.
Proof.
  intros Γc0 esc d ea_c xs epc altsc v bk be Hd Hf Hcon IH.
  destruct (IH be (be + length xs * (be + bk))) as [h0 [K0 H0]].
  exists h0, K0.
  intros Γc Φ Γs m altss k ks kenv n v_s HA Hk Hkenv Hks Hm Henv Hcont Halts Hif Hn Hev. subst Γc.
  destruct (contains_k_unspool_rigid_rev σ S k m esc Hcont nil nil nil (ECon d) ea_c
              (Forall3_nil _) (decompose_con_app_unspool esc d ea_c Hd) eq_refl Hif)
    as [args_s [ks' [Hus [HF Hs]]]].
  simpl in Hs.
  destruct (find_alt_contains_alt_k_rev σ S ks altss altsc d xs epc Halts Hf)
    as [eps [kp [Hfs [Hxs [Hep Hkp]]]]].
  destruct (extend_env_multi_contains_k σ S xs kenv kenv ks' Γs Γc0 Γs Γc0 args_s ea_c
              Hxs Henv Henv HF Hcon) as [k' [Hk' Henv']].
  assert (Hds : decompose_con_app m = Some (d, args_s)) by (unfold decompose_con_app; rewrite Hus; reflexivity).
  inversion Hev; subst.
  - simpl in Hif. discriminate Hif.
  - simpl in Hif. discriminate Hif.
  - match goal with
    | [ Hd' : decompose_con_app m = Some _, Hf' : find_alt _ altss = Some _,
        Hv : eval (Fin n) Φ _ _ v_s |- _ ] =>
        rewrite Hds in Hd'; injection Hd' as <- <-;
        rewrite Hfs in Hf'; injection Hf' as <- <-;
        exact (H0 _ Φ _ eps kp k' n v_s eq_refl ltac:(lia) ltac:(nia) Hm Henv' Hep ltac:(lia) Hv)
    end.
  - unfold decompose_con_app in Hds. simpl in Hds. discriminate Hds.
  - match goal with [ Hmatch : match decompose_con_app m with _ => _ end |- _ ] =>
      rewrite Hds in Hmatch; congruence end.
Qed.

Lemma fbot_core : forall Γc0 b altsc bk be,
  fcore_at σ S (eq Γc0) (EBot b) altsc (EBot b) bk be.
Proof.
  intros Γc0 b altsc bk be.
  exists 0, 0.
  intros Γc Φ Γs m altss k ks kenv n v_s HA Hk Hkenv Hks Hm Henv Hcont Halts Hif Hn Hev. subst Γc.
  inversion Hcont; subst; try cont_absurd Hif.
  inversion Hev; subst.
  - match goal with [ Hd : decompose_con_app _ = Some _ |- _ ] =>
      unfold decompose_con_app in Hd; simpl in Hd; discriminate Hd end.
  - exists 0. split; [lia | apply ContK_Bot].
  - match goal with [ Hb : is_bot _ = false |- _ ] => simpl in Hb; discriminate Hb end.
Qed.

Lemma fotherwise_core : forall Γc0 esc altsc bk be,
  (match decompose_con_app esc with
   | Some (d, _) => find_alt d altsc = None
   | None => True
   end) ->
  is_bot esc = false ->
  fcore_at σ S (eq Γc0) esc altsc (EBot BUndefined) bk be.
Proof.
  intros Γc0 esc altsc bk be Hmatch Hbot.
  exists 0, 0.
  intros Γc Φ Γs m altss k ks kenv n v_s HA Hk Hkenv Hks Hm Henv Hcont Halts Hif Hn Hev. subst Γc.
  inversion Hev; subst.
  - simpl in Hif. discriminate Hif.
  - simpl in Hif. discriminate Hif.
  - exfalso.
    match goal with
    | [ Hd : decompose_con_app m = Some (?d, ?ea), Hf : find_alt ?d altss = Some (?xs, ?ep) |- _ ] =>
        destruct (contains_k_unspool_con σ S k m esc Hcont nil nil nil (Forall3_nil _) d ea
                    (decompose_con_app_unspool m d ea Hd)) as [args_c [ks' [Huc _]]];
        assert (Hdc : decompose_con_app esc = Some (d, args_c))
          by (unfold decompose_con_app; simpl in Huc; rewrite Huc; reflexivity);
        rewrite Hdc in Hmatch;
        destruct (find_alt_contains_alt σ S altss altsc d xs ep
                    (contains_alts_k_erase σ S ks altss altsc Halts) Hf) as [epc [Hfc _]];
        congruence
    end.
  - exfalso. inversion Hcont; subst; try cont_absurd Hif. simpl in Hbot. discriminate Hbot.
  - exists 0. split; [lia | apply ContK_Bot].
Qed.

End CaseCores.

Section Main.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : SymFCCostLaws}.
Context (σ : valuation) (S : symvars).

Definition eval_motive (f : fuel) (Φ : path_condition) (Γ : environment) (e v : expr) : Prop :=
  f = Inf -> Φ = pc_true -> concore_expr e -> concrete_env Γ -> closed_program Γ e ->
  good σ S (eq Γ) e v.

Definition fold_motive (f : fuel) (Φ : path_condition) (Γ : environment) (e : expr)
  (alts : list alt) (v : expr) : Prop :=
  f = Inf -> Φ = pc_true -> concore_expr e -> Forall concore_alt alts -> concrete_env Γ ->
  scoped_env Γ -> closed_term e -> Forall (scoped_alt (dom_env Γ)) alts ->
  fgood σ S (eq Γ) e alts v.

Lemma forall2_good_of_ind : forall Γ args args',
  Forall2 (fun a a' => eval Inf pc_true Γ a a' /\ eval_motive Inf pc_true Γ a a') args args' ->
  Forall concore_expr args -> concrete_env Γ -> scoped_env Γ -> Forall (scoped (dom_env Γ)) args ->
  Forall2 (fun a a' => good σ S (eq Γ) a a') args args'.
Proof.
  intros Γ args args' HF Hc Hg HΓ Hs. induction HF as [| a a' l l' [_ Ha] _ IH]; constructor.
  - inversion Hc; subst. inversion Hs; subst.
    match goal with [Hca : concore_expr a, Hsa : scoped _ a |- _] =>
      exact (Ha eq_refl eq_refl Hca Hg (conj HΓ Hsa)) end.
  - inversion Hc; subst. inversion Hs; subst.
    match goal with [Hcl : Forall concore_expr l, Hsl : Forall (scoped _) l |- _] =>
      exact (IH Hcl Hsl) end.
Qed.

Lemma forall2_closed_of_ind : forall Γ args args',
  Forall2 (fun a a' => eval Inf pc_true Γ a a' /\ eval_motive Inf pc_true Γ a a') args args' ->
  Forall concore_expr args -> concrete_env Γ -> scoped_env Γ -> Forall (scoped (dom_env Γ)) args ->
  Forall closed_term args'.
Proof.
  intros Γ args args' HF Hc Hg HΓ Hs. induction HF as [| a a' l l' [Hev _] _ IH]; constructor.
  - inversion Hc; subst. inversion Hs; subst.
    match goal with [Hca : concore_expr a, Hsa : scoped _ a |- _] =>
      exact (closed_eval Γ a a' Hg Hca (conj HΓ Hsa) Hev) end.
  - inversion Hc; subst. inversion Hs; subst.
    match goal with [Hcl : Forall concore_expr l, Hsl : Forall (scoped _) l |- _] =>
      exact (IH Hcl Hsl) end.
Qed.

Theorem concrete_good : forall Γc e_c v_c,
  eval Inf pc_true Γc e_c v_c -> concore_expr e_c -> concrete_env Γc -> closed_program Γc e_c ->
  good σ S (eq Γc) e_c v_c.
Proof.
  intros Γc e_c v_c H.
  refine (eval_nested_ind eval_motive fold_motive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ _ _ _ Inf pc_true Γc e_c v_c H eq_refl eq_refl);
    unfold eval_motive, fold_motive.
  - intros f Φ Γ x Γ' e e' Hl _ IH Hf HΦ Hc Hg Hcl. injection Hf as ->. subst Φ.
    destruct (lookup_env_concrete Γ x Γ' e Hg Hl) as [Hg' He].
    destruct (lookup_env_scoped Γ x Γ' e (proj1 Hcl) Hl) as [HΓ' Hse].
    apply good_at_of_core. intros bk be _.
    exact (var_core σ S Γ x Γ' e e' bk be Hl (IH eq_refl eq_refl He Hg' (conj HΓ' Hse))).
  - intros f Φ Γ x Hl _ _ _ _ _. apply good_at_of_core. intros bk be _.
    exact (symvar_core σ S Γ x bk be Hl).
  - intros f Φ Γ l _ _ _ _ _. apply good_at_of_core. intros bk be _. apply lit_core.
  - intros f Φ Γ e d args Hu _ _ _ _ _. apply good_at_of_core. intros bk be _.
    exact (con_core σ S Γ e d args bk be Hu).
  - intros f Φ Γ e γ e' _ IH Hf HΦ Hc Hg Hcl. injection Hf as ->. subst Φ.
    apply good_at_of_core. intros bk be _.
    exact (cast_core σ S Γ e γ e' bk be
             (IH eq_refl eq_refl (concore_expr_cast e γ Hc) Hg (closed_program_cast _ _ _ Hcl))).
  - intros f Φ Γ Γ' x eb ea eb' _ IH Hf HΦ Hc Hg Hcl. injection Hf as ->. subst Φ.
    pose proof (concore_expr_app_l _ _ Hc) as Hcf.
    pose proof (concore_expr_app_r _ _ Hc) as Hca.
    pose proof (concore_expr_lam _ _ (concore_expr_thunk _ _ Hcf)) as Hcb.
    pose proof (concore_expr_thunk_env _ _ Hcf) as Hg'.
    apply good_at_of_core. intros bk be _.
    exact (app_abs_core σ S Γ Γ' x eb ea eb'
             (IH eq_refl eq_refl Hcb (concrete_env_extend Γ' x Γ ea Hg' Hg Hca)
                (closed_program_abs _ _ _ _ _ Hcl)) Hca bk be).
  - intros f Φ Γ ef ea ef' er Hcomp Hev1 IH1 _ IH2 Hf HΦ Hc Hg Hcl. injection Hf as ->. subst Φ.
    pose proof (concore_expr_app_l _ _ Hc) as Hcf.
    pose proof (concore_expr_app_r _ _ Hc) as Hca.
    pose proof (concore_eval_closed Γ ef ef' Hg Hcf Hev1) as Hcf'.
    pose proof (closed_program_app_l _ _ _ Hcl) as Hclf.
    pose proof (closed_eval Γ ef ef' Hg Hcf Hclf Hev1) as Hclf'.
    assert (Hcl2 : closed_program Γ (EApp ef' ea)).
    { split; [exact (proj1 Hcl) |].
      apply Scoped_App; [exact (closed_term_scoped _ _ Hclf') | exact (proj2 (closed_program_app_r _ _ _ Hcl))]. }
    assert (Hl : forall l, spine_head ef <> ELit l).
    { intros l Hsh. pose proof (eval_spine_head_lit _ _ _ _ _ Hev1 eq_refl eq_refl l Hsh) as ->.
      inversion Hcomp. }
    apply good_at_of_core. intros bk be _.
    exact (app_spine_core σ S Γ ef ea ef' er bk be Hcomp Hl (IH1 eq_refl eq_refl Hcf Hg Hclf)
             (IH2 eq_refl eq_refl (Con_App _ _ Hcf' Hca) Hg Hcl2)).
  - intros f Φ Γ b _ _ _ _ _. apply good_at_of_core. intros bk be _. apply bot_core.
  - intros f Φ Γ ef ea p args args' Hu _ HF Hf HΦ Hc Hg Hcl. injection Hf as ->. subst Φ.
    destruct (unspool_app_concore _ _ _ _ Hu Hc (Forall_nil _)) as [_ Hargs].
    destruct (unspool_app_scoped _ _ [] _ args Hu (proj2 Hcl) (Forall_nil _)) as [_ Hsargs].
    apply good_at_of_core. intros bk be _.
    exact (app_prim_core σ S Γ ef ea p args args' bk be Hu
             (forall2_closed_of_ind Γ args args' HF Hargs Hg (proj1 Hcl) Hsargs)
             (forall2_good_of_ind Γ args args' HF Hargs Hg (proj1 Hcl) Hsargs)).
  - intros f Φ Γ x e _ _ _ _ _. apply good_at_of_core. intros bk be _. apply lam_core.
  - intros f Φ Γ ef γ ea γ_a γ_r er Hd _ IH Hf HΦ Hc Hg Hcl. injection Hf as ->. subst Φ.
    pose proof (concore_expr_app_l _ _ Hc) as Hcf.
    pose proof (concore_expr_app_r _ _ Hc) as Hca.
    pose proof (concore_expr_cast _ _ Hcf) as Hcf0.
    apply good_at_of_core. intros bk be _.
    exact (app_cast_core σ S Γ ef γ ea γ_a γ_r er bk be Hd
             (IH eq_refl eq_refl (Con_Cast _ _ (Con_App _ _ Hcf0 (Con_Cast _ _ Hca))) Hg
                (closed_program_push _ _ _ _ _ _ Hcl))).
  - intros f Φ Γ e1 e2 ec et ef args er Hu _ _ _ _ Hc _ _. exfalso.
    destruct (unspool_app_concore _ _ _ _ Hu Hc (Forall_nil _)) as [Hh _].
    exact (not_concore_if _ _ _ Hh).
  - intros f Φ Γ b ea _ _ _ _ _. apply good_at_of_core. intros bk be _. apply app_bot_core.
  - intros f Φ Γ es alts es' er Hev1 IH1 Hfold IHF Hf HΦ Hc Hg Hcl. injection Hf as ->. subst Φ.
    inversion Hc as [| | | | | | es0 alts0 Hces Halts | | | | | | |]; subst.
    pose proof (concore_eval_closed Γ es es' Hg Hces Hev1) as Hces'.
    pose proof (closed_program_case_es _ _ _ Hcl) as Hcles.
    pose proof (closed_eval Γ es es' Hg Hces Hcles Hev1) as Hcles'.
    change (dec Unlimited) with Inf in *.
    rewrite (merge_concore_id Γ es' Hces') in Hfold, IHF.
    apply good_at_of_core. intros bk be _.
    exact (case_core σ S Γ es alts es' er bk be (IH1 eq_refl eq_refl Hces Hg Hcles)
             (IHF eq_refl eq_refl Hces' Halts Hg (proj1 Hcl) Hcles' (closed_program_case_alts _ _ _ Hcl))
             (fun Hi => fold_alts_inert _ _ _ _ _ _ Hi Hfold)).
  - intros. exfalso. match goal with [ Hc : concore_expr (EIf _ _ _) |- _ ] =>
      exact (not_concore_if _ _ _ Hc) end.
  - intros f Φ Γ γ _ _ _ _ _. apply good_at_of_core. intros bk be _. apply coercion_core.
  - intros f Φ Γ e Hs _ HΦ _ _ _. subst Φ. rewrite sat_pc_true in Hs. discriminate Hs.
  - intros f Φ Γ τ _ _ _ _ _. apply good_at_of_core. intros bk be _. apply type_core.
  - intros f Φ Γ Γ' e e' _ IH Hf HΦ Hc Hg Hcl. injection Hf as ->. subst Φ.
    apply (good_weaken σ S (fun _ => True)); [intros; exact I |].
    apply thunk_good.
    exact (IH eq_refl eq_refl (concore_expr_thunk _ _ Hc) (concore_expr_thunk_env _ _ Hc)
             (closed_program_thunk _ _ _ Hcl)).
  - intros Φ Γ e Hf. discriminate Hf.
  - intros. exfalso. match goal with [ Hc : concore_expr (EIf _ _ _) |- _ ] =>
      exact (not_concore_if _ _ _ Hc) end.
  - intros. exfalso. match goal with [ Hc : concore_expr (EIf _ _ _) |- _ ] =>
      exact (not_concore_if _ _ _ Hc) end.
  - intros f Φ Γ e d ea xs ep alts er Hd Hfa _ IH Hf HΦ Hc Halts Hg HΓ Hcle Hsalts. subst f Φ.
    pose proof (decompose_con_app_concore e d ea Hd Hc) as Hea.
    pose proof (find_alt_concore d alts xs ep Hfa Halts) as Hep.
    apply fgood_of_core. intros bk be _.
    exact (fcon_core σ S Γ e d ea xs ep alts er bk be Hd Hfa Hea
             (IH eq_refl eq_refl Hep (concrete_env_extend_multi xs ea Γ Γ Hg Hg Hea)
                (closed_program_fold_con Γ e d ea alts xs ep HΓ Hcle Hsalts Hd Hfa))).
  - intros f Φ Γ b alts _ _ _ _ _ _ _ _. apply fgood_of_core. intros bk be _. apply fbot_core.
  - intros f Φ Γ e alts _ Hmatch Hbot _ _ _ _ _ _ _ _. apply fgood_of_core. intros bk be _.
    exact (fotherwise_core σ S Γ e alts bk be Hmatch Hbot).
Qed.

Theorem forall_form : forall Γc e_con v_con,
  Γc ⊢ᶜ e_con ⇓ᶜ v_con ->
  forall Φ Γs e_sym,
    σ ⊨ Φ ->
    contains_env σ S Γs Γc ->
    contains σ S e_sym e_con ->
    concore_expr e_con ->
    closed_program Γc e_con ->
    exists h, forall n, (h <= n)%nat ->
      forall v_sym, eval (Fin n) Φ Γs e_sym v_sym -> contains σ S v_sym v_con.
Proof.
  intros Γc e_con v_con Hevc Φ Γs e_sym Hm Henv Hcont Hcon Hcl.
  destruct (contains_k_of_contains _ _ _ _ Hcont) as [k Hk].
  destruct (contains_env_k_of_contains_env _ _ _ _ Henv) as [kenv Hkenv].
  destruct (concrete_good Γc e_con v_con Hevc Hcon (contains_env_concrete σ S Γs Γc Henv) Hcl
              (k + kenv) (k + kenv)) as [h [K H]].
  exists h. intros n Hn v_sym Hv.
  destruct (H Γc Φ Γs e_sym k kenv n v_sym eq_refl ltac:(lia) ltac:(lia) Hm Hkenv Hk Hn Hv)
    as [k' [_ Hc']].
  exact (contains_k_erase _ _ _ _ _ Hc').
Qed.

End Main.

Section CompletenessUnderCostLaws.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : SymFCCostLaws}.

Theorem concore_completeness_forall : forall_form_lemma.
Proof.
  intros Γc e_con v_con Hevc Φ Γs σ S e_sym Hm Henv Hcont Hcon Hcl.
  exact (forall_form σ S Γc e_con v_con Hevc Φ Γs e_sym Hm Henv Hcont Hcon Hcl).
Qed.

Theorem concore_completeness_budget : target_completeness.
Proof.
  intros Φ Γs Γc σ S e_sym e_con v_con Hm Henv Hcont Hcon Hcl [hb Hb] Hevc.
  destruct (forall_form σ S Γc e_con v_con Hevc Φ Γs e_sym Hm Henv Hcont Hcon Hcl) as [h Hh].
  exists (h + hb). intros n Hn.
  destruct (Hb n ltac:(lia)) as [v Hv].
  exists v. split; [exact Hv | exact (Hh n ltac:(lia) v Hv)].
Qed.

Corollary concore_completeness_exists : existential_corollary.
Proof. exact (existential_corollary_of_target concore_completeness_budget). Qed.

End CompletenessUnderCostLaws.
