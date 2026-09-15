From SymCoreTheory Require Import SymCore ConCore BranchLaws CostLaws Model.
From Stdlib Require Import Strings.String Lists.List Bool.Bool.
Import ListNotations.
Open Scope string_scope.

Definition tt : @expr model_sorts := ELit true.
Definition ff : @expr model_sorts := ELit false.

Section AnyReducer.
Context {solver : @SymCoreSolver model_sorts}.

Lemma pc_value_ignores_bound : forall (e : expr) Γ pc (σ1 σ2 : valuation),
  expr_to_pc Γ e = Some pc ->
  (forall x, lookup_env Γ x = None -> σ1 x = σ2 x) ->
  pc_value σ1 pc = pc_value σ2 pc
  /\ (forall q qs, pc = PCPrim q qs -> map (pc_value σ1) qs = map (pc_value σ2) qs).
Proof.
  induction e; intros Γ pc σ1 σ2 Hpc Hag; simpl in Hpc; try discriminate.
  - destruct (lookup_env Γ v) eqn:Hl; [discriminate |].
    injection Hpc as <-. split; [simpl; apply Hag; exact Hl | intros q qs Heq; discriminate].
  - injection Hpc as <-. split; [reflexivity | intros q qs Heq; discriminate].
  - injection Hpc as <-. split; [reflexivity | intros q qs Heq; injection Heq as <- <-; reflexivity].
  - destruct (expr_to_pc Γ e1) as [pf |] eqn:E1; [| discriminate].
    destruct pf as [v | l | q qs];
      try (destruct (expr_to_pc Γ e2); discriminate).
    destruct (expr_to_pc Γ e2) as [pa |] eqn:E2; [| discriminate].
    injection Hpc as <-.
    destruct (IHe1 Γ _ σ1 σ2 E1 Hag) as [_ Hmap].
    destruct (IHe2 Γ _ σ1 σ2 E2 Hag) as [Hva _].
    specialize (Hmap q qs eq_refl).
    assert (Hl : map (pc_value σ1) (qs ++ pa :: nil) = map (pc_value σ2) (qs ++ pa :: nil)).
    { rewrite !map_app, Hmap. cbn [map]. rewrite Hva. reflexivity. }
    split.
    + change (prim_value q (map (pc_value σ1) (qs ++ pa :: nil))
              = prim_value q (map (pc_value σ2) (qs ++ pa :: nil))).
      rewrite Hl. reflexivity.
    + intros q' qs' Heq. injection Heq as <- <-. exact Hl.
Qed.

Lemma literal_instance_cases : forall σ S R (l : bool),
  contains σ S R (ELit l) ->
  R = ELit l \/ (exists v, R = EVar v /\ S v = true /\ σ v = l) \/ denote σ S R l
  \/ is_if R = true.
Proof.
  intros σ S R l H. inversion H; subst.
  - right. left. exists x. split; [reflexivity | split; [assumption | reflexivity]].
  - left. reflexivity.
  - discriminate.
  - right. right. right. reflexivity.
  - right. right. right. reflexivity.
  - right. right. left. assumption.
Qed.

Lemma unbound_variable_instance_cases : forall σ S R z,
  S z = false -> contains σ S R (EVar z) -> R = EVar z \/ is_if R = true.
Proof.
  intros σ S R z Hz H. inversion H; subst.
  - left. reflexivity.
  - discriminate.
  - right. reflexivity.
  - right. reflexivity.
Qed.

Definition binds (z : var) : environment := ExtendEnv z (MkClosure · ff) ·.

Lemma denotes_fixed : forall S R pc, denotes S R pc -> expr_to_pc · R = Some pc.
Proof. intros S R pc H. exact (H · (sym_free_env_empty S)). Qed.

Lemma denote_pc : forall σ S R l, denote σ S R l ->
  exists pc, expr_to_pc · R = Some pc /\ pc_value σ pc = l.
Proof. intros σ S R l [pc [Hd Hv]]. exists pc. split; [exact (denotes_fixed S R pc Hd) | exact Hv]. Qed.

Lemma if_has_no_pc : forall R Γ, is_if R = true -> expr_to_pc Γ R = None.
Proof. intros R Γ H. destruct R; try discriminate H. reflexivity. Qed.

Definition two (a b : var) : symvars := fun v => orb (String.eqb v a) (String.eqb v b).
Definition three (a b c : var) : symvars :=
  fun v => orb (String.eqb v a) (orb (String.eqb v b) (String.eqb v c)).
Definition assign (a : var) (va : bool) (b : var) (vb : bool) : valuation :=
  fun v => if String.eqb v a then va else if String.eqb v b then vb else false.

Section AndShortCircuit.
Context {contains_law : ReducePrimContains} {denote_law : ReducePrimDenote}.

Theorem and_false_short_circuit_forbidden :
  @reduce_prim model_sorts solver PAnd (ff :: EVar "z" :: nil) <> ff.
Proof.
  intros Hshort.
  set (R := @reduce_prim model_sorts solver PAnd (EVar "x" :: EVar "z" :: nil)).
  assert (Hc : contains (fun _ => false) (only "x") R ff).
  { rewrite <- Hshort. apply reduce_prim_contains.
    constructor; [exact (Cont_Var_Sym _ _ "x" eq_refl) |].
    constructor; [exact (Cont_Var_Bound _ _ "z" eq_refl) | constructor]. }
  assert (Hval : forall a b, exists pc, expr_to_pc · R = Some pc
            /\ pc_value (assign "x" a "z" b) pc = andb a b).
  { intros a b. apply (denote_pc _ (two "x" "z")).
    exact (reduce_prim_denote (assign "x" a "z" b) (two "x" "z") (PAnd : @primop model_sorts) _ (a :: b :: nil)
             (Forall2_cons _ _ (denote_symvar _ _ "x" eq_refl)
                (Forall2_cons _ _ (denote_symvar _ _ "z" eq_refl) (Forall2_nil _)))). }
  destruct (Hval true true) as [pc [Hpc Htt]].
  destruct (Hval true false) as [pc' [Hpc' Htf]].
  rewrite Hpc in Hpc'. injection Hpc' as <-.
  destruct (literal_instance_cases _ _ _ _ Hc) as [Hlit | [[v [Hv [Hs _]]] | [Hden | Hif]]].
  - rewrite Hlit in Hpc. injection Hpc as <-. discriminate Htt.
  - unfold only in Hs. destruct (string_dec v "x"); [subst v | discriminate Hs].
    rewrite Hv in Hpc. injection Hpc as <-. discriminate Htf.
  - destruct Hden as [pc1 [Hd1 _]].
    assert (Hz : expr_to_pc (binds "z") R = Some pc1)
      by (apply Hd1; intros y Hy; unfold only in Hy;
          destruct (string_dec y "x"); [subst; reflexivity | discriminate Hy]).
    rewrite (denotes_fixed _ _ _ Hd1) in Hpc. injection Hpc as <-.
    destruct (pc_value_ignores_bound R (binds "z") pc1 (assign "x" true "z" true)
                (assign "x" true "z" false) Hz) as [Heq _].
    + intros y Hy. unfold binds in Hy. simpl in Hy.
      destruct (string_dec y "z"); [discriminate Hy |].
      unfold assign. destruct (String.eqb y "x"); [reflexivity |].
      apply String.eqb_neq in n. rewrite n. reflexivity.
    + rewrite Htt, Htf in Heq. discriminate Heq.
  - rewrite (if_has_no_pc R · Hif) in Hpc. discriminate Hpc.
Qed.

Theorem ite_same_arms_forbidden :
  @reduce_prim model_sorts solver PIte (EVar "z" :: tt :: tt :: nil) <> tt.
Proof.
  intros Hsimp.
  set (R := @reduce_prim model_sorts solver PIte (EVar "z" :: EVar "y" :: tt :: nil)).
  assert (Hc : contains (fun _ => true) (only "y") R tt).
  { rewrite <- Hsimp. apply reduce_prim_contains.
    constructor; [exact (Cont_Var_Bound _ _ "z" eq_refl) |].
    constructor; [exact (Cont_Var_Sym _ _ "y" eq_refl) |].
    constructor; [apply Cont_Lit | constructor]. }
  assert (Hval : forall a b, exists pc, expr_to_pc · R = Some pc
            /\ pc_value (assign "z" a "y" b) pc = (if a then b else true)).
  { intros a b. apply (denote_pc _ (two "z" "y")).
    exact (reduce_prim_denote (assign "z" a "y" b) (two "z" "y") (PIte : @primop model_sorts) _ (a :: b :: true :: nil)
             (Forall2_cons _ _ (denote_symvar _ _ "z" eq_refl)
                (Forall2_cons _ _ (denote_symvar _ _ "y" eq_refl)
                   (Forall2_cons _ _ (denote_lit _ _ true) (Forall2_nil _))))). }
  destruct (Hval true false) as [pc [Hpc Htf]].
  destruct (Hval false false) as [pc' [Hpc' Hff]].
  rewrite Hpc in Hpc'. injection Hpc' as <-.
  destruct (literal_instance_cases _ _ _ _ Hc) as [Hlit | [[v [Hv [Hs _]]] | [Hden | Hif]]].
  - rewrite Hlit in Hpc. injection Hpc as <-. discriminate Htf.
  - unfold only in Hs. destruct (string_dec v "y"); [subst v | discriminate Hs].
    rewrite Hv in Hpc. injection Hpc as <-. discriminate Hff.
  - destruct Hden as [pc1 [Hd1 _]].
    assert (Hz : expr_to_pc (binds "z") R = Some pc1)
      by (apply Hd1; intros w Hw; unfold only in Hw;
          destruct (string_dec w "y"); [subst; reflexivity | discriminate Hw]).
    rewrite (denotes_fixed _ _ _ Hd1) in Hpc. injection Hpc as <-.
    destruct (pc_value_ignores_bound R (binds "z") pc1 (assign "z" true "y" false)
                (assign "z" false "y" false) Hz) as [Heq _].
    + intros w Hw. unfold binds in Hw. simpl in Hw.
      destruct (string_dec w "z"); [discriminate Hw |].
      unfold assign. apply String.eqb_neq in n. rewrite n. reflexivity.
    + rewrite Htf, Hff in Heq. discriminate Heq.
  - rewrite (if_has_no_pc R · Hif) in Hpc. discriminate Hpc.
Qed.

Theorem ite_true_condition_forbidden :
  @reduce_prim model_sorts solver PIte (tt :: EVar "z" :: EVar "w" :: nil) <> EVar "z".
Proof.
  intros Hfold.
  set (R := @reduce_prim model_sorts solver PIte (EVar "x" :: EVar "z" :: EVar "w" :: nil)).
  assert (Hc : contains (fun _ => true) (only "x") R (EVar "z")).
  { rewrite <- Hfold. apply reduce_prim_contains.
    constructor; [exact (Cont_Var_Sym _ _ "x" eq_refl) |].
    constructor; [exact (Cont_Var_Bound _ _ "z" eq_refl) |].
    constructor; [exact (Cont_Var_Bound _ _ "w" eq_refl) | constructor]. }
  set (σ := (fun v => if String.eqb v "z" then true else false) : @valuation model_sorts).
  destruct (denote_pc _ _ _ _
              (reduce_prim_denote σ (three "x" "z" "w") (PIte : @primop model_sorts) _ (false :: true :: false :: nil)
                 (Forall2_cons _ _ (denote_symvar _ _ "x" eq_refl)
                    (Forall2_cons _ _ (denote_symvar _ _ "z" eq_refl)
                       (Forall2_cons _ _ (denote_symvar _ _ "w" eq_refl) (Forall2_nil _))))))
    as [pc [Hpc Hv]].
  change (expr_to_pc · R = Some pc) in Hpc.
  destruct (unbound_variable_instance_cases _ _ _ "z" eq_refl Hc) as [Hz | Hif].
  - rewrite Hz in Hpc. injection Hpc as <-. discriminate Hv.
  - rewrite (if_has_no_pc R · Hif) in Hpc. discriminate Hpc.
Qed.

End AndShortCircuit.
End AnyReducer.

Section SameArmsModel.

Definition same_arms_unbranched (p : model_primop) (args : list expr) : expr :=
  match p, args with
  | PIte, _ :: a :: b :: nil => if expr_eqb a b then a else reduce_unbranched p args
  | _, _ => reduce_unbranched p args
  end.

Definition same_arms_reduce_prim (p : model_primop) (args : list expr) : expr :=
  split_args (same_arms_unbranched p) args.

Definition same_arms_solver : @SymCoreSolver model_sorts :=
  Build_SymCoreSolver
    model_sat (PCLit true) eq_refl same_arms_reduce_prim
    erase_cast keep_coercion keep_type.

Theorem same_arms_breaks_contains : ~ @ReducePrimContains model_sorts same_arms_solver.
Proof.
  intros Hlaw.
  pose proof (Hlaw (fun _ => true) (only "y") PIte
                (EVar "z" :: EVar "y" :: tt :: nil)
                (EVar "z" :: tt :: tt :: nil)) as H.
  assert (Hargs : Forall2 (contains (fun _ => true) (only "y"))
                    (EVar "z" :: EVar "y" :: tt :: nil)
                    (EVar "z" :: tt :: tt :: nil)).
  { constructor; [exact (Cont_Var_Bound _ _ "z" eq_refl) |].
    constructor; [exact (Cont_Var_Sym _ _ "y" eq_refl) |].
    constructor; [apply Cont_Lit | constructor]. }
  specialize (H Hargs). vm_compute in H.
  inversion H; subst.
  match goal with
  | [ Hd : denote _ _ _ _ |- _ ] =>
      destruct Hd as [pc [Hden _]];
      specialize (Hden (binds "z"));
      assert (Hfree : sym_free_env (only "y") (binds "z"))
        by (intros w Hw; unfold only in Hw; destruct (string_dec w "y");
            [subst; reflexivity | discriminate Hw]);
      specialize (Hden Hfree); vm_compute in Hden; discriminate Hden
  end.
Qed.

Theorem same_arms_breaks_saturated : ~ @ReducePrimSaturated model_sorts same_arms_solver.
Proof.
  intros Hlaw.
  pose proof (Hlaw PIte (EVar "x" :: EApp (EPrimOp PAnd) (EVar "y") :: EApp (EPrimOp PAnd) (EVar "y") :: nil)
                PAnd (EVar "y" :: nil) eq_refl) as H.
  discriminate H.
Qed.

Theorem same_arms_breaks_ground_value : ~ @ReducePrimGroundValue model_sorts same_arms_solver.
Proof.
  intros Hlaw.
  destruct (Hlaw PIte (EVar "x" :: @EPrimOp model_sorts PAnd :: @EPrimOp model_sorts PAnd :: nil) eq_refl) as [l Hl].
  discriminate Hl.
Qed.

End SameArmsModel.

Section MergeLosesInstance.

Definition merge_sigma : valuation := fun _ => true.
Definition merge_branch : expr := EIf (EVar "x") (EVar "z") (EVar "w").

Lemma merge_branch_instance : contains merge_sigma (only "x") merge_branch (EVar "z").
Proof.
  apply Cont_If_True; [| exact (Cont_Var_Bound _ _ "z" eq_refl)].
  exists (PCVar "x"). split; [| reflexivity].
  intros Γ Hfree. simpl. rewrite (Hfree "x" (only_self "x")). reflexivity.
Qed.

Theorem merge_loses_unbound_variable_instance :
  contains merge_sigma (only "x") merge_branch (EVar "z")
  /\ ~ contains merge_sigma (only "x") (@merge model_sorts model_solver · merge_branch) (EVar "z").
Proof.
  split; [exact merge_branch_instance |].
  vm_compute. intros H. inversion H.
Qed.

End MergeLosesInstance.
