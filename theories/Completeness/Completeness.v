From SymCoreTheory Require Export Completeness.Statement.
From Stdlib Require Import Strings.String Lists.List Lia Arith.PeanoNat.
Import ListNotations.

Section Leaves.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.

Definition leaf_value (v : value) : Prop :=
  match v with VIf _ _ _ => False | _ => True end.
Definition leaf_thunk (t : thunk) : Prop :=
  match t with TIf _ _ _ => False | _ => True end.

Lemma contains_val_by_leaves : forall σ vc (Q : value -> Prop),
  (forall vs, contains_val σ vs vc -> leaf_value vs -> Q vs) ->
  (forall p vt vf, σ ⊨ p -> Q vt -> Q (VIf p vt vf)) ->
  (forall p vt vf, σ ⊨ pc_not p -> Q vf -> Q (VIf p vt vf)) ->
  forall vs, contains_val σ vs vc -> Q vs.
Proof.
  intros σ vc Q Hleaf Htrue Hfalse vs.
  induction vs; intros Hvs; try (apply Hleaf; [exact Hvs | exact I]).
  inversion Hvs; subst; [apply Htrue | apply Hfalse]; auto.
Qed.

Lemma contains_thunk_by_leaves : forall σ tc (Q : thunk -> Prop),
  (forall ts, contains_thunk σ ts tc -> leaf_thunk ts -> Q ts) ->
  (forall p tt tf, σ ⊨ p -> Q tt -> Q (TIf p tt tf)) ->
  (forall p tt tf, σ ⊨ pc_not p -> Q tf -> Q (TIf p tt tf)) ->
  forall ts, contains_thunk σ ts tc -> Q ts.
Proof.
  intros σ tc Q Hleaf Htrue Hfalse ts.
  induction ts; intros Hts; try (apply Hleaf; [exact Hts | exact I]).
  inversion Hts; subst; [apply Htrue | apply Hfalse]; auto.
Qed.

End Leaves.

Section PeelBranches.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.

Lemma apply_by_leaves : forall σ g Γs e_s vf_c v_c,
  (forall vf_s, contains_val σ vf_s vf_c -> leaf_value vf_s ->
     forall Φ v_s, apply g Φ Γs vf_s e_s v_s -> σ ⊨ Φ -> contains_val σ v_s v_c) ->
  forall vf_s, contains_val σ vf_s vf_c ->
  forall Φ v_s, apply g Φ Γs vf_s e_s v_s -> σ ⊨ Φ -> contains_val σ v_s v_c.
Proof.
  intros σ g Γs e_s vf_c v_c Hleaf.
  apply (contains_val_by_leaves σ vf_c (fun vf_s => forall Φ v_s,
    apply g Φ Γs vf_s e_s v_s -> σ ⊨ Φ -> contains_val σ v_s v_c)); [exact Hleaf | |];
    intros p vt vf Hp IH Φ v_s Hrun Hm; inversion Hrun; subst.
  - apply ite_keeps; [exact Hp | eapply IH; eassumption].
  - apply ite_keeps_false; [exact Hp | eapply IH; eassumption].
Qed.

Lemma force_by_leaves : forall σ g t_c v_c,
  (forall t_s, contains_thunk σ t_s t_c -> leaf_thunk t_s ->
     forall Φ v_s, force g Φ t_s v_s -> σ ⊨ Φ -> contains_val σ v_s v_c) ->
  forall t_s, contains_thunk σ t_s t_c ->
  forall Φ v_s, force g Φ t_s v_s -> σ ⊨ Φ -> contains_val σ v_s v_c.
Proof.
  intros σ g t_c v_c Hleaf.
  apply (contains_thunk_by_leaves σ t_c (fun t_s => forall Φ v_s,
    force g Φ t_s v_s -> σ ⊨ Φ -> contains_val σ v_s v_c)); [exact Hleaf | |];
    intros p tt tf Hp IH Φ v_s Hrun Hm; inversion Hrun; subst.
  - apply ite_keeps; [exact Hp | eapply IH; eassumption].
  - apply ite_keeps_false; [exact Hp | eapply IH; eassumption].
Qed.

Lemma select_by_leaves : forall σ g tthen_s telse_s c_c v_c,
  (forall c_s, contains_val σ c_s c_c -> leaf_value c_s ->
     forall Φ v_s, select g Φ c_s tthen_s telse_s v_s -> σ ⊨ Φ -> contains_val σ v_s v_c) ->
  forall c_s, contains_val σ c_s c_c ->
  forall Φ v_s, select g Φ c_s tthen_s telse_s v_s -> σ ⊨ Φ -> contains_val σ v_s v_c.
Proof.
  intros σ g tthen_s telse_s c_c v_c Hleaf.
  apply (contains_val_by_leaves σ c_c (fun c_s => forall Φ v_s,
    select g Φ c_s tthen_s telse_s v_s -> σ ⊨ Φ -> contains_val σ v_s v_c)); [exact Hleaf | |];
    intros p ct cf Hp IH Φ v_s Hrun Hm; inversion Hrun; subst.
  - apply ite_keeps; [exact Hp | eapply IH; eassumption].
  - apply ite_keeps_false; [exact Hp | eapply IH; eassumption].
Qed.

Lemma fold_by_leaves : forall σ g Γs alts_s vs_c v_c,
  (forall vs_s, contains_val σ vs_s vs_c -> leaf_value vs_s ->
     forall Φ v_s, fold_alts g Φ Γs vs_s alts_s v_s -> σ ⊨ Φ -> contains_val σ v_s v_c) ->
  forall vs_s, contains_val σ vs_s vs_c ->
  forall Φ v_s, fold_alts g Φ Γs vs_s alts_s v_s -> σ ⊨ Φ -> contains_val σ v_s v_c.
Proof.
  intros σ g Γs alts_s vs_c v_c Hleaf.
  apply (contains_val_by_leaves σ vs_c (fun vs_s => forall Φ v_s,
    fold_alts g Φ Γs vs_s alts_s v_s -> σ ⊨ Φ -> contains_val σ v_s v_c)); [exact Hleaf | |];
    intros p vt vf Hp IH Φ v_s Hrun Hm; inversion Hrun; subst;
    try (simpl in *; contradiction).
  - apply ite_keeps; [exact Hp | eapply IH; [eassumption |]].
    apply models_and. split; assumption.
  - apply ite_keeps_false; [exact Hp | eapply IH; [eassumption |]].
    apply models_and. split; assumption.
Qed.

End PeelBranches.

Section Completeness.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.
Context {reduce_prim_literal_law : ReducePrimLiteral} {cast_concore_law : CastConcore}
  {models_sat_law : ModelsSat} {reduce_prim_contains_law : ReducePrimContains}
  {cast_contains_law : CastContains} {subst_contains_law : SubstContains}.

Lemma forces_complete : forall σ g ts_c vs_c,
  Forall2 (complete_force σ g pc_true) ts_c vs_c -> Forall concrete_thunk ts_c ->
  forall Φ ts_s vs_s, Forall2 (force g Φ) ts_s vs_s -> σ ⊨ Φ ->
  Forall2 (contains_thunk σ) ts_s ts_c -> Forall2 (contains_val σ) vs_s vs_c.
Proof.
  intros σ g ts_c vs_c Hall. induction Hall as [| t_c v_c ts_c' vs_c' Ht _ IH];
    intros Hconc Φ ts_s vs_s Hforces Hm Hts.
  - inversion Hts; subst. inversion Hforces; subst. constructor.
  - inversion Hts as [| t_s ? ts_s' ? Hts1 Hts']; subst.
    inversion Hforces as [| ? v_s ? vs_s' Hf Hforces']; subst.
    inversion Hconc; subst. constructor.
    + eapply Ht; eauto.
    + eapply IH; eauto.
Qed.

Ltac refute_leaf :=
  match goal with
  | Hl : leaf_value (VIf _ _ _) |- _ => destruct Hl
  | Hl : leaf_thunk (TIf _ _ _) |- _ => destruct Hl
  end.

Ltac invert_sym H := inversion H; subst; try refute_prune; try refute_leaf.

Ltac discharge_complete :=
  solve
    [ discharge_lockstep_premise
    | apply contains_merged; eauto with concrete
    | apply models_and; split; eassumption ].

Ltac fire IH := eapply IH; [reflexivity | discharge_complete ..].

Ltac peel L x Hx Φ v Hrun Hm :=
  revert Φ v Hrun Hm; revert x Hx; apply L; intros x Hx ?Hleaf Φ v Hrun Hm.

Lemma lockstep_complete : forall σ,
  (forall g Φ Γ e v, eval g Φ Γ e v -> complete_eval σ g Φ Γ e v) /\
  (forall g Φ Γ vf e v, apply g Φ Γ vf e v -> complete_apply σ g Φ Γ vf e v) /\
  (forall g Φ op ts v, prim_app g Φ op ts v -> complete_prim σ g Φ op ts v) /\
  (forall g Φ t v, force g Φ t v -> complete_force σ g Φ t v) /\
  (forall g Φ c tthen telse v, select g Φ c tthen telse v ->
     complete_select σ g Φ c tthen telse v) /\
  (forall g Φ Γ vs alts v, fold_alts g Φ Γ vs alts v -> complete_fold σ g Φ Γ vs alts v).
Proof.
  intros σ.
  apply (eval_mut_ind (complete_eval σ) (complete_apply σ) (complete_prim σ)
    (complete_force σ) (complete_select σ) (complete_fold σ));
    unfold complete_eval, complete_apply, complete_prim, complete_force, complete_select,
      complete_fold.
  - intros f Φc Γc x t v Hl Hf IH HΦ HΓc Hec Φ Γs e_s v_s Hrun Hm HΓ He. subst Φc.
    invert_sym He. invert_sym Hrun.
    match goal with
    | Hls : lookup_env Γs x = Some ?ts |- _ =>
        destruct (contains_lookup σ Γs Γc x ts HΓ Hls) as [tc [Hlc Htc]]
    end.
    rewrite Hl in Hlc. injection Hlc as <-. fire IH.
  - intros f Φc Γc l HΦ HΓc Hec Φ Γs e_s v_s Hrun Hm HΓ He. subst Φc.
    invert_sym He; invert_sym Hrun; repeat constructor.
  - intros f Φc Γc s HΦ HΓc Hec. inversion Hec.
  - intros f Φc Γc d HΦ HΓc Hec Φ Γs e_s v_s Hrun Hm HΓ He. subst Φc.
    invert_sym He. invert_sym Hrun. repeat constructor.
  - intros f Φc Γc op v Hp IH HΦ HΓc Hec Φ Γs e_s v_s Hrun Hm HΓ He. subst Φc.
    invert_sym He. invert_sym Hrun. fire IH.
  - intros f Φc Γc ef ea vf v Hef IHf Hea IHa HΦ HΓc Hec Φ Γs e_s v_s Hrun Hm HΓ He.
    subst Φc. invert_sym He. invert_concrete_shapes. invert_sym Hrun.
    match goal with
    | Hfs : eval (dec f) Φ Γs _ ?vf_s |- _ =>
        assert (Hvf : contains_val σ vf_s vf) by fire IHf
    end.
    fire IHa.
  - intros f Φc Γc x b HΦ HΓc Hec Φ Γs e_s v_s Hrun Hm HΓ He. subst Φc.
    invert_sym He. invert_sym Hrun. constructor; assumption.
  - intros f Φc Γc e γ v He' IH HΦ HΓc Hec Φ Γs e_s v_s Hrun Hm HΓ He. subst Φc.
    invert_sym He. invert_concrete_shapes. invert_sym Hrun.
    apply cast_contains. fire IH.
  - intros f Φc Γc b HΦ HΓc Hec Φ Γs e_s v_s Hrun Hm HΓ He. subst Φc.
    invert_sym He. invert_sym Hrun. constructor; assumption.
  - intros f Φc Γc es alts vs v Hes IHs Hfold IHfold HΦ HΓc Hec Φ Γs e_s v_s Hrun Hm HΓ He.
    subst Φc. invert_sym He. invert_concrete_shapes. invert_sym Hrun.
    match goal with
    | Hss : eval (dec f) Φ Γs _ ?vs_s |- _ =>
        assert (Hvs : contains_val σ vs_s vs) by fire IHs
    end.
    fire IHfold.
  - intros f Φc Γc γ HΦ HΓc Hec Φ Γs e_s v_s Hrun Hm HΓ He. subst Φc.
    invert_sym He. invert_sym Hrun.
    rewrite (subst_coerc_contains σ Γs Γc γ HΓ). constructor.
  - intros f Φc Γc τ HΦ HΓc Hec Φ Γs e_s v_s Hrun Hm HΓ He. subst Φc.
    invert_sym He. invert_sym Hrun.
    rewrite (subst_type_contains σ Γs Γc τ HΓ). constructor.
  - intros f Φc Γc e Hs HΦ. subst Φc. rewrite sat_pc_true in Hs. discriminate Hs.
  - intros Φc Γc e HΦ HΓc Hec Φ Γs e_s v_s Hrun Hm HΓ He.
    invert_sym Hrun. repeat constructor.
  - intros g Φc Γc d ts e_c HΦ HΓc Hvfc Hec Φ Γs vf_s e_s v_s Hrun Hm HΓ Hvf He. subst Φc.
    peel apply_by_leaves vf_s Hvf Φ v_s Hrun Hm.
    invert_sym Hvf. invert_sym Hrun. constructor. discharge_complete.
  - intros g Φc Γc Γ' x b e_c v Hb IH HΦ HΓc Hvfc Hec Φ Γs vf_s e_s v_s Hrun Hm HΓ Hvf He.
    subst Φc. invert_concrete_shapes.
    peel apply_by_leaves vf_s Hvf Φ v_s Hrun Hm.
    invert_sym Hvf. invert_sym Hrun. fire IH.
  - intros g Φc Γc op ts e_c v Hp IH HΦ HΓc Hvfc Hec Φ Γs vf_s e_s v_s Hrun Hm HΓ Hvf He.
    subst Φc. invert_concrete_shapes.
    peel apply_by_leaves vf_s Hvf Φ v_s Hrun Hm.
    invert_sym Hvf. invert_sym Hrun. fire IH.
  - intros g Φc Γc v' γ γa γr e_c v Hd Ha IH HΦ HΓc Hvfc Hec Φ Γs vf_s e_s v_s Hrun Hm HΓ
      Hvf He.
    subst Φc. invert_concrete_shapes.
    peel apply_by_leaves vf_s Hvf Φ v_s Hrun Hm.
    invert_sym Hvf. invert_sym Hrun.
    match goal with
    | Hd' : decomp_coerc_arrow γ = Some _ |- _ => rewrite Hd in Hd'; injection Hd' as <- <-
    end.
    constructor. fire IH.
  - intros g Φc Γc b e_c HΦ HΓc Hvfc Hec Φ Γs vf_s e_s v_s Hrun Hm HΓ Hvf He. subst Φc.
    peel apply_by_leaves vf_s Hvf Φ v_s Hrun Hm.
    invert_sym Hvf. invert_sym Hrun. constructor; assumption.
  - intros g Φc Γc p vt vf e_c vt' vf' _ _ _ _ HΦ HΓc Hvfc. inversion Hvfc.
  - intros g Φc op ts_c Hlt HΦ Hconc Φ ts_s v_s Hrun Hm Hts. subst Φc.
    pose proof (Forall2_length Hts) as Hlen.
    invert_sym Hrun; [constructor; exact Hts | ..]; rewrite ?op_ite_arity in *;
      simpl in *; lia.
  - intros g Φc tc tthen telse c v Hc IHc Hs IHs HΦ Hconc Φ ts_s v_s Hrun Hm Hts. subst Φc.
    invert_concrete_shapes.
    inversion Hts as [| tc_s ? r1 ? Htc Hr1]; subst.
    inversion Hr1 as [| tthen_s ? r2 ? Hthen Hr2]; subst.
    inversion Hr2 as [| telse_s ? r3 ? Helse Hr3]; subst.
    inversion Hr3; subst.
    invert_sym Hrun; [rewrite op_ite_arity in *; simpl in *; lia | | congruence].
    match goal with
    | Hcs : force g Φ tc_s ?c_s |- _ =>
        assert (Hcrel : contains_val σ c_s c) by fire IHc
    end.
    fire IHs.
  - intros g Φc op ts_c vs_c Hne Hlen Hall IHall HΦ Hconc Φ ts_s v_s Hrun Hm Hts. subst Φc.
    pose proof (Forall2_length Hts) as Hlen_s.
    invert_sym Hrun; [lia | contradiction |].
    apply lift_prim_keeps.
    + match goal with Hf : Forall2 (force g Φ) ts_s _ |- _ => rewrite <- (Forall2_length Hf) end.
      lia.
    + eapply forces_complete; eassumption.
    + exact (concrete_forces_output g ts_c vs_c Hall Hconc).
  - intros g Φc Γc e_c v He IH HΦ Hconc Φ t_s v_s Hrun Hm Ht. subst Φc.
    invert_concrete_shapes.
    peel force_by_leaves t_s Ht Φ v_s Hrun Hm.
    invert_sym Ht. invert_sym Hrun. fire IH.
  - intros g Φc p tthen telse vt vf _ _ _ _ HΦ Hconc. inversion Hconc.
  - intros g Φc tthen telse v Ht IH HΦ Hc Hthen Helse Φ c_s tthen_s telse_s v_s Hrun Hm Hcs
      Hthens Helses.
    subst Φc. peel select_by_leaves c_s Hcs Φ v_s Hrun Hm.
    invert_sym Hcs. invert_sym Hrun.
    + fire IH.
    + match goal with Hp : contains_prim _ (PLit _) _ |- _ => inversion Hp; subst end.
      contradiction.
    + match goal with
      | Hp : contains_prim σ ?q (PLit lit_true) |- _ =>
          assert (σ ⊨ q) by (apply contains_prim_denote; exact Hp)
      end.
      apply ite_keeps; [assumption | fire IH].
  - intros g Φc l tthen telse v Hl Hf IH HΦ Hc Hthen Helse Φ c_s tthen_s telse_s v_s Hrun Hm
      Hcs Hthens Helses.
    subst Φc. peel select_by_leaves c_s Hcs Φ v_s Hrun Hm.
    invert_sym Hcs. invert_sym Hrun.
    + match goal with Hp : contains_prim _ (PLit _) _ |- _ => inversion Hp; subst end.
      contradiction.
    + fire IH.
    + match goal with
      | Hp : contains_prim σ ?q (PLit l) |- _ =>
          assert (σ ⊨ pc_not q)
            by (apply models_not; rewrite (contains_prim_denote σ q l Hp); exact Hl)
      end.
      apply ite_keeps_false; [assumption | fire IH].
  - intros g Φc p tthen telse vt vf Hp _ _ _ _ HΦ Hc. subst Φc.
    apply concrete_prim_is_literal in Hc. congruence.
  - intros g Φc b tthen telse HΦ Hc Hthen Helse Φ c_s tthen_s telse_s v_s Hrun Hm Hcs Hthens
      Helses.
    subst Φc. peel select_by_leaves c_s Hcs Φ v_s Hrun Hm.
    invert_sym Hcs. invert_sym Hrun. constructor; assumption.
  - intros g Φc p ct cf tthen telse vt vf _ _ _ _ HΦ Hc. inversion Hc.
  - intros g Φc Γc d ts alts xs ep v Hfind He IH HΦ HΓc Hvsc Haltsc Φ Γs vs_s alts_s v_s
      Hrun Hm HΓ Hvs Halts.
    subst Φc. invert_concrete_shapes.
    peel fold_by_leaves vs_s Hvs Φ v_s Hrun Hm.
    invert_sym Hvs. invert_sym Hrun.
    + match goal with
      | Hfs : find_alt d alts_s = Some _ |- _ =>
          destruct (contains_find_alt σ d alts_s alts _ _ Halts Hfs) as [epc [Hfc Hep]]
      end.
      rewrite Hfind in Hfc. injection Hfc as <- <-. fire IH.
    + simpl in *.
      rewrite (contains_find_alt_none σ d alts_s alts Halts ltac:(assumption)) in Hfind.
      discriminate Hfind.
  - intros g Φc Γc b alts HΦ HΓc Hvsc Haltsc Φ Γs vs_s alts_s v_s Hrun Hm HΓ Hvs Halts.
    subst Φc. peel fold_by_leaves vs_s Hvs Φ v_s Hrun Hm.
    invert_sym Hvs. invert_sym Hrun; [constructor; assumption | simpl in *; contradiction].
  - intros g Φc Γc p vt vf alts vt' vf' _ _ _ _ HΦ HΓc Hvsc. inversion Hvsc.
  - intros g Φc Γc vs_c alts Hno HΦ HΓc Hvsc Haltsc Φ Γs vs_s alts_s v_s Hrun Hm HΓ Hvs Halts.
    subst Φc. peel fold_by_leaves vs_s Hvs Φ v_s Hrun Hm.
    invert_sym Hrun.
    + invert_sym Hvs. simpl in Hno.
      match goal with
      | Hfs : find_alt _ alts_s = Some _ |- _ =>
          destruct (contains_find_alt σ _ alts_s alts _ _ Halts Hfs) as [epc [Hfc _]]
      end.
      congruence.
    + invert_sym Hvs. simpl in Hno. contradiction.
    + repeat constructor.
Qed.

Theorem concore_completeness_forall : forall Φ Γs Γc σ e_s e_c v_c,
  σ ⊨ Φ -> contains_env σ Γs Γc -> contains_expr σ e_s e_c ->
  concore_expr e_c -> concrete_env Γc -> Γc ⊢ᶜ e_c ⇓ᶜ v_c ->
  exists h, forall n, h <= n -> forall v_s, eval (Fin n) Φ Γs e_s v_s -> contains_val σ v_s v_c.
Proof.
  intros Φ Γs Γc σ e_s e_c v_c Hm HΓ He Hec HΓc Heval.
  destruct (eval_inf_has_budget pc_true Γc e_c v_c Heval) as [h Hh].
  exists h. intros n Hn v_s Hrun.
  exact (proj1 (lockstep_complete σ) _ _ _ _ _ (Hh n Hn) eq_refl HΓc Hec
    Φ Γs e_s v_s Hrun Hm HΓ He).
Qed.

Theorem concore_completeness_budget : forall Φ Γs Γc σ e_s e_c v_c,
  σ ⊨ Φ -> contains_env σ Γs Γc -> contains_expr σ e_s e_c ->
  concore_expr e_c -> concrete_env Γc -> budget_total Φ Γs e_s -> Γc ⊢ᶜ e_c ⇓ᶜ v_c ->
  exists h, forall n, h <= n -> exists v_s, eval (Fin n) Φ Γs e_s v_s /\ contains_val σ v_s v_c.
Proof.
  intros Φ Γs Γc σ e_s e_c v_c Hm HΓ He Hec HΓc [h_total Htotal] Heval.
  destruct (concore_completeness_forall Φ Γs Γc σ e_s e_c v_c Hm HΓ He Hec HΓc Heval)
    as [h_related Hrelated].
  exists (Nat.max h_total h_related). intros n Hn.
  destruct (Htotal n ltac:(lia)) as [v_s Hrun].
  exists v_s. split; [exact Hrun | exact (Hrelated n ltac:(lia) v_s Hrun)].
Qed.

Corollary concore_completeness_exists : forall Φ Γs Γc σ e_s e_c v_c,
  σ ⊨ Φ -> contains_env σ Γs Γc -> contains_expr σ e_s e_c ->
  concore_expr e_c -> concrete_env Γc -> budget_total Φ Γs e_s -> Γc ⊢ᶜ e_c ⇓ᶜ v_c ->
  exists k v_s, eval (Fin k) Φ Γs e_s v_s /\ contains_val σ v_s v_c.
Proof.
  intros Φ Γs Γc σ e_s e_c v_c Hm HΓ He Hec HΓc Htotal Heval.
  destruct (concore_completeness_budget Φ Γs Γc σ e_s e_c v_c Hm HΓ He Hec HΓc Htotal Heval)
    as [h Hh].
  exists h. exact (Hh h (Nat.le_refl h)).
Qed.

End Completeness.
