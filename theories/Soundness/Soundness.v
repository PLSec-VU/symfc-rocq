From SymCoreTheory Require Export Soundness.MergeKeeps.
From Stdlib Require Import Strings.String Lists.List Lia Arith.PeanoNat.
Import ListNotations.

Section Transport.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.
Context {reduce_prim_literal_law : ReducePrimLiteral} {cast_concore_law : CastConcore}.

Lemma contains_lookup : forall σ Γs Γc x ts,
  contains_env σ Γs Γc -> lookup_env Γs x = Some ts ->
  exists tc, lookup_env Γc x = Some tc /\ contains_thunk σ ts tc.
Proof.
  intros σ Γs Γc x ts HΓ. induction HΓ as [| y ts' tc' Γs' Γc' Ht _ IH]; simpl; intros Hl.
  - discriminate.
  - destruct (string_dec x y).
    + injection Hl as <-. exists tc'. auto.
    + exact (IH Hl).
Qed.

Lemma contains_missing_field : forall σ, contains_thunk σ missing_field missing_field.
Proof.
  intros σ. repeat constructor.
Qed.

Lemma contains_bind_fields : forall σ Γs Γc xs ts tc,
  contains_env σ Γs Γc -> Forall2 (contains_thunk σ) ts tc ->
  contains_env σ (bind_fields Γs xs ts) (bind_fields Γc xs tc).
Proof.
  intros σ Γs Γc xs. induction xs as [| x xs IH]; intros ts tc HΓ Hts; simpl.
  - exact HΓ.
  - destruct Hts as [| t t' ts' tc' Ht Hts'].
    + constructor; [apply contains_missing_field | apply IH; auto].
    + constructor; [exact Ht | apply IH; auto].
Qed.

Lemma contains_find_alt : forall σ d alts_s alts_c xs es,
  Forall2 (contains_alt σ) alts_s alts_c -> find_alt d alts_s = Some (xs, es) ->
  exists ec, find_alt d alts_c = Some (xs, ec) /\ contains_expr σ es ec.
Proof.
  intros σ d alts_s alts_c xs es Hall.
  induction Hall as [| a_s a_c rest_s rest_c Ha _ IH]; simpl; intros Hfind.
  - discriminate.
  - destruct Ha as [d' xs' es' ec' He]. destruct (string_dec d d').
    + injection Hfind as <- <-. exists ec'. auto.
    + exact (IH Hfind).
Qed.

Lemma contains_find_alt_none : forall σ d alts_s alts_c,
  Forall2 (contains_alt σ) alts_s alts_c -> find_alt d alts_s = None -> find_alt d alts_c = None.
Proof.
  intros σ d alts_s alts_c Hall.
  induction Hall as [| a_s a_c rest_s rest_c Ha _ IH]; simpl; intros Hfind.
  - reflexivity.
  - destruct Ha as [d' xs' es' ec' He]. destruct (string_dec d d').
    + discriminate.
    + exact (IH Hfind).
Qed.

Lemma contains_no_alt_matches : forall σ vs vc alts_s alts_c,
  contains_val σ vs vc -> Forall2 (contains_alt σ) alts_s alts_c ->
  no_alt_matches vs alts_s -> no_alt_matches vc alts_c.
Proof.
  intros σ vs vc alts_s alts_c Hv Halts Hno.
  destruct Hv; simpl in *; try exact I; try contradiction.
  exact (contains_find_alt_none σ d alts_s alts_c Halts Hno).
Qed.

Lemma concrete_forces_output : forall g ts vs,
  Forall2 (force g pc_true) ts vs -> Forall concrete_thunk ts -> Forall concrete_value vs.
Proof.
  intros g ts vs Hall. induction Hall as [| t v ts' vs' Ht _ IH]; intros Hts.
  - constructor.
  - inversion Hts; subst. constructor; [exact (concrete_force_output g t v Ht ltac:(assumption)) | auto].
Qed.

End Transport.

Section Soundness.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.
Context {reduce_prim_literal_law : ReducePrimLiteral} {cast_concore_law : CastConcore}
  {models_sat_law : ModelsSat} {reduce_prim_contains_law : ReducePrimContains}
  {cast_contains_law : CastContains} {subst_contains_law : SubstContains}.

Definition sound_eval σ (g : fuel) Φ Γs e_s v_s : Prop :=
  σ ⊨ Φ -> forall Γc e_c,
  contains_env σ Γs Γc -> contains_expr σ e_s e_c -> concrete_env Γc -> concore_expr e_c ->
  exists v_c, eval g pc_true Γc e_c v_c /\ contains_val σ v_s v_c.
Definition sound_apply σ (g : fuel) Φ Γs vf_s e_s v_s : Prop :=
  σ ⊨ Φ -> forall Γc vf_c e_c,
  contains_env σ Γs Γc -> contains_val σ vf_s vf_c -> contains_expr σ e_s e_c ->
  concrete_env Γc -> concrete_value vf_c -> concore_expr e_c ->
  exists v_c, apply g pc_true Γc vf_c e_c v_c /\ contains_val σ v_s v_c.
Definition sound_prim σ (g : fuel) Φ op ts_s v_s : Prop :=
  σ ⊨ Φ -> forall ts_c,
  Forall2 (contains_thunk σ) ts_s ts_c -> Forall concrete_thunk ts_c ->
  exists v_c, prim_app g pc_true op ts_c v_c /\ contains_val σ v_s v_c.
Definition sound_force σ (g : fuel) Φ t_s v_s : Prop :=
  σ ⊨ Φ -> forall t_c,
  contains_thunk σ t_s t_c -> concrete_thunk t_c ->
  exists v_c, force g pc_true t_c v_c /\ contains_val σ v_s v_c.
Definition sound_select σ (g : fuel) Φ c_s tthen_s telse_s v_s : Prop :=
  σ ⊨ Φ -> forall c_c tthen_c telse_c,
  contains_val σ c_s c_c -> contains_thunk σ tthen_s tthen_c ->
  contains_thunk σ telse_s telse_c ->
  concrete_value c_c -> concrete_thunk tthen_c -> concrete_thunk telse_c ->
  exists v_c, select g pc_true c_c tthen_c telse_c v_c /\ contains_val σ v_s v_c.
Definition sound_fold σ (g : fuel) Φ Γs vs_s alts_s v_s : Prop :=
  σ ⊨ Φ -> forall Γc vs_c alts_c,
  contains_env σ Γs Γc -> contains_val σ vs_s vs_c -> Forall2 (contains_alt σ) alts_s alts_c ->
  concrete_env Γc -> concrete_value vs_c -> Forall concore_alt alts_c ->
  exists v_c, fold_alts g pc_true Γc vs_c alts_c v_c /\ contains_val σ v_s v_c.

Lemma forces_sound : forall σ g Φ ts_s vs_s,
  Forall2 (sound_force σ g Φ) ts_s vs_s -> σ ⊨ Φ ->
  forall ts_c, Forall2 (contains_thunk σ) ts_s ts_c -> Forall concrete_thunk ts_c ->
  exists vs_c, Forall2 (force g pc_true) ts_c vs_c /\ Forall2 (contains_val σ) vs_s vs_c.
Proof.
  intros σ g Φ ts_s vs_s Hall Hm.
  induction Hall as [| t v ts' vs' Ht _ IH]; intros ts_c Hts Hconc.
  - inversion Hts; subst. exists []. split; constructor.
  - inversion Hts as [| ? t_c ? ts_c' Htc Hts']; subst. inversion Hconc; subst.
    destruct (Ht Hm t_c Htc ltac:(assumption)) as [v_c [Hf Hv]].
    destruct (IH ts_c' Hts' ltac:(assumption)) as [vs_c [Hfs Hvs]].
    exists (v_c :: vs_c). split; constructor; assumption.
Qed.

Ltac enter_sound_case :=
  unfold sound_eval, sound_apply, sound_prim, sound_force, sound_select, sound_fold in *.

Ltac discharge_premise :=
  solve
    [ eassumption
    | unfold extend_env; constructor; [constructor |]; eassumption
    | apply Forall2_app; [eassumption | constructor; [constructor; eassumption | constructor]]
    | constructor; eassumption
    | apply contains_bind_fields; eassumption
    | unfold extend_env in *; eauto with concrete ].

Ltac fire IH := edestruct IH as [?v_c [?Hrun ?Hrel]]; [discharge_premise .. |].

Ltac invert_contains_prim :=
  match goal with
  | H : contains_prim _ _ _ |- _ => apply contains_prim_target in H; subst
  end.

Lemma lockstep_sound : forall σ,
  (forall g Φ Γ e v, eval g Φ Γ e v -> sound_eval σ g Φ Γ e v) /\
  (forall g Φ Γ vf e v, apply g Φ Γ vf e v -> sound_apply σ g Φ Γ vf e v) /\
  (forall g Φ op ts v, prim_app g Φ op ts v -> sound_prim σ g Φ op ts v) /\
  (forall g Φ t v, force g Φ t v -> sound_force σ g Φ t v) /\
  (forall g Φ c tthen telse v, select g Φ c tthen telse v ->
     sound_select σ g Φ c tthen telse v) /\
  (forall g Φ Γ vs alts v, fold_alts g Φ Γ vs alts v -> sound_fold σ g Φ Γ vs alts v).
Proof.
  intros σ.
  apply (eval_mut_ind (sound_eval σ) (sound_apply σ) (sound_prim σ) (sound_force σ)
    (sound_select σ) (sound_fold σ)); enter_sound_case.
  - intros f Φ Γ x t v Hl Hf IH Hm Γc e_c HΓ He HΓc Hec. inversion He; subst.
    destruct (contains_lookup σ Γ Γc x t HΓ Hl) as [tc [Hlc Htc]].
    destruct (IH Hm tc Htc (concrete_lookup Γc x tc HΓc Hlc)) as [vc [Hfc Hvc]].
    exists vc. split; [econstructor; eassumption | exact Hvc].
  - intros f Φ Γ l Hm Γc e_c HΓ He HΓc Hec. inversion He; subst.
    eexists; split; [constructor | repeat constructor].
  - intros f Φ Γ s Hm Γc e_c HΓ He HΓc Hec. inversion He; subst; [inversion Hec |].
    eexists; split; [constructor | repeat constructor].
  - intros f Φ Γ d Hm Γc e_c HΓ He HΓc Hec. inversion He; subst.
    eexists; split; [constructor | repeat constructor].
  - intros f Φ Γ op v Hp IH Hm Γc e_c HΓ He HΓc Hec. inversion He; subst.
    destruct (IH Hm [] (Forall2_nil _) (Forall_nil _)) as [vc [Hpc Hvc]].
    exists vc. split; [constructor; exact Hpc | exact Hvc].
  - intros f Φ Γ ef ea vf v Hef IHf Hea IHa Hm Γc e_c HΓ He HΓc Hec.
    inversion He; subst. inversion Hec; subst.
    fire IHf. fire IHa. exists v_c0. split; [econstructor; eassumption | exact Hrel0].
  - intros f Φ Γ x b Hm Γc e_c HΓ He HΓc Hec. inversion He; subst.
    eexists; split; [constructor | constructor; assumption].
  - intros f Φ Γ e γ v He' IH Hm Γc e_c HΓ He HΓc Hec. inversion He; subst.
    inversion Hec; subst. fire IH.
    exists (cast_value v_c γ). split; [constructor; exact Hrun | apply cast_contains; exact Hrel].
  - intros f Φ Γ b Hm Γc e_c HΓ He HΓc Hec. inversion He; subst.
    eexists; split; [constructor | constructor; assumption].
  - intros f Φ Γ es alts vs v Hes IHs Hfold IHfold Hm Γc e_c HΓ He HΓc Hec.
    inversion He; subst. inversion Hec; subst. fire IHs.
    assert (Hvsc : concrete_value v_c) by eauto with concrete.
    pose proof (merge_keeps σ vs v_c Hrel) as Hmerged.
    fire IHfold. exists v_c0. split; [| exact Hrel0].
    econstructor; [exact Hrun | rewrite concrete_merge by exact Hvsc; exact Hrun0].
  - intros f Φ Γ γ Hm Γc e_c HΓ He HΓc Hec. inversion He; subst.
    eexists; split; [constructor | rewrite (subst_coerc_contains σ Γ Γc γ HΓ); constructor].
  - intros f Φ Γ τ Hm Γc e_c HΓ He HΓc Hec. inversion He; subst.
    eexists; split; [constructor | rewrite (subst_type_contains σ Γ Γc τ HΓ); constructor].
  - intros f Φ Γ e Hs Hm. rewrite (models_sat σ Φ Hm) in Hs. discriminate.
  - intros Φ Γ e Hm Γc e_c HΓ He HΓc Hec.
    eexists; split; [constructor | repeat constructor].
  - intros g Φ Γ d ts e Hm Γc vf_c e_c HΓ Hvf He HΓc Hvfc Hec. inversion Hvf; subst.
    eexists; split; [constructor |].
    constructor. apply Forall2_app; [assumption | constructor; [constructor; assumption | constructor]].
  - intros g Φ Γ Γ' x b e v Hb IH Hm Γc vf_c e_c HΓ Hvf He HΓc Hvfc Hec.
    inversion Hvf; subst. inversion Hvfc; subst. fire IH.
    exists v_c. split; [constructor; exact Hrun | exact Hrel].
  - intros g Φ Γ op ts e v Hp IH Hm Γc vf_c e_c HΓ Hvf He HΓc Hvfc Hec.
    inversion Hvf; subst. inversion Hvfc; subst. fire IH.
    exists v_c. split; [constructor; exact Hrun | exact Hrel].
  - intros g Φ Γ v' γ γa γr e v Hd Ha IH Hm Γc vf_c e_c HΓ Hvf He HΓc Hvfc Hec.
    inversion Hvf; subst. inversion Hvfc; subst. fire IH.
    exists (VCast v_c γr). split; [econstructor; eassumption | constructor; exact Hrel].
  - intros g Φ Γ b e Hm Γc vf_c e_c HΓ Hvf He HΓc Hvfc Hec. inversion Hvf; subst.
    eexists; split; [constructor | constructor; assumption].
  - intros g Φ Γ p vt vf e vt' vf' Ht IHt Hf IHf Hm Γc vf_c e_c HΓ Hvf He HΓc Hvfc Hec.
    inversion Hvf; subst.
    + fire IHt. exists v_c. split; [exact Hrun | apply ite_keeps; assumption].
    + fire IHf. exists v_c. split; [exact Hrun | apply ite_keeps_false; assumption].
  - intros g Φ op ts Hlt Hm ts_c Hts Hconc.
    eexists; split; [constructor; rewrite <- (Forall2_length Hts); exact Hlt | constructor; exact Hts].
  - intros g Φ tc tthen telse c v Hc IHc Hs IHs Hm ts_c Hts Hconc.
    inversion Hts as [| ? tcc ? r1 Htc Hr1]; subst.
    inversion Hr1 as [| ? tthenc ? r2 Hthen Hr2]; subst.
    inversion Hr2 as [| ? telsec ? r3 Helse Hr3]; subst.
    inversion Hr3; subst. invert_concrete_shapes.
    fire IHc. assert (concrete_value v_c) by eauto with concrete.
    fire IHs. exists v_c0. split; [econstructor; eassumption | exact Hrel0].
  - intros g Φ op ts vs Hne Hlen Hall IHall Hm ts_c Hts Hconc.
    destruct (forces_sound σ g Φ ts vs IHall Hm ts_c Hts Hconc) as [vs_c [Hfc Hvs]].
    exists (lift_prim op vs_c). split.
    + constructor; [exact Hne | rewrite <- (Forall2_length Hts); exact Hlen | exact Hfc].
    + apply lift_prim_keeps.
      * rewrite <- (Forall2_length Hall). exact Hlen.
      * exact Hvs.
      * exact (concrete_forces_output g ts_c vs_c Hfc Hconc).
  - intros g Φ Γ e v He IH Hm t_c Ht Htc. inversion Ht; subst. inversion Htc; subst.
    fire IH. exists v_c. split; [constructor; exact Hrun | exact Hrel].
  - intros g Φ p tthen telse vt vf Ht IHt Hf IHf Hm t_c Htt Htc. inversion Htt; subst.
    + fire IHt. exists v_c. split; [exact Hrun | apply ite_keeps; assumption].
    + fire IHf. exists v_c. split; [exact Hrun | apply ite_keeps_false; assumption].
  - intros g Φ tthen telse v Ht IH Hm c_c tthen_c telse_c Hc Hthen Helse Hcc Hthenc Helsec.
    inversion Hc; subst. invert_contains_prim. fire IH.
    exists v_c. split; [constructor; exact Hrun | exact Hrel].
  - intros g Φ l tthen telse v Hl Hf IH Hm c_c tthen_c telse_c Hc Hthen Helse Hcc Hthenc
      Helsec.
    inversion Hc; subst. invert_contains_prim. fire IH.
    exists v_c. split; [apply Select_False; assumption | exact Hrel].
  - intros g Φ p tthen telse vt vf Hp Ht IHt Hf IHf Hm c_c tthen_c telse_c Hc Hthen Helse Hcc
      Hthenc Helsec.
    inversion Hc; subst. invert_contains_prim.
    destruct (lit_eq_dec (prim_denote σ p) lit_true) as [Htrue | Hfalse].
    + assert (Hm' : σ ⊨ pc_and Φ p) by (apply models_and; split; [exact Hm | exact Htrue]).
      fire IHt. exists v_c. split.
      * rewrite Htrue. apply Select_True. exact Hrun.
      * apply ite_keeps; [exact Htrue | exact Hrel].
    + assert (Hnot : σ ⊨ pc_not p) by (apply models_not; exact Hfalse).
      assert (Hm' : σ ⊨ pc_and Φ (pc_not p)) by (apply models_and; split; assumption).
      fire IHf. exists v_c. split.
      * apply Select_False; assumption.
      * apply ite_keeps_false; assumption.
  - intros g Φ b tthen telse Hm c_c tthen_c telse_c Hc Hthen Helse Hcc Hthenc Helsec.
    inversion Hc; subst. eexists; split; [constructor | constructor; assumption].
  - intros g Φ p ct cf tthen telse vt vf Ht IHt Hf IHf Hm c_c tthen_c telse_c Hc Hthen Helse
      Hcc Hthenc Helsec.
    inversion Hc; subst.
    + fire IHt. exists v_c. split; [exact Hrun | apply ite_keeps; assumption].
    + fire IHf. exists v_c. split; [exact Hrun | apply ite_keeps_false; assumption].
  - intros g Φ Γ d ts alts xs ep v Hfind He IH Hm Γc vs_c alts_c HΓ Hvs Halts HΓc Hvsc
      Haltsc.
    inversion Hvs; subst. inversion Hvsc; subst.
    destruct (contains_find_alt σ d alts alts_c xs ep Halts Hfind) as [epc [Hfindc Hep]].
    fire IH. exists v_c. split; [econstructor; eassumption | exact Hrel].
  - intros g Φ Γ b alts Hm Γc vs_c alts_c HΓ Hvs Halts HΓc Hvsc Haltsc.
    inversion Hvs; subst. eexists; split; [constructor | constructor; assumption].
  - intros g Φ Γ p vt vf alts vt' vf' Ht IHt Hf IHf Hm Γc vs_c alts_c HΓ Hvs Halts HΓc Hvsc
      Haltsc.
    inversion Hvs; subst.
    + assert (Hm' : σ ⊨ pc_and Φ p) by (apply models_and; split; assumption).
      fire IHt. exists v_c. split; [exact Hrun | apply ite_keeps; assumption].
    + assert (Hm' : σ ⊨ pc_and Φ (pc_not p)) by (apply models_and; split; assumption).
      fire IHf. exists v_c. split; [exact Hrun | apply ite_keeps_false; assumption].
  - intros g Φ Γ v alts Hno Hm Γc vs_c alts_c HΓ Hvs Halts HΓc Hvsc Haltsc.
    exists (VBot BUndefined). split; [| repeat constructor].
    constructor. exact (contains_no_alt_matches σ v vs_c alts alts_c Hvs Halts Hno).
Qed.

Theorem concore_soundness : forall Φ Γs Γc σ e_s e_c v_s,
  σ ⊨ Φ -> contains_env σ Γs Γc -> contains_expr σ e_s e_c ->
  concore_expr e_c -> concrete_env Γc ->
  Φ ; Γs ⊢ e_s ⇓ v_s ->
  exists v_c, Γc ⊢ᶜ e_c ⇓ᶜ v_c /\ contains_val σ v_s v_c.
Proof.
  intros Φ Γs Γc σ e_s e_c v_s Hm HΓ He Hec HΓc Heval.
  exact (proj1 (lockstep_sound σ) _ _ _ _ _ Heval Hm Γc e_c HΓ He HΓc Hec).
Qed.

End Soundness.
