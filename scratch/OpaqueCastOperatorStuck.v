From SymCoreTheory Require Import SymCore ConCore.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

Section Scratch.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : ConCoreLaws}.

(* ==========================================================================
   Applying a cast whose coercion is not an arrow is stuck.

   This is the fact that pays for deleting Rule App-Cast-Opaque. Figure 3
   has five rules that can look at an application: App-Abs, App-Spine,
   App-Prim, App-Cast and App-Bot. On the shape

       (e ⊲ γ) ea      with γ not an arrow

   every one of them is refused:

     App-Abs   wants a closure in operator position, not a cast;
     App-Bot   wants a bottom in operator position, not a cast;
     App-Prim  wants the spine head to be a primitive, and the head of this
               spine is the cast;
     App-Cast  wants γ to split into an argument coercion and a result
               coercion, and this one does not split;
     App-Spine now refuses EVERY cast operator, which is the change.

   So the term has no value. That holds for symbolic evaluation at any
   satisfiable path condition and, as a special case, for concrete
   evaluation at pc_true. The two sides are stuck on the same shape, which
   is the whole point: soundness never has to replay a step that the
   concrete side cannot take.
   ========================================================================== *)

Lemma eval_app_cast_non_arrow_stuck : forall Φ Γ eb γ ea v,
  sat Φ = true ->
  decomp_coerc_arrow γ = None ->
  Φ ; Γ ⊢ EApp (ECast eb γ) ea ⇓ v ->
  False.
Proof.
  intros Φ Γ eb γ ea v Hsat Hdec Heval.
  inversion Heval; subst.
  - (* Rule Con: the spine head is the cast, not a constructor *)
    no_con_head.
  - (* Rule App-Spine: the operator is a cast *)
    match goal with
    | [ H : is_cast (ECast eb γ) = false |- _ ] => discriminate H
    end.
  - (* Rule App-Prim: the spine head is the cast, not a primitive *)
    match goal with
    | [ H : unspool_app (EApp (ECast eb γ) ea) [] = _ |- _ ] =>
        simpl in H; injection H as Hh _; discriminate
    end.
  - (* Rule App-Cast: the coercion does not split *)
    match goal with
    | [ H : decomp_coerc_arrow γ = Some _ |- _ ] =>
        rewrite Hdec in H; discriminate
    end.
  - (* Rule Prune: the path condition holds *)
    match goal with
    | [ H : sat Φ = false |- _ ] => rewrite Hsat in H; discriminate
    end.
Qed.

(* ==========================================================================
   The concrete side is stuck on the SAME term, not on a different one.

   Concrete evaluation is symbolic evaluation at pc_true, so the lemma above
   already covers it as a special case. But soundness does not hand the
   concrete side the same term: it hands it a CONCRETION of the symbolic
   term. So the question is whether the concretion still has the stuck
   shape.

   It does, and the reason is Cont_Cast: concretion relates a cast to a cast
   with the SAME coercion. It never changes the coercion, so it never turns
   a coercion that does not split into one that does.
   ========================================================================== *)

Lemma concretion_keeps_the_stuck_shape : forall σ S Γs eb γ ea e_con,
  sym_free_env S Γs ->
  contains σ S (EApp (ECast eb γ) ea) e_con ->
  exists ebc ac,
    e_con = EApp (ECast ebc γ) ac /\ contains σ S eb ebc /\ contains σ S ea ac.
Proof.
  intros σ S Γs eb γ ea e_con Hfree Hcont.
  destruct (contains_app_inv σ S Γs (ECast eb γ) ea e_con Hfree Hcont) as
    [[fc [ac [Heq [Hcont_f Hcont_a]]]] | [Hsolv _]];
    [| exfalso; exact (solvable_not_cast Γs eb γ Hsolv)].
  apply contains_cast_inv in Hcont_f as [ebc [Heq_fc Hcont_b]].
  subst e_con fc.
  exists ebc, ac. split; [reflexivity | split; assumption].
Qed.

Lemma concrete_app_cast_non_arrow_stuck : forall σ S Γs Γc eb γ ea e_con v_con,
  sym_free_env S Γs ->
  contains σ S (EApp (ECast eb γ) ea) e_con ->
  decomp_coerc_arrow γ = None ->
  Γc ⊢ᶜ e_con ⇓ᶜ v_con ->
  False.
Proof.
  intros σ S Γs Γc eb γ ea e_con v_con Hfree Hcont Hdec Heval.
  destruct (concretion_keeps_the_stuck_shape σ S Γs eb γ ea e_con Hfree Hcont)
    as [ebc [ac [Heq _]]].
  subst e_con.
  unfold eval_con in Heval.
  exact (eval_app_cast_non_arrow_stuck pc_true Γc ebc γ ac v_con
           sat_pc_true Hdec Heval).
Qed.

(* ==========================================================================
   Therefore the soundness case for this shape is vacuous.

   concore_soundness assumes the symbolic run converged. On this shape it
   never does, so the case can never be reached. Nothing has to be replayed,
   and nothing is lost.

   Note which hypothesis does the work: only the symbolic one. The concrete
   result above is not needed to close the case - it is there to show the
   two sides agree, which is what makes the change honest rather than merely
   convenient.
   ========================================================================== *)

Theorem soundness_case_for_opaque_cast_operator_is_vacuous :
  forall Φ Γs Γc σ S eb γ ea e_con v_sym,
  σ ⊨ Φ ->
  contains_env σ S Γs Γc ->
  contains σ S (EApp (ECast eb γ) ea) e_con ->
  decomp_coerc_arrow γ = None ->
  Φ ; Γs ⊢ EApp (ECast eb γ) ea ⇓ v_sym ->
  False.
Proof.
  intros Φ Γs Γc σ S eb γ ea e_con v_sym Hmod Henv Hcont Hdec Heval.
  assert (Hsat : sat Φ = true) by (eapply models_sat; eassumption).
  exact (eval_app_cast_non_arrow_stuck Φ Γs eb γ ea v_sym Hsat Hdec Heval).
Qed.

(* Both sides at once, spelled out: neither the symbolic term nor any
   concretion of it has a value. *)
Corollary both_sides_are_stuck_together :
  forall Φ Γs Γc σ S eb γ ea e_con,
  σ ⊨ Φ ->
  contains_env σ S Γs Γc ->
  contains σ S (EApp (ECast eb γ) ea) e_con ->
  decomp_coerc_arrow γ = None ->
  (forall v_sym, ~ (Φ ; Γs ⊢ EApp (ECast eb γ) ea ⇓ v_sym))
  /\ (forall v_con, ~ (Γc ⊢ᶜ e_con ⇓ᶜ v_con)).
Proof.
  intros Φ Γs Γc σ S eb γ ea e_con Hmod Henv Hcont Hdec.
  assert (Hfree : sym_free_env S Γs)
    by (destruct (contains_env_sym_free σ S Γs Γc Henv) as [Hf _]; exact Hf).
  split.
  - intros v_sym Hs.
    exact (soundness_case_for_opaque_cast_operator_is_vacuous
             Φ Γs Γc σ S eb γ ea e_con v_sym Hmod Henv Hcont Hdec Hs).
  - intros v_con Hc.
    exact (concrete_app_cast_non_arrow_stuck σ S Γs Γc eb γ ea e_con v_con
             Hfree Hcont Hdec Hc).
Qed.

End Scratch.
