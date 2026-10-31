From SymCoreTheory Require Export Model.Reducer Soundness.Laws.
From Stdlib Require Import Lists.List Arith.PeanoNat.
Import ListNotations.

#[export] Instance model_solver : SymCoreSolver :=
  (@Build_SymCoreSolver _
    (fun _ => true) (PLit true) eq_refl model_reduce_prim
    VCast (fun _ γ => γ) (fun _ τ => τ)).

Instance model_reduce_prim_literal : ReducePrimLiteral.
Proof.
  intros op ls Hlen. change (model_reduce_prim op (map PLit ls) = VPrim (PLit (prim_value op ls))).
  unfold model_reduce_prim. rewrite all_literals_map_plit, Hlen, Nat.eqb_refl.
  reflexivity.
Qed.

Instance model_cast_concore : CastConcore.
Proof. intros v γ Hv. constructor. exact Hv. Qed.

Instance model_models_sat : ModelsSat.
Proof. intros σ Φ _. reflexivity. Qed.

Lemma forall2_contains_prim_denote : forall σ ps ls,
  Forall2 (contains_prim σ) ps (map PLit ls) -> map (prim_denote σ) ps = ls.
Proof.
  intros σ ps. induction ps as [| p rest IH]; intros [| l ls] H; simpl in H;
    inversion H; subst; simpl; try reflexivity.
  f_equal; [apply contains_prim_denote; assumption | apply IH; assumption].
Qed.

Instance model_reduce_prim_contains : ReducePrimContains.
Proof.
  intros σ op ps ls Hlen H. change (contains_val σ (model_reduce_prim op ps) (VPrim (PLit (prim_value op ls)))).
  unfold model_reduce_prim.
  pose proof (forall2_contains_prim_denote σ ps ls H) as Hden.
  destruct (all_literals ps) as [ls'|] eqn:E.
  - apply all_literals_sound in E. subst ps.
    rewrite length_map in Hlen. rewrite Hlen, Nat.eqb_refl.
    assert (ls' = ls) as ->.
    { rewrite map_map in Hden. simpl in Hden. rewrite map_id in Hden. exact Hden. }
    repeat constructor.
  - constructor. apply Contains_PDenote; [exact Hlen |].
    change (prim_value op (map (prim_denote σ) ps) = prim_value op ls).
    rewrite Hden. reflexivity.
Qed.

Instance model_cast_contains : CastContains.
Proof. intros σ vs vc γ H. constructor. exact H. Qed.

Instance model_subst_contains : SubstContains.
Proof.
  split; intros σ Γs Γc x _; reflexivity.
Qed.

#[export] Instance model_laws : ConCoreLaws :=
  concore_laws model_reduce_prim_literal model_cast_concore model_models_sat
    model_reduce_prim_contains model_cast_contains model_subst_contains.
