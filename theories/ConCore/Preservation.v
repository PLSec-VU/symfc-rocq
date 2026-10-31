From SymCoreTheory Require Export ConCore.Programs.
From Stdlib Require Import Strings.String Lists.List Lia Arith.PeanoNat.
Import ListNotations.

Section ConCore.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.

Class ReducePrimLiteral : Prop := reduce_prim_literal : forall op ls,
  length ls = primop_arity op -> reduce_prim op (map PLit ls) = VPrim (PLit (prim_value op ls)).
Class CastConcore : Prop := cast_concore : forall v γ, concrete_value v -> concrete_value (cast_value v γ).

Context {reduce_prim_literal_law : ReducePrimLiteral} {cast_concore_law : CastConcore}.

Lemma concrete_lift_prim_from : forall op vs ls,
  length ls + length vs = primop_arity op ->
  Forall concrete_value vs ->
  concrete_value (lift_prim_from op (map PLit ls) vs).
Proof.
  intros op vs. induction vs as [| v rest IH]; intros ls Hlen Hvs; simpl.
  - rewrite reduce_prim_literal by (simpl in Hlen; lia). constructor.
  - inversion Hvs as [| ? ? Hv Hrest]; subst.
    destruct Hv; simpl; try solve [constructor; assumption | repeat constructor].
    change [PLit l] with (map PLit [l]). rewrite <- map_app. apply IH; [rewrite length_app; simpl in *; lia | exact Hrest].
Qed.

Lemma concrete_lift_prim : forall op vs,
  length vs = primop_arity op -> Forall concrete_value vs -> concrete_value (lift_prim op vs).
Proof.
  intros op vs Hlen Hvs. exact (concrete_lift_prim_from op vs [] Hlen Hvs).
Qed.

Definition preserves_eval g Φ Γ e v : Prop :=
  g = Inf -> Φ = pc_true -> concrete_env Γ -> concore_expr e -> concrete_value v.
Definition preserves_apply g Φ Γ vf e v : Prop :=
  g = Inf -> Φ = pc_true -> concrete_env Γ -> concrete_value vf -> concore_expr e ->
  concrete_value v.
Definition preserves_prim g Φ (op : primop) ts v : Prop :=
  g = Inf -> Φ = pc_true -> Forall concrete_thunk ts -> concrete_value v.
Definition preserves_force g Φ t v : Prop :=
  g = Inf -> Φ = pc_true -> concrete_thunk t -> concrete_value v.
Definition preserves_select g Φ c tthen telse v : Prop :=
  g = Inf -> Φ = pc_true -> concrete_value c -> concrete_thunk tthen -> concrete_thunk telse ->
  concrete_value v.
Definition preserves_fold g Φ Γ vs alts v : Prop :=
  g = Inf -> Φ = pc_true -> concrete_env Γ -> concrete_value vs -> Forall concore_alt alts ->
  concrete_value v.

Lemma forces_preserve_concrete : forall ts vs,
  Forall2 (preserves_force Inf pc_true) ts vs -> Forall concrete_thunk ts ->
  Forall concrete_value vs.
Proof.
  intros ts vs Hall. induction Hall as [| t v ts' vs' Ht _ IH]; intros Hts.
  - constructor.
  - inversion Hts; subst. constructor; [apply Ht; auto | auto].
Qed.

Ltac enter_preserve_case :=
  unfold preserves_eval, preserves_apply, preserves_prim, preserves_force, preserves_select,
    preserves_fold in *;
  intros;
  match goal with
  | Hfuel : Spent = Inf |- _ => discriminate Hfuel
  | Hfuel : Live _ = Inf |- _ => injection Hfuel as ->
  | Hfuel : ?g = Inf |- _ => subst g
  end;
  match goal with
  | HΦ : ?Φ = pc_true |- _ => subst Φ
  end;
  simpl dec in *.

Ltac use_preserve_hyps :=
  repeat match goal with
  | IH : Inf = Inf -> _ |- _ => specialize (IH eq_refl)
  | IH : pc_true = pc_true -> _ |- _ => specialize (IH eq_refl)
  end.

Ltac invert_concrete_shapes :=
  repeat match goal with
  | H : concore_expr (_ _) |- _ => inversion H; subst; clear H
  | H : concore_expr (_ _ _) |- _ => inversion H; subst; clear H
  | H : concrete_value (_ _) |- _ => inversion H; subst; clear H
  | H : concrete_value (_ _ _) |- _ => inversion H; subst; clear H
  | H : concrete_value (_ _ _ _) |- _ => inversion H; subst; clear H
  | H : concrete_thunk (_ _ _) |- _ => inversion H; subst; clear H
  | H : concrete_thunk (_ _ _ _) |- _ => inversion H; subst; clear H
  | H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H
  end.

Lemma forall_snoc : forall (A : Type) (P : A -> Prop) xs x,
  Forall P xs -> P x -> Forall P (xs ++ [x]).
Proof.
  intros A P xs x Hxs Hx. apply Forall_app. split; [exact Hxs | constructor; [exact Hx | constructor]].
Qed.

Lemma concrete_merged : forall v, concrete_value v -> concrete_value (merge v).
Proof.
  intros v Hv. rewrite concrete_merge by exact Hv. exact Hv.
Qed.

Lemma concrete_reduced : forall op ts vs,
  length ts = primop_arity op ->
  Forall2 (preserves_force Inf pc_true) ts vs -> Forall concrete_thunk ts ->
  concrete_value (lift_prim op vs).
Proof.
  intros op ts vs Hlen Hall Hts. apply concrete_lift_prim.
  - rewrite <- (Forall2_length Hall). exact Hlen.
  - exact (forces_preserve_concrete ts vs Hall Hts).
Qed.

Hint Constructors concrete_value concrete_thunk concrete_env concore_expr concore_bottom
  concore_alt Forall : concrete.
Hint Resolve concrete_lookup concrete_bind_fields concore_find_alt cast_concore forall_snoc
  concrete_merged concrete_reduced : concrete.

Ltac close_preserve_case :=
  enter_preserve_case; use_preserve_hyps; unfold extend_env in *; invert_concrete_shapes;
  try solve
    [ rewrite sat_pc_true in *; discriminate
    | match goal with Hp : is_plit (PLit _) = false |- _ => discriminate Hp end
    | eauto with concrete ].

Lemma eval_preserves_concrete :
  (forall g Φ Γ e v, eval g Φ Γ e v -> preserves_eval g Φ Γ e v) /\
  (forall g Φ Γ vf e v, apply g Φ Γ vf e v -> preserves_apply g Φ Γ vf e v) /\
  (forall g Φ op ts v, prim_app g Φ op ts v -> preserves_prim g Φ op ts v) /\
  (forall g Φ t v, force g Φ t v -> preserves_force g Φ t v) /\
  (forall g Φ c tthen telse v, select g Φ c tthen telse v ->
     preserves_select g Φ c tthen telse v) /\
  (forall g Φ Γ vs alts v, fold_alts g Φ Γ vs alts v -> preserves_fold g Φ Γ vs alts v).
Proof.
  apply (eval_mut_ind preserves_eval preserves_apply preserves_prim preserves_force
    preserves_select preserves_fold); close_preserve_case.
Qed.

Lemma concrete_eval_output : forall Γ e v,
  eval Inf pc_true Γ e v -> concrete_env Γ -> concore_expr e -> concrete_value v.
Proof.
  intros Γ e v Heval HΓ He.
  exact (proj1 eval_preserves_concrete _ _ _ _ _ Heval eq_refl eq_refl HΓ He).
Qed.

Lemma concrete_apply_output : forall Γ vf e v,
  apply Inf pc_true Γ vf e v -> concrete_env Γ -> concrete_value vf -> concore_expr e ->
  concrete_value v.
Proof.
  intros Γ vf e v Happ HΓ Hvf He.
  exact (proj1 (proj2 eval_preserves_concrete) _ _ _ _ _ _ Happ eq_refl eq_refl HΓ Hvf He).
Qed.

Lemma concrete_prim_output : forall op ts v,
  prim_app Inf pc_true op ts v -> Forall concrete_thunk ts -> concrete_value v.
Proof.
  intros op ts v Hprim Hts.
  exact (proj1 (proj2 (proj2 eval_preserves_concrete)) _ _ _ _ _ Hprim eq_refl eq_refl Hts).
Qed.

Lemma concrete_force_output : forall t v,
  force Inf pc_true t v -> concrete_thunk t -> concrete_value v.
Proof.
  intros t v Hforce Ht.
  exact (proj1 (proj2 (proj2 (proj2 eval_preserves_concrete))) _ _ _ _ Hforce eq_refl eq_refl
    Ht).
Qed.

Lemma concrete_select_output : forall c tthen telse v,
  select Inf pc_true c tthen telse v -> concrete_value c -> concrete_thunk tthen ->
  concrete_thunk telse -> concrete_value v.
Proof.
  intros c tthen telse v Hselect Hc Hthen Helse.
  exact (proj1 (proj2 (proj2 (proj2 (proj2 eval_preserves_concrete))))
    _ _ _ _ _ _ Hselect eq_refl eq_refl Hc Hthen Helse).
Qed.

Lemma concrete_fold_output : forall Γ vs alts v,
  fold_alts Inf pc_true Γ vs alts v -> concrete_env Γ -> concrete_value vs ->
  Forall concore_alt alts -> concrete_value v.
Proof.
  intros Γ vs alts v Hfold HΓ Hvs Halts.
  exact (proj2 (proj2 (proj2 (proj2 (proj2 eval_preserves_concrete))))
    _ _ _ _ _ _ Hfold eq_refl eq_refl HΓ Hvs Halts).
Qed.

Lemma concore_eval_concrete : forall Γ e v,
  concrete_env Γ -> concore_expr e -> Γ ⊢ᶜ e ⇓ᶜ v -> concrete_value v.
Proof.
  intros Γ e v HΓ He Heval. exact (concrete_eval_output Γ e v Heval HΓ He).
Qed.

End ConCore.
