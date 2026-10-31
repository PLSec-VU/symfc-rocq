From SymCoreTheory Require Export ConCore.Preservation.
From Stdlib Require Import Strings.String Lists.List Lia Arith.PeanoNat.
Import ListNotations.

Section ConCore.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.
Context {reduce_prim_literal_law : ReducePrimLiteral} {cast_concore_law : CastConcore}.

Definition functional_eval g Φ Γ e v : Prop :=
  g = Inf -> Φ = pc_true -> concrete_env Γ -> concore_expr e ->
  forall v', eval g Φ Γ e v' -> v = v'.
Definition functional_apply g Φ Γ vf e v : Prop :=
  g = Inf -> Φ = pc_true -> concrete_env Γ -> concrete_value vf -> concore_expr e ->
  forall v', apply g Φ Γ vf e v' -> v = v'.
Definition functional_prim g Φ op ts v : Prop :=
  g = Inf -> Φ = pc_true -> Forall concrete_thunk ts ->
  forall v', prim_app g Φ op ts v' -> v = v'.
Definition functional_force g Φ t v : Prop :=
  g = Inf -> Φ = pc_true -> concrete_thunk t ->
  forall v', force g Φ t v' -> v = v'.
Definition functional_select g Φ c tthen telse v : Prop :=
  g = Inf -> Φ = pc_true -> concrete_value c -> concrete_thunk tthen -> concrete_thunk telse ->
  forall v', select g Φ c tthen telse v' -> v = v'.
Definition functional_fold g Φ Γ vs alts v : Prop :=
  g = Inf -> Φ = pc_true -> concrete_env Γ -> concrete_value vs -> Forall concore_alt alts ->
  forall v', fold_alts g Φ Γ vs alts v' -> v = v'.

Lemma forces_functional : forall ts vs,
  Forall2 (functional_force Inf pc_true) ts vs -> Forall concrete_thunk ts ->
  forall vs', Forall2 (force Inf pc_true) ts vs' -> vs = vs'.
Proof.
  intros ts vs Hall. induction Hall as [| t v ts' vs' Ht _ IH]; intros Hts ws Hws.
  - inversion Hws. reflexivity.
  - inversion Hts; subst. inversion Hws; subst. f_equal; [apply Ht; auto | apply IH; auto].
Qed.

Ltac enter_functional_case :=
  unfold functional_eval, functional_apply, functional_prim, functional_force,
    functional_select, functional_fold in *;
  intros;
  match goal with
  | Hfuel : Spent = Inf |- _ => discriminate Hfuel
  | Hfuel : Live _ = Inf |- _ => injection Hfuel as ->
  | Hfuel : ?g = Inf |- _ => subst g
  end;
  match goal with
  | HΦ : ?Φ = pc_true |- _ => subst Φ
  end;
  simpl dec in *;
  repeat match goal with
  | IH : Inf = Inf -> _ |- _ => specialize (IH eq_refl)
  | IH : pc_true = pc_true -> _ |- _ => specialize (IH eq_refl)
  end.

Ltac invert_second_derivation :=
  match goal with
  | H : eval Inf pc_true _ _ ?w |- _ = ?w => inversion H; subst
  | H : apply Inf pc_true _ _ _ ?w |- _ = ?w => inversion H; subst
  | H : prim_app Inf pc_true _ _ ?w |- _ = ?w => inversion H; subst
  | H : force Inf pc_true _ ?w |- _ = ?w => inversion H; subst
  | H : select Inf pc_true _ _ _ ?w |- _ = ?w => inversion H; subst
  | H : fold_alts Inf pc_true _ _ _ ?w |- _ = ?w => inversion H; subst
  end;
  simpl dec in *.

Ltac invert_concrete_inputs :=
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

Ltac refute_rule_overlap :=
  solve
    [ rewrite sat_pc_true in *; discriminate
    | match goal with Hp : is_plit (PLit _) = false |- _ => discriminate Hp end
    | match goal with Hne : ?x <> ?x |- _ => contradiction (Hne eq_refl) end
    | rewrite op_ite_arity in *; simpl in *; lia
    | simpl in *; lia
    | simpl in *; congruence ].

Ltac unify_lookups :=
  repeat match goal with
  | H1 : ?a = Some ?x, H2 : ?a = Some ?y |- _ =>
      rewrite H1 in H2; injection H2; clear H2; intros; subst
  end.

Hint Constructors concrete_value concrete_thunk concrete_env concore_expr concore_bottom
  concore_alt Forall : concrete.
Hint Resolve concrete_lookup concrete_bind_fields concore_find_alt concrete_merged
  concrete_eval_output concrete_apply_output concrete_force_output forall_snoc : concrete.

Ltac discharge_input_premises :=
  repeat match goal with
  | IH : ?A -> _ |- _ =>
      let HA := fresh in
      assert A as HA by (unfold extend_env in *; eauto with concrete);
      specialize (IH HA); clear HA
  end.

Ltac unify_outputs :=
  repeat match goal with
  | IH : forall w, _ -> _ = w, H : _ |- _ =>
      let Heq := fresh in
      pose proof (IH _ H) as Heq;
      lazymatch type of Heq with
      | ?a = ?a => fail
      | _ => clear IH; subst
      end
  end;
  repeat match goal with
  | Hall : Forall2 _ ?ts ?vs, Hws : Forall2 (force Inf pc_true) ?ts ?ws |- _ =>
      let Heq := fresh in
      pose proof (forces_functional ts vs Hall ltac:(assumption) ws Hws) as Heq;
      clear Hall; subst
  end.

Ltac close_functional_case :=
  enter_functional_case; invert_second_derivation; invert_concrete_inputs;
  try refute_rule_overlap; unify_lookups; discharge_input_premises; unify_outputs;
  try reflexivity.

Lemma eval_functional :
  (forall g Φ Γ e v, eval g Φ Γ e v -> functional_eval g Φ Γ e v) /\
  (forall g Φ Γ vf e v, apply g Φ Γ vf e v -> functional_apply g Φ Γ vf e v) /\
  (forall g Φ op ts v, prim_app g Φ op ts v -> functional_prim g Φ op ts v) /\
  (forall g Φ t v, force g Φ t v -> functional_force g Φ t v) /\
  (forall g Φ c tthen telse v, select g Φ c tthen telse v ->
     functional_select g Φ c tthen telse v) /\
  (forall g Φ Γ vs alts v, fold_alts g Φ Γ vs alts v -> functional_fold g Φ Γ vs alts v).
Proof.
  apply (eval_mut_ind functional_eval functional_apply functional_prim functional_force
    functional_select functional_fold); close_functional_case.
Qed.

Theorem concore_eval_deterministic : forall Γ e v1 v2,
  concrete_env Γ -> concore_expr e -> Γ ⊢ᶜ e ⇓ᶜ v1 -> Γ ⊢ᶜ e ⇓ᶜ v2 -> v1 = v2.
Proof.
  intros Γ e v1 v2 HΓ He H1 H2.
  exact (proj1 eval_functional _ _ _ _ _ H1 eq_refl eq_refl HΓ He v2 H2).
Qed.

End ConCore.
