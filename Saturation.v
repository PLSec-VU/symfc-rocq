From SymCoreTheory Require Import SymCore ConCore Completeness Model.
From Stdlib Require Import Strings.String Lists.List Arith.PeanoNat Lia.
Import ListNotations.

Section Saturation.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.

Inductive argument_count := Exactly | AtLeast.

Definition arity_met (rule : argument_count) (p : primop) (n : nat) : Prop :=
  match rule with
  | Exactly => primop_arity p = n
  | AtLeast => primop_arity p <= n
  end.

Fixpoint spine_ok (rule : argument_count) (n : nat) (e : expr) {struct e} : Prop :=
  match e with
  | EVar _ | ELit _ | ECon _ | ECoercion _ | EType _ => True
  | EPrimOp p => arity_met rule p n
  | EApp f a => spine_ok rule (S n) f /\ spine_ok Exactly 0 a
  | ELam _ b => spine_ok Exactly 0 b
  | ECase s alts =>
      spine_ok rule 0 s /\
      (fix alts_ok (l : list alt) : Prop :=
         match l with
         | nil => True
         | Alt _ _ b :: rest => spine_ok Exactly 0 b /\ alts_ok rest
         end) alts
  | ECast b _ => spine_ok rule 0 b
  | EIf c t f => spine_ok rule 0 c /\ spine_ok rule n t /\ spine_ok rule n f
  | EBot b => bottom_ok b
  | EThunk Γ b => env_ok Γ /\ spine_ok Exactly 0 b
  end
with bottom_ok (b : bottom) : Prop :=
  match b with
  | BRaise e => spine_ok Exactly 0 e
  | _ => True
  end
with env_ok (Γ : environment) : Prop :=
  match Γ with
  | EmptyEnv => True
  | ExtendEnv _ (MkClosure Γ' e) rest => env_ok Γ' /\ spine_ok Exactly 0 e /\ env_ok rest
  end.

Definition saturated (e : expr) : Prop := spine_ok Exactly 0 e.

Definition saturated_env (Γ : environment) : Prop := env_ok Γ.

Definition saturated_alt (a : alt) : Prop :=
  match a with Alt _ _ b => saturated b end.

Lemma alts_ok_forall : forall s alts rule,
  spine_ok rule 0 (ECase s alts) <-> spine_ok rule 0 s /\ Forall saturated_alt alts.
Proof.
  intros s alts rule. simpl. split; intros [Hs Ha]; split; try exact Hs.
  - induction alts as [| [d xs b] rest IH]; constructor; destruct Ha as [Hb Hr];
      [exact Hb | exact (IH Hr)].
  - induction Ha as [| [d xs b] rest Hb _ IH]; [exact I | split; [exact Hb | exact IH]].
Qed.

Fixpoint exact_at_least (e : expr) (n : nat) {struct e} :
  spine_ok Exactly n e -> spine_ok AtLeast n e.
Proof.
  destruct e; simpl; intro H; try exact H.
  - simpl in H. lia.
  - destruct H as [Hf Ha]. exact (conj (exact_at_least e1 (S n) Hf) Ha).
  - destruct H as [Hs Ha]. exact (conj (exact_at_least e 0 Hs) Ha).
  - exact (exact_at_least e 0 H).
  - destruct H as [Hc [Ht Hf]].
    exact (conj (exact_at_least e1 0 Hc) (conj (exact_at_least e2 n Ht) (exact_at_least e3 n Hf))).
Qed.

Fixpoint at_least_more (e : expr) (n m : nat) {struct e} :
  n <= m -> spine_ok AtLeast n e -> spine_ok AtLeast m e.
Proof.
  intros Hle H. destruct e; simpl in *; try exact H.
  - lia.
  - destruct H as [Hf Ha]. split; [| exact Ha].
    apply (at_least_more e1 (S n) (S m)); [lia | exact Hf].
  - destruct H as [Hc [Ht Hf]].
    exact (conj Hc (conj (at_least_more e2 n m Hle Ht) (at_least_more e3 n m Hle Hf))).
Qed.

Fixpoint spine_ok_any_count (e : expr) (rule : argument_count) (n m : nat) {struct e} :
  has_whole_spine_rule (spine_head e) = false -> spine_ok rule n e -> spine_ok rule m e.
Proof.
  intros Hhead H. destruct e; simpl in *; try exact H; try discriminate Hhead.
  destruct H as [Hf Ha]. exact (conj (spine_ok_any_count e1 rule (S n) (S m) Hhead Hf) Ha).
Qed.

Lemma unspool_spine_ok : forall e acc h args rule,
  spine_ok rule (length acc) e -> Forall saturated acc ->
  unspool_app e acc = (h, args) ->
  spine_ok rule (length args) h /\ Forall saturated args.
Proof.
  induction e; intros acc h args rule He Hacc Hu; simpl in Hu;
    try (injection Hu as <- <-; split; assumption).
  destruct He as [Hf Ha].
  exact (IHe1 (e2 :: acc) h args rule Hf (Forall_cons _ Ha Hacc) Hu).
Qed.

Lemma fold_left_spine_ok : forall args h n rule,
  spine_ok rule (length args + n) h -> Forall saturated args ->
  spine_ok rule n (fold_left EApp args h).
Proof.
  induction args as [| a rest IH]; intros h n rule Hh Hargs; simpl in *; [exact Hh |].
  inversion Hargs as [| a0 rest0 Ha Hrest]; subst.
  apply IH; [simpl; exact (conj Hh Ha) | exact Hrest].
Qed.

Lemma saturated_prim_spine : forall e p args,
  saturated e -> unspool_app e [] = (EPrimOp p, args) ->
  length args = primop_arity p.
Proof.
  intros e p args He Hu.
  destruct (unspool_spine_ok e [] (EPrimOp p) args Exactly He (Forall_nil _) Hu) as [Hp _].
  symmetry. exact Hp.
Qed.

Lemma at_least_prim_spine : forall e p args,
  spine_ok AtLeast 0 e -> unspool_app e [] = (EPrimOp p, args) ->
  primop_arity p <= length args.
Proof.
  intros e p args He Hu.
  destruct (unspool_spine_ok e [] (EPrimOp p) args AtLeast He (Forall_nil _) Hu) as [Hp _].
  exact Hp.
Qed.

Lemma lookup_saturated : forall Γ x Γ' e,
  saturated_env Γ -> lookup_env Γ x = Some (Γ', e) ->
  saturated_env Γ' /\ saturated e.
Proof.
  induction Γ as [| y [Γ0 e0] rest IH]; intros x Γ' e HΓ Hl; simpl in Hl; [discriminate |].
  destruct HΓ as [H0 [He0 Hrest]].
  destruct (string_dec x y); [injection Hl as <- <-; split; assumption |].
  exact (IH x Γ' e Hrest Hl).
Qed.

Lemma extend_saturated : forall Γ x Γ' e,
  saturated_env Γ -> saturated_env Γ' -> saturated e ->
  saturated_env (extend_env Γ x Γ' e).
Proof. intros Γ x Γ' e HΓ HΓ' He. simpl. exact (conj HΓ' (conj He HΓ)). Qed.

Lemma extend_multi_saturated : forall Γ xs args Γ',
  saturated_env Γ -> saturated_env Γ' -> Forall saturated args ->
  saturated_env (extend_env_multi Γ xs args Γ').
Proof.
  intros Γ xs. induction xs as [| x xs IH]; intros args Γ' HΓ HΓ' Hargs; simpl; [exact HΓ |].
  destruct args as [| a rest].
  - apply extend_saturated; [apply IH | exact HΓ' | exact I]; assumption.
  - inversion Hargs; subst. apply extend_saturated; [apply IH | |]; assumption.
Qed.

Lemma delay_saturated : forall Γ e,
  saturated_env Γ -> saturated e -> saturated (delay Γ e).
Proof. intros Γ e HΓ He. destruct e; try exact He; exact (conj HΓ He). Qed.

Lemma make_con_app_saturated : forall d args,
  Forall saturated args -> saturated (make_con_app d args).
Proof. intros d args H. apply fold_left_spine_ok; [exact I | exact H]. Qed.

Lemma decompose_con_app_saturated : forall e d args,
  saturated e -> decompose_con_app e = Some (d, args) -> Forall saturated args.
Proof.
  intros e d args He Hd.
  exact (proj2 (unspool_spine_ok e [] (ECon d) args Exactly He (Forall_nil _)
    (decompose_con_app_unspool e d args Hd))).
Qed.

Lemma zip_if_saturated : forall ec l1 l2,
  saturated ec -> Forall saturated l1 -> Forall saturated l2 ->
  Forall saturated (zip_if ec l1 l2).
Proof.
  intros ec l1. induction l1 as [| a1 t1 IH]; intros l2 Hc H1 H2; [constructor |].
  destruct l2 as [| a2 t2]; [constructor |].
  inversion H1; inversion H2; subst.
  constructor; [split; [exact Hc | split; assumption] | apply IH; assumption].
Qed.

Lemma find_alt_saturated : forall d alts xs ep,
  Forall saturated_alt alts -> find_alt d alts = Some (xs, ep) -> saturated ep.
Proof.
  intros d alts xs ep H. induction H as [| [d' xs' b] rest Hb _ IH]; simpl; [discriminate |].
  destruct (string_dec d d'); [intro Heq; injection Heq as <- <-; exact Hb | exact IH].
Qed.

Class ReducePrimKeepsSaturation : Prop :=
reduce_prim_keeps_saturation : forall p args,
  length args = primop_arity p -> Forall saturated args ->
  saturated (reduce_prim p args).

Class CastExprKeepsSaturation : Prop :=
cast_expr_keeps_saturation : forall e γ,
  saturated e -> saturated (cast_expr e γ).

Context {reduce_prim_law : ReducePrimKeepsSaturation} {cast_expr_law : CastExprKeepsSaturation}.

Lemma ite_leaf_saturated : forall Γ ec et ef,
  saturated ec -> saturated et -> saturated ef -> saturated (ite_leaf Γ ec et ef).
Proof.
  intros Γ ec et ef Hc Ht Hf. unfold ite_leaf.
  destruct (decompose_con_app et) as [[d1 a1] |] eqn:E1;
  destruct (decompose_con_app ef) as [[d2 a2] |] eqn:E2.
  1: destruct (andb _ _);
    [ apply make_con_app_saturated; apply zip_if_saturated;
        [exact Hc | exact (decompose_con_app_saturated _ _ _ Ht E1)
                  | exact (decompose_con_app_saturated _ _ _ Hf E2)]
    | exact (conj Hc (conj Ht Hf)) ].
  all: destruct (solvable_dec Γ et); [destruct (solvable_dec Γ ef) |].
  all: try (apply reduce_prim_keeps_saturation;
            [rewrite op_ite_arity; reflexivity | repeat constructor; assumption]).
  all: try exact (conj Hc (conj Ht Hf)).
  all: destruct et; try exact (conj Hc (conj Ht Hf)); destruct ef; try exact (conj Hc (conj Ht Hf)).
  all: repeat (match goal with
               | |- saturated (if ?b then _ else _) => destruct b
               | |- saturated (match ?x with _ => _ end) => destruct x
               end; try exact (conj Hc (conj Ht Hf)); try exact Ht).
  all: exact (conj (proj1 Ht) (conj Hc (conj (proj2 Ht) (proj2 Hf)))).
Qed.

Lemma ite_saturated : forall et Γ ec ef,
  saturated ec -> saturated et -> saturated ef -> saturated (ite Γ ec et ef).
Proof.
  induction et; intros Γ ec ef Hc Ht Hf;
    try (rewrite ite_leaf_of by (left; reflexivity); apply ite_leaf_saturated; assumption).
  destruct ef;
    try (rewrite ite_leaf_of by (right; reflexivity); apply ite_leaf_saturated; assumption).
  rewrite ite_cast. destruct (dec_eqb coercion_eq_dec c c0).
  - exact (IHet Γ ec ef Hc Ht Hf).
  - exact (conj Hc (conj Ht Hf)).
Qed.

Lemma merge_saturated : forall Γ e, saturated e -> saturated (merge Γ e).
Proof.
  intros Γ e He. destruct e; try exact He.
  destruct He as [Hc [Ht Hf]]. exact (ite_saturated _ Γ _ _ Hc Ht Hf).
Qed.

Definition saturates_value (f : fuel) (Φ : path_condition) (Γ : environment) (e v : expr) : Prop :=
  saturated_env Γ -> spine_ok AtLeast 0 e -> saturated v.

Definition saturates_fold (f : fuel) (Φ : path_condition) (Γ : environment) (e : expr)
  (alts : list alt) (v : expr) : Prop :=
  saturated_env Γ -> saturated e -> Forall saturated_alt alts -> saturated v.

Lemma eval_saturates_at_least : forall f Φ Γ e v,
  eval f Φ Γ e v -> saturates_value f Φ Γ e v.
Proof.
  apply (eval_nested_ind saturates_value saturates_fold); unfold saturates_value, saturates_fold.
  - intros f Φ Γ x Γ' e e' Hl _ IH HΓ _.
    destruct (lookup_saturated _ _ _ _ HΓ Hl) as [HΓ' He].
    exact (IH HΓ' (exact_at_least e 0 He)).
  - intros. exact I.
  - intros. exact I.
  - intros f Φ Γ e d args Hu HΓ He. apply make_con_app_saturated.
    destruct (unspool_spine_ok e [] (ECon d) args AtLeast He (Forall_nil _) Hu) as [_ Hargs].
    apply Forall_map. eapply Forall_impl; [| exact Hargs].
    intros a Ha. exact (delay_saturated Γ a HΓ Ha).
  - intros f Φ Γ e γ e' _ IH HΓ He.
    apply cast_expr_keeps_saturation. exact (IH HΓ He).
  - intros f Φ Γ Γ' x eb ea eb' _ IH HΓ He.
    destruct He as [[HΓ' Hb] Ha].
    apply IH; [apply extend_saturated; assumption | exact (exact_at_least eb 0 Hb)].
  - intros f Φ Γ ef ea ef' er Hc _ IHf _ IHapp HΓ He.
    destruct He as [Hf Ha].
    assert (Hf0 : spine_ok AtLeast 0 ef).
    { apply (spine_ok_any_count ef AtLeast 1 0); [| exact Hf].
      inversion Hc; subst; try reflexivity; assumption. }
    apply IHapp; [exact HΓ |]. split; [| exact Ha].
    apply (at_least_more ef' 0 1); [lia |]. apply exact_at_least. exact (IHf HΓ Hf0).
  - intros f Φ Γ b HΓ He. exact He.
  - intros f Φ Γ ef ea p args args' Hu Hl HF HΓ He.
    destruct (unspool_spine_ok _ [] _ _ AtLeast He (Forall_nil _) Hu) as [_ Hargs].
    apply reduce_prim_keeps_saturation.
    + rewrite <- (Forall2_length HF). exact Hl.
    + clear -HF Hargs HΓ.
      induction HF as [| a a' l l' [_ Ha] _ IH]; constructor; inversion Hargs; subst.
      * apply Ha; [exact HΓ | apply exact_at_least; assumption].
      * apply IH; assumption.
  - intros f Φ Γ x e HΓ He. exact (conj HΓ He).
  - intros f Φ Γ ef γ ea γ_a γ_r er _ _ IH HΓ He.
    destruct He as [Hf Ha]. apply IH; [exact HΓ |].
    split; [apply (at_least_more ef 0 1); [lia | exact Hf] | exact Ha].
  - intros f Φ Γ e1 e2 ec et ef args er Hu _ IH HΓ He.
    destruct (unspool_spine_ok _ [] _ _ AtLeast He (Forall_nil _) Hu) as [[Hc [Ht Hf]] Hargs].
    apply IH; [exact HΓ |].
    refine (conj Hc (conj _ _)); apply fold_left_spine_ok; try rewrite Nat.add_0_r; assumption.
  - intros f Φ Γ b ea HΓ He. exact (proj1 He).
  - intros f Φ Γ es alts es' er _ IHs _ IHf HΓ He.
    apply alts_ok_forall in He. destruct He as [Hs Halts].
    exact (IHf HΓ (merge_saturated Γ es' (IHs HΓ Hs)) Halts).
  - intros f Φ Γ ec et ef ec' et' ef' pc_c _ IHc _ _ IHt _ IHf HΓ He.
    destruct He as [Hc [Ht Hf]].
    exact (conj (IHc HΓ Hc) (conj (IHt HΓ Ht) (IHf HΓ Hf))).
  - intros. exact I.
  - intros. exact I.
  - intros. exact I.
  - intros f Φ Γ Γ' e e' _ IH HΓ He.
    destruct He as [HΓ' Hb]. exact (IH HΓ' (exact_at_least e 0 Hb)).
  - intros. exact I.
  - intros f Φ Γ ec et ef alts et' ef' pc_c _ _ IHt _ IHf HΓ He Halts.
    destruct He as [Hc [Ht Hf]].
    exact (conj Hc (conj (IHt HΓ Ht Halts) (IHf HΓ Hf Halts))).
  - intros. exact I.
  - intros f Φ Γ e d ea xs ep alts er Hd Hfind _ IH HΓ He Halts.
    apply IH.
    + apply extend_multi_saturated;
        [exact HΓ | exact HΓ | exact (decompose_con_app_saturated _ _ _ He Hd)].
    + exact (exact_at_least ep 0 (find_alt_saturated _ _ _ _ Halts Hfind)).
  - intros f Φ Γ b alts HΓ He _. exact He.
  - intros. exact I.
Qed.

Theorem eval_preserves_saturation : forall f Φ Γ e v,
  saturated_env Γ -> saturated e -> eval f Φ Γ e v -> saturated v.
Proof.
  intros f Φ Γ e v HΓ He Hev.
  exact (eval_saturates_at_least f Φ Γ e v Hev HΓ (exact_at_least e 0 He)).
Qed.

Theorem fold_alts_preserves_saturation : forall f Φ Γ e alts v,
  saturated_env Γ -> saturated e -> Forall saturated_alt alts ->
  fold_alts f Φ Γ e alts v -> saturated v.
Proof.
  intros f Φ Γ e alts v HΓ He Halts Hfold.
  induction Hfold as [f Φ Γ ec et ef alts et' ef' pc_c _ _ IHt _ IHf
                     | | f Φ Γ e d ea xs ep alts er Hd Hfind Hev | f Φ Γ b alts | ].
  - destruct He as [Hc [Ht Hf]].
    exact (conj Hc (conj (IHt HΓ Ht Halts) (IHf HΓ Hf Halts))).
  - exact I.
  - refine (eval_preserves_saturation _ _ _ _ _ _ (find_alt_saturated _ _ _ _ Halts Hfind) Hev).
    apply extend_multi_saturated; [exact HΓ | exact HΓ |].
    exact (decompose_con_app_saturated _ _ _ He Hd).
  - exact He.
  - exact I.
Qed.

Theorem saturated_prim_app_meets_arity : forall ef ea p args,
  saturated (EApp ef ea) -> unspool_app (EApp ef ea) [] = (EPrimOp p, args) ->
  length args = primop_arity p.
Proof. intros ef ea p args. apply saturated_prim_spine. Qed.

Theorem evaluated_prim_app_not_partial : forall ef ea p args,
  spine_ok AtLeast 0 (EApp ef ea) -> unspool_app (EApp ef ea) [] = (EPrimOp p, args) ->
  ~ length args < primop_arity p.
Proof.
  intros ef ea p args He Hu Hlt.
  pose proof (at_least_prim_spine _ p args He Hu) as Hge. lia.
Qed.

End Saturation.

Section ModelSaturation.

Lemma model_graft_arg_saturated : forall a f n,
  spine_ok Exactly (S n) f -> saturated a -> spine_ok Exactly n (graft_arg f a).
Proof.
  induction a; intros f n Hf Ha; try exact (conj Hf Ha).
  destruct Ha as [Hc [Ht He]].
  exact (conj Hc (conj (IHa2 f n Hf Ht) (IHa3 f n Hf He))).
Qed.

Lemma model_graft_saturated : forall f a n,
  spine_ok Exactly (S n) f -> saturated a -> spine_ok Exactly n (graft f a).
Proof.
  induction f; intros a n Hf Ha; try (apply model_graft_arg_saturated; assumption).
  destruct Hf as [Hc [Ht He]].
  exact (conj Hc (conj (IHf2 a n Ht Ha) (IHf3 a n He Ha))).
Qed.

Lemma model_lift_branches_saturated : forall e n,
  spine_ok Exactly n e -> spine_ok Exactly n (lift_branches e).
Proof.
  induction e; intros n He; try exact He.
  - destruct He as [Hf Ha]. apply model_graft_saturated; [apply IHe1 | apply IHe2]; assumption.
  - destruct He as [Hc [Ht Hf]]. exact (conj Hc (conj (IHe2 n Ht) (IHe3 n Hf))).
Qed.

Lemma model_fold_leaves_saturated : forall e n,
  spine_ok Exactly n e -> spine_ok Exactly n (fold_leaves e).
Proof.
  induction e; intros n He; simpl; unfold fold_leaf;
    try (destruct (smt_ground _)); try exact I; try exact He.
  destruct He as [Hc [Ht Hf]]. exact (conj Hc (conj (IHe2 n Ht) (IHe3 n Hf))).
Qed.

Lemma model_reduce_unbranched_saturated : forall p args,
  Forall saturated args -> saturated (reduce_unbranched p args).
Proof.
  intros p args Hargs. unfold reduce_unbranched.
  destruct (Nat.eqb (length args) (model_arity p)) eqn:Hlen; [| exact I].
  apply Nat.eqb_eq in Hlen.
  apply model_fold_leaves_saturated, model_lift_branches_saturated.
  apply fold_left_spine_ok; [| exact Hargs].
  rewrite Nat.add_0_r. simpl. unfold arity_met. exact (eq_sym Hlen).
Qed.

Lemma model_split_arg_saturated : forall k a,
  (forall a', saturated a' -> saturated (k a')) -> saturated a -> saturated (split_arg k a).
Proof.
  intros k a Hk. induction a; intros Ha; try exact (Hk _ Ha).
  destruct Ha as [Hc [Ht Hf]]. exact (conj Hc (conj (IHa2 Ht) (IHa3 Hf))).
Qed.

Lemma model_split_args_saturated : forall args k,
  (forall args', Forall saturated args' -> saturated (k args')) ->
  Forall saturated args -> saturated (split_args k args).
Proof.
  induction args as [| a rest IH]; intros k Hk Hargs; simpl; [apply Hk; constructor |].
  inversion Hargs as [| a0 rest0 Ha Hrest]; subst.
  apply model_split_arg_saturated; [| exact Ha].
  intros a' Ha'. apply IH; [| exact Hrest].
  intros rest' Hrest'. apply Hk. constructor; assumption.
Qed.

#[export] Instance model_reduce_prim_keeps_saturation : ReducePrimKeepsSaturation.
Proof.
  intros p args _ Hargs.
  change (saturated (model_reduce_prim p args)). unfold model_reduce_prim.
  apply model_split_args_saturated; [| exact Hargs].
  apply model_reduce_unbranched_saturated.
Qed.

#[export] Instance model_cast_expr_keeps_saturation : CastExprKeepsSaturation.
Proof. intros e γ He. exact He. Qed.

End ModelSaturation.
