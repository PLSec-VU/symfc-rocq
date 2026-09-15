From SymCoreTheory Require Import SymCore ConCore.
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

End Saturation.
