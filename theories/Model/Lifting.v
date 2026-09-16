From SymCoreTheory Require Export Model.Reducer.
From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat Lia.
Import ListNotations.

(** ========================================================================= *)
(** Lifting branches out of an application                                    *)
(** ========================================================================= *)

Fixpoint flat (e : expr) : bool :=
  match e with
  | EIf _ _ _ => false
  | EApp f a => flat f && flat a
  | _ => true
  end.

Lemma flat_not_if : forall e, flat e = true -> is_if e = false.
Proof. intros e H. destruct e; simpl in *; congruence. Qed.

Lemma graft_arg_not_if : forall f a, is_if a = false -> graft_arg f a = EApp f a.
Proof. intros f a H. destruct a; simpl in *; congruence. Qed.

Lemma graft_not_if : forall f a,
  is_if f = false -> is_if a = false -> graft f a = EApp f a.
Proof.
  intros f a Hf Ha. destruct f; simpl in Hf; try discriminate; simpl;
    apply graft_arg_not_if; exact Ha.
Qed.

Lemma lift_flat : forall e, flat e = true -> lift_branches e = e.
Proof.
  induction e; intros H; simpl in *; try reflexivity; try discriminate.
  apply andb_prop in H as [H1 H2].
  rewrite (IHe1 H1), (IHe2 H2). apply graft_not_if; apply flat_not_if; assumption.
Qed.

Lemma solvable_flat : forall Γ e, Solvable Γ e -> flat e = true.
Proof.
  intros Γ e H. induction H; simpl; try reflexivity.
  rewrite IHSolvable1, IHSolvable2. reflexivity.
Qed.

Lemma concore_flat : forall e, concore_expr e -> flat e = true.
Proof.
  induction e; intros H; simpl; try reflexivity.
  - inversion H; subst. rewrite IHe1, IHe2 by assumption. reflexivity.
  - exfalso. exact (not_concore_if _ _ _ H).
Qed.

Lemma denotes_flat : forall S e pc, denotes S e pc -> flat e = true.
Proof. intros S e pc H. exact (solvable_flat · e (denotes_solvable S e pc H)). Qed.

Lemma contains_flat_instance : forall σ S e X, contains σ S e X -> flat X = true.
Proof.
  intros σ S e X H. induction H; simpl; try reflexivity; try assumption.
  rewrite IHcontains1, IHcontains2. reflexivity.
Qed.

Inductive picks (σ : valuation) (S : symvars) : expr -> expr -> Prop :=
  | picks_leaf : forall e, is_if e = false -> picks σ S e e
  | picks_then : forall c t f L,
      models_cond σ S c -> picks σ S t L -> picks σ S (EIf c t f) L
  | picks_else : forall c t f L,
      models_not_cond σ S c -> picks σ S f L -> picks σ S (EIf c t f) L.

Inductive leaves (P : expr -> Prop) : expr -> Prop :=
  | leaves_leaf : forall e, is_if e = false -> P e -> leaves P e
  | leaves_if : forall c t f, leaves P t -> leaves P f -> leaves P (EIf c t f).

Lemma picks_leaves : forall σ S (P : expr -> Prop) T L,
  picks σ S T L -> leaves P T -> P L.
Proof.
  intros σ S P T L H. induction H; intros HT; inversion HT; subst; simpl in *;
    try discriminate; auto.
Qed.

Lemma leaves_mono : forall (P Q : expr -> Prop) T,
  (forall e, P e -> Q e) -> leaves P T -> leaves Q T.
Proof.
  intros P Q T HPQ H. induction H; [apply leaves_leaf; auto | apply leaves_if; auto].
Qed.

Definition app_of (P Q : expr -> Prop) (e : expr) : Prop :=
  exists f a, e = EApp f a /\ P f /\ Q a.

Lemma leaves_graft_arg : forall (P Q : expr -> Prop) f A,
  is_if f = false -> P f -> leaves Q A -> leaves (app_of P Q) (graft_arg f A).
Proof.
  intros P Q f A Hf Pf H. induction H.
  - rewrite graft_arg_not_if by assumption.
    apply leaves_leaf; [reflexivity | exists f, e; auto].
  - simpl. apply leaves_if; assumption.
Qed.

Lemma leaves_graft : forall (P Q : expr -> Prop) F A,
  leaves P F -> leaves Q A -> leaves (app_of P Q) (graft F A).
Proof.
  intros P Q F A HF HA. induction HF.
  - destruct e; simpl in H; try discriminate; simpl;
      apply leaves_graft_arg; try reflexivity; assumption.
  - simpl. apply leaves_if; assumption.
Qed.

Lemma leaves_lift_any : forall e, leaves (fun _ => True) (lift_branches e).
Proof.
  induction e; simpl; try (apply leaves_leaf; [reflexivity | exact I]).
  - apply (leaves_mono (app_of (fun _ => True) (fun _ => True))); [intros; exact I |].
    apply leaves_graft; assumption.
  - apply leaves_if; assumption.
Qed.

Definition spine_of (p : model_primop) (n : nat) (e : expr) : Prop :=
  exists L, e = op_spine p L /\ length L = n.

Lemma op_spine_snoc : forall p args a,
  op_spine p (args ++ a :: nil) = EApp (op_spine p args) a.
Proof. intros p args a. unfold op_spine. rewrite fold_left_app. reflexivity. Qed.

Lemma op_spine_unspool : forall p L, unspool_app (op_spine p L) nil = (EPrimOp p, L).
Proof. intros p L. unfold op_spine. rewrite unspool_fold_left_app, app_nil_r. reflexivity. Qed.

Lemma op_spine_not_if : forall p L, is_if (op_spine p L) = false.
Proof.
  intros p L. induction L as [| a L IH] using rev_ind; [reflexivity |].
  rewrite op_spine_snoc. reflexivity.
Qed.

Lemma leaves_lift_spine : forall p args,
  leaves (spine_of p (length args)) (lift_branches (op_spine p args)).
Proof.
  intros p args. induction args as [| a args IH] using rev_ind.
  - apply leaves_leaf; [reflexivity | exists nil; split; reflexivity].
  - rewrite op_spine_snoc. cbn [lift_branches].
    apply (leaves_mono (app_of (spine_of p (length args)) (fun _ => True))).
    + intros e [f [b [He [[L [Hf HL]] _]]]]. exists (L ++ b :: nil)%list.
      subst. rewrite op_spine_snoc, !length_app, HL. split; reflexivity.
    + apply leaves_graft; [exact IH | apply leaves_lift_any].
Qed.

Lemma fold_leaves_not_if : forall e, is_if e = false -> fold_leaves e = fold_leaf e.
Proof. intros e H. destruct e; simpl in *; congruence. Qed.

Lemma fold_leaf_not_if : forall e, is_if e = false -> is_if (fold_leaf e) = false.
Proof. intros e H. unfold fold_leaf. destruct (smt_ground e); [reflexivity | exact H]. Qed.

Lemma op_spine_flat : forall p args,
  Forall (fun a => flat a = true) args -> flat (op_spine p args) = true.
Proof.
  intros p args H. unfold op_spine.
  assert (Hh : flat (EPrimOp p) = true) by reflexivity.
  revert Hh. generalize (EPrimOp p). induction H as [| a args Ha Hargs IH]; intros h Hh.
  - exact Hh.
  - simpl. apply IH. simpl. rewrite Hh, Ha. reflexivity.
Qed.

(** ========================================================================= *)
(** The value of a closed term does not depend on the model                   *)
(** ========================================================================= *)

Lemma ground_pc_value : forall e pc σ1 σ2,
  smt_ground e = true -> expr_to_pc · e = Some pc ->
  pc_value σ1 pc = pc_value σ2 pc
  /\ (forall q qs, pc = PCPrim q qs -> map (pc_value σ1) qs = map (pc_value σ2) qs).
Proof.
  induction e; intros pc σ1 σ2 Hg Hpc; simpl in Hg; try discriminate.
  - simpl in Hpc. injection Hpc as <-.
    split; [reflexivity | intros q qs Heq; discriminate Heq].
  - simpl in Hpc. injection Hpc as <-.
    split; [reflexivity | intros q qs Heq; injection Heq as <- <-; reflexivity].
  - apply andb_prop in Hg as [Hg12 Hga]. apply andb_prop in Hg12 as [Hop Hgf].
    simpl in Hpc. destruct (expr_to_pc · e1) as [pf |] eqn:E1; [| discriminate].
    destruct pf as [v | l | q qs];
      try (destruct (expr_to_pc · e2); simpl in Hpc; discriminate).
    destruct (expr_to_pc · e2) as [pa |] eqn:E2; [| discriminate].
    injection Hpc as <-.
    destruct (IHe1 _ σ1 σ2 Hgf eq_refl) as [_ Hmap].
    destruct (IHe2 _ σ1 σ2 Hga eq_refl) as [Hva _].
    specialize (Hmap q qs eq_refl).
    assert (Hl : map (pc_value σ1) (qs ++ pa :: nil) = map (pc_value σ2) (qs ++ pa :: nil)).
    { rewrite !map_app, Hmap. cbn [map]. rewrite Hva. reflexivity. }
    split.
    + change (prim_value q (map (pc_value σ1) (qs ++ pa :: nil))
              = prim_value q (map (pc_value σ2) (qs ++ pa :: nil))).
      rewrite Hl. reflexivity.
    + intros q' qs' Heq. injection Heq as <- <-. exact Hl.
Qed.

Lemma closed_value_of : forall e pc,
  expr_to_pc · e = Some pc -> closed_value e = pc_value closed_model pc.
Proof. intros e pc H. unfold closed_value. rewrite H. reflexivity. Qed.

Lemma ground_instance_denotes : forall σ S L X,
  contains σ S L X -> flat L = true -> smt_ground X = true ->
  exists pcL pcX,
    denotes S L pcL /\ expr_to_pc · X = Some pcX /\
    pc_value σ pcL = pc_value closed_model pcX /\
    (is_op_app X = true ->
       exists q qsL qsX, pcL = PCPrim q qsL /\ pcX = PCPrim q qsX /\
         map (pc_value σ) qsL = map (pc_value closed_model) qsX).
Proof.
  intros σ S L X H. induction H; intros HfL HgX; simpl in HfL, HgX; try discriminate.
  - exists (PCVar x), (PCLit (σ x)).
    split; [intros Γ Hfree; simpl; rewrite (Hfree x H); reflexivity |].
    split; [reflexivity | split; [reflexivity | intros Hop; discriminate Hop]].
  - exists (PCLit l), (PCLit l).
    split; [intros Γ _; reflexivity |].
    split; [reflexivity | split; [reflexivity | intros Hop; discriminate Hop]].
  - exists (PCPrim p nil), (PCPrim p nil).
    split; [intros Γ _; reflexivity |].
    split; [reflexivity | split; [reflexivity |]].
    intros _. exists p, nil, nil. repeat split.
  - apply andb_prop in HgX as [HgX12 HgXa]. apply andb_prop in HgX12 as [HopX HgXf].
    apply andb_prop in HfL as [HfLf HfLa].
    destruct (IHcontains1 HfLf HgXf) as [pf [pfX [Hdf [Hef [_ Hopf]]]]].
    destruct (IHcontains2 HfLa HgXa) as [pa [paX [Hda [Hea [Hva _]]]]].
    destruct (Hopf HopX) as [q [qs [qsX [-> [-> Hmap]]]]].
    assert (Hl : map (pc_value σ) (qs ++ pa :: nil)
                 = map (pc_value closed_model) (qsX ++ paX :: nil)).
    { rewrite !map_app, Hmap. cbn [map]. rewrite Hva. reflexivity. }
    exists (PCPrim q (qs ++ pa :: nil)), (PCPrim q (qsX ++ paX :: nil)).
    split; [| split; [| split]].
    + intros Γ Hfree. simpl. rewrite (Hdf Γ Hfree), (Hda Γ Hfree). reflexivity.
    + simpl. rewrite Hef, Hea. reflexivity.
    + change (prim_value q (map (pc_value σ) (qs ++ pa :: nil))
              = prim_value q (map (pc_value closed_model) (qsX ++ paX :: nil))).
      rewrite Hl. reflexivity.
    + intros _. exists q, (qs ++ pa :: nil), (qsX ++ paX :: nil).
      split; [reflexivity | split; [reflexivity | exact Hl]].
  - exfalso. destruct ec; discriminate.
  - destruct H2 as [pc [Hd Hv]].
    exists pc, (PCLit l).
    split; [exact Hd | split; [reflexivity | split; [exact Hv | intros Hop; discriminate Hop]]].
Qed.

Lemma op_spine_denotes : forall S args pcs,
  Forall2 (denotes S) args pcs ->
  forall h q acc, denotes S h (PCPrim q acc) ->
  denotes S (fold_left EApp args h) (PCPrim q (acc ++ pcs)).
Proof.
  intros S args pcs H. induction H as [| a pa args pcs Ha Hargs IH]; intros h q acc Hh.
  - rewrite app_nil_r. exact Hh.
  - simpl. replace (acc ++ pa :: pcs) with ((acc ++ pa :: nil) ++ pcs)
      by (rewrite <- app_assoc; reflexivity).
    apply IH. intros Γ Hfree. simpl. rewrite (Hh Γ Hfree), (Ha Γ Hfree). reflexivity.
Qed.

