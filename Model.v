(**
  Model.v - One intended model of every parameter and law of SymCore.v and
  ConCore.v.

  Literals are the Booleans. The primitive operations are conjunction,
  negation and if-then-else, read the way the Booleans read them. The reducer
  folds an application whose arguments are closed, and leaves any other
  application as a residual term. A branch inside an argument is lifted out
  of the application first, so the reducer answers a branch of folded terms.
*)

From SymCoreTheory Require Import SymCore ConCore BranchLaws.
From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat Lia.
Import ListNotations.

(** ========================================================================= *)
(** 1. Sorts                                                                   *)
(** ========================================================================= *)

Inductive model_primop : Set := PAnd | PNot | PIte.

Definition model_primop_eq_dec : forall p q : model_primop, {p = q} + {p <> q}.
Proof. decide equality. Defined.

Definition model_tycon_eq_dec : forall t1 t2 : unit, {t1 = t2} + {t1 <> t2}.
Proof. decide equality. Defined.

Definition model_arity (p : model_primop) : nat :=
  match p with PAnd => 2 | PNot => 1 | PIte => 3 end.

Definition model_prim_value (p : model_primop) (ls : list bool) : bool :=
  match p, ls with
  | PAnd, a :: b :: nil => a && b
  | PNot, a :: nil => negb a
  | PIte, c :: a :: b :: nil => if c then a else b
  | _, _ => false
  end.

#[export] Instance model_sorts : SymCoreSorts :=
  Build_SymCoreSorts
    bool model_primop PAnd PNot PIte model_arity eq_refl
    bool_dec model_primop_eq_dec unit model_tycon_eq_dec
    model_prim_value true.

Lemma model_prim_value_wrong_arity : forall p ls,
  length ls <> model_arity p -> model_prim_value p ls = false.
Proof.
  intros p ls H.
  destruct p; destruct ls as [| a [| b [| c [| d ls]]]]; simpl in *; congruence.
Qed.

(** ========================================================================= *)
(** 2. The reducer                                                             *)
(** ========================================================================= *)

Definition closed_model : valuation := fun _ => false.

Definition closed_value (e : expr) : bool :=
  match expr_to_pc · e with
  | Some pc => pc_value closed_model pc
  | None => false
  end.

Fixpoint graft_arg (f a : expr) : expr :=
  match a with
  | EIf c t e => EIf c (graft_arg f t) (graft_arg f e)
  | _ => EApp f a
  end.

Fixpoint graft (f a : expr) : expr :=
  match f with
  | EIf c t e => EIf c (graft t a) (graft e a)
  | _ => graft_arg f a
  end.

Fixpoint lift_branches (e : expr) : expr :=
  match e with
  | EIf c t f => EIf c (lift_branches t) (lift_branches f)
  | EApp f a => graft (lift_branches f) (lift_branches a)
  | _ => e
  end.

Definition fold_leaf (e : expr) : expr :=
  if smt_ground e then ELit (closed_value e) else e.

Fixpoint fold_leaves (e : expr) : expr :=
  match e with
  | EIf c t f => EIf c (fold_leaves t) (fold_leaves f)
  | _ => fold_leaf e
  end.

Definition op_spine (p : model_primop) (args : list expr) : expr :=
  fold_left EApp args (EPrimOp p).

Definition reduce_unbranched (p : model_primop) (args : list expr) : expr :=
  if Nat.eqb (length args) (model_arity p)
  then fold_leaves (lift_branches (op_spine p args))
  else ELit false.

Fixpoint split_arg (k : expr -> expr) (a : expr) : expr :=
  match a with
  | EIf c t f => EIf c (split_arg k t) (split_arg k f)
  | _ => k a
  end.

Fixpoint split_args (k : list expr -> expr) (args : list expr) : expr :=
  match args with
  | nil => k nil
  | a :: rest => split_arg (fun a' => split_args (fun rest' => k (a' :: rest')) rest) a
  end.

Definition model_reduce_prim (p : model_primop) (args : list expr) : expr :=
  split_args (reduce_unbranched p) args.

Definition model_sat (Φ : path_condition) : bool := true.
Definition erase_cast (e : expr) (γ : coercion) : expr := e.
Definition keep_coercion (Γ : environment) (γ : coercion) : coercion := γ.
Definition keep_type (Γ : environment) (τ : type_fc) : type_fc := τ.

#[export] Instance model_solver : SymCoreSolver :=
  Build_SymCoreSolver
    model_sat (PCLit true) eq_refl model_reduce_prim
    erase_cast keep_coercion keep_type.

Lemma model_reduce_prim_folds :
  reduce_prim op_and (ELit true :: ELit false :: nil) = ELit false.
Proof. reflexivity. Qed.

Lemma model_reduce_prim_leaves_residual :
  reduce_prim op_and (EVar "x"%string :: ELit true :: nil)
  = EApp (EApp (EPrimOp PAnd) (EVar "x"%string)) (ELit true).
Proof. reflexivity. Qed.

(** ========================================================================= *)
(** 3. The laws that need no reasoning about the reducer                       *)
(** ========================================================================= *)

#[export] Instance model_cast_expr_concore : CastExprConcore.
Proof. intros e γ H. exact H. Qed.

#[export] Instance model_cast_expr_contains : CastExprContains.
Proof. intros σ S es ec γ H. exact H. Qed.

#[export] Instance model_subst_coerc_contains_env : SubstCoercContainsEnv.
Proof. intros σ S Γs Γc γ _. apply Cont_Coercion. Qed.

#[export] Instance model_subst_type_contains_env : SubstTypeContainsEnv.
Proof. intros σ S Γs Γc τ _. apply Cont_Type. Qed.

#[export] Instance model_models_sat : ModelsSat.
Proof. intros σ Φ _. reflexivity. Qed.

#[export] Instance model_prim_value_and : PrimValueAnd.
Proof. intros l1 l2. apply andb_true_iff. Qed.

(** ========================================================================= *)
(** 4. Lifting branches out of an application                                  *)
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

Lemma picks_contains : forall σ S T L Y,
  picks σ S T L -> contains σ S L Y -> contains σ S T Y.
Proof.
  intros σ S T L Y H. induction H; intros Hc;
    [exact Hc | apply Cont_If_True | apply Cont_If_False]; auto.
Qed.

Lemma picks_graft_arg : forall σ S L1 T2 L2,
  is_if L1 = false -> picks σ S T2 L2 -> picks σ S (graft_arg L1 T2) (EApp L1 L2).
Proof.
  intros σ S L1 T2 L2 H1 H. induction H.
  - rewrite graft_arg_not_if by assumption. apply picks_leaf. reflexivity.
  - simpl. apply picks_then; assumption.
  - simpl. apply picks_else; assumption.
Qed.

Lemma picks_graft : forall σ S T1 L1 T2 L2,
  picks σ S T1 L1 -> picks σ S T2 L2 -> picks σ S (graft T1 T2) (EApp L1 L2).
Proof.
  intros σ S T1 L1 T2 L2 H1 H2. induction H1.
  - destruct e; simpl in H; try discriminate; simpl;
      apply picks_graft_arg; try reflexivity; exact H2.
  - simpl. apply picks_then; assumption.
  - simpl. apply picks_else; assumption.
Qed.

Lemma lift_picks : forall σ S e X,
  contains σ S e X ->
  exists L, picks σ S (lift_branches e) L /\ contains σ S L X /\ flat L = true.
Proof.
  intros σ S e X H. induction H;
    try (eexists; split; [apply picks_leaf; reflexivity
                         | split; [simpl; solve [econstructor; eassumption] | reflexivity]]).
  - destruct IHcontains1 as [L1 [P1 [C1 F1]]].
    destruct IHcontains2 as [L2 [P2 [C2 F2]]].
    exists (EApp L1 L2). split; [simpl; apply picks_graft; assumption |].
    split; [apply Cont_App; assumption | simpl; rewrite F1, F2; reflexivity].
  - destruct IHcontains as [L [P [C F]]].
    exists L. split; [simpl; apply picks_then; assumption | split; assumption].
  - destruct IHcontains as [L [P [C F]]].
    exists L. split; [simpl; apply picks_else; assumption | split; assumption].
  - assert (Hflat : flat es = true)
      by (destruct H2 as [pc [Hd _]]; exact (denotes_flat S es pc Hd)).
    exists es. rewrite (lift_flat es Hflat).
    split; [apply picks_leaf; apply flat_not_if; exact Hflat |].
    split; [eapply Cont_Denote; eassumption | exact Hflat].
Qed.

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

Lemma picks_fold_leaves : forall σ S T L,
  picks σ S T L -> picks σ S (fold_leaves T) (fold_leaf L).
Proof.
  intros σ S T L H. induction H.
  - rewrite fold_leaves_not_if by assumption.
    apply picks_leaf. apply fold_leaf_not_if. assumption.
  - simpl. apply picks_then; assumption.
  - simpl. apply picks_else; assumption.
Qed.

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
(** 5. The value of a closed term does not depend on the model                *)
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

(** ========================================================================= *)
(** 6. The laws about the reducer                                              *)
(** ========================================================================= *)

Lemma leaf_contains : forall σ S p L X,
  spine_of p (model_arity p) L ->
  contains σ S L X -> flat L = true ->
  contains σ S (fold_leaf L) (fold_leaf X).
Proof.
  intros σ S p L X [L' [-> HL']] Hc HfL.
  unfold fold_leaf.
  destruct (smt_ground X) eqn:HgX; destruct (smt_ground (op_spine p L')) eqn:HgL.
  - rewrite (closed_smt_term_is_rigid σ S _ _ HgL Hc). apply Cont_Lit.
  - destruct (ground_instance_denotes σ S _ _ Hc HfL HgX) as [pcL [pcX [HdL [HeX [Hv _]]]]].
    apply (Cont_Denote σ S (op_spine p L') p L').
    + apply op_spine_unspool.
    + exact HL'.
    + exact HgL.
    + exists pcL. split; [exact HdL |]. rewrite (closed_value_of X pcX HeX). exact Hv.
  - pose proof (closed_smt_term_is_rigid σ S _ _ HgL Hc) as E.
    rewrite E in HgL. congruence.
  - exact Hc.
Qed.

Lemma unbranched_contains : forall σ S p args_s args_c,
  Forall2 (contains σ S) args_s args_c ->
  contains σ S (reduce_unbranched p args_s) (reduce_unbranched p args_c).
Proof.
  intros σ S p args_s args_c HF.
  unfold reduce_unbranched. rewrite <- (Forall2_length HF).
  destruct (Nat.eqb (length args_s) (model_arity p)) eqn:Hlen; [| apply Cont_Lit].
  apply Nat.eqb_eq in Hlen.
  assert (Hc : contains σ S (op_spine p args_s) (op_spine p args_c))
    by (apply contains_fold_left_app; [exact HF | apply Cont_PrimOp]).
  rewrite (lift_flat _ (contains_flat_instance σ S _ _ Hc)),
          (fold_leaves_not_if _ (op_spine_not_if p args_c)).
  destruct (lift_picks σ S _ _ Hc) as [L [Hp [HcL HfL]]].
  apply (picks_contains σ S _ (fold_leaf L)); [apply picks_fold_leaves; exact Hp |].
  apply (leaf_contains σ S p L); [| exact HcL | exact HfL].
  rewrite <- Hlen. exact (picks_leaves σ S _ _ _ Hp (leaves_lift_spine p args_s)).
Qed.

Lemma denote_args : forall σ S args ls,
  Forall2 (denote σ S) args ls ->
  exists pcs, Forall2 (denotes S) args pcs /\ map (pc_value σ) pcs = ls.
Proof.
  intros σ S args ls H.
  induction H as [| a l args ls [pc [Hd Hv]] _ [pcs [Hds Hvs]]].
  - exists nil. split; [constructor | reflexivity].
  - exists (pc :: pcs). split; [constructor; assumption |].
    cbn [map]. rewrite Hv, Hvs. reflexivity.
Qed.

Lemma denotes_all_flat : forall S args pcs,
  Forall2 (denotes S) args pcs -> Forall (fun a => flat a = true) args.
Proof.
  intros S args pcs H. induction H; constructor; [eapply denotes_flat; eassumption | assumption].
Qed.

Lemma unbranched_denote : forall σ S (p : primop) args ls,
  Forall2 (denote σ S) args ls ->
  denote σ S (reduce_unbranched p args) (prim_value p ls).
Proof.
  intros σ S p args ls HF.
  unfold reduce_unbranched.
  destruct (denote_args σ S args ls HF) as [pcs [Hds Hvs]].
  destruct (Nat.eqb (length args) (model_arity p)) eqn:Hlen.
  - rewrite (lift_flat _ (op_spine_flat p args (denotes_all_flat S args pcs Hds))),
            (fold_leaves_not_if _ (op_spine_not_if p args)).
    assert (Hd : denotes S (op_spine p args) (PCPrim p pcs))
      by (apply (op_spine_denotes S args pcs Hds (EPrimOp p) p nil); intros Γ _; reflexivity).
    assert (Hv : pc_value σ (PCPrim p pcs) = prim_value p ls)
      by (change (prim_value p (map (pc_value σ) pcs) = prim_value p ls); rewrite Hvs; reflexivity).
    unfold fold_leaf. destruct (smt_ground (op_spine p args)) eqn:Hg.
    + pose proof (Hd · (sym_free_env_empty S)) as He.
      rewrite (closed_value_of _ _ He).
      destruct (ground_pc_value _ _ closed_model σ Hg He) as [Hcl _].
      rewrite Hcl, Hv. apply denote_lit.
    + exists (PCPrim p pcs). split; [exact Hd | exact Hv].
  - apply Nat.eqb_neq in Hlen.
    change (prim_value p ls) with (model_prim_value p ls).
    rewrite model_prim_value_wrong_arity; [apply denote_lit |].
    rewrite <- Hvs, length_map, <- (Forall2_length Hds). exact Hlen.
Qed.

Lemma fold_leaves_ground : forall T,
  smt_ground (fold_leaves T) = true -> exists l, fold_leaves T = ELit l.
Proof.
  intros T H. destruct (is_if T) eqn:Hif.
  - destruct T; simpl in Hif, H; discriminate.
  - rewrite (fold_leaves_not_if T Hif) in *. unfold fold_leaf in *.
    destruct (smt_ground T) eqn:Hg; [eexists; reflexivity | congruence].
Qed.

Lemma unbranched_ground_value : forall p args,
  smt_ground (reduce_unbranched p args) = true ->
  exists l, reduce_unbranched p args = ELit l.
Proof.
  intros p args H.
  unfold reduce_unbranched in *.
  destruct (Nat.eqb (length args) (model_arity p));
    [apply fold_leaves_ground; exact H | eexists; reflexivity].
Qed.

Lemma unbranched_saturated : forall p args p0 args0,
  unspool_app (reduce_unbranched p args) nil = (EPrimOp p0, args0) ->
  length args0 = model_arity p0.
Proof.
  intros p args p0 args0 H.
  unfold reduce_unbranched in H.
  destruct (Nat.eqb (length args) (model_arity p)) eqn:Hlen; [| discriminate H].
  apply Nat.eqb_eq in Hlen.
  revert H. generalize (leaves_lift_spine p args).
  generalize (lift_branches (op_spine p args)). intros T Hl.
  destruct Hl as [e Hif [L [-> HL]] | c t f _ _]; intros H.
  - rewrite (fold_leaves_not_if _ Hif) in H. unfold fold_leaf in H.
    destruct (smt_ground (op_spine p L)); [simpl in H; discriminate H |].
    rewrite op_spine_unspool in H. injection H as <- <-. rewrite HL. exact Hlen.
  - simpl in H. discriminate H.
Qed.

Lemma solvable_op_spine : forall Γ args h,
  Solvable Γ h -> is_op_app h = true -> Forall (Solvable Γ) args ->
  Solvable Γ (fold_left EApp args h).
Proof.
  intros Γ args h Hh Hop HF. revert h Hh Hop.
  induction HF as [| a args Ha Hargs IH]; intros h Hh Hop; [exact Hh |].
  simpl. apply IH; [apply Solvable_AppPrim; [exact Hop | exact Hh | exact Ha] | exact Hop].
Qed.

Lemma unbranched_solvable : forall Γ p args,
  Forall (Solvable Γ) args -> Solvable Γ (reduce_unbranched p args).
Proof.
  intros Γ p args HF. unfold reduce_unbranched.
  destruct (Nat.eqb (length args) (model_arity p)); [| apply Solvable_Lit].
  assert (Hs : Solvable Γ (op_spine p args))
    by (apply solvable_op_spine; [apply Solvable_PrimOp | reflexivity | exact HF]).
  rewrite (lift_flat _ (solvable_flat Γ _ Hs)), (fold_leaves_not_if _ (op_spine_not_if p args)).
  unfold fold_leaf. destruct (smt_ground (op_spine p args)); [apply Solvable_Lit | exact Hs].
Qed.

Lemma unbranched_concore : forall p args,
  Forall concore_expr args -> concore_expr (reduce_unbranched p args).
Proof.
  intros p args HF. unfold reduce_unbranched.
  destruct (Nat.eqb (length args) (model_arity p)); [| apply Con_Lit].
  assert (Hc : concore_expr (op_spine p args))
    by (apply concore_fold_left_app; [exact HF | apply Con_PrimOp]).
  rewrite (lift_flat _ (concore_flat _ Hc)), (fold_leaves_not_if _ (op_spine_not_if p args)).
  unfold fold_leaf. destruct (smt_ground (op_spine p args)); [apply Con_Lit | exact Hc].
Qed.

Lemma ite_selects_arm : forall σ S ec et ef pt pf l,
  denotes S et pt -> denotes S ef pf ->
  contains σ S (EIf ec et ef) (ELit l) ->
  exists pc, denotes S ec pc /\ pc_value σ (PCPrim PIte (pc :: pt :: pf :: nil)) = l.
Proof.
  intros σ S ec et ef pt pf l Ht Hf Hc.
  destruct (contains_if_inv σ S ec et ef (ELit l) Hc)
    as [[[pc [Hd Hm]] Hct] | [[pc [Hd Hm]] Hcf]]; exists pc; split; try exact Hd.
  - pose proof (smt_concretion_determined σ S et _ l (ex_intro _ pt (conj Ht eq_refl)) Hct) as Hl.
    change ((if pc_value σ pc then pc_value σ pt else pc_value σ pf) = l).
    change (pc_value σ pc = true) in Hm. rewrite Hm. exact Hl.
  - pose proof (smt_concretion_determined σ S ef _ l (ex_intro _ pf (conj Hf eq_refl)) Hcf) as Hl.
    change ((if pc_value σ pc then pc_value σ pt else pc_value σ pf) = l).
    change (negb (pc_value σ pc) = true) in Hm. apply negb_true_iff in Hm. rewrite Hm. exact Hl.
Qed.

Lemma unbranched_ite_contains : forall σ S ec et ef pt pf l,
  denotes S et pt -> denotes S ef pf ->
  contains σ S (EIf ec et ef) (ELit l) ->
  contains σ S (reduce_unbranched PIte (ec :: et :: ef :: nil)) (ELit l).
Proof.
  intros σ S ec et ef pt pf l Ht Hf Hc.
  destruct (ite_selects_arm σ S ec et ef pt pf l Ht Hf Hc) as [pc [Hdc Hv]].
  unfold reduce_unbranched.
  replace (Nat.eqb (length (ec :: et :: ef :: nil)) (model_arity PIte)) with true by reflexivity.
  assert (Hflat : flat (op_spine PIte (ec :: et :: ef :: nil)) = true).
  { apply op_spine_flat.
    repeat constructor; eapply denotes_flat; eassumption. }
  rewrite (lift_flat _ Hflat), (fold_leaves_not_if _ (op_spine_not_if _ _)).
  assert (Hd : denotes S (op_spine PIte (ec :: et :: ef :: nil)) (PCPrim PIte (pc :: pt :: pf :: nil))).
  { apply (op_spine_denotes S (ec :: et :: ef :: nil) (pc :: pt :: pf :: nil) ltac:(repeat constructor; assumption) (EPrimOp op_ite) op_ite nil).
    intros Γ _. reflexivity. }
  unfold fold_leaf. destruct (smt_ground (op_spine PIte (ec :: et :: ef :: nil))) eqn:Hg.
  - pose proof (Hd · (sym_free_env_empty S)) as He.
    rewrite (closed_value_of _ _ He).
    destruct (ground_pc_value _ _ closed_model σ Hg He) as [Hcl _].
    rewrite Hcl, Hv. apply Cont_Lit.
  - apply (Cont_Denote σ S _ op_ite (ec :: et :: ef :: nil) l).
    + apply op_spine_unspool.
    + reflexivity.
    + exact Hg.
    + exists (PCPrim op_ite (pc :: pt :: pf :: nil)). split; [exact Hd | exact Hv].
Qed.

Lemma split_arg_not_if : forall k a, is_if a = false -> split_arg k a = k a.
Proof. intros k a H. destruct a; simpl in *; congruence. Qed.

Lemma split_args_not_if : forall k args,
  Forall (fun a => is_if a = false) args -> split_args k args = k args.
Proof.
  intros k args H. revert k. induction H as [| a args Ha _ IH]; intros k; [reflexivity |].
  cbn [split_args]. rewrite split_arg_not_if by exact Ha. apply IH.
Qed.

Lemma split_args_top : forall k args,
  split_args k args = k args \/ is_if (split_args k args) = true.
Proof.
  intros k args. revert k. induction args as [| a rest IH]; intros k; [left; reflexivity |].
  cbn [split_args]. destruct (is_if a) eqn:Ha.
  - destruct a; simpl in Ha; try discriminate. right. reflexivity.
  - rewrite split_arg_not_if by exact Ha. apply (IH (fun rest' => k (a :: rest'))).
Qed.

Lemma split_args_branch : forall k pre ec et ef post,
  Forall (fun e => is_if e = false) pre ->
  split_args k (pre ++ EIf ec et ef :: post) =
  EIf ec (split_args k (pre ++ et :: post)) (split_args k (pre ++ ef :: post)).
Proof.
  intros k pre ec et ef post H. revert k.
  induction H as [| a pre Ha _ IH]; intros k; [reflexivity |].
  cbn [app split_args]. rewrite !split_arg_not_if by exact Ha. apply IH.
Qed.

Lemma flat_all_not_if : forall args,
  Forall (fun a => flat a = true) args -> Forall (fun a => is_if a = false) args.
Proof. intros args H. eapply Forall_impl; [| exact H]. exact flat_not_if. Qed.

Lemma contains_picks_top : forall σ S e X,
  contains σ S e X -> exists L, picks σ S e L /\ contains σ S L X.
Proof.
  intros σ S e. induction e; intros X H;
    try (eexists; split; [apply picks_leaf; reflexivity | exact H]).
  destruct (contains_if_inv σ S _ _ _ X H) as [[Hm Hc] | [Hm Hc]].
  - destruct (IHe2 X Hc) as [L [Hp HL]]. exists L. split; [apply picks_then |]; assumption.
  - destruct (IHe3 X Hc) as [L [Hp HL]]. exists L. split; [apply picks_else |]; assumption.
Qed.

Lemma contains_args_picks : forall σ S args_s args_c,
  Forall2 (contains σ S) args_s args_c ->
  exists ls, Forall2 (picks σ S) args_s ls /\ Forall2 (contains σ S) ls args_c.
Proof.
  intros σ S args_s args_c H.
  induction H as [| a c args_s args_c Ha _ [ls [Hp Hc]]]; [exists nil; split; constructor |].
  destruct (contains_picks_top σ S a c Ha) as [L [HpL HcL]].
  exists (L :: ls). split; constructor; assumption.
Qed.

Lemma picks_split_arg : forall σ S K a L Y,
  picks σ S a L -> contains σ S (K L) Y -> contains σ S (split_arg K a) Y.
Proof.
  intros σ S K a L Y H. induction H; intros HK;
    [rewrite split_arg_not_if by assumption; exact HK
    | apply Cont_If_True; auto
    | apply Cont_If_False; auto].
Qed.

Lemma picks_split_args : forall σ S args ls,
  Forall2 (picks σ S) args ls ->
  forall k Y, contains σ S (k ls) Y -> contains σ S (split_args k args) Y.
Proof.
  intros σ S args ls H.
  induction H as [| a L args ls Ha _ IH]; intros k Y Hk; [exact Hk |].
  cbn [split_args]. apply (picks_split_arg σ S _ a L Y Ha).
  apply (IH (fun rest' => k (L :: rest'))). exact Hk.
Qed.

Lemma contains_instances_not_if : forall σ S args_s args_c,
  Forall2 (contains σ S) args_s args_c -> Forall (fun a => is_if a = false) args_c.
Proof.
  intros σ S args_s args_c H. induction H; constructor; [| assumption].
  apply flat_not_if. eapply contains_flat_instance. eassumption.
Qed.

#[export] Instance model_reduce_prim_contains : ReducePrimContains.
Proof.
  intros σ S p args_s args_c HF.
  change (contains σ S (model_reduce_prim p args_s) (model_reduce_prim p args_c)).
  unfold model_reduce_prim.
  rewrite (split_args_not_if _ args_c (contains_instances_not_if σ S _ _ HF)).
  destruct (contains_args_picks σ S _ _ HF) as [ls [Hp Hc]].
  apply (picks_split_args σ S _ _ Hp). apply unbranched_contains. exact Hc.
Qed.

#[export] Instance model_reduce_prim_denote : ReducePrimDenote.
Proof.
  intros σ S p args ls HF.
  change (denote σ S (model_reduce_prim p args) (prim_value p ls)).
  unfold model_reduce_prim.
  destruct (denote_args σ S args ls HF) as [pcs [Hds _]].
  rewrite (split_args_not_if _ args (flat_all_not_if _ (denotes_all_flat S args pcs Hds))).
  apply unbranched_denote. exact HF.
Qed.

#[export] Instance model_reduce_prim_ground_value : ReducePrimGroundValue.
Proof.
  intros p args H.
  change (smt_ground (model_reduce_prim p args) = true) in H.
  change (exists l, model_reduce_prim p args = ELit l).
  unfold model_reduce_prim in *.
  destruct (split_args_top (reduce_unbranched p) args) as [E | E].
  - rewrite E in *. apply unbranched_ground_value. exact H.
  - destruct (split_args (reduce_unbranched p) args); simpl in E, H; discriminate.
Qed.

#[export] Instance model_reduce_prim_saturated : ReducePrimSaturated.
Proof.
  intros p args p0 args0 H.
  change (unspool_app (model_reduce_prim p args) nil = (EPrimOp p0, args0)) in H.
  change (length args0 = model_arity p0).
  unfold model_reduce_prim in H.
  destruct (split_args_top (reduce_unbranched p) args) as [E | E].
  - rewrite E in H. exact (unbranched_saturated p args p0 args0 H).
  - destruct (split_args (reduce_unbranched p) args); simpl in E, H; discriminate.
Qed.

#[export] Instance model_reduce_prim_solvable : ReducePrimSolvable.
Proof.
  intros Γ p args HF.
  change (Solvable Γ (model_reduce_prim p args)). unfold model_reduce_prim.
  assert (Hflat : Forall (fun a => flat a = true) args)
    by (eapply Forall_impl; [| exact HF]; apply solvable_flat).
  rewrite (split_args_not_if _ args (flat_all_not_if _ Hflat)).
  apply unbranched_solvable. exact HF.
Qed.

#[export] Instance model_reduce_prim_concore : ReducePrimConcore.
Proof.
  intros p args HF.
  change (concore_expr (model_reduce_prim p args)). unfold model_reduce_prim.
  assert (Hflat : Forall (fun a => flat a = true) args)
    by (eapply Forall_impl; [| exact HF]; apply concore_flat).
  rewrite (split_args_not_if _ args (flat_all_not_if _ Hflat)).
  apply unbranched_concore. exact HF.
Qed.

#[export] Instance model_reduce_prim_ite_contains : ReducePrimIteContains.
Proof.
  intros σ S ec et ef pt pf l Ht Hf Hc.
  change (contains σ S (model_reduce_prim PIte (ec :: et :: ef :: nil)) (ELit l)).
  unfold model_reduce_prim.
  destruct (ite_selects_arm σ S ec et ef pt pf l Ht Hf Hc) as [pc [Hdc _]].
  assert (Hflat : Forall (fun a => flat a = true) (ec :: et :: ef :: nil))
    by (repeat constructor; eapply denotes_flat; eassumption).
  rewrite (split_args_not_if _ _ (flat_all_not_if _ Hflat)).
  exact (unbranched_ite_contains σ S ec et ef pt pf l Ht Hf Hc).
Qed.

#[export] Instance model_laws : ConCoreLaws.
Proof. constructor; exact _. Qed.

#[export] Instance model_reduce_prim_branch : ReducePrimBranch.
Proof.
  intros p pre ec et ef post H.
  exact (split_args_branch (reduce_unbranched p) pre ec et ef post H).
Qed.

#[export] Instance model_cast_expr_branch : CastExprBranch.
Proof. intros ec et ef γ. reflexivity. Qed.

#[export] Instance model_symfc_laws : SymFCLaws.
Proof. constructor; exact _. Qed.

(** ========================================================================= *)
(** 7. What the model shows                                                    *)
(** ========================================================================= *)

Theorem model_negation_is_satisfiable : prim_value op_not (false :: nil) = lit_true.
Proof. reflexivity. Qed.

Corollary some_literal_satisfies_negation :
  ~ (forall l : lit, prim_value op_not (l :: nil) <> lit_true).
Proof. intros H. exact (H false model_negation_is_satisfiable). Qed.

Theorem model_soundness_takes_else_branch :
  exists v_con,
    ⊢ᶜ else_match true false ⇓ᶜ v_con /\
    contains (else_model false) (only branch_var) (branch_on_x (ELit true) (ELit false)) v_con.
Proof. exact (soundness_takes_else_branch false model_negation_is_satisfiable true false). Qed.

Corollary model_else_branch_value : forall v,
  ⊢ᶜ else_match true false ⇓ᶜ v -> v = ELit false.
Proof.
  intros v Hv.
  exact (concore_eval_deterministic_top _ _ _ (else_match_concore true false) Hv
           (else_match_reads_else_arm true false)).
Qed.

Theorem model_soundness_on_negation : forall σ x,
  σ ⊨ pc_true ->
  exists v_con,
    ⊢ᶜ EApp (EPrimOp PNot) (ELit (σ x)) ⇓ᶜ v_con /\
    contains σ (only x) (reduce_prim PNot (EVar x :: nil)) v_con.
Proof.
  exact (soundness_on_computing_primitive PNot eq_refl (fun x => eq_refl)).
Qed.


