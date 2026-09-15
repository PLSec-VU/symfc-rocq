From SymCoreTheory Require Import SymCore ConCore Completeness Model.
From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat Arith.Wf_nat Lia.
Import ListNotations.
Open Scope string_scope.

Fixpoint nest (k : nat) (t : expr) : expr :=
  match k with
  | O => t
  | S k' => EThunk · (nest k' t)
  end.

Fixpoint nots (e : expr) : nat :=
  match e with
  | EApp (EPrimOp _) a => S (nots a)
  | _ => O
  end.

Definition inflation (j : expr) : nat := 10 + 5 * nots j.

Fixpoint inflate_not (a : expr) : expr :=
  match a with
  | EThunk _ _ => a
  | EIf c t j =>
      match c, t with
      | ELit true, EThunk _ _ => nest (inflation j) t
      | _, _ => EIf c (inflate_not t) (inflate_not j)
      end
  | _ => model_reduce_prim PNot (a :: nil)
  end.

Definition fuel_reduce_prim (p : model_primop) (args : list expr) : expr :=
  match p, args with
  | PNot, a :: nil => inflate_not a
  | _, _ => model_reduce_prim p args
  end.

Definition fuel_solver : SymCoreSolver :=
  Build_SymCoreSolver
    model_sat (PCLit true) eq_refl fuel_reduce_prim
    erase_cast keep_coercion keep_type.

#[local] Existing Instance fuel_solver | 0.

Lemma inflate_not_plain : forall a,
  is_if a = false -> is_thunk a = false -> inflate_not a = model_reduce_prim PNot (a :: nil).
Proof. intros a Hi Ht. destruct a; try discriminate; reflexivity. Qed.

Lemma inflate_not_if : forall c t j,
  inflate_not (EIf c t j) = EIf c (inflate_not t) (inflate_not j)
  \/ (c = ELit true /\ is_thunk t = true /\ inflate_not (EIf c t j) = nest (inflation j) t).
Proof.
  intros c t j. destruct c; try (left; reflexivity).
  destruct l; [| left; reflexivity].
  destruct t; try (left; reflexivity).
  right. auto.
Qed.

Lemma inflate_not_shape : forall a,
  (is_if a = false /\ is_thunk a = false /\ inflate_not a = model_reduce_prim PNot (a :: nil))
  \/ is_if (inflate_not a) = true \/ is_thunk (inflate_not a) = true.
Proof.
  intros a. destruct (is_if a) eqn:Hi; [| destruct (is_thunk a) eqn:Ht].
  - destruct a; try discriminate.
    destruct (inflate_not_if a1 a2 a3) as [H | [_ [_ H]]]; rewrite H; [right; left; reflexivity |].
    right; right. reflexivity.
  - destruct a; try discriminate. right; right. reflexivity.
  - left. auto using inflate_not_plain.
Qed.

Lemma solvable_not_if_thunk : forall Γ e, Solvable Γ e -> is_if e = false /\ is_thunk e = false.
Proof. intros Γ e H. inversion H; auto. Qed.

Lemma if_thunk_not_solvable : forall Γ e,
  is_if e = true \/ is_thunk e = true -> ~ Solvable Γ e.
Proof. intros Γ e [H | H] Hs; apply solvable_not_if_thunk in Hs; destruct Hs; congruence. Qed.

Lemma if_thunk_unspool : forall e p args,
  is_if e = true \/ is_thunk e = true -> unspool_app e [] <> (EPrimOp p, args).
Proof. intros e p args [H | H]; destruct e; try discriminate; simpl; congruence. Qed.

Lemma if_thunk_not_ground : forall e,
  is_if e = true \/ is_thunk e = true -> smt_ground e = false.
Proof. intros e [H | H]; destruct e; try discriminate; reflexivity. Qed.

#[local] Instance fuel_reduce_prim_solvable : ReducePrimSolvable.
Proof.
  intros Γ p args H.
  destruct p; [exact (model_reduce_prim_solvable Γ PAnd args H) | | exact (model_reduce_prim_solvable Γ PIte args H)].
  destruct args as [| a [| b rest]]; [exact (model_reduce_prim_solvable Γ PNot _ H) | | exact (model_reduce_prim_solvable Γ PNot _ H)].
  cbn [reduce_prim fuel_solver fuel_reduce_prim].
  pose proof (Forall_inv H) as Ha.
  destruct (solvable_not_if_thunk Γ a Ha) as [Hi Ht].
  rewrite (inflate_not_plain a Hi Ht). exact (model_reduce_prim_solvable Γ PNot [a] H).
Qed.

#[local] Instance fuel_reduce_prim_saturated : ReducePrimSaturated.
Proof.
  intros p args p0 args0 H.
  destruct p; [exact (model_reduce_prim_saturated PAnd args p0 args0 H) | | exact (model_reduce_prim_saturated PIte args p0 args0 H)].
  destruct args as [| a [| b rest]]; [exact (model_reduce_prim_saturated PNot _ p0 args0 H) | | exact (model_reduce_prim_saturated PNot _ p0 args0 H)].
  cbn [reduce_prim fuel_solver fuel_reduce_prim] in H.
  destruct (inflate_not_shape a) as [[_ [_ Heq]] | Hshape].
  - rewrite Heq in H. exact (model_reduce_prim_saturated PNot [a] p0 args0 H).
  - exfalso. exact (if_thunk_unspool _ p0 args0 Hshape H).
Qed.

#[local] Instance fuel_reduce_prim_concore : ReducePrimConcore.
Proof.
  intros p args H.
  destruct p; [exact (model_reduce_prim_concore PAnd args H) | | exact (model_reduce_prim_concore PIte args H)].
  destruct args as [| a [| b rest]]; [exact (model_reduce_prim_concore PNot _ H) | | exact (model_reduce_prim_concore PNot _ H)].
  cbn [reduce_prim fuel_solver fuel_reduce_prim].
  pose proof (Forall_inv H) as Ha.
  destruct a; try (rewrite inflate_not_plain by reflexivity; exact (model_reduce_prim_concore PNot _ H)).
  - exfalso. exact (not_concore_if _ _ _ Ha).
  - exact Ha.
Qed.

Lemma denote_not_if_thunk : forall σ S e l, denote σ S e l -> is_if e = false /\ is_thunk e = false.
Proof.
  intros σ S e l [pc [Hden _]].
  specialize (Hden · (sym_free_env_empty S)).
  destruct e; try discriminate; auto.
Qed.

#[local] Instance fuel_reduce_prim_denote : ReducePrimDenote.
Proof.
  intros σ S p args ls H.
  destruct p; [exact (model_reduce_prim_denote σ S PAnd args ls H) | | exact (model_reduce_prim_denote σ S PIte args ls H)].
  destruct args as [| a [| b rest]]; [exact (model_reduce_prim_denote σ S PNot _ ls H) | | exact (model_reduce_prim_denote σ S PNot _ ls H)].
  cbn [reduce_prim fuel_solver fuel_reduce_prim].
  destruct ls as [| l ls']; [inversion H |].
  assert (Ha : denote σ S a l) by (inversion H; assumption).
  destruct (denote_not_if_thunk σ S a l Ha) as [Hi Ht].
  rewrite (inflate_not_plain a Hi Ht). exact (model_reduce_prim_denote σ S PNot _ _ H).
Qed.

#[local] Instance fuel_reduce_prim_ground_value : ReducePrimGroundValue.
Proof.
  intros p args H.
  destruct p; [exact (model_reduce_prim_ground_value PAnd args H) | | exact (model_reduce_prim_ground_value PIte args H)].
  destruct args as [| a [| b rest]]; [exact (model_reduce_prim_ground_value PNot _ H) | | exact (model_reduce_prim_ground_value PNot _ H)].
  cbn [reduce_prim fuel_solver fuel_reduce_prim] in *.
  destruct (inflate_not_shape a) as [[_ [_ Heq]] | Hshape].
  - rewrite Heq in *. exact (model_reduce_prim_ground_value PNot [a] H).
  - exfalso. rewrite (if_thunk_not_ground _ Hshape) in H. discriminate.
Qed.

#[local] Instance fuel_reduce_prim_ite_contains : ReducePrimIteContains.
Proof. exact model_reduce_prim_ite_contains. Qed.

Lemma contains_thunk_right : forall σ S Γ e X,
  contains σ S (EThunk Γ e) X -> is_thunk X = true.
Proof.
  intros σ S Γ e X H. inversion H; subst; try reflexivity; try assumption.
  match goal with [Hu : unspool_app _ _ = _ |- _] => discriminate Hu end.
Qed.

Lemma contains_plain_right : forall σ S a X,
  contains σ S a X -> is_if a = false -> is_thunk a = false ->
  is_if X = false /\ is_thunk X = false.
Proof.
  intros σ S a X H Hi Ht.
  split; [apply flat_not_if; eapply contains_flat_instance; exact H |].
  inversion H; subst; simpl in *; congruence.
Qed.

Lemma nest_contains : forall σ S k t X,
  contains σ S t X -> is_thunk X = true -> contains σ S (nest k t) X.
Proof.
  intros σ S k t X H Ht. induction k as [| k IH]; simpl; [exact H |].
  apply (Cont_Thunk_Outer σ S · ·); [apply Cont_Env_Empty | exact IH | exact Ht].
Qed.

Lemma lit_true_not_models_not : forall σ S, ~ models_not_cond σ S (ELit true).
Proof.
  intros σ S [pc [Hden Hm]].
  specialize (Hden · (sym_free_env_empty S)). simpl in Hden. injection Hden as <-.
  unfold models in Hm. cbn in Hm. discriminate.
Qed.

Lemma inflate_not_contains : forall σ S a_s a_c,
  contains σ S a_s a_c -> contains σ S (inflate_not a_s) (inflate_not a_c).
Proof.
  intros σ S a_s. induction a_s; intros a_c H;
    try (destruct (contains_plain_right _ _ _ _ H eq_refl eq_refl) as [Hi Ht];
         rewrite (inflate_not_plain a_c Hi Ht);
         rewrite inflate_not_plain by reflexivity;
         exact (model_reduce_prim_contains σ S PNot _ _ (Forall2_cons _ _ H (Forall2_nil _)))).
  - assert (Hi : is_if a_c = false)
      by (apply flat_not_if; eapply contains_flat_instance; exact H).
    destruct (inflate_not_if a_s1 a_s2 a_s3) as [Heq | [Hc [Ht Heq]]]; rewrite Heq.
    + inversion H; subst.
      * apply Cont_If_True; [assumption | apply IHa_s2; assumption].
      * apply Cont_If_False; [assumption | apply IHa_s3; assumption].
      * match goal with [Hu : unspool_app _ _ = _ |- _] => discriminate Hu end.
    + subst. inversion H; subst.
      * destruct a_s2; try discriminate.
        match goal with [Hc : instantiates _ _ (EThunk _ _) a_c |- _] =>
          pose proof (contains_thunk_right _ _ _ _ _ Hc) as Hth end.
        destruct a_c; try discriminate. cbn [inflate_not].
        apply nest_contains; assumption.
      * exfalso. eapply lit_true_not_models_not. eassumption.
      * match goal with [Hu : unspool_app _ _ = _ |- _] => discriminate Hu end.
  - pose proof (contains_thunk_right _ _ _ _ _ H) as Hth.
    destruct a_c; try discriminate. simpl. exact H.
Qed.

#[local] Instance fuel_reduce_prim_contains : ReducePrimContains.
Proof.
  intros σ S p args_s args_c H.
  destruct p; [exact (model_reduce_prim_contains σ S PAnd _ _ H) | | exact (model_reduce_prim_contains σ S PIte _ _ H)].
  destruct H as [| a_s a_c rest_s rest_c Ha Hrest];
    [exact (model_reduce_prim_contains σ S PNot _ _ (Forall2_nil _)) |].
  destruct Hrest as [| b_s b_c rs rc Hb Hr].
  - cbn [reduce_prim fuel_solver fuel_reduce_prim]. apply inflate_not_contains. exact Ha.
  - exact (model_reduce_prim_contains σ S PNot _ _ (Forall2_cons _ _ Ha (Forall2_cons _ _ Hb Hr))).
Qed.

#[local] Instance fuel_laws : ConCoreLaws.
Proof.
  exact (@concore_laws model_sorts fuel_solver
    fuel_reduce_prim_solvable fuel_reduce_prim_saturated
    fuel_reduce_prim_concore model_cast_expr_concore
    model_models_sat model_prim_value_and
    fuel_reduce_prim_contains fuel_reduce_prim_denote fuel_reduce_prim_ground_value
    fuel_reduce_prim_ite_contains model_cast_expr_contains
    model_subst_coerc_contains_env model_subst_type_contains_env).
Qed.

Inductive tower : expr -> Prop :=
  | Tower_Bot : tower (EBot BOutOfFuel)
  | Tower_Not : forall a, tower a -> tower (EApp (EPrimOp PNot) a).

Lemma tower_flat_ground : forall a, tower a -> flat a = true /\ smt_ground a = false.
Proof.
  intros a H. induction H as [| a _ [Hf Hg]]; [split; reflexivity |].
  simpl. rewrite Hf, Hg. split; reflexivity.
Qed.

Lemma reduce_not_tower : forall a,
  tower a -> reduce_prim PNot (a :: nil) = EApp (EPrimOp PNot) a.
Proof.
  intros a H. destruct (tower_flat_ground a H) as [Hf Hg].
  assert (Hp : inflate_not a = model_reduce_prim PNot (a :: nil))
    by (destruct H; reflexivity).
  cbn [reduce_prim fuel_solver fuel_reduce_prim]. rewrite Hp.
  unfold model_reduce_prim.
  rewrite split_args_not_if by (constructor; [apply flat_not_if; exact Hf | constructor]).
  unfold reduce_unbranched, op_spine. cbn [length model_arity Nat.eqb fold_left].
  rewrite lift_flat by (simpl; rewrite Hf; reflexivity).
  simpl. unfold fold_leaf. simpl. rewrite Hg. reflexivity.
Qed.

Definition gv : var := "g".
Definition junk_arg : expr := EApp (EVar gv) (EVar gv).
Definition junk_body : expr := EApp (EPrimOp PNot) junk_arg.
Definition junk_fun : expr := ELam gv junk_body.
Definition junk : expr := EApp junk_fun junk_fun.

Inductive resolves : nat -> environment -> Prop :=
  | Resolves_Fun : forall Γ Γ0,
      lookup_env Γ gv = Some (Γ0, junk_fun) -> resolves 0 Γ
  | Resolves_Link : forall i Γ Γ0,
      lookup_env Γ gv = Some (Γ0, EVar gv) -> resolves i Γ0 -> resolves (S i) Γ.

Ltac kill_rule :=
  match goal with
  | [ Hs : sat _ = false |- _ ] => discriminate Hs
  | [ Hu : unspool_app _ _ = (ECon _, _) |- _ ] => discriminate Hu
  | [ Hu : unspool_app _ _ = (EIf _ _ _, _) |- _ ] => discriminate Hu
  | [ Hu : unspool_app _ _ = (EPrimOp _, _) |- _ ] => discriminate Hu
  | [ Hc : Comp _ (EPrimOp _) |- _ ] => inversion Hc
  | [ Hc : Comp _ (EBot _) |- _ ] => inversion Hc
  | [ Hc : Comp _ (EThunk _ (ELam _ _)) |- _ ] => inversion Hc; discriminate
  | [ Hl : lookup_env _ _ = None, Hs : lookup_env _ _ = Some _ |- _ ] => congruence
  end.

Lemma read_shape : forall i Γ Φ k v,
  resolves i Γ -> eval (Fin k) Φ Γ (EVar gv) v ->
  (v = EBot BOutOfFuel /\ k <= S i) \/ (exists Γ0, v = EThunk Γ0 junk_fun).
Proof.
  intros i Γ Φ k v HR. revert Φ k v.
  induction HR as [Γ Γ0 Hl | i Γ Γ0 Hl HR IH]; intros Φ k v H;
    (destruct k as [| k]; [left; split; [exact (eval_fin_zero_inv _ _ _ _ H) | lia] |]);
    inversion H; subst; try kill_rule;
    match goal with
    | [ Hs : lookup_env _ _ = Some _, Hv : eval (dec _) _ _ _ _ |- _ ] =>
        rewrite Hl in Hs; injection Hs as <- <-; rewrite dec_remaining in Hv
    end.
  - destruct k as [| k]; [left; split; [exact (eval_fin_zero_inv _ _ _ _ H5) | lia] |].
    unfold junk_fun in H5. inversion H5; subst; try kill_rule.
    right. eexists. reflexivity.
  - destruct (IH _ _ _ H5) as [[-> Hk] | Hr]; [left; split; [reflexivity | lia] | right; exact Hr].
Qed.

Lemma read_total : forall i Γ Φ k,
  resolves i Γ ->
  exists v, eval (Fin k) Φ Γ (EVar gv) v
    /\ (v = EBot BOutOfFuel \/ exists Γ0, v = EThunk Γ0 junk_fun).
Proof.
  intros i Γ Φ k HR. revert Φ k.
  induction HR as [Γ Γ0 Hl | i Γ Γ0 Hl HR IH]; intros Φ k;
    (destruct k as [| k]; [exists (EBot BOutOfFuel); split; [apply Eval_OutOfFuel | left; reflexivity] |]).
  - destruct k as [| k].
    + exists (EBot BOutOfFuel). split; [eapply Eval_Var; [exact Hl | apply Eval_OutOfFuel] | left; reflexivity].
    + exists (EThunk Γ0 junk_fun). split; [eapply Eval_Var; [exact Hl | apply Eval_Lam] | right; eexists; reflexivity].
  - destruct (IH Φ k) as [v [Hv Hs]]. exists v. split; [eapply Eval_Var; [exact Hl | exact Hv] | exact Hs].
Qed.

Lemma resolves_link : forall i Γ Γ0,
  resolves i Γ -> resolves (S i) (ExtendEnv gv (MkClosure Γ (EVar gv)) Γ0).
Proof.
  intros i Γ Γ0 HR. eapply Resolves_Link; [| exact HR]. reflexivity.
Qed.

Lemma resolves_fun : forall Γ Γ0,
  resolves 0 (ExtendEnv gv (MkClosure Γ junk_fun) Γ0).
Proof. intros Γ Γ0. eapply Resolves_Fun. reflexivity. Qed.

Lemma resolves_bound : forall i Γ, resolves i Γ -> lookup_env Γ gv <> None.
Proof. intros i Γ HR. destruct HR; congruence. Qed.

Lemma app_bot_value : forall Φ Γ k ea v,
  eval (Fin k) Φ Γ (EApp (EBot BOutOfFuel) ea) v -> v = EBot BOutOfFuel.
Proof.
  intros Φ Γ k ea v H. destruct k as [| k]; [exact (eval_fin_zero_inv _ _ _ _ H) |].
  inversion H; subst; try kill_rule; reflexivity.
Qed.

Lemma junk_bound : forall k,
  (forall i Γ Φ v, resolves i Γ -> eval (Fin k) Φ Γ junk_body v ->
     tower v /\ k <= 4 * nots v + i) /\
  (forall i Γ Φ v, resolves i Γ -> eval (Fin k) Φ Γ junk_arg v ->
     tower v /\ k <= 4 * nots v + i + 3).
Proof.
  intros k. induction k as [k IH] using lt_wf_ind.
  destruct k as [| k].
  { split; intros i Γ Φ v _ H; apply eval_fin_zero_inv in H; subst; split; [constructor | lia | constructor | lia]. }
  split; intros i Γ Φ v HR H.
  - unfold junk_body in H. inversion H; subst; try kill_rule.
    simpl in H3. injection H3 as <- <-.
    inversion H8 as [| a w rest rest' Hw Hrest]; subst.
    inversion Hrest; subst.
    rewrite dec_remaining in Hw.
    destruct (proj2 (IH k (Nat.lt_succ_diag_r k)) i Γ Φ w HR Hw) as [Ht Hk].
    rewrite (reduce_not_tower w Ht). simpl nots. split; [constructor; exact Ht | lia].
  - unfold junk_arg in H. inversion H; subst; try kill_rule.
    match goal with
    | [ Hf : eval _ _ _ (EVar gv) ?w, Ha : eval _ _ _ (EApp ?w (EVar gv)) _ |- _ ] =>
        rewrite dec_remaining in Hf, Ha;
        destruct (read_shape i Γ Φ k w HR Hf) as [[-> Hk] | [Γ0 ->]]
    end.
    + match goal with [Ha : eval _ _ _ (EApp (EBot _) _) _ |- _] => rewrite (app_bot_value _ _ _ _ _ Ha) end.
      split; [constructor | simpl; lia].
    + destruct k as [| k].
      * match goal with [Ha : eval (Fin 0) _ _ (EApp _ _) _ |- _] => apply eval_fin_zero_inv in Ha end.
        subst. split; [constructor | simpl; lia].
      * match goal with [Ha : eval _ _ _ (EApp (EThunk _ _) _) _ |- _] =>
          unfold junk_fun in Ha; inversion Ha; subst; try kill_rule end.
        match goal with [Hb : eval _ _ _ junk_body _ |- _] =>
          rewrite dec_remaining in Hb;
          destruct (proj1 (IH k ltac:(lia)) (S i) _ Φ v (resolves_link i Γ Γ0 HR) Hb) as [Ht Hk]
        end.
        split; [exact Ht | lia].
Qed.

Lemma junk_value_bound : forall Γ Φ k v,
  eval (Fin k) Φ Γ junk v -> tower v /\ k <= 4 * nots v + 2.
Proof.
  intros Γ Φ k v H. destruct k as [| k].
  { apply eval_fin_zero_inv in H. subst. split; [constructor | lia]. }
  unfold junk in H. inversion H; subst; try kill_rule.
  match goal with
  | [ Hf : eval _ _ _ junk_fun ?w, Ha : eval _ _ _ (EApp ?w junk_fun) _ |- _ ] =>
      rewrite dec_remaining in Hf, Ha; destruct k as [| k]
  end.
  - match goal with [Hf : eval (Fin 0) _ _ junk_fun _ |- _] => apply eval_fin_zero_inv in Hf end.
    subst. match goal with [Ha : eval _ _ _ (EApp (EBot _) _) _ |- _] => rewrite (app_bot_value _ _ _ _ _ Ha) end.
    split; [constructor | simpl; lia].
  - match goal with [Hf : eval _ _ _ junk_fun _ |- _] => unfold junk_fun in Hf; inversion Hf; subst; try kill_rule end.
    match goal with [Ha : eval _ _ _ (EApp (EThunk _ _) _) _ |- _] => inversion Ha; subst; try kill_rule end.
    match goal with [Hb : eval _ _ _ junk_body _ |- _] =>
      rewrite dec_remaining in Hb;
      destruct (proj1 (junk_bound k) 0 _ Φ v (resolves_fun Γ Γ) Hb) as [Ht Hk]
    end.
    split; [exact Ht | lia].
Qed.

Lemma junk_total : forall k,
  (forall i Γ Φ, resolves i Γ -> exists v, eval (Fin k) Φ Γ junk_body v) /\
  (forall i Γ Φ, resolves i Γ -> exists v, eval (Fin k) Φ Γ junk_arg v).
Proof.
  intros k. induction k as [k IH] using lt_wf_ind.
  destruct k as [| k].
  { split; intros; exists (EBot BOutOfFuel); apply Eval_OutOfFuel. }
  split; intros i Γ Φ HR.
  - destruct (proj2 (IH k (Nat.lt_succ_diag_r k)) i Γ Φ HR) as [w Hw].
    eexists. unfold junk_body. eapply Eval_AppPrim; [reflexivity | reflexivity |].
    constructor; [exact Hw | constructor].
  - destruct (read_total i Γ Φ k HR) as [w [Hw [-> | [Γ0 ->]]]].
    + exists (EBot BOutOfFuel). unfold junk_arg.
      eapply Eval_AppSpine; [apply Comp_Var; exact (resolves_bound i Γ HR) | exact Hw |].
      destruct k; [apply Eval_OutOfFuel | apply Eval_AppBot].
    + destruct k as [| k].
      * exists (EBot BOutOfFuel). unfold junk_arg.
        eapply Eval_AppSpine; [apply Comp_Var; exact (resolves_bound i Γ HR) | exact Hw | apply Eval_OutOfFuel].
      * destruct (proj1 (IH k ltac:(lia)) (S i) (ExtendEnv gv (MkClosure Γ (EVar gv)) Γ0) Φ
                    (resolves_link i Γ Γ0 HR)) as [v Hv].
        exists v. unfold junk_arg.
        eapply Eval_AppSpine; [apply Comp_Var; exact (resolves_bound i Γ HR) | exact Hw |].
        unfold junk_fun. apply Eval_AppAbs. exact Hv.
Qed.

Lemma junk_has_value : forall Γ Φ k, exists v, eval (Fin k) Φ Γ junk v.
Proof.
  intros Γ Φ k. destruct k as [| [| k]].
  - exists (EBot BOutOfFuel). apply Eval_OutOfFuel.
  - exists (EBot BOutOfFuel). unfold junk.
    eapply Eval_AppSpine; [apply Comp_Lam | apply Eval_OutOfFuel | apply Eval_OutOfFuel].
  - destruct (proj1 (junk_total k) 0 (ExtendEnv gv (MkClosure Γ junk_fun) Γ) Φ (resolves_fun Γ Γ))
      as [v Hv].
    exists v. unfold junk.
    eapply Eval_AppSpine; [apply Comp_Lam | unfold junk_fun; apply Eval_Lam |].
    unfold junk_fun. apply Eval_AppAbs. exact Hv.
Qed.

Definition kv : var := "k".
Definition yv : var := "y".
Definition id_fun : expr := ELam yv (EVar yv).
Definition model_arm : expr := EIf (@ELit model_sorts true) id_fun junk.
Definition consumer : expr := ELam kv (EApp (EVar kv) (@ELit model_sorts true)).
Definition sym_prog : expr := EApp consumer (EApp (EPrimOp PNot) model_arm).
Definition con_prog : expr := EApp consumer (EApp (EPrimOp PNot) id_fun).

Lemma nest_walk : forall k m t Φ Γ v,
  m <= k -> eval (Fin m) Φ Γ (nest k t) v -> v = EBot BOutOfFuel.
Proof.
  induction k as [| k IH]; intros m t Φ Γ v Hm H;
    (destruct m as [| m]; [exact (eval_fin_zero_inv _ _ _ _ H) |]); [lia |].
  cbn [nest] in H. inversion H; subst; try kill_rule.
  match goal with [Hv : eval (dec _) _ _ (nest _ _) _ |- _] =>
    rewrite dec_remaining in Hv; exact (IH m t Φ _ v ltac:(lia) Hv) end.
Qed.

Lemma arm_value : forall Φ Γ k v,
  eval (Fin (S (S k))) Φ Γ model_arm v ->
  exists J, v = EIf (@ELit model_sorts true) (EThunk Γ id_fun) J
    /\ eval (Fin (S k)) (Φ ∧ ¬ PCLit true) Γ junk J.
Proof.
  intros Φ Γ k v H. unfold model_arm in H. inversion H; subst; try kill_rule.
  match goal with
  | [ Hc : eval _ _ _ (@ELit model_sorts true) ?c, Hp : expr_to_pc _ ?c = Some _,
      Ht : eval _ _ _ id_fun ?t, Hj : eval _ _ _ junk ?j |- _ ] =>
      rewrite dec_remaining in Hc, Ht, Hj;
      inversion Hc; subst; try kill_rule;
      simpl in Hp; injection Hp as <-;
      unfold id_fun in Ht; inversion Ht; subst; try kill_rule;
      exists j; split; [reflexivity | exact Hj]
  end.
Qed.

Lemma prim_arm_value : forall Φ Γ k v,
  eval (Fin (S (S (S k)))) Φ Γ (EApp (EPrimOp PNot) model_arm) v ->
  exists J, v = nest (inflation J) (EThunk Γ id_fun)
    /\ eval (Fin (S k)) (Φ ∧ ¬ PCLit true) Γ junk J.
Proof.
  intros Φ Γ k v H. inversion H; subst; try kill_rule.
  match goal with [Hu : unspool_app _ _ = _ |- _] => simpl in Hu; injection Hu as <- <- end.
  match goal with [Hf : Forall2 _ _ _ |- _] =>
    inversion Hf as [| a w rest rest' Hw Hrest]; subst; inversion Hrest; subst end.
  rewrite dec_remaining in Hw.
  destruct (arm_value Φ Γ k w Hw) as [J [-> HJ]].
  exists J. split; [reflexivity | exact HJ].
Qed.

Lemma sym_prog_runs_out : forall k v,
  eval (Fin (7 + k)) pc_true · sym_prog v -> v = EBot BOutOfFuel.
Proof.
  intros k v H. unfold sym_prog, consumer in H. inversion H; subst; try kill_rule.
  match goal with [H6 : eval _ _ _ (ELam _ _) ?w, H8 : eval _ _ _ (EApp ?w _) _ |- _] =>
    rewrite dec_remaining in H6, H8; inversion H6; subst; try kill_rule;
    inversion H8; subst; try kill_rule end.
  match goal with [Hb : eval _ _ _ (EApp (EVar kv) _) _ |- _] =>
    rewrite dec_remaining in Hb; inversion Hb; subst; try kill_rule end.
  match goal with [Hf : eval _ _ _ (EVar kv) ?w, Ha : eval _ _ _ (EApp ?w _) _ |- _] =>
    rewrite dec_remaining in Hf, Ha; inversion Hf; subst;
    try match goal with [Hl : lookup_env _ _ = None |- _] => discriminate Hl end;
    try kill_rule end.
  match goal with [Hl : lookup_env _ kv = Some _, He : eval (dec _) _ _ _ ?w |- _] =>
    simpl in Hl; injection Hl as <- <-; rewrite dec_remaining in He;
    destruct (prim_arm_value pc_true · k w He) as [J [-> HJ]] end.
  destruct (junk_value_bound _ _ _ _ HJ) as [_ Hk].
  match goal with [Ha : eval _ _ _ (EApp (nest _ _) _) _ |- _] =>
    change (nest (inflation J) (EThunk · id_fun))
      with (EThunk · (nest (9 + 5 * nots J) (EThunk · id_fun))) in Ha;
    inversion Ha; subst; try kill_rule end.
  match goal with [Hw : eval _ _ _ (EThunk _ _) ?w, Hb : eval _ _ _ (EApp ?w _) _ |- _] =>
    pose proof (nest_walk (10 + 5 * nots J) (S (S (S k))) (EThunk · id_fun) pc_true _ w
                  ltac:(lia) Hw) as Hbot;
    subst w; exact (app_bot_value _ _ _ _ _ Hb) end.
Qed.

Lemma bot_not_contains_lit : forall σ S b l, ~ contains σ S (EBot b) (ELit l).
Proof.
  intros σ S b l H. inversion H.
  match goal with [Hu : unspool_app _ _ = _ |- _] => discriminate Hu end.
Qed.

Lemma nest_not_lam : forall i t, is_thunk t = true -> is_lam (nest i t) = false.
Proof. intros i t Ht. destruct i; [destruct t; try discriminate |]; reflexivity. Qed.

Lemma nest_value_total : forall i m Φ Γ,
  exists w, eval (Fin m) Φ Γ (nest i (EThunk · id_fun)) w
    /\ (w = EBot BOutOfFuel \/ w = EThunk · id_fun).
Proof.
  induction i as [| i IH]; intros m Φ Γ;
    (destruct m as [| m]; [exists (EBot BOutOfFuel); split; [apply Eval_OutOfFuel | left; reflexivity] |]).
  - destruct m as [| m].
    + exists (EBot BOutOfFuel). split; [apply Eval_Thunk; apply Eval_OutOfFuel | left; reflexivity].
    + exists (EThunk · id_fun). split; [apply Eval_Thunk; apply Eval_Lam | right; reflexivity].
  - destruct (IH m Φ ·) as [w [Hw Hs]].
    exists w. split; [cbn [nest]; apply Eval_Thunk; exact Hw | exact Hs].
Qed.

Lemma id_app_total : forall m Φ Γ,
  exists v, eval (Fin m) Φ Γ (EApp (EThunk · id_fun) (@ELit model_sorts true)) v.
Proof.
  intros m Φ Γ. destruct m as [| [| [| m]]].
  - exists (EBot BOutOfFuel). apply Eval_OutOfFuel.
  - exists (EBot BOutOfFuel). unfold id_fun. apply Eval_AppAbs. apply Eval_OutOfFuel.
  - exists (EBot BOutOfFuel). unfold id_fun. apply Eval_AppAbs.
    eapply Eval_Var; [reflexivity | apply Eval_OutOfFuel].
  - exists (@ELit model_sorts true). unfold id_fun. apply Eval_AppAbs.
    eapply Eval_Var; [reflexivity | apply Eval_Lit].
Qed.

Lemma walk_total : forall i m Φ Γ,
  exists v, eval (Fin m) Φ Γ (EApp (nest (S i) (EThunk · id_fun)) (@ELit model_sorts true)) v.
Proof.
  intros i m Φ Γ. destruct m as [| m]; [exists (EBot BOutOfFuel); apply Eval_OutOfFuel |].
  destruct (nest_value_total (S i) m Φ Γ) as [w [Hw [-> | ->]]].
  - exists (EBot BOutOfFuel).
    eapply Eval_AppSpine; [apply Comp_Thunk; apply nest_not_lam; reflexivity | exact Hw |].
    destruct m; [apply Eval_OutOfFuel | apply Eval_AppBot].
  - destruct (id_app_total m Φ Γ) as [v Hv]. exists v.
    eapply Eval_AppSpine; [apply Comp_Thunk; apply nest_not_lam; reflexivity | exact Hw | exact Hv].
Qed.

Lemma sym_prog_total : forall k, exists v, eval (Fin (7 + k)) pc_true · sym_prog v.
Proof.
  intros k.
  destruct (junk_has_value · (pc_true ∧ ¬ @PCLit model_sorts true) (S k)) as [J HJ].
  destruct (walk_total (9 + 5 * nots J) (S (S (S (S k)))) pc_true
              (extend_env · kv · (EApp (@EPrimOp model_sorts PNot) model_arm))) as [v Hv].
  exists v. unfold sym_prog, consumer.
  apply Eval_AppSpine with (ef' := EThunk · (ELam kv (EApp (EVar kv) (@ELit model_sorts true))));
    [apply Comp_Lam | apply Eval_Lam |].
  apply Eval_AppAbs.
  apply Eval_AppSpine with (ef' := nest (inflation J) (EThunk · id_fun));
    [apply Comp_Var; discriminate | | exact Hv].
  eapply Eval_Var; [reflexivity |].
  apply (@Eval_AppPrim model_sorts fuel_solver (Remaining (S (S k))) pc_true · (@EPrimOp model_sorts PNot) model_arm PNot
           (model_arm :: nil) (EIf (@ELit model_sorts true) (EThunk · id_fun) J :: nil));
    [reflexivity | reflexivity |].
  constructor; [| constructor].
  unfold model_arm.
  apply Eval_If with (pc_c := @PCLit model_sorts true); [apply Eval_Lit | reflexivity | apply Eval_Lam | exact HJ].
Qed.

Definition sigma_all : valuation := fun _ => true.
Definition no_symvars : symvars := fun _ => false.

Lemma lit_true_models_cond : models_cond sigma_all no_symvars (@ELit model_sorts true).
Proof. exists (@PCLit model_sorts true). split; [intros Γ _; reflexivity | reflexivity]. Qed.

Lemma prog_contains : contains sigma_all no_symvars sym_prog con_prog.
Proof.
  unfold sym_prog, con_prog, consumer, model_arm, id_fun.
  apply Cont_App.
  - apply Cont_Lam; [reflexivity |]. apply Cont_App; [apply Cont_Var_Bound; reflexivity | apply Cont_Lit].
  - apply Cont_App; [apply Cont_PrimOp |].
    apply Cont_If_True; [exact lit_true_models_cond |].
    apply Cont_Lam; [reflexivity | apply Cont_Var_Bound; reflexivity].
Qed.

Lemma con_prog_concore : concore_expr con_prog.
Proof. unfold con_prog, consumer, id_fun. repeat constructor. Qed.

Lemma con_prog_runs : · ⊢ᶜ con_prog ⇓ᶜ @ELit model_sorts true.
Proof.
  unfold eval_con, con_prog, consumer.
  apply Eval_AppSpine with (ef' := EThunk · (ELam kv (EApp (EVar kv) (@ELit model_sorts true))));
    [apply Comp_Lam | apply Eval_Lam |].
  apply Eval_AppAbs.
  apply Eval_AppSpine with (ef' := EThunk · id_fun); [apply Comp_Var; discriminate | |].
  - eapply Eval_Var; [reflexivity |].
    apply (@Eval_AppPrim model_sorts fuel_solver Unlimited pc_true · (@EPrimOp model_sorts PNot) id_fun PNot
             (id_fun :: nil) (EThunk · id_fun :: nil)); [reflexivity | reflexivity |].
    constructor; [apply Eval_Lam | constructor].
  - unfold id_fun. apply Eval_AppAbs. eapply Eval_Var; [reflexivity | apply Eval_Lit].
Qed.

Lemma sigma_models_pc_true : sigma_all ⊨ pc_true.
Proof. reflexivity. Qed.

Lemma sym_prog_budget_total : budget_total pc_true · sym_prog.
Proof.
  exists 7. intros n Hn. replace n with (7 + (n - 7)) by lia. apply sym_prog_total.
Qed.

Theorem fuel_inflation_counterexample :
  sigma_all ⊨ pc_true /\
  contains_env sigma_all no_symvars · · /\
  contains sigma_all no_symvars sym_prog con_prog /\
  concore_expr con_prog /\
  budget_total pc_true · sym_prog /\
  (· ⊢ᶜ con_prog ⇓ᶜ @ELit model_sorts true) /\
  (forall n, (7 <= n)%nat -> forall v_sym,
     eval (Fin n) pc_true · sym_prog v_sym ->
     ~ contains sigma_all no_symvars v_sym (@ELit model_sorts true)).
Proof.
  refine (conj sigma_models_pc_true (conj (Cont_Env_Empty _ _) (conj prog_contains
          (conj con_prog_concore (conj sym_prog_budget_total (conj con_prog_runs _)))))).
  intros n Hn v Hv. replace n with (7 + (n - 7)) in Hv by lia.
  rewrite (sym_prog_runs_out _ _ Hv). apply bot_not_contains_lit.
Qed.

Theorem target_completeness_is_false : ~ @target_completeness model_sorts fuel_solver.
Proof.
  intros Htarget.
  destruct fuel_inflation_counterexample as [Hm [Henv [Hc [Hcc [Hb [Hrun Hout]]]]]].
  destruct (Htarget pc_true · · sigma_all no_symvars sym_prog con_prog (@ELit model_sorts true)
              Hm Henv Hc Hcc Hb Hrun) as [h Hh].
  destruct (Hh (7 + h) ltac:(lia)) as [v [Hv Hcv]].
  exact (Hout (7 + h) ltac:(lia) v Hv Hcv).
Qed.

Theorem lawful_instance_refutes_target :
  @ConCoreLaws model_sorts fuel_solver /\ ~ @target_completeness model_sorts fuel_solver.
Proof. exact (conj fuel_laws target_completeness_is_false). Qed.

Lemma branch_stuck_at_fuel_one : forall Φ Γ ec et ef v,
  ~ eval (Fin 1) Φ Γ (EIf ec et ef) v.
Proof.
  intros Φ Γ ec et ef v H. inversion H; subst; try kill_rule.
  match goal with [Hc : eval (dec _) _ _ ec ?c, Hp : expr_to_pc _ ?c = Some _ |- _] =>
    apply eval_fin_zero_inv in Hc; subst; discriminate Hp end.
Qed.

Print Assumptions lawful_instance_refutes_target.
