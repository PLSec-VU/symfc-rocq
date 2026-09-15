From SymCoreTheory Require Import SymCore ConCore BranchLaws Completeness Model.
From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat Arith.Wf_nat Lia.
Import ListNotations.
Open Scope string_scope.

Fixpoint nest (k : nat) (t : expr) : expr :=
  match k with
  | O => t
  | S k' => EThunk · (nest k' t)
  end.

Fixpoint esize (e : expr) : nat :=
  match e with
  | EApp f a => S (esize f + esize a)
  | ELam _ b => S (esize b)
  | ECast e0 _ => S (esize e0)
  | ECase es _ => S (esize es)
  | EIf _ t f => S (esize t + esize f)
  | EThunk Γ e0 => S (envsize Γ + esize e0)
  | _ => 1
  end
with envsize (Γ : environment) : nat :=
  match Γ with
  | EmptyEnv => 0
  | ExtendEnv _ (MkClosure Γ' e) rest => S (envsize Γ' + esize e + envsize rest)
  end.

Definition wrap_con : dcon := "D".

Fixpoint wild_cast (e : expr) (γ : coercion) : expr :=
  match e with
  | EIf c t f => EIf c (wild_cast t γ) (wild_cast f γ)
  | EThunk _ _ => nest (5 * esize e) e
  | _ => EApp (ECon wrap_con) (EThunk · e)
  end.

Definition wild_solver : SymCoreSolver :=
  Build_SymCoreSolver
    model_sat (PCLit true) eq_refl model_reduce_prim
    wild_cast keep_coercion keep_type.

#[local] Existing Instance wild_solver | 0.

Lemma esize_positive : forall e, 1 <= esize e.
Proof. destruct e; simpl; lia. Qed.

Lemma contains_size_mut : forall σ S,
  (forall es ec, contains σ S es ec -> esize ec <= esize es)
  /\ (forall Γs Γc, contains_env σ S Γs Γc -> envsize Γc <= envsize Γs).
Proof.
  intros σ S. split.
  - apply (contains_mut _ σ S
             (fun es ec _ => esize ec <= esize es)
             (fun a ac _ => True)
             (fun Γs Γc _ => envsize Γc <= envsize Γs));
      intros; simpl in *; try lia; try exact I; apply esize_positive.
  - apply (contains_env_mut _ σ S
             (fun es ec _ => esize ec <= esize es)
             (fun a ac _ => True)
             (fun Γs Γc _ => envsize Γc <= envsize Γs));
      intros; simpl in *; try lia; try exact I; apply esize_positive.
Qed.

Lemma contains_size : forall σ S es ec, contains σ S es ec -> esize ec <= esize es.
Proof. intros σ S. apply contains_size_mut. Qed.

Lemma nest_contains_nest : forall σ S k j a_s a_c,
  j <= k -> contains σ S a_s a_c -> is_thunk a_c = true ->
  contains σ S (nest k a_s) (nest j a_c).
Proof.
  intros σ S k. induction k as [| k IH]; intros j a_s a_c Hjk H Ht.
  - replace j with 0 by lia. exact H.
  - destruct j as [| j].
    + cbn [nest]. apply (Cont_Thunk_Outer σ S · ·); [apply Cont_Env_Empty | | exact Ht].
      apply (IH 0); [lia | exact H | exact Ht].
    + cbn [nest]. apply (Cont_Thunk σ S · ·); [apply Cont_Env_Empty |].
      apply IH; [lia | exact H | exact Ht].
Qed.

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
  inversion H; subst; simpl in *; try discriminate; split; reflexivity.
Qed.

Lemma wild_cast_plain : forall e γ,
  is_if e = false -> is_thunk e = false -> wild_cast e γ = EApp (ECon wrap_con) (EThunk · e).
Proof. intros e γ Hi Ht. destruct e; try discriminate; reflexivity. Qed.

#[local] Instance wild_cast_expr_contains : CastExprContains.
Proof.
  intros σ S es. induction es; intros ec γ H; cbn [cast_expr wild_solver];
    try (destruct (contains_plain_right _ _ _ _ H eq_refl eq_refl) as [Hi Ht];
         rewrite (wild_cast_plain ec γ Hi Ht); rewrite wild_cast_plain by reflexivity;
         apply Cont_App; [apply Cont_Con | apply Cont_Thunk; [apply Cont_Env_Empty | exact H]]).
  - inversion H; subst; cbn [wild_cast].
    + apply Cont_If_True; [assumption | apply IHes2; assumption].
    + apply Cont_If_False; [assumption | apply IHes3; assumption].
    + match goal with [Hu : unspool_app _ _ = _ |- _] => discriminate Hu end.
  - pose proof (contains_thunk_right _ _ _ _ _ H) as Hth.
    destruct ec; try discriminate.
    change (contains σ S (nest (5 * esize (EThunk e es)) (EThunk e es))
                         (nest (5 * esize (EThunk e0 ec)) (EThunk e0 ec))).
    apply nest_contains_nest; [| exact H | reflexivity].
    pose proof (contains_size _ _ _ _ H). lia.
Qed.

Lemma nest_concore : forall k e, concore_expr e -> concore_expr (nest k e).
Proof.
  induction k as [| k IH]; intros e H; [exact H |].
  cbn [nest]. apply Con_Thunk; [apply CEnv_Empty | apply IH; exact H].
Qed.

#[local] Instance wild_cast_expr_concore : CastExprConcore.
Proof.
  intros e γ H. destruct e;
    try (apply Con_App; [apply Con_Con | apply Con_Thunk; [apply CEnv_Empty | exact H]]).
  - exfalso. exact (not_concore_if _ _ _ H).
  - apply nest_concore. exact H.
Qed.

#[local] Instance wild_cast_expr_branch : CastExprBranch.
Proof. intros ec et ef γ. reflexivity. Qed.

#[local] Instance wild_laws : ConCoreLaws.
Proof.
  exact (@concore_laws model_sorts wild_solver
    model_reduce_prim_solvable model_reduce_prim_saturated
    model_reduce_prim_concore wild_cast_expr_concore
    model_models_sat model_prim_value_and
    model_reduce_prim_contains model_reduce_prim_denote model_reduce_prim_ground_value
    model_reduce_prim_ite_contains wild_cast_expr_contains
    model_subst_coerc_contains_env model_subst_type_contains_env).
Qed.

#[local] Instance wild_reduce_prim_branch : ReducePrimBranch.
Proof. exact model_reduce_prim_branch. Qed.

#[local] Instance wild_symfc_laws : SymFCLaws.
Proof. exact (symfc_laws wild_laws wild_reduce_prim_branch wild_cast_expr_branch). Qed.

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
  cbn [reduce_prim wild_solver].
  unfold model_reduce_prim.
  rewrite split_args_not_if by (constructor; [apply flat_not_if; exact Hf | constructor]).
  unfold reduce_unbranched, op_spine. cbn [length model_arity Nat.eqb fold_left].
  rewrite lift_flat by (simpl; rewrite Hf; reflexivity).
  simpl. unfold fold_leaf. simpl. rewrite Hg. reflexivity.
Qed.

Fixpoint nots (e : expr) : nat :=
  match e with
  | EApp (EPrimOp _) a => S (nots a)
  | _ => O
  end.

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

Definition coerc0 : coercion := MkCoercion (TyCon tt) (TyCon tt) RoleNominal.
Definition zv : var := "z".
Definition wv : var := "w".
Definition kv : var := "k".
Definition unit_con : dcon := "U".
Definition id_fun : expr := ELam wv (EVar wv).
Definition arm_t : expr := ECast (ECon unit_con) coerc0.
Definition arm_f : expr := ECast junk coerc0.
Definition scrut : expr := EIf (@ELit model_sorts true) arm_t arm_f.
Definition alts : list alt := Alt wrap_con (zv :: nil) (ECast id_fun coerc0) :: nil.
Definition consumer : expr := ELam kv (EApp (EVar kv) (@ELit model_sorts true)).
Definition sym_prog : expr := EApp consumer (ECase scrut alts).
Definition con_prog : expr := EApp consumer (ECase arm_t alts).

Definition unit_field : expr := EThunk · (ECon unit_con).
Definition leak_env (Γ : environment) (J : expr) : environment :=
  ExtendEnv zv (MkClosure Γ (EIf (@ELit model_sorts true) unit_field (EThunk · J))) Γ.
Definition leak_clos (Γ : environment) (J : expr) : expr := EThunk (leak_env Γ J) id_fun.

Lemma case_value : forall Φ Γ k v,
  eval (Fin (S (S (S (S k))))) Φ Γ (ECase scrut alts) v ->
  exists J, v = nest (5 * esize (leak_clos Γ J)) (leak_clos Γ J)
    /\ eval (Fin (S k)) (Φ ∧ ¬ PCLit true) Γ junk J.
Proof.
  intros Φ Γ k v H. inversion H; subst; try kill_rule.
  match goal with
  | [ Hs : eval _ _ _ scrut ?w, Hf : fold_alts _ _ _ (merge _ ?w) _ _ |- _ ] =>
      rewrite dec_remaining in Hs, Hf; unfold scrut in Hs;
      inversion Hs; subst; try kill_rule
  end.
  match goal with
  | [ Hc : eval _ _ _ (ELit _) ?c, Hp : expr_to_pc _ ?c = Some _,
      Ht : eval _ _ _ arm_t _, Hj : eval _ _ _ arm_f _ |- _ ] =>
      rewrite dec_remaining in Hc, Ht, Hj;
      inversion Hc; subst; try kill_rule;
      simpl in Hp; injection Hp as <-;
      unfold arm_t in Ht; inversion Ht; subst; try kill_rule;
      unfold arm_f in Hj; inversion Hj; subst; try kill_rule
  end.
  match goal with
  | [ Hu : eval _ _ _ (ECon unit_con) _, Hj : eval _ _ _ junk ?J |- _ ] =>
      rewrite dec_remaining in Hu, Hj; inversion Hu; subst; try kill_rule;
      exists J; split; [| exact Hj];
      assert (Hplain : cast_expr J coerc0 = EApp (ECon wrap_con) (EThunk · J))
        by (destruct (proj1 (junk_value_bound _ _ _ _ Hj)); reflexivity)
  end.
  match goal with
  | [ Hu : unspool_app (ECon unit_con) [] = (ECon _, _) |- _ ] =>
      simpl in Hu; injection Hu as <- <-
  end.
  match goal with
  | [ Hf : fold_alts _ _ _ _ _ _ |- _ ] =>
      rewrite Hplain in Hf; cbn in Hf;
      inversion Hf; subst
  end.
  - match goal with
    | [ Hd : decompose_con_app _ = Some _, Hfind : find_alt _ alts = Some _,
        Hb : eval _ _ _ _ v |- _ ] =>
        cbn in Hd; injection Hd as <- <-; cbn in Hfind; injection Hfind as <- <-;
        inversion Hb; subst; try kill_rule
    end.
    match goal with
    | [ Hl : eval _ _ _ id_fun _ |- _ ] =>
        rewrite dec_remaining in Hl; unfold id_fun in Hl; inversion Hl; subst; try kill_rule
    end.
    reflexivity.
  - match goal with
    | [ Hn : match decompose_con_app _ with _ => _ end |- _ ] => cbn in Hn; discriminate Hn
    end.
Qed.

Lemma nots_le_esize : forall e, nots e <= esize e.
Proof.
  induction e; simpl; try lia.
  destruct e1; simpl in *; lia.
Qed.

Lemma leak_clos_size : forall Γ J, nots J + 8 <= esize (leak_clos Γ J).
Proof. intros Γ J. pose proof (nots_le_esize J) as HJ. simpl. lia. Qed.

Lemma nest_walk : forall k m t Φ Γ v,
  m <= k -> eval (Fin m) Φ Γ (nest k t) v -> v = EBot BOutOfFuel.
Proof.
  induction k as [| k IH]; intros m t Φ Γ v Hm H;
    (destruct m as [| m]; [exact (eval_fin_zero_inv _ _ _ _ H) |]); [lia |].
  cbn [nest] in H. inversion H; subst; try kill_rule.
  match goal with [Hv : eval (dec _) _ _ (nest _ _) _ |- _] =>
    rewrite dec_remaining in Hv; exact (IH m t Φ _ v ltac:(lia) Hv) end.
Qed.

Lemma walk_runs_out : forall j t Φ Γ a m v,
  is_thunk t = true -> m <= S j ->
  eval (Fin (S m)) Φ Γ (EApp (nest (S j) t) a) v -> v = EBot BOutOfFuel.
Proof.
  intros j t Φ Γ a m v Ht Hm H. cbn [nest] in H. inversion H; subst; try kill_rule.
  - exfalso. destruct j; destruct t; simpl in *; congruence.
  - match goal with
    | [ Hw : eval _ _ _ (EThunk · (nest j t)) ?w, Hb : eval _ _ _ (EApp ?w a) v |- _ ] =>
        rewrite dec_remaining in Hw, Hb;
        pose proof (nest_walk (S j) m t Φ Γ w Hm Hw) as Hbot; subst w;
        exact (app_bot_value _ _ _ _ _ Hb)
    end.
Qed.

Lemma sym_prog_runs_out : forall k v,
  eval (Fin (8 + k)) pc_true · sym_prog v -> v = EBot BOutOfFuel.
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
    destruct (case_value pc_true · k w He) as [J [-> HJ]] end.
  destruct (junk_value_bound _ _ _ _ HJ) as [_ Hk].
  pose proof (leak_clos_size · J) as Hsize.
  replace (5 * esize (leak_clos · J)) with (S (5 * esize (leak_clos · J) - 1)) in H12 by lia.
  apply (walk_runs_out _ (leak_clos · J) _ _ _ (S (S (S (S k)))) v eq_refl) in H12;
    [exact H12 | lia].
Qed.

Lemma bot_not_contains_lit : forall σ S b l, ~ contains σ S (EBot b) (ELit l).
Proof.
  intros σ S b l H. inversion H.
  match goal with [Hu : unspool_app _ _ = _ |- _] => discriminate Hu end.
Qed.

Lemma nest_not_lam : forall i t, is_thunk t = true -> is_lam (nest i t) = false.
Proof. intros i t Ht. destruct i; [destruct t; try discriminate |]; reflexivity. Qed.

Lemma nest_value_total : forall i m Φ Γ Γc,
  exists w, eval (Fin m) Φ Γ (nest i (EThunk Γc id_fun)) w
    /\ (w = EBot BOutOfFuel \/ w = EThunk Γc id_fun).
Proof.
  induction i as [| i IH]; intros m Φ Γ Γc;
    (destruct m as [| m]; [exists (EBot BOutOfFuel); split; [apply Eval_OutOfFuel | left; reflexivity] |]).
  - destruct m as [| m].
    + exists (EBot BOutOfFuel). split; [apply Eval_Thunk; apply Eval_OutOfFuel | left; reflexivity].
    + exists (EThunk Γc id_fun). split; [apply Eval_Thunk; apply Eval_Lam | right; reflexivity].
  - destruct (IH m Φ · Γc) as [w [Hw Hs]].
    exists w. split; [cbn [nest]; apply Eval_Thunk; exact Hw | exact Hs].
Qed.

Lemma id_app_total : forall m Φ Γ Γc,
  exists v, eval (Fin m) Φ Γ (EApp (EThunk Γc id_fun) (@ELit model_sorts true)) v.
Proof.
  intros m Φ Γ Γc. destruct m as [| [| [| m]]].
  - exists (EBot BOutOfFuel). apply Eval_OutOfFuel.
  - exists (EBot BOutOfFuel). unfold id_fun. apply Eval_AppAbs. apply Eval_OutOfFuel.
  - exists (EBot BOutOfFuel). unfold id_fun. apply Eval_AppAbs.
    eapply Eval_Var; [reflexivity | apply Eval_OutOfFuel].
  - exists (@ELit model_sorts true). unfold id_fun. apply Eval_AppAbs.
    eapply Eval_Var; [reflexivity | apply Eval_Lit].
Qed.

Lemma walk_total : forall i m Φ Γ Γc,
  exists v, eval (Fin m) Φ Γ (EApp (nest (S i) (EThunk Γc id_fun)) (@ELit model_sorts true)) v.
Proof.
  intros i m Φ Γ Γc. destruct m as [| m]; [exists (EBot BOutOfFuel); apply Eval_OutOfFuel |].
  destruct (nest_value_total (S i) m Φ Γ Γc) as [w [Hw [-> | ->]]].
  - exists (EBot BOutOfFuel).
    eapply Eval_AppSpine; [apply Comp_Thunk; apply nest_not_lam; reflexivity | exact Hw |].
    destruct m; [apply Eval_OutOfFuel | apply Eval_AppBot].
  - destruct (id_app_total m Φ Γ Γc) as [v Hv]. exists v.
    eapply Eval_AppSpine; [apply Comp_Thunk; apply nest_not_lam; reflexivity | exact Hw | exact Hv].
Qed.

Lemma case_total : forall k J,
  eval (Fin (S k)) (pc_true ∧ ¬ @PCLit model_sorts true) · junk J ->
  eval (Fin (S (S (S (S k))))) pc_true · (ECase scrut alts)
    (nest (5 * esize (leak_clos · J)) (leak_clos · J)).
Proof.
  intros k J HJ.
  assert (Hplain : cast_expr J coerc0 = EApp (ECon wrap_con) (EThunk · J))
    by (destruct (proj1 (junk_value_bound _ _ _ _ HJ)); reflexivity).
  apply Eval_Case with
    (es' := EIf (@ELit model_sorts true) (cast_expr (ECon unit_con) coerc0) (cast_expr J coerc0)).
  - unfold scrut. apply Eval_If with (pc_c := @PCLit model_sorts true);
      [apply Eval_Lit | reflexivity | |].
    + unfold arm_t. apply Eval_Cast. cbn [dec Fin].
      exact (Eval_Con (Remaining k) _ · (ECon unit_con) unit_con nil eq_refl).
    + unfold arm_f. apply Eval_Cast. exact HJ.
  - rewrite Hplain.
    change (merge · (EIf (@ELit model_sorts true) (cast_expr (ECon unit_con) coerc0)
                        (EApp (ECon wrap_con) (EThunk · J))))
      with (EApp (ECon wrap_con) (EIf (@ELit model_sorts true) unit_field (EThunk · J))).
    eapply FoldAlts_Con; [reflexivity | reflexivity |].
    exact (Eval_Cast (Remaining (S (S k))) pc_true (leak_env · J) id_fun coerc0
             (EThunk (leak_env · J) id_fun) (Eval_Lam _ _ _ _ _)).
Qed.

Lemma sym_prog_total : forall k, exists v, eval (Fin (8 + k)) pc_true · sym_prog v.
Proof.
  intros k.
  destruct (junk_has_value · (pc_true ∧ ¬ @PCLit model_sorts true) (S k)) as [J HJ].
  destruct (walk_total (5 * esize (leak_clos · J) - 1) (S (S (S (S (S k))))) pc_true
              (extend_env · kv · (ECase scrut alts)) (leak_env · J)) as [v Hv].
  exists v. unfold sym_prog, consumer.
  apply Eval_AppSpine with (ef' := EThunk · (ELam kv (EApp (EVar kv) (@ELit model_sorts true))));
    [apply Comp_Lam | apply Eval_Lam |].
  apply Eval_AppAbs.
  apply Eval_AppSpine with (ef' := nest (5 * esize (leak_clos · J)) (leak_clos · J));
    [apply Comp_Var; discriminate | |].
  - eapply Eval_Var; [reflexivity |]. exact (case_total k J HJ).
  - pose proof (leak_clos_size · J) as Hsize.
    replace (5 * esize (leak_clos · J)) with (S (5 * esize (leak_clos · J) - 1)) by lia.
    exact Hv.
Qed.

Definition sigma_all : valuation := fun _ => true.
Definition no_symvars : symvars := fun _ => false.

Lemma lit_true_models_cond : models_cond sigma_all no_symvars (@ELit model_sorts true).
Proof. exists (@PCLit model_sorts true). split; [intros Γ _; reflexivity | reflexivity]. Qed.

Lemma alts_contains : Forall2 (contains_alt sigma_all no_symvars) alts alts.
Proof.
  unfold alts, id_fun. constructor; [| constructor].
  apply Cont_Alt; [repeat constructor |].
  apply Cont_Cast. apply Cont_Lam; [reflexivity | apply Cont_Var_Bound; reflexivity].
Qed.

Lemma prog_contains : contains sigma_all no_symvars sym_prog con_prog.
Proof.
  unfold sym_prog, con_prog, consumer, scrut.
  apply Cont_App.
  - apply Cont_Lam; [reflexivity |]. apply Cont_App; [apply Cont_Var_Bound; reflexivity | apply Cont_Lit].
  - apply Cont_Case; [| exact alts_contains].
    apply Cont_If_True; [exact lit_true_models_cond |].
    unfold arm_t. apply Cont_Cast. apply Cont_Con.
Qed.

Lemma con_prog_concore : concore_expr con_prog.
Proof. unfold con_prog, consumer, arm_t, alts, id_fun. repeat constructor. Qed.

Lemma nest_eval_inf : forall i Φ Γ Γc,
  eval Inf Φ Γ (nest i (EThunk Γc id_fun)) (EThunk Γc id_fun).
Proof.
  induction i as [| i IH]; intros Φ Γ Γc; cbn [nest];
    apply Eval_Thunk; [apply Eval_Lam | apply IH].
Qed.

Lemma con_prog_runs :· ⊢ᶜ con_prog ⇓ᶜ @ELit model_sorts true.
Proof.
  unfold eval_con, con_prog, consumer.
  pose (clos_c := EThunk (ExtendEnv zv (MkClosure · unit_field) ·) id_fun).
  apply Eval_AppSpine with (ef' := EThunk · (ELam kv (EApp (EVar kv) (@ELit model_sorts true))));
    [apply Comp_Lam | apply Eval_Lam |].
  apply Eval_AppAbs.
  apply Eval_AppSpine with (ef' := nest (5 * esize clos_c) clos_c); [apply Comp_Var; discriminate | |].
  - eapply Eval_Var; [reflexivity |].
    apply Eval_Case with (es' := cast_expr (ECon unit_con) coerc0).
    + unfold arm_t. apply Eval_Cast.
      exact (Eval_Con Unlimited _ · (ECon unit_con) unit_con nil eq_refl).
    + change (merge · (cast_expr (ECon unit_con) coerc0))
        with (EApp (ECon wrap_con) unit_field).
      eapply FoldAlts_Con; [reflexivity | reflexivity |].
      exact (Eval_Cast Unlimited pc_true _ id_fun coerc0 clos_c (Eval_Lam _ _ _ _ _)).
  - replace (5 * esize clos_c) with (S (5 * esize clos_c - 1)) by (simpl; lia).
    eapply Eval_AppSpine; [apply Comp_Thunk; apply nest_not_lam; reflexivity | |].
    + exact (nest_eval_inf _ pc_true _ _).
    + unfold id_fun. apply Eval_AppAbs. eapply Eval_Var; [reflexivity | apply Eval_Lit].
Qed.

Lemma case_low_fuel : forall c Φ v,
  c <= 3 -> eval (Fin c) Φ · (ECase scrut alts) v ->
  v = EBot BOutOfFuel \/ exists t j, v = nest (S (S (S j))) t /\ is_thunk t = true.
Proof.
  intros c Φ v Hc H.
  destruct c as [| [| [| [| c]]]]; try lia;
    [left; exact (eval_fin_zero_inv _ _ _ _ H) | | |];
    inversion H; subst; try kill_rule;
    match goal with
    | [ Hs : eval _ _ _ scrut ?w, Hf : fold_alts _ _ _ (merge _ ?w) _ _ |- _ ] =>
        rewrite dec_remaining in Hs, Hf
    end.
  - apply eval_fin_zero_inv in H5. subst. simpl in H7.
    inversion H7; subst;
      first [ left; reflexivity
            | match goal with
              | [ Hd : decompose_con_app _ = Some _ |- _ ] => discriminate Hd
              | [ Hb : is_bot _ = false |- _ ] => discriminate Hb
              end ].
  - unfold scrut in H5. inversion H5; subst; try kill_rule.
    match goal with [Hc : eval _ _ _ (ELit _) ?c, Hp : expr_to_pc _ ?c = Some _ |- _] =>
      rewrite dec_remaining in Hc; apply eval_fin_zero_inv in Hc; subst; discriminate Hp end.
  - unfold scrut in H5. inversion H5; subst; try kill_rule.
    match goal with
    | [ Ht : eval _ _ _ arm_t _, Hj : eval _ _ _ arm_f _ |- _ ] =>
        rewrite dec_remaining in Ht, Hj;
        unfold arm_t in Ht; inversion Ht; subst; try kill_rule;
        unfold arm_f in Hj; inversion Hj; subst; try kill_rule
    end.
    repeat match goal with
    | [ Hz : eval (dec (Remaining 0)) _ _ _ _ |- _ ] =>
        rewrite dec_remaining in Hz; apply eval_fin_zero_inv in Hz; subst
    end.
    cbn in H7. inversion H7; subst.
    + match goal with
      | [ Hd : decompose_con_app _ = Some _, Hfind : find_alt _ alts = Some _,
          Hb : eval _ _ _ _ v |- _ ] =>
          cbn in Hd; injection Hd as <- <-; cbn in Hfind; injection Hfind as <- <-;
          inversion Hb; subst; try kill_rule
      end.
      match goal with
      | [ Hl : eval _ _ _ id_fun _ |- _ ] =>
          rewrite dec_remaining in Hl; unfold id_fun in Hl; inversion Hl; subst; try kill_rule
      end.
      right. do 2 eexists. split; reflexivity.
    + match goal with
      | [ Hn : match decompose_con_app _ with _ => _ end |- _ ] => cbn in Hn; discriminate Hn
      end.
Qed.

Lemma sym_prog_value_is_bot : forall n v,
  eval (Fin n) pc_true · sym_prog v -> v = EBot BOutOfFuel.
Proof.
  intros n v H.
  destruct (Nat.le_gt_cases 8 n) as [Hn | Hn].
  { replace n with (8 + (n - 8)) in H by lia. exact (sym_prog_runs_out _ _ H). }
  destruct n as [| n]; [exact (eval_fin_zero_inv _ _ _ _ H) |].
  unfold sym_prog, consumer in H. inversion H; subst; try kill_rule.
  match goal with [H6 : eval _ _ _ (ELam _ _) ?w, H8 : eval _ _ _ (EApp ?w _) _ |- _] =>
    rewrite dec_remaining in H6, H8; destruct n as [| n];
    [exact (eval_fin_zero_inv _ _ _ _ H8) |];
    inversion H6; subst; try kill_rule;
    inversion H8; subst; try kill_rule end.
  match goal with [Hb : eval _ _ _ (EApp (EVar kv) _) _ |- _] =>
    rewrite dec_remaining in Hb; destruct n as [| n];
    [exact (eval_fin_zero_inv _ _ _ _ Hb) |];
    inversion Hb; subst; try kill_rule end.
  match goal with [Hf : eval _ _ _ (EVar kv) ?w, Ha : eval _ _ _ (EApp ?w _) _ |- _] =>
    rewrite dec_remaining in Hf, Ha; destruct n as [| n];
    [exact (eval_fin_zero_inv _ _ _ _ Ha) |];
    inversion Hf; subst;
    try match goal with [Hl : lookup_env _ _ = None |- _] => discriminate Hl end;
    try kill_rule end.
  match goal with [Hl : lookup_env _ kv = Some _, He : eval (dec _) _ _ _ ?w |- _] =>
    simpl in Hl; injection Hl as <- <-; rewrite dec_remaining in He;
    destruct (case_low_fuel n pc_true w ltac:(lia) He) as [-> | [t [j [-> Ht]]]] end.
  - match goal with [Ha : eval _ _ _ (EApp (EBot _) _) v |- _] => exact (app_bot_value _ _ _ _ _ Ha) end.
  - match goal with [Ha : eval _ _ _ (EApp (nest _ _) _) v |- _] =>
      exact (walk_runs_out (S (S j)) t _ _ _ n v Ht ltac:(lia) Ha) end.
Qed.

Lemma sym_prog_budget_total : budget_total pc_true · sym_prog.
Proof.
  exists 8. intros n Hn. replace n with (8 + (n - 8)) by lia. apply sym_prog_total.
Qed.

Theorem zip_leak_counterexample :
  sigma_all ⊨ pc_true /\
  contains_env sigma_all no_symvars · · /\
  contains sigma_all no_symvars sym_prog con_prog /\
  concore_expr con_prog /\
  budget_total pc_true · sym_prog /\
  (· ⊢ᶜ con_prog ⇓ᶜ @ELit model_sorts true) /\
  (forall n, (8 <= n)%nat -> forall v_sym,
     eval (Fin n) pc_true · sym_prog v_sym ->
     ~ contains sigma_all no_symvars v_sym (@ELit model_sorts true)).
Proof.
  refine (conj eq_refl (conj (Cont_Env_Empty _ _) (conj prog_contains
          (conj con_prog_concore (conj sym_prog_budget_total (conj con_prog_runs _)))))).
  intros n Hn v Hv. replace n with (8 + (n - 8)) in Hv by lia.
  rewrite (sym_prog_runs_out _ _ Hv). apply bot_not_contains_lit.
Qed.

Theorem target_completeness_is_false : ~ @target_completeness model_sorts wild_solver.
Proof.
  intros Htarget.
  destruct zip_leak_counterexample as [Hm [Henv [Hc [Hcc [Hb [Hrun Hout]]]]]].
  destruct (Htarget pc_true · · sigma_all no_symvars sym_prog con_prog (@ELit model_sorts true)
              Hm Henv Hc Hcc Hb Hrun) as [h Hh].
  destruct (Hh (8 + h) ltac:(lia)) as [v [Hv Hcv]].
  exact (Hout (8 + h) ltac:(lia) v Hv Hcv).
Qed.

Theorem existential_corollary_is_false : ~ @existential_corollary model_sorts wild_solver.
Proof.
  intros Hex.
  destruct zip_leak_counterexample as [Hm [Henv [Hc [Hcc [Hb [Hrun _]]]]]].
  destruct (Hex pc_true · · sigma_all no_symvars sym_prog con_prog (@ELit model_sorts true)
              Hm Henv Hc Hcc Hb Hrun) as [k [v [Hv Hcv]]].
  rewrite (sym_prog_value_is_bot k v Hv) in Hcv.
  exact (bot_not_contains_lit _ _ _ _ Hcv).
Qed.

Theorem forall_form_lemma_is_false : ~ @forall_form_lemma model_sorts wild_solver.
Proof.
  intros Hall.
  destruct zip_leak_counterexample as [Hm [Henv [Hc [Hcc [_ [Hrun Hout]]]]]].
  destruct (Hall · con_prog (@ELit model_sorts true) Hrun pc_true · sigma_all no_symvars sym_prog
              Hm Henv Hc Hcc) as [h Hh].
  destruct (sym_prog_total h) as [v Hv].
  exact (Hout (8 + h) ltac:(lia) v Hv (Hh (8 + h) ltac:(lia) v Hv)).
Qed.

Theorem branch_lawful_instance_refutes_target :
  @SymFCLaws model_sorts wild_solver
  /\ ~ @target_completeness model_sorts wild_solver
  /\ ~ @existential_corollary model_sorts wild_solver
  /\ ~ @forall_form_lemma model_sorts wild_solver.
Proof.
  exact (conj wild_symfc_laws (conj target_completeness_is_false
           (conj existential_corollary_is_false forall_form_lemma_is_false))).
Qed.

Print Assumptions branch_lawful_instance_refutes_target.
