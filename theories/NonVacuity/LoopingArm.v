From SymCoreTheory Require Export NonVacuity.SoundnessInstances.
From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat Lia.
Import ListNotations.
Open Scope string_scope.

Section ElseBranchLoopingThenArm.

Definition nv_x : var := "x".
Definition nv_S : symvars := only nv_x.
Definition nv_sigma : valuation := fun _ => false.
Definition nv_phi : path_condition := PCLit true.
Definition nv_true : expr := @ELit model_sorts true.

Definition nv_alts : list alt :=
  Alt "T" [] self_app :: Alt "F" [] nv_true :: nil.
Definition nv_sym : expr := ECase (EIf (EVar nv_x) (ECon "T") (ECon "F")) nv_alts.
Definition nv_con : expr := ECase (ECon "F") nv_alts.

Lemma nv_sat : forall Φ, @sat model_sorts model_solver Φ = true.
Proof. reflexivity. Qed.
Definition nv_bot : expr := @EBot model_sorts BOutOfFuel.
Definition nv_undef : expr := @EBot model_sorts BUndefined.

Ltac nv_kill_prune :=
  match goal with [ H : sat _ = false |- _ ] => rewrite nv_sat in H; discriminate H end.

Ltac nv_live_fuel n :=
  match goal with [ Hf : Live ?f = Fin n |- _ ] =>
    destruct f as [| m]; [destruct n; discriminate Hf |] end.

Inductive nv_env : environment -> Prop :=
  | NVEnv_Empty : nv_env ·
  | NVEnv_Ext : forall Γ0 Γ e,
      nv_env Γ0 -> nv_env Γ ->
      (e = @self_app_fun model_sorts \/ e = @EVar model_sorts self_app_var) ->
      nv_env (extend_env Γ0 self_app_var Γ e).

Lemma nv_env_lookup : forall Γ, nv_env Γ -> forall z Γ1 e1,
  lookup_env Γ z = Some (Γ1, e1) ->
  nv_env Γ1 /\ (e1 = @self_app_fun model_sorts \/ e1 = @EVar model_sorts self_app_var).
Proof.
  intros Γ H. induction H as [| Γ0 Γ e HΓ0 IH0 HΓ IHΓ He]; intros z Γ1 e1 Hl.
  - discriminate Hl.
  - unfold extend_env in Hl. simpl in Hl.
    destruct (string_dec z self_app_var) as [_ | _].
    + injection Hl as <- <-. split; assumption.
    + exact (IH0 z Γ1 e1 Hl).
Qed.

Definition nv_selfval (v : expr) : Prop :=
  v = nv_bot \/ v = @EVar model_sorts self_app_var \/
  (exists Γ0, nv_env Γ0 /\ v = EThunk Γ0 (@self_app_fun model_sorts)).

Definition nv_loopterm (e : expr) : Prop :=
  e = @self_app model_sorts \/ e = @self_app_body model_sorts \/
  (exists Γ0, nv_env Γ0 /\
     e = EApp (EThunk Γ0 (@self_app_fun model_sorts)) (@self_app_fun model_sorts)) \/
  (exists Γ0, nv_env Γ0 /\
     e = EApp (EThunk Γ0 (@self_app_fun model_sorts)) (@EVar model_sorts self_app_var)) \/
  e = EApp nv_bot (@self_app_fun model_sorts) \/
  e = EApp nv_bot (@EVar model_sorts self_app_var).

Definition nv_selfterm (e : expr) : Prop :=
  nv_loopterm e \/ e = @self_app_fun model_sorts \/
  e = @EVar model_sorts self_app_var \/
  (exists Γ0, nv_env Γ0 /\ e = EThunk Γ0 (@self_app_fun model_sorts)) \/ e = nv_bot.

Lemma nv_fun_values : forall Φ n Γ v,
  eval (Fin n) Φ Γ (@self_app_fun model_sorts) v ->
  v = EThunk Γ (@self_app_fun model_sorts) \/ v = nv_bot.
Proof.
  intros Φ n Γ v H. unfold self_app_fun in H.
  inversion H; subst; try nv_kill_prune; try (simpl in *; discriminate);
    [left; reflexivity | right; reflexivity].
Qed.

Ltac nv_sv :=
  unfold nv_selfval, nv_bot;
  first [ left; reflexivity | right; left; reflexivity ].

Lemma nv_thunk_values : forall Φ n Γ Γ0 v,
  eval (Fin n) Φ Γ (EThunk Γ0 (@self_app_fun model_sorts)) v ->
  v = EThunk Γ0 (@self_app_fun model_sorts) \/ v = nv_bot.
Proof.
  intros Φ n Γ Γ0 v H.
  inversion H; subst; try nv_kill_prune; try (simpl in *; discriminate);
    try (right; reflexivity).
  nv_live_fuel n. change (dec (Remaining m)) with (Fin m) in *.
  match goal with [ Hv : eval _ _ Γ0 (@self_app_fun model_sorts) v |- _ ] =>
    destruct (nv_fun_values _ _ _ _ Hv) as [-> | ->] end;
    [left; reflexivity | right; reflexivity].
Qed.

Lemma nv_varf_values : forall n Φ Γ v,
  nv_env Γ -> eval (Fin n) Φ Γ (@EVar model_sorts self_app_var) v -> nv_selfval v.
Proof.
  induction n as [| n IH]; intros Φ Γ v HΓ H;
    (inversion H; subst; try nv_kill_prune; try (simpl in *; discriminate); try nv_sv).
  change (dec (Remaining n)) with (Fin n) in *.
  match goal with [ Hl : lookup_env Γ self_app_var = Some _ |- _ ] =>
    destruct (nv_env_lookup Γ HΓ _ _ _ Hl) as [HΓ1 [-> | ->]] end.
  - match goal with [ Hv : eval _ _ _ (@self_app_fun model_sorts) v |- _ ] =>
      destruct (nv_fun_values _ _ _ _ Hv) as [-> | ->] end;
      [right; right; eexists; split; [eassumption | reflexivity] | left; reflexivity].
  - match goal with [ Hv : eval _ _ ?G (@EVar model_sorts self_app_var) v |- _ ] =>
      exact (IH _ G v HΓ1 Hv) end.
Qed.

Lemma nv_loop_values : forall n Φ Γ e v,
  nv_env Γ -> nv_loopterm e -> eval (Fin n) Φ Γ e v -> v = nv_bot.
Proof.
  induction n as [| n IH]; intros Φ Γ e v HΓ He Hev.
  - inversion Hev; subst; reflexivity.
  - destruct He as [He | [He | [[Γ0 [HΓ0 He]] | [[Γ0 [HΓ0 He]] | [He | He]]]]]; subst e.
    + unfold self_app in Hev.
      inversion Hev; subst; try nv_kill_prune; try sym_absurd;
        try (simpl in *; discriminate); try reflexivity.
      change (dec (Remaining n)) with (Fin n) in *.
      match goal with [ Hf : eval _ Φ Γ (@self_app_fun model_sorts) ?w |- _ ] =>
        destruct (nv_fun_values Φ n Γ w Hf) as [-> | ->] end.
      * match goal with [ Ha : eval _ Φ Γ (EApp _ _) v |- _ ] =>
          refine (IH Φ Γ _ v HΓ _ Ha) end.
        right; right; left. exists Γ. split; [exact HΓ | reflexivity].
      * match goal with [ Ha : eval _ Φ Γ (EApp _ _) v |- _ ] =>
          refine (IH Φ Γ _ v HΓ _ Ha) end.
        right; right; right; right; left. reflexivity.
    + unfold self_app_body in Hev.
      inversion Hev; subst; try nv_kill_prune; try sym_absurd;
        try (simpl in *; discriminate); try reflexivity.
      change (dec (Remaining n)) with (Fin n) in *.
      match goal with [ Hf : eval _ Φ Γ (@EVar model_sorts self_app_var) ?w |- _ ] =>
        destruct (nv_varf_values n Φ Γ w HΓ Hf) as [-> | [-> | [Γ1 [HΓ1 ->]]]] end.
      * match goal with [ Ha : eval _ Φ Γ (EApp _ _) v |- _ ] =>
          refine (IH Φ Γ _ v HΓ _ Ha) end.
        right; right; right; right; right. reflexivity.
      * match goal with [ Ha : eval _ Φ Γ (EApp _ _) v |- _ ] =>
          refine (IH Φ Γ _ v HΓ _ Ha) end.
        right; left. reflexivity.
      * match goal with [ Ha : eval _ Φ Γ (EApp _ _) v |- _ ] =>
          refine (IH Φ Γ _ v HΓ _ Ha) end.
        right; right; right; left. exists Γ1. split; [exact HΓ1 | reflexivity].
    + inversion Hev; subst; try nv_kill_prune; try sym_absurd;
        try (simpl in *; discriminate); try reflexivity.
      change (dec (Remaining n)) with (Fin n) in *.
      match goal with [ Ha : eval _ Φ _ (@self_app_body model_sorts) v |- _ ] =>
        refine (IH Φ _ _ v _ _ Ha) end.
      * apply NVEnv_Ext; [exact HΓ0 | exact HΓ | left; reflexivity].
      * right; left. reflexivity.
    + inversion Hev; subst; try nv_kill_prune; try sym_absurd;
        try (simpl in *; discriminate); try reflexivity.
      change (dec (Remaining n)) with (Fin n) in *.
      match goal with [ Ha : eval _ Φ _ (@self_app_body model_sorts) v |- _ ] =>
        refine (IH Φ _ _ v _ _ Ha) end.
      * apply NVEnv_Ext; [exact HΓ0 | exact HΓ | right; reflexivity].
      * right; left. reflexivity.
    + inversion Hev; subst; try nv_kill_prune; try sym_absurd;
        try (simpl in *; discriminate); try reflexivity.
    + inversion Hev; subst; try nv_kill_prune; try sym_absurd;
        try (simpl in *; discriminate); try reflexivity.
Qed.

Lemma nv_bot_values : forall Φ n Γ b v,
  eval (Fin n) Φ Γ (@EBot model_sorts b) v -> v = @EBot model_sorts b \/ v = nv_bot.
Proof.
  intros Φ n Γ b v H. inversion H; subst; try nv_kill_prune;
    try (simpl in *; discriminate); [left; reflexivity | right; reflexivity].
Qed.

Lemma nv_selfterm_values : forall n Φ Γ e v,
  nv_env Γ -> nv_selfterm e -> eval (Fin n) Φ Γ e v -> nv_selfval v.
Proof.
  intros n Φ Γ e v HΓ [Hl | [-> | [-> | [[Γ0 [HΓ0 ->]] | ->]]]] Hev.
  - left. exact (nv_loop_values n Φ Γ e v HΓ Hl Hev).
  - destruct (nv_fun_values Φ n Γ v Hev) as [-> | ->];
      [right; right; exists Γ; split; [exact HΓ | reflexivity] | left; reflexivity].
  - exact (nv_varf_values n Φ Γ v HΓ Hev).
  - destruct (nv_thunk_values Φ n Γ Γ0 v Hev) as [-> | ->];
      [right; right; exists Γ0; split; [exact HΓ0 | reflexivity] | left; reflexivity].
  - destruct (nv_bot_values Φ n Γ BOutOfFuel v Hev) as [-> | ->]; left; reflexivity.
Qed.

Lemma nv_selfval_bound : forall Γ v, nv_selfval v -> smt_size (merge Γ v) <= 8.
Proof.
  intros Γ v [-> | [-> | [Γ0 [_ ->]]]]; vm_compute; lia.
Qed.

Lemma nv_varx_values : forall Φ n v,
  eval (Fin n) Φ · (@EVar model_sorts nv_x) v -> v = @EVar model_sorts nv_x \/ v = nv_bot.
Proof.
  intros Φ n v H. inversion H; subst; try nv_kill_prune;
    try (simpl in *; discriminate); [left; reflexivity | right; reflexivity].
Qed.

Lemma nv_con_values : forall Φ n Γ d v,
  eval (Fin n) Φ Γ (@ECon model_sorts d) v -> v = @ECon model_sorts d \/ v = nv_bot.
Proof.
  intros Φ n Γ d v H. inversion H; subst; try nv_kill_prune;
    try (simpl in *; discriminate); [| right; reflexivity].
  match goal with [ Hu : unspool_app (ECon d) nil = _ |- _ ] =>
    simpl in Hu; injection Hu as <- <- end.
  left. reflexivity.
Qed.

Lemma nv_lit_values : forall Φ n Γ v,
  eval (Fin n) Φ Γ nv_true v -> v = nv_true \/ v = nv_bot.
Proof.
  intros Φ n Γ v H. unfold nv_true in H. inversion H; subst; try nv_kill_prune;
    try (simpl in *; discriminate); [left; reflexivity | right; reflexivity].
Qed.

Definition nv_conish (a : expr) : Prop :=
  (exists d, a = @ECon model_sorts d) \/ a = nv_bot.

Definition nv_thenval (t : expr) : Prop := t = @ECon model_sorts "T" \/ t = nv_bot.
Definition nv_elseval (f : expr) : Prop := f = @ECon model_sorts "F" \/ f = nv_bot.

Definition nv_guardval (v : expr) : Prop :=
  v = nv_bot \/
  (exists t f, v = EIf (@EVar model_sorts nv_x) t f /\ nv_thenval t /\ nv_elseval f).

Lemma nv_guard_values : forall Φ n v,
  eval (Fin n) Φ · (EIf (@EVar model_sorts nv_x) (ECon "T") (ECon "F")) v ->
  nv_guardval v.
Proof.
  intros Φ n v H. inversion H; subst; try nv_kill_prune;
    try (simpl in *; discriminate); [| left; reflexivity].
  nv_live_fuel n. change (dec (Remaining m)) with (Fin m) in *.
  match goal with [ Hc : eval _ Φ · (@EVar model_sorts nv_x) ?c |- _ ] =>
    destruct (nv_varx_values Φ m c Hc) as [-> | ->] end;
    [| exfalso;
       match goal with [ Hpc : expr_to_pc · _ = Some _ |- _ ] =>
         unfold nv_bot in Hpc; simpl in Hpc; discriminate Hpc end ].
  right.
  match goal with [ Ht : eval _ _ _ (ECon "T") ?t |- _ ] =>
    destruct (nv_con_values _ m · "T" t Ht) as [-> | ->] end;
  match goal with [ Hf : eval _ _ _ (ECon "F") ?w |- _ ] =>
    destruct (nv_con_values _ m · "F" w Hf) as [-> | ->] end;
  eexists; eexists; repeat split; unfold nv_thenval, nv_elseval;
    first [ reflexivity | left; reflexivity | right; reflexivity ].
Qed.

Definition nv_scrut (m : expr) : Prop :=
  nv_conish m \/
  (exists t f, m = EIf (@EVar model_sorts nv_x) t f /\ nv_thenval t /\ nv_elseval f).

Lemma nv_merge_scrut : forall v, nv_guardval v -> nv_scrut (merge · v).
Proof.
  intros v [-> | [t [f [-> [[-> | ->] [-> | ->]]]]]].
  - left. right. reflexivity.
  - right. exists (@ECon model_sorts "T"), (@ECon model_sorts "F").
    unfold nv_thenval, nv_elseval. repeat split;
      first [ reflexivity | left; reflexivity ].
  - right. exists (@ECon model_sorts "T"), nv_bot.
    unfold nv_thenval, nv_elseval. repeat split;
      first [ reflexivity | left; reflexivity | right; reflexivity ].
  - right. exists nv_bot, (@ECon model_sorts "F").
    unfold nv_thenval, nv_elseval. repeat split;
      first [ reflexivity | left; reflexivity | right; reflexivity ].
  - left. right. reflexivity.
Qed.

Definition nv_armval (a : expr) : Prop :=
  a = nv_bot \/ a = nv_true \/ a = nv_undef.

Definition nv_foldval (v : expr) : Prop :=
  nv_armval v \/
  (exists t f, v = EIf (@EVar model_sorts nv_x) t f /\ nv_armval t /\ nv_armval f).

Lemma nv_fold_con_values : forall Φ n d v,
  fold_alts (Fin n) Φ · (@ECon model_sorts d) nv_alts v -> nv_armval v.
Proof.
  intros Φ n d v H. inversion H; subst; try (simpl in *; discriminate).
  - unfold decompose_con_app in H0. simpl in H0. injection H0 as <- <-.
    unfold nv_alts in H1. simpl in H1.
    destruct (string_dec d "T") as [_ | _].
    + injection H1 as <- <-. simpl in H2.
      left. exact (nv_loop_values _ _ _ _ _ NVEnv_Empty (or_introl eq_refl) H2).
    + destruct (string_dec d "F") as [_ | _]; [| discriminate H1].
      injection H1 as <- <-. simpl in H2.
      destruct (nv_lit_values _ _ _ _ H2) as [-> | ->];
        [right; left; reflexivity | left; reflexivity].
  - right; right; reflexivity.
Qed.

Lemma nv_fold_arm_values : forall Φ n a v,
  (a = @ECon model_sorts "T" \/ a = @ECon model_sorts "F" \/ a = nv_bot) ->
  fold_alts (Fin n) Φ · a nv_alts v -> nv_armval v.
Proof.
  intros Φ n a v [-> | [-> | ->]] H.
  - exact (nv_fold_con_values Φ n "T" v H).
  - exact (nv_fold_con_values Φ n "F" v H).
  - left. exact (fold_alts_bot_same (Fin n) Φ · BOutOfFuel nv_alts v H).
Qed.

Lemma nv_fold_values : forall Φ n m v,
  nv_scrut m -> fold_alts (Fin n) Φ · m nv_alts v -> nv_foldval v.
Proof.
  intros Φ n m v [[[d ->] | ->] | [t [f [-> [Ht Hf]]]]] H.
  - left. exact (nv_fold_con_values Φ n d v H).
  - left. left. exact (fold_alts_bot_same (Fin n) Φ · BOutOfFuel nv_alts v H).
  - destruct (fold_alts_if_some_inv (Fin n) Φ · (@EVar model_sorts nv_x) t f nv_alts v
                (@PCVar model_sorts nv_x) eq_refl H) as [et' [ef' [-> [Hft Hff]]]].
    right. exists et', ef'. split; [reflexivity | split].
    + refine (nv_fold_arm_values _ n t et' _ Hft).
      destruct Ht as [-> | ->]; [left; reflexivity | right; right; reflexivity].
    + refine (nv_fold_arm_values _ n f ef' _ Hff).
      destruct Hf as [-> | ->]; [right; left; reflexivity | right; right; reflexivity].
Qed.

Lemma nv_case_values : forall Φ n v,
  eval (Fin n) Φ · nv_sym v -> nv_foldval v \/ v = nv_bot.
Proof.
  intros Φ n v H. unfold nv_sym in H.
  inversion H; subst; try nv_kill_prune; try (simpl in *; discriminate);
    [| right; reflexivity].
  nv_live_fuel n. change (dec (Remaining m)) with (Fin m) in *.
  left.
  match goal with [ Hs : eval _ Φ · (EIf _ _ _) ?w |- _ ] =>
    pose proof (nv_merge_scrut w (nv_guard_values Φ m w Hs)) as Hsc end.
  match goal with [ Hfo : fold_alts _ Φ · _ nv_alts v |- _ ] =>
    exact (nv_fold_values Φ m _ v Hsc Hfo) end.
Qed.

Lemma nv_foldval_bound : forall v, nv_foldval v -> smt_size (merge · v) <= 8.
Proof.
  intros v [[-> | [-> | ->]] | [t [f [-> [[-> | [-> | ->]] [-> | [-> | ->]]]]]]];
    vm_compute; lia.
Qed.

Definition nv_outer (e : expr) : Prop :=
  e = nv_sym \/ e = EIf (@EVar model_sorts nv_x) (ECon "T") (ECon "F") \/
  e = @EVar model_sorts nv_x \/ e = @ECon model_sorts "T" \/
  e = @ECon model_sorts "F" \/ e = nv_true.

Definition nv_reach (st : sym_state) : Prop :=
  match st with
  | SEval Γ e => (Γ = · /\ nv_outer e) \/ (nv_env Γ /\ nv_selfterm e)
  | SFold Γ m alts => Γ = · /\ alts = nv_alts /\ nv_scrut m
  end.

Ltac nv_ex := eexists; (split; [| reflexivity]); assumption.

Ltac nv_disj := first [ reflexivity | nv_ex | left; nv_disj | right; nv_disj ].

Ltac nv_opick := left; split; [reflexivity | unfold nv_outer; nv_disj].

Ltac nv_spick :=
  right; split; [ assumption | unfold nv_selfterm, nv_loopterm; nv_disj ].

Ltac nv_cases H :=
  destruct H as [[-> He] | [HE He]];
  [ cbv beta delta [nv_outer] in He
  | cbv beta delta [nv_selfterm nv_loopterm] in He ];
  repeat match goal with
    | [ Hx : _ \/ _ |- _ ] => destruct Hx
    | [ Hx : exists _, _ |- _ ] => destruct Hx
    | [ Hx : _ /\ _ |- _ ] => destruct Hx
    end;
  subst;
  unfold nv_sym, nv_true, nv_bot, self_app, self_app_fun, self_app_body in *.

Lemma nv_reach_step : forall Φ st Φ' st', nv_reach st -> sym_step Φ st Φ' st' -> nv_reach st'.
Proof.
  intros Φ st Φ' st' Hr Hstep.
  destruct Hstep; simpl in Hr |- *.
  - nv_cases Hr; try discriminate.
    match goal with [ Hd : EVar _ = EVar _ |- _ ] => injection Hd as -> end.
    destruct (nv_env_lookup _ HE _ _ _ H) as [HΓ1 [-> | ->]];
      right; split; [exact HΓ1 | | exact HΓ1 |];
      unfold nv_selfterm, nv_loopterm; nv_disj.
  - nv_cases Hr; discriminate.
  - nv_cases Hr; try discriminate;
      match goal with [ Hd : EApp _ _ = EApp _ _ |- _ ] =>
        injection Hd; clear Hd; intros; subst end;
      (right; split;
       [ apply NVEnv_Ext; [assumption | assumption | nv_disj]
       | unfold nv_selfterm, nv_loopterm; nv_disj ]).
  - nv_cases Hr; try discriminate;
      match goal with [ Hd : EApp _ _ = EApp _ _ |- _ ] => injection Hd as -> -> end;
      nv_spick.
  - nv_cases Hr; try discriminate;
      match goal with [ Hd : EApp _ _ = EApp _ _ |- _ ] => injection Hd as -> -> end.
    + destruct (nv_fun_values Φ n Γ _ H) as [-> | ->]; nv_spick.
    + destruct (nv_varf_values n Φ Γ _ HE H) as [-> | [-> | [Γ1 [HΓ1 ->]]]]; nv_spick.
    + destruct (nv_thunk_values Φ n Γ _ _ H) as [-> | ->]; nv_spick.
    + destruct (nv_thunk_values Φ n Γ _ _ H) as [-> | ->]; nv_spick.
    + destruct (nv_bot_values Φ n Γ BOutOfFuel _ H) as [-> | ->]; nv_spick.
    + destruct (nv_bot_values Φ n Γ BOutOfFuel _ H) as [-> | ->]; nv_spick.
  - nv_cases Hr; simpl in H; injection H as <- <-; simpl in H0;
      repeat (destruct H0 as [<- | H0]); try contradiction;
      first [ nv_opick | nv_spick ].
  - nv_cases Hr; discriminate.
  - nv_cases Hr; try discriminate;
      match goal with [ Hd : EApp _ _ = EApp _ _ |- _ ] => injection Hd as -> -> end;
      simpl in H; discriminate H.
  - nv_cases Hr; try discriminate;
      match goal with [ Hd : EThunk _ _ = EThunk _ _ |- _ ] => injection Hd as -> -> end;
      nv_spick.
  - nv_cases Hr; try discriminate;
      match goal with [ Hd : EIf _ _ _ = EIf _ _ _ |- _ ] =>
        injection Hd as -> -> -> end; nv_opick.
  - nv_cases Hr; try discriminate;
      match goal with [ Hd : EIf _ _ _ = EIf _ _ _ |- _ ] =>
        injection Hd as -> -> -> end; nv_opick.
  - nv_cases Hr; try discriminate;
      match goal with [ Hd : EIf _ _ _ = EIf _ _ _ |- _ ] =>
        injection Hd as -> -> -> end; nv_opick.
  - nv_cases Hr; try discriminate;
      match goal with [ Hd : ECase _ _ = ECase _ _ |- _ ] => injection Hd as -> -> end;
      nv_opick.
  - nv_cases Hr; try discriminate;
      match goal with [ Hd : ECase _ _ = ECase _ _ |- _ ] => injection Hd as -> -> end.
    split; [reflexivity | split; [reflexivity |]].
    exact (nv_merge_scrut _ (nv_guard_values Φ n _ H)).
  - destruct Hr as [-> [-> Hm]].
    destruct Hm as [[[d Hd] | Hd] | [t [f [Hd [Ht Hf]]]]]; try discriminate Hd.
    injection Hd as -> -> ->.
    split; [reflexivity | split; [reflexivity |]].
    left. destruct Ht as [-> | ->]; [left; eexists; reflexivity | right; reflexivity].
  - destruct Hr as [-> [-> Hm]].
    destruct Hm as [[[d Hd] | Hd] | [t [f [Hd [Ht Hf]]]]]; try discriminate Hd.
    injection Hd as -> -> ->.
    split; [reflexivity | split; [reflexivity |]].
    left. destruct Hf as [-> | ->]; [left; eexists; reflexivity | right; reflexivity].
  - destruct Hr as [-> [-> Hm]].
    destruct Hm as [[[d0 ->] | ->] | [t [f [-> [Ht Hf]]]]];
      try (simpl in H; discriminate H).
    unfold decompose_con_app in H. simpl in H. injection H as <- <-.
    unfold nv_alts in H0. simpl in H0.
    destruct (string_dec d0 "T") as [_ | _].
    + injection H0 as <- <-. simpl.
      right. split; [apply NVEnv_Empty |].
      unfold nv_selfterm, nv_loopterm. left. left. reflexivity.
    + destruct (string_dec d0 "F") as [_ | _]; [| discriminate H0].
      injection H0 as <- <-. simpl. nv_opick.
  - destruct Hr as [-> [-> _]]. split; [reflexivity | split; [reflexivity |]].
    left. left. exists d. reflexivity.
  - destruct Hr as [-> [-> _]]. split; [reflexivity | split; [reflexivity |]].
    left. left. eexists. reflexivity.
  - destruct Hr as [-> [-> _]]. split; [reflexivity | split; [reflexivity |]].
    left. left. eexists. reflexivity.
Qed.

Lemma nv_reach_closed : forall Φ st Φ' st', nv_reach st -> sym_reach Φ st Φ' st' -> nv_reach st'.
Proof.
  intros Φ st Φ' st' Hr Hre. induction Hre; [exact Hr |].
  exact (IHHre (nv_reach_step Φ st Φ1 st1 Hr H)).
Qed.

Theorem nv_smt_bounded : smt_bounded_run nv_phi · nv_sym.
Proof.
  exists 8. intros Φ' Γ' e' n v Hre Hev.
  assert (Hr0 : nv_reach (SEval · nv_sym))
    by (simpl; left; split; [reflexivity | unfold nv_outer; tauto]).
  pose proof (nv_reach_closed nv_phi _ Φ' _ Hr0 Hre) as Hr.
  simpl in Hr. destruct Hr as [[-> He] | [HE He]].
  - unfold nv_outer in He.
    destruct He as [-> | [-> | [-> | [-> | [-> | ->]]]]].
    + destruct (nv_case_values Φ' n v Hev) as [Hf | ->];
        [exact (nv_foldval_bound v Hf) | vm_compute; lia].
    + destruct (nv_guard_values Φ' n v Hev) as [-> | [t [f [-> [[-> | ->] [-> | ->]]]]]];
        vm_compute; lia.
    + destruct (nv_varx_values Φ' n v Hev) as [-> | ->]; vm_compute; lia.
    + destruct (nv_con_values Φ' n · "T" v Hev) as [-> | ->]; vm_compute; lia.
    + destruct (nv_con_values Φ' n · "F" v Hev) as [-> | ->]; vm_compute; lia.
    + destruct (nv_lit_values Φ' n · v Hev) as [-> | ->]; vm_compute; lia.
  - exact (nv_selfval_bound Γ' v (nv_selfterm_values n Φ' Γ' e' v HE He Hev)).
Qed.

Lemma nv_sigma_models_phi : nv_sigma ⊨ nv_phi.
Proof. reflexivity. Qed.

Lemma nv_symbolic_program : symbolic_program nv_S · nv_sym.
Proof.
  split; [apply SymScoped_Env_Empty |].
  unfold nv_sym, nv_alts, self_app, self_app_fun, self_app_body.
  apply SymScoped_Case.
  - apply SymScoped_If;
      [apply SymScoped_Var; right; apply only_self
       | apply SymScoped_Con | apply SymScoped_Con].
  - apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
    + apply SymScoped_Alt. simpl.
      apply SymScoped_App; apply SymScoped_Lam; apply SymScoped_App;
        apply SymScoped_Var; left; simpl; left; reflexivity.
    + apply SymScoped_Alt. apply SymScoped_Lit.
Qed.

Lemma nv_guard_false : models_not_cond nv_sigma nv_S (EVar nv_x).
Proof.
  exists (PCVar nv_x). split; [| reflexivity].
  intros Γ Hfree. simpl. rewrite (Hfree nv_x (only_self nv_x)). reflexivity.
Qed.

Lemma nv_contains : contains nv_sigma nv_S nv_sym nv_con.
Proof.
  apply Cont_Case.
  - apply Cont_If_False; [exact nv_guard_false | apply Cont_Con].
  - apply Forall2_cons; [| apply Forall2_cons; [| apply Forall2_nil]].
    + apply Cont_Alt; [apply Forall_nil |].
      unfold self_app, self_app_fun, self_app_body.
      apply Cont_App; (apply Cont_Lam; [reflexivity |]);
        (apply Cont_App; apply Cont_Var_Bound; reflexivity).
    + apply Cont_Alt; [apply Forall_nil | apply Cont_Lit].
Qed.

Lemma nv_con_concore : concore_expr nv_con.
Proof.
  apply Con_Case; [apply Con_Con |].
  apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
  - apply Con_Alt. unfold self_app, self_app_fun, self_app_body.
    apply Con_App; apply Con_Lam; apply Con_App; apply Con_Var.
  - apply Con_Alt. apply Con_Lit.
Qed.

Lemma nv_con_closed : closed_program · nv_con.
Proof.
  split; [apply Scoped_Env_Empty |].
  unfold nv_con, nv_alts, self_app, self_app_fun, self_app_body.
  apply Scoped_Case; [apply Scoped_Con |].
  repeat constructor.
Qed.

Lemma nv_con_evaluates : · ⊢ᶜ nv_con ⇓ᶜ ELit true.
Proof.
  unfold eval_con, nv_con.
  eapply Eval_Case; [eapply Eval_Con; reflexivity |].
  simpl. eapply FoldAlts_Con; [reflexivity | reflexivity | apply Eval_Lit].
Qed.

Lemma nv_budget_total : budget_total nv_phi · nv_sym.
Proof.
  exists 3%nat. intros n Hn. destruct n as [| [| [| m]]]; [lia | lia | lia |].
  destruct (self_app_has_value_at_every_budget (Datatypes.S (Datatypes.S m))
              (nv_phi ∧ PCVar nv_x) ·) as [vt Hvt].
  exists (EIf (EVar nv_x) vt nv_true).
  unfold nv_sym. eapply Eval_Case.
  - eapply Eval_If with (pc_c := PCVar nv_x);
      [apply Eval_SymVar; reflexivity | reflexivity
      | eapply Eval_Con; reflexivity | eapply Eval_Con; reflexivity].
  - simpl. eapply FoldAlts_If; [reflexivity | |].
    + eapply FoldAlts_Con; [reflexivity | reflexivity | exact Hvt].
    + eapply FoldAlts_Con; [reflexivity | reflexivity | apply Eval_Lit].
Qed.

Theorem nv_completeness_instance :
  exists h, forall n, (h <= n)%nat ->
    exists v_sym, eval (Fin n) nv_phi · nv_sym v_sym /\ contains nv_sigma nv_S v_sym nv_true.
Proof.
  exact (concore_completeness_budget nv_phi · · nv_sigma nv_S nv_sym nv_con nv_true
           nv_sigma_models_phi (Cont_Env_Empty _ _) nv_contains nv_con_concore nv_con_closed
           nv_symbolic_program nv_smt_bounded nv_budget_total nv_con_evaluates).
Qed.

Theorem nv_completeness_forall_instance :
  exists h, forall n, (h <= n)%nat ->
    forall v_sym, eval (Fin n) nv_phi · nv_sym v_sym -> contains nv_sigma nv_S v_sym nv_true.
Proof.
  exact (concore_completeness_forall · nv_con nv_true nv_con_evaluates nv_phi · nv_sigma nv_S nv_sym
           nv_sigma_models_phi (Cont_Env_Empty _ _) nv_contains nv_con_concore nv_con_closed
           nv_symbolic_program nv_smt_bounded).
Qed.

Theorem nv_completeness_exists_instance :
  exists k v_sym, eval (Fin k) nv_phi · nv_sym v_sym /\ contains nv_sigma nv_S v_sym nv_true.
Proof.
  exact (concore_completeness_exists nv_phi · · nv_sigma nv_S nv_sym nv_con nv_true
           nv_sigma_models_phi (Cont_Env_Empty _ _) nv_contains nv_con_concore nv_con_closed
           nv_symbolic_program nv_smt_bounded nv_budget_total nv_con_evaluates).
Qed.

Theorem nv_symbolic_run_diverges : forall v, ~ nv_phi ; · ⊢ nv_sym ⇓ v.
Proof.
  intros v Hv.
  pose proof (eq_refl : @sat model_sorts model_solver nv_phi = true) as Hsat.
  destruct (Inversion.eval_case_inv nv_phi · _ _ v Hsat Hv) as [es' [Hes Hfold]].
  destruct (Inversion.eval_if_inv nv_phi · _ _ _ es' Hsat Hes)
    as [ec' [et' [ef' [pc [Hc [Hpc [Ht [Hf ->]]]]]]]].
  apply (eval_var_free_inv nv_phi · nv_x ec' Hsat eq_refl) in Hc. subst ec'.
  simpl in Hpc. injection Hpc as <-.
  apply (Inversion.eval_con_same (nv_phi ∧ PCVar nv_x) · "T" et' (nv_sat _)) in Ht.
  apply (Inversion.eval_con_same (nv_phi ∧ ¬ PCVar nv_x) · "F" ef' (nv_sat _)) in Hf.
  subst et' ef'.
  destruct (fold_alts_if_some_inv Inf nv_phi · (EVar nv_x) (ECon "T") (ECon "F") nv_alts v
              (PCVar nv_x) eq_refl Hfold) as [et' [ef' [_ [Hft _]]]].
  pose proof (Inversion.fold_alts_con_inv Inf (nv_phi ∧ PCVar nv_x) · (ECon "T") nv_alts et' "T" [] [] self_app
                eq_refl eq_refl eq_refl eq_refl Hft) as Hloop.
  exact (self_app_diverges (nv_phi ∧ PCVar nv_x) _ et' (nv_sat _) Hloop).
Qed.

Theorem nv_concrete_value_unique : forall v, · ⊢ᶜ nv_con ⇓ᶜ v -> v = nv_true.
Proof.
  intros v Hv.
  exact (concore_eval_deterministic · nv_con v nv_true CEnv_Empty nv_con_concore
           nv_con_closed Hv nv_con_evaluates).
Qed.

End ElseBranchLoopingThenArm.
