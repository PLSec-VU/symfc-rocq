From SymCoreTheory Require Import SymCore ConCore CostLaws Completeness Model.
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
  destruct (SymCore.eval_case_inv nv_phi · _ _ v Hsat Hv) as [es' [Hes Hfold]].
  destruct (SymCore.eval_if_inv nv_phi · _ _ _ es' Hsat Hes)
    as [ec' [et' [ef' [pc [Hc [Hpc [Ht [Hf ->]]]]]]]].
  apply (eval_var_free_inv nv_phi · nv_x ec' Hsat eq_refl) in Hc. subst ec'.
  simpl in Hpc. injection Hpc as <-.
  apply (SymCore.eval_con_same (nv_phi ∧ PCVar nv_x) · "T" et' (nv_sat _)) in Ht.
  apply (SymCore.eval_con_same (nv_phi ∧ ¬ PCVar nv_x) · "F" ef' (nv_sat _)) in Hf.
  subst et' ef'.
  destruct (fold_alts_if_some_inv Inf nv_phi · (EVar nv_x) (ECon "T") (ECon "F") nv_alts v
              (PCVar nv_x) eq_refl Hfold) as [et' [ef' [_ [Hft _]]]].
  pose proof (SymCore.fold_alts_con_inv Inf (nv_phi ∧ PCVar nv_x) · (ECon "T") nv_alts et' "T" [] [] self_app
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

Section PruningModel.

Fixpoint conjuncts (Φ : @path_condition model_sorts) : list path_condition :=
  match Φ with
  | PCPrim PAnd (a :: b :: nil) => conjuncts a ++ conjuncts b
  | _ => Φ :: nil
  end.

Definition refutes (cs : list (@path_condition model_sorts)) (c : path_condition) : bool :=
  match c with
  | PCVar x =>
      existsb (fun d => match d with
                        | PCPrim PNot (PCVar y :: nil) => String.eqb x y
                        | _ => false
                        end) cs
  | _ => false
  end.

Definition pruning_sat (Φ : @path_condition model_sorts) : bool :=
  negb (existsb (refutes (conjuncts Φ)) (conjuncts Φ)).

#[local] Instance pruning_solver : @SymCoreSolver model_sorts :=
  Build_SymCoreSolver
    pruning_sat (PCLit true) eq_refl model_reduce_prim
    erase_cast keep_coercion keep_type.

Fixpoint conjuncts_hold (σ : valuation) (Φ : path_condition) {struct Φ} :
  σ ⊨ Φ -> Forall (fun c => σ ⊨ c) (conjuncts Φ).
Proof.
  intros H. destruct Φ as [x | l | p args].
  - repeat constructor. exact H.
  - repeat constructor. exact H.
  - destruct p; [| repeat constructor; exact H | repeat constructor; exact H].
    destruct args as [| a [| b [| c rest]]];
      try (repeat constructor; exact H).
    unfold models in H. simpl in H. apply andb_true_iff in H as [Ha Hb].
    simpl. apply Forall_app. split; apply conjuncts_hold; assumption.
Qed.

#[local] Instance pruning_models_sat : @ModelsSat model_sorts pruning_solver.
Proof.
  intros σ Φ H.
  pose proof (conjuncts_hold σ Φ H) as Hall.
  change (negb (existsb (refutes (conjuncts Φ)) (conjuncts Φ)) = true).
  apply negb_true_iff. apply not_true_iff_false. intros Hex.
  apply existsb_exists in Hex as [c [Hc Hr]].
  destruct c as [x | l | p args]; try discriminate Hr.
  apply existsb_exists in Hr as [d [Hd Hxd]].
  destruct d as [| | q dargs]; try discriminate Hxd.
  destruct q; try discriminate Hxd.
  destruct dargs as [| [y | | ] [| ]]; try discriminate Hxd.
  apply String.eqb_eq in Hxd. subst y.
  rewrite Forall_forall in Hall.
  pose proof (Hall _ Hc) as Hx. pose proof (Hall _ Hd) as Hnx.
  unfold models in Hx, Hnx. simpl in Hx, Hnx. rewrite Hx in Hnx. discriminate Hnx.
Qed.

#[local] Instance pruning_cost_laws : @SymFCCostLaws model_sorts pruning_solver.
Proof.
  constructor.
  - constructor.
    + exact model_reduce_prim_solvable.
    + exact model_reduce_prim_saturated.
    + exact model_reduce_prim_concore.
    + exact model_cast_expr_concore.
    + exact model_reduce_prim_scoped.
    + exact model_cast_expr_scoped.
    + exact model_reduce_prim_keeps_out_of_fuel.
    + exact model_cast_expr_keeps_out_of_fuel.
    + exact pruning_models_sat.
    + exact model_prim_value_and.
    + exact model_reduce_prim_contains.
    + exact model_reduce_prim_denote.
    + exact model_reduce_prim_ground_value.
    + exact model_cast_expr_contains.
    + exact model_reduce_prim_ite_wellformed.
    + exact model_subst_coerc_contains_env.
    + exact model_subst_type_contains_env.
  - exact model_cast_expr_contains_k.
  - exact model_reduce_prim_contains_k.
Qed.

Definition pm_x : var := "x".
Definition pm_S : symvars := only pm_x.
Definition pm_sigma : valuation := fun _ => true.
Definition pm_phi : path_condition := PCVar pm_x.
Definition pm_true : expr := @ELit model_sorts true.
Definition pm_sym : expr := necessity_program pm_x true true.

Lemma pm_sigma_models_phi : pm_sigma ⊨ pm_phi.
Proof. reflexivity. Qed.

Lemma pm_else_path_pruned : @sat model_sorts pruning_solver (pm_phi ∧ ¬ PCVar pm_x) = false.
Proof. reflexivity. Qed.

Lemma pm_sym_evaluates :
  @eval model_sorts pruning_solver Inf pm_phi · pm_sym (EIf (EVar pm_x) pm_true (EBot BUnreachable)).
Proof.
  unfold pm_sym, necessity_program.
  eapply Eval_If with (pc_c := PCVar pm_x).
  - apply Eval_SymVar. reflexivity.
  - reflexivity.
  - apply Eval_Lit.
  - apply Eval_Prune. exact pm_else_path_pruned.
Qed.

Definition pm_bot : expr := @EBot model_sorts BOutOfFuel.
Definition pm_unreach : expr := @EBot model_sorts BUnreachable.
Definition pm_stuck : expr := EApp pm_true pm_true.

Definition pm_stop (v : expr) : Prop := v = pm_bot \/ v = pm_unreach.

Definition pm_terms (e : expr) : Prop :=
  e = pm_sym \/ e = @EVar model_sorts pm_x \/ e = pm_true \/ e = pm_stuck \/
  e = EApp pm_bot pm_true \/ e = EApp pm_unreach pm_true \/
  e = pm_bot \/ e = pm_unreach.

Ltac pm_pick :=
  unfold pm_stop, pm_bot, pm_unreach, pm_true, pm_stuck, pm_terms, pm_sym,
    necessity_program, necessity_stuck_arm;
  repeat (first [ left; reflexivity | right ]); reflexivity.

Ltac pm_live_fuel n :=
  match goal with [ Hf : Live ?f = Fin n |- _ ] =>
    destruct f as [| m]; [destruct n; discriminate Hf |] end.

Lemma pm_symbolic_program : symbolic_program pm_S · pm_sym.
Proof.
  split; [apply SymScoped_Env_Empty |].
  unfold pm_sym, necessity_program, necessity_stuck_arm.
  apply SymScoped_If;
    [apply SymScoped_Var; right; apply only_self | apply SymScoped_Lit |].
  apply SymScoped_App; apply SymScoped_Lit.
Qed.

Lemma pm_lit_values : forall Φ n Γ (b : bool) v,
  @eval model_sorts pruning_solver (Fin n) Φ Γ (ELit b) v ->
  v = @ELit model_sorts b \/ pm_stop v.
Proof.
  intros Φ n Γ b v H. inversion H; subst; try (simpl in *; discriminate); pm_pick.
Qed.

Lemma pm_var_values : forall Φ n Γ z v,
  @eval model_sorts pruning_solver (Fin n) Φ Γ (EVar z) v -> lookup_env Γ z = None ->
  v = @EVar model_sorts z \/ pm_stop v.
Proof.
  intros Φ n Γ z v H Hl. inversion H; subst; try (simpl in *; discriminate);
    try congruence; pm_pick.
Qed.

Lemma pm_bot_values : forall Φ n Γ b v,
  @eval model_sorts pruning_solver (Fin n) Φ Γ (@EBot model_sorts b) v ->
  v = @EBot model_sorts b \/ pm_stop v.
Proof.
  intros Φ n Γ b v H. inversion H; subst; try (simpl in *; discriminate); pm_pick.
Qed.

Lemma pm_appbot_values : forall Φ n Γ b u v,
  @eval model_sorts pruning_solver (Fin n) Φ Γ (EApp (@EBot model_sorts b) u) v ->
  v = @EBot model_sorts b \/ pm_stop v.
Proof.
  intros Φ n Γ b u v H. inversion H; subst; try sym_absurd;
    try (simpl in *; discriminate); pm_pick.
Qed.

Lemma pm_stuck_values : forall Φ n Γ v,
  @eval model_sorts pruning_solver (Fin n) Φ Γ pm_stuck v -> pm_stop v.
Proof.
  intros Φ n Γ v H. unfold pm_stuck, pm_true in H.
  inversion H; subst; try sym_absurd; try (simpl in *; discriminate); pm_pick.
Qed.

Lemma pm_sym_values : forall Φ n v,
  @eval model_sorts pruning_solver (Fin n) Φ · pm_sym v ->
  (exists t f, v = EIf (@EVar model_sorts pm_x) t f
     /\ (t = pm_true \/ pm_stop t) /\ pm_stop f) \/ pm_stop v.
Proof.
  intros Φ n v H. unfold pm_sym, necessity_program in H.
  inversion H; subst; try (simpl in *; discriminate); try (right; pm_pick).
  pm_live_fuel n.
  match goal with [ Hc : eval _ _ · (EVar pm_x) ?w |- _ ] =>
    destruct (pm_var_values Φ m · pm_x w Hc eq_refl) as [-> | Hst] end.
  - match goal with [ Hf : eval _ _ · (necessity_stuck_arm true) ?w |- _ ] =>
      pose proof (pm_stuck_values _ m · w Hf) as Hstf end.
    match goal with [ Ht : eval _ _ · (ELit true) ?t |- _ ] =>
      destruct (pm_lit_values _ m · true t Ht) as [-> | Hstt] end.
    + left. eexists; eexists.
      split; [reflexivity | split; [left; reflexivity | exact Hstf]].
    + left. eexists; eexists.
      split; [reflexivity | split; [right; exact Hstt | exact Hstf]].
  - exfalso. destruct Hst as [-> | ->];
      match goal with [ Hpc : expr_to_pc · _ = Some _ |- _ ] =>
        unfold pm_bot, pm_unreach in Hpc; simpl in Hpc; discriminate Hpc end.
Qed.

Lemma pm_merge_bound : forall t f,
  (t = pm_true \/ pm_stop t) -> pm_stop f ->
  smt_size (@merge model_sorts pruning_solver · (EIf (@EVar model_sorts pm_x) t f)) <= 8.
Proof.
  intros t f [-> | [-> | ->]] [-> | ->]; vm_compute; lia.
Qed.

Definition pm_reach (st : sym_state) : Prop :=
  match st with
  | SEval Γ e => Γ = · /\ pm_terms e
  | SFold _ _ _ => False
  end.

Ltac pm_cases H :=
  destruct H as [-> He];
  cbv beta delta [pm_terms] in He;
  repeat match goal with [ Hx : _ \/ _ |- _ ] => destruct Hx end;
  subst;
  unfold pm_sym, necessity_program, necessity_stuck_arm, pm_stuck, pm_true,
    pm_bot, pm_unreach in *.

Ltac pm_split := split; [reflexivity | pm_pick].

Lemma pm_reach_step : forall Φ st Φ' st',
  pm_reach st -> @sym_step model_sorts pruning_solver Φ st Φ' st' -> pm_reach st'.
Proof.
  intros Φ st Φ' st' Hr Hstep.
  destruct Hstep; simpl in Hr |- *; try contradiction.
  - pm_cases Hr; discriminate.
  - pm_cases Hr; discriminate.
  - pm_cases Hr; discriminate.
  - pm_cases Hr; try discriminate;
      match goal with [ Hd : EApp _ _ = EApp _ _ |- _ ] => injection Hd as -> -> end;
      pm_split.
  - pm_cases Hr; try discriminate;
      match goal with [ Hd : EApp _ _ = EApp _ _ |- _ ] => injection Hd as -> -> end;
      [ destruct (pm_lit_values Φ n · true _ H) as [-> | [-> | ->]]
      | destruct (pm_bot_values Φ n · BOutOfFuel _ H) as [-> | [-> | ->]]
      | destruct (pm_bot_values Φ n · BUnreachable _ H) as [-> | [-> | ->]] ];
      pm_split.
  - pm_cases Hr; simpl in H; injection H as <- <-; simpl in H0;
      repeat (destruct H0 as [<- | H0]); try contradiction; pm_split.
  - pm_cases Hr; discriminate.
  - pm_cases Hr; try discriminate;
      match goal with [ Hd : EApp _ _ = EApp _ _ |- _ ] => injection Hd as -> -> end;
      simpl in H; discriminate H.
  - pm_cases Hr; discriminate.
  - pm_cases Hr; try discriminate;
      match goal with [ Hd : EIf _ _ _ = EIf _ _ _ |- _ ] =>
        injection Hd as -> -> -> end; pm_split.
  - pm_cases Hr; try discriminate;
      match goal with [ Hd : EIf _ _ _ = EIf _ _ _ |- _ ] =>
        injection Hd as -> -> -> end; pm_split.
  - pm_cases Hr; try discriminate;
      match goal with [ Hd : EIf _ _ _ = EIf _ _ _ |- _ ] =>
        injection Hd as -> -> -> end; pm_split.
  - pm_cases Hr; discriminate.
  - pm_cases Hr; discriminate.
Qed.

Lemma pm_reach_closed : forall Φ st Φ' st',
  pm_reach st -> @sym_reach model_sorts pruning_solver Φ st Φ' st' -> pm_reach st'.
Proof.
  intros Φ st Φ' st' Hr Hre. induction Hre; [exact Hr |].
  exact (IHHre (pm_reach_step Φ st Φ1 st1 Hr H)).
Qed.

Theorem pm_smt_bounded : @smt_bounded_run model_sorts pruning_solver pm_phi · pm_sym.
Proof.
  exists 8. intros Φ' Γ' e' n v Hre Hev.
  assert (Hr0 : pm_reach (SEval · pm_sym))
    by (simpl; split; [reflexivity | unfold pm_terms; tauto]).
  pose proof (pm_reach_closed pm_phi _ Φ' _ Hr0 Hre) as Hr.
  simpl in Hr. destruct Hr as [-> He]. unfold pm_terms in He.
  destruct He as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]].
  - destruct (pm_sym_values Φ' n v Hev) as [[t [f [-> [Ht Hf]]]] | [-> | ->]];
      [exact (pm_merge_bound t f Ht Hf) | vm_compute; lia | vm_compute; lia].
  - destruct (pm_var_values Φ' n · pm_x v Hev eq_refl) as [-> | [-> | ->]];
      vm_compute; lia.
  - destruct (pm_lit_values Φ' n · true v Hev) as [-> | [-> | ->]]; vm_compute; lia.
  - destruct (pm_stuck_values Φ' n · v Hev) as [-> | ->]; vm_compute; lia.
  - destruct (pm_appbot_values Φ' n · BOutOfFuel _ v Hev) as [-> | [-> | ->]];
      vm_compute; lia.
  - destruct (pm_appbot_values Φ' n · BUnreachable _ v Hev) as [-> | [-> | ->]];
      vm_compute; lia.
  - destruct (pm_bot_values Φ' n · BOutOfFuel v Hev) as [-> | [-> | ->]]; vm_compute; lia.
  - destruct (pm_bot_values Φ' n · BUnreachable v Hev) as [-> | [-> | ->]]; vm_compute; lia.
Qed.

Lemma pm_contains : contains pm_sigma pm_S pm_sym pm_true.
Proof.
  apply Cont_If_True; [| apply Cont_Lit].
  exists (PCVar pm_x). split; [| reflexivity].
  intros Γ Hfree. simpl. rewrite (Hfree pm_x (only_self pm_x)). reflexivity.
Qed.

Lemma pm_true_closed : closed_program · pm_true.
Proof. split; [apply Scoped_Env_Empty | apply Scoped_Lit]. Qed.

Lemma pm_con_evaluates : @eval_con model_sorts pruning_solver · pm_true pm_true.
Proof. apply Eval_Lit. Qed.

Theorem pm_soundness_instance :
  exists v_con, @eval_con model_sorts pruning_solver · pm_true v_con /\
    contains pm_sigma pm_S (EIf (EVar pm_x) pm_true (EBot BUnreachable)) v_con.
Proof.
  exact (concore_soundness pm_phi · · pm_sigma pm_S pm_sym pm_true _
           pm_sigma_models_phi (Cont_Env_Empty _ _) pm_contains (Con_Lit _) pm_true_closed
           pm_symbolic_program pm_sym_evaluates).
Qed.

Theorem pm_completeness_instance :
  exists h, forall n, (h <= n)%nat ->
    exists v_sym, @eval model_sorts pruning_solver (Fin n) pm_phi · pm_sym v_sym
      /\ contains pm_sigma pm_S v_sym pm_true.
Proof.
  exact (concore_completeness_budget pm_phi · · pm_sigma pm_S pm_sym pm_true pm_true
           pm_sigma_models_phi (Cont_Env_Empty _ _) pm_contains (Con_Lit _) pm_true_closed
           pm_symbolic_program pm_smt_bounded
           (budget_total_of_terminating _ _ _ (ex_intro _ _ pm_sym_evaluates))
           pm_con_evaluates).
Qed.

Theorem pm_plain_model_not_budget_total :
  ~ @budget_total model_sorts model_solver pm_phi · pm_sym.
Proof.
  exact (@budget_total_fails_on_stuck_arm model_sorts model_solver pm_phi pm_x true true
           eq_refl eq_refl).
Qed.

Theorem pm_symbolic_evaluation_not_deterministic :
  @eval model_sorts pruning_solver Inf pm_phi · (EIf (EVar pm_x) pm_true pm_true)
    (EIf (EVar pm_x) pm_true pm_true)
  /\ @eval model_sorts pruning_solver Inf pm_phi · (EIf (EVar pm_x) pm_true pm_true)
    (EIf (EVar pm_x) pm_true (EBot BUnreachable)).
Proof.
  split; eapply Eval_If with (pc_c := PCVar pm_x);
    try (apply Eval_SymVar; reflexivity); try reflexivity; try apply Eval_Lit.
  apply Eval_Prune. exact pm_else_path_pruned.
Qed.

End PruningModel.

Section RuntimeBranch.


Definition rb_x : var := "x".
Definition rb_y : var := "y".
Definition rb_a : var := "a".

Definition rb_S : symvars := fun z => orb (String.eqb z rb_x) (String.eqb z rb_y).
Definition rb_sigma : valuation := fun z => if String.string_dec z rb_x then true else false.
Definition rb_phi : path_condition := @PCLit model_sorts true.

Definition rb_and (u w : expr) : expr := EApp (EApp (@EPrimOp model_sorts PAnd) u) w.

Definition rb_alts : list alt :=
  Alt dcon_true [] (@ELit model_sorts true) ::
  Alt dcon_false [] (@ELit model_sorts false) :: nil.

Definition rb_body : expr := ECase (rb_and (EVar rb_a) (EVar rb_y)) rb_alts.
Definition rb_lam : expr := ELam rb_a rb_body.
Definition rb_sym : expr := EApp rb_lam (EVar rb_x).

Definition rb_con_body : expr := ECase (rb_and (EVar rb_a) (@ELit model_sorts false)) rb_alts.
Definition rb_con : expr := EApp (ELam rb_a rb_con_body) (@ELit model_sorts true).

Definition rb_env : environment := extend_env · rb_a · (EVar rb_x).
Definition rb_guard : expr := rb_and (EVar rb_x) (EVar rb_y).
Definition rb_value : expr :=
  EIf rb_guard (@ELit model_sorts true) (@ELit model_sorts false).

Lemma rb_sigma_models_phi : rb_sigma ⊨ rb_phi.
Proof. reflexivity. Qed.

Lemma rb_symbolic_program : symbolic_program rb_S · rb_sym.
Proof.
  split; [apply SymScoped_Env_Empty |].
  unfold rb_sym, rb_lam, rb_body, rb_and, rb_alts.
  apply SymScoped_App; [| apply SymScoped_Var; right; reflexivity].
  apply SymScoped_Lam. apply SymScoped_Case.
  - apply SymScoped_App; [apply SymScoped_App |].
    + apply SymScoped_PrimOp.
    + apply SymScoped_Var. left. simpl. left. reflexivity.
    + apply SymScoped_Var. right. reflexivity.
  - repeat constructor.
Qed.

Lemma rb_contains : contains rb_sigma rb_S rb_sym rb_con.
Proof.
  unfold rb_sym, rb_con, rb_lam, rb_body, rb_con_body, rb_and.
  apply Cont_App.
  - apply Cont_Lam; [reflexivity |].
    apply Cont_Case.
    + apply Cont_App; [apply Cont_App |].
      * apply Cont_PrimOp.
      * apply Cont_Var_Bound. reflexivity.
      * apply Cont_Var_Sym. reflexivity.
    + apply Forall2_cons; [| apply Forall2_cons; [| apply Forall2_nil]];
        apply Cont_Alt; [apply Forall_nil | apply Cont_Lit | apply Forall_nil | apply Cont_Lit].
  - apply Cont_Var_Sym. reflexivity.
Qed.

Lemma rb_con_concore : concore_expr rb_con.
Proof.
  unfold rb_con, rb_con_body, rb_and, rb_alts.
  apply Con_App; [apply Con_Lam | apply Con_Lit].
  apply Con_Case; [repeat constructor |].
  repeat constructor.
Qed.

Lemma rb_con_closed : closed_program · rb_con.
Proof.
  split; [apply Scoped_Env_Empty |].
  unfold rb_con, rb_con_body, rb_and, rb_alts.
  repeat constructor.
Qed.

Lemma rb_con_evaluates : · ⊢ᶜ rb_con ⇓ᶜ @ELit model_sorts false.
Proof.
  unfold eval_con, rb_con, rb_con_body, rb_and, rb_alts.
  eapply Eval_AppSpine; [apply Comp_Lam | apply Eval_Lam |].
  simpl. eapply Eval_AppAbs. simpl.
  eapply Eval_Case.
  - eapply Eval_AppPrim with (p := PAnd); [reflexivity | reflexivity |].
    apply Forall2_cons; [| apply Forall2_cons; [| apply Forall2_nil]].
    + eapply Eval_Var; [reflexivity |]. simpl. apply Eval_Lit.
    + apply Eval_Lit.
  - simpl. eapply FoldAlts_GroundFormula; [reflexivity | reflexivity |].
    eapply FoldAlts_Con; [reflexivity | reflexivity |]. simpl. apply Eval_Lit.
Qed.

Lemma rb_sym_evaluates : rb_phi ; · ⊢ rb_sym ⇓ rb_value.
Proof.
  unfold rb_sym, rb_lam, rb_body, rb_and, rb_alts, rb_value, rb_guard.
  eapply Eval_AppSpine; [apply Comp_Lam | apply Eval_Lam |].
  simpl. eapply Eval_AppAbs. simpl.
  eapply Eval_Case.
  - eapply Eval_AppPrim with (p := PAnd); [reflexivity | reflexivity |].
    apply Forall2_cons; [| apply Forall2_cons; [| apply Forall2_nil]].
    + eapply Eval_Var; [reflexivity |]. simpl. apply Eval_SymVar. reflexivity.
    + apply Eval_SymVar. reflexivity.
  - simpl.
    eapply FoldAlts_SymbolicFormula; [reflexivity | reflexivity | reflexivity | |];
      (eapply FoldAlts_Con; [reflexivity | reflexivity |]); simpl; apply Eval_Lit.
Qed.

Lemma rb_guard_false : models_not_cond rb_sigma rb_S rb_guard.
Proof.
  exists (@PCPrim model_sorts PAnd (PCVar rb_x :: PCVar rb_y :: nil)).
  split; [| vm_compute; reflexivity].
  intros Γ Hfree. unfold rb_guard, rb_and. simpl.
  rewrite (Hfree rb_x eq_refl), (Hfree rb_y eq_refl). reflexivity.
Qed.

Lemma rb_value_contains : contains rb_sigma rb_S rb_value (@ELit model_sorts false).
Proof.
  unfold rb_value. apply Cont_If_False; [exact rb_guard_false | apply Cont_Lit].
Qed.

Definition rb_bot : expr := @EBot model_sorts BOutOfFuel.
Definition rb_clos : expr := EThunk · rb_lam.
Definition rb_open_guard : expr := rb_and (EVar rb_a) (EVar rb_y).

Lemma rb_sat : forall Φ, @sat model_sorts model_solver Φ = true.
Proof. reflexivity. Qed.

Ltac rb_kill_prune :=
  match goal with [ H : sat _ = false |- _ ] => rewrite rb_sat in H; discriminate H end.

Ltac rb_live_fuel n :=
  match goal with [ Hf : Live ?f = Fin n |- _ ] =>
    destruct f as [| m]; [destruct n; discriminate Hf |] end.

Definition rb_small (e : expr) : Prop :=
  e = @ELit model_sorts true \/ e = @ELit model_sorts false \/
  e = rb_bot \/ e = @EBot model_sorts BUndefined.

Definition rb_andval (v : expr) : Prop :=
  v = rb_and (EVar rb_x) (EVar rb_y) \/ v = rb_and (EVar rb_x) rb_bot \/
  v = rb_and rb_bot (EVar rb_y) \/ v = rb_and rb_bot rb_bot \/ v = rb_bot.

Lemma rb_free_var_values : forall Φ n Γ z v,
  eval (Fin n) Φ Γ (EVar z) v -> lookup_env Γ z = None ->
  v = @EVar model_sorts z \/ v = rb_bot.
Proof.
  intros Φ n Γ z v H Hl. inversion H; subst; try rb_kill_prune;
    try (simpl in *; discriminate); [congruence | left; reflexivity | right; reflexivity].
Qed.

Lemma rb_lookup_a : lookup_env rb_env rb_a = Some (·, @EVar model_sorts rb_x).
Proof. reflexivity. Qed.

Lemma rb_vara_values : forall Φ n v,
  eval (Fin n) Φ rb_env (EVar rb_a) v -> v = @EVar model_sorts rb_x \/ v = rb_bot.
Proof.
  intros Φ n v H. inversion H; subst; try rb_kill_prune;
    try (simpl in *; discriminate); [| right; reflexivity].
  rb_live_fuel n. change (dec (Remaining m)) with (Fin m) in *.
  match goal with [ Hl : lookup_env rb_env rb_a = Some _ |- _ ] =>
    rewrite rb_lookup_a in Hl; injection Hl as <- <- end.
  match goal with [ Hv : eval _ _ · (EVar rb_x) v |- _ ] =>
    exact (rb_free_var_values _ _ _ _ _ Hv eq_refl) end.
Qed.

Lemma rb_lit_values : forall Φ n Γ (b : bool) v,
  eval (Fin n) Φ Γ (ELit b) v -> v = @ELit model_sorts b \/ v = rb_bot.
Proof.
  intros Φ n Γ b v H. inversion H; subst; try rb_kill_prune;
    try (simpl in *; discriminate); [left; reflexivity | right; reflexivity].
Qed.

Lemma rb_prim_values : forall Φ n Γ v,
  eval (Fin n) Φ Γ (@EPrimOp model_sorts PAnd) v -> v = rb_bot.
Proof.
  intros Φ n Γ v H. inversion H; subst; try rb_kill_prune;
    try (simpl in *; discriminate). reflexivity.
Qed.

Lemma rb_bot_values : forall Φ n Γ b v,
  eval (Fin n) Φ Γ (@EBot model_sorts b) v -> v = @EBot model_sorts b \/ v = rb_bot.
Proof.
  intros Φ n Γ b v H. inversion H; subst; try rb_kill_prune;
    try (simpl in *; discriminate); [left; reflexivity | right; reflexivity].
Qed.

Lemma rb_appbot_values : forall Φ n Γ u v,
  eval (Fin n) Φ Γ (EApp rb_bot u) v -> v = rb_bot.
Proof.
  intros Φ n Γ u v H. inversion H; subst; try rb_kill_prune; try sym_absurd;
    try (simpl in *; discriminate); reflexivity.
Qed.

Lemma rb_and1_values : forall Φ n Γ u v,
  eval (Fin n) Φ Γ (EApp (@EPrimOp model_sorts PAnd) u) v -> v = rb_bot.
Proof.
  intros Φ n Γ u v H. inversion H; subst; try rb_kill_prune; try sym_absurd;
    try (simpl in *; discriminate); try reflexivity.
  match goal with [ Hu : unspool_app _ _ = (EPrimOp _, _) |- _ ] =>
    simpl in Hu; injection Hu as <- <- end.
  match goal with [ Hl : Datatypes.length _ = primop_arity _ |- _ ] =>
    simpl in Hl; discriminate Hl end.
Qed.

Lemma rb_lam_values : forall Φ n Γ v,
  eval (Fin n) Φ Γ rb_lam v -> v = EThunk Γ rb_lam \/ v = rb_bot.
Proof.
  intros Φ n Γ v H. unfold rb_lam in H. inversion H; subst; try rb_kill_prune;
    try (simpl in *; discriminate); [left; reflexivity | right; reflexivity].
Qed.

Lemma rb_guard_values : forall Φ n v,
  eval (Fin n) Φ rb_env rb_open_guard v -> rb_andval v.
Proof.
  intros Φ n v H. unfold rb_open_guard, rb_and in H.
  inversion H; subst; try rb_kill_prune; try sym_absurd;
    try (simpl in *; discriminate); [| right; right; right; right; reflexivity].
  rb_live_fuel n.
  match goal with [ Hu : unspool_app _ _ = (EPrimOp _, _) |- _ ] =>
    simpl in Hu; injection Hu as <- <- end.
  match goal with [ HF : Forall2 _ _ _ |- _ ] =>
    inversion HF as [| a1 b1 l1 l2 Hev1 HF1]; subst;
    inversion HF1 as [| a2 b2 l3 l4 Hev2 HF2]; subst; inversion HF2; subst end.
  destruct (rb_vara_values Φ m b1 Hev1) as [-> | ->];
    destruct (rb_free_var_values Φ m rb_env rb_y b2 Hev2 eq_refl) as [-> | ->];
    unfold rb_andval, rb_and, rb_bot; vm_compute; tauto.
Qed.

Lemma rb_fold_stuck : forall Φ n m v,
  expr_to_pc rb_env m = None -> is_op_app m = true ->
  fold_alts (Fin n) Φ rb_env m rb_alts v -> False.
Proof.
  intros Φ n m v Hpc Hop Hf. inversion Hf; subst; simpl in Hop; try discriminate Hop;
    try congruence.
  match goal with [ Hd : decompose_con_app m = Some (?d, ?ea) |- _ ] =>
    pose proof (unspool_is_con_app m [] d ea (decompose_con_app_unspool m d ea Hd)) as Hc end.
  rewrite (op_app_not_con_app m Hop) in Hc. discriminate Hc.
Qed.

Lemma rb_fold_con_values : forall Φ n d v,
  fold_alts (Fin n) Φ rb_env (ECon d) rb_alts v -> rb_small v.
Proof.
  intros Φ n d v H. inversion H; subst; try (simpl in *; discriminate).
  - unfold decompose_con_app in H0. simpl in H0. injection H0 as <- <-.
    unfold rb_alts in H1. simpl in H1.
    destruct (string_dec d "True") as [_ | _];
      [ injection H1 as <- <-
      | destruct (string_dec d "False") as [_ | _];
        [ injection H1 as <- <- | discriminate H1 ] ];
      simpl in H2;
      match goal with [ Hv : eval _ _ _ (ELit ?b) v |- _ ] =>
        destruct (rb_lit_values _ _ _ b v Hv) as [-> | ->] end;
      unfold rb_small; tauto.
  - right; right; right; reflexivity.
Qed.

Lemma rb_fold_guard_values : forall Φ n m v,
  rb_andval m -> fold_alts (Fin n) Φ rb_env m rb_alts v ->
  (exists r1 r2, v = EIf rb_guard r1 r2 /\ rb_small r1 /\ rb_small r2) \/ v = rb_bot.
Proof.
  intros Φ n m v [-> | [-> | [-> | [-> | ->]]]] Hf.
  - destruct (fold_alts_symbolic_formula_inv (Fin n) Φ rb_env rb_guard
                (@PCPrim model_sorts PAnd (@PCVar model_sorts rb_x :: @PCVar model_sorts rb_y :: nil))
                rb_alts v
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) Hf) as [r1 [r2 [-> [H1 H2]]]].
    left. exists r1, r2. split; [reflexivity | split].
    + exact (rb_fold_con_values _ _ _ r1 H1).
    + exact (rb_fold_con_values _ _ _ r2 H2).
  - exfalso. exact (rb_fold_stuck Φ n (rb_and (EVar rb_x) rb_bot) v
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hf).
  - exfalso. exact (rb_fold_stuck Φ n (rb_and rb_bot (EVar rb_y)) v
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hf).
  - exfalso. exact (rb_fold_stuck Φ n (rb_and rb_bot rb_bot) v
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hf).
  - right. exact (fold_alts_bot_same (Fin n) Φ rb_env BOutOfFuel rb_alts v Hf).
Qed.

Lemma rb_andval_merge : forall m, rb_andval m -> merge rb_env m = m.
Proof. intros m [-> | [-> | [-> | [-> | ->]]]]; reflexivity. Qed.

Lemma rb_andval_size : forall Γ m, rb_andval m -> smt_size (merge Γ m) <= 16.
Proof. intros Γ m [-> | [-> | [-> | [-> | ->]]]]; vm_compute; lia. Qed.

Lemma rb_merge_if_bound : forall Γ r1 r2, rb_small r1 -> rb_small r2 ->
  smt_size (merge Γ (EIf rb_guard r1 r2)) <= 16.
Proof.
  intros Γ r1 r2 [-> | [-> | [-> | ->]]] [-> | [-> | [-> | ->]]]; vm_compute; lia.
Qed.

Lemma rb_body_values : forall Φ n v,
  eval (Fin n) Φ rb_env rb_body v ->
  (exists r1 r2, v = EIf rb_guard r1 r2 /\ rb_small r1 /\ rb_small r2) \/ v = rb_bot.
Proof.
  intros Φ n v H. unfold rb_body in H.
  inversion H; subst; try rb_kill_prune; try (simpl in *; discriminate);
    [| right; reflexivity].
  rb_live_fuel n.
  match goal with [ Hv : eval _ Φ rb_env (rb_and (EVar rb_a) (EVar rb_y)) _ |- _ ] =>
    rename Hv into Hev0 end.
  match goal with [ Hf : fold_alts _ Φ rb_env _ rb_alts v |- _ ] => rename Hf into Hfo0 end.
  pose proof (rb_guard_values Φ m _ Hev0) as Hav.
  rewrite (rb_andval_merge _ Hav) in Hfo0.
  exact (rb_fold_guard_values Φ m _ v Hav Hfo0).
Qed.

Lemma rb_appclos_values : forall Φ n v,
  eval (Fin n) Φ · (EApp rb_clos (EVar rb_x)) v ->
  (exists r1 r2, v = EIf rb_guard r1 r2 /\ rb_small r1 /\ rb_small r2) \/ v = rb_bot.
Proof.
  intros Φ n v H. unfold rb_clos, rb_lam in H.
  inversion H; subst; try rb_kill_prune; try sym_absurd;
    try (simpl in *; discriminate); [| right; reflexivity].
  rb_live_fuel n.
  match goal with [ Hv : eval _ Φ _ rb_body v |- _ ] => exact (rb_body_values Φ m v Hv) end.
Qed.

Lemma rb_clos_values : forall Φ n Γ v,
  eval (Fin n) Φ Γ rb_clos v -> v = rb_clos \/ v = rb_bot.
Proof.
  intros Φ n Γ v H. unfold rb_clos in H.
  inversion H; subst; try rb_kill_prune; try (simpl in *; discriminate);
    [| right; reflexivity].
  rb_live_fuel n.
  match goal with [ Hv : eval _ Φ _ rb_lam v |- _ ] =>
    exact (rb_lam_values Φ m · v Hv) end.
Qed.

Lemma rb_sym_values : forall Φ n v,
  eval (Fin n) Φ · rb_sym v ->
  (exists r1 r2, v = EIf rb_guard r1 r2 /\ rb_small r1 /\ rb_small r2) \/ v = rb_bot.
Proof.
  intros Φ n v H. unfold rb_sym in H.
  inversion H; subst; try rb_kill_prune; try sym_absurd;
    try (simpl in *; discriminate); [| right; reflexivity].
  rb_live_fuel n.
  match goal with [ Hf : eval _ Φ · rb_lam ?w |- _ ] =>
    destruct (rb_lam_values Φ m · w Hf) as [-> | ->] end.
  - match goal with [ Hv : eval _ Φ _ (EApp (EThunk _ rb_lam) (EVar rb_x)) v |- _ ] =>
      exact (rb_appclos_values Φ m v Hv) end.
  - match goal with [ Hv : eval _ Φ · (EApp rb_bot (EVar rb_x)) v |- _ ] =>
      right; exact (rb_appbot_values Φ m · _ v Hv) end.
Qed.

Definition rb_outer (e : expr) : Prop :=
  e = rb_sym \/ e = rb_lam \/ e = @EVar model_sorts rb_x \/
  e = EApp rb_clos (EVar rb_x) \/ e = EApp rb_bot (EVar rb_x) \/
  e = rb_clos \/ e = rb_bot.

Definition rb_inner (e : expr) : Prop :=
  e = rb_body \/ e = rb_open_guard \/ e = EApp (@EPrimOp model_sorts PAnd) (EVar rb_a) \/
  e = @EPrimOp model_sorts PAnd \/ e = @EVar model_sorts rb_a \/
  e = @EVar model_sorts rb_y \/ e = EApp rb_bot (EVar rb_y) \/
  e = EApp rb_bot (EVar rb_a) \/ e = rb_bot \/
  e = @ELit model_sorts true \/ e = @ELit model_sorts false.

Definition rb_reach (st : sym_state) : Prop :=
  match st with
  | SEval Γ e => (Γ = · /\ rb_outer e) \/ (Γ = rb_env /\ rb_inner e)
  | SFold Γ m alts =>
      Γ = rb_env /\ alts = rb_alts /\ (rb_andval m \/ exists d, m = @ECon model_sorts d)
  end.

Ltac rb_pick :=
  unfold rb_outer, rb_inner, rb_sym, rb_clos, rb_lam, rb_body, rb_open_guard,
    rb_and, rb_bot;
  repeat (first [ left; reflexivity | right ]); reflexivity.

Ltac rb_left := left; split; [reflexivity | rb_pick].
Ltac rb_right := right; split; [reflexivity | rb_pick].

Ltac rb_cases H :=
  destruct H as [[-> He] | [-> He]];
  cbv beta delta [rb_outer rb_inner] in He;
  repeat match goal with [ Hx : _ \/ _ |- _ ] => destruct Hx end;
  subst;
  unfold rb_sym, rb_clos, rb_lam, rb_body, rb_open_guard, rb_and, rb_bot in *.

Ltac rb_app2 :=
  match goal with [ Hd : EApp _ _ = EApp _ _ |- _ ] => injection Hd as -> -> end.

Lemma rb_reach_step : forall Φ st Φ' st', rb_reach st -> sym_step Φ st Φ' st' -> rb_reach st'.
Proof.
  intros Φ st Φ' st' Hr Hstep.
  destruct Hstep; simpl in Hr |- *.
  - rb_cases Hr; try discriminate;
      match goal with [ Hd : EVar _ = EVar _ |- _ ] => injection Hd as -> end;
      try (vm_compute in H; discriminate H).
    rewrite rb_lookup_a in H. injection H as <- <-. rb_left.
  - rb_cases Hr; discriminate.
  - rb_cases Hr; try discriminate;
      match goal with [ Hd : EApp _ _ = EApp _ _ |- _ ] =>
        injection Hd; clear Hd; intros; subst end;
      rb_right.
  - rb_cases Hr; try discriminate; rb_app2; first [ rb_left | rb_right ].
  - rb_cases Hr; try discriminate; rb_app2;
      [ destruct (rb_lam_values Φ n · _ H) as [-> | ->]
      | destruct (rb_clos_values Φ n · _ H) as [-> | ->]
      | destruct (rb_bot_values Φ n · BOutOfFuel _ H) as [-> | ->]
      | rewrite (rb_and1_values Φ n rb_env _ _ H)
      | rewrite (rb_prim_values Φ n rb_env _ H)
      | destruct (rb_bot_values Φ n rb_env BOutOfFuel _ H) as [-> | ->]
      | destruct (rb_bot_values Φ n rb_env BOutOfFuel _ H) as [-> | ->] ];
      first [ rb_left | rb_right ].
  - rb_cases Hr; simpl in H; injection H as <- <-; simpl in H0;
      repeat (destruct H0 as [<- | H0]); try contradiction;
      first [ rb_left | rb_right ].
  - rb_cases Hr; discriminate.
  - rb_cases Hr; try discriminate; rb_app2; simpl in H; discriminate H.
  - rb_cases Hr; try discriminate;
      match goal with [ Hd : EThunk _ _ = EThunk _ _ |- _ ] => injection Hd as -> -> end;
      rb_left.
  - rb_cases Hr; discriminate.
  - rb_cases Hr; discriminate.
  - rb_cases Hr; discriminate.
  - rb_cases Hr; try discriminate;
      match goal with [ Hd : ECase _ _ = ECase _ _ |- _ ] => injection Hd as -> -> end;
      rb_right.
  - rb_cases Hr; try discriminate;
      match goal with [ Hd : ECase _ _ = ECase _ _ |- _ ] => injection Hd as -> -> end.
    pose proof (rb_guard_values Φ n _ H) as Hav.
    split; [reflexivity | split; [reflexivity |]].
    left. rewrite (rb_andval_merge _ Hav). exact Hav.
  - destruct Hr as [-> [Ha [Hm | [d0 Hm]]]];
      [ destruct Hm as [Hd | [Hd | [Hd | [Hd | Hd]]]] | rename Hm into Hd ];
      unfold rb_and, rb_bot in Hd; discriminate Hd.
  - destruct Hr as [-> [Ha [Hm | [d0 Hm]]]];
      [ destruct Hm as [Hd | [Hd | [Hd | [Hd | Hd]]]] | rename Hm into Hd ];
      unfold rb_and, rb_bot in Hd; discriminate Hd.
  - destruct Hr as [-> [-> [Hm | [d0 ->]]]].
    + exfalso. destruct Hm as [-> | [-> | [-> | [-> | ->]]]];
        unfold decompose_con_app, rb_and, rb_bot in H; simpl in H; discriminate H.
    + unfold decompose_con_app in H. simpl in H. injection H as <- <-.
      unfold rb_alts in H0. simpl in H0.
      destruct (string_dec d0 "True") as [_ | _];
        [ injection H0 as <- <-
        | destruct (string_dec d0 "False") as [_ | _];
          [ injection H0 as <- <- | discriminate H0 ] ];
        simpl; rb_right.
  - destruct Hr as [-> [-> _]]. split; [reflexivity | split; [reflexivity |]].
    right. exists d. reflexivity.
  - destruct Hr as [-> [-> _]]. split; [reflexivity | split; [reflexivity |]].
    right. exists dcon_true. reflexivity.
  - destruct Hr as [-> [-> _]]. split; [reflexivity | split; [reflexivity |]].
    right. exists dcon_false. reflexivity.
Qed.

Lemma rb_reach_closed : forall Φ st Φ' st', rb_reach st -> sym_reach Φ st Φ' st' -> rb_reach st'.
Proof.
  intros Φ st Φ' st' Hr Hre. induction Hre; [exact Hr |].
  exact (IHHre (rb_reach_step Φ st Φ1 st1 Hr H)).
Qed.

Theorem rb_smt_bounded : smt_bounded_run rb_phi · rb_sym.
Proof.
  exists 16. intros Φ' Γ' e' n v Hre Hev.
  assert (Hr0 : rb_reach (SEval · rb_sym))
    by (simpl; left; split; [reflexivity | unfold rb_outer; tauto]).
  pose proof (rb_reach_closed rb_phi _ Φ' _ Hr0 Hre) as Hr.
  simpl in Hr. destruct Hr as [[-> He] | [-> He]].
  - unfold rb_outer in He.
    destruct He as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]].
    + destruct (rb_sym_values Φ' n v Hev) as [[r1 [r2 [-> [H1 H2]]]] | ->];
        [exact (rb_merge_if_bound · r1 r2 H1 H2) | vm_compute; lia].
    + destruct (rb_lam_values Φ' n · v Hev) as [-> | ->]; vm_compute; lia.
    + destruct (rb_free_var_values Φ' n · rb_x v Hev eq_refl) as [-> | ->]; vm_compute; lia.
    + destruct (rb_appclos_values Φ' n v Hev) as [[r1 [r2 [-> [H1 H2]]]] | ->];
        [exact (rb_merge_if_bound · r1 r2 H1 H2) | vm_compute; lia].
    + rewrite (rb_appbot_values Φ' n · _ v Hev). vm_compute. lia.
    + destruct (rb_clos_values Φ' n · v Hev) as [-> | ->]; vm_compute; lia.
    + destruct (rb_bot_values Φ' n · BOutOfFuel v Hev) as [-> | ->]; vm_compute; lia.
  - unfold rb_inner in He.
    destruct He as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]].
    + destruct (rb_body_values Φ' n v Hev) as [[r1 [r2 [-> [H1 H2]]]] | ->];
        [exact (rb_merge_if_bound rb_env r1 r2 H1 H2) | vm_compute; lia].
    + exact (rb_andval_size rb_env v (rb_guard_values Φ' n v Hev)).
    + rewrite (rb_and1_values Φ' n rb_env _ v Hev). vm_compute. lia.
    + rewrite (rb_prim_values Φ' n rb_env v Hev). vm_compute. lia.
    + destruct (rb_vara_values Φ' n v Hev) as [-> | ->]; vm_compute; lia.
    + destruct (rb_free_var_values Φ' n rb_env rb_y v Hev eq_refl) as [-> | ->];
        vm_compute; lia.
    + rewrite (rb_appbot_values Φ' n rb_env _ v Hev). vm_compute. lia.
    + rewrite (rb_appbot_values Φ' n rb_env _ v Hev). vm_compute. lia.
    + destruct (rb_bot_values Φ' n rb_env BOutOfFuel v Hev) as [-> | ->]; vm_compute; lia.
    + destruct (rb_lit_values Φ' n rb_env true v Hev) as [-> | ->]; vm_compute; lia.
    + destruct (rb_lit_values Φ' n rb_env false v Hev) as [-> | ->]; vm_compute; lia.
Qed.

Theorem rb_soundness_instance :
  exists v_con, · ⊢ᶜ rb_con ⇓ᶜ v_con /\ contains rb_sigma rb_S rb_value v_con.
Proof.
  exact (concore_soundness rb_phi · · rb_sigma rb_S rb_sym rb_con rb_value
           rb_sigma_models_phi (Cont_Env_Empty _ _) rb_contains rb_con_concore
           rb_con_closed rb_symbolic_program rb_sym_evaluates).
Qed.

Definition rb_pc : path_condition :=
  @PCPrim model_sorts PAnd (@PCVar model_sorts rb_x :: @PCVar model_sorts rb_y :: nil).

Theorem rb_runtime_branch_fires :
  expr_to_pc rb_env rb_guard = Some rb_pc /\
  pc_has_var rb_pc = true /\
  pc_arities_ok rb_pc = true /\
  fold_alts Inf rb_phi rb_env (merge rb_env rb_guard) rb_alts rb_value /\
  rb_phi ; · ⊢ rb_sym ⇓ rb_value.
Proof.
  split; [reflexivity | split; [reflexivity | split; [reflexivity | split]]].
  - unfold rb_value.
    eapply FoldAlts_SymbolicFormula; [reflexivity | reflexivity | reflexivity | |];
      (eapply FoldAlts_Con; [reflexivity | reflexivity |]); simpl; apply Eval_Lit.
  - exact rb_sym_evaluates.
Qed.

Theorem rb_every_bounded_value_branches : forall Φ n v,
  eval (Fin n) Φ · rb_sym v ->
  v = rb_bot \/ exists r1 r2, v = EIf rb_guard r1 r2.
Proof.
  intros Φ n v H. destruct (rb_sym_values Φ n v H) as [[r1 [r2 [-> _]]] | ->];
    [right; exists r1, r2; reflexivity | left; reflexivity].
Qed.

Theorem rb_completeness_budget_instance :
  exists h, forall n, (h <= n)%nat ->
    exists v_sym, eval (Fin n) rb_phi · rb_sym v_sym
      /\ contains rb_sigma rb_S v_sym (@ELit model_sorts false).
Proof.
  exact (concore_completeness_budget rb_phi · · rb_sigma rb_S rb_sym rb_con
           (@ELit model_sorts false)
           rb_sigma_models_phi (Cont_Env_Empty _ _) rb_contains rb_con_concore
           rb_con_closed rb_symbolic_program rb_smt_bounded
           (budget_total_of_terminating _ _ _ (ex_intro _ _ rb_sym_evaluates))
           rb_con_evaluates).
Qed.

Theorem rb_completeness_forall_instance :
  exists h, forall n, (h <= n)%nat ->
    forall v_sym, eval (Fin n) rb_phi · rb_sym v_sym ->
      contains rb_sigma rb_S v_sym (@ELit model_sorts false).
Proof.
  exact (concore_completeness_forall · rb_con (@ELit model_sorts false) rb_con_evaluates
           rb_phi · rb_sigma rb_S rb_sym rb_sigma_models_phi (Cont_Env_Empty _ _)
           rb_contains rb_con_concore rb_con_closed rb_symbolic_program rb_smt_bounded).
Qed.

End RuntimeBranch.
