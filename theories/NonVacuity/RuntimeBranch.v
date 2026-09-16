From SymCoreTheory Require Export NonVacuity.PruningModel.
From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat Lia.
Import ListNotations.
Open Scope string_scope.

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
