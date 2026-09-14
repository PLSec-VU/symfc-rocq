From SymCoreTheory Require Import SymCore ConCore.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.
Open Scope string_scope.

(* ========================================================================= *)
(* Why the completeness theorem needs a depth bound.                          *)
(*                                                                            *)
(* scratch/CompletenessNeedsFuel.v blocks the symbolic run with a STUCK       *)
(* untaken arm.  A stuck arm has no derivation at any depth, so a bound is    *)
(* not the fix for it; an undefined-fallback rule is.                         *)
(*                                                                            *)
(* This file supplies the case a bound really does fix: a DIVERGENT untaken   *)
(* arm.  Rule If needs a derivation for both arms and never consults a        *)
(* model, so the arm the concrete run skips must still terminate.  A          *)
(* divergent arm has no derivation either, but truncating it at a finite      *)
(* depth produces one.                                                        *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* 1. The divergence witness                                                  *)
(* ------------------------------------------------------------------------- *)

Definition floop : var := "f".
Definition loop_body : expr := EApp (EVar floop) (EVar floop).
Definition w : expr := ELam floop loop_body.
Definition omega : expr := EApp w w.

(* ELam is not a WHNF constructor, so Rule App-Spine fires on (w w): the head
   reduces by Rule Lam to a closure, and Rule App-Abs then unfolds the loop. *)
Lemma w_not_whnf : forall Γ, ~ Whnf Γ w.
Proof.
  intros Γ H. inversion H; subst. inversion H0.
Qed.

Lemma eval_w : forall Φ Γ v,
  sat Φ = true -> Φ ; Γ ⊢ w ⇓ v -> v = EClos Γ floop loop_body.
Proof.
  intros Φ Γ v Hsat H. inversion H; subst; [reflexivity | congruence].
Qed.

(* The invariant.

   Unfolding the loop does not restore the starting configuration.  Each
   turn extends the environment, and the binding it adds for f is not w but
   the expression (EVar f) read back in the PREVIOUS environment.  So after
   n turns the name f resolves through a chain of n indirections before it
   reaches w.  ResolvesToW is exactly that chain, and it is what makes the
   induction close. *)
Inductive ResolvesToW : environment -> Prop :=
  | RW_Lam : forall Γ Γ0,
      lookup_env Γ floop = Some (Γ0, w) ->
      ResolvesToW Γ
  | RW_Indirect : forall Γ Γ0,
      lookup_env Γ floop = Some (Γ0, EVar floop) ->
      ResolvesToW Γ0 ->
      ResolvesToW Γ.

(* The two ways the loop extends the environment both keep the chain intact. *)
Lemma resolves_extend_w : forall Γ0 Γ,
  ResolvesToW (extend_env Γ0 floop Γ w).
Proof.
  intros Γ0 Γ. eapply RW_Lam. unfold extend_env. simpl.
  destruct (string_dec floop floop); [reflexivity | contradiction].
Qed.

Lemma resolves_extend_var : forall Γ0 Γ,
  ResolvesToW Γ -> ResolvesToW (extend_env Γ0 floop Γ (EVar floop)).
Proof.
  intros Γ0 Γ H. eapply RW_Indirect; [| exact H]. unfold extend_env. simpl.
  destruct (string_dec floop floop); [reflexivity | contradiction].
Qed.

(* A name that resolves through the chain is bound, so it is not a value. *)
Lemma resolves_var_not_whnf : forall Γ,
  ResolvesToW Γ -> ~ Whnf Γ (EVar floop).
Proof.
  intros Γ HR H. inversion H; subst. inversion H0; subst.
  destruct HR; congruence.
Qed.

(* Whatever the chain length, f still denotes the loop closure. *)
Lemma eval_loop_var : forall Φ Γ,
  ResolvesToW Γ ->
  sat Φ = true ->
  forall v, Φ ; Γ ⊢ EVar floop ⇓ v -> exists Γ0, v = EClos Γ0 floop loop_body.
Proof.
  intros Φ Γ HR Hsat. induction HR.
  - intros v Hev. inversion Hev; subst.
    + rewrite H in H1. injection H1 as ? ?; subst.
      eexists. eapply eval_w; [exact Hsat | exact H4].
    + congruence.
    + congruence.
  - intros v Hev. inversion Hev; subst.
    + rewrite H in H1. injection H1 as ? ?; subst. apply IHHR. exact H4.
    + congruence.
    + congruence.
Qed.

(* The four configurations the loop passes through. *)
Inductive LoopCfg : environment -> expr -> Prop :=
  | LC_Self : forall Γ,
      LoopCfg Γ omega
  | LC_ClosW : forall Γ Γ0,
      LoopCfg Γ (EApp (EClos Γ0 floop loop_body) w)
  | LC_Var : forall Γ,
      ResolvesToW Γ ->
      LoopCfg Γ loop_body
  | LC_ClosVar : forall Γ Γ0,
      ResolvesToW Γ ->
      LoopCfg Γ (EApp (EClos Γ0 floop loop_body) (EVar floop)).

(* Every step out of a loop configuration lands in a loop configuration, so
   the derivation can never bottom out.  The induction is on the derivation,
   not on the term. *)
Lemma loop_has_no_value : forall Φ Γ e v,
  Φ ; Γ ⊢ e ⇓ v -> sat Φ = true -> LoopCfg Γ e -> False.
Proof.
  intros Φ Γ e v H.
  induction H; intros Hsat HL;
    try (inversion HL; unfold omega, loop_body, w in *; discriminate).
  - (* Rule App-Abs *)
    inversion HL; subst.
    + apply IHeval; [exact Hsat | apply LC_Var; apply resolves_extend_w].
    + apply IHeval; [exact Hsat |].
      apply LC_Var. apply resolves_extend_var. exact H2.
  - (* Rule App-Spine *)
    inversion HL; subst.
    + (* head is the literal lambda w; Rule Lam turns it into the closure *)
      assert (Hef : ef' = EClos Γ floop loop_body) by (apply (eval_w Φ Γ ef' Hsat H0)).
      subst ef'. apply IHeval2; [exact Hsat | apply LC_ClosW].
    + exfalso. apply H. apply Whnf_Clos.
    + (* head is f; the chain resolves it to the closure *)
      destruct (eval_loop_var Φ Γ H4 Hsat ef' H0) as [Γ0 Hef]. subst ef'.
      apply IHeval2; [exact Hsat | apply LC_ClosVar; exact H4].
    + exfalso. apply H. apply Whnf_Clos.
  - (* Rule App-Prim *)
    inversion HL; subst; unfold omega, loop_body, w in H; simpl in H;
      injection H as ? ?; discriminate.
  - (* Rule Prune *)
    congruence.
Qed.

(* The witness: omega has no derivation on any satisfiable path. *)
Theorem omega_diverges : forall Φ Γ v,
  sat Φ = true -> ~ (Φ ; Γ ⊢ omega ⇓ v).
Proof.
  intros Φ Γ v Hsat H. eapply loop_has_no_value; [exact H | exact Hsat | apply LC_Self].
Qed.

(* omega is not stuck, it loops.  The rules DO apply to it: one unfolding
   turns the goal into the same goal one environment deeper.  That is the
   difference from EApp (ELit l) (ELit l), where no rule applies at all. *)
Theorem omega_unfolds_once : forall Φ Γ v,
  Φ ; extend_env Γ floop Γ w ⊢ loop_body ⇓ v -> Φ ; Γ ⊢ omega ⇓ v.
Proof.
  intros Φ Γ v H. unfold omega.
  eapply Eval_AppSpine with (ef' := EClos Γ floop loop_body).
  - apply w_not_whnf.
  - unfold w. apply Eval_Lam.
  - apply Eval_AppAbs. exact H.
Qed.

(* ------------------------------------------------------------------------- *)
(* 2. Completeness fails against plain eval                                   *)
(* ------------------------------------------------------------------------- *)

Section CompletenessFailsOnDivergentArm.
  Variables (Φ : path_condition) (σ : valuation) (S : symvars).
  Variables (x : var) (l' : lit).

  Hypothesis Hsat    : sat Φ = true.
  Hypothesis Hfeas   : forall pc, sat (Φ ∧ ¬ pc) = true.
  Hypothesis Hchoose : models_cond σ S (EVar x).

  Definition e_div : expr := EIf (EVar x) (ELit l') omega.

  (* Every premise of the planned completeness theorem holds. *)
  Lemma div_premises_hold :
    contains_env σ S · ·
    /\ contains σ S e_div (ELit l')
    /\ · ⊢ᶜ ELit l' ⇓ᶜ ELit l'.
  Proof.
    split; [apply Cont_Env_Empty |].
    split.
    - apply Cont_If_True; [exact Hchoose | apply Cont_Lit].
    - apply Eval_Lit.
  Qed.

  (* But the symbolic run has no value at all. *)
  Theorem no_symbolic_derivation_div : ~ (exists v, Φ ; · ⊢ e_div ⇓ v).
  Proof.
    intros [v Heval]. unfold e_div in Heval.
    inversion Heval; subst.
    - eapply omega_diverges; [apply Hfeas | exact H8].
    - congruence.
  Qed.
End CompletenessFailsOnDivergentArm.

(* The blockage does not depend on the model: Rule If mentions no valuation,
   and its conclusion carries both arms. *)
Theorem diverges_regardless_of_any_model : forall Φ x l',
  sat Φ = true ->
  (forall pc, sat (Φ ∧ ¬ pc) = true) ->
  ~ (exists v, Φ ; · ⊢ EIf (EVar x) (ELit l') omega ⇓ v).
Proof.
  intros Φ x l' Hsat Hfeas [v Heval].
  inversion Heval; subst.
  - eapply omega_diverges; [apply Hfeas | exact H8].
  - congruence.
Qed.

(* ------------------------------------------------------------------------- *)
(* 3. A depth bound rescues the divergent case                                *)
(* ------------------------------------------------------------------------- *)

(* A minimal depth-bounded evaluator.  It carries only the rules this example
   needs: an out-of-fuel rule, and the counterparts of Lit, Sym-Var, Var, Lam,
   App-Abs, App-Bot, App-Spine and If.  Apart from the out-of-fuel rule, each
   one is the rule of the same name in SymCore.v with a depth counter added.
   Every rule costs one unit of depth; only depth zero truncates.

   App-Bot is here for a reason.  Without it a truncated head (EBot
   BUndefined) in function position would block the next application, and
   the loop would have a value at some depths and none at others. *)
Inductive eval_k : nat -> path_condition -> environment -> expr -> expr -> Prop :=
  | EvalK_OutOfFuel : forall Φ Γ e,
      eval_k 0 Φ Γ e (EBot BUndefined)
  | EvalK_Lit : forall k Φ Γ l,
      eval_k (S k) Φ Γ (ELit l) (ELit l)
  | EvalK_SymVar : forall k Φ Γ y,
      lookup_env Γ y = None ->
      eval_k (S k) Φ Γ (EVar y) (EVar y)
  | EvalK_Var : forall k Φ Γ y Γ' e e',
      lookup_env Γ y = Some (Γ', e) ->
      eval_k k Φ Γ' e e' ->
      eval_k (S k) Φ Γ (EVar y) e'
  | EvalK_Lam : forall k Φ Γ y e,
      eval_k (S k) Φ Γ (ELam y e) (EClos Γ y e)
  | EvalK_AppAbs : forall k Φ Γ Γ' y eb ea eb',
      eval_k k Φ (extend_env Γ' y Γ ea) eb eb' ->
      eval_k (S k) Φ Γ (EApp (EClos Γ' y eb) ea) eb'
  | EvalK_AppBot : forall k Φ Γ b ea,
      eval_k (S k) Φ Γ (EApp (EBot b) ea) (EBot b)
  | EvalK_AppSpine : forall k Φ Γ ef ea ef' er,
      ~ Whnf Γ ef ->
      eval_k k Φ Γ ef ef' ->
      eval_k k Φ Γ (EApp ef' ea) er ->
      eval_k (S k) Φ Γ (EApp ef ea) er
  | EvalK_If : forall k Φ Γ ec et ef ec' et' ef' pc_c,
      eval_k k Φ Γ ec ec' ->
      expr_to_pc Γ ec' = Some pc_c ->
      eval_k k (Φ ∧ pc_c) Γ et et' ->
      eval_k k (Φ ∧ ¬ pc_c) Γ ef ef' ->
      eval_k (S k) Φ Γ (EIf ec et ef) (EIf ec' et' ef').

(* At depth zero every expression truncates. *)
Lemma eval_k_zero_inv : forall Φ Γ e v,
  eval_k 0 Φ Γ e v -> v = EBot BUndefined.
Proof.
  intros Φ Γ e v H. inversion H; subst. reflexivity.
Qed.

(* A truncated condition reads off no formula, so Rule If cannot fire above
   it.  That is why depth 1 is not enough here. *)
Lemma truncated_cond_blocks_if : forall Φ Γ ec ec' pc,
  eval_k 0 Φ Γ ec ec' -> expr_to_pc Γ ec' = Some pc -> False.
Proof.
  intros Φ Γ ec ec' pc H Hpc.
  rewrite (eval_k_zero_inv Φ Γ ec ec' H) in Hpc. simpl in Hpc. discriminate.
Qed.

Ltac kill_truncated_cond :=
  match goal with
  | [ Ha : eval_k 0 _ _ _ ?c, Hb : expr_to_pc _ ?c = Some _ |- _ ] =>
      exact (truncated_cond_blocks_if _ _ _ _ _ Ha Hb)
  end.

(* A truncated result never meets the completeness conclusion. *)
Lemma bot_undefined_not_lit : forall σ Sv l,
  ~ contains σ Sv (EBot BUndefined) (ELit l).
Proof.
  intros σ Sv l Hc. inversion Hc; subst; kill_denote.
Qed.

(* At depth 1 the loop truncates instead of blocking. *)
Lemma omega_truncates_at_one : forall Φ Γ,
  eval_k 1 Φ Γ omega (EBot BUndefined).
Proof.
  intros Φ Γ. unfold omega.
  eapply EvalK_AppSpine with (ef' := EBot BUndefined).
  - apply w_not_whnf.
  - apply EvalK_OutOfFuel.
  - apply EvalK_OutOfFuel.
Qed.

(* Reading f at a bounded depth either runs out of depth or delivers the loop
   closure.  Nothing else can come out, whatever the chain length. *)
Lemma loop_var_value : forall Γ,
  ResolvesToW Γ ->
  forall k Ψ, exists v,
    eval_k k Ψ Γ (EVar floop) v
    /\ (v = EBot BUndefined \/ exists Γ0, v = EClos Γ0 floop loop_body).
Proof.
  intros Γ HR. induction HR as [Γa Γb Hl | Γa Γb Hl HR IH];
    intros k Ψ; destruct k as [| k].
  - exists (EBot BUndefined). split; [apply EvalK_OutOfFuel | left; reflexivity].
  - destruct k as [| k].
    + exists (EBot BUndefined).
      split; [eapply EvalK_Var; [exact Hl | apply EvalK_OutOfFuel] | left; reflexivity].
    + exists (EClos Γb floop loop_body). split.
      * eapply EvalK_Var; [exact Hl |]. unfold w. apply EvalK_Lam.
      * right. exists Γb. reflexivity.
  - exists (EBot BUndefined). split; [apply EvalK_OutOfFuel | left; reflexivity].
  - destruct (IH k Ψ) as [v [Hv Hshape]].
    exists v. split; [eapply EvalK_Var; [exact Hl | exact Hv] | exact Hshape].
Qed.

(* The divergent term has a value at EVERY depth.  This is the whole point:
   the loop never blocks, it only truncates, so a bound always delivers a
   derivation where plain eval delivers none. *)
Lemma loop_truncates_at_every_depth : forall k Ψ Γ e,
  LoopCfg Γ e -> exists v, eval_k k Ψ Γ e v.
Proof.
  induction k as [| k IH]; intros Ψ Γ e HL.
  - exists (EBot BUndefined). apply EvalK_OutOfFuel.
  - inversion HL; subst.
    + (* omega *)
      destruct k as [| k].
      * exists (EBot BUndefined). unfold omega.
        eapply EvalK_AppSpine with (ef' := EBot BUndefined);
          [apply w_not_whnf | apply EvalK_OutOfFuel | apply EvalK_OutOfFuel].
      * destruct (IH Ψ Γ (EApp (EClos Γ floop loop_body) w) (LC_ClosW Γ Γ))
          as [v Hv].
        exists v. unfold omega.
        eapply EvalK_AppSpine with (ef' := EClos Γ floop loop_body);
          [apply w_not_whnf | unfold w; apply EvalK_Lam | exact Hv].
    + (* the closure applied to w *)
      destruct (IH Ψ (extend_env Γ1 floop Γ w) loop_body
                   (LC_Var _ (resolves_extend_w Γ1 Γ))) as [v Hv].
      exists v. apply EvalK_AppAbs. exact Hv.
    + (* f f, with f resolving through the chain *)
      destruct (loop_var_value Γ H k Ψ) as [vf [Hvf [Hbot | [Γ0 Hclos]]]].
      * subst vf. destruct k as [| k].
        -- exists (EBot BUndefined). unfold loop_body.
           eapply EvalK_AppSpine with (ef' := EBot BUndefined);
             [apply resolves_var_not_whnf; exact H | exact Hvf | apply EvalK_OutOfFuel].
        -- exists (EBot BUndefined). unfold loop_body.
           eapply EvalK_AppSpine with (ef' := EBot BUndefined);
             [apply resolves_var_not_whnf; exact H | exact Hvf | apply EvalK_AppBot].
      * subst vf.
        destruct (IH Ψ Γ (EApp (EClos Γ0 floop loop_body) (EVar floop))
                     (LC_ClosVar Γ Γ0 H)) as [v Hv].
        exists v. unfold loop_body.
        eapply EvalK_AppSpine with (ef' := EClos Γ0 floop loop_body);
          [apply resolves_var_not_whnf; exact H | exact Hvf | exact Hv].
    + (* the closure applied to f *)
      destruct (IH Ψ (extend_env Γ1 floop Γ (EVar floop)) loop_body
                   (LC_Var _ (resolves_extend_var Γ1 Γ H))) as [v Hv].
      exists v. apply EvalK_AppAbs. exact Hv.
Qed.

Corollary omega_truncates_at_every_depth : forall k Ψ Γ,
  exists v, eval_k k Ψ Γ omega v.
Proof.
  intros k Ψ Γ. apply (loop_truncates_at_every_depth k Ψ Γ omega (LC_Self Γ)).
Qed.

Section BoundRescuesDivergence.
  Variables (Φ : path_condition) (σ : valuation) (Sv : symvars).
  Variables (x : var) (l' : lit).

  Hypothesis Hchoose : models_cond σ Sv (EVar x).

  Definition v_div : expr := EIf (EVar x) (ELit l') (EBot BUndefined).

  (* Depth 2 works: the taken arm reaches ELit l', the untaken arm truncates. *)
  Theorem bound_rescues_divergence :
    eval_k 2 Φ · (EIf (EVar x) (ELit l') omega) v_div
    /\ contains σ Sv v_div (ELit l').
  Proof.
    split.
    - eapply EvalK_If with (pc_c := PCVar x).
      + apply EvalK_SymVar. reflexivity.
      + reflexivity.
      + apply EvalK_Lit.
      + apply omega_truncates_at_one.
    - apply Cont_If_True; [exact Hchoose | apply Cont_Lit].
  Qed.

  (* And every greater depth works too, so the bound is not a lucky number.
     The untaken arm truncates to something at each depth; whatever it is,
     the model selects the taken arm, which still reaches ELit l'. *)
  Theorem every_depth_above_one_works : forall k,
    exists v, eval_k (S (S k)) Φ · (EIf (EVar x) (ELit l') omega) v
           /\ contains σ Sv v (ELit l').
  Proof.
    intros k.
    destruct (omega_truncates_at_every_depth (S k) (Φ ∧ ¬ PCVar x) ·) as [vf Hvf].
    exists (EIf (EVar x) (ELit l') vf). split.
    - eapply EvalK_If with (pc_c := PCVar x).
      + apply EvalK_SymVar. reflexivity.
      + reflexivity.
      + apply EvalK_Lit.
      + exact Hvf.
    - apply Cont_If_True; [exact Hchoose | apply Cont_Lit].
  Qed.

  (* Two is the least depth that works. *)
  Theorem depth_zero_misses : forall v,
    eval_k 0 Φ · (EIf (EVar x) (ELit l') omega) v -> ~ contains σ Sv v (ELit l').
  Proof.
    intros v H. inversion H; subst. apply bot_undefined_not_lit.
  Qed.

  Theorem depth_one_has_no_value :
    ~ (exists v, eval_k 1 Φ · (EIf (EVar x) (ELit l') omega) v).
  Proof.
    intros [v H]. inversion H; subst.
    kill_truncated_cond.
  Qed.
End BoundRescuesDivergence.

(* ------------------------------------------------------------------------- *)
(* 4. Contrast: no depth rescues the stuck case                               *)
(* ------------------------------------------------------------------------- *)

Section BoundDoesNotRescueStuckness.
  Variables (Φ : path_condition) (σ : valuation) (Sv : symvars).
  Variables (x : var) (l l' : lit).

  Definition stuck_arm : expr := EApp (ELit l) (ELit l).
  Definition e_stuck : expr := EIf (EVar x) (ELit l') stuck_arm.

  (* A stuck term has no derivation at any POSITIVE depth: no rule matches it,
     and out-of-fuel fires only at depth zero.  That is the difference from a
     divergent term, which truncates at every positive depth. *)
  Lemma stuck_arm_no_value_above_zero : forall k Ψ Γ v,
    eval_k (S k) Ψ Γ stuck_arm v -> False.
  Proof.
    intros k Ψ Γ v H. unfold stuck_arm in H.
    inversion H; subst.
    match goal with
    | [ Hn : ~ Whnf _ (ELit _) |- _ ] =>
        apply Hn; apply Whnf_Solvable; apply Solvable_Lit
    end.
  Qed.

  (* So no depth meets the completeness conclusion: depth zero truncates the
     whole term, and every greater depth blocks on the stuck arm. *)
  Theorem no_bound_rescues_stuckness : forall k v,
    eval_k k Φ · e_stuck v -> ~ contains σ Sv v (ELit l').
  Proof.
    intros k v H. unfold e_stuck in H. destruct k as [| k].
    - inversion H; subst. apply bot_undefined_not_lit.
    - exfalso. inversion H; subst.
      destruct k as [| k].
      + kill_truncated_cond.
      + eapply stuck_arm_no_value_above_zero; eassumption.
  Qed.

  Theorem stuck_has_no_value_above_one : forall k v,
    ~ eval_k (S (S k)) Φ · e_stuck v.
  Proof.
    intros k v H. unfold e_stuck in H. inversion H; subst.
    eapply stuck_arm_no_value_above_zero; eassumption.
  Qed.
End BoundDoesNotRescueStuckness.
