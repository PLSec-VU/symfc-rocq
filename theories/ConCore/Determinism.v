From SymCoreTheory Require Export ConCore.Preservation.
From Stdlib Require Import Strings.String Lists.List Lia Arith.PeanoNat.
Import ListNotations.

Section ConCore.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}
  {reduce_prim_solvable_law : ReducePrimSolvable}
  {reduce_prim_saturated_law : ReducePrimSaturated}.
Context {reduce_prim_concore_law : ReducePrimConcore}.
Context {cast_expr_concore_law : CastExprConcore}.
Context {reduce_prim_scoped_law : ReducePrimScoped} {cast_expr_scoped_law : CastExprScoped}.
Context {reduce_prim_keeps_out_of_fuel_law : ReducePrimKeepsOutOfFuel}
  {cast_expr_keeps_out_of_fuel_law : CastExprKeepsOutOfFuel}.

(**
  The statement below is the one that matters for soundness: a ConCore
  expression, run in an environment that binds only ConCore expressions, has
  at most one value. Both hypotheses are needed.

  concore_expr excludes EIf, which is what keeps Rule Prune out of the way:
  Rule Prune fires only under an unsatisfiable path condition, the run
  starts at pc_true, and the only rule that changes the path condition is
  Rule If.

  concrete_env excludes it from the environment too. Without that, Rule Var
  walks into whatever the environment holds, a branch included, and Rule
  Prune can fire inside it.

  Everything else is rule disjointness, and the proof is one case per rule
  of the second derivation. The interesting rows:

    App-Spine against App-Cast   : a cast is not a computation.
    App-Spine against App-Prim   : a computation has no primitive spine head.
    App-Spine against App-If     : a computation has no branch spine head.
    App-Spine against App-Abs    : a closure is not a computation.
    App-Spine against App-Bot    : a bottom is not a computation.
*)

Lemma comp_spine_head : forall Γ ef ea h args,
  Comp Γ ef ->
  unspool_app (EApp ef ea) [] = (h, args) ->
  has_whole_spine_rule h = false.
Proof.
  intros Γ ef ea h args Hcomp Hu.
  replace h with (fst (unspool_app (EApp ef ea) [])) by (rewrite Hu; reflexivity).
  rewrite fst_unspool_app. simpl.
  destruct Hcomp; simpl in *; try reflexivity; assumption.
Qed.

End ConCore.

Ltac prune_absurd :=
  match goal with
  | [ Hs : sat ?F = true, Hu : sat ?F = false |- _ ] => rewrite Hs in Hu; discriminate
  end.

Ltac app_rule_absurd :=
  first
  [ prune_absurd
  | no_con_head
  | match goal with
    | [ H : Comp _ _ |- _ ] => solve [inversion H; subst; simpl in *; discriminate]
    end
  | match goal with
    | [ Hc : Comp _ ?f, Hu : unspool_app (EApp ?f _) [] = (_, _) |- _ ] =>
        solve [pose proof (comp_spine_head _ _ _ _ _ Hc Hu) as Hw; simpl in Hw; discriminate Hw]
    end
  | match goal with
    | [ H : unspool_app (EApp _ _) [] = _ |- _ ] => solve [simpl in H; discriminate H]
    end
  | match goal with
    | [ H1 : unspool_app ?e ?a = _, H2 : unspool_app ?e ?a = _ |- _ ] =>
        solve [rewrite H1 in H2; discriminate H2]
    end ].

Section ConCore.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}
  {reduce_prim_solvable_law : ReducePrimSolvable}
  {reduce_prim_saturated_law : ReducePrimSaturated}.
Context {reduce_prim_concore_law : ReducePrimConcore}.
Context {cast_expr_concore_law : CastExprConcore}.
Context {reduce_prim_scoped_law : ReducePrimScoped} {cast_expr_scoped_law : CastExprScoped}.
Context {reduce_prim_keeps_out_of_fuel_law : ReducePrimKeepsOutOfFuel}
  {cast_expr_keeps_out_of_fuel_law : CastExprKeepsOutOfFuel}.
(** One inversion lemma per shape of the term being evaluated. Each one says
    which rule the second derivation must have used, and carries its
    premises out. *)

Lemma eval_var_bound_inv : forall Φ Γ x Γ' e0 v,
  sat Φ = true ->
  lookup_env Γ x = Some (Γ', e0) ->
  Φ ; Γ ⊢ EVar x ⇓ v ->
  Φ ; Γ' ⊢ e0 ⇓ v.
Proof.
  intros Φ Γ x Γ' e0 v Hsat Hlook Heval.
  inversion Heval; subst; try prune_absurd; try no_con_head.
  - match goal with
    | [ H : lookup_env Γ x = Some (?G, ?E) |- _ ] =>
        assert (Heq : Some (G, E) = Some (Γ', e0)) by (rewrite <- H; exact Hlook)
    end.
    injection Heq as Hg He. subst. assumption.
  - congruence.
Qed.

Lemma eval_var_free_inv : forall Φ Γ x v,
  sat Φ = true ->
  lookup_env Γ x = None ->
  Φ ; Γ ⊢ EVar x ⇓ v ->
  v = EVar x.
Proof.
  intros Φ Γ x v Hsat Hlook Heval.
  inversion Heval; subst; try prune_absurd; try no_con_head; [congruence | reflexivity].
Qed.

Lemma eval_lit_inv : forall Φ Γ l v,
  sat Φ = true -> Φ ; Γ ⊢ ELit l ⇓ v -> v = ELit l.
Proof.
  intros Φ Γ l v Hsat Heval.
  inversion Heval; subst; try prune_absurd; try no_con_head; reflexivity.
Qed.

Lemma eval_bot_inv : forall Φ Γ b v,
  sat Φ = true -> Φ ; Γ ⊢ EBot b ⇓ v -> v = EBot b.
Proof.
  intros Φ Γ b v Hsat Heval.
  inversion Heval; subst; try prune_absurd; try no_con_head; reflexivity.
Qed.

Lemma eval_lam_inv : forall Φ Γ x e0 v,
  sat Φ = true -> Φ ; Γ ⊢ ELam x e0 ⇓ v -> v = EThunk Γ (ELam x e0).
Proof.
  intros Φ Γ x e0 v Hsat Heval.
  inversion Heval; subst; try prune_absurd; try no_con_head; reflexivity.
Qed.

Lemma eval_coercion_inv : forall Φ Γ γ v,
  sat Φ = true -> Φ ; Γ ⊢ ECoercion γ ⇓ v -> v = ECoercion (subst_coerc Γ γ).
Proof.
  intros Φ Γ γ v Hsat Heval.
  inversion Heval; subst; try prune_absurd; try no_con_head; reflexivity.
Qed.

Lemma eval_type_inv : forall Φ Γ τ v,
  sat Φ = true -> Φ ; Γ ⊢ EType τ ⇓ v -> v = EType (subst_type Γ τ).
Proof.
  intros Φ Γ τ v Hsat Heval.
  inversion Heval; subst; try prune_absurd; try no_con_head; reflexivity.
Qed.

Lemma eval_thunk_inv : forall Φ Γ Γ' e0 v,
  sat Φ = true -> Φ ; Γ ⊢ EThunk Γ' e0 ⇓ v -> Φ ; Γ' ⊢ e0 ⇓ v.
Proof.
  intros Φ Γ Γ' e0 v Hsat Heval.
  inversion Heval; subst; try prune_absurd; try no_con_head; assumption.
Qed.

Lemma eval_cast_inv : forall Φ Γ e0 γ v,
  sat Φ = true ->
  Φ ; Γ ⊢ ECast e0 γ ⇓ v ->
  exists e', Φ ; Γ ⊢ e0 ⇓ e' /\ v = cast_expr e' γ.
Proof.
  intros Φ Γ e0 γ v Hsat Heval.
  inversion Heval; subst; try prune_absurd; try no_con_head.
  eexists. split; [eassumption | reflexivity].
Qed.

Lemma eval_case_inv : forall Φ Γ es alts v,
  sat Φ = true ->
  Φ ; Γ ⊢ ECase es alts ⇓ v ->
  exists es', Φ ; Γ ⊢ es ⇓ es' /\ fold_alts Inf Φ Γ (merge Γ es') alts v.
Proof.
  intros Φ Γ es alts v Hsat Heval.
  inversion Heval; subst; try prune_absurd; try no_con_head.
  eexists. split; eassumption.
Qed.

Lemma eval_app_clos_inv : forall Φ Γ Γ' x eb ea v,
  sat Φ = true ->
  Φ ; Γ ⊢ EApp (EThunk Γ' (ELam x eb)) ea ⇓ v ->
  Φ ; extend_env Γ' x Γ ea ⊢ eb ⇓ v.
Proof.
  intros Φ Γ Γ' x eb ea v Hsat Heval.
  inversion Heval; subst; try app_rule_absurd.
  assumption.
Qed.

Lemma eval_app_bot_inv : forall Φ Γ b ea v,
  sat Φ = true ->
  Φ ; Γ ⊢ EApp (EBot b) ea ⇓ v ->
  v = EBot b.
Proof.
  intros Φ Γ b ea v Hsat Heval.
  inversion Heval; subst; try app_rule_absurd.
  reflexivity.
Qed.

Lemma eval_app_cast_arrow_inv : forall Φ Γ eb γ γ_a γ_r ea v,
  sat Φ = true ->
  decomp_coerc_arrow γ = Some (γ_a, γ_r) ->
  Φ ; Γ ⊢ EApp (ECast eb γ) ea ⇓ v ->
  Φ ; Γ ⊢ ECast (EApp eb (ECast ea (sym_coerc γ_a))) γ_r ⇓ v.
Proof.
  intros Φ Γ eb γ γ_a γ_r ea v Hsat Hdec Heval.
  inversion Heval; subst; try app_rule_absurd.
  match goal with
  | [ H : decomp_coerc_arrow γ = Some (?A, ?R) |- _ ] =>
      assert (Heq : Some (A, R) = Some (γ_a, γ_r)) by (rewrite <- H; exact Hdec)
  end.
  injection Heq as Ha Hr. subst. assumption.
Qed.

(** Rule App-Spine keeps its own premises: no other rule can fire where it
    fires, given that the operator already has a value. *)
Lemma eval_app_spine_inv : forall Φ Γ ef ea v,
  sat Φ = true ->
  Comp Γ ef ->
  Φ ; Γ ⊢ EApp ef ea ⇓ v ->
  exists ef', Φ ; Γ ⊢ ef ⇓ ef' /\ Φ ; Γ ⊢ EApp ef' ea ⇓ v.
Proof.
  intros Φ Γ ef ea v Hsat Hcomp Heval.
  inversion Heval; subst; try app_rule_absurd.
  eexists. split; eassumption.
Qed.

Lemma eval_app_prim_inv : forall Φ Γ ef ea p args v,
  sat Φ = true ->
  unspool_app (EApp ef ea) [] = (EPrimOp p, args) ->
  Datatypes.length args = primop_arity p ->
  Φ ; Γ ⊢ EApp ef ea ⇓ v ->
  exists args', Forall2 (eval Inf Φ Γ) args args' /\ v = reduce_prim p args'.
Proof.
  intros Φ Γ ef ea p args v Hsat Hun Hlen Heval.
  inversion Heval; subst; try app_rule_absurd.
  match goal with
  | [ H : unspool_app (EApp ef ea) [] = (EPrimOp ?q, ?qargs) |- _ ] =>
      assert (Heq : (EPrimOp q, qargs) = (EPrimOp p, args)) by (rewrite <- H; exact Hun)
  end.
  injection Heq as Hp Hargs. subst.
  eexists. split; [eassumption | reflexivity].
Qed.

(** A constructor spine is not a boolean formula, so the two formula clauses
    of fold-alts never compete with Rule FoldAlts_Con. *)
Lemma con_app_expr_to_pc_none : forall Γ e,
  is_con_app e = true -> expr_to_pc Γ e = None.
Proof.
  intros Γ e. induction e; simpl; intros H; try discriminate; try reflexivity.
  rewrite (IHe1 H). reflexivity.
Qed.

Lemma decompose_con_app_is_con_app : forall e d ea,
  decompose_con_app e = Some (d, ea) -> is_con_app e = true.
Proof.
  intros e d ea Hdec. destruct (is_con_app e) eqn:E; [reflexivity |].
  rewrite (decompose_con_app_none e E) in Hdec. discriminate Hdec.
Qed.

Lemma fold_alts_con_inv : forall f Φ Γ e d ea xs ep alts r,
  decompose_con_app e = Some (d, ea) ->
  find_alt d alts = Some (xs, ep) ->
  fold_alts f Φ Γ e alts r ->
  eval f Φ (extend_env_multi Γ xs ea Γ) ep r.
Proof.
  intros f Φ Γ e d ea xs ep alts r Hdec Hfind Hfold.
  assert (Hpcnone : expr_to_pc Γ e = None)
    by exact (con_app_expr_to_pc_none Γ e (decompose_con_app_is_con_app e d ea Hdec)).
  inversion Hfold; subst; unfold decompose_con_app in Hdec; simpl in Hdec;
    try discriminate;
    try (match goal with
         | [ H : expr_to_pc Γ e = Some _ |- _ ] => rewrite Hpcnone in H; discriminate H
         end).
  - match goal with
    | [ H : decompose_con_app e = Some (?D, ?EA) |- _ ] =>
        unfold decompose_con_app in H;
        assert (Heq : Some (D, EA) = Some (d, ea)) by (rewrite <- H; exact Hdec)
    end.
    injection Heq as Hd Hea. subst.
    match goal with
    | [ H : find_alt d alts = Some (?XS, ?EP) |- _ ] =>
        assert (Heq2 : Some (XS, EP) = Some (xs, ep)) by (rewrite <- H; exact Hfind)
    end.
    injection Heq2 as Hxs Hep. subst. assumption.
  - match goal with
    | [ H : match decompose_con_app ?E with _ => _ end |- _ ] =>
        unfold decompose_con_app in H; rewrite Hdec in H; congruence
    end.
Qed.

Lemma fold_alts_bot_inv : forall f Φ Γ b alts r,
  fold_alts f Φ Γ (EBot b) alts r -> r = EBot b.
Proof.
  intros f Φ Γ b alts r Hfold.
  inversion Hfold; subst; simpl in *; try reflexivity; try discriminate.
Qed.

Lemma fold_alts_otherwise_inv : forall f Φ Γ e alts r,
  expr_to_pc Γ e = None ->
  is_if e = false ->
  (match decompose_con_app e with
   | Some (d, _) => find_alt d alts = None
   | None => True
   end) ->
  is_bot e = false ->
  fold_alts f Φ Γ e alts r ->
  r = EBot BUndefined.
Proof.
  intros f Φ Γ e alts r Hpcnone Hif Hno Hbot Hfold.
  inversion Hfold; subst; simpl in *; try discriminate; try reflexivity;
    try (match goal with
         | [ H : expr_to_pc Γ e = Some _ |- _ ] => rewrite Hpcnone in H; discriminate H
         end).
  - exfalso. match goal with
    | [ Hd : decompose_con_app e = Some (?D, ?EA),
        Hf : find_alt ?D alts = Some _ |- _ ] =>
        rewrite Hd in Hno; rewrite Hno in Hf; discriminate
    end.
Qed.

(**
  Determinism itself, as a pair of mutually recursive fixpoints, for the
  same reason as concore_eval_closed_fix: Rule App-Prim needs the statement
  for every argument of its Forall2, and the derived induction scheme
  supplies no induction hypothesis there.

  The recursion runs on the FIRST derivation. The second one is taken apart
  by the inversion lemmas above, so nothing depends on its shape.

  Unlimited budget only, hence the k0 = Inf premise. Rule App-Spine no
  longer fires on a primitive spine, because Comp excludes it, so the old
  overlap with Rule App-Prim at Fin 0 is gone. A finite budget still breaks
  the argument in a different step. At a finite budget a value can be
  EBot BOutOfFuel, which is not ConCore, so concore_eval_closed_fix does not
  apply. The laws fix cast_expr and reduce_prim only on ConCore input and on
  input that contains relates, and a closure over an out-of-fuel binding is
  neither. So the laws allow cast_expr to turn such a closure into a branch,
  and Rule Prune can then answer its dead arm while Rule Lit answers the
  same arm.
*)
Fixpoint eval_det_fix (k0 : fuel) (Φ : path_condition) (Γ : environment) (e v1 : expr)
  (Heval : eval k0 Φ Γ e v1) {struct Heval} :
  k0 = Inf ->
  forall v2, sat Φ = true -> concrete_env Γ -> concore_expr e -> closed_program Γ e ->
    Φ; Γ ⊢ e ⇓ v2 -> v1 = v2
with fold_alts_det_fix (k0 : fuel) (Φ : path_condition) (Γ : environment) (e : expr)
  (alts : list alt) (r1 : expr) (Hfold : fold_alts k0 Φ Γ e alts r1) {struct Hfold} :
  k0 = Inf ->
  forall r2, sat Φ = true -> concrete_env Γ -> concore_expr e ->
    Forall concore_alt alts -> scoped_env Γ -> closed_term e ->
    Forall (scoped_alt (dom_env Γ)) alts ->
    fold_alts Inf Φ Γ e alts r2 -> r1 = r2.
Proof.
{
  destruct Heval as
    [ kv Φ Γ x Γ' e0 e' Hlook Heval_x
    | kv Φ Γ x Hnone
    | kv Φ Γ l
    | kv Φ Γ esp d args_con Hunspool_con
    | kv Φ Γ e0 γ e' Heval_e
    | kv Φ Γ Γ' x eb ea eb' Heval_b
    | kv Φ Γ ef ea ef' er Hcomp Heval_f Heval_app2
    | kv Φ Γ b
    | kv Φ Γ ef ea p args args' Hunspool Harity Hargs
    | kv Φ Γ x e0
    | kv Φ Γ ef γ ea γ_a γ_r er Hdecomp Heval_pushed
    | kv Φ Γ e1 e2 ec et ef args er Hunspool_if Heval_arms
    | kv Φ Γ b ea
    | kv Φ Γ es alts es' er Heval_es Hfold
    | kv Φ Γ ec et ef ec' et' ef' pc_c Heval_c Hpc Heval_t Heval_ff
    | kv Φ Γ γ
    | kv Φ Γ e0 Hunsat
    | kv Φ Γ τ
    | kv Φ Γ Γ' e0 e' Heval_t
    | Φ Γ e0
    ]; intros Hk0; try discriminate Hk0; injection Hk0 as Hk0; subst kv;
      intros v2 Hsat Henv Hcon [HΓ Hsc] H2.
  - (* Rule Var *)
    destruct (lookup_env_concrete Γ x Γ' e0 Henv Hlook) as [Henv' He].
    destruct (lookup_env_scoped Γ x Γ' e0 HΓ Hlook) as [HΓ' Hsc'].
    exact (eval_det_fix Inf Φ Γ' e0 e' Heval_x eq_refl v2 Hsat Henv' He (conj HΓ' Hsc')
             (eval_var_bound_inv Φ Γ x Γ' e0 v2 Hsat Hlook H2)).
  - (* Rule Sym-Var *) symmetry. exact (eval_var_free_inv Φ Γ x v2 Hsat Hnone H2).
  - (* Rule Lit *) symmetry. exact (eval_lit_inv Φ Γ l v2 Hsat H2).
  - (* Rule Con *) symmetry.
    exact (eval_con_spine_same Φ Γ esp d args_con v2 Hsat Hunspool_con H2).
  - (* Rule Cast *)
    destruct (eval_cast_inv Φ Γ e0 γ v2 Hsat H2) as [e2' [He2 Heq]]. subst v2.
    f_equal.
    inversion Hsc as [| | | | | | | L1 e1 γ1 Hsce | | | | |]; subst.
    exact (eval_det_fix Inf Φ Γ e0 e' Heval_e eq_refl e2' Hsat Henv
             (concore_expr_cast e0 γ Hcon) (conj HΓ Hsce) He2).
  - (* Rule App-Abs *)
    pose proof (concore_expr_app_l _ _ Hcon) as Hclos.
    pose proof (concore_expr_app_r _ _ Hcon) as Hea.
    inversion Hsc as [| | | | L0 f0 a0 Hscf Hsca | | | | | | | |]; subst.
    inversion Hscf as [| | | | | | | | | | | | L1 Γ1 e1 HΓ' Hsclam]; subst.
    inversion Hsclam as [| | | | | L2 x2 b2 Hscb | | | | | | |]; subst.
    exact (eval_det_fix Inf Φ (extend_env Γ' x Γ ea) eb eb' Heval_b eq_refl v2 Hsat
             (concrete_env_extend Γ' x Γ ea (concore_expr_thunk_env _ _ Hclos) Henv Hea)
             (concore_expr_lam _ _ (concore_expr_thunk _ _ Hclos))
             (conj (Scoped_Env_Extend x Γ ea Γ' HΓ Hsca HΓ') Hscb)
             (eval_app_clos_inv Φ Γ Γ' x eb ea v2 Hsat H2)).
  - (* Rule App-Spine *)
    pose proof (concore_expr_app_l _ _ Hcon) as Hcf.
    pose proof (concore_expr_app_r _ _ Hcon) as Hca.
    inversion Hsc as [| | | | L0 f0 a0 Hscf Hsca | | | | | | | |]; subst.
    destruct (eval_app_spine_inv Φ Γ ef ea v2 Hsat Hcomp H2)
      as [ef2 [Hef2 Happ2]].
    assert (Heqf : ef' = ef2)
      by exact (eval_det_fix Inf Φ Γ ef ef' Heval_f eq_refl ef2 Hsat Henv Hcf (conj HΓ Hscf) Hef2).
    subst ef2.
    destruct (concore_eval_closed_fix Inf Φ Γ ef ef' Heval_f eq_refl Hsat Henv Hcf (conj HΓ Hscf))
      as [Hcf' Hsf'].
    exact (eval_det_fix Inf Φ Γ (EApp ef' ea) er Heval_app2 eq_refl v2 Hsat Henv
             (Con_App ef' ea Hcf' Hca)
             (conj HΓ (Scoped_App _ _ _ (closed_term_scoped _ _ Hsf') Hsca))
             Happ2).
  - (* Rule Bot *) symmetry. exact (eval_bot_inv Φ Γ b v2 Hsat H2).
  - (* Rule App-Prim *)
    assert (Hcon_args : Forall concore_expr args).
    { destruct (unspool_app_concore (EApp ef ea) [] (EPrimOp p) args Hunspool Hcon
                 (Forall_nil _)) as [_ Hforall]. exact Hforall. }
    assert (Hsc_args : Forall (scoped (dom_env Γ)) args).
    { destruct (unspool_app_scoped _ (EApp ef ea) [] (EPrimOp p) args Hunspool Hsc
                 (Forall_nil _)) as [_ Hforall]. exact Hforall. }
    destruct (eval_app_prim_inv Φ Γ ef ea p args v2 Hsat Hunspool Harity H2)
      as [args2 [Hargs2 Heq]]. subst v2.
    f_equal.
    clear Hunspool Harity Hcon H2 Hsc.
    revert args2 Hargs2 Hcon_args Hsc_args.
    induction Hargs as [| a0 a0' tl tl' Ha0 Htl IH]; intros args2 Hargs2 Hcon_args Hsc_args;
      inversion Hargs2 as [| b0 b0' tl2 tl2' Hb0 Htl2]; subst.
    + reflexivity.
    + inversion Hcon_args as [| c0 ctl Hc0 Hctl]; subst.
      inversion Hsc_args as [| d0 dtl Hd0 Hdtl]; subst.
      f_equal.
      * exact (eval_det_fix Inf Φ Γ a0 a0' Ha0 eq_refl b0' Hsat Henv Hc0 (conj HΓ Hd0) Hb0).
      * exact (IH tl2' Htl2 Hctl Hdtl).
  - (* Rule Lam *) symmetry. exact (eval_lam_inv Φ Γ x e0 v2 Hsat H2).
  - (* Rule App-Cast *)
    pose proof (concore_expr_app_l _ _ Hcon) as Hcast.
    pose proof (concore_expr_app_r _ _ Hcon) as Hea.
    inversion Hsc as [| | | | L0 f0 a0 Hscf Hsca | | | | | | | |]; subst.
    inversion Hscf as [| | | | | | | L1 e1 γ1 Hsce | | | | |]; subst.
    exact (eval_det_fix Inf Φ Γ (ECast (EApp ef (ECast ea (sym_coerc γ_a))) γ_r) er
             Heval_pushed eq_refl v2 Hsat Henv
             (Con_Cast _ γ_r (Con_App _ _ (concore_expr_cast _ _ Hcast)
                                          (Con_Cast _ _ Hea)))
             (conj HΓ (Scoped_Cast _ _ γ_r
                        (Scoped_App _ _ _ Hsce (Scoped_Cast _ _ _ Hsca))))
             (eval_app_cast_arrow_inv Φ Γ ef γ γ_a γ_r ea v2 Hsat Hdecomp H2)).
  - (* Rule App-If: a ConCore expression has no branch at its spine head *)
    exfalso.
    destruct (unspool_app_concore (EApp e1 e2) [] _ args Hunspool_if Hcon (Forall_nil _))
      as [Hhead _].
    exact (not_concore_if ec et ef Hhead).
  - (* Rule App-Bot *) symmetry. exact (eval_app_bot_inv Φ Γ b ea v2 Hsat H2).
  - (* Rule Case *)
    destruct (eval_case_inv Φ Γ es alts v2 Hsat H2) as [es2 [Hes2 Hfold2]].
    assert (Hces : concore_expr es) by exact (concore_expr_case_es es alts Hcon).
    assert (Halts : Forall concore_alt alts) by (inversion Hcon; subst; assumption).
    inversion Hsc as [| | | | | | L0 es1 alts1 Hsc_es Hsc_alts | | | | | |]; subst.
    assert (Heq : es' = es2)
      by exact (eval_det_fix Inf Φ Γ es es' Heval_es eq_refl es2 Hsat Henv Hces
                  (conj HΓ Hsc_es) Hes2).
    subst es2.
    destruct (concore_eval_closed_fix Inf Φ Γ es es' Heval_es eq_refl Hsat Henv Hces
                (conj HΓ Hsc_es)) as [Hcon_es' Hsc_es'].
    rewrite (merge_concore_id Γ es' Hcon_es') in Hfold, Hfold2.
    exact (fold_alts_det_fix Inf Φ Γ es' alts er Hfold eq_refl v2 Hsat Henv Hcon_es'
             Halts HΓ Hsc_es' Hsc_alts Hfold2).
  - (* Rule If: a ConCore expression is never a branch *)
    exfalso. exact (not_concore_if ec et ef Hcon).
  - (* Rule Coercion *) symmetry. exact (eval_coercion_inv Φ Γ γ v2 Hsat H2).
  - (* Rule Prune: the path condition holds *)
    exfalso. rewrite Hsat in Hunsat. discriminate.
  - (* Rule Type *) symmetry. exact (eval_type_inv Φ Γ τ v2 Hsat H2).
  - (* Rule Thunk *)
    inversion Hcon as [| | | | | | | | | | | | | Γ0 e1 Henv' He]; subst.
    inversion Hsc as [| | | | | | | | | | | | L1 Γ1 e1 HΓ' Hsce]; subst.
    exact (eval_det_fix Inf Φ Γ' e0 e' Heval_t eq_refl v2 Hsat Henv' He (conj HΓ' Hsce)
             (eval_thunk_inv Φ Γ Γ' e0 v2 Hsat H2)).
}
{
  destruct Hfold as
    [ kv Φ Γ ec et ef alts et' ef' pc_c Hpc Hfold_t Hfold_f
    | kv Φ Γ ec et ef alts Hpc_none
    | kv Φ Γ e0 d ea xs ep alts er Hdec Halt Heval_ep
    | kv Φ Γ b alts
    | kv Φ Γ e0 pc alts r Hpcg Hvarg Hrec
    | kv Φ Γ e0 pc alts r1' r2' Hpcs Hvars Hars Hf1 Hf2
    | kv Φ Γ e0 alts Hpcnone Hopnone Hnothead Hnoalt Hnotbot
    ]; intros Hk0; subst kv; intros r2 Hsat Henv Hcon Halts HΓ Hsc Hsc_alts H2.
  - exfalso. exact (not_concore_if ec et ef Hcon).
  - exfalso. exact (not_concore_if ec et ef Hcon).
  - (* a constructor alternative matches *)
    assert (Hea : Forall concore_expr ea)
      by exact (decompose_con_app_concore e0 d ea Hdec Hcon).
    assert (Hep : concore_expr ep)
      by exact (find_alt_concore d alts xs ep Halt Halts).
    assert (Hsc_ea : Forall closed_term ea)
      by exact (proj2 (unspool_app_scoped nil e0 [] (ECon d) ea
                        (decompose_con_app_unspool e0 d ea Hdec) Hsc (Forall_nil _))).
    exact (eval_det_fix Inf Φ (extend_env_multi Γ xs ea Γ) ep er Heval_ep eq_refl r2 Hsat
             (concrete_env_extend_multi xs ea Γ Γ Henv Henv Hea) Hep
             (conj (scoped_env_extend_multi xs ea Γ Γ HΓ HΓ
                     (Forall_impl _ (fun a Ha => closed_term_scoped (dom_env Γ) a Ha) Hsc_ea))
                   (eq_ind_r (fun L => scoped L ep)
                      (find_alt_scoped (dom_env Γ) d alts xs ep Hsc_alts Halt)
                      (dom_env_extend_multi xs ea Γ Γ)))
             (fold_alts_con_inv Inf Φ Γ e0 d ea xs ep alts r2 Hdec Halt H2)).
  - (* a bottom scrutinee *) symmetry. exact (fold_alts_bot_inv Inf Φ Γ b alts r2 H2).
  - (* the scrutinee is a boolean formula with no variable *)
    exact (fold_alts_det_fix Inf Φ Γ (ECon (truth_constructor (pc_closed_value pc))) alts r
             Hrec eq_refl r2 Hsat Henv (Con_Con _) Halts HΓ (Scoped_Con nil _) Hsc_alts
             (fold_alts_ground_formula_inv Inf Φ Γ e0 pc alts r2 Hpcg Hvarg H2)).
  - (* a closed scrutinee's formula has no variable, so this clause cannot fire *)
    exfalso.
    rewrite (expr_to_pc_scoped_no_var Γ e0 pc (closed_term_scoped (dom_env Γ) e0 Hsc) Hpcs)
      in Hvars. discriminate Hvars.
  - (* no alternative matches *)
    symmetry.
    exact (fold_alts_otherwise_inv Inf Φ Γ e0 alts r2 Hpcnone
             (is_if_false_of_spine_head e0 Hnothead) Hnoalt Hnotbot H2).
}
Qed.

(** A ConCore program run in a ConCore environment has at most one value. *)
Lemma concore_eval_deterministic : forall Γ e v1 v2,
  concrete_env Γ ->
  concore_expr e ->
  closed_program Γ e ->
  Γ ⊢ᶜ e ⇓ᶜ v1 ->
  Γ ⊢ᶜ e ⇓ᶜ v2 ->
  v1 = v2.
Proof.
  intros Γ e v1 v2 Henv Hcon Hcl H1 H2.
  exact (eval_det_fix Inf pc_true Γ e v1 H1 eq_refl v2 sat_pc_true Henv Hcon Hcl H2).
Qed.

(** A whole program starts in the empty environment, which is ConCore, so
    the program's value is unique outright. *)
Corollary concore_eval_deterministic_top : forall e v1 v2,
  concore_expr e -> closed_term e -> ⊢ᶜ e ⇓ᶜ v1 -> ⊢ᶜ e ⇓ᶜ v2 -> v1 = v2.
Proof.
  intros e v1 v2 Hcon Hcl H1 H2.
  exact (concore_eval_deterministic · e v1 v2 CEnv_Empty Hcon
           (conj Scoped_Env_Empty Hcl) H1 H2).
Qed.

End ConCore.
