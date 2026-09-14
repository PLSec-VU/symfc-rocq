From SymCoreTheory Require Import SymCore ConCore.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

(* ==========================================================================
   Can Rule App-Cast-Opaque be deleted by demanding, in concore_expr, that a
   cast in OPERATOR position carries an arrow coercion?

   The proposed restriction is this test on the operator of an application:
   an operator that is a cast must carry a coercion that splits into an
   arrow, so that Rule App-Cast owns it.

   This file answers no, and says why. The restriction speaks about the
   operator of the program that is WRITTEN. Rule App-Spine replaces that
   operator by its value, and the value is produced by cast_expr, which is
   abstract. A program that passes the restriction can therefore step to one
   that fails it, and the term it steps to is exactly the shape that only
   Rule App-Cast-Opaque reduces.
   ========================================================================== *)

Definition opaque_cast_operator (e : expr) : bool :=
  match e with
  | ECast _ γ =>
      match decomp_coerc_arrow γ with
      | Some _ => false
      | None => true
      end
  | _ => false
  end.

(* A coercion between two type variables: it does not split into an arrow,
   so Rule App-Cast does not own an operator that carries it. *)
Definition opaque_coercion : coercion :=
  MkCoercion (TyVar "a") (TyVar "a") RoleNominal.

Lemma opaque_coercion_has_no_arrow :
  decomp_coerc_arrow opaque_coercion = None.
Proof. reflexivity. Qed.

(* The operator's value. The two hypotheses below are about cast_expr, the
   abstract cast simplifier. They say only that it keeps one cast and turns
   another into an undefined value; nothing in SymCore.v or ConCore.v says
   it may not. *)
Definition kept_cast : expr := ECast (ECon "D") opaque_coercion.

Definition env_with_cast : environment :=
  ExtendEnv "x" (MkClosure · (ECast (ECon "C") opaque_coercion)) ·.

Definition written_program : expr := EApp (EVar "x") (ECon "E").

Definition stepped_program : expr := EApp kept_cast (ECon "E").

(* 1. The written program passes the proposed restriction: its operator is a
      variable, not a cast at all. *)
Lemma written_program_passes_the_restriction :
  opaque_cast_operator (EVar "x") = false.
Proof. reflexivity. Qed.

(* 2. The term Rule App-Spine steps to FAILS the proposed restriction: its
      operator is a cast whose coercion does not split into an arrow. *)
Lemma stepped_program_fails_the_restriction :
  opaque_cast_operator kept_cast = true.
Proof. reflexivity. Qed.

(* 3. Rule App-Spine really does take the first to the second: the written
      operator is not a value, it is not an arrow cast, and it evaluates to
      the cast that fails the restriction. *)
Lemma written_operator_is_not_a_value :
  ~ Whnf env_with_cast (EVar "x").
Proof.
  intro H.
  inversion H as [e0 Hsolv | | | | | | | ]; subst.
  inversion Hsolv as [| y Hnone | |]; subst.
  simpl in Hnone. discriminate.
Qed.

Lemma written_operator_is_not_an_arrow_cast :
  cast_arrow_operator (EVar "x") = false.
Proof. reflexivity. Qed.

Lemma written_operator_evaluates_to_the_kept_cast :
  cast_expr (ECon "C") opaque_coercion = kept_cast ->
  pc_true ; env_with_cast ⊢ EVar "x" ⇓ kept_cast.
Proof.
  intros Hcast.
  eapply Eval_Var; [reflexivity |].
  rewrite <- Hcast.
  apply Eval_Cast. apply Eval_Con.
Qed.

(* 4. On that stepped term, Rule App-Spine cannot fire: a cast over a value
      is a value. *)
Lemma stepped_operator_is_a_value :
  Whnf env_with_cast kept_cast.
Proof. apply Whnf_Cast. apply Whnf_Con. Qed.

(* 5. And Rule App-Cast-Opaque is the ONLY rule that reduces the stepped
      term. This is eval_app_cast_opaque_inv from ConCore.v, section 12.4,
      instantiated here. Delete the rule and the stepped term is stuck. *)
Lemma only_app_cast_opaque_reduces_the_stepped_program : forall v,
  pc_true ; env_with_cast ⊢ stepped_program ⇓ v ->
  exists eb',
    pc_true ; env_with_cast ⊢ ECon "D" ⇓ eb' /\
    pc_true ; env_with_cast ⊢ EApp (cast_expr eb' opaque_coercion) (ECon "E") ⇓ v.
Proof.
  intros v Heval.
  apply eval_app_cast_opaque_inv;
    [exact sat_pc_true | reflexivity | apply Whnf_Con | exact Heval].
Qed.

(* 6. The written program has a value today, and every derivation of it goes
      through the stepped term. So deleting Rule App-Cast-Opaque takes the
      value away from a program that the proposed restriction ADMITS. *)
Lemma written_program_has_a_value :
  cast_expr (ECon "C") opaque_coercion = kept_cast ->
  cast_expr (ECon "D") opaque_coercion = EBot BUndefined ->
  env_with_cast ⊢ᶜ written_program ⇓ᶜ EBot BUndefined.
Proof.
  intros Hcast1 Hcast2.
  unfold eval_con, written_program.
  eapply Eval_AppSpine.
  - exact written_operator_is_not_a_value.
  - exact written_operator_is_not_an_arrow_cast.
  - exact (written_operator_evaluates_to_the_kept_cast Hcast1).
  - unfold kept_cast.
    eapply Eval_AppCastOpaque.
    + exact opaque_coercion_has_no_arrow.
    + apply Whnf_Con.
    + apply Eval_Con.
    + rewrite Hcast2. apply Eval_AppBot.
Qed.

(* 7. The written program is a ConCore program under the restriction as
      well: every application in it has a non-cast operator. *)
Lemma written_program_is_concore : concore_expr written_program.
Proof.
  unfold written_program. apply Con_App; [apply Con_Var | apply Con_Con].
Qed.

Lemma env_with_cast_is_concrete : concrete_env env_with_cast.
Proof.
  unfold env_with_cast.
  apply CEnv_Extend; [| apply CEnv_Empty | apply CEnv_Empty].
  apply Con_Cast. apply Con_Con.
Qed.

(* 8. The soundness proof reaches this exact instance. eval_con_app_whnf
      (ConCore.v, section 9.1.4) is the step that replays, on the concrete
      side, an operator that is already a value. Every one of its
      hypotheses holds here, and its conclusion is the stepped term of
      lemma 5 - the one only Rule App-Cast-Opaque reduces. *)
Lemma eval_con_app_whnf_instance_needs_the_rule :
  cast_expr (ECon "D") opaque_coercion = EBot BUndefined ->
  concore_expr kept_cast
  /\ Whnf env_with_cast kept_cast
  /\ is_op_app kept_cast = false
  /\ cast_arrow_operator kept_cast = false
  /\ pc_true ; env_with_cast ⊢ kept_cast ⇓ EBot BUndefined
  /\ pc_true ; env_with_cast ⊢ EApp (EBot BUndefined) (ECon "E") ⇓ EBot BUndefined
  /\ pc_true ; env_with_cast ⊢ stepped_program ⇓ EBot BUndefined.
Proof.
  intros Hcast2.
  repeat split.
  - apply Con_Cast. apply Con_Con.
  - exact stepped_operator_is_a_value.
  - unfold kept_cast. rewrite <- Hcast2. apply Eval_Cast. apply Eval_Con.
  - apply Eval_AppBot.
  - unfold stepped_program, kept_cast.
    eapply Eval_AppCastOpaque.
    + exact opaque_coercion_has_no_arrow.
    + apply Whnf_Con.
    + apply Eval_Con.
    + rewrite Hcast2. apply Eval_AppBot.
Qed.

(* ==========================================================================
   What this file shows

   The restriction on operator position is a restriction on written
   programs. It is not preserved by Rule App-Spine, because App-Spine puts
   the operator's VALUE in operator position and that value comes out of
   cast_expr. Lemmas 1, 2 and 3 exhibit one step from a program that passes
   the restriction to a term that fails it; lemmas 4 and 5 show that only
   Rule App-Cast-Opaque reduces that term; lemma 6 evaluates the whole
   program through it.

   Note what the two hypotheses on cast_expr are doing. They are the only
   thing that makes the step above possible, and no contract in SymCore.v or
   ConCore.v rules them out. So the exchange on offer is not "delete a rule,
   gain a restriction". It is:

   - delete the rule AND assume a new contract on cast_expr - that its
     result is never a cast with a coercion that fails to split, or that
     casting a value yields something applicable. That is trading the rule
     for an assumption, which is what the exercise set out to avoid; or

   - delete the rule AND put a stronger guard on Rule App-Spine: refuse
     EVERY cast operator, not just an arrow cast. Then an operator that is
     an opaque cast is stuck on the symbolic and the concrete side alike,
     the two sides stop together, and no rule is needed for the shape. That
     is a change to Figure 3, not a deletion from it, and it costs the
     programs above their value; or

   - keep the rule.

   The restriction on operator position is still worth having on its own -
   it is preserved by evaluation and it needs no new contract, see
   OperatorRestrictionPreservation.v - but it does not pay for the rule.
   ========================================================================== *)
