From SymCoreTheory Require Import SymCore ConCore.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

(* ==========================================================================
   HISTORY OF THIS FILE - READ THIS FIRST

   This file used to answer a question: can Rule App-Cast-Opaque be deleted
   by demanding, in concore_expr, that a cast in OPERATOR position carries a
   coercion that splits into an arrow?

   It answered no, and the answer stands: that restriction speaks about the
   program as WRITTEN, Rule App-Spine puts the operator's VALUE in operator
   position, and the value comes out of cast_expr, which is abstract. A
   program that passes the restriction can step to one that fails it. Lemmas
   1 to 3 below still show exactly that, unchanged.

   The file then listed three ways out, and the second one was taken:

     put a stronger guard on Rule App-Spine - refuse EVERY cast operator,
     not just an arrow cast. Then an operator that is an opaque cast is
     stuck on the symbolic and the concrete side alike, the two sides stop
     together, and no rule is needed for the shape. That is a change to
     Figure 3, not a deletion from it, and it costs the programs above their
     value.

   Rule App-Spine now reads "is_cast ef = false" and Rule App-Cast-Opaque is
   gone. So the last clause of that sentence has come due, and this file
   pays it. Two of its lemmas flipped:

     LEMMA 5 was only_app_cast_opaque_reduces_the_stepped_program, which
     said Rule App-Cast-Opaque is the only rule that reduces the stepped
     term. It is now stepped_program_has_no_value: NO rule reduces it.

     LEMMA 6 was written_program_has_a_value. It is now
     written_program_has_no_value.

   LEMMA 8 changed shape without changing its meaning. It used to feed this
   program's stepped term to eval_con_app_whnf and observe that every
   hypothesis held. eval_con_app_whnf's guard is now "is_cast fc = false",
   which this operator fails, so the instance no longer exists. The lemma
   now records that.

   Everything else - lemmas 1, 2, 3, 4 and 7 - is unchanged and still true.

   What the file shows now: deleting the rule DOES cost this program its
   value, exactly as the old note predicted, and the cost is paid on both
   sides at once. That is the point. The symbolic side and the concrete side
   are stuck on the same shape, so soundness is not disturbed: it never has
   to replay a step that neither side can take.
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

(* The operator's value. The hypothesis below is about cast_expr, the
   abstract cast simplifier. It says only that cast_expr keeps one cast;
   nothing in SymCore.v or ConCore.v says it may not. *)
Definition kept_cast : expr := ECast (ECon "D") opaque_coercion.

Definition env_with_cast : environment :=
  ExtendEnv "x" (MkClosure · (ECast (ECon "C") opaque_coercion)) ·.

Definition written_program : expr := EApp (EVar "x") (ECon "E").

Definition stepped_program : expr := EApp kept_cast (ECon "E").

Lemma lookup_x :
  lookup_env env_with_cast "x" = Some (·, ECast (ECon "C") opaque_coercion).
Proof. reflexivity. Qed.

(* 1. The written program passes the proposed restriction: its operator is a
      variable, not a cast at all. UNCHANGED. *)
Lemma written_program_passes_the_restriction :
  opaque_cast_operator (EVar "x") = false.
Proof. reflexivity. Qed.

(* 2. The term Rule App-Spine steps to FAILS the proposed restriction: its
      operator is a cast whose coercion does not split into an arrow.
      UNCHANGED. *)
Lemma stepped_program_fails_the_restriction :
  opaque_cast_operator kept_cast = true.
Proof. reflexivity. Qed.

(* 3. Rule App-Spine really does take the first to the second: the written
      operator is not a value, it is not a cast, and it evaluates to the
      cast that fails the restriction. UNCHANGED, except that the guard the
      operator passes is now the plain cast test. *)
Lemma written_operator_is_not_a_value :
  ~ Whnf env_with_cast (EVar "x").
Proof.
  intro H.
  inversion H as [e0 Hsolv | | | | | | | ]; subst; [| no_con_head].
  inversion Hsolv as [| y Hnone | |]; subst.
  simpl in Hnone. discriminate.
Qed.

Lemma written_operator_is_not_a_cast :
  is_cast (EVar "x") = false.
Proof. reflexivity. Qed.

Lemma written_operator_evaluates_to_the_kept_cast :
  cast_expr (ECon "C") opaque_coercion = kept_cast ->
  pc_true ; env_with_cast ⊢ EVar "x" ⇓ kept_cast.
Proof.
  intros Hcast.
  eapply Eval_Var; [exact lookup_x |].
  rewrite <- Hcast.
  apply Eval_Cast. eapply Eval_Con. reflexivity.
Qed.

(* And it evaluates to nothing else. *)
Lemma written_operator_has_only_that_value :
  cast_expr (ECon "C") opaque_coercion = kept_cast ->
  forall v, pc_true ; env_with_cast ⊢ EVar "x" ⇓ v -> v = kept_cast.
Proof.
  intros Hcast v Hv.
  pose proof (eval_var_bound_inv pc_true env_with_cast "x" ·
                (ECast (ECon "C") opaque_coercion) v sat_pc_true lookup_x Hv) as Hcastev.
  destruct (eval_cast_inv pc_true · (ECon "C") opaque_coercion v sat_pc_true Hcastev)
    as [e' [He' Heq]].
  rewrite (eval_con_inv pc_true · "C"%string e' sat_pc_true He') in Heq.
  rewrite Heq. exact Hcast.
Qed.

(* 4. On that stepped term, Rule App-Spine cannot fire: a cast over a value
      is a value - and, since the repair, it could not fire even if the body
      under the cast were not a value. UNCHANGED. *)
Lemma stepped_operator_is_a_value :
  Whnf env_with_cast kept_cast.
Proof. apply Whnf_Cast. eapply Whnf_Con. reflexivity. Qed.

(* 5. FLIPPED. This used to read

       only_app_cast_opaque_reduces_the_stepped_program

     and say that Rule App-Cast-Opaque is the one rule that reduces the
     stepped term. That rule is gone, and no rule replaced it, so the
     stepped term has no value at all. *)
Lemma stepped_program_has_no_value : forall v,
  ~ (env_with_cast ⊢ᶜ stepped_program ⇓ᶜ v).
Proof.
  intros v Heval.
  unfold eval_con, stepped_program, kept_cast in Heval.
  exact (eval_app_cast_opaque_stuck pc_true env_with_cast (ECon "D")
           opaque_coercion (ECon "E") v sat_pc_true opaque_coercion_has_no_arrow
           Heval).
Qed.

(* 6. FLIPPED. This used to read

       written_program_has_a_value

     and evaluate the whole program through Rule App-Cast-Opaque. Every
     derivation had to go through the stepped term, and the stepped term is
     now stuck, so the written program is stuck too. This is the cost of the
     repair, stated as a theorem rather than as a worry. *)
Lemma written_program_has_no_value :
  cast_expr (ECon "C") opaque_coercion = kept_cast ->
  forall v, ~ (env_with_cast ⊢ᶜ written_program ⇓ᶜ v).
Proof.
  intros Hcast v Heval.
  unfold eval_con, written_program in Heval.
  inversion Heval; subst.
  - (* Rule Con: the spine head is a variable, not a constructor *)
    no_con_head.
  - (* Rule App-Spine: the operator's only value is the kept cast, and the
       stepped term has no value *)
    match goal with
    | [ Hop : eval _ pc_true env_with_cast (EVar "x") ?ef',
        Happ : eval _ pc_true env_with_cast (EApp ?ef' (ECon "E")) v |- _ ] =>
        rewrite (written_operator_has_only_that_value Hcast ef' Hop) in Happ;
        exact (stepped_program_has_no_value v Happ)
    end.
  - (* Rule App-Prim: the spine head is a variable, not a primitive *)
    match goal with
    | [ H : unspool_app (EApp (EVar "x") (ECon "E")) [] = _ |- _ ] =>
        simpl in H; injection H as Hh _; discriminate
    end.
  - (* Rule Prune: pc_true is satisfiable *)
    rewrite sat_pc_true in *. discriminate.
Qed.

(* 7. The written program is a ConCore program under the restriction as
      well: every application in it has a non-cast operator. UNCHANGED.
      Note what this means together with lemma 6: the program is admitted by
      every syntactic filter in ConCore.v and still has no value. Being
      stuck is not a well-formedness failure here, it is the semantics
      declining to apply a non-function. *)
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

(* 8. RESHAPED. This used to be

       eval_con_app_whnf_instance_needs_the_rule

     and fed this program's stepped term to eval_con_app_whnf - the step in
     the soundness proof (ConCore.v, section 9.1.4) that replays a concrete
     operator which is already a value - observing that every hypothesis
     held and the conclusion was the term only Rule App-Cast-Opaque
     reduced.

     eval_con_app_whnf's guard is now "is_cast fc = false". This operator is
     a cast, so the instance does not exist any more. And the soundness
     proof never needs it: eval_app_spine_sound proves the concrete operator
     is not a cast before it calls eval_con_app_whnf, from
     contains_is_cast and eval_app_if_false. *)
Lemma eval_con_app_whnf_excludes_this_instance :
  is_cast kept_cast = true.
Proof. reflexivity. Qed.

(* 9. NEW. The soundness case for this program is vacuous, on the nose.
      Soundness assumes the SYMBOLIC side converged. Take the symbolic side
      to be this same program - it mentions no symbolic variable, so it is
      its own concretion - and the assumption cannot be met. There is
      nothing to replay. *)
Lemma the_soundness_case_is_vacuous :
  cast_expr (ECon "C") opaque_coercion = kept_cast ->
  forall v_sym, pc_true ; env_with_cast ⊢ written_program ⇓ v_sym -> False.
Proof.
  intros Hcast v_sym Hsym.
  exact (written_program_has_no_value Hcast v_sym Hsym).
Qed.

(* ==========================================================================
   What this file shows now

   The restriction on operator position is a restriction on written
   programs, and it is not preserved by Rule App-Spine. Lemmas 1, 2 and 3
   exhibit one step from a program that passes the restriction to a term
   that fails it. That part did not change and was never in doubt.

   What changed is the conclusion drawn from it. The old file offered three
   exchanges:

   - delete the rule AND assume a new contract on cast_expr. NOT TAKEN. The
     assumption count is unchanged at 34.

   - delete the rule AND refuse every cast operator in Rule App-Spine.
     TAKEN. Lemmas 5 and 6 are the receipt: this program lost its value.

   - keep the rule. NOT TAKEN.

   The reason the second exchange is sound, and the first is not, is that
   the second moves the guard off the coercion and onto the operator's
   constructor. A test on the coercion can pass symbolically and fail
   concretely, because concretion changes which terms are values. A test on
   the constructor cannot, because concretion does not change a non-cast
   into a cast - contains_is_cast in ConCore.v - unless the term is a
   branch, and an application with a branch in operator position has no
   value anyway - eval_app_if_false. So the two sides stop on the same
   shapes, and soundness never reaches the gap the old rule was patching.

   The restriction on operator position is still worth having on its own -
   it is preserved by evaluation and it needs no new contract, see
   OperatorRestrictionPreservation.v - but it never paid for the rule, and
   it is not what paid for the rule in the end.
   ========================================================================== *)
