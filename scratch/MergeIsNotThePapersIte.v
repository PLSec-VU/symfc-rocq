From SymCoreTheory Require Import SymCore ConCore.
From Stdlib Require Import Strings.String Lists.List Arith.PeanoNat.
Import ListNotations.

Section Scratch.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : ConCoreLaws}.

(* What this file recorded before, and what it records now.

   BEFORE: merge was an axiom, and the development assumed

     merge_fold_alts_equiv :
       fold_alts Inf Phi G (merge e) alts r <-> fold_alts Inf Phi G e alts r.

   This file showed that assumption is false of the merge the paper
   DEFINES (theory.tex, "Merge"), by writing out two of the paper's clauses
   by hand and refuting the assumption for each.

   NOW: merge is that definition (SymCore.v, Section 8.1), so the same two
   refutations are proved about the real function, not about a hand-written
   stand-in. A third refutation is new and is the important one: the
   one-sided repair

     merge_fold_alts_sound :
       fold_alts f Phi G e alts r ->
       exists r', fold_alts f Phi G (merge G e) alts r' and r' covers r

   is false as well. It asks only that the merged scrutinee still folds to
   SOMETHING, and even that fails.

   Which results flipped:
     merge                  axiom   -> definition   (SymCore.v Section 8.1)
     merge_concore          axiom   -> lemma        (ConCore.v Section 8.1)
     merge_contains         axiom   -> lemma        (ConCore.v Section 9.3)
     merge_fold_alts_equiv  axiom   -> refuted here, nothing replaces it
     merge_fold_alts_sound  proposed repair -> refuted here
   One assumption arrived to pay for the second merge clause:
     reduce_prim_ite_contains (ConCore.v Section 9.0), about the SMT
     reducer at op_ite, not about merge. *)

(* ------------------------------------------------------------------ *)
(* 1. The biconditional, refuted twice, against the real merge.        *)
(* ------------------------------------------------------------------ *)

(* If merging turns some branch into a non-branch that still folds, then
   the biconditional cannot hold: fold-alts answers a branch scrutinee with
   a branch (FoldAlts_If) or with undefined (FoldAlts_IfFail), never with
   the merged value. *)
Lemma merge_nonif_refutes :
  forall (G : environment) (ec et ef r : expr) (pc : path_condition) (alts : list alt),
    expr_to_pc G ec = Some pc ->
    fold_alts Inf (PCVar "p") G (merge G (EIf ec et ef)) alts r ->
    is_if r = false ->
    ~ (forall Phi G0 e a r', fold_alts Inf Phi G0 (merge G0 e) a r'
                             <-> fold_alts Inf Phi G0 e a r').
Proof.
  intros G ec et ef r pc alts Hpc Hfold Hnotif Hax.
  apply (Hax (PCVar "p") G (EIf ec et ef) alts r) in Hfold.
  inversion Hfold; subst.
  - simpl in Hnotif. discriminate.
  - rewrite Hpc in *. discriminate.
  - unfold decompose_con_app in *. simpl in *. discriminate.
  - simpl in Hnotif. discriminate.
Qed.

(* The paper's first clause: a shared constructor head is kept and the
   branch is pushed into the arguments pointwise. *)
Definition shared_con_scrutinee : expr := EIf (EVar "x") (ECon "D") (ECon "D").
Definition one_alt : list alt := [Alt "D" [] (ECon "E")].

Lemma merged_scrutinee : merge EmptyEnv shared_con_scrutinee = ECon "D".
Proof. reflexivity. Qed.

(* Merged, the alternative is reduced once and the answer is its body. *)
Lemma merged_fold :
  fold_alts Inf (PCVar "p") EmptyEnv (merge EmptyEnv shared_con_scrutinee)
            one_alt (ECon "E").
Proof.
  rewrite merged_scrutinee.
  eapply FoldAlts_Con with (d := "D") (ea := []) (xs := []) (ep := ECon "E").
  - reflexivity.
  - reflexivity.
  - eapply Eval_Con with (d := "E") (args := []). reflexivity.
Qed.

(* Unmerged, the same fold answers EIf x (ECon "E") (ECon "E"). *)
Lemma unmerged_fold :
  fold_alts Inf (PCVar "p") EmptyEnv shared_con_scrutinee one_alt
            (EIf (EVar "x") (ECon "E") (ECon "E")).
Proof.
  eapply FoldAlts_If with (pc_c := PCVar "x"); try reflexivity;
    (eapply FoldAlts_Con with (d := "D") (ea := []) (xs := []) (ep := ECon "E");
     [ reflexivity | reflexivity | eapply Eval_Con with (d := "E") (args := []); reflexivity ]).
Qed.

Lemma con_clause_refutes_merge_fold_alts_equiv :
  ~ (forall Phi G0 e a r', fold_alts Inf Phi G0 (merge G0 e) a r'
                           <-> fold_alts Inf Phi G0 e a r').
Proof.
  eapply merge_nonif_refutes
    with (G := EmptyEnv) (ec := EVar "x") (et := ECon "D") (ef := ECon "D")
         (pc := PCVar "x") (r := ECon "E") (alts := one_alt).
  - reflexivity.
  - exact merged_fold.
  - reflexivity.
Qed.

(* The same refutation for the paper's identical-bottoms clause. *)
Lemma bot_clause_refutes_merge_fold_alts_equiv :
  ~ (forall Phi G0 e a r', fold_alts Inf Phi G0 (merge G0 e) a r'
                           <-> fold_alts Inf Phi G0 e a r').
Proof.
  eapply merge_nonif_refutes
    with (G := EmptyEnv) (ec := EVar "x")
         (et := EBot BUndefined) (ef := EBot BUndefined)
         (pc := PCVar "x") (r := EBot BUndefined) (alts := []).
  - reflexivity.
  - simpl. apply FoldAlts_Bot.
  - reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The one-sided repair is false too.                               *)
(* ------------------------------------------------------------------ *)

(* Why it fails. Rule FoldAlts_If tests its guard with expr_to_pc BEFORE the
   guard is evaluated. Rule If tests the guard's VALUE. Merging a
   constructor spine moves the guard out of fold-alts and into the
   environment, where the next thing that reads it is Rule If. So a guard
   fold-alts accepts can be a guard evaluation is stuck on, and then the
   merged scrutinee has no fold at all.

   The guard below is such a guard. It is a saturated-looking application of
   op_ite to one argument. expr_to_pc reads it happily, because expr_to_pc
   never checks arity. Rule App-Prim refuses it, because op_ite takes three
   arguments and this one has one. Every other rule refuses it too: Rule
   App-Spine refuses a head that is already a value, and a primitive
   operation is one. *)

Definition cxEc : expr := EApp (EPrimOp op_ite) (EVar "x").
Definition cxEt : expr := EApp (ECon "D") (ECon "E").
Definition cxEf : expr := EApp (ECon "D") (ECon "F").
Definition cxAlts : list alt := [Alt "D" ["y"] (EVar "y")].
Definition cxScrut : expr := EIf cxEc cxEt cxEf.

Lemma cx_pc : expr_to_pc EmptyEnv cxEc = Some (PCPrim op_ite [PCVar "x"]).
Proof. reflexivity. Qed.

Lemma cx_merged :
  merge EmptyEnv cxScrut = EApp (ECon "D") (EIf cxEc (ECon "E") (ECon "F")).
Proof. reflexivity. Qed.

Lemma cx_unmerged_folds :
  fold_alts Inf pc_true EmptyEnv cxScrut cxAlts (EIf cxEc (ECon "E") (ECon "F")).
Proof.
  eapply FoldAlts_If with (pc_c := PCPrim op_ite [PCVar "x"]).
  - exact cx_pc.
  - eapply FoldAlts_Con with (d := "D") (ea := [ECon "E"]) (xs := ["y"]) (ep := EVar "y").
    + reflexivity.
    + reflexivity.
    + eapply Eval_Var; [reflexivity |].
      eapply Eval_Con with (d := "E") (args := []). reflexivity.
  - eapply FoldAlts_Con with (d := "D") (ea := [ECon "F"]) (xs := ["y"]) (ep := EVar "y").
    + reflexivity.
    + reflexivity.
    + eapply Eval_Var; [reflexivity |].
      eapply Eval_Con with (d := "F") (args := []). reflexivity.
Qed.

Lemma cx_guard_stuck : forall Phi G v, sat Phi = true -> eval Inf Phi G cxEc v -> False.
Proof.
  intros Phi G v Hsat H. unfold cxEc in H.
  inversion H; subst.
  - simpl in *; discriminate.
  - match goal with [ Hc : Comp _ _ |- _ ] => inversion Hc end.
  - match goal with [ Hu : unspool_app _ _ = (EPrimOp _, _) |- _ ] =>
      simpl in Hu; injection Hu as Hp Ha; subst end.
    match goal with [ Hl : length _ = primop_arity _ |- _ ] =>
      simpl in Hl; rewrite op_ite_arity in Hl; discriminate end.
  - match goal with [ Hu : unspool_app _ _ = (EIf _ _ _, _) |- _ ] =>
      simpl in Hu; discriminate Hu end.
  - congruence.
Qed.

Lemma cx_merged_stuck : forall r',
  fold_alts Inf pc_true EmptyEnv (merge EmptyEnv cxScrut) cxAlts r' -> False.
Proof.
  intros r' Hf. rewrite cx_merged in Hf.
  inversion Hf; subst.
  - (* FoldAlts_Con: the only rule that can fire *)
    match goal with [ Hd : decompose_con_app _ = Some _ |- _ ] =>
      unfold decompose_con_app in Hd; simpl in Hd; injection Hd as Hd1 Hd2; subst end.
    match goal with [ Ha : find_alt _ _ = Some _ |- _ ] =>
      simpl in Ha; injection Ha as Ha1 Ha2; subst end.
    match goal with [ He : eval _ _ _ (EVar "y") _ |- _ ] => rename He into Hev end.
    simpl in Hev.
    inversion Hev; subst.
    + match goal with [ Hlk : lookup_env _ "y" = Some _ |- _ ] =>
        simpl in Hlk; injection Hlk as Hl1 Hl2; subst end.
      match goal with [ Hi : eval _ _ _ (EIf _ _ _) _ |- _ ] => rename Hi into Hif end.
      inversion Hif; subst.
      * simpl in *; discriminate.
      * match goal with [ Hg : eval _ _ _ cxEc _ |- _ ] =>
          exact (cx_guard_stuck _ _ _ sat_pc_true Hg) end.
      * rewrite sat_pc_true in *; discriminate.
    + simpl in *; discriminate.
    + simpl in *; discriminate.
    + rewrite sat_pc_true in *; discriminate.
  - (* FoldAlts_Otherwise: blocked, the alternative for D exists *)
    match goal with [ Hn : match decompose_con_app _ with _ => _ end |- _ ] =>
      simpl in Hn; discriminate Hn end.
Qed.

Lemma merge_fold_alts_sound_is_false :
  ~ (forall f Phi G e alts r,
       fold_alts f Phi G e alts r ->
       exists r', fold_alts f Phi G (merge G e) alts r'
               /\ forall sg S v, contains sg S r v -> contains sg S r' v).
Proof.
  intros Hax.
  destruct (Hax Inf pc_true EmptyEnv cxScrut cxAlts _ cx_unmerged_folds) as [r' [Hf _]].
  exact (cx_merged_stuck r' Hf).
Qed.

(* The same counterexample kills the biconditional a third time, and this
   time without leaning on any clause being "nicer" than a branch: the
   merged scrutinee simply has no fold. *)
Lemma merge_fold_alts_equiv_is_false :
  ~ (forall Phi G e a r', fold_alts Inf Phi G (merge G e) a r'
                          <-> fold_alts Inf Phi G e a r').
Proof.
  intros Hax.
  pose proof cx_unmerged_folds as Hu.
  apply (Hax pc_true EmptyEnv cxScrut cxAlts (EIf cxEc (ECon "E") (ECon "F"))) in Hu.
  exact (cx_merged_stuck _ Hu).
Qed.

Print Assumptions con_clause_refutes_merge_fold_alts_equiv.
Print Assumptions bot_clause_refutes_merge_fold_alts_equiv.
Print Assumptions merge_fold_alts_sound_is_false.
Print Assumptions merge_fold_alts_equiv_is_false.

End Scratch.
