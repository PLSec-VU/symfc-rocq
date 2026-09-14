From SymCoreTheory Require Import SymCore.
From Stdlib Require Import Strings.String Lists.List Arith.PeanoNat.
Import ListNotations.

(* The paper (theory.tex, "Merge") defines ite(Γ, ec, et, ef) by cases. Every
   case except the last one turns a branch into a value with a resolved head:
   a constructor spine, a lambda, a cast, a bottom, a type or a coercion.

   The axiom merge_fold_alts_equiv says fold_alts reaches exactly the same
   results before and after merging. The two cannot both hold. fold_alts
   answers a branch scrutinee with a branch (FoldAlts_If) or with undefined
   (FoldAlts_IfFail); it can never answer it with the merged value. *)

Lemma merge_nonif_refutes :
  forall (m : expr -> expr) (ec et ef r : expr) (pc : path_condition) (alts : list alt),
    expr_to_pc EmptyEnv ec = Some pc ->
    fold_alts Inf (PCVar "p") EmptyEnv (m (EIf ec et ef)) alts r ->
    is_if r = false ->
    ~ (forall Phi G e a r', fold_alts Inf Phi G (m e) a r'
                            <-> fold_alts Inf Phi G e a r').
Proof.
  intros m ec et ef r pc alts Hpc Hfold Hnotif Hax.
  apply (Hax (PCVar "p") EmptyEnv (EIf ec et ef) alts r) in Hfold.
  inversion Hfold; subst.
  - simpl in Hnotif. discriminate.
  - rewrite Hpc in *. discriminate.
  - unfold decompose_con_app in *. simpl in *. discriminate.
  - simpl in Hnotif. discriminate.
Qed.

(* The paper's first case, written out: a shared constructor head is kept and
   the branch is pushed into the arguments pointwise. *)

Fixpoint zip_if (ec : expr) (l1 l2 : list expr) : list expr :=
  match l1, l2 with
  | a1 :: t1, a2 :: t2 => EIf ec a1 a2 :: zip_if ec t1 t2
  | _, _ => nil
  end.

Definition merge_con_clause (e : expr) : expr :=
  match e with
  | EIf ec et ef =>
      match decompose_con_app et, decompose_con_app ef with
      | Some (d1, a1), Some (d2, a2) =>
          if andb (String.eqb d1 d2) (Nat.eqb (length a1) (length a2))
          then make_con_app d1 (zip_if ec a1 a2)
          else e
      | _, _ => e
      end
  | _ => e
  end.

Definition shared_con_scrutinee : expr := EIf (EVar "x") (ECon "D") (ECon "D").
Definition one_alt : list alt := [Alt "D" [] (ECon "E")].

Lemma merged_scrutinee : merge_con_clause shared_con_scrutinee = ECon "D".
Proof. reflexivity. Qed.

(* Merged, the alternative is reduced once and the answer is its body. *)
Lemma merged_fold :
  fold_alts Inf (PCVar "p") EmptyEnv (merge_con_clause shared_con_scrutinee)
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
  ~ (forall Phi G e a r', fold_alts Inf Phi G (merge_con_clause e) a r'
                          <-> fold_alts Inf Phi G e a r').
Proof.
  eapply merge_nonif_refutes
    with (ec := EVar "x") (et := ECon "D") (ef := ECon "D")
         (pc := PCVar "x") (r := ECon "E") (alts := one_alt).
  - reflexivity.
  - exact merged_fold.
  - reflexivity.
Qed.

(* The same refutation for the paper's identical-bottoms case. *)
Definition merge_bot_clause (e : expr) : expr :=
  match e with
  | EIf _ (EBot BUndefined) (EBot BUndefined) => EBot BUndefined
  | _ => e
  end.

Lemma bot_clause_refutes_merge_fold_alts_equiv :
  ~ (forall Phi G e a r', fold_alts Inf Phi G (merge_bot_clause e) a r'
                          <-> fold_alts Inf Phi G e a r').
Proof.
  eapply merge_nonif_refutes
    with (ec := EVar "x") (et := EBot BUndefined) (ef := EBot BUndefined)
         (pc := PCVar "x") (r := EBot BUndefined) (alts := []).
  - reflexivity.
  - simpl. apply FoldAlts_Bot.
  - reflexivity.
Qed.

Print Assumptions con_clause_refutes_merge_fold_alts_equiv.
Print Assumptions bot_clause_refutes_merge_fold_alts_equiv.
