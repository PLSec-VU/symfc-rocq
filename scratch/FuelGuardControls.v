(* Controls for the fuel index on eval/fold_alts.

   Three questions, each answered by something Coq checks rather than by a
   comment:

   1. Does the guard checker accept a mutually recursive fixpoint over
      eval/fold_alts now that the recursive premises sit at (dec f), with no
      "k0 = Inf" crutch to lean on?
   2. Is Rule Out-Of-Fuel reachable at Fin 0, and unreachable at Inf?
   3. Is the guard checker actually running on these fixpoints, or is it
      waving them through?

   Question 1 used to be answered here by a throwaway copy of the pair. The
   copy is gone because the answer graduated: concore_eval_closed_fix and
   concore_fold_closed_fix in ConCore.v ARE that pair, fuel-polymorphic and
   crutch-free, and they are part of the development rather than a sample of
   it. Part A below just prints what they rest on. *)
Require Import SymCoreTheory.SymCore.
Require Import SymCoreTheory.ConCore.
Require Import Coq.Lists.List.
Import ListNotations.

(** Part A: the fuel-polymorphic pair. It takes the fuel as a parameter, asks
    nothing of it, recurses at (dec k) in every case, and the guard checker
    accepts it - which is what ConCore.v compiling at all already says. The
    listing below shows it adds no assumption of its own. *)
Print Assumptions concore_eval_closed_fix.

(** Part B: Fin 0 really does carry an out-of-fuel derivation, and Inf does not
    admit one, so "eval Inf" is the old relation unchanged. *)
Example out_of_fuel_reachable : forall l,
  eval (Fin 0) pc_true · (ELit l) (EBot BUndefined).
Proof. intros l. apply Eval_OutOfFuel. Qed.

Example dec_Inf_is_Inf : dec Inf = Inf.
Proof. reflexivity. Qed.

Example inf_prunes_out_of_fuel : forall Γ l v,
  eval Inf pc_true Γ (ELit l) v -> v = ELit l.
Proof.
  intros Γ l v H.
  (* one goal from Eval_Lit and one from Eval_Prune; the out-of-fuel case is
     dropped by inversion because Fin 0 cannot unify with Inf *)
  inversion H; subst.
  - reflexivity.
  - rewrite sat_pc_true in H0. discriminate.
Qed.

(** Part C: control. The same shape, but recursing on a NON-subterm, is
    rejected - so the acceptance in Part A is a real guard-checker
    acceptance. *)
Fail Fixpoint guard_control (k0 : fuel) (Φ : path_condition) (Γ : environment)
  (e v : expr) (Heval : eval k0 Φ Γ e v) {struct Heval} :
  sat Φ = true -> concrete_env Γ -> concore_expr e -> concore_expr v :=
  fun Hsat Henv Hcon => guard_control k0 Φ Γ e v Heval Hsat Henv Hcon.
