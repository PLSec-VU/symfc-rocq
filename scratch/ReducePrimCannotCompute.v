From SymCoreTheory Require Import SymCore ConCore.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

(* If reduce_prim COMPUTES -- returns a literal when given a literal --
   then it is either a constant function or the identity.  A real
   primitive (negation, increment, addition) is neither. *)
Theorem reduce_prim_cannot_compute : forall p g,
  (forall l, reduce_prim p [ELit l] = ELit (g l)) ->
  (exists l0, forall l, g l = l0) \/ (forall l, g l = l).
Proof.
  intros p g Hg.
  set (x := "x"%string).
  assert (HsolvV : Solvable · (EVar x)) by (apply Solvable_Var; reflexivity).
  assert (HsolvR : Solvable · (reduce_prim p [EVar x]))
    by (apply reduce_prim_solvable; constructor; [exact HsolvV | constructor]).
  assert (Hcont : forall σ : valuation,
            contains σ (only x) (reduce_prim p [EVar x]) (ELit (g (σ x)))).
  { intro σ. rewrite <- Hg. apply reduce_prim_contains.
    constructor; [| constructor]. apply Cont_Var_Sym. apply only_self. }
  destruct HsolvR as [l0 | y Hy | p0 | f a Hop Hf Ha].
  - left. exists l0. intro l.
    specialize (Hcont (fun _ => l)). simpl in Hcont.
    inversion Hcont; subst. reflexivity.
  - right. intro l.
    specialize (Hcont (fun _ => l)). simpl in Hcont.
    inversion Hcont; congruence.
  - right. intro l.
    specialize (Hcont (fun _ => l)). simpl in Hcont.
    inversion Hcont.
  - right. intro l.
    specialize (Hcont (fun _ => l)). simpl in Hcont.
    inversion Hcont.
Qed.
