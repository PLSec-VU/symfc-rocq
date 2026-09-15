From SymCoreTheory Require Import SymCore ConCore.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

Section Scratch.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver} {laws : ConCoreLaws}.

(* The old refutation, mechanically repaired everywhere the repair is
   possible, so that the ONE step which is now genuinely unavailable stands
   alone.  The three cases where reduce_prim returns a literal, a variable or
   a bare primitive operation still go through: contains is still rigid
   there.  The fourth case - reduce_prim returns a residual primitive
   application, which is what a real reducer returns on a symbolic argument -
   is where the proof dies. *)
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
    apply contains_lit_inv in Hcont. injection Hcont as Hcont. exact Hcont.
  - right. intro l.
    specialize (Hcont (fun _ => l)). simpl in Hcont.
    inversion Hcont; subst; [congruence | kill_denote].
  - right. intro l.
    specialize (Hcont (fun _ => l)). simpl in Hcont.
    apply contains_primop_inv in Hcont. discriminate.
  - right. intro l.
    specialize (Hcont (fun _ => l)). simpl in Hcont.
    (* HERE.  Hcont : contains σ (only x) (EApp f a) (ELit l), and the
       semantic rule Cont_Denote derives exactly that whenever the residual
       application f a has SMT value l.  inversion no longer closes the
       goal. *)
    inversion Hcont.
Abort.

End Scratch.
