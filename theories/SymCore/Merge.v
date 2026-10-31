From SymCoreTheory Require Import SymCore.Syntax SymCore.Solver.
From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.

Section SymCore.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.

Fixpoint zip_tif (p : prim) (ts1 ts2 : list thunk) : list thunk :=
  match ts1, ts2 with
  | t1 :: r1, t2 :: r2 => TIf p t1 t2 :: zip_tif p r1 r2
  | _, _ => []
  end.

Definition same_shape {A : Type} (l1 l2 : list A) : bool :=
  Nat.eqb (length l1) (length l2).

Definition same_coerc_ends (γ1 γ2 : coercion) : bool :=
  dec_eqb type_fc_eq_dec (coerc_src γ1) (coerc_src γ2) &&
  dec_eqb type_fc_eq_dec (coerc_dst γ1) (coerc_dst γ2).

Definition ite_leaf (p : prim) (vt vf : value) : value :=
  match vt, vf with
  | VCon d1 ts1, VCon d2 ts2 =>
      if String.eqb d1 d2 && same_shape ts1 ts2
      then VCon d1 (zip_tif p ts1 ts2)
      else VIf p vt vf
  | VPartial o1 ts1, VPartial o2 ts2 =>
      if dec_eqb primop_eq_dec o1 o2 && same_shape ts1 ts2
      then VPartial o1 (zip_tif p ts1 ts2)
      else VIf p vt vf
  | VPrim a, VPrim b => VPrim (PApp op_ite [p; a; b])
  | VBot b1, VBot b2 => if bottom_eqb b1 b2 then VBot b1 else VIf p vt vf
  | VType τ1, VType τ2 =>
      if dec_eqb type_fc_eq_dec τ1 τ2 then VType τ1 else VIf p vt vf
  | VCoercion γ1, VCoercion γ2 =>
      if dec_eqb coercion_eq_dec γ1 γ2 then VCoercion γ1 else VIf p vt vf
  | _, _ => VIf p vt vf
  end.

Fixpoint ite (p : prim) (vt vf : value) {struct vt} : value :=
  match vt, vf with
  | VCast v1 γ1, VCast v2 γ2 =>
      if same_coerc_ends γ1 γ2 then VCast (ite p v1 v2) γ1 else VIf p vt vf
  | _, _ => ite_leaf p vt vf
  end.

Definition merge (v : value) : value :=
  match v with
  | VIf p vt vf => ite p vt vf
  | _ => v
  end.

Fixpoint lift_prim_from (op : primop) (collected : list prim) (vs : list value)
  {struct vs} : value :=
  match vs with
  | [] => reduce_prim op collected
  | v :: rest =>
      (fix lift_head (v : value) : value :=
         match v with
         | VBot b => VBot b
         | VIf p a b => ite p (lift_head a) (lift_head b)
         | VPrim q => lift_prim_from op (collected ++ [q]) rest
         | _ => VBot BUndefined
         end) v
  end.

Definition lift_prim (op : primop) (vs : list value) : value :=
  lift_prim_from op [] vs.

Section Tests.
Variables (p s : prim) (d : dcon) (t1 t2 : thunk) (Γ : env) (x : var) (b : expr).
Variables (op : primop) (y : prim).

Lemma ite_con_merges : ite p (VCon d [t1]) (VCon d [t2]) = VCon d [TIf p t1 t2].
Proof.
  unfold ite, ite_leaf, same_shape. simpl. rewrite String.eqb_refl. reflexivity.
Qed.

Lemma ite_clos_stays :
  ite p (VClos Γ x b) (VClos Γ x b) = VIf p (VClos Γ x b) (VClos Γ x b).
Proof. reflexivity. Qed.

Lemma lift_prim_bottom_leaf :
  lift_prim op [VIf s (VBot BUndefined) (VPrim y)]
  = ite s (VBot BUndefined) (reduce_prim op [y]).
Proof. reflexivity. Qed.
End Tests.

End SymCore.
