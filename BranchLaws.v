From SymCoreTheory Require Import SymCore ConCore.
From Stdlib Require Import Lists.List.
Import ListNotations.

Section BranchLaws.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.

Class ReducePrimBranch : Prop :=
reduce_prim_branch : forall p pre ec et ef post,
  Forall (fun e => is_if e = false) pre ->
  reduce_prim p (pre ++ EIf ec et ef :: post) =
  EIf ec (reduce_prim p (pre ++ et :: post)) (reduce_prim p (pre ++ ef :: post)).

Class CastExprBranch : Prop :=
cast_expr_branch : forall ec et ef γ,
  cast_expr (EIf ec et ef) γ = EIf ec (cast_expr et γ) (cast_expr ef γ).

End BranchLaws.

Inductive SymFCLaws {sorts : SymCoreSorts} {solver : SymCoreSolver} : Prop :=
  symfc_laws : ConCoreLaws -> ReducePrimBranch -> CastExprBranch -> SymFCLaws.

Existing Class SymFCLaws.

#[export] Instance concore_laws_of_symfc_laws `{laws : SymFCLaws} : ConCoreLaws.
Proof. destruct laws; assumption. Qed.
#[export] Instance reduce_prim_branch_of_laws `{laws : SymFCLaws} : ReducePrimBranch.
Proof. destruct laws; assumption. Qed.
#[export] Instance cast_expr_branch_of_laws `{laws : SymFCLaws} : CastExprBranch.
Proof. destruct laws; assumption. Qed.
