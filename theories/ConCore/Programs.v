From SymCoreTheory Require Export SymCore.Budget.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

Section ConCore.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.

Inductive concore_expr : expr -> Prop :=
  | Concore_Var : forall x, concore_expr (EVar x)
  | Concore_Lit : forall l, concore_expr (ELit l)
  | Concore_PrimOp : forall op, concore_expr (EPrimOp op)
  | Concore_Con : forall d, concore_expr (ECon d)
  | Concore_App : forall ef ea,
      concore_expr ef -> concore_expr ea -> concore_expr (EApp ef ea)
  | Concore_Lam : forall x b, concore_expr b -> concore_expr (ELam x b)
  | Concore_Case : forall es alts,
      concore_expr es -> Forall concore_alt alts -> concore_expr (ECase es alts)
  | Concore_Cast : forall e γ, concore_expr e -> concore_expr (ECast e γ)
  | Concore_Coercion : forall γ, concore_expr (ECoercion γ)
  | Concore_Type : forall τ, concore_expr (EType τ)
  | Concore_Bot : forall b, concore_bottom b -> concore_expr (EBot b)

with concore_bottom : bottom -> Prop :=
  | Concore_Raise : forall e, concore_expr e -> concore_bottom (BRaise e)
  | Concore_Undefined : concore_bottom BUndefined

with concore_alt : alt -> Prop :=
  | Concore_Alt : forall d xs e, concore_expr e -> concore_alt (Alt d xs e).

Inductive concrete_value : value -> Prop :=
  | Concrete_Lit : forall l, concrete_value (VPrim (PLit l))
  | Concrete_Clos : forall Γ x b,
      concrete_env Γ -> concore_expr b -> concrete_value (VClos Γ x b)
  | Concrete_Con : forall d ts,
      Forall concrete_thunk ts -> concrete_value (VCon d ts)
  | Concrete_Partial : forall op ts,
      Forall concrete_thunk ts -> concrete_value (VPartial op ts)
  | Concrete_Type : forall τ, concrete_value (VType τ)
  | Concrete_Coercion : forall γ, concrete_value (VCoercion γ)
  | Concrete_Cast : forall v γ, concrete_value v -> concrete_value (VCast v γ)
  | Concrete_Bot : forall b, concore_bottom b -> concrete_value (VBot b)

with concrete_thunk : thunk -> Prop :=
  | Concrete_Susp : forall Γ e,
      concrete_env Γ -> concore_expr e -> concrete_thunk (TSusp Γ e)

with concrete_env : env -> Prop :=
  | Concrete_Empty : concrete_env EmptyEnv
  | Concrete_Extend : forall x t Γ,
      concrete_thunk t -> concrete_env Γ -> concrete_env (ExtendEnv x t Γ).

Lemma concrete_lookup : forall Γ x t,
  concrete_env Γ -> lookup_env Γ x = Some t -> concrete_thunk t.
Proof.
  intros Γ x t HΓ. induction HΓ as [| y t' Γ' Ht' _ IH]; simpl; intros Hlook.
  - discriminate.
  - destruct (string_dec x y); [injection Hlook as <-; exact Ht' | exact (IH Hlook)].
Qed.

Lemma concrete_missing_field : concrete_thunk missing_field.
Proof.
  repeat constructor.
Qed.

Lemma concrete_bind_fields : forall Γ xs ts,
  concrete_env Γ -> Forall concrete_thunk ts -> concrete_env (bind_fields Γ xs ts).
Proof.
  intros Γ xs. induction xs as [| x xs IH]; intros ts HΓ Hts; simpl.
  - exact HΓ.
  - destruct Hts as [| t ts' Ht Hts'].
    + constructor; [exact concrete_missing_field | apply IH; auto].
    + constructor; [exact Ht | apply IH; auto].
Qed.

Lemma concore_find_alt : forall d alts xs e,
  Forall concore_alt alts -> find_alt d alts = Some (xs, e) -> concore_expr e.
Proof.
  intros d alts xs e Halts. induction Halts as [| [d' xs' e'] rest Ha _ IH]; simpl; intros Hfind.
  - discriminate.
  - destruct (string_dec d d').
    + injection Hfind as <- <-. inversion Ha. assumption.
    + exact (IH Hfind).
Qed.

Lemma concrete_merge : forall v, concrete_value v -> merge v = v.
Proof.
  intros v Hv. destruct Hv; reflexivity.
Qed.

Lemma concrete_prim_is_literal : forall p, concrete_value (VPrim p) -> is_plit p = true.
Proof.
  intros p Hp. inversion Hp. reflexivity.
Qed.

Lemma concrete_not_if : forall p vt vf, ~ concrete_value (VIf p vt vf).
Proof.
  intros p vt vf H. inversion H.
Qed.

Lemma concrete_not_tif : forall p tt tf, ~ concrete_thunk (TIf p tt tf).
Proof.
  intros p tt tf H. inversion H.
Qed.

End ConCore.
