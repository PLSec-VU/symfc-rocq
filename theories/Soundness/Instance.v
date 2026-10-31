From SymCoreTheory Require Export SymCore.Syntax SymCore.Solver.
From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

Section Valuation.
Context {sorts : SymCoreSorts}.

Definition valuation : Type := var -> lit.

Fixpoint prim_denote (σ : valuation) (p : prim) : lit :=
  match p with
  | PLit l => l
  | PSym s => σ s
  | PApp op ps => prim_value op (map (prim_denote σ) ps)
  end.

Definition models (σ : valuation) (p : prim) : Prop := prim_denote σ p = lit_true.

End Valuation.

Notation "σ '⊨' p" := (models σ p) (at level 70, no associativity).

Section Instance.
Context {sorts : SymCoreSorts} {solver : SymCoreSolver}.

Inductive contains_prim (σ : valuation) : prim -> prim -> Prop :=
  | Contains_PLit : forall l, contains_prim σ (PLit l) (PLit l)
  | Contains_PSym : forall s, contains_prim σ (PSym s) (PLit (σ s))
  | Contains_PDenote : forall op ps l,
      length ps = primop_arity op ->
      prim_denote σ (PApp op ps) = l ->
      contains_prim σ (PApp op ps) (PLit l).

Inductive contains_expr (σ : valuation) : expr -> expr -> Prop :=
  | Contains_EVar : forall x, contains_expr σ (EVar x) (EVar x)
  | Contains_ESym : forall s, contains_expr σ (ESym s) (ESym s)
  | Contains_ESymLit : forall s, contains_expr σ (ESym s) (ELit (σ s))
  | Contains_ELit : forall l, contains_expr σ (ELit l) (ELit l)
  | Contains_EPrimOp : forall op, contains_expr σ (EPrimOp op) (EPrimOp op)
  | Contains_ECon : forall d, contains_expr σ (ECon d) (ECon d)
  | Contains_EApp : forall fs fc a_s a_c,
      contains_expr σ fs fc -> contains_expr σ a_s a_c ->
      contains_expr σ (EApp fs a_s) (EApp fc a_c)
  | Contains_ELam : forall x bs bc,
      contains_expr σ bs bc -> contains_expr σ (ELam x bs) (ELam x bc)
  | Contains_ECase : forall es ec alts_s alts_c,
      contains_expr σ es ec -> Forall2 (contains_alt σ) alts_s alts_c ->
      contains_expr σ (ECase es alts_s) (ECase ec alts_c)
  | Contains_ECast : forall es ec γ,
      contains_expr σ es ec -> contains_expr σ (ECast es γ) (ECast ec γ)
  | Contains_ECoercion : forall γ, contains_expr σ (ECoercion γ) (ECoercion γ)
  | Contains_EType : forall τ, contains_expr σ (EType τ) (EType τ)
  | Contains_EBot : forall bs bc,
      contains_bottom σ bs bc -> contains_expr σ (EBot bs) (EBot bc)

with contains_bottom (σ : valuation) : bottom -> bottom -> Prop :=
  | Contains_BRaise : forall es ec,
      contains_expr σ es ec -> contains_bottom σ (BRaise es) (BRaise ec)
  | Contains_BUnreachable : contains_bottom σ BUnreachable BUnreachable
  | Contains_BUndefined : contains_bottom σ BUndefined BUndefined
  | Contains_BOutOfFuel : contains_bottom σ BOutOfFuel BOutOfFuel

with contains_alt (σ : valuation) : alt -> alt -> Prop :=
  | Contains_Alt : forall d xs es ec,
      contains_expr σ es ec -> contains_alt σ (Alt d xs es) (Alt d xs ec).

Inductive contains_val (σ : valuation) : value -> value -> Prop :=
  | Contains_VPrim : forall ps pc,
      contains_prim σ ps pc -> contains_val σ (VPrim ps) (VPrim pc)
  | Contains_VClos : forall Γs Γc x bs bc,
      contains_env σ Γs Γc -> contains_expr σ bs bc ->
      contains_val σ (VClos Γs x bs) (VClos Γc x bc)
  | Contains_VCon : forall d ts_s ts_c,
      Forall2 (contains_thunk σ) ts_s ts_c -> contains_val σ (VCon d ts_s) (VCon d ts_c)
  | Contains_VPartial : forall op ts_s ts_c,
      Forall2 (contains_thunk σ) ts_s ts_c ->
      contains_val σ (VPartial op ts_s) (VPartial op ts_c)
  | Contains_VType : forall τ, contains_val σ (VType τ) (VType τ)
  | Contains_VCoercion : forall γ, contains_val σ (VCoercion γ) (VCoercion γ)
  | Contains_VCast : forall vs vc γ,
      contains_val σ vs vc -> contains_val σ (VCast vs γ) (VCast vc γ)
  | Contains_VBot : forall bs bc,
      contains_bottom σ bs bc -> contains_val σ (VBot bs) (VBot bc)
  | Contains_VIfT : forall p vt vf vc,
      σ ⊨ p -> contains_val σ vt vc -> contains_val σ (VIf p vt vf) vc
  | Contains_VIfF : forall p vt vf vc,
      σ ⊨ pc_not p -> contains_val σ vf vc -> contains_val σ (VIf p vt vf) vc

with contains_thunk (σ : valuation) : thunk -> thunk -> Prop :=
  | Contains_TSusp : forall Γs Γc es ec,
      contains_env σ Γs Γc -> contains_expr σ es ec ->
      contains_thunk σ (TSusp Γs es) (TSusp Γc ec)
  | Contains_TIfT : forall p tt tf tc,
      σ ⊨ p -> contains_thunk σ tt tc -> contains_thunk σ (TIf p tt tf) tc
  | Contains_TIfF : forall p tt tf tc,
      σ ⊨ pc_not p -> contains_thunk σ tf tc -> contains_thunk σ (TIf p tt tf) tc

with contains_env (σ : valuation) : env -> env -> Prop :=
  | Contains_Empty : contains_env σ EmptyEnv EmptyEnv
  | Contains_Extend : forall x ts tc Γs Γc,
      contains_thunk σ ts tc -> contains_env σ Γs Γc ->
      contains_env σ (ExtendEnv x ts Γs) (ExtendEnv x tc Γc).

Lemma contains_prim_target : forall σ p pc,
  contains_prim σ p pc -> pc = PLit (prim_denote σ p).
Proof.
  intros σ p pc H. destruct H as [| | op ps l _ Hl]; [reflexivity | reflexivity | subst l; reflexivity].
Qed.

Lemma contains_prim_denote : forall σ p l, contains_prim σ p (PLit l) -> prim_denote σ p = l.
Proof.
  intros σ p l H. apply contains_prim_target in H. injection H as Hl. symmetry. exact Hl.
Qed.

Lemma models_and : forall σ a b, σ ⊨ pc_and a b <-> σ ⊨ a /\ σ ⊨ b.
Proof.
  intros σ a b. unfold models, pc_and. simpl. apply prim_value_and.
Qed.

Lemma models_not : forall σ p, σ ⊨ pc_not p <-> prim_denote σ p <> lit_true.
Proof.
  intros σ p. unfold models, pc_not. simpl. apply prim_value_not.
Qed.

Class ModelsSat : Prop := models_sat : forall σ Φ, σ ⊨ Φ -> sat Φ = true.
Class ReducePrimContains : Prop := reduce_prim_contains : forall σ op ps ls,
  length ps = primop_arity op -> Forall2 (contains_prim σ) ps (map PLit ls) ->
  contains_val σ (reduce_prim op ps) (VPrim (PLit (prim_value op ls))).
Class CastContains : Prop := cast_contains : forall σ vs vc γ,
  contains_val σ vs vc -> contains_val σ (cast_value vs γ) (cast_value vc γ).
Class SubstContains : Prop := {
  subst_type_contains : forall σ Γs Γc τ,
    contains_env σ Γs Γc -> subst_type Γs τ = subst_type Γc τ;
  subst_coerc_contains : forall σ Γs Γc γ,
    contains_env σ Γs Γc -> subst_coerc Γs γ = subst_coerc Γc γ }.

End Instance.
