From Stdlib Require Import Strings.String Lists.List Bool.Bool Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.

Definition var : Set := string.
Definition dcon : Set := string.

Class SymCoreSorts : Type := {
  lit : Set;
  primop : Set;
  op_and : primop;
  op_not : primop;
  op_ite : primop;
  primop_arity : primop -> nat;
  op_ite_arity : primop_arity op_ite = 3%nat;
  lit_eq_dec : forall (l1 l2 : lit), {l1 = l2} + {l1 <> l2};
  primop_eq_dec : forall (p1 p2 : primop), {p1 = p2} + {p1 <> p2};
  tycon : Set;
  tycon_eq_dec : forall (t1 t2 : tycon), {t1 = t2} + {t1 <> t2};
  prim_value : primop -> list lit -> lit;
  lit_true : lit;
  prim_value_and : forall a b,
    prim_value op_and [a; b] = lit_true <-> a = lit_true /\ b = lit_true;
  prim_value_not : forall l, prim_value op_not [l] = lit_true <-> l <> lit_true;
  prim_value_ite : forall c t f,
    prim_value op_ite [c; t; f] = if lit_eq_dec c lit_true then t else f
}.

Section SymCore.
Context {sorts : SymCoreSorts}.

Inductive type_fc : Set :=
  | TyVar : var -> type_fc
  | TyCon : tycon -> type_fc
  | TyArrow : type_fc -> type_fc -> type_fc
  | TyApp : type_fc -> type_fc -> type_fc.

Inductive role : Set :=
  | RoleNominal
  | RoleRepresentational
  | RolePhantom.

Definition role_eq_dec : forall (r1 r2 : role), {r1 = r2} + {r1 <> r2}.
Proof.
  decide equality.
Defined.

Definition type_fc_eq_dec : forall (τ1 τ2 : type_fc), {τ1 = τ2} + {τ1 <> τ2}.
Proof.
  decide equality; [apply string_dec | apply tycon_eq_dec].
Defined.

Definition dec_eqb {A : Type} (d : forall x y : A, {x = y} + {x <> y}) (x y : A) : bool :=
  if d x y then true else false.

Lemma dec_eqb_eq : forall (A : Type) (d : forall x y : A, {x = y} + {x <> y}) x y,
  dec_eqb d x y = true -> x = y.
Proof.
  intros A d x y H. unfold dec_eqb in H. destruct (d x y); [assumption | discriminate].
Qed.

Record coercion : Set := MkCoercion {
  coerc_src : type_fc;
  coerc_dst : type_fc;
  coerc_role : role
}.

Definition sym_coerc (γ : coercion) : coercion :=
  MkCoercion (coerc_dst γ) (coerc_src γ) (coerc_role γ).

Definition coercion_eq_dec : forall (γ1 γ2 : coercion), {γ1 = γ2} + {γ1 <> γ2}.
Proof.
  decide equality; [apply role_eq_dec | apply type_fc_eq_dec | apply type_fc_eq_dec].
Defined.

Definition decomp_coerc_arrow (γ : coercion) : option (coercion * coercion) :=
  match coerc_src γ, coerc_dst γ with
  | TyArrow s1 s2, TyArrow d1 d2 =>
      Some (MkCoercion s1 d1 (coerc_role γ), MkCoercion s2 d2 (coerc_role γ))
  | _, _ => None
  end.

Inductive expr : Type :=
  | EVar : var -> expr
  | ESym : var -> expr
  | ELit : lit -> expr
  | EPrimOp : primop -> expr
  | ECon : dcon -> expr
  | EApp : expr -> expr -> expr
  | ELam : var -> expr -> expr
  | ECase : expr -> list alt -> expr
  | ECast : expr -> coercion -> expr
  | ECoercion : coercion -> expr
  | EType : type_fc -> expr
  | EBot : bottom -> expr

with bottom : Type :=
  | BRaise : expr -> bottom
  | BUnreachable : bottom
  | BUndefined : bottom
  | BOutOfFuel : bottom

with alt : Type :=
  | Alt : dcon -> list var -> expr -> alt.

Inductive prim : Type :=
  | PLit : lit -> prim
  | PSym : var -> prim
  | PApp : primop -> list prim -> prim.

Inductive value : Type :=
  | VPrim : prim -> value
  | VClos : env -> var -> expr -> value
  | VCon : dcon -> list thunk -> value
  | VPartial : primop -> list thunk -> value
  | VType : type_fc -> value
  | VCoercion : coercion -> value
  | VCast : value -> coercion -> value
  | VBot : bottom -> value
  | VIf : prim -> value -> value -> value

with thunk : Type :=
  | TSusp : env -> expr -> thunk
  | TIf : prim -> thunk -> thunk -> thunk

with env : Type :=
  | EmptyEnv : env
  | ExtendEnv : var -> thunk -> env -> env.

Definition path_condition : Type := prim.

Definition pc_and (a b : prim) : prim := PApp op_and [a; b].
Definition pc_not (a : prim) : prim := PApp op_not [a].

Fixpoint lookup_env (Γ : env) (x : var) : option thunk :=
  match Γ with
  | EmptyEnv => None
  | ExtendEnv y t rest => if string_dec x y then Some t else lookup_env rest x
  end.

Definition extend_env (Γ : env) (x : var) (t : thunk) : env := ExtendEnv x t Γ.

Definition missing_field : thunk := TSusp EmptyEnv (EBot BUndefined).

Fixpoint bind_fields (Γ : env) (xs : list var) (ts : list thunk) : env :=
  match xs, ts with
  | x :: xs', t :: ts' => extend_env (bind_fields Γ xs' ts') x t
  | x :: xs', [] => extend_env (bind_fields Γ xs' []) x missing_field
  | [], _ => Γ
  end.

Fixpoint find_alt (d : dcon) (alts : list alt) : option (list var * expr) :=
  match alts with
  | [] => None
  | Alt d' xs e :: rest => if string_dec d d' then Some (xs, e) else find_alt d rest
  end.

Definition is_plit (p : prim) : bool :=
  match p with
  | PLit _ => true
  | _ => false
  end.

Fixpoint list_eqb {A : Type} (f : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | x1 :: r1, x2 :: r2 => f x1 x2 && list_eqb f r1 r2
  | _, _ => false
  end.

Lemma list_eqb_eq : forall (A : Type) (f : A -> A -> bool),
  (forall x y, f x y = true -> x = y) ->
  forall l1 l2, list_eqb f l1 l2 = true -> l1 = l2.
Proof.
  intros A f Hf. induction l1 as [| x r IH]; intros [| y s] H; simpl in H;
    try discriminate; try reflexivity.
  apply andb_prop in H as [Hxy Hrest]. rewrite (Hf _ _ Hxy). f_equal. apply IH. exact Hrest.
Qed.

Definition vars_eqb : list var -> list var -> bool := list_eqb String.eqb.

Lemma vars_eqb_eq : forall xs1 xs2, vars_eqb xs1 xs2 = true -> xs1 = xs2.
Proof.
  exact (list_eqb_eq _ _ (fun x y => proj1 (String.eqb_eq x y))).
Qed.

Fixpoint expr_eqb (e1 e2 : expr) {struct e1} : bool :=
  match e1, e2 with
  | EVar x1, EVar x2 => String.eqb x1 x2
  | ESym s1, ESym s2 => String.eqb s1 s2
  | ELit l1, ELit l2 => dec_eqb lit_eq_dec l1 l2
  | EPrimOp p1, EPrimOp p2 => dec_eqb primop_eq_dec p1 p2
  | ECon d1, ECon d2 => String.eqb d1 d2
  | EApp f1 a1, EApp f2 a2 => expr_eqb f1 f2 && expr_eqb a1 a2
  | ELam x1 b1, ELam x2 b2 => String.eqb x1 x2 && expr_eqb b1 b2
  | ECase s1 alts1, ECase s2 alts2 =>
      expr_eqb s1 s2 &&
      (fix alts_eqb (l1 l2 : list alt) {struct l1} : bool :=
         match l1, l2 with
         | [], [] => true
         | a1 :: t1, a2 :: t2 => alt_eqb a1 a2 && alts_eqb t1 t2
         | _, _ => false
         end) alts1 alts2
  | ECast b1 γ1, ECast b2 γ2 => expr_eqb b1 b2 && dec_eqb coercion_eq_dec γ1 γ2
  | ECoercion γ1, ECoercion γ2 => dec_eqb coercion_eq_dec γ1 γ2
  | EType τ1, EType τ2 => dec_eqb type_fc_eq_dec τ1 τ2
  | EBot b1, EBot b2 => bottom_eqb b1 b2
  | _, _ => false
  end
with bottom_eqb (b1 b2 : bottom) {struct b1} : bool :=
  match b1, b2 with
  | BRaise e1, BRaise e2 => expr_eqb e1 e2
  | BUnreachable, BUnreachable => true
  | BUndefined, BUndefined => true
  | BOutOfFuel, BOutOfFuel => true
  | _, _ => false
  end
with alt_eqb (a1 a2 : alt) {struct a1} : bool :=
  match a1, a2 with
  | Alt d1 xs1 p1, Alt d2 xs2 p2 =>
      String.eqb d1 d2 && vars_eqb xs1 xs2 && expr_eqb p1 p2
  end.

Fixpoint expr_eqb_eq (e1 : expr) {struct e1} :
  forall e2, expr_eqb e1 e2 = true -> e1 = e2
with bottom_eqb_eq (b1 : bottom) {struct b1} :
  forall b2, bottom_eqb b1 b2 = true -> b1 = b2
with alt_eqb_eq (a1 : alt) {struct a1} :
  forall a2, alt_eqb a1 a2 = true -> a1 = a2.
Proof.
  - destruct e1; intros e2 H; destruct e2; simpl in H; try discriminate.
    + apply String.eqb_eq in H. subst. reflexivity.
    + apply String.eqb_eq in H. subst. reflexivity.
    + apply dec_eqb_eq in H. subst. reflexivity.
    + apply dec_eqb_eq in H. subst. reflexivity.
    + apply String.eqb_eq in H. subst. reflexivity.
    + apply andb_prop in H as [H1 H2].
      rewrite (expr_eqb_eq _ _ H1), (expr_eqb_eq _ _ H2). reflexivity.
    + apply andb_prop in H as [H1 H2]. apply String.eqb_eq in H1. subst.
      rewrite (expr_eqb_eq _ _ H2). reflexivity.
    + apply andb_prop in H as [H1 H2].
      rewrite (expr_eqb_eq _ _ H1). f_equal.
      revert l0 H2. induction l as [| a t IH]; intros [| a' t'] H2; simpl in H2;
        try discriminate; try reflexivity.
      apply andb_prop in H2 as [Ha Ht].
      rewrite (alt_eqb_eq _ _ Ha). f_equal. apply IH. exact Ht.
    + apply andb_prop in H as [H1 H2]. apply dec_eqb_eq in H2. subst.
      rewrite (expr_eqb_eq _ _ H1). reflexivity.
    + apply dec_eqb_eq in H. subst. reflexivity.
    + apply dec_eqb_eq in H. subst. reflexivity.
    + rewrite (bottom_eqb_eq _ _ H). reflexivity.
  - destruct b1; intros b2 H; destruct b2; simpl in H;
      try discriminate; try reflexivity.
    rewrite (expr_eqb_eq _ _ H). reflexivity.
  - destruct a1 as [d1 xs1 p1]; intros [d2 xs2 p2] H; simpl in H.
    apply andb_prop in H as [H12 H3]. apply andb_prop in H12 as [H1 H2].
    apply String.eqb_eq in H1. subst d2.
    rewrite (vars_eqb_eq _ _ H2), (expr_eqb_eq _ _ H3). reflexivity.
Qed.

Fixpoint prim_eqb (p1 p2 : prim) {struct p1} : bool :=
  match p1, p2 with
  | PLit l1, PLit l2 => dec_eqb lit_eq_dec l1 l2
  | PSym s1, PSym s2 => String.eqb s1 s2
  | PApp o1 as1, PApp o2 as2 =>
      dec_eqb primop_eq_dec o1 o2 &&
      (fix prims_eqb (l1 l2 : list prim) {struct l1} : bool :=
         match l1, l2 with
         | [], [] => true
         | q1 :: r1, q2 :: r2 => prim_eqb q1 q2 && prims_eqb r1 r2
         | _, _ => false
         end) as1 as2
  | _, _ => false
  end.

Fixpoint prim_eqb_eq (p1 : prim) {struct p1} :
  forall p2, prim_eqb p1 p2 = true -> p1 = p2.
Proof.
  destruct p1; intros p2 H; destruct p2; simpl in H; try discriminate.
  - apply dec_eqb_eq in H. subst. reflexivity.
  - apply String.eqb_eq in H. subst. reflexivity.
  - apply andb_prop in H as [H1 H2]. apply dec_eqb_eq in H1. subst.
    f_equal. revert l0 H2. induction l as [| q r IH]; intros [| q' r'] H2;
      simpl in H2; try discriminate; try reflexivity.
    apply andb_prop in H2 as [Hq Hr].
    rewrite (prim_eqb_eq _ _ Hq). f_equal. apply IH. exact Hr.
Qed.

Fixpoint thunk_eqb (t1 t2 : thunk) {struct t1} : bool :=
  match t1, t2 with
  | TSusp Γ1 e1, TSusp Γ2 e2 => env_eqb Γ1 Γ2 && expr_eqb e1 e2
  | TIf p1 a1 b1, TIf p2 a2 b2 =>
      prim_eqb p1 p2 && thunk_eqb a1 a2 && thunk_eqb b1 b2
  | _, _ => false
  end
with env_eqb (Γ1 Γ2 : env) {struct Γ1} : bool :=
  match Γ1, Γ2 with
  | EmptyEnv, EmptyEnv => true
  | ExtendEnv x1 t1 r1, ExtendEnv x2 t2 r2 =>
      String.eqb x1 x2 && thunk_eqb t1 t2 && env_eqb r1 r2
  | _, _ => false
  end.

Fixpoint value_eqb (v1 v2 : value) {struct v1} : bool :=
  match v1, v2 with
  | VPrim p1, VPrim p2 => prim_eqb p1 p2
  | VClos Γ1 x1 b1, VClos Γ2 x2 b2 =>
      env_eqb Γ1 Γ2 && String.eqb x1 x2 && expr_eqb b1 b2
  | VCon d1 ts1, VCon d2 ts2 => String.eqb d1 d2 && list_eqb thunk_eqb ts1 ts2
  | VPartial o1 ts1, VPartial o2 ts2 =>
      dec_eqb primop_eq_dec o1 o2 &&
      list_eqb thunk_eqb ts1 ts2
  | VType τ1, VType τ2 => dec_eqb type_fc_eq_dec τ1 τ2
  | VCoercion γ1, VCoercion γ2 => dec_eqb coercion_eq_dec γ1 γ2
  | VCast w1 γ1, VCast w2 γ2 => value_eqb w1 w2 && dec_eqb coercion_eq_dec γ1 γ2
  | VBot b1, VBot b2 => bottom_eqb b1 b2
  | VIf p1 a1 b1, VIf p2 a2 b2 =>
      prim_eqb p1 p2 && value_eqb a1 a2 && value_eqb b1 b2
  | _, _ => false
  end.

Fixpoint thunk_eqb_eq (t1 : thunk) {struct t1} :
  forall t2, thunk_eqb t1 t2 = true -> t1 = t2
with env_eqb_eq (Γ1 : env) {struct Γ1} :
  forall Γ2, env_eqb Γ1 Γ2 = true -> Γ1 = Γ2.
Proof.
  - destruct t1; intros t2 H; destruct t2; simpl in H; try discriminate.
    + apply andb_prop in H as [H1 H2].
      rewrite (env_eqb_eq _ _ H1), (expr_eqb_eq _ _ H2). reflexivity.
    + apply andb_prop in H as [H12 H3]. apply andb_prop in H12 as [H1 H2].
      rewrite (prim_eqb_eq _ _ H1), (thunk_eqb_eq _ _ H2), (thunk_eqb_eq _ _ H3).
      reflexivity.
  - destruct Γ1 as [| x1 t1 r1]; intros Γ2 H; destruct Γ2 as [| x2 t2 r2];
      simpl in H; try discriminate; try reflexivity.
    apply andb_prop in H as [H12 H3]. apply andb_prop in H12 as [H1 H2].
    apply String.eqb_eq in H1. subst x2.
    rewrite (thunk_eqb_eq _ _ H2), (env_eqb_eq _ _ H3). reflexivity.
Qed.

Fixpoint value_eqb_eq (v1 : value) {struct v1} :
  forall v2, value_eqb v1 v2 = true -> v1 = v2.
Proof.
  destruct v1; intros v2 H; destruct v2; simpl in H; try discriminate.
    + rewrite (prim_eqb_eq _ _ H). reflexivity.
    + apply andb_prop in H as [H12 H3]. apply andb_prop in H12 as [H1 H2].
      apply String.eqb_eq in H2. subst.
      rewrite (env_eqb_eq _ _ H1), (expr_eqb_eq _ _ H3). reflexivity.
    + apply andb_prop in H as [H1 H2]. apply String.eqb_eq in H1. subst.
      rewrite (list_eqb_eq _ _ thunk_eqb_eq _ _ H2). reflexivity.
    + apply andb_prop in H as [H1 H2]. apply dec_eqb_eq in H1. subst.
      rewrite (list_eqb_eq _ _ thunk_eqb_eq _ _ H2). reflexivity.
    + apply dec_eqb_eq in H. subst. reflexivity.
    + apply dec_eqb_eq in H. subst. reflexivity.
    + apply andb_prop in H as [H1 H2]. apply dec_eqb_eq in H2. subst.
      rewrite (value_eqb_eq _ _ H1). reflexivity.
    + rewrite (bottom_eqb_eq _ _ H). reflexivity.
    + apply andb_prop in H as [H12 H3]. apply andb_prop in H12 as [H1 H2].
      rewrite (prim_eqb_eq _ _ H1), (value_eqb_eq _ _ H2), (value_eqb_eq _ _ H3).
      reflexivity.
Qed.

Section Examples.
Variables t1 t2 : thunk.

Example lookup_shadow :
  lookup_env (ExtendEnv "x" t1 (ExtendEnv "x" t2 EmptyEnv)) "x" = Some t1 := eq_refl.

Example bind_fields_missing :
  lookup_env (bind_fields EmptyEnv ["a"; "b"] [t1]) "b" = Some (TSusp EmptyEnv (EBot BUndefined)) :=
  eq_refl.
Example bind_fields_drops_extra :
  bind_fields EmptyEnv ["a"] [t1; t2] = ExtendEnv "a" t1 EmptyEnv := eq_refl.
End Examples.

End SymCore.
