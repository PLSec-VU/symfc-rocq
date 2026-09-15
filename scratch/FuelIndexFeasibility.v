(* Does indexing an existing relation by a fuel type with an infinite
   element force every existing inversion to grow a case?

   Answered no, and the design has since landed: SymCore.v carries this exact
   fuel type, this dec, ordinary rules that conclude at a Live fuel, and Rule
   Out-Of-Fuel with Spent in its conclusion index. This file stays as the
   small standalone model, which imports nothing and can be read on its own.

   The first design wrote Fin 0 in the conclusion of the out-of-fuel rule and
   let every other rule conclude at any fuel, with dec (Fin 0) = Fin 0. Its
   model is kept at the end: there, Fin 0 runs every ordinary rule with no
   bound at all. *)
Inductive live_fuel := Unlimited | Remaining (n : nat).
Inductive fuel := Spent | Live (f : live_fuel).
Notation Inf := (Live Unlimited).
Definition Fin (n : nat) : fuel :=
  match n with O => Spent | S m => Live (Remaining m) end.
Definition dec (f : live_fuel) : fuel :=
  match f with Unlimited => Inf | Remaining n => Fin n end.

Inductive tm := Lit (n : nat) | Add (a b : tm) | Loop.

Inductive ev : fuel -> tm -> nat -> Prop :=
  | EvLit  : forall f n, ev (Live f) (Lit n) n
  | EvAdd  : forall f a b x y,
      ev (dec f) a x -> ev (dec f) b y -> ev (Live f) (Add a b) (x + y)
  | EvLoop : forall f v, ev (dec f) Loop v -> ev (Live f) Loop v
  (* the out-of-fuel rule names Spent in its CONCLUSION index *)
  | EvOut  : forall t, ev Spent t 0.

Notation "t '⇓' v" := (ev Inf t v) (at level 70).

(* At Inf, does inversion see the EvOut case at all? *)
Lemma inversion_at_Inf : forall a b v, Add a b ⇓ v -> exists x y, v = x + y.
Proof.
  intros a b v H.
  inversion H; subst.
  (* if EvOut appeared we would need a second bullet here *)
  exists x, y. reflexivity.
Qed.

(* At Fin 0 only EvOut is left. *)
Lemma inversion_at_Fin_0 : forall t v, ev (Fin 0) t v -> v = 0.
Proof.
  intros t v H.
  inversion H; subst.
  reflexivity.
Qed.

(* And the bounded relation really is inhabited on a divergent term. *)
Lemma loop_has_bounded_value : ev (Fin 3) Loop 0.
Proof. apply EvLoop. apply EvLoop. apply EvLoop. simpl. apply EvOut. Qed.

(* while at Inf it is not: no finite derivation exists. *)
Lemma loop_diverges_at_Inf : forall v, ~ (Loop ⇓ v).
Proof.
  intros v H. remember Inf as f eqn:Hf. remember Loop as t eqn:Ht.
  induction H; try discriminate.
  injection Hf as Hf. subst f.
  apply IHev; [ reflexivity | exact Ht ].
Qed.

(* The first design, for contrast. *)
Definition dec_old (f : fuel) : fuel :=
  match f with Spent => Spent | Live Unlimited => Inf | Live (Remaining n) => Fin n end.

Inductive ev_old : fuel -> tm -> nat -> Prop :=
  | EvOldLit  : forall f n, ev_old f (Lit n) n
  | EvOldAdd  : forall f a b x y,
      ev_old (dec_old f) a x -> ev_old (dec_old f) b y -> ev_old f (Add a b) (x + y)
  | EvOldLoop : forall f v, ev_old (dec_old f) Loop v -> ev_old f Loop v
  | EvOldOut  : forall t, ev_old Spent t 0.

(* At Fin 0 the first design still adds, and nests as deep as it likes. *)
Lemma old_fin_zero_is_not_a_bound :
  ev_old (Fin 0) (Add (Add (Lit 1) (Lit 2)) (Lit 3)) 6
  /\ ~ ev (Fin 0) (Add (Add (Lit 1) (Lit 2)) (Lit 3)) 6.
Proof.
  split.
  - apply (EvOldAdd Spent (Add (Lit 1) (Lit 2)) (Lit 3) 3 3);
      [apply (EvOldAdd Spent (Lit 1) (Lit 2) 1 2); apply EvOldLit | apply EvOldLit].
  - intros H. apply inversion_at_Fin_0 in H. discriminate H.
Qed.
