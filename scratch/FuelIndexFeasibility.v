(* Does indexing an existing relation by a fuel type with an infinite
   element force every existing inversion to grow a case?

   Answered no, and the design has since landed: SymCore.v carries this exact
   fuel type, this dec, and Rule Out-Of-Fuel with Fin 0 in its conclusion
   index. This file stays as the small standalone model, which imports
   nothing and can be read on its own. *)
Inductive fuel := Inf | Fin (n : nat).
Definition dec (f : fuel) : fuel :=
  match f with Inf => Inf | Fin 0 => Fin 0 | Fin (S n) => Fin n end.

Inductive tm := Lit (n : nat) | Add (a b : tm) | Loop.

Inductive ev : fuel -> tm -> nat -> Prop :=
  | EvLit  : forall f n, ev f (Lit n) n
  | EvAdd  : forall f a b x y,
      ev (dec f) a x -> ev (dec f) b y -> ev f (Add a b) (x + y)
  | EvLoop : forall f v, ev (dec f) Loop v -> ev f Loop v
  (* the out-of-fuel rule names Fin 0 in its CONCLUSION index *)
  | EvOut  : forall t, ev (Fin 0) t 0.

Notation "t '⇓' v" := (ev Inf t v) (at level 70).

(* At Inf, does inversion see the EvOut case at all? *)
Lemma inversion_at_Inf : forall a b v, Add a b ⇓ v -> exists x y, v = x + y.
Proof.
  intros a b v H.
  inversion H; subst.
  (* if EvOut appeared we would need a second bullet here *)
  exists x, y. reflexivity.
Qed.

(* And the bounded relation really is inhabited on a divergent term. *)
Lemma loop_has_bounded_value : ev (Fin 3) Loop 0.
Proof. apply EvLoop. apply EvLoop. apply EvLoop. simpl. apply EvOut. Qed.

(* while at Inf it is not: no finite derivation exists. *)
Lemma loop_diverges_at_Inf : forall v, ~ (Loop ⇓ v).
Proof.
  intros v H. remember Inf as f eqn:Hf. remember Loop as t eqn:Ht.
  induction H; try discriminate.
  apply IHev; [ rewrite Hf; reflexivity | exact Ht ].
Qed.
