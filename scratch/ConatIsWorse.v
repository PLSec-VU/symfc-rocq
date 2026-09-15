CoInductive conat := CoO | CoS (n : conat).
CoFixpoint omega : conat := CoS omega.
Definition dec (n : conat) : conat := match n with CoO => CoO | CoS m => m end.

Inductive tm := Lit (n : nat) | Add (a b : tm) | Loop.

Inductive ev : conat -> tm -> nat -> Prop :=
  | EvLit  : forall f n, ev f (Lit n) n
  | EvAdd  : forall f a b x y,
      ev (dec f) a x -> ev (dec f) b y -> ev f (Add a b) (x + y)
  | EvLoop : forall f v, ev (dec f) Loop v -> ev f Loop v
  | EvOut  : forall t, ev CoO t 0.

(* Q1: does dec omega reduce to omega definitionally? *)
Lemma dec_omega_defeq : dec omega = omega.
Proof. reflexivity. Qed.

(* Q2: at omega, does inversion prune the EvOut case (index CoO)? *)
Lemma inversion_at_omega : forall a b v, ev omega (Add a b) v -> exists x y, v = x + y.
Proof.
  intros a b v H.
  inversion H; subst.
  (* TWO goals: the EvOut case SURVIVES.  Coq cannot see a constructor
     clash between the rule's index CoO and the cofix term omega, so it
     keeps the case.  Compare FuelIndexFeasibility.v, where the index
     Spent clashes with Inf outright and inversion drops the case,
     leaving ONE goal.  That difference is the whole cost argument:
     with conat every existing inversion in the development grows a
     spurious case that must be discharged by hand. *)
Abort.
