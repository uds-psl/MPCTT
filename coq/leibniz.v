Section Equality.
  Variable eq : forall X, X -> X -> Prop.
  Variable Q : forall X x, eq X x x.
  Variable R : forall X x y (p: X -> Prop), eq X x y -> p x -> p y.

  Arguments eq [X].
  Arguments Q [X].
  Arguments R [X x y].
  Notation "s = t" := (eq s t) : type_scope.
  Notation "s <> t" := (~ s = t) : type_scope.

Goal True <> False.
Proof.
  intros H.
  change ((fun X => X) False).
  apply (R _ H).
  exact I.
  Show Proof.
Qed.

Goal True <> False.
Proof.
  intros H.
  apply (R (fun X => X) H).
  exact I.
  Show Proof.
Qed.

Goal true <> false.
Proof.
  intros H.
  change ((fun x:bool => if x then True else False) false).
  apply (R _ H).
  exact I.
  Show Proof.
Qed.

Goal forall x y, S x = S y -> x = y.
Proof.
  intros x y H.
  change ((fun z => x = match z with 0 => 0 | S z' => z' end) (S y)).
  apply (R _ H).
  exact (Q x).
  Show Proof.
Qed.

Goal forall x y, S x = S y -> x = y.
Proof.
 intros x y H.
  apply (R (fun z => x = match z with 0 => 0 | S z' => z' end) H).
  exact (Q _).
  Show Proof.
Qed.

Definition pred (x: nat) : nat :=
  match x with 0 => 0 | S x' => x' end.

Goal forall x y, S x = S y -> x = y.
Proof.
  intros x y H.
  change ((fun z => x = pred z) (S y)).
  apply (R _ H).
  exact (Q x).
  Show Proof.
Qed.

Goal forall X (x y: X), x = y -> y = x.
Proof.
  intros X x y H.
  change ((fun z => z = x) y).
  apply (R _ H).
  exact (Q x).
  Show Proof.
Qed.

Goal forall X (x y z: X), x = y -> y = z -> x = z.
Proof.
  intros X x y z H.
  change ((fun a => a = z -> x = z) y).
  apply (R _ H).
  exact (fun h => h).
  Show Proof.
Qed.

Goal forall X Y (f: X -> Y) (x x': X),
    x = x' -> f x = f x'.
Proof.
  intros X Y f x x' H.
  change ((fun z => f x = f z) x').
  apply (R _ H).
  exact (Q (f x)).
  Show Proof.     
Qed.

Goal forall X x y, x = y <-> forall p: X -> Prop, p x -> p y.
Proof.
  intros X x y.
  split.
  - intros H p H1.
    apply (R _ H H1).
  - intros H.
    change ((fun z => x = z) y).
    apply H.
    apply Q.
  Show Proof.
Qed.

End Equality.

(** Automation for predefined equality **)

Goal true <> false.
Proof.
  discriminate.
Qed.

Goal forall x y, S x = S y -> x = y.
Proof.
  congruence.
Qed.

Goal forall x y, S x = S y -> x = y.
Proof.
  intros x y [= H]. exact H. 
Qed.

Goal forall x, S x <> 0.
Proof.
  discriminate.
Qed.

(** Leibniz definition of equality *)

Module Type EQ.
  Parameter eq : forall X, X -> X -> Prop.
  Parameter Q : forall X x, eq X x x.
  Parameter R : forall X x y (p: X -> Prop), eq X x y -> p x -> p y.
End EQ.

Module EqLeibniz : EQ.
  Definition eq X x y := forall p: X -> Prop, p x -> p y.
  Definition Q X x : eq X x x := fun p h => h.
  Definition R X x y p (f: eq X x y) := f p.
End EqLeibniz.

Print EqLeibniz.R.

(** Could import EqLeibniz with [Import EqLeibniz.].  **)

(** Definition of equality with predefined inductive equality *)

Module EqInductive : EQ.
  Definition eq := @eq.
  Definition Q := @eq_refl.
  Definition R X x y (p: X -> Prop) (h: eq X x y) : p x -> p y
    := match h with eq_refl => fun h => h end.
End EqInductive.

(** Commands used:
    Notation, Module,
    Section, Variable, End, Arguments,
    Goal, Proof, Show Proof, Qed
 *)
(** Tactics used:
    change, 
    intros, apply, exact, split,
    discriminate, congruence   
 *)