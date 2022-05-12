Section Equality.
  Variable eq : forall X, X -> X -> Prop.
  Variable Q : forall X x, eq X x x.
  Variable R : forall X x y (p: X -> Prop), eq X x y -> p x -> p y.

  Arguments eq {X}.
  Arguments Q {X}.
  Arguments R {X x y}.
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

Fact eq_sym X (x y: X) :
  x = y -> y = x.
Proof.
  intros H.
  change ((fun z => z = x) y).
  apply (R _ H).
  exact (Q x).
  Show Proof.
Qed.

Fact eq_trans X (x y z: X) :
  x = y -> y = z -> x = z.
Proof.
  intros e.
  change ((fun y => y = z -> x = z) y).
  apply (R _ e).
  exact (fun e => e).
  Show Proof.
Qed.

Fact eq_trans' X (x y z: X) :
  x = y -> y = z -> x = z.
Proof.
  intros e1 e2.
  exact (R _ e2 e1).
  Show Proof.
Qed.

Fact f_eq {X Y} (f: X -> Y) {x x'} :
    x = x' -> f x = f x'.
Proof.
  intros H.
  change ((fun z => f x = f z) x').
  apply (R _ H).
  exact (Q (f x)).
  Show Proof.     
Qed.

Definition pred (x: nat) : nat :=
  match x with 0 => 0 | S x' => x' end.

Goal forall x y, S x = S y -> x = y.
Proof.
  intros x y H.
  exact (f_eq pred H).
Qed.

Goal true <> false.
Proof.
  intros H.
  enough (True = False) as H1.
  - exact (R (fun a => a) H1 I).
  - exact (f_eq (fun x:bool => if x then True else False) H).
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

Goal forall x, S x <> 0.
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

Goal forall x y, S x = S y -> x = y.
Proof.
  intros x y [= <-]. reflexivity. 
Qed.



(** Leibniz definition of equality *)

Module Type EQ.
  Parameter eq : forall X, X -> X -> Prop.
  Parameter Q : forall X x, eq X x x.
  Parameter R : forall X x y (p: X -> Prop), eq X x y -> p x -> p y.
End EQ.

Module EqLeibniz : EQ.
  Definition eq X x y := forall p: X -> Prop, p x -> p y.
  Definition Q X x : eq X x x := fun p a => a.
  Definition R X x y p (f: eq X x y) := f p.
End EqLeibniz.

Fail Print R.
Print EqLeibniz.R.

Import EqLeibniz.
Print R.
