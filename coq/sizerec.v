From Coq Require Import Arith Lia.
Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.
Notation pi1 := projT1.
Notation pi2 := projT2.

Definition size_rec {X: Type} (sigma: X -> nat) {p: X -> Type} :
  (forall x, (forall y, sigma y < sigma x -> p y) -> p x) ->
  (forall x, p x).
Proof.
  intros F.
  enough (forall n x, sigma x < n -> p x) as H.
  { intros x. apply (H (S (sigma x))). lia. }
  induction n as [|n IH]; intros x H.
  - exfalso. lia.
  - apply F. intros y H1. apply IH. lia.
Defined.

Definition size_rec2 {X Y: Type} (sigma: X -> Y -> nat) {p: X -> Y -> Type} :
  (forall x y, (forall x' y', sigma x' y' < sigma x y -> p x' y') -> p x y) ->
  (forall x y, p x y).
Proof.
  intros F.
  enough (forall '(x,y), p x y) as H.
  { intros x y. apply (H (x,y)). } 
  refine (size_rec (fun '(x,y) => sigma x y) (fun '(x,y) IH => _)). cbn in IH.
  apply F. intros x' y' H. apply (IH (x',y')), H.
Defined.

(** Euclidean Division *)

Definition div_rec (y: nat) {p: nat -> Type} :
  (forall x, x <= y -> p x) ->
  (forall x, x > y -> p (x - S y) -> p x) ->
  forall x, p x.
Proof.
  intros e1 e2.
  apply (size_rec (fun x => x)).
  intros x IH.
  destruct (le_lt_dec x y) as [H|H].
  - apply e1. exact H.
  - apply e2. exact H. apply IH. lia.
Defined.

Definition Div : forall x y, Sigma k, k * S y <= x < S k * S y.
Proof.
  intros x y. revert x. apply (div_rec y).
  - intros x H. exists 0. lia.
  - intros x H [k H1]. exists (S k). lia.
Defined.

Definition div (x y: nat) : nat :=
  match y with
  | 0 => 0
  | S y' => pi1 (Div x y')
  end.

Compute div 7 3.
Goal div 48 8 = 6.
  reflexivity.
Qed.

Definition div' : nat -> nat -> nat.
Proof.
  intros x [|y]. exact 0.
  revert x. apply (div_rec y).
  - exact (fun _ _ => 0).
  - exact (fun _ _ => S).
Defined.

Compute div' 7 3.
Goal div 48 8 = 6.
  reflexivity.
Qed.

(** Greatest common divisors *)

Definition gcd_rec (p: nat -> nat -> Type) :
  (forall x, p x 0) ->
  (forall x y, p y x -> p x y) ->
  (forall x y, x <= y -> p x (y - x) -> p x y) ->
  forall x y, p x y.
Proof.
  intros e1 e2 e3.
  apply (size_rec2 (fun x y => x + y)).
  intros x y IH.
  destruct y.
  - apply e1.
  - destruct x.
    + apply e2,e1.
    + destruct (le_lt_dec x y) as [H|H].
      * apply e3. lia. apply IH. lia.
      * apply e2,e3. lia. apply IH. lia.
Defined.

Definition gcd : nat -> nat -> nat.
Proof.
  apply (gcd_rec (fun _ _ => nat)).
  - exact (fun x => x).
  - exact (fun _ _ x => x).
  - exact (fun _ _ _ x => x).
Defined.

Compute gcd 49 63.
Goal gcd 49 63 = 7.
  reflexivity.
Qed.
  
(** Fibonacci *)

Definition Phi (f: nat -> nat) (n: nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | S (S n') => f n' + f (S n')
  end.

Definition fib_rec {p: nat -> Type} :
  p 0 ->
  p 1 ->
  (forall n, p n -> p (S n) -> p (S(S n))) ->
  forall n, p n.
Proof.
  intros e1 e2 e3.
  apply (size_rec (fun n => n)).
  intros n IH.
  destruct n. exact e1.
  destruct n. exact e2.
  apply e3; apply IH; lia.
Defined.

Notation agree f g := (forall n, f n = g n).

Fact phi_unique f g :
  agree f (Phi f) -> agree g (Phi g) -> agree f g.
Proof.
  intros H1 H2. apply fib_rec.
  - rewrite H1, H2. reflexivity.
  - rewrite H1, H2. reflexivity.
  - intros n IH1 IH2. rewrite H1, H2. cbn. f_equal; assumption.
Qed.

Fixpoint Fib k n :=
  match k with
  | 0 => 0
  | S k' => match n with
           | 0 => 0
           | 1 => 1
           | S (S n') => Fib k' n' + Fib k' (S n')
           end
  end.
Arguments Fib : simpl nomatch.

Fact Fib_index :
  forall n k k', n < k -> n < k' -> Fib k n = Fib k' n.
Proof.
  refine (fib_rec _ _ _).
  - intros [|k]. lia. intros [|k']. lia. easy.
  - intros [|k]. lia. intros [|k']. lia. easy.
  - intros n IH1 IH2 k k' H1 H2.
    destruct k. lia. destruct k'. lia. cbn. f_equal.
    + apply IH1; lia.
    + apply IH2; lia.
Qed.
  
Definition fib n := Fib (S n) n.

Compute fib 10.

Fact Phi_fib :
  agree fib (Phi fib).
Proof.
  intros [|n]. reflexivity.
  destruct n. reflexivity.
  cbn. unfold fib. f_equal. apply Fib_index; lia.
Qed.

Definition fib' : nat -> nat.
Proof.
  refine (fib_rec 0 1 _).
  exact (fun n a b => a + b).
Defined.

Goal fib 10 = fib' 10.
  reflexivity.
Qed.

