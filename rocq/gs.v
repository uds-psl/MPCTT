(*** MPCTT, Chapter 1 *)

(* Step through the commands and proofs 
   and try to understand what is happening.
   The main point is to understand 
   how theorems are stated and proved. *)       

(** Booleans *)

Check negb.
Compute negb true.

Fact negb_involutive b :
  negb (negb b) = b.
Proof.
  destruct b.
  - reflexivity.
  - reflexivity. 
Qed.

(** Commutativity of addition *)

Compute 4 + 3.
Check 4 + 3.

Fact add0 x :
  x + 0 = x.
Proof.
  induction x as [|x IH].
  - reflexivity.
  - cbn. f_equal. exact IH.
Qed.

Fact addS x y:
  x + S y = S (x + y).
Proof.
  induction x as [|x IH].
  - reflexivity.
  - cbn. f_equal. exact IH.
Qed.

Fact add_comm x y:
  x + y = y + x.
Proof.
  induction x as [|x IH]; cbn.
  - symmetry. apply add0.
  - rewrite addS. f_equal. exact IH.
Qed.

(** Subtraction *)

Compute 7 - 3.
Compute 3 - 7.

Fact sub_xx x :
  x - x = 0.
Proof.
  induction x as [|x IH]; cbn.
  - reflexivity.
  - exact IH.
Qed.

Fact add_sub x y :
  (x + y) - x = y.
Proof.
  induction x as [|x IH]; cbn.
  - destruct y; reflexivity.
  - exact IH.
Qed.
  
Fact add_sub' x y :
  (x + y) - y = x.
Proof.
  rewrite add_comm. apply add_sub.
Qed.

(** Distance, quantified inductive hypothesis *)

Fixpoint D x y :=
  match x, y with
  | 0, 0 => 0
  | 0, S y => S y
  | S x, 0 => S x
  | S x, S y => D x y
  end.

Compute D 7 3.
Compute D 3 7.

Fact D_comm x y :
  D x y = D y x.
Proof.
  revert y.
  induction x as [|x IH]; intros y.
  - destruct y; reflexivity.
  - destruct y; cbn.
    + reflexivity.
    + apply IH.
Qed.

Fact D_sub x y :
  D x y = (x - y) + (y - x).
Proof.
  revert y.
  induction x as [|x IH]; intros y.
  - destruct y; reflexivity.
  - destruct y; cbn.
    + rewrite add0. reflexivity.
    + apply IH.
Qed.

(** Pairs *)

Definition swap {X Y} (a: X * Y) : Y * X :=
  match a with (x, y) => (y, x) end.

Compute swap (3,5).

Fact swap_swap X Y (a: X * Y) :
  swap (swap a) = a.
Proof.
  destruct a as [x y]. reflexivity.
Qed.

Fact pair_eta X Y (a: X * Y) :
  (fst a, snd a) = a.
Proof.
  destruct a as [x y]. reflexivity.
Qed.

(* Printing of implicit arguments can be forced *)
Set Printing Implicit.
Check swap (3,5).
Check swap_swap.
Check pair_eta.
Unset Printing Implicit.

(* Everything can be printed *)
Set Printing All.
Check 1+2.
Check swap (1,2).
Check pair_eta.
Check nat -> nat.
Unset Printing All.

(* Printing of defined notations can be swiched off *)
Unset Printing Notations.
Check 2+3.
Check swap (1,2).
Check pair_eta.
Set Printing Notations.

(* ADVICE: Rocq comes with lots of  notational conveniences,
   including infix operators, argument inference, and implicit arguments.
   This can be confusing.  It is important to understand 
   what a phrase elaborates to once all notational conveniences are removed. *)

(** Iteration *)

Fixpoint iter {X: Type} (f: X -> X) (n:nat) (x:X) : X :=
  match n with
  | 0 => x
  | S n => f (iter f n x)
  end.

Fact iter_add n x :
  n + x = iter S n x.
Proof.
  induction n as [|n IH]; cbn.
  - reflexivity.
  - f_equal. exact IH.
Qed.

Fact iter_mul n x :
  n * x = iter (Nat.add x) n 0.
Proof.
  induction n as [|n IH]; cbn.
  - reflexivity.
  - f_equal. exact IH.
Qed.

Fact iter_pow n x :
  Nat.pow x n = iter (Nat.mul x) n 1.
Proof.
  induction n as [|n IH]; cbn.
  - reflexivity.
  - f_equal. exact IH.
Qed.

Fact iter_shift X (f: X -> X) n x :
  iter f (S n) x = iter f n (f x).
Proof.
  induction n as [|n IH].
  - cbn. reflexivity.
  - cbn. f_equal. exact IH.
Qed.

Fact iter_shift' X (f: X -> X) n x :
  f (iter f n x) = iter f n (f x).
Proof.
  rewrite <-iter_shift. reflexivity.
Qed.

(* Warning: Predefined iter has different argument order *)
Check Nat.iter.

(** Factorial *)

Fixpoint fac (n: nat) : nat :=
  match n with
  | 0 => 1
  | S n => S n * fac n
  end.

Definition fac_step (a: nat * nat) : nat * nat :=
  (S (fst a), S (fst a) * snd a).

Fact iter_fact n :
    (n, fac n) = iter fac_step n (0,1).
Proof.
  induction n as [|n IH].
  - reflexivity.
  - cbn. rewrite <-IH. reflexivity.
Qed.

(** Even *)

Definition Even f n :=
  match n with
  | 0 => true
  | 1 => false
  | S (S n) => f n
  end.

Fixpoint even n :=
  match n with
  | 0 => true
  | S n => negb (even n)
  end.

Fact even_correct n :
  even n = Even even n.
Proof.
  destruct n. reflexivity.
  destruct n. reflexivity.
  cbn. apply negb_involutive.
Qed.

Definition even_iter n := iter negb n true.

Fact even_iter_correct n :
  even_iter n = Even even_iter n.
Proof.
  destruct n. reflexivity.
  destruct n. reflexivity.
  cbn. apply negb_involutive.
Qed.

(** Fibonacci function *)

Definition Fib f n :=
  match n with
  | 0 => 0
  | 1 => 1
  | S (S n) => f n + f (S n)
  end.

Fixpoint fib_bool' n b :=
  match n, b with
  | 0, false => 0
  | 0, true => 1
  | S n, false => fib_bool' n true
  | S n, true => fib_bool' n false + fib_bool' n true
  end.

Definition fib_bool n := fib_bool' n false.

Check fib_bool.
Compute fib_bool 10.

Fact fib_bool_correct n :
  fib_bool n = Fib fib_bool n.
Proof.
  destruct n. reflexivity.
  destruct n. reflexivity.
  reflexivity.
Qed.

Definition fib_step (a: nat * nat) := (snd a, fst a + snd a).
Definition fib_iter n := fst (iter fib_step n (0,1)).

Check fib_iter.
Compute fib_iter 10.

Fact fib_iter_correct n :
  fib_iter n = Fib fib_iter n.
Proof.
  destruct n. reflexivity.
  destruct n. reflexivity.
  reflexivity.
Qed.

(** Ackermann function *)

Definition Acker f x y :=
  match x, y with
  | 0, y => S y
  | S x, 0 => f x 1
  | S x, S y => f x (f (S x) y)
  end.

Fixpoint acker' (f: nat -> nat) (x:nat) : nat :=
  match x with
  | 0 => f 1
  | S x => f (acker' f x)
  end.

Fixpoint acker (x:nat) : nat -> nat :=
  match x with
  | 0 => S
  | S x => acker' (acker x)
  end.

Check acker.
Compute acker 3 5.

Fact acker_correct x y :
  acker x y = Acker acker x y.
Proof.
  destruct x. reflexivity.
  destruct y. reflexivity.
  reflexivity.
Qed.

Definition B f y := iter f (S y) 1.
Definition A x := iter B x S.

Check A.
Compute A 3 5.

Fact acker_iter_correct x y :
  A x y = Acker A x y.
Proof.
  destruct x. reflexivity.
  destruct y. reflexivity.
  reflexivity.
Qed.

(** Automation available for arithmetic proofs. *)
From Stdlib Require Import Lia.

Goal forall x y, x + y - y = x.
Proof.
  lia.
Qed.
Goal forall x y, x * y  = y * x.
Proof.
  lia.
Qed.
Goal forall x y z, x * y * z = (x * y) * z.
Proof.
  lia.
Qed.
Goal forall x y z, x*(y + z) = x*y + x*z.
Proof.
  lia.
Qed.

(** Tactics used:
    reflexivity, symmetry, f_equal, cbn, rewrite,      
    apply, exact, destruct, induction, intros,
    lia *) 
