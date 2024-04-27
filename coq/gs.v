(*** MPCTT, Chapter 1 *)

(* Step through the commands and proofs 
   and try to understand what is happening *)

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

(** There is a command printing all defined constants *)
Print All.
Print Fib.
Print negb.

(** Automation available for arithmetic proofs. *)
From Coq Require Import Lia.

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
    apply, exact, destruct, induction, intros
    lia *) 






Print nat.
Check S (S O).
Compute 2 + 7.
Locate "+".
Print Nat.add.







(** We first give some basic definitions.  We enclose them in a module
    so that afterwards we can use the definitions from the standard library.  *)

Module Definitions.
 
  Inductive bool : Type :=
  | true : bool
  | false : bool.
 
  Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

  Inductive Pair (X Y: Type) : Type :=
  | pair : X -> Y -> Pair X Y.

  Definition negb (x: bool) : bool :=
    match x with
    | true => false
    | false => true
    end.

  Definition andb (x y: bool) : bool :=
    match x with
    | true => y
    | false => false
    end.

  Definition orb (x y: bool) : bool :=
    match x with
    | true => true
    | false => y end.
  
  Fixpoint add (x y: nat) : nat :=
    match x with
    | O => y
    | S x' => S (add x' y)
    end.
  
  Fixpoint mul (x y: nat) : nat :=
    match x with
    | O => O
    | S x' => add y (mul x' y)
    end.

  Fixpoint sub (x y: nat) : nat :=
    match x, y with
    | O, _  => O
    | S x', O => x
    | S x', S y' => sub x' y'
    end.
  
  Definition test (X Y: Type) (a: Pair X Y) : Pair Y X := 
    match a with
    |  pair _ _ x y => pair _ _ y x
    end.

  Check pair.
  Check pair nat.
  Check pair nat bool.
  Check pair nat bool (S O).
  Check pair nat bool (S O) false.
  Check pair _ _ (S O) false.
  
  Arguments pair {X Y}.
  Check pair (S O) false.
  Check pair.
  Check @pair.
  Check @pair nat.
  Check @pair nat bool.
  Check @pair nat bool (S O).
  
  Definition swap {X Y: Type} (a: Pair X Y) : Pair Y X := 
    match a with
    |  pair x y => pair y x
    end.

  Definition fst {X Y: Type} (a: Pair X Y) : X :=
    match a with
    |  pair x _ => x
    end.

  Definition snd {X Y: Type} (a: Pair X Y) : Y :=
    match a with
    |  pair _ y => y
    end.

  Check negb.
  Compute negb (negb (negb true)).
  Check orb.
  Compute orb false true.
  Check mul.
  Compute mul (S (S O)) (S (S (S O))).
  Compute sub (S (S (S O))) (S (S O)).
  Check swap.
  Check swap (pair O true).
  Compute swap (pair O true).
End Definitions.

Check Definitions.orb.
Check Definitions.swap.

(** We now switch to the definitions from the library.  
    They come with convenient notations.        *)

Locate "+".
Check Nat.add.
Check Nat.sub.
Check Nat.mul.
Print Nat.add.
Print Nat.mul.

Check nat.
Check bool.
(** Read "Set" as "Type" *)
Print nat.
Print bool.

From Coq Require Import Bool.

Fact L11 x :
  negb (negb x) = x.
Proof.
  destruct x.
  - cbn. reflexivity.
  - cbn. reflexivity.
Qed.

Fact L12 x y :
  x && y = y && x.
Proof.
  destruct x.
  - cbn. destruct y.
    + cbn. reflexivity.
    + cbn. reflexivity.
  - cbn. destruct y.
    + cbn. reflexivity.
    + cbn. reflexivity.
Qed.

Fact L12' x y :
  x && y = y && x.
Proof.
  destruct x, y; reflexivity.
Qed.

Fact L13 x y z :
  x && (y || z) = x && y || x &&z.
Proof.
  destruct x.
  - cbn. reflexivity.
  - cbn. reflexivity.
Qed.

(** if-then-else notation *)

Fact L14 (x: bool) :
  (if x then false else true) = match x with true => false | false => true end.
Proof.
  reflexivity.
Qed.



(** Quantified inductive hypothesis *)

Fixpoint D (x y: nat) : nat :=
  match x, y with
  | 0, y => y
  | S x, 0 => S x
  | S x, S y => D x y
  end.

Arguments D : simpl nomatch.

Fact D_com x y :
  D x y = D y x.
Proof.
  induction x as [|x IH].
  - destruct y; reflexivity.
  - destruct y.
    + reflexivity.
    + cbn.
Abort.

Fact D_com x y :
  D x y = D y x.
Proof.
  revert y.
  induction x as [|x IH].
  - destruct y; reflexivity.
  - destruct y.
    + reflexivity.
    + cbn. apply IH.
Qed.

Fact D_eq x y :
  D x y = (x - y) + (y - x).
Proof.
  revert y.
  induction x as [|x IH]; destruct y; cbn.
  - reflexivity.
  - reflexivity.
  - rewrite add0. reflexivity.
  - exact (IH y).
Qed.

(** Specifying equations **)

Fixpoint even x :=
  match x with
  | 0 => true
  | S x => negb (even x)
  end.

(** Fibonacci function *)

Fixpoint fib' n b :=
  match n, b with
  | 0, false => 0
  | 0, true => 1
  | S n, false => fib' n true
  | S n, true => fib' n false + fib' n true
  end.

Definition fib n := fib' n false.

Fact fib_eq3 n :
   fib (S (S n)) = fib n + fib (S n).
Proof.
  reflexivity.
Qed.

(** We now use the predefined pairs. *)

Locate "*".
Print pair.

(** We define a polymorphic swap function with
    implicit arguments. *)

Definition swap {X Y: Type} (a: X * Y) : Y * X := 
  match a with (x,y) => (y,x) end.

Fact swap_swap X Y (a: X * Y) :
  swap (swap a) = a.
Proof.
  destruct a as [x y]. cbn. reflexivity.
Qed.

Fact eta_law X Y (a: X * Y) :
  (fst a, snd a) = a.
Proof.
  destruct a as [x y]. cbn. reflexivity.
Qed.

(** Syntactic sugar and type inference *)

Definition swap' {X Y} '(x,y) : Y * X := (y,x).

Goal @swap' = @swap.
Proof.
  reflexivity.
Qed.

(** We make the objects of the predefined module Nat available
    without the module prefix, for instance, add rather than Nat.add. *) 

Print Nat.
Import Nat.
Check add.
Check sub.

(** Polymorphic iteration *)

Fixpoint iter {X: Type} (f: X -> X) (n:nat) (x:X) : X :=
  match n with
  | 0 => x
  | S n' => f (iter f n' x)
  end.

Fact iter_add n x :
  n + x = iter S n x.
Proof.
  induction n as [|n IH]; cbn.
  - reflexivity.
  - f_equal. exact IH.
Qed.

Definition add_iter (x y: nat) : nat := iter S x y.

Fact add_iter_eq1 y :
  add_iter 0 y = y.
Proof.
  reflexivity.
Qed.
  
Fact add_iter_eq2 x y :
  add_iter (S x) y = S (add_iter x y).
Proof.
  reflexivity.
Qed.
  
Fact iter_mul n x :
  n * x = iter (add x) n 0.
Proof.
  induction n as [|n IH]; cbn.
  - reflexivity.
  - f_equal. exact IH.
Qed.

Fact iter_pow n x :
  x^n = iter (mul x) n 1.
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
  induction n as [|n IH].
  - cbn. reflexivity.
  - cbn. f_equal. exact IH.
Qed.

Module Iter_Factorial.
  Fixpoint fac (n :nat) : nat :=
    match n with
    | 0 => 1
    | S n' => S n' * fac n'
    end.

  Definition sigma '(n, a) := (S n, S n * a).

  Fact iter_fact n :
    (n, fac n) = iter sigma n (0,1).
  Proof.
    induction n as [|n IH].
    - cbn. reflexivity.
    - cbn [iter sigma fac]. rewrite <-IH. reflexivity.
  Qed.

  Compute fac 5.
  Compute iter sigma 5 (0,1).
End Iter_Factorial.

Module Fib_Iter.
  Definition sigma c := (snd c, fst c + snd c).
  Definition fib n := fst (iter sigma n (0, 1)).
  Fact fib_eq0 :
    fib 0 = 0.
  Proof.
    reflexivity.
  Qed.
  Fact fib_eq1 :
    fib 1 = 1.
  Proof.
    reflexivity.
  Qed.
  Fact fib_eq3 n :
    fib (S (S n)) = fib n + fib (S n).
  Proof.
    reflexivity.
  Qed.
End Fib_Iter.

(** Ackermann function *) 

Fixpoint acker' (f: nat -> nat) (x:nat) : nat :=
  match x with
  | 0 => f 1
  | S x' => f (acker' f x')
  end.

Fixpoint acker (x:nat) : nat -> nat :=
  match x with
  | 0 => S
  | S x' => acker' (acker x')
  end.

Fact acker_eq3 x y :
  acker (S x) (S y) = acker x (acker (S x) y).
Proof.
  cbn [acker]. cbn [acker']. reflexivity.
Qed.

Module Ack_Iter.
  Definition B f y := iter f (S y) 1.
  Definition A x := iter B x S.

  Fact eq1 y :
    A 0 y = S y.
  Proof.
    reflexivity.
  Qed.
  Fact eq2 x :
    A (S x) 0 = A x 1.
  Proof.
    reflexivity.
  Qed.
  Fact eq3 x y :
    A (S x) (S y) = A x (A (S x) y).
  Proof.
    reflexivity.
  Qed.
End Ack_Iter.

(** Truncating subtraction with single discriminating argument *)

Definition sub'' (f: nat -> nat) (x:nat) (y: nat) :=
  match y with
  | 0 => x
  | S y' => f y'
  end.

Fixpoint sub' (x y: nat) : nat :=
  match x with
  | 0 => 0
  | S x' => sub'' (sub' x') x y
  end.

Fact sub'_eq1 y :
  sub' 0 y = 0.
Proof.
  reflexivity.
Qed.

Fact sub'_eq2 x :
  sub' (S x) 0 = S x.
Proof.
  reflexivity.
Qed.

Fact sub'_eq3 x y :
  sub' (S x) (S y) = sub' x y.
Proof.
  reflexivity.
Qed.

Fact sub_sub' x :
  forall y, sub' x y = x - y.
Proof.
  induction x as [|x IH].
  - destruct y; reflexivity.
  - destruct y; cbn.
    + reflexivity.
    + exact (IH y).
Qed.

(** ADVICE: Coq comes with lots of involved notational conveniences,
    including infix operators, type inference, and implicit arguments.
    This can be confusing.  It is important to understand 
    what a phrase elaborates to once all notational conveniences are removed. *)

Print negb.
Set Printing All.
Print negb.
Print swap.
Print swap'.
Check 6.
Check 2+3.
             Unset Printing All.
Check 2 + 3.

(** There is a command that prints all defined constants *)

Print All.

Module Procedural_Specifications.
  Definition Fib f n :=
    match n with
    | 0 => 0
    | 1 => 1
    | S (S n) => f n + f (S n)
    end.

  Fact fib_bool_correct n :
    fib n = Fib fib n.
  Proof.
    destruct n. reflexivity.
    destruct n; reflexivity.
  Qed.

  Definition fib_iter := Fib_Iter.fib.
  Definition fib_iter_eq3 := Fib_Iter.fib_eq3.

  Fact fib_iter_correct n :
    fib_iter n = Fib fib_iter n.
  Proof.
    destruct n. reflexivity.
    destruct n. reflexivity.
    cbn [Fib]. apply fib_iter_eq3.
  Qed.

  Definition Acker f x y :=
    match x, y with
    | 0, y => S y
    | S x, 0 => f x 1
    | S x, S y => f x (f (S x) y)
    end.

  Fact ack_higher_correct x y :
    acker x y = Acker acker x y.
  Proof.
    destruct x. reflexivity.
    destruct y; cbn [Acker]; reflexivity.
  Qed.

  Definition ack_iter := Ack_Iter.A.

  Fact ack_iter_correct x y :
    ack_iter x y = Acker ack_iter x y.
  Proof.
    destruct x. reflexivity.
    destruct y; cbn [Acker]; reflexivity.
  Qed.
    
End Procedural_Specifications.
