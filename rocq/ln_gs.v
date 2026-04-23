(** Step through the teaser file and relate what you see to what is discussed in the first chapter “Getting Started” of MPCTT. You want to understand the inductive proofs first. Next try to understand how the inductive functions “min” and “iter” are defined in Rocq. Note that “Fixpoint” is Rocq’s keyword for defining recursive functions. *)


(* We take 'nat', '+', and '-' as predefined.
   First we demo simplification (reduction) with defining equations
   and computational equality.   *)             
   
Goal forall y, 0 + y = y.
Proof.
  intros y.
  cbn.  (*apply defining equations *)
  reflexivity.
Qed.

Goal forall x y, S x + y = S (x + y).
Proof.
  intros x y.
  cbn.
  reflexivity.
Qed

(* Note that types of variables are derived automatically *).

Goal forall x y, S x + y = S (x + y).
Proof.
  reflexivity.  (* check computational equality *)
Qed.

(** Induction rule for numbers *)
Check nat_ind.

(** Addition is commutative *)

Fact addO x :
  x + 0 = x.
Proof.
  induction x as [|x IH].
  - reflexivity.
  - cbn. rewrite IH. reflexivity.
Qed.

Fact addS x y :
  x + S y = S (x + y).
Proof.
  induction x as [|x IH].
  - reflexivity.
  - cbn. rewrite IH. reflexivity.
Qed.

Fact add_comm x y :
  x + y = y + x.
Proof.
  induction x as [|x IH]; cbn.
  - rewrite addO. reflexivity.
  - rewrite addS. rewrite IH. reflexivity.
Qed.

(* Rocq's arithmetic reasoner 'lia' automatically proves
   commutativity and other arithmetic properties *)

From Stdlib Require Import Lia.

Goal forall x y, x + y = y + x.
Proof.
  lia.
Qed.

(** Subtraction is defined as truncating subtraction *)

Compute 7 - 3.
Compute 3 - 7.

Goal forall x y,
    0 - y = 0
    /\ S x - 0 = S x
    /\ S x - S y =  x - y.
Proof.
  cbn. easy.
Qed.

Goal forall x,  x - x = 0.
Proof.
  induction x as [|x IH]; cbn.
  - reflexivity.
  - apply IH.
Qed.

Fact add_sub x y :
  (x + y) - x = y.
Proof.
  induction x as [|x IH]; cbn.
  - destruct y; reflexivity.
  - apply IH.
Qed.
  
Goal forall x y, (x + y) - y = x.
Proof.
  intros. rewrite add_comm. apply add_sub.
Qed.

Goal forall x y, (x + y) - y = x.
Proof.
  lia.
Qed.

(** Minimum function *)

Fixpoint min x y :=
  match x, y with
  | 0, _ => 0
  | S _, 0 => 0
  | S x, S y => S (min x y)
  end.

(* In Rocq, inductive function definitions must be done
   with 'match' and a single defining equation.
   Moreover, simplification must be told that
   there is secondary discrimination.   *)
Arguments min : simpl nomatch.
(* Don't expose nested match upon simplification *)

(** Commutativity proof needs quantified IH *)

Fact min_comm x y :
  min x y = min y x.
Proof.
  revert y.
  induction x as [|x IH]; cbn.
  - destruct y.
    + reflexivity.
    + reflexivity.
  - destruct y.
    + reflexivity.
    + cbn. rewrite IH. reflexivity.
Qed.

(* Shorter proof script possible with ';' and
   congruence tactic automating simple equational proofs. *)

Goal forall x y, min x y = min y x.
Proof.
  induction x; destruct y; cbn; congruence.
Qed.

(** Iteration *)

Fixpoint iter (X: Type) (f: X -> X) (n:nat) (x:X) : X :=
  match n with
  | 0 => x
  | S n' => f (iter X f n' x)
  end.

Check iter.
Check iter nat.
Check iter bool.

Arguments iter {X}.
(* Make first argument implicit *)

Fact iter_add n x :
  n + x = iter S n x.
Proof.
  induction n as [|n IH]; cbn.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Fact iter_shift X f n (x: X) :
  iter f (S n) x = iter f n (f x).
Proof.
  induction n as [|n IH].
  - reflexivity.
  - cbn. rewrite <-IH. reflexivity.
Qed.

(* Simple function are dependent function types
   where the argument variable does not occur
   in the target type *) 

Goal (nat -> nat) = (forall n:nat, nat).
Proof.
  reflexivity.
Qed.

(** Pairs *)

(* We use a module to protect the predefined pairs *)
Module Pair.
  Inductive Pair (X Y: Type) : Type :=
  | pair : X -> Y -> Pair X Y.

  Check Pair.
  Check pair.
  Check pair nat bool.
  Check Pair_ind.  (* Discrimination rule for pairs *)
  Arguments pair {X Y}.  (* declare arguments 'X' and 'Y' as implixit *)

  Definition swap {X Y} (a: Pair X Y) : Pair Y X :=
    match a with pair x y => pair y x end.
  (* Curly braces declare type arguments of swap implicit *)
  
  Goal forall X Y (a: Pair X Y),
      swap (swap a) = a.
  Proof.
    intros X Y.
    destruct a as [x y].  (* discrimination on 'a' *)
    cbn. reflexivity.
  Qed.

  Definition fst {X Y} (a: Pair X Y) : X :=
    match a with pair x y => x end.
  
  Definition snd {X Y} (a: Pair X Y) : Y :=
    match a with pair x y => y end.

  Fact eta_law X Y (a: Pair X Y) :
    pair (fst a) (snd a) = a.
  Proof.
    destruct a as [x y]. cbn. reflexivity.
  Qed.

  
  Definition swap' {X Y} (a: Pair X Y) : Pair Y X :=
    pair (snd a) (fst a).

  Goal forall X Y (a: Pair X Y),
      swap' (swap' a) = a.
  Proof.
    intros X Y a.
    unfold swap'.
    destruct a as [x y]. cbn. reflexivity.
  Qed.
End Pair.

(** Fibonacci sequence with iteration on pairs *)

Definition step a := (snd a, fst a + snd a).

Definition fib n := fst (iter step n (0,1)).

Compute fib 10.

Goal forall n, fib (S (S n)) = fib n + fib (S n).
Proof.
  intros n. unfold fib. cbn. reflexivity.
Qed.

(* Step can also be defined as inductive function *)

Definition Step a := match a with (x,y) => (y, x + y) end.

Definition Fib n := fst (iter Step n (0,1)).

Compute Fib 10.

Goal forall n, Fib (S (S n)) = Fib n + Fib (S n).
Proof.
  intros n. unfold Fib. cbn.
  (* pattern (iter Step n (0,1)). explains it. *)
  destruct (iter Step n (0, 1)) as [x y].
  cbn. reflexivity.
Qed.
