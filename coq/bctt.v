
(** Beta and zeta reduction *)

Eval cbv beta in (fun x => x + x) (2 * 3).
Eval cbv zeta in let x := 2 * 5 in x + x.

(** Delta reduction *)

Definition T : nat -> nat :=
  fun x => S (S x).

Goal
  T 1 = 3.
Proof.
  cbv delta [T].
  cbv beta.
Abort.

(** Match reduction *)

Definition P : nat -> nat :=
  fun x => match x with 0 => 0 | S x' => x' end.

Goal
  P 2 = 1.
Proof.
  cbv delta [P].
  cbv beta.
  cbv match.
  cbv beta.
Abort.

(** Fix reduction *)

Definition D: nat -> nat :=
  fix f x := match x with 0 => 0 | S x' => S (S (f x')) end.

Goal
  D 1 = 2.
Proof.
  cbv delta [D].
  cbv fix. fold D.
  cbv beta.
  cbv match. cbv beta.
  cbv delta [D].
  cbv fix. fold D.
  cbv beta.
  cbv match.
Abort.

Goal
  D 1 = 2.
Proof.
  cbv delta [D].
  cbv fix. cbv beta.
  cbv match. cbv beta.
  cbv fix. cbv beta.
  cbv match.
Abort.

Example demo n :
  D (S n) = S (S (D n)).
Proof.
  set (a:= S (S (D n))).
  cbv delta [D]. cbv fix. fold D. cbv beta.
  cbv match. cbv beta.
  subst a.
Abort.

Locate "+".
Import Nat. (* Write add for Nat.add *)
Print add.

Example demo x :
  2 + x = S (S x).
Proof.
  cbv delta [add]. cbv fix. fold add. cbv beta.
  cbv match. cbv beta.
  cbv delta [add]. cbv fix. fold add. cbv beta.
  cbv match. cbv beta.
  cbv delta [add]. cbv fix. fold add. cbv beta.
  cbv match.
Abort.
 
Example demo x y :
  S (S x) + y = S (S (x + y)).
Proof.
  set (a:= x+y).
  cbv delta [add]. cbv fix. fold add. cbv beta.
  cbv match. cbv beta.
  cbv delta [add]. cbv fix. fold add. cbv beta.
  cbv match. cbv beta.
  subst a.
Abort.

(** We compute normal forms of terms describing functions *)

Compute add 0.
Compute add 1.
Compute add 2.
Compute fun x => 3 + x - 2.

(** Alpha conversion *)

Goal
  (fun n: nat => n) = (fun x => x).
Proof.
  reflexivity.
Abort.

(** Eta conversion *)

Goal
  add 1 = S.
Proof.
  cbv.
  change (S = S).
Abort.

Goal
  (fun x => 3 + x - 2) = S.
Proof.
  cbv.
  change (S = S).
Abort.

(* We use the predefined iter, which has arguments swapped *)

Check iter.
Eval cbv in iter.
Eval cbv in iter 2 S.
Eval cbv in add 2 = iter 2 S.

Inductive Pair X Y : Type :=
  pair: X -> Y -> Pair X Y.
Check Pair.
Check pair.

Definition swap :=
  fun X Y a => match a with pair _ _ x y => pair Y X y x end.

Print swap.

Example demo X Y x y :
  swap X Y (pair X Y x y) = pair Y X y x.
Proof.
  cbv delta. cbv beta. cbv match. cbv beta.
Abort.

(** If-then-else and let notations *)

Set Printing All.

Check fun b: bool => if b then false else true.

Check fun a: Pair nat nat => let (x,y) := a in pair nat nat y x.

(** Matches are equipped with return types,
    simple function types are printed as dependent function types *)

Unset Printing All.

Check fun b: bool => if b then false else true.
Check fun a: prod nat nat => let (x,y) := a in pair nat nat y x.

(** Commands used:
    Abort, Example, Eval 
 *)
(** Tactics used:
    cbv, fold, set, subst
 *)
