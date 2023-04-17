(** Step through the teaser file and relate what you see to what is discussed in the first chapter “Getting Started” of MPCTT. You want to understand the inductive proofs first. Next try to understand how the inductive functions “min” and “iter” are defined in Coq. Note that “Fixpoint” is Coq’s keyword for defining recursive functions. *)


Fact addO x :
  x + 0 = x.
Proof.
  induction x as [|x IH].
  - reflexivity.
  - cbn. rewrite IH. reflexivity.
Qed.

(* Note that types of variables are derived automatically *)

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
  - rewrite IH. rewrite addS. reflexivity.
Qed.

Fixpoint min x y :=
  match x, y with
  | 0, _ => 0
  | S x, 0 => 0
  | S x, S y => S (min x y)
  end.

Check min.

Arguments min : simpl nomatch.
(* Don't expose nested match upon simplification *)

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

(** Iteration *)

Fixpoint iter (X: Type) (f: X -> X) (n:nat) (x:X) : X :=
  match n with
  | 0 => x
  | S n' => f (iter X f n' x)
  end.

Check iter.

Arguments iter {X}.
(* Make first argument implicit *)

Fact iter_add n x :
  n + x = iter S n x.
Proof.
  induction n as [|n IH]; cbn.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Fact iter_shift X f n x :
  @iter X f (S n) x = iter f n (f x).
(* Help type inference with "@iter X" *)
Proof.
  induction n as [|n IH].
  - reflexivity.
  - cbn.  rewrite <-IH. reflexivity.
Qed.

(** Fibonacci function with iter and unfolding function *)

Definition Fib f n :=
  match n with
  | 0 => 0
  | 1 => 1
  | S(S n) => f n + f (S n)
  end.

Check Fib.

Definition step a := (snd a, fst a + snd a).

Definition fib n := fst (iter step n (0,1)).

Compute fib 10.

Fact fib_correct n :
  fib n = Fib fib n.
Proof.
  destruct n as [|n].
  - reflexivity.
  - destruct n as [|n].
    + reflexivity.
    + reflexivity.
Qed.

(* Remark: If you put a ";cbn" after the two destructs, the proof still goes through but you see things you don't want to see.  Getting simplification right in Coq is tricky. *)
