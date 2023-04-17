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



