From Stdlib Require Import List.
Import ListNotations.

Inductive exp : Type :=
| con: nat -> exp
| var: nat -> exp
| sub: exp -> exp -> exp.

Fixpoint lin (e: exp) : list nat :=
  match e with
  | con x => [S(S x)]
  | var x => [S(S x); 0]
  | sub e1 e2 => lin e1 ++ lin e2 ++ [1]
  end.

Fixpoint delin (A: list nat) (B: list exp) : list exp :=
  match A, B with
  | 0::A, con x :: B => delin A (var x :: B)
  | 1::A, e2::e1::B => delin A (sub e1 e2 :: B)
  | S(S x)::A, B => delin A (con x :: B)
  | _, B => B
  end.

Arguments delin : simpl nomatch.

Compute lin (sub (sub (con 3) (con 5)) (var 2)).
Compute delin (lin (sub (sub (con 3) (con 5)) (var 2))) [].

Fact delin_correct e A B :
  delin (lin e ++ A) B = delin A (e::B).
Proof.
  induction e as [x|x|e1 IH1 e2 IH2] in A,B|-*; cbn.
  - reflexivity.
  - reflexivity.
  - do 2 rewrite <-(app_assoc _ _ A). 
    rewrite IH1.  rewrite IH2. cbn.
    reflexivity.
Qed.

Fact delin_lin e :
  delin (lin e) [] = [e].
Proof.
  rewrite <-(app_nil_r (lin e)).
  apply delin_correct.
Qed.

Definition delin' A :=
  match delin A [] with [e] => e | _ => var 777 end.

Goal forall e, delin' (lin e) = e.
  intros e.
  unfold delin'.
  rewrite delin_lin.
  reflexivity.
Qed.
