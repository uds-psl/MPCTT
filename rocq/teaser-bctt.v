Definition P : nat -> nat :=
  fun x => match x with 0 => 0 | S x' => x' end.

Goal
  P 2 = 1.
Proof.
  cbv delta [P].
  cbv beta.
  cbv match.
Abort.

Definition D: nat -> nat :=
  fix f x := match x with 0 => 0 | S x' => S (S (f x')) end.

Print D.

Goal
  D 1 = 2.
Proof.
  cbv delta [D].
  cbv fix. fold D.
  cbv beta.
  cbv match.
  cbv delta [D].
  cbv fix. fold D.
  cbv beta.
  cbv match.
Abort.

Example demo n :
  D (S n) = S (S (D n)).
Proof.
  set (a:= S (S (D n))).
  cbv delta [D]. cbv fix. fold D. cbv beta.
  cbv match.
  subst a.
Abort.

