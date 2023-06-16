From Coq Require Import Arith Lia.
Definition dec (X: Type) := sum X (X -> False).
Definition eqdec X := forall x y: X, dec (x = y).
Definition decidable X p := forall x:X, dec (p x).
Notation sig := sigT.
Notation Sig := existT.
Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.
From Coq Require Import List.
Import ListNotations.
Notation "x 'el' A" := (In x A) (at level 70).

Section List1.
  Variable X : Type.
  Implicit Types A B : list X.

  Goal forall x A B,
      x el A ++ B <-> x el A \/ x el B.
  Proof.
    intros x A B.
    induction A as [|a A IH]; cbn.
    - intuition.
    - intuition.
  Qed.
  
  Goal eqdec X -> eqdec (list X).
  Proof.
    intros d A.
    induction A as [|a A IH]; cbn.
    - intros [|b B].
      + left. easy.
      + right. easy.
    - intros [|x B].
      + right. easy.
      + destruct (d a x) as [H|H].
        * destruct (IH B) as [H1|H2].
          -- left. congruence.
          -- right. congruence.
        * right. congruence.
  Qed.
