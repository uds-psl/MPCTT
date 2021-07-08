Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).
Notation pi1 := projT1.
Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Definition dec (X: Type) := sum X (X -> False).

Fact dec_boolean X (p: X -> Prop) :
  (forall x, dec (p x)) <=> Sigma f, forall x, p x <-> f x = true.
Proof.
  split.
  - intros F.
    exists (fun x => if F x then true else false).
    intros x.
    destruct (F x) as [H|H];
      intuition congruence.
  - intros [f H] x. specialize (H x). unfold dec.
    destruct (f x);
      intuition congruence.
Qed.

Fact dec_prop_impl P Q:
  dec P -> dec Q -> dec (P -> Q).
Proof.
  unfold dec. intuition.
Qed.

Definition dec_iff_invariance {X Y} :
  X <=> Y -> dec X -> dec Y.
Proof.
  intros H [H1|H1].
  - left. apply H, H1.
  - right. intros y. apply H1, H, y.
Defined.

Definition dec2bool {X} : dec X -> bool :=
  fun a => if a then true else false.


(*** Equality Deciders *)

Definition eqdec X := forall x y: X, dec (x = y).

Definition nat_eqdec : eqdec nat.
Proof.
  hnf. induction x as [|x IH]; destruct y.
  - left. reflexivity.
  - right. congruence.
  - right. congruence.
  - destruct (IH y) as [H|H].
    + left. congruence.
    + right. congruence.
Defined.

Compute dec2bool (nat_eqdec 3 5).

Definition option_eqdec {X} :
  eqdec X -> eqdec (option X).
Proof.
  intros H [x|] [y|].
  - specialize (H x y) as [H|H].
    + left. congruence.
    + right. congruence.
  - right. congruence.
  - right. congruence.
  - left. reflexivity.
Defined.

Compute dec2bool (option_eqdec nat_eqdec (Some 3) (Some 5)).

(*** Bijection Theorem for Option Types *)

Definition inv {X Y: Type} (g: Y -> X) (f: X -> Y) := forall x, g (f x) = x.

Inductive bijection (X Y: Type) : Type :=
| Bijection: forall (f: X -> Y) (g: Y -> X), inv g f -> inv f g -> bijection X Y.
Arguments Bijection {X Y}.

Fact R {X Y f g} :
  @inv (option X) (option Y) g f ->
  forall x, Sigma y, match f (Some x) with Some y' => y = y' | None => f None = Some y end.
Proof.
  intros H x.
  destruct (f (Some x)) as [y|] eqn:E1.
  - exists y. reflexivity.
  - destruct (f None) as [y|] eqn:E2.
    + exists y. reflexivity.
    + exfalso. congruence.
Qed.

Fact R_inv {X Y f g} :
  forall (H1: @inv (option X) (option Y) g f)
    (H2: inv f g),
    inv (fun y => pi1 (R H2 y)) (fun x => pi1 (R H1 x)).
Proof.
  intros H1 H2 x.
  destruct (R H1 x) as [y H3]; cbn.
  destruct (R H2 y) as [x' H4]; cbn.
  revert H3 H4.  
  destruct (f (Some x)) as [y1|] eqn:E.
  - intros <-. rewrite <-E, H1. easy.
  - intros <-.  rewrite H1. rewrite <-E, H1. congruence.
Qed.

Fact bijection_option X Y : 
  bijection (option X) (option Y) -> bijection X Y.
Proof.
  intros [f g H1 H2].
  exists (fun y => pi1 (R H1 y)) (fun x => pi1 (R H2 x)); apply R_inv.
Qed.

(*** Numeral Types *)

Fixpoint fin (n: nat) : Type :=
  match n with 0 => False | S n' => option (fin n') end.

Theorem fin_cardinality m n :
  bijection (fin m) (fin n) -> m = n.
Proof.
  induction m as [|m IH] in n |-*; destruct n.
  - easy.
  - intros [f g _ H]. exfalso. exact (g None).
  - intros [f g _ H]. exfalso. exact (f None).
  - intros H. f_equal. apply IH, bijection_option, H.
Qed.

Definition L {X Y}
  : (option X -> option (option Y)) -> X -> option Y
  := fun f x => match f (Some x) with
             | Some a => a
             | None => match f None with Some a => a | None => None end
             end.

Fact fin_bijection n f g :
  @inv (fin n) (fin n) g f -> inv f g.
Proof.
  revert f g.
  induction n as [|n IH]; cbn.
  { intros f g _ []. }
  destruct n; cbn.
  { intros f g H [[]|]. destruct f as [[]|]. reflexivity. }
  intros f g H.
  assert (H1: inv (L g) (L f)).
  { intros a. unfold L.
    destruct (f (Some a)) as [b|] eqn:?.
    - destruct (g (Some b)) eqn:?; congruence.
    - destruct (f None)  as [b|] eqn:?.
      + destruct (g (Some b)) eqn:?. 1:congruence.
        destruct (g None) eqn:?; congruence.
      + destruct (g (Some None)) eqn:?.
        * congruence.
        * destruct (g None) eqn:?; congruence. }
  specialize (IH _ _ H1). clear H1.
  destruct (f (g None)) as [b|] eqn:E1.
  - exfalso.
    destruct (f None) as [b'|] eqn:?.
    + generalize (IH b'). clear IH. unfold L.
      destruct  (g (Some b')) eqn:?. 1:congruence.
      destruct (g None) eqn:?.
      * rewrite E1. congruence.
      * destruct (f (Some None)) eqn:?; congruence.
    + congruence.      
  - intros [b|]. 2:exact E1.
    generalize (IH b). clear IH. unfold L.
    destruct (g (Some b)) as [a|] eqn:?.
    + destruct (f (Some a)) eqn:?.
      * congruence.
      * destruct (f None) eqn:?; congruence.
    + destruct (g None) as [a|] eqn:?.
      * rewrite E1. destruct (f None) eqn:?; congruence.
      * destruct (f (Some None)) eqn:?; congruence.
Qed.

(* Note that the congruence tactic is essential in the above proof,
   where it does the final verification steps in more than 20 cases.       
   We say that congruence does linear equational resoning. *)

(** Iterative definition *)

Fixpoint iter {X: Type} (f: X -> X) (n:nat) (x:X) : X :=
  match n with
  | 0 => x
  | S n' => f (iter f n' x)
  end.

Notation fin' n := (iter option n False).

Goal fin 3 = fin' 3.
Proof.
  cbn. reflexivity.
Qed.

Goal forall n, fin n = fin' n.
Proof.
  induction n as [|n IH]; cbn.
  - reflexivity.
  - f_equal. exact IH.
Qed.

(** Embedding recursive numerals into numbers *)

From Coq Require Import Arith Lia List.

Fixpoint E n (a: fin n) : nat :=
  match n, a with
  | 0, a => match a with end
  | S n, None => 0
  | S n, Some a => S (E n a)
  end.

Compute E 4 None.
Compute E 6 (Some (Some None)).

Fact E_lt n (a: fin n) :
  E n a < n.
Proof.
  induction n as [|n IH].
  - destruct a.
  - destruct a as [a|]; cbn.
    + specialize (IH a). lia.
    + lia.
Qed.

Fixpoint D k n : fin (S n) :=
  match k, n with
  | 0, _ => None
  | S _, 0 => None
  | S k, S n => Some (D k n)
  end.

Compute D 3 3.
Compute D 2 3.
Compute E 4 (D 2 3).
Compute D (E 6 None) 5.
Compute D (E 6 (D 3 5)) 5.

Fact DE_eq n (a: fin (S n)) :
  D (E (S n) a) n = a.
Proof.
  induction n as [|n IH].
  - destruct a as [a|]; cbn.
    + contradict a.
    + reflexivity.
  - destruct a as [a|].
    + cbn . f_equal. apply IH.
    + reflexivity.
Qed.

Fact ED_eq k n :
  k <= n -> E (S n) (D k n) = k.
Proof.
  induction k as [|k IH] in n |-*; cbn.
  - easy.
  - destruct n as [|n]; cbn.
    + intros H. exfalso. lia.
    + intros H. f_equal. apply IH. lia.
Qed.

(*** Coq's Decision Format *)

(** Coq offers support for equality decisions 
    but uses a different decision format. *)

Print sumbool.
From Coq Require Import Arith.
Search concl: ({_=_} + {_}).

Definition dec_adapt (P: Prop) :
  { P } + { ~ P} <=> dec P.
Proof.
  split.
  - intros [H|H].
    + left. exact H.
    + right. exact H.
  - intros [H|H].
    + left. exact H.
    + right. exact H.
Defined.

Definition coq_nat_eqdec : eqdec nat.
Proof.
  intros x y. apply dec_adapt. decide equality.
Defined.

Compute dec2bool (coq_nat_eqdec 3 5).

Definition coq_nat_eqdec' : eqdec nat.
Proof.
  intros x y. apply dec_adapt. apply Nat.eq_dec.
Defined.

Compute dec2bool (coq_nat_eqdec' 3 5).

Definition coq_option_eqdec {X} :
  eqdec X -> eqdec (option X).
Proof.
  intros H x y. apply dec_adapt. decide equality.
  apply dec_adapt, H.
Defined.
  
Compute dec2bool (coq_option_eqdec coq_nat_eqdec (Some 5) (Some 5)).



