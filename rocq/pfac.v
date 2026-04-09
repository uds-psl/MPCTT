(*** Prime Factorization *)
(** We represent prime factorizations as ascending lists of primes,
    give a certifying function computing prime factorizations, and
    prove uniqueness using Euclid's Lemma. *)

From Stdlib Require Import Lia List.
Import ListNotations.
Notation "x 'el' A" := (In x A) (at level 70).
Notation "x 'nel' A" := (~In x A) (at level 70).
Implicit Types A B : list nat.

Definition divides n x : Prop := exists k, x = k * n.
Notation "( n | x )" := (divides n x) (at level 0) : nat_scope.

Definition gamma x n := forall k, k > 1 -> (k|x) -> n <= k.
(* every factor of x is >= n *)

Definition prime x :=
  x > 1 /\ gamma x x.

Fixpoint pi A :=
  match A with [] => 1 | a :: A => a * pi A end.

Definition sigma' x A :=
  match A with [] => True | a::A => x <= a end.

Fixpoint sigma A :=
  match A with [] => True | a::A => sigma' a A /\ sigma A end.

Fixpoint all p A :=
  match A with a::A => p a /\ all p A |[] => True end.

Notation pfac x A := (x = pi A /\ all prime A /\ sigma A).

(*** Easy Facts *)

Fact divides_refl x :
  (x|x).
Proof.
  exists 1; easy.
Qed.

Fact divides_trans x y z :
  (x|y) -> (y|z) -> (x|z).
Proof.
  intros [a H1] [b H2]. exists (a * b). lia.
Qed.

Fact divides_le x y :
  (x | y) -> y > 0 -> 0 < x <= y.
Proof.
  intros [a H1] H2. destruct a; lia.
Qed.

Fact divides_sub x y k :
  x < y -> (k | x) -> (k | y) <-> (k | y - x).
Proof.
  intros H1 [a H2]. split.
  - intros [b H3]. exists (b - a). nia.
  - intros [c H3]. exists (c + a). nia.
Qed.

Fact gamma_le x k :
  x > 1 -> gamma x k -> k <= x.
Proof.
  intros H1 H2. apply H2. assumption. apply divides_refl.
Qed.

Fact gamma_back x k n :
  gamma x k -> (n|x) -> gamma n k.
Proof.
  intros H1 H2 m H3 H4.
  apply H1. assumption.
  eapply divides_trans; eassumption.
Qed.

Fact gamma_eq x k :
  x > 0 -> k > 1 -> (k|x) ->  gamma x x -> k = x.
Proof.
  intros H1 H2 H3 H4.
  enough (k <= x /\ x <= k) by lia. split.
  - destruct H3 as [a ->]. destruct a; lia.
  - apply H4; assumption.
Qed.

Fact prime_or x k :
  prime x -> (k | x) -> k = 1 \/ k = x.
Proof.
  intros H1 H2.
  assert (k > 0) by (destruct H1, H2; lia).
  assert (k = 1 \/ k > 1) as [-> |H3] by lia.
  - left; easy.
  - right. destruct H1; apply gamma_eq; assumption||lia.
Qed.

Fact prime_naive_char x :
  prime x <-> x > 1 /\ forall n, (n | x) -> n = 1 \/ n = x.
Proof.
  split.
  - intros H. assert (x > 1) by apply H.
    split. assumption. intro n. apply prime_or. assumption.
  - intros [H1 H2]. split. assumption.
    intros n H3 H4. specialize (H2 _ H4). intuition lia.
Qed.

Fact prime_not x y :
  x > 1 -> y > 1 -> ~prime (x * y).
Proof.
  intros H1 H2 [_ H3]. 
  enough (x * y <= x) by nia.
  apply H3. assumption. exists y. lia.
Qed.

Lemma sigma_le a A x :
  sigma (a::A) -> x el A -> a <= x.
Proof.
  induction A as [|a' A IH] in a|-*.
  - easy.
  - cbn. intros (H1&H2&H3) [-> | H4]. exact H1.
    apply IH. 2:exact H4. split. 2:exact H3.
    destruct A; cbn in *; intuition lia.
 Qed.

Lemma sigma_nel a A x :
  sigma (a::A) -> x < a -> x nel a::A.
Proof.
  intros H1 H4 H5.
  enough (a <= x) by lia.
  eapply sigma_le.  exact H1.
  destruct H5; intuition lia.
Qed.

Fact all_prime_one A :
  all prime A -> pi A >= 1.
Proof.
  induction A as [|a A IH]; cbn. lia.
  intros ([H1 _]&H2). apply IH in H2. lia.
Qed.

Fact pfac_divides x a A :
  pfac x (a::A) -> prime a /\ (a|x).
Proof.
  cbn. intros (H1&[H2 _]&_). split. easy. exists (pi A); lia.
Qed.

Fact pfac_one A :
  pfac 1 A -> A = [].
Proof.
  intros (H1&H2&_).
  destruct A as [|a A]. easy.
  exfalso. cbn in *.
  enough (a > 1 /\ pi A >= 1) by lia. split.
  - apply H2.
  - apply all_prime_one, H2.
Qed.

Fact gamma_pfac x :
  x > 1 -> gamma x x -> pfac x [x].
Proof.
  intros H1 H2. split; cbn. lia. easy.
Qed.

(*** Size Induction *)

Lemma size_ind1 (sigma: nat -> nat) {p: nat -> Type} :
  (forall x, (forall x', sigma x' < sigma x -> p x') -> p x) ->
  forall x, p x.
Proof.
  intros H.
  enough (forall n x, sigma x < n -> p x) by eauto.
  induction n as [|n IH]. lia.
  intros x H1. apply H. intros x' H2.
  apply IH. lia.
Qed.

Lemma size_ind2 (sigma: nat -> nat -> nat) {p: nat -> nat -> Type} :
  (forall x y, (forall x' y', sigma x' y' < sigma x y -> p x' y') -> p x y) ->
  forall x y, p x y.
Proof.
  intros H.
  enough (forall n x y, sigma x y < n -> p x y) by eauto.
  induction n as [|n IH]. lia.
  intros x y H1. apply H. intros x' y' H2.
  apply IH. lia.
Qed.

Notation sig := sigT.
Notation "'Sigma' x .. y , p" :=
  (sig (fun x => .. (sig (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.

(*** Certifying Prime
     Factorization  *)

Theorem divide x n:
  n > 0 -> (Sigma k, x = k * n) + ~(n | x).
Proof.
  intros H.
  revert x.
  refine (size_ind1 (fun x => x) _). intros x IH.
  assert ((x = 0) + (x > 0)) as [H1|H1].
  {destruct x; intuition lia.}
  - left. exists 0. lia. 
  - assert ((x < n) + (x >= n)) as [H2|H2].
    {destruct (n-x) eqn:?; intuition lia.}
    + right. intros [k H3]. destruct k; lia.
    + specialize (IH (x - n)) as [[k IH]|IH]. lia.
      * left. exists (S k). lia.
      * right. contradict IH.
        destruct IH as [a ->].
        exists (a - 1). nia.
Qed.

Fact gamma_inc k x :
  gamma x k -> ~(k|x) -> gamma x (S k).
Proof.
  intros H1 H2 n H3 H4.
  assert (n <> k) by congruence.
  apply H1 in H4; lia.
Qed.

Fact pfac_cons x' k x A :
  k > 1 -> gamma x k -> x = k * x' ->
  pfac x' A -> pfac x (k::A).
Proof.
  intros H1 H3 -> (H4&H5&H6).
  split. cbn; lia. split.
  - split. 2:assumption. split. assumption.    
    eapply gamma_back. exact H3. exists (pi A). lia.
  - split. 2:assumption.
    destruct A as [|a A]; cbn. easy.
    apply H3. apply H5.
    cbn in H4. exists (k*pi A); lia.
Qed.

Lemma pfac_sig' x k :
  x > 1 -> k > 1 -> gamma x k -> Sigma A, pfac x A.
Proof.
  revert x k.
  refine (size_ind2 (fun x k => x - k) _).
  intros x k IH H1 H2 H3.
  destruct (divide x k) as [[x' H4]|H4]. lia.
  - assert ((x' = 1) + (x' > 1)) as [-> |H5].
    {destruct (2 - x') eqn:?; intuition lia.}
    + assert (k = x) as -> by lia.
      exists [x]. now apply gamma_pfac.
    + destruct (IH x' k) as [A H7]. 1-3:nia.
      * eapply gamma_back. exact H3. exists k; lia.
      * exists (k::A). apply (pfac_cons x'); assumption||lia.
  - apply (IH x (S k)). 2,3:lia.
    + enough (k < x) by lia. 
      assert (k <= x ) by (apply gamma_le; assumption||lia).
      enough (k <> x) by lia.
      intros ->. apply H4, divides_refl.
    + apply gamma_inc; assumption.
 Qed.

Theorem pfac_sig x :
  x > 0 -> Sigma A, pfac x A.
Proof.
  intros H.
  destruct x. lia.
  destruct x. exists []; easy.
  apply (pfac_sig' _  2). 1,2:lia. easy.
Qed.

Fact prime_dec x :
  x > 1 -> prime x + Sigma a b, x = a * b /\ a > 1 /\ b > 1.
Proof.
  intros H.
  destruct (pfac_sig x) as ([|a [|b A]]&H1). lia.
  - exfalso. destruct H1 as [H1 _].  cbn in *; lia.
  - left. cbn in H1.
    replace (a * 1) with a in H1 by lia.
    intuition congruence.
  - right. exists a, (b*pi A). cbn in H1.
    assert (a > 1) by apply H1.
    assert (b > 1) by apply H1.
    repeat split. easy. easy. destruct (pi A); lia.
Qed.

Fact gamma_square_prime x k :
  x > 1 -> gamma x k -> k * k > x -> prime x.
Proof.
  intros H1 H2 H3.
  destruct (prime_dec x) as [H|(a&b&H4&H5&H6)]. lia.
  - exact H.
  - exfalso.
    enough (a >= k /\ b >= k) by nia. split.
    + apply H2. assumption. exists b; lia.
    + apply H2. assumption. exists a; lia.
Qed.

Lemma pfac_sig'' x k :
  x > 1 -> k > 1 -> gamma x k -> Sigma A, pfac x A.
Proof.
  revert x k.
  refine (size_ind2 (fun x k => x - k) _).
  intros x k IH H1 H2 H3.
  assert ((k*k > x ) + (k*k <= x)) as [H4|H4].
  {destruct (k*k-x) eqn:?; intuition lia.}
  - exists [x]. split;cbn. lia.
    enough (prime x) by easy.
    eapply (gamma_square_prime x k); assumption. 
  - destruct (divide x k) as [[x' H5]|H5]. lia.
    + destruct (IH x' k) as [A H7]. 1-3:nia.
      * eapply gamma_back. exact H3. exists k; lia.
      * exists (k::A). apply (pfac_cons x'); assumption||lia.
    + apply (IH x (S k)). nia. lia. lia.
      apply gamma_inc; assumption.
Qed.

(*** Euclid's Lemma *)

(** Euclid's lemma says that a prime dividing a product
    of a different prime and a number must divide the number.
    To enable a direct inductive proof, the statement must
    be generalized using the botion of coprimlity. We took
    the proof idea from  Wikipedia. *)

Definition coprime x y :=
  x > 0 /\ y > 0 /\ forall k, (k | x) -> (k | y) -> k = 1.
(* Every common factor of two number > 0 is 1 *)

Fact coprime_eq x :
  coprime x x -> x = 1.
Proof.
  intros (H1&H2&H3). apply H3; exists 1; lia.
Qed.

Fact coprime_sym x y :
  coprime x y -> coprime y x.
Proof.
  unfold coprime. intuition.
Qed.

Fact coprime_sub x y :
  x < y -> coprime x y -> coprime x (y - x).
Proof.
  intros H1 (H2&H3&H4). repeat split. assumption. lia.
  intros k H5 H6. apply H4. exact H5.
  apply <- divides_sub; eassumption.
Qed.

Fact prime_coprime x y :
  prime x -> prime y -> x <> y -> coprime x y.
Proof.
  intros H1 H2 H3.
  assert (x > 1) by apply H1.
  assert (y > 1) by apply H2.
  repeat split. 1,2: lia.
  intros k H4 H5.
  assert (k=1 \/ k=x) as [-> |H6] by (apply prime_or; assumption). easy.
  assert (k=1 \/ k=y) as [-> |H7] by (apply prime_or; assumption). easy.
  exfalso. lia.
Qed.

Lemma Euclid_coprime x y n :
  coprime n x -> (n | x * y) -> (n | y).
Proof.
  revert x y n.
  refine (size_ind2 (fun x y => x + y) _).
  intros x y IH n H1 [k H2].
  assert (y = 0 \/ y > 0) as [-> |H3] by lia. exists 0; lia.
  assert (x > 0) as H0 by apply H1.
  assert (n = x \/ n < x \/ n > x) as [<-|[H |H]] by lia.
  - apply coprime_eq in H1 as ->. exists y. lia.
  - apply (IH (x - n)).
    + lia.
    + apply coprime_sub; assumption.
    + exists (k - y). nia.
  - enough (n - x | y - k) as [a H4] by (exists a; nia).
    apply (IH x).
    + lia.
    + apply coprime_sym, coprime_sub, coprime_sym; assumption.
    + exists k. nia.
Qed.

Lemma Euclid x y n :
  prime n -> prime x -> n <> x -> (n | x * y) -> (n | y).
Proof.
  intros H1 H2 H3.
  apply Euclid_coprime, prime_coprime; assumption.
Qed.

Lemma prime_el A n :
  all prime A -> prime n -> (n | pi A) -> n el A.
Proof.
  induction A as [|a A IH] in n |-*; cbn.
  - intros _ [H1 _] [k H2]. destruct k; lia.
  - intros [H1 H2] H3 H4.
    assert (n = a \/ n <> a) as [-> |H] by lia. left; easy.
    right. apply IH. 1,2:assumption.
    eapply (Euclid a); assumption.
Qed.

(*** Uniqueness of
     Prime Factorization *)

Theorem pfac_unique x A B :
  pfac x A -> pfac x B -> A = B.
Proof.
  induction A as [|a A IH] in x,B|-*.
  - intros [-> _]. destruct B as [|b B]. easy.
    intros H%pfac_one. congruence. 
  - destruct B as [|b B].
    + intros H1 H2. exfalso.
      assert (x = 1) as -> by apply H2.
      apply pfac_one in H1. congruence.
    + assert (a = b \/ a < b \/ a > b) as [<- |[H|H]] by lia.
      * cbn. intros (->&H1&H2) (H3&H4&H5). f_equal.
        assert (a > 1) by apply H1.
        assert (pi A = pi B) by nia.
        apply (IH (pi A)); easy.
      * intros [H1 H2]%pfac_divides H3. exfalso.
        enough (a el b::B /\ a nel b::B) by tauto. split.
        -- apply prime_el. easy. easy.
           enough (x = pi (b::B)) by congruence. easy.
        -- apply sigma_nel; easy.
      * intros H3 [H1 H2]%pfac_divides. exfalso.
        enough (b el a::A /\ b nel a::A) by tauto. split.
        -- apply prime_el. easy. easy.
           enough (x = pi (a::A)) by congruence. easy.
        -- apply sigma_nel; easy.
Qed.


(*** Product Characterization *)

Fact pi_app A B :
  pi (A ++ B) = pi A * pi B.
Proof.
  induction A as [|a A IH];cbn; nia.
Qed.

Fact el_app x A B :
  x el A ++ B -> (x el A) \/ (x el B).
Proof.
  induction A as [|a A IH]; cbn; intuition congruence.
Qed.


Fact pi_el_divides x A :
  x el A -> (x | pi A).
Proof.
  induction A as [|a A IH]; cbn. easy.
  intros [-> |H].
  - exists (pi A); lia.
  - eapply divides_trans. apply IH, H. exists a; lia.
Qed.

Fact all_app p A B :
  all p (A ++ B) <-> all p A /\ all p B.
Proof.
  induction A as [|a A IH]; cbn; tauto.
Qed.

Theorem prime_product x :
  prime x -> forall a b, (x | a * b) -> (x | a) \/ (x | b).
Proof.
  intros H a b H1.
  enough (a > 0 -> b > 0 -> (x | a * b) -> (x | a) \/ (x | b)) as H2.
  { destruct a. left; exists 0; lia.
    destruct b. right; exists 0; lia.
    apply H2. lia. lia. assumption. }
  intros H2 H3 H4.
  destruct (pfac_sig a) as [A H5]. assumption.
  destruct (pfac_sig b) as [B H6]. assumption.
  assert (a = pi A) as -> by easy.
  assert (b = pi B) as -> by easy. 
  assert ((x el A) \/ (x el B)) as [H7|H7].
  { apply el_app, prime_el.
    - apply all_app; easy.
    - assumption.
    - now rewrite pi_app. }
  - left. now apply pi_el_divides.
  - right. now apply pi_el_divides.
Qed.

Theorem prime_product_char x :
  prime x <-> x > 1 /\ forall a b, (x | a * b) -> (x | a) \/ (x | b).
Proof.
  split.
  - intros H. split. now apply H.
    intros a b H1.
    destruct  (prime_product x H a b); intuition.
  - intros [H F].
    destruct (prime_dec x) as [H1|(a&b&H0&H1&H2)]. lia. assumption.
    exfalso. destruct (F a b) as [H3|H3]. {exists 1. lia.}
    + apply divides_le in H3. nia. lia.
    + apply divides_le in H3. nia. lia.
Qed.

(*** Left Overs *)

Fact all_prime_two a A :
  all prime (a::A) -> pi (a::A) >= 2.
Proof.
  destruct A as [|b A]; cbn.
  - intros ([H1 _]&_); lia.
  - intros ([H1 _]&[H2 _]&H3).
    enough (pi A >= 1) by lia.
    apply all_prime_one, H3.
Qed.

Fact sigma_tail a A :
  sigma (a::A) -> sigma A.
Proof.
  cbn. intuition.
Qed.

Fact sigma_cons a x A :
  x <= a -> sigma (a::A) -> sigma (x::a::A).
Proof.
  easy.
Qed.

Fact F1 k n x y :
  k*n = x*y ->
  (k - y) * n = (x - n) * y.
Proof.
  nia.
Qed.


Fact F2 k n x y :
  k*n = x*y ->
  k * (n - x)  = x * (y - k).
Proof.
  intros H.
  replace (k * (n - x)) with ((n - x) * k) by lia.
  replace (x * (y - k)) with ((y - k) * x) by lia.
  apply F1. lia.
Qed.

Fact F3 a k n x y :
  x < n ->
  k * n = x * y -> 
  a * (n - x) = y - k ->
  a * n = y.
Proof.
  nia.
Qed.

Fact G1 n x y :
  n * (x - y) = n * x - n * y.
Proof.
  nia.
Qed.

Fact G2 x y z  :
  y > z -> x = y - z -> z = y - x.
Proof.
  nia.
Qed.

