(*** Euclidean Division *)
From Coq Require Import Lia.
Definition dec (X: Type) : Type := X + (X -> False).
Notation sig := sigT.
Notation Sig := existT.
Notation pi1 := projT1.
Notation pi2 := projT2.
Notation "'Sigma' x .. y , p" :=
  (sig (fun x => .. (sig (fun y => p%type)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.

Fact le_lt_dec x y :
  (x <= y) + (y < x).
Proof.
  destruct (x - y) eqn:?; intuition lia.
Qed.

Definition complete_ind (p: nat -> Type) :
  (forall x, (forall y, y < x -> p y) -> p x) -> forall x, p x.
Proof.
  intros H x. apply H.
  induction x as [|x IH]. lia.
  intros y H1. apply H. intros z H3.
  apply IH. lia.
Qed.

(*** Existence *)

Definition delta x y a b := x = a * S y + b /\ b <= y.

Module Type DMT.
  Parameter D: nat -> nat -> nat.
  Parameter M: nat -> nat -> nat.
  Parameter DM_correct: forall x y, delta x y (D x y) (M x y).
End DMT.
Module DM: DMT.
  Definition delta_sig :
    forall x y, Sigma a b, delta x y a b.
  Proof.
    intros x y.
    induction x as [|x (a&b&IH)].
    - exists 0, 0. unfold delta; lia.
    - destruct (le_lt_dec (S b) y) as [H|H].
      + exists a, (S b). unfold delta in *; lia.
      + exists (S a), 0. unfold delta in *; lia.
  Qed.
  Definition D x y := pi1 (delta_sig x y).
  Definition M x y := pi1 (pi2 (delta_sig x y)).
  Fact  DM_correct x y :
    delta x y (D x y) (M x y).
  Proof.
    unfold D, M.
    destruct delta_sig as (a&b&H); cbn. exact H.
  Qed.
End DM.
Import DM.

Fact M_lt x y :
  M x y < S y.
Proof.
  destruct (DM_correct x y) as [_ H]. lia.
Qed.

Fact M_zero x y :
  M x y = 0 <-> x = D x y * S y.
Proof.
  destruct (DM_correct x y) as [H _]. lia.
Qed.

Fact E11 x y a b:
  delta x y a b -> b = x - a * S y.
Proof.
  unfold delta; lia.
Qed.
Fact E12 x y:
  M x y = x - D x y * S y.
Proof.
  apply E11, DM_correct.
Qed.

Definition safe p n := forall k, k < n -> ~p k.
Definition least p n := p n /\ safe p n.

Fact E16 x y :
  least (fun k => x <= y + k) (x - y).
Proof.
  split. lia. intros k. lia.
Qed.

(*** Uniqueness *)

Fact delta_unique x y a b a' b' :
  delta x y a b  -> delta x y a' b' -> a = a' /\ b = b'.
Proof.
  unfold delta. intros [-> H1] [H H2].  
  enough (a = a') by lia.
  revert a' H.
  induction a as [|a IH]; intros [|a']; intros H.
  - reflexivity.
  - lia.
  - lia.
  - specialize (IH a'). lia.
Qed.

(* A proof using more automation *)

Fact delta_unique' x y a b a' b' :
  delta x y a b  -> delta x y a' b' -> a = a' /\ b = b'.
Proof.
  unfold delta. intros H1 H2.
  enough (a = a') by lia.
  nia.
  (* nia is an extension of lia handling multiplication *)
Qed.

Goal D 100 3 = 25 /\ M 100 3 = 0.
Proof.
  eapply delta_unique.
  - apply DM_correct.
  - split; cbn. reflexivity. lia.
Qed.

Fact DM_zero x a y :
  x = a * S y <-> D x y = a /\ M x y = 0.
Proof.
  split.
  - intros H. apply (delta_unique x y).
    + apply DM_correct.
    + unfold delta. lia.
  - destruct (DM_correct x y) as [H _]. lia.
Qed.

Fact E20 a b y :
  b <= y ->
  D (a * S y + b) y = a /\ M (a * S y + b) y = b.
Proof.
  intros H.
  eapply delta_unique.
  - apply DM_correct.
  - easy.
Qed.

Fact E21 x y a :
  D x y = a <-> exists b, delta x y a b.
Proof.
  split.
  - intros <-. eexists. apply DM_correct.
  - intros [b H].
    apply (delta_unique x y (D x y) (M x y) a b).
    + apply DM_correct.
    + exact H.
Qed.
Fact E22 x y b :
  M x y = b <-> exists a, delta x y a b.
Proof.
  split.
  - intros <-. exists (D x y). apply DM_correct.
  - intros [a H].
    apply (delta_unique x y (D x y) (M x y) a b).
    + apply DM_correct.
    + exact H.
Qed.

Module Exercise_gamma.

  Definition gamma x y a := a * S y <= x < S a * S y.

  Fact gamma_delta x y a :
    gamma x y a <-> exists b, delta x y a b.
  Proof.
    unfold gamma, delta. split.
    - intros H. exists (x - a * S y). lia.
    - intros (b&H1&H2). lia.
  Qed.
  Fact E23 x y a :
    D x y = a <-> gamma x y a.
  Proof.
    split; intros H.
    - apply gamma_delta, E21, H.
    - apply E21, gamma_delta, H.
  Qed.
  Fact E13 x y:
    gamma x y (D x y).
  Proof.
    apply E23. reflexivity.
  Qed.
End Exercise_gamma.

(*** Repeated Subtraction *)

Fact rep_sub1 x y:
  x <= y -> delta x y 0 x.
Proof.
  unfold delta; lia.
Qed.

Fact rep_sub2 x y a b:
  delta (x - S y) y a b -> x > y -> delta x y (S a) b.
Proof.
  unfold delta; lia.
Qed.

Definition DIV f x y :=
  if x - y then 0 else S (f (x - S y) y).
Definition MOD f x y :=
  if x - y then x else f (x - S y) y.


Notation "f == f'" := (forall x y, f x y = f' x y) (at level 70).

Fact DM_rep_sub :
  D == DIV D /\ M == MOD M.
Proof.
  enough (forall x y, D x y = DIV D x y /\ M x y = MOD M x y) as H.
  { split; apply H. }
  intros x y. apply (delta_unique x y).
  - apply DM_correct.
  - unfold DIV, MOD.
    destruct (x - y) eqn:?.
    + apply rep_sub1. lia.
    + apply rep_sub2. 2:lia. apply DM_correct.
Qed.
   
Fact DIV_unique f f' :
  f == DIV f -> f' == DIV f' -> f ==  f'.
Proof.
  intros H1 H2 x y.
  revert x. apply complete_ind. intros x IH.
  rewrite H1, H2. unfold DIV.
  destruct (x - y) eqn:?. reflexivity.
  rewrite IH.  reflexivity. lia.
Qed.
       
Fact MOD_unique f f' :
  f == MOD f -> f' == MOD f' -> f ==  f'.
Proof.
  intros H1 H2 x y.
  revert x. apply complete_ind. intros x IH.
  rewrite H1, H2. unfold MOD.
  destruct (x - y) eqn:?. reflexivity.
  rewrite IH.  reflexivity. lia.
Qed.
       
Fact DIV_D_agree f :
  f == DIV f <-> f == D.
Proof.
  split; intros H.
  - apply DIV_unique. exact H. apply DM_rep_sub.
  - intros x y. unfold DIV. rewrite !H. apply DM_rep_sub.
Qed.
       
Fact MOD_M_agree f :
  f == MOD f <-> f == M.
Proof.
  split; intros H.
  - apply MOD_unique. exact H. apply DM_rep_sub.
  - intros x y. unfold MOD. rewrite !H. apply DM_rep_sub.
Qed.

(*** Divisibilty *)

Definition divides n x : Prop := exists k, x = k * n.
Notation "( n | x )" := (divides n x) (at level 0) : nat_scope.

Fact divides_M n x :
  (S n | x) <-> M x n = 0.
Proof.
  split.
  - intros [k H]. eapply DM_zero, H.
  - intros H. exists (D x n). apply M_zero, H.
Qed.

Fact divides_dec :
  forall n x, dec (n | x).
Proof.
  intros [|n] x.
  - destruct x.
    + left. hnf. exists 0. reflexivity.
    + right. intros [k H]. lia.
  - destruct (M x n) as [|b] eqn:H.
    + left. apply divides_M, H.
    + right. intros H1 %divides_M. lia.
Qed.

Fact divides_zero n :
  (n | 0).
Proof.
  exists 0. reflexivity.
Qed.

Fact divides_self x :
  (x | x).
Proof.
  exists 1. lia.
Qed.

Fact divides_bnd n x :
  x > 0 -> (n | x) -> n <= x.
Proof.
  intros H [k ->]. destruct k; lia.
Qed.

Fact divides_bnd' n x :
  n > x -> (n | x) -> x = 0.
Proof.
  intros H [k ->]. destruct k; lia.
Qed.
 
Lemma divides_le x y :
  (forall n, (n | x) <-> (n | y)) -> x <= y.
Proof.
  intros H.
  destruct y.
  - enough (x = 0) by lia.
    apply divides_bnd' with (n:= S x). lia.
    apply H, divides_zero.
  - apply divides_bnd. lia.
    apply H, divides_self.
Qed.

Fact divides_eq x y :
  (forall n, (n | x) <-> (n | y)) -> x = y.
Proof.
  intros H.
  enough (x <= y /\ y <= x) by lia.
  split; apply divides_le; firstorder.
Qed.

(*** Decidability of Primality *)

Definition prime x := x >= 2 /\ forall n, (n | x) -> n = 1 \/ n = x.
    
Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).
Definition eqdec X := forall x y: X, dec (x = y).
Definition decider {X} (p: X -> Type) := forall x, dec (p x).

Fact prime' x :
  prime x <=> x >= 2 /\ (forall n, n <  S x -> (n | x) -> n = 1 \/ n = x).
Proof.
  split.
  - firstorder.
  - intros [H1 H2]. split. exact H1.
    intros n H3. apply H2. 2:exact H3.
    enough (n <= x) by lia.
    apply divides_bnd. lia. exact H3.
Qed.

Definition nat_eqdec : eqdec nat.
Proof.
  intros x y.
  destruct ((x - y) + (y - x)) eqn:?.
  - left; lia.
  - right; lia.
Qed.

Definition transport_dec X Y :
  Y <=> X -> dec X -> dec Y.
Proof.
  unfold dec, iffT. tauto.
Qed.

Definition and_dec (X Y: Prop) :
  dec X -> dec Y -> dec (X /\ Y).
Proof.
  unfold dec. tauto.
Qed.
Definition or_dec (X Y: Prop) :
  dec X -> dec Y -> dec (X \/ Y).
Proof.
  unfold dec. tauto.
Qed.

Definition impl_dec (X Y: Prop) :
  dec X -> dec Y -> dec (X -> Y).
Proof.
  unfold dec. tauto.
Qed.

Definition forall_dec (p: nat -> Type) n :
  decider p -> dec (forall x, x < n -> p x).
Proof.
  intros d. induction n as [|n IH].
  { left. lia. }
  destruct (d n).
  2:{ right. auto. }
  destruct IH as [IH|IH].
  - left. intros x ?.
    destruct (nat_eqdec x n) as [->|?]. easy.
    apply IH. lia.
  - right. contradict IH. intros x ?. apply IH. lia.
Qed.

Definition prime_dec x :
  dec (prime x).
Proof.
  apply (transport_dec _ _ (prime' x)).
  apply and_dec.
  - unfold dec. destruct (le_lt_dec 2 x); intuition lia.
  - apply forall_dec.
    intros n. apply impl_dec.
    + apply divides_dec.
    + apply or_dec; apply nat_eqdec.
Qed.

(*** GCD *)

Definition gamma x y z : Prop :=
  forall n, (n | z) <-> (n | x) /\ (n | y).

Fact gamma_unique x y z z' :
  gamma x y z -> gamma x y z' -> z = z'.
Proof.
  intros H1 H2.
  apply divides_eq. intros n.
  unfold gamma in *. rewrite H1, H2. easy.
Qed.


Fact divides_sub x y n :
  x <= y -> (n | x) -> (n | y) <->  (n | y - x).
Proof.
  intros H [k ->]. split.
  - intros [l ->]. exists (l-k). nia.
  - intros [l H1]. exists (k + l). nia.
Qed.

Fact gamma_sub x y z :
  x <= y -> gamma x (y - x) z -> gamma x y z.
Proof.
  intros H H1 n.
  specialize (H1 n).
  generalize (divides_sub _ _ n H).
  tauto.
Qed.

Fact gamma_mod x y z :
  gamma (S x) (M y x) z -> gamma (S x) y z.
Proof.
  revert y. refine (complete_ind _ _). intros y IH.
  destruct DM_rep_sub as [_ H]. rewrite H. unfold MOD.
  destruct (y - x) eqn:?. easy.
  intros H2. apply gamma_sub. lia.
  apply IH. lia. exact H2.
Qed.

Fact gamma_sym x y z :
  gamma x y z -> gamma y x z.
Proof.
  unfold gamma. firstorder.
Qed.

Fact gamma_zero y :
  gamma 0 y y.
Proof.
  intros n.
  enough (n | 0) by tauto.
  exists 0. reflexivity.
Qed.

Module Type GCDT.
  Parameter gcd: nat -> nat -> nat.
  Parameter gcd_correct: forall x y, gamma x y (gcd x y).
End GCDT.
Module GCD: GCDT.
  Definition gamma_sig :
    forall x y, Sigma z, gamma x y z.
  Proof.
    refine (complete_ind _ _). intros x IH y.
    destruct x.
    - exists y. apply gamma_zero.
    - edestruct (IH (M y x)) as [z H]. {apply M_lt.}
      exists z. apply gamma_mod, gamma_sym, H.
  Qed.

  Definition gcd x y := pi1 (gamma_sig x y).

  Fact gcd_correct x y:
    gamma x y (gcd x y).
  Proof.
    unfold gcd. destruct gamma_sig as [z H]. exact H.
  Qed.
End GCD.
Import GCD.

Definition GCD f (x y: nat) : nat :=
  match x with
  | 0 => y
  | S x => f (M y x) (S x)
  end.

Fact rep_mod :
  gcd == GCD gcd.
Proof.
  intros x y.
  apply (gamma_unique x y).
  - apply gcd_correct.
  - unfold GCD.
    destruct x. {apply gamma_zero.}
    apply gamma_mod, gamma_sym, gcd_correct.
Qed.

Fact GCD_unique f f' :
  f == GCD f -> f' == GCD f' -> f == f'.
Proof.
  intros H1 H2.
  refine (complete_ind _ _). intros x IH y.
  rewrite H1, H2. unfold GCD.
  destruct x. reflexivity.
  apply IH, M_lt.
Qed.

Definition GCD_sub f (x y: nat) : nat :=
  if x then y else
    if x - y then f x (y - x) else f y x.

Fact gcd_rep_sub :
  gcd == GCD_sub gcd.
Proof.
  intros x y.
  apply (gamma_unique x y).
  - apply gcd_correct.
  - unfold GCD_sub.
    destruct x. {apply gamma_zero.}
    destruct (S x - y) eqn:H.
    + apply gamma_sub. lia. apply gcd_correct.
    + apply gamma_sym, gcd_correct.
Qed.

(*** Reducible Div and Mod *)

Fixpoint Div x c y :=
  match x, c with
  | 0, _ => 0
  | S x, 0 => S (Div x y y)
  | S x, S c => Div x c y
  end.

Fixpoint Mod x c y :=
  match x, c with
  | 0, c => y - c
  | S x, 0 => Mod x y y
  | S x, S c => Mod x c y
  end.

Compute 
  let x := 8 in
  let y := 3 in
  (Div x (y - 1) (y - 1), Mod x (y - 1) (y - 1)).

Fact Div_Mod_correct' x c y :
  c <= y ->
  delta (x + y - c) y (Div x c y) (Mod x c y).
Proof.
  induction x as [|x IH] in c|-*; intros H.
  - cbn. split; lia.
  -  destruct c; cbn.
     + specialize (IH y). unfold delta in *. lia.
     + apply (IH c). lia.
Qed.

Fact Div_Mod_agree x y :
  D x y = Div x y y /\
  M x y = Mod x y y.
Proof.
  eapply delta_unique.
  - apply DM_correct.
  - generalize (Div_Mod_correct' x y y). unfold delta. lia.
Qed.

(*** Coq's Predefined Functions *)

From Coq Require Import Arith.

Fact predefined_div_mod_delta x y :
  delta x y (x / S y) (x mod S y).
Proof.
  unfold delta.
  generalize (Nat.div_mod x (S y)).
  generalize (Nat.mod_upper_bound x (S y)).
  lia.
Qed.

Compute fun x => x / 0.
Compute fun x => x mod 0.
Compute 17 / 3.
Compute 17 mod 3.

Locate "/".
Print Nat.div.
Print Nat.divmod.
Locate "mod".
Print Nat.modulo.

Fact predefined_gcd x y :
  gamma x y (Nat.gcd x y).
Proof.
  intros n. split.
  - unfold divides. intros [k1 H]. split.
    + destruct (Nat.gcd_divide_l x y) as [k2 H1]. exists (k2 * k1). lia.
    + destruct (Nat.gcd_divide_r x y) as [k2 H1]. exists (k2 * k1). lia.
  - intros [H1 H2]. apply Nat.gcd_greatest; assumption.
Qed.

Print Nat.gcd.

