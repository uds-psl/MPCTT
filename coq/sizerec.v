From Coq Require Import Arith Lia.
Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.
Notation pi1 := projT1.
Notation pi2 := projT2.

Definition size_rec {X: Type} (sigma: X -> nat) {p: X -> Type} :
  (forall x, (forall y, sigma y < sigma x -> p y) -> p x) ->
  (forall x, p x).
Proof.
  intros F.
  enough (forall n x, sigma x < n -> p x) as H.
  { intros x. apply (H (S (sigma x))). lia. }
  induction n as [|n IH]; intros x H.
  - exfalso. lia.
  - apply F. intros y H1. apply IH. lia.
Defined.

Definition size_rec2 {X Y: Type} (sigma: X -> Y -> nat) {p: X -> Y -> Type} :
  (forall x y, (forall x' y', sigma x' y' < sigma x y -> p x' y') -> p x y) ->
  (forall x y, p x y).
Proof.
  intros F.
  enough (forall '(x,y), p x y) as H.
  { intros x y. apply (H (x,y)). } 
  refine (size_rec (fun '(x,y) => sigma x y) (fun '(x,y) IH => _)). cbn in IH.
  apply F. intros x' y' H. apply (IH (x',y')), H.
Defined.

Notation agree f g := (forall x y, f x y = g x y).
Notation respects f p := (forall x y, p x y (f x y)).
Notation functional p := (forall x y z z', p x y z -> p x y z' -> z = z').


(*** Euclidean Division *)

Definition delta x y k := k * S y <= x < S k * S y.

Definition Delta f x y :=
  if le_lt_dec x y then 0 else S (f (x - S y) y).

Fact Delta_unique f g :
  agree f (Delta f) -> agree g (Delta g) -> agree f g.
Proof.
  intros H1 H2 x y. revert x.
  apply (size_rec (fun x => x)).
  intros x IH. rewrite H1, H2. unfold Delta.
  destruct le_lt_dec as [H|H]. reflexivity.
  f_equal. apply IH. lia.
Qed.

Fact delta_fun :
  functional delta. 
Proof.
  unfold delta. nia.
Qed.

Fact delta1 x y :
  x <= y -> delta x y 0.
Proof.
  unfold delta. lia.
Qed.

Fact delta2 x y z :
  x > y -> delta (x - S y) y z -> delta x y (S z).
Proof.
  unfold delta. lia.
Qed.

Definition div_rec (y: nat) {p: nat -> Type} :
  (forall x, x <= y -> p x) ->
  (forall x, x > y -> p (x - S y) -> p x) ->
  forall x, p x.
Proof.
  intros e1 e2.
  apply (size_rec (fun x => x)).
  intros x IH.
  destruct (le_lt_dec x y) as [H|H].
  - apply e1. exact H.
  - apply e2. exact H. apply IH. lia.
Defined.

Definition Div :
  forall x y, Sigma z, delta x y z.
Proof.
  intros x y. revert x. apply (div_rec y).
  - intros x H. exists 0. apply delta1, H.
  - intros x H [z IH]. exists (S z). apply delta2. exact H. exact IH.
Defined.

Definition div (x y: nat) : nat :=
  match y with
  | 0 => 0
  | S y' => pi1 (Div x y')
  end.

Compute div 7 3.
Compute div 48 8.

Fact delta_Delta f :
  respects f delta -> agree f (Delta f).
Proof.
  intros H x y.
  apply (delta_fun x y).
  - apply H.
  - unfold Delta.
    destruct le_lt_dec as [H1|H1].
    + apply delta1. exact H1.
    + apply delta2. exact H1. apply H.
Qed.

Fact Delta_delta f :
  agree f (Delta f) -> respects f delta.
Proof.
  intros H x y. 
  revert x.
  apply (size_rec (fun x => x)).
  intros x IH. rewrite H. unfold Delta.
  destruct le_lt_dec as [H1|H1].
  - apply delta1, H1.
  - apply delta2. exact H1. apply IH. lia.
Qed.

Definition div' : nat -> nat -> nat.
Proof.
  intros x [|y]. exact 0.
  revert x. apply (div_rec y).
  - exact (fun _ _ => 0).
  - exact (fun _ _ => S).
Defined.

Compute div' 7 3.

(*** Greatest Common Divisors *)

Definition Gamma f x y :=
  match x, y with
  | 0, y => y
  | S x, 0 => S x
  | (S x), (S y) => if le_lt_dec x y then f (S x) (y - x) else f (x - y) (S y)
  end.

(** NB: Uniqueness of Gamma follows best with binary size recursion. *)
Fact Gamma_unique f g :
  agree f (Gamma f) -> agree g (Gamma g) -> agree f g.
Proof.
  intros F G.
  refine (size_rec2 (fun x y => x + y) _).
  intros x y IH. rewrite F, G.
  destruct x as [|x]. reflexivity.
  destruct y as [|y]. reflexivity.
  cbn. destruct le_lt_dec as [H|H]; apply IH; lia.
Qed.

(** Totality of gcd relation follows best with gcd recursion. *)
Definition gcd_rec (p: nat -> nat -> Type) :
  (forall y, p 0 y) ->
  (forall x y, p y x -> p x y) ->
  (forall x y, x <= y -> p x (y - x) -> p x y) ->
  forall x y, p x y.
Proof.
  intros e1 e2 e3.
  apply (size_rec2 (fun x y => x + y)).
  intros x y IH.
  destruct x.
  - apply e1.
  - destruct y.
    + apply e2,e1.
    + destruct (le_lt_dec x y) as [H|H].
      * apply e3. lia. apply IH. lia.
      * apply e2,e3. lia. apply IH. lia.
Defined.

Definition gcd' : nat -> nat -> nat.
Proof.
  apply (gcd_rec (fun _ _ => nat)).
  - exact (fun x => x).
  - exact (fun _ _ x => x).
  - exact (fun _ _ _ x => x).
Defined.

Compute gcd' 49 63.

Section Gcd_function.
  Variable gamma: nat -> nat -> nat -> Prop.
  Variable gamma1: forall y, gamma 0 y y.
  Variable gamma2: forall x y z, gamma x y z -> gamma y x z.
  Variable gamma3: forall x y z, x <= y -> gamma x (y - x) z -> gamma x y z.

  Definition GCD :
    forall x y, Sigma z, gamma x y z.
  Proof.
      apply gcd_rec.
      - intros y. exists y. apply gamma1.
      - intros x y [z IH]. exists z. apply gamma2, IH.
      - intros x y H [z IH]. exists z. apply gamma3. exact H. exact IH.
  Defined.

  Definition gcd (x y: nat) : nat :=
    pi1 (GCD x y).
    
  Compute gcd 49 63.
  
  Fact gamma_Gamma f :
    functional gamma -> respects f gamma -> agree f (Gamma f).
  Proof.
    intros H1 H2 x y. apply (H1 x y).
    - apply H2.
    - destruct x.
      + apply gamma1.
      + destruct y.
        * apply gamma2, gamma1.
        * cbn. destruct le_lt_dec as [H|H].
          -- apply gamma3. lia. apply H2.
          -- apply gamma2, gamma3. lia. apply gamma2, H2.
  Qed.

  Fact Gamma_gamma f :
    agree f (Gamma f) -> respects f gamma.
  Proof.
    intros H. hnf.
    apply (size_rec2 (fun x y => x + y)).
    intros x y IH. rewrite H.
    destruct x.
    - apply gamma1.
    - destruct y.
      + apply gamma2, gamma1.
      + cbn. destruct le_lt_dec as [H1|H1].
        * apply gamma3. lia. apply IH. lia.
        * apply gamma2,gamma3. lia. apply gamma2, IH. lia.
  Qed.
End Gcd_function.

(*** Concrete GCD Relation *)

Definition divides n x : Prop := exists k, x = k * n.
Notation "( n | x )" := (divides n x) (at level 0) : nat_scope.

Definition gamma x y z : Prop :=
  forall n, (n | z) <-> (n | x) /\ (n | y).

Fact divides_zero n :
  (n | 0).
Proof.
  exists 0. reflexivity.
Qed.

Fact divides_minus x y n :
  x <= y -> (n | x) -> (n | y) <->  (n | y - x).
Proof.
  intros H [k ->]. split.
  - intros [l ->]. exists (l-k). nia.
  - intros [l H1]. exists (k + l). nia.
Qed.

Fact gamma1 y :
  gamma 0 y y.
Proof.
  intros n. generalize (divides_zero n). tauto.
Qed.

Fact gamma2 x y z :
  gamma x y z -> gamma y x z.
Proof.
  unfold gamma. firstorder.
Qed.

Fact gamma3 x y z :
  x <= y -> gamma x (y - x) z -> gamma x y z.
Proof.
  intros H H1 n.
  specialize (H1 n).
  generalize (divides_minus _ _ n H).
  tauto.
Qed.

Fact divides_bnd n x :
  x > 0 -> (n | x) -> n <= x.
Proof.
  intros H [k ->]. destruct k.
  - exfalso. lia.
  - nia.
Qed.
 
Fact divides_eq' x y :
  x > 0 -> y > 0 -> (x | y) -> (y | x) -> x = y.
Proof.
  intros H1 H2 H3%divides_bnd H4%divides_bnd; lia.
Qed.

Fact divides_eq x y :
  (forall n, (n | x) <-> (n | y)) -> x = y.
Proof.
  destruct x, y; intros H.
  - reflexivity.
  - exfalso.
    enough (S(S y) <= S y) by lia.
    apply divides_bnd. lia.
    apply H, divides_zero.
  - exfalso.
    enough (S(S x) <= S x) by lia.
    apply divides_bnd. lia.
    apply H, divides_zero.
  - apply divides_eq'. lia. lia.
    + apply H. exists 1. lia.
    + apply H. exists 1. lia.
Qed.

Fact gamma_fun :
  functional gamma.
Proof.
  hnf. intros * H H'.
  apply divides_eq. intros n. split.
  - intros H1. apply H',H,H1.
  - intros H1. apply H,H',H1.
Qed.

Fact Gamma_concrete_gamma g :
  agree g (Gamma g) <-> forall x y n, (n | g x y) <-> (n | x) /\ (n | y).
Proof.
  split; intros H.
  - apply (Gamma_gamma gamma gamma1 gamma2 gamma3), H.
  - apply (gamma_Gamma gamma gamma1 gamma2 gamma3).
    + apply gamma_fun.
    + exact H.
Qed.

(*** GCDs with modulo *)

Module GCD_mod.
Section GCD_mod.
  Variable M: nat -> nat -> nat.
  Variable M_eq : forall x y, M x y = if le_lt_dec x y then x else M (x - S y) y.

  Fact M_le {x y} :
    M x y <= y.
  Proof.
    revert x.
    refine (size_rec (fun x => x) _).
    intros x IH. rewrite M_eq.
    destruct le_lt_dec as [H|H]. exact H.
    apply IH. lia.
  Qed.
  
  Variable gamma: nat -> nat -> nat -> Prop.
  Variable gamma1: forall y, gamma 0 y y.
  Variable gamma2: forall x y z, gamma x y z -> gamma y x z.
  Variable gamma3: forall x y z, x <= y -> gamma x (y - x) z -> gamma x y z.

  Fact gamma_M x y z :
    gamma (M y x) (S x) z -> gamma (S x) y z.
  Proof.
    revert y.
    refine (size_rec (fun x => x) _).
    intros y IH.
    rewrite M_eq.
    destruct le_lt_dec as [H|H].
    - apply gamma2.
    - intros H1. apply gamma3. lia. apply IH. lia. exact H1.
  Qed.
  
  Variable G: nat -> nat -> nat.
  Variable G_eq: forall x y, G x y = match x with 0 => y | S x' => G (M y x') x end.

  Fact G_gamma :
    respects G gamma.
  Proof.
    refine (size_rec (fun x => x) _).
    intros x IH y. rewrite G_eq.
    destruct x; cbn.
    - apply gamma1.
    - apply gamma_M. apply IH.
      enough (M y x <= x) by lia.
      apply M_le.
  Qed.

  Fact gamma_functional_respects g :
    respects g gamma -> functional gamma ->
    forall x y, g x y = match x with 0 => y | S x' => g (M y x') x end.
  Proof.
    intros HR HF x y.
    apply (HF x y).
    - apply HR.
    - destruct x.
      + apply gamma1.
      + apply gamma_M, HR.
  Qed.
End GCD_mod.
End GCD_mod.

(*** Predefined gcd function *)

Fact predefined_gcd x y :
  gamma x y (Nat.gcd x y).
Proof.
  intros n. split.
  - unfold divides. intros [k1 H]. split.
    + destruct (Nat.gcd_divide_l x y) as [k2 H1]. exists (k2 * k1). lia.
    + destruct (Nat.gcd_divide_r x y) as [k2 H1]. exists (k2 * k1). lia.
  - intros [H1 H2]. apply Nat.gcd_greatest; assumption.
Qed.


(*** Step-indexed Construction *)

Module Gcd_Step_Indexed.

Fixpoint G n x y := match n with 0 => 0 | S n' => Gamma (G n') x y end.
Definition gcd x y := G (S (x + y)) x y.

Compute gcd 12 16.

Fact G_index n n' x y :
  n > x + y -> n' >  x + y -> G n x y = G n' x y.
Proof.
  induction n as [|n IH] in n',x,y |-*;
    intros H1 H2.
  - exfalso. lia.
  - destruct n'.
    + exfalso. lia.
    + destruct x. reflexivity. 
      destruct y. reflexivity.
      cbn. destruct le_lt_dec; eapply IH;  lia.
Qed.

Fact Gamma_sat_gcd :
  agree gcd (Gamma gcd).
Proof.
  hnf. intros [|x] y. reflexivity.
  destruct y as [|y]. reflexivity.
  unfold gcd at 1. cbn [Gamma G]. 
  destruct le_lt_dec as [H|H];
    apply G_index; lia.
Qed.
End Gcd_Step_Indexed.

(*** Fibonacci *)

Notation agree1 f g := (forall n, f n = g n).

Definition Phi (f: nat -> nat) (n: nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | S (S n') => f n' + f (S n')
  end.

Fact phi_unique f g :
  agree1 f (Phi f) -> agree1 g (Phi g) -> agree1 f g.
Proof.
  intros H1 H2.
  apply (size_rec (fun n => n)).
  intros n IH. rewrite H1, H2.
  destruct n. reflexivity.
  destruct n. reflexivity.
  cbn. f_equal; apply IH; lia.
Qed.

Fixpoint Fib k n := match k with 0 => 0 | S k' => Phi (Fib k') n end.
Definition fib n := Fib (S n) n.

Compute fib 10.

Fact Fib_index n k k' :
  n < k -> n < k' -> Fib k n = Fib k' n.
Proof.
  induction k as [|k IH] in k', n |-*;
    intros H1 H2.
  - exfalso. lia.
  - destruct k'.
    + exfalso. lia.
    + destruct n. reflexivity.
      destruct n. reflexivity.
      cbn. f_equal; apply IH; lia.
Qed.

Fact Phi_fib :
  agree1 fib (Phi fib).
Proof.
  intros [|n]. reflexivity.
  destruct n. reflexivity.
  change (fib (S (S n))) with (Phi (Fib (S (S n))) (S (S n))).
  cbn [Phi]. f_equal. apply Fib_index; lia.
Qed.

Definition fib_rec {p: nat -> Type} :
  p 0 ->
  p 1 ->
  (forall n, p n -> p (S n) -> p (S(S n))) ->
  forall n, p n.
Proof.
  intros e1 e2 e3.
  apply (size_rec (fun n => n)).
  intros n IH.
  destruct n. exact e1.
  destruct n. exact e2.
  apply e3; apply IH; lia.
Defined.

Definition fib' : nat -> nat.
Proof.
  refine (fib_rec 0 1 _).
  exact (fun n a b => a + b).
Defined.

Compute fib' 10.
