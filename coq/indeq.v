From Coq Require Import Arith Bool.
Ltac refl := reflexivity.
Notation sig := sigT.
Notation Sig := existT.
Notation pi1 := projT1.
Notation pi2 := projT2.
Notation "'if' x 'is' p 'then' A 'else' B" :=
  (match x with p => A | _ => B end)
    (at level 200, p pattern,right associativity).
Definition FE : Prop :=
  forall X (p: X -> Type) (f g: forall x, p x), (forall x, f x = g x) -> f = g.
Definition stable (P: Prop) :=
  ~~P -> P.

Definition J {X} {x: X} (p: forall y, x = y -> Type)
  : p x eq_refl -> forall y e, p y e
  := fun a y e => match e with eq_refl => a end.

Definition cast {X} {p: X -> Type} {x: X}
  : forall {y}, x = y -> p x -> p y
  := fun y e a => match e with eq_refl => a end.

Goal forall X (x y: X) p (e: x = y) a,
    cast e a = J (fun y e => p y) a y e.
Proof.
  refl.
Qed.

Goal forall X (x y: X) p (a: p x),
    cast eq_refl a = a.
Proof.
  refl.
Qed.

Section SigmaTau.
  Variable X: Type.
  Implicit Types x y z: X.
  Definition sigma {x y}
    : x = y -> y = x
    := fun e => cast (p:= fun y => y = x) e eq_refl.
  Definition tau {x y z}
    : x = y -> y = z -> x = z
    := fun e => cast (p:= fun y => y = z -> x = z) e (fun a => a).
  Definition phi {A} (f: X -> A) {x y}
    : x = y -> f x = f y
    := fun e => cast (p:= fun y => f x = f y) e eq_refl.
  
  Fact sigma_involutive x y (e: x = y) :
    sigma (sigma e) = e.
  Proof.
    destruct e. refl.
  Qed.
  Fact tau_trans x y z z' (e1: x = y) (e2: y = z) (e3: z = z') :
    tau e1 (tau e2 e3) = tau (tau e1 e2) e3.
  Proof.
    destruct e1, e2, e3. refl.
  Qed.
  Fact tau_sigma x y (e: x = y) :
    tau e (sigma e) = eq_refl.
  Proof.
    destruct e. refl.
  Qed.
End SigmaTau.
Arguments sigma {X x y}.
Arguments tau {X x y z}.
 
Section UIP.
  Variable X: Type.
  Definition UIP := forall (x y: X) (e e': x = y), e = e'.
  Definition UIP' := forall (x : X) (e: x = x), e = eq_refl.
  Definition K_Streicher := forall (x: X) (p: x = x -> Prop), p (eq_refl x) -> forall e, p e.
  Definition CD := forall (p: X -> Type) (x: X) (a: p x) (e: x = x), cast e a = a.
  Definition DPI := forall (p: X -> Type) x u v, Sig p x u = Sig p x v -> u = v.
  
  Goal UIP -> UIP'.
  Proof.
    intros H x e. apply H.
  Qed.
   
  Goal UIP' -> UIP.
  Proof.
    intros H x y e e'. destruct e'.  apply H.
  Qed.
  
  Goal UIP' -> K_Streicher.
  Proof.
    intros H x p a e. rewrite (H x e). exact a.
  Qed.

  Goal K_Streicher -> CD.
  Proof.
    intros H p x a. apply H. refl.
  Qed.
  
  Goal CD -> DPI.
  Proof.
    intros H p x.
    enough (forall a b: sigT p, a = b -> forall e: pi1 a = pi1 b, cast e (pi2 a) = pi2 b) as H'.
    - intros u v e'. apply (H' _ _ e' eq_refl).
    - intros a b []. apply H.
  Qed.
    
  Goal DPI -> UIP'.
  Proof.
    intros H x e.
    apply (H (eq x)). revert e.
    enough (forall y (e: x = y), Sig (eq x) y e = Sig (eq x) x eq_refl) as H'.
    - apply H'. 
    - intros y []. refl.
  Qed.
  
  Lemma cast_eq {x y: X} :
    forall e: x = y, cast e (eq_refl x) = e.
  Proof.
    destruct e. refl.
  Qed.

  Goal CD -> UIP'.
  Proof.
    intros H x.
    enough (forall y (e: x = y), e = cast e (eq_refl x)) as H1.
    - intros e. rewrite (H1 x e). apply H.
    - destruct e. refl.
  Qed.
End UIP.

Definition  HF X (f: forall x y: X, x = y -> x = y) :=
  forall x y (e e': x = y), f x y e = f x y e'.

Lemma Hedberg' X :
  ex (HF X) -> UIP X.
Proof.
  intros [f H] x y.
  assert (H1: forall e: x = y,  tau (f x y e) (sigma (f y y eq_refl)) = e).
  { destruct e. apply tau_sigma. }
  intros e e'.
  rewrite <-(H1 e), <-(H1 e').
  f_equal. apply H.
Qed.

Theorem Hedberg X :
  (forall x y: X, x = y \/ x <> y) -> UIP X.
Proof.
  intros d. apply Hedberg'.
  exists (fun x y e => if d x y is or_introl e' then e' else e).
  intros x y e e'.
  destruct d as [e''|h]. refl. destruct (h e).
Qed.

(* Contributed by Dominik Kirst, 18 Feb. 2021 *)
Fact FE_stable_HF X :
  FE -> (forall x y: X, stable (x = y)) -> sig (HF X).
Proof.
  intros F G.
  exists (fun x y e => G x y (fun f => match f e with end)).
  intros x y e e'. f_equal. apply F. intros f.
  exfalso. exact (f e).
Qed.

Fact FE_test_eq_stable :
  FE -> forall f g: nat -> bool, stable (f = g).
Proof.
  intros F f g H. apply F. intros x.
  destruct (bool_dec (f x) (g x)) as [H1|H1].
  - exact H1.
  - contradict H. contradict H1. f_equal.
Qed.  


(*** Direct proof of UIP_nat *)
(* Idea from Andrej Dudenhefner *)

Module UIP_nat.
  Lemma nat_eqdec_eq x :
    Nat.eq_dec x x = left eq_refl.
  Proof.
    induction x. refl. 
    simpl. rewrite IHx. refl.
  Qed.
  Lemma UIP_nat' (x y: nat) :
  forall e: x = y,
    match Nat.eq_dec x y with
    | left e' => cast e' eq_refl = e
    | _ => True
    end.
  Proof.
    destruct e. rewrite nat_eqdec_eq. refl.
  Qed.
  Fact UIP_refl_nat (x: nat) :
    forall e: x = x, e = eq_refl.
  Proof.
    intros e.
    generalize (UIP_nat' x x e).
    rewrite nat_eqdec_eq. intros []. refl.
  Qed.
End UIP_nat.
  
(*** UIP propagates to identity at Type *)

Inductive id X (x: X) : X -> Set := Q : id X x x.
(* Must write Set, Type will be downgraded to Prop *)
Arguments id {X}.
Arguments Q {X}.

Check id nat.
Check id Type.

Definition D {X} {x y: X}
  : id x y -> x = y
  := fun a => match a with Q _ => eq_refl x end.
Definition U {X} {x y: X}
  : x = y -> id x y
  := fun e => match e with eq_refl _ => Q x end.
Fact UD_eq {X} {x y: X} (a: id x y) :
  U (D a) = a.
Proof.
  destruct a. refl.
Qed.
Fact DU_eq {X} {x y: X} (e: x = y) :
  D (U e) = e.
Proof.
  destruct e. refl.
Qed.

Fact id_fun X Y (f: X -> Y) (x x': X) :
  id x x' -> id (f x) (f x').
Proof.
  destruct 1. apply Q.
Qed.

Definition UIP_id X := forall (x y: X) (a b: id x y), id a b.
Fact UIP_up X :
  UIP X -> UIP_id X.
Proof.
  intros H x y a b.
  rewrite <-(UD_eq a), <-(UD_eq b).
  apply id_fun.
  apply U. apply H.
Qed.
Fact UIP_down X :
  UIP_id X -> UIP X.
Proof.
  intros H x y e e'.
  rewrite <-(DU_eq e), <-(DU_eq e').
  apply f_equal. apply D. apply H.
Qed.

