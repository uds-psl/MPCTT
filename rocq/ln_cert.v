From Stdlib Require Import Lia.
Notation "~ X" := (X -> False) (at level 75, right associativity) : type_scope.

Definition inv {X Y: Type} (g: Y -> X) (f: X -> Y) :=
  forall x, g (f x) = x.
Definition injective {X Y} (f: X -> Y) :=
  forall x x', f x = f x' -> x = x'.
Fact inv_injective X Y (f: X -> Y) (g: Y -> X) :
  inv g f -> injective f.
Proof.
  congruence.
Qed.
Inductive injection (X Y: Type) : Type :=
| Injection (f: X -> Y) (g: Y -> X) (H: inv g f).


(*** Decisions and deciders *)

Definition dec (X: Type) : Type := X + (~X).

Goal forall x y, dec (x <= y).
Proof.
  intros x y.
  destruct (x - y) as [|a] eqn:E.
  - left; lia.
  - right; lia.
Qed.

Goal forall x y, dec (x <= y).
Proof.
  induction x; destruct y; unfold dec.
  1-3: intuition lia.
  specialize (IHx y) as [IH|IH]; intuition lia.
Qed.

Goal forall x y, dec (x <= y).
Proof.
  intros x y.
  enough (forall z, x - y = z -> dec (x <= y)) by eauto.
  intros [|z] E.
  - left. lia.
  - right; lia.
Qed.

Section Assignment.
  Variable D : forall p: nat -> Type, p 0 -> (forall n, p (S n)) -> forall n, p n.
  Goal forall x y, dec (x <= y).
  Proof.
    intros x y.
    enough (forall z, x - y = z -> dec (x <= y)) as H.
    - refine (H (x-y) _). lia.
    - refine (D _ _ _).
      + intros H. left. lia.
      + intros H. right. lia.
  Qed.
End Assignment.
  

Goal forall x y, dec (x <= y).
Proof.
  intros x y.
  assert (dec (x - y = 0)) as [H|H].
  - destruct (x - y) as [|a].
    + left. reflexivity.
    + right. lia.
  - left; lia.
  - right; lia.
Qed.


Goal forall X Y,
    dec X -> dec Y -> dec (X + Y).
Proof.
  unfold dec. tauto.
Qed.

Definition eqdec X := forall x y: X, dec (x = y).

Fact eqdec_nat : eqdec nat.
Proof.
  intros x y.
  destruct ((x - y) + (y -x)) as [|a] eqn:E.
  - left; lia.
  - right; lia.
Qed.

Goal eqdec nat.
Proof.
  hnf.
  induction x; destruct y.
  all: unfold dec.
  1-3: intuition congruence.
  destruct (IHx y) as [H|H]; intuition congruence.
Qed.

Fact eqdec_prod X Y :
  eqdec X -> eqdec Y -> eqdec (X*Y).
Proof.
  intros dX dY [x y] [x' y'].
  destruct (dX x x') as [H1|H1].
  - destruct (dY y y') as [H2|H2].
    all: unfold dec.
    all: intuition congruence.
  - unfold dec; intuition congruence.
Qed.
 
Fact eqdec_injective {X Y f} :
  @injective X Y f -> eqdec Y -> eqdec X.
Proof.
  intros H d x x'. specialize (H x x').
  destruct (d (f x) (f x')) as [H1|H1];
    unfold dec in *; intuition congruence.
Qed.

Fact eqdec_injection X Y :
  injection X Y -> eqdec Y -> eqdec X.
Proof.
  intros [f g H] H1.
  apply inv_injective in H.
  revert H H1. apply eqdec_injective.
Qed.

From Stdlib Require Import List.
Import ListNotations.
Notation "x 'el' A" := (In x A) (at level 70).

Fact eqdec_list_membership X :
  eqdec X -> forall (x:X) A, dec (x el A).
Proof.
  intros d x.
  induction A as [|a A IH]; cbn.
  - right. easy.
  - destruct (d a x) as [H|H].
    + left. auto.
    + destruct IH as [IH|IH].
      * left. auto.
      * right. tauto.
Qed.

(*** Computational Soundness *)

Definition LEM := forall X:Prop, X \/ ~X.
Definition UD := forall X:Prop, X + (~X).

Goal False -> UD.
Proof.
  intros H X. left. exfalso. exact H.
Qed.
  
Goal UD -> LEM.
  intros F X.
  specialize (F X) as [F|F]; auto.
Qed.

(** Computational soundness: CTT cannot prove [LEM -> UD] *)
(** Logical soundness: CTT cannot prove [LEM -> False] *)

(** Computational soundness implies logical soundness *)
Goal ~LEM -> LEM -> UD.
Proof.
  intros F G X. left. exfalso. auto.
Qed.


(*** Sigma types *)

Inductive sig {X: Type} (p: X -> Type) : Type :=
| Sig : forall x, p x -> sig p.

Lemma discriminate_Sigma X (p: X -> Type) :
  sig p -> forall Z:Type, (forall x, p x -> Z) -> Z.
Proof.
  intros [x a] Z. eauto.
Qed.

Definition elim_Sigma X (p: X -> Type) (q: sig p -> Type)
  : (forall x h, q (Sig p x h)) -> forall a, q a
  := fun F a  => match a with Sig _ x h => F x h end.

Definition pi1 {X: Type} {p: X -> Type}
  : sig p -> X
  := @elim_Sigma X p _ (fun x y => x).

Definition pi2 {X: Type} {p: X -> Type}
  : forall a: sig p, p (pi1 a)
  := @elim_Sigma X p _ (fun x y => y).

Fact eta_law X (p: X -> Type) :
  forall a, a = Sig p (pi1 a) (pi2 a).
Proof.
  apply elim_Sigma. cbn. reflexivity.
Qed.

Hint Resolve Sig : core.  (* for eauto *)

(*** Translations *)

Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).

Abbreviation decider p := (forall x, dec (p x)).

Notation "'Sigma' x .. y , p" :=
  (sig (fun x => .. (sig (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.

Lemma Sigma_dec_equiv X (p: X -> Type) :
  decider p <=>
    Sigma f: X ->  bool , forall x,
        if f x then p x else ~p x.
Proof.
  split.
  - intros F.
    exists (fun x => if F x then true else false).
    intros x.
    destruct (F x) ; easy. (* dependent elimination *)
  - intros [f H] x.
    specialize (H x).
    destruct (f x); unfold dec; auto.
Qed.

Lemma Sigma_eqdec_equiv X :
  eqdec X <=>
    Sigma f: X -> X -> bool , forall x y,
        if f x y then x = y else x <> y.
Proof.
  split.
  - intros F.
    exists (fun x y => if F x y then true else false).
    intros x y.
    destruct (F x y); easy. (* dependent elimination *)
  - intros [f H] x y.
    specialize (H x y).
    destruct (f x y); unfold dec; auto.
Qed.

Lemma Sigma_sum_equiv X (p q: X -> Type) :
  (forall x, p x + q x) <=>
    Sigma f: X -> bool, forall x,
        if f x then p x else q x.
Proof.
  split.
  - intros F.
    exists (fun x => if F x then true else false).
    intros x.
    destruct (F x); easy. (* dependent elimination *)
  - intros [f H] x.
    specialize (H x).
    destruct (f x); auto.
Qed.
 
Lemma Sigma_Skolem X Y (p: X -> Y -> Type) :
  (forall x, sig ( p x)) -> Sigma f: X -> Y, forall x, p x ( f x).
Proof.
  intros F.
  exists (fun x => match (F x) with Sig _ y _ => y end).
  intros x.
  destruct (F x); easy. (* dependent elimination *)
Qed.

Lemma Sigma_Skolem' X Y (p: X -> Y -> Type) :
  (forall x, sig ( p x)) <=> Sigma f: X -> Y, forall x, p x ( f x).
Proof.
  split.
  - apply Sigma_Skolem.
  - intros [f H] x.
    specialize (H x). eauto. 
Qed.

Lemma Sigma_option_equiv X Y (p: X -> Y -> Type)  (q: X -> Type) :
  (forall x, sig (p x) + q x) <=>
    Sigma f: X -> option Y, forall x,
        match f x with Some y => p x y | None => q x end.
Proof.
  split.
  - intros F.
    exists (fun x => match F x with inl (Sig _ y H) => Some y |inr _ => None end).
    intros x.
    destruct (F x) as [[y H] | H]; easy.  (* dependent elimination *)
  - intros [f H] x.
    specialize (H x).
    destruct (f x); eauto.
Qed.

(*** Bijections *)

Inductive bijection (X Y: Type) : Type :=
| Bijection: forall (f: X -> Y) (g: Y -> X), inv g f -> inv f g -> bijection X Y.

(* Note first use of tactic "unshelve eexists" *)
Fact Sigma_product X Y :
  bijection (X * Y) (sig (fun _:X => Y)).
Proof.
  exists (fun a => Sig (fun _:X => Y) (fst a) (snd a))
    (fun a => (pi1 a, pi2 a)).
  all: hnf; cbn.
  all: intros [x y]; cbn.
  all: reflexivity.
Qed.

Fact bijection_sum X Y :
  bijection (X + Y) (sig (fun b:bool => if b then X else Y)).
Proof.
  exists (fun a => match a return sig (fun b:bool => if b then X else Y) with
           | inl x => Sig _ true x
           | inr y => Sig _ false y
           end)
    (fun a => match a with
           | Sig _ true x => inl x
           | Sig _ false y => inr y
           end).
  all: hnf.
  - intros [x|y]; reflexivity.
  - intros [[|] a]; reflexivity.
Qed.

(* Note: First time we construct a reducible function with tactics *)   
Fact bijection_injection X Y :
  bijection (injection X Y) (Sigma f g, @inv X Y g f).
Proof.
  unshelve eexists.
  - intros [f g H]. exists f, g. exact H.
  - intros [f [g H]]. exists f g. exact H.
  - hnf. intros [f g H]. reflexivity.
  - hnf. intros [f [g H]]. reflexivity.
Qed.

Fact bijection_bijection X Y :
  bijection (bijection X Y) (Sigma f g, @inv X Y g f /\ inv f g).
Proof.
  unshelve eexists.
  - intros [f g H1 H2]. exists f, g. easy.
  - intros [f [g H]]. exists f g; easy.
  - hnf. intros [f g H1 H2]. reflexivity.
  - hnf. intros [f [g [H1 H2]]]. reflexivity.
Qed.

(*** Least Witness Operator *)

Definition safe p n := forall k, k < n -> ~p k.
Definition least p n := p n /\ safe p n.

Fact safe_O p :
  safe p 0.
Proof.
  hnf. lia.
Qed.

Fact safe_S p n :
  safe p n -> ~p n -> safe p (S n).
Proof.
  intros H1 H2 k H3. unfold safe in *.
  assert (k < n \/ k = n) as [H|H] by lia.
  - apply H1. easy.
  - congruence.
Qed.

Fact least_unique p x x' :
  least p x -> least p x' -> x = x'.
Proof.
  intros [H1 H2] [H3 H4].
  specialize (H2 x').
  specialize (H4 x).
  enough (~ x < x' /\ ~ x' < x) by lia.
  auto.
Qed.

Fact worker {p: nat -> Prop} :
  decider p -> forall n, safe p n + Sigma k, k < n /\ least p k.
Proof.
  intros d.
  induction n as [|n IH].
  - left. apply safe_O.
  - destruct IH as [IH|IH].
   + destruct (d n) as [H|H].
     * right. exists n. split. lia. easy.
     * left. apply safe_S; easy.
   + destruct IH as (k&IH1&IH2). eauto 6.
Qed.

Fact lwo (p: nat -> Prop) :
  decider p -> sig p -> sig (least p).
Proof.
  intros d [n H].
  destruct (worker d n) as [H1|(k&H1&H2&H3)].
  - exists n. easy.
  - exists k. easy.
Qed.

Fact decider_safe  {p: nat -> Prop} :
  decider p -> decider (safe p).
Proof.
  intros d n.
  destruct (worker d n) as [H1|(k&H1&H2&H3)].
  - left. exact H1.
  - right. intros H. specialize (H k). auto.
Qed.

Fact decider_least  (p: nat -> Prop) :
  decider p -> decider (least p).
Proof.
  intros d n.
  destruct (decider_safe d n) as [H|H].
  - destruct (d n) as [H1|H1].
    + left. easy.
    + right. intros [H2 H3]. auto.
  - right. intros [H4 H5]. auto.
Qed.

Module SimplyTyped.
  Section SimplyTyped.
    Variable p : nat -> Prop.
    Variable d : nat -> bool.

    Fixpoint W n : option nat
      := match n with
         | 0 => None
         | S n => match W n with
                 | Some k => Some k
                 | None => if d n then Some n else None
                 end
         end.

    Variable d_correct : forall n, if d n then p n else ~p n.

    Fact W_correct n :
      match W n with
      | Some k => k < n /\ least p k
      | None => safe p n
      end.
    Proof.
      induction n as [|n IH]; cbn.
      - apply safe_O.
      - destruct (W n) as [k|].
        + intuition lia.
        + assert (H:= d_correct n).
          destruct (d n).
          * unfold least; intuition lia.
          * apply safe_S; easy.
    Qed.
  End SimplyTyped.
  Check W.
  Check W_correct.
End SimplyTyped.
    
(*** CFE *)

Definition CFE := False -> forall X:Type, X.

Inductive void : Type := .
Definition elim_void
  : void -> forall X:Type, X
  := fun v => match v with end.

Fact CFE_bijection_empty :
  CFE -> forall X: Type, ~ X ->  bijection X void.
Proof.
  intros F X f.
  exists (fun x => F (f x) void)
    (fun v => elim_void v X)
    ; hnf.
  - intros x. exfalso. exact (f x).
  - intros [].
Qed.

Goal CFE -> bijection False void.
Proof.
  intros F.
  apply CFE_bijection_empty.
  exact F. auto.
Qed.

Goal CFE -> forall x, x <> 0 -> Sigma y, x = S y.
Proof.
  intros F x H.
  destruct x as [|y].
  - apply F. auto.
  - eauto.
Qed.

(* CFE can be defined in Rocq using discrimination
   on inductive definition of [False] *)
Goal CFE.
Proof.
  intros [].
Qed.

    


