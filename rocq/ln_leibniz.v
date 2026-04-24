Module Fun_eq.
  Definition eq : forall X: Type , X -> X -> Prop :=
    fun X x y => forall p: X -> Prop, p x -> p y.
  
  Definition  Q (X: Type) (x: X) : eq X x x :=
    fun p a => a.

   
  Definition  R (X: Type) (x y: X)
    : eq X x y -> forall p: X -> Prop, p x -> p y
    :=  fun a => a.
End Fun_eq.

Module Abstract_eq.
Section Abstract_eq.
  Variable eq : forall X, X -> X -> Prop.
  Variable Q  : forall X x, eq X x x.
  Variable R  : forall X x y, eq X x y -> forall p: X -> Prop, p x -> p y.

  Arguments eq {X}.
  Arguments Q {X}.
  Arguments R {X x y}.
  Notation "s = t" := (eq s t) : type_scope.
  Notation "s <> t" := (~ s = t) : type_scope.

  Fact eq_sym  X (x y: X) :
    x = y -> y = x.
  Proof.
    intros * e.
    change ((fun y => y = x) y). (* can be omitted *)
    apply (R e).
    apply Q.
  Qed.

  Print eq_sym.
  
  Check fun X (x y: X) (e : x = y) =>
          R e (fun y => y = x) (Q x).

  Fact eq_trans  X (x y z: X) :
    x = y -> y = z -> x = z.
  Proof.
    intros * e.
    change ((fun y => y = z -> x = z) y). (* can be omitted *)
    apply (R e).
    easy.
  Qed.

  Print eq_trans.

  Inductive True : Prop := I.
   
  Fact neq_True_False:
    True <> False.
  Proof.
    intros e.
    change ((fun X => X) False).  (* can be omitted *)
    apply (R e).
    exact I.
  Qed.
  Print neq_True_False.
  
  Check fun (e : True = False) =>
          R e (fun X => X) I.
  
  Fact neq_O_S n :
    0 <> S n.
  Proof.
    intros e.    
    change ((fun n => match n with 0 => True | S n => False end) (S n)).
    apply (R e).
    exact I.
  Qed.
  Print neq_O_S.
 
  Fact S_injective x y :
    S x = S y -> x = y.
  Proof.
    intros e.    
    change ((fun n => match n with 0 => True | S y => x = y end) (S y)).
    apply (R e).
    apply Q.
  Qed.
  
  Definition match_nat
    : nat -> forall Z: Type, Z -> (nat -> Z) -> Z
    := fun n Z z f => match n with 0 => z | S n => f n end.

  Fact neq_O_S' n :
    0 <> S n.
  Proof.
    intros e.    
    change ((fun n => match_nat n Prop True (fun _ => False)) (S n)).
    apply (R e).
    exact I.
  Qed.

  Fact S_injective' x y :
    S x = S y -> x = y.
  Proof.
    intros e.    
    change ((fun n => match_nat n Prop True (fun y => x = y)) (S y)).
    apply (R e).
    apply Q.
  Qed.
 
End Abstract_eq.
End Abstract_eq.

(** Using equality as provided by Rocq *)
 
Fact eq_sym  X (x y: X) :
  x = y -> y = x.
Proof.
  intros e.
  rewrite e.
  easy.
Qed.

Fact eq_trans  X (x y z: X) :
  x = y -> y = z -> x = z.
Proof.
  intros e.
  rewrite e.
  easy.
Qed.

Fact neq_True_False:
  True <> False.
Proof.
  intros e.
  rewrite <-e.
  exact I.
Qed.

Fact S_injective x y :
  S x = S y -> x = y.
Proof.
  intros e.
  change match S x with 0 => False | S x => x = y end.
  rewrite e.
  reflexivity.
Qed.


Fact neq_O_S n :
  0 <> S n.
Proof.
  intros e.    
  change match S n with 0 => True | S n => False end.
  rewrite <-e.
  exact I.
Qed.
    
