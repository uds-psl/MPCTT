Goal forall X (x y: X), x = y -> y = x.
Proof.
  intros * e.
  pattern y.  (* conversion *)
  rewrite <- e.
  reflexivity.
Qed.
 
Goal True <> False.
  intros e.
  pattern False.  (* conversion *)
  rewrite <- e.
  exact I.
Qed.

Goal true <> false.
  intros e.
  change (if false then True else False).  (* conversion *)
  pattern false.  (* conversion *)
  rewrite <- e.
  exact I.
Qed.

Goal forall x y, S x = S y -> x = y.
  intros * e.
  change (x = match S y with 0 => 0 | S y => y end).
  pattern (S y).
  rewrite <- e.
  reflexivity.
Qed.
    
Section AbstractEquality.
  Variable eq : forall X, X -> X -> Prop.
  Variable Q  : forall X x, eq X x x.
  Variable R  : forall X x y (p: X -> Prop), eq X x y -> p x -> p y.

  Arguments eq {X}.
  Arguments Q {X}.
  Arguments R {X x y}.
  Notation "s = t" := (eq s t) : type_scope.
  Notation "s <> t" := (~ s = t) : type_scope.

  Goal forall X (x y: X), x = y -> y = x.
  Proof.
    intros * e.
    pattern y.
    apply (R _ e).
    apply Q.
  Qed.
  
  Check fun X (x y: X) (e : x = y) =>
          R (fun y => y = x) e (Q x).
  
  Goal True <> False.
    intros e.
    pattern False.
    apply (R _ e).
    exact I.
  Qed.
  
  Check fun X (x y: X) (e : x = y) =>
          R (fun y => y = x) e (Q x).

  Goal true <> false.
    intros e.
    change (if false then True else False).
    pattern false.
    apply (R _ e).
    exact I.
  Qed.

  Check fun (e : true = false) =>
          R (fun b:bool => if b then True else False) e I.

  Goal forall x y, S x = S y -> x = y.
    intros * e.
    change (x = match S y with 0 => 0 | S y => y end).
    pattern (S y).
    apply (R _ e).
    apply Q.
  Qed.
  
  Check fun x y (e : S x = S y) =>
          R (fun z => x = match z with 0 => 0 | S y => y end) e (Q x).
