Module Abstract_equality.
Section Abstract_equality.
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

  
  Fact neq_true_false :
    true <> false.
  Proof.
    intros e.
    change ((fun b:bool => if b then True else False) false).  (* can be omitted *)
    apply (R e).
    exact I.
  Qed.
  Print neq_true_false.

  Check fun (e : true = false) =>
          R e (fun b:bool => if b then True else False) I.

  Fact S_injective x y :
    S x = S y -> x = y.
  Proof.
    intros e.
    change ((fun n => match n with 0 => x = 0 | S y => x = y end) (S y)).
    apply (R e).
    apply Q.
  Qed.
  
  Check fun x y (e : S x = S y) =>
          R e (fun n => match n with 0 => x = 0 | S y => x = y end) (Q x).

End Abstract_equality.
End Abstract_equality.

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
  
Fact neq_true_false :
  true <> false.
Proof.
  intros e.
  change (if true then False else True).
  rewrite e.
  exact I.
Qed.

Fact S_injective x y :
  S x = S y -> x = y.
Proof.
  intros e.
  change (match S x with 0 => False | S x => x = y end).
    rewrite e.
    reflexivity.
Qed.

    
