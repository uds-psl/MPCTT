From Coq Require Import Lia.
Definition dec (X: Type) : Type := X + (X -> False).
Definition eqdec X := forall x y: X, dec (x = y).
Notation decidable p := (forall x, dec (p x)).
Notation sig := sigT.
Notation Sig := existT.
Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Implicit Types n k: nat.

Section EWO.
  Variable p: nat -> Prop.
  Variable p_dec: decidable p.

  Inductive T (n: nat) : Prop := C (phi: ~p n -> T (S n)).

  Definition W'
    : forall n, T n -> sig p
    := fix f n a := let (phi) := a in
                    match p_dec n with
                    | inl h => (Sig p n h)
                    | inr h => f (S n) (phi h)
                    end.

  (* Eliminator generalizing W' *)
  
  Definition elim_T (q: nat -> Type)
    : (forall n, (~p n -> q (S n)) -> q n) ->
      forall n, T n -> q n
    := fun e => fix f n a := let (phi) := a in e n (fun h => f (S n) (phi h)).


  Fact W'_elim_T_agree :
    W' = elim_T (fun _ => sig p)
           (fun n f => match p_dec n with
                    | inl h => (Sig p n h)
                    | inr h => f h
                    end).
  Proof.
    reflexivity.
  Qed.
  
  Fact elim_T_unfold q e n phi :
    elim_T q e n (C n phi) = e n (fun h => elim_T q e (S n) (phi h)).
  Proof.
    reflexivity.
  Qed.

End EWO.
