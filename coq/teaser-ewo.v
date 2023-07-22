From Coq Require Import Lia.
Definition dec (X: Type) : Type := X + (X -> False).
Definition eqdec X := forall x y: X, dec (x = y).
Notation decidable p := (forall x, dec (p x)).
Notation sig := sigT.
Notation Sig := existT.

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

  Lemma T_lower n :
    T n -> T 0.
  Proof.
    induction n as [|n IH]. easy.
    intros H. apply IH. constructor. auto.
  Qed.

  Definition W : ex p -> sig p.
  Proof.
    intros H. eapply W' with (n:=0).
    destruct H as [n H].
    enough (T n) as H1%T_lower by easy.
    constructor. easy.
  Qed.

End EWO.

Definition inv {X Y: Type} (g: Y -> X) (f: X -> Y) := forall x, g (f x) = x.

Section Countable_EWO.
  Variable X: Type.
  Variable f: X -> nat.
  Variable g: nat -> X.
  Variable gf: inv g f.
  Variable p: X -> Prop.
  Variable p_dec: decidable p.

  Definition cewo : ex p -> sig p.
  Proof.
    intros H.
    pose (q n := p (g n)).
    assert (q_dec: decidable q).
    { intros n. apply p_dec. }
    assert (q_ex: ex q).
    { destruct H as [x H]. exists (f x). hnf. congruence. }
    enough (sig q) as [n H1].
    { exists (g n). exact H1. }
    apply W; assumption.
  Qed.
End Countable_EWO.
    
      
