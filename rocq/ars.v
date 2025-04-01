From Stdlib Require Import Lia.
Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).
Ltac refl := reflexivity.

Section Path.
  Variable X: Type.
  Variable R: X -> X -> Type.
  Implicit Types x y z: X.

  Inductive path (x: X) : X -> Type :=
  | P1 : path x x
  | P2 : forall x' y, R x x' -> path x' y -> path x y.

  Definition len
    : forall {x y}, path x y -> nat
    := fix f x _ a := match a with
                      | P1 _ => 0
                      | P2 _ x' y r a => S (f x' y a)
                      end.

  Definition app
    : forall {z x y}, path x y -> path y z -> path x z
    := fun z => fix f x _ a := match a with
                            | P1 _ => fun b => b
                            | P2 _ x' y r a' => fun b => P2 x x' z r (f x' y a' b)
                            end.

  Fact app_P1_eq x z (b: path x z) :
    app (P1 x) b = b.
  Proof.
    refl.
  Qed.

  Fact app_P2_eq x x' y z (r: R x x') (a: path x' y) (b: path y z) :
    app (P2 x x' y r a) b = P2 x x' z r (app a b).
  Proof.
    refl.
  Qed.

  (* See the types of the pattern variables using refine *)
  Goal forall {z x y}, path x y -> path y z -> path x z.
  Proof.
    refine (fun z => fix f x _ a :=
              match a with
              | P1 _ => fun b => _
              | P2 _ x' y r a' => fun b => _
              end).
    - exact b.
    - exact (P2 x x' z r (f x' y a' b)).
  Qed.

  Definition path_elim (p: forall x y, path x y -> Type)
    : (forall x, p x x (P1 x)) ->
      (forall x x' y r a, p x' y a -> p x y (P2 x x' y r a)) ->
      forall x y a, p x y a
    := fun e1 e2 => fix f x _ a := match a with
                                | P1 _ => e1 x
                                | P2 _ x' y r a' => e2 x x' y r a' (f x' y a') 
                                end.

  Goal forall x y z (a: path x y) (b: path y z),
      len (app a b) = len a + len b.
  Proof.
    intros x y z. revert x y.
    refine (path_elim _ _ _); cbn.
    - intros x b. refl.
    - intros x x' y r a IH b. f_equal. apply IH.
  Qed.

  Goal forall x y z (a: path x y) (b: path y z),
      len (app a b) = len a + len b.
  Proof.
    induction a as [x|x x' y r a IH]; cbn.
    - intros b. refl.
    - intros b. f_equal. apply IH.
  Qed.
  
  Fact path_step x y :
    R x y -> path x y.
  Proof.
    intros H. eapply P2. exact H.  apply P1.
  Qed.

  Definition path_index (p: X -> X -> Type)
    : (forall x, p x x) ->
      (forall x x' y, R x x' -> p x' y -> p x y ) ->
      forall x y, path x y -> p x y
    := fun e1 e2 => fix f x _ a := match a with
                                | P1 _ => e1 x
                                | P2 _ x' y r a' => e2 x x' y r (f x' y a') 
                                end.

  Fact path_trans x y z :
    path x y -> path y z -> path x z.
  Proof.
    revert x y.
    refine (path_index _ _ _).
    - easy.
    - intros x x' y r IH H.
      eapply P2. exact r. apply IH, H.
  Qed.
End Path.
Arguments path {X}.
Arguments path_index {X R p}.

Module Exercise.
  Definition R x y := (S x = y).
  Goal forall x y, path R x y <=> x <= y.
  Proof.
    split.
    - revert x y.
      refine (path_index _ _).
      + lia. 
      + intros x y' y <-. lia.
    - enough (forall k, path R x (k + x)) as H.
      + intros H1. generalize (H (y - x)).
        replace ((y - x) + x) with y by lia.
        easy.
      + induction k as [|k IH] in x |-*.
        * apply P1.
        * apply (P2 _ _ x (S x)). 
          -- refl.
          -- replace (S k + x) with (k + S x) by lia.
             apply IH.
  Qed.
End Exercise.

Section Star.
  Variable X: Type.
  Implicit Type p: X -> X -> Type.

  Definition refl p := forall x, p x x.
  Definition trans p := forall x y z, p x y -> p y z -> p x z.
  Definition incl p p' := forall x y, p x y -> p' x y.

  Fact path_star p R :
    refl p -> trans p -> incl R p -> forall x y, path R x y -> p x y.
  Proof.
    intros H1 H2 H3.
    refine (path_index _ _).
    - exact H1.
    - intros x x' y H4 IH.
      eapply H2. 2: exact IH. apply H3, H4.
  Qed.
    
  Fact path_fun_char R x y :
    path R x y <=> forall p, refl p -> trans p -> incl R p -> p x y.
  Proof.
    split.
    - intros H1 p  H2 H3 H4.
      revert x y H1. apply path_star; assumption.
    - intros H. apply H; hnf.
      + apply P1.
      + eauto using app.
      + apply path_step.
  Qed.
  
  Fact path_path R (x y: X) :
    path R x y <=> path (path R) x y.
  Proof.
    split.
    - apply path_step. 
    - revert x y. apply path_star.
      + constructor.
      + intros x y z. apply app.
      + easy.
  Qed.
End Star.

  


  

  


  
  
