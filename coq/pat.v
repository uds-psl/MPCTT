(** We use Coq's definitions for falsity, truth, 
    conjunctions, and disjunctions. *)

Module Show_Definitions.
  Inductive False := .
  Inductive True := I.
  (** We cheat with negation.  Will be explained later. *)
  Notation "~ P" := (P -> False).
  Inductive and (P Q: Prop) : Prop :=
  | conj: P -> Q -> and P Q.
  Inductive or (P Q: Prop) : Prop :=
  | or_introl: P -> or P Q
  | or_intror: Q -> or P Q.
End Show_Definitions.

Print False.
Print True.
Print and.
Print or.

Definition elim_False
  : forall Z: Type, False -> Z
  := fun Z a => match a with end.

Locate "/\".
Check and.
Print and.
Print or.
About or.  (* Overloaded implicit arguments *)

Definition match_and
  : forall X Y Z: Prop, X /\ Y -> (X -> Y -> Z) -> Z
  := fun X Y Z a e => match a with conj x y => e x y end.

Definition match_or
  : forall X Y Z: Prop, X \/ Y -> (X -> Z) -> (Y -> Z) -> Z
  := fun X Y Z a e1 e2 => match a with or_introl x => e1 x | or_intror y => e2 y end.

Section Demo.
  Variables X Y Z: Prop.

  (** We type check normal proofs.  Note how 
      implicit arguments are supplied if necessary.
      Also note how parentheses are ommitted in the types derived. **)      

  Check fun x:X => x.
  Check fun (x: X) (y: Y) => x.
  Check fun (x: X) (y: Y) => y.
  Check fun (f: X -> Y -> Z) y x => f x y.
  Check fun h: X /\ Y => match h with conj x y => x end.
  Check fun h: X /\ Y => match h with conj x y => y end.
  Check fun h: X /\ Y => match h with conj x y => conj y x end.
  Check fun h: (X /\ Y) /\ Z => match h with
                             conj (conj x y) z => conj x (conj y z)
                           end.

  (** Note implicit argument overloading of or_introl and or_intror *)
  
  Check fun h: X \/ Y => match h with
                       or_introl x => or_intror Y x
                     | or_intror y => or_introl X y
                     end.
  Check fun h: (X \/ Y) \/ Z => match h with
                             or_introl (or_introl x) => or_introl (Y \/ Z) x
                           | or_introl (or_intror y) => or_intror (or_introl y)
                           | or_intror z => or_intror (or_intror z)
                           end.
  Check conj
        (fun h: X /\ Y => match h with conj x y => conj y x end)
        (fun h: Y /\ X => match h with conj y x => conj x y end).
  
  Check fun h: False => match h return X with end.  (* exfalso quodlibet *)

  Check fun x (f: ~X) => f x.
  Check fun x (f: ~X) => elim_False Y (f x).
  Check fun x (f: ~X) => match f x return Y with end.
  Check fun (f: X -> ~X) g => let x := g (fun x => f x x) in f x x.

  (** Proof construction with tactics **)

  Goal ~ ~X -> (X -> ~X) -> False.
  Proof.
    refine (fun f g => _).
    refine (f _).
    refine (fun x => _).
    exact (g x x).
    Show Proof.
  Qed.

  Goal ~ ~X -> (X -> ~X) -> False.
  Proof.
    intros f g.
    apply f.
    intros x.
    exact (g x x).
    Show Proof.
  Qed.

  Goal ~(X <-> ~X).
  Proof.
    refine (fun a => match a with conj f g => _ end).
    refine (let x:X := _ in f x x).
    refine (g (fun x => _)).
    exact (f x x).
    Show Proof.
  Qed.
  
  Fact Russell :
    ~(X <-> ~X).
  Proof.
    intros [f g].
    assert (x: X).
    - apply g. intros x. exact (f x x).
    - exact (f x x).
    Show Proof.
  Qed.

  Goal X /\ (Y \/ Z) <-> (X /\ Y) \/ (X /\ Z).
  Proof.
    refine (conj _ _).
    - refine (fun a => match a with
                    | conj x b => match b with
                                 | or_introl y => _
                                 | or_intror z => _
                                 end
                    end).
      + exact (or_introl (conj x y)). 
      + exact (or_intror (conj x z)). 
    - refine (fun a => match a with
                    | or_introl b => match b with conj x y => _ end
                    | or_intror b => match b with conj x z => _ end
                    end).
      + exact (conj x (or_introl y)).
      + exact (conj x (or_intror z)).
    Show Proof.
  Qed.
  
  Goal X /\ (Y \/ Z) <-> (X /\ Y) \/ (X /\ Z).
  Proof.
    split.
    - intros [x [y|z]].
      + left. split.
        * exact x.
        * exact y.
      + right. split.
        * exact x.
        * exact z.
    - intros [[x y]|[x z]].
      + split.
        * exact x.
        * left. exact y.
      + split.
        * exact x.
        * right. exact z.
    Show Proof.
  Qed.
  
  Goal X /\ (Y \/ Z) <-> (X /\ Y) \/ (X /\ Z).
  Proof.
    split.
    - intros [x [y|z]].
      + auto.
      + auto.
    - intros [[x y]|[x z]].
      + auto.
      + auto.
    Show Proof.
  Qed.
  
  Goal X /\ (Y \/ Z) <-> (X /\ Y) \/ (X /\ Z).
  Proof.
    tauto.
    Show Proof.  (* Uses match functions *)
  Qed.

  Goal ~ ~(X -> Y) <-> (~ ~X -> ~ ~Y).
  Proof.
    apply conj.
    - intros f g h.
      apply f. intros f'.
      apply g. intros x.
      exact (h (f' x)).
    - intros f g.
      apply g. intros x.
      exfalso.
      apply f.
      + intros h. exact (h x).
      + intros y. exact (g (fun _ => y)).
   Show Proof.
  Qed.

  Goal X <-> Y -> Y <-> Z -> X <-> Z.
  Proof.
    refine (fun a => match a with conj f g => _ end).
    refine (fun a' => match a' with conj f' g' => _ end).
    refine (conj (fun x => _) (fun z => _)).
    - exact (f' (f x)).
    - exact (g (g' z)).
    Show Proof.
  Qed.

  Goal X <-> Y -> Y <-> Z -> X <-> Z.
  Proof.
    intros [f g] [f' g'].
    split.
    - intros x. exact (f' (f x)).
    - intros z. exact (g (g' z)).
  Show Proof.
  Qed.

End Demo.

(** Assumed variables are now taken as leading arguments *)

Check Russell.

Goal forall X (p q: X -> Prop),
    (forall x, p x <-> q x) -> (forall x, q x) -> forall x, p x.
Proof.
  intros X p q f g x.
  destruct (f x) as [_ h].
  exact (h (g x)).
  Show Proof.
Qed.

Goal forall X (p q: X -> Prop),
    (forall x, p x <-> q x) -> (forall x, q x) -> forall x, p x.
Proof.
  intros X p q f g x.
  refine (match f x with conj _ h => _ end).
  exact (h (g x)).
  Show Proof.
Qed.

(** Impredicative characterizations *)

Goal False <-> forall Z: Prop, Z.
Proof.
  split.
  - intros [].
  - intros f. exact (f False).
  Show Proof.
Qed.

Goal forall X Y: Prop,
    X /\ Y <-> forall Z: Prop, (X -> Y -> Z) -> Z.
Proof.
  intros X Y.
  split.
  - intros [x y] Z f. exact (f x y).
  - intros f.  exact (f (X /\ Y) (@conj X Y)).
Qed.

Goal forall X Y: Prop,
    X \/ Y <-> forall Z: Prop, (X -> Z) -> (Y -> Z) -> Z.
Proof.
  intros X Y.
  split.
  - intros [x|y] Z f g.
    + exact (f x).
    + exact (g y).
  - intros f.
    exact (f (X \/ Y) (@or_introl X Y) (@or_intror X Y)).
  Show Proof.
Qed.
