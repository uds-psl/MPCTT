Section Demo.
  Variables X Y Z: Prop.

  Goal X -> Y -> X.
  Proof.
    intros x y. exact x.
    Show Proof.
  Qed.

  Goal X -> Y -> X.
  Proof.
    refine (fun x y => _).
    Show Proof.
    exact x.
  Qed.

  Goal (X -> Y -> Z) -> X /\ Y -> Z.
  Proof.
    intros f [x y]. exact (f x y).
    Show Proof.
  Qed.

  Goal (X -> Y -> Z) <-> (X /\ Y -> Z).
  Proof.
    split.
    Show Proof.
    - intros f [x y]. exact (f x y).
    - intros f x y. apply f. split.
      + exact x.
      + exact y.
    Show Proof.
  Qed.

  Goal X -> ~X -> False.
  Proof.
    exact (fun x f => f x).
    Show Proof.
  Qed.
  
  Goal X -> ~X -> Y.
  Proof.
    refine (fun x f => _).
    refine (False_ind _ _).
    exact (f x).
    Show Proof.
  Qed.
  
  Goal X -> ~X -> Y.
  Proof.
    intros x f.
    exfalso.
    exact (f x).
    Show Proof.
  Qed.
  
  Goal (X -> ~X) -> (~X -> X) -> False.
  Proof.
    refine (fun f g => _).
    refine (let x:X := _ in f x x).
    refine (g (fun x => _)).
    exact (f x x).
    Show Proof.
  Qed.

  Goal (X -> ~X) -> (~X -> X) -> False.
  Proof.
    intros f g.
    assert (x: X).
    - apply g. intros x. exact (f x x).
    - exact (f x x).
      Show Proof.
  Qed.
  
  Goal (X -> ~X) -> (~X -> X) -> False.
  Proof.
    refine (fun f g => _).
    refine (let x:X := _ in _).
    exact (f x x).
    Unshelve.
    refine (g (fun x => _)).
    exact (f x x).
    Show Proof.
  Qed.

End Demo.
