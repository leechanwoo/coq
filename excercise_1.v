
Theorem identify_fn_applied_twice :
  forall (f : bool -> bool),
    (forall (x:bool), f x = x) ->
    forall (b:bool), f (f b) = b.
Proof.
  intros f H b.
  rewrite <- H.
  destruct b.
  rewrite -> H.
  reflexivity.
  rewrite -> H.
  reflexivity.
Qed.


Theorem negation_fn_appliced_twice :
  forall (f : bool -> bool),
    (forall (x:bool), f x = negb x) ->
    forall (b:bool), f (f b) = b.
Proof.
  intros f H b.
  rewrite -> H.
  rewrite -> H.
  destruct b.
  reflexivity.
  reflexivity.
Qed.




Theorem andb_eq_orb :
  forall (b c : bool),
    (andb b c = orb b c) ->
    b = c.
Proof.
  intros b c.
  destruct b.
  destruct c.
  intro H.
  reflexivity.
  simpl.
  intro H.
  rewrite H.
  reflexivity.
  simpl.
  intro H.
  rewrite H.
  reflexivity.
Qed.



Inductive bin : Type :=
| Z
| B0 (n : bin)
| B1 (n : bin).

  
                          
            






  
  
