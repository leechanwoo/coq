
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

Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B1 Z 
  | B0 m' => B1 m'
  | B1 m' => B0 (incr m')
  end.
  
                  

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => O
  | B1 Z => S O
  | B1 m' => S O + bin_to_nat m' + bin_to_nat m'
  | B0 m' => bin_to_nat m' + bin_to_nat m'
  end.

Example bin_to_nat1 : bin_to_nat(B0 (B0 (B1 Z))) = S (S (S (S O))).
Proof. simpl. reflexivity. Qed.

Example bin_to_nat2 : bin_to_nat(B1 (B1 (B1 Z))) = 7.
Proof. simpl. reflexivity. Qed.
                       
Example bin_to_nat3 : bin_to_nat(B0 (B0 (B0 (B1 Z)))) = 8.
Proof. simpl. reflexivity. Qed.

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof. simpl. reflexivity. Qed.


Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof. simpl. reflexivity. Qed.


Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
Proof. simpl. reflexivity. Qed.


Example test_bin_incr5 :
  bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
Proof. simpl. reflexivity. Qed.


Example test_bin_incr6:
  bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
Proof. simpl. reflexivity. Qed.


