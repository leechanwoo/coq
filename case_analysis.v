

Fixpoint eqb (n m : nat ) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.


Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.



Theorem plus_1_neq_0_firsttry : forall n : nat,
    (n+1) =? 0 = false.
  
Proof.
  intros n.
  simpl.
 Abort.

Theorem plus_1_neq_0 : forall n : nat,
    (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.
    
Theorem negb_involutive : forall b : bool,
    negb (negb b) = b.

Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity. Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
Qed.


Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
Qed.


Theorem andb_true_elim2 : forall b c : bool,
    andb b c = true -> c = true.
Proof.
  intros x y.
  intro H.
  destruct x.
  destruct y.
  reflexivity.
  rewrite <- H.
  reflexivity.
  destruct y.
  reflexivity.
  rewrite <- H.
  reflexivity.
Qed.


Theorem andb_true_elim3 : forall b c: bool,
    andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct c.
  reflexivity.
  rewrite <- H.
  { destruct b eqn:Eb.
    reflexivity.
    reflexivity. } 
Qed.

