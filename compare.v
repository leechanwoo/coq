Fixpoint eqb (n m: nat) : bool := 
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

Fixpoint leb (n m: nat) : bool := 
  match n with
    | O => true
    | S n' => 
          match m with
            | O => false
            | S m'  => leb n' m'
            end
end.

Example test_leb1: leb 2 2 = true.
Proof. simpl. reflexivity. Qed.

Example test_leb2: leb 2 4 = true.
Proof. simpl. reflexivity. Qed.

Example test_leb3: leb 4 2 = false.
Proof. simpl. reflexivity. Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.

Definition ltb (n m: nat) : bool :=
  match n, m with 
    | O, O => false
    | O, S m' => true
    | S n', O => false
    | S n', S m' => match eqb n' m' with
      | false => leb n' m'
      | true => false
      end
  end.


Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.

Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.

Example test_lib3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.





