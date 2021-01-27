
(* Lists: Working with structured data *)

(* Pairs of Numbers *)

Inductive natprod : Type :=
| pair (n1 n2 : nat).

Check (pair 3 5) : natprod.

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Compute (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).

Compute (fst (3, 5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.


Fixpoint minus (n m : nat) : nat :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n', S m' => minus n' m'
  end.

(*
Definition bad_fst (p : natprod) : nat :=
  match p with
  | x, y => x
  end.
*)

(*
Definition bad_minus (n m : nat) : nat :=
  match n, m with
  | (O , _ ) => O
  | (S _ , O ) => n
  | (S n', S m') => bad_minus n' m'
  end.
*)


Theorem surjective_pairing' : forall (n m : nat),
    (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity. Qed.

Theorem surjective_pairing_stuck : forall (p : natprod),
    p = (fst p, snd p).
Proof.
  simpl.
Abort.

Theorem surjective_pairing : forall (p : natprod),
    p = (fst p, snd p).
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.


Theorem snd_fst_is_swap : forall (p : natprod),
    (snd p, fst p) = swap_pair p.
Proof.
  intros.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
    fst (swap_pair p) = snd p.
Proof.
  intros.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

Inductive natlist : Type :=
| nil
| cons (n : nat) (l : natlist).


Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l)
                       (at level 60, right associativity).

Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].


Notation "x + y" := (plus x y)
                      (at level 50, left associativity).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.


Notation "x ++ y" := (app x y)
                       (right associativity, at level 60).
Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.

Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.

Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.


Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1 : hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.

Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.

Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | O :: t => nonzeros t
  | h :: t => h :: (nonzeros t)
  end.


Example test_nonzzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

Fixpoint evenb (n:nat) : bool := 
match n with
| O => true
| S O => false
| S (S n') => evenb n'
end.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => match evenb h with
              | true => oddmembers t
              | false => h :: (oddmembers t)
              end
  end.
  

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.


Definition countoddmembers (l:natlist) : nat :=
  length (oddmembers l).
  

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. reflexivity. Qed.


Fixpoint alternate (l1 l2 : natlist) : natlist.
Admitted.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.


