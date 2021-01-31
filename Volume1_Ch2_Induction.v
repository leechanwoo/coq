
(* Proof by Induction *)

From LF Require Export Volume1_Ch1_Basics.

Theorem plus_n_O_firsttry : forall n:nat,
    n = n + 0.
Proof.
  intros n.
  simpl.
Abort.


Theorem plus_n_O_secondtry : forall n:nat,
    n = n + 0.
Proof.
  intros n. destruct n as [|n'] eqn:E.
  - reflexivity. 
  - simpl.
Abort.


Theorem plus_n_O : forall n:nat,
    n = n + 0.
Proof.
  intros n. induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity. Qed.


Theorem minus_n_n : forall n,
    minus n n = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.


(* Exercise *)
Theorem mult_0_r : forall n:nat,
    n * 0 = 0.
Proof.
  intros n. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.


Theorem plus_n_Sm : forall n m : nat,
    S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n.
  induction m.
  simpl. reflexivity.
  simpl. reflexivity.
  simpl. rewrite <- IHn.
  reflexivity.
Qed.



Theorem plus_comm : forall n m : nat,
    n + m = m + n.
Proof.
  intros.
  induction n.
  induction m.
  reflexivity.
  simpl.
  rewrite <- IHm.
  simpl.
  reflexivity.
  simpl.
  rewrite <- plus_n_Sm.
  rewrite <- IHn.
  reflexivity.
Qed.

 
Theorem plus_assoc : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof.
  intros.
  induction n.
  induction m.
  induction p.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  simpl.
  rewrite -> IHn.
  reflexivity.
Qed.


Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n,
    double n = n + n.
Proof.
  induction n as [| n'].
  reflexivity.
  simpl.
  rewrite -> IHn'.
  rewrite -> plus_n_Sm.
  reflexivity.
Qed.

Fixpoint evenb (n:nat) : bool := 
match n with
| O => true
| S O => false
| S (S n') => evenb n'
end.

Lemma neg_id : forall n,
    n = negb (negb n).
Proof.
  intros.
  induction n.
  reflexivity.
  reflexivity.
Qed.

Theorem evenb_S : forall n:nat,
    evenb (S n) = negb (evenb n).
Proof.
  intros.
  induction n.
  reflexivity.
  rewrite -> IHn.
  rewrite <- neg_id.
  reflexivity.
Qed.

(* Proofs Within Proofs *)

Theorem mult_0_plus' : forall n m : nat,
    (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n).
  { reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm.
    reflexivity. }
  rewrite <- H.
  reflexivity.
Qed.


(* Formal vs. Informal Proof *)

Theorem plus_assoc' : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof. intros. induction n as [| n' IHn']. reflexivity.
       simpl. rewrite -> IHn'. reflexivity. Qed.


Theorem plus_assoc'' : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof.
  intros.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.


(* More Exercises *)


Theorem plus_swap : forall n m p : nat,
    n + (m + p) = m + (n + p).
Proof.
  intros.
  rewrite plus_assoc.
  assert (H: m + n = n + m).
  { rewrite plus_comm.
    reflexivity. }
  rewrite <- H.
  rewrite plus_assoc.   
  reflexivity.
Qed.


Theorem mult_comm : forall m n : nat,
    m * n = n * m.
Proof.
Admitted.


Check leb.

Theorem leb_refl : forall n:nat,
    true = (n <=? n).
Proof.
Admitted.

Theorem zero_nbeq_S : forall n:nat,
    0 =? (S n) = false.
Proof.
Admitted.


Theorem andb_false_r : forall b:bool,
    andb b false = false.
Proof.
Admitted.

Theorem plus_ble_compat_l : forall n m p : nat,
    n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
Admitted.

Theorem S_nbeq_o : forall n:nat,
    (S n) =? 0 = false.
Proof.
Admitted.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
Admitted.

Theorem mult_plus_distr_r : forall n m p : nat,
    (n + m) * p = (n * p) + (m * p).
Proof.
Admitted.

Theorem mult_assoc : forall n m p : nat,
    n * (m * p) = (n * m ) * p.
Proof.
Admitted.


Theorem eqb_refl : forall n:nat,
    true = (n =? n).
Proof.
Admitted.

Theorem plus_swap' : forall n m p : nat,
    n + (m + p) = m + (n + p).
Proof.
Admitted.


Fixpoint nat_to_bin (n:nat) : bin
. Admitted.


Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
Admitted.

