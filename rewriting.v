Theorem plus_id_example: forall n m: nat,
  n = m ->
  n + n = m + m.

Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity. Qed.
  

Theorem plus_id_exercise : forall n m o : nat,
    n = m -> m = o -> n + m = m + o.
  
Proof.
  intros n m o.
  intros H G.
  rewrite -> H.
  rewrite -> G.
  reflexivity. Qed.
  

Check mult_n_O.
Check mult_n_Sm.

Theorem mult_n_0_m_0 : forall p q : nat,
    (p * 0) + (q * 0) = 0.

Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity. Qed.


Check mult_n_Sm.

Theorem mult_n_1 : forall p : nat,
    p * 1 = p.
Proof.
  intros p.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  rewrite <- plus_O_n.
  reflexivity. Qed.



