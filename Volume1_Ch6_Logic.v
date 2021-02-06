
Set Warnings "-notation-overriden,-parsing".
From LF Require Export Volume1_Ch5_Tactics.

(* Logic in Coq *) 

Check 3 = 3 : Prop.

Check forall n m : nat, n + m = m + n : Prop.


Check 2 = 2 : Prop.

Check 3 = 2 : Prop.

Check forall n : nat, n = 2 : Prop.


Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity. Qed.

Definition plus_claim : Prop := 2 + 2 = 4.
Check plus_claim : Prop.

Theorem plus_claim_is_true :
  plus_claim.
Proof. reflexivity. Qed.

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three : nat -> Prop.


Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.


Lemma succ_inj : injective S.
Proof.
  intros n m H. injection H as H1.
  apply H1.
Qed.

Check @eq : forall A : Type, A -> A -> Prop.


(* Logical Connectives *) 

(* Conjunction *)

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 * 2 = 4 *) reflexivity.
Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.


(* Exercise *)

Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
Admitted.


Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn.
  rewrite Hm.
  reflexivity.
Qed.


Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn.
  rewrite Hm.
  reflexivity.
Qed.


Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.


Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  apply and_exercise in H.
  destruct H as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.


Lemma proj1 : forall P Q : Prop,
    P /\ Q -> P.
Proof.
  intros P Q HPQ.
  destruct HPQ as [HP _].
  apply HP. Qed.


(* Exercise *)

Lemma proj2 : forall P Q : Prop,
    P /\ Q -> Q.
Proof.
Admitted.


Theorem and_commut : forall P Q : Prop,
    P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
  - (* left *) apply HQ.
  - (* right *) apply HP. Qed.

(* Exercise *)

Theorem and_assoc : forall P Q R : Prop,
    P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
Admitted.

Check and : Prop -> Prop -> Prop.

(* Disjuction *)

Lemma eq_mult_0 :
  forall n m : nat, n = 0 \/ m = 0 -> n *  m = 0.
Proof.
  intros n m [Hn | Hm].
  - (* n = 0 *)
    rewrite Hn. reflexivity.
  - (* m = 0 *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.


Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [|n'].
  - left. reflexivity.
  - right. reflexivity.
Qed.


(* Falsehood and Negation *)
Module MyNot.
  Definition not (P:Prop) := P -> False.

  Notation "~ x" := (not x) : type_scope.

  Check not : Prop -> Prop.

End MyNot.

Theorem ex_falso_quodlibet : forall (P:Prop),
    False -> P.
Proof.
  intros P contra.
  destruct contra.
Qed.

(* Exercise *)
Fact not_implies_our_not : forall (P:Prop),
    ~P -> (forall (Q:Prop), P -> Q).
Proof.
Admitted.

Notation "x <> y" := (~(x = y)).


Theorem zero_not_one : 0 <> 1.
Proof.
  unfold not.
  intros contra.
  discriminate contra.
Qed.

Theorem not_False :
  ~False.
Proof.
  unfold not.
  intros H.
  destruct H.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
    (P /\ ~P) -> Q.
Proof.
  intros P Q [HP HNA].
  unfold not in HNA.
  apply HNA in HP.
  destruct HP.
Qed.


Theorem double_neg : forall P : Prop,
    P -> ~~P.
Proof.
  intros P H.
  unfold not.
  intros G.
  apply G.
  apply H.
Qed.


(* Exercise *)

  
Theorem contrapositive : forall (P Q : Prop),
    (P -> Q) -> (~Q -> ~P).
Proof.
Admitted.

Theorem not_both_true_and_false : forall P : Prop,
    ~(P /\ ~P).
Proof.
Admitted.

Theorem not_true_is_false : forall b : bool,
    b <> true -> b = false.
Proof.
  intros b H.
  destruct b eqn:HE.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H.
    reflexivity.
  - (* b = fasle *)
    reflexivity.
Qed.


Theorem not_tru_is_false' : forall b : bool,
    b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    exfalso.
    apply H. reflexivity.
  - (* b = false *) reflexivity.
Qed.


(* Truth *)

Lemma True_is_true : True.
Proof. apply I. Qed.
       
(* Logical Equivalence *)

Module MyIff.
  Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

  Notation "P <-> Q" := (iff P Q)
                          (at level 95, no associativity)
                        : type_scope.
End MyIff.


Theorem iff_sym : forall P Q : Prop,
    (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HAB HBA].
  split.
  - (* -> *) apply HBA.
  - (* <- *) apply HAB. Qed.


Lemma not_true_iff_false : forall b,
    b <> true <-> b = false.
Proof.
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *) intros H.
    rewrite H. intros H'. discriminate H'.
Qed.


(* Exercise *)

Theorem or_distributes_over_and : forall P Q R : Prop,
    P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
Admitted.

(* Setoids and Logical Equivalence *)

From Coq Require Import Setoids.Setoid.


Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_eq_0.

    




    
  
  
