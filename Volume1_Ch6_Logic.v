
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

(* Disjunction *)

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


Lemma mult_eq_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m. destruct n as [|n']. 
    + intros _. left. reflexivity.
    + destruct m as [|m'].
        - intros _. right. reflexivity.
        - intros contra. inversion contra.
Qed.


Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_eq_0.
  - apply eq_mult_0.
Qed.


Theorem or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

Lemma mult_0_3:
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0. rewrite or_assoc.
  reflexivity.
Qed.

Lemma apply_iff_example :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. apply mult_0. apply H.
Qed.

(* Existential Quantification *)

Definition even x := exists n : nat, x = double n.

Lemma four_is_even : even 4.
Proof.
  unfold even. exists 2. reflexivity.
Qed.

Theorem exists_example_2 : forall n,
    (exists m, n = 4 + m) ->
    (exists o, n = 2 + o).
Proof.
  intros n [m Hm].
  exists (2 + m).
  apply Hm. Qed.

Theorem dist_not_exists : forall (X:Type) (P: X -> Prop),
    (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
Admitted.

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
    (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
Admitted.



(* Programming with Propositions *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1 : In 4 [1;2;3;4;5].
Proof. simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
            exists n', n = 2 * n'.
Proof.
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.



Theorem In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.


(* Exercise *)

Theorem In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.
Admitted.


Theorem In_app_iff : forall A l l' (a:A),
    In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l. induction l as [|a' l' IH].
Admitted.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop
. Admitted.

Theorem All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
Admitted.

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop
. Admitted.

Theorem combine_odd_even_intro:
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
Admitted.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
Admitted.

Theorem combine_odd_even_elim_even:
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
Admitted.

(* Applying Theorems to Arguments *)

Check plus_comm : forall n m : nat, n + m = m + n.

Lemma plus_comm3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  rewrite plus_comm.
Abort.

Lemma plus_comm3_take2 : 
      forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  assert (H : y + z = z + y).
  { rewrite plus_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

Lemma plus_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  rewrite (plus_comm y z).
  reflexivity.
Qed.

Theorem in_not_nil:
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l H. unfold not. intro Hl.
  rewrite Hl in H.
  simpl in H.
  apply H.
Qed.

Lemma in_not_nil_42 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  Fail applhy in_not_nil.
Abort.

Lemma in_not_nil_42_take2 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.

Lemma in_not_nil_42_take3 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil in H.
  apply H.
Qed.

Lemma in_not_nil_42_take4 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

Lemma in_not_nil_42_take5:
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns ) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
    as [m [Hm _]].
  rewrite mult_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

(* Coq vs Set Theory *) 

(* functional Extensionality *)

Example function_equality_ex1 :
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof. reflexivity. Qed.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
Abort.

Axiom functional_extensionality : forall {X Y : Type}
                                         {f g : X -> Y},
    (forall (x:X), f x = g x) -> f = g.

Example function_equality_ex2' : 
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply plus_comm.
Qed.

Print Assumptions function_equality_ex2'.


(* Exercise *)

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x::l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

    
Theorem tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
Admitted.

(* Propositions vs. Booleans *)

Example even_42_bool : evenb 42 = true.
Proof. reflexivity. Qed.

Example even_42_prop : even 42.
Proof. unfold even. exists 21. reflexivity. Qed.


Lemma evenb_double: forall k, evenb (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

Lemma evenb_double_conv : forall n, exists k,
      n = if evenb n then double k else S (double k).
Proof.
Admitted.

Theorem even_bool_prop : forall n,
    evenb n = true <-> even n.
Proof.
  intros n. split.
  - intros H. destruct (evenb_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply evenb_double.
Qed.

Theorem eqb_eq : forall n1 n2 : nat,
    n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. rewrite <- eqb_refl. reflexivity.
Qed.

Fail
  Definition is_even_prime n :=
  if n = 2 then true
  else false.

Example even_1000 : even 1000.
Proof. unfold even. exists 500. reflexivity. Qed.

Example even_1000' : evenb 1000 = true.
Proof. reflexivity. Qed.

Example even_1000'' : even 1000.
Proof. apply even_bool_prop. reflexivity. Qed.


Example not_even_1001 : evenb 1001 = false.
Proof.
  reflexivity.
Qed.


Example not_even_1001' : ~(even 1001).
Proof.
  rewrite <- even_bool_prop.
  unfold not.
  simpl.
  intro H.
  discriminate H.
Qed.

Lemma plus_eqb_example : forall n m p : nat,
    n =? m = true -> n + p =? m + p = true.
Proof.
  intros n m p H.
  rewrite eqb_eq in H.
  rewrite H.
  rewrite eqb_eq.
  reflexivity.
Qed.

(* Exercise *)

Theorem andb_true_iff : forall b1 b2 : bool,
    b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
Admitted.

Theorem orb_true_iff : forall b1 b2,
    b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
Admitted.


Theorem eqb_neq : forall x y : nat,
    x =? y = false <-> x <> y.
Proof.
Admitted.

Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool)
         (l1 l2 : list A) : bool
. Admitted.


Theorem eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
Admitted.

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l' => andb (test x) (forallb test l')
  end.


Theorem forallb_true_iff : forall X test (l : list X),
    forallb test l = true <-> All (fun x => test x = true) l.
Proof.
Admitted.


(* Classical vs Contructive Logic *)

Definition excluded_middle := forall P : Prop,
    P \/ ~ P.

Theorem restricted_excluded_middle : forall P b,
    (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. discriminate contra.
Qed.

Theorem restricted_excluded_middle_eq : forall (n m : nat),
    n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (n =? m)).
  symmetry.
  apply eqb_eq.
Qed.

(* Exercise *)

Theorem excluded_middle_irrefutable: forall (P:Prop),
    ~ ~ (P \/ ~ P).
Proof.
  unfold not. intros P H.
Admitted.


Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
Admitted.

Definition peirce := forall P Q: Prop,
    ((P->Q)->P)->P.

Definition double_negation_elemination := forall P:Prop,
    ~~P -> P.

Definition de_morgan_not_and_not := forall P Q:Prop,
    ~(~P \/ ~Q) -> P\/Q.

Definition implies_to_or := forall P Q:Prop,
    (P->Q) -> (~P\/Q).




           



