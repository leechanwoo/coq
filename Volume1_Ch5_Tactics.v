
From LF Require Export Volume1_Ch4_Poly.

(* The apply tactic *)

Theorem silly1 : forall (n m o p : nat),
    n = m ->
    [n;o] = [n;p] ->
    [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  apply eq2.
Qed.

Theorem silly2 : forall (n m o p : nat),
    n = m ->
    (n = m -> [n;o] = [m;p]) ->
    [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2.
  apply eq1.
Qed.


Theorem silly2a : forall (n m : nat),
    (n,n) = (m,m) ->
    (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
    [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2.
  apply eq1.
Qed.

Theorem silly_ex :
  (forall n, evenb n = true -> oddb (S n) = true) ->
  evenb 2 = true -> oddb 3 = true.
Proof.
  intros H H'.
  apply H.
  apply H'.
Qed.

Theorem silly3_firsttry : forall (n : nat),
    true = (n =? 5) ->
    (S (S n)) =? 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl.
  apply H.
Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
    l = rev l' -> l' = rev l.
Proof.
  intros.
  rewrite -> H.
  symmetry.
  apply rev_involutive.
Abort.


(* The apply with Tactic *)

Example trans_eq_example : forall (a b c d e f : nat),
    [a;b] = [c;d] ->
    [c;d] = [e;f] ->
    [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1.
  rewrite -> eq2.
  reflexivity.
Qed.


Theorem trans_eq : forall (X:Type) (n m o: X),
    n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2.
  rewrite -> eq1. rewrite -> eq2.
  reflexivity. Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
    [a;b] = [c;d] ->
    [c;d] = [e;f] ->
    [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c;d]).
  apply eq1.
  apply eq2.
Qed.


Example trans_eq_example'' : forall (a b c d e f : nat),
    [a;b] = [c;d] ->
    [c;d] = [e;f] ->
    [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  transitivity [c;d].
  apply eq1. apply eq2. Qed.

Example trans_eq_exercise : forall (n m o p : nat),
    m = (minustwo o) ->
    (n + p) = m ->
    (n + p) = (minustwo o).
Proof.
  intros n m p o eq1 eq2.
  transitivity m.
  apply eq2. apply eq1. Qed.

(* The injection and discriminate Tactics *)

(*  duplicated constructor with Datatypes.nat
Inductive nat : Type :=
| O
| S (n : nat).
 *)


Theorem S_injective : forall (n m : nat),
    S n = S m ->
    n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)).
  { reflexivity. }
  rewrite H2. rewrite H1. reflexivity.
Qed.


Theorem S_injetive' : forall (n m : nat),
    S n = S m ->
    n = m.
Proof.
  intros m n H.
  injection H as Hnm. apply Hnm.
Qed.


Theorem injection_ex1 : forall (n m o : nat),
    [n;m] = [o;o] ->
    [n] = [m].
Proof.
  intros n m o H.
  injection H as H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.

Theorem injection_ex2 : forall (n m o : nat),
    [n;m] = [o;o] ->
    [n] = [m].
Proof.
  intros n m o H.
  injection H.
  intros H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.


Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = z :: j ->
    j = z :: l ->
    x = y.
Proof.
  intros X x y z l j H H'.
  injection H as H1 H2.
  rewrite H1.
  assert (Ha: y :: l = z :: l).
  - rewrite -> H2.
    rewrite <- H'.
    reflexivity.
  - symmetry.
    injection Ha as Ha'.
    rewrite -> Ha'.
    reflexivity.
Qed.


Theorem eqb_0_1 : forall n,
    0 =? n = true -> n = 0.
Proof.
  intros n.
  destruct n as [|n'] eqn:E.
  - (* n = 0 *)
    intros H. reflexivity.
  - (* n = S n' *)
    simpl.
    intros H. discriminate H.
Qed.

Theorem discriminate_ex1 : forall (n : nat),
    S n = O ->
    2 + 2 = 5.
Proof.
  intros n contra.
  discriminate contra.
Qed.

Theorem discriminate_ex2 : forall (n m : nat),
    false = true ->
    [n] = [m].
Proof.
  intros n m contra.
  discriminate contra.
Qed.


Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
  intros X x y z l j H.
  discriminate H.
Qed.


Theorem f_equal: forall (A B : Type) (f: A -> B) (x y : A),
    x = y -> f x = f y.
Proof.
  intros A B f x y eq.
  rewrite eq.
  reflexivity.
Qed.

Theorem eq_implies_succ_equal : forall (n m : nat),
    n = m -> S n = S m.
Proof.
  intros n m H.
  apply f_equal.
  apply H.
Qed.

Theorem eq_implies_succ_equal' : forall (n m : nat),
    n = m -> S n = S m.
Proof.
  intros n m H.
  f_equal.
  apply H.
Qed.


(* Using Tactics on Hypotheses *)

Theorem S_inj : forall (n m : nat) (b : bool),
    (S n) =? (S m) = b ->
    n =? m = b.
Proof.
  intros n m b H.
  simpl in H.
  apply H.
Qed.


(* Varying the induction hypothesis *)

Theorem double_injective: forall n m ,
    double n = double m -> n = m.
Proof.
  intros n m.
  induction n.
Abort.

Theorem double_injective_FAILED : forall n m,
    double n = double m ->
    n = m.
Proof.
  intros n m. induction n as [| n' IHn'].
  - (* n = O *) simpl. intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) discriminate eq.
    + (* m = S m' *) apply f_equal.
Abort.


Theorem double_injective : forall n m,
    double n = double m ->
    n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = O *) simpl. intros m eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) simpl.
    intros m eq.
    destruct m as [| m'] eqn:E.
    + (* m = O *) discriminate eq.
    + (* m = S m' *)
      apply f_equal.
      apply IHn'. simpl in eq. injection eq as goal. apply goal. Qed.

(* Exercise *)

Theorem eqb_true : forall n m,
    n =? m = true -> n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = O *) intros m eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + discriminate eq. 
  - (* n = S n' *) intros m eq.
    destruct m as [| m'] eqn:E.
    + (* m = O *) discriminate eq.
    + (* m = S m' *)
      apply f_equal.
      apply IHn'.
      simpl in eq.
      apply eq.
Qed.
  

Theorem plus_n_n_injective : forall n m,
    n + n = m + m ->
    n = m.
Proof.
  intros n. induction n as [|n' IHn'].
  - (* n = O *)
    intros m H.
    destruct m as [| m'].
    + (* m = O *)
      reflexivity.
    + (* m = S m' *)
      discriminate H.
  - (* n = S n' *)
    intros m H.
    destruct m as [| m'].
    + (* m = O *)
      discriminate H.
    + (* m = S m' *)
      rewrite <- plus_n_Sm in H.
      rewrite <- plus_n_Sm in H.
      simpl in H.
      apply f_equal.
      apply IHn'.
      injection H as H'.
      apply H'.
Qed.

Theorem double_injective_take2_FAILED : forall n m,
    double n = double m ->
    n = m.
Proof.
  intros n m. induction m as [| m' IHm'].
  - (* m = O *) simpl. intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
Abort.


Theorem double_injective_take2 : forall n m,
    double n = double m ->
    n = m.
Proof.
  intros n m.
  (* n and m are both in the context *)
  generalize dependent n.
  (* Now n is back in the goal and we can do induction on 
    m and get a sufficiently general IH. *)
  induction m as [| m' IHm'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
      apply IHm'. injection eq as goal. apply goal. Qed.

Theorem nth_error_after_last : forall (n : nat) (X : Type) (l : list X),
    length l = n ->
    nth_error l n = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l as [|e l' IHl'].
  - (* l = nil *) reflexivity.
  - (* l = e::l' *) intros n eq.
    destruct n as [|n IHn'].
    + (* n = O *) discriminate eq.
    + (* n = S n' *) simpl.
      apply IHl'.
      injection eq as goal.
      apply goal.
Qed.


(* Unfolding Definitions *)

Definition square n := n * n.

Lemma square_mult : forall n m,
    square (n * m) = square n * square m.
Proof.
  intros n m.
  simpl.
  unfold square.
  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
  { rewrite mult_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.

Definition foo (x: nat) := 5.

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.


Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.


Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl.
Abort.

Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.


Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.
  destruct m eqn:E.
  - reflexivity.
  - reflexivity.
Qed.



(* Using destruct on Compound Expressions *)

Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
       else false.

Theorem sillyfun_false : forall (n : nat),
    sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3) eqn:E1.
  - (* n =? 3 = true *) reflexivity.
  - (* n =? 3 = false *) destruct (n =? 5) eqn:E2.
    + (* n =? 5 = true *) reflexivity.
    + (* n =? 5 = false *) reflexivity. Qed.

(* Exercise *)

Fixpoint split {X Y : Type} (l : list (X*Y))
  : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
    match split t with
    | (lx, ly) => (x :: lx, y :: ly)
    end
  end.


(* Review *)

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
    split l = (l1, l2) ->
    combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l as [| h t].
  - (* l = [] *) intros l1 l2 H. inversion H. reflexivity.
  - (* l = h::t *) destruct h as [x y]. intros l1 l2 H. inversion H.
    destruct (split t). 
    inversion H1. 
    simpl.
    rewrite IHt.
    reflexivity.
    reflexivity.
Qed.

    

Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
       else false.

Theorem sillyfun1_odd_FAILED : forall (n : nat),
    sillyfun1 n = true ->
    oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3).
Abort.

Theorem sillyfun1_odd : forall (n : nat),
    sillyfun1 n = true ->
    oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3) eqn:Heqe3.
  (* Now we have the same state as at the point where we got
     stuck above, except that the context contains an extra equality 
     assumption, which is exactly what we need to make progress. *)
  - (* e3 = true *) apply eqb_true in Heqe3.
    rewrite -> Heqe3. reflexivity.
  - (* e3 = false *)
    (* When we come to the second equality test in the body of the 
       function we are reasoning about, we can use 
       eqn: again in the same way, allowing us to finish the 
       proof. *)
    destruct (n =? 5) eqn:Heqe5.
    + (* e5 = true *)
      apply eqb_true in Heqe5.
      rewrite -> Heqe5. reflexivity.
    + (* e5 = false *) discriminate eq. Qed.


(* Review *)
Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
    f (f (f b)) = f b.
Proof.
  intros f b.
  destruct (f true) eqn:Hftrue.
  destruct (f false) eqn:Hffalse.
  destruct b.
  rewrite Hftrue.
  rewrite Hftrue.
  apply Hftrue.
  rewrite Hffalse.
  rewrite Hftrue.
  apply Hftrue.
  destruct b.
  rewrite Hftrue.
  rewrite Hftrue.
  apply Hftrue.
  rewrite Hffalse.
  rewrite Hffalse.
  apply Hffalse.
  destruct (f false) eqn:Hffalse.
  destruct b.
  rewrite Hftrue.
  rewrite Hffalse.
  apply Hftrue.
  rewrite Hffalse.
  rewrite Hftrue.
  apply Hffalse.
  destruct b.
  rewrite Hftrue.
  rewrite Hffalse.
  apply Hffalse.
  rewrite Hffalse.
  rewrite Hffalse.
  apply Hffalse.
Qed.

  
(* Review *)

(* intros: move hypotheses/variables from goal to context 
 * reflexivity: finish the proof (when the goal looks like e=e)
 * apply: prove goal using a hypothesis, lemma, or constructor 
 * apply...in H: explicitly specify values for variables that cannot be determined 
   by pattern matching 
 * simpl: simplify computations in the goal
 * simpl in H: ... or a hypothesis
 * rewrite: use an equality hypothesis (or lemma) to rewrite the goal
 * rewrite ... in H: ... or a hypothesis 
 * symmetry: changes a goal of the form t=u into u=t
 * symmetry in H: changes a hypothesis of the form t=u into u=t
 * transitivity y: prove a goal x=z by proving two new subgoals, x=y and y=z
 * unfold: replace a defined constant by its right-hand side in the goal
 * unfold...in H: ... or a hypothesis
 * destruct...as...: case analysis on values of inductively defined types
 * destruct...eqn:...: specify the name of an equation to be added to the context, 
   recording the result of the case analysis 
 * induction...as...: induction on values of inductively defined types
 * injection: reason by injectivity on equalities between values of inductively defined types
 * descriminate: reason by disjointness of constructors on equalities between values 
   of inductively defined types 
 * assert (H:e) (or assert (e) as H): introduce a "local lemma" e and call it H
 * generalize dependent x: move the variable x(and anything else that depends on it) 
   from the context back to an explicit hypothesis in the goal formula
 * f_equal: change a goal of the form f x = f y into x = y 
 *)

(* Additional Exercises *)

Theorem eqb_sym : forall (n m : nat),
    (n =? m) = (m =? n).
Proof.
  intros n.
  induction n as [|n' IHn'].
  - (* n = O *) induction m as [|m' IHm'].
    + (* m = O *) reflexivity.
    + (* m = S m' *) simpl. reflexivity.
  - (* n = O *) intros m. induction m as [|m' IHm'].
    + (* m = O *) simpl. reflexivity.
    + (* m = S m' *) simpl.
      apply IHn'.
Qed.


Theorem eqb_trans : forall n m p,
    n =? m = true ->
    m =? p = true ->
    n =? p = true.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - (* n = O *) induction m as [|m' IHm'].
    + (* m = O *) simpl. intros p Hp Hp'. apply Hp'.
    + (* m = S m' *) intros p Hp Hp'. discriminate Hp.
  - (* n = S n' *) induction m as [|m' IHm'].
    + (* m = O *) intros p Hp Hp'. discriminate Hp.
    + (* m = S m' *) intros p H1 H2.
      induction p as [|p' IHp].
      { (* p = O *) discriminate H2. }
      { (* p = S p' *)
        simpl.
        simpl in H1.
        simpl in H2.
        simpl in IHn'.
        apply IHn' in H2.
        apply H2.
        apply H1.
      }
Qed.
    


(* Review *)
Definition split_combine_statement : Prop := forall {X Y: Type}
           (l1: list X) (l2: list Y),

  length l1 = length l2 -> split (combine l1 l2) = (l1, l2).


Theorem split_combine : split_combine_statement.
Proof.
Admitted.
    

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                                 (x : X) (l lf : list X),
    filter test l = x :: lf ->
    test x = true.
Proof.
Admitted.


Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool
. Admitted.

Example test_forallb_1 : forallb oddb [1;3;5;7;9] = true.
Proof. Admitted.


Example test_forallb_2 : forallb negb [false;false] = true.
Proof. Admitted.

  
Example test_forallb_3 : forallb evenb [0;2;4;5] = false.
Proof. Admitted.


Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof. Admitted.

Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) : bool
. Admitted.

Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof. Admitted.

Example test_existsb_2 : existsb (andb true) [true;true;false] = false.
Proof. Admitted.

Example test_existsb_3 : existsb oddb [1;0;0;0;0;3] = false.
Proof. Admitted.

Example test_existsb_4 : existsb evenb [] = false.
Proof. Admitted.


Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool
. Admitted.

Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
    existsb test l = existsb' test l.
Proof.
Admitted.
