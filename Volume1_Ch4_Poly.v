
From LF Require Export Volume1_Ch3_Lists.

(* Polymorphism *)

Inductive boollist : Type :=
| bool_nil
| bool_cons (b : bool) (l : boollist).

Inductive list (X:Type) : Type :=
| nil
| cons (x : X) (l : list X).


Check list : Type -> Type.

Check (nil nat) : list nat.

Check (cons nat 3 (nil nat)) : list nat.

Check nil : forall X : Type, list X.


Check cons : forall X : Type, X -> list X -> list X.

Check (cons nat 2 (cons nat 1 (nil nat)))
  : list nat.


Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | O => nil X
  | S count' => cons X x (repeat X x count')
  end.


Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).


(* Type Annotation Inference *)

Fixpoint repeat' X x count : list X :=
  match count with
  | O => nil X
  | S count' => cons X x (repeat' X x count')
  end.


Check repeat' : forall X : Type, X -> nat -> list X.
Check repeat : forall X : Type, X -> nat -> list X.


(* Type Argument Synthesis *)

Fixpoint repeat'' X x count : list X :=
  match count with
  | O => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

Definition list123 :=
  cons nat 1 (cons nat 2 ( cons nat 3 (nil nat))).

Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _ ))).

(* Implicit Arguments *)

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.




 




