Set Implicit Arguments.
Require Import Setoid.
Require Import Omega.
Require Import List.
Import ListNotations.
Require Import Arith.
Import Coq.Bool.Bool.
Require Import Bool.
Require Import Classical.

(* 1 *)
(* a *)
Goal forall X Y : Prop, (~(X /\ Y) \/ (~X /\ Y) \/ (~X /\ ~Y)) <-> ~(X /\ Y).
Proof. Abort.

(* preko dvostruke negacije *)
Goal forall X Y : Prop, ~~((~(X /\ Y) \/ (~X /\ Y) \/ (~X /\ ~Y)) <-> (~X \/ ~Y)).
Proof.
  intros X Y nH. apply nH. split.
  - intros [H1 | [H2 | H3]].
   -- left. intros x. apply nH. split.
    --- intros G. right. intros y. apply H1. split ; assumption.
    --- intros G. left. apply H1.
   -- destruct H2. left. apply H.
   -- destruct H3. left. apply H.
  - intros H. left. intros G. destruct H ; destruct G as [x y].
   -- apply H. exact x.
   -- apply H. exact y.
Qed.

(* 1 *)
(* b *)
Goal forall X Y Z : Prop, (~(~X /\ Y /\ ~Z) /\ ~(X /\ Y /\ Z) /\ (X /\ ~Y /\ ~Z) <-> X /\ ~Y /\ ~Z).
Proof. Abort.

(* preko dvostruke negacije *)
Goal forall X Y Z : Prop, ~~(~(~X /\ Y /\ ~Z) /\ ~(X /\ Y /\ Z) /\ (X /\ ~Y /\ ~Z) <-> X /\ ~Y /\ ~Z).
Proof.
  intros X Y Z. intros nH. apply nH. split.
  - intros [F [G H]]. apply H.
  - intros H. split.
    -- destruct H as [x [ny nz]]. intros A. destruct A as [nx [y _]]. contradiction.
    -- destruct H as [x [ny nz]]. split.
     * intros A. destruct A as [_ [y z]]. contradiction.
     * split. 
       ** exact x.
       ** split ; assumption.
Qed.


