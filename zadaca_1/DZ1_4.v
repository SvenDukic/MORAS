Set Implicit Arguments.
Require Import List.
Import ListNotations.
Require Import Omega.

(* Bit *)

Inductive B : Type :=
  | O : B
  | I : B.

Definition And (x y : B) : B :=
match x with
  | O => O
  | I => y
end.

Definition Or (x y : B) : B :=
match x with
  | O => y
  | I => I
end.

Definition Not (x : B) : B :=
match x with
  | O => I
  | I => O
end.

Definition Add (x y c : B) : B :=
match x, y with
  | O, O => c
  | I, I => c
  | _, _ => Not c
end.

Definition Rem (x y c : B) : B := (* carry prilikom sumacije *)
match x, y with
  | O, O => O
  | I, I => I
  | _, _ => c
end.

(* ovo bi odgovaralo FULL-ADDER *)

(* List *)

Fixpoint AndL (x y : list B) : list B :=
match x, y with
| [], _ => []
| _, [] => []
| x :: xs, y :: ys => And x y :: AndL xs ys
end.

Fixpoint OrL (x y : list B) : list B :=
match x, y with
| [], _ => []
| _, [] => []
| x :: xs, y :: ys => Or x y :: OrL xs ys
end.

Fixpoint NotL (x : list B) : list B :=
match x with
  | [] => []
  | x :: xs => Not x :: NotL xs
end.

Fixpoint AddLr (x y : list B) (c : B) : list B :=
match x, y with
| [], _ => []
| _, [] => []
| x :: xs, y :: ys => Add x y c :: AddLr xs ys (Rem x y c)
end.

Definition AddL (x y : list B) : list B := rev (AddLr (rev x) (rev y) O).

(* prvo obrnem dva broja koja zelim zbrojiti, zbrojim ih, pa ih ponovno obrnem *)

Fixpoint IncLr (x : list B) (c : B) : list B :=
match x with
| [] => []
| x :: xs => Add x I c :: IncLr xs (Rem x I c)
end.

Definition IncL (x : list B) : list B := rev (IncLr (rev x) O).

(* poseban slucaj Add, sumiramo s jedinicom *)

(* ALU *)

Definition flag_zx (f : B) (x : list B) : list B :=
match f with
| I => repeat O (length x)
| O => x
end.

Definition flag_nx (f : B) (x : list B) : list B :=
match f with
| I => NotL x
| O => x
end.

Definition flag_f (f : B) (x y : list B) : list B :=
match f with
| I => AddL x y
| O => AndL x y
end.

Definition ALU (x y : list B) (zx nx zy ny f no : B) : list B := 
  flag_nx no (flag_f f (flag_nx nx (flag_zx zx x)) (flag_nx ny (flag_zx zy y))).

(* Teoremi *)

(* x i y su sabirnice jednake duljine *)

Lemma ALU_zero (x y : list B) :
  length x = length y -> ALU x y I O I O I O = repeat O (length x).
Proof.
    assert (P : forall (n : nat), AddL (repeat O n) (repeat O n) = repeat O n).
    {
      assert (P_rev_1 : forall (b : B) (n : nat), repeat b n ++ [b] = b :: repeat b n).
      {
        intros. induction n.
        - reflexivity.
        - simpl. rewrite IHn. reflexivity.
      }
      assert (P_rev_2 : forall (b : B) (n : nat), rev (repeat b n) = repeat b n).
      {
        intros. induction n.
        - reflexivity.
        - simpl. rewrite IHn. rewrite P_rev_1. reflexivity.
      }
      intros. unfold AddL.
      rewrite P_rev_2. 
      induction n.
      - reflexivity.
      - simpl. rewrite IHn. rewrite P_rev_1. reflexivity.
    }
    intros H. simpl. rewrite H. rewrite P. reflexivity.
Qed.

Lemma ALU_minus_one (x y : list B) : 
  length x = length y -> ALU x y I I I O I O = repeat I (length x).
Proof.
  assert (P_NotL : forall (n : nat), NotL (repeat O n) = repeat I n).
  {
    intros. induction n.
    - reflexivity.
    - simpl. rewrite IHn. reflexivity.
  }
  assert (P_AddL : forall (n : nat), AddL (repeat I n) (repeat O n) = repeat I n).
  {
    assert (P_rev_1 : forall (b : B) (n : nat), repeat b n ++ [b] = b :: repeat b n).
    {
      intros. induction n.
      - reflexivity.
      - simpl. rewrite IHn. reflexivity.
    }
    assert (P_rev_2 : forall (b : B) (n : nat), rev (repeat b n) = repeat b n).
    {
      intros. induction n.
      - reflexivity.
      - simpl. rewrite IHn. rewrite P_rev_1. reflexivity.
    }
    intros. unfold AddL. rewrite P_rev_2. rewrite P_rev_2. induction n.
    - reflexivity.
    - simpl. rewrite IHn. rewrite P_rev_1. reflexivity.
  }
  intros H. simpl. rewrite H, P_NotL. rewrite P_AddL. reflexivity.
Qed.

Lemma ALU_x (x y : list B) : 
  length x = length y -> ALU x y O O I I O O = x.
Proof. Abort.

Lemma ALU_y (x y : list B) : 
  length x = length y -> ALU x y I I O O O O = y.
Proof. Abort.

Lemma ALU_Not_x (x y : list B) : 
  length x = length y -> ALU x y O O I I O I = NotL x.
Proof. Abort.

Lemma ALU_Not_y (x y : list B) : 
  length x = length y -> ALU x y I I O O O I = NotL y.
Proof. Abort.


Lemma ALU_Add (x y : list B) : 
  length x = length y -> ALU x y O O O O I O = AddL x y.
Proof. Abort.


(* za rijesiti *)
Lemma ALU_And (x y : list B) : 
  length x = length y -> ALU x y O O O O O O = AndL x y.
Proof.
  simpl. intros. reflexivity.
Qed.

Lemma ALU_Or (x y : list B) : 
  length x = length y -> ALU x y O I O I O I = OrL x y.
Proof.
  intros H. unfold ALU. simpl.
  assert(P: forall x y : list B, AndL (NotL x) (NotL y) = NotL (OrL x y)).
  {
    induction x0, y0 ; simpl ; try reflexivity.
    specialize (IHx0 y0). rewrite IHx0. induction a.
    * simpl. reflexivity.
    * simpl. reflexivity.
  }
  assert(G : forall z : list B, NotL (NotL z) = z).
  {
    intros z. induction z.
    - simpl ; reflexivity.
    - simpl. rewrite IHz. induction a ; simpl ; reflexivity.
  }
  specialize (P x y). rewrite P.
  specialize (G (OrL x y)). apply G.
Qed.




Lemma ALU_One (n : nat) (x y : list B) :
  length x = n /\ length y = n /\ n <> 0 -> ALU x y I I I I I I = repeat O (pred n) ++ [I].
Proof.
  intros [H1 [H2 H3]]. unfold ALU. simpl. rewrite H1. rewrite H2. Check Init.Nat.pred n.
  assert(T1: forall n : nat, NotL (repeat O n) = repeat I n).
  {
    intros n0. induction n0 ; simpl.
    - reflexivity.
    - rewrite IHn0. reflexivity.
  }
  rewrite T1.
  assert (T2 : AddL (repeat I n) (repeat I n) = repeat I (pred n) ++ [O]).
  {
    induction n.
    - contradiction.
    - unfold AddL. simpl.
    assert (T3 : forall (b : B) (n : nat), repeat b n ++ [b] = b :: repeat b n).
    {
      intros. induction n0.
      - simpl. reflexivity.
      - simpl. rewrite IHn0. reflexivity.
    }
    assert (T4 : forall (b : B) (n : nat), rev (repeat b n) = repeat b n).
    {
      intros. induction n0.
      - reflexivity.
      - simpl. rewrite IHn0. rewrite T3. reflexivity.
    }
    specialize (T4 I n). rewrite T4.
    assert (T5: forall (b : B) (n : nat), repeat b n ++ [b] = repeat b (S n)).
    {
      intros. simpl. induction n0.
     - simpl. reflexivity.
     - simpl. rewrite IHn0. reflexivity.
    }
    specialize (T5 I n). rewrite T5. simpl. f_equal.
    assert(T6: forall n, AddLr (repeat I n) (repeat I n) I = repeat I n).
    {
     intros. induction n0 ; simpl. 
     - reflexivity.
     - rewrite IHn0. reflexivity.
    }
   specialize (T6 n). rewrite T6. rewrite T4. reflexivity.
  }
   rewrite T2.
   assert(T7: forall X Y : list B, NotL(X ++ Y) = NotL X ++ NotL Y).
   {
     intros. induction X ; simpl. 
     - reflexivity.
     - rewrite IHX. reflexivity.
   }
   specialize (T7 (repeat I (pred n)) [O]). rewrite T7. simpl. f_equal.
   assert (T8: forall n : nat, NotL (repeat I n) = repeat O n).
   {
    intros. induction n0 ; simpl.
    - reflexivity.
    - rewrite IHn0. reflexivity.
   }
   specialize (T8 (pred n)). rewrite T8. reflexivity.
Qed.
