Require Import Arith.
Require Import SfLib.
Require Import Coq.Structures.Orders.
Require Import Coq.Sorting.Sorting.

(** From Coq.Structures.Orders. *)
Local Coercion is_true : bool >-> Sortclass.
Hint Unfold is_true.

(* This allows us to use the boolean value 'true' as if it were the logical
   proposition True. *)
Example test_true : true.
Proof. auto. Qed.

(* From Coq.Sorting.Mergesort NatOrder example. Highest priority is 0. *)
Module Import PriorityOrder <: TotalLeBool.
  Definition t := nat.
  Fixpoint leb x y :=
    match x, y with
    | 0, _ => true
    | _, 0 => false
    | S x', S y' => leb x' y'
    end.
  Infix "<=?" := leb (at level 35).
  Theorem leb_total : forall a1 a2, a1 <=? a2 \/ a2 <=? a1.
  Proof. induction a1; destruct a2; simpl; auto. Qed.
End PriorityOrder.

(* Based on https://github.com/timjb/software-foundations/blob/master/Logic.v *)
Theorem leb_true : forall n m,
  n <=? m = true -> n <= m.
Proof.
  induction n as [|n'].
  Case "n = O". intros. apply le_0_n.
  Case "n = S n'". destruct m as [| m'].
    SCase "m = O". intros contra. inversion contra.
    SCase "m = S m'". intros H. simpl in H.
    apply le_n_S. apply IHn'. apply H.
Qed.

Theorem le_implies_leb_true : forall n m, n <= m -> n <=? m.
Proof.
  induction n as [|n'].
  Case "n = O". auto.
  Case "n = S n'". destruct m as [| m'].
    SCase "m = O". intros H. inversion H.
    SCase "m = S m'". intros H. simpl. apply IHn'. apply le_S_n. assumption.
Qed.

(* Copied from https://github.com/timjb/software-foundations/blob/master/Logic.v *)
Theorem leb_false : forall n m,
  n <=? m = false -> ~(n <= m).
Proof.
  intros n m. generalize dependent n.
  induction m as [|m'].
  Case "n = O". intros n h lte. inversion lte. rewrite H in h. inversion h.
  Case "n = S n'". intros n h lte. destruct n as [| n'].
    inversion h.
    apply IHm' in h. apply h. apply le_S_n. apply lte.
Qed.

Module Import PrioritySort := Sort PriorityOrder.

Example test_Sorted : Sorted leb [1; 2; 3].
Proof. auto. Qed.

Example test_not_Sorted : Sorted leb [2; 1; 3] -> False.
Proof.
  (* Name the hypothesis on the left side of "->" and break Sorted down by cases. *)
  intros contra. inversion contra.

  (* Look for an obviously false hypothesis, break it down, and repeat. *)
  repeat match goal with
    | [ H : HdRel _ 2 [1; 3] |- False ] => inversion_clear H
    | [ H : is_true (2 <=? 1) |- False ] => inversion_clear H
  end.
Qed.

Fixpoint insert_sorted (n : nat) (l : list nat) : list nat :=
  match l with
    | [] => [n]
    | n' :: l' =>
      if n <=? n'
      then n :: l
      else n' :: insert_sorted n l'
  end.

(* It's worth writing unit tests before trying to prove something really
   complicated, because doing so will make basic failures obvious, and
   you won't watch a proof fall apart mysteriously on some subclause. *)
Example test_insert_3_1_2 :
  insert_sorted 2 (insert_sorted 1 (insert_sorted 3 [])) = [1; 2; 3].
Proof. reflexivity. Qed.

Example test_insert_2_1_3 :
  insert_sorted 3 (insert_sorted 1 (insert_sorted 2 [])) = [1; 2; 3].
Proof. reflexivity. Qed.

Example test_insert_2_1_1 :
  insert_sorted 1 (insert_sorted 1 (insert_sorted 2 [])) = [1; 1; 2].
Proof. reflexivity. Qed.

(* As a general rule, we can solve any trivial theorem about inequalities using
   the omega tactic. *)
Theorem flip_not_le : forall (a b : nat), not (a <= b) -> b <= a.
Proof. intros. omega. Qed.

Theorem flip_not_leb : forall (a b : nat), (a <=? b) = false -> b <=? a.
Proof.
  intros. apply leb_false in H. apply flip_not_le in H.
  apply le_implies_leb_true. assumption.
Qed.
Hint Resolve flip_not_leb.

Hint Constructors Sorted.
Hint Constructors HdRel.

Theorem insert_sorted_stays_sorted : forall n l,
  Sorted leb l -> Sorted leb (insert_sorted n l).
Proof.
  intros n l H_sorted_l.
  induction l as [|n' l']; simpl; auto.
  Case "l = n' :: l'".
    destruct (n <=? n') eqn:H_n_le_n'; auto.
    SCase "n <=? n' = false".
      apply Sorted_inv in H_sorted_l.
      inversion H_sorted_l as [H_sorted_l' HdRel_n'_l'].

      apply Sorted_cons.
      { apply IHl'. auto. }
      {
        apply IHl' in H_sorted_l'.
        destruct l'; simpl; auto.
        destruct (n <=? n0); auto.
        inversion HdRel_n'_l'. auto.
      }
Qed.

Extraction Language Haskell.
Extract Inductive list => "([])" [ "[]" "(:)" ].
Extract Inductive bool => "Bool" [ "True" "False" ].
Extract Inductive nat => "Int" ["0" "(1+)"].
Extraction insert_sorted.

(*

Haskell supporting bits.

leb :: Int -> Int -> Bool
leb = (<=)

main :: IO () 
main = do
  print $ insert_sorted 5 (insert_sorted 3 [])

*)