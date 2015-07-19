(*=========================================================================
  Setup & Sorting
*)

Require Import SfLib.
Require Import Coq.Structures.Orders.
Require Import Coq.Sorting.Sorting.

(* From Coq.Structures.Orders. *)
Local Coercion is_true : bool >-> Sortclass.
Hint Unfold is_true.

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


(*=========================================================================
  Theorems about inequality

  Much of this machinery exists to translate between boolean expressions
  like `leb a b` and logical propositions like `a <= b`.
*)

(* Deal with implications of the form `ObviouslyFalse -> P` by introducting
  `ObviouslyFalse` as a hypotheses and inverting it. There's probably a
  built-in which does this, but I can't find it. *)
Ltac antecedent_is_false :=
  (* Use solve to make sure we either prove our goal completely, or fail
     atomically and leave the hypotheses unchanged. *)
  solve [ intros contra; inversion contra ].

Theorem leb_true : forall n m,
  n <=? m = true -> n <= m.
Proof.
  (* Dispose of most cases mechanically using built-in hypotheses. *)
  induction n; destruct m; simpl; auto using le_0_n, le_n_S.
  (* The remaining case is an obvious contradiction. *)
  antecedent_is_false.
Qed.

Theorem le_implies_leb_true : forall n m, n <= m -> n <=? m.
Proof.
  induction n; destruct m; simpl; auto using le_S_n.
  antecedent_is_false.
Qed.

(* Alternate: https://github.com/timjb/software-foundations/blob/master/Logic.v
   This gave me the hint to induct on m. *)
Theorem leb_false : forall n m,
  n <=? m = false -> ~(n <= m).
Proof.
  intros n m. generalize dependent n.
  (* Give the pattern of our proof, and simplify. *)
  induction m; destruct n; simpl;
    (* Eliminate cases with obvious contractions. *)
    try antecedent_is_false.
  Case "~ S n <= 0". auto using le_Sn_0.
  Case "n <=? m = false -> ~ S n <= S m".
     (* Use our induction hypothesis to rewrite the left-hand side,
        then use omega for logic crunching. *)
    intros H_not_leq_n_m. apply IHm in H_not_leq_n_m. omega.
Qed.

(* As a general rule, we can solve any trivial theorem about inequalities using
   the omega tactic. *)
Lemma flip_not_le : forall (a b : nat), not (a <= b) -> b <= a.
Proof. intros. omega. Qed.

(* This is somewhat specific (and deliberately weak) lemma that turns
   up a lot in our main proof. *)
Lemma flip_not_leb : forall (a b : nat), (a <=? b) = false -> b <=? a.
Proof.
  intros. apply leb_false in H. apply flip_not_le in H.
  apply le_implies_leb_true. assumption.
Qed.


(*=========================================================================
  Insertion
*)

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


(*=========================================================================
  Proof: Insertion preserves sorting
*)

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
      SSCase "Sorted (insert_sorted n l')". apply IHl'. auto.
      SSCase "HdRel n' (insert_sorted n l')".
        apply IHl' in H_sorted_l'.
        destruct l'; simpl; auto.
        destruct (n <=? n0); auto.
        inversion HdRel_n'_l'. auto.
Qed.


(*=========================================================================
  Generating Haskell code
*)

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
