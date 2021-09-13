(** * Assignment 2: COMS E6998 Formal Verification of System Software *)

(**

    - Due 10/21/2020 at 11:59 pm
    - Replace all the Admitted with your proofs or definitions.
    - Submit the filled in Assignment.v via coursework2
    - Academic Honesty
      The computer science department has very strict policies.
      Please read the department [Academic Honesty page](http://www.cs.columbia.edu/education/honesty/).
      You MUST submit original homework written by you and you alone.
      Do not look at anybody else’s answer.
      Do not show anybody your answer, or leave your answer where somebody else could see it.
      Cases of non-original submission will receive a 0 and will be referred to the Judicial Committee.

    1) To compile the assigment, first download the following files

    Coq_Lecture1_Basics.v
    Coq_Lecture2_Induction_List.v
    Coq_Lecture3_Tactics_Logic.v
    Assignment2.v

    in the same directory.

    2) Then compile Coq_Lecture3_Tactics_Logic.v by
    [coqc Coq_Lecture1_Basics Coq_Lecture2_Induction_List Coq_Lecture3_Tactics_Logic]
*)

Require Import Coq_Lecture3_Tactics_Logic.

(* ################################################################# *)
(** * Problem 1 *)

Lemma double_negb:
  forall b, negb (negb b) = b.
(* FILL IN HERE *) Admitted.


(* ################################################################# *)
(** * Problem 2 *)

Module Integer.

  (** In this problem, we will define Integer types together.
      Let's first define Positive Integers. *)

  Inductive Positive :=
  | I (* 1 *)
  | S (p: Positive).

  (** Integher can then be inductively defined using Positive. *)
  Inductive Integer :=
  | O (* 0 *)
  | Pos (p: Positive)
  | Neg (p: Positive).

  (** Please define the negi function to calculate the negation of an integer *)

  Definition negi (i: Integer): Integer
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

  Example test_negi1: negi O = O.
  (* FILL IN HERE *) Admitted.

  Example test_negi2: negi (Pos I) = Neg I.
  (* FILL IN HERE *) Admitted.


  (** Please define the add1 function to add 1 to the given integer *)
  Definition add1 (i: Integer): Integer
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.


  Example test_add11: add1 O = Pos I.
  (* FILL IN HERE *) Admitted.


  Example test_add12: add1 (Neg I) = O.
  (* FILL IN HERE *) Admitted.

  Example test_add13: add1 (Pos I) = Pos (S I).
  (* FILL IN HERE *) Admitted.

End Integer.

(* ################################################################# *)
(** * Problem 3 *)

Module NatPlayground3.

  (** In the class, we have defined our own plus and mult for nat. *)
  Print NatPlayground2.plus.
  Print NatPlayground2.mult.

  (** Let's try to define our own exponential function for nat. *)
  Fixpoint exp (base power : nat) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

  Lemma exp_1: forall power, exp 1 power = 1.
  (* FILL IN HERE *) Admitted.

  Eval compute in (exp 2 4).

End NatPlayground3.

(* ################################################################# *)
(** * Problem 4 *)

Module NatPlayground4.

  (** Let's prove some properties of plus and mult  *)
  Theorem plus_assoc : forall m n t : nat,
      m + (n + t) = m + n + t.
  (* FILL IN HERE *) Admitted.

  (** Hint use plus_assoc and plus_comm *)
  Theorem plus_comm' : forall m n t : nat,
      m + n + t = m + t + n.
  (* FILL IN HERE *) Admitted.

  (** Hint use plus_assoc and plus_comm' *)
  Theorem mult_plus_distr : forall m n t : nat,
      m * (n + t) = m * n + m * t.
  (* FILL IN HERE *) Admitted.

End NatPlayground4.


(* ################################################################# *)
(** * Problem 5 *)

(** Prove the following properties over beq_nat *)
Print beq_nat.

Lemma beq_nat_eq:
  forall n m,
    beq_nat n m = true ->
    n = m.
(* FILL IN HERE *) Admitted.

Lemma beq_nat_eq':
  forall n m,
    n = m
    -> beq_nat n m = true.
(* FILL IN HERE *) Admitted.

(** Hint: recall the Lecure for logic *)
Theorem zero_not_one : ~(0 = 1).
Proof.
  intros contra. inversion contra.
Qed.

Lemma beq_nat_neq:
  forall n m,
    beq_nat n m = false ->
    n <> m.
(* FILL IN HERE *) Admitted.

(** Hint use ex_falso_quodlibet *)
Lemma beq_nat_neq':
  forall n m,
    n <> m
    -> beq_nat n m = false.
(* FILL IN HERE *) Admitted.


(* ################################################################# *)
(** * Problem 6 *)

(** *** Bags via Lists *)

(** A [bag] (or [multiset]) is like a set, except that each element
    can appear multiple times rather than just once.  One possible
    implementation is to represent a bag of numbers as a list. *)

Definition bag := list nat.

(** Complete the following definitions for the functions
    [count], [sum], [add], and [member] for bags. *)

Fixpoint count (v:nat) (s:bag) : nat
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** All these proofs can be done just by [reflexivity]. *)
Example test_count1:              count 1 [1;2;3;1;4;1] = 3.
 (* FILL IN HERE *) Admitted.
Example test_count2:              count 6 [1;2;3;1;4;1] = 0.
simpl.
 (* FILL IN HERE *) Admitted.

(** Multiset [sum] is similar to set [union]: [sum a b] contains all
    the elements of [a] and of [b].  (Mathematicians usually define
    [union] on multisets a little bit differently -- using max instead
    of sum -- which is why we don't use that name for this operation.)
    For [sum] we're giving you a header that does not give explicit
    names to the arguments.  Moreover, it uses the keyword
    [Definition] instead of [Fixpoint], so even if you had names for
    the arguments, you wouldn't be able to process them recursively.
    The point of stating the question this way is to encourage you to
    think about whether [sum] can be implemented in another way --
    perhaps by using functions that have already been defined.  *)

Definition sum : bag -> bag -> bag
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_sum1:              count 1 (sum [1;2;3] [1;4;1]) = 3.
 (* FILL IN HERE *) Admitted.

Definition add (v:nat) (s:bag) : bag
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_add1:                count 1 (add 1 [1;4;1]) = 3.
 (* FILL IN HERE *) Admitted.
Example test_add2:                count 5 (add 1 [1;4;1]) = 0.
 (* FILL IN HERE *) Admitted.

Definition member (v:nat) (s:bag) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_member1:             member 1 [1;4;1] = true.
 (* FILL IN HERE *) Admitted.

Example test_member2:             member 2 [1;4;1] = false.
(* FILL IN HERE *) Admitted.
(** [] *)
