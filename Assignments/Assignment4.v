(** * Assignment 4: COMS E6998 Formal Verification of System Software *)

(** 

    - Due 11/27/2020 at 11:59 pm
    - Replace all the Admitted with your proofs or definitions.
    - Submit the filled in Assignment4.v via coursework2
    - Academic Honesty
      The computer science department has very strict policies. 
      Please read the department [Academic Honesty page](http://www.cs.columbia.edu/education/honesty/).
      You MUST submit original homework written by you and you alone.
      Do not look at anybody else’s answer. 
      Do not show anybody your answer, or leave your answer where somebody else could see it.
      Cases of non-original submission will receive a 0 and will be referred to the Judicial Committee.

    1) To compile the assigment, first download the following files
    
    _CoqProject 
    Coq_Lecture4_Program.v              
    Assignment4.v
    
    in the same directory.
    
    2) Then compile Coq_Lecture4_Program.v by
    [coqc Coq_Lecture4_Program]

    
    [make]
*)

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.

Require Export Coq_Lecture4_Program.

(** * Problem 1 ~ Problem 6 *)
(** Imperative languages like C and Java often include a [break] or
    similar statement for interrupting the execution of loops. In this
    assignment we consider how to add [break] to Imp.  First, we need to
    enrich the language of commands with an additional case. *)

Inductive com : Type :=
  | CSkip : com
  | CBreak : com               (* <-- new *)
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "'BREAK'" :=
  CBreak.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

(** Next, we need to define the behavior of [BREAK].  Informally,
    whenever [BREAK] is executed in a sequence of commands, it stops
    the execution of that sequence and signals that the innermost
    enclosing loop should terminate.  (If there aren't any
    enclosing loops, then the whole program simply terminates.)  The
    final state should be the same as the one in which the [BREAK]
    statement was executed.

    One important point is what to do when there are multiple loops
    enclosing a given [BREAK]. In those cases, [BREAK] should only
    terminate the _innermost_ loop. Thus, after executing the
    following...

       X ::= 0;;
       Y ::= 1;;
       WHILE 0 <> Y DO
         WHILE TRUE DO
           BREAK
         END;;
         X ::= 1;;
         Y ::= Y .- 1
       END

    ... the value of [X] should be [1], and not [0].

    One way of expressing this behavior is to add another parameter to
    the evaluation relation that specifies whether evaluation of a
    command executes a [BREAK] statement: *)

Inductive result : Type :=
  | SContinue : result
  | SBreak : result.

Reserved Notation "c1 '/' st '\\' s '/' st'"
                  (at level 40, st, s at level 39).

(** Intuitively, [c / st \\ s / st'] means that, if [c] is started in
    state [st], then it terminates in state [st'] and either signals
    that the innermost surrounding loop (or the whole program) should
    exit immediately ([s = SBreak]) or that execution should continue
    normally ([s = SContinue]).

    The definition of the "[c / st \\ s / st']" relation is very
    similar to the one we gave above for the regular evaluation
    relation ([c / st \\ st']) -- we just need to handle the
    termination signals appropriately:

    - If the command is [SKIP], then the state doesn't change and
      execution of any enclosing loop can continue normally.

    - If the command is [BREAK], the state stays unchanged but we
      signal a [SBreak].

    - If the command is an assignment, then we update the binding for
      that variable in the state accordingly and signal that execution
      can continue normally.

    - If the command is of the form [IFB b THEN c1 ELSE c2 FI], then
      the state is updated as in the original semantics of Imp, except
      that we also propagate the signal from the execution of
      whichever branch was taken.

    - If the command is a sequence [c1 ;; c2], we first execute
      [c1].  If this yields a [SBreak], we skip the execution of [c2]
      and propagate the [SBreak] signal to the surrounding context;
      the resulting state is the same as the one obtained by
      executing [c1] alone. Otherwise, we execute [c2] on the state
      obtained after executing [c1], and propagate the signal
      generated there.

    - Finally, for a loop of the form [WHILE b DO c END], the
      semantics is almost the same as before. The only difference is
      that, when [b] evaluates to true, we execute [c] and check the
      signal that it raises.  If that signal is [SContinue], then the
      execution proceeds as in the original semantics. Otherwise, we
      stop the execution of the loop, and the resulting state is the
      same as the one resulting from the execution of the current
      iteration.  In either case, since [BREAK] only terminates the
      innermost loop, [WHILE] signals [SContinue]. *)

(* ################################################################# *)
(** * Problem 1 *)

(** Based on the above description, complete the definition of the
    [ceval] relation. *)

Inductive ceval : com -> state -> result -> state -> Prop :=
  | E_Skip : forall st,
      CSkip / st \\ SContinue / st
  (* FILL IN HERE *)

  where "c1 '/' st '\\' s '/' st'" := (ceval c1 st s st').

Local Open Scope aexp_scope.
Local Open Scope bexp_scope.

Definition example: com :=
  X ::= 0;;
  Y ::= 1;;
  WHILE !(0 =? Y) DO
    WHILE true DO
      BREAK
    END;;
    X ::= 1;;
    Y ::= Y .- 1
  END.

Ltac inversion_program st :=
  match goal with
  | [Htf: true = false |- _] => inversion Htf
  | [Hft: false = true |- _] => inversion Hft
  | [Hst0: _ / ?st0 \\ _ / _  |- _ ] =>
    match st0 with
    | context[st] => (* context[st] means that the term contains st*)
      inversion Hst0; subst; simpl in *; clear Hst0
    end
  end.

Theorem ceval_example:
  forall st st',
    example / st \\ SContinue / st' ->
    st' X = 1 /\ st' Y = 0.
Proof.
  (* Please fix the following proof if it is broken by your definition.
  intros.
  repeat inversion_program st.
  rewrite t_update_eq.
  rewrite t_update_neq.
  - rewrite t_update_eq. split; reflexivity.
  - intro HF; inversion HF. 
Qed.
*)
Admitted.

(* ################################################################# *)
(** * Problem 2 *)
Theorem break_ignore : forall c st st' s,
     (BREAK;; c) / st \\ s / st' ->
     st = st'.
Proof.
  (* FILL IN HERE *) Admitted.

(* ################################################################# *)
(** * Problem 3 *)
Theorem while_continue : forall b c st st' s,
  (WHILE b DO c END) / st \\ s / st' ->
  s = SContinue.
Proof.
  (* FILL IN HERE *) Admitted.

(* ################################################################# *)
(** * Problem 4 *)
Theorem while_stops_on_break : forall b c st st',
  beval st b = true ->
  c / st \\ SBreak / st' ->
  (WHILE b DO c END) / st \\ SContinue / st'.
Proof.
  (* FILL IN HERE *) Admitted.

(* ################################################################# *)
(** * Problem 5 *)
(** Hint: use induction over He **)
Theorem while_break_true :
  forall p b c st st' 
         (Heq: p = (WHILE b DO c END))
         (He: p / st \\ SContinue / st')
         (Heval: beval st' b = true),
    exists st'', c / st'' \\ SBreak / st'.
Proof.
(* FILL IN HERE *) Admitted.

(* ################################################################# *)
(** * Problem 6 *)
(** Hint: refer to the deterministic for the original com taught in class **)
Theorem ceval_deterministic: forall (c:com) st st1 st2 s1 s2,
     c / st \\ s1 / st1  ->
     c / st \\ s2 / st2 ->
     st1 = st2 /\ s1 = s2.
Proof.
  (* FILL IN HERE *) Admitted.
