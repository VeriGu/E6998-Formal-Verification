(** * Assignment 3: COMS E6998 Formal Verification of System Software *)

(** 

    - Due 11/20/2020 at 11:59 pm
    - Replace all the Admitted with your proofs or definitions.
    - Submit the filled in Assignment3.v via coursework2
    - Academic Honesty
      The computer science department has very strict policies. 
      Please read the department [Academic Honesty page](http://www.cs.columbia.edu/education/honesty/).
      You MUST submit original homework written by you and you alone.
      Do not look at anybody else’s answer. 
      Do not show anybody your answer, or leave your answer where somebody else could see it.
      Cases of non-original submission will receive a 0 and will be referred to the Judicial Committee.

    1) To compile the assigment, first download the following files
    
    _CoqProject
    Coq_Lecture1_Basics.v
    Coq_Lecture2_Induction_List.v
    Coq_Lecture3_Tactics_Logic.v 
    Coq_Lecture4_Program.v              
    Assignment3.v
    
    in the same directory.
    
    2) Then compile Coq_Lecture4_Program.v by
    [coqc Coq_Lecture1_Basics Coq_Lecture2_Induction_List Coq_Lecture3_Tactics_Logic Coq_Lecture4_Program]
    
*)

Require Export Coq_Lecture3_Tactics_Logic Coq_Lecture4_Program.

(* ################################################################# *)
(** * Problem 1 *)

(** Prove the following Theorem  *)
Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(* ################################################################# *)
(** * Problem 2 *)

(** Prove by induction. *)

Theorem filter_exercise : forall (X : Type) (l lf : list X) (test : X -> bool)
                             (x : X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Problem 3 ~ Problem 6 *)
(** Old HP Calculators, programming languages like Forth and Postscript,
    and abstract machines like the Java Virtual Machine all evaluate
    arithmetic expressions using a _stack_. For instance, the expression

      (2*3)+(3*(4-2))

   would be written as

      2 3 * 3 4 2 - * +

   and evaluated like this (where we show the program being evaluated
   on the right and the contents of the stack on the left):

      [ ]           |    2 3 * 3 4 2 - * +
      [2]           |    3 * 3 4 2 - * +
      [3, 2]        |    * 3 4 2 - * +
      [6]           |    3 4 2 - * +
      [3, 6]        |    4 2 - * +
      [4, 3, 6]     |    2 - * +
      [2, 4, 3, 6]  |    - * +
      [2, 3, 6]     |    * +
      [6, 6]        |    +
      [12]          |

  The goal of the following problems is to write a small compiler that
  translates [aexp]s into stack machine instructions.

  The instruction set for our stack language will consist of the
  following instructions:
     - [SPush n]: Push the number [n] on the stack.
     - [SLoad x]: Load the identifier [x] from the store and push it
                  on the stack
     - [SPlus]:   Pop the two top numbers from the stack, add them, and
                  push the result onto the stack.
     - [SMinus]:  Similar, but subtract.
     - [SMult]:   Similar, but multiply. *)

Inductive sinstr : Type :=
| SPush : nat -> sinstr
| SLoad : string -> sinstr
| SPlus : sinstr
| SMinus : sinstr
| SMult : sinstr.

(* ################################################################# *)
(** * Problem 3 *)

(** Write a function to evaluate programs in the stack language. It
    should take as input a state, a stack represented as a list of
    numbers (top stack item is the head of the list), and a program
    represented as a list of instructions, and it should return the
    stack after executing the program.  Test your function on the
    examples below.

    Note that the specification leaves unspecified what to do when
    encountering an [SPlus], [SMinus], or [SMult] instruction if the
    stack contains less than two elements. The function should return
    None for these unspecified cases. But our compiler will never 
    emit such a malformed program. *)

(** Execute an instruction **)
Definition s_execute_instr (st : state) (stack : list nat)
         (instr : sinstr)
  : option (list nat)
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
               
(** Execute a program **)                                           
Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
  : option (list nat)
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
    
    
  
(*  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.*)

Example s_execute1 :
     s_execute { --> 0 } []
       [SPush 5; SPush 3; SPush 1; SMinus]
     = Some [2; 5].
(* FILL IN HERE *) Admitted.

Example s_execute2 :
     s_execute { X --> 3 } [3;4]
       [SPush 4; SLoad X; SMult; SPlus]
   = Some [15; 4].
(* FILL IN HERE *) Admitted.

(* ################################################################# *)
(** * Problem 4 *)

(** Next, write a function that compiles an [aexp] into a stack
    machine program. The effect of running the program should be the
    same as pushing the value of the expression on the stack. *)

Fixpoint s_compile (e : aexp) : list sinstr
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** After you've defined [s_compile], prove the following to test
    that it works. *)

Local Open Scope aexp_scope.

Example s_compile1 :
  s_compile (X .- (2 .* Y))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
(* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Problem 5 *)

(** Prove the following property for s_execute *)
Theorem s_execute_mono : forall (l1 l2: list sinstr) (sk sk': list nat) (st : state),
  s_execute st sk l1 = Some sk' ->
  s_execute st sk (l1 ++ l2) = s_execute st sk' l2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)    

(* ################################################################# *)
(** * Problem 6 *)
    
(** Now we'll prove the correctness of the compiler implemented in the
    previous exercise.  Remember that the specification left
    unspecified what to do when encountering an [SPlus], [SMinus], or
    [SMult] instruction if the stack contains less than two
    elements.  (In order to make your correctness proof easier you
    might find it helpful to go back and change your implementation!)

    Prove the following theorem.  You will need to start by stating a
    more general lemma to get a usable induction hypothesis; the main
    theorem will then be a simple corollary of this lemma. *)

Theorem s_compile_correct' : forall (e : aexp) (sk: list nat) (st : state),
  s_execute st sk (s_compile e) = Some (aeval st e :: sk).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = Some [ aeval st e ].
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)
