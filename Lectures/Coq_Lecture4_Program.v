(** * Simple Imperative Programs *)

(* ################################################################# *)
(** * Acknowledgement *)

(** The materials are borrowed from the  _Software Foundations_ series. 
    http://softwarefoundations.cis.upenn.edu 
 *)

(**  Compile the lecture notes using
    [coqc Coq_Lecture1_Basics Coq_Lecture2_Induction_List Coq_Lecture3_Tactics_Logic Coq_Lecture4_Program]

*)

(** In this chapter, we'll take a more serious look at how to use Coq
    to study interesting things outside of itself.  Our case study is
    a _simple imperative programming language_ called Imp, embodying a
    tiny core fragment of conventional mainstream languages such as C
    and Java.  Here is a familiar mathematical function written in
    Imp.

       Z ::= X;;
       Y ::= 1;;
       WHILE ! (Z =? 0) DO
         Y ::= Y .* Z;;
         Z ::= Z .- 1
       END
 *)

(** This chapter looks at how to define the _syntax_ and _semantics_
    of Imp; further chapters in _Programming Language Foundations_
    (_Software Foundations_, volume 2) develop a theory of _program
    equivalence_ and introduce _Hoare Logic_, a widely used logic for
    reasoning about imperative programs. *)

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.

(*From LF Require Import Maps.*)

(* ################################################################# *)
(** * Arithmetic and Boolean Expressions *)

(** We'll present Imp in three parts: first a core language of
    _arithmetic and boolean expressions_, then an extension of these
    expressions with _variables_, and finally a language of _commands_
    including assignment, conditions, sequencing, and loops. *)

(* ================================================================= *)
(** ** Syntax *)

Module AExp.

  (** These two definitions specify the _abstract syntax_ of
    arithmetic and boolean expressions. *)

  Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (e1 e2:  aexp) (* e1 + e2*)
  | AMinus (e1 e2:  aexp) (* e1 - e2 *)
  | AMult (e1 e2:  aexp) (* e1 * e2 *).

  Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (e1 e2 : aexp) (* e1 == e2 *)
  | BLe (e1 e2 : aexp) (* e1 <= e2 *)
  | BNot (b : bexp) (*  ~b  *)
  | BAnd (b1 b2 : bexp) (* b1 /\ b2 *).

  (** In this chapter, we'll mostly elide the translation from the
    concrete syntax that a programmer would actually write to these
    abstract syntax trees -- the process that, for example, would
    translate the string ["1+2*3"] to the AST

      APlus (ANum 1) (AMult (ANum 2) (ANum 3)). *)

  (** For comparison, here's a conventional BNF (Backus-Naur Form)
    grammar defining the same abstract syntax:

    a ::= nat
        | a + a
        | a - a
        | a * a

    b ::= true
        | false
        | a = a
        | a <= a
        | not b
        | b and b
   *)

  (** Compared to the Coq version above...

       - The BNF is more informal -- for example, it gives some
         suggestions about the surface syntax of expressions (like the
         fact that the addition operation is written [+] and is an
         infix symbol) while leaving other aspects of lexical analysis
         and parsing (like the relative precedence of [+], [-], and
         [*], the use of parens to explicitly group subexpressions,
         etc.) unspecified.  Some additional information (and human
         intelligence) would be required to turn this description into
         a formal definition, for example when implementing a
         compiler.

         The Coq version consistently omits all this information and
         concentrates on the abstract syntax only.

       - On the other hand, the BNF version is lighter and easier to
         read.  Its informality makes it flexible, a big advantage in
         situations like discussions at the blackboard, where
         conveying general ideas is more important than getting every
         detail nailed down precisely.

         Indeed, there are dozens of BNF-like notations and people
         switch freely among them, usually without bothering to say
         which form of BNF they're using because there is no need to:
         a rough-and-ready informal understanding is all that's
         important.

    It's good to be comfortable with both sorts of notations: informal
    ones for communicating between humans and formal ones for carrying
    out implementations and proofs. *)

  (* ================================================================= *)
  (** ** Evaluation *)

  (** _Evaluating_ an arithmetic expression produces a number. *)

  Fixpoint aeval (a : aexp) : nat :=
    match a with
    | ANum n => n
    | APlus a1 a2 => (aeval a1) + (aeval a2)
    | AMinus a1 a2  => (aeval a1) - (aeval a2)
    | AMult a1 a2 => (aeval a1) * (aeval a2)
    end.

  Example test_aeval1:
    aeval (APlus (ANum 2) (ANum 2)) = 4.
  Proof. simpl. reflexivity. Qed.

  (** Similarly, evaluating a boolean expression yields a boolean. *)
  Fixpoint beval (b : bexp) : bool :=
    match b with
    | BTrue       => true
    | BFalse      => false
    | BEq a1 a2   => beq_nat (aeval a1) (aeval a2)
    | BLe a1 a2   => leb (aeval a1) (aeval a2)
    | BNot b1     => negb (beval b1)
    | BAnd b1 b2  => andb (beval b1) (beval b2)
    end.

  (* ================================================================= *)
  (** ** Optimization *)

  (** We haven't defined very much yet, but we can already get
    some mileage out of the definitions.  Suppose we define a function
    that takes an arithmetic expression and slightly simplifies it,
    changing every occurrence of [0+e] (i.e., [(APlus (ANum 0) e])
    into just [e]. *)

  Fixpoint optimize_0plus (a:aexp) : aexp :=
    match a with
    | ANum n =>
      ANum n
    | APlus (ANum 0) e2 =>
      optimize_0plus e2
    | APlus e1 e2 =>
      APlus (optimize_0plus e1) (optimize_0plus e2)
    | AMinus e1 e2 =>
      AMinus (optimize_0plus e1) (optimize_0plus e2)
    | AMult e1 e2 =>
      AMult (optimize_0plus e1) (optimize_0plus e2)
    end.

  (** To make sure our optimization is doing the right thing we
    can test it on some examples and see if the output looks OK. *)

  Example test_optimize_0plus:
    optimize_0plus (APlus (ANum 2)
                          (APlus (ANum 0)
                                 (APlus (ANum 0) (ANum 1))))
    = APlus (ANum 2) (ANum 1).
  Proof. simpl. reflexivity. Qed.

  (** But if we want to be sure the optimization is correct --
    i.e., that evaluating an optimized expression gives the same
    result as the original -- we should prove it. *)

  Theorem optimize_0plus_sound: forall a,
      aeval (optimize_0plus a) = aeval a.
  Proof.
    induction a; trivial;
      try (simpl; rewrite IHa1; rewrite IHa2;
           reflexivity).
    simpl.
    destruct a1;
      try(simpl in *; rewrite IHa1; rewrite IHa2;
          reflexivity).
    destruct n; simpl; rewrite IHa2; reflexivity.
  Qed.

  (* ################################################################# *)
  (** * Coq Automation *)

  (** The amount of repetition in this last proof is a little
    annoying.  And if either the language of arithmetic expressions or
    the optimization being proved sound were significantly more
    complex, it would start to be a real problem.

    So far, we've been doing all our proofs using just a small handful
    of Coq's tactics and completely ignoring its powerful facilities
    for constructing parts of proofs automatically.  This section
    introduces some of these facilities, and we will see more over the
    next several chapters.  Getting used to them will take some
    energy -- Coq's automation is a power tool -- but it will allow us
    to scale up our efforts to more complex definitions and more
    interesting properties without becoming overwhelmed by boring,
    repetitive, low-level details. *)

  (* ================================================================= *)
  (** ** Tacticals *)

  (** _Tacticals_ is Coq's term for tactics that take other tactics as
    arguments -- "higher-order tactics," if you will.  *)

  (* ----------------------------------------------------------------- *)
  (** *** The [try] Tactical *)

  (** If [T] is a tactic, then [try T] is a tactic that is just like [T]
    except that, if [T] fails, [try T] _successfully_ does nothing at
    all (instead of failing). *)

  Theorem silly1 : forall ae, aeval ae = aeval ae.
  Proof. try reflexivity. (* this just does [reflexivity] *) Qed.

  Theorem silly2 : forall (P : Prop), P -> P.
  Proof.
    intros P HP.
    try reflexivity. (* just [reflexivity] would have failed *)
    apply HP. (* we can still finish the proof in some other way *)
  Qed.

  (** There is no real reason to use [try] in completely manual
    proofs like these, but it is very useful for doing automated
    proofs in conjunction with the [;] tactical, which we show
    next. *)

  (* ----------------------------------------------------------------- *)
  (** *** The [;] Tactical (Simple Form) *)

  (** In its most common form, the [;] tactical takes two tactics as
    arguments.  The compound tactic [T;T'] first performs [T] and then
    performs [T'] on _each subgoal_ generated by [T]. *)

  (** For example, consider the following trivial lemma: *)

  Lemma foo : forall n, leb 0 n = true.
  Proof.
    intros.
    destruct n.
    (* Leaves two subgoals, which are discharged identically...  *)
    - (* n=0 *) simpl. reflexivity.
    - (* n=Sn' *) simpl. reflexivity.
  Qed.

  (** We can simplify this proof using the [;] tactical: *)

  Lemma foo' : forall n, leb 0 n = true.
  Proof.
    intros.
    (* [destruct] the current goal *)
    destruct n;
      (* then [simpl] each resulting subgoal *)
      simpl;
      (* and do [reflexivity] on each resulting subgoal *)
      reflexivity.
  Qed.

  (** Using [try] and [;] together, we can get rid of the repetition in
    the proof that was bothering us a little while ago. *)

  Theorem optimize_0plus_sound': forall a,
      aeval (optimize_0plus a) = aeval a.
  Proof.
    intros a.
    induction a;
      (* Most cases follow directly by the IH... *)
      try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
    (* ... but the remaining cases -- ANum and APlus --
       are different: *)
    - (* ANum *) reflexivity.
    - (* APlus *)
      destruct a1;
        (* Again, most cases follow directly by the IH: *)
        try (simpl; simpl in IHa1; rewrite IHa1;
             rewrite IHa2; reflexivity).
      (* The interesting case, on which the [try...]
       does nothing, is when [e1 = ANum n]. In this
       case, we have to destruct [n] (to see whether
       the optimization applies) and rewrite with the
       induction hypothesis. *)
      + (* a1 = ANum n *) destruct n;
          simpl; rewrite IHa2; reflexivity.   Qed.

  (** Coq experts often use this "[...; try... ]" idiom after a tactic
    like [induction] to take care of many similar cases all at once.
    Naturally, this practice has an analog in informal proofs.  For
    example, here is an informal proof of the optimization theorem
    that matches the structure of the formal one:

    _Theorem_: For all arithmetic expressions [a],

       aeval (optimize_0plus a) = aeval a.

    _Proof_: By induction on [a].  Most cases follow directly from the
    IH.  The remaining cases are as follows:

      - Suppose [a = ANum n] for some [n].  We must show

          aeval (optimize_0plus (ANum n)) = aeval (ANum n).

        This is immediate from the definition of [optimize_0plus].

      - Suppose [a = APlus a1 a2] for some [a1] and [a2].  We must
        show

          aeval (optimize_0plus (APlus a1 a2)) = aeval (APlus a1 a2).

        Consider the possible forms of [a1].  For most of them,
        [optimize_0plus] simply calls itself recursively for the
        subexpressions and rebuilds a new expression of the same form
        as [a1]; in these cases, the result follows directly from the
        IH.

        The interesting case is when [a1 = ANum n] for some [n].  If
        [n = 0], then

          optimize_0plus (APlus a1 a2) = optimize_0plus a2

        and the IH for [a2] is exactly what we need.  On the other
        hand, if [n = S n'] for some [n'], then again [optimize_0plus]
        simply calls itself recursively, and the result follows from
        the IH.  [] *)

  (** However, this proof can still be improved: the first case (for
    [a = ANum n]) is very trivial -- even more trivial than the cases
    that we said simply followed from the IH -- yet we have chosen to
    write it out in full.  It would be better and clearer to drop it
    and just say, at the top, "Most cases are either immediate or
    direct from the IH.  The only interesting case is the one for
    [APlus]..."  We can make the same improvement in our formal proof
    too.  Here's how it looks: *)

  Theorem optimize_0plus_sound'': forall a,
      aeval (optimize_0plus a) = aeval a.
  Proof.
    intros a.
    induction a;
      (* Most cases follow directly by the IH *)
      try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
      (* ... or are immediate by definition *)
      try reflexivity.
    (* The interesting case is when a = APlus a1 a2. *)
    - (* APlus *)
      destruct a1; try (simpl; simpl in IHa1; rewrite IHa1;
                        rewrite IHa2; reflexivity).
      + (* a1 = ANum n *) destruct n;
          simpl; rewrite IHa2; reflexivity. Qed.

  (* ----------------------------------------------------------------- *)
  (** *** The [;] Tactical (General Form) *)

  (** The [;] tactical also has a more general form than the simple
    [T;T'] we've seen above.  If [T], [T1], ..., [Tn] are tactics,
    then

      T; [T1 | T2 | ... | Tn]

    is a tactic that first performs [T] and then performs [T1] on the
    first subgoal generated by [T], performs [T2] on the second
    subgoal, etc.

    So [T;T'] is just special notation for the case when all of the
    [Ti]'s are the same tactic; i.e., [T;T'] is shorthand for:

      T; [T' | T' | ... | T']
   *)

  (* ----------------------------------------------------------------- *)
  (** *** The [repeat] Tactical *)

  (** The [repeat] tactical takes another tactic and keeps applying this
    tactic until it fails. Here is an example showing that [10] is in
    a long list using repeat. *)

  Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
  Proof.
    repeat (try (left; reflexivity); right).
  Qed.

  (** The tactic [repeat T] never fails: if the tactic [T] doesn't apply
    to the original goal, then repeat still succeeds without changing
    the original goal (i.e., it repeats zero times). *)

  Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
  Proof.
    repeat (left; reflexivity).
    repeat (right; try (left; reflexivity)).
  Qed.

  (** The tactic [repeat T] also does not have any upper bound on the
    number of times it applies [T].  If [T] is a tactic that always
    succeeds, then repeat [T] will loop forever (e.g., [repeat simpl]
    loops, since [simpl] always succeeds).  While evaluation in Coq's
    term language, Gallina, is guaranteed to terminate, tactic
    evaluation is not!  This does not affect Coq's logical
    consistency, however, since the job of [repeat] and other tactics
    is to guide Coq in constructing proofs; if the construction
    process diverges, this simply means that we have failed to
    construct a proof, not that we have constructed a wrong one. *)

  (* ================================================================= *)
  (** ** Defining New Tactic Notations *)

  (** Coq also provides several ways of "programming" tactic
scripts.

    - The [Tactic Notation] idiom illustrated below gives a handy way
      to define "shorthand tactics" that bundle several tactics into a
      single command.

    - For more sophisticated programming, Coq offers a built-in
      language called [Ltac] with primitives that can examine and
      modify the proof state.  The details are a bit too complicated
      to get into here (and it is generally agreed that [Ltac] is not
      the most beautiful part of Coq's design!), but they can be found
      in the reference manual and other books on Coq, and there are
      many examples of [Ltac] definitions in the Coq standard library
      that you can use as examples.

    - There is also an OCaml API, which can be used to build tactics
      that access Coq's internal structures at a lower level, but this
      is seldom worth the trouble for ordinary Coq users.

    The [Tactic Notation] mechanism is the easiest to come to grips
    with, and it offers plenty of power for many purposes.  Here's an
    example. *)

  Tactic Notation "simpl_and_try" tactic(c) :=
    simpl;
    try c.

  (** This defines a new tactical called [simpl_and_try] that takes one
    tactic [c] as an argument and is defined to be equivalent to the
    tactic [simpl; try c].  Now writing "[simpl_and_try reflexivity.]"
    in a proof will be the same as writing "[simpl; try
    reflexivity.]" *)

  (* ================================================================= *)
  (** ** The [omega] Tactic *)

  (** The [omega] tactic implements a decision procedure for a subset of
    first-order logic called _Presburger arithmetic_.  It is based on
    the Omega algorithm invented by William Pugh [Pugh 1991] (in Bib.v).

    If the goal is a universally quantified formula made out of

      - numeric constants, addition ([+] and [S]), subtraction ([-]
        and [pred]), and multiplication by constants (this is what
        makes it Presburger arithmetic),

      - equality ([=] and [<>]) and ordering ([<=]), and

      - the logical connectives [/\], [\/], [~], and [->],

    then invoking [omega] will either solve the goal or fail, meaning
    that the goal is actually false.  (If the goal is _not_ of this
    form, [omega] will also fail.) *)
  
  Example silly_presburger_example : forall m n o p,
      m + n <= n + o /\ o + 3 = p + 3 ->
      m <= p.
  Proof.
    intros. omega.
  Qed.

  (** (Note the [Require Import Coq.omega.Omega.] at the top of
    the file.) *)

  (* ================================================================= *)
  (** ** A Few More Handy Tactics *)

  (** Finally, here are some miscellaneous tactics that you may find
    convenient.

     - [clear H]: Delete hypothesis [H] from the context.

     - [subst x]: Find an assumption [x = e] or [e = x] in the
       context, replace [x] with [e] throughout the context and
       current goal, and clear the assumption.

     - [subst]: Substitute away _all_ assumptions of the form [x = e]
       or [e = x].

     - [rename... into...]: Change the name of a hypothesis in the
       proof context.  For example, if the context includes a variable
       named [x], then [rename x into y] will change all occurrences
       of [x] to [y].

     - [assumption]: Try to find a hypothesis [H] in the context that
       exactly matches the goal; if one is found, behave like [apply
       H].

     - [contradiction]: Try to find a hypothesis [H] in the current
       context that is logically equivalent to [False].  If one is
       found, solve the goal.

     - [constructor]: Try to find a constructor [c] (from some
       [Inductive] definition in the current environment) that can be
       applied to solve the current goal.  If one is found, behave
       like [apply c].

    We'll see examples as we go along. *)

  (* ################################################################# *)
  (** * Evaluation as a Relation *)

  (** We have presented [aeval] and [beval] as functions defined by
    [Fixpoint]s.  Another way to think about evaluation -- one that we
    will see is often more flexible -- is as a _relation_ between
    expressions and their values.  This leads naturally to [Inductive]
    definitions like the following one for arithmetic expressions... *)

  Module aevalR_first_try.

    Print aeval.

    (*Fixpoint aeval (a : aexp) : nat :=
      match a with
      | Any => 
      | ANum n => n
      | APlus a1 a2 => (aeval a1) + (aeval a2)
      | AMinus a1 a2  => (aeval a1) - (aeval a2)
      | AMult a1 a2 => (aeval a1) * (aeval a2)
      end.*)

    Inductive aevalR : aexp -> nat -> Prop :=
    | E_ANum  : forall (n: nat),
        aevalR (ANum n) n
    | E_APlus : forall (e1 e2: aexp) (n1 n2: nat),
        aevalR e1 n1 ->
        aevalR e2 n2 ->
        aevalR (APlus e1 e2) (n1 + n2)
    | E_AMinus: forall (e1 e2: aexp) (n1 n2: nat),
        aevalR e1 n1 ->
        aevalR e2 n2 ->
        aevalR (AMinus e1 e2) (n1 - n2)
    | E_AMult : forall (e1 e2: aexp) (n1 n2: nat),
        aevalR e1 n1 ->
        aevalR e2 n2 ->
        aevalR (AMult e1 e2) (n1 * n2).

    (** It will be convenient to have an infix notation for
    [aevalR].  We'll write [e \\ n] to mean that arithmetic expression
    [e] evaluates to value [n]. *)

    Notation "e '\\' n"
      := (aevalR e n)
           (at level 50, left associativity)
         : type_scope.

  End aevalR_first_try.

  (** In fact, Coq provides a way to use this notation in the
    definition of [aevalR] itself.  This reduces confusion by avoiding
    situations where we're working on a proof involving statements in
    the form [e \\ n] but we have to refer back to a definition
    written using the form [aevalR e n].

    We do this by first "reserving" the notation, then giving the
    definition together with a declaration of what the notation
    means. *)

  Reserved Notation "e '\\' n" (at level 50, left associativity).

  Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat),
      (ANum n) \\ n
  | E_APlus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult :  forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (AMult e1 e2) \\ (n1 * n2)

  where "e '\\' n" := (aevalR e n) : type_scope.

  (* ================================================================= *)
  (** ** Inference Rule Notation *)

  (** In informal discussions, it is convenient to write the rules for
    [aevalR] and similar relations in the more readable graphical form
    of _inference rules_, where the premises above the line justify
    the conclusion below the line (we have already seen them in the
    [IndProp] chapter). *)

  (** For example, the constructor [E_APlus]...

      | E_APlus : forall (e1 e2: aexp) (n1 n2: nat),
          aevalR e1 n1 ->
          aevalR e2 n2 ->
          aevalR (APlus e1 e2) (n1 + n2)

    ...would be written like this as an inference rule:

                               e1 \\ n1
                               e2 \\ n2
                         --------------------                         (E_APlus)
                         APlus e1 e2 \\ n1+n2
   *)

  (** Formally, there is nothing deep about inference rules: they
    are just implications.  You can read the rule name on the right as
    the name of the constructor and read each of the linebreaks
    between the premises above the line (as well as the line itself)
    as [->].  All the variables mentioned in the rule ([e1], [n1],
    etc.) are implicitly bound by universal quantifiers at the
    beginning. (Such variables are often called _metavariables_ to
    distinguish them from the variables of the language we are
    defining.  At the moment, our arithmetic expressions don't include
    variables, but we'll soon be adding them.)  The whole collection
    of rules is understood as being wrapped in an [Inductive]
    declaration.  In informal prose, this is either elided or else
    indicated by saying something like "Let [aevalR] be the smallest
    relation closed under the following rules...". *)

  (** For example, [\\] is the smallest relation closed under these
    rules:

                             -----------                               (E_ANum)
                             ANum n \\ n

                               e1 \\ n1
                               e2 \\ n2
                         --------------------                         (E_APlus)
                         APlus e1 e2 \\ n1+n2

                               e1 \\ n1
                               e2 \\ n2
                        ---------------------                        (E_AMinus)
                        AMinus e1 e2 \\ n1-n2

                               e1 \\ n1
                               e2 \\ n2
                         --------------------                         (E_AMult)
                         AMult e1 e2 \\ n1*n2
   *)

  (* ================================================================= *)
  (** ** Equivalence of the Definitions *)

  (** It is straightforward to prove that the relational and functional
    definitions of evaluation agree: *)

  Theorem aeval_iff_aevalR : forall a n,
      (a \\ n) <-> aeval a = n.
  Proof.
    split.
    - (* -> *)
      intros H.
      induction H; simpl.
      + (* E_ANum *)
        reflexivity.
      + (* E_APlus *)
        rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
      + (* E_AMinus *)
        rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
      + (* E_AMult *)
        rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
    - (* <- *)
      generalize dependent n.
      induction a;
        simpl; intros; subst.
      + (* ANum *)
        apply E_ANum.
      + (* APlus *)
        apply E_APlus.
        apply IHa1. reflexivity.
        apply IHa2. reflexivity.
      + (* AMinus *)
        apply E_AMinus.
        apply IHa1. reflexivity.
        apply IHa2. reflexivity.
      + (* AMult *)
        apply E_AMult.
        apply IHa1. reflexivity.
        apply IHa2. reflexivity.
  Qed.

  (** We can make the proof quite a bit shorter by making more
    use of tacticals. *)


End AExp.

(* ================================================================= *)
(** ** Computational vs. Relational Definitions *)

(** For the definitions of evaluation for arithmetic and boolean
    expressions, the choice of whether to use functional or relational
    definitions is mainly a matter of taste: either way works.

    However, there are circumstances where relational definitions of
    evaluation work much better than functional ones.  *)

Module aevalR_division.

  (** For example, suppose that we wanted to extend the arithmetic
    operations by considering also a division operation:*)

  Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp
  | ADiv : aexp -> aexp -> aexp.   (* <--- new *)

  (** Extending the definition of [aeval] to handle this new operation
    would not be straightforward (what should we return as the result
    of [ADiv (ANum 5) (ANum 0)]?).  But extending [aevalR] is
    straightforward. *)

  Reserved Notation "e '\\' n"
           (at level 50, left associativity).

  Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat),
      (ANum n) \\ n
  | E_APlus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (APlus a1 a2) \\ (n1 + n2)
  | E_AMinus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (AMinus a1 a2) \\ (n1 - n2)
  | E_AMult :  forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (AMult a1 a2) \\ (n1 * n2)
  | E_ADiv :  forall (a1 a2: aexp) (n1 n2 n3: nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (n2 > 0) ->
      (mult n2 n3 = n1) -> (ADiv a1 a2) \\ n3

  where "a '\\' n" := (aevalR a n) : type_scope.

End aevalR_division.

Module aevalR_extended.

  (** Suppose, instead, that we want to extend the arithmetic operations
    by a nondeterministic number generator [any] that, when evaluated,
    may yield any number.  (Note that this is not the same as making a
    _probabilistic_ choice among all possible numbers -- we're not
    specifying any particular distribution of results, but just saying
    what results are _possible_.) *)

  Reserved Notation "e '\\' n" (at level 50, left associativity).

  Inductive aexp : Type :=
  | AAny  : aexp                   (* <--- NEW *)
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

  (** Again, extending [aeval] would be tricky, since now evaluation is
    _not_ a deterministic function from expressions to numbers, but
    extending [aevalR] is no problem... *)

  Inductive aevalR : aexp -> nat -> Prop :=
  | E_Any : forall (n:nat),
      AAny \\ n                 (* <--- new *)
  | E_ANum : forall (n:nat),
      (ANum n) \\ n
  | E_APlus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (APlus a1 a2) \\ (n1 + n2)
  | E_AMinus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (AMinus a1 a2) \\ (n1 - n2)
  | E_AMult :  forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (AMult a1 a2) \\ (n1 * n2)

  where "a '\\' n" := (aevalR a n) : type_scope.

End aevalR_extended.

(** At this point you maybe wondering: which style should I use by
    default?  The examples above show that relational definitions are
    fundamentally more powerful than functional ones.  For situations
    like these, where the thing being defined is not easy to express
    as a function, or indeed where it is _not_ a function, there is no
    choice.  But what about when both styles are workable?

    One point in favor of relational definitions is that they can be
    more elegant and easier to understand.

    Another is that Coq automatically generates nice inversion and
    induction principles from [Inductive] definitions. *)

(** On the other hand, functional definitions can often be more
    convenient:
     - Functions are by definition deterministic and defined on all
       arguments; for a relation we have to show these properties
       explicitly if we need them.
     - With functions we can also take advantage of Coq's computation
       mechanism to simplify expressions during proofs.

    Furthermore, functions can be directly "extracted" to executable
    code in OCaml or Haskell. *)

(** Ultimately, the choice often comes down to either the specifics of
    a particular situation or simply a question of taste.  Indeed, in
    large Coq developments it is common to see a definition given in
    _both_ functional and relational styles, plus a lemma stating that
    the two coincide, allowing further proofs to switch from one point
    of view to the other at will.*)

(* ################################################################# *)
(** * Expressions With Variables *)

(** Let's turn our attention back to defining Imp.  The next thing we
    need to do is to enrich our arithmetic and boolean expressions
    with variables.  To keep things simple, we'll assume that all
    variables are global and that they only hold numbers. *)

(* ================================================================= *)
(** ** States *)

(** Since we'll want to look variables up to find out their current
    values, we'll reuse maps from the [Maps] chapter, with
    [string]s as the type of variables in Imp.

    A _machine state_ (or just _state_) represents the current values
    of _all_ variables at some point in the execution of a program. *)

(** For simplicity, we assume that the state is defined for
    _all_ variables, even though any given program is only going to
    mention a finite number of them.  The state captures all of the
    information stored in memory.  For Imp programs, because each
    variable stores a natural number, we can represent the state as a
    mapping from strings to [nat], and will use [0] as default value
    in the store. For more complex programming languages, the state
    might have more structure. *)

Require Export Coq.Strings.String.

Section Maps.

  Definition total_map (A:Type) := string -> A.

  (** Intuitively, a total map over an element type [A] is just a
    function that can be used to look up [string]s, yielding [A]s. *)

  (** The function [t_empty] yields an empty total map, given a default
    element; this map always returns the default element when applied
    to any string. *)

  Definition t_empty {A:Type} (v : A) : total_map A :=
    (fun _ => v).

  (** More interesting is the [update] function, which (as before) takes
    a map [m], a key [x], and a value [v] and returns a new map that
    takes [x] to [v] and takes every other key to whatever [m] does. *)

  Definition beq_string x y :=
    if string_dec x y then true else false.

  Definition t_update {A:Type} (m : total_map A)
             (x : string) (v : A) :=
    fun x' => if beq_string x x' then v else m x'.

  (** This definition is a nice example of higher-order programming:
    [t_update] takes a _function_ [m] and yields a new function
    [fun x' => ...] that behaves like the desired map. *)

End Maps.

(** Next, let's introduce some new notations to facilitate working
    with maps. *)

(** First, we will use the following notation to create an empty total map
    with a default value. *)
Notation "{ --> d }" := (t_empty d) (at level 0).

(** We then introduce a convenient notation for extending an existing
    map with some bindings. *)

(** (The definition of the notation is a bit ugly, but because the
    notation mechanism of Coq is not very well suited for recursive
    notations, it's the best we can do.) *)

Notation "m '&' { a --> x }" :=
  (t_update m a x) (at level 20).

Definition state := total_map nat.

(* ================================================================= *)
(** ** Syntax  *)

(** We can add variables to the arithmetic expressions we had before by
    simply adding one more constructor: *)

Inductive aexp : Type :=
| ANum : nat -> aexp
| AId : string -> aexp                (* <----- NEW *)
| APlus : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp.

(** Defining a few variable names as notational shorthands will make
    examples easier to read: *)

Definition W : string := "W"%string.
Definition X : string := "X"%string.
Definition Y : string := "Y"%string.
Definition Z : string := "Z"%string.

(** (This convention for naming program variables ([X], [Y],
    [Z]) clashes a bit with our earlier use of uppercase letters for
    types.  Since we're not using polymorphism heavily in the chapters
    developed to Imp, this overloading should not cause confusion.) *)

(** The definition of [bexp]s is unchanged (except that it now refers
    to the new [aexp]s): *)

Inductive bexp : Type :=
| BTrue : bexp
| BFalse : bexp
| BEq : aexp -> aexp -> bexp
| BLe : aexp -> aexp -> bexp
| BNot : bexp -> bexp
| BAnd : bexp -> bexp -> bexp.

(* ================================================================= *)
(** ** Notations *)
(** To make Imp programs easier to read and write, we introduce some
    notations and implicit coercions.

    You do not need to understand what these declarations do in detail
    to follow this chapter.  Briefly, though, the [Coercion]
    declaration in Coq stipulates that a function (or constructor) can
    be implicitly used by the type system to coerce a value of the
    input type to a value of the output type.  For instance, the
    coercion declaration for [AId] allows us to use plain strings when
    an [aexp] is expected; the string will implicitly be wrapped with
    [AId]. *)

(** The notations below are declared in specific _notation scopes_, in
    order to avoid conflicts with other interpretations of the same
    symbols.  Again, it is not necessary to understand the details. *)

Print AId.

Check (APlus (AId X) (ANum 0)).


Coercion AId : string >-> aexp.

Check (APlus X (ANum 0)).

Coercion ANum : nat >-> aexp.

Check (APlus X 0).

Definition bool_to_bexp (b: bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.

Delimit Scope aexp_scope with aexp.
Local Open Scope aexp_scope.

Delimit Scope bexp_scope with bexp.
Local Open Scope bexp_scope.

Infix ".+" := APlus (at level 40) : aexp_scope.
Infix ".-" := AMinus (at level 40) : aexp_scope.
Infix ".*" := AMult (at level 30) : aexp_scope.

Infix "<=?" := BLe : bexp_scope.
Infix "=?" := BEq : bexp_scope.
Infix "&&" := BAnd : bexp_scope.
Notation "'!' b" := (BNot b) (at level 60) : bexp_scope.


(** We can now write [3 + (X * 2)] instead  of [APlus 3 (AMult X 2)],
    and [true && !(X <= 4)] instead of [BAnd true (BNot (BLe X 4))]. *)

(* ================================================================= *)
(** ** Evaluation *)

(** The arith and boolean evaluators are extended to handle
    variables in the obvious way, taking a state as an extra
    argument: *)

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                (* <----- NEW *)
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2   => leb (aeval st a1) (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

(** We specialize our notation for total maps to the specific case of states,
    i.e. using [{ --> 0 }] as empty state. *)

Notation "{ a --> x }" :=
  (t_update { --> 0 } a x) (at level 0).
Notation "{ a --> x ; b --> y }" :=
  (t_update ({ a --> x }) b y) (at level 0).
Notation "{ a --> x ; b --> y ; c --> z }" :=
  (t_update ({ a --> x ; b --> y }) c z) (at level 0).
Notation "{ a --> x ; b --> y ; c --> z ; d --> t }" :=
  (t_update ({ a --> x ; b --> y ; c --> z }) d t) (at level 0).
Notation "{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u }" :=
  (t_update ({ a --> x ; b --> y ; c --> z ; d --> t }) e u) (at level 0).
Notation "{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v }" :=
  (t_update ({ a --> x ; b --> y ; c --> z ; d --> t ; e --> u }) f v) (at level 0).

Example aexp1 :
  aeval { X --> 5 } (3 .+ (X .* 2))
  = 13.
Proof. simpl. reflexivity. Qed.

Example bexp1 :
  beval { X --> 5 } (true && !(X <=? 4))
  = true.
Proof. reflexivity. Qed.

(* ################################################################# *)
(** * Commands *)

(** Now we are ready define the syntax and behavior of Imp
    _commands_ (sometimes called _statements_). *)

(* ================================================================= *)
(** ** Syntax *)

(** Informally, commands [c] are described by the following BNF
    grammar.  (We choose this slightly awkward concrete syntax for the
    sake of being able to define Imp syntax using Coq's Notation
    mechanism.  In particular, we use [IFB] to avoid conflicting with
    the [if] notation from the standard library.)

     c ::= SKIP | x ::= a | c ;; c | IFB b THEN c ELSE c FI
         | WHILE b DO c END
 *)
(**
    For example, here's factorial in Imp:

     Z ::= X;;
     Y ::= 1;;
     WHILE ! (Z =? 0) DO
       Y ::= Y .* Z;;
       Z ::= Z .- 1
     END

   When this command terminates, the variable [Y] will contain the
   factorial of the initial value of [X]. *)

(** Here is the formal definition of the abstract syntax of
    commands: *)

Inductive com : Type :=
| CSkip
| CAss (v: string) (e: aexp)
| CSeq (c1 c2: com)
| CIf (b: bexp) (c1 c2: com)
| CWhile (b: bexp) (c: com).

(** As for expressions, we can use a few [Notation] declarations to make
    reading and writing Imp programs more convenient. *)

Delimit Scope com_scope with com.
Notation "'SKIP'" :=
  CSkip : com_scope.
Notation "x '::=' a" :=
  (CAss x a) (at level 60) : com_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : com_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : com_scope.
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity) : com_scope.

(** The following declaration is needed to be able to use the
    notations in match patterns. *)
Open Scope com_scope.

(** For example, here is the factorial function again, written as a
    formal definition to Coq: *)

Definition fact_in_coq : com :=
  Z ::= X;;
  Y ::= 1;;
  WHILE ! (Z =? 0) DO
     Y ::= Y .* Z;;
     Z ::= Z .- 1
  END.

(* ================================================================= *)
(** ** More Examples *)

(** Assignment: *)

Definition plus2 : com :=
  X ::= X .+ 2.

Definition XtimesYinZ : com :=
  Z ::= X .* Y.

Definition subtract_slowly_body : com :=
  Z ::= Z .- 1 ;;
  X ::= X .- 1.

(* ----------------------------------------------------------------- *)
(** *** Loops *)

Definition subtract_slowly : com :=
  WHILE ! (X =? 0) DO
        subtract_slowly_body
  END.

Definition subtract_3_from_5_slowly : com :=
  X ::= 3 ;;
  Z ::= 5 ;;
  subtract_slowly.

(* ----------------------------------------------------------------- *)
(** *** An infinite loop: *)

Definition loop : com :=
  WHILE true DO
        SKIP
  END.

(* ################################################################# *)
(** * Evaluating Commands *)

(** Next we need to define what it means to evaluate an Imp command.
    The fact that [WHILE] loops don't necessarily terminate makes
    defining an evaluation function tricky... *)

(* ================================================================= *)
(** ** Evaluation as a Function (Failed Attempt) *)

(** Here's an attempt at defining an evaluation function for commands,
    omitting the [WHILE] case. *)

Fixpoint ceval_fun_no_while (st : state) (c : com)
  : state :=
  match c with
  | SKIP =>
    st
  | x ::= a1 =>
          st & { x --> (aeval st a1) }
  | c1 ;; c2 =>
          let st' := ceval_fun_no_while st c1 in
          ceval_fun_no_while st' c2
  | IFB b THEN c1 ELSE c2 FI =>
          if (beval st b)
          then ceval_fun_no_while st c1
          else ceval_fun_no_while st c2
  | WHILE b DO c END =>
    if (beval st b)
    then st
    else st
  end.

(** In a traditional functional programming language like OCaml or
    Haskell we could add the [WHILE] case as follows:

        Fixpoint ceval_fun (st : state) (c : com) : state :=
          match c with
            ...
            | WHILE b DO c END =>
                if (beval st b)
                  then ceval_fun st (c;; WHILE b DO c END)
                  else st
          end.

    Coq doesn't accept such a definition ("Error: Cannot guess
    decreasing argument of fix") because the function we want to
    define is not guaranteed to terminate. Indeed, it _doesn't_ always
    terminate: for example, the full version of the [ceval_fun]
    function applied to the [loop] program above would never
    terminate. Since Coq is not just a functional programming
    language but also a consistent logic, any potentially
    non-terminating function needs to be rejected. Here is
    an (invalid!) program showing what would go wrong if Coq
    allowed non-terminating recursive functions:

         Fixpoint loop_false (n : nat) : False := loop_false n.

    That is, propositions like [False] would become provable
    ([loop_false 0] would be a proof of [False]), which
    would be a disaster for Coq's logical consistency.

    Thus, because it doesn't terminate on all inputs,
    of [ceval_fun] cannot be written in Coq -- at least not without
    additional tricks and workarounds (see chapter [ImpCEvalFun]
    if you're curious about what those might be). *)

(* ================================================================= *)
(** ** Evaluation as a Relation *)

(** Here's a better way: define [ceval] as a _relation_ rather than a
    _function_ -- i.e., define it in [Prop] instead of [Type], as we
    did for [aevalR] above. *)

(** This is an important change.  Besides freeing us from awkward
    workarounds, it gives us a lot more flexibility in the definition.
    For example, if we add nondeterministic features like [any] to the
    language, we want the definition of evaluation to be
    nondeterministic -- i.e., not only will it not be total, it will
    not even be a function! *)

(** We'll use the notation [c / st \\ st'] for the [ceval] relation:
    [c / st \\ st'] means that executing program [c] in a starting
    state [st] results in an ending state [st'].  This can be
    pronounced "[c] takes state [st] to [st']". *)

(* ----------------------------------------------------------------- *)
(** *** Operational Semantics *)

(** Here is an informal definition of evaluation, presented as inference
    rules for readability:

                           ----------------                            (E_Skip)
                           SKIP / st \\ st

                           aeval st a1 = n
                   --------------------------------                     (E_Ass)
                   x := a1 / st \\ st & { x --> n }

                           c1 / st \\ st'
                          c2 / st' \\ st''
                         -------------------                            (E_Seq)
                         c1;;c2 / st \\ st''

                          beval st b1 = true
                           c1 / st \\ st'
                -------------------------------------                (E_IfTrue)
                IF b1 THEN c1 ELSE c2 FI / st \\ st'

                         beval st b1 = false
                           c2 / st \\ st'
                -------------------------------------               (E_IfFalse)
                IF b1 THEN c1 ELSE c2 FI / st \\ st'

                         beval st b = false
                    ------------------------------               (E_WhileFalse)
                    WHILE b DO c END / st \\ st

                          beval st b = true
                           c / st \\ st'
                  WHILE b DO c END / st' \\ st''
                  ---------------------------------               (E_WhileTrue)
                    WHILE b DO c END / st \\ st''
 *)

(** Here is the formal definition.  Make sure you understand
    how it corresponds to the inference rules. *)

Reserved Notation "c1 '/' st '\\' st'"
         (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
| E_Skip : forall st,
    SKIP / st \\ st
| E_Ass  : forall st a1 n x,
    aeval st a1 = n ->
    (x ::= a1) / st \\ st & { x --> n }
| E_Seq : forall c1 c2 st st' st'',
    c1 / st  \\ st' ->
    c2 / st' \\ st'' ->
    (c1 ;; c2) / st \\ st''
| E_IfTrue : forall st st' b c1 c2,
    beval st b = true ->
    c1 / st \\ st' ->
    (IFB b THEN c1 ELSE c2 FI) / st \\ st'
| E_IfFalse : forall st st' b c1 c2,
    beval st b = false ->
    c2 / st \\ st' ->
    (IFB b THEN c1 ELSE c2 FI) / st \\ st'
| E_WhileFalse : forall b st c,
    beval st b = false ->
    (WHILE b DO c END) / st \\ st
| E_WhileTrue : forall st st' st'' b c,
    beval st b = true ->
    c / st \\ st' ->
    (WHILE b DO c END) / st' \\ st'' ->
    (WHILE b DO c END) / st \\ st''

where "c1 '/' st '\\' st'" := (ceval c1 st st').

(** The cost of defining evaluation as a relation instead of a
    function is that we now need to construct _proofs_ that some
    program evaluates to some result state, rather than just letting
    Coq's computation mechanism do it for us. *)

Example ceval_example1:
  (X ::= 2;;
   IFB X <=? 1
   THEN Y ::= 3
   ELSE Z ::= 4
   FI)
    / { --> 0 } \\ { X --> 2 ; Z --> 4 }.
Proof.
  (* We must supply the intermediate state *)
  econstructor.
  - (* assignment command *)
    constructor. reflexivity.
  - (* if command *)
    apply E_IfFalse.
    + reflexivity.
    + constructor. reflexivity.
Qed.

(** **** Exercise: 2 stars (ceval_example2)  *)
Example ceval_example2:
  (X ::= 0;; Y ::= 1;; Z ::= 2) / { --> 0 } \\
                                { X --> 0 ; Y --> 1 ; Z --> 2 }.
Proof.
  econstructor.
  - constructor. reflexivity.
  - econstructor.
    + constructor. reflexivity.
    + constructor. reflexivity.
Qed.

(* ================================================================= *)
(** ** Determinism of Evaluation *)

(** Changing from a computational to a relational definition of
    evaluation is a good move because it frees us from the artificial
    requirement that evaluation should be a total function.  But it
    also raises a question: Is the second definition of evaluation
    really a partial function?  Or is it possible that, beginning from
    the same state [st], we could evaluate some command [c] in
    different ways to reach two different output states [st'] and
    [st'']?

    In fact, this cannot happen: [ceval] _is_ a partial function: *)

Theorem ceval_deterministic: forall c st st1 st2,
    c / st \\ st1  ->
    c / st \\ st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1;
    intros st2 E2; inversion E2; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Ass *) reflexivity.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1.
    { (* Proof of assertion *) apply IHE1_1; assumption. }
    subst st'0.
    apply IHE1_2. assumption.
  - (* E_IfTrue, b1 evaluates to true *)
    apply IHE1. assumption.
  - (* E_IfTrue,  b1 evaluates to false (contradiction) *)
    rewrite H in H5. inversion H5.
  - (* E_IfFalse, b1 evaluates to true (contradiction) *)
    rewrite H in H5. inversion H5.
  - (* E_IfFalse, b1 evaluates to false *)
    apply IHE1. assumption.
  - (* E_WhileFalse, b1 evaluates to false *)
    reflexivity.
  - (* E_WhileFalse, b1 evaluates to true (contradiction) *)
    rewrite H in H2. inversion H2.
  - (* E_WhileTrue, b1 evaluates to false (contradiction) *)
    rewrite H in H4. inversion H4.
  - (* E_WhileTrue, b1 evaluates to true *)
    assert (st' = st'0) as EQ1.
    { (* Proof of assertion *) apply IHE1_1; assumption. }
    subst st'0.
    apply IHE1_2. assumption.  Qed.

(* ################################################################# *)
(** * Reasoning About Imp Programs *)

(** We'll get deeper into systematic techniques for reasoning about
    Imp programs in _Programming Language Foundations_, but we can do
    quite a bit just working with the bare definitions.  This section
    explores some examples. *)

Lemma t_update_eq : forall A (m: total_map A) x v,
    (m & {x --> v}) x = v.
Proof.
  intros. unfold t_update.
  unfold beq_string.
  destruct (string_dec x x); try reflexivity.
  elim n. reflexivity.
Qed.

Theorem t_update_neq : forall (X:Type) v x1 x2
                         (m : total_map X),
  x1 <> x2 ->
  (m & {x1 --> v}) x2 = m x2.
Proof.
  intros. unfold t_update.
  unfold beq_string.
  destruct (string_dec x1 x2); try reflexivity.
  elim H. assumption.
Qed.

Theorem plus2_spec : forall st n st',
    st X = n ->
    plus2 / st \\ st' ->
    st' X = (n + 2)%nat.
Proof.
  intros st n st' HX Heval.

  (** Inverting [Heval] essentially forces Coq to expand one step of
      the [ceval] computation -- in this case revealing that [st']
      must be [st] extended with the new value of [X], since [plus2]
      is an assignment. *)

  inversion Heval. subst. simpl.
  apply t_update_eq.  Qed.
