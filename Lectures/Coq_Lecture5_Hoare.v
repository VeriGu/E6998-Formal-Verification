(** * Hoare: Hoare Logic *)
(* ################################################################# *)
(** * Acknowledgement *)

(** The materials are borrowed from the  _Software Foundations_ series.
    http://softwarefoundations.cis.upenn.edu
 *)

(**
    [coqc Coq_Lecture1_Basics Coq_Lecture2_Induction_List Coq_Lecture3_Tactics_Logic Coq_Lecture4_Program Coq_Lecture5_Hoare]
*)


Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Export Coq_Lecture4_Program.

Local Open Scope aexp_scope.
Local Open Scope bexp_scope.

(** In the final lecture, we began applying the mathematical tools
    developed in the first part of the course to studying the theory
    of a small programming language, Imp.

    - We defined a type of _abstract syntax trees_ for Imp, together
      with an _evaluation relation_ (a partial function on states)
      that specifies the _operational semantics_ of programs.

      The language we defined, though small, captures some of the key
      features of full-blown languages like C, C++, and Java,
      including the fundamental notion of mutable state and some
      common control structures.

    - We proved a number of _metatheoretic properties_ -- "meta" in
      the sense that they are properties of the language as a whole,
      rather than of particular programs in the language.  These
      included:

        - determinism of evaluation

        - equivalence of some different ways of writing down the
          definitions (e.g., functional and relational definitions of
          arithmetic expression evaluation)

        - guaranteed termination of certain classes of programs

        - correctness (in the sense of preserving meaning) of a number
          of useful program transformations

        - behavioral equivalence of programs (in the [Equiv]
          chapter). *)

(** If we stopped here, we would already have something useful: a set
    of tools for defining and discussing programming languages and
    language features that are mathematically precise, flexible, and
    easy to work with, applied to a set of key properties.  All of
    these properties are things that language designers, compiler
    writers, and users might care about knowing.  Indeed, many of them
    are so fundamental to our understanding of the programming
    languages we deal with that we might not consciously recognize
    them as "theorems."  But properties that seem intuitively obvious
    can sometimes be quite subtle (sometimes also subtly wrong!).

    We'll return to the theme of metatheoretic properties of whole
    languages later in this volume when we discuss _types_ and _type
    soundness_.  In this chapter, though, we turn to a different set
    of issues.

    Our goal is to carry out some simple examples of _program
    verification_ -- i.e., to use the precise definition of Imp to
    prove formally that particular programs satisfy particular
    specifications of their behavior.  We'll develop a reasoning
    system called _Floyd-Hoare Logic_ -- often shortened to just
    _Hoare Logic_ -- in which each of the syntactic constructs of Imp
    is equipped with a generic "proof rule" that can be used to reason
    compositionally about the correctness of programs involving this
    construct.

    Hoare Logic originated in the 1960s, and it continues to be the
    subject of intensive research right up to the present day.  It
    lies at the core of a multitude of tools that are being used in
    academia and industry to specify and verify real software systems.

    Hoare Logic combines two beautiful ideas: a natural way of writing
    down _specifications_ of programs, and a _compositional proof
    technique_ for proving that programs are correct with respect to
    such specifications -- where by "compositional" we mean that the
    structure of proofs directly mirrors the structure of the programs
    that they are about. *)

(** This chapter:
      - A systematic method for reasoning about the _functional
        correctness_ of programs in Imp

    Goals:
      - a natural notation for _program specifications_ and
      - a _compositional_ proof technique for program correctness

    Plan:
      - specifications (assertions / Hoare triples)
      - proof rules
      - loop invariants
      - decorated programs
      - examples *)

(* ################################################################# *)
(** * Assertions *)

(** To talk about specifications of programs, the first thing we
    need is a way of making _assertions_ about properties that hold at
    particular points during a program's execution -- i.e., claims
    about the current state of the memory when execution reaches that
    point.  Formally, an assertion is just a family of propositions
    indexed by a [state]. *)

Definition Assertion := state -> Prop.

(** **** Exercise: 1 star, optional (assertions)  *)
(** Paraphrase the following assertions in English (or your favorite
    natural language). *)

Module ExAssertions.
  Definition as1 : Assertion := fun st => st X = 3.
  Definition as2 : Assertion := fun st => st X <= st Y.
  Definition as3 : Assertion :=
    fun st => st X = 3 \/ st X <= st Y.
  Definition as4 : Assertion :=
    fun st => st Z * st Z <= st X /\
              ~ (((S (st Z)) * (S (st Z))) <= st X).
  Definition as5 : Assertion := fun st => True.
  Definition as6 : Assertion := fun st => False.
  (* FILL IN HERE *)
End ExAssertions.
(** [] *)

(** This way of writing assertions can be a little bit heavy,
    for two reasons: (1) every single assertion that we ever write is
    going to begin with [fun st => ]; and (2) this state [st] is the
    only one that we ever use to look up variables in assertions (we
    will never need to talk about two different memory states at the
    same time).  For discussing examples informally, we'll adopt some
    simplifying conventions: we'll drop the initial [fun st =>], and
    we'll write just [X] to mean [st X].  Thus, instead of writing *)
(**

      fun st => (st Z) * (st Z) <= m /\
                ~ ((S (st Z)) * (S (st Z)) <= m)

    we'll write just

      Z * Z <= m /\ ~((S Z) * (S Z) <= m).
 *)

(** This example also illustrates a convention that we'll use
    throughout the Hoare Logic chapters: in informal assertions,
    capital letters like [X], [Y], and [Z] are Imp variables, while
    lowercase letters like [x], [y], [m], and [n] are ordinary Coq
    variables (of type [nat]).  This is why, when translating from
    informal to formal, we replace [X] with [st X] but leave [m]
    alone. *)

(** Given two assertions [P] and [Q], we say that [P] _implies_ [Q],
    written [P ->> Q], if, whenever [P] holds in some state [st], [Q]
    also holds. *)

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" := (assert_implies P Q)
                        (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

(** (The [hoare_spec_scope] annotation here tells Coq that this
    notation is not global but is intended to be used in particular
    contexts.  The [Open Scope] tells Coq that this file is one such
    context.) *)

(** We'll also want the "iff" variant of implication between
    assertions: *)

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

(* ################################################################# *)
(** * Hoare Triples *)

(** Next, we need a way of making formal claims about the
    behavior of commands. *)

(** In general, the behavior of a command is to transform one state to
    another, so it is natural to express claims about commands in
    terms of assertions that are true before and after the command
    executes:

      - "If command [c] is started in a state satisfying assertion
        [P], and if [c] eventually terminates in some final state,
        then this final state will satisfy the assertion [Q]."

    Such a claim is called a _Hoare Triple_.  The assertion [P] is
    called the _precondition_ of [c], while [Q] is the
    _postcondition_.  *)

(** Formally: *)

Definition hoare_triple
           (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st',
    c / st \\ st' ->
    P st ->
    Q st'.


(** Since we'll be working a lot with Hoare triples, it's useful to
    have a compact notation:

       {{P}} c {{Q}}.
 *)
(** (The traditional notation is [{P} c {Q}], but single braces
    are already used for other things in Coq.)  *)

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

(** **** Exercise: 1 star, optional (triples)  *)
(** Paraphrase the following Hoare triples in English.

   1) {{True}} c {{X = 5}}

   2) {{X = m}} c {{X = m + 5)}}

   3) {{X <= Y}} c {{Y <= X}}

   4) {{True}} c {{False}}

   5) {{X = m}}
      c
      {{Y = real_fact m}}

   6) {{X = m}}
      c
      {{(Z * Z) <= m /\ ~ (((S Z) * (S Z)) <= m)}}
 *)

(** [] *)

(** **** Exercise: 1 star, optional (valid_triples)  *)
(** Which of the following Hoare triples are _valid_ -- i.e., the
    claimed relation between [P], [c], and [Q] is true?

   1) {{True}} X ::= 5 {{X = 5}}

   2) {{X = 2}} X ::= X + 1 {{X = 3}}

   3) {{True}} X ::= 5; Y ::= 0 {{X = 5}}

   4) {{X = 2 /\ X = 3}} X ::= 5 {{X = 0}}

   5) {{True}} SKIP {{False}}

   6) {{False}} SKIP {{True}}

   7) {{True}} WHILE true DO SKIP END {{False}}

   8) {{X = 0}}
        WHILE X = 0 DO X ::= X + 1 END
      {{X = 1}}

   9) {{X = 1}}
        WHILE !(X = 0) DO X ::= X + 1 END
      {{X = 100}}
 *)
(** [] *)

(** To get us warmed up for what's coming, here are two simple facts
    about Hoare triples.  (Make sure you understand what they mean.) *)

Theorem hoare_post_true : forall (P Q : Assertion) c,
    (forall st, Q st) ->
    {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  apply H.  Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
    (forall st, ~(P st)) ->
    {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  unfold not in H. apply H in HP.
  inversion HP.  Qed.

(* ################################################################# *)
(** * Proof Rules *)

(** The goal of Hoare logic is to provide a _compositional_
    method for proving the validity of specific Hoare triples.  That
    is, we want the structure of a program's correctness proof to
    mirror the structure of the program itself.  To this end, in the
    sections below, we'll introduce a rule for reasoning about each of
    the different syntactic forms of commands in Imp -- one for
    assignment, one for sequencing, one for conditionals, etc. -- plus
    a couple of "structural" rules for gluing things together.  We
    will then be able to prove programs correct using these proof
    rules, without ever unfolding the definition of [hoare_triple]. *)

(* ================================================================= *)
(** ** Assignment *)

(** The rule for assignment is the most fundamental of the Hoare logic
    proof rules.  Here's how it works.

    Consider this valid Hoare triple:

       {{ Y = 1 }}  X ::= Y  {{ X = 1 }}

    In English: if we start out in a state where the value of [Y]
    is [1] and we assign [Y] to [X], then we'll finish in a
    state where [X] is [1].
    That is, the property of being equal to [1] gets transferred 
    from [Y] to [X]. *)

(** Similarly, in

       {{ Y + Z = 1 }}  X ::= Y + Z  {{ X = 1 }}

    the same property (being equal to one) gets transferred to
    [X] from the expression [Y + Z] on the right-hand side of
    the assignment. *)

(** More generally, if [a] is _any_ arithmetic expression, then

       {{ a = 1 }}  X ::= a {{ X = 1 }}

    is a valid Hoare triple. *)

(** Even more generally, to conclude that an arbitrary assertion [Q]
    holds after [X ::= a], we need to assume that [Q] holds before [X
    ::= a], but _with all occurrences of_ [X] replaced by [a] in
    [Q]. This leads to the Hoare rule for assignment

      {{ Q [a / X] }} X ::= a {{ Q }}

    where "[Q [a / X]]" is pronounced "[Q] where [a] is substituted
    for [X]". *)

(** For example, these are valid applications of the assignment
    rule:

      {{ (X <= 5) [X + 1 / X]
         i.e., X + 1 <= 5 }}
      X ::= X + 1
      {{ X <= 5 }}

      {{ (X = 3) [3 / X]
         i.e., 3 = 3}}
      X ::= 3
      {{ X = 3 }}

      {{ (0 <= X /\ X <= 5) [3 / X]
         i.e., (0 <= 3 /\ 3 <= 5)}}
      X ::= 3
      {{ 0 <= X /\ X <= 5 }}
 *)

(** To formalize the rule, we must first formalize the idea of
    "substituting an expression for an Imp variable in an assertion",
    which we refer to as assertion substitution, or [assn_sub].  That
    is, given a proposition [P], a variable [X], and an arithmetic
    expression [a], we want to derive another proposition [P'] that is
    just the same as [P] except that [P'] should mention [a] wherever
    [P] mentions [X]. *)

(** Since [P] is an arbitrary Coq assertion, we can't directly "edit"
    its text.  However, we can achieve the same effect by evaluating
    [P] in an updated state: *)

Definition assn_sub X e P : Assertion :=
  fun (st : state) =>
    P (st & { X  --> aeval st e }).

Notation "P [ e // X ]" := (assn_sub X e P) (at level 10).

(** That is, [P [ e / X]] stands for an assertion -- let's call it [P'] -- 
    that is just like [P] except that, wherever [P] looks up the 
    variable [X] in the current state, [P'] instead uses the value 
    of the expression [e]. *)

(** To see how this works, let's calculate what happens with a couple
    of examples.  First, suppose [P'] is [(X <= 5) [ 3 / X]] -- that
    is, more formally, [P'] is the Coq expression

    fun st =>
      (fun st' => st' X <= 5)
      (st & { X --> aeval st 3 }),

    which simplifies to

    fun st =>
      (fun st' => st' X <= 5)
      (st & { X --> 3 })

    and further simplifies to

    fun st =>
      ((st & { X --> 3 }) X) <= 5

    and finally to

    fun st =>
      3 <= 5.

    That is, [P'] is the assertion that [3] is less than or equal to
    [5] (as expected). *)

(** For a more interesting example, suppose [P'] is [(X <= 5) [X + 1 / X]].
    Formally, [P'] is the Coq expression

    fun st =>
      (fun st' => st' X <= 5)
      (st & { X --> aeval st (X+1) }),

    which simplifies to

    fun st =>
      (st & { X --> aeval st (X+1) }) X <= 5

    and further simplifies to

    fun st =>
      (aeval st (X+1)) <= 5.

    That is, [P'] is the assertion that [X+1] is at most [5].
 *)

(** Now, using the concept of substitution, we can give the precise 
    proof rule for assignment:

      ------------------------------ (hoare_asgn)
      {{Q [e // X]}} X ::= e {{Q}}
 *)

(** We can prove formally that this rule is indeed valid. *)

Theorem hoare_asgn : forall Q X e,
    {{Q [ e // X]}} (X ::= e) {{Q}}.
Proof.
  unfold hoare_triple.
  intros.
  inversion H.
  subst.
  assumption.
Qed.

(** Here's a first formal proof using this rule. *)
Example assn_sub_example :
  {{(fun st => st X < 5) [X.+1 // X]}}
    (X ::= X.+1)
  {{fun st => st X < 5}}.
Proof.
  apply hoare_asgn.
Qed.

(** Of course, what would be even more helpful is to prove this
    simpler triple:

      {{X < 4}} (X ::= X+1) {{X < 5}}

   We will see how to do so in the next section. *)


(** **** Exercise: 2 stars, recommended (hoare_asgn_wrong)  *)
(** The assignment rule looks backward to almost everyone the first
    time they see it.  If it still seems puzzling, it may help
    to think a little about alternative "forward" rules.  Here is a
    seemingly natural one:

      ------------------------------ (hoare_asgn_wrong)
      {{ True }} X ::= a {{ X = a }}

    Give a counterexample showing that this rule is incorrect and
    argue informally that it is really a counterexample.  (Hint:
    The rule universally quantifies over the arithmetic expression
    [a], and your counterexample needs to exhibit an [a] for which
    the rule doesn't work.) *)

(* FILL IN HERE *)

(* ================================================================= *)
(** ** Consequence *)

(** Sometimes the preconditions and postconditions we get from the
    Hoare rules won't quite be the ones we want in the particular
    situation at hand -- they may be logically equivalent but have a
    different syntactic form that fails to unify with the goal we are
    trying to prove, or they actually may be logically weaker (for
    preconditions) or stronger (for postconditions) than what we need.

    For instance, while

      {{(X = 3) [3 / X]}} X ::= 3 {{X = 3}},

    follows directly from the assignment rule,

      {{True}} X ::= 3 {{X = 3}}

    does not.  This triple is valid, but it is not an instance of
    [hoare_asgn] because [True] and [(X = 3) [3 / X]] are not
    syntactically equal assertions.  However, they are logically
    _equivalent_, so if one triple is valid, then the other must
    certainly be as well.  We can capture this observation with the
    following rule:

                {{P'}} c {{Q}}
                  P <<->> P'
         -----------------------------   (hoare_consequence_pre_equiv)
                {{P}} c {{Q}}
 *)

(** Taking this line of thought a bit further, we can see that
    strengthening the precondition or weakening the postcondition of a
    valid triple always produces another valid triple. This
    observation is captured by two _Rules of Consequence_.

                {{P'}} c {{Q}}
                   P ->> P'
         -----------------------------   (hoare_consequence_pre)
                {{P}} c {{Q}}

                {{P}} c {{Q'}}
                  Q' ->> Q
         -----------------------------    (hoare_consequence_post)
                {{P}} c {{Q}}
 *)

(** Here are the formal versions: *)

Theorem hoare_weak_pre : forall (P P' Q : Assertion) c,
    {{P'}} c {{Q}} ->
    P ->> P' ->
    {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st').
  assumption. apply Himp. assumption. Qed.

Theorem hoare_weak_post : forall (P Q Q' : Assertion) c,
    {{P}} c {{Q'}} ->
    Q' ->> Q ->
    {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st st' Hc HP.
  apply Himp.
  apply (Hhoare st st').
  assumption. assumption. Qed.

(** For example, we can use the first consequence rule like this:

    {{ True }} ->>
    {{ 1 = 1 }}
    X ::= 1
    {{ X = 1 }}

    Or, formally... *)

Example hoare_asgn_example1 :
  {{fun st => True}} (X ::= 1) {{fun st => st X = 1}}.
Proof.
  eapply hoare_weak_pre.
  - apply hoare_asgn.
  - intros st HP.
    reflexivity.
Qed.

(** We can also use it to prove the example mentioned earlier.

		{{ X < 4 }} ->>
		{{ (X < 5)[X+1 // X] }}
    X ::= X + 1
	        {{ X < 5 }}

   Or, formally ... *)

Example assn_sub_example2 :
  {{(fun st => st X < 4)}}
    (X ::= X.+1)
    {{fun st => st X < 5}}.
Proof.
  eapply hoare_weak_pre.
  - apply hoare_asgn.
  - intros st HP.
    unfold assn_sub.
    unfold t_update.
    simpl.
    omega.
Qed.
  
(** Finally, for convenience in proofs, here is a combined rule of 
    consequence that allows us to vary both the precondition and the 
    postcondition in one go.

                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}
 *)

Theorem hoare_weak : forall (P P' Q Q' : Assertion) c,
    {{P'}} c {{Q'}} ->
    P ->> P' ->
    Q' ->> Q ->
    {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Hht HPP' HQ'Q.
  apply hoare_weak_pre with (P' := P').
  apply hoare_weak_post with (Q' := Q').
  assumption. assumption. assumption.  Qed.

(* ================================================================= *)
(** ** Skip *)

(** Since [SKIP] doesn't change the state, it preserves any
    assertion [P]:

      --------------------  (hoare_skip)
      {{ P }} SKIP {{ P }}
 *)

Theorem hoare_skip : forall P,
    {{P}} SKIP {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  assumption.  Qed.

(* ================================================================= *)
(** ** Sequencing *)

(** More interestingly, if the command [c1] takes any state where
    [P] holds to a state where [Q] holds, and if [c2] takes any
    state where [Q] holds to one where [R] holds, then doing [c1]
    followed by [c2] will take any state where [P] holds to one
    where [R] holds:

        {{ P }} c1 {{ Q }}
        {{ Q }} c2 {{ R }}
       ---------------------  (hoare_seq)
       {{ P }} c1;;c2 {{ R }}
 *)

Theorem hoare_seq : forall P Q R c1 c2,
    {{Q}} c2 {{R}} ->
    {{P}} c1 {{Q}} ->
    {{P}} c1;;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  apply (H1 st'0 st'); try assumption.
  apply (H2 st st'0); assumption. Qed.

(** Note that, in the formal rule [hoare_seq], the premises are
    given in backwards order ([c2] before [c1]).  This matches the
    natural flow of information in many of the situations where we'll
    use the rule, since the natural way to construct a Hoare-logic
    proof is to begin at the end of the program (with the final
    postcondition) and push postconditions backwards through commands
    until we reach the beginning. *)

(** Informally, a nice way of displaying a proof using the sequencing
    rule is as a "decorated program" where the intermediate assertion
    [Q] is written between [c1] and [c2]:

      {{ a = n }}
    X ::= a;;
      {{ X = n }}    <---- decoration for Q
    SKIP
      {{ X = n }}
 *)

(** Here's an example of a program involving both assignment and
    sequencing. *)

Example hoare_asgn_example3 : forall a n,
    {{fun st => aeval st a = n}}
      (X ::= a;; SKIP)
    {{fun st => st X = n}}.
Proof.
  intros.
  eapply hoare_seq.
  - apply hoare_skip.
  - eapply hoare_weak_pre.
    + apply hoare_asgn.
    + intros st HP.
      assumption.
Qed.

(** We typically use [hoare_seq] in conjunction with
    [hoare_consequence_pre] and the [eapply] tactic, as in this
    example. *)

(** **** Exercise: 2 stars, recommended (hoare_asgn_example4)  *)
(** Translate this "decorated program" into a formal proof:

                   {{ True }} ->>
                   {{ 1 = 1 }}
    X ::= 1;;
                   {{ X = 1 }} ->>
                   {{ X = 1 /\ 2 = 2 }}
    Y ::= 2
                   {{ X = 1 /\ Y = 2 }}

   (Note the use of "[->>]" decorations, each marking a use of 
   [hoare_consequence_pre].) *)

Example hoare_asgn_example4 :
  {{fun st => True}}
    (X ::= 1;; Y ::= 2)
    {{fun st => st X = 1 /\ st Y = 2}}.
Proof.
  eapply hoare_seq.
  - apply hoare_asgn.
  - eapply hoare_weak_pre.
    + apply hoare_asgn.
    + intros st HP.
      split; reflexivity.
Qed.

(* ================================================================= *)
(** ** Conditionals *)

(** What sort of rule do we want for reasoning about conditional
    commands?

    Certainly, if the same assertion [Q] holds after executing 
    either of the branches, then it holds after the whole conditional.  
    So we might be tempted to write:

              {{P}} c1 {{Q}}
              {{P}} c2 {{Q}}
      --------------------------------
      {{P}} IFB b THEN c1 ELSE c2 {{Q}}
 *)

(** However, this is rather weak. For example, using this rule,
   we cannot show 

     {{ True }}
     IFB X = 0
     THEN Y ::= 2
     ELSE Y ::= X + 1
     FI
     {{ X <= Y }}

   since the rule tells us nothing about the state in which the
   assignments take place in the "then" and "else" branches. *)

(** Fortunately, we can say something more precise.  In the
    "then" branch, we know that the boolean expression [b] evaluates to
    [true], and in the "else" branch, we know it evaluates to [false].
    Making this information available in the premises of the rule gives
    us more information to work with when reasoning about the behavior
    of [c1] and [c2] (i.e., the reasons why they establish the
    postcondition [Q]). *)
(**

              {{P /\  b}} c1 {{Q}}
              {{P /\ ~b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} IFB b THEN c1 ELSE c2 FI {{Q}}
 *)

(** To interpret this rule formally, we need to do a little work.
    Strictly speaking, the assertion we've written, [P /\ b], is the
    conjunction of an assertion and a boolean expression -- i.e., it
    doesn't typecheck.  To fix this, we need a way of formally
    "lifting" any bexp [b] to an assertion.  We'll write [bassn b] for
    the assertion "the boolean expression [b] evaluates to [true] (in
    the given state)." *)

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

(** A couple of useful facts about [bassn]: *)

Lemma bexp_eval_true : forall b st,
    beval st b = true -> (bassn b) st.
Proof.
  intros b st Hbe.
  unfold bassn. assumption.  Qed.

Lemma bexp_eval_false : forall b st,
    beval st b = false -> ~ ((bassn b) st).
Proof.
  intros b st Hbe contra.
  unfold bassn in contra.
  rewrite -> contra in Hbe. inversion Hbe.  Qed.

(** Now we can formalize the Hoare proof rule for conditionals
    and prove it correct. *)

Theorem hoare_if : forall P Q b c1 c2,
    {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
    {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
    {{P}} (IFB b THEN c1 ELSE c2 FI) {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst.
  - (* b is true *) 
    apply (HTrue st st').
    assumption.
    split. assumption.
    apply bexp_eval_true. assumption.
  - (* b is false *)
    apply (HFalse st st').
    assumption.
    split. assumption.
    apply bexp_eval_false. assumption. Qed.

(* ----------------------------------------------------------------- *)
(** *** Example *)

(** Here is a formal proof that the program we used to motivate the
    rule satisfies the specification we gave. 
Hint: beq_nat_true, omega
*)

Example if_example :
  {{fun st => True}}
    IFB X =? 0
    THEN Y ::= 2
    ELSE Y ::= X .+ 1
    FI
    {{fun st => st X <= st Y}}.
Proof.
  apply hoare_if.
  - (* Then *)
    eapply hoare_weak_pre. apply hoare_asgn.
    unfold bassn, assn_sub, t_update, assert_implies.
    simpl. intros st [_ H].
    apply beq_nat_true in H.
    rewrite H. omega.
  - (* Else *)
    eapply hoare_weak_pre. apply hoare_asgn.
    unfold assn_sub, t_update, assert_implies.
    simpl; intros st _. omega.
Qed.

(* ================================================================= *)
(** ** Loops *)

(** Finally, we need a rule for reasoning about while loops. *)

(** Suppose we have a loop

      WHILE b DO c END

    and we want to find a pre-condition [P] and a post-condition
    [Q] such that

      {{P}} WHILE b DO c END {{Q}}

    is a valid triple. *)

(** First of all, let's think about the case where [b] is false at the
    beginning -- i.e., let's assume that the loop body never executes
    at all.  In this case, the loop behaves like [SKIP], so we might
    be tempted to write: *)

(**

      {{P}} WHILE b DO c END {{P}}.
 *)

(** But, as we remarked above for the conditional, we know a
    little more at the end -- not just [P], but also the fact
    that [b] is false in the current state.  So we can enrich the
    postcondition a little: *)
(**

      {{P}} WHILE b DO c END {{P /\ ~b}}
 *)

(** What about the case where the loop body _does_ get executed?
    In order to ensure that [P] holds when the loop finally
    exits, we certainly need to make sure that the command [c]
    guarantees that [P] holds whenever [c] is finished.
    Moreover, since [P] holds at the beginning of the first
    execution of [c], and since each execution of [c]
    re-establishes [P] when it finishes, we can always assume
    that [P] holds at the beginning of [c].  This leads us to the
    following rule: *)
(**

                   {{P}} c {{P}}
        -----------------------------------
        {{P}} WHILE b DO c END {{P /\ ~b}}
 *)
(** This is almost the rule we want, but again it can be improved a
    little: at the beginning of the loop body, we know not only that
    [P] holds, but also that the guard [b] is true in the current
    state. *)

(** This gives us a little more information to use in
    reasoning about [c] (showing that it establishes the invariant by
    the time it finishes).  *)
(** This gives us the final version of the rule: *)
(**

               {{P /\ b}} c {{P}}
        -----------------------------------  (hoare_while)
        {{P}} WHILE b DO c END {{P /\ ~b}}

    The proposition [P] is called an _invariant_ of the loop.
 *)

Theorem hoare_while : forall P b c,
    {{fun st => P st /\ bassn b st}} c {{P}} ->
    {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof.
  intros P b c Hhoare st st' He HP.
  (* Like we've seen before, we need to reason by induction
     on [He], because, in the "keep looping" case, its hypotheses
     talk about the whole loop instead of just [c]. *)
  remember (WHILE b DO c END) as wcom eqn:Heqwcom.
  induction He;
    try (inversion Heqwcom); subst; clear Heqwcom.
  - (* E_WhileFalse *)  
    split. assumption. apply bexp_eval_false. assumption.
  - (* E_WhileTrue *)
    apply IHHe2. reflexivity.
    apply (Hhoare st st'). assumption.
    split. assumption. apply bexp_eval_true. assumption.
Qed.

(** One subtlety in the terminology is that calling some assertion [P]
    a "loop invariant" doesn't just mean that it is preserved by the
    body of the loop in question (i.e., [{{P}} c {{P}}], where [c] is
    the loop body), but rather that [P] _together with the fact that
    the loop's guard is true_ is a sufficient precondition for [c] to
    ensure [P] as a postcondition.

    This is a slightly (but importantly) weaker requirement.  For
    example, if [P] is the assertion [X = 0], then [P] _is_ an
    invariant of the loop

    WHILE X = 2 DO X := 1 END

    although it is clearly _not_ preserved by the body of the
    loop.

    Hint: leb, leb_complete, leb_iff_conv
*)


(** Hint:
    bassn, assert_implies, assn_sub, t_update, beval, aeval 
    not_true_iff_false
    not_false_iff_true
    negb_true_iff
    negb_false_iff
    beq_nat_true_iff
    beq_nat_false_iff
    leb_iff
    leb_iff_conv
 *)

Ltac simplb :=
  repeat match goal with
         | [H0: leb _ _ = true |- _ ] =>
           rewrite leb_iff in H0
         | [H0: leb _ _ = false |- _ ] =>
           rewrite leb_iff_conv in H0
         | [H0: _ <> true |- _ ] =>
           rewrite not_true_iff_false in H0
         | [H0: _ <> false |- _ ] =>
           rewrite not_false_iff_true in H0
         | [H0: beq_nat _ _ = true |- _ ] =>
           rewrite beq_nat_true_iff in H0
         | [H0: beq_nat _ _ = false |- _ ] =>
           rewrite beq_nat_false_iff in H0
         | [H0: negb _ = true |- _] =>
           rewrite negb_true_iff in H0
         | [H0: negb _ = false |- _] =>
           rewrite negb_false_iff in H0
         end.

Ltac my_simpl :=
  unfold assert_implies, assn_sub, bassn, beval, aeval, t_update in *;
  simpl in *; intros;
  repeat match goal with
         | [ H0: _ /\ _ |- _ ] => destruct H0
         end;
  simplb; eauto; try omega; try congruence.

Ltac hoare :=
  intros;
  repeat match goal with
         | [|- {{ _ }} ?C {{ _ }}] =>
           match C with
           | WHILE _ DO _ END =>
             eapply hoare_weak_post; [eapply hoare_while | my_simpl]
           | _ ::= _ =>
                   try (apply hoare_asgn);
                   match goal with
                   | [|- {{_}} _ ::= _ {{ _ }}] =>
                        eapply hoare_weak_pre; [eapply hoare_asgn | my_simpl]
                   end
           | IFB _ THEN _ ELSE _ FI => eapply hoare_if
           | SKIP => eapply hoare_weak_pre; [eapply hoare_skip| my_simpl]
           | _ ;; _ => eapply hoare_seq
           end
         end.

Example while_example :
  {{fun st => st X <= 3}}
    WHILE X <=? 2
    DO X ::= X .+ 1 END
  {{fun st => st X >= 3}}.
Proof.
  hoare.
Qed.

Example while_example1 :
  {{fun st => st X = 5}}
    WHILE X <=? 2
    DO X ::= X .+ 1 END
  {{fun st => st X >= 3}}.
Proof.
  hoare.
Qed.

Example if_example1:
  {{fun st => True}}
    IFB X =? 0
    THEN Y ::= 2
    ELSE Y ::= X .+ 1
    FI
  {{fun st => st X <= st Y}}.
Proof.
  hoare.
Qed.

Example if_minus_plus_dec1:
  {{fun st => True}}
  IFB X <=? Y  THEN
    Z ::= Y .- X
  ELSE
    Y ::= X .+ Z
  FI
  {{fun st => st Y = st X + st Z}}.
Proof.
  hoare.
Qed.

Theorem always_loop_hoare : forall P Q,
    {{P}} WHILE true DO SKIP END {{Q}}.
Proof.
  hoare.
Qed.

Example swap_dec1:
  forall m n,
  {{ fun st => st X = m /\ st Y = n}}
  X ::= X .+ Y ;;
  Y ::= X .- Y ;;
  X ::= X .- Y
  {{ fun st => st X = n /\ st Y = m}}.
Proof.
  hoare.
Qed.

Local Opaque minus.

Example if_example2:
  {{fun st => True}}
    IFB X <=? 5
    THEN Y ::= 11 .- X
    ELSE Y ::= X
    FI
  {{fun st => st Y > 5}}.
Proof.
  hoare.
Qed.


(*
// { x0 = x+z }             (PRE)
while z != 0 {
  // { x0 = x+z ∧ z != 0}   (WHILE)
  // { x0 = (x+1)+(z-1) }   (WEAK)
  x := x + 1;
  // { x0 = x+(z-1) }       (ASG)
  z := z - 1;
  // { x0 = x+z }           (ASG)
}
// { x0 = x+z ∧ z = 0 }     (WHILE)
 *)

Example while_example2:
  forall x0,
  {{fun st => x0 = st X + st Y}}
    WHILE ! (Y =? 0)
    DO X ::= X .+ 1 ;; Y ::= Y .- 1
    END
  {{fun st => x0 = st X + st Y /\ st Y = 0}}.
Proof.
  hoare.
Qed.

(*
// Proof.
// { x > 0 }                (PRE)
// { 1 = 0! }               (WEAK)
y := 1;
// { y = 0! }               (ASG)
z := 0;
// { y = z! }               (ASG)
while (z != x) {
  // { y = z! ∧ z != x}     (WHILE)
  // { y * (z+1) = (z+1)!}  (WEAK)
  z := z + 1;
  // { y * z = z! }         (ASG)
  y := y * z;
  // { y = z! }             (ASG)
}
// { y = z! ∧ ~(z != x)}    (WHILE)
// { y = x!} 
 *)

Print fact.

Example fact_example:
  {{fun st => st X > 0}}
    Y ::= 1 ;;
    Z ::= 0 ;;
    WHILE ! (Z =? X)
    DO Z ::= Z .+ 1 ;; Y ::= Y .* Z
    END
  {{fun st => st Y = fact (st X)}}.
Proof.
  hoare. 
  - instantiate (1:= fun st => st Y = fact (st Z)).
    my_simpl.
    replace (st Z + 1)%nat with (S (st Z)) by omega.
    rewrite mult_comm.
    simpl. rewrite <- H. trivial.
  - my_simpl.
  - my_simpl.
Qed.

(** Of course, this result is not surprising if we remember that
    the definition of [hoare_triple] asserts that the postcondition
    must hold _only_ when the command terminates.  If the command
    doesn't terminate, we can prove anything we like about the
    post-condition. *)

(** Hoare rules that only talk about what happens when commands
    terminate (without proving that they do) are often said to
    describe a logic of "partial" correctness.  It is also possible to
    give Hoare rules for "total" correctness, which build in the fact
    that the commands terminate. However, in this course we will only
    talk about partial correctness. *)

(* ################################################################# *)
(** * Summary *)

(** So far, we've introduced Hoare Logic as a tool for reasoning about
    Imp programs. The rules of Hoare Logic are:

             ------------------------------ (hoare_asgn)
             {{Q [X |-> a]}} X::=a {{Q}}

             --------------------  (hoare_skip)
             {{ P }} SKIP {{ P }}

               {{ P }} c1 {{ Q }}
               {{ Q }} c2 {{ R }}
              ---------------------  (hoare_seq)
              {{ P }} c1;;c2 {{ R }}

              {{P /\  b}} c1 {{Q}}
              {{P /\ ~b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} IFB b THEN c1 ELSE c2 FI {{Q}}

               {{P /\ b}} c {{P}}
        -----------------------------------  (hoare_while)
        {{P}} WHILE b DO c END {{P /\ ~b}}

                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}

    In the next chapter, we'll see how these rules are used to prove
    that programs satisfy specifications of their behavior. *)


(* ################################################################# *)
(** * Decorated Programs *)

(** The beauty of Hoare Logic is that it is _compositional_: the
    structure of proofs exactly follows the structure of programs.

    This suggests that we can record the essential ideas of a
    proof (informally, and leaving out some low-level calculational
    details) by "decorating" a program with appropriate assertions on
    each of its commands.

    Such a _decorated program_ carries within it an argument for its
    own correctness. *)

(** For example, consider the program: *)
(**

    X ::= m;; 
    Z ::= p; 
    WHILE !(X = 0) DO 
      Z ::= Z - 1;; 
      X ::= X - 1 
    END

   (Note the _parameters_ [m] and [p], which stand for
   fixed-but-arbitrary numbers.  Formally, they are simply Coq
   variables of type [nat].)
*)
(** Here is one possible specification for this program: *)
(**

      {{ True }} 
    X ::= m;; 
    Z ::= p; 
    WHILE !(X = 0) DO 
      Z ::= Z - 1;;
      X ::= X - 1 
    END 
      {{ Z = p - m }}
*)
(** Here is a decorated version of the program, embodying a
    proof of this specification: *)
(**

      {{ True }} ->> 
      {{ m = m }} 
    X ::= m;; 
      {{ X = m }} ->> 
      {{ X = m /\ p = p }} 
    Z ::= p; 
      {{ X = m /\ Z = p }} ->> 
      {{ Z - X = p - m }}
    WHILE !(X = 0) DO 
        {{ Z - X = p - m /\ X <> 0 }} ->> 
        {{ (Z - 1) - (X - 1) = p - m }} 
      Z ::= Z - 1;; 
        {{ Z - (X - 1) = p - m }}
      X ::= X - 1 
        {{ Z - X = p - m }} 
    END 
      {{ Z - X = p - m /\ ~ (X <> 0) }} ->> {{ Z = p - m }}
*)

(** Concretely, a decorated program consists of the program text
    interleaved with assertions (either a single assertion or possibly
    two assertions separated by an implication). *)

(** To check that a decorated program represents a valid proof, we
    check that each individual command is _locally consistent_ with
    its nearby assertions in the following sense: *)

(** - [SKIP] is locally consistent if its precondition and
      postcondition are the same:

          {{ P }} SKIP {{ P }}
*)

(** - The sequential composition of [c1] and [c2] is locally
      consistent (with respect to assertions [P] and [R]) if [c1] is
      locally consistent (with respect to [P] and [Q]) and [c2] is
      locally consistent (with respect to [Q] and [R]):

          {{ P }} c1;; {{ Q }} c2 {{ R }}
*)

(** - An assignment is locally consistent if its precondition is the
      appropriate substitution of its postcondition:

          {{ P [a // X] }}
          X ::= a
          {{ P }}
*)

(** - A conditional is locally consistent (with respect to assertions
      [P] and [Q]) if the assertions at the top of its "then" and
      "else" branches are exactly [P /\ b] and [P /\ ~b] and if its
      "then" branch is locally consistent (with respect to [P /\ b]
      and [Q]) and its "else" branch is locally consistent (with
      respect to [P /\ ~b] and [Q]):

          {{ P }}
          IFB b THEN
            {{ P /\ b }}
            c1
            {{ Q }}
          ELSE
            {{ P /\ ~b }}
            c2
            {{ Q }}
          FI
          {{ Q }}
*)

(** - A while loop with precondition [P] is locally consistent if its
      postcondition is [P /\ ~b], if the pre- and postconditions of
      its body are exactly [P /\ b] and [P], and if its body is
      locally consistent:

          {{ P }}
          WHILE b DO
            {{ P /\ b }}
            c1
            {{ P }}
          END
          {{ P /\ ~b }}
*)

(** - A pair of assertions separated by [->>] is locally consistent if
      the first implies the second:

          {{ P }} ->> 
          {{ P' }}

      This corresponds to the application of [hoare_consequence], and it
      is the _only_ place in a decorated program where checking whether
      decorations are correct is not fully mechanical and syntactic,
      but rather may involve logical and/or arithmetic reasoning. *)

(** These local consistency conditions essentially describe a
    procedure for _verifying_ the correctness of a given proof.
    This verification involves checking that every single command is 
    locally consistent with the accompanying assertions.

    If we are instead interested in _finding_ a proof for a given
    specification, we need to discover the right assertions.  This can
    be done in an almost mechanical way, with the exception of finding
    loop invariants, which is the subject of the next section.  In the
    remainder of this section we explain in detail how to construct
    decorations for several simple programs that don't involve
    non-trivial loop invariants. *)

(* ================================================================= *)
(** ** Example: Swapping Using Addition and Subtraction *)

(** Here is a program that swaps the values of two variables using
    addition and subtraction (instead of by assigning to a temporary
    variable).

       X ::= X + Y;; 
       Y ::= X - Y;; 
       X ::= X - Y

    We can prove using decorations that this program is correct --
    i.e., it always swaps the values of variables [X] and [Y]. 
*)
(**

    (1)     {{ X = m /\ Y = n }} ->>
    (2)     {{ (X + Y) - ((X + Y) - Y) = n /\ (X + Y) - Y = m }}
           X ::= X + Y;;
    (3)     {{ X - (X - Y) = n /\ X - Y = m }}
           Y ::= X - Y;;
    (4)     {{ X - Y = n /\ Y = m }}
           X ::= X - Y
    (5)     {{ X = n /\ Y = m }}

    These decorations can be constructed as follows:
      - We begin with the undecorated program (the unnumbered lines).
      - We add the specification -- i.e., the outer precondition (1)
        and postcondition (5). In the precondition, we use parameters
        [m] and [n] to remember the initial values of variables [X]
        and [Y] so that we can refer to them in the postcondition (5).
      - We work backwards, mechanically, starting from (5) and
        proceeding until we get to (2). At each step, we obtain the
        precondition of the assignment from its postcondition by
        substituting the assigned variable with the right-hand-side of
        the assignment. For instance, we obtain (4) by substituting
        [X] with [X - Y] in (5), and we obtain (3) by substituting [Y] 
        with [X - Y] in (4).
      - Finally, we verify that (1) logically implies (2) -- i.e.,
        that the step from (1) to (2) is a valid use of the law of
        consequence. For this we substitute [X] by [m] and [Y] by [n]
        and calculate as follows:

            (m + n) - ((m + n) - n) = n /\ (m + n) - n = m 
            (m + n) - m = n /\ m = m 
            n = n /\ m = m

    Note that, since we are working with natural numbers rather than
    fixed-width machine integers, we don't need to worry about the
    possibility of arithmetic overflow anywhere in this argument.
    This makes life quite a bit simpler! *)

(* ================================================================= *)
(** ** Example: Simple Conditionals *)

(** Here is a simple decorated program using conditionals:

      (1)     {{True}}
            IFB X <= Y THEN
      (2)       {{True /\ X <= Y}} ->>
      (3)       {{(Y - X) + X = Y \/ (Y - X) + Y = X}}
              Z ::= Y - X
      (4)       {{Z + X = Y \/ Z + Y = X}}
            ELSE
      (5)       {{True /\ ~(X <= Y) }} ->>
      (6)       {{(X - Y) + X = Y \/ (X - Y) + Y = X}}
              Z ::= X - Y
      (7)       {{Z + X = Y \/ Z + Y = X}}
            FI
      (8)     {{Z + X = Y \/ Z + Y = X}}

These decorations were constructed as follows:
  - We start with the outer precondition (1) and postcondition (8).
  - We follow the format dictated by the [hoare_if] rule and copy the
    postcondition (8) to (4) and (7). We conjoin the precondition (1)
    with the guard of the conditional to obtain (2). We conjoin (1)
    with the negated guard of the conditional to obtain (5).
  - In order to use the assignment rule and obtain (3), we substitute
    [Z] by [Y - X] in (4). To obtain (6) we substitute [Z] by [X - Y]
    in (7).
  - Finally, we verify that (2) implies (3) and (5) implies (6). Both
    of these implications crucially depend on the ordering of [X] and
    [Y] obtained from the guard. For instance, knowing that [X <= Y]
    ensures that subtracting [X] from [Y] and then adding back [X]
    produces [Y], as required by the first disjunct of (3). Similarly,
    knowing that [~ (X <= Y)] ensures that subtracting [Y] from [X]
    and then adding back [Y] produces [X], as needed by the second
    disjunct of (6). Note that [n - m + m = n] does _not_ hold for
    arbitrary natural numbers [n] and [m] (for example, [3 - 5 + 5 =
    5]). *)

(* ################################################################# *)
(** * Formal Decorated Programs *)

(** Our informal conventions for decorated programs amount to a
    way of displaying Hoare triples, in which commands are annotated
    with enough embedded assertions that checking the validity of a
    triple is reduced to simple logical and algebraic calculations
    showing that some assertions imply others.  In this section, we
    show that this informal presentation style can actually be made
    completely formal and indeed that checking the validity of
    decorated programs can mostly be automated.  *)

(* ================================================================= *)
(** ** Syntax *)

(** The first thing we need to do is to formalize a variant of the
    syntax of commands with embedded assertions.  We call the new
    commands _decorated commands_, or [dcom]s. *)

(** We don't want both preconditions and postconditions on each
    command, because a sequence of two commands would contain
    redundant decorations, the postcondition of the first likely
    being the same as the precondition of the second. Instead,
    decorations are added corresponding to each postcondition.
    A separate type, [decorated], is used to add the precondition
    for the entire program. **)

Inductive dcom : Type :=
| DCSkip (Q:  Assertion)
| DCSeq (d1 d2:  dcom)
| DCAsgn (X: string) (e: aexp) (Q: Assertion)
| DCIf (b: bexp) (P1: Assertion) (d1: dcom) (P2: Assertion) (d2: dcom) (Q: Assertion)
| DCWhile (b: bexp) (Pbody: Assertion) (body: dcom) (Q: Assertion)
| DCPre  (P: Assertion) (d: dcom)
| DCPost (d: dcom) (Q: Assertion).

Inductive decorated : Type :=
  | Decorated : Assertion -> dcom -> decorated.

Notation "'SKIP' {{ P }}"
      := (DCSkip P)
      (at level 10) : dcom_scope.
Notation "l '::=' a {{ P }}"
      := (DCAsgn l a P)
      (at level 60, a at next level) : dcom_scope.
Notation "'WHILE' b 'DO' {{ Pbody }} d 'END' {{ Ppost }}"
      := (DCWhile b Pbody d Ppost)
      (at level 80, right associativity) : dcom_scope.
Notation "'IFB' b 'THEN' {{ P }} d 'ELSE' {{ P' }} d' 'FI' {{ Q }}"
      := (DCIf b P d P' d' Q)
      (at level 80, right associativity)  : dcom_scope.
Notation "'->>' {{ P }} d"
      := (DCPre P d)
      (at level 90, right associativity)  : dcom_scope.
Notation "d '->>' {{ P }}"
      := (DCPost d P)
      (at level 80, right associativity)  : dcom_scope.
Notation " d ;; d' "
      := (DCSeq d d')
      (at level 80, right associativity)  : dcom_scope.
Notation "{{ P }} d"
      := (Decorated P d)
      (at level 90)  : dcom_scope.

Delimit Scope dcom_scope with dcom.
Open Scope dcom_scope.
(** To avoid clashing with the existing [Notation] definitions for
    ordinary [com]mands, we introduce these notations in a special
    scope called [dcom_scope], and we [Open] this scope for the
    remainder of the file.

    Careful readers will note that we've defined two notations 
    for specifying a precondition explicitly, one with and one 
    without a [->>].  The "without" version is intended to be 
    used to supply the initial precondition at the very top 
    of the program. *)

Example dec_while : decorated := 
  {{ fun st => True }}
  WHILE !(X =? 0)
  DO
    {{ fun st => True /\ st X <> 0}}
    X ::= X .- 1
    {{ fun _ => True }}
  END
  {{ fun st => True /\ st X = 0}} ->>
  {{ fun st => st X = 0 }}.

(** It is easy to go from a [dcom] to a [com] by erasing all
    annotations. *)

Fixpoint extract (d:dcom) : com :=
  match d with
  | DCSkip _           => SKIP
  | DCSeq d1 d2        => (extract d1 ;; extract d2)%com
  | DCAsgn X a _       => X ::= a
  | DCIf b _ d1 _ d2 _ => IFB b THEN extract d1 ELSE extract d2 FI
  | DCWhile b _ d _    => WHILE b DO extract d END
  | DCPre _ d          => extract d
  | DCPost d _         => extract d
  end.

Definition extract_dec (dec : decorated) : com :=
  match dec with
  | Decorated P d => extract d
  end.

Compute (extract_dec dec_while).

(** The choice of exactly where to put assertions in the definition of
    [dcom] is a bit subtle.  The simplest thing to do would be to
    annotate every [dcom] with a precondition and postcondition.  But
    this would result in very verbose programs with a lot of repeated
    annotations: for example, a program like [SKIP;SKIP] would have to
    be annotated as

        {{P}} ({{P}} SKIP {{P}}) ;; ({{P}} SKIP {{P}}) {{P}},

    with pre- and post-conditions on each [SKIP], plus identical pre-
    and post-conditions on the semicolon!

    Instead, the rule we've followed is this:

       - The _post_-condition expected by each [dcom] [d] is embedded
         in [d].

       - The _pre_-condition is supplied by the context. *)

(** In other words, the invariant of the representation is that a
    [dcom] [d] together with a precondition [P] determines a Hoare
    triple [{{P}} (extract d) {{post d}}], where [post] is defined as
    follows: *)

Fixpoint post (d:dcom) : Assertion :=
  match d with
  | DCSkip P                => P
  | DCSeq d1 d2             => post d2
  | DCAsgn X a Q            => Q
  | DCIf  _ _ d1 _ d2 Q     => Q
  | DCWhile b Pbody c Q     => Q
  | DCPre _ d               => post d
  | DCPost c Q              => Q
  end.

(** It is straightforward to extract the precondition and
    postcondition from a decorated program. *)

Definition pre_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => P
  end.

Definition post_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => post d
  end.

(** We can express what it means for a decorated program to be
    correct as follows: *)

Definition dec_correct (dec : decorated) :=
  {{pre_dec dec}} (extract_dec dec) {{post_dec dec}}.

(** To check whether this Hoare triple is _valid_, we need a way to
    extract the "proof obligations" from a decorated program.  These
    obligations are often called _verification conditions_, because
    they are the facts that must be verified to see that the
    decorations are logically consistent and thus add up to a complete
    proof of correctness. *)

(* ================================================================= *)
(** ** Extracting Verification Conditions *)

(** The function [verification_conditions] takes a [dcom] [d] together
    with a precondition [P] and returns a _proposition_ that, if it
    can be proved, implies that the triple [{{P}} (extract d) {{post d}}]
    is valid. *)

(** It does this by walking over [d] and generating a big
    conjunction including all the "local checks" that we listed when
    we described the informal rules for decorated programs.  (Strictly
    speaking, we need to massage the informal rules a little bit to
    add some uses of the rule of consequence, but the correspondence
    should be clear.) *)

Fixpoint VC (P : Assertion) (d:dcom)
                               : Prop :=
  match d with
  | DCSkip Q =>
    P ->> Q
 
  | DCSeq d1 d2 =>
    VC P d1
    /\ VC (post d1)  d2
  | DCAsgn X a Q =>
    P ->> Q [a // X]

  | DCIf b P1 d1 P2 d2 Q =>
    (fun st => P st /\ (bassn b) st) ->> P1
    /\ (fun st => P st /\ ~(bassn b) st) ->> P2
    /\ post d1 ->> Q
    /\ post d2 ->> Q
    /\ VC P1 d1
    /\ VC P2 d2

  | DCWhile b Pbody d Ppost =>
    P ->> post d
    /\ (fun st => (post d) st /\ (bassn b) st) ->> Pbody
    /\ (fun st => (post d) st /\ ~(bassn b) st) ->> Ppost
    /\ VC Pbody d

  | DCPre P' d =>
    P ->> P' /\ VC P' d
  | DCPost d Q =>
    VC P d /\ post d ->> Q
end.

(** And now the key theorem, stating that [verification_conditions]
    does its job correctly.  Not surprisingly, we need to use each of
    the Hoare Logic rules at some point in the proof. *)

Theorem verification_correct : forall d P,
  VC P d -> {{P}} (extract d) {{post d}}.
Proof.
  induction d; intros ? H; simpl in *.
  - (* Skip *)
    eapply hoare_weak_pre.
      apply hoare_skip.
      assumption.
  - (* Seq *)
    inversion H as [H1 H2]. clear H.
    eapply hoare_seq.
      apply IHd2. apply H2.
      apply IHd1. apply H1.
  - (* Asgn *)
    eapply hoare_weak_pre.
      apply hoare_asgn.
      assumption.
  - (* If *)
    inversion H as [HPre1 [HPre2 [Hd1 [Hd2 [HThen HElse]]]]].
    clear H.
    apply IHd1 in HThen. clear IHd1.
    apply IHd2 in HElse. clear IHd2.
    apply hoare_if.
      + eapply hoare_weak_post with (Q':=post d1); eauto.
         eapply hoare_weak_pre; eauto.
      + eapply hoare_weak_post with (Q':=post d2); eauto.
         eapply hoare_weak_pre; eauto.
  - (* While *)
    inversion H as [Hpre [Hbody1 [Hpost1  Hd]]]. clear H.
    eapply hoare_weak_pre; eauto.
    eapply hoare_weak_post; eauto.
    apply hoare_while.
    eapply hoare_weak_pre; eauto.
  - (* Pre *)
    inversion H as [HP Hd]; clear H.
    eapply hoare_weak_pre. apply IHd. apply Hd. assumption.
  - (* Post *)
    inversion H as [Hd HQ]; clear H.
    eapply hoare_weak_post. apply IHd. apply Hd. assumption.
Qed.

(* ================================================================= *)
(** ** Automation *)

(** Now that all the pieces are in place, we can verify an entire program. *)

Definition VC_dec (dec : decorated) : Prop :=
  match dec with
  | Decorated P d => VC P d
  end.

Lemma verification_correct_dec : forall dec,
  VC_dec dec -> dec_correct dec.
Proof.
  intros [P d]. apply verification_correct.
Qed.

(** The propositions generated by [verification_conditions] are fairly
    big, and they contain many conjuncts that are essentially trivial. *)

Eval simpl in (VC_dec dec_while).
(**

    ==> 
    (((fun _ : state => True) ->> (fun _ : state => True)) /\
     ((fun st : state => True /\ bassn (! (X = 0)) st) ->>
      (fun st : state => True /\ st X <> 0)) /\
     ((fun st : state => True /\ ~ bassn (! (X = 0)) st) ->>
      (fun st : state => True /\ st X = 0)) /\
      (fun st : state => True /\ st X <> 0) ->> 
      (fun _ : state => True) [X |-> X - 1]) /\
      (fun st : state => True /\ st X = 0) ->> (fun st : state => st X = 0)    
*)

(** In principle, we could work with such propositions using just the
    tactics we have so far, but we can make things much smoother with
    a bit of automation.  We first define a custom [verify] tactic
    that uses [split] repeatedly to turn all the conjunctions into
    separate subgoals and then uses [omega] and [eauto] (described in
    chapter [Auto] in _Logical Foundations_) to deal with as many
    of them as possible. *)

(** Hint:
    bassn, assert_implies, assn_sub, t_update, beval, aeval 
    not_true_iff_false         
    not_false_iff_true
    negb_true_iff
    negb_false_iff
    beq_nat_true_iff
    beq_nat_false_iff
    leb_iff
    leb_iff_conv
 *)

(** What's left after [certify] does its thing is "just the interesting
    parts" of checking that the decorations are correct. For very
    simple examples [verify] immediately solves the goal (provided
    that the annotations are correct!). *)

Ltac verify :=
  intros;
  match goal with
  | [|- dec_correct _ ] =>
    apply verification_correct_dec;
    simpl; repeat split; my_simpl
  end.

Theorem dec_while_correct :
  dec_correct dec_while.
Proof.
  verify.
Qed.

(** Another example (formalizing a decorated program we've seen
    before): *)

Example subtract_slowly_dec (m:nat) (p:nat) : decorated := 
    {{ fun st => st X = m /\ st Z = p }} ->>
    {{ fun st => st Z - st X = p - m }}
  WHILE ! (X =? 0)
  DO   {{ fun st => st Z - st X = p - m /\ st X <> 0 }} ->>
       {{ fun st => (st Z - 1) - (st X - 1) = p - m }}
     Z ::= Z .- 1
       {{ fun st => st Z - (st X - 1) = p - m }} ;;
     X ::= X .- 1
       {{ fun st => st Z - st X = p - m }}
  END
    {{ fun st => st Z - st X = p - m /\ st X = 0 }} ->>
    {{ fun st => st Z = p - m }}.

Theorem subtract_slowly_dec_correct : forall m p,
    dec_correct (subtract_slowly_dec m p).
Proof.
  verify.
Qed.

(* ================================================================= *)
(** ** Examples *)

(** In this section, we use the automation developed above to verify
    formal decorated programs corresponding to most of the informal
    ones we have seen. *)

(* ----------------------------------------------------------------- *)
(** *** Swapping Using Addition and Subtraction *)

Definition swap : com :=
  (X ::= X .+ Y;;
  Y ::= X .- Y;;
  X ::= X .- Y)%com.

Definition swap_dec m n : decorated :=
   {{ fun st => st X = m /\ st Y = n}} ->>
   {{ fun st => (st X + st Y) - ((st X + st Y) - st Y) = n
                /\ (st X + st Y) - st Y = m }}
  X ::= X .+ Y
   {{ fun st => st X - (st X - st Y) = n /\ st X - st Y = m }};;
  Y ::= X .- Y
   {{ fun st => st X - st Y = n /\ st Y = m }};;
  X ::= X .- Y
   {{ fun st => st X = n /\ st Y = m}}.

Theorem swap_correct : forall m n,
    dec_correct (swap_dec m n).
Proof.
  verify.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Simple Conditionals *)

Definition if_minus_plus_com :=
  IFB X <=? Y
    THEN Z ::= Y .- X
    ELSE Y ::= X .+ Z
  FI.

Definition if_minus_plus_dec :=
  {{fun st => True}}
  IFB X <=? Y  THEN
      {{ fun st => True /\ st X <= st Y }} ->>
      {{ fun st => st Y = st X + (st Y - st X) }}
    Z ::= Y .- X
      {{ fun st => st Y = st X + st Z }}
  ELSE
      {{ fun st => True /\ ~(st X <= st Y) }} ->>
      {{ fun st => st X + st Z = st X + st Z }}
    Y ::= X .+ Z
      {{ fun st => st Y = st X + st Z }}
  FI
  {{fun st => st Y = st X + st Z}}.

Theorem if_minus_plus_correct :
  dec_correct if_minus_plus_dec.
Proof.
  verify.
Qed.

Definition if_minus_dec :=
  {{fun st => True}}
  IFB X <=? Y THEN
      {{fun st => True /\ st X <= st Y }} ->>
      {{fun st => (st Y - st X) + st X = st Y
               \/ (st Y - st X) + st Y = st X}}
    Z ::= Y .- X
      {{fun st => st Z + st X = st Y \/ st Z + st Y = st X}}
  ELSE
      {{fun st => True /\ ~(st X <= st Y) }} ->>
      {{fun st => (st X - st Y) + st X = st Y
               \/ (st X - st Y) + st Y = st X}}
    Z ::= X .- Y
      {{fun st => st Z + st X = st Y \/ st Z + st Y = st X}}
  FI
    {{fun st => st Z + st X = st Y \/ st Z + st Y = st X}}.

Theorem if_minus_correct :
  dec_correct if_minus_dec.
Proof.
  verify.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Division *)

Definition div_mod_dec (a b : nat) : decorated := 
  {{ fun st => True }} ->>
  {{ fun st => b * 0 + a = a }}
  X ::= a
  {{ fun st => b * 0 + st X = a }};;
  Y ::= 0
  {{ fun st => b * st Y + st X = a }};;
  WHILE b <=? X DO
    {{ fun st => b * st Y + st X = a /\ b <= st X }} ->>
    {{ fun st => b * (st Y + 1) + (st X - b) = a }}
    X ::= X .- b
    {{ fun st => b * (st Y + 1) + st X = a }};;
    Y ::= Y .+ 1
    {{ fun st => b * st Y + st X = a }}
  END
  {{ fun st => b * st Y + st X = a /\ ~(b <= st X) }} ->>
  {{ fun st => b * st Y + st X = a /\ (st X < b) }}.

Theorem div_mod_dec_correct : forall a b,
  dec_correct (div_mod_dec a b).
Proof.
  verify.
  rewrite mult_plus_distr_l. omega.
Qed.


(* ----------------------------------------------------------------- *)
(** *** Square Roots *)

Definition sqrt_dec m : decorated := 
    {{ fun st => st X = m }} ->>
    {{ fun st => st X = m /\ 0*0 <= m }}
  Z ::= 0
    {{ fun st => st X = m /\ st Z*st Z <= m }};;
  WHILE (Z.+1).*(Z.+1) <=? X DO
      {{ fun st => (st X = m /\ st Z*st Z<=m)
                   /\ (st Z + 1)*(st Z + 1) <= st X }} ->>
      {{ fun st => st X = m /\ (st Z+1)*(st Z+1)<=m }}
    Z ::= Z .+ 1
      {{ fun st => st X = m /\ st Z*st Z<=m }}
  END
    {{ fun st => (st X = m /\ st Z*st Z<=m)
                   /\ ~((st Z + 1)*(st Z + 1) <= st X) }} ->>
    {{ fun st => st Z*st Z<=m /\ m<(st Z+1)*(st Z+1) }}.

Theorem sqrt_correct : forall m,
  dec_correct (sqrt_dec m).
Proof. verify. Qed.

(* ----------------------------------------------------------------- *)
(** *** Two loops *)

Definition two_loops_dec (a b c : nat) : decorated :=
  {{ fun st => True }} ->>
  {{ fun st => c = 0 + c /\ 0 = 0 }}
  X ::= 0
  {{ fun st => c = st X + c /\ 0 = 0 }};;
  Y ::= 0
  {{ fun st => c = st X + c /\ st Y = 0 }};;
  Z ::= c
  {{ fun st => st Z = st X + c /\ st Y = 0 }};;
  WHILE !(X =? a) DO
    {{ fun st => (st Z = st X + c /\ st Y = 0) /\ st X <> a }} ->>
    {{ fun st => st Z + 1 = st X + 1 + c /\ st Y = 0 }}
    X ::= X .+ 1
    {{ fun st => st Z + 1 = st X + c /\ st Y = 0 }};;
    Z ::= Z .+ 1
    {{ fun st => st Z = st X + c /\ st Y = 0 }}
  END
  {{ fun st => (st Z = st X + c /\ st Y = 0) /\ st X = a }} ->>
  {{ fun st => st Z = a + st Y + c }};;
  WHILE !(Y =? b) DO
    {{ fun st => st Z = a + st Y + c /\ st Y <> b }} ->>
    {{ fun st => st Z + 1 = a + st Y + 1 + c }}
    Y ::= Y .+ 1
    {{ fun st => st Z + 1 = a + st Y + c }};;
    Z ::= Z .+ 1 
    {{ fun st => st Z = a + st Y + c }}
  END
  {{ fun st => (st Z = a + st Y + c) /\ st Y = b }} ->>
  {{ fun st => st Z = a + b + c }}.

Theorem two_loops_correct : forall a b c,
  dec_correct (two_loops_dec a b c).
Proof. verify. Qed.
