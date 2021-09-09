(** * Basics: Functional Programming in Coq *)

(* ################################################################# *)
(** * Acknowledgement *)

(** The materials are borrowed from the  _Software Foundations_ series. 
    http://softwarefoundations.cis.upenn.edu 
 *)

(** Compile the lecture notes using
    [coqc Coq_Lecture1_Basics]
*)

(* ################################################################# *)
(** * Overview *)

(** Building reliable software is really hard.  The scale and
    complexity of modern systems, the number of people involved, and
    the range of demands placed on them make it extremely difficult to
    build software that is even more-or-less correct, much less 100%%
    correct.  At the same time, the increasing degree to which
    information processing is woven into every aspect of society
    greatly amplifies the cost of bugs and insecurities.

    Computer scientists and software engineers have responded to these
    challenges by developing a whole host of techniques for improving
    software reliability, ranging from recommendations about managing
    software projects teams (e.g., extreme programming) to design
    philosophies for libraries (e.g., model-view-controller,
    publish-subscribe, etc.) and programming languages (e.g.,
    object-oriented programming, aspect-oriented programming,
    functional programming, ...) to mathematical techniques for
    specifying and reasoning about properties of software and tools
    for helping validate these properties.  The _Software Foundations_
    series is focused on this last set of techniques.

    The text is constructed around three conceptual threads:

    (1) basic tools from _logic_ for making and justifying precise
        claims about programs;

    (2) the use of _proof assistants_ to construct rigorous logical
        arguments;

    (3) _functional programming_, both as a method of programming that
        simplifies reasoning about programs and as a bridge between
        programming and logic.

    Some suggestions for further reading can be found in the
    [Postscript] chapter.  Bibliographic information for all
    cited works can be found in the file [Bib]. *)


(* ================================================================= *)
(** ** Proof Assistants *)

(** The flow of ideas between logic and computer science has not been
    unidirectional: CS has also made important contributions to logic.
    One of these has been the development of software tools for
    helping construct proofs of logical propositions.  These tools
    fall into two broad categories:

       - _Automated theorem provers_ provide "push-button" operation:
         you give them a proposition and they return either _true_ or
         _false_ (or, sometimes, _don't know: ran out of time_).
         Although their capabilities are still limited to specific
         domains, they have matured tremendously in recent years and
         are used now in a multitude of settings.  Examples of such
         tools include SAT solvers, SMT solvers, and model checkers.

       - _Proof assistants_ are hybrid tools that automate the more
         routine aspects of building proofs while depending on human
         guidance for more difficult aspects.  Widely used proof
         assistants include Isabelle, Agda, Twelf, ACL2, PVS, and Coq,
         among many others.

    This course is based around Coq, a proof assistant that has been
    under development since 1983 and that in recent years has
    attracted a large community of users in both research and
    industry.  Coq provides a rich environment for interactive
    development of machine-checked formal reasoning.  The kernel of
    the Coq system is a simple proof-checker, which guarantees that
    only correct deduction steps are ever performed.  On top of this
    kernel, the Coq environment provides high-level facilities for
    proof development, including a large library of common definitions
    and lemmas, powerful tactics for constructing complex proofs
    semi-automatically, and a special-purpose programming language for
    defining new proof-automation tactics for specific situations.

    Coq has been a critical enabler for a huge variety of work across
    computer science and mathematics:

    - As a _platform for modeling programming languages_, it has
      become a standard tool for researchers who need to describe and
      reason about complex language definitions.  It has been used,
      for example, to check the security of the JavaCard platform,
      obtaining the highest level of common criteria certification,
      and for formal specifications of the x86 and LLVM instruction
      sets and programming languages such as C.

    - As an _environment for developing formally certified software
      and hardware_, Coq has been used, for example, to build
      CompCert, a fully-verified optimizing compiler for C, and
      CertiKOS, a fully verified hypervisor, for proving the
      correctness of subtle algorithms involving floating point
      numbers, and as the basis for CertiCrypt, an environment for
      reasoning about the security of cryptographic algorithms.  It is
      also being used to build verified implementations of the
      open-source RISC-V processor.

    - As a _realistic environment for functional programming with
      dependent types_, it has inspired numerous innovations.  For
      example, the Ynot system embeds "relational Hoare reasoning" (an
      extension of the _Hoare Logic_ we will see later in this course)
      in Coq.

    - As a _proof assistant for higher-order logic_, it has been used
      to validate a number of important results in mathematics.  For
      example, its ability to include complex computations inside
      proofs made it possible to develop the first formally verified
      proof of the 4-color theorem.  This proof had previously been
      controversial among mathematicians because part of it included
      checking a large number of configurations using a program. In
      the Coq formalization, everything is checked, including the
      correctness of the computational part.  More recently, an even
      more massive effort led to a Coq formalization of the
      Feit-Thompson Theorem -- the first major step in the
      classification of finite simple groups.

   By the way, in case you're wondering about the name, here's what
   the official Coq web site at INRIA (the French national research
   lab where Coq has mostly been developed) says about it: "Some
   French computer scientists have a tradition of naming their
   software as animal species: Caml, Elan, Foc or Phox are examples of
   this tacit convention. In French, 'coq' means rooster, and it
   sounds like the initials of the Calculus of Constructions (CoC) on
   which it is based."  The rooster is also the national symbol of
   France, and C-o-q are the first three letters of the name of
   Thierry Coquand, one of Coq's early developers. *)

(* ================================================================= *)
(** ** System Requirements *)

(** Install Opam , Coq 8.4.6 **)

(** Coq runs on Windows, Linux, and macOS.  You will need:

       - A current installation of Coq, available from the Coq home
         page.  These files have been tested with Coq 8.8.0.

       - An IDE for interacting with Coq.  Currently, there are two
         choices:

           - Proof General is an Emacs-based IDE.  It tends to be
             preferred by users who are already comfortable with
             Emacs.  It requires a separate installation (google
             "Proof General").

             Adventurous users of Coq within Emacs may also want to
             check out extensions such as [company-coq] and
             [control-lock].

           - CoqIDE is a simpler stand-alone IDE.  It is distributed
             with Coq, so it should be available once you have Coq
             installed.  It can also be compiled from scratch, but on
             some platforms this may involve installing additional
             packages for GUI libraries and such. *)

(* ================================================================= *)
(** ** Compile the Coq Files *)

(** A tar file containing the full sources for the "release version"
    of this book (as a collection of Coq scripts and HTML files) is
    available at http://softwarefoundations.cis.upenn.edu.

    (If you are using the book as part of a class, your professor may
    give you access to a locally modified version of the files, which
    you should use instead of the release version.) *)



(* ################################################################# *)
(** * Introduction *)

(** The functional programming style is founded on simple, everyday
    mathematical intuition: If a procedure or method has no side
    effects, then (ignoring efficiency) all we need to understand
    about it is how it maps inputs to outputs -- that is, we can think
    of it as just a concrete method for computing a mathematical
    function.  This is one sense of the word "functional" in
    "functional programming."  The direct connection between programs
    and simple mathematical objects supports both formal correctness
    proofs and sound informal reasoning about program behavior.

    The other sense in which functional programming is "functional" is
    that it emphasizes the use of functions (or methods) as
    _first-class_ values -- i.e., values that can be passed as
    arguments to other functions, returned as results, included in
    data structures, etc.  The recognition that functions can be
    treated as data gives rise to a host of useful and powerful
    programming idioms.

    Other common features of functional languages include _algebraic
    data types_ and _pattern matching_, which make it easy to
    construct and manipulate rich data structures, and sophisticated
    _polymorphic type systems_ supporting abstraction and code reuse.
    Coq offers all of these features.

    The first half of this chapter introduces the most essential
    elements of Coq's functional programming language, called
    _Gallina_.  The second half introduces some basic _tactics_ that
    can be used to prove properties of Coq programs. *)

(* ################################################################# *)
(** * Data and Functions *)
(* ================================================================= *)
(** ** Enumerated Types *)

(** One notable aspect of Coq is that its set of built-in
    features is _extremely_ small.  For example, instead of providing
    the usual palette of atomic data types (booleans, integers,
    strings, etc.), Coq offers a powerful mechanism for defining new
    data types from scratch, with all these familiar types as
    instances.

    Naturally, the Coq distribution comes preloaded with an extensive
    standard library providing definitions of booleans, numbers, and
    many common data structures like lists and hash tables.  But there
    is nothing magic or primitive about these library definitions.  To
    illustrate this, we will explicitly recapitulate all the
    definitions we need in this course, rather than just getting them
    implicitly from the library. *)

(* ================================================================= *)
(** ** Days of the Week *)

(** To see how this definition mechanism works, let's start with
    a very simple example.  The following declaration tells Coq that
    we are defining a new set of data values -- a _type_. *)

Inductive day :=
| monday
| tuesday
| wednesday
| thursday
| friday
| saturday
| sunday.

(** Inituitionistic Logic
    A is True:= we have a proof p for A := (p: A)
    A is False:= we have a proof p for not A *)

(** The type is called [day], and its members are [monday],
    [tuesday], etc.  The second and following lines of the definition
    can be read "[monday] is a [day], [tuesday] is a [day], etc."

    Having defined [day], we can write functions that operate on
    days. *)

Definition next_weekday d :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | _    => monday
  end.

Compute (next_weekday tuesday).

(**

-------- (refl)
a = a

*)

Lemma test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof.
  reflexivity.
Qed.

(** This declaration does two things: it makes an
    assertion (that the second weekday after [saturday] is [tuesday]),
    and it gives the assertion a name that can be used to refer to it
    later.  Having made the assertion, we can also ask Coq to verify
    it, like this: *)

(** The details are not important for now (we'll come back to
    them in a bit), but essentially this can be read as "The assertion
    we've just made can be proved by observing that both sides of the
    equality evaluate to the same thing, after some simplification."

    Third, we can ask Coq to _extract_, from our [Definition], a
    program in some other, more conventional, programming
    language (OCaml, Scheme, or Haskell) with a high-performance
    compiler.  This facility is very interesting, since it gives us a
    way to go from proved-correct algorithms written in Gallina to
    efficient machine code.  (Of course, we are trusting the
    correctness of the OCaml/Haskell/Scheme compiler, and of Coq's
    extraction facility itself, but this is still a big step forward
    from the way most software is developed today.) Indeed, this is
    one of the main uses for which Coq was developed.  We'll come back
    to this topic in later chapters. *)


(* ================================================================= *)
(** ** Booleans *)

(** In a similar way, we can define the standard type [bool] of
    booleans, with members [true] and [false]. *)

Inductive bool :=
| true
| false.

Check True. (*True*)
Check False. (*False*)

(** Although we are rolling our own booleans here for the sake
    of building up everything from scratch, Coq does, of course,
    provide a default implementation of the booleans, together with a
    multitude of useful functions and lemmas.  (Take a look at
    [Coq.Init.Datatypes] in the Coq library documentation if you're
    interested.)  Whenever possible, we'll name our own definitions
    and theorems so that they exactly coincide with the ones in the
    standard library.

    Functions over booleans can be defined in the same way as
    above: *)

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Compute (negb false).

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Compute (orb false true).

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | false => false
  | true => b2
  end.

(** The last two of these illustrate Coq's syntax for
    multi-argument function definitions.  The corresponding
    multi-argument application syntax is illustrated by the following
    "unit tests," which constitute a complete specification -- a truth
    table -- for the [orb] function: *)

Example test_and1:  (andb true  false) = false.
Proof. simpl. reflexivity.  Qed.
Example test_orb2:  (orb false false) = false.
Proof. simpl. reflexivity.  Qed.
Example test_orb3:  (orb false true)  = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb4:  (orb true  true)  = true.
Proof. simpl. reflexivity.  Qed.

(** We can also introduce some familiar syntax for the boolean
    operations we have just defined. The [Notation] command defines a new
    symbolic notation for an existing definition. *)

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5:  false || false || true = true.
Proof. simpl. reflexivity. Qed.

(** _A note on notation_: In [.v] files, we use square brackets
    to delimit fragments of Coq code within comments; this convention,
    also used by the [coqdoc] documentation tool, keeps them visually
    separate from the surrounding text.  In the HTML version of the
    files, these pieces of text appear in a [different font].

    The command [Admitted] can be used as a placeholder for an
    incomplete proof.  We'll use it in exercises, to indicate the
    parts that we're leaving for you -- i.e., your job is to replace
    [Admitted]s with real proofs. *)


(* ================================================================= *)
(** ** Function Types *)

(** Every expression in Coq has a type, describing what sort of
    thing it computes. The [Check] command asks Coq to print the type
    of an expression. *)

Check true.

Check True.
Check I.
Check False.

(* ===> true : bool *)
Check (negb true).
(* ===> negb true : bool *)

(** Functions like [negb] itself are also data values, just like
    [true] and [false].  Their types are called _function types_, and
    they are written with arrows. *)

Check negb.
(* ===> negb : bool -> bool *)

(** The type of [negb], written [bool -> bool] and pronounced
    "[bool] arrow [bool]," can be read, "Given an input of type
    [bool], this function produces an output of type [bool]."
    Similarly, the type of [andb], written [bool -> bool -> bool], can
    be read, "Given two inputs, both of type [bool], this function
    produces an output of type [bool]." *)

(* ================================================================= *)
(** ** Compound Types *)

(** The types we have defined so far are examples of "enumerated
    types": their definitions explicitly enumerate a finite set of
    elements, each of which is just a bare constructor.  Here is a
    more interesting type definition, where one of the constructors
    takes an argument: *)

Inductive rgb : Type :=
| red : rgb
| green : rgb
| blue : rgb.

Inductive color :=
| black
| white
| primary (r : rgb).

(** Let's look at this in a little more detail.

    Every inductively defined type ([day], [bool], [rgb], [color],
    etc.) contains a set of _constructor expressions_ built from
    _constructors_ like [red], [primary], [true], [false], [monday],
    etc. *)
(** The definitions of [rgb] and [color] say how expressions in the
    sets [rgb] and [color] can be built:

    - [red], [green], and [blue] are the constructors of [rgb];
    - [black], [white], and [primary] are the constructors of [color];
    - the expression [red] belongs to the set [rgb], as do the
      expressions [green] and [blue];
    - the expressions [black] and [white] belong to the set [color];
    - if [p] is an expression belonging to the set [rgb], then
      [primary p] (pronounced "the constructor [primary] applied to
      the argument [p]") is an expression belonging to the set
      [color]; and
    - expressions formed in these ways are the _only_ ones belonging
      to the sets [rgb] and [color]. *)

(** We can define functions on colors using pattern matching just as
    we have done for [day] and [bool]. *)

Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary _ => false
  end.

(** Since the [primary] constructor takes an argument, a pattern
    matching [primary] should include either a variable (as above) or
    a constant of appropriate type (as below). *)

Definition isred' (c : color) : bool :=
  match c with
  | primary r =>
    match r with
    | red => true
    | _ => false
    end
  |_ => false
  end.


(** The pattern [primary _] here is shorthand for "[primary] applied
    to any [rgb] constructor except [red]."  (The wildcard pattern [_]
    has the same effect as the dummy pattern variable [p] in the
    definition of [monochrome].) *)

(* ================================================================= *)
(** ** Modules *)

(** Coq provides a _module system_, to aid in organizing large
    developments.  In this course we won't need most of its features,
    but one is useful: If we enclose a collection of declarations
    between [Module X] and [End X] markers, then, in the remainder of
    the file after the [End], these definitions are referred to by
    names like [X.foo] instead of just [foo].  We will use this
    feature to introduce the definition of the type [nat] in an inner
    module so that it does not interfere with the one from the
    standard library (which we want to use in the rest because it
    comes with a tiny bit of convenient special notation).  *)

Module NatPlayground.

  (* ================================================================= *)
  (** ** Numbers *)

  (** An even more interesting way of defining a type is to allow its
    constructors to take arguments from the very same type -- that is,
    to allow the rules describing its elements to be _inductive_.

    For example, we can define (a unary representation of) natural
    numbers as follows: *)

  Inductive nat :=
  | O
  | S (n: nat).

  Check nat_ind.

  Definition minustwo (n : nat) : nat :=
    match n with
    | O => O
    | S O => O
    | S (S n') => n'
    end.

  Compute (minustwo (S(S(S(S O))))).
  
  (** The clauses of this definition can be read:
      - [O] is a natural number (note that this is the letter "[O],"
        not the numeral "[0]").
      - [S] can be put in front of a natural number to yield another
        one -- if [n] is a natural number, then [S n] is too. *)

  (** Again, let's look at this in a little more detail.  The definition
    of [nat] says how expressions in the set [nat] can be built:

    - [O] and [S] are constructors;
    - the expression [O] belongs to the set [nat];
    - if [n] is an expression belonging to the set [nat], then [S n]
      is also an expression belonging to the set [nat]; and
    - expressions formed in these two ways are the only ones belonging
      to the set [nat]. *)

  (** The same rules apply for our definitions of [day], [bool],
    [color], etc.

    The above conditions are the precise force of the [Inductive]
    declaration.  They imply that the expression [O], the expression
_    [S O], the expression [S (S O)], the expression [S (S (S O))], and
    so on all belong to the set [nat], while other expressions built
    from data constructors, like [true], [andb true false], [S (S
    false)], and [O (O (O S))] do not.

_    A critical point here is that what we've done so far is just to
    define a _representation_ of numbers: a way of writing them down.
    The names [O] and [S] are arbitrary, and at this point they have
    no special meaning -- they are just two different marks that we
    can use to write down numbers (together with a rule that says any
    [nat] will be written as some string of [S] marks followed by an
    [O]).  If we like, we can write essentially the same definition
    this way: *)

  Inductive nat' : Type :=
  | stop : nat'
  | tick : nat' -> nat'.

  Check (tick stop).

  (** The _interpretation_ of these marks comes from how we use them to
    compute. *)

  (** We can do this by writing functions that pattern match on
    representations of natural numbers just as we did above with
    booleans and days -- for example, here is the predecessor
    function: *)

  Definition pred (n : nat) : nat :=
    match n with
    | O => O
    | S n' => n'
    end.

  Definition pred' (n : nat) : nat :=
    match n with
    | O => O
    | S n' => n'
    end.

(** The second branch can be read: "if [n] has the form [S n']
    for some [n'], then return [n']."  *)

End NatPlayground.


Check NatPlayground.pred.

Check NatPlayground.pred'.

Check pred.
Print nat.

(** Because natural numbers are such a pervasive form of data,
    Coq provides a tiny bit of built-in magic for parsing and printing
    them: ordinary arabic numerals can be used as an alternative to
    the "unary" notation defined by the constructors [S] and [O].  Coq
    prints numbers in arabic form by default: *)

Check (S (S (S (S O)))).
(* ===> 4 : nat *)

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Compute (minustwo 4).
(* ===> 2 : nat *)

(** The constructor [S] has the type [nat -> nat], just like
    [pred] and functions like [minustwo]: *)

Check S.
Check pred.
Check minustwo.

(** These are all things that can be applied to a number to yield a
    number.  However, there is a fundamental difference between the
    first one and the other two: functions like [pred] and [minustwo]
    come with _computation rules_ -- e.g., the definition of [pred]
    says that [pred 2] can be simplified to [1] -- while the
    definition of [S] has no such behavior attached.  Although it is
    like a function in the sense that it can be applied to an
    argument, it does not _do_ anything at all!  It is just a way of
    writing down numbers.  (Think about standard arabic numerals: the
    numeral [1] is not a computation; it's a piece of data.  When we
    write [111] to mean the number one hundred and eleven, we are
    using [1], three times, to write down a concrete representation of
    a number.)

    For most function definitions over numbers, just pattern matching
    is not enough: we also need recursion.  For example, to check that
    a number [n] is even, we may need to recursively check whether
    [n-2] is even.  To write such functions, we use the keyword
    [Fixpoint]. *)

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.


(** We can define [oddb] by a similar [Fixpoint] declaration, but here
    is a simpler definition: *)

Definition oddb (n:nat) : bool   :=   negb (evenb n).

Example test_oddb1:    oddb 1 = true.
Proof. simpl. reflexivity.  Qed.
Example test_oddb2:    oddb 4 = false.
Proof. simpl. reflexivity.  Qed.

(** (You will notice if you step through these proofs that
    [simpl] actually has no effect on the goal -- all of the work is
    done by [reflexivity].  We'll see more about why that is shortly.)

    Naturally, we can also define multi-argument functions by
    recursion.  *)

Module NatPlayground2.

  Fixpoint plus (n : nat) (m : nat) : nat :=
    match n with
    | O => m
    | S n' => plus n' (S m)
    end.

  (** Adding three to two now gives us five, as we'd expect. *)

  Compute (plus 3 2).

  (** The simplification that Coq performs to reach this conclusion can
    be visualized as follows: *)

  (*  [plus (S (S (S O))) (S (S O))]
==> [S (plus (S (S O)) (S (S O)))]
      by the second clause of the [match]
==> [S (S (plus (S O) (S (S O))))]
      by the second clause of the [match]
==> [S (S (S (plus O (S (S O)))))]
      by the second clause of the [match]
==> [S (S (S (S (S O))))]
      by the first clause of the [match]
   *)

  (** As a notational convenience, if two or more arguments have
    the same type, they can be written together.  In the following
    definition, [(n m : nat)] means just the same as if we had written
    [(n : nat) (m : nat)]. *)

  Fixpoint mult (n m : nat) : nat :=
    match n with
    | O => O
    | S n' => plus m (mult n' m)
    end.

  Example test_mult1: (mult 3 3) = 9.
  Proof. reflexivity. Qed.
  
  
  (** You can match two expressions at once by putting a comma
    between them: *)

  Fixpoint minus (n m:nat) : nat :=
    match n, m with
    | O   , _    => O
    | S _ , O    => n
    | S n', S m' => minus n' m'
    end.

  Compute (minus 44 3).

(** Again, the [_] in the first line is a _wildcard pattern_.  Writing
    [_] in a pattern is the same as writing some variable that doesn't
    get used on the right-hand side.  This avoids the need to invent a
    variable name. *)

End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => 1
  | S p => mult base (exp base p)
  end.

(** **** Exercise: 1 star (factorial)  *)
(** Recall the standard mathematical factorial function:

       factorial(0)  =  1
       factorial(n)  =  n * factorial(n-1)     (if n>0)

    Translate this into Coq. *)

Fixpoint factorial (n:nat) : nat :=
  match n with
  | O => 1
  | S n' => mult n (factorial n')
  end.

Compute (factorial 3).

Example test_factorial1:          (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

(** We can make numerical expressions a little easier to read and
    write by introducing _notations_ for addition, multiplication, and
    subtraction. *)

Notation "x + y" := (plus x y)
                      (at level 50, left associativity)
                    : nat_scope.
Notation "x - y" := (minus x y)
                      (at level 50, left associativity)
                    : nat_scope.
Notation "x * y" := (mult x y)
                      (at level 40, left associativity)
                    : nat_scope.

Compute (5 * 4 + 1).

Check ((0 + 1) + 1).

(** (The [level], [associativity], and [nat_scope] annotations
    control how these notations are treated by Coq's parser.  The
    details are not important for our purposes, but interested readers
    can refer to the "More on Notation" section at the end of this
    chapter.)

    Note that these do not change the definitions we've already made:
    they are simply instructions to the Coq parser to accept [x + y]
    in place of [plus x y] and, conversely, to the Coq pretty-printer
    to display [plus x y] as [x + y]. *)

(** When we say that Coq comes with almost nothing built-in, we really
    mean it: even equality testing is a user-defined operation!

    Here is a function [beq_nat], which tests [nat]ural numbers for
    [eq]uality, yielding a [b]oolean.  Note the use of nested
    [match]es (we could also have used a simultaneous match, as we did
    in [minus].) *)

Check (negb true).

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | _ => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Compute (beq_nat 5 4).

(** The [leb] function tests whether its first argument is less than or
  equal to its second argument, yielding a boolean. *)

Compute (pred 0).

Check (4 <= 5).

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' => match m with
            | O => false
            | S m' => leb n' m'
            end
  end.

Definition leb' (n m: nat): Prop :=
  match leb n m with
  | true => True
  | _ => False
  end.

Example test_leb1:             (leb 2 2) = true.
Proof. simpl. reflexivity.  Qed.
Example test_leb2:             (leb 2 4) = true.
Proof. simpl. reflexivity.  Qed.
Example test_leb3:             (leb 4 2) = false.
Proof. simpl. reflexivity.  Qed.

Section InformalProof.
  
  (* ################################################################# *)
  (** * Coq Proof v.s. Paper Proof *)
  (** 
    -------------- (les_i)
      Les n (S n)

    Show: forall m, exists m', Les m m'.
    Proof.
    ----------------------------------------------
    | H1: m0                    (hyp)
    | H2: Les m0 (S m0)         (les_i, m0)
    | H3: exists m', Les m0 m'  (exists_i, 2)
    ----------------------------------------------
    G0: forall m, exists m', Les m m'.   (forall_i, 1~3) *)

  Variable Les: nat -> nat -> Prop.
  Hypothesis les_i: forall n, Les n (S n).

  Lemma les_correct:
    forall m, exists m', Les m m'.
  Proof.
    intros m0.
    exists (S m0).
    apply les_i.
  Qed.

End InformalProof.

(* ################################################################# *)
(** * Proof by Simplification *)

(** Now that we've defined a few datatypes and functions, let's
    turn to stating and proving properties of their behavior.
    Actually, we've already started doing this: each [Example] in the
    previous sections makes a precise claim about the behavior of some
    function on some particular inputs.  The proofs of these claims
    were always the same: use [simpl] to simplify both sides of the
    equation, then use [reflexivity] to check that both sides contain
    identical values.

    The same sort of "proof by simplification" can be used to prove
    more interesting properties as well.  For example, the fact that
    [0] is a "neutral element" for [+] on the left can be proved just
    by observing that [0 + n] reduces to [n] no matter what [n] is, a
    fact that can be read directly off the definition of [plus].*)

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof. intros n. simpl. reflexivity. Qed.

(** (You may notice that the above statement looks different in
    the [.v] file in your IDE than it does in the HTML rendition in
    your browser, if you are viewing both. In [.v] files, we write the
    [forall] universal quantifier using the reserved identifier
    "forall."  When the [.v] files are converted to HTML, this gets
    transformed into an upside-down-A symbol.)

    This is a good place to mention that [reflexivity] is a bit
    more powerful than we have admitted. In the examples we have seen,
    the calls to [simpl] were actually not needed, because
    [reflexivity] can perform some simplification automatically when
    checking that two sides are equal; [simpl] was just added so that
    we could see the intermediate state -- after simplification but
    before finishing the proof.  Here is a shorter proof of the
    theorem: *)

Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

(** Moreover, it will be useful later to know that [reflexivity]
    does somewhat _more_ simplification than [simpl] does -- for
    example, it tries "unfolding" defined terms, replacing them with
    their right-hand sides.  The reason for this difference is that,
    if reflexivity succeeds, the whole goal is finished and we don't
    need to look at whatever expanded expressions [reflexivity] has
    created by all this simplification and unfolding; by contrast,
    [simpl] is used in situations where we may have to read and
    understand the new goal that it creates, so we would not want it
    blindly expanding definitions and leaving the goal in a messy
    state.

    The form of the theorem we just stated and its proof are almost
    exactly the same as the simpler examples we saw earlier; there are
    just a few differences.

    First, we've used the keyword [Theorem] instead of [Example].
    This difference is mostly a matter of style; the keywords
    [Example] and [Theorem] (and a few others, including [Lemma],
    [Fact], and [Remark]) mean pretty much the same thing to Coq.

    Second, we've added the quantifier [forall n:nat], so that our
    theorem talks about _all_ natural numbers [n].  Informally, to
    prove theorems of this form, we generally start by saying "Suppose
    [n] is some number..."  Formally, this is achieved in the proof by
    [intros n], which moves [n] from the quantifier in the goal to a
    _context_ of current assumptions.

    The keywords [intros], [simpl], and [reflexivity] are examples of
    _tactics_.  A tactic is a command that is used between [Proof] and
    [Qed] to guide the process of checking some claim we are making.
    We will see several more tactics in the rest of this chapter and
    yet more in future chapters. *)

(** Other similar theorems can be proved with the same pattern. *)

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. compute. reflexivity.  Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity.  Qed.

(** The [_l] suffix in the names of these theorems is
    pronounced "on the left." *)

(** It is worth stepping through these proofs to observe how the
    context and the goal change.  You may want to add calls to [simpl]
    before [reflexivity] to see the simplifications that Coq performs
    on the terms before checking that they are equal. *)

(* ################################################################# *)
(** * Proof by Rewriting *)

(** This theorem is a bit more interesting than the others we've
    seen: *)

Theorem plus_id_example :
  forall (n m:nat) (Heq: n = m),
    n + n = m + m.

(**

n = m      A[n/x]
----------------- (=e)
A[m/x]

  H1: n = m
  G2: A[n/x] :=  n + n = n + n (refl)
----------------
  G1: n + n = m + m := A[m/x] (=e, A:= n + n = x + x, H1)

 **)


(** Instead of making a universal claim about all numbers [n] and [m],
    it talks about a more specialized property that only holds when [n
    = m].  The arrow symbol is pronounced "implies."

    As before, we need to be able to reason by assuming we are given such
    numbers [n] and [m].  We also need to assume the hypothesis
    [n = m]. The [intros] tactic will serve to move all three of these
    from the goal into assumptions in the current context.

    Since [n] and [m] are arbitrary numbers, we can't just use
    simplification to prove this theorem.  Instead, we prove it by
    observing that, if we are assuming [n = m], then we can replace
    [n] with [m] in the goal statement and obtain an equality with the
    same expression on both sides.  The tactic that tells Coq to
    perform this replacement is called [rewrite]. *)

Proof.
  intros.
  rewrite <- Heq.
  reflexivity. Qed.

(** The first line of the proof moves the universally quantified
    variables [n] and [m] into the context.  The second moves the
    hypothesis [n = m] into the context and gives it the name [H].
    The third tells Coq to rewrite the current goal ([n + n = m + m])
    by replacing the left side of the equality hypothesis [H] with the
    right side.

    (The arrow symbol in the [rewrite] has nothing to do with
    implication: it tells Coq to apply the rewrite from left to right.
    To rewrite from right to left, you can use [rewrite <-].  Try
    making this change in the above proof and see what difference it
    makes.) *)

(** **** Exercise: 1 star (plus_id_exercise)  *)
(** Remove "[Admitted.]" and fill in the proof. *)

Theorem plus_id_exercise : forall n m x o : nat,
    n + x = m + x -> m + x = o + x -> (n + x) + (m + x) = (m + x) + (o + x).
Proof.
  intros n m x o.
  intros Heq1 Heq2.
  rewrite Heq1, Heq2.
  reflexivity. Qed.

(** [] *)

(** The [Admitted] command tells Coq that we want to skip trying
    to prove this theorem and just accept it as a given.  This can be
    useful for developing longer proofs, since we can state subsidiary
    lemmas that we believe will be useful for making some larger
    argument, use [Admitted] to accept them on faith for the moment,
    and continue working on the main argument until we are sure it
    makes sense; then we can go back and fill in the proofs we
    skipped.  Be careful, though: every time you say [Admitted] you
    are leaving a door open for total nonsense to enter Coq's nice,
    rigorous, formally checked world! *)

(** We can also use the [rewrite] tactic with a previously proved
    theorem instead of a hypothesis from the context. If the statement
    of the previously proved theorem involves quantified variables,
    as in the example below, Coq tries to instantiate them
    by matching with the current goal. *)

Theorem mult_0_plus : forall n m : nat,
    (0 + n) * m = n * m.
Proof.
  intros n m. reflexivity. Qed.

(* ################################################################# *)
(** * Proof by Case Analysis *)

(** Of course, not everything can be proved by simple
    calculation and rewriting: In general, unknown, hypothetical
    values (arbitrary numbers, booleans, lists, etc.) can block
    simplification.  For example, if we try to prove the following
    fact using the [simpl] tactic as above, we get stuck.  (We then
    use the [Abort] command to give up on it for the moment.)*)

Print beq_nat.

Theorem plus_1_neq_0_firsttry : forall n : nat,
    beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  simpl.  (* does nothing! *)
Abort.

Print beq_nat.

(** The reason for this is that the definitions of both
    [beq_nat] and [+] begin by performing a [match] on their first
    argument.  But here, the first argument to [+] is the unknown
    number [n] and the argument to [beq_nat] is the compound
    expression [n + 1]; neither can be simplified.

    To make progress, we need to consider the possible forms of [n]
    separately.  If [n] is [O], then we can calculate the final result
    of [beq_nat (n + 1) 0] and check that it is, indeed, [false].  And
    if [n = S n'] for some [n'], then, although we don't know exactly
    what number [n + 1] yields, we can calculate that, at least, it
    will begin with one [S], and this is enough to calculate that,
    again, [beq_nat (n + 1) 0] will yield [false].

    The tactic that tells Coq to consider, separately, the cases where
    [n = O] and where [n = S n'] is called [destruct]. *)

Theorem plus_1_neq_0 : forall n : nat,
    beq_nat (n + 1) 0 = false.
Proof.
  intros n. 
  destruct n as [ | n' ]; reflexivity. 
Qed.

(** The [destruct] generates _two_ subgoals, which we must then
    prove, separately, in order to get Coq to accept the theorem. The
    annotation "[as [| n']]" is called an _intro pattern_.  It tells
    Coq what variable names to introduce in each subgoal.  In general,
    what goes between the square brackets is a _list of lists_ of
    names, separated by [|].  In this case, the first component is
    empty, since the [O] constructor is nullary (it doesn't have any
    arguments).  The second component gives a single name, [n'], since
    [S] is a unary constructor.

    The [-] signs on the second and third lines are called _bullets_,
    and they mark the parts of the proof that correspond to each
    generated subgoal.  The proof script that comes after a bullet is
    the entire proof for a subgoal.  In this example, each of the
    subgoals is easily proved by a single use of [reflexivity], which
    itself performs some simplification -- e.g., the first one
    simplifies [beq_nat (S n' + 1) 0] to [false] by first rewriting
    [(S n' + 1)] to [S (n' + 1)], then unfolding [beq_nat], and then
    simplifying the [match].

    Marking cases with bullets is entirely optional: if bullets are
    not present, Coq simply asks you to prove each subgoal in
    sequence, one at a time. But it is a good idea to use bullets.
    For one thing, they make the structure of a proof apparent, making
    it more readable. Also, bullets instruct Coq to ensure that a
    subgoal is complete before trying to verify the next one,
    preventing proofs for different subgoals from getting mixed
    up. These issues become especially important in large
    developments, where fragile proofs lead to long debugging
    sessions.

    There are no hard and fast rules for how proofs should be
    formatted in Coq -- in particular, where lines should be broken
    and how sections of the proof should be indented to indicate their
    nested structure.  However, if the places where multiple subgoals
    are generated are marked with explicit bullets at the beginning of
    lines, then the proof will be readable almost no matter what
    choices are made about other aspects of layout.

    This is also a good place to mention one other piece of somewhat
    obvious advice about line lengths.  Beginning Coq users sometimes
    tend to the extremes, either writing each tactic on its own line
    or writing entire proofs on one line.  Good style lies somewhere
    in the middle.  One reasonable convention is to limit yourself to
    80-character lines.

    The [destruct] tactic can be used with any inductively defined
    datatype.  For example, we use it next to prove that boolean
    negation is involutive -- i.e., that negation is its own
    inverse. *)


Theorem negb_involutive : forall b : bool,
    negb (negb b) = b.
Proof.
  intros b. destruct b.
  - reflexivity.
  - reflexivity.  Qed.

(** Note that the [destruct] here has no [as] clause because
    none of the subcases of the [destruct] need to bind any variables,
    so there is no need to specify any names.  (We could also have
    written [as [|]], or [as []].)  In fact, we can omit the [as]
    clause from _any_ [destruct] and Coq will fill in variable names
    automatically.  This is generally considered bad style, since Coq
    often makes confusing choices of names when left to its own
    devices.

    It is sometimes useful to invoke [destruct] inside a subgoal,
    generating yet more proof obligations. In this case, we use
    different kinds of bullets to mark goals on different "levels."
    For example: *)


Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
Qed.

(** Each pair of calls to [reflexivity] corresponds to the
    subgoals that were generated after the execution of the [destruct c]
    line right above it. *)

(** Besides [-] and [+], we can use [*] (asterisk) as a third kind of
    bullet.  We can also enclose sub-proofs in curly braces, which is
    useful in case we ever encounter a proof that generates more than
    three levels of subgoals: *)

Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b.
  { destruct c.
    { reflexivity. }
    { reflexivity. } }
  { destruct c.
    { reflexivity. }
    { reflexivity. } }
Qed.

(** Since curly braces mark both the beginning and the end of a
    proof, they can be used for multiple subgoal levels, as this
    example shows. Furthermore, curly braces allow us to reuse the
    same bullet shapes at multiple levels in a proof: *)

Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b.
  - destruct c.
    { destruct d.
      - reflexivity.
      - reflexivity. }
    { destruct d.
      - reflexivity.
      - reflexivity. }
  - destruct c.
    { destruct d.
      - reflexivity.
      - reflexivity. }
    { destruct d.
      - reflexivity.
      - reflexivity. }
Qed.

(** Before closing the chapter, let's mention one final convenience.
    As you may have noticed, many proofs perform case analysis on a variable
    right after introducing it:

       intros x y. destruct y as [|y].

    This pattern is so common that Coq provides a shorthand for it: we
    can perform case analysis on a variable when introducing it by
    using an intro pattern instead of a variable name. For instance,
    here is a shorter proof of the [plus_1_neq_0] theorem above. *)

Theorem plus_1_neq_0' : forall n : nat,
    beq_nat (n + 1) 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.  Qed.

(** If there are no arguments to name, we can just write [[]]. *)

Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.


(* ================================================================= *)
(** ** More on Notation (Optional) *)

(** (In general, sections marked Optional are not needed to follow the
    rest of the book, except possibly other Optional sections.  On a
    first reading, you might want to skim these sections so that you
    know what's there for future reference.)

    Recall the notation definitions for infix plus and times: *)

Notation "x + y" := (plus x y)
                      (at level 50, left associativity)
                    : nat_scope.
Notation "x * y" := (mult x y)
                      (at level 40, left associativity)
                    : nat_scope.

(** For each notation symbol in Coq, we can specify its _precedence
    level_ and its _associativity_.  The precedence level [n] is
    specified by writing [at level n]; this helps Coq parse compound
    expressions.  The associativity setting helps to disambiguate
    expressions containing multiple occurrences of the same
    symbol. For example, the parameters specified above for [+] and
    [*] say that the expression [1+2*3*4] is shorthand for
    [(1+((2*3)*4))]. Coq uses precedence levels from 0 to 100, and
    _left_, _right_, or _no_ associativity.  We will see more examples
    of this later, e.g., in the [Lists]
    chapter.

    Each notation symbol is also associated with a _notation scope_.
    Coq tries to guess what scope is meant from context, so when it
    sees [S(O*O)] it guesses [nat_scope], but when it sees the
    cartesian product (tuple) type [bool*bool] (which we'll see in
    later chapters) it guesses [type_scope].  Occasionally, it is
    necessary to help it out with percent-notation by writing
    [(x*y)%nat], and sometimes in what Coq prints it will use [%nat]
    to indicate what scope a notation is in.

    Notation scopes also apply to numeral notation ([3], [4], [5],
    etc.), so you may sometimes see [0%nat], which means [O] (the
    natural number [0] that we're using in this chapter), or [0%Z],
    which means the Integer zero (which comes from a different part of
    the standard library).

    Pro tip: Coq's notation mechanism is not especially powerful.
    Don't expect too much from it! *)
