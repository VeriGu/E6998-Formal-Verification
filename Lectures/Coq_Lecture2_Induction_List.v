(** * Induction & List *)

(* ################################################################# *)
(** * Acknowledgement *)

(** The materials are borrowed from the  _Software Foundations_ series. 
    http://softwarefoundations.cis.upenn.edu 
 *)

(** Compile the lecture notes using
    [coqc Coq_Lecture1_Basics Coq_Lecture2_Induction_List]
*)


(** Before getting started, we need to import all of our
    definitions from the previous chapter: *)

Require Export Coq_Lecture1_Basics.


(** For the [Require Export] to work, you first need to use
    [coqc] to compile [Basics.v] into [Basics.vo].  This is like
    making a [.class] file from a [.java] file, or a [.o] file from a
    [.c] file.  There are two ways to do it:

     - In CoqIDE:

         Open [BasicsCoq_Lecture1_Basics.v].
         In the "Compile" menu, click on "Compile Buffer".

     - From the command line:
       [coqc Coq_Lecture1_Basics Coq_Lecture2_Induction_List]
*)

(* ################################################################# *)
(** * Proof by Induction *)

(** We proved in the last chapter that [0] is a neutral element
    for [+] on the left, using an easy argument based on
    simplification.  We also observed that proving the fact that it is
    also a neutral element on the _right_... *)

Theorem plus_n_O_firsttry : forall n:nat,
    n = n + 0.

(** ... can't be done in the same simple way.  Just applying
  [reflexivity] doesn't work, since the [n] in [n + 0] is an arbitrary
  unknown number, so the [match] in the definition of [+] can't be
  simplified.  *)

Proof.
  intros n.
  simpl.
  (* Does nothing! *)
Abort.

(** And reasoning by cases using [destruct n] doesn't get us much
    further: the branch of the case analysis where we assume [n = 0]
    goes through fine, but in the branch where [n = S n'] for some [n'] we
    get stuck in exactly the same way. *)

Theorem plus_n_O_secondtry : forall n:nat,
    n = n + 0.
Proof.
  intros n. destruct n as [| n'].
  - (* n = 0 *)
    reflexivity. (* so far so good... *)
  - (* n = S n' *)
    simpl.

    (* ...but here we are stuck again *)
Abort.

(**
(1) O \in K
(2) for n, if n \in K then S n in K
=>

every nat number is in K
 *)

(** We could use [destruct n'] to get one step further, but,
    since [n] can be arbitrarily large, if we just go on like this
    we'll never finish. *)

(** To prove interesting facts about numbers, lists, and other
    inductively defined sets, we usually need a more powerful
    reasoning principle: _induction_.

    Recall (from high school, a discrete math course, etc.) the
    _principle of induction over natural numbers_: If [P(n)] is some
    proposition involving a natural number [n] and we want to show
    that [P] holds for all numbers [n], we can reason like this:
         - show that [P(O)] holds;
         - show that, for any [n'], if [P(n')] holds, then so does
           [P(S n')];
         - conclude that [P(n)] holds for all [n].

    In Coq, the steps are the same: we begin with the goal of proving
    [P(n)] for all [n] and break it down (by applying the [induction]
    tactic) into two separate subgoals: one where we must show [P(O)]
    and another where we must show [P(n') -> P(S n')].  Here's how
    this works for the theorem at hand: *)

Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n.
  apply (nat_ind (fun n =>  n = n + 0)).
  - reflexivity.
  - intros n' IHn'.
    simpl. rewrite <- IHn'. reflexivity.
Qed.

(** Like [destruct], the [induction] tactic takes an [as...]
    clause that specifies the names of the variables to be introduced
    in the subgoals.  Since there are two subgoals, the [as...] clause
    has two parts, separated by [|].  (Strictly speaking, we can omit
    the [as...] clause and Coq will choose names for us.  In practice,
    this is a bad idea, as Coq's automatic choices tend to be
    confusing.)

    In the first subgoal, [n] is replaced by [0].  No new variables
    are introduced (so the first part of the [as...] is empty), and
    the goal becomes [0 = 0 + 0], which follows by simplification.

    In the second subgoal, [n] is replaced by [S n'], and the
    assumption [n' + 0 = n'] is added to the context with the name
    [IHn'] (i.e., the Induction Hypothesis for [n']).  These two names
    are specified in the second part of the [as...] clause.  The goal
    in this case becomes [S n' = (S n') + 0], which simplifies to
    [S n' = S (n' + 0)], which in turn follows from [IHn']. *)

(** (The use of the [intros] tactic in these proofs is actually
    redundant.  When applied to a goal that contains quantified
    variables, the [induction] tactic will automatically move them
    into the context as needed.) *)

Theorem minus_diag : forall n,
    minus n n = 0.
Proof.
  intros.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. exact IHn'.
Qed.

(** **** Exercise: 2 stars, recommended (basic_induction)  *)
(** Prove the following using induction. You might need previously proven results. *)

Theorem mult_0_r : forall n:nat,
    n * 0 = 0.
Proof.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl. exact IHn'.
Qed.

Theorem plus_n_Sm : forall n m : nat,
    S (n + m) = n + (S m).
Proof.
  induction n as [| n' IHn']; intros.
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
    n + m = m + n.
Proof.
  induction n as [| n' IHn']; intros.
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite IHn'. apply plus_n_Sm.
Qed.

(** **** Exercise: 2 stars, optional (evenb_S)  *)
(** One inconvenient aspect of our definition of [evenb n] is the
    recursive call on [n - 2]. This makes proofs about [evenb n]
    harder when done by induction on [n], since we may need an
    induction hypothesis about [n - 2]. The following lemma gives an
    alternative characterization of [evenb (S n)] that works better
    with induction: *)

Lemma double_negb: forall n, negb (negb n) = n.
Proof.
  destruct n; reflexivity.
Qed.

Theorem evenb_S : forall n : nat,
    evenb (S n) = negb (evenb n).
Proof.
  intros n. induction n as [|n' IHn'].
  - reflexivity.
  - rewrite IHn'.
    simpl.
    destruct (evenb n'); reflexivity.
Qed.

(** [] *)

(* ################################################################# *)
(** * Proofs Within Proofs *)

(** In Coq, as in informal mathematics, large proofs are often
    broken into a sequence of theorems, with later proofs referring to
    earlier theorems.  But sometimes a proof will require some
    miscellaneous fact that is too trivial and of too little general
    interest to bother giving it its own top-level name.  In such
    cases, it is convenient to be able to simply state and prove the
    needed "sub-theorem" right at the point where it is used.  The
    [assert] tactic allows us to do this. *)

Theorem evenb_S' : forall n : nat,
    evenb (S n) = negb (evenb n).
Proof.
  intros n. induction n as [|n' IHn'].
  - reflexivity.
  - rewrite IHn'.
    simpl.
    assert (Hneg_neg: forall b, b = negb (negb b)).
    {
      destruct b; reflexivity.
    }
    apply Hneg_neg.
Qed.
(** [] *)

(** The [assert] tactic introduces two sub-goals.  The first is
    the assertion itself; by prefixing it with [H:] we name the
    assertion [H].  (We can also name the assertion with [as] just as
    we did above with [destruct] and [induction], i.e., [assert (0 + n
    = n) as H].)  Note that we surround the proof of this assertion
    with curly braces [{ ... }], both for readability and so that,
    when using Coq interactively, we can see more easily when we have
    finished this sub-proof.  The second goal is the same as the one
    at the point where we invoke [assert] except that, in the context,
    we now have the assumption [H] that [0 + n = n].  That is,
    [assert] generates one subgoal where we must prove the asserted
    fact and a second subgoal where we can use the asserted fact to
    make progress on whatever we were trying to prove in the first
    place. *)


Module NatList.

  (* ################################################################# *)
  (** * Pairs of Numbers *)

  (** In an [Inductive] type definition, each constructor can take
    any number of arguments -- none (as with [true] and [O]), one (as
    with [S]), or more than one, as here: *)

  Inductive natprod :=
  | pair (n1 n2: nat).

  (** This declaration can be read: "There is just one way to
    construct a pair of numbers: by applying the constructor [pair] to
    two arguments of type [nat]." *)

  Check (pair 3 5).

  (** Here are simple functions for extracting the first and
    second components of a pair.  The definitions also illustrate how
    to do pattern matching on two-argument constructors. *)

  Definition fst (p : natprod) : nat :=
    match p with
    | pair x _ => x
    end.

  Definition snd (p : natprod) : nat :=
    match p with
    | pair _ y => y
    end.

  Compute (fst (pair 3 5)).
  (* ===> 3 *)

  (** Since pairs are used quite a bit, it is nice to be able to
    write them with the standard mathematical notation [(x,y)] instead
    of [pair x y].  We can tell Coq to allow this with a [Notation]
    declaration. *)

  Notation "( x , y )" := (pair x y).

  (** The new pair notation can be used both in expressions and in
    pattern matches (indeed, we've actually seen this already in the
    [Basics] chapter, in the definition of the [minus] function --
    this works because the pair notation is also provided as part of
    the standard library): *)

  Compute (fst (3,5)).

  Definition fst' (p : natprod) : nat :=
    match p with
    | (x,y) => x
    end.

  Definition snd' (p : natprod) : nat :=
    match p with
    | (x,y) => y
    end.

  Definition swap_pair (p : natprod) : natprod :=
    match p with
    | (x,y) => (y,x)
    end.

  (** Let's try to prove a few simple facts about pairs.

    If we state things in a slightly peculiar way, we can complete
    proofs with just reflexivity (and its built-in simplification): *)

  Theorem surjective_pairing' : forall (n m : nat),
      (n,m) = (fst (n,m), snd (n,m)).
  Proof.
    reflexivity.  Qed.

  (** But [reflexivity] is not enough if we state the lemma in a more
    natural way: *)

  Theorem surjective_pairing_stuck : forall (p : natprod),
      p = (fst p, snd p).
  Proof.
    destruct p. reflexivity.
  Abort.

  (** We have to expose the structure of [p] so that [simpl] can
    perform the pattern match in [fst] and [snd].  We can do this with
    [destruct]. *)

  Theorem surjective_pairing : forall (p : natprod),
      p = (fst p, snd p).
  Proof.
    intros p.  destruct p as [n m].  simpl.  reflexivity.  Qed.

  (** Notice that, unlike its behavior with [nat]s, [destruct]
    generates just one subgoal here.  That's because [natprod]s can
    only be constructed in one way. *)


  (* ################################################################# *)
  (** * Lists of Numbers *)


  (** Generalizing the definition of pairs, we can describe the
    type of _lists_ of numbers like this: "A list is either the empty
    list or else a pair of a number and another list." *)

  Inductive natlist :=
  | nil
  | cons (n : nat) (l: natlist).

  (** For example, here is a three-element list: *)

  Definition mylist := cons 1 (cons 2 (cons 3 nil)).

  (** As with pairs, it is more convenient to write lists in
    familiar programming notation.  The following declarations
    allow us to use [::] as an infix [cons] operator and square
    brackets as an "outfix" notation for constructing lists. *)

  Notation "x :: l" := (cons x l)
                         (at level 60, right associativity).
  Notation "[ ]" := nil.
  Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

  (** It is not necessary to understand the details of these
    declarations, but in case you are interested, here is roughly
    what's going on.  The [right associativity] annotation tells Coq
    how to parenthesize expressions involving several uses of [::] so
    that, for example, the next three declarations mean exactly the
    same thing: *)

  Definition mylist1 := 1 :: (2 :: (3 :: nil)).
  Definition mylist2 := 1 :: 2 :: 3 :: nil.
  Definition mylist3 := [1;2;3].

  (** The [at level 60] part tells Coq how to parenthesize
    expressions that involve both [::] and some other infix operator.
    For example, since we defined [+] as infix notation for the [plus]
    function at level 50,

  Notation "x + y" := (plus x y)
                      (at level 50, left associativity).

    the [+] operator will bind tighter than [::], so [1 + 2 :: [3]]
    will be parsed, as we'd expect, as [(1 + 2) :: [3]] rather than [1
    + (2 :: [3])].

    (Expressions like "[1 + 2 :: [3]]" can be a little confusing when
    you read them in a [.v] file.  The inner brackets, around 3, indicate
    a list, but the outer brackets, which are invisible in the HTML
    rendering, are there to instruct the "coqdoc" tool that the bracketed
    part should be displayed as Coq code rather than running text.)

    The second and third [Notation] declarations above introduce the
    standard square-bracket notation for lists; the right-hand side of
    the third one illustrates Coq's syntax for declaring n-ary
    notations and translating them to nested sequences of binary
    constructors. *)

  (* ----------------------------------------------------------------- *)
  (** *** Repeat *)

  (** A number of functions are useful for manipulating lists.
    For example, the [repeat] function takes a number [n] and a
    [count] and returns a list of length [count] where every element
    is [n]. *)

  Fixpoint repeat (n count : nat) : natlist :=
    match count with
    | O => nil
    | S count' => n :: (repeat n count')
    end.

  Compute (repeat 3 5).

  (* ----------------------------------------------------------------- *)
  (** *** Length *)

  (** The [length] function calculates the length of a list. *)

  Fixpoint length (l:natlist) : nat :=
    match l with
    | nil => O
    | cons _ l' => S (length l')
    end.

  Compute (length (repeat 3 5)).

  Lemma repeat_length_correct:
    forall n count, length(repeat n count) = count.
  Proof.
    intros. induction count as [|count' IHcount'].
    - reflexivity.
    - simpl. rewrite IHcount'. reflexivity.
  Qed.

  (* ----------------------------------------------------------------- *)
  (** *** Append *)

  (** The [app] function concatenates (appends) two lists. *)

  Fixpoint app (l1 l2 : natlist) : natlist :=
    match l1 with
    | [] => l2
    | t:: l' => t :: (app l' l2)
    end.

  (** Actually, [app] will be used a lot in some parts of what
    follows, so it is convenient to have an infix operator for it. *)

  Notation "x ++ y" := (app x y)
                         (right associativity, at level 60).

  Example test_app1:             [1;2;3] ++ [4;5] = [1;2;3;4;5].
  Proof. reflexivity.  Qed.
  Compute (nil ++ [4;5]).
  Example test_app3:             [1;2;3] ++ nil = [1;2;3].
  Proof. reflexivity.  Qed.

  (* ----------------------------------------------------------------- *)
  (** *** Head (with default) and Tail *)

  (** Here are two smaller examples of programming with lists.
    The [hd] function returns the first element (the "head") of the
    list, while [tl] returns everything but the first
    element (the "tail").
    Of course, the empty list has no first element, so we
    must pass a default value to be returned in that case.  *)

  Definition hd (l:natlist) :=
    match l with
    | nil => None
    | h :: t => Some h
    end.

  Compute (hd []).


  Definition tl (l:natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => t
    end.


  (* ################################################################# *)
  (** * Reasoning About Lists *)

  (** As with numbers, simple facts about list-processing
    functions can sometimes be proved entirely by simplification.  For
    example, the simplification performed by [reflexivity] is enough
    for this theorem... *)

  Theorem nil_app : forall l:natlist,
      [] ++ l = l.
  Proof. reflexivity. Qed.

  (** ...because the [[]] is substituted into the
    "scrutinee" (the expression whose value is being "scrutinized" by
    the match) in the definition of [app], allowing the match itself
    to be simplified. *)

  (** Also, as with numbers, it is sometimes helpful to perform case
    analysis on the possible shapes (empty or non-empty) of an unknown
    list. *)

  Theorem tl_length_pred : forall l:natlist,
      pred (length l) = length (tl l).
  Proof.
    induction l as [| n l' IHl'].
    - (* l = nil *)
      reflexivity.
    - (* l = cons n l' *)
      simpl.
      reflexivity.
  Qed.

  (** Here, the [nil] case works because we've chosen to define
    [tl nil = nil]. Notice that the [as] annotation on the [destruct]
    tactic here introduces two names, [n] and [l'], corresponding to
    the fact that the [cons] constructor for lists takes two
    arguments (the head and tail of the list it is constructing). *)

  (** Usually, though, interesting theorems about lists require
    induction for their proofs. *)

  (* ----------------------------------------------------------------- *)
  (** *** Micro-Sermon *)

  (** Simply reading example proof scripts will not get you very far!
    It is important to work through the details of each one, using Coq
    and thinking about what each step achieves.  Otherwise it is more
    or less guaranteed that the exercises will make no sense when you
    get to them.  'Nuff said. *)

  (* ================================================================= *)
  (** ** Induction on Lists *)

  (** Proofs by induction over datatypes like [natlist] are a
    little less familiar than standard natural number induction, but
    the idea is equally simple.  Each [Inductive] declaration defines
    a set of data values that can be built up using the declared
    constructors: a boolean can be either [true] or [false]; a number
    can be either [O] or [S] applied to another number; a list can be
    either [nil] or [cons] applied to a number and a list.

    Moreover, applications of the declared constructors to one another
    are the _only_ possible shapes that elements of an inductively
    defined set can have, and this fact directly gives rise to a way
    of reasoning about inductively defined sets: a number is either
    [O] or else it is [S] applied to some _smaller_ number; a list is
    either [nil] or else it is [cons] applied to some number and some
    _smaller_ list; etc. So, if we have in mind some proposition [P]
    that mentions a list [l] and we want to argue that [P] holds for
    _all_ lists, we can reason as follows:

      - First, show that [P] is true of [l] when [l] is [nil].

      - Then show that [P] is true of [l] when [l] is [cons n l'] for
        some number [n] and some smaller list [l'], assuming that [P]
        is true for [l'].

    Since larger lists can only be built up from smaller ones,
    eventually reaching [nil], these two arguments together establish
    the truth of [P] for all lists [l].  Here's a concrete example: *)

  Theorem app_assoc : forall l1 l2 l3 : natlist,
      (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
  Proof.
    intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
    - (* l1 = nil *)
      reflexivity.
    - (* l1 = cons n l1' *)
      simpl. rewrite -> IHl1'. reflexivity.  Qed.

  (* ----------------------------------------------------------------- *)
  (** *** Reversing a List *)

  (** For a slightly more involved example of inductive proof over
    lists, suppose we use [app] to define a list-reversing function
    [rev]: *)

  Fixpoint rev (l:natlist) : natlist :=
    match l with
    | [] => []
    | t :: l' => (rev l') ++ [t]
    end.

  Compute (rev [1;2;3]).

  (* ----------------------------------------------------------------- *)
  (** *** Properties of [rev] *)

  (** Now let's prove some theorems about our newly defined [rev].
    For something a bit more challenging than what we've seen, let's
    prove that reversing a list does not change its length.  Our first
    attempt gets stuck in the successor case... *)

  Lemma length_app:
    forall l1 l2, length (l1 ++ l2) = length l1 + length l2.
  Proof.
    intros.
    induction l1 as [| n l' IHl'].
    - simpl. reflexivity.
    - simpl. rewrite IHl'. reflexivity.
  Qed.

  
  Theorem rev_length_firsttry : forall l : natlist,
      length (rev l) = length l.
  Proof.
    induction l as [| n l' IHl'].
    - (* l = [] *)
      reflexivity.
    - (* l = n :: l' *)
      (* This is the tricky case.  Let's begin as usual
       by simplifying. *)
      simpl. rewrite length_app.
      rewrite IHl'.
      simpl.
      rewrite plus_comm.
      reflexivity.
  Qed.

End NatList.


(* ################################################################# *)
(** * Polymorphism *)

(** In this chapter we continue our development of basic
    concepts of functional programming.  The critical new ideas are
    _polymorphism_ (abstracting functions over the types of the data
    they manipulate) and _higher-order functions_ (treating functions
    as data).  We begin with polymorphism. *)

(* ================================================================= *)
(** ** Polymorphic Lists *)

(** For the last couple of chapters, we've been working just
    with lists of numbers.  Obviously, interesting programs also need
    to be able to manipulate lists with elements from other types --
    lists of strings, lists of booleans, lists of lists, etc.  We
    _could_ just define a new inductive datatype for each of these,
    for example... *)

Inductive boollist : Type :=
| bool_nil : boollist
| bool_cons : bool -> boollist -> boollist.

(** ... but this would quickly become tedious, partly because we
    have to make up different constructor names for each datatype, but
    mostly because we would also need to define new versions of all
    our list manipulating functions ([length], [rev], etc.) for each
    new datatype definition. *)

(** To avoid all this repetition, Coq supports _polymorphic_
    inductive type definitions.  For example, here is a _polymorphic
    list_ datatype. *)

Inductive list (X:Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.


(** This is exactly like the definition of [natlist] from the
    previous chapter, except that the [nat] argument to the [cons]
    constructor has been replaced by an arbitrary type [X], a binding
    for [X] has been added to the header, and the occurrences of
    [natlist] in the types of the constructors have been replaced by
    [list X].  (We can re-use the constructor names [nil] and [cons]
    because the earlier definition of [natlist] was inside of a
    [Module] definition that is now out of scope.)

    What sort of thing is [list] itself?  One good way to think
    about it is that [list] is a _function_ from [Type]s to
    [Inductive] definitions; or, to put it another way, [list] is a
    function from [Type]s to [Type]s.  For any particular type [X],
    the type [list X] is an [Inductive]ly defined set of lists whose
    elements are of type [X]. *)

Check (list nat).
(* ===> list : Type -> Type *)

(** What might the type of [nil] be? We can read off the type [list X]
    from the definition, but this omits the binding for [X] which is
    the parameter to [list]. [Type -> list X] does not explain the
    meaning of [X]. [(X : Type) -> list X] comes closer. Coq's
    notation for this situation is [forall X : Type, list X]. *)

Check nil.

(** The parameter [X] in the definition of [list] becomes a parameter
    to the constructors [nil] and [cons] -- that is, [nil] and [cons]
    are now polymorphic constructors, that need to be supplied with
    the type of the list they are building. As an example, [nil nat]
    constructs the empty list of type [nat]. *)

Check (nil nat).
(* ===> nil nat : list nat *)

(** Similarly, [cons nat] adds an element of type [nat] to a list of
    type [list nat]. Here is an example of forming a list containing
    just the natural number 3.*)

Check (cons nat 3 (nil nat)).
(* ===> cons nat 3 (nil nat) : list nat *)

(** We can now go back and make polymorphic versions of all the
    list-processing functions that we wrote before.  Here is [repeat],
    for example: *)

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S n' => cons X x (repeat X x n')
  end.

Compute (repeat nat 4 2).
(** As with [nil] and [cons], we can use [repeat] by applying it
    first to a type and then to an element of this type (and a number): *)

(* ----------------------------------------------------------------- *)
(** *** Type Annotation Inference *)

(** Let's write the definition of [repeat] again, but this time we
    won't specify the types of any of the arguments.  Will Coq still
    accept it? *)

Fixpoint repeat' X x count :=
  match count with
  | 0        => nil X
  | S count' => cons X x (repeat' X x count')
  end.

(** Indeed it will.  Let's see what type Coq has assigned to [repeat']: *)

Check repeat'.
(* ===> forall X : Type, X -> nat -> list X *)
Check repeat.
(* ===> forall X : Type, X -> nat -> list X *)

(** It has exactly the same type as [repeat].  Coq was able
    to use _type inference_ to deduce what the types of [X], [x], and
    [count] must be, based on how they are used.  For example, since
    [X] is used as an argument to [cons], it must be a [Type], since
    [cons] expects a [Type] as its first argument; matching [count]
    with [0] and [S] means it must be a [nat]; and so on.

    This powerful facility means we don't always have to write
    explicit type annotations everywhere, although explicit type
    annotations are still quite useful as documentation and sanity
    checks, so we will continue to use them most of the time.  You
    should try to find a balance in your own code between too many
    type annotations (which can clutter and distract) and too
    few (which forces readers to perform type inference in their heads
    in order to understand your code). *)

(* ----------------------------------------------------------------- *)
(** *** Type Argument Synthesis *)

(** To use a polymorphic function, we need to pass it one or
    more types in addition to its other arguments.  For example, the
    recursive call in the body of the [repeat] function above must
    pass along the type [X].  But since the second argument to
    [repeat] is an element of [X], it seems entirely obvious that the
    first argument can only be [X] -- why should we have to write it
    explicitly?

    Fortunately, Coq permits us to avoid this kind of redundancy.  In
    place of any type argument we can write the "implicit argument"
    [_], which can be read as "Please try to figure out for yourself
    what belongs here."  More precisely, when Coq encounters a [_], it
    will attempt to _unify_ all locally available information -- the
    type of the function being applied, the types of the other
    arguments, and the type expected by the context in which the
    application appears -- to determine what concrete type should
    replace the [_].

    This may sound similar to type annotation inference -- indeed, the
    two procedures rely on the same underlying mechanisms.  Instead of
    simply omitting the types of some arguments to a function, like

      repeat' X x count : list X :=

    we can also replace the types with [_]

      repeat' (X : _) (x : _) (count : _) : list X :=

    to tell Coq to attempt to infer the missing information.

    Using implicit arguments, the [repeat] function can be written like
    this: *)

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0        => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

(** In this instance, we don't save much by writing [_] instead of
    [X].  But in many cases the difference in both keystrokes and
    readability is nontrivial.  For example, suppose we want to write
    down a list containing the numbers [1], [2], and [3].  Instead of
    writing this... *)

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

(** ...we can use argument synthesis to write this: *)

Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

(* ----------------------------------------------------------------- *)
(** *** Implicit Arguments *)

(** We can go further and even avoid writing [_]'s in most cases by
    telling Coq _always_ to infer the type argument(s) of a given
    function.

    The [Arguments] directive specifies the name of the function (or
    constructor) and then lists its argument names, with curly braces
    around any arguments to be treated as implicit.  (If some
    arguments of a definition don't have a name, as is often the case
    for constructors, they can be marked with a wildcard pattern
    [_].) *)

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

(** Now, we don't have to supply type arguments at all: *)

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

(** Alternatively, we can declare an argument to be implicit
    when defining the function itself, by surrounding it in curly
    braces instead of parens.  For example: *)

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0        => nil
  | S count' => cons x (repeat''' x count')
  end.

(** (Note that we didn't even have to provide a type argument to the
    recursive call to [repeat''']; indeed, it would be invalid to
    provide one!)

    We will use the latter style whenever possible, but we will
    continue to use explicit [Argument] declarations for [Inductive]
    constructors.  The reason for this is that marking the parameter
    of an inductive type as implicit causes it to become implicit for
    the type itself, not just for its constructors.  For instance,
    consider the following alternative definition of the [list]
    type: *)

Inductive list' {X:Type} : Type :=
| nil' : list'
| cons' : X -> list' -> list'.

(** Because [X] is declared as implicit for the _entire_ inductive
    definition including [list'] itself, we now have to write just
    [list'] whether we are talking about lists of numbers or booleans
    or anything else, rather than [list' nat] or [list' bool] or
    whatever; this is a step too far. *)

(** Let's finish by re-implementing a few other standard list
    functions on our new polymorphic lists... *)

Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil      => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity.  Qed.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity.  Qed.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity.  Qed.

Check (cons 1 nil).

(* ----------------------------------------------------------------- *)
(** *** Supplying Type Arguments Explicitly *)

(** One small problem with declaring arguments [Implicit] is
    that, occasionally, Coq does not have enough local information to
    determine a type argument; in such cases, we need to tell Coq that
    we want to give the argument explicitly just this time.  For
    example, suppose we write this: *)

Definition mynil: list nat := nil.

(** (The [Fail] qualifier that appears before [Definition] can be
    used with _any_ command, and is used to ensure that that command
    indeed fails when executed. If the command does fail, Coq prints
    the corresponding error message, but continues processing the rest
    of the file.)

    Here, Coq gives us an error because it doesn't know what type
    argument to supply to [nil].  We can help it by providing an
    explicit type declaration (so that Coq has more information
    available when it gets to the "application" of [nil]): *)

(** Alternatively, we can force the implicit arguments to be explicit by
   prefixing the function name with [@]. *)

Check nil.
Check @nil.

Definition mynil' := @nil nat.

(** Using argument synthesis and implicit arguments, we can
    define convenient notation for lists, as before.  Since we have
    made the constructor type arguments implicit, Coq will know to
    automatically infer these when we use the notations. *)

Notation "x :: y" := (cons x y)
                       (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                       (at level 60, right associativity).

(** Now lists can be written just the way we'd hope: *)

Definition list123''' := [1; 2; 3].

(* ----------------------------------------------------------------- *)
(** *** Exercises *)

(** **** Exercise: 2 stars, optional (poly_exercises)  *)
(** Here are a few simple exercises, just like ones in the [Lists]
    chapter, for practice with polymorphism.  Complete the proofs below. *)

Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  induction l as [| h l' IHl'].
  - reflexivity.
  - simpl. rewrite IHl'. reflexivity.
Qed.

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  induction l as [| h l' IHl'].
  - reflexivity.
  - simpl. intros. rewrite IHl'. reflexivity.
Qed.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  induction l1 as [| h l' IHl'].
  - reflexivity.
  - simpl. intros. rewrite IHl'. reflexivity.
Qed.

(** **** Exercise: 2 stars, optional (more_poly_exercises)  *)
(** Here are some slightly more interesting ones... *)

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  induction l1 as [| h l' IHl']; intros; simpl.
  - rewrite app_nil_r. 
    reflexivity.
  - rewrite IHl'. rewrite app_assoc.
    reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  induction l as [| h l' IHl'].
  - reflexivity.
  - simpl. rewrite rev_app_distr. rewrite IHl'.
    reflexivity.
Qed.

(* ################################################################# *)
(** * Functions as Data *)

(** Like many other modern programming languages -- including
    all functional languages (ML, Haskell, Scheme, Scala, Clojure,
    etc.) -- Coq treats functions as first-class citizens, allowing
    them to be passed as arguments to other functions, returned as
    results, stored in data structures, etc.*)

(* ================================================================= *)
(** ** Higher-Order Functions *)

(** Functions that manipulate other functions are often called
    _higher-order_ functions.  Here's a simple one: *)

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

(** The argument [f] here is itself a function (from [X] to
    [X]); the body of [doit3times] applies [f] three times to some
    value [n]. *)

Check @doit3times.
(* ===> doit3times : forall X : Type, (X -> X) -> X -> X *)

Print minustwo.
Compute (doit3times minustwo 8).
Print negb.
Compute (doit3times negb true).

(* ================================================================= *)
(** ** Filter *)

(** Here is a more useful higher-order function, taking a list
    of [X]s and a _predicate_ on [X] (a function from [X] to [bool])
    and "filtering" the list, returning a new list containing just
    those elements for which the predicate returns [true]. *)

Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | []     => []
  | h :: t => if test h then h :: (filter test t)
                        else       filter test t
  end.

(** For example, if we apply [filter] to the predicate [evenb]
    and a list of numbers [l], it returns a list containing just the
    even members of [l]. *)

Compute (filter oddb [1;2;3;4]).

(* ================================================================= *)
(** ** Anonymous Functions *)

(** We can construct a function
    "on the fly" without declaring it at the top level or giving it a
    name. *)

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity.  Qed.
