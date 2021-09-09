(** * Tactics & Logic *)

(* ################################################################# *)
(** * Acknowledgement *)

(** The materials are borrowed from the  _Software Foundations_ series.
    http://softwarefoundations.cis.upenn.edu
 *)

(** Compile the lecture notes using
    [coqc Coq_Lecture1_Basics Coq_Lecture2_Induction_List Coq_Lecture3_Tactics_Logic]
*)

(** This chapter introduces several additional proof strategies
    and tactics that allow us to begin proving more interesting
    properties of functional programs.  We will see:

    - how to use auxiliary lemmas in both "forward-style" and
      "backward-style" proofs;
    - how to reason about data constructors (in particular, how to use
      the fact that they are injective and disjoint);
    - how to strengthen an induction hypothesis (and when such
      strengthening is required); and
    - more details on how to reason by case analysis. *)

Require Export Coq_Lecture2_Induction_List.

(* ################################################################# *)
(** * The [apply] Tactic *)

(** We often encounter situations where the goal to be proved is
    _exactly_ the same as some hypothesis in the context or some
    previously proved lemma. *)

Theorem silly1 : forall (n m o p : nat),
    n = m  ->
    [n;o] = [n;p] ->
    [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.

  (** Here, we could finish with "[rewrite -> eq2.  reflexivity.]" as we
    have done several times before.  We can achieve the same effect in
    a single step by using the [apply] tactic instead: *)

  exact eq2.  Qed.

(** The [apply] tactic also works with _conditional_ hypotheses
    and lemmas: if the statement being applied is an implication, then
    the premises of this implication will be added to the list of
    subgoals needing to be proved. *)

Theorem silly2 : forall (n m o p : nat),
    n = m  ->
    (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
    [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.

  (*
   A -> B   A
=================== (->e)
         B
   *)

  apply eq2.

  
  (** Typically, when we use [apply H], the statement [H] will
    begin with a [forall] that binds some _universal variables_.  When
    Coq matches the current goal against the conclusion of [H], it
    will try to find appropriate values for these variables.  For
    example, when we do [apply eq2] in the following proof, the
    universal variable [q] in [eq2] gets instantiated with [n] and [r]
    gets instantiated with [m]. *)

  apply eq1.  Qed.

(** To use the [apply] tactic, the (conclusion of the) fact
    being applied must match the goal exactly -- for example, [apply]
    will not work if the left and right sides of the equality are
    swapped. *)

Theorem silly3_firsttry : forall (n : nat),
    true = beq_nat n 5  ->
    beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.

  (** Here we cannot use [apply] directly, but we can use the [symmetry]
    tactic, which switches the left and right sides of an equality in
    the goal. *)
  simpl.
  
  symmetry.
  apply H.  Qed.

(** **** Exercise: 3 stars (apply_exercise1)  *)
(** (_Hint_: You can use [apply] with previously defined lemmas, not
    just hypotheses in the context.  Remember that [Search] is
    your friend.) *)

Theorem rev_exercise1 : forall (l l' : list nat),
    l = rev l' ->
    l' = rev l.
Proof.
  intros l l' Hl.
  rewrite Hl.
  symmetry.
  Search rev.
  apply rev_involutive.
Qed.


(* ################################################################# *)
(** * The [apply with] Tactic *)

Theorem trans_eq : forall (X:Type) (n m o : X),
    n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2.
  rewrite -> eq1. rewrite -> eq2.
  reflexivity.  Qed.

(** Now, we should be able to use [trans_eq] to prove the above
    example.  However, to do this we need a slight refinement of the
    [apply] tactic. *)

Example trans_eq_example' : forall (a b c d e f : nat),
    [a;b] = [c;d] ->
    [c;d] = [e;f] ->
    [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  eapply trans_eq.
  apply eq1.
  apply eq2.
  
(** If we simply tell Coq [apply trans_eq] at this point, it can
    tell (by matching the goal against the conclusion of the lemma)
    that it should instantiate [X] with [[nat]], [n] with [[a,b]], and
    [o] with [[e,f]].  However, the matching process doesn't determine
    an instantiation for [m]: we have to supply one explicitly by
    adding [with (m:=[c,d])] to the invocation of [apply]. *)
Qed.

(** Actually, we usually don't have to include the name [m] in
    the [with] clause; Coq is often smart enough to figure out which
    instantiation we're giving. We could instead write: [apply
    trans_eq with [c;d]]. *)

(* ################################################################# *)
(** * The [inversion] Tactic *)

(** Recall the definition of natural numbers:

     Inductive nat : Type :=
       | O : nat
       | S : nat -> nat.

S n = S m <-> n = m

    It is obvious from this definition that every number has one of
    two forms: either it is the constructor [O] or it is built by
    applying the constructor [S] to another number.  But there is more
    here than meets the eye: implicit in the definition (and in our
    informal understanding of how datatype declarations work in other
    programming languages) are two more facts:

    - The constructor [S] is _injective_.  That is, if [S n = S m], it
      must be the case that [n = m].

    - The constructors [O] and [S] are _disjoint_.  That is, [O] is not
      equal to [S n] for any [n].

    Similar principles apply to all inductively defined types: all
    constructors are injective, and the values built from distinct
    constructors are never equal.  For lists, the [cons] constructor
    is injective and [nil] is different from every non-empty list.
    For booleans, [true] and [false] are different.  (Since neither
    [true] nor [false] take any arguments, their injectivity is not
    interesting.)  And so on. *)

(** Coq provides a tactic called [inversion] that allows us to
    exploit these principles in proofs. To see how to use it, let's
    show explicitly that the [S] constructor is injective: *)

Theorem S_injective : forall (n m : nat),
    S n = S m ->
    n = m.
Proof.
  intros n m H.

  (** By writing [inversion H] at this point, we are asking Coq to
    generate all equations that it can infer from [H] as additional
    hypotheses, replacing variables in the goal as it goes. In the
    present example, this amounts to adding a new hypothesis [H1 : n =
    m] and replacing [n] by [m] in the goal. *)

  inversion H.
  reflexivity.
Qed.

(** Here's a more interesting example that shows how multiple
    equations can be derived at once. *)

Theorem inversion_ex1 : forall (n m o : nat),
    [n; m] = [o; o] ->
    [n] = [m].
Proof.
  intros n m o H.
  inversion H. reflexivity. Qed.

(** We can name the equations that [inversion] generates with an
    [as ...] clause: *)

Theorem inversion_ex2 : forall (n m : nat),
    [n] = [m] ->
    n = m.
Proof.
  intros n m H. inversion H as [Hnm]. reflexivity.  Qed.

(** **** Exercise: 1 star (inversion_ex3)  *)
Example inversion_ex3 : forall (X : Type) (x y z w : X) (l j : list X),
    x :: y :: l = w :: z :: j ->
    x :: l = z :: j ->
    x = y.
Proof.
  intros.
  inversion H0.
  inversion H.
  trivial.
Qed.

(** When used on a hypothesis involving an equality between
    _different_ constructors (e.g., [S n = O]), [inversion] solves the
    goal immediately.  Consider the following proof: *)

Theorem inversion_ex4 : forall (n : nat),
    S n = O ->
    2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

(** If you find the principle of explosion confusing, remember
    that these proofs are not actually showing that the conclusion of
    the statement holds.  Rather, they are arguing that, if the
    nonsensical situation described by the premise did somehow arise,
    then the nonsensical conclusion would follow.  We'll explore the
    principle of explosion of more detail in the next chapter. *)

(** **** Exercise: 1 star (inversion_ex6)  *)
Example inversion_ex6 : forall (X : Type)
                               (x y z : X) (l j : list X),
    cons x (y :: l) = nil ->
    y :: l = z :: j ->
    x = z.
Proof.
  intros.
  inversion H.
Qed.

(** To summarize this discussion, suppose [H] is a hypothesis in the
    context or a previously proven lemma of the form

        c a1 a2 ... an = d b1 b2 ... bm

    for some constructors [c] and [d] and arguments [a1 ... an] and
    [b1 ... bm].  Then [inversion H] has the following effect:

    - If [c] and [d] are the same constructor, then, by the
      injectivity of this constructor, we know that [a1 = b1], [a2 =
      b2], etc.  The [inversion H] adds these facts to the context and
      tries to use them to rewrite the goal.

    - If [c] and [d] are different constructors, then the hypothesis
      [H] is contradictory, and the current goal doesn't have to be
      considered at all.  In this case, [inversion H] marks the
      current goal as completed and pops it off the goal stack. *)

(** The injectivity of constructors allows us to reason that
    [forall (n m : nat), S n = S m -> n = m].  The converse of this
    implication is an instance of a more general fact about both
    constructors and functions, which we will find convenient in a few
    places below: *)


Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
    x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq.  reflexivity.  Qed.

(* ################################################################# *)
(** * Using Tactics on Hypotheses *)

(** By default, most tactics work on the goal formula and leave
    the context unchanged.  However, most tactics also have a variant
    that performs a similar operation on a statement in the context.

    For example, the tactic [simpl in H] performs simplification in
    the hypothesis named [H] in the context. *)

Theorem S_inj : forall (n m : nat) (b : bool),
    beq_nat (S n) (S m) = b  ->
    beq_nat (S n) (S m) = b.
Proof.
  intros n m b H. pose H as H0. simpl in *. apply H.  Qed.

(** Similarly, [apply L in H] matches some conditional statement
    [L] (of the form [L1 -> L2], say) against a hypothesis [H] in the
    context.  However, unlike ordinary [apply] (which rewrites a goal
    matching [L2] into a subgoal [L1]), [apply L in H] matches [H]
    against [L1] and, if successful, replaces it with [L2].

    In other words, [apply L in H] gives us a form of "forward
    reasoning": from [L1 -> L2] and a hypothesis matching [L1], it
    produces a hypothesis matching [L2].  By contrast, [apply L] is
    "backward reasoning": it says that if we know [L1->L2] and we are
    trying to prove [L2], it suffices to prove [L1].

    Here is a variant of a proof from above, using forward reasoning
    throughout instead of backward reasoning. *)

Theorem silly3' : forall (n : nat),
    (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
    true = beq_nat n 5  ->
    true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H.  Qed.

(** Forward reasoning starts from what is _given_ (premises,
    previously proven theorems) and iteratively draws conclusions from
    them until the goal is reached.  Backward reasoning starts from
    the _goal_, and iteratively reasons about what would imply the
    goal, until premises or previously proven theorems are reached.
    If you've seen informal proofs before (for example, in a math or
    computer science class), they probably used forward reasoning.  In
    general, idiomatic use of Coq tends to favor backward reasoning,
    but in some situations the forward style can be easier to think
    about.  *)

(** **** Exercise: 3 stars, recommended (plus_n_n_injective)  *)
(** Practice using "in" variants in this proof.  (Hint: use
    [plus_n_Sm].) *)

Print plus_n_Sm.

Theorem plus_n_n_injective :
  forall n m,
    n + n = m + m ->
    n = m.
Proof.
  induction n.
  - intros. simpl in H.
    destruct m.
    + reflexivity.
    + inversion H.
  - intros. rename m into m0.
    pose plus_n_Sm.
    destruct m0.
    + inversion H.
    + simpl in H.
      rewrite <- e in H.
      rewrite <- e in H.
      inversion H.
      apply IHn in H1.
      rewrite H1.
      reflexivity.
Qed.

(* ################################################################# *)
(** * Unfolding Definitions *)

(** It sometimes happens that we need to manually unfold a Definition
    so that we can manipulate its right-hand side.  For example, if we
    define... *)


Definition foo (x: nat) := 5.

(** ... and try to prove a simple fact about [foo]... *)

Lemma foo_eq : forall n m, foo (n + 1) = foo (m + 1).
Proof.
  intros n m. reflexivity.
Qed.

(** At this point, a deeper discussion of unfolding and simplification
    is in order.

    You may already have observed that tactics like [simpl],
    [reflexivity], and [apply] will often unfold the definitions of
    functions automatically when this allows them to make progress.  For
    example, *)

(** Then the [simpl] in the following proof (or the [reflexivity], if
    we omit the [simpl]) will unfold [foo m] to [(fun x => 5) m] and
    then further simplify this expression to just [5]. *)

Lemma foo_eq' : forall n m, foo (n + 1) + 1 = foo m + 1.
Proof.
  intros n m.
  reflexivity.
Qed.

(** However, this automatic unfolding is rather conservative.  For
    example, if we define a slightly more complicated function
    involving a pattern match... *)

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

(** ...then the analogous proof will get stuck: *)

Lemma bar_eq_FAILED : forall m, bar (m + 1) + 1 = bar m + 1.
Proof.
  intros m.
  simpl. (* Does nothing! *)
Abort.

(** The reason that [simpl] doesn't make progress here is that it
    notices that, after tentatively unfolding [bar m], it is left with
    a match whose scrutinee, [m], is a variable, so the [match] cannot
    be simplified further.  It is not smart enough to notice that the
    two branches of the [match] are identical, so it gives up on
    unfolding [bar m] and leaves it alone.  Similarly, tentatively
    unfolding [bar (m+1)] leaves a [match] whose scrutinee is a
    function application (that, itself, cannot be simplified, even
    after unfolding the definition of [+]), so [simpl] leaves it
    alone. *)

(** At this point, there are two ways to make progress.  One is to use
    [destruct m] to break the proof into two cases, each focusing on a
    more concrete choice of [m] ([O] vs [S _]).  In each case, the
    [match] inside of [bar] can now make progress, and the proof is
    easy to complete. *)

Lemma bar_eq : forall m, bar (m + 1) + 1 = bar m + 1.
Proof.
  intros m.
  destruct m.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(* ################################################################# *)
(** * Using [destruct] on Compound Expressions *)

(** We have seen many examples where [destruct] is used to
    perform case analysis of the value of some variable.  But
    sometimes we need to reason by cases on the result of some
    _expression_.  We can also do this with [destruct].

    Here are some examples: *)

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
    sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (beq_nat n 3).
  - (* beq_nat n 3 = true *) reflexivity.
  - (* beq_nat n 3 = false *)  reflexivity. Qed.

(** After unfolding [sillyfun] in the above proof, we find that
    we are stuck on [if (beq_nat n 3) then ... else ...].  But either
    [n] is equal to [3] or it isn't, so we can use [destruct (beq_nat
    n 3)] to let us reason about the two cases.

    In general, the [destruct] tactic can be used to perform case
    analysis of the results of arbitrary computations.  If [e] is an
    expression whose type is some inductively defined type [T], then,
    for each constructor [c] of [T], [destruct e] generates a subgoal
    in which all occurrences of [e] (in the goal and in the context)
    are replaced by [c]. *)

(** However, [destruct]ing compound expressions requires a bit of
    care, as such [destruct]s can sometimes erase information we need
    to complete a proof. *)
(** For example, suppose we define a function [sillyfun1] like
    this: *)

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else false.

(** Now suppose that we want to convince Coq of the (rather
    obvious) fact that [sillyfun1 n] yields [true] only when [n] is
    odd.  By analogy with the proofs we did with [sillyfun] above, it
    is natural to start the proof like this: *)

Theorem sillyfun1_odd_FAILED : forall (n : nat),
    sillyfun1 n = true ->
    oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3).
  (* stuck... *)
Abort. 

(** We get stuck at this point because the context does not
    contain enough information to prove the goal!  The problem is that
    the substitution performed by [destruct] is too brutal -- it threw
    away every occurrence of [beq_nat n 3], but we need to keep some
    memory of this expression and how it was destructed, because we
    need to be able to reason that, since [beq_nat n 3 = true] in this
    branch of the case analysis, it must be that [n = 3], from which
    it follows that [n] is odd.

    What we would really like is to substitute away all existing
    occurences of [beq_nat n 3], but at the same time add an equation
    to the context that records which case we are in.  The [eqn:]
    qualifier allows us to introduce such an equation, giving it a
    name that we choose. *)

Theorem sillyfun1_odd : forall (n : nat),
    sillyfun1 n = true ->
    oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  assert (forall n m, beq_nat n m = true -> n = m).
  {
    induction n0.
    - intros. inversion H.
      destruct m. trivial.
      inversion H1.

    - intros. simpl in H.
      destruct m. inversion H.
      apply IHn0 in H.
      inversion H. trivial.
  }

  destruct (beq_nat n 3) eqn:Heqe3.
  - apply H in Heqe3. rewrite Heqe3.
    trivial.
  - inversion eq.
Qed.

(* ################################################################# *)
(** * Review *)

(** We've now seen many of Coq's most fundamental tactics.  We'll
    introduce a few more in the coming chapters, and later on we'll
    see some more powerful _automation_ tactics that make Coq help us
    with low-level details.  But basically we've got what we need to
    get work done.

    Here are the ones we've seen:

      - [intros]: move hypotheses/variables from goal to context

      - [reflexivity]: finish the proof (when the goal looks like [e =
        e])

      - [apply]: prove goal using a hypothesis, lemma, or constructor

      - [apply... in H]: apply a hypothesis, lemma, or constructor to
        a hypothesis in the context (forward reasoning)

      - [apply... with...]: explicitly specify values for variables
        that cannot be determined by pattern matching

      - [simpl]: simplify computations in the goal

      - [simpl in H]: ... or a hypothesis

      - [rewrite]: use an equality hypothesis (or lemma) to rewrite
        the goal

      - [rewrite ... in H]: ... or a hypothesis

      - [symmetry]: changes a goal of the form [t=u] into [u=t]

      - [symmetry in H]: changes a hypothesis of the form [t=u] into
        [u=t]

      - [unfold]: replace a defined constant by its right-hand side in
        the goal

      - [unfold... in H]: ... or a hypothesis

      - [destruct... as...]: case analysis on values of inductively
        defined types

      - [destruct... eqn:...]: specify the name of an equation to be
        added to the context, recording the result of the case
        analysis

      - [induction... as...]: induction on values of inductively
        defined types

      - [inversion]: reason by injectivity and distinctness of
        constructors

      - [assert (H: e)] (or [assert (e) as H]): introduce a "local
        lemma" [e] and call it [H]

      - [generalize dependent x]: move the variable [x] (and anything
        else that depends on it) from the context back to an explicit
        hypothesis in the goal formula *)

(* ################################################################# *)
(** * Logic *)

(** Recall the syntax of first order logic

    t ::=  x | c | f(t1, t2, ..., tn)

    A := P(t1, t2,..., tn) | ~ A | A\/A | A/\A | A -> A | forall x. A | exists x. A
 *)

(** In previous chapters, we have seen many examples of how terms can be constructed
 *)

Print nat.

(** We also have seen many examples of factual
    claims (_propositions_) and ways of presenting evidence of their
    truth (_proofs_).  In particular, we have worked extensively with
    _equality propositions_ of the form [e1 = e2], with
    implications ([P -> Q]), and with quantified propositions ([forall
    x, P]).  In this chapter, we will see how Coq can be used to carry
    out other familiar forms of logical reasoning.

    Before diving into details, let's talk a bit about the status of
    mathematical statements in Coq.  Recall that Coq is a _typed_
    language, which means that every sensible expression in its world
    has an associated type.  Logical claims are no exception: any
    statement we might try to prove in Coq has a type, namely [Prop],
    the type of _propositions_.  We can see this with the [Check]
    command: *)

Check 3 = 3.
(* ===> Prop *)

Check @eq.
(* ===> forall A : Type, A -> A -> Prop *)

Check forall n m : nat, n + m = m + n.
(* ===> Prop *)

(** But propositions can be used in many other ways.  For example, we
    can give a name to a proposition using a [Definition], just as we
    have given names to expressions of other sorts. *)

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.
(* ===> plus_fact : Prop *)

(** We can later use this name in any situation where a proposition is
    expected -- for example, as the claim in a [Theorem] declaration. *)

Theorem plus_fact_is_true :
  plus_fact.
Proof. reflexivity.  Qed.

(** We can also write _parameterized_ propositions -- that is,
    functions that take arguments of some type and return a
    proposition. *)

(** For instance, the following function takes a number
    and returns a proposition asserting that this number is equal to
    three: *)

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three.
(* ===> nat -> Prop *)

(** In Coq, functions that return propositions are said to define
    _properties_ of their arguments.

    For instance, here's a (polymorphic) property defining the
    familiar notion of an _injective function_. *)

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H. inversion H. reflexivity.
Qed.

(* ################################################################# *)
(** * Logical Connectives *)

(* ================================================================= *)
(** ** Conjunction *)

(** The _conjunction_, or _logical and_, of propositions [A] and [B]
    is written [A /\ B], representing the claim that both [A] and [B]
    are true. 

A    B
--------- (/\i)
A /\ B

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.

 *)

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.

(** To prove a conjunction, use the [split] tactic.  It will generate
    two subgoals, one for each part of the statement: *)

Proof.
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

(** For any propositions [A] and [B], if we assume that [A] is true
    and we assume that [B] is true, we can conclude that [A /\ B] is
    also true. *)


(** So much for proving conjunctive statements.  To go in the other
    direction -- i.e., to _use_ a conjunctive hypothesis to help prove
    something else -- we employ the [destruct] tactic.

    If the proof context contains a hypothesis [H] of the form
    [A /\ B], writing [destruct H as [HA HB]] will remove [H] from the
    context and add two new hypotheses: [HA], stating that [A] is
    true, and [HB], stating that [B] is true.

A /\ B
--------- (/\e1)
  A

A /\ B
--------- (/\e2)
  B

 *)

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n = 0.
Proof.
  intros n m Hand.
  destruct Hand as [Hn Hm].
  rewrite Hn.
  reflexivity.
Qed.

(** As usual, we can also destruct [H] right when we introduce it,
    instead of introducing and then destructing it: *)

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.


(** But it's important
    to understand how to work with conjunctive hypotheses because
    conjunctions often arise from intermediate steps in proofs,
    especially in bigger developments.  Here's a simple example: *)

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros.
  assert (Hand: n = 0 /\ m = 0).
  {
    destruct n.
    - simpl in H. rewrite H.
      split; reflexivity.
    - inversion H.
  }
  destruct Hand as [Hn Hm].
  subst. trivial.
Qed.


(** By the way, the infix notation [/\] is actually just syntactic
    sugar for [and A B].  That is, [and] is a Coq operator that takes
    two propositions as arguments and yields a proposition. *)

Check and.
(* ===> and : Prop -> Prop -> Prop *)

(* ================================================================= *)
(** ** Disjunction *)

(** Another important connective is the _disjunction_, or _logical or_,
    of two propositions: [A \/ B] is true when either [A] or [B]
    is.  (Alternatively, we can write [or A B], where [or : Prop ->
    Prop -> Prop].) 

 *)

(** 

         A   B
         .   .
         .   .
         .   .
A \/ B   C   C
------------------- (\/e)
        C

    To use a disjunctive hypothesis in a proof, we proceed by case
    analysis, which, as for [nat] or other data types, can be done
    with [destruct] or [intros].  Here is an example: *)

Lemma or_example :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* This pattern implicitly does case analysis on
     [n = 0 \/ m = 0] *)
  intros n m Hor.
  destruct Hor as [Hn | Hm].
  - (* Here, [n = 0] *)
    rewrite Hn. reflexivity.
  - (* Here, [m = 0] *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

(** 

    A
--------- (\/i1)
  A \/ B

    B
--------- (\/i2)
  A \/ B

Conversely, to show that a disjunction holds, we need to show that
    one of its sides does. This is done via two tactics, [left] and
    [right].  As their names imply, the first one requires
    proving the left side of the disjunction, while the second
    requires proving its right side.  Here is a trivial use... *)

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros. destruct n.
  - left. reflexivity.
  - right. reflexivity.
Qed.

(* ================================================================= *)
(** ** Falsehood and Negation *)
(** So far, we have mostly been concerned with proving that certain
    things are _true_ -- addition is commutative, appending lists is
    associative, etc.  Of course, we may also be interested in
    _negative_ results, showing that certain propositions are _not_
    true. In Coq, such negative statements are expressed with the
    negation operator [~]. *)

(** To see how negation works, recall the discussion of the _principle
    of explosion_ from the [Tactics] chapter; it asserts that, if
    we assume a contradiction, then any other proposition can be
    derived.  Following this intuition, we could define [~ P] ("not
    [P]") as [forall Q, P -> Q].  Coq actually makes a slightly
    different choice, defining [~ P] as [P -> False], where [False] is
    a specific contradictory proposition defined in the standard
    library. *)

Module MyNot.

  Definition not (P:Prop) := P -> False.

  Notation "~ x" := (not x) : type_scope.

  Check not.
  (* ===> Prop -> Prop *)

End MyNot.

(** Since [False] is a contradictory proposition, the principle of
    explosion also applies to it. If we get [False] into the proof
    context, we can use [destruct] (or [inversion]) on it to complete
    any goal: *)

Theorem ex_falso_quodlibet : forall (P:Prop),
    False -> P.
Proof.
  intros P contra.
  inversion contra.  Qed.

(** The Latin _ex falso quodlibet_ means, literally, "from falsehood
    follows whatever you like"; this is another common name for the
    principle of explosion. *)

(** **** Exercise: 2 stars, optional (not_implies_our_not)  *)
(** Show that Coq's definition of negation implies the intuitive one
    mentioned above: *)

(**
   H1: ~ P  (Hyp)
   
=======================
   G1. forall Q, P -> Q  (forall i
 *)

Fact not_implies_our_not : forall (P:Prop),
    ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  intros P H1.
  intros Q0.
  intros H3.
  pose (H1 H3) as H4.
  apply ex_falso_quodlibet.
  apply H4.
Qed.

(** This is how we use [not] to state that [0] and [1] are different
    elements of [nat]: *)

Theorem zero_not_one : ~(0 = 1).
Proof.
  intros contra. inversion contra.
Qed.

(** Such inequality statements are frequent enough to warrant a
    special notation, [x <> y]: *)

Check (0 <> 1).
(* ===> Prop *)

Theorem zero_not_one' : 0 <> 1.
Proof.
  intros H. inversion H.
Qed.

(** It takes a little practice to get used to working with negation in
    Coq.  Even though you can see perfectly well why a statement
    involving negation is true, it can be a little tricky at first to
    get things into the right configuration so that Coq can understand
    it!  Here are proofs of a few familiar facts to get you warmed
    up. *)

Theorem not_False :
  ~ False.
Proof.
  intros H. inversion H. Qed.

Theorem double_neg : forall P : Prop,
    P -> ~~P.
Proof.
  intros P.
  intros H1.
  intros HnP.
  apply HnP.
  exact H1.
Qed.

(** Similarly, since inequality involves a negation, it requires a
    little practice to be able to work with it fluently.  Here is one
    useful trick.  If you are trying to prove a goal that is
    nonsensical (e.g., the goal state is [false = true]), apply
    [ex_falso_quodlibet] to change the goal to [False].  This makes it
    easier to use assumptions of the form [~P] that may be available
    in the context -- in particular, assumptions of the form
    [x<>y]. *)

Theorem not_true_is_false : forall b : bool,
    b <> true -> b = false.
Proof.
  intros b.
  intros Hnb.
  destruct b.
  - elim Hnb.
    reflexivity.
  - reflexivity.
Qed.


(** Since reasoning with [ex_falso_quodlibet] is quite common, Coq
    provides a built-in tactic, [exfalso], for applying it. *)

Theorem not_true_is_false' : forall b : bool,
    b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    exfalso.                (* <=== *)
    apply H. reflexivity.
  - (* b = false *) reflexivity.
Qed.

(* ================================================================= *)
(** ** Truth *)

(** Besides [False], Coq's standard library also defines [True], a
    proposition that is trivially true. To prove it, we use the
    predefined constant [I : True]: *)

Lemma True_is_true : True.
Proof. econstructor. Qed.

(** Unlike [False], which is used extensively, [True] is used quite
    rarely, since it is trivial (and therefore uninteresting) to prove
    as a goal, and it carries no useful information as a hypothesis. *)
(** But it can be quite useful when defining complex [Prop]s using
    conditionals or as a parameter to higher-order [Prop]s.  We will
    see examples of such uses of [True] later on. *)

(* ================================================================= *)
(** ** Existential Quantification *)

(** Another important logical connective is _existential
    quantification_.  To say that there is some [x] of type [T] such
    that some property [P] holds of [x], we write [exists x : T,
    P]. As with [forall], the type annotation [: T] can be omitted if
    Coq is able to infer from the context what the type of [x] should
    be. *)

(** To prove a statement of the form [exists x, P], we must show that
    [P] holds for some specific choice of value for [x], known as the
    _witness_ of the existential.  This is done in two steps: First,
    we explicitly tell Coq which witness [t] we have in mind by
    invoking the tactic [exists t].  Then we prove that [P] holds after
    all occurrences of [x] are replaced by [t]. *)

Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  eexists. 
  instantiate (1:= 2).
  reflexivity.
Qed.

(** Conversely, if we have an existential hypothesis [exists x, P] in
    the context, we can destruct it to obtain a witness [x] and a
    hypothesis stating that [P] holds of [x]. *)

Theorem exists_example_2 : forall n,
    (exists m, n = 4 + m) ->
    (exists o, n = 2 + o).
Proof.
  intros n Hex.
  destruct Hex as [m0 Hm0].
  exists (m0 + 2).
  rewrite Hm0.
  rewrite (plus_comm m0 2).
  simpl.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** Classical vs. Constructive Logic *)

(** We have seen that it is not possible to test whether or not a
    proposition [P] holds while defining a Coq function.  You may be
    surprised to learn that a similar restriction applies to _proofs_!
    In other words, the following intuitive reasoning principle is not
    derivable in Coq: *)

Definition excluded_middle := forall P : Prop,
    P \/ ~ P.

(** To understand operationally why this is the case, recall
    that, to prove a statement of the form [P \/ Q], we use the [left]
    and [right] tactics, which effectively require knowing which side
    of the disjunction holds.  But the universally quantified [P] in
    [excluded_middle] is an _arbitrary_ proposition, which we know
    nothing about.  We don't have enough information to choose which
    of [left] or [right] to apply, just as Coq doesn't have enough
    information to mechanically decide whether [P] holds or not inside
    a function. *)

(** However, if we happen to know that [P] is reflected in some
    boolean term [b], then knowing whether it holds or not is trivial:
    we just have to check the value of [b]. *)

Theorem restricted_excluded_middle : forall P b,
    (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  - left. apply H. reflexivity.
  - right. intros contra. apply H in contra. inversion contra.
Qed.

(** It may seem strange that the general excluded middle is not
    available by default in Coq; after all, any given claim must be
    either true or false.  Nonetheless, there is an advantage in not
    assuming the excluded middle: statements in Coq can make stronger
    claims than the analogous statements in standard mathematics.
    Notably, if there is a Coq proof of [exists x, P x], it is
    possible to explicitly exhibit a value of [x] for which we can
    prove [P x] -- in other words, every proof of existence is
    necessarily _constructive_. *)

(** Logics like Coq's, which do not assume the excluded middle, are
    referred to as _constructive logics_.

    More conventional logical systems such as ZFC, in which the
    excluded middle does hold for arbitrary propositions, are referred
    to as _classical_. *)

(** The following example illustrates why assuming the excluded middle
    may lead to non-constructive proofs:

    _Claim_: There exist irrational numbers [a] and [b] such that [a ^
    b] is rational.

    _Proof_: It is not difficult to show that [sqrt 2] is irrational.
    If [sqrt 2 ^ sqrt 2] is rational, it suffices to take [a = b =
    sqrt 2] and we are done.  Otherwise, [sqrt 2 ^ sqrt 2] is
    irrational.  In this case, we can take [a = sqrt 2 ^ sqrt 2] and
    [b = sqrt 2], since [a ^ b = sqrt 2 ^ (sqrt 2 * sqrt 2) = sqrt 2 ^
    2 = 2].  []

    Do you see what happened here?  We used the excluded middle to
    consider separately the cases where [sqrt 2 ^ sqrt 2] is rational
    and where it is not, without knowing which one actually holds!
    Because of that, we wind up knowing that such [a] and [b] exist
    but we cannot determine what their actual values are (at least,
    using this line of argument).

    As useful as constructive logic is, it does have its limitations:
    There are many statements that can easily be proven in classical
    logic but that have much more complicated constructive proofs, and
    there are some that are known to have no constructive proof at
    all!  Fortunately, like functional extensionality, the excluded
    middle is known to be compatible with Coq's logic, allowing us to
    add it safely as an axiom.  However, we will not need to do so in
    this book: the results that we cover can be developed entirely
    within constructive logic at negligible extra cost.

    It takes some practice to understand which proof techniques must
    be avoided in constructive reasoning, but arguments by
    contradiction, in particular, are infamous for leading to
    non-constructive proofs.  Here's a typical example: suppose that
    we want to show that there exists [x] with some property [P],
    i.e., such that [P x].  We start by assuming that our conclusion
    is false; that is, [~ exists x, P x]. From this premise, it is not
    hard to derive [forall x, ~ P x].  If we manage to show that this
    intermediate fact results in a contradiction, we arrive at an
    existence proof without ever exhibiting a value of [x] for which
    [P x] holds!

    The technical flaw here, from a constructive standpoint, is that
    we claimed to prove [exists x, P x] using a proof of
    [~ ~ (exists x, P x)].  Allowing ourselves to remove double
    negations from arbitrary statements is equivalent to assuming the
    excluded middle, as shown in one of the exercises below.  Thus,
    this line of reasoning cannot be encoded in Coq without assuming
    additional axioms. *)

(** **** Exercise: 3 stars (excluded_middle_irrefutable)  *)
(** Proving the consistency of Coq with the general excluded middle
    axiom requires complicated reasoning that cannot be carried out
    within Coq itself.  However, the following theorem implies that it
    is always safe to assume a decidability axiom (i.e., an instance
    of excluded middle) for any _particular_ Prop [P].  Why?  Because
    we cannot prove the negation of such an axiom.  If we could, we
    would have both [~ (P \/ ~P)] and [~ ~ (P \/ ~P)] (since [P]
    implies [~ ~ P], by the exercise below), which would be a
    contradiction.  But since we can't, it is safe to add [P \/ ~P] as
    an axiom. *)

Theorem excluded_middle_irrefutable: forall (P:Prop),
    ~ ~ (P \/ ~ P).
Proof.
  intros P.
  intros HP.
  assert (Hor: P \/ ~P).
  {
    right.
    intros HF.
    apply HP.
    left.
    exact HF.
  }
  apply HP. exact Hor.
Qed.
