(** This file introduces the [bounded] monad and associated
  definitions, which extend a type with upper and lower bounds. *)

Require Import LogicalRelations.
Require Import Structures.

Require Import ErrorMonad.
Require Import OptionMonad.
Require Import OptionOrders.


(** * Type constructor *)

Inductive bounded A :=
  | bbot : bounded A
  | btop : bounded A
  | binj : A -> bounded A.

Arguments bbot {_}.
Arguments btop {_}.
Arguments binj {_} _.

(** ** Monadic structure *)

Global Instance bounded_functor_ops:
  FunctorOps bounded :=
  {
    fmap A B f x :=
      match x with
        | bbot => bbot
        | btop => btop
        | binj a => binj (f a)
      end
  }.

Global Instance bounded_functor:
  Functor bounded.
Proof.
  split; destruct x; reflexivity.
Qed.

Global Instance bounded_monad_ops: MonadOps bounded :=
  {
    bind A B f x :=
      match x with
        | bbot => bbot
        | btop => btop
        | binj a => f a
      end;
    ret := @binj
  }.

Global Instance bounded_monad:
  Monad bounded.
Proof.
  split.
  - typeclasses eauto.
  - reflexivity.
  - reflexivity.
  - destruct m; reflexivity.
  - destruct m; reflexivity.
Qed.

Global Instance bounded_monad_inv_ret:
  MonadInvRet bounded.
Proof.
  intros A x y.
  inversion 1.
  reflexivity.
Qed.

Global Instance bounded_monad_inv_bind:
  MonadInvBind bounded.
Proof.
  intros A B f ma b Hb.
  destruct ma; eauto; simpl in Hb; congruence.
Qed.


(** * Relator *)

Inductive bounded_rel {A B} (R : rel A B) : rel (bounded A) (bounded B) :=
  | bbot_rel_def : bounded_rel R (@bbot A) (@bbot B)
  | btop_rel_def : bounded_rel R (@btop A) (@btop B)
  | binj_rel_def : (R ++> bounded_rel R)%rel (@binj A) (@binj B).

Global Instance bbot_rel:
  Monotonic (@bbot) (forallr R, bounded_rel R).
Proof.
  constructor.
Qed.

Global Instance btop_rel:
  Monotonic (@btop) (forallr R, bounded_rel R).
Proof.
  constructor.
Qed.

Global Instance binj_rel:
  Monotonic (@binj) (forallr R, R ++> bounded_rel R).
Proof.
  intros ? ? ?.
  apply binj_rel_def.
Qed.

Global Instance bounded_subrel {A B}:
  Monotonic (@bounded_rel A B) (subrel ++> subrel).
Proof.
  intros R1 R2 HR a b H.
  destruct H; rauto.
Qed.

Global Instance bounded_subrel_params:
  Params (@bounded_rel) 1.

Global Instance bounded_rel_monad:
  MonadRel (@bounded_rel).
Proof.
  split; simpl; rauto.
Qed.

Lemma bounded_rel_refl `(Reflexive):
  Reflexive (bounded_rel R).
Proof.
  intros [ | | x]; rauto.
Qed.

Hint Extern 1 (Reflexive (bounded_rel _)) =>
  eapply bounded_rel_refl : typeclass_instances.

Lemma bounded_rel_sym `(Symmetric):
  Symmetric (bounded_rel R).
Proof.
  intros ? ? [ | | x y Hxy]; rstep.
  symmetry; eauto.
Qed.

Hint Extern 1 (Symmetric (bounded_rel _)) =>
  eapply bounded_rel_sym : typeclass_instances.

Lemma bounded_rel_trans `(Transitive):
  Transitive (bounded_rel R).
Proof.
  intros x y z Hxy Hyz.
  destruct Hxy; inversion Hyz; subst; rstep.
  etransitivity; eauto.
Qed.

Hint Extern 1 (Transitive (bounded_rel _)) =>
  eapply bounded_rel_trans : typeclass_instances.


(** * Preorder *)

Inductive bounded_le {A B} (R : rel A B) : rel (bounded A) (bounded B) :=
  | bbot_le : LowerBound (bounded_le R) bbot
  | btop_le : UpperBound (bounded_le R) btop
  | binj_le_def : (R ++> bounded_le R)%rel (@binj A) (@binj B).

Global Existing Instance bbot_le.
Global Existing Instance btop_le.

Global Instance bounded_rel_le {A B} (R: rel A B):
  Related (bounded_rel R) (bounded_le R) subrel.
Proof.
  destruct 1; constructor; eauto.
Qed.

(** Note that [bounded_rel_le] means we don't have to define an
  explicit [binj_le] property such as the following, since [binj_rel]
  can be used for the same purpose.

  <<<
  Global Instance binj_le :
    Monotonic (@binj) (forallr R, R ++> bounded_le R).
  Proof.
    intros A B R.
    apply binj_le_def.
  Qed.
  >>>
 *)

Global Instance bounded_le_subrel {A B}:
  Monotonic (@bounded_le A B) (subrel ++> subrel).
Proof.
  intros R1 R2 HR a b H.
  destruct H; rauto.
Qed.

Global Instance bounded_le_subrel_params:
  Params (@bounded_le) 1.

Global Instance bounded_le_monad:
  MonadRel (@bounded_le).
Proof.
  split; simpl; rauto.
Qed.

Lemma bounded_le_refl `(Reflexive):
  Reflexive (bounded_le R).
Proof.
  intros [ | | x]; rauto.
Qed.

Hint Extern 1 (Reflexive (bounded_le _)) =>
  eapply bounded_le_refl : typeclass_instances.

Lemma bounded_le_trans `(Transitive):
  Transitive (bounded_le R).
Proof.
  intros x y z Hxy Hyz.
  destruct Hxy; inversion Hyz; subst; rstep.
  etransitivity; eauto.
Qed.

Hint Extern 1 (Transitive (bounded_le _)) =>
  eapply bounded_le_trans : typeclass_instances.


(** * Interaction with other monads *)

(** The [bounded] monad interacts natually with the [option] and [res]
  monads, defined elsewhere. We identify [None] with our bottom
  element [bbot], and [Error] with top element. Each one of those
  monads can be embedded into [bounded], and conversely a value of
  type [bounded A] can be extracted as either an [option (res A)] or a
  [res (option A)] value, which is convenient for manipulating the
  value as a [res A] value within an [option] computation, or an
  [option A] value withing a [res] computation. *)

(** Note that the symmetry between [option] and [res] is not perfect:
  there is no [res_rel] defined at the moment (FIXME: do it?), and
  [Error]s carry an [errmsg] (even though it is ignored by [res_le]). *)

(** ** Embedding [option] computations as [bounded] computations *)

Definition option_bounded_inj {A} (x : option A) : bounded A :=
  match x with
    | Some a => binj a
    | None => bbot
  end.

Global Instance option_bounded_inj_rel:
  Monotonic (@option_bounded_inj) (forallr R, option_rel R ++> bounded_rel R).
Proof.
  unfold option_bounded_inj.
  rauto.
Qed.

Global Instance option_bounded_inj_le:
  Monotonic (@option_bounded_inj) (forallr R, option_le R ++> bounded_le R).
Proof.
  unfold option_bounded_inj.
  rauto.
Qed.

Lemma option_bounded_inj_fmap {A B} (f : A -> B) (m : option A) :
  option_bounded_inj (fmap f m) =
  fmap f (option_bounded_inj m).
Proof.
  destruct m; reflexivity.
Qed.

Lemma option_bounded_inj_bind {A B} (f : A -> option B) (m : option A) :
  option_bounded_inj (bind f m) =
  bind (fun a => option_bounded_inj (f a)) (option_bounded_inj m).
Proof.
  destruct m; reflexivity.
Qed.

Lemma option_bounded_inj_ret {A} (a : A) :
  option_bounded_inj (ret a) =
  ret a.
Proof.
  reflexivity.
Qed.

(** ** Embedding [res] computations as [bounded] computations *)

Definition res_bounded_inj {A} (x : res A) : bounded A :=
  match x with
    | OK a => binj a
    | Error _ => btop
  end.

Global Instance res_bounded_inj_le:
  Monotonic (@res_bounded_inj) (forallr R, res_le R ++> bounded_le R).
Proof.
  unfold res_bounded_inj.
  rauto.
Qed.

Lemma res_bounded_inj_fmap {A B} (f : A -> B) (m : res A) :
  res_bounded_inj (fmap f m) =
  fmap f (res_bounded_inj m).
Proof.
  destruct m; reflexivity.
Qed.

Lemma res_bounded_inj_bind {A B} (f : A -> res B) (m : res A) :
  res_bounded_inj (bind f m) =
  bind (fun a => res_bounded_inj (f a)) (res_bounded_inj m).
Proof.
  destruct m; reflexivity.
Qed.

Lemma res_bounded_inj_ret {A} (a : A) :
  res_bounded_inj (ret a) =
  ret a.
Proof.
  reflexivity.
Qed.

(** ** Extracting [bounded] values into an [option] computation *)

Definition bounded_option_proj {A} (m : bounded A) : option (res A) :=
  match m with
    | bbot => None
    | btop => Some (Error nil)
    | binj a => Some (OK a)
  end.

Global Instance bounded_option_proj_rel:
  Monotonic
    (@bounded_option_proj)
    (forallr R, bounded_rel R ++> option_rel (res_le R)).
Proof.
  unfold bounded_option_proj.
  rauto.
Qed.

Global Instance bounded_option_proj_le:
  Monotonic
    (@bounded_option_proj)
    (forallr R, bounded_le R ++> option_le (res_le R)).
Proof.
  unfold bounded_option_proj.
  rauto.
Qed.

(** ** Extracting [bounded] values into a [res] computation *)

Definition bounded_res_proj {A} (m : bounded A) : res (option A) :=
  match m with
    | bbot => OK None
    | btop => Error nil
    | binj a => OK (Some a)
  end.

Global Instance bounded_res_proj_rel:
  Monotonic
    (@bounded_res_proj)
    (forallr R, bounded_rel R ++> res_le (option_rel R)).
Proof.
  unfold bounded_res_proj.
  rauto.
Qed.

Global Instance bounded_res_proj_le:
  Monotonic
    (@bounded_res_proj)
    (forallr R, bounded_le R ++> res_le (option_le R)).
Proof.
  unfold bounded_res_proj.
  rauto.
Qed.
