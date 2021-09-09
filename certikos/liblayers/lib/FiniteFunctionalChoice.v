(** Functional choice holds on finite types regardless of axioms.
  We show this for a characterization of (some) finite types that is
  somewhat convenient for us. *)

Require Import ChoiceFacts.
Require Import List.
Require Import LogicalRelations.
Require Import Decision.

(** * Functional choice on various types *)

(** ** Elements of a list *)

(** As a first step, do the proof for elements of a list on a support
  type. *)

Lemma FunctionalChoice_onlist {A B} (l: list A) (R: rel A B):
  EqDec A ->
  l <> nil ->
  (forall x, In x l -> exists y, R x y) ->
  exists (f: A -> B), forall x, In x l -> R x (f x).
Proof.
  intros HA Hl H.
  destruct l as [|a0 l].
  {
    elim Hl; reflexivity.
  }
  clear Hl.
  induction l.
  - simpl in *.
    edestruct H as [b Hb]; eauto.
    exists (fun _ => b).
    intros x Ha.
    destruct Ha; try contradiction.
    subst.
    assumption.
  - destruct (H a) as [b Hb]; simpl; eauto.
    destruct IHl as [f Hf].
    {
      simpl in *.
      intros x [Hx | Hx].
      - subst.
        eauto.
      - apply H.
        eauto.
    }
    exists (fun x => if Decision.decide (x = a) then b else f x).
    simpl in *.
    intros x [Hx|[Hx|Hx]].
    + destruct (decide (x = a)); try congruence.
      eauto.
    + destruct (decide (x = a)); try congruence.
    + destruct (decide (x = a)); try congruence.
      eauto.
Qed.

(** ** Finite types *)

(** Now we define our characterization of finite type as types with a
  complete enumeration of their elements as a list. *)

Record finite (T: Type): Prop :=
  {
    finite_enum: list T;
    finite_enum_complete x: In x finite_enum
  }.

Lemma FunctionalChoice_on_finite A B:
  finite A ->
  inhabited A ->
  EqDec A ->
  FunctionalChoice_on A B.
Proof.
  intros [l Hl] HA HAeq.
  intros R HR.
  edestruct (FunctionalChoice_onlist l R); eauto.
  intro; subst.
  destruct HA as [a].
  elim (Hl a).
Qed.

(** To define proofs of [finite], you can use the following ugly
  set of tactics. *)

Ltac in_open_list :=
  lazymatch goal with
    | |- In _ (_ :: _) =>
      apply in_cons; in_open_list
    | |- In _ ?l =>
      is_evar l; apply in_eq
  end.

Definition list_finished {A} (l : list A) := True.

Lemma list_finished_nil {A}: list_finished (@nil A).
Proof.
  firstorder.
Qed.

Lemma list_finished_cons {A} (x: A) l:
  list_finished l ->
  list_finished (x::l).
Proof.
  firstorder.
Qed.

Ltac close_list l :=
  let H := fresh in
  assert (H : list_finished l);
  [ repeat (apply list_finished_nil || apply list_finished_cons) | clear H].

Ltac solve_finite destruct_tac :=
  esplit;
  intro;
  lazymatch goal with |- In ?x ?l =>
    let T := type of x in
    cut True; [ intros _; destruct_tac x; in_open_list
              | close_list l; exact I ]
  end.

Definition bool_finite: finite bool.
Proof.
  solve_finite ltac:(fun x => destruct x).
Qed.


(** * Derived lemmas *)

Require Import ExtensionalityAxioms.

Lemma arrow_pointwise_rel_compose {A B1 B2 B3} (R12: rel B1 B2) (R23: rel B2 B3):
  ChoiceFacts.FunctionalChoice_on A B2 ->
  (- ==> rel_compose R12 R23)%rel =
  rel_compose (B := A -> B2) (- ==> R12)%rel (- ==> R23)%rel.
Proof.
  intros HAB2.
  apply functional_extensionality; intro f1.
  apply functional_extensionality; intro f3.
  apply prop_ext; split.
  - intros H.
    assert (Hf2: forall a, exists b2, (R12 (f1 a) b2 /\ R23 b2 (f3 a))%type) by eauto.
    eapply HAB2 in Hf2.
    destruct Hf2 as (f2 & Hf2).
    exists f2.
    split; intros a; destruct (Hf2 a); eauto.
  - intros (f2 & Hf12 & Hf23) a.
    eexists; eauto.
Qed.
