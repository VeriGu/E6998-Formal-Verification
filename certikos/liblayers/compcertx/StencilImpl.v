Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.common.Errors.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import liblayers.lib.Decision.
Require Import liblayers.lib.OptionMonad.
Require Import liblayers.logic.PTrees.
Require Export liblayers.logic.Modules.
Require Export liblayers.logic.Layers.
Require Import liblayers.compcertx.CompcertStructures.
Require Export liblayers.compcertx.ErrorMonad.

Require Import ProofIrrelevance.

(** Missing lemma from Globalenv. *)

Module Genv.
Export Globalenvs.Genv.

Theorem find_var_info_inversion:
  forall F V,
  forall (p: _ F V) b v,
    find_var_info (globalenv p) b = Some v ->
  exists id, In (id, Some (Gvar v)) (prog_defs p).
Proof.
  unfold find_var_info.
  intros.
  destruct (find_def (globalenv p) b) as [[?|?]|?] eqn:Hdef; try discriminate.
  inv H.
  eapply find_def_inversion; eauto.
Qed.

End Genv.

(** First, build a list of identifiers that will appear in the program.
  All of our programs have the same structure, that is, we enumerate
  definitions from 1 to [glob_threshold]. Hopefully the following
  definition will extract okay. *)

Definition stencil_ids_up_to thr :=
  positive_rec (list ident) nil (fun i ids => ids ++ i :: nil) thr.

Definition stencil_ids :=
  stencil_ids_up_to glob_threshold.

Lemma In_stencil_ids_up_to i j:
  In i (stencil_ids_up_to j) <-> (i < j)%positive.
Proof.
  unfold stencil_ids_up_to.
  pattern j.
  apply positive_Peano_ind.
  - rewrite positive_rec_base.
    split.
    + inversion 1.
    + apply Pos.nlt_1_r.
  - clear j.
    intros j IHj.
    rewrite positive_rec_succ.
    rewrite in_app.
    simpl.
    split.
    + intros [Hij | Hin].
      * apply IHj in Hij.
        xomega.
      * destruct Hin as [Hin|]; try tauto.
        subst.
        xomega.
    + intros Hij.
      rewrite IHj; clear IHj.
      apply Pos.lt_succ_r in Hij.
      apply Pos.lt_eq_cases in Hij.
      destruct Hij; eauto.
Qed.

Lemma stencil_ids_glob_threshold i:
  In i stencil_ids <-> (i < glob_threshold)%positive.
Proof.
  apply In_stencil_ids_up_to.
Qed.

Lemma stencil_ids_norepet:
  list_norepet stencil_ids.
Proof.
  unfold stencil_ids.
  generalize glob_threshold; intro j.

  pattern j; revert j; apply positive_Peano_ind.
  - unfold stencil_ids_up_to.
    rewrite positive_rec_base.
    constructor.
  - intros i IHi.
    unfold stencil_ids_up_to.
    rewrite positive_rec_succ.
    apply list_norepet_app.
    split; eauto.
    split.
    + constructor; eauto.
      constructor.
    + intros x y Hx Hy.
      apply In_stencil_ids_up_to in Hx.
      simpl in Hy.
      destruct Hy; eauto; subst.
      destruct (decide (x = y)); eauto; subst.
      apply Pos.lt_irrefl in Hx.
      elim Hx.
Qed.

Definition program_of_stencil: AST.program unit unit :=
  {|
    prog_defs := List.map (fun i => (i, None)) stencil_ids;
    prog_public := stencil_ids;
    prog_main := xH (* we do not really care here *)
  |}.

Definition globalenv_of_stencil: Genv.t unit unit :=
  Genv.globalenv program_of_stencil.

(** Extensionality properties of stencils (use proof irrelevance). *)

Fixpoint find_symbol_of_list (l: list ident) (i: ident) (res: option Values.block) (b: Values.block) {struct l} : option Values.block :=
  match l with
    | nil => res
    | i' :: l' => find_symbol_of_list l' i (if peq i i' then Some b else res) (Psucc b)
  end.

Lemma find_symbol_of_list_correct:
  forall {F V: Type} l (ge: _ F V) i,
    find_symbol_of_list (List.map fst l) i (Genv.find_symbol ge i) (Genv.genv_next ge) =
    Genv.find_symbol (Genv.add_globals ge l) i.
Proof.
  induction l.
   reflexivity.
  intros.
  change (Genv.add_globals ge (a :: l)) with (Genv.add_globals (Genv.add_global ge a) l).
  rewrite <- IHl. clear IHl.
  simpl.
  destruct (peq i (fst a)).
   subst. unfold Genv.add_global, Genv.find_symbol. simpl. rewrite PTree.gss. reflexivity.
   unfold Genv.add_global, Genv.find_symbol. simpl. rewrite PTree.gso. reflexivity.
  assumption.
Qed.

Lemma find_symbol_of_list_not_in:
  forall l i,
    ~ In i l ->
    forall res b,
    find_symbol_of_list l i res b = res.
Proof.
  induction l; simpl.
   reflexivity.
  intros. destruct (peq i a).
   subst. destruct H. auto.
  apply IHl. tauto.
Qed.

Lemma find_symbol_of_list_cons_not_in:
  forall l i,
    ~ In i l ->
    forall res b,
      find_symbol_of_list (i :: l) i res b = Some b.
Proof.
  simpl.
  intros.
  rewrite peq_true.
  apply find_symbol_of_list_not_in.
  assumption.
Qed.

Lemma find_symbol_of_list_le:
  forall l,
    list_norepet l ->
    forall i b,
    forall b', find_symbol_of_list l i None b = Some b' ->
               Ple b b'.
Proof.
  induction l; simpl.
   discriminate.
  intros. inv H. destruct (peq i a).
   subst. erewrite find_symbol_of_list_not_in in H0; eauto. inv H0. xomega.
  eapply Ple_trans.
  2: eapply IHl; eauto.
  xomega.
Qed.

Lemma find_symbol_of_list_lt:
  forall l i j r',
    j <> i ->
    list_norepet (i :: l) ->
    forall b,
    (find_symbol_of_list (i :: l) j None b) = Some r' ->
    Plt b r'.
Proof.
  simpl.
  intros.
  inv H0.
  destruct (peq j i).
   contradiction.
  generalize (find_symbol_of_list_le _ H5 _ _ _ H1).
  intro. xomega.
Qed.

Lemma find_symbol_of_list_cons:
  forall a1 l1,
    list_norepet (a1 :: l1) ->
    forall a2 l2,
      list_norepet (a2 :: l2) ->
      forall b,
    (forall i, find_symbol_of_list (a1 :: l1) i None b =
               find_symbol_of_list (a2 :: l2) i None b) ->
  a1 = a2.
Proof.
  intros.
  destruct (peq a1 a2).
   assumption.
  exfalso.  
  generalize (find_symbol_of_list_lt _ _ _ b n H0 b).  
  rewrite <- H1.
  inv H.
  rewrite find_symbol_of_list_cons_not_in; auto.
  intros. edestruct Plt_irrefl. apply H. reflexivity.
Qed.    

Lemma find_symbol_of_list_ext:
  forall l1 l2 b,         
    (forall i, find_symbol_of_list l1 i None b = find_symbol_of_list l2 i None b) ->
    list_norepet l1 ->
    list_norepet l2 ->
    length l1 = length l2 ->
    l1 = l2.
Proof.
  induction l1; destruct l2; try discriminate.
  - reflexivity.
  - intros.
    inv H2.
    assert (a = i) by (eapply find_symbol_of_list_cons; eauto).
    subst. f_equal.
    inv H1. inv H0.
    eapply IHl1; eauto.
    instantiate (1 := Pos.succ b).
    intros.
    generalize (H i0).
    simpl.
    destruct (peq i0 i).
     subst. intros. erewrite find_symbol_of_list_not_in; eauto.  erewrite find_symbol_of_list_not_in; eauto.
    eauto.
Qed.

Lemma advance_next_length_le:
  forall {F1 V1 F2 V2} (l1: list (ident * option (globdef F1 V1))) (l2: list (ident * option (globdef F2 V2))) b,
    Genv.advance_next l1 b = Genv.advance_next l2 b ->
    (length l1 <= length l2)%nat.
Proof.
  induction l1; simpl.
   intros; omega.
  destruct l2.
   simpl. intros. exfalso. 
   generalize (Genv.advance_next_le l1 (Pos.succ b)).
   rewrite H.
   intro.
   xomega.
   simpl.
   intros.
   generalize (IHl1 _ _ H).
   intro; omega.
Qed.

Lemma advance_next_length:
  forall {F1 V1 F2 V2} (l1: list (ident * option (globdef F1 V1))) (l2: list (ident * option (globdef F2 V2))) b,
    Genv.advance_next l1 b = Genv.advance_next l2 b ->
    length l1 = length l2.
Proof.
  intros.
  generalize (advance_next_length_le _ _ _ H).
  symmetry in H.
  generalize (advance_next_length_le _ _ _ H).
  omega.
Qed.   
