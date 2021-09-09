Require Import Coq.Program.Basics.
Require Import LogicalRelations.
Require Import SimulationRelation.
Require Import SimrelToolkit.
Require Import Structures.
Require Import OptionOrders.
Require Import compcert.lib.Floats.
Require Import compcert.common.Values.
Require Export liblayers.compcertx.SimValues.
Require Export liblayers.lib.ExtensionalityAxioms.

(** * [simrel_strong_id], a stronger version of [simrel_id],
      to prove that any primitive stable under [simrel_strong_id]
      makes [ec_valid_block] hold.
 *)

Section STRONG_IDENTITY.
  Context `{Hmem: BaseMemoryModel}.
  Context {D: layerdata}.
  Local Opaque mwd_ops.

  Inductive simrel_strong_id_match_mem (b: block): relation (mwd D) :=
    match_mem_intro_simrel_strong_id m:
      b = Mem.nextblock m ->
      simrel_strong_id_match_mem b m m.

  Lemma match_mem_incr_elim_simrel_strong_id
        b1 m1 m1'
        b2 m2 m2':
    Ple b1 b2 ->
    simrel_strong_id_match_mem b1 m1 m1' ->
    simrel_strong_id_match_mem b2 m2 m2' ->
    (forall b, Mem.valid_block m1 b -> Mem.valid_block m2 b) /\
    (forall b, Mem.valid_block m1' b -> Mem.valid_block m2' b).
  Proof.
    inversion 2; subst.
    inversion 1; subst.
    unfold Mem.valid_block.
    intuition xomega.
  Qed.
  
  Definition simrel_strong_id_ops: simrel_components D D :=
    {|
      simrel_world := block;
      simrel_acc := {| le := Ple |};
      simrel_new_glbl := nil;
      simrel_undef_matches_values_bool := false;
      simrel_undef_matches_block p b := False;
      simrel_meminj p := inject_id;
      match_mem := simrel_strong_id_match_mem
    |}.

  Local Instance simrel_strong_id_corefl:
    CoreflexiveInjection D D simrel_strong_id_ops.
  Proof.
    split.
    - reflexivity.
    - reflexivity.
    - tauto.
  Qed.

  Lemma match_block_sameofs_simrel_strong_id p:
    match_block_sameofs simrel_strong_id_ops p = eq.
  Proof.
    apply eqrel_eq; split.
    - inversion 1.
      reflexivity.
    - intros b _ [].
      reflexivity.
  Qed.

  Lemma match_block_simrel_strong_id p:
    match_block simrel_strong_id_ops p = eq.
  Proof.
    apply eqrel_eq; split.
    - intros b1 b2 [ofs H].
      inversion H; congruence.
    - intros b _ [].
      exists 0%Z.
      reflexivity.
  Qed.

  Lemma match_ptr_simrel_strong_id p:
    match_ptr simrel_strong_id_ops p = eq.
  Proof.
    eapply eqrel_eq.
    split.
    - destruct 1.
      inversion H; subst.
      rewrite Z.add_0_r.
      reflexivity.
    - intros [b ofs] y [].
      rewrite <- (Z.add_0_r ofs) at 2.
      constructor.
      reflexivity.
  Qed.

  Lemma match_ptrbits_simrel_strong_id p:
    match_ptrbits simrel_strong_id_ops p = eq.
  Proof.
    apply eqrel_eq; split.
    - destruct 1.
      inversion H; subst.
      change (Ptrofs.repr 0) with Ptrofs.zero.
      rewrite Ptrofs.add_zero.
      reflexivity.
    - intros [b ofs] y [].
      rewrite <- (Ptrofs.add_zero ofs) at 2.
      change Ptrofs.zero with (Ptrofs.repr 0).
      constructor.
      reflexivity.
  Qed.

  Lemma match_ptrrange_simrel_strong_id p:
    match_ptrrange simrel_strong_id_ops p = eq.
  Proof.
    eapply eqrel_eq.
    split.
    - destruct 1.
      inversion H; subst.
      rewrite match_ptr_simrel_strong_id in H.
      congruence.
    - intros [[b lo] hi] _ [].
      replace hi with (lo + (hi - lo))%Z by omega.
      constructor.
      rewrite match_ptr_simrel_strong_id.
      reflexivity.
  Qed.

  Lemma match_val_simrel_strong_id p:
    match_val simrel_strong_id_ops p = eq.
  Proof.
    apply eqrel_eq; split.
    - destruct 1; try contradiction; try discriminate; try reflexivity.
      rewrite match_ptrbits_simrel_strong_id in H.
      congruence.
    - intros v _ [].
      destruct v; constructor.
      rewrite match_ptrbits_simrel_strong_id.
      reflexivity.
  Qed.

  Lemma match_memval_simrel_strong_id p:
    match_memval simrel_strong_id_ops p = eq.
  Proof.
    apply eqrel_eq; split.
    - destruct 1; try contradiction; try discriminate; try reflexivity.
      rewrite match_val_simrel_strong_id in H.
      congruence.
    - intros v _ [].
      destruct v; constructor.
      rewrite match_val_simrel_strong_id.
      reflexivity.
  Qed.

  Local Instance simrel_strong_id_prf:
    CoreflexiveSimulationRelation D D simrel_strong_id_ops.
  Proof.
    constructor.

    + (* [simrel_acc_preorder] *)
      split.
    - red. apply Ple_refl.
    - red. apply Ple_trans.

    + (* [simrel_acc_meminj] *)
      repeat red. simpl. repeat constructor.

    + (* [simrel_undef_matches_block_not_weak_valid] *)
      simpl.
      inversion 1; subst.
      congruence.

    + (* [simrel_undef_matches_block_invalid] *)
      simpl.
      inversion 1; subst.
      congruence.

    + (* [match_global_block_sameofs] *)
      discriminate.

    + (* [Genv.init_mem] *)
      intros F V p1 p2 Hp.
      eapply genv_init_mem_simrel; eauto.
      * apply SimrelCategory.simrel_id_init_mem.
      * simpl.
        intros m _ [[] Hnb].
        exists glob_threshold.
        red in Hnb.
        constructor.
        destruct Hnb.
        reflexivity.

    + (* [simrel_alloc] *)
      repeat red.
      intros p m_ m.
      inversion 1; subst.
      exists (Psucc (Mem.nextblock m)).
      split.
      {
        apply Ple_succ.
      }
      split; try reflexivity.
      constructor.
      symmetry.
      destruct (Mem.alloc _ _ _) eqn:ALLOC.
      simpl.
      eapply Mem.nextblock_alloc; eauto.

    + (* [simrel_free] *)
      intros w m1 m2 Hm b1 b2 Hb lo hi.
      destruct Hm; subst.
      apply coreflexivity in Hb; subst.
      destruct (Mem.free _ _ _ _) eqn:FREE; constructor.
      exists (Mem.nextblock m).
      split; try reflexivity.
      constructor.
      symmetry; eapply Mem.nextblock_free; eauto.

    + (* [simrel_load] *)
      intros w chunk m1 m2 Hm b1 b2 Hb ofs.
      destruct Hm; subst.
      apply coreflexivity in Hb; subst.
      rewrite match_val_simrel_strong_id.
      reflexivity.

    + (* [simrel_store] *)
      intros w chunk m1 m2 Hm b1 b2 Hb ofs v1 v2 Hv.
      destruct Hm; subst.
      apply coreflexivity in Hb; subst.
      apply coreflexivity in Hv; subst.
      destruct (Mem.store _ _ _ _ _) eqn:STORE; constructor.
      exists (Mem.nextblock m).
      split; try reflexivity.
      constructor.
      symmetry; eapply Mem.nextblock_store; eauto.

    + (* [simrel_loadbytes] *)
      intros w m1 m2 Hm b1 b2 Hb ofs sz.
      destruct Hm; subst.
      apply coreflexivity in Hb; subst.
      rewrite match_memval_simrel_strong_id.
      reflexivity.

    + (* [simrel_storebytes] *)
      intros w m1 m2 Hm b1 b2 Hb ofs vs1 vs2 Hvs.
      destruct Hm; subst.
      apply coreflexivity in Hb; subst.
      apply coreflexivity in Hvs; subst.
    destruct (Mem.storebytes _ _ _ _) eqn:STORE; constructor.
    exists (Mem.nextblock m).
    split; try reflexivity.
    constructor.
    symmetry; eapply Mem.nextblock_storebytes; eauto.

    + (* [simrel_perm] *)
      intros w m1 m2 Hm b1 b2 Hb ofs k pe.
      destruct Hm; subst.
      apply coreflexivity in Hb; subst.
      reflexivity.

    + (* [simrel_valid_block] *)
      inversion 1.
      reflexivity.
  Qed.

  Definition simrel_strong_id: simrel D D :=
    {|
      simrel_ops := simrel_strong_id_ops
    |}.

End STRONG_IDENTITY.
