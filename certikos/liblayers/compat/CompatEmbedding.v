Require Import SimulationRelation.
Require Import AbstractData.
Require Import CompatData.

Require Import Structures.
Require Import CompcertStructures.
Require Import CompatCPrimitives.
Require Import CompatAsmPrimitives.
Require Import AsmPrimitives.
Require Import RelationPairs.

Section COMPAT_REL.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: !UseMemWithData mem}.

  (** * Simulation relations *)

  (** Slightly mismatched version of the properties in
    [MatchExtcallStates]. For instance the latter allows source blocks
    to be injected to the same target block. This is necessary to make
    these conditions independent of any memory state or memory
    injection predicate.

    An alternative solution would be to use a [(f, m1, m2)] tuple such
    that [Mem.inject f m1 m2] as elements of our [simrel_carrier],
    with suitably altered [match_mem] and [match_block] definitions.
   *)
  Record compatrel_embed_meminj_wf (f: meminj) :=
    {
      compatrel_embed_meminj_coarse b1 b2 δ:
        f b1 = Some (b2, δ) ->
        δ = 0%Z;
      compatrel_embed_meminj_injective b1 b2 b δ1 δ2:
        f b1 = Some (b, δ1) ->
        f b2 = Some (b, δ2) ->
        b1 = b2;
      compatrel_embed_meminj_flat:
        inject_incr (Mem.flat_inj glob_threshold) f
    }.

  Program Definition compatrel_embed_ops D1 D2 (R: compatrel D1 D2):
    simrel_components (mwd D1) (mwd D2) :=
    {|
      simrel_carrier :=
        sig compatrel_embed_meminj_wf;
      simrel_carrier_le :=
        {| le := (inject_incr @@ (@proj1_sig _ _))%signature |};
      simrel_undef_matches_values :=
        True;
      simrel_undef_matches_block p b :=
        True;
      match_mem f m1 m2 :=
        MatchExtcallStates R f (fst m1) (snd m1) (fst m2) (snd m2);
      match_block f b1 b2 :=
        f b1 = Some (b2, 0%Z)
    |}.

  Local Instance: forall A P, Measure (@proj1_sig A P).

  Require Import ExtensionalityAxioms.

  Program Lemma compatrel_embed_match_val D1 D2 R f:
    match_val (compatrel_embed_ops D1 D2 R) f =
    val_inject f.
  Proof.
    intros.
    eapply functional_extensionality; intro v1.
    eapply functional_extensionality; intro v2.
    eapply prop_ext; split; intro H.
    - destruct H; simpl in *; econstructor; eauto.
      + symmetry.
        apply Int.add_zero.
    - destruct H; simpl; try constructor.
      + destruct f as [f Hf]; simpl in *.
        pose proof (compatrel_embed_meminj_coarse f Hf _ _ _ H); subst.
        rewrite Int.add_zero.
        constructor; eauto.
      + destruct v; repeat constructor.
  Qed. 

  Program Lemma compatrel_embed_match_memval D1 D2 R f:
    match_memval (compatrel_embed_ops D1 D2 R) f =
    memval_inject f.
  Proof.
    intros.
    eapply functional_extensionality; intro v1.
    eapply functional_extensionality; intro v2.
    eapply prop_ext; split; intro H.
    - destruct H; simpl in *; econstructor; eauto.
      + symmetry.
        apply Int.add_zero.
    - destruct H; simpl; try constructor.
      + destruct f as [f Hf]; simpl in *.
        pose proof (compatrel_embed_meminj_coarse f Hf _ _ _ H); subst.
        rewrite Int.add_zero.
        constructor; eauto.
      + destruct mv; repeat constructor.
  Qed. 

  Global Instance compatrel_embed_prf D1 D2 R:
    SimulationRelation (compatrel_embed_ops D1 D2 R).
  Proof.
    split.
    - split; typeclasses eauto.
    - constructor.
    - intros f1 f2 H b1 b2.
      apply H.
    - constructor.
    - constructor.
    - simpl.
      congruence.
    - intros [f Hf] b1 b2 b.
      simpl.
      apply compatrel_embed_meminj_injective; eauto.
    - intros [f Hf] b Hb.
      simpl.
      eapply compatrel_embed_meminj_flat; eauto.
      Transparent block_is_global. (* just this once *)
      unfold Mem.flat_inj, block_is_global in *.
      Opaque block_is_global.
      destruct (plt b glob_threshold).
      + reflexivity.
      + contradiction.
    - (* Mem.alloc *)
      intros [f Hf] [m1 d1] [m2 d2] Hmd lo hi.
      simpl in Hmd.
      destruct Hmd.
      destruct (Mem.alloc m1 lo hi) as [m1' b1] eqn:Halloc1.
      edestruct Mem.alloc_parallel_inject
        as (f' & m2' & b2 & Halloc2 & Hm' & Hff' & Hfb & Hfnb);
        eauto.
      { reflexivity. }
      { reflexivity. }
      assert (Hf': compatrel_embed_meminj_wf f').
      {
        split.
        - intros x1 x2 δ Hx1.
          destruct (Decision.decide (x1 = b1)).
          * subst.
            congruence.
          * rewrite Hfnb in Hx1 by eauto.
            eapply compatrel_embed_meminj_coarse; eauto.
        - intros x1 x2 x δ1 δ2 H1 H2.
          admit. (* inj extended with new block still injective *)
        - admit. (* inj extended with new block still flat on globals *)
      }
      exists (exist _ f' Hf').
      split; eauto.
      lift_auto.
      rewrite Halloc1, Halloc2.
      split; simpl; eauto.
      pose proof (Mem.alloc_result _ _ _ _ _ Halloc1).
      pose proof (Mem.alloc_result _ _ _ _ _ Halloc2).
      subst.
      constructor; eauto.
      + eapply relate_incr; eauto.
      + eapply alloc_match_correct; eauto.
        intros i b Hi Hb.
        assert (H: b < Mem.nextblock m1) by eauto.
        intros H'.
        subst.
        xomega.
      + etransitivity; eauto.
      + intros b1 b2 delta Hb.
        destruct (Decision.decide (b1 = Mem.nextblock m1)).
        * subst.
          assert (b2 = Mem.nextblock m2) by congruence; subst.
          split; eauto.
          eapply compatrel_embed_meminj_coarse; eauto.
        * rewrite Hfnb in Hb by eauto.
          eauto.
      + erewrite (Mem.nextblock_alloc _ _ _ m1') by eauto.
        erewrite (Mem.nextblock_alloc _ _ _ m2') by eauto.
        rewrite <- Pos.succ_le_mono.
        assumption.
      + intros i b ofs k p Hi Hb.
        intros H.
        eapply Mem.perm_alloc_4 in H; eauto.
        * eapply match_newglob_noperm; eauto.
        * assert (Hnb: b < Mem.nextblock m1) by eauto.
          intros Hnb'.
          subst.
          xomega.
      + intros.
        transitivity (Mem.nextblock m1); eauto.
        erewrite (Mem.nextblock_alloc _ _ _ m1') by eauto.
        apply Plt_succ.
      + destruct Hf'; eauto.
    - (* Mem.free *)
      intros [f Hf] [m1 d1] [m2 d2] Hm b1 b2 Hb lo hi.
      simpl in *.
      destruct Hm.
      lift_unfold.
      destruct (Mem.free m1 _ _ _) as [m1'|] eqn:Hm1'; try constructor.
      assert (Hm2': exists m2', Mem.free m2 b2 lo hi = Some m2').
      {
        eapply Mem.range_perm_free.
        pose proof (Mem.range_perm_inject f m1 m2 b1 b2 0%Z lo hi) as Hfp.
        erewrite !Z.add_0_r in Hfp.
        eapply Hfp; eauto.
        eapply Mem.free_range_perm; eauto.
      }
      destruct Hm2' as [m2' Hm2'].
      rewrite Hm2'.
      constructor.
      simpl.
      constructor; eauto.
      + eapply (Mem.free_inject f m1 ((b1, lo, hi)::nil) m1' m2 b2 lo hi); eauto.
        * simpl.
          rewrite Hm1'.
          reflexivity.
        * simpl.
          intros b1' delta ofs k p Hb1' Hperm Hrange.
          assert (delta = 0%Z) by eauto using compatrel_embed_meminj_coarse.
          assert (b1' = b1) by eauto using compatrel_embed_meminj_injective.
          subst.
          rewrite Z.add_0_r in Hrange.
          eauto.
      + eapply free_match_correct; eauto.
        intros i b Hi Hib H; subst.
        admit. (* unfortunately [match_newglob_noperm] and [Mem.free_range_perm] don't suffice to establish this prerequisite, because it's technically possible to free a null range in the high mem despite there being no permissions. So we have to strengthen the property in [SimulationRelation] for now. Ultimately, I think the foo_match_correct properties should all be replaced by a single mem_unchanged_on_global_match_correct, which would be simpler to prove once and for all. *)
(*        assert (b1 = b2) by admit; subst. (* separate properties of match_block? so that we can use match_global_block_eq? *)
        eapply match_newglob_noperm; eauto.
        eapply Mem.free_range_perm; eauto.
        instantiate (1 := lo).
        split; try reflexivity.
        eassumption. *)
      + erewrite (Mem.nextblock_free m1 _ _ _ m1') by eauto.
        erewrite (Mem.nextblock_free m2 _ _ _ m2') by eauto.
        assumption.
      + intros i b ofs k p Hi Hib H.
        eapply Mem.perm_free_3 in H; eauto.
        eapply match_newglob_noperm; eauto.
      + intros.
        rewrite (Mem.nextblock_free m1 _ _ _ m1') by eauto.
        eauto.
    - (* Mem.load *)
      intros [f Hf] chunk [m1 d1] [m2 d2] Hm b1 b2 Hb ofs.
      simpl in *.
      destruct Hm.
      lift_unfold.
      rewrite compatrel_embed_match_val.
      destruct (Mem.load chunk m1 b1 ofs) as [v1|] eqn:Hv1; try constructor.
      edestruct (Mem.load_inject f m1 m2) as (v2 & Hv2 & Hv); eauto.
      rewrite Z.add_0_r in Hv2.
      rewrite Hv2.
      constructor; eauto.
    - (* Mem.store *)
      intros [f Hf] chunk [m1 d1] [m2 d2] Hm b1 b2 Hb ofs v1 v2 Hv.
      simpl in *.
      rewrite compatrel_embed_match_val in Hv.
      destruct Hm.
      lift_unfold.
      destruct (Mem.store _ m1 b1 ofs v1) as [m1'|] eqn:Hm1'; try constructor.
      edestruct (Mem.store_mapped_inject f) as (m2' & Hm2' & Hm'); eauto.
      rewrite Z.add_0_r in Hm2'.
      rewrite Hm2'.
      constructor.
      simpl.
      constructor; eauto.
      + eapply store_match_correct; eauto.
        intros i b Hi Hib H.
        subst.
        eapply match_newglob_noperm; eauto.
        eapply Mem.store_valid_access_3 in Hm1'.
        destruct Hm1' as [Hm1' _].
        assert (b1 = b2) by admit; subst.
        eapply Hm1'.
        instantiate (1 := ofs).
        destruct chunk; simpl; xomega.
      + erewrite (Mem.nextblock_store _ m1 _ _ _ m1') by eauto.
        erewrite (Mem.nextblock_store _ m2 _ _ _ m2') by eauto.
        assumption.
      + intros i b ofs' k p Hi Hib H.
        eapply Mem.perm_store_2 in H; eauto.
        eapply match_newglob_noperm; eauto.
      + intros.
        rewrite (Mem.nextblock_store _ m1 _ _ _ m1') by eauto.
        eauto.
    - (* Mem.loadbytes *)
      intros [f Hf] [m1 d1] [m2 d2] Hm b1 b2 Hb ofs sz.
      simpl in *.
      destruct Hm.
      lift_unfold.
      rewrite compatrel_embed_match_memval.
      simpl.
      destruct (Mem.loadbytes m1 b1 ofs sz) as [v1|] eqn:Hv1; try constructor.
      edestruct (Mem.loadbytes_inject f m1 m2) as (v2 & Hv2 & Hv); eauto.
      rewrite Z.add_0_r in Hv2.
      rewrite Hv2.
      constructor; eauto.
      admit. (* list_rel vs. list_forall2 *)
    - (* Mem.storebytes *)
      intros [f Hf] [m1 d1] [m2 d2] Hm b1 b2 Hb ofs v1 v2 Hv.
      simpl in *.
      rewrite compatrel_embed_match_memval in Hv.
      destruct Hm.
      lift_unfold.
      destruct (Mem.storebytes m1 b1 ofs v1) as [m1'|] eqn:Hm1'; try constructor.
      edestruct (Mem.storebytes_mapped_inject f) as (m2' & Hm2' & Hm'); eauto.
      instantiate (1:=v2); admit. (* list_forall2 vs. list_rel *)
      rewrite Z.add_0_r in Hm2'.
      rewrite Hm2'.
      constructor.
      simpl.
      constructor; eauto.
      + eapply storebytes_match_correct; eauto.
        admit. (* Same issue as free: may store no bytes *)
      + erewrite (Mem.nextblock_storebytes m1 _ _ _ m1') by eauto.
        erewrite (Mem.nextblock_storebytes m2 _ _ _ m2') by eauto.
        assumption.
      + intros i b ofs' k p Hi Hib H.
        eapply Mem.perm_storebytes_2 in H; eauto.
        eapply match_newglob_noperm; eauto.
      + intros.
        rewrite (Mem.nextblock_storebytes m1 _ _ _ m1') by eauto.
        eauto.
    - intros [f Hf] [m1 d1] [m2 d2] Hm b1 b2 Hb ofs k p H.
      simpl in *.
      destruct Hm.
      lift_unfold.
      eapply Mem.perm_inject in H; eauto.
      rewrite Z.add_0_r in H.
      assumption.
  Qed.

  Definition compatrel_embed D1 D2 (R: compatrel D1 D2): simrel D1 D2 :=
    {|
      simrel_ops := compatrel_embed_ops D1 D2 R
    |}.

  (** * Primitives *)

  Definition sprimcall_embed (D: compatdata) (σ: sprimcall_primsem D) :=
    {|
      asmprimitive_step s s' :=
        sprimcall_step σ (fst s) (snd s) (fst s') (snd s')
    |}.

  (** * Invariant preservation properties *)

  Lemma asmprim_inv_high_level_invariant (D: compatdata) rs m d:
    asmprim_inv D rs m d ->
    high_level_invariant d.
  Proof.
    intros [[Hhl _] _ _ _ _].
    assumption.
  Qed.

  Lemma asmprim_inv_low_level_invariant (D: compatdata) rs m d:
    asmprim_inv D rs m d ->
    low_level_invariant (Mem.nextblock m) d.
  Proof.
    intros [[_ Hll] _ _ _ _].
    assumption.
  Qed.

  Lemma asmprim_inv_asm_invariant D rs m d:
    asmprim_inv D rs m d ->
    asm_invariant rs (m, d).
  Proof.
    intros Hinv.
    destruct Hinv.
    split; eauto.
    split; eauto.
  Qed.

  Lemma asmprim_inv_embed (D: compatdata) rs m d:
    high_level_invariant d ->
    low_level_invariant (Mem.nextblock m) d ->
    asm_invariant rs (m, d) ->
    asmprim_inv D rs m d.
  Proof.
    intros Hhl Hll [[Hval Hmwf Hrwf] Hrwt].
    split; eauto.
    split; eauto.
  Qed.

  Global Instance sprimcall_embed_invariants D (σ: sprimcall_primsem D):
    PrimcallInvariants σ ->
    AsmPrimitivePreservesInvariant D (sprimcall_embed D σ).
  Proof.
    intros [Hasm Hll Hhl Hnb].
    split.
    - intros rs m d rs' m' d' H Hinv.
      simpl in H.
      pose proof (asmprim_inv_high_level_invariant D rs m d Hinv).
      pose proof (asmprim_inv_low_level_invariant D rs m d Hinv).
      pose proof (asmprim_inv_asm_invariant D rs m d Hinv).
      eapply asmprim_inv_embed; eauto.
      eapply Hll; eauto.
      destruct H2 as [[] ].
      split; eauto.
      split; eauto.
    - eapply Hnb.
  Qed.

  (** * Simulation diagrams *)

  Global Instance sprimcall_embed_le:
    Proper
      (∀ -, sprimcall_primsem_le ++> asmprim_sim _ _ simrel_id)
      sprimcall_embed.
  Proof.
    intros D σ1 σ2 [Hσ Hsig].
    eapply asmprim_sim_id_intro.
    simpl.
    solve_monotonic.
  Qed.

  Global Instance sprimcall_embed_rel:
    Proper
      (∀ R, sprimcall_sim R ++> asmprim_sim _ _ (compatrel_embed _ _ R))
      sprimcall_embed.
  Proof.
    intros D1 D2 R σ1 σ2 Hσ.
    split.
    - intros [f Hf] s1 s2 Hs (rs1' & m1' & d1') Hstep1.
      destruct Hs as [rs1 m1 d1 rs2 m2 d2 Hinv1 Hinv2 Hrs Hm]; simpl in *.
      destruct Hinv1 as [[Hhl1 Hll1] Hvalid1 Hmwf1 Hrwf1 Hrwt1].
      destruct Hinv2 as [[Hhl2 Hll2] Hvalid2 Hmwf2 Hrwf2 Hrwt2].
      edestruct (sprimcall_sim_step R _ _ Hσ f rs1 m1 d1 rs1' m1' d1' rs2 m2 d2)
        as (f' & rs2' & m2' & d2' & Hstep2 & Hs');
        eauto.
      {
        constructor; eauto.
        constructor; eauto.
      }
      {
        constructor; eauto.
        admit. (* val_inject vs. match_val *)
      }
      exists (rs2', (m2', d2')).
      simpl.
      split; eauto.
      assert (Hf': compatrel_embed_meminj_wf f').
      {
        admit. (* not possible because of mismatch *)
      }
      exists (exist _ f' Hf').
      split.
      {
        admit. (* need to add [inject_incr] to  [sprimcall_sim] *)
      }
      destruct Hs' as [Hs' Hrs'].
      split; simpl; eauto.
      intro i; simpl.
      rewrite compatrel_embed_match_val; simpl.
      eauto.
    - intros _.
      eapply sprimcall_embed_invariants.
      eapply sprimcall_sim_invs.
      eassumption.
  Qed.

  Require Import CompatPrimSem.
  Require Import CompatCallConv.

  Definition compatsem_sprimcall_primsem D (σ: compatsem D) :=
    match σ with
      | inl σc => callconv_primsem D σc
      | inr σasm => σasm
    end.

  Global Instance compatsem_sprimcall_primsem_le:
    Proper
      (∀ -, compatsem_le _ ++> sprimcall_primsem_le)
      compatsem_sprimcall_primsem.
  Proof.
    unfold compatsem_sprimcall_primsem.
    intros D σ1 σ2 Hσ.
    destruct Hσ; simpl; solve_monotonic.
  Qed.

  Global Instance compatsem_sprimcall_primsem_rel:
    Proper
      (∀ R, compatsim_def R ++> sprimcall_sim R)
      compatsem_sprimcall_primsem.
  Proof.
    unfold compatsem_sprimcall_primsem.
    intros D1 D2 R σ1 σ2 Hσ.
    destruct Hσ; simpl; solve_monotonic.
  Qed.

  Definition compatsem_embed D (σ: compatsem D) :=
    sprimcall_embed D (compatsem_sprimcall_primsem D σ).

  Global Instance compatsem_embed_le:
    Proper
      (∀ -, compatsem_le _ ++> asmprim_sim _ _ simrel_id)
      compatsem_embed.
  Proof.
    unfold compatsem_embed.
    solve_monotonic.
  Qed.

  Global Instance compatsem_embed_rel:
    Proper
      (∀ R, compatsim_def R ++> asmprim_sim _ _ (compatrel_embed _ _ R))
      compatsem_embed.
  Proof.
    unfold compatsem_embed.
    solve_monotonic.
  Qed.

  (** * Determinism *)

  Global Instance sprimcall_embed_props D (σ: sprimcall_primsem D):
    PrimcallProperties σ ->
    AsmPrimitiveDeterministic D (sprimcall_embed D σ).
  Proof.
    intros [Hdet].
    split.
    - intros [rs m] [rs1 m1] [rs2 m2].
      simpl.
      intros.
      destruct (Hdet rs m rs1 m1 rs2 m2); eauto.
      congruence.
  Qed.

  (** * Layers (remove?) *)

  Require Import Maps.
  Require Import AST.
  Require Import PTreeLayers.
  Require Import MakeProgram.

  Local Existing Instance ptree_layer_sim_op.
  Local Existing Instance ptree_layer_ops.
  Local Existing Instance ptree_layer_prf.

  Fixpoint compatrel_path_embed D1 D2 (R: path compatrel D1 D2): simrel D1 D2 :=
    match R with
      | path_nil =>
        simrel_id
      | path_cons D2 D3 R Rs =>
        simrel_compose (compatrel_embed D1 D2 R) (compatrel_path_embed D2 D3 Rs)
    end.

  Global Instance compatsem_embed_rel_path:
    Proper
      (∀ R, path_sim compatsem_le (@compatsim_def _ _ _) _ _ R ++>
            asmprim_sim _ _ (compatrel_path_embed _ _ R))
      compatsem_embed.
  Proof.
    intros D1 D2 R.
    induction R.
    - solve_monotonic.
    - intros σ1 σ3 Hσ13.
      apply rtransitivity in Hσ13.
      destruct Hσ13 as (σ2 & Hσ12 & Hσ23).
      simpl.
      htransitivity (compatsem_embed v2 σ2);
      solve_monotonic.
  Qed.

  Definition ptree_layer_embed D:
    ptree_layer compatsem (globvar Ctypes.type) D ->
    ptree_layer asmprimitive (globvar unit) D :=
    fun L =>
      (Maps.PTree.map (fun _ => fmap (compatsem_embed D)) (fst L),
       Maps.PTree.map (fun _ => fmap (globvar_map (fun _ => tt))) (snd L)).

  Global Instance ptree_layer_embed_rel:
    Proper
      (∀ R : (path compatrel) D1 D2, sim R ++> sim (compatrel_path_embed _ _ R))
      ptree_layer_embed.
  Proof.
    unfold ptree_layer_embed.
    simpl sim.
    solve_monotonic idtac.
    congruence.
  Qed.
End COMPAT_REL.
