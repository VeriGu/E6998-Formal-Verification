(** Although [SimulationRelation] includes a lot of properties, many
  of them are straightforward to prove, and many proofs end up being
  very similar. In this file we provide ready-to-use proofs for
  [simrel_components] which satisfy some common properties. *)

Require Export SimrelDefinition.

Section WITHMEM.
  Context `{Hmem: BaseMemoryModel}.
  Context D1 D2 (R: simrel_components D1 D2).


  (** * Trivial Kripke frames *)

  (** Often we use a trivial Kripke frame, then monotonicity wrt. the
    accessibility relation is trivial to prove. *)

  Class TrivialWorld :=
    {
      simrel_trivial_acc:
        le (A := simrel_world R) = eq;
    }.

  Section TRIVIAL_WORLD.
    Context `{HR: TrivialWorld}.

    Global Instance simrel_tw_acc_preorder:
      @PreOrder (simrel_world R) (≤).
    Proof.
      rewrite simrel_trivial_acc.
      typeclasses eauto.
    Qed.

    Global Instance simrel_tw_acc_undef_matches_pointer:
      Monotonic (simrel_undef_matches_block R) ((≤) ++> - ==> impl).
    Proof.
      rewrite simrel_trivial_acc.
      repeat rstep.
      congruence.
    Qed.

    Global Instance simrel_acc_meminj:
      Monotonic (simrel_meminj R) ((≤) ++> - ==> option_le eq).
    Proof.
      rewrite simrel_trivial_acc.
      repeat rstep.
      subst.
      reflexivity.
    Qed.
  End TRIVIAL_WORLD.


  (** * Coreflexive [match_val] *)

  (** ** Definition *)

  (** If [simrel_meminj] is a sub-injection of [inject_id] and the
    relation does not refine [Vundef], then the corresponding
    [match_val] is coreflexive. *)

  Class CoreflexiveInjection :=
    {
      simrel_meminj_corefl w:
        inject_incr (simrel_meminj R w) inject_id;
      simrel_undef_matches_values_corefl:
        simrel_undef_matches_values_bool R = false;
      simrel_undef_matches_block_corefl w b:
        ~ simrel_undef_matches_block R w b;
    }.

  (** ** Properties *)

  Section COREFL_MEMINJ.
    Context `{HR: CoreflexiveInjection}.

    Global Instance simrel_corefl_acc_undef_matches_pointer:
      Monotonic (simrel_undef_matches_block R) ((≤) ++> - ==> impl).
    Proof.
      intros w1 w2 _ b.
      generalize (simrel_undef_matches_block_corefl w1 b).
      generalize (simrel_undef_matches_block_corefl w2 b).
      clear.
      firstorder.
    Qed.

    Global Instance match_ptr_corefl w:
      Coreflexive (match_ptr R w).
    Proof.
      intros ptr1 ptr2 Hptr.
      destruct Hptr.
      apply simrel_meminj_corefl in H.
      inversion H; clear H; subst.
      rewrite Z.add_0_r.
      reflexivity.
    Qed.

    Global Instance match_ptrbits_corefl w:
      Coreflexive (match_ptrbits R w).
    Proof.
      intros ptr1 ptr2 Hptr.
      destruct Hptr.
      apply simrel_meminj_corefl in H.
      inversion H; subst.
      rewrite Ptrofs.add_zero.
      reflexivity.
    Qed.

    Global Instance match_ptrrange_corefl w:
      Coreflexive (match_ptrrange R w).
    Proof.
      intros r1 r2 Hr.
      destruct Hr as [b1 ofs1 b2 ofs2 delta Hptr].
      apply coreflexivity in Hptr.
      inversion Hptr; clear Hptr; subst.
      reflexivity.
    Qed.

    Global Instance match_val_corefl w:
      Coreflexive (match_val R w).
    Proof.
      pose proof simrel_undef_matches_values_corefl as Humvn.
      intros v1 v2 Hv.
      destruct Hv; eauto; try congruence.
      - apply coreflexivity in H.
        congruence.
      - apply simrel_undef_matches_block_corefl in H.
        contradiction.
    Qed.

    Global Instance match_memval_corefl w:
      Coreflexive (match_memval R w).
    Proof.
      pose proof simrel_undef_matches_values_corefl as Humvn.
      intros v1 v2 Hv.
      destruct Hv; eauto; try congruence.
      destruct H; eauto; try congruence.
      - apply coreflexivity in H.
        congruence.
      - apply simrel_undef_matches_block_corefl in H.
        contradiction.
    Qed.

    Global Instance match_block_corefl w:
      Coreflexive (match_block R w).
    Proof.
      intros b1 b2 Hb.
      destruct Hb.
      apply simrel_meminj_corefl in H.
      inversion H.
      reflexivity.
    Qed.

    Global Instance match_block_sameofs_corefl w:
      Coreflexive (match_block_sameofs R w).
    Proof.
      intros b1 b2 Hb.
      red in Hb.
      apply simrel_meminj_corefl in Hb.
      inversion Hb.
      reflexivity.
    Qed.

    Lemma simrel_corefl_undef_matches_values_also_block w ptr1 b2 ofs2:
      simrel_undef_matches_values R ->
      match_ptrbits R w ptr1 (b2, ofs2) ->
      simrel_undef_matches_block R w b2.
    Proof.
      intros Huv _.
      exfalso.
      red in Huv.
      rewrite simrel_undef_matches_values_corefl in Huv.
      discriminate.
    Qed.

    Lemma simrel_corefl_undef_matches_block_also_values w b2:
      simrel_undef_matches_block R w b2 ->
      simrel_undef_matches_values R.
    Proof.
      intros Hub.
      exfalso.
      apply simrel_undef_matches_block_corefl in Hub.
      contradiction.
    Qed.

    Lemma simrel_corefl_undef_matches_block_or_injective w b2:
      forall b1 b1',
        b1' <> b1 ->
        match_block R w b1 b2 ->
        match_block R w b1' b2 ->
        simrel_undef_matches_block R w b2.
    Proof.
      intros b1 b1' Hb1 Hb Hb'.
      exfalso.
      apply coreflexivity in Hb.
      apply coreflexivity in Hb'.
      congruence.
    Qed.

    Lemma simrel_corefl_different_pointers_inject:
      forall w m m' b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
        match_mem R w m m' ->
        b1 <> b2 ->
        Mem.valid_pointer m b1 (Ptrofs.unsigned ofs1) = true ->
        Mem.valid_pointer m b2 (Ptrofs.unsigned ofs2) = true ->
        simrel_meminj R w b1 = Some (b1', delta1) ->
        simrel_meminj R w b2 = Some (b2', delta2) ->
        b1' <> b2' \/
        Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) <>
        Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)).
    Proof.
      intros w m m' b1 ofs1 b2 ofs2 b1' delta1 b2' delta2.
      intros _ Hb _ _ Hb1 Hb2.
      left.
      apply simrel_meminj_corefl in Hb1.
      apply simrel_meminj_corefl in Hb2.
      unfold inject_id in *.
      inversion Hb1; clear Hb1.
      inversion Hb2; clear Hb2.
      congruence.
    Qed.

    Lemma simrel_corefl_weak_valid_pointer_address_inject_weak:
      forall w m1 m2 b1 b2 delta,
        match_mem R w m1 m2 ->
        simrel_meminj R w b1 = Some (b2, delta) ->
        exists delta',
          forall ofs1,
            Mem.weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs1) = true ->
            Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) =
            (Ptrofs.unsigned ofs1 + delta')%Z.
    Proof.
      intros w m1 m2 b1 b2 delta.
      intros _ H.
      exists delta.
      intros ofs1 _.
      apply simrel_meminj_corefl in H.
      inversion H; clear H.
      rewrite Ptrofs.add_zero.
      rewrite Z.add_0_r.
      reflexivity.
    Qed.

    Lemma simrel_corefl_address_inject:
      forall w m1 m2 b1 ofs1 b2 delta pe,
        match_mem R w m1 m2 ->
        Mem.perm m1 b1 (Ptrofs.unsigned ofs1) Cur pe ->
        simrel_meminj R w b1 = Some (b2, delta) ->
        Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) =
        (Ptrofs.unsigned ofs1 + delta)%Z.
    Proof.
      intros w m1 m2 b1 ofs1 b2 delta pe.
      intros _ _ H.
      apply simrel_meminj_corefl in H.
      inversion H; clear H.
      rewrite Ptrofs.add_zero.
      rewrite Z.add_0_r.
      reflexivity.
    Qed.

    Lemma simrel_corefl_aligned_area_inject:
      forall w m m' b ofs al sz b' delta,
        match_mem R w m m' ->
        (al = 1 \/ al = 2 \/ al = 4 \/ al = 8) ->
        sz > 0 ->
        (al | sz) ->
        Mem.range_perm m b ofs (ofs + sz) Cur Nonempty ->
        (al | ofs) ->
        simrel_meminj R w b = Some (b', delta) ->
        (al | ofs + delta).
    Proof.
      intros w m m' b ofs al sz b' delta.
      intros _ _ _ Hsz _ Hofs H.
      apply simrel_meminj_corefl in H.
      inversion H; clear H.
      rewrite Z.add_0_r.
      assumption.
    Qed.

    Lemma simrel_corefl_disjoint_or_equal_inject:
      forall w m m' b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 sz,
        match_mem R w m m' ->
        simrel_meminj R w b1 = Some (b1', delta1) ->
        simrel_meminj R w b2 = Some (b2', delta2) ->
        Mem.range_perm m b1 ofs1
                       (ofs1 + sz) Max Nonempty ->
        Mem.range_perm m b2 ofs2
                       (ofs2 + sz) Max Nonempty ->
        sz > 0 ->
        b1 <> b2 \/
        ofs1 = ofs2 \/
        ofs1 + sz <= ofs2 \/ ofs2 + sz <= ofs1 ->
        b1' <> b2' \/
        (ofs1 + delta1 = ofs2 + delta2)%Z \/
        ofs1 + delta1 + sz <= ofs2 + delta2 \/
        ofs2 + delta2 + sz <= ofs1 + delta1.
    Proof.
      intros w m m' b1 b1' delta' b2 b2' delta2 ofs1 ofs2 sz.
      intros _ H1 H2 _ _ _ H.
      apply simrel_meminj_corefl in H1; inversion H1; clear H1.
      apply simrel_meminj_corefl in H2; inversion H2; clear H2.
      rewrite !Z.add_0_r.
      destruct H; eauto.
      left; congruence.
    Qed.

    (** ** Simplified proof *)

    Class CoreflexiveSimulationRelation :=
      {
        simrel_corefl_acc_preorder:
          @PreOrder (simrel_world R) (≤);

        simrel_corefl_acc_meminj:
          Monotonic (simrel_meminj R) ((≤) ++> - ==> option_le ⊤);

        simrel_corefl_weak_valid_pointer w m1 m2 b ofs:
          match_mem R w m1 m2 ->
          Mem.weak_valid_pointer m1 b (Ptrofs.unsigned ofs) =
          Mem.weak_valid_pointer m2 b (Ptrofs.unsigned ofs);

        simrel_corefl_undef_matches_block_invalid w m1 m2 b ofs:
          match_mem R w m1 m2 ->
          Mem.valid_pointer m1 b (Ptrofs.unsigned ofs) = false ->
          Mem.valid_pointer m2 b (Ptrofs.unsigned ofs) = false;

        corefl_match_undef_global_block_sameofs w b:
          block_is_global b ->
          simrel_meminj R w b <> None;

        simrel_corefl_init_mem {F V}:
          Monotonic
            (Genv.init_mem (F:=F) (V:=V))
            (simrel_program_rel R ++>
             option_le (rexists w, match_mem R w));

        simrel_corefl_alloc w:
          Monotonic
            Mem.alloc
            (match_mem R w ++> - ==> - ==>
             incr w (match_mem R w * match_block_sameofs R w));

        simrel_corefl_free w:
          Monotonic
            Mem.free
            (match_mem R w ++> match_block R w ++> - ==> - ==>
             option_le (incr w (match_mem R w)));

        simrel_corefl_load w:
          Monotonic
            Mem.load
            (- ==> match_mem R w ++> match_block R w ++> - ==>
             option_le (match_val R w));

        simrel_corefl_store w:
          Monotonic
            Mem.store
            (- ==> match_mem R w ++> match_block R w ++> - ==> match_val R w ++>
             option_le (incr w (match_mem R w)));

        simrel_corefl_loadbytes w:
          Monotonic
            Mem.loadbytes
            (match_mem R w ++> match_block R w ++> - ==> - ==>
             option_le (list_rel (match_memval R w)));

        simrel_corefl_storebytes w:
          Monotonic
            Mem.storebytes
            (match_mem R w ++> match_block R w ++> - ==>
             list_rel (match_memval R w) ++>
             option_le (incr w (match_mem R w)));

        simrel_corefl_perm w:
          Monotonic
            Mem.perm
            (match_mem R w ++> match_block R w ++> - ==> - ==> - ==> impl);

        simrel_corefl_valid_block p:
          Monotonic
            Mem.valid_block
            (match_mem R p ++> - ==> iff);
      }.

    Global Instance simrel_corefl_prf `{CoreflexiveSimulationRelation}:
      SimulationRelation R.
    Proof.
      split; try typeclasses eauto.
      - apply simrel_corefl_acc_preorder.
      - intros w1 w2 Hw b.
        pose proof (simrel_corefl_acc_meminj w1 w2 Hw b) as Hb'.
        destruct (simrel_meminj R w1 b) as [[b1' o1]|] eqn:Hb1'; try constructor.
        inversion Hb' as [xb1' | xb1' [b2' o2] _ Hxb1' Hb2']; clear Hb'; subst.
        constructor.
        symmetry in Hb2'.
        apply simrel_meminj_corefl in Hb1'.
        apply simrel_meminj_corefl in Hb2'.
        congruence.
      - apply simrel_corefl_undef_matches_values_also_block.
      - apply simrel_corefl_undef_matches_block_also_values.
      - apply simrel_corefl_undef_matches_block_or_injective.
      - intros w m1 m2 b1 ofs1 b2 ofs2 Hm H1 Hptr H2.
        apply coreflexivity in Hptr.
        inversion Hptr; clear Hptr; subst.
        erewrite simrel_corefl_weak_valid_pointer in H1 by eauto.
        congruence.
      - intros w m1 m2 b1 ofs1 b2 ofs2 Hm H1 Hptr H2.
        apply coreflexivity in Hptr.
        inversion Hptr; clear Hptr; subst.
        eapply simrel_corefl_undef_matches_block_invalid in H1; eauto.
        congruence.
      - intros w b Hb.
        apply (corefl_match_undef_global_block_sameofs w) in Hb.
        unfold Proper, match_block_sameofs.
        destruct (simrel_meminj R w b) as [[b' delta]|] eqn:Hb'; [ | congruence].
        apply simrel_meminj_corefl in Hb'.
        unfold inject_id in Hb'.
        congruence.
      - intros F V.
        apply simrel_corefl_init_mem.
      - apply simrel_corefl_alloc.
      - intros w m1 m2 Hm [[b1 lo1] hi1] [[b2 lo2] hi2] Hrange.
        unfold uncurry.
        pose proof (coreflexivity _ _ Hrange) as Hrange_eq.
        apply match_ptrrange_ptr in Hrange.
        apply match_ptr_block in Hrange.
        inversion Hrange_eq; clear Hrange_eq; subst.
        edestruct (simrel_corefl_free w m1 m2 Hm b2 b2 Hrange lo2 hi2);
          constructor; eauto.
      - intros w chunk m1 m2 Hm [b1 ofs1] [b2 ofs2] Hptr.
        unfold uncurry.
        pose proof (coreflexivity _ _ Hptr) as Hptr_eq.
        inversion Hptr_eq; clear Hptr_eq; subst.
        apply match_ptr_block in Hptr.
        apply simrel_corefl_load; eauto.
      - intros w chunk m1 m2 Hm [b1 ofs1] [b2 ofs2] Hptr v1 v2 Hv.
        unfold uncurry.
        pose proof (match_ptr_block _ _ _ _ _ Hptr) as Hblock.
        apply coreflexivity in Hptr; inversion Hptr; clear Hptr; subst.
        apply simrel_corefl_store; eauto.
      - intros w m1 m2 Hm [b1 ofs1] [b2 ofs2] Hptr sz.
        unfold uncurry.
        pose proof (match_ptr_block _ _ _ _ _ Hptr) as Hblock.
        apply coreflexivity in Hptr; inversion Hptr; clear Hptr; subst.
        apply simrel_corefl_loadbytes; eauto.
      - intros w m1 m2 Hm [b1 ofs1] [b2 ofs2] Hptr bytes1 bytes2 Hbytes.
        unfold uncurry.
        pose proof (match_ptr_block _ _ _ _ _ Hptr) as Hblock.
        apply coreflexivity in Hptr; inversion Hptr; clear Hptr; subst.
        apply simrel_corefl_storebytes; eauto.
      - intros w m1 m2 Hm [b1 ofs1] [b2 ofs2] Hptr k pe.
        unfold uncurry.
        pose proof (match_ptr_block _ _ _ _ _ Hptr) as Hblock.
        apply coreflexivity in Hptr; inversion Hptr; clear Hptr; subst.
        apply (simrel_corefl_perm w); eauto.
      - intros w m1 m2 Hm b1 b2 Hb.
        pose proof Hb as Hblock.
        apply coreflexivity in Hb; subst.
        apply (simrel_corefl_valid_block w); eauto.
      - apply simrel_corefl_different_pointers_inject.
      - intros w m1 m2 b1 ofs1 b2 ofs2 Hm H1 Hptr.
        apply coreflexivity in Hptr; inversion Hptr; clear Hptr; subst.
        erewrite simrel_corefl_weak_valid_pointer in H1 by eauto.
        assumption.
      - apply simrel_corefl_weak_valid_pointer_address_inject_weak.
      - apply simrel_corefl_address_inject.
      - apply simrel_corefl_aligned_area_inject.
      - apply simrel_corefl_disjoint_or_equal_inject.
    Qed.
  End COREFL_MEMINJ.
End WITHMEM.
