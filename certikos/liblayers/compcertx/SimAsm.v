Require Import LogicalRelations.
Require Import CompcertStructures.
Require Import SimulationRelation.
Require Import SimValues.
Require Import SimEvents.
Require Import compcert.common.Globalenvs.
Require Import compcert.x86.Asm.
Require Import AsmX.
Require Export SimAsmRegset.
Local Opaque mwd_ops.

Section ASM_REL.
  Context `{Hmem: BaseMemoryModel}.
  Context {D1 D2} (R: simrel D1 D2).

  Section WITHGE.
    Context {F V: Type} (Rf: block -> relation F) (p: simrel_world R).

    Global Instance symbol_offset_match:
      Monotonic
        (@Genv.symbol_address F V)
        (genv_le Rf ++> - ==> - ==> match_val_of_type R p Tptr).
    Proof.
      unfold Genv.symbol_address.
      pose proof (genv_find_symbol_match (F:=F) (V:=V) (Rf:=Rf) p).
      Set Printing Coercions.
      repeat red. intros.
      repeat rstep.
      unfold Tptr.
      destruct Archi.ptr64 eqn:ARCHI; constructor; auto;
      eapply match_block_sameofs_ptrbits; eauto.
    Qed.

    Global Instance symbol_address_params: Params (@Genv.symbol_address) 3.
  End WITHGE.

  Global Instance eval_addrmode32_match p:
    Monotonic
      (@eval_addrmode32)
      (forallr -, forallr -, rforall Rf, genv_le Rf ++>
       - ==> wt_regset_match R p ++> match_val_of_type R p Tint).
  Proof.
    red. solve_monotonic.
    unfold eval_addrmode32. solve_monotonic. 
  Qed.

  Global Instance eval_addrmode64_match p:
    Monotonic
      (@eval_addrmode64)
      (forallr -, forallr -, rforall Rf, genv_le Rf ++>
       - ==> wt_regset_match R p ++> match_val_of_type R p Tlong).
  Proof.
    red. solve_monotonic.
    unfold eval_addrmode64. solve_monotonic. 
  Qed.

  Global Instance eval_addrmode_match p:
    Monotonic
      (@eval_addrmode)
      (forallr -, forallr -, rforall Rf, genv_le Rf ++>
       - ==> wt_regset_match R p ++> match_val_of_type R p Tptr).
  Proof.
    unfold eval_addrmode.
    unfold Tptr. destruct Archi.ptr64 eqn:ARCHI.
    apply eval_addrmode64_match.
    apply eval_addrmode32_match.
  Qed.

  Global Instance match_val_type_of_preg (R: simrel D1 D2) p v:
    Related (match_val R p) (match_val_of_type R p (typ_of_preg v)) subrel.
  Proof.
    intros.
    rstep. destruct v; rauto.
  Qed.

  Lemma match_val_of_bool p r b:
    simrel_undef_matches_values (simrel_ops R) ->
    match_val_of_type R p (typ_of_preg r) Vundef (Val.of_bool b).
  Proof.
    intros; eapply match_val_type_of_preg. destruct b; constructor; auto.        
  Qed.

  Global Instance compare_ints_match p:
    Monotonic
      compare_ints
      (match_val R p ++>
       match_val R p ++>
       wt_regset_match R p ++>
       match_mem R p ++>
       wt_regset_match R p).
  Proof.
    unfold compare_ints.
    intros vl1 vl2 Hvl vr1 vr2 Hvr rs1 rs2 Hrs m1 m2 Hm.
    repeat rstep.
  Qed.

  Global Instance compare_ints_match_params:
    Params (@compare_ints) 5.

  Global Instance val_subloverflow_match p:
    Monotonic
      (@Val.subl_overflow)
      (match_val R p ++> match_val R p ++> match_val_of_type R p Tint).
  Proof.
    repeat rstep.
    inv H; inv H0; simpl; constructor; auto.
  Qed.

  Global Instance val_negativel_match p:
    Monotonic (@Val.negativel) (match_val R p ++> match_val_of_type R p Tint).
  Proof.
    repeat rstep.
    inv H; simpl; constructor; auto.
  Qed.

  Definition no_ptr v v' :=
    match v, v' with
      Some (Vptr _ _), _ | _, Some (Vptr _ _) => False
    | _, _ => True
    end.

  Global Instance val_maketotal_match p t:
    Monotonic
      (@Val.maketotal)
      ((simrel_option_le R (match_val_of_type R p t) /\ no_ptr) ++>
       match_val R p).
  Proof.
    intros. red. red. intros. destruct H. destruct H; auto. rauto.
    rauto.
    destruct y; try constructor. simpl. destruct v; try rauto.
    red in H0. contradiction.    
  Qed.

  Global Instance noptr_cmplu:
    Monotonic (@Val.cmplu) (⊤ ++> ⊤ ++> ⊤ ++> ⊤ ++> no_ptr). 
  Proof.
    unfold Val.cmplu.
    unfold Val.of_bool.
    repeat rstep. unfold no_ptr. simpl.
    destruct (Val.cmplu_bool _ _ _ _) as [b|];
    destruct (Val.cmplu_bool _ _ _ _) as [b1|].
    destruct b, b1; simpl; auto.
    destruct b; simpl; auto.
    destruct b1; simpl; auto.
    simpl; auto.
  Qed.

  Global Instance val_cmplu_params: Params (@Val.cmplu) 4.

  Global Instance compare_longs_match p:
    Monotonic
      compare_longs
      (match_val R p ++>
       match_val R p ++>
       wt_regset_match R p ++>
       match_mem R p ++>
       wt_regset_match R p).
  Proof.
    unfold compare_longs.
    rauto.
  Qed.

  Global Instance compare_longs_match_params:
    Params (@compare_longs) 5.

  Global Instance compare_floats_match p:
    Monotonic
      (@compare_floats)
      (match_val R p ++>
       match_val R p ++>
       wt_regset_match R p ++>
       wt_regset_match R p).
  Proof.
    unfold compare_floats.
    solve_monotonic.
    - simpl.
      solve_monotonic;
      destruct (negb _); rauto.
    - simpl.
      destruct y0;
      solve_monotonic;
      destruct (negb _); rauto.
  Qed.

  Global Instance compare_floats32_match p:
    Monotonic
      (@compare_floats32)
      (match_val R p ++>
       match_val R p ++>
       wt_regset_match R p ++>
       wt_regset_match R p).
  Proof.
    unfold compare_floats32.
    solve_monotonic.
    - simpl.
      solve_monotonic;
      destruct (negb _); rauto.
    - simpl.
      destruct y0;
      solve_monotonic;
      destruct (negb _); rauto.
  Qed.

  Global Instance eval_testcond_match p:
    Monotonic
      (@eval_testcond)
      (- ==> regset_match R p ++> simrel_option_le R eq).
  Proof.
    unfold eval_testcond.
    repeat rstep.
  Qed.

  (** For [outcome_match] and [wt_outcome_match], if the left-hand
    side execution gets stuck, the right-hand side can adopt any
    behavior whatsoever. If this turns out to be too weak we can adopt
    an approach similar to [simrel_option_le].
    (In fact, we do need LowerBound Stuck, due to goto_label. --Tahina) *)

  Inductive outcome_match p: rel (outcome (mem := mwd D1)) (outcome (mem := mwd D2)) :=
    | Next_match:
        Monotonic Next (regset_match R p ++> match_mem R p ++> outcome_match p)
    | Stuck_lower_bound:
        LowerBound (outcome_match p) Stuck.

  Global Existing Instance Next_match.
  Global Existing Instance Stuck_lower_bound.

  Global Instance Stuck_match p:
    Monotonic Stuck (outcome_match p).
  Proof.
    red.
    apply lower_bound.
  Qed.

  Inductive wt_outcome_match p: rel (outcome (mem := mwd D1)) (outcome (mem := mwd D2)):=
    | Next_match_wt:
        Monotonic
          Next
          (wt_regset_match R p ++> match_mem R p ++> wt_outcome_match p)
    | Stuck_lower_bound_wt:
        LowerBound
          (wt_outcome_match p)
          Stuck.

  Global Existing Instance Next_match_wt.
  Global Existing Instance Stuck_lower_bound_wt.

  Global Instance Stuck_match_wt p:
    Monotonic Stuck (wt_outcome_match p).
  Proof.
    red.
    apply lower_bound.
  Qed.

  Global Instance Next_params: Params (@Next) 2.

  Global Instance nextinstr_match p:
    Monotonic (@nextinstr) (wt_regset_match R p ++> wt_regset_match R p).
  Proof.
    unfold nextinstr.
    solve_monotonic.
  Qed.

  Global Instance nextinstr_nf_match p:
    Monotonic (@nextinstr_nf) (wt_regset_match R p ++> wt_regset_match R p).
  Proof.
    unfold nextinstr_nf.
    solve_monotonic.
  Qed.
  
  Global Instance goto_label_match `{FindLabels} p:
    Monotonic
      (@goto_label _ _ _ _ _ _ _)
      (forallr -, forallr -, rforall Rf, genv_le Rf ==>
       - ==> - ==> wt_regset_match R p ++> match_mem R p ++> wt_outcome_match p).
  Proof.
    unfold goto_label. 
    solve_monotonic.
    destruct (Genv.find_funct_ptr x b1) eqn:?. 2: rauto.
    assert (block_is_global b1).
    transport Heqo.
    eapply find_funct_ptr_block_is_global; eauto.
    generalize H3; intro.
    eapply match_global_ptrbits_eq in H3; eauto. inv H3.
    transport Heqo. rewrite H3.
    constructor; auto.
    apply regset_set_rel_wt; auto.
    apply match_val_any64_val.
    eapply match_val_ptr_def.
    apply match_global_ptrbits. auto.
  Qed.

  Global Instance goto_label_match_params:
    Params (@goto_label) 5.

  (** Properties of default mem accessors *)

  Section DEFAULT_ACC.

    Local Instance exec_load_default_match p:
      Monotonic
        (@exec_load _ _)
        (forallr -, forallr -, rforall Rf, genv_le Rf ++>
         - ==> match_mem R p ++> - ==> wt_regset_match R p ++> - ==>
         incr p (wt_outcome_match p)).
    Proof.
      unfold exec_load.
      intros F V Rf ge1 ge2 Hge chunk m1 m2 Hm am rs1 rs2 Hrs r.
      destruct (Mem.loadv chunk m1 (eval_addrmode ge1 am rs1)) eqn:LOAD1.
      + transport LOAD1.
        rewrite H.
        solve_monotonic.
      + exists p; split; [ reflexivity | constructor ].
    Qed.

    Local Instance: Params (@exec_load) 7.
    
    Local Instance exec_store_default_match p:
      Monotonic
        (@exec_store _ _)
        (forallr -, forallr -, rforall Rf, genv_le Rf ++>
         - ==> match_mem R p ++> - ==> wt_regset_match R p ++> - ==> - ==>
         incr p (wt_outcome_match p)).
    Proof.
      unfold exec_store.
      intros F V Rf ge1 ge2 Hge chunk m1 m2 Hm am rs1 rs2 Hrs r erase.
      rstep.
      - rauto.
      - split_hyp H1.
        repeat rstep.
        exists p'; split; rauto.
    Qed.

    Local Instance: Params (@exec_store) 8.

  End DEFAULT_ACC.

  
  Global Instance val_floatofsingle_match p:
    Monotonic
      (@Val.floatofsingle)
      (match_val (simrel_ops R) p ++> match_val_of_type R p Tfloat).
  Proof.
    intros. rstep. rstep.
    inv H; simpl; rauto.
  Qed.

  Global Instance val_intofsingle_match p:
    Monotonic
      (@Val.intofsingle)
      (match_val R p ++> simrel_option_le R (match_val_of_type R p Tint)).
  Proof.
    unfold Val.intofsingle.
    solve_monotonic.
  Qed.

  Global Instance val_singleofint_match p:
    Monotonic
      (@Val.singleofint)
      (match_val R p ++> simrel_option_le R (match_val_of_type R p Tsingle)).
  Proof.
    unfold Val.singleofint.
    solve_monotonic.
  Qed.

  Global Instance val_longofsingle_match p:
    Monotonic
      (@Val.longofsingle)
      (match_val R p ++> simrel_option_le R (match_val_of_type R p Tlong)).
  Proof.
    unfold Val.longofsingle. solve_monotonic.
  Qed.

  Global Instance val_maketotal_singleoflong_match p:
    Monotonic
      (@Val.singleoflong)
      (match_val R p ++> simrel_option_le R (match_val_of_type R p Tsingle)).
  Proof.
    unfold Val.singleoflong; solve_monotonic.
  Qed.

  Global Instance val_longoffloat_match p:
    Monotonic
      (@Val.longoffloat)
      (match_val R p ++> simrel_option_le R (match_val_of_type R p Tlong)).
  Proof.
    unfold Val.longoffloat; solve_monotonic.
  Qed.

  Global Instance val_floatoflong_match p:
    Monotonic
      (@Val.floatoflong)
      (match_val R p ++> simrel_option_le R (match_val_of_type R p Tfloat)).
  Proof.
    unfold Val.floatoflong; solve_monotonic.
  Qed.

  Global Instance val_rorl_match p:
    Monotonic
      (@Val.rorl)
      (match_val (simrel_ops R) p ++> match_val (simrel_ops R) p ++>
       match_val_of_type R p Tlong).
  Proof.
    repeat rstep. inv H; inv H0; simpl; try constructor; auto.
  Qed.

  Global Instance val_addfs_match p:
    Monotonic
      (@Val.addfs)
      (match_val R p ++> match_val R p ++> match_val_of_type R p Tsingle).
  Proof.
    repeat rstep. inv H; inv H0; simpl; try constructor; auto.
  Qed.

  Global Instance val_subfs_match p:
    Monotonic
      (@Val.subfs)
      (match_val R p ++> match_val R p ++> match_val_of_type R p Tsingle).
  Proof.
    repeat rstep. inv H; inv H0; simpl; try constructor; auto.
  Qed.
  
  Global Instance val_mulfs_match p:
    Monotonic
      (@Val.mulfs)
      (match_val R p ++> match_val R p ++> match_val_of_type R p Tsingle).
  Proof.
    repeat rstep. inv H; inv H0; simpl; try constructor; auto.
  Qed.

  Global Instance val_divfs_match p:
    Monotonic
      (@Val.divfs)
      (match_val R p ++> match_val R p ++> match_val_of_type R p Tsingle).
  Proof.
    repeat rstep. inv H; inv H0; simpl; try constructor; auto.
  Qed.

  Global Instance val_negfs_match p:
    Monotonic
      (@Val.negfs)
      (match_val R p ++> match_val_of_type R p Tsingle).
  Proof.
    repeat rstep. inv H; simpl; try constructor; auto.
  Qed.

  Global Instance val_absfs_match p:
    Monotonic
      (@Val.absfs)
      (match_val R p ++> match_val_of_type R p Tsingle).
  Proof.
    repeat rstep. inv H; simpl; try constructor; auto.
  Qed.

  Ltac inv_option_map :=
    match goal with
      |- context[match option_map _ ?x with _ => _ end] => destruct x; simpl; auto
    end.

  Global Instance noptr_floatofint x y:
    Related (Val.floatofint x) (Val.floatofint y) no_ptr.
  Proof.
    unfold Related. 
    unfold no_ptr ; destruct x,y; simpl; auto.
  Qed.

  Global Instance noptr_floatoflong x y:
    Related (Val.floatoflong x) (Val.floatoflong y) no_ptr.
  Proof.
    unfold Related. 
    unfold no_ptr ; destruct x,y; simpl; auto.
  Qed.

  Global Instance noptr_intoffloat x y:
    Related (Val.intoffloat x) (Val.intoffloat y) no_ptr.
  Proof.
    unfold Related. 
    unfold no_ptr ; destruct x,y; simpl; auto; repeat inv_option_map.
  Qed.

  Global Instance noptr_longoffloat x y:
    Related (Val.longoffloat x) (Val.longoffloat y) no_ptr.
  Proof.
    unfold Related. 
    unfold no_ptr ; destruct x,y; simpl; auto; repeat inv_option_map.
  Qed.

  Global Instance noptr_singleofint x y:
    Related (Val.singleofint x) (Val.singleofint y) no_ptr.
  Proof.
    unfold Related. 
    unfold no_ptr ; destruct x,y; simpl; auto.
  Qed.

  Global Instance noptr_singleoflong x y:
    Related (Val.singleoflong x) (Val.singleoflong y) no_ptr.
  Proof.
    unfold Related. 
    unfold no_ptr ; destruct x,y; simpl; auto.
  Qed.

  Global Instance noptr_intofsingle x y:
    Related (Val.intofsingle x) (Val.intofsingle y) no_ptr.
  Proof.
    unfold Related. 
    unfold no_ptr ; destruct x,y; simpl; auto; repeat inv_option_map.
  Qed.

  Global Instance noptr_longofsingle x y:
    Related (Val.longofsingle x) (Val.longofsingle y) no_ptr.
  Proof.
    unfold Related. 
    unfold no_ptr ; destruct x,y; simpl; auto; repeat inv_option_map.
  Qed.

  (*
Lemma rstep_under_rel_incr {W A B C D} Rx R' acc (p:W) (m:A) (n:B) (m':C) (n':D):
  Reflexive acc ->
  (forall p, exists P, RStep P (R' p m' n') /\ P = Rx p m n)%type ->
  RStep (rel_incr acc Rx p m n) (rel_incr acc R' p m' n').
Proof.
  clear.
  intros.
Admitted.

Hint Extern 1 (RStep _ (rel_incr _ _ _)) =>
  eapply rstep_under_rel_incr; [ | split; [typeclasses eauto | reflexivity]] : typeclass_instances.
*)

Instance match_block_sameofs_ptrbits_rstep w b1 b2 ofs:
  RStep
    (match_block_sameofs R w b1 b2)
    (match_ptrbits R w (b1, ofs) (b2, ofs)) | 100.
Proof.
  intro.
  apply match_block_sameofs_ptrbits; eauto.
Qed.

Instance match_val_erase_type_acc_rstep w w' ty:
  RStep
    (w ≤ w')
    (subrel
       (match_val_of_type R w ty)
       (match_val R w')).
Proof.
  intro.
  transitivity (match_val R w); rauto.
Qed.

Lemma rel_inter_rintro {A B} (R1 R2: rel A B) m n:
  RIntro (R1 m n /\ R2 m n) (R1 /\ R2) m n.
Proof.
  clear.
  firstorder.
Qed.

Hint Extern 1 (RIntro _ (_ /\ _) _ _) =>
  eapply rel_inter_rintro : typeclass_instances.

  Global Instance exec_instr_match `{Hfl: FindLabels} p:
    Monotonic
      (@exec_instr _ _ _ _ _ _ _)
      (forallr _ : (forallr -, forallr -, rforall Rf, genv_le Rf ++> - ==>
                    match_mem R p ++> - ==> wt_regset_match R p ++> - ==>
                    incr p (wt_outcome_match p)),
       forallr _ : (forallr -, forallr -, rforall Rf, genv_le Rf ++> - ==>
                    match_mem R p ++> - ==> wt_regset_match R p ++> - ==> - ==>
                    incr p (wt_outcome_match p)),
       ⊤ ==> forallr -, forallr -, rforall Rf, genv_le Rf ++>
       - ==> - ==> wt_regset_match R p ++> match_mem R p ++>
       incr p (wt_outcome_match p)).
  Proof.
    intros el1 el2 Hel es1 es2 Hes MA1 MA2 _ F V Rf ge1 ge2 Hge.
    intros f instr rs1 rs2 Hrs m1 m2 Hm.
    Local Opaque Val.offset_ptr. (* to avoid unfolding storev for Pfreeframe. *)

    Time destruct instr; try (simpl exec_instr; rauto).

    - simpl.
      repeat rstep.
      destruct y; repeat rstep.
      destruct b; repeat rstep.
      + reexists; repeat rstep.
        eapply match_val_type_of_preg.
        eapply match_val_weaken_to_undef; eauto.
        repeat rstep.
      + reexists; repeat rstep.
        intros r.
        destruct (preg_eq r (IR rd)).
        * subst.
          rewrite Pregmap.gss.
          eapply match_val_type_of_preg.
          eapply match_val_weaken_to_undef; eauto.
          rauto.
        * rewrite Pregmap.gso; eauto.
    - simpl.
      repeat rstep.
      reexists; repeat rstep.
      eapply goto_label_match; eauto.
    - simpl.
      repeat rstep.
      reexists; repeat rstep.
      eapply goto_label_match; eauto.
    - simpl.
      repeat rstep.
      reexists; repeat rstep.
      eapply goto_label_match; eauto.
    - simpl.
      repeat rstep.
      reexists; repeat rstep.
      eapply goto_label_match; eauto.
      rauto.
    - simpl.
      repeat rstep.
      assert (w' ≤ w') by rauto.
      repeat rstep.
      split_hyp H5.
      repeat rstep.
      split_hyp H6.
      exists w'''; split; repeat rstep.
      eapply match_val_type_of_preg.
      rauto.
    - simpl.
      repeat rstep.
      change (Mem.free m1 b1 _ _) with (Mem.freev m1 (Vptr b1 ofs1) sz).
      change (Mem.free m2 b2 _ _) with (Mem.freev m2 (Vptr b2 ofs2) sz).
      repeat rstep.
      split_hyp H4.
      exists p'; split; repeat rstep.
      + eapply match_val_type_of_preg.
        rauto.
      + eapply match_val_type_of_preg.
        rauto.
  Qed.

  Global Instance wt_extcall_arg_match p:
    Monotonic
      extcall_arg
      (wt_regset_match R p ++> match_mem R p ++> forallr - @ l,
       set_rel (match_val_of_type R p (Locations.Loc.type l))).
  Proof.
    intros rs1 rs2 Hrs m1 m2 Hm l a EA.
    inv EA.
    + eexists; split. econstructor. simpl. generalize (Hrs (preg_of r)).
      destruct r; simpl; auto. 
    + simpl.
      transport H0.
      eexists; split. econstructor; eauto.
      apply match_val_of_type_intro; auto.
      destruct (rs2 RSP); try discriminate.
      Opaque Z.mul.
      Transparent Val.offset_ptr. simpl Val.offset_ptr in H.
      unfold Mem.loadv in H.
      replace ty with (type_of_chunk (chunk_of_type ty));
        eauto using (Mem.load_type (mem := mwd D2)).
      destruct ty; auto.
  Qed.

  Hint Extern 1 (Transport _ _ _ _ _) =>
    set_rel_transport @extcall_arg : typeclass_instances.

  Global Instance wt_extcall_arg_pair_match p:
    Monotonic
      extcall_arg_pair
      (wt_regset_match R p ++> match_mem R p ++> forallr - @ l,
       set_rel (match_val_of_type R p (typ_rpair Loc.type l))).
  Proof.
    intros rs1 rs2 Hrs m1 m2 Hm l a EA.
    inv EA.
    + eapply wt_extcall_arg_match in H; eauto. split_hyp H.
      eexists; split. econstructor. eauto. simpl. auto. 
    + simpl.
      eapply wt_extcall_arg_match in H; eauto. split_hyp H.
      eapply wt_extcall_arg_match in H0; eauto. split_hyp H0.
      eexists; split. econstructor; eauto.
      rauto.
  Qed.

  Hint Extern 1 (Transport _ _ _ _ _) =>
    set_rel_transport @extcall_arg_pair : typeclass_instances.

  Global Instance wt_extcall_arguments_match p:
    Monotonic extcall_arguments
      (wt_regset_match R p ++> match_mem R p ++> forallr - @ sg,
       set_rel (list_indexed_rel (match_val_of_type R p) (List.map (typ_rpair Loc.type) (Conventions1.loc_arguments sg)))).
  Proof.
    unfold extcall_arguments.
    intros rs1 rs2 Hrs m1 m2 Hm sg v1s Hv1s.
    induction Hv1s.
    - exists nil.
      split; repeat constructor.
    - split_hyp IHHv1s.
      eapply wt_extcall_arg_pair_match in H; eauto. split_hyp H.
      exists (x0 :: x).
      split; constructor; auto.
  Qed.

  Hint Extern 1 (Transport _ _ _ _ _) =>
    set_rel_transport @extcall_arguments : typeclass_instances.

  Inductive state_match p: rel (state (mem := mwd D1)) (state (mem := mwd D2)) :=
    | State_match:
        Monotonic
          State
          (wt_regset_match R p ++> match_mem R p ++> state_match p).

  Global Existing Instance State_match.

  Global Instance final_state_match p:
    Monotonic Asm.final_state (state_match p ++> - ==> impl).
  Proof.
    intros s1 s2 Hs r H1.
    destruct H1 as [rs1 m1 r Hpc Heax].
    inversion Hs as [rs1x rs2 Hrs m1x m2 Hm]; clear Hs; subst.
    constructor.
    - specialize (Hrs PC).
      rewrite Hpc in Hrs.
      inversion Hrs.
      reflexivity.
    - specialize (Hrs RAX).
      rewrite Heax in Hrs.
      inversion Hrs.
      reflexivity.
  Qed.

  Require Import Events.
  Require Import CompCertBuiltins.

  Context `{ec1_ops: !ExternalCallsOpsX (mwd D1)}.
  Context `{ec2_ops: !ExternalCallsOpsX (mwd D2)}.

  Context `{cc1_ops: !EnableBuiltins (mwd D1)}.
  Context `{cc2_ops: !EnableBuiltins (mwd D2)}.

  Context {exec_load1 exec_store1}
          `{mem_acc1: @MemAccessors (mwd D1) _ exec_load1 exec_store1}
          {exec_load2 exec_store2}
          `{mem_acc2: @MemAccessors (mwd D2) _ exec_load2 exec_store2}.

  Definition funsig (f: Asm.fundef): signature :=
    match f with
      | Internal f => fn_sig f
      | External ef => ef_sig ef
    end.

  Class AsmFunrel
        (Rf: block -> rel fundef fundef) ge1 ge2 :=
    {
      asm_funrel_builtin_disabled:
        cc_enable_external_as_builtin (mem := mwd D1) = false;
      asm_funrel_callstate_sim p t:
        genv_le Rf ge1 ge2 ->
        forall rs1 m1 rs2 m2 s1',
          state_match p (State rs1 m1) (State rs2 m2) ->
          step ge1 (State rs1 m1) t s1' ->
          exists s2',
            (Smallstep.plus step ge2 (State rs2 m2) t s2' /\
             exists p', p ≤ p' /\ state_match p' s1' s2')%type
    }.

  Import Smallstep.

  Definition genv_sim (ge1 ge2: genv) :=
    (rforall p,
       state_match p ++>
       - ==>
       set_rel (incr p (state_match p)))%rel
    (Asm.step ge1)
    (Smallstep.plus Asm.step ge2).
  
  Lemma genv_sim_plus:
    (rforall p,
       genv_sim ++>
       state_match p ++>
       - ==>
       set_rel (incr p (state_match p)))%rel
    (plus Asm.step)
    (plus Asm.step).
  Proof.
    intros p ge1 ge2 Hge s1 s2 Hs t s1' Hs1'.
    revert p s2 Hs.
    pattern s1, t, s1'.
    eapply plus_ind2; try eassumption; clear s1 t s1' Hs1'.
    - intros s1 t s1' Hstep p s2 Hs.
      eapply (Hge p); eauto.
    - intros s1 t s1' u s1'' tu H1 H1' IH Htu.
      intros p1 s2 Hs.
      eapply Hge in H1; eauto.
      destruct H1 as (s2' & H2 & p' & Hincr & Hs').
      edestruct IH as (s2'' & H2' & p'' & Hincr' & Hs''); eauto.
      exists s2''.
      split.
      + eapply plus_trans; eauto.
      + exists p''.
        split; auto.
        etransitivity; eauto.
  Qed.

  Lemma asm_sim `{HRf: AsmFunrel}:
    genv_le Rf ge1 ge2 ->
    genv_sim ge1 ge2.
  Proof.
    intros Hge.
    intros p s1 s2 Hs t s1' H1.
    deconstruct H1 ltac:(fun x => pose (c := x); inv Hs).
    transport e0.
    eapply asm_funrel_callstate_sim; eauto; econstructor; eauto.
    transport e0.
    eapply asm_funrel_callstate_sim; eauto; econstructor; eauto.
    transport e0.
    eapply asm_funrel_callstate_sim; eauto; econstructor; eauto.
  Qed.

End ASM_REL.

Hint Extern 1 (Transport _ _ _ _ _) =>
  set_rel_transport @extcall_arg : typeclass_instances.

Hint Extern 1 (Transport _ _ _ _ _) =>
  set_rel_transport @extcall_arguments : typeclass_instances.


(** * Functoriality of [outcome_match] et al. *)

Section IDREFL.
  Context `{Hmem: BaseMemoryModel}.
  Context {D: layerdata}.

  Global Instance outcome_match_refl p:
    Reflexive (outcome_match (simrel_id (D:=D)) p).
  Proof.
    intros [rs m|]; constructor.
    - rewrite regset_match_id.
      reflexivity.
    - simpl.
      reflexivity.
  Qed.
End IDREFL.

Section COMPOSE.
  Context `{Hmem: BaseMemoryModel}.
  Context {D1 D2 D3} (R12: simrel D1 D2) (R23: simrel D2 D3).

  Lemma outcome_match_compose p q:
    outcome_match (simrel_compose R12 R23) (p, q) =
    rel_compose (outcome_match R12 p) (outcome_match R23 q).
  Proof.
    apply functional_extensionality; intro o1.
    apply functional_extensionality; intro o3.
    apply prop_ext; split.
    - intros Ho.
      destruct Ho as [rs1 rs3 Hrs m1 m3 Hm | ].
      + simpl in Hm.
        destruct Hm as (m2 & Hm12 & Hm23).
        rewrite regset_match_compose in Hrs.
        destruct Hrs as (rs2 & Hrs12 & Hrs23).
        exists (Next rs2 m2); split; solve_monotonic.
      + exists Stuck; split; apply lower_bound.
    - intros (o2 & Ho12 & Ho23).
      destruct Ho12 as [rs1 rs2 Hrs12 m1 m2 Hm12 | ].
      + inversion Ho23; clear Ho23; subst.
        monotonicity || eapply Next_match. (** XXX monotonicity should work *)
        * rewrite regset_match_compose.
          exists rs2; eauto.
        * simpl.
          exists m2; eauto.
      + apply lower_bound.
  Qed.

  Lemma wt_outcome_match_compose p q:
    wt_outcome_match (simrel_compose R12 R23) (p, q) =
    rel_compose (wt_outcome_match R12 p) (wt_outcome_match R23 q).
  Proof.
    apply functional_extensionality; intro o1.
    apply functional_extensionality; intro o3.
    apply prop_ext; split.
    - intros Ho.
      destruct Ho as [rs1 rs3 Hrs m1 m3 Hm | ].
      + simpl in Hm.
        destruct Hm as (m2 & Hm12 & Hm23).
        rewrite wt_regset_match_compose in Hrs.
        destruct Hrs as (rs2 & Hrs12 & Hrs23).
        exists (Next rs2 m2); split; solve_monotonic; constructor; auto.
      + exists Stuck; split; apply lower_bound.
    - intros (o2 & Ho12 & Ho23).
      destruct Ho12 as [rs1 rs2 Hrs12 m1 m2 Hm12 | ].
      + inversion Ho23; clear Ho23; subst.
        monotonicity || eapply Next_match_wt. (** XXX monotonicity should work *)
        * rewrite wt_regset_match_compose.
          exists rs2; eauto.
        * simpl.
          exists m2; eauto.
      + apply lower_bound.
  Qed.
End COMPOSE.
