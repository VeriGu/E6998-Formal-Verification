(** ** Calling convention: convert C primitives to Asm primitives **)

Require Import compcert.lib.Coqlib.
Require Import compcert.common.Memtype.
Require Import compcert.common.AST.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import liblayers.lib.Decision.
Require Import coqrel.LogicalRelations.
Require Import liblayers.logic.LayerData.
Require Import liblayers.logic.Primitives.
Require Export liblayers.compcertx.CompcertStructures.
Require Import liblayers.compcertx.ErrorMonad.
Require Import AbstractData.
Require Import compcert.x86.Asm.
Require compcertx.x86.AsmX.
Require compcert.backend.EraseArgs.
Require Import SimulationRelation.
Require Import SimAsmRegset.
Require SimAsm.

Require CPrimitives.

Require compcert.cfrontend.Ctypes.
Require SimClight.

Require AsmPrimitives.

Require PTreeLayerMap.
Require MakeProgramSpec.

(* Registers destroyed at call (backported from compat/CompatCallConv.v) *)

Definition callconv_destroyed_regs :=
  map preg_of Conventions1.destroyed_at_call ++
      CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil.

Section ASMPRIMITIVE.
  Context `{Hmem: BaseMemoryModel}.

  Local Opaque callconv_destroyed_regs.

  Lemma has_type_any64 v:
    Val.has_type v Tany64.
  Proof.
    destruct v; simpl; auto.
  Qed.
  
  Lemma pair_wt_ok p v:
    AsmX.pair_wt p v.
  Proof.
    destruct p; simpl.
    eapply Val.has_subtype. 2: apply has_type_any64. destruct r; reflexivity.
    split.
    eapply Val.has_subtype. 2: apply has_type_any64. destruct rhi; reflexivity.
    eapply Val.has_subtype. 2: apply has_type_any64. destruct rlo; reflexivity.
  Qed.
  

  
  Program
  Definition c_to_asm_primitive (D: layerdata) (i: ident) (p: CPrimitives.cprimitive D): AsmPrimitives.asmprimitive D :=
    {|
      AsmPrimitives.asmprimitive_step rsm rsm' :=
        let '(rs, m_asm) := rsm in
        let '(rs', m') := rsm' in
        rs SP <> Vundef /\
        rs RA <> Vundef /\
        ( (* PC must point to the primitive entrypoint *)
          exists b,
            (* TODO: find a way to express symbol to memory block
               without resorting to a reference global environment
             *)
            find_symbol i = Some b /\
            rs PC = Vptr b Ptrofs.zero
        ) /\
        exists sg vargs_asm,
          extcall_arguments rs m_asm sg vargs_asm /\
          let vargs_c := (* decode_longs (sig_args sg) *) vargs_asm in
          (          
            (* protect the argument locations: the C primitive
               must have a valid semantics, regardless of the values
               or permissions of those memory locations. *)
            (* NOTE: the C signature might be different with than
               without the argument locations.
               Required in AsmXAsmGenproof. *)
            exists csg,
              In csg (CPrimitives.cprimitive_csig D p) /\
              sg = csig_sig csg /\
            exists m_c,
              EraseArgs.free_extcall_args (rs SP) m_asm (regs_of_rpairs (Conventions1.loc_arguments sg)) = Some m_c /\
              exists res_c,
                CPrimitives.cprimitive_step D p csg (vargs_c, m_c) res_c
          ) /\
          exists csg,
            In csg (CPrimitives.cprimitive_csig D p) /\
            sg = csig_sig csg /\
          exists v',
            CPrimitives.cprimitive_step D p csg (vargs_c, m_asm) (v', m') /\
            let rs1 := undef_regs callconv_destroyed_regs rs in
            let rs2 := set_pair (loc_external_result sg) (* (encode_long (sig_res sg) v') *) v' rs1 in
            let rs3 := rs2 # PC <- (rs RA) in
            let rs4 := rs3 # RA <- Vundef in
            rs' = rs4
    |}.
  Next Obligation.
    apply AsmX.undef_reg_wt.
    apply AsmX.set_reg_wt.
    {
      replace (AsmX.typ_of_preg PC) with (AsmX.typ_of_preg RA) by reflexivity.
      auto.
    }
    apply AsmX.set_pair_wt.
    apply AsmX.undef_regs_wt; auto.
    apply pair_wt_ok.
  Qed.

  Global Instance c_to_asm_primitive_monotonic:
    Monotonic
      c_to_asm_primitive
      (forallr R @ D1 D2,
       - ==>
       CPrimitives.cprimitive_sim D1 D2 R ++>
       AsmPrimitives.asmprim_sim D1 D2 R).
  Proof.
    intros D1 D2 R i σ1 σ2 Hσ.
    destruct Hσ as (Hσ_step & Hσ_sig).
    red in Hσ_sig.
    constructor.
    intros p s1 s2 Hs s'1 Hstep1.
    destruct s1 as [rs1 m1].
    destruct s'1 as [rs'1 m'1].
    destruct s2 as [rs2 m2].
    inversion Hs as (Hrs & Hm).
    simpl in Hrs, Hm.
    destruct Hstep1 as (SP_NOT_VUNDEF1 & RA_NOT_VUNDEF1 & SYMB1 & ? & vargs_asm1 & ARGS_ASM1 & LOC1 & csg & Hcsg & ? & v'1 & cstep1 & EQ1).
    subst.
    assert (rs2 RSP <> Vundef) as SP_NOT_VUNDEF2.
    {
      specialize (Hrs RSP).
      intro ABSURD. rewrite ABSURD in Hrs.
      inversion Hrs.
      congruence.
    }
    clear SP_NOT_VUNDEF1.
    assert (rs2 RA <> Vundef) as RA_NOT_VUNDEF2.
    {
      specialize (Hrs RA).
      intro ABSURD. rewrite ABSURD in Hrs.
      inversion Hrs.
      congruence.
    }
    clear RA_NOT_VUNDEF1.
    assert (exists b, find_symbol i = Some b /\ rs2 PC = Vptr b Ptrofs.zero) as SYMB2.
    {
      destruct SYMB1 as (b & Hb & HPC1).
      specialize (Hrs PC).
      rewrite HPC1 in Hrs.
      apply SimValues.match_val_erase_type in Hrs.
      inversion Hrs as [ | | | | ? ? b2 ofs2 BITS | | | | | | ] ; subst.
      exploit (CompcertStructures.find_symbol_block_is_global); eauto.
      intro GLOBAL.
      exploit (match_global_ptrbits p b Ptrofs.zero); eauto.
      intro BITS'.
      exploit (match_ptrbits_functional p).
      + eexact BITS.
      + eexact BITS'.
      + inversion 1; subst; eauto.
    }
    clear SYMB1.
    assert (exists vargs_asm2,
               extcall_arguments rs2 m2 (csig_sig csg) vargs_asm2 /\
               (SimAsmRegset.list_indexed_rel (SimValues.match_val_of_type R p)
                         (map (typ_rpair Locations.Loc.type) (Conventions1.loc_arguments (csig_sig csg))))
                 vargs_asm1 vargs_asm2) as ARGS_ASM2.
    {
      eapply SimAsm.wt_extcall_arguments_match; eauto.
    }
    destruct ARGS_ASM2 as (vargs_asm2 & ARGS_ASM2 & Hvargs_asm).
    clear ARGS_ASM1.
    assert (
            exists csg_,
              In csg_ (CPrimitives.cprimitive_csig D2 σ2) /\
              csig_sig csg = csig_sig csg_ /\
            exists m_c : mwd D2,
              EraseArgs.free_extcall_args
                (rs2 RSP) m2
                (regs_of_rpairs (Conventions1.loc_arguments (csig_sig csg))) =
              Some m_c /\
              (exists res_c : val × mwd D2,
                  CPrimitives.cprimitive_step D2 σ2 csg_
                                              (* (decode_longs *)
                                              (*    (sig_args (csig_sig csg)) *)
                                              (*    vargs_asm2, m_c) *)
                                              (vargs_asm2, m_c)
                                              res_c))
      as LOC2.
    {
      destruct LOC1 as (csg_ & Hcsg_ & Hcsg_eq & m_c1 & Hm_c1 & res_c1 & cstep_c1).
      exists csg_.
      split; auto.
      split; auto.
      assert (
          exists p_c,
            p ≤ p_c /\
            exists m_c2,
              EraseArgs.free_extcall_args (rs2 RSP) m2
               (regs_of_rpairs (Conventions1.loc_arguments (csig_sig csg))) = Some m_c2 /\
              match_mem R p_c m_c1 m_c2)
             as Hm_c.
      {
        Require SimEraseArgs.
        specialize (Hrs RSP).
        simpl in Hrs.
        apply SimValues.match_val_erase_type in Hrs.
        generalize (SimEraseArgs.free_extcall_args_mono _ _ _ _ Hrs _ _ Hm (regs_of_rpairs (Conventions1.loc_arguments (csig_sig csg)))).
        rewrite Hm_c1.
        inversion 1; subst.
        destruct H2 as (p_c & Hp & Hfree).
        eauto.
      }
      destruct Hm_c as (p_c & Hp & m_c2 & Hm_c2 & Hm_c).
      assert (CPrimitives.cprimitive_match_init_state D1 D2 R p_c
               ((* decode_longs (sig_args (csig_sig csg)) *) vargs_asm1, m_c1)
               ((* decode_longs (sig_args (csig_sig csg)) *) vargs_asm2, m_c2))
             as Hmatch_c.
      {
        constructor; auto.
        solve_monotonic.
        eapply SimAsmRegset.list_indexed_rel_match_val_of_type_weaken in Hvargs_asm.
        rstep.
      }
      specialize (Hσ_step _ _ _ _ Hmatch_c _ cstep_c1).
      destruct Hσ_step as (? & ? & ?).
      eauto.
    }
    clear LOC1.
    assert (CPrimitives.cprimitive_match_init_state
              D1 D2 R p
              ((* decode_longs (sig_args (csig_sig csg)) *) vargs_asm1, m1)
               ((* decode_longs (sig_args (csig_sig csg)) *) vargs_asm2, m2))
             as Hmatch_c.
    {
      constructor; auto.
      simpl.
      solve_monotonic.
    }
    specialize (Hσ_step _ _ _ _ Hmatch_c _ cstep1).
    clear Hmatch_c cstep1 Hm.
    destruct Hσ_step as ([v'2 m'2] & cstep2 & p' & Hp & Hv' & Hm').
    simpl in Hv', Hm'.
    Local Opaque callconv_destroyed_regs.
    assert (SimAsmRegset.regset_match R p' rs1 rs2) as Hrs_.
    {
      intro r.
      eapply match_val_acc; eauto.
      eapply SimValues.match_val_erase_type; eauto.
    }
    pose (rs'2 :=
        ((set_pair
            (loc_external_result (csig_sig csg))
            v'2
            (* (encode_long *)
            (*    (Ctypes.opttyp_of_type *)
            (*       (csig_res csg)) v'2) *)
            (undef_regs callconv_destroyed_regs rs2)) # PC <-
         (rs2 RA)) # RA <- Vundef).
    assert (AsmPrimitives.asmprim_match_state D1 D2 R p' (rs'1, m'1) (rs'2, m'2))
           as Hs'.
    {
      subst.
      unfold rs'2; clear rs'2.
      constructor; auto.
      simpl in EQ1.
      subst.
      simpl.
      apply regset_set_rel. rstep. 
      apply regset_set_rel. rstep.
      apply set_pair_match; auto.
      apply undef_regs_match; auto.
    }
    esplit.
    split; [ | esplit; eauto ] .
    repeat (refine (conj _ _)); eauto.
    eexists; eexists; split; eauto.
    simpl. split; eauto.
    destruct LOC2 as (csg_ & IN & EQsig & (m_c & FEA & (res_c & STEP))).
    eexists; repeat (refine (conj _ _)); eauto.
    eexists; repeat (refine (conj _ _)). 2: reflexivity.
    replace csg_ with csg by admit.
    eauto.
  Admitted.

  (** Invariant *)

  Global Instance c_to_asm_primitive_preserves_invariant D σ i:
    CPrimitives.CPrimitivePreservesInvariant D σ ->
    AsmPrimitives.AsmPrimitivePreservesInvariant D (c_to_asm_primitive D i σ).
  Proof.
    intros H.
    apply AsmPrimitives.inv_asmprim.
    red.
    repeat rstep.
  Qed.

  (** Properties *)

  Global Instance c_to_asm_primitive_properties_to_deterministic D σ i:
    CPrimitives.CPrimitiveExtcallProperties D σ ->
    AsmPrimitives.AsmPrimitiveDeterministic D (c_to_asm_primitive D i σ).
  Proof.
    intros H.
    constructor.
    simpl.
    intros [rs m] [rs1 m1] [rs2 m2].
    destruct 1 as (_ & _ & _ & sg1 & vargs_asm1 & ARGS1 & _ & csg1 & Hcsg1 & ? & v1 & Hstep1 & ?) ; subst.
    destruct 1 as (_ & _ & _ & sg2 & vargs_asm2 & ARGS2 & _ & csg2 & Hcsg2 & ? & v2 & Hstep2 & ?) ; subst.
    assert (csg1 = csg2) by eauto using CPrimitives.cprimitive_ec_determ_sg.
    subst.
    assert (vargs_asm1 = vargs_asm2).
    {
      revert ARGS2.
      revert ARGS1.
      apply extcall_arguments_determ.
    }
    subst.
    assert ((v1, m1) = (v2, m2)) by eauto using CPrimitives.cprimitive_ec_determ.
    congruence.
  Qed.

  (** Layers *)

  Definition c_to_asm_layer {D: layerdata}: CPrimitives.clayer D -> AsmPrimitives.asmlayer D :=
    PTreeLayerMap.map (c_to_asm_primitive D) (fun _ => MakeProgramSpec.globvar_map (fun _ => tt)).

  (* XXX: those should be (derived from) properties of [map] *)

  Global Instance c_to_asm_layer_monotonic:
    Monotonic
      (@c_to_asm_layer)
      (forallr R @ D1 D2,
       sim R ++>
       sim R).
  Proof.
    intros D1 D2 R L1 L2 HL.
    apply PTreeLayers.ptree_layer_sim_pointwise in HL.
    destruct HL as (HL_prim & HL_var).
    apply PTreeLayers.ptree_layer_pointwise_sim.
    + intros i.
      specialize (HL_prim i).
      unfold c_to_asm_layer.
      repeat erewrite @PTreeLayerMap.get_layer_primitive_map.
      inversion HL_prim as [ ? ? PRIM | ]; subst; constructor.
      inversion PRIM; subst; constructor.
      solve_monotonic.
    + intros i.
      specialize (HL_var i).
      unfold c_to_asm_layer.
      repeat erewrite @PTreeLayerMap.get_layer_globalvar_map.
      inversion HL_var as [ ? ? VAR | ]; subst; constructor.
      inversion VAR; subst; constructor.
      reflexivity.
  Qed.

  Global Instance c_to_asm_layer_preserves_invariant D L:
    Layers.ForallPrimitive D (CPrimitives.CPrimitivePreservesInvariant D) L ->
    Layers.ForallPrimitive D (AsmPrimitives.AsmPrimitivePreservesInvariant D) (c_to_asm_layer L).
  Proof.
    intros H.
    constructor.
    intros i σ.
    unfold c_to_asm_layer.
    erewrite @PTreeLayerMap.get_layer_primitive_map.
    destruct (Layers.get_layer_primitive i L) as [ [ | ] | ] eqn:PRIM; try discriminate.
    inversion 1; subst.
    generalize (Layers.forall_primitive_at _ _ PRIM).
    typeclasses eauto.
  Qed.

  Global Instance c_to_asm_layer_properties_to_deterministic D L:
    Layers.ForallPrimitive D (CPrimitives.CPrimitiveExtcallProperties D) L ->
    Layers.ForallPrimitive D (AsmPrimitives.AsmPrimitiveDeterministic D) (c_to_asm_layer L).
  Proof.
    intros H.
    constructor.
    intros i σ.
    unfold c_to_asm_layer.
    erewrite @PTreeLayerMap.get_layer_primitive_map.
    destruct (Layers.get_layer_primitive i L) as [ [ | ] | ] eqn:PRIM; try discriminate.
    inversion 1; subst.
    generalize (Layers.forall_primitive_at _ _ PRIM).
    typeclasses eauto.
  Qed.

  Lemma c_to_asm_layer_oplus {D: layerdata} (L1 L2: CPrimitives.clayer D):
    Layers.layers_disjoint L1 L2 ->
    c_to_asm_layer (L1 ⊕ L2) ≤ c_to_asm_layer L1 ⊕ c_to_asm_layer L2.
  Proof.
    intro DISJ.
    apply PTreeLayers.ptree_layer_pointwise_sim.
    + intro i.
      unfold c_to_asm_layer.
      rewrite Layers.get_layer_primitive_oplus.
      repeat erewrite @PTreeLayerMap.get_layer_primitive_map.
      generalize (Layers.layers_disjoint_primitive i _ _ _ DISJ).
      unfold CPrimitives.clayer_ops.
      destruct 1 as [EQ | EQ]; rewrite EQ;
      destruct (Layers.get_layer_primitive i L1) as [ [ c | ] | ];
        edestruct (Layers.get_layer_primitive i L2) as [ [ c0 | ] | ];
        simpl;
        monad_norm;
        simpl;
        repeat rstep;
      (* TODO: better automation or cleaner lemmas for: *)
        generalize (PseudoJoin.is_join D (c_to_asm_primitive D i c) (c_to_asm_primitive D i c0));
        intro LUB.
      - exact (PseudoJoin.hlub_ub_l (SimLUB := LUB)).
      - exact (PseudoJoin.hlub_ub_r (SimLUB := LUB)).
    + intro i.
      unfold c_to_asm_layer.
      rewrite Layers.get_layer_globalvar_oplus.
      repeat erewrite @PTreeLayerMap.get_layer_globalvar_map.
      generalize (Layers.layers_disjoint_globalvar i _ _ _ DISJ).
      unfold CPrimitives.clayer_ops.
      rewrite Layers.get_layer_globalvar_oplus.
      destruct 1 as [EQ | EQ]; rewrite EQ.
      - generalize (PseudoJoin.oplus_le_left (A := res (option (globvar unit)))).
        unfold LeftUpperBound. intro U.
        apply U.
      - rewrite GlobalVars.res_option_globalvar_oplus_comm.
        generalize (PseudoJoin.oplus_le_left (A := res (option (globvar unit)))).
        unfold LeftUpperBound. intro U.
        apply U.
  Qed.

  Lemma oplus_c_to_asm_primitive {D: layerdata} i (σ1 σ2: CPrimitives.cprimitive D):
    c_to_asm_primitive D i σ1 ⊕ c_to_asm_primitive D i σ2 ≤ c_to_asm_primitive D i (σ1 ⊕ σ2).
  Proof.
    split.
    intros p [rsh mh] [rsl ml] Hinit.
    destruct Hinit as [Hrs Hm].
    simpl in Hrs, Hm.
    subst.
    generalize Hrs. intro Hrs_.
    apply wt_regset_match_subrel in Hrs.
    rewrite regset_match_id in Hrs.
    subst.
    intros [rs' m'] Hstep.
    exists (rs', m').
    split.
    {
      destruct Hstep as [ PRIM | PRIM ];
      destruct PRIM as
      (SP_NOT_VUNDEF & RA_NOT_VUNDEF & SYMB &
       sg & vargs_asm & Hvargs_asm &
       (csg_c & Hcsg_c & Hsg_c & m_c & Hm_c & res_c & Hres_c) &
       csg & Hcsg & Hsg &
       v' & Hv' & Hrs');
      simpl;
      eauto 25 using in_or_app.
    }
    exists p.
    split; [ reflexivity | ].
    split; simpl; auto.
    rewrite regset_match_id.
    reflexivity.
  Qed.

  Lemma oplus_c_to_asm_layer {D: layerdata} (L1 L2: CPrimitives.clayer D):
    c_to_asm_layer L1 ⊕ c_to_asm_layer L2 ≤ c_to_asm_layer (L1 ⊕ L2).
  Proof.
    apply PTreeLayers.ptree_layer_pointwise_sim.
    + intro i.
      unfold c_to_asm_layer.
      rewrite Layers.get_layer_primitive_oplus.
      repeat erewrite @PTreeLayerMap.get_layer_primitive_map.
      rewrite Layers.get_layer_primitive_oplus.
      destruct (Layers.get_layer_primitive i L1) as [ [ | ] | ];
        edestruct (Layers.get_layer_primitive i L2) as [ [ | ] | ];
        simpl;
        monad_norm;
        simpl;
        repeat rstep.
      apply oplus_c_to_asm_primitive.
    + intro i.
      unfold c_to_asm_layer.
      rewrite Layers.get_layer_globalvar_oplus.
      repeat erewrite @PTreeLayerMap.get_layer_globalvar_map.
      rewrite Layers.get_layer_globalvar_oplus.
      destruct (Layers.get_layer_globalvar i L1) as [ [ g1 | ] | ];
        edestruct (Layers.get_layer_globalvar i L2) as [ [ g2 | ] | ];
        simpl;
        monad_norm;
        simpl;
        unfold Errors.bind;
        GlobalVars.res_option_globalvar_red;
        try now repeat constructor.
      unfold MakeProgramSpec.globvar_map.
      destruct (GlobalVars.globalvar_eq_dec g1 g2).
      - subst.
        autorewrite with res_option_globalvar.
        reflexivity.
      - rewrite (GlobalVars.res_option_globalvar_oplus_diff g1 g2) by assumption.
        constructor.
  Qed.

End ASMPRIMITIVE.
