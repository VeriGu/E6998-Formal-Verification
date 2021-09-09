Require Import compcert.lib.Coqlib.
Require Import compcert.common.AST.
Require Import compcert.common.Events.
Require Import compcert.cfrontend.Ctypes.
Require Import compcertx.x86.AsmX.
Require Import liblayers.lib.Decision.
Require Import liblayers.compcertx.CompcertStructures.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compcertx.AbstractData.
Require Import liblayers.compat.CompatData.
Require Import liblayers.compat.CompatCPrimitives.
Require Import liblayers.compat.CompatAsmPrimitives.

(** * Converting from [extcall] to [primcall] *)

Section CALLCONV_DATA_AGNOSTIC.
  Context `{Hmem: Mem.MemoryModel}.

  (** ** Computation of the final register state *)

  (** The final register state is obtained from the initial one by
    making three kinds of modifications. First, the callee-save
    registered are cleared to [Vundef]. Then, the return value is
    encoded into one or more registers, depending on the return type
    associated with the high-level primitive. Finally, the new [PC]
    is set to point to the initial [RA] (the new [RA] is cleared to
    [Vundef]).

    The challenge here is to express this process in a way that is
    somewhat convenient to reason about. For instance applying the
    steps as a sequence of [regset] transformations is cumbersome
    because in order to recover the value of a given register, we need
    to unroll the whole thing and track which step affect it and
    how. Instead, as much as possible, we try to compute the new value
    in one step as a function of the register's name. *)

  (** *** Clear destroyed registers *)

  (** The [destroyed_at_call] registers are cleared to [Vundef]. *)

  Global Instance preg_eq_dec: EqDec preg.
  Proof.
    intros r1 r2.
    red.
    repeat decide equality.
  Defined.

  Definition callconv_destroyed_regs :=
    map preg_of Conventions1.destroyed_at_call ++
    RA :: CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil.

  Definition callconv_destroy_regs (rs: regset): regset :=
    fun r =>
      if decide (In r callconv_destroyed_regs) then
        Vundef
      else
        rs r.

  Global Instance callconv_destroy_regs_inject f:
    Proper ((- ==> val_inject f) ++> (- ==> val_inject f)) callconv_destroy_regs.
  Proof.
    intros rs1 rs2 Hrs r.
    unfold callconv_destroy_regs.
    destruct (decide _); eauto.
  Qed.

  Lemma callconv_destroy_regs_wt rs:
    wt_regset rs ->
    wt_regset (callconv_destroy_regs rs).
  Proof.
    intros H r.
    unfold callconv_destroy_regs.
    destruct (decide _); eauto.
    constructor.
  Qed.

  (** *** Encode the return value *)

  (** The return value will can be encoded into one or more registers,
    depending on the signature's result type. The following function
    operates on a pair containing the register state and a list of
    remaining registers to encode the result in. The value is stored
    in the first register in the list, which is then dropped. *)

  Definition callconv_encode_result_item (rls: regset * list _) (v: val) :=
    match rls with
      | (rs, loc::locs) => (rs # loc <- v, locs)
      | _ => rls
    end.

  Definition callconv_encode_result sg (vres: val) (rs: regset): regset :=
    fst (List.fold_left
           callconv_encode_result_item
           (encode_long (sig_res sg) vres)
           (rs, loc_external_result sg)).

  Global Instance callconv_encode_result_item_inject f:
    Proper
      (prod_rel (- ==> val_inject f) eq ++>
       val_inject f ++>
       prod_rel (- ==> val_inject f) eq)
      callconv_encode_result_item.
  Proof.
    intros [rs1 locs1] [rs2 locs2] [Hrs Hlocs] v1 v2 Hv.
    simpl in *; subst.
    destruct locs2; simpl; solve_monotonic.
  Qed.

  Global Instance callconv_encode_result_inject f:
    Proper
      (- ==> val_inject f ++> (- ==> val_inject f) ++> (- ==> val_inject f))
      callconv_encode_result.
  Proof.
    unfold callconv_encode_result.
    solve_monotonic idtac.
    apply list_val_inject_val_list_inject.
    apply encode_long_inject.
    assumption.
  Qed.

  Lemma callconv_encode_result_wt sg vres rs:
    Val.has_type vres (typ_of_type (csig_res sg)) ->
    wt_regset rs ->
    wt_regset (callconv_encode_result (csig_sig sg) vres rs).
  Proof.
    intros Hvres.
    cut (list_forall2
           (fun v r => Val.has_type v (typ_of_preg r))
           (encode_long (sig_res (csig_sig sg)) vres)
           (loc_external_result (csig_sig sg))).
    * intros H.
      revert rs.
      unfold callconv_encode_result.
      induction H; simpl.
      - tauto.
      - intros rs Hrs.
        apply IHlist_forall2.
        intros r.
        unfold Pregmap.set.
        destruct (PregEq.eq _ _); subst; eauto.
    * unfold loc_external_result.
      unfold Conventions1.loc_result.
      unfold encode_long.
      destruct sg as [args res cc]; simpl in *.
      destruct res; simpl; repeat constructor; eauto.
      + destruct vres; constructor.
      + destruct vres; constructor.
      + destruct f, vres; repeat constructor; eauto.
  Qed.

  (** *** Combine the two and set the [PC] *)

  Definition callconv_final_regs sg (vres: val) (rs: regset): regset :=
    callconv_encode_result sg vres
      ((callconv_destroy_regs rs) # PC <- (rs RA)).

  Global Instance callconv_final_regs_inject f:
    Proper
      (- ==> val_inject f ++> (- ==> val_inject f) ++> (- ==> val_inject f))
      callconv_final_regs.
  Proof.
    unfold callconv_final_regs.
    solve_monotonic eauto.
  Qed.

  Lemma callconv_final_regs_wt sg vres rs:
    Val.has_type vres (typ_of_type (csig_res sg)) ->
    wt_regset rs ->
    wt_regset (callconv_final_regs (csig_sig sg) vres rs).
  Proof.
    intros Hvres Hrs.
    apply callconv_encode_result_wt; eauto.
    unfold Pregmap.set.
    intros r.
    destruct (PregEq.eq _ _); subst.
    * apply (Hrs RA).
    * apply callconv_destroy_regs_wt; eauto.
  Qed.


  (** ** Transformation of step relations *)

  Record callconv_match (sem: sextcall_sem) sg vargs rs m vres rs' m' :=
    {
      (** The original semantics takes a step (vargs, m) -> (vres, m') *)
      callconv_step: sem (decode_longs (sig_args sg) vargs) m vres m';

      (** The initial register state encodes arguments [vargs]. *)
      callconv_init_args: extcall_arguments rs m sg vargs;

      (** Furthermore, [SP] and [RA] should be defined, and [SP]
        should not point to a global variable (apparently, this is for
        the compiler's benefit). *)
      callconv_init_sp: rs ESP <> Vundef;
      callconv_init_ra: rs RA <> Vundef;
      callconv_init_sp_not_global b ofs:
        rs ESP = Values.Vptr b ofs ->
        glob_threshold <= b;

      (** The final register set is constructed as exprected,
        so as to encode the return value. *)
      callconv_final_rs: rs' = callconv_final_regs sg vres rs
    }.

  Definition callconv_sem sg (sem: sextcall_sem): sprimcall_sem :=
    fun rs m rs' m' =>
      exists vargs vres,
        callconv_match sem sg vargs rs m vres rs' m'.

  Definition callconv_info (sem: sextcall_info): sprimcall_info :=
    let sg := csig_sig (sextcall_csig sem) in
    {|
      sprimcall_step := callconv_sem sg (sextcall_step sem);
      sprimcall_sig := sg
    |}.

  Global Instance callconv_info_monotonic:
    Proper (sextcall_info_le ++> sprimcall_info_le) callconv_info.
  Proof.
    intros [step1 sig1] [step2 sig2] [Hstep Hsig].
    simpl in *.
    subst.
    constructor; simpl; eauto.
    intros rs m rs' m'.
    intros (vargs & vres & [Hestep Hvargs Hvres]).
    exists vargs, vres.
    split; eauto.
    apply Hstep; eauto.
  Qed.
End CALLCONV_DATA_AGNOSTIC.

Section CALLCONV_WITH_DATA.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Lemma extcall_arg_lift {D: compatdata} rs m (d: D) loc v:
    extcall_arg rs (m, d) loc v <->
    extcall_arg rs m loc v.
  Proof.
    split; destruct 1; econstructor; eauto.
  Qed.

  Lemma extcall_arguments_lift {D: compatdata} rs m (d: D) sg vargs:
    extcall_arguments rs (m, d) sg vargs <->
    extcall_arguments rs m sg vargs.
  Proof.
    unfold extcall_arguments.
    revert vargs.
    induction (Conventions1.loc_arguments sg) as [ | loc locs IHlocs].
    * split; inversion 1; subst; econstructor.
    * split; inversion 1; subst; econstructor.
      + rewrite extcall_arg_lift in H2; assumption.
      + rewrite IHlocs in H4; assumption.
      + rewrite extcall_arg_lift; assumption.
      + rewrite IHlocs; assumption.
  Qed.

  (** ** Projected invariants and properties *)

  Global Instance callconv_properties {D: compatdata} (sem: sextcall_info (mem := mwd D)):
    ExtcallProperties sem ->
    PrimcallProperties (callconv_info sem).
  Proof.
    intros Hsem.
    split.
    * intros rs m rs1 m1 rs2 m2 H1 H2.
      destruct H1 as (vargs1 & vres1 & [Hstep1 Hvargs1 Hvres1]).
      destruct H2 as (vargs2 & vres2 & [Hstep2 Hvargs2 Hvres2]).
      pose proof (extcall_arguments_determ rs m _ _ _ Hvargs2 Hvargs1); subst.
      edestruct (external_call_determ _ _ _ _ _ _ Hstep1 Hstep2); eauto.
      subst; eauto.
  Qed.

  Global Instance wt_regset_inject f:
    Proper ((- ==> val_inject f) --> impl) wt_regset.
  Proof.
    intros rs1 rs2 Hrs H r.
    specialize (H r).
    destruct (Hrs r); eauto.
    constructor.
  Qed.

  Global Instance callconv_invariants {D: compatdata} (sem: sextcall_info (mem := mwd D)):
    ExtcallInvariants sem ->
    PrimcallInvariants (callconv_info sem).
  Proof.
    intros Hsem.
    split.
    * intros rs [m d] rs' [m' d'] Hstep [[Hnext Hm Hrs] Hwt].
      destruct Hstep as (vargs & vres & [Hstep Hvargs Hvres]).
      split; [split|].
      + transitivity (Mem.nextblock m); eauto.
        lift_unfold.
        eapply external_call_inv_nextblock; eauto.
      + pose proof (extcall_args_inject_neutral (mem:=mwd D) rs (m, d)).
        lift_unfold.
        eapply external_call_inject_neutral; eauto.
        apply decode_longs_inject.
        eauto.
      + intros r.
        subst.
        pose proof (external_call_inv_nextblock _ _ _ _ _ _ Hstep) as Hfi.
        apply flat_inj_incr in Hfi.
        edestruct external_call_inject_neutral; eauto.
        {
          apply decode_longs_inject.
          eapply val_list_inject_incr; eauto.
          apply extcall_arguments_lift in Hvargs.
          eapply extcall_arguments_vargs_inject; eauto.
          apply Mem.neutral_inject.
          apply Hm.
        }
        solve_monotonic eauto.
      + subst.
        apply callconv_final_regs_wt; eauto.
        eapply external_call_inv_well_typed; eauto.
    * intros rs m d rs' m' d' Hstep Hai Hlli.
      destruct Hstep as (vargs & vres & [Hstep Hvargs Hvres]).
      eapply external_call_low_level_invariant; eauto.
      eapply inv_mem_valid.
      eapply inv_inject_neutral.
      eassumption.
    * intros rs m d rs' m' d' Hstep Hhli.
      destruct Hstep as (vargs & vres & [Hstep Hvargs Hvres]).
      eapply external_call_high_level_invariant; eauto.
    * intros rs m d rs' m' d' Hstep.
      destruct Hstep as (vargs & vres & [Hstep Hvargs Hvres]).
      eapply external_call_inv_nextblock; eauto.
  Qed.

  (** ** *)

  Definition callconv_primsem D (sem: sextcall_primsem D): sprimcall_primsem D :=
    {|
      sprimcall_primsem_step :=
        callconv_info (sextcall_primsem_step D sem);
      sprimcall_props :=
        match sextcall_props D sem with
          | OK _ => OK _
          | Error msg => Error msg
        end;
      sprimcall_invs :=
        match sextcall_invs D sem with
          | OK _ => OK _
          | Error msg => Error msg
        end
    |}.

  Global Instance callconv_primsem_le_monotonic:
    Proper (∀ -, sextcall_primsem_le ++> sprimcall_primsem_le) callconv_primsem.
  Proof.
    intros D σ1 σ2 Hσ.
    destruct σ1 as [[σ1 sig1] props1 invs1].
    destruct σ2 as [[σ2 sig2] props2 invs2].
    destruct Hσ as [Hstep Hsig].
    * split; simpl in *; subst; eauto.
      intros rs m rs' m' H.
      destruct H as (vargs & vres & [H Hvargs Hrs']).
      exists vargs, vres.
      split; eauto.
      eapply Hstep; eauto.
  Qed.

  Lemma val_inject_defined f v1 v2:
    val_inject f v1 v2 ->
    v1 <> Vundef ->
    v2 <> Vundef.
  Proof.
    intros Hv Hv1 Hv2.
    destruct Hv; congruence.
  Qed.

  Global Instance callconv_primsem_sim_monotonic:
    Proper (∀ R, sextcall_sim R ++> sprimcall_sim R) callconv_primsem.
  Proof.
    intros D1 D2 R σ1 σ2 Hσ.
    destruct σ1 as [[σ1 sig1] props1 invs1].
    destruct σ2 as [[σ2 sig2] props2 invs2].
    destruct Hσ as [Hstep Hsig Hinvs].
    split; simpl in *.
    * intros f rs1 m1 d1 rs1' m1' d1' rs2 m2 d2 Hl2 Hh2 Hh1 Hasm2 H Hmatch.
      destruct Hmatch as [Hmatch Hrs].
      destruct H as (vargs1 & vres1 & [H Hvargs1 Hsp Hra Hspng Hrs1']); subst.

      (** First, we need to come up with the injected arguments, which
        we read from [m2]. *)
      pose proof match_inject.
      edestruct extcall_arguments_inject as (vargs2 & Hvargs & Hvargs2); eauto.
      {
        apply (extcall_arguments_lift rs1 m1 d1 (csig_sig sig2) vargs1).
        assumption.
      }

      (** Now, apply the extcall step. *)
      specialize (Hstep).
      edestruct Hstep as (f' & vres2 & m2' & d2' & H2 & Hvres & Hm2 & Hf); eauto.
      {
        apply decode_longs_inject.
        eassumption.
      }

      (** From there, construct a corresponding low-level final state *)
      exists f', (callconv_final_regs (csig_sig sig2) vres2 rs2), m2', d2'.
      split.
      + exists vargs2, vres2.
        split; eauto.
        - apply extcall_arguments_lift; eauto.
        - eapply val_inject_defined; eauto.
        - eapply val_inject_defined; eauto.
        - intros b ofs Hrs2.
          specialize (Hrs ESP).
          unfold Pregmap.get in Hrs.
          destruct Hrs; inversion Hrs2; subst; eauto; try congruence.
          apply match_inject_forward in H1.
          destruct H1; subst.
          transitivity b1; eauto.
      + split; eauto.
        intros reg.
        unfold Pregmap.get.
        solve_monotonic eauto.
    * congruence.
    * eapply callconv_invariants in Hinvs.
      simpl in Hinvs.
      assumption.
  Qed.
End CALLCONV_WITH_DATA.
