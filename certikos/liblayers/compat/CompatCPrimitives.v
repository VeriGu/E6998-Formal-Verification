Require Import compcert.lib.Coqlib.
Require Import compcert.common.Memtype.
Require Import compcert.common.AST.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.cfrontend.Ctypes.
Require Import liblayers.lib.Decision.
Require Import liblayers.logic.LayerData.
Require Export liblayers.compcertx.CompcertStructures.
Require Import liblayers.compcertx.ErrorMonad.
Require Import liblayers.compcertx.AbstractData.
Require Import liblayers.compcertx.AbstractData.
Require Import liblayers.compat.CompatData.
Open Scope positive_scope.


(** * High-level step relations *)

Definition sextcall_sem `{mem_ops: Mem.MemoryModelOps} :=
  list val -> mem -> val -> mem -> Prop.

Section WITH_MEMORY_MODEL.
  Context `{mem_ops: Mem.MemoryModelOps}.

  (** ** Extra information *)

  (** In addition to the step relation, those specify the primitive's
    signature (in term of C types) as well as the requirements on
    the stencil used. *)

  Record sextcall_info :=
    {
      sextcall_step :> list val -> mem -> val -> mem -> Prop;
      sextcall_csig: csignature
    }.

  Global Instance: Measure sextcall_step.

  Definition sextcall_args (sem: sextcall_info): Ctypes.typelist :=
    csig_args (sextcall_csig sem).

  Definition sextcall_res (sem: sextcall_info): Ctypes.type :=
    csig_res (sextcall_csig sem).

  Definition sextcall_cc (sem: sextcall_info): AST.calling_convention :=
    csig_cc (sextcall_csig sem).

  Definition sextcall_sig (sem: sextcall_info): signature :=
    csig_sig (sextcall_csig sem).

  (** ** Order *)

  Record sextcall_info_le (sem1 sem2: sextcall_info): Prop :=
    {
      sextcall_info_le_sem:
        (- ==> - ==> - ==> - ==> impl) sem1 sem2;
      sextcall_info_le_sig:
        sextcall_csig sem1 = sextcall_csig sem2
    }.

  Global Instance sextcall_info_le_preorder:
    PreOrder sextcall_info_le.
  Proof.
    split.
    * intros sem.
      split; eauto; reflexivity.
    * intros sem1 sem2 sem3 [] [].
      split; eauto; etransitivity; eauto.
  Qed.
End WITH_MEMORY_MODEL.


(** * Optional properties *)

Section OPTIONAL_PROPERTIES.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  (** FIXME: nomenclature? m1 m2 m1' m2' *)
  Class ExtcallProperties {D: compatdata} (sem: sextcall_info (mem := mwd D)) :=
    {
      external_call_well_typed vargs m1 vres m2:
        sem vargs m1 vres m2 ->
        Val.has_type vres (typ_of_type (sextcall_res sem));

      external_call_valid_block vargs m1 vres m2 b:
        sem vargs m1 vres m2 ->
        Mem.valid_block m1 b ->
        Mem.valid_block m2 b;

      external_call_max_perm vargs m1 vres m2 b ofs p:
        sem vargs m1 vres m2 ->
        Mem.valid_block m1 b ->
        Mem.perm m2 b ofs Max p ->
        Mem.perm m1 b ofs Max p;

      external_call_readonly vargs m1 vres m2:
        sem vargs m1 vres m2 ->
        Mem.unchanged_on (loc_not_writable m1) m1 m2;

      external_call_mem_extends vargs m1 vres m2 m1' vargs':
        sem vargs m1 vres m2 ->
        Mem.extends m1 m1' ->
        Val.lessdef_list vargs vargs' ->
        exists vres' m2',
          sem vargs' m1' vres' m2' /\
          Val.lessdef vres vres' /\
          Mem.extends m2 m2' /\
          Mem.unchanged_on (loc_out_of_bounds m1) m1' m2';

      external_call_mem_inject vargs m1 vres m2 f m1' vargs':
        inject_incr (Mem.flat_inj glob_threshold) f ->
        sem vargs m1 vres m2 ->
        Mem.inject f m1 m1' ->
        val_list_inject f vargs vargs' ->
        exists f' vres' m2',
          sem vargs' m1' vres' m2' /\
          val_inject f' vres vres' /\
          Mem.inject f' m2 m2' /\
          Mem.unchanged_on (loc_unmapped f) m1 m2 /\
          Mem.unchanged_on (loc_out_of_reach f m1) m1' m2' /\
          inject_incr f f' /\
          inject_separated f f' m1 m1';

      external_call_determ vargs m vres1 m1 vres2 m2:
        sem vargs m vres1 m1 ->
        sem vargs m vres2 m2 ->
        vres1 = vres2 /\ m1 = m2

    }.

  Class ExtcallInvariants {D: compatdata} (sem: sextcall_info (mem := mwd D)) :=
    {
      external_call_low_level_invariant vargs m d vres m' d':
        sem vargs (m, d) vres (m', d') ->
        forall VALID_GENV_NEXT: glob_threshold <= Mem.nextblock m,
          low_level_invariant (Mem.nextblock m) d ->
          low_level_invariant (Mem.nextblock m') d';

      external_call_high_level_invariant vargs m d vres m' d':
        sem vargs (m, d) vres (m', d') ->
        high_level_invariant d ->
        high_level_invariant d';

      external_call_kernel_mode vargs m d vres m' d':
        sem vargs (m, d) vres (m', d') ->
        kernel_mode d ->
        kernel_mode d';

      external_call_inv_nextblock vargs m d vres m' d':
        sem vargs (m, d) vres (m', d') ->
        Mem.nextblock m <= Mem.nextblock m';

      external_call_inject_neutral vargs m d vres m' d':
        sem vargs (m, d) vres (m', d') ->
        (* XXXX: is [low_level_invariant (Mem.nextblock m) d] necessary here?
           If so, then this property will have to be moved to [ExtcallInvariants] *)
        val_list_inject (Mem.flat_inj (Mem.nextblock m)) vargs vargs ->
        Mem.inject_neutral (Mem.nextblock m) m ->
        forall NEXT_LE: Ple glob_threshold (Mem.nextblock m),
        (val_inject (Mem.flat_inj (Mem.nextblock m')) vres vres /\
         Mem.inject_neutral (Mem.nextblock m') m');

      external_call_inv_well_typed vargs m1 vres m2:
        sem vargs m1 vres m2 ->
        Val.has_type vres (typ_of_type (sextcall_res sem))

    }.

  Record sextcall_primsem (D: compatdata) :=
    {
      sextcall_primsem_step :> sextcall_info (mem := mwd D);
      sextcall_props: res (ExtcallProperties sextcall_primsem_step);
      sextcall_invs: res (ExtcallInvariants sextcall_primsem_step)
    }.

  Global Instance: forall D, Measure (sextcall_primsem_step D).

  (** ** Order *)

  Definition sextcall_primsem_le {D} :=
    (sextcall_info_le @@ sextcall_primsem_step D)%signature.

  Local Instance RelCompFun_preorder {A B} (R: relation B) (π: A -> B):
    Measure π ->
    PreOrder R ->
    PreOrder (R @@ π)%signature.
  Proof.
    intros Hπ HR.
    split; typeclasses eauto.
  Qed.

  Global Instance sextcall_primsem_le_preorder D:
    PreOrder (sextcall_primsem_le (D:=D)).
  Proof.
    typeclasses eauto.
  Qed.

  Lemma sextcall_primsem_le_invs {D} (sem1 sem2: sextcall_primsem D):
    sextcall_primsem_le sem1 sem2 ->
    ExtcallInvariants sem2 ->
    ExtcallInvariants sem1.
  Proof.
    intros Hsem H.
    destruct sem1 as [sem1 props1 invs1].
    destruct sem2 as [sem2 props2 invs2].
    destruct Hsem as [Hstep12 Hsig12].
    destruct H as [Hstep Hcsig Hvalid Hinvs Hinj Hwt]; subst.
    simpl in *.
    unfold arrow_pointwise_rel, impl in *.
    split; eauto.
    + unfold sextcall_res.
      rewrite Hsig12.
      eauto.
  Qed.
End OPTIONAL_PROPERTIES.


(** * Simulation diagrams *)

Section SIM.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Class MatchExtcallStates {D1 D2} (R: compatrel D1 D2)
      f m1 d1 m2 d2:=
    {
      match_inject:
        Mem.inject f m1 m2;
      match_related:
        relate_AbData f d1 d2;
      match_match:
        match_AbData d1 m2 f;
      match_inject_flat:
        inject_incr (Mem.flat_inj glob_threshold) f;
      match_inject_forward:
        forall b1 b2 delta, f b1 = Some (b2, delta) -> delta = 0%Z /\ b1 <= b2;
      match_nextblock_forward:
        Mem.nextblock m1 <= Mem.nextblock m2;
      match_newglob_noperm i b ofs k p:
        In i new_glbl ->
        find_symbol i = Some b ->
        ~ Mem.perm m1 b ofs k p;
      match_newglob_nextblock i b:
        In i new_glbl ->
        find_symbol i = Some b ->
        b < Mem.nextblock m1;
      match_inject_inject b1 b2 b delta1 delta2:
        f b1 = Some (b, delta1) ->
        f b2 = Some (b, delta2) ->
        b1 = b2
    }.

  Record sextcall_sim {D1 D2: compatdata} (R: compatrel D1 D2)
         (sem1: sextcall_primsem D1) (sem2: sextcall_primsem D2): Prop :=
    {
      sextcall_sim_step:
        forall f vargs1 m1 d1 vres1 m1' d1' vargs2 m2 d2,
        forall (LOW_LEVEL_INVARIANT: low_level_invariant (Mem.nextblock m2) d2),
        forall (L_HIGH_LEVEL_INVARIANT: high_level_invariant d2),
        forall (H_HIGH_LEVEL_INVARIANT: high_level_invariant d1),
        sem1 vargs1 (m1, d1) vres1 (m1', d1') ->
        val_list_inject f vargs1 vargs2 ->
        MatchExtcallStates R f m1 d1 m2 d2 ->
        exists f' vres2 m2' d2',
          sem2 vargs2 (m2, d2) vres2 (m2', d2') /\
          val_inject f vres1 vres2 /\
          MatchExtcallStates R f' m1' d1' m2' d2' /\
          inject_incr f f';
      sextcall_sim_sig:
        sextcall_csig sem1 = sextcall_csig sem2;
      sextcall_sim_invs:
        ExtcallInvariants sem1
    }.

  Global Instance sextcall_sim_le {D1 D2} (R: compatrel D1 D2):
    Proper
      (sextcall_primsem_le --> sextcall_primsem_le ++> impl)
      (sextcall_sim R).
  Proof.
    intros sem1' sem1 Hsem1 sem2 sem2' Hsem2 H.
    destruct sem1 as [sem1 props1 invs1].
    destruct sem2 as [sem2 props2 invs2].
    destruct sem1' as [sem1' props1' invs1'].
    destruct sem2' as [sem2' props2' invs2'].
    destruct Hsem1 as [Hstep1 Hsig1].
    destruct Hsem2 as [Hstep2 Hsig2].
    destruct H as [Hstep Hcsig Hinvs]; subst.
    simpl in *.
    constructor; simpl; eauto; try congruence.
    - intros.
      exploit Hstep; try rel_auto.
      intros [f' [vres2 [m2' [d2' [Hstep2' [Hinj12 Hmatch]]]]]].
      exists f', vres2, m2', d2'; rel_auto.
    - edestruct Hinvs as [Hll2 Hhl2 Hkm2 Hnb2 Hin2 Hwt2]; eauto.
      unfold arrow_pointwise_rel, impl in *.
      split; eauto.
      + unfold sextcall_res.
        rewrite Hsig1.
        eauto.
  Qed.
End SIM.
