Require Import compcert.lib.Coqlib.
Require Import compcert.common.Memtype.
Require Import compcert.common.AST.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcertx.x86.AsmX.
Require Import liblayers.lib.Decision.
Require Import liblayers.logic.LayerData.
Require Import liblayers.logic.Layers.
Require Export liblayers.compcertx.CompcertStructures.
Require Import liblayers.compcertx.ErrorMonad.
Require Import liblayers.compcertx.AbstractData.
Require Import liblayers.compcertx.AbstractData.
Require Import liblayers.compat.CompatData.
Require Import liblayers.compat.CompatCPrimitives.


(** * Low-level step relations *)

Definition sprimcall_sem `{mem_ops: Mem.MemoryModelOps} :=
  regset -> mem -> regset -> mem -> Prop.

Section STEP_RELATIONS.
  Context `{mem_ops: Mem.MemoryModelOps}.

  (** ** Semantics of low-level primitives *)

  Record sprimcall_info :=
    {
      sprimcall_step :> regset -> mem -> regset -> mem -> Prop;
      sprimcall_sig: AST.signature
    }.

  Record sprimcall_info_le (sem1 sem2: sprimcall_info): Prop :=
    {
      sprimcall_info_le_step:
        (- ==> - ==> - ==> - ==> impl)
          (sprimcall_step sem1)
          (sprimcall_step sem2);
      sprimcall_info_le_sig:
        sprimcall_sig sem1 =
        sprimcall_sig sem2
    }.

  Global Instance sprimcall_info_le_preorder:
    PreOrder sprimcall_info_le.
  Proof.
    split.
    * intros sem.
      split; eauto; reflexivity.
    * intros sem1 sem2 sem3 [] [].
      split; eauto; etransitivity; eauto.
  Qed.

  (** ** Miscellaneous definitions *)

  (** Here we need to redefine the whole thing just because of
    [inv_mem_valid], which hadrly belongs there. Oh well. *)

  Record inject_neutral_invariant (rs: Asm.regset) (m: mem) :=
    {
      inv_mem_valid:
        glob_threshold <= Mem.nextblock m;
      inv_mem_inject_neutral:
        Mem.inject_neutral (Mem.nextblock m) m;
      inv_reg_inject_neutral r:
        val_inject (Mem.flat_inj (Mem.nextblock m)) (rs r) (rs r)
    }.

  Record asm_invariant (rs: Asm.regset) (m: mem): Prop :=
    {
      inv_inject_neutral : inject_neutral_invariant rs m;
      inv_reg_wt : wt_regset rs
    }.
End STEP_RELATIONS.


(** * Optional properties *)

Section OPTIONAL_PROPERTIES.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Class PrimcallProperties {D: compatdata} (sem: sprimcall_sem (mem := mwd D)) :=
    {
      primitive_call_determ r m r1 m1 r2 m2:
        sem r m r1 m1 ->
        sem r m r2 m2 ->
        m1 = m2 /\ r1 = r2
    }.

  Class PrimcallInvariants {D: compatdata} (sem: sprimcall_sem (mem := mwd D)) :=
    {
      primitive_call_invariant rs m rs' m':
        sem rs m rs' m' ->
        asm_invariant rs m ->
        asm_invariant rs' m';

      primitive_call_low_level_invariant rs m d rs' m' d':
        sem rs (m, d) rs' (m', d') ->
        asm_invariant rs m ->
        low_level_invariant (Mem.nextblock m) d ->
        low_level_invariant (Mem.nextblock m') d';

      primitive_call_high_level_invariant rs m d rs' m' d':
        sem rs (m, d) rs' (m', d') ->
        high_level_invariant d ->
        high_level_invariant d';

      primitive_call_inv_nextblock rs m d rs' m' d':
        sem rs (m, d) rs' (m', d') ->
        Mem.nextblock m <= Mem.nextblock m'
    }.

  Record sprimcall_primsem (D: compatdata) :=
    {
      sprimcall_primsem_step :> sprimcall_info (mem := mwd D);
      sprimcall_props: res (PrimcallProperties sprimcall_primsem_step);
      sprimcall_invs: res (PrimcallInvariants sprimcall_primsem_step)
    }.

  Global Instance: forall D, Measure (sprimcall_primsem_step D).

  Definition sprimcall_primsem_le {D} :=
    (sprimcall_info_le @@ sprimcall_primsem_step D)%signature.

  Global Instance sprimcall_primsem_le_preorder D:
    PreOrder (sprimcall_primsem_le (D:=D)).
  Proof.
    split; typeclasses eauto.
  Qed.

  Lemma sprimcall_primsem_le_invs {D} (sem1 sem2: sprimcall_primsem D):
    sprimcall_primsem_le sem1 sem2 ->
    PrimcallInvariants sem2 ->
    PrimcallInvariants sem1.
  Proof.
    intros Hsem H.
    destruct sem1 as [sem1 props1 invs1].
    destruct sem2 as [sem2 props2 invs2].
    destruct Hsem as [Hstep12 Hsig12].
    destruct H as [Hstep Hcsig Hinvs Hinj Hwt]; subst.
    simpl in *.
    unfold arrow_pointwise_rel, impl in *.
    split; eauto.
  Qed.
End OPTIONAL_PROPERTIES.


(** * Simulation diagrams *)

Section SIM.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Class MatchPrimcallStates {D1 D2} R f rs1 m1 d1 rs2 m2 d2 :=
    {
      match_extcall_states :>
        MatchExtcallStates (D1:=D1) (D2:=D2) R f m1 d1 m2 d2;
      match_reg reg:
        val_inject f (Pregmap.get reg rs1) (Pregmap.get reg rs2)
    }.

  Record sprimcall_sim {D1 D2: compatdata} (R: compatrel D1 D2)
         (sem1: sprimcall_primsem D1) (sem2: sprimcall_primsem D2): Prop :=
    {
      sprimcall_sim_step:
        forall f rs1 m1 d1 rs1' m1' d1' rs2 m2 d2,
        forall (LOW_LEVEL_INVARIANT: low_level_invariant (Mem.nextblock m2) d2),
        forall (L_HIGH_LEVEL_INVARIANT: high_level_invariant d2),
        forall (H_HIGH_LEVEL_INVARIANT: high_level_invariant d1),
        forall (ASM_INV: asm_invariant (mem:= mwd D2) rs2 (m2, d2)),
          sprimcall_step sem1 rs1 (m1, d1) rs1' (m1', d1') ->
          MatchPrimcallStates R f rs1 m1 d1 rs2 m2 d2 ->
          exists f' rs2' m2' d2',
            sprimcall_step sem2 rs2 (m2, d2) rs2' (m2', d2') /\
            MatchPrimcallStates R f' rs1' m1' d1' rs2' m2' d2';
      sprimcall_sim_sig:
        sprimcall_sig sem2 = sprimcall_sig sem1;
      sprimcall_sim_invs:
        PrimcallInvariants sem1
    }.

  Global Instance sprimcall_sim_le {D1 D2} (R: compatrel D1 D2):
    Proper
      (sprimcall_primsem_le --> sprimcall_primsem_le ++> impl)
      (sprimcall_sim R).
  Proof.
    intros sem1' sem1 Hsem1 sem2 sem2' Hsem2 H.
    destruct sem1 as [sem1 props1 invs1].
    destruct sem2 as [sem2 props2 invs2].
    destruct sem1' as [sem1' props1' invs1'].
    destruct sem2' as [sem2' props2' invs2'].
    destruct Hsem1 as [Hstep1 Hsig1].
    destruct Hsem2 as [Hstep2 Hsig2].
    destruct H as [Hstep Hsig Hinvs].
    simpl in *.
    constructor; simpl; eauto; try congruence.
    - intros.
      exploit Hstep; try rel_auto; clear Hstep.
      intros [f' [rs2' [m2' [d2' [Hstep2' Hmatch]]]]].
      exists f', rs2', m2', d2'; rel_auto.
    - edestruct Hinvs as [Hasm Hll Hhl]; eauto.
      unfold arrow_pointwise_rel, impl in *.
      split; eauto.
  Qed.
End SIM.
