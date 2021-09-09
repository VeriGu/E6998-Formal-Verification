Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Floats.
Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcertx.backend.I64helpers.
Require Import compcert.backend.SelectLong.
Require Import compcertx.backend.SelectLongproofX.
Require Import liblayers.compat.CompatPrimSem.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatExternalCalls.
Require Import compcert.cfrontend.Ctypes.
Require Import liblayers.compat.I64Layer.

Section WITHSTENCIL.
Context `{Hmem: Mem.MemoryModel}.
Context `{Hmwd: UseMemWithData mem}.

Lemma res_le_T_ok {A B} (x: A) (y: B):
  res_le ⊤%rel (OK x) (OK y).
Proof.
  repeat constructor.
Qed.

Hint Extern 10 (res_le ⊤%rel _ _) => apply res_le_T_ok.

Theorem L64_auto_sim:
    forall (D1 D2: compatdata) (R: compatrel D1 D2),
      sim (path_inj R) L64 L64.
Proof.
  unfold L64. intros.
  refine (oplus_sim_monotonic _ _ _ _ _ _ _ _ _).
  {
    apply layer_sim_intro.
    constructor.
    constructor; auto.
    intros f vargs1 m1 d1 vres1 m1' d1' vargs2 m2 d2 LOW_LEVEL_INVARIANT.
    intros L_HIGH_LEVEL_INVARIANT H_HIGH_LEVEL_INVARIANT H H0 H1.
    inv H.
    inv H0. inv H5.
    inv H3; try discriminate.
    simpl in Hxz.
    destruct (Float.longoffloat f0) eqn:?; try discriminate.
    inv Hxz.
    esplit. esplit. esplit. esplit.
    split.
    - econstructor; simpl; eauto.
      rewrite Heqo. reflexivity.
    - split; eauto.
    - apply sextcall_longoffloat_invariants.
  }
  refine (oplus_sim_monotonic _ _ _ _ _ _ _ _ _).
  {
    apply layer_sim_intro.
    constructor.
    constructor; auto.
    intros f vargs1 m1 d1 vres1 m1' d1' vargs2 m2 d2 LOW_LEVEL_INVARIANT.
    intros L_HIGH_LEVEL_INVARIANT H_HIGH_LEVEL_INVARIANT H H0 H1.
    inv H.
    inv H0. inv H5.
    inv H3; try discriminate.
    simpl in Hxz.
    destruct (Float.longuoffloat f0) eqn:?; try discriminate.
    inv Hxz.
    esplit. esplit. esplit. esplit.
    split.
    - econstructor; simpl; eauto.
      rewrite Heqo. reflexivity.
    - split; eauto.
    - apply sextcall_longuoffloat_invariants.
  }
  refine (oplus_sim_monotonic _ _ _ _ _ _ _ _ _).
  {
    apply layer_sim_intro.
    constructor.
    constructor; auto.
    intros f vargs1 m1 d1 vres1 m1' d1' vargs2 m2 d2 LOW_LEVEL_INVARIANT.
    intros L_HIGH_LEVEL_INVARIANT H_HIGH_LEVEL_INVARIANT H H0 H1.
    inv H.
    inv H0. inv H5.
    inv H3; try discriminate.
    inv Hxz.
    esplit. esplit. esplit. esplit.
    split.
    - econstructor; simpl; eauto.
    - split; eauto.
    - apply sextcall_floatoflong_invariants.
  }
  refine (oplus_sim_monotonic _ _ _ _ _ _ _ _ _).
  {
    apply layer_sim_intro.
    constructor.
    constructor; auto.
    intros f vargs1 m1 d1 vres1 m1' d1' vargs2 m2 d2 LOW_LEVEL_INVARIANT.
    intros L_HIGH_LEVEL_INVARIANT H_HIGH_LEVEL_INVARIANT H H0 H1.
    inv H.
    inv H0. inv H5.
    inv H3; try discriminate.
    inv Hxz.
    esplit. esplit. esplit. esplit.
    split.
    - econstructor; simpl; eauto.
    - split; eauto.
    - apply sextcall_floatoflongu_invariants.
  }
  refine (oplus_sim_monotonic _ _ _ _ _ _ _ _ _).
  {
    apply layer_sim_intro.
    constructor.
    constructor; auto.
    intros f vargs1 m1 d1 vres1 m1' d1' vargs2 m2 d2 LOW_LEVEL_INVARIANT.
    intros L_HIGH_LEVEL_INVARIANT H_HIGH_LEVEL_INVARIANT H H0 H1.
    inv H.
    inv H0. inv H5.
    inv H3; try discriminate.
    inv Hxz.
    esplit. esplit. esplit. esplit.
    split.
    - econstructor; simpl; eauto.
    - split; eauto.
    - apply sextcall_singleoflong_invariants.
  }
  refine (oplus_sim_monotonic _ _ _ _ _ _ _ _ _).
  {
    apply layer_sim_intro.
    constructor.
    constructor; auto.
    intros f vargs1 m1 d1 vres1 m1' d1' vargs2 m2 d2 LOW_LEVEL_INVARIANT.
    intros L_HIGH_LEVEL_INVARIANT H_HIGH_LEVEL_INVARIANT H H0 H1.
    inv H.
    inv H0. inv H5.
    inv H3; try discriminate.
    inv Hxz.
    esplit. esplit. esplit. esplit.
    split.
    - econstructor; simpl; eauto.
    - split; eauto.
    - apply sextcall_singleoflongu_invariants.
  }
  refine (oplus_sim_monotonic _ _ _ _ _ _ _ _ _).
  {
    apply layer_sim_intro.
    constructor.
    constructor; auto.
    intros f vargs1 m1 d1 vres1 m1' d1' vargs2 m2 d2 LOW_LEVEL_INVARIANT.
    intros L_HIGH_LEVEL_INVARIANT H_HIGH_LEVEL_INVARIANT H H0 H1.
    inv H.
    inv H0. inv H5.
    inv H3; try discriminate.
    inv H6; try discriminate.
    inv H2; try discriminate.
    simpl in Hxz.
    destruct (
        Int64.eq i0 Int64.zero
                 || Int64.eq i (Int64.repr Int64.min_signed) &&
                 Int64.eq i0 Int64.mone
      ) eqn:?; try discriminate.
    inv Hxz.
    esplit. esplit. esplit. esplit.
    split.
    - econstructor; simpl; eauto.
      rewrite Heqb. reflexivity.
    - split; eauto.
    - apply sextcall_divls_invariants.
  }
  refine (oplus_sim_monotonic _ _ _ _ _ _ _ _ _).
  {
    apply layer_sim_intro.
    constructor.
    constructor; auto.
    intros f vargs1 m1 d1 vres1 m1' d1' vargs2 m2 d2 LOW_LEVEL_INVARIANT.
    intros L_HIGH_LEVEL_INVARIANT H_HIGH_LEVEL_INVARIANT H H0 H1.
    inv H.
    inv H0. inv H5.
    inv H3; try discriminate.
    inv H6; try discriminate.
    inv H2; try discriminate.
    simpl in Hxz.
    destruct (
        Int64.eq i0 Int64.zero
      ) eqn:?; try discriminate.
    inv Hxz.
    esplit. esplit. esplit. esplit.
    split.
    - econstructor; simpl; eauto.
      rewrite Heqb. reflexivity.
    - split; eauto.
    - apply sextcall_divlu_invariants.
  }
  refine (oplus_sim_monotonic _ _ _ _ _ _ _ _ _).
  {
    apply layer_sim_intro.
    constructor.
    constructor; auto.
    intros f vargs1 m1 d1 vres1 m1' d1' vargs2 m2 d2 LOW_LEVEL_INVARIANT.
    intros L_HIGH_LEVEL_INVARIANT H_HIGH_LEVEL_INVARIANT H H0 H1.
    inv H.
    inv H0. inv H5.
    inv H3; try discriminate.
    inv H6; try discriminate.
    inv H2; try discriminate.
    simpl in Hxz.
    destruct (
        Int64.eq i0 Int64.zero
                 || Int64.eq i (Int64.repr Int64.min_signed) &&
                 Int64.eq i0 Int64.mone
      ) eqn:?; try discriminate.
    inv Hxz.
    esplit. esplit. esplit. esplit.
    split.
    - econstructor; simpl; eauto.
      rewrite Heqb. reflexivity.
    - split; eauto.
    - apply sextcall_modls_invariants.
  }
  refine (oplus_sim_monotonic _ _ _ _ _ _ _ _ _).
  {
    apply layer_sim_intro.
    constructor.
    constructor; auto.
    intros f vargs1 m1 d1 vres1 m1' d1' vargs2 m2 d2 LOW_LEVEL_INVARIANT.
    intros L_HIGH_LEVEL_INVARIANT H_HIGH_LEVEL_INVARIANT H H0 H1.
    inv H.
    inv H0. inv H5.
    inv H3; try discriminate.
    inv H6; try discriminate.
    inv H2; try discriminate.
    simpl in Hxz.
    destruct (
        Int64.eq i0 Int64.zero
      ) eqn:?; try discriminate.
    inv Hxz.
    esplit. esplit. esplit. esplit.
    split.
    - econstructor; simpl; eauto.
      rewrite Heqb. reflexivity.
    - split; eauto.
    - apply sextcall_modlu_invariants.
  }
  refine (oplus_sim_monotonic _ _ _ _ _ _ _ _ _).
  {
    apply layer_sim_intro.
    constructor.
    constructor; auto.
    intros f vargs1 m1 d1 vres1 m1' d1' vargs2 m2 d2 LOW_LEVEL_INVARIANT.
    intros L_HIGH_LEVEL_INVARIANT H_HIGH_LEVEL_INVARIANT H H0 H1.
    inv H.
    inv H0. inv H5. inv H6.
    esplit. esplit. esplit. esplit.
    split.
    {
      econstructor; simpl; eauto.
    }
    split.
    - inv H3; auto.
      inv H2; auto.
      simpl.
      destruct (Int.ltu i0 Int64.iwordsize'); auto.
    - split; eauto.
    - apply sextcall_shll_invariants.
  }
  refine (oplus_sim_monotonic _ _ _ _ _ _ _ _ _).
  {
    apply layer_sim_intro.
    constructor.
    constructor; auto.
    intros f vargs1 m1 d1 vres1 m1' d1' vargs2 m2 d2 LOW_LEVEL_INVARIANT.
    intros L_HIGH_LEVEL_INVARIANT H_HIGH_LEVEL_INVARIANT H H0 H1.
    inv H.
    inv H0. inv H5. inv H6.
    esplit. esplit. esplit. esplit.
    split.
    {
      econstructor; simpl; eauto.
    }
    split.
    - inv H3; auto.
      inv H2; auto.
      simpl.
      destruct (Int.ltu i0 Int64.iwordsize'); auto.
    - split; eauto.
    - apply sextcall_shrlu_invariants.
  }
  {
    apply layer_sim_intro.
    constructor.
    constructor; auto.
    intros f vargs1 m1 d1 vres1 m1' d1' vargs2 m2 d2 LOW_LEVEL_INVARIANT.
    intros L_HIGH_LEVEL_INVARIANT H_HIGH_LEVEL_INVARIANT H H0 H1.
    inv H.
    inv H0. inv H5. inv H6.
    esplit. esplit. esplit. esplit.
    split.
    {
      econstructor; simpl; eauto.
    }
    split.
    - inv H3; auto.
      inv H2; auto.
      simpl.
      destruct (Int.ltu i0 Int64.iwordsize'); auto.
    - split; eauto.
    - apply sextcall_shrl_invariants.
  }
Qed.

End WITHSTENCIL.
