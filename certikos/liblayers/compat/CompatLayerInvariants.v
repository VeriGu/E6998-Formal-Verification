Require Import compcert.lib.Coqlib.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcert.cfrontend.Ctypes.
Require Import compcertx.x86.AsmX.
Require Import liblayers.lib.Decision.
Require Import liblayers.compcertx.ErrorMonad.
Require Export liblayers.logic.Layers.
Require Export liblayers.logic.PTreeLayers.
Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Export liblayers.compcertx.MemWithData.
Require Export liblayers.compat.CompatData.
Require Export liblayers.compat.CompatPrimSem.
Require Export liblayers.compat.CompatLayerDef.
Require Export liblayers.compat.CompatLayerFacts.

Section WITH_MEMORY_MODEL.
  Context `{Hmem: Mem.MemoryModel} `{Hmem': !UseMemWithData mem}.

  (** We need to know that external functions preserve kernel mode
    (and also other invariants) *)

  Definition sextcall_invs_defined {D} (σ: res (option (compatsem D))): bool :=
    match σ with
      | OK (Some (inl f)) =>
        match sextcall_invs _ f with
          | Error _ => false
          | _ => true
        end
      | _ => true
    end.

  Definition ExtcallInvariantsDefined {D} (L: compatlayer D): Prop :=
    forall i,
      (fun f => sextcall_invs_defined f = true)
      (get_layer_primitive i L).

  (* Declaring this instance is necessary to avoid [Existing Class]
    getting in the way of instance resolution *)
  Global Instance extcall_invariants_defined_dec:
    forall {D} (L: _ D), Decision.Decision (ExtcallInvariantsDefined L) := _.

  Existing Class ExtcallInvariantsDefined.

  (** Let us do the same for [PrimcallInvariants]. *)

  Definition sprimcall_invs_defined {D} (σ: res (option (compatsem D))): bool :=
    match σ with
      | OK (Some (inr f)) =>
        match sprimcall_invs _ f with
          | Error _ => false
          | _ => true
        end
      | _ => true
    end.

  Definition PrimcallInvariantsDefined {D} (L: compatlayer D): Prop :=
    forall i,
      (fun f => sprimcall_invs_defined f = true)
      (get_layer_primitive i L).

  (* Declaring this instance is necessary to avoid [Existing Class]
    getting in the way of instance resolution *)
  Global Instance primcall_invariants_defined_dec:
    forall {D} (L: _ D), Decision.Decision (PrimcallInvariantsDefined L) := _.

  Existing Class PrimcallInvariantsDefined.

  (** More general, less decidable classes. *)

  Inductive InvP {D}: compatsem D -> Prop :=
    | invp_extcall (σ: sextcall_primsem D):
        ExtcallInvariants σ -> InvP (inl σ)
    | invp_primcall (σ: sprimcall_primsem D):
        PrimcallInvariants σ -> InvP (inr σ).

  Class InvariantsAvailable {D} (L: compatlayer D) :=
    invariants_available i σ:
      get_layer_primitive i L = OK (Some σ) ->
      InvP σ.

  Lemma extcall_invariants_available `{Hinv: InvariantsAvailable} i σ:
    get_layer_primitive i L = OK (Some (compatsem_inl σ)) ->
    ExtcallInvariants σ.
  Proof.
    intros H.
    specialize (Hinv i (compatsem_inl σ) H).
    inversion Hinv.
    assumption.
  Qed.

  Lemma primcall_invariants_available `{Hinv: InvariantsAvailable} i σ:
    get_layer_primitive i L = OK (Some (compatsem_inr σ)) ->
    PrimcallInvariants σ.
  Proof.
    intros H.
    specialize (Hinv i (compatsem_inr σ) H).
    inversion Hinv.
    assumption.
  Qed.

  Global Instance invariants_defined_available {D} (L: compatlayer D):
    ExtcallInvariantsDefined L ->
    PrimcallInvariantsDefined L ->
    InvariantsAvailable L.
  Proof.
    intros HLe HLp i σ Hσ.
    destruct σ as [σe | σp]; constructor.
    - specialize (HLe i).
      rewrite Hσ in HLe; clear Hσ.
      destruct σe as [step props invs]; simpl in *.
      destruct invs; try discriminate.
      eauto.
    - specialize (HLp i).
      rewrite Hσ in HLp; clear Hσ.
      destruct σp as [step props invs]; simpl in *.
      destruct invs; try discriminate.
      eauto.
  Qed.

  Global Instance layer_wf_invariants_available {D} (L: compatlayer D):
    layer_wf L ->
    InvariantsAvailable L.
  Proof.
    intros [HLe HLp].
    intros i σ H.
    destruct σ as [σe|σp]; constructor.
    - apply (HLe i σe H).
    - apply (HLp i σp H).
  Qed.

  Lemma invariants_available_layer_wf {D} (L: compatlayer D):
    InvariantsAvailable L ->
    layer_wf L.
  Proof.
    intros H.
    split.
    * intros i σ Hσ.
      specialize (H i _ Hσ).
      inversion H.
      assumption.
    * intros i σ Hσ.
      specialize (H i _ Hσ).
      inversion H.
      assumption.
  Qed.

  Import Maps.
  Local Transparent ptree_layer_ops.

  Local Instance cl_invariants_oplus {D} (L1 L2: compatlayer D):
    InvariantsAvailable L1 ->
    InvariantsAvailable L2 ->
    InvariantsAvailable (L1 ⊕ L2).
  Proof.
    intros HL1 HL2 i σ Hσ.
    specialize (HL1 i).
    specialize (HL2 i).
    simpl in *.
    unfold ptree_layer_primitive in *; simpl in *.
    rewrite PTree.gcombine in Hσ by reflexivity.
    destruct ((fst (cl_base_layer L1)) ! i) as [[|]|];
    destruct ((fst (cl_base_layer L2)) ! i) as [[|]|];
    inversion Hσ; subst;
    simpl in *; monad_norm; simpl in *;
    eauto.
  Qed.

  Lemma compatsim_invs D1 D2 (R: path compatrel D1 D2) σ1 σ2:
    compatsim R σ1 σ2 ->
    InvP σ2 ->
    InvP σ1.
  Proof.
    revert σ1 σ2.
    induction R as [D | D1 D2 D3 R12 R23s IHR23s].
    - simpl.
      intros σ1 σ2 Hσ Hσ2.
      destruct Hσ as [σ1 σ2 Hσ | σ1 σ2 Hσ].
      + inversion Hσ2; clear Hσ2; subst.
        constructor.
        eapply sextcall_primsem_le_invs; eauto.
      + inversion Hσ2; clear Hσ2; subst.
        constructor.
        eapply sprimcall_primsem_le_invs; eauto.
    - intros σ1 σ3 Hσ13 H3.
      apply rtransitivity in Hσ13.
      destruct Hσ13 as (σ2 & Hσ12 & Hσ23).
      cut (InvP σ2); eauto.
      revert Hσ12; clear.
      intros Hσ12 H.
      destruct Hσ12 as [σ1 σ2 Hσ | σ1 σ2 Hσ | σ1 σ2 Hσ]; constructor.
      + inversion H; subst; clear H.
        eapply sextcall_sim_invs; eauto.
      + inversion H; subst; clear H.
        eapply sprimcall_sim_invs; eauto.
      + eauto.
  Qed.

  Lemma cl_sim_invs D1 D2 R (L1 L2: compatlayer _):
    cl_sim D1 D2 R L1 L2 ->
    LayerOK L2 ->
    InvariantsAvailable L2 ->
    InvariantsAvailable L1.
  Proof.
    intros HL HL2 HL2s i σ1 Hσ1.
    pose proof (get_layer_primitive_sim_monotonic _ _ _ i L1 L2 HL) as Hσ;
      clear HL.
    destruct (layer_ok_primitive L2 i (HL2 i)) as [σ2 Hσ2];
      clear HL2.
    pose proof (invariants_available i) as Hia2;
      clear HL2s.
    rewrite Hσ1, Hσ2 in *;
      clear L1 L2 Hσ1 Hσ2.
    inversion Hσ as [_ _ [? | σ1' σ2' Hσ'] | ?]; clear Hσ; subst.
    specialize (Hia2 _ eq_refl).
    eapply compatsim_invs; eauto.
    eapply Hσ'.
  Qed.
End WITH_MEMORY_MODEL.

(** These instances would produce a loop if used as-is in the presence
  of existential variables, but if we insist that the target layer
  actually has the appropriate structure, then it yields a perfect
  syntax-driven resolution. *)
Hint Extern 2 (InvariantsAvailable (_ ⊕ _)) =>
  eapply cl_invariants_oplus : typeclass_instances.
