Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcert.cfrontend.Ctypes.
Require Import liblayers.lib.Decision.
Require Import liblayers.logic.PTrees.
Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.PTreeLayers.
Require Import liblayers.logic.PTreeSemantics.
Require Import liblayers.logic.LayerLogicImpl.
Require Export liblayers.compat.CompatLayerDef.

(** * Semantics of languages *)

Section COMPAT_SEMANTICS.
  Context `{Hmem: Mem.MemoryModel} `{Hmem': !UseMemWithData mem}.
  Context {F: Type}.
  Local Existing Instance ptree_module_ops.
  Local Existing Instance ptree_module_prf.
  Context `{fsem_ops: !FunctionSemanticsOps _ _ _ _ (ptree_module F _) compatlayer}.
  Context `{Hfsem: !FunctionSemantics _ _ _ _ (ptree_module F _) compatlayer}.

  Section COMPAT_SEMANTICS_DEF.
  Local Existing Instance ptree_layer_ops.
  Local Existing Instance ptree_layer_prf.
  Local Existing Instance ptree_semof.
  Local Existing Instance ptree_semantics_ops.
  Local Existing Instance ptree_semantics_prf.

  (** ** [Semantics] *)

  Local Instance compat_semof: Semof (ptree_module _ _) compatlayer compatlayer :=
    {
      semof D ML := cl_inj (semof D ML)
    }.

  Local Instance compat_semantics_ops:
    SemanticsOps ident F compatsem _ (ptree_module _ _) compatlayer := {}.

  Local Existing Instance ptree_module_prf.
  Local Existing Instance ptree_layer_prf.
  Local Existing Instance ptree_semof.
  Local Opaque PTree.combine.
  Local Opaque ptree_semof.

  (** Special case for CompatClightSem. *)
Require Export coqrel.LogicalRelations.
  Local Instance compat_semantics_monotonic:
    Proper
      (∀ -, (≤) * (sim id ∩ rsat layer_wf) ++> - ==> - ==> res_le (sim id))
      (semof_fundef (FunctionSemanticsOps := fsem_ops)) ->
    Proper
      (∀ -, (≤) * (sim id ∩ rsat layer_wf) ++> sim id)
      semof.
  Proof.
    intros H D [M1 L1] [M2 L2] [HM [HL HL2]].
    apply cl_inj_sim_monotonic.
    eapply ptree_semantics_mapdef_monotonic; eauto.
    red.
    simpl.
    eauto.
  Qed.

  Local Instance compat_semantics_sim_monotonic:
    Proper (∀ R, (≤) * (sim R ∩ rsat layer_wf) ++> sim R) semof.
  Proof.
    intros D1 D2 R [L1 M1] [L2 M2] [HL HM].
    simpl.
    apply cl_inj_sim_monotonic.
    apply ptree_semantics_mapdef_sim_monotonic; eauto.
    solve_monotonic.
  Qed.

  Lemma compat_get_semof_primitive {D} i (M: ptree_module F (globvar type)) (L: compatlayer D):
    get_layer_primitive (layer := compatlayer) i (〚M〛 L) = 
    semof_function D (M, L) i (get_module_function i M).
  Proof.
    apply ptree_get_semof_primitive.
  Qed.

  Lemma compat_semantics_variable D i (τ: globvar type) (L: compatlayer D):
    i ↦ τ ≤ 〚i ↦ τ〛 L.
  Proof.
    constructor.
    - apply ptree_semantics_variable.
    - reflexivity.
    - reflexivity.
  Qed.

  Local Instance compat_semantics_prf:
    SemanticsBasics ident F compatsem _ (ptree_module _ _) compatlayer.
  Proof.
    split; intros.
    * solve_monotonic.
    * reflexivity.
    * apply compat_get_semof_primitive.
    * apply compat_semantics_variable.
  Qed.

  End COMPAT_SEMANTICS_DEF.

  Local Existing Instance compat_semantics_ops.
  Local Existing Instance compat_semantics_prf.

  (** Quick test of the decision procedure. *)
  Goal
    forall D,
      module_layer_disjoint (D:=D) (F:=F)
        (1%positive ↦ {| gvar_info := Tvoid;
                          gvar_init := nil;
                          gvar_readonly := false;
                          gvar_volatile := false |})
        (2%positive ↦ {| gvar_info := Tvoid;
                         gvar_init := nil;
                         gvar_readonly := false;
                         gvar_volatile := false |}).
  Proof.
    intros D.
    decision.
  Qed.

  (** Versions of [compat_semantics_spec_xxx] with [module_layer_disjoint]. *)

  Lemma compat_semantics_spec_some_disj {D} M L i f:
    get_module_function i M = OK (Some f) ->
    get_layer_primitive i (〚M〛 L) = fmap Some (semof_fundef D (M, L) i f).
  Proof.
    intros HMi.
    rewrite get_semof_primitive.
    rewrite HMi.
    reflexivity.
  Qed.
End COMPAT_SEMANTICS.
