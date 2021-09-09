Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import compcert.common.AST. (* For ident. *)
Require Import liblayers.compcertx.ErrorMonad.
Require Import liblayers.lib.OptionMonad.
Require Import liblayers.lib.Decision.
Require Import liblayers.logic.PseudoJoin.
Require Import liblayers.logic.OptionOrders.
Require Import liblayers.logic.PTrees.
Require Export liblayers.logic.Layers.
Require Export liblayers.logic.Primitives.
Require Import liblayers.logic.PTreeLayers.
Require Import liblayers.logic.GlobalVars.

(** Total maps between two PTreeLayers. *)

Section WITHMAP.
  Context
    {V_from V_to}
    {layerdata_from layerdata_to}
    {D_from: layerdata_from} {D_to: layerdata_to}
    {primsem_from primsem_to}
    (fp: ident -> primsem_from D_from -> primsem_to D_to)
    (fv: ident -> V_from -> V_to)
  .

  Definition map (L: ptree_layer primsem_from V_from D_from): ptree_layer primsem_to V_to D_to :=
    (PTree.map (fun i => fmap (fp i)) (fst L), PTree.map (fun i => fmap (fv i)) (snd L)).

  Context {primitive_ops_from: PrimitiveOps primsem_from}.
  Context {primitive_ops_to: PrimitiveOps primsem_to}.
  Context {gvar_ops_from: GlobalVarsOps V_from}.
  Context {gvar_ops_to: GlobalVarsOps V_to}.

  Existing Instance ptree_layer_ops.

  Lemma get_layer_primitive_map i (L: ptree_layer primsem_from V_from D_from):
    get_layer_primitive (primsem := primsem_to) i (map L) =
    fmap (option_map (fp i)) (get_layer_primitive (primsem := primsem_from) i L).
  Proof.
    simpl.
    unfold get_layer_primitive.
    Local Transparent ptree_layer_ops.
    unfold ptree_layer_ops.
    unfold ptree_layer_primitive.
    simpl.
    rewrite PTree.gmap.
    destruct (PTree.get i (fst L)); simpl; auto.
    destruct r; simpl; auto.
  Qed.

  Lemma get_layer_globalvar_map i (L: ptree_layer primsem_from V_from D_from):
    get_layer_globalvar i (map L) =
    fmap (option_map (fv i)) (get_layer_globalvar i L).
  Proof.
    simpl.
    unfold get_layer_globalvar.
    Local Transparent ptree_layer_ops.
    unfold ptree_layer_ops.
    unfold ptree_layer_globalvar.
    simpl.
    rewrite PTree.gmap.
    destruct (PTree.get i (snd L)); simpl; auto.
    destruct r; simpl; auto.
  Qed.

End WITHMAP.
