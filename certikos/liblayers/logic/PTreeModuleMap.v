Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import compcert.common.AST. (* For ident. *)
Require Import liblayers.compcertx.ErrorMonad.
Require Import liblayers.lib.OptionMonad.
Require Import liblayers.lib.Decision.
Require Import liblayers.logic.PseudoJoin.
Require Import liblayers.logic.OptionOrders.
Require Import liblayers.logic.PTrees.
Require Import liblayers.logic.Modules.
Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.GlobalVars.

(** Total maps between two PTreeModules. *)

Section WITHMAP.

  Context
    {F_from F_to V_from V_to}
    {gvar_from_ops: GlobalVarsOps V_from}
    {gvar_from_to: GlobalVarsOps V_to}
    (ff: ident -> F_from -> F_to)
    (fv: ident -> V_from -> V_to)
  .

  Definition map (M: ptree_module F_from V_from): ptree_module F_to V_to :=
    (PTree.map (fun i => fmap (ff i)) (fst M), PTree.map (fun i => fmap (fv i)) (snd M)).

  Existing Instance ptree_module_ops.

  Lemma get_module_function_map i (M: ptree_module F_from V_from):
    get_module_function i (map M) = fmap (option_map (ff i)) (get_module_function i M).
  Proof.
    simpl.
    unfold get_module_function.
    Local Transparent ptree_module_ops.
    unfold ptree_module_ops.
    unfold ptree_module_function.
    simpl.
    rewrite PTree.gmap.
    destruct (PTree.get i (fst M)); simpl; auto.
    destruct r; simpl; auto.
  Qed.

  Lemma get_module_variable_map i (M: ptree_module F_from V_from):
    get_module_variable i (map M) = fmap (option_map (fv i)) (get_module_variable i M).
  Proof.
    simpl.
    unfold get_module_variable.
    Local Transparent ptree_module_ops.
    unfold ptree_module_ops.
    unfold ptree_module_variable.
    simpl.
    rewrite PTree.gmap.
    destruct (PTree.get i (snd M)); simpl; auto.
    destruct r; simpl; auto.
  Qed.

End WITHMAP.

Section WITHMAPERROR.

  Context
    {F_from F_to V_from V_to}
    {gvar_from_ops: GlobalVarsOps V_from}
    {gvar_from_to: GlobalVarsOps V_to}
    (ff: ident -> F_from -> res F_to)
    (fv: ident -> V_from -> res V_to)
  .

  Definition map_error (M: ptree_module F_from V_from): ptree_module F_to V_to :=
    (PTree.map (fun i x => Errors.bind x (ff i)) (fst M), PTree.map (fun i x => Errors.bind x (fv i)) (snd M)).

  Existing Instance ptree_module_ops.

  Lemma get_module_function_map_error i (M: ptree_module F_from V_from):
    get_module_function i (map_error M) = option_res_flip (option_map (fun x => Errors.bind x (ff i)) (res_option_flip (get_module_function i M))).
  Proof.
    simpl.
    unfold get_module_function.
    Local Transparent ptree_module_ops.
    unfold ptree_module_ops.
    unfold ptree_module_function.
    simpl.
    rewrite PTree.gmap.
    rewrite option_res_flip_inv.
    reflexivity.
  Qed.

  Lemma get_module_variable_map_error i (M: ptree_module F_from V_from):
    get_module_variable i (map_error M) = option_res_flip (option_map (fun x => Errors.bind x (fv i)) (res_option_flip (get_module_variable i M))).
  Proof.
    simpl.
    unfold get_module_variable.
    Local Transparent ptree_module_ops.
    unfold ptree_module_ops.
    unfold ptree_module_variable.
    simpl.
    rewrite PTree.gmap.
    rewrite option_res_flip_inv.
    reflexivity.
  Qed.

End WITHMAPERROR.
