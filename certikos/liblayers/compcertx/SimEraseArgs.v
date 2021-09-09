Require Export compcert.common.Memory.
Require Import compcert.backend.Locations.
Require Export compcertx.backend.EraseArgsX.
Require Import liblayers.logic.Structures.
Require Import liblayers.logic.OptionOrders.
Require Export liblayers.simrel.SimulationRelation.
Require Export liblayers.compcertx.SimValues.

Section WITHMEM.
  Context `{Hmem: BaseMemoryModel}.
  Context {D1 D2} (R: simrel D1 D2).

  Local Instance free_extcall_arg_mono p:
    Monotonic
      EraseArgs.free_extcall_arg
      (match_val R p ++>
       match_mem R p ++>
       - ==>
       option_le (incr p (match_mem R p))).
  Proof.
    unfold EraseArgs.free_extcall_arg.
    repeat rstep.
    eapply match_ptrbits_ptr; repeat rstep.
    eapply match_ptrbits_shift; repeat rstep.
    eapply H1.
    destruct ty; simpl size_chunk; omega.
  Qed.

  Local Instance free_extcall_arg_mono_params:
    Params (@EraseArgs.free_extcall_arg) 3.

  Global Instance free_extcall_args_mono p:
    Monotonic
      EraseArgs.free_extcall_args
      (match_val R p ++>
       match_mem R p ++>
       - ==>
       option_le (incr p (match_mem R p))).
  Proof.
    intros sp1 sp2 Hsp m1 m2 Hm l.
    revert p Hsp m1 m2 Hm.
    induction l; simpl; intros; repeat rstep.
    destruct H1 as (w' & Hw' & xy).
    Existing Instance rel_incr_subrel. (* XXX: ?! *)
    exploit (IHl w'); try rauto.
  Qed.    

  Global Instance free_extcall_args_mono_params:
    Params (@EraseArgs.free_extcall_args) 3.

End WITHMEM.
