Require Export compcert.lib.Coqlib.
Require Export compcert.lib.Integers.
Require Export compcert.common.Values.
Require Export compcert.common.Memdata.
Require Export compcert.common.Memtype.
Require Export compcertx.common.MemoryX.
Require Export liblayers.lib.Lens.
Require Export liblayers.lib.Lift.
Require Import liblayers.compcertx.CompcertStructures.
Require Import liblayers.compcertx.LiftMemX.

Require Import Globalenvs.

(** * Types of abstract data *)

(** To use a given [ldata_type] as a layer's abstract data, we need
  the associated initial abstract [init_data], and an invariant
  [data_inv] that hold on the initial data and is to be preserved by
  all primitives.

  Additionally, since the data may contain pointers, we need a
  relation [data_inject] that tells us what it means for one abstract
  state to inject to another, by analogy to Compcert's [Val.inject]
  and friends. It is not yet entierly clear what properties will be
  required of [data_inject] besides [data_inject_compose], but I list
  a few things that make sense.

  You should make use of the [ldata_type] coercion and avoid referring
  to the underlying type directly. This will allow unification to
  recover the [layerdata] record of interest when using the fields
  [init_data], [data_inv], or [data_inject]. *)

Record layerdata :=
  {
    ldata_type :> Type;
    init_data: ldata_type;
    data_inv: ldata_type -> Prop;
    data_inject (f: meminj): relation ldata_type;

    init_data_inv:
      data_inv init_data;
    init_data_inject:
      Monotonic init_data (data_inject (Mem.flat_inj glob_threshold));
    (** May need when [Mem.inject] uses [data_inject] <<<
    data_inject_compose ι ι' d1 d2 d3:
      data_inject ι d1 d2 ->
      data_inject ι' d2 d3 ->
      data_inject (compose_meminj ι ι') d1 d3;
    >>>
    By contrast this is already used for inject-neutral properties: *)
    data_inject_incr:
      Monotonic data_inject (inject_incr ++> subrel);
  }.

Arguments init_data {D} : rename.
Arguments data_inv {D} d : rename.
Arguments data_inject {D} f : rename.

Global Existing Instance data_inject_incr.

Global Instance data_inject_incr_params:
  Params (@data_inject) 3.

Global Existing Instance init_data_inject.

Global Instance init_data_inject_params:
  Params (@init_data) 0.
