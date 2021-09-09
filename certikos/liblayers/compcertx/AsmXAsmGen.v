(** * From CompCertX AsmX to LayerLib Asm-style AsmX *)

Require Import compcert.lib.Coqlib.
Require Import compcert.common.AST.
Require Import compcert.common.Events.
Require Import compcert.x86.Asm.

Require Import AsmModules. (* for dummy_sig *)

(* NOTE: we are going to erase the signatures of internal and
  external functions. This way, the actual (LayerLib) module will only
  retain the code, and make_program will just stick in a dummy signature. *)

Definition erase_sig_external (x: external_function): external_function :=
  match x with
    | EF_external i _ => EF_external i dummy_sig
    | _ => x
  end.

Definition erase_sig_internal phi :=
  {| Asm.fn_code := Asm.fn_code phi;
     Asm.fn_sig := dummy_sig |}.

Definition erase_sig (f: Asm.fundef): Asm.fundef :=
  match f with
    | Internal phi => Internal (erase_sig_internal phi)
    | External x => External (erase_sig_external x)
  end.
