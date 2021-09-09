Require Export liblayers.logic.Modules.
Require Export compcert.x86.Asm.
Require Export liblayers.logic.PTreeModules.
Require Export compcert.common.AST.
Require Export liblayers.compcertx.AsmGlobalVars.

Notation asmmodule := (ptree_module Asm.code (globvar unit)).

Global Instance asmmodule_ops: ModuleOps ident Asm.code (globvar unit) asmmodule :=
  ptree_module_ops.

Global Instance asmmodule_prf: Modules ident Asm.code (globvar unit) asmmodule :=
  ptree_module_prf.

  (* a signature is required for external functions,
     even though it is not used in step *)
  Definition dummy_sig :=
    {| sig_args := nil; sig_res := None; sig_cc := cc_default  |}.
