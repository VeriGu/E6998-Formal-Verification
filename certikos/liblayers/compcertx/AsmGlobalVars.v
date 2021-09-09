Require Export liblayers.compcertx.CompCertGlobalVars.

Global Instance asm_global_vars_ops:
  CompCertGlobalVarsOps unit.
Proof.
  constructor.
  repeat red.
  decide equality.
Defined.
