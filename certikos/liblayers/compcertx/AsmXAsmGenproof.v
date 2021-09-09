(** * From CompCertX AsmX to LayerLib Asm-style AsmX *)

Require Import compcert.lib.Coqlib.
Require Import compcert.common.Memtype.
Require Import compcert.common.AST.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import liblayers.lib.Decision.
Require Import coqrel.LogicalRelations.
Require Import liblayers.logic.LayerData.
Require Import liblayers.logic.Primitives.
Require Export liblayers.compcertx.CompcertStructures.
Require Import liblayers.compcertx.ErrorMonad.
Require Import liblayers.simrel.AbstractData.
Require Import compcert.x86.Asm.
Require Import compcertx.x86.AsmX.
Require Import SimulationRelation.
Require Import SimAsm.

Require Import AsmPrimitives.
Require Import AsmXAsmSemantics.

Require Import CPrimitives.
Require Import CallConv.

Require Export AsmXAsmGen.


Section BUILTIN_ENABLED_DEC.
  Context `{ec_ops : ExternalCallsOps}.
  Context `{eb: EnableBuiltins}.

  Lemma builtin_enabled_dec (ec : external_function):
    {builtin_enabled ec} + {~ builtin_enabled ec}.
  Proof.
    destruct ec; auto; simpl.
    destruct cc_enable_external_as_builtin; auto.
  Defined.

  Lemma builtin_enabled_erase_sig ef:
    builtin_enabled (erase_sig_external ef) <-> builtin_enabled ef.
  Proof.
    destruct ef; tauto.
  Qed.
End BUILTIN_ENABLED_DEC.


Section WITHASMGENV.
  Context `{Hmem: Mem.MemoryModelX}.

  Context (ge1 ge2: Asm.genv)
          (genv_symbols_preserved: forall i, Genv.find_symbol ge2 i = Genv.find_symbol ge1 i).

  Lemma exec_load_symbols_preserved:
    forall rs m,
    forall chunk a rd,
      exec_load ge2 chunk m a rs rd =
      exec_load ge1 chunk m a rs rd.
  Proof.
    unfold exec_load.
    intros rs m chunk a rd.
    erewrite eval_addrmode64_symbols_preserved by eassumption.
    reflexivity.
  Qed.
  
  Lemma exec_store_symbols_preserved:
    forall rs m,
    forall chunk a rd rl,
      exec_store ge2 chunk m a rs rd rl =
      exec_store ge1 chunk m a rs rd rl.
  Proof.
    unfold exec_store.
    intros rs m chunk a rd rl.
    erewrite eval_addrmode64_symbols_preserved by eassumption.
    reflexivity.
  Qed.

End WITHASMGENV.


Section WITHMEMORYMODEL.
  Context `{Hmem: BaseMemoryModel}.
  Context {D: layerdata}.

  Lemma generalize_external_call ef {F V: Type} (ge: _ F V) args (m: mwd D) t res m' :
    (let ec_ops_x := empty_external_calls_ops_x (D := D) in
    external_call ef ge args m t res m') ->
    forall {EC: CompCertBuiltins.ExternalCallsOpsX (mwd D)},
      external_call ef ge args m t res m'.
  Proof.
    destruct ef; simpl; try tauto.
  Qed.
  
  Lemma generalize_builtin_call (L: clayer D) ef {F V: Type} (ge: _ F V) args (m: mwd D) t res m' :
    (let ec_ops_x := cprimitive_extcall_ops _ L in
     (external_call ef ge args m t res m' /\
      let cc_ops := cprimitive_cc_ops _ L in
      builtin_enabled ef)) ->
    (let ec_ops_x := empty_external_calls_ops_x (D := D) in
     external_call ef ge args m t res m').
  Proof.
    destruct ef; simpl; try tauto.
  Qed.

  (* CompCertX per-module semantics of LayerLib AsmX. *)
  
  Definition AsmXAsm_semantics (L: asmlayer D) lm p i sg args m :=
    Smallstep.Semantics (AsmXAsmSemantics.step L) (AsmX.initial_state lm p i sg args m) (AsmX.final_state lm sg) (Genv.globalenv p).


  (* Forward simulation between CompCertX AsmX and LayerLib AsmX. *)

  Context (Lc: clayer D).

  Lemma builtin_enabled_erase_sig_eq ef:
    (let ec_ops_x := cprimitive_extcall_ops _ Lc in
    let cc_ops := cprimitive_cc_ops _ Lc in
    builtin_enabled ef) ->
    erase_sig_external ef = ef.
  Proof.
    destruct ef; auto.
    contradiction.
  Qed.

  Lemma builtin_enabled_equiv ef:
    (let ec_ops_x := cprimitive_extcall_ops _ Lc in
    let cc_ops := cprimitive_cc_ops _ Lc in
    builtin_enabled ef) <->
    (let ec_ops_x := empty_external_calls_ops_x (D := D) in
     let cc_ops := empty_compiler_config_ops (D := D) in
     builtin_enabled ef).
  Proof.
    destruct ef; tauto.
  Qed.

  Context (Lasm: asmlayer D).

  Hypothesis Lc_to_Lasm:
    forall i prim,
      Layers.get_layer_primitive i Lc = OK (Some prim) ->
      Layers.get_layer_primitive i Lasm = OK (Some (c_to_asm_primitive _ i prim)).

  Variable p: Asm.program.

  Lemma find_funct_ptr_none:
    forall b0 : block,
      Genv.find_funct_ptr (Genv.globalenv (transform_program erase_sig p)) b0 =
      None <->
      Genv.find_funct_ptr (Genv.globalenv p) b0 =
      None.
  Proof.
  Admitted. (*
    intros b0.
    destruct (Genv.find_funct_ptr (Genv.globalenv (transform_program erase_sig p)) b0) eqn:TGT;
      destruct (Genv.find_funct_ptr (Genv.globalenv p) b0) eqn:SRC;
      (try intuition congruence);
      exfalso.
    {
      apply Genv.find_funct_ptr_rev_transf in TGT.
      destruct TGT as (? & ? & ?).
      congruence.
    }
    apply (Genv.find_funct_ptr_transf erase_sig) in SRC.
    congruence.
  Qed.
  *)

  (** To be able to reconcile the fact that the PC has to point to the
     primitive entrypoint in the calling convention wrapper, we have
     to assume that external function names correspond to their
     symbols in the program. *)

  Hypothesis stencil_matches_genv:
    stencil_matches (Genv.globalenv (transform_program erase_sig p)).

  Hypothesis find_external_function:
    forall i b,
      Genv.find_symbol (Genv.globalenv (transform_program erase_sig p)) i = Some b ->
      forall name sig,
        Genv.find_funct_ptr (Genv.globalenv (transform_program erase_sig p)) b =
        Some (AST.External (EF_external name sig)) ->
        name = name_of_ident i.

  Theorem compcertx_to_layerlib_asmx lm i sg args m:
    let ec_ops_x := cprimitive_extcall_ops _ Lc in
    let cc_ops := cprimitive_cc_ops _ Lc in
    Smallstep.forward_simulation
      (AsmX.semantics lm p i sg args m)
      (AsmXAsm_semantics Lasm lm (transform_program erase_sig p) i sg args m).
  Proof.
    intros ec_ops_x cc_ops.
    apply Smallstep.forward_simulation_step with
    (match_states := (Logic.eq : Smallstep.state (AsmX.semantics lm p i sg args m) -> Smallstep.state (AsmXAsm_semantics Lasm lm (transform_program erase_sig p) i sg args m) -> Prop)).
    * (* symbols preserved *)
      simpl.
      admit.
      (*
      apply Genv.find_symbol_transf.
       *)
    * (* initial states *)
      inversion 1; subst.
      esplit.
      split; eauto.
      econstructor; eauto.
      admit.
      (*
      rewrite Genv.find_symbol_transf; eauto.
       *)
    * (* final states *)
      intros s1 s2 r H H0 ; subst; auto.
    * (* step *)
      intros s1 t s1' H s2 H0.
      subst.
      esplit.
      split; eauto.
      inversion H; subst.
    + (* internal *)
      eapply exec_step_asm.
      eapply exec_step_internal.
      - eassumption.
      - simpl.
        admit.
        (*
        rewrite Genv.find_funct_ptr_transf with (f := Internal f); simpl; eauto.
         *)
      - eassumption.
      - admit.
        (*
        erewrite exec_instr_symbols_preserved; simpl; try (eauto || apply Genv.find_symbol_transf ).
        { apply find_funct_ptr_none. }
        { simpl. eapply exec_load_symbols_preserved; eauto.
          apply Genv.find_symbol_transf. }
        { simpl. eapply exec_store_symbols_preserved; eauto.
          apply Genv.find_symbol_transf. }
         *)
    + (* builtin *)      
      (*
      match goal with
          K: external_call' _ _ _ _ _ _ _ |- _ =>
          inversion K; subst
      end.
       *)
      eapply exec_step_asm.
      eapply exec_step_builtin.
      - eassumption.
      - simpl. 
        admit.
        (*
        rewrite Genv.find_funct_ptr_transf with (f := Internal f); simpl; eauto.
         *)
      - eassumption.
      - admit. (* eval_builtin_args *)
      - admit.
        (*
        econstructor; eauto.
        generalize (empty_external_calls_x (D := D)). intro.
        eapply @external_call_symbols_preserved; try typeclasses eauto.
        { eapply @generalize_builtin_call with (L := Lc); eauto. }
        { simpl. apply Genv.find_symbol_transf. }
        { simpl. apply Genv.find_var_info_transf. }
        { simpl. intros. eauto using Genv.find_funct_ptr_transf. }
        { simpl. apply Genv.genv_next_transf. }
         *)
      - assumption.
      - reflexivity.
        (*
    + (* annot *)
      match goal with
          K: external_call' _ _ _ _ _ _ _ |- _ =>
          inversion K; subst
      end.
      eapply exec_step_asm.
      eapply exec_step_annot.
      - eassumption.
      - simpl. 
        rewrite Genv.find_funct_ptr_transf with (f := Internal f); simpl; eauto.
      - eassumption.
      - eassumption.
      - econstructor; eauto.
        generalize (empty_external_calls_x (D := D)). intro.
        eapply @external_call_symbols_preserved; try typeclasses eauto.
        { eapply @generalize_builtin_call with (L := Lc); eauto. }
        { simpl. apply Genv.find_symbol_transf. }
        { simpl. apply Genv.find_var_info_transf. }
        { simpl. intros. eauto using Genv.find_funct_ptr_transf. }
        { simpl. apply Genv.genv_next_transf. }
      - assumption.
*)
    + (* external *)
      (*
      match goal with
          K: external_call' _ _ _ _ _ _ _ |- _ =>
          inversion K; subst
      end.
       *)
      destruct (builtin_enabled_dec ef).
      {
        (* builtin *)
        eapply exec_step_asm.
        eapply exec_step_external.
        - eassumption.
        - simpl.
          admit.
          (*
          match goal with
              K: Genv.find_funct_ptr _  _ = _ |- _ =>
              simpl in K;
                apply (Genv.find_funct_ptr_transf erase_sig p) in K;
                simpl in K
          end.
          eassumption.
           *)
  Admitted.
  (*
        - rewrite builtin_enabled_erase_sig_eq by assumption.
          eassumption.
        - rewrite builtin_enabled_erase_sig_eq by assumption.
          econstructor; eauto.
          generalize (empty_external_calls_x (D := D)). intro.
          eapply @external_call_symbols_preserved; try typeclasses eauto.
          { eapply @generalize_builtin_call with (L := Lc); eauto. }
          { simpl. apply Genv.find_symbol_transf. }
          { simpl. apply Genv.find_var_info_transf. }
          { simpl. intros. eauto using Genv.find_funct_ptr_transf. }
          { simpl. apply Genv.genv_next_transf. }
        - rewrite builtin_enabled_erase_sig_eq by assumption.
          reflexivity.
        - (* new calling convention *)
          rewrite builtin_enabled_erase_sig_eq by assumption.
          destruct STACK as (m_ & FREE & t_ & res'_ & m'_ & EXT_).
          esplit.
          split; eauto.
          inversion EXT_; subst.
          esplit. esplit. esplit.
          econstructor; eauto.
          generalize (empty_external_calls_x (D := D)). intro.
          eapply @external_call_symbols_preserved; try typeclasses eauto.
          { eapply @generalize_builtin_call with (L := Lc); eauto. }
          { simpl. apply Genv.find_symbol_transf. }
          { simpl. apply Genv.find_var_info_transf. }
          { simpl. intros. eauto using Genv.find_funct_ptr_transf. }
          { simpl. apply Genv.genv_next_transf. }
        - assumption.
        - assumption.
      }
      (* true external: switch to the Lasm layer, with the calling convention. *)
      destruct ef; try (exfalso; simpl in * ; tauto).
      match goal with
          K: external_call _ _ _ _ _ _ _ |- _ =>
          destruct K as (_ & prim & csg & Hget & Hprim & Hsig & ? & ?)
      end.
      subst.
      eapply exec_step_primitive; eauto.
      {
        simpl.
        match goal with
            K: Genv.find_funct_ptr _  _ = _ |- _ =>
            simpl in K;
              apply (Genv.find_funct_ptr_transf erase_sig p) in K;
              simpl in K
        end.
        eassumption.
      }
      econstructor; eauto.
      split; auto.
      split.
      { (* block and global environment *)
        simpl in H1.
        apply (Genv.find_funct_ptr_transf erase_sig) in H1.
        generalize H1. intro H1_.
        apply find_funct_ptr_block_is_global in H1_; auto.
        apply block_is_global_find_symbol in H1_.
        destruct H1_ as (symb & Hsymb).
        generalize (stencil_matches_symbols _ stencil_matches_genv symb).
        rewrite Hsymb.
        intro FIND.
        exploit find_external_function; eauto.
        intro; subst; eauto.
      }
      esplit.
      esplit.
      split; eauto.
      split.
      { (* new calling convention:
             protect argument memory locations.
         *)
        destruct STACK as (m_ & FREE & t_ & res'_ & m'_ & EXT_).
        inversion EXT_; subst.
        simpl in H4.
        destruct H4 as (_ & s & sg_ & Hs & STEP & U & Hsg_ & TR).
        assert (s = prim) by congruence.
        subst.
        simpl.
        replace (Ctypes.typlist_of_typelist (csig_args csg))
                with (sig_args (csig_sig csg))
          in *
                       by reflexivity.
        rewrite <- Hsg_ in *.
        eauto 7.
      }
      eauto 6.
  Qed.
*)

End WITHMEMORYMODEL.
