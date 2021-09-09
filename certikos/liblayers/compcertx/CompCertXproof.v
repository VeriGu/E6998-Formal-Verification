(** * CompCertX: from LayerLib C-style ClightX to LayerLib Asm-style AsmX *)

Require Import compcert.lib.Coqlib.
Require Import compcert.common.Memtype.
Require Import compcert.common.AST.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import liblayers.lib.Decision.
Require Import liblayers.logic.LayerData.
Require Import liblayers.logic.Primitives.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compcertx.ErrorMonad.
Require Import liblayers.simrel.SimulationRelation.
Require Import liblayers.simrel.AbstractData.
Require Import compcert.x86.Asm.
Require Import compcertx.x86.AsmX.

Require Import AsmPrimitives.
Require Import AsmModules.
Require Import AsmXAsmSemantics.

Require Import CPrimitives.
Require Import ClightModules.
(* Require Import ClightXSemantics. *)

Require Import CallConv.

Require Import SeparateCompiler.
Require Import SeparateCompilerproof.
(* Require Import AsmXAsmGenproof. *)

Require Import liblayers.logic.PTrees.
Require PTreeLayerMap.
Require PTreeModuleMap.

Require Import TransformProgram.

Require Export CompCertX.

(* CompCertX as CompCert-style transform_program. *)

Section WITHRESID.
(* Context `{res_id: I64helpers.ReservedId}. *)

Definition transf_clight_program fenv p :=
  let pr :=
      ComposePasses.apply_partial (OK p) SeparateCompiler.transf_clight_program_to_rtl
  in
  let pa :=
      ComposePasses.apply_partial pr (SeparateCompiler.transf_rtl_program fenv)
  in
  ComposePasses.apply_total pa (transform_program AsmXAsmGen.erase_sig)
.

Definition transf_clight_fundef cenv dm hf fenv :=
  ComposePasses.compose_partial' (SeparateCompiler.transf_clight_fundef' cenv dm hf fenv) (fun i x => OK (AsmXAsmGen.erase_sig x)).

(* Lemma transf_clight_program_to_fundef: *)
(*   forall fenv p tp, *)
(*     transf_clight_program fenv p = OK tp -> *)
(*     exists cenv dm hf,  *)
(*       transform_partial_program2 (transf_clight_fundef cenv dm hf fenv) Cshmgen.transl_globvar p = OK tp. *)
(* Proof. *)
(*   intros fenv p tp H. *)
(*   unfold transf_clight_program in H. *)
(*   repeat apply_elim. *)
(*   assert (transf_clight_program' fenv a1 = OK a) as EQ. *)
(*   { *)
(*     unfold transf_clight_program'. *)
(*     simpl. *)
(*     rewrite Har0. *)
(*     assumption. *)
(*   } *)
(*   apply transf_clight_program_to_fundef' in EQ. *)
(*   unfold transf_clight_fundef. *)
(*   replace (Cshmgen.transl_globvar) with (ComposePasses.compose_partial Cshmgen.transl_globvar (fun v => OK v)) by reflexivity. *)
(*   etransitivity. *)
(*   { *)
(*     eapply ComposePasses.transform_partial_program2_compose_out_in. *)
(*     unfold ComposePasses.compose_partial. *)
(*     simpl. *)
(*     rewrite EQ. *)
(*     simpl. *)
(*     replace ( *)
(*  transform_partial_program2 (fun x : Asm.fundef => OK (erase_sig x)) *)
(*      (fun v : unit => OK v) a *)
(*       ) with ( transform_partial_program (fun x => OK (erase_sig x)) a ) *)
(*                by reflexivity. *)
(*     eapply transform_program_partial_program. *)
(*   } *)
(*   reflexivity. *)
(* Qed. *)

Lemma transf_clight_fundef_to_program:
  forall dm hf fenv (p: program) tp,
     clight_helpers p = OK dm ->
     Selection.get_helpers dm = OK hf ->
     transform_partial_program2 (transf_clight_fundef (prog_comp_env p) dm hf fenv) Cshmgen.transl_globvar p = OK tp ->
     transf_clight_program fenv p = OK tp.
Proof.
  intros dm hf fenv p tp CHELPERS SHELPERS H.
  unfold transf_clight_program.
  replace (Cshmgen.transl_globvar) with (ComposePasses.compose_partial' Cshmgen.transl_globvar (fun i v => OK v)) in H by reflexivity.
  unfold transf_clight_fundef in H.
  apply ComposePasses.transform_partial_program2_compose_in_out in H.  
  unfold ComposePasses.compose_partial in H.
  unfold ComposePasses.apply_partial, ComposePasses.apply_total in * |- * .
  destruct (
      transform_partial_program2 (transf_clight_fundef' (prog_comp_env p) dm hf fenv)
                                 Cshmgen.transl_globvar p
    ) eqn: EQ;
    try discriminate.
  apply transf_clight_fundef_to_program' in EQ; auto.
  unfold transf_clight_program' in EQ.
  unfold ComposePasses.apply_partial in *.
  destruct (transf_clight_program_to_rtl p); try discriminate.
  rewrite EQ.
  generalize (transform_program_partial_program AsmXAsmGen.erase_sig (V := unit) p0).
  unfold transform_partial_program.
  congruence.
Qed.

Close Scope rel.

Theorem transf_clight_fundef_to_function_internal' :
  forall cenv dm hf fenv f x i,
    transf_clight_fundef' cenv dm hf fenv i (Ctypes.Internal f) = OK x ->
    exists tf,
      transf_clight_function' cenv dm hf fenv f = OK tf /\
      x = (AST.Internal tf).
Proof.
  intros.
  unfold transf_clight_fundef', transf_clight_fundef_to_rtl, SeparateCompiler.transf_rtl_fundef in H.
  repeat compose_elim.
  unfold transf_clight_function', transf_clight_function_to_rtl, SeparateCompiler.transf_rtl_function.
  unfold ComposePasses.compose_partial, ComposePasses.apply_partial, ComposePasses.compose_total_right, ComposePasses.apply_total, ComposePasses.apply_partial.
  unfold SelectionX.sel_function, SelectionX.sel_fundef in *.
  unfold CSEX.transf_function, CSEX.transf_fundef in *.
  unfold ConstpropX.transf_function, ConstpropX.transf_fundef in *.
  unfold DeadcodeX.transf_function, DeadcodeX.transf_fundef in *.
  simpl in *.
  monadInv Hab1. rewrite EQ; clear EQ.
  monadInv Hab. rewrite EQ; clear EQ.
  monadInv Hab2. rewrite EQ; clear EQ.
  monadInv Hab3. rewrite EQ; clear EQ.
  monadInv Hab0. rewrite EQ; clear EQ.
  monadInv Hbc4. rewrite EQ; clear EQ.
  monadInv Hbc3. rewrite EQ; clear EQ.
  monadInv Hbc2. rewrite EQ; clear EQ.
  monadInv Hbc1. rewrite EQ; clear EQ.
  monadInv Hbc. rewrite EQ; clear EQ.
  monadInv Hbc0. rewrite EQ; clear EQ.
  eauto.
Qed.

Theorem transf_clight_fundef_to_function_internal :
  forall cenv dm hf fenv f x i,
    transf_clight_fundef cenv dm hf fenv i (Ctypes.Internal f) = OK x ->
    exists tf,
      transf_clight_function cenv dm hf fenv f = OK tf /\
      x = (AST.Internal tf).
Proof.
  unfold transf_clight_fundef, transf_clight_function.
  unfold ComposePasses.compose_partial'.
  unfold ComposePasses.compose_partial.
  unfold ComposePasses.apply_partial.
  intros cenv dm hf fenv f x i H.
  destruct (transf_clight_fundef' cenv dm hf fenv i (Ctypes.Internal f)) eqn:F; try discriminate.
  apply transf_clight_fundef_to_function_internal' in F.
  destruct F as (? & F & ?); subst.
  rewrite F.
  inversion H; subst.
  eauto.
Qed.

Theorem transf_clight_function_to_fundef_internal :
  forall cenv dm hf fenv f tf i,
    transf_clight_function cenv dm hf fenv f = OK tf ->
    transf_clight_fundef cenv dm hf fenv i (Internal f) = OK (AST.Internal tf).
Proof.
  unfold transf_clight_fundef, transf_clight_function.
  unfold ComposePasses.compose_partial.
  unfold ComposePasses.compose_partial'.
  unfold ComposePasses.apply_partial.
  intros cenv dm hf fenv f tf i H.
  destruct (transf_clight_function' cenv dm hf fenv f) eqn:F; try discriminate.
  eapply SeparateCompiler.transf_clight_fundef_internal in F.
  rewrite F.
  simpl.
  inversion H; subst.
  reflexivity.
Qed.

Theorem transf_clight_fundef_external:
  forall cenv dm hf fenv ef tl ty cc i,
    ef_sig ef = Ctypes.signature_of_type tl ty cc ->
    transf_clight_fundef cenv dm hf fenv i (External ef tl ty cc) = OK (AST.External (AsmXAsmGen.erase_sig_external ef)).
Proof.  
  intros cenv dm hf fenv ef tl ty cc i H.
  eapply (SeparateCompiler.transf_clight_fundef_external cenv dm hf fenv) in H.
  unfold transf_clight_fundef.
  unfold ComposePasses.compose_partial'.
  unfold ComposePasses.apply_partial.
  rewrite H.
  eauto.
Qed.

Theorem transf_clight_function_erase :
  forall cenv dm hf fenv f tf,
    transf_clight_function cenv dm hf fenv f = OK tf ->
    AsmXAsmGen.erase_sig_internal tf = tf.
Proof.
  unfold transf_clight_function.
  unfold ComposePasses.compose_partial.
  unfold ComposePasses.apply_partial.
  intros.
  destruct (transf_clight_function' cenv dm hf fenv f); try discriminate.
  inversion H; subst.
  destruct f0; reflexivity.
Qed.

Lemma transf_rtl_function_intro cenv dm hf fenv fc fa:
  transf_clight_function cenv dm hf fenv fc = OK fa ->
  exists fr,
    transf_clight_function_to_rtl cenv dm hf fc = OK fr /\
    transf_rtl_function fenv fr = OK fa.
Proof.
  unfold transf_clight_function, transf_clight_function', transf_rtl_function.
  unfold ComposePasses.compose_partial, ComposePasses.apply_partial.
  intros H.
  destruct (transf_clight_function_to_rtl cenv dm hf fc); try discriminate.
  eauto.
Qed.

End WITHRESID.

Section WITHMEMORYMODEL.
  Context `{Hmem: BaseMemoryModel}.
  Context `{make_program_prf: MakeProgram}.
  (* Context `{res_id: I64helpers.ReservedId}. *)

    (* Properties of layer transformation *)

    (* Here we prove that transf_clight_program is suitably
       per-function. *)

    Variable D: layerdata.
    Variable Lc: clayer D.

    Let convert_primitive_to_program cenv dm hf fenv:
      forall (i: ident) (f: cprimitive D) (f_: Clight.fundef),
        make_external D i f = OK f_ -> 
        forall fto_,
          make_external D i (c_to_asm_primitive D i f) = OK fto_ ->
          transf_clight_fundef cenv dm hf fenv i f_ = OK fto_.
    Proof.
      simpl.
      intros i f f_ H fto_ H0.
      inv_monad H.
      inversion H0; clear H0; subst.
      rewrite transf_clight_fundef_external; auto.
    Qed.

    Let make_varinfo_from_map:
      forall v (v': globvar Ctypes.type),
        make_varinfo v = OK v' ->
        v' = globvar_map Datatypes.id v.
    Proof.
      simpl.
      intros v v' H.
      inversion H; subst.
      destruct v' ; reflexivity.
    Qed.

    Let make_varinfo_to_map:
      forall v (v' : globvar unit),
        make_varinfo v = OK v' ->
        v' = globvar_map Datatypes.id v.
    Proof.
      simpl.
      intros v v' H.
      inversion H; subst.
      destruct v' ; reflexivity.
    Qed.

    Let transf_V_module_to_program:
      forall v,
        Cshmgen.transl_globvar (Datatypes.id v) = OK (Datatypes.id ((fun _ => tt) v)).
    Proof.
      reflexivity.
    Qed.



(* Now, if compilation succeeds, let us connect with make_program. *)
    
    Variable Mc: cmodule.

    Let Masm: asmmodule := compcertx Mc.

    Let fenv := construct_fenv Mc.

    Let Lasm := c_to_asm_layer Lc.

    Let get_module_function_some:
      ModuleOK Masm ->
      forall i ffrom,
        get_module_function i Mc = OK (Some ffrom) ->
        exists fto,
          get_module_function i Masm = OK (Some fto) /\
          exists fp_from,
            make_internal ffrom = OK fp_from /\
            exists fp_to,
              transf_clight_fundef fenv fp_from = OK fp_to /\
              make_internal fto = OK fp_to.
    Proof.
      intros MOK i ffrom H.
      eapply compcertx_function_some in H; eauto.
      destruct H as (fasm & TRANSF & GET).
      unfold Masm.
      setoid_rewrite GET; clear GET.
      simpl.
      esplit.
      split; eauto.
      esplit.
      split; eauto.
      esplit.
      split; eauto using transf_clight_function_to_fundef_internal.
      symmetry.
      apply transf_clight_function_erase in TRANSF.
      rewrite <- TRANSF at 1.
      reflexivity.
    Qed.

    Let get_module_function_none:
      forall i,
        get_module_function i Mc = OK None ->
        get_module_function i Masm = OK None.
    Proof.
      unfold Masm.
      eapply compcertx_function_none; eauto.
    Qed.

    Let get_module_variable_eq:
      forall i ffrom,
        get_module_variable i Mc = OK ffrom ->
        get_module_variable i Masm = OK (option_map (globvar_map (fun _ => tt)) ffrom).
    Proof.
      unfold Masm.
      eapply compcertx_variable_ok; eauto.
    Qed.

    Let get_layer_primitive_eq:
      forall i ffrom,
        get_layer_primitive i Lc = OK ffrom ->
        get_layer_primitive i Lasm = OK (option_map (c_to_asm_primitive D i) ffrom).
    Proof.
      intros i ffrom H.
      generalize (PTreeLayerMap.get_layer_primitive_map (c_to_asm_primitive D) (fun _ => globvar_map (fun _ => tt)) i Lc).
      simpl.
      unfold Lasm, c_to_asm_layer.
      setoid_rewrite H.
      tauto.
    Qed.

    Let get_layer_globalvar_eq:
      forall i ffrom,
        get_layer_globalvar i Lc = OK ffrom ->
        get_layer_globalvar i Lasm = OK (option_map (globvar_map (fun _ => tt)) ffrom).
    Proof.
      intros i ffrom H.
      generalize (PTreeLayerMap.get_layer_globalvar_map (c_to_asm_primitive D) (fun _ => globvar_map (fun _ => tt)) i Lc).
      simpl.
      unfold Lasm, c_to_asm_layer.
      setoid_rewrite H.
      tauto.
    Qed.

(*
    Lemma make_program_from_to_exists: (* USELESS *)
      forall pc,
        make_program _ (Mc, Lc) = OK pc ->
        exists pax,
          make_program _ (Masm, Lasm) = OK pax.
    Proof.
      intros pc pc_exists.
      exact (make_program_from_to_exists _ _ _ _ (convert_primitive_to_program _) _ _ make_varinfo_from_map make_varinfo_to_map transf_V_module_to_program _ _ _ _ get_module_function_some get_module_function_none get_module_variable_eq get_layer_primitive_eq get_layer_globalvar_eq _ pc_exists).
    Qed.
*)

    Let Mfrom_OK_function:
      forall i,
        isError (get_module_function i Mc) ->
        isError (get_module_function i Masm).
    Proof.
      unfold Masm.
      apply compcertx_function_error.
    Qed.

    Let Mfrom_OK_variable:
      forall i,
        isError (get_module_variable i Mc) ->
        isError (get_module_variable i Masm).
    Proof.
      unfold Masm.
      eapply compcertx_variable_error; eauto.
    Qed.

    Let Lfrom_OK_primitive:
      forall i,
        isError (get_layer_primitive i Lc) ->
        isError (get_layer_primitive i Lasm).
    Proof.
      intros i H.
      destruct H as (? & H).
      unfold Lasm, c_to_asm_layer.
      setoid_rewrite PTreeLayerMap.get_layer_primitive_map.
      setoid_rewrite H.
      simpl.
      esplit; eauto.
    Qed.
      
    Let Lfrom_OK_globalvar:
      forall i,
        isError (get_layer_globalvar i Lc) ->
        isError (get_layer_globalvar i Lasm).
    Proof.
      intros i H.
      destruct H as (? & H).
      unfold Lasm, c_to_asm_layer.
      setoid_rewrite PTreeLayerMap.get_layer_globalvar_map.
      setoid_rewrite H.
      simpl.
      esplit; eauto.
    Qed.

    (* Needed by TransformProgram. Indeed, if Mc, Lc contain different
       global variables at one symbol, then make_program will fail on the
       C side, but those variables may be merged to the same global variable
       on the Asm side due to type erasure, thus make_program will succeed
       on the Asm side, hence breaking monotonicity.
     *)
    Hypothesis module_layer_disjoint_c:
      module_layer_disjoint Mc Lc.

    Lemma make_program_to_from_exists:
      forall pax,
        make_program _ (Masm, Lasm) = OK pax ->
        exists pc,
          make_program _ (Mc, Lc) = OK pc.
    Proof.
      intros pasm pasm_exists.
      assert (ModuleOK Masm) as MOK.
      {
          eapply make_program_module_ok.
          esplit.
          eauto.
      }
      exact (make_program_to_from_exists _ _ _ _ (convert_primitive_to_program _) _ _ make_varinfo_from_map make_varinfo_to_map transf_V_module_to_program _ _ _ _ (get_module_function_some MOK) get_module_function_none get_module_variable_eq get_layer_primitive_eq get_layer_globalvar_eq Mfrom_OK_function Mfrom_OK_variable Lfrom_OK_primitive Lfrom_OK_globalvar module_layer_disjoint_c _ pasm_exists).
    Qed.

    Theorem compcertx_syntax:
      forall pc,
        make_program _ (Mc, Lc) = OK pc ->
        forall pax,
          make_program _ (Masm, Lasm) = OK pax ->
          { pr : _ &
                   {fenv : _ &
                             {pa |
                              transf_clight_program_to_rtl pc = OK pr /\
                              transf_rtl_program fenv pr = OK pa /\
                              Inliningspec.fenv_compat (Genv.globalenv pr) fenv /\
                              pax = transform_program AsmXAsmGen.erase_sig pa
                             }
                   }
          }. (* must be in Type because forward_simulation: Type. *)
    Proof.
      intros pc pc_exists pax Hpto.
      assert (ModuleOK Masm) as MOK.
      {
          eapply make_program_module_ok.
          esplit.
          eauto.
      }
      generalize (make_program_transform_partial_program2 _ _ _ _ (convert_primitive_to_program _) _ _ make_varinfo_from_map make_varinfo_to_map transf_V_module_to_program _ _ _ _ (get_module_function_some MOK) get_module_function_none get_module_variable_eq get_layer_primitive_eq get_layer_globalvar_eq _ _ pc_exists Hpto).
      intros H.
      apply transf_clight_fundef_to_program in H.
      unfold transf_clight_program in H.
      unfold ComposePasses.apply_total, ComposePasses.apply_partial in H.
      destruct (transf_clight_program_to_rtl pc) as [ pr | ] eqn:TRANSFC; try discriminate.
      exists pr.
      exists fenv.
      destruct (transf_rtl_program fenv pr) as [ pa | ] ; try discriminate.
      exists pa.
      split; auto.
      split; auto.
      split; try congruence.
      (* fenv_compat *)
      red. intros id b f H0 H1.
      unfold fenv in H0.
      apply construct_fenv_spec in H0.
      destruct H0 as (? & MOD & TRANSF).
      generalize (make_program_make_globalenv _ _ _ pc_exists).
      intros H0.
      exploit @make_globalenv_get_module_function; simpl; eauto.
      destruct 1 as (b_ & SYMB & FUNC).
      apply transf_clight_program_to_rtl_fundef in TRANSFC.
      generalize H1. intro H1_.
      erewrite Genv.find_symbol_transf_partial2 in H1_ by eassumption.
      assert (b_ = b) by congruence.
      subst b_.
      exploit Genv.find_funct_ptr_transf_partial2; eauto.
      destruct 1 as (? & FIND' & TRANSF').
      apply transf_clight_function_to_rtl_internal in TRANSF.
      rewrite FIND'.
      f_equal.
      congruence.
    Qed.

End WITHMEMORYMODEL.


Section CORRECTNESS.

    (** Correctness proof: first port the per-function CompCertX-style
        forward simulation. *)

    Require Import liblayers.compcertx.L64.
    
    Context `{Hmem: Mem.MemoryModelX}.
    Context `{Hmwd: UseMemWithData mem}.
    Context `{make_program_prf: MakeProgram}.
    Context `{res_id: I64helpers.ReservedId}.

    Lemma make_program_l64:
      forall (M: ClightModules.cmodule) D L x,
        make_program D (M, L) = ret x ->
        L64 ≤ L ->
        ClightI64helpers.genv_contains_helpers I64helpers.hf (Genv.globalenv x)
    .
    Proof.

      Ltac t Heq := 
        let Hle := fresh "Hle" in
        destruct Heq as [ Heq | Hle ] ;
          [ inv Heq; simpl in *; now eauto 7 | ];
          try contradiction;
          t Hle.

      unfold L64.
      Opaque I64helpers.hf.
      intros M D L x H H0.
      unfold ClightI64helpers.genv_contains_helpers.
      generalize (make_program_make_globalenv _ _ _ H).
      clear H.
      generalize (Genv.globalenv x). clear x.
      intros ge Hge.
      assert (HM: M ≤ M) by reflexivity.
      pose proof (make_globalenv_monotonic D (_,_) (_,_) (conj HM H0)) as Hge1.
      clear H0.
      rewrite Hge in Hge1.
      clear Hge.
      inversion Hge1 as [ge' ? Hge HMAKE |]; clear Hge1; subst.
      symmetry in HMAKE.
      generalize (make_globalenv_split_module_layer _ _ _ HMAKE). clear HMAKE.
      destruct 1 as (_ & geL & _ & (HgeL & HgeLle')).
      rewrite Hge in HgeLle'.
      clear ge' Hge.
      inv_make_globalenv_split_layer inv_make_globalenv_leaftac HgeL HgeLle' .
      intros until sg. intro Hle.
      Local Transparent unique_element. simpl in *. Local Opaque unique_element.
      t Hle.
    Qed. (* Finished transaction in 183. secs (182.866494u,0.004165s) *)

    Lemma make_globalenv_valid:
      forall (M: ClightModules.cmodule) D L x,
        make_program D (M, L) = ret x ->
        L64 ≤ L ->
        SelectLongproofX.genv_valid (Genv.globalenv x).
    Proof.
      intros M D L x H H0.
      apply make_program_make_globalenv in H.
      red.
      simpl.
      eapply make_globalenv_stencil_matches; eauto.
    Qed.


    (** Requirements of value analysis (CSE, constant propagation, dead code elimination) *)
    Context `{mmatch_ops: !ValueDomain.MMatchOps mem}.
    Context `{mmatch_constructions_prf: !ValueAnalysis.MMatchConstructions mem}.

    (** Requirements of dead code elimination *)
    Context `{magree_ops: !Deadcodeproof.MAgreeOps mem} `{magree_prf: !Deadcodeproof.MAgree mem}.

    (** For external calls. *)
    Context `{builtin_idents_norepet_prf: !CompCertBuiltins.BuiltinIdentsNorepet}.


    Variable D: layerdata.

    Require Import liblayers.compcertx.LiftMem.

    Require Import liblayers.compcertx.LiftValueDomain.
    Require Import liblayers.compcertx.LiftValueAnalysis.
    Require Import liblayers.compcertx.LiftDeadcodeproof.

    (** TODO: why is this necessary? *)
    Local Existing Instance mwd_liftmem_prf.

    Variable Lc: clayer D.

    Let Lasm := c_to_asm_layer Lc.

    Local Instance ec_ops_x: CompCertBuiltins.ExternalCallsOpsX (mwd D) :=
      cprimitive_extcall_ops _ Lc.
    Local Existing Instance CompCertBuiltins.external_calls_ops_x_to_external_calls_ops.
    Local Existing Instance cprimitive_cc_ops.

    Hypothesis ec_prf: ExternalCalls (mwd D).

    Local Instance cc_prf: CompilerConfiguration (mwd D).
    Proof.
      constructor; typeclasses eauto.
    Qed.

    Hypothesis L64_le_Lc: L64 ≤ Lc.

    Variable Mc: cmodule.
    Let Masm: asmmodule := compcertx Mc.

    Section WITHPROGRAMS.

    Variable pc: Clight.program.
    Hypothesis make_c_program: make_program _ (Mc, Lc) = OK pc.

    Local Instance Lc_OK: LayerOK Lc.
    Proof.
      intro i.
      generalize (make_program_noconflict _ _ _ _ i make_c_program).
      intros H.
      constructor; inversion H; subst; auto.
    Qed.

    Local Instance i64_helpers:
      SelectLongproofX.ExternalCallI64Helpers
        external_functions_sem I64helpers.hf.
    Proof.
      apply L64_correct; auto; typeclasses eauto.
    Qed.

    Variable pasm: Asm.program.
    Hypothesis make_asm_program: make_program _ (Masm, Lasm) = OK pasm.

    Theorem compcertx_forward_simulation
         (m: mwd D) init_asm_rs
         (ASM_INVARIANT: AsmX.asm_invariant (Genv.globalenv pasm) init_asm_rs m)

         (** Arguments and so on, given by the local condition on Asm external call *)
         args sg
         (EXTCALL_ARGS: Asm.extcall_arguments init_asm_rs m sg args)
         i b
         (Hsymb:  Genv.find_symbol (Genv.globalenv pasm) i = Some b)
         (PC_VAL: init_asm_rs PC = Values.Vptr b Integers.Int.zero)
         (SP_NOT_VUNDEF: init_asm_rs ESP <> Vundef)
         (RA_NOT_VUNDEF: init_asm_rs RA <> Vundef)

         (* The C program has to be safe on the memory without arguments *)
         mh
         (FREE_ARGS: EraseArgs.free_extcall_args (init_asm_rs ESP) m (Conventions1.loc_arguments sg) = Some mh)
         (SAFE: BehaviorsX.strongly_safe (SmallstepX.semantics_as_asm (ClightX.csemantics pc i mh) sg args))
    :
      forward_simulation
        (SmallstepX.semantics_as_asm (ClightX.csemantics pc i m) sg args)
        (SmallstepX.semantics_with_inject (AsmXAsm_semantics Lasm init_asm_rs pasm i sg args m) m).

    Proof.

      generalize (compcertx_syntax _ _ _ _ make_c_program _ make_asm_program).
      destruct 1 as (pr & fenv & pa & TRANSF_C & TRANSF_RTL & FENV & Hpasm).

      assert (asm_invariant (Genv.globalenv pa) init_asm_rs m) as ASM_INVARIANT_.
      {
        inversion ASM_INVARIANT; subst.
        rewrite Genv.find_symbol_transf in Hsymb.
        inversion inv_inject_neutral.
        rewrite Genv.genv_next_transf in inv_mem_valid.
        split; auto.
        constructor; auto.
      }

      assert (Genv.find_symbol (Genv.globalenv pa) i = Some b) as Hsymb_.
      {
        subst.
        rewrite Genv.find_symbol_transf in Hsymb.
        assumption.
      }

      generalize (SeparateCompilerproof.transf_clight_program_correct
      _ _ TRANSF_C _ FENV (make_program_l64 _ _ _ _ make_c_program L64_le_Lc)
        (make_globalenv_valid _ _ _ _ make_c_program L64_le_Lc)
      _ TRANSF_RTL _ _ ASM_INVARIANT_ _ _ EXTCALL_ARGS
      _ _ Hsymb_ PC_VAL SP_NOT_VUNDEF RA_NOT_VUNDEF
      _ FREE_ARGS SAFE).

      intro S1.

      assert (forall i prim,
                get_layer_primitive i Lc = OK (Some prim) ->
                get_layer_primitive i Lasm = OK (Some (c_to_asm_primitive _ i prim)))
        as HLasm.
      {
        intros i0 prim H.
        unfold Lasm.
        unfold c_to_asm_layer.
        setoid_rewrite PTreeLayerMap.get_layer_primitive_map.
        setoid_rewrite H.
        reflexivity.
      }

      generalize (make_globalenv_stencil_matches _ _ _ (make_program_make_globalenv _ _ _ make_asm_program)).
      intro MATCHES. rewrite Hpasm in MATCHES.

      assert (
        forall i b,
          Genv.find_symbol (Genv.globalenv (transform_program erase_sig pa)) i = Some b ->
          forall name sig,
            Genv.find_funct_ptr (Genv.globalenv (transform_program erase_sig pa)) b =
            Some (AST.External (EF_external name sig)) ->
            name = i
        ) as FIND_EXT.
      {
        intros i0 b0 H name sig H0.
        rewrite <- Hpasm in H, H0.
        generalize (make_globalenv_find_funct_ptr _ _ _ _ _ (make_program_make_globalenv _ _ _ make_asm_program) H0).
        destruct 1 as (symb & SYMB & ALT).
        assert (symb = i0).
        {
          destruct (peq symb i0); auto.
          exfalso.
          eapply Genv.global_addresses_distinct; eauto.
        }
        subst symb.
        destruct ALT as [ (? & ? & ?) | (? & ? & EXT) ] ; try discriminate.
        inversion EXT.
        congruence.
      }

      generalize (compcertx_to_layerlib_asmx _ _  HLasm _ MATCHES FIND_EXT init_asm_rs i sg args m).
      simpl.
      intros S2.

      eapply compose_forward_simulation.
      {
        eexact S1.
      }

      apply SmallstepX.forward_simulation_inject.
      subst pasm.
      assumption.

    Qed.

    End WITHPROGRAMS.

    Require SimValuesInject.
    Local Coercion SimValuesInject.simrel_inject_meminj:
      SimValuesInject.simrel_inject_world >-> Funclass.

    Lemma flat_inj_exists b_ rs m d:
      asmprim_inv b_ D rs m d ->
      { j |
        SimValuesInject.simrel_inject_match_mem j (m, d) (m, d) /\
        Mem.flat_inj (Mem.nextblock (m, d)) = j }.
    Proof.
      intros H.
      inversion H.
      apply SimValuesInject.neutral_inject; auto.
      Local Transparent block_is_global.
      unfold block_is_global.
      intros b H0.
      unfold Mem.flat_inj.
      destruct (plt b (Mem.nextblock m)); auto.
      xomega.
    Qed.

    Lemma determinate_c_to_asm (csem: SmallstepX.csemantics (mem := mwd D)) sg args:
      determinate (SmallstepX.semantics_as_c csem sg (decode_longs (sig_args sg) args)) ->
      determinate (SmallstepX.semantics_as_asm csem sg args).
    Proof.
      inversion 1.
      split; auto.
      { (* initial state *)
        intros s1 s2 H0 H1.
        inversion H0.
        inversion H1.
        apply sd_initial_determ; simpl in * ; auto.
      }
      { (* final nostep *)
        intros s r H0.
        inversion H0; subst; eauto.
      }
      {
        (* final determ *)
        intros s r1 r2 H0 H1.
        inversion H0; subst.
        inversion H1; subst.
        assert ((v, m) = (v0, m0)) as K by eauto.
        congruence.
      }
    Qed.

    Lemma determinate_strongly_safe_state {RET} (S: Smallstep.semantics RET):
      determinate S ->
      forall s t0 v,
        Behaviors.state_behaves S s (Behaviors.Terminates t0 v) ->
        t0 = E0 ->
        forall t,
          Behaviors.state_behaves S s (Behaviors.Goes_wrong t) ->
          False.
    Proof.
      intros H s t0 v H0 H1 t H2.
      revert H1.
      inversion H0; clear H0; subst.
      inversion H2; clear H2; subst.
      revert v H5 s'0 t H1 H3 H6.
      induction H4.
      {
        intros v H5 s'0 t H1 H3 H6 H0.
        inversion H1; subst.
        {
          edestruct H6; eauto.
        }
        edestruct sd_final_nostep; eauto.
      }
      intros v H5 s'0 t0 H2 H3 H6 H7.
      subst.
      apply Eapp_E0_inv in H7.
      destruct H7; subst.
      inversion H2; subst.
      {
        edestruct H3; eauto.
      }
      exploit sd_determ.
      { eassumption. }
      { eexact H0. }
      { eexact H1. }
      destruct 1 as (MATCH & EQ).
      inversion MATCH; subst.
      specialize (EQ Logic.eq_refl).
      subst.
      eauto.
    Qed.

    Lemma determinate_strongly_safe {RET} (S: Smallstep.semantics RET):
      determinate S ->
      forall v,
        Behaviors.program_behaves S (Behaviors.Terminates E0 v) ->
        forall t,
          Behaviors.program_behaves S (Behaviors.Goes_wrong t) ->
          False.
    Proof.
      inversion 2; subst.
      inversion 1; subst.
      {
        exploit sd_initial_determ.
        { eassumption. }
        { eexact H1. }
        { eexact H4. }
        intro; subst.
        eapply determinate_strongly_safe_state; eauto.
      }
      edestruct H5; eauto.
    Qed.

    Lemma star_plus:
      forall {genv state: Type}
             {step: genv -> state -> trace -> state -> Prop}
             ge s t s',
        star step ge s t s' ->
        s <> s' ->
        plus step ge s t s'.
    Proof.
      inversion 1; subst.
      destruct 1; reflexivity.
      intros. econstructor; eauto.
    Qed.

    (* Slightly easier lemmas to handle set_reg, set_regs, undef_regs, val_inject. *)

    Lemma set_reg_inject_both j i i' rs rs' v v':
      (i' = i -> val_inject j v v') ->
      (i' <> i -> val_inject j (rs i') (rs' i')) ->
      val_inject j ((rs # i <- v) i') ((rs' # i <- v') i').
    Proof.
      intros H H0.
      generalize Pregmap.gsspec.
      unfold Pregmap.get.
      intro K.
      repeat rewrite K.
      destruct Pregmap.elt_eq; auto.
    Qed.

    Lemma set_reg_inject_left j i i' rs rs' v:
      (val_inject j v (rs' i)) ->
      (i' <> i -> val_inject j (rs i') (rs' i')) ->
      val_inject j ((rs # i <- v) i') (rs' i').
    Proof.
      intros H H0.
      generalize Pregmap.gsspec.
      unfold Pregmap.get.
      intro K.
      repeat rewrite K.
      destruct Pregmap.elt_eq; auto.
      subst; auto.
    Qed.

    Lemma set_regs_inject_left j l:
      forall vl i' rs rs',
        val_list_inject j vl (List.map rs' l) ->
        ((~ In i' l) -> val_inject j (rs i') (rs' i')) ->
        val_inject j (set_regs l vl rs i') (rs' i').
    Proof.
      induction l; simpl; auto.
      inversion 1; subst.
      intros.
      simpl in IHl.
      apply IHl; auto.
      intro.
      apply set_reg_inject_left; auto.
      intros H2.
      intuition congruence.
    Qed.

    Lemma undef_reg_inject j i i' rs rs':
      (i' <> i -> val_inject j (rs i') (rs' i')) ->
       val_inject j ((rs # i <- Vundef) i') (rs' i').
    Proof.
      intros H.
      generalize Pregmap.gsspec.
      unfold Pregmap.get.
      intro K.
      repeat rewrite K.
      destruct Pregmap.elt_eq; auto.
    Qed.

    Lemma undef_regs_inject j l:
      forall i' rs rs',
        ((~ In i' l) -> val_inject j (rs i') (rs' i')) ->
        val_inject j (undef_regs l rs i') (rs' i').
    Proof.
      induction l; simpl; auto.
      intros i' rs rs' H.
      apply IHl; auto.
      intros H0.
      apply undef_reg_inject.
      revert H H0.
      clear.
      intuition congruence.
    Qed.

    (* BEGIN Taken from SimAsm *)

    Ltac in_open_list :=
      lazymatch goal with
    | |- In _ (_ :: _) =>
      apply in_cons; in_open_list
    | |- In _ ?l =>
      is_evar l; apply in_eq
    end.

    Lemma mreg_enum_exists:
      { l | forall r: Machregs.mreg, In r l }.
    Proof.
      esplit.
      intro r.
      destruct r; in_open_list.
      Grab Existential Variables.
      exact nil.
    Defined.

    (* END Taken from SimAsm *)

    Definition mreg_enum := let (l, _) := mreg_enum_exists in l.

    Lemma mreg_enum_correct: forall r, In r mreg_enum.
    Proof.
      unfold mreg_enum.
      destruct mreg_enum_exists.
      assumption.
    Qed.

    Lemma mreg_not_forall_exists (P: Machregs.mreg -> Prop):
      (forall r, P r \/ ~ P r) ->
      (~ forall r, ~ P r) ->
      exists r, P r.
    Proof.
      intros H H0.
      destruct mreg_enum_exists as (l & Hl).
      cut (forall l2 l1, l = l1 ++ l2 -> (forall x, In x l1 -> ~ P x) -> exists r : Machregs.mreg, P r).
      {
        intros H1.
        apply (H1 l nil).
        + reflexivity.
        + tauto.
      }
      induction l2 as [ | a l2 ]; simpl.
      {
        intros l1 H1 H2.
        subst.
        rewrite <- app_nil_end in Hl.
        destruct H0.
        auto.
      }
      intros l1 H1 H2.
      destruct (H a); eauto.
      eapply (IHl2 (l1 ++ a :: nil)).
      + rewrite app_ass. assumption.
      + intros x. rewrite in_app. simpl.
        destruct 1 as [ | U ] ; auto.
        destruct U; subst; auto.
    Qed.

    Fixpoint lforall {A: Type} (P: A -> Prop) (l: list A) : Prop :=
      match l with
        | nil => True
        | a :: q => P a /\ lforall P q
      end.

    Lemma lforall_complete {A: Type} (P: A -> Prop) (l: list A):
      (forall a, In a l -> P a) ->
      lforall P l.
    Proof.
      induction l; simpl; auto.
    Qed.

    Lemma lforall_mreg_complete (P: _ -> Prop):
      (forall r, P r) ->
      lforall P mreg_enum.
    Proof.
      intros H.
      apply lforall_complete.
      intros a H0.
      apply H.
    Qed.

    Lemma destroyed_regs_correct u:
      u <> PC ->
      u <> RA ->
      ~ In u callconv_destroyed_regs ->
      u = ESP \/
      exists r,
        u = preg_of r /\
        ~ In r Conventions1.destroyed_at_call.
    Proof.
      intros H H0 H1.
      destruct (PregEq.eq u ESP) as [ | NEQ ]; auto.
      right.
      apply mreg_not_forall_exists.
      + intros.
        destruct (PregEq.eq u (preg_of r)).
        - destruct (in_dec Machregs.mreg_eq r (Conventions1.destroyed_at_call)); auto.
          right.
          intros [ A  B ].
          contradiction.
        - right.
          intros [ A B ].
          contradiction.
      + intro ABSURD. 
        apply lforall_mreg_complete in ABSURD.
        revert NEQ H H0 H1 ABSURD.
        simpl.
        clear.
        destruct u as [ | [ ] | [ ] | | [ ] | ]; intuition congruence.
    Qed.

    Hypothesis Lc_stable_INV: sim inv Lc Lc.
    Hypothesis Lc_stable_INJ: sim inj Lc Lc.

    (* Needed by TransformProgram. Indeed, if Mc, Lc contain different
       global variables at one symbol, then make_program will fail on the
       C side, but those variables may be merged to the same global variable
       on the Asm side due to type erasure, thus make_program will succeed
       on the Asm side, hence breaking monotonicity.
     *)
    Hypothesis module_layer_disjoint_c:
      module_layer_disjoint Mc Lc.

    Local Opaque Conventions1.destroyed_at_call.

    Theorem compcertx_module_correctness:
      sim (inj ∘ inv) ( c_to_asm_layer ( 〚 Mc 〛 Lc ))  ( 〚 Masm 〛 Lasm ).
    Proof.
      apply PTreeLayers.ptree_layer_pointwise_sim.
      { (* primitives *)
        intros i.
        unfold c_to_asm_layer.
        rewrite (PTreeLayerMap.get_layer_primitive_map (c_to_asm_primitive D) (fun _ => globvar_map (fun _ => tt))).
        rewrite Semantics.get_semof_primitive.
        rewrite Semantics.get_semof_primitive.
        destruct (get_module_function i Mc) as [ [ fc | ] | ] eqn:Fc.
        { (* some function *)
          destruct (get_module_function i Masm) as [ [ fasm | ] | ] eqn:Fasm.
          {
          unfold Semantics.semof_function.
          monad_norm.
          unfold Semantics.semof_fundef.
          unfold clight_function_semantics_ops.
          unfold asm_function_semantics_ops.
          monad_norm.
          destruct (make_globalenv D (Masm, Lasm)) as [ ge_asm | ] eqn:Gasm.
          { (* target make program exists *)
            generalize (make_globalenv_make_program _ _ Gasm).
            destruct 1 as (pasm & Pasm).
            generalize (make_program_make_globalenv _ _ _ Pasm).
            intro geasm.
            assert (ge_asm = Genv.globalenv pasm).
            {
              rewrite Gasm in geasm.
              inversion geasm.
              congruence.
            }
            subst ge_asm.
            clear Gasm.
            generalize (make_program_to_from_exists _ _ _ module_layer_disjoint_c  _ Pasm).
            destruct 1 as (pc & Pc).
            generalize (make_program_make_globalenv _ _ _ Pc).
            intro gec.
            rewrite gec.
            monad_norm.
            assert (get_layer_primitive i Lc = OK None) as Hprim_c_none.
            {
              exploit (fun K => make_program_module_layer_disjoint Mc Lc K i).
              { rewrite Pc. red; eauto. }
              revert Fc.
              clear.
              intro EQ.
              rewrite EQ.
              inversion 1; congruence.
            }
            unfold clayer_ops in Hprim_c_none |- *.
            rewrite Hprim_c_none.
            assert (get_layer_primitive i Lasm = OK None) as Hprim_asm_none.
            {
              unfold Lasm.
              unfold c_to_asm_layer.
              unfold clayer_ops, asmlayer_ops.
              rewrite (PTreeLayerMap.get_layer_primitive_map (c_to_asm_primitive D) (fun _ => globvar_map (fun _ => tt))).
              rewrite Hprim_c_none.
              reflexivity.
            }
            rewrite Hprim_asm_none.
            simpl.
            monad_norm.
            constructor.
            constructor.
            apply asmprim_sim_step_weak.
            {
              intros [cinv c] [rs1 [m1 d1]] [rs2 [m2 d2]] H.
              rewrite asmprim_match_state_compose in H.
              destruct H as ([rs1_inv [m1_inv d1_inv]] & Hinv & H).
              generalize (inv_asmprim_inv _ _ _ _ _ _ Hinv).
              destruct 1 as (INV & _ & EQ).
              symmetry in EQ.
              inversion EQ; clear EQ; subst.
              intros a asm_source.
              inversion H as (Hrs & Hmd).
              destruct (flat_inj_exists _ _ _ _ INV) as (jflat & Hjflat_inj & Hjflat_eq).
              cut (exists b1,
                     asmprimitive_step D (asm_asmprimitive D Lasm (Genv.globalenv pasm) fasm) (rs1, (m1, d1)) b1 /\ exists x, SimValuesInject.simrel_inject_acc jflat x /\ asmprim_match_state_weak D D inj x a b1).
              {
                intros (b1 & STEP1 & FINAL1).
                assert (exists b,
                     asmprimitive_step D (asm_asmprimitive D Lasm (Genv.globalenv pasm) fasm) (rs2, (m2, d2)) b /\ exists x0, SimValuesInject.simrel_inject_acc c x0 /\ asmprim_match_state D D inj x0 b1 b) as BYINJ.
                {
                  pose (MLasm := 〚 Masm 〛 (c_to_asm_layer Lc)).
                  assert (sim inj MLasm MLasm) as Minj.
                  {
                    unfold MLasm.
                    (* solve_monotonic idtac. # loops forever, maybe because layer_sim_module_layer_sim is not handled properly. *)
                    apply Semantics.semof_monotonic.
                    apply Semantics.layer_sim_module_layer_sim.
                    split.
                    {
                      simpl.
                      solve_monotonic.
                    }
                    split.
                    {
                      unfold snd.
                      solve_monotonic.
                    }
                    (* layer_wf *) exact I.
                  }
                  generalize (get_layer_primitive_sim_monotonic (Layers := asmlayer_prf) _ _ _ i _ _ Minj).
                  clear Minj.
                  unfold MLasm.
                  clear MLasm.
                  rewrite Semantics.get_semof_primitive.
                  unfold asmmodule_ops in Fasm |- *.
                  rewrite Fasm.
                  unfold Semantics.semof_function.
                  monad_norm.
                  unfold Semantics.semof_fundef.
                  simpl.
                  fold Lasm.
                  rewrite geasm.
                  monad_norm.
                  rewrite Hprim_asm_none.
                  intro Minj.
                  inversion Minj as [ u v K | ]; clear Minj; subst u v.
                  inversion K as [ | u v SIM ] ; clear K; subst u v.
                  apply (asmprim_sim_step _ _ _ _ _ SIM _ _ _ H _ STEP1).
                }
                destruct BYINJ as (b & ASM & MATCH).
                esplit.
                split; eauto.
                destruct FINAL1 as [x [Hx_le a_incr_b1]].
                destruct MATCH as [x0 [Hx0_le b1_incr_b]].
                assert (SimValuesInject.compose_meminj jflat c = c) as COMPOSE_EQ.
                {
                  inversion b1_incr_b.
                  eapply (SimValuesInject.flat_inj_compose (mem := mwd D)); eauto.
                }
                rewrite <- COMPOSE_EQ.
                assert (exists cinv', le (Le := simrel_acc (inv_ops D)) cinv cinv' /\ asmprim_match_state D D inv cinv' a a)
                       as INV'.
                {
                  assert ( res_le (option_le (sim inv)) (get_layer_primitive i (c_to_asm_layer ( 〚 Mc 〛 Lc ))) (get_layer_primitive i (c_to_asm_layer ( 〚 Mc 〛 Lc )))) as Minv
                  . (* by solve_monotonic. # loops forever, maybe because layer_sim_module_layer_sim is not handled properly. *)
                  {
                    apply get_layer_primitive_sim_monotonic.
                    apply c_to_asm_layer_monotonic.
                    apply Semantics.semof_monotonic.
                    apply Semantics.layer_sim_module_layer_sim.
                    split.
                    {
                      simpl. solve_monotonic.
                    }
                    split.
                    {
                      assumption.
                    }
                    exact I.
                  }
                  unfold c_to_asm_layer in Minv.
                  generalize (PTreeLayerMap.get_layer_primitive_map (c_to_asm_primitive D) (fun _ => globvar_map (fun _: type => tt)) i ( 〚 Mc 〛 Lc )).
                  revert Minv.
                  unfold clayer_ops, asmlayer_ops.
                  intros Minv H0.
                  rewrite H0 in Minv.
                  clear H0.
                  rewrite Semantics.get_semof_primitive in Minv.
                  rewrite Fc in Minv.
                  unfold Semantics.semof_function in Minv.
                  revert Minv.
                  monad_norm.
                  unfold Semantics.semof_fundef.
                  unfold clight_function_semantics_ops.
                  rewrite gec.
                  unfold clayer_ops.
                  rewrite Hprim_c_none.
                  monad_norm.
                  intro U.
                  simpl in U.
                  monad_norm.
                  inversion U as [ u v K | ]; clear U; subst u v.
                  inversion K as [ | u v SIM ] ; clear K; subst u v.
                  generalize (asmprim_sim_step _ _ _ _ _ SIM _ _ _ Hinv _ asm_source).
                  destruct 1 as (a0 & _ & cinv' & cinv_incr & Hinv').
                  destruct a as [? [? ?]].
                  generalize (inv_asmprim_inv _ _ _ _ _ _ Hinv').
                  destruct 1 as (_ & _ & ?).
                  subst a0.
                  eauto.
                }
                destruct INV' as (cinv' & INV'_le & INV').
                exists (cinv', SimValuesInject.compose_meminj x x0).
                split.
                {
                  split; auto.
                  inversion a_incr_b1.
                  inversion b1_incr_b.
                  eapply (SimValuesInject.compose_meminj_incr (mem := mwd D)); eauto.
                }
                inversion a_incr_b1 as [a_incr_b1_reg a_incr_b1_mem].
                inversion b1_incr_b as [b1_incr_b_reg b1_incr_b_mem].
                split.
                {
                  rewrite SimAsm.regset_match_compose.
                  exists (fst a).
                  split.
                  {
                    inversion INV'.
                    solve_monotonic.
                  }
                  repeat red in a_incr_b1_reg, b1_incr_b_reg |- * .
                  simpl in a_incr_b1_reg, b1_incr_b_reg |- * .
                  generalize (fun v => SimValues.match_val_erase_type _ _ _ _ _ (b1_incr_b_reg v)).
                  clear b1_incr_b_reg. intro b1_incr_b_reg. simpl in b1_incr_b_reg.
                  rewrite SimValuesInject.match_val_simrel_inject in a_incr_b1_reg, b1_incr_b_reg |- * .
                  intros a0.
                  rewrite <- SimValuesInject.compose_meminj_correct.
                  eapply val_inject_compose; eauto.
                }
                exists (snd a).
                split.
                {
                  inversion INV'.
                  assumption.
                }
                simpl.
                eapply (SimValuesInject.inject_compose (mem := mwd D)); eauto.
              }
              (* NOW transform the CompCert-style forward simulation *)
              clear Hinv H Hrs Hmd.
              simpl in asm_source.
              destruct a as [rs' m'].
              destruct asm_source as
                  (SP_NOT_VUNDEF & RA_NOT_VUNDEF &
                   (b & SYMB & HPC) &
                   sg & vargs_asm & ARGS &
                   (csg_c & Hcsg_c & Hsg_c & m_c & FREE & res_c & GUARD) &
                   csg & Hcsg & Hsg &
                   v' & SOURCE & SOURCE_RS).
              subst sg.
              destruct Hcsg_c; subst; try contradiction.
              destruct Hcsg; subst; try contradiction.
              clear Hsg.
              inversion SOURCE as [vargs m vres m'0 sg Hsg PLUS_C].
              subst vargs m vres m'0.
              subst sg.
              clear Hsg.
              assert (asm_invariant (Genv.globalenv pasm) rs1 (m1, d1)) as INVARIANT.
              {
                inversion INV.
                constructor; auto.
                constructor; auto.
                (* TODO: rephrase asmprim_inv_valid using block_is_global instead. *)
                apply make_globalenv_stencil_matches in geasm.
                inversion geasm; subst.
                simpl.
                lift_unfold.
                congruence.
              }
              rewrite <- (stencil_matches_symbols _ (make_globalenv_stencil_matches _ _ _ geasm)) in SYMB.
              generalize (determinate_c_to_asm _ (csig_sig (clight_cprimitive_csig fc)) vargs_asm (ClightX.csemantics_determinate pc i m_c _ _)).
              intro DETERM.

              generalize (make_globalenv_get_module_function _ _ _ _ _ _ gec Fc Logic.eq_refl).
              destruct 1 as (bc & SYMBC & FUNCTC).

              assert (exists vm, Behaviors.program_behaves (SmallstepX.semantics_as_asm (ClightX.csemantics pc i m_c)
         (csig_sig (clight_cprimitive_csig fc)) vargs_asm) (Behaviors.Terminates E0 vm)) as (vm & TERM).
              {
                clear PLUS_C.
                inversion GUARD as [vargs m vres m'0 PLUS_C].
                subst vargs m res_c.
                esplit.
                econstructor.
                {
                  econstructor.
                  econstructor; eauto; reflexivity.
                }
                econstructor.
                {
                  eapply plus_star.
                  eassumption.
                }
                econstructor; eauto.
                econstructor; eauto.
              }

              assert (BehaviorsX.strongly_safe
                        (SmallstepX.semantics_as_asm (ClightX.csemantics pc i m_c)
                                                     (csig_sig (clight_cprimitive_csig fc)) vargs_asm))
                     as SAFE.
              {
                red. intro ABSURD.
                destruct ABSURD as (? & STUCK).
                eapply determinate_strongly_safe; eauto.
              }

              generalize (compcertx_forward_simulation _ Pc _ Pasm _ _ INVARIANT
                                                       _ _ ARGS
                                                       _ _ SYMB HPC
                                                       SP_NOT_VUNDEF RA_NOT_VUNDEF
                                                       _ FREE SAFE).
              intro FS.

              clear TERM.
              assert (Behaviors.program_behaves (SmallstepX.semantics_as_asm (ClightX.csemantics pc i (m1,d1))
         (csig_sig (clight_cprimitive_csig fc)) vargs_asm) (Behaviors.Terminates E0 (encode_long (sig_res (csig_sig (clight_cprimitive_csig fc))) v', m')))
                       as TERM.
              {
                econstructor.
                {
                  econstructor; eauto.
                  econstructor; eauto; reflexivity.
                }
                econstructor.
                {
                  apply plus_star.
                  eassumption.
                }
                econstructor; eauto.
                econstructor; eauto.
              }

              generalize (make_globalenv_get_module_function _ _ _ _ _ _ geasm Fasm Logic.eq_refl).
              destruct 1 as (basm & SYMBASM & FUNCTASM).

              generalize (Behaviors.forward_simulation_behavior_improves FS TERM).
              destruct 1 as (beh & TERMASM & IMPROVES).
              simpl in IMPROVES.
              destruct IMPROVES.
              {
                subst beh.
                inversion TERMASM.
                subst beh.
                inversion H0.
                subst t r.
                inversion H.
                subst s.
                assert (b0 = b) by congruence.
                assert (basm = b) by congruence.
                subst b0 basm.
                inversion H4.
                subst v m.
                inversion Hfinal.
                subst v'0 s' v m_.
                apply star_plus in H3; try congruence.

                assert (forall b0 : block, Mem.valid_block (m1, d1) b0 -> Mem.valid_block m' b0) as MINCR.
                {
                  intros b0 H1.
                  assert (Mem.flat_inj (Mem.nextblock (m1, d1)) b0 = Some (b0, 0)).
                  {
                    unfold Mem.valid_block in H1.
                    unfold Mem.flat_inj.
                    destruct (plt _ _); congruence.
                  }
                  eapply Mem.valid_block_inject_1.
                  + eapply Hincr. eassumption.
                  + eassumption.
                }

                assert (forall b0 : block, Mem.valid_block (m1, d1) b0 -> Mem.valid_block m'0 b0) as MINCR0.
                {
                  intros b0 H1.
                  assert (Mem.flat_inj (Mem.nextblock (m1, d1)) b0 = Some (b0, 0)).
                  {
                    unfold Mem.valid_block in H1.
                    unfold Mem.flat_inj.
                    destruct (plt _ _); congruence.
                  }
                  eapply Mem.valid_block_inject_2.
                  + eapply Hincr. eassumption.
                  + eassumption.
                }

                unfold mwd in Hincr, Hsep.
                rewrite Hjflat_eq in Hincr, Hsep.
                generalize (SimValuesInject.inject_separated_inject_incr (mem := mwd D) _ _ _ _ _ _ Hjflat_inj Hincr Hsep MINJ MINCR MINCR0).
                destruct 1 as (j3 & ? & INJ3 & INCR3).
                subst j.

                esplit.
                split.
                {
                  econstructor.
                  {
                    rewrite HPC.
                    eassumption.
                  }
                  {
                    reflexivity.
                  }
                  eassumption.
                }
                econstructor.
                split.
                {
                  simpl.
                  eassumption.
                }
                split.
                {
                  (* register values inject: tedious but easy.
                     lessdef has to be transformed into inject
                     because those values previously existing
                     were values of the old memory, which are
                     unchanged by the memory injection. *)
                  inversion INVARIANT.
                  inversion inv_inject_neutral.
                  rewrite Hjflat_eq in inv_reg_inject_neutral.
                  simpl.
                  intro u.
                  simpl.
                  rewrite SimValuesInject.match_val_simrel_inject.
                  apply undef_reg_inject.
                  intros H1.
                  match goal with
                   K: rs1 RA = rs PC |- _ => rewrite K
                  end.
                  apply set_reg_inject_left.
                  {
                    (* PC *)
                    match goal with
                        K: rs1 RA = rs PC |- _ => rewrite <- K
                    end.
                    eapply val_inject_incr; eauto.
                  }
                  intros H2.
                  apply set_regs_inject_left; auto.
                  intros H6.
                  apply undef_regs_inject.
                  intros H8.
                  eapply val_inject_incr; eauto.
                  eapply ValuesX.val_inject_lessdef_compose; eauto.
                  exploit destroyed_regs_correct; eauto.
                  destruct 1 as [ SP | SAVED ].
                  {
                    subst.
                    replace (rs1 ESP) with (rs ESP) by auto.
                    apply Val.lessdef_refl.
                  }
                  destruct SAVED as (? & ? & ?).
                  subst.
                  eauto.
                }
                assumption.
              }

              (* strictly improving a terminating is impossible *)
              destruct H as (? & ? & ?).
              discriminate.
            }
           
          }

          (* Error *)
          monad_norm.
          destruct (get_layer_primitive i Lasm) as [ [ | ] | ] ;
          constructor.
        }

        {
          (* Asm module function None *)
          generalize (compcertx_function_some_strong _ _ _ _ Fc Fasm).
          destruct 1 as (? & ? & ?).
          discriminate.
        }

        {
          (* Asm module function Error *)
          unfold Semantics.semof_function.
          monad_norm.
          constructor.
        }

        }

        { (* None *)
          eapply compcertx_function_none in Fc; eauto.
          unfold Masm.
          rewrite Fc.
          unfold Semantics.semof_function.
          monad_norm.
          assert (OK None ⊕ get_layer_primitive i Lasm = get_layer_primitive i Lasm) as EQ.
          {
            destruct (get_layer_primitive i Lasm) as [ [ | ] | ]; reflexivity.
          }
          rewrite EQ; clear EQ.
          assert (x <- OK None ⊕ get_layer_primitive i Lc;
                   ret (Datatypes.option_map (c_to_asm_primitive D i) x) =
                   get_layer_primitive i Lasm) as EQ.
          {
            unfold Lasm.
            unfold c_to_asm_layer.
            unfold asmlayer_ops.
            rewrite (PTreeLayerMap.get_layer_primitive_map (c_to_asm_primitive D) (fun _ => globvar_map (fun _ => tt))).
            destruct (get_layer_primitive i Lc) as [ [ | ] | ] eqn:EQ;
            reflexivity.
          }
          rewrite EQ; clear EQ.
          unfold Lasm.
          apply get_layer_primitive_sim_monotonic.
          apply c_to_asm_layer_monotonic.
          ehtransitivity; eauto.
        }

        (* Error *)
        destruct (compcertx_function_error Mc i) as [? H].
        {
          rewrite Fc.
          esplit; eauto.
        }
        unfold Masm.
        rewrite H.
        constructor.

      }

      (* global variables *)
      intros i.
      unfold c_to_asm_layer.
      rewrite (PTreeLayerMap.get_layer_globalvar_map (c_to_asm_primitive D) (fun _ => globvar_map (fun _ => tt))).
      rewrite Semantics.get_semof_globalvar.
      rewrite Semantics.get_semof_globalvar.
      unfold Lasm.
      unfold c_to_asm_layer.
      unfold asmlayer_ops.
      rewrite (PTreeLayerMap.get_layer_globalvar_map (c_to_asm_primitive D) (fun _ => globvar_map (fun _ => tt))).
      destruct (get_module_variable i Mc) as [ o | ] eqn:VARC.
      {
        generalize VARC. intro VARC_.
        eapply compcertx_variable_ok in VARC; eauto.
        unfold Masm.
        rewrite VARC.
        destruct o as [ g | ].
        {
          (* HERE use module_layer_disjoint *)
          generalize (module_layer_disjoint_c i).
          rewrite VARC_.
          unfold clayer_ops.
          inversion 1; subst; autorewrite with res_option_globalvar; reflexivity.
        }
        autorewrite with res_option_globalvar.
        reflexivity.
      }
      assert (isError (get_module_variable i Mc)) as ERR.
      {
        rewrite VARC.
        esplit; eauto.
      }
      eapply compcertx_variable_error in ERR; eauto.
      destruct ERR as (? & ERR).
      unfold Masm.
      rewrite ERR.
      res_option_globalvar_red.
      constructor.

    Qed.

End CORRECTNESS.

Class CompCertXReqs
      mem
      `{memory_model_ops: Mem.MemoryModelOps mem}
      `{use_mem_with_data: !UseMemWithData mem}
      `{make_program_ops: MakeProgramOps}
      `{mmatch_ops: !ValueDomain.MMatchOps mem}
      `{magree_ops: !Deadcodeproof.MAgreeOps mem}
      `{res_id: I64helpers.ReservedId}
: Prop :=
  {
    memory_model: Mem.MemoryModelX mem;
    make_program_prf: MakeProgram;

    (** Requirements of value analysis (CSE, constant propagation, dead code elimination) *)
    mmatch_constructions_prf: ValueAnalysis.MMatchConstructions mem;

    (** Requirements of dead code elimination *)
    magree_prf: Deadcodeproof.MAgree mem;

    (** For external calls. *)
    builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet;
    i64_norepet: I64Norepet
  }.

Global Existing Instances memory_model make_program_prf mmatch_constructions_prf magree_prf builtin_idents_norepet_prf.
Global Existing Instance i64_norepet.

(** ** Layer logic proof rule *)

Section WITHREQS.
  Context `{compcertx_reqs: CompCertXReqs}.

  Theorem compcertx_correct
          (DH: layerdata)
          (LH: clayer DH)
          (DL: layerdata)
          (LL: clayer DL)
          (R: simrel DH DL)
          (M: cmodule):
    ForallPrimitive DL (CPrimitiveExtcallProperties DL) LL ->
    ForallPrimitive DL (CPrimitivePreservesInvariant DL) LL ->
    layers_disjoint (D2:=DL) LL L64 ->
    module_layer_disjoint M (LL ⊕ L64) ->
    LL ⊕ L64 ⊢ (R, M) : LH ->
    c_to_asm_layer LL ⊕ c_to_asm_layer L64 ⊢
      (inj ∘ inv ∘ R, compcertx M) : c_to_asm_layer LH.
  Proof.
    intros PROPS INVAR DISJ MLDISJ CPROOF.
    assert (Proper (sim (inv (mem := mem))) LL) as INVAR'
     by typeclasses eauto.
    clear INVAR.
    rename INVAR' into INVAR.
    apply LayerLogicImpl.logic_elim in CPROOF.
    apply LayerLogicImpl.logic_intro.
    htransitivity (c_to_asm_layer (〚M 〛 (LL ⊕ L64))).
    { solve_monotonic. }
    pose proof L64.L64_extcall_properties.
    pose proof L64_autosim.
    assert (sim inj (LL ⊕ L64) (LL ⊕ L64)) as LINJ.
    {
      apply oplus_sim_monotonic;
      solve_monotonic.
    }
    assert (sim inv (LL ⊕ L64) (LL ⊕ L64)) as LINV.
    {
      apply oplus_sim_monotonic;
      solve_monotonic.
    }
    {
      eapply cat_sim_trans_le_left.
      {
        eapply compcertx_module_correctness; eauto.
        + apply CompCertBuiltins.external_calls_ops_x_to_external_calls; try typeclasses eauto.
          apply cprimitive_extcall_prf.
          pose proof L64.L64_extcall_properties.
          pose proof (forallprim_oplus_disjoint DL).
          eauto.
        + apply right_upper_bound.
      }
      (* solve_monotonic idtac. # loops forever, maybe because layer_sim_module_layer_sim is not handled properly. *)
      apply Semantics.semof_monotonic.
      apply Semantics.layer_sim_module_layer_sim.
      split.
      { simpl. solve_monotonic. }
      split.
      { apply c_to_asm_layer_oplus. assumption. }
      (* rsat *)
      exact I.
    }
  Qed.

End WITHREQS.
