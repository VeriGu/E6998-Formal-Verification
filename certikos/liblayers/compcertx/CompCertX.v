(** * CompCertX: from LayerLib C-style ClightX to LayerLib Asm-style AsmX *)

Require Import compcert.lib.Coqlib.
Require Import compcert.common.AST.
Require Import liblayers.lib.Decision.
Require Import liblayers.compcertx.ErrorMonad.
Require Import compcert.x86.Asm.
Require Import compcertx.x86.AsmX.

Require Import AsmModules.

Require Import ClightModules.

Require Import SeparateCompiler.
Require Import AsmXAsmGen.

Require Import liblayers.logic.PTrees.
Require PTreeLayerMap.
Require PTreeModuleMap.

Require Import MakeProgramSpec. (* for globvar_map *)

(* CompCertX as CompCert-style transform_program. *)

Definition transf_clight_function
           (cenv: composite_env)
           (defmap: PTree.t (globdef Cminor.fundef unit))
           (hf: SplitLong.helper_functions)
           (fenv: Inlining.funenv) :=
  ComposePasses.compose_partial
    (SeparateCompiler.transf_clight_function' cenv defmap hf fenv)
    (fun x => OK (AsmXAsmGen.erase_sig_internal x)).

Definition transf_rtl_function fenv :=
  ComposePasses.compose_partial
    (SeparateCompiler.transf_rtl_function fenv)
    (fun x => OK (AsmXAsmGen.erase_sig_internal x)).

Lemma transf_rtl_function_elim cenv defmap hf fenv fc fr fa:
  transf_clight_function_to_rtl cenv defmap hf fc = OK fr ->
  transf_rtl_function fenv fr = OK fa ->
  transf_clight_function cenv defmap hf fenv fc = OK fa.
Proof.
  unfold transf_clight_function, transf_clight_function', transf_rtl_function.
  unfold ComposePasses.compose_partial, ComposePasses.apply_partial.
  intros Clight2RTL TRTL.
  rewrite Clight2RTL. assumption.
Qed.

(* Compiling a cmodule to an asmmodule. *)

  Section WITHMODULE.

    (* First, compile a module to RTL. *)

    Variable Mc: cmodule.

    Variable cenv: composite_env.
    Variable defmap: PTree.t (globdef Cminor.fundef unit).
    Variable hf: SplitLong.helper_functions.

    (* NOTE: the "eta-expansion" below for
       transf_clight_function_to_rtl is actually nontrivial, it hides
       a coercion from ClightModules.function to function. *)

    Let mrtl: PTree.t (res RTL.function) :=
      PTree.map (fun _ x => Errors.bind x (fun f: function => transf_clight_function_to_rtl cenv defmap hf f)) (get_module_functions Mc).

    Let mrtl_get i:
      mrtl ! i = 
      option_map
        (fun x => Errors.bind x (fun f: function => transf_clight_function_to_rtl cenv defmap hf f))
        (res_option_flip (get_module_function i Mc)).
    Proof.
      unfold mrtl.
      rewrite PTree.gmap.
      rewrite get_module_functions_spec.
      reflexivity.
    Qed.

    (* Construct the inlining environment. *)

    (* We do not use "definition" here. Instead,
       we first use "let", then embed it in definitions
       for the purpose of proofs. Thanks to let, the
       actual extracted code will share computations. *)

    Let fenv: Inlining.funenv :=
      PTree.map_option
        (fun i x => 
           match x with
             | Error _ => None
             | OK f =>
               (* read the `should_inline' flag from the
                  annotation in the source module *)
               match get_module_function i Mc with
                 | OK (Some phi) =>
                   if InlinableFunction.should_inline phi
                   then Some f
                   else None
                 | _ => None
               end
           end)
        mrtl.

    Definition construct_fenv := fenv.

    Lemma construct_fenv_spec i f:
      construct_fenv ! i = Some f ->
      exists fc: function,
        get_module_function i Mc = OK (Some fc) /\
        transf_clight_function_to_rtl cenv defmap hf fc = OK f.
    Proof.
      unfold construct_fenv, fenv.
      rewrite PTree.gmap_option, mrtl_get.
      intros FENV.
      destruct (get_module_function i Mc); try discriminate.
      destruct o; try discriminate.
      eexists; split; auto.
      simpl in FENV. monad_norm.
      destruct (transf_clight_function_to_rtl cenv defmap hf t); try discriminate.
      destruct (InlinableFunction.should_inline t); try discriminate.
      inv FENV; reflexivity.
    Qed.

    (* Compile RTL functions to assembly. *)

    Definition compcertx: asmmodule :=
      PTreeModuleMap.map_error
        (fun i _ =>
           match mrtl ! i with
             | None => Error (MSG "CompCertX: mrtl None, should not happen" :: nil)
             | Some f => Errors.bind (Errors.bind f (transf_rtl_function fenv)) (fun x => OK (fn_code x))
           end)
        (fun _ x => OK (globvar_map (fun _ => tt) x))
        Mc.

    Lemma compcertx_function_some_strong i (fc: function) x:
      get_module_function i Mc = OK (Some fc) ->
      get_module_function i compcertx = OK x ->
      exists fasm,
        transf_clight_function cenv defmap hf construct_fenv fc = OK fasm /\
        x = Some (fn_code fasm).
    Proof.
      intros H.
      unfold compcertx.
      setoid_rewrite PTreeModuleMap.get_module_function_map_error.
      rewrite mrtl_get.
      intros H0.
      simpl in H, H0.
      unfold cmodule_ops in H, H0.
      rewrite H in H0.
      simpl in H, H0.
      unfold cmodule_ops, ident in H, H0.
      rewrite H in H0.
      simpl in H0.
      unfold transf_clight_function.
      unfold transf_rtl_function in H0.
      unfold transf_clight_function'.
      unfold ComposePasses.compose_partial in * |- * .
      unfold ComposePasses.apply_partial in * |- * .
      unfold Errors.bind in H0.
      destruct (transf_clight_function_to_rtl cenv defmap hf fc); try discriminate.
      unfold construct_fenv.
      destruct (SeparateCompiler.transf_rtl_function fenv f); try discriminate.
      inversion H0; subst.
      eauto.
    Qed.

    Corollary compcertx_function_some:
      ModuleOK compcertx ->
      forall i (fc: function),
        get_module_function i Mc = OK (Some fc) ->
        exists fasm,
          transf_clight_function cenv defmap hf construct_fenv fc = OK fasm /\
          get_module_function i compcertx = OK (Some (fn_code fasm)).
    Proof.
      intros H i fc H0.
      specialize (H i).
      inversion H; subst.
      destruct module_ok_function.
      exploit compcertx_function_some_strong; eauto.
      destruct 1 as (? & ? & ?).
      subst x.
      eauto.
    Qed.

    Lemma compcertx_function_none i:
      get_module_function i Mc = OK None ->
      get_module_function i compcertx = OK None.
    Proof.
      intros H.
      unfold compcertx.
      setoid_rewrite PTreeModuleMap.get_module_function_map_error.
      simpl in * |- *.
      unfold cmodule_ops in * |- * .
      rewrite H.
      reflexivity.
    Qed.

    Lemma compcertx_function_error i:
      isError (get_module_function i Mc) ->
      isError (get_module_function i compcertx).
    Proof.
      destruct 1 as (? & H).
      unfold compcertx.
      setoid_rewrite PTreeModuleMap.get_module_function_map_error.
      simpl in * |- *.
      unfold cmodule_ops in * |- * .
      rewrite H.
      simpl.
      esplit; eauto.
    Qed.

    Lemma compcertx_variable_ok:
      forall i ffrom,
        get_module_variable i Mc = OK ffrom ->
        get_module_variable i compcertx = OK (option_map (globvar_map (fun _ => tt)) ffrom).
    Proof.
      intros i ffrom H.
      unfold compcertx.
      setoid_rewrite PTreeModuleMap.get_module_variable_map_error.
      simpl in * |- *.
      unfold cmodule_ops in * |- * .
      rewrite H.
      simpl.
      destruct ffrom; reflexivity.
    Qed.

    Lemma compcertx_variable_error:
      forall i,
        isError (get_module_variable i Mc) ->
        isError (get_module_variable i compcertx).
    Proof.
      intros i (? & H).
      unfold compcertx.
      setoid_rewrite PTreeModuleMap.get_module_variable_map_error.
      simpl in * |- *.
      unfold cmodule_ops in * |- * .
      rewrite H.
      simpl.
      esplit; eauto.
    Qed.

  End WITHMODULE.
