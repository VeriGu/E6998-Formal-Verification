(** CompCert transform_program* and LayerLib make_program. *)

Require Import compcert.lib.Coqlib.
Require Import compcert.common.Values.
Require Import compcert.common.AST.
Require Export liblayers.logic.Structures.
Require Export liblayers.logic.OptionOrders.
Require Export liblayers.lib.OptionMonad.
Require Export liblayers.compcertx.ErrorMonad.
Require Import Coq.Classes.RelationPairs.
Require Export liblayers.compcertx.CompcertStructures.
Require Import liblayers.compcertx.MakeProgramSpec.
Require Import liblayers.logic.GlobalVars.

Arguments mkglobvar {_} _ _ _ _.

Inductive globvar_rel
          {V_prog_from V_prog_to: Type} (R: rel V_prog_from V_prog_to):
  rel (globvar V_prog_from) (globvar V_prog_to)
  :=
    globvar_rel_intro:
      Monotonic
        mkglobvar
        (R ++> eq ++> eq ++> eq ++> globvar_rel R).

(* transform_program and program_rel *)

Section TRANSFORM_PROGRAM.

  Local Existing Instance globvar_rel_intro.

  Context {F_prog_from V_prog_from F_prog_to V_prog_to: Type}.

  Variables transf_F_prog: F_prog_from -> res F_prog_to.
  Variables transf_V_prog: V_prog_from -> res V_prog_to.

  Let RF_prog := fun _: ident => option_rel (fun f_from f_to => transf_F_prog f_from = OK f_to).
  Let RV_prog := fun _: ident => option_rel (globvar_rel (fun v_from v_to => transf_V_prog v_from = OK v_to)).

  Section GLOBDEFS_REL.

  Let globdefs_rel := list_rel ((eq (A := ident)) * rforall i, globdef_rel (RF_prog) (RV_prog) i)%rel.

  Lemma transf_globdefs_rel_recip l_from l_to:
      globdefs_rel l_from l_to ->
      transf_globdefs (fun _ => transf_F_prog) (fun _ => transf_V_prog) l_from = OK l_to.
  Proof.
    induction 1; simpl; auto.
    inversion_clear H; subst.
    destruct x; destruct y; simpl in * |- * ; subst.
    specialize (H2 i0).
    inversion_clear H2; subst.
    rewrite IHlist_rel; clear IHlist_rel; simpl.
    unfold Monad.bind in *;
    destruct o; destruct o0; simpl in * |- * ; auto.
    {
      destruct g; destruct g0; (try now inversion H); (try now inversion H1);
      unfold fun_of_globdef, var_of_globdef in *;
      simpl in *.
      {
        inversion_clear H; subst.
        rewrite H2.
        reflexivity.
      }
      inversion_clear H1; subst.
      inversion_clear H2; subst.
      unfold transf_globvar; simpl.
      unfold bind; simpl.
      rewrite H1.
      reflexivity.
    }
    {
      destruct g; (try now inversion H); (try now inversion H1).
    }
    destruct g; (try now inversion H); (try now inversion H1).
  Qed.    

  Lemma globdefs_rel_flip_impl:
    forall j,
      subrel
        (CompcertStructures.globdefs_rel (fun i => flip (RF_prog i)) (fun i => flip (RV_prog i)) j)
        (flip globdefs_rel).
  Proof.
    unfold flip, globdefs_rel.
    red.
    induction 1.
    { constructor. }
    apply app_rel; auto.
    constructor.
    {
      constructor; auto.
      red.
      intros c.
      inversion H0.
      constructor; auto.
    }
    constructor.
  Qed.

  End GLOBDEFS_REL.

  Lemma transform_partial_program2_recip_flip p:
    forall pto,
      program_rel (fun j => flip (RF_prog j)) (fun j => flip (RV_prog j)) pto p ->
      transform_partial_program2 (fun _ => transf_F_prog) (fun _ => transf_V_prog) p = OK pto.
  Proof.
    intros pto H.    
    inversion H; subst.
    inversion program_rel_upto_glob_threshold; subst.    
    unfold transform_partial_program2.
    simpl.
    apply globdefs_rel_flip_impl in H0.
    apply transf_globdefs_rel_recip in H0.
    rewrite H0.
    reflexivity.
  Qed.

  Context
    {ld_from Fm_from Vm_from module_from : Type}
    {primsem_from layer_from : ld_from -> Type}
    {gvar_from_ops: GlobalVarsOps (globvar Vm_from)}
    {module_from_ops : ModuleOps ident Fm_from (globvar Vm_from) module_from}
    {primsem_from_ops : PrimitiveOps primsem_from}
    {layer_from_ops : LayerOps ident primsem_from (globvar Vm_from) layer_from}
    {program_format_ops_from: ProgramFormatOps Fm_from Vm_from F_prog_from V_prog_from}
    {D_from: ld_from}
  .

  Context
    {ld_to Fm_to Vm_to module_to : Type}
    {primsem_to layer_to : ld_to -> Type}
    {gvar_to_ops: GlobalVarsOps (globvar Vm_to)}
    {module_to_ops : ModuleOps ident Fm_to (globvar Vm_to) module_to}
    {primsem_to_ops : PrimitiveOps primsem_to}
    {layer_to_ops : LayerOps ident primsem_to (globvar Vm_to) layer_to}
    {program_format_ops_to: ProgramFormatOps Fm_to Vm_to F_prog_to V_prog_to}
    {D_to: ld_to}
  .

  Variables
    (convert_primsem: ident -> primsem_from D_from -> primsem_to D_to)
    (convert_globalvar: Vm_from -> Vm_to)
  .

  (* Source to compiled. *)

  Let RF_module: funrel D_from D_to :=
    fun i =>
    option_rel
      ((fun (f_from: Fm_from) f_to =>
         exists fp_from,
           make_internal f_from = OK fp_from /\
           exists fp_to,
             transf_F_prog fp_from = OK fp_to /\
             make_internal f_to = OK fp_to) + (fun p_from p_to => convert_primsem i p_from = p_to)).

  Let RV_module: varrel (Vm1 := Vm_from) (Vm2 := Vm_to) :=
    fun _ =>
      option_rel (globvar_rel (fun v_from v_to => convert_globalvar v_from = v_to)).

  Hypothesis convert_primitive_to_program:
    forall i f f_,
      make_external D_from i f = OK f_ -> 
      forall fto_,
        make_external D_to i (convert_primsem i f) = OK fto_ ->
        transf_F_prog f_ = OK fto_.

  Variables (make_varinfo_from: Vm_from -> V_prog_from).
  Variables (make_varinfo_to: Vm_to -> V_prog_to).

  Hypothesis make_varinfo_from_map:
    forall v v',
    make_varinfo v = OK v' ->
    v' = globvar_map make_varinfo_from v.

  Hypothesis make_varinfo_to_map:
    forall v v',
    make_varinfo v = OK v' ->
    v' = globvar_map make_varinfo_to v.

  Hypothesis transf_V_module_to_program:
    forall v,
      transf_V_prog (make_varinfo_from v) = OK (make_varinfo_to (convert_globalvar v)).

  Local Instance make_program_relations:
    MakeProgramRelations D_from D_to RF_module RV_module RF_prog RV_prog.
  Proof.
    split.
    * intros i.
      red.
      unfold RF_module.
      inversion 1; subst; congruence.
    * intros i.
      red.
      unfold RV_module.
      inversion 1; subst; congruence.
    * repeat red.
      unfold RF_module.
      intros i x y H x0 y0 H0 H1.
      inversion H; clear H; subst.
      + inversion H1; clear H1; subst.
        inversion H0; clear H0; subst.
        inversion H3; clear H3; subst.
        {
          inversion H1; clear H1; subst.
          inversion H2; clear H2; subst.
          destruct H as (fp_from & make_from & fp_to & transf & make_to).
          constructor.
          congruence.
        }
        inversion H2; clear H2; subst.
        inversion H1; clear H1; subst.
        constructor.
        eauto.
      + inversion H1; clear H1; subst.
        inversion H0; clear H0; subst.
        constructor.
    * repeat red.
      unfold RV_module.
      intros i x y H x0 y0 H0 H1.
      inversion H; clear H; subst.
      + inversion H1; clear H1; subst.
        inversion H0; clear H0; subst.
        inversion H3; clear H3; subst.
        inversion H1; clear H1; subst.
        inversion H2; clear H2; subst.        
        apply make_varinfo_to_map in H0.
        unfold globvar_map in H0.
        simpl in H0.
        subst.
        apply make_varinfo_from_map in H1.
        unfold globvar_map in H1.
        simpl in H1.
        subst.
        constructor.
        constructor; auto.
      + inversion H1; clear H1; subst.
        inversion H0; clear H0; subst.
        constructor.
    * intros i f1 f2 Hf.
      inversion Hf; clear Hf; subst.
      destruct H1 as [f_from f_to Hf | p_from p_to Hp].
      + destruct Hf as (fp_from & Hfp_from & fp_to & Hfp & Hfp_to).
        simpl.
        rewrite Hfp_from, Hfp_to.
        intros [err H].
        discriminate.
      + simpl.        
        inversion 1.
        revert H.
        admit. (* need properties on convert_primsem vs. make_external *)
    * intros i v1 v2 Hv.
      inversion Hv; clear Hv; subst.
      destruct H1 as [v1 v2 Hv init _ [] ro _ [] vol _ []].
      admit. (* need properties on convert_globvar vs. make_varinfo *)
  Admitted.

  Local Instance make_program_relations_flip:
    MakeProgramRelations D_to D_from (fun i => flip (RF_module i)) (fun i => flip (RV_module i)) (fun i => flip (RF_prog i)) (fun i => flip (RV_prog i)).
  Proof.
    split.
    * intros i.
      red.
      unfold flip, RF_module.
      inversion 1; subst; congruence.
    * intros i.
      red.
      unfold flip, RV_module.
      inversion 1; subst; congruence.
    * repeat red.
      unfold flip, RF_module.
      intros i x y H x0 y0 H0 H1.
      inversion H; clear H; subst.
      + inversion H1; clear H1; subst.
        inversion H0; clear H0; subst.
        inversion H4; clear H4; subst.
        {
          inversion H1; clear H1; subst.
          inversion H2; clear H2; subst.
          destruct H as (fp_from & make_from & fp_to & transf & make_to).
          constructor.
          congruence.
        }
        inversion H2; clear H2; subst.
        inversion H1; clear H1; subst.
        constructor.
        eauto.
      + inversion H1; clear H1; subst.
        inversion H0; clear H0; subst.
        constructor.
    * repeat red.
      unfold flip, RV_module.
      intros i x y H x0 y0 H0 H1.
      inversion H; clear H; subst.
      + inversion H1; clear H1; subst.
        inversion H0; clear H0; subst.
        inversion H4; clear H4; subst.
        inversion H1; clear H1; subst.
        inversion H2; clear H2; subst.
        apply make_varinfo_from_map in H0.
        unfold globvar_map in H0.
        simpl in H0.
        subst.
        apply make_varinfo_to_map in H1.
        unfold globvar_map in H1.
        simpl in H1.
        subst.
        constructor.
        constructor; auto.
      + inversion H1; clear H1; subst.
        inversion H0; clear H0; subst.
        constructor.
    * intros i f1 f2 Hf.
      inversion Hf; clear Hf; subst.
      destruct H1 as [f_from f_to Hf | p_from p_to Hp].
      + destruct Hf as (fp_from & Hfp_from & fp_to & Hfp & Hfp_to).
        simpl.
        rewrite Hfp_from, Hfp_to.
        intros [err H].
        discriminate.
      + simpl.        
        inversion 1.
        revert H.
        admit. (* need properties on convert_primsem vs. make_external *)
    * intros i v1 v2 Hv.
      inversion Hv; clear Hv; subst.
      destruct H1 as [v1 v2 Hv init _ [] ro _ [] vol _ []].
      admit. (* need properties on convert_globvar vs. make_varinfo *)
  Admitted.

  (* For a correctly compiled module. *)

  Variables (Mfrom: module_from) (Mto: module_to).
  Variables (Lfrom: layer_from D_from) (Lto: layer_to D_to).

  Hypothesis get_module_function_some:
    forall i ffrom,
      get_module_function i Mfrom = OK (Some ffrom) ->
      exists fto,
        get_module_function i Mto = OK (Some fto) /\
        exists fp_from,
          make_internal ffrom = OK fp_from /\
          exists fp_to,
            transf_F_prog fp_from = OK fp_to /\
            make_internal fto = OK fp_to.

  Hypothesis get_module_function_none:
    forall i,
      get_module_function i Mfrom = OK None ->
      get_module_function i Mto = OK None.

  Hypothesis get_module_variable_eq:
    forall i ffrom,
      get_module_variable i Mfrom = OK ffrom ->
      get_module_variable i Mto = OK (option_map (globvar_map convert_globalvar) ffrom).

  Hypothesis get_layer_primitive_eq:
    forall i ffrom,
      get_layer_primitive i Lfrom = OK ffrom ->
      get_layer_primitive i Lto = OK (option_map (convert_primsem i) ffrom).

  Hypothesis get_layer_globalvar_eq:
    forall i ffrom,
      get_layer_globalvar i Lfrom = OK ffrom ->
      get_layer_globalvar i Lto = OK (option_map (globvar_map convert_globalvar) ffrom).
    
  Lemma module_layer_rel_flip_intro:      
    module_layer_rel D_to D_from (fun i : ident => flip (RF_module i))
                     (fun i : ident => flip (RV_module i)) (Mto, Lto) (Mfrom, Lfrom).
  Proof.
    unfold module_layer_rel.
    simpl.
    intros i.
    split.
    {
      unfold get_module_layer_function; simpl.
      destruct (get_module_function i Mfrom) eqn:H.
      {
        destruct (get_layer_primitive i Lfrom) eqn:H0.
        {
          apply get_layer_primitive_eq in H0.
          rewrite H0.
          destruct o.
          {
            apply get_module_function_some in H.
            destruct H as (? & H & TRANSF).
            rewrite H.
            simpl.
            destruct o0; simpl; constructor; auto.
            constructor.
            constructor.
            assumption.
          }
          apply get_module_function_none in H.
          rewrite H.
          simpl.
          destruct o0; simpl; constructor; auto; repeat constructor.
        }
        simpl.
        destruct o; constructor.
      }
      simpl.
      constructor.
    }
    unfold get_module_layer_variable; simpl.
    destruct (get_module_variable i Mfrom) as [ o | ] eqn:H; simpl.
    {
      apply get_module_variable_eq in H.
      rewrite H; clear H.
      destruct (get_layer_globalvar i Lfrom) as [ o0 | ] eqn:H0; simpl.
      {
        apply get_layer_globalvar_eq in H0.
        rewrite H0; clear H0.
        destruct o as [ g | ].
        {
          destruct o0 as [ g0 | ].
          {
            destruct (Decision.decide (g = g0)).
            {
              subst.
              autorewrite with res_option_globalvar.
              simpl.
              repeat constructor.
              destruct g0; repeat constructor.
            }
            rewrite (GlobalVars.res_option_globalvar_oplus_diff g g0) by assumption.
            constructor.
          }
          autorewrite with res_option_globalvar.
          simpl.
          repeat constructor.
          destruct g; repeat constructor.
        }
        autorewrite with res_option_globalvar.
        simpl.
        repeat constructor.
        destruct o0 as [ g0 | ]; repeat constructor.
        destruct g0; repeat constructor.
      }
      GlobalVars.res_option_globalvar_red.
      constructor.
    }
    GlobalVars.res_option_globalvar_red.
    constructor.
  Qed.
  
  Context `{make_program_prf: MakeProgram}.

  Lemma make_program_transform_partial_program2 pfrom pto:
    make_program _ (Mfrom, Lfrom) = OK pfrom ->
    make_program _ (Mto, Lto) = OK pto ->
    transform_partial_program2 (fun _ => transf_F_prog) (fun _ => transf_V_prog) pfrom = OK pto.
  Proof.
    intros H H0.
    generalize (make_program_rel make_program_relations_flip _ _ module_layer_rel_flip_intro).
    rewrite H.
    rewrite H0.
    inversion 1; subst.
    eapply transform_partial_program2_recip_flip; eauto.
  Qed.

  Lemma make_program_from_to_exists pfrom:
    make_program _ (Mfrom, Lfrom) = OK pfrom ->
    exists pto, make_program _ (Mto, Lto) = OK pto.
  Proof.
    intros H.
    generalize (make_program_rel make_program_relations_flip _ _ module_layer_rel_flip_intro).
    rewrite H.
    inversion 1; subst.
    eauto.
  Qed.

  Hypothesis Mfrom_OK_function:
    forall i,
      isError (get_module_function i Mfrom) ->
      isError (get_module_function i Mto).

  Hypothesis Mfrom_OK_variable:
    forall i,
      isError (get_module_variable i Mfrom) ->
      isError (get_module_variable i Mto).

  Hypothesis Lfrom_OK_primitive:
    forall i,
      isError (get_layer_primitive i Lfrom) ->
      isError (get_layer_primitive i Lto).

  Hypothesis Lfrom_OK_globalvar:
    forall i,
      isError (get_layer_globalvar i Lfrom) ->
      isError (get_layer_globalvar i Lto).

  (** The following condition is required to ensure that Mfrom, Lfrom
      do not have different global variables at the same
      symbol. Indeed, if we were to have some, and if those two global
      variables were converted to the same one, then we would have to
      prove [res_le (option_le _) (Error _) (OK _)], which obviously
      does not hold.

      The alternative is to require that [convert_globalvar] be
      injective, which is not realistic unless we use the same type for
      source and target global variables for modules and layers, and
      convert them only when translating their corresponding programs.
   *)
  Hypothesis DISJ: module_layer_disjoint Mfrom Lfrom.

  Lemma module_layer_rel_intro:
    module_layer_rel D_from D_to RF_module RV_module (Mfrom, Lfrom) (Mto, Lto).
  Proof.
    unfold module_layer_rel.
    simpl.
    intros i.
    split.
    {
      unfold get_module_layer_function; simpl.
      destruct (get_module_function i Mfrom) eqn:H.
      {
        destruct (get_layer_primitive i Lfrom) eqn:H0.
        {
          apply get_layer_primitive_eq in H0.
          rewrite H0.
          destruct o.
          {
            apply get_module_function_some in H.
            destruct H as (? & H & TRANSF).
            rewrite H.
            simpl.
            destruct o0; simpl; constructor; auto.
            constructor.
            constructor.
            assumption.
          }
          apply get_module_function_none in H.
          rewrite H.
          simpl.
          destruct o0; simpl; constructor; auto; repeat constructor.
        }
        destruct (Lfrom_OK_primitive i) as [? H1].
        { rewrite H0. econstructor. reflexivity. }
        rewrite H1.
        destruct (get_module_function i Mto).
        {
          destruct o0; constructor.
        }
        constructor.
      }
      destruct (Mfrom_OK_function i) as [? H1].
      { rewrite H. econstructor. reflexivity. }
      rewrite H1.
      constructor.
    }
    unfold get_module_layer_variable; simpl.
    destruct (get_module_variable i Mfrom) as [ o | ] eqn:H.
    {
      generalize H. intro H_.
      apply get_module_variable_eq in H.
      rewrite H; clear H.
      destruct (get_layer_globalvar i Lfrom) as [ o0 | ] eqn:H0.
      {
        generalize H0. intro H0_.
        apply get_layer_globalvar_eq in H0.
        rewrite H0; clear H0.
        destruct o as [ g | ].
        {
          destruct o0 as [ g0 | ].
          {
            assert (g = g0).
            {
              specialize (DISJ i).
              rewrite H_ in DISJ.
              rewrite H0_ in DISJ.
              inversion DISJ; congruence.
            }
            subst.
            autorewrite with res_option_globalvar.
            destruct g0; repeat constructor.
          }
          simpl.
          autorewrite with res_option_globalvar.
          destruct g; repeat constructor.
        }
        simpl.
        autorewrite with res_option_globalvar.
        destruct o0 as [ [ ] | ] ; repeat constructor.
      }
      edestruct Lfrom_OK_globalvar as [ ? EQ ]; unfold isError; eauto.
      rewrite EQ.
      res_option_globalvar_red.
      constructor.
    }
    edestruct Mfrom_OK_variable as [ ? EQ ]; unfold isError; eauto.
    rewrite EQ.
    res_option_globalvar_red.
    constructor.
  Qed.

  Lemma make_program_to_from_exists pto:
    make_program _ (Mto, Lto) = OK pto ->
    exists pfrom, make_program _ (Mfrom, Lfrom) = OK pfrom.
  Proof.
    intros H.
    generalize (make_program_rel make_program_relations _ _ module_layer_rel_intro).
    rewrite H.
    inversion 1; subst.
    eauto.
  Qed.

End TRANSFORM_PROGRAM.
