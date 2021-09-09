Require Import compcert.lib.Coqlib.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcert.cfrontend.Ctypes.
Require Import compcertx.x86.AsmX.
Require Import liblayers.lib.Decision.
Require Import liblayers.compcertx.ErrorMonad.
Require Export liblayers.logic.Layers.
Require Export liblayers.logic.PTreeLayers.
Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Export liblayers.compcertx.MemWithData.
Require Export liblayers.compat.CompatData.
Require Export liblayers.compat.CompatPrimSem.
Require Export liblayers.compat.CompatLayerDef.

Section WITH_MEMORY_MODEL.
  Context `{Hmem: Mem.MemoryModel} `{Hmem': !UseMemWithData mem}.

  (** * Extra interface *)

  Section POINTWISE.

  Local Existing Instance ptree_layer_sim_op.
  Local Existing Instance ptree_layer_ops.
  Local Existing Instance ptree_layer_prf.

  (** FIXME: those are theorems about [ptree_layer] *)
  Lemma cl_layer_pointwise D1 D2 (R: path compatrel D1 D2) L1 L2:
    sim R (cl_base_layer L1) (cl_base_layer L2) <->
    (forall (i: ident),
       res_le (option_le (compatsim R))
         (get_layer_primitive i L1)
         (get_layer_primitive i L2)) /\
     (forall (i: ident),
        res_le (option_le eq)
         (get_layer_globalvar i L1)
         (get_layer_globalvar i L2)).
  Proof.
    simpl.
    generalize (cl_base_layer L1) (cl_base_layer L2); clear L1 L2.
    intros L1 L2.
    split.
    * intros H.
      simpl.
      split; intro; solve_monotonic.
    * intros [Hfun Hvar].
      destruct L1 as [L1p L1v], L2 as [L2p L2v].
      Local Transparent ptree_layer_ops.
      constructor; intro i;
      specialize (Hfun i);
      specialize (Hvar i);
      simpl in *;
      unfold ptree_layer_primitive, ptree_layer_globalvar in *; simpl in *.
      Local Opaque ptree_layer_ops.
      + destruct (Maps.PTree.get i L1p) as [[|]|];
        destruct (Maps.PTree.get i L2p) as [[|]|];
        simpl in *;
        inversion Hfun as [x1 x2 Hx | ]; try inversion Hx; subst;
        solve_monotonic.
      + destruct (Maps.PTree.get i L1v) as [[|]|];
        destruct (Maps.PTree.get i L2v) as [[|]|];
        simpl in *;
        inversion Hvar as [x1 x2 Hx | ]; try inversion Hx; subst;
        solve_monotonic.
  Qed.

  (** FIXME: those are theorems about [ptree_layer] *)
  Lemma cl_le_layer_pointwise D (L1 L2: compatlayer D):
    sim id (cl_base_layer L1) (cl_base_layer L2) <->
    (forall (i: ident),
       res_le (option_le (compatsem_le D))
         (get_layer_primitive i L1)
         (get_layer_primitive i L2)) /\
     (forall (i: ident),
        res_le (option_le eq)
         (get_layer_globalvar i L1)
         (get_layer_globalvar i L2)).
  Proof.
    apply cl_layer_pointwise.
  Qed.

  (** FIXME: those are theorems about [ptree_layer] *)
  Lemma cl_sim_layer_pointwise D1 D2 (R: compatrel D1 D2) L1 L2:
    sim (path_inj R) (cl_base_layer L1) (cl_base_layer L2) <->
    (forall (i: ident),
       res_le (option_le (compatsim (path_inj R)))
         (get_layer_primitive i L1)
         (get_layer_primitive i L2)) /\
     (forall (i: ident),
        res_le (option_le eq)
         (get_layer_globalvar i L1)
         (get_layer_globalvar i L2)).
  Proof.
    apply cl_layer_pointwise.
  Qed.

  End POINTWISE.

  (** * Properties of LayerOK *)

  Lemma get_layer_primitive_mapsto_le_ok
        {D}
        (L: compatlayer D)
        {HOK: LayerOK L}
        i (σ: compatsem D)
        (Hle: (i ↦ σ) ≤ L):
    exists σ',
      get_layer_primitive i L = OK (Some σ') /\
      compatsem_le _ σ σ'.
  Proof.
    generalize (get_layer_primitive_sim_monotonic _ _ _ i _ _ Hle).
    rewrite get_layer_primitive_mapsto.
    inversion 1; subst.
    * inversion H2; subst.
      eauto.
    * exfalso. destruct (HOK i) as [[σ' Hσ'] _ _].
      simpl in *.
      congruence.
  Qed.

  Lemma get_layer_globalvar_mapsto_le_ok
        {D}
        (L: compatlayer D)
        {HOK: LayerOK L}
        i (τ: globvar (Ctypes.type))
        (Hle: (i ↦ τ) ≤ L):
    get_layer_globalvar i L = OK (Some τ).
  Proof.
    generalize (get_layer_globalvar_sim_monotonic _ _ _ i _ _ Hle).
    rewrite get_layer_globalvar_mapsto.
    inversion 1; subst.
    * inversion H2; subst.
      symmetry; assumption.
    * exfalso. destruct (HOK i) as [_ [τ' Hτ'] _].
      simpl in *.
      congruence.
  Qed.


  (** * Matching initial states *)

  Require Import MakeProgram.

  Record cl_init_sim_mem D1 D2 (R: compatrel D1 D2) (m2: mem) :=
    {
      cl_init_sim_relate:
        relate_AbData (Mem.flat_inj (Mem.nextblock m2)) empty_data empty_data;
      cl_init_sim_match:
        match_AbData empty_data m2 (Mem.flat_inj (Mem.nextblock m2))
    }.

  Section WITH_PROGRAM.

    Context `{Hmkp: MakeProgram}.
    Context `{Fm: Type}.
    Context `{Fp: Type}.
    Context `{Vp: Type}.
    Context `{Hmodule: Modules AST.ident Fm (globvar Ctypes.type)}.
    Context `{mkp_fmt_ops: !ProgramFormatOps Fm Ctypes.type Fp Vp}.
    Context `{mkp_fmt: !ProgramFormat Fm Ctypes.type Fp Vp}.

    Require Import InitMem.

    Record cl_init_sim_def D1 D2 R (L1: compatlayer D1) (M: module) (L2: compatlayer D2) :=
      {
        cl_init_sim_init_mem:
          forall (CTXT: module) (m2: mem),
            (p <- make_program _ (CTXT ⊕ M, L2); ret (Genv.init_mem p) = OK (Some m2)) ->
            cl_init_sim_mem D1 D2 R m2;

        cl_init_sim_glbl:
          forall i,
            List.In i new_glbl ->
            isOKNone (get_layer_globalvar i L1);

        cl_init_sim_glbl_prim:
          forall i,
            List.In i new_glbl ->
            isOKNone (get_layer_primitive i L1);

        cl_init_sim_glbl_module:
          forall i,
            List.In i new_glbl ->
            exists vi, get_module_variable i M = OK (Some vi);

        cl_init_sim_M:
          forall {F V} (ge: Genv.t F V) i vi,
          get_module_variable i M = OK (Some vi) ->
          Genv.init_data_list_valid ge 0 (gvar_init vi) = true;

        cl_init_sim_low:
          forall i,
            isOKNone (get_layer_globalvar i L2)

      }.

    Inductive cl_init_sim D1: forall D2, path compatrel D1 D2 ->
      compatlayer D1 -> module -> compatlayer D2 -> Prop :=
      | cl_init_sim_inj D2 R L1 M L2:
          cl_init_sim_def D1 D2 R L1 M L2 ->
          cl_init_sim D1 D2 (path_inj R) L1 M L2
      | cl_init_sim_cons D2 D3 R Rs L1 M L2 N L3:
          cl_init_sim_def D1 D2 R L1 M L2 ->
          cl_init_sim D2 D3 Rs L2 N L3 ->
          cl_init_sim D1 D3 (path_cons R Rs) L1 (M ⊕ N) L3.

    Lemma cl_init_sim_intro D1 D2 R (L1: compatlayer D1) (M: module) (L2: compatlayer D2):
      (forall (CTXT: module) (m2: mem),
         (p <- make_program _ (CTXT ⊕ M, L2); ret (Genv.init_mem p)) = OK (Some m2) ->
         cl_init_sim_mem D1 D2 R m2) ->
      (forall i,
         List.In i new_glbl ->
         isOKNone (get_layer_globalvar i L1)) ->
      (forall i,
         List.In i new_glbl ->
         isOKNone (get_layer_primitive i L1)) ->
      (forall i,
         List.In i new_glbl ->
         exists vi, get_module_variable i M = OK (Some vi)) ->
      (forall {F V} (ge: Genv.t F V)  i vi,
         get_module_variable i M = OK (Some vi) ->
         Genv.init_data_list_valid ge 0 (gvar_init vi) = true) ->
      (forall i,
         isOKNone (get_layer_globalvar i L2)) ->
      cl_init_sim D1 D2 (path_inj R) L1 M L2.
    Proof.
      intros Hinitmem HL1v HL1p HMglbl HMinitdata HMnonglbl.
      constructor.
      split.
      * intros.
        eauto.
      * intros i Hi.
        eauto.
      * intros. eauto.
      * intros. eauto.
      * intros. eauto.
      * intros. eauto.
    Qed.

  End  WITH_PROGRAM.
End WITH_MEMORY_MODEL.
