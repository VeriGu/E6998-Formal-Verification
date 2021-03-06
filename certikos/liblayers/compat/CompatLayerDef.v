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

Section WITH_MEMORY_MODEL.
  Context `{Hmem: Mem.MemoryModel} `{Hmem': !UseMemWithData mem}.

  (** * Memory accessors *)

  Definition load_accessor_sem (D: compatdata) :=
    forall F V, Genv.t F V ->
    AST.memory_chunk -> mwd D -> addrmode -> regset -> preg ->
    outcome (mem := mwd D).

  Definition store_accessor_sem (D: compatdata) :=
    forall F V, Genv.t F V ->
    AST.memory_chunk -> mwd D -> addrmode -> regset -> preg -> list preg ->
    outcome (mem := mwd D).

  (** ** Simulation diagrams *)

  Definition load_accessor_sim_def: sim_relation compatrel load_accessor_sem :=
    fun D1 D2 R exec_load1 exec_load2 =>
      forall F V (ge1 ge2: Genv.t F V),
      forall ι chunk rs1 (m1: mem) d1 a r rs1' m1' d1' rs2 (m2: mem) d2,
        stencil_matches ge1 ->
        stencil_matches ge2 ->
        exec_load1 F V ge1 chunk (m1, d1) a rs1 r = Next rs1' (m1', d1') ->
        MatchPrimcallStates R ι rs1 m1 d1 rs2 m2 d2 ->
        val_inject ι (Val.add (rs1 PC) Vone) (Val.add (rs2 PC) Vone) ->
        high_level_invariant d1 ->
        exists rs2' m2' d2',
          exec_load2 F V ge2 chunk (m2, d2) a rs2 r = Next rs2' (m2', d2') /\
          MatchPrimcallStates R ι rs1' m1' d1' rs2' m2' d2'.

  Definition store_accessor_sim_def: sim_relation compatrel store_accessor_sem :=
    fun D1 D2 R exec_store1 exec_store2 =>
      forall F V (ge1 ge2: Genv.t F V),
      forall ι chunk rs1 (m1: mem) d1 a r rd rs1' m1' d1' rs2 (m2: mem) d2,
        stencil_matches ge1 ->
        stencil_matches ge2 ->
        exec_store1 F V ge1 chunk (m1, d1) a rs1 r rd = Next rs1' (m1', d1') ->
        MatchPrimcallStates R ι rs1 m1 d1 rs2 m2 d2 ->
        val_inject ι (Val.add (rs1 PC) Vone) (Val.add (rs2 PC) Vone) ->
        high_level_invariant d1 ->
        exists rs2' m2' d2',
          exec_store2 F V ge2 chunk (m2, d2) a rs2 r rd = Next rs2' (m2', d2') /\
          MatchPrimcallStates R ι rs1' m1' d1' rs2' m2' d2'.

  (** ** Properties *)

  Class LoadAccessor (D: compatdata) (exec_load: load_accessor_sem D) :=
    {
      exec_load_symbols_preserved:
        forall {F V} (ge1 ge2: _ F V)
               (SYMB: forall i, Genv.find_symbol ge2 i = Genv.find_symbol ge1 i)
               (NEXT: Genv.genv_next ge2 = Genv.genv_next ge1)
               (BLOCK_IS_VOLATILE: forall b, Events.block_is_volatile ge2 b = Events.block_is_volatile ge1 b)
               chunk m a rs r,
          exec_load _ _ ge2 chunk m a rs r =
          exec_load _ _ ge1 chunk m a rs r;

      exec_load_kernel_mode:
        forall {F V} (ge: _ F V) chunk (m: mwd D) a rs r rs' m',
          Asm.exec_load ge chunk m a rs r = Next rs' m' ->
          kernel_mode (π_data m) ->
          exec_load _ _ ge chunk m a rs r = Next rs' m'
      ;

      exec_load_asm_invariant {F V} ge chunk m a rs rv rs' m':
        exec_load F V ge chunk m a rs rv = Next rs' m' ->
        subtype (type_of_chunk chunk) (typ_of_preg rv) = true ->
        AsmX.asm_invariant ge rs m ->
        AsmX.asm_invariant ge rs' m'
      ;

      exec_load_low_level_invariant {F V} ge chunk m a rs rv rs' m':
        exec_load F V ge chunk m a rs rv = Next rs' m' ->
        AsmX.asm_invariant ge rs m ->
        low_level_invariant (Mem.nextblock m) (snd m) ->
        low_level_invariant (Mem.nextblock m') (snd m')        
      ;

      exec_load_high_level_invariant {F V} ge chunk m a rs rv rs' m':
        exec_load F V ge chunk m a rs rv = Next rs' m' ->
        high_level_invariant (snd m) ->
        high_level_invariant (snd m')

    }.

  Record load_accessor (D: compatdata) :=
    {
      exec_load_sem :> forall F V, _;
      exec_load_spec: LoadAccessor D exec_load_sem
    }.

  Definition load_accessor_sim: sim_relation compatrel load_accessor :=
    fun D1 D2 R el1 el2 =>
      load_accessor_sim_def _ _ R (exec_load_sem _ el1) (exec_load_sem _ el2).

  Class StoreAccessor (D: compatdata) (exec_store: store_accessor_sem D) :=
    {
      exec_store_symbols_preserved:
        forall {F V} (ge1 ge2: _ F V)
               (SYMB: forall i, Genv.find_symbol ge2 i = Genv.find_symbol ge1 i)
               (NEXT: Genv.genv_next ge2 = Genv.genv_next ge1)
               (BLOCK_IS_VOLATILE: forall b, Events.block_is_volatile ge2 b = Events.block_is_volatile ge1 b)
               chunk m a rs r rl,
          exec_store _ _ ge2 chunk m a rs r rl =
          exec_store _ _ ge1 chunk m a rs r rl;

      exec_store_kernel_mode:
        forall {F V} (ge: _ F V) chunk (m: mwd D) a rs r rl rs' m',
          Asm.exec_store ge chunk m a rs r rl = Next rs' m' ->
          kernel_mode (π_data m) ->
          exec_store _ _ ge chunk m a rs r rl = Next rs' m'
      ;

      exec_store_asm_invariant {F V} ge chunk m a rs rv rvl rs' m':
        exec_store F V ge chunk m a rs rv rvl = Next rs' m' ->
        AsmX.asm_invariant ge rs m ->
        AsmX.asm_invariant ge rs' m'
      ;

      exec_store_low_level_invariant {F V} ge chunk m a rs rv rvl rs' m':
        exec_store F V ge chunk m a rs rv rvl = Next rs' m' ->
        AsmX.asm_invariant ge rs m ->
        low_level_invariant (Mem.nextblock m) (snd m) ->
        low_level_invariant (Mem.nextblock m') (snd m')        
      ;

      exec_store_high_level_invariant {F V} ge chunk m a rs rv rvl rs' m':
        exec_store F V ge chunk m a rs rv rvl = Next rs' m' ->
        high_level_invariant (snd m) ->
        high_level_invariant (snd m')

    }.

  Record store_accessor (D: compatdata) :=
    {
      exec_store_sem :> forall F V, _;
      exec_store_spec: StoreAccessor D exec_store_sem
    }.

  Definition store_accessor_sim: sim_relation compatrel store_accessor:=
    fun D1 D2 R es1 es2 =>
      store_accessor_sim_def _ _ R (exec_store_sem _ es1) (exec_store_sem _ es2).

  (** * Definition of layers *)

  Record compatlayer (D: compatdata) :=
    {
      cl_base_layer: ptree_layer compatsem (globvar Ctypes.type) D;
      cl_exec_load: res (option (load_accessor D));
      cl_exec_store: res (option (store_accessor D))
    }.

  Global Arguments cl_base_layer {D} _.
  Global Arguments cl_exec_load {D} _.
  Global Arguments cl_exec_store {D} _.

  Local Existing Instance ptree_layer_sim_op.
  Local Existing Instance ptree_layer_ops.
  Local Existing Instance ptree_layer_prf.

  Definition cl_empty (D: compatdata): compatlayer D :=
    {|
      cl_base_layer := ∅;
      cl_exec_load := OK None;
      cl_exec_store := OK None
    |}.

  Definition cl_oplus (D: compatdata) (L1 L2: compatlayer D) :=
    {|
      cl_base_layer := cl_base_layer L1 ⊕ cl_base_layer L2;
      cl_exec_load := cl_exec_load L1 ⊕ cl_exec_load L2;
      cl_exec_store := cl_exec_store L1 ⊕ cl_exec_store L2
    |}.

  Record cl_sim D1 D2 (R: path compatrel D1 D2) L1 L2 :=
    {
      cl_sim_layer:
        simRR D1 D2 R
          (cl_base_layer L1)
          (cl_base_layer L2);
      cl_sim_load:
        res_le (option_le (path_sim_eq load_accessor_sim D1 D2 R))
          (cl_exec_load L1)
          (cl_exec_load L2);
      cl_sim_store:
        res_le (option_le (path_sim_eq store_accessor_sim D1 D2 R))
          (cl_exec_store L1)
          (cl_exec_store L2)
    }.

  Local Arguments path_sim : simpl never.

  Global Instance cl_sim_htrans D1 D2 D3 R12 R23:
    HTransitive
      (cl_sim D1 D2 (path_inj R12))
      (cl_sim D2 D3 R23)
      (cl_sim D1 D3 (path_cons R12 R23)).
  Proof.
    intros [L1 l1 s1] [L2 l2 s2] [L3 l3 s3] [HL12 Hl12 Hs12] [HL23 Hl23 Hs23].
    constructor; simpl in *.
    * ehtransitivity.
      eapply HL12.
      eapply HL23.
    * ehtransitivity.
      eapply Hl12.
      eapply Hl23.
    * ehtransitivity.
      eapply Hs12.
      eapply Hs23.
  Qed.

  Global Instance cl_sim_rtrans D1 D2 D3 R12 R23:
    RTransitive
      (cl_sim D1 D2 (path_inj R12))
      (cl_sim D2 D3 R23)
      (cl_sim D1 D3 (path_cons R12 R23)).
  Proof.
    intros [L1 l1 s1] [L3 l3 s3] [HL13 Hl13 Hs13].
    unfold path_sim_eq in *; simpl in *.
    apply rtransitivity in HL13; destruct HL13 as (L2 & HL12 & HL23).
    apply rtransitivity in Hl13; destruct Hl13 as (l2 & Hl12 & Hl23).
    apply rtransitivity in Hs13; destruct Hs13 as (s2 & Hs12 & Hs23).
    exists {| cl_base_layer := L2; cl_exec_load := l2; cl_exec_store := s2 |}.
    split; constructor; assumption.
  Qed.

  Definition cl_inj {D} (L: ptree_layer compatsem (globvar Ctypes.type) D) :=
    {|
      cl_base_layer := L;
      cl_exec_load := OK None;
      cl_exec_store := OK None
    |}.

  Global Instance compatlayer_sim_op:
    Sim (path compatrel) compatlayer :=
    { simRR := cl_sim }.

  Global Instance cl_inj_monotonic:
    Proper (∀ -, (≤) ++> (≤)) (@cl_inj).
  Proof.
    intros D L1 L2 HL.
    split; try reflexivity.
    apply HL.
  Qed.

  Definition cl_inj_sim_monotonic:
    Proper (∀ R, sim R ++> sim R) (@cl_inj).
  Proof.
    intros D1 D2 R L1 L2 HL.
    split.
    * assumption.
    * repeat constructor.
    * repeat constructor.
  Qed.

  Local Instance cl_le_refl (D: compatdata):
    Reflexive (simRR D D path_nil).
  Proof.
    intros [L l s].
    constructor; simpl; reflexivity.
  Qed.

  Local Opaque ptree_layer_ops.
  Local Opaque ptree_layer_sim_op.
  Local Opaque path_ops.

  Local Instance cl_le_sim_compat D1 D2 D3 R12 R23:
    HTransitive (cl_sim D1 D2 R12) (cl_sim D2 D3 R23) (cl_sim D1 D3 (R23 ∘ R12)).
  Proof.
    intros [L1 l1 s1] [L2 l2 s2] [L3 l3 s3] [HL12 Hl12 Hs12] [HL23 Hl23 Hs23].
    constructor; simpl in *; ehtransitivity; eassumption.
  Qed.

  Global Instance compatlayer_quiv_sim_prf:
    CategorySim compatdata (path compatrel) compatlayer.
  Proof.
    split; try typeclasses eauto.
    - congruence.
  Qed.

  Global Instance compatlayer_ops:
    LayerOps ident compatsem (globvar Ctypes.type) compatlayer :=
    {
      layer_empty D := {| emptyset := cl_empty D |};
      layer_oplus D := {| oplus := cl_oplus D |};
      layer_mapsto_primitive D := {| mapsto i σ := cl_inj (i ↦ σ) |};
      layer_mapsto_globalvar D := {| mapsto i τ := cl_inj (i ↦ τ) |};
      get_layer_primitive D i L := get_layer_primitive i (cl_base_layer L);
      get_layer_globalvar D i L := get_layer_globalvar i (cl_base_layer L);
      layers_disjoint D1 D2 L1 L2 :=
        layers_disjoint (cl_base_layer L1) (cl_base_layer L2) /\
        (isOKNone (cl_exec_load L1) \/ isOKNone (cl_exec_load L2)) /\
        (isOKNone (cl_exec_store L1) \/ isOKNone (cl_exec_store L2));
      layer_wf D L :=
        (forall i σ,
          get_layer_primitive i (cl_base_layer L) = OK (Some (compatsem_inl σ))->
          ExtcallInvariants σ) /\
        (forall i σ,
          get_layer_primitive i (cl_base_layer L) = OK (Some (compatsem_inr σ))->
          PrimcallInvariants σ)
    }.
  Proof.
    typeclasses eauto.
  Defined.

  Local Opaque ptree_layer_sim_op.

  Global Instance compatlayer_pjoin:
    SimPseudoJoin compatdata (path compatrel) compatlayer cl_empty.
  Proof.
    split.
    * typeclasses eauto.
    * intros v1 v2 e x Hx.
      rewrite Hx; clear Hx.
      intros y; simpl.
      split.
      + apply lower_bound.
      + simpl. apply lower_bound.
      + simpl. apply lower_bound.
    * intros D1 D2 R.
      intros [L1 l1 s1] [L1' l1' s1'] [HL1 Hl1 Hs1]. 
      intros [L2 l2 s2] [L2' l2' s2'] [HL2 Hl2 Hs2].
      constructor; simpl in *.
      + apply oplus_sim_monotonic;
        solve_monotonic.
      + destruct Hl1 as [l1 l1' Hl1 | err l1']; repeat constructor; monad_norm.
        destruct Hl2 as [l2 l2' Hl2 | err l2']; repeat constructor; monad_norm.
        destruct Hl1 as [l1' | l1 l1' Hl1].
        - destruct Hl2 as [l2' | l2 l2' Hl2], l1', l2'; repeat constructor.
          assumption.
        - destruct Hl2 as [l2' | l2 l2' Hl2], l1', l2'; repeat constructor.
          assumption.
      + destruct Hs1 as [s1 s1' Hs1 | err s1']; repeat constructor; monad_norm.
        destruct Hs2 as [s2 s2' Hs2 | err s2']; repeat constructor; monad_norm.
        destruct Hs1 as [s1' | s1 s1' Hs1].
        - destruct Hs2 as [s2' | s2 s2' Hs2], s1', s2'; repeat constructor.
          assumption.
        - destruct Hs2 as [s2' | s2 s2' Hs2], s1', s2'; repeat constructor.
          assumption.
    * intros v x Hx.
      rewrite Hx; clear Hx.
      intros y; simpl.
      split; simpl.
      + rewrite id_left.
        simpl.
        change path_nil with (id (A := path compatrel v v)).
        reflexivity.
      + monad_norm.
        destruct (cl_exec_load y) as [[|]|]; repeat constructor.
      + monad_norm.
        destruct (cl_exec_store y) as [[|]|]; repeat constructor.

    * intros D x y z.
      split; simpl.
      + rewrite associativity.
        change path_nil with (id (A := path compatrel D D)).
        reflexivity.
      + destruct (cl_exec_load x) as [[|]|],
                 (cl_exec_load y) as [[|]|],
                 (cl_exec_load z) as [[|]|];
        repeat constructor.
      + destruct (cl_exec_store x) as [[|]|],
                 (cl_exec_store y) as [[|]|],
                 (cl_exec_store z) as [[|]|];
        repeat constructor.
    * intros D x y.
      split; simpl.
      + rewrite commutativity.
        change path_nil with (id (A := path compatrel D D)).
        reflexivity.
      + destruct (cl_exec_load x) as [[|]|],
                 (cl_exec_load y) as [[|]|];
        repeat constructor.
      + destruct (cl_exec_store x) as [[|]|],
                 (cl_exec_store y) as [[|]|];
        repeat constructor.
    * intros D x y.
      split; simpl.
      + change path_nil with (id (A := path compatrel D D)).
        apply left_upper_bound.
      + destruct (cl_exec_load x) as [[|]|],
                 (cl_exec_load y) as [[|]|];
        repeat constructor.
      + destruct (cl_exec_store x) as [[|]|],
                 (cl_exec_store y) as [[|]|];
        repeat constructor.
  Qed.

  (*Local Transparent ptree_layer_quiv_sim_ops.*)

  Global Instance compatlayer_prf:
    Layers ident compatsem (globvar Ctypes.type) compatlayer.
  Proof.
    split.
    * typeclasses eauto.
    * intros D1 D2 R i σ1 σ2 Hσ.
      split; simpl.
      + apply layer_sim_intro; assumption.
      + repeat constructor.
      + repeat constructor.
    * intros D i.
      simpl.
      apply get_layer_primitive_empty.
    * intros D i σ.
      simpl.
      apply get_layer_primitive_mapsto.
    * intros D i j σ Hij.
      simpl.
      apply get_layer_primitive_mapsto_other_primitive.
      assumption.
    * intros D i j τ.
      simpl.
      apply get_layer_primitive_mapsto_globalvar.
    * intros D i L1 L2.
      simpl.
      apply get_layer_primitive_oplus.
    * intros D1 D2 R i L1 L2 [HL _ _].
      simpl.
      solve_monotonic.

    * intros D i.
      simpl.
      apply get_layer_globalvar_empty.
    * intros D i σ.
      simpl.
      apply get_layer_globalvar_mapsto.
    * intros D i j σ Hij.
      simpl.
      apply get_layer_globalvar_mapsto_other_globalvar.
      assumption.
    * intros D i j τ.
      simpl.
      apply get_layer_globalvar_mapsto_primitive.
    * intros D i L1 L2.
      simpl.
      apply get_layer_globalvar_oplus.
    * intros D1 D2 R i L1 L2 [HL _ _].
      simpl.
      solve_monotonic.

    * split.
      + apply layers_disjoint_empty.
      + simpl.
        split; left; reflexivity.
    * intros D D' R [L l s] [L1 l1 s1] [L2 l2 s2] (HL2 & Hl2 & Hs2) [HL Hload Hstore].
      split; simpl in *.
      + eapply layer_sim_cancel_disjoint;
        eassumption.
      + unfold isOKNone in *.
        destruct Hl2; subst.
        - apply lower_bound.
        - destruct l1 as [[|]|]; monad_norm; eauto with liblayers.
      + unfold isOKNone in *.
        destruct Hs2; subst.
        - apply lower_bound.
        - destruct s1 as [[|]|]; monad_norm; eauto with liblayers.

    * intros D L1 L2 [HL1e HL1p] [HL2e HL2p].
      split;
        intros i σ;
        try specialize (HL1e i σ);
        try specialize (HL1p i σ);
        try specialize (HL2e i σ);
        try specialize (HL2p i σ);
        simpl in *;
        get_layer_normalize;
        destruct (get_layer_primitive i (cl_base_layer L1)) as [[[|]|]|];
        destruct (get_layer_primitive i (cl_base_layer L2)) as [[[|]|]|];
        inversion 1; subst;
        eauto.
  Qed.

  (** Convenient shortcut for defining variables as [v ↦ cvar τ]. *)

  Definition cvar (τ: Ctypes.type): globvar Ctypes.type :=
    {|
      gvar_info := τ;
      gvar_init := nil;
      gvar_readonly := false;
      gvar_volatile := false
    |}.

  (** Elementary layers for memory accessors *)

  Definition cl_load_accessor {D} exec_load `{!LoadAccessor D exec_load} :=
    {|
      cl_base_layer := ∅;
      cl_exec_load := OK (Some {| exec_load_sem := exec_load |});
      cl_exec_store := OK None
    |}.

  Definition cl_store_accessor {D} exec_store `{!StoreAccessor D exec_store} :=
    {|
      cl_base_layer := ∅;
      cl_exec_load := OK None;
      cl_exec_store := OK (Some {| exec_store_sem := exec_store |})
    |}.

  Lemma cl_load_accessor_sim_intro D1 D2 R el1 el2:
    forall `{Hel1: LoadAccessor D1 el1} `{Hel2: LoadAccessor D2 el2},
      load_accessor_sim_def D1 D2 R el1 el2 ->
      sim (path_inj R) (cl_load_accessor el1) (cl_load_accessor el2).
  Proof.
    intros Hel1 Hel2 H.
    constructor; simpl.
    * apply lower_bound.
    * eauto with liblayers.
    * eauto with liblayers.
  Qed.

  Lemma cl_store_accessor_sim_intro D1 D2 R es1 es2:
    forall `{Hes1: StoreAccessor D1 es1} `{Hes2: StoreAccessor D2 es2},
      store_accessor_sim_def D1 D2 R es1 es2 ->
      sim (path_inj R) (cl_store_accessor es1) (cl_store_accessor es2).
  Proof.
    intros Hel1 Hel2 H.
    constructor; simpl.
    * apply lower_bound.
    * eauto with liblayers.
    * eauto with liblayers.
  Qed.

  (** Same, as a single bundled thing with a ↦ syntax. *)

  Record cl_accessors D :=
    {
      exec_load: load_accessor_sem D;
      exec_store: store_accessor_sem D;
      exec_load_properties: LoadAccessor D exec_load;
      exec_store_properties: StoreAccessor D exec_store
    }.

  Global Arguments exec_load {D} _ _ _ _ _ _ _ _ _.
  Global Arguments exec_store {D} _ _ _ _ _ _ _ _ _ _.
  Global Existing Instance exec_load_properties.
  Global Existing Instance exec_store_properties.

  Inductive cl_accessors_name := accessors.

  Global Instance cl_accessors_mapsto D:
    Mapsto cl_accessors_name (cl_accessors D) (compatlayer D) :=
    {
      mapsto name acc :=
        cl_load_accessor (exec_load acc) ⊕
        cl_store_accessor (exec_store acc)
    }.

  Lemma cl_accessors_sim_intro D1 D2 R acc1 acc2:
    load_accessor_sim_def D1 D2 R (exec_load acc1) (exec_load acc2) ->
    store_accessor_sim_def D1 D2 R (exec_store acc1) (exec_store acc2) ->
    sim (path_inj R) (accessors ↦ acc1) (accessors ↦ acc2).
  Proof.
    intros Hload Hstore.
    unfold mapsto, cl_accessors_mapsto.
    apply oplus_sim_monotonic.
    * apply cl_load_accessor_sim_intro.
      assumption.
    * apply cl_store_accessor_sim_intro.
      assumption.
  Qed.
End WITH_MEMORY_MODEL.
