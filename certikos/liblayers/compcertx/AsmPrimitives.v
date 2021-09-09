Require Import compcert.lib.Coqlib.
Require Import compcert.common.Memtype.
Require Import compcert.common.AST.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import liblayers.lib.Decision.
Require Import coqrel.LogicalRelations.
Require Import liblayers.logic.PseudoJoin.
Require Import liblayers.logic.LayerData.
Require Import liblayers.logic.Primitives.
Require Export liblayers.compcertx.CompcertStructures.
Require Import liblayers.compcertx.ErrorMonad.
Require Import compcert.x86.Asm.
Require Import compcertx.x86.AsmX.
Require Import SimulationRelation.
Require Import SimrelInvariant.
Require Import SimAsmRegset.
Require Export liblayers.compcertx.AsmGlobalVars.

Infix "×" := prod_rel (right associativity, at level 45) : signature_scope.

Open Scope rel_scope.

Section EQUIV.
  Context `{SimulationRelationEquivalence}.

  Lemma match_regset_simrel_equiv_fw p1:
    subrel (regset_match R1 p1) (regset_match R2 (simrel_equiv_fw f p1)).
  Proof.
    unfold regset_match.
    rstep. apply match_val_simrel_equiv_fw.
  Qed.

  Lemma match_regset_simrel_equiv_bw p2:
    subrel (regset_match R2 p2) (regset_match R1 (simrel_equiv_bw f p2)).
  Proof.
    unfold regset_match.
    rstep; apply match_val_simrel_equiv_bw.
  Qed.

End EQUIV.


(** * Assembly-style primitives *)

Section ASMPRIMITIVE.
  Context `{Hmem: BaseMemoryModel}.

  (** ** Definition *)

  Definition asmprim_sem D :=
    regset * mwd D -> regset * mwd D -> Prop.

  Record asmprimitive (D: layerdata) :=
    {
      asmprimitive_step:
        asmprim_sem D
      ;
      asmprimitive_step_wt rs m rs' m' :
        asmprimitive_step (rs, m) (rs', m') ->
        wt_regset rs ->
        wt_regset rs'
    }.

  (** ** Invariant *)

  Record asmprim_inv (wt: bool) (D: layerdata) (rs: regset) (m: mem) (d: D) :=
    {
      asmprim_inv_inv:
        data_inv d;
      asmprim_inv_valid:
        (glob_threshold <= Mem.nextblock m)%positive;
      asmprim_inv_mem_wf:
        Mem.inject_neutral (Mem.nextblock m) m;
      admprim_inv_data_wf:
        data_inject (Mem.flat_inj (Mem.nextblock m)) d d;
      asmprim_inv_reg_wf r:
        Val.inject (Mem.flat_inj (Mem.nextblock m)) (rs r) (rs r);
      asmprim_inv_reg_wt:
        wt = true ->
        wt_regset rs
    }.

  Lemma asmprim_inv_false_intro b D rs m d:
    asmprim_inv b D rs m d ->
    asmprim_inv false D rs m d.
  Proof.
    inversion 1; subst; constructor; auto; discriminate.
  Qed.

  Lemma asmprim_inv_true_elim b D rs m d:
    asmprim_inv true D rs m d ->
    asmprim_inv b D rs m d.
  Proof.
    inversion 1; subst; constructor; auto; discriminate.
  Qed.

  Lemma asmprim_inv_true_intro b D rs m d:
    asmprim_inv b D rs m d ->
    wt_regset rs ->
    asmprim_inv true D rs m d.
  Proof.
    inversion 1; subst; constructor; auto.
  Qed.

  Class AsmPrimitivePreservesInvariant D (σ: asmprimitive D) :=
    {
      asmprim_preserves_invariant rs m d rs' m' d':
        asmprimitive_step D σ (rs, (m, d)) (rs', (m', d')) ->
        asmprim_inv true D rs m d ->
        asmprim_inv false D rs' m' d';
      asmprim_nextblock_incr rs m d rs' m' d':
        asmprimitive_step D σ (rs, (m, d)) (rs', (m', d')) ->
        asmprim_inv true D rs m d ->
        (Mem.nextblock m <= Mem.nextblock m')%positive
    }.

  (** ** Determinisim *)

  Class AsmPrimitiveDeterministic D (σ: asmprimitive D) :=
    {
      asmprim_deterministic s s1 s2:
        asmprimitive_step D σ s s1 ->
        asmprimitive_step D σ s s2 ->
        s1 = s2
    }.

  (** ** Simulations *)

  Definition asmprim_match_state_wt D1 D2 (R: simrel D1 D2) p := 
    wt_regset_match R p * match_mem R p.

  Definition asmprim_match_state D1 D2 (R: simrel D1 D2) p := 
    regset_match R p * match_mem R p.

  Global Instance asmprim_match_state_erase_type D1 D2 R p:
    Related
      (asmprim_match_state_wt D1 D2 R p)
      (asmprim_match_state D1 D2 R p)
      subrel.
  Proof.
    unfold asmprim_match_state_wt, asmprim_match_state.
    solve_monotonic.
  Qed.

  Global Instance asmprim_match_state_erase_type_params_wt:
    Params (@asmprim_match_state_wt) 2.

  Global Instance asmprim_match_state_erase_type_params:
    Params (@asmprim_match_state) 2.

  Record asmprim_sim D1 D2 (R: simrel D1 D2) σ1 σ2 :=
    {
      asmprim_sim_step p:
        Related
          (asmprimitive_step D1 σ1)
          (asmprimitive_step D2 σ2)
          (asmprim_match_state_wt D1 D2 R p ++>
           set_rel (incr p (asmprim_match_state D1 D2 R p)))
    }.

  Global Instance asmprimitive_step_sim:
    Monotonic
      asmprimitive_step
      (forallr R @ D1 D2, asmprim_sim D1 D2 R ++>
       rforall w, asmprim_match_state_wt D1 D2 R w ++>
       set_rel (incr w (asmprim_match_state_wt D1 D2 R w))).
  Proof.
    solve_monotonic.
    intros s1' Hs1'.
    edestruct asmprim_sim_step as (s2' & Hs2' & w' & Hw' & Hrs' & Hm'); eauto.
    eexists; split; solve_monotonic.
    eexists; split; solve_monotonic.
    split; eauto. 
    eapply wt_regset_match_intro; eauto.
    destruct s2', y0, H0.
    eapply asmprimitive_step_wt; eauto.
    eapply wt_regset_match_elim; eauto.
  Qed.

  (** Compatibility with [simrel_equiv]. *)

  Global Instance asmprim_sim_proper:
    Monotonic asmprim_sim (forallr -, forallr -, simrel_equiv ++> subrel).
  Proof.
    repeat red.
    intros D D' R1 R2 H pr pr' H0.
    destruct H as [s H].
    inversion H0.
    constructor; auto.
    repeat red.
    intros p2 x y H1 a H2.
    assert ((wt_regset_match R1 (simrel_equiv_bw s p2) * match_mem R1 (simrel_equiv_bw s p2))%rel x y) as INIT1.
    {
      unfold wt_regset_match in *.
      destruct H1 as (Hrs & Hm).
      split; intros; eauto.
      rstep.
      eapply match_val_of_type_simrel_equiv_bw; eauto.
      eapply match_mem_simrel_equiv_bw; eauto.
    }
    specialize (asmprim_sim_step0 _ _ _ INIT1 _ H2).
    destruct asmprim_sim_step0 as (b & STEP & FIN1).
    red in FIN1.
    destruct FIN1 as (p1' & INCR1 & FIN1).
    inversion FIN1.
    apply simrel_equiv_le_fw in INCR1.
    esplit.
    split; eauto.
    esplit.
    split; eauto.
    etransitivity. apply simrel_fw_bw_le. eauto.
    unfold asmprim_match_state, regset_match in *.
    split; intros; eauto.
    rstep.
    eapply match_val_simrel_equiv_fw; eauto.
    eapply match_mem_simrel_equiv_fw; eauto.
  Qed.

  (** ** User diagrams  *)

  (** *** Identity diagram  *)

  (** When using [simrel_id], [asmprim_sim_inv] is a consequence of
    [asmprim_sim_step], and so we only need to prove the latter.
    We can also simplify the simulation diagram further thanks to the
    fact that the simulation relation boils down to [eq]. *)

  Lemma asmprim_sim_id_intro D σ1 σ2:
    (- ==> - ==> impl) (asmprimitive_step D σ1) (asmprimitive_step D σ2) ->
    asmprim_sim D D simrel_id σ1 σ2.
  Proof.
    intros Hσ.
    split.
    - intros [].
      intros [rs1 [m1 d1]] [rs [m d]] [Hrs Hm].
      simpl in *.
      inversion Hm; clear Hm; subst.
      generalize Hrs. intro Hrs_.
      apply wt_regset_match_subrel in Hrs.
      rewrite regset_match_id in Hrs; subst.
      intros s' Hs'.
      exists s'.
      split.
      + revert Hs'.
        rauto.
      + exists tt.
        split; auto.
        split; auto.
        rewrite regset_match_id in *.
        reflexivity.
        reflexivity.
  Qed.

  (** ** Categorical properties  *)

  Global Instance asmprim_sim_refl D:
    Reflexive (asmprim_sim D D simrel_id).
  Proof.
    intros σ.
    eapply asmprim_sim_id_intro.
    reflexivity.
  Qed.

Require Import ExtensionalityAxioms.

Lemma prod_rel_compose {A1 A2 B1 B2 C1 C2} RAB1 RAB2 RBC1 RBC2:
  prod_rel (rel_compose RAB1 RBC1) (rel_compose RAB2 RBC2) =
  @rel_compose (A1*A2) (B1*B2) (C1*C2) (prod_rel RAB1 RAB2) (prod_rel RBC1 RBC2).
Proof.
  clear.
  eapply eqrel_eq; split.
  - intros [a1 a2] [c1 c2] [(b1 & Hab1 & Hbc1) (b2 & Hab2 & Hbc2)]; simpl in *.
    exists (b1, b2).
    split; constructor; assumption.
  - firstorder.
Qed.

  Lemma asmprim_match_state_wt_compose D1 D2 D3 R12 R23 w12 w23:
    asmprim_match_state_wt D1 D3 (simrel_compose R12 R23) (w12, w23) =
    rel_compose
      (asmprim_match_state_wt D1 D2 R12 w12)
      (asmprim_match_state_wt D2 D3 R23 w23).
  Proof.
    unfold asmprim_match_state_wt; simpl.
    rewrite wt_regset_match_compose, prod_rel_compose.
    reflexivity.
  Qed.

  Lemma asmprim_match_state_compose D1 D2 D3 R12 R23 w12 w23:
    asmprim_match_state D1 D3 (simrel_compose R12 R23) (w12, w23) =
    rel_compose
      (asmprim_match_state D1 D2 R12 w12)
      (asmprim_match_state D2 D3 R23 w23).
  Proof.
    unfold asmprim_match_state; simpl.
    rewrite regset_match_compose, prod_rel_compose.
    reflexivity.
  Qed.

  Global Instance asmprim_sim_htrans D1 D2 D3 R12 R23:
    HTransitive
      (asmprim_sim D1 D2 R12)
      (asmprim_sim D2 D3 R23)
      (asmprim_sim D1 D3 (simrel_compose R12 R23)).
  Proof.
    intros σ1 σ2 σ3 Hσ12 Hσ23.
    constructor.
    intros [w12 w23] s1 s3 Hs13.
    rewrite asmprim_match_state_wt_compose in Hs13.
    destruct Hs13 as (s2 & Hs12 & Hs23).
    eapply @htransitivity.
    - apply set_rel_htrans.
      apply rel_incr_htrans.
      + intros.
        rewrite (asmprim_match_state_compose D1 D2 D3 R12 R23 wab wbc).
        typeclasses eauto.
      + red. solve_monotonic.
    - solve_monotonic.
    - solve_monotonic.
  Qed.

  Global Instance asmprim_sim_ops: Sim simrel asmprimitive :=
    {
      simRR := asmprim_sim
    }.

  Global Instance asmprim_sim_prf:
    CategorySim layerdata simrel asmprimitive.
  Proof.
    split; typeclasses eauto.
  Qed.

  (** ** Union *)

  Definition asmprim_union_sem D (σ1 σ2: asmprim_sem D): asmprim_sem D :=
    fun s s' => (σ1 s s' \/ σ2 s s')%type.

  Program
  Definition asmprim_union D (σ1 σ2: asmprimitive D): asmprimitive D :=
    {|
      asmprimitive_step :=
        asmprim_union_sem D
          (asmprimitive_step D σ1)
          (asmprimitive_step D σ2)
    |}.
  Next Obligation.
    destruct H; eauto using asmprimitive_step_wt.
  Qed.

  Lemma asmprim_union_ub_l D σ1 σ2:
    asmprim_sim D D id σ1 (asmprim_union D σ1 σ2).
  Proof.
    eapply asmprim_sim_id_intro; simpl.
    repeat red.
    clear; intros; tauto.
  Qed.

  Lemma asmprim_union_ub_r D σ1 σ2:
    asmprim_sim D D id σ2 (asmprim_union D σ1 σ2).
  Proof.
    eapply asmprim_sim_id_intro; simpl.
    repeat red.
    clear; intros; tauto.
  Qed.

  Lemma asmprim_union_intro D D' R σ σ1 σ2:
    asmprim_sim D D' R σ1 σ ->
    asmprim_sim D D' R σ2 σ ->
    asmprim_sim D D' R (asmprim_union D σ1 σ2) σ.
  Proof.
    intros H1 H2.
    constructor.
    intros w s1 s2 Hs s1' Hs1; simpl in *.
    destruct Hs1 as [Hs1|Hs1].
    + eapply H1; eauto.
    + eapply H2; eauto.
  Qed.

  (** ** [Primitives] instance *)

  Global Instance asmprim_ops: PrimitiveOps asmprimitive :=
    {
      prim_union D := {| oplus := asmprim_union D |}
    }.

  Local Instance asmprim_union_prf:
    SimJoin layerdata simrel asmprimitive.
  Proof.
    intros D σ1 σ2.
    split.
    - apply asmprim_union_ub_l.
    - apply asmprim_union_ub_r.
    - intros.
      apply asmprim_union_intro; eauto.
  Qed.

  Global Instance asmprim_prf:
    Primitives asmprimitive.
  Proof.
    split; try typeclasses eauto.
  Qed.
    

  Require Import liblayers.logic.PTreeLayers.

End ASMPRIMITIVE.

  (* Contrary to C layers, assembly layers do not carry
     any type information on global variables. *)

  Notation asmlayer := (ptree_layer asmprimitive (globvar unit)).

Section ASMLAYERS.
  Context `{Hmem: BaseMemoryModel}.

  Global Instance asmlayer_ops:
    LayerOps ident asmprimitive (globvar unit) asmlayer
    :=
      ptree_layer_ops.

  Global Instance asmlayer_sim_op:
    Sim simrel asmlayer :=
    ptree_layer_sim_op.

  Global Instance asmlayer_prf:
    Layers ident asmprimitive (globvar unit) asmlayer
    :=
      ptree_layer_prf.

End ASMLAYERS.

(** * Relation between [inv] and [asmprim_inv] *)

Section INVARIANT.
  Context `{Hmem: BaseMemoryModel}.

  Global Instance inv_regset_match_eq D p:
    Coreflexive (regset_match (inv (D:=D)) p).
  Proof.
    intros rs1 rs2 Hrs.
    apply functional_extensionality; intro r.
    apply (coreflexivity _ _ (Hrs r)).
  Qed.

Lemma Ple_lub a b:
  (forall c, Plt c a -> Plt c b) <->
  Ple a b.
Proof.
  split; [ | intros; xomega ].
  intros H.
  destruct (peq a 1) as [ | NE ]; try xomega.
  generalize (Ppred_Plt _ NE). intro LT.
  specialize (H _ LT).
  revert LT.
  replace a with (Pos.succ (Pos.pred a)) at 2 3; [ xomega | ] .
  apply Pos.succ_pred.
  assumption.
Qed.

  Lemma inv_asmprim_inv D rs m d s p:
    asmprim_match_state_wt D D inv p (rs, (m, d)) s ->
    asmprim_inv true D rs m d /\ proj1_sig p = Mem.nextblock m /\ (rs, (m, d)) = s.
  Proof.
    intros [Hrs Hm]; simpl in *.
    assert ((rs, (m, d)) = s).
    {
      destruct s as [srs sm].
      simpl in *.
      apply wt_regset_match_subrel in Hrs.
      f_equal.
      solve_monotonic.
      solve_monotonic.
    }
    subst.
    inversion Hm; clear Hm; subst.
    split; eauto.
    split; eauto.
    - (* TODO: rephrase [asmprim_inv] with [block_is_global] instead of [glob_threshold] *)
      rewrite <- Ple_lub.
      tauto.
    - intro r; specialize (Hrs r).
      eapply inv_match_val_inject_neutral; eauto.
      * simpl in Hrs.
        apply SimValues.match_val_erase_type in Hrs.
        eapply Hrs.
      * reflexivity.
    - intros _.
      revert Hrs.
      apply wt_regset_match_elim.
  Qed.

  Lemma asmprim_inv_asminv D rs m d p:
    asmprim_inv true D rs m d ->
    proj1_sig p = Mem.nextblock m ->
    Proper
      (asmprim_match_state_wt D D inv p)
      (rs, (m, d)).
  Proof.
    intros Hinv Hp.
    destruct Hinv.
    specialize (asmprim_inv_reg_wt0 (eq_refl _)).
    split; simpl.
    - intros r.
      eapply SimValues.match_val_of_type_intro; eauto.
      apply inv_inject_neutral_match_val; eauto.
      rewrite Hp; eauto.
    - destruct p as [thr Hthr].
      simpl in Hp; subst.
      econstructor; eauto.
  Qed.

  Global Instance asmprim_asminv D σ:
    AsmPrimitivePreservesInvariant D σ ->
    Proper (asmprim_sim D D inv) σ.
  Proof.
    intros Hσ.
    constructor; try tauto.
    intros p (rs1 & m1 & d1) (rs & m & d) Hs.
    pose proof Hs as [Hrs Hm]; simpl in *.
    apply inv_asmprim_inv in Hs.
    destruct Hs as [Hinv _].
    generalize Hrs. intro Hrs_.
    apply wt_regset_match_subrel in Hrs.
    apply inv_regset_match_eq in Hrs.
    inversion Hm; clear Hm; subst.
    intros s' Hs'.
    exists s'.
    split; eauto.
    destruct s' as (rs' & m' & d').
    pose proof Hs' as Hinvp.
    eapply asmprim_preserves_invariant in Hinvp; eauto.
    destruct Hinvp as [Hinv' Hnb' Hmwf' Hrwf' Hrwt'].
    clear asmprim_inv_reg_wt0.
    assert (wt_regset rs') as asmprim_inv_reg_wt0.
    {
      eapply asmprimitive_step_wt; eauto.
      revert Hrs_.
      apply wt_regset_match_elim.
    }
    (* TODO: rephrase [asmprim_inv] using [block_is_global] instead of [glob_threshold] *)
    rewrite <- Ple_lub in Hnb'.
    exists (exist _ _ Hnb').
    split.
    - simpl; unfold RelCompFun; simpl.
      eapply asmprim_nextblock_incr; eauto.
    - split.
      + intros r.
        apply inv_inject_neutral_match_val; eauto.
      + simpl.
        constructor; eauto.
  Qed.

  Lemma inv_asmprim D σ:
    Proper (asmprim_sim D D inv) σ ->
    AsmPrimitivePreservesInvariant D σ.
  Proof.
    intros Hσ.
    split.
    - intros rs m d rs' m' d' Hstep Hinv.
      pose proof (asmprim_inv_valid _ D rs m d Hinv) as Hnb.
      (* TODO: rephrase [asmprim_inv] using [block_is_global] instead of [glob_threshold] *)
      rewrite <- Ple_lub in Hnb.     
      pose (p := exist _ _ Hnb : simrel_world (inv (D:=D))).
      edestruct (asmprimitive_step_sim D D inv σ σ Hσ p)
        as (s' & Hs' & p' & Hp' & Hstep'); eauto.
      + edestruct (asmprim_inv_asminv D rs m d p); eauto.
        constructor; eauto.
      + edestruct inv_asmprim_inv; eauto using asmprim_inv_true_elim.
    - intros rs m d rs' m' d' Hstep Hinv.
      (* TODO: rephrase [asmprim_inv] using [block_is_global] instead of [glob_threshold] *)
      assert (H: forall b, block_is_global b -> (b < Mem.nextblock m)%positive).
      {
        Local Transparent block_is_global.
        unfold block_is_global.
        Local Opaque block_is_global.
        rewrite Ple_lub.
        eapply asmprim_inv_valid; eauto.
      }
      edestruct asmprimitive_step_sim as (s' & Hs' & w' & Hw' & Hstep'); eauto.
      + instantiate (2 := exist _ _ H).
        eapply asmprim_inv_asminv; eauto.
      + simpl in Hw'.
        eapply inv_asmprim_inv in Hstep'.
        destruct Hstep' as (_ & Hnb' & _).
        destruct w'.
        simpl in *.
        subst.
        assumption.
  Qed.

  (** ** Adding invariants to a simulation relation *)

  Definition wrapinv {D1 D2} (R: simrel D1 D2): simrel D1 D2 :=
    inv ∘ R ∘ inv.

  (** Maybe we'll need something like this for the refinement proofs,
    depending on how things pan out. *)

  Inductive asmprim_inv_match_state D1 D2 R p:
    rel (regset * mwd D1)%type (regset * mwd D2)%type :=
    | asmprimitive_match_intro rs1 m1 d1 rs2 m2 d2:
        asmprim_inv true D1 rs1 m1 d1 ->
        asmprim_inv true D2 rs2 m2 d2 ->
        asmprim_match_state D1 D2 R p (rs1, (m1, d1)) (rs2, (m2, d2)) ->
        asmprim_inv_match_state D1 D2 R p (rs1, (m1, d1)) (rs2, (m2, d2)).

  Definition asmprim_inv_sim D1 D2 R: rel (asmprim_sem D1) (asmprim_sem D2) :=
    rforall p,
      asmprim_inv_match_state D1 D2 R p ++>
      set_rel (incr p (asmprim_match_state D1 D2 R p)).

  Global Instance asmprim_inv_sem_sim_rintro D1 D2 R σ1 σ2:
    RIntro _ (asmprim_inv_sim D1 D2 R) σ1 σ2 :=
    rel_all_rintro _ _ _.

  Global Instance asmprim_inv_sem_sim_relim D1 D2 R σ1 σ2 P Q:
    _ -> RElim (asmprim_inv_sim D1 D2 R) σ1 σ2 _ _ :=
    rel_all_relim _ _ _ P Q.

  Lemma asmprim_inv_sim_wrapinv_intro D1 D2 R σ1 σ2:
    AsmPrimitivePreservesInvariant D1 σ1 ->
    AsmPrimitivePreservesInvariant D2 σ2 ->
    asmprim_inv_sim D1 D2 R (asmprimitive_step _ σ1) (asmprimitive_step _ σ2) ->
    asmprim_sim D1 D2 (wrapinv R) σ1 σ2.
  Proof.
    intros H H0 H1.
    unfold asmprim_inv_sim in H1.
    unfold wrapinv.
    constructor.
    intros p s1 s2 Hs.
    destruct p as (pinv1 & p & pinv2).
    simpl in Hs.
    rewrite asmprim_match_state_wt_compose in Hs.
    rewrite asmprim_match_state_wt_compose in Hs.
    destruct Hs as (si1 & Hsi1 & si2 & Hsi & Hsi2).
    destruct s1 as [rs1 m1].
    destruct si1 as [rsi1 mi1].
    inversion Hsi1.
    simpl in * |- .
    match goal with
        K: wt_regset_match _ _ _ _ |- _ =>
        generalize K; intro Hrs1;
        apply wt_regset_match_subrel in K;
        apply inv_regset_match_eq in K;
        subst
    end.
    generalize (match_mem_inv_eq D1). intro INV1.
    simpl in INV1.
    match goal with
        K: inv_match_mem _ _ _ _ |- _ =>
        generalize K; intro Hm1; apply INV1 in K; subst; clear INV1
    end.
    destruct s2 as [rs2 m2].
    destruct si2 as [rsi2 mi2].
    inversion Hsi2.
    simpl in * |- .
    match goal with
        K: wt_regset_match _ _ _ _ |- _ =>
        generalize K; intro Hrs2;
        apply wt_regset_match_subrel in K;
        apply inv_regset_match_eq in K;
        subst
    end.
    generalize (match_mem_inv_eq D2). intro INV2.
    simpl in INV2.
    match goal with
        K: inv_match_mem _ _ _ _ |- _ =>
        generalize K; intro Hm2; apply INV2 in K; subst; clear INV2
    end.
    assert (asmprim_inv_match_state D1 D2 R p (rsi1, mi1) (rs2, m2)) as INIT.
    {
      destruct mi1 as [mi1 d1].
      destruct m2 as [mi2 d2].
      constructor; auto.
      + eapply inv_asmprim_inv; eauto.
      + eapply inv_asmprim_inv; eauto.
      + rauto.
    }
    specialize (H1 _ _ _ INIT); clear INIT.
    intros [rs1' m1'] Hs1.
    specialize (H1 _ Hs1).
    destruct H1 as ( [rs2' m2'] & Hs' & p' & Hp' & FIN).
    esplit.
    split; eauto.
    destruct mi1 as [m1 d1].
    destruct m1' as [m1' d1'].
    destruct m2 as [m2 d2].
    destruct m2' as [m2' d2'].

    exploit (asmprim_preserves_invariant (D := D1)); eauto.
    { eapply inv_asmprim_inv; eauto. }
    intro Hinv1'.
    assert (Mem.nextblock m1 <= Mem.nextblock m1')%positive as Hnb1.
    {
      eapply (asmprim_nextblock_incr (D := D1)); eauto.
      eapply inv_asmprim_inv; eauto.
    }
    assert (wt_regset rs1') as Hwt1'.
    {
      eapply asmprimitive_step_wt; eauto.
      revert Hrs1. apply wt_regset_match_elim.
    }
    exploit asmprim_inv_true_intro; eauto.
    clear Hinv1'. intro Hinv1'.
    assert (proj1_sig pinv1 = Mem.nextblock m1) as Hpinv1.
    {
      eapply inv_asmprim_inv; eauto.
    }
    assert (exists pinv1' : inv_world, proj1_sig pinv1' = Mem.nextblock m1' ) as INV1.
    {
      destruct pinv1 as [? HN]. simpl in Hpinv1. subst.
      assert (forall b, block_is_global b -> (b < Mem.nextblock m1')%positive) as HN'.
      {
        intros b H1.
        apply HN in H1.
        xomega.
      }
      exists (exist _ _ HN').
      reflexivity.
    }
    destruct INV1 as (pinv1' & Hpinv1').

    exploit (asmprim_preserves_invariant (D := D2)); eauto.
    { eapply inv_asmprim_inv; eauto. }
    intro Hinv2'.
    assert (Mem.nextblock m2 <= Mem.nextblock m2')%positive as Hnb2.
    {
      eapply (asmprim_nextblock_incr (D := D2)); eauto.
      eapply inv_asmprim_inv; eauto.
    }
    assert (wt_regset rs2') as Hwt2'.
    {
      eapply asmprimitive_step_wt; eauto.
      revert Hrs2. apply wt_regset_match_elim.
    }
    exploit asmprim_inv_true_intro; eauto.
    clear Hinv2'. intro Hinv2'.
    assert (proj1_sig pinv2 = Mem.nextblock m2) as Hpinv2.
    {
      eapply inv_asmprim_inv; eauto.
    }
    assert (exists pinv2' : inv_world, proj1_sig pinv2' = Mem.nextblock m2' ) as INV2.
    {
      destruct pinv2 as [? HN]. simpl in Hpinv2. subst.
      assert (forall b, block_is_global b -> (b < Mem.nextblock m2')%positive) as HN'.
      {
        intros b H1.
        apply HN in H1.
        xomega.
      }
      exists (exist _ _ HN').
      reflexivity.
    }
    destruct INV2 as (pinv2' & Hpinv2').

    exists (pinv1', (p', pinv2')).
    split.
    {
      split; simpl.
      { red. xomega. }
      split; simpl; auto.
      red; xomega.
    }
    simpl.
    repeat rewrite asmprim_match_state_compose.
    esplit.
    split.
    {
      apply asmprim_match_state_erase_type.
      apply asmprim_inv_asminv; auto.
    }
    esplit.
    split.
    { eassumption. }
    apply asmprim_match_state_erase_type.
    apply asmprim_inv_asminv; auto.
  Qed.

  (** The "wrapped" version does not require the invariant
    preconditions of [asmprim_match_state], since those are now
    built into the simulation relation. *)

  Global Instance asmprim_match_state_wrapinv_intro D1 D2 R p:
    Related
      (wt_regset_match (wrapinv R) p * match_mem (wrapinv R) p)
      (asmprim_inv_match_state D1 D2 (wrapinv R) p)
      subrel.
  Proof.
    intros (rs1 & m1 & d1) (rs2 & m2 & d2) [Hrs Hm].
    unfold fst, snd in *.
    assert (Hinv: asmprim_inv true D1 rs1 m1 d1 /\ asmprim_inv true D2 rs2 m2 d2).
    {
      unfold wrapinv in *.
      destruct p as (q1 & p & q2).
      destruct Hm as (m1' & Hm1 & m2' & Hm & Hm2).
      simpl in Hrs.
      rewrite !wt_regset_match_compose in Hrs.
      destruct Hrs as (rs1' & Hrs1 & rs2' & Hrs & Hrs2).
      unfold fst, snd in *.
      assert ((m1, d1) = m1') by solve_monotonic; subst.
      assert (m2' = (m2, d2)) by solve_monotonic; subst.
      assert (regset_match inv q1 rs1 rs1') by solve_monotonic.
      assert (rs1' = rs1) by (symmetry; solve_monotonic); subst.
      assert (regset_match inv q2 rs2' rs2) by solve_monotonic.
      assert (rs2' = rs2) by solve_monotonic; subst.
      edestruct (inv_asmprim_inv D1 rs1 m1 d1 (rs1, (m1, d1))).
      {
        split; simpl; eauto.
      }
      edestruct (inv_asmprim_inv D2 rs2 m2 d2 (rs2, (m2, d2))).
      {
        split; simpl; eauto.
      }
      eauto.
    }
    destruct Hinv.
    constructor; eauto.
    constructor; eauto.
    simpl; rauto.
  Qed.
End INVARIANT.

Lemma exec_load_invariant `{Hmem: BaseMemoryModel}:
  forall D {F V} (ge: Genv.t F V) chunk m addr rs r rs' m',
    Asm.exec_load ge chunk m addr rs r = Next rs' m' ->
    asmprim_inv true D rs (fst m) (snd m) ->
    asmprim_inv false D rs' (fst m') (snd m').
Proof.
  unfold Asm.exec_load.
  intros.
  unfold Mem.loadv in H.
  destruct (eval_addrmode _ _ _) eqn:?; try discriminate.
  destruct (Mem.load _ _ _ _) eqn:?; try discriminate. inv H.
  inv H0; constructor; simpl in *; try congruence.
  intros.
  apply nextinstr_nf_inject.
  apply set_reg_inject.
  destruct m'.
  eapply Mem.load_inject_neutral. 2: lift_unfold; eauto.
  auto.
  auto.
Qed.

Lemma exec_store_invariant `{Hmem: BaseMemoryModel}:
  forall D {F V} (ge: Genv.t F V) chunk m addr rs r rs' m' d,
    Genv.genv_next ge = glob_threshold ->
    Asm.exec_store ge chunk m addr rs r d = Next rs' m' ->
    asmprim_inv true D rs (fst m) (snd m) ->
    asmprim_inv false D rs' (fst m') (snd m').
Proof.
  unfold Asm.exec_store.
  intros.
  unfold Mem.storev in H0.
  destruct (eval_addrmode _ _ _) eqn:?; try discriminate.
  destruct (Mem.store _ _ _ _) eqn:?; try discriminate. inv H0.
  simpl in *. lift_unfold. destruct Heqo.
  inv H1; constructor; simpl in *; try congruence.
  - erewrite Mem.nextblock_store; eauto.
  - exploit (eval_addrmode_inject_neutral (F:=F) (V:=V)). rewrite H. eauto. eauto.
    intro A. rewrite Heqv in A. inv A. unfold Mem.flat_inj in H5. destruct (plt b (Mem.nextblock (fst m))); try discriminate. inv H5.
    clear H7.
    eapply Mem.store_inject_neutral; eauto; erewrite Mem.nextblock_store; eauto.
  - erewrite Mem.nextblock_store; eauto. congruence.
  - intros.
    apply nextinstr_nf_inject.
    apply undef_regs_inject.
    erewrite Mem.nextblock_store; eauto.
Qed.
