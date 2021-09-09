(** ** Semantics of AsmX with C-style primitives only. *)

Require Import compcert.lib.Coqlib.
Require Import compcert.common.Memtype.
Require Import compcert.common.AST.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.cfrontend.Ctypes.
Require Import liblayers.lib.Decision.
Require Import coqrel.LogicalRelations.
Require Import liblayers.logic.LayerData.
Require Import liblayers.logic.Primitives.
Require Export liblayers.compcertx.CompcertStructures.
Require Import liblayers.compcertx.ErrorMonad.
Require Import liblayers.compcertx.AbstractData.
Require Import SimulationRelation.
Require Import SimAsm.

Require Import liblayers.logic.PTreeLayers.
Require Import PTreeModules.
Require Import PTreeSemantics.
Require Import PTrees.
Require Import LogicalRelations.
Require Import MakeProgram.

Require Import CPrimitives. (* TODO: separate ClightX semantics away *)
Require Import AsmX.
Require Import EventsX.
Require Import EraseArgs.


(** How to construct a C signature from an assembly signature for assembly primitives *)

Definition type_of_typ (t: AST.typ): Ctypes.type :=
  match t with
    | AST.Tsingle => Ctypes.Tfloat Ctypes.F32 Ctypes.noattr
    | AST.Tfloat  => Ctypes.Tfloat Ctypes.F64 Ctypes.noattr
    | AST.Tlong   => Ctypes.Tlong Ctypes.Signed Ctypes.noattr
    | AST.Tint    => Ctypes.Tint  Ctypes.I32 Ctypes.Signed Ctypes.noattr
  end.

Definition type_of_opttyp (t: option AST.typ): Ctypes.type :=
  match t with
    | Some t' => type_of_typ t'
    | None    => Tvoid
  end.

Fixpoint typelist_of_typlist (l: list AST.typ): typelist :=
  match l with
    | nil => Ctypes.Tnil
    | t :: l' => Ctypes.Tcons (type_of_typ t) (typelist_of_typlist l')
  end.

Lemma typ_of_type_of_typ t:
  typ_of_type (type_of_typ t) = t.
Proof.
  destruct t; reflexivity.
Qed.

Lemma opttyp_of_type_of_opttyp t:
  opttyp_of_type (type_of_opttyp t) = t.
Proof.
  destruct t; try reflexivity.
  destruct t; reflexivity.
Qed.

Lemma typlist_of_typelist_of_typlist l:
  typlist_of_typelist (typelist_of_typlist l) = l.
Proof.
  induction l; simpl; f_equal; eauto using typ_of_type_of_typ.
Qed.

Lemma signature_of_type_correct s:
  signature_of_type (typelist_of_typlist (AST.sig_args s)) (type_of_opttyp (AST.sig_res s)) (AST.sig_cc s) = s.
Proof.
  unfold signature_of_type.
  destruct s; simpl.
  rewrite typlist_of_typelist_of_typlist.
  rewrite opttyp_of_type_of_opttyp.
  reflexivity.
Qed.


(** Semantics of AsmX modules *)

Section SEMANTICS.
  Context `{Hmem: Mem.MemoryModelX}.
  Context `{Hmwd: UseMemWithData mem}.
  Context `{res_id: I64helpers.ReservedId}.

  Definition asm_step D L (m: mwd D) ge :=
    Asm.step
      (compiler_config_ops := cprimitive_cc_ops D L)
      (MemAccessors0 := Asm.mem_accessors_default)
      ge.
    
  Inductive asm_cprimitive_step D L ge (κ: Asm.function):
    csignature -> (list val × mwd D) -> (val × mwd D) -> Prop :=
    | asm_cprimitive_step_intro csg vargs m vres m' lm:
        let sg := (Asm.fn_sig κ) in
        csig_sig csg = sg ->
        Genv.find_funct ge (lm PC) = Some (Internal κ) ->
        (
          (* the C calling convention may not hold. We do not want the C to Asm
             refinement to *prove* that the calling convention holds, so we have
             to assume it holds. *)
          forall m_ vargsl,
            decode_longs (sig_args sg) vargsl = vargs ->
            extcall_arguments lm m sg vargsl ->
            free_extcall_args (lm SP) m (Conventions1.loc_arguments sg) = Some m_ ->
            lm SP <> Vundef ->
            lm RA <> Vundef ->
            AsmX.asm_invariant ge lm m ->
            exists lm' ,
              Smallstep.plus (asm_step D L m) ge
                             (State lm m)
                             E0
                             (State lm' m')
              /\
              encode_long (sig_res sg) vres = List.map lm' (loc_external_result sg)
              /\
              lm' PC = lm RA
              /\
              forall r,
                ~ In r Conventions1.destroyed_at_call ->
                Val.lessdef (lm (preg_of r)) (lm' (preg_of r))
        ) ->
        asm_cprimitive_step D L ge κ csg (vargs, m) (vres, m').

  Definition asm_cprimitive_csig κ :=
    let sg := (Asm.fn_sig κ) in
    {|
      csig_args := typelist_of_typlist (sig_args sg);
      csig_res  := type_of_opttyp (sig_res sg);
      csig_cc := sig_cc sg
    |}.

  Definition asm_cprimitive D L ge κ :=
    mkcprimitive D (asm_cprimitive_step D L ge κ) (asm_cprimitive_csig κ).

  Existing Instance ptree_layer_ops.
  Existing Instance ptree_layer_sim_op.
  Existing Instance ptree_layer_prf.
  Existing Instance ptree_module_ops.
  Existing Instance ptree_module_prf.

  Global Instance make_asm_fundef_varinfo_ops:
    ProgramFormatOps Asm.function Ctypes.type (AST.fundef function) unit :=
    {
      make_internal κ :=
        OK (Internal κ);
      make_external D i σ :=
        csg <- unique_csig D σ;
        OK (External (EF_external i (csig_sig csg)));
      make_varinfo x :=
        OK (mkglobvar tt (gvar_init x) (gvar_readonly x) (gvar_volatile x))
    }.

  Global Instance make_asm_fundef_varinfo_prf:
    ProgramFormat Asm.function Ctypes.type (AST.fundef Asm.function) unit.
  Proof.
    constructor.
    - simpl.
      intros.
      solve_monotonic idtac.
      destruct H0.
      congruence.
  Qed.

  Context `{Hmkp: MakeProgram}.

  Global Instance:
    FunctionSemanticsOps ident function cprimitive (globvar type)
      (ptree_module _ _)
      (ptree_layer _ _) :=
    {
      semof_fundef D ML i κ :=
        ge <- make_globalenv D ML;
        ret (asm_cprimitive D (snd ML) ge κ)
    }.

  Local Opaque ptree_layer_ops.
  Local Opaque ptree_layer_sim_op.
  Local Opaque ptree_module_ops.
  Existing Instance ptree_semantics_ops.
  Existing Instance ptree_semantics_prf.


  (** ** Monotonicity in terms of [genv_sim] *)

  Section ASM_MONOT.
    Context D1 D2 (R: simrel D1 D2).
    Context (M1: ptree_module Asm.function (globvar Ctypes.type)).
    Context (L1: ptree_layer cprimitive (globvar type) D1).
    Context (M2: ptree_module Asm.function (globvar Ctypes.type)).
    Context (L2: ptree_layer cprimitive (globvar type) D2).
    Context (HM: M1 ≤ M2).
    Context (HL: sim R L1 (〚M2〛 L2 ⊕ L2)).
    Context p1 (Hp1: make_program D1 (M1, L1) = OK p1).
    Context p2 (Hp2: make_program D2 (M2, L2) = OK p2).

    Inductive asm_funrel:
      ident -> rel (function+cprimitive D1)%type (function+cprimitive D2)%type :=
      | asm_funrel_function i κ:
          asm_funrel i (inl κ) (inl κ)
      | asm_funrel_primitive i σ1 σ2:
          get_layer_primitive i L1 = OK (Some σ1) ->
          get_layer_primitive i L2 = OK (Some σ2) ->
          sim R σ1 σ2 ->
          asm_funrel i (inr σ1) (inr σ2)
      | asm_funrel_replace i σ1 κ2 σ2:
          get_layer_primitive (V := globvar type) i L1 = OK (Some σ1) ->
          get_module_function (V := globvar type) i M2 = OK (Some κ2) ->
          get_layer_primitive i (〚M2〛 L2) = OK (Some σ2) ->
          sim R σ1 σ2 ->
          asm_funrel i (inr σ1) (inl κ2).

    (** First, we show that our premises are sufficient to establish
      the "syntactic" module-layer relation derived from [asm_funrel].
      The idea is to go from whole-layer hypotheses (which will however
      remain available throughout the proof) to a per-definition
      relation which we can easily show is preserved by [make_globalenv]. *)

    Lemma asm_module_layer_funrel:
      module_layer_le D1 D2 asm_funrel (M1,L1) (M2,L2).
    Proof.
    Admitted.

    (** Next, we want to show that once this per-definition relation
      has been transported to global environments, we can establish a
      simulation in terms of the operational semantics of Asm. Most
      of this proof is not yet done in the [SimAsm] library. Here we
      establish that [asm_funrel] has the required properties for
      this proof to work: namely, that function calls in global
      environments related by [asm_funrel] will be compatible. *)

    Instance asm_funrel_prf:
      let _ := cprimitive_extcall_ops D1 L1 in
      let _ := cprimitive_extcall_ops D2 L2 in
      let _ := cprimitive_cc_ops D1 L1 in
      let _ := cprimitive_cc_ops D2 L2 in
      AsmFunrel R
        (fundef_le D1 D2 asm_funrel)
        (Genv.globalenv p1)
        (Genv.globalenv p2).
    Proof.
      intros ecops1 ecops2 ccops1 ccops2.
      split.
      - intros b f1 f2 Hf.
        destruct Hf as [fm1 fp1 Hfp1 fm2 fp2 Hfp2 Hfm].
        unfold match_fundef in *.
        destruct Hfm as [i κ | i σ1 σ2 Hσ1 Hσ2 Hσ | i σ1 κ2 σ2 Hσ1 Hκ2 Hσ2 Hσ];
        simpl in *.
        + congruence.
        + inv_monad Hfp1; inv_monad Hfp2; subst; simpl.
          assert (res_le eq (unique_csig D1 σ1) (unique_csig D2 σ2))
            by solve_monotonic.
          unfold ret in *; simpl in *.
          destruct H; try congruence.
        + inv_monad Hfp1; inv_monad Hfp2; subst; simpl.
          setoid_rewrite ptree_get_semof_primitive in Hσ2.
          rewrite Hκ2 in Hσ2.
          unfold semof_function in Hσ2.
          monad_norm.
          inv_monad Hσ2; subst.
          unfold make_globalenv in H1.
          rewrite Hp2 in H1.
          inv_monad H1; subst.
          assert (x = asm_cprimitive_csig κ2).
          {
            assert (Hsg2: unique_csig D2 σ2 = OK (asm_cprimitive_csig κ2)).
            {
              inversion Hσ2; clear Hσ2; subst.
              reflexivity.
            }
            assert (H: res_le eq (unique_csig D1 σ1) (unique_csig D2 σ2))
              by solve_monotonic.
            unfold ret in *; simpl in *.
            destruct H; try congruence.
          }
          subst.
          destruct κ2.
          simpl.
          apply signature_of_type_correct.
      (* need to enforce fn_callconv = cc_default -> check in make_internal + property in ProgramFormat? *)
      - reflexivity.
      - intros p t Hge.
        intros s1 s2 MATCH s1' Hs1'.
        admit. (* asm_funrel_prf *)
    Qed.

    (** Now we can use [asm_sim] to prove several properties.
      First, we show the monotonicity of our semantics "probes".
      This can then be used to prove both the simple monotonicity
      required by [FunctionSemantics], and hopefully vertical
      composition as well. *)

    Instance asm_cprimitive_step_match:
      let _ := cprimitive_extcall_ops D1 L1 in
      let _ := cprimitive_extcall_ops D2 L2 in
      let _ := cprimitive_cc_ops D1 L1 in
      let _ := cprimitive_cc_ops D2 L2 in
      Related
        (genv_sim R (* rexists i, fundef_le D1 D2 asm_funrel i *) ++>
         - ==> - ==>
         rforall p, list_rel (match_val R p) * match_mem R p ++>
         set_rel (rexists p, match_val R p * match_mem R p))%rel
        (asm_cprimitive_step D1 L1)
        (asm_cprimitive_step D2 L2).
    Proof.
      clear p1 p2 Hp1 Hp2.
      intros ecops1 ecops2 ccops1 ccops2.
      intros ge1 ge2 Hge κ sg p is1 [vargs2 m2] [Hvargs Hm] fs1 H.
      destruct H as [vargs1 m1 vres1 m1' lm sg H0 H1].
      Opaque Conventions1.destroyed_at_call.
      simpl in *.
      eapply (genv_sim_plus _ p) in Hge.
      (* calling convention does not necessarily hold. What if not? *)
      admit. (* asm_cprimitive_step_match *)
    Qed.

    Existing Instance ptree_layer_sim_op.

    Instance asm_cprimitive_match:
      let _ := cprimitive_extcall_ops D1 L1 in
      let _ := cprimitive_extcall_ops D2 L2 in
      let _ := cprimitive_cc_ops D1 L1 in
      let _ := cprimitive_cc_ops D2 L2 in
      Related
        (genv_sim R (*rexists i, fundef_le D1 D2 clight_funrel i*) ++> - ==>
         cprimitive_sim D1 D2 R)%rel
        (asm_cprimitive D1 L1)
        (asm_cprimitive D2 L2).
    Proof.
      split.
      - intros sg p m1 m2 Hm fs1 H1.
        edestruct asm_cprimitive_step_match as (fs2 & Hfs1 & p' & Hfs); eauto.
        + eapply H1.
        + eexists.
          split.
          * eapply Hfs1.
          * exists p'.
            split.
            admit. (* incr p *)
            assumption.
      - apply incl_refl.
    Qed.

    (** Then, we show that [clight_sim] can also be use to establish a
      Compcer forward simulation for whole programs. In particular
      this will be used for the soundness proof. *)

    Require Import Smallstep.

    Lemma asm_fw:
      forward_simulation
        (Asm.semantics (compiler_config_ops := cprimitive_cc_ops D1 L1) p1)
        (Asm.semantics (compiler_config_ops := cprimitive_cc_ops D2 L2) p2).
    Proof.
      eapply forward_simulation_plus with
        (match_states :=
           rexists p,
            state_match R (*rexists i, fundef_le D1 D2 asm_funrel i*) p).
      - admit. (* both are stencil_matches b/c genv_le *)
      - intros s1 Hs1.
        destruct Hs1.
        (* Initial state predicates match. Should be able to construct
          s2 via some monotonicity of make_program+init_mem; other
          properties also implied by the relation on programs. *)
        admit. (* relate initial state predicates *)
      - intros s1 s2 r [p Hs] H.
        destruct H.
        inversion Hs; clear Hs; subst.
        constructor.
        admit. (* integers related to themselves *)
        admit. (* integers related to themselves *)
      - simpl.
        intros s1 t s1' Hstep.
        simpl in *.
        intros s2 (p & Hs2).
        eapply asm_sim in Hs2; eauto.
        + specialize (Hs2 t s1').
          specialize (Hs2 Hstep).
          eassumption.
        + eapply asm_funrel_prf.
        + eapply genv_globalenv_rel.
          assert (res_le (program_le (fundef_le D1 D2 asm_funrel)) (OK p1) (OK p2)).
          {
            rewrite <- Hp1.
            rewrite <- Hp2.
            unfold program_le.
            monotonicity.
            eapply asm_module_layer_funrel.
          }
          inversion H; clear H; subst.
          assumption.
    Qed.

  End ASM_MONOT.

  Instance res_le_transport {A B} (R: rel A B) (x: res A) (y: res B) (b: B):
    Transport (res_le R) x y (y = OK b) (exists a, x = OK a /\ R a b).
  Proof.
    intros H Hy.
    destruct H; try congruence.
    inversion Hy; clear Hy; subst.
    exists x; eauto.
  Qed.

  Instance:
    FunctionSemantics ident function cprimitive (globvar type)
      (ptree_module _ _)
      (ptree_layer _ _).
  Proof.
    split.
    - intros D1 D2 R [M1 L1] [M2 L2] [HM HL] i κ.
      simpl in *.
      destruct (make_globalenv D2 (M2, L2)) as [ge2 | ] eqn:Hge2.
      2: constructor.
      pose proof Hge2 as Hge1.
      eapply transport in Hge1.
      2: instantiate (1 := (make_globalenv D1 (M1, L1))).
      2: instantiate (1 := genv_le (fundef_le D1 D2 (asm_funrel D1 D2 R L1 M2 L2))).
      2: monotonicity.
      2: eapply asm_module_layer_funrel. (* admit will need more work when it's an actual prf *)
      split_hyp Hge1.
      rewrite H.
      monad_norm.
      solve_monotonic idtac.
      split.
      + admit. (* AsmXCSemantics FunctionSemantics *)
(*
        eapply asm_cprimitive_match.
        eapply asm_sim; eauto.
        unfold make_globalenv in *.
        inv_monad Hge2.
        inv_monad H; subst.
        eapply asm_funrel_prf; eauto.
        destruct HL as [HL HLwf].
        htransitivity L2; eauto.
        admit. (* eapply right_upper_bound. *)
*)
      + simpl.
        apply incl_refl.
  Qed.

  Instance clight_semantics_ops:
    SemanticsOps _ Asm.function cprimitive (globvar type) (ptree_module _ _) (ptree_layer _ _) :=
    ptree_semantics_ops.

  Instance clight_semantics_basics_prf:
    SemanticsBasics _ function cprimitive (globvar type) (ptree_module _ _) (ptree_layer _ _).
  Proof.
    apply ptree_semantics_prf.
    typeclasses eauto.
  Qed.

  (** TODO: here we should be able to prove vertical composition as
    well. To do that we could modify [FunctionSemantics] to use the
    generalized notion of monotonicity and let [PTreeSemantics] do the
    rest. But this would break the existing code so maybe we want to
    start with adding hlper lemmas there. *)

  (** And now, the soundness proof. *)

  Require Import LayerLogicImpl.

  Instance asm_layer_logic_ops:
    LayerLogicOps (simrel := simrel) ident Asm.function cprimitive (globvar type) (ptree_module _ _) (ptree_layer _ _) := _.

  Notation clayer := (ptree_layer cprimitive (globvar type)).
  Notation asmmodule := (ptree_module Asm.function (globvar type)).

  Lemma soundness_fw D1 D2 (R: simrel D1 D2) (LL: clayer D2) (M: asmmodule) (LH: clayer D1) pl ph:
    LL ⊢ (R, M) : LH ->
    forall CTXT,
      make_program D1 (CTXT, LH) = OK ph ->
      make_program D2 (CTXT ⊕ M, LL) = OK pl ->
      forward_simulation
        (Asm.semantics (compiler_config_ops := cprimitive_cc_ops D1 LH) ph)
        (Asm.semantics (compiler_config_ops := cprimitive_cc_ops D2 LL) pl).
  Proof.
    intros HLM CTXT Hph Hpl.
    eapply asm_fw; eauto.
  Qed.

End SEMANTICS.
