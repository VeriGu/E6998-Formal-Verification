(** * Assembly-style semantics of AsmX *)

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
Require Import compcert.x86.Asm.
Require Import compcertx.x86.AsmX.
Require Import SimulationRelation.
Require Import SimAsm.

Require Import AsmPrimitives.
Require Import AsmModules.
Require Import String.
Require Import SimValues.

Section WITHMEMORYMODEL.
  Context `{Hmem: BaseMemoryModel}.
  Context `{SI: SymbolsInject}.

  Section WITHLAYER.
    Context {D: layerdata} (L: asmlayer D).

    (* We disallow external function calls altogether
     since all external calls are now assembly primitives. *)

    Local Instance empty_external_calls_ops_x: CompCertBuiltins.ExternalCallsOpsX (mwd D) :=
      {| CompCertBuiltins.external_functions_sem := fun _ _ _ _ _ _ _ _ => False |}
    .

    Local Instance empty_compiler_config_ops: EnableBuiltins (mwd D) :=
      {| cc_enable_external_as_builtin := false |}
    .
    Local Existing Instance mem_accessors_default.

    Inductive step (ge: genv): state (mem := mwd D) -> trace -> state (mem := mwd D) -> Prop :=
    | exec_step_asm s t s' :
        (* using empty_compiler_config_ops: external functions are disabled (except builtins),
         primitives must go through exec_step_primitive below
         *)
        Asm.step ge s t s' ->
        step ge s t s'

    | exec_step_primitive:
        forall b i sg prim rs m rs' m',
          rs PC = Vptr b Ptrofs.zero ->
          Genv.find_funct_ptr ge b = Some (External (EF_external (name_of_ident i) sg)) ->
          Layers.get_layer_primitive i L = OK (Some prim) ->
          asmprimitive_step _ prim (rs, m) (rs', m') ->
          step ge (State rs m) E0 (State rs' m')
    .


    (** Whole-machine semantics *)

    Definition whole_machine_semantics (p: Asm.program) :=
      Smallstep.Semantics step (Asm.initial_state p) Asm.final_state (Genv.globalenv p).

    Local Instance empty_external_calls_x: CompCertBuiltins.ExternalCallsPropsX (mwd D).
    Proof.
      constructor.
      intros.
      split; try (now inversion 1); try (now inversion 2); now inversion 3.
    Qed.

    Local Instance empty_compiler_configuration : ExternalCalls (mwd D).

    (** Whole-machine semantic steps only produce at most one event. *)

    Theorem whole_machine_semantics_single_events:
      forall p,
        Smallstep.single_events (whole_machine_semantics p).
    Proof.
      intros p.
      generalize (Asm.semantics_determinate p).
      inversion 1; subst.
      red.
      inversion 1; subst; eauto.
    Qed.

    (** Receptiveness of the whole-machine semantics. *)

    Theorem whole_machine_semantics_receptive:
      forall p,
        Smallstep.receptive (whole_machine_semantics p).
    Proof.
      intros p.
      generalize (Asm.semantics_determinate p).
      inversion 1; subst.
      split; auto using whole_machine_semantics_single_events.
      inversion 1; subst.
      * (* Asm step *)
        match goal with
            K: Asm.step _ _ _ _ |- _ =>
            inversion K; subst
        end.
        + (* internal *)
          inversion 1; subst; eauto.
        + (* builtin *)
          intros.
          exploit external_call_receptive; eauto.
          destruct 1 as (? & ? & ?).
          esplit.
          eleft.
          eapply Asm.exec_step_builtin; eauto.
        + (* external *)
          intros.
          exploit external_call_receptive; eauto.
          destruct 1 as (? & ? & ?).
          esplit.
          eleft.
          eapply Asm.exec_step_external; eauto.
      * (* primitive *)
        inversion 1; subst; eauto.
    Qed.

    Section DETERM.

    (** Determinacy of the whole-machine semantics. *)

      Hypothesis primitives_deterministic:
        Layers.ForallPrimitive _ (AsmPrimitiveDeterministic _) L.

      Theorem whole_machine_semantics_determinate:
        forall p,
          Smallstep.determinate (whole_machine_semantics p).
      Proof.
        intros.
        generalize (Asm.semantics_determinate p).
        inversion 1; subst.
        split; auto using whole_machine_semantics_single_events.
        * (* step determinacy *)
          inversion 1; subst; inversion 1; subst; eauto.
        + (* Asm.step vs. primitive *)
          (* the only possible Asm.step is exec_step_external *)
          match goal with
              U: Asm.step _ _ _ _ |- _ =>
              inversion U; subst; try congruence
          end.
          assert (ef = EF_external (name_of_ident i) sg) by congruence.
          subst ef.
          (* semantics of ef comes from empty_external_calls_ops_x *)
          contradiction.
        + (* primitive vs. Asm.step *)
          (* the only possible Asm.step is exec_step_external *)
          match goal with
              U: Asm.step _ _ _ _ |- _ =>
              inversion U; subst; try congruence
          end.
          assert (ef = EF_external (name_of_ident i) sg) by congruence.
          subst ef.
          (* semantics of ef comes from empty_external_calls_ops_x *)
          contradiction.
        + (* primitive vs. primitive *)
          (* the only possible trace is E0 *)
          split; [ now constructor | ].
          intros _.
          (* use the determinism hypothesis *)
          assert (name_of_ident i = name_of_ident i0) by congruence.
          assert (i = i0). eapply name_of_ident_inj; eauto. subst.
          assert (prim0 = prim) by congruence.
          subst prim0.
          exploit Layers.forall_primitive_at; [ eassumption | ].
          inversion 1; subst.
          match goal with
              U: asmprimitive_step _ _ _ _,
                 V: asmprimitive_step _ _ _ _
              |- _ =>
              specialize (asmprim_deterministic _ _ _ U V)
          end.
          congruence.
          * (* final state is stuck *)
            intros s r H0.
            red.
            intros t s'.
            intro ABSURD.
            inversion ABSURD; subst.
        + (* Asm step *)
          eapply sd_final_nostep; eauto.
        + (* primitive *)
          inversion H0; subst.
          unfold Vnullptr in * .
          destruct Archi.ptr64; congruence.
      Qed.

    End DETERM.

    (** well-typed. *)

    Theorem step_wt ge rs m t rs' m':
      step ge (State rs m) t (State rs' m') ->
      wt_regset rs ->
      wt_regset rs'.
    Proof.
      intros H H0.
      inversion H; subst.
      + (* Asm step *)
        eapply @AsmX.step_wt; eauto; try typeclasses eauto.
      + (* primitive *)
        eapply asmprimitive_step_wt; eauto.
    Qed.

    Theorem star_wt ge s t s':
      Smallstep.star step ge s t s' ->
      forall rs m,
        s = State rs m ->
        wt_regset rs ->
        forall rs' m',
          s' = State rs' m' ->
          wt_regset rs'.
    Proof.
      induction 1.
      * intros rs m H H0 rs' m' H1.
        subst.
        inv H1.
        assumption.
      * intros rs m H2 H3 rs' m' H4.
        destruct s2.
        eapply IHstar; eauto.
        subst.
        eapply step_wt; eauto.
    Qed.

    Theorem plus_wt ge rs m t rs' m' :
      Smallstep.plus step ge (State rs m) t (State rs' m') ->
      wt_regset rs ->
      wt_regset rs'.
    Proof.
      intros H H0.
      inversion H; subst.
      destruct s2.
      match goal with
          K: step _ _ _ _ |- _ =>
          eapply step_wt in K; eauto
      end.
      match goal with
          K: Smallstep.star _ _ _ _ _ |- _ =>
          eapply star_wt in K; eauto
      end.
    Qed.

  End WITHLAYER.

  (** Properties of step *)

  Section WITHREL.
    Context {D1 D2: layerdata} (R: simrel D1 D2)
            (L1: asmlayer D1) (L2: asmlayer D2).

    Definition genvx_sim (ge1 ge2: genv) :=
      (rforall p,
         state_match R p ++>
         - ==>
         set_rel (incr p (state_match R p)))%rel
      (step L1 ge1)
      (Smallstep.plus (step L2) ge2).

    Lemma genvx_sim_plus:
      (rforall p,
       genvx_sim ++>
       state_match R p ++>
       - ==>
       set_rel (incr p (state_match R p)))%rel
       (Smallstep.plus (step L1))
       (Smallstep.plus (step L2)).
    Proof.
      intros p ge1 ge2 Hge s1 s2 Hs t s1' Hs1'.
      revert p s2 Hs.
      pattern s1, t, s1'.
      eapply Smallstep.plus_ind2; try eassumption; clear s1 t s1' Hs1'.
      - intros s1 t s1' Hstep p s2 Hs.
        eapply (Hge p); eauto.
      - intros s1 t s1' u s1'' tu H1 H1' IH Htu.
        intros p1 s2 Hs.
        eapply Hge in H1; eauto.
        destruct H1 as (s2' & H2 & p' & Hincr & Hs').
        edestruct IH as (s2'' & H2' & p'' & Hincr' & Hs''); eauto.
        exists s2''.
        split.
        + eapply Smallstep.plus_trans; eauto.
        + exists p''.
                 split; auto.
                 etransitivity; eauto.
    Qed.

    Class AsmXFunrel (Rf: block -> rel fundef fundef) (ge1 ge2: genv) :=
      {
        asmx_funrel_builtin_disabled:
          cc_enable_external_as_builtin (EnableBuiltins := empty_compiler_config_ops (D := D1)) = false;
        asmx_funrel_callstate_sim p t:
          genv_le Rf ge1 ge2 ->
          forall rs1 m1 rs2 m2 s1',
            state_match R p (State rs1 m1) (State rs2 m2) ->
            step L1 ge1 (State rs1 m1) t s1' ->
            exists s2',
              (Smallstep.plus (step L2) ge2 (State rs2 m2) t s2' /\
               exists p', p ≤ p' /\ state_match R p' s1' s2')%type
      }.
    
    Lemma asmx_sim `{HRf: AsmXFunrel}:
      genv_le (V:=unit) Rf ge1 ge2 ->
      genvx_sim ge1 ge2.
    Proof.
      intros Hge.
      intros p s1 s2 Hs t s1' H1.
      inv H1.
      - inv Hs.
        eapply asmx_funrel_callstate_sim; eauto; econstructor; eauto.
      - inv Hs.
        eapply asmx_funrel_callstate_sim; eauto.
        2: econstructor 2; eauto. constructor; auto.
    Qed.

  End WITHREL.
  
  (* Per-module semantics *)

  (* Since the signature is not used at all, we are going to store
     only the function body in the LayerLib-style module, and we are
     sticking the dummy signature in the CompCert-style program. *)

  Inductive asm_asmprimitive_step D L ge (κ: Asm.code):
    asmprim_sem D :=
  | asm_asmprimitive_step_intro f lm m lm' m':
      Genv.find_funct ge (lm PC) = Some (Internal f) ->
      Asm.fn_code f = κ ->
      (* cannot properly characterize final state,
         so record all possible execution prefixes
         (and also potentially the caller's resumption) *)
      Smallstep.plus (step L) ge (State lm m) E0 (State lm' m') ->
      asm_asmprimitive_step D L ge κ (lm, m) (lm', m').

  Program Definition asm_asmprimitive D L ge κ: asmprimitive D :=
    {|
      asmprimitive_step := asm_asmprimitive_step D L ge κ
    |}.
  Next Obligation.
    inversion H; subst.
    eapply plus_wt; eauto.
  Qed.

  Require Import MakeProgram.

  Global Instance make_asm_fundef_varinfo_ops:
    ProgramFormatOps Asm.code unit (AST.fundef function) unit :=
    {
      make_internal κ :=
        OK (Internal {| Asm.fn_code := κ; Asm.fn_sig := dummy_sig |} );
      make_external D i σ :=
        OK (External (EF_external (name_of_ident i) dummy_sig));
      make_varinfo x :=
        OK x
    }.

  Global Instance make_asm_fundef_varinfo_prf:
    ProgramFormat Asm.code unit (AST.fundef Asm.function) unit.
  Proof.
    constructor.
    - simpl.
      intros.
      red. solve_monotonic.
      congruence.
  Qed.

  Context `{Hmkp: MakeProgram}.

  Import Semantics.

  Global Instance asm_function_semantics_ops:
    FunctionSemanticsOps ident code asmprimitive (globvar unit)
      asmmodule
      asmlayer :=
    {
      semof_fundef D ML i κ :=
        ge <- make_globalenv D ML;
        ret (asm_asmprimitive D (snd ML) ge κ)
    }.

  Require Import PTreeSemantics.

  Global Instance asm_semantics_ops:
    SemanticsOps ident code asmprimitive (globvar unit) asmmodule asmlayer
    :=
      ptree_semof.

  (** ** Monotonicity in terms of [genv_sim] *)

  Section ASM_MONOT.
    Context D1 D2 (R: simrel D1 D2).
    Context (M1: asmmodule).
    Context (L1: asmlayer D1).
    Context (M2: asmmodule).
    Context (L2: asmlayer D2).
    Context (HM: M1 ≤ M2).
    Context (HL: sim R L1 (〚M2〛 L2)).
    Context p1 (Hp1: make_program D1 (M1, L1) = OK p1).
    Context p2 (Hp2: make_program D2 (M2, L2) = OK p2).

    Inductive asm_funrel:
      ident -> rel (Asm.code+asmprimitive D1)%type (Asm.code+asmprimitive D2)%type :=
      | asm_funrel_function i κ:
          asm_funrel i (inl κ) (inl κ)
      | asm_funrel_primitive i σ1 σ2:
          get_layer_primitive i L1 = OK (Some σ1) ->
          get_layer_primitive i L2 = OK (Some σ2) ->
          sim R σ1 σ2 ->
          asm_funrel i (inr σ1) (inr σ2)
      | asm_funrel_replace i σ1 κ2 σ2:
          get_layer_primitive (V := globvar unit) i L1 = OK (Some σ1) ->
          get_module_function (V := globvar unit) i M2 = OK (Some κ2) ->
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
      intro i.
      apply PTreeLayers.ptree_layer_sim_pointwise in HL.
      destruct HL as (HL_prim & HL_var).
      clear HL.
      specialize (HL_prim i).
      specialize (HL_var i).
      generalize (ptree_get_semof_globalvar _ i M2 L2).
      unfold asm_semantics_ops, asmlayer_ops, asmmodule_ops in * |- * .
      intro EQ. rewrite EQ in HL_var. clear EQ.
      generalize (ptree_get_semof_primitive _ i M2 L2).
      unfold asm_semantics_ops, asmlayer_ops, asmmodule_ops in * |- * .
      intro EQ. rewrite EQ in HL_prim. clear EQ.
      unfold semof_function in HL_prim.
      unfold semof_fundef in HL_prim.
      unfold asm_function_semantics_ops in HL_prim.
      erewrite make_program_make_globalenv in HL_prim by eassumption.
      generalize (get_module_function_monotonic i _ _ HM).
      intro Hm_func.
      generalize (get_module_variable_monotonic i _ _ HM).
      intro Hm_var.
      clear HM.
      assert (HM_OK: ModuleOK M2).
      {
        eapply make_program_module_ok; esplit; eauto.
      }
      specialize (HM_OK i).
      destruct HM_OK.
      destruct module_ok_function as (? & HM_OK_fun).
      destruct module_ok_variable as (? & HM_OK_var).
      unfold get_module_layer_function.
      unfold get_module_layer_variable.
      simpl @fst.
      simpl @snd.
      generalize (make_program_noconflict _ _ _ _ i Hp2).
      intro Hnc2.
      unfold asm_semantics_ops, asmlayer_ops, asmmodule_ops in * |- * .
      rewrite HM_OK_fun in Hm_func, module_ok_disjoint, Hnc2 |- *.
      rewrite HM_OK_fun in HL_prim.
      rewrite HM_OK_var in HL_var.
      monad_norm.
      rewrite HM_OK_var in Hm_var, module_ok_disjoint, Hnc2 |- *.
      generalize (make_program_noconflict _ _ _ _ i Hp1).
      intro Hnc1.
      revert HL_prim HL_var Hm_func Hm_var.
      inversion Hnc1; clear Hnc1; subst; split; intros;
      autorewrite with res_option_globalvar; auto;
      (try now 
          match goal with
              |- res_le _ _ ?y => destruct y; repeat constructor
          end).
      + (* module function *)
        inversion Hm_func; clear Hm_func; subst.
        match goal with
            K: option_le _ _ _ |- _ =>
            inversion K; clear K; subst
        end.
        inversion Hnc2; subst.
        constructor.
        constructor.
        constructor.
      + (* module variable *)
        inversion Hm_var; clear Hm_var; subst.
        match goal with
            K: option_le _ _ _ |- _ =>
            inversion K; clear K; subst
        end.
        inversion Hnc2; subst; autorewrite with res_option_globalvar;
        reflexivity.
      + (* layer primitive *)
        destruct (get_layer_primitive i L2) as [ pr2 | ] eqn:Hprim2;
        [ | now 
            match type of HM_OK_fun with
                _ = OK ?z =>
                destruct z; constructor
            end ].
        inversion Hnc2; subst; try now
        (
          exfalso; simpl in HL_prim; inversion HL_prim; subst;
          match goal with
              K: option_le _ _ None |- _ =>
              inversion K; clear K; subst
          end
        ).
        - monad_norm.
          simpl in HL_prim.
          inversion HL_prim; subst.
          match goal with
              K: option_le _ (Some _) _ |- _ =>
              inversion K; clear K; subst
          end.
          constructor.
          constructor.
          econstructor; eauto.
          unfold asm_semantics_ops, asmlayer_ops, asmmodule_ops in * |- * .
          rewrite ptree_get_semof_primitive.
          rewrite HM_OK_fun.
          unfold asm_semantics_ops, asmlayer_ops, asmmodule_ops in * |- * .
          rewrite Hprim2.
          simpl.
          unfold semof_function.
          monad_norm.
          unfold semof_fundef.
          simpl.
          erewrite make_program_make_globalenv by eassumption.
          reflexivity.
        - simpl in HL_prim.
          inversion HL_prim; subst.
          match goal with
              K: option_le _ (Some _) (Some _) |- _ =>
              inversion K; clear K; subst
          end.
          constructor.
          constructor.
          constructor; auto.
    Qed.

    (** Next, we want to show that once this per-definition relation
      has been transported to global environments, we can establish a
      simulation in terms of the operational semantics of Asm. Here we
      establish that [asm_funrel] has the required properties for
      this proof to work: namely, that function calls in global
      environments related by [asm_funrel] will be compatible. *)

    Require SimCompCertBuiltins.

    Lemma builtin_preg_wt_all:
      forall res vl, builtin_preg_wt res vl.
    Proof.
      induction res; simpl; intros; auto.
      destruct x, vl; simpl; auto.
    Qed.

    Lemma wt_regset_match_set_res:
      forall res v v' rs rs' p,
        wt_regset_match R p rs rs' ->
        match_val R p v v' ->
        wt_regset_match R p (set_res res v rs) (set_res res v' rs').
    Proof.
      clear. induction res; simpl; intros; auto.
      apply regset_set_rel_wt; auto. rauto.
      apply IHres2; auto. apply IHres1; auto.
      eapply match_val_erase_type. eapply val_hiword_match; eauto.
      eapply match_val_erase_type. eapply val_loword_match; eauto.
    Qed.

    Instance asmx_funrel_prf:
      AsmXFunrel R L1 L2
        (fundef_le D1 D2 asm_funrel)
        (Genv.globalenv p1)
        (Genv.globalenv p2).
    Proof.
      pose (EC1 := CompCertBuiltins.external_calls_ops_x_to_external_calls_ops _ (external_calls_ops_x := empty_external_calls_ops_x (D := D1))).
      pose (EC2 := CompCertBuiltins.external_calls_ops_x_to_external_calls_ops _ (external_calls_ops_x := empty_external_calls_ops_x (D := D2))).
      pose (CCO1 := empty_compiler_config_ops (D := D1)).
      pose (CCO2 := empty_compiler_config_ops (D := D2)).
      pose (CC1 := empty_compiler_configuration (D := D1)).
      pose (CC2 := empty_compiler_configuration (D := D2)).
      split.
      - reflexivity.
      - intros p t Hge rs1 m1 rs2 m2 s1' Hs Hstep.
        inversion Hs; subst.
        inversion Hstep; subst.
        + (* Asm *)
          inversion H; subst.
          * (* instr *)
            assert (rs2 PC = Vptr b ofs) as Hptr2.
            {
              assert (match_val R p (rs1 PC) (rs2 PC)) as MATCH
              by solve_monotonic.
              match goal with
                  K: rs1 PC = Vptr _ _ |- _ =>
                  rewrite K in MATCH
              end.
              inversion MATCH; subst.
              match goal with
                  K: match_ptrbits _ _ _ _ |- _ =>
                  apply SimEvents.match_global_ptrbits_eq in K;
                [ congruence | ]
              end.
              eapply find_funct_ptr_block_is_global with (ge := Genv.globalenv p1); eauto.
            }
            (* transport_hyps. *)
            transport H5.
             match goal with
                K: fundef_le _ _ _ _ _ _ |- _ =>
                inversion K; clear K; subst
            end.
            match goal with
                K: match_fundef D1 _ _ (Internal _) |- _ =>
                inversion K; clear K; subst
            end.
            match goal with
                K: asm_funrel _ _ _ |- _ =>
                inversion K; clear K; subst; try discriminate
            end.
            match goal with
                K: match_fundef _ _ _ _ |- _ =>
                inversion K; clear K; subst
            end.
            match goal with
                K: make_fundef D1 _ (inl _) = OK (Internal _) |- _ =>
                simpl in K;
                  inversion K; clear K; subst
            end. 
            match goal with
                K: Asm.exec_instr _ ?f _ _ _ = _ |- _ =>
                rename K into INSTR1;
                pose (f_ := f)
            end.
            pose (MA := @mem_accessors_default).
            assert (
                incr p (wt_outcome_match R p)
                     (Asm.exec_instr (Genv.globalenv p1) f_ i rs1 m1)
                     (Asm.exec_instr (Genv.globalenv p2) f_ i rs2 m2)
              ) as INCR.
            {
              eapply @exec_instr_match; eauto; try typeclasses eauto.
              + apply exec_load_default_match.
              + apply exec_store_default_match.
              + rauto.
            }
            unfold f_ in INCR.
            unfold fundef in INSTR1.
            unfold MA in INCR.
            rewrite INSTR1 in INCR.
            destruct INCR as (p' & Hp' & INCR).
            inversion INCR; subst.
            match goal with
                K: Next _ _ = Asm.exec_instr _ _ _ _ _ |- _ =>
                symmetry in K
            end.
            esplit.
            split.
            {
              econstructor.
              + constructor.
                econstructor; eauto.
              + eleft.
              + traceEq.
            }
            esplit.
            split; [ eassumption | ] .
            constructor; auto.
          * (* builtin *)
            assert (rs2 PC = Vptr b ofs) as Hptr2.
            {
              assert (match_val R p (rs1 PC) (rs2 PC)) as MATCH
              by solve_monotonic.
              match goal with
                  K: rs1 PC = Vptr _ _ |- _ =>
                  rewrite K in MATCH
              end.
              inversion MATCH; subst.
              match goal with
                  K: match_ptrbits _ _ _ _ |- _ =>
                  apply SimEvents.match_global_ptrbits_eq in K;
                [ congruence | ]
              end.
              eapply find_funct_ptr_block_is_global with (ge := Genv.globalenv p1); eauto.
            }
            transport H5.
            match goal with
                K: fundef_le _ _ _ _ _ _ |- _ =>
                inversion K; clear K; subst
            end.
            match goal with
                K: match_fundef D1 _ _ (Internal _) |- _ =>
                inversion K; clear K; subst
            end.
            match goal with
                K: asm_funrel _ _ _ |- _ =>
                inversion K; clear K; subst; try discriminate
            end.
            match goal with
                K: match_fundef _ _ _ _ |- _ =>
                inversion K; clear K; subst
            end.
            match goal with
                K: make_fundef D1 _ (inl _) = OK (Internal _) |- _ =>
                simpl in K;
                  inversion K; clear K; subst
            end.
            assert (Monotonic
                      (external_call ef)
                      (SimEvents.extcall_sem_match (F:=fundef) (V:=unit) R p)) as PROP.
            {
              eapply SimEvents.builtin_external_call_match; eauto.
              apply SimCompCertBuiltins.builtin_functions_sem_match.
              apply SimCompCertBuiltins.runtime_functions_sem_match.
            }
            repeat red in PROP.
            apply SimEvents.genv_to_senv_le in Hge.
            specialize (PROP _ _ _ Hge).
            match goal with
                K: match_mem _ _ _ _ |- _ =>
                specialize (fun x y H => PROP x y H _ _ K)
            end.
            match goal with
                K: external_call _ _ _ _ _ _ _ |- _ =>
                specialize (fun y H => PROP _ y H _ (_, _) K)
            end.
            eapply (@SimEvents.eval_builtin_args_rel _ _ _ R) in H7; eauto.
            -- split_hyp H7.
               specialize (PROP _ H5).
               destruct PROP as ([vl2 m2'] & (Hext2 & p' & Hp' & Hvl & Hmatch)).
               simpl in Hvl. simpl in Hmatch. simpl in Hext2.
               esplit.
               split.
               {
                 econstructor.
                 + eleft. eapply Asm.exec_step_builtin; eauto.
                 + eleft.
                 + traceEq.
               }
               esplit.
               split.
               {
                 eassumption.
               }
               split; auto.
               apply wt_regset_match_intro.
               { 
                 apply nextinstr_nf_wt.
                 eapply set_res_wt; eauto.
                 eapply builtin_preg_wt_all.
                 apply undef_regs_wt; auto. 
                 match goal with
                   K: wt_regset_match _ _ _ rs2 |- _ =>
                   revert K; apply wt_regset_match_elim
                 end.
               }
               solve_monotonic.
               eapply wt_regset_match_set_res; eauto.
               apply undef_regs_match_wt; auto.
               eapply wt_regset_match_le_subrel; eauto.
            -- red; intros.
               eapply match_val_erase_type.
               apply (H2 a).
            -- eapply match_val_erase_type.
               apply (H2).
            -- rewrite list_rel_eq. auto.
          * (* external: absurd case, since all primitives must go through exec_step_primitive  *)
            exfalso.
            transport H5. 
            match goal with
                K: fundef_le _ _ _ _ _ _ |- _ =>
                inversion K; subst
            end.
            match goal with
                K: match_fundef _ _ ?u (External _) |- _ =>
                unfold match_fundef, make_fundef in K;
                  destruct u; (try discriminate); simpl in K; inversion K; subst
            end.
            contradiction.
        + (* primitive *)
          assert (rs2 PC = Vptr b Ptrofs.zero) as Hptr2.
          {
            assert (match_val R p (rs1 PC) (rs2 PC)) as MATCH
                by solve_monotonic.
            match goal with
                K: rs1 PC = Vptr _ _ |- _ =>
                rewrite K in MATCH
            end.
            inversion MATCH; subst.
            match goal with
                K: match_ptrbits _ _ _ _ |- _ =>
                apply SimEvents.match_global_ptrbits_eq in K;
                  [ congruence | ]
            end.
            eapply find_funct_ptr_block_is_global with (ge := Genv.globalenv p1); eauto.
          }
          transport H3.
          match goal with
              K: fundef_le _ _ _ _ _ _ |- _ =>
              inversion K; clear K; subst
          end.
          match goal with
              K: match_fundef _ _ ?u (External _) |- _ =>
              unfold match_fundef, make_fundef in K;
                destruct u; (try discriminate); simpl in K; inversion K; clear K; subst
          end.
          match goal with
              K: asm_funrel _ _ _ |- _ =>
              inversion K; clear K; subst
          end.
          * (* external *)
            match goal with
                K: match_fundef _ _ _ _ |- _ =>
                unfold match_fundef, make_fundef in K;
                  inversion K; clear K; subst
            end.
            apply name_of_ident_inj in H9; subst.
            match goal with
                K1: get_layer_primitive i L1 = OK (Some ?u1),
                K2: get_layer_primitive i L1 = OK (Some ?u2)
              |- _ =>
                assert (u1 = u2) by congruence
            end.
            subst.
            exploit asmprimitive_step_sim; eauto.
            { instantiate (1 := (_, _)).
              econstructor; simpl; eauto. }
            destruct 1 as ([rs2' m2'] & Hs2 & p' & Hp' & Hs').
            esplit.
            split.
            { econstructor.
              + eapply exec_step_primitive; eauto.
              + eleft.
              + traceEq. }
            esplit.
            split; eauto.
            inversion Hs'; subst; constructor; auto.
          * (* internal *)
            match goal with
                K: match_fundef _ _ _ _ |- _ =>
                unfold match_fundef, make_fundef in K;
                  inversion K; clear K; subst
            end.
            apply name_of_ident_inj in H9; subst.
            match goal with
                K1: get_layer_primitive i L1 = OK (Some ?u1),
                K2: get_layer_primitive i L1 = OK (Some ?u2)
              |- _ =>
                assert (u1 = u2) by congruence
            end.
            subst.
            exploit asmprimitive_step_sim; eauto.
            { instantiate (1 := (_, _)).
              econstructor; simpl; eauto. }
            destruct 1 as ([rs2' m2'] & Hs2 & p' & Hp' & Hs').
            match goal with
                K: get_layer_primitive _ 〚_〛_ = _ |- _ =>
                rename K into PRIM2
            end.
            unfold asm_semantics_ops, asmlayer_ops, asmmodule_ops in PRIM2.
            rewrite ptree_get_semof_primitive in PRIM2.
            match goal with
                K: get_module_function _ _ = _ |- _ =>
                rename K into FUNC2
            end.
            unfold asmmodule_ops in FUNC2.
            rewrite FUNC2 in PRIM2.
            unfold semof_function in PRIM2.
            revert PRIM2.
            monad_norm.
            unfold semof_fundef.
            unfold asm_function_semantics_ops.
            unfold make_globalenv.
            rewrite Hp2.
            monad_norm.
            unfold snd.
            destruct (get_layer_primitive i L2) as [ [ | ] | ] eqn:PRIM2 ; try discriminate.
            { (* primitive defined: impossible due to no_conflict *)
              exfalso.
              generalize (make_program_noconflict _ _ _ _ i Hp2).
              unfold asmmodule_ops, asmlayer_ops in * |- * .
              rewrite FUNC2.
              rewrite PRIM2.
              inversion 1. }
            simpl.
            clear PRIM2.
            intro PRIM2.
            inversion PRIM2; clear PRIM2; subst.
            simpl in Hs2.
            inversion Hs2; subst.
            esplit.
            split; eauto.
            esplit.
            split; eauto.
            inversion Hs'; subst; constructor; auto.
    Qed.

    Global Instance asm_make_fundef_error R i:
      Related (make_fundef D1 i) (make_fundef D2 i) (R ++> impl @@ isError).
    Proof.
      intros f1 f2 Hf H.
      unfold make_fundef in H.
      destruct H.
      destruct f1; discriminate.
    Qed.

    Global Instance asm_make_varinfo_error R:
      Monotonic make_varinfo (R ++> impl @@ isError).
    Proof.
      intros v1 v2 Hv H.
      simpl in H.
      destruct H.
      discriminate.
    Qed.

    (** Now we can use [asm_sim] to prove several properties.
      First, we show the monotonicity of our semantics "probes".
      This can then be used to prove both the simple monotonicity
      required by [FunctionSemantics], and hopefully vertical
      composition as well. *)

    Lemma genv_is_le:
      genv_le (fundef_le D1 D2 asm_funrel)
        (Genv.globalenv p1)
        (Genv.globalenv p2).
    Proof.
      generalize asm_module_layer_funrel.
      intro K.
      exploit @make_globalenv_le; eauto.
      repeat erewrite make_program_make_globalenv by eassumption.
      inversion 1; subst.
      assumption.
    Qed.

    Lemma asm_asmprimitive_match κ:
      asmprim_sim D1 D2 R
                  (asm_asmprimitive D1 L1 (Genv.globalenv p1) κ)
                  (asm_asmprimitive D2 L2 (Genv.globalenv p2) κ).
    Proof.
      constructor.
      intros p [rs1 m1] [rs2 m2] Hs [rs1' m1'] Hstep1.
      inversion Hstep1; subst.
      generalize genv_is_le. intro Hge.
      eapply asmx_sim in Hge; try typeclasses eauto.
      match goal with
          K: Smallstep.plus _ _ _ _ _ |- _ =>
          rename K into PLUS
      end.
      inversion Hs; subst.
      eapply genvx_sim_plus in PLUS; eauto.
      2: split; eauto.
      destruct PLUS as ([rs2' m2'] & PLUS & p' & Hp' & Hs').
      esplit.
      split.
      {
        econstructor; eauto.
        match goal with
            K: Genv.find_funct _ _ = _ |- _ =>
            revert K
        end.
        unfold Genv.find_funct.
        assert (match_val_of_type R p (typ_of_preg PC) (rs1 PC) (rs2 PC)) as MATCH by auto.
        destruct (rs1 PC); try discriminate.
        destruct (Ptrofs.eq_dec i Ptrofs.zero); try discriminate.
        subst.
        intro FUN1.
        apply match_val_erase_type in MATCH.
        inversion MATCH; subst.
        generalize genv_is_le.
        intro Hge_.
        match goal with
            K: match_ptrbits _ _ _ _ |- _ =>
            apply SimEvents.match_global_ptrbits_eq in K;
              [ | now eapply find_funct_ptr_block_is_global with (ge := Genv.globalenv p1); eauto ];
              inversion K; clear K; subst
        end.
        transport FUN1.
        match goal with
            K: fundef_le _ _ _ _ _ _ |- _ =>
            inversion K; clear K; subst
        end.
        match goal with
            K: match_fundef _ _ ?u (Internal _) |- _ =>
            destruct u; (try discriminate);
            inversion K; clear K; subst
        end.
        match goal with
            K: asm_funrel _ _ _ |- _ =>
            inversion K; clear K; subst
        end.
        match goal with
            K: match_fundef _ _ _ _ |- _ =>
            inversion K; clear K; subst
        end.
        assumption.
      }
      esplit.
      split; eauto.
      inversion Hs' ; rauto.
    Qed.

    (** Then, we show that [asm_sim] can also be use to establish a
      Compcer forward simulation for whole programs. In particular
      this will be used for the soundness proof. *)

    Require Import Smallstep.
    Require InitMemMakeProgram.

    Lemma module_layer_le_program_le:
      program_le (fundef_le D1 D2 asm_funrel) p1 p2.
    Proof.
      cut (res_le (program_le (fundef_le D1 D2 asm_funrel)) (OK p1) (OK p2)).
      {
        inversion 1; subst; auto.
      }
      rewrite <- Hp1.
      rewrite <- Hp2.
      unfold program_le.
      monotonicity.
      eapply asm_module_layer_funrel.
    Qed.


    Lemma make_program_same_public:
      prog_public p1 = prog_public p2.
    Proof.
      destruct module_layer_le_program_le.
      inv program_rel_upto_glob_threshold. simpl. auto.
    Qed.

    Lemma asm_fw:
      InitMemMakeProgram.module_layer_init_rel R (M1, L1) (M2, L2) ->
      forward_simulation
        (whole_machine_semantics L1 p1)
        (whole_machine_semantics L2 p2).
    Proof.
      intro INITREL.
      eapply forward_simulation_plus
      with (match_states := rexists p, state_match R p).
      - intros id.
        simpl.
        generalize (make_program_same_public); intro SP.
        apply make_program_make_globalenv in Hp1.
        apply make_program_make_globalenv in Hp2.
        apply make_globalenv_stencil_matches in Hp1.
        apply make_globalenv_stencil_matches in Hp2.
        unfold Genv.public_symbol.
        repeat rewrite stencil_matches_symbols by assumption.
        rewrite ! Genv.globalenv_public.
        unfold ident, fundef in *. rewrite SP.
        reflexivity.
      - intros s1 Hs1.
        destruct Hs1.
        generalize module_layer_le_program_le.
        intro PR.
        assert (simrel_program_rel R p1 p2) as PR_init.
        {
          cut (res_le (simrel_program_rel R) (make_program D1 (M1, L1)) (make_program D2 (M2, L2))).
          {
            rewrite Hp1.
            rewrite Hp2.
            inversion 1; subst; auto.
          }
          eapply InitMemMakeProgram.simrel_program_rel_intro.
          2: typeclasses eauto.
          2: eapply asm_module_layer_funrel.
          {
            intro i.
            red.
            inversion 1; subst; auto; congruence.
          }
          assumption.
        }
        apply simrel_init_mem in PR_init.
        unfold fundef in * |- * .
        rewrite H in PR_init.
        inversion PR_init as [ | ? m2 Hm _init2 INIT2 ]; subst; clear PR_init.
        destruct Hm as (w & Hm).
        generalize PR. intro PR_main.
        apply prog_main_rel in PR_main.
        apply genv_globalenv_rel in PR.
        esplit.
        split.
        { econstructor. symmetry; eassumption. }
        unfold fundef in * |- * .
        rewrite <- PR_main.
        exists w.
        split; auto.
        solve_monotonic.
        apply regset_set_rel_wt. constructor.
        apply regset_set_rel_wt. constructor.
        apply regset_set_rel_wt. eapply match_val_type_of_preg. eapply match_val_erase_type.
        eapply symbol_offset_match. eauto.
        red. red. simpl. intros. unfold Pregmap.init. rauto.
                                
      - intros s1 s2 r [p Hs] H.
        destruct H.
        inversion Hs; clear Hs; subst.
        constructor.
        + assert (match_val_of_type R p (typ_of_preg PC) (rs PC) (y PC)) as TPC by auto.
          rewrite H in TPC.
          inversion TPC; subst; auto.
        + assert (match_val_of_type R p (typ_of_preg RAX) (rs RAX) (y RAX)) as TEAX by auto.
          rewrite H0 in TEAX.
          inversion TEAX; subst; auto.
      - simpl.
        intros s1 t s1' Hstep.
        generalize genv_is_le. intro LE.
        eapply asmx_sim in LE; try typeclasses eauto.
        intros s2 [p Hs].
        eapply LE in Hstep; eauto.
        destruct Hstep as (? & ? & ? & ? & ?).
        esplit.
        split; eauto.
        esplit; eauto.
    Qed.

  End ASM_MONOT.

  Instance res_le_transport {A B} (R: rel A B) (x: res A) (y: res B) (b: B):
    Transport (res_le R) x y (y = OK b) (exists a, x = OK a /\ R a b)%type.
  Proof.
    intros H Hy.
    destruct H; try congruence.
    inversion Hy; clear Hy; subst.
    exists x; eauto.
  Qed.

  Lemma res_option_inj_inv {A B} (x: res (option A)) (y: res (option B)):
    ((x = OK None /\ y = OK None /\ res_option_inj x y = OK None) \/
    (exists t, x = OK (Some t) /\ y = OK None /\ res_option_inj x y = OK (Some (inl t))) \/
    (exists t, x = OK None /\ y = OK (Some t) /\ res_option_inj x y = OK (Some (inr t))) \/
    (exists e, res_option_inj x y = Error e))%type.
  Proof.
    unfold res_option_inj.
    clear.
    destruct x as [ [ | ] | ]; destruct y as [ [ | ] | ]; simpl; eauto;
    intuition eauto.
  Qed.

  Global Instance asm_function_semantics_prf:
    FunctionSemantics ident Asm.code asmprimitive (globvar unit)
                      asmmodule
                      asmlayer.
  Proof.
    split.
    - intros D1 D2 R ML1 ML2 HML i κ.
      inversion HML as [M1 M2 L1 L2 HM HL HL2wf HML2ok]; subst.
      simpl.
      destruct (make_globalenv D2 (M2, L2)) as [ge2 | ] eqn:Hge2.
      2: constructor.
      generalize Hge2. intro Hp2.
      apply make_globalenv_make_program in Hp2.
      destruct Hp2 as (p2 & Hp2).
      assert (ge2 = Genv.globalenv p2).
      {
        apply make_program_make_globalenv in Hp2.
        unfold ret in Hp2. simpl in Hp2. congruence.
      }
      subst.
      assert (isOK (make_program _ (M1, L1))) as P1.
      {
        assert (exists r, res_le r (make_program _ (M1, L1)) (make_program _ (M2, L2))) as P1.
        {
          exploit (foodef_rel_mpr D1 D2
                                  (fun i => option_le ⊤)
                                  (fun i => option_le ⊤)).
          intro RELS.
          esplit.
          eapply make_program_rel; eauto.
          clear i.
          intro i; split.
          + unfold get_module_layer_function; simpl.
            generalize (get_layer_primitive_sim_monotonic _ _ _ i _ _ HL).
            unfold asm_semantics_ops, asmlayer_ops, asmmodule_ops in * |- * .
            rewrite ptree_get_semof_primitive.
            intro LE.
            generalize (res_option_inj_inv (get_module_function i M2) (get_layer_primitive i L2)).
            destruct 1 as [ (Hm2 & Hl2 & RES) | [
                              (f & Hm2 & Hl2 & RES) | [
                                (v & Hm2 & Hl2 & RES) |
                                (e & RES)
                          ]]];
              unfold asm_semantics_ops, asmlayer_ops, asmmodule_ops in * |- * ;
              rewrite RES;
            clear RES;
            (try rewrite Hm2 in LE);
            (try rewrite Hl2 in LE);
            simpl in LE;
            try now constructor.
            - 
              Local Remove Hints lower_bound : typeclass_instances.
              Local Remove Hints upper_bound : typeclass_instances.
              eapply transport in Hm2.
              2: eapply get_module_function_monotonic. 2: rauto.
              split_hyp Hm2.
              unfold semof_function in LE.
              monad_norm.
              inversion LE; subst.
              repeat
              match goal with
                  K: option_le _ _ None |- _ =>
                  inversion K; clear K; subst
              end.
              match goal with
                  K: get_module_function i M1 = _ |- _ =>
                  rewrite K
              end.
              constructor.
              constructor.
            - unfold semof_function in LE.
              monad_norm.
              unfold semof_fundef in LE.
              simpl in LE.
              unfold asm_semantics_ops, asmlayer_ops, asmmodule_ops in * |- * .
              rewrite Hge2 in LE.
              monad_norm.
              generalize Hm2. intro Hm2_.
              eapply transport in Hm2.
              2: eapply get_module_function_monotonic. 2: rauto.
              split_hyp Hm2.
              match goal with
                  K: get_module_function i M1 = _ |- _ =>
                  rewrite K
              end.
              inversion LE; subst; simpl;
              (repeat
                match goal with
                    K: option_le _ _ (Some _) |- _ =>
                    inversion K; clear K; subst
                end);
              try now repeat constructor.
              edestruct @modules_layers_function_primitive_ok; eauto.
            - eapply transport in Hm2.
              2: eapply get_module_function_monotonic. 2: rauto.
              split_hyp Hm2.
              match goal with
                  K: option_le _ _ None |- _ =>
                  inversion K; clear K; subst
              end.
              match goal with
                  K: get_module_function i M1 = _ |- _ =>
                  rewrite K
              end.
              inversion LE; subst.
              simpl.
              match goal with
                  K: OK ?u = get_layer_primitive i L1 |- _ =>
                  destruct u; repeat constructor
              end.
          + unfold get_module_layer_variable.
            unfold fst. unfold snd.
            generalize (get_layer_globalvar_sim_monotonic _ _ _ i _ _ HL).
            unfold asm_semantics_ops, asmlayer_ops, asmmodule_ops in * |- * .
            rewrite ptree_get_semof_globalvar.
            intro LE.
            simpl.
            cut (res_le (option_le eq)
                        (get_module_variable i M1 ⊕ get_layer_globalvar i L1)
                        (get_module_variable i M2 ⊕ get_layer_globalvar i L2)).
            {
              unfold asmlayer_ops, asmmodule_ops.
              inversion 1; subst;
              try
              match goal with
                K: option_le _ _ _ |- _ =>
                inversion K; subst
              end;
              repeat constructor.
            }
            apply GlobalVars.res_option_globalvar_lub; auto.
            destruct (get_module_variable i M2) as [ [ g | ] | ] eqn:Hm2;
              try
                (eapply transport in Hm2;
                 [| eapply get_module_variable_monotonic; rauto];
                 split_hyp Hm2;
                 match goal with
                     K: get_module_variable i M1 = _ |- _ =>
                     rewrite K
                 end);
              res_option_globalvar_red;
              try now constructor.
            - destruct (get_layer_globalvar i L2) as [ [ g0 | ] | ];
              res_option_globalvar_red;
              try constructor; auto.
              destruct (globalvar_eq_dec g g0).
              {
                subst.
                autorewrite with res_option_globalvar.
                constructor; auto.
              }
              rewrite res_option_globalvar_oplus_diff by assumption.
              constructor.
            - match goal with
                K: option_le _ _ _ |- _ =>
                inversion K; subst
              end.
              apply oplus_lower_bound.
        }
        destruct P1 as (_R & Hp1).
        rewrite Hp2 in Hp1.
        inversion Hp1; subst.
        esplit; eauto.
      }
      destruct P1 as (p1 & Hp1).
      generalize Hp1. intro Hge1.
      apply make_program_make_globalenv in Hge1.
      rewrite Hge1.
      monad_norm.
      constructor.
      eapply asm_asmprimitive_match; eauto.
  Qed.

  Global Instance asm_semantics_prf:
    Semantics.Semantics _ Asm.code asmprimitive (globvar unit) asmmodule asmlayer.
  Proof.
    apply ptree_semof_prf.
  Qed.

  (** TODO: here we should be able to prove vertical composition as
    well. To do that we could modify [FunctionSemantics] to use the
    generalized notion of monotonicity and let [PTreeSemantics] do the
    rest. But this would break the existing code so maybe we want to
    start with adding hlper lemmas there. *)

  (** And now, the soundness proof. *)

  Require Import LayerLogicImpl.

(*
  Instance asm_layer_logic_ops:
    LayerLogicOps (simrel := simrel) ident Asm.code asmprimitive (globvar unit) (ptree_module _ _) (ptree_layer _ _) := _.
*)

  Lemma soundness_fw D1 D2 (R: simrel D1 D2) (LL: asmlayer D2) (M: asmmodule) (LH: asmlayer D1) pl ph:
    InitMemMakeProgram.module_layer_init_rel R (∅, LH) (M, LL) ->
    LL ⊢ (R, M) : LH ->
    forall CTXT,
      (forall i, ~ isOKNone (get_module_variable i CTXT) ->
                 ~ isOKNone (get_module_layer_variable i (M, LL)) ->
                 ~ In i (map fst (simrel_new_glbl R))) ->
      make_program D1 (CTXT, LH) = OK ph ->
      make_program D2 (CTXT ⊕ M, LL) = OK pl ->
      forward_simulation
        (whole_machine_semantics LH ph)
        (whole_machine_semantics LL pl).
  Proof.
    intros HINITREL HLM CTXT HCTXT_COMPAT Hph Hpl.
    eapply asm_fw; eauto.
    {
      apply oplus_le_left.
    }
    htransitivity (〚M〛 LL).
    - exact HLM.
    - (* solve_monotonic idtac. # loops forever, module_layer_sim *)
      apply semof_monotonic.
      apply layer_sim_module_layer_sim.
      split.
      + simpl. apply right_upper_bound.
      + split.
        { instantiate (1 := id). reflexivity. }
        { (* rsat *) exact I. }
    - simpl.
      assert (
          InitMemMakeProgram.module_layer_init_rel R
                                                   (CTXT ⊕ ∅, LH) (CTXT ⊕ M, LL)
        ) as HINITREL'.
      { apply InitMemMakeProgram.module_layer_init_rel_context; auto. }
      clear HINITREL.
      revert HINITREL' .
      apply InitMemMakeProgram.module_layer_init_rel_ext; auto.
      + symmetry. apply simrel_compose_id_left.
      + intro i.
        unfold get_module_layer_function.
        simpl.
        rewrite get_module_function_oplus.
        rewrite get_module_function_empty.
        match goal with
          |- context [ ?u ⊕ OK None ] =>
          replace (u ⊕ OK None) with u; auto
        end.
        destruct (get_module_function i CTXT) as [ [ | ] | ] ; auto.
      + intro i.
        unfold get_module_layer_variable.
        simpl.
        rewrite get_module_variable_oplus.
        rewrite get_module_variable_empty.
        GlobalVars.res_option_globalvar_red.
        reflexivity.
  Qed.

  Lemma soundness_bw
        D1 D2 (R: simrel D1 D2) (LL: asmlayer D2) (M: asmmodule) (LH: asmlayer D1) ph pl:
    ForallPrimitive D2 (AsmPrimitiveDeterministic D2) LL ->
    InitMemMakeProgram.module_layer_init_rel R (∅, LH) (M, LL) ->
    LL ⊢ (R, M) : LH ->
    forall CTXT,
      (forall i, ~ isOKNone (get_module_variable i CTXT) ->
                 ~ isOKNone (get_module_layer_variable i (M, LL)) ->
                 ~ In i (map fst (simrel_new_glbl R))) ->
      make_program D1 (CTXT, LH) = OK ph ->
      make_program D2 (CTXT ⊕ M, LL) = OK pl ->
      backward_simulation
        (whole_machine_semantics LH ph)
        (whole_machine_semantics LL pl).
  Proof.
    intros H H0 H1 CTXT H2 H3 H4.
    apply Smallstep.forward_to_backward_simulation.
    + eapply soundness_fw; eauto.
    + apply whole_machine_semantics_receptive; auto.
    + apply whole_machine_semantics_determinate; auto.
  Qed.

End WITHMEMORYMODEL.
