Require Import compcert.lib.Coqlib.
Require Import compcert.common.Memtype.
Require Import compcert.common.AST.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.x86.Asm.
Require Import compcertx.x86.AsmX.
Require Import liblayers.lib.Decision.
Require Import liblayers.logic.LayerData.
Require Import liblayers.logic.Layers.
Require Export liblayers.compcertx.CompcertStructures.
Require Import liblayers.compcertx.ErrorMonad.
Require Import liblayers.compcertx.AbstractData.
Require Import liblayers.compcertx.AbstractData.
Require Import liblayers.compat.CompatData.
Require Export liblayers.compat.CompatCPrimitives.
Require Export liblayers.compat.CompatAsmPrimitives.
Require Export liblayers.compat.CompatCallConv.
Open Scope positive_scope.

(** * Combined primitives *)

(** We should define a conversion from C primitive semantics to
  assembly primitive semantics. For now, we want to stick to the way
  existing proofs are done (ie. duplicated), and we just define the
  sum of both kinds. *)

Section COMBINED_PRIMITIVES.
Context `{Hmem: Mem.MemoryModel}.
Context `{Hmwd: UseMemWithData mem}.

(** ** Definition *)

Definition compatsem (D: compatdata) :=
  (sextcall_primsem D + sprimcall_primsem D)%type.

Definition compatsem_sig D (σ: compatsem D): signature :=
  match σ with
    | inl σl => sextcall_sig σl
    | inr σr => sprimcall_sig σr
  end.

(** Helps with unification. *)
Definition compatsem_inl {D}: sextcall_primsem D -> compatsem D := inl.
Definition compatsem_inr {D}: sprimcall_primsem D -> compatsem D := inr.

(** ** Order *)

Inductive compatsem_le (D: compatdata): relation (compatsem D) :=
  | compatsem_le_inl:
      Proper (sextcall_primsem_le ++> compatsem_le D) compatsem_inl
  | compatsem_le_inr:
      Proper (sprimcall_primsem_le ++> compatsem_le D) compatsem_inr.

Global Existing Instance compatsem_le_inl.
Global Existing Instance compatsem_le_inr.

Hint Resolve (compatsem_le_inl: forall D σ1 σ2, _ σ1 σ2 -> _) : liblayers.
Hint Resolve (compatsem_le_inr: forall D σ1 σ2, _ σ1 σ2 -> _) : liblayers.

Global Instance compatsem_le_preorder D:
  PreOrder (compatsem_le D).
Proof.
  split.
  * intros [σl | σr]; constructor; reflexivity.
  * intros _ _ σ3 [σl1 σl2 Hl12 | σr1 σr2 Hr12] H23;
    inversion H23 as [σl2x σl3 Hl23 | σr2x σr3 Hr23]; subst; clear H23;
    constructor;
    etransitivity;
    eassumption.
Qed.

Require Import OptionMonad.

(** ** Simulation diagrams *)

Record sextcall_sprimcall_sim {D1 D2} (R: compatrel D1 D2)
       (sem1: sextcall_primsem D1) (sem2: sprimcall_primsem D2): Prop :=
  {
    sextcall_sprimcall_sim_step:
                forall f vargs1 vargs2 vres m1 d1 m1' d1' rs2 m2 (d2: D2),
                (** Invariants *)
                forall (LOW_LEVEL_INVARIANT: low_level_invariant (Mem.nextblock m2) d2),
                forall (L_HIGH_LEVEL_INVARIANT: high_level_invariant d2),
                forall (H_HIGH_LEVEL_INVARIANT: high_level_invariant d1),
                (** Higher-layer semantics *)
                forall (SEM1: sem1 (decode_longs (sig_args (sextcall_sig sem1)) vargs1) (m1, d1) vres (m1', d1')),
                (** Match states *)
                forall (MATCH: MatchExtcallStates R f m1 d1 m2 d2),
                (** Calling convention *)
                forall (ARGS_INJ: val_list_inject f vargs1 vargs2),
                forall (EXTCALL_ARG: Asm.extcall_arguments rs2 (m2, d2) (sextcall_sig sem1) vargs2),
                (** Requirements of the compiler (to make "transitivity" possible) *)
                forall (ASM_INV: asm_invariant rs2 (m2, d2)),
                (*
      forall (KERNEL_MODE: kernel_mode d2),
                 *)
                forall (SP_NOT_VUNDEF: rs2 (Asm.IR Asm.ESP) <> Vundef),
                forall (RA_NOT_VUNDEF: rs2 Asm.RA <> Vundef),
                forall (INIT_SP_NOT_GLOBAL: 
                          forall (b : Values.block) (o : Integers.Int.int),
                            rs2 (Asm.IR Asm.ESP) = Values.Vptr b o ->
                            Ple glob_threshold b),
                exists f' rs2' m2' d2',
                  sprimcall_step sem2 rs2 (m2, d2) rs2' (m2', d2') /\
                  MatchExtcallStates R f' m1' d1' m2' d2' /\
                  inject_incr f f' /\
                  val_list_inject f'
                                  (encode_long (sig_res (sextcall_sig sem1)) vres)
                                  (map rs2' (loc_external_result (sextcall_sig sem1))) /\
                  (forall r,
                     ~ In r Conventions1.destroyed_at_call ->
                     Val.lessdef (rs2 (preg_of r)) (rs2' (preg_of r)))
                  /\ Val.lessdef (rs2 RA) (rs2' Asm.PC)
                  /\ Val.lessdef (rs2 ESP) (rs2' ESP);
    sextcall_sprimcall_sim_sig:
      sprimcall_sig sem2 = sextcall_sig sem1;
    sextcall_sprimcall_sim_invs:
      ExtcallInvariants sem1
  }.

(** We want to relate [sextcall_sprimcall_sim] with [callconv_primsem].
  One particularly challenging aspect is to establish that the final
  register states are related. In particular, we need to use the
  condition on [vres] to establish that the registers encoding it
  in [rs1] inject into [rs2]. *)

Lemma callconv_encode_result_item_inject f v reg regs rs1 rs2:
  (- ==> val_inject f) rs1 rs2 ->
  val_inject f v (rs2 reg) ->
  (prod_rel (- ==> val_inject f) eq)
    (callconv_encode_result_item (rs1, reg::regs) v)
    (rs2, regs).
Proof.
  intros Hrs Hv.
  split; eauto; simpl.
  intros reg'.
  unfold Pregmap.set.
  destruct (PregEq.eq _ _); subst; eauto.
Qed.

Lemma callconv_encode_result_items f (regs: list preg) vs (rs1 rs2: regset):
  (val_list_inject f) vs (map rs2 regs) ->
  (- ==> val_inject f) rs1 rs2 ->
  (- ==> val_inject f)
    (fst (fold_left callconv_encode_result_item vs (rs1, regs)))
    rs2.
Proof.
  change rs1 with (fst (rs1, regs)) at 1.
  change regs with (snd (rs1, regs)) at 1.
  generalize (rs1, regs) as rr.
  clear.
  induction vs as [ | v vs IHvs]; eauto.
  intros [rs1 regs] Hvs Hrs.
  destruct regs as [ | reg regs]; inversion Hvs; subst.
  apply IHvs; clear IHvs; simpl in *; eauto.
  intros reg'.
  unfold Pregmap.set.
  destruct (PregEq.eq _ _); subst; eauto.
Qed.

Lemma callconv_encode_result_inject f sg v rs1 rs2:
  (val_list_inject f)
    (encode_long (sig_res sg) v)
    (map rs2 (loc_external_result sg)) ->
  (- ==> val_inject f) rs1 rs2 ->
  (- ==> val_inject f) (callconv_encode_result sg v rs1) rs2.
Proof.
  apply callconv_encode_result_items.
Qed.

(** Furthermore, in order to do case analysis in terms if what happens
  to what register and use the conditions expressed in terms of
  [Machregs.mreg], we need to be able to distiguish whether a given
  [preg] is in the codomain of [preg_of]. *)

Definition mregs: list preg :=
  FR XMM0 :: FR XMM1 :: FR XMM2 :: FR XMM3 ::
  FR XMM4 :: FR XMM5 :: FR XMM6 :: FR XMM7 ::
  IR EAX  :: IR EBX  :: IR ECX  :: IR EDX  ::
  IR ESI  :: IR EDI  :: IR EBP  :: ST0     ::
  nil.

Lemma mregs_correct:
  forall r, In r mregs -> exists m, r = preg_of m.
Proof.
  intros [|[]|[]| |[]|] H;
  let rec tryall l :=
    match l with
      | ?m :: ?ms =>
        (exists m; reflexivity) || tryall ms
      | _ =>
        contradict H; decision
    end in
  tryall
    (Machregs.AX ::
     Machregs.BX ::
     Machregs.CX ::
     Machregs.DX ::
     Machregs.SI ::
     Machregs.DI ::
     Machregs.BP ::
     Machregs.X0 ::
     Machregs.X1 ::
     Machregs.X2 ::
     Machregs.X3 ::
     Machregs.X4 ::
     Machregs.X5 ::
     Machregs.X6 ::
     Machregs.X7 ::
     Machregs.FP0 ::
     nil).
  Qed.

Lemma mregs_complete:
  forall m, In (preg_of m) mregs.
Proof.
  intros []; decision.
Qed.

Lemma sextcall_sprimcall_sim_elim {D1 D2} (R: compatrel D1 D2) sem1 sem2:
  sextcall_sprimcall_sim R sem1 sem2 ->
  sprimcall_sim R (callconv_primsem D1 sem1) sem2.
Proof.
  intros [Hstep Hsig Hinvs].
  constructor; eauto.
  * intros f rs1 m1 d1 rs1' m1' d1' rs2 m2 d2.
    intros Hll2 Hhl2 Hhl1 Hasm H1 Hmatch.
    destruct H1 as (vargs1 & vres1 & [Hstep1 Hvargs1 Hsp Hra Hspng Hvres1]).
    destruct Hmatch as [Hmatch Hrs].
    apply extcall_arguments_lift in Hvargs1.
    edestruct extcall_arguments_inject as (vargs2 & Hvargs & Hvargs2); eauto.
    {
      apply match_inject.
    }
    edestruct Hstep as (f' & rs2' & m2' & d2' & H); eauto.
    + apply extcall_arguments_lift; assumption.
    + eapply val_inject_defined; eauto.
    + eapply val_inject_defined; eauto.
    + intros b ofs Hrs2.
      specialize (Hrs ESP).
      unfold Pregmap.get in Hrs.
      destruct Hrs; inversion Hrs2; subst; eauto; try congruence.
      apply match_inject_forward in H.
      destruct H; subst.
      transitivity b1; eauto.
      eapply Hspng; eauto.
    + destruct H as (Hstep2 & Hmatch' & Hf & Hvres & Hrd & HRAPC & HESP).
      exists f', rs2', m2', d2'.
      split; eauto.
      split; eauto.
      subst.
      intros reg.
      unfold callconv_final_regs.
      unfold Pregmap.get.
      apply callconv_encode_result_inject; eauto.
      unfold Pregmap.set.
      clear reg; intro reg.
      destruct (PregEq.eq reg PC); subst.
      {
        rewrite <- HRAPC.
        eauto.
      }
      unfold callconv_destroy_regs.
      unfold callconv_destroyed_regs.
      destruct (decide _) as [Hregd|Hregd]; try constructor.
      destruct (decide (In reg mregs)) as [Hregm|Hregm].
      {
        apply mregs_correct in Hregm.
        destruct Hregm as [r Hr]; subst.
        rewrite <- Hrd; eauto.
        intros H.
        apply Hregd.
        apply in_app; left.
        apply in_map; eauto.
      }
      {
        destruct reg as [|[]|[]| |[]|];
        try (contradict Hregm; decision);
        try (contradict Hregd; decision);
        try congruence.
        (* Only ESP left *)
        rewrite <- HESP.
        eauto.
      }
  * apply callconv_invariants in Hinvs.
    assumption.
Qed.

Inductive compatsim_def {D1 D2: compatdata} (R: compatrel D1 D2):
  compatsem D1 -> compatsem D2 -> Prop :=
    | sextcall_sim_either_sim sem1 sem2:
        sextcall_sim R sem1 sem2 ->
        compatsim_def R (compatsem_inl sem1) (compatsem_inl sem2)
    | sprimcall_sim_either_sim sem1 sem2:
        sprimcall_sim R sem1 sem2 ->
        compatsim_def R (compatsem_inr sem1) (compatsem_inr sem2)
    | sextcall_sprimcall_sim_either_sim sem1 sem2:
        sprimcall_sim R (callconv_primsem D1 sem1) sem2 ->
        ExtcallInvariants sem1 ->
        compatsim_def R (compatsem_inl sem1) (compatsem_inr sem2).

Global Instance compatsim_def_le {D1 D2} (R: compatrel D1 D2):
  Proper (compatsem_le D1 --> compatsem_le D2 ++> impl) (compatsim_def R).
Proof.
    intros σ1 σ1' H1 σ2 σ2' H2 H.
    unfold flip in *; simpl in *.
    destruct H as [sem1 sem2 Hl | sem1 sem2 Hr | sem sem2 Hlr].

    + (* extcall *)
      inversion H1 as [sem1' sem1x Hsem1 | ]; subst; clear H1.
      inversion H2 as [sem2x sem2' Hsem2 | ]; subst; clear H2.
      constructor.
      eapply sextcall_sim_le; eauto.

    + (* primcall *)
      inversion H1 as [ | sem1' sem1x Hsem1]; subst; clear H1.
      inversion H2 as [ | sem2x sem2' Hsem2]; subst; clear H2.
      constructor.
      eapply sprimcall_sim_le; eauto.

    + (* heterogenous *)
      inversion H1 as [ | sem1' sem1x Hsem1]; subst; clear H1.
      inversion H2 as [ | sem2x sem2' Hsem2]; subst; clear H2.
      constructor.
      * eapply sprimcall_sim_le; eauto.
        eapply callconv_primsem_le_monotonic.
        assumption.
      * destruct Hlr as [_ _ Hvalid _]; simpl in Hvalid.
        destruct Hsem2 as [_ _ Hvalid2].
        eapply (sextcall_primsem_le_invs x sem); eauto.
Qed.

Definition compatsim {D1 D2}:
  path compatrel D1 D2 -> compatsem D1 -> compatsem D2 -> Prop :=
  path_sim compatsem_le (@compatsim_def) D1 D2.

Global Instance compat_sim_op: Sim (path compatrel) compatsem | 1 :=
  path_sim_op compatsem_le (@compatsim_def).

Global Instance compat_primsem_ops: PrimitiveOps compatsem :=
  {
    (*prim_union := compatsem_union*)
  }.

Global Instance compatsem_primsem_prf:
  Primitives compatsem.
Proof.
  split; try typeclasses eauto.
  * apply path_sim_prf; typeclasses eauto.
Qed.

(** Convenient shortcut for defining primitives as [p ↦ csem sem]. *)

Definition csem {D: compatdata} (sem: sextcall_sem (mem := mwd D)) targs tres :=
  compatsem_inl
    {|
      sextcall_primsem_step :=
        {|
          sextcall_step := sem;
          sextcall_csig := mkcsig targs tres
        |};
      sextcall_props := Error (MSG "missing extcall properties"::nil);
      sextcall_invs := Error (MSG "primitive does not preserve invariants"::nil)
    |}.

Definition null_signature :=
  {| sig_args := nil; sig_res := None; sig_cc := cc_default |}.

Definition asmsem {D: compatdata} (sem: sprimcall_sem (mem := mwd D)) :=
  compatsem_inr
    {|
      sprimcall_primsem_step :=
        {|
          sprimcall_step := sem;
          sprimcall_sig := null_signature
        |};
      sprimcall_props := Error (MSG "missing primcall properties"::nil);
      sprimcall_invs := Error (MSG "primitive does not preserve invariants"::nil)
    |}.

Definition asmsem_withsig {D: compatdata} (sem: sprimcall_sem (mem := mwd D)) sig :=
  compatsem_inr
    {|
      sprimcall_primsem_step :=
        {|
          sprimcall_step := sem;
          sprimcall_sig := sig
        |};
      sprimcall_props := Error (MSG "missing primcall properties"::nil);
      sprimcall_invs := Error (MSG "primitive does not preserve invariants"::nil)
    |}.

End COMBINED_PRIMITIVES.
