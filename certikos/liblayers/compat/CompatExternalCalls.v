Require Import compcert.lib.Coqlib.
Require Import compcert.common.Errors.
Require Import compcert.common.AST.
Require Import compcert.common.Events.
Require Import liblayers.lib.Decision.
Require Import liblayers.compat.CompatLayers.
Require Import compcertx.driver.CompCertBuiltins.

Section WITH_MEMORY_MODEL.
Context `{Hmem: Mem.MemoryModel}.
Context `{Hmwd: UseMemWithData mem}.

(** We cannot use [Inductive] here, because [Events.extcall_sem]
introduces dependency on the type of [ge], which cannot be inverted
properly. *)

Definition compatsem_extcall {D: compatdata}:
  compatsem D -> signature -> Events.extcall_sem (mem := mwd D) :=
  fun f sg F V ge vargs m t vres m' =>
    exists (σ: sextcall_primsem D),
      stencil_matches ge /\
      sextcall_step σ vargs m vres m' /\
      f = inl σ /\
      sg = sextcall_sig σ /\
      t = E0.

Lemma compatsem_extcall_intro {D: compatdata}
      (σ: sextcall_primsem D) F V ge vargs m vres m':
        stencil_matches ge ->
        sextcall_step σ vargs m vres m' ->
        compatsem_extcall (inl σ) (sextcall_sig σ) F V ge vargs m E0 vres m'.
Proof.
  unfold compatsem_extcall; eauto 7.
Qed.

Lemma compatsem_extcall_le {D: compatdata}
      (σ1 σ2: compatsem D)
      (LE: σ1 ≤ σ2)
      sg F V ge vargs m t vres m'
      (Hsem: compatsem_extcall σ1 sg F V ge vargs m t vres m')
:
  compatsem_extcall σ2 sg F V ge vargs m t vres m'.
Proof.
  destruct Hsem as (σ & Hmatch & Hstep & ? & ? & ?); subst.
  inversion LE; subst; clear LE.
  destruct H0 as [Hstep' Hsig].
  destruct σ; subst; simpl in *.
  destruct y; subst; simpl in *.
  subst; simpl in *.
  repeat (econstructor; eauto).
  (** XXX only true if σ2 valid for all stencils; fortunately only used
    in I64Layers where it's probably true. *)
  * simpl; eauto.
    intros. eapply Hstep'; eauto.
  * simpl; unfold sextcall_sig; congruence.
Qed.

Local Instance compatlayer_extcall_ops_x {D} (L: compatlayer D):
  ExternalCallsOpsX (mwd D) :=
  {|
    external_functions_sem i sg F V ge vargs m t vres m' :=
      exists σ,
        get_layer_primitive i L = Errors.OK (Some σ) /\
        compatsem_extcall σ sg _ _ ge vargs m t vres m'
  |}.

Local Instance compatlayer_extcall_ops {D} (L: compatlayer D):
  ExternalCallsOps (mwd D) :=
  external_calls_ops_x_to_external_calls_ops (mwd D) (external_calls_ops_x := compatlayer_extcall_ops_x L).

Local Instance compatlayer_compiler_config_ops {D} (L: compatlayer D):
  CompilerConfigOps _
      (external_calls_ops := compatlayer_extcall_ops L)
 :=
  {|
    (** We want to follow the calling conventions when calling an
    external function which will be replaced later with code. This is
    not possible if EF_extcall are enabled at builtin call sites. *)
    cc_enable_external_as_builtin := false
  |}.

(** To prove that a layer can provide external function properties
suitable to CompCert, we need a "strong layer" premise. *)

Definition sextcall_props_defined {D} (σ: res (option (compatsem D))): bool :=
  match σ with
    | OK (Some (inl f)) =>
      match sextcall_props _ f with
        | Error _ => false
        | _ => true
      end
    | _ => true
  end.

Definition ExternalCallsXDefined {D} (L: compatlayer D): Prop :=
  forall i, (fun f => sextcall_props_defined f = true) (get_layer_primitive i L).

(* Declaring this instance is necessary to avoid [Existing Class]
getting in the way of instance resolution *)
Global Instance external_calls_x_defined_dec: forall {D} (L: _ D), Decision (ExternalCallsXDefined L) := _.

Existing Class ExternalCallsXDefined.

Local Instance compatlayer_extcall_x_strong:
  forall {D} (L: compatlayer D),
  forall (DEF: ExternalCallsXDefined L),
    ExternalCallsX _
                   (external_calls_ops_x := compatlayer_extcall_ops_x L).
Proof.

Ltac t DEF id H :=
  let σ := fresh "σ" in
  let Hget := fresh "Hget" in
  let Hsem := fresh "Hsem" in
  let s := fresh "s" in
  let σf := fresh "σf" in
  let Hmatch := fresh "Hmatch" in
  let Hdef := fresh "Hdef" in
  let Hprop := fresh "Hprop" in
  destruct H as (σ & Hget & Hsem);
    destruct Hsem as (σf & Hmatch & Hsem & ? & ? & ?);
    subst;
    generalize (DEF id); rewrite Hget; intro Hdef; simpl in Hdef;
    destruct (sextcall_props _ σf) as [Hprop | ]; try discriminate
.

  Local Transparent find_symbol.
  intros.
  constructor.
  constructor;
    intros; try (t DEF id H).
  * replace (proj_sig_res (sextcall_sig σf)) with (Ctypes.typ_of_type (sextcall_res σf)).
    + eapply external_call_well_typed; eauto.
    + unfold proj_sig_res, sextcall_sig, sextcall_res.
      destruct (sextcall_csig σf); simpl.
      destruct csig_res; simpl; try reflexivity.
      destruct f; reflexivity.
  * t DEF id H1.
    econstructor. split; eauto.
    esplit. esplit.
    eapply stencil_matches_symbols_preserved; eauto.
    esplit; eauto.
  * eapply external_call_valid_block; eauto.
  * eapply external_call_max_perm; eauto.
  * eapply external_call_readonly; eauto.
  * exploit external_call_mem_extends; eauto.
    destruct 1 as (? & ? & ? & ?).
    esplit. esplit.
    split; eauto.
    econstructor.
    split; eauto.
    esplit. esplit; eauto.
  * t DEF id H0.
    edestruct (external_call_mem_inject vargs m1 vres m2 f m1' vargs')
      as (? & ? & ? & ? & ?); eauto.
    {
      intros b b' delta Hb.
      destruct H as (Hsymb & _).
      specialize (Hsymb b b).
      unfold Mem.flat_inj in Hb.
      destruct (plt b glob_threshold) as [Hbglob|]; try discriminate.
      rewrite <- Hb.
      rewrite stencil_matches_symbols in Hsymb; eauto.
      unfold find_symbol, find_symbol_upto in Hsymb.
      change (b < glob_threshold) in Hbglob.
      destruct (decide (b < glob_threshold)); eauto.
      contradiction.
    }
    repeat (eexists; eauto).
  * simpl; omega.
  * inversion H0; subst.
    esplit. esplit. econstructor; eauto. split; eauto.
    esplit. esplit; eauto.
  * t DEF id H0.
    split.
    + constructor.
    + replace σf0 with σf in * by congruence.
      intro; eapply external_call_determ; eauto.
Qed.

Local Instance compatlayer_extcall_strong :
  forall `{builtin_norepet: BuiltinIdentsNorepet},
  forall {D} (L: compatlayer D),
    forall (DEF: ExternalCallsXDefined L),
    ExternalCalls _
      (external_calls_ops := compatlayer_extcall_ops L)
  := _.

Local Instance compatlayer_compiler_config :
  forall `{builtin_norepet: BuiltinIdentsNorepet},
  forall {D} (L: compatlayer D),
    forall (DEF: ExternalCallsXDefined L),
    CompilerConfiguration _
      (external_calls_ops := compatlayer_extcall_ops L).
Proof.
  constructor.
  typeclasses eauto.
  apply compatlayer_extcall_strong.
  assumption.
Qed.

End WITH_MEMORY_MODEL.
