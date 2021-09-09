Require Import LogicalRelations.
Require Import SimulationRelation.
Require Export SimValues.
Require Export AsmX.
Require Import FiniteFunctionalChoice.


(** * Relations for [Asm.regset]s *)

Section ASM_REL.
  Context `{Hmem: BaseMemoryModel}.
  Context {D1 D2} (R: simrel D1 D2).

  (** ** Preliminaries *)

  (** We need the following definition in order to express the
    monotonicity of [set_regs]. XXX: set_regs is no longer a thing? *)

  Definition indexed_rel C A B := C -> rel A B.

  Inductive list_indexed_rel {C A B} (R: indexed_rel C A B):
    indexed_rel (list C) (list A) (list B) :=
    | nil_indexed_rel:
        Monotonic nil
          (list_indexed_rel R nil)
    | cons_indexed_rel c cs:
        Monotonic cons
          (R c ++> list_indexed_rel R cs ++> list_indexed_rel R (c::cs)).

  Lemma list_indexed_rel_match_val_of_type_intro p tl:
    forall vl vl2,
      list_rel (match_val R p) vl vl2 ->
      Val.has_type_list vl2 tl ->
      list_indexed_rel (match_val_of_type R p) tl vl vl2.
  Proof.
    induction tl; inversion 1; inversion 1; subst; constructor; auto.
    apply match_val_of_type_intro; auto.
  Qed.

  Global Instance list_indexed_rel_match_val_of_type_elim p tl:
    Related
      (list_indexed_rel (match_val_of_type R p) tl)
      (list_rel (match_val R p))
      subrel.
  Proof.
    red.
    induction 1; constructor; auto.
    eapply match_val_erase_type; eauto.
  Qed.

  Global Instance list_indexed_rel_match_val_of_type_weaken l p:
    Related
      (list_indexed_rel (match_val_of_type R p) l)
      (list_rel (match_val R p))
      subrel.
  Proof.
    red.
    induction 1; constructor; auto.
    eapply match_val_erase_type; eauto.
  Qed.

  (** ** The [regset_match] relation *)

  Definition regset_match p: rel regset regset :=
    (- ==> match_val R p).

  Global Instance regset_match_relim p rs1 rs2 r:
    RElim (regset_match p) rs1 rs2 True (match_val R p (rs1 r) (rs2 r)).
  Proof.
    unfold regset_match.
    repeat intro; solve_monotonic.
  Qed.

  Lemma wt_regset_regset_match p:
    Monotonic (@wt_regset) (regset_match p --> impl).
  Proof.
    intros rs2 rs1 Hrs Hrs2 r.
    specialize (Hrs r).
    specialize (Hrs2 r).
    eapply (val_has_type_match R); eauto.
  Qed.

  (** ** The [wt_regset_match] relation *)

  Definition wt_regset_match p: rel regset regset :=
    forall_pointwise_rel (fun r => match_val_of_type R p (typ_of_preg r)).

  Global Instance wt_regset_match_relim p rs1 rs2 r ty:
    RElim (wt_regset_match p) rs1 rs2
      (typ_of_preg r = ty)
      (match_val_of_type R p ty (rs1 r) (rs2 r)).
  Proof.
    unfold wt_regset_match.
    intros Hrs Hty; subst.
    solve_monotonic.
  Qed.

  Lemma wt_regset_match_intro p rs1 rs2:
    wt_regset rs2 ->
    regset_match p rs1 rs2 ->
    wt_regset_match p rs1 rs2.
  Proof.
    intros Hrs2 Hrs r.
    eapply match_val_of_type_intro; eauto.
  Qed.

  Lemma wt_regset_match_elim p rs1 rs2:
    wt_regset_match p rs1 rs2 ->
    wt_regset rs2 /\ regset_match p rs1 rs2.
  Proof.
    intros Hrs.
    split.
    - intro r.
      eapply (match_val_has_type R).
      solve_monotonic.
    - solve_monotonic.
      intros r; rauto.
  Qed.

  Global Instance wt_regset_match_subrel p:
    Related (wt_regset_match p) (regset_match p) subrel.
  Proof.
    intros rs1 rs2 Hrs.
    solve_monotonic.
    intros r; rauto.
  Qed.

  Global Instance wt_regset_match_le_subrel:
    Monotonic (@wt_regset_match) (le ++> subrel)%rel.
  Proof.
    intros p p' LE rs rs' Hrs i. specialize (Hrs i). simpl in Hrs.
    eapply match_val_of_type_acc; eauto.
  Qed.
  
  Global Instance reg_eq_transport p rs1 rs2 r v1:
    Transport (wt_regset_match p) rs1 rs2
      (rs1 r = v1)
      (exists v2, rs2 r = v2 /\ match_val_of_type R p (typ_of_preg r) v1 v2)%type.
  Proof.
    intros Hrs H.
    specialize (Hrs r).
    rewrite H in Hrs; clear H.
    eauto.
  Qed.

  (** ** Relational properties of [regset] operations *)

  (** *** [Pregmap.set] *)

  Global Instance regset_set_rel_wt p:
    Monotonic
      (@Pregmap.set val)
      (forallr - @ r,
         match_val_of_type R p (typ_of_preg r) ++>
         wt_regset_match p ++>
         wt_regset_match p).
  Proof.
    unfold Pregmap.set.
    solve_monotonic.
    intros r; solve_monotonic.
    congruence.
  Qed.

  Local Instance regset_set_rel p:
    Monotonic
      (@Pregmap.set val)
      (- ==> match_val R p ++> regset_match p ++> regset_match p).
  Proof.
    unfold Pregmap.set.
    solve_monotonic.
    intros r; solve_monotonic.
  Qed.

  Global Instance regset_set_rel_params:
    Params (@Pregmap.set) 4.

  (** *** [undef_regs] *)

  Global Instance undef_regs_match_wt p:
    Monotonic
      (@undef_regs)
      (- ==> wt_regset_match p ++> wt_regset_match p).
  Proof.
    intro l.
    induction l; simpl; solve_monotonic.
  Qed.

  Local Instance undef_regs_match p:
    Monotonic
      (@undef_regs)
      (- ==> regset_match p ++> regset_match p).
  Proof.
    intro l.
    induction l; simpl; solve_monotonic.
  Qed.

  Local Instance set_pair_match p:
    Monotonic (@set_pair)
              ( - ==> match_val R p ++> regset_match p ++> regset_match p).
  Proof.
    intro pr. destruct pr; repeat rstep; simpl; repeat rstep. 
  Qed.

  
  (** *** [set_regs] *)

  (** XXX set_regs is no longer a thing? *)

  (*
  Local Instance set_regs_match D1 D2 (R: simrel D1 D2) p:
    Monotonic
      (@set_regs)
      (- ==> list_rel (match_val R p) ++> regset_match p ++> regset_match p).
  Proof.
    intro l.
    induction l; simpl.
    - solve_monotonic.
    - intros v1 v2 H.
      Local Remove Hints arrow_pointwise_rintro : typeclass_instances.
      solve_monotonic.
  Qed.
  *)
End ASM_REL.

Global Instance regset_match_le_subrel_params:
  Params (@regset_match) 3.

Global Instance wt_regset_match_le_subrel_params:
  Params (@wt_regset_match) 3.


(** ** Functoriality of [regset_match] *)

Section FUNCTOR.
  Context `{Hmem: BaseMemoryModel}.

  Lemma FunctionalChoice_on_preg {B}:
    ChoiceFacts.FunctionalChoice_on preg B.
  Proof.
    eapply FunctionalChoice_on_finite.
    - solve_finite ltac:(fun r => destruct r as [|[]|[]| |[]|]).
    - exact (inhabits PC).
    - exact preg_eq.
  Qed.

  Lemma regset_match_id {D} p:
    regset_match (simrel_id (D:=D)) p = eq.
  Proof.
    apply functional_extensionality; intro rs1.
    apply functional_extensionality; intro rs2.
    unfold regset_match.
    unfold simrel_id; simpl.
    rewrite match_val_simrel_id.
    apply prop_ext; split.
    - intros H.
      apply functional_extensionality; intro r.
      auto.
    - red; congruence.
  Qed.

  Lemma regset_match_compose {D1 D2 D3} R12 R23 p q:
    regset_match (simrel_compose (D1:=D1) (D2:=D2) (D3:=D3) R12 R23) (p, q) =
    rel_compose (regset_match R12 p) (regset_match R23 q).
  Proof.
    unfold regset_match.
    rewrite (match_val_simrel_compose R12 R23) by typeclasses eauto.
    rewrite arrow_pointwise_rel_compose.
    - reflexivity.
    - apply FunctionalChoice_on_preg.
  Qed.

  Lemma wt_regset_match_compose {D1 D2 D3} R12 R23 p q:
    wt_regset_match (simrel_compose (D1:=D1) (D2:=D2) (D3:=D3) R12 R23) (p, q) =
    rel_compose (wt_regset_match R12 p) (wt_regset_match R23 q).
  Proof.
    apply functional_extensionality; intro rs1.
    apply functional_extensionality; intro rs3.
    apply prop_ext; split.
    - intros H.
      apply wt_regset_match_elim in H.
      destruct H as [Hrs3 Hrs].
      rewrite regset_match_compose in Hrs.
      destruct Hrs as (rs2 & Hrs12 & Hrs23).
      exists rs2; split; eapply wt_regset_match_intro; eauto.
      eapply (wt_regset_regset_match R23); eauto.
    - intros (rs2 & Hrs12 & Hrs23).
      apply wt_regset_match_elim in Hrs12; destruct Hrs12 as [Hrs2 Hrs12].
      apply wt_regset_match_elim in Hrs23; destruct Hrs23 as [Hrs3 Hrs23].
      apply wt_regset_match_intro; eauto.
      rewrite regset_match_compose.
      exists rs2; split; eauto.
  Qed.

  Global Instance regset_match_wfunctor:
    SimrelFunctorW (@regset_match Hmem).
  Proof.
    split.
    - intros.
      intros wa wb Hwb.
      red in Hwb; subst.
      unfold regset_match.
      rstep. eapply match_val_simrel_equiv_fw.
    - intros.
      eapply regset_match_id.
    - intros.
      eapply regset_match_compose.
  Qed.
End FUNCTOR.
