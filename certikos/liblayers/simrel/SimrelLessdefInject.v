Require Export liblayers.simrel.SimulationRelation.
Require Export liblayers.simrel.SimrelLessdef.
Require Export liblayers.simrel.SimrelInject.
Require Import liblayers.simrel.MemoryRel.
Local Opaque mwd_ops.

(** extends cancels out when composed with inject *)

Section WITHMEM.
  Context `{Hmem: BaseMemoryModel}.
  Context {D: layerdata}.

  Global Instance extends_inject_compose:
    SimulationRelationEquivalence _ _ (equiv_extends_compose_left (inj (D:=D))).
  Proof.
    apply extends_compose_left; simpl; auto.
    - reflexivity.
    - intros p m1 m2 m3 H H0.
      eapply inject_same_nextblock; eauto.
      + eapply (Mem.extends_inject_compose (mem := mwd D)); eauto.
        destruct H0; eauto.
      + apply memrel_mext_next; eauto.
  Qed.

  Global Instance inject_extends_compose:
    SimulationRelationEquivalence _ _ (equiv_extends_compose_right (inj (D:=D))).
  Proof.
    apply extends_compose_right; simpl; auto.
    - reflexivity.
    - intros p m1 m2 m3 H H0.
      eapply inject_same_nextblock; eauto.
      + eapply Mem.inject_extends_compose; eauto.
        destruct H; eauto.
      + symmetry.
        apply memrel_mext_next; eauto.
  Qed.
End WITHMEM.
