Require Import SimrelDefinition.
Require Import SimrelCategory.
Require Import AbstractDataType.
Require SimrelInvariant.

(** This module originated as a variant of [SimrelInvariant] to account for the
  fact that primitives should preserve the kernel mode flag of the abstract
  data. *)

(** ** Invariants *)

Section KERNELMODE.
  Context `{Hmem: BaseMemoryModel}.

  (** *** Definition *)

  Definition km_world :=
    unit.
    (* sig (fun x => forall b, block_is_global b -> Pos.lt b x). *)

  Definition kernel_mode (D: certikosdata) (d: D) :=
    ikern d = true /\ ihost d = true.
  
  Program Definition km_ops (D: certikosdata): simrel_components D D :=
    {|
      simrel_world := km_world;
      simrel_acc := {| le := fun _ _ => True |};
      simrel_new_glbl := nil;
      simrel_undef_matches_values_bool := false;
      simrel_undef_matches_block p b := False;
      match_mem w m m' := m = m' /\ kernel_mode D (snd m);
      simrel_meminj w := inject_id
    |}.

  (** *** Properties *)

  Global Instance match_mem_corefl D p:
    Coreflexive (match_mem (km_ops D) p).
  Proof.
    intros m m' H.
    destruct H. 
    assumption.
  Qed.

  Global Instance match_val_km_refl D p:
    Reflexive (match_val (km_ops D) p).
  Proof.
    red. intro v; subst.
    destruct v; try constructor.
    replace i with (Ptrofs.add i Ptrofs.zero) at 2 by apply Ptrofs.add_zero.
    econstructor; eauto.
  Qed.

  Global Instance match_val_km_corefl D p:
    Coreflexive (match_val (km_ops D) p).
  Proof.
    intros v1 v2 Hv.
    destruct Hv; try constructor; try now (discriminate H || destruct H).
    inv H. simpl in H1. unfold inject_id in H1.
    inv H1. rewrite Ptrofs.add_zero. reflexivity.
  Qed.

  Global Instance match_ptr_km_corefl D p:
    Coreflexive (match_ptr (km_ops D) p).
  Proof.
    intros v1 v2 Hv.
    destruct Hv; try constructor; try now (discriminate H || destruct H).
    inv H. rewrite Z.add_0_r. reflexivity.
  Qed.

  Global Instance match_ptrbits_km_corefl D p:
    Coreflexive (match_ptrbits (km_ops D) p).
  Proof.
    intros v1 v2 Hv.
    destruct Hv. simpl in H.
    unfold inject_id in H. inv H.
    rewrite Ptrofs.add_zero. reflexivity.
  Qed.


  Global Instance match_ptrrange_km_corefl D p:
    Coreflexive (match_ptrrange (km_ops D) p).
  Proof.
    intros v1 v2 Hv.
    destruct Hv.
    apply coreflexivity in H. inv H. reflexivity. 
  Qed.

  Global Instance match_block_km_corefl D p:
    Coreflexive (match_block (km_ops D) p).
  Proof.
    intros v1 v2 Hv.
    destruct Hv. simpl in H.
    unfold inject_id in H. inv H.
    reflexivity.
  Qed.


  Global Instance match_vals_km_corefl D p:
    Coreflexive (list_rel (match_val (km_ops D) p)).
  Proof.
    intros vs1 vs2 Hvs.
    induction Hvs; try constructor.
    f_equal; eauto.
    eapply match_val_km_corefl; eauto.
  Qed.

  Global Instance match_memval_km_corefl D p:
    Coreflexive (match_memval (km_ops D) p).
  Proof.
    intros v1 v2 Hv.
    destruct Hv; try constructor; try now (discriminate H || destruct H).
    f_equal; rauto.
  Qed.

  Global Instance match_memval_km_refl D p:
    Reflexive (match_memval (km_ops D) p).
  Proof.
    red. intro v; subst.
    destruct v; try constructor.
    reflexivity.
  Qed.

  Global Instance match_memvals_km_refl D p:
    Reflexive (list_rel (match_memval (km_ops D) p)).
  Proof.
    red.
    induction x; simpl; intros; constructor; reflexivity.
  Qed.

  Global Instance match_memvals_km_corefl D p:
    Coreflexive (list_rel (match_memval (km_ops D) p)).
  Proof.
    intros vs1 vs2 Hvs.
    induction Hvs; try constructor.
    f_equal; eauto.
    eapply match_memval_km_corefl; eauto.
  Qed.

  Lemma km_inject_neutral_match_val D p v :
    Val.inject inject_id v v <->
    match_val (km_ops D) p v v.
  Proof.
    split; intros Hv;
    inversion Hv; clear Hv; try constructor.
    {
      pattern ofs1 at 2.
      rewrite H3.
      constructor.
      assumption.
    }
    subst.
    inversion H1.
    rewrite H4 at 1.
    econstructor; eauto.
  Qed.

  Lemma km_inject_neutral_match_vals D p l:
    Val.inject_list inject_id l l <->
    list_rel (match_val (km_ops D) p) l l .
  Proof.
    split; intros Hl; induction l; inversion Hl; subst; constructor; auto.
    + rewrite <- km_inject_neutral_match_val. simpl. assumption.
    + rewrite <- km_inject_neutral_match_val in *. simpl in *. assumption.
  Qed.

  Lemma km_inject_neutral_match_memval D p v:
    memval_inject inject_id v v <->
    match_memval (km_ops D) p v v.
  Proof.
    split; intros Hv;
    inversion Hv; clear Hv; try constructor.
    - apply km_inject_neutral_match_val.
      assumption.
    - apply km_inject_neutral_match_val in H1.
      assumption.
  Qed.

  Lemma km_inject_neutral_match_memvals D p vs:
    list_forall2 (memval_inject inject_id) vs vs <->
    list_rel (match_memval (km_ops D) p) vs vs.
  Proof.
    generalize (eq_refl vs).
    generalize vs at 2 4 6.
    revert vs.
    intros vs1 vs2 Hvseq.
    split.
    {
      intro Hvs.
      revert Hvseq.
      induction Hvs.
      - constructor.
      - intros Heq.
        constructor.
        + inversion Heq.
          eapply km_inject_neutral_match_memval.
          congruence.
        + eapply IHHvs.
          congruence.
    }
    intro Hvs.
    revert Hvseq.
    induction Hvs.
    - constructor.
    - intros Heq.
      constructor.
      + inversion Heq.
        rewrite km_inject_neutral_match_memval with (D := D) (p:=p).
        congruence.
      + eapply IHHvs.
        congruence.
  Qed.

  Lemma km_match_val_inject_neutral D p v1 v2:
    match_val (km_ops D) p v1 v2 ->
    Val.inject inject_id v1 v2.
  Proof.
    intros Hv.
    inversion Hv; subst; try now constructor.
    inversion H; subst.
    econstructor; eauto.
  Qed.

  Lemma km_match_memval_inject_neutral D p v1 v2:
    match_memval (km_ops D) p v1 v2 ->
    memval_inject inject_id v1 v2.
  Proof.
    intros Hv.
    inversion Hv; subst; constructor.
    eapply km_match_val_inject_neutral; eauto.
  Qed.

  Lemma km_match_memvals_inject_neutral D p v1 v2:
    list_rel (match_memval (km_ops D) p) v1 v2 ->
    list_forall2 (memval_inject inject_id) v1 v2.
  Proof.
    intros Hv.
    induction Hv; constructor; eauto.
    eapply km_match_memval_inject_neutral; eauto.
  Qed.

  (** *** Initial states *)

  (** To prove that initial memories satisfy the invariant, we first
    characterize the construction of initial memories with abstract
    data. *)

(*  Section WITHDATA.
    Context {D: layerdata}.

    Lemma store_zeros_with_data:
      forall m b o n (d: D),
        store_zeros (m, d) b o n =
        match store_zeros m b o n with
          | Some m' => Some (m', d)
          | None => None
        end.
    Proof.
      intros.
      functional induction (store_zeros m b o n); intros.
      * rewrite store_zeros_equation.
        rewrite e.
        reflexivity.
      * rewrite <- IHo0; clear IHo0.
        rewrite store_zeros_equation.
        rewrite e.
        lift_unfold.
        rewrite e0.
        reflexivity.
      * rewrite store_zeros_equation.
        rewrite e.
        lift_unfold.
        rewrite e0.
        reflexivity.
    Qed.

    Lemma store_init_data_with_data:
      forall {F V: Type} (ge: _ F V) m b p a (d: D),
        Genv.store_init_data ge (m, d) b p a =
        match Genv.store_init_data ge m b p a with
          | Some m' => Some (m', d)
          | None => None
        end.
    Proof.
      intros.
      destruct a; simpl; try reflexivity.
      destruct (Genv.find_symbol ge i); reflexivity.
    Qed.

    Lemma store_init_data_list_with_data:
      forall {F V: Type} (ge: _ F V) l m b p (d: D),
        Genv.store_init_data_list ge (m, d) b p l =
        match Genv.store_init_data_list ge m b p l with
          | Some m' => Some (m', d)
          | None => None
        end.
    Proof.
      induction l; simpl; try reflexivity.
      intros.
      rewrite store_init_data_with_data.
      destruct (Genv.store_init_data ge m b p a); try reflexivity.
      eauto.
    Qed.

    Lemma alloc_global_with_data:
      forall {F V} (ge: _ F V),
        forall m ig (d: D),
          Genv.alloc_global ge (m, d) ig =
          match Genv.alloc_global ge m ig with
            | Some m' => Some (m', d)
            | None => None
          end.
    Proof.
      unfold Genv.alloc_global. intros.
      destruct ig as [? [ [ | ] | ]].
      * (* function *)
        lift_unfold.
        destruct (Mem.alloc m 0 1).
        reflexivity.
      * (* variable *)
        lift_unfold.
        destruct (Mem.alloc m 0 (init_data_list_size (gvar_init v))).
        unfold set; simpl.
        rewrite store_zeros_with_data.
        destruct (store_zeros m0 b 0 (init_data_list_size (gvar_init v))); try reflexivity.
        rewrite store_init_data_list_with_data.
        destruct (Genv.store_init_data_list ge m1 b 0 (gvar_init v)); reflexivity.
      * (* none *)
        lift_unfold.
        destruct (Mem.alloc m 0 0); reflexivity.
    Qed.

    Lemma alloc_globals_with_data:
      forall {F V} (ge: _ F V),
        forall l m (d: D),
          Genv.alloc_globals ge (m, d) l =
          match Genv.alloc_globals ge m l with
            | Some m' => Some (m', d)
            | None => None
          end.
    Proof.
      induction l; simpl; try reflexivity.
      intros.
      rewrite alloc_global_with_data.
      destruct (Genv.alloc_global ge m a); try reflexivity.
      eauto.
    Qed.

    Theorem init_mem_with_data:
      forall {F V} (p: _ F V),
        Genv.init_mem (mem := mwd D) p =
        match Genv.init_mem (mem := mem) p with
          | Some m' => Some (m', init_data)
          | None => None
        end.
    Proof.
      intros.
      unfold Genv.init_mem.
      simpl.
      apply alloc_globals_with_data.
    Qed.
  End WITHDATA.
 *)
  
(** XXX: mettre au bon endroit. *)
Instance:
  Related Pos.lt Pos.le subrel.
Proof.
  intros x y Hxy.
  apply Pos.le_lteq.
  eauto.
Qed.


Ltac coreflexivity H :=
  let Heq := fresh in
  pose proof (coreflexivity _ _ H) as Heq; inv Heq.


  Global Instance km_prf D:
    SimulationRelation (km_ops D).
  Proof.
    split.
    - (* carrier preorder *)
      split; simpl; eauto.
    - (* simrel_undef_matches_block increases with carrier *)
      simpl. solve_monotonic.
    - (* match_block increases with carrier *)
      simpl; unfold RelCompFun.
      intros p1 p2 Hp.
      red.
      intro b.
      unfold inject_id. repeat constructor.
    - (* undef_matches_values implies undef_matches_block *)
      discriminate.
    - (* undef_matches_block implies undef_matches_values *)
      simpl; tauto.
    - (* undef_match_block for non-injective match_block *)
      simpl.
      intros.
      coreflexivity H0.
      coreflexivity H1.
      congruence.
    - (* undef_match_block for non weakly valid pointers *)
      intros.
      coreflexivity H1.
      coreflexivity H.
      revert H0 H2; simpl. 
      unfold Mem.weak_valid_pointer; simpl.
      lift_unfold.
      congruence.
    - (* undef_match_block for invalid pointers *)
      intros.
      coreflexivity H1.
      coreflexivity H.
      revert H0 H2; simpl. 
      unfold Mem.weak_valid_pointer; simpl.
      lift_unfold.
      congruence.

    - (* global blocks related to themselves *)
      intros p b Hb.
      destruct p as [thr Hthr].
      red. 
      unfold match_block_sameofs.
      simpl.
      unfold inject_id.
      auto.

    - (* global blocks related to themselves, reciprocal *)
      intros p b1 b2 Hb2 [delta Hinj].
      simpl in Hinj.
      unfold inject_id in Hinj.
      congruence.

    - (* [Genv.init_mem] *)
      intros.
      intros p1 p2 Hp.
      assert
        ((option_le ((rexists w, match_mem (simrel_id (D:=D)) w) /\
                     (req glob_threshold @@ Mem.nextblock)))
           (Genv.init_mem p1)
           (Genv.init_mem p2)) as Hm.
      {
        eapply genv_init_mem_simrel_withnextblock; eauto.
        + apply SimrelCategory.simrel_id_init_mem.
        + intros x y [H _].
          exists tt.
          assumption.
      }
      pose proof (@SimrelInvariant.init_mem_with_data _ D F1 V p1).
      destruct (Genv.init_mem (mem:=mwd D) p1) as [m1|] eqn:Hinit_mem; [|constructor].
      destruct (Genv.init_mem (mem:=mem) p1) as [m|] eqn:Hm1'; try discriminate.
      inversion Hm as [ | xm1 xm2 Hmeq]; clear Hm; subst.
      constructor.
      destruct Hmeq as [[[] Hmeq] Hmnb].
      simpl in Hmeq; subst.
      inversion H; clear H; subst.
      assert (Hw: forall b, block_is_global b -> (b < Mem.nextblock m)%positive).
      {
        intros b Hb.
        red in Hmnb.
        lift_unfold.
        destruct Hmnb.
        exact Hb.
      }
      exists tt.
      split; auto.
      simpl.
      red; split; reflexivity.

    - (* [Mem.alloc] *)
      intros p m m1 Hm ofs sz.
      coreflexivity Hm.
      exists tt; split; auto. 
      + simpl; auto.
      + split; [ constructor | ] ; simpl.
        * lift_unfold.
          destruct Hm; subst.
          f_equal.
        * lift_unfold. destruct Hm; subst.
          destruct @Mem.alloc. simpl. auto.
        * lift_unfold.
          destruct Hm; subst.
          destruct @Mem.alloc. simpl. auto.
          unfold match_block_sameofs.
          simpl.
          unfold inject_id.
          congruence.

    - (* [Mem.free] *)
      intros p m1 m2 Hm [[b1 lo1] hi1] [[b2 lo2] hi2] Hb.
      coreflexivity Hm.
      coreflexivity Hb.
      simpl in *.
      lift_unfold.
      destruct (Mem.free _ _ _ _) as [m'|] eqn:Hm'; constructor.
      exists tt.
      split; auto.
      split; auto.
      lift_simpl. intuition.
      
    - (* [Mem.load] *)
      intros p chunk m1 m2 Hm [b1 ofs1] [b2 ofs2] Hb.
      coreflexivity Hm.
      coreflexivity Hb.
      simpl in *.
      lift_unfold.
      destruct (@Mem.load) as [v|] eqn:Hv; constructor.
      reflexivity.

    - (* [Mem.store] *)
      intros p chunk m1 m2 Hm [b1 ofs1] [b2 ofs2] Hb v1 v2 Hv.
      coreflexivity Hb.
      coreflexivity Hv.
      coreflexivity Hm.
      destruct (uncurry _ _ _) eqn:?; constructor.
      exists tt; simpl; split; auto.
      split; auto.
      simpl in Hm; intuition.
      unfold uncurry in Heqy.
      lift_unfold. intuition congruence.

    - (* [Mem.loadbytes] *)
      intros p m1 m2 Hm [b1 ofs1] [b2 ofs2] Hb len.
      coreflexivity Hm.
      coreflexivity Hb. 
      simpl in *.
      lift_unfold.
      destruct (Mem.loadbytes _ _ _ _) as [v|] eqn:Hv; constructor.
      reflexivity.

    - (* [Mem.storebytes] *)
      intros p m1 m2 Hm [b1 ofs1] [b2 ofs2] Hb vs1 vs2 Hvs.
      coreflexivity Hm.
      coreflexivity Hb.
      coreflexivity Hvs. 
      simpl in *.
      lift_unfold.
      destruct (Mem.storebytes _ _ _ _) as [m'|] eqn:Hm'; constructor.
      split; split; split; eauto.
      lift_simpl. intuition.

    - (* [Mem.perm] *)
      intros p m1 m2 Hm [b1 ofs1] [b2 ofs2] Hb k perm.
      coreflexivity Hm.
      coreflexivity Hb.
      reflexivity.

    - (* [Mem.valid_block] *)
      intros p m1 m2 Hm b1 b2 Hb.
      coreflexivity Hm.
      coreflexivity Hb. 
      simpl in *.
      unfold Mem.valid_block. simpl. lift_unfold.
      tauto.

    - (* [Mem.different_pointers_inject] *)
      intros p m m' b1 ofs1 b2 ofs2 b1' delta1 b2' delta2 H H0 H1 H2 H3 H4.
      simpl in H3, H4.
      unfold inject_id in H3, H4.
      inv H3. inv H4.
      tauto.

    - (* [Mem.weak_valid_pointer_inject_val] *)
      intros.
      coreflexivity H.
      coreflexivity H1.
      assumption.

    - (* weak_valid_pointer_address_inject_weak *)
      intros p m1 m2 b1 b2 delta H H0.
      coreflexivity H. 
      simpl in H0.
      unfold inject_id in H0.
      inv H0.
      exists 0.
      intros ofs1 WVP.
      rewrite Ptrofs.add_zero.
      omega.

    - (* [Mem.address_inject] *)
      intros p m1 m2 b1 ofs1 b2 delta pe H H0 H1.
      simpl in H1.
      unfold inject_id in H1.
      inv H1.
      rewrite Ptrofs.add_zero.
      omega.

    - (* [Mem.aligned_area_inject] *)
      intros p m m' b ofs al sz b' delta H H0 H1 H2 H3 H4 H5.
      simpl in H5.
      unfold inject_id in H5.
      inv H5.
      rewrite Z.add_0_r.
      assumption.

    - (* [Mem.disjoint_or_equal_inject] *)
      intros p m m' b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 sz H H0 H1 H2 H3 H4 H5.
      simpl in H0, H1.
      unfold inject_id in H0, H1.
      inv H0; inv H1.
      intuition omega.
  Qed.

  Definition km {D: certikosdata}: simrel D D :=
    {|
      simrel_ops := km_ops D
    |}.
End KERNELMODE.
