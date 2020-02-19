Require Import Coqlib.
Require Import Maps.
Require Import Maps2.
Require Import AST.
Require Import Op.
Require Import Registers.
Require Import Utils.
Require Import Integers.
Require Import Floats.
Require Import Classical.
Require Import Lattice.
Require Import Iteration.
Require Import DLib.
Require Import Kildall.
Require Import KildallComp.
Require Import SSA.
Require Import SSAtool.
Require Import SSAutils.
Require Import Utilsvalidproof.

Require Import SCCPopt.
Require Opt.
Require Import Dsd.

(** This file instantiate the framework of [OptInv] to SCCP *)

(** * Structural properties. Helpers *)
Lemma join_point_transf_function :
  forall (f:function)  j,
    join_point j (transf_function f) <-> join_point j f.
Proof.
  intros.
  eapply Opt.join_point_transf_function; eauto.
  eapply new_code_same_or_Iop; eauto.
  apply f.
Qed.

Lemma successors_transf_function:
  forall (f:function)  pc,
    (successors (transf_function f))!pc = (successors f)!pc.
Proof.
  intros.
  eapply Opt.successors_transf_function; eauto.
  eapply new_code_same_or_Iop; eauto.
  apply f.
Qed.

Lemma make_predecessors_transf_function: forall f:function,
  (Kildall.make_predecessors (fn_code (transf_function f)) successors_instr) =
  (Kildall.make_predecessors (fn_code f) successors_instr).
Proof.
  intros.
  eapply Opt.make_predecessors_transf_function; eauto.
  eapply new_code_same_or_Iop; eauto.
  apply f.
Qed.

(** * Proof obligations from [OptInv] *)
Module DS := DataflowSolver.

Section DSD_ANALYSIS.

  Require Import ConstpropOp ConstpropOpproofSSA OptInv.
  Notation A := fixpoint.
  Notation A_r f := (fst (A f)).
  Notation A_e f := (snd (A f)).

  Definition G ge sp (rs: regset) := (val_match_approx ge sp).
  Hint Unfold G.
  Definition result := reg -> Approx.t.
  Definition is_at_Top (res: result) (r: reg) : Prop := res r = Unknown.

  Lemma G_increasing: forall ge sp rs x y z,
                        Approx.ge x y -> G ge sp rs y z -> G ge sp rs x z.
  Proof.
    intros.
    unfold G in *.
    destruct y, x; invh val_match_approx;
    repeat invh Approx.ge ; repeat invh or ; go.
  Qed.

  Lemma uh: forall ge sp rs r x, x = Unknown -> G ge sp rs x (rs#2 r).
  Proof.
    intuition. subst. firstorder.
  Qed.

  Lemma G_top : forall f r ge sp rs, is_at_Top (A_r f) r -> G ge sp rs (A_r f r) (rs#2 r).
  Proof.
    intros. invh is_at_Top.
    eapply uh; auto.
  Qed.

 Lemma is_at_Top_eq_is_at_Top : forall f dst x,
   is_at_Top (A_r f) dst -> A_r f x = A_r f dst -> is_at_Top (A_r f) x.
  Proof.
    unfold is_at_Top; intros. congruence.
  Qed.

  Remark ext_params_not_defined: forall (f:function) x,
      wf_ssa_function f ->
      ext_params f x ->
      DS.not_defined f handle_instr x.
  Proof.
    intros.
    Ltac ssa_params :=
      match goal with
          HH : In _ (fn_params _) |- _ => apply fn_ssa_params in HH
      end.

    unfold DS.not_defined. split.
    + intros lv r' nv i pc H1. unfold DS.cfg in *.
      unfold handle_instr in *.
      intro contra; subst.
      flatten H1; assert (assigned_code_spec (fn_code f) pc r'); eauto;
      try (invh ext_params; [ ssa_params ; [intro; subst; intuition; eauto | eauto]
                  | intro; subst; unfold not in *; eauto]).
    + intros. unfold DS.phicode in *.
      intro contra; subst.
      assert (assigned_phi_spec (fn_phicode f) pc r'); try (econstructor; eauto).
      invh ext_params.
      - ssa_params. intuition; eauto. assumption.
      - intuition; eauto.
  Qed.

  Remark params_at_top_aux: forall f,
                            forall r inilv res,
    fold_left (fun lv r => P2Map.set r Approx.top lv) (fn_params f)  inilv = res ->
    ((In r (fn_params f) -> res #2 r = Approx.top)
     /\ ((~In r (fn_params f)) -> res #2 r = inilv #2 r)).
  Proof.
    intros. subst. generalize dependent inilv.
    unfold initial.
    induction (fn_params f).
    + intros. simpl in *. intuition.
    + intros. simpl in *. specialize (IHl (inilv #2 a <- Approx.top)). invh and.
      split.
    - intros. invh or.
      destruct (in_dec p2eq r l); intuition;
      match goal with
          H: ?t = ?t' |- _ => rewrite H
      end; apply P2Map.gss; intuition. intuition.
    - intros H1. intuition. match goal with H1: _ : _ |- _ => rewrite H1 end.
      apply P2Map.gso; eauto.
  Qed.

  Lemma params_at_top: forall f,
                            forall r,
                         In r (fn_params f) -> (initial f) #2 r = Approx.top.
  Proof.
    intros.
    set (lv := initial f). unfold initial in *.
    set (HH := params_at_top_aux f).
    specialize (HH r (P2Map.init Approx.bot) lv).
    intuition.
  Qed.

  Lemma ext_param_at_top: forall (f:function) r,
                            ext_params f r -> is_at_Top (A_r f) r.
  Proof.
    intros.
    destruct (in_dec p2eq r (fn_params f)).
    + assert ((initial f) #2 r = Approx.top) by (apply params_at_top; auto).
      exploit ext_params_not_defined; eauto. apply f. intros NDEF.
      eapply DS.defined_nowhere_stays_top; eauto.
    + set (ini := initial f). unfold initial in *.
      set (HH := params_at_top_aux f).
      specialize (HH r (P2Map.init Approx.bot) ini).
      rewrite P2Map.gi in *.
      assert (ini #2 r = Approx.bot) by intuition.
      exploit ext_params_not_defined; eauto. apply f. intros NDEF.
      eapply DS.defined_nowhere_becomes_top; eauto.
  Qed.

  Definition exec f pc := DS.executable_node f pc (A_e f).

  Lemma exec_fn_entrypoint : forall f, exec f (fn_entrypoint f).
  Proof.
    go.
  Qed.

(** Instantiating the [DsdAnalysis] record *)
  Definition SCCP := (OptInv.Build_DsdAnalysis Approx.t G is_at_Top A
                                               exec exec_fn_entrypoint
                                               is_at_Top_eq_is_at_Top
                                               ext_param_at_top G_top).
End DSD_ANALYSIS.


(** * Some more auxiliary lemmas to retrieve soundness invariant of the analysis *)

Section AuxResults.

Inductive single_succ_instr f : node -> Prop :=
| SSnop: forall pc s,
   (fn_code f) !pc = Some (Inop s) -> single_succ_instr f pc
| SSop: forall pc op args dst s,
   (fn_code f) !pc = Some (Iop op args dst s) -> single_succ_instr f pc
| SSload: forall pc chk adr args dst s,
   (fn_code f) !pc = Some (Iload chk adr args dst s) -> single_succ_instr f pc
| SSbuiltin: forall pc ef args dst s,
   (fn_code f) !pc = Some (Ibuiltin ef args dst s) -> single_succ_instr f pc
| SSstore: forall pc chk adr args src s,
   (fn_code f) !pc = Some (Istore chk adr args src s) -> single_succ_instr f pc
| SScall: forall pc sig fn args dst s,
   (fn_code f) !pc = Some (Icall sig fn args dst s) -> single_succ_instr f pc.

Lemma exec_single_succ: forall (f:function) lv es pc pc' i,
  wf_ssa_function f ->
  DS.fixpoint f handle_instr (initial f) f = (lv, es) ->
  (fn_code f) ! pc = Some i ->
  single_succ_instr f pc ->
  successors_instr i = pc'::nil ->
  exec f pc ->
  es #2 (pc, pc') = true.
Proof.
  intros f lv es pc pc' i WF FIX H H0 H1 H2.
  generalize FIX ; intro FIX'.
  apply DS.post_fixpoint in FIX as [_ [_ He]].
  unfold DS.exec_flags_sound in *.
  destruct (classic (es !!2 (pc, pc') = true)) as [Hc | Hc].
  + assumption.
  + apply not_true_iff_false in Hc.
    assert (exists i', (fn_code f) ! pc' = Some i') as [i' Hex].
    { eapply fn_code_closed; eauto. rewrite H1. auto. }
    assert (Hcfg: cfg f pc pc').
    { econstructor; eauto. rewrite H1. auto. }
    specialize (He pc pc' i' Hcfg Hc Hex).
    inv He.
  - inv H2. eelim H3; go.
    invh ex ; invh and.
    unfold fixpoint in *. simpl in *.
    rewrite FIX' in *. simpl in H4.
    eelim H3. econstructor 2; eauto; go.
  - destruct ((fn_code f) ! pc) as [| i0] eqn:eq.
    destruct i0; try contradiction.
    inv H. simpl in *. inv H1.
    inv H. inv H0; congruence.
    contradiction.
Qed.

Lemma exec_node_single_succ: forall (f:function) lv es pc pc' i,
   wf_ssa_function f ->
   DS.fixpoint f handle_instr (initial f) f = (lv, es) ->
   (fn_code f) ! pc = Some i ->
   single_succ_instr f pc ->
   successors_instr i = pc'::nil ->
   exec f pc ->
   exec f pc'.
Proof.
  intros.
  assert (es #2 (pc, pc') = true).
  eapply exec_single_succ; eauto.
  right.
  exists pc. split.
  - unfold fixpoint. simpl. rewrite H0. simpl. intuition.
  - econstructor; eauto.
    assert (In pc' (pc'::nil)). auto. congruence.
Qed.

Hint Unfold successors_instr.

Lemma step_phi_aux: forall (f:function) ge pc pc' phib k sp rs,
   wf_ssa_function f ->
   reached f pc ->
   exec f pc ->

   (fn_code f) ! pc = Some (Inop pc') ->
   (fn_phicode f) ! pc' = Some phib ->
   index_pred (Kildall.make_predecessors (fn_code f) successors_instr) pc pc' = Some k ->

   gamma SCCP f ge sp pc rs ->
   gamma SCCP f ge sp pc' (phi_store k phib rs).
Proof.
  intros f ge pc pc' phib k sp rs WF HH H H0 H1 H2 H3.
  intros r Hr Hexr.
  destruct (classic (assigned_phi_spec (fn_phicode f) pc' r)) as [H6 | H6].
  + invh assigned_phi_spec. invh ex.
    allinv.
    destruct (nth_error x k) eqn:eq.
    * erewrite phi_store_copy2; eauto.
      assert (Approx.ge (A_r SCCP f r) (A_r SCCP f r0)).
      { case_eq (DS.fixpoint f handle_instr (initial f) f). intros lv es Hfp.
        exploit DS.post_fixpoint; eauto.
        intros [Hc [Hp He]].
        exploit Hp; eauto.
        eapply exec_single_succ with (lv:= lv); eauto; intuition.
        econstructor; eauto.
        intros.
        unfold SCCP, A_r ; simpl.
        rewrite Hfp. simpl. auto.
      }

      exploit dsd_pred_jpn'; eauto.
      intros [Hcase1 | Hcase2]; invh and.
      - eapply G_increasing; eauto.
        eapply H3; eauto.
      - eapply G_increasing; eauto.
        exploit ext_param_at_top ; eauto. intros Htop.
        replace (A_r SCCP f r0) with (fst (fixpoint f) r0) by reflexivity.
        eapply (G_top). apply Htop.

    * unfold phi_store.
      assert (exists arg : reg, nth_error x k = Some arg).
      eapply fn_phiargs; eauto. invh ex. congruence.
  + erewrite phi_store_notin_preserved; eauto.
    destruct (peq pc (fn_entrypoint f)).
    * subst.
      exploit dsd_entry_ext_param; eauto.
      intros.
      replace (A_r SCCP f r) with (fst (fixpoint f) r) by reflexivity.
      erewrite ext_param_at_top ; eauto.
      go.
    * replace (A_r SCCP f r) with (fst (fixpoint f) r) by reflexivity.
      exploit (dsd_pred_njp f WF pc pc' r) ; eauto. go.
      { intros [Hcase1 | [Hcase2 | Hcase3]]; repeat invh and.
        - exploit H3; eauto.
        - exploit (H3 r); eauto.
          invh def; try congruence.
          unfold fn_code in *.
          invh assigned_code_spec; try congruence.
        - congruence.
      }
Qed.

Lemma exec_exec_helper : forall f pc es,
 exec f pc ->
 es = (A_e SCCP f) ->
 DS.executable_node f pc es.
Proof.
  unfold SCCP, A_e ; simpl in *.
  intros. rewrite H0.
  inv H. go.
  invh ex; invh and; go.
Qed.

Lemma same_fn_code1 : forall (f:function) pc res,
  forall (WF : wf_ssa_function f),
    (forall op args res pc', (fn_code f) ! pc <> Some (Iop op args res pc')) ->
    exec f pc ->
    assigned_code_spec (fn_code f) pc res ->
    is_at_Top (A_r SCCP f) res.
Proof.
  intros.
  case_eq (DS.fixpoint f handle_instr (initial f) f); intros lv es FIX.
  generalize FIX; intros FIX'.
  eapply DS.post_fixpoint in FIX as [Hc [Hp _]].
  unfold DS.code_post_fixpoint in *.
  assert (Approx.ge lv !!2 res Unknown).
  { inv H1; eapply Hc; eauto; try eapply exec_exec_helper; go;
    (unfold SCCP, A_e; simpl; rewrite FIX';auto).
  }
  unfold SCCP, A_r ; simpl.
  rewrite FIX'. simpl.
  unfold is_at_Top.
  invh Approx.ge; auto; invh or;  congruence.
Qed.

Lemma G_list_val_list_match_approx : forall f ge sp lv es args rs,
  G_list SCCP ge sp rs (map (A_r SCCP f) args) rs ##2 args ->
  DS.fixpoint f handle_instr (initial f) f = (lv, es) ->
  val_list_match_approx ge sp lv ##2 args rs ##2 args.
Proof.
  induction args ; intros; go.
  simpl in *. inv H.
  econstructor; eauto.
  unfold G, SCCP, A_r in * ; simpl in * ; rewrite H0 in * ; simpl in *.
  apply H4; auto.
Qed.

Require Import SSAtoolinv.
Require Import Utils.

Lemma Iop_correct : forall (f:function) pc sf op args res pc' v rs ge sp m x,
                    forall (WFF: wf_ssa_function f)
                           (SINV: s_inv ge (State sf f sp pc rs m)),
    (fn_code f) ! pc = Some (Iop op args res pc') ->
    eval_operation ge sp op (rs ##2 args) m = Some v ->
    gamma SCCP f ge sp pc rs ->
    exec f pc ->
    dsd f x pc' ->
    G ge sp (rs #2 res <- v) (A_r SCCP f x) (rs #2 res <- v) !!2 x.
Proof.
  intros until x; intros WFF SINV CODE EVAL GAMMA EXE DSD.
  destruct (p2eq x res).
  - subst.
    rewrite P2Map.gss.
    case_eq (DS.fixpoint f handle_instr (initial f) f).
    intros lv es FIX.
    assert (Approx.ge (lv !!2 res) (eval_static_operation op lv ##2 args)).
    { generalize FIX ; intros FIX'.
      apply DS.post_fixpoint in FIX as [Hc _].
      unfold DS.code_post_fixpoint in Hc.
      eapply Hc; eauto.
      unfold SCCP, A_e in * ; simpl in *; auto.
      unfold exec in EXE; simpl in *.
      rewrite FIX' in EXE. simpl in *. auto.
    }
    assert (val_match_approx ge sp (eval_static_operation op lv ##2 args) v).
    { eapply eval_static_operation_correct; eauto.
      exploit (all_used_approx SCCP ge f pc sp rs args); eauto.
      induction args; go.
      intros HG_list.
      eapply G_list_val_list_match_approx; eauto.
    }
    eapply G_increasing; eauto.
    replace (A_r SCCP f res) with ((fst (fixpoint f)) res) by reflexivity.
    unfold fixpoint ; simpl; rewrite FIX; auto.
  - exploit (dsd_pred_not_join_point f WFF pc pc' x); eauto.
    go. 
    intro contra. eapply fn_normalized with (pc := pc) in contra; go.
    + unfold fn_code in *. go.
    + unfold successors, Kildall.successors_list.
      rewrite PTree.gmap1. unfold option_map.
      unfold fn_code in *.
      rewrite CODE. simpl. auto.
    + intros [Hcase1 | [ Hcase2 | Hcase3]]; invh and; try congruence.
      * exploit ext_param_at_top; go.
        intros HTOP.
        replace (A_r SCCP f x) with ((fst (fixpoint f)) x) in * by reflexivity.
        eapply G_top; eauto.
      * rewrite P2Map.gso; eauto.
        exploit GAMMA; eauto.
      * unfold fn_code in *.
        invh assigned_code_spec; try congruence.
Grab Existential Variables.
go. go. go. go.
Qed.

Require Import Dom.
Hint Resolve sdom_dom_pred fn_code_reached fn_entry_pred fn_phicode_inv
             list_nth_z_in.
Hint Unfold reached.
Hint Constructors SSA.step.

Lemma exec_step : forall prog0 ,
                  forall ge0  t sf sp pc rs m (f0:function) s',
   wf_ssa_function f0 ->
   sfg_inv SCCP prog0 sf ->
   gamma SCCP f0 ge0 sp pc rs ->
   OptInv.exec SCCP f0 pc ->
   SSAtool.step ge0 (State sf f0 sp pc rs m) t s' ->
   match s' with
   | State _ f1 _ pc' _ _ => OptInv.exec SCCP f1 pc'
   | Callstate nil _ _ _ => True
   | Callstate (Stackframe _ f2 _ pc' _ :: _) _ _ _ =>
       OptInv.exec SCCP f2 pc'
   | Returnstate _ _ _ => True
   end.
Proof.
 intros.
    case_eq (DS.fixpoint f0 handle_instr (initial f0) f0); intros lv es FIX.
    generalize H3 ; intros STEP.
    inv H3; try solve [exploit exec_node_single_succ; go]; auto.
    + destruct sf; auto.
      destruct s. inv H0; go.
    + assert (es #2 (pc, ifso) = true).
      { generalize FIX ; intros FIX'.
        apply DS.post_fixpoint in FIX as [_ [_ Hes]].
        unfold DS.exec_flags_sound in *.
        assert (Hcfg: cfg f0 pc ifso) by go.
        destruct (classic (es !!2 (pc, ifso) = true)) as [Hcl | Hcl]; auto.
        apply not_true_iff_false in Hcl.
        assert (exists i, (fn_code f0) ! ifso = Some i)
          as [i Hpc'] by (eapply fn_code_closed; go).
        specialize (Hes pc ifso i Hcfg Hcl Hpc').
        destruct Hes.
        + eelim H3; eapply exec_exec_helper; eauto.
          unfold SCCP, A_e ; simpl ; rewrite FIX'; go.
        + flatten H12. destruct H3 as [Hso _].
          specialize (Hso (eq_refl _)).
          eapply eval_static_condition_correct with  (m:= m) (vl:= (rs##2 args)) in Hso.
          congruence.
          eapply G_list_val_list_match_approx; eauto.
          eapply all_used_approx; eauto.
          induction args; go.
      }
      right. exists pc ; split; go.
      unfold fixpoint ; rewrite FIX; simpl; auto.
    + assert (es #2 (pc, ifnot) = true).
      { generalize FIX ; intros FIX'.
        apply DS.post_fixpoint in FIX as [_ [_ Hes]].
        unfold DS.exec_flags_sound in *.
        assert (Hcfg: cfg f0 pc ifnot) by go.
        destruct (classic (es !!2 (pc, ifnot) = true)) as [Hcl | Hcl]; auto.
        apply not_true_iff_false in Hcl.
        assert (exists i, (fn_code f0) ! ifnot = Some i)
          as [i Hpc'] by (eapply fn_code_closed; go).
        specialize (Hes pc ifnot i Hcfg Hcl Hpc').
        destruct Hes.
        + eelim H3; eapply exec_exec_helper; eauto.
          unfold SCCP, A_e ; simpl ; rewrite FIX'; go.
        + flatten H12. destruct H3 as [_ Hifnot].
          specialize (Hifnot (eq_refl _)).
          eapply eval_static_condition_correct with  (m:= m) (vl:= (rs##2 args)) in Hifnot.
          congruence.
          eapply G_list_val_list_match_approx; eauto.
          eapply all_used_approx; eauto.
          induction args; go.
      }
      right. exists pc ; split; go.
      unfold fixpoint ; rewrite FIX; simpl; auto.
    + assert (es #2 (pc, pc') = true).
      { generalize FIX ; intros FIX'.
        apply DS.post_fixpoint in FIX as [_ [_ Hes]].
        unfold DS.exec_flags_sound in *.
        assert (Hcfg: cfg f0 pc pc') by go.
        destruct (classic (es !!2 (pc, pc') = true)) as [Hcl | Hcl]; auto.
        apply not_true_iff_false in Hcl.
        assert (exists i, (fn_code f0) ! pc' = Some i)
          as [i Hpc'] by (eapply fn_code_closed; go).
        specialize (Hes pc pc' i Hcfg Hcl Hpc').
        destruct Hes.
        + eelim H3; eapply exec_exec_helper; eauto.
          unfold SCCP, A_e ; simpl ; rewrite FIX'; go.
        + flatten H12. invh ex ; invh and.
          assert (x = n).
          {
            assert (val_match_approx ge0 sp lv !!2 arg rs !!2 arg).
            exploit used_match_approx; eauto.
            econstructor 10; eauto. intros.
            unfold G, SCCP, A_r in * ; simpl in *; auto.
            rewrite FIX' in *. simpl in *. go.
            unfold val_match_approx in *.
            rewrite H3 in *. congruence.
          }
          subst.
          congruence.
      }
      right. exists pc ; split; go.
      unfold fixpoint ; rewrite FIX; simpl; auto.
Grab Existential Variables.
go. go. go. go. go. go. go. go.
Qed.

End AuxResults.
