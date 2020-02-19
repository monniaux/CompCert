
Require Import Coqlib.
Require Import Errors.
Require Import AST.
Require Import RTL.
Require Import Values.
Require Import Op.
Require Import Events.
Require Import SSA.
Require Import Utils.
Require Import SSAvalid.
Require Import SSAvalidator_proof.
Require Import SSAgen.
Require Import SSAgenproof.
Require Import DLib.
Require Import RTLdfsproof.
Require Import Globalenvs.
Require Import SSAtool.
Require Import Smallstep.

Module RemoveTool.
  Definition transf_function (f: SSAtool.function) : SSA.function := func f.
  Definition transf_fundef (fd: SSAtool.fundef) : SSA.fundef :=
    AST.transf_fundef transf_function fd.
  Definition transf_program (p: SSAtool.program) : SSA.program :=
    transform_program transf_fundef p.

  Section TRANSF.
  Variable prog: program.

  Let tprog := transf_program prog.
  Let ge : genv := Genv.globalenv prog.
  Let tge : SSA.genv := Genv.globalenv tprog.


  Lemma symbols_preserved:
    forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof.
    intro. unfold ge, tge.
    apply Genv.find_symbol_transf.
  Qed.

  Inductive match_stackframes : list SSA.stackframe -> list stackframe -> Prop :=
  | match_stackframes_nil: match_stackframes nil nil
  | match_stackframes_cons: 
      forall res f sp pc rs s ts 
             (STACK : (match_stackframes s ts)),
        match_stackframes
          ((SSA.Stackframe res (func f) sp pc rs) :: s)
          ((Stackframe res f sp pc rs) :: ts).


  Inductive match_states : SSAtool.state -> SSA.state -> Prop :=
  | match_states_State: forall s st f sp pc rs m
    (MS: match_stackframes s st),
    match_states (State st f sp pc rs m) (SSA.State s (func f) sp pc rs m) 
  | match_callstate_Callstate: forall s st f args m
    (MS: match_stackframes s st),
    match_states (Callstate st f args m) (SSA.Callstate s (transf_fundef f) args m)
  | match_callstate_Returnstate: forall s st v m
    (MS: match_stackframes s st),
    match_states (Returnstate st v m) (SSA.Returnstate s v m).

  Lemma function_ptr_translated:
    forall (b: Values.block) (f: fundef),
      Genv.find_funct_ptr ge b = Some f ->
      Genv.find_funct_ptr tge b = Some (transf_fundef f).
  Proof.  
    intros. 
    exact (Genv.find_funct_ptr_transf (transf_fundef) _ _ H).
  Qed.

  Lemma function_ptr_translated_rev:
    forall (b: Values.block) (tf: SSA.fundef),
      Genv.find_funct_ptr tge b = Some tf ->
      exists f, Genv.find_funct_ptr ge b = Some f /\ transf_fundef f = tf.
  Proof.  
    intros. 
    eapply (Genv.find_funct_ptr_rev_transf (transf_fundef) prog b H). 
  Qed.

  Lemma sig_function_translated:
    forall f,
      SSA.funsig (transf_fundef f) = funsig f.
  Proof.
    intros. destruct f; reflexivity.
  Qed.

  Lemma transf_initial_states:
    forall st1, SSAtool.initial_state prog st1 ->
                exists st2, SSA.initial_state tprog st2 /\ match_states st1 st2.
  Proof.
    intros. inversion H.
    exploit function_ptr_translated; eauto; intro FIND.
    exists (SSA.Callstate nil (transf_fundef f) nil m0); split.
    econstructor; eauto.
    - apply Genv.init_mem_transf; auto.
    - replace (prog_main tprog) with (prog_main prog).
      rewrite symbols_preserved. eauto.
      reflexivity.
    - rewrite <- H3. apply sig_function_translated.
    - constructor; go .
  Qed.

  Lemma store_init_data_same : forall (g : Genv.t fundef unit) (tg : Genv.t SSA.fundef unit) 
                                       l m a b,
     (forall (s: ident), Genv.find_symbol tg s = Genv.find_symbol g s) ->
     Genv.store_init_data g m a b l = Genv.store_init_data tg m a b l.
  Proof.
    unfold Genv.store_init_data; intros.
    flatten.
  Qed.

  Lemma store_init_data_list_same : 
    forall (g : Genv.t fundef unit) (tg : Genv.t SSA.fundef unit) l m a b,
     (forall (s: ident), Genv.find_symbol tg s = Genv.find_symbol g s) ->
     Genv.store_init_data_list g m a b l = Genv.store_init_data_list tg m a b l.
  Proof.
    induction l; simpl; auto; intros.
    rewrite (store_init_data_same g tg); auto.
    flatten.
    auto.
  Qed.

  Lemma init_mem_same_aux : forall g tg,
    (forall (s: ident), Genv.find_symbol tg s = Genv.find_symbol g s) ->
    forall (l:list (ident * globdef fundef unit)) m0,
      Genv.alloc_globals g m0 l =
      Genv.alloc_globals tg m0 (map (transform_program_globdef transf_fundef) l).
  Proof.
    induction l; simpl; go.
    intros m0.
    assert (Hg:Genv.alloc_global g m0 a =
               Genv.alloc_global tg m0 (transform_program_globdef transf_fundef a)).
      { destruct a as (id & ifo). 
        destruct ifo.
        - reflexivity.
        - simpl transform_program_globdef. 
          simpl; flatten.
          * generalize (store_init_data_list_same g tg (gvar_init v) m1 b 0 H); congruence.
          * generalize (store_init_data_list_same g tg (gvar_init v) m1 b 0 H); congruence.
          * generalize (store_init_data_list_same g tg (gvar_init v) m1 b 0 H); congruence. }
    rewrite <- Hg.        
    flatten.
  Qed.

  Lemma init_mem_same : Genv.init_mem prog = Genv.init_mem tprog.
  Proof.
    unfold Genv.init_mem.
    unfold tprog, transf_program, transform_program; simpl. 
    eapply init_mem_same_aux; eauto.
    intros.
    apply symbols_preserved.
  Qed.

  Lemma transf_initial_states_rev:
    forall st1, SSA.initial_state tprog st1 ->
                exists st2, SSAtool.initial_state prog st2 /\ match_states st2 st1.
  Proof.
    intros. inversion H.
    exploit function_ptr_translated_rev; eauto; intros (f' & FIND1 & FIND2).
    subst.
    exists (Callstate nil f' nil m0); split; go.
    econstructor; eauto.
    -  rewrite init_mem_same; auto.
    - replace (prog_main tprog) with (prog_main prog).
      rewrite <- symbols_preserved. eauto.
      reflexivity.
    - rewrite <- H3. rewrite sig_function_translated. auto.
  Qed.

  Lemma transf_final_states:
    forall st1 st2 r, 
      match_states st1 st2 ->
      final_state (SSAtool.semantics prog) st1 r ->
      final_state (SSA.semantics tprog) st2 r.
  Proof.
    intros. inv H0. inv H. inv MS. go.
  Qed.

  Lemma transf_final_states_rev:
    forall st1 st2 r, 
      match_states st1 st2 ->
      final_state (SSA.semantics tprog) st2 r ->
      final_state (SSAtool.semantics prog) st1 r.
  Proof.
    intros. inv H0. inv H. inv MS. go.
  Qed.

  Lemma transf_ros_correct:
    forall ros rs f,
      find_function ge ros rs = Some f ->
      SSA.find_function tge ros rs = Some (transf_fundef f).
  Proof.
    intros. destruct ros; simpl in *.
    - destruct (rs !!2 r); simpl in H; try discriminate.
      flatten H.
      simpl.
      flatten.
      apply function_ptr_translated; auto.
    - rewrite symbols_preserved.
      flatten.
      apply function_ptr_translated; auto.
  Qed.

  Lemma transf_ros_correct_rev:
    forall ros rs tf,
      SSA.find_function tge ros rs = Some tf ->
      exists f, find_function ge ros rs = Some f /\ transf_fundef f = tf.
  Proof.
    intros. destruct ros; simpl in *.
    - destruct (rs !!2 r); simpl in H; try discriminate.
      flatten H.
      simpl.
      flatten.
      apply function_ptr_translated_rev; auto.
    - rewrite <- symbols_preserved.
      flatten.
      apply function_ptr_translated_rev; auto.
  Qed.

  Lemma varinfo_preserved:
    forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
  Proof.
    intros; unfold ge, tge, tprog, transf_program. 
    apply Genv.find_var_info_transf.
  Qed.

  Lemma transf_step_correct:
   forall (s1 : state (SSAtool.semantics prog)) (t : Events.trace)
     (s1' : state (SSAtool.semantics prog)),
   Step (SSAtool.semantics prog) s1 t s1' ->
   forall s2 : state (SSA.semantics tprog),
   match_states s1 s2 ->
   exists s2' : state (SSA.semantics tprog),
     Step (SSA.semantics tprog) s2 t s2' /\ match_states s1' s2'.
  Proof.
    intros s1 t s1' H s2 H0.
    inv H; inv H0; go.
    - econstructor; split; [idtac|go].
      econstructor; eauto.
      erewrite eval_operation_preserved; eauto.
      exact symbols_preserved.
    - econstructor; split; [idtac|go].      
      rewrite <- eval_addressing_preserved with (ge2:=tge) in H2; eauto.
      go.
      exact symbols_preserved.
    - rewrite <- eval_addressing_preserved with (ge2:=tge) in H2; eauto.
      go.
      exact symbols_preserved.
    - econstructor; split; [idtac|go].
      eapply SSA.exec_Icall; eauto.
      + eapply transf_ros_correct; auto.
      + apply sig_function_translated.
    - econstructor; split; [idtac|go].
      eapply SSA.exec_Itailcall; eauto.
      + eapply transf_ros_correct; auto.
      + apply sig_function_translated.
    - econstructor; split; [idtac|go].
      eapply SSA.exec_Ibuiltin; eauto.
      eapply external_call_symbols_preserved; eauto.
      exact symbols_preserved. 
      exact varinfo_preserved.
    - econstructor; split; [idtac|go].
      eapply SSA.exec_function_external; eauto.
      eapply external_call_symbols_preserved; eauto.
      exact symbols_preserved. exact varinfo_preserved.
    - inv MS.
      econstructor; split; [idtac|go].
      eapply SSA.exec_return; eauto. 
  Qed.

  Lemma transf_step_correct_rev:
   forall (s1 : state (SSA.semantics tprog)) (t : Events.trace)
     (s1' : state (SSA.semantics tprog)),
   Step (SSA.semantics tprog) s1 t s1' ->
   forall s2 : state (SSAtool.semantics prog),
   match_states s2 s1 ->
   exists s2' : state (SSAtool.semantics prog),
     Step (SSAtool.semantics prog) s2 t s2' /\ match_states s2' s1'.
  Proof.
    intros s1 t s1' H s2 H0.
    inv H; inv H0; go.
    - econstructor; split; [idtac|go].
      econstructor; eauto.
      erewrite eval_operation_preserved; eauto.
      intros; rewrite symbols_preserved; reflexivity.
    - econstructor; split; [idtac|go].      
      eapply exec_Iload; eauto.
      rewrite <- eval_addressing_preserved with (ge2:=tge); eauto.
      intros; rewrite symbols_preserved; reflexivity.
    - econstructor; split; [idtac|go].      
      eapply exec_Istore; eauto.
      rewrite <- eval_addressing_preserved with (ge2:=tge); eauto.
      intros; rewrite symbols_preserved; reflexivity.
    - edestruct transf_ros_correct_rev as (tf & F1 & F2); eauto.
      subst.
      econstructor; split; [idtac|go].
      eapply exec_Icall; eauto.
      rewrite sig_function_translated; auto.
    - edestruct transf_ros_correct_rev as (tf & F1 & F2); eauto.
      subst.
      econstructor; split; [idtac|go].
      eapply exec_Itailcall; eauto.
      rewrite sig_function_translated; auto.
    - econstructor; split; [idtac|go].
      eapply exec_Ibuiltin; eauto.
      eapply external_call_symbols_preserved; eauto.
      intros; rewrite symbols_preserved; reflexivity. 
      intro; rewrite varinfo_preserved; reflexivity.
    - destruct f0; inv H4.
      econstructor; split; [idtac|go].
      eapply exec_function_internal; eauto.
    - destruct f; inv H4.
      econstructor; split; [idtac|go].
      eapply exec_function_external; eauto.
      eapply external_call_symbols_preserved; eauto.
      intros; rewrite symbols_preserved; reflexivity. 
      intro; rewrite varinfo_preserved; reflexivity.
    - inv MS.
      econstructor; split; [idtac|go].
      eapply exec_return; eauto. 
  Qed.

  Lemma transf_program_correct :
    forward_simulation (SSAtool.semantics prog) (SSA.semantics tprog).
  Proof.
    apply forward_simulation_step with match_states.
    - apply symbols_preserved.
    - apply transf_initial_states.
    - apply transf_final_states.
    - apply transf_step_correct.
  Qed.

  Lemma transf_program_correct_rev :
    forward_simulation (SSA.semantics tprog) (SSAtool.semantics prog).
  Proof.
    apply forward_simulation_step with (fun s1 s2 => match_states s2 s1).
    - intros; rewrite symbols_preserved; reflexivity.
    - apply transf_initial_states_rev.
    - intros; eapply transf_final_states_rev; eauto.
    - intros; eapply transf_step_correct_rev; eauto.
  Qed.

  Lemma wf_ssa_program_transf_program :
    wf_ssa_program tprog.
  Proof.
    intro.
    destruct f; constructor.
    unfold tprog, transf_program, transform_program, prog_defs in *.
    apply list_in_map_inv in H.
    destruct H as (ii & I1 & I2).
    unfold transform_program_globdef in I1.
    flatten I1.
    destruct f0; inv H.
    destruct f0; simpl; auto.
  Qed.

  End TRANSF.

End RemoveTool.


Section PRESERVATION.

  Variable prog: RTL.program.
  Variable tprog: program.
  Hypothesis TRANSF_PROG: transf_program prog = OK tprog.

  Lemma ssa_tprog_exists : 
     SSAgen.transf_program prog = OK (RemoveTool.transf_program tprog).
  Proof.
    unfold transf_program, SSAgen.transf_program in *.
    unfold transform_partial_program in *.
    unfold transform_partial_program2 in *.
    unfold RemoveTool.transf_program, transform_program.
    revert TRANSF_PROG.
    unfold bind in *; flatten.
    - intros T; inv T.
      simpl.
      f_equal.
      f_equal.
      generalize dependent (prog_defs prog).
      intros l1; revert l l0.
      induction l1; simpl; intros.
      + inv Eq; inv Eq0; reflexivity.
      + flatten Eq.
        * unfold bind in *; flatten Eq.
          simpl.
          f_equal; eauto.
          repeat f_equal.
          { destruct f; simpl in *.
            - unfold transf_function in *.
              destruct (transf_function_rich f); inv Eq4.
              destruct s as (tf & F1 & F2 & F3).
              inv H0.
              rewrite F2 in Eq3; inv Eq3.
              simpl.
              reflexivity.
            - inv Eq3; inv Eq4; reflexivity. }
        * unfold bind in *; flatten Eq.
          simpl.
          repeat f_equal.
          eapply IHl1; eauto.
    - intros T; inv T.
      apply False_ind.
      generalize dependent (prog_defs prog).
      intros l1; revert l.
      induction l1; simpl; intros; go.
      flatten Eq.
      + unfold bind in *; flatten Eq.
        eelim IHl1; eauto.
      + destruct f; inv Eq4; inv Eq3.
        unfold bind in *; flatten Eq.
        unfold transf_function in *.
        destruct (transf_function_rich f) as [(f0 & tf & F1 & F2)|].
        * subst.
          inv Eq1.
          congruence.
        * inv Eq1.
      + unfold bind in *; flatten Eq.
        eelim IHl1; eauto.
  Qed.

  Theorem transf_program_correct:
    forward_simulation (RTL.semantics prog) (SSAtool.semantics tprog).
  Proof.
    eapply compose_forward_simulation.
    - eapply SSAgenproof.transf_program_correct; eauto.
      eapply ssa_tprog_exists.
    - eapply RemoveTool.transf_program_correct_rev.
  Qed.

End PRESERVATION.


