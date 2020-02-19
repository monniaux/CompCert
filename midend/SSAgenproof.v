(** Proof of correctness of the SSA generation phase. It combines the
   correctness proofs of the three main phases (i) code normalization
   [RTLnorm] (ii) unreachable code removal [RTLdfs] and (iii)
   validation of the externally generated SSA code [SSAvalidproof] *)

Require Import Coqlib.
Require Import Errors.
Require Import AST.
Require Import Globalenvs.
Require Import Values.
Require Import RTL.
Require Import SSA.
Require Import Utils.
Require Import Compo.
Require Import Smallstep.
Require Import SSAgen.
Require RTLdfs.
Require SSAvalid.
Require SSAvalidproof.
Require RTLdfsproof.
Require RTLnormproof.
Require SSAvalidator_proof.

(** The generation algorithm is built by composing several
   transformations.  Hence, we show several lemmas that helps
   decomposing these, by reasoning about monadic computations.*)
Section COMPO_TRANS.

Lemma transf_fundef_first : forall fd fd', 
  transf_fundef fd = OK fd' ->
  exists fd1,   RTLnorm.transl_fundef_opt fd = OK fd1. 
Proof.
  intros.
  unfold transf_fundef in H.
  destruct fd ; simpl in *; eauto.
  monadInv H. unfold bind.
  unfold transf_function in EQ. monadInv EQ.
  rewrite EQ0 ; eauto.
Qed.  

Lemma transf_fundef_trans : forall fd fd' fd1 fd2, 
  transf_fundef fd = OK fd' ->
  RTLnorm.transl_fundef_opt fd = OK fd1 ->
  RTLdfs.transf_fundef fd1 = OK fd2 -> 
  SSAvalid.transf_fundef fd2 = OK fd'. 
Proof.
  intros.
  unfold transf_fundef in H.
  destruct fd ; simpl in *; eauto.
  monadInv H.  monadInv H0. 
  
  unfold transf_function in EQ. monadInv EQ.
  rewrite EQ0 in * ; eauto. inv EQ1.
  simpl in H1. unfold bind in H1. rewrite EQ in *. inv H1 ; auto.
  simpl. unfold bind.
  rewrite EQ3 ; auto.
  inv H0; auto.
  inv H. simpl in H1 ; inv H1. auto.
Qed.  


Lemma map_partial_first : forall lp ltp,
  transf_globdefs transf_fundef (fun v : unit => OK v) lp = OK ltp ->
  exists ox, 
    transf_globdefs RTLnorm.transl_fundef_opt (fun v : unit => OK v) lp = OK ox.
Proof.
  induction lp; intros.
  - simpl in *.
    inv H. eauto.
  - simpl in H. 
    destruct a as [a_id a_fun].
    destruct a_fun.
    * 
      case_eq (transf_fundef f) ; intros a_fun' Ha_fun'OK; rewrite Ha_fun'OK in *; try congruence.
      monadInv H. 
      unfold transf_fundef in Ha_fun'OK.
      exploit IHlp; eauto. intros [oxx Hoxx].      
      simpl. rewrite Hoxx.
      case_eq (RTLnorm.transl_fundef_opt f); intros.
      simpl. eauto.
      
      destruct f; simpl in *; try congruence.
      unfold transf_function in *.
      monadInv Ha_fun'OK.
      monadInv EQ0.
      rewrite EQ1 in *. simpl in *. congruence. 
      
    * monadInv H.  
      exploit IHlp; eauto. intros [oxx Hoxx].      
      simpl.
      rewrite Hoxx. simpl. eauto.
Qed.

Lemma map_partial_second : forall lp tp ox,
  transf_globdefs transf_fundef (fun v : unit => OK v) lp = OK tp ->
  transf_globdefs RTLnorm.transl_fundef_opt (fun v : unit => OK v) lp = OK ox ->
  exists ox', 
    transf_globdefs RTLdfs.transf_fundef (fun v : unit => OK v) ox = OK ox'.
Proof.
  induction lp; intros.
  - simpl in *.
    inv H0. inv H. simpl. eauto.
  - simpl in H.
    destruct a as [a_id a_fun].
    destruct a_fun.
    * 
      case_eq (transf_fundef f) ; intros a_fun' Ha_fun'OK; rewrite Ha_fun'OK in *; try congruence.
      monadInv H. 
      unfold transf_fundef in Ha_fun'OK.
      simpl in H0.
      
      case_eq (RTLnorm.transl_fundef_opt f) ; intros a_fun'' Ha_fun''OK; rewrite Ha_fun''OK in *; try congruence.
      monadInv H0. 

      exploit IHlp; eauto. intros [oxx Hoxx].      
      simpl. rewrite Hoxx.
            
      case_eq (RTLdfs.transf_fundef a_fun''); intros.
      simpl. eauto.
      
      destruct a_fun''; simpl in *; try congruence.
      unfold transf_function in *.
      clear EQ0.
      clear dependent Hoxx.
      unfold transf_partial_fundef in *. 
      destruct f. 
      {  monadInv Ha_fun'OK.
         monadInv EQ0.
         unfold RTLnorm.transl_fundef_opt , transf_partial_fundef in *.
         monadInv Ha_fun''OK.
         rewrite EQ2 in EQ1. inv EQ1.
         rewrite EQ0 in *. inv H.
      }      
      {  unfold RTLnorm.transl_fundef_opt , transf_partial_fundef in *.
         monadInv Ha_fun'OK.
         congruence. 
      }
    * monadInv H.
      simpl in H0.
      monadInv H0.
      exploit IHlp; eauto. intros [oxx Hoxx].      
      simpl.
      rewrite Hoxx. simpl. eauto.
Qed.
  
Lemma map_partial_trans: 
  forall lp ltp ox ox',
    transf_globdefs transf_fundef (fun v : unit => OK v) lp = OK ltp ->
    transf_globdefs RTLnorm.transl_fundef_opt (fun v : unit => OK v) lp = OK ox ->
    transf_globdefs RTLdfs.transf_fundef (fun v : unit => OK v) ox = OK ox' ->
    transf_globdefs SSAvalid.transf_fundef (fun v : unit => OK v) ox' = OK ltp.
Proof.
  induction lp ; intros.
  - inv H. inv H0. inv H1. simpl ; auto.
  - simpl in *.
    destruct a as [a_id a_fun].
    destruct a_fun.
    * case_eq (transf_fundef f) ; intros; rewrite H2 in *.
      { 
        exploit transf_fundef_first ; eauto. intros [a_fun1 Ha_fun1].  
        rewrite Ha_fun1 in *. 
        monadInv H0. simpl in *. 
        case_eq (RTLdfs.transf_fundef a_fun1) ; intros; rewrite H0 in *.
        { 
          monadInv H1.  monadInv H.
          simpl. 
          erewrite transf_fundef_trans ; eauto.
          unfold bind.
          erewrite IHlp ; eauto.
        } 
        { inv H1. }
     }
     { inv H. }
    *
      monadInv H.
      monadInv H0. 
      monadInv H1.
      simpl.
      unfold bind.
      erewrite IHlp; eauto. 
Qed. 

Lemma virt_tp : forall p tp, 
  transf_program p = OK tp -> 
  exists tp_norm, exists tp_dfs, 
    RTLnorm.transl_program_opt p = OK tp_norm 
    /\ RTLdfs.transf_program tp_norm = OK tp_dfs 
    /\ SSAvalid.transf_program tp_dfs = OK tp.
Proof.
  intros.
  unfold transf_program in H.
  unfold transform_partial_program in *. monadInv H.
  exploit map_partial_first ; eauto. intros [ox Hox].  
  exploit map_partial_second ; eauto. intros [ox' Hox'].    
  exists {| prog_defs := ox; prog_main := prog_main p |}.  
  exists {| prog_defs := ox'; prog_main := prog_main p |}.  
  unfold RTLnorm.transl_program_opt. 
  unfold transform_partial_program. 
  unfold transform_partial_program2. 
  unfold bind. rewrite Hox at 1.  split ; auto.

  unfold RTLdfs.transf_program. 
  unfold transform_partial_program. 
  unfold transform_partial_program2. 
  unfold bind. rewrite Hox' at 1.  split ; auto.  
  
  exploit map_partial_trans ; eauto.
  intros Hox''. 
  unfold SSAvalid.transf_program.
  unfold transform_partial_program. 
  unfold transform_partial_program2. 
  simpl. 
  rewrite Hox''.
  auto. 
Qed.

End COMPO_TRANS.

(** A generated SSA program satisfies the [wf_ssa_program] predicate. *)  
Lemma transf_program_wf : forall p tp, 
  transf_program p = OK tp ->
  wf_ssa_program tp.
Proof.
  intros.
  exploit virt_tp ; eauto. intros [tp_norm [tp_dfs [Hnorm [Hdfs Hvalid]]]].
  eapply SSAvalidator_proof.transf_program_wf ; eauto.
  eapply RTLdfsproof.transf_program_wf_dfs ; eauto.  
Qed.


(** * Semantic preservation *)

Section PRESERVATION.

  Variable prog: RTL.program.
  Variable tprog: SSA.program.
  Hypothesis TRANSF_PROG: SSAgen.transf_program prog = OK tprog.
  
  Let ge : RTL.genv := Genv.globalenv prog.
  Let tge : SSA.genv := Genv.globalenv tprog.

  Lemma symbols_preserved:
    forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof.
    intro. unfold ge, tge.
    apply Genv.find_symbol_transf_partial with SSAgen.transf_fundef.
    exact TRANSF_PROG.
  Qed.

  Lemma functions_translated:
    forall (v: val) (f: RTL.fundef),
      Genv.find_funct ge v = Some f ->
      exists tf, Genv.find_funct tge v = Some tf /\ SSAgen.transf_fundef f = OK tf.
  Proof.
    apply (Genv.find_funct_transf_partial SSAgen.transf_fundef). 
    exact TRANSF_PROG.
  Qed.

  Lemma function_ptr_translated:
    forall (b: block) (f: RTL.fundef),
      Genv.find_funct_ptr ge b = Some f ->
      exists tf, Genv.find_funct_ptr tge b = Some tf /\ SSAgen.transf_fundef f = OK tf.
  Proof.
    apply (Genv.find_funct_ptr_transf_partial SSAgen.transf_fundef).
    exact TRANSF_PROG.
  Qed.

  Lemma var_info_preserved:
    forall (b: block), Genv.find_var_info tge b = Genv.find_var_info ge b.
  Proof.
    intro. unfold ge, tge.
    apply Genv.find_var_info_transf_partial with SSAgen.transf_fundef.
    exact TRANSF_PROG.
  Qed.

  (** The simulation relation is built by composing the simulation
relation that holds for each elementary transformation. *)
  Inductive match_states : RTL.state -> SSA.state -> Prop :=
  | match_states_def: forall s_rtl s_ssa s_norm s_dfs
    (MS1: RTLnormproof.match_states s_rtl s_norm)
    (MS2: RTLdfsproof.match_states s_norm s_dfs)
    (MS3: SSAvalidproof.match_states s_dfs s_ssa),
    match_states s_rtl s_ssa.
Hint Constructors match_states.

  
Lemma sig_function_translated:
  forall f tf,
    SSAgen.transf_fundef f = OK tf ->
    SSA.funsig tf = RTL.funsig f.
Proof.
  intros f tf. destruct f; simpl; intros.
  monadInv H.
  monadInv EQ. 
  exploit RTLnormproof.sig_function_translated ; eauto. intros Hsig1.
  exploit RTLdfsproof.sig_function_translated ; eauto. intros Hsig0.
  simpl. exploit SSAvalidproof.sig_function_translated ; eauto.
  congruence.
  inv H; auto.
Qed.

Hint Constructors 
  RTLnormproof.match_states 
  RTLdfsproof.match_states 
  SSAvalidproof.match_states 
  RTLnormproof.match_stackframes
  RTLdfsproof.match_stackframes
  SSAvalidproof.match_stackframes. 
    
Lemma transf_initial_states:
  forall st1, RTL.initial_state prog st1 ->
    exists st2, SSA.initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H.
  exploit function_ptr_translated ; eauto. intros [tf [Hfind Htrans]].
  exists (Callstate nil tf nil m0); split.
  assert (MEM: (Genv.init_mem tprog) = Some m0) by (eapply (Genv.init_mem_transf_partial); eauto).
  econstructor; eauto.
  rewrite symbols_preserved.
  rewrite (transform_partial_program_main _ _ TRANSF_PROG). auto.
  rewrite <- H3. 
  apply sig_function_translated; auto.  
  unfold transf_fundef in Htrans.
  case_eq f ; intros ff Hff ; inv Hff ; monadInv  Htrans.
  monadInv EQ. 
  eapply match_states_def  with 
    (RTL.Callstate nil (Internal x0) nil m0)
    (RTL.Callstate nil (Internal x1) nil m0) ; eauto;
    (econstructor ; eauto).
  simpl. unfold bind ; rewrite EQ0 ; eauto.
  unfold RTLdfs.transf_fundef. simpl ; unfold bind ; rewrite EQ ; eauto.
  constructor. 
  constructor.
  eapply RTLdfsproof.transf_function_ppoints2 ; eauto. 
  eapply RTLdfsproof.transf_function_ppoints6 ; eauto. 
  eapply RTLdfsproof.transf_function_ppoints3 ; eauto. 
  unfold SSAvalid.transf_fundef. simpl. unfold bind. rewrite EQ2; auto. 
  
  eapply match_states_def with
    (RTL.Callstate nil (External ff) nil m0)
    (RTL.Callstate nil (External ff) nil m0) ; eauto.
  econstructor ; eauto.
  constructor.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> RTL.final_state st1 r -> SSA.final_state st2 r.
Proof.
  intros. 
  inv H0. inv H. 
  eapply RTLnormproof.transf_final_states  with (r:= r) in MS1 ; eauto; [|constructor].
  eapply RTLdfsproof.transf_final_states  with (r:= r) in MS2 ; eauto. 
  eapply SSAvalidproof.transf_final_states  with (r:= r) in MS3 ; eauto. 
Qed.

Theorem transl_step_correct:
  forall s1 t s2, RTL.step ge s1 t s2 ->
    forall s1', 
      match_states s1 s1' ->
      exists s2',
        Smallstep.plus SSA.step tge s1' t s2' /\ match_states s2 s2'.
Proof.
  exploit virt_tp ; eauto. 
  intros [P_NORM [P_DFS [TRANSF_NORM [TRANSF_DFS TRANSF_VALID]]]].
  intros. inv H0.
  eapply RTLnormproof.transl_step_correct in H ; eauto. 
  destruct H as [s_aux [Hstep_aux Hmatch_aux]].
  eapply simulation_plus_plus with (step1:= RTL.step) (step2:= RTL.step) 
    (genv' := (Genv.globalenv P_DFS)) 
    (3:= MS2) in Hstep_aux ; eauto.  
  destruct Hstep_aux as [s_aux' [Hstep_aux' Hmatch_aux']].  
  
  eapply simulation_plus_plus with (step1:= RTL.step) (step2:= SSA.step) 
    (genv' := (Genv.globalenv tprog))
    (3:= MS3) in Hstep_aux' ; eauto.  
  destruct Hstep_aux' as [s_aux'' [Hstep_aux'' Hmatch_aux'']].
  exists s_aux''. split; auto.  
  eapply match_states_def with (s_norm:= s_aux) (s_dfs:= s_aux') ; auto.

  intros.
  exploit (SSAvalidproof.transl_step_correct P_DFS tprog); eauto.
  eapply RTLdfsproof.transf_program_wf_dfs; eauto. 

  intros. destruct H1 as [s2' [Hplus Hmatch]].
  exists s2'. split ; auto. eapply plus_one ; eauto.

  intros.
  exploit (RTLdfsproof.transl_step_correct P_NORM P_DFS); eauto.
  intros. destruct H1 as [s2' [Hplus Hmatch]].
  exists s2'. split ; auto. eapply plus_one ; eauto.
Qed.

(** Final semantics preservation result *)
Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (SSA.semantics tprog).
Proof.
  eapply forward_simulation_plus.
  eexact symbols_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact transl_step_correct. 
Qed.

End PRESERVATION.


