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
Require Import Dom.
Require Import SSA.
Require Import SSAtool.
Require Import SSAutils.

(** This file defines a generic program optimization.  In our SSA
 middle-end, we instantiate this to SCCP and GVN-CSE, but in general,
 it could also be instantiated to any intra-procedural, scala
 optimization. *)

(** The optimization can be "conditional", hence we define the type
[m_exec] for storing executable flag for CFG edges. *)

Definition m_exec := P2Map.t bool.

Section Opt.

(** * Definition of the optimization *)
Variable res : Type.
Variable analysis : function -> (res * m_exec).
Variable transf_instr : res -> node -> instruction -> instruction.

Definition transf_function (f : function) : SSA.function :=
  let (res,m_ex) := analysis f in
  mkfunction
     f.(fn_sig)
     f.(fn_params)
     (fn_stacksize f)
     (PTree.map (transf_instr res) (fn_code f))
     f.(fn_phicode)
     f.(fn_max_indice)
     f.(fn_entrypoint).

(** * Proof that it preserves the wf_ssa_function predicate *)
Hypothesis new_code_same_or_Iop : forall f:function,
  wf_ssa_function f ->
  forall pc ins,
    (fn_code f)!pc = Some ins ->
    transf_instr (fst (analysis f)) pc ins = ins
    \/ match ins with
         | Iop _ _ dst pc' 
         | Iload _ _ _ dst pc'
         | Icall _ _ _ dst pc'  
         | Ibuiltin _ _ dst pc' => 
           exists op' args',
           transf_instr (fst (analysis f)) pc ins = Iop op' args' dst pc'
           /\ forall x, In x args' -> exists d : node, def f x d /\ sdom f d pc
         | _ => False
       end.

Lemma fn_params_transf_function : forall f,
  fn_params (transf_function f) = fn_params f.
Proof.
  unfold transf_function; eauto. 
  intros. destruct (analysis f) ; eauto.
Qed.

Lemma fn_phicode_transf_function : forall f,
  fn_phicode (transf_function f) = fn_phicode f.
Proof.
  unfold transf_function; auto. 
  intros. destruct (analysis f) ; eauto.
Qed.

Lemma fn_entrypoint_transf_function : forall f,
  fn_entrypoint (transf_function f) = fn_entrypoint f.
Proof.
  unfold transf_function; auto. 
  intros. destruct (analysis f) ; eauto.
Qed.

Lemma fn_code_transf_function : forall (f:function) pc ins,
 (fn_code f)!pc = Some ins ->
 exists ins, (SSA.fn_code (transf_function f))!pc = Some ins.
Proof.
  simpl. intros. 
  unfold transf_function. 
  destruct (analysis f); simpl.
  rewrite PTree.gmap in *.
  rewrite H. simpl. 
  eexists; eauto.
Qed.

Lemma fn_code_transf_function' : forall f pc ins,
  (SSA.fn_code (transf_function f))!pc = Some ins ->
  exists ins, (fn_code f)!pc = Some ins.
Proof.
  simpl. intros. 
  unfold transf_function in *. 
  destruct (analysis f); simpl in *.
  rewrite PTree.gmap in *.
  destruct ((fn_code f)!pc); eauto.
Qed.

Hint Constructors assigned_code_spec.

Lemma assigned_phi_spec_same : forall (f:function) pc r,
  assigned_phi_spec (f.(fn_phicode)) pc r <->
  assigned_phi_spec ((transf_function f).(fn_phicode)) pc r.
Proof.
  intros. 
  unfold transf_function in *. 
  destruct (analysis f); simpl in *.
  reflexivity.
Qed.

Definition assigned_code_spec2 (code : code) (pc : node) (x:reg) : Prop :=
  match code!pc with
    | Some (Iop _ _ dst succ) 
    | Some (Iload _ _ _ dst succ) 
    | Some (Icall _ _ _ dst succ) 
    | Some (Ibuiltin _ _ dst succ) => dst = x
    | _ => False
  end.

Lemma assigned_code_spec_equiv : forall code pc r,
  assigned_code_spec code pc r <->
  assigned_code_spec2 code pc r.
Proof.
  split; intros H.
  - inv H; unfold assigned_code_spec2; rewrite H0; auto.
  - unfold assigned_code_spec2 in *.
    flatten H; go.
Qed.

Lemma assigned_code_spec_same : forall (f:function) (Hwf:wf_ssa_function f) pc r,
  assigned_code_spec (fn_code f) pc r <->
  assigned_code_spec ((transf_function f).(SSA.fn_code)) pc r.
Proof.
  intros f Hwf pc r.
  repeat rewrite assigned_code_spec_equiv.
  unfold transf_function, assigned_code_spec2; simpl; intros.
  case_eq (analysis f) ; intros lv es Ha ;  simpl in *.
  rewrite PTree.gmap.
  destruct ((fn_code f)!pc) eqn:E; simpl; try tauto.
  destruct (new_code_same_or_Iop f Hwf pc i) as [Hi | Hi]; auto.
  - rewrite Ha in Hi; simpl in * ; rewrite Hi; tauto.
  - rewrite Ha in Hi; simpl in * .
    flatten Hi; try (elim Hi; fail); destruct Hi as (op' & args' & Hi & Hi2); rewrite Hi; tauto.
Qed.

Lemma use_code_transf_function: forall f:function,
  wf_ssa_function f -> forall x u,
  use_code (transf_function f) x u -> 
  use_code f x u \/ exists d, def f x d /\ sdom f d u.
Proof.
  intros f H x u H0.
  inv H0;
  simpl in H1;
  unfold transf_function in *;
  case_eq (analysis f) ; intros lv es Ha ; rewrite Ha in * ; simpl in *;
  rewrite PTree.gmap in H1;
  destruct ((fn_code f)!u) eqn:E; try (inv H1; fail);
  simpl in H1;
  (destruct (new_code_same_or_Iop f H u i) as [Hi | Hi]; auto;
   [left; rewrite Ha in * ; simpl in * ; rewrite Hi in H1; rewrite <- E in H1; econstructor (eauto; fail)
   |idtac]);
  destruct i; 
    try (elim Hi; fail); destruct Hi as (op' & args' & Hi1 & Hi2);
        try (rewrite Ha in * ; simpl in *) ; 
        try (rewrite Ha in * ; simpl in * ; congruence);
    right; apply Hi2; congruence.
Qed.

Lemma new_code: forall pc ins (f:function) (Hwf:wf_ssa_function f),
  (fn_code f)!pc = Some ins ->                  
  successors_instr ins = successors_instr (transf_instr (fst (analysis f)) pc ins).
Proof.
  intros pc ins f Hwf Hi.
  destruct (new_code_same_or_Iop f Hwf pc ins); auto.
  - rewrite H; auto.
  - destruct ins; try (elim H; fail); destruct H as (op' & args' & H1 & H2); rewrite H1; auto.
Qed.

Hint Constructors use_code: ssa.
Hint Constructors use: ssa.

Lemma successors_transf_function: forall (f:function) (Hwf:wf_ssa_function f) pc,
  (successors (transf_function f))!pc = (successors f)!pc.
Proof.
  unfold successors; intros.
  unfold transf_function.
  simpl.
  case_eq (analysis f) ; intros lv es Ha ; simpl in *.
  repeat rewrite PTree.gmap1.
  unfold option_map.
  repeat rewrite PTree.gmap.
  unfold option_map.
  unfold fn_code.
  destruct ((SSA.fn_code f)!pc)  eqn:Heq; simpl; auto.
  exploit fn_code_transf_function; eauto.
  intros [ins' Hins'].
  unfold transf_function in *.
  rewrite Ha in * ; simpl in *.
  replace lv with (fst (analysis f)) by (rewrite Ha ; auto).
  erewrite <- new_code; auto.
Qed.


Lemma same_successors : forall (f:function) (Hwf:wf_ssa_function f),
  successors (transf_function f) = successors f.
Proof.
  unfold successors, transf_function; intros.
  case_eq (analysis f) ; intros lv es Ha ; simpl in *.
  rewrite <- map1_assoc.
  rewrite <- map1_opt.
  apply map_ext; intros.
  replace lv with (fst (analysis f)) by (rewrite Ha ; auto).
  erewrite <- new_code; eauto.
Qed.

Lemma join_point_transf_function : forall (f:function) (Hwf:wf_ssa_function f) j,
  join_point j (transf_function f) <-> join_point j f.
Proof.
  split; intros.
  - inv H. 
  erewrite @same_successors_same_predecessors with 
    (m2:= (fn_code f))
    (f2:= successors_instr) in Hpreds; eauto.
  econstructor; eauto.
  generalize (same_successors f). unfold successors. intros Hsuccs i. 
  rewrite Hsuccs at 1; auto.
  - inv H.
  erewrite @same_successors_same_predecessors with 
    (m2:= (SSA.fn_code (transf_function f)))
    (f2:= successors_instr) in Hpreds; eauto.
  econstructor; eauto.
  generalize (same_successors f). unfold successors. intros Hsuccs i. 
  rewrite Hsuccs at 1; auto.
Qed.


Lemma make_predecessors_transf_function: forall (f:function) (Hwf:wf_ssa_function f),
  (Kildall.make_predecessors (SSA.fn_code (transf_function f)) successors_instr) =
  (Kildall.make_predecessors (fn_code f) successors_instr).
Proof.
  intros.
  eapply same_successors_same_predecessors.
  apply successors_transf_function; auto.
Qed.

Lemma successors_list_transf_function: forall (f:function) (Hwf:wf_ssa_function f) pc,
  (Kildall.successors_list (successors (transf_function f)) pc) =
  (Kildall.successors_list (successors f) pc).
Proof.
  unfold Kildall.successors_list; intros.
  rewrite successors_transf_function; auto.
Qed.


Lemma use_phicode_transf_function: forall f:function,
  wf_ssa_function f -> forall x u,
  use_phicode (transf_function f) x u -> 
  use_phicode f x u.
Proof.
  intros f H x u H0.
  inv H0.
  simpl in PHIB.
  replace (Kildall.make_predecessors (SSA.fn_code (transf_function f))
               successors_instr) with
          (Kildall.make_predecessors (fn_code f) successors_instr) in KPRED.
  - unfold transf_function in *  ; destruct analysis ; go.
  - rewrite make_predecessors_transf_function; auto.
Qed.


Lemma use_transf_function: forall (f:function) x u, 
  wf_ssa_function f ->
  use (transf_function f) x u -> 
  use f x u \/ exists d, def f x d /\ sdom f d u.
Proof.
  intros f x u H H0.
  inv H0.
  - edestruct use_code_transf_function; eauto.
    left; go.
  - apply use_phicode_transf_function in H1; go.
Qed.

Lemma def_transf_function: forall (f:function) x d, 
  wf_ssa_function f ->
  def (transf_function f) x d -> def f x d.
Proof.
  intros f.
  unfold transf_function in * ;
  case_eq (analysis f) ; intros lv es Ha.
  intros x d H H1; inv H1; simpl; go.
  - inv H0; go.
    simpl in *.
    destruct H1 as (pc & Hpc).
    edestruct use_transf_function; eauto.
    unfold transf_function ; rewrite Ha ; simpl; eauto.
    + econstructor 1; eauto.
      econstructor 2; eauto.
      replace (SSA.fn_code f) with (fn_code f).
      intros; rewrite assigned_code_spec_same; auto.
      unfold transf_function ; rewrite Ha ; simpl; eauto.
      reflexivity.

    + destruct H0 as (d & Hd & Hs).
      inv Hd; go.
      * eelim (H3 d). 
        simpl. 
        assert (Has:= (assigned_code_spec_same f H d x)); eauto.
        unfold transf_function in * ; rewrite Ha in * ; simpl in *; auto.
        eapply Has; auto.
      * eelim (H2 d). 
        assert (Has:= (assigned_phi_spec_same f d x)); eauto.
  - simpl in *. 
    assert (Has:= (assigned_code_spec_same f H d x)); eauto.
    unfold transf_function in * ; rewrite Ha in * ; simpl in *; auto.
    eapply Has in H0; auto.
Qed.
  

Lemma cfg_transf_function : forall (f:function) (Hwf:wf_ssa_function f) i j,
  cfg f i j <-> cfg (transf_function f) i j.
Proof.
  intros f i j.
  split; intros.
  - inv H. 
    exploit fn_code_transf_function ; eauto. 
    intros [ins' Hins'].
    intros. unfold transf_function in *.
    case_eq (analysis f) ; intros lv es Ha ; simpl in *.
    rewrite Ha in * ; simpl in *.    
    econstructor; simpl; eauto.
    rewrite PTree.gmap in *.
    unfold fn_code in *.
    unfold option_map in *. rewrite HCFG_ins in *.
    inv Hins'.
    replace lv with (fst (analysis f)) in * by (rewrite Ha ; auto). 
    erewrite <- new_code; eauto.
  - inv H.
    exploit fn_code_transf_function' ; eauto.
    intros [ins' Hins'].
    unfold transf_function in *; case_eq (analysis f) ; intros lv es Ha ;
    rewrite Ha in * ; simpl in *.
    econstructor; simpl; eauto.
    rewrite PTree.gmap in *.
    unfold option_map in *. rewrite Hins' in *.
    inv HCFG_ins.
    replace lv with (fst (analysis f)) in * by (rewrite Ha ; auto).     
    erewrite new_code; eauto. 
Qed.

Lemma reached_transf_function : forall (f:function) (Hwf:wf_ssa_function f) i,
  reached f i <-> reached (transf_function f) i.
Proof.
  split; intros.
  rewrite fn_entrypoint_transf_function.
  apply star_eq with (cfg f); auto.
  intros; rewrite <- cfg_transf_function; auto.
  apply star_eq with (cfg (transf_function f)); auto.
  intros a b; rewrite <- cfg_transf_function; auto.
  rewrite fn_entrypoint_transf_function in *; auto. 
Qed.

Lemma exit_exit : forall (f:function) (Hwf: wf_ssa_function f) pc, 
                    exit f pc <-> exit (transf_function f) pc.
Proof.
  split.
  - intros. 
    assert (Hins: exists ins, (fn_code f) ! pc = Some ins).
    { unfold exit in *.
      flatten NOSTEP; eauto.
      inv H; go.
    }        
    destruct Hins as [ins0 Hins0].
    exploit (fn_code_transf_function f pc); eauto. 
    intros [ins Hins].
    unfold transf_function in *; 
    unfold exit in *; rewrite Hins in *.
    unfold fn_code in *. rewrite Hins0 in *.
    case_eq (analysis f) ; intros lv es Ha ; rewrite Ha in *; simpl in *.
    rewrite PTree.gmap in *.
    unfold option_map in *.
    rewrite Hins0 in *.
    inv Hins.
    exploit new_code_same_or_Iop; eauto.  
    flatten; auto; (intros [Heq | Hcont]; [idtac | elim Hcont]);
    replace lv with (fst (analysis f)) in * by (rewrite Ha ; auto);
    try congruence.
  - intros.
    assert (Hins: exists ins, (SSA.fn_code (transf_function f)) ! pc = Some ins).
    { unfold exit in *.
      flatten NOSTEP; eauto.
      inv H; go.
    }        
    destruct Hins as [ins0 Hins0].
    unfold transf_function in *; 
    unfold exit in *; rewrite Hins0 in *.
    unfold fn_code in *. 
    case_eq (analysis f) ; intros lv es Ha ; rewrite Ha in *; simpl in *.
    rewrite PTree.gmap in *.
    unfold option_map in *.
    flatten Hins0; intuition.         
    + destruct (new_code_same_or_Iop f Hwf pc i); auto.
      * replace lv with (fst (analysis f)) in * by (rewrite Ha ; auto).
        rewrite H0 in H1 ; inv H1; auto.
      * replace lv with (fst (analysis f)) in * by (rewrite Ha ; auto);
        destruct i; try (elim H1; fail); destruct H1 as (op' & args' & H2 & H3);  congruence. 
    + destruct (new_code_same_or_Iop f Hwf pc i); auto.
      * replace lv with (fst (analysis f)) in * by (rewrite Ha ; auto).
        rewrite H0 in H1 ; inv H1; auto.
      * replace lv with (fst (analysis f)) in * by (rewrite Ha ; auto);
        destruct i; try (elim H1; fail); destruct H1 as (op' & args' & H2 & H3);  congruence. 
Qed.

Lemma ssa_path_transf_function : forall (f:function) (Hwf:wf_ssa_function f) i p j,
  SSApath f i p j <-> SSApath (transf_function f) i p j.
Proof.
  split.
  - induction 1; go.
    econstructor 2 with s2; auto.
    inv STEP.
    + assert (cfg (transf_function f) pc pc')
        by (rewrite <- cfg_transf_function; eauto; econstructor; eauto).
      inv H0.
      econstructor; eauto.
      rewrite <- reached_transf_function; auto.
      go.
    + assert (Hins: exists ins, (fn_code f) ! pc = Some ins).
      { unfold exit in *.
        flatten NOSTEP; eauto.
        inv H; go.
      }        
      destruct Hins as [ins0 Hins0].
      exploit (fn_code_transf_function f pc); eauto. 
      intros [ins Hins].
      econstructor; eauto.
      eapply reached_transf_function in CFG; eauto.
      eapply exit_exit; eauto.
  - induction 1; go.
    econstructor 2 with s2; auto.
    inv STEP.
    + assert (cfg f pc pc') by (rewrite cfg_transf_function; eauto; econstructor; eauto).
      inv H0.
      econstructor; eauto.
      go.
    + assert (Hins: exists ins, (SSA.fn_code (transf_function f)) ! pc = Some ins).
      { unfold exit in *.
        flatten NOSTEP; eauto.
        inv H; go.
      }        
      destruct Hins as [ins0 Hins0].      
      eelim fn_code_transf_function' ; eauto. 
      intros ins' H'.
      econstructor; eauto.
      eapply exit_exit; eauto.
Qed.
  
Lemma dom_transf_function : forall (f:function) (Hwf:wf_ssa_function f) i j,
  dom f i j <-> dom (transf_function f) i j.
Proof.
  split; intros.
  - inv H; constructor.
    + rewrite <- reached_transf_function; auto.
    + unfold entry in *. intros.
      apply PATH.
      rewrite ssa_path_transf_function; auto.
      rewrite fn_entrypoint_transf_function in *.
      auto.
  - inv H; constructor.
    + rewrite reached_transf_function; auto.
    + intros.
      apply PATH.
      rewrite <- ssa_path_transf_function; auto.
      rewrite fn_entrypoint_transf_function in *.
      unfold entry in *; auto.      
Qed.

Lemma transf_function_Inop : forall (f:function) (Hwf:wf_ssa_function f) pc jp,
  (fn_code f) ! pc = Some (Inop jp) ->
  (SSA.fn_code (transf_function f)) ! pc = Some (Inop jp).
Proof.
  intros.
  unfold transf_function; simpl.
  case_eq (analysis f) ; intros lv es Ha ; try rewrite Ha in * ;  simpl in *.
  rewrite PTree.gmap.
  rewrite H; simpl.
  destruct (new_code_same_or_Iop f Hwf pc (Inop jp)); auto.
  - replace lv with (fst (analysis f)) by (rewrite Ha ; auto). rewrite H0; auto.
  - elim H0.
Qed.

Lemma transf_function_preserve_wf_ssa_function : forall (f:function),
  wf_ssa_function f -> wf_ssa_function (transf_function f).
Proof.
  constructor.
  +
  generalize (fn_ssa _ H).
  unfold unique_def_spec; split; intros.
  repeat rewrite <- assigned_phi_spec_same; auto.
  repeat rewrite <- assigned_code_spec_same; auto.
  destruct H0; auto.
  unfold transf_function in *.
  destruct (analysis f) in * ; simpl in *; eauto.
  destruct H0 as [_ H0]; eauto.
  
  +
  intros x; rewrite fn_params_transf_function; intros T.
  elim fn_ssa_params with (1:=H) (2:=T); split; intros.
  rewrite <- assigned_code_spec_same; auto.
  rewrite <- assigned_phi_spec_same; auto.

  +
  intros x u d Hu Hd.
  rewrite <- dom_transf_function.
  apply def_transf_function in Hd; auto.
  apply use_transf_function in Hu; auto.
  destruct Hu as [Hu|[y [Hu1 Hu2]]].
  - apply fn_strict with x; auto.
  - assert (y=d) by (eapply ssa_def_unique; eauto); subst.
    inv Hu2; auto.
  - assumption.

  +
  intros x pc Hu Ha.
  rewrite <- assigned_code_spec_same in Ha; auto.
  apply use_code_transf_function in Hu; auto.
  destruct Hu.
  - eelim fn_use_def_code; eauto.
  - destruct H0 as [d [D1 D2]].
    assert (def f x pc) by eauto.
    destruct D2.
    elim NEQ; eapply ssa_def_unique; eauto.

  +
  intros pc block args x.
  rewrite fn_phicode_transf_function.
  rewrite make_predecessors_transf_function; auto.
  eapply fn_wf_block; eauto.
  
  +
  intros.
  rewrite join_point_transf_function in H0; auto.
  rewrite successors_list_transf_function in H1; auto.
  exploit fn_normalized; eauto; intros.
  exploit transf_function_Inop; eauto.
 
  +
  intros.
  rewrite join_point_transf_function; auto.
  rewrite fn_phicode_transf_function; auto.
  eapply fn_phicode_inv; eauto.

  +
  intros pc ins.
  rewrite <- reached_transf_function; intros; auto.
  eelim fn_code_transf_function'; eauto.
  
  +
  intros pc pc' instr Hi Hj.
  assert (cfg f pc pc') by (rewrite cfg_transf_function; eauto; econstructor; eauto).
  inv H0.
  exploit fn_code_closed; eauto.
  intros [ii HH].
  eapply fn_code_transf_function; eauto. 

  +
  exploit fn_entry; eauto.
  intros [s Hs].
  exists s; rewrite fn_entrypoint_transf_function.
  exploit transf_function_Inop; eauto.

  +
  intros pc; rewrite <- cfg_transf_function; auto; rewrite fn_entrypoint_transf_function.
  apply fn_entry_pred; auto.
Qed.

Program Definition transf_function_tool (f : function) : function :=
  let f' := transf_function f in
  Build_function f' _ (Build_ssa_tool f' (fn_ext_params _ f) (fn_dom_test _ f) _ _).
Next Obligation.
  apply transf_function_preserve_wf_ssa_function.
  apply (wf f).
Qed.
Next Obligation.
  apply fn_ext_params_correct.
  inv H. 
  - unfold transf_function in H0; simpl in H0.
    destruct analysis; go.
  - destruct H0 as [pc H0].
    rewrite fn_phicode_transf_function in H1.
    exploit use_transf_function; eauto.
    + apply f.
    + destruct 1.
      * econstructor 2; eauto.
        intros.
        rewrite (assigned_code_spec_same f); eauto.
        apply f.
      * destruct H as (d & H & _).
        inv H; go.
        eelim H2; rewrite <- assigned_code_spec_same; eauto. apply f.
        eelim H1; eauto.
Qed. 
Next Obligation.
  rewrite <- dom_transf_function.
  eapply fn_dom_test_correct; eauto.
  rewrite reached_transf_function; auto.
  apply f.
  apply f.
Qed.

Definition transf_fundef_tool (f: fundef) : fundef :=
   AST.transf_fundef transf_function_tool f.

Definition transf_program_tool (p: program) : program :=
   transform_program transf_fundef_tool p.

(*
Lemma transf_program_preserve_wf_ssa : forall prog,
  SSA.wf_ssa_program prog -> SSA.wf_ssa_program (transf_program prog).
Proof.
  repeat intro.
  elim transform_program_function with (1:=H0).
  intros g [F1 F2].
  destruct g; simpl in *; inv F2; constructor.
  apply transf_function_preserve_wf_ssa_function.
  assert (F:=H _ _ F1); inv F; auto.
Qed.
*)

End Opt.