(** This file contains some properties that are satisfied by
well-typed functions.  For functions that satisfy certain structural
invariants, we show that they satisfy some of the invariants required
for [wf_ssa_functions] *)

Require Import Classical.
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Registers.
Require Import Floats.
Require Import Utils.

Require Import RTL.
Require Import RTLutils.
 
Require Import Dom.
Require Import SSA. 
Require Import SSAutils. 
Require Import Path.
Require Import Conventions1.

Require Import SSAvalidspec.
Require Import Utilsvalidproof.
Require Import Kildall.
Require Import KildallComp.
Require Import Relation_Operators.
Require Import LightLive.
Require DomCompute.

Notation path_step := (fun f => path_step (cfg f) (exit f) (entry f)).
Section WT_FUNCTION.

Variable f_rtl : RTL.function.
Variable f : function.
Variable G : SSAvalid.tgamma.
Variable live: PMap.t Regset.t.

Hypothesis fn_wt : wt_function f_rtl f live G.
Hypothesis fn_wfi : wf_init f G.
Hypothesis fn_erased : check_erased_spec f_rtl f.
Hypothesis fn_wfl : wf_live f_rtl (Lout live).

Hypothesis fn_ssa : unique_def_spec f.
Hypothesis fn_ssa_params1 : forall x pc, In x (fn_params f) -> ~ assigned_code_spec (fn_code f) pc x.
Hypothesis fn_ssa_params2 : forall x pc, In x (fn_params f) -> ~ assigned_phi_spec (fn_phicode f) pc x.

Hypothesis fn_reached : forall pc ins, (fn_code f) ! pc = Some ins -> reached f pc.
Hypothesis fn_entry : exists s, (fn_code f) ! (fn_entrypoint f) = Some (Inop s).
Hypothesis fn_phicode_code : forall pc block, 
    (fn_phicode f) ! pc = Some block -> 
    exists ins, (fn_code f) ! pc = Some ins.
Hypothesis fn_code_closed:
    forall pc pc' instr, f.(fn_code) ! pc = Some instr ->
    In pc' (successors_instr instr) -> 
    exists instr', f.(fn_code) ! pc' = Some instr'.
Hypothesis fn_entrypoint_inv: 
    (exists i, (f.(fn_code) ! (f.(fn_entrypoint)) = Some i)) /\ 
    ~ join_point f.(fn_entrypoint) f.
Hypothesis fn_code_inv2: forall jp pc i, (join_point jp f) ->
  In jp ((successors f) !!! pc) ->
  f.(fn_code) ! jp = Some i ->
  f.(fn_code) ! pc = Some (Inop jp).
Hypothesis fn_phicode_inv1: forall phib jp i,
    f.(fn_code) ! jp = Some i -> 
    f.(fn_phicode) ! jp = Some phib ->
    join_point jp f.
Hypothesis fn_phicode_inv2: forall jp i,
    join_point jp f ->
    f.(fn_code) ! jp = Some i -> 
    exists phib, f.(fn_phicode) ! jp = Some phib.

Notation ui := (erase_reg).
Notation gi := (get_index).
Notation entry := fn_entrypoint.
Hint Constructors rtl_path_step rtl_path.


(** * Utility lemmas about indexed registers. *)
Lemma pair_fst_snd : forall (A B C: Type) (f: A -> B * C) (a:A),
  f a = ((fst (f a)),(snd (f a))).
Proof.
  intros. destruct (f0 a). auto.
Qed.

Lemma rmap_fst_snd : forall dst x, 
  dst = (ui x, gi x) ->
  dst = x.
Proof.
  intros.
  unfold erase_reg, get_index in *.
  destruct x; simpl in *; congruence.
Qed.  

Lemma rmap_uigi : forall x, x = (ui x, gi x).
Proof.
  destruct x; simpl in *; congruence.
Qed.
Hint Resolve rmap_uigi : bij.

(** * Utility lemmas on the erasure function *)
Lemma elim_structural : forall pc pc' instr instr' block,
  (fn_code f) ! pc = Some instr ->
  (fn_code f) ! pc' = Some instr' ->
  (fn_phicode f) ! pc' = Some block ->
  In pc' (successors_instr instr) -> instr = Inop pc'.
Proof.
  intros.
  exploit (fn_code_inv2 pc' pc) ; eauto.
  unfold successors_list.
  unfold successors.
  rewrite PTree.gmap1.
  unfold option_map. simpl. rewrite H. auto.
  intros. simpl in *; congruence.
Qed.

Lemma erased_funct_erased_instr_2: forall pc f tf rinstr,
  check_erased_spec f tf  ->
  ((SSA.fn_code tf)!pc = Some rinstr) ->
  exists pinstr,
    ((RTL.fn_code f) ! pc = Some pinstr)
    /\ (pinstr =  (erase_instr rinstr)).
Proof.
  clear.
  intros; inv H.
  exists (erase_instr rinstr).
  split ; auto.
  rewrite HCODE ; eauto.
  unfold erase_code.  
  rewrite PTree.gmap. 
  unfold option_map. rewrite H0 ; auto.
Qed.

Lemma erased_assigned_code_spec : 
  forall pc x, 
    RTLutils.assigned_code_spec (RTL.fn_code f_rtl) pc (ui x) ->
    exists idx, assigned_code_spec (fn_code f) pc (((ui x),idx)).
Proof.
  intros.
  inv H;
  
  ((exploit_dstr erased_funct_erased_instr ; eauto);
  (unfold erase_instr in * ; destruct x0 ; allinv; try congruence; inv H4);

  try ((case_eq r; intros uix idx Hx);
  (exists idx ; unfold erase_reg in *; rewrite Hx in *;simpl in *);
  (destruct s0 ; congruence);
  (destruct s0 ; congruence);
  (destruct o ; congruence)));
  try (solve 
  [
    (destruct s0 ; congruence)
    | (destruct o ; congruence)]).

destruct x; destruct r; inv H8; simpl in *; subst.
repeat econstructor; rewrite H3; eauto.

destruct x; destruct r; inv H9; simpl in *; subst.
exists p0; econstructor 2; eauto.

destruct r; destruct x; destruct s0; inv H6; simpl in *.
exists p; econstructor 3; eauto.
exists p; econstructor 3; eauto.

destruct x; destruct r; inv H8; simpl in *; subst.
exists p0; econstructor 4; eauto.
Qed.


Lemma use_code_spec : 
  forall pc x, 
    use_code f x pc ->
    use_rtl_code f_rtl (ui x) pc.
Proof.
  intros.
  inv H ; 
  (exploit erased_funct_erased_instr_2 ; eauto);
  (intros [pinstr [Hcode Hins]]; inv Hins);
  (unfold erase_instr in * ; simpl in *).

  econstructor 1 ; eauto; (eapply in_map ; eauto).
  econstructor 2 ; eauto; (eapply in_map ; eauto).
  econstructor 3 ; eauto; (eapply in_map ; eauto).
  econstructor 4 ; eauto; (eapply in_map ; eauto).
  econstructor 5 ; eauto. econstructor 2 ; eauto. (eapply in_map ; eauto).
  econstructor 6 ; eauto. inv H1; eauto. econstructor 2 ; eauto. (eapply in_map ; eauto).
  econstructor 8 ; eauto. inv H1; eauto. econstructor 2 ; eauto. (eapply in_map ; eauto).
  econstructor 7 ; eauto. (eapply in_map ; eauto).
  econstructor 9 ; eauto. (eapply in_map ; eauto).
  econstructor 10 ; eauto. 
  econstructor 11 ; eauto. 
Qed.

Lemma use_ins_code : forall pc x, 
  use f x pc ->
  exists ins, (fn_code f) ! pc = Some ins.
Proof.
  intros. inv H.
  inv H0 ; eauto.
  inv H0. 
  exploit index_pred_some_nth; eauto. intros. 
  exploit nth_error_some_in ; eauto. intros.
  eapply (make_predecessors_some (fn_code f) successors_instr pc0) ; eauto.
  unfold make_preds, successors_list in *. 
  destruct ((make_predecessors (fn_code f) successors_instr) ! pc0). auto.
  inv H0. 
Qed.

(** * Utility lemmas about [cfg] [edge], and [path] *)
Lemma cfg_edge_aux : forall pc pc',
  pc <> pc' ->
  (cfg f) ** pc pc' ->
  exists pred, is_edge f pred pc'.
Proof.
  induction 2 ; intros.
  inv H0. exists x. econstructor ; eauto.
  congruence.
  destruct (peq z y).
  inv e. exploit IHclos_refl_trans1 ; eauto.
  exploit IHclos_refl_trans2 ; eauto.
Qed.
    
Lemma cfg_edge : forall pc i,
  pc <> (entry f)  ->
  reached f pc ->
  (fn_code f) ! pc = Some i ->
  exists pred, is_edge f pred pc.
Proof.
  intros.
  exploit (cfg_edge_aux (entry f)) ; eauto.
Qed.

Hint Constructors rtl_cfg.
Lemma cfg_rtl_cfg : forall f tf pc1 pc2,
  check_erased_spec f tf ->
  cfg tf pc1 pc2 -> 
  rtl_cfg f pc1 pc2.
Proof.
  clear. intros.
  inv H0.
  exploit erased_funct_erased_instr_2 ; eauto.
  intros [pinstr [Hcode Hins]]. inv Hins.
  destruct ins; simpl in * ; eauto.
  (destruct s0; allinv; (inv HCFG_in; eauto)).
  econstructor; eauto; simpl; auto.
  intuition.
  econstructor; eauto; simpl; auto.
  intuition.
Qed.  

Lemma cfg_star_rtl_cfg_star : forall f tf, 
  check_erased_spec f tf ->
  forall pc pc', (cfg tf)** pc pc' -> (rtl_cfg f)** pc pc'.
Proof.
  clear.
  intros f tf Her. 
  eapply (clos_refl_trans_ind node) ; eauto.
  intros. inv H.
  exploit erased_funct_erased_instr_2 ; eauto.
  intros [pinstr [Hcode Hins]]. inv Hins.
  destruct ins; simpl in * ; eauto.
  (destruct s0; allinv; (inv HCFG_in; eauto)).
  constructor.
  econstructor; eauto; simpl; auto.
  intuition.
  constructor.
  econstructor; eauto; simpl; auto.
  intuition.
Qed.

Lemma reached_rtl_reached : forall f tf, 
  check_erased_spec f tf ->
  forall pc , reached tf pc -> 
  rtl_reached f pc.
Proof.
  clear. intros. unfold rtl_reached.
  eapply cfg_star_rtl_cfg_star ; eauto. 
  replace (RTL.fn_entrypoint f) with (fn_entrypoint tf); auto.
  inv H; auto.
Qed.  


Require Import DLib.

Lemma path_step_rtl_path_step : forall f tf s1 s2 pc, 
  check_erased_spec f tf ->
  path_step tf s1 pc s2 -> 
  rtl_path_step f s1 pc s2.
Proof.
  clear. intros. 
  inv H0.
  - inv STEP;
    ((exploit erased_funct_erased_instr_2 ; eauto); 
     intros [pinstr [Hcode Hins]]; inv Hins;
     econstructor ; eauto; 
     [ eapply reached_rtl_reached ; eauto
     | destruct ins ; (simpl ; auto);
       [(destruct s0; allinv; auto)
       | (destruct s0; allinv; auto)
       | (destruct o; allinv; auto)]]).
  - destruct ((fn_code tf) ! pc) eqn: Heq;
    unfold exit in * ; rewrite Heq in *; flatten NOSTEP; go;
    ((exploit erased_funct_erased_instr_2 ; eauto); 
     intros [pinstr [Hcode Hins]]; inv Hins;
     econstructor ; eauto;
     [ eapply reached_rtl_reached ; eauto
     | simpl; flatten; simpl; eauto]; 
    simpl; flatten; eauto).
    simpl; flatten; eauto.
    simpl; flatten; eauto.    
Qed.
    
Notation path := (fun f => path (cfg f) (exit f) (entry f)).

Lemma path_rtl_path : forall f tf p s1 s2,
  check_erased_spec f tf ->
  path tf s1 p s2 -> 
  rtl_path f s1 p s2.
Proof.
  clear.
  induction p ; intros; (inv H0; econstructor ; eauto).
  eapply path_step_rtl_path_step ; eauto.
Qed.
Hint Resolve path_rtl_path.

Lemma path_cfg : forall f p s1 s2, 
  path f s1 p s2 ->
  match s1, s2 with
    | (PState pc1), (PState pc2) => (cfg f **) pc1 pc2
      | _, _ => True
  end.
Proof.
  clear.
  induction 1 ; intros.
  destruct s; auto.
  destruct s1; destruct s3; auto.
  destruct s2.
  apply rt_trans with pc2; eauto.
  apply rt_step. 
  inv STEP. auto.
  econstructor ; eauto.
  exploit (@path_from_ret_nil node) ; eauto.
  intro Heq. inv Heq. inv H.
Qed.

Lemma path_reached : forall f p pc, 
  path f (PState (entry f)) p (PState pc) ->
  reached f pc.
Proof.
  intros. 
  simpl in H.
  eapply path_cfg in H ; eauto.
Qed.  

Lemma path_first : forall p pc pc', 
  path f (PState pc) p (PState pc') ->
  pc <> pc' ->
  exists pc'', exists p', exists p'',
    path f (PState pc) p' (PState pc'') /\
    ~ In pc' p' /\
    pc'' <> pc' /\
    path_step f (PState pc'') pc'' (PState pc') /\
    p = p'++(pc''::p'').
Proof.
  clear.
    induction p ; intros; inv H. 
    congruence.
    assert (a = pc) by (inv STEP; auto). inv H.
    destruct s2.
    destruct (peq pc0 pc').
    (* peq *)
    inv e.  exists pc. exists nil. exists p.
    split; eauto.  econstructor ; eauto.
    (* diff *)
    exploit IHp ; eauto. intros [pc'' [p'  [p'' [Hp' [Hpc'' [Hdiff [Hnotin Happ]]]]]]].
    exists pc''. exists (pc::p'). exists p''.
    split ; auto.
    econstructor ; eauto. 
    split ; auto.
    intro Hcont. inv Hcont. congruence. elim Hpc'' ; auto.
    split. intro Hcont. inv Hcont. congruence.
    split ; eauto. simpl. rewrite Happ ; auto.
    exploit (@path_from_ret_nil node); eauto. intros Heq ; inv Heq.
    inv PATH.
  Qed.

Lemma use_reached : forall pc x, 
  use f x pc ->
  reached f pc.
Proof.
  intros.
  exploit use_ins_code ; eauto.
  intros [ins Hins]. 
  eapply fn_reached ; eauto.  
Qed.

(** * Tactics *)
Ltac error_struct tf pc pc' :=
  (match goal with
     | [ H1 : (fn_code tf) ! pc = Some _ ,
         H2 : (fn_phicode tf) ! pc' = Some _
       |- _ ] =>
     let Hcont := fresh "Hcont" in
       (exploit (fn_code_closed pc pc') ; eauto) ;
       (allinv ; simpl ; auto) ;
       (intros [ins' Hins'] ; (exploit (elim_structural pc pc'); eauto);
         [ allinv ; (simpl) ; auto | (intros HHCont; inv HHCont)])
     | [ H1 : (fn_code tf) ! pc = Some _ ,
         H2 : (fn_phicode tf) ! pc' = Some _
       |- _ ] =>
       (exploit (fn_code_closed pc pc') ; eauto);
       (intros [ins' Hins'] ; (exploit (elim_structural pc pc'); eauto)) ; (intro HHcont ; inv HHcont)
   end).

Ltac well_typed :=
  match goal with
    | [ Hwt : wt_instr _ _ _ |- _ ] => inv Hwt
  end.

(** * Properties required for [wf_ssa_function]  *)

Lemma unique_def_spec_def : forall x d1 d2, 
  def f x d1 -> def f x d2 -> d1 <> d2 ->  False.
Proof.
  intros.
  destruct fn_ssa as [Hssa1 Hssa2].
  destruct fn_entry as [succ Hentry].
  inv H ; inv H0 ; inv H ; inv H2;
  try congruence;
  try solve [
      exploit fn_ssa_params1 ; eauto
    | exploit fn_ssa_params2 ; eauto
    | exploit H3 ; eauto 
    | exploit H4 ; eauto; intuition
    |   (eelim (Hssa1 x d1 d2) ; eauto; intuition ; eauto)].
Qed.

Lemma def_def_eq : forall x d1 d2,
  def f x d1 ->
  def f x d2 ->
  d1 = d2.
Proof.
  intros.
  destruct (peq d1 d2) ; auto.
  eelim (unique_def_spec_def x d1 d2) ; eauto.
Qed.  

Lemma use_code_gamma : forall u x
  (USE : use_code f x u),
  G u (ui x) = (gi x).
Proof.
  intros.
  destruct x as (x,idx); simpl in *.
  inv USE;
  match goal with 
    | [Hins : (fn_code f) ! u = Some (Icall _ _ _ _ _) |- _ ] => inv H0
    | [Hins : (fn_code f) ! u = Some (Itailcall _ _ _) |- _ ] => inv H0
    | [Hins : (fn_code f) ! u = Some (Ijumptable _ _) |- _ ] => 
      destruct tbl as [ _ | s succ]; [ idtac  |]
    | _ => idtac
  end ;
  let tac := ((inv fn_wt);
      ((assert (Ho : is_out_node f u) by ( solve [econstructor 2 ; eauto | econstructor 1 ; eauto])) ;
        (exploit (WTO u) ; eauto ; intro Hwto) ;
        (inv Hwto; allinv; try error_struct f u s);
        ( well_typed ; eauto))) in 
  (match goal with 
    | [Hins : (fn_code f) ! u = Some (Ireturn _) |- _ ] => tac
    | [Hins : (fn_code f) ! u = Some (Itailcall _ _ _) |- _]  => tac            
    | _ => 
      try ((inv fn_wt);
      ((assert (He : is_edge f u s) by (econstructor ; eauto ; simpl ; auto)) ;
          (exploit (WTE u s) ; eauto ; intro Hwte);
          (inv Hwte; allinv; try error_struct f u s);
          ( well_typed ; eauto)))
  end).  

  ((inv fn_wt);
    ((assert (Ho : is_out_node f u) by ( solve [econstructor 3 ; eauto | econstructor 1 ; eauto])) ;
      (exploit (WTO u) ; eauto ; intro Hwto) ;
      (inv Hwto; allinv; try error_struct f u s);
      ( well_typed ;  eauto))). 
Qed.

Lemma use_phicode_gamma : forall u x
  (USE : use_phicode f x u),
  G u (ui x) = (gi x).
Proof.
  intros.
  inv USE. 
  inv fn_wt. 
  assert (He : is_edge f u pc) by (eapply pred_is_edge ; eauto).

  exploit WTE ; eauto ; intro Hwte.
  inv Hwte ; allinv.
  inv WTPHID0.
  case_eq x ; intros rx ix Hx.
  unfold erase_reg, get_index ; inv Hx ; simpl.
  destruct dst.
  exploit USES ; eauto. intro Hphiu. 
  exploit index_pred_some_nth ; eauto. intros Hnth.
  exploit (@list_map_nth_some node (Registers.reg -> positive) G) ; eauto. intros Hnth'.
  exploit phiu_nth ; eauto. intros [i [Hbij' HG]]. 
  congruence.
Qed.
  
Lemma use_gamma : forall x u, 
  use f x u ->
  G u (ui x) = gi x.
Proof.
  intros. inv H. 
  eapply use_code_gamma ; eauto.
  eapply use_phicode_gamma ; eauto.
Qed.

Lemma wt_use_isdef : forall x u,  use f x u -> exists d, def f x d.
Proof.
  intros.
  exploit use_gamma ; eauto. intros HGamma.
  destruct (classic (exists pc, assigned_code_spec (fn_code f) pc x)).
  destruct H0. eauto.
  destruct (classic (exists pc, assigned_phi_spec (fn_phicode f) pc x)).
  destruct H1. eauto.
  inv fn_wfi.
  exists (fn_entrypoint f). eauto.
  econstructor ; eauto.
  econstructor 2 ; eauto.
Qed.

Lemma gamma_entry_param : forall x d, 
  G (entry f) (ui x) = gi x ->
  def f x d ->
  d = (entry f).
Proof.
  intros. inv fn_wt.
  inv H0.
  (* entry *)
  auto.
  (* defined in code *)
  inv H1;
  (assert (Hedge : is_edge f d succ) by (econstructor; eauto; simpl; auto)) ;
  (exploit WTE ; eauto ; intros Hwte;
    (inv Hwte; allinv; [
    inv EIDX ; simpl in *; try (intuition; fail)
    | error_struct f d succ])).
  (* defined in phicode *)
  inv H1. destruct H2 as [args Hin].
  exploit fn_phicode_code ; eauto. intros [ins Hins].
  exploit fn_phicode_inv1 ; eauto. intros Hjp.
  inv Hjp. 
  assert (Hpred : exists pc, exists k, index_pred (make_predecessors (fn_code f) successors_instr) pc d = Some k).
  assert (exists pc, In pc l).
    destruct l; simpl in *.
    apply False_ind; omega.
    eauto.
  destruct H1 as [pc H1].
  exists pc.
  assert (In pc ((make_predecessors (fn_code f) successors_instr)!!!d)).
  { unfold successors_list; rewrite Hpreds; auto. }
  
  exploit @make_predecessors_some ; eauto. intros (ipc & Hpc).
  exploit @make_predecessors_correct2; eauto. intros Hind.
  eapply index_pred_instr_some ; eauto.
  destruct Hpred as [pred [k Hidxp]].  
  exploit pred_is_edge ; eauto. intros Hedge.
  (exploit WTE ; eauto ; intros Hwte). 
  inv Hwte; allinv. 
  inv PEIDX. exploit (H1 x) ; eauto. econstructor ; eauto.
  eapply rmap_uigi. intuition.
Qed.

Lemma gamma_path_def : forall p s,
  DomCompute.path f p s ->
  match s with 
    | PStop => True
    | PState pc =>
      forall x d i, 
        def f (x,i) d ->
        G pc x = i ->
        Regset.In x (Lin f_rtl pc (Lout live)) -> 
        (In d p
          \/ (d = pc /\ 
            ~ ( use_code f (x,i) pc /\ 
              assigned_code_spec (fn_code f) pc (x,i))))
  end.
Proof.
  induction 1 ; intros ; auto. 

  (* nil : defined in params *)
  right.
  exploit gamma_entry_param ; eauto. 
  unfold erase_reg,  get_index. simpl; auto.
  intro Heq; inv Heq ; split ; auto. 
  intros [_ Hcont2].  destruct fn_entry  as [se Hentry].
  inv Hcont2 ; allinv.
  
  (* pc::p *)
  assert (is_edge f pc pc') by (econstructor ; eauto).
  inv fn_wt.
  
  destruct (classic (Regset.In x (Lin f_rtl pc (Lout live)))).
  
  exploit WTE ; eauto. intros Hwte.
  inv Hwte; allinv. destruct ins.
  
  (* nop *)
  inv WTI. rewrite <- H7 in *. exploit IHpath ; eauto.
  intros [HH1 | [HH21 HH22]]. 
  left ; eauto.
  inv HH21. left ; eauto.
  
  (* iop *)  
  inv WTI. 
  destruct (p2eq (x, G pc' x) (r0,i)).
  (* x is def at pc *)
  inv e. 
  left. left. 
  (destruct (peq d pc); auto) ;
  (exploit (unique_def_spec_def (r0, G pc' r0) d pc) ; eauto).
  intuition.  
   
  (* another x version is def at pc *)
  exploit IHpath  ; eauto.
  rewrite <- H10.
  unfold update. destruct (peq x r0).
  inv e. elim n0. rewrite <- H10.
  unfold update ; unfold erase_reg. 
  rewrite peq_true; auto.
  auto.

  intros [HH1 | [HH21 HH22]]. 
  left ; eauto.
  inv HH21 ; eauto.
  
  (* iload *)  
  inv WTI. 
  
  destruct (p2eq (x, G pc' x) (r0, i)).
  (* x is def at pc *)
  inv e. 
  left ; left.
  (destruct (peq d pc); auto) ;
  (exploit (unique_def_spec_def (r0, G pc' r0) d pc) ; eauto).
  intuition.  
   
  (* another x version is def at pc *)
  exploit IHpath ; eauto.
  rewrite <- H11.
  unfold update. destruct (peq x r0).
  inv e. elim n0. rewrite <- H11.
  unfold update, erase_reg. 
  rewrite peq_true. 
  auto.
  auto.

  intros [HH1 | [HH21 HH22]]. 
  left ; eauto.
  inv HH21 ; eauto.

  
  (* istore *)  
  inv WTI ; rewrite <- H11 in * ; eauto.
  exploit IHpath ; eauto. 
  intros [HH1 | [HH21 HH22]]. 
  left ; eauto.
  inv HH21 ; eauto.
 
  (* icall *)  
  inv WTI. 
  
  destruct (p2eq (x, G pc' x) (r0, i)).
  (* x is def at pc *)
  inv e. unfold erase_reg, get_index in * ; simpl in *. 
  left ; left.
  (destruct (peq d pc); auto) ;
  (exploit (unique_def_spec_def (r0, G pc' r0) d pc) ; eauto).
  intuition.  
   
  (* another x version is def at pc *)
  exploit IHpath ; eauto.
  rewrite <- H11.
  unfold update. destruct (peq x r0).
  inv e. elim n0. rewrite <- H11.
  unfold update, erase_reg. 
  rewrite peq_true. 
  auto.
  auto.

  intros [HH1 | [HH21 HH22]]. 
  left ; eauto.
  inv HH21 ; eauto.

  destruct (p2eq (x, G pc' x) (r0, i)).
  (* x is def at pc *)
  inv e. unfold erase_reg, get_index in * ; simpl in *. 
  left ; left.
  (destruct (peq d pc); auto) ;
  (exploit (unique_def_spec_def (r0, G pc' r0) d pc) ; eauto).
  intuition.  
   
  (* another x version is def at pc *)
  exploit IHpath ; eauto.
  rewrite <- H11.
  unfold update. destruct (peq x r0).
  inv e. elim n0. rewrite <- H11.
  unfold update, erase_reg. 
  rewrite peq_true. 
  auto.
  auto.

  intros [HH1 | [HH21 HH22]]. 
  left ; eauto.
  inv HH21 ; eauto.  
  
  (* itailcall *)  
  inv WTI. rewrite <- H9 in * ; eauto.
  exploit IHpath ; eauto.
  intros [HH1 | [HH21 HH22]]. 
  left ; eauto.
  inv HH21 ; eauto.

  rewrite <- H9 in * ; eauto.
  exploit IHpath ; eauto.
  intros [HH1 | [HH21 HH22]]. 
  left ; eauto.
  inv HH21 ; eauto.

  
  (* builtin *)
  inv WTI.     
  
  destruct (p2eq (x, G pc' x) (r0, i)).
  (* x is def at pc *)
  inv e0. 
  left ; left. 
  (destruct (peq d pc); auto) ;
  (exploit (unique_def_spec_def (r0, G pc' r0) d pc) ; eauto).
  intuition.  
   
  (* another x version is def at pc *)
  exploit IHpath ; eauto.
  rewrite <- H10.
  unfold update. destruct (peq x r0).
  subst.
  elim n0.
  rewrite <- H10.
  unfold update; rewrite peq_true ;auto.
  auto.

  intros [HH1 | [HH21 HH22]]. 
  left ; eauto.
  inv HH21 ; eauto.

  (* icond *)  
  inv WTI. rewrite <- H10 in * ; eauto.
  exploit IHpath ; eauto.
  intros [HH1 | [HH21 HH22]]. 
  left ; eauto.
  inv HH21 ; eauto.


  (* ijmptable *)  
  inv WTI. rewrite <- H8 in * ; eauto.
  exploit IHpath ; eauto.
  intros [HH1 | [HH21 HH22]]. 
  left ; eauto.
  inv HH21 ; eauto.
  
  (* ireturn *)
  inv WTI. rewrite <- H6 in * ; eauto.
  exploit IHpath ; eauto.
  intros [HH1 | [HH21 HH22]]. 
  left ; eauto.
  inv HH21 ; eauto.

  rewrite <- H7 in * ; eauto.
  exploit IHpath ; eauto.
  intros [HH1 | [HH21 HH22]]. 
  left ; eauto.
  inv HH21 ; eauto.
  
  (* join point at pc' *)
  inv WTPHID.
  destruct (classic (assigned (x, G pc' x) block)).
   
  (*  assig in the block *)
  right.
  assert (d = pc').
  (destruct (peq d pc'); auto) ;
  (exploit (unique_def_spec_def (x, G pc' x) d pc') ; eauto).
  intuition.  split ; auto. 
  
  intros [Hcont1 Hcont2].
  inv H5. 
  inv fn_ssa. 
  destruct (H5 (x, G pc' x) pc' pc') as [_ [_ [Hcont _]]].
  exploit Hcont ; eauto.  
  
  (* not assig in the block *) 
  destruct (classic (erased_reg_assigned x block)).
  inv H5. inv H6.
  destruct x0; simpl in *. 
  exploit (ASSIG (r, p0)); auto. 
  right.
  assert (d = pc'). destruct (peq d pc') ; auto. 
  rewrite H6 in *. intuition. 
  intuition. inv H7.  intuition.
    
  exploit (NASSIG x) ; eauto.
  intros. intros Hcont.  elim H5. 
  exists (x,i). split ; auto. subst; simpl; auto.
  intros [HH1 | HH2].
  
  rewrite HH1 in * ; eauto.
  exploit IHpath ; eauto.
  intros [HH1' | [HH21' HH22']]. 
  left ; eauto.
  inv HH21' ; eauto.
  
  intuition.
  
  (* x not live at pc *)
  exploit (wf_live_incl f_rtl (Lout live) fn_wfl pc pc')  ; eauto.
  eapply cfg_rtl_cfg ; eauto. econstructor ; eauto.
  intros [HH1 | HH2]; auto. 
  intuition. 

  exploit (erased_assigned_code_spec pc (x, G pc' x)) ; eauto.
  intros [idx Hass]. 
  inv Hass ; allinv.
  
  (* iop *)
  exploit WTE ; eauto.
  intros Hwte. inv Hwte ; allinv ; try (error_struct f pc pc').
  
  inv WTI.
  rewrite <- H11 in *. 
  inv H11.

  assert (d = pc).
  unfold update in * ; rewrite peq_true in *.
  (destruct (peq d pc); auto) ;
  (exploit (unique_def_spec_def (x, idx) d pc) ; eauto).
  intuition.  inv H4. eauto. 

  (* load *)
  exploit WTE ; eauto.
  intros Hwte. inv Hwte ; allinv ; try (error_struct f pc pc').
  
  inv WTI.
  rewrite <- H12 in *. 
  inv H12.

  assert (d = pc).
  unfold update in * ; rewrite peq_true in *.
  (destruct (peq d pc); auto) ;
  (exploit (unique_def_spec_def  (x, idx) d pc) ; eauto).
  intuition.  inv H4. auto. 

                      
  (* icall *)
  exploit WTE ; eauto.
  intros Hwte. inv Hwte ; allinv ; try (error_struct f pc pc').
  
  inv WTI.
  rewrite <- H12 in *. 
  inv H12.
  assert (d = pc).
  unfold update in * ; rewrite peq_true in *.
  (destruct (peq d pc); auto) ;
  (exploit (unique_def_spec_def ((x, idx)) d pc) ; eauto).
  intuition.  inv H4. auto. 

  rewrite <-H12 in *. inv H12.
  assert (d = pc).
  unfold update in * ; rewrite peq_true in *.
  (destruct (peq d pc); auto) ;
  (exploit (unique_def_spec_def ((x, idx)) d pc) ; eauto).
  intuition.  inv H4. auto. 
  
  (* builtin *)
  exploit WTE ; eauto.
  intros Hwte. inv Hwte ; allinv ; try (error_struct f pc pc').
  
  inv WTI.
  rewrite <- H11 in *. 
  inv H11.
  assert (d = pc).
  unfold update in * ; rewrite peq_true in *.
  (destruct (peq d pc); auto) ;
  (exploit (unique_def_spec_def (x, idx) d pc) ; eauto).
  intuition.  inv H4. auto. 
Qed.

Lemma gamma_def_path : forall p pc x i d, 
  def f (x,i) d ->
  G pc x = i ->
  DomCompute.path f p (PState pc) -> 
  Regset.In x (Lin f_rtl pc (Lout live)) -> In d (pc::p).
Proof.
  intros.
  exploit gamma_path_def ; eauto.
  simpl. intros. exploit H3 ; eauto.
  intros [HH1 | [HH21 HH22]].
  right ; auto. 
  inv HH21. left ; auto.
Qed.

Lemma gamma_path_sdef : forall p pc,
  DomCompute.path f p (PState pc) ->
  forall x d i, 
    def f (x,i) d ->
    G pc x = i ->
    Regset.In x (Lin f_rtl pc (Lout live)) -> 
    (In d p
      \/ (d = pc /\ 
        ~ ( use_code f (x,i) pc /\ 
          assigned_code_spec (fn_code f) pc (x,i)))).
Proof.
  intros. exploit gamma_path_def ; eauto.
Qed.

Lemma phiu_same_length : forall r args gammas, 
  phiu r args gammas ->
  length args = length gammas.
Proof.
  induction 1 ; intros ; eauto.
  simpl. eauto.
Qed.

Lemma wt_phiu_args_dst : forall pc phib args dst k xi x i,
  (fn_phicode f) ! pc = Some phib ->
  In (Iphi args dst) phib ->
  nth_error args k = Some xi ->
  xi = (x, i) ->
  wt_phiu (make_predecessors (fn_code f) successors_instr) !!! pc phib G ->
  exists idx, dst = (x, idx).
Proof.
  intros.
  inv H3.
  destruct dst. 
  exploit USES ; eauto. intros Hphiu. 
  set (gammas := (map G (make_predecessors (fn_code f) successors_instr) !!! pc)) in *.
  exploit phiu_same_length ; eauto. intros Hlength.
  exploit @nth_error_some_same_length ; eauto. intros [e Hnthgammas].
  exploit phiu_nth ; eauto. intros [i0 [Hxi' Hi0]].
  inv Hxi'; eauto.
Qed. 


Lemma wt_pdom : forall x u d
  (USE: use f x u)
  (DEF: def f x d),
  dom f d u.
Proof. 
  intros.
  destruct (peq u d).  inv e ; econstructor ; eauto.

  eelim (classic (dom f d u)) ; eauto. intro Hcont.
  assert (exists p, path f (PState (entry f)) p (PState u) /\ ~ In d p).

  eapply (@not_dom_path_wo node peq) ; eauto.  eapply use_reached ; eauto. 
  destruct H as [p [Hp Hnotin]].
  
  exploit use_gamma ; eauto. intro HGamma.
    
  destruct x as [x i].

  exploit DomCompute.SSA_path_this_path ; eauto. intros Hpath.
  exploit gamma_def_path ; eauto.
  
  inv USE. 
  (* use in code *)
  eapply wf_live_use ; eauto. 
  eapply use_code_spec in H ; eauto.
  (* use in phicode *)
  inv H. 
  assert (Hedge : is_edge f u pc) by (eapply pred_is_edge ; eauto).
  inv fn_wt. exploit WTE ; eauto. intros Hwte. inv Hwte ; allinv.
  unfold gi in  * ; simpl in * ; inv HGamma. 
  exploit (wt_phiu_args_dst pc block args dst k (x, G u x) x (G u x)); eauto. intros [idx Hidx].  
  
  assert (Hlpc : Regset.In x (Lin f_rtl pc (Lout live))).
  inv WTPHID. exploit (LIVE (x, idx)) ; eauto. econstructor ; eauto.
    
  exploit (wf_live_incl f_rtl (Lout live) fn_wfl u pc) ; eauto.
  eapply cfg_rtl_cfg ; eauto. inv Hedge ; eauto. econstructor ; eauto.
  intros [HH1 | HH2]; auto.
  
  exploit fn_phicode_code ; eauto. intros [ins0 Hins0].
  exploit fn_phicode_inv1 ; eauto. intros Hjp. 
  exploit (fn_code_inv2 pc u) ; eauto. 
  inv Hedge. unfold successors_list, successors. rewrite PTree.gmap1.
  unfold option_map. rewrite H0 ; auto. intros Hcode.
  inv fn_erased. 
  inv HH2; rewrite HCODE in H0;
  (
  (unfold erase_code in H0; rewrite PTree.gmap in H0);
  (unfold option_map in H0; rewrite Hcode in H0);
  (inv H0)).

  intros Hcont'.  inv Hcont'.
  econstructor ; eauto. 
  elim Hnotin. eapply in_rev ; eauto. 
Qed.  

Lemma wt_def_use_code_false : forall x pc
  (USE: use_code f x pc)
  (DEF: assigned_code_spec (fn_code f) pc x),
  False.
Proof.
  intros.
  case_eq x ; intros r idx Hrmap.
  
  exploit use_code_gamma ; eauto; intros Hgamma.
  exploit use_code_spec ; eauto. intros Hrtl.  
  exploit wf_live_use ; eauto. intros Hlive.
  assert (Htmp : use f x pc). econstructor ; eauto. exploit wt_use_isdef ; eauto. intros [d Hdef].
  unfold get_index, erase_reg in *. rewrite Hrmap in * ; simpl in *.
  
  exploit use_reached ; eauto. intros Rpc.
  exploit (@reached_path node) ; eauto. intros [p Hp].  
  exploit (path_first p (entry f)) ; eauto. 
  intro Hcont. inv Hcont. inv fn_wt. destruct fn_entry. inv USE; allinv.
  intros [pc' [p' [p'' [Hp' [Hnotin [Hdiff [Hpc' Happ]]]]]]]. 
  
  assert (DomCompute.path f (pc'::(rev p')) (PState pc)).  
  { inv Hpc'.
    inv STEP. 
    econstructor ; eauto. eapply DomCompute.SSA_path_this_path ; eauto.
  }
  exploit gamma_path_def ; eauto. simpl.
  intros. exploit (H0 r pc idx) ; eauto.
    
  intros [[HH11 | HH12] | [_ HH2]]. 
  
  congruence.

  elim Hnotin. apply in_rev ; eauto.
  
  elim HH2. 
  split; auto.
Qed.

  
End WT_FUNCTION.
