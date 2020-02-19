
(** This is the liveness analysis over RTL that is used by the SSA
   generation algorithm.  This is based on the liveness analysis
   already provided by CompCert.  We adapt it so that it resemble more
   the traditional liveness analysis, and that it fulfills the
   requirements we demand on liveness information. *)

Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Lattice.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Globalenvs.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import Kildall.
Require Import Locations.
Require Import Conventions.
Require Import RTLutils.
Require Import Path.


(** * Liveness analysis over RTL *)

Notation reg_live := Regset.add.
Notation reg_dead := Regset.remove.

Definition reg_option_live (or: option reg) (lv: Regset.t) :=
  match or with None => lv | Some r => reg_live r lv end.

Definition reg_sum_live (ros: reg + ident) (lv: Regset.t) :=
  match ros with inl r => reg_live r lv | inr s => lv end.

Fixpoint reg_list_live
             (rl: list reg) (lv: Regset.t) {struct rl} : Regset.t :=
  match rl with
  | nil => lv
  | r1 :: rs => reg_list_live rs (reg_live r1 lv)
  end.

Fixpoint reg_list_dead
             (rl: list reg) (lv: Regset.t) {struct rl} : Regset.t :=
  match rl with
  | nil => lv
  | r1 :: rs => reg_list_dead rs (reg_dead r1 lv)
  end.

Definition transfer
            (f: RTL.function) (pc: node) (after: Regset.t) : Regset.t :=
  match f.(fn_code)!pc with
  | None =>
      Regset.empty
  | Some i =>
      match i with
      | Inop s =>
          after
      | Iop op args res s =>  
          reg_list_live args (reg_dead res after)        
      | Iload chunk addr args dst s => 
          reg_list_live args (reg_dead dst after)
      | Istore chunk addr args src s =>
          reg_list_live args (reg_live src after)
      | Icall sig ros args res s =>
          reg_list_live args
           (reg_sum_live ros (reg_dead res after))
      | Itailcall sig ros args =>
          reg_list_live args (reg_sum_live ros Regset.empty)
      | Ibuiltin ef args res s =>
          reg_list_live args (reg_dead res after)
      | Icond cond args ifso ifnot =>
          reg_list_live args after
      | Ijumptable arg tbl =>
          reg_live arg after
      | Ireturn optarg =>
          reg_option_live optarg Regset.empty
      end
  end.

(** The liveness analysis is then obtained by instantiating the
  general framework for backward dataflow analysis provided by
  module [Kildall].  *)

Module RegsetLat := LFSet(Regset).
Module DS := Backward_Dataflow_Solver(RegsetLat)(NodeSetBackward).


Definition analyze (f: function): option (PMap.t Regset.t) :=
  DS.fixpoint f.(fn_code) successors_instr (transfer f) nil.

(** * Well-formedness condition for a liveness analysis *)

Section WF_LIVE.

  Variable f: RTL.function.
  
  Definition Lin := (fun pc live_out => (transfer f pc (live_out pc))).
  
  Definition Lout {A: Type} := (fun (live: PMap.t A) pc => live # pc).

  Record wf_live  (live_out: positive -> Regset.t):= MK_WF_LIVE {
    wf_live_incl : forall pc pc' x, 
      rtl_cfg f pc pc' ->
      Regset.In x (Lin pc' live_out) ->
      (Regset.In x (Lin pc live_out) \/ RTLutils.assigned_code_spec (RTL.fn_code f) pc x) ;
    
    wf_live_use : forall pc x, use_rtl_code f x pc -> (Regset.In x (Lin pc live_out)) 
  }.

  (** ** Auxiliary lemmas about [analyze] *)
  Lemma reg_list_live_incl : forall x l s, 
    Regset.In x s ->
    Regset.In x (reg_list_live l s).
  Proof.
    induction l ; intros ; simpl ; auto.
    eapply IHl ; eauto.
    eapply Regset.add_2 ; eauto.
  Qed.
  
  Lemma reg_list_live_incl_2 : forall x l s, 
    In x l ->
    Regset.In x (reg_list_live l s).
  Proof.
    induction l ; intros ; inv H.
    simpl. 
    eapply reg_list_live_incl ; eauto.
    eapply Regset.add_1 ; eauto.
    eapply IHl ; eauto.
  Qed.

  Lemma reg_list_live_cases : forall x l s, 
    Regset.In x (reg_list_live l s) ->
    (Regset.In x s) \/ In x l.
  Proof.
    induction l ; intros ; simpl ; auto.
    exploit IHl ; eauto.
    intros [Hcase1 | Hcase2].
    destruct (peq a x). 
    inv e; auto. 
    left. 
    eapply Regset.add_3 ; eauto.
    auto.
  Qed.
    
  Hint Constructors RTLutils.assigned_code_spec.

  Lemma live_incl : forall live, analyze f = Some live ->
    forall pc pc' x, 
      rtl_cfg f pc pc' ->
      Regset.In x (Lin pc' (Lout live)) ->
      Regset.In x (Lin pc (Lout live)) \/ RTLutils.assigned_code_spec (RTL.fn_code f) pc x.
  Proof.
    intros.
    generalize H ; intros AN.
    unfold analyze in H.
    assert (cfg (fn_code f) pc pc'). inv H0 ; eauto.  
    inv H0.
    (exploit (DS.fixpoint_solution _ (fn_code f)
                                   RTL.successors_instr 
                                   (transfer f) 
                                   nil live pc ins pc' H HCFG_ins HCFG_in x)); eauto.
    intros.
    (unfold Lout, Lin in * ; unfold transfer).
    case_eq (RTL.fn_code f) ! pc ; intros.
    case_eq i ; intros ; subst; auto.
    
    - destruct (peq r x). 
    inv e. right ; eauto.
    left.
    (eapply reg_list_live_incl ; eauto).
    (eapply Regset.remove_2 ; eauto).
    - destruct (peq r x). 
    inv e. right ; eauto.
    left.
    (eapply reg_list_live_incl ; eauto).
    (eapply Regset.remove_2 ; eauto).
    - 
    left.
    (eapply reg_list_live_incl ; eauto).
    (eapply Regset.add_2 ; eauto).
    - 
    destruct (peq r x). 
    inv e. right ; eauto.
    left.
    (eapply reg_list_live_incl ; eauto).
    destruct s0; simpl.
    (eapply Regset.add_2 ; eauto).
    (eapply Regset.remove_2 ; eauto).
    (eapply Regset.remove_2 ; eauto).
    - 
    rewrite H3 in * ; inv HCFG_ins. 
    simpl in HCFG_in . intuition.
    - 
    destruct (peq r x). 
    inv e0. right ; eauto.
    left.
    (eapply reg_list_live_incl ; eauto).
    (eapply Regset.remove_2 ; eauto).
    - 
    left. (eapply reg_list_live_incl ; eauto).
    - 
    left. (eapply Regset.add_2 ; eauto).
    - 
    simpl in HCFG_in. 
    rewrite H3 in * ; inv HCFG_ins.   
    inv HCFG_in.   
    - 
    rewrite H3 in * ; inv HCFG_ins.   
  Qed.  

Lemma live_use : forall live, analyze f = Some live ->
  forall pc x,
    use_rtl_code f x pc ->
    Regset.In x (Lin pc (Lout live)).
Proof.
  intros.
  generalize H ; intros AN.
  unfold analyze in H.
  inv H0; (unfold Lin, Lout in * ; unfold transfer; rewrite H1) ; 
  try ( solve [
    eapply reg_list_live_incl_2 ; eauto
    |
      ( inv H2); 
      [(eapply reg_list_live_incl ; eauto) ;
        (eapply Regset.add_1 ; eauto)
        | eapply reg_list_live_incl_2 ; eauto]
    |
      (case_eq (Regset.mem dst live # pc) ; intros);
      [   eapply reg_list_live_incl_2 ; eauto
        | (right; exists dst);
          (split; eauto);
          (intro Hcont) ; (exploit Regset.mem_1 ; eauto ; intuition ; congruence)]
    |   simpl; eapply Regset.add_1 ; eauto]
  ).     
Qed.

  (** ** [analyze] is well-formed with regards to [wf_live] *)
Lemma live_wf_live : 
  forall live, analyze f = Some live ->
    wf_live (Lout live).
Proof.
  intros.
  constructor.
  apply live_incl; auto.
  apply live_use ; auto.
Qed.

End WF_LIVE.

Hint Constructors wf_live.

