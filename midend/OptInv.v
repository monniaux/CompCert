Require Import Classical.
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Events.
Require Import Registers.
Require Import Floats.
Require Import Utils.
Require Import Dom.
Require Import SSA. 
Require Import SSAtool. 
Require Import SSAutils. 
Require Import SSAtoolinv. 
Require Import Utilsvalidproof.
Require Import DomCompute.
Require Import Axioms.
Require Import KildallComp.
Require Import OrderedType.
Require Import Ordered.
Require Import FSets.
Require FSetAVL.
Require Import Dsd.
Require Import Opt.
Require Import DLib.

(** This file defines a generic program optimization.  In our SSA
 middle-end, we instantiate this to SCCP and GVN-CSE, but in general,
 it could also be instantiated to any intra-procedural, scalar
 optimization. *)

Ltac ssa_def := 
  let eq_pc pc1 pc2 := 
      assert (pc1 = pc2) by (eapply ssa_def_unique; eauto); subst
  in
  unfold node in *;
    match goal with 
      | r : reg |- _ =>
        match goal with 
            id: def _ r ?x,
            id': def _ r ?y
            |- _ => eq_pc x y ; try clear id'
        end
      | x : positive, 
        y : positive |- _ =>
        match goal with 
              id: def _ ?r x,
              id': assigned_phi_spec_with_args _ y ?r _ |- _ => 
              assert (x = y) 
                by (repeat invh assigned_phi_spec_with_args;
                    eapply ssa_def_unique; eauto); subst
        end
      | pc1: positive,
        pc2: positive |- _ =>
            match goal with 
                id : def _ ?r pc1,
                id': assigned_phi_spec _ pc2 ?r |- _ =>
                eq_pc pc1 pc2
            end
      |  pc1: positive,
         pc2: positive |- _ =>
            match goal with 
                id: assigned_phi_spec _ pc1 ?r,
                id': assigned_phi_spec _ pc2 ?r |- _ =>
                eq_pc pc1 pc2
            end
      | id1: assigned_phi_spec_with_args _ ?pc1 ?r _,
        id2: In (Iphi _ ?r) ?phib,
        id3: _ ! ?pc2 = Some ?phib |- _  =>
        assert (pc1 = pc2) 
          by (inv id1;
              eapply ssa_def_unique; eauto); subst
      | id : _ ! ?pc1 = Some (Iop _ _ ?r _),
        id' : _ ! ?pc2 = Some (Iop _ _ ?r _)
        |- _ => 
        match pc2 with
          | pc1 => fail 1
          | _ => idtac
        end;
          eq_pc pc1 pc2
      | id : _ ! ?pc1 = Some (Iop _ _ ?r _),
        id': def _ ?r ?pc2 |- _ =>
        match pc2 with
          | pc1 => fail 1
          | _ => idtac
        end;
          eq_pc pc1 pc2
      end.


(** * Record for a dominance-based static analysis  *)
Record DsdAnalysis := {
 (** Flow insensitive analysis *)
   approx: Type
 ; result := reg -> approx

 (** [G ge sp rs a v] : in context ge sp rs, a is a correct approximation of the value v *)
 ; G : genv -> val -> regset -> approx -> val -> Prop

 (** [is_at_Top R r] : characterization of registers put at Top *) 
 ; is_at_Top : result -> reg -> Prop

 (** The analysis itself *)
 ; A : function -> (result * m_exec)

 ; exec : function -> node -> Prop

 (** The following are hypotheses we require on the analysis. To be proved when instantiating the framework *)
 ; exec_fn_entry : forall f, exec f (fn_entrypoint f)

 ; is_at_Top_eq_is_at_Top : 
     forall f dst x, 
       is_at_Top (fst (A f)) dst -> 
       fst (A f) x = fst (A f) dst -> 
       is_at_Top (fst (A f)) x

 ; params_Top : 
     forall (f:function) r, 
       ext_params f r -> 
       is_at_Top (fst (A f)) r

 (** A register put to top approximates any concrete value (_any_ context) *)
 ; G_top : 
     forall f r ge sp rs, 
       is_at_Top (fst (A f)) r -> 
       G ge sp rs (fst (A f) r) (rs#2 r)

}.

Section Opt_ANALYSIS.

 Variable AA: DsdAnalysis.

 Inductive G_list ge sp rs : list (approx AA) -> list val -> Prop :=
    vlma_nil : G_list ge sp rs nil nil
  | vlma_cons : forall a al v vl,
                G AA ge sp rs a v ->
                G_list ge sp rs al vl ->
                G_list ge sp rs (a :: al) (v :: vl).

 Definition A_r f := fst (A AA f).
 Definition A_e f := snd (A AA f).
                     
 Definition gamma (f:function) ge sp (pc:node) (rs:regset) : Prop :=
    (forall x, dsd f x pc -> 
               exec AA f pc -> 
               G AA ge sp rs (A_r f x) (rs#2 x)).

  Lemma gamma_entry (f:function) : 
    wf_ssa_function f -> 
    forall ge sp rs, gamma f ge sp (fn_entrypoint f) rs.
  Proof.
    intros WF ge sp rs r Hr _.
    eelim ssa_dsd_entry; eauto. 
    (* intros Hparams.
    exploit (params_Top AA); eauto. intros Htop. 
    eapply G_top ; auto.  *)
  Qed.

  Lemma gamma_sdom_gamma (f: function) : forall pc pc' ge sp rs,
    wf_ssa_function f -> 
    gamma f ge sp pc rs ->
    exec AA f pc ->
    sdom f pc' pc ->
    gamma f ge sp pc' rs.
  Proof.
    intros pc pc' ge sp rs WF G EXE SDOM r Hr He. 
    inv Hr. 
    - eapply G; eauto.
      econstructor; eauto.
      eapply (sdom_trans peq); eauto.
      intro Hcont.
      ssa_def.
      eapply (elim_sdom_sdom peq); eauto.
    - eapply G; eauto.
      econstructor 1; eauto.
      intro Hcont.       
      ssa_def. 
      eelim SDOM; eauto. 
  Qed.

  Lemma used_match_approx: forall (f:function) ge sp pc rs r,
    wf_ssa_function f -> 
    gamma f ge sp pc rs ->
    use_code f r pc -> 
    exec AA f pc ->
    G AA ge sp rs (A_r f r) (rs#2 r).
  Proof.
    intros f ge sp pc rs r WF GAMMA USE EXE.
    assert (H3: exists pc', def f r pc') by (eapply ssa_use_exists_def; go).
    destruct H3 as [x H0].
    eapply GAMMA; auto.
    destruct (classic (assigned_phi_spec (fn_phicode f) pc r)) as [H4 | H4].
      + go. 
      + econstructor 1; eauto.
        assert (H5: dom f x pc) by (eapply fn_strict; go). 
        apply (dom_eq_sdom peq) in H5. inv H5; auto.
        assert (assigned_code_spec (fn_code f) pc r)
          by (inv H0; try (destruct (fn_entry f); auto; invh use_code; congruence)).
        eelim ssa_def_use_code_false; eauto. 
  Qed.

  Lemma all_used_approx: forall ge f pc sp rs args,
     exec AA f pc ->                           
     wf_ssa_function f ->
     (forall r, In r args -> use_code f r pc) ->
     gamma f ge sp pc rs -> 
     G_list ge sp rs (map (A_r f) args) (rs##2 args). 
  Proof.
  induction args; intros.
  - go. 
  - simpl. econstructor; eauto. 
    eapply H2; eauto.
    assert (use_code f a pc) by go.
    exploit ssa_use_exists_def; go. intros [dr Hr].
    exploit fn_strict; go. intros.
    exploit (dom_eq_sdom peq); eauto. intros [HCase | HCase]. 
    + subst. inv Hr; try go.
      * exploit fn_entry; eauto. intros [s Hnop].
        inv H3; try congruence.  
      * eelim fn_use_def_code; eauto.
    + eapply def_sdom_dsd; eauto.
  Qed.

  Lemma gamma_v_args : forall ge f sp rs res op pc pc' args,
     exec AA f pc ->
     wf_ssa_function f ->
     gamma f ge sp pc rs -> 
     (fn_code f) ! pc = Some (Iop op args res pc') ->
     G_list ge sp rs (map (A_r f) args) (rs##2 args).
  Proof.
    intros. 
    eapply all_used_approx; eauto.
    intros; go.
  Qed.

  (** A couple of extra hypotheses.*)
  Variable A_intra_locals : forall f:function,
         forall pc res,
         (forall op args res pc', (fn_code f) ! pc <> Some (Iop op args res pc')) ->
         exec AA f pc ->
         assigned_code_spec (fn_code f) pc res -> is_at_Top AA (A_r f) res.

  Variable G_upd_diff : forall (f:function) (Hwf:wf_ssa_function f) ge sp rs dst x v,
                    x <> dst ->
                    A_r f x <> A_r f dst ->
                    G AA ge sp rs (A_r f x) rs !!2 x ->
                    G AA ge sp (rs #2 dst <- v) (A_r f x) rs !!2 x.

  (** Local soundness of analysis for variable assignment *)
  Variable Iop_correct : forall (f:function) pc sf op args res pc' v rs ge sp m x,
                      forall (WFF: wf_ssa_function f)
                             (SINV: s_inv ge (State sf f sp pc rs m)),
                        (fn_code f) ! pc = Some (Iop op args res pc') ->
                        eval_operation ge sp op (rs ##2 args) m = Some v ->
                        gamma f ge sp pc rs ->
                        exec AA f pc ->
                        dsd f x pc' ->
                        G AA ge sp (rs #2 res <- v) (A_r f x) (rs #2 res <- v) !!2 x.

  (** Local soundness of analysis for phi-blocks *)
  Variable gamma_step_phi: forall (f:function) ge sp pc pc' phib k rs,
   wf_ssa_function f ->
   reached f pc ->
   exec AA f pc ->
   
   (fn_code f) ! pc = Some (Inop pc') ->
   (fn_phicode f) ! pc' = Some phib ->
   index_pred (Kildall.make_predecessors (fn_code f) successors_instr) pc pc' = Some k ->
   
   gamma f ge sp pc rs ->
   gamma f ge sp pc' (phi_store k phib rs).


(** * Soundness invariant. Subject-reduction proof *)
Section subject_reduction.

  Variable prog: program.
  Let ge := Genv.globalenv prog.

  Inductive sfg_inv : list stackframe -> Prop :=
  | sf_inv_nil: sfg_inv nil
  | sf_inv_cons: 
    forall res (f:function) sp pc rs s
      (STACK: sfg_inv s)
      (HG:forall v, gamma f ge sp pc (rs#2 res <- v))
      (EXE: exec AA f pc),
      sfg_inv ((Stackframe res f sp pc rs) :: s).
  Hint Constructors sfg_inv.
  
  Inductive sg_inv (ge: genv): state -> Prop :=
  | si_State:
      forall s sp pc rs m f
        (SINV:s_inv ge (State s f sp pc rs m))
        (HG:gamma f ge sp pc rs)
        (EXE: exec AA f pc)
        (STACK: sfg_inv s),
        sg_inv ge (State s f sp pc rs m)
  | si_Call:
      forall s f args m
        (SINV:s_inv ge (Callstate s f args m))
        (STACK: sfg_inv s),
        sg_inv ge (Callstate s f args m)
  | si_Return:
      forall s v m 
        (SINV:s_inv ge (Returnstate s v m))
        (STACK: sfg_inv s),
        sg_inv ge (Returnstate s v m).
  Hint Constructors sg_inv.

  Lemma s_inv_initial : forall s, initial_state prog s -> sg_inv ge s.
  Proof.
    intros. inv H. go. 
  Qed.

  Variable exec_step : forall (f:function) ge t sf sp pc rs m s',
                   sfg_inv sf ->
                   gamma f ge sp pc rs ->
                   exec AA f pc ->
                   step ge (State sf f sp pc rs m) t s' ->
                   match s' with 
                     | (State _ f _ pc' _ _) 
                     | (Callstate (Stackframe _ f _ pc' _ :: _) _ _ _) => exec AA f pc'
                     | _ => True
                   end.

  Lemma subj_red : forall s s' t,
    sg_inv ge s ->
    step ge s t s' ->
    step ge s t s' ->
    sg_inv ge s'.  
  Proof.
  intros s s' t HINV STEP STEP'.
  inv HINV.
  
  - (* from State *)
    assert (WF:=wf f).
    invh step; (econstructor; eauto);
    try solve [eapply subj_red; eauto];
    try solve [eapply exec_step in STEP ; eauto].

    + (* Inop njp *)
      unfold gamma in *; intros x Hx He.
      assert (~assigned_code_spec (fn_code f) pc x)
        by (intros contra; inv contra; congruence).
      exploit (dsd_pred_not_join_point f (wf f) pc pc' x); eauto. go.
      intros [Hcase1 | [ Hcase2 | Hcase3]]; invh and; try congruence.
      * exploit G_top; eauto. 
        eapply params_Top; eauto. 
      * eapply HG; eauto.  
      * unfold fn_code in *; intuition.
    + (* Iop *)
      unfold gamma in *; intros x Hyp1 Hyp2.
      eapply Iop_correct; eauto.

    + (* Iload *)
      unfold gamma in *; intros x Hyp1 Hyp2.
      { destruct (p2eq x dst).
        - subst. 
          exploit (A_intra_locals f pc); go. 
          eapply G_top; eauto; go.
        - exploit (A_intra_locals f pc); go. 
          intros. 
          unfold fn_code in *.
          exploit (HG x); eauto.
          * destruct dsd_pred_njp with f pc pc' x as 
                [[Dx Dx']|[[Dx [Dx' Dx'']]|[Dx Dx']]]; simplify_dsd; eauto.            
            intro; subst; exploit fn_entry; eauto; intros (succ' & Hscucc);
            congruence. go.
            eelim ssa_not_Inop_not_phi; eauto; go.
          * intros.
            { destruct (classic ((A_r f x) = (A_r f dst))).
              - assert (is_at_Top AA (A_r f) x) by (eapply is_at_Top_eq_is_at_Top; eauto). 
                eapply G_top; eauto. 
              - rewrite P2Map.gso; auto.  
            }             
      }

    + (* Istore *) 
      unfold gamma, fn_code in *; intros x Hyp1 Hyp2.     
      destruct dsd_pred_njp with f pc pc' x as
          [[Dx Dx']|[[Dx [Dx' Dx'']]|[Dx Dx']]]; simplify_dsd; eauto.
      * intro; subst; exploit fn_entry; eauto; intros (succ' & Hscucc); congruence. 
      * go. 
      * eelim ssa_not_Inop_not_phi; simpl; go; simpl; go. 
      
    + (* Icall *)
      econstructor; eauto.
      unfold fn_code in *.
      intros v x Hyp1 Hyp2.
        { destruct (p2eq x res).
          - subst. exploit (A_intra_locals f pc); go. 
            eapply G_top; eauto. 
          - exploit (HG x); eauto. 
            * destruct dsd_pred_njp with f pc pc' x as 
                [[Dx Dx']|[[Dx [Dx' Dx'']]|[Dx Dx']]]; simplify_dsd; eauto.
              intro; subst; exploit fn_entry; eauto; intros (succ' & Hscucc);
              congruence. go.
              eelim ssa_not_Inop_not_phi; eauto; go.
            * exploit (A_intra_locals f pc); go. 
              intros.
              { destruct (classic ((A_r f x) = (A_r f res))).
                - assert (is_at_Top AA (A_r f) x) by (eapply is_at_Top_eq_is_at_Top; eauto). 
                  eapply G_top; eauto. 
                - rewrite P2Map.gso; auto.  
              }
        } 
       eapply exec_step in STEP; eauto.

    + (* Itailcall *)
      unfold gamma, fn_code in *; intros x Hyp1 Hyp2.
      { destruct (p2eq x res).
        - subst. exploit (A_intra_locals f pc); go. 
          eapply G_top; eauto. 
        - exploit (HG x); eauto. 
          + destruct dsd_pred_njp with f pc pc' x as 
              [[Dx Dx']|[[Dx [Dx' Dx'']]|[Dx Dx']]]; simplify_dsd; eauto.
            intro; subst; exploit fn_entry; eauto; intros (succ' & Hscucc); congruence.
            go.
            eelim ssa_not_Inop_not_phi; eauto; go. 
          + exploit (A_intra_locals f pc); go. 
              intros.
              { destruct (classic ((A_r f x) = (A_r f res))).
                - assert (is_at_Top AA (A_r f) x) 
                    by (eapply is_at_Top_eq_is_at_Top; eauto). 
                  eapply G_top; eauto. 
                - rewrite P2Map.gso; auto.  
              }
      }

    + (* Icond true *)
      unfold gamma, fn_code in *; intros x Hyp1 Hyp2.
      destruct dsd_pred_njp with f pc ifso x as
          [[Dx Dx']|[[Dx [Dx' Dx'']]|[Dx Dx']]]; simplify_dsd; eauto.
      * intro; subst; exploit fn_entry; eauto; intros (succ' & Hscucc); congruence.
      * go. 
      * eelim ssa_not_Inop_not_phi; eauto. simpl; auto. congruence.
        
    + (* Icond false *)
      unfold gamma, fn_code in *; intros x Hyp1 Hyp2.
      destruct dsd_pred_njp with f pc ifnot x as
          [[Dx Dx']|[[Dx [Dx' Dx'']]|[Dx Dx']]]; simplify_dsd; eauto.
      * intro; subst; exploit fn_entry; eauto; intros (succ' & Hscucc); congruence.
      * go. 
      * eelim ssa_not_Inop_not_phi; eauto. simpl; auto. congruence.

    + (* Ijumptable *)
      unfold gamma, fn_code in *; intros x Hyp1.
      destruct dsd_pred_njp with f pc pc' x as
            [[Dx Dx']|[[Dx [Dx' Dx'']]|[Dx Dx']]]; simplify_dsd; eauto using list_nth_z_in.
      * intro; subst; exploit fn_entry; eauto; intros (succ' & Hscucc); congruence.
      * econstructor; eauto. eauto using list_nth_z_in. 
      * eelim ssa_not_Inop_not_phi; eauto. simpl; eauto using list_nth_z_in. congruence.

  - (* from CallState *)
    invh step; econstructor; eauto ; try solve [eapply subj_red; eauto ].

    + (* Internal PO1 *)
      eapply gamma_entry; eauto.
      inv SINV. apply f0.
    + eapply exec_fn_entry; eauto.

  - (* from ReturnState *)
    invh step. 
    invh sfg_inv; eauto.
    econstructor; eauto. 
    eapply subj_red; eauto. 
Qed.

Lemma ssa_inv1_aux : forall s s' t, 
  sg_inv ge s ->
  star step ge s t s' ->
  sg_inv ge s'.
Proof.
  induction 2 ; intros. 
  auto.
  eapply IHstar ; eauto.
  eapply subj_red ; eauto.
Qed.

Theorem ssa_inv1 : forall  s s' t, 
  initial_state prog s -> 
  star step ge s t s' -> 
  sg_inv ge s'.
Proof.
  intros.
  eapply ssa_inv1_aux ; eauto.  
  eapply s_inv_initial ; eauto.
Qed.

(** * Final correctness lemma. To be used in correctness proof of optimization *)
Lemma subj_red_gamma : forall (f f':function) t m m' rs rs' sp sp' pc pc' s s', 
  gamma f ge sp pc rs ->
  exec AA f pc ->
  sfg_inv s ->
  s_inv ge (State s f sp pc rs m) ->
  step ge (State s f sp pc rs m) t (State s' f' sp' pc' rs' m') ->
  gamma f' ge sp' pc' rs'.  
Proof.
  intros.
  exploit subj_red; eauto.
  intros. invh sg_inv; eauto.
Qed.

End subject_reduction. 

End Opt_ANALYSIS.

