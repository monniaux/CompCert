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
Require Opt.
Require Import Dsd.
Require ConstpropOp.

(** Instantiation of the generic analysis to Sparse Conditional Constant Propagation *)


(** * The constant analysis *)

(** ** The constant lattice *)
Module CO := ConstpropOp.

Module Approx <: SEMILATTICE_WITH_TOP.
  Definition t := CO.approx.
  Definition eq (x y : t) := x = y.
  Definition eq_refl: forall x, eq x x := (@refl_equal t).
  Definition eq_sym: forall x y, eq x y -> eq y x := (@sym_equal t).
  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := (@trans_equal t).
  Lemma eq_dec: forall (x y : t), {x = y} + {x <> y}.
  Proof.
    decide equality;
    eauto using Int.eq_dec,
                Float.eq_dec,
                Int64.eq_dec,
                AST.ident_eq.
  Qed.

  Definition beq (x y: t) := if eq_dec x y then true else false.

  Definition beq_top (x: t) :=
    match x with
      | CO.Unknown => true
      | _ => false
    end.

  Lemma beq_correct: forall x y, beq x y = true -> x = y.
  Proof.
    intros x y H. unfold beq in H. destruct (eq_dec x y); congruence.
  Qed.

  Definition ge (x y : t) : Prop :=
    x = CO.Unknown \/ y = CO.Novalue \/ x = y.
  Lemma ge_refl: forall x y, eq x y -> ge x y.
    Proof. intros. unfold ge. right. right. unfold eq in H. subst. reflexivity. Qed.
  Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
    Proof. intros. unfold ge in *. intuition congruence. Qed.
  Lemma ge_compat: forall x x' y y', eq x x' -> eq y y' -> ge x y -> ge x' y'.
    Proof. intros. unfold ge, eq in *. congruence. Qed.
  Definition top := CO.Unknown.
  Definition bot := CO.Novalue.

  Lemma ge_top: forall x, ge top x.
    Proof. unfold ge, top. firstorder. Qed.
  Lemma ge_bot: forall x, ge x bot.
    Proof. unfold ge, top; firstorder. Qed.

  Definition lub (x y : t) : t :=
    if eq_dec x y then x else
      match x, y with
        | CO.Novalue, _ => y
        | _, CO.Novalue => x
        | _, _ => CO.Unknown
      end.

  Definition ge_lub_left: forall x y, ge (lub x y) x.
  Proof.
    intros. unfold lub.
    case (eq_dec x y); intros.
    apply ge_refl; apply eq_refl.
    destruct x; destruct y; unfold ge; tauto.
  Qed.

  Definition ge_lub_right: forall x y, ge (lub x y) y.
  Proof.
    intros. unfold lub.
    case (eq_dec x y); intros.
    subst; apply ge_refl; apply eq_refl.
    destruct x; destruct y; unfold ge; tauto.
  Qed.
End Approx.


(** * Def-Use Chains *)
Definition ssainstruction := (node * (instruction + phiinstruction))%type.
Definition du_chain := P2Map.t (list ssainstruction).

(** ** Construction *)
Definition regs_used_by (i : instruction) : list reg :=
 match i with
    | Iop _ l _ _ => l
    | Iload _ _ l _ _ => l
    | Istore _ _ l _ _ => l
    | Icall _ ros l _ _
    | Itailcall _ ros l =>
      match ros with
        | inl r => r :: l
        | inr _ => l
      end
    | Ibuiltin _ l _ _ => l
    | Icond _ l _ _ => l
    | Ijumptable r _ => r :: nil
    | Ireturn (Some r) => r :: nil
    | _ => nil
  end.

Definition handle_reg_list (duc: du_chain) (ssai: ssainstruction) (rs: list reg) :=
  List.fold_left (fun u r => P2Map.set r (ssai :: u #2 r) u) rs duc.

Definition def_use_1 duc c :=
  PTree.fold (fun u pc i => handle_reg_list u (pc, inl _ i) (regs_used_by i)) c duc.

Definition handle_phi_block (duc : du_chain) pc (pb : phiblock) :=
  List.fold_left
    (fun u pi => match pi with
                     Iphi args _ => handle_reg_list u (pc, inr _ pi) args end)
    pb duc.

Definition def_use_2 duc phic :=
  PTree.fold (fun u pc pb => handle_phi_block u pc pb) phic duc.

Definition make_du_chain f : du_chain :=
  let u := def_use_1 (P2Map.init nil) (fn_code f) in
  def_use_2 u (fn_phicode f).

(** ** Correctness of construction *)
Definition ssai_in_function ssai f :=
  match ssai with
    | (pc, inl i)  => (fn_code f) ! pc = Some i
    | (pc, inr pi) => exists pb, (fn_phicode f) ! pc = Some pb /\ In pi pb
  end.

Definition maps_into_function f m := forall r ssai,
  In ssai (m #2 r) -> ssai_in_function ssai f.

Hint Unfold maps_into_function ssai_in_function.

Remark duc_maps_into_function_handle_reg_list: forall f duc ssai rs,
  maps_into_function f duc ->
  ssai_in_function ssai f ->
  maps_into_function f (handle_reg_list duc ssai rs).
Proof.
  intros. generalize dependent duc.
  induction rs.
  tauto.
  intros.
  simpl in *. eapply IHrs; eauto.
  unfold maps_into_function in *. intros.
  destruct (p2eq a r).
  + subst.
    rewrite P2Map.gss in *.
    apply in_inv in H1.
    invh or; eauto.
  + rewrite P2Map.gso in *; auto. eauto.
Qed.

Remark duc_maps_into_function_code: forall f duc,
  maps_into_function f duc ->
  maps_into_function f (def_use_1 duc (fn_code f)).
Proof.
  intros.
  unfold def_use_1.
  apply PTree_Properties.fold_rec; auto.
  intros.
  apply duc_maps_into_function_handle_reg_list; auto.
Qed.

Remark duc_maps_into_function_phibloc: forall f duc pc pb l,
  maps_into_function f duc ->
  (fn_phicode f) ! pc = Some pb ->
  (exists pref, pref ++ l = pb) ->
  maps_into_function f (handle_phi_block duc pc l).
Proof.
  intros.
  generalize dependent duc. induction l; auto.
  destruct a.
  unfold maps_into_function; intros.
  simpl in *; flatten H2.

  eapply IHl with (duc := (handle_reg_list duc (pc, inr (Iphi l0 r)) l0)); eauto.
   { invh ex. exists (x ++ Iphi l0 r :: nil). rewrite <- app_assoc. reflexivity. }
  eapply duc_maps_into_function_handle_reg_list; eauto.
  simpl. exists pb. intuition. invh ex.
   { assert (In (Iphi l0 r) (Iphi l0 r :: l)). auto. apply in_app. auto. }
Qed.

Remark duc_maps_into_function_phicode: forall f duc,
  maps_into_function f duc ->
  maps_into_function f (def_use_2 duc (fn_phicode f)).
Proof.
  intros.
  unfold def_use_2.
  apply PTree_Properties.fold_rec; auto.
  intros.
  eapply duc_maps_into_function_phibloc; eauto.
  exists nil; reflexivity.
Qed.

Lemma duc_maps_into_function: forall f,
  maps_into_function f (make_du_chain f).
Proof.
  unfold make_du_chain. intros.
  eapply duc_maps_into_function_phicode; eauto.
  eapply duc_maps_into_function_code; eauto.
  unfold maps_into_function. intros.
  rewrite P2Map.gi in H.
  contradiction.
Qed.


(** * Dataflow solver over DU chains *)
Module DataflowSolver.
  Module L := Approx.

  Section CDS.

  Definition lattice_values := P2Map.t L.t.
  Definition exec_state := P2Map.t bool.

  Definition instr_workset := (list reg * list reg)%type.
  Definition edge := (node * node)%type.

  Definition state := (list edge * instr_workset * lattice_values * exec_state)%type.
  Record const_state := mkConstantState {
     cs_duc: du_chain;
     cs_preds: PTree.t (list node)
  }.

  Definition db_concat (iws : instr_workset) := let (t, nt) := iws in (t ++ nt).

  Variable f: function.
  Variable absint : instruction -> lattice_values -> option (reg * L.t).
  Variable initial_values : lattice_values.

  Definition cfg := fn_code f.
  Definition phicode := fn_phicode f.

  Definition duc := make_du_chain f.
  Definition bge (x y : L.t) : bool := L.beq (L.lub x y) x.

  Lemma bge_correct: forall x y, bge x y = true -> L.ge x y.
  Proof.
    intros. unfold bge in H. apply L.beq_correct in H. eapply L.ge_trans.
    apply L.ge_refl. apply L.eq_sym. apply H. apply L.ge_lub_right.
  Qed.

  (** Determining whether a given node is executable, in current dataflow solver *)
  Definition preds_of cs pc := match (cs_preds cs) ! pc with
                              | None => nil
                              | Some l => l
                            end.

  Fixpoint node_is_executable_rec (es: exec_state) preds pc' :=
    match preds with
      | nil => false
      | pc :: pcs =>
        if es #2 (pc, pc') then true else node_is_executable_rec es pcs pc'
    end.

  Definition node_is_executable cs (st:state) pc' :=
    match st with
        (cfgwl, iws, lv, es) => node_is_executable_rec es (preds_of cs pc') pc'
    end.

  (* Unconditionally set an edge as executable when there is only one child *)
  Definition single_succ (pc: node) (i: instruction) : option edge :=
   match i with
   | Inop s => Some (pc, s)
   | Iop op args res s => Some (pc, s)
   | Iload chunk addr args dst s => Some (pc, s)
   | Istore chunk addr args src s => Some (pc, s)
   | Icall sig ros args res s => Some (pc, s)
   | Itailcall sig ros args => None
   | Ibuiltin ef args res s => Some (pc, s)
   | Icond cond args ifso ifnot => None
   | Ijumptable arg tbl => None
   | Ireturn optarg => None
   end.

  (** Picks a register from the worklist, from the top list if possible *)
  Fixpoint pick_instr_rec vl (iws_t: list reg) (iws_nt: list reg) : (option reg * instr_workset) :=
    match iws_t, iws_nt with
      | x::xs, ys => (Some x, (xs, ys))
      | nil, y::ys => if Approx.beq_top vl #2 y then pick_instr_rec vl nil ys else (Some y, (nil, ys))
      | nil, nil => (None, (nil, nil))
    end.

  Definition pick_instr vl (iws: instr_workset) : option reg * instr_workset:=
    match iws with
        (ts, nts) => pick_instr_rec vl ts nts
    end.

  (** Updates the state with the new value [nv] of [r], and adds it
   to the workset if necessary *)
  Definition add_instr_aux (r: reg) (v: L.t) (iws: instr_workset) :=
    let (top, ntop) := iws in
    if L.eq_dec v L.top then (r :: top, ntop) else (top, r :: ntop).

  Definition update_vals lv iws r nv :=
    let ov := lv #2 r in
    if bge ov nv
    then (lv, iws)
    else (lv #2 r <- (L.lub nv ov), add_instr_aux r (L.lub nv ov) iws).


  (** Static evaluation of a phi-block *)
   Fixpoint visit_phi_rec (lv: lattice_values) (es: exec_state) pc' args preds x :=
     if Approx.beq_top x then Some L.top else
     match args, preds with
       | y::ys, pc::pcs =>
         let a := if es #2 (pc, pc') then lv #2 y else L.bot in
         visit_phi_rec lv es pc' ys pcs (L.lub x a)
       | nil, nil => Some x
       | _, _ => None
     end.

   Definition visit_phi cs (st_in: state) pc' r_used pi : state :=
     match st_in with (cfgwl, iws, lv, es) =>
     match pi with Iphi args r =>
       if Approx.beq_top lv #2 r then (cfgwl, iws, lv, es) else
       match visit_phi_rec lv es pc' args (preds_of cs pc') r_used with
         | Some x => let (lv', iws') := update_vals lv iws r x in
                     (cfgwl, iws', lv', es)
         | None => (cfgwl, iws, lv, es)
       end
     end
     end.

   Definition visit_phibloc cs st r_used pc :=
     match phicode ! pc with
       | None => st
       | Some pb => fold_left (fun acc pi => visit_phi cs acc pc r_used pi)
                              pb
                              st
     end.

  (** Static evaluation of an instruction *)
   Definition visit_instr (st_in : state) pc instr :=
     match st_in with (cfgwl, iws, lv, es) =>
     match instr with
       | Icond cond args ifso ifnot =>
         match CO.eval_static_condition cond lv ##2 args with
           | Some true => ((pc, ifso)::cfgwl, iws, lv, es)
           | Some false => ((pc, ifnot)::cfgwl, iws, lv, es)
           | None => ((pc, ifso) :: (pc, ifnot) :: cfgwl, iws, lv, es)
         end
       | Ijumptable arg tbl =>
         match lv #2 arg with
           | CO.I k => match list_nth_z tbl (Int.unsigned k) with
                         | None => (map (fun x:node => (pc, x)) tbl ++ cfgwl, iws, lv, es)
                         | Some pc' => ((pc, pc')::cfgwl, iws, lv, es)
                       end
           | x => (map (fun x:node => (pc, x)) tbl ++ cfgwl, iws, lv, es)
         end
       | _ => match absint instr lv with
                | Some (r, x) =>
                  let (lv', iws') := update_vals lv iws r x in
                  (cfgwl, iws', lv', es)
                | None => (cfgwl, iws, lv, es)
              end
     end
     end.

   (** The register defined by an instruction *)
   Definition def_reg i :=
     match i with
       | Iop _ _ r _ | Iload _ _ _ r _  | Istore _ _ _ r _
       | Icall _ _ _ r _ | Ibuiltin _ _ r _  => Some r
     | _ => None
   end.

   Definition visit_ssainstr cs st r_used (ssai : ssainstruction) :=
     match st with (_, _, lv, _) =>
     match ssai with
       | (pc, inr pi) =>
         visit_phi cs st pc r_used pi
       | (pc, inl instr) =>
         match def_reg instr with
           | Some r => if Approx.beq_top lv #2 r (* Optim: nothing to do if at top *)
                       then st
                       else match node_is_executable cs st pc with
                              | false => st
                              | true => visit_instr st pc instr
                            end
           | None =>  match node_is_executable cs st pc with (* Mostly conditionals*)
                              | false => st
                              | true => visit_instr st pc instr
                      end
         end
     end
     end.

   Definition step (ms : const_state * state) : (option (lattice_values * exec_state))
                                                + (const_state * state) :=
     let (cs, st) := ms in
     match st with (cfgwl, iws, lv, es) =>
     match cfgwl with
       | (pc0, pc) :: cfgwl' =>
         match es #2 (pc0, pc) with
           | true => inr _ (cs, (cfgwl', iws, lv, es))
           | false =>
             let es' := es #2 (pc0, pc) <- true in
             let st2 := visit_phibloc cs (cfgwl', iws, lv ,es') L.bot pc in
             match cfg ! pc with
               | None => inl _ None
               | Some instr =>
                 match visit_instr st2 pc instr with
                   | (cfgwl'', iws'', lv'', es'') =>
                     match single_succ pc instr with
                       | None => inr _ (cs, (cfgwl'', iws'', lv'', es''))
                       | Some (x, y) => inr _ (cs, (if es' #2 (x,y)
                                                    then cfgwl''
                                                    else (x,y)::cfgwl'', iws'', lv'', es''))
                     end
                 end
             end
         end
       | nil =>
         match pick_instr lv iws with
           | (Some r, iws') => (* Fold over all uses of [r] *)
             inr _ (cs, (fold_left (fun st_in ssai => visit_ssainstr cs st_in lv #2 r ssai)
                                   (cs_duc cs) #2 r
                                   (cfgwl, iws', lv, es)))
           | _ => inl _ (Some (lv, es))
         end
     end

     end.

   Definition initial_state : option state :=
     let start i := match single_succ (fn_entrypoint f) i with
                      | None => nil
                      | Some x => x :: nil
                    end in
     match cfg ! (fn_entrypoint f) with
       | None => None
       | Some i => Some (start i, (nil, nil), initial_values, P2Map.init false)
     end.


  (** * Post-fixpoint checker *)
  Definition executable_node (pc': node) (es: exec_state) :=
    pc' = fn_entrypoint f \/ exists pc, es #2 (pc, pc') = true /\ SSA.cfg f pc pc'.

  Definition bexecutable_node (pc': node) (preds: PTree.t (list node)) (es: exec_state) :=
    if Pos.eq_dec pc' (fn_entrypoint f) then true else
      existsb (fun pc => es #2 (pc, pc')) preds !!! pc'.

  Definition check_code lv preds es :=
    forall_ptree (fun pc i => match bexecutable_node pc preds es with
                                | false => true
                                | true => match absint i lv with
                                            | None => true
                                            | Some (r, nv) => bge (lv #2 r) nv
                                          end
                              end) cfg.

  Fixpoint check_phiinstruction lv es r rs preds pc' :=
    match rs, preds with
      | nil, nil => true
      | x::xs, pc::pcs => match es #2 (pc, pc') with
                            | false => check_phiinstruction lv es r xs pcs pc'
                            | true => bge (lv #2 r) (lv #2 x) &&
                                          check_phiinstruction lv es r xs pcs pc'
                          end
      | _, _ => false
    end.

  Definition check_phicode_g lv es preds (pc: node) pb :=
    forallb (fun pi => match pi with
                         | Iphi rs r => check_phiinstruction lv es r rs (preds !!! pc)  pc
                       end) pb.

  Definition check_phicode lv es preds :=
    forall_ptree (check_phicode_g lv es preds) phicode.

  Definition check_non_exec_edge lv pc pc' :=
    match cfg ! pc with
      | Some (Icond cond args ifso ifnot) =>
        match Pos.eq_dec pc' ifso with
          | left _ => match CO.eval_static_condition cond lv ##2 args with
                      | Some false => match Pos.eq_dec pc' ifnot with
                                        | right _ => true
                                        | left _ => match CO.eval_static_condition cond lv ##2 args with
                                                      | Some true => true
                                                      | _ => false
                                                    end
                                      end
                      | _ => false
                      end
          | right _ => match Pos.eq_dec pc' ifnot with
                       | right _ => false
                       | left _ => match CO.eval_static_condition cond lv ##2 args with
                                   | Some true => true
                                   | _ => false
                                   end
                       end
        end
      | Some (Ijumptable arg tbl) =>
        match lv #2 arg with
          | CO.I n => match list_nth_z tbl (Int.unsigned n) with
                        | Some p => if Pos.eq_dec p pc' then false else true
                        | None => true (* ???? *)
                      end
          | _ => false
        end
      | Some i => false
      | None => false
    end.

  Definition check_executable_flags lv es preds :=
    forall_ptree
      (fun pc' _ => forallb (fun pc => match bexecutable_node pc preds es with
                                         | true => if bool_dec es #2 (pc, pc') false
                                                   then check_non_exec_edge lv pc pc'
                                                   else true
                                         | false => true
                                       end) (preds !!! pc')) cfg.

  Definition check lv es preds :=
    (check_phicode lv es preds)
      && (check_code lv preds es)
      && (check_executable_flags lv es preds).

   (** Fixpoint *)
   Definition fixpoint (tool:ssa_tool f) :=
     let failed := (P2Map.init L.top, P2Map.init true) in
     let preds :=  make_predecessors (fn_code f) successors_instr in
     let cs := mkConstantState (make_du_chain f) preds in
     match initial_state with
         | Some is =>
           match PrimIter.iterate _ _ step (cs, is) with
             | Some (Some (lv, es)) =>
               let lv' := P2Map.map (fun v => if Approx.eq_dec v Approx.bot then L.top else v) lv in
               if check lv' es preds then (lv', es) else failed
             | _ => failed
           end
         | None => failed
     end.




  (** ** Proof of the checker *)
   Remark bexecutable_node_correct: forall es pc',
     bexecutable_node pc' (make_predecessors (fn_code f) successors_instr) es = true <->
     executable_node pc' es.
   Proof.
     intros es pc'. split. unfold executable_node, bexecutable_node in *.
     intros H.
     destruct (Pos.eq_dec pc' (fn_entrypoint f)). auto. right.
     apply existsb_exists in H as [pc [H1 H2]].
     exists pc. intuition.
     assert (exists i : instruction, (fn_code f) ! pc = Some i).
     unfold "!!!" in *. flatten H1.
     eapply make_predecessors_some in Eq; eauto.
     unfold In in *. contradiction.
     destruct H as [i H].
     assert (In pc' (successors_instr i)).
     eapply make_predecessors_correct2; eauto.
     econstructor; eauto.

     intros H. unfold bexecutable_node.
     destruct (Pos.eq_dec pc' (fn_entrypoint f)). auto.
     apply existsb_exists. unfold executable_node in *.
     destruct H as [H | [pc H]].
     contradiction.
     exists pc.
     intuition.
     invh SSA.cfg.
     eapply make_predecessors_correct_1; eauto.
   Qed.

   Definition code_post_fixpoint lv es :=
     forall pc i r v,
     (fn_code f) ! pc = Some i ->
     executable_node pc es ->
     absint i lv = Some (r, v) ->
     L.ge lv #2 r v.

   Lemma check_code_correct: forall lv es,
     check_code lv (make_predecessors (fn_code f) successors_instr) es = true ->
     code_post_fixpoint lv es.
   Proof.
     intros lv es H. unfold check_code, code_post_fixpoint in *.
     intros. eapply forall_ptree_true in H; eauto.
     apply bexecutable_node_correct in H1.
     flatten H.
     apply bge_correct; auto.
   Qed.

   Definition phicode_post_fixpoint lv es := forall pc pb r l xi pc' k,
    (fn_phicode f) ! pc' = Some pb ->
    In (Iphi l r) pb ->
    index_pred (make_predecessors (fn_code f) successors_instr) pc pc' = Some k ->
    es #2 (pc, pc') = true ->
    nth_error l k = Some xi ->
    L.ge (lv #2 r) (lv #2 xi).

   Hint Resolve bge_correct.

   Lemma get_index_cons_succ: forall x xs k y,
     SSA.get_index (x::xs) y = Some (S k) -> SSA.get_index xs y = Some k.
   Proof.
     intros.
     unfold SSA.get_index in *.
     simpl in *.
     flatten H.
     eapply get_index_some_sn; eauto.
     simpl in *.
     flatten; eauto.
     assert ((k+1)%nat = S k). omega.
     rewrite H0 in *.
     assumption.
   Qed.

   Lemma check_phiinstruction_correct: forall lv es pb r l pc' preds,
     (fn_phicode f) ! pc' = Some pb ->
     check_phiinstruction lv es r l preds  pc' = true->
     forall pc xi k,
     (k < length preds)%nat ->
     SSA.get_index preds pc = Some k ->
     es #2 (pc, pc') = true ->
     nth_error l k = Some xi ->
     L.ge (lv #2 r) (lv #2 xi).
   Proof.
     intros.
     generalize dependent l.
     induction preds.
     + simpl in *. intros. omega.
     + simpl in *. intros.
       destruct l.
       simpl in *. congruence.

       assert (check_phiinstruction lv es r l preds pc' = true).
       simpl in *.
       flatten H0; apply andb_true_iff in H0; intuition.

       destruct (eq_nat_dec k O).
       - subst. unfold nth_error in H4. inv H4.
         assert (a = pc).
         apply get_index_nth_error in H2.
         unfold nth_error in *. simpl in *. inv H2. reflexivity.
         subst. simpl in *. flatten H0.
          * apply bge_correct. apply andb_true_iff in H0. intuition.
          * unfold node in *. congruence.
       - assert (exists k0, k = S k0) as [k0 Hk].
           destruct (O_or_S k). inv s. exists x. auto.
           congruence.
         subst.
         eapply IHpreds with (k := k0) (l := l); eauto.
         * omega.
         * eapply get_index_cons_succ; eauto.
   Qed.

   Lemma check_phicode_correct: forall lv es,
     check_phicode lv es (make_predecessors (fn_code f) successors_instr) = true ->
     phicode_post_fixpoint lv es.
   Proof.
     intros lv es H.
     unfold phicode_post_fixpoint, check_phicode in *.
     intros pc pb r l xi pc' k H1 H2 H3 H4.
     eapply forall_ptree_true in H; eauto.
     unfold check_phicode_g in *. eapply forallb_forall in H; eauto.
     flatten H.
     eapply check_phiinstruction_correct; eauto.
     eapply index_pred_some; eauto.
     unfold index_pred in *. flatten H3.
   Qed.

   Definition exec_flags_sound lv es :=
     forall pc pc' i
            (EX_CFG: SSA.cfg f pc pc')
            (EX_NOTEXEC: es #2 (pc, pc') = false)
            (EX_INS: (fn_code f) ! pc' = Some i),
       ~executable_node pc es \/
       match (fn_code f) ! pc with
         | Some (Icond cond args ifso ifnot) =>
           (ifso  = pc' -> CO.eval_static_condition cond lv ##2 args = Some false) /\
           (ifnot = pc' -> CO.eval_static_condition cond lv ##2 args = Some true)
         | Some (Ijumptable arg tbl) =>
           exists n, (lv #2 arg = CO.I n /\ list_nth_z tbl (Int.unsigned n) <> Some pc')
         | _ => False
       end.

   Lemma check_executable_flags_correct: forall es lv,
     check_executable_flags lv es (make_predecessors (fn_code f) successors_instr) = true ->
     exec_flags_sound lv es.
   Proof.
     intros.
     unfold exec_flags_sound, check_executable_flags in *. intros.
     match goal with
       | H: forall_ptree ?f cfg = true |- _ =>
         assert (forall pp x, cfg ! pp = Some x -> f pp x = true) as H0
     end.
     apply forall_ptree_true; auto.
     destruct (classic (executable_node pc es)); intuition.
     destruct ((fn_code f) ! pc) eqn:eq.
     + unfold cfg in *. specialize (H0 pc' i EX_INS).
       eapply forallb_forall with (x := pc) in H0; eauto.
       flatten H0; eauto.
       - unfold check_non_exec_edge in H0. unfold cfg in *. rewrite eq in H0.
         flatten H0; right; intuition.
         * exists i1. intuition. rewrite Eq2 in H2. inv H2. auto.
         * exists i1. intuition. congruence.
       - left. intro contra; apply bexecutable_node_correct in contra. congruence.
       - invh SSA.cfg. eapply make_predecessors_correct_1; eauto.
     + invh SSA.cfg. unfold fn_code in *. rewrite eq in HCFG_ins. congruence.
   Qed.

   Lemma top_is_post_fixpoint:
    code_post_fixpoint (P2Map.init L.top) (P2Map.init true)
    /\ phicode_post_fixpoint (P2Map.init L.top) (P2Map.init true)
    /\ exec_flags_sound (P2Map.init L.top) (P2Map.init true).
  Proof.
    unfold code_post_fixpoint. split. intros.
    rewrite P2Map.gi. apply L.ge_top. split.
    unfold phicode_post_fixpoint. intros. rewrite P2Map.gi. apply L.ge_top.
    unfold exec_flags_sound. intros. rewrite P2Map.gi in *. discriminate.
  Qed.

  Lemma check_correct: forall lv es,
    check lv es (make_predecessors (fn_code f) successors_instr) = true ->
    code_post_fixpoint lv es /\ phicode_post_fixpoint lv es /\ exec_flags_sound lv es.
  Proof.
    intros. unfold check in H. apply andb_prop in H. destruct H as [H1 H2].
    apply andb_prop in H1. destruct H1 as [H1 H3].
    split.
      apply check_code_correct; assumption. split.
      apply check_phicode_correct; assumption.
      apply check_executable_flags_correct; assumption.
  Qed.

  (* Proof that uninitialized values stay at bot *)
  Definition get_lv (st: state) :=
    match st with
        (_, _, lv, _) => lv
    end.

  Definition not_defined r := (forall lv r' nv i pc,
    cfg ! pc = Some i -> absint i lv = Some (r', nv) -> r <> r') /\
    (forall pc pb l r', phicode ! pc = Some pb -> In (Iphi l r') pb -> r <> r').

  Remark defined_nowhere_stationary_aux_update_val:
    forall lv b r t lv',
      fst (update_vals lv b r t) = lv' ->
      (forall r', r' <> r -> lv' #2 r' = lv #2 r').
  Proof.
    intros.
    unfold update_vals in *.
    flatten H; simpl in *; try congruence.
    subst. rewrite P2Map.gso; auto.
  Qed.

  Remark defined_nowhere_stationary_aux_visit_instr: forall st r pc i,
    not_defined r ->
    cfg ! pc = Some i ->
    (get_lv (visit_instr st pc i)) #2 r = (get_lv st) #2 r.
  Proof.
    intros.
    unfold not_defined in *.
    unfold visit_instr in *.
    destruct H as [Ha Hb].
    flatten; simpl in *; try (reflexivity); subst;
      try match goal with
          [H: (absint _ _ = Some (?r0, _)),
           H1: update_vals ?l ?i0 ?r1 ?t = (?t0, ?i1)  |- (_ = ?l !!2 r) ]=>
           assert (r <> r0);
             [intro contra; subst; eapply Ha; eauto |
              eapply (defined_nowhere_stationary_aux_update_val l i0 r0 t) ; eauto];
             rewrite H1; simpl; auto
      end.
  Qed.

  Remark defined_nowhere_stationary_aux_visit_phi: forall st cs r pc r_used pi pb,
    not_defined r ->
    phicode ! pc = Some pb -> In pi pb ->
    (get_lv (visit_phi cs st pc r_used pi)) #2 r = (get_lv st) #2 r.
  Proof.
    intros.
    unfold visit_phi in *.
    flatten.
    assert (r <> r0) by ( destruct H as [Ha Hb]; eapply Hb; eauto).
    subst.
    assert (fst (update_vals l i r0 a) = t) by (rewrite Eq5; simpl; auto).
    eapply defined_nowhere_stationary_aux_update_val; go.
  Qed.

  Remark defined_nowhere_stationary_aux_visit_phibloc_rec:
    forall st st' cs r pc r_used pb,
    not_defined r ->
    phicode ! pc = Some pb ->
    (forall l, (exists l', l' ++ l = pb) ->
               fold_left (fun acc pi => visit_phi cs acc pc r_used pi)
                         l
                         st = st' ->
               (get_lv st') #2 r = (get_lv st) #2 r).
  Proof.
    intros.
    generalize dependent st.
    induction l.
    + intros. simpl in *. unfold get_lv. flatten.
    + intros.
      simpl in *.
      assert ((get_lv st') !!2 r = (get_lv (visit_phi cs st pc r_used a)) !!2 r).
      eapply IHl with (st := visit_phi cs st pc r_used a); eauto.
      invh ex.
      exists (x ++ a :: nil). {
        rewrite <- app_assoc.
        simpl.
        apply eq_refl.
      }
      assert ((get_lv (visit_phi cs st pc r_used a)) !!2 r = (get_lv st) !!2 r).
      eapply defined_nowhere_stationary_aux_visit_phi; eauto.
      invh ex. {
        assert (In a (a::l)). apply in_eq.
        apply in_app.
        auto.
      }
      congruence.
  Qed.

  Remark defined_nowhere_stationary_aux_visit_phibloc: forall st st' cs r pc r_used,
    not_defined r ->
    visit_phibloc cs st r_used pc = st' ->
    (get_lv (visit_phibloc cs st r_used pc)) !!2 r = (get_lv st) !!2 r.
  Proof.
    intros.
    unfold visit_phibloc in *.
    destruct (phicode ! pc) as [pb |] eqn:eq.
    eapply defined_nowhere_stationary_aux_visit_phibloc_rec
      with (l := pb) (cs := cs) (r_used := r_used) (st := st); eauto.
    exists nil. reflexivity.
    subst. reflexivity.
  Qed.

  Lemma defined_nowhere_stationary_aux_rec_helper: forall r m (x : ssainstruction) l',
    maps_into_function f m ->
    (exists pref, pref ++ x :: l' = m #2 r) ->
    ssai_in_function x f.
  Proof.
    intros.
    destruct H0 as [prefs H0].
    assert (In x m #2 r).
    rewrite <- H0.
    assert (In x (x::l')); auto.
    apply in_app. auto.
    eapply H; eauto.
  Qed.

  Remark defined_nowhere_stationary_aux: forall st st' r cs cs',
    not_defined r -> step (cs, st) = inr (cs', st') ->
    maps_into_function f (cs_duc cs) ->
    (get_lv st) #2 r = (get_lv st') #2 r.
  Proof.
    intros.
    remember st as St.
    destruct st as [[[a b] lv] c].
    unfold step in *.
    rewrite HeqSt in *.
    flatten H0; try (flatten H0; reflexivity); simpl;
    try (match goal with
        [ h: context[ visit_phibloc ?cs ?stin ?bot ?n0 ] |- _ ] =>
        assert ((get_lv (visit_phibloc cs stin bot n0)) !!2 r = lv !!2 r);
          [eapply defined_nowhere_stationary_aux_visit_phibloc; eauto |
           assert ( (get_lv (visit_instr
                               (visit_phibloc cs stin bot n0) n0 i)) !!2 r =
                    (get_lv (visit_phibloc cs stin bot n0)) !!2 r);
                  [eapply defined_nowhere_stationary_aux_visit_instr; eauto |
                    assert ((get_lv
                               (visit_instr
                                  (visit_phibloc cs stin bot n0) n0 i)) = t)]
          ]
      end; [

      match goal with
          [ H: visit_instr _ _ _ = _ |- _ ] => rewrite H; reflexivity
      end |
      congruence]).

    match goal with
        [ |- context [ fold_left ?fn_ ?l_ ?acc0 ] ]=>
        set (fn := fn_); set (l := l_)
    end.
    assert (forall l' acc,
              (exists pref, pref ++ l' = l) ->
              (get_lv (fold_left fn l' acc)) !!2 r = (get_lv acc) !!2 r) as Hbi.
    + induction l'; intros; simpl in *.
      - tauto.
      - assert ((get_lv (fn acc a)) #2 r = (get_lv acc) #2 r) as Hsame.
        * unfold fn. unfold visit_ssainstr.
          flatten;
          try (unfold l in *; subst;
               assert (ssai_in_function (n, inl i1) f);
               [eapply defined_nowhere_stationary_aux_rec_helper; eauto |
                eapply defined_nowhere_stationary_aux_visit_instr; eauto]).
          assert (ssai_in_function (n, inr p1) f).
          eapply defined_nowhere_stationary_aux_rec_helper; eauto.
          unfold ssai_in_function in *.
          invh ex. invh and.
          eapply defined_nowhere_stationary_aux_visit_phi; eauto.
        * rewrite <- Hsame.
          eapply IHl'.
          invh ex.
          exists (x ++ a::nil). rewrite <- app_assoc. auto.
    + rewrite Hbi; auto.
      exists nil; auto.
  Qed.

  Remark cs_constant: forall cs cs' st st',
    step (cs, st) = inr (cs', st') -> cs = cs'.
  Proof.
    intros.
    unfold step in *. flatten H.
  Qed.

  Lemma defined_nowhere_stationary: forall r lv es is ,
    not_defined r -> initial_state = Some is ->
    PrimIter.iterate
      _ _ step (mkConstantState (make_du_chain f)
                                (make_predecessors (fn_code f) successors_instr), is) = Some (Some (lv, es)) ->
     lv #2 r = initial_values #2 r.
  Proof.
    intros.
    set (P (s:const_state*state) :=
           forall cs st, s = (cs, st) ->
                         ((get_lv st) #2 r = initial_values #2 r)
                         /\ (maps_into_function f (cs_duc cs))).
    set (Q (o: option (lattice_values * exec_state)) :=
           forall v es', o = Some (v, es') -> v #2 r = initial_values #2 r).
    assert (Q (Some (lv, es))).
    {
      eapply PrimIter.iterate_prop with (step := step) (P := P) ; unfold P, Q.
      + intro. destruct (step a) eqn:eq.
        unfold step in eq. intros. subst.
        flatten eq.
        assert ((get_lv ((nil, i, v, es'):state)) #2 r =  v #2 r) by reflexivity.
        destruct (H2 c (nil, i, v, es')) as [Hlv Hduc]; auto.

        intros. subst. destruct a as (cs0, st0).
        destruct (H2 cs0 st0) as [Hlv Hduc]; auto.
        split. rewrite <- Hlv. apply eq_sym.
        eapply defined_nowhere_stationary_aux; eauto.
        eapply cs_constant in eq. subst. assumption.

      + eapply H1.
      + intros. unfold initial_state in *.
        flatten H0. split; [auto | apply duc_maps_into_function].
                    split; [auto | apply duc_maps_into_function].
      }

      unfold Q in *. apply H2 with es. apply eq_refl.
  Qed.

  Lemma defined_nowhere_becomes_top: forall tool r,
    not_defined r -> initial_values #2 r = L.bot -> (fst (fixpoint tool)) #2 r = L.top.
  Proof.
    intros.
    unfold fixpoint in *.
    flatten; subst; simpl; try (rewrite P2Map.gi; eauto).
    assert (l #2 r = initial_values #2 r)
      by (eapply defined_nowhere_stationary; eauto).
    rewrite P2Map.gmap.
    rewrite H1. rewrite H0. unfold L.bot.
    destruct (Approx.eq_dec CO.Novalue CO.Novalue); auto. congruence.
  Qed.

  Lemma defined_nowhere_stays_top: forall tool r lv,
    not_defined r -> initial_values #2 r = L.top -> lv = fst (fixpoint tool) -> lv #2 r = L.top.
  Proof.
    intros; unfold fixpoint in *.
    flatten H1 ; subst; try (simpl ; rewrite P2Map.gi;  eauto).
    simpl. rewrite P2Map.gmap.
    assert (l !!2 r = initial_values !!2 r)
      by (eapply defined_nowhere_stationary; eauto).
    rewrite H0 in *.
    rewrite H1.
    unfold Approx.bot, L.top.
    destruct (Approx.eq_dec CO.Unknown CO.Novalue); apply eq_refl.
  Qed.

  Lemma vals_never_bot: forall tool r,
                          (fst (fixpoint tool)) #2 r <> L.bot.
  Proof.
    intros. unfold fixpoint in *.
    flatten; subst; simpl;
    try (intro contra; rewrite P2Map.gi in contra; discriminate).
    rewrite P2Map.gmap; flatten; intuition; discriminate.
  Qed.

  (** * Correctness lemma *)
  Lemma post_fixpoint: forall tool lv es,
    fixpoint tool = (lv, es) ->
    code_post_fixpoint lv es
    /\ phicode_post_fixpoint lv es
    /\ exec_flags_sound lv es.
  Proof.
    intros. unfold fixpoint in H.
    destruct (initial_state).
    match goal with
        H: context [ PrimIter.iterate ?x ?y ?z ?t ] |- _ =>
        destruct (PrimIter.iterate x y z t)
    end.
     + destruct o. destruct p.
       - flatten H.
         apply check_correct in Eq. assumption.
         apply top_is_post_fixpoint.
       - inv H. apply top_is_post_fixpoint.
     + inv H. apply top_is_post_fixpoint.
     + inv H. apply top_is_post_fixpoint.
  Qed.

 End CDS.
 End DataflowSolver.

(** * SCCP optimization *)
Section Opt.

  (** ** Definition *)
 Definition handle_instr (i: instruction) res : option (reg * Approx.t) :=
   match i with
     | Iop op regs r _ =>
       let vs := List.map (fun r => (P2Map.get r res)) regs in
       Some (r,  CO.eval_static_operation op vs)
     | Iload _ _ _ r _ | Icall _ _ _ r _ | Ibuiltin _ _ r _ => Some (r, CO.Unknown)
     | _ => None
   end.

 Definition initial f :=
   List.fold_left
     (fun vals r => P2Map.set r Approx.top vals)
     (fn_params f)
     (P2Map.init Approx.bot).

 Definition fixpoint f:=
   let fp := (DataflowSolver.fixpoint f handle_instr (initial f) f) in
   ((fun r => P2Map.get r (fst fp)),snd fp).

  Definition transf_instr (app: reg -> Approx.t) (n: node) i :=
   match i with
     | Iop op args res s =>
       match CO.eval_static_operation op (List.map (fun r => app r) args) with
         | CO.I k => Iop (Ointconst k) nil res s
         | CO.F k => Iop (Ofloatconst k) nil res s
         | _ => i
       end
     | _ => i
   end.

  (** ** Proof obligation implying the preservation of SSA well-formedness *)
  Lemma new_code_same_or_Iop :
  forall (f:function) (Hwf: wf_ssa_function f) pc ins,
    (fn_code f) ! pc = Some ins ->
    transf_instr (fst (fixpoint f)) pc ins = ins
    \/ match ins with
         | Iop _ _ dst pc'
         | Iload _ _ _ dst pc'
         | Icall _ _ _ dst pc'
         | Ibuiltin _ _ dst pc' =>
           exists op' args',
             transf_instr (fst (fixpoint f)) pc ins = Iop op' args' dst pc'
             /\ forall x, In x args' -> exists d : node, def f x d /\ sdom f d pc
         | _ => False
       end.
Proof.
  destruct ins; simpl; flatten; eauto;
  match goal with
      [ H: _ |- context[ Iop (?Op ?i) nil _ _] ] =>
      right; exists (Op i); exists nil;
      split; auto;
      intros x Hin; inv Hin
  end.
Qed.

(** ** Instantiating the generic optimization using previous proof obligation *)
 Definition transf_function (f : function) : function :=
   Opt.transf_function_tool _ fixpoint transf_instr new_code_same_or_Iop f.

 Definition transf_fundef (f: fundef) : fundef :=
   Opt.transf_fundef_tool _ fixpoint transf_instr new_code_same_or_Iop f.

 Definition transf_program (p: program) : program :=
   Opt.transf_program_tool _ fixpoint transf_instr new_code_same_or_Iop p.

End Opt.
