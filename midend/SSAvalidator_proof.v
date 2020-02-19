(** This file contains the proof that the implementation of the validator satisfies its specification, that can be found in SSAvalidspec. *)

Require Import Coq.Unicode.Utf8.
Require Import Axioms.
Require Import Classical.
Require Recdef.
Require Import FSets.
Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Op.
Require Import Registers.
Require Import Conventions. 
Require Import Kildall.
Require Import KildallComp.
Require Import Utils.
Require Import RTL.
Require Import RTLutils.
Require Import Path.
Require RTLdfs.
Require Import SSA.
Require Import SSAutils.
Require Import SSAvalid.  
Require Import Utilsvalidproof.
Require Import SSAvalidprop.
Require Import LightLive.
Require Import SSAvalidspec.


(** * The checker [check_function_inv] satisfies its specification *)

Lemma check_function_inv_correct0 : forall (f: RTL.function), 
  check_function_inv f (make_predecessors (RTL.fn_code f) RTL.successors_instr) = true -> 
  forall pc pc' instr , (RTL.fn_code f) ! pc = Some instr ->
    In pc' (RTL.successors_instr instr) -> 
    exists instr', (RTL.fn_code f) ! pc' = Some instr'.
Proof.
  intros tf  CHECK pc  pc' instr Hinstr Hsuccs.
  unfold check_function_inv in *.
  case_eq ((RTL.fn_code tf) ! (RTL.fn_entrypoint tf)); intros; rewrite H in *. 
  destruct i ; boolInv; try congruence. 
  eapply ptree_forall with (i := pc) in H1; eauto. 
  unfold check_instr_inv in H1. rewrite Hinstr in *. boolInv.
  set (f := (fun (i : positive) => match (RTL.fn_code tf) ! i with
                                     | Some _ => true
                                     | None => false
                                   end)) in *.
  exploit (list_forall f) ; eauto. 
  unfold f in *.
  case_eq ((RTL.fn_code tf) ! pc') ; intros; eauto.
  rewrite H4 in *; congruence. inv CHECK.
Qed.
  
Lemma check_function_inv_correct01 : forall (f: RTL.function), 
  check_function_inv f (make_predecessors (RTL.fn_code f) RTL.successors_instr) = true -> 
  forall i ins, 
    (RTL.fn_code f)!i = Some ins ->
    In (RTL.fn_entrypoint f) (RTL.successors_instr ins) -> False.
Proof.
  intros f CHECK pc ins Hpc1 Hcont. 
  unfold check_function_inv in *.
  case_eq ((RTL.fn_code f) ! (RTL.fn_entrypoint f)); [intros i Hi | intros Hi] ; rewrite Hi in *.
  - destruct i ; try congruence.
    unfold no_pred in *.
    boolInv. clear H0.
    case_eq ((make_predecessors (RTL.fn_code f) RTL.successors_instr) !!! (RTL.fn_entrypoint f));
      [intros Hpreds | intros p l Hpreds]; rewrite Hpreds in *. 
    * clear Hi.
      exploit @make_predecessors_correct_1; eauto. 
      intros Hcont'. rewrite Hpreds in Hcont'. inv Hcont'.
    * congruence. 
  - congruence.
Qed.

Lemma check_function_inv_correct11 : forall (f: RTL.function), 
  check_function_inv f (make_predecessors (RTL.fn_code f) RTL.successors_instr) = true -> 
  (exists instr, (RTL.fn_code f) ! (RTL.fn_entrypoint f) = Some instr).
Proof.
  intros tf  CHECK. 
  unfold check_function_inv in *.
  case_eq ((RTL.fn_code tf) ! (RTL.fn_entrypoint tf)); intros; eauto.
  rewrite H in *. inv CHECK.
Qed.

Lemma check_function_inv_correct12 : forall (f: RTL.function), 
  check_function_inv f (make_predecessors (RTL.fn_code f) RTL.successors_instr) = true -> 
  ~ RTLutils.join_point (RTL.fn_entrypoint f) f.
Proof.
  intros tf  CHECK. 
  generalize (check_function_inv_correct11 tf CHECK) ; intros.
  destruct H.
  intro Hjp.
  inv Hjp. 
  
  unfold check_function_inv in *.
  rewrite H in *.
  destruct x ; try congruence ; boolInv.
  rename H1 into CHECK.
  eapply ptree_forall with (i := RTL.fn_entrypoint tf) in CHECK; eauto. 
  unfold check_instr_inv in CHECK. 
  rewrite peq_true in *.
  boolInv.
  rewrite Hpreds in *.
  destruct l; simpl in *; try omega.
  destruct l; simpl in *; try omega.
  congruence.
Qed.

Lemma check_function_inv_correct1 : forall (f: RTL.function), 
  check_function_inv f (make_predecessors (RTL.fn_code f) RTL.successors_instr) = true -> 
  (exists instr, (RTL.fn_code f) ! (RTL.fn_entrypoint f) = Some instr)
  /\  ~ RTLutils.join_point (RTL.fn_entrypoint f) f.
Proof.
  intros. split.
  apply check_function_inv_correct11; eauto.
  apply check_function_inv_correct12; auto.
Qed.

Lemma check_function_inv_correct3 : forall f: RTL.function, 
  check_function_inv f (make_predecessors (RTL.fn_code f) RTL.successors_instr) = true -> 
  (forall jp pc i,
    RTLutils.join_point jp f -> In jp (RTL.successors_map f) !!! pc ->
    (RTL.fn_code f) ! jp = Some i ->
    (RTL.fn_code f) ! pc = Some (RTL.Inop jp)).  
Proof.
  intros tf CHECK jp pc i Hjp Hinsuccpc Hi.
  generalize Hjp; intros.
  inv Hjp0. 

  generalize CHECK ; intros CHECK'.
  unfold check_function_inv in CHECK'.
  exploit check_function_inv_correct11 ; eauto. intros [instr Hinstr]. 
  rewrite Hinstr in *. allinv. 
  destruct instr ; try congruence.
  boolInv. 
  rename H0 into CHECK'.
  eapply ptree_forall with (i := jp) in CHECK'; eauto. 
  unfold check_instr_inv in CHECK'.
  
  rewrite Hi in *.  rewrite Hpreds in *. 
  destruct (peq (RTL.fn_entrypoint tf) jp).
  - 
    boolInv. 
    destruct l; simpl in *; try (apply False_ind; omega).
    destruct l; simpl in *; try (apply False_ind; omega).
    congruence.
  - 
    boolInv.
    
    destruct l. congruence. 
    destruct l. simpl in *. omega.

    assert (In pc ((make_predecessors (RTL.fn_code tf) RTL.successors_instr)!!! jp)).
    { 
      unfold RTL.successors_map, successors_list in Hinsuccpc.      
      rewrite PTree.gmap1 in Hinsuccpc.
      case_eq (option_map RTL.successors_instr (RTL.fn_code tf) ! pc) ; intros.
      exploit option_map_some; eauto. intros [ipc Hipc]. 
      eapply make_predecessors_correct_1 with (n1:= pc); eauto.
      unfold option_map in *.
      rewrite Hipc in *. inv H1. auto.
      
      unfold option_map in *.
      case_eq ((RTL.fn_code tf) ! pc) ; intros; rewrite H3 in *. 
      congruence.
      inv Hinsuccpc.
    }      

    unfold successors_list in *.
    rewrite Hpreds in *.
    unfold RTL.successors_map in *.
    rewrite PTree.gmap1 in Hinsuccpc.
    unfold option_map in Hinsuccpc. 

    exploit @make_predecessors_some; eauto.
    intros [ipc Hipc]. 
    eapply list_forall in H1; eauto.
    unfold instr_is_nop in *. 
    rewrite Hipc in *.
    destruct ipc ; try congruence.
    simpl in *. destruct Hinsuccpc; subst; intuition.
Qed.


(** * Utility lemmas and usefull tactics *)

Lemma fold_left_update_ctx_propagate_error : 
  forall preds def def_phi clean_code live  ppoints e,
  fold_left (update_ctx preds def def_phi clean_code live) ppoints
  (Error e) = Error e.
Proof.
  induction ppoints; auto.
Qed.

Ltac reduce_get_option := 
  match goal with
    [ id: context [get_option ?x _] |- _ ] => 
    generalize id; clear id; case_eq x; simpl; intros; 
      try (rewrite fold_left_update_ctx_propagate_error in *; try congruence)
  end.

Ltac reduce_is_joinpoint := 
  match goal with
    [ id: context [is_joinpoint ?preds ?n] |- _ ] => 
    generalize id; clear id; case_eq (is_joinpoint preds n); simpl; intros; 
      try (rewrite fold_left_update_ctx_propagate_error in *; try congruence)
  end.

Ltac reduce_forall3_ptree := 
  match goal with
    [ id: context [forall3_ptree ?f ?m1 ?m2 ?m3] |- _ ] => 
    generalize id; clear id; case_eq (forall3_ptree f m1 m2 m3); simpl; intros; 
      try (rewrite fold_left_update_ctx_propagate_error in *; try congruence)
  | [ |- context [forall3_ptree ?f ?m1 ?m2 ?m3] ] => 
    case_eq (forall3_ptree f m1 m2 m3); simpl; intros Hforall2; 
      try (rewrite fold_left_update_ctx_propagate_error in *; try congruence)
  end.

Ltac rewrite_some :=
 match goal with
  |  [ id: _ = Some _ |- _] => rewrite id
  |  [ id: _ = None |- _] => rewrite id
  end.

Lemma op_forall3_ptree : forall (def_phi:PTree.t index) (live: Regset.t) n (x:option index),
  (fun x i i' o => 
    let i := match i with None => dft_pos | Some i => i end in
      let i' := match i' with None => dft_pos | Some i => i end in
        match o with
          | None => peq i i' || negb (Regset.mem x live)
          | Some _ => true
        end) n None None x = true.
Proof.
  simpl; auto.
  intros.
  destruct x; auto.
Qed.

Lemma upd_list_some : forall l (g:PTree.t index) G n, 
  (In n l /\ (upd_list l g G) ! n = Some g) \/
  (~ In n l /\ (upd_list l g G) ! n = G !n).
Proof.
  induction l; simpl; intros; auto.
  elim IHl with g (PTree.set a g G) n; intuition.
  rewrite PTree.gsspec in H1; destruct peq; intuition.
Qed.

(** * Properties of [build_phi_block] and [update_ctx] *)

Section fold_left_update_ctx_prop.

Variable code: RTL.code.
Variable preds: PTree.t (list node).
Variable def: PTree.t index.
Variable def_phi: PTree.t (PTree.t index).

Hypothesis pred_hyp2: forall n1 n2 n' ins1 ins2, 
  code!n1 = Some ins1 -> In n' (RTL.successors_instr ins1) -> 
  code!n2 = Some ins2 -> In n' (RTL.successors_instr ins2) -> 
  is_joinpoint preds n' = false -> n1=n2.

Hypothesis pred_hyp3 : forall i j ins,
  code ! i = Some ins ->
  In j (RTL.successors_instr ins) ->
  is_joinpoint  preds j = true ->
  ins = RTL.Inop j.

Ltac kill_error :=
  rewrite fold_left_update_ctx_propagate_error in *; try congruence.

Ltac and_proof :=
  match goal with
    [ |- ?A /\ ?B ] => 
    let h := fresh "Pr" in
      (assert (h:A); [idtac|split; [exact h|and_proof]])
  | _ => idtac
  end.

Ltac new_code_tac :=
match goal with
    |  h:forall i, forall ins, (PTree.set ?x ?ins ?m) ! i = Some ins -> _ |- _ =>
      let H := fresh "Hgss" in 
        (generalize (h _ _ (PTree.gss x ins m)); intros H)
end.

Ltac clean := 
  try new_code_tac;
  repeat 
  match goal with
    | id1: ?a = ?b1, id2: ?a = ?b2 |- _ => rewrite id1 in id2; inv id2
end.

Ltac in_succ_case :=
  match goal with
    id: In ?j (successors_instr ?ins) |- _ => simpl in id; 
      repeat destruct id as [id|id]; subst; try (elim id; fail)
  |  id: In ?j (RTL.successors_instr ?ins) |- _ => simpl in id; 
      repeat destruct id as [id|id]; subst; try (elim id; fail)
  end.

Hint Extern 4 (In _ (successors_instr _)) => simpl.
Hint Extern 4 (In _ (RTL.successors_instr _)) => simpl.

Definition get_dft {A B:Type} (dft:B) (f:A->B) (x:option A) :=
  match x with
    | None => dft
    | Some x => f x
  end.

Inductive is_out_instr : instruction -> Prop:=
| Out_jumptable: forall arg, 
  is_out_instr (Ijumptable arg nil)
| Out_tailcall: forall sig fn args, 
  is_out_instr (Itailcall sig fn args)
| Out_return : forall or,
  is_out_instr (Ireturn or).


Lemma build_phi_block_correct: forall preds live def_phi G phicode pc phicode'
  (EQ:build_phi_block preds live def_phi G (OK phicode) pc = OK phicode'),
  (forall i phi, phicode'!i = Some phi -> (i=pc \/ phicode!i = Some phi)) /\
  (exists phi, phicode'!pc = Some phi) /\
  (forall i phi, phicode!i = Some phi -> phicode'!i = Some phi
    \/ (i=pc /\ phicode!pc <> None)).
Proof.
  unfold build_phi_block; simpl; intros preds0 live def_phi0 G phicode pc phicode'.
  case_eq (preds0!pc); simpl; intros prd Hprd; [idtac|congruence].
  case_eq (def_phi0!pc); simpl; intros df Hdf; [idtac|congruence].
  destruct (@forall_ptree positive).
  intros EQ; inv EQ.
  repeat split.

  intros i phi; rewrite PTree.gsspec; destruct peq; auto.

  rewrite PTree.gss; eauto.

  intros HH i phi; rewrite PTree.gsspec; destruct peq; [subst|auto].
  right; split; congruence.
  congruence.
Qed.

Lemma fold_build_phi_block_some : forall f live def_phi G jpoints phiblock acc,
  fold_left
  (build_phi_block
    (make_predecessors (RTL.fn_code f) RTL.successors_instr) live def_phi G)
  jpoints acc = OK phiblock ->
  exists a, acc = OK a.
Proof.
  induction jpoints; simpl; intros; eauto.
  exploit IHjpoints; eauto.
  intros [a' Ha].
  destruct acc; eauto.
  unfold build_phi_block in Ha.
  destruct (get_option (make_predecessors (RTL.fn_code f) RTL.successors_instr)!a); 
    simpl in Ha; try congruence.
  destruct (def_phi0!a); simpl in Ha; try congruence.
  destruct (@forall_ptree positive); congruence.
Qed.

Lemma fold_build_phi_block_def_phi_same : forall f live def_phi G jpoints phiblock phiblock',
  fold_left
  (build_phi_block
    (make_predecessors (RTL.fn_code f) RTL.successors_instr) live def_phi G)
  jpoints (OK phiblock) = OK phiblock' ->
  forall pc, ~ In pc jpoints -> phiblock!pc = phiblock'!pc.
Proof.
  induction jpoints; simpl; intros.
  inv H; auto.
  exploit fold_build_phi_block_some; eauto; intros [b Hb].
  rewrite Hb in H.
  exploit IHjpoints; eauto; intros Heq; clear IHjpoints H.
  rewrite <- Heq; clear Heq.
  unfold build_phi_block in *.
  destruct ((make_predecessors (RTL.fn_code f) RTL.successors_instr)!a); simpl in *; try congruence.
  destruct (def_phi0!a); simpl in *; try congruence.
  destruct (@forall_ptree positive).
  inv Hb.
  rewrite PTree.gso; auto.
  congruence.
Qed.

Lemma fold_build_phi_block_def_phi_some : forall f live def_phi G jpoints phiblock acc,
  fold_left
  (build_phi_block
    (make_predecessors (RTL.fn_code f) RTL.successors_instr) live def_phi G)
  jpoints acc = OK phiblock ->
  forall pc, In pc jpoints -> exists d, 
    def_phi!pc = Some d /\ 
    forall x i, d!x = Some i -> i<>xH.
Proof.
  induction jpoints; simpl; intros.
  intuition.
  destruct H0; subst; eauto.
  exploit fold_build_phi_block_some; eauto; intros [a Ha].
  unfold build_phi_block in *.
  destruct ((make_predecessors (RTL.fn_code f) RTL.successors_instr)!pc); simpl in *; try congruence.
  destruct (def_phi0!pc); simpl in *; eauto.
  exists t; split; auto.
  case_eq (forall_ptree (fun _ xdef : positive => negb (Peqb 1 xdef)) t); intros Hb.
  red; intros; subst.
  exploit forall_ptree_true; eauto.
  simpl; congruence.
  rewrite Hb in *; congruence.
  congruence.
Qed.

Lemma fold_build_phi_block_value: forall f live def_phi G jpoints phiblock acc,
  fold_left
  (build_phi_block 
    (make_predecessors (RTL.fn_code f) RTL.successors_instr) live def_phi G)
  jpoints acc = OK phiblock -> 
  forall pc pred d, In pc jpoints -> 
    (make_predecessors (RTL.fn_code f) RTL.successors_instr)!pc = Some pred ->
    def_phi!pc = Some d ->
    let live := live pc in 
      let get_Gpreds := 
        (fun pc_pred => 
          match G ! pc_pred with
            | None => (* should not happen *) PTree.empty _
            | Some m => m
          end) in
  let new_phi_block :=
    PTree.fold
      (fun phis x xdef =>
        if Regset.mem x live then
          let phi_args := List.map
            (fun pc => (x,read_gamma (get_Gpreds pc) x)) pred in
            let phi_def := (x,xdef) in
              (Iphi phi_args phi_def)::phis
          else phis
        ) d nil in
      phiblock!pc = Some new_phi_block.
Proof.
  induction jpoints; simpl; intros.
  intuition.
  destruct H0; subst; eauto.
  exploit fold_build_phi_block_some; eauto; intros [a Ha].
  destruct (classic (In pc jpoints)).
  eauto.
  rewrite Ha in H.
  exploit fold_build_phi_block_def_phi_same; eauto; intros Heq.
  rewrite <- Heq; clear IHjpoints; clear Heq.
  unfold build_phi_block in *.
  rewrite H1 in *; simpl in *.
  rewrite H2 in *; simpl in *.
  destruct (@forall_ptree positive).
  destruct acc; inv Ha.
  rewrite PTree.gss; auto.
  congruence.
Qed.

Lemma fold_build_phi_block_correct : forall f live def_phi G jpoints m phicode,
  fold_left
  (build_phi_block
    (make_predecessors (RTL.fn_code f) RTL.successors_instr) live def_phi G)
  jpoints (OK m) = OK phicode ->
  (forall i phi, phicode!i = Some phi -> (In i jpoints) \/ m!i = Some phi) /\
  (forall i, In i jpoints -> exists phi, phicode!i = Some phi) /\
  (forall i phi, m!i = Some phi -> exists phi, phicode!i = Some phi).
Proof.
  intros f live0 def_phi0 G.
  induction jpoints; simpl; intros.
  inv H; intuition.
  eauto.
  exploit fold_build_phi_block_some; eauto; intros [b Hb].
  rewrite Hb in *.
  exploit IHjpoints; eauto; intros [T1 [T2 T3]].
  exploit build_phi_block_correct; eauto; intros [B1 [B2 B3]].
  split.
  intros i phi Hp.
  elim T1 with i phi; auto.
  intros.
  elim B1 with i phi; auto.
  split.
  intros i Hi; intuition; subst; eauto.
  destruct B2; eauto.
  intros i phi HH; intuition.
  exploit B3; eauto.
  destruct 1; eauto.
  destruct H0; subst.
  destruct B2; eauto.
Qed.

Lemma fold_left_update_ctx_prop: forall live
  ppoints G new_code juncpoints G' new_code' juncpoints',
  fold_left (update_ctx  preds def def_phi code live) ppoints 
  (OK (G,new_code,juncpoints)) = OK (G',new_code',juncpoints') ->
  list_norepet ppoints ->
  (forall n1 n2 ins g, 
    G ! n2 = Some g -> 
    In n1 ppoints -> 
    code ! n1 = Some ins ->
    In n2 (RTL.successors_instr ins) ->
    is_joinpoint preds n2 = true) ->
  (forall j gj dphi,
    G!j = Some gj -> 
    is_joinpoint preds j = true ->
    def_phi!j = Some dphi ->
    forall x i, Regset.mem x (live j)=true -> dphi!x = Some i -> read_gamma gj x = i) ->
  (forall i, In i ppoints -> new_code!i = None) ->
  (forall i g, is_joinpoint preds i = true -> G!i = Some g -> In i juncpoints) ->
  (forall n g, G ! n = Some g -> G' ! n = Some g) /\
  (forall i ins, new_code!i = Some ins -> new_code'!i = Some ins) /\
  (forall i, In i ppoints -> 
    get_opt successors_instr (new_code'!i) = get_opt RTL.successors_instr (code!i)) /\
  (forall i, In i ppoints -> 
    get_opt erase_instr (new_code'!i) = get_opt (fun x => x) (code!i)) /\
  (forall i j ins gi gj,
    In i ppoints ->
    new_code'!i = Some ins -> In j (successors_instr ins) ->
    G'!i = Some gi -> G'!j = Some gj -> 
    is_joinpoint preds j = false ->
    wt_instr (read_gamma gi) ins (read_gamma gj)) /\
  (forall i ins gi,
    In i ppoints ->
    new_code'!i = Some ins -> is_out_instr ins ->
    G'!i = Some gi ->
    wt_instr (read_gamma gi) ins (read_gamma gi)) /\
  (forall i j ins gi gj dphi,
    In i ppoints ->
    new_code'!i = Some ins -> In j (successors_instr ins) ->
    G'!i = Some gi -> G'!j = Some gj -> 
    is_joinpoint preds j = true ->
    def_phi!j = Some dphi ->
    (forall x i, dphi!x = Some i -> Regset.mem x (live j)=true -> read_gamma gj x = i) /\
    (forall x, dphi!x = None -> Regset.mem x (live j)=true -> read_gamma gi x = read_gamma gj x)) /\
  (forall i, In i juncpoints' -> In i juncpoints \/ is_joinpoint preds i = true) /\
  (forall i, In i juncpoints -> In i juncpoints') /\
  (forall i j ins, In i ppoints -> 
    code ! i = Some ins ->
    In j (RTL.successors_instr ins) ->
    is_joinpoint preds j = true -> In j juncpoints') /\
  (forall i ins,
    new_code'!i = Some ins -> In i ppoints \/ new_code!i = Some ins) /\
  (forall i ins,
    new_code'!i = Some ins -> 
    new_code!i = Some ins \/
    G'!i <> None /\ 
    wt_eidx  (fun _ => xH) ins /\
    forall j, In j (successors_instr ins) ->
      G'!j <> None)  /\
  (forall i g, is_joinpoint preds i = true -> G'!i = Some g -> In i juncpoints').
Proof.
  induction ppoints; simpl.
  intros G new_code juncpoints G' new_code' juncpoints' H H0 H1.
  repeat split; try (intuition; fail).
  inv H; auto.
  inv H; auto.
  inv H; auto.
  inv H; auto.
  inv H; intuition.
  inv H; intuition.
  inv H; intuition.
  

  intros G new_code juncpoints G' new_code' juncpoints'.
  case_eq (code ! a); [intros ins Hins|intro; simpl; kill_error].
  case_eq (G ! a); [intros g Hg|intro; simpl; kill_error].
  destruct ins; simpl in *.
  case_eq (is_joinpoint  preds n); intros Hj; try kill_error.
  case_eq (def_phi ! n); [intros dphi Hdphi|simpl; intros; kill_error].
  simpl.
  case_eq (G ! n); simpl; [intros g' Hg'|intros Hg'].
  reduce_forall3_ptree.
  (* Inop + is_joinpoint + G!n = Some _ *)
  intros Heq Hln INV1 INV2 INV3 INV4.
  inversion Hln as [|a' l' Hln1 Hln2]; subst; clear Hln.
  elim IHppoints with (1:=Heq) (2:=Hln2); [intros HINV [HINV1 [HINV4 [HINV2 [HINV5 [HINV3 [HINV6 [HINV7 [HINV8 [HINV9 [HINV10 [HINV11 HINV12]]]]]]]]]]]|eauto|eauto|idtac|eauto].
  and_proof; auto.
  intros i ins Hn; eapply HINV1.
  rewrite PTree.gsspec; destruct peq; subst; auto.
  rewrite INV3 in Hn; auto; congruence.

  intros i Hin; destruct Hin; [subst|apply HINV4; auto; fail].   
  rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
  
  intros i Hin; destruct Hin; [subst|apply HINV2; auto; fail].   
  rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.

  
  intros i j ins gi gj Hin Hsucc1 Hsucc2 Hgi Hgj Hjun ; destruct Hin; [subst| try eapply HINV6;eauto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean.
  in_succ_case; clean.

  intros i ins gi Hin Hcode Hout Hgi; destruct Hin; [subst|apply HINV3 with i;auto;fail].
  clean; inv Hout.
  intros i j ins gi gj dpi Hin Hsucc1 Hsucc2 Hgi Hgj Hjun Hdefphi; destruct Hin; [subst|eapply HINV6;eauto;fail].
  assert (G2:G!i=Some g /\ G!n = Some g') by (split; auto).
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean; in_succ_case; clean.
  generalize (@gforall3_ptree _ _ _ (@op_forall3_ptree dphi (live j)) _ _ _ Hforall2); clear Hforall2; intros Hforall2.
  assert (Hforall2':forall x, dphi! x = None -> Regset.mem x (live j) = true -> read_gamma g x = read_gamma g' x).
  { intros x H HT.
    unfold read_gamma, index.
    generalize (Hforall2 x).
    rewrite HT; simpl; rewrite orb_false_r.
    rewrite H.
    destruct (@PTree.get positive x g); destruct (@PTree.get positive x g');
    destruct peq; intros H0; intuition.
  }    
    
  clear Hforall2.
  split; intros.
  destruct G2; exploit (INV2 j); eauto.
  simpl; auto.
  intros i j ins Hin Hsucc1 Hsucc2 Hjun; destruct Hin; [subst|eapply HINV9; eauto; fail].
  clean; in_succ_case; clean.
  apply HINV8.
  eauto.
  intros i ins Hs; elim HINV10 with (1:=Hs); auto.
  rewrite PTree.gsspec; destruct peq; subst; auto.
  intros i ins Hs; elim HINV11 with (1:=Hs); auto.
  rewrite PTree.gsspec; destruct peq; subst; auto.
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  intros Hss; inv Hss; right; repeat split; try congruence; try constructor; intros.
  in_succ_case.
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  congruence.
  intros i Hin; rewrite PTree.gsspec; destruct peq; subst; intuition. 
  (* Inop + is_joinpoint + G!n = None *)
  intros Heq Hln INV1 INV2 INV3 INV4.
  inversion Hln as [|a' l' Hln1 Hln2]; subst; clear Hln.
  elim IHppoints with (1:=Heq) (2:=Hln2); [intros HINV [HINV1 [HINV4 [HINV2 [HINV5 [HINV3 [HINV6 [HINV7 [HINV8 [HINV9 [HINV10 [HINV11 HINV12]]]]]]]]]]]|idtac|idtac|idtac|idtac].
  and_proof; auto.
  intros; eapply HINV; eauto.
  rewrite PTree.gsspec; destruct peq; auto.
  congruence.
  intros i ins Hn; apply HINV1; rewrite PTree.gsspec; destruct peq; subst; auto.
  rewrite INV3 in Hn; auto; congruence.  
  intros i Hin; destruct Hin; [subst|apply HINV4; auto; fail].
  rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
  intros i Hin; destruct Hin; [subst|apply HINV2; auto; fail].
  rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
  
  intros i j ins gi gj Hin Hsucc1 Hsucc2 Hgi Hgj Hjun; destruct Hin; [subst|eapply HINV5;eauto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean.
  in_succ_case; clean.
  intros i ins gi Hin Hcode Hout Hgi; destruct Hin; [subst|apply HINV3 with i;auto;fail].
  clean; inv Hout.
  intros i j ins gi gj dpi Hin Hsucc1 Hsucc2 Hgi Hgj Hjun Hdefphi; destruct Hin; [subst|eapply HINV6;eauto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean; in_succ_case; clean.
  generalize (HINV j); rewrite PTree.gss; clear HINV.
  intros HINV; generalize (HINV _ (refl_equal _)); clear HINV; intros HINV.
  clean.
  assert (forall A l g x,
    ~ In x (List.map (@fst _ A) l) ->
    (fold_left (fun a p => if Regset.mem (fst p) (live j) then PTree.set (fst p) (snd p) a else a) l g) ! x = g ! x).
    induction l; simpl; intros.
    auto.    
    rewrite IHl; auto.
    destruct Regset.mem; auto.
    rewrite PTree.gso; auto.
  assert (forall x (i:index) l g,
    In (x,i) l ->
    Regset.mem x (live j) = true ->
    list_norepet (List.map (@fst _ _) l) ->
    (fold_left (fun a p => if Regset.mem (fst p) (live j) then PTree.set (fst p) (snd p) a else a) l g) ! x = Some i).
    induction l; simpl; intros.
    intuition.
    inv H2.
    destruct H0; subst; simpl in *.    
    rewrite H; try rewrite H1.
    rewrite PTree.gss; auto.
    apply H5.
    auto.
  split; intros.
  rewrite PTree.fold_spec.
  unfold read_gamma; rewrite (H0 x i0); auto.
  apply PTree.elements_correct; auto.
  apply PTree.elements_keys_norepet; auto.
  rewrite PTree.fold_spec.  
  unfold read_gamma; rewrite H; auto.
  red; intros.
  elim list_in_map_inv with (1:= H3).
  intros (x',i'); simpl; destruct 1; subst.
  rewrite (PTree.elements_complete dphi x' i') in H1; congruence.
  intros i Hin; elim HINV7 with i; simpl; intuition.
  subst; auto.
  intros i j ins Hin Hcode1 Hcode2 Hjun; destruct Hin; [subst|eapply HINV9; eauto; fail]. 
  clean; in_succ_case; clean.
  apply HINV8; auto.
  intros i ins Hs; elim HINV10 with (1:=Hs); auto.
  rewrite PTree.gsspec; destruct peq; subst; auto. 
  intros i ins Hs; elim HINV11 with (1:=Hs); auto.
  rewrite PTree.gsspec; destruct peq; subst; auto.
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  intros Hss; inv Hss; right; repeat split; try congruence; try constructor; intros.
  in_succ_case.
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  generalize (HINV _ _ (PTree.gss _ _ _)); congruence.
  (* PO1 *)
  intros; rewrite PTree.gsspec in H; destruct peq; subst; auto.
  eauto.
  (* PO2 *)
  intros j gj dphi0 H H0 H1 x i HR H2.
  rewrite PTree.gsspec in H; destruct peq; [subst|eapply INV2; eauto; fail].
  assert (forall A l g x,
    ~ In x (List.map (@fst _ A) l) ->
    (fold_left (fun a p => if Regset.mem (fst p) (live n) then PTree.set (fst p) (snd p) a else a) l g) ! x = g ! x).
    induction l; simpl; intros.
    auto.
    rewrite IHl; auto.
    clear HR; destruct Regset.mem; auto.
    rewrite PTree.gso; auto.
  assert (forall x (i:index) l g,
    In (x,i) l ->
    Regset.mem x (live n) = true ->
    list_norepet (List.map (@fst _ _) l) ->
    (fold_left (fun a p => if Regset.mem (fst p) (live n) then PTree.set (fst p) (snd p) a else a) l g) ! x = Some i).
    induction l; simpl; intros.
    intuition.
    inv H6.
    destruct H4; subst; simpl in *.
    rewrite H3.
    rewrite H5.
    rewrite PTree.gss; auto.
    apply H9.
    auto.
  inv H.
  rewrite PTree.fold_spec.
  unfold read_gamma; rewrite (H4 x i); auto.
  apply PTree.elements_correct; auto.
  clean; auto.
  apply PTree.elements_keys_norepet; auto.
  (* PO3 *)
  intros; rewrite PTree.gsspec; destruct peq; subst; intuition.
  (* PO4 *)
  intros.
  rewrite PTree.gsspec in H0; destruct peq; subst; simpl; eauto.
  (* Inop + not is_joinpoint *)
  intros Heq Hln INV1 INV2 INV3 INV4.
  inversion Hln as [|a' l' Hln1 Hln2]; subst; clear Hln.
  elim IHppoints with (1:=Heq) (2:=Hln2); [intros HINV [HINV1 [HINV4 [HINV2 [HINV5 [HINV3 [HINV6 [HINV7 [HINV8 [HINV9 [HINV10 [HINV11 HINV12]]]]]]]]]]]|idtac|idtac|idtac|idtac].
  and_proof; auto.
  intros; eapply HINV; eauto.
  rewrite PTree.gsspec; destruct peq; auto.
  subst.
  exploit INV1; eauto.
  simpl; auto.
  intros.
  congruence.
  intros i ins Hn; apply HINV1; rewrite PTree.gsspec; destruct peq; subst; auto.
  rewrite INV3 in Hn; auto; congruence.
  intros i Hin; destruct Hin; [subst|apply HINV4; auto; fail].
  rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
  intros i Hin; destruct Hin; [subst|apply HINV2; auto; fail].  
  rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
  intros i j ins gi gj Hin Hsucc1 Hsucc2 Hgi Hgj Hjun; destruct Hin; [subst|eapply HINV5;eauto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean; in_succ_case; clean.
  rewrite (HINV j g) in Hgj.
  inv Hgj; constructor.
  rewrite PTree.gss; auto.
  intros i ins gi Hin Hcode Hout Hgi; destruct Hin; [subst|apply HINV3 with i;auto;fail].
  clean; inv Hout.
  intros i j ins gi gj dpi Hin Hsucc1 Hsucc2 Hgi Hgj Hjun Hdefphi; destruct Hin; [subst|eapply HINV6;eauto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean; in_succ_case; clean.
  intros i j ins Hin Hsucc1 Hsucc2 Hjun; destruct Hin; [subst|eapply HINV9; eauto; fail].
  clean; in_succ_case; clean. 
  
  intros i ins Hs; elim HINV10 with (1:=Hs); auto.
  rewrite PTree.gsspec; destruct peq; subst; auto. 
  intros i ins Hs; elim HINV11 with (1:=Hs); auto.
  rewrite PTree.gsspec; destruct peq; subst; auto.
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  intros Hss; inv Hss; right; repeat split; try congruence; try constructor; intros.
  in_succ_case.
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  generalize (HINV _ _ (PTree.gss _ _ _)); congruence.
  (* PO1 *)
  intros n1 n2 ins g' T1 T2 T3 T4.
  rewrite PTree.gsspec in T1; destruct peq; subst; auto.
  assert (n1=a).
    eapply pred_hyp2; eauto; simpl; auto.
  subst; clean.
  intuition.
  eauto.
  (* PO2 *)
  intros j gj dphi H H0 H1 x i H2.
  rewrite PTree.gsspec in H; destruct peq; [subst; congruence|eauto].
  (* PO3 *)
  intros; rewrite PTree.gsspec; destruct peq; subst; intuition.
  (* PO4 *)
  intros.
  rewrite PTree.gsspec in H0; destruct peq; subst; simpl; try congruence; eauto.
  (* Iop *)
  case_eq (def ! a); simpl; [intros df Hdef|intro; kill_error].
  case_eq (negb (Peqb 1 df)); [intros Hnp|simpl; kill_error].
  intros Heq Hln INV1 INV2 INV3 INV4.
  inversion Hln as [|a' l' Hln1 Hln2]; subst; clear Hln.  
  elim IHppoints with (1:=Heq) (2:=Hln2); [intros HINV [HINV1 [HINV4 [HINV2 [HINV5 [HINV3 [HINV6 [HINV7 [HINV8 [HINV9 [HINV10 [HINV11 HINV12]]]]]]]]]]]|idtac|idtac|idtac|idtac]; clear Heq.
  and_proof; auto.
  intros; eapply HINV; eauto.
  rewrite PTree.gsspec; destruct peq; auto.
  subst.
  exploit INV1; eauto.
  simpl; auto.
  intros.
  exploit pred_hyp3; eauto.
  simpl; auto.
  congruence.
  intros; apply HINV1; rewrite PTree.gsspec; destruct peq; subst; auto.
  rewrite INV3 in H; auto; congruence.
  intros i Hin; destruct Hin; [subst|apply HINV4; auto; fail].
  rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
  intros i Hin; destruct Hin; [subst|apply HINV2; auto; fail].
  rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
  unfold erase_instr, get_opt ; simpl.
  rewrite map_map_erase with (f:= (read_gamma g)) ; eauto.
  intros i j ins gi gj Hin Hsucc1 Hsucc2 Hgi Hgj Hjun; destruct Hin; [subst|eapply HINV5;eauto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean; in_succ_case; clean.
  replace (read_gamma gj) with (update (read_gamma g) r df).
  constructor.
  intros.
  elim list_in_map_inv with (1:= H); intros x [V1 V2]; subst.
  inv V1; auto.
  auto.
  generalize (HINV _ _ (PTree.gss _ _ _)); intros; clean.
  apply extensionality; unfold update; intros; destruct peq; unfold read_gamma.
  subst; rewrite PTree.gss; auto.
  rewrite PTree.gso; auto.
  intros i ins gi Hin Hcode Hout Hgi; destruct Hin; [subst|apply HINV3 with i;auto;fail].
  clean; inv Hout.
  intros i j ins gi gj dpi Hin Hsucc1 Hsucc2 Hgi Hgj Hjun Hdefphi; destruct Hin; [subst|eapply HINV6;eauto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean; in_succ_case; clean.
  exploit pred_hyp3; eauto; intro T; inv T.
  intros i j ins Hin Hsucc1 Hsucc2 Hjun; destruct Hin; [subst|eapply HINV9; eauto; fail].
  clean; in_succ_case; clean.
  exploit pred_hyp3; eauto; intro T; inv T.
  intros i ins Hs; elim HINV10 with (1:=Hs); auto.
  rewrite PTree.gsspec; destruct peq; subst; auto. 
  intros i ins Hs; elim HINV11 with (1:=Hs); auto.
  rewrite PTree.gsspec; destruct peq; subst; auto.
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  intros Hss; inv Hss; right; repeat split; try congruence; intros.
  econstructor; eauto.
  intros EE; rewrite <- (Peqb_eq xH df) in EE; destruct (Peqb xH df); simpl in *; congruence.
  in_succ_case.
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  generalize (HINV _ _ (PTree.gss _ _ _)); congruence.
  (* PO1 *)
  intros n1 n2 ins g' T1 T2 T3 T4.
  rewrite PTree.gsspec in T1; destruct peq; subst; auto.
  case_eq (is_joinpoint preds n); intros; auto.
  assert (n1=a).
  eapply pred_hyp2; eauto; simpl; auto.
  subst; intuition.
  eauto.
  (* PO2 *)
  intros j gj dphi H H0 H1 x i H2.
  rewrite PTree.gsspec in H; destruct peq; [subst|eauto].
  exploit pred_hyp3; eauto.
  congruence.
  (* PO3 *)
  intros i Hn; rewrite PTree.gsspec; destruct peq; subst; intuition.
  (* PO4 *)
  intros.
  rewrite PTree.gsspec in H0; destruct peq; subst; simpl; try congruence; eauto.
  exploit pred_hyp3; eauto; intro T; inv T.
  (* Iload *)
  case_eq (def ! a); simpl; [intros df Hdef|intro; kill_error].
  case_eq (negb (Peqb 1 df)); [intros Hnp|simpl; kill_error].
  intros Heq Hln INV1 INV2 INV3 INV4.
  inversion Hln as [|a' l' Hln1 Hln2]; subst; clear Hln.
  elim IHppoints with (1:=Heq) (2:=Hln2); [intros HINV [HINV1 [HINV4 [HINV2 [HINV5 [HINV3 [HINV6 [HINV7 [HINV8 [HINV9 [HINV10 [HINV11 HINV12]]]]]]]]]]]|idtac|idtac|idtac|idtac]; clear Heq.
  and_proof; auto.
  intros; eapply HINV; eauto.
  rewrite PTree.gsspec; destruct peq; auto.
  subst.
  exploit INV1; eauto.
  intros.
  exploit pred_hyp3; eauto.
  congruence.
  intros; apply HINV1; rewrite PTree.gsspec; destruct peq; subst; auto.
  rewrite INV3 in H; auto; congruence.
  intros i Hin; destruct Hin; [subst|apply HINV4; auto; fail].
  rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
  intros i Hin; destruct Hin; [subst|apply HINV2; auto; fail].
  rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
  unfold erase_instr, get_opt ; simpl.
  rewrite map_map_erase with (f:= (read_gamma g)) ; eauto.  
  intros i j ins gi gj Hin Hsucc1 Hsucc2 Hgi Hgj Hjun; destruct Hin; [subst|eapply HINV5;eauto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean; in_succ_case; clean.
  replace (read_gamma gj) with (update (read_gamma g) r df).
  constructor.
  intros.
  elim list_in_map_inv with (1:= H); intros x [V1 V2]; subst.
  inv V1; auto.
  auto.
  generalize (HINV _ _ (PTree.gss _ _ _)); intros; clean.
  apply extensionality; unfold update; intros; destruct peq; unfold read_gamma.
  subst; rewrite PTree.gss; auto.
  rewrite PTree.gso; auto.
  intros i ins gi Hin Hcode Hout Hgi; destruct Hin; [subst|apply HINV3 with i;auto;fail].
  clean; inv Hout.
  intros i j ins gi gj dpi Hin Hsucc1 Hsucc2 Hgi Hgj Hjun Hdefphi; destruct Hin; [subst|eapply HINV6;eauto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean; in_succ_case; clean.
  exploit pred_hyp3; eauto; intro T; inv T.
  intros i j ins Hin Hsucc1 Hsucc2 Hjun; destruct Hin; [subst|eapply HINV9; eauto; fail].
  clean; in_succ_case; clean.
  exploit pred_hyp3; eauto; intro T; inv T.
  intros i ins Hs; elim HINV10 with (1:=Hs); auto.
  rewrite PTree.gsspec; destruct peq; subst; auto. 
  intros i ins Hs; elim HINV11 with (1:=Hs); auto.
  rewrite PTree.gsspec; destruct peq; subst; auto.
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  intros Hss; inv Hss; right; repeat split; try congruence; intros.
  econstructor; eauto.
  intros EE; rewrite <- (Peqb_eq xH df) in EE; destruct (Peqb xH df); simpl in *; congruence.
  in_succ_case.
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  generalize (HINV _ _ (PTree.gss _ _ _)); congruence.
  (* PO1 *)
  intros n1 n2 ins g' T1 T2 T3 T4.
  rewrite PTree.gsspec in T1; destruct peq; subst; auto.
  case_eq (is_joinpoint preds n); intros; auto.
  assert (n1=a).
  eapply pred_hyp2; eauto; simpl; auto.
  subst; intuition.
  eauto.
  (* PO2 *)
  intros j gj dphi H H0 H1 x i H2.
  rewrite PTree.gsspec in H; destruct peq; [subst|eauto].
  exploit pred_hyp3; eauto.
  congruence.
  (* PO3 *)
  intros i Hn; rewrite PTree.gsspec; destruct peq; subst; intuition.
  (* PO4 *)
  intros.
  rewrite PTree.gsspec in H0; destruct peq; subst; simpl; try congruence; eauto.
  exploit pred_hyp3; eauto; intro T; inv T.

  (* Istore *)
  intros Heq Hln INV1 INV2 INV3 INV4.
  inversion Hln as [|a' l' Hln1 Hln2]; subst; clear Hln.
  elim IHppoints with (1:=Heq) (2:=Hln2); [intros HINV [HINV1 [HINV4 [HINV2 [HINV5 [HINV3 [HINV6 [HINV7 [HINV8 [HINV9 [HINV10 [HINV11 HINV12]]]]]]]]]]]|idtac|idtac|idtac|idtac]; clear Heq.
  and_proof; auto.
  intros; eapply HINV; eauto.
  rewrite PTree.gsspec; destruct peq; auto.
  subst.
  exploit INV1; eauto.
  intros.
  exploit pred_hyp3; eauto.
  congruence.
  intros; apply HINV1; rewrite PTree.gsspec; destruct peq; subst; auto.
  rewrite INV3 in H; auto; congruence.
  intros i Hin; destruct Hin; [subst|apply HINV4; auto; fail].
  rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
  intros i Hin; destruct Hin; [subst|apply HINV2; auto; fail].
  rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
  unfold erase_instr, get_opt ; simpl.
  rewrite map_map_erase with (f:= (read_gamma g)) ; eauto.
  intros i j ins gi gj Hin Hsucc1 Hsucc2 Hgi Hgj Hjun; destruct Hin; [subst|eapply HINV5;eauto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean; in_succ_case; clean.
  generalize (HINV _ _ (PTree.gss _ _ _)); intros; clean.
  econstructor 8 ; eauto. 
  intros. inv H. congruence.
  elim list_in_map_inv with (1:= H0); intros x [V1 V2]; subst.
  inv V1; auto.
  intros i ins gi Hin Hcode Hout Hgi; destruct Hin; [subst|apply HINV3 with i;auto;fail].
  clean; inv Hout.
  intros i j ins gi gj dpi Hin Hsucc1 Hsucc2 Hgi Hgj Hjun Hdefphi; destruct Hin; [subst|eapply HINV6;eauto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean; in_succ_case; clean.
  exploit pred_hyp3; eauto; intro T; inv T.
  intros i j ins Hin Hsucc1 Hsucc2 Hjun; destruct Hin; [subst|eapply HINV9; eauto; fail].
  clean; in_succ_case; clean.
  exploit pred_hyp3; eauto; intro T; inv T.
  intros i ins Hs; elim HINV10 with (1:=Hs); auto.
  rewrite PTree.gsspec; destruct peq; subst; auto. 
  intros i ins Hs; elim HINV11 with (1:=Hs); auto.
  rewrite PTree.gsspec; destruct peq; subst; auto.
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  intros Hss; inv Hss; right; repeat split; try congruence; try constructor; intros.
  in_succ_case.
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  generalize (HINV _ _ (PTree.gss _ _ _)); congruence.
  (* PO1 *)
  intros n1 n2 ins g' T1 T2 T3 T4.
  rewrite PTree.gsspec in T1; destruct peq; subst; auto.
  case_eq (is_joinpoint preds n); intros; auto.
  assert (n1=a).
  eapply pred_hyp2; eauto; simpl; auto.
  subst; intuition.
  eauto.
  (* PO2 *)
  intros j gj dphi H H0 H1 x i H2.
  rewrite PTree.gsspec in H; destruct peq; [subst|eauto].
  exploit pred_hyp3; eauto.
  congruence.
  (* PO3 *)
  intros i Hn; rewrite PTree.gsspec; destruct peq; subst; intuition.
  (* PO4 *)
  intros.
  rewrite PTree.gsspec in H0; destruct peq; subst; simpl; try congruence; eauto.
  exploit pred_hyp3; eauto; intro T; inv T.

  (* Icall *)
  case_eq (def ! a); simpl; [intros df Hdef|intro; kill_error].
  case_eq (negb (Peqb 1 df)); [intros Hnp|simpl; kill_error].
  intros Heq Hln INV1 INV2 INV3 INV4.
  inversion Hln as [|a' l' Hln1 Hln2]; subst; clear Hln.
  elim IHppoints with (1:=Heq) (2:=Hln2); [intros HINV [HINV1 [HINV4 [HINV2 [HINV5 [HINV3 [HINV6 [HINV7 [HINV8 [HINV9 [HINV10 [HINV11 HINV12]]]]]]]]]]]|idtac|idtac|idtac|idtac]; clear Heq.
  and_proof; auto.
  intros; eapply HINV; eauto.
  rewrite PTree.gsspec; destruct peq; auto.
  subst.
  exploit INV1; eauto.
  intros.
  exploit pred_hyp3; eauto.
  congruence.
  intros; apply HINV1; rewrite PTree.gsspec; destruct peq; subst; auto.
  rewrite INV3 in H; auto; congruence.
  intros i Hin; destruct Hin; [subst|apply HINV4; auto; fail].
  rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
  intros i Hin; destruct Hin; [subst|apply HINV2; auto; fail].
  rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
  unfold erase_instr, get_opt ; simpl.
  rewrite map_map_erase with (f:= (read_gamma g)) ; eauto.
  destruct s0 ; simpl ; eauto.
  intros i j ins gi gj Hin Hsucc1 Hsucc2 Hgi Hgj Hjun; destruct Hin; [subst|eapply HINV5;eauto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean; in_succ_case; clean.
  replace (read_gamma gj) with (update (read_gamma g) r df).
  destruct s0; simpl; econstructor; eauto.
  intros.  inv H ; try congruence.
  elim list_in_map_inv with (1:= H0); intros x [V1 V2]; subst.
  inv V1; auto.
  intros.
  elim list_in_map_inv with (1:= H); intros x [V1 V2]; subst.
  inv V1; auto.
  generalize (HINV _ _ (PTree.gss _ _ _)); intros; clean.
  apply extensionality; unfold update; intros; destruct peq; unfold read_gamma.
  subst; rewrite PTree.gss; auto.
  rewrite PTree.gso; auto.
  intros i ins gi Hin Hcode Hout Hgi; destruct Hin; [subst|apply HINV3 with i;auto;fail].
  clean; inv Hout.
  intros i j ins gi gj dpi Hin Hsucc1 Hsucc2 Hgi Hgj Hjun Hdefphi; destruct Hin; [subst|eapply HINV6;eauto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean; in_succ_case; clean.
  exploit pred_hyp3; eauto; intro T; inv T.
  intros i j ins Hin Hsucc1 Hsucc2 Hjun; destruct Hin; [subst|eapply HINV9; eauto; fail].
  clean; in_succ_case; clean.
  exploit pred_hyp3; eauto; intro T; inv T.
  intros i ins Hs; elim HINV10 with (1:=Hs); auto.
  rewrite PTree.gsspec; destruct peq; subst; auto. 
  intros i ins Hs; elim HINV11 with (1:=Hs); auto.
  rewrite PTree.gsspec; destruct peq; subst; auto.
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  intros Hss; inv Hss; right; repeat split; try congruence; intros.
  econstructor; eauto.
  intros EE; rewrite <- (Peqb_eq xH df) in EE; destruct (Peqb xH df); simpl in *; congruence.
  in_succ_case.
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  generalize (HINV _ _ (PTree.gss _ _ _)); congruence.
  (* PO1 *)
  intros n1 n2 ins g' T1 T2 T3 T4.
  rewrite PTree.gsspec in T1; destruct peq; subst; auto.
  case_eq (is_joinpoint preds n); intros; auto.
  assert (n1=a).
  eapply pred_hyp2; eauto; simpl; auto.
  subst; intuition.
  eauto.
  (* PO2 *)
  intros j gj dphi H H0 H1 x i H2.
  rewrite PTree.gsspec in H; destruct peq; [subst|eauto].
  exploit pred_hyp3; eauto.
  congruence.
  (* PO3 *)
  intros i Hn; rewrite PTree.gsspec; destruct peq; subst; intuition.
  (* PO4 *)
  intros.
  rewrite PTree.gsspec in H0; destruct peq; subst; simpl; try congruence; eauto.
  exploit pred_hyp3; eauto; intro T; inv T.

  (* Itailcall *)
  intros Heq Hln INV1 INV2 INV3 INV4.
  inversion Hln as [|a' l' Hln1 Hln2]; subst; clear Hln.
  elim IHppoints with (1:=Heq) (2:=Hln2); [intros HINV [HINV1 [HINV4 [HINV11 [HINV2 [HINV5 [HINV3 [HINV6 [HINV7 [HINV8 [HINV9 [HINV10 HINV12]]]]]]]]]]]|idtac|idtac|idtac|idtac]; clear Heq.
  and_proof; auto. 

  intros; apply HINV1; rewrite PTree.gsspec; destruct peq; subst; auto.
  
  rewrite INV3 in H; auto; congruence.
  intros i Hin; destruct Hin; [subst|apply HINV4; auto; fail].
  rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
  intros i Hin; destruct Hin; [subst|apply HINV11; auto; fail].
  rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
  unfold erase_instr, get_opt ; simpl.
  rewrite map_map_erase with (f:= (read_gamma g)) ; eauto.
  destruct s0 ; simpl; eauto.

  intros i j ins gi gj Hin Hsucc1 Hsucc2 Hgi Hgj Hjun; destruct Hin; [subst|eapply HINV2;eauto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean; in_succ_case; clean.
  intros i ins gi Hin Hcode Hout Hgi; destruct Hin; [subst|apply HINV5 with i;auto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean.
  destruct s0; unfold map_os ; simpl; econstructor; eauto.
  intros. inv H ; try congruence.
  elim list_in_map_inv with (1:= H0); intros x [V1 V2]; subst.
  inv V1; auto.
  intros.
  elim list_in_map_inv with (1:= H); intros x [V1 V2]; subst.
  inv V1; auto.
  intros i j ins gi gj dpi Hin Hsucc1 Hsucc2 Hgi Hgj Hjun Hdefphi; destruct Hin; [subst|eapply HINV3;eauto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean; in_succ_case; clean.
  intros i j ins Hin Hsucc1 Hsucc2 Hjun; destruct Hin; [subst|eapply HINV8; eauto; fail].
  clean; in_succ_case; clean.
  intros i ins Hs; elim HINV9 with (1:=Hs); auto.
  rewrite PTree.gsspec; destruct peq; subst; auto. 
  intros i ins Hs; elim HINV10 with (1:=Hs); auto.
  rewrite PTree.gsspec; destruct peq; subst; auto.
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  intros Hss; inv Hss; right; repeat split; try congruence; try constructor; intros.
  in_succ_case.
  (* PO1 *)
  intros n1 n2 ins g' T1 T2 T3 T4.
  apply INV1 with n1 ins g'; auto.
  (* PO2 *)
  eauto.
  (* PO3 *)
  intros i Hn; rewrite PTree.gsspec; destruct peq; subst; intuition.
  (* PO4 *)
  eauto.

  (* Ibuiltin *)
  case_eq (def ! a); simpl; [intros df Hdef|intro; kill_error].
  try kill_error.
  case_eq (negb (Peqb 1 df)); [intros Hnp|simpl; kill_error].
  intros Heq Hln INV1 INV2 INV3 INV4.
  inversion Hln as [|a' l' Hln1 Hln2]; subst; clear Hln.
  elim IHppoints with (1:=Heq) (2:=Hln2); [intros HINV [HINV1 [HINV4 [HINV11 [HINV2 [HINV5 [HINV3 [HINV6 [HINV7 [HINV8 [HINV9 [HINV10 HINV12]]]]]]]]]]]|idtac|idtac|idtac|idtac]; clear Heq.
  and_proof; auto.
  intros; eapply HINV; eauto.
  rewrite PTree.gsspec; destruct peq; auto.
  subst.
  exploit INV1; eauto.
  intros.
  exploit pred_hyp3; eauto.
  congruence.
  intros; apply HINV1; rewrite PTree.gsspec; destruct peq; subst; auto.
  rewrite INV3 in H; auto; congruence.
  intros i Hin; destruct Hin; [subst|apply HINV4; auto; fail].
  rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
  intros i Hin; destruct Hin; [subst|apply HINV11; auto; fail].
  rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
  unfold erase_instr, get_opt ; simpl.
  rewrite map_map_erase with (f:= (read_gamma g)) ; eauto.
  
  intros i j ins gi gj Hin Hsucc1 Hsucc2 Hgi Hgj Hjun; destruct Hin; [subst|eapply HINV2;eauto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean; in_succ_case; clean.
  replace (read_gamma gj) with (update (read_gamma g) r df).
  constructor; auto.
  intros.
  elim list_in_map_inv with (1:= H); intros x [V1 V2]; subst.
  inv V1; auto.
  generalize (HINV _ _ (PTree.gss _ _ _)); intros; clean.
  apply extensionality; unfold update; intros; destruct peq; unfold read_gamma.
  subst; rewrite PTree.gss; auto.
  rewrite PTree.gso; auto.
  intros i ins gi Hin Hcode Hout Hgi; destruct Hin; [subst|apply HINV5 with i;auto;fail].
  clean; inv Hout.
  intros i j ins gi gj dpi Hin Hsucc1 Hsucc2 Hgi Hgj Hjun Hdefphi; destruct Hin; [subst|eapply HINV3;eauto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean; in_succ_case; clean.
  exploit pred_hyp3; eauto; intro T; inv T.
  intros i j ins Hin Hsucc1 Hsucc2 Hjun; destruct Hin; [subst|eapply HINV8; eauto; fail].
  clean; in_succ_case; clean.
  exploit pred_hyp3; eauto; intro T; inv T.
  intros i ins Hs; elim HINV9 with (1:=Hs); auto.
  rewrite PTree.gsspec; destruct peq; subst; auto. 
  intros i ins Hs; elim HINV10 with (1:=Hs); auto.
  rewrite PTree.gsspec; destruct peq; subst; auto.
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  intros Hss; inv Hss; right; repeat split; try congruence; intros.
  econstructor; eauto.
  intros EE; rewrite <- (Peqb_eq xH df) in EE; destruct (Peqb xH df); simpl in *; congruence.
  in_succ_case.
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  generalize (HINV _ _ (PTree.gss _ _ _)); congruence.
  (* PO1 *)
  intros n1 n2 ins g' T1 T2 T3 T4.
  rewrite PTree.gsspec in T1; destruct peq; subst; auto.
  case_eq (is_joinpoint preds n); intros; auto.
  assert (n1=a).
  eapply pred_hyp2; eauto; simpl; auto.
  subst; intuition.
  eauto.
  (* PO2 *)
  intros j gj dphi H H0 H1 x i H2.
  rewrite PTree.gsspec in H; destruct peq; [subst|eauto].
  exploit pred_hyp3; eauto.
  congruence.
  (* PO3 *)
  intros i Hn; rewrite PTree.gsspec; destruct peq; subst; intuition.
  (* PO4 *)
  intros.
  rewrite PTree.gsspec in H0; destruct peq; subst; simpl; try congruence; eauto.
  exploit pred_hyp3; eauto; intro T; inv T.

  (* Icond *)
  intros Heq Hln INV1 INV2 INV3 INV4.
  inversion Hln as [|a' l' Hln1 Hln2]; subst; clear Hln.
  elim IHppoints with (1:=Heq) (2:=Hln2); [intros HINV [HINV1 [HINV4 [HINV11 [HINV2 [HINV5 [HINV3 [HINV6 [HINV7 [HINV8 [HINV9 [HINV10 HINV12]]]]]]]]]]]|idtac|idtac|idtac|idtac]; clear Heq.
  and_proof; auto.
  intros; eapply HINV; eauto.
  rewrite PTree.gsspec; destruct peq; auto.
  subst.
  exploit INV1; eauto.
  intros.
  exploit (pred_hyp3 a n0); eauto.
  congruence.
  rewrite PTree.gsspec; destruct peq; auto.
  subst.
  exploit INV1; eauto.
  intros.
  exploit (pred_hyp3 a n); eauto.
  congruence.
  intros; apply HINV1; rewrite PTree.gsspec; destruct peq; subst; auto.
  rewrite INV3 in H; auto; congruence.
  intros i Hin; destruct Hin; [subst|apply HINV4; auto; fail].
  rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
  intros i Hin; destruct Hin; [subst|apply HINV11; auto; fail].
  rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
  unfold erase_instr, get_opt ; simpl.
  rewrite map_map_erase with (f:= (read_gamma g)) ; eauto.
  intros i j ins gi gj Hin Hsucc1 Hsucc2 Hgi Hgj Hjun; destruct Hin; [subst|eapply HINV2;eauto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean; in_succ_case; clean.
  assert (G'!j=Some g).
    apply HINV.
    rewrite PTree.gsspec; destruct peq; auto.
    rewrite PTree.gss; auto.
  clean.
  econstructor; eauto.
  intros.
  elim list_in_map_inv with (1:= H); intros x [V1 V2]; subst.
  inv V1; auto.
  generalize (HINV _ _ (PTree.gss _ _ _)); intros; clean.
  econstructor; eauto.
  intros.
  elim list_in_map_inv with (1:= H); intros x [V1 V2]; subst.
  inv V1; auto.
  intros i ins gi Hin Hcode Hout Hgi; destruct Hin; [subst|apply HINV5 with i;auto;fail].
  clean; inv Hout.
  intros i j ins gi gj dpi Hin Hsucc1 Hsucc2 Hgi Hgj Hjun Hdefphi; destruct Hin; [subst|eapply HINV3;eauto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean; in_succ_case; clean.
  exploit (pred_hyp3 i j); eauto. intro T; inv T.
  exploit (pred_hyp3 i j); eauto; intro T; inv T.
  intros i j ins Hin Hsucc1 Hsucc2 Hjun; destruct Hin; [subst|eapply HINV8; eauto; fail].
  clean; in_succ_case; clean.
  exploit (pred_hyp3 i j); eauto; intro T; inv T.
  exploit (pred_hyp3 i j); eauto; intro T; inv T.
  intros i ins Hs; elim HINV9 with (1:=Hs); auto.
  rewrite PTree.gsspec; destruct peq; subst; auto. 
  intros i ins Hs; elim HINV10 with (1:=Hs); auto.
  rewrite PTree.gsspec; destruct peq; subst; auto.
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  intros Hss; inv Hss; right; repeat split; try congruence; try constructor; intros.
  in_succ_case.
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  rewrite (HINV j g).
  congruence.
  rewrite PTree.gsspec; destruct peq; auto.
  apply PTree.gss; auto.
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  generalize (HINV _ _ (PTree.gss _ _ _)); congruence.
  (* PO1 *)
  intros n1 n2 ins g' T1 T2 T3 T4.
  rewrite PTree.gsspec in T1; destruct peq; subst; auto.
  case_eq (is_joinpoint preds n0); intros; auto.
  assert (n1=a).
  eapply pred_hyp2; eauto; simpl; auto.
  subst; intuition.
  rewrite PTree.gsspec in T1; destruct peq; subst; auto.
  case_eq (is_joinpoint preds n); intros; auto.
  assert (n1=a).
  eapply pred_hyp2; eauto; simpl; auto.
  subst; intuition.
  eauto.
  (* PO2 *)
  intros j gj dphi H H0 H1 x i H2.
  rewrite PTree.gsspec in H; destruct peq; [subst|eauto].
  exploit (pred_hyp3 a n0); eauto.
  congruence.
  rewrite PTree.gsspec in H; destruct peq; [subst|eauto].
  exploit (pred_hyp3 a n); eauto.
  congruence.
  (* PO3 *)
  intros i Hn; rewrite PTree.gsspec; destruct peq; subst; intuition.
  (* PO4 *)
  intros.
  rewrite PTree.gsspec in H0; destruct peq; subst; simpl; try congruence.
  exploit (pred_hyp3 a n0); eauto; intro T; inv T.
  rewrite PTree.gsspec in H0; destruct peq; subst; simpl; eauto.
  exploit (pred_hyp3 a n); eauto; intro T; inv T.

  (* Ijumptable *)
  intros Heq Hln INV1 INV2 INV3 INV4.
  inversion Hln as [|a' l' Hln1 Hln2]; subst; clear Hln.
  elim IHppoints with (1:=Heq) (2:=Hln2); [intros HINV [HINV1 [HINV4 [HINV11 [HINV2 [HINV5 [HINV3 [HINV6 [HINV7 [HINV8 [HINV9 [HINV10 HINV12]]]]]]]]]]]|idtac|idtac|idtac|idtac]; clear Heq.
  and_proof; auto.
  intros; eapply HINV; eauto.
  elim upd_list_some with l g G n; destruct 1; auto.
  exploit INV1; eauto.
  intros.
  exploit (pred_hyp3 a n); eauto.
  congruence.
  rewrite H1; auto.
  intros; apply HINV1; rewrite PTree.gsspec; destruct peq; subst; auto.
  rewrite INV3 in H; auto; congruence.
  intros i Hin; destruct Hin; [subst|apply HINV4; auto; fail].
  rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
  intros i Hin; destruct Hin; [subst|apply HINV11; auto; fail].
  rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.

  intros i j ins gi gj Hin Hsucc1 Hsucc2 Hgi Hgj Hjun; destruct Hin; [subst|eapply HINV2;eauto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean; in_succ_case; clean.
  assert (G'!j=Some g).
    apply HINV.
    elim upd_list_some with l g G j; destruct 1; intuition.
  clean.
  econstructor; eauto.
  intros. inv H ; inv H0 ; auto.
  intros i ins gi Hin Hcode Hout Hgi; destruct Hin; [subst|apply HINV5 with i;auto;fail].
  clean; inv Hout.
  assert (G!i = Some gi).
    simpl in HINV.
    rewrite (HINV _ g) in Hgi; congruence.
  rewrite H in Hg; inv Hg.
  econstructor; eauto.
  intros ; inv H0 ; inv H1 ; auto.

  intros i j ins gi gj dpi Hin Hsucc1 Hsucc2 Hgi Hgj Hjun Hdefphi; destruct Hin; [subst|eapply HINV3;eauto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean; in_succ_case; clean.
  exploit pred_hyp3; eauto; intro T; inv T.
  intros i j ins Hin Hsucc1 Hsucc2 Hjun; destruct Hin; [subst|eapply HINV8; eauto; fail].
  clean; in_succ_case; clean.
  exploit pred_hyp3; eauto; intro T; inv T.
  intros i ins Hs; elim HINV9 with (1:=Hs); auto.
  rewrite PTree.gsspec; destruct peq; subst; auto. 
  intros i ins Hs; elim HINV10 with (1:=Hs); auto.
  rewrite PTree.gsspec; destruct peq; subst; auto.
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  intros Hss; inv Hss; right; repeat split; try congruence; try constructor; intros.
  in_succ_case.
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  rewrite (HINV j g).
  congruence.
  elim upd_list_some with l g G j; destruct 1; intuition.
  (* PO1 *)
  intros n1 n2 ins g' T1 T2 T3 T4.
  elim upd_list_some with l g G n2; destruct 1; auto.
  case_eq (is_joinpoint preds n2); intros; auto.
  assert (n1=a).
  eapply pred_hyp2; eauto; simpl; auto.
  subst; intuition.
  rewrite H0 in *; eauto.
  (* PO2 *)
  intros j gj dphi H H0 H1 x i H2.
  elim upd_list_some with l g G j; destruct 1; auto.
  exploit pred_hyp3; eauto.
  congruence.
  rewrite H4 in *; eauto.
  (* PO3 *)
  intros i Hn; rewrite PTree.gsspec; destruct peq; subst; intuition.
  (* PO4 *)
  intros.
  elim upd_list_some with l g G i; destruct 1; auto.
  exploit pred_hyp3; eauto; intro T; inv T.
  rewrite H2 in H0; eauto.

  (* Ireturn *)
  case_eq o; [intros oa Ho|intros Ho].
  intros Heq Hln INV1 INV2 INV3 INV4.
  inversion Hln as [|a' l' Hln1 Hln2]; subst; clear Hln.
  elim IHppoints with (1:=Heq) (2:=Hln2); [intros HINV [HINV1 [HINV4 [HINV11 [HINV2 [HINV5 [HINV3 [HINV6 [HINV7 [HINV8 [HINV9 [HINV10 HINV12]]]]]]]]]]]|idtac|idtac|idtac|idtac]; clear Heq.
  and_proof; auto.
  intros.
  intros; apply HINV1; rewrite PTree.gsspec; destruct peq; subst; auto.
  rewrite INV3 in H; auto; congruence.
  intros i Hin; destruct Hin; [subst|apply HINV4; auto; fail].
  rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
  intros i Hin; destruct Hin; [subst|apply HINV11; auto; fail].
  rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
  unfold erase_instr, get_opt ; simpl.

  intros i j ins gi gj Hin Hsucc1 Hsucc2 Hgi Hgj Hjun; destruct Hin; [subst|eapply HINV2;eauto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean; in_succ_case; clean.
  intros i ins gi Hin Hcode Hout Hgi; destruct Hin; [subst|apply HINV5 with i;auto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean.
  econstructor; eauto.
  intros. inv H ; inv H0 ; auto.
  intros i j ins gi gj dpi Hin Hsucc1 Hsucc2 Hgi Hgj Hjun Hdefphi; destruct Hin; [subst|eapply HINV3;eauto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean; in_succ_case; clean.
  intros i j ins Hin Hsucc1 Hsucc2 Hjun; destruct Hin; [subst|eapply HINV8; eauto; fail].
  clean; in_succ_case; clean.
  intros i ins Hs; elim HINV9 with (1:=Hs); auto.
  rewrite PTree.gsspec; destruct peq; subst; auto. 
  intros i ins Hs; elim HINV10 with (1:=Hs); auto.
  rewrite PTree.gsspec; destruct peq; subst; auto.
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  intros Hss; inv Hss; right; repeat split; try congruence; try constructor; intros.
  in_succ_case.
  (* PO1 *)
  intros n1 n2 ins g' T1 T2 T3 T4.
  eauto.
  (* PO2 *)
  eauto.
  (* PO3 *)
  intros i Hn; rewrite PTree.gsspec; destruct peq; subst; intuition.
  (* PO4 *)
  intros.
  eauto.

  intros Heq Hln INV1 INV2 INV3 INV4.
  inversion Hln as [|a' l' Hln1 Hln2]; subst; clear Hln.
  elim IHppoints with (1:=Heq) (2:=Hln2); [intros HINV [HINV1 [HINV4 [HINV11 [HINV2 [HINV5 [HINV3 [HINV6 [HINV7 [HINV8 [HINV9 [HINV10 HINV12]]]]]]]]]]]|idtac|idtac|idtac|idtac]; clear Heq.
  and_proof; auto.
  intros.
  intros; apply HINV1; rewrite PTree.gsspec; destruct peq; subst; auto.
  rewrite INV3 in H; auto; congruence.
  intros i Hin; destruct Hin; [subst|apply HINV4; auto; fail].
  rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
  intros i Hin; destruct Hin; [subst|apply HINV11; auto; fail].
  rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
  unfold erase_instr, get_opt ; simpl.
  intros i j ins gi gj Hin Hsucc1 Hsucc2 Hgi Hgj Hjun; destruct Hin; [subst|eapply HINV2;eauto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean; in_succ_case; clean.
  intros i ins gi Hin Hcode Hout Hgi; destruct Hin; [subst|apply HINV5 with i;auto;fail].
  clean.
  econstructor; auto.
  intros i j ins gi gj dpi Hin Hsucc1 Hsucc2 Hgi Hgj Hjun Hdefphi; destruct Hin; [subst|eapply HINV3;eauto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean; in_succ_case; clean.
  intros i j ins Hin Hsucc1 Hsucc2 Hjun; destruct Hin; [subst|eapply HINV8; eauto; fail].
  clean; in_succ_case; clean.
  intros i ins Hs; elim HINV9 with (1:=Hs); auto.
  rewrite PTree.gsspec; destruct peq; subst; auto. 
  intros i ins Hs; elim HINV10 with (1:=Hs); auto.
  rewrite PTree.gsspec; destruct peq; subst; auto.
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  intros Hss; inv Hss; right; repeat split; try congruence; try constructor; intros.
  in_succ_case.
  (* PO1 *)
  intros n1 n2 ins g' T1 T2 T3 T4.
  eauto.
  (* PO2 *)
  eauto.
  (* PO3 *)
  intros i Hn; rewrite PTree.gsspec; destruct peq; subst; intuition.
  (* PO4 *)
  eauto.
Qed.

End fold_left_update_ctx_prop.


(** * Properties about [normalised_function] *)
Lemma normalised_entry_not_successor : forall f ins i,
  normalised_function f ->
  (RTL.fn_code f)!i = Some ins ->
  In (RTL.fn_entrypoint f) (RTL.successors_instr ins) -> False.
Proof.
  unfold normalised_function; intros.
  exploit check_function_inv_correct01; eauto.
Qed.

Lemma normalised_entry_not_joinpoint : forall f,
  normalised_function f ->
  ~ is_joinpoint (make_predecessors (RTL.fn_code f) RTL.successors_instr) (RTL.fn_entrypoint f) = true.
Proof.
  red; unfold normalised_function; intros.
  exploit check_function_inv_correct12; eauto.
  rewrite is_joinpoint_iff_join_point; auto.
Qed.

Lemma assigned_fold_Iphi_map : forall (pred:list node) (live:Registers.reg->bool) f g (d:PTree.t index)
  args dst,
  In (Iphi args dst)
  (PTree.fold
    (fun phis x xdef =>
      if live x
        then Iphi (map (f x) pred) (g x xdef) :: phis
        else phis) d nil) -> 
  exists x, exists xdef, d!x = Some xdef /\
    args = map (f x) pred /\ dst = g x xdef /\ live x = true
.
Proof.
  intros pred live f g d.
  apply (@PTree_Properties.fold_rec _ _ 
    (fun phis x xdef =>
      if live x
        then Iphi (map (f x) pred) (g x xdef) :: phis
        else phis)
    (fun d phis => forall args dst,
      In (Iphi args dst) phis -> 
      exists x, exists xdef, d!x = Some xdef /\
        args = map (f x) pred /\ dst = g x xdef /\ live x = true) nil d).
  intros m m' phis He H args dst Hi.
  elim H with (1:=Hi); intros x [xdef [Hx1 Hx2]].
  rewrite He in Hx1; eauto.
  simpl; intuition.
  intros m a k v Hm1 Hm2 Hm3 args dst.
  case_eq (live k); intros.
  simpl in H0; destruct H0.
  inv H0.
  exists k; exists v.
  rewrite PTree.gss; auto.
  elim Hm3 with (1:=H0); intros x [xdef [Hx1 Hx2]].
  exists x; exists xdef; split; auto.
  rewrite PTree.gso; auto.
  intro; congruence.
  elim Hm3 with (1:=H0); intros x [xdef [Hx1 Hx2]].
  exists x; exists xdef; split; auto.
  rewrite PTree.gso; auto.
  intro; congruence.
Qed.

Lemma assigned_fold_Iphi_map2 : forall (pred:list node) (live:Registers.reg->bool) f g (d:PTree.t index)
  x xdef,
  d!x = Some xdef -> live x = true ->
  In (Iphi (map (f x) pred) (g x xdef))
  (PTree.fold
    (fun phis x xdef =>
      if live x
        then Iphi (map (f x) pred) (g x xdef) :: phis
        else phis) d nil).
Proof.
  intros pred live f g d.
  apply (@PTree_Properties.fold_rec _ _ 
    (fun phis x xdef =>
      if live x
        then Iphi (map (f x) pred) (g x xdef) :: phis
        else phis)
    (fun d phis => forall x xdef,
      d!x = Some xdef -> live x = true ->
      In (Iphi (map (f x) pred) (g x xdef)) phis)).
  intros m m' phis He H args dst Hi.
  rewrite <- He in Hi; eauto.
  intros; rewrite PTree.gempty in *; congruence.
  intros m a k v Hm1 Hm2 Hm3 x xdef.
  case_eq (live k); intros.
  rewrite PTree.gsspec in H0; destruct peq; subst.
  left; congruence.
  right; eauto.
  rewrite PTree.gso in H0; eauto.
  intro; congruence.
Qed.


Lemma In_Iphi_fold1: forall (l:list positive) f (g:positive->bool) args dst d1 d2,
  In (Iphi args dst)
  (PTree.fold
    (fun phis (x xdef:positive) =>
      if g x then Iphi (map (f x) l) (x, xdef) :: phis
        else phis) d1 d2) -> length l = length args \/ In (Iphi args dst) d2.
Proof.
  intros l f g args dst d1 d2.
  apply PTree_Properties.fold_rec with
    (P:=fun m d3 => In (Iphi args dst) d3 -> length l = length args \/ In (Iphi args dst) d2); auto.
  intros.
  destruct (g k); auto.
  destruct H2; auto.
  inv H2; left.
  rewrite list_length_map; auto.
Qed.

Lemma In_Iphi_fold1': forall (l:list positive) f (g:positive->bool) args dst d1,
  In (Iphi args dst)
  (PTree.fold
    (fun phis (x xdef:positive) =>
      if g x then Iphi (map (f x) l) (x, xdef) :: phis
        else phis) d1 nil) -> length l = length args.
Proof.
  intros.
  exploit In_Iphi_fold1; eauto.
  destruct 1; auto.
  elim H0.
Qed.

Lemma In_Iphi_fold2: forall (l:list positive) f (g:positive->bool) args dst d1,
  In (Iphi args dst)
  (PTree.fold
    (fun phis (x xdef:positive) =>
      if g x then Iphi (map (f x) l) (x, xdef) :: phis
        else phis) d1 nil) -> 
  forall k, nth_okp k l -> nth_okp k args.
Proof.
  intros.
  exploit In_Iphi_fold1; eauto.
  destruct 1; auto.
  eapply nth_okp_length; eauto.
  inv H1.
Qed.

Lemma In_Iphi_fold3: forall (l:list positive) f (g:positive->bool) args dst arg d1 d2,
  In (Iphi args dst)
  (PTree.fold
    (fun phis (x xdef:positive) =>
      if g x then Iphi (map (fun pc => (x,f x pc)) l) (x, xdef) :: phis
        else phis) d1 d2) ->
  In arg args -> fst arg = fst dst \/ In (Iphi args dst) d2.
Proof.
  intros l f g args dst arg d1 d2.
  apply PTree_Properties.fold_rec with (P:=fun m d3 =>
    In (Iphi args dst) d3 ->
    In arg args -> fst arg = fst dst \/ In (Iphi args dst) d2); auto.
  intros.
  destruct (g k); auto.
  simpl in H2; destruct H2; auto.
  inv H2; simpl.
  left; clear H1.
  elim list_in_map_inv with (1:=H3); intros p [P1 P2]; subst.
  auto.
Qed.

Lemma In_Iphi_fold4: forall (l:list positive) f (g:positive->bool) args dst dst' args' d1 d2,
    In (Iphi args dst)
    (fold_left
      (fun phis x =>
        if g (fst x) then Iphi (map (fun pc => (fst x,f (fst x) pc)) l) (fst x,snd x) :: phis
          else phis) d1 d2) ->
    In (Iphi args' dst')
    (fold_left
      (fun phis x =>
        if g (fst x) then Iphi (map (fun pc => (fst x,f (fst x) pc)) l) (fst x,snd x) :: phis
          else phis) d1 d2) ->
    (forall args dst args' dst', In (Iphi args dst) d2 -> In (Iphi args' dst') d2 -> fst dst = fst dst' -> dst = dst' /\ args=args') ->
    (forall args dst , In (Iphi args dst) d2 -> ~ In (fst dst) (List.map (@fst _ _) d1)) ->
    list_norepet (List.map (@fst _ _) d1) ->
    fst dst = fst dst' -> dst = dst' /\ args = args'.
Proof.
  induction d1; simpl; intros.
  eauto.
  inv H3.
  eapply IHd1; eauto.
  intros.
  destruct (g (fst a)); eauto.
  simpl in *; destruct H3; destruct H5.
  inv H3; inv H5; auto.
  inv H3.
  elim (H2 _ _ H5); auto.
  inv H5.
  elim (H2 _ _ H3); auto.
  eauto.

  intros.
  destruct (g (fst a)).
  simpl in H3; destruct H3.
  inv H3; auto.
  intro; elim H2 with (1:=H3); auto.
  intro; elim H2 with (1:=H3); auto.
Qed.

Lemma In_Iphi_fold5: forall (l:list positive) f (g:positive->bool) args dst dst' args' d1,
    In (Iphi args dst)
    (PTree.fold
      (fun phis (x xdef:positive) =>
        if g x then Iphi (map (fun pc => (x,f x pc)) l) (x, xdef) :: phis
          else phis) d1 nil) ->
    In (Iphi args' dst')
    (PTree.fold
      (fun phis (x xdef:positive) =>
        if g x then Iphi (map (fun pc => (x,f x pc)) l) (x, xdef) :: phis
          else phis) d1 nil) ->
    fst dst = fst dst' -> dst = dst' /\ args = args'.
Proof.
  intros l f g args dst dst' args' d1.
  rewrite PTree.fold_spec; intros.
  eapply (In_Iphi_fold4 l f g) with (1:=H) (2:=H0); eauto.
  intros.
  elim H2.
  apply PTree.elements_keys_norepet.
Qed.

Lemma In_Iphi_fold6: forall (l:list positive) f (g:positive->bool) d1,
    para_block
    (PTree.fold
      (fun phis (x xdef:positive) =>
        if g x then Iphi (map (fun pc => (x,f x pc)) l) (x, xdef) :: phis
          else phis) d1 nil).
Proof.
  intros l f g d1 dst args arg H1 H2 H3 args' H4.
  elim H3; clear H3.
  apply (In_Iphi_fold5 _ _ _ _ _ _ _ _ H1 H4).
  elim In_Iphi_fold3 with (1:=H1) (2:=H2); eauto.
  intros T; elim T.
Qed.

Lemma In_Iphi_fold7: forall (l:list positive) f (g:positive->bool) d1 args dst args' dst',
    In (Iphi args dst) (PTree.fold
      (fun phis (x xdef:positive) =>
        if g x then Iphi (map (fun pc => (x,f x pc)) l) (x, xdef) :: phis
          else phis) d1 nil) -> 
    In (Iphi args' dst') (PTree.fold
      (fun phis (x xdef:positive) =>
        if g x then Iphi (map (fun pc => (x,f x pc)) l) (x, xdef) :: phis
          else phis) d1 nil) ->
    (args <> args' \/ dst <> dst') ->
    (erase_reg dst) <> (erase_reg dst').
Proof.
  intros; intro.
  destruct dst; destruct dst'; simpl in *.
  elim (In_Iphi_fold5 _ _ _ _ _ _ _ _ H H0); auto.
  destruct H1; intuition.
Qed.

Lemma aux_same_succ : forall l rtl_code code,
  (∀ (j : positive) (ins : RTL.instruction),
         rtl_code ! j = Some ins → In j l) ->
  (∀ i : node,
       In i l
       → get_opt successors_instr code ! i =
         get_opt RTL.successors_instr rtl_code ! i) ->
  (∀ (i : positive) (ins : instruction),
       code ! i = Some ins
       → In i l ∨ (PTree.empty instruction) ! i = Some ins) ->
  forall i:node, 
    (PTree.map1 RTL.successors_instr rtl_code)!i = 
    (PTree.map1 successors_instr code)!i.
Proof.
  intros l rtl_code code T H1 H9 i1.
  repeat rewrite PTree.gmap1.
  case_eq (rtl_code!i1); intros.
  - exploit (H1 i1).
    eapply T; eauto.
    rewrite H.
    simpl.
    destruct (code!i1); simpl; auto.
  - case_eq (code!i1); intros.
    * simpl in *.
      exploit H9; eauto.
      destruct 1.
      exploit (H1 i1) ;eauto.
      rewrite H; rewrite H0; simpl; try congruence.
      rewrite PTree.gempty in *; congruence.
    * auto.
Qed.



(** * The typechercker [typecheck_function] satisfies his specification *)
Theorem typecheck_function_correct : forall f size def def_phi live f_ssa,
  True ->
  (forall j ins, (RTL.fn_code f)!j = Some ins -> In j (fn_dfs f)) ->
  list_norepet (fn_dfs f) ->
  typecheck_function f size def def_phi (fun pc => (Lin f pc (Lout live))) = OK f_ssa ->
  exists G, wt_function f f_ssa live G /\ wf_init f_ssa G /\ check_erased_spec f f_ssa /\ normalised_function f 
   /\ (check_phi_params_spec f_ssa /\ check_para_block_spec f_ssa /\ check_no_duplicates_spec f_ssa)
   /\ (forall pc block, (fn_phicode f_ssa) ! pc = Some block ->  exists ins, (fn_code f_ssa) ! pc = Some ins)
   /\ (forall pc, RTLutils.join_point pc f <-> join_point pc f_ssa)
   /\ (forall phib jp i, (fn_code f_ssa) ! jp = Some i
                         -> (fn_phicode f_ssa) ! jp = Some phib
                         -> join_point jp f_ssa)
   /\ (forall phib jp, (fn_phicode f_ssa) ! jp = Some phib ->
       forall args dst, In (Iphi args dst) phib -> length args = length ((make_predecessors (fn_code f_ssa) successors_instr) !!! jp))
   /\ (forall phib jp i, f_ssa.(fn_code) ! jp = Some i -> f_ssa.(fn_phicode) ! jp = Some phib -> join_point jp f_ssa)
   /\ (  forall jp i, join_point jp f_ssa ->  f_ssa.(fn_code) ! jp = Some i -> 
             exists phib, f_ssa.(fn_phicode) ! jp = Some phib)
   /\ (forall i, get_opt erase_instr ((f_ssa.(fn_code))!i) = get_opt (fun x => x) ((f.(RTL.fn_code))!i))
.
Proof.
  unfold typecheck_function; intros f size def def_phi live f_ssa.
  
  case_eq (check_function_inv f (make_predecessors (RTL.fn_code f) RTL.successors_instr)); intros Hcheck; try congruence.
  assert (Hnl:normalised_function f).
    apply Hcheck.
  match goal with |- context[fold_left ?f ?l ?x] => 
    case_eq (fold_left f l x); 
    [intros ((G,new_code),jpoints) Hf|simpl; intros; congruence]
  end.
  match goal with |- context[fold_left ?f ?l ?x] => 
    case_eq (fold_left f l x); simpl;
    [intros phiblock Hphi|intros; congruence]
  end.
  match goal with |- context[check_unique_def ?x] => 
    case_eq (check_unique_def x); simpl;
    [intros Hcu|intros; congruence]
  end.
  match goal with |- context[check_code_at_phipoints ?x] => 
    case_eq (check_code_at_phipoints x); simpl;
    [intros Hcap|intros; congruence]
  end.
  intros _ Hdf1 Hdfs Hok.  
  inv Hok; simpl in *.
  exploit fold_left_update_ctx_prop; eauto.
  
  intros n1 n2 n' ins1 ins2 H H0 H1 H2 H3.
  assert (~ RTLutils.join_point n' f).
    intro.
    rewrite is_joinpoint_iff_join_point in H4.
    congruence.
  destruct (peq n1 n2); auto.
  elim H4; clear H4 H3.
  assert (In n' ((RTL.successors_map f) !!! n1)).
    unfold successors_list.
    unfold RTL.successors_map; rewrite PTree.gmap1; rewrite H; simpl; auto.
  assert (In n' ((RTL.successors_map f) !!! n2)).
    unfold successors_list.
    unfold RTL.successors_map; rewrite PTree.gmap1; rewrite H1; simpl; auto.
  exploit @make_predecessors_correct_1; eauto. 
  generalize H1 ; clear H1.
  exploit @make_predecessors_correct_1; eauto. 
  intros T3 H1 T4.
  unfold successors_list in *.
  case_eq ((make_predecessors (RTL.fn_code f) RTL.successors_instr)!n'); intros.
  rewrite H5 in *.
  econstructor; eauto.
  destruct l; simpl in *.
  intuition.
  destruct l; simpl in *.
  intuition subst.
  intuition.
  simpl; omega.
  rewrite H5 in *.
  elim T3.

  intros i j ins Hp Hp0 Hp1.
  rewrite <- is_joinpoint_iff_join_point in Hp1.
  assert (In j (RTL.successors_map f) !!! i).
    unfold successors_list.
    unfold RTL.successors_map; rewrite PTree.gmap1; rewrite Hp; simpl; auto.    
  exploit check_function_inv_correct0; eauto.
  intros [ins' Hi'].
  rewrite (check_function_inv_correct3 _ Hnl _ _ ins' Hp1 H) in Hp; auto.
  congruence.

  intros n1 n2 ins g Hsome Hin Hsucc1 Hsucc2.
  unfold entry_Gamma in *.
  rewrite PTree.gsspec in Hsome; destruct peq; subst.
  elim normalised_entry_not_successor with f ins n1; auto.
  rewrite PTree.gempty in *; congruence.

  intros j gj dphi Hsucc1 Hjun Hd x i Hx.
  unfold entry_Gamma in *.
  rewrite PTree.gsspec in Hsucc1; destruct peq; subst.
  elim normalised_entry_not_joinpoint with f; auto.
  intros.
  rewrite PTree.gempty in *; congruence.
  intros; rewrite PTree.gempty in *; congruence.

  intros i g Hj Hsome.
  unfold entry_Gamma in *.
  rewrite PTree.gsspec in Hsome; destruct peq; subst.
  elim normalised_entry_not_joinpoint with f; auto.
  rewrite PTree.gempty in *; congruence.

  intros [H [H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 H11]]]]]]]]]]]].
  simpl.
  exists (fun n => match G!n with None => fun _ => xH | Some g => read_gamma g end); split. 
  constructor; simpl; intros.
  inv H12; simpl in *.
  elim H10 with i instr; auto.
  rewrite PTree.gempty; congruence.
  intros [T1 [T3 T2]]; generalize (T2 _ H14); clear T2; intros T2.
  assert (HI: In i (fn_dfs f)).
    elim H9 with i instr; auto.
    rewrite PTree.gempty; congruence.
  assert (He: exists ins', (RTL.fn_code f)!i = Some ins').
    exploit H1; eauto.
    rewrite H13; simpl.
    case_eq ((RTL.fn_code f)!i); simpl.
    intros ins0; exists ins0; auto.
    congruence.    
  destruct He as [instr' He].
  case_eq (is_joinpoint (make_predecessors (RTL.fn_code f) RTL.successors_instr) j); intros Hj.
  exploit (H8 i j instr'); eauto.
  exploit H1; eauto.
  rewrite H13; rewrite He; simpl; intros.
  inv H12; auto.
  intros HInj.
  exploit fold_build_phi_block_correct; eauto; intros [_ [HT _]].
  elim HT with j; auto; intros phi Hphi0.
  econstructor 2; eauto.
  econstructor 1; simpl; eauto.
  simpl.

  (* wt_eidx *)
  assert (HG: (entry_Gamma f) ! (RTL.fn_entrypoint f) = Some (PTree.empty index)).
    unfold entry_Gamma.
    rewrite PTree.gss; auto.    
  rewrite (H _ _ HG).
  replace (read_gamma (PTree.empty index)) with (fun _ : Registers.reg => 1%positive); auto.
  apply extensionality.
    intros; unfold read_gamma; simpl; rewrite PTree.gempty; auto.
  (* wt_ephi *) 
  case_eq (G!i); [intros gi Hgi| intuition;fail].
  case_eq (G!j); [intros gj Hgj| intuition;fail].
  exploit fold_build_phi_block_def_phi_some; eauto; intros [d [Hd Hd2]]; eauto.
  simpl.
  assert (HG: (entry_Gamma f) ! (RTL.fn_entrypoint f) = Some (PTree.empty index)).
    unfold entry_Gamma.
    rewrite PTree.gss; auto.    
  rewrite (H _ _ HG).
  replace (read_gamma (PTree.empty index)) with (fun _ : Registers.reg => 1%positive).
  case_eq ((make_predecessors (RTL.fn_code f) RTL.successors_instr) ! j); eauto.
  intros pred Hpred.
  exploit fold_build_phi_block_value; eauto.
  rewrite Hphi0; intros T.
  inv T.
  constructor.
  intros ri' r i' Has.
  inv Has.
  destruct (assigned_fold_Iphi_map _ _ _ _ _ _ _ H12) as [r' [idx [R1 [R2 [R3 R4]]]]].
  intros; subst.
  inv H15.
  generalize (Hd2 _ _ R1); auto.
  unfold is_joinpoint in *.
  intros T; rewrite T in *; congruence.
  apply extensionality.
    intros; unfold read_gamma; simpl; rewrite PTree.gempty; auto.

  simpl; constructor; simpl.
    case_eq (G!i); [intros gi Hgi| intuition;fail].
    case_eq (G!j); [intros gj Hgj| intuition;fail].
    exploit fold_build_phi_block_def_phi_some; eauto; intros [d [Hd _]]; eauto.
    exploit H5; eauto; intros [T4 _].
    unfold is_joinpoint in *.
    case_eq ((make_predecessors (RTL.fn_code f) RTL.successors_instr) ! j); eauto.
    intros pred Hpred.
    exploit fold_build_phi_block_value; eauto.
    rewrite Hphi0; intros T.
    inv T.
    intros ri' r i' Has.
    inv Has.
    destruct (assigned_fold_Iphi_map _ _ _ _ _ _ _ H12) as [r' [idx [R1 [R2 [R3 R4]]]]].
    subst; clear H12.
    intros T; inv T.
    eauto.
    intros Hjunc.
    rewrite Hjunc in *; congruence.

    intros ri r i0 Ha Hb.    
    destruct Ha as [x X].
    case_eq ((make_predecessors (RTL.fn_code f) RTL.successors_instr) ! j); 
      [intros pred Hpred| intros Hpred; unfold is_joinpoint in Hj; rewrite Hpred in Hj; congruence].
    exploit fold_build_phi_block_def_phi_some; eauto; intros [d [Hd _]]; eauto.
    exploit fold_build_phi_block_value; eauto.
    intros Hp; rewrite Hphi0 in Hp; inv Hp.
    destruct (assigned_fold_Iphi_map _ _ _ _ _ _ _ X) as [x' [xdef [D1 [D2 [D3 D4]]]]]; subst.
    inv D3.
    apply Regset.mem_2; auto.
    
  intros r Hri.
    case_eq (G!i); [intros gi Hgi| intuition;fail].
    case_eq (G!j); [intros gj Hgj| intuition;fail].
    exploit fold_build_phi_block_def_phi_some; eauto; intros [d [Hd _]]; eauto.
    exploit H5; eauto; intros [_ T4].
    unfold is_joinpoint in *.
    case_eq ((make_predecessors (RTL.fn_code f) RTL.successors_instr) ! j); eauto.
    intros pred Hpred.
    exploit fold_build_phi_block_value; eauto.
    rewrite Hphi0; intros T.
    inv T.
    unfold assigned in Hri.
    case_eq (Regset.mem r (Lin f j (Lout live))); intros Hrm; [left|right].
    symmetry; apply T4; auto.
    case_eq (d!r); auto; intros rdef Hrdef.
    elim Hri with ((r,rdef)) rdef.
    auto.
    econstructor; apply assigned_fold_Iphi_map2 with
      (f:=fun x pc => (x, read_gamma
                    match G ! pc with
                    | Some m => m
                    | None => PTree.empty index
                    end x))
      (g:=fun x xdef => ((x, xdef))); eauto.
  intros Ti; exploit Regset.mem_1; eauto.
  intros; congruence.
  intros Hjj; rewrite Hjj in Hj; congruence.

  constructor; simpl.
  intros args dst r i0 Hi Hb.
    set (ff:={|
     fn_sig := RTL.fn_sig f;
     fn_params := map (fun r0 => (r0, dft_pos))
                    (RTL.fn_params f);
     fn_stacksize := RTL.fn_stacksize f;
     fn_code := new_code;
     fn_phicode := phiblock;
     fn_max_indice := size;
     fn_entrypoint := RTL.fn_entrypoint f
      |}).
    exploit fold_build_phi_block_def_phi_some; eauto; intros [d [Hd _]]; eauto.
    unfold is_joinpoint in *.
    case_eq ((make_predecessors (RTL.fn_code f) RTL.successors_instr) ! j); eauto.
    intros pred Hpred.
    exploit fold_build_phi_block_value; eauto.
    rewrite Hphi0; intros T; inv T.
    destruct (assigned_fold_Iphi_map _ _ _ _ _ _ _ Hi) as [r' [idx [R1 [R2 [R3 R4]]]]].
    subst; clear Hi.
    inv R3.
    assert (forall i, (RTL.successors_map f) !i = (successors ff) !i)
           by (eapply aux_same_succ; eauto).
    replace ((make_predecessors new_code successors_instr) !!!j) with pred.
    clear Hpred Hphi0; induction pred; simpl; constructor; auto.
    econstructor; split; [idtac|reflexivity].

    destruct (G!a); simpl; auto.
    unfold read_gamma.
    rewrite PTree.gempty; auto. 
    { unfold successors_list.
      erewrite <- (same_successors_same_predecessors _ _ (RTL.fn_code f) new_code); 
        eauto.
      rewrite Hpred; auto.
    }
    intros T; rewrite T in *; congruence.

  constructor 1 with instr; simpl; auto.
  constructor 1 with instr; simpl; auto.
  assert (Ni:~ In j jpoints).
    intro T; elim (H6 _ T); auto; congruence.
  case_eq (phiblock!j); auto; intros phi Hphi1.
  exploit fold_build_phi_block_correct; eauto.
  intros [T _].
  exploit T; eauto; rewrite PTree.gempty.
  destruct 1; intuition; congruence.
  (* wt_eidx. *)
  assert (HG: (entry_Gamma f) ! (RTL.fn_entrypoint f) = Some (PTree.empty index)).
    unfold entry_Gamma.
    rewrite PTree.gss; auto.    
  rewrite (H _ _ HG).
  replace (read_gamma (PTree.empty index)) with (fun _ : Registers.reg => 1%positive); auto.
  apply extensionality.
    intros; unfold read_gamma; simpl; rewrite PTree.gempty; auto.

 (* wt_instr *)
  case_eq (G!i); [intros gi Hgi| intuition;fail].
  case_eq (G!j); [intros gj Hgj| intuition;fail].
  exploit H2; eauto.

  assert (Hi:exists instr, new_code!i = Some instr).
    inv H12; simpl in *; eauto.
  destruct Hi as [instrs Hi].
  econstructor; eauto.
  exploit H10; eauto; rewrite PTree.gempty; destruct 1; try congruence.
  destruct H13 as [G1 [G2 G3]].
  case_eq (G!i); [intros gi Hgi| intuition;fail].
  exploit H4; eauto.
  exploit H9; eauto; rewrite PTree.gempty; destruct 1; auto; congruence.
  inv H12 ; simpl in H13; rewrite Hi in H13 ; inv H13; econstructor; eauto.

  (** wf_init **)
  assert (HG: (entry_Gamma f) ! (RTL.fn_entrypoint f) = Some (PTree.empty index)).
    unfold entry_Gamma.
    rewrite PTree.gss; auto.

  split.
  constructor; simpl; intros.
  rewrite (H _ _ HG).
  exploit list_in_map_inv; eauto; simpl; intros [r [Hr1 Hr2]]; subst.
  exists r.
  unfold read_gamma; simpl; rewrite PTree.gempty; auto.

  split.
  constructor; simpl; auto.
  rewrite map_map; simpl.
  assert (forall l: list Registers.reg, l = map (fun x => x) l).
    induction l; simpl; congruence.
  apply H12.
  unfold erase_code; simpl.
  intros ; intuition.
  rewrite PTree.gmap ; eauto.
  case_eq (RTL.fn_code f) ! p; intros.
  exploit Hdf1 ; eauto. intros.   
  exploit H2 ; eauto.
  intros. rewrite H12 in * ; simpl in *.
  rewrite <- H14 ; unfold get_opt, option_map; reflexivity.
  case_eq (new_code ! p) ; intros.
  exploit H9 ; eauto. intros [HH1 | HH2].
  exploit H2 ; eauto.
  intros. rewrite H13 in * ; simpl in *.
  rewrite H12 in H14 ; unfold get_opt, option_map in *. congruence.
  rewrite PTree.gempty in HH2.  inv HH2. 
  reflexivity.

  split.
  apply Hcheck.

  split. split.
  intros pc pc0 phiinstr args dst k HH10 H12 H13; simpl in *.
  assert (In pc jpoints).
    exploit fold_build_phi_block_correct; eauto; intros [T _].
    eelim T; eauto.
    rewrite PTree.gempty; congruence.
  unfold successors in *; simpl in *.
  exploit fold_build_phi_block_def_phi_some; eauto.
  intros [d [D1 D2]].
  generalize dependent H12.
  unfold index_pred, successors_list in *.
  case_eq ((make_predecessors new_code successors_instr) ! pc); intros.  
  replace (make_predecessors new_code successors_instr)
      with (make_predecessors (RTL.fn_code f) RTL.successors_instr) in *.
  exploit fold_build_phi_block_value; eauto.
  intros.
  inv H16.
  assert (nth_okp k l).
    destruct l; try congruence.
    eapply get_index_acc_nth_okp; eauto.
  rewrite HH10 in H18; inv H18.
  generalize (In_Iphi_fold2 _ _ _ _ _ _ H13); eauto.



  (* *) 
  erewrite same_successors_same_predecessors; eauto.
  eapply aux_same_succ; eauto.
  congruence.
  (*****)
  split.
  intros pc block; simpl; intros Hb.
  assert (In pc jpoints).
    exploit fold_build_phi_block_correct; eauto; intros [T _].
    eelim T; eauto.
    rewrite PTree.gempty; congruence.
  exploit fold_build_phi_block_def_phi_some; eauto.
  intros [d [D1 _]].
  exploit H6; eauto; destruct 1 as [V|V]; [elim V|idtac].
  case_eq ((make_predecessors (RTL.fn_code f) RTL.successors_instr)!pc); [intros l|idtac];
    intros Hl; unfold is_joinpoint in *; rewrite Hl in *; try congruence; clear V.
  exploit fold_build_phi_block_value; eauto.
  intros F; inv F.  
  rewrite H14 in Hb; inv Hb.
  eapply In_Iphi_fold6; eauto.

  intros pc block; simpl; intros.
  assert (In pc jpoints).
    exploit fold_build_phi_block_correct; eauto; intros [T _].
    eelim T; eauto.
    rewrite PTree.gempty; congruence.
  exploit fold_build_phi_block_def_phi_some; eauto.
  intros [d [D1 _]].
  exploit H6; eauto; destruct 1 as [V|V]; [elim V|idtac].
  case_eq ((make_predecessors (RTL.fn_code f) RTL.successors_instr)!pc); [intros l|idtac];
    intros Hl; unfold is_joinpoint in *; rewrite Hl in *; try congruence; clear V.
  exploit fold_build_phi_block_value; eauto.
  intros F; inv F.  
  rewrite H19 in H12; inv H12.
  generalize (In_Iphi_fold7 _ _ _ _ _ _ _ _ H14 H15); eauto.

  split. 
  unfold check_code_at_phipoints in Hcap; simpl in Hcap.
  intros; exploit forall_ptree_true; eauto.
  simpl.
  destruct (new_code!pc); simpl; eauto; congruence.
  (* make_predecessors *)
  assert (TT: ∀pc : RTL.node, RTLutils.join_point pc f ↔ join_point pc {|
        fn_sig := RTL.fn_sig f;
        fn_params := map (fun r : Registers.reg => (r, dft_pos))
                       (RTL.fn_params f);
        fn_stacksize := RTL.fn_stacksize f;
        fn_code := new_code;
        fn_phicode := phiblock;
        fn_max_indice := size;
        fn_entrypoint := RTL.fn_entrypoint f |}).
  intros pc. 
  rewrite is_joinpoint_iff_join_point ; eauto.
  rewrite is_joinpoint_iff_join_point_ssa ; eauto.  
  unfold successors, successors.  simpl.
  replace (make_predecessors new_code successors_instr)
      with (make_predecessors (RTL.fn_code f) RTL.successors_instr) in *. intuition. 
  erewrite same_successors_same_predecessors; eauto.
  eapply aux_same_succ; eauto.
  
  split.
  apply TT.
  (*****)
  split. 
  intros.
  exploit fold_build_phi_block_correct ; eauto.
  intros [HH _]. exploit HH ; eauto.
  intros [HH1 | HH2]. exploit H6 ; eauto.
  intros [HH1' | HH2']. inv HH1'.
  rewrite <- TT.
  rewrite is_joinpoint_iff_join_point; auto.
  rewrite PTree.gempty in HH2. inv HH2.

  split.
  intros.
  assert (In jp jpoints).
    exploit fold_build_phi_block_correct; eauto; intros [T _].
    eelim T; eauto.
    rewrite PTree.gempty; congruence.
  exploit H6; eauto.
  destruct 1 as [V1|V1].
  elim V1.
  unfold successors in *; simpl in *.
  exploit fold_build_phi_block_def_phi_some; eauto.
  intros [d [D1 D2]].
  generalize dependent H12.
  unfold index_pred, successors_list in *.
  case_eq ((make_predecessors new_code successors_instr) !jp); intros.  
  replace (make_predecessors new_code successors_instr)
      with (make_predecessors (RTL.fn_code f) RTL.successors_instr) in *.
  exploit fold_build_phi_block_value; eauto.
  intros.
  inv H16.
  rewrite H15 in H18; inv H18.
  generalize (In_Iphi_fold1' _ _ _ _ _ _ H13); eauto.
  (* *) 
  erewrite same_successors_same_predecessors; eauto.
  eapply aux_same_succ; eauto.
  rewrite <- is_joinpoint_iff_join_point in V1.
  rewrite TT in V1.
  rewrite is_joinpoint_iff_join_point_ssa in V1.
  generalize V1; unfold successors, is_joinpoint.   simpl.
  rewrite H12; congruence.

  split.
  intros.
  assert (In jp jpoints).
    exploit fold_build_phi_block_correct; eauto; intros [T _].
    eelim T; eauto.
    rewrite PTree.gempty; congruence.
  exploit H6; eauto.
  destruct 1 as [V1|V1].
  elim V1.
  rewrite <- TT.
  rewrite is_joinpoint_iff_join_point; auto.

  split.
  intros.
  assert (In jp (fn_dfs f)).
    exploit H9; eauto.
    rewrite PTree.gempty; destruct 1; auto; congruence.
  exploit fold_build_phi_block_correct; eauto; intros [_ [T _]].
  apply T.
  exploit H10; eauto; destruct 1.
  rewrite PTree.gempty in *; congruence.
  destruct H15 as [H15 _].
  case_eq (G!jp); intros; try congruence.
  eapply H11; eauto.
  rewrite <- is_joinpoint_iff_join_point; auto.
  rewrite TT; auto.

  intros i.
  case_eq ((RTL.fn_code f)!i); intros.
  exploit Hdf1; eauto; intros Hi.
  exploit H2; eauto.
  rewrite H12; auto.
  case_eq (new_code!i); intros.
  exploit H9; eauto; destruct 1.
  exploit H2; eauto.
  congruence.
  rewrite PTree.gempty in *; congruence.
  reflexivity.
Qed.

(** Smaller lemmas, derived from the main lemma. These are to be used
in the proofs.*)

Lemma typecheck_function_size : forall f size def def_phi live tf,
  typecheck_function  f size def def_phi live = OK tf ->
  fn_max_indice tf = size.
Proof.
  intros.
  unfold typecheck_function in H.
  destruct check_function_inv.
  destruct (fold_left
    (update_ctx  (make_predecessors (RTL.fn_code f) RTL.successors_instr)
      def def_phi (RTL.fn_code f) live) (fn_dfs f)
    (OK (entry_Gamma f, PTree.empty instruction, nil))) in H.
  destruct p as [[G newcode] jp].
  monadInv H.
  destruct check_unique_def.
  destruct check_code_at_phipoints; simpl in *; try congruence.
  inv EQ0 ; auto.
  simpl in *; congruence.
  congruence.
  congruence.
Qed.

Lemma typecheck_function_correct_sig:
  forall f tf def def_phi live ,
    typecheck_function f (fn_max_indice tf) def def_phi live = OK tf ->
    RTL.fn_sig f = fn_sig tf.
Proof.
  intros.
  unfold typecheck_function in H.
  destruct check_function_inv.
  destruct (fold_left
          (update_ctx (make_predecessors (RTL.fn_code f) RTL.successors_instr) def
             def_phi (RTL.fn_code f) live) (fn_dfs f)
          (OK (entry_Gamma f, PTree.empty instruction, nil))).
  destruct p ; destruct p.
  monadInv H.
  case_eq (check_unique_def {|
              fn_sig := RTL.fn_sig f;
              fn_params := map (fun r : Registers.reg => (r, dft_pos))
                             (RTL.fn_params f);
              fn_stacksize := RTL.fn_stacksize f;
              fn_code := t0;
              fn_phicode := x;
              fn_max_indice := (fn_max_indice tf);
              fn_entrypoint := RTL.fn_entrypoint f |}); intros Hif ; rewrite Hif in *.
  destruct check_code_at_phipoints; simpl in EQ0; try congruence.
  inversion EQ0. auto.
  simpl in *; congruence. congruence. congruence.
Qed.

Lemma typecheck_function_correct_ssize:
  forall f tf def def_phi live ,
    typecheck_function f (fn_max_indice tf) def def_phi live = OK tf ->
    RTL.fn_stacksize f = fn_stacksize tf.
Proof.
  intros.
  unfold typecheck_function in H.
  case_eq (check_function_inv f (make_predecessors (RTL.fn_code f) RTL.successors_instr)) ; intros Hif ; rewrite Hif in *.
  destruct (fold_left
          (update_ctx (make_predecessors (RTL.fn_code f) RTL.successors_instr) def
             def_phi (RTL.fn_code f) live) (fn_dfs f)
          (OK (entry_Gamma f, PTree.empty instruction, nil))).
  destruct p ; destruct p.
  monadInv H.
  case_eq (check_unique_def {|
              fn_sig := RTL.fn_sig f;
              fn_params := map (fun r : Registers.reg => (r, dft_pos))
                             (RTL.fn_params f);
              fn_stacksize := RTL.fn_stacksize f;
              fn_code := t0;
              fn_phicode := x;
              fn_max_indice := (fn_max_indice tf);
              fn_entrypoint := RTL.fn_entrypoint f |}); intros Hif' ; rewrite Hif' in *.
  destruct check_code_at_phipoints; simpl in EQ0; try congruence.
  inversion EQ0. auto.
  simpl in *; congruence. congruence. congruence.
Qed.

Lemma typecheck_function_correct_erase:
  forall f tf def def_phi live ,
    RTLdfs.wf_dfs_function f ->
    typecheck_function f (fn_max_indice tf) def def_phi (fun pc => (Lin f pc (Lout live))) = OK tf ->
    check_erased_spec f tf.
Proof.
  intros f tf def def_phi live HDFS Hok.
  inv HDFS; exploit typecheck_function_correct; eauto.
  destruct 1; intuition.
Qed.  

Lemma typecheck_function_correct_udef:
  forall f tf def def_phi live ,
    typecheck_function f (fn_max_indice tf) def def_phi live = OK tf ->
    unique_def_spec tf.
Proof.
  intros.
  unfold typecheck_function in H.
  destruct check_function_inv.
  destruct (fold_left
          (update_ctx (make_predecessors (RTL.fn_code f) RTL.successors_instr) def
             def_phi (RTL.fn_code f) live) (fn_dfs f)
          (OK (entry_Gamma f, PTree.empty instruction, nil))).
  destruct p ; destruct p.
  monadInv H.
  case_eq (check_unique_def {|
              fn_sig := RTL.fn_sig f;
              fn_params := map (fun r : Registers.reg => (r, dft_pos))
                             (RTL.fn_params f);
              fn_stacksize := RTL.fn_stacksize f;
              fn_code := t0;
              fn_phicode := x;
              fn_max_indice := (fn_max_indice tf);
              fn_entrypoint := RTL.fn_entrypoint f |}); intros Hif ; rewrite Hif in *.
  destruct check_code_at_phipoints; simpl in *; try congruence.
  inversion EQ0.
  eapply check_unique_def_correct ; eauto.
  simpl in *; congruence. congruence. congruence.
Qed.

Lemma typecheck_function_correct_phiparams:
  forall f tf def def_phi live ,
    RTLdfs.wf_dfs_function f ->
    typecheck_function f (fn_max_indice tf) def def_phi (fun pc => (Lin f pc (Lout live))) = OK tf ->
    check_phi_params_spec tf.
Proof.
  intros.
  inv H; exploit typecheck_function_correct; eauto.
  destruct 1.
  decompose [and] H; auto.
Qed.

Lemma typecheck_function_correct_parablocks:
  forall f tf def def_phi live ,
    RTLdfs.wf_dfs_function f ->
    typecheck_function f (fn_max_indice tf) def def_phi (fun pc => (Lin f pc (Lout live))) = OK tf ->
    check_para_block_spec tf.
Proof.
  intros.
  inv H; exploit typecheck_function_correct; eauto.
  destruct 1.
  decompose [and] H; auto.
Qed.
  
Lemma typecheck_function_correct_noduplicates:
  forall f tf def def_phi live ,
    RTLdfs.wf_dfs_function f ->
    typecheck_function f (fn_max_indice tf) def def_phi (fun pc => (Lin f pc (Lout live))) = OK tf ->
    check_no_duplicates_spec tf.
Proof.
  intros.
  inv H; exploit typecheck_function_correct; eauto.
  destruct 1.
  decompose [and] H; auto.
Qed.

Lemma typecheck_function_correct_structural_checks:
  forall f tf def def_phi live ,
    RTLdfs.wf_dfs_function f ->
    typecheck_function f (fn_max_indice tf) def def_phi (fun pc => (Lin f pc (Lout live)))  = OK tf ->
    structural_checks_spec f tf.
Proof.
  intros. 
  constructor. eapply typecheck_function_correct_sig; eauto.
  constructor. eapply typecheck_function_correct_ssize; eauto.
  constructor. eapply typecheck_function_correct_erase; eauto.
  constructor. eapply typecheck_function_correct_udef; eauto.
  constructor. eapply typecheck_function_correct_phiparams; eauto.
  constructor. eapply typecheck_function_correct_parablocks; eauto.
  eapply typecheck_function_correct_noduplicates; eauto.
Qed.  

Lemma fn_ssa_params1 : forall f tf def def_phi live ,
    RTLdfs.wf_dfs_function f ->
    typecheck_function f (fn_max_indice tf) def def_phi (fun pc => (Lin f pc (Lout live)))  = OK tf ->
    forall x pc, In x (fn_params tf) -> ~ assigned_code_spec (fn_code tf) pc x.
Proof.
  intros.
  exploit typecheck_function_correct ; eauto; [ eapply RTLdfs.fn_dfs_comp ; eauto|eapply RTLdfs.fn_dfs_norep ; eauto|idtac].
  intros [G [HWT [HWFI [HER HPHI]]]]. 
  intros Hcont.
  inv HWFI. exploit H2 ; eauto. intros [r Heq] ; subst.  
   (inv Hcont;  
    inv HWT; (exploit (WTE pc succ) ; eauto ); 
    try (econstructor ; eauto ; simpl ; eauto));
  (intros Hwte; inv Hwte; ( inv EIDX; congruence)). 
Qed.

Lemma fn_ssa_params2 : forall f tf def def_phi live ,
  RTLdfs.wf_dfs_function f ->
  typecheck_function f (fn_max_indice tf) def def_phi (fun pc => (Lin f pc (Lout live)))  = OK tf ->
  forall x pc, In x (fn_params tf) -> ~ assigned_phi_spec (fn_phicode tf) pc x.
Proof.
  intros.
  exploit typecheck_function_correct ; eauto; [ eapply RTLdfs.fn_dfs_comp ; eauto|eapply RTLdfs.fn_dfs_norep ; eauto|idtac].
  intros [G [HWT [HWFI [HERASE [HNORM [[HPHI [HPHI2 HPHI3]] [HPHI4 [HJP [HPHI5 HPHI6]]]]]]]]].
  intro Hcont.
  inv HWFI. exploit H2 ; eauto. intros [r Heq] ; subst.  
  inv Hcont. destruct H4.  
  exploit HPHI4 ; eauto. intros [ins Hins].
  exploit HPHI5 ; eauto. intros Hjp.
  inv Hjp.
  assert (exists p0, In p0 l). destruct l ; simpl in *. inv Hl. exists p. eauto.
  destruct H5 as [p0 Hin].
  assert ((make_predecessors (fn_code tf) (successors_instr)) !!! pc = l).
  unfold successors_list. rewrite Hpreds ; simpl ; auto.  
  exploit @make_predecessors_some; eauto. intros [ip0 Hip0].
  rewrite <- H5 in Hin.
  assert (HH : In pc (successors_instr ip0)).
  eapply @KildallComp.make_predecessors_correct2; eauto.
  
  assert (is_edge tf p0 pc). econstructor ; eauto.
  inv HWT; (exploit (WTE p0 pc) ; eauto ).
  intros Hwte; inv Hwte; allinv. 
  inv PEIDX. eelim H5 with (ri:= (r, G (fn_entrypoint tf) r)) ; eauto.
  econstructor ; eauto. 
Qed.

Lemma fn_parablock: forall pc block, 
  forall f tf def def_phi live ,
    RTLdfs.wf_dfs_function f ->
    typecheck_function f (fn_max_indice tf) def def_phi (fun pc => (Lin f pc (Lout live)))  = OK tf ->
    (fn_phicode tf) ! pc = Some block -> 
    NoDup block /\ para_block block.
Proof.
  intros.
  exploit typecheck_function_correct ; eauto; [ eapply RTLdfs.fn_dfs_comp ; eauto|eapply RTLdfs.fn_dfs_norep ; eauto|idtac].
  intros [G [HWT [HWFI [HER [_ [[_ [HPHI Hn]] _]]]]]].
  generalize (HPHI  _ _ H1); split; auto.
  exploit typecheck_function_correct_udef; eauto; intros [_ Hu].
  exploit Hu; eauto; intuition.
Qed.  

Lemma fn_reached : forall f tf def def_phi live ,
  RTLdfs.wf_dfs_function f ->
  typecheck_function f (fn_max_indice tf) def def_phi (fun pc => (Lin f pc (Lout live)))  = OK tf ->
  forall pc ins, (fn_code tf) ! pc = Some ins -> reached tf pc.
Proof.
  intros.
  assert (∀i : positive, get_opt erase_instr (fn_code tf) ! i = get_opt (fun x => x) (RTL.fn_code f) ! i).
    exploit typecheck_function_correct ; eauto; [ eapply RTLdfs.fn_dfs_comp ; eauto|eapply RTLdfs.fn_dfs_norep ; eauto|idtac].
    intros [G HG].
    decompose [and] HG; assumption.
  assert (exists ins', (RTL.fn_code f)!pc = Some ins').
    generalize (H2 pc); rewrite H1; simpl.
    case_eq ((RTL.fn_code f)!pc); simpl; try congruence; eauto.
  destruct H3 as [ins' H3].
  assert (In pc (fn_dfs f)).
    inv H; eauto.
  assert (forall i j, RTLutils.cfg (RTL.fn_code f) i j -> cfg tf i j).
    intros i j T.
    inv T.
    generalize (H2 i); rewrite HCFG_ins; simpl.
    case_eq ((fn_code tf)!i); simpl; try congruence; intros.
    inv H6.
    replace (RTL.successors_instr (erase_instr i0)) with (successors_instr i0) in *.
    econstructor; eauto.
    destruct i0 ; simpl ; eauto.
    destruct s0 ; simpl ; eauto.
    destruct s0 ; simpl ; eauto.
    destruct o; simpl ; eauto.
  assert (forall i j, (RTLutils.cfg (RTL.fn_code f))** i j -> (cfg tf)** i j).
    induction 1.
    constructor 1; auto.
    constructor 2.
    constructor 3 with y; auto.
  apply H6. unfold entry.
  replace (fn_entrypoint tf) with (RTL.fn_entrypoint f).
  eapply RTLdfs.fn_dfs_reached; eauto.
  
  unfold typecheck_function in H0.
  destruct check_function_inv; try (inv H0; fail).
  destruct (fold_left
           (update_ctx (make_predecessors (RTL.fn_code f) RTL.successors_instr)
              def def_phi (RTL.fn_code f)
              (fun pc : node => Lin f pc (Lout live))) 
           (fn_dfs f) (OK (entry_Gamma f, PTree.empty instruction, nil))); try (inv H0; fail).
  destruct p; destruct p.
  destruct (fold_left
            (build_phi_block
               (make_predecessors (RTL.fn_code f) RTL.successors_instr)
               (fun pc : node => Lin f pc (Lout live)) def_phi t) l
            (OK (PTree.empty phiblock))); try (inv H0; fail).
  simpl in H0.
  destruct check_unique_def; try (inv H0; fail).
  destruct check_code_at_phipoints; simpl in H0; inversion H0; clear H0.
  simpl; auto.
Qed.

Lemma fn_entry : forall f tf def def_phi live ,
  RTLdfs.wf_dfs_function f ->
  typecheck_function f (fn_max_indice tf) def def_phi (fun pc => (Lin f pc (Lout live)))  = OK tf ->
  exists s, (fn_code tf) ! (fn_entrypoint tf) = Some (Inop s).
Proof.
  intros.
  exploit typecheck_function_correct ; eauto; [ eapply RTLdfs.fn_dfs_comp ; eauto|eapply RTLdfs.fn_dfs_norep ; eauto|idtac].
  intros [G [HWT [HWFI [HER [H' HPHI]]]]]. inv HER.  
  inv H'. unfold check_function_inv in H2.
  case_eq (RTL.fn_code f) ! (RTL.fn_entrypoint f) ; intros.
  rewrite H1 in * ; destruct i ; try congruence.
  rewrite HCODE in H1.
  unfold erase_code in H1. rewrite PTree.gmap in H1.
  unfold option_map in H1.
  rewrite HENTRY in *.
  destruct ((fn_code tf) ! (fn_entrypoint tf)); try congruence.
  destruct i; simpl in *; try congruence.
  eauto.
  destruct s0; try congruence.
  destruct s0; try congruence.
  destruct o; try congruence.
  rewrite H1 in * ; congruence.
Qed.

Lemma fn_phicode_code : forall f tf def def_phi live ,
  RTLdfs.wf_dfs_function f ->
  typecheck_function f (fn_max_indice tf) def def_phi (fun pc => (Lin f pc (Lout live)))  = OK tf ->
  forall pc block, 
    (fn_phicode tf) ! pc = Some block -> 
    exists ins, (fn_code tf) ! pc = Some ins.
Proof.
  intros.
  exploit typecheck_function_correct ; eauto; [ eapply RTLdfs.fn_dfs_comp ; eauto|eapply RTLdfs.fn_dfs_norep ; eauto|idtac].
  intros [G HH]. decompose [and] HH.
  eauto.
Qed.

Lemma fn_code_closed:forall f tf def def_phi live ,
  RTLdfs.wf_dfs_function f ->
  typecheck_function f (fn_max_indice tf) def def_phi (fun pc => (Lin f pc (Lout live)))  = OK tf ->
  forall pc pc' instr, tf.(fn_code) ! pc = Some instr ->
    In pc' (successors_instr instr) -> 
    exists instr', tf.(fn_code) ! pc' = Some instr'.
Proof.
  intros.
  exploit typecheck_function_correct_erase ; eauto. intros Herased; inv Herased.
  unfold typecheck_function in H0.
  case_eq (check_function_inv f (make_predecessors (RTL.fn_code f) RTL.successors_instr)) ; intros Hif ; rewrite Hif in *.
  assert ((erase_code tf) ! pc = Some (erase_instr instr)).
  unfold erase_code ; rewrite PTree.gmap ; unfold option_map ; rewrite H1.
  auto.
  rewrite <- HCODE in H3.
  exploit (check_function_inv_correct0 f Hif pc pc') ; eauto.
  assert ((successors_instr instr) = (RTL.successors_instr (erase_instr instr))).
  induction instr ; simpl ; eauto.
  destruct s0 ; simpl ; eauto.
  destruct s0 ; simpl ; eauto.
  destruct o; simpl ; eauto.
  rewrite H4 in *.  auto.
  intros [instr' Hinstr'].
  rewrite HCODE in Hinstr'. 
  unfold erase_code in Hinstr' ; rewrite PTree.gmap in Hinstr' ; unfold option_map in *.
  destruct (fn_code tf) ! pc'. exists i ; auto. 
  congruence.
  congruence.
Qed.

Lemma fn_entrypoint_inv: forall f tf def def_phi live ,
  RTLdfs.wf_dfs_function f ->
  typecheck_function f (fn_max_indice tf) def def_phi (fun pc => (Lin f pc (Lout live)))  = OK tf ->
  (exists i, (tf.(fn_code) ! (tf.(fn_entrypoint)) = Some i)) /\ 
  ~ join_point tf.(fn_entrypoint) tf.
Proof.
intros.
  exploit typecheck_function_correct_erase ; eauto. intros Herased; inv Herased.
  exploit typecheck_function_correct ; eauto. 
  eapply RTLdfs.fn_dfs_comp ; eauto.
  eapply RTLdfs.fn_dfs_norep ; eauto.
  intros [_ [_ [_ [_ [_ [_ [_ [HH _]]]]]]]].
  
  unfold typecheck_function in H0.
  case_eq (check_function_inv f (make_predecessors (RTL.fn_code f) RTL.successors_instr)) ; intros Hif ; rewrite Hif in *.
  assert (exists ins, (RTL.fn_code f) ! (RTL.fn_entrypoint f) = Some ins).
  eapply (check_function_inv_correct11 f) ; eauto.
  split.
  destruct H1. rewrite HCODE in H1. unfold erase_code in H1. rewrite PTree.gmap in H1.
  unfold option_map in H1. rewrite HENTRY in H1.
  destruct (fn_code tf) ! (fn_entrypoint tf); intros. exists i ; auto. congruence.
  eapply (check_function_inv_correct12 f) in Hif ; eauto. 
  clear H0.
  intro Hcont. rewrite HENTRY in * . eelim (HH (fn_entrypoint tf)) ; eauto.
  congruence.
Qed.

Lemma fn_code_inv2: forall f tf def def_phi live ,
  RTLdfs.wf_dfs_function f ->
  typecheck_function f (fn_max_indice tf) def def_phi (fun pc => (Lin f pc (Lout live)))  = OK tf ->
  forall jp pc i, (join_point jp tf) ->
    In jp ((successors tf) !!! pc) ->
    tf.(fn_code) ! jp = Some i ->
    tf.(fn_code) ! pc = Some (Inop jp).
Proof.
  intros.
  exploit typecheck_function_correct ; eauto; [ eapply RTLdfs.fn_dfs_comp ; eauto|eapply RTLdfs.fn_dfs_norep ; eauto|idtac].
  intros [G [HWT [HWFI [HERASE [HNORM [[HPHI [HPHI2 HPHI3]] [HPHI4 [HJP HPHI5]]]]]]]].
  inv HNORM. inv HERASE.
  assert ((RTL.fn_code f) ! jp = Some (erase_instr i)).
  rewrite HCODE. unfold erase_code ; rewrite PTree.gmap ; unfold option_map.
  rewrite H3 ; auto. 
  assert (In jp (RTL.successors_map f) !!! pc).
  unfold successors_list, RTL.successors_map. rewrite PTree.gmap1.
  unfold option_map. 
  unfold successors, successors_list in H2.
  rewrite PTree.gmap1 in H2. unfold option_map in H2.
  case_eq (fn_code tf) ! pc ; intros; rewrite H6 in *; [| inv H2].
  assert ((RTL.fn_code f) ! pc = Some (erase_instr i0)).
  rewrite HCODE. unfold erase_code ; rewrite PTree.gmap ; unfold option_map.
  rewrite H6 ; auto. 
  rewrite H7. destruct i0 ; simpl ; eauto.
  destruct s0 ; simpl ; eauto.
  destruct s0 ; simpl ; eauto.
  destruct o ; simpl ; eauto.
  exploit check_function_inv_correct3 ; eauto.
  eapply HJP; auto.
  intros.
  rewrite HCODE in H7. unfold erase_code in H7.
  rewrite PTree.gmap in H7. unfold option_map in H7. 
  destruct ((fn_code tf) ! pc) ; [destruct i0 ; simpl in * ; try congruence|].
  destruct s0 ; simpl ; congruence.
  destruct s0 ; simpl ; congruence.
  destruct o ; simpl ; congruence. congruence.
Qed. 
  
Lemma fn_phicode_inv1: forall f tf def def_phi live ,
  RTLdfs.wf_dfs_function f ->
  typecheck_function f (fn_max_indice tf) def def_phi (fun pc => (Lin f pc (Lout live)))  = OK tf ->
  forall phib jp i,
    tf.(fn_code) ! jp = Some i -> 
    tf.(fn_phicode) ! jp = Some phib ->
    join_point jp tf.
Proof.
  intros.
  exploit typecheck_function_correct ; eauto; [ eapply RTLdfs.fn_dfs_comp ; eauto|eapply RTLdfs.fn_dfs_norep ; eauto|idtac].
  intros [G HH]; decompose [and] HH.
  eauto.
Qed.

Lemma fn_phicode_inv2: forall f tf def def_phi live ,
  RTLdfs.wf_dfs_function f ->
  typecheck_function f (fn_max_indice tf) def def_phi (fun pc => (Lin f pc (Lout live)))  = OK tf ->
  forall jp i,
    join_point jp tf ->
    tf.(fn_code) ! jp = Some i -> 
    exists phib, tf.(fn_phicode) ! jp = Some phib.
Proof.
  intros.
  exploit typecheck_function_correct ; eauto; [ eapply RTLdfs.fn_dfs_comp ; eauto|eapply RTLdfs.fn_dfs_norep ; eauto|idtac].
  intros [G HH]; decompose [and] HH.
  eauto.
Qed.

Lemma typecheck_function_fn_uacf : forall f  def def_phi tf live,
  RTLdfs.wf_dfs_function f ->
  (wf_live f (Lout live)) ->
  typecheck_function f (fn_max_indice tf) def def_phi (fun pc0 : node => Lin f pc0 (Lout live)) = OK tf ->
  ∀x : reg,
  ∀pc : node,
  use_code tf x pc
  → assigned_code_spec (fn_code tf) pc x → False.
Proof.
  intros.
  exploit typecheck_function_correct ; eauto.  
  eapply RTLdfs.fn_dfs_comp ; eauto.
  eapply RTLdfs.fn_dfs_norep ; eauto.
  intros [G [HWT [HWFI [HER HPHI]]]]. inv HER.
  exploit wt_def_use_code_false; eauto. constructor ; eauto.
  eapply typecheck_function_correct_udef ; eauto.
  
  eapply fn_ssa_params1 ; eauto. 
  eapply fn_ssa_params2 ; eauto.
  eapply fn_reached ; eauto.
  eapply fn_entry ; eauto.   
  eapply fn_phicode_code ; eauto.
  eapply fn_code_closed ; eauto.
  eapply fn_entrypoint_inv ; eauto.
  eapply fn_code_inv2 ; eauto.
  eapply fn_phicode_inv1 ; eauto.
Qed.

Lemma typecheck_function_fn_strict : forall f  def def_phi tf live,
  RTLdfs.wf_dfs_function f ->
  (wf_live f (Lout live)) ->
  typecheck_function f (fn_max_indice tf) def def_phi (fun pc0 : node => Lin f pc0 (Lout live)) = OK tf ->
   ∀x : reg, ∀u d : node, use tf x u → SSA.def tf x d → dom tf d u.
Proof.
  intros.
  exploit typecheck_function_correct ; eauto.  
  eapply RTLdfs.fn_dfs_comp ; eauto.
  eapply RTLdfs.fn_dfs_norep ; eauto.
  intros [G [HWT [HWFI [HER HPHI]]]]. inv HER.
  exploit wt_pdom; eauto. constructor ; eauto.
  eapply typecheck_function_correct_udef ; eauto.
  eapply fn_ssa_params1 ; eauto.
  eapply fn_ssa_params2 ; eauto.
  eapply fn_reached ; eauto.
  eapply fn_entry ; eauto.
  eapply fn_phicode_code ; eauto.
  eapply fn_code_closed ; eauto.
  eapply fn_entrypoint_inv ; eauto.
  eapply fn_code_inv2 ; eauto.
  eapply fn_phicode_inv1 ; eauto.
Qed.

(** * All generated function satisfy [wf_ssa_function] *)  
Lemma typecheck_function_wf_ssa_function : forall f size def def_phi tf live,
  RTLdfs.wf_dfs_function f ->
  (wf_live f (Lout live)) ->
  typecheck_function f size def def_phi (fun pc0 : node => Lin f pc0 (Lout live)) = OK tf ->
  wf_ssa_function tf.
Proof.
  intros.   
  exploit typecheck_function_size  ; eauto. intros Heq ; inv Heq.

  constructor.
  eapply typecheck_function_correct_udef ; eauto.
  split; intros.
  eapply fn_ssa_params1 ; eauto.
  eapply fn_ssa_params2 ; eauto.
  eapply typecheck_function_fn_strict ; eauto.
  eapply typecheck_function_fn_uacf ; eauto.

  exploit typecheck_function_correct ; eauto.  
  eapply RTLdfs.fn_dfs_comp ; eauto.
  eapply RTLdfs.fn_dfs_norep ; eauto.
  intros [G HG]; decompose [and] HG.
  intros pc phib args x T1 T2.
  symmetry; eapply H12; eauto.
  
  intros. 
  case_eq ((fn_code tf) ! jp) ; intros.
  eapply fn_code_inv2 ; eauto.
  unfold successors_list, successors in H3.
  rewrite PTree.gmap1 in H3. 
  case_eq ((fn_code tf) ! pc) ; intros; rewrite H5 in *; simpl in *.
    exploit fn_code_closed ; eauto. intros. destruct H6.
    congruence.
  intuition.

  intros.
  split; intros.
  intro Hcont.
  inv H2.
  assert (exists p, In p l).
  destruct l.  simpl in * .  omega. eauto. destruct H2.  
  assert ((make_predecessors (fn_code tf) successors_instr) !!! jp = l).
  unfold successors_list ; rewrite Hpreds ; simpl ; auto.  
  exploit @make_predecessors_some; eauto. intros [ix Hix].
  assert (HH : In jp (successors_instr ix)).
  eapply @KildallComp.make_predecessors_correct2  ; eauto.
  unfold successors_list, successors in *.
  rewrite Hpreds in *.
  unfold make_preds. rewrite Hpreds in *. auto.
  exploit fn_code_closed ; eauto. intros [ins' Hins'].
  exploit fn_phicode_inv2 ; eauto.
  econstructor; eauto. intros.
  destruct H4. congruence. 
  case_eq (fn_phicode tf) ! jp ; intros; [| congruence].
  exploit fn_phicode_code ; eauto. intros [ins Hins].
  exploit fn_phicode_inv1 ; eauto.
   
  eapply fn_reached ; eauto.
  eapply fn_code_closed ; eauto.
  eapply fn_entry ; eauto.  
  
  exploit typecheck_function_correct_erase ; eauto. intros Herased.
  unfold typecheck_function in H1.
  case_eq (check_function_inv f
             (make_predecessors (RTL.fn_code f) RTL.successors_instr)) ; intros Hif ; rewrite Hif in *.
  clear H1. intros.
  intro Hcont.  inv Hcont.
  inv Herased.
  assert ((RTL.fn_code f) ! pc = (Some (erase_instr ins))).
  rewrite HCODE.
  unfold erase_code. rewrite PTree.gmap. unfold option_map. rewrite HCFG_ins. auto.
  eelim (check_function_inv_correct01 f Hif pc) ; eauto.
  rewrite HENTRY.
  destruct ins ; simpl ; eauto.
  destruct s0 ; simpl ; eauto.
  destruct s0 ; simpl ; eauto.
  destruct o ; simpl ; eauto.
  congruence.
Qed.  

Lemma transf_function_wf_ssa_function : forall f tf,
  RTLdfs.wf_dfs_function f ->
  transf_function f = OK tf -> wf_ssa_function tf.
Proof.
  intros.
  unfold transf_function in H0.  monadInv H0.
  destruct (extern_gen_ssa f) as [[max def] def_phi].
  eapply typecheck_function_wf_ssa_function ; eauto.
  case_eq (analyze f); intros;  rewrite H0 in * ; simpl in *. 
  inv EQ. eapply live_wf_live ; eauto. 
 congruence.
Qed.  

Lemma transf_program_wf : forall (p: RTL.program) (tp: SSA.program),
  RTLdfs.wf_dfs_program p ->
  transf_program p = OK tp ->
  wf_ssa_program tp.
Proof.
  repeat intro.
  elim transform_partial_program_function with (1:=H0) (2:=H1).
  intros g [F1 F2].
  destruct g; simpl in *.
  case_eq (transf_function f0); intros; rewrite H2 in *; inv F2.
  constructor.
  eapply transf_function_wf_ssa_function; eauto.
  exploit H ; eauto. intros. inv H3 ; auto.
  inv F2; constructor.
Qed.
