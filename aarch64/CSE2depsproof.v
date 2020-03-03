Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Memory Registers Op RTL Maps.

Require Import Globalenvs Values.
Require Import Linking Values Memory Globalenvs Events Smallstep.
Require Import Registers Op RTL.
Require Import CSE2 CSE2deps.
Require Import Lia.

Lemma ptrofs_size :
  Ptrofs.wordsize = 64%nat.
Proof.
  unfold Ptrofs.wordsize.
  unfold Wordsize_Ptrofs.wordsize.
  trivial.
Qed.

Lemma ptrofs_modulus :
  Ptrofs.modulus = 18446744073709551616.
Proof.
  reflexivity.
Qed.

Section SOUNDNESS.
  Variable F V : Type.
  Variable genv: Genv.t F V.
  Variable sp : val.

Section MEMORY_WRITE.
  Variable m m2 : mem.
  Variable chunkw chunkr : memory_chunk.
  Variable base : val.
  
  Variable addrw addrr valw valr : val.
  Hypothesis STORE : Mem.storev chunkw m addrw valw = Some m2.
  Hypothesis READ : Mem.loadv chunkr m addrr = Some valr.

  Section INDEXED_AWAY.
  Variable ofsw ofsr : int64.
  Hypothesis ADDRW : eval_addressing genv sp
                       (Aindexed ofsw) (base :: nil) = Some addrw. 
  Hypothesis ADDRR : eval_addressing genv sp
                       (Aindexed ofsr) (base :: nil) = Some addrr.

  Lemma load_store_away1 :
    forall RANGEW : 0 <= Int64.unsigned ofsw <= Ptrofs.modulus - largest_size_chunk,
    forall RANGER : 0 <= Int64.unsigned ofsr <= Ptrofs.modulus - largest_size_chunk,
    forall SWAPPABLE :    Int64.unsigned ofsw + size_chunk chunkw <= Int64.unsigned ofsr
                       \/ Int64.unsigned ofsr + size_chunk chunkr <= Int64.unsigned ofsw,
    Mem.loadv chunkr m2 addrr = Some valr.
  Proof.
    intros.
    
    pose proof (max_size_chunk chunkr) as size_chunkr_bounded.
    pose proof (max_size_chunk chunkw) as size_chunkw_bounded.
    unfold largest_size_chunk in *.

    rewrite ptrofs_modulus in *.
    simpl in *.
    inv ADDRR.
    inv ADDRW.
    rewrite <- READ.
    destruct base; try discriminate.
    eapply Mem.load_store_other with (chunk := chunkw) (v := valw) (b := b).
    exact STORE.
    right.

    all: unfold Ptrofs.of_int64.

    all: try (destruct (Ptrofs.unsigned_add_either i (Ptrofs.repr (Int64.unsigned ofsr))) as [OFSR | OFSR];
              rewrite OFSR).
    all: try (destruct (Ptrofs.unsigned_add_either i (Ptrofs.repr (Int64.unsigned ofsw))) as [OFSW | OFSW];
              rewrite OFSW).
    all: repeat rewrite Ptrofs.unsigned_repr by (change Ptrofs.max_unsigned with 18446744073709551615; lia).

    all: try rewrite ptrofs_modulus in *.

    all: intuition lia.
  Qed.
  
  Theorem load_store_away :
    can_swap_accesses_ofs (Ptrofs.unsigned ofsr) chunkr (Ptrofs.unsigned ofsw) chunkw = true ->
    Mem.loadv chunkr m2 addrr = Some valr.
  Proof.
    intro SWAP.
    unfold can_swap_accesses_ofs in SWAP.
    repeat rewrite andb_true_iff in SWAP.
    repeat rewrite orb_true_iff in SWAP.
    repeat rewrite Z.leb_le in SWAP.
    apply load_store_away1.
    all: tauto.
  Qed.
  End INDEXED_AWAY.
End MEMORY_WRITE.
End SOUNDNESS.


Section SOUNDNESS.
  Variable F V : Type.
  Variable genv: Genv.t F V.
  Variable sp : val.

Lemma may_overlap_sound:
  forall m m' : mem,
  forall chunk addr args chunk' addr' args' v a a' vl rs,
    (eval_addressing genv sp addr (rs ## args)) = Some a ->
    (eval_addressing genv sp addr' (rs ## args')) = Some a' ->
    (may_overlap chunk addr args chunk' addr' args') = false ->
    (Mem.storev chunk m a v) = Some m' ->
    (Mem.loadv chunk' m  a') = Some vl ->
    (Mem.loadv chunk' m' a') = Some vl.
Proof.
  intros until rs.
  intros ADDR ADDR' OVERLAP STORE LOAD.
  destruct addr; destruct addr'; try discriminate.
  { (* Aindexed / Aindexed *)
  destruct args as [ | base [ | ]]. 1,3: discriminate.
  destruct args' as [ | base' [ | ]]. 1,3: discriminate.
  simpl in OVERLAP.
  destruct (peq base base'). 2: discriminate.
  subst base'.
  destruct (can_swap_accesses_ofs (Ptrofs.unsigned i0) chunk' (Ptrofs.unsigned i) chunk) eqn:SWAP.
  2: discriminate.
  simpl in *.
  eapply load_store_away with (F:=F) (V:=V) (genv:=genv) (sp:=sp); eassumption.
  }
Qed.

End SOUNDNESS.
