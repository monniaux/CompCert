Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Memory Registers Op RTL Maps.

Require Import Globalenvs Values.
Require Import Linking Values Memory Globalenvs Events Smallstep.
Require Import Registers Op RTL.
Require Import CSE2.
Require Import Lia.

Section SOUNDNESS.
  Variable F V : Type.
  Variable genv: Genv.t F V.
  Variable sp : val.

Section MEMORY_WRITE.
  Variable m m2 : mem.
  Variable chunkw chunkr : memory_chunk.
  Variable base : val.

  Lemma size_chunk_bounded :
    forall chunk, 0 <= size_chunk chunk <= max_chunk_size.
  Proof.
    unfold max_chunk_size.
    destruct chunk; simpl; lia.
  Qed.
  
  Variable addrw addrr valw valr : val.
  Hypothesis STORE : Mem.storev chunkw m addrw valw = Some m2.
  Hypothesis READ : Mem.loadv chunkr m addrr = Some valr.

  Section INDEXED_AWAY.
  Variable ofsw ofsr : Z.
  Hypothesis ADDRW : eval_addressing genv sp
                       (Aindexed ofsw) (base :: nil) = Some addrw. 
  Hypothesis ADDRR : eval_addressing genv sp
                       (Aindexed ofsr) (base :: nil) = Some addrr.

  Lemma load_store_away1 :
    forall RANGEW : 0 <= ofsw <= Ptrofs.modulus - max_chunk_size,
    forall RANGER : 0 <= ofsr <= Ptrofs.modulus - max_chunk_size,
    forall SWAPPABLE :    ofsw + size_chunk chunkw <= ofsr
                       \/ ofsr + size_chunk chunkr <= ofsw,
    Mem.loadv chunkr m2 addrr = Some valr.
  Proof.
    intros.
    
    pose proof (size_chunk_bounded chunkr) as size_chunkr_bounded.
    pose proof (size_chunk_bounded chunkw) as size_chunkw_bounded.
    unfold max_chunk_size in size_chunkr_bounded, size_chunkw_bounded.
    try change (Ptrofs.modulus - max_chunk_size) with 4294967288 in *.
    try change (Ptrofs.modulus - max_chunk_size) with 18446744073709551608 in *.
    destruct addrr ; simpl in * ; try discriminate.
    unfold eval_addressing in *.
    destruct Archi.ptr64 eqn:PTR64; destruct base; simpl in *; try discriminate.
    rewrite PTR64 in *.
    
    inv ADDRR.
    inv ADDRW.
    rewrite <- READ.
    eapply Mem.load_store_other with (chunk := chunkw) (v := valw) (b := b).
    exact STORE.
    right.
 
    all: try (destruct (Ptrofs.unsigned_add_either i0
                (Ptrofs.of_int (Int.repr ofsr))) as [OFSR | OFSR];
              rewrite OFSR).
    all: try (destruct (Ptrofs.unsigned_add_either i0
                (Ptrofs.of_int64 (Int64.repr ofsr))) as [OFSR | OFSR];
              rewrite OFSR).
    all: try (destruct (Ptrofs.unsigned_add_either i0
                (Ptrofs.of_int (Int.repr ofsw))) as [OFSW | OFSW];
              rewrite OFSW).
    all: try (destruct (Ptrofs.unsigned_add_either i0
                (Ptrofs.of_int64 (Int64.repr ofsw))) as [OFSW | OFSW];
              rewrite OFSW).
    
    all: unfold Ptrofs.of_int64.
    all: unfold Ptrofs.of_int.
   

    all: repeat rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
    all: repeat rewrite Ptrofs.unsigned_repr by (change Ptrofs.max_unsigned with 4294967295; lia).
    all: repeat rewrite Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia).
    all: repeat rewrite Ptrofs.unsigned_repr by (change Ptrofs.max_unsigned with 18446744073709551615; lia).

    all: try change Ptrofs.modulus with 4294967296.
    all: try change Ptrofs.modulus with 18446744073709551616.
   
    all: intuition lia.
  Qed.
  
  Theorem load_store_away :
    can_swap_accesses_ofs ofsr chunkr ofsw chunkw = true ->
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

  Section DIFFERENT_GLOBALS.
    Variable ofsw ofsr : ptrofs.
    Hypothesis symw symr : ident.
    Hypothesis ADDRW : eval_addressing genv sp
                                       (Aglobal symw ofsw) nil = Some addrw. 
    Hypothesis ADDRR : eval_addressing genv sp
                                       (Aglobal symr ofsr) nil = Some addrr.
    
    Lemma load_store_diff_globals :
      symw <> symr ->
      Mem.loadv chunkr m2 addrr = Some valr.
    Proof.
      intros.
      unfold eval_addressing in *.
      destruct Archi.ptr64 eqn:PTR64; simpl in *.
      rewrite PTR64 in *.
      2: simpl in *; discriminate.
      unfold Genv.symbol_address in *.
      unfold Genv.find_symbol in *.
      destruct ((Genv.genv_symb genv) ! symw) as [bw |] eqn:SYMW; inv ADDRW.
      2: simpl in STORE; discriminate.
      destruct ((Genv.genv_symb genv) ! symr) as [br |] eqn:SYMR; inv ADDRR.
      2: simpl in READ; discriminate.
      assert (br <> bw).
      {
        intro EQ.
        subst br.
        assert (symr = symw).
        {
          eapply Genv.genv_vars_inj; eauto.
        }
        congruence.
      }
      rewrite <- READ.
      eapply Mem.load_store_other with (chunk := chunkw) (v := valw) (b := bw).
      - exact STORE.
      - left. assumption.
    Qed.
  End DIFFERENT_GLOBALS.

  Section SAME_GLOBALS.
    Variable ofsw ofsr : ptrofs.
    Hypothesis sym : ident.
    Hypothesis ADDRW : eval_addressing genv sp
                                       (Aglobal sym ofsw) nil = Some addrw. 
    Hypothesis ADDRR : eval_addressing genv sp
                                       (Aglobal sym ofsr) nil = Some addrr.
    
  Lemma load_store_glob_away1 :
    forall RANGEW : 0 <= (Ptrofs.unsigned ofsw) <= Ptrofs.modulus - max_chunk_size,
    forall RANGER : 0 <= (Ptrofs.unsigned ofsr) <= Ptrofs.modulus - max_chunk_size,
    forall SWAPPABLE : (Ptrofs.unsigned ofsw) + size_chunk chunkw <= (Ptrofs.unsigned ofsr)
                    \/ (Ptrofs.unsigned ofsr) + size_chunk chunkr <= (Ptrofs.unsigned ofsw),
    Mem.loadv chunkr m2 addrr = Some valr.
  Proof.
    intros.
    
    pose proof (size_chunk_bounded chunkr) as size_chunkr_bounded.
    pose proof (size_chunk_bounded chunkw) as size_chunkw_bounded.
    unfold max_chunk_size in size_chunkr_bounded, size_chunkw_bounded.
    try change (Ptrofs.modulus - max_chunk_size) with 4294967288 in *.
    try change (Ptrofs.modulus - max_chunk_size) with 18446744073709551608 in *.
    unfold eval_addressing, eval_addressing32, eval_addressing64 in *.
    destruct Archi.ptr64 eqn:PTR64.

    {
      unfold Genv.symbol_address in *.
      inv ADDRR.
      inv ADDRW.
      destruct (Genv.find_symbol genv sym).
      2: discriminate.
      
      rewrite <- READ.
      eapply Mem.load_store_other with (chunk := chunkw) (v := valw) (b := b).
      exact STORE.
      right.
      tauto.
    }

    {
      unfold Genv.symbol_address in *.
      inv ADDRR.
      inv ADDRW.
      destruct (Genv.find_symbol genv sym).
      2: discriminate.
      
      rewrite <- READ.
      eapply Mem.load_store_other with (chunk := chunkw) (v := valw) (b := b).
      exact STORE.
      right.
      tauto.
    }
  Qed.

  Lemma load_store_glob_away :
    (can_swap_accesses_ofs (Ptrofs.unsigned ofsr) chunkr (Ptrofs.unsigned ofsw) chunkw) = true ->
    Mem.loadv chunkr m2 addrr = Some valr.
  Proof.
    intro SWAP.
    unfold can_swap_accesses_ofs in SWAP.
    repeat rewrite andb_true_iff in SWAP.
    repeat rewrite orb_true_iff in SWAP.
    repeat rewrite Z.leb_le in SWAP.
    apply load_store_glob_away1.
    all: tauto.
  Qed.
  End SAME_GLOBALS.
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
  destruct (can_swap_accesses_ofs z0 chunk' z chunk) eqn:SWAP.
  2: discriminate.
  simpl in *.
  eapply load_store_away; eassumption.
  }
  { (* Aglobal / Aglobal *)
    destruct args. 2: discriminate.
    destruct args'. 2: discriminate.
    simpl in *.
    destruct (peq i i1).
    {
      subst i1.
      rewrite negb_false_iff in OVERLAP.
      eapply load_store_glob_away; eassumption.
    }
    eapply load_store_diff_globals; eassumption.
  }
Qed.

End SOUNDNESS.
