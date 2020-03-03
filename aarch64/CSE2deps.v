Require Import BoolEqual Coqlib.
Require Import AST Integers Floats.
Require Import Values Memory Globalenvs Events.
Require Import Op.


Definition can_swap_accesses_ofs ofsr chunkr ofsw chunkw :=
     (0 <=? ofsw) && (ofsw <=? (Ptrofs.modulus - largest_size_chunk))
  && (0 <=? ofsr) && (ofsr <=? (Ptrofs.modulus - largest_size_chunk))
  && ((ofsw + size_chunk chunkw <=? ofsr) ||
      (ofsr + size_chunk chunkr <=? ofsw)).

Definition may_overlap chunk addr args chunk' addr' args' :=
  match addr, addr', args, args' with
  | (Aindexed ofs), (Aindexed ofs'),
    (base :: nil), (base' :: nil) =>
    if peq base base'
    then negb (can_swap_accesses_ofs (Int64.unsigned ofs') chunk' (Int64.unsigned ofs) chunk)
    else true  | _, _, _, _ => true
  end.
