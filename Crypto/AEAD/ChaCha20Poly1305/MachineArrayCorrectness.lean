import Crypto.AEAD.ChaCha20Poly1305.MachineCorrectness

namespace Crypto.ChaCha20Poly1305.Machine
open Fast
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
attribute [local irreducible] Fast.mulReduce Fast.Limbs.addNat

theorem addArray_eq (a : Array UInt8) (offset : Nat) (h : Limbs) :
    WordBlocks.addWords h (loadWords a offset).w0 (loadWords a offset).w1
      (loadWords a offset).w2 (loadWords a offset).w3 =
    h.addNat (bytesToNatLE ((a.toList.drop offset).take 16) + 256^16) := by
  have hw := loadWords_bound a offset
  rw [WordBlocks.addWords_eq _ _ _ _ _ hw.1 hw.2.1 hw.2.2.1 hw.2.2.2]
  change h.addNat ((loadWords a offset).value + 2^128) = _
  rw [loadWords_value]

theorem blocksList_full (r : RKey) (xs : List UInt8) (h : Limbs) (hlen : 16 ≤ xs.length) :
    blocksList r xs h = blocksList r (xs.drop 16)
      (mulReduce (h.addNat (bytesToNatLE (xs.take 16) + 256^16)) r) := by
  cases xs with
  | nil => simp at hlen
  | cons b bs =>
      have hl : ((b::bs).take 16).length = 16 := by
        simp only [List.length_take]
        exact Nat.min_eq_left hlen
      exact (blocksList.eq_2 r h b bs).trans
        (congrArg (fun k => blocksList r ((b::bs).drop 16)
          (mulReduce (h.addNat (bytesToNatLE ((b::bs).take 16) + 256^k)) r)) hl)

theorem blocksArray_eq (r : RKey) (a : Array UInt8) (n offset : Nat) (h : Limbs)
    (hn : offset + 16*n ≤ a.size) :
    blocksArray r a n offset h = blocksList r (a.toList.drop offset) h := by
  fun_induction blocksArray r a n offset h with
  | case1 offset h =>
      apply congrArg (fun xs => blocksList r xs h)
      rw [Array.toList_extract]
      change (a.toList.drop offset).take (a.size-offset) = _
      exact List.take_of_length_le (by simp)
  | case2 n offset h ih =>
      have hlen : 16 ≤ (a.toList.drop offset).length := by simp; omega
      have hadd := congrArg (fun x => mulReduce x r) (addArray_eq a offset h)
      have hd : a.toList.drop (offset+16) = (a.toList.drop offset).drop 16 := by
        simp only [List.drop_drop]
      calc
        blocksArray r a n (offset+16) (arrayStep r a offset h) =
            blocksList r (a.toList.drop (offset+16)) (arrayStep r a offset h) := ih (by omega)
        _ = blocksList r ((a.toList.drop offset).drop 16) (arrayStep r a offset h) :=
          congrArg (fun xs => blocksList r xs (arrayStep r a offset h)) hd
        _ = blocksList r ((a.toList.drop offset).drop 16)
              (mulReduce (h.addNat (bytesToNatLE ((a.toList.drop offset).take 16) + 256^16)) r) :=
          congrArg (fun x => blocksList r ((a.toList.drop offset).drop 16) x) hadd
        _ = blocksList r (a.toList.drop offset) h := (blocksList_full r _ h hlen).symm

theorem poly1305Array_correct (message key : Array UInt8) :
    poly1305Array message key = Spec.poly1305 message.toList key.toList := by
  have hr := decodeWords_eq (loadWords key 0) (loadWords_bound ..)
  have hs := loadWords_value key 16
  have hv := loadWords_value key 0
  simp only [List.drop_zero] at hv
  rw [hv] at hr
  let rNat := bytesToNatLE (key.toList.take 16) &&& 0x0ffffffc0ffffffc0ffffffc0fffffff
  have hb := blocksList_correct rNat message.toList ⟨0,0,0,0,0⟩ zero_stateBound (clamped_lt_limbRange key.toList)
  unfold poly1305Array
  dsimp only
  rw [hr, blocksArray_eq _ _ _ _ _ (by omega), List.drop_zero,
    finish_eq _ _ hb.1 (loadWords_bound ..), hs, hb.2]
  simp only [Spec.poly1305, ← bytesToNatLE_correct, ← natToBytesLE_correct]
  rfl

end Crypto.ChaCha20Poly1305.Machine
