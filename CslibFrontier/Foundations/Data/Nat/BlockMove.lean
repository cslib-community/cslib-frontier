/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Moving two adjacent finite blocks in raw natural indices

The prefix is fixed and the following two blocks exchange places. Every index beyond the
three-block interval stays fixed as well, so raw binary table entries retain a total inverse.
On the two bounded blocks this is the existing `finAddFlip`, translated past the prefix.
The native probe-append program uses the operation to move its old left probe behind the
right body and probe, without choosing an abstract dart inverse at runtime.
-/

public section

namespace Nat

/-- Exchange the blocks of lengths `moved` and `after`, fixing the prefix and every raw
index past the three blocks. Zero-length blocks require no special input convention. -/
@[expose] def blockMove (before moved after i : ℕ) : ℕ :=
  if i < before then i
  else if i < before + moved then i + after
  else if i < before + moved + after then i - moved
  else i

/-- On a bounded suffix index, the raw block move is the existing finite block exchange. -/
theorem blockMove_eq_finAddFlip (before moved after : ℕ)
    (i : Fin (moved + after)) :
    blockMove before moved after (before + i.val) = before + (finAddFlip i).val := by
  unfold blockMove
  rw [ite_eq_right (by omega)]
  by_cases hi : i.val < moved
  · rw [ite_eq_left (by omega), finAddFlip_apply_mk_left hi]
    change before + i.val + after = before + (after + i.val)
    omega
  · rw [ite_eq_right (by omega), ite_eq_left (by omega),
      finAddFlip_apply_mk_right (by omega) i.isLt]
    change before + i.val - moved = before + (i.val - moved)
    omega

/-- Exchanging the two lengths gives the literal inverse on every raw index, including
out-of-range binary entries. This does not assume an index or table validity guard. -/
theorem blockMove_inverse (before moved after i : ℕ) :
    blockMove before after moved (blockMove before moved after i) = i := by
  by_cases hp : i < before
  · simp only [blockMove, ite_eq_left hp]
  by_cases hb : i < before + moved + after
  · let j : Fin (moved + after) := ⟨i - before, by omega⟩
    have he : before + j.val = i := by dsimp [j]; omega
    have hf : finAddFlip (finAddFlip j) = j := by simp [finAddFlip]
    calc
      _ = blockMove before after moved (blockMove before moved after (before + j.val)) := by
        rw [he]
      _ = before + (finAddFlip (finAddFlip j)).val := by
        rw [blockMove_eq_finAddFlip, blockMove_eq_finAddFlip]
      _ = i := by rw [hf]; exact he
  · have hs : ¬i < before + moved := by omega
    have hp' : ¬i < before + after := by omega
    have hb' : ¬i < before + after + moved := by omega
    simp only [blockMove, ite_eq_right hp, ite_eq_right hs, ite_eq_right hb,
      ite_eq_right hp', ite_eq_right hb']

/-- An index inside the actual three blocks stays inside their unchanged total length. -/
theorem blockMove_lt {before moved after i : ℕ} (hi : i < before + moved + after) :
    blockMove before moved after i < before + moved + after := by
  by_cases hp : i < before
  · simp only [blockMove, ite_eq_left hp]
    omega
  · let j : Fin (moved + after) := ⟨i - before, by omega⟩
    have he : before + j.val = i := by dsimp [j]; omega
    rw [← he, blockMove_eq_finAddFlip]
    have h := (finAddFlip j).isLt
    omega

/-- Moving an empty block fixes every raw index. -/
theorem blockMove_zero_moved (a b i : ℕ) : Nat.blockMove a 0 b i = i := by
  simp only [Nat.blockMove]
  split_ifs <;> omega

/-- Moving a block past an empty block fixes every raw index. -/
theorem blockMove_zero_after (a b i : ℕ) : Nat.blockMove a b 0 i = i := by
  simp only [Nat.blockMove]
  split_ifs <;> omega

end Nat
