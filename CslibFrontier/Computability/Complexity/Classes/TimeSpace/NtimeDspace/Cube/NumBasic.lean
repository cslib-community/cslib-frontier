/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.Pieces
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.SumProduct.NatList

/-!
# Numbers for the data of the formula

The explicit programs of Lemma 6.4 work on natural numbers. This module fixes how the data of the
formula are written as numbers, once for all program modules:

* a list of numbers by `NatList.enc` (self-delimiting, head in the low bits);
* a multiset of numbers by the code of its increasing list (`encMs`), so equal multisets have
  equal codes;
* a label `(σ, τ)` by `enc [encMs σ, encMs τ]` (`encLabel`);
* an integer by the zigzag code `0, -1, 1, -2, 2, … ↦ 0, 1, 2, 3, 4, …` (`zz`, inverse `unzz`);
* a place of a half-routing by `plNum` (`none ↦ 0`, the corners `x, y, u, v ↦ 1, 2, 3, 4`), a typed
  place `(pl, i)` by `plNum pl + 8 i` (`tgtNum`), and a multiset of typed places by the code of
  its image (`encTs`).
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube.Num

open SumProduct.NatList

/-- The code of a multiset of numbers: the code of its increasing list. -/
def encMs (σ : Multiset ℕ) : ℕ := enc (σ.sort (· ≤ ·))

/-- The code of a label. -/
def encLabel (l : Label) : ℕ := enc [encMs l.1, encMs l.2]

/-- The zigzag code of an integer. -/
def zz (v : ℤ) : ℕ := if 0 ≤ v then 2 * v.toNat else 2 * (-v).toNat - 1

/-- The integer of a zigzag code. -/
def unzz (n : ℕ) : ℤ := if n % 2 = 0 then ((n / 2 : ℕ) : ℤ) else -(((n + 1) / 2 : ℕ) : ℤ)

/-- The number of a corner. -/
def cornerNum : Corner → ℕ
  | .x => 1
  | .y => 2
  | .u => 3
  | .v => 4

/-- The number of a place. -/
def plNum : HPlace → ℕ
  | none => 0
  | some c => cornerNum c

/-- The number of a typed place. -/
def tgtNum (t : HPlace × ℕ) : ℕ := plNum t.1 + 8 * t.2

/-- The code of a multiset of typed places. -/
def encTs (T : Multiset (HPlace × ℕ)) : ℕ := encMs (T.map tgtNum)

theorem encMs_injective : Function.Injective encMs := by
  intro σ τ h
  have h' := enc_injective h
  rw [← Multiset.sort_eq σ (· ≤ ·), ← Multiset.sort_eq τ (· ≤ ·), h']

theorem unzz_zz (v : ℤ) : unzz (zz v) = v := by
  unfold zz unzz
  split_ifs with h1 h2 h2 <;> omega

theorem cornerNum_injective : Function.Injective cornerNum := by
  intro a b h; cases a <;> cases b <;> simp_all [cornerNum]

theorem plNum_lt (pl : HPlace) : plNum pl < 5 := by
  rcases pl with _ | c
  · simp [plNum]
  · cases c <;> simp [plNum, cornerNum]

theorem plNum_injective : Function.Injective plNum := by
  intro a b h
  rcases a with _ | a <;> rcases b with _ | b
  · rfl
  · cases b <;> simp [plNum, cornerNum] at h
  · cases a <;> simp [plNum, cornerNum] at h
  · simp only [plNum] at h; rw [cornerNum_injective h]

theorem tgtNum_injective : Function.Injective tgtNum := by
  intro a b h
  have ha := plNum_lt a.1; have hb := plNum_lt b.1
  unfold tgtNum at h
  have h1 : plNum a.1 = plNum b.1 := by omega
  have h2 : a.2 = b.2 := by omega
  exact Prod.ext (plNum_injective h1) h2

theorem encTs_injective : Function.Injective encTs := by
  intro S T h
  exact Multiset.map_injective tgtNum_injective (encMs_injective h)

end Cslib.Complexity.NtimeDspace.Cube.Num
