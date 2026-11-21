/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.OuterRootLeaf

/-!
# Cost of routing an outer carry-save leaf to a root contraction

The long fields, including arbitrary physical index padding, take a constant number of scans.
Fixed powers of the metadata and the binary path and count lengths fit in the block count.
-/

public section

namespace Cslib.Complexity.CountingSimulation.OuterRootLeaf

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeATM OuterRootLeafRequest

/-- The entire leaf setup, including serialization, fits within a constant times the block count. -/
theorem exists_setup_clock (k states d : ℕ) : ∃ K, ∀ {t : ℕ}, 2 ≤ t →
    ∀ (path bits : List Bool) (carry : Bool),
    let L := 2 * (k + 1) * numBlocks t
    let w := paddedTime t + 1
    let x := source k states t path carry bits
    bits.length + path.length ≤ CarrySaveCountingRoot.sizeBudget (2 ^ L) w →
      path.length + 2 * (encInput x).length + 9 + longSize x + shortSize x ^ d ≤
        K * (numBlocks t + 1) := by
  obtain ⟨A, E, hA⟩ :=
    (computableInPolyTime_outerRootTemplate k states).polyBounded_length.exists_le
  obtain ⟨B, hB⟩ := exists_size_pow_le_numBlocks 1
  let H := 2 * (k + 1)
  let J := 4 * H + B + 10
  let P := fun z : ℕ => A * (z + 1) ^ E + 2 * (J.size + z) + z + 3
  have poly : PolynomiallyBounded (fun z => 8 * P z + P z ^ d + 33) := by
    dsimp [P]
    fun_prop
  obtain ⟨F, D, hF⟩ := polynomiallyBounded_iff_le.mp poly
  obtain ⟨G, hG⟩ := exists_size_pow_le_numBlocks D
  refine ⟨10 * J + F * G, ?_⟩
  intro t ht path bits carry L w x hbudget
  let z := (t + 2).size
  let q := numBlocks t
  have hq : q ≤ t := (Nat.ceilDiv_le_iff (one_le_blockLength t)).mpr
    (Nat.le_mul_of_pos_right _ (one_le_blockLength t))
  have hqs : (q + 1).size ≤ z := Nat.size_le_size (by omega)
  have hts : t.size ≤ z := Nat.size_le_size (by omega)
  have hw : w.size ≤ z + 2 := by
    have h := (Nat.size_le_size (paddedTime_add_one_le ht)).trans (Nat.size_mul_le 2 t)
    change w.size ≤ 2 + t.size at h
    omega
  have hz := hB t
  change (z + 1) ^ 1 ≤ B * (q + 1) at hz
  rw [pow_one] at hz
  have hl : L = H * q := rfl
  have hL : L ≤ H * (q + 1) := hl ▸ Nat.mul_le_mul_left _ (Nat.le_succ q)
  have hlen : bits.length + path.length + (L + 1) ≤ J * (q + 1) := by
    rw [CarrySaveCountingRoot.sizeBudget, Nat.clog_pow _ _ one_lt_two] at hbudget
    have h := Nat.size_le_self L
    dsimp only [J]
    rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc]
    omega
  have hpath : path.length.size ≤ J.size + z := (Nat.size_le_size
    (show path.length ≤ J * (q + 1) by omega)).trans ((Nat.size_mul_le _ _).trans (by omega))
  have hcount : (L + 1).size ≤ J.size + z := (Nat.size_le_size
    (show L + 1 ≤ J * (q + 1) by omega)).trans ((Nat.size_mul_le _ _).trans (by omega))
  have htempl : (RootBalanceRequest.encPublic (outerRootTemplate k states t)).length ≤
      A * (z + 1) ^ E := by
    apply (hA t).trans
    rw [length_encNat_eq_size]
    gcongr
  have hc : x.count.length = L + 1 := by
    change (encNat (2 ^ L)).length = L + 1
    rw [length_encNat_eq_size, Nat.size_pow]
  have hwidth : x.width.length = w.size := length_encNat_eq_size _
  have hs : shortSize x ≤ P z := by
    change (RootBalanceRequest.encPublic (outerRootTemplate k states t)).length +
      x.count.length.size + path.length.size + x.width.length + 1 ≤ _
    rw [hc, hwidth]
    dsimp only [P]
    omega
  have hlong : longSize x ≤ J * (q + 1) := by
    change x.count.length + path.length + bits.length ≤ _
    omega
  have henc := encInput_length_le x
  have hfinal : 8 * P z + P z ^ d + 33 ≤ F * G * (q + 1) := by
    rw [Nat.mul_assoc]
    exact (hF z).trans (Nat.mul_le_mul_left _ (hG t))
  have hpow := Nat.pow_le_pow_left hs d
  change _ ≤ (10 * J + F * G) * (q + 1)
  rw [Nat.add_mul, Nat.mul_assoc]
  omega

end Cslib.Complexity.CountingSimulation.OuterRootLeaf
