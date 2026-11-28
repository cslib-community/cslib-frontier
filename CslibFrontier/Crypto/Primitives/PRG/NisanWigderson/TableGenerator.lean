/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Boolean.HardnessAmplification.PolySchedule
public import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.BitPolynomial
public import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.Derandomization
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The Nisan–Wigderson generator of a truth table

A function `f` of `n` bits whose circuit complexity is polynomial in `n + S + m` gives a
pseudorandom generator of `m` bits that fools tests of size `S`, with seed length quadratic in
`n + log (n + S + m + 1)` [NisanWigderson1994], [ImpagliazzoWigderson1997]. This is the
polynomial-regime assembly of the polynomial-hardness encoding
(`Cslib.HardnessEncoding.exists_isAverageCaseHard_polyEncode`) and the Nisan–Wigderson generator
over the bit-indexed polynomial design (`Cslib.Crypto.PRG.NisanWigderson.Design.binaryPolynomial`),
fooling in counting form (`Cslib.Crypto.PRG.NisanWigderson.abs_card_div_sub_card_div_lt`).

**Parameters.** For tests of size `S` on `m` bits put

* `ℓ = ⌊log₂ m⌋ + 1` (`tableLog`), so that `m < 2 ^ ℓ` and `2 ^ (ℓ - 1) ≤ m` for `m ≥ 1`;
* `s = S + 20 (m + 1) ^ 3 + 2` (`tableHardness`), the hardness to which the encoding is taken:
  it satisfies `S + 1 + m (2 ^ (ℓ - 1) (2 (ℓ - 1) + 3) + 1) + 1 ≤ s` and `6 m < s`, which are the
  hypotheses of the fooling inequality with overlap `a = ℓ - 1` and `ε = 1 / 6`;
* `N = polyArity n s` (`tableBlock`), the number of bits of the encoding of `f`, which is the block
  size of the design;
* `e = binaryFieldDegree N` and the seed length `N 2 ^ e` (`tableSeedLength`).

**How a seed is read.** The design is `Design.binaryPolynomial N ℓ`, whose universe is the
`N 2 ^ e` cells `finProdFinEquiv (j, v)`, `j < N` the row and `v < 2 ^ e` the column, numbered
row-major, i.e. cell `j * 2 ^ e + v`; the seed `z : BitString (N 2 ^ e)` is read with this
numbering. Output bit `i < m` is the value of the encoding `polyEncode n s f` on the `N` bits
`x_j = z (finProdFinEquiv (j, v_{i,j}))`, `j < N`, where `v_{i,j} < 2 ^ e` is the column whose
bits (least significant first, `BitString.equivFin`) are the bits of the field element
`A_i (r_j)`: `i` is read as the bit string `(BitString.equivFin ℓ).symm i`, `A_i (x)` is the
polynomial `∑_t i_t x ^ t` over `BinaryField e`, and `r_j` is the field element numbered `j`
(`binaryFieldPoints`). Bit `c` of `A_i (r_j)` is the parity of `i` on the exponents `t` for which
bit `c` of `r_j ^ t` is set (`Design.restrict_binaryPolynomial`, `bits_bitPoly_eq_parityOn`). So
the encoding point of output bit `i` is read from the seed one cell per row, and the encoding
`polyEncode n s f` (a function of `N` bits whose truth table is that of `f` over the binary field of
degree `4 b`) is evaluated at it.

## Main definitions

* `Cslib.Crypto.PRG.NisanWigderson.tableHardness`, `tableLog`, `tableBlock`, `tableSeedLength`:
  the parameters.
* `Cslib.Crypto.PRG.NisanWigderson.tableDesign`: the first `m` blocks of the bit-indexed
  polynomial design.
* `Cslib.Crypto.PRG.NisanWigderson.tableGenerator`: the generator of a table.
* `Cslib.Crypto.PRG.NisanWigderson.TableGeneratorFools`: the generator of the tables of a hardness
  exponent fools small tests.

## Main results

* `Cslib.Crypto.PRG.NisanWigderson.tableSeedLength_le`: the seed length is quadratic in
  `n + log (n + S + m + 1)`.
* `Cslib.Crypto.PRG.NisanWigderson.exists_tableGenerator_fools`: **the generator of a hard table
  fools small tests**.

## References

* [N. Nisan, A. Wigderson, *Hardness vs randomness*][NisanWigderson1994]
* [R. Impagliazzo, A. Wigderson, *P = BPP if E requires exponential circuits: Derandomizing the
  XOR lemma*][ImpagliazzoWigderson1997]
-/

@[expose] public section

namespace Cslib.Crypto.PRG.NisanWigderson

open Finset Cslib.Circuits Cslib.Circuits.Boolean Cslib.HardnessEncoding

/-- The hardness `s = S + 20 (m + 1) ^ 3 + 2` of the encoding, for tests of size `S` on `m` bits. -/
def tableHardness (S m : ℕ) : ℕ := S + 20 * (m + 1) ^ 3 + 2

/-- The design parameter `ℓ = ⌊log₂ m⌋ + 1`, so that `m < 2 ^ ℓ`. -/
def tableLog (m : ℕ) : ℕ := Nat.log 2 m + 1

/-- The block size `N = polyArity n s` of the design: the arity of the encoding of a function of
`n` bits for hardness `s = tableHardness S m`. -/
def tableBlock (n S m : ℕ) : ℕ := polyArity n (tableHardness S m)

/-- The seed length of the generator of a table on `n` bits for tests of size `S` on `m` bits:
`N 2 ^ e` for `N = tableBlock n S m` and `e = binaryFieldDegree N`. -/
def tableSeedLength (n S m : ℕ) : ℕ :=
  tableBlock n S m * 2 ^ binaryFieldDegree (tableBlock n S m)

/-- There are at least `m` blocks in the design with `ℓ = tableLog m`. -/
theorem le_two_pow_tableLog (m : ℕ) : m ≤ 2 ^ tableLog m :=
  (Nat.lt_pow_succ_log_self (by norm_num) m).le

/-- The first `m` blocks of the bit-indexed polynomial design `Design.binaryPolynomial N ℓ` for
`N = tableBlock n S m` and `ℓ = tableLog m`: a design of `m` blocks of `N` cells in the universe of
`tableSeedLength n S m` cells, any two sharing at most `ℓ - 1` cells. -/
noncomputable def tableDesign (n S m : ℕ) :
    Design (tableSeedLength n S m) (tableBlock n S m) (tableLog m - 1) m :=
  (Design.binaryPolynomial (tableBlock n S m) (tableLog m)).subfamily
    (Fin.castLEEmb (le_two_pow_tableLog m))

/-- **The generator of a truth table**: the Nisan–Wigderson generator, over the bit-indexed
polynomial design, of the polynomial-regime encoding of `f`. Output bit `i` is
`polyEncode n (tableHardness S m) f` applied to the bits of the seed in block `i` of
`Design.binaryPolynomial N ℓ`, read one cell per row (see the module documentation). -/
noncomputable def tableGenerator (n S m : ℕ) (f : BooleanFunction n) :
    BitString (tableSeedLength n S m) → BitString m :=
  generator (tableDesign n S m) (polyEncode n (tableHardness S m) f)

/-- A bound used twice: `n + s + 1 ≤ 23 X ^ 3` for `X = n + S + m + 1` and `s = tableHardness S m`.
-/
private theorem n_add_tableHardness_le (n S m : ℕ) :
    n + tableHardness S m + 1 ≤ 23 * (n + S + m + 1) ^ 3 := by
  have hX : 1 ≤ n + S + m + 1 := by omega
  have h1 : n + S + m + 1 ≤ (n + S + m + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have h2 : (m + 1) ^ 3 ≤ (n + S + m + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have h3 : 1 ≤ (n + S + m + 1) ^ 3 := Nat.one_le_pow _ _ hX
  unfold tableHardness
  omega

/-- **The seed length is quadratic** in `n + log (n + S + m + 1)`. -/
theorem tableSeedLength_le : ∃ c : ℕ, ∀ n S m : ℕ,
    tableSeedLength n S m ≤ c * (n + Nat.log 2 (n + S + m + 1) + 1) ^ 2 := by
  obtain ⟨c1, hc1⟩ := polyArity_le
  refine ⟨2 * (9 * c1) ^ 2, fun n S m => ?_⟩
  have hlog : Nat.log 2 (n + tableHardness S m + 1) ≤ 3 * Nat.log 2 (n + S + m + 1) + 8 := by
    have hlt : n + S + m + 1 < 2 ^ (Nat.log 2 (n + S + m + 1) + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) _
    have h3 : (n + S + m + 1) ^ 3 < (2 ^ (Nat.log 2 (n + S + m + 1) + 1)) ^ 3 :=
      Nat.pow_lt_pow_left hlt (by norm_num)
    have h4 : n + tableHardness S m + 1 < 2 ^ (3 * Nat.log 2 (n + S + m + 1) + 8) := by
      calc n + tableHardness S m + 1 ≤ 23 * (n + S + m + 1) ^ 3 := n_add_tableHardness_le n S m
        _ < 32 * (2 ^ (Nat.log 2 (n + S + m + 1) + 1)) ^ 3 := by omega
        _ = 2 ^ (3 * Nat.log 2 (n + S + m + 1) + 8) := by
          rw [← pow_mul, show (32 : ℕ) = 2 ^ 5 by norm_num, ← pow_add]
          congr 1
          ring
    have := Nat.log_lt_of_lt_pow (by omega) h4
    omega
  have hN : tableBlock n S m ≤ 9 * c1 * (n + Nat.log 2 (n + S + m + 1) + 1) := by
    have h := hc1 n (tableHardness S m)
    calc tableBlock n S m ≤ c1 * (n + Nat.log 2 (n + tableHardness S m + 1) + 1) := h
      _ ≤ c1 * (9 * (n + Nat.log 2 (n + S + m + 1) + 1)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 9 * c1 * (n + Nat.log 2 (n + S + m + 1) + 1) := by ring
  calc tableSeedLength n S m ≤ 2 * tableBlock n S m ^ 2 := Design.seedLength_binaryPolynomial_le _
    _ ≤ 2 * (9 * c1 * (n + Nat.log 2 (n + S + m + 1) + 1)) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hN 2)
    _ = 2 * (9 * c1) ^ 2 * (n + Nat.log 2 (n + S + m + 1) + 1) ^ 2 := by ring

/-- **The generator of tables of hardness exponent `c` fools small tests**: if `f` on `n` bits
needs more than `c (n + S + m + 1) ^ c` gates, then every test of at most `S` gates on `m` bits
accepts the output of `tableGenerator n S m f` on a fraction of the `2 ^ tableSeedLength n S m`
seeds that differs by less than `1 / 6` from the fraction of strings it accepts. -/
def TableGeneratorFools (c : ℕ) : Prop :=
  ∀ (n S m : ℕ) (f : BooleanFunction n),
    c * (n + S + m + 1) ^ c < complexity interpretation (single f) →
    ∀ test : BooleanFunction m, complexity interpretation (single test) ≤ S →
      |(#{z | test (tableGenerator n S m f z) = true} : ℝ) / 2 ^ tableSeedLength n S m -
        #{r | test r = true} / 2 ^ m| < 1 / 6

/-- **The generator of a hard table fools small tests** (`TableGeneratorFools`): for some `c`,
if `f` on `n` bits needs more than `c (n + S + m + 1) ^ c` gates, then every test of at most `S`
gates on `m` bits accepts the output of `tableGenerator n S m f` on a fraction of the
`2 ^ tableSeedLength n S m` seeds that differs by less than `1 / 6` from the fraction of strings it
accepts. For `m = 0` the test is constant and the two fractions are equal. -/
theorem exists_tableGenerator_fools : ∃ c : ℕ, TableGeneratorFools c := by
  obtain ⟨c0, hc0⟩ := exists_isAverageCaseHard_polyEncode
  refine ⟨c0 * 23 ^ c0 + 3 * c0, fun n S m f hhard test htest => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have e : BitString 0 := fun i => Fin.elim0 i
    have h2 : ∀ r : BitString 0, r = e := fun r => Subsingleton.elim _ _
    simp only [h2]
    generalize tableSeedLength n S 0 = s
    cases test e
    · simp
    · simp [Finset.card_univ]
  have hs2 : 2 ≤ tableHardness S m := by unfold tableHardness; omega
  have hX1 : 1 ≤ n + S + m + 1 := by omega
  have hH : c0 * (n + tableHardness S m + 1) ^ c0 < complexity interpretation (single f) := by
    refine lt_of_le_of_lt ?_ hhard
    calc c0 * (n + tableHardness S m + 1) ^ c0 ≤ c0 * (23 * (n + S + m + 1) ^ 3) ^ c0 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (n_add_tableHardness_le n S m) _)
      _ = c0 * 23 ^ c0 * (n + S + m + 1) ^ (3 * c0) := by rw [mul_pow, ← pow_mul]; ring
      _ ≤ (c0 * 23 ^ c0 + 3 * c0) * (n + S + m + 1) ^ (3 * c0) :=
          Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
      _ ≤ (c0 * 23 ^ c0 + 3 * c0) * (n + S + m + 1) ^ (c0 * 23 ^ c0 + 3 * c0) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX1 (by omega))
  have hf := hc0 n (tableHardness S m) f hs2 hH
  have hm0 : m ≠ 0 := by omega
  have ha1 : 2 ^ (tableLog m - 1) ≤ m := by
    simpa [tableLog] using Nat.pow_log_le_self 2 hm0
  have ha2 : tableLog m - 1 ≤ m := by
    have := Nat.lt_two_pow_self (n := tableLog m - 1)
    omega
  have hcoef : 2 ^ (tableLog m - 1) * (2 * (tableLog m - 1) + 3) + 1 ≤ m * (2 * m + 3) + 1 := by
    have := Nat.mul_le_mul ha1 (by omega : 2 * (tableLog m - 1) + 3 ≤ 2 * m + 3)
    omega
  have hsum : S + 1 + m * (2 ^ (tableLog m - 1) * (2 * (tableLog m - 1) + 3) + 1) + 1 ≤
      tableHardness S m := by
    have h1 := Nat.mul_le_mul_left m hcoef
    have h2 : m * (m * (2 * m + 3) + 1) ≤ 20 * (m + 1) ^ 3 := by nlinarith [Nat.zero_le (m ^ 3)]
    unfold tableHardness
    omega
  have hmε : (m : ℝ) < 1 / 6 * (tableHardness S m : ℕ) := by
    have h1 : m + 1 ≤ (m + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    have h2 : 6 * m < tableHardness S m := by
      unfold tableHardness
      omega
    have h3 : (6 * m : ℝ) < (tableHardness S m : ℕ) := by exact_mod_cast h2
    linarith
  exact abs_card_div_sub_card_div_lt (tableDesign n S m) hf hsum hmε test htest

end Cslib.Crypto.PRG.NisanWigderson
