/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.HardnessEncoding.Program
public import CslibFrontier.Computability.MCSP.NP
public import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.TableGenerator
import CslibFrontier.Foundations.Data.BitString.Binary
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The generator of a truth table on bit lists

`Cslib.Crypto.PRG.NisanWigderson.tableGenerator n S m f` is the Nisan–Wigderson generator of the
polynomial-regime encoding of a function `f` of `n` bits over the bit-indexed polynomial design.
This file computes it from the truth table of `f` by a program on bit lists
(`Cslib.Crypto.PRG.NisanWigderson.tableGeneratorList`), and proves that the program is correct
(`Cslib.Crypto.PRG.NisanWigderson.tableGeneratorList_eq`). Polynomial time is shown in
`Cslib.Crypto.PRG.NisanWigderson.TableGeneratorListPolyTime`.

**The program.** For a truth table `T` of length `2 ^ n` (so `n = ⌊log₂ |T|⌋`) and a seed `z`:

* the parameters `s`, `ℓ`, `N` and `e = binaryFieldDegree N` are those of `tableGenerator`;
* output bit `i < m` is the encoding program `Cslib.HardnessEncoding.encodedProgramAt` of the
  decider `u ↦ tableValue T (u.take n)` (the function of the first `n` bits, read as
  `Cslib.MCSP.tableFunction n T`), run on the `N` bits `z_{cell i j}`, `j < N`;
* the cell of row `j` is `v + 2 ^ e j`, where the column `v` has the bits of `A_i (r_j)`. These
  are computed over `Cslib.BinaryField e` in coordinates by Horner's rule (`hornerWord`): the
  bits of `i` are the coefficients, and `r_j` is the word of the bits of `j`.

The truth table is read as `Cslib.MCSP.tableFunction n T` reads it: the first input bit is the
least significant bit of the position in `T`.

## Main definitions

* `Cslib.Crypto.PRG.NisanWigderson.hornerWord`: Horner's rule on coordinate words.
* `Cslib.Crypto.PRG.NisanWigderson.tableCell`: the seed cell read in a row.
* `Cslib.Crypto.PRG.NisanWigderson.tableGeneratorList`: the generator of a truth table on lists.

## Main results

* `Cslib.Crypto.PRG.NisanWigderson.encodedProgramAt_polyEncode`: the encoding program computes
  `polyEncode` of a table function.
* `Cslib.Crypto.PRG.NisanWigderson.tableGeneratorList_eq`: **the program computes
  `tableGenerator`** of the function of the truth table.
* `Cslib.Crypto.PRG.NisanWigderson.tableGeneratorList_take`: the program reads only the first
  `tableSeedLength` bits of its seed.

## References

* [M. Sudan, L. Trevisan, S. Vadhan, *Pseudorandom generators without the XOR lemma*]
  [SudanTrevisanVadhan2001]
* [M. L. Carmosino, R. Impagliazzo, V. Kabanets, A. Kolokolova, *Learning algorithms from natural
  proofs*][CarmosinoImpagliazzoKabanetsKolokolova2016], §3.1, proof of Theorem 3.6
* [N. Nisan, A. Wigderson, *Hardness vs randomness*][NisanWigderson1994]
-/

@[expose] public section

namespace Cslib.Crypto.PRG.NisanWigderson

open Cslib.HardnessEncoding Cslib.BinaryField Cslib.BitString Cslib.Circuits
  Cslib.Circuits.Boolean

/-! ### Horner's rule in coordinates -/

/-- **Horner's rule on coordinate words**: the value at `x`, over the field with multiplication
table `tab` and coordinates of width `e`, of the polynomial whose coefficients are the bits `c`
in increasing degree. -/
def hornerWord (tab : List (List (List Bool))) (e : ℕ) (x c : List Bool) : List Bool :=
  c.reverse.foldl (fun acc a => listXor e [if a then [true] else [], fieldMul tab acc x]) []

theorem hornerWord_cons (tab : List (List (List Bool))) (e : ℕ) (x : List Bool) (a : Bool)
    (c : List Bool) : hornerWord tab e x (a :: c) =
      listXor e [if a then [true] else [], fieldMul tab (hornerWord tab e x c) x] := by
  simp [hornerWord, List.reverse_cons, List.foldl_append]

/-- **Horner's rule computes `bitPoly`**: the coordinates `hornerWord` of the bits of `i` at the
point with coordinates `x` are those of `bitPoly i` at that point. -/
theorem fieldOfBits_hornerWord {e : ℕ} (he : e ≠ 0) (x : List Bool) :
    ∀ (ℓ : ℕ) (i : BitString ℓ),
      fieldOfBits (BinaryField.basis he) (hornerWord (fieldTable e) e x (List.ofFn i)) =
        bitPoly i (fieldOfBits (BinaryField.basis he) x)
  | 0, i => by simp [hornerWord, bitPoly]
  | ℓ + 1, i => by
    have ih := fieldOfBits_hornerWord he x ℓ (fun t => i t.succ)
    rw [List.ofFn_succ, hornerWord_cons, fieldOfBits_listXor]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      fieldOfBits_fieldMul (isMulTable_fieldTable he), ih]
    unfold bitPoly
    rw [Fin.sum_univ_succ, Finset.sum_mul]
    congr 1
    · cases h : i 0 <;> simp [fieldOfBits_one he]
    · refine Finset.sum_congr rfl fun t _ => ?_
      by_cases h : i t.succ = true <;> simp [h, pow_succ]

/-! ### The seed cell of a row -/

/-- **The seed cell of a row**: for output bit `i` and row `j`, the cell `v + 2 ^ e j` of the
seed, `v` the column whose bits are the coordinates of `A_i (r_j)` over `BinaryField e`, computed
by Horner's rule from the bits of `i` and of `j`. -/
def tableCell (e ℓ i j : ℕ) : ℕ :=
  binaryValue (hornerWord (fieldTable e) e (lowBits e j) (lowBits ℓ i)).reverse + 2 ^ e * j

/-- **The cell computed in coordinates is the cell of the design**: the cell of row `j` in block
`i` of `Design.binaryPolynomial N ℓ` is `finProdFinEquiv (j, v)` with the column `v` numbering
`A_i (r_j)`. -/
theorem tableCell_eq (N ℓ : ℕ) (hℓ : 0 < ℓ) (i : Fin (2 ^ ℓ)) (j : Fin N) :
    tableCell (binaryFieldDegree N) ℓ i j =
      (finProdFinEquiv (j, binaryFieldNum (binaryFieldDegree_ne_zero N)
        (bitPoly ((equivFin ℓ).symm i) (binaryFieldPoints N j))) : ℕ) := by
  set e := binaryFieldDegree N with he_def
  have he : e ≠ 0 := binaryFieldDegree_ne_zero N
  have hj : (j : ℕ) < 2 ^ e := lt_of_lt_of_le j.2 (le_two_pow_binaryFieldDegree N)
  have hx : lowBits e j = List.ofFn ((equivFin e).symm ⟨j, hj⟩) :=
    lowBits_eq_ofFn_equivFin_symm e ⟨j, hj⟩
  have hc : lowBits ℓ i = List.ofFn ((equivFin ℓ).symm i) := lowBits_eq_ofFn_equivFin_symm ℓ i
  set A := hornerWord (fieldTable e) e (lowBits e j) (lowBits ℓ i) with hA_def
  have hpt : fieldOfBits (BinaryField.basis he) (lowBits e j) = binaryFieldPoints N j := by
    rw [hx, fieldOfBits_ofFn he]
    exact (binaryFieldPoints_apply N j).symm
  have hA : fieldOfBits (BinaryField.basis he) A =
      bitPoly ((equivFin ℓ).symm i) (binaryFieldPoints N j) := by
    rw [hA_def, hc, fieldOfBits_hornerWord he _ ℓ, hpt]
  have hlen : A.length = e := by
    obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
    rw [hA_def, hc, List.ofFn_succ, hornerWord_cons, length_listXor]
  have hofFn : (List.ofFn fun c : Fin e => A.getD c false) = A := by
    refine List.ext_getElem (by simp [hlen]) fun k h₁ h₂ => ?_
    rw [List.getElem_ofFn, List.getD_eq_getElem _ _ (by omega)]
  have hv : binaryValue A.reverse =
      (binaryFieldNum he (bitPoly ((equivFin ℓ).symm i) (binaryFieldPoints N j)) : ℕ) := by
    rw [← hA, binaryFieldNum_apply,
      show BinaryField.equivBits he (fieldOfBits (BinaryField.basis he) A) =
        fun c : Fin e => A.getD c false from funext (equivBits_fieldOfBits he A),
      ← binaryValue_reverse_ofFn, hofFn]
  rw [tableCell, finProdFinEquiv_apply_val, ← hv]

/-! ### The generator on lists -/

/-- **The seed bits read for an output bit**: the `N` bits `z_{cell i j}`, `j < N`, at the cells of
block `i`; `e` is the field degree, `ℓ` the number of bits of the block index. -/
def tablePoint (N e ℓ : ℕ) (z : List Bool) (i : ℕ) : List Bool :=
  (List.range N).map fun j => z.getD (tableCell e ℓ i j) false

/-- Output bit `i` of the generator of the truth table `T` on `n` bits, for seed `z`: the encoding
program of the table function, at the point of the seed read in block `i`. -/
def tableOutput (S m n : ℕ) (T z : List Bool) (i : ℕ) : Bool :=
  encodedProgramAt (polyBlocks n (tableHardness S m))
    (fun u => MCSP.tableValue T (u.take n))
    (tablePoint (tableBlock n S m) (binaryFieldDegree (tableBlock n S m)) (tableLog m) z i)
    (polyBlock n (tableHardness S m))

/-- The generator of a truth table on bit lists: `n` is read as `Nat.log 2 |T|`. -/
def tableGeneratorList (S m : ℕ) (T z : List Bool) : List Bool :=
  (List.range m).map (tableOutput S m (Nat.log 2 T.length) T z)

/-! ### Correctness -/

/-- The language of the words whose first `n` bits, read as a position, index a one of `T`. -/
private def tableLang (n : ℕ) (T : List Bool) : Language Bool :=
  {u | MCSP.tableValue T (u.take n) = true}

/-- The encoding of the extension of a table function is the encoding slice of the language of
the table: the value of the slice at `M b` bits is read from the first `n` bits. -/
private theorem slice_eq_polyExtend (n s : ℕ) (T : List Bool) :
    Language.slice (tableLang n T) (polyBlocks n s * polyBlock n s) =
      polyExtend n s (MCSP.tableFunction n T) := by
  funext y
  rw [Bool.eq_iff_iff, Language.slice_eq_true_iff]
  have htake : (List.ofFn y).take n =
      List.ofFn fun i : Fin n => y (Fin.castLE (le_polyBlocks_mul n s) i) := by
    refine List.ext_getElem (by simp [le_polyBlocks_mul n s]) fun k h₁ h₂ => ?_
    simp
  change MCSP.tableValue T ((List.ofFn y).take n) = true ↔ _
  rw [htake]
  rfl

/-- The encoded slice, at a length whose block length is `b`, is the encoding of the slice. -/
private theorem encodedSlice_eq_hardnessEncode (L : Language Bool) (M N b : ℕ)
    (hb : blockLength M N = b) (hb0 : b ≠ 0) (hle : M * (4 * b) + 4 * b ≤ N) (X : BitString N) :
    encodedSlice L M N X =
      hardnessEncode (BinaryField.equivBits (w := 4 * b) (by omega)).toEquiv
        (BinaryField.embed (by omega) (by omega)) (L.slice (M * b))
        (fun i => X (Fin.castLE hle i)) := by
  subst hb
  simp only [encodedSlice, hb0, dite_false]

/-- **The encoding program computes `polyEncode` of a table function.** If `y` lists the bits of
`X` then `encodedProgramAt` of the decider `u ↦ tableValue T (u.take n)` is the encoding
`polyEncode n s` of `tableFunction n T`, at `X`. -/
theorem encodedProgramAt_polyEncode (n s : ℕ) (T y : List Bool) (X : BitString (polyArity n s))
    (hy : y.length = polyArity n s)
    (hX : ∀ (k : ℕ) (hk : k < polyArity n s), X ⟨k, hk⟩ = y.getD k false) :
    encodedProgramAt (polyBlocks n s) (fun u => MCSP.tableValue T (u.take n)) y
        (polyBlock n s) = polyEncode n s (MCSP.tableFunction n T) X := by
  classical
  set M := polyBlocks n s with hM
  set b := polyBlock n s with hb
  let L : Language Bool := tableLang n T
  have hgL : ∀ u, u ∈ L ↔ MCSP.tableValue T (u.take n) = true := fun _ => Iff.rfl
  have hN : polyArity n s = 4 * (M + 1) * b := by
    unfold polyArity
    ring
  have hbl : blockLength M (polyArity n s) = b := by
    rw [blockLength, hN]
    exact Nat.mul_div_cancel_left _ (by positivity)
  have key : ∀ (N : ℕ) (y : List Bool) (X : BitString N), y.length = N →
      (∀ (k : ℕ) (hk : k < N), X ⟨k, hk⟩ = y.getD k false) →
      encodedProgram M (fun u => MCSP.tableValue T (u.take n)) y N = encodedSlice L M N X := by
    intro N y X hN hX
    subst hN
    rw [encodedProgram_eq hgL M y]
    congr 1
    funext i
    rw [hX i i.2, List.getD_eq_getElem _ _ i.2]
    rfl
  have h1 := key (polyArity n s) y X hy hX
  rw [encodedProgram, hbl] at h1
  rw [h1, encodedSlice_eq_hardnessEncode L M (polyArity n s) b hbl (polyBlock_pos n s).ne'
    (le_of_eq (by rw [hN]; ring)) X, slice_eq_polyExtend n s T]
  rfl

private theorem getElem_tableGeneratorList (S m : ℕ) (T z : List Bool) (k : ℕ)
    (h : k < (tableGeneratorList S m T z).length) :
    (tableGeneratorList S m T z)[k] = tableOutput S m (Nat.log 2 T.length) T z k := by
  simp [tableGeneratorList]

/-- **The program computes the generator of a truth table.** On the truth table `T` of a function
of `n` bits, `tableGeneratorList` outputs the bits of `tableGenerator n S m` of the table function
`MCSP.tableFunction n T`, on the bits of the seed. -/
theorem tableGeneratorList_eq (S m : ℕ) {n : ℕ} (T : List Bool) (hT : T.length = 2 ^ n)
    (z : BitString (tableSeedLength n S m)) :
    tableGeneratorList S m T (List.ofFn z) =
      List.ofFn (tableGenerator n S m (MCSP.tableFunction n T) z) := by
  have hn : Nat.log 2 T.length = n := by rw [hT, Nat.log_pow (by norm_num)]
  have hlen : (tableGeneratorList S m T (List.ofFn z)).length = m := by
    simp only [tableGeneratorList, List.length_map, List.length_range]
  refine List.ext_getElem (by simp only [hlen, List.length_ofFn]) fun k h₁ h₂ => ?_
  have hk : k < m := hlen ▸ h₁
  rw [getElem_tableGeneratorList, List.getElem_ofFn, hn]
  have e1 : tableGenerator n S m (MCSP.tableFunction n T) z ⟨k, hk⟩ =
      polyEncode n (tableHardness S m) (MCSP.tableFunction n T)
        ((tableDesign n S m).restrict ⟨k, hk⟩ z) := generator_apply _ _ _ _
  rw [e1]
  unfold tableOutput
  have hℓ : 0 < tableLog m := by simp [tableLog]
  have hik : k < 2 ^ tableLog m := lt_of_lt_of_le hk (le_two_pow_tableLog m)
  have hlen' : (tablePoint (tableBlock n S m) (binaryFieldDegree (tableBlock n S m))
      (tableLog m) (List.ofFn z) k).length = polyArity n (tableHardness S m) := by
    simp only [tablePoint, List.length_map, List.length_range]
    rfl
  refine encodedProgramAt_polyEncode n (tableHardness S m) T _ _ hlen' fun r hr => ?_
  have hr' : r < tableBlock n S m := hr
  rw [tablePoint, List.getD_map_range _ _ hr', tableCell_eq (tableBlock n S m) (tableLog m) hℓ
    ⟨k, hik⟩ ⟨r, hr'⟩]
  change (tableDesign n S m).restrict ⟨k, hk⟩ z ⟨r, hr'⟩ = _
  unfold tableDesign
  change (Design.binaryPolynomial (tableBlock n S m) (tableLog m)).restrict
    (Fin.castLE (le_two_pow_tableLog m) ⟨k, hk⟩) z ⟨r, hr'⟩ = _
  rw [Design.binaryPolynomial_eq]
  exact (Design.restrict_bitPolynomial _ z _).trans (List.getD_ofFn z _ false).symm

/-! ### The bits of the seed that are read -/

/-- Output bit `i < m` of a generator reads only the first `tableSeedLength` bits of its seed. -/
theorem tableOutput_take (S m n : ℕ) (T σ : List Bool) {i : ℕ} (hi : i < m) :
    tableOutput S m n T (σ.take (tableSeedLength n S m)) i = tableOutput S m n T σ i := by
  have hℓ : 0 < tableLog m := by simp [tableLog]
  have hik : i < 2 ^ tableLog m := lt_of_lt_of_le hi (le_two_pow_tableLog m)
  have hpt : tablePoint (tableBlock n S m) (binaryFieldDegree (tableBlock n S m)) (tableLog m)
      (σ.take (tableSeedLength n S m)) i =
      tablePoint (tableBlock n S m) (binaryFieldDegree (tableBlock n S m)) (tableLog m) σ i := by
    unfold tablePoint
    refine List.map_congr_left fun j hj => ?_
    have hj' : j < tableBlock n S m := List.mem_range.mp hj
    have hcell : tableCell (binaryFieldDegree (tableBlock n S m)) (tableLog m) i j <
        tableSeedLength n S m := by
      rw [tableCell_eq (tableBlock n S m) (tableLog m) hℓ ⟨i, hik⟩ ⟨j, hj'⟩]
      exact (finProdFinEquiv _).isLt
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt hcell]
  unfold tableOutput
  rw [hpt]

/-- **A generator reads only the first `tableSeedLength` bits of its seed.** -/
theorem tableGeneratorList_take (S m : ℕ) (T σ : List Bool) :
    tableGeneratorList S m T (σ.take (tableSeedLength (Nat.log 2 T.length) S m)) =
      tableGeneratorList S m T σ := by
  unfold tableGeneratorList
  exact List.map_congr_left fun i hi => tableOutput_take S m _ T σ (List.mem_range.mp hi)

end Cslib.Crypto.PRG.NisanWigderson
