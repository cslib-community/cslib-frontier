/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.ExactLog
public import CslibFrontier.DataStructure.HashFamily.WordRAM.Tabulation
public import CslibFrontier.Foundations.FieldTheory.Finite.Trinomial
public import CslibFrontier.Probability.KWiseIndependent.Trinomial
import CslibFrontier.Computability.WordRAM.Randomized.SymbolicExec
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame
import CslibFrontier.Foundations.Data.Nat.Power
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.SuppCases
import CslibFrontier.Tactic.WramOmega

/-!
# Self-contained Word-RAM `k`-wise independent hashing

This file implements self-contained Word-RAM `k`-wise independent hashing over
`Cslib.WordRAM.Basis.exact` by evaluating degree-`(k - 1)` polynomials over the characteristic-`2`
finite field $\mathbb{F}_{2^{2 \cdot 3^t}} = \mathbb{F}_2[X] / (X^{2 \cdot 3^t} + X^{3^t} + 1)$
(`Cslib.TrinomialField t`, where `t = trinomialStep U M` is chosen at runtime so that
$q = 2 \cdot 3^t \ge \max(\lceil \log_2 \max(U, 2) \rceil, \max(M, 1))$) and projecting to the low
`M` bits (`Cslib.Probability.trinomialPolyHash`). The binary-field polynomial construction and
bit-prefix projection follow [Vadhan, Section 3.5.5, Construction 3.32 / Proposition 3.33 and
Corollary 3.34][Vadhan2012] and [Wegman and Carter][WegmanCarter1981], building on the universal
hashing framework of [Carter and Wegman, pp. 144–145][CarterWegman1979] and finite-field arithmetic
in [Lidl and Niederreiter][LidlNiederreiter1997].

Because `Basis.exact` lacks a hardware carryless-multiplication instruction, `initTableCode k`
precomputes a Four-Russians carryless multiplication table `clmulTab[0 .. 2 ^ (2 * b) - 1]` for
$b$-bit chunks (`b = chunkBits n_max = max 1 (⌊log₂ (max n_max 2)⌋ / 3)`). This table uses at most
$\max(4, n_{\max})$ words for all $n_{\max}$ (`two_pow_two_mul_chunkBits_le`) and satisfies the
sublinear cube bound $(2^{2b})^3 \le n_{\max}^2$, i.e., $2^{2b} \le n_{\max}^{2/3}$, whenever
$n_{\max} \ge 8$ (`two_pow_two_mul_chunkBits_pow_three_le`). Each $q$-bit field multiplication
splits its operands into $L = \lceil q / b \rceil$ limbs of $b$ bits, accumulates the $L \times L$
chunk products from `clmulTab`, and reduces the resulting $< 2^{2q}$ polynomial modulo
$X^{2r} + X^r + 1$ in 8 bit operations (`reduceTrinomialCode`). Under the closed-form bound
`evalSteps n_max U M k = ((11 * L + 12) * L + 30) * k + 19`, each field multiplication takes
$O(L^2)$ instructions, which is $O(1)$ instructions when both $U \le n_{\max}^c$ and
$M \le c \log_2 n_{\max}$ for a fixed constant $c$.

The initialization is factored into two reusable stages:
1. **`initTableCode k`**: deterministically computes $r = 3^t$, $q = 2r$, $b$, masks, and populates
   `clmulTab[0 .. 2 ^ (2 * b) - 1]` in `initTableSteps n_max U M`
   ($= O(n_{\max} + \log U + \log M)$) deterministic instructions from `(base, n_max, U, M)` alone.
2. **`resampleCode k`**: samples the $k$ polynomial coefficients `seed[0 .. k - 1]` uniformly and
   independently in `Fin (2 ^ q)` using $k$ `Code.rand` calls in $5k + 10 = O(k)$ instructions while
   preserving `clmulTab`, so rehashing takes $O(k)$ instructions without rebuilding `clmulTab`.
3. **`initCode k := .seq (initTableCode k) (resampleCode k)`**: full one-shot initialization.
4. **`evalCode k`**: evaluates Horner's rule for `trinomialPolyHash` in `evalSteps n_max U M k`
   ($= O(k \cdot L^2 + 1)$) deterministic instructions, preserving all memory and writing
   `(trinomialPolyHash (trinomialStep U M) k U M c u).val` into `regOut`.

## Main definitions

* `Cslib.DataStructure.HashFamily.WordRAM.KWise.chunkBits`,
  `Cslib.DataStructure.HashFamily.WordRAM.KWise.limbCount`,
  `Cslib.DataStructure.HashFamily.WordRAM.KWise.space`: chunk bit-width, limb count, and memory
  footprint.
* `Cslib.DataStructure.HashFamily.WordRAM.KWise.TableRep`,
  `Cslib.DataStructure.HashFamily.WordRAM.KWise.SeedRep`,
  `Cslib.DataStructure.HashFamily.WordRAM.KWise.Rep`: memory representation predicates separating
  the deterministic `clmulTab` / header from the $k$ random seed words.
* `Cslib.DataStructure.HashFamily.WordRAM.KWise.initTableCode`,
  `Cslib.DataStructure.HashFamily.WordRAM.KWise.resampleCode`,
  `Cslib.DataStructure.HashFamily.WordRAM.KWise.initCode`,
  `Cslib.DataStructure.HashFamily.WordRAM.KWise.evalCode`,
  `Cslib.DataStructure.HashFamily.WordRAM.KWise.evalHashOut`: structured Word-RAM programs over
  `Basis.exact` and the induced deterministic hash output map.

## Main results

* `Cslib.DataStructure.HashFamily.WordRAM.KWise.two_pow_two_mul_chunkBits_le`,
  `Cslib.DataStructure.HashFamily.WordRAM.KWise.two_pow_two_mul_chunkBits_pow_three_le`: coarse
  $\max(4, n_{\max})$ and sublinear $n_{\max}^{2/3}$ bounds on the Four-Russians table size.
* `Cslib.DataStructure.HashFamily.WordRAM.KWise.fits_two_pow_trinomialDeg`: the word-width
  bound `2 * trinomialDeg U M ≤ w` makes `2 ^ trinomialDeg U M` fit in a word.
* `Cslib.DataStructure.HashFamily.WordRAM.KWise.extractSeeds_eq_of_seedRep`,
  `Cslib.DataStructure.HashFamily.WordRAM.KWise.SeedRep.congr_of_footprint`,
  `Cslib.DataStructure.HashFamily.WordRAM.KWise.extractSeeds_congr_of_footprint`: seed-extraction
  inversion and memory-footprint congruence lemmas for `SeedRep` and `extractSeeds`.
* `Cslib.DataStructure.HashFamily.WordRAM.KWise.initTableCode_execWithin`: deterministic
  `initTableSteps n_max U M` ($= O(n_{\max} + \log U + \log M)$) table construction establishing
  `TableRep`.
* `Cslib.DataStructure.HashFamily.WordRAM.KWise.resampleCode_execRand`,
  `Cslib.DataStructure.HashFamily.WordRAM.KWise.map_extractSeeds_eval_resampleComp`,
  `Cslib.DataStructure.HashFamily.WordRAM.KWise.resampleCode_execRandWithin`: $(5k + 10)$-step,
  $k$-query seed resampling preserving `TableRep` and inducing
  `PMF.uniformOfFintype (Fin k → Fin (2 ^ q))`.
* `Cslib.DataStructure.HashFamily.WordRAM.KWise.evalCode_execWithin`,
  `Cslib.DataStructure.HashFamily.WordRAM.KWise.evalHashOut_eq_trinomialPolyHash`: deterministic
  `evalSteps n_max U M k` ($= O(k \cdot L^2 + 1)$) Horner evaluation matching `trinomialPolyHash`.
* `Cslib.DataStructure.HashFamily.WordRAM.KWise.map_evalHashOut_eval_resampleComp`,
  `Cslib.DataStructure.HashFamily.WordRAM.KWise.isKWiseIndependentHash_eval`: composed Word-RAM
  $k$-wise independence theorem proving that for every set $T$ of at most $k$ keys, the restricted
  tuple of `evalCode k` outputs after `resampleCode k` is uniformly distributed on
  $T \to \text{Fin}(2^M)$.

## References

* [S. P. Vadhan, *Pseudorandomness*, Section 3.5.5][Vadhan2012]
* [J. L. Carter and M. N. Wegman, *Universal Classes of Hash Functions*][CarterWegman1979]
* [M. N. Wegman and J. L. Carter, *New Hash Functions and Their Use in Authentication and Set
  Equality*][WegmanCarter1981]
* [R. Lidl and H. Niederreiter, *Finite Fields*][LidlNiederreiter1997]
* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017]
-/

public section

namespace Cslib.DataStructure.HashFamily.WordRAM.KWise

open Cslib.WordRAM Cslib.Probability
open Cslib.WordRAM.ExactLog
open Cslib.DataStructure.HashFamily.WordRAM.Tabulation
open scoped ENNReal

/-! ## Section 1: Parameters, bounds, and memory layout -/

/-- Chunk bit-width `b = max 1 (⌊log₂ (max n_max 2)⌋ / 3)` for Four-Russians carryless
multiplication, ensuring `1 ≤ b` and `2 ^ (2 * b) ≤ max 4 n_max`. -/
@[expose] def chunkBits (n_max : ℕ) : ℕ :=
  max 1 (Nat.log 2 (max n_max 2) / 3)

/-- `chunkBits n_max` is always at least `1`. -/
theorem one_le_chunkBits (n_max : ℕ) : 1 ≤ chunkBits n_max :=
  Nat.le_max_left 1 _

/-- `chunkBits n_max` is always positive. -/
theorem chunkBits_pos (n_max : ℕ) : 0 < chunkBits n_max :=
  one_le_chunkBits n_max

/-- The Four-Russians carryless multiplication table size `2 ^ (2 * chunkBits n_max)` is at most
`max 4 n_max` for all `n_max`. -/
theorem two_pow_two_mul_chunkBits_le (n_max : ℕ) :
    2 ^ (2 * chunkBits n_max) ≤ max 4 n_max := by
  rcases le_total (Nat.log 2 (max n_max 2) / 3) 1 with h | h
  · rw [chunkBits, max_eq_left h]
    exact Nat.le_max_left 4 n_max
  · rw [chunkBits, max_eq_right h]
    exact (Nat.pow_le_pow_right two_pos (by omega : 2 * (Nat.log 2 (max n_max 2) / 3) ≤
        Nat.log 2 (max n_max 2))).trans
      ((Nat.pow_log_le_self 2 (by omega)).trans (by omega))

/-- For `8 ≤ n_max`, the Four-Russians table size `2 ^ (2 * chunkBits n_max)` satisfies the
sublinear cube bound `(2 ^ (2 * chunkBits n_max)) ^ 3 ≤ n_max ^ 2` (i.e.,
`2 ^ (2 * chunkBits n_max) ≤ n_max ^ (2 / 3)`). -/
theorem two_pow_two_mul_chunkBits_pow_three_le {n_max : ℕ} (hn : 8 ≤ n_max) :
    (2 ^ (2 * chunkBits n_max)) ^ 3 ≤ n_max ^ 2 := by
  have hlog3 : 3 ≤ Nat.log 2 n_max := Nat.le_log_of_pow_le one_lt_two (by omega)
  have hcb : chunkBits n_max = Nat.log 2 n_max / 3 := by
    simp only [chunkBits, Nat.max_eq_left (by omega : 2 ≤ n_max)]; omega
  rw [← pow_mul]
  exact (Nat.pow_le_pow_right two_pos
    (by omega : 2 * chunkBits n_max * 3 ≤ Nat.log 2 n_max * 2)).trans
    (by rw [pow_mul]; exact Nat.pow_le_pow_left (Nat.pow_log_le_self 2 (by omega)) 2)

/-- Number of `b`-bit limbs `L = ⌈q / b⌉ = (q + b - 1) / b` needed to cover a `q`-bit field
element. -/
@[expose] def limbCountFromB (b q : ℕ) : ℕ :=
  (q + b - 1) / b

/-- Number of `chunkBits n_max`-bit limbs covering `trinomialDeg U M` bits. -/
@[expose] def limbCount (n_max U M : ℕ) : ℕ :=
  limbCountFromB (chunkBits n_max) (trinomialDeg U M)

/-- When `0 < b`, `limbCountFromB b q * b` is at least `q`. -/
theorem le_limbCountFromB_mul {b : ℕ} (hb : 0 < b) (q : ℕ) :
    q ≤ limbCountFromB b q * b :=
  (Nat.le_mul_iff_le_left hb).mpr le_rfl

/-- `limbCount n_max U M * chunkBits n_max` covers all `trinomialDeg U M` bits. -/
theorem trinomialDeg_le_limbCount_mul_chunkBits (n_max U M : ℕ) :
    trinomialDeg U M ≤ limbCount n_max U M * chunkBits n_max :=
  le_limbCountFromB_mul (chunkBits_pos n_max) (trinomialDeg U M)

/-- Memory footprint `8 + k + 2 ^ (2 * b)` words for `k`-wise independent hashing with chunk width
`b`: 8 header words, `k` seed words, and `2 ^ (2 * b)` carryless multiplication table entries. -/
@[expose] def spaceFromB (b k : ℕ) : ℕ :=
  8 + k + 2 ^ (2 * b)

/-- Memory footprint `8 + k + 2 ^ (2 * chunkBits n_max)` words at capacity parameter `n_max`. -/
@[expose] def space (n_max k : ℕ) : ℕ :=
  spaceFromB (chunkBits n_max) k

attribute [local wram_arith] spaceFromB space

/-- Discharger combining `omega` and `wram_omega` without unnecessary-`wram_omega` warnings. -/
local macro "layout_omega" : tactic => `(tactic| first | omega | wram_omega)

/-- `space n_max k` is at most `8 + k + max 4 n_max = O(n_max + k)`. -/
theorem space_le (n_max k : ℕ) : space n_max k ≤ 8 + k + max 4 n_max :=
  Nat.add_le_add_left (two_pow_two_mul_chunkBits_le n_max) _

/-- The width bound `2 * trinomialDeg U M ≤ w` makes the field size `2 ^ trinomialDeg U M` fit in
a word. -/
theorem fits_two_pow_trinomialDeg {w U M : ℕ} (hw : 2 * trinomialDeg U M ≤ w) :
    Fits w (2 ^ trinomialDeg U M) :=
  Nat.pow_lt_pow_right one_lt_two
    (by have : 0 < trinomialDeg U M := by dsimp only [trinomialDeg]; positivity
        omega)

/-- Deterministic table representation predicate `TableRep base b U M k mem`:
stores the 8 header parameters `(r, q, 2 ^ r - 1, 2 ^ q - 1, 2 ^ M - 1, b, 2 ^ b - 1, L)` at
`base + 0 .. base + 7` and the Four-Russians carryless multiplication table
`clmul (idx >>> b) (idx &&& (2 ^ b - 1))` at `base + 8 + k + idx` for `idx < 2 ^ (2 * b)`. -/
@[expose] def TableRep (base b U M k : ℕ) (mem : ℕ → ℕ) : Prop :=
  let r := 3 ^ trinomialStep U M
  let q := trinomialDeg U M
  mem base = r ∧
  mem (base + 1) = q ∧
  mem (base + 2) = 2 ^ r - 1 ∧
  mem (base + 3) = 2 ^ q - 1 ∧
  mem (base + 4) = 2 ^ M - 1 ∧
  mem (base + 5) = b ∧
  mem (base + 6) = 2 ^ b - 1 ∧
  mem (base + 7) = limbCountFromB b q ∧
  ∀ idx < 2 ^ (2 * b),
    mem (base + 8 + k + idx) = clmul (idx >>> b) (idx &&& (2 ^ b - 1))

/-- Seed representation predicate `SeedRep base U M k c mem`: stores the `k` polynomial
coefficients `(c j).val < 2 ^ (trinomialDeg U M)` at `base + 8 + j.val`. -/
@[expose] def SeedRep (base U M k : ℕ)
    (c : Fin k → Fin (2 ^ trinomialDeg U M)) (mem : ℕ → ℕ) : Prop :=
  ∀ j : Fin k, mem (base + 8 + j.val) = (c j).val

/-- Full representation predicate combining `TableRep` and `SeedRep`. -/
@[expose] def Rep (base b U M k : ℕ)
    (c : Fin k → Fin (2 ^ trinomialDeg U M)) (mem : ℕ → ℕ) : Prop :=
  TableRep base b U M k mem ∧ SeedRep base U M k c mem

/-- Extract the `k`-tuple of seeds `Fin k → Fin (2 ^ trinomialDeg U M)` from
`[base + 8, base + 8 + k)`. -/
@[expose] def extractSeeds (base U M k : ℕ) (mem : ℕ → ℕ) :
    Fin k → Fin (2 ^ trinomialDeg U M) :=
  extractSlice (base + 8) (trinomialDeg U M) k mem

/-- When `SeedRep base U M k c mem` holds, `extractSeeds base U M k mem` recovers the seed tuple
`c`. -/
theorem extractSeeds_eq_of_seedRep {base U M k : ℕ}
    {c : Fin k → Fin (2 ^ trinomialDeg U M)} {mem : ℕ → ℕ}
    (hseed : SeedRep base U M k c mem) :
    extractSeeds base U M k mem = c :=
  funext fun j => Fin.ext <| by
    simpa only [extractSeeds, extractSlice, hseed j] using wordOfNat_val_of_lt (c j).isLt

/-- `SeedRep base U M k c` depends only on the memory values in `[base, base + 8 + k)`. -/
theorem SeedRep.congr_of_footprint {base U M k : ℕ}
    {c : Fin k → Fin (2 ^ trinomialDeg U M)} {mem mem' : ℕ → ℕ}
    (hseed : SeedRep base U M k c mem)
    (hm : ∀ a, base ≤ a → a < base + 8 + k → mem' a = mem a) :
    SeedRep base U M k c mem' :=
  fun j => (hm (base + 8 + j.val) (by omega) (by have := j.isLt; omega)).trans (hseed j)

/-- `extractSeeds base U M k` depends only on the memory values in `[base, base + 8 + k)`. -/
theorem extractSeeds_congr_of_footprint {base U M k : ℕ} {mem mem' : ℕ → ℕ}
    (hm : ∀ a, base ≤ a → a < base + 8 + k → mem' a = mem a) :
    extractSeeds base U M k mem' = extractSeeds base U M k mem :=
  funext fun j => congrArg (wordOfNat _) (hm _ (by omega) (by have := j.isLt; omega))

/-! ## Section 2: Helper loops for `initTableCode` -/

/-- Final remainder reached by `trinomialStepAux` when repeatedly mapping `B ↦ (B + 2) / 3` until
`≤ 2`. -/
@[expose] def trinomialStepRem (B : ℕ) : ℕ :=
  if B ≤ 2 then B else trinomialStepRem ((B + 2) / 3)

/-- `trinomialStepRem B` is always at most `2`. -/
theorem trinomialStepRem_le_two (B : ℕ) : trinomialStepRem B ≤ 2 := by
  fun_induction trinomialStepRem B with
  | case1 _ h => exact h
  | case2 _ _ ih => exact ih

/-- `trinomialStepAux B` is at most `B`. -/
theorem trinomialStepAux_le (B : ℕ) : trinomialStepAux B ≤ B := by
  fun_induction trinomialStepAux B <;> omega

/-- Body of `trinomialStepLoop` on `Data 4` (`reg 0 = rem`, `reg 1 = r`, `reg 2 = 2`,
`reg 3 = 3`): updates `rem ← (rem + 2) / 3` and `r ← r * 3`. -/
@[expose] def trinomialStepBody : Code .exact 4 :=
  .seq (.op (.exactBin .add 0 0 2))
  (.seq (.op (.exactBin .div 0 0 3))
        (.op (.exactBin .mul 1 1 3)))

/-- Loop `while 2 < rem do [ rem ← (rem + 2) / 3; r ← r * 3 ]` computing
`3 ^ trinomialStepAux B`. -/
@[expose] def trinomialStepLoop : Code .exact 4 :=
  .loop (.lt 2 0) trinomialStepBody

/-- Closed-form final state of `trinomialStepLoop`. -/
@[expose] def trinomialStepLoopData (B acc : ℕ) (x : Data 4) : Data 4 :=
  (x.set 0 (trinomialStepRem B)).set 1 (acc * 3 ^ trinomialStepAux B)

/-- `trinomialStepLoop` executes deterministically in `5 * trinomialStepAux B + 2` instructions,
accumulating `acc * 3 ^ trinomialStepAux B` into register `1` and preserving all memory. -/
theorem trinomialStepLoop_exec {w : ℕ} (B : ℕ) {acc : ℕ} {x : Data 4}
    (hrem : x.regs 0 = B) (hacc : x.regs 1 = acc) (htwo : x.regs 2 = 2) (hthree : x.regs 3 = 3)
    (hfit_B2 : Fits w (B + 2)) (hfit_res : Fits w (acc * 3 ^ trinomialStepAux B)) :
    Exec w trinomialStepLoop x (trinomialStepLoopData B acc x)
      (5 * trinomialStepAux B + 2) := by
  fun_induction trinomialStepAux B generalizing acc x with
  | case1 B hB =>
    have hrem0 : trinomialStepRem B = B := by rw [trinomialStepRem, ite_eq_left hB]
    have hd : trinomialStepLoopData B acc x = x := by
      have haux : trinomialStepAux B = 0 := by rw [trinomialStepAux, ite_eq_left hB]
      ext i : 2
      · fin_cases i <;> simp +decide [trinomialStepLoopData, hrem0, haux, hrem, hacc]
      · rfl
    rw [hd]
    exact Exec.loop_exit (by simp [Cond.Holds, hrem, htwo]; omega)
  | case2 B hB ih =>
    have hrem_step : trinomialStepRem B = trinomialStepRem ((B + 2) / 3) := by
      rw [trinomialStepRem, ite_eq_right hB]
    have hmul : acc * 3 * 3 ^ trinomialStepAux ((B + 2) / 3) =
        acc * 3 ^ (trinomialStepAux ((B + 2) / 3) + 1) := by rw [Nat.pow_succ']; ring
    have hfit_acc3 : Fits w (acc * 3) :=
      hfit_res.of_le (hmul ▸ Nat.le_mul_of_pos_right _ (by positivity))
    refine WP.Exact.exec (WP.Exact.loop_iter (by simp [Cond.Holds, hrem, htwo]; omega) ?_)
    wram_exec [trinomialStepBody, hrem, hacc, htwo, hthree]
    refine WP.Exact.of_exec (ih (acc := acc * 3) (by wram_simp) (by wram_simp)
      (by wram_simp [htwo]) (by wram_simp [hthree]) (by fits) (by rwa [hmul])) ⟨by omega, ?_⟩
    have hstep : trinomialStepAux B = trinomialStepAux ((B + 2) / 3) + 1 := by
      rw [trinomialStepAux, ite_eq_right hB]
    ext i : 2
    · fin_cases i <;> wram_simp [trinomialStepLoopData, hrem_step, hstep, hmul]
    · rfl

/-- Body of `clmulTabLoop` on `Data 18` (`reg 0 = tabBase`, `reg 1 = idx`, `reg 2 = tabSize`,
`reg 3 = b`, `reg 4 = 2 ^ b - 1`, `reg 5 = 1`, `reg 6..9` scratch): populates
`mem[tabBase + idx] ← clmul (idx >>> b) (idx &&& (2 ^ b - 1))` using previously filled entry
`prevIdx = ((idx >>> b) <<< b) + ((idx &&& (2 ^ b - 1)) >>> 1)` and increments `idx`. -/
@[expose] def clmulTabBody : Code .exact 18 :=
  .seq (.op (.exactBin .add 6 0 1))
  (.seq (.op (.const 9 0))
  (.seq (.op (.store 6 9))
  (.seq (.op (.exactBin .shiftRight 7 1 3))
  (.seq (.op (.exactBin .and 8 1 4))
  (.seq (.op (.exactBin .shiftRight 9 8 5))
  (.seq (.op (.exactBin .shiftLeft 6 7 3))
  (.seq (.op (.exactBin .add 9 6 9))
  (.seq (.op (.exactBin .add 9 0 9))
  (.seq (.op (.load 9 9))
  (.seq (.op (.exactBin .shiftLeft 9 9 5))
  (.seq (.op (.exactBin .and 8 8 5))
  (.seq (.op (.exactBin .mul 8 8 7))
  (.seq (.op (.exactBin .xor 9 8 9))
  (.seq (.op (.exactBin .add 6 0 1))
  (.seq (.op (.store 6 9))
        (.op (.exactBin .add 1 1 5)))))))))))))))))

/-- Loop `while idx < tabSize do clmulTabBody` populating the Four-Russians carryless
multiplication table `clmulTab[0 .. 2 ^ (2 * b) - 1]`. -/
@[expose] def clmulTabLoop : Code .exact 18 :=
  .loop (.lt 1 2) clmulTabBody

private theorem clmul_shiftLeft_lt {x y sh_x sh_y q : ℕ}
    (hx : x * 2 ^ sh_x < 2 ^ q) (hy : y * 2 ^ sh_y < 2 ^ q) :
    clmul x y <<< (sh_x + sh_y) < 2 ^ (2 * q) := by
  rcases eq_or_ne x 0 with rfl | hx0; · simp
  rcases eq_or_ne y 0 with rfl | hy0; · simp
  have split {c s : ℕ} (hc : 0 < c) (h : c * 2 ^ s < 2 ^ q) : s ≤ q ∧ c < 2 ^ (q - s) := by
    have hs : s ≤ q := by_contra fun hlt =>
      ((Nat.pow_le_pow_right two_pos (by omega)).trans (Nat.le_mul_of_pos_left _ hc)).not_gt h
    exact ⟨hs, Nat.lt_of_mul_lt_mul_right (a := 2 ^ s)
      (by rwa [← pow_add, Nat.sub_add_cancel hs])⟩
  obtain ⟨hsx, hx'⟩ := split (Nat.pos_of_ne_zero hx0) hx
  obtain ⟨hsy, hy'⟩ := split (Nat.pos_of_ne_zero hy0) hy
  rw [Nat.shiftLeft_eq]
  calc clmul x y * 2 ^ (sh_x + sh_y)
      < 2 ^ (q - sh_x + (q - sh_y)) * 2 ^ (sh_x + sh_y) :=
        Nat.mul_lt_mul_of_pos_right (clmul_lt_two_pow hx' hy') (by positivity)
    _ = 2 ^ (2 * q) := by rw [← pow_add]; congr 1; omega

/-- `clmulTabLoop` executes deterministically in `19 * (2 ^ (2 * b) - idx) + 2` instructions,
filling `mem[tabBase + i] = clmul (i >>> b) (i &&& (2 ^ b - 1))` for all `i < 2 ^ (2 * b)` and
preserving `reg 0 = tabBase` and memory outside `[tabBase + idx, tabBase + 2 ^ (2 * b))`. -/
theorem clmulTabLoop_exec {w tabBase b : ℕ}
    (hfit_end : Fits w (tabBase + 2 ^ (2 * b))) :
    ∀ rem idx : ℕ, ∀ x : Data 18,
      idx + rem = 2 ^ (2 * b) →
      x.regs 0 = tabBase →
      x.regs 1 = idx →
      x.regs 2 = 2 ^ (2 * b) →
      x.regs 3 = b →
      x.regs 4 = 2 ^ b - 1 →
      x.regs 5 = 1 →
      (∀ i < idx, x.mem (tabBase + i) = clmul (i >>> b) (i &&& (2 ^ b - 1))) →
      ∃ y : Data 18,
        Exec w clmulTabLoop x y (19 * rem + 2) ∧
        y.regs 0 = tabBase ∧
        (∀ i < 2 ^ (2 * b), y.mem (tabBase + i) = clmul (i >>> b) (i &&& (2 ^ b - 1))) ∧
        (∀ a, (a < tabBase + idx ∨ tabBase + 2 ^ (2 * b) ≤ a) → y.mem a = x.mem a) := by
  intro rem
  induction rem with
  | zero =>
    intro idx x hsum h0 h1 h2 _ _ _ hinv
    refine ⟨x, Exec.loop_exit (by simp [Cond.Holds, h1, h2]; omega), h0,
      fun i hi => hinv i (by omega), fun _ _ => rfl⟩
  | succ rem ih =>
    intro idx x hsum h0 h1 h2 h3 h4 h5 hinv
    obtain ⟨hu_lt, hv_lt, huv_eq, hprev_le, hprev_lt, hprev_zero, hprev_u, hprev_v⟩ :=
      clmulTab_index_props (by omega : idx < 2 ^ (2 * b))
    set u := idx >>> b with hu
    set v := idx &&& (2 ^ b - 1) with hv
    set prevIdx := (u <<< b) + (v >>> 1) with hprev
    have hpow_le : 2 ^ b ≤ 2 ^ (2 * b) := Nat.pow_le_pow_right two_pos (by omega)
    have hsh_lt : clmul u (v >>> 1) <<< 1 < 2 ^ (2 * b) :=
      clmul_shiftLeft_lt (sh_x := 0) (sh_y := 1) (by simpa using hu_lt)
        (by rw [Nat.shiftRight_eq_div_pow, pow_one]; exact (Nat.div_mul_le_self v 2).trans_lt hv_lt)
    have hbit_le : (v &&& 1) * u ≤ u :=
      (Nat.mul_le_mul_right u Nat.and_le_right).trans_eq (Nat.one_mul u)
    have hval_lt : clmul u v < 2 ^ (2 * b) := clmul_lt_two_pow_two_mul hu_lt hv_lt
    have hfit_vbit : Fits w (v &&& 1) := (by fits : Fits w v).of_le Nat.and_le_left
    have hprev_mem : (((x.set 6 (tabBase + idx)).set 9 0).write (tabBase + idx) 0).mem
        (tabBase + prevIdx) = clmul u (v >>> 1) := by
      rcases eq_or_ne v 0 with hv0 | hv0
      · simp [Data.write, Data.set, hprev_zero hv0, hv0]
      · have := hprev_lt hv0
        wram_simp [hinv prevIdx this, hprev_u, hprev_v]
    refine WP.Exact.exists_exec (WP.Exact.loop_iter (by simp [Cond.Holds, h1, h2]; omega) ?_)
    wram_exec [clmulTabBody,
      h0, h1, h3, h4, h5, ← hu, ← hv, ← hprev, hprev_mem, clmul_eq_bit_mul_xor]
    wram_call (ih (idx + 1) _ (by omega) (by regs_frame) (by wram_simp) (by regs_frame)
      (by regs_frame) (by regs_frame) (by regs_frame) fun i hi => by
        rcases eq_or_ne i idx with rfl | hne
        · wram_simp [u, v]
        · wram_simp [hinv i (by omega)]) with y ⟨hy0, hytab, hyout⟩
    exact ⟨by omega, hy0, hytab, fun a ha => by rw [hyout a (by omega)]; wram_simp⟩

/-! ## Section 3: Table construction (`initTableCode`) and seed resampling (`resampleCode`) -/

/-- Register `0`: holds the base memory address `base`. -/
abbrev regBase : Fin 18 := 0

/-- Register `1`: holds `n_max` on entry to `initTableCode` (and `key` on entry to `evalCode`). -/
abbrev regNMax : Fin 18 := 1

/-- Register `2`: holds `U` on entry to `initTableCode` (and output in `evalCode`). -/
abbrev regU : Fin 18 := 2

/-- Register `3`: holds `M` on entry to `initTableCode`. -/
abbrev regM : Fin 18 := 3

/-- Subprogram on `Data 18` computing `chunkBits n_max` into register `5` and `1` into register `6`
from `n_max` in register `1`, while preserving registers `0, 1, 2, 3` and memory. -/
@[expose] def chunkBitsCode : Code .exact 18 :=
  .seq (.op (.const 4 2))
  (.seq (maxCode 4 1 4)
  (.seq (.op (.const 5 0))
  (.seq (.op (.const 6 1))
  (.seq (log2Loop.rename ![4, 5, 6])
  (.seq (.op (.const 4 3))
  (.seq (.op (.exactBin .div 5 5 4))
        (maxCode 5 6 5)))))))

private theorem maxCode_spec {w n : ℕ} (dst a b : Fin n) (x : Data n) :
    ∃ y, Exec w (maxCode dst a b) x y 3 ∧ y = x.set dst (max (x.regs a) (x.regs b)) :=
  ⟨_, maxCode_exec dst a b x, rfl⟩

private theorem log2Loop_spec {w : ℕ} (rem : ℕ) {x : Data 3}
    (hrem : x.regs 0 = rem) (hacc : x.regs 1 = 0) (hone : x.regs 2 = 1) (hfit : Fits w rem) :
    ∃ y, Exec w log2Loop x y (4 * Nat.log 2 rem + 2) ∧
      y.regs 1 = Nat.log 2 rem ∧ y.regs 2 = 1 ∧ y.mem = x.mem := by
  have hlog_le : Nat.log 2 rem ≤ rem := Nat.log_le_self 2 rem
  exact ⟨_, log2Loop_exec rem hrem hacc hone hfit (by fits),
    by simp +decide [log2LoopData], by simp +decide [log2LoopData, hone], rfl⟩

private theorem clog2Loop_spec {w : ℕ} (rem : ℕ) {x : Data 3}
    (hrem : x.regs 0 = rem) (hacc : x.regs 1 = 0) (hone : x.regs 2 = 1)
    (hfit_rem : Fits w (rem + 1)) (hfit_res : Fits w (Nat.clog 2 rem)) :
    ∃ y, Exec w clog2Loop x y (5 * Nat.clog 2 rem + 2) ∧
      y.regs 1 = Nat.clog 2 rem ∧ y.regs 2 = 1 ∧ y.mem = x.mem :=
  ⟨_, clog2Loop_exec rem hrem hacc hone hfit_rem (by simpa using hfit_res),
    by simp +decide [clog2LoopData], by simp +decide [clog2LoopData, hone], rfl⟩

private theorem trinomialStepLoop_spec {w : ℕ} (B : ℕ) {x : Data 4}
    (hrem : x.regs 0 = B) (hacc : x.regs 1 = 1) (htwo : x.regs 2 = 2) (hthree : x.regs 3 = 3)
    (hfit_B2 : Fits w (B + 2)) (hfit_res : Fits w (3 ^ trinomialStepAux B)) :
    ∃ y, Exec w trinomialStepLoop x y (5 * trinomialStepAux B + 2) ∧
      y.regs 1 = 3 ^ trinomialStepAux B ∧ y.regs 2 = 2 ∧ y.mem = x.mem :=
  ⟨_, trinomialStepLoop_exec B hrem hacc htwo hthree hfit_B2 (by simpa using hfit_res),
    by simp +decide [trinomialStepLoopData], by simp +decide [trinomialStepLoopData, htwo], rfl⟩

/-- `chunkBitsCode` executes deterministically in `4 * Nat.log 2 (max n_max 2) + 13` steps. -/
theorem chunkBitsCode_exec {w base n_max U M : ℕ} {x : Data 18}
    (h0 : x.regs 0 = base) (h1 : x.regs 1 = n_max) (h2 : x.regs 2 = U) (h3 : x.regs 3 = M)
    (hfit_n : Fits w (max n_max 2)) (hfit_3 : Fits w 3) :
    ∃ y : Data 18,
      Exec w chunkBitsCode x y (4 * Nat.log 2 (max n_max 2) + 13) ∧
      y.regs 0 = base ∧
      y.regs 2 = U ∧
      y.regs 3 = M ∧
      y.regs 5 = chunkBits n_max ∧
      y.regs 6 = 1 ∧
      y.mem = x.mem := by
  have hlog_le : Nat.log 2 (max n_max 2) ≤ max n_max 2 := Nat.log_le_self 2 _
  refine WP.Exact.exists_exec ?_
  wram_exec [chunkBitsCode]
  wram_call (maxCode_spec 4 1 4 _) with _ rfl
  wram_exec
  wram_call (log2Loop_spec (max n_max 2)
      (by simp +decide [Data.comap, Data.set, h1]) (by simp +decide [Data.comap, Data.set])
      (by simp +decide [Data.comap, Data.set]) hfit_n)
    renamed (by decide : Function.Injective (![4, 5, 6] : Fin 3 → Fin 18))
    with s5 ⟨⟨hs5_5, hs5_6, hs5_mem⟩, hs5_fr⟩
  simp +decide only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val] at hs5_5 hs5_6
  wram_exec [hs5_5]
  wram_call (maxCode_spec 5 6 5 _) with _ rfl
  exact ⟨by omega, by regs_frame, by regs_frame, by regs_frame,
    by wram_simp [hs5_5, hs5_6, chunkBits], by regs_frame, by wram_simp [hs5_mem]⟩

/-- Subprogram on `Data 18` computing `r = 3 ^ trinomialStep U M` into register `1`,
`q = trinomialDeg U M` into register `2`, and `2` into register `4` from `U` in register `2`,
`M` in register `3`, and `1` in register `6`, while preserving `reg 0 = base`, `reg 3 = M`,
`reg 5 = b`, `reg 6 = 1`, and memory. -/
@[expose] def trinomialParamsCode : Code .exact 18 :=
  .seq (.op (.const 4 2))
  (.seq (maxCode 7 2 4)
  (.seq (.op (.const 8 0))
  (.seq (clog2Loop.rename ![7, 8, 6])
  (.seq (maxCode 7 3 6)
  (.seq (maxCode 7 8 7)
  (.seq (.op (.const 1 1))
  (.seq (.op (.const 8 3))
  (.seq (trinomialStepLoop.rename ![7, 1, 4, 8])
        (.op (.exactBin .mul 2 4 1))))))))))

/-- `trinomialParamsCode` executes deterministically in
`5 * Nat.clog 2 (max U 2) + 5 * trinomialStep U M + 18` steps. -/
theorem trinomialParamsCode_exec {w base U M b : ℕ} {x : Data 18}
    (h0 : x.regs 0 = base) (h2 : x.regs 2 = U) (h3 : x.regs 3 = M)
    (h5 : x.regs 5 = b) (h6 : x.regs 6 = 1)
    (hfit_U : Fits w (max U 2 + 1)) (hfit_q : Fits w (2 ^ trinomialDeg U M)) :
    ∃ y : Data 18,
      Exec w trinomialParamsCode x y
        (5 * Nat.clog 2 (max U 2) + 5 * trinomialStep U M + 18) ∧
      y.regs 0 = base ∧
      y.regs 1 = 3 ^ trinomialStep U M ∧
      y.regs 2 = trinomialDeg U M ∧
      y.regs 3 = M ∧
      y.regs 4 = 2 ∧
      y.regs 5 = b ∧
      y.regs 6 = 1 ∧
      y.mem = x.mem := by
  set B := trinomialTargetBits U M
  have hB_le_q : B ≤ trinomialDeg U M := trinomialTargetBits_le_trinomialDeg U M
  have hpow_q : trinomialDeg U M + 2 ≤ 2 ^ trinomialDeg U M :=
    Nat.add_two_le_two_pow <| by
      have := Nat.one_le_pow (trinomialStep U M) 3 (by decide)
      dsimp only [trinomialDeg]; omega
  have hfit_q2 : Fits w (trinomialDeg U M + 2) := by fits
  have hclog_le_B : Nat.clog 2 (max U 2) ≤ B := le_max_left _ _
  have hr_le_q : 3 ^ trinomialStepAux B ≤ trinomialDeg U M := by
    change 3 ^ trinomialStep U M ≤ 2 * 3 ^ trinomialStep U M; omega
  refine WP.Exact.exists_exec ?_
  wram_exec [trinomialParamsCode]
  wram_call (maxCode_spec 7 2 4 _) with _ rfl
  wram_exec
  wram_call (clog2Loop_spec (max U 2)
      (by simp +decide [Data.comap, Data.set, h2]) (by simp +decide [Data.comap, Data.set])
      (by simp +decide [Data.comap, Data.set, h6]) hfit_U (by fits))
    renamed (by decide : Function.Injective (![7, 8, 6] : Fin 3 → Fin 18))
    with s4 ⟨⟨hs4_8, hs4_6, hs4_mem⟩, hs4_fr⟩
  simp +decide only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val] at hs4_8 hs4_6
  wram_exec
  wram_call (maxCode_spec 7 3 6 _) with _ rfl
  wram_exec
  wram_call (maxCode_spec 7 8 7 _) with _ rfl
  wram_exec
  wram_call (trinomialStepLoop_spec B
      (by simp +decide [Data.comap, Data.set, hs4_8, hs4_6, hs4_fr 3 (by decide), h3, B,
            trinomialTargetBits])
      (by simp +decide [Data.comap, Data.set])
      (by simp +decide [Data.comap, Data.set, hs4_fr 4 (by decide)])
      (by simp +decide [Data.comap, Data.set]) (by fits) (by fits))
    renamed (by decide : Function.Injective (![7, 1, 4, 8] : Fin 4 → Fin 18))
    with s9 ⟨⟨hs9_1, hs9_4, hs9_mem⟩, hs9_fr⟩
  simp +decide only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val] at hs9_1 hs9_4
  wram_exec [hs9_1, hs9_4, show 2 * 3 ^ trinomialStepAux B = trinomialDeg U M from rfl]
  exact ⟨by rw [show trinomialStepAux B = trinomialStep U M from rfl]; omega,
    by regs_frame, by wram_simp [hs9_1]; rfl, by wram_simp, by regs_frame,
    by regs_frame, by regs_frame, by regs_frame, by wram_simp [hs9_mem, hs4_mem]⟩

/-- First 17-instruction header-store block: writes `r, q, 2 ^ r - 1, 2 ^ q - 1, 2 ^ M - 1, b` to
`base + 0 .. base + 5`. -/
@[expose] def storeHeaderPart1 : Code .exact 18 :=
  .seq (.op (.store 0 1))
  (.seq (.op (.exactBin .add 7 0 6))
  (.seq (.op (.store 7 2))
  (.seq (.op (.exactBin .shiftLeft 8 6 1))
  (.seq (.op (.exactBin .sub 8 8 6))
  (.seq (.op (.exactBin .add 7 7 6))
  (.seq (.op (.store 7 8))
  (.seq (.op (.exactBin .shiftLeft 8 6 2))
  (.seq (.op (.exactBin .sub 8 8 6))
  (.seq (.op (.exactBin .add 7 7 6))
  (.seq (.op (.store 7 8))
  (.seq (.op (.exactBin .shiftLeft 8 6 3))
  (.seq (.op (.exactBin .sub 8 8 6))
  (.seq (.op (.exactBin .add 7 7 6))
  (.seq (.op (.store 7 8))
  (.seq (.op (.exactBin .add 7 7 6))
        (.op (.store 7 5)))))))))))))))))

/-- Second 17-instruction header-store and loop-prep block: writes `2 ^ b - 1` and
`limbCountFromB b q` to `base + 6, base + 7` and sets registers `0..5` for `clmulTabLoop`. -/
@[expose] def storeHeaderPart2 (k : ℕ) : Code .exact 18 :=
  .seq (.op (.exactBin .shiftLeft 8 6 5))
  (.seq (.op (.exactBin .sub 8 8 6))
  (.seq (.op (.exactBin .add 7 7 6))
  (.seq (.op (.store 7 8))
  (.seq (.op (.exactBin .sub 9 2 6))
  (.seq (.op (.exactBin .div 9 9 5))
  (.seq (.op (.exactBin .add 9 9 6))
  (.seq (.op (.exactBin .add 7 7 6))
  (.seq (.op (.store 7 9))
  (.seq (.op (.exactBin .mul 2 4 5))
  (.seq (.op (.exactBin .shiftLeft 2 6 2))
  (.seq (.op (.copy 3 5))
  (.seq (.op (.copy 4 8))
  (.seq (.op (.copy 5 6))
  (.seq (.op (.const 1 0))
  (.seq (.op (.const 9 (8 + k)))
        (.op (.exactBin .add 0 0 9)))))))))))))))))

/-- When `0 < b` and `0 < q`, `(q - 1) / b + 1 = limbCountFromB b q`. -/
private theorem div_pred_add_one_eq_limbCountFromB {b q : ℕ} (hb : 0 < b) (hq : 0 < q) :
    (q - 1) / b + 1 = limbCountFromB b q := by
  dsimp only [limbCountFromB]
  have h : q + b - 1 = (q - 1) + 1 * b := by omega
  rw [h, Nat.add_mul_div_right _ _ hb]

/-- `storeHeaderPart1` executes deterministically in `17` steps. -/
theorem storeHeaderPart1_exec {w base r q M b : ℕ} {x : Data 18}
    (h0 : x.regs 0 = base) (h1 : x.regs 1 = r) (h2 : x.regs 2 = q)
    (h3 : x.regs 3 = M) (h4 : x.regs 4 = 2) (h5 : x.regs 5 = b) (h6 : x.regs 6 = 1)
    (hr_le : r ≤ q) (hM_le : M ≤ q)
    (hfit_end : Fits w (base + 8)) (hfit_q : Fits w (2 ^ q)) :
    ∃ y : Data 18,
      Exec w storeHeaderPart1 x y 17 ∧
      y.regs 0 = base ∧
      y.regs 2 = q ∧
      y.regs 4 = 2 ∧
      y.regs 5 = b ∧
      y.regs 6 = 1 ∧
      y.regs 7 = base + 5 ∧
      y.mem base = r ∧
      y.mem (base + 1) = q ∧
      y.mem (base + 2) = 2 ^ r - 1 ∧
      y.mem (base + 3) = 2 ^ q - 1 ∧
      y.mem (base + 4) = 2 ^ M - 1 ∧
      y.mem (base + 5) = b ∧
      (∀ a, (a < base ∨ base + 6 ≤ a) → y.mem a = x.mem a) := by
  have hpow_r : 2 ^ r ≤ 2 ^ q := Nat.pow_le_pow_right two_pos hr_le
  have hpow_M : 2 ^ M ≤ 2 ^ q := Nat.pow_le_pow_right two_pos hM_le
  wram_exec (disch := first | fits | layout_omega)
    [storeHeaderPart1, h0, h1, h2, h3, h4, h5, h6, Nat.shiftLeft_eq, Nat.one_mul]
  wram_simp [h0, h2, h4, h5, h6]
  exact fun _ _ => by wram_simp

/-- `storeHeaderPart2 k` executes deterministically in `17` steps. -/
theorem storeHeaderPart2_exec {w base q b k : ℕ} {x : Data 18}
    (hb : 0 < b) (hq : 0 < q)
    (h0 : x.regs 0 = base) (h2 : x.regs 2 = q) (h4 : x.regs 4 = 2)
    (h5 : x.regs 5 = b) (h6 : x.regs 6 = 1) (h7 : x.regs 7 = base + 5)
    (hfit_space : Fits w (base + spaceFromB b k)) (hfit_q : Fits w q) :
    ∃ y : Data 18,
      Exec w (storeHeaderPart2 k) x y 17 ∧
      y.regs 0 = base + 8 + k ∧
      y.regs 1 = 0 ∧
      y.regs 2 = 2 ^ (2 * b) ∧
      y.regs 3 = b ∧
      y.regs 4 = 2 ^ b - 1 ∧
      y.regs 5 = 1 ∧
      y.mem (base + 6) = 2 ^ b - 1 ∧
      y.mem (base + 7) = limbCountFromB b q ∧
      (∀ a, (a < base + 6 ∨ base + 8 ≤ a) → y.mem a = x.mem a) := by
  have hpow_le : 2 ^ b ≤ 2 ^ (2 * b) := Nat.pow_le_pow_right two_pos (by omega)
  have h2b_lt : 2 * b < 2 ^ (2 * b) := Nat.lt_two_pow_self
  have hdiv_le : (q - 1) / b ≤ q - 1 := Nat.div_le_self _ _
  have hfit_pow2b : Fits w (2 ^ (2 * b)) := by wram_omega
  wram_exec (disch := first | fits | layout_omega)
    [storeHeaderPart2, h0, h2, h4, h5, h6, h7, Nat.shiftLeft_eq, Nat.one_mul]
  wram_simp [h0, h2, h4, h5, h6, h7, div_pred_add_one_eq_limbCountFromB hb hq]
  exact ⟨by omega, fun _ _ => by wram_simp⟩

/-- 2-instruction suffix restoring `regBase = base` from `base + 8 + k`. -/
@[expose] def restoreBaseCode (k : ℕ) : Code .exact 18 :=
  .seq (.op (.const 9 (8 + k)))
        (.op (.exactBin .sub 0 0 9))

/-- Complete deterministic table initialization program `initTableCode k`: computes
`(r, q, b, L)` and masks from `(base, n_max, U, M)` in registers `0..3` and populates
`clmulTab[0 .. 2 ^ (2 * b) - 1]`. -/
@[expose] def initTableCode (k : ℕ) : Code .exact 18 :=
  .seq chunkBitsCode
  (.seq trinomialParamsCode
  (.seq storeHeaderPart1
  (.seq (storeHeaderPart2 k)
  (.seq clmulTabLoop
        (restoreBaseCode k)))))

/-- Exact step count of `initTableCode k`. -/
@[expose] def initTableSteps (n_max U M : ℕ) : ℕ :=
  19 * 2 ^ (2 * chunkBits n_max) +
    4 * Nat.log 2 (max n_max 2) +
    5 * Nat.clog 2 (max U 2) +
    5 * trinomialStep U M + 69

/-- **`KWise.initTableCode k` correctness and complexity**: from `reg 0 = base`, `reg 1 = n_max`,
`reg 2 = U`, `reg 3 = M`, `initTableCode k` halts deterministically in
`initTableSteps n_max U M = O(n_max + log U + log M)` instructions, establishing
`TableRep base (chunkBits n_max) U M k y.mem`, preserving `reg 0 = base`, and modifying memory
only within `[base, base + space n_max k)`. -/
theorem initTableCode_execWithin {w base n_max U M k : ℕ} {x : Data 18}
    (h0 : x.regs 0 = base) (h1 : x.regs 1 = n_max) (h2 : x.regs 2 = U) (h3 : x.regs 3 = M)
    (hfit_space : Fits w (base + space n_max k))
    (hfit_n : Fits w (max n_max 2)) (hfit_U : Fits w (max U 2 + 1))
    (hfit_q : Fits w (2 ^ trinomialDeg U M)) :
    ∃ y : Data 18,
      ExecWithin w (initTableCode k) x y (initTableSteps n_max U M) ∧
      TableRep base (chunkBits n_max) U M k y.mem ∧
      y.regs 0 = base ∧
      (∀ a, (a < base ∨ base + space n_max k ≤ a) → y.mem a = x.mem a) := by
  have hq_pos : 0 < trinomialDeg U M := by dsimp only [trinomialDeg]; positivity
  refine WP.exists_execWithin (WP.Exact.toWP ?_)
  wram_exec [initTableCode]
  wram_call (chunkBitsCode_exec h0 h1 h2 h3 hfit_n (by wram_omega))
    with d1 ⟨hd1_0, hd1_2, hd1_3, hd1_5, hd1_6, hd1_mem⟩
  wram_exec
  wram_call (trinomialParamsCode_exec hd1_0 hd1_2 hd1_3 hd1_5 hd1_6 hfit_U hfit_q)
    with d2 ⟨hd2_0, hd2_1, hd2_2, hd2_3, hd2_4, hd2_5, hd2_6, hd2_mem⟩
  wram_exec
  wram_call (storeHeaderPart1_exec hd2_0 hd2_1 hd2_2 hd2_3 hd2_4 hd2_5 hd2_6
    (by dsimp only [trinomialDeg]; omega) (le_trinomialDeg U M) (by wram_omega) hfit_q)
    with d3 ⟨hd3_0, hd3_2, hd3_4, hd3_5, hd3_6, hd3_7, hm0, hm1, hm2, hm3, hm4, hm5, hd3_out⟩
  wram_exec
  wram_call (storeHeaderPart2_exec (chunkBits_pos n_max) hq_pos hd3_0 hd3_2 hd3_4 hd3_5 hd3_6
    hd3_7 hfit_space (hfit_q.of_le Nat.lt_two_pow_self.le))
    with d4 ⟨hd4_0, hd4_1, hd4_2, hd4_3, hd4_4, hd4_5, hm6, hm7, hd4_out⟩
  wram_exec
  wram_call (clmulTabLoop_exec (by wram_omega) (2 ^ (2 * chunkBits n_max)) 0 d4 (by omega)
    hd4_0 hd4_1 hd4_2 hd4_3 hd4_4 hd4_5 fun _ hi => by omega)
    with d5 ⟨hd5_0, htab, hd5_out⟩
  wram_exec (disch := first | fits | layout_omega) [restoreBaseCode, hd5_0]
  refine ⟨by dsimp only [initTableSteps]; omega, ?_, by wram_simp; omega, fun a ha => ?_⟩
  · wram_simp [TableRep]
    simp (disch := omega) only [hd5_out, hd4_out, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, true_and]
    exact htab
  · wram_simp [hd5_out a (by wram_omega), hd4_out a (by wram_omega),
      hd3_out a (by wram_omega), hd2_mem, hd1_mem]

/-- Setup prefix for `resampleCode k`: loads `2 ^ q - 1` from `base + 3` into register `1` and
initializes `ptr = base + 8` (`reg 2`), `end = base + 8 + k` (`reg 3`), and `one = 1` (`reg 4`). -/
@[expose] def resampleSetupCode (k : ℕ) : Code .exact 18 :=
  .seq (.op (.const 1 3))
  (.seq (.op (.exactBin .add 1 0 1))
  (.seq (.op (.load 1 1))
  (.seq (.op (.const 2 8))
  (.seq (.op (.exactBin .add 2 0 2))
  (.seq (.op (.const 3 k))
  (.seq (.op (.exactBin .add 3 2 3))
        (.op (.const 4 1))))))))

/-- Closed-form state after `resampleSetupCode k`. -/
@[expose] def resampleSetupData (base U M k : ℕ) (x : Data 18) : Data 18 :=
  ((((x.set 1 (2 ^ trinomialDeg U M - 1)).set 2 (base + 8)).set 3 (base + 8 + k)).set 4 1)

/-- Injective register map embedding `randFillLoop` into `Data 18` so `regExtra` (`5`) maps to
`regBase` (`0`). -/
@[expose] def resampleMap : Fin 6 → Fin 18 :=
  ![2, 3, 1, 4, 5, 0]

theorem injective_resampleMap : Function.Injective resampleMap := by
  decide

/-- Seed-resampling program `resampleCode k`: samples the `k` polynomial coefficients
`seed[0 .. k - 1]` uniformly in `Fin (2 ^ trinomialDeg U M)` using `k` `Code.rand` calls in
`5 * k + 10` instructions while preserving `TableRep` and `regBase = base`. -/
@[expose] def resampleCode (k : ℕ) : Code .exact 18 :=
  .seq (resampleSetupCode k) (randFillLoop.rename resampleMap)

/-- Exact `ProbComp` semantics of `resampleCode k`. -/
@[expose] noncomputable def resampleComp (base U M k : ℕ) (x : Data 18) : ProbComp (Data 18 × ℕ) :=
  let d0 := resampleSetupData base U M k x
  (fun z : Data 6 × ℕ => (z.1.extend resampleMap d0, 8 + z.2)) <$>
    randFillComp (trinomialDeg U M) (base + 8) k (d0.comap resampleMap)

/-- `resampleSetupCode k` executes deterministically in `8` steps. -/
theorem resampleSetupCode_exec {w base b U M k : ℕ} {x : Data 18}
    (htab : TableRep base b U M k x.mem) (h0 : x.regs 0 = base)
    (hfit_end : Fits w (base + 8 + k)) :
    Exec w (resampleSetupCode k) x (resampleSetupData base U M k x) 8 := by
  obtain ⟨-, -, -, hm3, -⟩ := htab
  wram_exec [resampleSetupCode, h0, hm3]
  ext i : 2 <;> [fin_cases i <;> rfl; rfl]

/-- **`KWise.resampleCode k` exact randomized execution**: executes with exact `ProbComp`
semantics `resampleComp base U M k x`. -/
theorem resampleCode_execRand {w base b U M k : ℕ} {x : Data 18}
    (htab : TableRep base b U M k x.mem) (h0 : x.regs 0 = base)
    (hfit_end : Fits w (base + 8 + k)) (hfit_q : Fits w (2 ^ trinomialDeg U M)) :
    ExecRand w (resampleCode k) x (resampleComp base U M k x) := by
  unfold resampleCode
  refine WP.Rand.execRand ?_
  wram_rand_call (resampleSetupCode_exec htab h0 hfit_end)
  wram_rand_call (randFillLoop_execRand (bits := trinomialDeg U M) (arrBase := base + 8) k
    (by simp +decide [resampleSetupData, resampleMap, Data.comap, regPtr])
    (by simp +decide [resampleSetupData, resampleMap, Data.comap, regEnd])
    (by simp +decide [resampleSetupData, resampleMap, Data.comap, regMask])
    (by simp +decide [resampleSetupData, resampleMap, Data.comap, regOne]) hfit_end (by fits))
    renamed injective_resampleMap
  simp only [resampleComp, Functor.map_map]

/-- **Uniformity of resampled seeds**: under `(resampleComp base U M k x).eval`, the extracted seed
tuple `extractSeeds base U M k z.1.mem` is uniformly distributed over
`Fin k → Fin (2 ^ trinomialDeg U M)`. -/
theorem map_extractSeeds_eval_resampleComp (base U M k : ℕ) (x : Data 18) :
    ((resampleComp base U M k x).eval).map (fun z => extractSeeds base U M k z.1.mem) =
      PMF.uniformOfFintype (Fin k → Fin (2 ^ trinomialDeg U M)) := by
  dsimp only [resampleComp, extractSeeds]
  rw [ProbComp.eval_map, PMF.map_comp]
  exact map_extractSlice_eval_randFillComp (trinomialDeg U M) (base + 8) k _

/-- Every outcome `z ∈ (resampleComp base U M k x).support` preserves `TableRep base b U M k`,
establishes `Rep base b U M k (extractSeeds base U M k z.1.mem) z.1.mem`, sets `z.1.regs 0 = base`,
modifies memory only within `[base + 8, base + 8 + k)`, and takes at most `5 * k + 10` steps. -/
theorem mem_support_resampleComp {base b U M k : ℕ} {x : Data 18}
    (htab : TableRep base b U M k x.mem) (h0 : x.regs 0 = base)
    {z : Data 18 × ℕ} (hz : z ∈ (resampleComp base U M k x).support) :
    (Rep base b U M k (extractSeeds base U M k z.1.mem) z.1.mem ∧
      z.1.regs 0 = base ∧
      (∀ a, (a < base + 8 ∨ base + 8 + k ≤ a) → z.1.mem a = x.mem a)) ∧
    z.2 ≤ 5 * k + 10 := by
  dsimp only [resampleComp] at hz
  supp_cases hz with ⟨z0, hz0, rfl⟩
  obtain ⟨hsteps, -, -, -, -, hextra, hlt, hout⟩ := mem_support_randFillComp hz0
  have htab' : TableRep base b U M k z0.1.mem := by
    simpa (disch := omega) only [TableRep, hout, Data.comap_mem, resampleSetupData,
      Data.set_mem] using htab
  have hseed : SeedRep base U M k (extractSeeds base U M k z0.1.mem) z0.1.mem := fun j => by
    simp [extractSeeds, extractSlice, hlt j.val j.isLt]
  have hbase' : (z0.1.extend resampleMap (resampleSetupData base U M k x)).regs 0 = base := by
    change ((z0.1.extend resampleMap (resampleSetupData base U M k x)).comap
      resampleMap).regs regExtra = base
    rw [Data.comap_extend injective_resampleMap, hextra]
    simpa +decide [resampleSetupData, resampleMap, Data.comap, regExtra] using h0
  exact ⟨⟨⟨htab', hseed⟩, hbase', hout⟩, by omega⟩

/-- **`KWise.resampleCode k` Hoare-style specification**: halts in `5 * k + 10 = O(k)` steps and `k`
`rand` queries, preserving `TableRep base b U M k`, establishing
`Rep base b U M k (extractSeeds base U M k z.1.mem) z.1.mem`, preserving `reg 0 = base`, and
modifying memory only within `[base + 8, base + 8 + k)`. -/
theorem resampleCode_execRandWithin {w base b U M k : ℕ} {x : Data 18}
    (htab : TableRep base b U M k x.mem) (h0 : x.regs 0 = base)
    (hfit_end : Fits w (base + 8 + k)) (hfit_q : Fits w (2 ^ trinomialDeg U M)) :
    ExecRandWithin w (resampleCode k) x
      (fun y =>
        Rep base b U M k (extractSeeds base U M k y.mem) y.mem ∧
        y.regs 0 = base ∧
        (∀ a, (a < base + 8 ∨ base + 8 + k ≤ a) → y.mem a = x.mem a))
      (5 * k + 10) k :=
  ⟨resampleComp base U M k x, resampleCode_execRand htab h0 hfit_end hfit_q,
    (OracleComp.isCostBounded_map_iff _ _ _).mpr
      (isQueryBounded_randFillComp (trinomialDeg U M) (base + 8) k _),
    fun _ hz => mem_support_resampleComp htab h0 hz⟩

/-- Full one-shot initialization program `initCode k := .seq (initTableCode k) (resampleCode k)`. -/
@[expose] def initCode (k : ℕ) : Code .exact 18 :=
  .seq (initTableCode k) (resampleCode k)

/-- **`KWise.initCode k` Hoare-style specification**: runs `initTableCode k` followed by
`resampleCode k` in `initTableSteps n_max U M + (5 * k + 10)` steps and `k` `rand` calls. -/
theorem initCode_execRandWithin {w base n_max U M k : ℕ} {x : Data 18}
    (h0 : x.regs 0 = base) (h1 : x.regs 1 = n_max) (h2 : x.regs 2 = U) (h3 : x.regs 3 = M)
    (hfit_space : Fits w (base + space n_max k))
    (hfit_n : Fits w (max n_max 2)) (hfit_U : Fits w (max U 2 + 1))
    (hfit_q : Fits w (2 ^ trinomialDeg U M)) :
    ExecRandWithin w (initCode k) x
      (fun y =>
        Rep base (chunkBits n_max) U M k (extractSeeds base U M k y.mem) y.mem ∧
        y.regs 0 = base ∧
        (∀ a, (a < base ∨ base + space n_max k ≤ a) → y.mem a = x.mem a))
      (initTableSteps n_max U M + (5 * k + 10)) k := by
  unfold initCode
  refine WP.RandWithin.execRandWithin ?_
  wram_rand_call (initTableCode_execWithin h0 h1 h2 h3 hfit_space hfit_n hfit_U hfit_q)
    with dTab ⟨htab, hdTab_0, hdTab_out⟩
  wram_rand_call (resampleCode_execRandWithin htab hdTab_0 (by wram_omega) hfit_q)
  rintro y ⟨hrep, hy0, hy_out⟩
  exact ⟨hrep, hy0, fun a ha => (hy_out a (by wram_omega)).trans (hdTab_out a ha)⟩

/-! ## Section 4: Deterministic Horner evaluation (`evalCode`) and `k`-wise independence -/

/-- Register `1`: holds the input key `u < U` on entry to `evalCode`. -/
abbrev regKey : Fin 18 := 1

/-- Register `2`: holds the output hash value `< 2 ^ M` on exit from `evalCode`. -/
abbrev regOut : Fin 18 := 2

private theorem xor_clmul_split_right (acc a v b sh : ℕ) :
    (acc ^^^ (clmul a (v &&& (2 ^ b - 1)) <<< sh)) ^^^ (clmul a (v >>> b) <<< (sh + b)) =
      acc ^^^ (clmul a v <<< sh) := by
  rw [Nat.xor_assoc, Nat.add_comm sh b, Nat.shiftLeft_add, ← Nat.shiftLeft_xor_distrib,
    ← clmul_shiftLeft_right, ← clmul_xor_right, and_xor_shiftRight_shiftLeft]

private theorem shiftLeft_lt_two_pow_two_mul {u b : ℕ} (hu : u < 2 ^ b) :
    u <<< b < 2 ^ (2 * b) ∧ u < 2 ^ (2 * b) :=
  ⟨by rw [Nat.shiftLeft_eq, two_mul, pow_add]; exact Nat.mul_lt_mul_of_pos_right hu (by positivity),
   hu.trans_le (Nat.pow_le_pow_right two_pos (by omega))⟩

private theorem shiftLeft_xor_parts {u v b : ℕ} (hu : u < 2 ^ b) (hv : v < 2 ^ b) :
    (u <<< b) ^^^ v < 2 ^ (2 * b) ∧
    ((u <<< b) ^^^ v) >>> b = u ∧
    ((u <<< b) ^^^ v) &&& (2 ^ b - 1) = v := by
  have hv_bit {k : ℕ} (hk : b ≤ k) : v.testBit k = false :=
    Nat.testBit_lt_two_pow (hv.trans_le (Nat.pow_le_pow_right two_pos hk))
  refine ⟨Nat.xor_lt_two_pow (shiftLeft_lt_two_pow_two_mul hu).1
    (shiftLeft_lt_two_pow_two_mul hv).2, Nat.eq_of_testBit_eq fun i => ?_,
    Nat.eq_of_testBit_eq fun i => ?_⟩
  · simp [Nat.testBit_shiftRight, Nat.testBit_xor, Nat.testBit_shiftLeft,
      hv_bit (Nat.le_add_right b i)]
  · by_cases hi : i < b
    · simp [Nat.testBit_xor, Nat.testBit_shiftLeft, hi, not_le.mpr hi]
    · simp [Nat.testBit_xor, Nat.testBit_shiftLeft, hi, hv_bit (not_lt.mp hi)]

private theorem and_mask_bounds (v b : ℕ) :
    v &&& (2 ^ b - 1) < 2 ^ b ∧
    (v &&& (2 ^ b - 1)) <<< b < 2 ^ (2 * b) ∧
    v &&& (2 ^ b - 1) < 2 ^ (2 * b) := by
  have hlt : v &&& (2 ^ b - 1) < 2 ^ b :=
    Nat.and_two_pow_sub_one_eq_mod v b ▸ Nat.mod_lt v (Nat.two_pow_pos b)
  exact ⟨hlt, shiftLeft_lt_two_pow_two_mul hlt⟩

private theorem shiftRight_step_bounds {w q b rem v sh bound : ℕ}
    (hb : 0 < b) (hw : 2 * q ≤ w)
    (hv_lt : v < 2 ^ ((rem + 1) * b)) (hv_bound : v * 2 ^ sh < 2 ^ q)
    (hrem_le : (rem + 1) * b ≤ bound) (hfit_bound : Fits w bound) :
    v >>> b < 2 ^ (rem * b) ∧
    (v >>> b) * 2 ^ (sh + b) < 2 ^ q ∧
    Fits w (v >>> b) ∧
    Fits w rem := by
  have hv_lt_q : v < 2 ^ q := (Nat.le_mul_of_pos_right _ (by positivity)).trans_lt hv_bound
  have hrem_mul : rem * 1 ≤ (rem + 1) * b := Nat.mul_le_mul (by omega) hb
  refine ⟨?_, ?_, Fits.mono ((Nat.shiftRight_le v b).trans_lt hv_lt_q) (by omega),
    hfit_bound.of_le (by omega)⟩
  · rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_of_lt_mul (by rwa [← pow_add, show b + rem * b = (rem + 1) * b by ring])
  · rw [Nat.shiftRight_eq_div_pow, pow_add, ← mul_assoc, mul_comm (v / 2 ^ b), mul_assoc]
    exact (Nat.mul_le_mul_left (2 ^ sh) (Nat.div_mul_le_self v (2 ^ b))).trans_lt
      (by rwa [mul_comm])

/-- Body of `innerClmulLoop`: looks up `clmul (x_rem &&& mask_b) (y_rem &&& mask_b)` in `clmulTab`,
shifts left by `shift_j`, XORs into `acc` (`reg 2`), shifts `y_rem` right by `b`, advances
`shift_j` by `b`, and decrements `rem_j`. -/
@[expose] def innerClmulBody : Code .exact 18 :=
  .seq (.op (.exactBin .and 17 15 5))
  (.seq (.op (.exactBin .xor 17 13 17))
  (.seq (.op (.exactBin .add 17 7 17))
  (.seq (.op (.load 17 17))
  (.seq (.op (.exactBin .shiftLeft 17 17 16))
  (.seq (.op (.exactBin .xor 2 2 17))
  (.seq (.op (.exactBin .shiftRight 15 15 4))
  (.seq (.op (.exactBin .add 16 16 4))
        (.op (.exactBin .sub 14 14 8)))))))))

/-- Inner Four-Russians loop `while 0 < rem_j do innerClmulBody`. -/
@[expose] def innerClmulLoop : Code .exact 18 :=
  .loop (.lt 9 14) innerClmulBody

/-- `innerClmulLoop` executes deterministically in `11 * rem_j + 2` steps, XORing
`clmul (x_rem &&& (2 ^ b - 1)) y_rem <<< (sh_x + sh_y)` into `reg 2` (`acc`). -/
theorem innerClmulLoop_exec {w tabBase b q x_rem sh_x : ℕ}
    (hb : 0 < b) (hw : 2 * q ≤ w)
    (hfit_tabEnd : Fits w (tabBase + 2 ^ (2 * b)))
    (hx_bound : x_rem * 2 ^ sh_x < 2 ^ q) :
    ∀ rem_j y_rem sh_y acc : ℕ, ∀ s : Data 18,
      y_rem < 2 ^ (rem_j * b) →
      y_rem * 2 ^ sh_y < 2 ^ q →
      acc < 2 ^ (2 * q) →
      Fits w (sh_x + sh_y + rem_j * b) →
      s.regs 2 = acc →
      s.regs 4 = b →
      s.regs 5 = 2 ^ b - 1 →
      s.regs 7 = tabBase →
      s.regs 8 = 1 →
      s.regs 9 = 0 →
      s.regs 13 = (x_rem &&& (2 ^ b - 1)) <<< b →
      s.regs 14 = rem_j →
      s.regs 15 = y_rem →
      s.regs 16 = sh_x + sh_y →
      (∀ i < 2 ^ (2 * b), s.mem (tabBase + i) = clmul (i >>> b) (i &&& (2 ^ b - 1))) →
      ∃ y : Data 18,
        Exec w innerClmulLoop s y (11 * rem_j + 2) ∧
        y.regs 2 = acc ^^^ (clmul (x_rem &&& (2 ^ b - 1)) y_rem <<< (sh_x + sh_y)) ∧
        (∀ r : Fin 18, r ≠ 2 ∧ r ≠ 14 ∧ r ≠ 15 ∧ r ≠ 16 ∧ r ≠ 17 → y.regs r = s.regs r) ∧
        y.mem = s.mem := by
  intro rem_j
  induction rem_j with
  | zero =>
    intro y_rem _ _ s hy_lt _ _ _ h2 _ _ _ _ h9 _ h14 _ _ _
    exact ⟨s, Exec.loop_exit (by simp [Cond.Holds, h9, h14]),
      by simp [h2, show y_rem = 0 by simpa using hy_lt], fun _ _ => rfl, rfl⟩
  | succ rem_j ih =>
    intro y_rem sh_y acc s hy_lt hy_bound hacc_lt hfit_sh h2 h4 h5 h7 h8 h9 h13 h14 h15 h16 htab
    obtain ⟨hxc_lt, -, -⟩ := and_mask_bounds x_rem b
    obtain ⟨hyc_lt, -, hyc_lt2⟩ := and_mask_bounds y_rem b
    set xc := x_rem &&& (2 ^ b - 1) with hxc
    set yc := y_rem &&& (2 ^ b - 1) with hyc
    obtain ⟨hidx_lt, hidx_u, hidx_v⟩ := shiftLeft_xor_parts hxc_lt hyc_lt
    set idx := (xc <<< b) ^^^ yc with hidx
    have hval_sh_lt : clmul xc yc <<< (sh_x + sh_y) < 2 ^ (2 * q) :=
      clmul_shiftLeft_lt ((Nat.mul_le_mul_right _ Nat.and_le_left).trans_lt hx_bound)
        ((Nat.mul_le_mul_right _ Nat.and_le_left).trans_lt hy_bound)
    have hacc'_lt := Nat.xor_lt_two_pow hacc_lt hval_sh_lt
    have hfit_val_sh : Fits w (clmul xc yc <<< (sh_x + sh_y)) := Fits.mono hval_sh_lt hw
    have hfit_acc' : Fits w (acc ^^^ (clmul xc yc <<< (sh_x + sh_y))) := Fits.mono hacc'_lt hw
    obtain ⟨hy_shr_lt, hy_shr_bound, hfit_y_shr, hfit_rem⟩ :=
      shiftRight_step_bounds hb hw hy_lt hy_bound (by omega) hfit_sh
    have hfit_sh_next : Fits w (sh_x + sh_y + b) := hfit_sh.of_le (by rw [Nat.succ_mul]; omega)
    refine WP.Exact.exists_exec (WP.Exact.loop_iter (by simp [Cond.Holds, h9, h14]) ?_)
    wram_exec (disch := first | fits | exact hfit_tabEnd.of_le (by omega) | omega)
      [innerClmulBody, h2, h4, h5, h7, h8, h13, h14, h15, h16, ← hxc, ← hyc, ← hidx,
        show s.mem (tabBase + idx) = clmul xc yc by rw [htab idx hidx_lt, hidx_u, hidx_v]]
    wram_call (ih (y_rem >>> b) (sh_y + b) (acc ^^^ (clmul xc yc <<< (sh_x + sh_y))) _ hy_shr_lt
      hy_shr_bound hacc'_lt (by rwa [show sh_x + (sh_y + b) + rem_j * b =
        sh_x + sh_y + (rem_j + 1) * b by ring])
      (by wram_simp) (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame)
      (by regs_frame) (by regs_frame) (by wram_simp) (by wram_simp)
      (by wram_simp [Nat.add_assoc]) htab) with y ⟨hy2, hy_regs, hy_mem⟩
    exact ⟨by omega, hy2.trans (by rw [← Nat.add_assoc]; exact xor_clmul_split_right _ _ _ _ _),
      fun r ⟨hr2, hr14, hr15, hr16, hr17⟩ => by
        rw [hy_regs r ⟨hr2, hr14, hr15, hr16, hr17⟩]; wram_simp, hy_mem⟩

/-- Body of `outerClmulLoop`: computes `x_chunk_sh = (x_rem &&& mask_b) <<< b`, initializes the
inner loop over `L` limbs of `u` starting at shift `shift_i`, runs `innerClmulLoop`, and advances
`x_rem`, `shift_i`, and `rem_i`. -/
@[expose] def outerClmulBody : Code .exact 18 :=
  .seq (.op (.exactBin .and 13 11 5))
  (.seq (.op (.exactBin .shiftLeft 13 13 4))
  (.seq (.op (.copy 14 6))
  (.seq (.op (.copy 15 1))
  (.seq (.op (.copy 16 12))
  (.seq innerClmulLoop
  (.seq (.op (.exactBin .shiftRight 11 11 4))
  (.seq (.op (.exactBin .add 12 12 4))
        (.op (.exactBin .sub 10 10 8)))))))))

/-- Outer Four-Russians loop `while 0 < rem_i do outerClmulBody`. -/
@[expose] def outerClmulLoop : Code .exact 18 :=
  .loop (.lt 9 10) outerClmulBody

/-- `outerClmulLoop` executes deterministically in `(11 * L + 12) * rem_i + 2` steps, XORing
`clmul x_rem u <<< sh_x` into `reg 2` (`acc`). -/
theorem outerClmulLoop_exec {w tabBase b q L u : ℕ}
    (hb : 0 < b) (hw : 2 * q ≤ w)
    (hfit_tabEnd : Fits w (tabBase + 2 ^ (2 * b)))
    (hu_limbs : u < 2 ^ (L * b)) (hu_bound : u < 2 ^ q) :
    ∀ rem_i x_rem sh_x acc : ℕ, ∀ s : Data 18,
      x_rem < 2 ^ (rem_i * b) →
      x_rem * 2 ^ sh_x < 2 ^ q →
      acc < 2 ^ (2 * q) →
      Fits w (sh_x + rem_i * b + L * b) →
      s.regs 1 = u →
      s.regs 2 = acc →
      s.regs 4 = b →
      s.regs 5 = 2 ^ b - 1 →
      s.regs 6 = L →
      s.regs 7 = tabBase →
      s.regs 8 = 1 →
      s.regs 9 = 0 →
      s.regs 10 = rem_i →
      s.regs 11 = x_rem →
      s.regs 12 = sh_x →
      (∀ i < 2 ^ (2 * b), s.mem (tabBase + i) = clmul (i >>> b) (i &&& (2 ^ b - 1))) →
      ∃ y : Data 18,
        Exec w outerClmulLoop s y ((11 * L + 12) * rem_i + 2) ∧
        y.regs 2 = acc ^^^ (clmul x_rem u <<< sh_x) ∧
        (∀ r : Fin 18, r.val < 10 ∧ r ≠ 2 → y.regs r = s.regs r) ∧
        y.mem = s.mem := by
  intro rem_i
  induction rem_i with
  | zero =>
    intro x_rem _ _ s hx_lt _ _ _ _ h2 _ _ _ _ _ h9 h10 _ _ _
    exact ⟨s, Exec.loop_exit (by simp [Cond.Holds, h9, h10]),
      by simp [h2, show x_rem = 0 by simpa using hx_lt], fun _ _ => rfl, rfl⟩
  | succ rem_i ih =>
    intro x_rem sh_x acc s hx_lt hx_bound hacc_lt hfit_sh h1 h2 h4 h5 h6 h7 h8 h9 h10 h11 h12 htab
    obtain ⟨hxc_lt, hxc_sh_lt, hxc_lt2⟩ := and_mask_bounds x_rem b
    set xc := x_rem &&& (2 ^ b - 1) with hxc
    obtain ⟨hx_shr_lt, hx_shr_bound, hfit_x_shr, hfit_rem_i⟩ :=
      shiftRight_step_bounds hb hw hx_lt hx_bound (by omega) hfit_sh
    have hfit_sh_next : Fits w (sh_x + b) := hfit_sh.of_le (by rw [Nat.succ_mul]; omega)
    have hacc'_lt : acc ^^^ (clmul xc u <<< sh_x) < 2 ^ (2 * q) :=
      Nat.xor_lt_two_pow hacc_lt (clmul_shiftLeft_lt (sh_y := 0)
        ((Nat.mul_le_mul_right _ Nat.and_le_left).trans_lt hx_bound) (by simpa using hu_bound))
    refine WP.Exact.exists_exec (WP.Exact.loop_iter (by simp [Cond.Holds, h9, h10]) ?_)
    wram_exec (disch := first | fits | exact hfit_tabEnd.of_le (by omega) | omega)
      [outerClmulBody, h1, h4, h5, h6, h11, h12, ← hxc]
    wram_call (innerClmulLoop_exec hb hw hfit_tabEnd hx_bound L u 0 acc _ hu_limbs
      (by simpa using hu_bound) hacc_lt (hfit_sh.of_le (by omega)) (by regs_frame) (by regs_frame)
      (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame) (by wram_simp [hxc])
      (by wram_simp) (by wram_simp) (by wram_simp) htab)
      with s6 ⟨hs6_2, hs6_regs, hs6_mem⟩
    wram_exec [hs6_regs, h4, h8, h10, h11, h12]
    wram_call (ih (x_rem >>> b) (sh_x + b) (acc ^^^ (clmul xc u <<< sh_x)) _ hx_shr_lt hx_shr_bound
      hacc'_lt (by rwa [show sh_x + b + rem_i * b + L * b =
        sh_x + (rem_i + 1) * b + L * b by ring])
      (by regs_frame) (by wram_simp [hs6_2, hxc]) (by regs_frame) (by regs_frame) (by regs_frame)
      (by regs_frame) (by regs_frame) (by regs_frame) (by wram_simp) (by wram_simp) (by wram_simp)
      (fun i hi => by wram_simp [hs6_mem, htab i hi])) with y ⟨hy2, hy_regs, hy_mem⟩
    refine ⟨by ring, hy2.trans ?_, fun r ⟨hr_lt, hr2⟩ => by
      rw [hy_regs r ⟨hr_lt, hr2⟩]; wram_simp [hs6_regs], hy_mem.trans hs6_mem⟩
    simpa only [clmul_comm _ u] using xor_clmul_split_right acc u x_rem b sh_x

/-- 16-instruction straight-line reduction block on `Data 18`: loads `r`, `q = 2 * r`,
`2 ^ r - 1`, and `2 ^ q - 1` from `base + 0 .. base + 3` into registers `10..13` and replaces `c`
in `reg 2` with `reduceTrinomialCode (trinomialStep U M) c`, preserving registers `0, 1, 3..9` and
memory. -/
@[expose] def reduceStepCode : Code .exact 18 :=
  .seq (.op (.load 10 0))
  (.seq (.op (.exactBin .add 15 0 8))
  (.seq (.op (.load 11 15))
  (.seq (.op (.exactBin .add 15 15 8))
  (.seq (.op (.load 12 15))
  (.seq (.op (.exactBin .add 15 15 8))
  (.seq (.op (.load 13 15))
  (.seq (.op (.exactBin .add 14 11 10))
  (.seq (.op (.exactBin .shiftRight 15 2 14))
  (.seq (.op (.exactBin .shiftRight 16 2 11))
  (.seq (.op (.exactBin .and 16 16 12))
  (.seq (.op (.exactBin .and 2 2 13))
  (.seq (.op (.exactBin .xor 2 2 15))
  (.seq (.op (.exactBin .xor 2 2 16))
  (.seq (.op (.exactBin .shiftLeft 16 16 10))
        (.op (.exactBin .xor 2 2 16))))))))))))))))

/-- `reduceStepCode` executes deterministically in `16` instructions, replacing `c` in `reg 2`
with `reduceTrinomialCode (trinomialStep U M) c`. -/
theorem reduceStepCode_exec {w base b U M k c : ℕ} {s : Data 18}
    (htab : TableRep base b U M k s.mem)
    (hw : 2 * trinomialDeg U M ≤ w)
    (hfit_end8 : Fits w (base + 8))
    (hc : c < 2 ^ (2 * trinomialDeg U M))
    (h0 : s.regs 0 = base) (h2 : s.regs 2 = c) (h8 : s.regs 8 = 1) :
    ∃ y : Data 18,
      Exec w reduceStepCode s y 16 ∧
      y.regs 2 = reduceTrinomialCode (trinomialStep U M) c ∧
      (∀ r : Fin 18, r.val < 10 ∧ r ≠ 2 → y.regs r = s.regs r) ∧
      y.mem = s.mem := by
  set r := 3 ^ trinomialStep U M
  set q := trinomialDeg U M
  obtain ⟨hm0, hm1, hm2, hm3, -⟩ := htab
  have hfit_3r : Fits w (q + r) := Fits.mono
    ((show q + r ≤ 2 * q by dsimp only [q, trinomialDeg, r]; omega).trans_lt Nat.lt_two_pow_self) hw
  have hfit_c2r : Fits w (c >>> q) := (Fits.mono hc hw).of_le (Nat.shiftRight_le _ _)
  have hcLow_lt : c &&& (2 ^ q - 1) < 2 ^ q := (and_mask_bounds c q).1
  have hc3_lt : c >>> (q + r) < 2 ^ q := by
    rw [Nat.shiftRight_eq_div_pow]
    exact (Nat.div_lt_of_lt_mul (by rwa [← pow_add, show q + r + r = 2 * q by
      dsimp only [q, trinomialDeg, r]; omega])).trans_le
      (Nat.pow_le_pow_right two_pos (by dsimp only [q, trinomialDeg, r]; omega))
  obtain ⟨-, hc2_sh_lt, hc2_lt⟩ := (rfl : q = 2 * r) ▸ and_mask_bounds (c >>> q) r
  wram_exec [reduceStepCode, h0, h2, h8, hm0, hm1, hm2, hm3, Nat.add_assoc]
  · refine ⟨?_, fun _ ⟨_, _⟩ => by wram_simp, rfl⟩
    wram_simp [reduceTrinomialCode, q, trinomialDeg, r,
      show 2 * 3 ^ trinomialStep U M + 3 ^ trinomialStep U M = 3 * 3 ^ trinomialStep U M by ring]
  all_goals
    exact Fits.mono (w := q)
      (by (repeat' apply Nat.xor_lt_two_pow); all_goals assumption) (by omega)

/-- Body of `hornerLoop` on `Data 18`: decrements `j` (`reg 3`), multiplies `acc` (`reg 2`) by
`u` (`reg 1`) in `TrinomialField (trinomialStep U M)` via `outerClmulLoop` and `reduceStepCode`,
and adds `seed[j]` from `mem[base + 8 + j]`. -/
@[expose] def hornerBody : Code .exact 18 :=
  .seq (.op (.exactBin .sub 3 3 8))
  (.seq (.op (.copy 11 2))
  (.seq (.op (.copy 2 9))
  (.seq (.op (.copy 10 6))
  (.seq (.op (.copy 12 9))
  (.seq outerClmulLoop
  (.seq reduceStepCode
  (.seq (.op (.const 15 8))
  (.seq (.op (.exactBin .add 15 0 15))
  (.seq (.op (.exactBin .add 15 15 3))
  (.seq (.op (.load 15 15))
        (.op (.exactBin .xor 2 2 15))))))))))))

/-- Horner evaluation loop `while 0 < j do hornerBody`. -/
@[expose] def hornerLoop : Code .exact 18 :=
  .loop (.lt 9 3) hornerBody

private theorem fits_two_mul_limbCount {w base b q k : ℕ}
    (hb : 0 < b) (hw : 2 * q ≤ w) (hfit : Fits w (base + spaceFromB b k)) :
    Fits w (0 + limbCountFromB b q * b + limbCountFromB b q * b) := by
  have hdiv := Nat.div_mul_le_self (q + b - 1) b
  have h2b_lt : 2 * b < w := hfit.lt_of_pow_le (by wram_omega)
  have hlt : w - 1 < 2 ^ (w - 1) := Nat.lt_two_pow_self
  have hpow : 2 ^ w = 2 ^ (w - 1) * 2 := by rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ w)]
  dsimp only [Fits, limbCountFromB] at *; omega

private theorem horner_step_arith {t k m : ℕ} (hm : m + 1 ≤ k)
    (c : Fin k → Fin (2 ^ (2 * 3 ^ t))) {u : ℕ} (hu : u < 2 ^ (2 * 3 ^ t))
    (acc : TrinomialField t) :
    let c_field : Fin k → TrinomialField t := fun j => (TrinomialField.equivFin t).symm (c j)
    let x_field : TrinomialField t := AdjoinRoot.mk (trinomial t) (polyOfCode u)
    let acc_next := acc * x_field + c_field ⟨m, by omega⟩
    reduceTrinomialCode t (clmul (TrinomialField.equivFin t acc).val u) ^^^
      (c ⟨m, by omega⟩).val = (TrinomialField.equivFin t acc_next).val ∧
    acc_next * x_field ^ m +
        ∑ i : Fin m, c_field (Fin.castLE (Nat.le_of_succ_le hm) i) * x_field ^ (i : ℕ) =
      acc * x_field ^ (m + 1) +
        ∑ i : Fin (m + 1), c_field (Fin.castLE hm i) * x_field ^ (i : ℕ) := by
  intro c_field x_field acc_next
  refine ⟨?_, ?_⟩
  · have hx_val : (TrinomialField.equivFin t x_field).val = u :=
      TrinomialField.val_equivFin_mk_polyOfCode t hu
    have hc_val : (c ⟨m, by omega⟩).val =
        (TrinomialField.equivFin t (c_field ⟨m, by omega⟩)).val :=
      congrArg Fin.val ((TrinomialField.equivFin t).apply_symm_apply _).symm
    rw [TrinomialField.val_equivFin_add, TrinomialField.val_equivFin_mul, hx_val, hc_val]
  · rw [Fin.sum_univ_castSucc]
    simp only [acc_next, Fin.val_castSucc, Fin.val_last, pow_succ,
      show ∀ i : Fin m, Fin.castLE hm i.castSucc = Fin.castLE (Nat.le_of_succ_le hm) i from
        fun _ => rfl,
      show Fin.castLE hm (Fin.last m) = ⟨m, by omega⟩ from rfl]
    ring

/-- `hornerLoop` executes deterministically in `((11 * L + 12) * L + 30) * m + 2` instructions,
updating `reg 2` from `(equivFin t acc).val` to
`(equivFin t (acc * x ^ m + ∑ i : Fin m, c_field (Fin.castLE hm i) * x ^ (i : ℕ))).val`. -/
theorem hornerLoop_exec {w base b U M k : ℕ}
    {c : Fin k → Fin (2 ^ trinomialDeg U M)} (u : Fin U)
    (hb : 0 < b) (hw : 2 * trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + spaceFromB b k)) :
    let t := trinomialStep U M
    let q := trinomialDeg U M
    let L := limbCountFromB b q
    let c_field : Fin k → TrinomialField t := fun j => (TrinomialField.equivFin t).symm (c j)
    let x_field : TrinomialField t := AdjoinRoot.mk (trinomial t) (polyOfCode u.val)
    ∀ m : ℕ, ∀ hm : m ≤ k, ∀ acc : TrinomialField t, ∀ s : Data 18,
      Rep base b U M k c s.mem →
      s.regs 0 = base →
      s.regs 1 = u.val →
      s.regs 2 = (TrinomialField.equivFin t acc).val →
      s.regs 3 = m →
      s.regs 4 = b →
      s.regs 5 = 2 ^ b - 1 →
      s.regs 6 = L →
      s.regs 7 = base + 8 + k →
      s.regs 8 = 1 →
      s.regs 9 = 0 →
      ∃ y : Data 18,
        Exec w hornerLoop s y (((11 * L + 12) * L + 30) * m + 2) ∧
        y.regs 0 = base ∧
        y.regs 1 = u.val ∧
        y.regs 2 = (TrinomialField.equivFin t
          (acc * x_field ^ m + ∑ i : Fin m, c_field (Fin.castLE hm i) * x_field ^ (i : ℕ))).val ∧
        y.mem = s.mem := by
  intro t q L c_field x_field m
  induction m with
  | zero =>
    intro _ acc s _ h0 h1 h2 h3 _ _ _ _ _ h9
    exact ⟨s, Exec.loop_exit (by simp [Cond.Holds, h9, h3]), h0, h1, by simp [h2], rfl⟩
  | succ m ih =>
    intro hm acc s ⟨htab, hseed⟩ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    have hpow_q_Lb := Nat.pow_le_pow_right two_pos (le_limbCountFromB_mul hb q)
    have hu_bound : u.val < 2 ^ q := u.isLt.trans_le (le_two_pow_trinomialDeg U M)
    set acc_val := (TrinomialField.equivFin t acc).val
    have hacc_bound : acc_val < 2 ^ q := (TrinomialField.equivFin t acc).isLt
    obtain ⟨hxor_val, hsum⟩ := horner_step_arith hm c hu_bound acc
    set acc_next := acc * x_field + c_field ⟨m, by omega⟩
    have hfit_acc_next := Fits.mono (TrinomialField.equivFin t acc_next).isLt
      (show 2 * 3 ^ t ≤ w by change 2 * (2 * 3 ^ t) ≤ w at hw; omega)
    refine WP.Exact.exists_exec (WP.Exact.loop_iter (by simp [Cond.Holds, h9, h3]) ?_)
    wram_exec (disch := first | fits | layout_omega) [hornerBody, h2, h3, h6, h8, h9]
    wram_call (outerClmulLoop_exec (tabBase := base + 8 + k) hb hw (by wram_omega)
      (hu_bound.trans_le hpow_q_Lb) hu_bound L acc_val 0 0 _ (hacc_bound.trans_le hpow_q_Lb)
      (by simpa using hacc_bound) (by positivity) (fits_two_mul_limbCount hb hw hfit_space)
      (by regs_frame) (by wram_simp) (by regs_frame) (by regs_frame) (by regs_frame)
      (by regs_frame) (by regs_frame) (by regs_frame) (by wram_simp) (by wram_simp) (by wram_simp)
      fun i hi => (by rcases htab with ⟨-, -, -, -, -, -, -, -, h⟩; exact h i hi))
      with s6 ⟨hs6_2, hs6_low, hs6_mem⟩
    wram_exec
    wram_call (reduceStepCode_exec (by rw [hs6_mem]; exact htab) hw (by wram_omega)
      (clmul_lt_two_pow_two_mul hacc_bound hu_bound) (by regs_frame)
      (by simpa [Nat.shiftLeft_zero] using hs6_2) (by regs_frame))
      with s7 ⟨hs7_2, hs7_low, hs7_mem⟩
    wram_exec (disch := first | fits | layout_omega)
      [hs7_low, hs6_low, hs7_mem, hs6_mem, h0, hseed ⟨m, by omega⟩, hs7_2, acc_val, t, hxor_val]
    wram_call (ih (Nat.le_of_succ_le hm) acc_next _
      (by wram_simp [hs7_mem, hs6_mem]; exact ⟨htab, hseed⟩)
      (by regs_frame) (by regs_frame) (by wram_simp [t]) (by regs_frame) (by regs_frame)
      (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame))
      with y ⟨hy0, hy1, hy2, hy_mem⟩
    exact ⟨by ring, hy0, hy1, by rw [hy2, hsum], by rw [hy_mem]; wram_simp [hs7_mem, hs6_mem]⟩

/-- 13-instruction setup block for `evalCode k`: initializes `reg 8 = 1`, `reg 9 = 0`,
`reg 2 = 0`, `reg 3 = k`, loads `b`, `2 ^ b - 1`, `L` from `base + 5 .. base + 7` into `reg 4..6`,
and sets `reg 7 = base + 8 + k`. -/
@[expose] def evalSetupCode (k : ℕ) : Code .exact 18 :=
  .seq (.op (.const 8 1))
  (.seq (.op (.const 9 0))
  (.seq (.op (.copy 2 9))
  (.seq (.op (.const 3 k))
  (.seq (.op (.const 15 5))
  (.seq (.op (.exactBin .add 15 0 15))
  (.seq (.op (.load 4 15))
  (.seq (.op (.exactBin .add 15 15 8))
  (.seq (.op (.load 5 15))
  (.seq (.op (.exactBin .add 15 15 8))
  (.seq (.op (.load 6 15))
  (.seq (.op (.const 7 (8 + k)))
        (.op (.exactBin .add 7 0 7)))))))))))))

/-- 4-instruction suffix for `evalCode k`: loads `2 ^ M - 1` from `base + 4` and masks `reg 2`. -/
@[expose] def evalMaskCode : Code .exact 18 :=
  .seq (.op (.const 15 4))
  (.seq (.op (.exactBin .add 15 0 15))
  (.seq (.op (.load 15 15))
        (.op (.exactBin .and 2 2 15))))

/-- Deterministic evaluation program `evalCode k`: given `reg 0 = base` and `reg 1 = u.val`,
evaluates `trinomialPolyHash (trinomialStep U M) k U M c u` into `reg 2` (`regOut`) in
`evalStepsFromB b U M k` instructions while preserving `reg 0 = base`, `reg 1 = u.val`, and
all memory. -/
@[expose] def evalCode (k : ℕ) : Code .exact 18 :=
  .seq (evalSetupCode k) (.seq hornerLoop evalMaskCode)

/-- Exact instruction count of `evalCode k` for chunk width `b`, universe `U`, output bits `M`,
and independence parameter `k`. -/
@[expose] def evalStepsFromB (b U M k : ℕ) : ℕ :=
  let L := limbCountFromB b (trinomialDeg U M)
  ((11 * L + 12) * L + 30) * k + 19

/-- Exact instruction count of `evalCode k` for capacity `n_max`, universe `U`, output bits `M`,
and independence parameter `k`. -/
@[expose] def evalSteps (n_max U M k : ℕ) : ℕ :=
  evalStepsFromB (chunkBits n_max) U M k

/-- `evalSetupCode k` executes deterministically in `13` steps. -/
theorem evalSetupCode_exec {w base b U M k : ℕ} {x : Data 18}
    (htab : TableRep base b U M k x.mem) (h0 : x.regs 0 = base)
    (hfit_end : Fits w (base + 8 + k)) :
    ∃ y : Data 18,
      Exec w (evalSetupCode k) x y 13 ∧
      y.regs 0 = base ∧
      y.regs 1 = x.regs 1 ∧
      y.regs 2 = 0 ∧
      y.regs 3 = k ∧
      y.regs 4 = b ∧
      y.regs 5 = 2 ^ b - 1 ∧
      y.regs 6 = limbCountFromB b (trinomialDeg U M) ∧
      y.regs 7 = base + 8 + k ∧
      y.regs 8 = 1 ∧
      y.regs 9 = 0 ∧
      y.mem = x.mem := by
  obtain ⟨-, -, -, -, -, hm5, hm6, hm7, -⟩ := htab
  wram_exec [evalSetupCode, h0, hm5, hm6, hm7]
  wram_simp [h0, Nat.add_assoc]

/-- **`KWise.evalCode k` correctness and complexity (general `b`)**: from
`Rep base b U M k c x.mem`, `x.regs 0 = base`, and `x.regs 1 = u.val` (`u : Fin U`), `evalCode k`
halts deterministically in `evalStepsFromB b U M k = O(k * L ^ 2 + 1)` instructions, writing
`(trinomialPolyHash (trinomialStep U M) k U M c u).val` into `reg 2` (`regOut`) and preserving
`reg 0 = base`, `reg 1 = u.val`, and all memory (`y.mem = x.mem`). -/
theorem evalCode_execWithin_fromB {w base b U M k : ℕ}
    {c : Fin k → Fin (2 ^ trinomialDeg U M)} (u : Fin U) {x : Data 18}
    (hb : 0 < b) (hrep : Rep base b U M k c x.mem)
    (h0 : x.regs 0 = base) (h1 : x.regs 1 = u.val)
    (hw : 2 * trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + spaceFromB b k)) :
    ∃ y : Data 18,
      ExecWithin w (evalCode k) x y (evalStepsFromB b U M k) ∧
      y.regs 0 = base ∧
      y.regs 1 = u.val ∧
      y.regs 2 = (trinomialPolyHash (trinomialStep U M) k U M c u).val ∧
      y.mem = x.mem := by
  set t := trinomialStep U M
  have hzero_val : (TrinomialField.equivFin t 0).val = 0 := by
    rw [show (0 : TrinomialField t) = AdjoinRoot.mk (trinomial t) (polyOfCode 0) by simp]
    exact TrinomialField.val_equivFin_mk_polyOfCode t (by positivity)
  have hfit_out : Fits w ((trinomialPolyEval t k U c u).val &&& (2 ^ M - 1)) :=
    Fits.mono (Nat.and_le_left.trans_lt (trinomialPolyEval t k U c u).isLt)
      (by change 2 * (2 * 3 ^ t) ≤ w at hw; omega)
  obtain ⟨-, -, -, -, hm4, -⟩ := hrep.1
  refine WP.exists_execWithin (WP.Exact.toWP ?_)
  wram_exec [evalCode]
  wram_call (evalSetupCode_exec hrep.1 h0 (by wram_omega))
    with d1 ⟨hd1_0, hd1_1, hd1_2, hd1_3, hd1_4, hd1_5, hd1_6, hd1_7, hd1_8, hd1_9, hd1_mem⟩
  wram_exec
  wram_call (hornerLoop_exec u hb hw hfit_space k le_rfl 0 d1 (hd1_mem ▸ hrep) hd1_0
    (hd1_1.trans h1) (hd1_2.trans hzero_val.symm) hd1_3 hd1_4 hd1_5 hd1_6 hd1_7 hd1_8 hd1_9)
    with d2 ⟨hd2_0, hd2_1, hd2_2, hd2_mem⟩
  have hd2_eval : d2.regs 2 = (trinomialPolyEval t k U c u).val := by
    simpa [trinomialPolyEval, polynomialHash] using hd2_2
  wram_exec (disch := first | fits | layout_omega) [evalMaskCode,
    hd2_0, hd2_mem, hd1_mem, hm4, hd2_eval]
  exact ⟨by dsimp only [evalStepsFromB]; omega, by wram_simp [hd2_0], by wram_simp [hd2_1],
    by wram_simp [t]; exact (val_trinomialPolyHash t k U M c u).symm,
    by wram_simp [hd2_mem, hd1_mem]⟩

/-- **`KWise.evalCode k` correctness and complexity**: from
`Rep base (chunkBits n_max) U M k c x.mem`, `x.regs 0 = base`, and `x.regs 1 = u.val`
(`u : Fin U`), `evalCode k` halts deterministically in `evalSteps n_max U M k = O(k * L ^ 2 + 1)`
instructions, writing `(trinomialPolyHash (trinomialStep U M) k U M c u).val` into `reg 2`
(`regOut`) and preserving `reg 0 = base`, `reg 1 = u.val`, and all memory (`y.mem = x.mem`). -/
theorem evalCode_execWithin {w base n_max U M k : ℕ}
    {c : Fin k → Fin (2 ^ trinomialDeg U M)} (u : Fin U) {x : Data 18}
    (hrep : Rep base (chunkBits n_max) U M k c x.mem)
    (h0 : x.regs 0 = base) (h1 : x.regs 1 = u.val)
    (hw : 2 * trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + space n_max k)) :
    ∃ y : Data 18,
      ExecWithin w (evalCode k) x y (evalSteps n_max U M k) ∧
      y.regs 0 = base ∧
      y.regs 1 = u.val ∧
      y.regs 2 = (trinomialPolyHash (trinomialStep U M) k U M c u).val ∧
      y.mem = x.mem :=
  evalCode_execWithin_fromB u (chunkBits_pos n_max) hrep h0 h1 hw hfit_space

/-- Output of deterministic `evalCode k` execution at word size `w` from state `y` with
`reg 0 ← base` and `reg 1 ← u.val`, reduced modulo `2 ^ M` into `Fin (2 ^ M)`. -/
noncomputable def evalHashOut (w base k U M : ℕ) (y : Data 18) (u : Fin U) : Fin (2 ^ M) :=
  open Classical in
  let x_u := (y.set 0 base).set 1 u.val
  if h : ∃ z n, Exec w (evalCode k) x_u z n then
    ⟨(Classical.choose h).regs 2 % 2 ^ M, Nat.mod_lt _ (Nat.two_pow_pos M)⟩
  else
    ⟨0, Nat.two_pow_pos M⟩

/-- On any machine state `y` satisfying `Rep base (chunkBits n_max) U M k c y.mem`, the
deterministic `evalCode k` output `evalHashOut w base k U M y u` equals
`trinomialPolyHash (trinomialStep U M) k U M c u`. -/
theorem evalHashOut_eq_trinomialPolyHash {w base n_max U M k : ℕ}
    {c : Fin k → Fin (2 ^ trinomialDeg U M)} {y : Data 18}
    (hrep : Rep base (chunkBits n_max) U M k c y.mem)
    (hw : 2 * trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + space n_max k))
    (u : Fin U) :
    evalHashOut w base k U M y u = trinomialPolyHash (trinomialStep U M) k U M c u := by
  obtain ⟨z, ⟨n, _, hexec⟩, -, -, hz2, -⟩ :=
    evalCode_execWithin u (x := (y.set 0 base).set 1 u.val) hrep (by wram_simp) (by wram_simp)
      hw hfit_space
  have hex : ∃ z n, Exec w (evalCode k) ((y.set 0 base).set 1 u.val) z n := ⟨z, n, hexec⟩
  obtain ⟨_, hspec⟩ := Classical.choose_spec hex
  have huniq : Classical.choose hex = z := (hspec.unique hexec).1
  exact Fin.ext (by simp only [evalHashOut, hex, ↓reduceDIte, huniq, hz2,
    Nat.mod_eq_of_lt (trinomialPolyHash _ k U M c u).isLt])

/-- Under `resampleComp base U M k x`, the Word-RAM hash function `evalHashOut w base k U M z.1`
has the exact distribution of `trinomialPolyHash (trinomialStep U M) k U M c` for a uniform seed
`c : Fin k → Fin (2 ^ trinomialDeg U M)`. -/
theorem map_evalHashOut_eval_resampleComp {w base n_max U M k : ℕ} {x : Data 18}
    (htab : TableRep base (chunkBits n_max) U M k x.mem)
    (h0 : x.regs 0 = base)
    (hw : 2 * trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + space n_max k)) :
    ((resampleComp base U M k x).eval).map (fun z => evalHashOut w base k U M z.1) =
      (PMF.uniformOfFintype (Fin k → Fin (2 ^ trinomialDeg U M))).map
        (trinomialPolyHash (trinomialStep U M) k U M) := by
  rw [← map_extractSeeds_eval_resampleComp base U M k x]
  dsimp only [trinomialDeg, extractSeeds, extractSlice]
  rw [PMF.map_comp]
  exact Cslib.Probability.PMF.map_congr_on_support _ _ _ fun z hz => funext <|
    evalHashOut_eq_trinomialPolyHash
      (mem_support_resampleComp htab h0 ((ProbComp.support_eval _).symm ▸ hz)).1.1 hw hfit_space

/-- For any `k`-wise independent hash family `h : ι → X → Y` and any set `T : Finset X` of at most
`k` points, restricting `h i` to `T` under a uniform seed `i ← PMF.uniformOfFintype ι` yields the
uniform distribution `PMF.uniformOfFintype (T → Y)`. -/
theorem uniformOfFintype_map_restrict_of_isKWiseIndependentHash
    {ι X Y : Type*} [Fintype ι] [Nonempty ι] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    {k : ℕ} {h : ι → X → Y} (hh : IsKWiseIndependentHash k h)
    {T : Finset X} (hT : Finset.card T ≤ k) :
    (PMF.uniformOfFintype ι).map (fun i => T.restrict (h i)) =
      PMF.uniformOfFintype (T → Y) := by
  ext y
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [Cslib.Probability.PMF.toReal_uniformOfFintype_map_apply, hh.dens_filter_restrict_eq hT y]
  simp

/-- **Composed Word-RAM `k`-wise independence of `resampleCode` and `evalCode`
(`isKWiseIndependentHash_eval`)**:
from any machine state `x` satisfying `TableRep base (chunkBits n_max) U M k x.mem` and
`x.regs 0 = base`, under the resampling distribution `(resampleComp base U M k x).eval` of
`resampleCode k`, for every set `T : Finset (Fin U)` of at most `k` keys (`T.card ≤ k`), the
restricted tuple of deterministic `evalCode k` outputs `T.restrict (evalHashOut w base k U M z.1)`
is uniformly distributed on `T → Fin (2 ^ M)` (`PMF.uniformOfFintype (T → Fin (2 ^ M))`). -/
theorem isKWiseIndependentHash_eval {w base n_max U M k : ℕ} {x : Data 18}
    (htab : TableRep base (chunkBits n_max) U M k x.mem)
    (h0 : x.regs 0 = base)
    (hw : 2 * trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + space n_max k))
    {T : Finset (Fin U)} (hT : Finset.card T ≤ k) :
    ((resampleComp base U M k x).eval).map (fun z => T.restrict (evalHashOut w base k U M z.1)) =
      PMF.uniformOfFintype (T → Fin (2 ^ M)) := by
  have hmap := congrArg (PMF.map T.restrict)
    (map_evalHashOut_eval_resampleComp htab h0 hw hfit_space)
  dsimp only [trinomialDeg] at hmap
  rw [PMF.map_comp, PMF.map_comp] at hmap
  exact hmap.trans (uniformOfFintype_map_restrict_of_isKWiseIndependentHash
    (isKWiseIndependentHash_trinomialPolyHash (le_two_pow_trinomialDeg U M) (le_trinomialDeg U M))
    hT)

end Cslib.DataStructure.HashFamily.WordRAM.KWise
