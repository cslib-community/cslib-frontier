/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.Approximation.GapLin
public import CslibFrontier.Computability.PCP.Approximation.Hastad.Reduction
public import CslibFrontier.Computability.PCP.Approximation.LabelCover.SmallSoundness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import CslibFrontier.Logics.Propositional.CNF.PolyTime
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Håstad's optimal inapproximability for MAX-E3LIN-2 and MAX-E3SAT (imperfect completeness)

This module connects small-soundness Label Cover (`Cslib.Complexity.GapLabelCover_npHard_pow`),
Håstad's noisy 3-bit linear test dichotomy (`Cslib.PCP.Hastad.gapLabelCover_dichotomy_lt_one`),
the folded Long Code reduction (`Cslib.PCP.Hastad.Reduction.reduce`), and the four-clause XOR
gadget (`Cslib.Logic.PL.CSP.toCNFBounded`) to establish:

1. **MAX-E3LIN-2 (`GapExactThreeLin`, `[Hastad2001]` Theorem 5.4, author PDF pp. 27–28 / JACM
   pp. 821–822)**: for every `0 < δ`, `0 < ε` with `1 / 2 + ε < 1 - δ`, distinguishing systems of
   parity equations on three distinct variables (`e.scope.length = 3 ∧ e.scope.Nodup`, matching
   `[Hastad2001]` Definition 2.5, author PDF p. 7) of value at least `1 - δ` from those of value
   at most `1 / 2 + ε` is NP-hard (`GapExactThreeLin_npHard`). Consequently, any polynomial-time
   `ρ`-approximation algorithm for MAX-E3LIN-2 with `1 / 2 < ρ` (approximation factor `2 - ε`)
   implies `P = NP` (`P_eq_NP_of_maxExactThreeLin_approx`).
2. **`GapLin (1 - δ) (1 / 2 + ε)` (`[Goldreich2007DraftR5]` Theorem 10.9, r5 PDF p. 80 / printed
   p. 462, in the corrected separated range)**: transferring `GapExactThreeLin` to
   `Cslib.Complexity.XORSAT.System` via `toGapLin` proves NP-hardness of
   `GapLin (1 - δ) (1 / 2 + ε)` for every `0 < δ`, `0 < ε` with `1 / 2 + ε < 1 - δ`
   (`GapLin_npHard_of_lt`), upgrading the fixed-constant Exercise 10.5 result
   `Cslib.Complexity.exists_GapLin_npHard`.
3. **MAX-E3SAT with imperfect completeness (`GapMaxExactThreeSAT`, `[Hastad2001]` Theorem 6.1,
   author PDF p. 38 / JACM p. 831)**: composing with `CSP.toCNFBounded 3 CSP.paritySem` transfers
   `CSP.unsatVal` by an exact factor of four (`CSP.unsatVal_toCNFBounded_parity`) and preserves
   distinctness (`CNF.IsExactThreeDistinct`), proving NP-hardness of
   `GapMaxExactThreeSAT (1 - δ) (7 / 8 + ε)` for every `0 < δ`, `0 < ε` with
   `7 / 8 + ε < 1 - δ` (`GapMaxExactThreeSAT_npHard`). Consequently, any polynomial-time
   `ρ`-approximation algorithm for MAX-E3SAT on `CNF.IsExactThreeDistinct` formulas with
   `7 / 8 < ρ` (approximation factor `8 / 7 - ε`) implies `P = NP`
   (`P_eq_NP_of_maxExactThreeSAT_approx`), matching Johnson's polynomial-time `7 / 8`-approximation
   `Cslib.Complexity.exists_polyTime_maxExactThreeSAT_approx`.

**Scope and distinction from `[Hastad2001]` Theorem 6.5.** `GapMaxExactThreeSAT (1 - δ) (7 / 8 + ε)`
has *imperfect completeness* `1 - δ < 1` and requires three distinct variables per clause
(`CNF.IsExactThreeDistinct`); it sits alongside `Cslib.Complexity.GapExactThreeSAT s` (which fixes
completeness `1` and permits repeated literals in a clause). Håstad's stronger hardness for
*satisfiable* E3-CNF formulas (`[Hastad2001]` Theorem 6.5, author PDF p. 42) uses a different PCP
test and is not formalized here (see issue #886).

## Main definitions

* `Cslib.Complexity.GapExactThreeLin`: MAX-E3LIN-2 gap problem on three distinct variables per
  equation (`CSP Bool ℕ` under `CSP.paritySem`).
* `Cslib.Complexity.GapMaxExactThreeSAT`: imperfect-completeness MAX-E3SAT gap problem on three
  distinct variables per clause (`CNF ℕ` under `CNF.IsExactThreeDistinct`).
* `Cslib.Complexity.toGapLin`: polynomial-time conversion from `CSP Bool ℕ` parity systems to
  `XORSAT.System`, mapping the empty system to a single satisfiable three-variable equation.

## Main results

* `Cslib.Logic.PL.CSP.unsatVal_toCNFBounded_parity`: exact quarter-factor value transfer under the
  four-clause XOR gadget.
* `Cslib.Complexity.polyTimeReducible_GapExactThreeLin_GapLin`: reduction from `GapExactThreeLin`
  to `GapLin`.
* `Cslib.Complexity.polyTimeReducible_GapExactThreeLin_GapMaxExactThreeSAT`: reduction from
  `GapExactThreeLin c s` to `GapMaxExactThreeSAT ((3 + c) / 4) ((3 + s) / 4)`.
* `Cslib.Complexity.GapExactThreeLin_npHard`: NP-hardness of `GapExactThreeLin (1 - δ) (1 / 2 + ε)`.
* `Cslib.Complexity.GapLin_npHard_of_lt`: NP-hardness of `GapLin (1 - δ) (1 / 2 + ε)`.
* `Cslib.Complexity.GapMaxExactThreeSAT_npHard`: NP-hardness of
  `GapMaxExactThreeSAT (1 - δ) (7 / 8 + ε)`.
* `Cslib.Complexity.P_eq_NP_of_maxExactThreeLin_approx`: `[Hastad2001]` Theorem 5.4,
  inapproximability of MAX-E3LIN-2 beyond `1 / 2` (factor `2 - ε`).
* `Cslib.Complexity.P_eq_NP_of_maxExactThreeSAT_approx`: `[Hastad2001]` Theorem 6.1,
  inapproximability of MAX-E3SAT beyond `7 / 8` (factor `8 / 7 - ε`).

## References

* [J. Håstad, *Some optimal inapproximability results*][Hastad2001], Definition 2.5 (author PDF
  p. 7), Theorem 5.4 (author PDF pp. 27–28 / JACM pp. 821–822), and Theorem 6.1 (author PDF p. 38
  / JACM p. 831).
* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, draft of April 2007,
  Theorem 10.9 (r5.pdf PDF p. 80 / printed p. 462)][Goldreich2007DraftR5].
-/

public section

namespace Cslib.Logic.PL.CSP

/-- Under the four-clause parity gadget, the unsatisfiability value falls by an exact factor of
four on every system of three-variable parity equations (including the empty system). -/
theorem unsatVal_toCNFBounded_parity {V : Type*} {F : CSP Bool V}
    (hF : ∀ c ∈ F, c.scope.length = 3) :
    (F.toCNFBounded 3 paritySem).unsatVal = F.unsatVal paritySem / 4 := by
  refine le_antisymm ?_ ((CNF.le_unsatVal_iff _).2 fun σ => by
    rw [proportion_countUnsat_toCNFBounded_parity hF σ]
    exact div_le_div_of_nonneg_right (CSP.unsatVal_le paritySem F σ) (by norm_num))
  obtain ⟨σ, hσ⟩ := CSP.exists_countUnsat_div_eq_unsatVal paritySem F
  simpa only [proportion_countUnsat_toCNFBounded_parity hF σ, hσ] using
    (F.toCNFBounded 3 paritySem).unsatVal_le σ

end Cslib.Logic.PL.CSP

namespace Cslib.Complexity

open Cslib.Logic.PL Cslib.PCP Cslib.PCP.Encoded Cslib.PCP.Hastad Cslib.PCP.Hastad.Reduction
  Turing.MultiTapeTM ComputableInPolyTime

/-! ### Gap problems for MAX-E3LIN-2 and imperfect-completeness MAX-E3SAT -/

/-- The gap problem of **MAX-E3LIN-2** (`[Hastad2001]`, Definition 2.5): parity equations over
three distinct variables (`CSP Bool ℕ` under `CSP.paritySem`), separating systems of value
`1 - unsatVal ≥ c` from those of value `≤ s` (with `s < c`). -/
@[expose] noncomputable def GapExactThreeLin (c s : ℝ) : PromiseProblem (CSP Bool ℕ) :=
  (PromiseProblem.gapMax (fun F => 1 - F.unsatVal CSP.paritySem) (fun _ => c) (fun _ => s)).restrict
    {F | ∀ e ∈ F, e.scope.length = 3 ∧ e.scope.Nodup}

/-- Yes-instances of `GapExactThreeLin c s`: distinct 3-variable parity systems of value at least
`c`. -/
theorem mem_yes_GapExactThreeLin {c s : ℝ} {F : CSP Bool ℕ} :
    F ∈ (GapExactThreeLin c s).yes ↔
      (∀ e ∈ F, e.scope.length = 3 ∧ e.scope.Nodup) ∧ c ≤ 1 - F.unsatVal CSP.paritySem := by
  simp only [GapExactThreeLin, PromiseProblem.yes_restrict, Set.mem_inter_iff,
    PromiseProblem.mem_yes_gapMax, Set.mem_ofPred_eq, and_comm]

/-- No-instances of `GapExactThreeLin c s` for `s < c`: distinct 3-variable parity systems of value
at most `s`. -/
theorem mem_no_GapExactThreeLin {c s : ℝ} (hsc : s < c) {F : CSP Bool ℕ} :
    F ∈ (GapExactThreeLin c s).no ↔
      (∀ e ∈ F, e.scope.length = 3 ∧ e.scope.Nodup) ∧ 1 - F.unsatVal CSP.paritySem ≤ s := by
  simp only [GapExactThreeLin, PromiseProblem.no_restrict, Set.mem_inter_iff,
    PromiseProblem.mem_no_gapMax_of_lt (c := fun _ => c) (s := fun _ => s) hsc,
    Set.mem_ofPred_eq, and_comm]

/-- The gap problem of **MAX-E3SAT with completeness `c` and soundness `s`**, on formulas with
three distinct variables per clause (`CNF.IsExactThreeDistinct`). Unlike
`Cslib.Complexity.GapExactThreeSAT s` (which fixes completeness `1` and permits repeated literals),
this problem allows imperfect completeness `c < 1` and matches the distinct-variable model of
`Cslib.Complexity.exists_polyTime_maxExactThreeSAT_approx` and `[Hastad2001]` Theorem 6.1. -/
@[expose] noncomputable def GapMaxExactThreeSAT (c s : ℝ) : PromiseProblem (CNF ℕ) :=
  (PromiseProblem.gapMax (fun φ => 1 - φ.unsatVal) (fun _ => c) (fun _ => s)).restrict
    {φ | φ.IsExactThreeDistinct}

/-- Yes-instances of `GapMaxExactThreeSAT c s`. -/
theorem mem_yes_GapMaxExactThreeSAT {c s : ℝ} {φ : CNF ℕ} :
    φ ∈ (GapMaxExactThreeSAT c s).yes ↔ φ.IsExactThreeDistinct ∧ c ≤ 1 - φ.unsatVal := by
  simp only [GapMaxExactThreeSAT, PromiseProblem.yes_restrict, Set.mem_inter_iff,
    PromiseProblem.mem_yes_gapMax, Set.mem_ofPred_eq, and_comm]

/-- No-instances of `GapMaxExactThreeSAT c s` for `s < c`. -/
theorem mem_no_GapMaxExactThreeSAT {c s : ℝ} (hsc : s < c) {φ : CNF ℕ} :
    φ ∈ (GapMaxExactThreeSAT c s).no ↔ φ.IsExactThreeDistinct ∧ 1 - φ.unsatVal ≤ s := by
  simp only [GapMaxExactThreeSAT, PromiseProblem.no_restrict, Set.mem_inter_iff,
    PromiseProblem.mem_no_gapMax_of_lt (c := fun _ => c) (s := fun _ => s) hsc,
    Set.mem_ofPred_eq, and_comm]

/-! ### Bridge to `GapLin` (`XORSAT.System`) and four-clause reduction to `GapMaxExactThreeSAT` -/

/-- Convert a `CSP Bool ℕ` parity system to an `XORSAT.System`, replacing the empty system by the
single satisfiable equation `x₀ ⊕ x₁ ⊕ x₂ = 0` so that the empty yes-instance of `GapExactThreeLin`
maps to a nonempty yes-instance of `GapLin`. -/
@[expose] def toGapLin (F : CSP Bool ℕ) : XORSAT.System :=
  if F.isEmpty then [⟨[0, 1, 2], false⟩] else F.map fun c => ⟨c.scope, c.rel⟩

/-- `toGapLin` is computable in polynomial time under `encCSP encBool encNat` and
`XORSAT.encoding`. -/
@[fun_prop]
theorem computableInPolyTime_toGapLin :
    ComputableInPolyTime toGapLin (encCSP encBool encNat) XORSAT.encoding :=
  ComputableInPolyTime.ite (ComputableInPolyTime.listIsEmpty' (encConstraint encBool encNat))
    (.const ([⟨[0, 1, 2], false⟩] : XORSAT.System))
    (ComputableInPolyTime.map (by fun_prop : ComputableInPolyTime
      (fun c : Constraint Bool ℕ => (⟨c.scope, c.rel⟩ : AffineEquation ℕ)) _ _))

private theorem eval_paritySem_eq_holds (c : Constraint Bool ℕ) (σ : ℕ → Bool) :
    Constraint.eval CSP.paritySem σ c = decide (AffineEquation.Holds ⟨c.scope, c.rel⟩ σ) := by
  have hsum : (c.scope.map σ).foldl Bool.xor false = (c.scope.map σ).sum := by
    rw [List.sum_eq_foldl]; rfl
  by_cases h : (c.scope.map σ).sum = c.rel <;>
    simp [Constraint.eval, CSP.paritySem, AffineEquation.Holds, hsum, h]

private theorem countSat_map_affine (F : CSP Bool ℕ) (σ : ℕ → Bool) :
    AffineSystem.countSat (F.map fun c => (⟨c.scope, c.rel⟩ : AffineEquation ℕ)) σ =
      F.countP (Constraint.eval CSP.paritySem σ) := by
  rw [AffineSystem.countSat, List.countP_map]
  exact List.countP_congr fun c _ => by simp only [Function.comp_apply, eval_paritySem_eq_holds]

private theorem countSat_div_add_countUnsat_div {F : CSP Bool ℕ} (hF : 0 < F.length)
    (σ : ℕ → Bool) :
    (F.countP (Constraint.eval CSP.paritySem σ) : ℝ) / F.length +
      (F.countP (fun c => !Constraint.eval CSP.paritySem σ c) : ℝ) / F.length = 1 := by
  have hsplit : F.countP (Constraint.eval CSP.paritySem σ) +
      F.countP (fun c => !Constraint.eval CSP.paritySem σ c) = F.length :=
    (List.length_eq_countP_add_countP (Constraint.eval CSP.paritySem σ) (l := F)).symm
  rw [← add_div, ← Nat.cast_add, hsplit, div_self (Nat.cast_ne_zero.2 hF.ne')]

/-- **`GapExactThreeLin` reduces to `GapLin`**: for `c ≤ 1` and `s < s' ≤ c`, `toGapLin` maps
`GapExactThreeLin c s` to `GapLin c s'` in polynomial time. The strict slack `s < s'` bridges
`GapExactThreeLin`'s `≤ s` no-condition to `GapLin`'s `< s'` no-condition. -/
theorem polyTimeReducible_GapExactThreeLin_GapLin {c s s' : ℝ} (hc1 : c ≤ 1) (hs : s < s')
    (hs'c : s' ≤ c) :
    PromiseProblem.PolyTimeReducible (encCSP encBool encNat) XORSAT.encoding
      (GapExactThreeLin c s) (GapLin c s') := by
  refine ⟨toGapLin, computableInPolyTime_toGapLin, fun F hF => ?_, fun F hF => ?_⟩
  · rw [mem_yes_GapExactThreeLin] at hF
    rw [mem_yes_GapLin]
    rcases eq_or_ne F [] with rfl | he
    · refine ⟨fun _ => false, ?_⟩
      change c ≤ ((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)
      simpa using hc1
    · obtain ⟨σ, hσ⟩ := CSP.exists_countUnsat_div_eq_unsatVal CSP.paritySem F
      refine ⟨σ, ?_⟩
      simp only [toGapLin, List.isEmpty_eq_false_iff.mpr he, Bool.false_eq_true, ↓reduceIte,
        countSat_map_affine, List.length_map]
      linarith [countSat_div_add_countUnsat_div (List.length_pos_of_ne_nil he) σ]
  · rw [mem_no_GapExactThreeLin (hs.trans_le hs'c)] at hF
    rw [mem_no_GapLin]
    have he : F ≠ [] := by
      rintro rfl
      simp only [CSP.unsatVal_nil, sub_zero] at hF
      linarith
    refine ⟨hs'c, fun σ => ?_⟩
    simp only [toGapLin, List.isEmpty_eq_false_iff.mpr he, Bool.false_eq_true, ↓reduceIte,
      countSat_map_affine, List.length_map]
    linarith [CSP.unsatVal_le CSP.paritySem F σ,
      countSat_div_add_countUnsat_div (List.length_pos_of_ne_nil he) σ]

/-- **The four-clause reduction from MAX-E3LIN-2 to MAX-E3SAT** (`[Hastad2001]`, proof of
Theorem 6.1, author PDF p. 38 / JACM p. 831): `CSP.toCNFBounded 3 CSP.paritySem` maps
`GapExactThreeLin c s` to `GapMaxExactThreeSAT ((3 + c) / 4) ((3 + s) / 4)` in polynomial time,
preserving distinctness of the three variables in every clause. -/
theorem polyTimeReducible_GapExactThreeLin_GapMaxExactThreeSAT {c s : ℝ} (hsc : s < c) :
    PromiseProblem.PolyTimeReducible (encCSP encBool encNat) encCNF
      (GapExactThreeLin c s) (GapMaxExactThreeSAT ((3 + c) / 4) ((3 + s) / 4)) := by
  refine ⟨CSP.toCNFBounded 3 CSP.paritySem,
    CSP.computableInPolyTime_toCNFBounded_parity encNat, fun F hF => ?_, fun F hF => ?_⟩
  · rw [mem_yes_GapExactThreeLin] at hF
    rw [mem_yes_GapMaxExactThreeSAT, CSP.unsatVal_toCNFBounded_parity fun e he => (hF.1 e he).1]
    exact ⟨CSP.isExactThreeDistinct_toCNFBounded_parity hF.1, by linarith⟩
  · rw [mem_no_GapExactThreeLin hsc] at hF
    rw [mem_no_GapMaxExactThreeSAT (by linarith),
      CSP.unsatVal_toCNFBounded_parity fun e he => (hF.1 e he).1]
    exact ⟨CSP.isExactThreeDistinct_toCNFBounded_parity hF.1, by linarith⟩

/-! ### NP-hardness of MAX-E3LIN-2, `GapLin`, and imperfect-completeness MAX-E3SAT -/

/-- **Håstad's Theorem 5.4 (gap form, distinct variables)** `[Hastad2001]` (author PDF pp. 27–28 /
JACM pp. 821–822): for every `0 < δ`, `0 < ε` with `1 / 2 + ε < 1 - δ`, distinguishing systems of
three-variable parity equations over distinct variables of value at least `1 - δ` from those of
value at most `1 / 2 + ε` is NP-hard. -/
theorem GapExactThreeLin_npHard {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (h : 1 / 2 + ε < 1 - δ) :
    PromiseProblem.NPHard (encCSP encBool encNat) (GapExactThreeLin (1 - δ) (1 / 2 + ε)) := by
  -- Step 1: choose rational noise rate `1 / m ≤ δ / 2` with `3 ≤ m` (so `1 / m < 1 / 2`).
  let m : ℕ := Nat.ceil (2 / δ) + 3
  have hm2 : 2 ≤ m := by omega
  have hm0 : (0 : ℝ) < m := by positivity
  have hinv_le : 1 / (m : ℝ) ≤ δ / 2 := by
    have hm_ge : 2 / δ ≤ (m : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_add_right _ 3)
    rw [div_le_iff₀ hm0, div_mul_eq_mul_div, le_div_iff₀ two_pos]
    rw [div_le_iff₀ hδ] at hm_ge; linarith
  have hinv_lt_half : 1 / (m : ℝ) < 1 / 2 :=
    one_div_lt_one_div_of_lt two_pos (by exact_mod_cast (by omega : 2 < m))
  -- Step 2: obtain the Label Cover soundness threshold `η ∈ (0, 1)` for `ε' = ε / 8`.
  obtain ⟨η, hη0, hη1, hdich⟩ :=
    gapLabelCover_dichotomy_lt_one (ε := ε / 8) (δ := 1 / (m : ℝ))
      (by linarith) (by positivity) hinv_lt_half
  -- Step 3: choose `k = 21 * n` large enough for both Label Cover soundness `≤ η` and
  -- degenerate-equation share `(1 - 1 / m) ^ |β| < min (δ / 2) (ε / 4)`.
  let wMax : ℝ := min (δ / 2) (ε / 4)
  let baseLC : ℝ := 1 - 1 / (6000 * 2 ^ 186)
  let baseDrop : ℝ := 1 - 1 / (m : ℝ)
  have hbaseDrop1 : baseDrop < 1 := by
    dsimp only [baseDrop]; linarith [show (0 : ℝ) < 1 / m by positivity]
  obtain ⟨n₁, hn₁⟩ := exists_pow_lt_of_lt_one hη0 (by norm_num : baseLC < 1)
  obtain ⟨n₂, hn₂⟩ := exists_pow_lt_of_lt_one (lt_min (by linarith) (by linarith) :
    0 < wMax) hbaseDrop1
  let n : ℕ := max n₁ n₂ + 1
  let k : ℕ := 21 * n
  -- Instantiate the `k`-round Label Cover hardness at soundness `η`.
  let A := Bool × (Fin 6 → Bool)
  let β := Fin k → A × A
  let γ := Fin k → A
  have hLC_npHard : PromiseProblem.NPHard
      (Graph.encoding (encPi (encPi (encPair encBool (encPi encBool)))))
      (GapLabelCover β γ 1 η) := by
    refine (GapLabelCover_npHard_pow (by positivity : 0 < k)).mono (fun _ hg => hg) fun g hg => ?_
    have hpow : baseLC ^ ((k : ℝ) / 21) = baseLC ^ n := by
      rw [← Real.rpow_natCast]
      congr 1
      dsimp only [k]
      push_cast
      ring
    rw [GapLabelCover, PromiseProblem.mem_no_gapMax] at hg ⊢
    change 1 - (g.toGraph projectionEval).unsatVal ≤ baseLC ^ ((k : ℝ) / 21) ∧ _ at hg
    rw [hpow] at hg
    exact ⟨hg.1.trans <| (pow_le_pow_of_le_one (by norm_num) (by norm_num)
      ((le_max_left n₁ n₂).trans (Nat.le_succ _))).trans hn₁.le, hη1⟩
  -- Bound the degenerate-equation share `w = (1 - 1 / m) ^ |β| < wMax`.
  have hcard_ge : n₂ ≤ Fintype.card β := by
    have hcard_β : Fintype.card β = (128 * 128) ^ k := by simp [β, A, Fintype.card_prod]
    have := Nat.lt_two_pow_self (n := k)
    have := Nat.pow_le_pow_left (by norm_num : 2 ≤ 128 * 128) k
    have : n₂ ≤ n := (le_max_right n₁ n₂).trans (Nat.le_succ _)
    dsimp only [k] at *; omega
  set w : ℝ := (1 - 1 / (m : ℝ)) ^ Fintype.card β with hw_def
  have hw_lt : w < wMax :=
    (pow_le_pow_of_le_one (by dsimp only [baseDrop]; linarith) hbaseDrop1.le hcard_ge).trans_lt hn₂
  have hw_lt_δ : w < δ / 2 := hw_lt.trans_le (min_le_left _ _)
  have hw_lt_ε : w < ε / 4 := hw_lt.trans_le (min_le_right _ _)
  -- Step 4: reduce `GapLabelCover β γ 1 η` to `GapExactThreeLin (1 - δ) (1 / 2 + ε)`.
  let y₀ : γ := fun _ => (false, fun _ => false)
  let T : Tables β γ m := Tables.ofFintype m y₀
  have hT : T.Valid := Tables.valid_ofFintype m y₀
  refine hLC_npHard.trans ⟨reduce T, isPolyTime_reduce T (encPi (encPair encBool (encPi encBool))),
    fun g hg => ?_, fun g hg => ?_⟩
  · rw [mem_yes_GapExactThreeLin]
    refine ⟨scopes_reduce hT g, ?_⟩
    by_cases hedge : g.edges = []
    · rw [reduce_of_edges_nil T hedge, (CSP.unsatVal_eq_zero_iff CSP.paritySem [trivialEq]).2
        ⟨fun _ => false, by decide⟩]
      linarith
    · obtain ⟨B, A_tbl, hB, hprob⟩ := (hdich hedge).1 hg
      obtain ⟨σ, hσ⟩ := exists_countSat_reduce_ge hm2 hT hedge hB A_tbl
      rw [hprob] at hσ
      linarith [countSat_div_add_countUnsat_div (length_reduce_pos hm2 hT g) σ,
        CSP.unsatVal_le CSP.paritySem (reduce T g) σ]
  · rw [mem_no_GapExactThreeLin h]
    refine ⟨scopes_reduce hT g, ?_⟩
    have hedge : g.edges ≠ [] := by
      intro hnil
      rw [GapLabelCover, PromiseProblem.mem_no_gapMax] at hg
      have hsat : (g.toGraph projectionEval).Satisfiable :=
        ⟨fun _ => ((fun _ => ((false, fun _ => false), (false, fun _ => false))), y₀),
          fun i => absurd (i.isLt.trans_eq (congrArg List.length hnil)) (Nat.not_lt_zero _)⟩
      rw [(ConstraintGraph.unsatVal_eq_zero_iff _).2 hsat] at hg; linarith
    have hunsat : 1 - (1 / 2 + ε) ≤ (reduce T g).unsatVal CSP.paritySem := by
      refine (CSP.le_unsatVal_iff _ _).2 fun σ => ?_
      have hprob := (hdich hedge).2 hg (decodeRight T σ) (decodeLeft T σ) (isOdd_decodeRight T σ)
      have h1w : 0 < 1 - w := by linarith
      have hsat_le :
          ((reduce T g).countP (Constraint.eval CSP.paritySem σ) : ℝ) / (reduce T g).length ≤
            1 / 2 + ε :=
        (countSat_reduce_div_length_le hm2 hT hedge σ).trans <|
          (div_le_div_of_nonneg_right hprob h1w.le).trans ((div_le_iff₀ h1w).2 (by nlinarith))
      linarith [countSat_div_add_countUnsat_div (length_reduce_pos hm2 hT g) σ]
    linarith

/-- **Goldreich Theorem 10.9 (`gapLin_{1 - δ, 1 / 2 + ε}` is NP-hard)** `[Goldreich2007DraftR5]`
(r5.pdf PDF p. 80 / printed p. 462, in the corrected separated range `1 / 2 + ε < 1 - δ`;
`[Hastad2001]` Theorem 5.4): for every `0 < δ`, `0 < ε` with `1 / 2 + ε < 1 - δ`, the promise
problem `GapLin (1 - δ) (1 / 2 + ε)` on `XORSAT.System` is NP-hard. -/
theorem GapLin_npHard_of_lt {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (h : 1 / 2 + ε < 1 - δ) :
    PromiseProblem.NPHard XORSAT.encoding (GapLin (1 - δ) (1 / 2 + ε)) :=
  (GapExactThreeLin_npHard hδ (by linarith : 0 < ε / 2) (by linarith)).trans
    (polyTimeReducible_GapExactThreeLin_GapLin (c := 1 - δ) (s := 1 / 2 + ε / 2) (s' := 1 / 2 + ε)
      (by linarith) (by linarith) (by linarith))

/-- **Håstad's Theorem 6.1 (gap form, imperfect completeness, distinct variables)** `[Hastad2001]`
(author PDF p. 38 / JACM p. 831): for every `0 < δ`, `0 < ε` with `7 / 8 + ε < 1 - δ`,
distinguishing E3-CNF formulas with three distinct variables per clause of value at least `1 - δ`
from those of value at most `7 / 8 + ε` is NP-hard.

This theorem has imperfect completeness `1 - δ < 1`; it does not establish `[Hastad2001]`
Theorem 6.5 (perfect completeness `1` vs `7 / 8 + ε`). -/
theorem GapMaxExactThreeSAT_npHard {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (h : 7 / 8 + ε < 1 - δ) :
    PromiseProblem.NPHard encCNF (GapMaxExactThreeSAT (1 - δ) (7 / 8 + ε)) := by
  have hlin := GapExactThreeLin_npHard (δ := 4 * δ) (ε := 4 * ε)
    (by linarith) (by linarith) (by linarith)
  have hred := polyTimeReducible_GapExactThreeLin_GapMaxExactThreeSAT
    (c := 1 - 4 * δ) (s := 1 / 2 + 4 * ε) (by linarith)
  rw [show (3 + (1 - 4 * δ)) / 4 = 1 - δ by ring,
    show (3 + (1 / 2 + 4 * ε)) / 4 = 7 / 8 + ε by ring] at hred
  exact hlin.trans hred

/-! ### Approximation-factor consequences (`2 - ε` for MAX-E3LIN-2 and `8 / 7 - ε` for MAX-E3SAT) -/

/-- For any threshold `0 ≤ t < 1` and ratio `t < ρ`, there exist `δ, ε > 0` separating
`t + ε < 1 - δ` and `t + ε < ρ * (1 - δ)`. -/
private theorem exists_gap_params_of_gt {t ρ : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (hρ : t < ρ) :
    ∃ δ ε : ℝ, 0 < δ ∧ 0 < ε ∧ t + ε < 1 - δ ∧ t + ε < ρ * (1 - δ) := by
  let γ : ℝ := min ρ 1 - t
  have hγ0 : 0 < γ := by dsimp only [γ]; linarith [lt_min hρ ht1]
  have hγ_le : γ ≤ 1 - t := by dsimp only [γ]; linarith [min_le_right ρ 1]
  refine ⟨γ / 4, γ / 4, by linarith, by linarith, by linarith, ?_⟩
  exact (by nlinarith : t + γ / 4 < (t + γ) * (1 - γ / 4)).trans_le <|
    mul_le_mul_of_nonneg_right
      (by dsimp only [γ]; linarith [min_le_left ρ 1])
      (by linarith)

/-- Generic rational-threshold decider turning a polynomial-time `ρ`-approximation algorithm into a
`PromiseP` decider for a restricted `gapMax (1 - uval)` problem when `0 ≤ s < c ≤ 1` and
`s < ρ * c`. -/
private theorem gapMax_restrict_mem_PromiseP_of_approx {α : Type} {enc : α ↪ List Bool}
    {P : α → Prop} {len u : α → ℕ} {uval : α → ℝ} {ρ c s : ℝ}
    (hs0 : 0 ≤ s) (hsc : s < c) (hc1 : c ≤ 1) (hsρc : s < ρ * c)
    (hlen : ComputableInPolyTime len enc encNat)
    (hu : ComputableInPolyTime u enc encNat)
    (huval_le : ∀ x, P x → uval x ≤ (u x : ℝ) / len x)
    (hlen_pos : ∀ x, P x → 0 < uval x → 0 < len x)
    (happrox : ∀ x, P x → ρ * (1 - uval x) * len x ≤ (len x : ℝ) - u x) :
    (PromiseProblem.gapMax (fun x => 1 - uval x) (fun _ => c) (fun _ => s)).restrict {x | P x} ∈
      PromiseP enc := by
  obtain ⟨q, hsq, hqρc⟩ := exists_rat_btwn hsρc
  set a := q.num.toNat
  set b := q.den
  have hb : (0 : ℝ) < b := by exact_mod_cast q.den_pos
  have hab : (q : ℝ) = a / b := by
    have hnum : (0 : ℤ) ≤ q.num := Rat.num_nonneg.2 (by exact_mod_cast (hs0.trans_lt hsq).le)
    rw [← Rat.num_div_den q]
    push_cast
    rw [show ((q.num : ℤ) : ℝ) = (a : ℝ) by exact_mod_cast (Int.toNat_of_nonneg hnum).symm]
  have hiff (x : α) :
      a * len x + b * u x ≤ b * len x ↔ (q : ℝ) * len x ≤ (len x : ℝ) - u x := by
    rw [hab, div_mul_eq_mul_div, div_le_iff₀ hb, ← @Nat.cast_le ℝ]
    push_cast
    constructor <;> intro h <;> nlinarith
  refine mem_PromiseP_iff.2
    ⟨fun x => decide (a * len x + b * u x ≤ b * len x),
      binary_le' (binary_add' (binary_mul' (const a) hlen) (binary_mul' (const b) hu))
        (binary_mul' (const b) hlen),
      fun x hx => ?_, fun x hx => ?_⟩
  · simp only [PromiseProblem.yes_restrict, Set.mem_inter_iff, PromiseProblem.mem_yes_gapMax,
      Set.mem_ofPred_eq] at hx
    have hρ0 : 0 ≤ ρ := by nlinarith
    exact decide_eq_true ((hiff x).2 <|
      (mul_le_mul_of_nonneg_right (hqρc.le.trans (mul_le_mul_of_nonneg_left hx.1 hρ0))
        (Nat.cast_nonneg _)).trans (happrox x hx.2))
  · simp only [PromiseProblem.no_restrict, Set.mem_inter_iff,
      PromiseProblem.mem_no_gapMax_of_lt (c := fun _ => c) (s := fun _ => s) hsc,
      Set.mem_ofPred_eq] at hx
    refine decide_eq_false fun h => ?_
    have h := (hiff x).1 h
    have hle := huval_le x hx.2
    have hpos : (0 : ℝ) < len x := by exact_mod_cast hlen_pos x hx.2 (by linarith)
    rw [le_div_iff₀ hpos] at hle
    nlinarith

/-- **Håstad's Theorem 5.4: MAX-E3LIN-2 has no polynomial-time `(1 / 2 + ε)`-approximation
algorithm (factor `2 - ε`) unless `P = NP`** `[Hastad2001]` (author PDF p. 27 / JACM p. 821).
If a polynomial-time algorithm `A` outputs, on every system `F` of three-variable parity equations
over distinct variables, a list of variables set to `true` satisfying at least
`ρ · (1 - unsatVal F) · |F|` equations with `1 / 2 < ρ`, then `P = NP`. -/
theorem P_eq_NP_of_maxExactThreeLin_approx {A : CSP Bool ℕ → List ℕ} {ρ : ℝ}
    (hρ : 1 / 2 < ρ) (hA : ComputableInPolyTime A (encCSP encBool encNat) (encList encNat))
    (happrox : ∀ F : CSP Bool ℕ, (∀ e ∈ F, e.scope.length = 3 ∧ e.scope.Nodup) →
      ρ * (1 - F.unsatVal CSP.paritySem) * F.length ≤
        F.length - F.countP (fun e => !Constraint.eval CSP.paritySem
          (fun v => decide (v ∈ A F)) e))
    {β : Type} (enc : β ↪ List Bool) : P enc = NP enc := by
  obtain ⟨δ, ε, hδ, hε, hgap, hsρc⟩ :=
    exists_gap_params_of_gt (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hρ
  have hcnf : ComputableInPolyTime (CSP.toCNFBounded 3 CSP.paritySem)
      (encCSP encBool encNat) encCNF :=
    CSP.computableInPolyTime_toCNFBounded_parity encNat
  have hu : ComputableInPolyTime
      (fun F : CSP Bool ℕ => (F.toCNFBounded 3 CSP.paritySem).countUnsat fun v => decide (v ∈ A F))
      (encCSP encBool encNat) encNat :=
    unary_to_binary.comp ((computableInPolyTime_countUnsat_mem encNat).comp (hcnf.prod hA))
  have hmem : GapExactThreeLin (1 - δ) (1 / 2 + ε) ∈ PromiseP (encCSP encBool encNat) :=
    gapMax_restrict_mem_PromiseP_of_approx (by linarith) hgap (by linarith) hsρc
      (length_list_binary _) hu
      (fun F hF => by
        rw [CSP.countUnsat_toCNFBounded CSP.paritySem (fun e he => (hF e he).1.le)]
        exact CSP.unsatVal_le CSP.paritySem F _)
      (fun F _ hpos => Nat.pos_of_ne_zero fun h0 => by
        rw [List.length_eq_zero_iff.1 h0, CSP.unsatVal_nil] at hpos
        exact lt_irrefl _ hpos)
      (fun F hF => by
        rw [CSP.countUnsat_toCNFBounded CSP.paritySem (fun e he => (hF e he).1.le)]
        exact happrox F hF)
  exact (GapExactThreeLin_npHard hδ hε hgap).P_eq_NP_of_mem_PromiseP hmem enc

/-- **Håstad's Theorem 6.1: MAX-E3SAT has no polynomial-time `(7 / 8 + ε)`-approximation
algorithm (factor `8 / 7 - ε`) unless `P = NP`** `[Hastad2001]` (author PDF p. 38 / JACM p. 831).
If a polynomial-time algorithm `A` outputs, on every formula `φ` with three distinct variables per
clause (`CNF.IsExactThreeDistinct`), a list of variables set to `true` satisfying at least
`ρ · (1 - unsatVal φ) · |φ|` clauses with `7 / 8 < ρ`, then `P = NP`. This matches the
`7 / 8`-approximation of Johnson's algorithm
`Cslib.Complexity.exists_polyTime_maxExactThreeSAT_approx`. -/
theorem P_eq_NP_of_maxExactThreeSAT_approx {A : CNF ℕ → List ℕ} {ρ : ℝ}
    (hρ : 7 / 8 < ρ) (hA : ComputableInPolyTime A encCNF (encList encNat))
    (happrox : ∀ φ : CNF ℕ, φ.IsExactThreeDistinct →
      ρ * (1 - φ.unsatVal) * φ.length ≤
        φ.length - φ.countUnsat (fun v => decide (v ∈ A φ)))
    {β : Type} (enc : β ↪ List Bool) : P enc = NP enc := by
  obtain ⟨δ, ε, hδ, hε, hgap, hsρc⟩ :=
    exists_gap_params_of_gt (by norm_num : (0 : ℝ) ≤ 7 / 8) (by norm_num) hρ
  have hu : ComputableInPolyTime
      (fun φ : CNF ℕ => φ.countUnsat fun v => decide (v ∈ A φ)) encCNF encNat :=
    unary_to_binary.comp ((computableInPolyTime_countUnsat_mem encNat).comp (id'.prod hA))
  have hmem : GapMaxExactThreeSAT (1 - δ) (7 / 8 + ε) ∈ PromiseP encCNF :=
    gapMax_restrict_mem_PromiseP_of_approx (by linarith) hgap (by linarith) hsρc
      (length_list_binary _) hu
      (fun φ _ => CNF.unsatVal_le φ _)
      (fun _ _ hpos => CNF.length_pos_of_unsatVal_pos hpos)
      happrox
  exact (GapMaxExactThreeSAT_npHard hδ hε hgap).P_eq_NP_of_mem_PromiseP hmem enc

end Cslib.Complexity
