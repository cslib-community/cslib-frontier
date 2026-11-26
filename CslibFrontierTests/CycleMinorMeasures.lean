/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module

public import CslibFrontier.Computability.Circuit.Boolean.CycleMinorMeasures
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod

/-! Concrete `module` clients for the two measures of the cycle-and-minor function: the transfer
theorems at `d = 6` with cuts of between `2` and `4` of the `6` coordinates (`⌈d / 3⌉` and
`⌊2 d / 3⌋`), lower bounds on the measures turned into size lower bounds, values of the minor tables
at `d = 4`, and a read-once parity program computing the function at `d = 1`. -/

public section

namespace CslibFrontierTests.CycleMinorMeasures

open Cslib.Circuits Cslib.Circuits.CycleMinor Cslib.BranchingPrograms

/-! ### The transfer theorems -/

/-- The main theorem: a syntactically multilinear circuit with `s` gates over `F₂` computing the
multilinear representative of the function bounds the cut cover number over any `F₂`-algebra of
characteristic two by `2 s + 1`, and the component size of `HC_6` by `s + 1`. -/
example {K : Type*} [CommRing K] [Algebra (ZMod 2) K] [CharP K 2]
    (A : Circuit (arithSignature (ZMod 2)) (CycleMinor.inputs 6) 1)
    (hA : A.IsSyntacticallyMultilinear) (hf : A.ComputesMultilinear (cycleMinorFn 6)) :
    cutCover K 6 2 4 ≤ (2 * A.size + 1 : ℕ) ∧ hcComponentSize (ZMod 2) 6 ≤ (A.size + 1 : ℕ) :=
  measures_le_of_syntacticallyMultilinear A hA hf (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- A d-D with `s` gates computing the function bounds the cut cover number by `8 s + 1` and the
component size of `HC_6` by `4 s + 1`. -/
example (c : Circuit Boolean.signature (CycleMinor.inputs 6) 1) (hc : c.IsDeterministicDecomposable)
    (hf : c.Computes Boolean.interpretation (single (cycleMinorFn 6))) :
    cutCover (ZMod 2) 6 2 4 ≤ (8 * c.size + 1 : ℕ) ∧
      hcComponentSize (ZMod 2) 6 ≤ (4 * c.size + 1 : ℕ) :=
  ⟨hc.cutCover_le hf (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc.hcComponentSize_le hf⟩

/-- A read-once parity program with `w` wires computing the function bounds the cut cover number
by `2 (2 + 5 w) + 1` and the component size of `HC_6` by `2 + 5 w + 1`. -/
example {n : ℕ} (P : NBP (Fin (CycleMinor.inputs 6)) Bool n) (hP : P.IsReadOnce)
    (hf : ∀ z, P.AcceptsParity z ↔ cycleMinorFn 6 z = true) :
    cutCover (ZMod 2) 6 2 4 ≤ (2 * (2 + 5 * P.wireCount) + 1 : ℕ) ∧
      hcComponentSize (ZMod 2) 6 ≤ (2 + 5 * P.wireCount + 1 : ℕ) :=
  ⟨NBP.cutCover_le hP hf (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    NBP.hcComponentSize_le hP hf⟩

/-! ### From lower bounds on the measures to size lower bounds -/

/-- If every list of cuts writing every minor table as a sum has at least `M` cuts, then every
syntactically multilinear circuit computing the function has `2 s + 1 ≥ M`. -/
example (M : ℕ) (hM : ∀ L, CutRepresentable (ZMod 2) 6 2 4 L → M ≤ L)
    (A : Circuit (arithSignature (ZMod 2)) (CycleMinor.inputs 6) 1)
    (hA : A.IsSyntacticallyMultilinear) (hf : A.ComputesMultilinear (cycleMinorFn 6)) :
    M ≤ 2 * A.size + 1 := by
  have h := ((le_cutCover_iff (k := (M : ℕ∞))).mpr fun L hL => by exact_mod_cast hM L hL).trans
    (cutCover_le_of_syntacticallyMultilinear (K := ZMod 2) A hA hf (by norm_num) (by norm_num)
      (by norm_num) (by norm_num))
  exact_mod_cast h

/-- If every circuit whose component of degree `6` is `HC_6` has at least `M` gates, then every
read-once parity program computing the function has `2 + 5 w + 1 ≥ M`. -/
example (M : ℕ) (hM : ∀ c : Circuit (arithSignature (ZMod 2)) (6 * 6) 1,
      MvPolynomial.homogeneousComponent 6
          (c.eval (arithInterpretationWith (ZMod 2) MvPolynomial.C) MvPolynomial.X 0) =
        (Arithmetic.hcFamily (ZMod 2)).poly 6 → M ≤ c.size)
    {n : ℕ} (P : NBP (Fin (CycleMinor.inputs 6)) Bool n) (hP : P.IsReadOnce)
    (hf : ∀ z, P.AcceptsParity z ↔ cycleMinorFn 6 z = true) : M ≤ 2 + 5 * P.wireCount + 1 := by
  have h := ((le_hcComponentSize_iff (k := (M : ℕ∞))).mpr fun c hc => by
    exact_mod_cast hM c hc).trans
    (NBP.hcComponentSize_le (K := ZMod 2) hP hf)
  exact_mod_cast h

/-! ### Minor tables -/

/-- The table of the `2 × 4` matrix `[[1, 0, 0, 0], [1, 1, 0, 0]]` is its minor on the two selected
columns, here the first two. -/
example : minorTable ℤ !![1, 0, 0, 0; 1, 1, 0, 0] ![true, true, false, false] = 1 := by
  rw [minorTable_eq_det _ (Fin.castLEOrderEmb (by norm_num)) (by decide) (by decide)]
  simp [Matrix.det_fin_two]

/-- The table is zero when three columns are selected. -/
example : minorTable ℤ !![1, 0, 0, 0; 1, 1, 0, 0] ![true, true, true, false] = 0 :=
  minorTable_of_card_ne _ (by decide)

/-! ### A read-once parity program at `d = 1` -/

/-- At `d = 1` the inputs are `Y (0, 0)`, `x 0` and `b`, and the function is `¬ x 0` for `b = 1`
and `Y (0, 0)` for `b = 0`. -/
theorem cycleMinorFn_one (z : Fin (CycleMinor.inputs 1) → Bool) :
    cycleMinorFn 1 z = if z 2 then !z 1 else z 0 := by
  have hb : (bIdx : Fin (CycleMinor.inputs 1)) = 2 := rfl
  have hx : xIdx (0 : Fin 1) = 1 := rfl
  have hy : yIdx ((0, 0) : Fin 1 × Fin 1) = 0 := rfl
  simp only [cycleMinorFn, hb]
  cases z 2
  · rw [cycleMinor_false]
    have : IsCycleMatrix (fun v : Fin 1 × Fin 1 => z (yIdx v)) ↔ z 0 = true := by
      constructor
      · rintro ⟨σ, -, h⟩
        rw [← hy, ← congrFun h (0, 0)]
        simp [permBoolMatrix, Subsingleton.elim (σ 0) 0]
      · intro h0
        refine ⟨1, Equiv.Perm.isCycleOn_of_subsingleton _ _, funext fun v => ?_⟩
        rw [Subsingleton.elim v (0, 0), hy, h0]
        simp [permBoolMatrix]
    simp [this]
  · rw [cycleMinor_true]
    cases h1 : z 1
    · rw [minorBit_eq_det _ (Fin.castLEOrderEmb (by norm_num)) (fun c => c.elim0) (by
        simp [selected, hx, h1, Finset.filter_eq_empty_iff])]
      simp
    · exact minorBit_of_card_ne _ (by simp [selected, hx, h1, Finset.filter_true_of_mem])

/-- A read-once parity program computing the function at `d = 1`: the source tests `b`, then the
program tests `¬ x 0` or `Y (0, 0)`. Nodes: `0` the target, `1` tests `¬ x 0`, `2` tests `Y (0, 0)`,
`3` the source. -/
def cycleMinorOne : NBP (Fin (CycleMinor.inputs 1)) Bool 4 :=
  NBP.target
    |>.node [⟨0, some (1, false)⟩]
    |>.node [⟨0, some (0, true)⟩]
    |>.node [⟨1, some (2, true)⟩, ⟨2, some (2, false)⟩]

theorem cycleMinorOne_isReadOnce : cycleMinorOne.IsReadOnce := by
  decide

theorem cycleMinorOne_computes (z : Fin (CycleMinor.inputs 1) → Bool) :
    cycleMinorOne.AcceptsParity z ↔ cycleMinorFn 1 z = true := by
  rw [cycleMinorFn_one, ← decide_eq_true_iff (p := cycleMinorOne.AcceptsParity z)]
  revert z
  decide

theorem cycleMinorOne_wireCount : cycleMinorOne.wireCount = 4 := by
  decide

/-- The hypotheses of the read-once parity bounds are met: with its `4` wires the program bounds
both measures at `d = 1`, with cuts of one coordinate. -/
example : cutCover (ZMod 2) 1 1 1 ≤ (2 * (2 + 5 * cycleMinorOne.wireCount) + 1 : ℕ) ∧
    hcComponentSize (ZMod 2) 1 ≤ (2 + 5 * cycleMinorOne.wireCount + 1 : ℕ) :=
  ⟨NBP.cutCover_le cycleMinorOne_isReadOnce cycleMinorOne_computes le_rfl le_rfl le_rfl le_rfl,
    NBP.hcComponentSize_le cycleMinorOne_isReadOnce cycleMinorOne_computes⟩

end CslibFrontierTests.CycleMinorMeasures
