/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.BlockNetworks
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Counting.ChoiceTable

/-!
# Reading original counting bits at the padded block clock

For an ordinary fair-coin table, the unused suffix of a completed run is arbitrary. Padding
therefore shifts the answer by exactly the number of extra coins. For an occurrence-labelled
counting machine the parsimonious binary table uses a unique zero suffix after every halt,
so the requested bit keeps its original index.
-/

public section

namespace Cslib.Complexity.CountingSimulation

open _root_.Turing _root_.Turing.MultiTapeTM

private theorem count_append_irrelevant {α : Type} (V : α × List Bool → Bool)
    (x : α) (t d : ℕ) (h : ∀ u, u.length = t → ∀ v, V (x, u ++ v) = V (x, u)) :
    acceptCount V x (t + d) = acceptCount V x t * 2 ^ d := by
  rw [acceptCount_add]
  have hs (u : Fin t → Bool) : acceptCount (fun z => V (z.1, List.ofFn u ++ z.2)) x d =
      (if V (x, List.ofFn u) then 1 else 0) * 2 ^ d := by
    rw [acceptCount_congr (W := fun _ => V (x, List.ofFn u))
      (fun w => h _ List.length_ofFn w)]
    cases hv : V (x, List.ofFn u) <;> simp [acceptCount_true, acceptCount_false]
  simp only [hs, ← Finset.sum_mul]
  rw [Finset.sum_boole]
  rfl

/-- A fair-coin machine whose branches have all halted by the source clock has exactly
one arbitrary suffix of padding choices for each bit string of the extra length. -/
theorem acceptCount_add_of_halted {k : ℕ} {S : Type} (M : MultiTapePTM k Bool S)
    (x : List Bool) (t d : ℕ)
    (h : ∀ u : List Bool, u.length = t → (M.stepCoins u (Cfg.init M.initial x)).state = none) :
    M.acceptCount x (t + d) = M.acceptCount x t * 2 ^ d := by
  apply count_append_irrelevant
  intro u hu v
  simp only [MultiTapePTM.runClosedCoins_eq_output_stepCoins, MultiTapePTM.stepCoins_append]
  have hh := h u hu
  let c := M.stepCoins u (Cfg.init M.initial x)
  have he : M.stepCoins v c = c := by
    induction v with
    | nil => rfl
    | cons a v ih =>
      rw [MultiTapePTM.stepCoins_cons, step_of_halt hh, ih]
  rw [he]

/-- Read an original fair-coin count bit by offsetting the physical contraction bit. -/
theorem padded_acceptCount_testBit {k : ℕ} {S : Type} (M : MultiTapePTM k Bool S)
    (x : List Bool) (t bit : ℕ)
    (h : ∀ u : List Bool, u.length = t → (M.stepCoins u (Cfg.init M.initial x)).state = none) :
    (M.acceptCount x (paddedTime t)).testBit (bit + (paddedTime t - t)) =
      (M.acceptCount x t).testBit bit := by
  let d := paddedTime t - t
  have he : paddedTime t = t + d := by dsimp [d]; have := le_paddedTime t; omega
  change (M.acceptCount x (paddedTime t)).testBit (bit + d) = _
  conv_lhs => rw [he, acceptCount_add_of_halted M x t d h, Nat.testBit_mul_two_pow]
  simp

/-- At the widened source clock a CTM's occurrence-labelled terminal count has no bit shift. -/
theorem padded_terminalCount_testBit {k width : ℕ} {S : Type} (hw : 0 < width)
    (M : MultiTapeCTM k Bool S) (x : List Bool) (t bit : ℕ)
    (hbound : ∀ cfg : Cfg k Bool S x, (M.actions cfg).length ≤ 2 ^ width)
    (h : M.HaltsWithin t (Cfg.init M.initial x)) :
    ((MultiTapeCTM.CountingChoice.table hw M).acceptCount x (paddedTime (t * width))).testBit bit =
      (M.acceptCount t (Cfg.init M.initial x)).testBit bit := by
  rw [MultiTapeCTM.CountingChoice.acceptCount_table_of_halts hw M x hbound h (le_paddedTime _)]

end Cslib.Complexity.CountingSimulation
