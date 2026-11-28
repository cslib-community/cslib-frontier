/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Lupanov.FormulaConstruction
public import CslibFrontier.Computability.Circuit.Boolean.Lupanov.FormulaAsymptotics
public import CslibFrontier.Computability.Circuit.Boolean.Formula.ConstantFree

/-!
# Lupanov's unrestricted formula upper bound

For every positive `ε`, all Boolean functions on sufficiently many inputs have a De Morgan formula
with at most `(1 + ε) * 2 ^ n / log₂ n` literal occurrences. The formula has no constant gates and
negations occur only directly on inputs, matching the literal-only convention of
[Lupanov1961Formulas, §1, printed/PDF pp. 1–2 of the English translation].

This is the unrestricted-depth upper corollary of the theorem in §4, printed/PDF p. 8, using
the class inclusion in §1, equation (1), p. 3. The main theorem and equation (5) in §1, p. 4,
state the stronger result with alternating depth three, together with an almost-all lower bound.
Neither alternating depth nor the lower bound is asserted here. The finite construction factors
open-sphere selectors outside block formulas; this preserves the sharp upper constant when
depth is unrestricted.

The endpoint constructs actual native `Formula Boolean.signature n` objects. Its hypotheses ask
only for `ε > 0` and sufficiently many inputs; the partition, local coding, parameter estimates,
constant elimination and negation normalization are all proved internally.
-/

public section

namespace Cslib.Circuits.Boolean.LupanovFormula

open Filter Formula

private theorem two_le_formulaBound (a c r s : ℕ) :
    2 ≤ formulaBound a c (2 ^ r) s := by
  have hd : 0 < 2 ^ r := Nat.two_pow_pos r
  have hq : 1 ≤ 2 ^ (2 ^ r) / 2 ^ r := Nat.div_pos Nat.lt_two_pow_self.le hd
  have hprod : 1 ≤ (2 ^ c / s + 1) * (2 ^ s * c * s + 2 ^ r) :=
    Nat.mul_pos (Nat.succ_pos _) (hd.trans_le (Nat.le_add_left _ _))
  have hb : 2 ≤ (2 ^ r) ^ 2 + (2 ^ c / s + 1) * (2 ^ s * c * s + 2 ^ r) :=
    Nat.add_le_add (Nat.one_le_pow _ _ hd) hprod
  simpa only [Nat.one_mul, formulaBound] using
    Nat.mul_le_mul (Nat.two_pow_pos a) (le_trans (Nat.mul_le_mul hq hb) (Nat.le_add_left _ _))

/-- The finite synthesis bound can be attained in the literal-only model: no constant gates,
negations only directly on inputs, and the same numerical bound. -/
theorem exists_constantFree_isNNF_leafSize_le_formulaBound (a c r s : ℕ) (hs : 0 < s)
    (f : BooleanFunction (a + (c + 2 ^ r))) :
    ∃ F : Formula signature (a + (c + 2 ^ r)), F.IsConstantFree ∧ F.IsNNF ∧
      F.Computes interpretation f ∧ F.leafSize ≤ formulaBound a c (2 ^ r) s := by
  obtain ⟨F, hF, hsize⟩ := exists_computes_leafSize_le_formulaBound a c r s hs f
  have hn : 0 < a + (c + 2 ^ r) := by have := Nat.two_pow_pos r; omega
  obtain ⟨G, hG, hNNF, heval, hGsize⟩ := exists_constantFree_isNNF_leafSize_le hn F
  exact ⟨G, hG, hNNF, fun x => (heval x).trans (hF x),
    hGsize.trans (max_le (two_le_formulaBound a c r s) hsize)⟩

/-- Lupanov's unrestricted-depth formula upper bound: for every `ε > 0`, every Boolean function
on sufficiently many inputs has a constant-free formula in negation normal form with at most
`(1 + ε) * 2 ^ n / log₂ n` literal occurrences. This is the upper corollary of
[Lupanov1961Formulas, §4, unnumbered theorem, printed/PDF p. 8 of the translation], using
§1, equation (1), p. 3;
the stronger alternating-depth-three bound and the almost-all lower bound are not claimed. -/
theorem eventually_exists_computes_leafSize_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ f : BooleanFunction n,
      ∃ F : Formula signature n, F.IsConstantFree ∧ F.IsNNF ∧
        F.Computes interpretation f ∧
        (F.leafSize : ℝ) ≤ (1 + ε) * 2 ^ n / Real.logb 2 n := by
  filter_upwards [eventually_exists_formulaBound_real_le hε] with n hparams f
  obtain ⟨a, c, r, s, hs, rfl, hbound⟩ := hparams
  obtain ⟨F, hF, hNNF, hf, hsize⟩ :=
    exists_constantFree_isNNF_leafSize_le_formulaBound a c r s hs f
  exact ⟨F, hF, hNNF, hf, (Nat.cast_le.mpr hsize).trans hbound⟩

end Cslib.Circuits.Boolean.LupanovFormula
