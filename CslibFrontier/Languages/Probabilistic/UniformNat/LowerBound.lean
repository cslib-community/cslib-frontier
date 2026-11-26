/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.UniformNat
import Cslib.Probability.PMF
import CslibFrontier.Tactic.ENNRealToReal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lower bounds on the residue probabilities of `sampleModNat`

`sampleModNat w m` reduces a number written with `w` fair coins modulo `m`. Each residue `i < m`
is hit by at least `⌊2 ^ w / m⌋` of the `2 ^ w` coin outcomes, so its probability is at least
`(1 - m / 2 ^ w) / m`, that is, `1 / m - 1 / 2 ^ w`. The bound holds for every `w`; it is vacuous
when `2 ^ w ≤ m`. When `m` divides `2 ^ w`, the residue distribution is exact (`Pr[i] ≥ 1 / m`).

## Main results

* `Cslib.ProbComp.le_eval_sampleModNat_toReal`: every residue below `m` has probability at least
  `(1 - m / 2 ^ w) / m`, in `ℝ`.
* `Cslib.ProbComp.one_le_mul_eval_sampleModNat_add`: the same bound in `ℝ≥0∞`, without
  subtraction: `1 ≤ m * Pr[i] + m / 2 ^ w`.
* `Cslib.ProbComp.one_le_mul_eval_sampleModNat_of_dvd`: when `m ∣ 2 ^ w`, `1 ≤ m * Pr[i]` in
  `ℝ≥0∞` without an additive error term.
-/

public section

namespace Cslib.ProbComp

open Probability
open scoped ENNReal

private theorem card_div_le_filter_mod_eq {w m i : ℕ} (hi : i < m) :
    2 ^ w / m ≤ (Finset.univ.filter (fun x : Fin (2 ^ w) => x.val % m = i)).card := by
  have hm : 0 < m := (Nat.zero_le _).trans_lt hi
  let emb : Fin (2 ^ w / m) ↪ Fin (2 ^ w) :=
    ⟨fun q => ⟨q.val * m + i, by
      have := Nat.mul_le_mul_right m q.isLt
      have := Nat.div_mul_le_self (2 ^ w) m
      linarith⟩, fun _ _ hab => Fin.ext (Nat.mul_right_cancel hm
        (Nat.add_right_cancel (Fin.mk.inj hab)))⟩
  calc 2 ^ w / m = (Finset.univ.map emb).card := by simp only [Finset.card_map, Finset.card_fin]
    _ ≤ (Finset.univ.filter (fun x : Fin (2 ^ w) => x.val % m = i)).card :=
      Finset.card_le_card fun x hx => by
        obtain ⟨q, -, rfl⟩ := Finset.mem_map.mp hx
        simp [emb, Nat.add_comm _ i, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]

private theorem eval_sampleModNat_eq_card_mul_inv (w m i : ℕ) :
    ProbComp.eval (ProbComp.sampleModNat w m) i =
      ((Finset.univ.filter (fun x : Fin (2 ^ w) => x.val % m = i)).card : ℝ≥0∞) *
        ((2 : ℝ≥0∞) ^ w)⁻¹ := by
  rw [ProbComp.eval_sampleModNat, PMF.map_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat,
    eq_comm (a := i), ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- Pointwise lower bound on `sampleModNat w m`: every residue `i < m` has probability at least
`(1 - m / 2 ^ w) / m`. -/
theorem le_eval_sampleModNat_toReal {w m i : ℕ} (hi : i < m) :
    (1 - (m : ℝ) / (2 : ℝ) ^ w) * (m : ℝ)⁻¹ ≤
      (ProbComp.eval (ProbComp.sampleModNat w m) i).toReal := by
  have hm : 0 < m := (Nat.zero_le _).trans_lt hi
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let Q := 2 ^ w / m
  have hQ_ineq : (2 : ℝ) ^ w - m ≤ (Q : ℝ) * m := by
    have hrem : 2 ^ w ≤ (Q + 1) * m := by
      have := Nat.div_add_mod (2 ^ w) m
      have := Nat.mod_lt (2 ^ w) hm
      dsimp only [Q]
      nlinarith
    linarith [show (2 : ℝ) ^ w ≤ ((Q : ℝ) + 1) * m by exact_mod_cast hrem]
  have hQ_le : (Q : ℝ) ≤ (Finset.univ.filter (fun x : Fin (2 ^ w) => x.val % m = i)).card := by
    exact_mod_cast card_div_le_filter_mod_eq hi
  rw [eval_sampleModNat_eq_card_mul_inv]
  ennreal_to_real
  calc (1 - (m : ℝ) / (2 : ℝ) ^ w) * (m : ℝ)⁻¹
      = ((2 : ℝ) ^ w - m) / ((m : ℝ) * (2 : ℝ) ^ w) := by field_simp
    _ ≤ ((Q : ℝ) * m) / ((m : ℝ) * (2 : ℝ) ^ w) := by gcongr
    _ = (Q : ℝ) * ((2 : ℝ) ^ w)⁻¹ := by field_simp
    _ ≤ _ := by gcongr

/-- The pointwise lower bound on `sampleModNat w m` in `ℝ≥0∞`, without subtraction: for every
residue `i < m`, `m` times its probability is at least `1 - m / 2 ^ w`. -/
theorem one_le_mul_eval_sampleModNat_add {w m i : ℕ} (hi : i < m) :
    1 ≤ (m : ℝ≥0∞) * ProbComp.eval (ProbComp.sampleModNat w m) i + m / 2 ^ w := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_le i).trans_lt hi
  ennreal_to_real
  have hcancel :
      (m : ℝ) * ((1 - (m : ℝ) / (2 : ℝ) ^ w) * (m : ℝ)⁻¹) = 1 - (m : ℝ) / (2 : ℝ) ^ w := by
    field_simp
  nlinarith [mul_le_mul_of_nonneg_left (le_eval_sampleModNat_toReal (w := w) hi) hmR.le]

/-- Exact divisibility lower bound on `sampleModNat w m` in `ℝ≥0∞`: when `m` divides `2 ^ w`, every
residue `i < m` has probability at least `1 / m` (`1 ≤ m * Pr[i]`) without bias. -/
theorem one_le_mul_eval_sampleModNat_of_dvd {w m i : ℕ} (hi : i < m) (hdvd : m ∣ 2 ^ w) :
    1 ≤ (m : ℝ≥0∞) * ProbComp.eval (ProbComp.sampleModNat w m) i := by
  rw [eval_sampleModNat_eq_card_mul_inv]
  have hcard : ((2 ^ w / m : ℕ) : ℝ≥0∞) ≤
      (Finset.univ.filter (fun x : Fin (2 ^ w) => x.val % m = i)).card := by
    exact_mod_cast card_div_le_filter_mod_eq (w := w) hi
  calc (1 : ℝ≥0∞)
      = ((2 : ℝ≥0∞) ^ w) * ((2 : ℝ≥0∞) ^ w)⁻¹ :=
        (ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero)
          (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)).symm
    _ = (m : ℝ≥0∞) * (((2 ^ w / m : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ w)⁻¹) := by
        rw [← mul_assoc, mul_comm (m : ℝ≥0∞)]
        exact congrArg (· * ((2 : ℝ≥0∞) ^ w)⁻¹) (by exact_mod_cast (Nat.div_mul_cancel hdvd).symm)
    _ ≤ _ := by gcongr

end Cslib.ProbComp
