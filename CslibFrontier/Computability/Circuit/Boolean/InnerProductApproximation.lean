/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.NonlinearCost
public import CslibFrontier.Foundations.BooleanAnalysis.InnerProduct
import CslibFrontier.Computability.Circuit.Simulation
import Mathlib.Tactic.Ring

/-!
# Optimal inner-product approximation with a nonlinear gate budget

The inner product of two `n`-bit strings is their sum of pairwise products over the Boolean ring.
Its sign has a flat Fourier spectrum of magnitude `2⁻ⁿ`. A circuit with `m` nonaffine binary
gates has Fourier norm at most `2ᵐ`, including circuits that freely reuse intermediate values.
Its absolute correlation with inner product is therefore at most `2ᵐ / 2ⁿ`.

This bound is exact for `m ≤ n`. Compute the products on any `m` coordinate pairs and XOR them.
The remaining independent pairs each contribute a factor `1/2` to correlation. Thus the greatest
correlation attainable over the full binary basis with at most `m` nonaffine gates is `2ᵐ / 2ⁿ`.
Equivalently, the optimal fraction of correct answers is `(1 + 2ᵐ / 2ⁿ) / 2`.

The cost counts nonaffine gates, with affine gates, constants and output wires free. There is no
restriction on total size, depth or reuse. These are bounds on nonlinear cost, not superlinear
lower bounds on unrestricted total circuit size. All statements include `m = 0` and `n = 0`.

## Main results

* `Cslib.Circuits.Circuit.abs_correlation_innerProduct_le`: the upper bound for any Boolean
  basis of fan-in at most two.
* `Cslib.Circuits.Boolean.isGreatest_innerProduct_correlation`: the exact optimum over the
  full binary basis, with an attaining circuit.
-/

public section

namespace Cslib.Circuits

open Finset BitString
open scoped BigOperators

universe u

/-- A circuit on `2n` inputs with `m` nonaffine binary gates has absolute correlation at most
`2ᵐ / 2ⁿ` with inner product, even with unlimited affine gates and arbitrary sharing. -/
theorem Circuit.abs_correlation_innerProduct_le {σ : Signature.{u}} {n : ℕ}
    (c : Circuit σ (n + n) 1) (I : Interpretation σ Bool)
    (hArity : ∀ op, σ.Arity op ≤ 2) :
    |𝔼 x, signVal (fstBits x ⬝ᵥ sndBits x) * signVal (c.eval I x 0)| ≤
      (2 : ℝ) ^ c.program.cost (Boolean.nonlinearCost I) / 2 ^ n :=
  (abs_expect_signVal_dotProduct_mul_le (fun x => signVal (c.eval I x 0))).trans
    (div_le_div_of_nonneg_right
      (c.sum_abs_fourierCoeff_signVal_eval_le_two_pow_nonlinearCost I hArity 0)
      (by positivity))

namespace Boolean

private theorem isAffine_add_pair : IsAffine (fun x : Fin 2 → Bool => x 0 + x 1) := by
  intro x y z
  simp only [Pi.add_apply]; ring

private theorem not_isAffine_mul_pair : ¬ IsAffine (fun x : Fin 2 → Bool => x 0 * x 1) := by
  intro h
  have h' := h ![false, false] ![true, false] ![false, true]
  norm_num [Pi.add_apply, Bool.add_eq_xor, Bool.mul_eq_and] at h'

private theorem nonlinearCost_full_add :
    nonlinearCost (fullInterpretation (k := 2) (Carrier := Bool))
      (.fn fun x => x 0 + x 1) = 0 := by
  change (if IsAffine (fun x : Fin 2 → Bool => x 0 + x 1) then 0 else 1) = 0
  simp only [isAffine_add_pair, ite_true]

private theorem nonlinearCost_full_mul :
    nonlinearCost (fullInterpretation (k := 2) (Carrier := Bool))
      (.fn fun x => x 0 * x 1) = 1 := by
  change (if IsAffine (fun x : Fin 2 → Bool => x 0 * x 1) then 0 else 1) = 1
  simp only [not_isAffine_mul_pair, ite_false]

private theorem nonlinearCost_full_con (b : Bool) :
    nonlinearCost (fullInterpretation (k := 2) (Carrier := Bool)) (.con b) = 0 := by
  change (if IsAffine (fun _ : Fin 0 → Bool => b) then 0 else 1) = 0
  rw [ite_eq_left (isAffine_const (by decide) b)]

private theorem exists_circuit_innerProduct_sum {n : ℕ} (S : Finset (Fin n)) :
    ∃ c : Circuit (fullSignature 2 Bool) (n + n) 1,
      c.program.cost (nonlinearCost fullInterpretation) = S.card ∧
      ∀ x, c.eval fullInterpretation x 0 = ∑ i ∈ S, fstBits x i * sndBits x i := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨Circuit.oneGate (.con false) Fin.elim0, (Circuit.cost_program_oneGate
      (σ := fullSignature 2 Bool) (.con false) Fin.elim0 _).trans (nonlinearCost_full_con false),
      fun x => ?_⟩
    change false = ∑ i ∈ (∅ : Finset (Fin n)), fstBits x i * sndBits x i
    simp only [sum_empty, Bool.zero_eq_false]
  | @insert i S hi ih =>
    obtain ⟨c, hcost, hc⟩ := ih
    let pair : Circuit (fullSignature 2 Bool) (n + n) 1 :=
      Circuit.oneGate (.fn fun x => x 0 * x 1) ![Fin.castAdd n i, Fin.natAdd n i]
    let add : Circuit (fullSignature 2 Bool) 2 1 :=
      Circuit.oneGate (.fn fun x => x 0 + x 1) id
    refine ⟨add.comp (pair.append c), ?_, fun x => ?_⟩
    · have hpair : pair.program.cost (nonlinearCost fullInterpretation) = 1 :=
        (Circuit.cost_program_oneGate _ _ _).trans nonlinearCost_full_mul
      have hadd : add.program.cost (nonlinearCost fullInterpretation) = 0 :=
        (Circuit.cost_program_oneGate _ _ _).trans nonlinearCost_full_add
      rw [Circuit.cost_program_comp, Circuit.cost_program_append, hpair, hadd, hcost,
        card_insert_of_notMem hi]
      omega
    · rw [Circuit.eval_comp, Circuit.eval_append]
      change fstBits x i * sndBits x i + c.eval fullInterpretation x 0 = _
      rw [hc, sum_insert hi]

private theorem fullSignature_arity_le_two (op : (fullSignature 2 Bool).Op) :
    (fullSignature 2 Bool).Arity op ≤ 2 := by
  cases op <;> simp [fullSignature]

/-- Among full-binary-basis circuits with at most `m ≤ n` nonaffine gates, the largest
correlation with the `n`-pair inner product is exactly `2ᵐ / 2ⁿ`. The witness computes any `m`
of the pairwise products and XORs them; all affine operations are free. -/
theorem isGreatest_innerProduct_correlation {n m : ℕ} (hm : m ≤ n) :
    IsGreatest
      {ρ : ℝ | ∃ c : Circuit (fullSignature 2 Bool) (n + n) 1,
        c.program.cost (nonlinearCost fullInterpretation) ≤ m ∧
        (𝔼 x, signVal (fstBits x ⬝ᵥ sndBits x) * signVal (c.eval fullInterpretation x 0)) = ρ}
      ((2 : ℝ) ^ m / 2 ^ n) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨S, -, hS⟩ := exists_subset_card_eq (s := (univ : Finset (Fin n))) (by simpa using hm)
    obtain ⟨c, hcost, hc⟩ := exists_circuit_innerProduct_sum S
    refine ⟨c, hcost.trans_le hS.le, ?_⟩
    simp only [hc]
    rw [expect_signVal_dotProduct_mul_signVal_sum, hS]
  · rintro ρ ⟨c, hcost, rfl⟩
    exact (le_abs_self _).trans ((c.abs_correlation_innerProduct_le
      fullInterpretation fullSignature_arity_le_two).trans
        (div_le_div_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hcost) (by positivity)))

end Boolean
end Cslib.Circuits
