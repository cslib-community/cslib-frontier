/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.BQP.Time
public import CslibFrontier.Computability.Complexity.Classes.CeqP
import CslibFrontier.Computability.Circuit.Quantum.PhaseOracle
import CslibFrontier.Computability.Complexity.Classes.BQP.Counting
import CslibFrontier.Computability.Complexity.Classes.BQP.ReturnTest
import CslibFrontier.Computability.Complexity.Classes.QMA.MA
import CslibFrontier.Computability.Complexity.Classes.SharpP.Combinators
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Nondeterministic quantum computation and nonzero counting gaps

`NQP` accepts exactly when the probability of measuring one on the output qubit is positive.
We prove `NQP_eq_coCeqP` for polynomial-time uniform circuits over Hadamard, NOT, CNOT and Toffoli.
The exact path sum gives the upper bound. For the converse we implement a difference of two counts
as a circuit's acceptance bias, flip the phase of its accepting subspace and uncompute.
Measuring return to the input gives the square of the bias
(`exists_uniformCircuitFamily_acceptProb_sq_of_mem_GapP`).
[Fenner, Green, Homer and Pruim][FennerGreenHomerPruim1999], Theorem 1.1, use polynomial-time
quantum Turing machines with algebraic amplitudes. Their construction for the counting-to-quantum
direction (Theorem 3.2) uses only signs and Hadamard amplitudes, as observed in Section 4.

## Main definitions

* `Cslib.Complexity.NQP` accepts members with strictly positive probability.

## Main results

* `Cslib.Complexity.NQP_eq_coCeqP` characterizes nonzero quantum acceptance by a nonzero GapP
  function.
* `Cslib.Complexity.exists_uniformCircuitFamily_acceptProb_sq_of_mem_GapP` realizes the square
  of a normalized GapP function as an exact acceptance probability.
* `Cslib.Complexity.NQP_eq_iUnion_NQTIME` recovers the polynomial gate bounds.

## References

* [S. Fenner, F. Green, S. Homer and R. Pruim, *Determining acceptance possibility for a quantum
  computation is hard for the polynomial hierarchy*][FennerGreenHomerPruim1999],
  arXiv:quant-ph/9812056v1, Theorems 1.1 and 3.2.
-/

public section

namespace Cslib.Complexity

open Quantum Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- Languages recognized with strictly positive acceptance probability by polynomial-time
uniform elementary quantum circuits. This is the circuit model of nondeterministic quantum
polynomial time over Hadamard, NOT, CNOT and Toffoli. -/
@[expose] def NQP (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ F : UniformCircuitFamily, ∀ a, a ∈ A ↔ 0 < F.acceptProb (enc a)}

/-- Nondeterministic quantum polynomial time is the union of the polynomial gate bounds in
`NQTIME`. -/
theorem NQP_eq_iUnion_NQTIME : NQP enc = ⋃ k : ℕ, NQTIME enc fun n => n ^ k := by
  refine Set.Subset.antisymm (fun A ⟨F, hF⟩ => ?_) (Set.iUnion_subset fun _ _ ⟨F, _, _, _, hF⟩ =>
    ⟨F, hF⟩)
  obtain ⟨d, c₁, c₂, hg⟩ := F.exists_polynomial_gate_bound
  exact Set.mem_iUnion.mpr ⟨d, F, c₁, c₂, hg, hF⟩

/-- The nonzero acceptance probability of an elementary circuit detects a nonzero GapP
numerator in the exact path sum. -/
theorem NQP_subset_coCeqP : NQP enc ⊆ coCeqP enc := by
  rintro A ⟨F, hF⟩
  refine mem_coCeqP_iff_exists_GapP.mpr ⟨_, acceptGap_mem_GapP F, fun a => ?_⟩
  rw [hF a]
  have h := F.acceptProb_nonneg (enc a)
  change Quantum.acceptProb _ _ _ ≥ 0 at h
  change 0 < Quantum.acceptProb _ _ _ ↔ _
  rw [lt_iff_le_and_ne, and_iff_right h, ne_comm, acceptProb_eq_acceptGap _ (F.wellFormed _) _]
  simp

/-- A GapP function is the acceptance bias of a uniform circuit, scaled by a power of two
depending only on the encoded input length. Equal-length padded verifiers for the two counts are
selected by a fair bit, complementing the first verifier. -/
private theorem exists_uniformCircuitFamily_bias_of_mem_GapP {g : α → ℤ} (hg : g ∈ GapP enc) :
    ∃ (F : UniformCircuitFamily) (p : Polynomial ℕ), ∀ a,
      1 - 2 * F.acceptProb (enc a) = (g a : ℝ) / 2 ^ p.eval (enc a).length := by
  obtain ⟨f₁, ⟨p, V₁, h₁, hf₁⟩, f₂, ⟨q, V₂, h₂, hf₂⟩, hg⟩ := hg
  let W₁ := padVerifier (fun a => p.eval (enc a).length) V₁
  let W₂ := padVerifier (fun a => q.eval (enc a).length) V₂
  let V := selectVerifier (fun x => !W₁ x) W₂
  have hV : ComputableInPolyTime V (encPair enc encBits) encBool := by
    dsimp only [V, W₁, W₂]
    fun_prop
  obtain ⟨F, hF⟩ := exists_uniformCircuitFamily hV
  refine ⟨(UniformVerifierFamily.ofMA F 0 (p + q + 1)).toUniformCircuitFamily, p + q, fun a => ?_⟩
  rw [UniformVerifierFamily.acceptProb_ofMA_zeroWitness F (p + q + 1) (enc a) (fun w => V (a, w))
    (fun w _ => hF (a, w))]
  change 1 - 2 * ((acceptCount V a _) / (2 : ℝ) ^ _) = _
  let r := (p + q).eval (enc a).length
  have hr : (p + q + 1).eval (enc a).length = r + 1 := by simp [r]
  have htotal := acceptCount_add_acceptCount_not W₁ a r
  have h₁' : acceptCount W₁ a r = f₁ a :=
    (acceptCount_padVerifier_of_le _ _ (by simp [r])).trans (hf₁ a).symm
  have h₂' : acceptCount W₂ a r = f₂ a :=
    (acceptCount_padVerifier_of_le _ _ (by simp [r])).trans (hf₂ a).symm
  rw [h₁'] at htotal
  rw [hr, acceptCount_selectVerifier, h₂', hg a, pow_succ]
  change 1 - 2 * _ = _ / (2 : ℝ) ^ r
  push_cast
  have hsum : (f₁ a : ℝ) + (acceptCount (fun x => !W₁ x) a r : ℝ) = (2 : ℝ) ^ r := by
    exact_mod_cast htotal
  field_simp
  linarith

private def phaseFamily (F : UniformCircuitFamily) : UniformCircuitFamily :=
  { F with
    gates := fun n => GateCode.phaseOracleCodes (F.gates n) 0
    computableInPolyTime_gates := by
      have := F.computableInPolyTime_gates
      unfold GateCode.phaseOracleCodes
      fun_prop
    wellFormed := by
      intro n g hg
      rcases List.mem_append.mp hg with hg | hg
      · rcases List.mem_append.mp hg with hg | hg
        · exact F.wellFormed n g hg
        · exact GateCode.wellFormed_zCodes (F.width_pos n) g hg
      · exact F.wellFormed n g (List.mem_reverse.mp hg) }

/-- Every GapP function is realized by a uniform quantum circuit with acceptance probability
equal to its square divided by a power of two depending only on the input length. This is the
acceptance probability in [Fenner et al.][FennerGreenHomerPruim1999], Theorem 3.2, for our
elementary circuit model. -/
theorem exists_uniformCircuitFamily_acceptProb_sq_of_mem_GapP {g : α → ℤ} (hg : g ∈ GapP enc) :
    ∃ (F : UniformCircuitFamily) (p : Polynomial ℕ), ∀ a,
      F.acceptProb (enc a) = ((g a : ℝ) / 2 ^ p.eval (enc a).length) ^ 2 := by
  obtain ⟨F, p, hF⟩ := exists_uniformCircuitFamily_bias_of_mem_GapP hg
  refine ⟨(phaseFamily F).returnTest, p, fun a => ?_⟩
  rw [UniformCircuitFamily.acceptProb_returnTest]
  simp only [phaseFamily, Circuit.run_phaseOracleCodes_input (F.wellFormed _) (F.width_pos _) _]
  change ‖1 - 2 * (F.acceptProb (enc a) : ℂ)‖ ^ 2 = _
  conv_lhs => norm_cast
  rw [Real.norm_eq_abs, sq_abs, hF]

/-- A language with a GapP function nonzero exactly on its members is in nondeterministic
quantum polynomial time. -/
theorem coCeqP_subset_NQP : coCeqP enc ⊆ NQP enc := by
  intro A hA
  obtain ⟨g, hg, hA⟩ := mem_coCeqP_iff_exists_GapP.mp hA
  obtain ⟨F, p, hF⟩ := exists_uniformCircuitFamily_acceptProb_sq_of_mem_GapP hg
  refine ⟨F, fun a => ?_⟩
  rw [hA a, hF a, sq_pos_iff]
  simp

/-- **NQP = coC₌P** for polynomial-time uniform Hadamard, NOT, CNOT and Toffoli circuits,
the circuit version of [Fenner et al.][FennerGreenHomerPruim1999], Theorem 1.1. -/
theorem NQP_eq_coCeqP : NQP enc = coCeqP enc :=
  Set.Subset.antisymm NQP_subset_coCeqP coCeqP_subset_NQP

end Cslib.Complexity
