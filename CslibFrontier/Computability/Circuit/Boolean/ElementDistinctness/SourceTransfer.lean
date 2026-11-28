/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.ElementDistinctness.BatchTransfer
public import CslibFrontier.Computability.Circuit.Boolean.ElementDistinctness.NoPortsVolume
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.TrivalentVolume
import CslibFrontier.Computability.Circuit.Frontier.Compiler.OpenBitNetwork
import CslibFrontier.Computability.Circuit.InnerSize
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The two source inputs to the element-distinctness lower bound

Over a field without ports, the routing rectangle gives a superlinear lower bound directly.
Over a finite field with ports, [OpenAI2026EuclideanSpectrum, Proposition 14.1] supplies the exact
tagged compiler and [OpenAI2026HamiltonianPermanent, §12.1 and Theorem 12.1] supplies the
polynomial-size signed verifier and its hardness on joint batches. The theorem below assumes
these two inputs for the field under consideration. These are the remaining source results
needed for an unconditional native proof of [OpenAI2026MatrixExponentNineFourths, Theorem 2.2]
over a finite field. No field classification is required by the transfer.
-/

public section

namespace Cslib.Circuits.Boolean.ElementDistinctness

open Filter Frontier Frontier.OpenBitNetwork

/-- Minimum exact trivalent volume over all internal graphs realizing `t` lists of
`2 ^ w` records of `2 * w` bits. The lists can share internal wires. -/
@[expose] noncomputable def batchVolume (K : Type) [CommSemiring K] (w t : ℕ) : ℕ :=
  minTrivalentVolume (fun z : Fin t × Fin (2 ^ w * (2 * w)) → Bool =>
    ∏ i : Fin t, if elementDistinctness (2 ^ w) (2 * w) (fun q => z (i, q)) then (1 : K) else 0)

/-- For every width and batch count, some trivalent network realizes the minimum joint volume. -/
theorem exists_network_eq_batchVolume (K : Type) [CommSemiring K] (w t : ℕ) :
    ∃ (V E : Type) (_ : Fintype V) (_ : Fintype E) (_ : DecidableEq E)
      (M : OpenBitNetwork K (Fin t × Fin (2 ^ w * (2 * w))) V E), M.Trivalent ∧
      (∀ z, M.contraction z = ∏ i : Fin t,
        if elementDistinctness (2 ^ w) (2 * w) (fun q => z (i, q)) then 1 else 0) ∧
      M.volume = batchVolume K w t := by
  obtain ⟨B, hB, _⟩ := exists_computes_size_eq_complexity (I := fullInterpretation (k := 2))
    (f := single (elementDistinctness (2 ^ w) (2 * w)))
  obtain ⟨_, _, _, _, _, P, hP, _, hp⟩ := Compiler.exists_trivalent_openBitNetwork B
    fullInterpretation K B.fanInAtMost_fullSignature
  obtain ⟨_, _, _, _, _, M, ht, _, hM⟩ := P.exists_tensorPower hP t
  apply exists_volume_eq_minTrivalentVolume _ M ht
  intro z
  have he (x) : B.eval fullInterpretation x 0 = elementDistinctness (2 ^ w) (2 * w) x :=
    congrFun (hB x) 0
  simpa only [hp, he] using hM z

private theorem eventually_lt_mul_rpow {a v : ℝ} (ha : 0 < a) (hv : 0 < v) :
    ∀ᶠ w : ℕ in atTop, (w : ℝ) ^ (a / 2) < v * (w : ℝ) ^ a := by
  have hhalf : 0 < a / 2 := by positivity
  have ht := (tendsto_rpow_atTop hhalf).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [ht.eventually_gt_atTop (1 / v), eventually_ge_atTop 1] with w hw hpos
  have hp : 0 < (w : ℝ) := by exact_mod_cast hpos
  have hg : 1 < v * (w : ℝ) ^ (a / 2) := by simpa [mul_comm] using (div_lt_iff₀ hv).mp hw
  have hm := mul_lt_mul_of_pos_right hg (Real.rpow_pos_of_pos hp (a / 2))
  rwa [one_mul, mul_assoc, ← Real.rpow_add hp, add_halves] at hm

/-- Conditional transfer to the finite-field list-volume theorem and its unrestricted circuit
corollary. The two hypotheses are the exact tagged compiler and the existence of a polynomial
signed verifier whose batches remain hard over the field. Each is needed only in the ports
case. Their proofs for the source's universal verifier and compiler remain open in #8448. -/
theorem exists_bounds_of_exact_compiler_of_hard_verifier (K : Type) [Field K]
    (compiler : PartyTensor.HasPorts K →
      ∃ (a κ : ℝ) (C : ℕ), 0 < a ∧ 0 ≤ κ ∧ HasExactTaggedCompiler K a κ C)
    (workload : PartyTensor.HasPorts K →
      ∃ (ver : (ℓ : ℕ) → Circuit (fullSignature 2 Bool) (ℓ + (ℓ ^ 100 + 1)) 1)
        (δ ξ : ℝ) (A : ℕ), 0 < δ ∧ 0 < ξ ∧ (∀ᶠ ℓ : ℕ in atTop, (ver ℓ).size ≤ ℓ ^ A) ∧
        HasHardVerifierBatches K ver δ ξ) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧
      (∀ᶠ w : ℕ in atTop, ∀ t : ℕ, 0 < t → t ≤ 2 ^ w →
        (t * (2 ^ w * (2 * w)) : ℕ) * (w : ℝ) ^ ε < batchVolume K w t) ∧
      (∀ᶠ m : ℕ in atTop, let N := m * (2 * Nat.clog 2 m)
        c * N * (Real.logb 2 N) ^ ε <
          complexity (fullInterpretation (k := 2))
            (single (elementDistinctness m (2 * Nat.clog 2 m)))) ∧
      ∀ A : ℝ, ∀ᶠ m : ℕ in atTop, A * (m * (2 * Nat.clog 2 m) : ℕ) <
        complexity (fullInterpretation (k := 2))
          (single (elementDistinctness m (2 * Nat.clog 2 m))) := by
  have vol : ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ w : ℕ in atTop, ∀ t : ℕ, 0 < t → t ≤ 2 ^ w →
      (t * (2 ^ w * (2 * w)) : ℕ) * (w : ℝ) ^ ε < batchVolume K w t := by
    by_cases ports : PartyTensor.HasPorts K
    · obtain ⟨a, κ, C, ha, hκ, hc⟩ := compiler ports
      obtain ⟨ver, δ, ξ, A, hδ, hξ, hp, hh⟩ := workload ports
      let v := 1 / (32 * (3 * κ + 2) * (2 : ℝ) ^ a)
      have hv : 0 < v := by dsimp [v]; positivity
      refine ⟨a / 2, by positivity, ?_⟩
      filter_upwards [eventually_batch_volume_of_hard_verifier_of_compiler K ver ha hδ hξ hκ
        hp hh hc, eventually_lt_mul_rpow ha hv, eventually_ge_atTop 1] with w hw hpow hw1
      intro t ht hmax
      obtain ⟨V, E, _, _, _, M, hM, hD, hmin⟩ := exists_network_eq_batchVolume K w t
      have hc := hw t ht hmax V E M hM hD
      let b := t * (2 ^ w * (2 * w))
      have hb : 0 < (b : ℝ) := by dsimp [b]; positivity
      calc
        (b : ℝ) * (w : ℝ) ^ (a / 2) < b * (v * (w : ℝ) ^ a) :=
          mul_lt_mul_of_pos_left hpow hb
        _ = v * b * (w : ℝ) ^ a := by ring
        _ ≤ M.volume := hc
        _ = batchVolume K w t := by rw [hmin]
    · refine ⟨1 / 4, by norm_num, ?_⟩
      filter_upwards [eventually_elementDistinctness_volume_of_not_hasPorts K ports
        (by norm_num : (1 / 4 : ℝ) < 1 / 2)] with w hw
      intro t ht hmax
      obtain ⟨_, _, _, _, _, M, hM, hc, hmin⟩ := exists_network_eq_batchVolume K w t
      simpa only [Nat.cast_mul, hmin] using hw t ht hmax M hM hc
  obtain ⟨ε, he, hvol⟩ := vol
  have gates := eventual_complexity_of_single_copy_volume K (a := 1) he zero_lt_one (by
    filter_upwards [hvol] with w h
    intro V E _ _ _ N hN hD
    let I := Fin (2 ^ w * (2 * w))
    let e : Fin 1 × I ≃ I := Equiv.uniqueProd _ _
    obtain ⟨M, ht, hv, hc⟩ := N.exists_reindex hN e
    have hM : batchVolume K w 1 ≤ M.volume :=
      minTrivalentVolume_le _ M ht (fun x => by rw [hc, hD, Fin.prod_univ_one]; rfl)
    have h' := (h 1 (by decide) Nat.one_le_two_pow).le.trans (Nat.cast_le.mpr hM)
    simpa only [one_mul, hv] using h')
  refine ⟨ε, _, he, by positivity, hvol, gates, ?_⟩
  exact eventually_gt_mul_of_log_power he (by positivity) gates

end Cslib.Circuits.Boolean.ElementDistinctness
