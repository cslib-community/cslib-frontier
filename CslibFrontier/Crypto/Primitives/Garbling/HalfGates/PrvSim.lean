/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.HalfGates.Reduction
public import CslibFrontier.Crypto.Primitives.Garbling.Asymptotic
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Tactic.PolyTime

/-!
# Half-gates garbling is simulation private

The half-gates scheme `HalfGates.scheme hash` over XOR–AND circuits is `prv.sim` secure with the
side information `Φ_circ`, which reveals the circuit, for every circular correlation robust hash
family `hash`: `CircularCorrelationRobust.prvSim_halfGates`. The simulator is `HalfGates.simWord`,
which does not depend on the adversary, so the proof gives more than the definition asks
(`CircularCorrelationRobust.negligible_prvSimAdvantage_simWord`): one PPT simulator whose
advantage against every uniform strict PPT adversary is negligible.

The proof bounds the number of gates of the adversary's chosen circuits by a polynomial `P k` in
the parameter, read from the length bound of its choice stage. At every parameter with
`2 P k ≤ 2 ^ k`, which holds from some parameter on, the advantage is exactly the circular
correlation robustness advantage of the certified reduction `HalfGates.prvSimReduction`
(`HalfGates.prvSimAdvantage_simWord_eq`). That reduction is legal at every level
(`HalfGates.isTweakUnique_prvSimReduction`) and oracle PPT
(`HalfGates.isOraclePPT_prvSimReduction`), so its advantage is negligible by
`CircularCorrelationRobust.negligible_advantage`.

This is this library's theorem under circular correlation robustness in the form of Definition 1
of Zahur, Rosulek and Evans [ZahurRosulekEvans2015] (§4.1, p. 10), as
`CircularCorrelationRobust` states it. It is not a formalization of Theorem 1 there (p. 12),
which proves `prv.sim` and `obv.sim` under the weaker Definition 3 (p. 11), circular
correlation robustness for naturally derived keys; Definition 3 is not formalized. The scheme
differs from Figure 2 (p. 9) in its tweaks, its projective encoding and its label length, as
`CslibFrontier.Crypto.Primitives.Garbling.HalfGates.Scheme` lists. Obliviousness is not
treated here.

## Main results

* `Cslib.Crypto.CircularCorrelationRobust.negligible_prvSimAdvantage_simWord`: the advantage of
  every uniform strict PPT adversary against the simulator `simWord` is negligible.
* `Cslib.Crypto.CircularCorrelationRobust.prvSim_halfGates`: half-gates garbling is `prv.sim`
  secure over `Φ_circ`.

## References

* [S. Zahur, M. Rosulek, D. Evans, *Two Halves Make a Whole: Reducing Data Transfer in Garbled
  Circuits using Half Gates*][ZahurRosulekEvans2015]
* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
-/

public section

namespace Cslib.Crypto

open Garbling Garbling.HalfGates Turing.MultiTapeTM Probability Filter

variable {hash : List Bool → List Bool → List Bool}

/-- **One simulator serves every adversary.** For a circular correlation robust hash family
`hash` and every uniform strict PPT `prv.sim` adversary `B`, the `prv.sim` advantage of `B`
against the simulator `simWord hash` for half-gates garbling with the side information `Φ_circ`
is negligible. -/
theorem CircularCorrelationRobust.negligible_prvSimAdvantage_simWord
    (h : CircularCorrelationRobust hash) {σ : Type} {encσ : σ ↪ List Bool}
    {B : ℕ → PrvSimAdversary XorAndCircuit σ}
    (hB : TwoStage.IsPPT encUnit (encQuery XorAndCircuit encXorAndCircuit) (encOption encPrvView)
      encBool encσ B) :
    Negligible fun k => prvSimAdvantage (HalfGates.scheme hash)
      (SideInfo.circ (HalfGates.scheme hash)) k (simWord hash k) (B k) := by
  obtain ⟨c, d, hlen⟩ := hB.choose.length_le
  let P : ℕ → ℕ := fun k => c * (4 * (k + 1)) ^ d
  have hP : ∀ k query state, (query, state) ∈ (ProbComp.eval ((B k).choose ())).support →
      query.fn.circuit.q ≤ P k := by
    intro k query state hmem
    have h₁ := hlen (k, ()) (query, state) hmem
    have h₂ := n_add_q_le_length_encValidCircuit query.fn.val
    have h₃ : (encValidCircuit query.fn.val).length ≤
        (encPair (encQuery XorAndCircuit encXorAndCircuit) encσ (query, state)).length := by
      simp only [length_encPair, encQuery_apply, encXorAndCircuit_apply]
      omega
    have h₄ : (encPair encUnary encUnit (k, ())).length + 1 ≤ 4 * (k + 1) := by
      have hu : (encUnit ()).length = 0 := rfl
      simp only [length_encPair, encUnary_apply, List.length_replicate, hu]
      omega
    calc query.fn.circuit.q
        ≤ c * ((encPair encUnary encUnit (k, ())).length + 1) ^ d := by
          simp only [XorAndCircuit.circuit] at h₂ ⊢
          omega
      _ ≤ P k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h₄ _)
  have hbound : ∀ k, (4 * (k + 1)) ^ d = 4 ^ d * (k + 1) ^ d := fun k => mul_pow _ _ _
  have hsmall : PolynomiallyBounded fun k => 2 * P k := by
    refine polynomiallyBounded_iff_le.mpr ⟨2 * c * 4 ^ d, d, fun k => ?_⟩
    simp only [P, hbound]
    ring_nf
    exact le_rfl
  have hev : ∀ᶠ k in atTop, 2 * P k ≤ 2 ^ k :=
    hsmall.eventually_lt_two_pow.mono fun _ hk => hk.le
  have hneg := h.negligible_advantage (isOraclePPT_prvSimReduction h.polyTime hB)
    (isTweakUnique_prvSimReduction hash B)
  refine negligible_of_eventually_le hneg ?_
  filter_upwards [hev] with k hk
  rw [prvSimAdvantage_simWord_eq hash B k fun query state hmem _ =>
    (Nat.mul_le_mul_left 2 (hP k query state hmem)).trans hk]

/-- **Half-gates garbling is `prv.sim` secure with the side information `Φ_circ`**, for every
circular correlation robust hash family `hash`: for every uniform strict PPT adversary there is a
PPT simulator, on `(1^k, y, f)` with XOR–AND circuits encoded by `encXorAndCircuit`, whose
advantage is negligible. The simulator `simWord hash` is the same for every adversary
(`CircularCorrelationRobust.negligible_prvSimAdvantage_simWord`). The model is the standard model
with uniform adversaries and a single `Garble` query, as in `Scheme.PrvSimSecure`.

This is this library's theorem under [ZahurRosulekEvans2015] Definition 1 (§4.1, p. 10), in the
form `CircularCorrelationRobust` states. It is not a formalization of Theorem 1 there (p. 12),
which assumes only the weaker Definition 3 (p. 11), circular correlation robustness for naturally
derived keys. The scheme also differs from Figure 2 (p. 9) in three ways: slot `s` of gate `g`
has the tweak `2 g + s` modulo `2 ^ k`, where Figure 2 takes its indices from `NextIndex`; the
encoding information `e` is projective, listing both labels of each input; and labels have
`k + 2` bits, where Figure 2 has `k`. -/
theorem CircularCorrelationRobust.prvSim_halfGates (h : CircularCorrelationRobust hash) :
    (HalfGates.scheme hash).PrvSimSecure (SideInfo.circ (HalfGates.scheme hash)) encXorAndCircuit
      encXorAndCircuit :=
  fun _ _ _ hB => ⟨simWord hash, isPPTOn_simWord h.polyTime,
    h.negligible_prvSimAdvantage_simWord hB⟩

end Cslib.Crypto
