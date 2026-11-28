/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.FreeXOR.Reduction
public import CslibFrontier.Crypto.Primitives.Garbling.Asymptotic
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Tactic.PolyTime

/-!
# Free-XOR garbling is simulation private

The Free-XOR scheme `FreeXOR.scheme hash` over valid conventional circuits is `prv.sim` secure
with the side information `phiXor`, which reveals the circuit topology and which gates compute XOR
while hiding the truth tables of all non-XOR gates, for every circular correlation robust hash
family `hash`: `CircularCorrelationRobust.prvSim_freeXOR` (and the universal-simulator form
`CircularCorrelationRobust.prvSimUniversal_freeXOR`). The simulator is `FreeXOR.simWord`, which
does not depend on the adversary, so the proof gives more than `Scheme.PrvSimSecure` asks
(`CircularCorrelationRobust.negligible_prvSimAdvantage_freeXOR`): one PPT simulator whose advantage
against every uniform strict PPT adversary is negligible.

The proof bounds the number of gates of the adversary's chosen circuits by a polynomial `P k` in
the parameter, read from the length bound of its choice stage. At every parameter with
`8 P k ≤ 2 ^ k`, which holds from some parameter on, the advantage is exactly the circular
correlation robustness advantage of the certified non-adaptive reduction `FreeXOR.prvSimReduction`
(`FreeXOR.prvSimAdvantage_simWord_eq`). That reduction is legal at every level
(`FreeXOR.isTweakUnique_prvSimReduction`) and oracle PPT
(`FreeXOR.isOraclePPT_prvSimReduction`), so its advantage is negligible by
`CircularCorrelationRobust.negligible_advantage`.

This is this library's own theorem under circular correlation robustness in the form of
Definition 1 of Zahur, Rosulek and Evans [ZahurRosulekEvans2015], as
`CircularCorrelationRobust` states it. It is not a formalization of Theorem 3 of Choi, Katz,
Kumaresan and Zhou [ChoiKatzKumaresanZhou2012] (which assumes dual-key circular correlation
robustness in Definition 4 together with 2PC) and not a random-oracle proof in the model of
Kolesnikov and Schneider [KolesnikovSchneider2008]. Obliviousness is not treated here.

## Main results

* `Cslib.Crypto.CircularCorrelationRobust.negligible_prvSimAdvantage_freeXOR`: the advantage of
  every uniform strict PPT adversary against the simulator `simWord` is negligible.
* `Cslib.Crypto.CircularCorrelationRobust.prvSimUniversal_freeXOR`: Free-XOR garbling is
  `prv.sim` secure over `phiXor` with a single universal simulator.
* `Cslib.Crypto.CircularCorrelationRobust.prvSim_freeXOR`: Free-XOR garbling is `prv.sim` secure
  over `phiXor`.

## References

* [S. Zahur, M. Rosulek, D. Evans, *Two Halves Make a Whole: Reducing Data Transfer in Garbled
  Circuits using Half Gates*][ZahurRosulekEvans2015]
* [S. G. Choi, J. Katz, R. Kumaresan, H.-S. Zhou, *On the Security of the "Free-XOR"
  Technique*][ChoiKatzKumaresanZhou2012]
* [V. Kolesnikov, T. Schneider, *Improved Garbled Circuit: Free XOR Gates and
  Applications*][KolesnikovSchneider2008]
* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
-/

public section

namespace Cslib.Crypto

open Garbling Garbling.FreeXOR Turing.MultiTapeTM Probability Filter

variable {hash : List Bool → List Bool → List Bool}

/-- Library infrastructure (no cited result): **One simulator serves every adversary.** For a
circular correlation robust hash family `hash` and every uniform strict PPT `prv.sim` adversary
`B`, the `prv.sim` advantage of `B` against the simulator `simWord hash` for Free-XOR garbling
with the side information `phiXor` is negligible. -/
theorem CircularCorrelationRobust.negligible_prvSimAdvantage_freeXOR
    (h : CircularCorrelationRobust hash) {σ : Type} {encσ : σ ↪ List Bool}
    {B : ℕ → PrvSimAdversary ValidCircuit σ}
    (hB : TwoStage.IsPPT encUnit (encQuery ValidCircuit encValidCircuit) (encOption encPrvView)
      encBool encσ B) :
    Negligible fun k => prvSimAdvantage (FreeXOR.scheme hash) FreeXOR.phiXor k
      (simWord hash k) (B k) := by
  obtain ⟨c, d, hlen⟩ := hB.choose.length_le
  let P : ℕ → ℕ := fun k => c * (4 * (k + 1)) ^ d
  have hP : ∀ k query state, (query, state) ∈ (ProbComp.eval ((B k).choose ())).support →
      query.fn.val.q ≤ P k := by
    intro k query state hmem
    have h₁ := hlen (k, ()) (query, state) hmem
    have h₂ := n_add_q_le_length_encValidCircuit query.fn
    have h₃ : (encValidCircuit query.fn).length ≤
        (encPair (encQuery ValidCircuit encValidCircuit) encσ (query, state)).length := by
      simp only [length_encPair, encQuery_apply]; omega
    have h₄ : (encPair encUnary encUnit (k, ())).length + 1 ≤ 4 * (k + 1) := by
      simp only [length_encPair, encUnary_apply, List.length_replicate,
        show (encUnit ()).length = 0 from rfl]
      omega
    calc query.fn.val.q
        ≤ c * ((encPair encUnary encUnit (k, ())).length + 1) ^ d := by omega
      _ ≤ P k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h₄ _)
  have hsmall : PolynomiallyBounded fun k => 8 * P k :=
    polynomiallyBounded_iff_le.mpr ⟨8 * c * 4 ^ d, d, fun k =>
      le_of_eq (by simp only [P, mul_pow]; ring)⟩
  have hev : ∀ᶠ k in atTop, 8 * P k ≤ 2 ^ k :=
    hsmall.eventually_lt_two_pow.mono fun _ hk => hk.le
  have hneg := h.negligible_advantage (isOraclePPT_prvSimReduction h.polyTime hB)
    (isTweakUnique_prvSimReduction hash B)
  refine negligible_of_eventually_le hneg ?_
  filter_upwards [hev] with k hk
  rw [prvSimAdvantage_simWord_eq hash B k fun query state hmem _ =>
    (Nat.mul_le_mul_left 8 (hP k query state hmem)).trans hk]

/-- This is this library's own theorem under [ZahurRosulekEvans2015] Definition 1, in the form
`CircularCorrelationRobust` states; it is not [ChoiKatzKumaresanZhou2012] Theorem 3 (dual-key
Definition 4 together with 2PC) and not [KolesnikovSchneider2008] in the random-oracle model
(obliviousness is not treated here, and simulation privacy does not use validity).

**Free-XOR garbling is `prv.sim` secure with a universal simulator over `phiXor`**, for every
circular correlation robust hash family `hash`. -/
theorem CircularCorrelationRobust.prvSimUniversal_freeXOR (h : CircularCorrelationRobust hash) :
    (FreeXOR.scheme hash).PrvSimSecureUniversal FreeXOR.phiXor encValidCircuit encXorTopology :=
  ⟨simWord hash, isPPTOn_simWord h.polyTime,
    fun _ _ _ hB => h.negligible_prvSimAdvantage_freeXOR hB⟩

/-- This is this library's own theorem under [ZahurRosulekEvans2015] Definition 1, in the form
`CircularCorrelationRobust` states; it is not [ChoiKatzKumaresanZhou2012] Theorem 3 (dual-key
Definition 4 together with 2PC) and not [KolesnikovSchneider2008] in the random-oracle model
(obliviousness is not treated here, and simulation privacy does not use validity).

**Free-XOR garbling is `prv.sim` secure with the side information `phiXor`**, for every
circular correlation robust hash family `hash`: for every uniform strict PPT adversary there is a
PPT simulator, on `(1^k, y, φ)` with circuits encoded by `encValidCircuit` and side information by
`encXorTopology`, whose advantage is negligible. The simulator `simWord hash` is the same for every
adversary (`CircularCorrelationRobust.negligible_prvSimAdvantage_freeXOR`). -/
theorem CircularCorrelationRobust.prvSim_freeXOR (h : CircularCorrelationRobust hash) :
    (FreeXOR.scheme hash).PrvSimSecure FreeXOR.phiXor encValidCircuit encXorTopology :=
  (h.prvSimUniversal_freeXOR).prvSimSecure

end Cslib.Crypto
