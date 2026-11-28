/-
Copyright (c) 2026 Uladzislau Artsemyeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uladzislau Artsemyeu
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.CutProgram
import CslibFrontier.Foundations.Combinatorics.DepthReduction
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# Valiant depth reduction for bounded-fan-in programs

Specializes `Cslib.IsGrading.exists_sdiff`
(`CslibFrontier.Foundations.Combinatorics.DepthReduction`)
[Valiant1977; Jukna2012, Lemma 1.4; AroraBarak09, Lemma 13.14; Lokam2009, Lemma 2.2]
to
arbitrary bounded-fan-in straight-line programs `p : Program σ n g` (`p.FanInAtMost r`). For any
`t ≤ k` and `p.depth < 2 ^ k`, cutting at most `r * t * g / k` gates leaves every wire with
residual gate depth at most `2 ^ (k - t)` (`Program.valiantDepthReduction`), and turning those
cut gates into extra inputs produces a fan-in-preserving cut program of depth at most `2 ^ (k - t)`
with the exact same wire trace (`Program.exists_cutProgram`, `Program.exists_depthReduced_program`).

## Main results

* `Cslib.Circuits.Program.valiantDepthReduction`: cuts at most `r * t * g / k` gates so every wire
  has residual depth at most `2 ^ (k - t)`.
* `Cslib.Circuits.Program.exists_depthReduced_program`: combines `valiantDepthReduction` and
  `exists_cutProgram` into a fan-in-preserving program of depth at most `2 ^ (k - t)` on `m` extra
  cut-gate inputs (`m ≤ r * t * g / k`).

## References

* [L. G. Valiant, *Graph-Theoretic Arguments in Low-Level Complexity*][Valiant1977]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [S. V. Lokam, *Complexity Lower Bounds using Linear Algebra*][Lokam2009]
-/

public section

namespace Cslib.Circuits

section ValiantReduction

variable {σ : Signature} {n g : ℕ}

/-- **Valiant Depth-Reduction Lemma** ([Valiant1977]; [Jukna2012, Lemma 1.4];
[AroraBarak09, Lemma 13.14]; [Lokam2009, Lemma 2.2]), specialized from
`Cslib.IsGrading.exists_sdiff`
to bounded-fan-in straight-line programs: for `t ≤ k` and `p.depth < 2 ^ k`, cutting at most
`r * t * g / k` gates makes every wire's residual gate depth at most `2 ^ (k - t)`. -/
theorem Program.valiantDepthReduction (p : Program σ n g) {r k t : ℕ}
    (hr : p.FanInAtMost r) (ht : t ≤ k) (hdepth : p.depth < 2 ^ k) :
    ∃ cut : Finset (Fin g),
      cut.card ≤ r * t * g / k ∧
      ∀ w : Wire n g, p.residualWireDepths cut w ≤ 2 ^ (k - t) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · obtain rfl : t = 0 := Nat.eq_zero_of_le_zero ht
    refine ⟨∅, by simp, fun w => ?_⟩
    rw [p.residualWireDepths_empty, Nat.sub_zero, pow_zero]
    have hlt := (p.wireDepths_le_depth w).trans_lt hdepth
    omega
  · let E : Finset (Wire n g × Wire n g) :=
      Finset.univ.biUnion fun j : Fin g =>
        Finset.univ.image fun a => ((p.lines j).wires a, Wire.gate j)
    have hEcard : E.card ≤ r * g := by
      calc E.card
          ≤ ∑ j : Fin g, (Finset.univ.image fun a =>
              ((p.lines j).wires a, (Wire.gate j : Wire n g))).card := Finset.card_biUnion_le
        _ ≤ ∑ _j : Fin g, r := Finset.sum_le_sum fun j _ =>
            Finset.card_image_le.trans ((Finset.card_univ.trans (Fintype.card_fin _)).trans_le
              (Program.fanInAtMost_iff.1 hr j))
        _ = r * g := by simp [mul_comm]
    have hgrade : Cslib.IsGrading E (2 ^ k) p.wireDepths := by
      refine ⟨fun w => (p.wireDepths_le_depth w).trans_lt hdepth, fun e he => ?_⟩
      simp only [E, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at he
      obtain ⟨j, a, -, rfl⟩ := he
      exact p.wireDepths_lines_lt j a
    obtain ⟨F, -, hFcard, g', hg'⟩ := hgrade.exists_sdiff ht
    let cut : Finset (Fin g) := Finset.univ.filter fun j : Fin g => Wire.gate j ∈ F.image Prod.snd
    have hcutF : cut.card ≤ F.card := by
      have hInj : cut.card ≤ (F.image Prod.snd).card := by
        apply Finset.card_le_card_of_injOn Wire.gate
        · intro j hj
          exact (Finset.mem_filter.1 hj).2
        · intro j₁ _ j₂ _ h
          exact Wire.gate.inj h
      exact hInj.trans Finset.card_image_le
    refine ⟨cut, ?_, fun w => ?_⟩
    · rw [Nat.le_div_iff_mul_le hk]
      calc cut.card * k
          ≤ F.card * k := Nat.mul_le_mul_right k hcutF
        _ = k * F.card := mul_comm _ _
        _ ≤ t * E.card := hFcard
        _ ≤ t * (r * g) := Nat.mul_le_mul_left t hEcard
        _ = r * t * g := by ring
    · have hResLe : ∀ u : Wire n g, p.residualWireDepths cut u ≤ g' u + 1 := by
        intro u
        refine p.wire_induction (P := fun u => p.residualWireDepths cut u ≤ g' u + 1)
          (fun _ => by simp) (fun j ih => ?_) u
        rw [p.residualWireDepths_gate]
        by_cases hj : j ∈ cut
        · simp [hj]
        · rw [ite_eq_right hj, Line.depth_le_add_one_iff]
          intro a
          have hmem : ((p.lines j).wires a, Wire.gate j) ∈ E :=
            Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _,
              Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩⟩
          have hnotF : ((p.lines j).wires a, Wire.gate j) ∉ F := fun hF =>
            hj (Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.mem_image.2 ⟨_, hF, rfl⟩⟩)
          have hlt := hg'.2 _ (Finset.mem_sdiff.2 ⟨hmem, hnotF⟩)
          dsimp only at hlt
          have := ih a
          omega
      have hg'lt := hg'.1 w
      have := hResLe w
      omega

/-- Every bounded-fan-in program `p` of depth `< 2 ^ k` admits `m ≤ r * t * g / k` cut gates
whose replacement by extra inputs yields a `FanInAtMost r` program of depth at most `2 ^ (k - t)`
computing the same wire trace. -/
theorem Program.exists_depthReduced_program (p : Program σ n g) {r k t : ℕ}
    (hr : p.FanInAtMost r) (ht : t ≤ k) (hdepth : p.depth < 2 ^ k) :
    ∃ (m : ℕ) (q : Program σ (n + m) (g - m))
      (wireMap : Wire n g → Wire (n + m) (g - m)) (cutGate : Fin m → Fin g),
      m ≤ r * t * g / k ∧
      q.FanInAtMost r ∧
      q.depth ≤ 2 ^ (k - t) ∧
      (∀ {U : Type*} (I : Interpretation σ U) (x : Fin n → U) (w : Wire n g),
        q.trace I (Fin.append x (fun i => p.eval I x (cutGate i))) (wireMap w) =
          p.trace I x w) := by
  obtain ⟨cut, hCard, hRes⟩ := p.valiantDepthReduction hr ht hdepth
  obtain ⟨q, wireMap, cutGate, _, hFan, hDepth, hSurj, hTrace⟩ := p.exists_cutProgram cut
  refine ⟨cut.card, q, wireMap, cutGate, hCard, hFan r hr, ?_, hTrace⟩
  rw [Program.depth_le_iff]
  intro k'
  obtain ⟨j, hj⟩ := hSurj k'
  rw [← Program.wireDepths_gateWire, ← hj, hDepth]
  exact hRes (.gate j)

end ValiantReduction

end Cslib.Circuits
