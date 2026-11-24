/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Prefix.ConsistentTree
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.NumberTheory.Real.GoldenRatio
-- `import all`: reads private DAG decomposition helpers (`programWord`, `ancMul`, `stripId`,
-- `leftSpine`, `universal_mul_sets`) from `Basic` and private recurrence/synthesis helpers
-- (`sum_Ico_one_succ_shift`, `diagSum_recurrence`, `exists_rippleOptimalPrefixCircuit`) from
-- `ConsistentTree`.
import all CslibFrontier.Computability.Circuit.Prefix.Basic
import all CslibFrontier.Computability.Circuit.Prefix.ConsistentTree
import CslibFrontier.Computability.Circuit.Basic
import CslibFrontier.Computability.Circuit.FanIn
import CslibFrontier.Computability.Circuit.Program
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# Minimal depth of optimal fanout-bounded prefix circuits

Following Sergeev [Sergeev2025PrefixDepth], we complete the depth characterization of optimal
(zero-deficiency) fanout-`k` universal prefix circuits. Extracting principal-chain segments directly
from any zero-deficiency universal prefix DAG yields sharp `k = 2` width bounds
(`width_le_one_add_maxCircuitWidthUpper_two`, `width_le_maxCircuitWidthUpper_two`) and general
exponential circuit width upper bounds (`width_le_mul_alphaRoot_pow`) in terms of the unique
positive root `α_k` (`alphaRoot k`) of the characteristic polynomial
`P_k(x) = 2 + x + ⋯ + x^{k-2} - x^k` (`prefixCharPoly k`).

Combining these upper bounds with the constructive lower bounds of
`CslibFrontier.Computability.Circuit.Prefix.ConsistentTree`, we establish that for each fanout bound
`k ≥ 2`, there exists a constant `C ≥ 0` (depending on `k`) such that for every input width
`N ≥ 1`, the minimal depth `D(N, k)` (`optimalPrefixDepth N k`) of an optimal fanout-`k` universal
prefix circuit on `N` inputs satisfies
`|(optimalPrefixDepth N k : ℝ) - Real.logb (alphaRoot k) N| ≤ C`
(`abs_optimalPrefixDepth_sub_logb_le`), together with the exact `k = 2` threshold characterization
(`optimalPrefixDepth_two_le_iff`), strict monotonicity of `α_k` on `k ≥ 2`
(`alphaRoot_strictMonoOn`), and convergence `α_k → φ` (`tendsto_alphaRoot_atTop`).

## Main definitions

* `Cslib.Circuits.Prefix.prefixCharPoly`, `Cslib.Circuits.Prefix.alphaRoot`: characteristic
  polynomial `P_k(x)` and its unique positive root `α_k`.
* `Cslib.Circuits.Prefix.optimalPrefixDepth`: minimal depth `D(N, k)` of an optimal fanout-`k`
  universal prefix circuit on `N` inputs.

## Main results

* `Cslib.Circuits.Prefix.width_le_one_add_maxCircuitWidthUpper_two`,
  `Cslib.Circuits.Prefix.width_le_maxCircuitWidthUpper_two`,
  `Cslib.Circuits.Prefix.width_le_mul_alphaRoot_pow`: sharp `k = 2` and general exponential width
  upper bounds for optimal fanout-`k` universal prefix circuits.
* `Cslib.Circuits.Prefix.prefixCharPoly_alphaRoot`,
  `Cslib.Circuits.Prefix.eq_alphaRoot_of_pos_of_prefixCharPoly_eq_zero`,
  `Cslib.Circuits.Prefix.one_lt_alphaRoot`,
  `Cslib.Circuits.Prefix.alphaRoot_lt_goldenRatio`,
  `Cslib.Circuits.Prefix.three_halves_lt_alphaRoot`,
  `Cslib.Circuits.Prefix.alphaRoot_two`,
  `Cslib.Circuits.Prefix.alphaRoot_strictMonoOn`,
  `Cslib.Circuits.Prefix.tendsto_alphaRoot_atTop`: existence, uniqueness, enclosure, `k = 2` value
  `√2`, strict monotonicity, and convergence `α_k → φ` of `α_k`.
* `Cslib.Circuits.Prefix.exists_optimalPrefixCircuit_depth_eq`,
  `Cslib.Circuits.Prefix.optimalPrefixDepth_one`,
  `Cslib.Circuits.Prefix.optimalPrefixDepth_two_le_iff`,
  `Cslib.Circuits.Prefix.abs_optimalPrefixDepth_sub_logb_le`: attainment of `D(N, k)`, `N = 1`
  base case, exact `k = 2` threshold characterization, and main theorem
  `D(N, k) = log_{α_k} N ± O(1)`.

## References

* [I. S. Sergeev, *A Note on the Depth of Optimal Fanout-Bounded Prefix
  Circuits*][Sergeev2025PrefixDepth]
-/

public section

namespace Cslib.Circuits.Prefix

private inductive IntervalTree : ℕ → ℕ → Type
  | leaf (a : ℕ) : IntervalTree a (a + 1)
  | node {a m b : ℕ} (left : IntervalTree a m) (right : IntervalTree m b) : IntervalTree a b

private theorem IntervalTree.lt {a b : ℕ} (t : IntervalTree a b) : a < b := by
  induction t with
  | leaf a => exact Nat.lt_succ_self a
  | node _ _ ihL ihR => exact ihL.trans ihR

private def IntervalTree.depth : {a b : ℕ} → IntervalTree a b → ℕ
  | _, _, .leaf _ => 0
  | _, _, .node L R => max L.depth R.depth + 1

private def IntervalTree.intervals : {a b : ℕ} → IntervalTree a b → Finset (ℕ × ℕ)
  | _, _, .leaf a => {(a, a + 1)}
  | a, b, .node L R => insert (a, b) (L.intervals ∪ R.intervals)

private theorem IntervalTree.width_le_two_pow {a b : ℕ} (t : IntervalTree a b) :
    b - a ≤ 2 ^ t.depth := by
  induction t with
  | leaf a => simp only [IntervalTree.depth, pow_zero, Nat.add_sub_cancel_left, le_rfl]
  | node L R ihL ihR =>
    have hL := L.lt
    have hR := R.lt
    have hpowL : 2 ^ L.depth ≤ 2 ^ max L.depth R.depth :=
      Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _)
    have hpowR : 2 ^ R.depth ≤ 2 ^ max L.depth R.depth :=
      Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _)
    simp only [IntervalTree.depth, Nat.pow_succ]
    omega

/-! #### Zero-deficiency DAG segment extraction and upper bounds -/

private theorem range'_eq_range'_iff {a₁ len₁ a₂ len₂ : ℕ} (h1 : 1 ≤ len₁)
    (heq : List.range' a₁ len₁ = List.range' a₂ len₂) : a₁ = a₂ ∧ len₁ = len₂ := by
  have hlen : len₁ = len₂ := by
    have := congrArg List.length heq
    simpa only [List.length_range'] using this
  subst hlen
  obtain ⟨m, rfl⟩ : ∃ m, len₁ = m + 1 := ⟨len₁ - 1, by omega⟩
  simp only [List.range'_succ, List.cons.injEq] at heq
  exact ⟨heq.1, rfl⟩

private theorem IntervalTree.mem_intervals_bounds {a b : ℕ} (t : IntervalTree a b) :
    ∀ {p q : ℕ}, (p, q) ∈ t.intervals → a ≤ p ∧ p < q ∧ q ≤ b := by
  induction t with
  | leaf a =>
    intro p q hpq
    simp only [IntervalTree.intervals, Finset.mem_singleton, Prod.mk.injEq] at hpq
    omega
  | node L R ihL ihR =>
    intro p q hpq
    have hL := L.lt
    have hR := R.lt
    simp only [IntervalTree.intervals, Finset.mem_insert, Finset.mem_union, Prod.mk.injEq] at hpq
    rcases hpq with ⟨rfl, rfl⟩ | hpL | hpR
    · exact ⟨le_rfl, hL.trans hR, le_rfl⟩
    · obtain ⟨h1, h2, h3⟩ := ihL hpL
      exact ⟨h1, h2, by omega⟩
    · obtain ⟨h1, h2, h3⟩ := ihR hpR
      exact ⟨by omega, h2, h3⟩

private theorem IntervalTree.unit_mem_intervals {a b : ℕ} (t : IntervalTree a b) :
    ∀ p, a ≤ p → p < b → (p, p + 1) ∈ t.intervals := by
  induction t with
  | leaf a =>
    intro p hp1 hp2
    have hpeq : p = a := by omega
    rw [hpeq]
    simp only [IntervalTree.intervals, Finset.mem_singleton]
  | @node _ m _ L R ihL ihR =>
    intro p hp1 hp2
    simp only [IntervalTree.intervals, Finset.mem_insert, Finset.mem_union]
    by_cases hpm : p < m
    · exact Or.inr (Or.inl (ihL p hp1 hpm))
    · exact Or.inr (Or.inr (ihR p (by omega) hp2))

private theorem IntervalTree.erase_root_eq_union {a m b : ℕ} (L : IntervalTree a m)
    (R : IntervalTree m b) :
    (IntervalTree.node L R).intervals.erase (a, b) = L.intervals ∪ R.intervals := by
  have hL := L.lt
  have hR := R.lt
  have hnot : (a, b) ∉ L.intervals ∪ R.intervals := by
    rw [Finset.mem_union]
    rintro (h1 | h2)
    · have := L.mem_intervals_bounds h1; omega
    · have := R.mem_intervals_bounds h2; omega
  simp only [IntervalTree.intervals, Finset.erase_insert hnot]

private theorem IntervalTree.suffixOfLeftPrefix {a b : ℕ} (t : IntervalTree a b) :
    ∀ s, (a, s) ∈ t.intervals.erase (a, b) →
      a < s ∧ s < b ∧
        ∃ J : IntervalTree s b,
          J.depth ≤ t.depth ∧
          ∀ p q, (p, q) ∈ t.intervals.erase (a, b) → s ≤ p → (p, q) ∈ J.intervals := by
  induction t with
  | leaf a =>
    intro s hs
    simp only [IntervalTree.intervals, Finset.erase_singleton, Finset.notMem_empty] at hs
  | @node a m b L R ihL _ =>
    intro s hs
    have hL := L.lt
    have hR := R.lt
    rw [IntervalTree.erase_root_eq_union, Finset.mem_union] at hs
    have hsL : (a, s) ∈ L.intervals := by
      rcases hs with hsL | hsR
      · exact hsL
      · have := R.mem_intervals_bounds hsR; omega
    have hbds := L.mem_intervals_bounds hsL
    by_cases hsm : s = m
    · rw [hsm]
      refine ⟨hL, hR, R, by simp only [IntervalTree.depth]; omega, ?_⟩
      intro p q hpq hmp
      rw [IntervalTree.erase_root_eq_union, Finset.mem_union] at hpq
      rcases hpq with hpL | hpR
      · have := L.mem_intervals_bounds hpL; omega
      · exact hpR
    · have hsL_er : (a, s) ∈ L.intervals.erase (a, m) := by
        refine Finset.mem_erase.mpr ⟨?_, hsL⟩
        intro heq
        rw [Prod.mk.injEq] at heq
        exact hsm heq.2
      obtain ⟨has, _, JL, hJL_d, hJL_sub⟩ := ihL s hsL_er
      refine ⟨has, by omega, .node JL R, ?_, ?_⟩
      · simp only [IntervalTree.depth]
        omega
      · intro p q hpq hsp
        rw [IntervalTree.erase_root_eq_union, Finset.mem_union] at hpq
        simp only [IntervalTree.intervals, Finset.mem_insert, Finset.mem_union]
        rcases hpq with hpL | hpR
        · have hpL_er : (p, q) ∈ L.intervals.erase (a, m) := by
            refine Finset.mem_erase.mpr ⟨?_, hpL⟩
            intro heq
            rw [Prod.mk.injEq] at heq
            omega
          exact Or.inr (Or.inl (hJL_sub p q hpL_er hsp))
        · exact Or.inr (Or.inr hpR)

private theorem exists_wireIntervalTree {N g : ℕ} (p : Program prefixSignature N g)
    (w : Wire N g) :
    ∀ a b : ℕ, a < b → programWord p w = List.range' a (b - a) →
      ∃ I : IntervalTree a b,
        I.depth ≤ p.wireDepths w ∧
        ∀ j ∈ ancMul p w, ∀ p₀ q₀, p₀ < q₀ →
          programWord p (.gate j) = List.range' p₀ (q₀ - p₀) → (p₀, q₀) ∈ I.intervals := by
  refine prefix_wire_induction p
    (fun i a b hab hw => ?_)
    (fun k wires hline ih0 a b hab hw => ?_)
    (fun k wires hline ih0 ih1 a b hab hw => ?_) w
  · rw [programWord_input] at hw
    have hlen : b - a = 1 := by
      have := congrArg List.length hw
      simpa only [List.length_singleton, List.length_range'] using this.symm
    obtain rfl : b = a + 1 := by omega
    refine ⟨.leaf a, Nat.zero_le _, fun j hj => ?_⟩
    rw [ancMul_input] at hj
    exact absurd hj (Finset.notMem_empty j)
  · rw [programWord_gate_id p k wires hline] at hw
    obtain ⟨I, hd, hanc⟩ := ih0 a b hab hw
    refine ⟨I, ?_, ?_⟩
    · rw [wireDepths_gate_id p k wires hline]; omega
    · rw [ancMul_gate_id p k wires hline]; exact hanc
  · have hw_orig := hw
    rw [programWord_gate_mul p k wires hline] at hw
    obtain ⟨hm1, hm2, hw0, hw1⟩ := range_split_of_append
      (programWord_ne_nil p (wires 0)) (programWord_ne_nil p (wires 1)) hw
    set len0 := (programWord p (wires 0)).length
    set m := a + len0
    obtain ⟨IL, hdL, hancL⟩ :=
      ih0 a m (by omega) (by simpa only [m, Nat.add_sub_cancel_left] using hw0)
    obtain ⟨IR, hdR, hancR⟩ := ih1 m b (by omega) (by
      have hbm : b - m = b - a - len0 := by omega
      rw [hbm]
      exact hw1)
    refine ⟨.node IL IR, ?_, ?_⟩
    · rw [wireDepths_gate_mul p k wires hline]
      simp only [IntervalTree.depth]
      omega
    · intro j hj p₀ q₀ hpq hjw
      rw [ancMul_gate_mul p k wires hline, Finset.mem_insert, Finset.mem_union] at hj
      simp only [IntervalTree.intervals, Finset.mem_insert, Finset.mem_union]
      rcases hj with rfl | hj0 | hj1
      · obtain ⟨rfl, hlen⟩ := range'_eq_range'_iff (by omega) (hjw.symm.trans hw_orig)
        exact Or.inl (Prod.ext rfl (by omega))
      · exact Or.inr (Or.inl (hancL j hj0 p₀ q₀ hpq hjw))
      · exact Or.inr (Or.inr (hancR j hj1 p₀ q₀ hpq hjw))

private theorem spine_decomposition {N g : ℕ} (p : Program prefixSignature N g) (hN : 1 ≤ N) :
    ∀ (w : Wire N g) (M : ℕ), 1 ≤ M →
      programWord p w = List.range' 0 M →
      (leftSpine p w).length = p.wireDepths w →
      ∃ (v : ℕ → Wire N g) (u : ℕ → Wire N g) (T : ℕ → ℕ),
        v 0 = .input ⟨0, hN⟩ ∧
        T 0 = 1 ∧
        v (p.wireDepths w) = w ∧
        T (p.wireDepths w) = M ∧
        (∀ d < p.wireDepths w,
          T d < T (d + 1) ∧
          (∃ sg : Fin g,
            (leftSpine p w)[d]? = some sg ∧
            v (d + 1) = .gate sg ∧
            ∃ wires : Fin 2 → Wire N g,
              p.lines sg = ⟨.mul, wires⟩ ∧ wires 0 = v d ∧ wires 1 = u d) ∧
          p.wireDepths (v d) = d ∧
          p.wireDepths (u d) ≤ d ∧
          programWord p (v d) = List.range' 0 (T d) ∧
          programWord p (u d) = List.range' (T d) (T (d + 1) - T d)) ∧
        (∀ j ∈ ancMul p w,
          j ∈ leftSpine p w ∨ ∃ d < p.wireDepths w, j ∈ ancMul p (u d)) := by
  intro w
  refine prefix_wire_induction p
    (fun i M _ hw _ => ?_)
    (fun k wires hline _ M _ _ hlen => ?_)
    (fun k wires hline ih0 _ M _ hw hlen => ?_) w
  · rw [programWord_input] at hw
    have hM1 : M = 1 := by
      have := congrArg List.length hw
      simpa only [List.length_singleton, List.length_range'] using this.symm
    subst hM1
    simp only [List.range'_one, List.cons.injEq, and_true] at hw
    have hi0 : i = ⟨0, hN⟩ := Fin.ext hw
    subst hi0
    refine ⟨fun _ => .input ⟨0, hN⟩, fun _ => .input ⟨0, hN⟩, fun _ => 1,
      rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro d hd
      simp only [Program.wireDepths_input] at hd
      omega
    · intro j hj
      rw [ancMul_input] at hj
      exact absurd hj (Finset.notMem_empty j)
  · rw [leftSpine_gate_id p k wires hline, wireDepths_gate_id p k wires hline] at hlen
    have hle := leftSpine_length_le_wireDepths p (wires 0)
    omega
  · rw [leftSpine_gate_mul p k wires hline, List.length_append, List.length_singleton,
      wireDepths_gate_mul p k wires hline] at hlen
    have hle0 := leftSpine_length_le_wireDepths p (wires 0)
    have hlen0 : (leftSpine p (wires 0)).length = p.wireDepths (wires 0) := by omega
    have hd1_le : p.wireDepths (wires 1) ≤ p.wireDepths (wires 0) := by omega
    have hdepth_gate : p.wireDepths (.gate k) = p.wireDepths (wires 0) + 1 := by
      rw [wireDepths_gate_mul p k wires hline]; omega
    rw [programWord_gate_mul p k wires hline] at hw
    obtain ⟨hm1, hm2, hw0, hw1⟩ := range_split_of_append
      (programWord_ne_nil p (wires 0)) (programWord_ne_nil p (wires 1)) hw
    set M₀ := (programWord p (wires 0)).length
    set D₀ := p.wireDepths (wires 0)
    obtain ⟨v₀, u₀, T₀, hv0, hT0, hvD0, hTD0, hseg0, hanc0⟩ := ih0 M₀ (by omega) hw0 hlen0
    let v : ℕ → Wire N g := fun d => if d = D₀ + 1 then .gate k else v₀ d
    let u : ℕ → Wire N g := fun d => if d = D₀ then wires 1 else u₀ d
    let T : ℕ → ℕ := fun d => if d = D₀ + 1 then M else T₀ d
    refine ⟨v, u, T, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [v, Nat.zero_ne_add_one, ↓reduceIte, hv0]
    · simp only [T, Nat.zero_ne_add_one, ↓reduceIte, hT0]
    · simp only [v, hdepth_gate, ↓reduceIte]
    · simp only [T, hdepth_gate, ↓reduceIte]
    · intro d hd
      rw [hdepth_gate] at hd
      by_cases hd_eq : d = D₀
      · subst hd_eq
        have hsg : (leftSpine p (.gate k))[D₀]? = some k := by
          simp only [leftSpine_gate_mul p k wires hline,
            List.getElem?_append_right (by rw [hlen0]), hlen0, Nat.sub_self,
            List.getElem?_cons_zero]
        have hv_D0 : v D₀ = wires 0 := by
          simp only [v, show D₀ ≠ D₀ + 1 by omega, ↓reduceIte, hvD0]
        have hv_succ : v (D₀ + 1) = .gate k := by simp only [v, ↓reduceIte]
        have hu_D0 : u D₀ = wires 1 := by simp only [u, ↓reduceIte]
        have hT_D0 : T D₀ = M₀ := by
          simp only [T, show D₀ ≠ D₀ + 1 by omega, ↓reduceIte, hTD0]
        have hT_succ : T (D₀ + 1) = M := by simp only [T, ↓reduceIte]
        refine ⟨by omega, ⟨k, hsg, hv_succ, wires, hline, hv_D0.symm, hu_D0.symm⟩, ?_, ?_, ?_, ?_⟩
        · rw [hv_D0]
        · rw [hu_D0]; exact hd1_le
        · rw [hv_D0, hT_D0]; exact hw0
        · rw [hu_D0, hT_D0, hT_succ]; simpa only [Nat.zero_add] using hw1
      · have hd_lt : d < D₀ := by omega
        obtain ⟨hTd_lt, ⟨sg₀, hsg₀, hvd_succ, hwires_d⟩, hvd_d, hud_d, hvd_w, hud_w⟩ :=
          hseg0 d hd_lt
        have hsg : (leftSpine p (.gate k))[d]? = some sg₀ := by
          rw [leftSpine_gate_mul p k wires hline,
            List.getElem?_append_left (by rw [hlen0]; exact hd_lt)]
          exact hsg₀
        have hv_d : v d = v₀ d := by simp only [v, show d ≠ D₀ + 1 by omega, ↓reduceIte]
        have hv_s : v (d + 1) = v₀ (d + 1) := by
          simp only [v, show d + 1 ≠ D₀ + 1 by omega, ↓reduceIte]
        have hu_d : u d = u₀ d := by simp only [u, hd_eq, ↓reduceIte]
        have hT_d : T d = T₀ d := by simp only [T, show d ≠ D₀ + 1 by omega, ↓reduceIte]
        have hT_s : T (d + 1) = T₀ (d + 1) := by
          simp only [T, show d + 1 ≠ D₀ + 1 by omega, ↓reduceIte]
        refine ⟨by omega, ⟨sg₀, hsg, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
        · rw [hv_s]; exact hvd_succ
        · rw [hv_d, hu_d]; exact hwires_d
        · rw [hv_d]; exact hvd_d
        · rw [hu_d]; exact hud_d
        · rw [hv_d, hT_d]; exact hvd_w
        · rw [hu_d, hT_d, hT_s]; exact hud_w
    · intro j hj
      rw [ancMul_gate_mul p k wires hline, Finset.mem_insert, Finset.mem_union] at hj
      rw [leftSpine_gate_mul p k wires hline, List.mem_append, List.mem_singleton, hdepth_gate]
      rcases hj with rfl | hj0 | hj1
      · exact Or.inl (Or.inr rfl)
      · rcases hanc0 j hj0 with hsp | ⟨d, hd, hju⟩
        · exact Or.inl (Or.inl hsp)
        · refine Or.inr ⟨d, by omega, ?_⟩
          simpa only [u, show d ≠ D₀ by omega, ↓reduceIte] using hju
      · refine Or.inr ⟨D₀, by omega, ?_⟩
        simpa only [u, ↓reduceIte] using hj1

private def firstInput {N g : ℕ} (l : Line prefixSignature N g) : Wire N g :=
  match l with
  | ⟨.id, wires⟩ => wires 0
  | ⟨.mul, wires⟩ => wires 0

private theorem rank_firstInput_lt {N g : ℕ} (p : Program prefixSignature N g) (k : Fin g) :
    (firstInput (p.lines k)).rank < (Wire.gate k : Wire N g).rank := by
  cases h : p.lines k with
  | mk op wires =>
    cases op
    · exact rank_lt_of_lines_eq p k h 0
    · exact rank_lt_of_lines_eq p k h 0

private theorem wireDepths_firstInput_lt {N g : ℕ} (p : Program prefixSignature N g) (k : Fin g) :
    p.wireDepths (firstInput (p.lines k)) + 1 ≤ p.wireDepths (.gate k) := by
  cases h : p.lines k with
  | mk op wires =>
    cases op
    · rw [wireDepths_gate_mul p k wires h]
      simp only [firstInput]
      omega
    · rw [wireDepths_gate_id p k wires h]
      simp only [firstInput]
      omega

private def firstSlotOfGate {N m : ℕ} (c : Circuit prefixSignature N m) (k : Fin c.size) :
    c.Slot :=
  ⟨k, match _h : (c.program.lines k).op with
    | .mul => 0
    | .id => 0⟩

private theorem slotWire_firstSlotOfGate {N m : ℕ} (c : Circuit prefixSignature N m)
    (k : Fin c.size) : c.slotWire (firstSlotOfGate c k) = firstInput (c.program.lines k) := by
  unfold firstSlotOfGate Circuit.slotWire firstInput
  dsimp only
  cases h : c.program.lines k with
  | mk op wires =>
    cases op <;> rfl

private theorem firstSlotOfGate_injective {N m : ℕ} (c : Circuit prefixSignature N m) :
    Function.Injective (firstSlotOfGate c) := by
  intro k₁ k₂ h
  exact congrArg Sigma.fst h

private inductive GenPrefixTree : Type
  | node (state : ℕ) (hasOut : Bool) (r : ℕ) (isMul : Fin r → Bool)
      (child : Fin r → GenPrefixTree) : GenPrefixTree

private def GenPrefixTree.state : GenPrefixTree → ℕ
  | .node s _ _ _ _ => s

private def GenPrefixTree.rootBudget : GenPrefixTree → ℕ
  | .node _ hasOut r _ _ => r + if hasOut then 1 else 0

private def GenPrefixTree.rootArity : GenPrefixTree → ℕ
  | .node _ _ r _ _ => r

private def GenPrefixTree.depth : GenPrefixTree → ℕ
  | .node _ _ r _ child => Finset.univ.sup fun i : Fin r => (child i).depth + 1

private def GenPrefixTree.FanoutAtMost (k : ℕ) : GenPrefixTree → Prop
  | .node _ hasOut r _ child =>
      r + (if hasOut then 1 else 0) ≤ k ∧ ∀ i : Fin r, (child i).FanoutAtMost k

private def GenPrefixTree.MaxStateLt (b : ℕ) : GenPrefixTree → Prop
  | .node s _ r _ child => s < b ∧ ∀ i : Fin r, (child i).MaxStateLt b

private def GenPrefixTree.Valid (iv : Finset (ℕ × ℕ)) : GenPrefixTree → Prop
  | .node s _ r isMul child =>
      (∀ i : Fin r,
        if isMul i then s < (child i).state ∧ (s, (child i).state) ∈ iv
        else (child i).state = s) ∧
        ∀ i : Fin r, (child i).Valid iv

private def GenPrefixTree.outCount : GenPrefixTree → ℕ
  | .node _ hasOut r _ child => (if hasOut then 1 else 0) + ∑ i : Fin r, (child i).outCount

private def GenPrefixTree.outAt (s : ℕ) : GenPrefixTree → ℕ
  | .node st hasOut r _ child =>
      (if hasOut ∧ st = s then 1 else 0) + ∑ i : Fin r, (child i).outAt s

private def GenPrefixTree.mulCount (m : ℕ) : GenPrefixTree → ℕ
  | .node _ _ r isMul child =>
      ∑ i : Fin r,
        ((if isMul i ∧ (child i).state = m then 1 else 0) + (child i).mulCount m)

private theorem GenPrefixTree.child_depth_lt {st : ℕ} {hasOut : Bool} {r : ℕ}
    {isMul : Fin r → Bool} {child : Fin r → GenPrefixTree} (i : Fin r) :
    (child i).depth + 1 ≤ (GenPrefixTree.node st hasOut r isMul child).depth :=
  Finset.le_sup (f := fun j : Fin r => (child j).depth + 1) (Finset.mem_univ i)

private theorem GenPrefixTree.outCount_le_two_pow :
    ∀ (t : GenPrefixTree), t.FanoutAtMost 2 → (∀ s, t.outAt s ≤ 1) →
      t.outCount ≤ 2 ^ t.depth
  | .node st hasOut r isMul child, hfan, hout => by
    obtain ⟨hr, hch_fan⟩ := hfan
    have hch_out : ∀ i : Fin r, ∀ s, (child i).outAt s ≤ 1 := by
      intro i s
      have hs := hout s
      simp only [GenPrefixTree.outAt] at hs
      have hle : (child i).outAt s ≤ ∑ j : Fin r, (child j).outAt s :=
        Finset.single_le_sum (f := fun j : Fin r => (child j).outAt s)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    by_cases hr0 : r = 0
    · subst hr0
      simp only [GenPrefixTree.outCount, Finset.univ_eq_empty, Finset.sum_empty]
      have h1 : 1 ≤ 2 ^ (GenPrefixTree.node st hasOut 0 isMul child).depth :=
        Nat.one_le_pow _ _ (by omega)
      cases hasOut <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
    · have hr_le2 : r ≤ 2 := by omega
      have hd_pos : 1 ≤ (GenPrefixTree.node st hasOut r isMul child).depth := by
        have := GenPrefixTree.child_depth_lt (child := child) (isMul := isMul)
          (st := st) (hasOut := hasOut) ⟨0, by omega⟩
        omega
      set H := (GenPrefixTree.node st hasOut r isMul child).depth - 1
      have hch_le : ∀ i : Fin r, (child i).outCount ≤ 2 ^ H := by
        intro i
        have h1 := GenPrefixTree.outCount_le_two_pow (child i) (hch_fan i) (hch_out i)
        have h2 := GenPrefixTree.child_depth_lt (st := st) (hasOut := hasOut) (isMul := isMul)
          (child := child) i
        exact h1.trans (Nat.pow_le_pow_right (by omega) (by omega))
      have hsum_le : ∑ i : Fin r, (child i).outCount ≤ r * 2 ^ H := by
        calc
          ∑ i : Fin r, (child i).outCount ≤ ∑ _i : Fin r, 2 ^ H :=
            Finset.sum_le_sum fun i _ => hch_le i
          _ = r * 2 ^ H := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      have hpow : 2 ^ (GenPrefixTree.node st hasOut r isMul child).depth = 2 * 2 ^ H := by
        rw [show (GenPrefixTree.node st hasOut r isMul child).depth = H + 1 by omega,
          Nat.pow_succ, Nat.mul_comm]
      have hH_pos : 1 ≤ 2 ^ H := Nat.one_le_pow _ _ (by omega)
      simp only [GenPrefixTree.outCount]
      rcases (show r = 1 ∨ r = 2 by omega) with rfl | rfl <;>
        (cases hasOut <;>
          simp only [Bool.false_eq_true, ↓reduceIte, Nat.one_mul] at hr hsum_le ⊢ <;>
          omega)

private def segHasOut {N : ℕ} (c : PrefixCircuit N) (a b : ℕ) (w : Wire N c.size) : Bool :=
  decide (∃ j : Fin N, a ≤ j.val + 1 ∧ j.val + 1 < b ∧ c.outputs j = w)

private def segActive {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (root w : Wire N c.size) : Bool :=
  segHasOut c a b w ||
    (List.finRange c.size).any fun g =>
      if _h : (Wire.gate g : Wire N c.size) ≠ root ∧
          firstInput (c.program.lines g) = w then
        segActive c a b root (.gate g)
      else
        false
termination_by c.size - w.rank
decreasing_by
  have hlt : w.rank < (Wire.gate g : Wire N c.size).rank := by
    rw [← _h.2]
    exact rank_firstInput_lt c.program g
  have hle := Wire.rank_le (Wire.gate g : Wire N c.size)
  omega

private def segChildren {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (root w : Wire N c.size) : List (Fin c.size) :=
  (List.finRange c.size).filter fun g =>
    decide ((Wire.gate g : Wire N c.size) ≠ root ∧ firstInput (c.program.lines g) = w) &&
      segActive c a b root (.gate g)

private theorem mem_segChildren_iff {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (root w : Wire N c.size) (g : Fin c.size) :
    g ∈ segChildren c a b root w ↔
      (Wire.gate g : Wire N c.size) ≠ root ∧
        firstInput (c.program.lines g) = w ∧
        segActive c a b root (.gate g) = true := by
  simp only [segChildren, List.mem_filter, List.mem_finRange, true_and, Bool.and_eq_true,
    decide_eq_true_eq, and_assoc]

private theorem segActive_iff {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (root w : Wire N c.size) :
    segActive c a b root w = true ↔
      segHasOut c a b w = true ∨ ∃ g, g ∈ segChildren c a b root w := by
  conv_lhs => unfold segActive
  simp only [Bool.or_eq_true, List.any_eq_true, List.mem_finRange, true_and, mem_segChildren_iff]
  refine or_congr_right ⟨?_, ?_⟩
  · rintro ⟨g, hg⟩
    split_ifs at hg with h
    · exact ⟨g, h.1, h.2, hg⟩
  · rintro ⟨g, h1, h2, h3⟩
    refine ⟨g, ?_⟩
    split_ifs with h
    · exact h3
    · exact absurd ⟨h1, h2⟩ h

private theorem segChildren_rank_lt {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (root w : Wire N c.size) (i : Fin (segChildren c a b root w).length) :
    w.rank < (Wire.gate (segChildren c a b root w)[i] : Wire N c.size).rank := by
  have hmem : (segChildren c a b root w)[i] ∈ segChildren c a b root w := List.getElem_mem _
  obtain ⟨_, hfi, _⟩ := (mem_segChildren_iff c a b root w _).mp hmem
  have hlt := rank_firstInput_lt c.program (segChildren c a b root w)[i]
  rw [hfi] at hlt
  exact hlt

private def wireState {N g : ℕ} (p : Program prefixSignature N g) (w : Wire N g) : ℕ :=
  (programWord p w).length

private def buildSegTree {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (root w : Wire N c.size) : GenPrefixTree :=
  GenPrefixTree.node
    (wireState c.program w)
    (segHasOut c a b w)
    (segChildren c a b root w).length
    (fun i => (c.program.lines (segChildren c a b root w)[i]).op == .mul)
    (fun i => buildSegTree c a b root (.gate (segChildren c a b root w)[i]))
termination_by c.size - w.rank
decreasing_by
  have hlt := segChildren_rank_lt c a b root w i
  have hle := Wire.rank_le (Wire.gate (segChildren c a b root w)[i] : Wire N c.size)
  omega

private theorem buildSegTree_eq {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (root w : Wire N c.size) :
    buildSegTree c a b root w =
      GenPrefixTree.node
        (wireState c.program w)
        (segHasOut c a b w)
        (segChildren c a b root w).length
        (fun i => (c.program.lines (segChildren c a b root w)[i]).op == .mul)
        (fun i => buildSegTree c a b root (.gate (segChildren c a b root w)[i])) := by
  rw [buildSegTree]

private inductive ReachesInSeg {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (root : Wire N c.size) : Wire N c.size → Wire N c.size → Prop
  | refl (u : Wire N c.size) : ReachesInSeg c a b root u u
  | step {z p : Wire N c.size} {g : Fin c.size} :
      g ∈ segChildren c a b root p →
      ReachesInSeg c a b root z p →
      ReachesInSeg c a b root z (.gate g)

private theorem ReachesInSeg.rank_le {N : ℕ} {c : PrefixCircuit N} {a b : ℕ}
    {root z u : Wire N c.size} (h : ReachesInSeg c a b root z u) : z.rank ≤ u.rank := by
  induction h with
  | refl => exact le_rfl
  | @step p g hg _ ih =>
    obtain ⟨_, hfi, _⟩ := (mem_segChildren_iff c a b root p g).mp hg
    have hlt : p.rank < (Wire.gate g : Wire N c.size).rank := by
      rw [← hfi]; exact rank_firstInput_lt c.program g
    omega

private theorem ReachesInSeg.trans_step_top {N : ℕ} {c : PrefixCircuit N} {a b : ℕ}
    {root w : Wire N c.size} {g : Fin c.size} {u : Wire N c.size}
    (hg : g ∈ segChildren c a b root w)
    (hu : ReachesInSeg c a b root (.gate g) u) :
    ReachesInSeg c a b root w u := by
  induction hu with
  | refl => exact ReachesInSeg.step hg (ReachesInSeg.refl w)
  | step hg' _ ih => exact ReachesInSeg.step hg' ih

private theorem ReachesInSeg.top_inversion {N : ℕ} {c : PrefixCircuit N} {a b : ℕ}
    {root w u : Wire N c.size} (h : ReachesInSeg c a b root w u) :
    u = w ∨ ∃ g ∈ segChildren c a b root w, ReachesInSeg c a b root (.gate g) u := by
  induction h with
  | refl => exact Or.inl rfl
  | @step p g hg _ ih =>
    rcases ih with rfl | ⟨g₀, hg₀, hsub⟩
    · exact Or.inr ⟨g, hg, ReachesInSeg.refl (.gate g)⟩
    · exact Or.inr ⟨g₀, hg₀, ReachesInSeg.step hg hsub⟩

private theorem ReachesInSeg.child_unique {N : ℕ} {c : PrefixCircuit N} {a b : ℕ}
    {root w u : Wire N c.size} {g₁ g₂ : Fin c.size}
    (hg₁ : g₁ ∈ segChildren c a b root w) (hg₂ : g₂ ∈ segChildren c a b root w)
    (h₁ : ReachesInSeg c a b root (.gate g₁) u) (h₂ : ReachesInSeg c a b root (.gate g₂) u) :
    g₁ = g₂ := by
  induction h₁ with
  | refl =>
    cases h₂ with
    | refl => rfl
    | step hg' hsub =>
      obtain ⟨_, hfi', _⟩ := (mem_segChildren_iff c a b root _ _).mp hg'
      obtain ⟨_, hfi₁, _⟩ := (mem_segChildren_iff c a b root w g₁).mp hg₁
      obtain ⟨_, hfi₂, _⟩ := (mem_segChildren_iff c a b root w g₂).mp hg₂
      have hp := hfi'.symm.trans hfi₁
      rw [hp] at hsub
      have hrk := hsub.rank_le
      have hlt : w.rank < (Wire.gate g₂ : Wire N c.size).rank :=
        hfi₂ ▸ rank_firstInput_lt c.program g₂
      omega
  | step hg' hsub₁ ih =>
    cases h₂ with
    | refl =>
      obtain ⟨_, hfi', _⟩ := (mem_segChildren_iff c a b root _ _).mp hg'
      obtain ⟨_, hfi₁, _⟩ := (mem_segChildren_iff c a b root w g₁).mp hg₁
      obtain ⟨_, hfi₂, _⟩ := (mem_segChildren_iff c a b root w g₂).mp hg₂
      have hp := hfi'.symm.trans hfi₂
      rw [hp] at hsub₁
      have hrk := hsub₁.rank_le
      have hlt : w.rank < (Wire.gate g₁ : Wire N c.size).rank :=
        hfi₁ ▸ rank_firstInput_lt c.program g₁
      omega
    | step hg₂' hsub₂ =>
      obtain ⟨_, hfi', _⟩ := (mem_segChildren_iff c a b root _ _).mp hg'
      obtain ⟨_, hfi₂', _⟩ := (mem_segChildren_iff c a b root _ _).mp hg₂'
      have hp := hfi₂'.symm.trans hfi'
      rw [hp] at hsub₂
      exact ih hsub₂

private theorem ReachesInSeg.segActive_of {N : ℕ} {c : PrefixCircuit N} {a b : ℕ}
    {root z u : Wire N c.size} (hz : segActive c a b root z = true)
    (h : ReachesInSeg c a b root z u) : segActive c a b root u = true := by
  induction h with
  | refl => exact hz
  | @step p g hg _ _ => exact ((mem_segChildren_iff c a b root p g).mp hg).2.2

private def countWireInSeg {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (root target w : Wire N c.size) : ℕ :=
  (if w = target then 1 else 0) +
    ∑ i : Fin (segChildren c a b root w).length,
      countWireInSeg c a b root target (.gate (segChildren c a b root w)[i])
termination_by c.size - w.rank
decreasing_by
  have hlt := segChildren_rank_lt c a b root w i
  have hle := Wire.rank_le (Wire.gate (segChildren c a b root w)[i] : Wire N c.size)
  omega

private theorem countWireInSeg_def {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (root target w : Wire N c.size) :
    countWireInSeg c a b root target w =
      (if w = target then 1 else 0) +
        ∑ i : Fin (segChildren c a b root w).length,
          countWireInSeg c a b root target (.gate (segChildren c a b root w)[i]) := by
  rw [countWireInSeg]

private theorem countWireInSeg_iff {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (root target : Wire N c.size) :
    ∀ w : Wire N c.size,
      (ReachesInSeg c a b root w target → countWireInSeg c a b root target w = 1) ∧
      (¬ ReachesInSeg c a b root w target → countWireInSeg c a b root target w = 0) := by
  intro w
  have haux : ∀ rem, ∀ w : Wire N c.size, c.size - w.rank = rem →
      (ReachesInSeg c a b root w target → countWireInSeg c a b root target w = 1) ∧
      (¬ ReachesInSeg c a b root w target → countWireInSeg c a b root target w = 0) := by
    intro rem
    induction rem using Nat.strong_induction_on with
    | _ rem ih =>
      intro w hrem
      have hnodup : (segChildren c a b root w).Nodup := (List.nodup_finRange c.size).filter _
      have hch_ih : ∀ i : Fin (segChildren c a b root w).length,
          (ReachesInSeg c a b root (.gate (segChildren c a b root w)[i]) target →
            countWireInSeg c a b root target (.gate (segChildren c a b root w)[i]) = 1) ∧
          (¬ ReachesInSeg c a b root (.gate (segChildren c a b root w)[i]) target →
            countWireInSeg c a b root target (.gate (segChildren c a b root w)[i]) = 0) := by
        intro i
        have hlt := segChildren_rank_lt c a b root w i
        have hle := Wire.rank_le (Wire.gate (segChildren c a b root w)[i] : Wire N c.size)
        exact ih (c.size - (Wire.gate (segChildren c a b root w)[i] : Wire N c.size).rank)
          (by omega) (.gate (segChildren c a b root w)[i]) rfl
      refine ⟨fun hreach => ?_, fun hnreach => ?_⟩
      · rw [countWireInSeg_def]
        by_cases hwt : w = target
        · have hzero : ∀ i : Fin (segChildren c a b root w).length,
              countWireInSeg c a b root target (.gate (segChildren c a b root w)[i]) = 0 := by
            intro i
            refine (hch_ih i).2 fun hr => ?_
            have hrk := hr.rank_le
            have hlt := segChildren_rank_lt c a b root w i
            have hwt_rk : w.rank = target.rank := congrArg Wire.rank hwt
            omega
          rw [Finset.sum_eq_zero fun i _ => hzero i]
          simp only [hwt, ↓reduceIte, Nat.add_zero]
        · obtain ⟨g, hg_mem, hg_sub⟩ := (hreach.top_inversion).resolve_left (Ne.symm hwt)
          obtain ⟨idx, hidx_lt, hidx_eq⟩ := List.getElem_of_mem hg_mem
          let i₀ : Fin (segChildren c a b root w).length := ⟨idx, hidx_lt⟩
          have hi₀ : countWireInSeg c a b root target
              (.gate (segChildren c a b root w)[i₀]) = 1 := by
            refine (hch_ih i₀).1 ?_
            dsimp only [i₀]
            rw [Fin.getElem_fin, hidx_eq]
            exact hg_sub
          have hother : ∀ i : Fin (segChildren c a b root w).length, i ≠ i₀ →
              countWireInSeg c a b root target (.gate (segChildren c a b root w)[i]) = 0 := by
            intro i hne
            refine (hch_ih i).2 fun hi_sub => ?_
            have heq_g := ReachesInSeg.child_unique (List.getElem_mem _) hg_mem hi_sub hg_sub
            rw [← hidx_eq] at heq_g
            have heq_idx := (List.Nodup.getElem_inj_iff hnodup).mp heq_g
            exact hne (Fin.ext heq_idx)
          rw [Fintype.sum_eq_single i₀ hother, hi₀]
          simp only [hwt, ↓reduceIte, Nat.zero_add]
      · rw [countWireInSeg_def]
        have hwt : w ≠ target := fun heq => hnreach (heq ▸ ReachesInSeg.refl w)
        have hzero : ∀ i : Fin (segChildren c a b root w).length,
            countWireInSeg c a b root target (.gate (segChildren c a b root w)[i]) = 0 := by
          intro i
          exact (hch_ih i).2 fun hi_sub =>
            hnreach (ReachesInSeg.trans_step_top (List.getElem_mem _) hi_sub)
        rw [Finset.sum_eq_zero fun i _ => hzero i]
        simp only [hwt, ↓reduceIte, Nat.add_zero]
  exact haux (c.size - w.rank) w rfl

private theorem countWireInSeg_eq_one_of_reaches {N : ℕ} {c : PrefixCircuit N} {a b : ℕ}
    {root target w : Wire N c.size} (h : ReachesInSeg c a b root w target) :
    countWireInSeg c a b root target w = 1 :=
  (countWireInSeg_iff c a b root target w).1 h

private theorem countWireInSeg_eq_zero_of_not_reaches {N : ℕ} {c : PrefixCircuit N} {a b : ℕ}
    {root target w : Wire N c.size} (h : ¬ ReachesInSeg c a b root w target) :
    countWireInSeg c a b root target w = 0 :=
  (countWireInSeg_iff c a b root target w).2 h

private theorem reaches_of_countWireInSeg_ne_zero {N : ℕ} {c : PrefixCircuit N} {a b : ℕ}
    {root target w : Wire N c.size} (h : countWireInSeg c a b root target w ≠ 0) :
    ReachesInSeg c a b root w target := by
  by_contra hnr
  exact h (countWireInSeg_eq_zero_of_not_reaches hnr)

private theorem countWireInSeg_le_one {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (root target w : Wire N c.size) :
    countWireInSeg c a b root target w ≤ 1 := by
  by_cases h : ReachesInSeg c a b root w target
  · rw [countWireInSeg_eq_one_of_reaches h]
  · rw [countWireInSeg_eq_zero_of_not_reaches h]; omega

private theorem buildSegTree_counts {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (root w : Wire N c.size) :
    (buildSegTree c a b root w).outCount =
      (∑ u : Wire N c.size, if segHasOut c a b u then countWireInSeg c a b root u w else 0) ∧
    (∀ s, (buildSegTree c a b root w).outAt s =
      ∑ u : Wire N c.size,
        if segHasOut c a b u ∧ wireState c.program u = s then
          countWireInSeg c a b root u w
        else 0) ∧
    (∀ m, (buildSegTree c a b root w).mulCount m =
      ∑ g : Fin c.size,
        if (c.program.lines g).op = .mul ∧ wireState c.program (.gate g) = m ∧ w ≠ .gate g then
          countWireInSeg c a b root (.gate g) w
        else 0) := by
  have haux : ∀ rem, ∀ w : Wire N c.size, c.size - w.rank = rem →
      (buildSegTree c a b root w).outCount =
        (∑ u : Wire N c.size, if segHasOut c a b u then countWireInSeg c a b root u w else 0) ∧
      (∀ s, (buildSegTree c a b root w).outAt s =
        ∑ u : Wire N c.size,
          if segHasOut c a b u ∧ wireState c.program u = s then
            countWireInSeg c a b root u w
          else 0) ∧
      (∀ m, (buildSegTree c a b root w).mulCount m =
        ∑ g : Fin c.size,
          if (c.program.lines g).op = .mul ∧ wireState c.program (.gate g) = m ∧ w ≠ .gate g then
            countWireInSeg c a b root (.gate g) w
          else 0) := by
    intro rem
    induction rem using Nat.strong_induction_on with
    | _ rem ih =>
      intro w hrem
      have hch_ih : ∀ i : Fin (segChildren c a b root w).length,
          (buildSegTree c a b root (.gate (segChildren c a b root w)[i])).outCount =
            (∑ u : Wire N c.size,
              if segHasOut c a b u then
                countWireInSeg c a b root u (.gate (segChildren c a b root w)[i])
              else 0) ∧
          (∀ s, (buildSegTree c a b root (.gate (segChildren c a b root w)[i])).outAt s =
            ∑ u : Wire N c.size,
              if segHasOut c a b u ∧ wireState c.program u = s then
                countWireInSeg c a b root u (.gate (segChildren c a b root w)[i])
              else 0) ∧
          (∀ m, (buildSegTree c a b root (.gate (segChildren c a b root w)[i])).mulCount m =
            ∑ g : Fin c.size,
              if (c.program.lines g).op = .mul ∧ wireState c.program (.gate g) = m ∧
                  (Wire.gate (segChildren c a b root w)[i] : Wire N c.size) ≠ .gate g then
                countWireInSeg c a b root (.gate g) (.gate (segChildren c a b root w)[i])
              else 0) := by
        intro i
        have hlt := segChildren_rank_lt c a b root w i
        have hle := Wire.rank_le (Wire.gate (segChildren c a b root w)[i] : Wire N c.size)
        exact ih (c.size - (Wire.gate (segChildren c a b root w)[i] : Wire N c.size).rank)
          (by omega) (.gate (segChildren c a b root w)[i]) rfl
      refine ⟨?_, ?_, ?_⟩
      · rw [buildSegTree_eq]
        simp only [GenPrefixTree.outCount]
        rw [Finset.sum_congr rfl fun i _ => (hch_ih i).1, Finset.sum_comm]
        have hw_split : (if segHasOut c a b w = true then 1 else 0) =
            ∑ u : Wire N c.size,
              if segHasOut c a b u = true then (if w = u then 1 else 0) else 0 := by
          rw [Fintype.sum_eq_single w]
          · simp only [↓reduceIte]
          · intro u hne; simp only [Ne.symm hne, ↓reduceIte, ite_self]
        rw [hw_split, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [countWireInSeg_def]
        by_cases hu : segHasOut c a b u = true
        · simp only [hu, ↓reduceIte]
        · simp only [hu, Bool.false_eq_true, ↓reduceIte, Finset.sum_const_zero, Nat.add_zero]
      · intro s
        rw [buildSegTree_eq]
        simp only [GenPrefixTree.outAt]
        rw [Finset.sum_congr rfl fun i _ => (hch_ih i).2.1 s, Finset.sum_comm]
        have hw_split : (if segHasOut c a b w = true ∧ wireState c.program w = s then 1 else 0) =
            ∑ u : Wire N c.size,
              if segHasOut c a b u = true ∧ wireState c.program u = s then
                (if w = u then 1 else 0)
              else 0 := by
          rw [Fintype.sum_eq_single w]
          · simp only [↓reduceIte]
          · intro u hne; simp only [Ne.symm hne, ↓reduceIte, ite_self]
        rw [hw_split, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [countWireInSeg_def]
        by_cases hu : segHasOut c a b u = true ∧ wireState c.program u = s
        · simp only [hu, and_self, ↓reduceIte]
        · simp only [hu, ↓reduceIte, Finset.sum_const_zero, Nat.add_zero]
      · intro m
        rw [buildSegTree_eq]
        simp only [GenPrefixTree.mulCount, beq_iff_eq]
        have hstep : ∀ i : Fin (segChildren c a b root w).length,
            ((if (c.program.lines (segChildren c a b root w)[i]).op = .mul ∧
                (buildSegTree c a b root (.gate (segChildren c a b root w)[i])).state = m then 1
              else 0) +
              (buildSegTree c a b root (.gate (segChildren c a b root w)[i])).mulCount m) =
            ∑ g : Fin c.size,
              if (c.program.lines g).op = .mul ∧ wireState c.program (.gate g) = m ∧
                  w ≠ .gate g then
                countWireInSeg c a b root (.gate g) (.gate (segChildren c a b root w)[i])
              else 0 := by
          intro i
          let gi := (segChildren c a b root w)[i]
          have hmem : gi ∈ segChildren c a b root w := List.getElem_mem _
          obtain ⟨_, hfi, _⟩ := (mem_segChildren_iff c a b root w gi).mp hmem
          have hne_w : w ≠ .gate gi := by
            intro heq
            have hlt := rank_firstInput_lt c.program gi
            rw [hfi, heq] at hlt
            omega
          have hst_eq : (buildSegTree c a b root (.gate gi)).state =
              wireState c.program (.gate gi) := by
            rw [buildSegTree_eq]
            rfl
          change ((if (c.program.lines gi).op = .mul ∧
                (buildSegTree c a b root (.gate gi)).state = m then 1 else 0) +
              (buildSegTree c a b root (.gate gi)).mulCount m) =
            ∑ g : Fin c.size,
              if (c.program.lines g).op = .mul ∧ wireState c.program (.gate g) = m ∧
                  w ≠ .gate g then
                countWireInSeg c a b root (.gate g) (.gate gi)
              else 0
          rw [hst_eq, (hch_ih i).2.2 m]
          have hhead : (if (c.program.lines gi).op = .mul ∧
                wireState c.program (.gate gi) = m then 1 else 0) =
              ∑ g : Fin c.size,
                if (c.program.lines g).op = .mul ∧ wireState c.program (.gate g) = m ∧
                    g = gi then 1 else 0 := by
            rw [Fintype.sum_eq_single gi]
            · simp only [and_true]
            · intro g hne; simp only [hne, and_false, ↓reduceIte]
          rw [hhead, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun g _ => ?_
          change _ + (if (c.program.lines g).op = .mul ∧ wireState c.program (.gate g) = m ∧
              (Wire.gate gi : Wire N c.size) ≠ .gate g then
                countWireInSeg c a b root (.gate g) (.gate gi) else 0) = _
          by_cases hopm : (c.program.lines g).op = .mul ∧ wireState c.program (.gate g) = m
          · rcases hopm with ⟨hop, hwm⟩
            by_cases hgi : g = gi
            · rw [hgi]
              have hself : countWireInSeg c a b root (.gate gi) (.gate gi) = 1 :=
                countWireInSeg_eq_one_of_reaches (ReachesInSeg.refl _)
              rw [hself]
              rw [hgi] at hop hwm
              simp only [hop, hwm, ne_eq, not_true_eq_false, and_false, and_true, ↓reduceIte,
                hne_w, not_false_eq_true, Nat.add_zero]
            · have hgate_ne : (Wire.gate gi : Wire N c.size) ≠ .gate g := fun h =>
                hgi (Wire.gate.inj h).symm
              by_cases hgw : w = .gate g
              · have hzero : countWireInSeg c a b root (.gate g) (.gate gi) = 0 := by
                  apply countWireInSeg_eq_zero_of_not_reaches
                  intro hr
                  have hrk := hr.rank_le
                  have hlt := rank_firstInput_lt c.program gi
                  rw [hfi, hgw] at hlt
                  omega
                rw [hzero]
                simp only [hgi, hgw, ne_eq, not_true_eq_false, and_false, ↓reduceIte, ite_self]
              · simp only [hop, hwm, hgi, and_false, hgate_ne, hgw, ne_eq, not_false_eq_true,
                  and_true, ↓reduceIte, Nat.zero_add]
          · have hf1 : ¬ ((c.program.lines g).op = .mul ∧
                wireState c.program (.gate g) = m ∧ g = gi) := fun h => hopm ⟨h.1, h.2.1⟩
            have hf2 : ¬ ((c.program.lines g).op = .mul ∧
                wireState c.program (.gate g) = m ∧
                  (Wire.gate gi : Wire N c.size) ≠ .gate g) := fun h => hopm ⟨h.1, h.2.1⟩
            have hf3 : ¬ ((c.program.lines g).op = .mul ∧
                wireState c.program (.gate g) = m ∧ w ≠ .gate g) := fun h => hopm ⟨h.1, h.2.1⟩
            simp only [hf1, hf2, hf3, ↓reduceIte]
        rw [Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_comm]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [countWireInSeg_def]
        by_cases hc : (c.program.lines g).op = .mul ∧ wireState c.program (.gate g) = m ∧
            w ≠ .gate g
        · rcases hc with ⟨hc1, hc2, hc3⟩
          have hwg : ¬ (w = .gate g) := hc3
          simp only [hc1, hc2, hwg, ne_eq, not_false_eq_true, and_self, ↓reduceIte, Nat.zero_add]
        · simp only [hc, ↓reduceIte, Finset.sum_const_zero]
  exact haux (c.size - w.rank) w rfl

private theorem segHasOut_le_card_outputs {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (w : Wire N c.size) :
    (if segHasOut c a b w then 1 else 0) ≤
      (Finset.univ.filter fun j : Fin N => c.outputs j = w).card := by
  by_cases h : segHasOut c a b w = true
  · simp only [h, ↓reduceIte]
    simp only [segHasOut, decide_eq_true_eq] at h
    obtain ⟨j, _, _, hjw⟩ := h
    exact Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjw⟩⟩
  · simp only [h, Bool.false_eq_true, ↓reduceIte, Nat.zero_le]

private theorem seg_fanout_bound {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (root w : Wire N c.size) :
    (segChildren c a b root w).length + (if segHasOut c a b w then 1 else 0) ≤
      wireFanout c w := by
  set ch := segChildren c a b root w
  have hnodup : ch.Nodup := (List.nodup_finRange c.size).filter _
  have hdeg : ch.length ≤ c.outDeg w := by
    rw [c.outDeg_eq_card_filter, ← List.toFinset_card_of_nodup hnodup]
    refine Finset.card_le_card_of_injOn (firstSlotOfGate c) ?_ ?_
    · intro g hg
      rw [Finset.mem_coe, List.mem_toFinset, mem_segChildren_iff] at hg
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (slotWire_firstSlotOfGate c g).trans hg.2.1⟩
    · intro g₁ _ g₂ _ h
      exact firstSlotOfGate_injective c h
  have hout := segHasOut_le_card_outputs c a b w
  rw [wireFanout]
  omega

private theorem seg_root_fanout_bound {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (root : Wire N c.size) (sg : Fin c.size)
    (hsg_fi : firstInput (c.program.lines sg) = root)
    (hsg_not : sg ∉ segChildren c a b root root) :
    (segChildren c a b root root).length + (if segHasOut c a b root then 1 else 0) + 1 ≤
      wireFanout c root := by
  set ch := segChildren c a b root root
  have hnodup : ch.Nodup := (List.nodup_finRange c.size).filter _
  have hsg_not_fin : sg ∉ ch.toFinset := by rw [List.mem_toFinset]; exact hsg_not
  have hdeg : ch.length + 1 ≤ c.outDeg root := by
    rw [c.outDeg_eq_card_filter, ← List.toFinset_card_of_nodup hnodup,
      ← Finset.card_insert_of_notMem hsg_not_fin]
    refine Finset.card_le_card_of_injOn (firstSlotOfGate c) ?_ ?_
    · intro g hg
      rw [Finset.mem_coe, Finset.mem_insert, List.mem_toFinset, mem_segChildren_iff] at hg
      rw [Finset.mem_coe, Finset.mem_filter]
      rcases hg with rfl | hg
      · exact ⟨Finset.mem_univ _, (slotWire_firstSlotOfGate c g).trans hsg_fi⟩
      · exact ⟨Finset.mem_univ _, (slotWire_firstSlotOfGate c g).trans hg.2.1⟩
    · intro g₁ _ g₂ _ h
      exact firstSlotOfGate_injective c h
  have hout := segHasOut_le_card_outputs c a b root
  rw [wireFanout]
  omega

private theorem buildSegTree_props {N k : ℕ} (c : PrefixCircuit N) (a b D : ℕ)
    (root : Wire N c.size) (I : IntervalTree a b)
    (hfan : FanoutAtMost c k)
    (houtWord : ∀ j : Fin N, programWord c.program (c.outputs j) = List.range' 0 (j.val + 1))
    (hout_depth : ∀ j : Fin N, c.program.wireDepths (c.outputs j) ≤ D)
    (hroot_unique : ∀ g : Fin c.size,
      (c.program.lines g).op = .mul →
      programWord c.program (.gate g) = List.range' 0 a → Wire.gate g = root)
    (hmul_seg : ∀ g : Fin c.size, ∀ s, a < s → s < b →
      (c.program.lines g).op = .mul →
      programWord c.program (.gate g) = List.range' 0 s →
        ∃ p, a ≤ p ∧ p < s ∧
          programWord c.program (firstInput (c.program.lines g)) = List.range' 0 p ∧
          (p, s) ∈ I.intervals.erase (a, b)) :
    ∀ w : Wire N c.size, segActive c a b root w = true →
      (∃ s, a ≤ s ∧ s < b ∧ programWord c.program w = List.range' 0 s ∧
        (buildSegTree c a b root w).state = s) ∧
      (buildSegTree c a b root w).MaxStateLt b ∧
      (buildSegTree c a b root w).FanoutAtMost k ∧
      (buildSegTree c a b root w).Valid (I.intervals.erase (a, b)) ∧
      c.program.wireDepths w + (buildSegTree c a b root w).depth ≤ D := by
  intro w
  have haux : ∀ rem, ∀ w : Wire N c.size, c.size - w.rank = rem →
      segActive c a b root w = true →
      (∃ s, a ≤ s ∧ s < b ∧ programWord c.program w = List.range' 0 s ∧
        (buildSegTree c a b root w).state = s) ∧
      (buildSegTree c a b root w).MaxStateLt b ∧
      (buildSegTree c a b root w).FanoutAtMost k ∧
      (buildSegTree c a b root w).Valid (I.intervals.erase (a, b)) ∧
      c.program.wireDepths w + (buildSegTree c a b root w).depth ≤ D := by
    intro rem
    induction rem using Nat.strong_induction_on with
    | _ rem ih =>
      intro w hrem hact
      have hch_ih : ∀ i : Fin (segChildren c a b root w).length,
          (∃ s, a ≤ s ∧ s < b ∧
            programWord c.program (.gate (segChildren c a b root w)[i]) = List.range' 0 s ∧
            (buildSegTree c a b root (.gate (segChildren c a b root w)[i])).state = s) ∧
          (buildSegTree c a b root (.gate (segChildren c a b root w)[i])).MaxStateLt b ∧
          (buildSegTree c a b root (.gate (segChildren c a b root w)[i])).FanoutAtMost k ∧
          (buildSegTree c a b root (.gate (segChildren c a b root w)[i])).Valid
            (I.intervals.erase (a, b)) ∧
          c.program.wireDepths (.gate (segChildren c a b root w)[i]) +
            (buildSegTree c a b root (.gate (segChildren c a b root w)[i])).depth ≤ D := by
        intro i
        have hmem : (segChildren c a b root w)[i] ∈ segChildren c a b root w := List.getElem_mem _
        obtain ⟨_, _, hact_i⟩ := (mem_segChildren_iff c a b root w _).mp hmem
        have hlt := segChildren_rank_lt c a b root w i
        have hle := Wire.rank_le (Wire.gate (segChildren c a b root w)[i] : Wire N c.size)
        exact ih (c.size - (Wire.gate (segChildren c a b root w)[i] : Wire N c.size).rank)
          (by omega) (.gate (segChildren c a b root w)[i]) rfl hact_i
      have hw_state : ∃ s, a ≤ s ∧ s < b ∧ programWord c.program w = List.range' 0 s := by
        rcases (segActive_iff c a b root w).mp hact with hout | ⟨g, hg⟩
        · simp only [segHasOut, decide_eq_true_eq] at hout
          obtain ⟨j, hj1, hj2, hjeq⟩ := hout
          exact ⟨j.val + 1, hj1, hj2, hjeq ▸ houtWord j⟩
        · obtain ⟨idx, hidx_lt, hidx_eq⟩ := List.getElem_of_mem hg
          let i₀ : Fin (segChildren c a b root w).length := ⟨idx, hidx_lt⟩
          obtain ⟨⟨s', hs1, hs2, hgw, _⟩, _⟩ := hch_ih i₀
          dsimp only [i₀] at hgw
          rw [Fin.getElem_fin, hidx_eq] at hgw
          obtain ⟨hne_r, hfi, _⟩ := (mem_segChildren_iff c a b root w g).mp hg
          cases hline : c.program.lines g with
          | mk op wires =>
            cases op with
            | mul =>
              have hs_ne : s' ≠ a := by
                intro heq
                rw [heq] at hgw
                exact hne_r (hroot_unique g (by rw [hline]) hgw)
              obtain ⟨p, hp1, hp2, hpw, _⟩ :=
                hmul_seg g s' (by omega) hs2 (by rw [hline]) hgw
              exact ⟨p, hp1, by omega, hfi ▸ hpw⟩
            | id =>
              have hpw : programWord c.program (wires 0) = List.range' 0 s' := by
                rw [← programWord_gate_id c.program g wires hline]
                exact hgw
              have hfi0 : wires 0 = w := by simpa only [hline, firstInput] using hfi
              exact ⟨s', hs1, hs2, hfi0 ▸ hpw⟩
      obtain ⟨s, hs1, hs2, hpw⟩ := hw_state
      have hws : wireState c.program w = s := by
        simp only [wireState, hpw, List.length_range']
      have hst_tree : (buildSegTree c a b root w).state = s := by
        rw [buildSegTree_eq]
        exact hws
      refine ⟨⟨s, hs1, hs2, hpw, hst_tree⟩, ?_, ?_, ?_, ?_⟩
      · rw [buildSegTree_eq]
        exact ⟨by rw [hws]; exact hs2, fun i => (hch_ih i).2.1⟩
      · rw [buildSegTree_eq]
        exact ⟨(seg_fanout_bound c a b root w).trans (hfan w), fun i => (hch_ih i).2.2.1⟩
      · rw [buildSegTree_eq]
        refine ⟨fun i => ?_, fun i => (hch_ih i).2.2.2.1⟩
        dsimp only
        let gi := (segChildren c a b root w)[i]
        obtain ⟨⟨s_i, hsi1, hsi2, hgwi, hsti⟩, _⟩ := hch_ih i
        obtain ⟨hne_r, hfi, _⟩ := (mem_segChildren_iff c a b root w gi).mp (List.getElem_mem _)
        change if ((c.program.lines gi).op == .mul) = true then
            wireState c.program w < (buildSegTree c a b root (.gate gi)).state ∧
              (wireState c.program w, (buildSegTree c a b root (.gate gi)).state) ∈
                I.intervals.erase (a, b)
          else (buildSegTree c a b root (.gate gi)).state = wireState c.program w
        change programWord c.program (.gate gi) = List.range' 0 s_i at hgwi
        change (buildSegTree c a b root (.gate gi)).state = s_i at hsti
        rw [hws, hsti]
        cases hline : c.program.lines gi with
        | mk op wires =>
          cases op with
          | mul =>
            simp only [BEq.rfl, ↓reduceIte]
            have hsi_ne : s_i ≠ a := by
              intro heq
              rw [heq] at hgwi
              exact hne_r (hroot_unique gi (by rw [hline]) hgwi)
            obtain ⟨p, hp1, hp2, hpw_p, hpiv⟩ :=
              hmul_seg gi s_i (by omega) hsi2 (by rw [hline]) hgwi
            have hps : p = s := by
              have h1 : List.range' 0 p = List.range' 0 s := by
                rw [← hpw_p, hfi, hpw]
              have := congrArg List.length h1
              simpa only [List.length_range'] using this
            rw [← hps]
            exact ⟨hp2, hpiv⟩
          | id =>
            have hop : ((PrefixOp.id == PrefixOp.mul) = true) = False := by decide
            simp only [hop, ↓reduceIte]
            have h1 : List.range' 0 s_i = List.range' 0 s := by
              rw [← hgwi, programWord_gate_id c.program gi wires hline]
              have hfi0 : wires 0 = w := by simpa only [hline, firstInput] using hfi
              rw [hfi0, hpw]
            have := congrArg List.length h1
            simpa only [List.length_range'] using this
      · rw [buildSegTree_eq]
        simp only [GenPrefixTree.depth]
        by_cases hch0 : (segChildren c a b root w).length = 0
        · have hempty : (Finset.univ : Finset (Fin (segChildren c a b root w).length)) = ∅ := by
            ext i; exact absurd i.isLt (by omega)
          rw [hempty, Finset.sup_empty, Nat.bot_eq_zero, Nat.add_zero]
          rcases (segActive_iff c a b root w).mp hact with hout | ⟨g, hg⟩
          · simp only [segHasOut, decide_eq_true_eq] at hout
            obtain ⟨j, _, _, rfl⟩ := hout
            exact hout_depth j
          · exact absurd (List.length_pos_of_mem hg) (by omega)
        · let i₀ : Fin (segChildren c a b root w).length := ⟨0, by omega⟩
          have hsup_le : (Finset.univ.sup fun i : Fin (segChildren c a b root w).length =>
              (buildSegTree c a b root (.gate (segChildren c a b root w)[i])).depth + 1) ≤
              D - c.program.wireDepths w := by
            refine Finset.sup_le fun i _ => ?_
            have hdi := (hch_ih i).2.2.2.2
            have hmem : (segChildren c a b root w)[i] ∈ segChildren c a b root w :=
              List.getElem_mem _
            obtain ⟨_, hfi, _⟩ := (mem_segChildren_iff c a b root w _).mp hmem
            have hstep := wireDepths_firstInput_lt c.program (segChildren c a b root w)[i]
            rw [hfi] at hstep
            omega
          have hwd_le : c.program.wireDepths w ≤ D := by
            have hdi := (hch_ih i₀).2.2.2.2
            have hmem : (segChildren c a b root w)[i₀] ∈ segChildren c a b root w :=
              List.getElem_mem _
            obtain ⟨_, hfi, _⟩ := (mem_segChildren_iff c a b root w _).mp hmem
            have hstep := wireDepths_firstInput_lt c.program (segChildren c a b root w)[i₀]
            rw [hfi] at hstep
            omega
          omega
  exact haux (c.size - w.rank) w rfl

private theorem reaches_root_of_seg_wire {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (hN : 1 ≤ N) (ha1 : 1 ≤ a) (root : Wire N c.size)
    (hroot_zero : a = 1 → root = .input ⟨0, hN⟩)
    (hroot_unique : ∀ g : Fin c.size,
      (c.program.lines g).op = .mul →
      programWord c.program (.gate g) = List.range' 0 a → Wire.gate g = root)
    (hmul_seg : ∀ g : Fin c.size, ∀ s, a < s → s < b →
      (c.program.lines g).op = .mul →
      programWord c.program (.gate g) = List.range' 0 s →
        ∃ p, a ≤ p ∧ p < s ∧
          programWord c.program (firstInput (c.program.lines g)) = List.range' 0 p) :
    ∀ u : Wire N c.size, ∀ s, a ≤ s → s < b →
      programWord c.program u = List.range' 0 s →
      segActive c a b root u = true →
      ReachesInSeg c a b root root u := by
  intro u
  refine prefix_wire_induction c.program
    (fun i s hs1 _ hpw _ => ?_)
    (fun g wires hline ih0 s hs1 hs2 hpw hact => ?_)
    (fun g wires hline ih0 _ s hs1 hs2 hpw hact => ?_) u
  · rw [programWord_input] at hpw
    have hs_eq : s = 1 := by
      have := congrArg List.length hpw
      simpa only [List.length_singleton, List.length_range'] using this.symm
    subst hs_eq
    have ha_eq : a = 1 := by omega
    simp only [List.range'_one, List.cons.injEq, and_true] at hpw
    have hi : i = ⟨0, hN⟩ := Fin.ext hpw
    rw [hi, ← hroot_zero ha_eq]
    exact ReachesInSeg.refl root
  · by_cases hgr : (Wire.gate g : Wire N c.size) = root
    · rw [hgr]; exact ReachesInSeg.refl root
    · have hpw0 : programWord c.program (wires 0) = List.range' 0 s := by
        rw [← programWord_gate_id c.program g wires hline]; exact hpw
      have hfi : firstInput (c.program.lines g) = wires 0 := by simp only [hline, firstInput]
      have hg_ch : g ∈ segChildren c a b root (wires 0) :=
        (mem_segChildren_iff c a b root (wires 0) g).mpr ⟨hgr, hfi, hact⟩
      have hact0 : segActive c a b root (wires 0) = true :=
        (segActive_iff c a b root (wires 0)).mpr (Or.inr ⟨g, hg_ch⟩)
      exact ReachesInSeg.step hg_ch (ih0 s hs1 hs2 hpw0 hact0)
  · by_cases hgr : (Wire.gate g : Wire N c.size) = root
    · rw [hgr]; exact ReachesInSeg.refl root
    · have hs_ne : s ≠ a := fun heq => hgr (hroot_unique g (by rw [hline]) (heq ▸ hpw))
      obtain ⟨p, hp1, hp2, hpw0⟩ := hmul_seg g s (by omega) hs2 (by rw [hline]) hpw
      have hfi : firstInput (c.program.lines g) = wires 0 := by simp only [hline, firstInput]
      rw [hfi] at hpw0
      have hg_ch : g ∈ segChildren c a b root (wires 0) :=
        (mem_segChildren_iff c a b root (wires 0) g).mpr ⟨hgr, hfi, hact⟩
      have hact0 : segActive c a b root (wires 0) = true :=
        (segActive_iff c a b root (wires 0)).mpr (Or.inr ⟨g, hg_ch⟩)
      exact ReachesInSeg.step hg_ch (ih0 p hp1 (by omega) hpw0 hact0)

private theorem optimal_segment_decomposition {N k : ℕ} (hN : 1 ≤ N)
    {c : PrefixCircuit N} (hopt : IsOptimalPrefixCircuit c) (hfan : FanoutAtMost c k) :
    ∃ T : ℕ → ℕ,
      T 0 = 1 ∧
      T c.depth = N ∧
      ∀ d < c.depth,
        T d < T (d + 1) ∧
        ∃ (I : IntervalTree (T d) (T (d + 1))) (t : GenPrefixTree),
          I.depth ≤ d ∧
          t.state = T d ∧
          t.MaxStateLt (T (d + 1)) ∧
          t.rootBudget + 1 ≤ k ∧
          t.FanoutAtMost k ∧
          d + t.depth ≤ c.depth ∧
          t.Valid (I.intervals.erase (T d, T (d + 1))) ∧
          (∀ s, t.outAt s ≤ 1) ∧
          (∀ m, t.mulCount m ≤ 1) ∧
          T (d + 1) - T d ≤ t.outCount := by
  obtain ⟨hc, hzero_def⟩ := hopt
  set D := c.depth
  obtain ⟨houtWord, hwLast, hB, hF_sub, hF_card, lastMul, hlastSpec,
      hOut_sub, hOut_card, hinter_sub⟩ := universal_mul_sets hN hc
  have hlastWord : ∀ r : Fin (N - 1),
      programWord c.program (.gate (lastMul r)) = List.range' 0 (r.val + 2) :=
    fun r => (hlastSpec r).2.2
  let B : Finset (Fin c.size) := Finset.univ.filter fun g => (c.program.lines g).op = .mul
  let wLast : Wire N c.size := c.outputs ⟨N - 1, by omega⟩
  let F : Finset (Fin c.size) := ancMul c.program wLast
  let OutMul : Finset (Fin c.size) := Finset.univ.image lastMul
  have hc1 := Finset.card_le_card hinter_sub
  have hc2 := List.toFinset_card_le (leftSpine c.program wLast)
  have hc3 := leftSpine_length_le_wireDepths c.program wLast
  have hc4 : c.program.wireDepths wLast ≤ D := c.outputDepths_le_depth ⟨N - 1, by omega⟩
  have hunion_le := Finset.card_le_card (Finset.union_subset hF_sub hOut_sub)
  have hie := Finset.card_union_add_card_inter F OutMul
  dsimp only [B, wLast, F, OutMul] at hc1 hc2 hc3 hc4 hunion_le hie hB hF_card hOut_card
  have hB_eq : F ∪ OutMul = B :=
    Finset.eq_of_subset_of_card_le (Finset.union_subset hF_sub hOut_sub)
      (by dsimp only [B, wLast, F, OutMul]; omega)
  have hinter_eq : F ∩ OutMul = (leftSpine c.program wLast).toFinset :=
    Finset.eq_of_subset_of_card_le hinter_sub (by dsimp only [wLast, F, OutMul]; omega)
  have hspine_len : (leftSpine c.program wLast).length = D := by dsimp only [wLast]; omega
  have hwLast_d : c.program.wireDepths wLast = D := by dsimp only [wLast]; omega
  obtain ⟨v, u, T, hv0, hT0, hvD, hTD, hseg, hanc_part⟩ :=
    spine_decomposition c.program hN wLast N hN hwLast (hspine_len.trans hwLast_d.symm)
  rw [hwLast_d] at hvD hTD hseg hanc_part
  have hT_mono : ∀ d₁ d₂, d₁ ≤ d₂ → d₂ ≤ D → T d₁ ≤ T d₂ := by
    intro d₁ d₂ h12 h2D
    induction d₂ with
    | zero =>
      have hd0 : d₁ = 0 := by omega
      rw [hd0]
    | succ d₂ ih =>
      by_cases h_eq : d₁ = d₂ + 1
      · rw [h_eq]
      · exact (ih (by omega) (by omega)).trans (hseg d₂ (by omega)).1.le
  have hT_strict : ∀ d₁ d₂, d₁ < d₂ → d₂ ≤ D → T d₁ < T d₂ := by
    intro d₁ d₂ hlt h2D
    exact lt_of_lt_of_le (hseg d₁ (by omega)).1 (hT_mono (d₁ + 1) d₂ (by omega) h2D)
  have hmul_unique : ∀ (g : Fin c.size) (s : ℕ) (_ : 2 ≤ s) (_ : s ≤ N),
      (c.program.lines g).op = .mul →
      programWord c.program (.gate g) = List.range' 0 s →
      g = lastMul ⟨s - 2, by omega⟩ := by
    intro g s hs2 hsN hop hgw
    have hgB : g ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ g, hop⟩
    rw [← hB_eq, Finset.mem_union] at hgB
    have hgOut : g ∈ OutMul := by
      rcases hgB with hgF | hgO
      · have hsp : g ∈ (leftSpine c.program wLast).toFinset := by
          rw [List.mem_toFinset]
          refine (zero_mem_ancMul_iff_mem_leftSpine c.program wLast N hN hwLast g hgF).mp ?_
          rw [hgw, List.mem_range'_1]; omega
        rw [← hinter_eq, Finset.mem_inter] at hsp
        exact hsp.2
      · exact hgO
    rcases Finset.mem_image.mp hgOut with ⟨r, _, rfl⟩
    have h1 := hgw.symm.trans (hlastWord r)
    have hlen := congrArg List.length h1
    simp only [List.length_range'] at hlen
    congr 1
    exact Fin.ext (by simp only; omega)
  refine ⟨T, hT0, hTD, fun d hd => ?_⟩
  obtain ⟨hTd_lt, ⟨sg, _, hvd_succ, wires_d, hsg_line, hsg_w0, hsg_w1⟩,
      hvd_d, hud_d, hvd_w, hud_w⟩ := hseg d hd
  refine ⟨hTd_lt, ?_⟩
  set a := T d
  set b := T (d + 1)
  set root := v d
  have ha1 : 1 ≤ a := by
    have := hT_mono 0 d (Nat.zero_le d) (by omega)
    omega
  have hbN : b ≤ N := by
    have := hT_mono (d + 1) D (by omega) le_rfl
    omega
  obtain ⟨I, hI_d, hI_anc⟩ := exists_wireIntervalTree c.program (u d) a b hTd_lt hud_w
  have hroot_zero : a = 1 → root = .input ⟨0, hN⟩ := by
    intro ha_eq
    by_cases hd0 : d = 0
    · dsimp only [root]; rw [hd0, hv0]
    · have := hT_strict 0 d (by omega) (by omega)
      omega
  have hroot_unique : ∀ g : Fin c.size,
      (c.program.lines g).op = .mul →
      programWord c.program (.gate g) = List.range' 0 a → Wire.gate g = root := by
    intro g hop hgw
    by_cases hd0 : d = 0
    · have ha_eq : a = 1 := by dsimp only [a]; rw [hd0, hT0]
      rw [ha_eq] at hgw
      cases hline : c.program.lines g with
      | mk op wires =>
        cases op with
        | id => rw [hline] at hop; cases hop
        | mul =>
          rw [programWord_gate_mul c.program g wires hline] at hgw
          have h0_pos : 1 ≤ (programWord c.program (wires 0)).length :=
            List.length_pos_iff.mpr (programWord_ne_nil c.program (wires 0))
          have h1_pos : 1 ≤ (programWord c.program (wires 1)).length :=
            List.length_pos_iff.mpr (programWord_ne_nil c.program (wires 1))
          have hlen := congrArg List.length hgw
          simp only [List.length_append, List.length_range'] at hlen
          omega
    · have ha2 : 2 ≤ a := by
        have := hT_strict 0 d (by omega) (by omega)
        omega
      obtain ⟨_, ⟨sg_prev, _, hv_prev_succ, _, hprev_line, _, _⟩, _, _, _, _⟩ :=
        hseg (d - 1) (by omega)
      have hv_eq : root = .gate sg_prev := by
        dsimp only [root]
        simpa only [show d - 1 + 1 = d by omega] using hv_prev_succ
      have hg_eq := hmul_unique g a ha2 (by omega) hop hgw
      have hprev_eq := hmul_unique sg_prev a ha2 (by omega) (by rw [hprev_line])
        (hv_eq ▸ hvd_w)
      rw [hv_eq, hg_eq, hprev_eq]
  have hmul_seg : ∀ g : Fin c.size, ∀ s, a < s → s < b →
      (c.program.lines g).op = .mul →
      programWord c.program (.gate g) = List.range' 0 s →
        ∃ p, a ≤ p ∧ p < s ∧
          programWord c.program (firstInput (c.program.lines g)) = List.range' 0 p ∧
          (p, s) ∈ I.intervals.erase (a, b) := by
    intro g s has hsb hop hgw
    cases hline : c.program.lines g with
    | mk op wires =>
      cases op with
      | id => rw [hline] at hop; cases hop
      | mul =>
        rw [programWord_gate_mul c.program g wires hline] at hgw
        obtain ⟨hp_pos, hps_pos, hw0, hw1⟩ := range_split_of_append
          (programWord_ne_nil c.program (wires 0)) (programWord_ne_nil c.program (wires 1)) hgw
        set p := (programWord c.program (wires 0)).length
        rw [Nat.zero_add] at hw1
        obtain ⟨hsw, _, hs_op⟩ := stripId_spec c.program (wires 1)
        rw [hw1] at hsw
        cases hs_id : stripId c.program (wires 1) with
        | input i =>
          rw [hs_id, programWord_input] at hsw
          have hlen := congrArg List.length hsw
          simp only [List.length_singleton, List.length_range'] at hlen
          have hp_eq : p = s - 1 := by omega
          refine ⟨p, by omega, by omega, by simpa only [firstInput] using hw0, ?_⟩
          refine Finset.mem_erase.mpr ⟨?_, ?_⟩
          · intro heq; rw [Prod.mk.injEq] at heq; omega
          · rw [show s = p + 1 by omega]
            exact I.unit_mem_intervals p (by omega) (by omega)
        | gate g₁ =>
          have hg₁_op : (c.program.lines g₁).op = .mul := hs_op g₁ hs_id
          have hg₁_w : programWord c.program (.gate g₁) = List.range' p (s - p) := hs_id ▸ hsw
          have hg₁_not0 : 0 ∉ programWord c.program (.gate g₁) := by
            rw [hg₁_w, List.mem_range'_1]; omega
          have hg₁_B : g₁ ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ g₁, hg₁_op⟩
          rw [← hB_eq, Finset.mem_union] at hg₁_B
          have hg₁_F : g₁ ∈ F := by
            rcases hg₁_B with hF1 | hO1
            · exact hF1
            · rcases Finset.mem_image.mp hO1 with ⟨r, _, rfl⟩
              exfalso
              apply hg₁_not0
              rw [hlastWord r, List.mem_range'_1]; omega
          have hg₁_not_sp : g₁ ∉ leftSpine c.program wLast := fun hsp =>
            hg₁_not0 ((zero_mem_ancMul_iff_mem_leftSpine c.program wLast N hN hwLast g₁ hg₁_F).mpr
              hsp)
          rcases hanc_part g₁ hg₁_F with hsp | ⟨r, hrD, hg₁_ur⟩
          · exact absurd hsp hg₁_not_sp
          · obtain ⟨_, _, _, _, _, hur_w⟩ := hseg r hrD
            have hr_lt := (hseg r hrD).1
            obtain ⟨hsub_r, _⟩ := ancMul_range_and_card c.program (u r) (T r) (T (r + 1) - T r)
              (by omega) hur_w
            obtain ⟨p₀, q₀, hp₀, hpq₀, hq₀, hg₁_pq⟩ := hsub_r g₁ hg₁_ur
            obtain ⟨hp_eq_p₀, hlen_eq⟩ := range'_eq_range'_iff (by omega) (hg₁_w.symm.trans hg₁_pq)
            have hq₀_eq : q₀ = s := by omega
            have hrd : r = d := by
              by_contra hne
              rcases lt_or_gt_of_ne hne with hr_lt_d | hd_lt_r
              · have := hT_mono (r + 1) d (by omega) (by omega)
                omega
              · have := hT_mono (d + 1) r (by omega) (by omega)
                omega
            subst hrd
            have hmem_I := hI_anc g₁ hg₁_ur p s (by omega) hg₁_w
            refine ⟨p, by omega, by omega, by simpa only [firstInput] using hw0,
              Finset.mem_erase.mpr ⟨?_, hmem_I⟩⟩
            intro heq; rw [Prod.mk.injEq] at heq; omega
  have hmul_seg_weak : ∀ g : Fin c.size, ∀ s, a < s → s < b →
      (c.program.lines g).op = .mul →
      programWord c.program (.gate g) = List.range' 0 s →
        ∃ p, a ≤ p ∧ p < s ∧
          programWord c.program (firstInput (c.program.lines g)) = List.range' 0 p :=
    fun g s has hsb hop hgw =>
      let ⟨p, hp1, hp2, hpw, _⟩ := hmul_seg g s has hsb hop hgw
      ⟨p, hp1, hp2, hpw⟩
  have hreach_out : ∀ (s : ℕ) (_ : a ≤ s) (_ : s < b),
      segHasOut c a b (c.outputs ⟨s - 1, by omega⟩) = true ∧
        ReachesInSeg c a b root root (c.outputs ⟨s - 1, by omega⟩) := by
    intro s hs1 hs2
    let j : Fin N := ⟨s - 1, by omega⟩
    have hj_has : segHasOut c a b (c.outputs j) = true := by
      simp only [segHasOut, decide_eq_true_eq]
      exact ⟨j, by dsimp only [j]; omega, by dsimp only [j]; omega, rfl⟩
    have hj_act : segActive c a b root (c.outputs j) = true :=
      (segActive_iff c a b root (c.outputs j)).mpr (Or.inl hj_has)
    have hj_w : programWord c.program (c.outputs j) = List.range' 0 s := by
      simpa only [j, show s - 1 + 1 = s by omega] using houtWord j
    exact ⟨hj_has, reaches_root_of_seg_wire c a b hN ha1 root hroot_zero hroot_unique
      hmul_seg_weak (c.outputs j) s hs1 hs2 hj_w hj_act⟩
  have hroot_act : segActive c a b root root = true := by
    obtain ⟨hhas_a, hr_a⟩ := hreach_out a le_rfl hTd_lt
    rcases hr_a.top_inversion with heq | ⟨g, hg, _⟩
    · rw [heq] at hhas_a
      exact (segActive_iff c a b root root).mpr (Or.inl hhas_a)
    · exact (segActive_iff c a b root root).mpr (Or.inr ⟨g, hg⟩)
  let t := buildSegTree c a b root root
  obtain ⟨⟨s_r, _, _, hpw_r, hst_r⟩, hmax_t, hfan_t, hval_t, hd_t⟩ :=
    buildSegTree_props c a b D root I hfan houtWord
      (fun j => c.outputDepths_le_depth j) hroot_unique hmul_seg root hroot_act
  have hsr_eq : s_r = a := by
    have := congrArg List.length (hpw_r.symm.trans hvd_w)
    simpa only [List.length_range'] using this
  have hsg_fi : firstInput (c.program.lines sg) = root := by
    simp only [hsg_line, firstInput, hsg_w0]
  have hsg_not : sg ∉ segChildren c a b root root := by
    intro hsg_mem
    obtain ⟨_, _, hsg_act⟩ := (mem_segChildren_iff c a b root root sg).mp hsg_mem
    obtain ⟨⟨s_sg, _, hs_sg_lt, hpw_sg, _⟩, _⟩ :=
      buildSegTree_props c a b D root I hfan houtWord
        (fun j => c.outputDepths_le_depth j) hroot_unique hmul_seg (.gate sg) hsg_act
    have hpw_b : programWord c.program (.gate sg) = List.range' 0 b := by
      dsimp only [b]
      rw [← hvd_succ]
      by_cases hd1 : d + 1 < D
      · exact (hseg (d + 1) hd1).2.2.2.2.1
      · have hdD : d + 1 = D := by omega
        rw [hdD, hvD, hTD]
        exact hwLast
    have := congrArg List.length (hpw_sg.symm.trans hpw_b)
    simp only [List.length_range'] at this
    omega
  have hroot_bud : t.rootBudget + 1 ≤ k := by
    have hbud_eq : t.rootBudget =
        (segChildren c a b root root).length + (if segHasOut c a b root then 1 else 0) := by
      dsimp only [t]
      rw [buildSegTree_eq]
      rfl
    rw [hbud_eq]
    exact (seg_root_fanout_bound c a b root sg hsg_fi hsg_not).trans (hfan root)
  obtain ⟨hout_cnt, hout_at, hmul_cnt⟩ := buildSegTree_counts c a b root root
  refine ⟨I, t, hI_d.trans hud_d, hst_r.trans hsr_eq, hmax_t, hroot_bud, hfan_t,
    by rw [hvd_d] at hd_t; exact hd_t, hval_t, ?_, ?_, ?_⟩
  · intro s
    change (buildSegTree c a b root root).outAt s ≤ 1
    rw [hout_at s]
    by_cases hs_in : a ≤ s ∧ s < b
    · let u_s := c.outputs ⟨s - 1, by omega⟩
      have hother : ∀ u : Wire N c.size, u ≠ u_s →
          (if segHasOut c a b u = true ∧ wireState c.program u = s then
            countWireInSeg c a b root u root else 0) = 0 := by
        intro u hne
        split_ifs with hc
        · exfalso
          obtain ⟨hhas_u, hws_u⟩ := hc
          simp only [segHasOut, decide_eq_true_eq] at hhas_u
          obtain ⟨j, _, _, rfl⟩ := hhas_u
          have hj_s : j.val + 1 = s := by
            simpa only [wireState, houtWord j, List.length_range'] using hws_u
          apply hne
          dsimp only [u_s]
          congr 1
          exact Fin.ext (by simp only; omega)
        · rfl
      rw [Fintype.sum_eq_single u_s hother]
      split_ifs
      · exact countWireInSeg_le_one c a b root u_s root
      · exact Nat.zero_le _
    · have hzero : ∀ u : Wire N c.size,
          (if segHasOut c a b u = true ∧ wireState c.program u = s then
            countWireInSeg c a b root u root else 0) = 0 := by
        intro u
        split_ifs with hc
        · exfalso
          obtain ⟨hhas_u, hws_u⟩ := hc
          simp only [segHasOut, decide_eq_true_eq] at hhas_u
          obtain ⟨j, hj1, hj2, rfl⟩ := hhas_u
          have hj_s : j.val + 1 = s := by
            simpa only [wireState, houtWord j, List.length_range'] using hws_u
          omega
        · rfl
      simp only [hzero, Finset.sum_const_zero, Nat.zero_le]
  · intro m
    change (buildSegTree c a b root root).mulCount m ≤ 1
    rw [hmul_cnt m]
    by_cases hm_in : 2 ≤ m ∧ m ≤ N
    · let g_m := lastMul ⟨m - 2, by omega⟩
      have hother : ∀ g : Fin c.size, g ≠ g_m →
          (if (c.program.lines g).op = .mul ∧ wireState c.program (.gate g) = m ∧
              root ≠ .gate g then
            countWireInSeg c a b root (.gate g) root else 0) = 0 := by
        intro g hne
        split_ifs with hc
        · by_cases hcnt : countWireInSeg c a b root (.gate g) root = 0
          · exact hcnt
          · exfalso
            have hr := reaches_of_countWireInSeg_ne_zero hcnt
            have hact_g := hr.segActive_of hroot_act
            obtain ⟨⟨s_g, _, _, hpw_g, _⟩, _⟩ :=
              buildSegTree_props c a b D root I hfan houtWord
                (fun j => c.outputDepths_le_depth j) hroot_unique hmul_seg (.gate g) hact_g
            have hsm : s_g = m := by
              simpa only [wireState, hpw_g, List.length_range'] using hc.2.1
            rw [hsm] at hpw_g
            exact hne (hmul_unique g m hm_in.1 hm_in.2 hc.1 hpw_g)
        · rfl
      rw [Fintype.sum_eq_single g_m hother]
      split_ifs
      · exact countWireInSeg_le_one c a b root (.gate g_m) root
      · exact Nat.zero_le _
    · have hzero : ∀ g : Fin c.size,
          (if (c.program.lines g).op = .mul ∧ wireState c.program (.gate g) = m ∧
              root ≠ .gate g then
            countWireInSeg c a b root (.gate g) root else 0) = 0 := by
        intro g
        split_ifs with hc
        · by_cases hcnt : countWireInSeg c a b root (.gate g) root = 0
          · exact hcnt
          · exfalso
            have hr := reaches_of_countWireInSeg_ne_zero hcnt
            have hact_g := hr.segActive_of hroot_act
            obtain ⟨⟨s_g, hs1_g, hs2_g, hpw_g, _⟩, _⟩ :=
              buildSegTree_props c a b D root I hfan houtWord
                (fun j => c.outputDepths_le_depth j) hroot_unique hmul_seg (.gate g) hact_g
            have hsm : s_g = m := by
              simpa only [wireState, hpw_g, List.length_range'] using hc.2.1
            have hm2 : 2 ≤ m := by
              by_contra hm_lt2
              have hm_eq_a : m = a := by omega
              rw [hsm, hm_eq_a] at hpw_g
              exact hc.2.2 (hroot_unique g hc.1 hpw_g).symm
            omega
        · rfl
      simp only [hzero, Finset.sum_const_zero, Nat.zero_le]
  · change b - a ≤ (buildSegTree c a b root root).outCount
    rw [hout_cnt]
    let outMap : ℕ → Wire N c.size := fun s =>
      if hs : a ≤ s ∧ s < b then c.outputs ⟨s - 1, by omega⟩ else root
    let fCnt : Wire N c.size → ℕ := fun u =>
      if segHasOut c a b u = true then countWireInSeg c a b root u root else 0
    have hinj : Set.InjOn outMap (Finset.Ico a b) := by
      intro s₁ hs₁ s₂ hs₂ heq
      rw [Finset.mem_coe, Finset.mem_Ico] at hs₁ hs₂
      simp only [outMap, hs₁, hs₂, and_self, ↓reduceDIte] at heq
      have hw := congrArg (fun w => (programWord c.program w).length) heq
      simp only [houtWord, List.length_range'] at hw
      omega
    calc
      b - a = ∑ _s ∈ Finset.Ico a b, 1 := by
        rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul, Nat.mul_one]
      _ ≤ ∑ s ∈ Finset.Ico a b, fCnt (outMap s) := by
        refine Finset.sum_le_sum fun s hs => ?_
        rw [Finset.mem_Ico] at hs
        have h_eq : outMap s = c.outputs ⟨s - 1, by omega⟩ := by
          simp only [outMap, hs, and_self, ↓reduceDIte]
        dsimp only [fCnt]
        rw [h_eq]
        obtain ⟨hhas_s, hr_s⟩ := hreach_out s hs.1 hs.2
        rw [countWireInSeg_eq_one_of_reaches hr_s]
        simp only [hhas_s, ↓reduceIte, le_rfl]
      _ = ∑ u ∈ (Finset.Ico a b).image outMap, fCnt u :=
        (Finset.sum_image (f := fCnt) hinj).symm
      _ ≤ ∑ u : Wire N c.size, fCnt u :=
        Finset.sum_le_sum_of_subset fun u _ => Finset.mem_univ u

/-- Exact maximum width bound for optimal fanout-2 prefix circuits of positive depth:
`N ≤ 1 + w_2*(c.depth - 1)` ([Sergeev2025PrefixDepth], p. 3, `w_2(D) = w_2*(D - 1)`). -/
theorem width_le_one_add_maxCircuitWidthUpper_two {N : ℕ} (hN : 1 ≤ N)
    {c : PrefixCircuit N} (hopt : IsOptimalPrefixCircuit c) (hfan : FanoutAtMost c 2)
    (hD : 1 ≤ c.depth) :
    N ≤ 1 + maxCircuitWidthUpper 2 (c.depth - 1) := by
  obtain ⟨T, hT0, hTD, hseg⟩ := optimal_segment_decomposition hN hopt hfan
  set D := c.depth
  have htele : ∀ r ≤ D, T r = 1 + ∑ d ∈ Finset.range r, (T (d + 1) - T d) := by
    intro r hr
    induction r with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, Nat.add_zero, hT0]
    | succ r ih =>
      rw [Finset.sum_range_succ, ← Nat.add_assoc, ← ih (by omega)]
      have hlt := (hseg r (by omega)).1
      omega
  rw [← hTD, htele D le_rfl]
  unfold maxCircuitWidthUpper
  rw [show D - 1 + 1 = D by omega]
  refine Nat.add_le_add_left (Finset.sum_le_sum fun d hd => ?_) 1
  rw [Finset.mem_range] at hd
  obtain ⟨hTd_lt, I, t, hI_d, _, _, hbud, hfan_t, hd_t, _, hout_at, _, hw_le⟩ := hseg d hd
  rw [maxConsistentWidth_two]
  have hd_bound : T (d + 1) - T d ≤ 2 ^ d :=
    (I.width_le_two_pow).trans (Nat.pow_le_pow_right (by omega) hI_d)
  have hh_bound : T (d + 1) - T d ≤ 2 ^ (D - 1 - d) := by
    rcases t with ⟨st, hasOut, r, isMul, child⟩
    simp only [GenPrefixTree.rootBudget] at hbud
    obtain ⟨_, hch_fan⟩ := hfan_t
    have hch_out : ∀ i : Fin r, ∀ s, (child i).outAt s ≤ 1 := by
      intro i s
      have hs := hout_at s
      simp only [GenPrefixTree.outAt] at hs
      have hle : (child i).outAt s ≤ ∑ j : Fin r, (child j).outAt s :=
        Finset.single_le_sum (f := fun j : Fin r => (child j).outAt s)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    by_cases hr0 : r = 0
    · subst hr0
      simp only [GenPrefixTree.outCount, Finset.univ_eq_empty, Finset.sum_empty] at hw_le
      have h1 : 1 ≤ 2 ^ (D - 1 - d) := Nat.one_le_pow _ _ (by omega)
      cases hasOut <;> simp only [Bool.false_eq_true, ↓reduceIte] at hw_le <;> omega
    · have hr1 : r = 1 := by omega
      have hno_out : hasOut = false := by
        cases hasOut
        · rfl
        · simp only [↓reduceIte] at hbud; omega
      subst hr1 hno_out
      simp only [GenPrefixTree.outCount, Bool.false_eq_true, ↓reduceIte,
        Nat.zero_add, Fin.sum_univ_one] at hw_le
      have hc0_d : (child 0).depth + 1 ≤
          (GenPrefixTree.node st false 1 isMul child).depth :=
        GenPrefixTree.child_depth_lt 0
      have hc0_ub := (child 0).outCount_le_two_pow (hch_fan 0) (hch_out 0)
      exact hw_le.trans (hc0_ub.trans (Nat.pow_le_pow_right (by omega) (by omega)))
  by_cases hmin : d ≤ D - 1 - d
  · rw [Nat.min_eq_left hmin]; exact hd_bound
  · rw [Nat.min_eq_right (by omega)]; exact hh_bound

/-- Every optimal fanout-2 prefix circuit on `N ≥ 1` inputs satisfies
`N ≤ maxCircuitWidthUpper 2 c.depth` ([Sergeev2025PrefixDepth], p. 3, Eq. (3)). -/
theorem width_le_maxCircuitWidthUpper_two {N : ℕ} (hN : 1 ≤ N)
    {c : PrefixCircuit N} (hopt : IsOptimalPrefixCircuit c) (hfan : FanoutAtMost c 2) :
    N ≤ maxCircuitWidthUpper 2 c.depth := by
  by_cases hD0 : c.depth = 0
  · obtain ⟨T, hT0, hTD, _⟩ := optimal_segment_decomposition hN hopt hfan
    rw [hD0, hT0] at hTD
    rw [hD0]
    unfold maxCircuitWidthUpper
    rw [Finset.range_one, Finset.sum_singleton, Nat.sub_zero,
      maxConsistentWidth_zero_left (by omega)]
    omega
  · refine (width_le_one_add_maxCircuitWidthUpper_two hN hopt hfan (by omega)).trans ?_
    set D := c.depth
    unfold maxCircuitWidthUpper
    rw [show D - 1 + 1 = D by omega, Finset.sum_range_succ, Nat.sub_self,
      maxConsistentWidth_zero_right (by omega), Nat.add_comm 1]
    refine Nat.add_le_add_right (Finset.sum_le_sum fun d hd => ?_) 1
    rw [maxConsistentWidth_two, maxConsistentWidth_two]
    exact Nat.pow_le_pow_right (by omega) (by omega)

/-! #### General `k ≥ 3` real segment bound `V_k(d, h)` and `V_k*(D)` recurrence -/

private noncomputable def V (k : ℕ) : ℕ → ℕ → ℝ
  | d, 0 => (3 / 2 : ℝ) ^ d
  | 0, _ + 1 => 1
  | d + 1, h + 1 =>
      let l := min (d + 1) (k - 1)
      (∑ i ∈ Finset.Ico 1 l, V k (d + 1 - i) h) + 2 * V k (d + 1 - l) h

private theorem V_zero_right (k d : ℕ) : V k d 0 = (3 / 2 : ℝ) ^ d := by
  cases d <;> rfl

private theorem V_zero_left (k h : ℕ) : V k 0 h = 1 := by
  cases h <;> simp only [V, pow_zero]

private theorem V_one_le (k d h : ℕ) : (1 : ℝ) ≤ V k d h := by
  induction h generalizing d with
  | zero =>
    rw [V_zero_right]
    exact one_le_pow₀ (by norm_num)
  | succ h ih =>
    cases d with
    | zero => rw [V_zero_left]
    | succ d =>
      change (1 : ℝ) ≤
        (∑ i ∈ Finset.Ico 1 (min (d + 1) (k - 1)), V k (d + 1 - i) h) +
          2 * V k (d + 1 - min (d + 1) (k - 1)) h
      have hsum : (0 : ℝ) ≤ ∑ i ∈ Finset.Ico 1 (min (d + 1) (k - 1)), V k (d + 1 - i) h :=
        Finset.sum_nonneg fun i _ => ( zero_le_one.trans (ih _) )
      have hlast := ih (d + 1 - min (d + 1) (k - 1))
      linarith

private theorem V_nonneg (k d h : ℕ) : (0 : ℝ) ≤ V k d h :=
  zero_le_one.trans (V_one_le k d h)

private theorem V_one_left {k : ℕ} (hk : 2 ≤ k) (h : ℕ) : V k 1 (h + 1) = 2 := by
  have hl : min 1 (k - 1) = 1 := Nat.min_eq_left (by omega)
  change (∑ i ∈ Finset.Ico 1 (min 1 (k - 1)), V k (1 - i) h) +
      2 * V k (1 - min 1 (k - 1)) h = 2
  rw [hl, Finset.Ico_self, Finset.sum_empty, zero_add, Nat.sub_self, V_zero_left, mul_one]

private theorem V_succ_sub_self_small {k d : ℕ} (hd : d + 1 ≤ k - 1) (h : ℕ) :
    V k (d + 1) (h + 1) - V k d (h + 1) =
      if d = 0 then 1 else V k d h := by
  cases d with
  | zero =>
    have hk2 : 2 ≤ k := by omega
    rw [V_one_left hk2, V_zero_left]
    norm_num
  | succ m =>
    have hl1 : min (m + 1) (k - 1) = m + 1 := Nat.min_eq_left (by omega)
    have hl2 : min (m + 2) (k - 1) = m + 2 := Nat.min_eq_left hd
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    change ((∑ i ∈ Finset.Ico 1 (min (m + 2) (k - 1)), V k (m + 2 - i) h) +
        2 * V k (m + 2 - min (m + 2) (k - 1)) h) -
      ((∑ i ∈ Finset.Ico 1 (min (m + 1) (k - 1)), V k (m + 1 - i) h) +
        2 * V k (m + 1 - min (m + 1) (k - 1)) h) = V k (m + 1) h
    rw [hl1, hl2, Nat.sub_self, Nat.sub_self, V_zero_left,
      sum_Ico_one_succ_shift (l := m + 1) (by omega) (m + 1) (fun x => V k x h)]
    ring

private theorem V_step_le_mul {k a b h : ℕ} {c : ℝ} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : k - 1 ≤ a) (hb : k - 1 ≤ b)
    (hstep : ∀ i ≤ k - 1, V k (a - i) h ≤ c * V k (b - i) h) :
    V k a (h + 1) ≤ c * V k b (h + 1) := by
  have hrec (n : ℕ) (hn : n ≠ 0) : V k n (h + 1) =
      (∑ i ∈ Finset.Ico 1 (min n (k - 1)), V k (n - i) h) + 2 * V k (n - min n (k - 1)) h := by
    cases n with
    | zero => exact (hn rfl).elim
    | succ m => rfl
  rw [hrec a ha0, hrec b hb0, Nat.min_eq_right ha, Nat.min_eq_right hb,
    mul_add, Finset.mul_sum]
  have hsum : ∑ i ∈ Finset.Ico 1 (k - 1), V k (a - i) h ≤
      ∑ i ∈ Finset.Ico 1 (k - 1), c * V k (b - i) h := by
    refine Finset.sum_le_sum fun i hi => ?_
    simp only [Finset.mem_Ico] at hi
    exact hstep i (by omega)
  have hlast := hstep (k - 1) le_rfl
  linarith

private theorem V_mono_left (k : ℕ) :
    ∀ d h : ℕ, V k d h ≤ V k (d + 1) h := by
  intro d h
  induction h generalizing d with
  | zero =>
    simp only [V_zero_right, pow_succ]
    have hp : (0 : ℝ) ≤ (3 / 2 : ℝ) ^ d := by positivity
    linarith
  | succ h ih =>
    cases d with
    | zero =>
      rw [V_zero_left]
      exact V_one_le k 1 (h + 1)
    | succ d =>
      by_cases hle : d + 2 ≤ k - 1
      · have hdiff := V_succ_sub_self_small hle h
        simp only [Nat.succ_ne_zero, ↓reduceIte] at hdiff
        have hpos := V_nonneg k (d + 1) h
        linarith
      · simpa only [one_mul] using
          V_step_le_mul (c := 1) (by omega) (by omega) (by omega) (by omega) fun i hi => by
            rw [show d + 2 - i = (d + 1 - i) + 1 by omega, one_mul]
            exact ih _

private theorem V_mono_right {k : ℕ} (hk : 3 ≤ k) :
    ∀ d h : ℕ, V k d h ≤ V k d (h + 1) := by
  intro d h
  induction h generalizing d with
  | zero =>
    cases d with
    | zero => simp only [V_zero_left, le_rfl]
    | succ m =>
      cases m with
      | zero =>
        rw [V_zero_right, pow_one, V_one_left (by omega)]
        norm_num
      | succ n =>
        set l := min (n + 2) (k - 1)
        have hl_ge2 : 2 ≤ l := by dsimp only [l]; omega
        change (3 / 2 : ℝ) ^ (n + 2) ≤
          (∑ i ∈ Finset.Ico 1 l, V k (n + 2 - i) 0) + 2 * V k (n + 2 - l) 0
        have hp_base : (0 : ℝ) ≤ (3 / 2 : ℝ) ^ n := by positivity
        by_cases hl2 : l = 2
        · rw [hl2]
          have h1 : Finset.Ico 1 2 = {1} := by decide
          rw [h1, Finset.sum_singleton, show n + 2 - 1 = n + 1 by omega,
            show n + 2 - 2 = n by omega, V_zero_right, V_zero_right]
          have hpow1 : (3 / 2 : ℝ) ^ (n + 1) = (3 / 2) * (3 / 2 : ℝ) ^ n := by ring
          have hpow2 : (3 / 2 : ℝ) ^ (n + 2) = (9 / 4) * (3 / 2 : ℝ) ^ n := by ring
          linarith
        · have hl3 : 3 ≤ l := by omega
          have hsub : ({1, 2} : Finset ℕ) ⊆ Finset.Ico 1 l := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            simp only [Finset.mem_Ico]
            omega
          have hpair : ∑ i ∈ ({1, 2} : Finset ℕ), V k (n + 2 - i) 0 ≤
              ∑ i ∈ Finset.Ico 1 l, V k (n + 2 - i) 0 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => V_nonneg k _ 0
          rw [Finset.sum_pair (by decide), show n + 2 - 1 = n + 1 by omega,
            show n + 2 - 2 = n by omega, V_zero_right, V_zero_right] at hpair
          have hlast := V_nonneg k (n + 2 - l) 0
          have hpow1 : (3 / 2 : ℝ) ^ (n + 1) = (3 / 2) * (3 / 2 : ℝ) ^ n := by ring
          have hpow2 : (3 / 2 : ℝ) ^ (n + 2) = (9 / 4) * (3 / 2 : ℝ) ^ n := by ring
          linarith
  | succ h ih =>
    cases d with
    | zero => simp only [V_zero_left, le_rfl]
    | succ d =>
      set l := min (d + 1) (k - 1)
      change (∑ i ∈ Finset.Ico 1 l, V k (d + 1 - i) h) + 2 * V k (d + 1 - l) h ≤
        (∑ i ∈ Finset.Ico 1 l, V k (d + 1 - i) (h + 1)) + 2 * V k (d + 1 - l) (h + 1)
      have hsum : ∑ i ∈ Finset.Ico 1 l, V k (d + 1 - i) h ≤
          ∑ i ∈ Finset.Ico 1 l, V k (d + 1 - i) (h + 1) :=
        Finset.sum_le_sum fun i _ => ih _
      have hlast := ih (d + 1 - l)
      linarith

private theorem V_le_two_mul {k : ℕ} (hk : 3 ≤ k) :
    ∀ d h : ℕ, V k (d + 1) h ≤ 2 * V k d h := by
  intro d h
  induction h generalizing d with
  | zero =>
    simp only [V_zero_right, pow_succ]
    have hp : (0 : ℝ) ≤ (3 / 2 : ℝ) ^ d := by positivity
    linarith
  | succ h ih =>
    cases d with
    | zero =>
      rw [V_one_left (by omega), V_zero_left]
      norm_num
    | succ m =>
      by_cases hle : m + 2 ≤ k - 1
      · have hdiff := V_succ_sub_self_small hle h
        simp only [Nat.succ_ne_zero, ↓reduceIte] at hdiff
        have hmr := V_mono_right hk (m + 1) h
        linarith
      · exact V_step_le_mul (c := 2) (by omega) (by omega) (by omega) (by omega) fun i hi => by
          rw [show m + 2 - i = (m + 1 - i) + 1 by omega]
          exact ih _

private theorem V_three_term {k : ℕ} (hk : 3 ≤ k) :
    ∀ n h : ℕ, 2 * V k n h + V k (n + 2) h ≤ 3 * V k (n + 1) h := by
  intro n h
  induction h generalizing n with
  | zero =>
    simp only [V_zero_right]
    have hp : (0 : ℝ) ≤ (3 / 2 : ℝ) ^ n := by positivity
    have hp1 : (3 / 2 : ℝ) ^ (n + 1) = (3 / 2) * (3 / 2 : ℝ) ^ n := by ring
    have hp2 : (3 / 2 : ℝ) ^ (n + 2) = (9 / 4) * (3 / 2 : ℝ) ^ n := by ring
    linarith
  | succ h ih =>
    cases n with
    | zero =>
      rw [V_zero_left, V_one_left (by omega)]
      have h2 := V_le_two_mul hk 1 (h + 1)
      rw [V_one_left (by omega)] at h2
      linarith
    | succ m =>
      by_cases h1 : m + 3 ≤ k - 1
      · have hd1 := V_succ_sub_self_small (by omega : m + 2 ≤ k - 1) h
        have hd2 := V_succ_sub_self_small h1 h
        simp only [Nat.succ_ne_zero, ↓reduceIte] at hd1 hd2
        have htwo := V_le_two_mul hk (m + 1) h
        linarith
      · by_cases h2 : m + 2 = k - 1
        · have hd1 := V_succ_sub_self_small (by omega : m + 2 ≤ k - 1) h
          simp only [Nat.succ_ne_zero, ↓reduceIte] at hd1
          have hl2 : min (m + 2) (k - 1) = m + 2 := Nat.min_eq_left (by omega)
          have hl3 : min (m + 3) (k - 1) = m + 2 := by rw [← h2]; exact Nat.min_eq_right (by omega)
          have hd2 : V k (m + 3) (h + 1) - V k (m + 2) (h + 1) =
              V k (m + 2) h + V k 1 h - 2 * V k 0 h := by
            change ((∑ i ∈ Finset.Ico 1 (min (m + 3) (k - 1)), V k (m + 3 - i) h) +
                2 * V k (m + 3 - min (m + 3) (k - 1)) h) -
              ((∑ i ∈ Finset.Ico 1 (min (m + 2) (k - 1)), V k (m + 2 - i) h) +
                2 * V k (m + 2 - min (m + 2) (k - 1)) h) = _
            rw [hl2, hl3, show m + 3 - (m + 2) = 1 by omega, Nat.sub_self]
            have hsum_tel : (∑ i ∈ Finset.Ico 1 (m + 2), V k (m + 3 - i) h) -
                (∑ i ∈ Finset.Ico 1 (m + 2), V k (m + 2 - i) h) =
                V k (m + 2) h - V k 1 h := by
              have hleft : ∑ i ∈ Finset.Ico 1 (m + 2), V k (m + 3 - i) h =
                  V k (m + 2) h + ∑ j ∈ Finset.Ico 1 (m + 1), V k (m + 2 - j) h :=
                sum_Ico_one_succ_shift (l := m + 1) (by omega) (m + 2) (fun x => V k x h)
              have hright : ∑ i ∈ Finset.Ico 1 (m + 2), V k (m + 2 - i) h =
                  (∑ j ∈ Finset.Ico 1 (m + 1), V k (m + 2 - j) h) + V k 1 h := by
                rw [Finset.sum_Ico_succ_top (by omega) (fun i => V k (m + 2 - i) h),
                  show m + 2 - (m + 1) = 1 by omega]
              rw [hleft, hright]
              ring
            linarith
          have hv1 : V k 1 h ≤ 2 * V k 0 h := V_le_two_mul hk 0 h
          have htwo := V_le_two_mul hk (m + 1) h
          linarith
        · have hl1 : min (m + 1) (k - 1) = k - 1 := Nat.min_eq_right (by omega)
          have hl2 : min (m + 2) (k - 1) = k - 1 := Nat.min_eq_right (by omega)
          have hl3 : min (m + 3) (k - 1) = k - 1 := Nat.min_eq_right (by omega)
          change 2 * ((∑ i ∈ Finset.Ico 1 (min (m + 1) (k - 1)), V k (m + 1 - i) h) +
              2 * V k (m + 1 - min (m + 1) (k - 1)) h) +
            ((∑ i ∈ Finset.Ico 1 (min (m + 3) (k - 1)), V k (m + 3 - i) h) +
              2 * V k (m + 3 - min (m + 3) (k - 1)) h) ≤
            3 * ((∑ i ∈ Finset.Ico 1 (min (m + 2) (k - 1)), V k (m + 2 - i) h) +
              2 * V k (m + 2 - min (m + 2) (k - 1)) h)
          rw [hl1, hl2, hl3, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
          have hsum : (∑ i ∈ Finset.Ico 1 (k - 1), 2 * V k (m + 1 - i) h) +
              (∑ i ∈ Finset.Ico 1 (k - 1), V k (m + 3 - i) h) ≤
              ∑ i ∈ Finset.Ico 1 (k - 1), 3 * V k (m + 2 - i) h := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_le_sum fun i hi => ?_
            simp only [Finset.mem_Ico] at hi
            rw [show m + 3 - i = (m + 1 - i) + 2 by omega,
              show m + 2 - i = (m + 1 - i) + 1 by omega]
            exact ih (m + 1 - i)
          have hlast : 2 * V k (m + 1 - (k - 1)) h + V k (m + 3 - (k - 1)) h ≤
              3 * V k (m + 2 - (k - 1)) h := by
            rw [show m + 3 - (k - 1) = (m + 1 - (k - 1)) + 2 by omega,
              show m + 2 - (k - 1) = (m + 1 - (k - 1)) + 1 by omega]
            exact ih _
          linarith

private theorem V_one_mul_three_halves {k n : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n) :
    V k (n + 1) 1 = (3 / 2 : ℝ) * V k n 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hl1 : min (m + 1) (k - 1) = k - 1 := Nat.min_eq_right (by omega)
  have hl2 : min (m + 2) (k - 1) = k - 1 := Nat.min_eq_right (by omega)
  change (∑ i ∈ Finset.Ico 1 (min (m + 2) (k - 1)), V k (m + 2 - i) 0) +
      2 * V k (m + 2 - min (m + 2) (k - 1)) 0 =
    (3 / 2 : ℝ) * ((∑ i ∈ Finset.Ico 1 (min (m + 1) (k - 1)), V k (m + 1 - i) 0) +
      2 * V k (m + 1 - min (m + 1) (k - 1)) 0)
  rw [hl1, hl2, mul_add, Finset.mul_sum]
  have hsum : ∑ i ∈ Finset.Ico 1 (k - 1), V k (m + 2 - i) 0 =
      ∑ i ∈ Finset.Ico 1 (k - 1), (3 / 2 : ℝ) * V k (m + 1 - i) 0 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_Ico] at hi
    rw [show m + 2 - i = (m + 1 - i) + 1 by omega, V_zero_right, V_zero_right, pow_succ]
    ring
  have hlast : V k (m + 2 - (k - 1)) 0 = (3 / 2 : ℝ) * V k (m + 1 - (k - 1)) 0 := by
    rw [show m + 2 - (k - 1) = (m + 1 - (k - 1)) + 1 by omega, V_zero_right, V_zero_right,
      pow_succ]
    ring
  rw [hsum, hlast]
  ring

private theorem pow_le_V_one {k : ℕ} (hk : 3 ≤ k) :
    ∀ n : ℕ, 2 ≤ n → (3 / 2 : ℝ) ^ (n + 1) ≤ V k n 1 := by
  intro n hn
  induction hn with
  | refl =>
    have hl : min 2 (k - 1) = 2 := Nat.min_eq_left (by omega)
    change (3 / 2 : ℝ) ^ 3 ≤
      (∑ i ∈ Finset.Ico 1 (min 2 (k - 1)), V k (2 - i) 0) + 2 * V k (2 - min 2 (k - 1)) 0
    rw [hl, show Finset.Ico 1 2 = {1} by decide, Finset.sum_singleton, V_zero_right, V_zero_right]
    norm_num
  | @step m hm ih =>
    change (3 / 2 : ℝ) ^ (m + 2) ≤ V k (m + 1) 1
    have hm_ge2 : 2 ≤ m := hm
    by_cases hsmall : m + 1 ≤ k - 1
    · have hm0 : m ≠ 0 := by omega
      have hdiff := V_succ_sub_self_small hsmall 0
      simp only [Nat.zero_add, hm0, ↓reduceIte, V_zero_right] at hdiff
      have hp : (0 : ℝ) ≤ (3 / 2 : ℝ) ^ m := by positivity
      have hp1 : (3 / 2 : ℝ) ^ (m + 1) = (3 / 2) * (3 / 2 : ℝ) ^ m := by ring
      have hp2 : (3 / 2 : ℝ) ^ (m + 2) = (9 / 4) * (3 / 2 : ℝ) ^ m := by ring
      linarith
    · have hmul := V_one_mul_three_halves hk (by omega : k - 1 ≤ m)
      have hp2 : (3 / 2 : ℝ) ^ (m + 2) = (3 / 2) * (3 / 2 : ℝ) ^ (m + 1) := by ring
      linarith

private theorem V_step_ineq {k : ℕ} (hk : 3 ≤ k) :
    ∀ n h : ℕ, V k (n + 1) h + 2 * V k n (h + 1) ≤ 2 * V k (n + 1) (h + 1) := by
  intro n h
  induction h generalizing n with
  | zero =>
    cases n with
    | zero =>
      rw [V_zero_right, pow_one, V_zero_left, V_one_left (by omega)]
      norm_num
    | succ m =>
      change V k (m + 2) 0 + 2 * V k (m + 1) 1 ≤ 2 * V k (m + 2) 1
      rw [V_zero_right]
      by_cases hsmall : m + 2 ≤ k - 1
      · have hdiff := V_succ_sub_self_small hsmall 0
        simp only [Nat.zero_add, Nat.succ_ne_zero, ↓reduceIte, V_zero_right] at hdiff
        have hp : (0 : ℝ) ≤ (3 / 2 : ℝ) ^ (m + 1) := by positivity
        have hp1 : (3 / 2 : ℝ) ^ (m + 2) = (3 / 2) * (3 / 2 : ℝ) ^ (m + 1) := by ring
        linarith
      · have hm_ge : k - 1 ≤ m + 1 := by omega
        have hmul := V_one_mul_three_halves hk hm_ge
        have hpow := pow_le_V_one hk (m + 1) (by omega)
        linarith
  | succ h ih =>
    cases n with
    | zero =>
      rw [V_one_left (by omega), V_zero_left, V_one_left (by omega)]
      norm_num
    | succ m =>
      by_cases hsmall : m + 2 ≤ k - 1
      · have hdiff := V_succ_sub_self_small hsmall (h + 1)
        simp only [Nat.succ_ne_zero, ↓reduceIte] at hdiff
        have htwo := V_le_two_mul hk (m + 1) (h + 1)
        linarith
      · have hl1 : min (m + 1) (k - 1) = k - 1 := Nat.min_eq_right (by omega)
        have hl2 : min (m + 2) (k - 1) = k - 1 := Nat.min_eq_right (by omega)
        change ((∑ i ∈ Finset.Ico 1 (min (m + 2) (k - 1)), V k (m + 2 - i) h) +
            2 * V k (m + 2 - min (m + 2) (k - 1)) h) +
          2 * ((∑ i ∈ Finset.Ico 1 (min (m + 1) (k - 1)), V k (m + 1 - i) (h + 1)) +
            2 * V k (m + 1 - min (m + 1) (k - 1)) (h + 1)) ≤
          2 * ((∑ i ∈ Finset.Ico 1 (min (m + 2) (k - 1)), V k (m + 2 - i) (h + 1)) +
            2 * V k (m + 2 - min (m + 2) (k - 1)) (h + 1))
        rw [hl1, hl2, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
        have hsum : (∑ i ∈ Finset.Ico 1 (k - 1), V k (m + 2 - i) h) +
            (∑ i ∈ Finset.Ico 1 (k - 1), 2 * V k (m + 1 - i) (h + 1)) ≤
            ∑ i ∈ Finset.Ico 1 (k - 1), 2 * V k (m + 2 - i) (h + 1) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_le_sum fun i hi => ?_
          simp only [Finset.mem_Ico] at hi
          rw [show m + 2 - i = (m + 1 - i) + 1 by omega]
          exact ih (m + 1 - i)
        have hlast : V k (m + 2 - (k - 1)) h + 2 * V k (m + 1 - (k - 1)) (h + 1) ≤
            2 * V k (m + 2 - (k - 1)) (h + 1) := by
          rw [show m + 2 - (k - 1) = (m + 1 - (k - 1)) + 1 by omega]
          exact ih _
        linarith

private noncomputable def W (k r d : ℕ) : ℕ → ℝ
  | 0 => (3 / 2 : ℝ) ^ d
  | h + 1 =>
      if r = 0 then 0
      else if r = 1 then V k d h
      else if d = 0 then 1
      else
        let l := min d (r - 1)
        (∑ i ∈ Finset.Ico 1 l, V k (d - i) h) + 2 * V k (d - l) h

private theorem W_eq_V {k : ℕ} (hk : 2 ≤ k) (d h : ℕ) : W k k d h = V k d h := by
  cases h with
  | zero => rw [W, V_zero_right]
  | succ h =>
    unfold W
    have hk0 : k ≠ 0 := by omega
    have hk1 : k ≠ 1 := by omega
    simp only [hk0, hk1, ↓reduceIte]
    cases d with
    | zero => simp only [↓reduceIte, V_zero_left]
    | succ d => simp only [Nat.succ_ne_zero, ↓reduceIte]; rfl

private theorem W_one_le {k r : ℕ} (hr : 1 ≤ r) (d h : ℕ) : (1 : ℝ) ≤ W k r d h := by
  cases h with
  | zero =>
    unfold W
    exact one_le_pow₀ (by norm_num)
  | succ h =>
    unfold W
    have hr0 : r ≠ 0 := by omega
    simp only [hr0, ↓reduceIte]
    by_cases hr1 : r = 1
    · simp only [hr1, ↓reduceIte]; exact V_one_le k d h
    · simp only [hr1, ↓reduceIte]
      by_cases hd0 : d = 0
      · simp only [hd0, ↓reduceIte, le_rfl]
      · simp only [hd0, ↓reduceIte]
        have hsum : (0 : ℝ) ≤ ∑ i ∈ Finset.Ico 1 (min d (r - 1)), V k (d - i) h :=
          Finset.sum_nonneg fun i _ => V_nonneg k _ h
        have hlast := V_one_le k (d - min d (r - 1)) h
        linarith

private theorem W_mono_budget {k : ℕ} (hk : 3 ≤ k) :
    ∀ {r₁ r₂ : ℕ}, r₁ ≤ r₂ → ∀ d h : ℕ, W k r₁ d h ≤ W k r₂ d h := by
  have hstep : ∀ r d h, W k r d h ≤ W k (r + 1) d h := by
    intro r d h
    cases h with
    | zero => simp only [W, le_rfl]
    | succ h =>
      cases r with
      | zero =>
        simp only [W, ↓reduceIte]
        exact V_nonneg k d h
      | succ m =>
        cases m with
        | zero =>
          simp only [W, ↓reduceIte, show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega]
          cases d with
          | zero => simp only [Nat.succ_ne_zero, ↓reduceIte, V_zero_left, le_rfl]
          | succ d' =>
            have hl : min (d' + 1) (2 - 1) = 1 := Nat.min_eq_right (by omega)
            simp only [Nat.succ_ne_zero, ↓reduceIte, hl, Finset.Ico_self, Finset.sum_empty,
              zero_add, Nat.add_sub_cancel]
            exact V_le_two_mul hk d' h
        | succ n =>
          have hr1_0 : n + 2 ≠ 0 := by omega
          have hr1_1 : n + 2 ≠ 1 := by omega
          have hr2_0 : n + 3 ≠ 0 := by omega
          have hr2_1 : n + 3 ≠ 1 := by omega
          simp only [W, hr1_0, hr1_1, hr2_0, hr2_1, ↓reduceIte]
          by_cases hd0 : d = 0
          · simp only [hd0, ↓reduceIte, le_rfl]
          · simp only [hd0, ↓reduceIte]
            by_cases hd_le : d ≤ n + 1
            · have hl1 : min d (n + 2 - 1) = d := Nat.min_eq_left hd_le
              have hl2 : min d (n + 3 - 1) = d := Nat.min_eq_left (by omega)
              rw [hl1, hl2]
            · have hl1 : min d (n + 2 - 1) = n + 1 := Nat.min_eq_right (by omega)
              have hl2 : min d (n + 3 - 1) = n + 2 := Nat.min_eq_right (by omega)
              have hsplit_sum : ∑ i ∈ Finset.Ico 1 (n + 2), V k (d - i) h =
                  (∑ i ∈ Finset.Ico 1 (n + 1), V k (d - i) h) + V k (d - (n + 1)) h :=
                Finset.sum_Ico_succ_top (by omega) (fun i => V k (d - i) h)
              rw [hl1, hl2, hsplit_sum]
              have htwo : V k (d - (n + 1)) h ≤ 2 * V k (d - (n + 2)) h := by
                rw [show d - (n + 1) = (d - (n + 2)) + 1 by omega]
                exact V_le_two_mul hk _ h
              linarith
  intro r₁ r₂ hr d h
  induction hr with
  | refl => exact le_rfl
  | @step m _ ih => exact ih.trans (hstep m d h)

private theorem W_mono_left (k : ℕ) :
    ∀ r d h : ℕ, W k r d h ≤ W k r (d + 1) h := by
  intro r d h
  cases h with
  | zero =>
    simp only [W, pow_succ]
    have hp : (0 : ℝ) ≤ (3 / 2 : ℝ) ^ d := by positivity
    linarith
  | succ h =>
    by_cases hr0 : r = 0
    · simp only [W, hr0, ↓reduceIte, le_rfl]
    · by_cases hr1 : r = 1
      · simp only [W, hr1, ↓reduceIte]
        exact V_mono_left k d h
      · simp only [W, hr0, hr1, ↓reduceIte, Nat.succ_ne_zero]
        by_cases hd0 : d = 0
        · subst hd0
          have hl : min 1 (r - 1) = 1 := Nat.min_eq_left (by omega)
          simp only [↓reduceIte, hl, Finset.Ico_self, Finset.sum_empty, zero_add, Nat.sub_self,
            V_zero_left]
          norm_num
        · simp only [hd0, ↓reduceIte]
          by_cases hsmall : d + 1 ≤ r - 1
          · have hl1 : min d (r - 1) = d := Nat.min_eq_left (by omega)
            have hl2 : min (d + 1) (r - 1) = d + 1 := Nat.min_eq_left hsmall
            rw [hl1, hl2, Nat.sub_self, Nat.sub_self, V_zero_left,
              sum_Ico_one_succ_shift (l := d) (by omega) d (fun x => V k x h)]
            have hp := V_nonneg k d h
            linarith
          · have hl1 : min d (r - 1) = r - 1 := Nat.min_eq_right (by omega)
            have hl2 : min (d + 1) (r - 1) = r - 1 := Nat.min_eq_right (by omega)
            rw [hl1, hl2]
            have hsum : ∑ i ∈ Finset.Ico 1 (r - 1), V k (d - i) h ≤
                ∑ i ∈ Finset.Ico 1 (r - 1), V k (d + 1 - i) h := by
              refine Finset.sum_le_sum fun i hi => ?_
              simp only [Finset.mem_Ico] at hi
              rw [show d + 1 - i = (d - i) + 1 by omega]
              exact V_mono_left k _ h
            have hlast : V k (d - (r - 1)) h ≤ V k (d + 1 - (r - 1)) h := by
              rw [show d + 1 - (r - 1) = (d - (r - 1)) + 1 by omega]
              exact V_mono_left k _ h
            linarith

private theorem W_split_depth_one {k r d h : ℕ} (hr : 2 ≤ r) :
    W k (r - 1) d (h + 1) + V k d h = W k r (d + 1) (h + 1) := by
  have hr0 : r ≠ 0 := by omega
  have hr1 : r ≠ 1 := by omega
  by_cases hr2 : r = 2
  · subst hr2
    have hl : min (d + 1) (2 - 1) = 1 := Nat.min_eq_right (by omega)
    simp only [W, Nat.add_sub_cancel, ↓reduceIte, hr0, hr1, Nat.succ_ne_zero, hl,
      Finset.Ico_self, Finset.sum_empty, zero_add]
    ring
  · have hr_m1_0 : r - 1 ≠ 0 := by omega
    have hr_m1_1 : r - 1 ≠ 1 := by omega
    cases d with
    | zero =>
      have hl : min 1 (r - 1) = 1 := Nat.min_eq_left (by omega)
      simp only [W, hr_m1_0, hr_m1_1, hr0, hr1, ↓reduceIte, Nat.succ_ne_zero, hl,
        Finset.Ico_self, Finset.sum_empty, zero_add, Nat.sub_self, V_zero_left]
      norm_num
    | succ m =>
      change W k (r - 1) (m + 1) (h + 1) + V k (m + 1) h = W k r (m + 2) (h + 1)
      simp only [W, hr_m1_0, hr_m1_1, hr0, hr1, ↓reduceIte, Nat.succ_ne_zero]
      rw [show r - 1 - 1 = r - 2 by omega]
      set l' := min (m + 1) (r - 2)
      have hl : min (m + 2) (r - 1) = l' + 1 := by
        rw [show r - 1 = (r - 2) + 1 by omega]
        exact Nat.succ_min_succ (m + 1) (r - 2)
      have hl'_pos : 1 ≤ l' := by dsimp only [l']; omega
      rw [hl, show m + 2 - (l' + 1) = m + 1 - l' by omega,
        sum_Ico_one_succ_shift hl'_pos (m + 1) (fun x => V k x h)]
      ring

private theorem W_split_depth_two {k r d h : ℕ} (hk : 3 ≤ k) (hr : 2 ≤ r) (_hrk : r ≤ k) :
    W k r d (h + 2) + V k d h ≤ W k r (d + 1) (h + 2) := by
  have hr0 : r ≠ 0 := by omega
  have hr1 : r ≠ 1 := by omega
  cases d with
  | zero =>
    have hl : min 1 (r - 1) = 1 := Nat.min_eq_left (by omega)
    simp only [W, hr0, hr1, ↓reduceIte, Nat.succ_ne_zero, hl, Finset.Ico_self, Finset.sum_empty,
      zero_add, Nat.sub_self, V_zero_left]
    norm_num
  | succ m =>
    change W k r (m + 1) (h + 2) + V k (m + 1) h ≤ W k r (m + 2) (h + 2)
    simp only [W, hr0, hr1, ↓reduceIte, Nat.succ_ne_zero]
    by_cases hsmall : m + 2 ≤ r - 1
    · have hl1 : min (m + 1) (r - 1) = m + 1 := Nat.min_eq_left (by omega)
      have hl2 : min (m + 2) (r - 1) = m + 2 := Nat.min_eq_left hsmall
      rw [hl1, hl2, Nat.sub_self, Nat.sub_self, V_zero_left,
        sum_Ico_one_succ_shift (l := m + 1) (by omega) (m + 1) (fun x => V k x (h + 1))]
      have hmr := V_mono_right hk (m + 1) h
      linarith
    · obtain ⟨u, hu_eq⟩ : ∃ u, r - 1 = u + 1 := ⟨r - 2, by omega⟩
      have hu_le : u + 1 ≤ m + 1 := by omega
      have hl1 : min (m + 1) (r - 1) = u + 1 := by rw [hu_eq]; exact Nat.min_eq_right hu_le
      have hl2 : min (m + 2) (r - 1) = u + 1 := by rw [hu_eq]; exact Nat.min_eq_right (by omega)
      rw [hl1, hl2]
      have htel_sum : (∑ i ∈ Finset.Ico 1 (u + 1), V k (m + 2 - i) (h + 1)) +
          2 * V k (m + 2 - (u + 1)) (h + 1) -
          ((∑ i ∈ Finset.Ico 1 (u + 1), V k (m + 1 - i) (h + 1)) +
            2 * V k (m + 1 - (u + 1)) (h + 1)) =
          V k (m + 1) (h + 1) + V k (m + 2 - (u + 1)) (h + 1) -
            2 * V k (m + 1 - (u + 1)) (h + 1) := by
        cases u with
        | zero =>
          rw [Finset.Ico_self, Finset.sum_empty, show m + 2 - 1 = m + 1 by omega]
          ring
        | succ u' =>
          have hleft :=
            sum_Ico_one_succ_shift (l := u' + 1) (by omega) (m + 1) (fun x => V k x (h + 1))
          have hright : ∑ i ∈ Finset.Ico 1 (u' + 2), V k (m + 1 - i) (h + 1) =
              (∑ j ∈ Finset.Ico 1 (u' + 1), V k (m + 1 - j) (h + 1)) +
                V k (m + 2 - (u' + 2)) (h + 1) := by
            rw [Finset.sum_Ico_succ_top (by omega) (fun i => V k (m + 1 - i) (h + 1)),
              show m + 1 - (u' + 1) = m + 2 - (u' + 2) by omega]
          rw [hleft, hright]
          ring
      set a := m - u
      have ha_eq1 : m + 2 - (u + 1) = a + 1 := by omega
      have ha_eq2 : m + 1 - (u + 1) = a := by omega
      have ha_eq3 : m + 1 = a + u + 1 := by omega
      have hchain : ∀ w : ℕ,
          2 * (V k (a + w + 1) (h + 1) - V k (a + w) (h + 1)) ≤
            V k (a + w + 1) (h + 1) + V k (a + 1) (h + 1) - 2 * V k a (h + 1) := by
        intro w
        induction w with
        | zero =>
          simp only [Nat.add_zero]
          linarith
        | succ w ih =>
          have h3 := V_three_term hk (a + w) (h + 1)
          rw [show a + w + 2 = a + w + 1 + 1 by omega] at h3
          rw [← Nat.add_assoc a w 1]
          linarith
      have hchain_u := hchain u
      have hstep_last := V_step_ineq hk (a + u) h
      rw [ha_eq1, ha_eq2, ha_eq3] at htel_sum ⊢
      linarith

private theorem exists_eq_one_of_sum_eq_one {r : ℕ} {f : Fin r → ℕ}
    (h : ∑ i : Fin r, f i = 1) :
    ∃ i₀ : Fin r, f i₀ = 1 ∧ ∀ j : Fin r, j ≠ i₀ → f j = 0 := by
  have hex : ∃ i₀ : Fin r, f i₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    simp only [hall, Finset.sum_const_zero] at h
    omega
  obtain ⟨i₀, hi₀_ne⟩ := hex
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by have := i₀.isLt; omega⟩
  rw [Fin.sum_univ_succAbove f i₀] at h
  have hi₀_eq : f i₀ = 1 := by omega
  have hrest : ∑ j : Fin r', f (i₀.succAbove j) = 0 := by omega
  rw [Finset.sum_eq_zero_iff] at hrest
  refine ⟨i₀, hi₀_eq, fun j hj => ?_⟩
  obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
  exact hrest j' (Finset.mem_univ j')

private theorem GenPrefixTree.all_state_eq_of_valid_empty :
    ∀ (t : GenPrefixTree), t.Valid ∅ →
      ∀ s, s ≠ t.state → t.outAt s = 0
  | .node st hasOut r isMul child, hval, s, hne => by
    obtain ⟨hedges, hch_val⟩ := hval
    have hch_zero : ∀ i : Fin r, (child i).outAt s = 0 := by
      intro i
      have hi := hedges i
      by_cases hm : isMul i = true
      · simp only [hm, ↓reduceIte, Finset.notMem_empty, and_false] at hi
      · simp only [hm, Bool.false_eq_true, ↓reduceIte] at hi
        exact (child i).all_state_eq_of_valid_empty (hch_val i) s (hi.symm ▸ hne)
    simp only [GenPrefixTree.outAt, GenPrefixTree.state] at hne ⊢
    have h0 : ¬ (hasOut = true ∧ st = s) := fun h => hne h.2.symm
    simp only [h0, ↓reduceIte, hch_zero, Finset.sum_const_zero, Nat.add_zero]

private theorem GenPrefixTree.outCount_eq_outAt_of_valid_empty :
    ∀ (t : GenPrefixTree), t.Valid ∅ → t.outCount = t.outAt t.state
  | .node st hasOut r isMul child, hval => by
    obtain ⟨hedges, hch_val⟩ := hval
    have hch_eq : ∀ i : Fin r, (child i).outCount = (child i).outAt st := by
      intro i
      have hi := hedges i
      by_cases hm : isMul i = true
      · simp only [hm, ↓reduceIte, Finset.notMem_empty, and_false] at hi
      · simp only [hm, Bool.false_eq_true, ↓reduceIte] at hi
        rw [← hi]
        exact (child i).outCount_eq_outAt_of_valid_empty (hch_val i)
    simp only [GenPrefixTree.outCount, GenPrefixTree.outAt, GenPrefixTree.state, and_true]
    rw [Finset.sum_congr rfl fun i _ => hch_eq i]

private theorem child_edge_left {a m b st s' : ℕ} {hmul : Bool}
    (IL : IntervalTree a m) (IR : IntervalTree m b)
    (hst_ge : a ≤ st) (hst_lt : st < m)
    (hed : if hmul = true then st < s' ∧ (st, s') ∈ IL.intervals ∪ IR.intervals else s' = st)
    (hnhit : ¬ (hmul = true ∧ s' = m)) :
    a ≤ s' ∧ s' < m ∧
      (if hmul = true then st < s' ∧ (st, s') ∈ IL.intervals.erase (a, m) else s' = st) := by
  by_cases hm : hmul = true
  · simp only [hm, ↓reduceIte] at hed ⊢
    have hne_m : s' ≠ m := fun heq => hnhit ⟨hm, heq⟩
    rw [Finset.mem_union] at hed
    have hmem_L : (st, s') ∈ IL.intervals := by
      rcases hed.2 with hL | hR
      · exact hL
      · have := IR.mem_intervals_bounds hR; omega
    have hbds := IL.mem_intervals_bounds hmem_L
    refine ⟨by omega, by omega, hed.1, Finset.mem_erase.mpr ⟨?_, hmem_L⟩⟩
    intro heq; rw [Prod.mk.injEq] at heq; exact hne_m heq.2
  · simp only [hm, Bool.false_eq_true, ↓reduceIte] at hed ⊢
    exact ⟨by omega, by omega, hed⟩

private theorem GenPrefixTree.valid_left_of_mulCount_zero {a m b : ℕ}
    (IL : IntervalTree a m) (IR : IntervalTree m b) :
    ∀ (t : GenPrefixTree),
      a ≤ t.state →
      t.state < m →
      t.Valid (IL.intervals ∪ IR.intervals) →
      t.mulCount m = 0 →
      t.MaxStateLt m ∧ t.Valid (IL.intervals.erase (a, m))
  | .node st hasOut r isMul child, hst_ge, hst_lt, hval, hmc0 => by
    simp only [GenPrefixTree.state] at hst_ge hst_lt
    simp only [GenPrefixTree.mulCount, Finset.sum_eq_zero_iff, Finset.mem_univ,
      forall_true_left] at hmc0
    obtain ⟨hedges, hch_val⟩ := hval
    have hch_step : ∀ i : Fin r,
        (if isMul i = true then
          st < (child i).state ∧ (st, (child i).state) ∈ IL.intervals.erase (a, m)
        else (child i).state = st) ∧
        (child i).MaxStateLt m ∧
        (child i).Valid (IL.intervals.erase (a, m)) := by
      intro i
      have hi_mc := hmc0 i
      have hnhit : ¬ (isMul i = true ∧ (child i).state = m) := by
        rintro ⟨h1, h2⟩; simp only [h1, h2, and_self, ↓reduceIte] at hi_mc; omega
      obtain ⟨hs_ge, hs_lt, hed'⟩ := child_edge_left IL IR hst_ge hst_lt (hedges i) hnhit
      have ih := (child i).valid_left_of_mulCount_zero IL IR hs_ge hs_lt (hch_val i)
        (Nat.add_eq_zero_iff.mp hi_mc).2
      exact ⟨hed', ih.1, ih.2⟩
    exact ⟨⟨hst_lt, fun i => (hch_step i).2.1⟩,
      ⟨fun i => (hch_step i).1, fun i => (hch_step i).2.2⟩⟩

private theorem GenPrefixTree.child_valid_left_of_step_zero {a m b st : ℕ} {hmul : Bool}
    (IL : IntervalTree a m) (IR : IntervalTree m b) (c : GenPrefixTree)
    (hst_ge : a ≤ st) (hst_lt : st < m)
    (hed : if hmul = true then st < c.state ∧ (st, c.state) ∈ IL.intervals ∪ IR.intervals
      else c.state = st)
    (hval : c.Valid (IL.intervals ∪ IR.intervals))
    (hstep0 : (if hmul = true ∧ c.state = m then 1 else 0) + c.mulCount m = 0) :
    (if hmul = true then st < c.state ∧ (st, c.state) ∈ IL.intervals.erase (a, m)
      else c.state = st) ∧
    c.MaxStateLt m ∧ c.Valid (IL.intervals.erase (a, m)) := by
  have hnhit : ¬ (hmul = true ∧ c.state = m) := by
    rintro ⟨h1, h2⟩; simp only [h1, h2, and_self, ↓reduceIte] at hstep0; omega
  obtain ⟨hs_ge, hs_lt, hed'⟩ := child_edge_left IL IR hst_ge hst_lt hed hnhit
  have hsub := c.valid_left_of_mulCount_zero IL IR hs_ge hs_lt hval
    (Nat.add_eq_zero_iff.mp hstep0).2
  exact ⟨hed', hsub.1, hsub.2⟩

private theorem GenPrefixTree.valid_right_of_state_ge {a m b : ℕ}
    (IL : IntervalTree a m) (IR : IntervalTree m b) :
    ∀ (t : GenPrefixTree),
      m ≤ t.state →
      t.MaxStateLt b →
      t.Valid (IL.intervals ∪ IR.intervals) →
      t.Valid (IR.intervals.erase (m, b))
  | .node st hasOut r isMul child, hst_ge, hmax, hval => by
    simp only [GenPrefixTree.state] at hst_ge
    obtain ⟨_, hch_max⟩ := hmax
    obtain ⟨hedges, hch_val⟩ := hval
    have hch_st_lt : ∀ i : Fin r, (child i).state < b := by
      intro i
      rcases h : child i with ⟨s', _, _, _, _⟩
      have := hch_max i
      rw [h] at this
      exact this.1
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have hi_ed := hedges i
      by_cases hm : isMul i = true
      · simp only [hm, ↓reduceIte] at hi_ed ⊢
        rw [Finset.mem_union] at hi_ed
        have hmem_R : (st, (child i).state) ∈ IR.intervals := by
          rcases hi_ed.2 with hL | hR
          · have := IL.mem_intervals_bounds hL; omega
          · exact hR
        have hlt_b := hch_st_lt i
        refine ⟨hi_ed.1, Finset.mem_erase.mpr ⟨?_, hmem_R⟩⟩
        intro heq; rw [Prod.mk.injEq] at heq; omega
      · simp only [hm, Bool.false_eq_true, ↓reduceIte] at hi_ed ⊢
        exact hi_ed
    · have hi_ed := hedges i
      have hge_i : m ≤ (child i).state := by
        by_cases hm : isMul i = true
        · simp only [hm, ↓reduceIte] at hi_ed; omega
        · simp only [hm, Bool.false_eq_true, ↓reduceIte] at hi_ed; omega
      exact (child i).valid_right_of_state_ge IL IR hge_i (hch_max i) (hch_val i)

private theorem GenPrefixTree.extract_mul_subtree {k a m b : ℕ}
    (IL : IntervalTree a m) (IR : IntervalTree m b) :
    ∀ (t : GenPrefixTree),
      a ≤ t.state →
      t.state < m →
      t.MaxStateLt b →
      t.FanoutAtMost k →
      t.Valid (IL.intervals ∪ IR.intervals) →
      t.mulCount m = 1 →
      (∃ Q₁ Q₂ : GenPrefixTree,
        Q₁.state = t.state ∧
        Q₁.rootBudget + 1 = t.rootBudget ∧
        Q₁.depth ≤ t.depth ∧
        Q₁.FanoutAtMost k ∧
        Q₁.MaxStateLt m ∧
        Q₁.Valid (IL.intervals.erase (a, m)) ∧
        (∀ x, Q₁.outAt x ≤ t.outAt x) ∧
        (∀ x, Q₁.mulCount x ≤ t.mulCount x) ∧
        Q₂.state = m ∧
        Q₂.depth + 1 ≤ t.depth ∧
        Q₂.FanoutAtMost k ∧
        Q₂.MaxStateLt b ∧
        Q₂.Valid (IR.intervals.erase (m, b)) ∧
        (∀ x, Q₂.outAt x ≤ t.outAt x) ∧
        (∀ x, Q₂.mulCount x ≤ t.mulCount x) ∧
        t.outCount = Q₁.outCount + Q₂.outCount) ∨
      (∃ Q₁ Q₂ : GenPrefixTree,
        Q₁.state = t.state ∧
        Q₁.rootBudget ≤ t.rootBudget ∧
        Q₁.depth ≤ t.depth ∧
        Q₁.FanoutAtMost k ∧
        Q₁.MaxStateLt m ∧
        Q₁.Valid (IL.intervals.erase (a, m)) ∧
        (∀ x, Q₁.outAt x ≤ t.outAt x) ∧
        (∀ x, Q₁.mulCount x ≤ t.mulCount x) ∧
        Q₂.state = m ∧
        Q₂.depth + 2 ≤ t.depth ∧
        Q₂.FanoutAtMost k ∧
        Q₂.MaxStateLt b ∧
        Q₂.Valid (IR.intervals.erase (m, b)) ∧
        (∀ x, Q₂.outAt x ≤ t.outAt x) ∧
        (∀ x, Q₂.mulCount x ≤ t.mulCount x) ∧
        t.outCount = Q₁.outCount + Q₂.outCount)
  | .node _ _ 0 _ _, _, _, _, _, _, hmc1 => by
    simp only [GenPrefixTree.mulCount, Finset.univ_eq_empty, Finset.sum_empty] at hmc1
    omega
  | .node st hasOut (r' + 1) isMul child, hst_ge, hst_lt, hmax, hfan, hval, hmc1 => by
    simp only [GenPrefixTree.state] at hst_ge hst_lt
    obtain ⟨hst_b, hch_max⟩ := hmax
    obtain ⟨hr_bud, hch_fan⟩ := hfan
    obtain ⟨hedges, hch_val⟩ := hval
    simp only [GenPrefixTree.mulCount] at hmc1
    obtain ⟨i₀, hi₀_one, hother_zero⟩ := exists_eq_one_of_sum_eq_one hmc1
    have hother_left (j : Fin (r' + 1)) (hj : j ≠ i₀) :=
      (child j).child_valid_left_of_step_zero IL IR hst_ge hst_lt (hedges j) (hch_val j)
        (hother_zero j hj)
    by_cases hhit : isMul i₀ = true ∧ (child i₀).state = m
    · left
      let Q₁ := GenPrefixTree.node st hasOut r' (isMul ∘ i₀.succAbove) (child ∘ i₀.succAbove)
      let Q₂ := child i₀
      refine ⟨Q₁, Q₂, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hhit.2,
        GenPrefixTree.child_depth_lt i₀, hch_fan i₀, hch_max i₀,
        (child i₀).valid_right_of_state_ge IL IR hhit.2.ge (hch_max i₀) (hch_val i₀),
        ?_, ?_, ?_⟩
      · simp only [Q₁, GenPrefixTree.rootBudget]; omega
      · simp only [Q₁, GenPrefixTree.depth]
        refine Finset.sup_le fun j _ => ?_
        exact GenPrefixTree.child_depth_lt (st := st) (hasOut := hasOut)
          (isMul := isMul) (child := child) (i₀.succAbove j)
      · exact ⟨by omega, fun j => hch_fan (i₀.succAbove j)⟩
      · exact ⟨hst_lt, fun j => (hother_left _ (Fin.succAbove_ne i₀ j)).2.1⟩
      · exact ⟨fun j => (hother_left _ (Fin.succAbove_ne i₀ j)).1,
          fun j => (hother_left _ (Fin.succAbove_ne i₀ j)).2.2⟩
      · intro x
        simp only [Q₁, GenPrefixTree.outAt, Function.comp_apply]
        rw [Fin.sum_univ_succAbove (fun i => (child i).outAt x) i₀]
        omega
      · intro x
        simp only [Q₁, GenPrefixTree.mulCount, Function.comp_apply]
        rw [Fin.sum_univ_succAbove
          (fun i => (if isMul i = true ∧ (child i).state = x then 1 else 0) +
            (child i).mulCount x) i₀]
        omega
      · intro x
        simp only [Q₂, GenPrefixTree.outAt]
        rw [Fin.sum_univ_succAbove (fun i => (child i).outAt x) i₀]
        omega
      · intro x
        simp only [Q₂, GenPrefixTree.mulCount]
        rw [Fin.sum_univ_succAbove
          (fun i => (if isMul i = true ∧ (child i).state = x then 1 else 0) +
            (child i).mulCount x) i₀]
        omega
      · simp only [Q₁, Q₂, GenPrefixTree.outCount, Function.comp_apply]
        rw [Fin.sum_univ_succAbove (fun i => (child i).outCount) i₀]
        omega
    · right
      have hi₀_mc1 : (child i₀).mulCount m = 1 := by
        simp only [hhit, ↓reduceIte, Nat.zero_add] at hi₀_one
        exact hi₀_one
      have hi₀_bounds := child_edge_left IL IR hst_ge hst_lt (hedges i₀) hhit
      have hcommon : ∀ (Q₁_s Q₂ : GenPrefixTree),
          Q₁_s.state = (child i₀).state →
          Q₁_s.depth ≤ (child i₀).depth →
          Q₁_s.FanoutAtMost k →
          Q₁_s.MaxStateLt m →
          Q₁_s.Valid (IL.intervals.erase (a, m)) →
          (∀ x, Q₁_s.outAt x ≤ (child i₀).outAt x) →
          (∀ x, Q₁_s.mulCount x ≤ (child i₀).mulCount x) →
          Q₂.state = m →
          Q₂.depth + 1 ≤ (child i₀).depth →
          Q₂.FanoutAtMost k →
          Q₂.MaxStateLt b →
          Q₂.Valid (IR.intervals.erase (m, b)) →
          (∀ x, Q₂.outAt x ≤ (child i₀).outAt x) →
          (∀ x, Q₂.mulCount x ≤ (child i₀).mulCount x) →
          (child i₀).outCount = Q₁_s.outCount + Q₂.outCount →
          ∃ Q₁ Q₂' : GenPrefixTree,
            Q₁.state = st ∧
            Q₁.rootBudget ≤ (GenPrefixTree.node st hasOut (r' + 1) isMul child).rootBudget ∧
            Q₁.depth ≤ (GenPrefixTree.node st hasOut (r' + 1) isMul child).depth ∧
            Q₁.FanoutAtMost k ∧
            Q₁.MaxStateLt m ∧
            Q₁.Valid (IL.intervals.erase (a, m)) ∧
            (∀ x, Q₁.outAt x ≤ (GenPrefixTree.node st hasOut (r' + 1) isMul child).outAt x) ∧
            (∀ x, Q₁.mulCount x ≤
              (GenPrefixTree.node st hasOut (r' + 1) isMul child).mulCount x) ∧
            Q₂'.state = m ∧
            Q₂'.depth + 2 ≤ (GenPrefixTree.node st hasOut (r' + 1) isMul child).depth ∧
            Q₂'.FanoutAtMost k ∧
            Q₂'.MaxStateLt b ∧
            Q₂'.Valid (IR.intervals.erase (m, b)) ∧
            (∀ x, Q₂'.outAt x ≤ (GenPrefixTree.node st hasOut (r' + 1) isMul child).outAt x) ∧
            (∀ x, Q₂'.mulCount x ≤
              (GenPrefixTree.node st hasOut (r' + 1) isMul child).mulCount x) ∧
            (GenPrefixTree.node st hasOut (r' + 1) isMul child).outCount =
              Q₁.outCount + Q₂'.outCount := by
        intro Q₁_s Q₂ hQ1_st hQ1_d hQ1_fan hQ1_max hQ1_val hQ1_oa hQ1_mc
          hQ2_st hQ2_d hQ2_fan hQ2_max hQ2_val hQ2_oa hQ2_mc hcnt_eq
        let ch' := Function.update child i₀ Q₁_s
        let Q₁ := GenPrefixTree.node st hasOut (r' + 1) isMul ch'
        have hc0_d : (child i₀).depth + 1 ≤
            (GenPrefixTree.node st hasOut (r' + 1) isMul child).depth :=
          GenPrefixTree.child_depth_lt i₀
        refine ⟨Q₁, Q₂, rfl, le_rfl, ?_, ⟨hr_bud, ?_⟩, ⟨hst_lt, ?_⟩, ⟨?_, ?_⟩, ?_, ?_,
          hQ2_st, by omega, hQ2_fan, hQ2_max, hQ2_val, ?_, ?_, ?_⟩
        · simp only [Q₁, GenPrefixTree.depth]
          refine Finset.sup_le fun j _ => ?_
          dsimp only [ch']
          by_cases hj : j = i₀
          · rw [hj, Function.update_self]
            exact (Nat.add_le_add_right hQ1_d 1).trans
              (Finset.le_sup (f := fun i => (child i).depth + 1) (Finset.mem_univ i₀))
          · rw [Function.update_of_ne hj]
            exact Finset.le_sup (f := fun i => (child i).depth + 1) (Finset.mem_univ j)
        · intro j; dsimp only [ch']
          by_cases hj : j = i₀
          · rw [hj, Function.update_self]; exact hQ1_fan
          · rw [Function.update_of_ne hj]; exact hch_fan j
        · intro j; dsimp only [ch']
          by_cases hj : j = i₀
          · rw [hj, Function.update_self]; exact hQ1_max
          · rw [Function.update_of_ne hj]; exact (hother_left j hj).2.1
        · intro j; dsimp only [ch']
          by_cases hj : j = i₀
          · rw [hj, Function.update_self, hQ1_st]; exact hi₀_bounds.2.2
          · rw [Function.update_of_ne hj]; exact (hother_left j hj).1
        · intro j; dsimp only [ch']
          by_cases hj : j = i₀
          · rw [hj, Function.update_self]; exact hQ1_val
          · rw [Function.update_of_ne hj]; exact (hother_left j hj).2.2
        · intro x
          simp only [Q₁, GenPrefixTree.outAt]
          refine Nat.add_le_add_left (Finset.sum_le_sum fun j _ => ?_) _
          dsimp only [ch']
          by_cases hj : j = i₀
          · rw [hj, Function.update_self]; exact hQ1_oa x
          · rw [Function.update_of_ne hj]
        · intro x
          simp only [Q₁, GenPrefixTree.mulCount]
          refine Finset.sum_le_sum fun j _ => ?_
          by_cases hj : j = i₀
          · simp only [ch', hj, Function.update_self, hQ1_st]
            exact Nat.add_le_add_left (hQ1_mc x) _
          · simp only [ch', Function.update_of_ne hj, le_rfl]
        · intro x
          simp only [GenPrefixTree.outAt]
          rw [Fin.sum_univ_succAbove (fun i => (child i).outAt x) i₀]
          have := hQ2_oa x
          omega
        · intro x
          simp only [GenPrefixTree.mulCount]
          rw [Fin.sum_univ_succAbove
            (fun i => (if isMul i = true ∧ (child i).state = x then 1 else 0) +
              (child i).mulCount x) i₀]
          have := hQ2_mc x
          omega
        · simp only [Q₁, GenPrefixTree.outCount, ch']
          rw [Fin.sum_univ_succAbove (fun i => (child i).outCount) i₀,
            Fin.sum_univ_succAbove (fun i => (Function.update child i₀ Q₁_s i).outCount) i₀,
            Function.update_self]
          have hrest_eq : (∑ j : Fin r',
              (Function.update child i₀ Q₁_s (i₀.succAbove j)).outCount) =
              ∑ j : Fin r', (child (i₀.succAbove j)).outCount :=
            Finset.sum_congr rfl fun j _ => by
              rw [Function.update_of_ne (Fin.succAbove_ne i₀ j)]
          rw [hrest_eq, hcnt_eq]
          omega
      rcases (child i₀).extract_mul_subtree IL IR hi₀_bounds.1 hi₀_bounds.2.1
          (hch_max i₀) (hch_fan i₀) (hch_val i₀) hi₀_mc1 with
        ⟨Q₁_s, Q₂, h1, _, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ |
        ⟨Q₁_s, Q₂, h1, _, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩
      · exact hcommon Q₁_s Q₂ h1 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
      · exact hcommon Q₁_s Q₂ h1 h3 h4 h5 h6 h7 h8 h9 (by omega) h11 h12 h13 h14 h15 h16

private theorem GenPrefixTree.valid_suffix {a c b : ℕ} {S T : Finset (ℕ × ℕ)}
    (hsub : ∀ x y, (x, y) ∈ S → c ≤ x → (x, y) ∈ T) :
    ∀ (u : GenPrefixTree),
      c ≤ u.state →
      u.MaxStateLt b →
      u.Valid S →
      u.Valid (T.erase (c, b))
  | .node su ho ru imu chu, hge_u, hmax_u, hval_u => by
    change c ≤ su at hge_u
    obtain ⟨_, hch_mu⟩ := hmax_u
    obtain ⟨hed_u, hcv_u⟩ := hval_u
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have hi := hed_u i
      by_cases hmi : imu i = true
      · simp only [hmi, ↓reduceIte] at hi ⊢
        have hlt_b : (chu i).state < b := by
          rcases hcu : chu i with ⟨_, _, _, _, _⟩
          have := hch_mu i
          rw [hcu] at this
          exact this.1
        refine ⟨hi.1, Finset.mem_erase.mpr ⟨?_, hsub _ _ hi.2 hge_u⟩⟩
        intro heq; rw [Prod.mk.injEq] at heq; omega
      · simp only [hmi, Bool.false_eq_true, ↓reduceIte] at hi ⊢
        exact hi
    · have hi := hed_u i
      have hge_i : c ≤ (chu i).state := by
        by_cases hmi : imu i = true
        · simp only [hmi, ↓reduceIte] at hi; omega
        · simp only [hmi, Bool.false_eq_true, ↓reduceIte] at hi; omega
      exact (chu i).valid_suffix (a := a) hsub hge_i (hch_mu i) (hcv_u i)

private theorem GenPrefixTree.outCount_le_W {k : ℕ} (hk : 3 ≤ k) :
    ∀ (d h r a b : ℕ) (I : IntervalTree a b) (t : GenPrefixTree),
      r ≤ k →
      I.depth ≤ d →
      t.depth ≤ h →
      t.state = a →
      t.MaxStateLt b →
      t.rootBudget ≤ r →
      t.FanoutAtMost k →
      t.Valid (I.intervals.erase (a, b)) →
      (∀ s, t.outAt s ≤ 1) →
      (∀ m, t.mulCount m ≤ 1) →
      (t.outCount : ℝ) ≤ W k r d h := by
  have haux : ∀ n, ∀ (d h r a b : ℕ) (I : IntervalTree a b) (t : GenPrefixTree),
      d + h = n →
      r ≤ k →
      I.depth ≤ d →
      t.depth ≤ h →
      t.state = a →
      t.MaxStateLt b →
      t.rootBudget ≤ r →
      t.FanoutAtMost k →
      t.Valid (I.intervals.erase (a, b)) →
      (∀ s, t.outAt s ≤ 1) →
      (∀ m, t.mulCount m ≤ 1) →
      (t.outCount : ℝ) ≤ W k r d h := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro d h r a b I t hdh hrk hd_le hh_le hst hmax hbud hfan hval hout_at hmul_cnt
      cases h with
      | zero =>
        rcases t with ⟨st, hasOut, r_ch, isMul, child⟩
        by_cases hr0 : r_ch = 0
        · subst hr0
          simp only [GenPrefixTree.outCount, Finset.univ_eq_empty, Finset.sum_empty, Nat.add_zero]
          have h1 : (1 : ℝ) ≤ W k r d 0 := by unfold W; exact one_le_pow₀ (by norm_num)
          cases hasOut <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_one, Nat.cast_zero]
          · positivity
          · exact h1
        · have hc0 := GenPrefixTree.child_depth_lt (st := st) (hasOut := hasOut)
            (isMul := isMul) (child := child) ⟨0, by omega⟩
          omega
      | succ h' =>
        by_cases hr0 : r = 0
        · subst hr0
          rcases t with ⟨st, hasOut, r_ch, isMul, child⟩
          simp only [GenPrefixTree.rootBudget] at hbud
          have hr_ch0 : r_ch = 0 := by omega
          have hno : hasOut = false := by
            cases hasOut
            · rfl
            · simp only [↓reduceIte] at hbud; omega
          subst hr_ch0 hno
          simp only [GenPrefixTree.outCount, Bool.false_eq_true, ↓reduceIte, Finset.univ_eq_empty,
            Finset.sum_empty, Nat.add_zero, Nat.cast_zero, W, le_rfl]
        · by_cases hr1 : r = 1
          · subst hr1
            have hw_eq : W k 1 d (h' + 1) = W k k d h' := by
              rw [W_eq_V (by omega)]
              rfl
            rw [hw_eq]
            rcases t with ⟨st, hasOut, r_ch, isMul, child⟩
            simp only [GenPrefixTree.rootBudget] at hbud
            simp only [GenPrefixTree.state] at hst
            by_cases hr_ch0 : r_ch = 0
            · subst hr_ch0
              simp only [GenPrefixTree.outCount, Finset.univ_eq_empty, Finset.sum_empty,
                Nat.add_zero]
              have h1 := W_one_le (k := k) (by omega : 1 ≤ k) d h'
              cases hasOut <;>
                simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_zero, Nat.cast_one]
              · linarith
              · exact h1
            · have hr_ch1 : r_ch = 1 := by omega
              have hno : hasOut = false := by
                cases hasOut
                · rfl
                · simp only [↓reduceIte] at hbud; omega
              subst hr_ch1 hno
              simp only [GenPrefixTree.outCount, Bool.false_eq_true, ↓reduceIte, Nat.zero_add,
                Fin.sum_univ_one]
              have hc0_d : (child 0).depth ≤ h' := by
                have := GenPrefixTree.child_depth_lt (st := st) (hasOut := false)
                  (isMul := isMul) (child := child) 0
                omega
              obtain ⟨_, hch_max⟩ := hmax
              obtain ⟨_, hch_fan⟩ := hfan
              obtain ⟨hedges, hch_val⟩ := hval
              have hc0_bud : (child 0).rootBudget ≤ k := by
                rcases h : child 0 with ⟨_, _, _, _, _⟩
                have hf0 := hch_fan 0
                rw [h] at hf0
                exact hf0.1
              have hc0_oa : ∀ s, (child 0).outAt s ≤ 1 := by
                intro s
                have hs := hout_at s
                simp only [GenPrefixTree.outAt, Bool.false_eq_true, false_and, ↓reduceIte,
                  Nat.zero_add, Fin.sum_univ_one] at hs
                exact hs
              have hc0_mc : ∀ m, (child 0).mulCount m ≤ 1 := by
                intro m
                have hm := hmul_cnt m
                simp only [GenPrefixTree.mulCount, Fin.sum_univ_one] at hm
                omega
              have hed0 := hedges 0
              by_cases hm0 : isMul 0 = true
              · simp only [hm0, ↓reduceIte, hst] at hed0
                obtain ⟨_, _, J, hJd, hJsub⟩ := I.suffixOfLeftPrefix (child 0).state hed0.2
                have hc0_val_J : (child 0).Valid (J.intervals.erase ((child 0).state, b)) :=
                  (child 0).valid_suffix (a := a) hJsub le_rfl (hch_max 0) (hch_val 0)
                exact ih (d + h') (by omega) d h' k (child 0).state b J (child 0) rfl le_rfl
                  (hJd.trans hd_le) hc0_d rfl (hch_max 0) hc0_bud (hch_fan 0) hc0_val_J
                  hc0_oa hc0_mc
              · simp only [hm0, Bool.false_eq_true, ↓reduceIte, hst] at hed0
                exact ih (d + h') (by omega) d h' k a b I (child 0) rfl le_rfl hd_le hc0_d
                  hed0 (hch_max 0) hc0_bud (hch_fan 0) (hch_val 0) hc0_oa hc0_mc
          · have hr2 : 2 ≤ r := by omega
            cases I with
            | leaf a =>
              have hval_emp : t.Valid ∅ := by
                simpa only [IntervalTree.intervals, Finset.erase_singleton] using hval
              have heq_oa := t.outCount_eq_outAt_of_valid_empty hval_emp
              have hle1 : t.outCount ≤ 1 := heq_oa ▸ hout_at t.state
              have h1 := W_one_le (k := k) (by omega : 1 ≤ r) d (h' + 1)
              have hcast : (t.outCount : ℝ) ≤ 1 := by exact_mod_cast hle1
              exact hcast.trans h1
            | @node a m b IL IR =>
              have hIL := IL.lt
              have hIR := IR.lt
              simp only [IntervalTree.depth] at hd_le
              obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
              have hdL : IL.depth ≤ d' := by omega
              have hdR : IR.depth ≤ d' := by omega
              rw [IntervalTree.erase_root_eq_union] at hval
              have hmc_m := hmul_cnt m
              by_cases hmc0 : t.mulCount m = 0
              · obtain ⟨hmax_L, hval_L⟩ := t.valid_left_of_mulCount_zero IL IR
                  (by omega) (by omega) hval hmc0
                have hsub := ih (d' + (h' + 1)) (by omega) d' (h' + 1) r a m IL t rfl hrk
                  hdL hh_le hst hmax_L hbud hfan hval_L hout_at hmul_cnt
                exact hsub.trans (W_mono_left k r d' (h' + 1))
              · have hmc1 : t.mulCount m = 1 := by omega
                rcases t.extract_mul_subtree IL IR (by omega) (by omega) hmax hfan hval hmc1 with
                  ⟨Q₁, Q₂, hQ1_st, hQ1_bud, hQ1_d, hQ1_fan, hQ1_max, hQ1_val, hQ1_oa, hQ1_mc,
                    hQ2_st, hQ2_d, hQ2_fan, hQ2_max, hQ2_val, hQ2_oa, hQ2_mc, hcnt_eq⟩ |
                  ⟨Q₁, Q₂, hQ1_st, hQ1_bud, hQ1_d, hQ1_fan, hQ1_max, hQ1_val, hQ1_oa, hQ1_mc,
                    hQ2_st, hQ2_d, hQ2_fan, hQ2_max, hQ2_val, hQ2_oa, hQ2_mc, hcnt_eq⟩
                · have hQ2_bud : Q₂.rootBudget ≤ k := by
                    rcases hq : Q₂ with ⟨_, _, _, _, _⟩
                    have hf := hQ2_fan
                    rw [hq] at hf
                    exact hf.1
                  have hb1 := ih (d' + (h' + 1)) (by omega) d' (h' + 1) (r - 1) a m IL Q₁ rfl
                    (by omega) hdL (hQ1_d.trans hh_le) (hQ1_st.trans hst) hQ1_max (by omega)
                    hQ1_fan hQ1_val (fun s => (hQ1_oa s).trans (hout_at s))
                    (fun x => (hQ1_mc x).trans (hmul_cnt x))
                  have hb2 := ih (d' + h') (by omega) d' h' k m b IR Q₂ rfl le_rfl hdR
                    (by omega) hQ2_st hQ2_max hQ2_bud hQ2_fan hQ2_val
                    (fun s => (hQ2_oa s).trans (hout_at s))
                    (fun x => (hQ2_mc x).trans (hmul_cnt x))
                  rw [W_eq_V (by omega)] at hb2
                  have hsp := W_split_depth_one (k := k) (d := d') (h := h') hr2
                  rw [hcnt_eq, Nat.cast_add]
                  linarith
                · obtain ⟨h'', rfl⟩ : ∃ h'', h' = h'' + 1 := ⟨h' - 1, by omega⟩
                  have hQ2_bud : Q₂.rootBudget ≤ k := by
                    rcases hq : Q₂ with ⟨_, _, _, _, _⟩
                    have hf := hQ2_fan
                    rw [hq] at hf
                    exact hf.1
                  have hb1 := ih (d' + (h'' + 2)) (by omega) d' (h'' + 2) r a m IL Q₁ rfl hrk
                    hdL (hQ1_d.trans hh_le) (hQ1_st.trans hst) hQ1_max (hQ1_bud.trans hbud)
                    hQ1_fan hQ1_val (fun s => (hQ1_oa s).trans (hout_at s))
                    (fun x => (hQ1_mc x).trans (hmul_cnt x))
                  have hb2 := ih (d' + h'') (by omega) d' h'' k m b IR Q₂ rfl le_rfl hdR
                    (by omega) hQ2_st hQ2_max hQ2_bud hQ2_fan hQ2_val
                    (fun s => (hQ2_oa s).trans (hout_at s))
                    (fun x => (hQ2_mc x).trans (hmul_cnt x))
                  rw [W_eq_V (by omega)] at hb2
                  have hsp := W_split_depth_two (d := d') (h := h'') hk hr2 hrk
                  rw [hcnt_eq, Nat.cast_add]
                  linarith
  intro d h r a b I t
  exact haux (d + h) d h r a b I t rfl

private noncomputable def V_star (k D : ℕ) : ℝ :=
  ∑ d ∈ Finset.range (D + 1), V k d (D - d)

private theorem V_star_recurrence {k D : ℕ} (hk : 3 ≤ k) (hD : k ≤ D) :
    V_star k D =
      (∑ i ∈ Finset.Ico 2 k, V_star k (D - i)) +
        2 * V_star k (D - k) + (3 / 2 : ℝ) ^ D + ((k - 1 : ℕ) : ℝ) := by
  unfold V_star
  rw [diagSum_recurrence (by omega) hD (V k) (V_zero_left k) (fun _ _ => rfl), V_zero_right]

private theorem width_le_V_star {N k : ℕ} (hk : 3 ≤ k) (hN : 1 ≤ N)
    {c : PrefixCircuit N} (hopt : IsOptimalPrefixCircuit c) (hfan : FanoutAtMost c k) :
    (N : ℝ) ≤ V_star k c.depth := by
  obtain ⟨T, hT0, hTD, hseg⟩ := optimal_segment_decomposition hN hopt hfan
  set D := c.depth
  have htele : ∀ r ≤ D, T r = 1 + ∑ d ∈ Finset.range r, (T (d + 1) - T d) := by
    intro r hr
    induction r with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, Nat.add_zero, hT0]
    | succ r ih =>
      rw [Finset.sum_range_succ, ← Nat.add_assoc, ← ih (by omega)]
      have hlt := (hseg r (by omega)).1
      omega
  have hN_eq : (N : ℝ) = 1 + ∑ d ∈ Finset.range D, ((T (d + 1) - T d : ℕ) : ℝ) := by
    rw [← hTD, htele D le_rfl, Nat.cast_add, Nat.cast_one, Nat.cast_sum]
  rw [hN_eq]
  unfold V_star
  rw [Finset.sum_range_succ, Nat.sub_self, V_zero_right, add_comm (1 : ℝ)]
  have h1 : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ D := one_le_pow₀ (by norm_num)
  have hsum : (∑ d ∈ Finset.range D, ((T (d + 1) - T d : ℕ) : ℝ)) ≤
      ∑ d ∈ Finset.range D, V k d (D - d) := by
    refine Finset.sum_le_sum fun d hd => ?_
    rw [Finset.mem_range] at hd
    obtain ⟨_, I, t, hI_d, hst, hmax, hbud, hfan_t, hd_t, hval, hout_at, hmul_cnt, hw_le⟩ :=
      hseg d hd
    have hcast : ((T (d + 1) - T d : ℕ) : ℝ) ≤ (t.outCount : ℝ) := by exact_mod_cast hw_le
    have hW := t.outCount_le_W hk d (D - d) k (T d) (T (d + 1)) I le_rfl hI_d (by omega)
      hst hmax (by omega) hfan_t hval hout_at hmul_cnt
    rw [W_eq_V (by omega)] at hW
    exact hcast.trans hW
  linarith

/-! ### Part 3: Characteristic polynomial `P_k`, positive root `α_k`, and optimal depth `D(N, k)` -/

/-- Characteristic polynomial `P_k(x) = 2 + x + ⋯ + x^{k-2} - x^k` governing the asymptotic growth
of optimal fanout-`k` prefix circuit widths ([Sergeev2025PrefixDepth], p. 2). -/
@[expose] def prefixCharPoly (k : ℕ) (x : ℝ) : ℝ :=
  2 + (∑ i ∈ Finset.Ico 1 (k - 1), x ^ i) - x ^ k

private theorem prefixCharPoly_succ_sub {k : ℕ} (hk : 2 ≤ k) (x : ℝ) :
    prefixCharPoly (k + 1) x - prefixCharPoly k x = x ^ (k - 1) * (1 + x - x ^ 2) := by
  unfold prefixCharPoly
  have hsum : ∑ i ∈ Finset.Ico 1 (k + 1 - 1), x ^ i =
      (∑ i ∈ Finset.Ico 1 (k - 1), x ^ i) + x ^ (k - 1) := by
    rw [Nat.add_sub_cancel, show k = (k - 1) + 1 by omega]
    exact Finset.sum_Ico_succ_top (by omega) (fun i => x ^ i)
  have hpow2 : x ^ (k + 1) = x ^ (k - 1) * x ^ 2 := by
    rw [← pow_add, show k - 1 + 2 = k + 1 by omega]
  have hpow1 : x ^ k = x ^ (k - 1) * x := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega]
    exact pow_succ x (k - 1)
  rw [hsum, hpow2, hpow1]
  ring

private theorem sub_one_mul_prefixCharPoly {k : ℕ} (hk : 2 ≤ k) (x : ℝ) :
    (x - 1) * prefixCharPoly k x = (x - 2) + x ^ (k - 1) * (1 + x - x ^ 2) := by
  induction hk with
  | refl =>
    unfold prefixCharPoly
    simp only [Nat.reduceSub, Finset.Ico_self, Finset.sum_empty, pow_one]
    ring
  | @step m hm ih =>
    change (x - 1) * prefixCharPoly (m + 1) x = (x - 2) + x ^ m * (1 + x - x ^ 2)
    have hm2 : 2 ≤ m := hm
    have hdiff := prefixCharPoly_succ_sub hm x
    have hstep : prefixCharPoly (m + 1) x =
        prefixCharPoly m x + x ^ (m - 1) * (1 + x - x ^ 2) := by linarith
    have hpow : x ^ m = x ^ (m - 1) * x := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega]
      exact pow_succ x (m - 1)
    rw [hstep, mul_add, ih, hpow]
    ring

private theorem prefixCharPoly_continuous (k : ℕ) : Continuous (prefixCharPoly k) := by
  unfold prefixCharPoly
  have hsum : ∀ s : Finset ℕ, Continuous fun x : ℝ => ∑ i ∈ s, x ^ i := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact continuous_const
    | @insert a s ha ih =>
      have heq : (fun x : ℝ => ∑ i ∈ insert a s, x ^ i) =
          fun x : ℝ => x ^ a + ∑ i ∈ s, x ^ i := by
        ext x
        exact Finset.sum_insert ha
      rw [heq]
      exact (continuous_pow a).add ih
  exact (continuous_const.add (hsum _)).sub (continuous_pow k)

private theorem prefixCharPoly_one_pos (k : ℕ) : 0 < prefixCharPoly k 1 := by
  unfold prefixCharPoly
  simp only [one_pow, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
  have hnn : (0 : ℝ) ≤ ((k - 1 - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith

private theorem prefixCharPoly_goldenRatio_neg {k : ℕ} (hk : 2 ≤ k) :
    prefixCharPoly k Real.goldenRatio < 0 := by
  have htel := sub_one_mul_prefixCharPoly hk Real.goldenRatio
  have hsq := Real.goldenRatio_sq
  have hgt := Real.one_lt_goldenRatio
  have hlt := Real.goldenRatio_lt_two
  have hzero : 1 + Real.goldenRatio - Real.goldenRatio ^ 2 = 0 := by linarith
  rw [hzero, mul_zero, add_zero] at htel
  nlinarith

private theorem prefixCharPoly_three_halves_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < prefixCharPoly k (3 / 2) := by
  have htel := sub_one_mul_prefixCharPoly (by omega : 2 ≤ k) (3 / 2)
  have hpow : (3 / 2 : ℝ) ^ 2 ≤ (3 / 2 : ℝ) ^ (k - 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hnum : (1 : ℝ) + 3 / 2 - (3 / 2) ^ 2 = 1 / 4 := by norm_num
  have hsq : (3 / 2 : ℝ) ^ 2 = 9 / 4 := by norm_num
  rw [hnum] at htel
  rw [hsq] at hpow
  linarith

private noncomputable def invPoly (k : ℕ) (x : ℝ) : ℝ :=
  2 * (x⁻¹) ^ k + (∑ i ∈ Finset.Ico 1 (k - 1), (x⁻¹) ^ (k - i)) - 1

private theorem pow_mul_invPoly {k : ℕ} {x : ℝ} (hx : 0 < x) :
    x ^ k * invPoly k x = prefixCharPoly k x := by
  unfold invPoly prefixCharPoly
  have hne : x ≠ 0 := hx.ne'
  have h1 : x ^ k * (2 * (x⁻¹) ^ k) = 2 := by
    rw [← mul_assoc, mul_comm (x ^ k) 2, mul_assoc, ← mul_pow, mul_inv_cancel₀ hne,
      one_pow, mul_one]
  have h2 : x ^ k * (∑ i ∈ Finset.Ico 1 (k - 1), (x⁻¹) ^ (k - i)) =
      ∑ i ∈ Finset.Ico 1 (k - 1), x ^ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_Ico] at hi
    have hxk : x ^ k = x ^ i * x ^ (k - i) := by
      rw [← pow_add, Nat.add_sub_of_le (by omega)]
    rw [hxk, mul_assoc, ← mul_pow, mul_inv_cancel₀ hne, one_pow, mul_one]
  linarith

private theorem invPoly_strictAnti {k : ℕ} (hk : 2 ≤ k) {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    invPoly k y < invPoly k x := by
  unfold invPoly
  have hy : 0 < y := hx.trans hxy
  have hx_inv : 0 < x⁻¹ := inv_pos.mpr hx
  have hy_inv : 0 < y⁻¹ := inv_pos.mpr hy
  have hmul_x : x * x⁻¹ = 1 := mul_inv_cancel₀ hx.ne'
  have hmul_y : y * y⁻¹ = 1 := mul_inv_cancel₀ hy.ne'
  have hinv : y⁻¹ < x⁻¹ := by
    by_contra hle
    have hge : x⁻¹ ≤ y⁻¹ := le_of_not_gt hle
    nlinarith
  have hpow_lt : (y⁻¹) ^ k < (x⁻¹) ^ k := pow_lt_pow_left₀ hinv hy_inv.le (by omega)
  have hsum_le : (∑ i ∈ Finset.Ico 1 (k - 1), (y⁻¹) ^ (k - i)) ≤
      ∑ i ∈ Finset.Ico 1 (k - 1), (x⁻¹) ^ (k - i) :=
    Finset.sum_le_sum fun i _ => pow_le_pow_left₀ hy_inv.le hinv.le _
  linarith

private theorem exists_root_mem_Icc {k : ℕ} (hk : 2 ≤ k) :
    ∃ r ∈ Set.Icc 1 Real.goldenRatio, prefixCharPoly k r = 0 := by
  have hmem : (0 : ℝ) ∈ Set.Icc (prefixCharPoly k Real.goldenRatio) (prefixCharPoly k 1) :=
    ⟨(prefixCharPoly_goldenRatio_neg hk).le, (prefixCharPoly_one_pos k).le⟩
  exact intermediate_value_Icc' Real.one_lt_goldenRatio.le
    (prefixCharPoly_continuous k).continuousOn hmem

/-- For `k ≥ 2`, the unique positive real root `α_k` of `prefixCharPoly k`
([Sergeev2025PrefixDepth], p. 2). Returns `0` when `k < 2`. -/
noncomputable def alphaRoot (k : ℕ) : ℝ :=
  if hk : 2 ≤ k then Classical.choose (exists_root_mem_Icc hk) else 0

private theorem alphaRoot_mem_Icc {k : ℕ} (hk : 2 ≤ k) :
    alphaRoot k ∈ Set.Icc 1 Real.goldenRatio := by
  unfold alphaRoot
  simp only [hk, ↓reduceDIte]
  exact (Classical.choose_spec (exists_root_mem_Icc hk)).1

/-- `alphaRoot k` is a root of `prefixCharPoly k` for all `k ≥ 2`
([Sergeev2025PrefixDepth], p. 2). -/
theorem prefixCharPoly_alphaRoot {k : ℕ} (hk : 2 ≤ k) :
    prefixCharPoly k (alphaRoot k) = 0 := by
  unfold alphaRoot
  simp only [hk, ↓reduceDIte]
  exact (Classical.choose_spec (exists_root_mem_Icc hk)).2

/-- `1 < alphaRoot k` for all `k ≥ 2`. -/
theorem one_lt_alphaRoot {k : ℕ} (hk : 2 ≤ k) : 1 < alphaRoot k := by
  have hle := (alphaRoot_mem_Icc hk).1
  refine lt_of_le_of_ne hle fun heq => ?_
  have hpos := prefixCharPoly_one_pos k
  have h0 := prefixCharPoly_alphaRoot hk
  rw [← heq] at h0
  linarith

/-- `alphaRoot k < Real.goldenRatio` for all `k ≥ 2`, immediate from `P_k(φ) < 0` for the
characteristic polynomial `P_k(x)` ([Sergeev2025PrefixDepth], p. 2). -/
theorem alphaRoot_lt_goldenRatio {k : ℕ} (hk : 2 ≤ k) :
    alphaRoot k < Real.goldenRatio := by
  have hle := (alphaRoot_mem_Icc hk).2
  refine lt_of_le_of_ne hle fun heq => ?_
  have hneg := prefixCharPoly_goldenRatio_neg hk
  have h0 := prefixCharPoly_alphaRoot hk
  rw [heq] at h0
  linarith

private theorem alphaRoot_pos {k : ℕ} (hk : 2 ≤ k) : 0 < alphaRoot k :=
  zero_lt_one.trans (one_lt_alphaRoot hk)

private theorem invPoly_alphaRoot {k : ℕ} (hk : 2 ≤ k) : invPoly k (alphaRoot k) = 0 := by
  have hmul := pow_mul_invPoly (k := k) (alphaRoot_pos hk)
  rw [prefixCharPoly_alphaRoot hk] at hmul
  have hp : 0 < (alphaRoot k) ^ k := pow_pos (alphaRoot_pos hk) k
  exact (mul_eq_zero.mp hmul).resolve_left hp.ne'

private theorem lt_alphaRoot_of_pos_of_prefixCharPoly_pos {k : ℕ} {x : ℝ}
    (hk : 2 ≤ k) (hx : 0 < x) (hpos : 0 < prefixCharPoly k x) :
    x < alphaRoot k := by
  have hinv_pos : 0 < invPoly k x := by
    have hmul := pow_mul_invPoly (k := k) hx
    have hp : 0 < x ^ k := pow_pos hx k
    nlinarith
  have hinv_root := invPoly_alphaRoot hk
  by_contra hge
  have hle : alphaRoot k ≤ x := le_of_not_gt hge
  rcases eq_or_lt_of_le hle with rfl | hlt
  · linarith
  · have hanti := invPoly_strictAnti hk (alphaRoot_pos hk) hlt
    linarith

/-- Uniqueness of the positive root `alphaRoot k` of `prefixCharPoly k` for `k ≥ 2`
([Sergeev2025PrefixDepth], p. 2). -/
theorem eq_alphaRoot_of_pos_of_prefixCharPoly_eq_zero {k : ℕ} {x : ℝ}
    (hk : 2 ≤ k) (hx : 0 < x) (h0 : prefixCharPoly k x = 0) :
    x = alphaRoot k := by
  have hinv_x : invPoly k x = 0 := by
    have hmul := pow_mul_invPoly (k := k) hx
    rw [h0] at hmul
    have hp : 0 < x ^ k := pow_pos hx k
    exact (mul_eq_zero.mp hmul).resolve_left hp.ne'
  have hinv_root := invPoly_alphaRoot hk
  rcases lt_trichotomy x (alphaRoot k) with hlt | heq | hgt
  · have := invPoly_strictAnti hk hx hlt
    linarith
  · exact heq
  · have := invPoly_strictAnti hk (alphaRoot_pos hk) hgt
    linarith

/-- Original auxiliary root lower bound `3 / 2 < alphaRoot k` for all `k ≥ 3` (via
`prefixCharPoly k (3 / 2) > 0`), used in the inhomogeneous recurrence bound of
`width_le_mul_alphaRoot_pow`. -/
theorem three_halves_lt_alphaRoot {k : ℕ} (hk : 3 ≤ k) :
    (3 / 2 : ℝ) < alphaRoot k :=
  lt_alphaRoot_of_pos_of_prefixCharPoly_pos (by omega) (by norm_num)
    (prefixCharPoly_three_halves_pos hk)

/-- At fanout `k = 2`, `alphaRoot 2 = √2`, immediate from `P_2(x) = 2 - x^2`
([Sergeev2025PrefixDepth], p. 2). -/
theorem alphaRoot_two : alphaRoot 2 = Real.sqrt 2 := by
  symm
  refine eq_alphaRoot_of_pos_of_prefixCharPoly_eq_zero le_rfl (Real.sqrt_pos.mpr (by norm_num)) ?_
  unfold prefixCharPoly
  simp only [Nat.reduceSub, Finset.Ico_self, Finset.sum_empty, add_zero]
  rw [Real.sq_sqrt (by norm_num)]
  ring

/-- The positive roots `alphaRoot k` form a strictly increasing sequence on `k ≥ 2`, immediate from
the definition of `P_k(x)` ([Sergeev2025PrefixDepth], p. 2). -/
theorem alphaRoot_strictMonoOn : StrictMonoOn alphaRoot (Set.Ici 2) := by
  have hstep : ∀ k ≥ 2, alphaRoot k < alphaRoot (k + 1) := by
    intro k hk
    set x := alphaRoot k
    have hx_pos := alphaRoot_pos hk
    have hx_lt_two : x < 2 := (alphaRoot_lt_goldenRatio hk).trans Real.goldenRatio_lt_two
    have htel := sub_one_mul_prefixCharPoly hk x
    rw [prefixCharPoly_alphaRoot hk, mul_zero] at htel
    have hdiff := prefixCharPoly_succ_sub hk x
    rw [prefixCharPoly_alphaRoot hk, sub_zero] at hdiff
    have hnext_pos : 0 < prefixCharPoly (k + 1) x := by linarith
    exact lt_alphaRoot_of_pos_of_prefixCharPoly_pos (by omega) hx_pos hnext_pos
  intro a ha b _ hab
  simp only [Set.mem_Ici] at ha
  obtain ⟨m, rfl⟩ : ∃ m, b = a + m + 1 := ⟨b - a - 1, by omega⟩
  have hadd : ∀ n : ℕ, alphaRoot a < alphaRoot (a + n + 1) := by
    intro n
    induction n with
    | zero => exact hstep a ha
    | succ n ih => exact ih.trans (hstep (a + n + 1) (by omega))
  exact hadd m

/-- As `k → ∞`, `alphaRoot k` converges to the golden ratio `φ = (1 + √5) / 2`
([Sergeev2025PrefixDepth], p. 2). -/
theorem tendsto_alphaRoot_atTop :
    Filter.Tendsto alphaRoot Filter.atTop (nhds Real.goldenRatio) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have h54_lt : (5 / 4 : ℝ) < Real.goldenRatio := by
      by_contra hge
      have hle : Real.goldenRatio ≤ 5 / 4 := le_of_not_gt hge
      nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
    set c := max a (5 / 4)
    have hc_ge_a : a ≤ c := le_max_left a (5 / 4)
    have hc_ge_54 : (5 / 4 : ℝ) ≤ c := le_max_right a (5 / 4)
    have hc1 : 1 < c := by linarith
    have hc_lt : c < Real.goldenRatio := max_lt ha h54_lt
    have hquad_pos : 0 < 1 + c - c ^ 2 := by
      have hfac : 1 + c - c ^ 2 = (Real.goldenRatio - c) * (c + Real.goldenRatio - 1) := by
        have hsq := Real.goldenRatio_sq
        nlinarith
      rw [hfac]
      have hgt1 := Real.one_lt_goldenRatio
      nlinarith
    have hpow_lim := Filter.tendsto_atTop.mp (tendsto_pow_atTop_atTop_of_one_lt hc1)
      ((2 - c) / (1 + c - c ^ 2) + 1)
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hpow_lim
    refine Filter.eventually_atTop.mpr ⟨max 2 (M + 1), fun k hk => ?_⟩
    have hk2 : 2 ≤ k := (le_max_left 2 (M + 1)).trans hk
    have hkM : M ≤ k - 1 := by
      have := (le_max_right 2 (M + 1)).trans hk
      omega
    have hcm := hM (k - 1) hkM
    have hdiv_lt : (2 - c) / (1 + c - c ^ 2) < c ^ (k - 1) := by linarith
    have hmul_gt : 2 - c < c ^ (k - 1) * (1 + c - c ^ 2) := (div_lt_iff₀ hquad_pos).mp hdiv_lt
    have htel := sub_one_mul_prefixCharPoly hk2 c
    have hc_poly_pos : 0 < prefixCharPoly k c := by nlinarith
    exact hc_ge_a.trans_lt (lt_alphaRoot_of_pos_of_prefixCharPoly_pos hk2 (by linarith) hc_poly_pos)
  · exact Filter.eventually_atTop.mpr ⟨2, fun k hk => (alphaRoot_lt_goldenRatio hk).trans hb⟩

private theorem pow_recurrence_sub {k D : ℕ} (hk : 2 ≤ k) (hD : k ≤ D) (x : ℝ) :
    x ^ D - (∑ j ∈ Finset.Ico 2 k, x ^ (D - j)) - 2 * x ^ (D - k) =
      -x ^ (D - k) * prefixCharPoly k x := by
  unfold prefixCharPoly
  have hsum : ∑ j ∈ Finset.Ico 2 k, x ^ (D - j) =
      x ^ (D - k) * ∑ i ∈ Finset.Ico 1 (k - 1), x ^ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_bij (fun j _ => k - j) ?_ ?_ ?_ ?_
    · intro j hj; simp only [Finset.mem_Ico] at hj ⊢; omega
    · intro j₁ hj₁ j₂ hj₂ heq; simp only [Finset.mem_Ico] at hj₁ hj₂; omega
    · intro i hi
      simp only [Finset.mem_Ico] at hi
      exact ⟨k - i, by simp only [Finset.mem_Ico]; omega, by omega⟩
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      rw [← pow_add, show D - k + (k - j) = D - j by omega]
  have hpow : x ^ D = x ^ (D - k) * x ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hD]
  rw [hsum, hpow]
  ring

private theorem alphaRoot_pow_le_maxCircuitWidthUpper {k : ℕ} (hk : 2 ≤ k) :
    ∀ D : ℕ, ((alphaRoot k) ^ k)⁻¹ * (alphaRoot k) ^ D ≤ (maxCircuitWidthUpper k D : ℝ) := by
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
    set α := alphaRoot k
    have hα1 := one_lt_alphaRoot hk
    have hα_pos : 0 < α := zero_lt_one.trans hα1
    have hαk_pos : 0 < α ^ k := pow_pos hα_pos k
    by_cases hD : D < k
    · have hpow_le : α ^ D ≤ α ^ k := pow_le_pow_right₀ hα1.le hD.le
      have hlhs_le : (α ^ k)⁻¹ * α ^ D ≤ 1 := by
        have := mul_le_mul_of_nonneg_left hpow_le (inv_nonneg.mpr hαk_pos.le)
        rwa [inv_mul_cancel₀ hαk_pos.ne'] at this
      have hw1 : 1 ≤ maxCircuitWidthUpper k D := by
        unfold maxCircuitWidthUpper
        have hmem : 0 ∈ Finset.range (D + 1) := Finset.mem_range.mpr (by omega)
        have h0 : 1 ≤ maxConsistentWidth k 0 (D - 0) := by
          rw [maxConsistentWidth_zero_left hk]
        exact h0.trans
          (Finset.single_le_sum (f := fun d => maxConsistentWidth k d (D - d))
            (fun _ _ => Nat.zero_le _) hmem)
      exact hlhs_le.trans (by exact_mod_cast hw1)
    · have hkD : k ≤ D := le_of_not_gt hD
      have hrec_α := pow_recurrence_sub hk hkD α
      rw [prefixCharPoly_alphaRoot hk, mul_zero] at hrec_α
      have hαD : α ^ D = (∑ j ∈ Finset.Ico 2 k, α ^ (D - j)) + 2 * α ^ (D - k) := by linarith
      have hlhs : (α ^ k)⁻¹ * α ^ D =
          (∑ j ∈ Finset.Ico 2 k, (α ^ k)⁻¹ * α ^ (D - j)) +
            2 * ((α ^ k)⁻¹ * α ^ (D - k)) := by
        rw [hαD, mul_add, Finset.mul_sum]
        ring
      have hsum_le : (∑ j ∈ Finset.Ico 2 k, (α ^ k)⁻¹ * α ^ (D - j)) ≤
          ∑ j ∈ Finset.Ico 2 k, (maxCircuitWidthUpper k (D - j) : ℝ) := by
        refine Finset.sum_le_sum fun j hj => ?_
        simp only [Finset.mem_Ico] at hj
        exact ih (D - j) (by omega)
      have hlast_le := ih (D - k) (by omega)
      have hrec_W := maxCircuitWidthUpper_recurrence hk hkD
      have hrec_W_real : (maxCircuitWidthUpper k D : ℝ) =
          (∑ j ∈ Finset.Ico 2 k, (maxCircuitWidthUpper k (D - j) : ℝ)) +
            2 * (maxCircuitWidthUpper k (D - k) : ℝ) + (k : ℝ) := by
        exact_mod_cast hrec_W
      have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith

private theorem maxCircuitWidthUpper_zero {k : ℕ} (hk : 2 ≤ k) :
    maxCircuitWidthUpper k 0 = 1 := by
  rw [maxCircuitWidthUpper, Finset.sum_range_one, Nat.sub_zero, maxConsistentWidth_zero_left hk]

/-- Exponential upper bound on the input width of any optimal (zero-deficiency) fanout-`k`
universal prefix circuit in terms of `(alphaRoot k) ^ c.depth` ([Sergeev2025PrefixDepth],
pp. 3–5). -/
theorem width_le_mul_alphaRoot_pow {k : ℕ} (hk : 2 ≤ k) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {N : ℕ}, 1 ≤ N →
      ∀ {c : PrefixCircuit N}, IsOptimalPrefixCircuit c → FanoutAtMost c k →
        (N : ℝ) ≤ A * (alphaRoot k) ^ c.depth := by
  by_cases hk2 : k = 2
  · subst hk2
    refine ⟨4, by norm_num, fun {N} hN {c} hopt hfan => ?_⟩
    set α := alphaRoot 2
    have hα1 := one_lt_alphaRoot (k := 2) le_rfl
    have hα_pos : 0 < α := zero_lt_one.trans hα1
    have hα_sq : α ^ 2 = 2 := by
      have h0 := prefixCharPoly_alphaRoot (k := 2) le_rfl
      unfold prefixCharPoly at h0
      simp only [Nat.reduceSub, Finset.Ico_self, Finset.sum_empty, add_zero] at h0
      linarith
    have hu_bound : ∀ D : ℕ, (maxCircuitWidthUpper 2 D : ℝ) + 2 ≤ 4 * α ^ D := by
      intro D
      induction D using Nat.strong_induction_on with
      | _ D ih =>
        match D with
        | 0 =>
          rw [maxCircuitWidthUpper_zero le_rfl, pow_zero]
          norm_num
        | 1 =>
          have h1 : maxCircuitWidthUpper 2 1 = 2 := by
            rw [maxCircuitWidthUpper, Finset.sum_range_succ, Finset.sum_range_one, Nat.sub_zero,
              Nat.sub_self, maxConsistentWidth_zero_left le_rfl,
              maxConsistentWidth_zero_right le_rfl]
          rw [h1, pow_one, Nat.cast_ofNat]
          linarith
        | m + 2 =>
          have hrec := maxCircuitWidthUpper_recurrence (k := 2) le_rfl (by omega : 2 ≤ m + 2)
          simp only [Finset.Ico_self, Finset.sum_empty, zero_add, Nat.add_sub_cancel] at hrec
          have hrec_r : (maxCircuitWidthUpper 2 (m + 2) : ℝ) + 2 =
              2 * ((maxCircuitWidthUpper 2 m : ℝ) + 2) := by
            have hcast : (maxCircuitWidthUpper 2 (m + 2) : ℝ) =
                2 * (maxCircuitWidthUpper 2 m : ℝ) + 2 := by exact_mod_cast hrec
            linarith
          have hih := ih m (by omega)
          have hpow : α ^ (m + 2) = 2 * α ^ m := by
            rw [pow_add, hα_sq, mul_comm]
          linarith
    have hN_w : N ≤ maxCircuitWidthUpper 2 c.depth := width_le_maxCircuitWidthUpper_two hN hopt hfan
    have hN_r : (N : ℝ) ≤ (maxCircuitWidthUpper 2 c.depth : ℝ) := by exact_mod_cast hN_w
    linarith [hu_bound c.depth]
  · have hk3 : 3 ≤ k := by omega
    set α := alphaRoot k
    have hα1 := one_lt_alphaRoot hk
    have hp32 := prefixCharPoly_three_halves_pos hk3
    set b : ℝ := (3 / 2 : ℝ) ^ k / prefixCharPoly k (3 / 2)
    have hb_pos : 0 < b := div_pos (by positivity) hp32
    set A : ℝ := 1 + ∑ m ∈ Finset.range k, (V_star k m + b * (3 / 2 : ℝ) ^ m + 1)
    have hterm_nn : ∀ m, 0 ≤ V_star k m + b * (3 / 2 : ℝ) ^ m + 1 := by
      intro m
      have hvs : 0 ≤ V_star k m :=
        Finset.sum_nonneg fun d _ => V_nonneg k d (m - d)
      have hbm : 0 ≤ b * (3 / 2 : ℝ) ^ m := mul_nonneg hb_pos.le (by positivity)
      linarith
    have hA1 : 1 ≤ A := by
      have hsum_nn : 0 ≤ ∑ m ∈ Finset.range k, (V_star k m + b * (3 / 2 : ℝ) ^ m + 1) :=
        Finset.sum_nonneg fun m _ => hterm_nn m
      linarith
    set B : ℕ → ℝ := fun D => A * α ^ D - b * (3 / 2 : ℝ) ^ D - 1
    have hV_le_B : ∀ D : ℕ, V_star k D ≤ B D := by
      intro D
      induction D using Nat.strong_induction_on with
      | _ D ih =>
        by_cases hD : D < k
        · have hmem : D ∈ Finset.range k := Finset.mem_range.mpr hD
          have hle_A : V_star k D + b * (3 / 2 : ℝ) ^ D + 1 ≤ A := by
            have := Finset.single_le_sum (fun m _ => hterm_nn m) hmem
            linarith
          have hpow1 : 1 ≤ α ^ D := one_le_pow₀ hα1.le
          have hA_le : A ≤ A * α ^ D := le_mul_of_one_le_right (by linarith) hpow1
          dsimp only [B]
          linarith
        · have hkD : k ≤ D := le_of_not_gt hD
          have hrec_α := pow_recurrence_sub hk hkD α
          rw [prefixCharPoly_alphaRoot hk, mul_zero] at hrec_α
          have hrec_32 := pow_recurrence_sub hk hkD (3 / 2)
          have hb_mul : b * ((3 / 2 : ℝ) ^ (D - k) * prefixCharPoly k (3 / 2)) =
              (3 / 2 : ℝ) ^ D := by
            dsimp only [b]
            have h1 : (3 / 2 : ℝ) ^ k / prefixCharPoly k (3 / 2) *
                ((3 / 2 : ℝ) ^ (D - k) * prefixCharPoly k (3 / 2)) =
                (3 / 2 : ℝ) ^ k * (3 / 2 : ℝ) ^ (D - k) := by
              field_simp [hp32.ne']
            rw [h1, ← pow_add, Nat.add_sub_of_le hkD]
          have hconst : (∑ j ∈ Finset.Ico 2 k, (1 : ℝ)) = ((k - 2 : ℕ) : ℝ) := by
            simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
          have hk_cast : ((k - 1 : ℕ) : ℝ) = ((k - 2 : ℕ) : ℝ) + 1 := by
            rw [show k - 1 = (k - 2) + 1 by omega, Nat.cast_add, Nat.cast_one]
          have hB_rec : B D = (∑ j ∈ Finset.Ico 2 k, B (D - j)) + 2 * B (D - k) +
              (3 / 2 : ℝ) ^ D + ((k - 1 : ℕ) : ℝ) := by
            have hsum_B : ∑ j ∈ Finset.Ico 2 k, B (D - j) =
                A * (∑ j ∈ Finset.Ico 2 k, α ^ (D - j)) -
                  b * (∑ j ∈ Finset.Ico 2 k, (3 / 2 : ℝ) ^ (D - j)) -
                  ((k - 2 : ℕ) : ℝ) := by
              dsimp only [B]
              rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
                ← Finset.mul_sum, hconst]
            dsimp only [B]
            rw [hsum_B, hk_cast]
            nlinarith [hrec_α, hrec_32, hb_mul]
          have hV_rec := V_star_recurrence hk3 hkD
          have hsum_le : ∑ j ∈ Finset.Ico 2 k, V_star k (D - j) ≤
              ∑ j ∈ Finset.Ico 2 k, B (D - j) := by
            refine Finset.sum_le_sum fun j hj => ?_
            simp only [Finset.mem_Ico] at hj
            exact ih (D - j) (by omega)
          have hlast_le := ih (D - k) (by omega)
          linarith
    refine ⟨A, hA1, fun {N} hN {c} hopt hfan => ?_⟩
    have hNV := width_le_V_star hk3 hN hopt hfan
    have hVB := hV_le_B c.depth
    have hbm : 0 ≤ b * (3 / 2 : ℝ) ^ c.depth := mul_nonneg hb_pos.le (by positivity)
    dsimp only [B] at hVB
    linarith

/-- Minimal depth `D(N, k)` of an optimal (zero-deficiency) universal prefix circuit on `N` inputs
with wire fanout bounded by `k` ([Sergeev2025PrefixDepth], p. 2). -/
@[expose] noncomputable def optimalPrefixDepth (N k : ℕ) : ℕ :=
  sInf {D : ℕ | ∃ c : PrefixCircuit N,
    IsOptimalPrefixCircuit c ∧ FanoutAtMost c k ∧ c.depth = D}

/-- For every `k ≥ 2` and `N ≥ 1`, there exists an optimal fanout-`k` universal prefix circuit on
`N` inputs attaining depth `optimalPrefixDepth N k`. -/
theorem exists_optimalPrefixCircuit_depth_eq {N k : ℕ} (hk : 2 ≤ k) (hN : 1 ≤ N) :
    ∃ c : PrefixCircuit N,
      IsOptimalPrefixCircuit c ∧ FanoutAtMost c k ∧ c.depth = optimalPrefixDepth N k := by
  obtain ⟨c₀, _, hopt₀, hfan₀, _⟩ := exists_rippleOptimalPrefixCircuit hk hN
  have hne : {D : ℕ | ∃ c : PrefixCircuit N,
      IsOptimalPrefixCircuit c ∧ FanoutAtMost c k ∧ c.depth = D}.Nonempty :=
    ⟨c₀.depth, c₀, hopt₀, hfan₀, rfl⟩
  exact Nat.sInf_mem hne

/-- On a single input `N = 1`, the minimal depth of an optimal fanout-`k` prefix circuit is `0`. -/
theorem optimalPrefixDepth_one {k : ℕ} (hk : 2 ≤ k) : optimalPrefixDepth 1 k = 0 := by
  obtain ⟨c₀, _, hopt₀, hfan₀, hd₀⟩ := exists_rippleOptimalPrefixCircuit hk (le_rfl : 1 ≤ 1)
  have hle : optimalPrefixDepth 1 k ≤ c₀.depth := Nat.sInf_le ⟨c₀, hopt₀, hfan₀, rfl⟩
  omega

/-- Exact threshold characterization of `optimalPrefixDepth N 2` for `D ≥ 1` and `N ≥ 1`:
`optimalPrefixDepth N 2 ≤ D` if and only if `N ≤ 1 + maxCircuitWidthUpper 2 (D - 1)`
([Sergeev2025PrefixDepth], pp. 2–3, following Eq. (3)). -/
theorem optimalPrefixDepth_two_le_iff {N D : ℕ} (hN : 1 ≤ N) (hD : 1 ≤ D) :
    optimalPrefixDepth N 2 ≤ D ↔ N ≤ 1 + maxCircuitWidthUpper 2 (D - 1) := by
  constructor
  · intro hle
    by_cases hN1 : N = 1
    · omega
    · obtain ⟨c, hopt, hfan, hd_eq⟩ := exists_optimalPrefixCircuit_depth_eq (k := 2) le_rfl hN
      have hcD_pos : 1 ≤ c.depth := by
        by_contra h0
        have hc0 : c.depth = 0 := by omega
        have hw := width_le_maxCircuitWidthUpper_two hN hopt hfan
        rw [hc0, maxCircuitWidthUpper_zero le_rfl] at hw
        omega
      have hw := width_le_one_add_maxCircuitWidthUpper_two hN hopt hfan hcD_pos
      refine hw.trans (Nat.add_le_add_left ?_ 1)
      have hd_le : c.depth - 1 ≤ D - 1 := by omega
      have hmono : ∀ m₁ m₂, m₁ ≤ m₂ → maxCircuitWidthUpper 2 m₁ ≤ maxCircuitWidthUpper 2 m₂ := by
        intro m₁ m₂ hm
        induction hm with
        | refl => exact le_rfl
        | @step m _ ihm =>
          refine ihm.trans ?_
          unfold maxCircuitWidthUpper
          rw [Finset.sum_range_succ (n := m + 1)]
          refine le_trans ?_ (Nat.le_add_right _ _)
          refine Finset.sum_le_sum fun d hd => ?_
          rw [Finset.mem_range] at hd
          rw [maxConsistentWidth_two, maxConsistentWidth_two]
          exact Nat.pow_le_pow_right (by omega) (by omega)
      exact hmono _ _ hd_le
  · intro hN_ub
    obtain ⟨c, hopt, hfan, hd_le⟩ :=
      exists_optimalPrefixCircuit_of_le_maxCircuitWidthUpper le_rfl hD hN hN_ub
    have hmem : c.depth ∈ {D' : ℕ | ∃ c : PrefixCircuit N,
        IsOptimalPrefixCircuit c ∧ FanoutAtMost c 2 ∧ c.depth = D'} :=
      ⟨c, hopt, hfan, rfl⟩
    exact (Nat.sInf_le hmem).trans hd_le

/-- **Sergeev's Theorem** ([Sergeev2025PrefixDepth], p. 2): for every fanout bound `k ≥ 2`, there
exists a constant `C ≥ 0` (depending only on `k`) such that for every input width `N ≥ 1`, the
minimal depth `optimalPrefixDepth N k` of an optimal (zero-deficiency) fanout-`k` universal prefix
circuit on `N` inputs satisfies
`|(optimalPrefixDepth N k : ℝ) - Real.logb (alphaRoot k) N| ≤ C`. -/
theorem abs_optimalPrefixDepth_sub_logb_le {k : ℕ} (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      |(optimalPrefixDepth N k : ℝ) - Real.logb (alphaRoot k) N| ≤ C := by
  set α := alphaRoot k
  have hα1 := one_lt_alphaRoot hk
  have hα_pos : 0 < α := zero_lt_one.trans hα1
  obtain ⟨A, hA1, hA_bound⟩ := width_le_mul_alphaRoot_pow hk
  have hlogA_nn : 0 ≤ Real.logb α A := by
    have := Real.logb_le_logb_of_le hα1 zero_lt_one hA1
    simpa only [Real.logb_one] using this
  set C : ℝ := Real.logb α A + ((k : ℝ) + 2)
  have hC_nn : 0 ≤ C := by
    dsimp only [C]
    have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  refine ⟨C, hC_nn, fun N hN => ?_⟩
  set D := optimalPrefixDepth N k
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN_ge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN_nn : 0 ≤ Real.logb α N := by
    have := Real.logb_le_logb_of_le hα1 zero_lt_one hN_ge1
    simpa only [Real.logb_one] using this
  have hlow : Real.logb α N - C ≤ (D : ℝ) := by
    obtain ⟨c, hopt, hfan, hd_eq⟩ := exists_optimalPrefixCircuit_depth_eq hk hN
    change c.depth = D at hd_eq
    have hN_ub : (N : ℝ) ≤ A * α ^ D := by
      rw [← hd_eq]
      exact hA_bound hN hopt hfan
    have hlog_ub := Real.logb_le_logb_of_le hα1 hN_pos hN_ub
    rw [Real.logb_mul (by linarith) (pow_pos hα_pos D).ne', Real.logb_pow,
      Real.logb_self_eq_one hα1, mul_one] at hlog_ub
    dsimp only [C]
    have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hhigh : (D : ℝ) - Real.logb α N ≤ C := by
    by_cases hsmall : D ≤ k + 1
    · have hD_le : (D : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast hsmall
      dsimp only [C]
      linarith
    · have hk2_le : k + 2 ≤ D := by omega
      have hnot_prev : 1 + maxCircuitWidthUpper k (D - 2) < N := by
        by_contra hge
        have hle : N ≤ 1 + maxCircuitWidthUpper k ((D - 1) - 1) := by
          rw [show (D - 1) - 1 = D - 2 by omega]
          omega
        obtain ⟨c, hopt, hfan, hd_le⟩ :=
          exists_optimalPrefixCircuit_of_le_maxCircuitWidthUpper hk (by omega : 1 ≤ D - 1) hN hle
        have hmem : c.depth ∈ {D' : ℕ | ∃ c : PrefixCircuit N,
            IsOptimalPrefixCircuit c ∧ FanoutAtMost c k ∧ c.depth = D'} :=
          ⟨c, hopt, hfan, rfl⟩
        have hD_le_c : D ≤ c.depth := Nat.sInf_le hmem
        omega
      have hw_lt : (maxCircuitWidthUpper k (D - 2) : ℝ) < (N : ℝ) := by
        exact_mod_cast (by omega : maxCircuitWidthUpper k (D - 2) < N)
      have hexp_lb := alphaRoot_pow_le_maxCircuitWidthUpper hk (D - 2)
      have hpow_lt : (α ^ k)⁻¹ * α ^ (D - 2) < (N : ℝ) := hexp_lb.trans_lt hw_lt
      have hαD_eq : α ^ D = α ^ (k + 2) * ((α ^ k)⁻¹ * α ^ (D - 2)) := by
        have h1 : α ^ (k + 2) * ((α ^ k)⁻¹ * α ^ (D - 2)) =
            (α ^ k * (α ^ k)⁻¹) * (α ^ 2 * α ^ (D - 2)) := by
          rw [pow_add α k 2]
          ring
        rw [h1, mul_inv_cancel₀ (pow_pos hα_pos k).ne', one_mul, ← pow_add,
          show 2 + (D - 2) = D by omega]
      have hαD_le : α ^ D ≤ α ^ (k + 2) * (N : ℝ) := by
        rw [hαD_eq]
        exact mul_le_mul_of_nonneg_left hpow_lt.le (pow_pos hα_pos (k + 2)).le
      have hlog_le := Real.logb_le_logb_of_le hα1 (pow_pos hα_pos D) hαD_le
      rw [Real.logb_pow, Real.logb_self_eq_one hα1, mul_one,
        Real.logb_mul (pow_pos hα_pos (k + 2)).ne' hN_pos.ne',
        Real.logb_pow, Real.logb_self_eq_one hα1, mul_one, Nat.cast_add,
        Nat.cast_ofNat] at hlog_le
      dsimp only [C]
      linarith
  exact abs_sub_le_iff.mpr ⟨hhigh, by linarith⟩

end Cslib.Circuits.Prefix
