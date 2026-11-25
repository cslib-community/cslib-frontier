/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.Price.Basic
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.Fan
public import CslibFrontier.Foundations.Geometry.CAT0.Basic
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.MidpointTerm
import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.Price.Random
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Every price is the metric of a price space

Proposition C.3 of *VP ≠ VNP over every field* [AnthropicVPVNP2026]. Every price `w` on a set `V`
is the pull-back of the metric of a complete CAT(0) space whose metric is a price
(`exists_completeCAT0Space_of_isPrice`).

The proof follows the paper. Formal midpoint terms over `V` (`FreeMagma V`, with C1's
`Separation.MidpointTerm.depth` and `place`) are added depth by depth, each new point placed by
random points (Proposition A.8) halfway between its two arguments; together the steps form a price
in which every new point is a midpoint of its pair. After identifying points at distance `0`, the
completion satisfies the CN inequality by Theorem C.1 (`isPrice_sq_le_of_mid`), since midpoints of
Cauchy sequences are Cauchy, and its metric is a price as a limit.

## Main results

* `exists_completeCAT0Space_of_isPrice`: Proposition C.3.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Proposition C.3 of the paper; module `Paper.Curvature` (`prop_space`)
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Curvature

open Finset Filter Topology Cslib.PartyTensor

variable {K : Type} [Field K]

section Space

open Cslib.CAT0 Cslib.Circuits.Arithmetic.Separation.MidpointTerm

variable {V : Type} {w : V → V → ℝ}

/-- One step of the proof of Proposition C.3: let V_{l+1} be V_l with a new point for each
pair of its points; define
prices by placing each new point at either end with probability ½ (Proposition A.8). The
points are named by terms;
V_n consists of the terms of depth at most n. -/
private theorem prop_space_step {d : FreeMagma V → FreeMagma V → ℝ} (hd : IsPrice K d) (n : ℕ) :
    ∃ d' : FreeMagma V → FreeMagma V → ℝ, IsPrice K d' ∧
      (∀ s t, (depth s) ≤ n → (depth t) ≤ n → d' s t = d s t) ∧
      ∀ s t, max (depth s) (depth t) = n →
        d' s (s * t) ≤ d s t / 2 ∧ d' t (s * t) ≤ d s t / 2 := by
  obtain ⟨w', h1, h2, h3⟩ := IsPrice.exists_extend_of_weights hd (Q := FreeMagma V × FreeMagma V)
      (Λ := Fin 2) (fun _ => 1 / 2)
    (fun _ => by norm_num) (by simp) (fun l κ => if l = 0 then κ.1 else κ.2)
  refine ⟨fun s t => w' (MidpointTerm.place n s) (MidpointTerm.place n t), h1.comp _, ?_, ?_⟩
  · intro s t hs ht
    simpa only [MidpointTerm.place, ite_eq_left hs, ite_eq_left ht] using h2 s t
  · intro s t hst
    have hm : ¬ depth (s * t) ≤ n := by simp only [depth, hst]; omega
    simp only [MidpointTerm.place, ite_eq_left (hst ▸ le_max_left _ _),
      ite_eq_left (hst ▸ le_max_right _ _), ite_eq_right hm]
    have g1 := h3 (Sum.inl s) (Sum.inr (s, t))
    have g2 := h3 (Sum.inl t) (Sum.inr (s, t))
    simp only
        [Fin.sum_univ_two, Sum.elim_inl, Sum.elim_inr, id, ite_true, Fin.isValue, one_ne_zero,
            ite_false] at g1 g2
    rw [hd.self] at g1 g2
    rw [hd.symm t s] at g2
    constructor <;> linarith

/-- Each step extends the one before, so together they form a price; in it each new point is a
midpoint of its pair. -/
private theorem prop_space_midpoints (hw : IsPrice K w) : ∃ d : FreeMagma V → FreeMagma V → ℝ,
    IsPrice K d ∧
    (∀ a b, d (FreeMagma.of a) (FreeMagma.of b) = w a b) ∧
    ∀ s t, d s (s * t) ≤ d s t / 2 ∧ d t (s * t) ≤ d s t / 2 := by
  choose! f hf1 hf2 hf3 using fun (n : ℕ) (d : FreeMagma V → FreeMagma V → ℝ)
      (hd : IsPrice K d) => prop_space_step hd n
  let D : ℕ → FreeMagma V → FreeMagma V → ℝ := fun n => Nat.rec (fun s t => w (base s) (base t))
      (fun n d => f n d) n
  have hDs : ∀ n, D (n + 1) = f n (D n) := fun _ => rfl
  have hP (n : ℕ) : IsPrice K (D n) := Nat.rec (hw.comp _) (fun n ih => hf1 n _ ih) n
  have hst (n k s t) (hs : depth s ≤ n) (ht : depth t ≤ n) : D (n + k) s t = D n s t := by
    induction k with
    | zero => rfl
    | succ k ih => rw [← add_assoc, hDs, hf2 _ _ (hP _) s t (by omega) (by omega), ih]
  refine ⟨fun s t => D (max (depth s) (depth t)) s t, ?_, fun _ _ => rfl, fun s t => ?_⟩
  · refine isPrice_of_tendsto (l := atTop) (d := D) (fun s t => tendsto_const_nhds.congr' ?_)
      (Eventually.of_forall hP)
    filter_upwards [eventually_ge_atTop (max (depth s) (depth t))] with n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact (hst _ k s t (le_max_left _ _) (le_max_right _ _)).symm
  · have e1 : max (depth s) (depth (s * t)) = max (depth s) (depth t) + 1 := by
      simp only [depth]; omega
    have e2 : max (depth t) (depth (s * t)) = max (depth s) (depth t) + 1 := by
      simp only [depth]; omega
    simpa only [e1, e2, hDs] using hf3 _ _ (hP _) s t rfl

/-- Midpoints of Cauchy sequences are Cauchy by (CN) itself: if a n → x and b n → v, and m n
satisfies (CN) for a n and b n,
then (m n) is a Cauchy sequence. -/
private theorem prop_space_cauchy {X : Type*} [MetricSpace X] {a b m : ℕ → X} {x v : X}
    (ha : Tendsto a atTop (𝓝 x))
    (hb : Tendsto b atTop (𝓝 v))
    (hm : ∀ n z,
        dist z (m n) ^ 2 ≤ (dist z (a n) ^ 2 + dist z (b n) ^ 2) / 2 - dist (a n) (b n) ^ 2 / 4) :
    CauchySeq m := by
  have hmid (n) : dist (a n) (m n) ≤ dist (a n) (b n) / 2 ∧
      dist (b n) (m n) ≤ dist (a n) (b n) / 2 := by
    have h1 := hm n (a n)
    have h2 := hm n (b n)
    rw [dist_self] at h1 h2
    rw [dist_comm (b n) (a n)] at h2
    exact ⟨(abs_le_of_sq_le_sq' (by nlinarith) (by positivity)).2,
      (abs_le_of_sq_le_sq' (by nlinarith) (by positivity)).2⟩
  rw [Metric.cauchySeq_iff]
  intro ε hε
  set R := dist x v + 1
  have hR0 : 0 < R := by positivity
  set δ := min 1 (ε ^ 2 / (2 * (2 * R + 4)))
  have hδ0 : 0 < δ := by positivity
  obtain ⟨N₁, hN₁⟩ := Metric.cauchySeq_iff.1 ha.cauchySeq (δ / 2) (by positivity)
  obtain ⟨N₂, hN₂⟩ := Metric.cauchySeq_iff.1 hb.cauchySeq (δ / 2) (by positivity)
  obtain ⟨N₃, hN₃⟩ :=
    eventually_atTop.1 ((ha.dist hb).eventually (gt_mem_nhds (show dist x v < R by linarith)))
  refine ⟨max N₁ (max N₂ N₃), fun l hl k hk => ?_⟩
  have e1 := hN₁ l ((le_max_left _ _).trans hl) k ((le_max_left _ _).trans hk)
  have e2 := hN₂ l (((le_max_left _ _).trans (le_max_right _ _)).trans hl) k
    (((le_max_left _ _).trans (le_max_right _ _)).trans hk)
  have e3 := hN₃ k (((le_max_right _ _).trans (le_max_right _ _)).trans hk)
  set e := dist (a l) (a k) + dist (b l) (b k)
  have he0 : 0 ≤ e := by positivity
  have hed : e < δ := by linarith
  have t2 := dist_triangle4 (a l) (a k) (b k) (b l)
  rw [dist_comm (b k) (b l)] at t2
  have d1 : dist (m l) (a k) ≤ dist (a k) (b k) / 2 + 2 * e := by
    linarith [dist_triangle_left (m l) (a k) (a l), (hmid l).1, dist_nonneg (x := b l) (y := b k)]
  have d2 : dist (m l) (b k) ≤ dist (a k) (b k) / 2 + 2 * e := by
    linarith [dist_triangle_left (m l) (b k) (b l), (hmid l).2, dist_nonneg (x := a l) (y := a k)]
  have d6 : dist (m l) (m k) ^ 2 ≤ (2 * R + 4) * e := by
    nlinarith [hm k (m l), pow_le_pow_left₀ dist_nonneg d1 2, pow_le_pow_left₀ dist_nonneg d2 2,
      hed.le.trans (min_le_left _ _), mul_le_mul_of_nonneg_right e3.le he0]
  have e4 := (lt_div_iff₀ (by positivity)).1 (hed.trans_le (min_le_right _ _))
  exact lt_of_pow_lt_pow_left₀ 2 hε.le (d6.trans_lt (by nlinarith [sq_pos_of_pos hε]))

/-- The completion satisfies (CN): a complete metric space is CAT(0) if any two points x, v of a
dense subset S have a
point m for which (CN) holds at all z in S. -/
private theorem prop_space_completion {X : Type*} [MetricSpace X] [CompleteSpace X] {S : Set X}
    (hS : Dense S)
    (h : ∀ x ∈ S, ∀ v ∈ S, ∃ m, ∀ z ∈ S,
      dist z m ^ 2 ≤ (dist z x ^ 2 + dist z v ^ 2) / 2 - dist x v ^ 2 / 4) : CompleteCAT0Space X :=
          by
  have h' (x) (hx : x ∈ S) (v) (hv : v ∈ S) : ∃ m, ∀ z,
      dist z m ^ 2 ≤ (dist z x ^ 2 + dist z v ^ 2) / 2 - dist x v ^ 2 / 4 := by
    obtain ⟨m, hm⟩ := h x hx v hv
    have hc : IsClosed {z | dist z m ^ 2 ≤ (dist z x ^ 2 + dist z v ^ 2) / 2 - dist x v ^ 2 / 4} :=
      isClosed_le (by fun_prop) (by fun_prop)
    exact ⟨m, fun z => hc.closure_subset_iff.2 hm (hS z)⟩
  refine { exists_mid := fun x v => ?_ }
  obtain ⟨a, haS, ha⟩ := mem_closure_iff_seq_limit.1 (hS x)
  obtain ⟨b, hbS, hb⟩ := mem_closure_iff_seq_limit.1 (hS v)
  choose m hm using fun n => h' (a n) (haS n) (b n) (hbS n)
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete (prop_space_cauchy ha hb hm)
  refine ⟨p, fun z => ?_⟩
  exact (le_of_tendsto_of_tendsto' ((tendsto_const_nhds.dist hp).pow 2)
    (((((tendsto_const_nhds.dist ha).pow 2).add ((tendsto_const_nhds.dist hb).pow 2)).div_const
      2).sub (((ha.dist hb).pow 2).div_const 4)) fun n => hm n z).trans_eq (by ring)

/-- Its metric is a price as a limit: if the distance of a pseudometric space is a price, so is
the metric of its
completion. -/
private theorem prop_space_limit {T : Type} [PseudoMetricSpace T]
    (hd : IsPrice K fun s t : T => dist s t) :
    IsPrice K fun a b : UniformSpace.Completion T => dist a b := by
  have hseq (a : UniformSpace.Completion T) :
      ∃ u : ℕ → T, Tendsto (fun n => ((u n : T) : UniformSpace.Completion T)) atTop (𝓝 a) := by
    obtain ⟨u, hu, ha⟩ :=
      mem_closure_iff_seq_limit.1 (UniformSpace.Completion.denseRange_coe (α := T) a)
    choose u' hu' using hu
    exact ⟨u', by simpa only [hu'] using ha⟩
  choose u hu using hseq
  refine isPrice_of_tendsto (l := atTop) (d := fun n a b => dist (u a n) (u b n))
    (fun a b => by simpa only [UniformSpace.Completion.dist_eq] using (hu a).dist (hu b))
    (Eventually.of_forall fun n => hd.comp fun a => u a n)

/-- **Paper: Proposition C.3.** Every price `w` on a set `V` is the pull-back of the metric of a
price space: a complete CAT(0) space whose metric is a price. -/
theorem exists_completeCAT0Space_of_isPrice {V : Type} {w : V → V → ℝ} (hw : IsPrice K w) :
    ∃ (X : Type) (_ : MetricSpace X) (_ : CompleteCAT0Space X) (f : V → X),
      IsPrice K (fun a b : X => dist a b) ∧ ∀ a b, dist (f a) (f b) = w a b := by
  obtain ⟨d, hd, hof, hmid⟩ := prop_space_midpoints hw
  let _ : PseudoMetricSpace (FreeMagma V) :=
    { dist := d, dist_self := hd.self, dist_comm := hd.symm, dist_triangle := hd.triangle }
  have hdd : ∀ s t : FreeMagma V, dist s t = d s t := fun _ _ => rfl
  -- identify points at distance `0`; the completion satisfies (CN), and its metric is a price
  -- as a limit
  refine ⟨UniformSpace.Completion (FreeMagma V), inferInstance,
    prop_space_completion UniformSpace.Completion.denseRange_coe ?_,
    fun v => ((FreeMagma.of v : FreeMagma V) : UniformSpace.Completion (FreeMagma V)),
    prop_space_limit hd, ?_⟩
  · -- each new point is a midpoint of its pair, so (CN) holds by Theorem C.1
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    refine ⟨(((s * t) : FreeMagma V) : UniformSpace.Completion (FreeMagma V)), ?_⟩
    rintro _ ⟨z, rfl⟩
    simp only [UniformSpace.Completion.dist_eq, hdd]
    exact (isPrice_sq_le_of_mid hd s t (s * t) z (D := d s t / 2)
      (hmid s t).1 (hmid s t).2 (by ring)).trans_eq (by ring)
  · intro a b
    simpa only [UniformSpace.Completion.dist_eq, hdd] using hof a b

end Space

end Cslib.Circuits.Arithmetic.Separation.Curvature
