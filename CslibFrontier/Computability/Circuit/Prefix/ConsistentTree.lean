/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Prefix.Basic
public import Mathlib.Order.Lattice.Nat
-- `import all`: reads private gate-depth lemmas `wireDepths_gate_id` and `wireDepths_gate_mul`.
import all CslibFrontier.Computability.Circuit.Prefix.Basic
import CslibFrontier.Computability.Circuit.Basic
import CslibFrontier.Computability.Circuit.FanIn
import CslibFrontier.Computability.Circuit.Program
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Consistent tree pairs, segment-width recurrences, and optimal prefix circuit synthesis

Following Sergeev [Sergeev2025PrefixDepth], decomposing a zero-deficiency fanout-`k` prefix circuit
along its principal chain partitions its segments into consistent pairs of a binary interval
aggregation tree `I_d` of depth `≤ d` and a fanout-`k` prefix distribution tree `Q_d` of depth
`≤ h` (`ConsistentTree`, `ConsistentChain`, `ConsistentTreePair`).

We prove Sergeev's exact recurrence (`maxConsistentWidth_eq`, Claim (4)) for the maximum segment
width `w_k(d, h)` (`maxConsistentWidth k d h`) of consistent tree pairs, deduce the closed form
`w_2(d, h) = 2 ^ min d h` (`maxConsistentWidth_two`) and the order-`k` linear recurrence
`w_k*(D) = (∑_{i=2}^{k-1} w_k*(D - i)) + 2 * w_k*(D - k) + k` (`maxCircuitWidthUpper_recurrence`)
for `w_k*(D) = ∑_{d=0}^D w_k(d, D - d)` (`maxCircuitWidthUpper k D`), and constructively synthesize
an optimal (zero-deficiency) fanout-`k` universal prefix circuit of depth at most `D` for every
width `1 ≤ N ≤ 1 + w_k*(D - 1)` (`exists_optimalPrefixCircuit_of_le_maxCircuitWidthUpper`).

## Main definitions

* `Cslib.Circuits.Prefix.ConsistentTree`, `Cslib.Circuits.Prefix.ConsistentChain`,
  `Cslib.Circuits.Prefix.ConsistentTreePair`: consistent pairs of interval aggregation and prefix
  distribution trees.
* `Cslib.Circuits.Prefix.maxConsistentWidth`, `Cslib.Circuits.Prefix.maxCircuitWidthUpper`:
  maximum segment width `w_k(d, h)` and circuit width sum `w_k*(D)`.

## Main results

* `Cslib.Circuits.Prefix.maxConsistentWidth_eq`,
  `Cslib.Circuits.Prefix.maxConsistentWidth_two`: Sergeev's Claim (4) for `w_k(d, h)` and closed
  form `w_2(d, h) = 2 ^ min d h`.
* `Cslib.Circuits.Prefix.maxCircuitWidthUpper_recurrence`: linear recurrence
  `w_k*(D) = (∑_{i=2}^{k-1} w_k*(D - i)) + 2 * w_k*(D - k) + k` for `D ≥ k ≥ 2`.
* `Cslib.Circuits.Prefix.exists_optimalPrefixCircuit_of_le_maxCircuitWidthUpper`: constructive
  existence of optimal fanout-`k` universal prefix circuits of depth `≤ D` for all widths
  `1 ≤ N ≤ 1 + w_k*(D - 1)`.

## References

* [I. S. Sergeev, *A Note on the Depth of Optimal Fanout-Bounded Prefix
  Circuits*][Sergeev2025PrefixDepth]
-/

public section

namespace Cslib.Circuits.Prefix

mutual
/-- A consistent pair of interval aggregation and prefix distribution trees over `[a, b)` along
the left spine of an interval tree ([Sergeev2025PrefixDepth], Fig. 1 and Eq. (5)). -/
inductive ConsistentTree : ℕ → ℕ → Type
  | leaf (a : ℕ) : ConsistentTree a (a + 1)
  | buffer {a b : ℕ} (child : ConsistentTree a b) : ConsistentTree a b
  | split {a m b : ℕ} (chain : ConsistentChain a m b) : ConsistentTree a b

/-- A contiguous chain of `≥ 2` consistent tree pairs covering `[a, b)` along the left spine of an
interval tree ([Sergeev2025PrefixDepth], Fig. 1 and Eq. (5)). -/
inductive ConsistentChain : ℕ → ℕ → ℕ → Type
  | two {a m b : ℕ} (first : ConsistentTree a m) (second : ConsistentTree m b) :
      ConsistentChain a m b
  | snoc {a m₁ m₂ b : ℕ} (init : ConsistentChain a m₁ m₂) (last : ConsistentTree m₂ b) :
      ConsistentChain a m₁ b
end

mutual
/-- Depth of the binary interval aggregation tree `I` underlying a `ConsistentTree`. -/
@[expose] def ConsistentTree.inDepth : {a b : ℕ} → ConsistentTree a b → ℕ
  | _, _, .leaf _ => 0
  | _, _, .buffer c => c.inDepth
  | _, _, .split ch => ch.inDepth

/-- Depth of the left-associated binary interval aggregation tree formed by a `ConsistentChain`. -/
@[expose] def ConsistentChain.inDepth : {a m b : ℕ} → ConsistentChain a m b → ℕ
  | _, _, _, .two t₁ t₂ => max t₁.inDepth t₂.inDepth + 1
  | _, _, _, .snoc init t => max init.inDepth t.inDepth + 1
end

mutual
/-- Depth of the prefix distribution tree `Q` in a `ConsistentTree`. -/
@[expose] def ConsistentTree.outDepth : {a b : ℕ} → ConsistentTree a b → ℕ
  | _, _, .leaf _ => 0
  | _, _, .buffer c => c.outDepth + 1
  | _, _, .split ch => ch.maxOutDepth + 1

/-- Maximum `outDepth` among the children in a `ConsistentChain`. -/
@[expose] def ConsistentChain.maxOutDepth : {a m b : ℕ} → ConsistentChain a m b → ℕ
  | _, _, _, .two t₁ t₂ => max t₁.outDepth t₂.outDepth
  | _, _, _, .snoc init t => max init.maxOutDepth t.outDepth
end

/-- Number of immediate branches in a `ConsistentChain`. -/
@[expose] def ConsistentChain.arity : {a m b : ℕ} → ConsistentChain a m b → ℕ
  | _, _, _, .two _ _ => 2
  | _, _, _, .snoc init _ => init.arity + 1

mutual
/-- Fanout bound `≤ k` at every node of the prefix distribution tree `Q`. -/
@[expose] def ConsistentTree.FanoutAtMost (k : ℕ) : {a b : ℕ} → ConsistentTree a b → Prop
  | _, _, .leaf _ => 1 ≤ k
  | _, _, .buffer c => 1 ≤ k ∧ c.FanoutAtMost k
  | _, _, .split ch => ch.arity ≤ k ∧ ch.FanoutAtMost k

/-- Fanout bound `≤ k` across all subtrees in a `ConsistentChain`. -/
@[expose] def ConsistentChain.FanoutAtMost (k : ℕ) : {a m b : ℕ} → ConsistentChain a m b → Prop
  | _, _, _, .two t₁ t₂ => t₁.FanoutAtMost k ∧ t₂.FanoutAtMost k
  | _, _, _, .snoc init t => init.FanoutAtMost k ∧ t.FanoutAtMost k
end

mutual
/-- Every `ConsistentTree a b` spans a nonempty interval `a < b`. -/
theorem ConsistentTree.lt : {a b : ℕ} → (t : ConsistentTree a b) → a < b
  | _, _, .leaf a => Nat.lt_succ_self a
  | _, _, .buffer c => c.lt
  | _, _, .split ch => ch.lt

theorem ConsistentChain.lt : {a m b : ℕ} → (ch : ConsistentChain a m b) → a < b
  | _, _, _, .two t₁ t₂ => t₁.lt.trans t₂.lt
  | _, _, _, .snoc init t => init.lt.trans t.lt
end

/-- A pair of consistent trees `(I, Q)` of input-tree depth `≤ d`, output-tree depth `≤ h`, and
output-tree fanout `≤ k` ([Sergeev2025PrefixDepth], p. 3). -/
structure ConsistentTreePair (k d h : ℕ) where
  /-- Left endpoint of the input/output interval `[a, b)`. -/
  a : ℕ
  /-- Right endpoint of the input/output interval `[a, b)`. -/
  b : ℕ
  /-- Underlying consistent pair of interval and prefix trees. -/
  tree : ConsistentTree a b
  /-- Input binary tree `I` has depth at most `d`. -/
  inDepth_le : tree.inDepth ≤ d
  /-- Output `k`-ary tree `Q` has depth at most `h`. -/
  outDepth_le : tree.outDepth ≤ h
  /-- Output tree `Q` has fanout bounded by `k`. -/
  fanout_le : tree.FanoutAtMost k

/-- Width `w = b - a` of a `ConsistentTreePair`. -/
@[expose] def ConsistentTreePair.width {k d h : ℕ} (p : ConsistentTreePair k d h) : ℕ :=
  p.b - p.a

/-- Maximum width `w_k(d, h)` of a consistent tree pair with input depth `≤ d`, output depth `≤ h`,
and fanout `≤ k` ([Sergeev2025PrefixDepth], p. 3). -/
@[expose] noncomputable def maxConsistentWidth (k d h : ℕ) : ℕ :=
  sSup {w : ℕ | ∃ p : ConsistentTreePair k d h, p.width = w}

/-- Sum of maximum segment widths `w_k*(D) = ∑_{d=0}^D w_k(d, D - d)` ([Sergeev2025PrefixDepth],
p. 3). -/
@[expose] noncomputable def maxCircuitWidthUpper (k D : ℕ) : ℕ :=
  ∑ d ∈ Finset.range (D + 1), maxConsistentWidth k d (D - d)

/-! #### Closed-form recurrence helper `segmentWidth` and equivalence with `maxConsistentWidth` -/

private def segmentWidth (k : ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 1
  | d + 1, h + 1 =>
      let l := min (d + 1) (k - 1)
      (∑ i ∈ Finset.Ico 1 l, segmentWidth k (d + 1 - i) h) + 2 * segmentWidth k (d + 1 - l) h

private theorem segmentWidth_zero_right (k d : ℕ) : segmentWidth k d 0 = 1 := by
  cases d <;> rfl

private theorem segmentWidth_zero_left (k h : ℕ) : segmentWidth k 0 h = 1 := by
  cases h <;> rfl

private theorem segmentWidth_pos (k d h : ℕ) : 1 ≤ segmentWidth k d h := by
  induction h generalizing d with
  | zero => rw [segmentWidth_zero_right]
  | succ h ih =>
    cases d with
    | zero => rw [segmentWidth_zero_left]
    | succ d =>
      simp only [segmentWidth]
      have := ih (d + 1 - min (d + 1) (k - 1))
      omega

private theorem sum_Ico_one_succ_shift {M : Type*} [AddCommMonoid M] {l : ℕ} (hl : 1 ≤ l)
    (n : ℕ) (g : ℕ → M) :
    ∑ i ∈ Finset.Ico 1 (l + 1), g (n + 1 - i) =
      g n + ∑ j ∈ Finset.Ico 1 l, g (n - j) := by
  have hins : Finset.Ico 1 (l + 1) = insert 1 (Finset.Ico 2 (l + 1)) := by
    ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
  rw [hins, Finset.sum_insert (by simp only [Finset.mem_Ico]; omega), Nat.add_sub_cancel]
  congr 1
  refine Finset.sum_bij (fun i _ => i - 1) ?_ ?_ ?_ ?_
  · intro i hi; simp only [Finset.mem_Ico] at hi ⊢; omega
  · intro i₁ hi₁ i₂ hi₂ heq; simp only [Finset.mem_Ico] at hi₁ hi₂; omega
  · intro j hj
    simp only [Finset.mem_Ico] at hj
    exact ⟨j + 1, by simp only [Finset.mem_Ico]; omega, Nat.add_sub_cancel _ _⟩
  · intro i hi
    simp only [Finset.mem_Ico] at hi
    rw [show n + 1 - i = n - (i - 1) by omega]

private theorem segmentWidth_mono_left (k : ℕ) :
    ∀ d h : ℕ, segmentWidth k d h ≤ segmentWidth k (d + 1) h := by
  intro d h
  induction h generalizing d with
  | zero => simp only [segmentWidth_zero_right, le_rfl]
  | succ h ih =>
    cases d with
    | zero =>
      rw [segmentWidth_zero_left]
      exact segmentWidth_pos k 1 (h + 1)
    | succ d =>
      by_cases hle : d + 2 ≤ k - 1
      · have hl1 : min (d + 1) (k - 1) = d + 1 := Nat.min_eq_left (by omega)
        have hl2 : min (d + 2) (k - 1) = d + 2 := Nat.min_eq_left hle
        change (∑ i ∈ Finset.Ico 1 (min (d + 1) (k - 1)), segmentWidth k (d + 1 - i) h) +
            2 * segmentWidth k (d + 1 - min (d + 1) (k - 1)) h ≤
          (∑ i ∈ Finset.Ico 1 (min (d + 2) (k - 1)), segmentWidth k (d + 2 - i) h) +
            2 * segmentWidth k (d + 2 - min (d + 2) (k - 1)) h
        rw [hl1, hl2, Nat.sub_self, Nat.sub_self,
          sum_Ico_one_succ_shift (l := d + 1) (by omega) (d + 1) (fun x => segmentWidth k x h)]
        omega
      · have hl1 : min (d + 1) (k - 1) = k - 1 := Nat.min_eq_right (by omega)
        have hl2 : min (d + 2) (k - 1) = k - 1 := Nat.min_eq_right (by omega)
        change (∑ i ∈ Finset.Ico 1 (min (d + 1) (k - 1)), segmentWidth k (d + 1 - i) h) +
            2 * segmentWidth k (d + 1 - min (d + 1) (k - 1)) h ≤
          (∑ i ∈ Finset.Ico 1 (min (d + 2) (k - 1)), segmentWidth k (d + 2 - i) h) +
            2 * segmentWidth k (d + 2 - min (d + 2) (k - 1)) h
        rw [hl1, hl2]
        have hsum : ∑ i ∈ Finset.Ico 1 (k - 1), segmentWidth k (d + 1 - i) h ≤
            ∑ i ∈ Finset.Ico 1 (k - 1), segmentWidth k (d + 2 - i) h := by
          refine Finset.sum_le_sum fun i hi => ?_
          simp only [Finset.mem_Ico] at hi
          rw [show d + 2 - i = (d + 1 - i) + 1 by omega]
          exact ih (d + 1 - i)
        have hlast : segmentWidth k (d + 1 - (k - 1)) h ≤ segmentWidth k (d + 2 - (k - 1)) h := by
          rw [show d + 2 - (k - 1) = (d + 1 - (k - 1)) + 1 by omega]
          exact ih (d + 1 - (k - 1))
        omega

private theorem segmentWidth_mono_left_le {k d₁ d₂ h : ℕ} (hd : d₁ ≤ d₂) :
    segmentWidth k d₁ h ≤ segmentWidth k d₂ h := by
  induction d₂, hd using Nat.le_induction with
  | base => exact le_rfl
  | succ d₂ _ ih => exact ih.trans (segmentWidth_mono_left k d₂ h)

private theorem segmentWidth_mono_right (k : ℕ) :
    ∀ d h : ℕ, segmentWidth k d h ≤ segmentWidth k d (h + 1) := by
  intro d h
  induction h generalizing d with
  | zero =>
    rw [segmentWidth_zero_right]
    exact segmentWidth_pos k d 1
  | succ h ih =>
    cases d with
    | zero => simp only [segmentWidth_zero_left, le_rfl]
    | succ d =>
      simp only [segmentWidth]
      have hsum : ∑ i ∈ Finset.Ico 1 (min (d + 1) (k - 1)), segmentWidth k (d + 1 - i) h ≤
          ∑ i ∈ Finset.Ico 1 (min (d + 1) (k - 1)), segmentWidth k (d + 1 - i) (h + 1) :=
        Finset.sum_le_sum fun i _ => ih (d + 1 - i)
      have hlast := ih (d + 1 - min (d + 1) (k - 1))
      omega

private theorem segmentWidth_le_two_mul {k : ℕ} (hk : 2 ≤ k) :
    ∀ d h : ℕ, segmentWidth k (d + 1) h ≤ 2 * segmentWidth k d h := by
  intro d h
  induction h generalizing d with
  | zero =>
    simp only [segmentWidth_zero_right]
    omega
  | succ h ih =>
    cases d with
    | zero =>
      have hl : min 1 (k - 1) = 1 := Nat.min_eq_left (by omega)
      change (∑ i ∈ Finset.Ico 1 (min 1 (k - 1)), segmentWidth k (1 - i) h) +
          2 * segmentWidth k (1 - min 1 (k - 1)) h ≤ 2 * segmentWidth k 0 (h + 1)
      rw [hl, Finset.Ico_self, Finset.sum_empty, Nat.sub_self, segmentWidth_zero_left,
        segmentWidth_zero_left]
    | succ d =>
      by_cases hle : d + 2 ≤ k - 1
      · have hl1 : min (d + 1) (k - 1) = d + 1 := Nat.min_eq_left (by omega)
        have hl2 : min (d + 2) (k - 1) = d + 2 := Nat.min_eq_left hle
        have hsplit : segmentWidth k (d + 2) (h + 1) =
            segmentWidth k (d + 1) h + segmentWidth k (d + 1) (h + 1) := by
          change (∑ i ∈ Finset.Ico 1 (min (d + 2) (k - 1)), segmentWidth k (d + 2 - i) h) +
              2 * segmentWidth k (d + 2 - min (d + 2) (k - 1)) h =
            segmentWidth k (d + 1) h +
              ((∑ i ∈ Finset.Ico 1 (min (d + 1) (k - 1)), segmentWidth k (d + 1 - i) h) +
                2 * segmentWidth k (d + 1 - min (d + 1) (k - 1)) h)
          rw [hl1, hl2, Nat.sub_self, Nat.sub_self, ← Nat.add_assoc,
            sum_Ico_one_succ_shift (l := d + 1) (by omega) (d + 1) (fun x => segmentWidth k x h)]
        rw [hsplit]
        have hm := segmentWidth_mono_right k (d + 1) h
        omega
      · have hl1 : min (d + 1) (k - 1) = k - 1 := Nat.min_eq_right (by omega)
        have hl2 : min (d + 2) (k - 1) = k - 1 := Nat.min_eq_right (by omega)
        change (∑ i ∈ Finset.Ico 1 (min (d + 2) (k - 1)), segmentWidth k (d + 2 - i) h) +
            2 * segmentWidth k (d + 2 - min (d + 2) (k - 1)) h ≤
          2 * ((∑ i ∈ Finset.Ico 1 (min (d + 1) (k - 1)), segmentWidth k (d + 1 - i) h) +
            2 * segmentWidth k (d + 1 - min (d + 1) (k - 1)) h)
        rw [hl1, hl2]
        have hsum : ∑ i ∈ Finset.Ico 1 (k - 1), segmentWidth k (d + 2 - i) h ≤
            2 * ∑ i ∈ Finset.Ico 1 (k - 1), segmentWidth k (d + 1 - i) h := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun i hi => ?_
          simp only [Finset.mem_Ico] at hi
          rw [show d + 2 - i = (d + 1 - i) + 1 by omega]
          exact ih (d + 1 - i)
        have hlast : segmentWidth k (d + 2 - (k - 1)) h ≤
            2 * segmentWidth k (d + 1 - (k - 1)) h := by
          rw [show d + 2 - (k - 1) = (d + 1 - (k - 1)) + 1 by omega]
          exact ih (d + 1 - (k - 1))
        omega

private theorem segmentWidth_mono_right_le {k d h₁ h₂ : ℕ} (hh : h₁ ≤ h₂) :
    segmentWidth k d h₁ ≤ segmentWidth k d h₂ := by
  induction h₂, hh using Nat.le_induction with
  | base => exact le_rfl
  | succ h₂ _ ih => exact ih.trans (segmentWidth_mono_right k d h₂)

private def chainWidthBound (k d h r : ℕ) : ℕ :=
  if r ≤ 1 then
    segmentWidth k d h
  else
    let l := min d (r - 1)
    (∑ i ∈ Finset.Ico 1 l, segmentWidth k (d - i) h) + 2 * segmentWidth k (d - l) h

private theorem chainWidthBound_two {k d h : ℕ} (hd : 1 ≤ d) :
    chainWidthBound k d h 2 = 2 * segmentWidth k (d - 1) h := by
  have hl : min d 1 = 1 := Nat.min_eq_right hd
  simp only [chainWidthBound, show ¬(2 ≤ 1) by omega, ↓reduceIte, hl, Finset.Ico_self,
    Finset.sum_empty, Nat.zero_add]

private theorem chainWidthBound_snoc {k d h r : ℕ} (hd : 2 ≤ d) (hr : 2 ≤ r) :
    chainWidthBound k (d - 1) h r + segmentWidth k (d - 1) h =
      chainWidthBound k d h (r + 1) := by
  have hr1 : ¬(r ≤ 1) := by omega
  have hr2 : ¬(r + 1 ≤ 1) := by omega
  simp only [chainWidthBound, hr1, hr2, ↓reduceIte, Nat.add_sub_cancel]
  have hmin : min d r = min (d - 1) (r - 1) + 1 := by omega
  rw [hmin]
  set l₀ := min (d - 1) (r - 1)
  have hl₀_pos : 1 ≤ l₀ := by omega
  have hsub : d - (l₀ + 1) = d - 1 - l₀ := by omega
  rw [hsub]
  have hsplit : ∑ i ∈ Finset.Ico 1 (l₀ + 1), segmentWidth k (d - i) h =
      segmentWidth k (d - 1) h + ∑ j ∈ Finset.Ico 1 l₀, segmentWidth k (d - 1 - j) h := by
    conv_lhs => rw [show d = (d - 1) + 1 by omega]
    exact sum_Ico_one_succ_shift hl₀_pos (d - 1) (fun x => segmentWidth k x h)
  rw [hsplit]
  omega

private theorem chainWidthBound_mono_arity {k d h r : ℕ} (hk : 2 ≤ k) (hr : 2 ≤ r) :
    chainWidthBound k d h r ≤ chainWidthBound k d h (r + 1) := by
  have hr1 : ¬(r ≤ 1) := by omega
  have hr2 : ¬(r + 1 ≤ 1) := by omega
  simp only [chainWidthBound, hr1, hr2, ↓reduceIte, Nat.add_sub_cancel]
  by_cases hle : d ≤ r - 1
  · have hl1 : min d (r - 1) = d := Nat.min_eq_left hle
    have hl2 : min d r = d := Nat.min_eq_left (by omega)
    rw [hl1, hl2]
  · have hl1 : min d (r - 1) = r - 1 := Nat.min_eq_right (by omega)
    have hl2 : min d r = r := Nat.min_eq_right (by omega)
    rw [hl1, hl2]
    have hsplit : ∑ i ∈ Finset.Ico 1 r, segmentWidth k (d - i) h =
        (∑ i ∈ Finset.Ico 1 (r - 1), segmentWidth k (d - i) h) +
          segmentWidth k (d - (r - 1)) h := by
      have h1 : r = (r - 1) + 1 := by omega
      conv_lhs => rw [h1]
      exact Finset.sum_Ico_succ_top (by omega) (fun i => segmentWidth k (d - i) h)
    rw [hsplit]
    have htwo : segmentWidth k (d - (r - 1)) h ≤ 2 * segmentWidth k (d - r) h := by
      rw [show d - (r - 1) = (d - r) + 1 by omega]
      exact segmentWidth_le_two_mul hk (d - r) h
    omega

private theorem chainWidthBound_mono_arity_le {k d h r₁ r₂ : ℕ} (hk : 2 ≤ k)
    (hr₁ : 2 ≤ r₁) (hr : r₁ ≤ r₂) :
    chainWidthBound k d h r₁ ≤ chainWidthBound k d h r₂ := by
  induction r₂, hr using Nat.le_induction with
  | base => exact le_rfl
  | succ r₂ hle ih => exact ih.trans (chainWidthBound_mono_arity hk (hr₁.trans hle))

private theorem ConsistentChain.two_le_arity :
    {a m b : ℕ} → (ch : ConsistentChain a m b) → 2 ≤ ch.arity
  | _, _, _, .two _ _ => le_rfl
  | _, _, _, .snoc init _ => by
    have := init.two_le_arity
    simp only [ConsistentChain.arity]
    omega

private theorem ConsistentChain.one_le_inDepth {a m b : ℕ} (ch : ConsistentChain a m b) :
    1 ≤ ch.inDepth := by
  cases ch <;> simp only [ConsistentChain.inDepth] <;> omega

mutual
private theorem ConsistentTree.width_le_segmentWidth {k : ℕ} (hk : 2 ≤ k) :
    ∀ {a b : ℕ} (t : ConsistentTree a b) (d h : ℕ),
      t.inDepth ≤ d → t.outDepth ≤ h → t.FanoutAtMost k →
      b - a ≤ segmentWidth k d h
  | _, _, .leaf a, d, h, _, _, _ => by
    have hpos := segmentWidth_pos k d h
    omega
  | _, _, .buffer c, d, h, hd, hh, hfan => by
    cases h with
    | zero =>
      simp only [ConsistentTree.outDepth] at hh
      omega
    | succ h =>
      simp only [ConsistentTree.inDepth] at hd
      simp only [ConsistentTree.outDepth] at hh
      have hc := c.width_le_segmentWidth hk d h hd (by omega) hfan.2
      exact hc.trans (segmentWidth_mono_right k d h)
  | _, _, .split ch, d, h, hd, hh, hfan => by
    cases h with
    | zero =>
      simp only [ConsistentTree.outDepth] at hh
      omega
    | succ h =>
      have hd1 : 1 ≤ d := ch.one_le_inDepth.trans hd
      cases d with
      | zero => omega
      | succ d =>
        simp only [ConsistentTree.inDepth] at hd
        simp only [ConsistentTree.outDepth] at hh
        have hch := ch.width_le_chainWidthBound hk (d + 1) h hd (by omega) hfan.2
        have hmon := chainWidthBound_mono_arity_le (d := d + 1) (h := h) hk
          ch.two_le_arity hfan.1
        have heq : chainWidthBound k (d + 1) h k = segmentWidth k (d + 1) (h + 1) := by
          simp only [chainWidthBound, show ¬(k ≤ 1) by omega, ↓reduceIte, segmentWidth]
        omega

private theorem ConsistentChain.width_le_chainWidthBound {k : ℕ} (hk : 2 ≤ k) :
    ∀ {a m b : ℕ} (ch : ConsistentChain a m b) (d h : ℕ),
      ch.inDepth ≤ d → ch.maxOutDepth ≤ h → ch.FanoutAtMost k →
      b - a ≤ chainWidthBound k d h ch.arity
  | _, _, _, .two t₁ t₂, d, h, hd, hh, hfan => by
    have hd1 : 1 ≤ d := by simp only [ConsistentChain.inDepth] at hd; omega
    simp only [ConsistentChain.inDepth] at hd
    simp only [ConsistentChain.maxOutDepth] at hh
    have h1 := t₁.width_le_segmentWidth hk (d - 1) h (by omega) (by omega) hfan.1
    have h2 := t₂.width_le_segmentWidth hk (d - 1) h (by omega) (by omega) hfan.2
    have hlt1 := t₁.lt
    have hlt2 := t₂.lt
    simp only [ConsistentChain.arity]
    rw [chainWidthBound_two hd1]
    omega
  | _, _, _, .snoc init t, d, h, hd, hh, hfan => by
    have hinit_pos := init.one_le_inDepth
    simp only [ConsistentChain.inDepth] at hd
    simp only [ConsistentChain.maxOutDepth] at hh
    have hd2 : 2 ≤ d := by omega
    have h1 := init.width_le_chainWidthBound hk (d - 1) h (by omega) (by omega) hfan.1
    have h2 := t.width_le_segmentWidth hk (d - 1) h (by omega) (by omega) hfan.2
    have hlt1 := init.lt
    have hlt2 := t.lt
    simp only [ConsistentChain.arity]
    rw [← chainWidthBound_snoc hd2 init.two_le_arity]
    omega
end

private def ConsistentChain.castRight {a m b b' : ℕ} (hb : b = b') (ch : ConsistentChain a m b) :
    ConsistentChain a m b' :=
  hb ▸ ch

private theorem ConsistentChain.inDepth_castRight {a m b b' : ℕ} (hb : b = b')
    (ch : ConsistentChain a m b) : (ch.castRight hb).inDepth = ch.inDepth := by
  subst hb; rfl

private theorem ConsistentChain.maxOutDepth_castRight {a m b b' : ℕ} (hb : b = b')
    (ch : ConsistentChain a m b) : (ch.castRight hb).maxOutDepth = ch.maxOutDepth := by
  subst hb; rfl

private theorem ConsistentChain.arity_castRight {a m b b' : ℕ} (hb : b = b')
    (ch : ConsistentChain a m b) : (ch.castRight hb).arity = ch.arity := by
  subst hb; rfl

private theorem ConsistentChain.fanoutAtMost_castRight {k a m b b' : ℕ} (hb : b = b')
    (ch : ConsistentChain a m b) : (ch.castRight hb).FanoutAtMost k ↔ ch.FanoutAtMost k := by
  subst hb; exact Iff.rfl

private def ConsistentTree.castRight {a b b' : ℕ} (hb : b = b') (t : ConsistentTree a b) :
    ConsistentTree a b' :=
  hb ▸ t

private theorem ConsistentTree.inDepth_castRight {a b b' : ℕ} (hb : b = b')
    (t : ConsistentTree a b) : (t.castRight hb).inDepth = t.inDepth := by
  subst hb; rfl

private theorem ConsistentTree.outDepth_castRight {a b b' : ℕ} (hb : b = b')
    (t : ConsistentTree a b) : (t.castRight hb).outDepth = t.outDepth := by
  subst hb; rfl

private theorem ConsistentTree.fanoutAtMost_castRight {k a b b' : ℕ} (hb : b = b')
    (t : ConsistentTree a b) : (t.castRight hb).FanoutAtMost k ↔ t.FanoutAtMost k := by
  subst hb; exact Iff.rfl

private def buildConsistentChainAux {k h : ℕ} (hk : 2 ≤ k)
    (buildTree : ∀ (a d : ℕ),
      {t : ConsistentTree a (a + segmentWidth k d h) //
        t.inDepth ≤ d ∧ t.outDepth ≤ h ∧ t.FanoutAtMost k}) :
    ∀ (a d m : ℕ) (_hm1 : 1 ≤ m) (_hmd : m ≤ d) (_hmk : m + 1 ≤ k),
      {p : Σ mid : ℕ, ConsistentChain a mid (a + chainWidthBound k d h (m + 1)) //
        p.2.inDepth ≤ d ∧ p.2.maxOutDepth ≤ h ∧ p.2.arity = m + 1 ∧ p.2.FanoutAtMost k}
  | a, d, 0, hm1, _, _ => absurd hm1 (by omega)
  | a, d, 1, _, hmd, _ =>
    let t₁ := buildTree a (d - 1)
    let t₂ := buildTree (a + segmentWidth k (d - 1) h) (d - 1)
    have hb : a + segmentWidth k (d - 1) h + segmentWidth k (d - 1) h =
        a + chainWidthBound k d h 2 := by
      rw [chainWidthBound_two hmd]
      omega
    let ch := (ConsistentChain.two t₁.1 t₂.1).castRight hb
    ⟨⟨a + segmentWidth k (d - 1) h, ch⟩, by
      rw [ConsistentChain.inDepth_castRight, ConsistentChain.maxOutDepth_castRight,
        ConsistentChain.arity_castRight, ConsistentChain.fanoutAtMost_castRight]
      simp only [ConsistentChain.inDepth, ConsistentChain.maxOutDepth, ConsistentChain.arity,
        ConsistentChain.FanoutAtMost]
      exact ⟨by have := t₁.2.1; have := t₂.2.1; omega,
        Nat.max_le.mpr ⟨t₁.2.2.1, t₂.2.2.1⟩, trivial, t₁.2.2.2, t₂.2.2.2⟩⟩
  | a, d, m + 2, _, hmd, hmk =>
    let init := buildConsistentChainAux hk buildTree a (d - 1) (m + 1) (by omega) (by omega)
      (by omega)
    let last := buildTree (a + chainWidthBound k (d - 1) h (m + 2)) (d - 1)
    have hb : a + chainWidthBound k (d - 1) h (m + 2) + segmentWidth k (d - 1) h =
        a + chainWidthBound k d h (m + 3) := by
      rw [Nat.add_assoc, chainWidthBound_snoc (by omega) (by omega)]
    let ch := (ConsistentChain.snoc init.1.2 last.1).castRight hb
    ⟨⟨init.1.1, ch⟩, by
      rw [ConsistentChain.inDepth_castRight, ConsistentChain.maxOutDepth_castRight,
        ConsistentChain.arity_castRight, ConsistentChain.fanoutAtMost_castRight]
      simp only [ConsistentChain.inDepth, ConsistentChain.maxOutDepth, ConsistentChain.arity,
        ConsistentChain.FanoutAtMost]
      exact ⟨by have := init.2.1; have := last.2.1; omega,
        Nat.max_le.mpr ⟨init.2.2.1, last.2.2.1⟩, by have := init.2.2.2.1; omega,
        init.2.2.2.2, last.2.2.2⟩⟩

private def buildConsistentTree {k : ℕ} (hk : 2 ≤ k) :
    ∀ (a d h : ℕ),
      {t : ConsistentTree a (a + segmentWidth k d h) //
        t.inDepth ≤ d ∧ t.outDepth ≤ h ∧ t.FanoutAtMost k}
  | a, d, 0 =>
    let t := (ConsistentTree.leaf a).castRight (by rw [segmentWidth_zero_right])
    ⟨t, by
      rw [ConsistentTree.inDepth_castRight, ConsistentTree.outDepth_castRight,
        ConsistentTree.fanoutAtMost_castRight]
      exact ⟨Nat.zero_le _, le_rfl, by simp only [ConsistentTree.FanoutAtMost]; omega⟩⟩
  | a, 0, h + 1 =>
    let t := (ConsistentTree.leaf a).castRight (by rw [segmentWidth_zero_left])
    ⟨t, by
      rw [ConsistentTree.inDepth_castRight, ConsistentTree.outDepth_castRight,
        ConsistentTree.fanoutAtMost_castRight]
      exact ⟨le_rfl, Nat.zero_le _, by simp only [ConsistentTree.FanoutAtMost]; omega⟩⟩
  | a, d + 1, h + 1 =>
    let l := min (d + 1) (k - 1)
    let ch := buildConsistentChainAux (h := h) hk (fun a' d' => buildConsistentTree hk a' d' h)
      a (d + 1) l (by omega) (Nat.min_le_left _ _) (by omega)
    have hb : a + chainWidthBound k (d + 1) h (l + 1) =
        a + segmentWidth k (d + 1) (h + 1) := by
      congr 1
      have hmin : min (d + 1) l = l := Nat.min_eq_right (Nat.min_le_left _ _)
      simp only [chainWidthBound, show ¬(l + 1 ≤ 1) by omega, ↓reduceIte, Nat.add_sub_cancel, hmin,
        segmentWidth]
      rfl
    let t := (ConsistentTree.split ch.1.2).castRight hb
    ⟨t, by
      rw [ConsistentTree.inDepth_castRight, ConsistentTree.outDepth_castRight,
        ConsistentTree.fanoutAtMost_castRight]
      simp only [ConsistentTree.inDepth, ConsistentTree.outDepth, ConsistentTree.FanoutAtMost]
      exact ⟨ch.2.1, Nat.succ_le_succ ch.2.2.1, ⟨by have := ch.2.2.2.1; omega, ch.2.2.2.2⟩⟩⟩

private theorem maxConsistentWidth_eq_segmentWidth {k : ℕ} (hk : 2 ≤ k) (d h : ℕ) :
    maxConsistentWidth k d h = segmentWidth k d h := by
  unfold maxConsistentWidth
  let built := buildConsistentTree hk 0 d h
  let p₀ : ConsistentTreePair k d h :=
    ⟨0, segmentWidth k d h, built.1.castRight (Nat.zero_add _),
      by rw [ConsistentTree.inDepth_castRight]; exact built.2.1,
      by rw [ConsistentTree.outDepth_castRight]; exact built.2.2.1,
      by rw [ConsistentTree.fanoutAtMost_castRight]; exact built.2.2.2⟩
  apply le_antisymm
  · apply csSup_le
    · exact ⟨segmentWidth k d h, ⟨p₀, Nat.sub_zero _⟩⟩
    · rintro w ⟨p, rfl⟩
      exact p.tree.width_le_segmentWidth hk d h p.inDepth_le p.outDepth_le p.fanout_le
  · apply le_csSup
    · refine ⟨segmentWidth k d h, ?_⟩
      rintro w ⟨p, rfl⟩
      exact p.tree.width_le_segmentWidth hk d h p.inDepth_le p.outDepth_le p.fanout_le
    · exact ⟨p₀, Nat.sub_zero _⟩

/-- Boundary value `w_k(d, 0) = 1` ([Sergeev2025PrefixDepth], p. 4). -/
theorem maxConsistentWidth_zero_right {k : ℕ} (hk : 2 ≤ k) (d : ℕ) :
    maxConsistentWidth k d 0 = 1 := by
  rw [maxConsistentWidth_eq_segmentWidth hk, segmentWidth_zero_right]

/-- Boundary value `w_k(0, h) = 1` ([Sergeev2025PrefixDepth], p. 4). -/
theorem maxConsistentWidth_zero_left {k : ℕ} (hk : 2 ≤ k) (h : ℕ) :
    maxConsistentWidth k 0 h = 1 := by
  rw [maxConsistentWidth_eq_segmentWidth hk, segmentWidth_zero_left]

/-- Monotonicity `w_k(d, h) ≤ w_k(d + 1, h)` ([Sergeev2025PrefixDepth], Eq. (6)). -/
theorem maxConsistentWidth_mono_left {k : ℕ} (hk : 2 ≤ k) (d h : ℕ) :
    maxConsistentWidth k d h ≤ maxConsistentWidth k (d + 1) h := by
  rw [maxConsistentWidth_eq_segmentWidth hk, maxConsistentWidth_eq_segmentWidth hk]
  exact segmentWidth_mono_left k d h

/-- Halving bound `w_k(d, h) ≤ 2 * w_k(d - 1, h)` for `d ≥ 1` ([Sergeev2025PrefixDepth],
Eq. (7)). -/
theorem maxConsistentWidth_le_two_mul {k d : ℕ} (hk : 2 ≤ k) (hd : 1 ≤ d) (h : ℕ) :
    maxConsistentWidth k d h ≤ 2 * maxConsistentWidth k (d - 1) h := by
  rw [maxConsistentWidth_eq_segmentWidth hk, maxConsistentWidth_eq_segmentWidth hk]
  cases d with
  | zero => omega
  | succ d => exact segmentWidth_le_two_mul hk d h

/-- Sergeev's Claim (4) ([Sergeev2025PrefixDepth], p. 3, Eq. (4)): for `d, h > 0` and
`l = min d (k - 1)`,
`w_k(d, h) = (∑_{i=1}^{l-1} w_k(d - i, h - 1)) + 2 * w_k(d - l, h - 1)`. -/
theorem maxConsistentWidth_eq {k d h : ℕ} (hk : 2 ≤ k) (hd : 0 < d) (hh : 0 < h) :
    maxConsistentWidth k d h =
      (∑ i ∈ Finset.Ico 1 (min d (k - 1)), maxConsistentWidth k (d - i) (h - 1)) +
        2 * maxConsistentWidth k (d - min d (k - 1)) (h - 1) := by
  cases d with
  | zero => omega
  | succ d =>
    cases h with
    | zero => omega
    | succ h =>
      simp only [maxConsistentWidth_eq_segmentWidth hk, Nat.add_sub_cancel]
      rfl

/-- Exact closed form `w_2(d, h) = 2 ^ min d h` at fanout `k = 2`. -/
theorem maxConsistentWidth_two (d h : ℕ) :
    maxConsistentWidth 2 d h = 2 ^ min d h := by
  rw [maxConsistentWidth_eq_segmentWidth (by omega)]
  induction h generalizing d with
  | zero => simp only [segmentWidth_zero_right, Nat.min_zero, pow_zero]
  | succ h ih =>
    cases d with
    | zero => simp only [segmentWidth_zero_left, Nat.zero_min, pow_zero]
    | succ d =>
      have hl : min (d + 1) (2 - 1) = 1 := Nat.min_eq_right (by omega)
      change (∑ i ∈ Finset.Ico 1 (min (d + 1) (2 - 1)), segmentWidth 2 (d + 1 - i) h) +
          2 * segmentWidth 2 (d + 1 - min (d + 1) (2 - 1)) h = 2 ^ min (d + 1) (h + 1)
      rw [hl, Finset.Ico_self, Finset.sum_empty, Nat.zero_add, Nat.add_sub_cancel, ih d,
        Nat.succ_min_succ, Nat.pow_succ, Nat.mul_comm]

private theorem sum_Ico_sub_eq_sum_range {R : Type*} [AddCommMonoid R] (f : ℕ → ℕ → R)
    {a D : ℕ} (ha : a < D) :
    ∑ d ∈ Finset.Ico a D, f (d - a) (D - d - 1) =
      ∑ m ∈ Finset.range (D - (a + 1) + 1), f m (D - (a + 1) - m) := by
  rw [Finset.sum_Ico_eq_sum_range, show D - (a + 1) + 1 = D - a by omega]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Nat.add_sub_cancel_left, show D - (a + m) - 1 = D - (a + 1) - m by omega]

private theorem diagSum_recurrence {R : Type*} [CommSemiring R] {k D : ℕ}
    (hk : 2 ≤ k) (hD : k ≤ D) (f : ℕ → ℕ → R)
    (hf0 : ∀ h, f 0 h = 1)
    (hfrec : ∀ d h, f (d + 1) (h + 1) =
      (∑ j ∈ Finset.Ico 1 (min (d + 1) (k - 1)), f (d + 1 - j) h) +
        2 * f (d + 1 - min (d + 1) (k - 1)) h) :
    (∑ d ∈ Finset.range (D + 1), f d (D - d)) =
      (∑ i ∈ Finset.Ico 2 k, ∑ m ∈ Finset.range (D - i + 1), f m (D - i - m)) +
        2 * (∑ m ∈ Finset.range (D - k + 1), f m (D - k - m)) +
        f D 0 + ((k - 1 : ℕ) : R) := by
  have hrange : ∑ d ∈ Finset.range (D + 1), f d (D - d) =
      f D 0 + 1 + ∑ d ∈ Finset.Ico 1 D, f d (D - d) := by
    rw [Finset.sum_range_succ, Nat.sub_self]
    have h0 : ∑ d ∈ Finset.range D, f d (D - d) =
        f 0 D + ∑ d ∈ Finset.Ico 1 D, f d (D - d) := by
      rw [Finset.range_eq_Ico]
      have := Finset.sum_eq_sum_Ico_succ_bot (a := 0) (b := D) (by omega)
        (fun d => f d (D - d))
      simpa only [Nat.sub_zero] using this
    rw [h0, hf0]
    ring
  rw [hrange]
  have hstep : ∀ d, 1 ≤ d → d < D → f d (D - d) =
      (∑ j ∈ Finset.Ico 1 (min d (k - 1)), f (d - j) (D - d - 1)) +
        2 * f (d - min d (k - 1)) (D - d - 1) := by
    intro d hd1 hdD
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    obtain ⟨h', hh'⟩ : ∃ h', D - (d' + 1) = h' + 1 := ⟨D - (d' + 1) - 1, by omega⟩
    rw [hh', Nat.add_sub_cancel, hfrec]
  rw [← Finset.sum_Ico_consecutive (f := fun d => f d (D - d))
    (m := 1) (n := k - 1) (k := D) (by omega) (by omega)]
  have hlow : ∑ d ∈ Finset.Ico 1 (k - 1), f d (D - d) =
      ((k - 2 : ℕ) : R) + ∑ d ∈ Finset.Ico 1 (k - 1),
        ∑ j ∈ Finset.Ico 1 (d + 1), f (d - j) (D - d - 1) := by
    have hterm : ∀ d ∈ Finset.Ico 1 (k - 1),
        f d (D - d) =
          1 + ∑ j ∈ Finset.Ico 1 (d + 1), f (d - j) (D - d - 1) := by
      intro d hd
      simp only [Finset.mem_Ico] at hd
      rw [hstep d (by omega) (by omega), Nat.min_eq_left (by omega : d ≤ k - 1), Nat.sub_self,
        hf0, Finset.sum_Ico_succ_top (by omega : 1 ≤ d), Nat.sub_self, hf0]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico,
      nsmul_one, show k - 1 - 1 = k - 2 by omega]
  have hhigh : ∑ d ∈ Finset.Ico (k - 1) D, f d (D - d) =
      (∑ d ∈ Finset.Ico (k - 1) D,
        ∑ j ∈ Finset.Ico 1 (k - 1), f (d - j) (D - d - 1)) +
      2 * ∑ m ∈ Finset.range (D - k + 1), f m (D - k - m) := by
    have hterm : ∀ d ∈ Finset.Ico (k - 1) D,
        f d (D - d) =
          (∑ j ∈ Finset.Ico 1 (k - 1), f (d - j) (D - d - 1)) +
            2 * f (d - (k - 1)) (D - d - 1) := by
      intro d hd
      simp only [Finset.mem_Ico] at hd
      rw [hstep d (by omega) (by omega), Nat.min_eq_right (by omega : k - 1 ≤ d)]
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
    congr 2
    rw [sum_Ico_sub_eq_sum_range f (by omega), show k - 1 + 1 = k by omega]
  rw [hlow, hhigh]
  have hfub :
      (∑ d ∈ Finset.Ico 1 (k - 1),
        ∑ j ∈ Finset.Ico 1 (d + 1), f (d - j) (D - d - 1)) +
      (∑ d ∈ Finset.Ico (k - 1) D,
        ∑ j ∈ Finset.Ico 1 (k - 1), f (d - j) (D - d - 1)) =
      ∑ i ∈ Finset.Ico 2 k,
        ∑ m ∈ Finset.range (D - i + 1), f m (D - i - m) := by
    have hswap1 :
        ∑ d ∈ Finset.Ico 1 (k - 1),
          ∑ j ∈ Finset.Ico 1 (d + 1), f (d - j) (D - d - 1) =
        ∑ j ∈ Finset.Ico 1 (k - 1),
          ∑ d ∈ Finset.Ico j (k - 1), f (d - j) (D - d - 1) := by
      exact Finset.sum_comm' fun d j => by
        simp only [Finset.mem_Ico]; constructor <;> intro h <;> omega
    rw [hswap1, Finset.sum_comm (s := Finset.Ico (k - 1) D) (t := Finset.Ico 1 (k - 1)),
      ← Finset.sum_add_distrib]
    have hmerge : ∀ j ∈ Finset.Ico 1 (k - 1),
        (∑ d ∈ Finset.Ico j (k - 1), f (d - j) (D - d - 1)) +
          (∑ d ∈ Finset.Ico (k - 1) D, f (d - j) (D - d - 1)) =
        ∑ m ∈ Finset.range (D - (j + 1) + 1), f m (D - (j + 1) - m) := by
      intro j hj
      simp only [Finset.mem_Ico] at hj
      rw [Finset.sum_Ico_consecutive (f := fun d => f (d - j) (D - d - 1))
        (m := j) (n := k - 1) (k := D) (by omega) (by omega)]
      exact sum_Ico_sub_eq_sum_range f (by omega)
    rw [Finset.sum_congr rfl hmerge]
    refine Finset.sum_bij (fun j _ => j + 1) ?_ ?_ ?_ ?_
    · intro j hj; simp only [Finset.mem_Ico] at hj ⊢; omega
    · intro j₁ _ j₂ _ heq; omega
    · intro i hi
      simp only [Finset.mem_Ico] at hi
      exact ⟨i - 1, by simp only [Finset.mem_Ico]; omega, by omega⟩
    · intro _ _; rfl
  have hk_cast : ((k - 1 : ℕ) : R) = ((k - 2 : ℕ) : R) + 1 := by
    rw [show k - 1 = (k - 2) + 1 by omega, Nat.cast_add, Nat.cast_one]
  rw [hk_cast, ← hfub]
  ring

/-- Sergeev's order-`k` linear recurrence ([Sergeev2025PrefixDepth], p. 4): for `k ≥ 2` and
`D ≥ k`, `w_k*(D) = (∑_{i=2}^{k-1} w_k*(D - i)) + 2 * w_k*(D - k) + k`. -/
theorem maxCircuitWidthUpper_recurrence {k D : ℕ} (hk : 2 ≤ k) (hD : k ≤ D) :
    maxCircuitWidthUpper k D =
      (∑ i ∈ Finset.Ico 2 k, maxCircuitWidthUpper k (D - i)) +
        2 * maxCircuitWidthUpper k (D - k) + k := by
  have hW : ∀ m, maxCircuitWidthUpper k m =
      ∑ d ∈ Finset.range (m + 1), segmentWidth k d (m - d) := by
    intro m
    unfold maxCircuitWidthUpper
    exact Finset.sum_congr rfl fun d _ => maxConsistentWidth_eq_segmentWidth hk d (m - d)
  rw [hW D, hW (D - k), Finset.sum_congr rfl (fun i _ => hW (D - i)),
    diagSum_recurrence hk hD (segmentWidth k) (segmentWidth_zero_left k) (fun _ _ => rfl),
    segmentWidth_zero_right]
  simp only [Nat.cast_id]
  omega

/-! #### Constructive compilation of optimal fanout-bounded prefix circuits -/

private theorem exists_consistentChain_of_le_chainWidthBound {k h : ℕ} (hk : 2 ≤ k)
    (ihTree : ∀ (a d w : ℕ), 1 ≤ w → w ≤ segmentWidth k d h →
      ∃ t : ConsistentTree a (a + w), t.inDepth ≤ d ∧ t.outDepth ≤ h ∧ t.FanoutAtMost k) :
    ∀ (m a d w : ℕ), 1 ≤ m → m ≤ d → m + 1 ≤ k → 2 ≤ w → w ≤ chainWidthBound k d h (m + 1) →
      ∃ (mid : ℕ) (ch : ConsistentChain a mid (a + w)),
        ch.inDepth ≤ d ∧ ch.maxOutDepth ≤ h ∧ ch.arity ≤ m + 1 ∧ ch.FanoutAtMost k := by
  intro m
  induction m with
  | zero => intro _ _ _ hm1; omega
  | succ m ih =>
    cases m with
    | zero =>
      intro a d w _ hmd _ hw2 hwB
      rw [chainWidthBound_two hmd] at hwB
      have hpos := segmentWidth_pos k (d - 1) h
      let w₁ := min (w - 1) (segmentWidth k (d - 1) h)
      let w₂ := w - w₁
      obtain ⟨t₁, hd₁, hh₁, hf₁⟩ := ihTree a (d - 1) w₁ (by omega) (Nat.min_le_right _ _)
      obtain ⟨t₂, hd₂, hh₂, hf₂⟩ := ihTree (a + w₁) (d - 1) w₂ (by omega) (by omega)
      have hb : a + w₁ + w₂ = a + w := by omega
      refine ⟨a + w₁, (ConsistentChain.two t₁ t₂).castRight hb, ?_, ?_, ?_, ?_⟩
      · rw [ConsistentChain.inDepth_castRight]
        simp only [ConsistentChain.inDepth]
        omega
      · rw [ConsistentChain.maxOutDepth_castRight]
        simp only [ConsistentChain.maxOutDepth, Nat.max_le]
        exact ⟨hh₁, hh₂⟩
      · rw [ConsistentChain.arity_castRight]
        exact le_rfl
      · rw [ConsistentChain.fanoutAtMost_castRight]
        exact ⟨hf₁, hf₂⟩
    | succ m =>
      intro a d w _ hmd hmk hw2 hwB
      by_cases hw_eq : w = 2
      · subst hw_eq
        let ch := (ConsistentChain.two (ConsistentTree.leaf a)
          (ConsistentTree.leaf (a + 1))).castRight (show a + 1 + 1 = a + 2 by omega)
        refine ⟨a + 1, ch, ?_, ?_, ?_, ?_⟩
        · rw [ConsistentChain.inDepth_castRight]
          simp only [ConsistentChain.inDepth, ConsistentTree.inDepth]
          omega
        · rw [ConsistentChain.maxOutDepth_castRight]
          simp only [ConsistentChain.maxOutDepth, ConsistentTree.outDepth, Nat.max_self,
            Nat.zero_le]
        · rw [ConsistentChain.arity_castRight]
          simp only [ConsistentChain.arity]
          omega
        · rw [ConsistentChain.fanoutAtMost_castRight]
          simp only [ConsistentChain.FanoutAtMost, ConsistentTree.FanoutAtMost]
          omega
      · have hw3 : 3 ≤ w := by omega
        rw [← chainWidthBound_snoc (by omega) (by omega)] at hwB
        have hpos_d1 := segmentWidth_pos k (d - 1) h
        have hB2 : 2 ≤ chainWidthBound k (d - 1) h (m + 2) := by
          have hpos := segmentWidth_pos k (d - 1 - 1) h
          have h2 := chainWidthBound_two (k := k) (d := d - 1) (h := h) (by omega)
          have hmon := chainWidthBound_mono_arity_le (d := d - 1) (h := h) (r₁ := 2)
            (r₂ := m + 2) hk le_rfl (by omega)
          omega
        let w_init := min (w - 1) (chainWidthBound k (d - 1) h (m + 2))
        let w_last := w - w_init
        obtain ⟨mid, init, hd_i, hh_i, har_i, hf_i⟩ :=
          ih a (d - 1) w_init (by omega) (by omega) (by omega) (by omega) (Nat.min_le_right _ _)
        obtain ⟨last, hd_l, hh_l, hf_l⟩ :=
          ihTree (a + w_init) (d - 1) w_last (by omega) (by omega)
        have hb : a + w_init + w_last = a + w := by omega
        refine ⟨mid, (ConsistentChain.snoc init last).castRight hb, ?_, ?_, ?_, ?_⟩
        · rw [ConsistentChain.inDepth_castRight]
          simp only [ConsistentChain.inDepth]
          omega
        · rw [ConsistentChain.maxOutDepth_castRight]
          simp only [ConsistentChain.maxOutDepth, Nat.max_le]
          exact ⟨hh_i, hh_l⟩
        · rw [ConsistentChain.arity_castRight]
          simp only [ConsistentChain.arity]
          omega
        · rw [ConsistentChain.fanoutAtMost_castRight]
          exact ⟨hf_i, hf_l⟩

private theorem exists_consistentTree_of_le_segmentWidth {k : ℕ} (hk : 2 ≤ k) :
    ∀ (h a d w : ℕ), 1 ≤ w → w ≤ segmentWidth k d h →
      ∃ t : ConsistentTree a (a + w), t.inDepth ≤ d ∧ t.outDepth ≤ h ∧ t.FanoutAtMost k := by
  intro h
  induction h with
  | zero =>
    intro a d w hw1 hwB
    rw [segmentWidth_zero_right] at hwB
    have hw : w = 1 := by omega
    subst hw
    exact ⟨.leaf a, Nat.zero_le _, le_rfl, by simp only [ConsistentTree.FanoutAtMost]; omega⟩
  | succ h ih =>
    intro a d w hw1 hwB
    by_cases hw_one : w = 1
    · subst hw_one
      exact ⟨.leaf a, Nat.zero_le _, Nat.zero_le _,
        by simp only [ConsistentTree.FanoutAtMost]; omega⟩
    · cases d with
      | zero =>
        rw [segmentWidth_zero_left] at hwB
        omega
      | succ d =>
        let l := min (d + 1) (k - 1)
        have hB : w ≤ chainWidthBound k (d + 1) h (l + 1) := by
          have hmin : min (d + 1) l = l := Nat.min_eq_right (Nat.min_le_left _ _)
          simpa only [chainWidthBound, show ¬(l + 1 ≤ 1) by omega, ↓reduceIte,
            Nat.add_sub_cancel, hmin, segmentWidth] using hwB
        obtain ⟨mid, ch, hd_c, hh_c, har_c, hf_c⟩ :=
          exists_consistentChain_of_le_chainWidthBound hk ih l a (d + 1) w
            (by omega) (Nat.min_le_left _ _) (by omega) (by omega) hB
        refine ⟨.split ch, hd_c, Nat.succ_le_succ hh_c, ⟨by omega, hf_c⟩⟩

private theorem exists_segmentWidths_of_le_sum :
    ∀ (D : ℕ) (f : ℕ → ℕ) (M : ℕ),
      1 ≤ D → (∀ d < D, 1 ≤ f d) → D ≤ M → M ≤ ∑ d ∈ Finset.range D, f d →
      ∃ w : ℕ → ℕ, (∀ d < D, 1 ≤ w d ∧ w d ≤ f d) ∧ ∑ d ∈ Finset.range D, w d = M := by
  intro D
  induction D with
  | zero => intro _ _ hD; omega
  | succ D ih =>
    cases D with
    | zero =>
      intro f M _ _ hM1 hMf
      rw [Finset.sum_range_one] at hMf
      refine ⟨fun _ => M, ?_, Finset.sum_range_one _⟩
      intro d hd
      have hd0 : d = 0 := by omega
      subst hd0
      exact ⟨hM1, hMf⟩
    | succ D =>
      intro f M _ hf hMD hMf
      rw [Finset.sum_range_succ] at hMf
      let S' := ∑ d ∈ Finset.range (D + 1), f d
      have hS'_lb : D + 1 ≤ S' := by
        calc
          D + 1 = ∑ _d ∈ Finset.range (D + 1), 1 := by
            rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_one]
          _ ≤ S' := Finset.sum_le_sum fun d hd =>
            hf d (Nat.lt_succ_of_lt (Finset.mem_range.mp hd))
      have hf_last : 1 ≤ f (D + 1) := hf (D + 1) (Nat.lt_succ_self _)
      let w_last := max 1 (M - S')
      let M' := M - w_last
      obtain ⟨w', hw'_bd, hw'_sum⟩ := ih f M' (by omega)
        (fun d hd => hf d (Nat.lt_succ_of_lt hd)) (by omega) (by omega)
      refine ⟨fun d => if d = D + 1 then w_last else w' d, ?_, ?_⟩
      · intro d hd
        by_cases hdeq : d = D + 1
        · subst hdeq
          simp only [↓reduceIte]
          exact ⟨by omega, by omega⟩
        · simp only [hdeq, ↓reduceIte]
          exact hw'_bd d (by omega)
      · rw [Finset.sum_range_succ]
        simp only [↓reduceIte]
        have hcongr : ∑ d ∈ Finset.range (D + 1), (if d = D + 1 then w_last else w' d) =
            ∑ d ∈ Finset.range (D + 1), w' d := by
          refine Finset.sum_congr rfl fun d hd => ?_
          rw [Finset.mem_range] at hd
          have hne : d ≠ D + 1 := by omega
          simp only [hne, ↓reduceIte]
        rw [hcongr, hw'_sum]
        omega

private theorem wire_cases_castSucc_or_last {N g : ℕ} (w : Wire N (g + 1)) :
    w = .gate (Fin.last g) ∨ ∃ u : Wire N g, w = u.castSucc := by
  cases w with
  | input i => exact Or.inr ⟨.input i, rfl⟩
  | gate k =>
    refine Fin.lastCases (Or.inl rfl) (fun j => Or.inr ⟨.gate j, rfl⟩) k

private theorem castSucc_ne_lastGate {N g : ℕ} (u : Wire N g) :
    u.castSucc ≠ .gate (Fin.last g) := by
  cases u <;> simp only [Wire.castSucc, ne_eq, Wire.gate.injEq, Fin.castSucc_ne_last,
    not_false_eq_true, reduceCtorEq]

private def progOutDeg {N g : ℕ} (p : Program prefixSignature N g) (w : Wire N g) : ℕ :=
  ∑ k : Fin g,
    (Finset.univ.filter fun a : Fin (prefixSignature.Arity (p.lines k).op) =>
      (p.lines k).wires a = w).card

private theorem progOutDeg_empty {N : ℕ} (w : Wire N 0) :
    progOutDeg (.empty : Program prefixSignature N 0) w = 0 := rfl

private theorem progOutDeg_gate_last {N g : ℕ} (p : Program prefixSignature N g)
    (line : Line prefixSignature N g) :
    progOutDeg (p.gate line) (.gate (Fin.last g)) = 0 := by
  unfold progOutDeg
  rw [Fin.sum_univ_castSucc]
  have h1 : ∀ j : Fin g,
      (Finset.univ.filter fun a : Fin (prefixSignature.Arity ((p.gate line).lines j.castSucc).op) =>
        ((p.gate line).lines j.castSucc).wires a = .gate (Fin.last g)).card = 0 := by
    intro j
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    have hline_eq := Program.lines_gate_castSucc p line j
    revert hline_eq
    generalize ((p.gate line).lines j.castSucc) = l'
    rintro rfl a _
    exact castSucc_ne_lastGate ((p.lines j).wires a)
  have h2 :
      (Finset.univ.filter
        fun a : Fin (prefixSignature.Arity ((p.gate line).lines (Fin.last g)).op) =>
          ((p.gate line).lines (Fin.last g)).wires a = .gate (Fin.last g)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    have hlast_eq := Program.lines_gate_last p line
    revert hlast_eq
    generalize ((p.gate line).lines (Fin.last g)) = l'
    rintro rfl a _
    exact castSucc_ne_lastGate (line.wires a)
  simp only [h1, h2, Finset.sum_const_zero]

private theorem progOutDeg_gate_castSucc {N g : ℕ} (p : Program prefixSignature N g)
    (line : Line prefixSignature N g) (u : Wire N g) :
    progOutDeg (p.gate line) u.castSucc =
      progOutDeg p u + (Finset.univ.filter fun a : Fin (prefixSignature.Arity line.op) =>
        line.wires a = u).card := by
  unfold progOutDeg
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Fintype.sum_congr _ _ fun j => ?_
    have hline_eq := Program.lines_gate_castSucc p line j
    revert hline_eq
    generalize ((p.gate line).lines j.castSucc) = l'
    rintro rfl
    simp only [Line.mapWires_op, Line.mapWires_wires, Wire.Renaming.castSucc_apply,
      Wire.castSucc_injective.eq_iff]
    rfl
  · have hlast_eq := Program.lines_gate_last p line
    revert hlast_eq
    generalize ((p.gate line).lines (Fin.last g)) = l'
    rintro rfl
    simp only [Line.mapWires_op, Line.mapWires_wires, Wire.Renaming.castSucc_apply,
      Wire.castSucc_injective.eq_iff]
    rfl

private theorem progOutDeg_eq_circuit_outDeg {N m : ℕ} (c : Circuit prefixSignature N m)
    (w : Wire N c.size) :
    c.outDeg w = progOutDeg c.program w := by
  rw [c.outDeg_eq_card_filter]
  unfold progOutDeg
  have hsig : (Finset.univ.filter fun s : c.Slot => c.slotWire s = w) =
      Finset.univ.sigma fun k : Fin c.size =>
        Finset.univ.filter fun a : Fin (prefixSignature.Arity (c.program.lines k).op) =>
          (c.program.lines k).wires a = w := by
    ext ⟨k, a⟩
    rw [Finset.mem_filter, Finset.mem_sigma, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, Circuit.slotWire]
  rw [hsig, Finset.card_sigma]

private structure PrefixBuilder (N g : ℕ) where
  program : Program prefixSignature N g
  outs : ℕ → Option (Wire N g)
  lo : Wire N g → ℕ
  hi : Wire N g → ℕ
  validInputs : ∀ i : Fin N, lo (.input i) = i.val ∧ hi (.input i) = i.val + 1
  validGates : ∀ k : Fin g,
    match program.lines k with
    | ⟨.id, wires⟩ => lo (.gate k) = lo (wires 0) ∧ hi (.gate k) = hi (wires 0)
    | ⟨.mul, wires⟩ =>
        lo (wires 0) < hi (wires 0) ∧ hi (wires 0) = lo (wires 1) ∧
        lo (wires 1) < hi (wires 1) ∧
        lo (.gate k) = lo (wires 0) ∧ hi (.gate k) = hi (wires 1)

private def PrefixBuilder.mulCost {N g : ℕ} (B : PrefixBuilder N g) : ℕ :=
  B.program.cost fun | .mul => 1 | .id => 0

private theorem PrefixBuilder.input_ne_of_lo_ne {N g : ℕ} (B : PrefixBuilder N g) {i : Fin N}
    {v : Wire N g} (h : B.lo v ≠ i.val) : (Wire.input i : Wire N g) ≠ v := by
  rintro rfl; exact h (B.validInputs i).1

private def PrefixBuilder.uses {N g : ℕ} (B : PrefixBuilder N g) (w : Wire N g) : ℕ :=
  progOutDeg B.program w + ((Finset.range N).filter fun j => B.outs j = some w).card

private structure BuilderExt {N g g' : ℕ} (B : PrefixBuilder N g) (B' : PrefixBuilder N g') where
  emb : Wire N g → Wire N g'
  emb_injective : Function.Injective emb
  emb_input : ∀ i : Fin N, emb (.input i) = .input i
  lo_emb : ∀ u, B'.lo (emb u) = B.lo u
  hi_emb : ∀ u, B'.hi (emb u) = B.hi u
  depth_emb : ∀ u, B'.program.wireDepths (emb u) = B.program.wireDepths u
  outs_old : ∀ j w, B.outs j = some w → B'.outs j = some (emb w)

private def BuilderExt.trans {N g₀ g₁ g₂ : ℕ} {B₀ : PrefixBuilder N g₀}
    {B₁ : PrefixBuilder N g₁} {B₂ : PrefixBuilder N g₂}
    (e₁ : BuilderExt B₀ B₁) (e₂ : BuilderExt B₁ B₂) : BuilderExt B₀ B₂ where
  emb := e₂.emb ∘ e₁.emb
  emb_injective := e₂.emb_injective.comp e₁.emb_injective
  emb_input i := by simp only [Function.comp_apply, e₁.emb_input, e₂.emb_input]
  lo_emb u := by simp only [Function.comp_apply, e₂.lo_emb, e₁.lo_emb]
  hi_emb u := by simp only [Function.comp_apply, e₂.hi_emb, e₁.hi_emb]
  depth_emb u := by simp only [Function.comp_apply, e₂.depth_emb, e₁.depth_emb]
  outs_old j w h := e₂.outs_old j (e₁.emb w) (e₁.outs_old j w h)

private theorem BuilderExt.emb_ne_input {N g g' : ℕ} {B : PrefixBuilder N g}
    {B' : PrefixBuilder N g'} (e : BuilderExt B B') {u : Wire N g} {i : Fin N}
    (h : u ≠ .input i) : e.emb u ≠ .input i :=
  fun heq => h (e.emb_injective (heq.trans (e.emb_input i).symm))

private theorem BuilderExt.emb_ne_input_of_lo {N g g' : ℕ} {B : PrefixBuilder N g}
    {B' : PrefixBuilder N g'} (e : BuilderExt B B') {u : Wire N g} {i : Fin N}
    (h : B.lo u ≠ i.val) : e.emb u ≠ .input i :=
  e.emb_ne_input (B.input_ne_of_lo_ne h).symm

private def PrefixBuilder.empty (N : ℕ) : PrefixBuilder N 0 where
  program := .empty
  outs _ := none
  lo | .input i => i.val | .gate k => k.elim0
  hi | .input i => i.val + 1 | .gate k => k.elim0
  validInputs _ := ⟨rfl, rfl⟩
  validGates k := k.elim0

private theorem PrefixBuilder.uses_empty {N : ℕ} (w : Wire N 0) :
    (PrefixBuilder.empty N).uses w = 0 := by
  unfold PrefixBuilder.uses PrefixBuilder.empty
  dsimp only
  rw [progOutDeg_empty, Nat.zero_add, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro _ _ h
  cases h

private def PrefixBuilder.assignOut {N g : ℕ} (B : PrefixBuilder N g) (j₀ : ℕ)
    (w₀ : Wire N g) : PrefixBuilder N g where
  program := B.program
  outs j := if j = j₀ then some w₀ else B.outs j
  lo := B.lo
  hi := B.hi
  validInputs := B.validInputs
  validGates := B.validGates

private def PrefixBuilder.assignOutExt {N g : ℕ} (B : PrefixBuilder N g) (j₀ : ℕ)
    (w₀ : Wire N g) (hnone : B.outs j₀ = none) :
    BuilderExt B (B.assignOut j₀ w₀) where
  emb := id
  emb_injective := Function.injective_id
  emb_input _ := rfl
  lo_emb _ := rfl
  hi_emb _ := rfl
  depth_emb _ := rfl
  outs_old j w hw := by
    have hj : j ≠ j₀ := by intro heq; subst heq; rw [hnone] at hw; cases hw
    simp only [PrefixBuilder.assignOut, id_eq, hj, ↓reduceIte]
    exact hw

private theorem PrefixBuilder.uses_assignOut_self {N g : ℕ} (B : PrefixBuilder N g) {j₀ : ℕ}
    (hj₀ : j₀ < N) (w₀ : Wire N g) (hnone : B.outs j₀ = none) :
    (B.assignOut j₀ w₀).uses w₀ = B.uses w₀ + 1 := by
  unfold PrefixBuilder.uses PrefixBuilder.assignOut
  dsimp only
  have hfilt : ((Finset.range N).filter fun j => (if j = j₀ then some w₀ else B.outs j) = some w₀) =
      insert j₀ ((Finset.range N).filter fun j => B.outs j = some w₀) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    by_cases hj : j = j₀
    · subst hj
      simp only [↓reduceIte, hj₀, hnone, reduceCtorEq, and_false, or_false, and_self]
    · simp only [hj, ↓reduceIte, false_or]
  rw [hfilt, Finset.card_insert_of_notMem]
  · omega
  · simp only [Finset.mem_filter, hnone, reduceCtorEq, and_false, not_false_eq_true]

private theorem PrefixBuilder.uses_assignOut_ne {N g : ℕ} (B : PrefixBuilder N g) (j₀ : ℕ)
    (w₀ u : Wire N g) (hnone : B.outs j₀ = none) (hne : u ≠ w₀) :
    (B.assignOut j₀ w₀).uses u = B.uses u := by
  unfold PrefixBuilder.uses PrefixBuilder.assignOut
  dsimp only
  congr 1
  congr 1
  ext j
  simp only [Finset.mem_filter]
  by_cases hj : j = j₀
  · subst hj
    have hw_ne : some w₀ ≠ some u := fun h => hne (Option.some.inj h).symm
    simp only [↓reduceIte, hw_ne, hnone, reduceCtorEq, and_false]
  · simp only [hj, ↓reduceIte]

private def liftWireVal {N g : ℕ} (f : Wire N g → ℕ) (lastVal : ℕ) : Wire N (g + 1) → ℕ
  | .input i => f (.input i)
  | .gate k => Fin.lastCases lastVal (fun j => f (.gate j)) k

private theorem liftWireVal_castSucc {N g : ℕ} (f : Wire N g → ℕ) (lastVal : ℕ) (u : Wire N g) :
    liftWireVal f lastVal u.castSucc = f u := by
  cases u with
  | input _ => rfl
  | gate j => simp only [Wire.castSucc, liftWireVal, Fin.lastCases_castSucc]

private theorem liftWireVal_last {N g : ℕ} (f : Wire N g → ℕ) (lastVal : ℕ) :
    liftWireVal f lastVal (.gate (Fin.last g)) = lastVal := by
  simp only [liftWireVal, Fin.lastCases_last]

private def PrefixBuilder.addId {N g : ℕ} (B : PrefixBuilder N g) (w₀ : Wire N g) :
    PrefixBuilder N (g + 1) where
  program := B.program.gate ⟨.id, fun _ => w₀⟩
  outs j := (B.outs j).map Wire.castSucc
  lo := liftWireVal B.lo (B.lo w₀)
  hi := liftWireVal B.hi (B.hi w₀)
  validInputs i := B.validInputs i
  validGates := by
    refine Fin.lastCases ?_ (fun j => ?_)
    · rw [Program.lines_gate_last]
      simp only [Line.mapWires, Function.comp_apply, Wire.Renaming.castSucc_apply,
        liftWireVal_last, liftWireVal_castSucc, and_self]
    · rw [Program.lines_gate_castSucc]
      have hj := B.validGates j
      revert hj
      cases B.program.lines j with
      | mk op wires =>
        cases op <;>
        · intro hj
          simpa only [Line.mapWires, Function.comp_apply, Wire.Renaming.castSucc_apply,
            show Wire.gate j.castSucc = (Wire.gate j : Wire N g).castSucc from rfl,
            liftWireVal_castSucc] using hj

private def PrefixBuilder.addIdExt {N g : ℕ} (B : PrefixBuilder N g) (w₀ : Wire N g) :
    BuilderExt B (B.addId w₀) where
  emb := Wire.castSucc
  emb_injective := Wire.castSucc_injective
  emb_input _ := rfl
  lo_emb u := liftWireVal_castSucc B.lo (B.lo w₀) u
  hi_emb u := liftWireVal_castSucc B.hi (B.hi w₀) u
  depth_emb u := Program.wireDepths_gate_castSucc B.program _ u
  outs_old j w hw := by simp only [PrefixBuilder.addId, hw, Option.map_some]

private theorem PrefixBuilder.uses_addId_last {N g : ℕ} (B : PrefixBuilder N g) (w₀ : Wire N g) :
    (B.addId w₀).uses (.gate (Fin.last g)) = 0 := by
  unfold PrefixBuilder.uses PrefixBuilder.addId
  dsimp only
  rw [progOutDeg_gate_last, Nat.zero_add, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j _ h
  rcases hopt : B.outs j with _ | u <;> rw [hopt] at h
  · cases h
  · simp only [Option.map_some, Option.some.injEq] at h
    exact castSucc_ne_lastGate u h

private theorem PrefixBuilder.uses_addId_castSucc {N g : ℕ} (B : PrefixBuilder N g)
    (w₀ u : Wire N g) :
    (B.addId w₀).uses u.castSucc = B.uses u + (if u = w₀ then 1 else 0) := by
  unfold PrefixBuilder.uses PrefixBuilder.addId
  dsimp only
  rw [progOutDeg_gate_castSucc]
  have hout : ((Finset.range N).filter fun j => (B.outs j).map Wire.castSucc = some u.castSucc) =
      (Finset.range N).filter fun j => B.outs j = some u := by
    ext j
    simp only [Finset.mem_filter, Option.map_eq_some_iff]
    constructor
    · rintro ⟨hj, w', hw', heq⟩
      exact ⟨hj, Wire.castSucc_injective heq ▸ hw'⟩
    · rintro ⟨hj, hw⟩
      exact ⟨hj, u, hw, rfl⟩
  rw [hout]
  have hslot : (Finset.univ.filter fun _ : Fin 1 => w₀ = u).card = if u = w₀ then 1 else 0 := by
    by_cases h : u = w₀
    · subst h
      have hf : (Finset.univ.filter fun _ : Fin 1 => u = u) = Finset.univ :=
        Finset.filter_eq_self.mpr fun _ _ => rfl
      rw [hf, Finset.card_univ, Fintype.card_fin]
      simp only [↓reduceIte]
    · have hf : (Finset.univ.filter fun _ : Fin 1 => w₀ = u) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun _ _ heq => h heq.symm
      rw [hf, Finset.card_empty]
      simp only [h, ↓reduceIte]
  dsimp only at hslot ⊢
  rw [hslot]
  omega

private theorem PrefixBuilder.depth_addId_last {N g : ℕ} (B : PrefixBuilder N g)
    (w₀ : Wire N g) :
    (B.addId w₀).program.wireDepths (.gate (Fin.last g)) =
      B.program.wireDepths w₀ + 1 := by
  simp only [PrefixBuilder.addId]
  rw [wireDepths_gate_id _ (Fin.last g) (fun _ => w₀.castSucc)
      (by rw [Program.lines_gate_last]; rfl),
    Program.wireDepths_gate_castSucc]

private def mulWires {N g : ℕ} (w₀ w₁ : Wire N g) : Fin 2 → Wire N g
  | 0 => w₀
  | 1 => w₁

private def PrefixBuilder.addMul {N g : ℕ} (B : PrefixBuilder N g) (w₀ w₁ : Wire N g)
    (h0 : B.lo w₀ < B.hi w₀) (hmid : B.hi w₀ = B.lo w₁) (h1 : B.lo w₁ < B.hi w₁) :
    PrefixBuilder N (g + 1) where
  program := B.program.gate ⟨.mul, mulWires w₀ w₁⟩
  outs j := (B.outs j).map Wire.castSucc
  lo := liftWireVal B.lo (B.lo w₀)
  hi := liftWireVal B.hi (B.hi w₁)
  validInputs i := B.validInputs i
  validGates := by
    refine Fin.lastCases ?_ (fun j => ?_)
    · rw [Program.lines_gate_last]
      simp only [Line.mapWires, Function.comp_apply, Wire.Renaming.castSucc_apply, mulWires,
        liftWireVal_last, liftWireVal_castSucc, and_self]
      exact ⟨h0, hmid, h1, trivial⟩
    · rw [Program.lines_gate_castSucc]
      have hj := B.validGates j
      revert hj
      cases B.program.lines j with
      | mk op wires =>
        cases op <;>
        · intro hj
          simpa only [Line.mapWires, Function.comp_apply, Wire.Renaming.castSucc_apply,
            show Wire.gate j.castSucc = (Wire.gate j : Wire N g).castSucc from rfl,
            liftWireVal_castSucc] using hj

private def PrefixBuilder.addMulExt {N g : ℕ} (B : PrefixBuilder N g) (w₀ w₁ : Wire N g)
    (h0 : B.lo w₀ < B.hi w₀) (hmid : B.hi w₀ = B.lo w₁) (h1 : B.lo w₁ < B.hi w₁) :
    BuilderExt B (B.addMul w₀ w₁ h0 hmid h1) where
  emb := Wire.castSucc
  emb_injective := Wire.castSucc_injective
  emb_input _ := rfl
  lo_emb u := liftWireVal_castSucc B.lo (B.lo w₀) u
  hi_emb u := liftWireVal_castSucc B.hi (B.hi w₁) u
  depth_emb u := Program.wireDepths_gate_castSucc B.program _ u
  outs_old j w hw := by simp only [PrefixBuilder.addMul, hw, Option.map_some]

private theorem PrefixBuilder.uses_addMul_last {N g : ℕ} (B : PrefixBuilder N g)
    (w₀ w₁ : Wire N g) (h0 : B.lo w₀ < B.hi w₀) (hmid : B.hi w₀ = B.lo w₁)
    (h1 : B.lo w₁ < B.hi w₁) :
    (B.addMul w₀ w₁ h0 hmid h1).uses (.gate (Fin.last g)) = 0 := by
  unfold PrefixBuilder.uses PrefixBuilder.addMul
  dsimp only
  rw [progOutDeg_gate_last, Nat.zero_add, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j _ h
  rcases hopt : B.outs j with _ | u <;> rw [hopt] at h
  · cases h
  · simp only [Option.map_some, Option.some.injEq] at h
    exact castSucc_ne_lastGate u h

private theorem PrefixBuilder.uses_addMul_castSucc {N g : ℕ} (B : PrefixBuilder N g)
    (w₀ w₁ : Wire N g) (h0 : B.lo w₀ < B.hi w₀) (hmid : B.hi w₀ = B.lo w₁)
    (h1 : B.lo w₁ < B.hi w₁) (u : Wire N g) :
    (B.addMul w₀ w₁ h0 hmid h1).uses u.castSucc =
      B.uses u + (if u = w₀ then 1 else 0) + (if u = w₁ then 1 else 0) := by
  unfold PrefixBuilder.uses PrefixBuilder.addMul
  dsimp only
  rw [progOutDeg_gate_castSucc]
  have hout : ((Finset.range N).filter fun j => (B.outs j).map Wire.castSucc = some u.castSucc) =
      (Finset.range N).filter fun j => B.outs j = some u := by
    ext j
    simp only [Finset.mem_filter, Option.map_eq_some_iff]
    constructor
    · rintro ⟨hj, w', hw', heq⟩
      exact ⟨hj, Wire.castSucc_injective heq ▸ hw'⟩
    · rintro ⟨hj, hw⟩
      exact ⟨hj, u, hw, rfl⟩
  rw [hout]
  have hslot : (Finset.univ.filter fun a : Fin 2 => mulWires w₀ w₁ a = u).card =
      (if u = w₀ then 1 else 0) + (if u = w₁ then 1 else 0) := by
    have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by
      ext a
      fin_cases a <;> decide
    rw [huniv, Finset.filter_insert, Finset.filter_singleton]
    dsimp only [mulWires]
    by_cases h_0 : w₀ = u <;> by_cases h_1 : w₁ = u
    · subst h_0
      rw [h_1] at hmid
      omega
    · subst h_0
      have h_1' : w₀ ≠ w₁ := Ne.symm h_1
      simp only [h_1, h_1', ↓reduceIte]
      decide
    · subst h_1
      have h_0' : w₁ ≠ w₀ := Ne.symm h_0
      simp only [h_0, h_0', ↓reduceIte, Finset.card_singleton]
    · have h_0' : u ≠ w₀ := Ne.symm h_0
      have h_1' : u ≠ w₁ := Ne.symm h_1
      simp only [h_0, h_0', h_1, h_1', ↓reduceIte, Finset.card_empty]
  dsimp only at hslot ⊢
  rw [hslot]
  omega

private theorem PrefixBuilder.depth_addMul_last {N g : ℕ} (B : PrefixBuilder N g)
    (w₀ w₁ : Wire N g) (h0 : B.lo w₀ < B.hi w₀) (hmid : B.hi w₀ = B.lo w₁)
    (h1 : B.lo w₁ < B.hi w₁) :
    (B.addMul w₀ w₁ h0 hmid h1).program.wireDepths (.gate (Fin.last g)) =
      max (B.program.wireDepths w₀) (B.program.wireDepths w₁) + 1 := by
  simp only [PrefixBuilder.addMul]
  rw [wireDepths_gate_mul _ (Fin.last g)
      (Wire.Renaming.castSucc ∘ mulWires w₀ w₁)
      (by rw [Program.lines_gate_last]; rfl)]
  simp only [Function.comp_apply, mulWires, Wire.Renaming.castSucc_apply,
    Program.wireDepths_gate_castSucc]

private theorem PrefixBuilder.toCircuit_spec {N g k D : ℕ} (B : PrefixBuilder N g)
    (houts : ∀ j : Fin N, ∃ w, B.outs j.val = some w ∧ B.lo w = 0 ∧ B.hi w = j.val + 1 ∧
      B.program.wireDepths w ≤ D)
    (huses : ∀ w : Wire N g, B.uses w ≤ k) :
    ∃ c : PrefixCircuit N,
      IsIntervalPrefixCircuit c ∧
      IsUniversalPrefixCircuit c ∧
      FanoutAtMost c k ∧
      binaryComplexity c = B.mulCost ∧
      c.depth ≤ D ∧
      (∀ j : Fin N, ∀ w, B.outs j.val = some w →
        c.outputDepths j = B.program.wireDepths w) := by
  choose outWire hout_eq hout_lo hout_hi hout_depth using houts
  let c : PrefixCircuit N := ⟨B.program, outWire⟩
  have hint : IsIntervalPrefixCircuit c := by
    refine ⟨B.lo, B.hi, B.validInputs, fun k => ?_, fun j => ⟨hout_lo j, hout_hi j⟩⟩
    have hk := B.validGates k
    dsimp only [c]
    cases h : B.program.lines k with
    | mk op wires =>
      cases op <;> simpa only [h] using hk
  refine ⟨c, hint, hint.isUniversalPrefixCircuit, ?_, rfl, ?_, ?_⟩
  · intro w
    have hfan_eq : wireFanout c w = B.uses w := by
      simp only [wireFanout, PrefixBuilder.uses, progOutDeg_eq_circuit_outDeg c w]
      congr 1
      refine Finset.card_bij (fun (j : Fin N) _ => j.val) ?_ ?_ ?_
      · intro j hj
        rcases Finset.mem_filter.mp hj with ⟨_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr j.isLt, hout_eq j⟩
      · intro j₁ _ j₂ _ heq
        exact Fin.ext heq
      · intro m hm
        rcases Finset.mem_filter.mp hm with ⟨hm_lt, hm_eq⟩
        rw [Finset.mem_range] at hm_lt
        let j : Fin N := ⟨m, hm_lt⟩
        have hw_eq : outWire j = w := Option.some.inj ((hout_eq j).symm.trans hm_eq)
        exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hw_eq⟩, rfl⟩
    rw [hfan_eq]
    exact huses w
  · exact (Circuit.depth_le_iff c).mpr hout_depth
  · intro j w hw
    have heq : outWire j = w := Option.some.inj ((hout_eq j).symm.trans hw)
    simp only [Circuit.outputDepths, Function.comp_apply, c, heq]

private theorem PrefixBuilder.uses_addId_self {N g : ℕ} (B : PrefixBuilder N g)
    (w₀ : Wire N g) :
    (B.addId w₀).uses w₀.castSucc = B.uses w₀ + 1 := by
  rw [PrefixBuilder.uses_addId_castSucc]
  simp only [↓reduceIte]

private theorem PrefixBuilder.uses_addId_ne {N g : ℕ} (B : PrefixBuilder N g)
    (w₀ u : Wire N g) (hne : u ≠ w₀) :
    (B.addId w₀).uses u.castSucc = B.uses u := by
  rw [PrefixBuilder.uses_addId_castSucc]
  simp only [hne, ↓reduceIte, Nat.add_zero]

private theorem PrefixBuilder.uses_addMul_left {N g : ℕ} (B : PrefixBuilder N g)
    (w₀ w₁ : Wire N g) (h0 : B.lo w₀ < B.hi w₀) (hmid : B.hi w₀ = B.lo w₁)
    (h1 : B.lo w₁ < B.hi w₁) :
    (B.addMul w₀ w₁ h0 hmid h1).uses w₀.castSucc = B.uses w₀ + 1 := by
  have hne : w₀ ≠ w₁ := by intro heq; rw [heq] at hmid; omega
  rw [PrefixBuilder.uses_addMul_castSucc]
  simp only [hne, ↓reduceIte, Nat.add_zero]

private theorem PrefixBuilder.uses_addMul_right {N g : ℕ} (B : PrefixBuilder N g)
    (w₀ w₁ : Wire N g) (h0 : B.lo w₀ < B.hi w₀) (hmid : B.hi w₀ = B.lo w₁)
    (h1 : B.lo w₁ < B.hi w₁) :
    (B.addMul w₀ w₁ h0 hmid h1).uses w₁.castSucc = B.uses w₁ + 1 := by
  have hne : w₁ ≠ w₀ := by intro heq; rw [← heq] at hmid; omega
  rw [PrefixBuilder.uses_addMul_castSucc]
  simp only [hne, ↓reduceIte, Nat.add_zero]

private theorem PrefixBuilder.uses_addMul_ne {N g : ℕ} (B : PrefixBuilder N g)
    (w₀ w₁ : Wire N g) (h0 : B.lo w₀ < B.hi w₀) (hmid : B.hi w₀ = B.lo w₁)
    (h1 : B.lo w₁ < B.hi w₁) (u : Wire N g) (hne₀ : u ≠ w₀) (hne₁ : u ≠ w₁) :
    (B.addMul w₀ w₁ h0 hmid h1).uses u.castSucc = B.uses u := by
  rw [PrefixBuilder.uses_addMul_castSucc]
  simp only [hne₀, hne₁, ↓reduceIte, Nat.add_zero]

private theorem PrefixBuilder.uses_assignOut_le {N g k : ℕ} (B : PrefixBuilder N g) {j₀ : ℕ}
    (hj₀ : j₀ < N) (w₀ : Wire N g) (hnone : B.outs j₀ = none)
    (hw₀ : B.uses w₀ + 1 ≤ k) (hall : ∀ w : Wire N g, B.uses w ≤ k) :
    ∀ w' : Wire N g, (B.assignOut j₀ w₀).uses w' ≤ k := by
  intro w'
  by_cases hw' : w' = w₀
  · rw [hw', B.uses_assignOut_self hj₀ w₀ hnone]; exact hw₀
  · rw [B.uses_assignOut_ne j₀ w₀ w' hnone hw']; exact hall w'

private theorem PrefixBuilder.uses_addId_le {N g k : ℕ} (B : PrefixBuilder N g) (w₀ : Wire N g)
    (hw₀ : B.uses w₀ + 1 ≤ k) (hall : ∀ w : Wire N g, B.uses w ≤ k) :
    ∀ w' : Wire N (g + 1), (B.addId w₀).uses w' ≤ k := by
  intro w'
  rcases wire_cases_castSucc_or_last w' with rfl | ⟨u, rfl⟩
  · rw [B.uses_addId_last w₀]; exact Nat.zero_le k
  · by_cases huv : u = w₀
    · rw [huv, B.uses_addId_self w₀]; exact hw₀
    · rw [B.uses_addId_ne w₀ u huv]; exact hall u

private theorem PrefixBuilder.uses_addMul_le {N g k : ℕ} (B : PrefixBuilder N g)
    (w₀ w₁ : Wire N g) (h0 : B.lo w₀ < B.hi w₀) (hmid : B.hi w₀ = B.lo w₁)
    (h1 : B.lo w₁ < B.hi w₁) (hw₀ : B.uses w₀ + 1 ≤ k) (hw₁ : B.uses w₁ + 1 ≤ k)
    (hall : ∀ w : Wire N g, B.uses w ≤ k) :
    ∀ w' : Wire N (g + 1), (B.addMul w₀ w₁ h0 hmid h1).uses w' ≤ k := by
  intro w'
  rcases wire_cases_castSucc_or_last w' with rfl | ⟨u, rfl⟩
  · rw [B.uses_addMul_last w₀ w₁ h0 hmid h1]; exact Nat.zero_le k
  · by_cases hu0 : u = w₀
    · rw [hu0, B.uses_addMul_left w₀ w₁ h0 hmid h1]; exact hw₀
    · by_cases hu1 : u = w₁
      · rw [hu1, B.uses_addMul_right w₀ w₁ h0 hmid h1]; exact hw₁
      · rw [B.uses_addMul_ne w₀ w₁ h0 hmid h1 u hu0 hu1]; exact hall u

/-- Final step shared by both cases of `compileChain_exists`. Given the builder `B₁` compiled from
`B` for every tree of a chain except the last, whose root `u_init` covers `[a, m₂)`, multiply the
spine wire by `u_init`, compile `last` from the product, and multiply `u_init` by the root of
`last`. -/
private theorem compileChain_snoc {N k a m₂ b : ℕ} (hk : 2 ≤ k) (last : ConsistentTree m₂ b)
    (hlast : ∀ {g : ℕ} (B : PrefixBuilder N g) (v : Wire N g),
      1 ≤ m₂ → b ≤ N → last.FanoutAtMost k →
      B.lo v = 0 → B.hi v = m₂ → B.uses v = 0 →
      last.inDepth ≤ B.program.wireDepths v →
      (∀ j, m₂ - 1 ≤ j → j < b - 1 → B.outs j = none) →
      (∀ i : Fin N, m₂ ≤ i.val → i.val < b → B.uses (.input i) = 0) →
      (∀ w : Wire N g, B.uses w ≤ k) →
      ∃ (g' : ℕ) (B' : PrefixBuilder N g') (e : BuilderExt B B') (u : Wire N g'),
        B'.lo u = m₂ ∧ B'.hi u = b ∧
        B'.program.wireDepths u ≤ last.inDepth ∧
        B'.uses u = 0 ∧
        B'.mulCost = B.mulCost + 2 * (b - m₂ - 1) ∧
        (∀ j, m₂ - 1 ≤ j → j < b - 1 →
          ∃ w, B'.outs j = some w ∧ B'.lo w = 0 ∧ B'.hi w = j + 1 ∧
            B'.program.wireDepths w ≤ B.program.wireDepths v + last.outDepth) ∧
        (∀ j, (j < m₂ - 1 ∨ b - 1 ≤ j) → B'.outs j = (B.outs j).map e.emb) ∧
        (∀ w : Wire N g, w ≠ v → (∀ i : Fin N, m₂ ≤ i.val → i.val < b → w ≠ .input i) →
          e.emb w ≠ u ∧ B'.uses (e.emb w) = B.uses w) ∧
        (∀ w' : Wire N g', B'.uses w' ≤ k))
    {g g₁ : ℕ} (B : PrefixBuilder N g) (v : Wire N g) (B₁ : PrefixBuilder N g₁)
    (e₁ : BuilderExt B B₁) (u_init : Wire N g₁) (r dIn dOut : ℕ)
    (ha : 1 ≤ a) (hbN : b ≤ N) (ham : a < m₂) (hmb : m₂ < b) (hfan : last.FanoutAtMost k)
    (hv_lo : B.lo v = 0) (hv_hi : B.hi v = a) (hv_uses : B.uses v + (r + 1) ≤ k)
    (hv_depth : max dIn last.inDepth + 1 ≤ B.program.wireDepths v)
    (houts_free : ∀ j, a - 1 ≤ j → j < b - 1 → B.outs j = none)
    (hin_free : ∀ i : Fin N, a ≤ i.val → i.val < b → B.uses (.input i) = 0)
    (hui_lo : B₁.lo u_init = a) (hui_hi : B₁.hi u_init = m₂)
    (hui_d : B₁.program.wireDepths u_init ≤ dIn) (hui_u : B₁.uses u_init = 0)
    (hv_B₁_uses : B₁.uses (e₁.emb v) = B.uses v + r)
    (hcost₁ : B₁.mulCost = B.mulCost + 2 * (m₂ - a - 1))
    (hout₁_in : ∀ j, a - 1 ≤ j → j < m₂ - 1 → ∃ w, B₁.outs j = some w ∧ B₁.lo w = 0 ∧
      B₁.hi w = j + 1 ∧ B₁.program.wireDepths w ≤ B.program.wireDepths v + dOut + 1)
    (hout₁_out : ∀ j, (j < a - 1 ∨ m₂ - 1 ≤ j) → B₁.outs j = (B.outs j).map e₁.emb)
    (hold₁ : ∀ w : Wire N g, w ≠ v → (∀ i : Fin N, a ≤ i.val → i.val < m₂ → w ≠ .input i) →
      e₁.emb w ≠ u_init ∧ B₁.uses (e₁.emb w) = B.uses w)
    (hall₁ : ∀ w' : Wire N g₁, B₁.uses w' ≤ k) :
    ∃ (g' : ℕ) (B' : PrefixBuilder N g') (e : BuilderExt B B') (u : Wire N g'),
      B'.lo u = a ∧ B'.hi u = b ∧
      B'.program.wireDepths u ≤ max dIn last.inDepth + 1 ∧
      B'.uses u = 0 ∧
      B'.uses (e.emb v) = B.uses v + (r + 1) ∧
      B'.mulCost = B.mulCost + 2 * (b - a - 1) ∧
      (∀ j, a - 1 ≤ j → j < b - 1 →
        ∃ w, B'.outs j = some w ∧ B'.lo w = 0 ∧ B'.hi w = j + 1 ∧
          B'.program.wireDepths w ≤ B.program.wireDepths v + max dOut last.outDepth + 1) ∧
      (∀ j, (j < a - 1 ∨ b - 1 ≤ j) → B'.outs j = (B.outs j).map e.emb) ∧
      (∀ w : Wire N g, w ≠ v → (∀ i : Fin N, a ≤ i.val → i.val < b → w ≠ .input i) →
        e.emb w ≠ u ∧ B'.uses (e.emb w) = B.uses w) ∧
      (∀ w' : Wire N g', B'.uses w' ≤ k) := by
  let v_in_B₁ := e₁.emb v
  have hv_B₁_lo : B₁.lo v_in_B₁ = 0 := by rw [e₁.lo_emb, hv_lo]
  have hv_B₁_hi : B₁.hi v_in_B₁ = a := by rw [e₁.hi_emb, hv_hi]
  have hv_B₁_d : B₁.program.wireDepths v_in_B₁ = B.program.wireDepths v := e₁.depth_emb v
  have h0_2 : B₁.lo v_in_B₁ < B₁.hi v_in_B₁ := by omega
  have hmid_2 : B₁.hi v_in_B₁ = B₁.lo u_init := by omega
  have h1_2 : B₁.lo u_init < B₁.hi u_init := by omega
  let B₂ := B₁.addMul v_in_B₁ u_init h0_2 hmid_2 h1_2
  let e₂ := B₁.addMulExt v_in_B₁ u_init h0_2 hmid_2 h1_2
  let v_last : Wire N (g₁ + 1) := .gate (Fin.last g₁)
  have hvl_lo : B₂.lo v_last = 0 := by
    simp only [B₂, v_last, PrefixBuilder.addMul, liftWireVal_last, hv_B₁_lo]
  have hvl_hi : B₂.hi v_last = m₂ := by
    simp only [B₂, v_last, PrefixBuilder.addMul, liftWireVal_last, hui_hi]
  have hvl_d_eq : B₂.program.wireDepths v_last = B.program.wireDepths v + 1 := by
    have := B₁.depth_addMul_last v_in_B₁ u_init h0_2 hmid_2 h1_2
    dsimp only [B₂, v_last] at *; omega
  have houts₂ : ∀ j, m₂ - 1 ≤ j → j < b - 1 → B₂.outs j = none := by
    intro j hj1 hj2
    simp only [B₂, PrefixBuilder.addMul]
    rw [hout₁_out j (Or.inr hj1), houts_free j (by omega) hj2, Option.map_none, Option.map_none]
  have hin₂ : ∀ i : Fin N, m₂ ≤ i.val → i.val < b → B₂.uses (.input i) = 0 := by
    intro i hi1 hi2
    have hne_v : (Wire.input i : Wire N g₁) ≠ v_in_B₁ := B₁.input_ne_of_lo_ne (by omega)
    have hne_ui : (Wire.input i : Wire N g₁) ≠ u_init := B₁.input_ne_of_lo_ne (by omega)
    have hB₁_in : B₁.uses (.input i) = 0 := by
      have h1 : (Wire.input i : Wire N g) ≠ v := B.input_ne_of_lo_ne (by omega)
      have h2 : ∀ i' : Fin N, a ≤ i'.val → i'.val < m₂ →
          (Wire.input i : Wire N g) ≠ .input i' :=
        fun i' _ hi'2 => mt Wire.input.inj (Fin.ne_of_val_ne (by omega))
      rw [← e₁.emb_input i]
      exact (hold₁ (.input i) h1 h2).2.trans (hin_free i (by omega) hi2)
    exact (B₁.uses_addMul_ne v_in_B₁ u_init h0_2 hmid_2 h1_2 (.input i) hne_v hne_ui).trans
      hB₁_in
  have hall₂ : ∀ w' : Wire N (g₁ + 1), B₂.uses w' ≤ k :=
    B₁.uses_addMul_le v_in_B₁ u_init h0_2 hmid_2 h1_2
      (by dsimp only [v_in_B₁] at *; omega) (by omega) hall₁
  obtain ⟨g₃, B₃, e₃, u_last, hul_lo, hul_hi, hul_d, hul_u, hcost₃, hout₃_in, hout₃_out, hold₃,
      hall₃⟩ :=
    hlast B₂ v_last (by omega) hbN hfan hvl_lo hvl_hi
      (B₁.uses_addMul_last v_in_B₁ u_init h0_2 hmid_2 h1_2) (by omega) houts₂ hin₂ hall₂
  let ui_in_B₃ := e₃.emb (e₂.emb u_init)
  have hui_B₃_lo : B₃.lo ui_in_B₃ = a := by rw [e₃.lo_emb, e₂.lo_emb, hui_lo]
  have hui_B₃_hi : B₃.hi ui_in_B₃ = m₂ := by rw [e₃.hi_emb, e₂.hi_emb, hui_hi]
  have hui_B₃_d : B₃.program.wireDepths ui_in_B₃ = B₁.program.wireDepths u_init := by
    rw [e₃.depth_emb, e₂.depth_emb]
  have hui_B₃_uses : B₃.uses ui_in_B₃ = 1 := by
    have h1 : e₂.emb u_init ≠ v_last := castSucc_ne_lastGate u_init
    have h2 : ∀ i : Fin N, m₂ ≤ i.val → i.val < b → e₂.emb u_init ≠ .input i :=
      fun i hi1 _ => e₂.emb_ne_input_of_lo (by omega)
    have hstep := B₁.uses_addMul_right v_in_B₁ u_init h0_2 hmid_2 h1_2
    rw [hui_u] at hstep
    exact (hold₃ (e₂.emb u_init) h1 h2).2.trans hstep
  have h0_4 : B₃.lo ui_in_B₃ < B₃.hi ui_in_B₃ := by omega
  have hmid_4 : B₃.hi ui_in_B₃ = B₃.lo u_last := by omega
  have h1_4 : B₃.lo u_last < B₃.hi u_last := by omega
  let B₄ := B₃.addMul ui_in_B₃ u_last h0_4 hmid_4 h1_4
  let e₄ := B₃.addMulExt ui_in_B₃ u_last h0_4 hmid_4 h1_4
  let u : Wire N (g₃ + 1) := .gate (Fin.last g₃)
  let e_all := ((e₁.trans e₂).trans e₃).trans e₄
  have hv_B₃_uses : B₃.uses (e₃.emb (e₂.emb v_in_B₁)) = B.uses v + r + 1 := by
    have h1 : e₂.emb v_in_B₁ ≠ v_last := castSucc_ne_lastGate v_in_B₁
    have h2 : ∀ i : Fin N, m₂ ≤ i.val → i.val < b → e₂.emb v_in_B₁ ≠ .input i :=
      fun i hi1 _ => e₂.emb_ne_input_of_lo (by omega)
    have hstep := B₁.uses_addMul_left v_in_B₁ u_init h0_2 hmid_2 h1_2
    rw [hv_B₁_uses] at hstep
    exact (hold₃ _ h1 h2).2.trans hstep
  refine ⟨g₃ + 1, B₄, e_all, u, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [B₄, u, PrefixBuilder.addMul, liftWireVal_last, hui_B₃_lo]
  · simp only [B₄, u, PrefixBuilder.addMul, liftWireVal_last, hul_hi]
  · have := B₃.depth_addMul_last ui_in_B₃ u_last h0_4 hmid_4 h1_4
    dsimp only [B₄, u] at *; omega
  · exact B₃.uses_addMul_last ui_in_B₃ u_last h0_4 hmid_4 h1_4
  · have hlo (w) (hw : B₃.lo w ≠ 0) : e₃.emb (e₂.emb v_in_B₁) ≠ w := fun heq => hw <| by
      rw [← heq, e₃.lo_emb, e₂.lo_emb, hv_B₁_lo]
    rw [← Nat.add_assoc]
    exact (B₃.uses_addMul_ne ui_in_B₃ u_last h0_4 hmid_4 h1_4 _ (hlo _ (by omega))
      (hlo _ (by omega))).trans hv_B₃_uses
  · have hc2 : B₂.mulCost = B₁.mulCost + 1 := by
      simp only [PrefixBuilder.mulCost, B₂, PrefixBuilder.addMul, Program.cost_gate]
    have hc4 : B₄.mulCost = B₃.mulCost + 1 := by
      simp only [PrefixBuilder.mulCost, B₄, PrefixBuilder.addMul, Program.cost_gate]
    omega
  · intro j hj1 hj2
    by_cases hjm : j < m₂ - 1
    · obtain ⟨w₁, hw₁_eq, hw₁_lo, hw₁_hi, hw₁_d⟩ := hout₁_in j hj1 hjm
      have hw₃_eq : B₃.outs j = some (e₃.emb (e₂.emb w₁)) := by
        rw [hout₃_out j (Or.inl hjm)]
        simp only [B₂, PrefixBuilder.addMul, hw₁_eq, Option.map_some]; rfl
      refine ⟨e₄.emb (e₃.emb (e₂.emb w₁)), ?_, ?_, ?_, ?_⟩
      · simp only [B₄, PrefixBuilder.addMul, hw₃_eq, Option.map_some]; rfl
      · rw [e₄.lo_emb, e₃.lo_emb, e₂.lo_emb, hw₁_lo]
      · rw [e₄.hi_emb, e₃.hi_emb, e₂.hi_emb, hw₁_hi]
      · rw [e₄.depth_emb, e₃.depth_emb, e₂.depth_emb]
        omega
    · obtain ⟨w₃, hw₃_eq, hw₃_lo, hw₃_hi, hw₃_d⟩ := hout₃_in j (by omega) hj2
      refine ⟨e₄.emb w₃, ?_, ?_, ?_, ?_⟩
      · simp only [B₄, PrefixBuilder.addMul, hw₃_eq, Option.map_some]; rfl
      · rw [e₄.lo_emb, hw₃_lo]
      · rw [e₄.hi_emb, hw₃_hi]
      · rw [e₄.depth_emb]
        omega
  · intro j hj
    have hj3 : j < m₂ - 1 ∨ b - 1 ≤ j := by omega
    have hj1 : j < a - 1 ∨ m₂ - 1 ≤ j := by omega
    simp only [B₄, PrefixBuilder.addMul]
    rw [hout₃_out j hj3]
    simp only [B₂, PrefixBuilder.addMul, Option.map_map]
    rw [hout₁_out j hj1]
    simp only [Option.map_map]; rfl
  · intro w hw_ne hw_in
    refine ⟨castSucc_ne_lastGate _, ?_⟩
    obtain ⟨hne_ui, huses₁⟩ := hold₁ w hw_ne (fun i hi1 hi2 => hw_in i hi1 (by omega))
    have hne_v : e₁.emb w ≠ v_in_B₁ := fun heq => hw_ne (e₁.emb_injective heq)
    have huses₂ : B₂.uses (e₂.emb (e₁.emb w)) = B.uses w :=
      (B₁.uses_addMul_ne v_in_B₁ u_init h0_2 hmid_2 h1_2 _ hne_v hne_ui).trans huses₁
    have h2_w : e₂.emb (e₁.emb w) ≠ v_last := castSucc_ne_lastGate _
    have h3_w : ∀ i : Fin N, m₂ ≤ i.val → i.val < b → e₂.emb (e₁.emb w) ≠ .input i :=
      fun i hi1 hi2 => e₂.emb_ne_input (e₁.emb_ne_input (hw_in i (by omega) hi2))
    obtain ⟨hne_ul, huses₃⟩ := hold₃ _ h2_w h3_w
    have hne_ui_B₃ : e₃.emb (e₂.emb (e₁.emb w)) ≠ ui_in_B₃ :=
      fun heq => hne_ui (e₂.emb_injective (e₃.emb_injective heq))
    exact (B₃.uses_addMul_ne ui_in_B₃ u_last h0_4 hmid_4 h1_4 _ hne_ui_B₃ hne_ul).trans
      (huses₃.trans huses₂)
  · exact B₃.uses_addMul_le ui_in_B₃ u_last h0_4 hmid_4 h1_4 (by omega) (by omega) hall₃

mutual
private theorem compileTree_exists {N k : ℕ} (hk : 2 ≤ k) :
    ∀ {a b : ℕ} (t : ConsistentTree a b) {g : ℕ} (B : PrefixBuilder N g) (v : Wire N g),
      1 ≤ a → b ≤ N → t.FanoutAtMost k →
      B.lo v = 0 → B.hi v = a → B.uses v = 0 →
      t.inDepth ≤ B.program.wireDepths v →
      (∀ j, a - 1 ≤ j → j < b - 1 → B.outs j = none) →
      (∀ i : Fin N, a ≤ i.val → i.val < b → B.uses (.input i) = 0) →
      (∀ w : Wire N g, B.uses w ≤ k) →
      ∃ (g' : ℕ) (B' : PrefixBuilder N g') (e : BuilderExt B B') (u : Wire N g'),
        B'.lo u = a ∧ B'.hi u = b ∧
        B'.program.wireDepths u ≤ t.inDepth ∧
        B'.uses u = 0 ∧
        B'.mulCost = B.mulCost + 2 * (b - a - 1) ∧
        (∀ j, a - 1 ≤ j → j < b - 1 →
          ∃ w, B'.outs j = some w ∧ B'.lo w = 0 ∧ B'.hi w = j + 1 ∧
            B'.program.wireDepths w ≤ B.program.wireDepths v + t.outDepth) ∧
        (∀ j, (j < a - 1 ∨ b - 1 ≤ j) → B'.outs j = (B.outs j).map e.emb) ∧
        (∀ w : Wire N g, w ≠ v → (∀ i : Fin N, a ≤ i.val → i.val < b → w ≠ .input i) →
          e.emb w ≠ u ∧ B'.uses (e.emb w) = B.uses w) ∧
        (∀ w' : Wire N g', B'.uses w' ≤ k)
  | _, _, .leaf a, g, B, v, ha, hbN, _, hv_lo, hv_hi, hv_uses, _, houts_free, hin_free,
      hall_uses => by
    have hnone : B.outs (a - 1) = none := houts_free (a - 1) le_rfl (by omega)
    let B₁ := B.assignOut (a - 1) v
    let e₁ := B.assignOutExt (a - 1) v hnone
    let u : Wire N g := .input ⟨a, hbN⟩
    have hvu : u ≠ v := B.input_ne_of_lo_ne (show B.lo v ≠ a by omega)
    refine ⟨g, B₁, e₁, u, (B.validInputs ⟨a, hbN⟩).1, (B.validInputs ⟨a, hbN⟩).2, le_rfl, ?_, ?_,
      ?_, ?_, ?_, B.uses_assignOut_le (by omega) v hnone (by omega) hall_uses⟩
    · exact (B.uses_assignOut_ne (a - 1) v u hnone hvu).trans
        (hin_free ⟨a, hbN⟩ le_rfl (Nat.lt_succ_self a))
    · simp only [PrefixBuilder.mulCost, B₁, PrefixBuilder.assignOut,
        show a + 1 - a - 1 = 0 by omega, Nat.mul_zero, Nat.add_zero]
    · intro j hj1 hj2
      have hj : j = a - 1 := by omega
      subst hj
      refine ⟨v, ?_, hv_lo, ?_, ?_⟩
      · simp only [B₁, PrefixBuilder.assignOut, ↓reduceIte]
      · dsimp only [B₁, PrefixBuilder.assignOut]; omega
      · simp only [B₁, PrefixBuilder.assignOut, ConsistentTree.outDepth, Nat.add_zero]
        exact le_rfl
    · intro j hj
      have hj_ne : j ≠ a - 1 := by omega
      simp only [B₁, e₁, PrefixBuilder.assignOut, PrefixBuilder.assignOutExt, hj_ne, ↓reduceIte]
      cases B.outs j <;> rfl
    · intro w hw_ne hw_in
      have hwu : w ≠ u := hw_in ⟨a, hbN⟩ le_rfl (Nat.lt_succ_self a)
      exact ⟨hwu, B.uses_assignOut_ne (a - 1) v w hnone hw_ne⟩
  | a, b, .buffer c, g, B, v, ha, hbN, hfan, hv_lo, hv_hi, hv_uses, hv_depth, houts_free, hin_free,
      hall_uses => by
    let B₁ := B.addId v
    let e₁ := B.addIdExt v
    let v₁ : Wire N (g + 1) := .gate (Fin.last g)
    have hv₁_lo : B₁.lo v₁ = 0 := by
      simp only [B₁, v₁, PrefixBuilder.addId, liftWireVal_last, hv_lo]
    have hv₁_hi : B₁.hi v₁ = a := by
      simp only [B₁, v₁, PrefixBuilder.addId, liftWireVal_last, hv_hi]
    have hv₁_uses : B₁.uses v₁ = 0 := B.uses_addId_last v
    have hv₁_depth : c.inDepth ≤ B₁.program.wireDepths v₁ := by
      have hd1 := B.depth_addId_last v
      simp only [ConsistentTree.inDepth] at hv_depth
      dsimp only [B₁, v₁] at *
      omega
    have houts₁ : ∀ j, a - 1 ≤ j → j < b - 1 → B₁.outs j = none := by
      intro j hj1 hj2
      simp only [B₁, PrefixBuilder.addId, houts_free j hj1 hj2, Option.map_none]
    have hin₁ : ∀ i : Fin N, a ≤ i.val → i.val < b → B₁.uses (.input i) = 0 := by
      intro i hi1 hi2
      have hne : (Wire.input i : Wire N g) ≠ v := B.input_ne_of_lo_ne (by omega)
      exact (B.uses_addId_ne v (.input i) hne).trans (hin_free i hi1 hi2)
    have hall₁ : ∀ w' : Wire N (g + 1), B₁.uses w' ≤ k :=
      B.uses_addId_le v (by omega) hall_uses
    obtain ⟨g₂, B₂, e₂, u, hu_lo, hu_hi, hu_d, hu_u, hcost, hout_in, hout_out, hold, hall₂⟩ :=
      compileTree_exists hk c B₁ v₁ ha hbN hfan.2 hv₁_lo hv₁_hi hv₁_uses hv₁_depth houts₁ hin₁
        hall₁
    refine ⟨g₂, B₂, e₁.trans e₂, u, hu_lo, hu_hi, hu_d, hu_u, ?_, ?_, ?_, ?_, hall₂⟩
    · simpa only [PrefixBuilder.mulCost, B₁, PrefixBuilder.addId, Program.cost_gate,
        Nat.add_zero] using hcost
    · intro j hj1 hj2
      obtain ⟨w, hw_eq, hw_lo, hw_hi, hw_d⟩ := hout_in j hj1 hj2
      refine ⟨w, hw_eq, hw_lo, hw_hi, ?_⟩
      have hd1 := B.depth_addId_last v
      simp only [ConsistentTree.outDepth]
      dsimp only [B₁, v₁] at *
      omega
    · intro j hj
      rw [hout_out j hj]
      simp only [B₁, PrefixBuilder.addId, Option.map_map]
      rfl
    · intro w hw_ne hw_in
      have h1 : e₁.emb w ≠ v₁ := castSucc_ne_lastGate w
      have h2 : ∀ i : Fin N, a ≤ i.val → i.val < b → e₁.emb w ≠ .input i :=
        fun i hi1 hi2 => e₁.emb_ne_input (hw_in i hi1 hi2)
      obtain ⟨hne_u, huses_w⟩ := hold (e₁.emb w) h1 h2
      refine ⟨hne_u, ?_⟩
      exact huses_w.trans (B.uses_addId_ne v w hw_ne)
  | a, b, .split ch, g, B, v, ha, hbN, hfan, hv_lo, hv_hi, hv_uses, hv_depth, houts_free, hin_free,
      hall_uses => by
    simp only [ConsistentTree.inDepth] at hv_depth
    obtain ⟨g', B', e, u, hu_lo, hu_hi, hu_d, hu_u, _, hcost, hout_in, hout_out, hold, hall'⟩ :=
      compileChain_exists hk ch B v ha hbN hfan.2 hv_lo hv_hi
        (by rw [hv_uses, Nat.zero_add]; exact hfan.1) hv_depth houts_free hin_free hall_uses
    exact ⟨g', B', e, u, hu_lo, hu_hi, hu_d, hu_u, hcost, hout_in, hout_out, hold, hall'⟩

private theorem compileChain_exists {N k : ℕ} (hk : 2 ≤ k) :
    ∀ {a m₀ b : ℕ} (ch : ConsistentChain a m₀ b) {g : ℕ} (B : PrefixBuilder N g) (v : Wire N g),
      1 ≤ a → b ≤ N → ch.FanoutAtMost k →
      B.lo v = 0 → B.hi v = a → B.uses v + ch.arity ≤ k →
      ch.inDepth ≤ B.program.wireDepths v →
      (∀ j, a - 1 ≤ j → j < b - 1 → B.outs j = none) →
      (∀ i : Fin N, a ≤ i.val → i.val < b → B.uses (.input i) = 0) →
      (∀ w : Wire N g, B.uses w ≤ k) →
      ∃ (g' : ℕ) (B' : PrefixBuilder N g') (e : BuilderExt B B') (u : Wire N g'),
        B'.lo u = a ∧ B'.hi u = b ∧
        B'.program.wireDepths u ≤ ch.inDepth ∧
        B'.uses u = 0 ∧
        B'.uses (e.emb v) = B.uses v + ch.arity ∧
        B'.mulCost = B.mulCost + 2 * (b - a - 1) ∧
        (∀ j, a - 1 ≤ j → j < b - 1 →
          ∃ w, B'.outs j = some w ∧ B'.lo w = 0 ∧ B'.hi w = j + 1 ∧
            B'.program.wireDepths w ≤ B.program.wireDepths v + ch.maxOutDepth + 1) ∧
        (∀ j, (j < a - 1 ∨ b - 1 ≤ j) → B'.outs j = (B.outs j).map e.emb) ∧
        (∀ w : Wire N g, w ≠ v → (∀ i : Fin N, a ≤ i.val → i.val < b → w ≠ .input i) →
          e.emb w ≠ u ∧ B'.uses (e.emb w) = B.uses w) ∧
        (∀ w' : Wire N g', B'.uses w' ≤ k)
  | a, m, b, .two t₁ t₂, g, B, v, ha, hbN, hfan, hv_lo, hv_hi, hv_uses, hv_depth, houts_free,
      hin_free, hall_uses => by
    have hlt1 := t₁.lt
    have hlt2 := t₂.lt
    simp only [ConsistentChain.arity] at hv_uses
    simp only [ConsistentChain.inDepth] at hv_depth
    let B₁ := B.addId v
    let e₁ := B.addIdExt v
    let v₁ : Wire N (g + 1) := .gate (Fin.last g)
    have hv₁_lo : B₁.lo v₁ = 0 := by
      simp only [B₁, v₁, PrefixBuilder.addId, liftWireVal_last, hv_lo]
    have hv₁_hi : B₁.hi v₁ = a := by
      simp only [B₁, v₁, PrefixBuilder.addId, liftWireVal_last, hv_hi]
    have houts₁ : ∀ j, a - 1 ≤ j → j < m - 1 → B₁.outs j = none := by
      intro j hj1 hj2
      simp only [B₁, PrefixBuilder.addId, houts_free j hj1 (by omega), Option.map_none]
    have hin₁ : ∀ i : Fin N, a ≤ i.val → i.val < m → B₁.uses (.input i) = 0 := by
      intro i hi1 hi2
      have hne : (Wire.input i : Wire N g) ≠ v := B.input_ne_of_lo_ne (by omega)
      exact (B.uses_addId_ne v (.input i) hne).trans (hin_free i hi1 (by omega))
    have hd1 := B.depth_addId_last v
    obtain ⟨g₂, B₂, e₂, u₁, hu₁_lo, hu₁_hi, hu₁_d, hu₁_u, hcost₂, hout₂_in, hout₂_out, hold₂,
        hall₂⟩ :=
      compileTree_exists hk t₁ B₁ v₁ ha (by omega) hfan.1 hv₁_lo hv₁_hi (B.uses_addId_last v)
        (by dsimp only [B₁, v₁] at *; omega) houts₁ hin₁ (B.uses_addId_le v (by omega) hall_uses)
    refine compileChain_snoc hk t₂ (compileTree_exists hk t₂) B v B₂ (e₁.trans e₂) u₁ 1 t₁.inDepth
      t₁.outDepth ha hbN hlt1 hlt2 hfan.2 hv_lo hv_hi hv_uses hv_depth houts_free hin_free hu₁_lo
      hu₁_hi hu₁_d hu₁_u ?_ ?_ ?_ ?_ ?_ hall₂
    · exact (hold₂ (e₁.emb v) (castSucc_ne_lastGate v)
        fun i hi1 _ => e₁.emb_ne_input_of_lo (by omega)).2.trans (B.uses_addId_self v)
    · have hc1 : B₁.mulCost = B.mulCost := by
        simp only [PrefixBuilder.mulCost, B₁, PrefixBuilder.addId, Program.cost_gate, Nat.add_zero]
      omega
    · intro j hj1 hj2
      obtain ⟨w, hw_eq, hw_lo, hw_hi, hw_d⟩ := hout₂_in j hj1 hj2
      refine ⟨w, hw_eq, hw_lo, hw_hi, ?_⟩
      dsimp only [B₁, v₁] at hw_d; omega
    · intro j hj
      rw [hout₂_out j hj]
      simp only [B₁, PrefixBuilder.addId, Option.map_map]; rfl
    · intro w hw_ne hw_in
      obtain ⟨hne, huses⟩ := hold₂ (e₁.emb w) (castSucc_ne_lastGate w)
        fun i hi1 hi2 => e₁.emb_ne_input (hw_in i hi1 hi2)
      exact ⟨hne, huses.trans (B.uses_addId_ne v w hw_ne)⟩
  | a, m₁, b, .snoc (m₂ := m₂) init last, g, B, v, ha, hbN, hfan, hv_lo, hv_hi, hv_uses, hv_depth,
      houts_free, hin_free, hall_uses => by
    have hlt_init := init.lt
    have hlt_last := last.lt
    simp only [ConsistentChain.arity] at hv_uses
    simp only [ConsistentChain.inDepth] at hv_depth
    obtain ⟨g₁, B₁, e₁, u_init, hui_lo, hui_hi, hui_d, hui_u, hv_B₁_uses, hcost₁, hout₁_in,
        hout₁_out, hold₁, hall₁⟩ :=
      compileChain_exists hk init B v ha (by omega) hfan.1 hv_lo hv_hi (by omega) (by omega)
        (fun j hj1 hj2 => houts_free j hj1 (by omega))
        (fun i hi1 hi2 => hin_free i hi1 (by omega)) hall_uses
    exact compileChain_snoc hk last (compileTree_exists hk last) B v B₁ e₁ u_init init.arity
      init.inDepth init.maxOutDepth ha hbN hlt_init hlt_last hfan.2 hv_lo hv_hi hv_uses hv_depth
      houts_free hin_free hui_lo hui_hi hui_d hui_u hv_B₁_uses hcost₁ hout₁_in hout₁_out hold₁
      hall₁
end

private theorem exists_rippleOptimalPrefixCircuit {N k : ℕ} (hk : 2 ≤ k) (hN : 1 ≤ N) :
    ∃ c : PrefixCircuit N,
      IsIntervalPrefixCircuit c ∧ IsOptimalPrefixCircuit c ∧ FanoutAtMost c k ∧
        c.depth = N - 1 := by
  have hloop : ∀ m : ℕ, 1 ≤ m → m ≤ N →
      ∃ (g : ℕ) (B : PrefixBuilder N g) (v : Wire N g),
        B.lo v = 0 ∧ B.hi v = m ∧ B.program.wireDepths v = m - 1 ∧
        B.uses v = 1 ∧ B.mulCost = m - 1 ∧
        B.outs (m - 1) = some v ∧
        (∀ j < m, ∃ w, B.outs j = some w ∧ B.lo w = 0 ∧ B.hi w = j + 1 ∧
          B.program.wireDepths w = j) ∧
        (∀ j, m ≤ j → B.outs j = none) ∧
        (∀ i : Fin N, m ≤ i.val → B.uses (.input i) = 0) ∧
        (∀ w : Wire N g, B.uses w ≤ k) := by
    intro m
    induction m with
    | zero => intro hm; omega
    | succ m ih =>
      cases m with
      | zero =>
        intro _ _
        let B₀ := PrefixBuilder.empty N
        let v₀ : Wire N 0 := .input ⟨0, hN⟩
        let B₁ := B₀.assignOut 0 v₀
        refine ⟨0, B₁, v₀, rfl, rfl, rfl, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
        · exact (B₀.uses_assignOut_self hN v₀ rfl).trans (by rw [PrefixBuilder.uses_empty])
        · simp only [B₁, PrefixBuilder.assignOut, ↓reduceIte]
        · intro j hj
          have hj0 : j = 0 := by omega
          subst hj0
          exact ⟨v₀, by simp only [B₁, PrefixBuilder.assignOut, ↓reduceIte], rfl, rfl, rfl⟩
        · intro j hj
          have hj_ne : j ≠ 0 := by omega
          simp only [B₁, PrefixBuilder.assignOut, hj_ne, ↓reduceIte]; rfl
        · intro i hi
          have hne : (Wire.input i : Wire N 0) ≠ v₀ :=
            mt Wire.input.inj (Fin.ne_of_val_ne (show i.val ≠ 0 by omega))
          exact (B₀.uses_assignOut_ne 0 v₀ (.input i) rfl hne).trans
            (PrefixBuilder.uses_empty (.input i))
        · exact B₀.uses_assignOut_le hN v₀ rfl
            (by rw [PrefixBuilder.uses_empty]; omega)
            (fun w => by rw [PrefixBuilder.uses_empty]; omega)
      | succ m =>
        intro _ hmN
        obtain ⟨g, B, v, hv_lo, hv_hi, hv_d, hv_u, hcost, _, hout_lt, hout_ge, hin_ge, hall⟩ :=
          ih (by omega) (by omega)
        let inp : Wire N g := .input ⟨m + 1, hmN⟩
        have hinp_lo : B.lo inp = m + 1 := (B.validInputs ⟨m + 1, hmN⟩).1
        have hinp_hi : B.hi inp = m + 2 := (B.validInputs ⟨m + 1, hmN⟩).2
        have h0 : B.lo v < B.hi v := by omega
        have hmid : B.hi v = B.lo inp := by omega
        have h1 : B.lo inp < B.hi inp := by omega
        let B₁ := B.addMul v inp h0 hmid h1
        let e₁ := B.addMulExt v inp h0 hmid h1
        let v' : Wire N (g + 1) := .gate (Fin.last g)
        have hnone₁ : B₁.outs (m + 1) = none := by
          simp only [B₁, PrefixBuilder.addMul, hout_ge (m + 1) le_rfl, Option.map_none]
        let B₂ := B₁.assignOut (m + 1) v'
        have hv'_d : B₁.program.wireDepths v' = m + 1 := by
          have hd_last := B.depth_addMul_last v inp h0 hmid h1
          have hd_inp : B.program.wireDepths inp = 0 := rfl
          dsimp only [B₁, v'] at *; omega
        have hv'_lo : B₂.lo v' = 0 := by
          simp only [B₂, PrefixBuilder.assignOut, B₁, v', PrefixBuilder.addMul, liftWireVal_last,
            hv_lo]
        have hv'_hi : B₂.hi v' = m + 2 := by
          simp only [B₂, PrefixBuilder.assignOut, B₁, v', PrefixBuilder.addMul, liftWireVal_last,
            hinp_hi]
        refine ⟨g + 1, B₂, v', hv'_lo, hv'_hi, hv'_d, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · have := B₁.uses_assignOut_self hmN v' hnone₁
          have := B.uses_addMul_last v inp h0 hmid h1
          dsimp only [B₁, B₂, v'] at *; omega
        · simp only [B₂, PrefixBuilder.assignOut, PrefixBuilder.mulCost, B₁,
            PrefixBuilder.addMul, Program.cost_gate]
          dsimp only [PrefixBuilder.mulCost] at hcost
          omega
        · simp only [B₂, PrefixBuilder.assignOut, Nat.add_sub_cancel, ↓reduceIte]
        · intro j hj
          by_cases hjeq : j = m + 1
          · subst hjeq
            exact ⟨v', by simp only [B₂, PrefixBuilder.assignOut, ↓reduceIte], hv'_lo, hv'_hi,
              hv'_d⟩
          · obtain ⟨w, hw_eq, hw_lo, hw_hi, hw_d⟩ := hout_lt j (by omega)
            refine ⟨e₁.emb w, ?_, ?_, ?_, ?_⟩
            · simp only [B₂, PrefixBuilder.assignOut, hjeq, ↓reduceIte, B₁,
                PrefixBuilder.addMul, hw_eq, Option.map_some]; rfl
            · exact e₁.lo_emb w |>.trans hw_lo
            · exact e₁.hi_emb w |>.trans hw_hi
            · exact e₁.depth_emb w |>.trans hw_d
        · intro j hj
          have hj_ne : j ≠ m + 1 := by omega
          simp only [B₂, PrefixBuilder.assignOut, hj_ne, ↓reduceIte, B₁, PrefixBuilder.addMul,
            hout_ge j (by omega), Option.map_none]
        · intro i hi
          have hne_v' : (Wire.input i : Wire N (g + 1)) ≠ v' := castSucc_ne_lastGate (.input i)
          have hne_v : (Wire.input i : Wire N g) ≠ v := B.input_ne_of_lo_ne (by omega)
          have hne_inp : (Wire.input i : Wire N g) ≠ inp :=
            mt Wire.input.inj (Fin.ne_of_val_ne (show i.val ≠ m + 1 by omega))
          exact (B₁.uses_assignOut_ne (m + 1) v' (.input i) hnone₁ hne_v').trans
            ((B.uses_addMul_ne v inp h0 hmid h1 (.input i) hne_v hne_inp).trans
              (hin_ge i (by omega)))
        · have hall₁ : ∀ w' : Wire N (g + 1), B₁.uses w' ≤ k :=
            B.uses_addMul_le v inp h0 hmid h1 (by omega)
              (by have := hin_ge ⟨m + 1, hmN⟩ le_rfl; dsimp only [inp] at *; omega) hall
          exact B₁.uses_assignOut_le hmN v' hnone₁
            (by have := B.uses_addMul_last v inp h0 hmid h1; dsimp only [B₁, v'] at *; omega) hall₁
  obtain ⟨g, B, v, _, _, hv_d, _, hcost, hv_out, hout_lt, _, _, hall⟩ := hloop N hN le_rfl
  obtain ⟨c, hint, huniv, hfan, hbc, hdepth_le, hout_d⟩ :=
    B.toCircuit_spec (D := N - 1)
      (fun j => by
        obtain ⟨w, hw_eq, hw_lo, hw_hi, hw_d⟩ := hout_lt j.val j.isLt
        exact ⟨w, hw_eq, hw_lo, hw_hi, by omega⟩) hall
  have hdepth_ge : N - 1 ≤ c.depth := by
    have := c.outputDepths_le_depth ⟨N - 1, by omega⟩
    rw [hout_d ⟨N - 1, by omega⟩ v hv_out, hv_d] at this
    exact this
  have hdepth : c.depth = N - 1 := le_antisymm hdepth_le hdepth_ge
  refine ⟨c, hint, ⟨huniv, ?_⟩, hfan, hdepth⟩
  rw [hbc, hcost, hdepth]
  omega

/-- Constructive existence of an optimal (zero-deficiency) fanout-`k` universal prefix circuit of
depth at most `D` for every width `1 ≤ N ≤ 1 + w_k*(D - 1)` when `k ≥ 2` and `D ≥ 1`
([Sergeev2025PrefixDepth], p. 3, Eq. (3)). -/
theorem exists_optimalPrefixCircuit_of_le_maxCircuitWidthUpper {N k D : ℕ}
    (hk : 2 ≤ k) (hD : 1 ≤ D) (hN : 1 ≤ N) (hN_ub : N ≤ 1 + maxCircuitWidthUpper k (D - 1)) :
    ∃ c : PrefixCircuit N, IsOptimalPrefixCircuit c ∧ FanoutAtMost c k ∧ c.depth ≤ D := by
  by_cases hND : N ≤ D
  · obtain ⟨c, _, hopt, hfan, hdepth⟩ := exists_rippleOptimalPrefixCircuit hk hN
    exact ⟨c, hopt, hfan, by omega⟩
  · have hDN : D + 1 ≤ N := by omega
    have hsum_eq : maxCircuitWidthUpper k (D - 1) =
        ∑ d ∈ Finset.range D, segmentWidth k d (D - 1 - d) := by
      unfold maxCircuitWidthUpper
      rw [show D - 1 + 1 = D by omega]
      exact Finset.sum_congr rfl fun d _ => maxConsistentWidth_eq_segmentWidth hk d (D - 1 - d)
    obtain ⟨w, hw_bd, hw_sum⟩ := exists_segmentWidths_of_le_sum D
      (fun d => segmentWidth k d (D - 1 - d)) (N - 1) hD
      (fun d _ => segmentWidth_pos k d (D - 1 - d)) (by omega) (by omega)
    let prefSum : ℕ → ℕ := fun r => 1 + ∑ d ∈ Finset.range r, w d
    have hpref_zero : prefSum 0 = 1 := rfl
    have hpref_succ : ∀ r, prefSum (r + 1) = prefSum r + w r := by
      intro r
      simp only [prefSum, Finset.sum_range_succ]
      omega
    have hpref_D : prefSum D = N := by
      simp only [prefSum, hw_sum]
      omega
    have hpref_le_N : ∀ r ≤ D, prefSum r ≤ N := by
      intro r hr
      have hsub : ∑ d ∈ Finset.range r, w d ≤ ∑ d ∈ Finset.range D, w d :=
        Finset.sum_le_sum_of_subset (Finset.range_mono hr)
      simp only [prefSum]
      omega
    have hpref_pos : ∀ r, 1 ≤ prefSum r := by intro r; simp only [prefSum]; omega
    have hpref_lb : ∀ r ≤ D, r ≤ prefSum r - 1 := by
      intro r hr
      have h_lb : r ≤ ∑ m ∈ Finset.range r, w m := by
        simpa only [Finset.card_range, smul_eq_mul, Nat.mul_one] using
          Finset.card_nsmul_le_sum (Finset.range r) w 1 fun m hm =>
            (hw_bd m (Nat.lt_of_lt_of_le (Finset.mem_range.mp hm) hr)).1
      simp only [prefSum]
      omega
    have hseg_loop : ∀ r : ℕ, r ≤ D →
        ∃ (g : ℕ) (B : PrefixBuilder N g) (v : Wire N g),
          B.lo v = 0 ∧ B.hi v = prefSum r ∧ B.program.wireDepths v = r ∧
          B.uses v = 0 ∧ B.mulCost = 2 * (prefSum r - 1) - r ∧
          (∀ j < prefSum r - 1, ∃ w_out, B.outs j = some w_out ∧ B.lo w_out = 0 ∧
            B.hi w_out = j + 1 ∧ B.program.wireDepths w_out ≤ D) ∧
          (∀ j, prefSum r - 1 ≤ j → B.outs j = none) ∧
          (∀ i : Fin N, prefSum r ≤ i.val → B.uses (.input i) = 0) ∧
          (∀ w' : Wire N g, B.uses w' ≤ k) := by
      intro r
      induction r with
      | zero =>
        intro _
        let B₀ := PrefixBuilder.empty N
        refine ⟨0, B₀, .input ⟨0, hN⟩, rfl, hpref_zero.symm, rfl, PrefixBuilder.uses_empty _, ?_,
          ?_, ?_, ?_, ?_⟩
        · rw [hpref_zero]; rfl
        · rw [hpref_zero]; intro j hj; omega
        · intro _ _; rfl
        · intro i _; exact PrefixBuilder.uses_empty (.input i)
        · intro w'; exact (PrefixBuilder.uses_empty w').trans_le (by omega)
      | succ d ih =>
        intro hdD
        have hd_lt : d < D := by omega
        have hd_lb : d ≤ prefSum d - 1 := hpref_lb d (by omega)
        have ha1_pre : 1 ≤ prefSum d := hpref_pos d
        have hbN_pre : prefSum (d + 1) ≤ N := hpref_le_N (d + 1) hdD
        have hab_pre : prefSum (d + 1) = prefSum d + w d := hpref_succ d
        obtain ⟨g, B, v, hv_lo, hv_hi, hv_d, hv_u, hcost, hout_lt, hout_ge, hin_ge, hall⟩ :=
          ih (by omega)
        obtain ⟨hw_pos, hw_ub⟩ := hw_bd d hd_lt
        set a := prefSum d
        set b := prefSum (d + 1)
        by_cases hw_one : w d = 1
        · have hnone : B.outs (a - 1) = none := hout_ge (a - 1) le_rfl
          let B₁ := B.assignOut (a - 1) v
          let u_d : Wire N g := .input ⟨a, by omega⟩
          have h0 : B₁.lo v < B₁.hi v := by dsimp only [B₁, PrefixBuilder.assignOut]; omega
          have hmid : B₁.hi v = B₁.lo u_d := by
            dsimp only [B₁, PrefixBuilder.assignOut]
            exact hv_hi.trans ((B.validInputs ⟨a, by omega⟩).1).symm
          have h1 : B₁.lo u_d < B₁.hi u_d := by
            dsimp only [B₁, PrefixBuilder.assignOut, u_d]
            rw [(B.validInputs ⟨a, by omega⟩).1, (B.validInputs ⟨a, by omega⟩).2]
            omega
          let B₂ := B₁.addMul v u_d h0 hmid h1
          let e₂ := B₁.addMulExt v u_d h0 hmid h1
          let v_next : Wire N (g + 1) := .gate (Fin.last g)
          have hv_ne_ud : v ≠ u_d := Ne.symm (B.input_ne_of_lo_ne (show B.lo v ≠ a by omega))
          refine ⟨g + 1, B₂, v_next, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp only [B₂, v_next, PrefixBuilder.addMul, liftWireVal_last, B₁,
              PrefixBuilder.assignOut, hv_lo]
          · simp only [B₂, v_next, PrefixBuilder.addMul, liftWireVal_last, B₁,
              PrefixBuilder.assignOut, u_d, (B.validInputs ⟨a, by omega⟩).2]
            omega
          · have hd_last := B₁.depth_addMul_last v u_d h0 hmid h1
            have hd_ud : B₁.program.wireDepths u_d = 0 := rfl
            dsimp only [B₂, v_next, B₁, PrefixBuilder.assignOut] at *; omega
          · exact B₁.uses_addMul_last v u_d h0 hmid h1
          · simp only [PrefixBuilder.mulCost, B₂, PrefixBuilder.addMul, Program.cost_gate, B₁,
              PrefixBuilder.assignOut]
            dsimp only [PrefixBuilder.mulCost] at hcost
            omega
          · intro j hj
            by_cases hjeq : j = a - 1
            · subst hjeq
              refine ⟨e₂.emb v, ?_, ?_, ?_, ?_⟩
              · simp only [B₂, PrefixBuilder.addMul, B₁, PrefixBuilder.assignOut, ↓reduceIte,
                  Option.map_some]; rfl
              · exact e₂.lo_emb v |>.trans hv_lo
              · rw [e₂.hi_emb v]
                dsimp only [B₁, PrefixBuilder.assignOut]
                omega
              · rw [e₂.depth_emb v]
                dsimp only [B₁, PrefixBuilder.assignOut]
                omega
            · obtain ⟨w_out, hw_eq, hw_lo, hw_hi, hw_d⟩ := hout_lt j (by omega)
              refine ⟨e₂.emb w_out, ?_, ?_, ?_, ?_⟩
              · simp only [B₂, PrefixBuilder.addMul, B₁, PrefixBuilder.assignOut, hjeq,
                  ↓reduceIte, hw_eq, Option.map_some]; rfl
              · exact e₂.lo_emb w_out |>.trans hw_lo
              · exact e₂.hi_emb w_out |>.trans hw_hi
              · rw [e₂.depth_emb w_out]
                dsimp only [B₁, PrefixBuilder.assignOut]
                omega
          · intro j hj
            have hj_ne : j ≠ a - 1 := by omega
            simp only [B₂, PrefixBuilder.addMul, B₁, PrefixBuilder.assignOut, hj_ne, ↓reduceIte,
              hout_ge j (by omega), Option.map_none]
          · intro i hi
            have hne_v : (Wire.input i : Wire N g) ≠ v := B.input_ne_of_lo_ne (by omega)
            have hne_ud : (Wire.input i : Wire N g) ≠ u_d :=
              mt Wire.input.inj (Fin.ne_of_val_ne (show i.val ≠ a by omega))
            exact (B₁.uses_addMul_ne v u_d h0 hmid h1 (.input i) hne_v hne_ud).trans
              ((B.uses_assignOut_ne (a - 1) v (.input i) hnone hne_v).trans (hin_ge i (by omega)))
          · have hall₁ : ∀ w' : Wire N g, B₁.uses w' ≤ k :=
              B.uses_assignOut_le (by omega) v hnone (by omega) hall
            exact B₁.uses_addMul_le v u_d h0 hmid h1
              (by have := B.uses_assignOut_self (by omega) v hnone; dsimp only [B₁] at *; omega)
              (by
                have := B.uses_assignOut_ne (a - 1) v u_d hnone hv_ne_ud.symm
                have := hin_ge ⟨a, by omega⟩ le_rfl
                dsimp only [B₁, u_d] at *; omega)
              hall₁
        · obtain ⟨t_raw, ht_in, ht_out, ht_fan⟩ :=
            exists_consistentTree_of_le_segmentWidth hk (D - 1 - d) a d (w d) hw_pos hw_ub
          let t : ConsistentTree a b := t_raw.castRight hab_pre.symm
          have ht_in' : t.inDepth ≤ d := by
            rw [ConsistentTree.inDepth_castRight]; exact ht_in
          have ht_out' : t.outDepth ≤ D - 1 - d := by
            rw [ConsistentTree.outDepth_castRight]; exact ht_out
          have ht_fan' : t.FanoutAtMost k := by
            rw [ConsistentTree.fanoutAtMost_castRight]; exact ht_fan
          let B₁ := B.addId v
          let e₁ := B.addIdExt v
          let v_buf : Wire N (g + 1) := .gate (Fin.last g)
          have hvb_lo : B₁.lo v_buf = 0 := by
            simp only [B₁, v_buf, PrefixBuilder.addId, liftWireVal_last, hv_lo]
          have hvb_hi : B₁.hi v_buf = a := by
            simp only [B₁, v_buf, PrefixBuilder.addId, liftWireVal_last, hv_hi]
          have hvb_d : B₁.program.wireDepths v_buf = d + 1 := by
            have := B.depth_addId_last v; dsimp only [B₁, v_buf] at *; omega
          have houts₁ : ∀ j, a - 1 ≤ j → j < b - 1 → B₁.outs j = none := by
            intro j hj1 _
            simp only [B₁, PrefixBuilder.addId, hout_ge j hj1, Option.map_none]
          have hin₁ : ∀ i : Fin N, a ≤ i.val → B₁.uses (.input i) = 0 := by
            intro i hi1
            have hne : (Wire.input i : Wire N g) ≠ v := B.input_ne_of_lo_ne (by omega)
            exact (B.uses_addId_ne v (.input i) hne).trans (hin_ge i hi1)
          have hall₁ : ∀ w' : Wire N (g + 1), B₁.uses w' ≤ k :=
            B.uses_addId_le v (by omega) hall
          obtain ⟨g₂, B₂, e₂, u_d, hud_lo, hud_hi, hud_d, hud_u, hcost₂, hout₂_in, hout₂_out,
              hold₂, hall₂⟩ :=
            compileTree_exists hk t B₁ v_buf ha1_pre hbN_pre ht_fan' hvb_lo hvb_hi
              (B.uses_addId_last v) (by omega) houts₁ (fun i hi1 _ => hin₁ i hi1) hall₁
          let v_in_B₂ := e₂.emb (e₁.emb v)
          have hv2_lo : B₂.lo v_in_B₂ = 0 := by rw [e₂.lo_emb, e₁.lo_emb, hv_lo]
          have hv2_hi : B₂.hi v_in_B₂ = a := by rw [e₂.hi_emb, e₁.hi_emb, hv_hi]
          have hv2_d : B₂.program.wireDepths v_in_B₂ = d := by rw [e₂.depth_emb, e₁.depth_emb, hv_d]
          have hv2_uses : B₂.uses v_in_B₂ = 1 := by
            have h1 : e₁.emb v ≠ v_buf := castSucc_ne_lastGate v
            have h2 : ∀ i : Fin N, a ≤ i.val → i.val < b → e₁.emb v ≠ .input i :=
              fun i hi1 _ => e₁.emb_ne_input_of_lo (by omega)
            have hstep := B.uses_addId_self v
            rw [hv_u] at hstep
            exact (hold₂ (e₁.emb v) h1 h2).2.trans hstep
          have h0 : B₂.lo v_in_B₂ < B₂.hi v_in_B₂ := by omega
          have hmid : B₂.hi v_in_B₂ = B₂.lo u_d := by omega
          have h1 : B₂.lo u_d < B₂.hi u_d := by omega
          let B₃ := B₂.addMul v_in_B₂ u_d h0 hmid h1
          let e₃ := B₂.addMulExt v_in_B₂ u_d h0 hmid h1
          let v_next : Wire N (g₂ + 1) := .gate (Fin.last g₂)
          refine ⟨g₂ + 1, B₃, v_next, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp only [B₃, v_next, PrefixBuilder.addMul, liftWireVal_last, hv2_lo]
          · simp only [B₃, v_next, PrefixBuilder.addMul, liftWireVal_last, hud_hi]
          · have := B₂.depth_addMul_last v_in_B₂ u_d h0 hmid h1
            dsimp only [B₃, v_next] at *; omega
          · exact B₂.uses_addMul_last v_in_B₂ u_d h0 hmid h1
          · have hc1 : B₁.mulCost = B.mulCost := by
              simp only [PrefixBuilder.mulCost, B₁, PrefixBuilder.addId, Program.cost_gate,
                Nat.add_zero]
            have hc3 : B₃.mulCost = B₂.mulCost + 1 := by
              simp only [PrefixBuilder.mulCost, B₃, PrefixBuilder.addMul, Program.cost_gate]
            omega
          · intro j hj
            by_cases hja : j < a - 1
            · obtain ⟨w_out, hw_eq, hw_lo, hw_hi, hw_d⟩ := hout_lt j hja
              have hw₂_eq : B₂.outs j = some (e₂.emb (e₁.emb w_out)) := by
                rw [hout₂_out j (Or.inl hja)]
                simp only [B₁, PrefixBuilder.addId, hw_eq, Option.map_some]; rfl
              refine ⟨e₃.emb (e₂.emb (e₁.emb w_out)), ?_, ?_, ?_, ?_⟩
              · simp only [B₃, PrefixBuilder.addMul, hw₂_eq, Option.map_some]; rfl
              · rw [e₃.lo_emb, e₂.lo_emb, e₁.lo_emb, hw_lo]
              · rw [e₃.hi_emb, e₂.hi_emb, e₁.hi_emb, hw_hi]
              · rw [e₃.depth_emb, e₂.depth_emb, e₁.depth_emb]; exact hw_d
            · obtain ⟨w₂, hw₂_eq, hw₂_lo, hw₂_hi, hw₂_d⟩ := hout₂_in j (by omega) hj
              refine ⟨e₃.emb w₂, ?_, ?_, ?_, ?_⟩
              · simp only [B₃, PrefixBuilder.addMul, hw₂_eq, Option.map_some]; rfl
              · rw [e₃.lo_emb, hw₂_lo]
              · rw [e₃.hi_emb, hw₂_hi]
              · rw [e₃.depth_emb]; omega
          · intro j hj
            simp only [B₃, PrefixBuilder.addMul]
            rw [hout₂_out j (Or.inr hj)]
            simp only [B₁, PrefixBuilder.addId, hout_ge j (by omega), Option.map_none]
          · intro i hi
            have hne_v : (Wire.input i : Wire N g₂) ≠ v_in_B₂ := B₂.input_ne_of_lo_ne (by omega)
            have hne_ud : (Wire.input i : Wire N g₂) ≠ u_d := B₂.input_ne_of_lo_ne (by omega)
            have hB₂_in : B₂.uses (.input i) = 0 := by
              have h1_in : e₁.emb (.input i) ≠ v_buf := castSucc_ne_lastGate (.input i)
              have h2_in : ∀ i' : Fin N, a ≤ i'.val → i'.val < b →
                  e₁.emb (.input i) ≠ .input i' :=
                fun i' _ hi'2 => e₁.emb_ne_input (mt Wire.input.inj (Fin.ne_of_val_ne (by omega)))
              have h_eq : e₂.emb (e₁.emb (.input i)) = .input i := by
                rw [e₁.emb_input, e₂.emb_input]
              rw [← h_eq]
              exact (hold₂ _ h1_in h2_in).2.trans (hin₁ i (by omega))
            exact (B₂.uses_addMul_ne v_in_B₂ u_d h0 hmid h1 (.input i) hne_v hne_ud).trans hB₂_in
          · exact B₂.uses_addMul_le v_in_B₂ u_d h0 hmid h1 (by omega) (by omega) hall₂
    obtain ⟨g, B, v_D, hv_lo, hv_hi, hv_d, hv_u, hcost, hout_lt, hout_ge, _, hall⟩ :=
      hseg_loop D le_rfl
    rw [hpref_D] at hv_hi hcost hout_lt hout_ge
    have hnone_last : B.outs (N - 1) = none := hout_ge (N - 1) le_rfl
    let B_fin := B.assignOut (N - 1) v_D
    have hall_fin : ∀ w' : Wire N g, B_fin.uses w' ≤ k :=
      B.uses_assignOut_le (by omega) v_D hnone_last (by omega) hall
    obtain ⟨c, _, huniv, hfan, hbc, hdepth_le, hout_d⟩ :=
      B_fin.toCircuit_spec (D := D)
        (fun j => by
          by_cases hjeq : j.val = N - 1
          · refine ⟨v_D, ?_, hv_lo, ?_, ?_⟩
            · simp only [B_fin, PrefixBuilder.assignOut, hjeq, ↓reduceIte]
            · dsimp only [B_fin, PrefixBuilder.assignOut]; omega
            · dsimp only [B_fin, PrefixBuilder.assignOut]; omega
          · obtain ⟨w_out, hw_eq, hw_lo, hw_hi, hw_d⟩ := hout_lt j.val (by omega)
            refine ⟨w_out, ?_, hw_lo, hw_hi, hw_d⟩
            simp only [B_fin, PrefixBuilder.assignOut, hjeq, ↓reduceIte, hw_eq])
        hall_fin
    have hdepth_ge : D ≤ c.depth := by
      have := c.outputDepths_le_depth ⟨N - 1, by omega⟩
      have hout_last : B_fin.outs (N - 1) = some v_D := by
        simp only [B_fin, PrefixBuilder.assignOut, ↓reduceIte]
      rw [hout_d ⟨N - 1, by omega⟩ v_D hout_last] at this
      dsimp only [B_fin, PrefixBuilder.assignOut] at this
      omega
    have hdepth : c.depth = D := le_antisymm hdepth_le hdepth_ge
    refine ⟨c, ⟨huniv, ?_⟩, hfan, hdepth.le⟩
    have hmul_fin : B_fin.mulCost = B.mulCost := rfl
    rw [hbc, hmul_fin, hcost, hdepth]
    omega

end Cslib.Circuits.Prefix
