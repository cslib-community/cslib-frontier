/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.AverageCase
public import CslibFrontier.Computability.Circuit.Frontier.Correlation
public import CslibFrontier.Computability.Circuit.Frontier.FanInTwo
public import CslibFrontier.Computability.Circuit.Frontier.Ledger.Sweep
public import CslibFrontier.Computability.Communication.QuadFormSignRank
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Components
import CslibFrontier.Computability.Circuit.Program
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpBounds
import CslibFrontier.Foundations.Combinatorics.Hoeffding
import CslibFrontier.Foundations.Data.BitString.Agree
import CslibFrontier.Foundations.Data.Set.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sum
import Mathlib.Order.Interval.Finset.Nat

/-!
# Frontier lower bounds for circuits with unbounded-weight threshold tops

The ledger extension of the frontier method (`Cslib.Circuits.Frontier.Ledger`) absorbs unbounded
fan-in gates that aggregate in a *finite* commutative monoid `M` with `log |M| = o(n)`. That
approach cannot handle an unbounded-fan-in *real-weighted linear threshold gate* (perceptron)
reading all `n + g` wires of a bounded-fan-in program with arbitrary real weights: irrational or
exponentially growing weights generate `2^{Θ(n)}` distinct partial sums, and fixing the values on a
frontier edge cut leaves a two-party halfspace (`Greater-Than`) rather than a monochromatic
combinatorial rectangle.

This module proves that the full `4.575972 n` median-switched Gaussian frontier lower bound
nevertheless holds for arbitrary-real-weight multi-perceptron tops (`ThresholdTop`) over bounded
fan-in programs (`THR ∘ THR_t ∘ Circuit`, or any Boolean combination `G` of `t` unbounded-weight
linear threshold units reading all inputs and internal gates):

1. **Order-rank compression of two-party halfspaces** (`card_isHalfspaceComb_le`). A two-party
   halfspace `decide (φ a + ψ b < 0)` on `α × β` is determined by the strict rank map
   `z ↦ #{w : α ⊕ β | g w < g z} < |α| + |β|` of `g = Sum.elim φ (-ψ)`. Consequently, across all
   unbounded real weights, at most `2^{2^t} (|α| + |β|)^{t (|α| + |β|)}` functions on `α × β` are
   Boolean combinations of `t` two-party halfspaces (`IsHalfspaceComb`).
2. **Existence of small-bias targets** (`exists_halfspaceCombBias`,
   `exists_halfspaceCombBias_family`). Union-bounding Hoeffding's inequality over spanned
   rectangles of sizes `k₁, k₂ ≥ K` shows that when `(2 (t + 1) (n + 1) : ℝ) ≤ b^2 K` and
   `2^t + 3 n + 2 ≤ 2 K`, sets `S ⊆ Bool^n` of bias at most `b` against every `t`-halfspace
   combination on `K × K`-large rectangles (`HalfspaceCombBias`) exist; for instance
   `K_n = 2 (t + 1) (n + 1)^3 + 2^t` and `b_n = 1 / (n + 1) → 0`.
3. **Realized-edge peeling on the unconstrained live network**
   (`eventually_agreement_thresholdTop_le_of_layoutBound`,
   `eventually_agreement_thresholdTop_le_switched`). Erasing no gates (`special := False`) turns a
   program `p` of fan-in at most two into `liveCircuit p`, whose constraint network accepts every
   input unambiguously (`accepted = univ`). On every state rectangle `peers τ x = rectangle X A B`,
   every wire of `p` depends on `X` alone or on `Xᶜ` alone, reducing `T.eval p I` on `A × B` to
   `IsHalfspaceComb t`. Bounding the realized edges at each step inside component `W` simultaneously
   by the frontier width and by `|readIn W|` eliminates disconnected-component blowup via the
   convex combination `min (A (s + 1 - n_W)) n_W ≤ (A / (1 + A)) (s + 1)`, yielding agreement at
   most `1/2 + b_n + exp (-γ n)` whenever `s ≤ (1 + 2π / (3 arccos (5/6)) - ε) n`.
4. **Single-cut sign-rank bound and Forster corollary** (`signRank_thresholdTop_le`,
   `eventually_lt_innerSize_thresholdTop_hardForm`). Across any single vertex cut `P` of the
   live network, integer order-ranks shifted by `1/2` factor a sign-representation of a single
   threshold unit (`t = 1`) through `2 |U|^{|edgeCut P|}` dimensions
   (`Communication.signRank_le_card_of_mul`), without topological perturbation. Paired with
   Forster's bilinear theorem (`Forster.lean`) and Lindsey's lemma on the nonconstructively chosen
   bilinear form `hardForm n`, every `THR ∘ B₂` circuit (including direct input skip-wires)
   computing `hardForm n` needs more than `(1 + π / (6 arccos (5/6)) - ε) n ≈ 1.893993 n` inner
   gates.

The frontier lower-bound extensions to arbitrary-real-weight threshold tops developed here —
combining order-rank compression on realized state rectangles with componentwise edge peeling, and
combining cut-wise shifted order-rank factorizations with Forster's theorem on graphs — are
original to this library.

## Main definitions

* `Cslib.Circuits.Frontier.IsHalfspaceComb`: Boolean combinations of `t` two-party real halfspaces.
* `Cslib.Circuits.Frontier.HalfspaceCombBias`: bounded signed discrepancy against every
  `t`-halfspace combination on rectangles with both sides of size at least `K`.
* `Cslib.Circuits.Frontier.ThresholdTop`, `Cslib.Circuits.Frontier.ThresholdTop.eval`: `t`
  arbitrary-real-weight threshold units over all wires of a program, with a Boolean combiner.

## Main results

* `Cslib.Circuits.Frontier.card_isHalfspaceComb_le`: upper bound on realizable `t`-halfspace
  combinations over finite domains.
* `Cslib.Circuits.Frontier.exists_halfspaceCombBias`,
  `Cslib.Circuits.Frontier.exists_halfspaceCombBias_family`: counting existence of low-bias sets.
* `Cslib.Circuits.Frontier.eventually_agreement_thresholdTop_le_of_layoutBound`,
  `Cslib.Circuits.Frontier.eventually_agreement_thresholdTop_le_switched`: average-case `4.575972 n`
  lower bound for `ThresholdTop` circuits.
* `Cslib.Circuits.Frontier.signRank_le_two_of_isHalfspaceComb_one`,
  `Cslib.Circuits.Frontier.signRank_thresholdTop_le`,
  `Cslib.Circuits.Frontier.eventually_lt_innerSize_thresholdTop_hardForm`: single-cut sign-rank
  bounds and `hardForm` lower bound via Forster's theorem.

## References

* [J. Forster, *A linear lower bound on the unbounded error probabilistic communication
  complexity*][Forster2002]
* [S. Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster
  Exponential Algorithms*][Gaspers2026]
* [A. A. Sherstov, P. Wu, *Near-Optimal Lower Bounds on the Threshold Degree and Sign-Rank of
  AC⁰*][SherstovWu2019]
-/

public section

namespace Cslib.Circuits.Frontier

open Set Filter Asymptotics Real
open scoped Finset Matrix

universe u v

/-! ### Two-party halfspace combinations and order-rank compression -/

/-- `f : α → β → Bool` is a Boolean combination of `t` two-party real halfspaces when there are
real potentials `φ r : α → ℝ` and `ψ r : β → ℝ` (`r : Fin t`) and a combiner
`G : (Fin t → Bool) → Bool` such that `f a b = G (fun r => decide (φ r a + ψ r b < 0))`. -/
@[expose]
def IsHalfspaceComb (t : ℕ) {α β : Type*} (f : α → β → Bool) : Prop :=
  ∃ (G : (Fin t → Bool) → Bool) (φ : Fin t → α → ℝ) (ψ : Fin t → β → ℝ),
    ∀ a b, f a b = G fun r => decide (φ r a + ψ r b < 0)

/-- `IsHalfspaceComb` is preserved under precomposition on both sides. -/
theorem IsHalfspaceComb.comp {t : ℕ} {α β α' β' : Type*} {f : α → β → Bool}
    (hf : IsHalfspaceComb t f) (ha : α' → α) (hb : β' → β) :
    IsHalfspaceComb t (fun a' b' => f (ha a') (hb b')) := by
  obtain ⟨G, φ, ψ, h⟩ := hf
  exact ⟨G, fun r a' => φ r (ha a'), fun r b' => ψ r (hb b'), fun a' b' => h (ha a') (hb b')⟩

/-- Negating the output preserves `IsHalfspaceComb`. -/
theorem IsHalfspaceComb.not {t : ℕ} {α β : Type*} {f : α → β → Bool}
    (hf : IsHalfspaceComb t f) : IsHalfspaceComb t (fun a b => !f a b) := by
  obtain ⟨G, φ, ψ, h⟩ := hf
  exact ⟨fun v => !G v, φ, ψ, fun a b => by dsimp only; rw [h]⟩

/-- Weak inequalities `decide (θ ≤ φ a + ψ b)` are `1`-halfspace combinations via negation. -/
theorem isHalfspaceComb_one_decide_le {α β : Type*} (φ : α → ℝ) (ψ : β → ℝ) (θ : ℝ) :
    IsHalfspaceComb 1 (fun a b => decide (θ ≤ φ a + ψ b)) := by
  refine ⟨fun v => !v 0, fun _ a => φ a - θ, fun _ b => ψ b, fun a b => ?_⟩
  by_cases h : φ a - θ + ψ b < 0
  · have h' : ¬(θ ≤ φ a + ψ b) := by linarith
    simp [h, h']
  · have h' : θ ≤ φ a + ψ b := by linarith
    simp [h, h']

/-- The strict rank `#{w | g w < g z}` of `z : α ⊕ β` under `g : α ⊕ β → ℝ`, valued in
`Fin (|α| + |β|)`. -/
private noncomputable def strictRank {α β : Type*} [Fintype α] [Fintype β]
    (g : α ⊕ β → ℝ) (z : α ⊕ β) : Fin (Fintype.card α + Fintype.card β) :=
  ⟨(Finset.univ.filter fun w => g w < g z).card, by
    have hlt : (Finset.univ.filter fun w => g w < g z).card <
        (Finset.univ : Finset (α ⊕ β)).card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.filter_subset _ _, fun h => by
          have hz : z ∈ (Finset.univ : Finset (α ⊕ β)) := Finset.mem_univ z
          rw [← h] at hz
          exact lt_irrefl (g z) (Finset.mem_filter.mp hz).2⟩)
    simpa only [Finset.card_univ, Fintype.card_sum] using hlt⟩

/-- Strict order on `g` coincides with strict order on `strictRank g`. -/
private theorem strictRank_lt_iff {α β : Type*} [Fintype α] [Fintype β]
    (g : α ⊕ β → ℝ) (x y : α ⊕ β) :
    strictRank g x < strictRank g y ↔ g x < g y := by
  rw [Fin.lt_def]
  dsimp only [strictRank]
  constructor
  · intro h
    by_contra hge
    have hyx : g y ≤ g x := not_lt.mp hge
    have hsub : (Finset.univ.filter fun w => g w < g y) ⊆
        (Finset.univ.filter fun w => g w < g x) := fun w hw => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      exact hw.trans_le hyx
    exact absurd (Finset.card_le_card hsub) (not_le.mpr h)
  · intro hxy
    refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨fun w hw => ?_, fun h => ?_⟩)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      exact hw.trans hxy
    · have hx : x ∈ Finset.univ.filter (fun w => g w < g y) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxy⟩
      rw [← h] at hx
      exact lt_irrefl (g x) (Finset.mem_filter.mp hx).2

/-- Strict ranks of `Sum.elim φ (-ψ)` compare across the two sides as the halfspace `φ a + ψ b < 0`.
-/
private theorem strictRank_inl_lt_inr_iff {α β : Type*} [Fintype α] [Fintype β]
    (φ : α → ℝ) (ψ : β → ℝ) (a : α) (b : β) :
    strictRank (Sum.elim φ (-ψ)) (.inl a) < strictRank (Sum.elim φ (-ψ)) (.inr b) ↔
      φ a + ψ b < 0 :=
  (strictRank_lt_iff _ _ _).trans lt_neg_iff_add_neg

/-- **Number of `t`-halfspace combinations on `α × β`.** Over finite types `α` and `β` with
`m = |α| + |β|`, at most `2 ^ (2 ^ t) * m ^ (t * m)` functions `α → β → Bool` belong to
`IsHalfspaceComb t`, independent of the real weights. -/
theorem card_isHalfspaceComb_le (t : ℕ) (α β : Type*) [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    [DecidablePred (IsHalfspaceComb t (α := α) (β := β))] :
    (Finset.univ.filter fun f : α → β → Bool => IsHalfspaceComb t f).card ≤
      2 ^ (2 ^ t) * (Fintype.card α + Fintype.card β) ^
        (t * (Fintype.card α + Fintype.card β)) := by
  classical
  set m := Fintype.card α + Fintype.card β
  let decode : ((Fin t → Bool) → Bool) × (Fin t → α ⊕ β → Fin m) → α → β → Bool :=
    fun p a b => p.1 fun r => decide (p.2 r (.inl a) < p.2 r (.inr b))
  have hsub : (Finset.univ.filter fun f : α → β → Bool => IsHalfspaceComb t f) ⊆
      Finset.univ.image decode := by
    intro f hf
    obtain ⟨G, φ, ψ, h⟩ := (Finset.mem_filter.mp hf).2
    refine Finset.mem_image.mpr ⟨(G, fun r => strictRank (Sum.elim (φ r) (-ψ r))),
      Finset.mem_univ _, funext fun a => funext fun b => ?_⟩
    dsimp only [decode]
    rw [h a b]
    congr 1 with r
    exact decide_eq_decide.mpr (strictRank_inl_lt_inr_iff _ _ _ _)
  calc (Finset.univ.filter fun f : α → β → Bool => IsHalfspaceComb t f).card
      ≤ (Finset.univ.image decode).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (((Fin t → Bool) → Bool) × (Fin t → α ⊕ β → Fin m))).card :=
        Finset.card_image_le
    _ = 2 ^ (2 ^ t) * m ^ (t * m) := by
        rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Fintype.card_fun,
          Fintype.card_fun, Fintype.card_fin, Fintype.card_sum, Fintype.card_fin, ← pow_mul]
        rw [mul_comm m t]

/-! ### Bias against `t`-halfspace combinations on large rectangles -/

/-- `S ⊆ (ι → U)` has *`t`-halfspace-combination bias* at most `b` above side threshold `K` when,
on every combinatorial rectangle `rectangle X A B` with `K ≤ |A|` and `K ≤ |B|`, every
`f : (X → U) → (↥Xᶜ → U) → Bool` satisfying `IsHalfspaceComb t f` agrees and disagrees with `S`
within `2 b |rectangle X A B|`. -/
@[expose]
def HalfspaceCombBias (t : ℕ) {ι U : Type*} (S : Set (ι → U)) (K : ℕ) (b : ℝ) : Prop :=
  ∀ (X : Set ι) (A : Set (X → U)) (B : Set (↥Xᶜ → U)),
    K ≤ A.ncard → K ≤ B.ncard →
    ∀ f : (X → U) → (↥Xᶜ → U) → Bool, IsHalfspaceComb t f →
      |signedCount {x | x ∈ S ↔ f (X.domRestrict x) (Xᶜ.domRestrict x) = true}
        (rectangle X A B)| ≤ 2 * b * (rectangle X A B).ncard

/-- `HalfspaceCombBias` is monotone in the side threshold `K`. -/
theorem HalfspaceCombBias.mono {t : ℕ} {ι U : Type*} {S : Set (ι → U)} {K K' : ℕ} {b : ℝ}
    (h : HalfspaceCombBias t S K b) (hK : K ≤ K') : HalfspaceCombBias t S K' b :=
  fun X A B hA hB f hf => h X A B (hK.trans hA) (hK.trans hB) f hf

/-- Every set has `HalfspaceCombBias` at most `1/2`. -/
theorem halfspaceCombBias_one_half (t : ℕ) {ι U : Type*} [Finite ι] [Finite U]
    (S : Set (ι → U)) (K : ℕ) : HalfspaceCombBias t S K (1 / 2) := by
  intro X A B _ _ f _
  have := abs_signedCount_le {x | x ∈ S ↔ f (X.domRestrict x) (Xᶜ.domRestrict x) = true}
    (rectangle X A B)
  linarith

/-- Nonnegativity of `b` once `K ≤ |U| ^ ⌊|ι| / 2⌋`: some rectangle has both sides of size `≥ K`. -/
private theorem HalfspaceCombBias.nonneg {t : ℕ} {ι U : Type*} [Finite ι] [Finite U] [Nonempty U]
    {S : Set (ι → U)} {K : ℕ} {b : ℝ} (hS : HalfspaceCombBias t S K b) (hKpos : 0 < K)
    (hK : K ≤ Nat.card U ^ (Nat.card ι / 2)) : 0 ≤ b := by
  classical
  have e := Finite.equivFin ι
  set X : Set ι := e ⁻¹' {i : Fin (Nat.card ι) | i.val < Nat.card ι / 2}
  have hX : X.ncard = Nat.card ι / 2 := by
    rw [ncard_preimage_of_injective_subset_range e.injective (by simp [e.surjective.range_eq])]
    have hsub : {i : Fin (Nat.card ι) | i.val < Nat.card ι / 2} =
        ((Finset.univ.filter fun i : Fin (Nat.card ι) => i.val < Nat.card ι / 2) : Set _) := by
      ext i; simp
    rw [hsub, ncard_coe_finset]
    rw [Fin.card_filter_val_lt, min_eq_right (Nat.div_le_self _ _)]
  have hXc : Xᶜ.ncard = Nat.card ι - Nat.card ι / 2 := by
    have := ncard_add_ncard_compl X
    omega
  have hA : K ≤ (univ : Set (X → U)).ncard := by
    rw [ncard_univ, Nat.card_fun, Nat.card_coe_set_eq, hX]
    exact hK
  have hB : K ≤ (univ : Set (↥Xᶜ → U)).ncard := by
    rw [ncard_univ, Nat.card_fun, Nat.card_coe_set_eq, hXc]
    exact hK.trans (Nat.pow_le_pow_right Nat.card_pos (by omega))
  have hf : IsHalfspaceComb t (fun (_ : X → U) (_ : ↥Xᶜ → U) => false) :=
    ⟨fun _ => false, fun _ _ => 0, fun _ _ => 0, fun _ _ => rfl⟩
  have h := hS X univ univ hA hB _ hf
  have hpos : (0 : ℝ) < (rectangle X (univ : Set (X → U)) univ).ncard := by
    rw [ncard_rectangle]
    have : 0 < (univ : Set (X → U)).ncard * (univ : Set (↥Xᶜ → U)).ncard :=
      Nat.mul_pos (lt_of_lt_of_le hKpos hA) (lt_of_lt_of_le hKpos hB)
    exact_mod_cast this
  nlinarith [abs_nonneg (signedCount {x | x ∈ S ↔ false = true} (rectangle X univ univ))]

/-- A signed count on `R` depends only on the counted set's trace on `R`. -/
private theorem signedCount_congr {ι U : Type*} {D D' R : Set (ι → U)}
    (h : ∀ x ∈ R, x ∈ D ↔ x ∈ D') : signedCount D R = signedCount D' R := by
  have h₁ : R ∩ D = R ∩ D' := Set.ext fun x => and_congr_right (h x)
  have h₂ : R \ D = R \ D' := Set.ext fun x => and_congr_right fun hx => not_congr (h x hx)
  rw [signedCount, signedCount, h₁, h₂]

section Witness

/-- For a fixed finite subset `R ⊆ (ι → Bool)` and fixed pattern `p : (ι → Bool) → Bool`,
Hoeffding's inequality bounds the number of `f : (ι → Bool) → Bool` whose agreement signed count on
`R` exceeds `2 b |R|`. -/
private theorem card_filter_lt_abs_signedCount_agree_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Set (ι → Bool)) (p : (ι → Bool) → Bool) {b : ℝ} (hb : 0 ≤ b) :
    (#(Finset.univ.filter fun f : (ι → Bool) → Bool =>
      2 * b * R.ncard < |signedCount {x | f x = p x} R|) : ℝ) ≤
        2 * 2 ^ Fintype.card (ι → Bool) * exp (-(2 * b ^ 2 * R.ncard)) := by
  classical
  set RF := R.toFinset
  have hR : R.ncard = RF.card := ncard_eq_toFinset_card' R
  let bij : ((ι → Bool) → Bool) ≃ ((ι → Bool) → Bool) :=
    { toFun := fun f x => !(xor (f x) (p x))
      invFun := fun g x => !(xor (g x) (p x))
      left_inv := fun f => funext fun x => by dsimp only; cases f x <;> cases p x <;> rfl
      right_inv := fun g => funext fun x => by dsimp only; cases g x <;> cases p x <;> rfl }
  have hsc (f : (ι → Bool) → Bool) :
      |signedCount {x | f x = p x} R| =
        2 * |((RF.filter fun x => bij f x = true).card : ℝ) - RF.card / 2| := by
    have h1 : (R ∩ {x | f x = p x}).ncard = (RF.filter fun x => bij f x = true).card := by
      rw [ncard_eq_toFinset_card']
      congr 1
      ext x
      simp only [RF, mem_toFinset, mem_inter_iff, mem_ofPred_eq, Finset.mem_filter, bij,
        Equiv.coe_fn_mk]
      cases f x <;> cases p x <;> simp
    have hpart : ((R ∩ {x | f x = p x}).ncard : ℝ) + (R \ {x | f x = p x}).ncard = RF.card := by
      rw [← hR]
      exact_mod_cast ncard_inter_add_ncard_sdiff_eq_ncard R {x | f x = p x}
    have hdef : signedCount {x | f x = p x} R =
        ((R ∩ {x | f x = p x}).ncard : ℝ) - (R \ {x | f x = p x}).ncard := rfl
    rw [hdef, show ((R ∩ {x | f x = p x}).ncard : ℝ) - (R \ {x | f x = p x}).ncard =
      2 * (((R ∩ {x | f x = p x}).ncard : ℝ) - RF.card / 2) by linarith, h1, abs_mul,
      abs_of_pos two_pos]
  have hcard_eq : (Finset.univ.filter fun f : (ι → Bool) → Bool =>
      2 * b * R.ncard < |signedCount {x | f x = p x} R|).card =
      (Finset.univ.filter fun g : (ι → Bool) → Bool =>
        b * RF.card < |((RF.filter fun x => g x = true).card : ℝ) - RF.card / 2|).card := by
    refine Finset.card_bij (fun f _ => bij f) (fun f hf => ?_)
      (fun f₁ _ f₂ _ h => bij.injective h) (fun g hg => ⟨bij.symm g, ?_, bij.apply_symm_apply g⟩)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
      rw [hsc, hR] at hf
      linarith
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      rw [hsc, bij.apply_symm_apply, hR]
      linarith
  rw [hcard_eq]
  calc (#(Finset.univ.filter fun g : (ι → Bool) → Bool =>
        b * RF.card < |((RF.filter fun x => g x = true).card : ℝ) - RF.card / 2|) : ℝ)
      ≤ #(Finset.univ.filter fun g : (ι → Bool) → Bool =>
          b * RF.card ≤ |((RF.filter fun x => g x = true).card : ℝ) - RF.card / 2|) := by
        exact_mod_cast Finset.card_le_card fun g hg => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
          exact hg.le
    _ ≤ 2 * 2 ^ Fintype.card (ι → Bool) * exp (-(2 * (b * RF.card) ^ 2 / RF.card)) :=
        BitString.card_filter_le_abs_card_filter_sub_half_le RF (by positivity)
    _ = 2 * 2 ^ Fintype.card (ι → Bool) * exp (-(2 * b ^ 2 * R.ncard)) := by
        rw [hR]
        rcases eq_or_ne (RF.card : ℝ) 0 with h0 | h0
        · simp [h0]
        · congr 3
          field_simp

/-- **Sets of small `t`-halfspace-combination bias exist.** Let `n = |ι|`, `b > 0`,
`(2 (t + 1) (n + 1) : ℝ) ≤ b ^ 2 * K`, and `(2 ^ t + 3 * n + 2 : ℝ) ≤ 2 * K`. Then some set
`S ⊆ (ι → Bool)` satisfies `HalfspaceCombBias t S K b`. -/
theorem exists_halfspaceCombBias {ι : Type*} [Fintype ι] (t K : ℕ) {b : ℝ} (hb : 0 < b)
    (hKb : (2 * (t + 1) * (Fintype.card ι + 1) : ℝ) ≤ b ^ 2 * K)
    (hKt : ((2 ^ t + 3 * Fintype.card ι + 2 : ℕ) : ℝ) ≤ 2 * K) :
    ∃ S : Set (ι → Bool), HalfspaceCombBias t S K b := by
  classical
  rcases le_or_gt (1 / 2) b with hb2 | hb2
  · refine ⟨∅, fun X A B hA hB f hf => ?_⟩
    have h0 := halfspaceCombBias_one_half t (∅ : Set (ι → Bool)) K X A B hA hB f hf
    exact h0.trans (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _))
  set n := Fintype.card ι
  set N := Fintype.card (ι → Bool)
  have hN : N = 2 ^ n := by simp [N, n]
  have hKpos : 0 < K :=
    (Nat.cast_pos (α := ℝ)).mp
      (by linarith [show (0 : ℝ) < ((2 ^ t + 3 * n + 2 : ℕ) : ℝ) by positivity])
  let WType (k₁ k₂ : ℕ) :=
    Set ι × (Fin k₁ → ι → Bool) × (Fin k₂ → ι → Bool) ×
      ((Fin t → Bool) → Bool) × (Fin t → Fin k₁ ⊕ Fin k₂ → Fin (k₁ + k₂))
  let rectOf (k₁ k₂ : ℕ) (w : WType k₁ k₂) : Set (ι → Bool) :=
    rectangle w.1 (range fun i => w.1.domRestrict (w.2.1 i))
      (range fun j => w.1ᶜ.domRestrict (w.2.2.1 j))
  let patOf (k₁ k₂ : ℕ) (w : WType k₁ k₂) (z : ι → Bool) : Bool :=
    if hi : ∃ i : Fin k₁, w.1.domRestrict (w.2.1 i) = w.1.domRestrict z then
      if hj : ∃ j : Fin k₂, w.1ᶜ.domRestrict (w.2.2.1 j) = w.1ᶜ.domRestrict z then
        w.2.2.2.1 fun r => decide (w.2.2.2.2 r (.inl (Classical.choose hi)) <
          w.2.2.2.2 r (.inr (Classical.choose hj)))
      else false
    else false
  let E (k₁ k₂ : ℕ) (w : WType k₁ k₂) : Finset ((ι → Bool) → Bool) :=
    Finset.univ.filter fun f => (rectOf k₁ k₂ w).ncard = k₁ * k₂ ∧
      2 * b * (rectOf k₁ k₂ w).ncard <
        |signedCount {z | (f z = true) ↔ (patOf k₁ k₂ w z = true)} (rectOf k₁ k₂ w)|
  have hE (k₁ k₂ : ℕ) (w : WType k₁ k₂) :
      (#(E k₁ k₂ w) : ℝ) ≤ 2 * 2 ^ N * exp (-(2 * b ^ 2 * (k₁ * k₂ : ℕ))) := by
    by_cases hw : (rectOf k₁ k₂ w).ncard = k₁ * k₂
    · rw [← hw]
      have hsub : E k₁ k₂ w ⊆ Finset.univ.filter fun f : (ι → Bool) → Bool =>
          2 * b * (rectOf k₁ k₂ w).ncard <
            |signedCount {z | f z = patOf k₁ k₂ w z} (rectOf k₁ k₂ w)| := by
        intro f hf
        simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
        have heq : {z : ι → Bool | (f z = true) ↔ (patOf k₁ k₂ w z = true)} =
            {z | f z = patOf k₁ k₂ w z} := Set.ext fun _ => Bool.coe_iff_coe
        exact heq ▸ hf.2
      exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
        (card_filter_lt_abs_signedCount_agree_le (rectOf k₁ k₂ w) (patOf k₁ k₂ w) hb.le)
    · have h0 : E k₁ k₂ w = ∅ := by
        ext f
        simp [E, hw]
      rw [h0, Finset.card_empty, Nat.cast_zero]
      positivity
  set bad : Finset ((ι → Bool) → Bool) :=
    Finset.univ.filter fun f => ¬HalfspaceCombBias t {z | f z = true} K b
  have hbad : bad ⊆ (Finset.Icc K N).biUnion fun k₁ => (Finset.Icc K N).biUnion fun k₂ =>
      Finset.univ.biUnion (E k₁ k₂) := by
    intro f hf
    simp only [bad, HalfspaceCombBias, Finset.mem_filter, Finset.mem_univ, true_and,
      not_forall, not_le] at hf
    obtain ⟨X, A, B, hA, hB, hcomb, ⟨G, φ, ψ, hG⟩, hbias⟩ := hf
    set k₁ := A.ncard
    set k₂ := B.ncard
    let eA : Fin k₁ ≃ A :=
      (Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq])).symm
    let eB : Fin k₂ ≃ B :=
      (Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq])).symm
    let a : Fin k₁ → X → Bool := fun i => (eA i).1
    let c : Fin k₂ → ↥Xᶜ → Bool := fun j => (eB j).1
    have ha_inj : Function.Injective a := Subtype.val_injective.comp eA.injective
    have hc_inj : Function.Injective c := Subtype.val_injective.comp eB.injective
    have ha_eq : range a = A := by
      rw [show a = Subtype.val ∘ eA from rfl, eA.surjective.range_comp, Subtype.range_coe]
    have hc_eq : range c = B := by
      rw [show c = Subtype.val ∘ eB from rfl, eB.surjective.range_comp, Subtype.range_coe]
    let x (i : Fin k₁) : ι → Bool :=
      (Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool).symm (a i, fun _ => false)
    let y (j : Fin k₂) : ι → Bool :=
      (Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool).symm (fun _ => false, c j)
    have hx (i : Fin k₁) : X.domRestrict (x i) = a i :=
      congrArg Prod.fst ((Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool).apply_symm_apply _)
    have hy (j : Fin k₂) : Xᶜ.domRestrict (y j) = c j :=
      congrArg Prod.snd ((Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool).apply_symm_apply _)
    have hxa : (fun i => X.domRestrict (x i)) = a := funext hx
    have hyc : (fun j => Xᶜ.domRestrict (y j)) = c := funext hy
    have hrect_ncard : (rectangle X A B).ncard = k₁ * k₂ := ncard_rectangle X A B
    have hRN : k₁ * k₂ ≤ N :=
      hrect_ncard ▸ (ncard_le_card _).trans_eq Nat.card_eq_fintype_card
    have hk₁N : k₁ ≤ N := (Nat.le_mul_of_pos_right _ (by omega)).trans hRN
    have hk₂N : k₂ ≤ N := (Nat.le_mul_of_pos_left _ (by omega)).trans hRN
    let rk : Fin t → Fin k₁ ⊕ Fin k₂ → Fin (k₁ + k₂) := fun r =>
      Sum.rec (fun i => (strictRank (Sum.elim (fun i' => φ r (a i')) (-fun j' => ψ r (c j')))
        (.inl i)).cast (by simp [Fintype.card_fin]))
        (fun j => (strictRank (Sum.elim (fun i' => φ r (a i')) (-fun j' => ψ r (c j')))
        (.inr j)).cast (by simp [Fintype.card_fin]))
    let w : WType k₁ k₂ := (X, x, y, G, rk)
    have hw_rect : rectOf k₁ k₂ w = rectangle X A B := by
      dsimp only [rectOf, w]
      rw [hxa, hyc, ha_eq, hc_eq]
    refine Finset.mem_biUnion.mpr ⟨k₁, Finset.mem_Icc.mpr ⟨hA, hk₁N⟩,
      Finset.mem_biUnion.mpr ⟨k₂, Finset.mem_Icc.mpr ⟨hB, hk₂N⟩,
        Finset.mem_biUnion.mpr ⟨w, Finset.mem_univ w, ?_⟩⟩⟩
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and, hw_rect, hrect_ncard, true_and]
    have hpat_eq : ∀ z ∈ rectangle X A B,
        patOf k₁ k₂ w z = hcomb (X.domRestrict z) (Xᶜ.domRestrict z) := by
      intro z hz
      rcases hz with ⟨hzA, hzB⟩
      rw [← ha_eq] at hzA
      rw [← hc_eq] at hzB
      obtain ⟨i, hi⟩ := hzA
      obtain ⟨j, hj⟩ := hzB
      have hi' : ∃ i', X.domRestrict (x i') = X.domRestrict z := ⟨i, (hx i).trans hi⟩
      have hj' : ∃ j', Xᶜ.domRestrict (y j') = Xᶜ.domRestrict z := ⟨j, (hy j).trans hj⟩
      simp only [patOf, w, hi', hj', ↓reduceDIte]
      have hi_eq : Classical.choose hi' = i := ha_inj
        (((hx (Classical.choose hi')).symm.trans (Classical.choose_spec hi')).trans hi.symm)
      have hj_eq : Classical.choose hj' = j := hc_inj
        (((hy (Classical.choose hj')).symm.trans (Classical.choose_spec hj')).trans hj.symm)
      rw [hi_eq, hj_eq, ← hi, ← hj, hG (a i) (c j)]
      congr 1 with r
      dsimp only [rk]
      exact decide_eq_decide.mpr (by
        rw [Fin.lt_def, Fin.val_cast, Fin.val_cast, ← Fin.lt_def, strictRank_inl_lt_inr_iff])
    rw [← hrect_ncard]
    exact hbias.trans_eq (congrArg abs (signedCount_congr fun z hz => by
      simp only [mem_ofPred_eq, hpat_eq z hz]))
  have hterm (k₁ k₂ : ℕ) (hk₁ : K ≤ k₁) (hk₂ : K ≤ k₂) (hk₁N : k₁ ≤ N) (hk₂N : k₂ ≤ N) :
      ∑ w : WType k₁ k₂, (#(E k₁ k₂ w) : ℝ) ≤
        2 ^ (2 ^ t + n + 1) * 2 ^ N * exp (-(2 * K)) := by
    have hk₁' : (K : ℝ) ≤ k₁ := by exact_mod_cast hk₁
    have hk₂' : (K : ℝ) ≤ k₂ := by exact_mod_cast hk₂
    have hsum_le : k₁ + k₂ ≤ 2 ^ (n + 1) := by
      rw [pow_succ', ← hN]
      omega
    have hWcard : (Fintype.card (WType k₁ k₂) : ℝ) ≤
        2 ^ (2 ^ t + n) * 2 ^ ((t + 1) * (n + 1) * (k₁ + k₂)) := by
      have hcard_nat : Fintype.card (WType k₁ k₂) ≤
          2 ^ (2 ^ t + n) * 2 ^ ((t + 1) * (n + 1) * (k₁ + k₂)) := by
        simp only [WType, Fintype.card_prod, Fintype.card_set, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, Fintype.card_sum]
        calc 2 ^ n * ((2 ^ n) ^ k₁ * ((2 ^ n) ^ k₂ * (2 ^ 2 ^ t * ((k₁ + k₂) ^ (k₁ + k₂)) ^ t)))
            ≤ 2 ^ n * ((2 ^ (n + 1)) ^ k₁ * ((2 ^ (n + 1)) ^ k₂ *
                (2 ^ 2 ^ t * ((2 ^ (n + 1)) ^ (k₁ + k₂)) ^ t))) := by
              gcongr <;> omega
          _ = 2 ^ (2 ^ t + n) * 2 ^ ((t + 1) * (n + 1) * (k₁ + k₂)) := by
              simp only [← pow_mul, ← pow_add]
              congr 1
              ring
      exact_mod_cast hcard_nat
    have hexp : (2 : ℝ) ^ ((t + 1) * (n + 1) * (k₁ + k₂)) *
        exp (-(2 * b ^ 2 * (k₁ * k₂ : ℕ))) ≤ exp (-(2 * K)) := by
      refine (mul_le_mul_of_nonneg_right (two_pow_le_exp _) (exp_pos _).le).trans ?_
      rw [← exp_add, exp_le_exp]
      push_cast
      have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
      have htn1 : (1 : ℝ) ≤ ((t : ℝ) + 1) * ((n : ℝ) + 1) := by
        nlinarith [Nat.cast_nonneg (α := ℝ) t, Nat.cast_nonneg (α := ℝ) n]
      -- `(t + 1) (n + 1) (k₁ + k₂) ≤ b² k₁ k₂` and `2 K ≤ 2 (t + 1) (n + 1) K ≤ b² K² ≤ b² k₁ k₂`.
      linarith [mul_le_mul_of_nonneg_right hKb (by positivity : (0 : ℝ) ≤ k₁ + k₂),
        mul_le_mul_of_nonneg_right hKb hK0, mul_le_mul_of_nonneg_right htn1 hK0,
        mul_le_mul_of_nonneg_left hk₂' (by positivity : (0 : ℝ) ≤ b ^ 2 * k₁),
        mul_le_mul_of_nonneg_left hk₁' (by positivity : (0 : ℝ) ≤ b ^ 2 * k₂),
        mul_le_mul_of_nonneg_left (mul_le_mul hk₁' hk₂' hK0 (Nat.cast_nonneg k₁)) (sq_nonneg b)]
    calc ∑ w : WType k₁ k₂, (#(E k₁ k₂ w) : ℝ)
        ≤ ∑ _w : WType k₁ k₂, 2 * 2 ^ N * exp (-(2 * b ^ 2 * (k₁ * k₂ : ℕ))) :=
          Finset.sum_le_sum fun w _ => hE k₁ k₂ w
      _ = (Fintype.card (WType k₁ k₂) : ℝ) *
            (2 * 2 ^ N * exp (-(2 * b ^ 2 * (k₁ * k₂ : ℕ)))) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ (2 ^ (2 ^ t + n) * 2 ^ ((t + 1) * (n + 1) * (k₁ + k₂))) *
            (2 * 2 ^ N * exp (-(2 * b ^ 2 * (k₁ * k₂ : ℕ)))) := by gcongr
      _ = 2 ^ (2 ^ t + n + 1) * 2 ^ N *
            ((2 : ℝ) ^ ((t + 1) * (n + 1) * (k₁ + k₂)) * exp (-(2 * b ^ 2 * (k₁ * k₂ : ℕ)))) := by
          rw [pow_succ]
          ring
      _ ≤ 2 ^ (2 ^ t + n + 1) * 2 ^ N * exp (-(2 * K)) := by gcongr
  have hcount : (#bad : ℝ) < 2 ^ N := by
    have hIcc : #(Finset.Icc K N) ≤ N := by
      rw [Nat.card_Icc]
      omega
    calc (#bad : ℝ)
        ≤ ∑ k₁ ∈ Finset.Icc K N, ∑ k₂ ∈ Finset.Icc K N, ∑ w : WType k₁ k₂, (#(E k₁ k₂ w) : ℝ) := by
          refine le_trans (Nat.cast_le.mpr ((Finset.card_le_card hbad).trans
            (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun k₁ _ =>
              Finset.card_biUnion_le.trans (Finset.sum_le_sum fun k₂ _ =>
                Finset.card_biUnion_le))))) ?_
          push_cast
          rfl
      _ ≤ ∑ _k₁ ∈ Finset.Icc K N, ∑ _k₂ ∈ Finset.Icc K N,
            2 ^ (2 ^ t + n + 1) * 2 ^ N * exp (-(2 * K)) :=
          Finset.sum_le_sum fun k₁ hk₁ => Finset.sum_le_sum fun k₂ hk₂ =>
            hterm k₁ k₂ (Finset.mem_Icc.mp hk₁).1 (Finset.mem_Icc.mp hk₂).1
              (Finset.mem_Icc.mp hk₁).2 (Finset.mem_Icc.mp hk₂).2
      _ ≤ N * N * (2 ^ (2 ^ t + n + 1) * 2 ^ N * exp (-(2 * K))) := by
          simp only [Finset.sum_const, nsmul_eq_mul, ← mul_assoc]
          have : (#(Finset.Icc K N) : ℝ) ≤ N := by exact_mod_cast hIcc
          gcongr
      _ = (2 : ℝ) ^ (2 ^ t + 3 * n + 1) * exp (-(2 * K)) * 2 ^ N := by
          rw [hN]; push_cast; ring
      _ < 2 ^ N := by
          refine mul_lt_of_lt_one_left (by positivity) ?_
          refine (mul_le_mul_of_nonneg_right (two_pow_le_exp _) (exp_pos _).le).trans_lt ?_
          rw [← exp_add, exp_lt_one_iff]
          push_cast at hKt ⊢
          linarith
  by_contra! hall
  have huniv : bad = Finset.univ := Finset.eq_univ_of_forall fun f => by simp [bad, hall]
  rw [huniv, Finset.card_univ, Fintype.card_fun, Fintype.card_bool] at hcount
  push_cast at hcount
  exact lt_irrefl _ hcount

/-- **Families meeting `HalfspaceCombBias` with bias tending to zero.** For any fixed `t : ℕ`,
there is a family `S_n ⊆ Bool^n` (selected nonconstructively via `Classical.choose` from the
counting witness `exists_halfspaceCombBias`) with
`HalfspaceCombBias t (S n) (2 (t + 1) (n + 1)^3 + 2^t) (1 / (n + 1))`, `log K_n = o(n)`, and
`b_n → 0`. -/
theorem exists_halfspaceCombBias_family (t : ℕ) :
    ∃ S : ∀ n, Set (Fin n → Bool),
      (∀ᶠ n in atTop,
        HalfspaceCombBias t (S n) (2 * (t + 1) * (n + 1) ^ 3 + 2 ^ t) (1 / ((n : ℝ) + 1))) ∧
      (fun n : ℕ => Real.log (((2 * (t + 1) * (n + 1) ^ 3 + 2 ^ t : ℕ) : ℝ))) =o[atTop]
        (fun n => (n : ℝ)) ∧
      Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) := by
  have hKb (n : ℕ) :
      (2 * (t + 1) * (Fintype.card (Fin n) + 1) : ℝ) ≤
        (1 / ((n : ℝ) + 1)) ^ 2 * ((2 * (t + 1) * (n + 1) ^ 3 + 2 ^ t : ℕ) : ℝ) := by
    rw [Fintype.card_fin]
    have hsub : 2 * (t + 1) * (n + 1) ^ 3 ≤ 2 * (t + 1) * (n + 1) ^ 3 + 2 ^ t :=
      Nat.le_add_right _ _
    calc (2 * (t + 1) * (n + 1) : ℝ)
        = (1 / ((n : ℝ) + 1)) ^ 2 * (((2 * (t + 1) * (n + 1) ^ 3 : ℕ) : ℝ)) := by
          push_cast; field_simp
      _ ≤ (1 / ((n : ℝ) + 1)) ^ 2 * ((2 * (t + 1) * (n + 1) ^ 3 + 2 ^ t : ℕ) : ℝ) := by
          gcongr
  have hKt (n : ℕ) :
      ((2 ^ t + 3 * Fintype.card (Fin n) + 2 : ℕ) : ℝ) ≤
        2 * ((2 * (t + 1) * (n + 1) ^ 3 + 2 ^ t : ℕ) : ℝ) := by
    rw [Fintype.card_fin]
    have hnat : 2 ^ t + 3 * n + 2 ≤ 2 * (2 * (t + 1) * (n + 1) ^ 3 + 2 ^ t) := by
      have h1 : 1 ≤ 2 * (t + 1) := by omega
      have h2 : 3 * n + 2 ≤ 2 * (1 * (n + 1) ^ 3) := by
        have : (n + 1) ^ 3 = n ^ 3 + 3 * n ^ 2 + 3 * n + 1 := by ring
        omega
      have h3 : 2 * (1 * (n + 1) ^ 3) ≤ 2 * (2 * (t + 1) * (n + 1) ^ 3) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ h1)
      have h4 : 2 ^ t ≤ 2 * 2 ^ t := Nat.le_mul_of_pos_left _ two_pos
      omega
    exact_mod_cast hnat
  choose S hS using fun n : ℕ =>
    exists_halfspaceCombBias (ι := Fin n) t (2 * (t + 1) * (n + 1) ^ 3 + 2 ^ t) (by positivity)
      (hKb n) (hKt n)
  refine ⟨S, Eventually.of_forall hS, ?_, tendsto_one_div_add_atTop_nhds_zero_nat⟩
  set C : ℝ := ((2 * (t + 1) + 2 ^ t : ℕ) : ℝ)
  have hC1 : 1 ≤ C := by
    simp only [C]
    exact_mod_cast Nat.le_add_right_of_le (by omega : 1 ≤ 2 * (t + 1))
  have hlog1 := isLittleO_log_affine (α := (1 : ℝ)) (β := 1) zero_le_one le_rfl
  refine IsBigO.trans_isLittleO
    (g := fun n : ℕ => Real.log C + 3 * Real.log (1 * (n : ℝ) + 1)) ?_
    ((isLittleO_const_id_atTop (Real.log C)).natCast_atTop.add (hlog1.const_mul_left 3))
  refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
  have hk_ge : (1 : ℝ) ≤ ((2 * (t + 1) * (n + 1) ^ 3 + 2 ^ t : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_pos_right (2 * (t + 1) * (n + 1) ^ 3) (Nat.pow_pos two_pos)
  have hk_le : ((2 * (t + 1) * (n + 1) ^ 3 + 2 ^ t : ℕ) : ℝ) ≤ C * ((n : ℝ) + 1) ^ 3 := by
    have hp : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 :=
      one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have h2t_nn : (0 : ℝ) ≤ (2 : ℝ) ^ t := by positivity
    have hC_eq : C = (2 * ((t : ℝ) + 1)) + (2 : ℝ) ^ t := by simp only [C]; push_cast; ring
    rw [hC_eq]
    push_cast
    nlinarith
  simp only [one_mul, Real.norm_eq_abs]
  rw [abs_of_nonneg (Real.log_nonneg hk_ge),
    abs_of_nonneg (add_nonneg (Real.log_nonneg hC1)
      (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n]))))]
  calc Real.log (((2 * (t + 1) * (n + 1) ^ 3 + 2 ^ t : ℕ) : ℝ))
      ≤ Real.log (C * ((n : ℝ) + 1) ^ 3) := Real.log_le_log (by positivity) hk_le
    _ = Real.log C + 3 * Real.log ((n : ℝ) + 1) := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
        ring

end Witness

/-! ### Unbounded-real-weight threshold tops over bounded-fan-in programs -/

/-- A *threshold top* of `t` unbounded-real-weight linear threshold units reading all `n + g`
wires of a program `p : Program σ n g`, combined by `combine : (Fin t → Bool) → Bool`. -/
structure ThresholdTop (U : Type u) (n g t : ℕ) where
  /-- Real contribution `weight r w u` when wire `w` carries value `u : U`. -/
  weight : Fin t → Wire n g → U → ℝ
  /-- Additive real bias of threshold unit `r`. -/
  bias : Fin t → ℝ
  /-- Outer Boolean combiner of the `t` threshold units. -/
  combine : (Fin t → Bool) → Bool

namespace ThresholdTop

/-- Evaluate `T` on the wire trace of `p` under interpretation `I` and input `x`. -/
@[expose]
noncomputable def eval {σ : Signature.{v}} {U : Type u} {n g t : ℕ}
    (T : ThresholdTop U n g t) (p : Program σ n g) (I : Interpretation σ U)
    (x : Fin n → U) : Bool :=
  T.combine fun r => decide (T.bias r + ∑ w : Wire n g, T.weight r w (p.trace I x w) < 0)

end ThresholdTop

/-! ### Live-network wire splicing and realized-edge peeling -/

section LivePeeling

private def unitLedger {σ : Signature.{v}} {U : Type u} {n g : ℕ}
    (p : Program σ n g) (I : Interpretation σ U) :
    Ledger (fun _ : Fin g => False) p I Unit where
  contribution _ _ := ()
  readout _ h := h.2.elim
  readout_prod _ h := h.2.elim

private theorem unitLedger_run_eq_trace {σ : Signature.{v}} {U : Type u} {n g : ℕ}
    (p : Program σ n g) (I : Interpretation σ U) (x : Fin n → U) :
    (unitLedger p I).run () x = p.trace I x :=
  (unitLedger p I).run_eq_trace rfl

open Classical in
/-- On any subset of inputs `R ⊆ univ` all sharing the same edge-cut transcript on `edgeCut P`,
`T.eval p I` restricts to a `t`-halfspace combination across `(readIn P, (readIn P)ᶜ)`. -/
private theorem exists_isHalfspaceComb_on_cut {σ : Signature.{v}} {U : Type u}
    {n g t : ℕ} (T : ThresholdTop U n g t) (p : Program σ n g) (I : Interpretation σ U)
    (P : Set (Compiler.Vertex (liveCircuit p (fun _ => False))))
    (τ : Compiler.Edge (liveCircuit p (fun _ => False)) → Option U) :
    ∃ f : ((liveNetwork p (fun _ => False) U).readIn P → U) →
        (↥((liveNetwork p (fun _ => False) U).readIn P)ᶜ → U) → Bool,
      IsHalfspaceComb t f ∧
      ∀ z : Fin n → U,
        (fun e => if e ∈ (liveNetwork p (fun _ => False) U).edgeCut P then
          some (p.trace I z e.signal.1) else none) = τ →
          T.eval p I z = f (((liveNetwork p (fun _ => False) U).readIn P).domRestrict z)
            (((liveNetwork p (fun _ => False) U).readIn P)ᶜ.domRestrict z) := by
  set X := (liveNetwork p (fun _ => False) U).readIn P
  set Ecut := (liveNetwork p (fun _ => False) U).edgeCut P
  let matchesCut (x : Fin n → U) : Prop :=
    (fun e => if e ∈ Ecut then some (p.trace I x e.signal.1) else none) = τ
  let φ : Fin t → (X → U) → ℝ := fun r a =>
    if ha : ∃ x : Fin n → U, matchesCut x ∧ X.domRestrict x = a then
      T.bias r + ∑ w ∈ Finset.univ.filter (· ∈ wiresIn P),
        T.weight r w (p.trace I (Classical.choose ha) w)
    else 0
  let ψ : Fin t → (↥Xᶜ → U) → ℝ := fun r b =>
    if hb : ∃ y : Fin n → U, matchesCut y ∧ Xᶜ.domRestrict y = b then
      ∑ w ∈ Finset.univ.filter (· ∉ wiresIn P),
        T.weight r w (p.trace I (Classical.choose hb) w)
    else 0
  refine ⟨fun a b => T.combine fun r => decide (φ r a + ψ r b < 0),
    ⟨T.combine, φ, ψ, fun _ _ => rfl⟩, fun z hz => ?_⟩
  have ha : ∃ x : Fin n → U, matchesCut x ∧ X.domRestrict x = X.domRestrict z := ⟨z, hz, rfl⟩
  have hb : ∃ y : Fin n → U, matchesCut y ∧ Xᶜ.domRestrict y = Xᶜ.domRestrict z := ⟨z, hz, rfl⟩
  obtain ⟨hax_cut, hax_dom⟩ := Classical.choose_spec ha
  obtain ⟨hby_cut, hby_dom⟩ := Classical.choose_spec hb
  set x₀ := Classical.choose ha
  set y₀ := Classical.choose hb
  have hcut_xy : EqOn (fun e => p.trace I x₀ e.signal.1) (fun e => p.trace I y₀ e.signal.1) Ecut :=
    fun e he => by
      have h1 := congrFun hax_cut e
      have h2 := congrFun hby_cut e
      simp only [he, ↓reduceIte] at h1 h2
      exact Option.some_injective _ (h1.trans h2.symm)
  have hzx : EqOn z x₀ X := domRestrict_eq_domRestrict_iff.mp hax_dom.symm
  have hzy : EqOn z y₀ Xᶜ := domRestrict_eq_domRestrict_iff.mp hby_dom.symm
  have hsplit := (unitLedger p I).trace_of_splice (x := x₀) (y := y₀) rfl rfl hcut_xy hzx hzy
  dsimp only [ThresholdTop.eval]
  congr 1 with r
  have hsum_eq : T.bias r + ∑ w : Wire n g, T.weight r w (p.trace I z w) =
      φ r (X.domRestrict z) + ψ r (Xᶜ.domRestrict z) := by
    simp only [φ, ψ, ha, hb, ↓reduceDIte]
    have hpart := (Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Wire n g)))
      (p := (· ∈ wiresIn P)) (f := fun w => T.weight r w (p.trace I z w))).symm
    rw [hpart]
    have h1 : ∑ w ∈ Finset.univ.filter (· ∈ wiresIn P), T.weight r w (p.trace I z w) =
        ∑ w ∈ Finset.univ.filter (· ∈ wiresIn P), T.weight r w (p.trace I x₀ w) :=
      Finset.sum_congr rfl fun w hw => by rw [(hsplit w).1 (Finset.mem_filter.mp hw).2]
    have h2 : ∑ w ∈ Finset.univ.filter (· ∉ wiresIn P), T.weight r w (p.trace I z w) =
        ∑ w ∈ Finset.univ.filter (· ∉ wiresIn P), T.weight r w (p.trace I y₀ w) :=
      Finset.sum_congr rfl fun w hw => by rw [(hsplit w).2 (Finset.mem_filter.mp hw).2]
    rw [h1, h2, add_assoc]
  rw [hsum_eq]

/-- The *realized edge count* of a read-once branching program: the sum across steps of the
number of edges traversed by chosen accepting paths of accepted inputs. -/
private noncomputable def realizedSize {ι U M : Type*} (B : ReadOnceNBP ι U M) : ℕ :=
  ∑ s ∈ Finset.range B.length, (B.edgeOf s '' B.accepted).ncard

private theorem transitionCount_le_realizedSize {ι U M : Type*} [Finite ι] [Finite U]
    (B : ReadOnceNBP ι U M) : B.sweep.transitionCount ≤ realizedSize B := by
  refine Finset.sum_le_sum fun t _ => ?_
  exact ncard_image_le_ncard_image_of_factorsThrough (toFinite _) fun x _ y _ h => by
    simp only [ReadOnceNBP.edgeOf, Prod.mk.injEq] at h
    exact Prod.ext h.1 (Prod.ext h.2.2 h.2.1)

private theorem one_le_realizedSize {ι U M : Type*} [Finite ι] [Finite U]
    {B : ReadOnceNBP ι U M} (hL : 0 < B.length) (hne : B.accepted.Nonempty) :
    1 ≤ realizedSize B := by
  obtain ⟨x, hx⟩ := hne
  have h0 : 1 ≤ (B.edgeOf 0 '' B.accepted).ncard :=
    (ncard_pos (toFinite _)).mpr ⟨B.edgeOf 0 x, x, hx, rfl⟩
  exact h0.trans (Finset.single_le_sum (f := fun s => (B.edgeOf s '' B.accepted).ncard)
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hL))

private theorem ncard_accepted_le_mul_realizedSize {ι U M : Type*} [Finite ι] [Finite U]
    {B : ReadOnceNBP ι U M} (hL : 0 < B.length) {K : ℕ} (hS : B.SmallSides K) :
    B.accepted.ncard ≤ (K - 1) ^ 2 * realizedSize B := by
  rcases B.accepted.eq_empty_or_nonempty with h | hne
  · simp [h]
  have hK1 := hS.one_lt hne
  by_cases hK : K ≤ B.accepted.ncard
  · calc B.accepted.ncard ≤ (K - 1) * (K - 1) * B.sweep.transitionCount :=
          B.sweep.ncard_le_mul_transitionCount hK1 hK fun t ht x hx =>
            (hS t ht x hx).imp
              (fun h => (encard_lt_coe_iff_finite_ncard_lt.mp h).2)
              (fun h => (encard_lt_coe_iff_finite_ncard_lt.mp h).2)
      _ ≤ (K - 1) ^ 2 * realizedSize B := by
          rw [sq]
          exact Nat.mul_le_mul_left _ (transitionCount_le_realizedSize B)
  · calc B.accepted.ncard ≤ K - 1 := by omega
      _ ≤ (K - 1) ^ 2 * 1 := by
          rw [sq, mul_one]
          exact Nat.le_mul_of_pos_left _ (by omega)
      _ ≤ (K - 1) ^ 2 * realizedSize B :=
          Nat.mul_le_mul_left _ (one_le_realizedSize hL hne)

private theorem realizedSize_eraseNode_le {ι U M : Type*} [Finite ι] [Finite U]
    {B : ReadOnceNBP ι U M} (hB : B.Unambiguous) (hL : 0 < B.length) {t : ℕ} (ht : t ≤ B.length)
    (m : M) : realizedSize (B.eraseNode t m) ≤ realizedSize B := by
  refine Finset.sum_le_sum fun s hs => ?_
  have hs' : s < B.length := Finset.mem_range.mp hs
  refine ncard_le_ncard ?_ ((toFinite B.accepted).image _)
  rintro _ ⟨x, hx, rfl⟩
  have hpath := ((B.isAcceptingPath_eraseNode_iff hL ht).mp
    ((B.eraseNode t m).isAcceptingPath_path hx)).1
  have hxB : x ∈ B.accepted := ⟨_, hpath⟩
  have eq_s := hB x _ _ hpath (B.isAcceptingPath_path hxB) s (by omega)
  have eq_s1 := hB x _ _ hpath (B.isAcceptingPath_path hxB) (s + 1) (by omega)
  exact ⟨x, hxB, Prod.ext eq_s.symm (Prod.ext rfl eq_s1.symm)⟩

/-- Peeling with `realizedSize` when `D` has bounded signed count on every `K × K`-large state
rectangle of a root unambiguous program `B₀`. -/
private theorem abs_signedCount_le_of_root_peers {ι U M : Type*} [Finite ι] [Finite U]
    {B₀ B : ReadOnceNBP ι U M} (hB : B.Unambiguous) (hLen : B.length = B₀.length)
    (hRev : B.revealed = B₀.revealed) (hL : 0 < B.length)
    (hsub : ∀ x ∈ B.accepted, x ∈ B₀.accepted ∧ ∀ s ≤ B₀.length, B.path x s = B₀.path x s)
    (D : Set (ι → U)) {K : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (hpeer : ∀ s ≤ B₀.length, ∀ x ∈ B₀.accepted,
      ∀ (A : Set (B₀.revealed s → U)) (C : Set (↥(B₀.revealed s)ᶜ → U)),
        K ≤ A.ncard → K ≤ C.ncard → rectangle (B₀.revealed s) A C ⊆ B₀.sweep.peers s x →
          |signedCount D (rectangle (B₀.revealed s) A C)| ≤
            2 * b * (rectangle (B₀.revealed s) A C).ncard) :
    |signedCount D B.accepted| ≤
      2 * b * B.accepted.ncard + ((K - 1) ^ 2 * realizedSize B : ℕ) := by
  induction hn : B.accepted.ncard using Nat.strong_induction_on generalizing B with
  | ind k ih =>
    subst hn
    by_cases hthick : ∃ s ≤ B.length, ∃ x ∈ B.accepted,
        K ≤ (B.sweep.pastSide s x).ncard ∧ K ≤ (B.sweep.futureSide s x).ncard
    · obtain ⟨s, hs, x, hx, hA, hC⟩ := hthick
      have hR : B.sweep.peers s x ⊆ B.accepted := fun _ hy => hy.1
      have hacc : (B.eraseNode s (B.path x s)).accepted = B.accepted \ B.sweep.peers s x := by
        rw [B.accepted_eraseNode hB hL hs]
        ext y
        simp only [mem_ofPred_eq, Set.mem_sdiff]
        change y ∈ B.accepted ∧ B.path y s ≠ B.path x s ↔
          y ∈ B.accepted ∧ ¬(y ∈ B.accepted ∧ B.path y s = B.path x s)
        tauto
      have hcard := ncard_sdiff_add_ncard_of_subset hR
      have hpos : 0 < (B.sweep.peers s x).ncard := (ncard_pos (toFinite _)).mpr ⟨x, hx, rfl⟩
      have hB' : (B.eraseNode s (B.path x s)).Unambiguous :=
        fun y γ δ hγ hδ u hu =>
          hB y γ δ ((B.isAcceptingPath_eraseNode_iff hL hs).mp hγ).1
            ((B.isAcceptingPath_eraseNode_iff hL hs).mp hδ).1 u hu
      have hsub' : ∀ y ∈ (B.eraseNode s (B.path x s)).accepted,
          y ∈ B₀.accepted ∧ ∀ u ≤ B₀.length,
            (B.eraseNode s (B.path x s)).path y u = B₀.path y u := by
        intro y hy
        have hpy := ((B.isAcceptingPath_eraseNode_iff hL hs).mp
          ((B.eraseNode s (B.path x s)).isAcceptingPath_path hy)).1
        have hyB : y ∈ B.accepted := ⟨_, hpy⟩
        refine ⟨(hsub y hyB).1, fun u hu => ?_⟩
        rw [hB y _ _ hpy (B.isAcceptingPath_path hyB) u (hLen ▸ hu)]
        exact (hsub y hyB).2 u hu
      have hrest := ih _ (by rw [hacc]; omega) hB' hLen hRev hL hsub' rfl
      rw [hacc] at hrest
      have hrect : |signedCount D (B.sweep.peers s x)| ≤ 2 * b * (B.sweep.peers s x).ncard := by
        rw [hB.peers_eq_rectangle hs x]
        have hs0 : s ≤ B₀.length := hLen ▸ hs
        have hpeers_sub : B.sweep.peers s x ⊆ B₀.sweep.peers s x := by
          intro y hy
          refine ⟨(hsub y hy.1).1, ?_⟩
          change B₀.path y s = B₀.path x s
          rw [← (hsub y hy.1).2 s hs0, ← (hsub x hx).2 s hs0]
          exact hy.2
        rw [hB.peers_eq_rectangle hs x] at hpeers_sub
        have htr {X₁ : Set ι} (heq : X₁ = B₀.revealed s)
            (A₁ : Set (X₁ → U)) (C₁ : Set (↥X₁ᶜ → U))
            (hA₁ : K ≤ A₁.ncard) (hC₁ : K ≤ C₁.ncard)
            (hsub₁ : rectangle X₁ A₁ C₁ ⊆ B₀.sweep.peers s x) :
            |signedCount D (rectangle X₁ A₁ C₁)| ≤ 2 * b * (rectangle X₁ A₁ C₁).ncard := by
          subst heq
          exact hpeer s hs0 x (hsub x hx).1 A₁ C₁ hA₁ hC₁ hsub₁
        exact htr (congrFun hRev s) _ _ hA hC hpeers_sub
      have hsize : (((K - 1) ^ 2 * realizedSize (B.eraseNode s (B.path x s)) : ℕ) : ℝ) ≤
          ((K - 1) ^ 2 * realizedSize B : ℕ) := by
        exact_mod_cast Nat.mul_le_mul_left _ (realizedSize_eraseNode_le hB hL hs (B.path x s))
      have hcardR : ((B.accepted \ B.sweep.peers s x).ncard : ℝ) + (B.sweep.peers s x).ncard =
          B.accepted.ncard := by exact_mod_cast hcard
      rw [signedCount_eq_add_sdiff D hR, ← hcardR]
      linarith [abs_add_le (signedCount D (B.sweep.peers s x))
        (signedCount D (B.accepted \ B.sweep.peers s x))]
    · push Not at hthick
      have hsmall : B.SmallSides K := fun s hs x hx => by
        by_cases hA : K ≤ (B.sweep.pastSide s x).ncard
        · exact Or.inr (encard_lt_coe_iff_finite_ncard_lt.mpr
            ⟨toFinite _, hthick s hs x hx hA⟩)
        · exact Or.inl (encard_lt_coe_iff_finite_ncard_lt.mpr ⟨toFinite _, not_le.mp hA⟩)
      have hcount : (B.accepted.ncard : ℝ) ≤ ((K - 1) ^ 2 * realizedSize B : ℕ) := by
        exact_mod_cast ncard_accepted_le_mul_realizedSize hL hsmall
      linarith [abs_signedCount_le D B.accepted,
        mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * b) (Nat.cast_nonneg (α := ℝ) B.accepted.ncard)]

/-- At step `s < |V|` of a componentwise layout of `liveNetwork p (fun _ => False) U`, the number
of realized edges is bounded both by `|U| ^ (|frontier s| + 4)` (for fan-in `≤ 2`) and by
`|U| ^ |readIn W|`, where `W` is the component of the vertex processed at step `s`. -/
private theorem ncard_realizedEdge_le_min {σ : Signature.{v}} {U : Type u} [Finite U] [Nonempty U]
    {n g : ℕ} (p : Program σ n g) (I : Interpretation σ U)
    (hfan : (liveCircuit p (fun _ => False)).FanInAtMost 2)
    (lay : Layout (Compiler.Vertex (liveCircuit p (fun _ => False))))
    {s : ℕ} (hs : s < Nat.card (Compiler.Vertex (liveCircuit p (fun _ => False))))
    (hcomp : (liveNetwork p (fun _ => False) U).frontier lay s ∪
        (liveNetwork p (fun _ => False) U).frontier lay (s + 1) ⊆
      (liveNetwork p (fun _ => False) U).touching
        ((liveNetwork p (fun _ => False) U).component (lay.symm ⟨s, hs⟩))) :
    ((((unitLedger p I).network ()).branchingProgram lay).edgeOf s ''
        (((unitLedger p I).network ()).branchingProgram lay).accepted).ncard ≤
      min (Nat.card U ^ (((liveNetwork p (fun _ => False) U).frontier lay s).ncard + 4))
        (Nat.card U ^
          ((liveNetwork p (fun _ => False) U).readIn
            ((liveNetwork p (fun _ => False) U).component (lay.symm ⟨s, hs⟩))).ncard) := by
  set L := unitLedger p I
  set B₀ := (L.network ()).branchingProgram lay
  set W := (liveNetwork p (fun _ => False) U).component (lay.symm ⟨s, hs⟩)
  have hq : 1 ≤ Nat.card U := Nat.card_pos
  refine le_min ?_ ?_
  · -- Width bound: realized edges are a subset of `B₀.edges s`.
    have hsub : B₀.edgeOf s '' B₀.accepted ⊆ B₀.edges s := by
      rintro _ ⟨x, hx, rfl⟩
      exact B₀.edgeOf_mem_edges hx (Nat.lt_succ_of_lt hs)
    have hF : ((L.network ()).frontier lay s ∪ (L.network ()).frontier lay (s + 1)).ncard +
        ((L.network ()).readAt (lay.symm ⟨s, hs⟩)).ncard ≤
          ((liveNetwork p (fun _ => False) U).frontier lay s).ncard + 4 := by
      have hU : ((L.network ()).frontier lay s ∪ (L.network ()).frontier lay (s + 1)).ncard ≤
          ((L.network ()).frontier lay s).ncard + 3 :=
        (ncard_le_ncard
          (union_subset subset_union_left ((L.network ()).frontier_succ_subset lay hs))
          (toFinite _)).trans ((ncard_union_le _ _).trans
            (Nat.add_le_add_left (Compiler.maxDegreeLE le_rfl hfan _) _))
      have hR : ((L.network ()).readAt (lay.symm ⟨s, hs⟩)).ncard ≤ 1 :=
        Compiler.ncard_readAt_le _ _ _
      have hf_eq : ((L.network ()).frontier lay s).ncard =
          ((liveNetwork p (fun _ => False) U).frontier lay s).ncard := rfl
      omega
    exact (ncard_le_ncard hsub (toFinite _)).trans
      (((L.network ()).ncard_edges_le lay hs).trans (Nat.pow_le_pow_right hq hF))
  · -- Component input bound: inside closed `W`, frontiers and `newly s` depend only on `readIn W`.
    have hW_closed : (liveNetwork p (fun _ => False) U).edgeCut W = ∅ :=
      (liveNetwork p (fun _ => False) U).edgeCut_component _
    have hnewly_sub : B₀.newly s ⊆ (liveNetwork p (fun _ => False) U).readIn W := by
      have h1 := (L.network ()).revealedBy_succ_diff_subset lay hs
      intro i hi
      have hi' : i ∈ (L.network ()).readAt (lay.symm ⟨s, hs⟩) := h1 hi
      exact ⟨lay.symm ⟨s, hs⟩, (liveNetwork p (fun _ => False) U).mem_component_self _, hi'⟩
    have hpath_eq (x : Fin n → U) (hx : x ∈ B₀.accepted) (hr : ℕ)
        (hhr : hr ≤ Nat.card (Compiler.Vertex (liveCircuit p (fun _ => False)))) :
        B₀.path x hr = (L.network ()).frontierValues lay hr (fun e => p.trace I x e.signal.1) := by
      obtain ⟨α, hα, hfv⟩ := (L.network ()).exists_satisfies_of_isAcceptingPath lay
        (B₀.isAcceptingPath_path hx)
      rw [hfv hr (Nat.le_succ_of_le hhr), Network.frontierValues_eq_iff]
      intro e _
      have h : α e = L.run () x e.signal.1 := Compiler.eq_trace hα e
      rwa [unitLedger_run_eq_trace] at h
    calc (B₀.edgeOf s '' B₀.accepted).ncard
        ≤ (((liveNetwork p (fun _ => False) U).readIn W).domRestrict '' B₀.accepted).ncard := by
          refine ncard_image_le_ncard_image_of_factorsThrough (toFinite _) fun x hx y hy hxy => ?_
          have hxx' : EqOn x y ((liveNetwork p (fun _ => False) U).readIn W) :=
            domRestrict_eq_domRestrict_iff.mp hxy
          have hrun_eq {e : Compiler.Edge (liveCircuit p (fun _ => False))}
              (he : e ∈ (liveNetwork p (fun _ => False) U).touching W) :
              p.trace I x e.signal.1 = p.trace I y e.signal.1 := by
            have h := L.run_eq_of_eqOn_readIn () hW_closed hxx' he
            rwa [unitLedger_run_eq_trace, unitLedger_run_eq_trace] at h
          refine Prod.ext ?_ (Prod.ext ?_ ?_)
          · dsimp only [ReadOnceNBP.edgeOf]
            rw [hpath_eq x hx s hs.le, hpath_eq y hy s hs.le, Network.frontierValues_eq_iff]
            exact fun e he => hrun_eq (hcomp (Or.inl he))
          · exact domRestrict_eq_domRestrict_iff.mpr (hxx'.mono hnewly_sub)
          · dsimp only [ReadOnceNBP.edgeOf]
            rw [hpath_eq x hx (s + 1) hs, hpath_eq y hy (s + 1) hs, Network.frontierValues_eq_iff]
            exact fun e he => hrun_eq (hcomp (Or.inr he))
      _ ≤ Nat.card (((liveNetwork p (fun _ => False) U).readIn W) → U) := ncard_le_card _
      _ = Nat.card U ^ ((liveNetwork p (fun _ => False) U).readIn W).ncard := by
          rw [Nat.card_fun, Nat.card_coe_set_eq]

private theorem step_exponent_le {A ε₀ C : ℝ} (hA : 0 < A) (hε₀ : 0 < ε₀)
    {n se V f_s ρW nW : ℕ}
    (hsize : (se : ℝ) ≤ (1 + 1 / A - ε₀) * n)
    (hV_le : V ≤ 7 * se + 3 * n)
    (hf : (f_s : ℝ) ≤ (A + (A * ε₀ / (8 * ((1 + 1 / A) + 10 * (2 + 1 / A))))) * ρW +
      (A * ε₀ / (8 * ((1 + 1 / A) + 10 * (2 + 1 / A)))) * V + C)
    (hρ : (ρW : ℝ) + nW ≤ se + 1) :
    min ((f_s : ℝ) + 4) (nW : ℝ) ≤
      (1 - 3 * (A * ε₀ / (4 * (1 + A)))) * n +
        (|C| + A + (A * ε₀ / (8 * ((1 + 1 / A) + 10 * (2 + 1 / A)))) + 5) := by
  set Bcoef : ℝ := (1 + 1 / A) + 10 * (2 + 1 / A)
  have hBcoef : 0 < Bcoef := by positivity
  set η : ℝ := A * ε₀ / (8 * Bcoef)
  have hη : 0 < η := by positivity
  set μ : ℝ := A * ε₀ / (4 * (1 + A))
  have hu : (f_s : ℝ) + 4 ≤ (A + η) * (se + 1 - nW) + η * V + C + 4 := by
    have := mul_le_mul_of_nonneg_left (show (ρW : ℝ) ≤ se + 1 - nW by linarith)
      (by positivity : (0 : ℝ) ≤ A + η)
    linarith
  have hw1 : 0 ≤ 1 / (1 + A) := by positivity
  have hw2 : 0 ≤ A / (1 + A) := by positivity
  have hsum1 : 1 / (1 + A) + A / (1 + A) = 1 := by field_simp
  have m1 := mul_le_mul_of_nonneg_left ((min_le_left ((f_s : ℝ) + 4) nW).trans hu) hw1
  have m2 := mul_le_mul_of_nonneg_left (min_le_right ((f_s : ℝ) + 4) nW) hw2
  have hconv : min ((f_s : ℝ) + 4) (nW : ℝ) ≤
      1 / (1 + A) * ((A + η) * (se + 1 - nW) + η * V + C + 4) + A / (1 + A) * nW := by
    linarith [show 1 / (1 + A) * min ((f_s : ℝ) + 4) nW + A / (1 + A) * min ((f_s : ℝ) + 4) nW =
      min ((f_s : ℝ) + 4) nW by rw [← add_mul, hsum1, one_mul]]
  have h1 : 1 / (1 + A) * ((A + η) * (se + 1 - nW) + η * V + C + 4) + A / (1 + A) * nW =
      A / (1 + A) * se + 1 / (1 + A) * (η * (se - nW) + η * V + A + η + C + 4) := by
    field_simp; ring
  have hAse : A / (1 + A) * se ≤ (1 - 4 * μ) * n := by
    have hse' : A * se ≤ (1 + A - A * ε₀) * n := by
      have := mul_le_mul_of_nonneg_left hsize hA.le
      have heq : A * ((1 + 1 / A - ε₀) * n) = (1 + A - A * ε₀) * n := by field_simp; ring
      linarith
    have hdiv : A * se / (1 + A) ≤ (1 + A - A * ε₀) * n / (1 + A) := by gcongr
    have hmu_eq : (1 + A - A * ε₀) * n / (1 + A) = (1 - 4 * μ) * n := by
      simp only [μ]; field_simp
    linarith [show A / (1 + A) * se = A * se / (1 + A) by ring]
  have hη_term : 1 / (1 + A) * (η * (se - nW) + η * V) ≤ μ * n := by
    have hnW0 : (0 : ℝ) ≤ nW := Nat.cast_nonneg _
    have hse_b : (se : ℝ) ≤ (1 + 1 / A) * n := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hV_r : (V : ℝ) ≤ 7 * se + 3 * n := by exact_mod_cast hV_le
    have hV_b : (V : ℝ) ≤ 10 * (2 + 1 / A) * n := by
      nlinarith [Nat.cast_nonneg (α := ℝ) n, div_pos one_pos hA]
    have hnum : η * (se - nW) + η * V ≤ η * Bcoef * n := by
      simp only [Bcoef]
      nlinarith
    have hηB : η * Bcoef = A * ε₀ / 8 := by simp only [η]; field_simp
    rw [hηB] at hnum
    have hdiv2 : 1 / (1 + A) * (A * ε₀ / 8 * n) ≤ μ * n := by
      simp only [μ]
      have : (0 : ℝ) ≤ A * ε₀ / (8 * (1 + A)) * n := by positivity
      linarith [show 1 / (1 + A) * (A * ε₀ / 8 * n) = A * ε₀ / (8 * (1 + A)) * n by field_simp,
        show A * ε₀ / (4 * (1 + A)) * n = 2 * (A * ε₀ / (8 * (1 + A)) * n) by field_simp; ring]
    exact (mul_le_mul_of_nonneg_left hnum (by positivity)).trans hdiv2
  have hconst_le : 1 / (1 + A) * (A + η + C + 4) ≤ |C| + A + η + 5 := by
    have h1A : 1 / (1 + A) ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
    have hc_abs := le_abs_self C
    have hpos_sum : 0 ≤ A + η + |C| + 4 := by positivity
    calc 1 / (1 + A) * (A + η + C + 4)
        ≤ 1 / (1 + A) * (A + η + |C| + 4) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ 1 * (A + η + |C| + 4) := mul_le_mul_of_nonneg_right h1A hpos_sum
      _ ≤ |C| + A + η + 5 := by linarith
  linarith

/-- **Average-case lower bound for `ThresholdTop` under `LayoutBound 3 A`.** Fix `A > 0` with
`LayoutBound 3 A`. For every `ε > 0` there is `γ > 0` such that for every finite nontrivial
alphabet `U`, every `t : ℕ → ℕ`, `K : ℕ → ℕ` with `log K_n = o(n)`, `b : ℕ → ℝ`, and `S_n ⊆ U^n`
eventually satisfying `HalfspaceCombBias (t n) (S n) (K n) (b n)`, for all large `n`, every
program `p : Program σ n g` of fan-in at most `2` with `(p.innerGates.card : ℝ) ≤ (1 + 1/A - ε) n`
and every `T : ThresholdTop U n g (t n)` (with arbitrary unbounded real weights!) has
`agreement (S n) {x | T.eval p I x = true} ≤ 1 / 2 + b n + exp (-γ n)`. -/
theorem eventually_agreement_thresholdTop_le_of_layoutBound {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound 3 A) {ε : ℝ} (hε : 0 < ε) :
    ∃ γ > 0, ∀ (U : Type u) [Finite U] [Nontrivial U] (t K : ℕ → ℕ) (b : ℕ → ℝ)
      (S : ∀ n, Set (Fin n → U)),
      (∀ᶠ n in atTop, HalfspaceCombBias (t n) (S n) (K n) (b n)) →
      (fun n => Real.log (K n)) =o[atTop] (fun n => (n : ℝ)) →
      ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (g : ℕ)
        (p : Program σ n g) (T : ThresholdTop U n g (t n)),
        p.FanInAtMost 2 → (p.innerGates.card : ℝ) ≤ (1 + 1 / A - ε) * n →
          agreement (S n) {x | T.eval p I x = true} ≤ 1 / 2 + b n + Real.exp (-(γ * n)) := by
  set ε₀ := min ε (1 / 2)
  have hε₀ : 0 < ε₀ := lt_min hε (by norm_num)
  set μ := A * ε₀ / (4 * (1 + A))
  have hμ : 0 < μ := by positivity
  have hμ_le : μ ≤ 1 / 8 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [min_le_right ε (1 / 2 : ℝ)]
  refine ⟨μ * Real.log 2, by positivity, ?_⟩
  intro U _ _ t K b S hbias hK
  set q := Nat.card U
  have hq1 : 1 < q := Finite.one_lt_card
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq1
  have hlogq : 0 < Real.log q := Real.log_pos (by linarith)
  have hlq2 : Real.log 2 ≤ Real.log q := Real.log_le_log two_pos hq2
  set K' : ℕ → ℕ := fun n => max (K n) 2
  have hlogbK : (fun n => Real.logb q (K' n)) =o[atTop] fun n => (n : ℝ) :=
    isLittleO_logb_max_two hK q
  set Bcoef : ℝ := (1 + 1 / A) + 10 * (2 + 1 / A)
  have hBcoef : 0 < Bcoef := by positivity
  set η : ℝ := A * ε₀ / (8 * Bcoef)
  have hη : 0 < η := by positivity
  obtain ⟨C, hC⟩ := hlayout.exists_layout_componentwise hη
  have hlog_aff := isLittleO_log_affine (α := 10 * (2 + 1 / A)) (β := 11) (by positivity)
    (by norm_num)
  set κ : ℝ := 4 + 1 / Real.log 2
  have hκ_pos : 0 < κ := by simp only [κ]; positivity
  have hsmall_err : ∀ᶠ n : ℕ in atTop,
      2 * Real.logb q (K' n) + κ * Real.log (10 * (2 + 1 / A) * n + 11) + (|C| + A + η + 6) ≤
        μ * n := by
    have herr : (fun n : ℕ => 2 * Real.logb q (K' n) +
        κ * Real.log (10 * (2 + 1 / A) * n + 11) + (|C| + A + η + 6)) =o[atTop]
          fun n => (n : ℝ) :=
      ((hlogbK.const_mul_left 2).add (hlog_aff.const_mul_left κ)).add
        (isLittleO_const_id_atTop _).natCast_atTop
    filter_upwards [herr.bound hμ] with n hn
    simp only [Real.norm_eq_abs, Nat.abs_cast] at hn
    linarith [le_abs_self (2 * Real.logb q (K' n) +
      κ * Real.log (10 * (2 + 1 / A) * n + 11) + (|C| + A + η + 6))]
  have hsmallK : ∀ᶠ n : ℕ in atTop, K' n ≤ q ^ (n / 2) := by
    filter_upwards [((isLittleO_const_id_atTop (1 : ℝ)).natCast_atTop.add
      (hlogbK.const_mul_left 2)).bound (by norm_num : (0 : ℝ) < 1 / 2)] with n hn
    simp only [Real.norm_eq_abs, id, Nat.abs_cast] at hn
    exact le_pow_half_of_logb hq1 (by positivity)
      (by linarith [le_abs_self (1 + 2 * Real.logb q (K' n))])
  filter_upwards [hbias, hsmall_err, hsmallK, eventually_ge_atTop 4] with n hbiasn herrn hKn hn4
  intro σ I g p T hfan hsize_orig
  have hsize : (p.innerGates.card : ℝ) ≤ (1 + 1 / A - ε₀) * n :=
    hsize_orig.trans (mul_le_mul_of_nonneg_right (sub_le_sub_left (min_le_left _ _) _)
      (Nat.cast_nonneg n))
  have hS : HalfspaceCombBias (t n) (S n) (K' n) (b n) := hbiasn.mono (le_max_left _ _)
  have hb : 0 ≤ b n := hS.nonneg (by positivity) (by
    rw [Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]
    exact hKn)
  set lc := liveCircuit p (fun _ => False)
  set L := unitLedger p I
  set Nnet := liveNetwork p (fun _ => False) U
  set V := Nat.card (Compiler.Vertex lc)
  have hfan_lc : lc.FanInAtMost 2 :=
    (Program.fanInAtMost_eraseGates_iff (special := fun _ => False)).2 fun k _ =>
      Program.fanInAtMost_iff.mp hfan k
  obtain ⟨lay, hlay⟩ := hC _ _ (Compiler.graph lc) Compiler.loopless
    (Compiler.maxDegreeLE le_rfl hfan_lc)
  set B₀ := (L.network ()).branchingProgram lay
  have hB₀_unamb : B₀.Unambiguous :=
    (L.network ()).unambiguous_branchingProgram lay fun _ _ _ => Compiler.satisfies_unique
  have hB₀_acc : B₀.accepted = univ := by
    rw [Network.accepted_branchingProgram, Compiler.accepted_network]
    ext x; simp
  -- Every `K' n × K' n` sub-rectangle of `B₀.sweep.peers s x` has bounded signed count.
  set D : Set (Fin n → U) := {x | x ∈ S n ↔ T.eval p I x = true}
  have hpeer : ∀ s ≤ B₀.length, ∀ x ∈ B₀.accepted,
      ∀ (Aset : Set (B₀.revealed s → U)) (Cset : Set (↥(B₀.revealed s)ᶜ → U)),
        K' n ≤ Aset.ncard → K' n ≤ Cset.ncard →
        rectangle (B₀.revealed s) Aset Cset ⊆ B₀.sweep.peers s x →
          |signedCount D (rectangle (B₀.revealed s) Aset Cset)| ≤
            2 * b n * (rectangle (B₀.revealed s) Aset Cset).ncard := by
    intro s hs x hx Aset Cset hAset hCset hrect_sub
    by_cases hsV : s ≤ V
    · have hrev_eq : B₀.revealed s = Nnet.readIn (lay.initial s) := by
        change (L.network ()).revealedBy lay s = Nnet.readIn (lay.initial s)
        have hsV' : s ≤ Nat.card (Compiler.Vertex (liveCircuit p (fun _ => False))) := hsV
        simp only [Network.revealedBy, hsV', ↓reduceIte]
        rfl
      have hpath_eq (y : Fin n → U) :
          B₀.path y s = (L.network ()).frontierValues lay s (fun e => p.trace I y e.signal.1) := by
        have hy : y ∈ B₀.accepted := hB₀_acc.symm ▸ mem_univ y
        obtain ⟨α, hα, hfv⟩ := (L.network ()).exists_satisfies_of_isAcceptingPath lay
          (B₀.isAcceptingPath_path hy)
        rw [hfv s hs, Network.frontierValues_eq_iff]
        intro e _
        have h : α e = L.run () y e.signal.1 := Compiler.eq_trace hα e
        rwa [unitLedger_run_eq_trace] at h
      obtain ⟨fcomb, hfcomb, hfeval⟩ := exists_isHalfspaceComb_on_cut T p I (lay.initial s)
        (B₀.path x s)
      -- Transport across `hrev_eq : B₀.revealed s = Nnet.readIn (lay.initial s)`.
      revert Aset Cset hAset hCset hrect_sub
      rw [hrev_eq]
      intro Aset Cset hAset hCset hrect_sub
      have hon : ∀ y ∈ rectangle (Nnet.readIn (lay.initial s)) Aset Cset,
          T.eval p I y = fcomb ((Nnet.readIn (lay.initial s)).domRestrict y)
            ((Nnet.readIn (lay.initial s))ᶜ.domRestrict y) := fun y hy =>
        hfeval y (by rw [← show B₀.path y s = B₀.path x s from (hrect_sub hy).2, hpath_eq y]; rfl)
      convert hS _ Aset Cset hAset hCset fcomb hfcomb using 2
      exact signedCount_congr fun y hy => by simp only [D, mem_ofPred_eq, hon y hy]
    · -- `s = V + 1`: `B₀.revealed s = univ`, so `(↥univᶜ → U)` has card `1 < 2 ≤ K' n`.
      have hs_top : s = V + 1 := by
        change s ≤ V + 1 at hs
        omega
      have hrev_top : B₀.revealed s = univ := by
        rw [hs_top]
        exact B₀.revealed_length
      have hC1 : Cset.ncard ≤ 1 := by
        calc Cset.ncard ≤ Nat.card (↥(B₀.revealed s)ᶜ → U) := ncard_le_card Cset
          _ = 1 := by
              rw [hrev_top, compl_univ, Nat.card_fun, Nat.card_coe_set_eq, ncard_empty, pow_zero]
      have : 2 ≤ K' n := le_max_right _ _
      omega
  have hpeel := abs_signedCount_le_of_root_peers hB₀_unamb rfl rfl (Nat.succ_pos _)
    (fun x hx => ⟨hx, fun _ _ => rfl⟩) D hb hpeer
  rw [hB₀_acc] at hpeel
  -- Bound `realizedSize B₀` using `ncard_realizedEdge_le_min` and the convex combination.
  set se := p.innerGates.card
  have hse : lc.innerSize = se := by
    simp [lc, innerSize_liveCircuit, se]
  have hV_le : V ≤ 7 * se + 3 * n := by
    have h := Compiler.card_vertex_le hfan_lc
    have hlive := card_live_le (p := p) (special := fun _ => False)
    rw [hse] at h hlive
    omega
  have hV_bound : (V : ℝ) ≤ 10 * (2 + 1 / A) * n := by
    have hse_le : (se : ℝ) ≤ (1 + 1 / A) * n := by
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hV_r : (V : ℝ) ≤ 7 * se + 3 * n := by exact_mod_cast hV_le
    nlinarith [Nat.cast_nonneg (α := ℝ) n, div_pos one_pos hA]
  have hlogV_le : Real.log (V + 1) ≤ Real.log (10 * (2 + 1 / A) * n + 11) :=
    Real.log_le_log (by positivity) (by linarith)
  have hpos_edge_step (s : ℕ) : (0 : ℝ) < (B₀.edgeOf s '' univ).ncard := by
    exact_mod_cast (ncard_pos (toFinite _)).mpr (univ_nonempty.image _)
  -- Bound the exponent `w_max` of `q ^ w_max` across all steps `s < V`.
  have hstep_le (s : ℕ) (hs : s < V) :
      Real.logb q ((B₀.edgeOf s '' univ).ncard : ℝ) ≤
        (1 - 2 * μ) * n - 2 * Real.logb q (K' n) - κ * Real.log (V + 1) - 1 := by
    set W := Nnet.component (lay.symm ⟨s, hs⟩)
    set nW := (Nnet.readIn W).ncard
    have hcomp_sub : Nnet.frontier lay s ∪ Nnet.frontier lay (s + 1) ⊆ Nnet.touching W :=
      union_subset (hlay s hs s le_rfl (by omega)).1 (hlay s hs (s + 1) (by omega) le_rfl).1
    have hmin := ncard_realizedEdge_le_min p I hfan_lc lay hs hcomp_sub
    rw [hB₀_acc] at hmin
    have hlogb (m : ℕ) (h : (B₀.edgeOf s '' univ).ncard ≤ q ^ m) :
        Real.logb q ((B₀.edgeOf s '' univ).ncard : ℝ) ≤ m :=
      (Real.logb_le_iff_le_rpow (by linarith) (hpos_edge_step s)).mpr (by
        rw [Real.rpow_natCast]; exact_mod_cast h)
    have hlog_min : Real.logb q ((B₀.edgeOf s '' univ).ncard : ℝ) ≤
        min (((Nnet.frontier lay s).ncard : ℝ) + 4) (nW : ℝ) :=
      le_min (by exact_mod_cast hlogb _ (hmin.trans (min_le_left _ _)))
        (hlogb _ (hmin.trans (min_le_right _ _)))
    have hfront_le : ((Nnet.frontier lay s).ncard : ℝ) ≤
        (A + η) * (Compiler.graph lc).cycleRankOn W + η * V + C :=
      (hlay s hs s le_rfl (by omega)).2
    have hρ : ((Compiler.graph lc).cycleRankOn W : ℝ) + nW ≤ se + 1 := by
      have h := Compiler.cycleRankOn_add_ncard_readIn_le (I.withConstants (L.readout ()))
        (fun _ => univ) hfan_lc (Nnet.edgeCut_component (lay.symm ⟨s, hs⟩))
        (Nnet.ncard_component_le_ncard_touching_add_one (lay.symm ⟨s, hs⟩))
      rw [hse] at h
      change (Compiler.graph lc).cycleRankOn W + nW ≤ (2 - 1) * se + 1 at h
      have h' : (Compiler.graph lc).cycleRankOn W + nW ≤ se + 1 := by omega
      exact_mod_cast h'
    have hexp := step_exponent_le hA hε₀ hsize hV_le hfront_le hρ
    linarith [hlog_min.trans hexp, mul_le_mul_of_nonneg_left hlogV_le hκ_pos.le]
  -- At the final step `s = V`, `Nnet.read = univ`, so `B₀.edges V` has size `≤ q ^ 0 = 1`.
  have hlast_le : (B₀.edgeOf V '' univ).ncard ≤ 1 := by
    have hsub : B₀.edgeOf V '' B₀.accepted ⊆ B₀.edges V := by
      rintro _ ⟨x, hx, rfl⟩
      exact B₀.edgeOf_mem_edges hx (Nat.lt_succ_self V)
    rw [← hB₀_acc]
    calc (B₀.edgeOf V '' B₀.accepted).ncard
        ≤ (B₀.edges V).ncard := ncard_le_ncard hsub (toFinite _)
      _ ≤ q ^ (L.network ()).readᶜ.ncard := (L.network ()).ncard_edges_last_le lay
      _ = 1 := by
          have hread : (L.network ()).read = univ := read_liveNetwork (U := U)
          rw [hread, compl_univ, ncard_empty, pow_zero]
  -- Sum over all `V + 1` steps to bound `((K' n - 1)^2 * realizedSize B₀) / q^n`.
  set M_exp : ℝ := (1 - 2 * μ) * n - 2 * Real.logb q (K' n) - κ * Real.log (V + 1) - 1
  have hM_nonneg : 0 ≤ M_exp := by
    have h13 : 0 ≤ (1 - 3 * μ) * n := mul_nonneg (by linarith) (Nat.cast_nonneg n)
    have hC_pos : 0 ≤ |C| + A + η := by positivity
    linarith [herrn, mul_le_mul_of_nonneg_left hlogV_le hκ_pos.le]
  have hrealized : ((realizedSize B₀ : ℕ) : ℝ) ≤ (V + 1 : ℝ) * (q : ℝ) ^ M_exp := by
    rw [realizedSize, show B₀.length = V + 1 from rfl, Finset.sum_range_succ, hB₀_acc]
    push_cast
    have h1_le_qM : (1 : ℝ) ≤ (q : ℝ) ^ M_exp := Real.one_le_rpow (by linarith) hM_nonneg
    have hsum_le : ∑ x ∈ Finset.range V, ((B₀.edgeOf x '' univ).ncard : ℝ) ≤
        (V : ℝ) * (q : ℝ) ^ M_exp :=
      (Finset.sum_le_sum fun s hs => (Real.logb_le_iff_le_rpow (by linarith)
        (hpos_edge_step s)).mp (hstep_le s (Finset.mem_range.mp hs))).trans_eq
        (by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul])
    have hlast_r : ((B₀.edgeOf V '' univ).ncard : ℝ) ≤ (q : ℝ) ^ M_exp :=
      (Nat.cast_le.mpr hlast_le).trans (by simpa only [Nat.cast_one] using h1_le_qM)
    linarith
  have hK'_rpow : (((K' n - 1) ^ 2 : ℕ) : ℝ) ≤ (q : ℝ) ^ (2 * Real.logb q (K' n)) := by
    have hK'_pos : (0 : ℝ) < (K' n : ℕ) := by exact_mod_cast (show 0 < K' n by positivity)
    rw [mul_comm, Real.rpow_mul (by positivity),
      Real.rpow_logb (by positivity) (by linarith) hK'_pos, Real.rpow_two]
    exact_mod_cast Nat.pow_le_pow_left (Nat.sub_le (K' n) 1) 2
  have hV1_rpow : (V + 1 : ℝ) ≤ (q : ℝ) ^ (κ * Real.log (V + 1)) := by
    have hV1_eq : (V + 1 : ℝ) = (q : ℝ) ^ Real.logb q (V + 1) :=
      (Real.rpow_logb (by positivity) (by linarith) (by positivity)).symm
    have hlogV_nn : 0 ≤ Real.log (V + 1) := Real.log_nonneg (by linarith)
    have hexp_le : Real.logb q (V + 1) ≤ κ * Real.log (V + 1) := by
      rw [Real.logb]
      calc Real.log (V + 1) / Real.log q
          ≤ Real.log (V + 1) / Real.log 2 :=
            div_le_div_of_nonneg_left hlogV_nn (Real.log_pos one_lt_two) hlq2
        _ = 1 / Real.log 2 * Real.log (V + 1) := by ring
        _ ≤ κ * Real.log (V + 1) :=
            mul_le_mul_of_nonneg_right (by simp only [κ]; linarith) hlogV_nn
    calc (V + 1 : ℝ) = (q : ℝ) ^ Real.logb q (V + 1) := hV1_eq
      _ ≤ (q : ℝ) ^ (κ * Real.log (V + 1)) := Real.rpow_le_rpow_of_exponent_le (by linarith) hexp_le
  have hnum_le : (((K' n - 1) ^ 2 * realizedSize B₀ : ℕ) : ℝ) ≤ (q : ℝ) ^ ((1 - μ) * n) := by
    rw [Nat.cast_mul]
    calc (((K' n - 1) ^ 2 : ℕ) : ℝ) * (realizedSize B₀ : ℝ)
        ≤ (q : ℝ) ^ (2 * Real.logb q (K' n)) * ((V + 1 : ℝ) * (q : ℝ) ^ M_exp) := by gcongr
      _ ≤ (q : ℝ) ^ (2 * Real.logb q (K' n)) * ((q : ℝ) ^ (κ * Real.log (V + 1)) *
            (q : ℝ) ^ M_exp) :=
          by gcongr
      _ = (q : ℝ) ^ (2 * Real.logb q (K' n) + (κ * Real.log (V + 1) + M_exp)) := by
          rw [← Real.rpow_add (by positivity), ← Real.rpow_add (by positivity)]
      _ ≤ (q : ℝ) ^ ((1 - μ) * n) := by
          refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
          simp only [M_exp]
          linarith [mul_nonneg hμ.le (Nat.cast_nonneg (α := ℝ) n)]
  have hcard_univ : (Nat.card (Fin n → U) : ℝ) = (q : ℝ) ^ (n : ℝ) := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin, Real.rpow_natCast]
    push_cast
    rfl
  -- `R ≤ q ^ ((1 - μ) n) ≤ exp (-μ log 2 · n) q ^ n` bounds the peeling residual.
  have hres_le : (((K' n - 1) ^ 2 * realizedSize B₀ : ℕ) : ℝ) ≤
      Real.exp (-(μ * Real.log 2 * n)) * Nat.card (Fin n → U) := by
    rw [hcard_univ]
    refine hnum_le.trans ?_
    rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (by positivity), ← Real.exp_add,
      Real.exp_le_exp]
    nlinarith [mul_le_mul_of_nonneg_right hlq2 (show (0 : ℝ) ≤ μ * n by positivity)]
  have hN_pos : (0 : ℝ) < Nat.card (Fin n → U) := by exact_mod_cast Nat.card_pos
  have hsc := signedCount_eq_two_mul D univ
  rw [univ_inter, ncard_univ] at hsc
  rw [ncard_univ] at hpeel
  rw [agreement, div_le_iff₀ hN_pos]
  change (D.ncard : ℝ) ≤ _
  linarith [le_abs_self (signedCount D univ), mul_pos (Real.exp_pos (-(μ * Real.log 2 * n))) hN_pos]

end LivePeeling

/-! ### Unconditional median-switched average-case bounds (`4.575972 n`) -/

/-- **Median-switched average-case bound for `ThresholdTop` (`4.575972 n`).** Below
`(L₃ - ε) n` inner gates, where `L₃ = 1 + 2π / (3 arccos (5 / 6)) ≈ 4.575972`, every fan-in-two
program topped with `t_n` arbitrary-real-weight linear threshold units agrees with any
`HalfspaceCombBias` target `S_n` on at most `1/2 + b_n + exp (-γ n)` of the inputs. -/
theorem eventually_agreement_thresholdTop_le_switched {ε : ℝ} (hε : 0 < ε) :
    ∃ γ > 0, ∀ (U : Type u) [Finite U] [Nontrivial U] (t K : ℕ → ℕ) (b : ℕ → ℝ)
      (S : ∀ n, Set (Fin n → U)),
      (∀ᶠ n in atTop, HalfspaceCombBias (t n) (S n) (K n) (b n)) →
      (fun n => Real.log (K n)) =o[atTop] (fun n => (n : ℝ)) →
      ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (g : ℕ)
        (p : Program σ n g) (T : ThresholdTop U n g (t n)),
        p.FanInAtMost 2 →
        (p.innerGates.card : ℝ) ≤ (1 + 2 * π / (3 * arccos (5 / 6)) - ε) * n →
          agreement (S n) {x | T.eval p I x = true} ≤ 1 / 2 + b n + Real.exp (-(γ * n)) := by
  have h := eventually_agreement_thresholdTop_le_of_layoutBound.{u, v}
    (mul_pos two_pos Switched.switchedCoefficient_pos) layoutBound_switched hε
  rwa [Switched.one_add_inv_two_mul_switchedCoefficient] at h

/-- **Rational `(4.57597 - ε) n` average-case bound for `ThresholdTop`.** -/
theorem eventually_agreement_thresholdTop_le_457597 {ε : ℝ} (hε : 0 < ε) :
    ∃ γ > 0, ∀ (U : Type u) [Finite U] [Nontrivial U] (t K : ℕ → ℕ) (b : ℕ → ℝ)
      (S : ∀ n, Set (Fin n → U)),
      (∀ᶠ n in atTop, HalfspaceCombBias (t n) (S n) (K n) (b n)) →
      (fun n => Real.log (K n)) =o[atTop] (fun n => (n : ℝ)) →
      ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (g : ℕ)
        (p : Program σ n g) (T : ThresholdTop U n g (t n)),
        p.FanInAtMost 2 → (p.innerGates.card : ℝ) ≤ (457597 / 100000 - ε) * n →
          agreement (S n) {x | T.eval p I x = true} ≤ 1 / 2 + b n + Real.exp (-(γ * n)) := by
  obtain ⟨γ, hγ, H⟩ := eventually_agreement_thresholdTop_le_switched.{u, v} hε
  refine ⟨γ, hγ, fun U _ _ t K b S hbias hK => ?_⟩
  filter_upwards [H U t K b S hbias hK] with n hn
  intro σ I g p T hfan hsize
  exact hn σ I g p T hfan (hsize.trans (mul_le_mul_of_nonneg_right
    (by linarith [Switched.circuitCoefficient_ge_457597]) (Nat.cast_nonneg n)))

/-! ### Single-cut sign-rank bound and Forster's theorem -/

section SignRankForster

/-- Every `1`-halfspace combination `f : α → β → Bool` admits a rank-`2` real factorization
`U_mat * V_mat` that strictly sign-represents `f` (using integer strict order-ranks shifted by
`1 / 2`, with no topological perturbation). -/
private theorem exists_mul_signRepresents_of_isHalfspaceComb_one {α β : Type*}
    [Finite α] [Finite β] {f : α → β → Bool} (hf : IsHalfspaceComb 1 f) :
    ∃ (U_mat : Matrix α (Fin 2) ℝ) (V_mat : Matrix (Fin 2) β ℝ),
      Communication.SignRepresents (U_mat * V_mat) f := by
  cases nonempty_fintype α
  cases nonempty_fintype β
  obtain ⟨G, φ, ψ, h⟩ := hf
  set rk := strictRank (Sum.elim (φ 0) (-ψ 0))
  -- `(Ucd c d * V₀) a b = c (rk a - rk b + 1/2) + d`; `(c, d)` is read off the truth table of `G`.
  let Ucd (c d : ℝ) : Matrix α (Fin 2) ℝ :=
    fun a i => if i = 0 then c * ((rk (.inl a) : ℝ) + 1 / 2) + d else c
  let V₀ : Matrix (Fin 2) β ℝ := fun i b => if i = 0 then 1 else -(rk (.inr b) : ℝ)
  have hmul (c d : ℝ) (a : α) (b : β) :
      (Ucd c d * V₀) a b = c * ((rk (.inl a) : ℝ) - rk (.inr b) + 1 / 2) + d := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Fin.isValue, Ucd, V₀, ↓reduceIte, one_ne_zero]
    ring
  have hfab (a : α) (b : β) : f a b = G fun _ => decide (rk (.inl a) < rk (.inr b)) := by
    rw [h a b]
    congr 1 with r
    rw [Fin.eq_zero r]
    exact decide_eq_decide.mpr (strictRank_inl_lt_inr_iff _ _ _ _).symm
  -- Integer ranks put `rk a - rk b + 1/2` at distance `≥ 1/2` from `0`.
  have hrk (a : α) (b : β) :
      rk (.inl a) < rk (.inr b) ∧ ((rk (.inl a) : ℕ) : ℝ) + 1 ≤ (rk (.inr b) : ℕ) ∨
        ¬rk (.inl a) < rk (.inr b) ∧ ((rk (.inr b) : ℕ) : ℝ) ≤ (rk (.inl a) : ℕ) := by
    rcases lt_or_ge (rk (.inl a)) (rk (.inr b)) with h' | h'
    · exact .inl ⟨h', by exact_mod_cast (h' : (rk (.inl a) : ℕ) + 1 ≤ rk (.inr b))⟩
    · exact .inr ⟨not_lt.mpr h', by exact_mod_cast h'⟩
  -- `G` is `const false`, `id`, `not` or `const true`.
  cases hb0 : G (fun _ => false) <;> cases hb1 : G (fun _ => true) <;>
    [refine ⟨Ucd 0 1, V₀, ?_⟩; refine ⟨Ucd 1 0, V₀, ?_⟩; refine ⟨Ucd (-1) 0, V₀, ?_⟩;
      refine ⟨Ucd 0 (-1), V₀, ?_⟩] <;>
  refine Communication.SignRepresents.iff_lt.mpr fun a b => ?_ <;>
  rw [hfab, hmul] <;>
  rcases hrk a b with ⟨hlt, hX⟩ | ⟨hlt, hX⟩ <;>
  simp only [hlt, decide_true, decide_false, hb0, hb1, Bool.false_eq_true, ↓reduceIte] <;>
  linarith

/-- **Sign-rank of a two-party halfspace (`t = 1`).** Every `1`-halfspace combination over finite
domains has sign-rank at most `2`. -/
theorem signRank_le_two_of_isHalfspaceComb_one {α β : Type*} [Finite α] [Fintype β]
    {f : α → β → Bool} (hf : IsHalfspaceComb 1 f) :
    Communication.signRank f ≤ 2 := by
  obtain ⟨U_mat, V_mat, hrep⟩ := exists_mul_signRepresents_of_isHalfspaceComb_one hf
  simpa only [Fintype.card_fin] using Communication.signRank_le_card_of_mul hrep

open Classical in
/-- **Single-cut sign-rank bound for `ThresholdTop` (`t = 1`).** Across any vertex cut `P` of
`liveNetwork p (fun _ => False) U`, letting `X = readIn P`, the single-perceptron top
`T : ThresholdTop U n g 1` has communication sign-rank at most `2 * |U| ^ |edgeCut P|` across
`(X, Xᶜ)`. -/
theorem signRank_thresholdTop_le {σ : Signature.{v}} {U : Type u} [Fintype U]
    {n g : ℕ} (T : ThresholdTop U n g 1) (p : Program σ n g) (I : Interpretation σ U)
    (P : Set (Compiler.Vertex (liveCircuit p (fun _ => False)))) :
    Communication.signRank
      (fun (a : (liveNetwork p (fun _ => False) U).readIn P → U)
          (b : ↥((liveNetwork p (fun _ => False) U).readIn P)ᶜ → U) =>
        T.eval p I
          ((Equiv.piEquivPiSubtypeProd
            (· ∈ (liveNetwork p (fun _ => False) U).readIn P) fun _ => U).symm (a, b))) ≤
      2 * Fintype.card U ^ ((liveNetwork p (fun _ => False) U).edgeCut P).ncard := by
  set Nnet := liveNetwork p (fun _ => False) U
  set X := Nnet.readIn P
  set Ecut := Nnet.edgeCut P
  cases nonempty_fintype Ecut
  let glue := (Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => U).symm
  have hglue_X (a : X → U) (b : ↥Xᶜ → U) : X.domRestrict (glue (a, b)) = a :=
    congrArg Prod.fst ((Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => U).apply_symm_apply (a, b))
  have hglue_Xc (a : X → U) (b : ↥Xᶜ → U) : Xᶜ.domRestrict (glue (a, b)) = b :=
    congrArg Prod.snd ((Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => U).apply_symm_apply (a, b))
  let cutVal (z : Fin n → U) : Ecut → U := fun e => p.trace I z e.1.signal.1
  let Aset (τ : Ecut → U) : Set (X → U) :=
    {a | ∃ x : Fin n → U, X.domRestrict x = a ∧ cutVal x = τ}
  let Bset (τ : Ecut → U) : Set (↥Xᶜ → U) :=
    {b | ∃ y : Fin n → U, Xᶜ.domRestrict y = b ∧ cutVal y = τ}
  -- Rectangle characterization: `(a ∈ Aset τ ∧ b ∈ Bset τ) ↔ cutVal (glue (a, b)) = τ`.
  have hrect_iff (τ : Ecut → U) (a : X → U) (b : ↥Xᶜ → U) :
      (a ∈ Aset τ ∧ b ∈ Bset τ) ↔ cutVal (glue (a, b)) = τ := by
    constructor
    · rintro ⟨⟨x, hxa, hxτ⟩, ⟨y, hyb, hyτ⟩⟩
      have hcut_xy : EqOn (fun e => p.trace I x e.signal.1)
          (fun e => p.trace I y e.signal.1) Ecut :=
        fun e he => (congrFun hxτ ⟨e, he⟩).trans (congrFun hyτ ⟨e, he⟩).symm
      have hzx : EqOn (glue (a, b)) x X :=
        domRestrict_eq_domRestrict_iff.mp ((hglue_X a b).trans hxa.symm)
      have hzy : EqOn (glue (a, b)) y Xᶜ :=
        domRestrict_eq_domRestrict_iff.mp ((hglue_Xc a b).trans hyb.symm)
      have hsp := (unitLedger p I).trace_of_splice (x := x) (y := y) rfl rfl hcut_xy hzx hzy
      ext e
      by_cases hw : e.1.signal.1 ∈ wiresIn P
      · exact ((hsp e.1.signal.1).1 hw).trans (congrFun hxτ e)
      · exact ((hsp e.1.signal.1).2 hw).trans (congrFun hyτ e)
    · intro hτ
      exact ⟨⟨glue (a, b), hglue_X a b, hτ⟩, ⟨glue (a, b), hglue_Xc a b, hτ⟩⟩
  -- For each `τ : Ecut → U`, pick a rank-2 sign-representation on the slice of `τ`.
  let τOpt (τ : Ecut → U) : Compiler.Edge (liveCircuit p (fun _ => False)) → Option U :=
    fun e => if he : e ∈ Ecut then some (τ ⟨e, he⟩) else none
  choose f_slice hf_comb hf_eval using fun τ : Ecut → U =>
    exists_isHalfspaceComb_on_cut T p I P (τOpt τ)
  choose U_slice V_slice hrep_slice using fun τ : Ecut → U =>
    exists_mul_signRepresents_of_isHalfspaceComb_one (hf_comb τ)
  let U_big : Matrix (X → U) ((Ecut → U) × Fin 2) ℝ :=
    fun a p_idx => if a ∈ Aset p_idx.1 then U_slice p_idx.1 a p_idx.2 else 0
  let V_big : Matrix ((Ecut → U) × Fin 2) (↥Xᶜ → U) ℝ :=
    fun p_idx b => if b ∈ Bset p_idx.1 then V_slice p_idx.1 p_idx.2 b else 0
  have hrep : Communication.SignRepresents (U_big * V_big)
      (fun a b => T.eval p I (glue (a, b))) := by
    refine Communication.SignRepresents.iff_lt.mpr fun a b => ?_
    set τ₀ := cutVal (glue (a, b))
    have hmul : (U_big * V_big) a b = (U_slice τ₀ * V_slice τ₀) a b := by
      rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single τ₀ (fun τ _ hτ => ?_)
        (fun h => absurd (Finset.mem_univ τ₀) h)]
      · obtain ⟨ha, hb⟩ := (hrect_iff τ₀ a b).mpr rfl
        simp only [U_big, V_big, ha, hb, ↓reduceIte, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases ha : a ∈ Aset τ
      · have hb : b ∉ Bset τ := fun hb => hτ ((hrect_iff τ a b).mp ⟨ha, hb⟩).symm
        simp only [U_big, V_big, hb, ↓reduceIte, mul_zero]
      · simp only [U_big, V_big, ha, ↓reduceIte, zero_mul]
    have heval_eq : T.eval p I (glue (a, b)) = f_slice τ₀ a b := by
      have h1 := hf_eval τ₀ (glue (a, b)) (funext fun e => by
        by_cases he : e ∈ Ecut
        · simp only [τOpt, Ecut, Nnet, he, ↓reduceDIte, ↓reduceIte, τ₀, cutVal]
        · simp only [τOpt, Ecut, Nnet, he, ↓reduceDIte, ↓reduceIte])
      rwa [hglue_X, hglue_Xc] at h1
    rw [hmul, heval_eq]
    exact Communication.SignRepresents.iff_lt.mp (hrep_slice τ₀) a b
  have hcard_idx : Fintype.card ((Ecut → U) × Fin 2) = 2 * Fintype.card U ^ Ecut.ncard := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, mul_comm,
      ← Nat.card_eq_fintype_card (α := Ecut), Nat.card_coe_set_eq]
  exact (Communication.signRank_le_card_of_mul hrep).trans_eq hcard_idx

/-- Complementing a vertex set in `liveNetwork p (fun _ => False) U` complements `readIn`. -/
private theorem readIn_compl_liveNetwork {σ : Signature.{v}} {U : Type u} {n g : ℕ}
    (p : Program σ n g) (P : Set (Compiler.Vertex (liveCircuit p (fun _ => False)))) :
    (liveNetwork p (fun _ => False) U).readIn Pᶜ =
      ((liveNetwork p (fun _ => False) U).readIn P)ᶜ := by
  set lc := liveCircuit p (fun _ => False)
  ext i
  have hreach : Compiler.Reach lc (.input i) := reach_input i
  have hsite := Compiler.site_of_reach hreach
  constructor
  · rintro ⟨v, hvP, hvi⟩ ⟨w, hwP, hwi⟩
    have hv : v = .signal ⟨.input i, hreach⟩ := Option.some_injective _ (hvi.symm.trans hsite)
    have hw : w = .signal ⟨.input i, hreach⟩ := Option.some_injective _ (hwi.symm.trans hsite)
    exact hvP (hv ▸ hw ▸ hwP)
  · intro hi
    refine ⟨.signal ⟨.input i, hreach⟩, fun hP => hi ⟨_, hP, hsite⟩, hsite⟩

open Classical in
private theorem cutRank_hardMatrix_le_of_thresholdTop_eval {σ : Signature.{v}} {n g : ℕ}
    {T : ThresholdTop Bool n g 1} {p : Program σ n g} {I : Interpretation σ Bool}
    (hTeval : ∀ x, T.eval p I x = hardForm n x)
    (P : Set (Compiler.Vertex (liveCircuit p (fun _ => False)))) :
    (hardMatrix n + (hardMatrix n)ᵀ).cutRank ((liveNetwork p (fun _ => False) Bool).readIn P) ≤
      2 * ((liveNetwork p (fun _ => False) Bool).edgeCut P).ncard + 2 := by
  have hsr_up := signRank_thresholdTop_le T p I P
  rw [Fintype.card_bool] at hsr_up
  have heval_eq :
      (fun (a : (liveNetwork p (fun _ => False) Bool).readIn P → Bool)
          (b : ↥((liveNetwork p (fun _ => False) Bool).readIn P)ᶜ → Bool) =>
        T.eval p I
          ((Equiv.piEquivPiSubtypeProd
            (· ∈ (liveNetwork p (fun _ => False) Bool).readIn P) fun _ => Bool).symm (a, b))) =
      (fun (a : (liveNetwork p (fun _ => False) Bool).readIn P → Bool)
          (b : ↥((liveNetwork p (fun _ => False) Bool).readIn P)ᶜ → Bool) =>
        BitString.quadForm (hardMatrix n)
          ((Equiv.piEquivPiSubtypeProd
            (· ∈ (liveNetwork p (fun _ => False) Bool).readIn P) fun _ => Bool).symm (a, b))) :=
    funext fun _ => funext fun _ => hTeval _
  have hsr_lo := Communication.two_pow_cutRank_le_signRank_quadForm_sq (hardMatrix n)
    ((liveNetwork p (fun _ => False) Bool).readIn P)
  rw [← heval_eq] at hsr_lo
  have hsq_up : (2 * 2 ^ ((liveNetwork p (fun _ => False) Bool).edgeCut P).ncard) ^ 2 =
      2 ^ (2 * ((liveNetwork p (fun _ => False) Bool).edgeCut P).ncard + 2) := by
    rw [mul_pow, ← pow_mul, show (2 : ℕ) ^ 2 = 2 ^ 2 from rfl, ← pow_add, add_comm, mul_comm _ 2]
  have hpow := hsr_lo.trans ((Nat.pow_le_pow_left hsr_up 2).trans_eq hsq_up)
  by_contra! hgt
  have := Nat.pow_lt_pow_right one_lt_two hgt
  omega

/-- **Single-cut `hardForm` lower bound for `ThresholdTop` (`t = 1`) under `LayoutBound 3 A`.**
Every fan-in-two program `p` topped with a single arbitrary-real-weight linear threshold unit `T`
(including direct input skip-wires) computing the nonconstructively chosen bilinear form
`hardForm n` (selected via `Classical.choose`) needs more than `(1 + 1 / (4 A) - ε) n` inner
gates. -/
theorem eventually_lt_innerSize_thresholdTop_hardForm_of_layoutBound {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound 3 A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (g : ℕ)
      (p : Program σ n g) (T : ThresholdTop Bool n g 1),
      p.FanInAtMost 2 → (∀ x, T.eval p I x = hardForm n x) →
        (1 + 1 / (4 * A) - ε) * n < p.innerGates.card := by
  set Bcoef : ℝ := (1 + 1 / (4 * A)) + 10 * (2 + 1 / (4 * A))
  have hBcoef : 0 < Bcoef := by positivity
  set η : ℝ := A * ε / (4 * Bcoef)
  have hη : 0 < η := by positivity
  obtain ⟨C, hC⟩ := hlayout.exists_layout_componentwise hη
  set defic : ℕ → ℕ := fun n => 2 * (2 * Nat.sqrt (n / 2) + 1) + 1
  have hdefic_o : (fun n : ℕ => ((defic n : ℕ) : ℝ)) =o[atTop] fun n => (n : ℝ) :=
    isLittleO_hardDeficiency
  have herr_o : (fun n : ℕ => (1 + 2 * (A + η)) * (defic n : ℝ) +
      (2 * |C| + 6 * (A + η) + 4)) =o[atTop] fun n => (n : ℝ) :=
    (hdefic_o.const_mul_left _).add (isLittleO_const_id_atTop _).natCast_atTop
  have hsmall_defic : ∀ᶠ n : ℕ in atTop, 4 * (defic n + 2) + 4 ≤ n := by
    filter_upwards [hdefic_o.bound (by norm_num : (0 : ℝ) < 1 / 8), eventually_ge_atTop 24]
      with n hn hn24
    simp only [Real.norm_eq_abs, Nat.abs_cast] at hn
    have hn24' : (24 : ℝ) ≤ n := by exact_mod_cast hn24
    exact_mod_cast (by linarith [le_abs_self (defic n : ℝ)] : (4 * (defic n + 2) + 4 : ℝ) ≤ n)
  filter_upwards [herr_o.bound (show (0 : ℝ) < A * ε by positivity), hsmall_defic] with n herrn hdn
  simp only [Real.norm_eq_abs, Nat.abs_cast] at herrn
  have herr : (1 + 2 * (A + η)) * (defic n : ℝ) + (2 * |C| + 6 * (A + η) + 4) ≤ A * ε * n := by
    linarith [le_abs_self ((1 + 2 * (A + η)) * (defic n : ℝ) + (2 * |C| + 6 * (A + η) + 4))]
  intro σ I g p T hfan hTeval
  by_contra! hsize
  set lc := liveCircuit p (fun _ => False)
  set Nnet := liveNetwork p (fun _ => False) Bool
  set V := Nat.card (Compiler.Vertex lc)
  set se := p.innerGates.card
  have hse : lc.innerSize = se := by simp [lc, innerSize_liveCircuit, se]
  have hfan_lc : lc.FanInAtMost 2 :=
    (Program.fanInAtMost_eraseGates_iff (special := fun _ => False)).2 fun k _ =>
      Program.fanInAtMost_iff.mp hfan k
  obtain ⟨lay, hlay⟩ := hC _ _ (Compiler.graph lc) Compiler.loopless
    (Compiler.maxDegreeLE le_rfl hfan_lc)
  -- For any vertex set `Qset` with `edgeCut Qset = ∅`, either `|readIn Qset| ≤ defic n + 2` or
  -- `|readIn Qset| ≥ n - (defic n + 2)`.
  have hclosed_dichotomy (Qset : Set (Compiler.Vertex lc)) (hQ : Nnet.edgeCut Qset = ∅) :
      (Nnet.readIn Qset).ncard ≤ defic n + 2 ∨
        n - (defic n + 2) ≤ (Nnet.readIn Qset).ncard := by
    have hcut_le (Pset : Set (Compiler.Vertex lc)) (hP : Nnet.edgeCut Pset = ∅)
        (hP_half : (Nnet.readIn Pset).ncard ≤ n / 2) :
        (Nnet.readIn Pset).ncard ≤ defic n + 2 := by
      have hcr_le := cutRank_hardMatrix_le_of_thresholdTop_eval hTeval Pset
      rw [hP, ncard_empty, mul_zero, zero_add] at hcr_le
      have hbis := ncard_le_cutRank_add_of_bisection (e := (defic n : ℝ))
        (fun U hU => by exact_mod_cast half_le_cutRank_hardMatrix n hU) hP_half
      have hcr_r : ((hardMatrix n + (hardMatrix n)ᵀ).cutRank (Nnet.readIn Pset) : ℝ) ≤ 2 := by
        exact_mod_cast hcr_le
      have hXP_r : (((Nnet.readIn Pset).ncard : ℕ) : ℝ) ≤ (defic n + 2 : ℕ) := by
        push_cast; linarith
      exact_mod_cast hXP_r
    by_cases hhalf : (Nnet.readIn Qset).ncard ≤ n / 2
    · exact Or.inl (hcut_le Qset hQ hhalf)
    · refine Or.inr ?_
      have hQc_cut : Nnet.edgeCut Qsetᶜ = ∅ :=
        (Compiler.graph lc).edgeCut_eq_empty_iff.mpr fun e =>
          not_iff_not.mpr ((Compiler.graph lc).edgeCut_eq_empty_iff.mp hQ e)
      have hQc_eq : Nnet.readIn Qsetᶜ = (Nnet.readIn Qset)ᶜ := readIn_compl_liveNetwork p Qset
      have hsum_n : (Nnet.readIn Qset).ncard + (Nnet.readIn Qsetᶜ).ncard = n := by
        rw [hQc_eq, ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
      have hQc_le := hcut_le Qsetᶜ hQc_cut (by omega)
      omega
  -- Pick the layer `s` where `readIn (lay.initial s)` has size `⌊n / 2⌋`.
  have hread_all : n / 2 ≤ Nnet.read.ncard := by
    rw [read_liveNetwork, ncard_univ, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]
    exact Nat.div_le_self n 2
  obtain ⟨s, hsV, hXs⟩ := Nnet.exists_ncard_readIn_initial_eq lay
    (Compiler.ncard_readAt_le (I.withConstants ((unitLedger p I).readout ())) (fun _ => univ))
    hread_all
  have hs_lt : s < V := by
    rcases eq_or_lt_of_le hsV with rfl | hlt
    · rw [lay.initial_of_card_le le_rfl] at hXs
      have hread_n : (Nnet.readIn univ).ncard = n := by
        have hread : Nnet.readIn univ = univ := read_liveNetwork (U := Bool)
        rw [hread, ncard_univ, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]
      omega
    · exact hlt
  -- At step `s < V`, let `W` be the component of `lay.symm ⟨s, hs_lt⟩`.
  set W := Nnet.component (lay.symm ⟨s, hs_lt⟩)
  have hW_cut : Nnet.edgeCut W = ∅ := Nnet.edgeCut_component _
  have hfront_W : Nnet.frontier lay s ⊆ Nnet.touching W := (hlay s hs_lt s le_rfl (by omega)).1
  have hfront_le : ((Nnet.frontier lay s).ncard : ℝ) ≤
      (A + η) * (Compiler.graph lc).cycleRankOn W + η * V + C :=
    (hlay s hs_lt s le_rfl (by omega)).2
  -- Show `n - (defic n + 2) ≤ (Nnet.readIn W).ncard`: otherwise `lay.initial s \ W` is closed of
  -- forbidden intermediate size!
  have hW_large : n - (defic n + 2) ≤ (Nnet.readIn W).ncard := by
    rcases hclosed_dichotomy W hW_cut with hW_small | hW_big
    · exfalso
      set Bset := lay.initial s \ W
      have hB_cut : Nnet.edgeCut Bset = ∅ := Multigraph.edgeCut_sdiff_eq_empty hW_cut hfront_W
      have hB_sub : Nnet.readIn Bset ⊆ Nnet.readIn (lay.initial s) :=
        fun _ ⟨v, hv, hi⟩ => ⟨v, hv.1, hi⟩
      have hinit_sub : Nnet.readIn (lay.initial s) ⊆ Nnet.readIn Bset ∪ Nnet.readIn W := by
        rintro i ⟨v, hv, hi⟩
        by_cases hvW : v ∈ W
        · exact Or.inr ⟨v, hvW, hi⟩
        · exact Or.inl ⟨v, ⟨hv, hvW⟩, hi⟩
      have hB_le : (Nnet.readIn Bset).ncard ≤ n / 2 :=
        (ncard_le_ncard hB_sub (toFinite _)).trans_eq hXs
      have hB_ge : n / 2 ≤ (Nnet.readIn Bset).ncard + (Nnet.readIn W).ncard :=
        hXs ▸ (ncard_le_ncard hinit_sub (toFinite _)).trans (ncard_union_le _ _)
      rcases hclosed_dichotomy Bset hB_cut with hB_s | hB_l <;> omega
    · exact hW_big
  -- Combine `hW_large`, `cycleRankOn_add_ncard_readIn_le`, and
  -- `cutRank_hardMatrix_le_of_thresholdTop_eval` at layer `s`.
  have hcr_le : (hardMatrix n + (hardMatrix n)ᵀ).cutRank (Nnet.readIn (lay.initial s)) ≤
      2 * (Nnet.frontier lay s).ncard + 2 :=
    cutRank_hardMatrix_le_of_thresholdTop_eval hTeval (lay.initial s)
  have hbis_s : n / 2 ≤ (hardMatrix n + (hardMatrix n)ᵀ).cutRank (Nnet.readIn (lay.initial s)) +
      defic n := half_le_cutRank_hardMatrix n hXs
  have hhalf_le : n / 2 ≤ 2 * (Nnet.frontier lay s).ncard + 2 + defic n := by omega
  have hρW : ((Compiler.graph lc).cycleRankOn W : ℝ) ≤ se - n + (defic n : ℝ) + 3 := by
    set L := unitLedger p I
    have h := Compiler.cycleRankOn_add_ncard_readIn_le (I.withConstants (L.readout ()))
      (fun _ => univ) hfan_lc hW_cut (Nnet.ncard_component_le_ncard_touching_add_one _)
    rw [hse] at h
    change (Compiler.graph lc).cycleRankOn W + (Nnet.readIn W).ncard ≤ (2 - 1) * se + 1 at h
    have h_r : ((Compiler.graph lc).cycleRankOn W : ℝ) + n ≤ se + 1 + (defic n + 2 : ℕ) := by
      exact_mod_cast (by omega : (Compiler.graph lc).cycleRankOn W + n ≤ se + 1 + (defic n + 2))
    push_cast at h_r
    linarith
  have hV_le : V ≤ 7 * se + 3 * n := by
    have h := Compiler.card_vertex_le hfan_lc
    have hlive := card_live_le (p := p) (special := fun _ => False)
    rw [hse] at h hlive
    omega
  have hse_b : (se : ℝ) ≤ (1 + 1 / (4 * A)) * n := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hV_b : (V : ℝ) ≤ 10 * (2 + 1 / (4 * A)) * n := by
    have hV_r : (V : ℝ) ≤ 7 * se + 3 * n := by exact_mod_cast hV_le
    nlinarith [Nat.cast_nonneg (α := ℝ) n, div_pos one_pos hA]
  have h2η_term : 2 * η * (se - n + V) ≤ (1 / 2) * (A * ε) * n := by
    have hsum_le : (se : ℝ) - n + V ≤ Bcoef * n := by
      simp only [Bcoef]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hηB : 2 * η * Bcoef = (1 / 2) * (A * ε) := by simp only [η]; field_simp; ring
    calc 2 * η * ((se : ℝ) - n + V)
        ≤ 2 * η * (Bcoef * n) := mul_le_mul_of_nonneg_left hsum_le (by positivity)
      _ = (2 * η * Bcoef) * n := by ring
      _ = (1 / 2) * (A * ε) * n := by rw [hηB]
  have h2A_se : 2 * A * ((se : ℝ) - n) ≤ (1 / 2 - 2 * A * ε) * n := by
    have h1 : (se : ℝ) - n ≤ (1 / (4 * A) - ε) * n := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * A)
    have h3 : 2 * A * ((1 / (4 * A) - ε) * n) = (1 / 2 - 2 * A * ε) * n := by field_simp; ring
    linarith
  have hfront_full : 2 * ((Nnet.frontier lay s).ncard : ℝ) + 2 + defic n ≤
      (1 / 2 - (1 / 2) * (A * ε)) * n - 1 := by
    have hmul_ρ := mul_le_mul_of_nonneg_left hρW (by positivity : (0 : ℝ) ≤ 2 * (A + η))
    have hC_le := le_abs_self C
    have hAe_pos : 0 < A * ε := by positivity
    linarith [hfront_le, herr]
  have hn_div2 : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (by omega : n ≤ 2 * (n / 2) + 1)
  have hhalf_r : ((n / 2 : ℕ) : ℝ) ≤ 2 * ((Nnet.frontier lay s).ncard : ℝ) + 2 + defic n := by
    exact_mod_cast hhalf_le
  have hAe_nonneg : 0 ≤ (1 / 2) * (A * ε) * n := by positivity
  linarith

/-- **Median-switched `hardForm` lower bound for `ThresholdTop` (`1.893993 n`).** Every fan-in-two
program `p` topped with a single arbitrary-real-weight linear threshold unit `T` (including direct
input skip-wires) computing the nonconstructively chosen bilinear form `hardForm n` needs more than
`(1 + π / (6 * arccos (5 / 6)) - ε) * n` inner gates. -/
theorem eventually_lt_innerSize_thresholdTop_hardForm {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (g : ℕ)
      (p : Program σ n g) (T : ThresholdTop Bool n g 1),
      p.FanInAtMost 2 → (∀ x, T.eval p I x = hardForm n x) →
        (1 + π / (6 * arccos (5 / 6)) - ε) * n < p.innerGates.card := by
  have h := eventually_lt_innerSize_thresholdTop_hardForm_of_layoutBound.{v}
    (mul_pos two_pos Switched.switchedCoefficient_pos) layoutBound_switched hε
  have hcoef : 1 + 1 / (4 * (2 * Switched.switchedCoefficient)) =
      1 + π / (6 * arccos (5 / 6)) := by
    have h1 := Switched.one_add_inv_two_mul_switchedCoefficient
    have h2 : 1 / (2 * Switched.switchedCoefficient) = 2 * π / (3 * arccos (5 / 6)) := by linarith
    have h3 : 1 / (4 * (2 * Switched.switchedCoefficient)) =
        1 / (2 * Switched.switchedCoefficient) / 4 := by field_simp
    rw [h3, h2]
    ring
  rwa [hcoef] at h

/-- **Rational `(1.89399 - ε) n` lower bound for `ThresholdTop` (`t = 1`) on `hardForm n`.** -/
theorem eventually_lt_innerSize_thresholdTop_hardForm_189399 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (g : ℕ)
      (p : Program σ n g) (T : ThresholdTop Bool n g 1),
      p.FanInAtMost 2 → (∀ x, T.eval p I x = hardForm n x) →
        (189399 / 100000 - ε) * n < p.innerGates.card := by
  filter_upwards [eventually_lt_innerSize_thresholdTop_hardForm.{v} hε] with n hn
  intro σ I g p T hfan hTeval
  refine lt_of_le_of_lt ?_ (hn σ I g p T hfan hTeval)
  have hge : (189399 / 100000 : ℝ) ≤ 1 + π / (6 * arccos (5 / 6)) := by
    have h45 := Switched.circuitCoefficient_ge_457597
    have hdiv : π / (6 * arccos (5 / 6)) = (2 * π / (3 * arccos (5 / 6))) / 4 := by ring
    linarith
  exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n)

end SignRankForster

end Cslib.Circuits.Frontier
