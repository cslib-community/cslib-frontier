/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Communication.Protocol
public import CslibFrontier.Computability.Communication.Rectangle
public import CslibFrontier.GameTheory.Mechanism.CombinatorialAuction.Walrasian
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Combinatorial auctions: exponential communication complexity lower bound

This module formalizes §11.6 of [BlumrosenNisan2007] (pp. 287–289): even with unlimited
computational power and arbitrary query types, any deterministic two-party communication protocol
(in Yao's model, `Cslib.Communication.Protocol`) that computes a welfare-maximizing allocation for
every pair of normalized monotone `0/1` valuations over a nonempty finite item set `M` of size
`m = Fintype.card M` requires at least `m.choose (m / 2)` bits of communication in the worst case.

## Precision notes on the printed source

1. **Normalization and `v(M) = 1` in Lemma 11.26 (pp. 288–289):**
   Definition 11.1 (p. 268) requires valuations to be normalized (`v ∅ = 0`) and monotone. In
   Lemma 11.26, the proof shows that a shared protocol leaf on `(v, v*)` and `(u, u*)` forces the
   common allocation `a` to have welfare `0` on `(u, v*)`, concluding `a` is not optimal for
   `(u, v*)`. That final step relies on `v ∅ = 0` so that `(∅, univ)` gives `u ∅ + v* univ = 1 > 0`
   (without normalization, the constant functions `u ≡ 0` and `v ≡ 1` give `u + v* ≡ 0`, refuting
   the literal unnormalized statement; witnessed in
   `CslibFrontierTests.GameTheory.CombinatorialAuctionQueryComm`). Moreover, the dual valuation
   `v*(S) = 1 - v(Sᶜ)` is itself normalized (`v* ∅ = 0`) exactly when `v univ = 1`. Restricting
   `MonotoneZeroOneVal.dual` to valuations with `v.val univ = true` keeps both `v` and `v.dual`
   inside the class of normalized monotone `0/1` valuations, and still includes all
   `2 ^ (m.choose (m / 2))` middle-slice valuations for `m ≥ 2`.
2. **Nonempty item set (`Nonempty M`, i.e., `1 ≤ m`) in Theorem 11.25 (p. 288):**
   when `m = 0`, `0.choose 0 = 1` whereas the unique allocation `(∅, ∅)` is returned in `0` bits
   (checked in `CslibFrontierTests.GameTheory.CombinatorialAuctionQueryComm`). Theorem 11.25 holds
   for every `[Nonempty M]`: `m ≥ 2` follows from Lemma 11.26 on the `2 ^ (m.choose (m / 2))`
   slice valuations, and `m = 1` (`1.choose 0 = 1`) follows because no single allocation is optimal
   for both `(v₁, v₀)` and `(v₀, v₁)`.

## Main definitions

* `Cslib.GameTheory.CombinatorialAuction.MonotoneZeroOneVal`,
  `MonotoneZeroOneVal.toReal`: normalized monotone `0/1` valuations on `Finset M`
  ([BlumrosenNisan2007], Definition 11.1 and §11.6.1, pp. 268 and 287).
* `Cslib.GameTheory.CombinatorialAuction.MonotoneZeroOneVal.dual`: dual valuation
  `v*(S) = 1 - v(Sᶜ)` for `v` satisfying `v(M) = 1` ([BlumrosenNisan2007], §11.6.2, p. 288).
* `Cslib.GameTheory.CombinatorialAuction.OptimalTwoBidderAlloc`: welfare-maximizing allocation
  predicate for two bidders over all `Allocation (Fin 2) M`.

## Main results

* `MonotoneZeroOneVal.toReal_empty`, `MonotoneZeroOneVal.toReal_monotone`,
  `MonotoneZeroOneVal.toReal_add_dual_compl`: normalization, monotonicity, and partition
  complementarity `v(S) + v*(Sᶜ) = 1` ([BlumrosenNisan2007], §11.6.2, p. 288).
* `leaf_dual_ne_of_ne`: **Lemma 11.26** ([BlumrosenNisan2007], §11.6.2, pp. 288–289): distinct
  normalized monotone `0/1` valuations `u ≠ v` with `u(M) = v(M) = 1` cannot lead to the same
  protocol leaf on `(v, v*)` and `(u, u*)`.
* `choose_half_le_depth`, `choose_half_le_ecomplexity`: **Theorem 11.25** ([BlumrosenNisan2007],
  §§11.6.1–11.6.2, pp. 288–289): every deterministic communication protocol finding an optimal
  allocation for all normalized monotone `0/1` valuation pairs over a nonempty finite item set `M`
  uses at least `(Fintype.card M).choose (Fintype.card M / 2)` bits of communication.

## References

* [L. Blumrosen and N. Nisan, *Combinatorial Auctions*][BlumrosenNisan2007], Chapter 11, §11.6,
  pp. 287–289.
-/

public section

namespace Cslib.GameTheory.CombinatorialAuction

open Finset Cslib.Communication

/-! ### Normalized monotone `0/1` valuations and duality (§11.6, pp. 287–288) -/

/-- A normalized monotone `0/1` valuation on item set `M`: `val ∅ = false` and
`S ⊆ T → val S ≤ val T` ([BlumrosenNisan2007], Definition 11.1 and §11.6.1, pp. 268 and 287). -/
@[ext]
structure MonotoneZeroOneVal (M : Type*) where
  /-- Indicator `val S = true` iff bundle `S` has value `1` (otherwise `0`). -/
  val : Finset M → Bool
  /-- Normalization: the empty bundle has value `0`. -/
  empty : val ∅ = false
  /-- Monotonicity ("free disposal"): adding items never lowers the value. -/
  mono : Monotone val

/-- Real-valued valuation `v : Finset M → ℝ` associated with a `MonotoneZeroOneVal`: `1` when
`v.val S = true` and `0` otherwise. -/
@[expose] def MonotoneZeroOneVal.toReal {M : Type*} (v : MonotoneZeroOneVal M)
    (S : Finset M) : ℝ :=
  if v.val S then 1 else 0

/-- Every `MonotoneZeroOneVal` is normalized as a real valuation (`v.toReal ∅ = 0`). -/
@[simp] theorem MonotoneZeroOneVal.toReal_empty {M : Type*} (v : MonotoneZeroOneVal M) :
    v.toReal ∅ = 0 := by
  simp [MonotoneZeroOneVal.toReal, v.empty]

/-- Every `MonotoneZeroOneVal` is monotone as a real valuation. -/
theorem MonotoneZeroOneVal.toReal_monotone {M : Type*} (v : MonotoneZeroOneVal M) :
    Monotone v.toReal := by
  intro S T hST
  have hm := v.mono hST
  unfold MonotoneZeroOneVal.toReal
  cases h1 : v.val S <;> cases h2 : v.val T <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact le_rfl
  · norm_num
  · rw [h1, h2] at hm; exact absurd hm (by decide)
  · exact le_rfl

/-- The *dual valuation* `v*(S) = 1 - v(Sᶜ)` of a normalized monotone `0/1` valuation `v` with
`v(M) = 1` ([BlumrosenNisan2007], §11.6.2, p. 288). Requiring `hv : v.val Finset.univ = true`
ensures that `v.dual hv` is itself normalized (`v*(∅) = 0`), while `v.empty` gives
`v*(M) = 1`. -/
def MonotoneZeroOneVal.dual {M : Type*} [Fintype M] [DecidableEq M]
    (v : MonotoneZeroOneVal M) (hv : v.val Finset.univ = true) : MonotoneZeroOneVal M where
  val S := !(v.val Sᶜ)
  empty := by simp [hv]
  mono S T hST := by
    have hm := v.mono (Finset.compl_subset_compl.mpr hST)
    cases h1 : v.val Sᶜ <;> cases h2 : v.val Tᶜ <;> simp_all

@[simp] theorem MonotoneZeroOneVal.dual_val {M : Type*} [Fintype M] [DecidableEq M]
    (v : MonotoneZeroOneVal M) (hv : v.val Finset.univ = true) (S : Finset M) :
    (v.dual hv).val S = !(v.val Sᶜ) := by
  rfl

theorem MonotoneZeroOneVal.dual_val_univ {M : Type*} [Fintype M] [DecidableEq M]
    (v : MonotoneZeroOneVal M) (hv : v.val Finset.univ = true) :
    (v.dual hv).val Finset.univ = true := by
  simp [v.empty]

/-- Complementarity of a `0/1` valuation and its dual on every partition `(S, Sᶜ)`:
`v(S) + v*(Sᶜ) = 1` ([BlumrosenNisan2007], §11.6.2, property (ii), p. 288). -/
theorem MonotoneZeroOneVal.toReal_add_dual_compl {M : Type*} [Fintype M] [DecidableEq M]
    (v : MonotoneZeroOneVal M) (hv : v.val Finset.univ = true) (S : Finset M) :
    v.toReal S + (v.dual hv).toReal Sᶜ = 1 := by
  unfold MonotoneZeroOneVal.toReal
  simp only [dual_val, compl_compl]
  cases v.val S <;> norm_num

/-- An allocation `a : Allocation (Fin 2) M` is *optimal* for a two-bidder valuation pair
`(v₁, v₂)` if it maximizes social welfare `v₁ (a.bundle 0) + v₂ (a.bundle 1)` over all allocations
`b : Allocation (Fin 2) M` ([BlumrosenNisan2007], §11.6.1, pp. 287–288). -/
@[expose] def OptimalTwoBidderAlloc {M : Type*}
    (v₁ v₂ : Finset M → ℝ) (a : Allocation (Fin 2) M) : Prop :=
  ∀ b : Allocation (Fin 2) M, welfare ![v₁, v₂] b ≤ welfare ![v₁, v₂] a

/-! ### Lemma 11.26: dual-valuation fooling property (§11.6.2, pp. 288–289) -/

section Fooling

variable {M : Type*} [Fintype M] [DecidableEq M]

private def commPartitionAlloc (S : Finset M) : Allocation (Fin 2) M where
  bundle := ![S, Sᶜ]
  disjoint i₁ i₂ hne := by
    fin_cases i₁ <;> fin_cases i₂
    · exact absurd rfl hne
    · exact disjoint_compl_right
    · exact disjoint_compl_left
    · exact absurd rfl hne

private theorem leaf_dual_ne_of_exists_true_false
    {p : Protocol (MonotoneZeroOneVal M) (MonotoneZeroOneVal M) (Allocation (Fin 2) M)}
    (hp : p.Solves (fun v₁ v₂ a => OptimalTwoBidderAlloc v₁.toReal v₂.toReal a)
      {v | v.val Finset.univ = true} {v | v.val Finset.univ = true})
    {u v : MonotoneZeroOneVal M} (hu : u.val Finset.univ = true) (hv : v.val Finset.univ = true)
    (hdiff : ∃ T : Finset M, v.val T = true ∧ u.val T = false) :
    p.leaf v (v.dual hv) ≠ p.leaf u (u.dual hu) := by
  intro hleaf
  obtain ⟨T, hvT, huT⟩ := hdiff
  set i := p.leaf v (v.dual hv)
  have hvA : v ∈ p.leafAlice i := Protocol.mem_leafAlice_leaf
  have hvB : v.dual hv ∈ p.leafBob i := Protocol.mem_leafBob_leaf
  have huA : u ∈ p.leafAlice i := (Protocol.leaf_eq_iff.mp hleaf.symm).1
  have huB : u.dual hu ∈ p.leafBob i := (Protocol.leaf_eq_iff.mp hleaf.symm).2
  set a := p.leafOutput i
  have hrun_vu : p.run v (u.dual hu) = a := Protocol.run_eq_leafOutput hvA huB
  have hrun_uv : p.run u (v.dual hv) = a := Protocol.run_eq_leafOutput huA hvB
  -- On `(v, u*)`, `(T, Tᶜ)` gives welfare `2`, so `a` must also achieve welfare `≥ 2`.
  have hopt_vu : OptimalTwoBidderAlloc v.toReal (u.dual hu).toReal a :=
    hrun_vu ▸ hp v hv (u.dual hu) (u.dual_val_univ hu)
  have hge2 := hopt_vu (commPartitionAlloc T)
  simp only [welfare, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at hge2
  have hpart_vu : v.toReal T + (u.dual hu).toReal Tᶜ = 2 := by
    simp only [MonotoneZeroOneVal.toReal, MonotoneZeroOneVal.dual_val, compl_compl, hvT, huT]
    norm_num
  have h0 : (commPartitionAlloc T).bundle 0 = T := rfl
  have h1 : (commPartitionAlloc T).bundle 1 = Tᶜ := rfl
  rw [h0, h1, hpart_vu] at hge2
  have hva0 : v.val (a.bundle 0) = true := by
    unfold MonotoneZeroOneVal.toReal at hge2
    cases h : v.val (a.bundle 0) <;> cases h' : (u.dual hu).val (a.bundle 1) <;>
      simp only [h, h', Bool.false_eq_true, ↓reduceIte] at hge2
    · norm_num at hge2
    · norm_num at hge2
    · norm_num at hge2
    · rfl
  have hua1 : u.val (a.bundle 1)ᶜ = false := by
    unfold MonotoneZeroOneVal.toReal at hge2
    cases h : v.val (a.bundle 0) <;> cases h' : (u.dual hu).val (a.bundle 1) <;>
      simp only [h, h', Bool.false_eq_true, ↓reduceIte] at hge2
    · norm_num at hge2
    · norm_num at hge2
    · norm_num at hge2
    · simpa [MonotoneZeroOneVal.dual_val] using h'
  -- Disjointness gives `a.bundle 0 ⊆ (a.bundle 1)ᶜ`, forcing welfare `0` on `(u, v*)`.
  have hsub : a.bundle 0 ⊆ (a.bundle 1)ᶜ :=
    Finset.subset_compl_iff_disjoint_right.mpr (a.disjoint (by decide : (0 : Fin 2) ≠ 1))
  have hua0 : u.val (a.bundle 0) = false := by
    have hm := u.mono hsub
    rw [hua1] at hm
    cases h : u.val (a.bundle 0)
    · rfl
    · rw [h] at hm; exact absurd hm (by decide)
  have hva1c : v.val (a.bundle 1)ᶜ = true := by
    have hm := v.mono hsub
    rw [hva0] at hm
    cases h : v.val (a.bundle 1)ᶜ
    · rw [h] at hm; exact absurd hm (by decide)
    · rfl
  have ha_zero : welfare ![u.toReal, (v.dual hv).toReal] a = 0 := by
    simp [welfare, Fin.sum_univ_two, MonotoneZeroOneVal.toReal, hua0, hva1c]
  -- On `(u, v*)`, `(∅, univ)` achieves welfare `1` since `v*(univ) = 1 - v(∅) = 1`.
  have hopt_uv : OptimalTwoBidderAlloc u.toReal (v.dual hv).toReal a :=
    hrun_uv ▸ hp u hu (v.dual hv) (v.dual_val_univ hv)
  have hge1 := hopt_uv (commPartitionAlloc ∅)
  rw [ha_zero] at hge1
  simp only [welfare, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at hge1
  have h0e : (commPartitionAlloc (∅ : Finset M)).bundle 0 = ∅ := rfl
  have h1e : (commPartitionAlloc (∅ : Finset M)).bundle 1 = Finset.univ := by
    simp [commPartitionAlloc]
  rw [h0e, h1e, u.toReal_empty] at hge1
  simp only [MonotoneZeroOneVal.toReal, v.dual_val_univ hv, ↓reduceIte, zero_add] at hge1
  linarith

/-- **Lemma 11.26** ([BlumrosenNisan2007], §11.6.2, pp. 288–289): if `p` is a deterministic
communication protocol that finds a welfare-maximizing allocation on every pair of normalized
monotone `0/1` valuations with `v(M) = 1`, then distinct valuations `u ≠ v` reach distinct leaves
on `(v, v.dual hv)` and `(u, u.dual hu)`. -/
theorem leaf_dual_ne_of_ne
    {p : Protocol (MonotoneZeroOneVal M) (MonotoneZeroOneVal M) (Allocation (Fin 2) M)}
    (hp : p.Solves (fun v₁ v₂ a => OptimalTwoBidderAlloc v₁.toReal v₂.toReal a)
      {v | v.val Finset.univ = true} {v | v.val Finset.univ = true})
    {u v : MonotoneZeroOneVal M} (hu : u.val Finset.univ = true) (hv : v.val Finset.univ = true)
    (hne : u ≠ v) :
    p.leaf v (v.dual hv) ≠ p.leaf u (u.dual hu) := by
  have hex : ∃ T : Finset M, v.val T ≠ u.val T := by
    by_contra hall
    push Not at hall
    exact hne (MonotoneZeroOneVal.ext (funext fun T => (hall T).symm))
  obtain ⟨T, hT⟩ := hex
  cases hvT : v.val T <;> cases huT : u.val T
  · exact absurd (hvT.trans huT.symm) hT
  · exact (leaf_dual_ne_of_exists_true_false hp hv hu ⟨T, huT, hvT⟩).symm
  · exact leaf_dual_ne_of_exists_true_false hp hu hv ⟨T, hvT, huT⟩
  · exact absurd (hvT.trans huT.symm) hT

/-! ### Theorem 11.25: exponential communication lower bound (§§11.6.1–11.6.2, pp. 288–289) -/

/-- Middle-slice monotone `0/1` valuation for `2 ≤ Fintype.card M`: assigns `0` to bundles of size
`< m / 2`, `1` to bundles of size `> m / 2`, and `S ∈ A` on bundles of size `m / 2`. -/
private def sliceVal (hm : 2 ≤ Fintype.card M) (A : Finset (Finset M)) : MonotoneZeroOneVal M where
  val S :=
    if Fintype.card M / 2 < S.card then true
    else if S.card = Fintype.card M / 2 then decide (S ∈ A)
    else false
  empty := by
    have hnot1 : ¬ Fintype.card M / 2 < 0 := by omega
    have hnot2 : 0 ≠ Fintype.card M / 2 := by omega
    simp only [Finset.card_empty, hnot1, hnot2, ↓reduceIte]
  mono S T hST := by
    have hcard := Finset.card_le_card hST
    dsimp only
    split_ifs with h1 h2 h3 h4 h5 h6
    · exact le_rfl
    · omega
    · omega
    · exact Bool.le_true _
    · have hEq : S = T := Finset.eq_of_subset_of_card_le hST (by omega)
      rw [hEq]
    · omega
    · exact Bool.false_le _
    · exact Bool.false_le _
    · exact le_rfl

private theorem sliceVal_univ (hm : 2 ≤ Fintype.card M) (A : Finset (Finset M)) :
    (sliceVal hm A).val Finset.univ = true := by
  have hlt : Fintype.card M / 2 < Fintype.card M := by omega
  simp [sliceVal, hlt]

private theorem sliceVal_injOn (hm : 2 ≤ Fintype.card M) :
    Set.InjOn (sliceVal hm)
      ((Finset.powersetCard (Fintype.card M / 2) (Finset.univ : Finset M)).powerset :
        Set (Finset (Finset M))) := by
  intro A hA B hB hEq
  have hA' : A ⊆ Finset.powersetCard (Fintype.card M / 2) (Finset.univ : Finset M) :=
    Finset.mem_powerset.mp (Finset.mem_coe.mp hA)
  have hB' : B ⊆ Finset.powersetCard (Fintype.card M / 2) (Finset.univ : Finset M) :=
    Finset.mem_powerset.mp (Finset.mem_coe.mp hB)
  ext S
  by_cases hcard : S.card = Fintype.card M / 2
  · have hS := congrFun (congrArg MonotoneZeroOneVal.val hEq) S
    simp only [sliceVal, hcard, lt_irrefl, ↓reduceIte, decide_eq_decide] at hS
    exact hS
  · have hnotA : S ∉ A := fun h => hcard (Finset.mem_powersetCard.mp (hA' h)).2
    have hnotB : S ∉ B := fun h => hcard (Finset.mem_powersetCard.mp (hB' h)).2
    exact iff_of_false hnotA hnotB

end Fooling

private theorem choose_half_le_depth_of_two_le {M : Type*} [Fintype M] (hm : 2 ≤ Fintype.card M)
    {p : Protocol (MonotoneZeroOneVal M) (MonotoneZeroOneVal M) (Allocation (Fin 2) M)}
    (hp : p.Solves (fun v₁ v₂ a => OptimalTwoBidderAlloc v₁.toReal v₂.toReal a)
      {v | v.val Finset.univ = true} {v | v.val Finset.univ = true}) :
    (Fintype.card M).choose (Fintype.card M / 2) ≤ p.depth := by
  classical
  set F := (Finset.powersetCard (Fintype.card M / 2) (Finset.univ : Finset M)).powerset
  let f : Finset (Finset M) → Fin p.leafCount :=
    fun A => p.leaf (sliceVal hm A) ((sliceVal hm A).dual (sliceVal_univ hm A))
  have hinj : Set.InjOn f (F : Set (Finset (Finset M))) := by
    intro A hA B hB hf
    by_contra hne
    have hvne : sliceVal hm A ≠ sliceVal hm B := fun h => hne (sliceVal_injOn hm hA hB h)
    exact leaf_dual_ne_of_ne hp (sliceVal_univ hm B) (sliceVal_univ hm A) hvne.symm hf
  have hpow : 2 ^ (Fintype.card M).choose (Fintype.card M / 2) ≤ 2 ^ p.depth := by
    calc 2 ^ (Fintype.card M).choose (Fintype.card M / 2)
        = F.card := by
            simp only [F, Finset.card_powerset, Finset.card_powersetCard, Finset.card_univ]
      _ ≤ (Finset.univ : Finset (Fin p.leafCount)).card :=
            Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) hinj
      _ = p.leafCount := by rw [Finset.card_univ, Fintype.card_fin]
      _ ≤ 2 ^ p.depth := p.leafCount_le_two_pow_depth
  exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp hpow

/-- **Theorem 11.25 (protocol depth form)** ([BlumrosenNisan2007], §§11.6.1–11.6.2, pp. 288–289):
every deterministic two-party communication protocol finding a welfare-maximizing allocation for
every pair of normalized monotone `0/1` valuations on a nonempty finite item set `M` has depth at
least `(Fintype.card M).choose (Fintype.card M / 2)`. -/
theorem choose_half_le_depth {M : Type*} [Fintype M] [Nonempty M]
    {p : Protocol (MonotoneZeroOneVal M) (MonotoneZeroOneVal M) (Allocation (Fin 2) M)}
    (hp : p.Solves (fun v₁ v₂ a => OptimalTwoBidderAlloc v₁.toReal v₂.toReal a)
      Set.univ Set.univ) :
    (Fintype.card M).choose (Fintype.card M / 2) ≤ p.depth := by
  classical
  by_cases hm : 2 ≤ Fintype.card M
  · exact choose_half_le_depth_of_two_le hm (hp.mono (Set.subset_univ _) (Set.subset_univ _))
  · have hcard1 : Fintype.card M = 1 := by
      have hpos : 0 < Fintype.card M := Fintype.card_pos
      omega
    rw [hcard1]
    simp only [Nat.reduceDiv, Nat.choose_zero_right]
    -- When `|M| = 1`, depth `0` would output a single allocation `a` optimal for both
    -- `(vOne, vZero)` and `(vZero, vOne)`, forcing the unique item into both `a.bundle 0` and
    -- `a.bundle 1`.
    cases p with
    | output a =>
      exfalso
      let vZero : MonotoneZeroOneVal M := ⟨fun _ => false, rfl, fun _ _ _ => le_rfl⟩
      let vOne : MonotoneZeroOneVal M :=
        ⟨fun S => decide S.Nonempty, by simp, fun S T hST => by
          by_cases hS : S.Nonempty
          · simp [hS, hS.mono hST]
          · simp [hS]⟩
      have h10 := hp vOne trivial vZero trivial (commPartitionAlloc Finset.univ)
      have h01 := hp vZero trivial vOne trivial (commPartitionAlloc ∅)
      simp only [Protocol.run_output, welfare, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one] at h10 h01
      have h0u : (commPartitionAlloc (Finset.univ : Finset M)).bundle 0 = Finset.univ := rfl
      have h1e : (commPartitionAlloc (∅ : Finset M)).bundle 1 = Finset.univ := by
        simp [commPartitionAlloc]
      rw [h0u] at h10
      rw [h1e] at h01
      have hne0 : (a.bundle 0).Nonempty := by
        by_contra h
        simp only [MonotoneZeroOneVal.toReal, vOne, vZero, Finset.univ_nonempty, decide_true,
          ↓reduceIte, Bool.false_eq_true, add_zero, h, decide_false] at h10
        linarith
      have hne1 : (a.bundle 1).Nonempty := by
        by_contra h
        simp only [MonotoneZeroOneVal.toReal, vOne, vZero, Finset.univ_nonempty, decide_true,
          ↓reduceIte, Bool.false_eq_true, zero_add, h, decide_false] at h01
        linarith
      obtain ⟨x, hx⟩ := hne0
      obtain ⟨y, hy⟩ := hne1
      have hsub : Subsingleton M := Fintype.card_le_one_iff_subsingleton.mp hcard1.le
      have hxy : x = y := Subsingleton.elim x y
      exact Finset.disjoint_left.mp (a.disjoint (by decide : (0 : Fin 2) ≠ 1)) hx (hxy ▸ hy)
    | alice _ _ _ | bob _ _ _ =>
      simp only [Protocol.depth_alice, Protocol.depth_bob]
      omega

/-- **Theorem 11.25 (communication complexity form)** ([BlumrosenNisan2007], §§11.6.1–11.6.2,
pp. 288–289): the deterministic two-party communication complexity (`Protocol.ecomplexity`) of
finding a welfare-maximizing allocation for normalized monotone `0/1` valuations on any nonempty
finite item set `M` is at least `(Fintype.card M).choose (Fintype.card M / 2)` bits. -/
theorem choose_half_le_ecomplexity (M : Type*) [Fintype M] [Nonempty M] :
    (((Fintype.card M).choose (Fintype.card M / 2) : ℕ) : ℕ∞) ≤
      Protocol.ecomplexity
        (fun (v₁ v₂ : MonotoneZeroOneVal M) (a : Allocation (Fin 2) M) =>
          OptimalTwoBidderAlloc v₁.toReal v₂.toReal a)
        Set.univ Set.univ :=
  Protocol.le_ecomplexity_iff.mpr fun _ hp => Nat.cast_le.mpr (choose_half_le_depth hp)

end Cslib.GameTheory.CombinatorialAuction
