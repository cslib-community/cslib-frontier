/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.ParityCheck
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Lindsey
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Odd circuits and one extra parity check

A finite set `S` of vectors is a *zero-sum circuit* (`Cslib.Code.IsZeroSumCircuit`) when it is
nonempty, sums to zero, and no nonempty proper subset sums to zero. Over `𝔽₂ = ZMod 2` these are
exactly the inclusion-minimal linearly dependent sets of vectors.

Saglam's refinement of the folklore union-bound argument for linear codes [Saglam2027] rests on
two facts about a finite set `K` of vectors over `𝔽₂`.

* If every zero-sum subset of `K` has even size, then one more parity check maps every element
  of `K` to `1`: there is `v` with `v ⬝ᵥ x = 1` for all `x ∈ K`
  (`Cslib.Code.exists_dotProduct_eq_one_of_even`). Every odd zero-sum subset contains an odd
  circuit (`Cslib.Code.exists_isZeroSumCircuit_odd`), so it suffices that `K` contains no odd
  circuit.
* A circuit `S` spans a space of dimension at least `|S| - 1`
  (`Cslib.Code.card_sub_one_le_finrank_span`), so a uniformly random `m`-row matrix kills all of
  `S` with probability at most `2 ^ (-m (|S| - 1))`
  (`Cslib.Code.card_filter_forall_mulVec_eq_zero_mul_le`).

Counting matrices then gives: if the odd circuits `S` of a finite set `B` satisfy
`∑_S 2 ^ (-m (|S| - 1)) < 1`, some `M ∈ 𝔽₂^{m × ι}` leaves no odd circuit of `B` in its kernel,
and appending the extra row to `M` gives an `(m + 1)`-row matrix whose kernel misses `B`
(`Cslib.Code.exists_mulVec_ne_zero_of_sum_lt_one`). For `B` the nonzero words of weight less than
`d` this is a parity-check matrix of a linear code of minimum distance at least `d`
(`Cslib.Code.exists_le_minDist_parityCheckCode_of_sum_lt_one`). This is the deterministic part of
[Saglam2027, Sections 1–2]; the sum is the expected number `𝔼 Z` of odd circuits in the kernel,
bounded there by Fourier analysis (`Cslib.Code.OddCircuitFourier`).

## Main definitions

* `Cslib.Code.IsZeroSumCircuit`: a nonempty zero-sum finite set with no nonempty proper zero-sum
  subset.

## Main results

* `Cslib.Code.exists_isZeroSumCircuit_odd`: an odd zero-sum set contains an odd circuit.
* `Cslib.Code.exists_dotProduct_eq_one_of_even`: without odd dependencies, one linear form is `1`
  on every vector.
* `Cslib.Code.card_sub_one_le_finrank_span`: the rank of a circuit.
* `Cslib.Code.card_filter_forall_mulVec_eq_zero_mul_le`: few matrices kill a circuit.
* `Cslib.Code.exists_mulVec_ne_zero_of_sum_lt_one`,
  `Cslib.Code.exists_le_minDist_parityCheckCode_of_sum_lt_one`: the odd-circuit existence
  argument.

## References

* [M. Saglam, *Linear codes exceeding the Gilbert–Varshamov bound*][Saglam2027], STOC 2027
  submission 1516, Sections 1–2.
-/

public section

namespace Cslib.Code

open Finset Matrix

section Circuit

variable {G : Type*} [AddCommGroup G]

/-- A *zero-sum circuit*: a nonempty finite set `S` whose elements sum to zero while no nonempty
proper subset of `S` sums to zero. Over `ZMod 2` these are the inclusion-minimal linearly dependent
sets of vectors. -/
def IsZeroSumCircuit (S : Finset G) : Prop :=
  S.Nonempty ∧ ∑ x ∈ S, x = 0 ∧ ∀ T ⊂ S, T.Nonempty → ∑ x ∈ T, x ≠ 0

theorem isZeroSumCircuit_iff {S : Finset G} :
    IsZeroSumCircuit S ↔
      S.Nonempty ∧ ∑ x ∈ S, x = 0 ∧ ∀ T ⊂ S, T.Nonempty → ∑ x ∈ T, x ≠ 0 :=
  Iff.rfl

/-- A zero-sum circuit sums to zero. -/
theorem IsZeroSumCircuit.sum_eq_zero {S : Finset G} (hS : IsZeroSumCircuit S) :
    ∑ x ∈ S, x = 0 :=
  hS.2.1

instance [DecidableEq G] : DecidablePred (IsZeroSumCircuit (G := G)) := fun S =>
  decidable_of_iff (S.Nonempty ∧ ∑ x ∈ S, x = 0 ∧ ∀ T ∈ S.ssubsets, T.Nonempty → ∑ x ∈ T, x ≠ 0)
    (by simp [IsZeroSumCircuit])

/-- **Odd zero-sum sets contain odd circuits** [Saglam2027, Section 2]. A smallest odd zero-sum
subset is a circuit: removing a nonempty zero-sum proper subset would leave a smaller odd one. -/
theorem exists_isZeroSumCircuit_odd {T : Finset G} (hT : ∑ x ∈ T, x = 0) (hodd : Odd #T) :
    ∃ S ⊆ T, IsZeroSumCircuit S ∧ Odd #S := by
  classical
  induction hn : #T using Nat.strong_induction_on generalizing T with
  | _ n ih =>
    subst hn
    by_cases hc : ∀ U ⊂ T, U.Nonempty → ∑ x ∈ U, x ≠ 0
    · exact ⟨T, Subset.rfl, ⟨card_pos.1 hodd.pos, hT, hc⟩, hodd⟩
    push Not at hc
    obtain ⟨U, hUT, hU, hU0⟩ := hc
    rcases Nat.even_or_odd #U with heven | hUodd
    · -- The complement of an even zero-sum subset is a smaller odd zero-sum subset.
      have hsub : T \ U ⊂ T := sdiff_ssubset hUT.subset hU
      have hcard : Odd #(T \ U) :=
        card_sdiff_of_subset hUT.subset ▸ Nat.Odd.sub_even (card_le_card hUT.subset) hodd heven
      obtain ⟨S, hS, hSc, hSodd⟩ := ih _ (card_lt_card hsub)
        (by rw [sum_sdiff_eq_sub hUT.subset, hT, hU0, sub_zero]) hcard rfl
      exact ⟨S, hS.trans hsub.subset, hSc, hSodd⟩
    · obtain ⟨S, hS, hSc, hSodd⟩ := ih _ (card_lt_card hUT) hU0 hUodd rfl
      exact ⟨S, hS.trans hUT.subset, hSc, hSodd⟩

end Circuit

section ZModTwo

variable {G : Type*} [AddCommGroup G] [Module (ZMod 2) G]

/-- Over `𝔽₂`, a linear combination is the sum of the vectors with nonzero coefficient. -/
theorem sum_zmodTwo_smul_eq_sum_filter {α : Type*} (s : Finset α) (a : α → ZMod 2) (f : α → G) :
    ∑ i ∈ s, a i • f i = ∑ i ∈ s with a i ≠ 0, f i := by
  classical
  rw [sum_filter]
  refine sum_congr rfl fun i _ => ?_
  by_cases h : a i = 0
  · simp [h]
  · have h1 : a i = 1 := by revert h; generalize a i = z; decide +revert
    simp [h1]

/-- Over `𝔽₂`, the sum of the coefficients is the parity of the number of nonzero ones. -/
theorem sum_zmodTwo_eq_card_filter {α : Type*} (s : Finset α) (a : α → ZMod 2) :
    ∑ i ∈ s, a i = (#{i ∈ s | a i ≠ 0} : ZMod 2) := by
  classical
  simpa using sum_zmodTwo_smul_eq_sum_filter s a (fun _ => (1 : ZMod 2))

/-- Over `𝔽₂`, a finite set in which no nonempty subset sums to zero is linearly independent. -/
theorem linearIndepOn_of_forall_sum_ne_zero {s : Finset G}
    (hs : ∀ T ⊆ s, T.Nonempty → ∑ x ∈ T, x ≠ 0) : LinearIndepOn (ZMod 2) id (s : Set G) := by
  rw [linearIndepOn_finset_iff]
  exact fun a ha i hi => by_contra fun hai =>
    hs _ (filter_subset _ _) ⟨i, mem_filter.2 ⟨hi, hai⟩⟩
      (sum_zmodTwo_smul_eq_sum_filter s a id ▸ ha)

/-- **The rank of a circuit** [Saglam2027, Section 2]. Removing one element of a zero-sum circuit
leaves a linearly independent set, so the circuit spans a space of dimension at least `|S| - 1`
(in fact exactly `|S| - 1`). -/
theorem card_sub_one_le_finrank_span {S : Finset G} (hS : IsZeroSumCircuit S) :
    #S - 1 ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (S : Set G)) := by
  classical
  obtain ⟨⟨x, hx⟩, -, hmin⟩ := hS
  have hind : LinearIndepOn (ZMod 2) id ((S.erase x : Finset G) : Set G) :=
    linearIndepOn_of_forall_sum_ne_zero fun T hT => hmin T (hT.trans_ssubset (erase_ssubset hx))
  have : FiniteDimensional (ZMod 2) (Submodule.span (ZMod 2) (S : Set G)) :=
    FiniteDimensional.span_finset (ZMod 2) S
  have hle : Submodule.span (ZMod 2) ((S.erase x : Finset G) : Set G) ≤
      Submodule.span (ZMod 2) (S : Set G) := Submodule.span_mono (by simp)
  rw [← card_erase_of_mem hx, show #(S.erase x) =
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ((S.erase x : Finset G) : Set G)) by
    rw [finrank_span_set_eq_card hind]; exact congrArg _ (by ext; simp [and_comm])]
  exact Submodule.finrank_mono hle

end ZModTwo

section Vectors

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **One extra parity check** [Saglam2027, Section 2]. If every zero-sum subset of a finite set
`K` of vectors over `𝔽₂` has even size, then some vector `v` has `v ⬝ᵥ x = 1` for every `x ∈ K`:
the all-ones row lies in the row space of the matrix whose columns are the elements of `K`. -/
theorem exists_dotProduct_eq_one_of_even {K : Finset (ι → ZMod 2)}
    (hK : ∀ T ⊆ K, ∑ x ∈ T, x = 0 → Even #T) : ∃ v : ι → ZMod 2, ∀ x ∈ K, v ⬝ᵥ x = 1 := by
  classical
  -- Coefficient vectors `a : K → 𝔽₂`; `L i a` is coordinate `i` of `∑ a x • x`.
  let comb : (K → ZMod 2) →ₗ[ZMod 2] ι → ZMod 2 :=
    Fintype.linearCombination (ZMod 2) fun x : K => (x : ι → ZMod 2)
  let L : ι → (K → ZMod 2) →ₗ[ZMod 2] ZMod 2 := fun i => (LinearMap.proj i).comp comb
  let ones : (K → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    Fintype.linearCombination (ZMod 2) fun _ : K => (1 : ZMod 2)
  have hker : ⨅ i, LinearMap.ker (L i) ≤ LinearMap.ker ones := fun a ha => by
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, L, LinearMap.comp_apply,
      LinearMap.proj_apply] at ha
    have hsum : ∑ x : K, a x • (x : ι → ZMod 2) = 0 :=
      funext fun i => by simpa [comb, Fintype.linearCombination_apply] using ha i
    rw [sum_zmodTwo_smul_eq_sum_filter] at hsum
    have heven := hK ((univ.filter fun x : K => a x ≠ 0).map (.subtype _))
      (fun _ hy => by obtain ⟨x, -, rfl⟩ := mem_map.1 hy; exact x.2) (by rwa [sum_map])
    rw [card_map] at heven
    simp only [LinearMap.mem_ker, ones, Fintype.linearCombination_apply, smul_eq_mul, mul_one,
      sum_zmodTwo_eq_card_filter, ZMod.natCast_eq_zero_iff_even.2 heven]
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1
    (mem_span_of_iInf_ker_le_ker hker)
  exact ⟨c, fun x hx => by
    simpa [L, comb, ones, Fintype.linearCombination_apply_single, dotProduct] using
      LinearMap.congr_fun hc (Pi.single ⟨x, hx⟩ 1)⟩

/-- **Few matrices kill a circuit** [Saglam2027, Section 2]. At most a `2 ^ (-m (|S| - 1))`
fraction of the matrices with `m` rows over `𝔽₂` kill every vector of a zero-sum circuit `S`. -/
theorem card_filter_forall_mulVec_eq_zero_mul_le {S : Finset (ι → ZMod 2)} (hS : IsZeroSumCircuit S)
    (m : ℕ) :
    #{M : Matrix (Fin m) ι (ZMod 2) | ∀ x ∈ S, M *ᵥ x = 0} * 2 ^ (m * (#S - 1)) ≤
      2 ^ (m * Fintype.card ι) := by
  classical
  -- The rows orthogonal to `S` form the kernel of the matrix whose rows are the elements of `S`.
  let B : Matrix S ι (ZMod 2) := Matrix.of fun x => (x : ι → ZMod 2)
  have hrows : #{r : ι → ZMod 2 | ∀ x ∈ S, r ⬝ᵥ x = 0} = #{r : ι → ZMod 2 | B *ᵥ r = 0} :=
    congrArg card <| Finset.ext fun r => by
      simp only [mem_filter, mem_univ, true_and, funext_iff, Pi.zero_apply]
      exact ⟨fun h x => by simpa [B, mulVec, dotProduct_comm] using h x x.2,
        fun h x hx => by simpa [B, mulVec, dotProduct_comm] using h ⟨x, hx⟩⟩
  have hrank :
      B.rank = Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (↑S : Set (ι → ZMod 2))) := by
    rw [rank_eq_finrank_span_row, show Set.range B.row = (↑S : Set (ι → ZMod 2)) from
      Set.ext fun x => ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩]
  rw [card_filter_forall_mulVec_eq_zero, pow_mul', pow_mul', ← mul_pow]
  refine Nat.pow_le_pow_left ?_ m
  exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right two_pos
    (card_sub_one_le_finrank_span hS))).trans_eq (hrank ▸ hrows ▸ card_ker_mul_two_pow_rank B)

omit [DecidableEq ι] in
/-- **The odd-circuit existence argument** [Saglam2027, Sections 1–2]. Let `B` be a finite set of
vectors over `𝔽₂`. If its odd zero-sum circuits `S` satisfy `∑_S 2 ^ (-m (|S| - 1)) < 1`, then
some `(m + 1)`-row matrix `H` maps every element of `B` to a nonzero vector.

The sum bounds the expected number of odd circuits of `B` inside the kernel of a uniformly random
`m`-row matrix `M`. Some `M` therefore has none, and then every zero-sum subset of `B ∩ ker M` is
even, so one extra row `v` with `v ⬝ᵥ x = 1` on `B ∩ ker M` completes `H`. The hypothesis forces
`0 ∉ B`, as `{0}` is an odd circuit. -/
theorem exists_mulVec_ne_zero_of_sum_lt_one (B : Finset (ι → ZMod 2)) (m : ℕ)
    (h : ∑ S ∈ B.powerset with IsZeroSumCircuit S ∧ Odd #S, ((2 : ℝ) ^ m)⁻¹ ^ (#S - 1) < 1) :
    ∃ H : Matrix (Fin (m + 1)) ι (ZMod 2), ∀ x ∈ B, H *ᵥ x ≠ 0 := by
  classical
  set C := {S ∈ B.powerset | IsZeroSumCircuit S ∧ Odd #S} with hC
  -- `Z M` counts the odd circuits of `B` in the kernel of `M`.
  let Z : Matrix (Fin m) ι (ZMod 2) → ℕ := fun M => #{S ∈ C | ∀ x ∈ S, M *ᵥ x = 0}
  have hlt : ∑ M, (Z M : ℝ) < ∑ _M : Matrix (Fin m) ι (ZMod 2), (1 : ℝ) := by
    have hcard : (Fintype.card (Matrix (Fin m) ι (ZMod 2)) : ℝ) = 2 ^ (m * Fintype.card ι) := by
      change ((Fintype.card (Fin m → ι → ZMod 2) : ℕ) : ℝ) = _
      simp [ZMod.card, ← pow_mul, mul_comm]
    rw [sum_const, card_univ, nsmul_eq_mul, mul_one, hcard, ← Nat.cast_sum]
    simp only [Z, card_filter]
    rw [sum_comm, Nat.cast_sum]
    refine (sum_le_sum (g := fun S => (2 : ℝ) ^ (m * Fintype.card ι) * ((2 : ℝ) ^ m)⁻¹ ^ (#S - 1))
      fun S hS => ?_).trans_lt ?_
    · rw [← card_filter, inv_pow, ← pow_mul, le_mul_inv_iff₀ (by positivity)]
      exact_mod_cast card_filter_forall_mulVec_eq_zero_mul_le (mem_filter.1 hS).2.1 m
    · rw [← mul_sum]
      exact (mul_lt_mul_of_pos_left h (by positivity)).trans_eq (mul_one _)
  obtain ⟨M, -, hM⟩ := exists_lt_of_sum_lt hlt
  have hZ : Z M = 0 := Nat.lt_one_iff.1 (by exact_mod_cast hM)
  -- Inside `K = B ∩ ker M` every zero-sum subset is even.
  have heven : ∀ T ⊆ {x ∈ B | M *ᵥ x = 0}, ∑ x ∈ T, x = 0 → Even #T := fun T hT hT0 => by
    by_contra hodd
    obtain ⟨S, hST, hS, hSodd⟩ := exists_isZeroSumCircuit_odd hT0 (Nat.not_even_iff_odd.1 hodd)
    have hmem : S ∈ {S ∈ C | ∀ x ∈ S, M *ᵥ x = 0} :=
      mem_filter.2 ⟨mem_filter.2 ⟨mem_powerset.2 fun x hx => (mem_filter.1 (hT (hST hx))).1,
        hS, hSodd⟩, fun x hx => (mem_filter.1 (hT (hST hx))).2⟩
    exact absurd (card_pos.2 ⟨S, hmem⟩) (by omega : ¬0 < Z M)
  obtain ⟨v, hv⟩ := exists_dotProduct_eq_one_of_even heven
  refine ⟨Matrix.of (vecCons v fun i => M i), fun x hx h0 => ?_⟩
  have hMx : M *ᵥ x = 0 := funext fun i => by simpa [mulVec] using congr_fun h0 i.succ
  have hvx : v ⬝ᵥ x = 0 := by simpa [mulVec] using congr_fun h0 0
  exact one_ne_zero (hv x (mem_filter.2 ⟨hx, hMx⟩) ▸ hvx)

/-- **Codes from the odd-circuit argument** [Saglam2027, Sections 1–2]. If the odd zero-sum
circuits `S` among the nonzero words of weight less than `d` satisfy
`∑_S 2 ^ (-m (|S| - 1)) < 1`, then some `(m + 1)`-row parity-check matrix over `𝔽₂` defines a
linear code of minimum distance at least `d`, with at least `2 ^ (|ι| - (m + 1))` codewords. -/
theorem exists_le_minDist_parityCheckCode_of_sum_lt_one (d m : ℕ)
    (h : ∑ S ∈ ({x : ι → ZMod 2 | x ≠ 0 ∧ hammingNorm x < d} : Finset _).powerset
      with IsZeroSumCircuit S ∧ Odd #S, ((2 : ℝ) ^ m)⁻¹ ^ (#S - 1) < 1) :
    ∃ H : Matrix (Fin (m + 1)) ι (ZMod 2),
      (d : ℕ∞) ≤ minDist (parityCheckCode H : Set (ι → ZMod 2)) ∧
        2 ^ (Fintype.card ι - (m + 1)) ≤ Nat.card (parityCheckCode H) := by
  obtain ⟨H, hH⟩ := exists_mulVec_ne_zero_of_sum_lt_one _ m h
  refine ⟨H, (le_minDist_iff_hammingNorm _).2 fun x hx hx0 => not_lt.1 fun hlt => ?_,
    by simpa [ZMod.card] using pow_sub_le_card_parityCheckCode H⟩
  exact hH x (by simp [hx0, Nat.cast_lt.1 hlt]) (mem_parityCheckCode.1 hx)

end Vectors

end Cslib.Code
