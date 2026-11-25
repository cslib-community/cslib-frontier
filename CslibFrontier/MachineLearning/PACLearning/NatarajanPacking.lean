/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.NatarajanDimension
public import CslibFrontier.MachineLearning.PACLearning.Packing
import CslibFrontier.Foundations.Data.Nat.Choose.Real

/-!
# Packing and covering numbers of multiclass Natarajan classes

Fix sample points `x : Fin m → α` and a multiclass concept class `C : ConceptClass α β` over a
finite label alphabet `β` (`k = Fintype.card β`). A finite set `P` of labelings realized by `C` on
`x` is *`ε`-separated* if distinct members of `P` differ on at least `ε m` sample coordinates.

Combining the polymorphic coordinate-subsampling lemma `exists_injOn_comp_of_two_mul_log_card_lt`
from `CslibFrontier/MachineLearning/PACLearning/Packing.lean` with Natarajan's lemma
(`ncard_restriction_le_natarajanSum` in
`CslibFrontier/MachineLearning/PACLearning/NatarajanDimension.lean`) extends Dudley's sample-size-
independent packing and covering bounds from binary VC classes to arbitrary finite-alphabet
multiclass classes:

1. **Exponential-polynomial bound on `natarajanSum`** (`natarajanSum_le_exp_mul_pow`): for every
   real `T ≥ 1`, `natarajanSum n k d ≤ exp (n / T) · (T · max 1 (k choose 2)) ^ d` (and with
   `k ≥ 2`, `max 1 (k choose 2) = k choose 2`).
2. **Subsampling to `natarajanSum`** (`card_le_natarajanSum_of_two_mul_log_card_lt`): when
   `2 log |P| < ε r`, some `r` sample positions distinguish all words of `P`, giving
   `|P| ≤ natarajanSum r |β| d`.
3. **Sample-size-independent Natarajan packing bound** (`card_le_div_pow_of_natarajanShatters`):
   choosing `r = ⌊2 log |P| / ε⌋ + 1` and `T = 4 / ε` yields
   `|P| ≤ (8 · max 1 (|β| choose 2) / ε) ^ (2 d)` for `0 < ε ≤ 1`, independent of `m`. When
   `|β| ≥ 2` (`card_le_div_pow_of_natarajanShatters_of_two_le`), this is
   `(8 · (|β| choose 2) / ε) ^ (2 d)`, which at `β = Bool` (`2 choose 2 = 1`) specializes directly
   to the binary bound `(8 / ε) ^ (2 d)` of `card_le_div_pow_of_le_hammingDist`.
4. **Multiclass Hamming covering numbers** (`exists_covering_of_natarajanShatters`): a maximal
   separated subset at radius `⌊ε m⌋` is an `ε m`-Hamming net of `(· ∘ x) '' C` obeying the same
   cardinality bound.

## Main results

- `natarajanSum_le_exp_mul_pow`: exponential-polynomial upper bound on `natarajanSum`.
- `card_le_natarajanSum_of_two_mul_log_card_lt`: subsampling bound for `ε`-separated multiclass
  labelings.
- `card_le_div_pow_of_natarajanShatters`, `card_le_div_pow_of_natarajanShatters_of_two_le`,
  `card_le_div_pow_of_hasFiniteNatarajanDim`: sample-size-independent packing bounds for classes of
  bounded Natarajan dimension.
- `exists_covering_of_natarajanShatters`: multiclass Hamming covering-net bound on a sample.

## References

* [B. K. Natarajan, *On learning sets and functions*][Natarajan1989]
* [R. Vershynin, *High-Dimensional Probability*][Vershynin2018], Section 8.3
* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014], Section 29.1
-/

public section

open Finset

namespace Cslib.MachineLearning.PACLearning

variable {α β : Type*}

/-- Exponential-polynomial form of Natarajan's lemma: for every real `T ≥ 1`,
`natarajanSum n k d ≤ exp (n / T) · (T · max 1 (k choose 2)) ^ d`. -/
theorem natarajanSum_le_exp_mul_pow (n k d : ℕ) {T : ℝ} (hT : 1 ≤ T) :
    (natarajanSum n k d : ℝ) ≤ Real.exp (n / T) * (T * (max 1 (k.choose 2) : ℕ)) ^ d := by
  set K : ℕ := max 1 (k.choose 2)
  have hK1 : 1 ≤ K := le_max_left 1 _
  have hKk : k.choose 2 ≤ K := le_max_right 1 _
  have hsum_nat : natarajanSum n k d ≤ (∑ i ∈ range (d + 1), n.choose i) * K ^ d := by
    rw [natarajanSum, sum_mul]
    refine sum_le_sum fun i hi => Nat.mul_le_mul_left _ ?_
    exact (Nat.pow_le_pow_left hKk i).trans
      (Nat.pow_le_pow_right hK1 (Nat.lt_succ_iff.mp (mem_range.mp hi)))
  calc (natarajanSum n k d : ℝ)
      ≤ (∑ i ∈ range (d + 1), (n.choose i : ℝ)) * (K : ℝ) ^ d := by exact_mod_cast hsum_nat
    _ ≤ (Real.exp (n / T) * T ^ d) * (K : ℝ) ^ d := by
        gcongr
        exact Cslib.sum_choose_le_exp_mul_pow n d T hT
    _ = Real.exp (n / T) * (T * (K : ℝ)) ^ d := by rw [mul_assoc, ← mul_pow]

/-- **Multiclass packing by `natarajanSum`.** If every finite set N-shattered by `C` has size at
most `d`, the labelings in `P ⊆ (· ∘ x) '' C` pairwise differ on at least `ε m` of the `m > 0`
points `x`, and `2 log |P| < ε r`, then `P.card ≤ natarajanSum r |β| d`. -/
theorem card_le_natarajanSum_of_two_mul_log_card_lt [Fintype β] {C : ConceptClass α β} {d : ℕ}
    (hC : ∀ W : Finset α, NatarajanShatters C ↑W → W.card ≤ d) {m r : ℕ} (hm : 0 < m)
    {x : Fin m → α} {P : Finset (Fin m → β)} (hPC : ∀ u ∈ P, u ∈ (· ∘ x) '' C)
    [DecidableEq β] {ε : ℝ}
    (hP : ∀ u ∈ P, ∀ v ∈ P, u ≠ v → ε * m ≤ hammingDist u v)
    (hr : 2 * Real.log P.card < ε * r) :
    P.card ≤ natarajanSum r (Fintype.card β) d := by
  obtain ⟨t, ht⟩ := exists_injOn_comp_of_two_mul_log_card_lt hm P hP hr
  calc P.card = (P.image fun (u : Fin m → β) j => u (t j)).card := (card_image_of_injOn ht).symm
    _ = ((P.image fun (u : Fin m → β) j => u (t j) : Finset _) : Set (Fin r → β)).ncard :=
        (Set.ncard_coe_finset _).symm
    _ ≤ ((· ∘ (x ∘ t)) '' C).ncard := by
        refine Set.ncard_le_ncard ?_ (Set.toFinite _)
        intro w hw
        obtain ⟨u, hu, rfl⟩ := mem_image.mp (mem_coe.mp hw)
        obtain ⟨c, hc, rfl⟩ := hPC u hu
        exact ⟨c, hc, rfl⟩
    _ ≤ natarajanSum r (Fintype.card β) d := ncard_restriction_le_natarajanSum hC (x ∘ t)

/-- **Packing bound for multiclass Natarajan classes:** if every finite set N-shattered by `C` has
at most `d` points, any `ε`-separated finite set `P ⊆ (· ∘ x) '' C` on `m` sample points (`0 < ε`,
`ε ≤ 1`) has at most `(8 · max 1 (|β| choose 2) / ε) ^ (2 d)` elements, independent of `m`. -/
theorem card_le_div_pow_of_natarajanShatters [Fintype β] [DecidableEq β] {C : ConceptClass α β}
    {d : ℕ} (hC : ∀ W : Finset α, NatarajanShatters C ↑W → W.card ≤ d) {m : ℕ} {x : Fin m → α}
    {P : Finset (Fin m → β)} (hPC : ∀ u ∈ P, u ∈ (· ∘ x) '' C) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hP : ∀ u ∈ P, ∀ v ∈ P, u ≠ v → ε * m ≤ hammingDist u v) :
    (P.card : ℝ) ≤ (8 * (max 1 ((Fintype.card β).choose 2) : ℕ) / ε) ^ (2 * d) := by
  have hK1 : (1 : ℝ) ≤ (max 1 ((Fintype.card β).choose 2) : ℕ) := by
    exact_mod_cast le_max_left 1 ((Fintype.card β).choose 2)
  refine card_le_div_pow_of_forall_two_mul_log_card_lt hK1 hε hε1 fun {r T} hm hlog hT1 => ?_
  exact (Nat.cast_le.mpr (card_le_natarajanSum_of_two_mul_log_card_lt hC hm hPC hP hlog)).trans
    (natarajanSum_le_exp_mul_pow r (Fintype.card β) d hT1)

/-- Multiclass Natarajan packing bound for nontrivial label alphabets (`2 ≤ |β|`):
`(P.card : ℝ) ≤ (8 · (|β| choose 2) / ε) ^ (2 d)`. At `β = Bool` (`2 choose 2 = 1`), this reduces
directly to `(8 / ε) ^ (2 d)`. -/
theorem card_le_div_pow_of_natarajanShatters_of_two_le [Fintype β] [DecidableEq β]
    (hβ : 2 ≤ Fintype.card β) {C : ConceptClass α β} {d : ℕ}
    (hC : ∀ W : Finset α, NatarajanShatters C ↑W → W.card ≤ d) {m : ℕ} {x : Fin m → α}
    {P : Finset (Fin m → β)} (hPC : ∀ u ∈ P, u ∈ (· ∘ x) '' C) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hP : ∀ u ∈ P, ∀ v ∈ P, u ≠ v → ε * m ≤ hammingDist u v) :
    (P.card : ℝ) ≤ (8 * ((Fintype.card β).choose 2 : ℝ) / ε) ^ (2 * d) := by
  have hmax : max 1 ((Fintype.card β).choose 2) = (Fintype.card β).choose 2 :=
    max_eq_right (Nat.choose_pos hβ)
  simpa only [hmax] using card_le_div_pow_of_natarajanShatters hC hPC hε hε1 hP

/-- Natarajan packing bound stated in terms of `HasFiniteNatarajanDim`. -/
theorem card_le_div_pow_of_hasFiniteNatarajanDim [Fintype β] [DecidableEq β]
    {C : ConceptClass α β} (hC : HasFiniteNatarajanDim C) {m : ℕ} {x : Fin m → α}
    {P : Finset (Fin m → β)} (hPC : ∀ u ∈ P, u ∈ (· ∘ x) '' C) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hP : ∀ u ∈ P, ∀ v ∈ P, u ≠ v → ε * m ≤ hammingDist u v) :
    let d := (natarajanDim C).untop hC
    (P.card : ℝ) ≤ (8 * (max 1 ((Fintype.card β).choose 2) : ℕ) / ε) ^ (2 * d) := by
  intro d
  have hd : natarajanDim C = d := (WithTop.coe_untop _ _).symm
  exact card_le_div_pow_of_natarajanShatters
    (fun _ hW => Nat.cast_le.mp (hd ▸ hW.card_le_natarajanDim)) hPC hε hε1 hP

/-- **Multiclass Hamming covering-number bound:** if every finite set N-shattered by `C` has size at
most `d`, then for any `m` points `x` and scale `0 < ε ≤ 1`, `(· ∘ x) '' C` admits an `ε m`-Hamming
net `N ⊆ (· ∘ x) '' C` of size at most `(8 · max 1 (|β| choose 2) / ε) ^ (2 d)`. -/
theorem exists_covering_of_natarajanShatters [Fintype β] [DecidableEq β] {C : ConceptClass α β}
    {d : ℕ} (hC : ∀ W : Finset α, NatarajanShatters C ↑W → W.card ≤ d) {m : ℕ} (x : Fin m → α)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N : Finset (Fin m → β), (∀ u ∈ N, u ∈ (· ∘ x) '' C) ∧
      (N.card : ℝ) ≤ (8 * (max 1 ((Fintype.card β).choose 2) : ℕ) / ε) ^ (2 * d) ∧
      ∀ u ∈ (· ∘ x) '' C, ∃ v ∈ N, (hammingDist v u : ℝ) ≤ ε * m := by
  let V : Finset (Fin m → β) := (Set.toFinite ((· ∘ x) '' C)).toFinset
  obtain ⟨N, hNV, hsep, hcov⟩ := exists_subset_separated_and_covering V hε.le
  have hNC : ∀ u ∈ N, u ∈ (· ∘ x) '' C :=
    fun u hu => (Set.Finite.mem_toFinset _).mp (hNV hu)
  exact ⟨N, hNC, card_le_div_pow_of_natarajanShatters hC hNC hε hε1 hsep,
    fun u hu => hcov u ((Set.Finite.mem_toFinset _).mpr hu)⟩

end Cslib.MachineLearning.PACLearning
