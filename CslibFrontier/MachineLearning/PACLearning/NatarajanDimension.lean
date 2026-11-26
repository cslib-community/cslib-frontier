/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.VCDimension
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Powerset
import CslibFrontier.Foundations.Data.Nat.Choose.Sum

/-!
# The Natarajan dimension and Natarajan's lemma

The *Natarajan dimension* extends the VC dimension from binary to multiclass concept classes
`C : ConceptClass α β` [ShalevShwartzBenDavid2014, Section 29.1; Natarajan1989]. A set `W` is
*N-shattered* by `C` if there are two labelings `f₀ f₁ : α → β` that differ at every point of `W`
such that for every `B ⊆ W` some concept of `C` agrees with `f₀` on `B` and with `f₁` on `W \ B`
(Definition 29.1). The Natarajan dimension is the supremum in `ℕ∞` of the sizes of finite
N-shattered sets (Definition 29.2). With `Bool` labels N-shattering is ordinary shattering, so the
Natarajan dimension is the VC dimension (`natarajanDim_eq_evcDim`).

*Natarajan's lemma* replaces Sauer's lemma in the multiclass fundamental theorem
[ShalevShwartzBenDavid2014, Lemma 29.4]. With `k` labels, a set of labelings of `n` points whose
N-shattered sets have at most `d` points has at most

`∑_{i ≤ d} (n choose i) (k choose 2) ^ i`

elements (`ncard_le_natarajanSum`). The proof is the induction suggested in
[ShalevShwartzBenDavid2014, Exercise 29.3], splitting off one point: a labeling of the remaining
points that extends with `s` labels at the new point is counted once among the tails and once for
each of the `s choose 2 ≥ s - 1` pairs of those labels, and the tails extending with both labels
of a fixed pair N-shatter only sets of at most `d - 1` points. The hint sums over ordered pairs of
labels; unordered pairs give the factor `k choose 2`. With at least one label the sum is at most
`(n + 1) ^ d k ^ (2 d)` (`natarajanSum_le`). For a class on a finite domain `α` this gives
`|C| ≤ |α| ^ Ndim(C) k ^ (2 Ndim(C))`, the form of Lemma 29.4 (`ncard_le_card_pow_natarajanDim`).
The source states Lemma 29.4 for classes of functions from `X` to `[k]`; here the labels are any
finite type.

## Main definitions

- `NatarajanShatters C W`: the concept class `C` N-shatters the set `W`.
- `natarajanDim C`: the Natarajan dimension of `C`.
- `HasFiniteNatarajanDim C`: the N-shattered finite sets of `C` have bounded size.
- `natarajanSum n k d`: the bound `∑_{i ≤ d} (n choose i) (k choose 2) ^ i` of Natarajan's lemma.

## Main results

- `NatarajanShatters.subset`, `NatarajanShatters.superset`: (anti)monotonicity.
- `NatarajanShatters.of_restrict`: N-shattering transfers from the restriction of a class to
  sample points back to the points themselves.
- `NatarajanShatters.image_comp`, `natarajanShatters_image_equiv_comp`,
  `natarajanDim_image_equiv_comp`: invariance under injective and bijective label maps.
- `natarajanShatters_iff_setShatters`, `natarajanDim_eq_evcDim`, `natarajanDim_eq_evcDim_of_equiv`,
  `hasFiniteNatarajanDim_iff_hasFiniteVCDim`: with two labels the Natarajan dimension is the VC
  dimension.
- `natarajanSum_two`: at `k = 2` labels, `natarajanSum` reduces to the binary Sauer–Shelah sum
  `∑_{i ≤ d} (n choose i)`.
- `ncard_le_natarajanSum`, `ncard_restriction_le_natarajanSum`: **Natarajan's lemma** for sets of
  labelings and for the labelings a class realizes on sample points.
- `natarajanSum_le_sum_choose_mul`, `natarajanSum_le`, `ncard_le_card_pow_natarajanDim`: the
  polynomial form of Lemma 29.4.

## References

* [B. K. Natarajan, *On learning sets and functions*][Natarajan1989]
* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

open Finset

namespace Cslib.MachineLearning.PACLearning

variable {α β γ : Type*}

/-- A concept class `C` *N-shatters* a set `W` if there are labelings `f₀ f₁ : α → β` that differ
at every point of `W` such that for every `B ⊆ W` some concept `c ∈ C` agrees with `f₀` on `B` and
with `f₁` on `W \ B` [ShalevShwartzBenDavid2014, Definition 29.1]. -/
@[expose] def NatarajanShatters (C : ConceptClass α β) (W : Set α) : Prop :=
  ∃ f₀ f₁ : α → β, (∀ x ∈ W, f₀ x ≠ f₁ x) ∧
    ∀ B ⊆ W, ∃ c ∈ C, (∀ x ∈ B, c x = f₀ x) ∧ ∀ x ∈ W \ B, c x = f₁ x

/-- The Natarajan dimension is the supremum of the sizes of finite N-shattered sets.
Unbounded sizes give `⊤` [ShalevShwartzBenDavid2014, Definition 29.2]. -/
noncomputable def natarajanDim (C : ConceptClass α β) : ℕ∞ :=
  ⨆ W : Finset α, ⨆ _ : NatarajanShatters C ↑W, (W.card : ℕ∞)

/-- The Natarajan dimension is finite. -/
@[expose] def HasFiniteNatarajanDim (C : ConceptClass α β) : Prop := natarajanDim C ≠ ⊤

/-- N-shattering is anti-monotone in the shattered set. -/
theorem NatarajanShatters.subset {C : ConceptClass α β} {W V : Set α}
    (hW : NatarajanShatters C W) (hVW : V ⊆ W) : NatarajanShatters C V := by
  obtain ⟨f₀, f₁, hne, h⟩ := hW
  refine ⟨f₀, f₁, fun x hx => hne x (hVW hx), fun B hB => ?_⟩
  obtain ⟨c, hc, h₀, h₁⟩ := h B (hB.trans hVW)
  exact ⟨c, hc, h₀, fun x hx => h₁ x ⟨hVW hx.1, hx.2⟩⟩

/-- N-shattering is monotone in the concept class. -/
theorem NatarajanShatters.superset {C C' : ConceptClass α β} {W : Set α}
    (hW : NatarajanShatters C W) (hCC' : C ⊆ C') : NatarajanShatters C' W := by
  obtain ⟨f₀, f₁, hne, h⟩ := hW
  refine ⟨f₀, f₁, hne, fun B hB => ?_⟩
  obtain ⟨c, hc, h₀, h₁⟩ := h B hB
  exact ⟨c, hCC' hc, h₀, h₁⟩

/-- A class N-shatters some set only if it is nonempty. -/
theorem NatarajanShatters.nonempty {C : ConceptClass α β} {W : Set α}
    (hW : NatarajanShatters C W) : C.Nonempty := by
  obtain ⟨_, _, _, h⟩ := hW
  obtain ⟨c, hc, _⟩ := h ∅ (Set.empty_subset W)
  exact ⟨c, hc⟩

/-- Every nonempty class N-shatters the empty set. -/
theorem natarajanShatters_empty {C : ConceptClass α β} (hC : C.Nonempty) :
    NatarajanShatters C ∅ := by
  obtain ⟨c, hc⟩ := hC
  exact ⟨c, c, fun _ hx => hx.elim, fun B _ => ⟨c, hc, fun _ _ => rfl, fun _ _ => rfl⟩⟩

/-- N-shattering transfers from the labelings a class realizes on the points `e : γ → α` back to
the points: if `(· ∘ e) '' C` N-shatters `W`, then `e` is injective on `W` and `C` N-shatters
`e '' W`. -/
theorem NatarajanShatters.of_restrict {C : ConceptClass α β} {e : γ → α} {W : Set γ}
    (hW : NatarajanShatters ((· ∘ e) '' C) W) : Set.InjOn e W ∧ NatarajanShatters C (e '' W) := by
  obtain ⟨f₀, f₁, hne, h⟩ := hW
  have hinj : Set.InjOn e W := by
    intro i hi j hj hij
    by_contra hne'
    obtain ⟨_, ⟨c, -, rfl⟩, -, h₁⟩ := h ∅ (Set.empty_subset W)
    obtain ⟨_, ⟨c', -, rfl⟩, h₀', h₁'⟩ := h {i} (Set.singleton_subset_iff.2 hi)
    have hci : c (e i) = f₁ i := h₁ i ⟨hi, Set.notMem_empty i⟩
    have hcj : c (e j) = f₁ j := h₁ j ⟨hj, Set.notMem_empty j⟩
    have hc'i : c' (e i) = f₀ i := h₀' i rfl
    have hc'j : c' (e j) = f₁ j := h₁' j ⟨hj, fun h => hne' (Set.mem_singleton_iff.1 h).symm⟩
    exact hne i hi (by rw [← hc'i, hij, hc'j, ← hcj, ← hij, hci])
  refine ⟨hinj, ?_⟩
  rcases W.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · obtain ⟨_, ⟨c, hc, rfl⟩, -⟩ := h ∅ (Set.empty_subset _)
    rw [Set.image_empty]
    exact natarajanShatters_empty ⟨c, hc⟩
  have : Nonempty γ := ⟨i₀⟩
  set g := Function.invFunOn e W
  have hg : ∀ i ∈ W, g (e i) = i := fun i hi => hinj.leftInvOn_invFunOn hi
  refine ⟨f₀ ∘ g, f₁ ∘ g, ?_, fun B hB => ?_⟩
  · rintro _ ⟨i, hi, rfl⟩
    simpa only [Function.comp_apply, hg i hi] using hne i hi
  · obtain ⟨_, ⟨c, hc, rfl⟩, h₀, h₁⟩ := h (W ∩ e ⁻¹' B) Set.inter_subset_left
    refine ⟨c, hc, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := hB hx
      simpa only [Function.comp_apply, hg i hi] using h₀ i ⟨hi, hx⟩
    · rintro x ⟨⟨i, hi, rfl⟩, hx⟩
      simpa only [Function.comp_apply, hg i hi] using h₁ i ⟨hi, fun h => hx h.2⟩

/-- Post-composing concepts with an injective map on labels preserves N-shattering. -/
theorem NatarajanShatters.image_comp {C : ConceptClass α β} {W : Set α} {g : β → γ}
    (hg : Function.Injective g) (hW : NatarajanShatters C W) :
    NatarajanShatters ((g ∘ ·) '' C) W := by
  obtain ⟨f₀, f₁, hne, h⟩ := hW
  refine ⟨g ∘ f₀, g ∘ f₁, fun x hx => hg.ne (hne x hx), fun B hB => ?_⟩
  obtain ⟨c, hc, h₀, h₁⟩ := h B hB
  exact ⟨g ∘ c, ⟨c, hc, rfl⟩, fun x hx => congrArg g (h₀ x hx),
    fun x hx => congrArg g (h₁ x hx)⟩

/-- N-shattering is invariant under relabeling by an equivalence `e : β ≃ γ`. -/
@[simp] theorem natarajanShatters_image_equiv_comp {C : ConceptClass α β} {W : Set α}
    (e : β ≃ γ) : NatarajanShatters ((e ∘ ·) '' C) W ↔ NatarajanShatters C W := by
  refine ⟨fun h => ?_, fun h => h.image_comp e.injective⟩
  simpa only [Set.image_image, ← Function.comp_assoc, Equiv.symm_comp_self, Function.id_comp,
    Set.image_id'] using h.image_comp e.symm.injective

/-- The Natarajan dimension is invariant under relabeling by an equivalence `e : β ≃ γ`. -/
@[simp] theorem natarajanDim_image_equiv_comp (C : ConceptClass α β) (e : β ≃ γ) :
    natarajanDim ((e ∘ ·) '' C) = natarajanDim C := by
  simp only [natarajanDim, natarajanShatters_image_equiv_comp]

/-- With `Bool` labels, N-shattering is ordinary shattering. -/
theorem natarajanShatters_iff_setShatters {C : ConceptClass α Bool} {W : Set α} :
    NatarajanShatters C W ↔ SetShatters C W := by
  classical
  constructor
  · rintro ⟨f₀, f₁, hne, h⟩ W' hW'
    obtain ⟨c, hc, h₀, h₁⟩ := h {x ∈ W | f₀ x = decide (x ∈ W')} (fun x hx => hx.1)
    -- On `W`, `c` agrees with `f₀` where `f₀` is the indicator of `W'`, and otherwise with the
    -- other Boolean `f₁`, so `c` is the indicator of `W'` there.
    have hcx : ∀ x ∈ W, c x = decide (x ∈ W') := fun x hx => by
      by_cases hB : f₀ x = decide (x ∈ W')
      · exact (h₀ x ⟨hx, hB⟩).trans hB
      · rw [h₁ x ⟨hx, fun h => hB h.2⟩]
        revert hB
        have := hne x hx
        revert this
        cases f₀ x <;> cases f₁ x <;> cases decide (x ∈ W') <;> decide
    refine ⟨c, hc, Set.ext fun x => ⟨fun ⟨hcx', hx⟩ => ?_, fun hx => ⟨?_, hW' hx⟩⟩⟩
    · simpa [hcx x hx] using hcx'
    · simpa [hx] using hcx x (hW' hx)
  · intro h
    refine ⟨fun _ => true, fun _ => false, fun _ _ => by simp, fun B hB => ?_⟩
    obtain ⟨c, hc, hcB⟩ := h B hB
    refine ⟨c, hc, fun x hx => ?_, fun x hx => ?_⟩
    · have : x ∈ c ⁻¹' {true} ∩ W := hcB ▸ hx
      exact this.1
    · have : x ∉ c ⁻¹' {true} ∩ W := hcB ▸ hx.2
      simpa [hx.1] using this

/-- With Boolean labels the Natarajan and VC dimensions agree, including at infinity. -/
theorem natarajanDim_eq_evcDim (C : ConceptClass α Bool) : natarajanDim C = evcDim C := by
  simp only [natarajanDim, evcDim, natarajanShatters_iff_setShatters]

/-- For any two-element label type `e : β ≃ Bool` (for instance `finTwoEquiv : Fin 2 ≃ Bool`),
the Natarajan dimension agrees with the VC dimension of the relabeled binary class. -/
theorem natarajanDim_eq_evcDim_of_equiv (C : ConceptClass α β) (e : β ≃ Bool) :
    natarajanDim C = evcDim ((e ∘ ·) '' C) :=
  (natarajanDim_image_equiv_comp C e).symm.trans (natarajanDim_eq_evcDim _)

/-- With Boolean labels, finite Natarajan dimension coincides with finite VC dimension. -/
theorem hasFiniteNatarajanDim_iff_hasFiniteVCDim {C : ConceptClass α Bool} :
    HasFiniteNatarajanDim C ↔ HasFiniteVCDim C := by
  rw [HasFiniteNatarajanDim, natarajanDim_eq_evcDim, ne_eq, evcDim_eq_top_iff, not_not]

/-- Every finite N-shattered set has size at most the Natarajan dimension. -/
theorem NatarajanShatters.card_le_natarajanDim {C : ConceptClass α β} {W : Finset α}
    (hW : NatarajanShatters C ↑W) : (W.card : ℕ∞) ≤ natarajanDim C :=
  le_iSup₂_of_le W hW le_rfl

/-- Every finite set N-shattered by a class of finite Natarajan dimension has size at most the
untopped Natarajan dimension. -/
theorem NatarajanShatters.card_le_untop_natarajanDim {C : ConceptClass α β}
    (hC : HasFiniteNatarajanDim C) {W : Finset α} (hW : NatarajanShatters C ↑W) :
    W.card ≤ (natarajanDim C).untop hC :=
  Nat.cast_le.mp ((WithTop.coe_untop _ hC).symm ▸ hW.card_le_natarajanDim)

/-- Evaluating the untopped Natarajan dimension from an equation `natarajanDim C = d`. -/
theorem untop_natarajanDim_eq {C : ConceptClass α β} (hC : HasFiniteNatarajanDim C) {d : ℕ}
    (hd : natarajanDim C = d) : (natarajanDim C).untop hC = d :=
  Nat.cast_inj.mp ((WithTop.coe_untop _ hC).trans hd)

/-- Bounding the Natarajan dimension amounts to bounding every finite N-shattered set. -/
theorem natarajanDim_le_iff {C : ConceptClass α β} {d : ℕ∞} :
    natarajanDim C ≤ d ↔ ∀ W : Finset α, NatarajanShatters C ↑W → (W.card : ℕ∞) ≤ d :=
  iSup₂_le_iff

/-- A class has finite Natarajan dimension iff its finite N-shattered sets have bounded size. -/
theorem hasFiniteNatarajanDim_iff {C : ConceptClass α β} :
    HasFiniteNatarajanDim C ↔
      ∃ n : ℕ, ∀ W : Finset α, NatarajanShatters C ↑W → W.card ≤ n := by
  constructor
  · intro hC
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hC
    exact ⟨n, fun W hW => Nat.cast_le.mp (hn ▸ hW.card_le_natarajanDim)⟩
  · rintro ⟨n, hn⟩
    exact ne_top_of_le_ne_top (ENat.natCast_ne_top n)
      (natarajanDim_le_iff.mpr fun W hW => Nat.cast_le.mpr (hn W hW))

/-- Every class on a finite domain has finite Natarajan dimension. -/
theorem hasFiniteNatarajanDim_of_finite [Finite α] (C : ConceptClass α β) :
    HasFiniteNatarajanDim C :=
  have := Fintype.ofFinite α
  hasFiniteNatarajanDim_iff.mpr ⟨Fintype.card α, fun W _ => W.card_le_univ⟩

/-- A positive finite Natarajan dimension is attained by an N-shattered set of that size. -/
theorem exists_natarajanShatters_card_eq {C : ConceptClass α β} {d : ℕ}
    (hd : natarajanDim C = d) (hpos : 0 < d) :
    ∃ W : Finset α, W.card = d ∧ NatarajanShatters C ↑W := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  have hlt : (n : ℕ∞) < natarajanDim C := by rw [hd]; exact_mod_cast Nat.lt_succ_self n
  simp only [natarajanDim, lt_iSup_iff] at hlt
  obtain ⟨W, hW, hlt⟩ := hlt
  exact ⟨W, (Nat.cast_le.mp (hd ▸ hW.card_le_natarajanDim)).antisymm
    (Nat.cast_lt.mp hlt), hW⟩

/-! ### Natarajan's lemma -/

/-- The bound `∑_{i ≤ d} (n choose i) (k choose 2) ^ i` of Natarajan's lemma on the number of
labelings of `n` points with `k` labels whose N-shattered sets have at most `d` points. The body
is exposed so that clients can evaluate the bound. -/
@[expose] def natarajanSum (n k d : ℕ) : ℕ :=
  ∑ i ∈ range (d + 1), n.choose i * k.choose 2 ^ i

@[simp] theorem natarajanSum_zero_left (k d : ℕ) : natarajanSum 0 k d = 1 := by
  simp [natarajanSum, sum_range_succ']

@[simp] theorem natarajanSum_zero_right (n k : ℕ) : natarajanSum n k 0 = 1 := by
  simp [natarajanSum]

/-- With at most one label no pair of distinct labels exists, so `natarajanSum n k d = 1`. -/
@[simp] theorem natarajanSum_of_le_one (n d : ℕ) {k : ℕ} (hk : k ≤ 1) : natarajanSum n k d = 1 := by
  have hk2 : k.choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
  simp [natarajanSum, hk2, sum_range_succ']

/-- At `k = 2` labels, `(2 choose 2) = 1`, so `natarajanSum` reduces to the binary Sauer–Shelah
sum `∑_{i ≤ d} (n choose i)`. -/
@[simp] theorem natarajanSum_two (n d : ℕ) :
    natarajanSum n 2 d = ∑ i ∈ range (d + 1), n.choose i := by
  simp [natarajanSum]

/-- Pascal's rule for `natarajanSum`. -/
theorem natarajanSum_succ (n k d : ℕ) :
    natarajanSum (n + 1) k (d + 1) =
      natarajanSum n k (d + 1) + k.choose 2 * natarajanSum n k d := by
  simp only [natarajanSum]
  rw [sum_range_succ', sum_range_succ' (fun i => n.choose i * k.choose 2 ^ i), mul_sum]
  simp only [Nat.choose_succ_succ', Nat.choose_zero_right, pow_zero, add_mul, sum_add_distrib]
  have : ∀ i ∈ range (d + 1), n.choose i * k.choose 2 ^ (i + 1) =
      k.choose 2 * (n.choose i * k.choose 2 ^ i) := fun i _ => by ring
  rw [sum_congr rfl this]
  ring

private theorem le_one_add_choose_two (s : ℕ) : s ≤ 1 + s.choose 2 := by
  rcases s with _ | s
  · simp
  · have h : (s + 1).choose 2 = s.choose 1 + s.choose 2 := Nat.choose_succ_succ s 1
    rw [Nat.choose_one_right] at h
    omega

/-- The step `W ↦ succ '' W` of the induction: if the tails of the members of `R` N-shatter `W`,
then `R` N-shatters `Fin.succ '' W`. -/
private theorem natarajanShatters_image_succ {n : ℕ} {R : Set (Fin (n + 1) → β)}
    {W : Set (Fin n)} (hW : NatarajanShatters (Fin.tail '' R) W) :
    NatarajanShatters R (Fin.succ '' W) := by
  obtain ⟨f₀, f₁, hne, h⟩ := hW
  obtain ⟨_, ⟨f, hf, rfl⟩, -⟩ := h ∅ (Set.empty_subset W)
  refine ⟨Fin.cons (f 0) f₀, Fin.cons (f 0) f₁, ?_, fun B hB => ?_⟩
  · rintro _ ⟨i, hi, rfl⟩
    simpa only [Fin.cons_succ] using hne i hi
  · obtain ⟨_, ⟨c, hc, rfl⟩, h₀, h₁⟩ :=
      h (Fin.succ ⁻¹' B) fun i hi => (Fin.succ_injective n).mem_set_image.1 (hB hi)
    refine ⟨c, hc, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, -, rfl⟩ := hB hx
      simpa only [Fin.tail, Fin.cons_succ] using h₀ i hx
    · rintro _ ⟨⟨i, hi, rfl⟩, hx⟩
      simpa only [Fin.tail, Fin.cons_succ] using h₁ i ⟨hi, hx⟩

/-- The other step of the induction: if the tails extending with both labels `b₀ ≠ b₁` at `0`
N-shatter `W`, then `R` N-shatters `insert 0 (Fin.succ '' W)`. -/
private theorem natarajanShatters_insert_zero {n : ℕ} {R : Set (Fin (n + 1) → β)} {b₀ b₁ : β}
    (hb : b₀ ≠ b₁) {W : Set (Fin n)}
    (hW : NatarajanShatters {g | Fin.cons b₀ g ∈ R ∧ Fin.cons b₁ g ∈ R} W) :
    NatarajanShatters R (insert 0 (Fin.succ '' W)) := by
  classical
  obtain ⟨f₀, f₁, hne, h⟩ := hW
  have hmem : ∀ i, Fin.succ i ∈ insert (0 : Fin (n + 1)) (Fin.succ '' W) → i ∈ W := fun i h =>
    (Fin.succ_injective n).mem_set_image.1 (h.resolve_left (Fin.succ_ne_zero i))
  refine ⟨Fin.cons b₀ f₀, Fin.cons b₁ f₁, ?_, fun B hB => ?_⟩
  · intro x hx
    rcases hx with rfl | ⟨i, hi, rfl⟩
    · simpa only [Fin.cons_zero] using hb
    · simpa only [Fin.cons_succ] using hne i hi
  · obtain ⟨g, ⟨hg₀, hg₁⟩, h₀, h₁⟩ := h (W ∩ Fin.succ ⁻¹' B) Set.inter_subset_left
    refine ⟨Fin.cons (if (0 : Fin (n + 1)) ∈ B then b₀ else b₁) g, ?_, ?_, ?_⟩
    · split_ifs <;> assumption
    · intro x hx
      rcases Fin.eq_zero_or_eq_succ x with rfl | ⟨i, rfl⟩
      · simp only [Fin.cons_zero, hx, ↓reduceIte]
      · simpa only [Fin.cons_succ] using h₀ i ⟨hmem i (hB hx), hx⟩
    · rintro x ⟨hx, hxB⟩
      rcases Fin.eq_zero_or_eq_succ x with rfl | ⟨i, rfl⟩
      · simp only [Fin.cons_zero, hxB, ↓reduceIte]
      · simpa only [Fin.cons_succ] using h₁ i ⟨hmem i hx, fun h => hxB h.2⟩

/-- **Natarajan's lemma** for finite sets of labelings of `Fin n`. -/
private theorem card_le_natarajanSum [Fintype β] :
    ∀ (n d : ℕ) (R : Finset (Fin n → β)),
      (∀ W : Finset (Fin n), NatarajanShatters (R : Set (Fin n → β)) ↑W → W.card ≤ d) →
      R.card ≤ natarajanSum n (Fintype.card β) d := by
  classical
  intro n
  induction n with
  | zero =>
    intro d R _
    rw [natarajanSum_zero_left]
    exact Finset.card_le_one.2 fun a _ b _ => Subsingleton.elim a b
  | succ n ih =>
    intro d R hR
    -- Labels at `0` with which a tail `g` extends inside `R`.
    set V : (Fin n → β) → Finset β := fun g => univ.filter fun b => Fin.cons b g ∈ R
    set R' := R.image Fin.tail
    set Rp : Finset β → Finset (Fin n → β) := fun p =>
      R'.filter fun g => p ⊆ V g
    -- Each member of `R` is determined by its tail and its label at `0`.
    have hfib : ∀ g ∈ R', (R.filter fun f => Fin.tail f = g).card = (V g).card := fun g _ => by
      refine card_nbij' (fun f => f 0) (fun b => Fin.cons b g) (fun f hf => ?_) (fun b hb => ?_)
        (fun f hf => ?_) fun b _ => Fin.cons_zero _ _
      · simp only [mem_coe, mem_filter] at hf
        simpa only [mem_coe, mem_filter, mem_univ, true_and, V, ← hf.2, Fin.cons_self_tail]
          using hf.1
      · simp only [mem_coe, mem_filter, mem_univ, true_and, V] at hb
        exact mem_filter.2 ⟨hb, Fin.tail_cons _ _⟩
      · dsimp only
        rw [← (mem_filter.1 hf).2, Fin.cons_self_tail]
    have hcount : R.card ≤ R'.card + ∑ p ∈ univ.powersetCard 2, (Rp p).card := by
      calc R.card = ∑ g ∈ R', (R.filter fun f => Fin.tail f = g).card :=
            card_eq_sum_card_fiberwise fun f hf => mem_image_of_mem _ hf
        _ = ∑ g ∈ R', (V g).card := sum_congr rfl hfib
        _ ≤ ∑ g ∈ R', (1 + (V g).card.choose 2) :=
            sum_le_sum fun g _ => le_one_add_choose_two _
        _ = R'.card + ∑ g ∈ R',
              (((univ : Finset β).powersetCard 2).filter fun p => p ⊆ V g).card := by
            rw [sum_add_distrib, sum_const, smul_eq_mul, mul_one]
            congr 1
            refine sum_congr rfl fun g _ => ?_
            rw [← card_powersetCard]
            congr 1
            ext p
            simp only [mem_powersetCard, mem_filter, subset_univ, true_and]
            tauto
        _ = R'.card + ∑ p ∈ univ.powersetCard 2, (Rp p).card := by
            congr 1
            simp only [card_filter, Rp]
            exact sum_comm
    -- The tails N-shatter only sets of at most `d` points.
    have hR' : ∀ W : Finset (Fin n), NatarajanShatters (R' : Set (Fin n → β)) ↑W →
        W.card ≤ d := by
      intro W hW
      rw [coe_image] at hW
      have := hR (W.map (Fin.succEmb n)) (by
        rw [coe_map]
        exact natarajanShatters_image_succ hW)
      rwa [card_map] at this
    -- The tails extending with both labels of a pair N-shatter only sets of at most `d - 1`
    -- points.
    have hRp : ∀ p ∈ (univ : Finset β).powersetCard 2, ∀ W : Finset (Fin n),
        NatarajanShatters (Rp p : Set (Fin n → β)) ↑W → W.card + 1 ≤ d := by
      intro p hp W hW
      obtain ⟨b₀, b₁, hb, rfl⟩ := card_eq_two.1 (mem_powersetCard.1 hp).2
      have hW' : NatarajanShatters {g | Fin.cons b₀ g ∈ R ∧ Fin.cons b₁ g ∈ R} ↑W := by
        refine hW.superset fun g hg => ?_
        simp only [coe_filter, Set.mem_ofPred_eq, insert_subset_iff, singleton_subset_iff,
          mem_filter, mem_univ, true_and, Rp, V] at hg
        exact hg.2
      have h0 : (0 : Fin (n + 1)) ∉ W.map (Fin.succEmb n) := by
        simp only [mem_map, Fin.coe_succEmb, not_exists, not_and]
        exact fun i _ => Fin.succ_ne_zero i
      have := hR (insert 0 (W.map (Fin.succEmb n))) (by
        rw [coe_insert, coe_map]
        exact natarajanShatters_insert_zero hb hW')
      rwa [card_insert_of_notMem h0, card_map] at this
    rcases d with _ | d
    · -- With `d = 0` no pair of labels extends a common tail.
      have hzero : ∀ p ∈ (univ : Finset β).powersetCard 2, (Rp p).card = 0 := fun p hp =>
        card_eq_zero.2 <| not_nonempty_iff_eq_empty.1 fun hne => by
          simpa using hRp p hp ∅ (by
            rw [coe_empty]
            exact natarajanShatters_empty (coe_nonempty.2 hne))
      rw [sum_congr rfl hzero, sum_const_zero, add_zero] at hcount
      simpa only [natarajanSum_zero_right] using hcount.trans (ih 0 R' hR')
    · have hle : ∀ p ∈ (univ : Finset β).powersetCard 2,
          (Rp p).card ≤ natarajanSum n (Fintype.card β) d :=
        fun p hp => ih d (Rp p) fun W hW => by have := hRp p hp W hW; omega
      calc R.card ≤ R'.card + ∑ p ∈ univ.powersetCard 2, (Rp p).card := hcount
        _ ≤ natarajanSum n (Fintype.card β) (d + 1) +
            ∑ _p ∈ (univ : Finset β).powersetCard 2, natarajanSum n (Fintype.card β) d :=
          add_le_add (ih (d + 1) R' hR') (sum_le_sum hle)
        _ = natarajanSum (n + 1) (Fintype.card β) (d + 1) := by
          rw [sum_const, card_powersetCard, card_univ, smul_eq_mul, natarajanSum_succ]

/-- **Natarajan's lemma** [ShalevShwartzBenDavid2014, Lemma 29.4 and Exercise 29.3]: a set of
labelings of `n` points with `k` labels whose N-shattered finite sets have at most `d` points has
at most `∑_{i ≤ d} (n choose i) (k choose 2) ^ i` elements. -/
theorem ncard_le_natarajanSum [Fintype β] {n d : ℕ} {R : Set (Fin n → β)}
    (hR : ∀ W : Finset (Fin n), NatarajanShatters R ↑W → W.card ≤ d) :
    R.ncard ≤ natarajanSum n (Fintype.card β) d := by
  classical
  have hfin : R.Finite := Set.toFinite R
  rw [Set.ncard_eq_toFinset_card R hfin]
  exact card_le_natarajanSum n d hfin.toFinset fun W hW => hR W (by rwa [hfin.coe_toFinset] at hW)

/-- **Natarajan's lemma** for the labelings `i ↦ c (x i)` that a class realizes on sample points
`x : Fin n → α`: if `C` N-shatters no finite set of more than `d` points, there are at most
`∑_{i ≤ d} (n choose i) (k choose 2) ^ i` of them. Repeated sample points are allowed. -/
theorem ncard_restriction_le_natarajanSum [Fintype β] {C : ConceptClass α β} {d : ℕ}
    (hC : ∀ W : Finset α, NatarajanShatters C ↑W → W.card ≤ d) {n : ℕ} (x : Fin n → α) :
    ((· ∘ x) '' C).ncard ≤ natarajanSum n (Fintype.card β) d := by
  classical
  refine ncard_le_natarajanSum fun W hW => ?_
  obtain ⟨hinj, hsh⟩ := hW.of_restrict
  have := hC (W.image x) (by rwa [coe_image])
  rwa [card_image_of_injOn hinj] at this

/-- `k choose 2 ≤ k ^ 2 / 2`, in the form `2 (k choose 2) ≤ k ^ 2`. -/
private theorem two_mul_choose_two_le (k : ℕ) : 2 * k.choose 2 ≤ k ^ 2 := by
  rw [Nat.choose_two_right, sq]
  exact (Nat.mul_div_le _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))

/-- Factored upper bound on `natarajanSum`: with at least one label,
`∑_{i ≤ d} (n choose i) (k choose 2) ^ i ≤ (∑_{i ≤ d} (n choose i)) k ^ (2 d)`. -/
theorem natarajanSum_le_sum_choose_mul (n d : ℕ) {k : ℕ} (hk : 0 < k) :
    natarajanSum n k d ≤ (∑ i ∈ range (d + 1), n.choose i) * k ^ (2 * d) := by
  have hK : k.choose 2 ≤ k ^ 2 := by have := two_mul_choose_two_le k; omega
  calc natarajanSum n k d ≤ ∑ i ∈ range (d + 1), n.choose i * (k ^ 2) ^ d := by
        refine sum_le_sum fun i hi => Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hK i).trans ?_)
        exact Nat.pow_le_pow_right (by positivity) (Nat.lt_succ_iff.1 (mem_range.1 hi))
    _ = (∑ i ∈ range (d + 1), n.choose i) * (k ^ 2) ^ d := (sum_mul _ _ _).symm
    _ = (∑ i ∈ range (d + 1), n.choose i) * k ^ (2 * d) := by rw [← pow_mul]

/-- The polynomial form of Natarajan's lemma: with at least one label,
`∑_{i ≤ d} (n choose i) (k choose 2) ^ i` is at most `(n + 1) ^ d k ^ (2 d)`. -/
theorem natarajanSum_le (n d : ℕ) {k : ℕ} (hk : 0 < k) :
    natarajanSum n k d ≤ (n + 1) ^ d * k ^ (2 * d) :=
  (natarajanSum_le_sum_choose_mul n d hk).trans
    (Nat.mul_le_mul_right _ (sum_range_choose_le_add_one_pow n d))

/-- **Natarajan's lemma** in the form of [ShalevShwartzBenDavid2014, Lemma 29.4]: a class on a
finite domain `α` with `k` labels has at most `|α| ^ Ndim(C) k ^ (2 Ndim(C))` members. -/
theorem ncard_le_card_pow_natarajanDim [Fintype α] [Fintype β] (C : ConceptClass α β) :
    let d := (natarajanDim C).untop (hasFiniteNatarajanDim_of_finite C)
    C.ncard ≤ Fintype.card α ^ d * Fintype.card β ^ (2 * d) := by
  classical
  intro d
  have hdC : natarajanDim C = d := (WithTop.coe_untop _ _).symm
  set e := (Fintype.equivFin α).symm
  have hC : ∀ W : Finset α, NatarajanShatters C ↑W → W.card ≤ d :=
    fun _ hW => hW.card_le_untop_natarajanDim (hasFiniteNatarajanDim_of_finite C)
  have hcard : ((· ∘ e) '' C).ncard = C.ncard :=
    Set.ncard_image_of_injective C fun f g hfg => by
      funext a
      simpa using congr_fun hfg (e.symm a)
  have hbound := ncard_restriction_le_natarajanSum hC e
  rw [hcard] at hbound
  rcases Nat.eq_zero_or_pos d with hd | hd
  · rw [hd, natarajanSum_zero_right] at hbound
    rw [hd]
    simpa using hbound
  -- A shattered set of `d ≥ 1` points forces `|α| ≥ 1` and `k ≥ 2`.
  obtain ⟨W, hWc, hW⟩ := exists_natarajanShatters_card_eq hdC hd
  obtain ⟨a, ha⟩ : W.Nonempty := card_pos.1 (hWc ▸ hd)
  obtain ⟨f₀, f₁, hne, -⟩ := hW
  have hα : 1 ≤ Fintype.card α := Fintype.card_pos_iff.2 ⟨a⟩
  have hk : 2 ≤ Fintype.card β := Fintype.one_lt_card_iff.2 ⟨f₀ a, f₁ a, hne a ha⟩
  refine hbound.trans ?_
  set n := Fintype.card α
  set k := Fintype.card β
  have h2K : 2 * k.choose 2 ≤ k ^ 2 := two_mul_choose_two_le k
  calc natarajanSum n k d ≤ ∑ i ∈ range (d + 1), n.choose i * k.choose 2 ^ d := by
        refine sum_le_sum fun i hi => Nat.mul_le_mul_left _ ?_
        exact Nat.pow_le_pow_right (Nat.choose_pos (by omega)) (Nat.lt_succ_iff.1 (mem_range.1 hi))
    _ = (∑ i ∈ range (d + 1), n.choose i) * k.choose 2 ^ d := (sum_mul _ _ _).symm
    _ ≤ (n + 1) ^ d * k.choose 2 ^ d := Nat.mul_le_mul_right _ (sum_range_choose_le_add_one_pow n d)
    _ ≤ (2 * n) ^ d * k.choose 2 ^ d := by gcongr; omega
    _ = n ^ d * (2 * k.choose 2) ^ d := by ring
    _ ≤ n ^ d * (k ^ 2) ^ d := by gcongr
    _ = n ^ d * k ^ (2 * d) := by rw [← pow_mul]

end Cslib.MachineLearning.PACLearning
