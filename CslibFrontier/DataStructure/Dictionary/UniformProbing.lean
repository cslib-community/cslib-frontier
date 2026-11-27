/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.Spec
public import CslibFrontier.Languages.Probabilistic.RandomOracle
public import CslibFrontier.Probability.PMF.Expect
public import CslibFrontier.Probability.PMF.Uniform
public import CslibFrontier.Probability.Product
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.UniformBound
import Mathlib.Data.Fintype.Perm
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Uniform Probing in Open-Addressed Hash Tables

This file formalizes the classical uniform-probing model of open-addressed hashing from
[Cormen, Leiserson, Rivest, and Stein, *Introduction to Algorithms*, third edition (MIT Press,
2009), Section 11.4 ("Open addressing", pp. 269–277)][CLRS2009], realizing the bounded-capacity
insert-only dictionary specification `Cslib.DataStructure.Dictionary.spec` over `m` table slots
(`2 * n_max ≤ m`).

In the textbook uniform-probing ("uniform hashing") model, each key `u : Fin U` is assigned an
independent uniform random permutation `π u : Equiv.Perm (Fin m)`
(`PMF.uniformOfFintype (Fin U → Equiv.Perm (Fin m))`), which may equivalently be sampled lazily on
demand via `Cslib.RandomOracle.uniform_interpret_eq_lazy`
(`CslibFrontier/Languages/Probabilistic/RandomOracle.lean`).

## Source statements and notation mapping

In [CLRS2009], third edition, Section 11.4:
* An open-address table has `m` slots (`Fin m`) and holds `n` stored elements (`O.card` or
  `(Dictionary.dom s).card`, bounded by `n_max` with `2 * n_max ≤ m`), giving load factor
  `α = n / m < 1` (`α ≤ 1 / 2` when `2 * n ≤ m`).
* Under uniform hashing (p. 271), each key's probe sequence `h(k, 0), h(k, 1), …, h(k, m - 1)` is
  equally likely to be any of the `m!` permutations of `{0, 1, …, m - 1}` (`Equiv.Perm (Fin m)`).
  Every search or insertion counts all inspected slots along the probe sequence up to and including
  the stopping slot (`unsuccessfulProbes O σ = missedProbes O σ + 1` and
  `probeCount T u σ = unsuccessfulProbes (otherOccupiedSlots T u) σ`).
* **Theorem 11.6 (pp. 274–275)** states that in an open-address hash table with load factor
  `α = n / m < 1`, the expected number of probes in an unsuccessful search is at most
  `1 / (1 - α) = m / (m - n)` under uniform hashing; its proof establishes the exact occupancy tail
  product `Pr{X ≥ i} = ∏_{j = 0}^{i - 2} ((n - j) / (m - j)) ≤ α ^ (i - 1)`.
* **Corollary 11.7 (p. 275)** states that inserting an element into an open-address hash table with
  load factor `α < 1` requires at most `1 / (1 - α) = m / (m - n)` probes on average.
* **Theorem 11.8 (p. 276)** states that when each key in the table is equally likely to be searched
  for, the expected number of probes in a successful search is at most `(1 / α) ln(1 / (1 - α))`.
  Its proof first establishes for a fixed stored key `u` that searching for `u` follows the exact
  same probe sequence as when `u` was inserted (`probeCount_runTable_eq_firstInsert`), so if `u` was
  first inserted after a prefix `ops₁` reaching state `s₁` with `i = (Dictionary.dom s₁).card` keys,
  the expected number of probes for `u` is at most `1 / (1 - i / m) = m / (m - i)`
  (`expect_probeCount_of_mem_dom_le`, and `≤ 2` when `2 * n_max ≤ m` via
  `expect_probeCount_of_mem_dom_le_two`). The uniform-key-averaged logarithmic endpoint
  `(1 / α) ln(1 / (1 - α))` is not formalized here.

## Main definitions

* `Cslib.DataStructure.Dictionary.UniformProbing.allOccupied`,
  `Cslib.DataStructure.Dictionary.UniformProbing.missedProbesFrom`,
  `Cslib.DataStructure.Dictionary.UniformProbing.missedProbes`,
  `Cslib.DataStructure.Dictionary.UniformProbing.unsuccessfulProbes`,
  `Cslib.DataStructure.Dictionary.UniformProbing.probeSlotIndex`: slot-probe predicates, probe
  counts, and
  first-available slot index along a probe permutation `σ : Equiv.Perm (Fin m)`.
* `Cslib.DataStructure.Dictionary.UniformProbing.Table`,
  `Cslib.DataStructure.Dictionary.UniformProbing.emptyTable`,
  `Cslib.DataStructure.Dictionary.UniformProbing.occupiedSlots`,
  `Cslib.DataStructure.Dictionary.UniformProbing.otherOccupiedSlots`,
  `Cslib.DataStructure.Dictionary.UniformProbing.probeCount`: pure open-addressed table of `m`
  slots and
  per-key probe count.
* `Cslib.DataStructure.Dictionary.UniformProbing.tableQuery`,
  `Cslib.DataStructure.Dictionary.UniformProbing.tableInsert`,
  `Cslib.DataStructure.Dictionary.UniformProbing.tableStep`,
  `Cslib.DataStructure.Dictionary.UniformProbing.runTable`,
  `Cslib.DataStructure.Dictionary.UniformProbing.TableRep`: open-addressed `query`/`insert`
  operations and
  representation invariant linking `Table U m` to `Dictionary.State U`.

## Main results

* `Cslib.DataStructure.Dictionary.UniformProbing.toOuterMeasure_allOccupied_eq_prod`,
  `Cslib.DataStructure.Dictionary.UniformProbing.toOuterMeasure_allOccupied_le_pow`: on a table with
  `n = O.card ≤ m` occupied slots, the probability over
  `σ ← PMF.uniformOfFintype (Equiv.Perm (Fin m))`
  that the first `k ≤ m` probes all hit `O` (`k < unsuccessfulProbes O σ`) is
  `∏ i ∈ Finset.range k, ((n - i : ℝ≥0∞) / (m - i : ℝ≥0∞)) ≤ ((n : ℝ≥0∞) / (m : ℝ≥0∞)) ^ k`
  ([CLRS2009], third edition, proof of Theorem 11.6, pp. 274–275).
* `Cslib.DataStructure.Dictionary.UniformProbing.expect_unsuccessfulProbes_le`,
  `Cslib.DataStructure.Dictionary.UniformProbing.expect_unsuccessfulProbes_le_two`,
  `Cslib.DataStructure.Dictionary.UniformProbing.expect_probeCount_of_eq_none_le`,
  `Cslib.DataStructure.Dictionary.UniformProbing.expect_probeCount_of_eq_none_le_two`: Theorem 11.6
  (pp. 274–275) and Corollary 11.7 (p. 275) of [CLRS2009], third edition — an unsuccessful lookup or
  fresh-key insertion into a table holding `n < m` keys makes at most `m / (m - n)` probes in
  expectation (`≤ 2` when `2 * n ≤ m`).
* `Cslib.DataStructure.Dictionary.UniformProbing.TableRep.probeCount_tableInsert_of_isSome`,
  `Cslib.DataStructure.Dictionary.UniformProbing.probeCount_runTable_eq_firstInsert`,
  `Cslib.DataStructure.Dictionary.UniformProbing.expect_probeCount_of_mem_dom_le`,
  `Cslib.DataStructure.Dictionary.UniformProbing.expect_probeCount_of_mem_dom_le_two`: pathwise
  insertion-cost identity and per-key intermediate bound from the proof of Theorem 11.8 (p. 276) of
  [CLRS2009], third edition — a successful lookup of a fixed present key `u ∈ dom s` makes the
  exact same number of probes as the operation that first inserted `u` after prefix `ops₁`
  (reaching state `s₁`), which is at most `m / (m - (Dictionary.dom s₁).card) ≤ 2` in expectation
  when `2 * n_max ≤ m` (the uniform-key-averaged `(1 / α) ln(1 / (1 - α))` endpoint of Theorem 11.8
  is not formalized here).
* `Cslib.DataStructure.Dictionary.UniformProbing.uniform_interpret_eq_lazy_perm`: eager sampling
  of the
  independent permutation family `Fin U → Equiv.Perm (Fin m)` agrees in distribution with lazy
  on-demand oracle evaluation (`RandomOracle.uniform_interpret_eq_lazy`).
* `Cslib.DataStructure.Dictionary.UniformProbing.missedProbes_le_card`,
  `Cslib.DataStructure.Dictionary.UniformProbing.probeCount_le_card_otherOccupied_add_one`,
  `Cslib.DataStructure.Dictionary.UniformProbing.probeCount_le_dom_card_add_one`,
  `Cslib.DataStructure.Dictionary.UniformProbing.probeCount_le_add_one`,
  `Cslib.DataStructure.Dictionary.UniformProbing.expect_probeCount_le_add_one`: deterministic and
  expected pigeonhole probe-count bounds (`probeCount T u (π u) ≤ n_max + 1`) for any full-cycle
  probe permutation family `π`.

## Representation space note

Storing an explicit table of independent permutations in `(Equiv.Perm (Fin m)) ^ U` requires
`U * log₂ (m!)` bits (`Ω(U)` machine words when `U = poly(n_max) ≫ n_max`). To achieve an
`O(n_max)`-word self-contained Word-RAM dictionary,
`CslibFrontier/DataStructure/Dictionary/WordRAM/UniformProbing.lean` pairs a Double Tabulation
primary hash `h₁(u) ∈ Fin (2 ^ M)` with a Double Tabulation stride index
`h₂(u) ∈ Fin (2 ^ (M - 1))`, probing with the odd stride `2 * h₂(u) + 1`
([CLRS2009], third edition, Section 11.4, "Double hashing", pp. 272–274), reusing the
open-addressed table invariants proved here.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein,
  *Introduction to Algorithms*, third edition (MIT Press, 2009), Section 11.4,
  pp. 269–277][CLRS2009]
* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017]
-/

@[expose] public section

namespace Cslib.DataStructure.Dictionary.UniformProbing

open Cslib.Probability
open scoped BigOperators ENNReal

/-! ## Section 1: Permutation probe counts and stopping indices -/

/-- Event that the first `k` slots `σ ⟨0, _⟩, ..., σ ⟨k - 1, _⟩` of permutation `σ` all belong to
the occupied slot set `O`. -/
def allOccupied {m : ℕ} (O : Finset (Fin m)) (k : ℕ) (σ : Equiv.Perm (Fin m)) : Prop :=
  ∀ i : Fin m, i.val < k → σ i ∈ O

instance instDecidableAllOccupied {m : ℕ} (O : Finset (Fin m)) (k : ℕ)
    (σ : Equiv.Perm (Fin m)) : Decidable (allOccupied O k σ) := by
  unfold allOccupied
  infer_instance

@[simp]
theorem allOccupied_zero {m : ℕ} (O : Finset (Fin m)) (σ : Equiv.Perm (Fin m)) :
    allOccupied O 0 σ :=
  fun _ hi => absurd hi (Nat.not_lt_zero _)

theorem allOccupied_succ_iff {m : ℕ} {O : Finset (Fin m)} {k : ℕ} (hk : k < m)
    (σ : Equiv.Perm (Fin m)) :
    allOccupied O (k + 1) σ ↔ allOccupied O k σ ∧ σ ⟨k, hk⟩ ∈ O := by
  refine ⟨fun h => ⟨fun i hi => h i (by omega), h ⟨k, hk⟩ (Nat.lt_succ_self k)⟩, ?_⟩
  rintro ⟨h, hk_mem⟩ i hi
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
  · exact h i hlt
  · exact (Fin.ext heq : i = ⟨k, hk⟩) ▸ hk_mem

theorem allOccupied_mono {m : ℕ} {O : Finset (Fin m)} {j k : ℕ} (hjk : j ≤ k)
    {σ : Equiv.Perm (Fin m)} (h : allOccupied O k σ) : allOccupied O j σ :=
  fun i hi => h i (lt_of_lt_of_le hi hjk)

/-- Count how many consecutive slots `σ ⟨idx, _⟩, σ ⟨idx + 1, _⟩, ...` belong to `O`, for up to
`rem` steps starting at `idx`. -/
def missedProbesFrom {m : ℕ} (O : Finset (Fin m)) (σ : Equiv.Perm (Fin m)) :
    ℕ → ℕ → ℕ
  | 0, _ => 0
  | rem + 1, idx =>
    if h : idx < m then
      if σ ⟨idx, h⟩ ∈ O then 1 + missedProbesFrom O σ rem (idx + 1) else 0
    else 0

/-- Number of consecutive probes `σ 0, σ 1, ...` that hit `O` before the first slot outside `O`. -/
def missedProbes {m : ℕ} (O : Finset (Fin m)) (σ : Equiv.Perm (Fin m)) : ℕ :=
  missedProbesFrom O σ m 0

/-- Total number of slot probes `1 + missedProbes O σ` made by an unsuccessful search (or fresh-key
insertion) against occupied slot set `O` along permutation `σ`. -/
def unsuccessfulProbes {m : ℕ} (O : Finset (Fin m)) (σ : Equiv.Perm (Fin m)) : ℕ :=
  1 + missedProbes O σ

theorem missedProbesFrom_le {m : ℕ} (O : Finset (Fin m)) (σ : Equiv.Perm (Fin m))
    (rem idx : ℕ) : missedProbesFrom O σ rem idx ≤ rem := by
  induction rem generalizing idx with
  | zero => simp [missedProbesFrom]
  | succ rem ih =>
    have := ih (idx + 1)
    simp only [missedProbesFrom]
    split_ifs <;> omega

theorem missedProbes_le {m : ℕ} (O : Finset (Fin m)) (σ : Equiv.Perm (Fin m)) :
    missedProbes O σ ≤ m :=
  missedProbesFrom_le O σ m 0

theorem mem_of_lt_missedProbesFrom {m : ℕ} {O : Finset (Fin m)} {σ : Equiv.Perm (Fin m)}
    {rem idx t : ℕ} (hrem : idx + rem ≤ m) (ht : t < missedProbesFrom O σ rem idx) :
    ∃ h : idx + t < m, σ ⟨idx + t, h⟩ ∈ O := by
  induction rem generalizing idx t with
  | zero => simp [missedProbesFrom] at ht
  | succ rem ih =>
    have hidx : idx < m := by omega
    simp only [missedProbesFrom, hidx, ↓reduceDIte] at ht
    split_ifs at ht with hmem
    · cases t with
      | zero => exact ⟨hidx, hmem⟩
      | succ t =>
        obtain ⟨h', hmem'⟩ := ih (idx := idx + 1) (t := t) (by omega) (by omega)
        have heq : (⟨idx + (t + 1), by omega⟩ : Fin m) = ⟨idx + 1 + t, h'⟩ :=
          Fin.ext (Nat.add_right_comm idx t 1)
        exact ⟨by omega, heq ▸ hmem'⟩
    · omega

theorem notMem_at_missedProbesFrom {m : ℕ} {O : Finset (Fin m)} {σ : Equiv.Perm (Fin m)}
    {rem idx : ℕ} (hrem : idx + rem ≤ m) (hlt : missedProbesFrom O σ rem idx < rem) :
    ∃ h : idx + missedProbesFrom O σ rem idx < m,
      σ ⟨idx + missedProbesFrom O σ rem idx, h⟩ ∉ O := by
  induction rem generalizing idx with
  | zero => omega
  | succ rem ih =>
    have hidx : idx < m := by omega
    simp only [missedProbesFrom, hidx, ↓reduceDIte] at hlt ⊢
    split_ifs at hlt ⊢ with hmem
    · obtain ⟨h', hnot⟩ := ih (idx := idx + 1) (by omega) (by omega)
      have heq : (⟨idx + (1 + missedProbesFrom O σ rem (idx + 1)), by omega⟩ : Fin m) =
          ⟨idx + 1 + missedProbesFrom O σ rem (idx + 1), h'⟩ :=
        Fin.ext (Nat.add_assoc idx 1 _).symm
      exact ⟨by omega, heq ▸ hnot⟩
    · exact ⟨hidx, hmem⟩

/-- For any `k ≤ m`, at least `k` probes miss (`k ≤ missedProbes O σ`) if and only if the first `k`
slots of `σ` all belong to `O`. -/
theorem le_missedProbes_iff_allOccupied {m : ℕ} {O : Finset (Fin m)} {k : ℕ} (hk : k ≤ m)
    (σ : Equiv.Perm (Fin m)) :
    k ≤ missedProbes O σ ↔ allOccupied O k σ := by
  refine ⟨fun hle i hi => ?_, fun hall => ?_⟩
  · obtain ⟨_, hmem⟩ := mem_of_lt_missedProbesFrom (by omega) (lt_of_lt_of_le hi hle)
    simpa only [Nat.zero_add] using hmem
  · by_contra! hlt
    obtain ⟨_, hnotMem⟩ := notMem_at_missedProbesFrom (by omega) (hlt.trans_le hk)
    simp only [Nat.zero_add] at hnotMem
    exact hnotMem (hall ⟨missedProbes O σ, by omega⟩ hlt)

/-- For any `k ≤ m`, an unsuccessful search inspects more than `k` slots
(`k < unsuccessfulProbes O σ`) if and only if the first `k` slots of `σ` all belong to `O`. -/
theorem lt_unsuccessfulProbes_iff_allOccupied {m : ℕ} {O : Finset (Fin m)} {k : ℕ} (hk : k ≤ m)
    (σ : Equiv.Perm (Fin m)) :
    k < unsuccessfulProbes O σ ↔ allOccupied O k σ := by
  rw [unsuccessfulProbes, ← le_missedProbes_iff_allOccupied hk]
  omega

/-- When `O.card < m`, not all `m` slots of `σ` can belong to `O`. -/
theorem not_allOccupied_self_of_card_lt {m : ℕ} {O : Finset (Fin m)} (hO : O.card < m)
    (σ : Equiv.Perm (Fin m)) : ¬ allOccupied O m σ := by
  intro hall
  have hcard := Finset.card_le_card_of_injOn σ
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => hall i i.isLt)
    fun _ _ _ _ h => σ.injective h
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  omega

/-- When `O.card < m`, `missedProbes O σ < m` for every permutation `σ`. -/
theorem missedProbes_lt_of_card_lt {m : ℕ} {O : Finset (Fin m)} (hO : O.card < m)
    (σ : Equiv.Perm (Fin m)) : missedProbes O σ < m :=
  lt_of_le_of_ne (missedProbes_le O σ) fun heq =>
    not_allOccupied_self_of_card_lt hO σ ((le_missedProbes_iff_allOccupied le_rfl σ).mp heq.ge)

/-- The probe index `⟨missedProbes O σ, _⟩ : Fin m` of the first slot along `σ` outside `O` when
`O.card < m`. -/
def probeSlotIndex {m : ℕ} (O : Finset (Fin m)) (σ : Equiv.Perm (Fin m))
    (hO : O.card < m) : Fin m :=
  ⟨missedProbes O σ, missedProbes_lt_of_card_lt hO σ⟩

@[simp]
theorem val_probeSlotIndex {m : ℕ} (O : Finset (Fin m)) (σ : Equiv.Perm (Fin m))
    (hO : O.card < m) : (probeSlotIndex O σ hO).val = missedProbes O σ :=
  rfl

theorem mem_of_lt_probeSlotIndex {m : ℕ} {O : Finset (Fin m)} {σ : Equiv.Perm (Fin m)}
    (hO : O.card < m) {i : Fin m} (hi : i.val < (probeSlotIndex O σ hO).val) :
    σ i ∈ O :=
  (le_missedProbes_iff_allOccupied (le_of_lt (missedProbes_lt_of_card_lt hO σ)) σ).mp le_rfl i hi

theorem notMem_apply_probeSlotIndex {m : ℕ} {O : Finset (Fin m)} {σ : Equiv.Perm (Fin m)}
    (hO : O.card < m) : σ (probeSlotIndex O σ hO) ∉ O := by
  obtain ⟨_, hnot⟩ := notMem_at_missedProbesFrom (O := O) (σ := σ) (by omega)
    (missedProbes_lt_of_card_lt hO σ)
  simp only [Nat.zero_add] at hnot
  exact hnot

/-- Exact characterization of `missedProbes O σ`: for any `i₀ : Fin m`, `missedProbes O σ = i₀.val`
if and only if all earlier probes `i < i₀` lie in `O` and `σ i₀ ∉ O`. -/
theorem missedProbes_eq_iff {m : ℕ} {O : Finset (Fin m)} {σ : Equiv.Perm (Fin m)} (i₀ : Fin m) :
    missedProbes O σ = i₀.val ↔ allOccupied O i₀.val σ ∧ σ i₀ ∉ O := by
  constructor
  · intro heq
    have hall := (le_missedProbes_iff_allOccupied i₀.isLt.le σ).mp heq.ge
    have hlt : missedProbesFrom O σ m 0 < m := by
      change missedProbes O σ < m
      rw [heq]
      exact i₀.isLt
    obtain ⟨hidx, hnot⟩ := notMem_at_missedProbesFrom (O := O) (σ := σ) (by omega) hlt
    have hi₀ : (⟨0 + missedProbesFrom O σ m 0, hidx⟩ : Fin m) = i₀ := by
      ext
      simpa only [Nat.zero_add, missedProbes] using heq
    exact ⟨hall, hi₀ ▸ hnot⟩
  · rintro ⟨hall, hnot⟩
    have hge := (le_missedProbes_iff_allOccupied i₀.isLt.le σ).mpr hall
    by_contra! hne
    have hlt : i₀.val + 1 ≤ missedProbes O σ := by omega
    exact hnot ((le_missedProbes_iff_allOccupied i₀.isLt σ).mp hlt i₀ (Nat.lt_succ_self _))

theorem probeSlotIndex_eq_iff {m : ℕ} {O : Finset (Fin m)} {σ : Equiv.Perm (Fin m)}
    (hO : O.card < m) (i₀ : Fin m) :
    probeSlotIndex O σ hO = i₀ ↔ allOccupied O i₀.val σ ∧ σ i₀ ∉ O := by
  rw [Fin.ext_iff, val_probeSlotIndex, missedProbes_eq_iff]

/-- Tail-sum identity on `Fin m`: when `O.card < m`, the total number of probes
`unsuccessfulProbes O σ` equals the number of `k ∈ Finset.range m` for which `allOccupied O k σ`
holds. -/
theorem unsuccessfulProbes_eq_sum_boole {m : ℕ} {O : Finset (Fin m)} (hO : O.card < m)
    (σ : Equiv.Perm (Fin m)) :
    unsuccessfulProbes O σ =
      ∑ k ∈ Finset.range m, if allOccupied O k σ then 1 else 0 := by
  have hlt := missedProbes_lt_of_card_lt hO σ
  calc
    unsuccessfulProbes O σ
      = (Finset.range (missedProbes O σ + 1)).card := by
          rw [Finset.card_range, unsuccessfulProbes, Nat.add_comm]
    _ = ((Finset.range m).filter fun k => allOccupied O k σ).card := by
          congr 1
          ext k
          simp only [Finset.mem_range, Finset.mem_filter]
          exact ⟨fun hk => ⟨by omega, (le_missedProbes_iff_allOccupied (by omega) σ).mp (by omega)⟩,
            fun ⟨hkm, hall⟩ =>
              Nat.lt_succ_of_le ((le_missedProbes_iff_allOccupied hkm.le σ).mpr hall)⟩
    _ = ∑ k ∈ Finset.range m, if allOccupied O k σ then 1 else 0 := Finset.card_filter _ _

/-! ## Section 2: Textbook Uniform-Probing Expected-Probe Bounds ([CLRS2009], Theorem 11.6) -/

/-- Set of permutations `σ : Equiv.Perm (Fin m)` whose first `k` probes all belong to `O`. -/
def occPermSet {m : ℕ} (O : Finset (Fin m)) (k : ℕ) : Finset (Equiv.Perm (Fin m)) :=
  Finset.univ.filter fun σ => allOccupied O k σ

@[simp]
theorem mem_occPermSet {m : ℕ} {O : Finset (Fin m)} {k : ℕ} {σ : Equiv.Perm (Fin m)} :
    σ ∈ occPermSet O k ↔ allOccupied O k σ := by
  simp [occPermSet]

@[simp]
theorem occPermSet_zero {m : ℕ} (O : Finset (Fin m)) :
    occPermSet O 0 = Finset.univ := by
  ext σ
  simp [occPermSet]

/-- Right-multiplying `σ` by `Equiv.swap ⟨k, hk⟩ j` (for `k ≤ j.val`) preserves `allOccupied O k`.
-/
private theorem allOccupied_mul_swap_iff {m : ℕ} {O : Finset (Fin m)} {k : ℕ} (hk : k < m)
    {j : Fin m} (hj : k ≤ j.val) (σ : Equiv.Perm (Fin m)) :
    allOccupied O k (σ * Equiv.swap ⟨k, hk⟩ j) ↔ allOccupied O k σ := by
  have hfix : ∀ i : Fin m, i.val < k → (Equiv.swap ⟨k, hk⟩ j) i = i := by grind
  exact forall₂_congr fun i hi => by rw [Equiv.Perm.mul_apply, hfix i hi]

/-- By transposition symmetry `σ ↦ σ * Equiv.swap ⟨k, hk⟩ j`, for every `j : Fin m` with
`k ≤ j.val`, the number of permutations in `occPermSet O k` with `σ j ∈ O` equals
`(occPermSet O (k + 1)).card`. -/
private theorem card_filter_occPermSet_eq_succ {m : ℕ} (O : Finset (Fin m)) {k : ℕ} (hk : k < m)
    {j : Fin m} (hj : k ≤ j.val) :
    ((occPermSet O k).filter fun σ => σ j ∈ O).card = (occPermSet O (k + 1)).card := by
  classical
  refine Finset.card_equiv (Equiv.mulRight (Equiv.swap ⟨k, hk⟩ j)) fun σ => ?_
  simp only [Finset.mem_filter, mem_occPermSet, allOccupied_succ_iff hk, Equiv.coe_mulRight,
    allOccupied_mul_swap_iff hk hj, Equiv.Perm.mul_apply, Equiv.swap_apply_left]

/-- Cardinality of `{i : Fin m | k ≤ i.val}` when `k ≤ m`. -/
private theorem card_filter_val_ge {m k : ℕ} (hk : k ≤ m) :
    (Finset.univ.filter fun i : Fin m => k ≤ i.val).card = m - k := by
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m))) (fun i => i.val < k)
  simp only [not_lt, Fin.card_filter_val_lt, min_eq_right hk, Finset.card_univ,
    Fintype.card_fin] at hpart
  omega

/-- For any `σ ∈ occPermSet O k` with `k ≤ m`, the number of remaining indices `j ≥ k` satisfying
`σ j ∈ O` is `O.card - k` (and `k ≤ O.card`). -/
private theorem card_filter_ge_and_mem {m : ℕ} {O : Finset (Fin m)} {k : ℕ} (hk : k ≤ m)
    {σ : Equiv.Perm (Fin m)} (hσ : σ ∈ occPermSet O k) :
    ((Finset.univ.filter fun j : Fin m => k ≤ j.val).filter fun j => σ j ∈ O).card =
      O.card - k := by
  set S := Finset.univ.filter fun j : Fin m => σ j ∈ O
  set L := Finset.univ.filter fun j : Fin m => j.val < k
  have hsub : L ⊆ S := fun j hj => by
    simp only [L, S, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact (mem_occPermSet.mp hσ) j hj
  have heq : ((Finset.univ.filter fun j : Fin m => k ≤ j.val).filter fun j => σ j ∈ O) = S \ L := by
    ext j
    simp [S, L, and_comm]
  have hS : S.card = O.card := Finset.card_equiv σ (by simp [S])
  rw [heq, Finset.card_sdiff_of_subset hsub, hS, Fin.card_filter_val_lt, min_eq_right hk]

/-- **Exact step recurrence for `occPermSet`**: for any `k < m`,
`(m - k) * (occPermSet O (k + 1)).card = (O.card - k) * (occPermSet O k).card`. -/
theorem mul_card_occPermSet_succ {m : ℕ} (O : Finset (Fin m)) {k : ℕ} (hk : k < m) :
    (m - k) * (occPermSet O (k + 1)).card = (O.card - k) * (occPermSet O k).card := by
  classical
  set J_ge := Finset.univ.filter fun j : Fin m => k ≤ j.val
  have hsum_j :
      ∑ j ∈ J_ge, ((occPermSet O k).filter fun σ => σ j ∈ O).card =
        (m - k) * (occPermSet O (k + 1)).card := by
    rw [Finset.sum_congr rfl
      fun j hj => card_filter_occPermSet_eq_succ O hk (Finset.mem_filter.mp hj).2,
      Finset.sum_const, smul_eq_mul, card_filter_val_ge hk.le]
  have hsum_σ :
      ∑ j ∈ J_ge, ((occPermSet O k).filter fun σ => σ j ∈ O).card =
        (O.card - k) * (occPermSet O k).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm, Finset.sum_congr (g := fun _ => O.card - k) rfl fun σ hσ => by
      rw [← Finset.card_filter]
      exact card_filter_ge_and_mem hk.le hσ]
    rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  exact hsum_j.symm.trans hsum_σ

/-- **Exact textbook product formula ([CLRS2009], Proof of Theorem 11.6)**:
for any occupied slot set `O : Finset (Fin m)` and `k ≤ m`, the probability over a uniform random
permutation `σ ← PMF.uniformOfFintype (Equiv.Perm (Fin m))` that the first `k` probes all hit `O`
(`k < unsuccessfulProbes O σ`) is `∏ i ∈ Finset.range k, ((O.card - i : ℝ≥0∞) / (m - i : ℝ≥0∞))`.
-/
theorem toOuterMeasure_allOccupied_eq_prod {m : ℕ} (O : Finset (Fin m)) {k : ℕ} (hk : k ≤ m) :
    (PMF.uniformOfFintype (Equiv.Perm (Fin m))).toOuterMeasure {σ | allOccupied O k σ} =
      ∏ i ∈ Finset.range k, (((O.card - i : ℕ) : ℝ≥0∞) / ((m - i : ℕ) : ℝ≥0∞)) := by
  induction k with
  | zero =>
    rw [show {σ | allOccupied O 0 σ} = Set.univ from Set.eq_univ_of_forall (allOccupied_zero O)]
    rw [PMF.toOuterMeasure_uniformOfFintype]
    simp only [Finset.prod_range_zero, Set.mem_univ, Finset.filter_true, Finset.card_univ]
    exact ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _)
  | succ k ih =>
    rw [Finset.prod_range_succ, ← ih (Nat.le_of_succ_le hk), PMF.toOuterMeasure_uniformOfFintype,
      PMF.toOuterMeasure_uniformOfFintype]
    change ((occPermSet O (k + 1)).card : ℝ≥0∞) * _ =
      ((occPermSet O k).card : ℝ≥0∞) * _ * _
    have hcard_eq : ((occPermSet O (k + 1)).card : ℝ≥0∞) =
        ((occPermSet O k).card : ℝ≥0∞) * (((O.card - k : ℕ) : ℝ≥0∞) / ((m - k : ℕ) : ℝ≥0∞)) := by
      rw [← mul_div_assoc, ENNReal.eq_div_iff (Nat.cast_ne_zero.mpr (by omega))
        (ENNReal.natCast_ne_top _)]
      exact_mod_cast (mul_card_occPermSet_succ O hk).trans (Nat.mul_comm _ _)
    rw [hcard_eq]
    ring

/-- Each factor `(n - i) / (m - i)` for `i < m` and `n ≤ m` is at most `n / m`. -/
theorem sub_div_sub_le_div {n m i : ℕ} (hnm : n ≤ m) (hi : i < m) :
    (((n - i : ℕ) : ℝ≥0∞) / ((m - i : ℕ) : ℝ≥0∞)) ≤ (n : ℝ≥0∞) / (m : ℝ≥0∞) := by
  refine ENNReal.div_le_of_le_mul ?_
  rw [← ENNReal.mul_div_right_comm,
    ENNReal.le_div_iff_mul_le (.inl (Nat.cast_ne_zero.mpr (by omega)))
      (.inl (ENNReal.natCast_ne_top m))]
  have hnat : (n - i) * m ≤ n * (m - i) := by
    rw [Nat.sub_mul, Nat.mul_sub, Nat.mul_comm n i]
    exact Nat.sub_le_sub_left (Nat.mul_le_mul_left i hnm) (n * m)
  exact_mod_cast hnat

/-- **Upper bound `(n / m) ^ k` on the `k`-probe tail probability ([CLRS2009], Proof of Theorem
11.6)**: for any occupied slot set `O : Finset (Fin m)` and `k ≤ m`, the probability over a uniform
random permutation `σ` that the first `k` probes all hit `O` is at most
`((O.card : ℝ≥0∞) / (m : ℝ≥0∞)) ^ k`. -/
theorem toOuterMeasure_allOccupied_le_pow {m : ℕ} (O : Finset (Fin m)) {k : ℕ} (hk : k ≤ m) :
    (PMF.uniformOfFintype (Equiv.Perm (Fin m))).toOuterMeasure {σ | allOccupied O k σ} ≤
      ((O.card : ℝ≥0∞) / (m : ℝ≥0∞)) ^ k := by
  have hO_le : O.card ≤ m := by
    simpa using Finset.card_le_univ O
  rw [toOuterMeasure_allOccupied_eq_prod O hk]
  calc
    (∏ i ∈ Finset.range k, (((O.card - i : ℕ) : ℝ≥0∞) / ((m - i : ℕ) : ℝ≥0∞)))
      ≤ ∏ _i ∈ Finset.range k, ((O.card : ℝ≥0∞) / (m : ℝ≥0∞)) :=
        Finset.prod_le_prod fun i hi =>
          sub_div_sub_le_div hO_le (lt_of_lt_of_le (Finset.mem_range.mp hi) hk)
    _ = ((O.card : ℝ≥0∞) / (m : ℝ≥0∞)) ^ k := by
        simp [Finset.prod_const]

/-- Finite geometric sum identity in `ℝ≥0∞` without subtraction: for `n < m`,
`∑ k ∈ Finset.range j, (n / m) ^ k + (m / (m - n)) * (n / m) ^ j = m / (m - n)`. -/
theorem sum_div_pow_add_tail {n m : ℕ} (hnm : n < m) (j : ℕ) :
    (∑ k ∈ Finset.range j, ((n : ℝ≥0∞) / (m : ℝ≥0∞)) ^ k) +
      ((m : ℝ≥0∞) / ((m - n : ℕ) : ℝ≥0∞)) * ((n : ℝ≥0∞) / (m : ℝ≥0∞)) ^ j =
        (m : ℝ≥0∞) / ((m - n : ℕ) : ℝ≥0∞) := by
  have hstep : 1 + ((m : ℝ≥0∞) / ((m - n : ℕ) : ℝ≥0∞)) * ((n : ℝ≥0∞) / (m : ℝ≥0∞)) =
      (m : ℝ≥0∞) / ((m - n : ℕ) : ℝ≥0∞) := by
    rw [mul_comm,
      ENNReal.div_mul_div_cancel (Nat.cast_ne_zero.mpr (by omega)) (ENNReal.natCast_ne_top _),
      ← ENNReal.div_self (a := ((m - n : ℕ) : ℝ≥0∞)) (Nat.cast_ne_zero.mpr (by omega))
        (ENNReal.natCast_ne_top _),
      ← ENNReal.add_div]
    congr 1
    exact_mod_cast Nat.sub_add_cancel hnm.le
  induction j with
  | zero => simp
  | succ j ih =>
    calc
      (∑ k ∈ Finset.range (j + 1), ((n : ℝ≥0∞) / (m : ℝ≥0∞)) ^ k) +
          ((m : ℝ≥0∞) / ((m - n : ℕ) : ℝ≥0∞)) * ((n : ℝ≥0∞) / (m : ℝ≥0∞)) ^ (j + 1)
        = (∑ k ∈ Finset.range j, ((n : ℝ≥0∞) / (m : ℝ≥0∞)) ^ k) +
            (1 + ((m : ℝ≥0∞) / ((m - n : ℕ) : ℝ≥0∞)) * ((n : ℝ≥0∞) / (m : ℝ≥0∞))) *
              ((n : ℝ≥0∞) / (m : ℝ≥0∞)) ^ j := by
            rw [Finset.sum_range_succ]; ring
      _ = (m : ℝ≥0∞) / ((m - n : ℕ) : ℝ≥0∞) := by rw [hstep, ih]

/-- For `n < m`, any partial geometric sum `∑ k ∈ Finset.range j, (n / m) ^ k` is at most
`m / (m - n)`. -/
theorem sum_div_pow_le {n m : ℕ} (hnm : n < m) (j : ℕ) :
    (∑ k ∈ Finset.range j, ((n : ℝ≥0∞) / (m : ℝ≥0∞)) ^ k) ≤
      (m : ℝ≥0∞) / ((m - n : ℕ) : ℝ≥0∞) := by
  rw [← sum_div_pow_add_tail hnm j]
  exact le_self_add

/-- When `2 * n ≤ m` and `0 < m`, `m / (m - n) ≤ 2` (`1 / (1 - α) ≤ 2` for load factor `α ≤ 1 / 2`).
-/
theorem div_sub_le_two {n m : ℕ} (hm : 0 < m) (h2n : 2 * n ≤ m) :
    (m : ℝ≥0∞) / ((m - n : ℕ) : ℝ≥0∞) ≤ 2 := by
  rw [ENNReal.div_le_iff (Nat.cast_ne_zero.mpr (by omega)) (ENNReal.natCast_ne_top _)]
  exact_mod_cast (by omega : m ≤ 2 * (m - n))

/-- **Theorem 11.6 of [CLRS2009] (Expected probes in an unsuccessful search)**:
for any occupied slot set `O : Finset (Fin m)` with `O.card < m`, the expected number of probes
`unsuccessfulProbes O σ` over a uniform random permutation
`σ ← PMF.uniformOfFintype (Equiv.Perm (Fin m))` is at most `m / (m - O.card)`. -/
theorem expect_unsuccessfulProbes_le {m : ℕ} {O : Finset (Fin m)} (hO : O.card < m) :
    (∑' σ : Equiv.Perm (Fin m),
      PMF.uniformOfFintype (Equiv.Perm (Fin m)) σ * (unsuccessfulProbes O σ : ℝ≥0∞)) ≤
        (m : ℝ≥0∞) / ((m - O.card : ℕ) : ℝ≥0∞) := by
  classical
  let μ := PMF.uniformOfFintype (Equiv.Perm (Fin m))
  have hsum : ∀ σ : Equiv.Perm (Fin m),
      (unsuccessfulProbes O σ : ℝ≥0∞) =
        ∑ k ∈ Finset.range m, ({τ : Equiv.Perm (Fin m) | allOccupied O k τ}).indicator 1 σ := by
    intro σ
    simpa [Set.indicator_apply] using
      congrArg ((↑) : ℕ → ℝ≥0∞) (unsuccessfulProbes_eq_sum_boole hO σ)
  calc
    (∑' σ : Equiv.Perm (Fin m), μ σ * (unsuccessfulProbes O σ : ℝ≥0∞))
      = ∑ σ : Equiv.Perm (Fin m), ∑ k ∈ Finset.range m,
          μ σ * ({τ : Equiv.Perm (Fin m) | allOccupied O k τ}).indicator 1 σ := by
          rw [tsum_fintype]
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [hsum σ, Finset.mul_sum]
    _ = ∑ k ∈ Finset.range m, μ.toOuterMeasure {τ | allOccupied O k τ} := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Cslib.Probability.PMF.toOuterMeasure_eq_tsum_mul_indicator, tsum_fintype]
    _ ≤ ∑ k ∈ Finset.range m, ((O.card : ℝ≥0∞) / (m : ℝ≥0∞)) ^ k :=
          Finset.sum_le_sum fun k hk =>
            toOuterMeasure_allOccupied_le_pow O (Finset.mem_range.mp hk).le
    _ ≤ (m : ℝ≥0∞) / ((m - O.card : ℕ) : ℝ≥0∞) := sum_div_pow_le hO m

/-- **Half-load corollary of Theorem 11.6 ([CLRS2009], Section 11.4)**:
when `0 < m` and `2 * O.card ≤ m` (load factor `α = O.card / m ≤ 1 / 2`), the expected number of
probes in an unsuccessful search is at most `2`. -/
theorem expect_unsuccessfulProbes_le_two {m : ℕ} {O : Finset (Fin m)}
    (hm : 0 < m) (h2n : 2 * O.card ≤ m) :
    (∑' σ : Equiv.Perm (Fin m),
      PMF.uniformOfFintype (Equiv.Perm (Fin m)) σ * (unsuccessfulProbes O σ : ℝ≥0∞)) ≤ 2 :=
  (expect_unsuccessfulProbes_le (by omega)).trans (div_sub_le_two hm h2n)


/-! ## Section 3: Open-Addressed Table Model ([CLRS2009], Section 11.4, pp. 269–276) -/

/-- Pure open-addressed hash table of `m` slots over key universe `Fin U`, where each slot holds
`none` (empty) or `some (u, v)` (occupied by key `u` with value `v`). -/
abbrev Table (U m : ℕ) := Fin m → Option (Fin U × ℕ)

/-- The initially empty table of `m` slots. -/
def emptyTable (U m : ℕ) : Table U m := fun _ => none

/-- The finite set of currently occupied slot indices in table `T`. -/
def occupiedSlots {U m : ℕ} (T : Table U m) : Finset (Fin m) :=
  Finset.univ.filter fun j => (T j).isSome

/-- The finite set of slot indices in `T` occupied by keys distinct from `u`. -/
def otherOccupiedSlots {U m : ℕ} (T : Table U m) (u : Fin U) : Finset (Fin m) :=
  Finset.univ.filter fun j => (T j).isSome ∧ (T j).map Prod.fst ≠ some u

/-- Total number of slot probes `1 + missedProbes (otherOccupiedSlots T u) σ` made when probing
table `T` for key `u` along permutation `σ`. -/
def probeCount {U m : ℕ} (T : Table U m) (u : Fin U) (σ : Equiv.Perm (Fin m)) : ℕ :=
  unsuccessfulProbes (otherOccupiedSlots T u) σ

@[simp]
theorem occupiedSlots_emptyTable (U m : ℕ) :
    occupiedSlots (emptyTable U m) = ∅ := by
  ext j
  simp [occupiedSlots, emptyTable]

@[simp]
theorem otherOccupiedSlots_emptyTable (U m : ℕ) (u : Fin U) :
    otherOccupiedSlots (emptyTable U m) u = ∅ := by
  ext j
  simp [otherOccupiedSlots, emptyTable]

theorem mem_otherOccupiedSlots_iff {U m : ℕ} {T : Table U m} {u : Fin U} {j : Fin m} :
    j ∈ otherOccupiedSlots T u ↔ ∃ u' v', T j = some (u', v') ∧ u' ≠ u := by
  simp only [otherOccupiedSlots, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases T j with _ | ⟨u', v'⟩ <;> simp

theorem otherOccupiedSlots_subset_occupiedSlots {U m : ℕ} (T : Table U m) (u : Fin U) :
    otherOccupiedSlots T u ⊆ occupiedSlots T := fun _ hj =>
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2.1⟩

/-- Open-addressed table representation invariant linking concrete slot array `T : Table U m` to
abstract dictionary state `s : Dictionary.State U` under permutation family
`π : Fin U → Equiv.Perm (Fin m)`. -/
structure TableRep {U m : ℕ} (π : Fin U → Equiv.Perm (Fin m)) (s : Dictionary.State U)
    (T : Table U m) : Prop where
  /-- Every occupied slot `j` holds `(u, v)` with `s u = some v` at key `u`'s stopping probe index.
  -/
  slot_spec : ∀ j u v, T j = some (u, v) →
    s u = some v ∧ ∃ h : missedProbes (otherOccupiedSlots T u) (π u) < m,
      j = π u ⟨missedProbes (otherOccupiedSlots T u) (π u), h⟩
  /-- Every present key `u` with `s u = some v` is stored at its stopping probe index. -/
  key_spec : ∀ u v, s u = some v →
    ∃ h : missedProbes (otherOccupiedSlots T u) (π u) < m,
      T (π u ⟨missedProbes (otherOccupiedSlots T u) (π u), h⟩) = some (u, v)

/-- The empty table represents `Dictionary.empty U` under any permutation family `π`. -/
theorem tableRep_empty {U m : ℕ} (π : Fin U → Equiv.Perm (Fin m)) :
    TableRep π (Dictionary.empty U) (emptyTable U m) where
  slot_spec j _ _ h := by simp [emptyTable] at h
  key_spec u _ h := by simp [Dictionary.empty] at h

/-- Under `TableRep π s T`, each key `u` occupies at most one slot in `T`. -/
theorem TableRep.slot_eq_of_same_key {U m : ℕ} {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T)
    {j₁ j₂ : Fin m} {u : Fin U} {v₁ v₂ : ℕ}
    (h₁ : T j₁ = some (u, v₁)) (h₂ : T j₂ = some (u, v₂)) : j₁ = j₂ := by
  obtain ⟨-, hlt₁, rfl⟩ := hrep.slot_spec j₁ u v₁ h₁
  obtain ⟨-, _, rfl⟩ := hrep.slot_spec j₂ u v₂ h₂
  rfl

/-- Under `TableRep π s T`, any slot set characterized by `(u', v')` satisfying `p u'` has the same
cardinality as `(Dictionary.dom s).filter p`. -/
private theorem TableRep.card_filter_slots {U m : ℕ} {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T)
    (S : Finset (Fin m)) (p : Fin U → Prop) [DecidablePred p]
    (hS : ∀ j, j ∈ S ↔ ∃ u' v', T j = some (u', v') ∧ p u') :
    S.card = ((Dictionary.dom s).filter p).card := by
  refine Finset.card_bij
    (fun j hj => ((T j).get (by obtain ⟨u', v', hTj, -⟩ := (hS j).mp hj; simp [hTj])).1)
    ?_ ?_ ?_
  · intro j hj
    obtain ⟨u', v', hTj, hp⟩ := (hS j).mp hj
    have hsu := (hrep.slot_spec j u' v' hTj).1
    simp [Dictionary.dom, hTj, hsu, hp]
  · intro j₁ hj₁ j₂ hj₂ heq
    obtain ⟨u₁, v₁, h₁, -⟩ := (hS j₁).mp hj₁
    obtain ⟨u₂, v₂, h₂, -⟩ := (hS j₂).mp hj₂
    have hu : u₁ = u₂ := by simpa [h₁, h₂] using heq
    subst hu
    exact hrep.slot_eq_of_same_key h₁ h₂
  · intro u' hu'
    rcases Finset.mem_filter.mp hu' with ⟨hu'_dom, hp⟩
    obtain ⟨v', hsu'⟩ := Dictionary.mem_dom_iff.mp hu'_dom
    obtain ⟨hlt, hTj⟩ := hrep.key_spec u' v' hsu'
    refine ⟨π u' ⟨missedProbes (otherOccupiedSlots T u') (π u'), hlt⟩, ?_, by simp [hTj]⟩
    exact (hS _).mpr ⟨u', v', hTj, hp⟩

/-- Under `TableRep π s T`, the number of occupied slots in `T` equals `(Dictionary.dom s).card`. -/
theorem TableRep.card_occupiedSlots {U m : ℕ} {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T) :
    (occupiedSlots T).card = (Dictionary.dom s).card := by
  rw [← Finset.filter_true (s := Dictionary.dom s)]
  exact hrep.card_filter_slots (occupiedSlots T) (fun _ => True) fun j => by
    simp [occupiedSlots, Option.isSome_iff_exists]

/-- Under `TableRep π s T`, `(otherOccupiedSlots T u).card = ((Dictionary.dom s).erase u).card`. -/
theorem TableRep.card_otherOccupiedSlots {U m : ℕ} {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T) (u : Fin U) :
    (otherOccupiedSlots T u).card = ((Dictionary.dom s).erase u).card := by
  rw [show (Dictionary.dom s).erase u = (Dictionary.dom s).filter (· ≠ u) from by
    ext; simp [and_comm]]
  exact hrep.card_filter_slots (otherOccupiedSlots T u) (· ≠ u) fun _ => mem_otherOccupiedSlots_iff

/-- Under `TableRep π s T`, `(otherOccupiedSlots T u).card ≤ (Dictionary.dom s).card`. -/
theorem TableRep.card_otherOccupiedSlots_le {U m : ℕ} {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T) (u : Fin U) :
    (otherOccupiedSlots T u).card ≤ (Dictionary.dom s).card := by
  rw [hrep.card_otherOccupiedSlots u]
  exact Finset.card_erase_le

/-- When `s u = none`, no slot in `T` holds key `u`, so `otherOccupiedSlots T u = occupiedSlots T`.
-/
theorem TableRep.otherOccupiedSlots_eq_occupiedSlots_of_eq_none {U m : ℕ}
    {π : Fin U → Equiv.Perm (Fin m)} {s : Dictionary.State U} {T : Table U m}
    (hrep : TableRep π s T) {u : Fin U} (hu : s u = none) :
    otherOccupiedSlots T u = occupiedSlots T := by
  ext j
  refine ⟨(otherOccupiedSlots_subset_occupiedSlots T u ·), fun hj => ?_⟩
  obtain ⟨⟨u', v'⟩, hTj⟩ := Option.isSome_iff_exists.mp (Finset.mem_filter.mp hj).2
  have hsu' := (hrep.slot_spec j u' v' hTj).1
  exact mem_otherOccupiedSlots_iff.mpr ⟨u', v', hTj, fun h => by simp [h, hu] at hsu'⟩

/-- When `TableRep π s T` and `(Dictionary.dom s).card < m`, the stopping index for any key `u`
satisfies `missedProbes (otherOccupiedSlots T u) (π u) < m`. -/
theorem TableRep.missedProbes_lt {U m : ℕ} {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T)
    (hcard : (Dictionary.dom s).card < m) (u : Fin U) :
    missedProbes (otherOccupiedSlots T u) (π u) < m :=
  missedProbes_lt_of_card_lt (lt_of_le_of_lt (hrep.card_otherOccupiedSlots_le u) hcard) (π u)

/-- Target slot `π u ⟨missedProbes (otherOccupiedSlots T u) (π u), _⟩` where key `u` is found or
inserted when `(otherOccupiedSlots T u).card < m`. -/
def targetSlot {U m : ℕ} (π : Fin U → Equiv.Perm (Fin m)) (T : Table U m) (u : Fin U)
    (hO : (otherOccupiedSlots T u).card < m) : Fin m :=
  π u (probeSlotIndex (otherOccupiedSlots T u) (π u) hO)

/-- Under `TableRep π s T` and `hO : (otherOccupiedSlots T u).card < m`, `T (targetSlot π T u hO)`
equals `(s u).map (fun v => (u, v))`. -/
theorem TableRep.apply_targetSlot {U m : ℕ} {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T) (u : Fin U)
    (hO : (otherOccupiedSlots T u).card < m) :
    T (targetSlot π T u hO) = (s u).map (fun v => (u, v)) := by
  cases hsu : s u with
  | none =>
    by_contra hne
    obtain ⟨⟨u', v'⟩, hTj⟩ := Option.ne_none_iff_exists'.mp hne
    have hu' : u' ≠ u := fun h => by
      have := (hrep.slot_spec _ u' v' hTj).1
      simp [h, hsu] at this
    exact notMem_apply_probeSlotIndex hO (mem_otherOccupiedSlots_iff.mpr ⟨u', v', hTj, hu'⟩)
  | some v => exact (hrep.key_spec u v hsu).2

/-- Pure open-addressed lookup `tableQuery hm π T u` when `0 < m`: inspects slot
`π u ⟨min (missedProbes (otherOccupiedSlots T u) (π u)) (m - 1), _⟩` and returns `some v` if it
contains `(u, v)`, else `none`. -/
def tableQuery {U m : ℕ} (hm : 0 < m) (π : Fin U → Equiv.Perm (Fin m)) (T : Table U m)
    (u : Fin U) : Option ℕ :=
  let idx := min (missedProbes (otherOccupiedSlots T u) (π u)) (m - 1)
  match T (π u ⟨idx, by omega⟩) with
  | some (u', v) => if u' = u then some v else none
  | none => none

/-- Pure open-addressed insertion `tableInsert hm π T u v`: writes `some (u, v)` at slot
`π u ⟨min (missedProbes (otherOccupiedSlots T u) (π u)) (m - 1), _⟩`. -/
def tableInsert {U m : ℕ} (hm : 0 < m) (π : Fin U → Equiv.Perm (Fin m)) (T : Table U m)
    (u : Fin U) (v : ℕ) : Table U m :=
  let idx := min (missedProbes (otherOccupiedSlots T u) (π u)) (m - 1)
  Function.update T (π u ⟨idx, by omega⟩) (some (u, v))

/-- When `O.card < m`, clamping `missedProbes O σ` to `m - 1` agrees with `probeSlotIndex O σ hO`.
-/
private theorem probeSlotIndex_eq_min {m : ℕ} (hm : 0 < m) (O : Finset (Fin m))
    (σ : Equiv.Perm (Fin m)) (hO : O.card < m) :
    (⟨min (missedProbes O σ) (m - 1), by omega⟩ : Fin m) = probeSlotIndex O σ hO :=
  Fin.ext (Nat.min_eq_left (Nat.le_pred_of_lt (missedProbes_lt_of_card_lt hO σ)))

theorem tableInsert_eq_update_targetSlot {U m : ℕ} (hm : 0 < m) (π : Fin U → Equiv.Perm (Fin m))
    (T : Table U m) (u : Fin U) (v : ℕ) (hO : (otherOccupiedSlots T u).card < m) :
    tableInsert hm π T u v = Function.update T (targetSlot π T u hO) (some (u, v)) := by
  dsimp only [tableInsert, targetSlot]
  rw [probeSlotIndex_eq_min hm _ (π u) hO]

/-- Under `TableRep π s T` and `(otherOccupiedSlots T u).card < m`, `tableQuery hm π T u = s u`. -/
theorem TableRep.tableQuery_eq {U m : ℕ} (hm : 0 < m) {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T) (u : Fin U)
    (hO : (otherOccupiedSlots T u).card < m) :
    tableQuery hm π T u = s u := by
  dsimp only [tableQuery]
  rw [probeSlotIndex_eq_min hm _ (π u) hO]
  change (match T (targetSlot π T u hO) with
    | some (u', v) => if u' = u then some v else none | none => none) = s u
  rw [hrep.apply_targetSlot u hO]
  cases s u <;> simp

/-- Inserting `(u, v)` leaves `otherOccupiedSlots` for `u` itself unchanged. -/
theorem otherOccupiedSlots_tableInsert_self {U m : ℕ} (hm : 0 < m)
    {π : Fin U → Equiv.Perm (Fin m)} {s : Dictionary.State U} {T : Table U m}
    (_hrep : TableRep π s T) (u : Fin U) (v : ℕ)
    (hO : (otherOccupiedSlots T u).card < m) :
    otherOccupiedSlots (tableInsert hm π T u v) u = otherOccupiedSlots T u := by
  rw [tableInsert_eq_update_targetSlot hm π T u v hO]
  ext j
  by_cases hj : j = targetSlot π T u hO
  · subst hj
    refine iff_of_false ?_ (notMem_apply_probeSlotIndex hO)
    simp [mem_otherOccupiedSlots_iff]
  · simp [mem_otherOccupiedSlots_iff, Function.update_of_ne hj]

/-- Any slot `j` holding a key `w ≠ u` cannot be `targetSlot π T u hO`. -/
private theorem TableRep.slot_ne_targetSlot {U m : ℕ} {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T)
    {j : Fin m} {u w : Fin U} {vw : ℕ}
    (hO : (otherOccupiedSlots T u).card < m) (hTj : T j = some (w, vw)) (hwu : w ≠ u) :
    j ≠ targetSlot π T u hO := by
  intro heq
  have htarget := hrep.apply_targetSlot u hO
  rw [← heq, hTj] at htarget
  cases hsu : s u with
  | none => simp [hsu] at htarget
  | some vu =>
    simp only [hsu, Option.map_some, Option.some.injEq, Prod.mk.injEq] at htarget
    exact hwu htarget.1

/-- Inserting `(u, v)` preserves the stopping index `missedProbes (otherOccupiedSlots · w) (π w)`
for every key `w` already present in `s` (`(s w).isSome`). -/
theorem TableRep.missedProbes_tableInsert_of_isSome {U m : ℕ} (hm : 0 < m)
    {π : Fin U → Equiv.Perm (Fin m)} {s : Dictionary.State U} {T : Table U m}
    (hrep : TableRep π s T) (u : Fin U) (v : ℕ)
    (hO : (otherOccupiedSlots T u).card < m)
    {w : Fin U} (hw : (s w).isSome) :
    missedProbes (otherOccupiedSlots (tableInsert hm π T u v) w) (π w) =
      missedProbes (otherOccupiedSlots T w) (π w) := by
  by_cases hwu : w = u
  · subst hwu
    rw [otherOccupiedSlots_tableInsert_self hm hrep w v hO]
  · obtain ⟨vw, hsw⟩ := Option.isSome_iff_exists.mp hw
    obtain ⟨hlt_w, hTw⟩ := hrep.key_spec w vw hsw
    set iw : Fin m := ⟨missedProbes (otherOccupiedSlots T w) (π w), hlt_w⟩
    have hiw_spec := (missedProbes_eq_iff (O := otherOccupiedSlots T w) (σ := π w) iw).mp rfl
    have hne_slot := hrep.slot_ne_targetSlot hO hTw hwu
    rw [tableInsert_eq_update_targetSlot hm π T u v hO]
    apply (missedProbes_eq_iff iw).mpr
    refine ⟨fun i hi => ?_, ?_⟩
    · rcases mem_otherOccupiedSlots_iff.mp (hiw_spec.1 i hi) with ⟨u', v', hTi, hne'⟩
      rw [mem_otherOccupiedSlots_iff]
      by_cases h_eq : π w i = targetSlot π T u hO
      · exact ⟨u, v, by simp [h_eq], Ne.symm hwu⟩
      · exact ⟨u', v', by simp [Function.update_of_ne h_eq, hTi], hne'⟩
    · simp [mem_otherOccupiedSlots_iff, Function.update_of_ne hne_slot, hTw]

/-- **Preservation of `TableRep` under `tableInsert`**: if `TableRep π s T` and
`(otherOccupiedSlots T u).card < m`, then `tableInsert hm π T u v` satisfies
`TableRep π (Function.update s u (some v))`. -/
theorem TableRep.tableInsert {U m : ℕ} (hm : 0 < m) {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T) (u : Fin U) (v : ℕ)
    (hO : (otherOccupiedSlots T u).card < m) :
    TableRep π (Function.update s u (some v)) (tableInsert hm π T u v) := by
  have hlt_u : missedProbes (otherOccupiedSlots T u) (π u) < m :=
    missedProbes_lt_of_card_lt hO (π u)
  have hself_mp :
      missedProbes (otherOccupiedSlots (UniformProbing.tableInsert hm π T u v) u) (π u) =
        missedProbes (otherOccupiedSlots T u) (π u) := by
    rw [otherOccupiedSlots_tableInsert_self hm hrep u v hO]
  have hupd := tableInsert_eq_update_targetSlot hm π T u v hO
  refine ⟨?_, ?_⟩
  · intro j w vw hj
    rw [hupd] at hj
    by_cases hju : j = targetSlot π T u hO
    · subst hju
      simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hj
      rcases hj with ⟨rfl, rfl⟩
      refine ⟨Function.update_self _ _ _, by rw [hself_mp]; exact hlt_u, ?_⟩
      simp only [targetSlot, probeSlotIndex, hself_mp]
    · rw [Function.update_of_ne hju] at hj
      obtain ⟨hsw, hlt_w, hj_eq⟩ := hrep.slot_spec j w vw hj
      have hwu : w ≠ u := by
        rintro rfl
        exact hju (hrep.slot_eq_of_same_key hj (hrep.key_spec w vw hsw).2)
      have hw_mp := hrep.missedProbes_tableInsert_of_isSome hm u v hO (w := w) (by simp [hsw])
      refine ⟨by simp [Function.update_of_ne hwu, hsw], by omega, ?_⟩
      simp only [hw_mp]
      exact hj_eq
  · intro w vw hsw'
    by_cases hwu : w = u
    · subst hwu
      simp only [Function.update_self, Option.some.injEq] at hsw'
      subst hsw'
      refine ⟨by rw [hself_mp]; exact hlt_u, ?_⟩
      rw [congrFun hupd]
      simp only [hself_mp]
      exact Function.update_self (targetSlot π T w hO) (some (w, v)) T
    · simp only [Function.update_of_ne hwu] at hsw'
      obtain ⟨hlt_w, hTw⟩ := hrep.key_spec w vw hsw'
      have hw_mp := hrep.missedProbes_tableInsert_of_isSome hm u v hO (w := w) (by simp [hsw'])
      have hne_slot := hrep.slot_ne_targetSlot hO hTw hwu
      refine ⟨by rw [hw_mp]; exact hlt_w, ?_⟩
      rw [congrFun hupd]
      simp only [hw_mp]
      rw [Function.update_of_ne hne_slot, hTw]

/-- Inserting `(u, v)` leaves `probeCount · u (π u)` unchanged. -/
theorem TableRep.probeCount_tableInsert_self {U m : ℕ} (hm : 0 < m)
    {π : Fin U → Equiv.Perm (Fin m)} {s : Dictionary.State U} {T : Table U m}
    (hrep : TableRep π s T) (u : Fin U) (v : ℕ)
    (hO : (otherOccupiedSlots T u).card < m) :
    probeCount (UniformProbing.tableInsert hm π T u v) u (π u) = probeCount T u (π u) := by
  simp [probeCount, unsuccessfulProbes, otherOccupiedSlots_tableInsert_self hm hrep u v hO]

/-- **Probe invariance for present keys ([CLRS2009], proof of Theorem 11.8, p. 276)**:
once a key `w` is present in `s` (`(s w).isSome`), inserting or updating any key `(u, v)` leaves
the number of probes `probeCount · w (π w)` made when searching for `w` unchanged. -/
theorem TableRep.probeCount_tableInsert_of_isSome {U m : ℕ} (hm : 0 < m)
    {π : Fin U → Equiv.Perm (Fin m)} {s : Dictionary.State U} {T : Table U m}
    (hrep : TableRep π s T) (u : Fin U) (v : ℕ)
    (hO : (otherOccupiedSlots T u).card < m)
    {w : Fin U} (hw : (s w).isSome) :
    probeCount (UniformProbing.tableInsert hm π T u v) w (π w) = probeCount T w (π w) := by
  simp [probeCount, unsuccessfulProbes, hrep.missedProbes_tableInsert_of_isSome hm u v hO hw]

/-- Execute a single `Dictionary.Op U` on open-addressed table `T`. -/
def tableStep {U m : ℕ} (hm : 0 < m) (π : Fin U → Equiv.Perm (Fin m)) (T : Table U m)
    (o : Dictionary.Op U) : Table U m × (Dictionary.spec U 0 0).Result o :=
  match o with
  | .query u => (T, tableQuery hm π T u)
  | .insert u v => (tableInsert hm π T u v, ())

/-- Execute a sequence of `Dictionary.Op U` operations on `T` under permutation family `π`. -/
def runTableFrom {U m : ℕ} (hm : 0 < m) (π : Fin U → Equiv.Perm (Fin m)) :
    Table U m → List (Dictionary.Op U) → Table U m
  | T, [] => T
  | T, o :: os => runTableFrom hm π (tableStep hm π T o).1 os

/-- Table produced by running `ops` starting from `emptyTable U m`. -/
def runTable {U m : ℕ} (hm : 0 < m) (π : Fin U → Equiv.Perm (Fin m))
    (ops : List (Dictionary.Op U)) : Table U m :=
  runTableFrom hm π (emptyTable U m) ops

/-- Under an admissible insertion `(Dictionary.spec U V n_max).valid s (.insert u v)` with
`n_max ≤ m`, `TableRep π s T` and `(Dictionary.dom s).card ≤ n_max`,
`(otherOccupiedSlots T u).card < m` holds for the inserted key `u`. -/
theorem TableRep.card_otherOccupiedSlots_lt_of_valid {U V n_max m : ℕ} (_hm : 0 < m)
    (hcap : n_max ≤ m) {π : Fin U → Equiv.Perm (Fin m)} {s : Dictionary.State U} {T : Table U m}
    (hrep : TableRep π s T) (hs : (Dictionary.dom s).card ≤ n_max)
    {u : Fin U} {v : ℕ} (hval : (Dictionary.spec U V n_max).valid s (.insert u v)) :
    (otherOccupiedSlots T u).card < m := by
  rcases hval.1 with hlt | hisSome
  · have hle := hrep.card_otherOccupiedSlots_le u
    omega
  · rw [hrep.card_otherOccupiedSlots u]
    have hmem : u ∈ Dictionary.dom s := Dictionary.mem_dom_iff_isSome.mpr hisSome
    have herase := Finset.card_erase_lt_of_mem hmem
    omega

/-- Any valid operation history preserves `TableRep`. -/
theorem tableRep_runTableFrom {U V n_max m : ℕ} (hm : 0 < m) (hcap : n_max ≤ m)
    (π : Fin U → Equiv.Perm (Fin m)) {s : Dictionary.State U} {T : Table U m}
    (hrep : TableRep π s T) (hs : (Dictionary.dom s).card ≤ n_max)
    {ops : List (Dictionary.Op U)} (hvh : (Dictionary.spec U V n_max).ValidHistory s ops) :
    TableRep π ((Dictionary.spec U V n_max).run s ops).1 (runTableFrom hm π T ops) := by
  induction ops generalizing s T with
  | nil => exact hrep
  | cons o os ih =>
    have hs' : (Dictionary.dom ((Dictionary.spec U V n_max).stepFn s o).1).card ≤ n_max :=
      Dictionary.card_dom_step_le_of_valid hs hvh.1
    cases o with
    | query u =>
      exact ih hrep hs' hvh.2
    | insert u v =>
      have hO : (otherOccupiedSlots T u).card < m :=
        hrep.card_otherOccupiedSlots_lt_of_valid hm hcap hs hvh.1
      exact ih (hrep.tableInsert hm u v hO) hs' hvh.2

/-- Running any valid operation history from `emptyTable U m` produces a table satisfying
`TableRep`. -/
theorem tableRep_runTable {U V n_max m : ℕ} (hm : 0 < m) (hcap : n_max ≤ m)
    (π : Fin U → Equiv.Perm (Fin m)) {ops : List (Dictionary.Op U)}
    (hvh : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U) ops) :
    TableRep π ((Dictionary.spec U V n_max).run (Dictionary.empty U) ops).1
      (runTable hm π ops) :=
  tableRep_runTableFrom hm hcap π (tableRep_empty π) (by simp) hvh

/-- If key `w` is already present in `s`, then running any valid continuation `ops` from `(s, T)`
preserves `probeCount · w (π w)`. -/
theorem probeCount_runTableFrom_of_isSome {U V n_max m : ℕ} (hm : 0 < m) (hcap : n_max ≤ m)
    (π : Fin U → Equiv.Perm (Fin m)) {s : Dictionary.State U} {T : Table U m}
    (hrep : TableRep π s T) (hs : (Dictionary.dom s).card ≤ n_max)
    {w : Fin U} (hw : (s w).isSome)
    {ops : List (Dictionary.Op U)} (hvh : (Dictionary.spec U V n_max).ValidHistory s ops) :
    probeCount (runTableFrom hm π T ops) w (π w) = probeCount T w (π w) := by
  induction ops generalizing s T with
  | nil => rfl
  | cons o os ih =>
    have hs' : (Dictionary.dom ((Dictionary.spec U V n_max).stepFn s o).1).card ≤ n_max :=
      Dictionary.card_dom_step_le_of_valid hs hvh.1
    cases o with
    | query u =>
      exact ih hrep hs' hw hvh.2
    | insert u v =>
      have hO : (otherOccupiedSlots T u).card < m :=
        hrep.card_otherOccupiedSlots_lt_of_valid hm hcap hs hvh.1
      have hw' : ((Function.update s u (some v)) w).isSome := by
        by_cases h : w = u <;> simp [h, hw]
      rw [runTableFrom, tableStep, ih (hrep.tableInsert hm u v hO) hs' hw' hvh.2]
      exact hrep.probeCount_tableInsert_of_isSome hm u v hO hw

/-- Prefix + suffix decomposition for `ValidHistory` and `runTableFrom`. -/
theorem validHistory_and_runTableFrom_append {U V n_max m : ℕ} (hm : 0 < m)
    (π : Fin U → Equiv.Perm (Fin m)) :
    ∀ {l₁ l₂ : List (Dictionary.Op U)} {s : Dictionary.State U} (T : Table U m),
      (Dictionary.spec U V n_max).ValidHistory s (l₁ ++ l₂) →
      (Dictionary.spec U V n_max).ValidHistory s l₁ ∧
      (Dictionary.spec U V n_max).ValidHistory ((Dictionary.spec U V n_max).run s l₁).1 l₂ ∧
      runTableFrom hm π T (l₁ ++ l₂) = runTableFrom hm π (runTableFrom hm π T l₁) l₂
  | [], _, _, _, h => ⟨trivial, h, rfl⟩
  | o :: l₁, l₂, s, T, h => by
    obtain ⟨h₁, h₂, hrun⟩ :=
      validHistory_and_runTableFrom_append hm π
        (s := ((Dictionary.spec U V n_max).stepFn s o).1) (tableStep hm π T o).1 h.2
    exact ⟨⟨h.1, h₁⟩, h₂, hrun⟩

/-- **Pathwise insertion-cost identity from the proof of Theorem 11.8 of [CLRS2009], third edition,
p. 276 (`probeCount_runTable_eq_firstInsert`)**:
if `ops = ops₁ ++ (.insert u v₀ :: ops₂)` is a valid operation history where `ops₁` is the prefix
before `u` is inserted (`((Dictionary.spec U V n_max).run (Dictionary.empty U) ops₁).1 u = none`),
then the number of probes made when searching for `u` after the entire history `ops` equals the
number of probes made when `u` was first inserted after `ops₁`. -/
theorem probeCount_runTable_eq_firstInsert {U V n_max m : ℕ} (hm : 0 < m) (hcap : n_max ≤ m)
    (π : Fin U → Equiv.Perm (Fin m))
    {ops₁ ops₂ : List (Dictionary.Op U)} {u : Fin U} {v₀ : ℕ}
    (hvh : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U)
      (ops₁ ++ (.insert u v₀ :: ops₂))) :
    probeCount (runTable hm π (ops₁ ++ (.insert u v₀ :: ops₂))) u (π u) =
      probeCount (runTable hm π ops₁) u (π u) := by
  obtain ⟨hvh₁, hvh_rest, hrun_eq⟩ :=
    validHistory_and_runTableFrom_append hm π (emptyTable U m) hvh
  set T₁ := runTable hm π ops₁
  have hrep₁ := tableRep_runTable hm hcap π hvh₁
  have hs₁ := Dictionary.card_dom_run_empty_le hvh₁
  have hO₁ := hrep₁.card_otherOccupiedSlots_lt_of_valid hm hcap hs₁ hvh_rest.1
  dsimp only [runTable]
  rw [hrun_eq]
  dsimp only [runTableFrom, tableStep]
  exact (probeCount_runTableFrom_of_isSome hm hcap π (hrep₁.tableInsert hm u v₀ hO₁)
    (Dictionary.card_dom_step_le_of_valid hs₁ hvh_rest.1) (by simp) hvh_rest.2).trans
    (hrep₁.probeCount_tableInsert_self hm u v₀ hO₁)

/-- If key `u` is never inserted during `ops` (`∀ v, .insert u v ∉ ops`), then `runTableFrom` is
independent of `π u`: updating `π` at `u` leaves the resulting table unchanged. -/
theorem runTableFrom_update_eq {U m : ℕ} (hm : 0 < m) (π : Fin U → Equiv.Perm (Fin m))
    (u : Fin U) (σ : Equiv.Perm (Fin m)) (T : Table U m) :
    ∀ {ops : List (Dictionary.Op U)},
      (∀ v, Dictionary.Op.insert u v ∉ ops) →
      runTableFrom hm (Function.update π u σ) T ops = runTableFrom hm π T ops
  | [], _ => rfl
  | .query _ :: os, hno =>
    runTableFrom_update_eq hm π u σ T (ops := os) fun v hv => hno v (List.mem_cons_of_mem _ hv)
  | .insert w v :: os, hno => by
    have hwu : w ≠ u := fun h => hno v (h ▸ List.mem_cons_self)
    have hins : tableInsert hm (Function.update π u σ) T w v = tableInsert hm π T w v := by
      simp [tableInsert, Function.update_of_ne hwu]
    dsimp only [runTableFrom, tableStep]
    rw [hins]
    exact runTableFrom_update_eq hm π u σ (tableInsert hm π T w v) (ops := os)
      fun v' hv' => hno v' (List.mem_cons_of_mem _ hv')

/-- Once `(s₀ u).isSome`, running any list of operations `l` preserves `isSome` at `u`. -/
private theorem isSome_run_of_isSome {U V n_max : ℕ} {u : Fin U} :
    ∀ (l : List (Dictionary.Op U)) {s₀ : Dictionary.State U},
      (s₀ u).isSome → (((Dictionary.spec U V n_max).run s₀ l).1 u).isSome
  | [], _, h => h
  | .query _ :: l, _, h => isSome_run_of_isSome l h
  | .insert w _ :: l, s₀, h =>
    isSome_run_of_isSome l (s₀ := ((Dictionary.spec U V n_max).stepFn s₀ (.insert w _)).1)
      (by by_cases hwu : u = w <;> simp [hwu, h])

/-- If `((Dictionary.spec U V n_max).run s ops).1 u = none`, then no `.insert u v` appears in `ops`.
-/
theorem not_mem_insert_of_run_eq_none {U V n_max : ℕ} {u : Fin U} :
    ∀ {ops : List (Dictionary.Op U)} {s : Dictionary.State U},
      ((Dictionary.spec U V n_max).run s ops).1 u = none →
      ∀ v, Dictionary.Op.insert u v ∉ ops
  | [], _, _, _ => List.not_mem_nil
  | o :: os, s, hnone, v => fun hmem => by
    rcases List.mem_cons.mp hmem with rfl | htail
    · have his := isSome_run_of_isSome (V := V) (n_max := n_max) (u := u) os
        (s₀ := ((Dictionary.spec U V n_max).stepFn s (.insert u v)).1) (by simp)
      change (((Dictionary.spec U V n_max).run s (.insert u v :: os)).1 u).isSome at his
      rw [hnone] at his
      cases his
    · exact not_mem_insert_of_run_eq_none
        (s := ((Dictionary.spec U V n_max).stepFn s o).1) hnone v htail

/-- **Theorem 11.6 (pp. 274–275) & Corollary 11.7 (p. 275) of [CLRS2009], third edition, over
`PMF.uniformOfFintype`**:
for any valid operation history `ops` reaching state `s` with `(Dictionary.dom s).card < m` and any
absent key `u` (`s u = none`), the expected number of probes made by an unsuccessful lookup
`query u` or fresh-key insertion `insert u v` on `runTable hm π ops` over
`π ← PMF.uniformOfFintype (Fin U → Equiv.Perm (Fin m))` is at most
`m / (m - (Dictionary.dom s).card)` (`≤ 2` when `2 * (Dictionary.dom s).card ≤ m`). -/
theorem expect_probeCount_of_eq_none_le {U V n_max m : ℕ} (hm : 0 < m) (hcap : n_max ≤ m)
    {ops : List (Dictionary.Op U)}
    (hvh : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U) ops)
    {u : Fin U} (hu : ((Dictionary.spec U V n_max).run (Dictionary.empty U) ops).1 u = none)
    (hcard :
      (Dictionary.dom ((Dictionary.spec U V n_max).run (Dictionary.empty U) ops).1).card < m) :
    let s := ((Dictionary.spec U V n_max).run (Dictionary.empty U) ops).1
    (∑' π : Fin U → Equiv.Perm (Fin m),
      PMF.uniformOfFintype (Fin U → Equiv.Perm (Fin m)) π *
        (probeCount (runTable hm π ops) u (π u) : ℝ≥0∞)) ≤
      (m : ℝ≥0∞) / ((m - (Dictionary.dom s).card : ℕ) : ℝ≥0∞) := by
  intro s
  have : Nonempty (Equiv.Perm (Fin m)) := ⟨1⟩
  let μ_all := PMF.uniformOfFintype (Fin U → Equiv.Perm (Fin m))
  let μ_one := PMF.uniformOfFintype (Equiv.Perm (Fin m))
  have hno : ∀ v, Dictionary.Op.insert u v ∉ ops := not_mem_insert_of_run_eq_none hu
  have hupd : μ_all = μ_all.bind (fun π₀ => μ_one.map (fun σ => Function.update π₀ u σ)) := by
    dsimp only [μ_all, μ_one]
    conv_lhs => rw [← PMF.uniformOfFintype_update u]
    simp only [← PMF.bind_pure_comp]
    exact PMF.bind_comm _ _ _
  calc
    (∑' π, μ_all π * (probeCount (runTable hm π ops) u (π u) : ℝ≥0∞))
      = ∑' π₀, μ_all π₀ * ∑' σ, μ_one σ *
          (probeCount (runTable hm (Function.update π₀ u σ) ops) u
            ((Function.update π₀ u σ) u) : ℝ≥0∞) := by
          conv_lhs => rw [hupd]
          rw [PMF.tsum_bind_mul]
          refine tsum_congr fun π₀ => congrArg (μ_all π₀ * ·) ?_
          exact PMF.tsum_map_mul μ_one (fun σ => Function.update π₀ u σ) _
    _ ≤ ∑' π₀, μ_all π₀ * ((m : ℝ≥0∞) / ((m - (Dictionary.dom s).card : ℕ) : ℝ≥0∞)) := by
          refine tsum_le_tsum fun π₀ => ?_
          gcongr
          have hrep := tableRep_runTable hm hcap π₀ hvh
          have hcongr : ∀ σ,
              probeCount (runTable hm (Function.update π₀ u σ) ops) u
                ((Function.update π₀ u σ) u) =
                unsuccessfulProbes (occupiedSlots (runTable hm π₀ ops)) σ := fun σ => by
            dsimp only [runTable]
            rw [runTableFrom_update_eq hm π₀ u σ (emptyTable U m) hno, Function.update_self]
            exact congrArg (unsuccessfulProbes · σ)
              (hrep.otherOccupiedSlots_eq_occupiedSlots_of_eq_none hu)
          simp_rw [hcongr]
          dsimp only [μ_one]
          exact (expect_unsuccessfulProbes_le (hrep.card_occupiedSlots.symm ▸ hcard)).trans_eq
            (by rw [hrep.card_occupiedSlots])
    _ = (m : ℝ≥0∞) / ((m - (Dictionary.dom s).card : ℕ) : ℝ≥0∞) := by
          rw [ENNReal.tsum_mul_right, μ_all.tsum_coe, one_mul]

/-- **Half-load corollary of Theorem 11.6 & Corollary 11.7 ([CLRS2009], third edition, Section 11.4,
pp. 274–276)**:
when `2 * n_max ≤ m`, any unsuccessful lookup or fresh-key insertion after a valid history `ops`
makes at most `2` probes in expectation over
`π ← PMF.uniformOfFintype (Fin U → Equiv.Perm (Fin m))`. -/
theorem expect_probeCount_of_eq_none_le_two {U V n_max m : ℕ} (hm : 0 < m) (h2cap : 2 * n_max ≤ m)
    {ops : List (Dictionary.Op U)}
    (hvh : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U) ops)
    {u : Fin U} (hu : ((Dictionary.spec U V n_max).run (Dictionary.empty U) ops).1 u = none) :
    (∑' π : Fin U → Equiv.Perm (Fin m),
      PMF.uniformOfFintype (Fin U → Equiv.Perm (Fin m)) π *
        (probeCount (runTable hm π ops) u (π u) : ℝ≥0∞)) ≤ 2 := by
  have hdom_le :
      (Dictionary.dom ((Dictionary.spec U V n_max).run (Dictionary.empty U) ops).1).card ≤ n_max :=
    Dictionary.card_dom_run_empty_le hvh
  refine (expect_probeCount_of_eq_none_le hm (by omega) hvh hu (by omega)).trans ?_
  exact div_sub_le_two hm (by omega)

/-- **Per-key successful-search bound from the proof of Theorem 11.8 of [CLRS2009], third edition,
p. 276**:
if `ops = ops₁ ++ (.insert u v₀ :: ops₂)` is a valid operation history where `ops₁` is the prefix
before `u` is first inserted (`s₁ u = none`), then the expected number of probes made when
searching for the fixed key `u` after `ops` equals the expected number of probes when `u` was first
inserted after `ops₁`, and is at most `m / (m - (Dictionary.dom s₁).card)` (this formalizes the
per-key intermediate bound `1 / (1 - i / m) = m / (m - i)` for `i = (Dictionary.dom s₁).card` from
the proof of Theorem 11.8; the uniform-key-averaged `(1 / α) ln(1 / (1 - α))` endpoint of Theorem
11.8 is not formalized here). -/
theorem expect_probeCount_of_mem_dom_le {U V n_max m : ℕ} (hm : 0 < m) (hcap : n_max ≤ m)
    {ops₁ ops₂ : List (Dictionary.Op U)} {u : Fin U} {v₀ : ℕ}
    (hvh : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U)
      (ops₁ ++ (.insert u v₀ :: ops₂)))
    (hu₁ : ((Dictionary.spec U V n_max).run (Dictionary.empty U) ops₁).1 u = none)
    (hcard₁ :
      (Dictionary.dom ((Dictionary.spec U V n_max).run (Dictionary.empty U) ops₁).1).card < m) :
    let s₁ := ((Dictionary.spec U V n_max).run (Dictionary.empty U) ops₁).1
    (∑' π : Fin U → Equiv.Perm (Fin m),
      PMF.uniformOfFintype (Fin U → Equiv.Perm (Fin m)) π *
        (probeCount (runTable hm π (ops₁ ++ (.insert u v₀ :: ops₂))) u (π u) : ℝ≥0∞)) ≤
      (m : ℝ≥0∞) / ((m - (Dictionary.dom s₁).card : ℕ) : ℝ≥0∞) := by
  intro s₁
  have hvh₁ := ((StateTransitionSpec.validHistory_append _ _ _).mp hvh).1
  have hcongr : ∀ π : Fin U → Equiv.Perm (Fin m),
      probeCount (runTable hm π (ops₁ ++ (.insert u v₀ :: ops₂))) u (π u) =
        probeCount (runTable hm π ops₁) u (π u) :=
    fun π => probeCount_runTable_eq_firstInsert hm hcap π hvh
  simp_rw [hcongr]
  exact expect_probeCount_of_eq_none_le hm hcap hvh₁ hu₁ hcard₁

/-- **Half-load per-key successful-search bound from the proof of Theorem 11.8 ([CLRS2009], third
edition, Section 11.4, p. 276)**:
when `2 * n_max ≤ m`, any successful lookup of a fixed present key `u` (first inserted after prefix
`ops₁`) makes at most `2` probes in expectation over
`π ← PMF.uniformOfFintype (Fin U → Equiv.Perm (Fin m))`. -/
theorem expect_probeCount_of_mem_dom_le_two {U V n_max m : ℕ} (hm : 0 < m) (h2cap : 2 * n_max ≤ m)
    {ops₁ ops₂ : List (Dictionary.Op U)} {u : Fin U} {v₀ : ℕ}
    (hvh : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U)
      (ops₁ ++ (.insert u v₀ :: ops₂)))
    (hu₁ : ((Dictionary.spec U V n_max).run (Dictionary.empty U) ops₁).1 u = none) :
    (∑' π : Fin U → Equiv.Perm (Fin m),
      PMF.uniformOfFintype (Fin U → Equiv.Perm (Fin m)) π *
        (probeCount (runTable hm π (ops₁ ++ (.insert u v₀ :: ops₂))) u (π u) : ℝ≥0∞)) ≤ 2 := by
  have hvh₁ := ((StateTransitionSpec.validHistory_append _ _ _).mp hvh).1
  have hdom₁_le :
      (Dictionary.dom ((Dictionary.spec U V n_max).run (Dictionary.empty U) ops₁).1).card ≤ n_max :=
    Dictionary.card_dom_run_empty_le hvh₁
  refine (expect_probeCount_of_mem_dom_le hm (by omega) hvh hu₁ (by omega)).trans ?_
  exact div_sub_le_two hm (by omega)

/-! ## Section 4: Lazy Random-Oracle Equivalence (`RandomOracle.uniform_interpret_eq_lazy`) -/

/-- Any adaptive oracle program querying per-key permutations `u ↦ π u : Equiv.Perm (Fin m)` has the
exact same output distribution whether the permutation table
`π ← PMF.uniformOfFintype (Fin U → Equiv.Perm (Fin m))` is sampled eagerly upfront or lazily on
first query via `Cslib.RandomOracle.answer`. -/
theorem uniform_interpret_eq_lazy_perm {U m : ℕ} {α : Type}
    (program : OracleComp (fun _ : Fin U => Equiv.Perm (Fin m)) α) :
    (do
      let π ← PMF.uniformOfFintype (Fin U → Equiv.Perm (Fin m))
      OracleComp.interpret (fun u => PMF.pure (π u)) program) =
        ((OracleComp.interpret
          (Cslib.RandomOracle.answer (fun _ : Fin U => PMF.uniformOfFintype (Equiv.Perm (Fin m))))
          program).run (fun _ => none)).map Prod.fst :=
  Cslib.RandomOracle.uniform_interpret_eq_lazy program

/-! ## Section 5: Deterministic Pigeonhole Probe-Count Bounds -/

/-- For any occupied slot set `O : Finset (Fin m)` and permutation `σ : Equiv.Perm (Fin m)`, the
number of consecutive missed probes `missedProbes O σ` is at most `O.card` by injectivity of `σ`. -/
theorem missedProbes_le_card {m : ℕ} (O : Finset (Fin m)) (σ : Equiv.Perm (Fin m)) :
    missedProbes O σ ≤ O.card := by
  have hle_m := missedProbes_le O σ
  have hall := (le_missedProbes_iff_allOccupied hle_m σ).mp le_rfl
  have hle := Finset.card_le_card_of_injOn σ
    (fun i (hi : i ∈ Finset.univ.filter fun i : Fin m => i.val < missedProbes O σ) =>
      hall i (Finset.mem_filter.mp hi).2)
    fun _ _ _ _ h => σ.injective h
  rwa [Fin.card_filter_val_lt, min_eq_right hle_m] at hle

/-- **Deterministic Pigeonhole Probe Bound**: for any table `T : Table U m`, key `u : Fin U`, and
probe permutation `σ : Equiv.Perm (Fin m)`, `probeCount T u σ ≤ (otherOccupiedSlots T u).card + 1`.
-/
theorem probeCount_le_card_otherOccupied_add_one {U m : ℕ} (T : Table U m) (u : Fin U)
    (σ : Equiv.Perm (Fin m)) :
    probeCount T u σ ≤ (otherOccupiedSlots T u).card + 1 := by
  rw [probeCount, unsuccessfulProbes, Nat.add_comm]
  exact Nat.add_le_add_right (missedProbes_le_card (otherOccupiedSlots T u) σ) 1

/-- Under `TableRep π s T`, `probeCount T u (π u) ≤ (Dictionary.dom s).card + 1` holds
deterministically for every key `u : Fin U`. -/
theorem probeCount_le_dom_card_add_one {U m : ℕ} {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T) (u : Fin U) :
    probeCount T u (π u) ≤ (Dictionary.dom s).card + 1 :=
  (probeCount_le_card_otherOccupied_add_one T u (π u)).trans
    (Nat.add_le_add_right (hrep.card_otherOccupiedSlots_le u) 1)

/-- Under `TableRep π s T` and `(Dictionary.dom s).card ≤ n_max`,
`probeCount T u (π u) ≤ n_max + 1` holds deterministically for every key `u : Fin U`. -/
theorem probeCount_le_add_one {U m n_max : ℕ} {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T)
    (hdom : (Dictionary.dom s).card ≤ n_max) (u : Fin U) :
    probeCount T u (π u) ≤ n_max + 1 :=
  (probeCount_le_dom_card_add_one hrep u).trans (Nat.add_le_add_right hdom 1)

/-- **Deterministic Expected Probe-Count Bound (`≤ n_max + 1`) for Any Full-Cycle Permutation
Family**: for any nonempty finite seed space `Θ` and any permutation family
`π : Θ → Fin U → Equiv.Perm (Fin m)` representing `s` in `T θ` with
`(Dictionary.dom s).card ≤ n_max`, the expected probe count of `u` under `PMF.uniformOfFintype Θ`
is at most `n_max + 1`. -/
theorem expect_probeCount_le_add_one
    {Θ : Type*} [Fintype Θ] [Nonempty Θ] {U m n_max : ℕ}
    {π : Θ → Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Θ → Table U m}
    (hrep : ∀ θ, TableRep (π θ) s (T θ))
    (hdom : (Dictionary.dom s).card ≤ n_max) (u : Fin U) :
    (∑' θ : Θ, PMF.uniformOfFintype Θ θ * (probeCount (T θ) u (π θ u) : ℝ≥0∞)) ≤
      (n_max + 1 : ℝ≥0∞) := by
  have hsum : (∑ θ : Θ, probeCount (T θ) u (π θ u)) ≤ (n_max + 1) * Fintype.card Θ :=
    (Finset.sum_le_sum fun θ _ => probeCount_le_add_one (hrep θ) hdom u).trans_eq
      (by simp [Nat.mul_comm])
  exact mod_cast Cslib.Probability.PMF.tsum_uniformOfFintype_le_of_sum_le hsum

end Cslib.DataStructure.Dictionary.UniformProbing
