/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.UniformProbing
public import CslibFrontier.Foundations.Data.Nat.OddMulMod
public import CslibFrontier.Probability.KWiseIndependent.DoubleTabulation
import CslibFrontier.Foundations.Data.Nat.Power
import CslibFrontier.Probability.KWiseIndependent.DoubleTabulation.Parameters
import CslibFrontier.Probability.KWiseIndependent.Restriction
import CslibFrontier.Probability.PMF.UniformBound
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.GetD
import Mathlib.Order.Interval.Finset.Nat
public import CslibFrontier.Tactic.WramOmega.Init
import CslibFrontier.Tactic.WramOmega

/-!
# Odd-Stride Double Hashing under Limited Independence and Double Tabulation

This module proves $O(1)$ expected probes for power-of-two odd-stride double hashing
`oddStridePerm h₁ h₂ u i = (h₁(u) + i * (2 * h₂(u) + 1)) mod 2 ^ M` ([CLRS2009], Section 11.4,
pp. 272–274) over open-addressed tables
`Cslib.DataStructure.Dictionary.UniformProbing.Table U (2 ^ M)`
with key universe size `U`, table bit-width `M` (`m = 2 ^ M` slots), and maximum stored key count
`n_max`. The bound holds both under $(2 L + 1)$-wise independence for probe cutoff
`L = maxProbeCutoff n_max = Nat.clog 2 (max n_max 4) + 4` and under Mikkel Thorup's Double
Tabulation (`[Thorup2013]`, Theorem 1(a) and Lemma 2) with `c` characters of `b` bits
(`U ≤ 2 ^ (c * b)`) or polynomial universe exponent `c_exp` (`U ≤ max n_max 4 ^ c_exp`).

Under the hypotheses of the cited theorems, the expected probe count is at most `2` under
$(2 L + 1)$-wise independence (`expect_probeCount_oddStride_of_kWiseIndependent`) and at most `3`
under Double Tabulation with an explicit code bound
(`expect_probeCount_oddStride_doubleTab_of_codeBound_le`). For the exponent `c_exp`, the bound `3`
is proved for `doubleTabThreshold c_exp ≤ n_max` (`expect_probeCount_oddStride_doubleTab_le`), where
`doubleTabThreshold c_exp = 2 ^ (2 * doubleTabMinB c_exp) ≥ 2 ^ 25088`. Below the threshold the
proof uses only the deterministic bound `probeCount ≤ n_max + 1` (`probeCount_le_add_one`), valid
for every probe permutation family representing the table; together the two cases give
`max (doubleTabThreshold c_exp : ℝ≥0∞) 3` for every `n_max`
(`expect_probeCount_oddStride_unconditional_le`).

## Source statements and notation mapping

* **J. P. Schmidt and A. Siegel ([SchmidtSiegel1990], STOC 1990, pp. 224–234; extended NYU Courant
  Technical Report `TR1995-687`, May 1995, pp. 1–2, 4–7, 37–39)**:
  - **Definition 1 (`TR1995-687`, p. 2)**: Sequential closed-hashing insertion of a key set $D$
    into a table of size $n$ (`[0..n - 1]`) over universe $[0..m - 1]$ along $1$-indexed per-key
    probe sequences $p(x, 1), p(x, 2), \dots$ and affine double hashing. Here we map table size to
    $m = 2^M$ (`Fin (2 ^ M)`), universe to `Fin U`, and probe sequences to $0$-indexed permutations
    `π u i`.
  - **Definition 2 (`Models UH, DH, and DH_ψ`, `TR1995-687`, pp. 4–5)**: Formulates two-probe slot
    uniformity (Condition 1, p. 4) and $\psi$-wise cross-key probe independence for
    $\psi = c \log n$ (Condition 2, p. 5).
  - **Definition 3 and Equation (1) (`[SchmidtSiegel1990]`, Theorem 1; `TR1995-687`, pp. 6–7)**:
    Defines the dependency set $\mathrm{dep}(x, D)$, dependency DAG $G(x, D)$, and partial
    dependency DAG $G_r(x, D)$ (vertices reachable from $x$ starting along the first $r$ probes of
    $x$). At bounded load factor $\alpha \le 1 / 32$, the trivial vacancy overestimator
    $q(i) \equiv 1$ yields $O(1)$ expected probes by bounding the probability of size-$w$ partial
    dependency witnesses without the vacancy inclusion-exclusion machinery needed for
    $\alpha \to 1$.
  - **Appendix A, Lemma A (`TR1995-687`, pp. 37–39)**: Bounds the probability that a $w$-vertex
    subset hashes into a dependency tree (Part 1, pp. 37–38) or into a non-tree dependency DAG with
    spanning tree $Tr$ (Part 2, pp. 38–39) by charging one non-tree collision per vertex with a
    diamond edge.
* **M. Thorup ([Thorup2013], FOCS 2013, pp. 90–99; arXiv:1311.3121v2, 16 October 2018, Section 1.1
  Theorem 1(a) and Lemma 2, and Section 3, pp. 4–5, 11–13)**:
  Conditioned on $k$-uniqueness (`IsKUnique k (simpleTabTuple T₁)`), `doubleTabHash` is $k$-wise
  independent (`isKWiseIndependentHash_doubleTabHash_of_isKUnique`), and the fraction of
  non-$k$-unique top seeds is at most $2 (\mathrm{doubleTabCodeBound}\ c\ (8c)\ 4\ k)^2 / 2^{6b}$
  (`card_not_isKUnique_eight_mul_le`).
* **Original elementary adaptations**:
  1. **Breadth-first search (`BFS`) spanning-tree ordering**: We order the vertices of a closed
     partial dependency set $W = \mathrm{partialDepSet}(x_0, r)$ by a flat BFS queue. Every
     non-tree probe of $x_b$ then hits a slot in the set $F_{< b}$ of slots already enqueued before
     $x_b$'s expansion, while the $h_{b+1}$ new tree-child slots of $x_b$ are the first $h_{b+1}$
     slots of $[\pi(x_b, 0), \dots, \pi(x_b, w - 1)]$ outside $F_{< b}$ independently of the
     landing index $k_b$.
  2. **Power-of-two quotient fiber bound (`Nat.card_odd_mul_mod_eq_le`)**: On $m = 2^M$, an even
     probe-index difference $\Delta = k_b - j_1 \in [1, w]$ is not invertible mod $2^M$, but the
     Euclidean quotient map $s \mapsto \lfloor \Delta(2s + 1)/2^M \rfloor \in \mathrm{Fin}\ \Delta$
     bounds the stride fiber by $\Delta \le w$.
  3. **Deterministic pigeonhole bound & high-probability conditioning bridge**: Every odd stride
     $2 h_2(u) + 1$ is coprime to $2^M$, so `oddStridePerm` is a full-cycle permutation on *every*
     seed and `probeCount ≤ n_max + 1` holds deterministically (`probeCount_le_add_one`). This
     bounds both the bad-top-seed tail for $n_{\max} \ge \mathrm{doubleTabThreshold}\ c_{\exp}$ and
     the entire small-capacity regime $n_{\max} < \mathrm{doubleTabThreshold}\ c_{\exp}$.

## Main definitions

* `Cslib.DataStructure.Dictionary.DoubleHashing.OrderedTableRep`: open-addressed representation
  invariant
  extending `UniformProbing.TableRep` with an acyclic insertion-order rank.
* `Cslib.DataStructure.Dictionary.DoubleHashing.oddStrideSeq`,
  `Cslib.DataStructure.Dictionary.DoubleHashing.oddStridePerm`,
  `Cslib.DataStructure.Dictionary.DoubleHashing.twoStageOddStridePerm`: full-cycle odd-stride
  double-hashing
  probe sequence and permutation families on `Fin (2 ^ M)`.
* `Cslib.DataStructure.Dictionary.DoubleHashing.maxProbeCutoff`,
  `Cslib.DataStructure.Dictionary.DoubleHashing.DoubleTabOddStrideSeed`,
  `Cslib.DataStructure.Dictionary.DoubleHashing.doubleTabOddStridePerm`,
  `Cslib.DataStructure.Dictionary.DoubleHashing.DoubleHashSeed`,
  `Cslib.DataStructure.Dictionary.DoubleHashing.doubleHashOddStridePerm`: cutoff parameter and
  Double
  Tabulation seed types and permutation families.

## Main results

* `Cslib.DataStructure.Dictionary.DoubleHashing.OrderedTableRep.empty`,
  `Cslib.DataStructure.Dictionary.DoubleHashing.OrderedTableRep.tableInsert`,
  `Cslib.DataStructure.Dictionary.DoubleHashing.orderedTableRep_runTable`,
  `Cslib.DataStructure.Dictionary.DoubleHashing.exists_orderedTableRep`: preservation and existence
  of
  `OrderedTableRep`.
* `Cslib.DataStructure.Dictionary.DoubleHashing.sum_probeCount_oddStride_le_of_kWiseIndependent`,
  `Cslib.DataStructure.Dictionary.DoubleHashing.expect_probeCount_oddStride_of_kWiseIndependent`:
  expected
  probe count $\le 2$ under $(2 L + 1)$-wise independent $(h_1, h_2)$.
* `Cslib.DataStructure.Dictionary.DoubleHashing.sum_probeCount_oddStride_of_whp_kWiseIndependent`,
  `Cslib.DataStructure.Dictionary.DoubleHashing.expect_probeCount_oddStride_of_whp_kWiseIndependent`
  expected probe count $\le 3$ under high-probability $(2 L + 1)$-wise independence.
* `Cslib.DataStructure.Dictionary.DoubleHashing.sum_probeCount_oddStride_doubleTab_le`,
  `Cslib.DataStructure.Dictionary.DoubleHashing.expect_probeCount_oddStride_doubleTab_le`,
  `Cslib.DataStructure.Dictionary.DoubleHashing.expect_probeCount_oddStride_unconditional_le`:
  expected probe
  count $\le 3$ under Double Tabulation for $n_{\max} \ge \mathrm{doubleTabThreshold}\ c_{\exp}$,
  and $\le \max(\mathrm{doubleTabThreshold}\ c_{\exp}, 3)$ for all $n_{\max}$.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein,
  *Introduction to Algorithms*, third edition (MIT Press, 2009), Section 11.4,
  pp. 269–277][CLRS2009]
* [J. P. Schmidt and A. Siegel, *The Analysis of Closed Hashing under Limited
  Randomness*][SchmidtSiegel1990]
* [M. Thorup, *Simple Tabulation, Fast Expanders, Double Tabulation, and High
  Independence*][Thorup2013]
-/

public section

namespace Cslib.DataStructure.Dictionary.DoubleHashing

open Cslib.DataStructure.Dictionary.UniformProbing
open Cslib.Probability
open scoped BigOperators ENNReal

/-! ## Section 1: Acyclic Insertion-Order Invariant (`OrderedTableRep`) -/

/-- Open-addressed table representation invariant extending `TableRep π s T` with an acyclic
insertion-order witness `rank : Fin U → ℕ`: for every stored key `w ∈ Dictionary.dom s` and every
failed probe index `i : Fin m` with `i.val < missedProbes (otherOccupiedSlots T w) (π w)`, the slot
`π w i` holds a distinct key `y ∈ (Dictionary.dom s).erase w` with `rank y < rank w`. -/
structure OrderedTableRep {U m : ℕ} (π : Fin U → Equiv.Perm (Fin m)) (s : Dictionary.State U)
    (T : Table U m) : Prop extends TableRep π s T where
  /-- Existence of an insertion-order ranking under which every failed probe of a stored key `w`
  is blocked by a strictly lower-ranked key `y ∈ (Dictionary.dom s).erase w`. -/
  exists_rank : ∃ rank : Fin U → ℕ,
    ∀ w ∈ Dictionary.dom s, ∀ i : Fin m,
      i.val < missedProbes (otherOccupiedSlots T w) (π w) →
        ∃ y ∈ (Dictionary.dom s).erase w, ∃ vy : ℕ,
          T (π w i) = some (y, vy) ∧ rank y < rank w

/-- The empty table satisfies `OrderedTableRep` under any permutation family `π`. -/
theorem OrderedTableRep.empty {U m : ℕ} (π : Fin U → Equiv.Perm (Fin m)) :
    OrderedTableRep π (Dictionary.empty U) (emptyTable U m) where
  toTableRep := tableRep_empty π
  exists_rank := ⟨fun _ => 0, fun w hw => by simp [Dictionary.empty, Dictionary.dom] at hw⟩

/-- **Preservation of `OrderedTableRep` under `tableInsert`**: if `OrderedTableRep π s T` and
`(otherOccupiedSlots T u).card < m`, then `tableInsert hm π T u v` satisfies
`OrderedTableRep π (Function.update s u (some v))`. -/
theorem OrderedTableRep.tableInsert {U m : ℕ} (hm : 0 < m) {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : OrderedTableRep π s T) (u : Fin U) (v : ℕ)
    (hO : (otherOccupiedSlots T u).card < m) :
    OrderedTableRep π (Function.update s u (some v))
      (UniformProbing.tableInsert hm π T u v) where
  toTableRep := hrep.toTableRep.tableInsert hm u v hO
  exists_rank := by
    classical
    obtain ⟨rank, hrank⟩ := hrep.exists_rank
    have htarget := hrep.toTableRep.apply_targetSlot u hO
    -- Every stored key keeps its slot; only the value at the target slot may change.
    have hval : ∀ {j y vy}, T j = some (y, vy) →
        ∃ vy', UniformProbing.tableInsert hm π T u v j = some (y, vy') := fun {j y vy} hT => by
      rw [tableInsert_eq_update_targetSlot hm π T u v hO, Function.update_apply]
      split_ifs with hj
      · rw [← hj, hT] at htarget
        cases hsu : s u <;> simp_all
      · exact ⟨vy, hT⟩
    -- Stored keys keep their rank; a fresh key is ranked above all of them.
    refine ⟨fun y => if y ∈ Dictionary.dom s then rank y else (Dictionary.dom s).sup rank + 1,
      fun w hw i hi => ?_⟩
    rw [Dictionary.dom_insert] at hw ⊢
    by_cases hw_dom : w ∈ Dictionary.dom s
    · rw [hrep.toTableRep.missedProbes_tableInsert_of_isSome hm u v hO
        (Dictionary.mem_dom_iff_isSome.mp hw_dom)] at hi
      obtain ⟨y, hy, vy, hTwi, hlt_rank⟩ := hrank w hw_dom i hi
      obtain ⟨vy', h⟩ := hval hTwi
      exact ⟨y, Finset.erase_subset_erase w (Finset.subset_insert u _) hy, vy', h,
        by simpa [Finset.mem_of_mem_erase hy, hw_dom] using hlt_rank⟩
    · obtain rfl : w = u := by simpa [hw_dom] using hw
      rw [otherOccupiedSlots_tableInsert_self hm hrep.toTableRep w v hO] at hi
      obtain ⟨y, vy, hTwi, hyw⟩ := mem_otherOccupiedSlots_iff.mp (mem_of_lt_probeSlotIndex hO hi)
      have hy_dom := Dictionary.mem_dom_iff.mpr ⟨vy, (hrep.toTableRep.slot_spec _ y vy hTwi).1⟩
      obtain ⟨vy', h⟩ := hval hTwi
      exact ⟨y, by simp [hyw, hy_dom], vy', h,
        by simpa [hy_dom, hw_dom, Nat.lt_succ_iff] using Finset.le_sup hy_dom⟩

/-- Convenience wrapper for `OrderedTableRep.tableInsert` when `(Dictionary.dom s).card < m`. -/
theorem OrderedTableRep.tableInsert_of_card_lt {U m : ℕ} {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : OrderedTableRep π s T)
    (hcard : (Dictionary.dom s).card < m) (u : Fin U) (v : ℕ) :
    OrderedTableRep π (Function.update s u (some v))
      (UniformProbing.tableInsert (Nat.pos_of_ne_zero (by omega)) π T u v) :=
  hrep.tableInsert (Nat.pos_of_ne_zero (by omega)) u v
    (lt_of_le_of_lt (hrep.toTableRep.card_otherOccupiedSlots_le u) hcard)

/-- Any valid operation history preserves `OrderedTableRep`. -/
theorem orderedTableRep_runTableFrom {U V n_max m : ℕ} (hm : 0 < m) (hcap : n_max ≤ m)
    (π : Fin U → Equiv.Perm (Fin m)) {s : Dictionary.State U} {T : Table U m}
    (hrep : OrderedTableRep π s T) (hs : (Dictionary.dom s).card ≤ n_max)
    {ops : List (Dictionary.Op U)} (hvh : (Dictionary.spec U V n_max).ValidHistory s ops) :
    OrderedTableRep π ((Dictionary.spec U V n_max).run s ops).1 (runTableFrom hm π T ops) := by
  induction ops generalizing s T with
  | nil => exact hrep
  | cons o os ih =>
    have hs' := Dictionary.card_dom_step_le_of_valid hs hvh.1
    cases o with
    | query u => exact ih hrep hs' hvh.2
    | insert u v =>
      exact ih (hrep.tableInsert hm u v
        (hrep.toTableRep.card_otherOccupiedSlots_lt_of_valid hm hcap hs hvh.1)) hs' hvh.2

/-- Running any valid operation history from `emptyTable U m` produces a table satisfying
`OrderedTableRep`. -/
theorem orderedTableRep_runTable {U V n_max m : ℕ} (hm : 0 < m) (hcap : n_max ≤ m)
    (π : Fin U → Equiv.Perm (Fin m)) {ops : List (Dictionary.Op U)}
    (hvh : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U) ops) :
    OrderedTableRep π ((Dictionary.spec U V n_max).run (Dictionary.empty U) ops).1
      (runTable hm π ops) :=
  orderedTableRep_runTableFrom hm hcap π (OrderedTableRep.empty π) (by simp) hvh

/-- Every finite dictionary state `s` with `(Dictionary.dom s).card ≤ m` admits an open-addressed
table `T : Table U m` satisfying `OrderedTableRep π s T` for any permutation family
`π : Fin U → Equiv.Perm (Fin m)`. -/
theorem exists_orderedTableRep {U m : ℕ} (π : Fin U → Equiv.Perm (Fin m))
    (s : Dictionary.State U) (hcard : (Dictionary.dom s).card ≤ m) :
    ∃ T : Table U m, OrderedTableRep π s T := by
  induction hD : Dictionary.dom s using Finset.induction_on generalizing s with
  | empty =>
    obtain rfl : s = Dictionary.empty U :=
      funext fun w => Dictionary.notMem_dom_iff.mp (by simp [hD])
    exact ⟨emptyTable U m, .empty π⟩
  | @insert a D' ha ih =>
    obtain ⟨va, hsa⟩ := Dictionary.mem_dom_iff.mp (hD ▸ Finset.mem_insert_self a D')
    rw [hD, Finset.card_insert_of_notMem ha] at hcard
    have hD' : Dictionary.dom (Function.update s a none) = D' := by
      rw [← Finset.erase_insert ha, ← hD]
      ext w
      by_cases hwa : w = a <;> simp [hwa]
    obtain ⟨T', hrep'⟩ := ih _ (hD' ▸ Nat.le_of_succ_le hcard) hD'
    have := hrep'.tableInsert_of_card_lt (hD' ▸ hcard) a va
    rw [Function.update_idem, Function.update_eq_self_iff.mpr hsa.symm] at this
    exact ⟨_, this⟩

/-! ## Section 2: Odd-Stride Double-Hashing Probe Permutation on `Fin (2 ^ M)` -/

/-- Power-of-two odd-stride double-hashing probe sequence
`oddStrideSeq M p s i = (p + i * (2 * s + 1)) mod 2 ^ M` on `Fin (2 ^ M)` ([CLRS2009], Section 11.4,
"Double hashing", pp. 272–274). -/
@[expose] def oddStrideSeq (M : ℕ) (p : Fin (2 ^ M)) (s : Fin (2 ^ (M - 1)))
    (i : Fin (2 ^ M)) : Fin (2 ^ M) :=
  ⟨(p.val + i.val * (2 * s.val + 1)) % 2 ^ M, Nat.mod_lt _ (Nat.two_pow_pos M)⟩

/-- Because `2 * s.val + 1` is odd and therefore coprime to `2 ^ M`, `oddStrideSeq M p s` is a
bijection on `Fin (2 ^ M)` for every `p` and `s`. -/
theorem bijective_oddStrideSeq (M : ℕ) (p : Fin (2 ^ M)) (s : Fin (2 ^ (M - 1))) :
    Function.Bijective (oddStrideSeq M p s) := by
  refine Function.Injective.bijective_of_finite fun i j heq => Fin.ext ?_
  have hmod : p.val + i.val * (2 * s.val + 1) ≡ p.val + j.val * (2 * s.val + 1) [MOD 2 ^ M] :=
    Fin.ext_iff.mp heq
  exact (Nat.ModEq.cancel_right_of_coprime
    ((Nat.coprime_two_left.mpr (odd_two_mul_add_one s.val)).pow_left M)
    (Nat.ModEq.add_left_cancel' _ hmod)).eq_of_lt_of_lt i.isLt j.isLt

/-- Noncomputable full-cycle permutation `Equiv.Perm (Fin (2 ^ M))` induced by primary hash value
`p : Fin (2 ^ M)` and stride index `s : Fin (2 ^ (M - 1))`. -/
noncomputable def oddStridePermOfPair (M : ℕ) (p : Fin (2 ^ M)) (s : Fin (2 ^ (M - 1))) :
    Equiv.Perm (Fin (2 ^ M)) :=
  Equiv.ofBijective (oddStrideSeq M p s) (bijective_oddStrideSeq M p s)

@[simp]
theorem oddStridePermOfPair_apply (M : ℕ) (p : Fin (2 ^ M)) (s : Fin (2 ^ (M - 1)))
    (i : Fin (2 ^ M)) :
    oddStridePermOfPair M p s i = oddStrideSeq M p s i := by
  rfl

/-- Odd-stride double-hashing permutation family `Fin U → Equiv.Perm (Fin (2 ^ M))` constructed
from a primary hash function `h₁ : Fin U → Fin (2 ^ M)` and a half-range stride hash function
`h₂ : Fin U → Fin (2 ^ (M - 1))`. -/
noncomputable def oddStridePerm {U M : ℕ} (h₁ : Fin U → Fin (2 ^ M))
    (h₂ : Fin U → Fin (2 ^ (M - 1))) (u : Fin U) : Equiv.Perm (Fin (2 ^ M)) :=
  oddStridePermOfPair M (h₁ u) (h₂ u)

@[simp]
theorem oddStridePerm_apply {U M : ℕ} (h₁ : Fin U → Fin (2 ^ M))
    (h₂ : Fin U → Fin (2 ^ (M - 1))) (u : Fin U) (i : Fin (2 ^ M)) :
    oddStridePerm h₁ h₂ u i = oddStrideSeq M (h₁ u) (h₂ u) i := by
  rfl

theorem val_oddStridePerm {U M : ℕ} (h₁ : Fin U → Fin (2 ^ M))
    (h₂ : Fin U → Fin (2 ^ (M - 1))) (u : Fin U) (i : Fin (2 ^ M)) :
    (oddStridePerm h₁ h₂ u i).val =
      ((h₁ u).val + i.val * (2 * (h₂ u).val + 1)) % 2 ^ M := by
  rfl

/-! ## Section 3: Dependency Sets and the Minimal Overflow Dichotomy -/

/-- Maximum probe-depth cutoff `L = Nat.clog 2 (max n_max 4) + 4` for the partial dependency
dichotomy ([SchmidtSiegel1990], Theorem 1). -/
@[expose, wram_arith] def maxProbeCutoff (n_max : ℕ) : ℕ :=
  Nat.clog 2 (max n_max 4) + 4

/-- Extended insertion-order rank placing an absent query key `u ∉ Dictionary.dom s` strictly
above all stored keys in `Dictionary.dom s`. -/
private def extRank {U : ℕ} (s : Dictionary.State U) (rank : Fin U → ℕ) (u : Fin U) :
    Fin U → ℕ :=
  if u ∈ Dictionary.dom s then rank
  else Function.update rank u ((Dictionary.dom s).sup rank + 1)

private theorem extRank_blocker_spec {U m : ℕ} {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T)
    {rank : Fin U → ℕ}
    (hrank : ∀ w ∈ Dictionary.dom s, ∀ i : Fin m,
      i.val < missedProbes (otherOccupiedSlots T w) (π w) →
        ∃ y ∈ (Dictionary.dom s).erase w, ∃ vy : ℕ,
          T (π w i) = some (y, vy) ∧ rank y < rank w)
    (u : Fin U) {x : Fin U} (hx : x ∈ insert u (Dictionary.dom s))
    {i : Fin m} (hi : i.val < missedProbes (otherOccupiedSlots T x) (π x)) :
    ∃ y ∈ (Dictionary.dom s).erase x, ∃ vy : ℕ,
      T (π x i) = some (y, vy) ∧ extRank s rank u y < extRank s rank u x := by
  classical
  have hmem_eq {z : Fin U} (hz : z ∈ Dictionary.dom s) : extRank s rank u z = rank z := by
    unfold extRank
    split_ifs with hu
    exacts [rfl, Function.update_of_ne (fun h : z = u => hu (h ▸ hz)) _ _]
  by_cases hx_dom : x ∈ Dictionary.dom s
  · obtain ⟨y, hy, vy, hT, hlt⟩ := hrank x hx_dom i hi
    exact ⟨y, hy, vy, hT, by rwa [hmem_eq (Finset.mem_erase.mp hy).2, hmem_eq hx_dom]⟩
  · obtain rfl : x = u := by simpa [hx_dom] using hx
    obtain ⟨y, vy, hT, hyx⟩ := mem_otherOccupiedSlots_iff.mp
      ((le_missedProbes_iff_allOccupied (missedProbes_le _ _) (π x)).mp le_rfl i hi)
    have hy_dom : y ∈ Dictionary.dom s :=
      Dictionary.mem_dom_iff.mpr ⟨vy, (hrep.slot_spec _ y vy hT).1⟩
    refine ⟨y, Finset.mem_erase.mpr ⟨hyx, hy_dom⟩, vy, hT, ?_⟩
    rw [hmem_eq hy_dom]
    simpa [extRank, hx_dom, Nat.lt_succ_iff] using Finset.le_sup hy_dom

/-- Keys `y : Fin U` with `r_ext y < r_ext x` that occupy a slot `π x i` among the first
`min r (missedProbes (otherOccupiedSlots T x) (π x))` probes of `x`. -/
private def directBlockers {U m : ℕ} (T : Table U m) (π : Fin U → Equiv.Perm (Fin m))
    (r_ext : Fin U → ℕ) (x : Fin U) (r : ℕ) : Finset (Fin U) :=
  Finset.univ.filter fun y =>
    r_ext y < r_ext x ∧
      ∃ i : Fin m, i.val < r ∧ i.val < missedProbes (otherOccupiedSlots T x) (π x) ∧
        (T (π x i)).map Prod.fst = some y

/-- Full dependency set of key `x` (including `x` itself), defined by well-founded recursion on
`r_ext x` ([SchmidtSiegel1990], Definition 3). -/
private def depSet {U m : ℕ} (T : Table U m) (π : Fin U → Equiv.Perm (Fin m))
    (r_ext : Fin U → ℕ) (x : Fin U) : Finset (Fin U) :=
  insert x ((directBlockers T π r_ext x m).attach.biUnion fun ⟨y, hy⟩ =>
    have : r_ext y < r_ext x := (Finset.mem_filter.mp hy).2.1
    depSet T π r_ext y)
termination_by r_ext x

/-- Partial dependency set of key `x` along its first `r` probes (excluding `x` itself), defined as
the union of `depSet T π r_ext y` over `y ∈ directBlockers T π r_ext x r` ([SchmidtSiegel1990],
Definition 3, $G_r(x, D)$). -/
private def partialDepSet {U m : ℕ} (T : Table U m) (π : Fin U → Equiv.Perm (Fin m))
    (r_ext : Fin U → ℕ) (x : Fin U) (r : ℕ) : Finset (Fin U) :=
  (directBlockers T π r_ext x r).biUnion (depSet T π r_ext)

private theorem depSet_eq {U m : ℕ} (T : Table U m) (π : Fin U → Equiv.Perm (Fin m))
    (r_ext : Fin U → ℕ) (x : Fin U) :
    depSet T π r_ext x = insert x (partialDepSet T π r_ext x m) := by
  rw [depSet, partialDepSet]
  ext z
  simp

private theorem self_mem_depSet {U m : ℕ} (T : Table U m) (π : Fin U → Equiv.Perm (Fin m))
    (r_ext : Fin U → ℕ) (x : Fin U) :
    x ∈ depSet T π r_ext x :=
  depSet_eq T π r_ext x ▸ Finset.mem_insert_self x _

private theorem partialDepSet_zero {U m : ℕ} (T : Table U m) (π : Fin U → Equiv.Perm (Fin m))
    (r_ext : Fin U → ℕ) (x : Fin U) :
    partialDepSet T π r_ext x 0 = ∅ := by
  simp [partialDepSet, directBlockers]

private theorem directBlockers_eq_of_missedProbes_le {U m : ℕ} (T : Table U m)
    (π : Fin U → Equiv.Perm (Fin m)) (r_ext : Fin U → ℕ) (x : Fin U) {r : ℕ}
    (hr : missedProbes (otherOccupiedSlots T x) (π x) ≤ r) :
    directBlockers T π r_ext x r = directBlockers T π r_ext x m := by
  ext y
  simp only [directBlockers, Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_congr_right fun _ => exists_congr fun i =>
    ⟨fun ⟨_, h2, h3⟩ => ⟨i.isLt, h2, h3⟩, fun ⟨_, h2, h3⟩ => ⟨lt_of_lt_of_le h2 hr, h2, h3⟩⟩

private theorem mem_partialDepSet_of_mem_directBlockers {U m : ℕ} (T : Table U m)
    (π : Fin U → Equiv.Perm (Fin m)) (r_ext : Fin U → ℕ) {x y : Fin U} {r : ℕ}
    (hy : y ∈ directBlockers T π r_ext x r) :
    y ∈ partialDepSet T π r_ext x r :=
  Finset.mem_biUnion.mpr ⟨y, hy, self_mem_depSet T π r_ext y⟩

private theorem mem_depSet_of_mem_directBlockers {U m : ℕ} (T : Table U m)
    (π : Fin U → Equiv.Perm (Fin m)) (r_ext : Fin U → ℕ) {x y : Fin U}
    (hy : y ∈ directBlockers T π r_ext x m) :
    y ∈ depSet T π r_ext x :=
  depSet_eq T π r_ext x ▸
    Finset.mem_insert_of_mem (mem_partialDepSet_of_mem_directBlockers T π r_ext hy)

private theorem exists_val_of_map_fst_eq_some {U m : ℕ} {T : Table U m} {slot : Fin m}
    {y : Fin U} (h : (T slot).map Prod.fst = some y) :
    ∃ vy : ℕ, T slot = some (y, vy) := by
  obtain ⟨⟨y', vy⟩, hT, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨vy, hT⟩

private theorem partialDepSet_eq_of_missedProbes_le {U m : ℕ} (T : Table U m)
    (π : Fin U → Equiv.Perm (Fin m)) (r_ext : Fin U → ℕ) (x : Fin U) {r : ℕ}
    (hr : missedProbes (otherOccupiedSlots T x) (π x) ≤ r) :
    partialDepSet T π r_ext x r = partialDepSet T π r_ext x m := by
  simp only [partialDepSet, directBlockers_eq_of_missedProbes_le T π r_ext x hr]

private theorem rank_le_and_depSet_subset_of_mem_depSet {U m : ℕ} (T : Table U m)
    (π : Fin U → Equiv.Perm (Fin m)) (r_ext : Fin U → ℕ) (x : Fin U) :
    ∀ {z : Fin U}, z ∈ depSet T π r_ext x →
      r_ext z ≤ r_ext x ∧ depSet T π r_ext z ⊆ depSet T π r_ext x := by
  induction hx : r_ext x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    intro z hz
    rw [depSet_eq, Finset.mem_insert, partialDepSet, Finset.mem_biUnion] at hz
    obtain rfl | ⟨y, hy_dir, hzy⟩ := hz
    · exact ⟨hx.le, subset_rfl⟩
    · have hy_lt : r_ext y < n := hx ▸ (Finset.mem_filter.mp hy_dir).2.1
      obtain ⟨hzy_le, hsub_zy⟩ := ih (r_ext y) hy_lt y rfl hzy
      exact ⟨by omega, hsub_zy.trans fun w hw => depSet_eq T π r_ext x ▸
        Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨y, hy_dir, hw⟩)⟩

private theorem rank_lt_and_depSet_subset_of_mem_partialDepSet {U m : ℕ} (T : Table U m)
    (π : Fin U → Equiv.Perm (Fin m)) (r_ext : Fin U → ℕ) (x : Fin U) (r : ℕ)
    {z : Fin U} (hz : z ∈ partialDepSet T π r_ext x r) :
    r_ext z < r_ext x ∧ depSet T π r_ext z ⊆ partialDepSet T π r_ext x r := by
  obtain ⟨y, hy_dir, hzy⟩ := Finset.mem_biUnion.mp hz
  obtain ⟨hzy_le, hsub_zy⟩ := rank_le_and_depSet_subset_of_mem_depSet T π r_ext y hzy
  exact ⟨hzy_le.trans_lt (Finset.mem_filter.mp hy_dir).2.1,
    hsub_zy.trans (Finset.subset_biUnion_of_mem _ hy_dir)⟩

private theorem notMem_partialDepSet_self {U m : ℕ} (T : Table U m)
    (π : Fin U → Equiv.Perm (Fin m)) (r_ext : Fin U → ℕ) (x : Fin U) (r : ℕ) :
    x ∉ partialDepSet T π r_ext x r :=
  fun hx => lt_irrefl _ (rank_lt_and_depSet_subset_of_mem_partialDepSet T π r_ext x r hx).1

private theorem card_depSet_eq {U m : ℕ} (T : Table U m) (π : Fin U → Equiv.Perm (Fin m))
    (r_ext : Fin U → ℕ) (x : Fin U) :
    (depSet T π r_ext x).card =
      1 + (partialDepSet T π r_ext x (missedProbes (otherOccupiedSlots T x) (π x))).card := by
  rw [depSet_eq, ← partialDepSet_eq_of_missedProbes_le T π r_ext x le_rfl,
    Finset.card_insert_of_notMem (notMem_partialDepSet_self T π r_ext x _), Nat.add_comm]

private theorem depSet_subset_of_directBlockers_closed {U m : ℕ} (T : Table U m)
    (π : Fin U → Equiv.Perm (Fin m)) (r_ext : Fin U → ℕ) {C : Finset (Fin U)}
    (hclosed : ∀ z ∈ C, directBlockers T π r_ext z m ⊆ C) {y : Fin U} (hy : y ∈ C) :
    depSet T π r_ext y ⊆ C := by
  induction hn : r_ext y using Nat.strong_induction_on generalizing y with
  | _ n ih =>
    intro w hw
    rw [depSet_eq, Finset.mem_insert, partialDepSet, Finset.mem_biUnion] at hw
    obtain rfl | ⟨z, hz_dir, hwz⟩ := hw
    · exact hy
    · exact ih (r_ext z) (hn ▸ (Finset.mem_filter.mp hz_dir).2.1) (hclosed y hy hz_dir) rfl hwz

private theorem mem_dom_of_mem_directBlockers {U m : ℕ} {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T)
    {r_ext : Fin U → ℕ} {x y : Fin U} {r : ℕ} (hy : y ∈ directBlockers T π r_ext x r) :
    y ∈ Dictionary.dom s := by
  obtain ⟨-, -, i, -, -, hTy⟩ := Finset.mem_filter.mp hy
  obtain ⟨vy, hTi⟩ := exists_val_of_map_fst_eq_some hTy
  exact Dictionary.mem_dom_iff.mpr ⟨vy, (hrep.slot_spec _ y vy hTi).1⟩

private theorem mem_dom_of_mem_partialDepSet {U m : ℕ} {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T)
    (r_ext : Fin U → ℕ) (x : Fin U) (r : ℕ) {z : Fin U}
    (hz : z ∈ partialDepSet T π r_ext x r) :
    z ∈ Dictionary.dom s := by
  obtain ⟨y, hy, hzy⟩ := Finset.mem_biUnion.mp hz
  exact depSet_subset_of_directBlockers_closed T π r_ext
    (fun _ _ _ h => mem_dom_of_mem_directBlockers hrep h) (mem_dom_of_mem_directBlockers hrep hy)
    hzy

private theorem partialDepSet_subset_erase {U m : ℕ} {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T)
    {r_ext : Fin U → ℕ} {u x : Fin U} (hx_le : r_ext x ≤ r_ext u) (r : ℕ) :
    partialDepSet T π r_ext x r ⊆ ((Dictionary.dom s).erase u).erase x := by
  intro z hz
  have hlt_x := (rank_lt_and_depSet_subset_of_mem_partialDepSet T π r_ext x r hz).1
  exact Finset.mem_erase.mpr ⟨by rintro rfl; omega, Finset.mem_erase.mpr
    ⟨by rintro rfl; omega, mem_dom_of_mem_partialDepSet hrep r_ext x r hz⟩⟩

private theorem card_partialDepSet_ge {U m : ℕ} {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T)
    {rank : Fin U → ℕ}
    (hrank : ∀ w ∈ Dictionary.dom s, ∀ i : Fin m,
      i.val < missedProbes (otherOccupiedSlots T w) (π w) →
        ∃ y ∈ (Dictionary.dom s).erase w, ∃ vy : ℕ,
          T (π w i) = some (y, vy) ∧ rank y < rank w)
    (u : Fin U) {x : Fin U} (hx : x ∈ insert u (Dictionary.dom s)) {r : ℕ}
    (hr : r ≤ missedProbes (otherOccupiedSlots T x) (π x)) :
    r ≤ (partialDepSet T π (extRank s rank u) x r).card := by
  classical
  have hrm : r ≤ m := hr.trans (missedProbes_le _ _)
  have hbl : ∀ i : Fin r, ∃ y ∈ directBlockers T π (extRank s rank u) x r,
      ∃ vy, T (π x (i.castLE hrm)) = some (y, vy) := fun i => by
    obtain ⟨y, _, vy, hT, hlt⟩ :=
      extRank_blocker_spec hrep hrank u hx (i := i.castLE hrm) (i.isLt.trans_le hr)
    exact ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, i.castLE hrm, i.isLt,
      i.isLt.trans_le hr, by simp [hT]⟩, vy, hT⟩
  choose f hf_mem hf_T using hbl
  have hinj : Function.Injective f := fun i₁ i₂ heq => by
    obtain ⟨vy₁, hT₁⟩ := hf_T i₁
    obtain ⟨vy₂, hT₂⟩ := hf_T i₂
    exact Fin.castLE_injective hrm
      ((π x).injective (hrep.slot_eq_of_same_key (heq ▸ hT₁) hT₂))
  simpa using Finset.card_le_card_of_injOn (s := Finset.univ) f
    (fun i _ => mem_partialDepSet_of_mem_directBlockers T π _ (hf_mem i)) hinj.injOn

private theorem missedProbes_lt_card_of_mem_partialDepSet {U m : ℕ}
    {π : Fin U → Equiv.Perm (Fin m)} {s : Dictionary.State U} {T : Table U m}
    (hrep : TableRep π s T) {rank : Fin U → ℕ}
    (hrank : ∀ w ∈ Dictionary.dom s, ∀ i : Fin m,
      i.val < missedProbes (otherOccupiedSlots T w) (π w) →
        ∃ y ∈ (Dictionary.dom s).erase w, ∃ vy : ℕ,
          T (π w i) = some (y, vy) ∧ rank y < rank w)
    (u x : Fin U) (r : ℕ) {z : Fin U}
    (hz : z ∈ partialDepSet T π (extRank s rank u) x r) :
    missedProbes (otherOccupiedSlots T z) (π z) <
      (partialDepSet T π (extRank s rank u) x r).card := by
  have hcard_le := Finset.card_le_card
    (rank_lt_and_depSet_subset_of_mem_partialDepSet T π (extRank s rank u) x r hz).2
  rw [card_depSet_eq] at hcard_le
  have hge := card_partialDepSet_ge hrep hrank u (Finset.mem_insert_of_mem
    (mem_dom_of_mem_partialDepSet hrep (extRank s rank u) x r hz)) le_rfl
  omega

private theorem partialDepSet_succ_subset_union {U m : ℕ} {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T)
    {rank : Fin U → ℕ}
    (hrank : ∀ w ∈ Dictionary.dom s, ∀ i : Fin m,
      i.val < missedProbes (otherOccupiedSlots T w) (π w) →
        ∃ y ∈ (Dictionary.dom s).erase w, ∃ vy : ℕ,
          T (π w i) = some (y, vy) ∧ rank y < rank w)
    (u : Fin U) {x : Fin U} (hx : x ∈ insert u (Dictionary.dom s)) {r : ℕ}
    (hr : r < missedProbes (otherOccupiedSlots T x) (π x)) :
    ∃ z ∈ (Dictionary.dom s).erase x,
      extRank s rank u z < extRank s rank u x ∧
      partialDepSet T π (extRank s rank u) x (r + 1) ⊆
        partialDepSet T π (extRank s rank u) x r ∪ depSet T π (extRank s rank u) z := by
  have hrm : r < m := hr.trans_le (missedProbes_le _ _)
  obtain ⟨z, hz_erase, vz, hTz, hlt_z⟩ :=
    extRank_blocker_spec hrep hrank u hx (i := ⟨r, hrm⟩) hr
  refine ⟨z, hz_erase, hlt_z, fun w hw => ?_⟩
  simp only [partialDepSet, directBlockers, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_union] at hw ⊢
  obtain ⟨y, ⟨hy_lt, i, hi_lt, hi_mp, hTy⟩, hwy⟩ := hw
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi_lt with hi_r | hi_eq
  · exact .inl ⟨y, ⟨hy_lt, i, hi_r, hi_mp, hTy⟩, hwy⟩
  · obtain rfl : i = ⟨r, hrm⟩ := Fin.ext hi_eq
    obtain rfl : z = y := by simpa [hTz] using hTy
    exact .inr hwy

/-- **Minimal Overflow Dichotomy ([SchmidtSiegel1990], Theorem 1 & Lemma A)**:
for any `L ≥ 1` and query key `u : Fin U`, either
1. **(Normal Regime)** `missedProbes (otherOccupiedSlots T u) (π u) < L` and
   `(partialDepSet T π (extRank s rank u) u
     (missedProbes (otherOccupiedSlots T u) (π u))).card < L`,
   or
2. **(Overflow Regime)** there exist `x₀ ∈ insert u (Dictionary.dom s)` with
   `extRank s rank u x₀ ≤ extRank s rank u u` and `r₀ : ℕ` with
   `1 ≤ r₀ ∧ r₀ ≤ min (missedProbes (otherOccupiedSlots T x₀) (π x₀)) L` such that
   `L ≤ (partialDepSet T π (extRank s rank u) x₀ r₀).card` and
   `(partialDepSet T π (extRank s rank u) x₀ r₀).card < 2 * L`. -/
private theorem dichotomy_partialDepSet {U m : ℕ} {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T)
    {rank : Fin U → ℕ}
    (hrank : ∀ w ∈ Dictionary.dom s, ∀ i : Fin m,
      i.val < missedProbes (otherOccupiedSlots T w) (π w) →
        ∃ y ∈ (Dictionary.dom s).erase w, ∃ vy : ℕ,
          T (π w i) = some (y, vy) ∧ rank y < rank w)
    (u : Fin U) {L : ℕ} (hL : 1 ≤ L) :
    (missedProbes (otherOccupiedSlots T u) (π u) < L ∧
      (partialDepSet T π (extRank s rank u) u
        (missedProbes (otherOccupiedSlots T u) (π u))).card < L) ∨
      ∃ x₀ ∈ insert u (Dictionary.dom s),
        extRank s rank u x₀ ≤ extRank s rank u u ∧
        ∃ r₀ : ℕ, 1 ≤ r₀ ∧ r₀ ≤ min (missedProbes (otherOccupiedSlots T x₀) (π x₀)) L ∧
          L ≤ (partialDepSet T π (extRank s rank u) x₀ r₀).card ∧
          (partialDepSet T π (extRank s rank u) x₀ r₀).card < 2 * L := by
  classical
  have key : ∀ y ∈ insert u (Dictionary.dom s),
      (partialDepSet T π (extRank s rank u) y
        (min (missedProbes (otherOccupiedSlots T y) (π y)) L)).card < L →
      missedProbes (otherOccupiedSlots T y) (π y) < L ∧
        (partialDepSet T π (extRank s rank u) y
          (missedProbes (otherOccupiedSlots T y) (π y))).card < L := fun y hy hlt => by
    have hge := card_partialDepSet_ge hrep hrank u hy
      (Nat.min_le_left (missedProbes (otherOccupiedSlots T y) (π y)) L)
    have hlt' : missedProbes (otherOccupiedSlots T y) (π y) < L := by omega
    exact ⟨hlt', by rwa [Nat.min_eq_left hlt'.le] at hlt⟩
  by_cases hnorm :
      (partialDepSet T π (extRank s rank u) u
        (min (missedProbes (otherOccupiedSlots T u) (π u)) L)).card < L
  · exact .inl (key u (Finset.mem_insert_self u _) hnorm)
  · right
    let B := (insert u (Dictionary.dom s)).filter fun x =>
      extRank s rank u x ≤ extRank s rank u u ∧
        L ≤ (partialDepSet T π (extRank s rank u) x
          (min (missedProbes (otherOccupiedSlots T x) (π x)) L)).card
    obtain ⟨x₀, hx₀B, hmin_x₀⟩ := B.exists_min_image (extRank s rank u)
      ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_insert_self u _, le_rfl, not_lt.mp hnorm⟩⟩
    obtain ⟨hx₀_ins, hx₀_le_u, hx₀_ge_L⟩ := Finset.mem_filter.mp hx₀B
    have hex_r : ∃ r ≤ min (missedProbes (otherOccupiedSlots T x₀) (π x₀)) L,
        L ≤ (partialDepSet T π (extRank s rank u) x₀ r).card := ⟨_, le_rfl, hx₀_ge_L⟩
    obtain ⟨hr₀_le, hr₀_ge⟩ := Nat.find_spec hex_r
    have hr₀_pos : 1 ≤ Nat.find hex_r :=
      (Nat.find_pos hex_r).mpr (by simp [partialDepSet_zero]; omega)
    have hr₀_prev_lt :
        (partialDepSet T π (extRank s rank u) x₀ (Nat.find hex_r - 1)).card < L :=
      not_le.mp fun hge_prev =>
        Nat.find_min hex_r (m := Nat.find hex_r - 1) (by omega) ⟨by omega, hge_prev⟩
    obtain ⟨z, hz_erase, hlt_z, hsub_step⟩ := partialDepSet_succ_subset_union hrep hrank u
      hx₀_ins (r := Nat.find hex_r - 1) (by omega)
    rw [Nat.sub_add_cancel hr₀_pos] at hsub_step
    have hz_ins := Finset.mem_insert_of_mem (b := u) (Finset.mem_of_mem_erase hz_erase)
    have hz_lt := (key z hz_ins <| not_le.mp fun hge_z => (hmin_x₀ z (Finset.mem_filter.mpr
      ⟨hz_ins, (hlt_z.trans_le hx₀_le_u).le, hge_z⟩)).not_gt hlt_z).2
    have hdep_z := card_depSet_eq T π (extRank s rank u) z
    have hle_union := (Finset.card_le_card hsub_step).trans (Finset.card_union_le _ _)
    exact ⟨x₀, hx₀_ins, hx₀_le_u, _, hr₀_pos, hr₀_le, hr₀_ge, by omega⟩

/-! ## Section 4: BFS Spanning-Tree Witness and `(2 * L + 1)`-Wise Independent Probe Bound -/

/-- Slot at step `i : ℕ` along `σ : Equiv.Perm (Fin m)` when `0 < m`. -/
private def probeAt {m : ℕ} (hm : 0 < m) (σ : Equiv.Perm (Fin m)) (i : ℕ) : Fin m :=
  σ ⟨i % m, Nat.mod_lt i hm⟩

/-- First `l` slots probed along `σ : Equiv.Perm (Fin m)` when `0 < m`. -/
private def probePrefix {m : ℕ} (hm : 0 < m) (σ : Equiv.Perm (Fin m)) (l : ℕ) : List (Fin m) :=
  (List.range l).map (probeAt hm σ)

private theorem probeAt_eq_of_lt {m : ℕ} (hm : 0 < m) (σ : Equiv.Perm (Fin m)) {i : ℕ}
    (hi : i < m) : probeAt hm σ i = σ ⟨i, hi⟩ := by
  simp [probeAt, Nat.mod_eq_of_lt hi]

private theorem length_probePrefix {m : ℕ} (hm : 0 < m) (σ : Equiv.Perm (Fin m)) (l : ℕ) :
    (probePrefix hm σ l).length = l := by
  simp [probePrefix]

private theorem nodup_probePrefix {m : ℕ} (hm : 0 < m) (σ : Equiv.Perm (Fin m)) {l : ℕ}
    (hl : l ≤ m) : (probePrefix hm σ l).Nodup := by
  refine List.nodup_range.map_on fun i hi j hj heq => ?_
  rw [List.mem_range] at hi hj
  rw [probeAt_eq_of_lt hm σ (hi.trans_le hl), probeAt_eq_of_lt hm σ (hj.trans_le hl)] at heq
  exact Fin.mk.inj (σ.injective heq)

private theorem take_probePrefix {m : ℕ} (hm : 0 < m) (σ : Equiv.Perm (Fin m)) {k w : ℕ}
    (hkw : k ≤ w) : (probePrefix hm σ w).take k = probePrefix hm σ k := by
  rw [probePrefix, probePrefix, ← List.map_take, List.take_range, Nat.min_eq_left hkw]

/-- Landing-index-free filter identity: if `k ≤ w` and `((probePrefix hm σ k).filter p).length = d`,
then taking the first `d` elements of `(probePrefix hm σ w).filter p` recovers
`(probePrefix hm σ k).filter p` without knowing `k`. -/
private theorem take_filter_probePrefix_eq {m : ℕ} (hm : 0 < m) (σ : Equiv.Perm (Fin m))
    {k w d : ℕ} (hkw : k ≤ w) (p : Fin m → Bool)
    (hd : ((probePrefix hm σ k).filter p).length = d) :
    ((probePrefix hm σ w).filter p).take d = (probePrefix hm σ k).filter p := by
  have hsplit := List.take_append_drop k (probePrefix hm σ w)
  rw [take_probePrefix hm σ hkw] at hsplit
  rw [← hsplit, List.filter_append, ← hd, List.take_left]

/-- Cumulative BFS slot queue parameterized only by `(x₀, w, h, x)` and the first `w` probes of
each vertex. -/
private def bfsQueue {U m : ℕ} (hm : 0 < m) (π : Fin U → Equiv.Perm (Fin m))
    (x₀ : Fin U) (w : ℕ) (h : Fin (w + 1) → ℕ) (x : Fin w → Fin U) : ℕ → List (Fin m)
  | 0 => probePrefix hm (π x₀) (h 0)
  | b + 1 =>
    let q := bfsQueue hm π x₀ w h x b
    if hb : b < w then
      q ++ ((probePrefix hm (π (x ⟨b, hb⟩)) w).filter (· ∉ q)).take
        (h ⟨b + 1, Nat.succ_lt_succ hb⟩)
    else q

private theorem sum_fin_succ_eq {w : ℕ} (h : Fin (w + 1) → ℕ) :
    h 0 + (∑ i ∈ Finset.range w, if hi : i < w then h ⟨i + 1, Nat.succ_lt_succ hi⟩ else 0) =
      ∑ a : Fin (w + 1), h a := by
  rw [Fin.sum_univ_succ, Finset.sum_range]
  simp [Fin.succ]

/-- Local BFS step event at vertex `x b` (`b : Fin w`) given `q = bfsQueue hm π x₀ w h x b.val`
and `slot_b = q.getD b.val ⟨0, hm⟩`. -/
private def bfsStepEvent {U m : ℕ} (hm : 0 < m) (π : Fin U → Equiv.Perm (Fin m))
    (x₀ : Fin U) (w : ℕ) (h : Fin (w + 1) → ℕ) (x : Fin w → Fin U) (b : Fin w) : Prop :=
  let q := bfsQueue hm π x₀ w h x b.val
  let slot_b := q.getD b.val ⟨0, hm⟩
  let σ := π (x b)
  probeAt hm σ (h ⟨b.val + 1, Nat.succ_lt_succ b.isLt⟩) = slot_b ∨
    ∃ k_b : Fin w, ∃ j₁ : Fin w,
      j₁.val < k_b.val ∧
      probeAt hm σ j₁.val ∈ q.toFinset ∧
      probeAt hm σ k_b.val = slot_b

private instance instDecidableBfsStepEvent {U m : ℕ} (hm : 0 < m)
    (π : Fin U → Equiv.Perm (Fin m)) (x₀ : Fin U) (w : ℕ) (h : Fin (w + 1) → ℕ)
    (x : Fin w → Fin U) (b : Fin w) :
    Decidable (bfsStepEvent hm π x₀ w h x b) := by
  unfold bfsStepEvent
  infer_instance

/-- Existence of a size-`w` BFS dependency witness rooted at `x₀` over stored keys `D`
([SchmidtSiegel1990], Appendix A, Lemma A). -/
private def HasBFSWitness {U m : ℕ} (hm : 0 < m) (π : Fin U → Equiv.Perm (Fin m))
    (D : Finset (Fin U)) (x₀ : Fin U) (w : ℕ) : Prop :=
  ∃ h : Fin (w + 1) → ℕ,
    1 ≤ h 0 ∧
    (∑ a : Fin (w + 1), h a = w) ∧
    ∃ x : Fin w → Fin U,
      Function.Injective x ∧
      (∀ b : Fin w, x b ∈ D.erase x₀) ∧
      ∀ b : Fin w, bfsStepEvent hm π x₀ w h x b

/-- Landing slot `probeAt hm (π y) (missedProbes (otherOccupiedSlots T y) (π y))` of key `y`. -/
private def landingSlot {U m : ℕ} (hm : 0 < m) (T : Table U m)
    (π : Fin U → Equiv.Perm (Fin m)) (y : Fin U) : Fin m :=
  probeAt hm (π y) (missedProbes (otherOccupiedSlots T y) (π y))

/-- Key stored at slot `j` in `T`, defaulting to `u₀` if `T j = none`. -/
private def keyAt {U m : ℕ} (T : Table U m) (u₀ : Fin U) (j : Fin m) : Fin U :=
  match T j with
  | some (y, _) => y
  | none => u₀

private theorem apply_landingSlot_of_mem_dom {U m : ℕ} (hm : 0 < m)
    {π : Fin U → Equiv.Perm (Fin m)} {s : Dictionary.State U} {T : Table U m}
    (hrep : TableRep π s T) {y : Fin U} (hy : y ∈ Dictionary.dom s) :
    ∃ vy, T (landingSlot hm T π y) = some (y, vy) := by
  obtain ⟨vy, hsy⟩ := Dictionary.mem_dom_iff.mp hy
  obtain ⟨hlt, hTy⟩ := hrep.key_spec y vy hsy
  exact ⟨vy, by rwa [landingSlot, probeAt_eq_of_lt hm (π y) hlt]⟩

private theorem keyAt_landingSlot_of_mem_dom {U m : ℕ} (hm : 0 < m)
    {π : Fin U → Equiv.Perm (Fin m)} {s : Dictionary.State U} {T : Table U m}
    (hrep : TableRep π s T) (u₀ : Fin U) {y : Fin U} (hy : y ∈ Dictionary.dom s) :
    keyAt T u₀ (landingSlot hm T π y) = y := by
  obtain ⟨vy, hTy⟩ := apply_landingSlot_of_mem_dom hm hrep hy
  simp [keyAt, hTy]

private theorem landingSlot_injOn_dom {U m : ℕ} (hm : 0 < m)
    {π : Fin U → Equiv.Perm (Fin m)} {s : Dictionary.State U} {T : Table U m}
    (hrep : TableRep π s T) :
    Set.InjOn (landingSlot hm T π) (Dictionary.dom s : Set (Fin U)) := fun y₁ hy₁ y₂ hy₂ heq => by
  rw [← keyAt_landingSlot_of_mem_dom hm hrep y₁ hy₁, heq]
  exact keyAt_landingSlot_of_mem_dom hm hrep y₁ hy₂

private theorem toFinset_probePrefix_eq_image_directBlockers {U m : ℕ} (hm : 0 < m)
    {π : Fin U → Equiv.Perm (Fin m)} {s : Dictionary.State U} {T : Table U m}
    (hrep : TableRep π s T) {rank : Fin U → ℕ}
    (hrank : ∀ w ∈ Dictionary.dom s, ∀ i : Fin m,
      i.val < missedProbes (otherOccupiedSlots T w) (π w) →
        ∃ y ∈ (Dictionary.dom s).erase w, ∃ vy : ℕ,
          T (π w i) = some (y, vy) ∧ rank y < rank w)
    (u : Fin U) {z : Fin U} (hz : z ∈ insert u (Dictionary.dom s)) {r : ℕ}
    (hr : r ≤ missedProbes (otherOccupiedSlots T z) (π z)) :
    (probePrefix hm (π z) r).toFinset =
      (directBlockers T π (extRank s rank u) z r).image (landingSlot hm T π) := by
  ext j
  simp only [List.mem_toFinset, probePrefix, List.mem_map, List.mem_range, Finset.mem_image,
    directBlockers, Finset.mem_filter, Finset.mem_univ, true_and]
  have hrm : r ≤ m := hr.trans (missedProbes_le _ _)
  have hland : ∀ {i : Fin m} {y vy}, T (π z i) = some (y, vy) →
      landingSlot hm T π y = probeAt hm (π z) i.val := fun {i y vy} hT => by
    obtain ⟨_, hlt, hslot⟩ := hrep.slot_spec _ y vy hT
    rw [landingSlot, probeAt_eq_of_lt hm (π y) hlt, probeAt_eq_of_lt hm (π z) i.isLt, hslot]
  constructor
  · rintro ⟨i, hi_r, rfl⟩
    obtain ⟨y, _, vy, hTy, hlt_y⟩ :=
      extRank_blocker_spec hrep hrank u hz (i := ⟨i, hi_r.trans_le hrm⟩) (hi_r.trans_le hr)
    exact ⟨y, ⟨hlt_y, ⟨i, hi_r.trans_le hrm⟩, hi_r, hi_r.trans_le hr, by simp [hTy]⟩, hland hTy⟩
  · rintro ⟨y, ⟨_, i, hi_r, _, hTy⟩, rfl⟩
    obtain ⟨vy, hTi⟩ := exists_val_of_map_fst_eq_some hTy
    exact ⟨i.val, hi_r, (hland hTi).symm⟩

/-- Raw BFS slot queue constructed directly from `(T, π, x₀, r₀)`. -/
private def rawQueue {U m : ℕ} (hm : 0 < m) (T : Table U m) (π : Fin U → Equiv.Perm (Fin m))
    (x₀ : Fin U) (r₀ : ℕ) : ℕ → List (Fin m)
  | 0 => probePrefix hm (π x₀) r₀
  | b + 1 =>
    let q := rawQueue hm T π x₀ r₀ b
    let slot_b := q.getD b ⟨0, hm⟩
    let x_b := keyAt T x₀ slot_b
    let k_b := missedProbes (otherOccupiedSlots T x_b) (π x_b)
    q ++ (probePrefix hm (π x_b) k_b).filter (· ∉ q)

private theorem nodup_rawQueue {U m : ℕ} (hm : 0 < m) (T : Table U m)
    (π : Fin U → Equiv.Perm (Fin m)) (x₀ : Fin U) {r₀ : ℕ} (hr₀ : r₀ ≤ m) :
    ∀ b : ℕ, (rawQueue hm T π x₀ r₀ b).Nodup
  | 0 => nodup_probePrefix hm (π x₀) hr₀
  | b + 1 => List.nodup_append.mpr ⟨nodup_rawQueue hm T π x₀ hr₀ b,
      (nodup_probePrefix hm _ (missedProbes_le _ _)).filter _,
      fun j₁ hj₁ j₂ hj₂ heq => by simpa [heq ▸ hj₁] using (List.mem_filter.mp hj₂).2⟩

private theorem rawQueue_prefix {U m : ℕ} (hm : 0 < m) (T : Table U m)
    (π : Fin U → Equiv.Perm (Fin m)) (x₀ : Fin U) (r₀ : ℕ) {a b : ℕ} (hab : a ≤ b) :
    rawQueue hm T π x₀ r₀ a <+: rawQueue hm T π x₀ r₀ b := by
  induction hab with
  | refl => exact List.prefix_rfl
  | step _ ih => exact ih.trans (List.prefix_append _ _)

private theorem getD_rawQueue_eq_of_le {U m : ℕ} (hm : 0 < m) (T : Table U m)
    (π : Fin U → Equiv.Perm (Fin m)) (x₀ : Fin U) (r₀ : ℕ) {a b i : ℕ}
    (hab : a ≤ b) (hi : i < (rawQueue hm T π x₀ r₀ a).length) :
    (rawQueue hm T π x₀ r₀ b).getD i ⟨0, hm⟩ =
      (rawQueue hm T π x₀ r₀ a).getD i ⟨0, hm⟩ := by
  obtain ⟨t, ht⟩ := rawQueue_prefix hm T π x₀ r₀ hab
  rw [← ht, List.getD_append _ _ _ _ hi]

private theorem mem_rawQueue_succ_of_mem_probePrefix {U m : ℕ} (hm : 0 < m) (T : Table U m)
    (π : Fin U → Equiv.Perm (Fin m)) (x₀ : Fin U) (r₀ a : ℕ) {j : Fin m}
    (hj : j ∈ probePrefix hm
      (π (keyAt T x₀ ((rawQueue hm T π x₀ r₀ a).getD a ⟨0, hm⟩)))
      (missedProbes (otherOccupiedSlots T
        (keyAt T x₀ ((rawQueue hm T π x₀ r₀ a).getD a ⟨0, hm⟩)))
        (π (keyAt T x₀ ((rawQueue hm T π x₀ r₀ a).getD a ⟨0, hm⟩))))) :
    j ∈ rawQueue hm T π x₀ r₀ (a + 1) :=
  List.mem_append.mpr ((em (j ∈ rawQueue hm T π x₀ r₀ a)).imp_right fun h =>
    List.mem_filter.mpr ⟨hj, by simpa using h⟩)

private theorem keyAt_getD_mem_of_toFinset_subset {U m : ℕ} (hm : 0 < m)
    {π : Fin U → Equiv.Perm (Fin m)} {s : Dictionary.State U} {T : Table U m}
    (hrep : TableRep π s T) (x₀ : Fin U) {W : Finset (Fin U)} (hW : W ⊆ Dictionary.dom s)
    {q : List (Fin m)} (hq : q.toFinset ⊆ W.image (landingSlot hm T π))
    {i : ℕ} (hi : i < q.length) :
    keyAt T x₀ (q.getD i ⟨0, hm⟩) ∈ W ∧
      landingSlot hm T π (keyAt T x₀ (q.getD i ⟨0, hm⟩)) = q.getD i ⟨0, hm⟩ := by
  rw [List.getD_eq_getElem q ⟨0, hm⟩ hi]
  obtain ⟨y, hyW, hland⟩ :=
    Finset.mem_image.mp (hq (List.mem_toFinset.mpr (List.getElem_mem hi)))
  rw [← hland, keyAt_landingSlot_of_mem_dom hm hrep x₀ (hW hyW)]
  exact ⟨hyW, rfl⟩

private theorem rawQueue_spec {U m : ℕ} (hm : 0 < m)
    {π : Fin U → Equiv.Perm (Fin m)} {s : Dictionary.State U} {T : Table U m}
    (hrep : TableRep π s T) {rank : Fin U → ℕ}
    (hrank : ∀ w ∈ Dictionary.dom s, ∀ i : Fin m,
      i.val < missedProbes (otherOccupiedSlots T w) (π w) →
        ∃ y ∈ (Dictionary.dom s).erase w, ∃ vy : ℕ,
          T (π w i) = some (y, vy) ∧ rank y < rank w)
    (u : Fin U) {x₀ : Fin U} (hx₀ : x₀ ∈ insert u (Dictionary.dom s))
    {r₀ : ℕ} (hr₀_pos : 1 ≤ r₀) (hr₀_mp : r₀ ≤ missedProbes (otherOccupiedSlots T x₀) (π x₀)) :
    ∀ b ≤ (partialDepSet T π (extRank s rank u) x₀ r₀).card,
      (rawQueue hm T π x₀ r₀ b).toFinset ⊆
        (partialDepSet T π (extRank s rank u) x₀ r₀).image (landingSlot hm T π) ∧
      min (b + 1) (partialDepSet T π (extRank s rank u) x₀ r₀).card ≤
        (rawQueue hm T π x₀ r₀ b).length := by
  classical
  set r_ext := extRank s rank u
  set W := partialDepSet T π r_ext x₀ r₀
  have hW_dom : W ⊆ Dictionary.dom s := fun z hz =>
    mem_dom_of_mem_partialDepSet hrep r_ext x₀ r₀ hz
  have hpref : ∀ z ∈ W, ∀ j,
      j ∈ probePrefix hm (π z) (missedProbes (otherOccupiedSlots T z) (π z)) ↔
        ∃ y ∈ directBlockers T π r_ext z m, landingSlot hm T π y = j := fun z hz j => by
    rw [← List.mem_toFinset, toFinset_probePrefix_eq_image_directBlockers hm hrep hrank u
      (Finset.mem_insert_of_mem (hW_dom hz)) le_rfl,
      directBlockers_eq_of_missedProbes_le T π r_ext z le_rfl, Finset.mem_image]
  have hdirW : ∀ z ∈ W, directBlockers T π r_ext z m ⊆ W := fun z hz y hy =>
    (rank_lt_and_depSet_subset_of_mem_partialDepSet T π r_ext x₀ r₀ hz).2
      (mem_depSet_of_mem_directBlockers T π r_ext hy)
  have h0 : (rawQueue hm T π x₀ r₀ 0).toFinset =
      (directBlockers T π r_ext x₀ r₀).image (landingSlot hm T π) :=
    toFinset_probePrefix_eq_image_directBlockers hm hrep hrank u hx₀ hr₀_mp
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hbw
    cases b with
    | zero =>
      exact ⟨h0 ▸ Finset.image_subset_image fun y hy =>
        mem_partialDepSet_of_mem_directBlockers T π r_ext hy,
        by simp only [rawQueue, length_probePrefix]; omega⟩
    | succ c =>
      obtain ⟨hsub_c, hlen_c⟩ := ih c (Nat.lt_succ_self c) (by omega)
      obtain ⟨hxc_W, -⟩ :=
        keyAt_getD_mem_of_toFinset_subset hm hrep x₀ hW_dom hsub_c (i := c) (by omega)
      refine ⟨fun j hj => ?_, ?_⟩
      · simp only [rawQueue, List.toFinset_append, Finset.mem_union, List.mem_toFinset,
          List.mem_filter] at hj
        refine hj.elim (fun hj_c => hsub_c (List.mem_toFinset.mpr hj_c)) fun ⟨hj_new, _⟩ => ?_
        obtain ⟨y, hy_dir, rfl⟩ := (hpref _ hxc_W j).mp hj_new
        exact Finset.mem_image_of_mem _ (hdirW _ hxc_W hy_dir)
      -- Otherwise every enqueued slot has been expanded, so the keys landing in the queue are
      -- closed under direct blockers and contain all of `W`, which is larger than the queue.
      by_contra hlt_succ
      have hlen_le_succ := (rawQueue_prefix hm T π x₀ r₀ (Nat.le_succ c)).length_le
      set q' := rawQueue hm T π x₀ r₀ (c + 1)
      let C := W.filter fun y => landingSlot hm T π y ∈ q'
      have hdir0_C : directBlockers T π r_ext x₀ r₀ ⊆ C := fun y hy =>
        Finset.mem_filter.mpr ⟨mem_partialDepSet_of_mem_directBlockers T π r_ext hy,
          (rawQueue_prefix hm T π x₀ r₀ (Nat.zero_le (c + 1))).subset
            (List.mem_toFinset.mp (h0 ▸ Finset.mem_image_of_mem _ hy))⟩
      have hclosed_C : ∀ z ∈ C, directBlockers T π r_ext z m ⊆ C := by
        intro z hz y hy_dir
        obtain ⟨hzW, hz_land⟩ := Finset.mem_filter.mp hz
        obtain ⟨a, ha_lt, hqa⟩ := List.mem_iff_getElem.mp hz_land
        obtain ⟨-, hlen_a⟩ := ih a (by omega) (by omega)
        have hkey_a : keyAt T x₀ ((rawQueue hm T π x₀ r₀ a).getD a ⟨0, hm⟩) = z := by
          rw [← getD_rawQueue_eq_of_le hm T π x₀ r₀ (b := c + 1) (by omega) (by omega),
            List.getD_eq_getElem q' ⟨0, hm⟩ ha_lt, hqa,
            keyAt_landingSlot_of_mem_dom hm hrep x₀ (hW_dom hzW)]
        exact Finset.mem_filter.mpr ⟨hdirW z hzW hy_dir,
          (rawQueue_prefix hm T π x₀ r₀ (b := c + 1) (by omega)).subset
            (mem_rawQueue_succ_of_mem_probePrefix hm T π x₀ r₀ a
              (hkey_a ▸ (hpref z hzW _).mpr ⟨y, hy_dir, rfl⟩))⟩
      have hW_sub_C : W ⊆ C := Finset.biUnion_subset.mpr fun y hy_dir =>
        depSet_subset_of_directBlockers_closed T π r_ext hclosed_C (hdir0_C hy_dir)
      have hcard := (Finset.card_le_card_of_injOn (landingSlot hm T π)
        (fun y hy => List.mem_toFinset.mpr (Finset.mem_filter.mp (hW_sub_C hy)).2)
        ((landingSlot_injOn_dom hm hrep).mono hW_dom)).trans (List.toFinset_card_le q')
      omega

/-- **BFS Spanning-Tree Witness Extraction ([SchmidtSiegel1990], Appendix A, Lemma A)**:
any partial dependency set `W = partialDepSet T π (extRank s rank u) x₀ r₀` with
`1 ≤ r₀ ≤ missedProbes (otherOccupiedSlots T x₀) (π x₀)` yields a size-`W.card` BFS witness
`HasBFSWitness hm π ((Dictionary.dom s).erase u) x₀ W.card`. -/
private theorem hasBFSWitness_of_partialDepSet {U m : ℕ} (hm : 0 < m)
    {π : Fin U → Equiv.Perm (Fin m)} {s : Dictionary.State U} {T : Table U m}
    (hrep : TableRep π s T) {rank : Fin U → ℕ}
    (hrank : ∀ w ∈ Dictionary.dom s, ∀ i : Fin m,
      i.val < missedProbes (otherOccupiedSlots T w) (π w) →
        ∃ y ∈ (Dictionary.dom s).erase w, ∃ vy : ℕ,
          T (π w i) = some (y, vy) ∧ rank y < rank w)
    (u : Fin U) {x₀ : Fin U} (hx₀ : x₀ ∈ insert u (Dictionary.dom s))
    (hx₀_le : extRank s rank u x₀ ≤ extRank s rank u u)
    {r₀ : ℕ} (hr₀_pos : 1 ≤ r₀) (hr₀_mp : r₀ ≤ missedProbes (otherOccupiedSlots T x₀) (π x₀)) :
    HasBFSWitness hm π ((Dictionary.dom s).erase u) x₀
      (partialDepSet T π (extRank s rank u) x₀ r₀).card := by
  classical
  have hspec := rawQueue_spec hm hrep hrank u hx₀ hr₀_pos hr₀_mp
  set r_ext := extRank s rank u
  set W := partialDepSet T π r_ext x₀ r₀
  set w := W.card
  have hW_dom : W ⊆ Dictionary.dom s := fun z hz =>
    mem_dom_of_mem_partialDepSet hrep r_ext x₀ r₀ hz
  let x : Fin w → Fin U := fun b =>
    keyAt T x₀ ((rawQueue hm T π x₀ r₀ b.val).getD b.val ⟨0, hm⟩)
  let h : Fin (w + 1) → ℕ := Fin.cases r₀ fun b : Fin w =>
    ((probePrefix hm (π (x b))
      (missedProbes (otherOccupiedSlots T (x b)) (π (x b)))).filter
        (· ∉ rawQueue hm T π x₀ r₀ b.val)).length
  have hlen_lt (b : Fin w) : b.val < (rawQueue hm T π x₀ r₀ b.val).length := by
    have := (hspec b.val b.isLt.le).2; have := b.isLt; omega
  have hxb_spec : ∀ b : Fin w, x b ∈ W ∧
      landingSlot hm T π (x b) = (rawQueue hm T π x₀ r₀ b.val).getD b.val ⟨0, hm⟩ := fun b =>
    keyAt_getD_mem_of_toFinset_subset hm hrep x₀ hW_dom (hspec b.val b.isLt.le).1 (hlen_lt b)
  have hk_lt : ∀ b : Fin w, missedProbes (otherOccupiedSlots T (x b)) (π (x b)) < w := fun b =>
    missedProbes_lt_card_of_mem_partialDepSet hrep hrank u x₀ r₀ (hxb_spec b).1
  have hqueue_eq : ∀ b ≤ w,
      bfsQueue hm π x₀ w h x b = rawQueue hm T π x₀ r₀ b ∧
      (rawQueue hm T π x₀ r₀ b).length =
        h 0 + ∑ i ∈ Finset.range b,
          if hi : i < w then h ⟨i + 1, Nat.succ_lt_succ hi⟩ else 0 := by
    intro b hbw
    induction b with
    | zero => simp [bfsQueue, rawQueue, h, length_probePrefix]
    | succ b ih =>
      have hb_lt : b < w := hbw
      obtain ⟨ih_q, ih_len⟩ := ih hb_lt.le
      have htake := take_filter_probePrefix_eq hm (π (x ⟨b, hb_lt⟩)) (hk_lt ⟨b, hb_lt⟩).le
        (· ∉ rawQueue hm T π x₀ r₀ b) (d := h ⟨b + 1, Nat.succ_lt_succ hb_lt⟩) rfl
      refine ⟨by simp only [bfsQueue, hb_lt, ↓reduceDIte, ih_q, htake]; rfl, ?_⟩
      rw [Finset.sum_range_succ, dite_eq_left hb_lt, ← Nat.add_assoc, ← ih_len]
      exact List.length_append
  have hnodup_w := nodup_rawQueue hm T π x₀ (hr₀_mp.trans (missedProbes_le _ _)) w
  have hlen_w : (rawQueue hm T π x₀ r₀ w).length = w := by
    obtain ⟨hsub_w, hlen_w_ge⟩ := hspec w le_rfl
    have := (Finset.card_le_card hsub_w).trans_eq
      (Finset.card_image_of_injOn ((landingSlot_injOn_dom hm hrep).mono hW_dom))
    rw [List.toFinset_card_of_nodup hnodup_w] at this
    omega
  refine ⟨h, hr₀_pos, by rw [← sum_fin_succ_eq h, ← (hqueue_eq w le_rfl).2, hlen_w], x, ?_,
    fun b => partialDepSet_subset_erase hrep hx₀_le r₀ (hxb_spec b).1, fun b => ?_⟩
  · intro b₁ b₂ heq
    have hland : landingSlot hm T π (x b₁) = landingSlot hm T π (x b₂) := congrArg _ heq
    rw [(hxb_spec b₁).2, (hxb_spec b₂).2,
      ← getD_rawQueue_eq_of_le hm T π x₀ r₀ b₁.isLt.le (hlen_lt b₁),
      ← getD_rawQueue_eq_of_le hm T π x₀ r₀ b₂.isLt.le (hlen_lt b₂),
      List.getD_eq_getElem _ _ (hlen_w.symm ▸ b₁.isLt),
      List.getD_eq_getElem _ _ (hlen_w.symm ▸ b₂.isLt)] at hland
    exact Fin.ext (hnodup_w.getElem_inj_iff.mp hland)
  · dsimp only [bfsStepEvent]
    rw [(hqueue_eq b.val b.isLt.le).1]
    set q := rawQueue hm T π x₀ r₀ b.val
    set k_b := missedProbes (otherOccupiedSlots T (x b)) (π (x b))
    have hslot_eq : probeAt hm (π (x b)) k_b = q.getD b.val ⟨0, hm⟩ := (hxb_spec b).2
    have hhb_le : h ⟨b.val + 1, Nat.succ_lt_succ b.isLt⟩ ≤ k_b :=
      (List.length_filter_le _ _).trans (length_probePrefix hm _ _).le
    rcases eq_or_lt_of_le hhb_le with hhb_eq_kb | hhb_lt_kb
    · exact .inl (by rw [hhb_eq_kb, hslot_eq])
    · rw [← length_probePrefix hm (π (x b)) k_b] at hhb_lt_kb
      obtain ⟨j, hj_pref, hj_q⟩ := List.length_filter_lt_length_iff_exists.mp hhb_lt_kb
      obtain ⟨j₁, hj₁_lt, rfl⟩ := List.mem_map.mp hj_pref
      rw [List.mem_range] at hj₁_lt
      exact .inr ⟨⟨k_b, hk_lt b⟩, ⟨j₁, hj₁_lt.trans (hk_lt b)⟩, hj₁_lt,
        List.mem_toFinset.mpr (by simpa using hj_q), hslot_eq⟩

open scoped Classical in
/-- **Pointwise Probe-Count Decomposition via Minimal Overflow Dichotomy and BFS Witnesses**:
for any `OrderedTableRep π s T` with `(Dictionary.dom s).card ≤ n_max`, query key `u : Fin U`,
and cutoff `L ≥ 1`, `probeCount T u (π u)` is bounded by `1` plus the normal-regime witness sum
over `w ∈ [1, L)` plus `n_max` times the overflow-regime witness sum over
`x₀ ∈ insert u (Dictionary.dom s)` and `w ∈ [L, 2 * L)`. -/
private theorem probeCount_le_sum_hasBFSWitness {U m n_max : ℕ} (hm : 0 < m)
    {π : Fin U → Equiv.Perm (Fin m)} {s : Dictionary.State U} {T : Table U m}
    (hrep : OrderedTableRep π s T) (hdom : (Dictionary.dom s).card ≤ n_max)
    (u : Fin U) {L : ℕ} (hL : 1 ≤ L) :
    probeCount T u (π u) ≤
      1 +
      (∑ w ∈ Finset.Ico 1 L,
        if HasBFSWitness hm π ((Dictionary.dom s).erase u) u w then w else 0) +
      n_max *
        (∑ x₀ ∈ insert u (Dictionary.dom s),
          ∑ w ∈ Finset.Ico L (2 * L),
            if HasBFSWitness hm π ((Dictionary.dom s).erase u) x₀ w then 1 else 0) := by
  have hpc_eq : probeCount T u (π u) = 1 + missedProbes (otherOccupiedSlots T u) (π u) := rfl
  rcases Nat.eq_zero_or_pos (missedProbes (otherOccupiedSlots T u) (π u)) with hk0 | hk_pos
  · omega
  · obtain ⟨rank, hrank⟩ := hrep.exists_rank
    rcases dichotomy_partialDepSet hrep.toTableRep hrank u hL with
      ⟨hku_lt, hcard_lt⟩ | ⟨x₀, hx₀_ins, hx₀_le, r₀, hr₀_pos, hr₀_le_min, hw_ge_L, hw_lt_2L⟩
    · have hku_le_w := card_partialDepSet_ge hrep.toTableRep hrank u
        (Finset.mem_insert_self u _) le_rfl
      have hle_sum := Finset.single_le_sum (s := Finset.Ico 1 L)
        (f := fun w' => if HasBFSWitness hm π ((Dictionary.dom s).erase u) u w' then w' else 0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_Ico.mpr ⟨by omega, hcard_lt⟩)
      rw [ite_eq_left (hasBFSWitness_of_partialDepSet hm hrep.toTableRep hrank u
        (Finset.mem_insert_self u _) le_rfl hk_pos le_rfl)] at hle_sum
      omega
    · have hle_inner := Finset.single_le_sum
        (f := fun w' => if HasBFSWitness hm π ((Dictionary.dom s).erase u) x₀ w' then 1 else 0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_Ico.mpr ⟨hw_ge_L, hw_lt_2L⟩)
      rw [ite_eq_left (hasBFSWitness_of_partialDepSet hm hrep.toTableRep hrank u hx₀_ins hx₀_le
        hr₀_pos (hr₀_le_min.trans (Nat.min_le_left _ _)))] at hle_inner
      have hmul := Nat.mul_le_mul_left n_max (hle_inner.trans (Finset.single_le_sum
        (f := fun x₀' => ∑ w' ∈ Finset.Ico L (2 * L),
          if HasBFSWitness hm π ((Dictionary.dom s).erase u) x₀' w' then 1 else 0)
        (fun _ _ => Nat.zero_le _) hx₀_ins))
      have hpc_le := probeCount_le_add_one hrep.toTableRep hdom u
      omega

/-- Single-step fiber of hash pairs `(p, s) ∈ Fin (2 ^ M) × Fin (2 ^ (M - 1))` satisfying the
BFS step constraint at `slot_b` with degree `d` against queue `q`. -/
private noncomputable def stepFiber (M w : ℕ) (q : List (Fin (2 ^ M)))
    (slot_b : Fin (2 ^ M)) (d : ℕ) :
    Finset (Fin (2 ^ M) × Fin (2 ^ (M - 1))) :=
  Finset.univ.filter fun ps =>
    let σ := oddStridePermOfPair M ps.1 ps.2
    let hm := Nat.two_pow_pos M
    probeAt hm σ d = slot_b ∨
      ∃ k_b : Fin w, ∃ j₁ : Fin w,
        j₁.val < k_b.val ∧
        probeAt hm σ j₁.val ∈ q.toFinset ∧
        probeAt hm σ k_b.val = slot_b

private theorem probeAt_oddStridePermOfPair_injective (M : ℕ) (s : Fin (2 ^ (M - 1)))
    (idx : ℕ) : Function.Injective fun p : Fin (2 ^ M) =>
      probeAt (Nat.two_pow_pos M) (oddStridePermOfPair M p s) idx := by
  intro p₁ p₂ h
  simp only [probeAt, oddStridePermOfPair_apply, oddStrideSeq, Fin.ext_iff] at h
  exact Fin.ext ((Nat.ModEq.add_right_cancel' _ h).eq_of_lt_of_lt p₁.isLt p₂.isLt)

private theorem card_filter_prod_probeAt_le (M : ℕ)
    {F : Finset (Fin (2 ^ M) × Fin (2 ^ (M - 1)))} {S : Finset (Fin (2 ^ (M - 1)))}
    (d : ℕ) (slot : Fin (2 ^ M))
    (hF : ∀ ps ∈ F, ps.2 ∈ S ∧
      probeAt (Nat.two_pow_pos M) (oddStridePermOfPair M ps.1 ps.2) d = slot) :
    F.card ≤ S.card := by
  refine Finset.card_le_card_of_injOn Prod.snd (fun ps hps => (hF ps hps).1) ?_
  rintro ⟨p₁, s₁⟩ h₁ ⟨p₂, s₂⟩ h₂ (rfl : s₁ = s₂)
  exact Prod.ext (probeAt_oddStridePermOfPair_injective M s₁ d
    ((hF _ h₁).2.trans (hF _ h₂).2.symm)) rfl

private theorem card_filter_two_probes_eq_le (M : ℕ) {j₁ k_b : ℕ} (hjk : j₁ < k_b)
    (hkb : k_b < 2 ^ M) (slot₁ slot₂ : Fin (2 ^ M)) :
    (Finset.univ.filter fun ps : Fin (2 ^ M) × Fin (2 ^ (M - 1)) =>
      probeAt (Nat.two_pow_pos M) (oddStridePermOfPair M ps.1 ps.2) j₁ = slot₁ ∧
      probeAt (Nat.two_pow_pos M) (oddStridePermOfPair M ps.1 ps.2) k_b = slot₂).card ≤
        k_b - j₁ := by
  refine (card_filter_prod_probeAt_le M k_b slot₂
    (S := Finset.univ.filter fun s : Fin (2 ^ (M - 1)) =>
      ((k_b - j₁) * (2 * s.val + 1)) % 2 ^ M = (slot₂.val + 2 ^ M - slot₁.val) % 2 ^ M)
    fun ⟨p, s⟩ hps => ?_).trans (Nat.card_odd_mul_mod_eq_le M _ _ (by omega))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hps ⊢
  have h1 : p.val + j₁ * (2 * s.val + 1) ≡ slot₁.val [MOD 2 ^ M] := by
    simpa [probeAt_eq_of_lt (Nat.two_pow_pos M) _ (hjk.trans hkb), oddStrideSeq, Fin.ext_iff,
      Nat.ModEq, Nat.mod_eq_of_lt slot₁.isLt] using hps.1
  have h2 : p.val + k_b * (2 * s.val + 1) ≡ slot₂.val [MOD 2 ^ M] := by
    simpa [probeAt_eq_of_lt (Nat.two_pow_pos M) _ hkb, oddStrideSeq, Fin.ext_iff,
      Nat.ModEq, Nat.mod_eq_of_lt slot₂.isLt] using hps.2
  refine ⟨h1.add_left_cancel ?_, hps.2⟩
  calc p.val + j₁ * (2 * s.val + 1) + (k_b - j₁) * (2 * s.val + 1)
      = p.val + k_b * (2 * s.val + 1) := by
        rw [Nat.add_assoc, ← Nat.add_mul, Nat.add_sub_cancel' hjk.le]
    _ ≡ slot₂.val + 2 ^ M [MOD 2 ^ M] := h2.trans (Nat.add_modEq_right).symm
    _ = slot₁.val + (slot₂.val + 2 ^ M - slot₁.val) := by have := slot₁.isLt; omega

/-- **Single-Step Fiber Bound**: for any queue `q` with `q.toFinset.card ≤ w` and `w ≤ 2 ^ M`,
`(stepFiber M w q slot_b d).card ≤ 2 ^ (M - 1) + w ^ 4`. -/
private theorem card_stepFiber_le (M : ℕ) {w : ℕ} (hw : w ≤ 2 ^ M) (q : List (Fin (2 ^ M)))
    (hq : q.toFinset.card ≤ w) (slot_b : Fin (2 ^ M)) (d : ℕ) :
    (stepFiber M w q slot_b d).card ≤ 2 ^ (M - 1) + w ^ 4 := by
  classical
  let hm := Nat.two_pow_pos M
  let F₁ : Finset (Fin (2 ^ M) × Fin (2 ^ (M - 1))) :=
    Finset.univ.filter fun ps => probeAt hm (oddStridePermOfPair M ps.1 ps.2) d = slot_b
  let P (k_b j₁ : Fin w) (slot₁ : Fin (2 ^ M)) : Finset (Fin (2 ^ M) × Fin (2 ^ (M - 1))) :=
    Finset.univ.filter fun ps => j₁.val < k_b.val ∧
      probeAt hm (oddStridePermOfPair M ps.1 ps.2) j₁.val = slot₁ ∧
      probeAt hm (oddStridePermOfPair M ps.1 ps.2) k_b.val = slot_b
  have hsub : stepFiber M w q slot_b d ⊆ F₁ ∪ Finset.univ.biUnion fun k_b =>
      Finset.univ.biUnion fun j₁ => q.toFinset.biUnion (P k_b j₁) := by
    intro ps hps
    simp only [stepFiber, F₁, P, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_biUnion] at hps ⊢
    exact hps.imp_right fun ⟨k_b, j₁, hlt, hmem, heq⟩ => ⟨k_b, j₁, _, hmem, hlt, rfl, heq⟩
  have hF₁ : F₁.card ≤ 2 ^ (M - 1) := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      card_filter_prod_probeAt_le M d slot_b (S := Finset.univ) fun ps hps =>
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp hps).2⟩
  have hP_le (k_b j₁ : Fin w) (slot₁ : Fin (2 ^ M)) : (P k_b j₁ slot₁).card ≤ w := by
    by_cases hlt : j₁.val < k_b.val
    · simp only [P, hlt, true_and]
      exact (card_filter_two_probes_eq_le M hlt (k_b.isLt.trans_le hw) slot₁ slot_b).trans
        ((Nat.sub_le _ _).trans k_b.isLt.le)
    · simp [P, show ¬j₁ < k_b from hlt]
  calc (stepFiber M w q slot_b d).card
      ≤ F₁.card + _ := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    _ ≤ 2 ^ (M - 1) + Fintype.card (Fin w) * (Fintype.card (Fin w) * (q.toFinset.card * w)) :=
        Nat.add_le_add hF₁ (Finset.card_biUnion_le_card_mul _ _ _ fun k_b _ =>
          Finset.card_biUnion_le_card_mul _ _ _ fun j₁ _ =>
            Finset.card_biUnion_le_card_mul _ _ _ fun slot₁ _ => hP_le k_b j₁ slot₁)
    _ ≤ 2 ^ (M - 1) + w * (w * (w * w)) := by rw [Fintype.card_fin]; gcongr
    _ = 2 ^ (M - 1) + w ^ 4 := by ring

/-- Queue of discovered slots at step `b` for a prefix tuple
`ps : Fin (b + 1) → Fin (2 ^ M) × Fin (2 ^ (M - 1))`. -/
private noncomputable def tupleQueue (M w : ℕ) (h : Fin (w + 1) → ℕ) :
    (b : ℕ) → b ≤ w → (Fin (b + 1) → Fin (2 ^ M) × Fin (2 ^ (M - 1))) → List (Fin (2 ^ M))
  | 0, _, ps =>
      let hm := Nat.two_pow_pos M
      let σ₀ := oddStridePermOfPair M (ps 0).1 (ps 0).2
      probePrefix hm σ₀ (h 0)
  | b + 1, hb, ps =>
      let hm := Nat.two_pow_pos M
      let q := tupleQueue M w h b (Nat.le_of_succ_le hb) (Fin.init ps)
      let p_last := ps (Fin.last (b + 1))
      let σ := oddStridePermOfPair M p_last.1 p_last.2
      q ++ ((probePrefix hm σ w).filter (· ∉ q)).take
        (h ⟨b + 1, Nat.succ_lt_succ hb⟩)

private theorem length_tupleQueue_le (M w : ℕ) (h : Fin (w + 1) → ℕ) :
    ∀ (b : ℕ) (hb : b ≤ w) (ps : Fin (b + 1) → Fin (2 ^ M) × Fin (2 ^ (M - 1))),
      (tupleQueue M w h b hb ps).length ≤
        h 0 + ∑ i ∈ Finset.range b,
          if hi : i < w then h ⟨i + 1, Nat.succ_lt_succ hi⟩ else 0
  | 0, _, ps => by simp [tupleQueue, length_probePrefix]
  | b + 1, hbw, ps => by
      have hb : b < w := hbw
      have ih := length_tupleQueue_le M w h b hb.le (Fin.init ps)
      simp only [tupleQueue, List.length_append, Finset.sum_range_succ, hb, ↓reduceDIte,
        List.length_take]
      omega

private theorem card_toFinset_tupleQueue_le (M w : ℕ) (h : Fin (w + 1) → ℕ)
    (hsum : ∑ a : Fin (w + 1), h a = w) {b : ℕ} (hb : b ≤ w)
    (ps : Fin (b + 1) → Fin (2 ^ M) × Fin (2 ^ (M - 1))) :
    (tupleQueue M w h b hb ps).toFinset.card ≤ w := by
  have hsub := Finset.sum_le_sum_of_subset (Finset.range_mono hb)
    (f := fun i => if hi : i < w then h ⟨i + 1, Nat.succ_lt_succ hi⟩ else 0)
  linarith [List.toFinset_card_le (tupleQueue M w h b hb ps), length_tupleQueue_le M w h b hb ps,
    sum_fin_succ_eq h]

/-- Prefix tuples `ps : Fin (b + 1) → Fin (2 ^ M) × Fin (2 ^ (M - 1))` satisfying the first `b`
BFS step constraints. -/
private noncomputable def validTuples (M w : ℕ) (h : Fin (w + 1) → ℕ) :
    (b : ℕ) → b ≤ w → Finset (Fin (b + 1) → Fin (2 ^ M) × Fin (2 ^ (M - 1)))
  | 0, _ => Finset.univ
  | b + 1, hb =>
      (validTuples M w h b (Nat.le_of_succ_le hb)).biUnion fun ps =>
        let q := tupleQueue M w h b (Nat.le_of_succ_le hb) ps
        let slot_b := q.getD b ⟨0, Nat.two_pow_pos M⟩
        let d_b := h ⟨b + 1, Nat.succ_lt_succ hb⟩
        (stepFiber M w q slot_b d_b).map
          ⟨fun p_last => Fin.snoc ps p_last, fun p₁ p₂ hp => by
            simpa [Fin.snoc_last] using congrFun hp (Fin.last (b + 1))⟩

private theorem card_validTuples_le (M : ℕ) {w : ℕ} (hw : w ≤ 2 ^ M)
    (h : Fin (w + 1) → ℕ) (hsum : (∑ a : Fin (w + 1), h a) = w) :
    ∀ (b : ℕ) (hb : b ≤ w),
      (validTuples M w h b hb).card ≤
        (2 ^ M * 2 ^ (M - 1)) * (2 ^ (M - 1) + w ^ 4) ^ b
  | 0, _ => by simp [validTuples, Fintype.card_pi]
  | b + 1, hb => by
      have ih := card_validTuples_le M hw h hsum b (Nat.le_of_succ_le hb)
      calc (validTuples M w h (b + 1) hb).card
          ≤ (validTuples M w h b (Nat.le_of_succ_le hb)).card * (2 ^ (M - 1) + w ^ 4) :=
            Finset.card_biUnion_le_card_mul _ _ _ fun ps _ =>
              (Finset.card_map _).trans_le <| card_stepFiber_le M hw _
                (card_toFinset_tupleQueue_le M w h hsum (Nat.le_of_succ_le hb) ps) _ _
        _ ≤ (2 ^ M * 2 ^ (M - 1)) * (2 ^ (M - 1) + w ^ 4) ^ (b + 1) := by
            rw [pow_succ (2 ^ (M - 1) + w ^ 4), ← mul_assoc]; gcongr

private def restrictTuple {α : Type*} {w : ℕ} (f : Fin (w + 1) → α) (b : ℕ) (hb : b ≤ w) :
    Fin (b + 1) → α :=
  fun i => f ⟨i.val, lt_of_lt_of_le i.isLt (Nat.succ_le_succ hb)⟩

private theorem init_restrictTuple {α : Type*} {w : ℕ} (f : Fin (w + 1) → α) (b : ℕ)
    (hb : b + 1 ≤ w) :
    Fin.init (restrictTuple f (b + 1) hb) = restrictTuple f b (Nat.le_of_succ_le hb) :=
  rfl

private theorem snoc_restrictTuple {α : Type*} {w : ℕ} (f : Fin (w + 1) → α) (b : ℕ)
    (hb : b + 1 ≤ w) :
    Fin.snoc (restrictTuple f b (Nat.le_of_succ_le hb))
      (f ⟨b + 1, Nat.succ_lt_succ hb⟩) = restrictTuple f (b + 1) hb := by
  ext i
  cases i using Fin.lastCases <;> simp [restrictTuple]

private theorem tupleQueue_restrictTuple_eq_bfsQueue {U M w : ℕ}
    (x₀ : Fin U) (h : Fin (w + 1) → ℕ) (x : Fin w → Fin U)
    (p : Fin U → Fin (2 ^ M)) (s : Fin U → Fin (2 ^ (M - 1))) :
    let xExt : Fin (w + 1) → Fin U := Fin.cases x₀ x
    let f : Fin (w + 1) → Fin (2 ^ M) × Fin (2 ^ (M - 1)) := fun a => (p (xExt a), s (xExt a))
    let π : Fin U → Equiv.Perm (Fin (2 ^ M)) := fun u => oddStridePermOfPair M (p u) (s u)
    ∀ (b : ℕ) (hb : b ≤ w),
      tupleQueue M w h b hb (restrictTuple f b hb) =
        bfsQueue (Nat.two_pow_pos M) π x₀ w h x b := by
  intro xExt f π b hb
  induction b with
  | zero => rfl
  | succ b ih =>
      have hbw : b < w := hb
      simp only [tupleQueue, init_restrictTuple, ih hbw.le, bfsQueue, hbw, ↓reduceDIte]
      rfl

private theorem mem_validTuples_of_bfsStepEvent {U M w : ℕ}
    (x₀ : Fin U) (h : Fin (w + 1) → ℕ) (x : Fin w → Fin U)
    (p : Fin U → Fin (2 ^ M)) (s : Fin U → Fin (2 ^ (M - 1)))
    (hev : ∀ b : Fin w,
      bfsStepEvent (Nat.two_pow_pos M) (fun u => oddStridePermOfPair M (p u) (s u)) x₀ w h x b) :
    let xExt : Fin (w + 1) → Fin U := Fin.cases x₀ x
    let f : Fin (w + 1) → Fin (2 ^ M) × Fin (2 ^ (M - 1)) := fun a => (p (xExt a), s (xExt a))
    ∀ (b : ℕ) (hb : b ≤ w),
      restrictTuple f b hb ∈ validTuples M w h b hb := by
  intro xExt f b hb
  induction b with
  | zero => exact Finset.mem_univ _
  | succ b ih =>
      have hbw : b < w := hb
      have hev_b := hev ⟨b, hbw⟩
      dsimp only [bfsStepEvent] at hev_b
      rw [← tupleQueue_restrictTuple_eq_bfsQueue x₀ h x p s b hbw.le] at hev_b
      exact Finset.mem_biUnion.mpr ⟨restrictTuple f b hbw.le, ih hbw.le, Finset.mem_map.mpr
        ⟨f ⟨b + 1, Nat.succ_lt_succ hbw⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hev_b⟩,
          snoc_restrictTuple f b hb⟩⟩

open scoped Classical in
/-- **Fixed-Tuple BFS Event Bound under `k`-Wise Independence**:
for any `(w + 1)`-wise independent hash pair `(h₁, h₂)`, injective vertex sequence `x₀, x`,
and degree sequence `h` summing to `w ≤ 2 ^ M`, the number of seeds `θ : Θ₁ × Θ₂` satisfying all
`w` BFS step constraints is at most `(2 ^ (M - 1) + w ^ 4) ^ w / (2 ^ M * 2 ^ (M - 1)) ^ w` of
`Fintype.card (Θ₁ × Θ₂)`. -/
private theorem card_filter_bfsStepEvent_le
    {Θ₁ Θ₂ : Type*} [Fintype Θ₁] [Fintype Θ₂] {U M k w : ℕ}
    {h₁ : Θ₁ → Fin U → Fin (2 ^ M)} {h₂ : Θ₂ → Fin U → Fin (2 ^ (M - 1))}
    (hh₁ : Cslib.Probability.IsKWiseIndependentHash k h₁)
    (hh₂ : Cslib.Probability.IsKWiseIndependentHash k h₂)
    (hwk : w + 1 ≤ k) (hwM : w ≤ 2 ^ M)
    (x₀ : Fin U) (h : Fin (w + 1) → ℕ) (hsum : ∑ a : Fin (w + 1), h a = w)
    (x : Fin w → Fin U) (hx : Function.Injective x) (hne : ∀ b : Fin w, x b ≠ x₀) :
    (Finset.univ.filter fun θ : Θ₁ × Θ₂ =>
      ∀ b : Fin w,
        bfsStepEvent (Nat.two_pow_pos M) (oddStridePerm (h₁ θ.1) (h₂ θ.2)) x₀ w h x b).card *
      (2 ^ M * 2 ^ (M - 1)) ^ w ≤
      (2 ^ (M - 1) + w ^ 4) ^ w * Fintype.card (Θ₁ × Θ₂) := by
  let xExt : Fin (w + 1) → Fin U := Fin.cases x₀ x
  have hxExt : Function.Injective xExt :=
    Fin.cons_injective_iff.mpr ⟨fun ⟨b, hb⟩ => hne b hb, hx⟩
  have : Nonempty (Fin (2 ^ M)) := ⟨⟨0, Nat.two_pow_pos M⟩⟩
  have : Nonempty (Fin (2 ^ (M - 1))) := ⟨⟨0, Nat.two_pow_pos (M - 1)⟩⟩
  let V := validTuples M w h w le_rfl
  let evalSeed (θ : Θ₁ × Θ₂) : Fin (w + 1) → Fin (2 ^ M) × Fin (2 ^ (M - 1)) :=
    fun a => (h₁ θ.1 (xExt a), h₂ θ.2 (xExt a))
  let F (ps : Fin (w + 1) → Fin (2 ^ M) × Fin (2 ^ (M - 1))) : Finset (Θ₁ × Θ₂) :=
    Finset.univ.filter fun θ => evalSeed θ = ps
  set S_ev : Finset (Θ₁ × Θ₂) := Finset.univ.filter fun θ =>
    ∀ b : Fin w,
      bfsStepEvent (Nat.two_pow_pos M) (oddStridePerm (h₁ θ.1) (h₂ θ.2)) x₀ w h x b
  have hsub : S_ev ⊆ V.biUnion F := fun θ hθ => Finset.mem_biUnion.mpr ⟨evalSeed θ,
    mem_validTuples_of_bfsStepEvent x₀ h x (h₁ θ.1) (h₂ θ.2) (Finset.mem_filter.mp hθ).2 w le_rfl,
    Finset.mem_filter.mpr ⟨Finset.mem_univ θ, rfl⟩⟩
  have hF_eq (ps : Fin (w + 1) → Fin (2 ^ M) × Fin (2 ^ (M - 1))) :
      (F ps).card * (2 ^ M * 2 ^ (M - 1)) ^ (w + 1) = Fintype.card (Θ₁ × Θ₂) := by
    have hprod : F ps =
        (Finset.univ.filter fun θ₁ : Θ₁ => (fun a => h₁ θ₁ (xExt a)) = fun a => (ps a).1) ×ˢ
        (Finset.univ.filter fun θ₂ : Θ₂ => (fun a => h₂ θ₂ (xExt a)) = fun a => (ps a).2) := by
      ext ⟨θ₁, θ₂⟩
      simp [F, evalSeed, funext_iff, Prod.ext_iff, forall_and]
    have h1 := (hh₁.comp hxExt).card_filter_eq_of_card_le (by simpa using hwk) fun a => (ps a).1
    have h2 := (hh₂.comp hxExt).card_filter_eq_of_card_le (by simpa using hwk) fun a => (ps a).2
    simp only [Fintype.card_fin] at h1 h2
    rw [hprod, Finset.card_product, mul_pow, Fintype.card_prod, ← h1, ← h2]
    ring
  refine Nat.le_of_mul_le_mul_left ?_ (Nat.mul_pos (Nat.two_pow_pos M) (Nat.two_pow_pos (M - 1)))
  calc 2 ^ M * 2 ^ (M - 1) * (S_ev.card * (2 ^ M * 2 ^ (M - 1)) ^ w)
      = S_ev.card * (2 ^ M * 2 ^ (M - 1)) ^ (w + 1) := by ring
    _ ≤ (∑ ps ∈ V, (F ps).card) * (2 ^ M * 2 ^ (M - 1)) ^ (w + 1) :=
        Nat.mul_le_mul_right _ ((Finset.card_le_card hsub).trans Finset.card_biUnion_le)
    _ = V.card * Fintype.card (Θ₁ × Θ₂) := by
        simp only [Finset.sum_mul, hF_eq, Finset.sum_const, smul_eq_mul]
    _ ≤ ((2 ^ M * 2 ^ (M - 1)) * (2 ^ (M - 1) + w ^ 4) ^ w) * Fintype.card (Θ₁ × Θ₂) :=
        Nat.mul_le_mul_right _ (card_validTuples_le M hwM h hsum w le_rfl)
    _ = _ := by ring

private def degSeqFinset (w : ℕ) : Finset (Fin (w + 1) → Fin (w + 1)) :=
  Finset.univ.filter fun f => ∑ a : Fin (w + 1), (f a).val = w

private def degPrefSum (w : ℕ) (f : Fin (w + 1) → Fin (w + 1)) (b : ℕ) : ℕ :=
  b + ∑ a ∈ Finset.univ.filter (fun a : Fin (w + 1) => a.val ≤ b), (f a).val

private def degPrefImage (w : ℕ) (f : Fin (w + 1) → Fin (w + 1)) : Finset (Fin (2 * w)) :=
  (Finset.univ : Finset (Fin w)).image fun b =>
    if h : degPrefSum w f b.val < 2 * w then ⟨degPrefSum w f b.val, h⟩
    else ⟨0, by have := b.isLt; omega⟩

private theorem card_degSeqFinset_le_four_pow (w : ℕ) :
    (degSeqFinset w).card ≤ 4 ^ w := by
  have hinj : Set.InjOn (degPrefImage w) (degSeqFinset w) := by
    intro f₁ hf₁ f₂ hf₂ himg
    -- `g f` lists `degPrefImage w f` in increasing order, so the image determines `g f`.
    let g (f : Fin (w + 1) → Fin (w + 1)) (b : Fin w) : Fin (2 * w) :=
      if h : degPrefSum w f b.val < 2 * w then ⟨degPrefSum w f b.val, h⟩
      else ⟨0, by have := b.isLt; omega⟩
    have hg (f) (hf : f ∈ degSeqFinset w) (b : Fin w) : (g f b).val = degPrefSum w f b.val := by
      have hle := (Finset.sum_le_univ_sum_of_nonneg
        (s := Finset.univ.filter (·.val ≤ b.val)) fun _ => Nat.zero_le _).trans
        (Finset.mem_filter.mp hf).2.le
      have hlt : degPrefSum w f b.val < 2 * w := by have := b.isLt; dsimp only [degPrefSum]; omega
      simp only [g, hlt, ↓reduceDIte]
    have hg_mono : ∀ f ∈ degSeqFinset w, StrictMono (g f) := fun f hf b₁ b₂ hb => by
      rw [Fin.lt_def, hg f hf, hg f hf]
      have := Finset.sum_le_sum_of_subset (f := fun a : Fin (w + 1) => (f a).val)
        (Finset.monotone_filter_right Finset.univ fun a _ (h : a.val ≤ b₁.val) => h.trans hb.le)
      dsimp only [degPrefSum]
      omega
    have hg_eq : g f₁ = g f₂ := (hg_mono f₁ hf₁).eq_of_range_eq (hg_mono f₂ hf₂) <| by
      simpa using congrArg (↑· : Finset (Fin (2 * w)) → Set (Fin (2 * w)))
        (show Finset.univ.image (g f₁) = Finset.univ.image (g f₂) from himg)
    have hpref_eq : ∀ b ≤ w,
        ∑ a ∈ Finset.univ.filter (fun a : Fin (w + 1) => a.val ≤ b), (f₁ a).val =
          ∑ a ∈ Finset.univ.filter (fun a : Fin (w + 1) => a.val ≤ b), (f₂ a).val := fun b hb => by
      rcases hb.eq_or_lt with rfl | hlt_b
      · rw [Finset.filter_true_of_mem fun a _ => Nat.le_of_lt_succ a.isLt,
          (Finset.mem_filter.mp hf₁).2, (Finset.mem_filter.mp hf₂).2]
      · have hval := congrArg Fin.val (congrFun hg_eq ⟨b, hlt_b⟩)
        rw [hg f₁ hf₁, hg f₂ hf₂] at hval
        exact Nat.add_left_cancel hval
    -- Equal prefix sums give equal entries, by strong induction on the index.
    refine funext fun a => ?_
    induction hn : a.val using Nat.strong_induction_on generalizing a with
    | _ n ih =>
      have hmem : a ∈ Finset.univ.filter (fun c : Fin (w + 1) => c.val ≤ n) := by simp [hn]
      have h := hpref_eq n (hn ▸ Nat.le_of_lt_succ a.isLt)
      have hrest := Finset.sum_congr
        (rfl : (Finset.univ.filter (fun c : Fin (w + 1) => c.val ≤ n)).erase a = _)
        fun c hc => congrArg Fin.val (ih c.val (by simp [Fin.ext_iff] at hc; omega) c rfl)
      rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem, hrest] at h
      exact Fin.ext (Nat.add_right_cancel h)
  calc (degSeqFinset w).card ≤ (Finset.univ : Finset (Fin (2 * w))).powerset.card :=
      Finset.card_le_card_of_injOn (degPrefImage w) (fun f _ => by simp) hinj
    _ = 4 ^ w := by
      rw [Finset.card_powerset, Finset.card_univ, Fintype.card_fin, pow_mul]
      rfl

open scoped Classical in
/-- **Union Bound over BFS Witnesses of Size `w`**:
under `(w + 1)`-wise independence of `h₁` and `h₂`, `1 ≤ M`, `32 * n_max ≤ 2 ^ M`, and
`2 * w ^ 4 ≤ 2 ^ M`, the fraction of seeds `θ : Θ₁ × Θ₂` admitting a size-`w` BFS dependency
witness over `D` (with `D.card ≤ n_max`) rooted at `x₀` is at most `4 ^ (-w)`. -/
private theorem four_pow_mul_card_hasBFSWitness_le
    {Θ₁ Θ₂ : Type*} [Fintype Θ₁] [Fintype Θ₂] {U M n_max k w : ℕ}
    {h₁ : Θ₁ → Fin U → Fin (2 ^ M)} {h₂ : Θ₂ → Fin U → Fin (2 ^ (M - 1))}
    (hh₁ : Cslib.Probability.IsKWiseIndependentHash k h₁)
    (hh₂ : Cslib.Probability.IsKWiseIndependentHash k h₂)
    (hM : 1 ≤ M) (hload : 32 * n_max ≤ 2 ^ M) (hw4 : 2 * w ^ 4 ≤ 2 ^ M)
    (hwk : w + 1 ≤ k) {D : Finset (Fin U)} (hD : D.card ≤ n_max) (x₀ : Fin U) :
    4 ^ w * (Finset.univ.filter fun θ : Θ₁ × Θ₂ =>
      HasBFSWitness (Nat.two_pow_pos M) (oddStridePerm (h₁ θ.1) (h₂ θ.2)) D x₀ w).card ≤
      Fintype.card (Θ₁ × Θ₂) := by
  have hwM : w ≤ 2 ^ M := (Nat.le_self_pow (n := 4) (by norm_num) w).trans (by omega)
  let X_set : Finset (Fin w → Fin U) :=
    (Fintype.piFinset fun _ : Fin w => D.erase x₀).filter Function.Injective
  have hX_card : X_set.card ≤ n_max ^ w := (Finset.card_filter_le _ _).trans <| by
    simpa [Fintype.card_piFinset] using Nat.pow_le_pow_left ((Finset.card_erase_le).trans hD) w
  let E (f : Fin (w + 1) → Fin (w + 1)) (x : Fin w → Fin U) : Finset (Θ₁ × Θ₂) :=
    Finset.univ.filter fun θ =>
      ∀ b : Fin w,
        bfsStepEvent (Nat.two_pow_pos M) (oddStridePerm (h₁ θ.1) (h₂ θ.2))
          x₀ w (fun a => (f a).val) x b
  set S_wit : Finset (Θ₁ × Θ₂) := Finset.univ.filter fun θ =>
    HasBFSWitness (Nat.two_pow_pos M) (oddStridePerm (h₁ θ.1) (h₂ θ.2)) D x₀ w
  have hsub : S_wit ⊆ (degSeqFinset w).biUnion fun f => X_set.biUnion fun x => E f x := by
    intro θ hθ
    obtain ⟨h, _, hsum, x, hx_inj, hx_mem, hev⟩ := (Finset.mem_filter.mp hθ).2
    have hle_w (a : Fin (w + 1)) : h a ≤ w :=
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)).trans hsum.le
    exact Finset.mem_biUnion.mpr ⟨fun a => ⟨h a, Nat.lt_succ_of_le (hle_w a)⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsum⟩, Finset.mem_biUnion.mpr
        ⟨x, Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr hx_mem, hx_inj⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ θ, hev⟩⟩⟩
  have hE_le : ∀ f ∈ degSeqFinset w, ∀ x ∈ X_set, (E f x).card * (2 ^ M * 2 ^ (M - 1)) ^ w ≤
      (2 ^ (M - 1) + w ^ 4) ^ w * Fintype.card (Θ₁ × Θ₂) := fun f hf x hx =>
    card_filter_bfsStepEvent_le hh₁ hh₂ hwk hwM x₀ (fun a => (f a).val) (Finset.mem_filter.mp hf).2
      x (Finset.mem_filter.mp hx).2 fun b =>
        (Finset.mem_erase.mp (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hx).1 b)).1
  have hsum_bi : S_wit.card * (2 ^ M * 2 ^ (M - 1)) ^ w ≤
      4 ^ w * (n_max ^ w * ((2 ^ (M - 1) + w ^ 4) ^ w * Fintype.card (Θ₁ × Θ₂))) :=
    calc S_wit.card * (2 ^ M * 2 ^ (M - 1)) ^ w
        ≤ (∑ f ∈ degSeqFinset w, ∑ x ∈ X_set, (E f x).card) * (2 ^ M * 2 ^ (M - 1)) ^ w :=
          Nat.mul_le_mul_right _ ((Finset.card_le_card hsub).trans
            (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun f _ => Finset.card_biUnion_le)))
      _ ≤ (degSeqFinset w).card *
            (X_set.card * ((2 ^ (M - 1) + w ^ 4) ^ w * Fintype.card (Θ₁ × Θ₂))) := by
          simp only [Finset.sum_mul]
          exact Finset.sum_le_card_nsmul _ _ _ fun f hf =>
            Finset.sum_le_card_nsmul _ _ _ fun x hx => hE_le f hf x hx
      _ ≤ 4 ^ w * (n_max ^ w * ((2 ^ (M - 1) + w ^ 4) ^ w * Fintype.card (Θ₁ × Θ₂))) :=
          Nat.mul_le_mul (card_degSeqFinset_le_four_pow w)
            (Nat.mul_le_mul_right _ hX_card)
  have h2M_eq : 2 ^ M = 2 * 2 ^ (M - 1) := by rw [← pow_succ', Nat.sub_add_cancel hM]
  have hstep_base : 16 * n_max * (2 ^ (M - 1) + w ^ 4) ≤ 2 ^ M * 2 ^ (M - 1) :=
    calc 16 * n_max * (2 ^ (M - 1) + w ^ 4)
        ≤ 2 ^ (M - 1) * (2 ^ (M - 1) + 2 ^ (M - 1)) :=
          Nat.mul_le_mul (by omega) (Nat.add_le_add_left (by omega) _)
      _ = 2 ^ M * 2 ^ (M - 1) := by rw [h2M_eq]; ring
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.pow_pos (n := w)
    (Nat.mul_pos (Nat.two_pow_pos M) (Nat.two_pow_pos (M - 1))))
  calc (4 ^ w * S_wit.card) * (2 ^ M * 2 ^ (M - 1)) ^ w
      = 4 ^ w * (S_wit.card * (2 ^ M * 2 ^ (M - 1)) ^ w) := by ring
    _ ≤ 4 ^ w * (4 ^ w * (n_max ^ w * ((2 ^ (M - 1) + w ^ 4) ^ w * Fintype.card (Θ₁ × Θ₂)))) :=
        Nat.mul_le_mul_left _ hsum_bi
    _ = (16 * n_max * (2 ^ (M - 1) + w ^ 4)) ^ w * Fintype.card (Θ₁ × Θ₂) := by
        simp only [mul_pow]
        rw [show (16 : ℕ) = 4 * 4 from rfl, mul_pow]
        ring
    _ ≤ (2 ^ M * 2 ^ (M - 1)) ^ w * Fintype.card (Θ₁ × Θ₂) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hstep_base w)
    _ = Fintype.card (Θ₁ × Θ₂) * (2 ^ M * 2 ^ (M - 1)) ^ w := Nat.mul_comm _ _

private theorem mul_two_pow_succ_le_four_pow : ∀ w : ℕ, w * 2 ^ (w + 1) ≤ 4 ^ w
  | 0 => by simp
  | 1 => by decide
  | w + 2 => by
      have ih : (w + 1) * 2 ^ (w + 2) ≤ 4 ^ (w + 1) := mul_two_pow_succ_le_four_pow (w + 1)
      rw [pow_succ 4, pow_succ 2 (w + 2)]
      nlinarith [Nat.zero_le (w * 2 ^ (w + 2))]

/-- Geometric-decay summation with the slack kept explicit: if `2 ^ (w - a + 1) * f w ≤ B` on
`[a, a + n)`, then `2 ^ n * ∑ f + B ≤ 2 ^ n * B`. -/
private theorem two_pow_mul_sum_Ico_add_le {a B : ℕ} {f : ℕ → ℕ} : ∀ n : ℕ,
    (∀ w ∈ Finset.Ico a (a + n), 2 ^ (w - a + 1) * f w ≤ B) →
      2 ^ n * ∑ w ∈ Finset.Ico a (a + n), f w + B ≤ 2 ^ n * B
  | 0, _ => by simp
  | n + 1, h => by
      have ih := two_pow_mul_sum_Ico_add_le n fun w hw =>
        h w (Finset.Ico_subset_Ico_right (by omega) hw)
      have hn := h (a + n) (by simp)
      rw [Nat.add_sub_cancel_left, pow_succ] at hn
      rw [← Nat.add_assoc, Finset.sum_Ico_succ_top (Nat.le_add_right a n), pow_succ]
      linarith

/-- If `f w ≤ B / 2 ^ (w - a + 1)` on `[a, b)`, then `∑ w ∈ [a, b), f w ≤ B`. -/
private theorem sum_Ico_le_of_two_pow_mul_le {a b B : ℕ} {f : ℕ → ℕ}
    (h : ∀ w ∈ Finset.Ico a b, 2 ^ (w - a + 1) * f w ≤ B) : ∑ w ∈ Finset.Ico a b, f w ≤ B := by
  rcases le_total b a with hba | hab
  · simp [Finset.Ico_eq_empty_of_le hba]
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hab
    exact Nat.le_of_mul_le_mul_left ((Nat.le_add_right _ B).trans
      (two_pow_mul_sum_Ico_add_le n h)) (Nat.two_pow_pos n)

private theorem four_mul_n_max_sq_le_four_pow_maxProbeCutoff (n_max : ℕ) :
    4 * n_max * (n_max + 1) ≤ 4 ^ maxProbeCutoff n_max := by
  have hclog := Nat.le_pow_clog (b := 2) (by decide) (max n_max 4)
  calc 4 * n_max * (n_max + 1)
      ≤ (16 * 2 ^ Nat.clog 2 (max n_max 4)) * (16 * 2 ^ Nat.clog 2 (max n_max 4)) :=
        Nat.mul_le_mul (by omega) (by omega)
    _ = (2 * 2) ^ maxProbeCutoff n_max := by rw [mul_pow, maxProbeCutoff, pow_add]; ring

open scoped Classical in
/-- **Seed-Sum Probe-Count Bound under `(2 * L + 1)`-Wise Independence**:
for `1 ≤ M`, `32 * max n_max 4 ≤ 2 ^ M`, `2 * (2 * maxProbeCutoff n_max) ^ 4 ≤ 2 ^ M`, and
any `(2 * maxProbeCutoff n_max + 1)`-wise independent hash families `h₁` and `h₂`, the sum of
`probeCount (T θ) u (oddStridePerm (h₁ θ.1) (h₂ θ.2) u)` over all `θ : Θ₁ × Θ₂` is at most
`2 * Fintype.card (Θ₁ × Θ₂)`. -/
theorem sum_probeCount_oddStride_le_of_kWiseIndependent
    {Θ₁ Θ₂ : Type*} [Fintype Θ₁] [Fintype Θ₂] {U M n_max : ℕ}
    {h₁ : Θ₁ → Fin U → Fin (2 ^ M)} {h₂ : Θ₂ → Fin U → Fin (2 ^ (M - 1))}
    (hh₁ : Cslib.Probability.IsKWiseIndependentHash (2 * maxProbeCutoff n_max + 1) h₁)
    (hh₂ : Cslib.Probability.IsKWiseIndependentHash (2 * maxProbeCutoff n_max + 1) h₂)
    (hM : 1 ≤ M) (hload : 32 * max n_max 4 ≤ 2 ^ M)
    (hw4 : 2 * (2 * maxProbeCutoff n_max) ^ 4 ≤ 2 ^ M)
    {s : Dictionary.State U} {T : Θ₁ × Θ₂ → Table U (2 ^ M)}
    (hrep : ∀ θ, OrderedTableRep (oddStridePerm (h₁ θ.1) (h₂ θ.2)) s (T θ))
    (hdom : (Dictionary.dom s).card ≤ n_max) (u : Fin U) :
    (∑ θ : Θ₁ × Θ₂, probeCount (T θ) u (oddStridePerm (h₁ θ.1) (h₂ θ.2) u)) ≤
      2 * Fintype.card (Θ₁ × Θ₂) := by
  let L := maxProbeCutoff n_max
  have hL_ge4 : 4 ≤ L := by wram_omega
  let D := (Dictionary.dom s).erase u
  let C (x₀ : Fin U) (w : ℕ) : ℕ :=
    (Finset.univ.filter fun θ : Θ₁ × Θ₂ =>
      HasBFSWitness (Nat.two_pow_pos M) (oddStridePerm (h₁ θ.1) (h₂ θ.2)) D x₀ w).card
  have hC_bound (x₀ : Fin U) {w : ℕ} (hw : w < 2 * L) :
      4 ^ w * C x₀ w ≤ Fintype.card (Θ₁ × Θ₂) :=
    four_pow_mul_card_hasBFSWitness_le hh₁ hh₂ hM
      ((Nat.mul_le_mul_left 32 (le_max_left n_max 4)).trans hload)
      ((Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hw.le 4)).trans hw4) (by omega)
      (Finset.card_erase_le.trans hdom) x₀
  have hC_sum (x₀ : Fin U) (w c : ℕ) :
      (∑ θ : Θ₁ × Θ₂,
        if HasBFSWitness (Nat.two_pow_pos M) (oddStridePerm (h₁ θ.1) (h₂ θ.2)) D x₀ w then c
        else 0) = c * C x₀ w := by
    simp [C, Finset.sum_ite, mul_comm]
  have hnorm_two :
      2 * (∑ w ∈ Finset.Ico 1 L, w * C u w) ≤ Fintype.card (Θ₁ × Θ₂) := by
    rw [Finset.mul_sum]
    refine sum_Ico_le_of_two_pow_mul_le fun w hw => ?_
    obtain ⟨hw1, hwL⟩ := Finset.mem_Ico.mp hw
    calc 2 ^ (w - 1 + 1) * (2 * (w * C u w)) = (w * 2 ^ (w + 1)) * C u w := by
          rw [Nat.sub_add_cancel hw1]; ring
      _ ≤ 4 ^ w * C u w := Nat.mul_le_mul_right _ (mul_two_pow_succ_le_four_pow w)
      _ ≤ Fintype.card (Θ₁ × Θ₂) := hC_bound u (by omega)
  have hov_x₀ (x₀ : Fin U) :
      4 ^ L * (∑ w ∈ Finset.Ico L (2 * L), C x₀ w) ≤ 2 * Fintype.card (Θ₁ × Θ₂) := by
    rw [Finset.mul_sum]
    refine sum_Ico_le_of_two_pow_mul_le fun w hw => ?_
    obtain ⟨hwL, hw2L⟩ := Finset.mem_Ico.mp hw
    calc 2 ^ (w - L + 1) * (4 ^ L * C x₀ w) = 2 * ((2 ^ (w - L) * 4 ^ L) * C x₀ w) := by ring
      _ ≤ 2 * ((4 ^ (w - L) * 4 ^ L) * C x₀ w) := by gcongr; decide
      _ = 2 * (4 ^ w * C x₀ w) := by rw [← pow_add, Nat.sub_add_cancel hwL]
      _ ≤ 2 * Fintype.card (Θ₁ × Θ₂) := Nat.mul_le_mul_left 2 (hC_bound x₀ hw2L)
  have hov_two :
      2 * (n_max * ∑ x₀ ∈ insert u (Dictionary.dom s), ∑ w ∈ Finset.Ico L (2 * L), C x₀ w) ≤
        Fintype.card (Θ₁ × Θ₂) := by
    have hsum_4L := (Finset.sum_le_card_nsmul _ _ _ fun x₀ _ => hov_x₀ x₀).trans
      (Nat.mul_le_mul_right _ ((Finset.card_insert_le u _).trans (Nat.add_le_add_right hdom 1)))
    rw [← Finset.mul_sum] at hsum_4L
    refine Nat.le_of_mul_le_mul_left ?_ (Nat.pow_pos (n := L) (show 0 < 4 by decide))
    linarith [Nat.mul_le_mul_left (2 * n_max) hsum_4L, Nat.mul_le_mul_right (Fintype.card (Θ₁ × Θ₂))
      (four_mul_n_max_sq_le_four_pow_maxProbeCutoff n_max)]
  have hpt :
      (∑ θ : Θ₁ × Θ₂, probeCount (T θ) u (oddStridePerm (h₁ θ.1) (h₂ θ.2) u)) ≤
        Fintype.card (Θ₁ × Θ₂) +
        (∑ w ∈ Finset.Ico 1 L, w * C u w) +
        n_max * (∑ x₀ ∈ insert u (Dictionary.dom s), ∑ w ∈ Finset.Ico L (2 * L), C x₀ w) := by
    refine (Finset.sum_le_sum fun θ _ => probeCount_le_sum_hasBFSWitness (Nat.two_pow_pos M)
      (hrep θ) hdom u (L := L) (by omega)).trans_eq ?_
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
      ← Finset.mul_sum]
    congr 2
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun w _ => hC_sum u w w
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun x₀ _ => Finset.sum_comm.trans
        (Finset.sum_congr rfl fun w _ => (hC_sum x₀ w 1).trans (one_mul _))
  omega

/-- **Expected Probe-Count Bound under `(2 * L + 1)`-Wise Independence**:
under the hypotheses of `sum_probeCount_oddStride_le_of_kWiseIndependent`, the expected probe count
of `u` under `PMF.uniformOfFintype (Θ₁ × Θ₂)` is at most `2` ([SchmidtSiegel1990], Theorem 1). -/
theorem expect_probeCount_oddStride_of_kWiseIndependent
    {Θ₁ Θ₂ : Type*} [Fintype Θ₁] [Fintype Θ₂] [Nonempty Θ₁] [Nonempty Θ₂] {U M n_max : ℕ}
    {h₁ : Θ₁ → Fin U → Fin (2 ^ M)} {h₂ : Θ₂ → Fin U → Fin (2 ^ (M - 1))}
    (hh₁ : Cslib.Probability.IsKWiseIndependentHash (2 * maxProbeCutoff n_max + 1) h₁)
    (hh₂ : Cslib.Probability.IsKWiseIndependentHash (2 * maxProbeCutoff n_max + 1) h₂)
    (hM : 1 ≤ M) (hload : 32 * max n_max 4 ≤ 2 ^ M)
    (hw4 : 2 * (2 * maxProbeCutoff n_max) ^ 4 ≤ 2 ^ M)
    {s : Dictionary.State U} {T : Θ₁ × Θ₂ → Table U (2 ^ M)}
    (hrep : ∀ θ, OrderedTableRep (oddStridePerm (h₁ θ.1) (h₂ θ.2)) s (T θ))
    (hdom : (Dictionary.dom s).card ≤ n_max) (u : Fin U) :
    (∑' θ : Θ₁ × Θ₂,
      PMF.uniformOfFintype (Θ₁ × Θ₂) θ *
        (probeCount (T θ) u (oddStridePerm (h₁ θ.1) (h₂ θ.2) u) : ℝ≥0∞)) ≤ 2 :=
  PMF.tsum_uniformOfFintype_le_of_sum_le
    (sum_probeCount_oddStride_le_of_kWiseIndependent hh₁ hh₂ hM hload hw4 hrep hdom u)

/-! ## Section 5: High-Probability Conditioning Bridge & Double Tabulation Instantiation -/

open Cslib.Probability

/-- Odd-stride double-hashing permutation family on a two-stage seed pair
`((top₁, bottom₁), (top₂, bottom₂)) : (Θ_top₁ × Θ_bot₁) × (Θ_top₂ × Θ_bot₂)`. -/
noncomputable def twoStageOddStridePerm {Θ_top₁ Θ_bot₁ Θ_top₂ Θ_bot₂ : Type*} {U M : ℕ}
    (H₁ : Θ_top₁ → Θ_bot₁ → Fin U → Fin (2 ^ M))
    (H₂ : Θ_top₂ → Θ_bot₂ → Fin U → Fin (2 ^ (M - 1))) :
    (Θ_top₁ × Θ_bot₁) × (Θ_top₂ × Θ_bot₂) → Fin U → Equiv.Perm (Fin (2 ^ M))
  | ((top₁, bottom₁), (top₂, bottom₂)) => oddStridePerm (H₁ top₁ bottom₁) (H₂ top₂ bottom₂)

theorem twoStageOddStridePerm_apply {Θ_top₁ Θ_bot₁ Θ_top₂ Θ_bot₂ : Type*} {U M : ℕ}
    (H₁ : Θ_top₁ → Θ_bot₁ → Fin U → Fin (2 ^ M))
    (H₂ : Θ_top₂ → Θ_bot₂ → Fin U → Fin (2 ^ (M - 1))) (top₁ : Θ_top₁) (bottom₁ : Θ_bot₁)
    (top₂ : Θ_top₂) (bottom₂ : Θ_bot₂) :
    twoStageOddStridePerm H₁ H₂ ((top₁, bottom₁), (top₂, bottom₂)) =
      oddStridePerm (H₁ top₁ bottom₁) (H₂ top₂ bottom₂) := by
  rfl

/-- **High-Probability Conditioning Bridge for Odd-Stride Double Hashing**:
if `H₁ top₁` and `H₂ top₂` are `(2 * maxProbeCutoff n_max + 1)`-wise independent whenever
`Good₁ top₁` and `Good₂ top₂` hold, and the bad top-seed sets `Finset.univ.filter (¬ Goodᵢ ·)`
each have density at most `1 / (2 * (n_max + 1))`, then the sum of `probeCount` over all seeds
`θ : (Θ_top₁ × Θ_bot₁) × (Θ_top₂ × Θ_bot₂)` is at most `3` times the total number of seeds. -/
theorem sum_probeCount_oddStride_of_whp_kWiseIndependent
    {Θ_top₁ Θ_bot₁ Θ_top₂ Θ_bot₂ : Type*}
    [Fintype Θ_top₁] [Fintype Θ_bot₁] [Fintype Θ_top₂] [Fintype Θ_bot₂]
    {U M n_max : ℕ}
    {H₁ : Θ_top₁ → Θ_bot₁ → Fin U → Fin (2 ^ M)}
    {H₂ : Θ_top₂ → Θ_bot₂ → Fin U → Fin (2 ^ (M - 1))}
    (Good₁ : Θ_top₁ → Prop) (Good₂ : Θ_top₂ → Prop)
    [DecidablePred Good₁] [DecidablePred Good₂]
    (hk₁ : ∀ top₁, Good₁ top₁ →
      Cslib.Probability.IsKWiseIndependentHash (2 * maxProbeCutoff n_max + 1) (H₁ top₁))
    (hk₂ : ∀ top₂, Good₂ top₂ →
      Cslib.Probability.IsKWiseIndependentHash (2 * maxProbeCutoff n_max + 1) (H₂ top₂))
    (hbad₁ : 2 * (Finset.univ.filter (fun top₁ : Θ_top₁ => ¬ Good₁ top₁)).card * (n_max + 1) ≤
      Fintype.card Θ_top₁)
    (hbad₂ : 2 * (Finset.univ.filter (fun top₂ : Θ_top₂ => ¬ Good₂ top₂)).card * (n_max + 1) ≤
      Fintype.card Θ_top₂)
    (hM : 1 ≤ M) (hload : 32 * max n_max 4 ≤ 2 ^ M)
    (hw4 : 2 * (2 * maxProbeCutoff n_max) ^ 4 ≤ 2 ^ M)
    {s : Dictionary.State U}
    {T : (Θ_top₁ × Θ_bot₁) × (Θ_top₂ × Θ_bot₂) → Table U (2 ^ M)}
    (hrep : ∀ θ, OrderedTableRep (twoStageOddStridePerm H₁ H₂ θ) s (T θ))
    (hdom : (Dictionary.dom s).card ≤ n_max) (u : Fin U) :
    (∑ θ : (Θ_top₁ × Θ_bot₁) × (Θ_top₂ × Θ_bot₂),
      probeCount (T θ) u (twoStageOddStridePerm H₁ H₂ θ u)) ≤
      3 * Fintype.card ((Θ_top₁ × Θ_bot₁) × (Θ_top₂ × Θ_bot₂)) := by
  let B_card := Fintype.card (Θ_bot₁ × Θ_bot₂)
  let b₁ (top₁ : Θ_top₁) : ℕ := (n_max + 1) * if ¬ Good₁ top₁ then 1 else 0
  let b₂ (top₂ : Θ_top₂) : ℕ := (n_max + 1) * if ¬ Good₂ top₂ then 1 else 0
  have hinner (top₁ : Θ_top₁) (top₂ : Θ_top₂) :
      (∑ bot : Θ_bot₁ × Θ_bot₂,
        probeCount (T ((top₁, bot.1), (top₂, bot.2))) u
          (oddStridePerm (H₁ top₁ bot.1) (H₂ top₂ bot.2) u)) ≤
        (2 + b₁ top₁ + b₂ top₂) * B_card := by
    by_cases h : Good₁ top₁ ∧ Good₂ top₂
    · simpa [b₁, b₂, h.1, h.2, B_card] using sum_probeCount_oddStride_le_of_kWiseIndependent
        (hk₁ top₁ h.1) (hk₂ top₂ h.2) hM hload hw4
        (fun bot => hrep ((top₁, bot.1), (top₂, bot.2))) hdom u
    · -- Deterministic fallback for a bad top seed: every probe count is at most `n_max + 1`.
      calc _ ≤ ∑ _bot : Θ_bot₁ × Θ_bot₂, (n_max + 1) :=
            Finset.sum_le_sum fun bot _ =>
              probeCount_le_add_one (hrep ((top₁, bot.1), (top₂, bot.2))).toTableRep hdom u
        _ = (n_max + 1) * B_card := by simp [B_card, Nat.mul_comm]
        _ ≤ (2 + b₁ top₁ + b₂ top₂) * B_card := Nat.mul_le_mul_right B_card <| by
            simp only [b₁, b₂]; split_ifs <;> first | omega | tauto
  calc (∑ θ : (Θ_top₁ × Θ_bot₁) × (Θ_top₂ × Θ_bot₂),
        probeCount (T θ) u (twoStageOddStridePerm H₁ H₂ θ u))
      = ∑ top₁ : Θ_top₁, ∑ top₂ : Θ_top₂, ∑ bot : Θ_bot₁ × Θ_bot₂,
          probeCount (T ((top₁, bot.1), (top₂, bot.2))) u
            (oddStridePerm (H₁ top₁ bot.1) (H₂ top₂ bot.2) u) := by
        simp only [Fintype.sum_prod_type, twoStageOddStridePerm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ ≤ ∑ top₁ : Θ_top₁, ∑ top₂ : Θ_top₂, (2 + b₁ top₁ + b₂ top₂) * B_card :=
        Finset.sum_le_sum fun top₁ _ => Finset.sum_le_sum fun top₂ _ => hinner top₁ top₂
    _ ≤ (3 * (Fintype.card Θ_top₁ * Fintype.card Θ_top₂)) * B_card := by
        simp only [b₁, b₂, ← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, smul_eq_mul, ← Finset.mul_sum, Finset.sum_boole, Nat.cast_id]
        have h1 := Nat.mul_le_mul_right (Fintype.card Θ_top₂) hbad₁
        have h2 := Nat.mul_le_mul_left (Fintype.card Θ_top₁) hbad₂
        exact Nat.mul_le_mul_right _ (by ring_nf at h1 h2 ⊢; omega)
    _ = 3 * Fintype.card ((Θ_top₁ × Θ_bot₁) × (Θ_top₂ × Θ_bot₂)) := by
        simp only [B_card, Fintype.card_prod]; ring

/-- **Expected Probe-Count Bound under High-Probability `(2 * L + 1)`-Wise Independence**:
under the hypotheses of `sum_probeCount_oddStride_of_whp_kWiseIndependent`, the expected probe count
of `u` under `PMF.uniformOfFintype ((Θ_top₁ × Θ_bot₁) × (Θ_top₂ × Θ_bot₂))` is at most `3`. -/
theorem expect_probeCount_oddStride_of_whp_kWiseIndependent
    {Θ_top₁ Θ_bot₁ Θ_top₂ Θ_bot₂ : Type*}
    [Fintype Θ_top₁] [Fintype Θ_bot₁] [Fintype Θ_top₂] [Fintype Θ_bot₂]
    [Nonempty Θ_top₁] [Nonempty Θ_bot₁] [Nonempty Θ_top₂] [Nonempty Θ_bot₂]
    {U M n_max : ℕ}
    {H₁ : Θ_top₁ → Θ_bot₁ → Fin U → Fin (2 ^ M)}
    {H₂ : Θ_top₂ → Θ_bot₂ → Fin U → Fin (2 ^ (M - 1))}
    (Good₁ : Θ_top₁ → Prop) (Good₂ : Θ_top₂ → Prop)
    [DecidablePred Good₁] [DecidablePred Good₂]
    (hk₁ : ∀ top₁, Good₁ top₁ →
      Cslib.Probability.IsKWiseIndependentHash (2 * maxProbeCutoff n_max + 1) (H₁ top₁))
    (hk₂ : ∀ top₂, Good₂ top₂ →
      Cslib.Probability.IsKWiseIndependentHash (2 * maxProbeCutoff n_max + 1) (H₂ top₂))
    (hbad₁ : 2 * (Finset.univ.filter (fun top₁ : Θ_top₁ => ¬ Good₁ top₁)).card * (n_max + 1) ≤
      Fintype.card Θ_top₁)
    (hbad₂ : 2 * (Finset.univ.filter (fun top₂ : Θ_top₂ => ¬ Good₂ top₂)).card * (n_max + 1) ≤
      Fintype.card Θ_top₂)
    (hM : 1 ≤ M) (hload : 32 * max n_max 4 ≤ 2 ^ M)
    (hw4 : 2 * (2 * maxProbeCutoff n_max) ^ 4 ≤ 2 ^ M)
    {s : Dictionary.State U}
    {T : (Θ_top₁ × Θ_bot₁) × (Θ_top₂ × Θ_bot₂) → Table U (2 ^ M)}
    (hrep : ∀ θ, OrderedTableRep (twoStageOddStridePerm H₁ H₂ θ) s (T θ))
    (hdom : (Dictionary.dom s).card ≤ n_max) (u : Fin U) :
    (∑' θ : (Θ_top₁ × Θ_bot₁) × (Θ_top₂ × Θ_bot₂),
      PMF.uniformOfFintype ((Θ_top₁ × Θ_bot₁) × (Θ_top₂ × Θ_bot₂)) θ *
        (probeCount (T θ) u (twoStageOddStridePerm H₁ H₂ θ u) : ℝ≥0∞)) ≤ 3 :=
  PMF.tsum_uniformOfFintype_le_of_sum_le
    (sum_probeCount_oddStride_of_whp_kWiseIndependent
      Good₁ Good₂ hk₁ hk₂ hbad₁ hbad₂ hM hload hw4 hrep hdom u)

/-- Seed space for odd-stride double hashing instantiated with two independent copies of Mikkel
Thorup's Double Tabulation (`[Thorup2013]`, Theorem 1(a)), into `Fin (2 ^ M)` and
`Fin (2 ^ (M - 1))`. -/
abbrev DoubleTabOddStrideSeed (c b M : ℕ) : Type :=
  (DoubleTabTopSeed c (8 * c) b × DoubleTabBotSeed (8 * c) b M) ×
    (DoubleTabTopSeed c (8 * c) b × DoubleTabBotSeed (8 * c) b (M - 1))

/-- Odd-stride double-hashing permutation family driven by two independent `doubleTabHash`
instances (`[Thorup2013]`, Theorem 1(a)). -/
@[expose] noncomputable def doubleTabOddStridePerm (c b U M : ℕ) :
    DoubleTabOddStrideSeed c b M → Fin U → Equiv.Perm (Fin (2 ^ M)) :=
  twoStageOddStridePerm (doubleTabHash c (8 * c) b U M) (doubleTabHash c (8 * c) b U (M - 1))

/-- **Double Tabulation Summed Probe-Count Bound under Explicit Code Bound (`[Thorup2013]`,
Theorem 1(a) & `[SchmidtSiegel1990]`, Theorem 1)**:
when `1 ≤ c`, `U ≤ 2 ^ (c * b)`, `1 ≤ M`, `32 * max n_max 4 ≤ 2 ^ M`,
`2 * (2 * maxProbeCutoff n_max) ^ 4 ≤ 2 ^ M`, and
`2 * (n_max + 1) * doubleTabCodeBound c (8 * c) 4 (2 * maxProbeCutoff n_max + 1) ≤ 2 ^ (3 * b)`,
the sum of `probeCount` over all seeds in `DoubleTabOddStrideSeed c b M` is at most `3` times the
total number of seeds. -/
theorem sum_probeCount_oddStride_doubleTab_of_codeBound_le
    {c b U M n_max : ℕ}
    (hc : 1 ≤ c) (hU : U ≤ 2 ^ (c * b))
    (hM : 1 ≤ M) (hload : 32 * max n_max 4 ≤ 2 ^ M)
    (hw4 : 2 * (2 * maxProbeCutoff n_max) ^ 4 ≤ 2 ^ M)
    (hbound : 2 * (n_max + 1) *
      doubleTabCodeBound c (8 * c) 4 (2 * maxProbeCutoff n_max + 1) ≤ 2 ^ (3 * b))
    {s : Dictionary.State U}
    {T : DoubleTabOddStrideSeed c b M → Table U (2 ^ M)}
    (hrep : ∀ θ, OrderedTableRep (doubleTabOddStridePerm c b U M θ) s (T θ))
    (hdom : (Dictionary.dom s).card ≤ n_max) (u : Fin U) :
    (∑ θ : DoubleTabOddStrideSeed c b M,
      probeCount (T θ) u (doubleTabOddStridePerm c b U M θ u)) ≤
      3 * Fintype.card (DoubleTabOddStrideSeed c b M) := by
  let k := 2 * maxProbeCutoff n_max + 1
  let Good (T₁ : DoubleTabTopSeed c (8 * c) b) : Prop := IsKUnique k (simpleTabTuple T₁)
  have hwhp : 2 * (Finset.univ.filter fun T₁ : DoubleTabTopSeed c (8 * c) b => ¬ Good T₁).card *
      (n_max + 1) ≤ Fintype.card (DoubleTabTopSeed c (8 * c) b) :=
    two_mul_card_not_isKUnique_mul_le hc (by omega) hbound
  exact sum_probeCount_oddStride_of_whp_kWiseIndependent Good Good
    (fun _ hT₁ => isKWiseIndependentHash_doubleTabHash_of_isKUnique hU hT₁)
    (fun _ hT₂ => isKWiseIndependentHash_doubleTabHash_of_isKUnique hU hT₂)
    hwhp hwhp hM hload hw4 hrep hdom u

/-- **Expected Probe-Count Bound for Double Tabulation Odd-Stride Double Hashing under Explicit Code
Bound**: under the hypotheses of `sum_probeCount_oddStride_doubleTab_of_codeBound_le`, the expected
probe count of `u` under `PMF.uniformOfFintype (DoubleTabOddStrideSeed c b M)` is at most `3`. -/
theorem expect_probeCount_oddStride_doubleTab_of_codeBound_le
    {c b U M n_max : ℕ}
    (hc : 1 ≤ c) (hU : U ≤ 2 ^ (c * b))
    (hM : 1 ≤ M) (hload : 32 * max n_max 4 ≤ 2 ^ M)
    (hw4 : 2 * (2 * maxProbeCutoff n_max) ^ 4 ≤ 2 ^ M)
    (hbound : 2 * (n_max + 1) *
      doubleTabCodeBound c (8 * c) 4 (2 * maxProbeCutoff n_max + 1) ≤ 2 ^ (3 * b))
    {s : Dictionary.State U}
    {T : DoubleTabOddStrideSeed c b M → Table U (2 ^ M)}
    (hrep : ∀ θ, OrderedTableRep (doubleTabOddStridePerm c b U M θ) s (T θ))
    (hdom : (Dictionary.dom s).card ≤ n_max) (u : Fin U) :
    (∑' θ : DoubleTabOddStrideSeed c b M,
      PMF.uniformOfFintype (DoubleTabOddStrideSeed c b M) θ *
        (probeCount (T θ) u (doubleTabOddStridePerm c b U M θ u) : ℝ≥0∞)) ≤ 3 :=
  PMF.tsum_uniformOfFintype_le_of_sum_le
    (sum_probeCount_oddStride_doubleTab_of_codeBound_le hc hU hM hload hw4 hbound hrep hdom u)

/-- Canonical Double Tabulation seed space for odd-stride double hashing at polynomial universe
exponent `c_exp`, capacity `n_max`, and table bit-width `M`. -/
abbrev DoubleHashSeed (c_exp n_max M : ℕ) : Type :=
  DoubleTabOddStrideSeed (2 * max c_exp 1) ((1 + Nat.clog 2 (max n_max 4)) / 2) M

/-- Canonical Double Tabulation odd-stride permutation family at polynomial universe exponent
`c_exp`, capacity `n_max`, universe size `U`, and table bit-width `M`. -/
@[expose] noncomputable def doubleHashOddStridePerm (c_exp n_max U M : ℕ) :
    DoubleHashSeed c_exp n_max M → Fin U → Equiv.Perm (Fin (2 ^ M)) :=
  doubleTabOddStridePerm (2 * max c_exp 1) ((1 + Nat.clog 2 (max n_max 4)) / 2) U M

/-- **Summed Probe-Count Bound for Double Tabulation Odd-Stride Double Hashing above
`doubleTabThreshold c_exp` (`[Thorup2013]`, Theorem 1(a) & `[SchmidtSiegel1990]`, Theorem 1)**:
whenever `doubleTabThreshold c_exp ≤ n_max`, `U ≤ max n_max 4 ^ c_exp`, and
`32 * max n_max 4 ≤ 2 ^ M`, the sum of `probeCount` over all seeds in
`DoubleHashSeed c_exp n_max M` is at most `3` times the total number of seeds. -/
theorem sum_probeCount_oddStride_doubleTab_le
    {c_exp n_max U M : ℕ}
    (hge : doubleTabThreshold c_exp ≤ n_max)
    (hU : U ≤ max n_max 4 ^ c_exp) (hm : 32 * max n_max 4 ≤ 2 ^ M)
    {s : Dictionary.State U}
    {T : DoubleHashSeed c_exp n_max M → Table U (2 ^ M)}
    (hrep : ∀ θ, OrderedTableRep (doubleHashOddStridePerm c_exp n_max U M θ) s (T θ))
    (hdom : (Dictionary.dom s).card ≤ n_max) (u : Fin U) :
    (∑ θ : DoubleHashSeed c_exp n_max M,
      probeCount (T θ) u (doubleHashOddStridePerm c_exp n_max U M θ u)) ≤
      3 * Fintype.card (DoubleHashSeed c_exp n_max M) := by
  let c := 2 * max c_exp 1
  let b := (1 + Nat.clog 2 (max n_max 4)) / 2
  have hc1 : 1 ≤ c := by omega
  have hM : 1 ≤ M := by grind
  obtain ⟨hU_cb, hb_ge, hmax_le_2b⟩ := doubleTab_canonical_params hge hU
  have hb_min_def : doubleTabMinB c_exp = 4 * (24 * c + 8) ^ 2 := doubleTabMinB_eq c_exp
  have hb_64 : 64 ≤ b := ((by decide : 64 ≤ 4 * 8 ^ 2).trans
    (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (by omega) 2))).trans (hb_min_def ▸ hb_ge)
  have hcut_le : maxProbeCutoff n_max ≤ 2 * b + 4 := by grind [maxProbeCutoff]
  have h2cut_sq : 2 * maxProbeCutoff n_max + 1 ≤ b ^ 2 := by
    have := Nat.mul_le_mul_right b hb_64; rw [sq]; omega
  have h2n_le : 2 * (n_max + 1) ≤ 2 ^ (2 * b) * b ^ 2 :=
    (by omega : 2 * (n_max + 1) ≤ max n_max 4 * 4).trans
      (Nat.mul_le_mul hmax_le_2b (Nat.pow_le_pow_left (by omega : 2 ≤ b) 2))
  have hclog_le_M : Nat.clog 2 (max n_max 4) ≤ M :=
    (Nat.clog_le_iff_le_pow (by decide)).mpr (by omega)
  have hw4 : 2 * (2 * maxProbeCutoff n_max) ^ 4 ≤ 2 ^ M :=
    calc 2 * (2 * maxProbeCutoff n_max) ^ 4
        ≤ b * (b ^ 2) ^ 4 := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) 4)
      _ = b ^ 9 := by ring
      _ ≤ b ^ (24 * c + 8) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ 2 ^ b := Nat.pow_le_two_pow (by omega) (hb_min_def ▸ hb_ge)
      _ ≤ 2 ^ M := Nat.pow_le_pow_right (by decide) (by omega)
  exact sum_probeCount_oddStride_doubleTab_of_codeBound_le hc1 hU_cb hM hm hw4
    (mul_doubleTabCodeBound_le hb_ge h2cut_sq h2n_le) hrep hdom u

/-- **`O(1)` Expected Probes (`≤ 3`) for Double Tabulation Odd-Stride Double Hashing above
`doubleTabThreshold c_exp` (`[Thorup2013]`, Theorem 1(a) & `[SchmidtSiegel1990]`, Theorem 1)**:
whenever `doubleTabThreshold c_exp ≤ n_max`, `U ≤ max n_max 4 ^ c_exp`, and
`32 * max n_max 4 ≤ 2 ^ M`, the expected probe count of `u` under
`PMF.uniformOfFintype (DoubleHashSeed c_exp n_max M)` is at most `3`. -/
theorem expect_probeCount_oddStride_doubleTab_le
    {c_exp n_max U M : ℕ}
    (hge : doubleTabThreshold c_exp ≤ n_max)
    (hU : U ≤ max n_max 4 ^ c_exp) (hm : 32 * max n_max 4 ≤ 2 ^ M)
    {s : Dictionary.State U}
    {T : DoubleHashSeed c_exp n_max M → Table U (2 ^ M)}
    (hrep : ∀ θ, OrderedTableRep (doubleHashOddStridePerm c_exp n_max U M θ) s (T θ))
    (hdom : (Dictionary.dom s).card ≤ n_max) (u : Fin U) :
    (∑' θ : DoubleHashSeed c_exp n_max M,
      PMF.uniformOfFintype (DoubleHashSeed c_exp n_max M) θ *
        (probeCount (T θ) u (doubleHashOddStridePerm c_exp n_max U M θ u) : ℝ≥0∞)) ≤ 3 :=
  PMF.tsum_uniformOfFintype_le_of_sum_le
    (sum_probeCount_oddStride_doubleTab_le hge hU hm hrep hdom u)

/-- **`O_{c_exp}(1)` Expected Probe-Count Bound without a Threshold on `n_max : ℕ`**:
whenever `U ≤ max n_max 4 ^ c_exp` and `32 * max n_max 4 ≤ 2 ^ M`, combining the deterministic
full-cycle pigeonhole bound `probeCount ≤ n_max + 1 ≤ doubleTabThreshold c_exp` for
`n_max < doubleTabThreshold c_exp` with the Double Tabulation bound `≤ 3` for
`doubleTabThreshold c_exp ≤ n_max` yields expected probe count at most
`max (doubleTabThreshold c_exp : ℝ≥0∞) 3 = doubleTabThreshold c_exp` for every `n_max : ℕ`. Below
the threshold the bound uses no independence property of Double Tabulation. -/
theorem expect_probeCount_oddStride_unconditional_le
    {c_exp n_max U M : ℕ}
    (hU : U ≤ max n_max 4 ^ c_exp) (hm : 32 * max n_max 4 ≤ 2 ^ M)
    {s : Dictionary.State U}
    {T : DoubleHashSeed c_exp n_max M → Table U (2 ^ M)}
    (hrep : ∀ θ, OrderedTableRep (doubleHashOddStridePerm c_exp n_max U M θ) s (T θ))
    (hdom : (Dictionary.dom s).card ≤ n_max) (u : Fin U) :
    (∑' θ : DoubleHashSeed c_exp n_max M,
      PMF.uniformOfFintype (DoubleHashSeed c_exp n_max M) θ *
        (probeCount (T θ) u (doubleHashOddStridePerm c_exp n_max U M θ u) : ℝ≥0∞)) ≤
      max (doubleTabThreshold c_exp : ℝ≥0∞) 3 := by
  by_cases hge : doubleTabThreshold c_exp ≤ n_max
  · exact (expect_probeCount_oddStride_doubleTab_le hge hU hm hrep hdom u).trans (le_max_right _ 3)
  · exact ((expect_probeCount_le_add_one (fun θ => (hrep θ).toTableRep) hdom u).trans
      (mod_cast (by omega : n_max + 1 ≤ doubleTabThreshold c_exp))).trans (le_max_left _ 3)

end Cslib.DataStructure.Dictionary.DoubleHashing
