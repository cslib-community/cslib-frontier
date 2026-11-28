/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Formula
public import CslibFrontier.Computability.Communication.NOF.Discrepancy
public import CslibFrontier.Probability.PMF
import CslibFrontier.Computability.Communication.NOF.GeneralizedInnerProduct
import CslibFrontier.Foundations.Combinatorics.Hoeffding
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Read-`r` and fan-in-two formula compilation to multiparty NOF protocols

Every fan-in-two Boolean formula `F : Formula σ n` in which each variable appears at most `r` times
(`Formula.ReadAtMost r`) compiles to a low-depth deterministic `(r + 1)`-party number-on-forehead
(`NOF.Protocol`) protocol on balanced disjoint blocks of variables, yielding `Ω(n log n)` leaf-size
lower bounds for general fan-in-two Boolean formulas from balanced multiparty `NOF` discrepancy
(`Cslib.Communication.NOF.discrepancy`) as well as unconditionally via Hoeffding's inequality.

The development combines four ingredients:

1. **Exact Hall balance theorem** (`exists_nof_partition_of_bag_card_le`,
   `exists_disjoint_blocks_avoiding_bags`). Given `r + 1` bags `W_0, …, W_r ⊆ Fin n` such that
   every variable `i` lies in at most `r` bags and each bag has size at most `(r * n) / (r + 1)`,
   Hall's marriage theorem assigns every variable `i` to a player `owner i` with
   `i ∉ W_{owner i}` and guarantees every player at least `n / (r * (r + 1))` variables (tight for
   every `r ≥ 1`).

2. **Bottom-up binary-tree chopping and greedy bag packing** (`exists_nof_protocol_of_readAtMost`,
   `exists_nof_protocol_of_formula`). Chopping deepest subtrees exceeding leaf budget `B ≥ 1`
   decomposes `F` into `d ≤ F.leafSize / (B + 1)` subtrees of leaf weight in `[B + 1, 2 B]` plus a
   residual root of weight `≤ 2 B`, communicating `≤ F.leafSize / (B + 1) + 1` bits. Greedily
   assigning each piece to the lightest of `r + 1` bags keeps every bag below
   `(F.leafSize + 2 r B) / (r + 1)`.

3. **General fan-in-two Boolean formulas and balanced NOF discrepancy**
   (`exists_nof_protocol_of_formula`, `one_le_two_pow_mul_nof_discrepancy_of_formula`,
   `two_mul_le_two_pow_mul_nof_discrepancy_of_formula`,
   `mul_log_le_leafSize_of_balanced_discrepancy`). For an *arbitrary* fan-in-two formula `F` over
   any signature `σ` and Boolean interpretation `I`, setting `r = 4 * F.leafSize / n + 1` leaves at
   least `(3 n + 1) / 4` inputs read at most `r` times, while chopping at `B = n / 8` compiles `F`
   to an `(r + 1)`-party NOF protocol of **`≤ 2 r + 1` (`O(r)`) bits** on pairwise disjoint blocks
   of size `n / (4 r)`. Conditionally on the Babai–Nisan–Szegedy cube discrepancy bound across the
   balanced regime `1 ≤ r`, `4 r + 6 ≤ log₂ n` (`q = n / (4 r)`), this forces
   `n * (Nat.log 2 n - 12) ≤ 16 * F.leafSize`.

4. **Probabilistic existence and unconditional `Ω(n log n)` formula lower bound**
   (`exists_balanced_nof_discrepancy`, `exists_function_mul_log_le_leafSize`). Applying Hoeffding's
   inequality (`Cslib.BitString.card_filter_le_abs_sum_mul_signVal_le`) and a union bound over all
   balanced block tuples and cylinder intersections establishes that for every `n`, a Boolean
   function `f : (Fin n → Bool) → Bool` satisfies the balanced BNS cube discrepancy bound and
   therefore requires `n * (Nat.log 2 n - 12) ≤ 16 * F.leafSize` for every fan-in-two Boolean
   formula over any signature `σ`.

## Main definitions

* `Cslib.Circuits.Formula.ReadAtMost`: every input variable appears at most `r` times as a leaf.
* `Cslib.Circuits.Frontier.embedBlocks`: embeds multiparty block inputs `∀ j, X j → U` into
  `Fin n → U` using a background assignment outside `⋃ j, X j`.

## Main results

* `Cslib.Circuits.Frontier.exists_nof_partition_of_bag_card_le`: exact `n / (r * (r + 1))` Hall
  balance theorem for `(r + 1)`-party NOF input assignment.
* `Cslib.Circuits.Frontier.exists_nof_protocol_of_readAtMost`: read-`r` fan-in-two Boolean formula
  to `(r + 1)`-party `NOF.Protocol` compiler.
* `Cslib.Circuits.Frontier.exists_nof_protocol_of_formula`: general fan-in-two Boolean formula
  compilation to a `(2 r + 1)`-bit `(r + 1)`-party `NOF.Protocol` at `r = 4 * F.leafSize / n + 1`.
* `Cslib.Circuits.Frontier.one_le_two_pow_mul_nof_discrepancy_of_formula`,
  `Cslib.Circuits.Frontier.two_mul_le_two_pow_mul_nof_discrepancy_of_formula`: exact and
  distributional discrepancy bounds wired into `Cslib.Communication.NOF.discrepancy`.
* `Cslib.Circuits.Frontier.mul_log_le_leafSize_of_balanced_discrepancy`: conditional `Ω(n log n)`
  fan-in-two Boolean formula leaf-size lower bound from balanced NOF cube discrepancy.
* `Cslib.Circuits.Frontier.exists_balanced_nof_discrepancy`,
  `Cslib.Circuits.Frontier.exists_function_mul_log_le_leafSize`: probabilistic existence of balanced
  NOF-hard functions and unconditional `Ω(n log n)` fan-in-two Boolean formula lower bound.

The exact `n / (r * (r + 1))` Hall balance theorem, the greedy `(r + 1)`-bag subtree-chopping
compiler for arbitrary fan-in-two Boolean formulas, and the balanced NOF cube discrepancy reduction
and Hoeffding existence bound over arbitrary basis signatures are original to this library, building
on multiparty NOF discrepancy [ChandraFurstLipton1983], [BabaiNisanSzegedy1992], [Jukna2012],
Hoeffding's inequality [Hoeffding1963], and classical formula lower bounds [Khrapchenko1971].

## References

* [L. Babai, N. Nisan and M. Szegedy, *Multiparty protocols, pseudorandom generators for logspace,
  and time-space trade-offs*][BabaiNisanSzegedy1992]
* [A. K. Chandra, M. L. Furst and R. J. Lipton, *Multi-party protocols*][ChandraFurstLipton1983]
* [W. Hoeffding, *Probability inequalities for sums of bounded random variables*][Hoeffding1963]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
* [V. M. Khrapchenko, *Complexity of the realization of a linear function in the class of
  Π-schemes*][Khrapchenko1971]
-/

public section

namespace Cslib.Circuits.Formula

/-- Every input variable `i : Fin n` appears at most `r` times among the leaves of `F`. -/
@[expose] def ReadAtMost {σ : Signature} {n : ℕ} (r : ℕ) (F : Formula σ n) : Prop :=
  ∀ i : Fin n, F.leafSizeIn {i} ≤ r

/-- A read-`r` formula on `n` variables has at most `r * n` leaves. -/
theorem leafSize_le_of_readAtMost {σ : Signature} {n r : ℕ} {F : Formula σ n}
    (hF : F.ReadAtMost r) : F.leafSize ≤ r * n := by
  rw [← F.leafSizeIn_univ, ← F.sum_leafSizeIn_singleton]
  calc ∑ i : Fin n, F.leafSizeIn {i} ≤ ∑ _i : Fin n, r := Finset.sum_le_sum fun i _ => hF i
    _ = r * n := by simp [mul_comm]

end Cslib.Circuits.Formula

namespace Cslib.Circuits.Frontier

open Finset Cslib.Circuits Cslib.Communication Cslib.Probability

/-! ### Part 1: Exact Hall balance theorem for `(r + 1)`-party NOF partitions -/

/-- **Subset-restricted Hall balance.** Given a pool `L : Finset (Fin n)` of candidate inputs and
`r + 1` bags `bags : Fin (r + 1) → Finset (Fin n)` such that every `i ∈ L` belongs to at most `r`
bags and each bag contains at most `cap` elements of `L`, whenever `(r + 1) * q ≤ L.card` and
`cap + r * q ≤ L.card` there exist `r + 1` pairwise disjoint blocks `X j ⊆ L` of exact size `q`
with `Disjoint (X j) (bags j)` for every player `j`. -/
theorem exists_disjoint_blocks_avoiding_bags {n r cap q : ℕ} (L : Finset (Fin n))
    (bags : Fin (r + 1) → Finset (Fin n))
    (hread : ∀ i ∈ L, (Finset.univ.filter fun j : Fin (r + 1) => i ∈ bags j).card ≤ r)
    (hcap : ∀ j : Fin (r + 1), (L ∩ bags j).card ≤ cap)
    (hq_tot : (r + 1) * q ≤ L.card) (hq_cap : cap + r * q ≤ L.card) :
    ∃ X : Fin (r + 1) → Finset (Fin n),
      Pairwise (fun j₁ j₂ => Disjoint (X j₁) (X j₂)) ∧
      ∀ j : Fin (r + 1), X j ⊆ L ∧ (X j).card = q ∧ Disjoint (X j) (bags j) := by
  let avail : Fin (r + 1) × Fin q → Finset (Fin n) := fun p => L \ bags p.1
  have hhall : ∀ s : Finset (Fin (r + 1) × Fin q), s.card ≤ (s.biUnion avail).card := by
    intro s
    let J : Finset (Fin (r + 1)) := s.image Prod.fst
    have hs_sub : s ⊆ J ×ˢ (Finset.univ : Finset (Fin q)) := fun p hp =>
      Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp, Finset.mem_univ _⟩
    have hs_card : s.card ≤ J.card * q := by
      calc s.card ≤ (J ×ˢ (Finset.univ : Finset (Fin q))).card := Finset.card_le_card hs_sub
        _ = J.card * q := by simp
    rcases J.eq_empty_or_nonempty with hJ0 | ⟨j₀, hj₀⟩
    · simp [Finset.image_eq_empty.mp hJ0]
    · by_cases hJr : J.card ≤ r
      · obtain ⟨p₀, hp₀, rfl⟩ := Finset.mem_image.mp hj₀
        have hsub : L \ bags p₀.1 ⊆ s.biUnion avail := Finset.subset_biUnion_of_mem avail hp₀
        have hsdiff := Finset.card_sdiff_add_card_inter L (bags p₀.1)
        have hbag := hcap p₀.1
        have hge : r * q ≤ (L \ bags p₀.1).card := by omega
        exact hs_card.trans ((Nat.mul_le_mul_right q hJr).trans
          (hge.trans (Finset.card_le_card hsub)))
      · have hJcard : J.card ≤ r + 1 := by simpa [Fintype.card_fin] using Finset.card_le_univ J
        have hJu : J = Finset.univ := by
          apply Finset.eq_univ_of_card
          rw [Fintype.card_fin]
          omega
        have hL_sub : L ⊆ s.biUnion avail := by
          intro i hi
          have hlt : (Finset.univ.filter fun j : Fin (r + 1) => i ∈ bags j).card <
              (Finset.univ : Finset (Fin (r + 1))).card := by
            simpa using Nat.lt_succ_of_le (hread i hi)
          obtain ⟨j, -, hj_not⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
          have hjJ : j ∈ J := by simp [hJu]
          obtain ⟨p, hp, hpj⟩ := Finset.mem_image.mp hjJ
          refine Finset.mem_biUnion.mpr ⟨p, hp, ?_⟩
          simp only [avail, hpj, Finset.mem_sdiff]
          exact ⟨hi, fun hmem => hj_not (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hmem⟩)⟩
        calc s.card ≤ J.card * q := hs_card
          _ ≤ (r + 1) * q := Nat.mul_le_mul_right q hJcard
          _ ≤ L.card := hq_tot
          _ ≤ (s.biUnion avail).card := Finset.card_le_card hL_sub
  obtain ⟨f, hf_inj, hf_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' avail).mp hhall
  refine ⟨fun j => Finset.univ.image fun u : Fin q => f (j, u), ?_, ?_⟩
  · intro j₁ j₂ hne
    refine Finset.disjoint_left.mpr fun i hi₁ hi₂ => ?_
    obtain ⟨u₁, -, rfl⟩ := Finset.mem_image.mp hi₁
    obtain ⟨u₂, -, heq⟩ := Finset.mem_image.mp hi₂
    exact hne (congrArg Prod.fst (hf_inj heq.symm))
  · intro j
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hi
      exact (Finset.mem_sdiff.mp (hf_mem (j, u))).1
    · rw [Finset.card_image_of_injective _ fun u₁ u₂ h =>
        congrArg Prod.snd (hf_inj h), Finset.card_fin]
    · refine Finset.disjoint_left.mpr fun i hi hbag => ?_
      obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hi
      exact (Finset.mem_sdiff.mp (hf_mem (j, u))).2 hbag

/-- **Exact Hall balance theorem for `(r + 1)`-party NOF partitions**
(`min_j |X_j| ≥ n / (r(r+1))`). Given `1 ≤ r` and `r + 1` bags
`bags : Fin (r + 1) → Finset (Fin n)` such that every variable `i` belongs to at most `r` bags and
each bag has size at most `(r * n) / (r + 1)`, there exists a total assignment
`owner : Fin n → Fin (r + 1)` such that every variable avoids its owner's bag
(`i ∉ bags (owner i)`) and every player owns at least `n / (r * (r + 1))` variables. -/
theorem exists_nof_partition_of_bag_card_le {n r : ℕ} (hr : 1 ≤ r)
    (bags : Fin (r + 1) → Finset (Fin n))
    (hread : ∀ i : Fin n, (Finset.univ.filter fun j : Fin (r + 1) => i ∈ bags j).card ≤ r)
    (hcap : ∀ j : Fin (r + 1), (bags j).card ≤ (r * n) / (r + 1)) :
    ∃ owner : Fin n → Fin (r + 1),
      (∀ i : Fin n, i ∉ bags (owner i)) ∧
      ∀ j : Fin (r + 1),
        n / (r * (r + 1)) ≤ (Finset.univ.filter fun i : Fin n => owner i = j).card := by
  classical
  set q := n / (r * (r + 1))
  have hmul_q : r * (r + 1) * q ≤ n := Nat.mul_div_le n (r * (r + 1))
  have hq_tot : (r + 1) * q ≤ (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_fin]
    calc (r + 1) * q = 1 * ((r + 1) * q) := (one_mul _).symm
      _ ≤ r * ((r + 1) * q) := Nat.mul_le_mul_right _ hr
      _ = r * (r + 1) * q := (mul_assoc _ _ _).symm
      _ ≤ n := hmul_q
  have hq_cap : (r * n) / (r + 1) + r * q ≤ (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_fin]
    have h1 : r * n + (r * q) * (r + 1) ≤ (r + 1) * n := by nlinarith
    calc (r * n) / (r + 1) + r * q
        = (r * n + (r * q) * (r + 1)) / (r + 1) :=
          (Nat.add_mul_div_right (r * n) (r * q) (Nat.succ_pos r)).symm
      _ ≤ ((r + 1) * n) / (r + 1) := Nat.div_le_div_right h1
      _ = n := Nat.mul_div_right n (Nat.succ_pos r)
  obtain ⟨X, hdisj, hX⟩ := exists_disjoint_blocks_avoiding_bags Finset.univ bags
    (fun i _ => hread i) (fun j => by simpa using hcap j) hq_tot hq_cap
  have hexists_avoid : ∀ i : Fin n, ∃ j : Fin (r + 1), i ∉ bags j := fun i => by
    have hlt : (Finset.univ.filter fun j : Fin (r + 1) => i ∈ bags j).card <
        (Finset.univ : Finset (Fin (r + 1))).card := by
      simpa using Nat.lt_succ_of_le (hread i)
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    exact ⟨j, fun hmem => hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hmem⟩)⟩
  let owner (i : Fin n) : Fin (r + 1) :=
    if h : ∃ j, i ∈ X j then Classical.choose h else Classical.choose (hexists_avoid i)
  refine ⟨owner, fun i => ?_, fun j => ?_⟩
  · dsimp only [owner]
    split_ifs with h
    · exact Finset.disjoint_left.mp (hX (Classical.choose h)).2.2 (Classical.choose_spec h)
    · exact Classical.choose_spec (hexists_avoid i)
  · have hsub : X j ⊆ Finset.univ.filter (fun i : Fin n => owner i = j) := by
      intro i hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
      have hex : ∃ j', i ∈ X j' := ⟨j, hi⟩
      dsimp only [owner]
      rw [dite_eq_left_of_eq_true (eq_true hex)]
      by_contra hne
      exact Finset.disjoint_left.mp (hdisj hne) (Classical.choose_spec hex) hi
    calc q = (X j).card := ((hX j).2.1).symm
      _ ≤ (Finset.univ.filter fun i : Fin n => owner i = j).card := Finset.card_le_card hsub

/-! ### Part 2: Embedding multiparty block inputs and player views -/

/-- Embed multiparty block inputs `y : ∀ j : Fin k, X j → U` into `Fin n → U`, filling coordinates
outside `⋃ j, X j` from the background assignment `z` (selecting the block index via
`Classical.choose`; for pairwise disjoint `X`, use `embedBlocks_of_mem` and
`embedBlocks_of_notMem`). -/
noncomputable def embedBlocks {k n : ℕ} {U : Type*} (X : Fin k → Finset (Fin n)) (z : Fin n → U)
    (y : ∀ j : Fin k, X j → U) (i : Fin n) : U := by
  classical
  exact if h : ∃ j : Fin k, i ∈ X j then
    y (Classical.choose h) ⟨i, Classical.choose_spec h⟩
  else z i

/-- On `i ∈ X j` (for pairwise disjoint `X`), `embedBlocks X z y i` reads player `j`'s input. -/
theorem embedBlocks_of_mem {k n : ℕ} {U : Type*} {X : Fin k → Finset (Fin n)}
    (hdisj : Pairwise fun j₁ j₂ => Disjoint (X j₁) (X j₂)) (z : Fin n → U)
    (y : ∀ j : Fin k, X j → U) {j : Fin k} {i : Fin n} (hi : i ∈ X j) :
    embedBlocks X z y i = y j ⟨i, hi⟩ := by
  classical
  have hex : ∃ j' : Fin k, i ∈ X j' := ⟨j, hi⟩
  unfold embedBlocks
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  have hj_eq : Classical.choose hex = j := by
    by_contra hne
    exact Finset.disjoint_left.mp (hdisj hne) (Classical.choose_spec hex) hi
  cases hj_eq
  rfl

/-- Outside `⋃ j, X j`, `embedBlocks X z y i` equals the background assignment `z i`. -/
theorem embedBlocks_of_notMem {k n : ℕ} {U : Type*} {X : Fin k → Finset (Fin n)} (z : Fin n → U)
    (y : ∀ j : Fin k, X j → U) {i : Fin n} (hnot : ∀ j : Fin k, i ∉ X j) :
    embedBlocks X z y i = z i := by
  classical
  have hne : ¬∃ j : Fin k, i ∈ X j := fun ⟨j, hj⟩ => hnot j hj
  unfold embedBlocks
  exact dite_eq_right_of_eq_false (eq_false hne)

/-- Player `j` reconstructs every coordinate outside `X j` from their NOF view `v` and the public
background `z`. -/
private noncomputable def reconstructFromView {k n : ℕ} {U : Type*} (X : Fin k → Finset (Fin n))
    (z : Fin n → U) (j : Fin k) (v : NOF.View (fun j' => X j' → U) j) (i : Fin n) : U := by
  classical
  exact if h : ∃ j' : {j' : Fin k // j' ≠ j}, i ∈ X j'.val then
    v (Classical.choose h) ⟨i, Classical.choose_spec h⟩
  else z i

private theorem reconstructFromView_eq_embedBlocks {k n : ℕ} {U : Type*}
    {X : Fin k → Finset (Fin n)} (hdisj : Pairwise fun j₁ j₂ => Disjoint (X j₁) (X j₂))
    (z : Fin n → U) (j : Fin k) (y : ∀ j' : Fin k, X j' → U) {i : Fin n} (hi : i ∉ X j) :
    reconstructFromView X z j (NOF.view j y) i = embedBlocks X z y i := by
  classical
  by_cases hex : ∃ j₀ : Fin k, i ∈ X j₀
  · obtain ⟨j₀, hj₀⟩ := hex
    have hne : j₀ ≠ j := fun heq => hi (heq ▸ hj₀)
    have hex' : ∃ j' : {j' : Fin k // j' ≠ j}, i ∈ X j'.val := ⟨⟨j₀, hne⟩, hj₀⟩
    rw [embedBlocks_of_mem hdisj z y hj₀]
    unfold reconstructFromView
    rw [dite_eq_left_of_eq_true (eq_true hex')]
    have hview : ∀ (c : {j' : Fin k // j' ≠ j}) (hc : i ∈ X c.val),
        NOF.view j y c ⟨i, hc⟩ = y j₀ ⟨i, hj₀⟩ := by
      rintro ⟨cval, hcne⟩ hc
      have hval : cval = j₀ := by
        by_contra hne'
        exact Finset.disjoint_left.mp (hdisj hne') hc hj₀
      subst hval
      rfl
    exact hview (Classical.choose hex') (Classical.choose_spec hex')
  · have hnot : ∀ j₀ : Fin k, i ∉ X j₀ := fun j₀ hj₀ => hex ⟨j₀, hj₀⟩
    rw [embedBlocks_of_notMem z y hnot]
    have hne' : ¬∃ j' : {j' : Fin k // j' ≠ j}, i ∈ X j'.val := fun ⟨j', hj'⟩ => hnot j'.val hj'
    unfold reconstructFromView
    exact dite_eq_right_of_eq_false (eq_false hne')

/-! ### Part 3: Bottom-up binary formula chopping and greedy bag compilation -/

section Chopping

/-- Auxiliary Boolean formula tree over `Fin n` original inputs and `Fin m` previously spoken
blackboard bits (which contribute `0` original-input leaves). -/
private inductive ChopTree (n : ℕ) : ℕ → Type where
  | input {m : ℕ} (i : Fin n) : ChopTree n m
  | prev {m : ℕ} (t : Fin m) : ChopTree n m
  | node {m : ℕ} (a : ℕ) (op : (Fin a → Bool) → Bool) (args : Fin a → ChopTree n m) :
      ChopTree n m

namespace ChopTree

private def eval {n m : ℕ} : ChopTree n m → (Fin n → Bool) → (Fin m → Bool) → Bool
  | input i, x, _ => x i
  | prev t, _, b => b t
  | node _ op args, x, b => op fun s => (args s).eval x b

private def leafAt {n m : ℕ} (i : Fin n) : ChopTree n m → ℕ
  | input i' => if i' = i then 1 else 0
  | prev _ => 0
  | node _ _ args => ∑ s, (args s).leafAt i

private def leafCount {n m : ℕ} : ChopTree n m → ℕ
  | input _ => 1
  | prev _ => 0
  | node _ _ args => ∑ s, (args s).leafCount

private def FanIn2 {n m : ℕ} : ChopTree n m → Prop
  | input _ => True
  | prev _ => True
  | node a _ args => a ≤ 2 ∧ ∀ s, (args s).FanIn2

private theorem eval_congr_of_leafAt_eq_zero {n m : ℕ} (T : ChopTree n m) {x x' : Fin n → Bool}
    (b : Fin m → Bool) (hx : ∀ i : Fin n, T.leafAt i ≠ 0 → x i = x' i) :
    T.eval x b = T.eval x' b := by
  induction T with
  | input i => exact hx i (by simp [leafAt])
  | prev _ => rfl
  | node a op args ih =>
    simp only [eval]
    congr 1 with s : 1
    refine ih s fun i hi => hx i ?_
    simp only [leafAt]
    intro hsum
    exact hi ((Finset.sum_eq_zero_iff.mp hsum) s (Finset.mem_univ s))

private def ofFormula {σ : Signature} {n : ℕ} (I : Interpretation σ Bool) :
    Formula σ n → ChopTree n 0
  | .input i => .input i
  | .gate op args => .node (σ.Arity op) (I op) fun s => ofFormula I (args s)

private theorem eval_ofFormula {σ : Signature} {n : ℕ} (I : Interpretation σ Bool)
    (F : Formula σ n) (x : Fin n → Bool) (b : Fin 0 → Bool) :
    (ofFormula I F).eval x b = F.eval I x := by
  induction F with
  | input i => rfl
  | gate op args ih =>
    simp only [ofFormula, eval, Formula.eval_gate]
    congr 1 with s : 1
    exact ih s

private theorem leafCount_ofFormula {σ : Signature} {n : ℕ} (I : Interpretation σ Bool)
    (F : Formula σ n) : (ofFormula I F).leafCount = F.leafSize := by
  induction F with
  | input _ => rfl
  | gate _ _ ih => simp [ofFormula, leafCount, ih]

private theorem leafAt_ofFormula {σ : Signature} {n : ℕ} (I : Interpretation σ Bool)
    (F : Formula σ n) (i : Fin n) : (ofFormula I F).leafAt i = F.leafSizeIn {i} := by
  induction F with
  | input j => simp [ofFormula, leafAt]
  | gate _ _ ih => simp [ofFormula, leafAt, ih]

private theorem fanIn2_ofFormula {σ : Signature} {n : ℕ} (I : Interpretation σ Bool)
    {F : Formula σ n} (hF : F.FanInAtMost 2) : (ofFormula I F).FanIn2 := by
  induction F with
  | input _ => trivial
  | gate _ _ ih => exact ⟨hF.1, fun s => ih s (hF.2 s)⟩

private def liftPrev {n m : ℕ} : ChopTree n m → ChopTree n (m + 1)
  | input i => input i
  | prev t => prev t.castSucc
  | node a op args => node a op fun s => (args s).liftPrev

private theorem eval_liftPrev {n m : ℕ} (T : ChopTree n m) (x : Fin n → Bool) (b : Fin m → Bool)
    (bit : Bool) : T.liftPrev.eval x (Fin.snoc b bit) = T.eval x b := by
  induction T with
  | input _ => rfl
  | prev t => simp [liftPrev, eval]
  | node _ _ _ ih =>
    simp only [liftPrev, eval]
    congr 1 with s : 1
    exact ih s

private theorem leafCount_liftPrev {n m : ℕ} (T : ChopTree n m) :
    T.liftPrev.leafCount = T.leafCount := by
  induction T with
  | input _ => rfl
  | prev _ => rfl
  | node _ _ _ ih => simp [liftPrev, leafCount, ih]

private theorem leafAt_liftPrev {n m : ℕ} (T : ChopTree n m) (i : Fin n) :
    T.liftPrev.leafAt i = T.leafAt i := by
  induction T with
  | input _ => rfl
  | prev _ => rfl
  | node _ _ _ ih => simp [liftPrev, leafAt, ih]

private theorem fanIn2_liftPrev {n m : ℕ} {T : ChopTree n m} (hT : T.FanIn2) :
    T.liftPrev.FanIn2 := by
  induction T with
  | input _ => trivial
  | prev _ => trivial
  | node _ _ _ ih => exact ⟨hT.1, fun s => ih s (hT.2 s)⟩

/-- Pluck a deepest subtree `K` with `B < K.leafCount ≤ 2 * B` from `T`, replacing `K` by
`prev (Fin.last m)`. -/
private noncomputable def pluck {n m B : ℕ} (hB : 1 ≤ B) (T : ChopTree n m) (hfan : T.FanIn2)
    (hgt : B < T.leafCount) :
    {KC : ChopTree n m × ChopTree n (m + 1) //
      KC.1.FanIn2 ∧ KC.2.FanIn2 ∧ B < KC.1.leafCount ∧ KC.1.leafCount ≤ 2 * B ∧
      KC.2.leafCount + KC.1.leafCount = T.leafCount ∧
      (∀ i : Fin n, KC.2.leafAt i + KC.1.leafAt i = T.leafAt i) ∧
      ∀ (x : Fin n → Bool) (b : Fin m → Bool),
        KC.2.eval x (Fin.snoc b (KC.1.eval x b)) = T.eval x b} := by
  classical
  match T with
  | input _ =>
    exfalso
    simp only [leafCount] at hgt
    omega
  | prev _ =>
    exfalso
    simp only [leafCount] at hgt
    omega
  | node a op args =>
    obtain ⟨ha, hargs⟩ := hfan
    by_cases hex : ∃ s : Fin a, B < (args s).leafCount
    · let s₀ : Fin a := Classical.choose hex
      have hs₀ : B < (args s₀).leafCount := Classical.choose_spec hex
      let sub := pluck hB (args s₀) (hargs s₀) hs₀
      let K := sub.val.1
      let C₀ := sub.val.2
      obtain ⟨hK_fan, hC₀_fan, hK_gt, hK_le, hsum_cnt, hsum_at, heval⟩ := sub.property
      let args' : Fin a → ChopTree n (m + 1) :=
        fun s => if s = s₀ then C₀ else (args s).liftPrev
      refine ⟨(K, node a op args'), hK_fan, ⟨ha, fun s => ?_⟩, hK_gt, hK_le, ?_, ?_, ?_⟩
      · dsimp only [args']
        split_ifs with h
        · exact hC₀_fan
        · exact fanIn2_liftPrev (hargs s)
      · simp only [leafCount]
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ s₀),
          ← Finset.sum_erase_add _ (fun s => (args s).leafCount) (Finset.mem_univ s₀)]
        have h₀ : (args' s₀).leafCount = C₀.leafCount := by simp [args']
        have hrest : ∑ s ∈ Finset.univ.erase s₀, (args' s).leafCount =
            ∑ s ∈ Finset.univ.erase s₀, (args s).leafCount := by
          refine Finset.sum_congr rfl fun s hs => ?_
          have hne : s ≠ s₀ := (Finset.mem_erase.mp hs).1
          simp [args', hne, leafCount_liftPrev]
        rw [h₀, hrest, add_assoc, hsum_cnt]
      · intro i
        simp only [leafAt]
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ s₀),
          ← Finset.sum_erase_add _ (fun s => (args s).leafAt i) (Finset.mem_univ s₀)]
        have h₀ : (args' s₀).leafAt i = C₀.leafAt i := by simp [args']
        have hrest : ∑ s ∈ Finset.univ.erase s₀, (args' s).leafAt i =
            ∑ s ∈ Finset.univ.erase s₀, (args s).leafAt i := by
          refine Finset.sum_congr rfl fun s hs => ?_
          have hne : s ≠ s₀ := (Finset.mem_erase.mp hs).1
          simp [args', hne, leafAt_liftPrev]
        rw [h₀, hrest, add_assoc, hsum_at i]
      · intro x b
        simp only [eval]
        congr 1 with s : 1
        dsimp only [args']
        by_cases h : s = s₀
        · subst h
          simpa using heval x b
        · simp [h, eval_liftPrev]
    · have hall : ∀ s : Fin a, (args s).leafCount ≤ B := fun s => not_lt.mp fun hs => hex ⟨s, hs⟩
      have hle2B : (node a op args).leafCount ≤ 2 * B := by
        simp only [leafCount]
        calc ∑ s : Fin a, (args s).leafCount
            ≤ ∑ _s : Fin a, B := Finset.sum_le_sum fun s _ => hall s
          _ = a * B := by simp
          _ ≤ 2 * B := Nat.mul_le_mul_right B ha
      refine ⟨(node a op args, prev (Fin.last m)), ⟨ha, hargs⟩, trivial, hgt, hle2B, ?_, ?_, ?_⟩
      · simp [leafCount]
      · intro i; simp [leafAt]
      · intro x b; simp [eval]

end ChopTree

/-- Telescope of chopped subtrees evaluated bottom-up on a shared blackboard. -/
private inductive ChopSeq (n : ℕ) : ℕ → Type where
  | root {m : ℕ} (T : ChopTree n m) : ChopSeq n m
  | step {m : ℕ} (K : ChopTree n m) (rest : ChopSeq n (m + 1)) : ChopSeq n m

namespace ChopSeq

private def eval {n m : ℕ} : ChopSeq n m → (Fin n → Bool) → (Fin m → Bool) → Bool
  | root T, x, b => T.eval x b
  | step K rest, x, b => rest.eval x (Fin.snoc b (K.eval x b))

private def steps {n m : ℕ} : ChopSeq n m → ℕ
  | root _ => 1
  | step _ rest => rest.steps + 1

private def totalLeaves {n m : ℕ} : ChopSeq n m → ℕ
  | root T => T.leafCount
  | step K rest => K.leafCount + rest.totalLeaves

private def totalLeafAt {n m : ℕ} (i : Fin n) : ChopSeq n m → ℕ
  | root T => T.leafAt i
  | step K rest => K.leafAt i + rest.totalLeafAt i

private def AllBounded (W : ℕ) {n m : ℕ} : ChopSeq n m → Prop
  | root T => T.leafCount ≤ W
  | step K rest => K.leafCount ≤ W ∧ rest.AllBounded W

private noncomputable def chopAux {n : ℕ} (B : ℕ) (hB : 1 ≤ B) :
    ∀ (fuel : ℕ) {m : ℕ} (T : ChopTree n m), T.FanIn2 → T.leafCount ≤ fuel → ChopSeq n m
  | 0, _, T, _, _ => root T
  | fuel + 1, _, T, hfan, hfuel =>
    if hle : T.leafCount ≤ 2 * B then root T
    else
      let res := T.pluck hB hfan (by omega)
      step res.val.1 (chopAux B hB fuel res.val.2 res.property.2.1 (by
        have hgt := res.property.2.2.1
        have hsum := res.property.2.2.2.2.1
        omega))

private theorem chopAux_spec {n B : ℕ} (hB : 1 ≤ B) (fuel : ℕ) {m : ℕ} (T : ChopTree n m)
    (hfan : T.FanIn2) (hfuel : T.leafCount ≤ fuel) :
    (chopAux B hB fuel T hfan hfuel).AllBounded (2 * B) ∧
    ((chopAux B hB fuel T hfan hfuel).steps - 1) * (B + 1) ≤ T.leafCount ∧
    (chopAux B hB fuel T hfan hfuel).totalLeaves = T.leafCount ∧
    (∀ i : Fin n, (chopAux B hB fuel T hfan hfuel).totalLeafAt i = T.leafAt i) ∧
    ∀ (x : Fin n → Bool) (b : Fin m → Bool),
      (chopAux B hB fuel T hfan hfuel).eval x b = T.eval x b := by
  fun_induction chopAux B hB fuel T hfan hfuel with
  | case1 T _ hfuel => -- fuel exhausted
    have h0 : T.leafCount = 0 := Nat.le_zero.mp hfuel
    refine ⟨?_, ?_, rfl, fun _ => rfl, fun _ _ => rfl⟩
    · simp [AllBounded, h0]
    · simp [steps]
  | case2 fuel T hfan hfuel hle => -- leafCount ≤ 2 * B: a single root
    refine ⟨hle, ?_, rfl, fun _ => rfl, fun _ _ => rfl⟩
    simp [steps]
  | case3 fuel T hfan hfuel hle res ih => -- pluck a piece, recurse on the rest
    obtain ⟨hK_fan, hC_fan, hK_gt, hK_le, hsum_cnt, hsum_at, heval⟩ := res.property
    have hC_fuel : res.val.2.leafCount ≤ fuel := by omega
    obtain ⟨hbd, hsteps, htot, hat, hev⟩ := ih
    have hpos : 1 ≤ (chopAux B hB fuel res.val.2 hC_fan hC_fuel).steps := by
      cases chopAux B hB fuel res.val.2 hC_fan hC_fuel <;> simp [steps]
    refine ⟨⟨hK_le, hbd⟩, ?_, ?_, ?_, ?_⟩
    · dsimp only [steps]
      rw [Nat.add_sub_cancel]
      have hstep1 : ((chopAux B hB fuel res.val.2 hC_fan hC_fuel).steps - 1 + 1) =
          (chopAux B hB fuel res.val.2 hC_fan hC_fuel).steps := by omega
      rw [← hstep1, Nat.succ_mul]
      omega
    · dsimp only [totalLeaves]
      rw [htot]
      exact (add_comm _ _).trans hsum_cnt
    · intro i
      dsimp only [totalLeafAt]
      rw [hat i]
      exact (add_comm _ _).trans (hsum_at i)
    · intro x b
      dsimp only [eval]
      exact (hev x _).trans (heval x b)

/-- Pick the player in `Fin (r + 1)` with minimum current load. -/
private noncomputable def minBag {r : ℕ} (load : Fin (r + 1) → ℕ) : Fin (r + 1) :=
  Classical.choose (Finset.exists_min_image Finset.univ load ⟨0, Finset.mem_univ 0⟩)

private theorem minBag_le {r : ℕ} (load : Fin (r + 1) → ℕ) (j : Fin (r + 1)) :
    load (minBag load) ≤ load j :=
  (Classical.choose_spec (Finset.exists_min_image Finset.univ load ⟨0, Finset.mem_univ 0⟩)).2 j
    (Finset.mem_univ j)

private theorem mul_minBag_le_sum {r : ℕ} (load : Fin (r + 1) → ℕ) :
    (r + 1) * load (minBag load) ≤ ∑ j : Fin (r + 1), load j := by
  calc (r + 1) * load (minBag load)
      = ∑ _j : Fin (r + 1), load (minBag load) := by simp
    _ ≤ ∑ j : Fin (r + 1), load j := Finset.sum_le_sum fun j _ => minBag_le load j

/-- Greedily assign each tree in `ChopSeq` to the minimum-load player in `Fin (r + 1)`, returning
the accumulated per-player variable footprints `Fin (r + 1) → Fin n → ℕ`. -/
private noncomputable def bagLeafWeights {n r : ℕ} :
    ∀ {m : ℕ}, (Fin (r + 1) → ℕ) → ChopSeq n m → Fin (r + 1) → Fin n → ℕ
  | _, load, root T =>
    let j₀ := minBag load
    fun j i => if j = j₀ then T.leafAt i else 0
  | _, load, step K rest =>
    let j₀ := minBag load
    let restW := bagLeafWeights (Function.update load j₀ (load j₀ + K.leafCount)) rest
    fun j i => (if j = j₀ then K.leafAt i else 0) + restW j i

/-- Final total load per bag under greedy assignment. -/
private noncomputable def bagFinalLoads {n r : ℕ} :
    ∀ {m : ℕ}, (Fin (r + 1) → ℕ) → ChopSeq n m → Fin (r + 1) → ℕ
  | _, load, root T =>
    let j₀ := minBag load
    Function.update load j₀ (load j₀ + T.leafCount)
  | _, load, step K rest =>
    let j₀ := minBag load
    bagFinalLoads (Function.update load j₀ (load j₀ + K.leafCount)) rest

private theorem sum_bagLeafWeights_eq {n r m : ℕ} (load : Fin (r + 1) → ℕ) (S : ChopSeq n m)
    (i : Fin n) : (∑ j : Fin (r + 1), bagLeafWeights load S j i) = S.totalLeafAt i := by
  induction S generalizing load with
  | root T =>
    simp [bagLeafWeights, totalLeafAt]
  | step K rest ih =>
    simp only [bagLeafWeights, Finset.sum_add_distrib, ih, totalLeafAt]
    simp

private theorem sum_bagLeafWeights_vars_le {n r m : ℕ} (L : Finset (Fin n))
    (hcnt : ∀ {m' : ℕ} (T : ChopTree n m'), (∑ i ∈ L, T.leafAt i) ≤ T.leafCount)
    (load : Fin (r + 1) → ℕ) (S : ChopSeq n m) (j : Fin (r + 1)) :
    load j + (∑ i ∈ L, bagLeafWeights load S j i) ≤ bagFinalLoads load S j := by
  induction S generalizing load with
  | root T =>
    simp only [bagLeafWeights, bagFinalLoads]
    by_cases hj : j = minBag load
    · subst hj
      simp only [↓reduceIte, Function.update_self]
      exact Nat.add_le_add_left (hcnt T) _
    · simp [hj]
  | step K rest ih =>
    simp only [bagLeafWeights, bagFinalLoads]
    set j₀ := minBag load
    have hstep := ih (Function.update load j₀ (load j₀ + K.leafCount))
    rw [Finset.sum_add_distrib]
    by_cases hj : j = j₀
    · subst hj
      simp only [↓reduceIte, Function.update_self] at hstep ⊢
      have hK := hcnt K
      omega
    · simp only [hj, ↓reduceIte, Finset.sum_const_zero, zero_add]
      rwa [Function.update_of_ne hj] at hstep

private theorem bagFinalLoads_le {n r W m : ℕ} (load : Fin (r + 1) → ℕ) (S : ChopSeq n m)
    (hbd : S.AllBounded W) {Total : ℕ}
    (htot : (∑ j : Fin (r + 1), load j) + S.totalLeaves ≤ Total)
    (hinv : ∀ j : Fin (r + 1), load j ≤ (Total + r * W) / (r + 1)) :
    ∀ j : Fin (r + 1), bagFinalLoads load S j ≤ (Total + r * W) / (r + 1) := by
  induction S generalizing load with
  | root T =>
    intro j
    simp only [bagFinalLoads]
    set j₀ := minBag load
    by_cases hj : j = j₀
    · subst hj
      rw [Function.update_self]
      have hmin := mul_minBag_le_sum load
      have hT : T.leafCount ≤ W := hbd
      simp only [totalLeaves] at htot
      have hmul : (r + 1) * (load j₀ + T.leafCount) ≤ Total + r * W := by
        calc (r + 1) * (load j₀ + T.leafCount)
            = (r + 1) * load j₀ + T.leafCount + r * T.leafCount := by ring
          _ ≤ (∑ j', load j') + T.leafCount + r * W :=
            Nat.add_le_add (Nat.add_le_add_right hmin _) (Nat.mul_le_mul_left r hT)
          _ ≤ Total + r * W := Nat.add_le_add_right htot _
      exact (Nat.le_div_iff_mul_le (Nat.succ_pos r)).mpr (by linarith)
    · rw [Function.update_of_ne hj]
      exact hinv j
  | step K rest ih =>
    obtain ⟨hK, hrest⟩ := hbd
    set j₀ := minBag load
    let load' := Function.update load j₀ (load j₀ + K.leafCount)
    have hsum' : (∑ j : Fin (r + 1), load' j) + rest.totalLeaves ≤ Total := by
      have hupd : ∑ j : Fin (r + 1), load' j = (∑ j : Fin (r + 1), load j) + K.leafCount := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j₀),
          ← Finset.sum_erase_add _ load (Finset.mem_univ j₀)]
        have hrest_eq : ∑ j ∈ Finset.univ.erase j₀, load' j =
            ∑ j ∈ Finset.univ.erase j₀, load j :=
          Finset.sum_congr rfl fun j hj => Function.update_of_ne (Finset.mem_erase.mp hj).1 _ _
        simp only [load', Function.update_self, hrest_eq]
        omega
      rw [hupd]
      simpa only [totalLeaves, add_assoc] using htot
    have hinv' : ∀ j : Fin (r + 1), load' j ≤ (Total + r * W) / (r + 1) := by
      intro j
      by_cases hj : j = j₀
      · subst hj
        simp only [load', Function.update_self]
        have hmin := mul_minBag_le_sum load
        simp only [totalLeaves] at htot
        have hmul : (r + 1) * (load j₀ + K.leafCount) ≤ Total + r * W := by
          calc (r + 1) * (load j₀ + K.leafCount)
              = (r + 1) * load j₀ + K.leafCount + r * K.leafCount := by ring
            _ ≤ (∑ j', load j') + K.leafCount + r * W :=
              Nat.add_le_add (Nat.add_le_add_right hmin _) (Nat.mul_le_mul_left r hK)
            _ ≤ Total + r * W := Nat.add_le_add_right (by omega) _
        exact (Nat.le_div_iff_mul_le (Nat.succ_pos r)).mpr (by linarith)
      · simp only [load', Function.update_of_ne hj]
        exact hinv j
    exact ih load' hrest hsum' hinv'

/-- Compile a `ChopSeq` directly into a `(r + 1)`-party `NOF.Protocol` following the greedy bag
owners. -/
private noncomputable def toProtocol {n r : ℕ} (X : Fin (r + 1) → Finset (Fin n))
    (z : Fin n → Bool) :
    ∀ {m : ℕ}, (Fin (r + 1) → ℕ) → ChopSeq n m → (Fin m → Bool) →
      NOF.Protocol (fun j : Fin (r + 1) => X j → Bool) Bool
  | _, load, root T, b =>
    let j₀ := minBag load
    NOF.Protocol.speak j₀ (fun v => T.eval (reconstructFromView X z j₀ v) b)
      (NOF.Protocol.output false) (NOF.Protocol.output true)
  | _, load, step K rest, b =>
    let j₀ := minBag load
    let load' := Function.update load j₀ (load j₀ + K.leafCount)
    NOF.Protocol.speak j₀ (fun v => K.eval (reconstructFromView X z j₀ v) b)
      (toProtocol X z load' rest (Fin.snoc b false))
      (toProtocol X z load' rest (Fin.snoc b true))

private theorem depth_toProtocol {n r m : ℕ} (X : Fin (r + 1) → Finset (Fin n))
    (z : Fin n → Bool) (load : Fin (r + 1) → ℕ) (S : ChopSeq n m) (b : Fin m → Bool) :
    (S.toProtocol X z load b).depth = S.steps := by
  induction S generalizing load with
  | root _ => simp [toProtocol, steps]
  | step K rest ih =>
    simp only [toProtocol, NOF.Protocol.depth_speak, ih, max_self, steps]

private theorem run_toProtocol {n r m : ℕ} {X : Fin (r + 1) → Finset (Fin n)}
    (hdisj : Pairwise fun j₁ j₂ => Disjoint (X j₁) (X j₂)) (z : Fin n → Bool)
    (load : Fin (r + 1) → ℕ) (S : ChopSeq n m)
    (havoid : ∀ j : Fin (r + 1), ∀ i ∈ X j, bagLeafWeights load S j i = 0)
    (b : Fin m → Bool) (y : ∀ j : Fin (r + 1), X j → Bool) :
    (S.toProtocol X z load b).run y = S.eval (embedBlocks X z y) b := by
  induction S generalizing load with
  | root T =>
    simp only [toProtocol, NOF.Protocol.run_speak, NOF.Protocol.run_output, eval]
    set j₀ := minBag load
    have hTeq : T.eval (reconstructFromView X z j₀ (NOF.view j₀ y)) b =
        T.eval (embedBlocks X z y) b := by
      refine T.eval_congr_of_leafAt_eq_zero b fun i hi => ?_
      refine reconstructFromView_eq_embedBlocks hdisj z j₀ y fun hiX => hi ?_
      have h0 := havoid j₀ i hiX
      simpa [bagLeafWeights, j₀] using h0
    rw [hTeq]
    cases T.eval (embedBlocks X z y) b <;> rfl
  | step K rest ih =>
    simp only [toProtocol, NOF.Protocol.run_speak, eval]
    set j₀ := minBag load
    let load' := Function.update load j₀ (load j₀ + K.leafCount)
    have hKeq : K.eval (reconstructFromView X z j₀ (NOF.view j₀ y)) b =
        K.eval (embedBlocks X z y) b := by
      refine K.eval_congr_of_leafAt_eq_zero b fun i hi => ?_
      refine reconstructFromView_eq_embedBlocks hdisj z j₀ y fun hiX => hi ?_
      have h0 := havoid j₀ i hiX
      simp only [bagLeafWeights, Nat.add_eq_zero_iff] at h0
      simpa [j₀] using h0.1
    have havoid' : ∀ j : Fin (r + 1), ∀ i ∈ X j, bagLeafWeights load' rest j i = 0 := by
      intro j i hiX
      have h0 := havoid j i hiX
      simp only [bagLeafWeights, Nat.add_eq_zero_iff] at h0
      exact h0.2
    rw [hKeq]
    cases hbit : K.eval (embedBlocks X z y) b <;>
      simpa [hbit] using ih load' havoid' (Fin.snoc b _)

end ChopSeq

private theorem sum_leafAt_le_leafCount {n m : ℕ} (L : Finset (Fin n)) (T : ChopTree n m) :
    (∑ i ∈ L, T.leafAt i) ≤ T.leafCount := by
  induction T with
  | input j =>
    simp only [ChopTree.leafAt, ChopTree.leafCount]
    by_cases hj : j ∈ L
    · rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hne; simp [Ne.symm hne]
      · intro hnot; exact absurd hj hnot
    · rw [Finset.sum_eq_zero]
      · omega
      · intro i hi; have hne : j ≠ i := fun h => hj (h ▸ hi); simp [hne]
  | prev _ => simp [ChopTree.leafAt, ChopTree.leafCount]
  | node a op args ih =>
    simp only [ChopTree.leafAt, ChopTree.leafCount]
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun s _ => ih s

/-- Core compilation lemma on a light-variable subset `L : Finset (Fin n)`: given `F.FanInAtMost 2`,
every `i ∈ L` read at most `r` times, chopping budget `1 ≤ B`, and block size `q` satisfying
`(r + 1) * q ≤ L.card` and `(F.leafSize + 2 * r * B) / (r + 1) + r * q ≤ L.card`, `F` compiles to a
deterministic `(r + 1)`-party `NOF.Protocol` of depth `≤ F.leafSize / (B + 1) + 1`. -/
theorem exists_nof_protocol_on_subset {σ : Signature} {n r B q : ℕ} (hB : 1 ≤ B)
    (I : Interpretation σ Bool) (F : Formula σ n) (hfan : F.FanInAtMost 2)
    (L : Finset (Fin n)) (hread : ∀ i ∈ L, F.leafSizeIn {i} ≤ r)
    (hq_tot : (r + 1) * q ≤ L.card)
    (hq_cap : (F.leafSize + 2 * r * B) / (r + 1) + r * q ≤ L.card) :
    ∃ X : Fin (r + 1) → Finset (Fin n),
      Pairwise (fun j₁ j₂ => Disjoint (X j₁) (X j₂)) ∧
      (∀ j : Fin (r + 1), X j ⊆ L ∧ (X j).card = q) ∧
      ∀ z : Fin n → Bool, ∃ p : NOF.Protocol (fun j : Fin (r + 1) => X j → Bool) Bool,
        (∀ y, p.run y = F.eval I (embedBlocks X z y)) ∧
        p.depth ≤ F.leafSize / (B + 1) + 1 := by
  classical
  let T₀ := ChopTree.ofFormula I F
  have hT₀_fan : T₀.FanIn2 := ChopTree.fanIn2_ofFormula I hfan
  have hT₀_cnt : T₀.leafCount = F.leafSize := ChopTree.leafCount_ofFormula I F
  let S := ChopSeq.chopAux B hB T₀.leafCount T₀ hT₀_fan le_rfl
  obtain ⟨hbd, hsteps, htot, hat, hev⟩ :=
    ChopSeq.chopAux_spec hB T₀.leafCount T₀ hT₀_fan le_rfl
  let zeroLoad : Fin (r + 1) → ℕ := fun _ => 0
  let wBag := ChopSeq.bagLeafWeights zeroLoad S
  let bags : Fin (r + 1) → Finset (Fin n) := fun j => Finset.univ.filter fun i => wBag j i ≠ 0
  have hbag_read : ∀ i ∈ L, (Finset.univ.filter fun j : Fin (r + 1) => i ∈ bags j).card ≤ r := by
    intro i hi
    calc (Finset.univ.filter fun j : Fin (r + 1) => i ∈ bags j).card
        = ∑ j : Fin (r + 1), if wBag j i ≠ 0 then 1 else 0 := by
          rw [Finset.card_filter]; refine Finset.sum_congr rfl fun j _ => by simp [bags]
      _ ≤ ∑ j : Fin (r + 1), wBag j i := by
          refine Finset.sum_le_sum fun j _ => ?_
          by_cases h0 : wBag j i = 0 <;> simp [h0]; omega
      _ = S.totalLeafAt i := ChopSeq.sum_bagLeafWeights_eq zeroLoad S i
      _ = F.leafSizeIn {i} := (hat i).trans (ChopTree.leafAt_ofFormula I F i)
      _ ≤ r := hread i hi
  have hbag_cap : ∀ j : Fin (r + 1), (L ∩ bags j).card ≤ (F.leafSize + 2 * r * B) / (r + 1) := by
    intro j
    have hcard_le_sum : (L ∩ bags j).card ≤ ∑ i ∈ L, wBag j i := by
      rw [← Finset.filter_mem_eq_inter, Finset.card_filter]
      refine Finset.sum_le_sum fun i _ => ?_
      simp only [bags, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases h0 : wBag j i = 0 <;> simp [h0]; omega
    have hsum_le_final :=
      ChopSeq.sum_bagLeafWeights_vars_le L (fun T => sum_leafAt_le_leafCount L T) zeroLoad S j
    simp only [zeroLoad, zero_add] at hsum_le_final
    have hfinal_le := ChopSeq.bagFinalLoads_le zeroLoad S hbd (Total := F.leafSize)
      (by
        simp only [zeroLoad, Finset.sum_const_zero, zero_add]
        exact htot.trans_le hT₀_cnt.le) (fun _ => Nat.zero_le _) j
    exact hcard_le_sum.trans (hsum_le_final.trans (by
      rwa [show r * (2 * B) = 2 * r * B by ring] at hfinal_le))
  obtain ⟨X, hdisj, hX⟩ := exists_disjoint_blocks_avoiding_bags L bags hbag_read hbag_cap
    hq_tot hq_cap
  have havoid : ∀ j : Fin (r + 1), ∀ i ∈ X j, wBag j i = 0 := by
    intro j i hiX
    simpa [bags] using Finset.disjoint_left.mp (hX j).2.2 hiX
  have hdepth : S.steps ≤ F.leafSize / (B + 1) + 1 := by
    have hsteps' : (S.steps - 1) * (B + 1) ≤ F.leafSize := hsteps.trans_eq hT₀_cnt
    have hdiv : S.steps - 1 ≤ F.leafSize / (B + 1) :=
      (Nat.le_div_iff_mul_le (Nat.succ_pos B)).mpr (by nlinarith)
    omega
  refine ⟨X, hdisj, fun j => ⟨(hX j).1, (hX j).2.1⟩, fun z => ?_⟩
  refine ⟨S.toProtocol X z zeroLoad Fin.elim0, fun y => ?_, ?_⟩
  · rw [ChopSeq.run_toProtocol hdisj z zeroLoad S havoid Fin.elim0 y, hev,
      ChopTree.eval_ofFormula]
  · rw [ChopSeq.depth_toProtocol]
    exact hdepth

end Chopping

/-! ### Part 4: Read-`r` formula compilation, general `O(r)`-bit formula compilation, and
`Ω(n log n)` discrepancy lower bounds -/

private theorem div_succ_add_le {a b r m : ℕ} (h : a + b * (r + 1) ≤ (r + 1) * m) :
    a / (r + 1) + b ≤ m :=
  calc a / (r + 1) + b = (a + b * (r + 1)) / (r + 1) :=
        (Nat.add_mul_div_right a b (Nat.succ_pos r)).symm
    _ ≤ ((r + 1) * m) / (r + 1) := Nat.div_le_div_right h
    _ = m := Nat.mul_div_right m (Nat.succ_pos r)

/-- **Read-`r` formula to `(r + 1)`-party NOF protocol.** Every fan-in-two, read-`r` formula `F`
on `n` variables (`1 ≤ r`, `4 * r ≤ n`) compiles on pairwise disjoint blocks of size
`n / (2 * r * (r + 1))` to a deterministic `(r + 1)`-party `NOF.Protocol` of depth at most
`F.leafSize / (n / (4 * r) + 1) + 1 ≤ 4 * r ^ 2 + 1` (`O(r)` bits when `F.leafSize = O(n)`, and
`O(1)` bits for fixed `r`). -/
theorem exists_nof_protocol_of_readAtMost {σ : Signature} {n r : ℕ} (hr : 1 ≤ r)
    (hn : 4 * r ≤ n) (I : Interpretation σ Bool) (F : Formula σ n) (hfan : F.FanInAtMost 2)
    (hread : F.ReadAtMost r) :
    ∃ X : Fin (r + 1) → Finset (Fin n),
      Pairwise (fun j₁ j₂ => Disjoint (X j₁) (X j₂)) ∧
      (∀ j : Fin (r + 1), (X j).card = n / (2 * r * (r + 1))) ∧
      ∀ z : Fin n → Bool, ∃ p : NOF.Protocol (fun j : Fin (r + 1) => X j → Bool) Bool,
        (∀ y, p.run y = F.eval I (embedBlocks X z y)) ∧
        p.depth ≤ F.leafSize / (n / (4 * r) + 1) + 1 ∧
        p.depth ≤ 4 * r ^ 2 + 1 := by
  set B := n / (4 * r)
  set q := n / (2 * r * (r + 1))
  have hB : 1 ≤ B := (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith)
  have hL : F.leafSize ≤ r * n := F.leafSize_le_of_readAtMost hread
  have h4rB : 4 * r * B ≤ n := Nat.mul_div_le n (4 * r)
  have hmul_q : 2 * r * (r + 1) * q ≤ n := Nat.mul_div_le n (2 * r * (r + 1))
  have hq_tot : (r + 1) * q ≤ (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_fin]
    nlinarith
  have hq_cap : (F.leafSize + 2 * r * B) / (r + 1) + r * q ≤
      (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_fin]
    refine div_succ_add_le ?_
    have h1 : 2 * (2 * r * B) ≤ n := by linarith
    have h2 : 2 * ((r * q) * (r + 1)) ≤ n := by nlinarith
    nlinarith
  obtain ⟨X, hdisj, hX, hprot⟩ := exists_nof_protocol_on_subset hB I F hfan Finset.univ
    (fun i _ => hread i) hq_tot hq_cap
  have hdiv_bound : F.leafSize / (B + 1) ≤ 4 * r ^ 2 := by
    have hn_lt : n < 4 * r * (B + 1) := Nat.lt_mul_div_succ n (by omega)
    have hL_le : F.leafSize ≤ (4 * r ^ 2) * (B + 1) := by
      calc F.leafSize ≤ r * n := hL
        _ ≤ r * (4 * r * (B + 1)) := Nat.mul_le_mul_left r hn_lt.le
        _ = (4 * r ^ 2) * (B + 1) := by ring
    exact (Nat.div_le_iff_le_mul_add_pred (Nat.succ_pos B)).mpr (by nlinarith)
  refine ⟨X, hdisj, fun j => (hX j).2, fun z => ?_⟩
  obtain ⟨p, hp_run, hp_depth⟩ := hprot z
  exact ⟨p, hp_run, hp_depth, hp_depth.trans (Nat.add_le_add_right hdiv_bound 1)⟩

/-- **General fan-in-two formula compilation to an `O(r)`-bit `(r + 1)`-party NOF protocol.**
For *any* fan-in-two formula `F : Formula σ n` (`8 ≤ n`, no read bound assumed), setting
`r = 4 * F.leafSize / n + 1`, there exist `r + 1` pairwise disjoint blocks `X j` each of size
`n / (4 * r)` such that for every background assignment `z : Fin n → Bool`, `F` compiles to a
deterministic `(r + 1)`-party `NOF.Protocol` of depth at most `2 * r + 1`. -/
theorem exists_nof_protocol_of_formula {σ : Signature} {n : ℕ} (hn8 : 8 ≤ n)
    (I : Interpretation σ Bool) (F : Formula σ n) (hfan : F.FanInAtMost 2) :
    let r := 4 * F.leafSize / n + 1
    ∃ X : Fin (r + 1) → Finset (Fin n),
      Pairwise (fun j₁ j₂ => Disjoint (X j₁) (X j₂)) ∧
      (∀ j : Fin (r + 1), (X j).card = n / (4 * r)) ∧
      ∀ z : Fin n → Bool, ∃ p : NOF.Protocol (fun j : Fin (r + 1) => X j → Bool) Bool,
        (∀ y, p.run y = F.eval I (embedBlocks X z y)) ∧
        p.depth ≤ 2 * r + 1 := by
  classical
  set r := 4 * F.leafSize / n + 1
  have hr_def : r = 4 * F.leafSize / n + 1 := rfl
  have hr : 1 ≤ r := Nat.succ_pos _
  have h4L_lt : 4 * F.leafSize < r * n :=
    (Nat.lt_mul_div_succ _ (by omega)).trans_eq (mul_comm _ _)
  let heavy : Finset (Fin n) := Finset.univ.filter fun i => r < F.leafSizeIn {i}
  let light : Finset (Fin n) := Finset.univ.filter fun i => ¬r < F.leafSizeIn {i}
  have hheavy_le : (r + 1) * heavy.card ≤ F.leafSize := by
    calc (r + 1) * heavy.card = ∑ _i ∈ heavy, (r + 1) := by simp [mul_comm]
      _ ≤ ∑ i ∈ heavy, F.leafSizeIn {i} :=
        Finset.sum_le_sum fun i hi => Nat.succ_le_of_lt (Finset.mem_filter.mp hi).2
      _ = F.leafSizeIn heavy := F.sum_leafSizeIn_singleton heavy
      _ ≤ F.leafSize := F.leafSizeIn_le_leafSize heavy
  have h4heavy : 4 * heavy.card < n := by
    have h1 : 4 * (r + 1) * heavy.card ≤ 4 * F.leafSize := by nlinarith
    have h2 : 4 * F.leafSize < (r + 1) * n := h4L_lt.trans (by nlinarith)
    nlinarith
  have hpart : heavy.card + light.card = n :=
    (Finset.card_filter_add_card_filter_not _).trans (Finset.card_fin n)
  set B := n / 8
  have hB : 1 ≤ B := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  set q := n / (4 * r)
  have hmul_q : 4 * r * q ≤ n := Nat.mul_div_le n (4 * r)
  have hq_tot : (r + 1) * q ≤ light.card := by nlinarith
  have hq_cap : (F.leafSize + 2 * r * B) / (r + 1) + r * q ≤ light.card := by
    have h8B : 8 * B ≤ n := Nat.mul_div_le n 8
    have hlight_ge : 3 * n < 4 * light.card := by omega
    exact div_succ_add_le (by nlinarith)
  obtain ⟨X, hdisj, hX, hprot⟩ := exists_nof_protocol_on_subset hB I F hfan light
    (fun i hi => not_lt.mp (Finset.mem_filter.mp hi).2) hq_tot hq_cap
  have hdepth2r : F.leafSize / (B + 1) + 1 ≤ 2 * r + 1 := by
    have hn_lt : n < 8 * (B + 1) := Nat.lt_mul_div_succ n (by omega)
    have hL_le : F.leafSize ≤ (2 * r) * (B + 1) := by
      have h1 : 4 * F.leafSize ≤ r * (8 * (B + 1)) :=
        h4L_lt.le.trans (Nat.mul_le_mul_left r hn_lt.le)
      nlinarith
    have hdiv : F.leafSize / (B + 1) ≤ 2 * r :=
      (Nat.div_le_iff_le_mul_add_pred (Nat.succ_pos B)).mpr (by nlinarith)
    omega
  refine ⟨X, hdisj, fun j => (hX j).2, fun z => ?_⟩
  obtain ⟨p, hp_run, hp_depth⟩ := hprot z
  exact ⟨p, hp_run, hp_depth.trans hdepth2r⟩

/-- **Exact formula discrepancy bound** wired directly into `Cslib.Communication.NOF.discrepancy`:
for any fan-in-two formula `F` computing `f` (`8 ≤ n`, `r = 4 * F.leafSize / n + 1`), some
`(r + 1)`-tuple of pairwise disjoint blocks `X j` of size `n / (4 * r)` satisfies
`1 ≤ 2 ^ (2 * r + 1) * NOF.discrepancy uniform (fun y => f (embedBlocks X z y))` for every `z`. -/
theorem one_le_two_pow_mul_nof_discrepancy_of_formula {σ : Signature} {n : ℕ} (hn8 : 8 ≤ n)
    (I : Interpretation σ Bool) {F : Formula σ n} (hfan : F.FanInAtMost 2)
    {f : (Fin n → Bool) → Bool} (hcomp : F.Computes I f) :
    let r := 4 * F.leafSize / n + 1
    ∃ X : Fin (r + 1) → Finset (Fin n),
      Pairwise (fun j₁ j₂ => Disjoint (X j₁) (X j₂)) ∧
      (∀ j : Fin (r + 1), (X j).card = n / (4 * r)) ∧
      ∀ z : Fin n → Bool,
        1 ≤ (2 : ℝ) ^ (2 * r + 1) *
          NOF.discrepancy (PMF.uniformOfFintype (∀ j : Fin (r + 1), X j → Bool))
            (fun y => f (embedBlocks X z y)) := by
  obtain ⟨X, hdisj, hcard, hprot⟩ := exists_nof_protocol_of_formula hn8 I F hfan
  refine ⟨X, hdisj, hcard, fun z => ?_⟩
  obtain ⟨p, hp_run, hp_depth⟩ := hprot z
  have hrun : p.run = fun y => f (embedBlocks X z y) :=
    funext fun y => (hp_run y).trans (hcomp (embedBlocks X z y))
  have hdisc := p.one_le_two_pow_mul_discrepancy hrun
    (PMF.uniformOfFintype (∀ j : Fin (4 * F.leafSize / n + 1 + 1), X j → Bool))
  exact hdisc.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ one_le_two hp_depth) NOF.discrepancy_nonneg)

/-- Bijection splitting `Fin n → Bool` into a multiparty block assignment `∀ j, X j → Bool` and a
background assignment on the complement `(univ.biUnion X)ᶜ`. -/
private noncomputable def equivBlocksRest {k n : ℕ} {X : Fin k → Finset (Fin n)}
    (hdisj : Pairwise fun j₁ j₂ => Disjoint (X j₁) (X j₂)) :
    ((∀ j : Fin k, X j → Bool) × (↥(Finset.univ.biUnion X)ᶜ → Bool)) ≃ (Fin n → Bool) where
  toFun yw := embedBlocks X
    (fun i => if hi : i ∈ (Finset.univ.biUnion X)ᶜ then yw.2 ⟨i, hi⟩ else false) yw.1
  invFun x := (fun _ u => x u.val, fun w => x w.val)
  left_inv := by
    rintro ⟨y, w⟩
    refine Prod.ext (funext fun j => funext fun u => ?_) (funext fun u => ?_)
    · dsimp only
      exact embedBlocks_of_mem hdisj _ y u.property
    · dsimp only
      have hnot : ∀ j : Fin k, u.val ∉ X j := fun j hj =>
        (Finset.mem_compl.mp u.property) (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hj⟩)
      rw [embedBlocks_of_notMem _ y hnot]
      exact dite_eq_left_of_eq_true (eq_true u.property)
  right_inv := by
    intro x
    funext i
    dsimp only
    by_cases hmem : i ∈ Finset.univ.biUnion X
    · obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hmem
      exact embedBlocks_of_mem hdisj _ _ hj
    · have hnot : ∀ j : Fin k, i ∉ X j := fun j hj =>
        hmem (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hj⟩)
      have hc : i ∈ (Finset.univ.biUnion X)ᶜ := Finset.mem_compl.mpr hmem
      rw [embedBlocks_of_notMem _ _ hnot]
      exact dite_eq_left_of_eq_true (eq_true hc)

/-- **Distributional / average-case formula discrepancy bound** wired directly into
`Cslib.Communication.NOF.discrepancy`: if a fan-in-two formula `F` (`8 ≤ n`,
`r = 4 * F.leafSize / n + 1`) has signed correlation at least `2 * γ` with `f` under the uniform
distribution on `Fin n → Bool`, then there exist pairwise disjoint blocks `X j` of size
`n / (4 * r)` and a background fixing `z : Fin n → Bool` such that
`2 * γ ≤ 2 ^ (2 * r + 1) * NOF.discrepancy uniform (fun y => f (embedBlocks X z y))`. -/
theorem two_mul_le_two_pow_mul_nof_discrepancy_of_formula {σ : Signature} {n : ℕ} (hn8 : 8 ≤ n)
    (I : Interpretation σ Bool) {F : Formula σ n} (hfan : F.FanInAtMost 2)
    {f : (Fin n → Bool) → Bool} {γ : ℝ}
    (hcorr : 2 * γ * (2 : ℝ) ^ n ≤
      |∑ x : Fin n → Bool, BitString.signVal (f x) * BitString.signVal (F.eval I x)|) :
    let r := 4 * F.leafSize / n + 1
    ∃ (X : Fin (r + 1) → Finset (Fin n)) (z : Fin n → Bool),
      Pairwise (fun j₁ j₂ => Disjoint (X j₁) (X j₂)) ∧
      (∀ j : Fin (r + 1), (X j).card = n / (4 * r)) ∧
      2 * γ ≤ (2 : ℝ) ^ (2 * r + 1) *
        NOF.discrepancy (PMF.uniformOfFintype (∀ j : Fin (r + 1), X j → Bool))
          (fun y => f (embedBlocks X z y)) := by
  classical
  set r := 4 * F.leafSize / n + 1
  obtain ⟨X, hdisj, hcard, hprot⟩ := exists_nof_protocol_of_formula hn8 I F hfan
  let R := (Finset.univ.biUnion X)ᶜ
  let Y := ∀ j : Fin (r + 1), X j → Bool
  let W := ↥R → Bool
  let e := equivBlocksRest hdisj
  let zOf (w : W) : Fin n → Bool := fun i => if hi : i ∈ R then w ⟨i, hi⟩ else false
  have hcard_prod : (Fintype.card Y : ℝ) * (Fintype.card W : ℝ) = (2 : ℝ) ^ n := by
    exact_mod_cast (Fintype.card_prod Y W).symm.trans ((Fintype.card_congr e).trans (by simp))
  have hsum_split : (∑ x : Fin n → Bool, BitString.signVal (f x) * BitString.signVal (F.eval I x)) =
      ∑ w : W, ∑ y : Y,
        BitString.signVal (f (embedBlocks X (zOf w) y)) *
          BitString.signVal (F.eval I (embedBlocks X (zOf w) y)) := by
    let g : Y × W → ℝ := fun yw =>
      BitString.signVal (f (embedBlocks X (zOf yw.2) yw.1)) *
        BitString.signVal (F.eval I (embedBlocks X (zOf yw.2) yw.1))
    have heq : (∑ x : Fin n → Bool, BitString.signVal (f x) * BitString.signVal (F.eval I x)) =
        ∑ yw : Y × W, g yw :=
      (Fintype.sum_equiv e g
        (fun x => BitString.signVal (f x) * BitString.signVal (F.eval I x)) fun _ => rfl).symm
    rw [heq, Fintype.sum_prod_type, Finset.sum_comm]
  have habs_le : |∑ x : Fin n → Bool, BitString.signVal (f x) * BitString.signVal (F.eval I x)| ≤
      ∑ w : W, |∑ y : Y, BitString.signVal (f (embedBlocks X (zOf w) y)) *
        BitString.signVal (F.eval I (embedBlocks X (zOf w) y))| := by
    rw [hsum_split]
    exact Finset.abs_sum_le_sum_abs _ _
  have hY_pos : (0 : ℝ) < Fintype.card Y := by exact_mod_cast (Fintype.card_pos (α := Y))
  obtain ⟨w₀, -, hw₀⟩ : ∃ w₀ ∈ (Finset.univ : Finset W),
      2 * γ * (Fintype.card Y : ℝ) ≤
        |∑ y : Y, BitString.signVal (f (embedBlocks X (zOf w₀) y)) *
          BitString.signVal (F.eval I (embedBlocks X (zOf w₀) y))| := by
    by_contra! hlt
    have hsum_lt : (∑ w : W, |∑ y : Y, BitString.signVal (f (embedBlocks X (zOf w) y)) *
          BitString.signVal (F.eval I (embedBlocks X (zOf w) y))|) <
        ∑ _w : W, (2 * γ * (Fintype.card Y : ℝ)) :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun w hw => hlt w hw
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum_lt
    linarith [show (Fintype.card W : ℝ) * (2 * γ * Fintype.card Y) = 2 * γ * 2 ^ n by
      rw [← hcard_prod]; ring]
  obtain ⟨p, hp_run, hp_depth⟩ := hprot (zOf w₀)
  let ν : PMF Y := PMF.uniformOfFintype Y
  have hν_apply : ∀ y : Y, (ν y).toReal = (Fintype.card Y : ℝ)⁻¹ := fun y => by
    simp [ν, PMF.uniformOfFintype_apply]
  have hslice := p.abs_sum_mul_signVal_le ν (fun y => f (embedBlocks X (zOf w₀) y))
    (fun _ _ => true)
  simp only [NOF.cylinderIntersection_true, Set.mem_univ, Finset.filter_true, hν_apply, hp_run]
    at hslice
  simp only [mul_assoc, ← Finset.mul_sum] at hslice
  rw [abs_mul, abs_of_pos (inv_pos.mpr hY_pos), inv_mul_le_iff₀ hY_pos] at hslice
  have h2γ : 2 * γ ≤ (2 : ℝ) ^ p.depth *
      NOF.discrepancy ν (fun y => f (embedBlocks X (zOf w₀) y)) :=
    le_of_mul_le_mul_left (by linarith [hw₀.trans hslice]) hY_pos
  refine ⟨X, zOf w₀, hdisj, hcard, h2γ.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hp_depth) NOF.discrepancy_nonneg

/-- **Conditional `Ω(n log n)` formula leaf-size lower bound from balanced NOF cube discrepancy.**
Let `f : (Fin n → Bool) → Bool` satisfy the Babai–Nisan–Szegedy cube discrepancy bound
`disc(f|_{X, false}) ^ (2 ^ (r + 1)) ≤ (1 - 2 / 2 ^ (r + 1)) ^ (n / (4 * r))` across the balanced
regime `1 ≤ r`, `4 * r + 6 ≤ Nat.log 2 n` on pairwise disjoint variable blocks `X` of size
`n / (4 * r)`. Then every fan-in-two Boolean formula `F : Formula σ n` over any signature `σ` and
interpretation `I` computing `f` satisfies `n * (Nat.log 2 n - 12) ≤ 16 * F.leafSize`. -/
theorem mul_log_le_leafSize_of_balanced_discrepancy {σ : Signature} {n : ℕ}
    (I : Interpretation σ Bool) {F : Formula σ n} (hfan : F.FanInAtMost 2)
    {f : (Fin n → Bool) → Bool} (hcomp : F.Computes I f)
    (hdisc : ∀ (r : ℕ), 1 ≤ r → 4 * r + 6 ≤ Nat.log 2 n →
      ∀ X : Fin (r + 1) → Finset (Fin n),
        Pairwise (fun j₁ j₂ => Disjoint (X j₁) (X j₂)) →
        (∀ j : Fin (r + 1), (X j).card = n / (4 * r)) →
        NOF.discrepancy (PMF.uniformOfFintype (∀ j : Fin (r + 1), X j → Bool))
          (fun y => f (embedBlocks X (fun _ => false) y)) ^ (2 ^ (r + 1)) ≤
          (1 - 2 / (2 : ℝ) ^ (r + 1)) ^ (n / (4 * r))) :
    n * (Nat.log 2 n - 12) ≤ 16 * F.leafSize := by
  rcases le_or_gt (Nat.log 2 n) 12 with hlog12 | hlog_gt
  · have : Nat.log 2 n - 12 = 0 := by omega
    simp [this]
  · have hn_ne0 : n ≠ 0 := by
      rintro rfl
      simp at hlog_gt
    set r := 4 * F.leafSize / n + 1
    have hr_def : r = 4 * F.leafSize / n + 1 := rfl
    have hr1 : 1 ≤ r := Nat.succ_pos _
    by_cases hr_log : 4 * r + 6 ≤ Nat.log 2 n
    · exfalso
      have hn_pow : 2 ^ (4 * r + 6) ≤ n :=
        (Nat.pow_le_pow_right (by omega) hr_log).trans (Nat.pow_log_le_self 2 hn_ne0)
      have hr_pow : r ≤ 2 ^ r := Nat.lt_two_pow_self.le
      have hr_pow4 : r ≤ 2 ^ (4 * r) :=
        hr_pow.trans (Nat.pow_le_pow_right (by omega) (by omega : r ≤ 4 * r))
      have h8r_le : 8 * r ≤ n := by
        calc 8 * r ≤ 64 * 2 ^ (4 * r) := by omega
          _ = 2 ^ (4 * r + 6) := by rw [pow_add]; norm_num; ring
          _ ≤ n := hn_pow
      have hn8 : 8 ≤ n := by omega
      obtain ⟨X, hdisj, hcard, h1⟩ :=
        one_le_two_pow_mul_nof_discrepancy_of_formula hn8 I hfan hcomp
      set q := n / (4 * r)
      have hcube := hdisc r hr1 hr_log X hdisj hcard
      have hbns := NOF.two_mul_le_four_pow_mul_of_cube_discrepancy (Nat.succ_ne_zero r)
        (h1 fun _ => false) hcube
      have h4r_pos : 0 < 4 * r := by positivity
      have hq_ge2 : 2 ≤ q := (Nat.le_div_iff_mul_le h4r_pos).mpr (by omega)
      have hn_lt_q : n < 4 * r * (q + 1) := Nat.lt_mul_div_succ n h4r_pos
      have hn_le_6rq : n ≤ 3 * r * (2 * q) := by nlinarith
      have hr_sq : r * r ≤ 4 ^ r := by
        calc r * r ≤ 2 ^ r * 2 ^ r := Nat.mul_le_mul hr_pow hr_pow
          _ = 4 ^ r := by rw [← mul_pow]; norm_num
      have hpoly_lt : 3 * r * (2 * r + 1) < 16 * 4 ^ r := by
        have hlin : 3 * r * (2 * r + 1) ≤ 9 * (r * r) := by nlinarith
        have h4pos : 1 ≤ 4 ^ r := Nat.one_le_pow r 4 (by omega)
        nlinarith
      have hn_lt_pow : n < 2 ^ (4 * r + 6) := by
        have h2r_eq : 2 * (4 * F.leafSize / n + 1) + 1 = 2 * r + 1 := rfl
        rw [h2r_eq] at hbns
        calc n ≤ 3 * r * (2 * q) := hn_le_6rq
          _ ≤ 3 * r * (4 ^ (r + 1) * (2 * r + 1)) := Nat.mul_le_mul_left _ hbns
          _ = 3 * r * (2 * r + 1) * 4 ^ (r + 1) := by ring
          _ < (16 * 4 ^ r) * 4 ^ (r + 1) :=
            Nat.mul_lt_mul_of_pos_right hpoly_lt (Nat.pow_pos (by omega))
          _ = 2 ^ (4 * r + 6) := by
            have h4 : ∀ m : ℕ, 4 ^ m = 2 ^ (2 * m) := fun m => by
              rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
            rw [show (16 : ℕ) = 2 ^ 4 by norm_num, h4 r, h4 (r + 1), ← pow_add, ← pow_add]
            congr 1
            omega
      exact (Nat.log_lt_of_lt_pow hn_ne0 hn_lt_pow).not_ge hr_log
    · have hlog_sub : Nat.log 2 n - 12 ≤ 4 * (4 * F.leafSize / n) := by omega
      calc n * (Nat.log 2 n - 12)
          ≤ n * (4 * (4 * F.leafSize / n)) := Nat.mul_le_mul_left n hlog_sub
        _ = 4 * (n * (4 * F.leafSize / n)) := by ring
        _ ≤ 4 * (4 * F.leafSize) := Nat.mul_le_mul_left 4 (Nat.mul_div_le (4 * F.leafSize) n)
        _ = 16 * F.leafSize := by ring

/-! ### Part 5: Probabilistic existence of balanced NOF-hard Boolean functions via Hoeffding -/

private theorem embedBlocks_injective {k n : ℕ} {U : Type*} {X : Fin k → Finset (Fin n)}
    (hdisj : Pairwise fun j₁ j₂ => Disjoint (X j₁) (X j₂)) (z : Fin n → U) :
    Function.Injective (embedBlocks X z) := by
  intro y₁ y₂ heq
  funext j u
  have h := congrFun heq u.val
  rwa [embedBlocks_of_mem hdisj z y₁ u.property, embedBlocks_of_mem hdisj z y₂ u.property] at h

private theorem card_bad_cylinder_le {k n : ℕ} {X : Fin k → Finset (Fin n)}
    (hdisj : Pairwise fun j₁ j₂ => Disjoint (X j₁) (X j₂)) (z₀ : Fin n → Bool)
    (φ : ∀ j : Fin k, NOF.View (fun j' => X j' → Bool) j → Bool) {t : ℝ} (ht : 0 < t) :
    ((Finset.univ.filter fun f : (Fin n → Bool) → Bool =>
        t ≤ |∑ y with y ∈ NOF.cylinderIntersection φ,
          ((PMF.uniformOfFintype (∀ j : Fin k, X j → Bool)) y).toReal *
            BitString.signVal (f (embedBlocks X z₀ y))|).card : ℝ) ≤
      2 * (Fintype.card ((Fin n → Bool) → Bool) : ℝ) *
        Real.exp (-(t ^ 2 * (Fintype.card (∀ j : Fin k, X j → Bool) : ℝ) / 2)) := by
  classical
  let Ω := Fin n → Bool
  let Y := ∀ j : Fin k, X j → Bool
  let C : Finset Y := Finset.univ.filter (· ∈ NOF.cylinderIntersection φ)
  have hY_pos : (0 : ℝ) < Fintype.card Y := by exact_mod_cast Fintype.card_pos (α := Y)
  rcases C.eq_empty_or_nonempty with hC0 | hCne
  · rw [Finset.filter_false_of_mem fun f _ => ?_, Finset.card_empty, Nat.cast_zero]
    · positivity
    · change ¬t ≤ |∑ y ∈ C, _|
      rw [hC0, Finset.sum_empty, abs_zero, not_le]
      exact ht
  · let emb : Y ↪ Ω := ⟨embedBlocks X z₀, embedBlocks_injective hdisj z₀⟩
    let a : Ω → ℝ := fun x => if x ∈ C.map emb then (Fintype.card Y : ℝ)⁻¹ else 0
    have hν : ∀ y : Y, ((PMF.uniformOfFintype Y) y).toReal = (Fintype.card Y : ℝ)⁻¹ :=
      fun y => by simp [PMF.uniformOfFintype_apply]
    have hsum_eq : ∀ f : Ω → Bool, (∑ x : Ω, a x * BitString.signVal (f x)) =
        ∑ y ∈ C, ((PMF.uniformOfFintype Y) y).toReal *
          BitString.signVal (f (embedBlocks X z₀ y)) := by
      intro f
      simp only [a, ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_map,
        emb, Function.Embedding.coeFn_mk, hν]
    have hsq : ∑ x : Ω, a x ^ 2 = (C.card : ℝ) * ((Fintype.card Y : ℝ)⁻¹) ^ 2 := by
      have hite : ∀ x : Ω, a x ^ 2 = if x ∈ C.map emb then ((Fintype.card Y : ℝ)⁻¹) ^ 2 else 0 :=
        fun x => by dsimp only [a]; split_ifs <;> simp
      simp only [hite, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, Finset.card_map,
        nsmul_eq_mul]
    have hC_pos : (0 : ℝ) < C.card := by exact_mod_cast hCne.card_pos
    have hC_le : (C.card : ℝ) ≤ Fintype.card Y := by exact_mod_cast Finset.card_le_univ C
    have hsq_pos : 0 < ∑ x : Ω, a x ^ 2 := by rw [hsq]; positivity
    have hsq_le : ∑ x : Ω, a x ^ 2 ≤ (Fintype.card Y : ℝ)⁻¹ := by
      rw [hsq, sq, ← mul_assoc]
      exact mul_le_of_le_one_left (by positivity)
        (by rw [mul_inv_le_iff₀ hY_pos, one_mul]; exact hC_le)
    have hexp_ge : t ^ 2 * (Fintype.card Y : ℝ) / 2 ≤ t ^ 2 / (2 * ∑ x : Ω, a x ^ 2) := by
      have hlhs : t ^ 2 * (Fintype.card Y : ℝ) / 2 = t ^ 2 / (2 * (Fintype.card Y : ℝ)⁻¹) := by
        field_simp
      rw [hlhs]
      exact div_le_div_of_nonneg_left (sq_nonneg t) (by positivity) (by linarith)
    have hhoeff := Cslib.BitString.card_filter_le_abs_sum_mul_signVal_le a ht.le
    have hcard_fn : (2 : ℝ) ^ Fintype.card Ω = Fintype.card (Ω → Bool) := by simp
    change ((Finset.univ.filter fun f : Ω → Bool =>
      t ≤ |∑ y ∈ C, ((PMF.uniformOfFintype Y) y).toReal *
        BitString.signVal (f (embedBlocks X z₀ y))|).card : ℝ) ≤ _
    simp only [← hsum_eq]
    exact hhoeff.trans (by rw [hcard_fn]; gcongr)

private theorem balanced_exponent_bound {n r : ℕ} (hr : 1 ≤ r) (hn_ne0 : n ≠ 0)
    (hr_log : 4 * r + 6 ≤ Nat.log 2 n) :
    let q := n / (4 * r)
    let m := q / 4 + 1
    2 * m + 1 ≤ (r + 1) * q ∧
      (n + 1) + (1 + n * (r + 1) + (r + 1) * 2 ^ (r * q)) ≤
        2 ^ ((r + 1) * q - (2 * m + 1)) := by
  intro q m
  have hn_pow : 2 ^ (4 * r + 6) ≤ n :=
    (Nat.pow_le_pow_right (by omega) hr_log).trans (Nat.pow_log_le_self 2 hn_ne0)
  have hr_pow : r < 2 ^ (2 * r) :=
    Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by omega) (by omega : r ≤ 2 * r))
  have h4r_le : 4 * r ≤ 2 ^ (2 * r + 2) := by
    rw [pow_add]
    norm_num
    omega
  have hmul : 4 * r * 2 ^ (2 * r + 4) ≤ n :=
    calc 4 * r * 2 ^ (2 * r + 4)
        ≤ 2 ^ (2 * r + 2) * 2 ^ (2 * r + 4) := Nat.mul_le_mul_right _ h4r_le
      _ = 2 ^ (4 * r + 6) := by rw [← pow_add]; congr 1; omega
      _ ≤ n := hn_pow
  have h4r_pos : 0 < 4 * r := by positivity
  have hq_pow : 2 ^ (2 * r + 4) ≤ q := (Nat.le_div_iff_mul_le h4r_pos).mpr (by linarith)
  have h2r_lt : 2 * r < 2 ^ (2 * r) := Nat.lt_two_pow_self
  have hpow_ge : 16 * (2 * r + 1) ≤ 2 ^ (2 * r + 4) := by
    rw [pow_add]
    norm_num
    omega
  have hq_ge : 2 * r + 28 ≤ q := by omega
  have hm_def : m = q / 4 + 1 := rfl
  have hadd_rq : (r + 1) * q = r * q + q := by ring
  have h2m_le : 2 * m + 1 ≤ (r + 1) * q := by omega
  have hE_ge : r * q + r + 10 ≤ (r + 1) * q - (2 * m + 1) := by omega
  refine ⟨h2m_le, ?_⟩
  have h1024 : 1024 * 2 ^ r * 2 ^ (r * q) ≤ 2 ^ ((r + 1) * q - (2 * m + 1)) := by
    calc 1024 * 2 ^ r * 2 ^ (r * q)
        = 2 ^ (r * q + r + 10) := by rw [pow_add, pow_add]; norm_num; ring
      _ ≤ 2 ^ ((r + 1) * q - (2 * m + 1)) := Nat.pow_le_pow_right (by omega) hE_ge
  have hn_lt : n < 4 * r * (q + 1) := Nat.lt_mul_div_succ n h4r_pos
  have hn_le_rq : n ≤ 8 * (r * q) := by nlinarith
  have hrq_lt : r * q < 2 ^ (r * q) := Nat.lt_two_pow_self
  have hnB : n ≤ 8 * 2 ^ (r * q) := by omega
  have hrA : r + 1 ≤ 2 ^ r := Nat.lt_two_pow_self
  have hA_pos : 1 ≤ 2 ^ r := Nat.one_le_pow r 2 (by omega)
  have hB_pos : 1 ≤ 2 ^ (r * q) := Nat.one_le_pow (r * q) 2 (by omega)
  have hterm1 : n * (r + 1) ≤ (8 * 2 ^ (r * q)) * 2 ^ r := Nat.mul_le_mul hnB hrA
  have hterm2 : (r + 1) * 2 ^ (r * q) ≤ 2 ^ r * 2 ^ (r * q) := Nat.mul_le_mul_right _ hrA
  have hterm3 : n ≤ 8 * (2 ^ r * 2 ^ (r * q)) := by nlinarith
  have hsum_le : (n + 1) + (1 + n * (r + 1) + (r + 1) * 2 ^ (r * q)) ≤
      1024 * 2 ^ r * 2 ^ (r * q) := by nlinarith
  exact hsum_le.trans h1024

/-- **Probabilistic existence of Boolean functions with exponentially small balanced NOF
discrepancy.** By Hoeffding's inequality (`Cslib.BitString.card_filter_le_abs_sum_mul_signVal_le`)
and a union bound over balanced block tuples `X : Fin (r + 1) → Finset (Fin n)` and `(r + 1)`-party
cylinder tests `φ`, for every `n : ℕ` there exists `f : (Fin n → Bool) → Bool` satisfying the
Babai–Nisan–Szegedy cube discrepancy bound across the balanced regime `1 ≤ r`,
`4 * r + 6 ≤ Nat.log 2 n`. -/
theorem exists_balanced_nof_discrepancy (n : ℕ) :
    ∃ f : (Fin n → Bool) → Bool,
      ∀ (r : ℕ), 1 ≤ r → 4 * r + 6 ≤ Nat.log 2 n →
        ∀ X : Fin (r + 1) → Finset (Fin n),
          Pairwise (fun j₁ j₂ => Disjoint (X j₁) (X j₂)) →
          (∀ j : Fin (r + 1), (X j).card = n / (4 * r)) →
          NOF.discrepancy (PMF.uniformOfFintype (∀ j : Fin (r + 1), X j → Bool))
            (fun y => f (embedBlocks X (fun _ => false) y)) ^ (2 ^ (r + 1)) ≤
            (1 - 2 / (2 : ℝ) ^ (r + 1)) ^ (n / (4 * r)) := by
  classical
  rcases eq_or_ne n 0 with rfl | hn_ne0
  · refine ⟨fun _ => false, fun _ _ hr_log => ?_⟩
    simp at hr_log
  · let ℱ := (Fin n → Bool) → Bool
    let z₀ : Fin n → Bool := fun _ => false
    let Rset : Finset ℕ := (Finset.Icc 1 n).filter fun r => 4 * r + 6 ≤ Nat.log 2 n
    let goodX (r : ℕ) : Finset (Fin (r + 1) → Finset (Fin n)) :=
      Finset.univ.filter fun X =>
        Pairwise (fun j₁ j₂ => Disjoint (X j₁) (X j₂)) ∧
          ∀ j : Fin (r + 1), (X j).card = n / (4 * r)
    let tOf (r : ℕ) : ℝ := (1 / 2 : ℝ) ^ ((n / (4 * r)) / 4 + 1)
    let badCyl {r : ℕ} (X : Fin (r + 1) → Finset (Fin n))
        (φ : ∀ j : Fin (r + 1), NOF.View (fun j' => X j' → Bool) j → Bool) : Finset ℱ :=
      Finset.univ.filter fun f : ℱ =>
        tOf r ≤ |∑ y with y ∈ NOF.cylinderIntersection φ,
          ((PMF.uniformOfFintype (∀ j : Fin (r + 1), X j → Bool)) y).toReal *
            BitString.signVal (f (embedBlocks X z₀ y))|
    let badR (r : ℕ) : Finset ℱ :=
      (goodX r).biUnion fun X => Finset.univ.biUnion fun φ => badCyl X φ
    let badTotal : Finset ℱ := Rset.biUnion badR
    have hbadR_le : ∀ r ∈ Rset,
        ((badR r).card : ℝ) ≤ (Fintype.card ℱ : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ := by
      intro r hrR
      have hrIcc := (Finset.mem_filter.mp hrR).1
      have hr_log : 4 * r + 6 ≤ Nat.log 2 n := (Finset.mem_filter.mp hrR).2
      have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hrIcc).1
      set q := n / (4 * r)
      set m := q / 4 + 1
      obtain ⟨h2m_le', hE_bound'⟩ := balanced_exponent_bound hr1 hn_ne0 hr_log
      have h2m_le : 2 * m + 1 ≤ (r + 1) * q := h2m_le'
      set E := (r + 1) * q - (2 * m + 1)
      have hE_bound : (n + 1) + (1 + n * (r + 1) + (r + 1) * 2 ^ (r * q)) ≤ 2 ^ E := hE_bound'
      have ht_pos : 0 < tOf r := by dsimp only [tOf]; positivity
      have hbadX_le : ∀ X ∈ goodX r,
          ((Finset.univ.biUnion fun φ => badCyl X φ).card : ℝ) ≤
            (2 : ℝ) ^ ((r + 1) * 2 ^ (r * q)) *
              (2 * (Fintype.card ℱ : ℝ) * ((2 : ℝ) ^ (2 ^ E))⁻¹) := by
        intro X hX
        obtain ⟨hdisj, hcard'⟩ := (Finset.mem_filter.mp hX).2
        have hcard : ∀ j : Fin (r + 1), (X j).card = q := hcard'
        have hcard_Y : Fintype.card (∀ j : Fin (r + 1), X j → Bool) = 2 ^ ((r + 1) * q) := by
          rw [Fintype.card_pi]
          have hterm : ∀ j : Fin (r + 1), Fintype.card (X j → Bool) = 2 ^ q :=
            fun j => by simp [hcard j]
          simp only [hterm, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          rw [← pow_mul, mul_comm]
        have hcard_view : ∀ i : Fin (r + 1),
            Fintype.card (NOF.View (fun j => X j → Bool) i) = 2 ^ (r * q) := by
          intro i
          unfold NOF.View
          rw [Fintype.card_pi]
          have hterm : ∀ j : {j : Fin (r + 1) // j ≠ i}, Fintype.card (X j.val → Bool) = 2 ^ q :=
            fun j => by simp [hcard j.val]
          simp only [hterm, Finset.prod_const, Finset.card_univ]
          have hcompl : Fintype.card {j : Fin (r + 1) // j ≠ i} = r := by simp
          rw [hcompl, ← pow_mul, mul_comm]
        have hcard_phi :
            Fintype.card (∀ i : Fin (r + 1), NOF.View (fun j => X j → Bool) i → Bool) =
              2 ^ ((r + 1) * 2 ^ (r * q)) := by
          rw [Fintype.card_pi]
          have hterm : ∀ i : Fin (r + 1),
              Fintype.card (NOF.View (fun j => X j → Bool) i → Bool) = 2 ^ (2 ^ (r * q)) :=
            fun i => by simp [hcard_view i]
          simp only [hterm, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          rw [← pow_mul, mul_comm]
        have ht_exp : tOf r ^ 2 * ((2 ^ ((r + 1) * q) : ℕ) : ℝ) / 2 = (2 : ℝ) ^ E := by
          have hE_def : E = (r + 1) * q - (2 * m + 1) := rfl
          have hsplit : (r + 1) * q = E + (2 * m + 1) := by omega
          rw [Nat.cast_pow, Nat.cast_ofNat, hsplit, pow_add]
          change ((1 / 2 : ℝ) ^ m) ^ 2 * ((2 : ℝ) ^ E * (2 : ℝ) ^ (2 * m + 1)) / 2 = (2 : ℝ) ^ E
          rw [← pow_mul, mul_comm m 2, one_div, inv_pow, pow_succ]
          have hne : (2 : ℝ) ^ (2 * m) ≠ 0 := by positivity
          field_simp
        have hexp_bound : Real.exp (-((2 : ℝ) ^ E)) ≤ ((2 : ℝ) ^ (2 ^ E))⁻¹ := by
          have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
          have hpow : (2 : ℝ) ^ (2 ^ E) ≤ Real.exp (2 ^ E : ℕ) :=
            (pow_le_pow_left₀ zero_le_two h2e (2 ^ E)).trans_eq (by simp)
          rw [show (2 : ℝ) ^ E = ((2 ^ E : ℕ) : ℝ) by norm_cast, Real.exp_neg]
          exact inv_anti₀ (by positivity) hpow
        have hcyl_le : ∀ φ, ((badCyl X φ).card : ℝ) ≤
            2 * (Fintype.card ℱ : ℝ) * ((2 : ℝ) ^ (2 ^ E))⁻¹ := by
          intro φ
          have hc := card_bad_cylinder_le hdisj z₀ φ ht_pos
          rw [hcard_Y, ht_exp] at hc
          exact hc.trans (mul_le_mul_of_nonneg_left hexp_bound (by positivity))
        calc ((Finset.univ.biUnion fun φ => badCyl X φ).card : ℝ)
            ≤ ∑ φ, ((badCyl X φ).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
          _ ≤ Finset.univ.card • (2 * (Fintype.card ℱ : ℝ) * ((2 : ℝ) ^ (2 ^ E))⁻¹) :=
              Finset.sum_le_card_nsmul _ _ _ fun φ _ => hcyl_le φ
          _ = (2 : ℝ) ^ ((r + 1) * 2 ^ (r * q)) *
                (2 * (Fintype.card ℱ : ℝ) * ((2 : ℝ) ^ (2 ^ E))⁻¹) := by
              rw [nsmul_eq_mul, Finset.card_univ, hcard_phi, Nat.cast_pow, Nat.cast_ofNat]
      have hcard_goodX : ((goodX r).card : ℝ) ≤ (2 : ℝ) ^ (n * (r + 1)) := by
        exact_mod_cast (Finset.card_le_univ _).trans_eq
          (by simp [← pow_mul] : Fintype.card (Fin (r + 1) → Finset (Fin n)) = 2 ^ (n * (r + 1)))
      set K := 1 + n * (r + 1) + (r + 1) * 2 ^ (r * q)
      have hK_inv : (2 : ℝ) ^ K * ((2 : ℝ) ^ (2 ^ E))⁻¹ ≤ ((2 : ℝ) ^ (n + 1))⁻¹ := by
        rw [← div_eq_mul_inv, div_le_iff₀ (by positivity), ← div_eq_inv_mul,
          le_div_iff₀ (by positivity), ← pow_add]
        exact pow_le_pow_right₀ one_le_two (by omega)
      calc ((badR r).card : ℝ)
          ≤ ∑ X ∈ goodX r, ((Finset.univ.biUnion fun φ => badCyl X φ).card : ℝ) := by
            exact_mod_cast Finset.card_biUnion_le
        _ ≤ (goodX r).card • ((2 : ℝ) ^ ((r + 1) * 2 ^ (r * q)) *
              (2 * (Fintype.card ℱ : ℝ) * ((2 : ℝ) ^ (2 ^ E))⁻¹)) :=
            Finset.sum_le_card_nsmul _ _ _ hbadX_le
        _ ≤ (2 : ℝ) ^ (n * (r + 1)) * ((2 : ℝ) ^ ((r + 1) * 2 ^ (r * q)) *
              (2 * (Fintype.card ℱ : ℝ) * ((2 : ℝ) ^ (2 ^ E))⁻¹)) := by
            rw [nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hcard_goodX (by positivity)
        _ = (Fintype.card ℱ : ℝ) * ((2 : ℝ) ^ K * ((2 : ℝ) ^ (2 ^ E))⁻¹) := by
            dsimp only [K]
            rw [pow_add, pow_add, pow_one]
            ring
        _ ≤ (Fintype.card ℱ : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ :=
            mul_le_mul_of_nonneg_left hK_inv (by positivity)
    have hR_card : (Rset.card : ℝ) < (2 : ℝ) ^ (n + 1) := by
      have hlt : n < 2 ^ (n + 1) :=
        Nat.lt_two_pow_self.trans (Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self n))
      exact_mod_cast ((Finset.card_filter_le _ _).trans_eq (by simp)).trans_lt hlt
    have htot_lt : (badTotal.card : ℝ) < Fintype.card ℱ := by
      calc (badTotal.card : ℝ)
          ≤ ∑ r ∈ Rset, ((badR r).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
        _ ≤ Rset.card • ((Fintype.card ℱ : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) :=
            Finset.sum_le_card_nsmul _ _ _ hbadR_le
        _ < (2 : ℝ) ^ (n + 1) * ((Fintype.card ℱ : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹) := by
            rw [nsmul_eq_mul]; exact mul_lt_mul_of_pos_right hR_card (by positivity)
        _ = Fintype.card ℱ := by field_simp
    have hcard_lt : badTotal.card < (Finset.univ : Finset ℱ).card := by
      rw [Finset.card_univ]; exact_mod_cast htot_lt
    obtain ⟨f, -, hf_good⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard_lt
    refine ⟨f, fun r hr1 hr_log X hdisj hcard => ?_⟩
    have hr_le_n : r ≤ n := by have := Nat.log_le_self 2 n; omega
    have hrR : r ∈ Rset :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hr1, hr_le_n⟩, hr_log⟩
    have hX_good : X ∈ goodX r :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ X, hdisj, hcard⟩
    have hdisc_le : NOF.discrepancy (PMF.uniformOfFintype (∀ j : Fin (r + 1), X j → Bool))
        (fun y => f (embedBlocks X z₀ y)) ≤ tOf r := by
      refine ciSup_le fun φ => not_lt.mp fun hgt => hf_good (Finset.mem_biUnion.mpr ⟨r, hrR,
        Finset.mem_biUnion.mpr ⟨X, hX_good, Finset.mem_biUnion.mpr ⟨φ, Finset.mem_univ φ,
          Finset.mem_filter.mpr ⟨Finset.mem_univ f, hgt.le⟩⟩⟩⟩)
    set q := n / (4 * r)
    set m := q / 4 + 1
    have h4 : 4 ≤ 2 ^ (r + 1) := Nat.pow_le_pow_right two_pos (by omega : 2 ≤ r + 1)
    have hexp_q : q ≤ m * 2 ^ (r + 1) := (show q ≤ m * 4 by omega).trans (Nat.mul_le_mul_left m h4)
    have hhalf_le : (1 / 2 : ℝ) ≤ 1 - 2 / (2 : ℝ) ^ (r + 1) := by
      have h4R : (4 : ℝ) ≤ 2 ^ (r + 1) := by exact_mod_cast h4
      rw [le_sub_comm, div_le_iff₀ (by positivity)]
      linarith
    calc NOF.discrepancy (PMF.uniformOfFintype (∀ j : Fin (r + 1), X j → Bool))
          (fun y => f (embedBlocks X z₀ y)) ^ (2 ^ (r + 1))
        ≤ tOf r ^ (2 ^ (r + 1)) :=
          pow_le_pow_left₀ NOF.discrepancy_nonneg hdisc_le (2 ^ (r + 1))
      _ = (1 / 2 : ℝ) ^ (m * 2 ^ (r + 1)) := by
          change ((1 / 2 : ℝ) ^ m) ^ (2 ^ (r + 1)) = _
          rw [← pow_mul]
      _ ≤ (1 / 2 : ℝ) ^ q := pow_le_pow_of_le_one (by norm_num) (by norm_num) hexp_q
      _ ≤ (1 - 2 / (2 : ℝ) ^ (r + 1)) ^ q := pow_le_pow_left₀ (by norm_num) hhalf_le q

/-- **Unconditional `Ω(n log n)` fan-in-two Boolean formula leaf-size lower bound.** For every
`n : ℕ`, there exists `f : (Fin n → Bool) → Bool` such that *every* fan-in-two Boolean formula
`F : Formula σ n` over *any* signature `σ` and interpretation `I` computing `f` satisfies
`n * (Nat.log 2 n - 12) ≤ 16 * F.leafSize`. -/
theorem exists_function_mul_log_le_leafSize (n : ℕ) :
    ∃ f : (Fin n → Bool) → Bool,
      ∀ {σ : Signature} (I : Interpretation σ Bool) {F : Formula σ n},
        F.FanInAtMost 2 → F.Computes I f → n * (Nat.log 2 n - 12) ≤ 16 * F.leafSize := by
  obtain ⟨f, hf⟩ := exists_balanced_nof_discrepancy n
  exact ⟨f, fun {_σ} I {_F} hfan hcomp =>
    mul_log_le_leafSize_of_balanced_discrepancy I hfan hcomp hf⟩

end Cslib.Circuits.Frontier
