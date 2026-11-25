/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.Circuit.Simulation
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Nat.Dist
public import Mathlib.Data.Nat.Log
public import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.AdditiveDefs
import CslibFrontier.Computability.Circuit.Simulation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.Synthesis
import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.SectionPairing
import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.BlockCols
import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.ParameterBounds

/-!
# Active-square additive matrix bounds ([Sergeev, Lemma 1][Sergeev2013AdditiveMultiplicative])

Proves both the explicit `(s, p)` active-square additive matrix synthesis bound
(`Additive.exists_circuit_matrix_le_bound`) and its asymptotic form
(`Additive.exists_circuit_matrix_le`).

## Main results

* `Cslib.Circuits.Additive.exists_circuit_matrix_le_bound`: explicit active-square additive matrix
  synthesis bound ([Sergeev, Lemma 1, pp. 2–3][Sergeev2013AdditiveMultiplicative]).
* `Cslib.Circuits.Additive.exists_circuit_matrix_le`: asymptotic active-square additive matrix
  bound `S(A) / (2 log₂ m) + ε (m + n)² / log₂ m`
  ([Sergeev, Lemma 1, p. 2][Sergeev2013AdditiveMultiplicative]).

## References

* [I. S. Sergeev, *A relation between additive and multiplicative complexity of Boolean
  functions*][Sergeev2013AdditiveMultiplicative]
-/

public section

open Finset

namespace Cslib.Circuits

namespace Additive

section MatrixSynthesis

variable {G : Type*} [AddCommMonoid G] {m n : ℕ}

/-- Each nonempty full block of width `s ≤ Nat.log 2 m + 1` in row `r` activates all `s` entries
of that block in `A.activeSquare`. -/
private theorem mul_sum_hasFullCol_le_activeSquare (A : Matrix (Fin m) (Fin n) Bool)
    {s : ℕ} (hs_log : s ≤ Nat.log 2 m + 1) :
    s * (∑ r : Fin m, #{c : FullCol n s | hasFullCol A s r c = true}) ≤ A.activeSquare := by
  have hrow (r : Fin m) :
      #{c : FullCol n s | hasFullCol A s r c = true} =
        #{q : Fin (n / s) | (fullRowPattern A s r q).Nonempty} := by
    let activeQ := univ.filter fun q : Fin (n / s) => (fullRowPattern A s r q).Nonempty
    let φ : {q : Fin (n / s) // q ∈ activeQ} → FullCol n s :=
      fun q => (q.1, ⟨fullRowPattern A s r q.1, (mem_filter.mp q.2).2⟩)
    have hφ_inj : Function.Injective φ := fun q₁ q₂ h =>
      Subtype.ext (congrArg Prod.fst h)
    have himg : univ.filter (fun c : FullCol n s => hasFullCol A s r c = true) =
        univ.image φ := by
      ext ⟨q, T, hT⟩
      simp only [hasFullCol, FullCol.block, FullCol.subset, decide_eq_true_eq, mem_filter, mem_univ,
        true_and, mem_image, φ, Prod.mk.injEq, Subtype.mk.injEq]
      constructor
      · rintro rfl
        exact ⟨⟨q, mem_filter.mpr ⟨mem_univ q, hT⟩⟩, rfl, rfl⟩
      · rintro ⟨⟨q', _⟩, rfl, rfl⟩
        rfl
    rw [himg, card_image_of_injective _ hφ_inj, card_univ, Fintype.card_coe]
  simp_rw [hrow]
  rw [mul_sum]
  let blockPts (r : Fin m) : Finset (Fin m × Fin n) :=
    (univ.filter fun q : Fin (n / s) => (fullRowPattern A s r q).Nonempty).biUnion fun q =>
      univ.image fun a : Fin s => (r, fullBlockEmb q a)
  have hcard_pts (r : Fin m) :
      s * #{q : Fin (n / s) | (fullRowPattern A s r q).Nonempty} = #(blockPts r) := by
    dsimp only [blockPts]
    rw [card_biUnion]
    · have hcard_one (q : Fin (n / s)) :
          #(univ.image fun a : Fin s => (r, fullBlockEmb q a)) = s := by
        rw [card_image_of_injective]
        · simp
        · intro a₁ a₂ h
          exact (fullBlockEmb q).injective (congrArg Prod.snd h)
      rw [sum_congr rfl fun q _ => hcard_one q, sum_const, smul_eq_mul, mul_comm]
    · intro q₁ _ q₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro p hp₁ hp₂
      obtain ⟨a₁, _, rfl⟩ := mem_image.mp hp₁
      obtain ⟨a₂, _, heq⟩ := mem_image.mp hp₂
      have hemb : fullBlockEmb q₂ a₂ = fullBlockEmb q₁ a₁ := congrArg Prod.snd heq
      exact hne (Fin.ext (by rw [← fullBlockEmb_div q₁ a₁, ← hemb, fullBlockEmb_div q₂ a₂]))
  simp_rw [hcard_pts]
  have hdisj_rows : ((univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint blockPts := by
    intro r₁ _ r₂ _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    dsimp only [blockPts] at hp₁ hp₂
    rw [mem_biUnion] at hp₁ hp₂
    obtain ⟨_, _, hp₁⟩ := hp₁
    obtain ⟨_, _, hp₂⟩ := hp₂
    obtain ⟨_, _, rfl⟩ := mem_image.mp hp₁
    obtain ⟨_, _, heq⟩ := mem_image.mp hp₂
    exact hne (congrArg Prod.fst heq).symm
  rw [← card_biUnion hdisj_rows]
  refine card_le_card fun p hp => ?_
  rw [mem_biUnion] at hp
  obtain ⟨r, _, hp⟩ := hp
  dsimp only [blockPts] at hp
  rw [mem_biUnion] at hp
  obtain ⟨q, hq, hp⟩ := hp
  obtain ⟨a, _, rfl⟩ := mem_image.mp hp
  obtain ⟨a₀, ha₀⟩ := (mem_filter.mp hq).2
  have hA₀ := (mem_filter.mp ha₀).2
  refine mem_filter.mpr ⟨mem_univ _, fullBlockEmb q a₀, hA₀, ?_⟩
  change Nat.dist (q.1 * s + a.1) (q.1 * s + a₀.1) ≤ Nat.log 2 m
  unfold Nat.dist
  have := a.isLt
  have := a₀.isLt
  omega


private def matrixPairVal (A : Matrix (Fin m) (Fin n) Bool) (s p : ℕ)
    (up : ℕ × (Fin m × Fin m)) (x : Fin n → G) : G :=
  ∑ c ∈ pairedCols (hasFullCol A s) p up.1 up.2.1 up.2.2, fullColVal c x

private def matrixOddVal (A : Matrix (Fin m) (Fin n) Bool) (s p : ℕ)
    (r : Fin m) (x : Fin n → G) : G :=
  ∑ c ∈ oddCols (hasFullCol A s) p r, fullColVal c x


private def matrixRowParts (A : Matrix (Fin m) (Fin n) Bool) (s p : ℕ) (r : Fin m) :
    Finset (Fin m ⊕ Bool) :=
  ((sectionPeers p r).filter fun r' =>
      (pairedCols (hasFullCol A s) p (r.1 / p) (min r r') (max r r')).Nonempty).map
        Function.Embedding.inl ∪
    (if (oddCols (hasFullCol A s) p r).Nonempty then {Sum.inr false} else ∅) ∪
    (if (matrixTailSet A s r).Nonempty then {Sum.inr true} else ∅)

private def matrixPartVal (A : Matrix (Fin m) (Fin n) Bool) (s p : ℕ) (r : Fin m) :
    Fin m ⊕ Bool → (Fin n → G) → G
  | .inl r' => matrixPairVal A s p (r.1 / p, (min r r', max r r'))
  | .inr false => matrixOddVal A s p r
  | .inr true => fun x => ∑ j ∈ matrixTailSet A s r, x j

private theorem card_matrixRowParts_le (A : Matrix (Fin m) (Fin n) Bool) (s : ℕ)
    {p : ℕ} (hp : 0 < p) (r : Fin m) :
    #(matrixRowParts A s p r) ≤ p + 1 := by
  unfold matrixRowParts
  set peerPart := ((sectionPeers p r).filter fun r' =>
      (pairedCols (hasFullCol A s) p (r.1 / p) (min r r') (max r r')).Nonempty).map
        Function.Embedding.inl
  set oddPart : Finset (Fin m ⊕ Bool) :=
    if (oddCols (hasFullCol A s) p r).Nonempty then {Sum.inr false} else ∅
  set tailPart : Finset (Fin m ⊕ Bool) :=
    if (matrixTailSet A s r).Nonempty then {Sum.inr true} else ∅
  have hc1 : #peerPart ≤ p - 1 := by
    rw [card_map]
    exact (card_le_card (filter_subset _ _)).trans (card_sectionPeers_le hp r)
  have hc2 : #oddPart ≤ 1 := by
    dsimp only [oddPart]
    split_ifs <;> simp
  have hc3 : #tailPart ≤ 1 := by
    dsimp only [tailPart]
    split_ifs <;> simp
  have hu1 := card_union_le (peerPart ∪ oddPart) tailPart
  have hu2 := card_union_le peerPart oddPart
  omega


private theorem sum_matrixRowParts_eq (A : Matrix (Fin m) (Fin n) Bool) {s : ℕ} (hs : 0 < s)
    (p : ℕ) (r : Fin m) (x : Fin n → G) :
    (∑ k ∈ matrixRowParts A s p r, matrixPartVal A s p r k x) =
      ∑ j : Fin n, if A r j then x j else 0 := by
  unfold matrixRowParts
  set peerPart := ((sectionPeers p r).filter fun r' =>
      (pairedCols (hasFullCol A s) p (r.1 / p) (min r r') (max r r')).Nonempty).map
        Function.Embedding.inl
  set oddPart : Finset (Fin m ⊕ Bool) :=
    if (oddCols (hasFullCol A s) p r).Nonempty then {Sum.inr false} else ∅
  set tailPart : Finset (Fin m ⊕ Bool) :=
    if (matrixTailSet A s r).Nonempty then {Sum.inr true} else ∅
  have hd12 : Disjoint peerPart oddPart := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    obtain ⟨_, _, rfl⟩ := mem_map.mp hz1
    dsimp only [oddPart] at hz2
    split_ifs at hz2 <;> simp at hz2
  have hd123 : Disjoint (peerPart ∪ oddPart) tailPart := by
    rw [Finset.disjoint_left]
    intro z hz12 hz3
    dsimp only [tailPart] at hz3
    split_ifs at hz3 with hne
    · rw [mem_singleton.mp hz3] at hz12
      rcases mem_union.mp hz12 with hz1 | hz2
      · obtain ⟨_, _, habs⟩ := mem_map.mp hz1
        nomatch habs
      · dsimp only [oddPart] at hz2
        split_ifs at hz2 <;> simp at hz2
    · exact notMem_empty _ hz3
  rw [sum_union hd123, sum_union hd12, sum_map]
  have hpeers_sum :
      (∑ r' ∈ (sectionPeers p r).filter (fun r' =>
          (pairedCols (hasFullCol A s) p (r.1 / p) (min r r') (max r r')).Nonempty),
        matrixPairVal A s p (r.1 / p, (min r r', max r r')) x) =
      ∑ r' ∈ sectionPeers p r, matrixPairVal A s p (r.1 / p, (min r r', max r r')) x := by
    rw [sum_filter]
    refine sum_congr rfl fun r' _ => ?_
    split_ifs with hne
    · rfl
    · rw [not_nonempty_iff_eq_empty] at hne
      simp [matrixPairVal, hne]
  have hodd_sum :
      (∑ k ∈ oddPart, matrixPartVal A s p r k x) = matrixOddVal A s p r x := by
    dsimp only [oddPart]
    split_ifs with hne
    · simp [matrixPartVal]
    · rw [not_nonempty_iff_eq_empty] at hne
      simp [matrixOddVal, hne]
  have htail_sum :
      (∑ k ∈ tailPart, matrixPartVal A s p r k x) = ∑ j ∈ matrixTailSet A s r, x j := by
    dsimp only [tailPart]
    split_ifs with hne
    · simp [matrixPartVal]
    · rw [not_nonempty_iff_eq_empty] at hne
      simp [hne]
  change (∑ r' ∈ (sectionPeers p r).filter _,
        matrixPairVal A s p (r.1 / p, (min r r', max r r')) x) +
      (∑ k ∈ oddPart, matrixPartVal A s p r k x) +
      (∑ k ∈ tailPart, matrixPartVal A s p r k x) = _
  rw [hpeers_sum, hodd_sum, htail_sum]
  have hfull := (sum_filter_hasCol_eq (hasFullCol A s) p (fun c => fullColVal c x) r).symm
  unfold matrixPairVal matrixOddVal
  rw [hfull, sum_row_eq_fullCol_add_tail A hs r x]

/-- **Explicit active-square additive matrix bound**
([Sergeev, Lemma 1, pp. 2–3][Sergeev2013AdditiveMultiplicative]):
over any additive commutative monoid `G`, every `m × n` Boolean matrix `A` is computed by an
additive `{0, +}`-circuit of size at most `matrixBound A s p` whenever `0 < s ≤ Nat.log 2 m + 1`
and `0 < p` (`AddCommMonoid G` supplies `0` for all-zero rows on total output wires, whereas
Sergeev's p. 2 footnote 4 states a commutative semigroup `(G, +)` and the construction here emits
zero `Op.zero` gates whenever every row of `A` has a `true` entry). -/
theorem exists_circuit_matrix_le_bound (G : Type*) [AddCommMonoid G]
    (A : Matrix (Fin m) (Fin n) Bool) {s p : ℕ} (hs : 0 < s) (hs_log : s ≤ Nat.log 2 m + 1)
    (hp : 0 < p) :
    ∃ c : Circuit signature n m,
      c.Computes (interpretation G) (fun x i => ∑ j : Fin n, if A i j then x j else 0) ∧
      c.size ≤ matrixBound A s p := by
  classical
  rcases m.eq_zero_or_pos with rfl | hm
  · exact ⟨Circuit.wiring signature Fin.elim0, fun _ => funext fun i => i.elim0, by simp⟩
  let I := interpretation G
  let w0 : Op → ℕ := fun _ => 0
  have hArity : signature.Arity Op.add = 2 := rfl
  have hEval : ∀ args : Fin (signature.Arity Op.add) → G, I Op.add args = args 0 + args 1 :=
    fun _ => rfl
  have hZeroW : w0 Op.add = 0 := rfl
  -- Step 1: All nonempty subset sums in each width-`s` input block.
  have hgroup := all_group_subSums (I := I) (w := w0) (s := inputs n) hs hArity hEval hZeroW
    (fun j (x : Fin n → G) => x j) (fun j => ⟨j, rfl⟩)
  set groupSet : Set ((Fin n → G) → G) :=
    {f | ∃ (q : ℕ) (T : Finset (Fin n)),
      T.Nonempty ∧ (∀ j ∈ T, j.1 / s = q) ∧ f = fun x => ∑ j ∈ T, x j}
  have hcolVal_mem (c : FullCol n s) : fullColVal c ∈ inputs n ∪ groupSet := by
    refine Or.inr ⟨c.1.1, c.2.1.map (fullBlockEmb c.1), c.2.2.map, ?_, ?_⟩
    · intro j hj
      obtain ⟨a, _, rfl⟩ := mem_map.mp hj
      exact fullBlockEmb_div c.1 a
    · funext x
      rw [sum_map]
      rfl
  -- Step 2: Nonempty paired sums.
  set pairIdx : Finset (ℕ × (Fin m × Fin m)) :=
    ((range (m ⌈/⌉ p)).product univ).filter fun up =>
      (pairedCols (hasFullCol A s) p up.1 up.2.1 up.2.2).Nonempty
  have hpair_step (up : ℕ × (Fin m × Fin m)) (hup : up ∈ pairIdx) :
      CostSynthesis I w0 (inputs n ∪ groupSet) {matrixPairVal A s p up}
        (#(pairedCols (hasFullCol A s) p up.1 up.2.1 up.2.2) - 1) 0 :=
    nonempty_sum_of_mem hArity hEval hZeroW _ (mem_filter.mp hup).2 fullColVal
      fun c _ => hcolVal_mem c
  have hpairs := CostSynthesis.biUnion pairIdx (fun up => {matrixPairVal A s p up})
    (fun up => #(pairedCols (hasFullCol A s) p up.1 up.2.1 up.2.2) - 1) (fun _ => 0) hpair_step
  have hpairs_cost :
      ∑ up ∈ pairIdx, (#(pairedCols (hasFullCol A s) p up.1 up.2.1 up.2.2) - 1) ≤
        A.activeSquare / (2 * s) := by
    have h₁ : ∑ up ∈ pairIdx, (#(pairedCols (hasFullCol A s) p up.1 up.2.1 up.2.2) - 1) ≤
        ∑ u ∈ range (m ⌈/⌉ p), ∑ pair : Fin m × Fin m,
          #(pairedCols (hasFullCol A s) p u pair.1 pair.2) :=
      ((sum_le_sum_of_subset (filter_subset _ _)).trans
        (sum_le_sum fun _ _ => Nat.sub_le _ _)).trans_eq (sum_product _ _ _)
    apply (Nat.le_div_iff_mul_le (Nat.mul_pos two_pos hs)).mpr
    have h₂ := two_mul_sum_card_pairedCols_le (hasFullCol A s) hp
    have h₃ := mul_sum_hasFullCol_le_activeSquare A hs_log
    nlinarith only [h₁, h₂, h₃]
  -- Step 3: Nonempty odd-one sums.
  set oddIdx : Finset (Fin m) :=
    univ.filter fun r : Fin m => (oddCols (hasFullCol A s) p r).Nonempty
  have hodd_step (r : Fin m) (hr : r ∈ oddIdx) :
      CostSynthesis I w0 (inputs n ∪ groupSet) {matrixOddVal A s p r}
        (#(oddCols (hasFullCol A s) p r) - 1) 0 :=
    nonempty_sum_of_mem hArity hEval hZeroW _ (mem_filter.mp hr).2 fullColVal
      fun c _ => hcolVal_mem c
  have hodds := CostSynthesis.biUnion oddIdx (fun r => {matrixOddVal A s p r})
    (fun r => #(oddCols (hasFullCol A s) p r) - 1) (fun _ => 0) hodd_step
  have hodds_cost :
      ∑ r ∈ oddIdx, (#(oddCols (hasFullCol A s) p r) - 1) ≤ (m ⌈/⌉ p) * 2 ^ s * (n ⌈/⌉ s) := by
    calc ∑ r ∈ oddIdx, (#(oddCols (hasFullCol A s) p r) - 1)
        ≤ ∑ r : Fin m, #(oddCols (hasFullCol A s) p r) :=
          (sum_le_sum_of_subset (filter_subset _ _)).trans
            (sum_le_sum fun _ _ => Nat.sub_le _ _)
      _ ≤ (m ⌈/⌉ p) * Fintype.card (FullCol n s) :=
          sum_card_oddCols_le (hasFullCol A s) hp
      _ ≤ (m ⌈/⌉ p) * (2 ^ s * (n ⌈/⌉ s)) :=
          Nat.mul_le_mul_left _ (card_fullCol_le n s hs)
      _ = (m ⌈/⌉ p) * 2 ^ s * (n ⌈/⌉ s) := by ring
  set stage3Set : Set ((Fin n → G) → G) :=
    inputs n ∪ (groupSet ∪
      ((⋃ up ∈ pairIdx, {matrixPairVal A s p up}) ∪ ⋃ r ∈ oddIdx, {matrixOddVal A s p r}))
  have hpre : CostSynthesis I w0 (inputs n) stage3Set
      ((n * 2 ^ s) / s + A.activeSquare / (2 * s) + (m ⌈/⌉ p) * 2 ^ s * (n ⌈/⌉ s)) 0 := by
    have h123 := (CostSynthesis.of_subset (I := I) (w := w0) Set.Subset.rfl).union
      (hgroup.comp (hpairs.union hodds))
    exact h123.mono Set.Subset.rfl Set.Subset.rfl
      (by linarith only [hpairs_cost, hodds_cost]) (by simp)
  -- Step 4: Row assembly.
  have hpartVal_mem (r : Fin m) (k : Fin m ⊕ Bool) (hk : k ∈ matrixRowParts A s p r) :
      matrixPartVal A s p r k ∈ stage3Set := by
    unfold matrixRowParts at hk
    rcases mem_union.mp hk with hk12 | hktail
    · rcases mem_union.mp hk12 with hkpeer | hkodd
      · obtain ⟨r', hr', rfl⟩ := mem_map.mp hkpeer
        have hne := (mem_filter.mp hr').2
        refine Or.inr (Or.inr (Or.inl ?_))
        rw [Set.mem_iUnion₂]
        exact ⟨(r.1 / p, (min r r', max r r')),
          mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (div_lt_ceilDiv r.isLt hp), mem_univ _⟩,
            hne⟩, rfl⟩
      · split_ifs at hkodd with hne
        · rw [mem_singleton.mp hkodd]
          refine Or.inr (Or.inr (Or.inr ?_))
          rw [Set.mem_iUnion₂]
          exact ⟨r, mem_filter.mpr ⟨mem_univ r, hne⟩, rfl⟩
        · exact (notMem_empty _ hkodd).elim
    · split_ifs at hktail with hne
      · rw [mem_singleton.mp hktail]
        exact Or.inr (Or.inl ⟨n / s, matrixTailSet A s r, hne,
          fun _ hj => div_eq_of_mem_matrixTailSet hj, rfl⟩)
      · exact (notMem_empty _ hktail).elim
  let rowFn (r : Fin m) (x : Fin n → G) : G := ∑ j : Fin n, if A r j then x j else 0
  set nonempRows : Finset (Fin m) := univ.filter fun r : Fin m => (matrixRowParts A s p r).Nonempty
  have hrow_synth (r : Fin m) (hr : r ∈ nonempRows) :
      CostSynthesis I w0 stage3Set {rowFn r} p 0 := by
    have hne := (mem_filter.mp hr).2
    have hs_r := nonempty_sum_of_mem hArity hEval hZeroW (matrixRowParts A s p r) hne
      (matrixPartVal A s p r) (hpartVal_mem r)
    have hfun : (fun x => ∑ k ∈ matrixRowParts A s p r, matrixPartVal A s p r k x) = rowFn r :=
      funext (sum_matrixRowParts_eq A hs p r)
    rw [hfun] at hs_r
    have hcard := card_matrixRowParts_le A s hp r
    exact hs_r.mono Set.Subset.rfl Set.Subset.rfl (by omega) le_rfl
  by_cases hall_ne : #nonempRows = m
  · have hrows := CostSynthesis.biUnion nonempRows (fun r => {rowFn r})
      (fun _ => p) (fun _ => 0) hrow_synth
    have htot := hpre.trans (hrows.mono Set.subset_union_right Set.Subset.rfl le_rfl le_rfl)
    have hall_univ : nonempRows = univ := eq_univ_of_card nonempRows (by simp [hall_ne])
    have htarget : Set.range rowFn ⊆ ⋃ r ∈ nonempRows, {rowFn r} := by
      rintro _ ⟨r, rfl⟩
      rw [hall_univ, Set.mem_iUnion₂]
      exact ⟨r, mem_univ r, rfl⟩
    have hcost :
        ((n * 2 ^ s) / s + A.activeSquare / (2 * s) + (m ⌈/⌉ p) * 2 ^ s * (n ⌈/⌉ s)) +
          ∑ _ ∈ nonempRows, p ≤ matrixBound A s p := by
      rw [sum_const, smul_eq_mul, hall_ne]
      unfold matrixBound
      omega
    obtain ⟨c, hc, hsize, -⟩ :=
      (htot.mono Set.Subset.rfl htarget hcost (wa' := 0) (by simp)).exists_circuit_outputs
    exact ⟨c, hc, hsize⟩
  · have hle_m1 : #nonempRows ≤ m - 1 := by
      have hle : #nonempRows ≤ m := (card_filter_le _ _).trans_eq (by simp)
      omega
    have hzero_gate : CostSynthesis I w0 stage3Set {fun _ => (0 : G)} 1 0 := by
      simpa only [I, w0, interpretation_zero] using
        CostSynthesis.gate (I := I) (w := w0) (s := stage3Set) Op.zero Fin.elim0 fun i => i.elim0
    have hrows := CostSynthesis.biUnion nonempRows (fun r => {rowFn r})
      (fun _ => p) (fun _ => 0) hrow_synth
    have htot := hpre.trans
      ((hzero_gate.union hrows).mono Set.subset_union_right Set.Subset.rfl le_rfl le_rfl)
    have htarget : Set.range rowFn ⊆ {fun _ => (0 : G)} ∪ ⋃ r ∈ nonempRows, {rowFn r} := by
      rintro _ ⟨r, rfl⟩
      by_cases hr : r ∈ nonempRows
      · refine Or.inr ?_
        rw [Set.mem_iUnion₂]
        exact ⟨r, hr, rfl⟩
      · refine Or.inl ?_
        have hempty : matrixRowParts A s p r = ∅ := by
          rcases (matrixRowParts A s p r).eq_empty_or_nonempty with h0 | hne
          · exact h0
          · exact (hr (mem_filter.mpr ⟨mem_univ r, hne⟩)).elim
        funext x
        dsimp only [rowFn]
        rw [← sum_matrixRowParts_eq A hs p r x, hempty, sum_empty]
    have hcost4 : 1 + ∑ _ ∈ nonempRows, p ≤ m * p := by
      rw [sum_const, smul_eq_mul]
      calc 1 + #nonempRows * p ≤ p + (m - 1) * p :=
            Nat.add_le_add hp (Nat.mul_le_mul_right p hle_m1)
        _ = (1 + (m - 1)) * p := by ring
        _ = m * p := by rw [Nat.add_sub_of_le hm]
    have hcost :
        ((n * 2 ^ s) / s + A.activeSquare / (2 * s) + (m ⌈/⌉ p) * 2 ^ s * (n ⌈/⌉ s)) +
          (1 + ∑ _ ∈ nonempRows, p) ≤ matrixBound A s p := by
      unfold matrixBound
      omega
    obtain ⟨c, hc, hsize, -⟩ :=
      (htot.mono Set.Subset.rfl htarget hcost (wa' := 0) (by simp)).exists_circuit_outputs
    exact ⟨c, hc, hsize⟩

end MatrixSynthesis

/-- **Asymptotic active-square additive matrix bound**
([Sergeev, Lemma 1, p. 2][Sergeev2013AdditiveMultiplicative]):
for every `ε > 0`, for all sufficiently large `m + n` with `2 ≤ m`, every `m × n` Boolean matrix `A`
over any additive commutative monoid `G` is computed by an additive `{0, +}`-circuit of size at most
`A.activeSquare / (2 * Real.logb 2 m) + ε * ((m + n) ^ 2 / Real.logb 2 m)`. -/
theorem exists_circuit_matrix_le {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ {m n : ℕ}, 2 ≤ m → N₀ ≤ m + n →
      ∀ (G : Type*) [AddCommMonoid G] (A : Matrix (Fin m) (Fin n) Bool),
        ∃ c : Circuit signature n m,
          c.Computes (interpretation G) (fun x i => ∑ j : Fin n, if A i j then x j else 0) ∧
          (c.size : ℝ) ≤
            (A.activeSquare : ℝ) / (2 * Real.logb 2 m) +
              ε * ((m + n : ℝ) ^ 2 / Real.logb 2 m) := by
  let C : ℕ := ⌈((4 + 2 * 34 : ℕ) : ℝ) / ε⌉₊ + 10
  obtain ⟨L₁, hL₁8, _, hL₁⟩ := exists_log_threshold C
  let M₁ : ℕ := 2 ^ L₁
  have hM₁_ge2 : 2 ≤ M₁ := by
    have : 2 ^ 1 ≤ 2 ^ L₁ := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa [M₁] using this
  let B : ℝ := (3 * (M₁ : ℝ) + 3) * Real.logb 2 M₁
  let N₀ : ℕ := M₁ + ⌈B / ε⌉₊ + 1
  refine ⟨N₀, fun {m n} hm hN₀ G _ A => ?_⟩
  have hlogm_ge1 : 1 ≤ Real.logb 2 m := logb_two_ge_one hm
  have hlogm_pos : 0 < Real.logb 2 m := lt_of_lt_of_le zero_lt_one hlogm_ge1
  by_cases hmM₁ : M₁ ≤ m
  · have hL_ge : L₁ ≤ Nat.log 2 m := Nat.le_log_of_pow_le one_lt_two hmM₁
    obtain ⟨hClog, h6log, hpow2⟩ := hL₁ hL_ge
    have hL8 : 8 ≤ Nat.log 2 m := hL₁8.trans hL_ge
    obtain ⟨hs_pos, hs_le, _, _, _, _⟩ := log_param_props hL8 h6log hpow2
    set L := Nat.log 2 m
    set s := L - 3 * Nat.log 2 L
    set p := m / L ^ 2 + 1
    obtain ⟨c, hc, hsize⟩ := exists_circuit_matrix_le_bound G A hs_pos
      (hs_le.trans (Nat.le_succ L)) (Nat.succ_pos _)
    refine ⟨c, hc, (Nat.cast_le.mpr hsize).trans ?_⟩
    set rem : ℕ := (n * 2 ^ s) / s + m * p + (m ⌈/⌉ p) * 2 ^ s * (n ⌈/⌉ s)
    have hmb_eq : matrixBound A s p = A.activeSquare / (2 * s) + rem := by
      unfold matrixBound rem
      ring
    rw [hmb_eq, Nat.cast_add]
    have hSU : A.activeSquare ≤ (m + n) ^ 2 :=
      A.activeSquare_le_mul.trans (by nlinarith)
    have hbound := div_two_sub_add_rem_le hε hL8 h6log hpow2 hClog hSU
      (matrixRem_mul_sq_le m n hL8 h6log hpow2)
    have hsq_cast : (((m + n) ^ 2 : ℕ) : ℝ) = (m + n : ℝ) ^ 2 := by push_cast; ring
    rw [hsq_cast] at hbound
    exact hbound
  · -- Bounded-row regime `2 ≤ m < M₁`: take `s = 1` and `p = 1`.
    have hm_lt : m < M₁ := Nat.lt_of_not_ge hmM₁
    obtain ⟨c, hc, hsize⟩ := exists_circuit_matrix_le_bound G A Nat.one_pos
      (Nat.succ_le_succ (Nat.zero_le _)) Nat.one_pos
    refine ⟨c, hc, (Nat.cast_le.mpr hsize).trans ?_⟩
    have hmb11 : matrixBound A 1 1 ≤ (3 * M₁ + 3) * (m + n) := by
      have hS_mn : A.activeSquare / 2 ≤ m * n :=
        (Nat.div_le_self _ _).trans A.activeSquare_le_mul
      unfold matrixBound
      simp only [ceilDiv_one, pow_one, Nat.div_one, mul_one]
      nlinarith
    have hcast11 : (matrixBound A 1 1 : ℝ) ≤ (3 * (M₁ : ℝ) + 3) * (m + n : ℝ) := by
      exact_mod_cast hmb11
    have hlog_le : Real.logb 2 m ≤ Real.logb 2 M₁ := by
      unfold Real.logb
      exact div_le_div_of_nonneg_right
        (Real.log_le_log (by positivity) (by exact_mod_cast hm_lt.le))
        (Real.log_nonneg (by norm_num))
    have hB_le : B ≤ ε * (m + n : ℝ) := by
      have hceil_B : B / ε ≤ (⌈B / ε⌉₊ : ℝ) := Nat.le_ceil _
      have hmn_ge : (⌈B / ε⌉₊ : ℝ) ≤ (m + n : ℝ) := by
        have : ⌈B / ε⌉₊ ≤ m + n := by omega
        exact_mod_cast this
      have hdiv : B / ε ≤ m + n := hceil_B.trans hmn_ge
      rwa [div_le_iff₀ hε, mul_comm] at hdiv
    have herr_ge : (3 * (M₁ : ℝ) + 3) * (m + n : ℝ) ≤ ε * ((m + n : ℝ) ^ 2 / Real.logb 2 m) := by
      rw [mul_div_assoc', le_div_iff₀ hlogm_pos]
      calc (3 * (M₁ : ℝ) + 3) * (m + n : ℝ) * Real.logb 2 m
          ≤ (3 * (M₁ : ℝ) + 3) * (m + n : ℝ) * Real.logb 2 M₁ :=
            mul_le_mul_of_nonneg_left hlog_le (by positivity)
        _ = B * (m + n : ℝ) := by
            dsimp only [B]
            ring
        _ ≤ (ε * (m + n : ℝ)) * (m + n : ℝ) :=
            mul_le_mul_of_nonneg_right hB_le (by positivity)
        _ = ε * (m + n : ℝ) ^ 2 := by ring
    have hS_nonneg : 0 ≤ (A.activeSquare : ℝ) / (2 * Real.logb 2 m) := by positivity
    linarith

end Additive

end Cslib.Circuits
