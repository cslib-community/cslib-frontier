/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.Circuit.Simulation
public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.Synthesis
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.SectionPairing

/-!
# Internal full-block column encoding and block group-sum synthesis

Internal block-sum combinators (`all_group_subSums`) and compressed full-block column helpers
(`fullBlockEmb`, `fullRowPattern`, `FullCol`, `hasFullCol`, `fullColVal`, `matrixTailSet`,
`sum_fullCol_lt_eq`, `sum_row_eq_fullCol_add_tail`) shared by `AdditiveBound`, `StageParts`,
`StageStep`, and `UpperBound`; never re-exported through `Zhegalkin`.

## Main definitions

* `Cslib.Circuits.Additive.fullBlockEmb`, `fullRowPattern`, `FullCol`, `hasFullCol`,
  `fullColVal`, `matrixTailSet`: compressed width-`s` block columns and trailing columns.

## Main results

* `Cslib.Circuits.all_group_subSums`: width-`s` block subset-sum synthesis bound.
* `Cslib.Circuits.Additive.sum_fullCol_lt_eq`,
  `Cslib.Circuits.Additive.sum_row_eq_fullCol_add_tail`: prefix full-block and full-row sum
  identities.
-/

public section

open Finset

namespace Cslib.Circuits

section GroupSubSums

universe v u
variable {σ : Signature.{v}} {n : ℕ}
variable {G : Type u} [AddCommMonoid G] {I : Interpretation σ G} {w : σ.Op → ℕ}
variable {addOp : σ.Op}

/-- All nonempty subset sums within each width-`width` block of `v : Fin k → (Fin n → G) → G`
cost at most `(k * 2 ^ width) / width` binary addition gates. -/
theorem all_group_subSums {k width : ℕ} (hw : 0 < width)
    (hArity : σ.Arity addOp = 2)
    (hEval : ∀ args : Fin (σ.Arity addOp) → G,
      I addOp args = args ⟨0, by omega⟩ + args ⟨1, by omega⟩)
    (hZeroW : w addOp = 0) {s : Set ((Fin n → G) → G)}
    (v : Fin k → (Fin n → G) → G) (hv : ∀ j, v j ∈ s) :
    CostSynthesis I w s
      {f | ∃ (q : ℕ) (T : Finset (Fin k)),
        T.Nonempty ∧ (∀ j ∈ T, j.1 / width = q) ∧ f = fun x => ∑ j ∈ T, v j x}
      ((k * 2 ^ width) / width) 0 := by
  let B (q : ℕ) := blockIndices k width q
  let emb (q : ℕ) : Fin #(B q) ↪o Fin k := (B q).orderEmbOfFin rfl
  let blockTarget (q : ℕ) : Set ((Fin n → G) → G) :=
    {f | ∃ T' : Finset (Fin #(B q)), T'.Nonempty ∧ f = fun x => ∑ i ∈ T', v (emb q i) x}
  have hq (q : ℕ) : CostSynthesis I w s (blockTarget q) (2 ^ #(B q) - #(B q) - 1) 0 :=
    block_nonempty_subSums hArity hEval hZeroW (fun i => v (emb q i)) fun i => hv (emb q i)
  have hall := CostSynthesis.biUnion (range (k ⌈/⌉ width)) blockTarget
    (fun q => 2 ^ #(B q) - #(B q) - 1) (fun _ => 0) fun q _ => hq q
  have hsum_le :
      ∑ q ∈ range (k ⌈/⌉ width), (2 ^ #(B q) - #(B q) - 1) ≤ (k * 2 ^ width) / width := by
    apply (Nat.le_div_iff_mul_le hw).mpr
    rw [mul_comm, mul_sum]
    calc ∑ q ∈ range (k ⌈/⌉ width), width * (2 ^ #(B q) - #(B q) - 1)
        ≤ ∑ q ∈ range (k ⌈/⌉ width), #(B q) * 2 ^ width :=
          sum_le_sum fun q _ => mul_sub_two_pow_le (card_blockIndices_le k width q hw)
      _ = (∑ q ∈ range (k ⌈/⌉ width), #(B q)) * 2 ^ width := (sum_mul _ _ _).symm
      _ = k * 2 ^ width := by rw [sum_card_blockIndices k width hw]
  refine hall.mono Set.Subset.rfl ?_ hsum_le (by simp)
  rintro _ ⟨q, T, hT, hTq, rfl⟩
  obtain ⟨j₀, hj₀⟩ := hT
  have hq_lt : q < k ⌈/⌉ width := hTq j₀ hj₀ ▸ div_lt_ceilDiv j₀.isLt hw
  rw [Set.mem_iUnion₂]
  let T' : Finset (Fin #(B q)) := univ.filter fun i => emb q i ∈ T
  have hT_map : T'.map (emb q).toEmbedding = T := by
    ext j
    simp only [T', mem_map, mem_filter, mem_univ, true_and, RelEmbedding.coe_toEmbedding]
    refine ⟨fun ⟨i, hi, he⟩ => he ▸ hi, fun hjT => ?_⟩
    obtain ⟨i, rfl⟩ : j ∈ Set.range (emb q) := by
      rw [range_orderEmbOfFin]
      exact mem_filter.mpr ⟨mem_univ j, hTq j hjT⟩
    exact ⟨i, hjT, rfl⟩
  have hT'ne : T'.Nonempty := map_nonempty.mp (by rw [hT_map]; exact ⟨j₀, hj₀⟩)
  refine ⟨q, mem_range.mpr hq_lt, T', hT'ne, ?_⟩
  funext x
  rw [← hT_map, sum_map]
  rfl


end GroupSubSums

namespace Additive

section BlockCols

variable {G : Type*} [AddCommMonoid G] {m n : ℕ}

/-- Injects within-block index `a : Fin s` into block `q`'s global column index in `Fin n`. -/
@[expose] def fullBlockEmb {n s : ℕ} (q : Fin (n / s)) : Fin s ↪ Fin n where
  toFun a := ⟨q.1 * s + a.1, by
    have hq : (q.1 + 1) * s ≤ n :=
      (Nat.mul_le_mul_right s (Nat.succ_le_of_lt q.isLt)).trans (Nat.div_mul_le_self n s)
    have := a.isLt
    nlinarith⟩
  inj' a₁ a₂ h := Fin.ext (by
    have hv : q.1 * s + a₁.1 = q.1 * s + a₂.1 := congrArg Fin.val h
    omega)

theorem fullBlockEmb_div {n s : ℕ} (q : Fin (n / s)) (a : Fin s) :
    (fullBlockEmb q a).1 / s = q.1 := by
  have hs : 0 < s := Nat.zero_lt_of_lt a.isLt
  change (q.1 * s + a.1) / s = q.1
  rw [mul_comm, Nat.mul_add_div hs, Nat.div_eq_of_lt a.isLt, add_zero]

/-- Subset of `Fin s` where row `r` of `A` has `true` in full width-`s` block `q < n / s`. -/
@[expose] def fullRowPattern (A : Matrix (Fin m) (Fin n) Bool) (s : ℕ) (r : Fin m)
    (q : Fin (n / s)) : Finset (Fin s) :=
  univ.filter fun a : Fin s => A r (fullBlockEmb q a) = true

/-- Columns of the compressed full-block matrix: pairs `(q, T)` with `q < n / s` and `T` a nonempty
subset of `Fin s`. -/
abbrev FullCol (n s : ℕ) := Fin (n / s) × {T : Finset (Fin s) // T.Nonempty}

/-- Block index `q : Fin (n / s)` selected by full-block column `c`. -/
abbrev FullCol.block {n s : ℕ} (c : FullCol n s) : Fin (n / s) := c.1

/-- Nonempty set of local offsets within `c.block` selected by full-block column `c`. -/
abbrev FullCol.subset {n s : ℕ} (c : FullCol n s) : Finset (Fin s) := c.2.1

theorem card_nonempty_finset_fin (s : ℕ) :
    Fintype.card {T : Finset (Fin s) // T.Nonempty} = 2 ^ s - 1 := by
  have heq : univ.filter (fun T : Finset (Fin s) => T.Nonempty) = univ.erase ∅ := by
    ext T
    simp [nonempty_iff_ne_empty]
  rw [Fintype.card_subtype, heq, card_erase_of_mem (mem_univ ∅), card_univ,
    Fintype.card_finset, Fintype.card_fin]

theorem card_fullCol_le (n s : ℕ) (hs : 0 < s) :
    Fintype.card (FullCol n s) ≤ 2 ^ s * (n ⌈/⌉ s) := by
  have hdiv : n / s ≤ n ⌈/⌉ s := by
    apply (Nat.div_le_iff_le_mul_add_pred hs).mpr
    have hceil : n ≤ s * (n ⌈/⌉ s) := (ceilDiv_le_iff_le_smul hs).mp le_rfl
    nlinarith
  rw [Fintype.card_prod, Fintype.card_fin, Additive.card_nonempty_finset_fin]
  calc (n / s) * (2 ^ s - 1) ≤ (n ⌈/⌉ s) * 2 ^ s :=
        Nat.mul_le_mul hdiv (Nat.sub_le _ _)
    _ = 2 ^ s * (n ⌈/⌉ s) := mul_comm _ _

/-- Boolean indicator that row `r` of `A` matches the nonempty full-block column `c`. -/
@[expose] def hasFullCol (A : Matrix (Fin m) (Fin n) Bool) (s : ℕ) (r : Fin m)
    (c : FullCol n s) : Bool :=
  decide (fullRowPattern A s r c.block = c.subset)

/-- Sum of inputs selected by the full-block column `c` under valuation `x`. -/
@[expose] def fullColVal {n s : ℕ} (c : FullCol n s) (x : Fin n → G) : G :=
  ∑ a ∈ c.subset, x (fullBlockEmb c.block a)

/-- Trailing active column indices `j` of row `r` with `j / s = n / s`. -/
@[expose] def matrixTailSet (A : Matrix (Fin m) (Fin n) Bool) (s : ℕ) (r : Fin m) :
    Finset (Fin n) :=
  univ.filter fun j : Fin n => n / s ≤ j.1 / s ∧ A r j = true

theorem div_eq_of_mem_matrixTailSet {A : Matrix (Fin m) (Fin n) Bool} {s : ℕ}
    {r : Fin m} {j : Fin n} (hj : j ∈ matrixTailSet A s r) : j.1 / s = n / s := by
  have hge : n / s ≤ j.1 / s := (mem_filter.mp hj).2.1
  have hle : j.1 / s ≤ n / s := Nat.div_le_div_right j.isLt.le
  omega

theorem sum_fullCol_lt_eq {m K s Q : ℕ} (A : Matrix (Fin m) (Fin K) Bool)
    (hs : 0 < s) (hQ : Q ≤ K / s) (r : Fin m) (v : Fin K → G) :
    (∑ c : FullCol K s with decide (c.block.1 < Q ∧ fullRowPattern A s r c.block = c.subset) = true,
      fullColVal c v) =
    ∑ j ∈ univ.filter (fun j : Fin K => j.1 / s < Q ∧ A r j = true), v j := by
  have hblock (q : Fin (K / s)) :
      (∑ T : {T : Finset (Fin s) // T.Nonempty},
        if decide (q.1 < Q ∧ fullRowPattern A s r q = T.1) = true then fullColVal (q, T) v
        else 0) =
      if q.1 < Q then ∑ a ∈ fullRowPattern A s r q, v (fullBlockEmb q a) else 0 := by
    by_cases hq : q.1 < Q
    · simp only [hq, true_and, ↓reduceIte]
      rcases (fullRowPattern A s r q).eq_empty_or_nonempty with hempty | hne
      · rw [hempty, sum_empty, sum_eq_zero]
        rintro ⟨T, hT⟩ -
        simp [hT.ne_empty.symm]
      · rw [sum_eq_single ⟨fullRowPattern A s r q, hne⟩ (fun ⟨T, _⟩ _ h => by
            simp [show fullRowPattern A s r q ≠ T from fun e => h (Subtype.ext e.symm)])
          fun h => (h (mem_univ _)).elim]
        simp [fullColVal]
    · simp [hq]
  rw [sum_filter, Fintype.sum_prod_type, sum_congr rfl fun q _ => hblock q, ← sum_filter]
  let blockJ (q : Fin (K / s)) : Finset (Fin K) :=
    (fullRowPattern A s r q).map (fullBlockEmb q)
  have hdisj_q :
      ((univ.filter fun q : Fin (K / s) => q.1 < Q) :
        Set (Fin (K / s))).PairwiseDisjoint blockJ := by
    intro q₁ _ q₂ _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro j hj₁ hj₂
    obtain ⟨a₁, _, rfl⟩ := mem_map.mp hj₁
    obtain ⟨a₂, _, heq⟩ := mem_map.mp hj₂
    exact hne (Fin.ext (by rw [← fullBlockEmb_div q₁ a₁, ← heq, fullBlockEmb_div q₂ a₂]))
  have hbi :
      (univ.filter fun q : Fin (K / s) => q.1 < Q).biUnion blockJ =
        univ.filter (fun j : Fin K => j.1 / s < Q ∧ A r j = true) := by
    ext j
    simp only [mem_biUnion, mem_filter, mem_univ, true_and, blockJ, mem_map, fullRowPattern]
    constructor
    · rintro ⟨q, hq, a, hA, rfl⟩
      exact ⟨by rwa [fullBlockEmb_div], hA⟩
    · rintro ⟨hlt, hA⟩
      refine ⟨⟨j.1 / s, lt_of_lt_of_le hlt hQ⟩, hlt, ⟨j.1 % s, Nat.mod_lt _ hs⟩, ?_, ?_⟩
      · convert hA using 2
        exact Fin.ext (Nat.div_add_mod' j.1 s)
      · exact Fin.ext (Nat.div_add_mod' j.1 s)
  rw [← hbi, sum_biUnion hdisj_q]
  exact sum_congr rfl fun q _ => (sum_map _ _ _).symm

theorem sum_row_eq_fullCol_add_tail (A : Matrix (Fin m) (Fin n) Bool) {s : ℕ} (hs : 0 < s)
    (r : Fin m) (x : Fin n → G) :
    (∑ j : Fin n, if A r j then x j else 0) =
      (∑ c : FullCol n s with hasFullCol A s r c = true, fullColVal c x) +
      ∑ j ∈ matrixTailSet A s r, x j := by
  have hsplit_j :
      (∑ j : Fin n, if A r j then x j else 0) =
        (∑ j ∈ univ.filter (fun j : Fin n => j.1 / s < n / s ∧ A r j = true), x j) +
        ∑ j ∈ matrixTailSet A s r, x j := by
    unfold matrixTailSet
    rw [← sum_filter]
    have hunion :
        (univ.filter fun j : Fin n => A r j = true) =
          (univ.filter fun j : Fin n => j.1 / s < n / s ∧ A r j = true) ∪
          (univ.filter fun j : Fin n => n / s ≤ j.1 / s ∧ A r j = true) := by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_union]
      by_cases h : j.1 / s < n / s
      · simp [h]
      · simp [h, Nat.le_of_not_lt h]
    rw [hunion, sum_union (disjoint_left.mpr fun j hj1 hj2 => by
      have := (mem_filter.mp hj1).2.1; have := (mem_filter.mp hj2).2.1; omega)]
  rw [hsplit_j]
  congr 1
  rw [← sum_fullCol_lt_eq A hs le_rfl r x]
  refine sum_congr ?_ fun _ _ => rfl
  ext c
  simp [hasFullCol]

end BlockCols

end Additive

end Cslib.Circuits
