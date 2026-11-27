/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomFunction.PrefixHybrid.Eager
public import CslibFrontier.Foundations.Data.BitString.List
import CslibFrontier.Probability.PMF.Uniform

/-!
# Splitting the next prefix-hybrid table

At a cut one block deeper, a word ending at or before the old cut has its own label.
A longer word takes its label from the child table for its parent at the old cut, then
evaluates the remaining suffix. The label table for short words and the child tables
are independent. This is the ideal-table step in the cascade argument of [BonehShoup2023],
v0.6, Section 6.4.2 (printed pp. 229–230), using the hybrids of Section 4.6.1
(printed pp. 152–153).

Valid queries after the old cut must contain a complete next block. The equality is a law
of the ideal table, including for adaptive queries with repeats.
-/

public section

namespace Cslib.Crypto

open Probability

private abbrev SplitPrefix (cut width : ℕ) :=
  {word : List Bool // word.length ≤ cut} ⊕ (BitString cut × BitString width)

private def splitPrefixIndex (cut width : ℕ) (query : List Bool) : SplitPrefix cut width :=
  if h : query.length ≤ cut then .inl ⟨query, h⟩
  else .inr (BitString.ofList cut query, BitString.ofList width (query.drop cut))

private def splitPrefixKey {cut width : ℕ} (hwidth : 0 < width) :
    SplitPrefix cut width ↪ List Bool where
  toFun := Sum.elim Subtype.val (fun (parent, block) => List.ofFn parent ++ List.ofFn block)
  inj' := by
    apply Function.LeftInverse.injective (g := splitPrefixIndex cut width)
    intro key
    rcases key with ⟨word, hword⟩ | ⟨parent, block⟩
    · simp [splitPrefixIndex, hword]
    · simp [splitPrefixIndex, hwidth.ne', BitString.ofList_ofFn_append,
        List.drop_left' (List.length_ofFn (f := parent))]

private theorem splitPrefixKey_index {cut width : ℕ} (hwidth : 0 < width)
    {query : List Bool} (hquery : cut < query.length → cut + width ≤ query.length) :
    splitPrefixKey hwidth (splitPrefixIndex cut width query) = query.take (cut + width) := by
  by_cases h : query.length ≤ cut
  · simp [splitPrefixIndex, splitPrefixKey, h]
    omega
  · have hofFn {w : ℕ} {xs : List Bool} (hw : w ≤ xs.length) :
        List.ofFn (BitString.ofList w xs) = xs.take w :=
      BitString.ofList_take w xs ▸ BitString.ofFn_ofList (List.length_take_of_le hw)
    have hdrop : width ≤ (query.drop cut).length := by
      rw [List.length_drop]
      exact Nat.le_sub_of_add_le' (hquery (Nat.lt_of_not_ge h))
    simp [splitPrefixIndex, splitPrefixKey, h, hofFn (Nat.le_of_not_ge h), hofFn hdrop,
      List.take_add]

/-- Read a short word's own label, or find the next-block label in its parent's child table
and evaluate the remaining suffix. The caller handles query validity. -/
def prefixHybridSplitAnswer {n cut width : ℕ}
    (family : List Bool → List Bool → List Bool)
    (short : {word : List Bool // word.length ≤ cut} → BitString n)
    (children : BitString cut → BitString width → BitString n) (query : List Bool) :
    List Bool :=
  match splitPrefixIndex cut width query with
  | .inl word => List.ofFn (short word)
  | .inr (parent, block) => family (List.ofFn (children parent block)) (query.drop (cut + width))

/-- A query ending at or before the old cut reads its own label. -/
theorem prefixHybridSplitAnswer_of_length_le {n cut width : ℕ}
    {family : List Bool → List Bool → List Bool}
    {short : {word : List Bool // word.length ≤ cut} → BitString n}
    {children : BitString cut → BitString width → BitString n} {query : List Bool}
    (h : query.length ≤ cut) :
    prefixHybridSplitAnswer family short children query = List.ofFn (short ⟨query, h⟩) := by
  simp [prefixHybridSplitAnswer, splitPrefixIndex, h]

/-- A query beyond the old cut reads its child label and evaluates the suffix after the block. -/
theorem prefixHybridSplitAnswer_of_lt_length {n cut width : ℕ}
    {family : List Bool → List Bool → List Bool}
    {short : {word : List Bool // word.length ≤ cut} → BitString n}
    {children : BitString cut → BitString width → BitString n} {query : List Bool}
    (h : cut < query.length) :
    prefixHybridSplitAnswer family short children query =
      family (List.ofFn (children (BitString.ofList cut query)
        (BitString.ofList width (query.drop cut)))) (query.drop (cut + width)) := by
  simp [prefixHybridSplitAnswer, splitPrefixIndex, h.not_ge]

/-- The next-cut hybrid has the same law as sampling an independent short-label table and
a uniform child function for every parent. Valid queries beyond `cut` contain a whole next
block, and evaluating an empty suffix returns its starting label. -/
theorem eval_prefixHybridGame_add_eq_split (valid : ℕ → List Bool → Bool)
    (family : List Bool → List Bool → List Bool) (adversary : OracleDistinguisher)
    (n cut width : ℕ) [Fintype {word : List Bool // word.length ≤ cut}]
    (hwidth : 0 < width) (hnil : ∀ seed, family seed [] = seed)
    (hquery : ∀ query, valid n query = true → cut < query.length → cut + width ≤ query.length) :
    ProbComp.eval (prefixHybridGame valid family adversary n (cut + width)) =
      (PMF.uniformOfFintype
        (({word : List Bool // word.length ≤ cut} → BitString n) ×
          (BitString cut → BitString width → BitString n))).bind fun tables =>
        OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
          (fun request => PMF.pure (if valid n request.2 then
            prefixHybridSplitAnswer family tables.1 tables.2 request.2 else [])))
          (adversary n []) := by
  classical
  let splitTable : (SplitPrefix cut width → BitString n) ≃
      ({word : List Bool // word.length ≤ cut} → BitString n) ×
        (BitString cut → BitString width → BitString n) :=
    (Equiv.sumArrowEquivProdArrow _ _ _).trans
      (Equiv.prodCongr (Equiv.refl _) (Equiv.curry _ _ _))
  rw [eval_prefixHybridGame_eq_eager_of_index (splitPrefixKey hwidth)
    (splitPrefixIndex cut width) valid family adversary n (cut + width)
    (fun query hv => splitPrefixKey_index hwidth (hquery query hv))]
  rw [← PMF.uniformOfFintype_map_equiv splitTable, PMF.bind_map]
  have hreply (table : SplitPrefix cut width → BitString n) (query : List Bool) :
      family (List.ofFn (table (splitPrefixIndex cut width query)))
          (query.drop (cut + width)) =
        prefixHybridSplitAnswer family (splitTable table).1 (splitTable table).2 query := by
    by_cases h : query.length ≤ cut
    · have hdrop : query.drop (cut + width) = [] := List.drop_eq_nil_of_le (by omega)
      simp [prefixHybridSplitAnswer_of_length_le h, splitPrefixIndex, h, hdrop, hnil, splitTable]
    · simp [prefixHybridSplitAnswer_of_lt_length (Nat.lt_of_not_ge h), splitPrefixIndex, h,
        splitTable]
  simp only [Function.comp_def, hreply]

end Cslib.Crypto
