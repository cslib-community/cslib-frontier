/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.Circuit.Boolean.Complexity
public import Mathlib.Algebra.Order.Floor.Div
public import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.Basis
public import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.Decomposition
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Ring.BooleanRing
public import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.BlockCols
public import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.SectionPairing
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Internal staged column-pairing partition for `{⊕, ∧, 1}` synthesis

Internal combined `X ⊕ G` column definitions and row-sum partition lemmas (`ZhegCol`,
`mul_sum_hasZhegCol_le`, `zhegRowParts`, `card_zhegRowParts_le`, `sum_zhegRowParts_eq`) consumed by
`StageStep` and `UpperBound`; never re-exported through `Zhegalkin`.

## Main definitions

* `Cslib.Circuits.Boolean.Zhegalkin.ZhegCol`, `zhegColVal`, `hasZhegCol`, `zhegPairVal`,
  `zhegOddVal`, `intraGSet`, `hFn`, `ZhegPartIdx`, `zhegRowParts`, `zhegPartVal`: staged column
  and row-partition indices.

## Main results

* `Cslib.Circuits.Boolean.Zhegalkin.card_zhegCol_le`, `mul_sum_hasZhegCol_le`,
  `card_zhegRowParts_le`, `sum_zhegRowParts_eq`: cardinality bounds and row-sum partition
  identity.
-/

public section

open Finset

namespace Cslib.Circuits.Boolean.Zhegalkin

section StageParts

variable {n M k : ℕ} {f : BooleanFunction n}

/-- Combined column index across original `X` blocks and prior `G` gate blocks. -/
abbrev ZhegCol (n M s : ℕ) := Additive.FullCol n s ⊕ Additive.FullCol M s

theorem card_zhegCol_le (n M s : ℕ) (hs : 0 < s) :
    Fintype.card (ZhegCol n M s) ≤ 2 ^ s * ((n + M) ⌈/⌉ s) := by
  have hdiv : n / s + M / s ≤ (n + M) ⌈/⌉ s := by
    apply Nat.lt_succ_iff.mp
    apply Nat.lt_of_mul_lt_mul_left (a := s)
    calc s * (n / s + M / s)
        = s * (n / s) + s * (M / s) := by ring
      _ ≤ n + M := Nat.add_le_add (Nat.mul_div_le n s) (Nat.mul_div_le M s)
      _ ≤ s * ((n + M) ⌈/⌉ s) := (ceilDiv_le_iff_le_smul hs).mp le_rfl
      _ < s * ((n + M) ⌈/⌉ s + 1) := by nlinarith
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    Additive.card_nonempty_finset_fin]
  calc (n / s) * (2 ^ s - 1) + (M / s) * (2 ^ s - 1)
      = (n / s + M / s) * (2 ^ s - 1) := by ring
    _ ≤ ((n + M) ⌈/⌉ s) * 2 ^ s := Nat.mul_le_mul hdiv (Nat.sub_le _ _)
    _ = 2 ^ s * ((n + M) ⌈/⌉ s) := mul_comm _ _

/-- Boolean function associated with column `c : ZhegCol n M s`. -/
@[expose] def zhegColVal {s : ℕ} (d : PaddedDecomp f M k) :
    ZhegCol n M s → BooleanFunction n
  | .inl cx => Additive.fullColVal cx
  | .inr cg => fun x => ∑ a ∈ cg.subset, d.gFn (Additive.fullBlockEmb cg.block a) x

/-- Whether conjunction input row `r` uses non-intra column `c : ZhegCol n M s`. -/
@[expose] def hasZhegCol (d : PaddedDecomp f M k) (s : ℕ) (r : Fin (2 * M)) :
    ZhegCol n M s → Bool
  | .inl cx => Additive.hasFullCol d.aX s r cx
  | .inr cg =>
    decide (cg.block.val < (r.val / 2) / s ∧ Additive.fullRowPattern d.aG s r cg.block = cg.subset)

theorem mul_sum_hasZhegCol_le (d : PaddedDecomp f M k) (s : ℕ) :
    s * (∑ r : Fin (2 * M), #{c : ZhegCol n M s | hasZhegCol d s r c = true}) ≤
      M * (M + 2 * n) := by
  have hrow (r : Fin (2 * M)) :
      #{c : ZhegCol n M s | hasZhegCol d s r c = true} ≤ n / s + (r.val / 2) / s := by
    have hsplit : #{c : ZhegCol n M s | hasZhegCol d s r c = true} =
        #{cx : Additive.FullCol n s | Additive.hasFullCol d.aX s r cx = true} +
        #{cg : Additive.FullCol M s |
          decide (cg.1.val < (r.val / 2) / s ∧
            Additive.fullRowPattern d.aG s r cg.1 = cg.2.val) = true} := by
      simp only [card_filter]
      rw [Fintype.sum_sum_type]
      rfl
    rw [hsplit]
    apply Nat.add_le_add
    · let activeX := univ.filter fun cx : Additive.FullCol n s =>
        Additive.hasFullCol d.aX s r cx = true
      have hinj : Set.InjOn Prod.fst (activeX : Set (Additive.FullCol n s)) := by
        intro ⟨q₁, T₁, _⟩ hx₁ ⟨q₂, T₂, _⟩ hx₂ hq
        dsimp only at hq
        subst hq
        have heq₁ : Additive.fullRowPattern d.aX s r q₁ = T₁ :=
          of_decide_eq_true (mem_filter.mp hx₁).2
        have heq₂ : Additive.fullRowPattern d.aX s r q₁ = T₂ :=
          of_decide_eq_true (mem_filter.mp hx₂).2
        exact Prod.ext rfl (Subtype.ext (heq₁.symm.trans heq₂))
      exact (card_le_card_of_injOn Prod.fst (fun _ _ => mem_univ _) hinj).trans_eq (by simp)
    · let targetQ : Finset (Fin (M / s)) := univ.filter fun q => q.val < (r.val / 2) / s
      let activeG := univ.filter fun cg : Additive.FullCol M s =>
        decide (cg.1.val < (r.val / 2) / s ∧
          Additive.fullRowPattern d.aG s r cg.1 = cg.2.val) = true
      have hinj : Set.InjOn Prod.fst (activeG : Set (Additive.FullCol M s)) := by
        intro ⟨q₁, T₁, _⟩ hx₁ ⟨q₂, T₂, _⟩ hx₂ hq
        dsimp only at hq
        subst hq
        have heq₁ : Additive.fullRowPattern d.aG s r q₁ = T₁ :=
          (of_decide_eq_true (mem_filter.mp hx₁).2).2
        have heq₂ : Additive.fullRowPattern d.aG s r q₁ = T₂ :=
          (of_decide_eq_true (mem_filter.mp hx₂).2).2
        exact Prod.ext rfl (Subtype.ext (heq₁.symm.trans heq₂))
      have hmaps : ∀ cg ∈ univ.filter (fun cg : Additive.FullCol M s =>
          decide (cg.1.val < (r.val / 2) / s ∧
            Additive.fullRowPattern d.aG s r cg.1 = cg.2.val) = true), cg.1 ∈ targetQ :=
        fun cg hcg => mem_filter.mpr ⟨mem_univ _, (of_decide_eq_true (mem_filter.mp hcg).2).1⟩
      have hcardQ : #targetQ ≤ (r.val / 2) / s := by
        have hinjVal : Set.InjOn Fin.val (targetQ : Set (Fin (M / s))) :=
          fun _ _ _ _ h => Fin.ext h
        exact (card_le_card_of_injOn Fin.val
          (fun q hq => mem_range.mpr (mem_filter.mp hq).2) hinjVal).trans_eq (card_range _)
      exact (card_le_card_of_injOn Prod.fst hmaps hinj).trans hcardQ
  calc s * (∑ r : Fin (2 * M), #{c : ZhegCol n M s | hasZhegCol d s r c = true})
      ≤ s * (∑ r : Fin (2 * M), (n / s + (r.val / 2) / s)) :=
        Nat.mul_le_mul_left s (sum_le_sum fun r _ => hrow r)
    _ = ∑ r : Fin (2 * M), (s * (n / s) + s * ((r.val / 2) / s)) := by
        rw [mul_sum]
        exact sum_congr rfl fun r _ => by ring
    _ ≤ ∑ r : Fin (2 * M), (n + r.val / 2) :=
        sum_le_sum fun r _ => Nat.add_le_add (Nat.mul_div_le n s) (Nat.mul_div_le _ s)
    _ = 2 * M * n + ∑ r ∈ range (2 * M), r / 2 := by
        rw [Fin.sum_univ_eq_sum_range (fun t => n + t / 2), sum_add_distrib, sum_const,
          card_range, smul_eq_mul]
    _ ≤ M * (M + 2 * n) := by
        have hsum_div : ∑ r ∈ range (2 * M), r / 2 ≤ M * M := by
          clear * -
          induction M with
          | zero => simp
          | succ m ih =>
            have h2 : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
            rw [h2, sum_range_succ, sum_range_succ]
            have hd1 : (2 * m) / 2 = m := by omega
            have hd2 : (2 * m + 1) / 2 = m := by omega
            nlinarith
        nlinarith

/-- Shared sum of columns paired between two rows in horizontal section `up.sec`. -/
@[expose] def zhegPairVal (d : PaddedDecomp f M k) (s p : ℕ)
    (up : SectionPeer (2 * M)) (x : Fin n → Bool) : Bool :=
  ∑ c ∈ pairedCols (hasZhegCol d s) p up.sec up.row₁ up.row₂, zhegColVal d c x

/-- Sum of unpaired odd-leftover columns for row `r`. -/
@[expose] def zhegOddVal (d : PaddedDecomp f M k) (s p : ℕ) (r : Fin (2 * M))
    (x : Fin n → Bool) : Bool :=
  ∑ c ∈ oddCols (hasZhegCol d s) p r, zhegColVal d c x

/-- Intra-stage conjunction indices `ℓ < r / 2` active in row `r`. -/
@[expose] def intraGSet (d : PaddedDecomp f M k) (s : ℕ) (r : Fin (2 * M)) : Finset (Fin M) :=
  univ.filter fun ℓ : Fin M => ℓ.val / s = (r.val / 2) / s ∧ ℓ.val < r.val / 2 ∧ d.aG r ℓ = true

private theorem card_intraGSet_le (d : PaddedDecomp f M k) {s : ℕ} (hs : 0 < s)
    (r : Fin (2 * M)) : #(intraGSet d s r) ≤ s - 1 := by
  let mod0 : Fin s := ⟨(r.val / 2) % s, Nat.mod_lt _ hs⟩
  have hmaps : ∀ ℓ ∈ intraGSet d s r,
      (⟨ℓ.val % s, Nat.mod_lt _ hs⟩ : Fin s) ∈ univ.erase mod0 := by
    intro ℓ hℓ
    obtain ⟨_, hdiv, hlt, _⟩ := mem_filter.mp hℓ
    refine mem_erase.mpr ⟨fun heq => ?_, mem_univ _⟩
    have hm : ℓ.val % s = (r.val / 2) % s := congrArg Fin.val heq
    have h1 := Nat.div_add_mod ℓ.val s
    have h2 := Nat.div_add_mod (r.val / 2) s
    rw [hdiv, hm] at h1
    omega
  have hinj : Set.InjOn (fun ℓ : Fin M => (⟨ℓ.val % s, Nat.mod_lt _ hs⟩ : Fin s))
      (intraGSet d s r) := by
    intro ℓ₁ h₁ ℓ₂ h₂ heq
    have hd₁ := (mem_filter.mp h₁).2.1
    have hd₂ := (mem_filter.mp h₂).2.1
    have hm : ℓ₁.val % s = ℓ₂.val % s := congrArg Fin.val heq
    apply Fin.ext
    rw [← Nat.div_add_mod ℓ₁.val s, ← Nat.div_add_mod ℓ₂.val s, hd₁, hd₂, hm]
  exact (card_le_card_of_injOn _ hmaps hinj).trans_eq
    (by rw [card_erase_of_mem (mem_univ mod0), card_univ, Fintype.card_fin])

/-- Linear input form `hFn d r` fed into conjunction gate `r / 2`. -/
@[expose] def hFn (d : PaddedDecomp f M k) (r : Fin (2 * M)) : BooleanFunction n :=
  linForm (d.cH r) (d.aX r) (d.aG r) d.gFn

/-- Index tags partitioning a conjunction input row `r` across stages. -/
inductive ZhegPartIdx (M : ℕ) where
  /-- Constant-`1` term. -/
  | constOne
  /-- Section-peer paired column sum. -/
  | peer (r' : Fin (2 * M))
  /-- Section unpaired column sum. -/
  | odd
  /-- Trailing `X` input terms. -/
  | xTail
  /-- Intra-stage prior conjunction wire. -/
  | intraG (ℓ : Fin M)
  deriving DecidableEq

/-- Embedding of section peers into `ZhegPartIdx M`. -/
@[expose] def peerEmb (M : ℕ) : Fin (2 * M) ↪ ZhegPartIdx M :=
  ⟨.peer, fun _ _ h => by injection h⟩

/-- Embedding of intra-stage gates into `ZhegPartIdx M`. -/
@[expose] def intraEmb (M : ℕ) : Fin M ↪ ZhegPartIdx M :=
  ⟨.intraG, fun _ _ h => by injection h⟩

/-- Finset of non-empty partition pieces making up `hFn d r`. -/
@[expose] def zhegRowParts (d : PaddedDecomp f M k) (s p : ℕ) (r : Fin (2 * M)) :
    Finset (ZhegPartIdx M) :=
  (if d.cH r then {.constOne} else ∅) ∪
    ((sectionPeers p r).filter fun r' =>
        (pairedCols (hasZhegCol d s) p (r.val / p) (min r r') (max r r')).Nonempty).map
      (peerEmb M) ∪
    (if (oddCols (hasZhegCol d s) p r).Nonempty then {.odd} else ∅) ∪
    (if (Additive.matrixTailSet d.aX s r).Nonempty then {.xTail} else ∅) ∪
    (intraGSet d s r).map (intraEmb M)

/-- Boolean function for each tag in `zhegRowParts d s p r`. -/
@[expose] def zhegPartVal (d : PaddedDecomp f M k) (s p : ℕ) (r : Fin (2 * M)) :
    ZhegPartIdx M → BooleanFunction n
  | .constOne => Boolean.Zhegalkin.constOne n
  | .peer r' => zhegPairVal d s p (r.val / p, (min r r', max r r'))
  | .odd => zhegOddVal d s p r
  | .xTail => fun x => ∑ j ∈ Additive.matrixTailSet d.aX s r, x j
  | .intraG ℓ => d.gFn ℓ

theorem card_zhegRowParts_le (d : PaddedDecomp f M k) {s p : ℕ} (hs : 0 < s) (hp : 0 < p)
    (r : Fin (2 * M)) :
    #(zhegRowParts d s p r) ≤ p + s + 1 := by
  have hite (P : Prop) [Decidable P] (z : ZhegPartIdx M) : #(if P then {z} else ∅) ≤ 1 := by
    split_ifs <;> simp
  unfold zhegRowParts
  -- Bound the five parts by `1`, `p - 1`, `1`, `1` and `s - 1`.
  refine (card_union_le _ _).trans <| (add_le_add ((card_union_le _ _).trans <| add_le_add
    ((card_union_le _ _).trans <| add_le_add ((card_union_le _ _).trans <| add_le_add (hite _ _)
      ((card_map _).trans_le <| (card_filter_le _ _).trans (card_sectionPeers_le hp r)))
      (hite _ _)) (hite _ _)) ((card_map _).trans_le (card_intraGSet_le d hs r))).trans ?_
  omega

theorem sum_zhegRowParts_eq (d : PaddedDecomp f M k) {s : ℕ} (hs : 0 < s) (p : ℕ)
    (r : Fin (2 * M)) (x : Fin n → Bool) :
    (∑ idx ∈ zhegRowParts d s p r, zhegPartVal d s p r idx x) = hFn d r x := by
  unfold zhegRowParts
  set p1 : Finset (ZhegPartIdx M) := if d.cH r then {.constOne} else ∅
  set p2 : Finset (ZhegPartIdx M) :=
    ((sectionPeers p r).filter fun r' =>
        (pairedCols (hasZhegCol d s) p (r.val / p) (min r r') (max r r')).Nonempty).map (peerEmb M)
  set p3 : Finset (ZhegPartIdx M) :=
    if (oddCols (hasZhegCol d s) p r).Nonempty then {.odd} else ∅
  set p4 : Finset (ZhegPartIdx M) :=
    if (Additive.matrixTailSet d.aX s r).Nonempty then {.xTail} else ∅
  set p5 : Finset (ZhegPartIdx M) := (intraGSet d s r).map (intraEmb M)
  have hd12 : Disjoint p1 p2 := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    obtain ⟨_, _, rfl⟩ := mem_map.mp hz2
    dsimp only [p1] at hz1
    split_ifs at hz1 <;> simp [peerEmb] at hz1
  have hd123 : Disjoint (p1 ∪ p2) p3 := by
    rw [Finset.disjoint_left]
    intro z hz12 hz3
    dsimp only [p3] at hz3
    split_ifs at hz3 with hne
    · rw [mem_singleton.mp hz3] at hz12
      rcases mem_union.mp hz12 with hz1 | hz2
      · dsimp only [p1] at hz1; split_ifs at hz1 <;> simp at hz1
      · obtain ⟨_, _, habs⟩ := mem_map.mp hz2; nomatch habs
    · exact notMem_empty _ hz3
  have hd1234 : Disjoint (p1 ∪ p2 ∪ p3) p4 := by
    rw [Finset.disjoint_left]
    intro z hz123 hz4
    dsimp only [p4] at hz4
    split_ifs at hz4 with hne
    · rw [mem_singleton.mp hz4] at hz123
      rcases mem_union.mp hz123 with hz12 | hz3
      · rcases mem_union.mp hz12 with hz1 | hz2
        · dsimp only [p1] at hz1; split_ifs at hz1 <;> simp at hz1
        · obtain ⟨_, _, habs⟩ := mem_map.mp hz2; nomatch habs
      · dsimp only [p3] at hz3; split_ifs at hz3 <;> simp at hz3
    · exact notMem_empty _ hz4
  have hd12345 : Disjoint (p1 ∪ p2 ∪ p3 ∪ p4) p5 := by
    rw [Finset.disjoint_left]
    intro z hz1234 hz5
    obtain ⟨_, _, rfl⟩ := mem_map.mp hz5
    rcases mem_union.mp hz1234 with hz123 | hz4
    · rcases mem_union.mp hz123 with hz12 | hz3
      · rcases mem_union.mp hz12 with hz1 | hz2
        · dsimp only [p1] at hz1; split_ifs at hz1 <;> simp [intraEmb] at hz1
        · obtain ⟨_, _, habs⟩ := mem_map.mp hz2; nomatch habs
      · dsimp only [p3] at hz3; split_ifs at hz3 <;> simp [intraEmb] at hz3
    · dsimp only [p4] at hz4; split_ifs at hz4 <;> simp [intraEmb] at hz4
  rw [sum_union hd12345, sum_union hd1234, sum_union hd123, sum_union hd12, sum_map, sum_map]
  have hs1 : (∑ z ∈ p1, zhegPartVal d s p r z x) = if d.cH r then true else (0 : Bool) := by
    dsimp only [p1]
    split_ifs <;> simp [zhegPartVal, constOne]
  have hs2 :
      (∑ r' ∈ (sectionPeers p r).filter (fun r' =>
          (pairedCols (hasZhegCol d s) p (r.val / p) (min r r') (max r r')).Nonempty),
        zhegPartVal d s p r (peerEmb M r') x) =
      ∑ r' ∈ sectionPeers p r, zhegPairVal d s p (r.val / p, (min r r', max r r')) x :=
    sum_filter_of_ne fun _ _ h => nonempty_of_sum_ne_zero h
  have hs3 : (∑ z ∈ p3, zhegPartVal d s p r z x) = zhegOddVal d s p r x := by
    rcases (oddCols (hasZhegCol d s) p r).eq_empty_or_nonempty with h | h <;>
      simp [p3, h, zhegPartVal, zhegOddVal]
  have hs4 : (∑ z ∈ p4, zhegPartVal d s p r z x) =
      ∑ j ∈ Additive.matrixTailSet d.aX s r, x j := by
    rcases (Additive.matrixTailSet d.aX s r).eq_empty_or_nonempty with h | h <;>
      simp [p4, h, zhegPartVal]
  change (∑ z ∈ p1, zhegPartVal d s p r z x) +
      (∑ r' ∈ (sectionPeers p r).filter _, zhegPartVal d s p r (peerEmb M r') x) +
      (∑ z ∈ p3, zhegPartVal d s p r z x) +
      (∑ z ∈ p4, zhegPartVal d s p r z x) +
      (∑ ℓ ∈ intraGSet d s r, d.gFn ℓ x) = _
  rw [hs1, hs2, hs3, hs4]
  have hcol_sum :
      (∑ r' ∈ sectionPeers p r, zhegPairVal d s p (r.val / p, (min r r', max r r')) x) +
        zhegOddVal d s p r x =
      (∑ cx : Additive.FullCol n s with Additive.hasFullCol d.aX s r cx = true,
        Additive.fullColVal cx x) +
      (∑ cg : Additive.FullCol M s with
        decide (cg.1.val < (r.val / 2) / s ∧
          Additive.fullRowPattern d.aG s r cg.1 = cg.2.val) = true,
        ∑ a ∈ cg.2.val, d.gFn (Additive.fullBlockEmb cg.1 a) x) := by
    have hfull := (sum_filter_hasCol_eq (hasZhegCol d s) p (fun c => zhegColVal d c x) r).symm
    unfold zhegPairVal zhegOddVal
    rw [hfull, sum_filter, Fintype.sum_sum_type, ← sum_filter, ← sum_filter]
    rfl
  -- Combine `p2 + p3` using `hcol_sum`.
  rw [add_assoc _ _ (zhegOddVal d s p r x), hcol_sum]
  have hx_eq := Additive.sum_row_eq_fullCol_add_tail d.aX hs r x
  -- Show the `g`-blocks plus `intraGSet` equal `∑ ℓ : Fin M, if d.aG r ℓ then d.gFn ℓ x else 0`.
  have hg_early :
      (∑ cg : Additive.FullCol M s with
        decide (cg.1.val < (r.val / 2) / s ∧
          Additive.fullRowPattern d.aG s r cg.1 = cg.2.val) = true,
        ∑ a ∈ cg.2.val, d.gFn (Additive.fullBlockEmb cg.1 a) x) =
      ∑ ℓ ∈ univ.filter (fun ℓ : Fin M => ℓ.val / s < (r.val / 2) / s ∧ d.aG r ℓ = true),
        d.gFn ℓ x := by
    have hQ : (r.val / 2) / s ≤ M / s := Nat.div_le_div_right (by omega)
    exact Additive.sum_fullCol_lt_eq d.aG hs hQ r (fun ℓ => d.gFn ℓ x)
  have hg_split :
      (∑ ℓ ∈ univ.filter (fun ℓ : Fin M => ℓ.val / s < (r.val / 2) / s ∧ d.aG r ℓ = true),
        d.gFn ℓ x) +
      (∑ ℓ ∈ intraGSet d s r, d.gFn ℓ x) =
      ∑ ℓ : Fin M, if d.aG r ℓ then d.gFn ℓ x else 0 := by
    rw [← sum_filter]
    have hunion :
        (univ.filter fun ℓ : Fin M => ℓ.val / s < (r.val / 2) / s ∧ d.aG r ℓ = true) ∪
          intraGSet d s r =
        univ.filter fun ℓ : Fin M => d.aG r ℓ = true := by
      ext ℓ
      simp only [intraGSet, mem_union, mem_filter, mem_univ, true_and]
      constructor
      · rintro (⟨_, h⟩ | ⟨_, _, h⟩) <;> exact h
      · intro haG
        have hlt : ℓ.val < r.val / 2 := by
          by_contra hge
          have hc := d.causal r ℓ (Nat.le_of_not_lt hge)
          rw [hc] at haG
          exact Bool.false_ne_true haG
        have hdiv_le : ℓ.val / s ≤ (r.val / 2) / s := Nat.div_le_div_right hlt.le
        rcases lt_or_eq_of_le hdiv_le with hdiv_lt | hdiv_eq
        · exact Or.inl ⟨hdiv_lt, haG⟩
        · exact Or.inr ⟨hdiv_eq, hlt, haG⟩
    have hdisj :
        Disjoint (univ.filter fun ℓ : Fin M => ℓ.val / s < (r.val / 2) / s ∧ d.aG r ℓ = true)
          (intraGSet d s r) := by
      rw [Finset.disjoint_left]
      intro ℓ h1 h2
      have hlt := (mem_filter.mp h1).2.1
      have heq := (mem_filter.mp h2).2.1
      omega
    rw [← sum_union hdisj, hunion]
  rw [hg_early]
  unfold hFn linForm
  rw [hx_eq, ← hg_split]
  abel

end StageParts

end Cslib.Circuits.Boolean.Zhegalkin
