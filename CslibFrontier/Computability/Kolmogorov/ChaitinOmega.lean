/-
Copyright (c) 2026 Matthew Doty, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Kolmogorov.KraftChaitin
public import CslibFrontier.Foundations.Computability.DistinctValues
public import CslibFrontier.Foundations.Data.BitString.List.Binary
public import CslibFrontier.Probability.BitString.CoinFlips
public import Mathlib.NumberTheory.Real.Irrational
import CslibFrontier.Foundations.Analysis.ENNRealTsum
import CslibFrontier.Foundations.Data.BitString.Enumeration
import CslibFrontier.Foundations.Data.BitString.List.PrefixFree
import CslibFrontier.Foundations.Data.List.Primrec
import CslibFrontier.Foundations.Data.Nat.Bits
import CslibFrontier.Foundations.Data.Nat.Primrec
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Computability.Halting
import Mathlib.Computability.Primrec.List

/-!
# Chaitin's halting probability `Ω`, Martin-Löf randomness, and bit incompleteness

For any prefix-free description method `M : DescriptionMethod α`, **Chaitin's halting
probability** is `chaitinOmega M = ∑' p : M.haltingSet, (2 : ℝ)⁻¹ ^ p.length`
(`chaitinOmega`). By Kraft's inequality it lies in `[0, 1]` (`IsPrefixFree.chaitinOmega_le_one`),
and for the universal prefix-free machine `universalPrefix` it lies strictly inside `(0, 1)`.

Formalizing the computable monotone enumeration `universalPrefixTable` of accepted pairs of
`universalPrefix` yields:

* **Left-c.e. approximation**: `universalPrefixApprox : ℕ → ℚ` is computable, monotone, bounded
  above by `Ω := chaitinOmega universalPrefix`, and converges to `Ω`
  (`tendsto_universalPrefixApprox`).
* **Halting reduction, irrationality, and uncomputability**: deciding whether an arbitrary string
  belongs to `universalPrefix.haltingSet` solves the halting problem
  (`not_computablePred_haltingSet_universalPrefix`), so no computable rational sequence converges
  to `Ω` at rate `2⁻¹ ^ m` (`not_exists_computable_approx_chaitinOmega`); in particular `Ω` is
  irrational (`irrational_chaitinOmega_universalPrefix`) and its binary digits `realBit Ω` are
  uncomputable (`not_computable_realBit_chaitinOmega_universalPrefix`).
* **Halting connection and incompressibility**: waiting until `universalPrefixApprox t` overtakes
  `0.(Ω ↾ n)` captures every halting program of length at most `n`
  (`universalPrefixTable_captures_length_le`), yielding Chaitin's incompressibility
  theorem `n ≤ K(Ω ↾ n) + O(1)` (`exists_le_complexity_realPrefix_chaitinOmega`).
* **Martin-Löf randomness**: defining `MartinLofTest` and `IsMartinLofRandom` against
  `Cslib.BitString.coinFlips`, online disjointification plus Kraft–Chaitin shows that every
  tape satisfying `n ≤ K(x ↾ n) + O(1)` is Martin-Löf random (`isMartinLofRandom_of_le_complexity`);
  hence `realBit (chaitinOmega universalPrefix)` is Martin-Löf random
  (`isMartinLofRandom_chaitinOmega`), whereas no computable sequence is random
  (`not_isMartinLofRandom_of_computable`).
* **Chaitin's bit-incompleteness theorem** [Chaitin1974], [LiVitanyi2019]: every r.e. set of pairs
  `(i, b)` that is sound for `realBit (chaitinOmega universalPrefix)` is finite
  (`finite_of_rePred_of_sound_realBit_chaitinOmega`).

## Main definitions

* `Cslib.Kolmogorov.DescriptionMethod.chaitinOmega`: halting probability of a description method.
* `Cslib.Kolmogorov.DescriptionMethod.universalPrefixTable`,
  `Cslib.Kolmogorov.DescriptionMethod.universalPrefixApprox`: left-c.e. enumeration and dyadic
  rational approximation to `chaitinOmega universalPrefix`.
* `Cslib.Kolmogorov.realBit`, `Cslib.Kolmogorov.realPrefix`: binary expansion of a real number.
* `Cslib.Kolmogorov.prefixCylinderList`, `Cslib.Kolmogorov.MartinLofTest`,
  `Cslib.Kolmogorov.IsMartinLofRandom`: Martin-Löf tests and randomness under `coinFlips`.

## References

* [G. J. Chaitin, *Information-Theoretic Limitations of Formal Systems*][Chaitin1974]
* [M. Li, P. Vitányi, *An Introduction to Kolmogorov Complexity and Its
  Applications*][LiVitanyi2019]
* [A. Shen, V. A. Uspensky, N. Vereshchagin, *Kolmogorov Complexity and Algorithmic
  Randomness*][ShenUspenskyVereshchagin2017]
-/

public section

open scoped BigOperators ENNReal Filter Topology

namespace Cslib.Kolmogorov

open Encodable Denumerable Nat.Partrec Filter MeasureTheory

private theorem length_le_foldr_max (L : List (List Bool)) {u : List Bool} (hu : u ∈ L) :
    u.length ≤ L.foldr (fun s m => max s.length m) 0 := by
  induction L with
  | nil => simp at hu
  | cons a rest ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hu with rfl | hu'
    · exact le_max_left _ _
    · exact (ih hu').trans (le_max_right _ _)

private theorem primrec_enumList : Primrec Cslib.BitString.enumList := by
  have hh : Primrec₂ fun (_ : ℕ) (IH : List (List Bool)) =>
      IH.flatMap fun word => [false :: word, true :: word] := by
    have hcons : Primrec₂ fun (_ : ℕ × List (List Bool)) (word : List Bool) =>
        [false :: word, true :: word] :=
      Primrec₂.mk <| Primrec.list_cons.comp
        (Primrec.list_cons.comp (Primrec.const false) Primrec.snd)
        (Primrec.list_cons.comp
          (Primrec.list_cons.comp (Primrec.const true) Primrec.snd)
          (Primrec.const []))
    exact Primrec₂.mk <| Primrec.list_flatMap Primrec.snd hcons
  refine (Primrec.nat_rec₁ [[]] hh).of_eq fun k => ?_
  have hrec : ∀ m : ℕ, Nat.rec [[]]
      (fun _ IH => IH.flatMap fun word => [false :: word, true :: word]) m =
      Cslib.BitString.enumList m := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [Cslib.BitString.enumList_succ, ← ih]
  exact hrec k

private theorem primrec_binaryValue : Primrec Cslib.BitString.binaryValue := by
  have hbool : Primrec fun b : Bool => b.toNat :=
    (Primrec.cond Primrec.id (Primrec.const 1) (Primrec.const 0)).of_eq fun b => by
      cases b <;> rfl
  have hh : Primrec₂ fun (_ : List Bool) (accb : ℕ × Bool) => 2 * accb.1 + accb.2.toNat :=
    Primrec₂.mk <| Primrec.nat_add.comp (Primrec.nat_double.comp (Primrec.fst.comp Primrec.snd))
      (hbool.comp (Primrec.snd.comp Primrec.snd))
  exact (Primrec.list_foldl Primrec.id (Primrec.const 0) hh).of_eq fun _ => rfl

/-! ### Binary expansion of real numbers in `[0, 1)` -/

/-- The `i`-th binary digit of a real number `x`, indexed from `0` after the binary point. -/
noncomputable def realBit (x : ℝ) (i : ℕ) : Bool :=
  decide (⌊x * (2 : ℝ) ^ (i + 1)⌋ % 2 = 1)

/-- The `n`-bit binary prefix of `x` after the binary point. -/
noncomputable def realPrefix (x : ℝ) (n : ℕ) : List Bool :=
  (List.range n).map (realBit x)

@[simp]
theorem length_realPrefix (x : ℝ) (n : ℕ) : (realPrefix x n).length = n := by
  simp [realPrefix]

theorem realPrefix_succ (x : ℝ) (n : ℕ) :
    realPrefix x (n + 1) = realPrefix x n ++ [realBit x n] := by
  simp [realPrefix, List.range_succ]

theorem getElem_realPrefix {x : ℝ} {n i : ℕ} (hi : i < (realPrefix x n).length) :
    (realPrefix x n)[i] = realBit x i := by
  simp [realPrefix]

private theorem floor_two_mul_eq (r : ℝ) :
    ⌊2 * r⌋ = 2 * ⌊r⌋ + (if ⌊2 * r⌋ % 2 = 1 then 1 else 0) := by
  have hr1 : (⌊r⌋ : ℝ) ≤ r := Int.floor_le r
  have hr2 : r < ⌊r⌋ + 1 := Int.lt_floor_add_one r
  have hbound : 2 * ⌊r⌋ ≤ ⌊2 * r⌋ ∧ ⌊2 * r⌋ ≤ 2 * ⌊r⌋ + 1 := by
    refine ⟨?_, ?_⟩
    · exact Int.le_floor.mpr (by push_cast; linarith)
    · have hlt : (⌊2 * r⌋ : ℝ) < (2 * ⌊r⌋ + 2 : ℤ) := by
        calc (⌊2 * r⌋ : ℝ) ≤ 2 * r := Int.floor_le (2 * r)
          _ < 2 * (⌊r⌋ + 1) := by linarith
          _ = ((2 * ⌊r⌋ + 2 : ℤ) : ℝ) := by push_cast; ring
      have hltZ : ⌊2 * r⌋ < 2 * ⌊r⌋ + 2 := by exact_mod_cast hlt
      omega
  omega

theorem binaryValue_realPrefix_eq_floor {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    (Cslib.BitString.binaryValue (realPrefix x n) : ℤ) = ⌊x * (2 : ℝ) ^ n⌋ := by
  induction n with
  | zero =>
    simp only [realPrefix, List.range_zero, List.map_nil, Cslib.BitString.binaryValue,
      List.foldl_nil, Nat.cast_zero, pow_zero, mul_one]
    exact (Int.floor_eq_zero_iff.mpr ⟨hx0, hx1⟩).symm
  | succ n ih =>
    rw [realPrefix_succ, Cslib.BitString.binaryValue_snoc]
    have hm := floor_two_mul_eq (x * (2 : ℝ) ^ n)
    have hrw : x * (2 : ℝ) ^ (n + 1) = 2 * (x * (2 : ℝ) ^ n) := by rw [pow_succ]; ring
    rw [← hrw] at hm
    rw [hrw]
    push_cast
    rw [ih, realBit, ← hrw]
    by_cases hmod : ⌊x * (2 : ℝ) ^ (n + 1)⌋ % 2 = 1
    · simp only [hmod, decide_true, Bool.toNat_true, Nat.cast_one]
      split_ifs at hm
      linarith
    · simp only [hmod, decide_false, Bool.toNat_false, Nat.cast_zero]
      split_ifs at hm
      linarith

/-- For `x ∈ [0, 1)`, the dyadic interval of `realPrefix x n` contains `x`. -/
theorem realPrefix_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    (Cslib.BitString.binaryValue (realPrefix x n) : ℝ) * (2 : ℝ)⁻¹ ^ n ≤ x ∧
      x < ((Cslib.BitString.binaryValue (realPrefix x n) : ℝ) + 1) * (2 : ℝ)⁻¹ ^ n := by
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hfloor : (Cslib.BitString.binaryValue (realPrefix x n) : ℝ) =
      ((⌊x * (2 : ℝ) ^ n⌋ : ℤ) : ℝ) := by
    exact_mod_cast binaryValue_realPrefix_eq_floor hx0 hx1 n
  have h1 : (⌊x * (2 : ℝ) ^ n⌋ : ℝ) ≤ x * (2 : ℝ) ^ n := Int.floor_le _
  have h2 : x * (2 : ℝ) ^ n < (⌊x * (2 : ℝ) ^ n⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  constructor
  · calc (Cslib.BitString.binaryValue (realPrefix x n) : ℝ) * (2 : ℝ)⁻¹ ^ n
      _ = (⌊x * (2 : ℝ) ^ n⌋ : ℝ) * ((2 : ℝ) ^ n)⁻¹ := by rw [hfloor, inv_pow]
      _ ≤ (x * (2 : ℝ) ^ n) * ((2 : ℝ) ^ n)⁻¹ := by
          gcongr
      _ = x := by rw [mul_assoc, mul_inv_cancel₀ hpow_pos.ne', mul_one]
  · calc x = (x * (2 : ℝ) ^ n) * ((2 : ℝ) ^ n)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hpow_pos.ne', mul_one]
      _ < ((⌊x * (2 : ℝ) ^ n⌋ : ℝ) + 1) * ((2 : ℝ) ^ n)⁻¹ := by gcongr
      _ = ((Cslib.BitString.binaryValue (realPrefix x n) : ℝ) + 1) * (2 : ℝ)⁻¹ ^ n := by
          rw [hfloor, inv_pow]

namespace DescriptionMethod

/-! ### Chaitin's halting probability `Ω` -/

/-- **Chaitin's halting probability `Ω`** of a description method `M`: the dyadic measure
`∑' p ∈ M.haltingSet, 2⁻¹ ^ |p|`. -/
@[expose] noncomputable def chaitinOmega {α : Type*} (M : DescriptionMethod α) : ℝ :=
  ∑' p : M.haltingSet, (2 : ℝ)⁻¹ ^ (p : List Bool).length

theorem chaitinOmega_nonneg {α : Type*} (M : DescriptionMethod α) : 0 ≤ chaitinOmega M :=
  tsum_nonneg fun _ => by positivity

/-- For every prefix-free description method, `chaitinOmega M ≤ 1` by Kraft's inequality. -/
theorem IsPrefixFree.chaitinOmega_le_one {α : Type*} {M : DescriptionMethod α}
    (hM : M.IsPrefixFree) : chaitinOmega M ≤ 1 :=
  hM.tsum_two_inv_pow_length_le_one

@[simp]
theorem chaitinOmega_universalPrefixBits :
    chaitinOmega universalPrefixBits = chaitinOmega universalPrefix := by
  rw [chaitinOmega, chaitinOmega, haltingSet_universalPrefixBits]

theorem chaitinOmega_universalPrefix_pos : 0 < chaitinOmega universalPrefix := by
  obtain ⟨p, hp⟩ := ecomplexity_ne_top_iff.mp (ecomplexity_universalPrefix_ne_top 0)
  have hp_mem : p ∈ universalPrefix.haltingSet := ⟨0, hp⟩
  have hle : (2 : ℝ)⁻¹ ^ p.length ≤ chaitinOmega universalPrefix := by
    have hs := isPrefixFree_universalPrefix.summable_two_inv_pow_length
    simpa [chaitinOmega] using
      hs.le_tsum ⟨p, hp_mem⟩ fun q _ => by positivity
  exact lt_of_lt_of_le (by positivity) hle

theorem chaitinOmega_universalPrefix_lt_one : chaitinOmega universalPrefix < 1 := by
  obtain ⟨q, hq⟩ := universalPrefix_exists_incomparable_prefix
  have hle := tsum_two_inv_pow_length_add_le_one_of_incomparable isPrefixFree_universalPrefix hq
  have hq_pos : (0 : ℝ) < (2 : ℝ)⁻¹ ^ q.length := by positivity
  change chaitinOmega universalPrefix + (2 : ℝ)⁻¹ ^ q.length ≤ 1 at hle
  linarith

/-! ### Left-c.e. dyadic approximation to `Ω` -/

/-- Candidate `(program, output)` pair enumerated at dovetailing index `k` for `universalPrefix`. -/
@[expose] def universalPrefixCand (k : ℕ) : Option (List Bool × ℕ) :=
  (decode (α := List Bool × ℕ) k).bind fun qt =>
    ((parseCodeHeader qt.1).bind fun cp =>
      (prefixAccepted cp.1 qt.2).lookup cp.2).map fun x => (qt.1, x)

theorem primrec_universalPrefixCand : Primrec universalPrefixCand := by
  have hinner : Primrec fun qtx : (List Bool × ℕ) × ℕ => (qtx.1.1, qtx.2) :=
    Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hlook : Primrec fun qt : List Bool × ℕ =>
      (parseCodeHeader qt.1).bind fun cp => (prefixAccepted cp.1 qt.2).lookup cp.2 :=
    Primrec.option_bind (primrec_parseCodeHeader.comp Primrec.fst)
      (primrec₂_prefixAccepted_lookup.comp Primrec.snd (Primrec.snd.comp Primrec.fst))
  have hmap : Primrec fun qt : List Bool × ℕ =>
      ((parseCodeHeader qt.1).bind fun cp =>
        (prefixAccepted cp.1 qt.2).lookup cp.2).map fun x => (qt.1, x) :=
    Primrec.option_map hlook hinner
  exact (Primrec.option_bind Primrec.decode (hmap.comp Primrec.snd).to₂).of_eq fun _ => rfl

/-- Stage-`n` prefix-free table of distinct `(program, output)` pairs accepted by
`universalPrefix`. -/
@[expose] def universalPrefixTable (n : ℕ) : List (List Bool × ℕ) :=
  Nat.distinctValues universalPrefixCand n

theorem primrec_universalPrefixTable : Primrec universalPrefixTable := by
  have h : Primrec₂ fun (_ : Unit) (k : ℕ) => universalPrefixCand k :=
    Primrec₂.mk <| primrec_universalPrefixCand.comp Primrec.snd
  exact ((Primrec.distinctValues h).comp (Primrec.const ()) Primrec.id).of_eq fun _ => rfl

theorem mem_universalPrefixTable_produces {n : ℕ} {q : List Bool} {x : ℕ}
    (h : (q, x) ∈ universalPrefixTable n) : universalPrefix.Produces q x := by
  obtain ⟨k, -, hk⟩ := Nat.mem_distinctValues.mp h
  simp only [universalPrefixCand, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hk
  obtain ⟨⟨q', t⟩, _, x', hx', hpair⟩ := hk
  cases hpair
  rw [universalPrefix_produces_iff]
  obtain ⟨⟨c, p⟩, hcp, hlook⟩ := hx'
  exact ⟨c, p, hcp, ofPrefixCode_produces_iff.mpr ⟨t, mem_prefixAccepted_iff_lookup.mpr hlook⟩⟩

theorem produces_iff_exists_mem_universalPrefixTable {q : List Bool} {x : ℕ} :
    universalPrefix.Produces q x ↔ ∃ n, (q, x) ∈ universalPrefixTable n := by
  constructor
  · intro hprod
    obtain ⟨c, p, hcp, hp⟩ := universalPrefix_produces_iff.mp hprod
    obtain ⟨t, ht⟩ := ofPrefixCode_produces_iff.mp hp
    refine ⟨encode (q, t) + 1, Nat.mem_distinctValues.mpr ⟨encode (q, t), Nat.lt_succ_self _, ?_⟩⟩
    simp [universalPrefixCand, hcp, Option.mem_def.mp (mem_prefixAccepted_iff_lookup.mp ht)]
  · rintro ⟨n, hn⟩
    exact mem_universalPrefixTable_produces hn

theorem haltingSet_iff_exists_mem_universalPrefixTable {q : List Bool} :
    q ∈ universalPrefix.haltingSet ↔ ∃ n, q ∈ (universalPrefixTable n).map Prod.fst := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨n, hn⟩ := produces_iff_exists_mem_universalPrefixTable.mp hx
    exact ⟨n, List.mem_map.mpr ⟨(q, x), hn, rfl⟩⟩
  · rintro ⟨n, hn⟩
    obtain ⟨⟨q', x⟩, hmem, rfl⟩ := List.mem_map.mp hn
    exact ⟨x, mem_universalPrefixTable_produces hmem⟩

theorem nodup_map_fst_universalPrefixTable (n : ℕ) :
    ((universalPrefixTable n).map Prod.fst).Nodup := by
  refine (Nat.nodup_distinctValues universalPrefixCand n).map_on fun a ha b hb heq => ?_
  have ha' := mem_universalPrefixTable_produces ha
  have hb' := mem_universalPrefixTable_produces hb
  rw [heq] at ha'
  have hdet := Part.mem_unique
    (isPartrec_universalPrefix.choose_spec.2 _ _ |>.mp ha')
    (isPartrec_universalPrefix.choose_spec.2 _ _ |>.mp hb')
  exact Prod.ext heq hdet

theorem universalPrefixTable_prefix {m n : ℕ} (hmn : m ≤ n) :
    universalPrefixTable m <+: universalPrefixTable n :=
  Nat.distinctValues_prefix universalPrefixCand hmn

theorem mem_map_fst_universalPrefixTable_mono {m n : ℕ} (hmn : m ≤ n) {q : List Bool}
    (hq : q ∈ (universalPrefixTable m).map Prod.fst) :
    q ∈ (universalPrefixTable n).map Prod.fst :=
  List.mem_map.mpr <| let ⟨px, hpx, hpeq⟩ := List.mem_map.mp hq
    ⟨px, (universalPrefixTable_prefix hmn).subset hpx, hpeq⟩

/-- Monotone dyadic rational approximation `Ω_n` to `chaitinOmega universalPrefix` at stage `n`. -/
@[expose] def universalPrefixApprox (n : ℕ) : ℚ :=
  listWeight ((universalPrefixTable n).map Prod.fst)

theorem monotone_universalPrefixApprox : Monotone universalPrefixApprox := by
  intro m n hmn
  obtain ⟨t, ht⟩ := universalPrefixTable_prefix hmn
  rw [universalPrefixApprox, universalPrefixApprox, ← ht, List.map_append, listWeight_append]
  have hnonneg : 0 ≤ listWeight (t.map Prod.fst) := by
    refine List.sum_nonneg fun x hx => ?_
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hx
    simp only [wordWeight]
    positivity
  linarith

private theorem universalPrefixApprox_eq_finsetSum (n : ℕ) :
    (universalPrefixApprox n : ℝ) =
      ∑ w ∈ ((universalPrefixTable n).map Prod.fst).toFinset, (2 : ℝ)⁻¹ ^ w.length := by
  have hnodup := nodup_map_fst_universalPrefixTable n
  have hcast : ∀ L : List (List Bool),
      ((L.map wordWeight).sum : ℝ) = (L.map fun w => (2 : ℝ)⁻¹ ^ w.length).sum := by
    intro L
    induction L with
    | nil => simp
    | cons a l ih => simp [wordWeight, ih]
  rw [universalPrefixApprox, listWeight, hcast,
    ← List.sum_toFinset (fun w : List Bool => (2 : ℝ)⁻¹ ^ w.length) hnodup]

theorem universalPrefixApprox_le_chaitinOmega (n : ℕ) :
    (universalPrefixApprox n : ℝ) ≤ chaitinOmega universalPrefix := by
  classical
  rw [universalPrefixApprox_eq_finsetSum]
  let T := ((universalPrefixTable n).map Prod.fst).toFinset
  have hT : (T : Set (List Bool)) ⊆ universalPrefix.haltingSet := fun w hw =>
    haltingSet_iff_exists_mem_universalPrefixTable.mpr ⟨n, List.mem_toFinset.mp hw⟩
  let fEmbed : {w : List Bool // w ∈ T} ↪ universalPrefix.haltingSet :=
    ⟨fun x => ⟨x.1, hT x.2⟩,
      fun a b h => Subtype.ext (congrArg (fun z : universalPrefix.haltingSet => z.1) h)⟩
  let F : Finset universalPrefix.haltingSet := T.attach.map fEmbed
  have hF : ∑ w ∈ F, (2 : ℝ)⁻¹ ^ (w : List Bool).length = ∑ w ∈ T, (2 : ℝ)⁻¹ ^ w.length := by
    rw [Finset.sum_map]
    exact Finset.sum_attach T fun w => (2 : ℝ)⁻¹ ^ w.length
  rw [← hF]
  exact isPrefixFree_universalPrefix.summable_two_inv_pow_length.sum_le_tsum F
    fun _ _ => by positivity

/-- `universalPrefixApprox` converges from below to `chaitinOmega universalPrefix`. -/
theorem tendsto_universalPrefixApprox :
    Tendsto (fun n => (universalPrefixApprox n : ℝ)) atTop (𝓝 (chaitinOmega universalPrefix)) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hs := isPrefixFree_universalPrefix.summable_two_inv_pow_length
  have htend : ∃ F₀ : Finset universalPrefix.haltingSet,
      chaitinOmega universalPrefix - ε <
        ∑ w ∈ F₀, (2 : ℝ)⁻¹ ^ (w : List Bool).length := by
    by_contra! hall
    have hle := hs.tsum_le_of_sum_le hall
    change chaitinOmega universalPrefix ≤ chaitinOmega universalPrefix - ε at hle
    linarith
  obtain ⟨F₀, hF₀⟩ := htend
  have hex_n : ∀ q : universalPrefix.haltingSet,
      ∃ n, q.1 ∈ (universalPrefixTable n).map Prod.fst := fun q =>
    haltingSet_iff_exists_mem_universalPrefixTable.mp q.2
  let N : ℕ := F₀.sup fun q => Nat.find (hex_n q)
  refine ⟨N, fun n hn => ?_⟩
  have hsub : F₀.image Subtype.val ⊆ ((universalPrefixTable n).map Prod.fst).toFinset := by
    intro w hw
    obtain ⟨q, hqF, rfl⟩ := Finset.mem_image.mp hw
    have hqn : Nat.find (hex_n q) ≤ n := (Finset.le_sup hqF).trans hn
    exact List.mem_toFinset.mpr
      (mem_map_fst_universalPrefixTable_mono hqn (Nat.find_spec (hex_n q)))
  have hsum_F₀ : ∑ w ∈ F₀, (2 : ℝ)⁻¹ ^ (w : List Bool).length =
      ∑ w ∈ F₀.image Subtype.val, (2 : ℝ)⁻¹ ^ w.length :=
    (Finset.sum_image (f := fun w : List Bool => (2 : ℝ)⁻¹ ^ w.length)
      fun _ _ _ _ h => Subtype.ext h).symm
  have hle_approx : ∑ w ∈ F₀, (2 : ℝ)⁻¹ ^ (w : List Bool).length ≤
      (universalPrefixApprox n : ℝ) := by
    rw [hsum_F₀, universalPrefixApprox_eq_finsetSum]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  have hle_omega := universalPrefixApprox_le_chaitinOmega n
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

-- Maximum program length occurring in `universalPrefixTable n`.
private def universalPrefixMaxLen (n : ℕ) : ℕ :=
  ((universalPrefixTable n).map Prod.fst).foldr (fun w m => max w.length m) 0

-- Scaled integer numerator `universalPrefixApprox n * 2 ^ universalPrefixMaxLen n`.
private def universalPrefixScaled (n : ℕ) : ℕ :=
  (((universalPrefixTable n).map Prod.fst).map
    fun w => 2 ^ (universalPrefixMaxLen n - w.length)).sum

private theorem primrec_universalPrefixMaxLen : Primrec universalPrefixMaxLen := by
  have hh : Primrec₂ fun (_ : ℕ) (wm : List Bool × ℕ) => max wm.1.length wm.2 :=
    Primrec₂.mk <| Primrec.nat_max.comp
      (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldr
    (Primrec.list_map primrec_universalPrefixTable (Primrec.fst.comp Primrec.snd).to₂)
    (Primrec.const 0) hh).of_eq fun _ => rfl

private theorem primrec_universalPrefixScaled : Primrec universalPrefixScaled := by
  have hprog : Primrec fun n => (universalPrefixTable n).map Prod.fst :=
    Primrec.list_map primrec_universalPrefixTable (Primrec.fst.comp Primrec.snd).to₂
  have hel : Primrec₂ fun (n : ℕ) (w : List Bool) => 2 ^ (universalPrefixMaxLen n - w.length) :=
    Primrec₂.mk <| primrec_two_pow.comp
      (Primrec.nat_sub.comp (primrec_universalPrefixMaxLen.comp Primrec.fst)
        (Primrec.list_length.comp Primrec.snd))
  exact (Primrec.list_sum (Primrec.list_map hprog hel)).of_eq fun _ => rfl

private theorem universalPrefixScaled_cast (n : ℕ) :
    (universalPrefixApprox n : ℝ) * (2 : ℝ) ^ universalPrefixMaxLen n =
      (universalPrefixScaled n : ℝ) := by
  have hle : ∀ w ∈ (universalPrefixTable n).map Prod.fst, w.length ≤ universalPrefixMaxLen n :=
    fun _ hw => length_le_foldr_max _ hw
  simp only [universalPrefixApprox, listWeight, universalPrefixScaled]
  set L := (universalPrefixTable n).map Prod.fst
  set M := universalPrefixMaxLen n
  clear_value L M
  induction L with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons, Rat.cast_add, add_mul, Nat.cast_add]
    have ha : a.length ≤ M := hle a List.mem_cons_self
    have hpow_eq : (wordWeight a : ℝ) * (2 : ℝ) ^ M = ((2 ^ (M - a.length) : ℕ) : ℝ) := by
      have hM : a.length + (M - a.length) = M := Nat.add_sub_of_le ha
      simp only [wordWeight, Rat.cast_pow, Rat.cast_inv, Rat.cast_ofNat]
      conv_lhs =>
        rw [← hM, pow_add, ← mul_assoc, inv_pow, inv_mul_cancel₀ (by positivity), one_mul]
      push_cast
      rfl
    have hrest := ih fun w hw => hle w (List.mem_cons_of_mem a hw)
    push_cast at hrest ⊢
    rw [hpow_eq, hrest]
    push_cast
    rfl

/-! ### Undecidability of `universalPrefix.haltingSet`, irrationality, and uncomputability -/

private def universalPrefixHdrTest (cq : Code × List Bool) : Bool :=
  decide (encode (parseCodeHeader cq.2) = encode (some (cq.1, ([] : List Bool))))

private theorem computable_universalPrefixHdrTest : Computable universalPrefixHdrTest :=
  Primrec.eq.decide.to_comp.comp
    (Primrec.encode.to_comp.comp (primrec_parseCodeHeader.to_comp.comp Computable.snd))
    (Primrec.encode.to_comp.comp
      (Computable.option_some.comp (Computable.fst.pair (Computable.const ([] : List Bool)))))

private theorem computable_codeHeader : Computable codeHeader := by
  have hstep : Computable₂ fun (c : Code) (n : ℕ) =>
      (decode (α := List Bool) n).bind fun q =>
        bif universalPrefixHdrTest (c, q) then some q else Option.none :=
    Computable.option_bind (Computable.decode.comp Computable.snd)
      (Computable.cond
        (computable_universalPrefixHdrTest.comp
          (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd))
        (Computable.option_some.comp Computable.snd)
        (Computable.const Option.none)).to₂
  let findHdr : Code →. List Bool := fun c => Nat.rfindOpt fun n =>
    (decode (α := List Bool) n).bind fun q =>
      bif universalPrefixHdrTest (c, q) then some q else Option.none
  have hfind : Partrec findHdr := Partrec.rfindOpt hstep
  have hdom : ∀ c : Code, (findHdr c).Dom := fun c => by
    have hpc : parseCodeHeader (codeHeader c) = some (c, []) :=
      parseCodeHeader_eq_some_iff.mpr (List.append_nil _)
    refine Nat.rfindOpt_dom.mpr ⟨encode (codeHeader c), codeHeader c, ?_⟩
    rw [Option.mem_def, encodek]
    simp [universalPrefixHdrTest, hpc]
  refine hfind.of_eq fun c => ?_
  have hmem := Part.get_mem (hdom c)
  obtain ⟨n, hn⟩ := Nat.rfindOpt_spec hmem
  simp only [Option.mem_def, Option.bind_eq_some_iff] at hn
  obtain ⟨q, -, hq⟩ := hn
  by_cases hp : parseCodeHeader q = some (c, [])
  · have ht : universalPrefixHdrTest (c, q) = true := by simp [universalPrefixHdrTest, hp]
    simp only [ht, Bool.cond_true, Option.some.injEq] at hq
    have hqc : codeHeader c = q := by
      simpa using parseCodeHeader_eq_some_iff.mp hp
    rw [← hqc] at hq
    exact (Part.some_get (hdom c)).symm.trans (congrArg Part.some hq.symm)
  · have ht : universalPrefixHdrTest (c, q) = false := by
      simp only [universalPrefixHdrTest, decide_eq_false_iff_not]
      exact fun he => hp (encode_injective he)
    simp [ht] at hq

private def haltingReduceStep (ab : ℕ × ℕ) (k : ℕ) : Option ℕ :=
  if ab.2 = encode ([] : List Bool) then Code.evaln k (ofNat Code ab.1) 0 else Option.none

private theorem primrec₂_haltingReduceStep : Primrec₂ haltingReduceStep :=
  Primrec₂.mk <| (Primrec.ite
    (Primrec.eq.comp (Primrec.snd.comp Primrec.fst) (Primrec.const (encode ([] : List Bool))))
    (Code.primrec_evaln.comp (Primrec.pair (Primrec.pair Primrec.snd
      ((Primrec.ofNat Code).comp (Primrec.fst.comp Primrec.fst))) (Primrec.const 0)))
    (Primrec.const Option.none)).of_eq fun _ => rfl

/-- Deciding the halting domain of `universalPrefix` solves the halting problem. -/
theorem not_computablePred_haltingSet_universalPrefix :
    ¬ ComputablePred fun q : List Bool => q ∈ universalPrefix.haltingSet := by
  intro hhalt
  have hF : Nat.Partrec fun n : ℕ => Nat.rfindOpt (haltingReduceStep n.unpair) :=
    Partrec.nat_iff.mp <| Partrec.rfindOpt
      (Primrec₂.comp primrec₂_haltingReduceStep
        (Primrec.unpair.comp Primrec.fst) Primrec.snd).to_comp
  obtain ⟨d, hd⟩ := Code.exists_code.mp hF
  let D : Code → Code := fun c => d.curry (encode c)
  have hD_comp : Computable D :=
    (Code.primrec₂_curry.comp (Primrec.const d) Primrec.encode).to_comp
  have hD_eval : ∀ c b, (D c).eval b =
      if b = encode ([] : List Bool) then c.eval 0 else Part.none := by
    intro c b
    simp only [D, Code.eval_curry]
    rw [hd]
    dsimp only
    rw [Nat.unpair_pair]
    by_cases hb : b = encode ([] : List Bool)
    · ext y
      rw [Nat.rfindOpt_mono fun {a m n} hmn ha => by
        simp only [haltingReduceStep, hb, ↓reduceIte] at ha ⊢
        exact Code.evaln_mono hmn ha]
      simp [haltingReduceStep, hb, Code.evaln_complete]
    · simp only [hb, ↓reduceIte]
      rw [Part.eq_none_iff']
      intro hdom
      obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp hdom
      obtain ⟨k, hk⟩ := Nat.rfindOpt_spec hy
      simp only [haltingReduceStep, hb, ↓reduceIte, Option.mem_def] at hk
      cases hk
  have hD_pf : ∀ c : Code, (ofCode (D c)).IsPrefixFree := by
    intro c p₁ ⟨y₁, hp₁⟩ p₂ ⟨y₂, hp₂⟩ _
    rw [ofCode_produces_iff, hD_eval] at hp₁ hp₂
    by_cases hp₁_nil : p₁ = []
    · by_cases hp₂_nil : p₂ = []
      · exact hp₁_nil.trans hp₂_nil.symm
      · have hne : encode p₂ ≠ encode ([] : List Bool) := encode_injective.ne hp₂_nil
        simp only [hne, ↓reduceIte, Part.notMem_none] at hp₂
    · have hne : encode p₁ ≠ encode ([] : List Bool) := encode_injective.ne hp₁_nil
      simp only [hne, ↓reduceIte, Part.notMem_none] at hp₁
  have hiff : ∀ c : Code,
      (codeHeader (D c) ++ [] ∈ universalPrefix.haltingSet) ↔ (c.eval 0).Dom := by
    intro c
    constructor
    · rintro ⟨x, hx⟩
      rw [universalPrefix_produces_codeHeader_append] at hx
      have hx' := ofCode_produces_iff.mp (ofCode_produces_of_ofPrefixCode_produces hx)
      rw [hD_eval] at hx'
      simp only [↓reduceIte] at hx'
      exact Part.dom_iff_mem.mpr ⟨x, hx'⟩
    · intro hdom
      obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp hdom
      have hprod : (ofCode (D c)).Produces [] x := by
        rw [ofCode_produces_iff, hD_eval]
        simpa using hx
      exact ⟨x, universalPrefix_produces_codeHeader_append.mpr
        ((ofPrefixCode_produces_iff_of_isPrefixFree (hD_pf c)).mpr hprod)⟩
  have hhalt' : ComputablePred fun c : Code => (c.eval 0).Dom := by
    have hcomp := hhalt.comp (Primrec.list_append.to_comp.comp (computable_codeHeader.comp hD_comp)
      (Computable.const ([] : List Bool)))
    exact hcomp.of_eq fun c => hiff c
  exact ComputablePred.halting_problem 0 hhalt'

private def universalPrefixCondHalted (p : List Bool) (t : ℕ) : Bool :=
  ((universalPrefixTable t).map Prod.fst).any fun q => decide (q = p)

private theorem primrec₂_universalPrefixCondHalted : Primrec₂ universalPrefixCondHalted := by
  have hrel : PrimrecRel (fun (L : List (List Bool)) (p : List Bool) => ∃ q ∈ L, q = p) :=
    PrimrecRel.exists_mem_list Primrec.eq
  have hpred := hrel.comp
    (Primrec.list_map (primrec_universalPrefixTable.comp Primrec.snd)
      (Primrec.fst.comp Primrec.snd).to₂) Primrec.fst
  refine Primrec₂.mk <| hpred.decide.of_eq fun ⟨p, t⟩ => ?_
  have hiff : (∃ q ∈ (universalPrefixTable t).map Prod.fst, q = p) ↔
      universalPrefixCondHalted p t = true := by
    simp [universalPrefixCondHalted, List.any_eq_true]
  exact Bool.eq_iff_iff.mpr (decide_eq_true_iff.trans hiff)

private def approxCondClose (num den : ℕ → ℕ) (p : List Bool) (t : ℕ) : Bool :=
  let m := p.length + 2
  decide ((num m * 2 ^ m + den m) * 2 ^ (universalPrefixMaxLen t + p.length) <
    (universalPrefixScaled t * 2 ^ p.length + 2 ^ universalPrefixMaxLen t) *
      2 ^ m * den m)

private theorem computable₂_approxCondClose {num den : ℕ → ℕ}
    (hnum : Computable num) (hden : Computable den) :
    Computable₂ (approxCondClose num den) := by
  have hfst : Computable fun pt : List Bool × ℕ => pt.1 := Computable.fst
  have hsnd : Computable fun pt : List Bool × ℕ => pt.2 := Computable.snd
  have hm : Computable fun pt : List Bool × ℕ => pt.1.length + 2 :=
    (Primrec.nat_add.comp Primrec.list_length (Primrec.const 2)).to_comp.comp hfst
  have hpow2 : Computable fun n : ℕ => 2 ^ n := primrec_two_pow.to_comp
  have hnum_m := hnum.comp hm
  have hden_m := hden.comp hm
  have hm_pow := hpow2.comp hm
  have hmax_len : Computable fun pt : List Bool × ℕ => universalPrefixMaxLen pt.2 :=
    primrec_universalPrefixMaxLen.to_comp.comp hsnd
  have hlen_p : Computable fun pt : List Bool × ℕ => pt.1.length :=
    Computable.list_length.comp hfst
  have hlhs : Computable fun pt : List Bool × ℕ =>
      (num (pt.1.length + 2) * 2 ^ (pt.1.length + 2) + den (pt.1.length + 2)) *
        2 ^ (universalPrefixMaxLen pt.2 + pt.1.length) :=
    Primrec.nat_mul.to_comp.comp
      (Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp hnum_m hm_pow) hden_m)
      (hpow2.comp (Primrec.nat_add.to_comp.comp hmax_len hlen_p))
  have hrhs : Computable fun pt : List Bool × ℕ =>
      (universalPrefixScaled pt.2 * 2 ^ pt.1.length + 2 ^ universalPrefixMaxLen pt.2) *
        2 ^ (pt.1.length + 2) * den (pt.1.length + 2) :=
    Primrec.nat_mul.to_comp.comp
      (Primrec.nat_mul.to_comp.comp
        (Primrec.nat_add.to_comp.comp
          (Primrec.nat_mul.to_comp.comp
            (primrec_universalPrefixScaled.to_comp.comp hsnd) (hpow2.comp hlen_p))
          (hpow2.comp hmax_len))
        hm_pow)
      hden_m
  exact (Primrec.nat_lt.decide.to_comp.comp hlhs hrhs).of_eq fun _ => rfl

/-- **Uncomputability of Chaitin's `Ω`**: no pair of computable sequences `(num, den)` with
`den m > 0` approximates `chaitinOmega universalPrefix` within `(2 : ℝ)⁻¹ ^ m` at every `m`. -/
theorem not_exists_computable_approx_chaitinOmega :
    ¬ ∃ (num den : ℕ → ℕ), Computable num ∧ Computable den ∧ (∀ m, 0 < den m) ∧
      ∀ m : ℕ, |chaitinOmega universalPrefix - (num m : ℝ) / (den m : ℝ)| ≤ (2 : ℝ)⁻¹ ^ m := by
  rintro ⟨num, den, hnum, hden, hden_pos, happrox⟩
  let haltTest (p : List Bool) (t : ℕ) : Bool :=
    universalPrefixCondHalted p t || approxCondClose num den p t
  have hcondHalted := primrec₂_universalPrefixCondHalted
  have hcondClose := computable₂_approxCondClose hnum hden
  have hhaltTest : Computable₂ haltTest := by
    change Computable fun pt : List Bool × ℕ =>
      universalPrefixCondHalted pt.1 pt.2 || approxCondClose num den pt.1 pt.2
    exact (Computable.cond hcondHalted.to_comp (Computable.const true) hcondClose).of_eq
      fun ⟨p, t⟩ => by cases universalPrefixCondHalted p t <;> rfl
  have hcondClose_iff : ∀ p t, approxCondClose num den p t = true ↔
      (num (p.length + 2) : ℝ) / (den (p.length + 2) : ℝ) + (2 : ℝ)⁻¹ ^ (p.length + 2) <
        (universalPrefixApprox t : ℝ) + (2 : ℝ)⁻¹ ^ p.length := by
    intro p t
    set m := p.length + 2
    set M := universalPrefixMaxLen t
    have hdpos : (0 : ℝ) < (den m : ℝ) := by exact_mod_cast hden_pos m
    have hpow_m : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
    have hpow_Mp : (0 : ℝ) < (2 : ℝ) ^ (M + p.length) := by positivity
    have hdenom : (0 : ℝ) < (den m : ℝ) * (2 : ℝ) ^ m * (2 : ℝ) ^ (M + p.length) := by positivity
    simp only [approxCondClose, m, decide_eq_true_eq]
    have hsc := universalPrefixScaled_cast t
    have hcast_lhs :
        (((num m * 2 ^ m + den m) * 2 ^ (M + p.length) : ℕ) : ℝ) =
          ((num m : ℝ) / (den m : ℝ) + (2 : ℝ)⁻¹ ^ m) *
            ((den m : ℝ) * (2 : ℝ) ^ m * (2 : ℝ) ^ (M + p.length)) := by
      rw [inv_pow]
      field_simp
      push_cast
      ring
    have hcast_rhs :
        (((universalPrefixScaled t * 2 ^ p.length + 2 ^ M) * 2 ^ m * den m : ℕ) : ℝ) =
          ((universalPrefixApprox t : ℝ) + (2 : ℝ)⁻¹ ^ p.length) *
            ((den m : ℝ) * (2 : ℝ) ^ m * (2 : ℝ) ^ (M + p.length)) := by
      have hm_eq : m = p.length + 2 := rfl
      have hsc' : (universalPrefixScaled t : ℝ) =
          (universalPrefixApprox t : ℝ) * (2 : ℝ) ^ M := hsc.symm
      have hpow_p : (2 : ℝ) ^ p.length ≠ 0 := by positivity
      rw [inv_pow, pow_add]
      field_simp
      push_cast
      rw [hsc', hm_eq]
      ring
    rw [← @Nat.cast_lt ℝ, hcast_lhs, hcast_rhs, mul_lt_mul_iff_left₀ hdenom]
  have hex_haltTest : ∀ p : List Bool, ∃ t : ℕ, haltTest p t = true := by
    intro p
    have hε : (0 : ℝ) < (2 : ℝ)⁻¹ ^ (p.length + 1) := by positivity
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp tendsto_universalPrefixApprox _ hε
    refine ⟨N, ?_⟩
    have hdist := hN N le_rfl
    rw [Real.dist_eq, abs_sub_lt_iff] at hdist
    have happ := happrox (p.length + 2)
    rw [abs_sub_le_iff] at happ
    have hpow_eq : 2 * (2 : ℝ)⁻¹ ^ (p.length + 2) + (2 : ℝ)⁻¹ ^ (p.length + 1) =
        (2 : ℝ)⁻¹ ^ p.length := by
      rw [pow_succ, pow_succ]
      ring
    have hclose : approxCondClose num den p N = true := by
      rw [hcondClose_iff]
      linarith [happ.2, hdist.2, hpow_eq]
    simp [haltTest, hclose]
  have hdec_part :
      Partrec fun p : List Bool => Nat.rfind fun t => Part.some (haltTest p t) :=
    Partrec.rfind hhaltTest.partrec₂
  have hdom_stage :
      ∀ p : List Bool, (Nat.rfind fun t => Part.some (haltTest p t)).Dom := fun p => by
    obtain ⟨t, ht⟩ := hex_haltTest p
    obtain ⟨t', ht', _⟩ := Nat.rfind_min' (p := fun t => haltTest p t) ht
    exact Part.dom_iff_mem.mpr ⟨t', ht'⟩
  let stage : List Bool → ℕ := fun p =>
    (Nat.rfind fun t => Part.some (haltTest p t)).get (hdom_stage p)
  have hstage : Computable stage :=
    hdec_part.of_eq fun p => (Part.some_get (hdom_stage p)).symm
  have hdec : Computable fun p : List Bool => universalPrefixCondHalted p (stage p) :=
    hcondHalted.to_comp.comp Computable.id hstage
  have hiff : ∀ p : List Bool,
      universalPrefixCondHalted p (stage p) = true ↔ p ∈ universalPrefix.haltingSet := by
    intro p
    constructor
    · intro hp
      simp only [universalPrefixCondHalted, List.any_eq_true, decide_eq_true_eq] at hp
      obtain ⟨q, hq, hqp⟩ := hp
      rw [← hqp]
      exact haltingSet_iff_exists_mem_universalPrefixTable.mpr ⟨stage p, hq⟩
    · intro hp
      by_contra hnot
      have hspec : haltTest p (stage p) = true := by
        simpa [stage] using Nat.rfind_spec (Part.get_mem (hdom_stage p))
      have hnot' : universalPrefixCondHalted p (stage p) = false := Bool.eq_false_iff.mpr hnot
      simp only [haltTest, hnot', Bool.false_or] at hspec
      rw [hcondClose_iff] at hspec
      have hnotin : p ∉ ((universalPrefixTable (stage p)).map Prod.fst).toFinset := by
        intro hmem
        apply hnot
        simp only [universalPrefixCondHalted, List.any_eq_true, decide_eq_true_eq]
        exact ⟨p, List.mem_toFinset.mp hmem, rfl⟩
      have hsub :
          (((universalPrefixTable (stage p)).map Prod.fst).toFinset : Set (List Bool)) ⊆
            universalPrefix.haltingSet := fun q hq =>
        haltingSet_iff_exists_mem_universalPrefixTable.mpr ⟨stage p, List.mem_toFinset.mp hq⟩
      have htail := finsetSum_add_two_inv_pow_le_tsum_of_notMem isPrefixFree_universalPrefix hsub
        hp hnotin
      rw [← universalPrefixApprox_eq_finsetSum] at htail
      change (universalPrefixApprox (stage p) : ℝ) + (2 : ℝ)⁻¹ ^ p.length ≤
        chaitinOmega universalPrefix at htail
      have happ := (abs_sub_le_iff.mp (happrox (p.length + 2))).1
      linarith
  have hpred : ComputablePred fun p : List Bool => p ∈ universalPrefix.haltingSet :=
    ComputablePred.computable_iff.mpr
      ⟨fun p => universalPrefixCondHalted p (stage p), hdec,
        funext fun p => propext (hiff p).symm⟩
  exact not_computablePred_haltingSet_universalPrefix hpred

/-- **Chaitin's `Ω` is irrational** [Chaitin1974], [LiVitanyi2019]. -/
theorem irrational_chaitinOmega_universalPrefix :
    Irrational (chaitinOmega universalPrefix) := by
  intro ⟨q, hq⟩
  have hq0 : 0 ≤ q := by
    have : (0 : ℝ) ≤ (q : ℝ) := hq.symm ▸ chaitinOmega_nonneg universalPrefix
    exact_mod_cast this
  have hnum : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq0)
  apply not_exists_computable_approx_chaitinOmega
  refine ⟨fun _ => q.num.toNat, fun _ => q.den, Computable.const _, Computable.const _,
    fun _ => q.pos, fun m => ?_⟩
  have hq_real : (chaitinOmega universalPrefix : ℝ) = (q.num.toNat : ℝ) / (q.den : ℝ) := by
    rw [← hq]
    have hq_rat : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := Rat.cast_def q
    rw [hq_rat]
    congr 1
    exact_mod_cast hnum.symm
  rw [hq_real, sub_self, abs_zero]
  positivity

-- No computable dyadic integer numerator approximates `chaitinOmega universalPrefix` within
-- `2⁻¹ ^ m`.
private theorem not_exists_computable_dyadic_approx_chaitinOmega :
    ¬ ∃ f : ℕ → ℕ, Computable f ∧
      ∀ m : ℕ, |chaitinOmega universalPrefix - (f m : ℝ) * (2 : ℝ)⁻¹ ^ m| ≤ (2 : ℝ)⁻¹ ^ m := by
  rintro ⟨f, hf, happrox⟩
  apply not_exists_computable_approx_chaitinOmega
  refine ⟨f, fun m => 2 ^ m, hf, primrec_two_pow.to_comp, fun _ => by positivity, fun m => ?_⟩
  simpa [div_eq_mul_inv, inv_pow] using happrox m

/-- **The binary expansion of Chaitin's `Ω` is uncomputable.** -/
theorem not_computable_realBit_chaitinOmega_universalPrefix :
    ¬ Computable (realBit (chaitinOmega universalPrefix)) := by
  intro hbits
  let f : ℕ → ℕ := fun m =>
    Cslib.BitString.binaryValue (realPrefix (chaitinOmega universalPrefix) m)
  have hf : Computable f := by
    have hstep : Computable₂ fun (_ : ℕ) (p : ℕ × ℕ) =>
        2 * p.2 + (realBit (chaitinOmega universalPrefix) p.1).toNat := by
      have hbit : Computable fun arg : ℕ × (ℕ × ℕ) =>
          (realBit (chaitinOmega universalPrefix) arg.2.1).toNat :=
        (Primrec.cond Primrec.id (Primrec.const 1) (Primrec.const 0)).to_comp.comp
          (hbits.comp (Computable.fst.comp Computable.snd)) |>.of_eq fun _ => by
            cases realBit _ _ <;> rfl
      exact (Primrec.nat_add.to_comp.comp
        (Primrec.nat_double.to_comp.comp (Computable.snd.comp Computable.snd)) hbit).to₂
    refine (Computable.nat_rec Computable.id (Computable.const 0) hstep).of_eq fun m => ?_
    have hrec : ∀ n : ℕ, Nat.rec 0
        (fun y IH => 2 * IH + (realBit (chaitinOmega universalPrefix) y).toNat) n = f n := by
      intro n
      induction n with
      | zero => simp [f, realPrefix, Cslib.BitString.binaryValue]
      | succ n ih =>
        change 2 * Nat.rec 0 _ n + _ = _
        rw [ih]
        simp only [f, realPrefix_succ, Cslib.BitString.binaryValue_snoc]
    exact hrec m
  apply not_exists_computable_dyadic_approx_chaitinOmega
  refine ⟨f, hf, fun m => ?_⟩
  have hb := realPrefix_bounds chaitinOmega_universalPrefix_pos.le
    chaitinOmega_universalPrefix_lt_one m
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-! ### Halting connection and incompressibility of initial segments of `Ω` -/

theorem binaryValue_realPrefix_chaitinOmega_mul_lt (n : ℕ) :
    (Cslib.BitString.binaryValue (realPrefix (chaitinOmega universalPrefix) n) : ℝ) *
      (2 : ℝ)⁻¹ ^ n < chaitinOmega universalPrefix := by
  have hb := (realPrefix_bounds chaitinOmega_universalPrefix_pos.le
    chaitinOmega_universalPrefix_lt_one n).1
  refine lt_of_le_of_ne hb fun heq => ?_
  apply irrational_chaitinOmega_universalPrefix
  let q : ℚ := (Cslib.BitString.binaryValue (realPrefix (chaitinOmega universalPrefix) n) : ℚ) *
    (2 : ℚ)⁻¹ ^ n
  refine ⟨q, ?_⟩
  push_cast [q]
  exact heq

/-- **Halting connection**: once `universalPrefixApprox t` overtakes the lower dyadic endpoint
of `Ω ↾ n`, `universalPrefixTable t` already contains every halting program of length at most
`n`. -/
theorem universalPrefixTable_captures_length_le {n t : ℕ}
    (ht : (Cslib.BitString.binaryValue (realPrefix (chaitinOmega universalPrefix) n) : ℝ) *
      (2 : ℝ)⁻¹ ^ n < (universalPrefixApprox t : ℝ))
    {q : List Bool} (hq : q ∈ universalPrefix.haltingSet) (hlen : q.length ≤ n) :
    q ∈ (universalPrefixTable t).map Prod.fst := by
  by_contra hnot
  have hnotin : q ∉ ((universalPrefixTable t).map Prod.fst).toFinset := by
    simpa using hnot
  have hsub : (((universalPrefixTable t).map Prod.fst).toFinset : Set (List Bool)) ⊆
      universalPrefix.haltingSet := fun w hw =>
    haltingSet_iff_exists_mem_universalPrefixTable.mpr ⟨t, List.mem_toFinset.mp hw⟩
  have htail := finsetSum_add_two_inv_pow_le_tsum_of_notMem isPrefixFree_universalPrefix hsub hq
    hnotin
  rw [← universalPrefixApprox_eq_finsetSum] at htail
  change (universalPrefixApprox t : ℝ) + (2 : ℝ)⁻¹ ^ q.length ≤
    chaitinOmega universalPrefix at htail
  have hupper := (realPrefix_bounds chaitinOmega_universalPrefix_pos.le
    chaitinOmega_universalPrefix_lt_one n).2
  have hpow : (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ q.length :=
    pow_le_pow_of_le_one (by positivity) (by norm_num) hlen
  have hdiff : (2 : ℝ)⁻¹ ^ q.length < (2 : ℝ)⁻¹ ^ n := by linarith
  exact (not_le_of_gt hdiff) hpow

/-- Returns a binary word absent from `L` (always succeeding because `2 ^ |L| > |L|`). -/
private def firstFresh (L : List (List Bool)) : List Bool :=
  (Cslib.BitString.enumList L.length).foldr (fun s acc => if s ∈ L then acc else s) []

private theorem firstFresh_notMem (L : List (List Bool)) : firstFresh L ∉ L := by
  have hex : ∃ s ∈ Cslib.BitString.enumList L.length, s ∉ L := by
    by_contra! hall
    have hsub : (Cslib.BitString.enumList L.length).toFinset ⊆ L.toFinset := fun s hs =>
      List.mem_toFinset.mpr (hall s (List.mem_toFinset.mp hs))
    have hnodup : (Cslib.BitString.enumList L.length).Nodup :=
      (Cslib.BitString.nodup_enum L.length).map List.ofFn_injective
    have hcard : 2 ^ L.length ≤ L.length := by
      calc 2 ^ L.length
        _ = (Cslib.BitString.enumList L.length).length :=
            (Cslib.BitString.length_enumList L.length).symm
        _ = (Cslib.BitString.enumList L.length).toFinset.card :=
            (List.toFinset_card_of_nodup hnodup).symm
        _ ≤ L.toFinset.card := Finset.card_le_card hsub
        _ ≤ L.length := List.toFinset_card_le L
    exact (Nat.lt_two_pow_self (n := L.length)).not_ge hcard
  have hfold : ∀ E : List (List Bool), (∃ s ∈ E, s ∉ L) →
      E.foldr (fun s acc => if s ∈ L then acc else s) [] ∉ L := by
    intro E hE
    induction E with
    | nil => simp at hE
    | cons a rest ih =>
      simp only [List.foldr_cons]
      by_cases ha : a ∈ L
      · simp only [ha, ↓reduceIte]
        apply ih
        obtain ⟨s, hs, hsnot⟩ := hE
        rcases List.mem_cons.mp hs with rfl | hs'
        · exact absurd ha hsnot
        · exact ⟨s, hs', hsnot⟩
      · simp [ha]
  unfold firstFresh
  exact hfold _ hex

private theorem primrec_firstFresh : Primrec firstFresh := by
  have hmem : PrimrecRel fun (L : List (List Bool)) (s : List Bool) => s ∈ L :=
    (PrimrecRel.exists_mem_list Primrec.eq).of_eq fun _ _ => by simp
  have hh : Primrec₂ fun (L : List (List Bool)) (sa : List Bool × List Bool) =>
      if sa.1 ∈ L then sa.2 else sa.1 :=
    Primrec₂.mk <| Primrec.ite
      (hmem.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd)
  exact (Primrec.list_foldr (primrec_enumList.comp Primrec.list_length)
    (Primrec.const []) hh).of_eq fun _ => rfl

/-- **Incompressibility of initial segments of Chaitin's `Ω`**: every `n`-bit prefix `Ω ↾ n` has
prefix-free Kolmogorov complexity at least `n - c`. -/
theorem exists_le_complexity_realPrefix_chaitinOmega :
    ∃ c : ℕ, ∀ n : ℕ,
      n ≤ universalPrefixBits.complexity (realPrefix (chaitinOmega universalPrefix) n) + c := by
  obtain ⟨fU, hfU, hfU_spec⟩ := isPartrec_universalPrefix
  let waitStage : List Bool → ℕ → Option ℕ := fun w t =>
    let M := max w.length (universalPrefixMaxLen t)
    if Cslib.BitString.binaryValue w * 2 ^ (M - w.length) <
        universalPrefixScaled t * 2 ^ (M - universalPrefixMaxLen t) then
      some t
    else Option.none
  have hwait_prim : Primrec₂ waitStage := by
    have hM : Primrec₂ fun (w : List Bool) (t : ℕ) => max w.length (universalPrefixMaxLen t) :=
      Primrec₂.mk <| Primrec.nat_max.comp (Primrec.list_length.comp Primrec.fst)
        (primrec_universalPrefixMaxLen.comp Primrec.snd)
    have hlhs : Primrec₂ fun (w : List Bool) (t : ℕ) =>
        Cslib.BitString.binaryValue w *
          2 ^ (max w.length (universalPrefixMaxLen t) - w.length) :=
      Primrec₂.mk <| Primrec.nat_mul.comp (primrec_binaryValue.comp Primrec.fst)
        (primrec_two_pow.comp
          (Primrec.nat_sub.comp (hM.comp Primrec.fst Primrec.snd)
            (Primrec.list_length.comp Primrec.fst)))
    have hrhs : Primrec₂ fun (w : List Bool) (t : ℕ) =>
        universalPrefixScaled t *
          2 ^ (max w.length (universalPrefixMaxLen t) - universalPrefixMaxLen t) :=
      Primrec₂.mk <| Primrec.nat_mul.comp (primrec_universalPrefixScaled.comp Primrec.snd)
        (primrec_two_pow.comp
          (Primrec.nat_sub.comp (hM.comp Primrec.fst Primrec.snd)
            (primrec_universalPrefixMaxLen.comp Primrec.snd)))
    exact Primrec₂.mk <| (Primrec.ite (PrimrecRel.comp Primrec.nat_lt hlhs hrhs)
      (Primrec.option_some.comp Primrec.snd) (Primrec.const Option.none)).of_eq fun _ => rfl
  have hwait_iff : ∀ w t, waitStage w t = some t ↔
      (Cslib.BitString.binaryValue w : ℝ) * (2 : ℝ)⁻¹ ^ w.length <
        (universalPrefixApprox t : ℝ) := by
    intro w t
    set M := max w.length (universalPrefixMaxLen t)
    have hM1 : w.length ≤ M := le_max_left _ _
    have hM2 : universalPrefixMaxLen t ≤ M := le_max_right _ _
    have hpos : (0 : ℝ) < (2 : ℝ) ^ M := by positivity
    have h1 : (Cslib.BitString.binaryValue w : ℝ) * (2 : ℝ)⁻¹ ^ w.length * (2 : ℝ) ^ M =
        ((Cslib.BitString.binaryValue w * 2 ^ (M - w.length) : ℕ) : ℝ) := by
      have hMw : w.length + (M - w.length) = M := Nat.add_sub_of_le hM1
      calc (Cslib.BitString.binaryValue w : ℝ) * (2 : ℝ)⁻¹ ^ w.length * (2 : ℝ) ^ M
        _ = (Cslib.BitString.binaryValue w : ℝ) *
              ((2 : ℝ)⁻¹ ^ w.length * ((2 : ℝ) ^ w.length * (2 : ℝ) ^ (M - w.length))) := by
            rw [← pow_add, hMw, mul_assoc]
        _ = (Cslib.BitString.binaryValue w : ℝ) *
              (((2 : ℝ)⁻¹ ^ w.length * (2 : ℝ) ^ w.length) * (2 : ℝ) ^ (M - w.length)) := by ring
        _ = ((Cslib.BitString.binaryValue w * 2 ^ (M - w.length) : ℕ) : ℝ) := by
            rw [inv_pow, inv_mul_cancel₀ (by positivity), one_mul]
            push_cast
            rfl
    have h2 : (universalPrefixApprox t : ℝ) * (2 : ℝ) ^ M =
        ((universalPrefixScaled t * 2 ^ (M - universalPrefixMaxLen t) : ℕ) : ℝ) := by
      have hMt : universalPrefixMaxLen t + (M - universalPrefixMaxLen t) = M :=
        Nat.add_sub_of_le hM2
      calc (universalPrefixApprox t : ℝ) * (2 : ℝ) ^ M
        _ = ((universalPrefixApprox t : ℝ) * (2 : ℝ) ^ universalPrefixMaxLen t) *
              (2 : ℝ) ^ (M - universalPrefixMaxLen t) := by
            rw [mul_assoc, ← pow_add, hMt]
        _ = ((universalPrefixScaled t * 2 ^ (M - universalPrefixMaxLen t) : ℕ) : ℝ) := by
            rw [universalPrefixScaled_cast t]
            push_cast
            rfl
    have heq : (Cslib.BitString.binaryValue w * 2 ^ (M - w.length) <
        universalPrefixScaled t * 2 ^ (M - universalPrefixMaxLen t)) ↔
        (Cslib.BitString.binaryValue w : ℝ) * (2 : ℝ)⁻¹ ^ w.length <
          (universalPrefixApprox t : ℝ) := by
      rw [← @Nat.cast_lt ℝ, ← h1, ← h2, mul_lt_mul_iff_left₀ hpos]
    simp only [waitStage]
    split_ifs with hlt
    · simp only [true_iff]
      exact heq.mp hlt
    · simp only [false_iff, not_lt]
      exact not_lt.mp (heq.not.mp hlt)
  let produced : ℕ → List (List Bool) := fun t =>
    (universalPrefixTable t).map fun px => (decode (α := List Bool) px.2).getD []
  have hproduced_prim : Primrec produced := by
    have hmap : Primrec₂ fun (_ : ℕ) (px : List Bool × ℕ) =>
        (decode (α := List Bool) px.2).getD [] :=
      Primrec₂.mk <|
        Primrec.option_getD_default.comp (Primrec.decode.comp (Primrec.snd.comp Primrec.snd))
    exact (Primrec.list_map primrec_universalPrefixTable hmap).of_eq fun _ => rfl
  let omegaDiag : List Bool →. List Bool := fun q =>
    (fU q).bind fun m =>
      let w := (decode (α := List Bool) m).getD []
      (Nat.rfindOpt (waitStage w)).map fun t => firstFresh (produced t)
  have hdiag_part : Partrec omegaDiag := by
    have hw : Computable fun m : ℕ => (decode (α := List Bool) m).getD [] :=
      Primrec.option_getD_default.to_comp.comp Computable.decode
    have hrfind : Partrec fun m : ℕ =>
        Nat.rfindOpt (waitStage ((decode (α := List Bool) m).getD [])) :=
      (Partrec.rfindOpt hwait_prim.to_comp).comp hw
    have hmap : Partrec fun m : ℕ =>
        (Nat.rfindOpt (waitStage ((decode (α := List Bool) m).getD []))).map
          fun t => firstFresh (produced t) :=
      hrfind.map ((primrec_firstFresh.comp hproduced_prim).to_comp.comp Computable.snd)
    exact hfU.bind (hmap.comp Computable.snd)
  have hdiag_pf : InformationTheory.IsPrefixFree {q | (omegaDiag q).Dom} := by
    refine isPrefixFree_universalPrefix.anti fun q hq => ?_
    obtain ⟨_, hm⟩ := Part.dom_iff_mem.mp hq
    obtain ⟨m, hm', _⟩ := Part.mem_bind_iff.mp hm
    exact ⟨m, (hfU_spec q m).mpr hm'⟩
  obtain ⟨c, hc⟩ := minorizesPrefixPartrec_universalPrefixBits omegaDiag hdiag_part hdiag_pf
  refine ⟨c, fun n => ?_⟩
  let w := realPrefix (chaitinOmega universalPrefix) n
  obtain ⟨p, hp_prod, hp_len⟩ :=
    exists_length_eq_ecomplexity (ecomplexity_universalPrefixBits_ne_top w)
  rw [← natCast_complexity_universalPrefixBits, Nat.cast_inj] at hp_len
  obtain ⟨m, hm_prod, hm_dec⟩ := map_produces_iff.mp hp_prod
  have hfUm : m ∈ fU p := (hfU_spec p m).mp hm_prod
  have hlt_omega := binaryValue_realPrefix_chaitinOmega_mul_lt n
  have hex_t : ∃ t : ℕ, (Cslib.BitString.binaryValue w : ℝ) * (2 : ℝ)⁻¹ ^ n <
      (universalPrefixApprox t : ℝ) := by
    have hε : 0 < chaitinOmega universalPrefix -
        (Cslib.BitString.binaryValue w : ℝ) * (2 : ℝ)⁻¹ ^ n := sub_pos.mpr hlt_omega
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp tendsto_universalPrefixApprox _ hε
    refine ⟨N, ?_⟩
    have hdist := abs_sub_lt_iff.mp ((Real.dist_eq _ _).symm ▸ hN N le_rfl)
    linarith
  obtain ⟨t₀, ht₀⟩ := hex_t
  have hwait0 : waitStage ((decode (α := List Bool) m).getD []) t₀ = some t₀ := by
    rw [hm_dec]
    exact (hwait_iff w t₀).mpr (by simpa [w] using ht₀)
  obtain ⟨t, ht⟩ := Part.dom_iff_mem.mp (Nat.rfindOpt_dom.mpr ⟨t₀, t₀, hwait0⟩)
  obtain ⟨t', ht'⟩ := Nat.rfindOpt_spec ht
  have hteq : t = t' := by
    simp only [waitStage] at ht'
    split_ifs at ht'
    · exact (Option.some.inj ht').symm
    · simp at ht'
  subst hteq
  have ht_lt : (Cslib.BitString.binaryValue w : ℝ) * (2 : ℝ)⁻¹ ^ n <
      (universalPrefixApprox t : ℝ) := by
    have := (hwait_iff ((decode (α := List Bool) m).getD []) t).mp ht'
    simpa [hm_dec, w] using this
  let z : List Bool := firstFresh (produced t)
  have hz_mem : z ∈ omegaDiag p := Part.mem_bind hfUm (Part.mem_map _ ht)
  have hz_ub : universalPrefixBits.ecomplexity z ≤ p.length + c := hc p z hz_mem
  have hz_lb : n + 1 ≤ universalPrefixBits.complexity z := by
    by_contra! hle_z
    obtain ⟨qz, hqz_prod, hqz_len⟩ :=
      exists_length_eq_ecomplexity (ecomplexity_universalPrefixBits_ne_top z)
    rw [← natCast_complexity_universalPrefixBits, Nat.cast_inj] at hqz_len
    obtain ⟨mz, hmz_prod, hmz_dec⟩ := map_produces_iff.mp hqz_prod
    have hqz_halt : qz ∈ universalPrefix.haltingSet := ⟨mz, hmz_prod⟩
    have hqz_cap := universalPrefixTable_captures_length_le ht_lt hqz_halt (by omega)
    obtain ⟨⟨q', y'⟩, hmem_table, hqeq⟩ := List.mem_map.mp hqz_cap
    dsimp only at hqeq
    subst hqeq
    have hsame : y' = mz :=
      Part.mem_unique ((hfU_spec q' y').mp (mem_universalPrefixTable_produces hmem_table))
        ((hfU_spec q' mz).mp hmz_prod)
    subst hsame
    have hz_in_prod : z ∈ produced t :=
      List.mem_map.mpr ⟨(q', y'), hmem_table, hmz_dec⟩
    exact firstFresh_notMem (produced t) hz_in_prod
  have hz_ub_nat : universalPrefixBits.complexity z ≤ p.length + c := by
    rw [← natCast_complexity_universalPrefixBits] at hz_ub
    exact_mod_cast hz_ub
  dsimp only [w] at hp_len
  omega

end DescriptionMethod

/-! ### Martin-Löf randomness -/

/-- Cylinder set of infinite bit sequences starting with the finite binary word `w`. -/
@[expose] def prefixCylinderList (w : List Bool) : Set (ℕ → Bool) :=
  Cslib.BitString.prefixCylinder (fun i : Fin w.length => w[i])

theorem mem_prefixCylinderList {w : List Bool} {x : ℕ → Bool} :
    x ∈ prefixCylinderList w ↔ ∀ i : Fin w.length, x i = w[i] :=
  Cslib.BitString.mem_prefixCylinder

theorem measurableSet_prefixCylinderList (w : List Bool) : MeasurableSet (prefixCylinderList w) :=
  Cslib.BitString.measurableSet_prefixCylinder _

theorem coinFlips_prefixCylinderList (w : List Bool) :
    Cslib.BitString.coinFlips (prefixCylinderList w) = (2 ^ w.length)⁻¹ :=
  Cslib.BitString.coinFlips_prefixCylinder _

theorem prefixCylinderList_subset_of_isPrefix {u v : List Bool} (huv : u <+: v) :
    prefixCylinderList v ⊆ prefixCylinderList u := by
  intro x hx
  rw [mem_prefixCylinderList] at hx ⊢
  intro i
  have hi : (i : ℕ) < v.length := i.2.trans_le huv.length_le
  rw [hx ⟨i.1, hi⟩]
  exact (List.IsPrefix.getElem huv i.2).symm

theorem disjoint_prefixCylinderList_of_prefixDisjoint {u v : List Bool}
    (huv : PrefixDisjoint u v) : Disjoint (prefixCylinderList u) (prefixCylinderList v) := by
  refine Set.disjoint_left.mpr fun x hxu hxv => ?_
  rw [mem_prefixCylinderList] at hxu hxv
  rcases le_total u.length v.length with hle | hle
  · apply huv.1
    rw [List.prefix_iff_eq_take]
    refine List.ext_getElem (by simp [hle]) fun i hi1 hi2 => ?_
    have hi_u : i < u.length := by simpa using hi1
    have hi_v : i < v.length := hi_u.trans_le hle
    have hxu' := hxu ⟨i, hi_u⟩
    have hxv' := hxv ⟨i, hi_v⟩
    simp only [List.getElem_take]
    exact hxu'.symm.trans hxv'
  · apply huv.2
    rw [List.prefix_iff_eq_take]
    refine List.ext_getElem (by simp [hle]) fun i hi1 hi2 => ?_
    have hi_v : i < v.length := by simpa using hi1
    have hi_u : i < u.length := hi_v.trans_le hle
    have hxu' := hxu ⟨i, hi_u⟩
    have hxv' := hxv ⟨i, hi_v⟩
    simp only [List.getElem_take]
    exact hxv'.symm.trans hxu'

/-- A **Martin-Löf randomness test**: a computably enumerable family of prefix covers
`cover m` whose union has `coinFlips`-measure at most `(2 : ℝ≥0∞)⁻¹ ^ m`. -/
structure MartinLofTest where
  /-- Level-`m` set of binary prefixes covering the test at error bound `2⁻¹ ^ m`. -/
  cover : ℕ → Set (List Bool)
  /-- Uniform computable enumerability of `(m, w) ↦ w ∈ cover m`. -/
  re : REPred fun p : ℕ × List Bool => p.2 ∈ cover p.1
  /-- Fair-coin measure bound `coinFlips (⋃ w ∈ cover m, prefixCylinderList w) ≤ 2⁻¹ ^ m`. -/
  measure_le : ∀ m : ℕ,
    Cslib.BitString.coinFlips (⋃ w ∈ cover m, prefixCylinderList w) ≤ (2 : ℝ≥0∞)⁻¹ ^ m

/-- An infinite bit sequence is **Martin-Löf random** when it passes every `MartinLofTest`. -/
@[expose] def IsMartinLofRandom (x : ℕ → Bool) : Prop :=
  ∀ T : MartinLofTest, ∃ m : ℕ, x ∉ ⋃ w ∈ T.cover m, prefixCylinderList w

/-- No computable infinite bit sequence is Martin-Löf random. -/
theorem not_isMartinLofRandom_of_computable {x : ℕ → Bool} (hx : Computable x) :
    ¬ IsMartinLofRandom x := by
  let pref : ℕ → List Bool := fun m => List.ofFn fun i : Fin m => x i
  have hpref : Computable pref := by
    have hstep : Computable₂ fun (_ : ℕ) (p : ℕ × List Bool) => p.2 ++ [x p.1] :=
      Primrec.list_append.to_comp.comp (Computable.snd.comp Computable.snd)
        (Primrec.list_cons.to_comp.comp (hx.comp (Computable.fst.comp Computable.snd))
          (Computable.const []))
    refine (Computable.nat_rec Computable.id (Computable.const []) hstep).of_eq fun m => ?_
    have hrec : ∀ n : ℕ, Nat.rec [] (fun y IH => IH ++ [x y]) n = pref n := by
      intro n
      induction n with
      | zero => simp [pref]
      | succ n ih =>
        change Nat.rec [] (fun y IH => IH ++ [x y]) n ++ [x n] = pref (n + 1)
        rw [ih]
        refine List.ext_getElem (by simp [pref]) fun i hi1 hi2 => ?_
        have hin : i < n + 1 := by simpa [pref] using hi2
        rcases Nat.lt_succ_iff_lt_or_eq.mp hin with hlt | rfl
        · simp only [pref, List.getElem_append_left, List.length_ofFn, List.getElem_ofFn, hlt]
        · simp only [pref, List.getElem_append_right, List.length_ofFn, le_rfl, Nat.sub_self,
            List.getElem_singleton, List.getElem_ofFn]
    exact hrec m
  let T : MartinLofTest :=
    { cover := fun m => {pref m}
      re := by
        have hpred : ComputablePred fun p : ℕ × List Bool => p.2 = pref p.1 :=
          (Primrec.eq.decide.to_comp.comp Computable.snd
            (hpref.comp Computable.fst)).computablePred
        exact hpred.to_re
      measure_le := fun m => by
        have hlen : (pref m).length = m := by simp [pref]
        have hu : (⋃ w ∈ ({pref m} : Set (List Bool)), prefixCylinderList w) =
            prefixCylinderList (pref m) := by simp
        rw [hu, coinFlips_prefixCylinderList, hlen, ENNReal.inv_pow] }
  intro hrand
  obtain ⟨m, hm⟩ := hrand T
  apply hm
  refine Set.mem_iUnion₂.mpr ⟨pref m, rfl, mem_prefixCylinderList.mpr fun i => ?_⟩
  simp [pref]

/-! #### Online disjointification for Martin-Löf randomness -/

/-- Expands a new cover word `w` down to `max |w| (maxLen seen)` and filters out extensions of
previously seen prefixes. -/
private def mlExpand (w : List Bool) (seen : List (List Bool)) : List (List Bool) :=
  let M := seen.foldr (fun u m => max u.length m) 0
  let L := max w.length M
  ((Cslib.BitString.enumList (L - w.length)).map (w ++ ·)).foldr
    (fun v acc => if seen.any (fun u => decide (u <+: v)) then acc else v :: acc) []

private theorem primrec₂_mlExpand : Primrec₂ mlExpand := by
  have hh_max : Primrec₂ fun (_ : List (List Bool)) (bs : List Bool × ℕ) =>
      max bs.1.length bs.2 :=
    Primrec₂.mk <| Primrec.nat_max.comp
      (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  have hM : Primrec fun seen : List (List Bool) => seen.foldr (fun u m => max u.length m) 0 :=
    (Primrec.list_foldr Primrec.id (Primrec.const 0) hh_max).of_eq fun _ => rfl
  have hL : Primrec₂ fun (w : List Bool) (seen : List (List Bool)) =>
      max w.length (seen.foldr (fun u m => max u.length m) 0) :=
    Primrec₂.mk <| Primrec.nat_max.comp
      (Primrec.list_length.comp Primrec.fst) (hM.comp Primrec.snd)
  have hext : Primrec₂ fun (w : List Bool) (seen : List (List Bool)) =>
      (Cslib.BitString.enumList
        (max w.length (seen.foldr (fun u m => max u.length m) 0) - w.length)).map (w ++ ·) :=
    Primrec₂.mk <| Primrec.list_map
      (primrec_enumList.comp (Primrec.nat_sub.comp (hL.comp Primrec.fst Primrec.snd)
        (Primrec.list_length.comp Primrec.fst)))
      (Primrec₂.mk <| Primrec.list_append.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
  have hpref_rel : PrimrecRel fun (seen : List (List Bool)) (v : List Bool) =>
      ∃ u ∈ seen, u <+: v :=
    PrimrecRel.exists_mem_list Primrec.list_isPrefix
  have hfold : Primrec₂ fun (w : List Bool) (seen : List (List Bool)) =>
      ((Cslib.BitString.enumList
          (max w.length (seen.foldr (fun u m => max u.length m) 0) - w.length)).map
        (w ++ ·)).foldr
        (fun v acc => if seen.any (fun u => decide (u <+: v)) then acc else v :: acc) [] := by
    have hh : Primrec₂ fun (ws : List Bool × List (List Bool))
        (va : List Bool × List (List Bool)) =>
        if ws.2.any (fun u => decide (u <+: va.1)) then va.2 else va.1 :: va.2 := by
      have hpred : PrimrecPred fun arg :
          (List Bool × List (List Bool)) × (List Bool × List (List Bool)) =>
          ∃ u ∈ arg.1.2, u <+: arg.2.1 :=
        hpref_rel.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
      refine Primrec₂.mk <| (Primrec.ite hpred
        (Primrec.snd.comp Primrec.snd)
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp Primrec.snd))).of_eq fun ⟨⟨w, seen⟩, ⟨v, acc⟩⟩ => ?_
      have hiff : (seen.any fun u => decide (u <+: v)) = true ↔ ∃ u ∈ seen, u <+: v := by
        simp [List.any_eq_true]
      by_cases h : ∃ u ∈ seen, u <+: v
      · simp [h, hiff.mpr h]
      · have hf : (seen.any fun u => decide (u <+: v)) = false :=
          Bool.eq_false_iff.mpr (mt hiff.mp h)
        simp [h, hf]
    exact Primrec₂.mk <| Primrec.list_foldr (hext.comp Primrec.fst Primrec.snd)
      (Primrec.const []) hh
  exact hfold.of_eq fun _ _ => rfl

private theorem foldr_filter_not_mem_prefix {E : List (List Bool)} {seen : List (List Bool)} :
    ∀ v ∈ E.foldr (fun v acc => if seen.any (fun u => decide (u <+: v)) then acc else v :: acc) [],
      v ∈ E ∧ ∀ u ∈ seen, ¬ (u <+: v) := by
  intro v hv
  induction E with
  | nil => simp at hv
  | cons a rest ih =>
    simp only [List.foldr_cons] at hv
    by_cases ha : seen.any (fun u => decide (u <+: a)) = true
    · simp only [ha, ↓reduceIte] at hv
      have ⟨h1, h2⟩ := ih hv
      exact ⟨List.mem_cons_of_mem a h1, h2⟩
    · have haf : seen.any (fun u => decide (u <+: a)) = false := Bool.eq_false_iff.mpr ha
      simp only [haf, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at hv
      rcases hv with rfl | hv'
      · refine ⟨List.mem_cons_self, fun u hu huv => ?_⟩
        apply ha
        exact List.any_eq_true.mpr ⟨u, hu, decide_eq_true huv⟩
      · have ⟨h1, h2⟩ := ih hv'
        exact ⟨List.mem_cons_of_mem a h1, h2⟩

private theorem mem_foldr_filter_not_mem_prefix {E seen : List (List Bool)} {v : List Bool}
    (hvE : v ∈ E) (hvnot : ∀ u ∈ seen, ¬ (u <+: v)) :
    v ∈ E.foldr (fun s acc =>
      if seen.any (fun u => decide (u <+: s)) then acc else s :: acc) [] := by
  induction E with
  | nil => simp at hvE
  | cons a rest ih =>
    simp only [List.foldr_cons]
    by_cases ha : seen.any (fun u => decide (u <+: a)) = true
    · simp only [ha, ↓reduceIte]
      rcases List.mem_cons.mp hvE with rfl | hv'
      · obtain ⟨u, hu, huv⟩ := List.any_eq_true.mp ha
        exact absurd (decide_eq_true_eq.mp huv) (hvnot u hu)
      · exact ih hv'
    · have haf : seen.any (fun u => decide (u <+: a)) = false := Bool.eq_false_iff.mpr ha
      simp only [haf, Bool.false_eq_true, ↓reduceIte, List.mem_cons]
      rcases List.mem_cons.mp hvE with rfl | hv'
      · exact Or.inl rfl
      · exact Or.inr (ih hv')

private theorem nodup_foldr_filter {E : List (List Bool)} (hE : E.Nodup)
    (seen : List (List Bool)) :
    (E.foldr (fun s acc =>
      if seen.any (fun u => decide (u <+: s)) then acc else s :: acc) []).Nodup := by
  induction E with
  | nil => simp
  | cons a rest ih =>
    rcases List.nodup_cons.mp hE with ⟨ha_not, hrest⟩
    simp only [List.foldr_cons]
    split_ifs with h
    · exact ih hrest
    · refine List.nodup_cons.mpr ⟨fun hmem => ha_not ?_, ih hrest⟩
      exact (foldr_filter_not_mem_prefix a hmem).1

/-- Stage enumeration for level `2 * k + 2` of a code `e`. -/
private def levelStageWord (e : Code) (k j : ℕ) : Option (List Bool) :=
  (decode (α := List Bool × ℕ) j).bind fun wf =>
    (Code.evaln wf.2 e (encode (2 * k + 2, wf.1))).map fun _ => wf.1

private theorem primrec₂_levelStageWord (e : Code) : Primrec₂ (levelStageWord e) := by
  have hev : Primrec fun arg : ℕ × (List Bool × ℕ) =>
      Code.evaln arg.2.2 e (encode (2 * arg.1 + 2, arg.2.1)) :=
    Code.primrec_evaln.comp <| Primrec.pair
      (Primrec.pair (Primrec.snd.comp Primrec.snd) (Primrec.const e))
      (Primrec.encode.comp <| Primrec.pair
        (Primrec.nat_add.comp (Primrec.nat_double.comp Primrec.fst) (Primrec.const 2))
        (Primrec.fst.comp Primrec.snd))
  have hmap : Primrec₂ fun (k : ℕ) (wf : List Bool × ℕ) =>
      (Code.evaln wf.2 e (encode (2 * k + 2, wf.1))).map fun _ => wf.1 :=
    Primrec₂.mk <| Primrec.option_map hev (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).to₂
  exact Primrec₂.mk <| (Primrec.option_bind (Primrec.decode.comp Primrec.snd)
    (hmap.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).of_eq fun _ => rfl

/-- Disjointifying trace at level `k` across dovetailing steps `j`, producing
`(seen, newlyEmitted)`. -/
private def mlLevelTrace (e : Code) (k : ℕ) : ℕ → List (List Bool) × List (List Bool)
  | 0 => ([], [])
  | j + 1 =>
    let seen := (mlLevelTrace e k j).1
    match levelStageWord e k j with
    | Option.none => (seen, [])
    | some w =>
      let new := mlExpand w seen
      (seen ++ new, new)

private theorem primrec₂_mlLevelTrace (e : Code) : Primrec₂ (mlLevelTrace e) := by
  have hh : Primrec₂ fun (k : ℕ) (p : ℕ × (List (List Bool) × List (List Bool))) =>
      match levelStageWord e k p.1 with
      | Option.none => (p.2.1, [])
      | some w => (p.2.1 ++ mlExpand w p.2.1, mlExpand w p.2.1) := by
    have hsome : Primrec₂ fun (kp : ℕ × (ℕ × (List (List Bool) × List (List Bool))))
        (w : List Bool) => (kp.2.2.1 ++ mlExpand w kp.2.2.1, mlExpand w kp.2.2.1) := by
      have hseen : Primrec fun arg :
          (ℕ × (ℕ × (List (List Bool) × List (List Bool)))) × List Bool => arg.1.2.2.1 :=
        Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      exact Primrec₂.mk <| Primrec.pair
        (Primrec.list_append.comp hseen (primrec₂_mlExpand.comp Primrec.snd hseen))
        (primrec₂_mlExpand.comp Primrec.snd hseen)
    refine Primrec₂.mk <| (Primrec.option_casesOn
      ((primrec₂_levelStageWord e).comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const []))
      hsome).of_eq fun x => by cases levelStageWord e x.1 x.2.1 <;> rfl
  refine (Primrec.nat_rec (Primrec.const ([], [])) hh).of_eq fun k j => ?_
  let step (y : ℕ) (IH : List (List Bool) × List (List Bool)) :
      List (List Bool) × List (List Bool) :=
    match levelStageWord e k y with
    | Option.none => (IH.1, [])
    | some w => (IH.1 ++ mlExpand w IH.1, mlExpand w IH.1)
  change Nat.rec ([], []) step j = mlLevelTrace e k j
  induction j with
  | zero => rfl
  | succ j ih =>
    change step j (Nat.rec ([], []) step j) = _
    rw [ih]
    dsimp only [step, mlLevelTrace]

/-- Online Kraft–Chaitin request stream associated with a code `e` for a Martin-Löf test. -/
private def mlReq (e : Code) (i : ℕ) : Option (ℕ × List Bool) :=
  (decode (α := (ℕ × ℕ) × ℕ) i).bind fun kji =>
    ((mlLevelTrace e kji.1.1 (kji.1.2 + 1)).2[kji.2]?).map fun v => (v.length - kji.1.1, v)

private theorem primrec_mlReq (e : Code) : Primrec (mlReq e) := by
  have hget : Primrec fun kji : (ℕ × ℕ) × ℕ =>
      (mlLevelTrace e kji.1.1 (kji.1.2 + 1)).2[kji.2]? :=
    Primrec.list_getElem?.comp
      (Primrec.snd.comp ((primrec₂_mlLevelTrace e).comp
        (Primrec.fst.comp Primrec.fst) (Primrec.succ.comp (Primrec.snd.comp Primrec.fst))))
      Primrec.snd
  have hmap : Primrec fun kji : (ℕ × ℕ) × ℕ =>
      ((mlLevelTrace e kji.1.1 (kji.1.2 + 1)).2[kji.2]?).map fun v => (v.length - kji.1.1, v) :=
    Primrec.option_map hget <| Primrec₂.mk <| Primrec.pair
      (Primrec.nat_sub.comp (Primrec.list_length.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      Primrec.snd
  exact (Primrec.option_bind Primrec.decode (hmap.comp Primrec.snd).to₂).of_eq fun _ => rfl

private theorem mlExpand_spec (w : List Bool) (seen : List (List Bool)) :
    let L := max w.length (seen.foldr (fun u m => max u.length m) 0)
    (∀ v ∈ mlExpand w seen, w <+: v ∧ v.length = L ∧ ∀ u ∈ seen, ¬ (u <+: v)) ∧
      (mlExpand w seen).Pairwise PrefixDisjoint ∧
      (∀ u ∈ seen, ∀ v ∈ mlExpand w seen, PrefixDisjoint u v) := by
  dsimp only [mlExpand]
  set M := seen.foldr (fun u m => max u.length m) 0
  set L := max w.length M
  have hprop : ∀ v ∈ mlExpand w seen, w <+: v ∧ v.length = L ∧ ∀ u ∈ seen, ¬ (u <+: v) := by
    intro v hv
    have ⟨hvE, hvnot⟩ := foldr_filter_not_mem_prefix v hv
    obtain ⟨t, htE, rfl⟩ := List.mem_map.mp hvE
    have htlen := Cslib.BitString.length_of_mem_enumList htE
    refine ⟨List.prefix_append w t, ?_, hvnot⟩
    rw [List.length_append, htlen]
    have hwL : w.length ≤ L := le_max_left _ _
    omega
  have hnodup : (mlExpand w seen).Nodup := by
    refine nodup_foldr_filter ?_ seen
    exact ((Cslib.BitString.nodup_enum (L - w.length)).map List.ofFn_injective).map
      (List.append_right_injective w)
  have hpair : (mlExpand w seen).Pairwise PrefixDisjoint := by
    have hpair_eq : ∀ L0 : List (List Bool), L0.Nodup → (∀ a ∈ L0, a.length = L) →
        L0.Pairwise PrefixDisjoint := by
      intro L0 hnd hlen
      induction L0 with
      | nil => simp
      | cons a t iht =>
        rcases List.nodup_cons.mp hnd with ⟨hant, htnd⟩
        refine List.pairwise_cons.mpr ⟨fun b hbt => ?_,
          iht htnd fun b hbt => hlen b (List.mem_cons_of_mem a hbt)⟩
        have hne : a ≠ b := fun heq => hant (heq ▸ hbt)
        have hal := hlen a List.mem_cons_self
        have hbl := hlen b (List.mem_cons_of_mem a hbt)
        exact ⟨fun h => hne (h.eq_of_length (hal.trans hbl.symm)),
          fun h => hne (h.eq_of_length (hbl.trans hal.symm)).symm⟩
    exact hpair_eq (mlExpand w seen) hnodup fun v hv => (hprop v hv).2.1
  have hcross : ∀ u ∈ seen, ∀ v ∈ mlExpand w seen, PrefixDisjoint u v := by
    intro u hu v hv
    have ⟨_, hvlen, hvnot⟩ := hprop v hv
    refine ⟨hvnot u hu, fun hvu => ?_⟩
    have hle : v.length ≤ u.length := hvu.length_le
    have huM := length_le_foldr_max seen hu
    have hML : M ≤ L := le_max_right _ _
    have huv_len : v.length = u.length := by omega
    exact hvnot u hu (by rw [hvu.eq_of_length huv_len])
  exact ⟨hprop, hpair, hcross⟩

private theorem mlLevelTrace_pairwise_and_dom (e : Code) (k j : ℕ) :
    (mlLevelTrace e k j).1.Pairwise PrefixDisjoint ∧
      ∀ v ∈ (mlLevelTrace e k j).1, ∃ w, (e.eval (encode (2 * k + 2, w))).Dom ∧ w <+: v := by
  induction j with
  | zero => simp [mlLevelTrace]
  | succ j ih =>
    obtain ⟨hpair, hdom⟩ := ih
    simp only [mlLevelTrace]
    cases hst : levelStageWord e k j with
    | none => exact ⟨hpair, hdom⟩
    | some w =>
      have hw_dom : (e.eval (encode (2 * k + 2, w))).Dom := by
        simp only [levelStageWord, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hst
        obtain ⟨⟨w', f⟩, -, ⟨_, hf, rfl⟩⟩ := hst
        exact Part.dom_iff_mem.mpr ⟨_, Code.evaln_sound hf⟩
      obtain ⟨hprop, hnew_pair, hcross⟩ := mlExpand_spec w (mlLevelTrace e k j).1
      refine ⟨List.pairwise_append.mpr ⟨hpair, hnew_pair, hcross⟩, fun v hv => ?_⟩
      rcases List.mem_append.mp hv with hv_seen | hv_new
      · exact hdom v hv_seen
      · exact ⟨w, hw_dom, (hprop v hv_new).1⟩

private theorem mlLevelTrace_covers (e : Code) (x : ℕ → Bool) (k j : ℕ) :
    ∀ i < j, ∀ w, levelStageWord e k i = some w → x ∈ prefixCylinderList w →
      ∃ u ∈ (mlLevelTrace e k j).1, x ∈ prefixCylinderList u := by
  induction j with
  | zero => intro i hi; simp at hi
  | succ j ih =>
    intro i hi w' hiw' hx
    simp only [mlLevelTrace]
    cases hst : levelStageWord e k j with
    | none =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · exact ih i hlt w' hiw' hx
      · simp [hst] at hiw'
    | some w =>
      set seen := (mlLevelTrace e k j).1
      set new := mlExpand w seen
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · obtain ⟨u, hu_seen, hxu⟩ := ih i hlt w' hiw' hx
        exact ⟨u, List.mem_append_left _ hu_seen, hxu⟩
      · rw [hst, Option.some.injEq] at hiw'
        subst hiw'
        by_cases hex_seen : ∃ u ∈ seen, x ∈ prefixCylinderList u
        · obtain ⟨u, hu_seen, hxu⟩ := hex_seen
          exact ⟨u, List.mem_append_left _ hu_seen, hxu⟩
        · let M := seen.foldr (fun u m => max u.length m) 0
          let L := max w.length M
          let v : List Bool := List.ofFn fun idx : Fin L => x idx
          have hv_len : v.length = L := by simp [v]
          have hw_le_L : w.length ≤ L := le_max_left _ _
          have hx_fn := mem_prefixCylinderList.mp hx
          have hwv : w <+: v := by
            rw [List.prefix_iff_eq_take]
            refine List.ext_getElem (by simp [hv_len, hw_le_L]) fun t ht1 ht2 => ?_
            have htw : t < w.length := by simpa [hv_len, hw_le_L] using ht1
            simp only [v, List.getElem_take, List.getElem_ofFn]
            exact (hx_fn ⟨t, htw⟩).symm
          rcases hwv with ⟨suf, hsuf⟩
          have hsuf_len : suf.length = L - w.length := by
            have := congrArg List.length hsuf
            rw [List.length_append, hv_len] at this
            omega
          have hvE : v ∈ (Cslib.BitString.enumList (L - w.length)).map (w ++ ·) :=
            List.mem_map.mpr ⟨suf, Cslib.BitString.mem_enumList.mpr hsuf_len, hsuf⟩
          have hv_mem : x ∈ prefixCylinderList v :=
            mem_prefixCylinderList.mpr fun idx => by simp [v]
          have hv_not : ∀ u ∈ seen, ¬ (u <+: v) := fun u hu huv =>
            hex_seen ⟨u, hu, prefixCylinderList_subset_of_isPrefix huv hv_mem⟩
          have hv_new : v ∈ new := mem_foldr_filter_not_mem_prefix hvE hv_not
          exact ⟨v, List.mem_append_right _ hv_new, hv_mem⟩

private theorem mlLevelTrace_mono (e : Code) (k : ℕ) {m n : ℕ} (hmn : m ≤ n) {v : List Bool}
    (hv : v ∈ (mlLevelTrace e k m).1) : v ∈ (mlLevelTrace e k n).1 := by
  induction hmn with
  | refl => exact hv
  | step _ ih =>
    simp only [mlLevelTrace]
    cases levelStageWord e k _ with
    | none => exact ih
    | some w => exact List.mem_append_left _ ih

private theorem mlLevelTrace_new_mem (e : Code) (k j : ℕ) {v : List Bool}
    (hv : v ∈ (mlLevelTrace e k (j + 1)).2) : v ∈ (mlLevelTrace e k (j + 1)).1 := by
  simp only [mlLevelTrace] at hv ⊢
  cases hst : levelStageWord e k j with
  | none => simp [hst] at hv
  | some w =>
    simp only [hst] at hv ⊢
    exact List.mem_append_right _ hv

private theorem mlLevelTrace_disjoint_prev (e : Code) (k j₁ j₂ : ℕ) {v₁ v₂ : List Bool}
    (hlt : j₁ < j₂) (hv₁ : v₁ ∈ (mlLevelTrace e k (j₁ + 1)).2)
    (hv₂ : v₂ ∈ (mlLevelTrace e k (j₂ + 1)).2) : PrefixDisjoint v₁ v₂ := by
  have hv₁_seen : v₁ ∈ (mlLevelTrace e k j₂).1 :=
    mlLevelTrace_mono e k hlt (mlLevelTrace_new_mem e k j₁ hv₁)
  simp only [mlLevelTrace] at hv₂
  cases hst : levelStageWord e k j₂ with
  | none => simp [hst] at hv₂
  | some w =>
    simp only [hst] at hv₂
    have hpair_j₂ := (mlLevelTrace_pairwise_and_dom e k (j₂ + 1)).1
    simp only [mlLevelTrace, hst] at hpair_j₂
    exact (List.pairwise_append.mp hpair_j₂).2.2 v₁ hv₁_seen v₂ hv₂

private theorem mlLevelTrace_nodup_snd (e : Code) (k j : ℕ) :
    ((mlLevelTrace e k (j + 1)).2).Nodup := by
  simp only [mlLevelTrace]
  cases levelStageWord e k j with
  | none => simp
  | some w =>
    exact nodup_foldr_filter
      (((Cslib.BitString.nodup_enum _).map List.ofFn_injective).map
        (List.append_right_injective w)) _

private theorem mlLevelTrace_level_bound (T : MartinLofTest) {e : Code}
    (he : ∀ p : ℕ × List Bool, p.2 ∈ T.cover p.1 ↔ (e.eval (encode p)).Dom)
    (k J : ℕ) (F : Finset (List Bool)) (hF : ∀ v ∈ F, v ∈ (mlLevelTrace e k J).1) :
    (∀ v ∈ F, 2 * k + 2 ≤ v.length) ∧
      ∑ v ∈ F, (2 : ℝ)⁻¹ ^ v.length ≤ (2 : ℝ)⁻¹ ^ (2 * k + 2) := by
  have htrace := mlLevelTrace_pairwise_and_dom e k J
  have hp_list : ∀ S : List (List Bool), S.Pairwise PrefixDisjoint →
      ∀ v₁ ∈ S, ∀ v₂ ∈ S, v₁ ≠ v₂ → PrefixDisjoint v₁ v₂ := by
    intro S hS v₁ hv₁ v₂ hv₂ hne
    induction S with
    | nil => simp at hv₁
    | cons a t iht =>
      rw [List.pairwise_cons] at hS
      rcases List.mem_cons.mp hv₁ with rfl | h1 <;>
        rcases List.mem_cons.mp hv₂ with rfl | h2
      · exact absurd rfl hne
      · exact hS.1 v₂ h2
      · exact (hS.1 v₁ h1).symm
      · exact iht hS.2 h1 h2
  have hdisj : (F : Set (List Bool)).PairwiseDisjoint prefixCylinderList := fun v₁ hv₁ v₂ hv₂ hne =>
    disjoint_prefixCylinderList_of_prefixDisjoint
      (hp_list (mlLevelTrace e k J).1 htrace.1 v₁ (hF v₁ hv₁) v₂ (hF v₂ hv₂) hne)
  have hsub : (⋃ v ∈ F, prefixCylinderList v) ⊆
      ⋃ w ∈ T.cover (2 * k + 2), prefixCylinderList w := by
    refine Set.iUnion₂_subset fun v hv => ?_
    obtain ⟨w, hw_dom, hwv⟩ := htrace.2 v (hF v hv)
    have hw_cov : w ∈ T.cover (2 * k + 2) := (he (2 * k + 2, w)).mpr hw_dom
    refine (prefixCylinderList_subset_of_isPrefix hwv).trans ?_
    exact fun y hy => Set.mem_iUnion₂.mpr ⟨w, hw_cov, hy⟩
  have hmeas_F : ∑ v ∈ F, (2 : ℝ≥0∞)⁻¹ ^ v.length ≤ (2 : ℝ≥0∞)⁻¹ ^ (2 * k + 2) := by
    calc ∑ v ∈ F, (2 : ℝ≥0∞)⁻¹ ^ v.length
      _ = ∑ v ∈ F, Cslib.BitString.coinFlips (prefixCylinderList v) := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [coinFlips_prefixCylinderList, ENNReal.inv_pow]
      _ = Cslib.BitString.coinFlips (⋃ v ∈ F, prefixCylinderList v) := by
          rw [measure_biUnion_finset hdisj fun v _ => measurableSet_prefixCylinderList v]
      _ ≤ Cslib.BitString.coinFlips (⋃ w ∈ T.cover (2 * k + 2), prefixCylinderList w) :=
          measure_mono hsub
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ (2 * k + 2) := T.measure_le (2 * k + 2)
  have hlen_ge : ∀ v ∈ F, 2 * k + 2 ≤ v.length := by
    intro v hv
    have hsingle : (2 : ℝ≥0∞)⁻¹ ^ v.length ≤ (2 : ℝ≥0∞)⁻¹ ^ (2 * k + 2) :=
      (Finset.single_le_sum (fun _ _ => by positivity) hv).trans hmeas_F
    have hreal_s : (2 : ℝ)⁻¹ ^ v.length ≤ (2 : ℝ)⁻¹ ^ (2 * k + 2) := by
      have hm := ENNReal.toReal_mono (by simp) hsingle
      simpa using hm
    by_contra! hlt
    have hpow_lt : (2 : ℝ)⁻¹ ^ (2 * k + 2) < (2 : ℝ)⁻¹ ^ v.length :=
      pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) hlt
    linarith
  refine ⟨hlen_ge, ?_⟩
  have hreal : (∑ v ∈ F, (2 : ℝ≥0∞)⁻¹ ^ v.length).toReal ≤
      ((2 : ℝ≥0∞)⁻¹ ^ (2 * k + 2)).toReal :=
    ENNReal.toReal_mono (by simp) hmeas_F
  simpa [ENNReal.toReal_sum] using hreal

private theorem mlReq_decode_of_isSome {e : Code} {k i : ℕ}
    (hk : (decode (α := (ℕ × ℕ) × ℕ) i).get!.1.1 = k)
    (hsome : (mlReq e i).isSome) :
    ∃ j idx v,
      decode (α := (ℕ × ℕ) × ℕ) i = some ((k, j), idx) ∧
      (mlLevelTrace e k (j + 1)).2[idx]? = some v ∧
      mlReq e i = some (v.length - k, v) := by
  cases hdec : decode (α := (ℕ × ℕ) × ℕ) i with
  | none =>
    rw [mlReq, hdec] at hsome
    simp at hsome
  | some kji =>
    rcases kji with ⟨⟨k', j⟩, idx⟩
    have hk' : k' = k := by
      rw [hdec] at hk
      exact hk
    subst hk'
    rw [mlReq, hdec] at hsome
    simp only [Option.bind_some, Option.isSome_map] at hsome
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    refine ⟨j, idx, v, rfl, hv, ?_⟩
    dsimp only [mlReq]
    rw [hdec, Option.bind_some, hv]
    rfl

private theorem mlReq_sum_le_one (T : MartinLofTest) {e : Code}
    (he : ∀ p : ℕ × List Bool, p.2 ∈ T.cover p.1 ↔ (e.eval (encode p)).Dom) (n : ℕ) :
    ∑ i ∈ Finset.range n,
      (match mlReq e i with | Option.none => (0 : ℝ) | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ) ≤ 1 := by
  let kOf : ℕ → ℕ := fun i => (decode (α := (ℕ × ℕ) × ℕ) i).get!.1.1
  let jOf : ℕ → ℕ := fun i => (decode (α := (ℕ × ℕ) × ℕ) i).get!.1.2
  let wordOf : ℕ → List Bool := fun i =>
    match mlReq e i with | Option.none => [] | some (_, v) => v
  let K : ℕ := (Finset.range n).sup kOf + 1
  rw [← Finset.sum_fiberwise_of_maps_to (g := kOf) (t := Finset.range K)
    (fun i hi => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup hi)))]
  have hfiber : ∀ k ∈ Finset.range K,
      ∑ i ∈ (Finset.range n).filter (fun i => kOf i = k),
        (match mlReq e i with | Option.none => (0 : ℝ) | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ) ≤
        (2 : ℝ)⁻¹ ^ (k + 2) := by
    intro k _
    let s := ((Finset.range n).filter (fun i => kOf i = k)).filter (fun i => (mlReq e i).isSome)
    have hs_eq :
        ∑ i ∈ (Finset.range n).filter (fun i => kOf i = k),
          (match mlReq e i with | Option.none => (0 : ℝ) | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ) =
          ∑ i ∈ s, (2 : ℝ)⁻¹ ^ ((wordOf i).length - k) := by
      rw [← Finset.sum_filter_add_sum_filter_not _ (fun i => (mlReq e i).isSome)]
      have hzero : ∑ i ∈ ((Finset.range n).filter (fun i => kOf i = k)).filter
          (fun i => ¬ (mlReq e i).isSome),
          (match mlReq e i with | Option.none => (0 : ℝ) | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ) = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        have hnot : ¬ (mlReq e i).isSome := by simpa using (Finset.mem_filter.mp hi).2
        rw [Option.not_isSome_iff_eq_none.mp hnot]
      rw [hzero, add_zero]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hsome := (Finset.mem_filter.mp hi).2
      have hk : kOf i = k := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
      obtain ⟨_, _, v, _, _, hml⟩ := mlReq_decode_of_isSome hk hsome
      simp [wordOf, hml]
    rw [hs_eq]
    let J : ℕ := s.sup jOf + 1
    let F := s.image wordOf
    have hF_sub : ∀ v ∈ F, v ∈ (mlLevelTrace e k J).1 := by
      intro v hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      have hsome := (Finset.mem_filter.mp hi).2
      have hk : kOf i = k := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
      obtain ⟨j', _, v', hdec, hv', hml⟩ := mlReq_decode_of_isSome hk hsome
      have hj_le : j' + 1 ≤ J := Nat.succ_le_succ (by
        have hle := Finset.le_sup (f := jOf) hi
        dsimp only [jOf] at hle
        rw [hdec] at hle
        exact hle)
      have hv'_mem : v' ∈ (mlLevelTrace e k (j' + 1)).2 := List.mem_of_getElem? hv'
      have hwo : wordOf i = v' := by simp [wordOf, hml]
      rw [hwo]
      exact mlLevelTrace_mono e k hj_le (mlLevelTrace_new_mem e k j' hv'_mem)
    have hinj : Set.InjOn wordOf (s : Set ℕ) := by
      intro i₁ hi₁ i₂ hi₂ heqw
      have hs₁ := (Finset.mem_filter.mp (Finset.mem_coe.mp hi₁)).2
      have hs₂ := (Finset.mem_filter.mp (Finset.mem_coe.mp hi₂)).2
      have hk₁ : kOf i₁ = k :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hi₁)).1).2
      have hk₂ : kOf i₂ = k :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hi₂)).1).2
      obtain ⟨j₁, idx₁, v₁, hdec₁, hv₁, hml₁⟩ := mlReq_decode_of_isSome hk₁ hs₁
      obtain ⟨j₂, idx₂, v₂, hdec₂, hv₂, hml₂⟩ := mlReq_decode_of_isSome hk₂ hs₂
      have hv_eq : v₁ = v₂ := by
        simpa [wordOf, hml₁, hml₂] using heqw
      subst hv_eq
      have hj_eq : j₁ = j₂ := by
        by_contra hjne
        rcases lt_or_gt_of_ne hjne with hlt | hgt
        · exact (mlLevelTrace_disjoint_prev e k j₁ j₂ hlt
            (List.mem_of_getElem? hv₁) (List.mem_of_getElem? hv₂)).1 List.prefix_rfl
        · exact (mlLevelTrace_disjoint_prev e k j₂ j₁ hgt
            (List.mem_of_getElem? hv₂) (List.mem_of_getElem? hv₁)).1 List.prefix_rfl
      subst hj_eq
      have hidx_eq : idx₁ = idx₂ := by
        have hval := (List.getElem?_eq_some_iff.mp hv₁).2.trans
          (List.getElem?_eq_some_iff.mp hv₂).2.symm
        exact ((mlLevelTrace_nodup_snd e k j₁).getElem_inj_iff).mp hval
      subst hidx_eq
      have hdec_eq : decode (α := (ℕ × ℕ) × ℕ) i₁ = decode (α := (ℕ × ℕ) × ℕ) i₂ :=
        hdec₁.trans hdec₂.symm
      simp only [decode_prod_val, decode_nat, Option.bind_some, Option.map_some,
        Option.some.injEq] at hdec_eq
      have heq := congrArg (fun t : (ℕ × ℕ) × ℕ => Nat.pair (Nat.pair t.1.1 t.1.2) t.2) hdec_eq
      simpa only [Nat.pair_unpair] using heq
    obtain ⟨hlen_ge, hF_sum⟩ := mlLevelTrace_level_bound T he k J F hF_sub
    calc ∑ i ∈ s, (2 : ℝ)⁻¹ ^ ((wordOf i).length - k)
      _ = ∑ v ∈ F, (2 : ℝ)⁻¹ ^ (v.length - k) :=
          (Finset.sum_image (f := fun v : List Bool => (2 : ℝ)⁻¹ ^ (v.length - k))
            fun i₁ hi₁ i₂ hi₂ => hinj hi₁ hi₂).symm
      _ = ∑ v ∈ F, (2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ v.length := by
          refine Finset.sum_congr rfl fun v hv => ?_
          have hk_le : k ≤ v.length := by have := hlen_ge v hv; omega
          have hv_split : (v.length - k) + k = v.length := Nat.sub_add_cancel hk_le
          have hmul : (2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ v.length = (2 : ℝ)⁻¹ ^ (v.length - k) := by
            conv_lhs => rw [← hv_split]
            rw [pow_add, inv_pow, inv_pow]
            field_simp
          exact hmul.symm
      _ = (2 : ℝ) ^ k * ∑ v ∈ F, (2 : ℝ)⁻¹ ^ v.length := by rw [Finset.mul_sum]
      _ ≤ (2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ (2 * k + 2) := by gcongr
      _ = (2 : ℝ)⁻¹ ^ (k + 2) := by
          have hpow : (2 : ℝ)⁻¹ ^ (2 * k + 2) = (2 : ℝ)⁻¹ ^ k * (2 : ℝ)⁻¹ ^ (k + 2) := by
            rw [← pow_add]
            ring_nf
          rw [hpow, ← mul_assoc, inv_pow, mul_inv_cancel₀ (by positivity), one_mul]
  have hgeom : ∀ m : ℕ, ∑ k ∈ Finset.range m, (2 : ℝ)⁻¹ ^ (k + 2) ≤ 1 := by
    intro m
    have hlt : ∑ k ∈ Finset.range m, (2 : ℝ)⁻¹ ^ k < 2 := by
      induction m with
      | zero => norm_num
      | succ m ihm =>
        have hstep : ∑ k ∈ Finset.range (m + 1), (2 : ℝ)⁻¹ ^ k =
            1 + (2 : ℝ)⁻¹ * ∑ k ∈ Finset.range m, (2 : ℝ)⁻¹ ^ k := by
          rw [Finset.sum_range_succ', Finset.mul_sum]
          simp [pow_zero, pow_succ, mul_comm]
          ring
        linarith
    have hmul4 : ∑ k ∈ Finset.range m, (2 : ℝ)⁻¹ ^ (k + 2) =
        (4 : ℝ)⁻¹ * ∑ k ∈ Finset.range m, (2 : ℝ)⁻¹ ^ k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pow_add]
      norm_num
      ring
    rw [hmul4]
    linarith
  exact (Finset.sum_le_sum hfiber).trans (hgeom K)

private theorem mem_mlLevelTrace_exists_emit (e : Code) (k : ℕ) :
    ∀ N : ℕ, ∀ {u : List Bool}, u ∈ (mlLevelTrace e k N).1 →
      ∃ j < N, u ∈ (mlLevelTrace e k (j + 1)).2 := by
  intro N
  induction N with
  | zero => simp [mlLevelTrace]
  | succ m ihm =>
    intro u hu
    simp only [mlLevelTrace] at hu
    cases hst : levelStageWord e k m with
    | none =>
      rw [hst] at hu
      obtain ⟨j, hj, hju⟩ := ihm hu
      exact ⟨j, Nat.lt_succ_of_lt hj, hju⟩
    | some w' =>
      rw [hst] at hu
      rcases List.mem_append.mp hu with hseen | hnew
      · obtain ⟨j, hj, hju⟩ := ihm hseen
        exact ⟨j, Nat.lt_succ_of_lt hj, hju⟩
      · exact ⟨m, Nat.lt_succ_self _, by simp [mlLevelTrace, hst, hnew]⟩

/-- **Incompressibility implies Martin-Löf randomness**: any tape `x : ℕ → Bool` whose initial
segments are incompressible (`n ≤ K(x ↾ n) + c`) passes every `MartinLofTest`. -/
theorem isMartinLofRandom_of_le_complexity {x : ℕ → Bool}
    (hincomp : ∃ c : ℕ, ∀ n : ℕ,
      n ≤ DescriptionMethod.universalPrefixBits.complexity
        (List.ofFn fun i : Fin n => x i) + c) :
    IsMartinLofRandom x := by
  obtain ⟨c, hc⟩ := hincomp
  intro T
  obtain ⟨e, he⟩ := rePred_iff_exists_code.mp T.re
  obtain ⟨C, hC⟩ :=
    DescriptionMethod.minorizesPrefixPartrec_universalPrefixBits.kraftChaitin_of_sum_le_one
      (primrec_mlReq e).to_comp fun n =>
        le_of_eq_of_le
          (Finset.sum_congr rfl fun i _ => by cases mlReq e i <;> rfl)
          (mlReq_sum_le_one T he n)
  let k : ℕ := c + C + 1
  by_contra! hfail
  obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp (hfail (2 * k + 2))
  obtain ⟨y₀, hy₀⟩ := Part.dom_iff_mem.mp ((he (2 * k + 2, w)).mp hw)
  obtain ⟨f₀, hf₀⟩ := Code.evaln_complete.mp hy₀
  let j₀ : ℕ := encode (w, f₀)
  have hj₀ : levelStageWord e k j₀ = some w := by
    dsimp only [levelStageWord, j₀]
    rw [encodek, Option.bind_some, Option.map_eq_some_iff]
    exact ⟨y₀, Option.mem_def.mp hf₀, rfl⟩
  obtain ⟨u, hu_seen, hxu⟩ := mlLevelTrace_covers e x k (j₀ + 1) j₀ (Nat.lt_succ_self _) w hj₀ hxw
  obtain ⟨j, -, hj_mem⟩ := mem_mlLevelTrace_exists_emit e k (j₀ + 1) hu_seen
  obtain ⟨idx, hidx_lt, hidx_eq⟩ := List.getElem_of_mem hj_mem
  have hreq_eq : mlReq e (encode ((k, j), idx)) = some (u.length - k, u) := by
    dsimp only [mlReq]
    rw [encodek, Option.bind_some, Option.map_eq_some_iff]
    exact ⟨u, List.getElem?_eq_some_iff.mpr ⟨hidx_lt, hidx_eq⟩, rfl⟩
  have hK_ub := hC (encode ((k, j), idx)) (u.length - k) u hreq_eq
  rw [← DescriptionMethod.natCast_complexity_universalPrefixBits] at hK_ub
  have hK_ub_nat : DescriptionMethod.universalPrefixBits.complexity u ≤ (u.length - k) + C := by
    exact_mod_cast hK_ub
  have hxu_fn := mem_prefixCylinderList.mp hxu
  have hu_eq : u = List.ofFn fun i : Fin u.length => x i := by
    refine List.ext_getElem (by simp) fun i hi1 hi2 => ?_
    simpa using (hxu_fn ⟨i, hi1⟩).symm
  have hK_lb := hc u.length
  rw [← hu_eq] at hK_lb
  have hlen_u : 2 * k + 2 ≤ u.length :=
    (mlLevelTrace_level_bound T he k (j₀ + 1) {u} fun v hv => by
      simpa using (Finset.mem_singleton.mp hv) ▸ hu_seen).1 u
      (Finset.mem_singleton_self u)
  omega

/-- **Chaitin's `Ω` is Martin-Löf random** [LiVitanyi2019, ShenUspenskyVereshchagin2017]. -/
theorem isMartinLofRandom_chaitinOmega :
    IsMartinLofRandom
      (realBit (DescriptionMethod.chaitinOmega DescriptionMethod.universalPrefix)) := by
  refine isMartinLofRandom_of_le_complexity ?_
  obtain ⟨c, hc⟩ := DescriptionMethod.exists_le_complexity_realPrefix_chaitinOmega
  refine ⟨c, fun n => ?_⟩
  have heq : (List.ofFn fun i : Fin n =>
      realBit (DescriptionMethod.chaitinOmega DescriptionMethod.universalPrefix) i) =
      realPrefix (DescriptionMethod.chaitinOmega DescriptionMethod.universalPrefix) n := by
    refine List.ext_getElem (by simp) fun i hi1 hi2 => ?_
    simp [realPrefix]
  rw [heq]
  exact hc n

/-! ### Chaitin's incompleteness theorem for bits of `Ω` -/

private theorem primrec_maxFst :
    Primrec fun L : List (ℕ × Bool) => (L.map Prod.fst).foldr max 0 := by
  have hmap : Primrec fun L : List (ℕ × Bool) => L.map Prod.fst :=
    Primrec.list_map Primrec.id (Primrec.fst.comp Primrec.snd).to₂
  have hh : Primrec₂ fun (_ : List ℕ) (am : ℕ × ℕ) => max am.1 am.2 :=
    Primrec₂.mk <| Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)
  have hfold : Primrec fun L : List ℕ => L.foldr max 0 :=
    (Primrec.list_foldr Primrec.id (Primrec.const 0) hh).of_eq fun _ => rfl
  exact hfold.comp hmap

private theorem fst_le_foldr_max (L : List (ℕ × Bool)) {ib : ℕ × Bool} (hib : ib ∈ L) :
    ib.1 ≤ (L.map Prod.fst).foldr max 0 := by
  induction L with
  | nil => simp at hib
  | cons a rest ih =>
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp hib with rfl | hib'
    · exact le_max_left _ _
    · exact (ih hib').trans (le_max_right _ _)

private def bitCandS (e : Code) (j : ℕ) : Option (ℕ × Bool) :=
  (decode (α := (ℕ × Bool) × ℕ) j).bind fun pf =>
    (Code.evaln pf.2 e (encode pf.1)).map fun _ => pf.1

private theorem primrec_bitCandS (e : Code) : Primrec (bitCandS e) := by
  have hev : Primrec fun pf : (ℕ × Bool) × ℕ => Code.evaln pf.2 e (encode pf.1) :=
    Code.primrec_evaln.comp <| Primrec.pair (Primrec.pair Primrec.snd (Primrec.const e))
      (Primrec.encode.comp Primrec.fst)
  have hmap : Primrec fun pf : (ℕ × Bool) × ℕ =>
      (Code.evaln pf.2 e (encode pf.1)).map fun _ => pf.1 :=
    Primrec.option_map hev (Primrec.fst.comp Primrec.fst).to₂
  exact (Primrec.option_bind Primrec.decode (hmap.comp Primrec.snd).to₂).of_eq fun _ => rfl

private def bitTableS (e : Code) : ℕ → List (ℕ × Bool) :=
  Nat.distinctValues (bitCandS e)

private theorem primrec_bitTableS (e : Code) : Primrec (bitTableS e) := by
  have h : Primrec₂ fun (_ : Unit) (j : ℕ) => bitCandS e j :=
    Primrec₂.mk <| (primrec_bitCandS e).comp Primrec.snd
  exact ((Primrec.distinctValues h).comp (Primrec.const ()) Primrec.id).of_eq fun _ => rfl

private def bitMissingIdx (L : List (ℕ × Bool)) : List ℕ :=
  let M := (L.map Prod.fst).foldr max 0 + 1
  (List.range M).foldr
    (fun idx acc => if L.any (fun ib => decide (ib.1 = idx)) then acc else idx :: acc) []

private theorem primrec_bitMissingIdx : Primrec bitMissingIdx := by
  have hM : Primrec fun L : List (ℕ × Bool) => (L.map Prod.fst).foldr max 0 + 1 :=
    Primrec.succ.comp primrec_maxFst
  have hany : PrimrecRel fun (L : List (ℕ × Bool)) (idx : ℕ) => ∃ ib ∈ L, ib.1 = idx :=
    PrimrecRel.exists_mem_list (Primrec.eq.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
  have hh : Primrec₂ fun (L : List (ℕ × Bool)) (ia : ℕ × List ℕ) =>
      if L.any (fun ib => decide (ib.1 = ia.1)) then ia.2 else ia.1 :: ia.2 := by
    have hpred : PrimrecPred fun arg : List (ℕ × Bool) × (ℕ × List ℕ) =>
        ∃ ib ∈ arg.1, ib.1 = arg.2.1 :=
      hany.comp Primrec.fst (Primrec.fst.comp Primrec.snd)
    refine Primrec₂.mk <| (Primrec.ite hpred
      (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd))).of_eq fun ⟨L, ⟨idx, acc⟩⟩ => ?_
    have hiff : (L.any fun ib => decide (ib.1 = idx)) = true ↔ ∃ ib ∈ L, ib.1 = idx := by
      simp [List.any_eq_true]
    by_cases h : ∃ ib ∈ L, ib.1 = idx
    · simp [h, hiff.mpr h]
    · have hf : (L.any fun ib => decide (ib.1 = idx)) = false :=
        Bool.eq_false_iff.mpr (mt hiff.mp h)
      simp [h, hf]
  exact (Primrec.list_foldr (Primrec.list_range.comp hM) (Primrec.const []) hh).of_eq fun _ => rfl

private def bitReconstruct (L : List (ℕ × Bool)) (rest : List Bool) : List Bool :=
  let M := (L.map Prod.fst).foldr max 0 + 1
  let missing := bitMissingIdx L
  (List.range M).map fun idx =>
    match L.lookup idx with
    | some b => b
    | Option.none => rest.getD (missing.idxOf idx) false

private theorem primrec₂_bitReconstruct : Primrec₂ bitReconstruct := by
  have hlookup : Primrec₂ fun (L : List (ℕ × Bool)) (idx : ℕ) => L.lookup idx :=
    Primrec.listLookup.comp₂ Primrec₂.right Primrec₂.left
  have hM : Primrec fun L : List (ℕ × Bool) => (L.map Prod.fst).foldr max 0 + 1 :=
    Primrec.succ.comp primrec_maxFst
  have hnone : Primrec fun arg : List (ℕ × Bool) × List Bool × ℕ =>
      arg.2.1.getD ((bitMissingIdx arg.1).idxOf arg.2.2) false :=
    (Primrec.list_getD false).comp (Primrec.fst.comp Primrec.snd)
      (Primrec.list_idxOf.comp (Primrec.snd.comp Primrec.snd)
        (primrec_bitMissingIdx.comp Primrec.fst))
  have hel : Primrec₂ fun (Lr : List (ℕ × Bool) × List Bool) (idx : ℕ) =>
      match Lr.1.lookup idx with
      | some b => b
      | Option.none => Lr.2.getD ((bitMissingIdx Lr.1).idxOf idx) false :=
    Primrec₂.mk <| (Primrec.option_casesOn
      (hlookup.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      (hnone.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)))
      Primrec₂.right).of_eq fun ⟨⟨L, rest⟩, idx⟩ => by cases L.lookup idx <;> rfl
  exact Primrec₂.mk <| (Primrec.list_map (Primrec.list_range.comp (hM.comp Primrec.fst))
    hel).of_eq fun _ => rfl

private def bitIncompStep (e : Code) (q : List Bool) (n : ℕ) : Option (List Bool) :=
  (decodeSelfDelimiting? q).bind fun bp =>
    let b := bp.1
    let rest := bp.2
    if b.length = (b.foldr Nat.bit 0).size then
      let k := b.foldr Nat.bit 0
      let L := bitTableS e n
      if L.length = k ∧ rest.length = (bitMissingIdx L).length then
        some (bitReconstruct L rest)
      else Option.none
    else Option.none

private theorem primrec₂_bitIncompStep (e : Code) : Primrec₂ (bitIncompStep e) := by
  have hval : Primrec fun bp : List Bool × List Bool => bp.1.foldr Nat.bit 0 :=
    Primrec.list_foldr_nat_bit.comp Primrec.fst
  have htableS := primrec_bitTableS e
  have hcond : PrimrecPred fun arg : (List Bool × List Bool) × ℕ =>
      (bitTableS e arg.2).length = arg.1.1.foldr Nat.bit 0 ∧
        arg.1.2.length = (bitMissingIdx (bitTableS e arg.2)).length :=
    (Primrec.eq.comp (Primrec.list_length.comp (htableS.comp Primrec.snd))
      (hval.comp Primrec.fst)).and
      (Primrec.eq.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.list_length.comp (primrec_bitMissingIdx.comp (htableS.comp Primrec.snd))))
  have hb2 : Primrec fun arg : (List Bool × ℕ) × (List Bool × List Bool) =>
      if (bitTableS e arg.1.2).length = arg.2.1.foldr Nat.bit 0 ∧
          arg.2.2.length = (bitMissingIdx (bitTableS e arg.1.2)).length then
        some (bitReconstruct (bitTableS e arg.1.2) arg.2.2)
      else Option.none :=
    Primrec.ite
      (hcond.comp (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst)))
      (Primrec.option_some.comp
        (primrec₂_bitReconstruct.comp (htableS.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.snd.comp Primrec.snd)))
      (Primrec.const Option.none)
  have hinner : Primrec₂ fun (qn : List Bool × ℕ) (bp : List Bool × List Bool) =>
      if bp.1.length = (bp.1.foldr Nat.bit 0).size then
        if (bitTableS e qn.2).length = bp.1.foldr Nat.bit 0 ∧
            bp.2.length = (bitMissingIdx (bitTableS e qn.2)).length then
          some (bitReconstruct (bitTableS e qn.2) bp.2)
        else Option.none
      else Option.none :=
    Primrec₂.mk <| Primrec.ite
      (primrecPred_length_eq_size_foldr_bit.comp (Primrec.fst.comp Primrec.snd))
      hb2 (Primrec.const Option.none)
  exact Primrec₂.mk <| (Primrec.option_bind
    (primrec_decodeSelfDelimiting?.comp Primrec.fst) hinner).of_eq fun _ => rfl

/-- **Chaitin's bit-incompleteness theorem for `Ω`** [Chaitin1974], [LiVitanyi2019]: every
computably enumerable set `S ⊆ ℕ × Bool` that correctly predicts bits of
`Ω = chaitinOmega universalPrefix` is finite. -/
theorem finite_of_rePred_of_sound_realBit_chaitinOmega {S : Set (ℕ × Bool)}
    (hS : REPred fun p => p ∈ S)
    (hsound : ∀ i b, (i, b) ∈ S →
      realBit (DescriptionMethod.chaitinOmega DescriptionMethod.universalPrefix) i = b) :
    S.Finite := by
  obtain ⟨e, he⟩ := rePred_iff_exists_code.mp hS
  let decS : List Bool →. List Bool := fun q => Nat.rfindOpt (bitIncompStep e q)
  have hdecS_part : Partrec decS := Partrec.rfindOpt (primrec₂_bitIncompStep e).to_comp
  have hdecS_pf : InformationTheory.IsPrefixFree {q | (decS q).Dom} := by
    rintro q₁ h₁ q₂ h₂ hpref
    obtain ⟨n₁, x₁, hx₁⟩ := Nat.rfindOpt_dom.mp h₁
    obtain ⟨n₂, x₂, hx₂⟩ := Nat.rfindOpt_dom.mp h₂
    simp only [bitIncompStep, Option.mem_def, Option.bind_eq_some_iff] at hx₁ hx₂
    obtain ⟨⟨b₁, rest₁⟩, hd₁, hrest₁⟩ := hx₁
    obtain ⟨⟨b₂, rest₂⟩, hd₂, hrest₂⟩ := hx₂
    split_ifs at hrest₁ with hsz₁ hk₁
    split_ifs at hrest₂ with hsz₂ hk₂
    have hq₁ := decodeSelfDelimiting?_eq_some_iff.mp hd₁
    have hq₂ := decodeSelfDelimiting?_eq_some_iff.mp hd₂
    rw [← hq₁, ← hq₂] at hpref
    obtain ⟨hb_eq, hrest_pref⟩ := Cslib.BitString.prefix_append_of_isPrefixFree
      isPrefixFree_range_selfDelimitingCode ⟨b₁, rfl⟩ ⟨b₂, rfl⟩ hpref
    have hb₁₂ : b₁ = b₂ := by
      have h' : selfDelimitingCode b₁ ++ [] = selfDelimitingCode b₂ ++ [] := by simpa using hb_eq
      exact (selfDelimitingCode_append_inj h').1
    subst hb₁₂
    have htable_eq : bitTableS e n₁ = bitTableS e n₂ := by
      rcases le_total n₁ n₂ with hle | hle
      · exact (Nat.distinctValues_prefix (bitCandS e) hle).eq_of_length (hk₁.1.trans hk₂.1.symm)
      · exact ((Nat.distinctValues_prefix (bitCandS e) hle).eq_of_length
          (hk₂.1.trans hk₁.1.symm)).symm
    have hrest_eq : rest₁ = rest₂ := by
      refine hrest_pref.eq_of_length ?_
      rw [hk₁.2, hk₂.2, htable_eq]
    rw [← hq₁, ← hq₂, hrest_eq]
  obtain ⟨c₁, hc₁⟩ :=
    DescriptionMethod.minorizesPrefixPartrec_universalPrefixBits decS hdecS_part hdecS_pf
  obtain ⟨c₀, hc₀⟩ := DescriptionMethod.exists_le_complexity_realPrefix_chaitinOmega
  by_contra hinf
  have hex_table_len : ∀ k : ℕ, ∃ n : ℕ, (bitTableS e n).length = k := by
    intro k
    induction k with
    | zero => exact ⟨0, rfl⟩
    | succ k ih =>
      obtain ⟨n, hn⟩ := ih
      have hex_new : ∃ p ∈ S, p ∉ bitTableS e n := by
        by_contra! hsub
        exact hinf ((bitTableS e n).finite_toSet.subset hsub)
      obtain ⟨p, hpS, hp_not⟩ := hex_new
      obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp ((he p).mp hpS)
      obtain ⟨f, hf⟩ := Code.evaln_complete.mp hy
      let j := encode (p, f)
      have hj : bitCandS e j = some p := by
        dsimp only [bitCandS, j]
        rw [encodek]
        simp [Option.mem_def.mp hf]
      have hle_j : n < j + 1 := by
        by_contra! hle
        exact hp_not (Nat.mem_distinctValues.mpr ⟨j, hle, hj⟩)
      have hex_ge : ∃ m : ℕ, k + 1 ≤ (bitTableS e m).length := by
        refine ⟨j + 1, ?_⟩
        obtain ⟨t, ht⟩ := Nat.distinctValues_prefix (bitCandS e) (Nat.le_of_lt hle_j)
        have hp_in : p ∈ bitTableS e (j + 1) :=
          Nat.mem_distinctValues.mpr ⟨j, Nat.lt_succ_self _, hj⟩
        have hlen_lt : (bitTableS e n).length < (bitTableS e (j + 1)).length := by
          dsimp only [bitTableS]
          rw [← ht, List.length_append]
          cases t with
          | nil =>
            simp only [List.append_nil] at ht
            dsimp only [bitTableS] at hp_in hp_not
            exact absurd (ht ▸ hp_in) hp_not
          | cons _ _ => simp
        omega
      let m₀ := Nat.find hex_ge
      have hspec_m0 : k + 1 ≤ (bitTableS e m₀).length := Nat.find_spec hex_ge
      have hm₀_pos : 0 < m₀ :=
        Nat.pos_of_ne_zero fun hz => by simp [hz, bitTableS] at hspec_m0
      have hlt_pred : (bitTableS e (m₀ - 1)).length < k + 1 :=
        lt_of_not_ge (Nat.find_min hex_ge (Nat.pred_lt hm₀_pos.ne'))
      have hsucc_eq : bitTableS e m₀ = bitTableS e ((m₀ - 1) + 1) := by congr 1; omega
      have hstep_le : (bitTableS e m₀).length ≤ (bitTableS e (m₀ - 1)).length + 1 := by
        rw [hsucc_eq]
        dsimp only [bitTableS, Nat.distinctValues]
        cases bitCandS e (m₀ - 1) with
        | none => simp
        | some b =>
          dsimp only
          split_ifs <;> simp
      exact ⟨m₀, by omega⟩
  let m : ℕ := c₀ + c₁ + 10
  let k : ℕ := 2 ^ m
  obtain ⟨n, hn⟩ := hex_table_len k
  let L := bitTableS e n
  have hL_S : ∀ ib ∈ L, ib ∈ S := fun ib hib => by
    obtain ⟨j, -, hj⟩ := Nat.mem_distinctValues.mp hib
    simp only [bitCandS, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hj
    obtain ⟨⟨p, f⟩, -, ⟨_, hf, rfl⟩⟩ := hj
    exact (he p).mpr (Part.dom_iff_mem.mpr ⟨_, Code.evaln_sound hf⟩)
  have hL_sound : ∀ ib ∈ L,
      realBit (DescriptionMethod.chaitinOmega DescriptionMethod.universalPrefix) ib.1 = ib.2 :=
    fun ib hib => hsound ib.1 ib.2 (hL_S ib hib)
  have hL_fst_inj : (L.map Prod.fst).Nodup := by
    refine (Nat.nodup_distinctValues (bitCandS e) n).map_on fun ⟨i₁, b₁⟩ h₁ ⟨i₂, b₂⟩ h₂ hi => ?_
    dsimp only at hi
    subst hi
    congr 1
    exact (hL_sound _ h₁).symm.trans (hL_sound _ h₂)
  let M := (L.map Prod.fst).foldr max 0 + 1
  have hL_lt_M : ∀ ib ∈ L, ib.1 < M := fun ib hib =>
    Nat.lt_succ_of_le (fst_le_foldr_max L hib)
  have hmissing_prop :
      (bitMissingIdx L).Nodup ∧
      (∀ idx ∈ bitMissingIdx L, idx < M ∧ ∀ ib ∈ L, ib.1 ≠ idx) ∧
      (∀ idx < M, (∃ ib ∈ L, ib.1 = idx) ∨ idx ∈ bitMissingIdx L) := by
    have hnd_range : (List.range M).Nodup := List.nodup_range
    suffices hgen : ∀ R : List ℕ, R.Nodup → (∀ idx ∈ R, idx < M) →
        (R.foldr (fun idx acc => if L.any (fun ib => decide (ib.1 = idx)) then acc else idx :: acc)
          []).Nodup ∧
        (∀ idx ∈ R.foldr
            (fun idx acc => if L.any (fun ib => decide (ib.1 = idx)) then acc else idx :: acc) [],
          idx ∈ R ∧ idx < M ∧ ∀ ib ∈ L, ib.1 ≠ idx) ∧
        (∀ idx ∈ R, (∃ ib ∈ L, ib.1 = idx) ∨ idx ∈ R.foldr
          (fun idx acc => if L.any (fun ib => decide (ib.1 = idx)) then acc else idx :: acc)
          []) by
      have hg := hgen (List.range M) hnd_range fun idx h => List.mem_range.mp h
      refine ⟨hg.1, fun idx hidx => (hg.2.1 idx hidx).2, fun idx hidx => ?_⟩
      exact hg.2.2 idx (List.mem_range.mpr hidx)
    intro R hRnd hRlt
    induction R with
    | nil => simp
    | cons a t iht =>
      rcases List.nodup_cons.mp hRnd with ⟨hat, htnd⟩
      obtain ⟨ihnd, ihsub, ihcov⟩ := iht htnd fun idx h => hRlt idx (List.mem_cons_of_mem a h)
      simp only [List.foldr_cons]
      by_cases ha : L.any (fun ib => decide (ib.1 = a)) = true
      · simp only [ha, ↓reduceIte]
        refine ⟨ihnd, fun idx hidx => ?_, fun idx hidx => ?_⟩
        · obtain ⟨h1, h2⟩ := ihsub idx hidx
          exact ⟨List.mem_cons_of_mem a h1, h2⟩
        · rcases List.mem_cons.mp hidx with rfl | ht
          · obtain ⟨ib, hib, heq⟩ := List.any_eq_true.mp ha
            exact Or.inl ⟨ib, hib, decide_eq_true_eq.mp heq⟩
          · exact ihcov idx ht
      · have haf : L.any (fun ib => decide (ib.1 = a)) = false := Bool.eq_false_iff.mpr ha
        simp only [haf, Bool.false_eq_true, ↓reduceIte]
        have ha_no : ∀ ib ∈ L, ib.1 ≠ a := fun ib hib heq => by
          apply ha
          exact List.any_eq_true.mpr ⟨ib, hib, decide_eq_true heq⟩
        refine ⟨List.nodup_cons.mpr ⟨fun hm => hat (ihsub a hm).1, ihnd⟩, fun idx hidx => ?_,
          fun idx hidx => ?_⟩
        · rcases List.mem_cons.mp hidx with rfl | ht
          · exact ⟨List.mem_cons_self, hRlt idx List.mem_cons_self, ha_no⟩
          · obtain ⟨h1, h2⟩ := ihsub idx ht
            exact ⟨List.mem_cons_of_mem a h1, h2⟩
        · rcases List.mem_cons.mp hidx with rfl | ht
          · exact Or.inr List.mem_cons_self
          · rcases ihcov idx ht with hL | hacc
            · exact Or.inl hL
            · exact Or.inr (List.mem_cons_of_mem a hacc)
  have hmissing_len : (bitMissingIdx L).length + k = M := by
    have hdisj : Disjoint (bitMissingIdx L).toFinset (L.map Prod.fst).toFinset := by
      rw [Finset.disjoint_left]
      intro idx h1 h2
      obtain ⟨ib, hib, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp h2)
      exact (hmissing_prop.2.1 ib.1 (List.mem_toFinset.mp h1)).2 ib hib rfl
    have hunion : (bitMissingIdx L).toFinset ∪ (L.map Prod.fst).toFinset = Finset.range M := by
      ext idx
      simp only [Finset.mem_union, List.mem_toFinset, List.mem_map, Finset.mem_range]
      constructor
      · rintro (h | ⟨ib, hib, rfl⟩)
        · exact (hmissing_prop.2.1 idx h).1
        · exact hL_lt_M ib hib
      · intro hlt
        rcases hmissing_prop.2.2 idx hlt with ⟨ib, hib, rfl⟩ | hm
        · exact Or.inr ⟨ib, hib, rfl⟩
        · exact Or.inl hm
    have hcard := congrArg Finset.card hunion
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_range,
      List.toFinset_card_of_nodup hmissing_prop.1,
      List.toFinset_card_of_nodup hL_fst_inj, List.length_map] at hcard
    simpa [L, hn] using hcard
  let Ω := DescriptionMethod.chaitinOmega DescriptionMethod.universalPrefix
  let rest : List Bool := (bitMissingIdx L).map (realBit Ω)
  have hrest_len : rest.length = (bitMissingIdx L).length := by simp [rest]
  let q : List Bool := selfDelimitingCode k.bits ++ rest
  have hq_step : bitIncompStep e q n = some (bitReconstruct L rest) := by
    have hsz : k.bits.length = (k.bits.foldr Nat.bit 0).size := by
      rw [Nat.foldr_bit_bits, Nat.size_eq_bits_len]
    simp only [bitIncompStep, q, decodeSelfDelimiting?_selfDelimitingCode_append,
      Option.bind_some, Nat.foldr_bit_bits, hsz, ↓reduceIte, L, hn, hrest_len, and_self]
  have hreconstruct_eq : bitReconstruct L rest = realPrefix Ω M := by
    refine List.ext_getElem (by simp [bitReconstruct, M]) fun idx hidx1 hidx2 => ?_
    have hidxM : idx < M := by simpa using hidx2
    simp only [bitReconstruct, List.getElem_map, List.getElem_range]
    rw [getElem_realPrefix hidx2]
    cases hlook : L.lookup idx with
    | some b =>
      obtain ⟨l₁, l₂, hl, -⟩ := List.lookup_eq_some_iff.mp hlook
      have hib : (idx, b) ∈ L := by simp [hl]
      exact (hL_sound (idx, b) hib).symm
    | none =>
      have hnotin : ¬ ∃ ib ∈ L, ib.1 = idx := by
        rintro ⟨⟨i', b'⟩, hib, rfl⟩
        have hmem_look := (List.lookup_eq_none_iff).mp hlook (i', b') hib
        simp at hmem_look
      rcases hmissing_prop.2.2 idx hidxM with h | hmiss
      · exact absurd h hnotin
      · obtain ⟨j, hj_lt, hj_eq⟩ := List.getElem_of_mem hmiss
        have hidxOf : (bitMissingIdx L).idxOf idx = j := by
          rw [← hj_eq]
          exact List.Nodup.idxOf_getElem hmissing_prop.1 j hj_lt
        rw [hidxOf]
        have hj_rest : j < rest.length := by simpa [hrest_len] using hj_lt
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_some_iff.mpr ⟨hj_rest, rfl⟩,
          rest, hj_eq]
  obtain ⟨out, hout⟩ :=
    Part.dom_iff_mem.mp (Nat.rfindOpt_dom.mpr ⟨n, bitReconstruct L rest, hq_step⟩)
  obtain ⟨n', hn'⟩ := Nat.rfindOpt_spec hout
  have hn'_eq : bitIncompStep e q n' =
      if (bitTableS e n').length = k ∧ rest.length = (bitMissingIdx (bitTableS e n')).length then
        some (bitReconstruct (bitTableS e n') rest)
      else Option.none := by
    rw [bitIncompStep, decodeSelfDelimiting?_selfDelimitingCode_append]
    simp only [Option.bind_some, Nat.foldr_bit_bits]
    have hsz : k.bits.length = k.size := Nat.size_eq_bits_len k
    simp only [hsz, ↓reduceIte]
  rw [hn'_eq] at hn'
  split_ifs at hn' with hcond
  · have hnq : bitTableS e n' = bitTableS e n := by
      rcases le_total n n' with hle | hle
      · exact ((Nat.distinctValues_prefix (bitCandS e) hle).eq_of_length
          (hn.trans hcond.1.symm)).symm
      · exact (Nat.distinctValues_prefix (bitCandS e) hle).eq_of_length
          (hcond.1.trans hn.symm)
    have hout_eq : out = realPrefix Ω M := by
      rw [Option.mem_def, Option.some.injEq] at hn'
      rw [← hn', hnq, ← hreconstruct_eq]
    subst hout_eq
    have hK_ub := hc₁ q (realPrefix Ω M) hout
    rw [← DescriptionMethod.natCast_complexity_universalPrefixBits] at hK_ub
    have hK_ub_nat : DescriptionMethod.universalPrefixBits.complexity (realPrefix Ω M) ≤
        q.length + c₁ := by
      exact_mod_cast hK_ub
    have hK_lb_nat : M ≤
        DescriptionMethod.universalPrefixBits.complexity (realPrefix Ω M) + c₀ := hc₀ M
    have hk_size : k.size = m + 1 := by
      dsimp only [k]
      rw [Nat.size_pow]
    have hsz_size : (m + 1).size ≤ m + 1 := Nat.size_le.mpr Nat.lt_two_pow_self
    have hq_len : q.length = k.bits.length + (2 * k.bits.length.size + 1) + rest.length := by
      simp only [q, List.length_append, length_selfDelimitingCode]
    have hk_bits : k.bits.length = m + 1 := by rw [Nat.size_eq_bits_len, hk_size]
    have hrest_le : rest.length + k = M := by rw [hrest_len, hmissing_len]
    have hlin : k ≤ 3 * m + 4 + c₀ + c₁ := by
      rw [hk_bits] at hq_len
      omega
    have hpow_gt : ∀ t : ℕ, 4 * t + 34 < 2 ^ (t + 10) := fun t => by
      induction t with
      | zero => norm_num
      | succ t ih =>
        rw [show t + 1 + 10 = (t + 10) + 1 by omega, pow_succ]
        omega
    have hlt_pow : 4 * (c₀ + c₁) + 34 < k := hpow_gt (c₀ + c₁)
    have hm_sum : 3 * m + 4 + c₀ + c₁ = 4 * (c₀ + c₁) + 34 := by dsimp [m]; omega
    omega
  · simp at hn'

end Cslib.Kolmogorov




