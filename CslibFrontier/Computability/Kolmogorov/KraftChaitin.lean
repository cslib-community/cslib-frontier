/-
Copyright (c) 2026 Matthew Doty, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Kolmogorov.PrefixFree
public import Mathlib.InformationTheory.Coding.Kraft
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import CslibFrontier.Foundations.Data.List.Primrec
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Rat.Cast.Order

/-!
# Kraft's inequality and the online Kraft–Chaitin theorem

This file develops the quantitative side of binary prefix-free codes for Kolmogorov complexity:

* **Kraft's inequality**: specialization of Mathlib's `InformationTheory.IsPrefixFree` Kraft
  theorems (`Mathlib/InformationTheory/Coding/Kraft.lean`) to binary prefix-free sets and
  `DescriptionMethod.IsPrefixFree`, together with tail and incomparable-prefix bounds needed for
  Chaitin's `Ω`.
* **Executable online Kraft–Chaitin allocator**: given any stream of codeword-length requests
  `reqs : ℕ → Option ℕ` whose finite partial Kraft sums `∑ i < n, 2⁻¹ ^ ℓ_i` stay below `1`,
  `kcTrace` maintains a list of prefix-disjoint available dyadic intervals of pairwise distinct
  lengths (`splitAtLen`, `bestLenLe?`, `splitFrom`), always allocating a codeword of the requested
  length disjoint from all previous allocations and remaining intervals.
* **Kraft–Chaitin theorem** [LiVitanyi2019, ShenUspenskyVereshchagin2017]: any computable stream
  `req : ℕ → Option (ℕ × α)` with Kraft sum at most `1` is realized by a computable prefix-free
  `DescriptionMethod α`, giving `K_U(y) ≤ ℓ + O(1)` for every `U.MinorizesPrefixPartrec`.

## Main definitions

* `Cslib.Kolmogorov.PrefixDisjoint`: prefix incomparability of two binary strings.
* `Cslib.Kolmogorov.splitFrom`, `Cslib.Kolmogorov.bestLenLe?`, `Cslib.Kolmogorov.splitAtLen`,
  `Cslib.Kolmogorov.kcStep`, `Cslib.Kolmogorov.kcAllocList`, `Cslib.Kolmogorov.kcTrace`,
  `Cslib.Kolmogorov.kcCode`: executable online binary Kraft–Chaitin allocator.

## Main results

* `Cslib.Kolmogorov.DescriptionMethod.IsPrefixFree.finsetSum_two_inv_pow_length_le_one`,
  `Cslib.Kolmogorov.DescriptionMethod.IsPrefixFree.summable_two_inv_pow_length`,
  `Cslib.Kolmogorov.DescriptionMethod.IsPrefixFree.tsum_two_inv_pow_length_le_one`: binary Kraft's
  inequality for prefix-free description methods.
* `Cslib.Kolmogorov.kcAllocList_eq_some_of_sum_le_one`: correctness of the finite executable
  allocator on any list of lengths with Kraft sum at most `1`.
* `Cslib.Kolmogorov.DescriptionMethod.kraftChaitin_of_sum_le_one`,
  `Cslib.Kolmogorov.DescriptionMethod.kraftChaitin`: construction of a prefix-free computable
  description method realizing any valid computable request stream.
* `Cslib.Kolmogorov.DescriptionMethod.MinorizesPrefixPartrec.kraftChaitin_of_sum_le_one`,
  `Cslib.Kolmogorov.DescriptionMethod.MinorizesPrefixPartrec.kraftChaitin`: `K_U(y) ≤ ℓ + O(1)`
  for any prefix-free minorizing method `U`.

## References

* [L. G. Kraft, *A Device for Quantizing, Grouping, and Coding Amplitude-Modulated
  Pulses*][Kraft1949]
* [M. Li, P. Vitányi, *An Introduction to Kolmogorov Complexity and Its
  Applications*][LiVitanyi2019]
* [A. Shen, V. A. Uspensky, N. Vereshchagin, *Kolmogorov Complexity and Algorithmic
  Randomness*][ShenUspenskyVereshchagin2017]
-/

public section

open scoped BigOperators

namespace Cslib.Kolmogorov

/-! ### Prefix-disjointness and Kraft's inequality -/

/-- Two binary words are *prefix-disjoint* when neither is a prefix of the other. -/
@[expose] def PrefixDisjoint (u v : List Bool) : Prop :=
  ¬ (u <+: v) ∧ ¬ (v <+: u)

@[simp]
theorem PrefixDisjoint.symm {u v : List Bool} (h : PrefixDisjoint u v) : PrefixDisjoint v u :=
  ⟨h.2, h.1⟩

theorem PrefixDisjoint.irrefl (u : List Bool) : ¬ PrefixDisjoint u u :=
  fun h => h.1 List.prefix_rfl

theorem PrefixDisjoint.ne {u v : List Bool} (h : PrefixDisjoint u v) : u ≠ v :=
  fun heq => PrefixDisjoint.irrefl v (heq ▸ h)

/-- If `u` is prefix-disjoint with `y` and `x` extends `u`, then `x` is prefix-disjoint with `y`. -/
theorem PrefixDisjoint.of_prefix_left {u x y : List Bool} (huy : PrefixDisjoint u y)
    (hux : u <+: x) : PrefixDisjoint x y :=
  ⟨fun hxy => huy.1 (by trans x <;> assumption), fun hyx =>
    (List.prefix_or_prefix_of_prefix hux hyx).elim huy.1 huy.2⟩

theorem prefixDisjoint_append_false_true (u : List Bool) :
    PrefixDisjoint (u ++ [false]) (u ++ [true]) := by
  constructor <;> intro hp <;> have h' := (List.prefix_append_right_inj u).mp hp <;> simp at h'

theorem isPrefixFree_of_pairwise_prefixDisjoint {L : List (List Bool)}
    (hL : L.Pairwise PrefixDisjoint) : InformationTheory.IsPrefixFree {w | w ∈ L} := by
  intro x hx y hy hxy
  by_contra hne
  induction L with
  | nil => simp at hx
  | cons a rest ih =>
    rw [List.pairwise_cons] at hL
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · exact hne rfl
    · exact (hL.1 y hy').1 hxy
    · exact (hL.1 x hx').2 hxy
    · exact ih hL.2 hx' hy'

theorem nodup_of_pairwise_prefixDisjoint {L : List (List Bool)} (hL : L.Pairwise PrefixDisjoint) :
    L.Nodup :=
  hL.imp fun h => h.ne

namespace DescriptionMethod

-- Binary Kraft's inequality (finite set form) [Kraft1949].
private theorem finsetSum_two_inv_pow_length_le_one_of_isPrefixFree {S : Finset (List Bool)}
    (hS : InformationTheory.IsPrefixFree (S : Set (List Bool))) :
    ∑ w ∈ S, (2 : ℝ)⁻¹ ^ w.length ≤ 1 := by
  simpa only [Fintype.card_bool, Nat.cast_ofNat, one_div] using
    hS.finsetSum_one_div_card_pow_length_le_one

-- Summability of `2⁻¹ ^ |w|` over any binary prefix-free set.
private theorem summable_two_inv_pow_length_of_isPrefixFree {S : Set (List Bool)}
    (hS : InformationTheory.IsPrefixFree S) :
    Summable fun w : S => (2 : ℝ)⁻¹ ^ (w : List Bool).length := by
  simpa only [Fintype.card_bool, Nat.cast_ofNat, one_div] using
    hS.summable_one_div_card_pow_length

-- Binary Kraft's inequality (infinite set form) [Kraft1949].
private theorem tsum_two_inv_pow_length_le_one_of_isPrefixFree {S : Set (List Bool)}
    (hS : InformationTheory.IsPrefixFree S) :
    ∑' w : S, (2 : ℝ)⁻¹ ^ (w : List Bool).length ≤ 1 := by
  simpa only [Fintype.card_bool, Nat.cast_ofNat, one_div] using
    hS.tsum_one_div_card_pow_length_le_one

/-- Adding a prefix `q` incomparable with every member of `S` strictly reserves weight
`2⁻¹ ^ |q|`. -/
theorem tsum_two_inv_pow_length_add_le_one_of_incomparable {S : Set (List Bool)}
    (hS : InformationTheory.IsPrefixFree S) {q : List Bool}
    (hq : ∀ r ∈ S, ¬ (q <+: r) ∧ ¬ (r <+: q)) :
    (∑' w : S, (2 : ℝ)⁻¹ ^ (w : List Bool).length) + (2 : ℝ)⁻¹ ^ q.length ≤ 1 := by
  have hq_not : q ∉ S := fun hmem => (hq q hmem).1 List.prefix_rfl
  refine add_le_of_le_sub_right ?_
  refine (summable_two_inv_pow_length_of_isPrefixFree hS).tsum_le_of_sum_le fun F => ?_
  classical
  let T : Finset (List Bool) := F.image Subtype.val
  have hTS : (T : Set (List Bool)) ⊆ S := by
    intro x hx
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    exact w.2
  have hqT : q ∉ T := fun h => hq_not (hTS h)
  have hpf :
      InformationTheory.IsPrefixFree ((insert q T : Finset (List Bool)) : Set (List Bool)) := by
    intro x hx y hy hxy
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · rfl
    · exact absurd hxy (hq y (hTS hy)).1
    · exact absurd hxy (hq x (hTS hx)).2
    · exact hS x (hTS hx) y (hTS hy) hxy
  have hkraft := finsetSum_two_inv_pow_length_le_one_of_isPrefixFree hpf
  rw [Finset.sum_insert hqT] at hkraft
  have hsum_F : ∑ w ∈ F, (2 : ℝ)⁻¹ ^ (w : List Bool).length = ∑ w ∈ T, (2 : ℝ)⁻¹ ^ w.length :=
    (Finset.sum_image (f := fun w : List Bool => (2 : ℝ)⁻¹ ^ w.length)
      fun _ _ _ _ h => Subtype.ext h).symm
  linarith

/-- Any finite prefix subset `T ⊆ S` plus any outside element `p ∈ S \ T` has total weight at most
the full Kraft sum over `S`. -/
theorem finsetSum_add_two_inv_pow_le_tsum_of_notMem {S : Set (List Bool)}
    (hS : InformationTheory.IsPrefixFree S) {T : Finset (List Bool)}
    (hT : (T : Set (List Bool)) ⊆ S) {p : List Bool} (hp : p ∈ S) (hpT : p ∉ T) :
    (∑ w ∈ T, (2 : ℝ)⁻¹ ^ w.length) + (2 : ℝ)⁻¹ ^ p.length ≤
      ∑' w : S, (2 : ℝ)⁻¹ ^ (w : List Bool).length := by
  classical
  have hs := summable_two_inv_pow_length_of_isPrefixFree hS
  let U : Finset (List Bool) := insert p T
  have hU_sub : (U : Set (List Bool)) ⊆ S := by
    simpa [U] using Set.insert_subset hp hT
  let fEmbed : {x : List Bool // x ∈ U} ↪ S :=
    ⟨fun x => ⟨x.1, hU_sub x.2⟩, fun a b h => Subtype.ext (congrArg (fun z : S => z.1) h)⟩
  let F : Finset S := U.attach.map fEmbed
  have hF_sum : ∑ w ∈ F, (2 : ℝ)⁻¹ ^ (w : List Bool).length =
      (∑ w ∈ T, (2 : ℝ)⁻¹ ^ w.length) + (2 : ℝ)⁻¹ ^ p.length := by
    rw [Finset.sum_map]
    calc ∑ x ∈ U.attach, (2 : ℝ)⁻¹ ^ (fEmbed x : List Bool).length
      _ = ∑ x ∈ U, (2 : ℝ)⁻¹ ^ x.length := Finset.sum_attach U (fun x => (2 : ℝ)⁻¹ ^ x.length)
      _ = (2 : ℝ)⁻¹ ^ p.length + ∑ w ∈ T, (2 : ℝ)⁻¹ ^ w.length := Finset.sum_insert hpT
      _ = (∑ w ∈ T, (2 : ℝ)⁻¹ ^ w.length) + (2 : ℝ)⁻¹ ^ p.length := add_comm _ _
  rw [← hF_sum]
  exact hs.sum_le_tsum F (fun _ _ => by positivity)

/-- **Kraft's inequality** for a finite set of halting programs of a prefix-free method. -/
theorem IsPrefixFree.finsetSum_two_inv_pow_length_le_one {α : Type*} {M : DescriptionMethod α}
    (hM : M.IsPrefixFree) {S : Finset (List Bool)} (hS : (S : Set (List Bool)) ⊆ M.haltingSet) :
    ∑ w ∈ S, (2 : ℝ)⁻¹ ^ w.length ≤ 1 :=
  finsetSum_two_inv_pow_length_le_one_of_isPrefixFree (hM.anti hS)

/-- Summability of `2⁻¹ ^ |p|` over the halting domain of a prefix-free description method. -/
theorem IsPrefixFree.summable_two_inv_pow_length {α : Type*} {M : DescriptionMethod α}
    (hM : M.IsPrefixFree) :
    Summable fun p : M.haltingSet => (2 : ℝ)⁻¹ ^ (p : List Bool).length :=
  summable_two_inv_pow_length_of_isPrefixFree hM

/-- **Kraft's inequality** for the halting domain of a prefix-free description method. -/
theorem IsPrefixFree.tsum_two_inv_pow_length_le_one {α : Type*} {M : DescriptionMethod α}
    (hM : M.IsPrefixFree) :
    ∑' p : M.haltingSet, (2 : ℝ)⁻¹ ^ (p : List Bool).length ≤ 1 :=
  tsum_two_inv_pow_length_le_one_of_isPrefixFree hM

end DescriptionMethod

/-! ### Executable online binary Kraft–Chaitin allocator -/

/-- Dyadic weight `2⁻¹ ^ |w|` in `ℚ`. -/
@[expose] def wordWeight (w : List Bool) : ℚ := (2 : ℚ)⁻¹ ^ w.length

/-- Total dyadic weight of a list of words in `ℚ`. -/
@[expose] def listWeight (L : List (List Bool)) : ℚ := (L.map wordWeight).sum

@[simp]
theorem listWeight_nil : listWeight [] = 0 := rfl

@[simp]
theorem listWeight_cons (w : List Bool) (L : List (List Bool)) :
    listWeight (w :: L) = wordWeight w + listWeight L := rfl

@[simp]
theorem listWeight_append (L₁ L₂ : List (List Bool)) :
    listWeight (L₁ ++ L₂) = listWeight L₁ + listWeight L₂ := by
  simp [listWeight]

/-- Splits an available prefix `u` down by `d` bits, returning `(codeword, leftoverBlocks)` where
`codeword = u ++ 0^d` has length `|u| + d` and `leftoverBlocks` contains one fresh block of each
length `|u| + 1, ..., |u| + d`. -/
@[expose] def splitFrom : List Bool → ℕ → List Bool × List (List Bool)
  | u, 0 => (u, [])
  | u, d + 1 =>
    let res := splitFrom (u ++ [false]) d
    (res.1, (u ++ [true]) :: res.2)

private theorem splitFrom_fst (u : List Bool) (d : ℕ) :
    (splitFrom u d).1 = u ++ List.replicate d false := by
  induction d generalizing u with
  | zero => simp [splitFrom]
  | succ d ih =>
    simp [splitFrom, ih, List.replicate_succ, List.append_assoc]

@[simp]
private theorem length_splitFrom_fst (u : List Bool) (d : ℕ) :
    (splitFrom u d).1.length = u.length + d := by
  simp [splitFrom_fst]

private theorem mem_splitFrom_snd_iff {u w : List Bool} {d : ℕ} :
    w ∈ (splitFrom u d).2 ↔ ∃ k < d, w = u ++ List.replicate k false ++ [true] := by
  induction d generalizing u with
  | zero => simp [splitFrom]
  | succ d ih =>
    simp only [splitFrom, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨k, hk, h⟩)
      · exact ⟨0, Nat.zero_lt_succ d, by simp⟩
      · refine ⟨k + 1, Nat.succ_lt_succ hk, ?_⟩
        simpa [List.replicate_succ, List.append_assoc] using h
    · rintro ⟨k, hk, h⟩
      cases k with
      | zero =>
        left
        simpa using h
      | succ k =>
        right
        refine ⟨k, Nat.lt_of_succ_lt_succ hk, ?_⟩
        simpa [List.replicate_succ, List.append_assoc] using h

private theorem splitFrom_snd_eq (u : List Bool) (d : ℕ) :
    (splitFrom u d).2 = (List.range d).map fun k => u ++ List.replicate k false ++ [true] := by
  induction d generalizing u with
  | zero => rfl
  | succ d ih =>
    rw [splitFrom, ih, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp [List.replicate_succ, List.append_assoc]

private theorem prefix_splitFrom_fst (u : List Bool) (d : ℕ) : u <+: (splitFrom u d).1 := by
  rw [splitFrom_fst]
  exact List.prefix_append _ _

private theorem prefix_of_mem_splitFrom_snd {u w : List Bool} {d : ℕ} (hw : w ∈ (splitFrom u d).2) :
    u <+: w := by
  obtain ⟨k, _, rfl⟩ := mem_splitFrom_snd_iff.mp hw
  rw [List.append_assoc]
  exact List.prefix_append _ _

private theorem length_mem_splitFrom_snd {u w : List Bool} {d : ℕ} (hw : w ∈ (splitFrom u d).2) :
    u.length < w.length ∧ w.length ≤ u.length + d := by
  obtain ⟨k, hk, rfl⟩ := mem_splitFrom_snd_iff.mp hw
  simp only [List.length_append, List.length_replicate, List.length_singleton]
  omega

private theorem nodup_map_length_splitFrom_snd (u : List Bool) (d : ℕ) :
    ((splitFrom u d).2.map List.length).Nodup := by
  induction d generalizing u with
  | zero => simp [splitFrom]
  | succ d ih =>
    simp only [splitFrom, List.map_cons, List.nodup_cons]
    refine ⟨fun h => ?_, ih (u ++ [false])⟩
    obtain ⟨w, hw, hlen⟩ := List.mem_map.mp h
    have hlt := (length_mem_splitFrom_snd hw).1
    simp only [List.length_append, List.length_singleton] at hlt hlen
    omega

private theorem pairwise_prefixDisjoint_splitFrom (u : List Bool) (d : ℕ) :
    ((splitFrom u d).1 :: (splitFrom u d).2).Pairwise PrefixDisjoint := by
  induction d generalizing u with
  | zero => simp [splitFrom]
  | succ d ih =>
    have ih' := ih (u ++ [false])
    simp only [splitFrom, List.pairwise_cons] at ih' ⊢
    refine ⟨fun w hw => ?_, fun w hw => ?_, ih'.2⟩
    · rcases List.mem_cons.mp hw with rfl | hw'
      · exact (prefixDisjoint_append_false_true u).of_prefix_left
          (prefix_splitFrom_fst (u ++ [false]) d)
      · exact ih'.1 w hw'
    · exact ((prefixDisjoint_append_false_true u).of_prefix_left
        (prefix_of_mem_splitFrom_snd hw)).symm

private theorem weight_splitFrom (u : List Bool) (d : ℕ) :
    wordWeight (splitFrom u d).1 + listWeight (splitFrom u d).2 = wordWeight u := by
  induction d generalizing u with
  | zero => simp [splitFrom]
  | succ d ih =>
    have ih' := ih (u ++ [false])
    simp only [splitFrom, listWeight_cons]
    have hhalves : wordWeight (u ++ [false]) + wordWeight (u ++ [true]) = wordWeight u := by
      simp only [wordWeight, List.length_append, List.length_singleton, pow_succ]
      ring
    linarith

/-- `List.replicate` on `Bool` is primitive recursive. -/
theorem primrec_list_replicate_bool :
    Primrec₂ (fun (n : ℕ) (b : Bool) => List.replicate n b) :=
  Primrec₂.mk <| (Primrec.list_map (Primrec.list_range.comp Primrec.fst)
    (Primrec.snd.comp Primrec.fst).to₂).of_eq fun ⟨n, b⟩ => by simp [List.map_const']

private theorem primrec₂_splitFrom : Primrec₂ splitFrom := by
  have h1 : Primrec₂ fun (u : List Bool) (d : ℕ) => u ++ List.replicate d false :=
    Primrec₂.mk <| Primrec.list_append.comp Primrec.fst
      (primrec_list_replicate_bool.comp Primrec.snd (Primrec.const false))
  have h2 : Primrec₂ fun (u : List Bool) (d : ℕ) =>
      (List.range d).map fun k => u ++ List.replicate k false ++ [true] := by
    have hel : Primrec₂ fun (ud : List Bool × ℕ) (k : ℕ) =>
        ud.1 ++ List.replicate k false ++ [true] :=
      Primrec₂.mk <| Primrec.list_append.comp
        (Primrec.list_append.comp (Primrec.fst.comp Primrec.fst)
          (primrec_list_replicate_bool.comp Primrec.snd (Primrec.const false)))
        (Primrec.const [true])
    exact Primrec₂.mk <| Primrec.list_map (Primrec.list_range.comp Primrec.snd) hel
  refine (Primrec.pair (h1.comp Primrec.fst Primrec.snd)
    (h2.comp Primrec.fst Primrec.snd)).to₂.of_eq fun u d => ?_
  ext <;> simp [splitFrom_fst, splitFrom_snd_eq]

/-- Finds the largest length at most `ℓ` among the available blocks, if any exists. -/
@[expose] def bestLenLe? (ℓ : ℕ) : List (List Bool) → Option ℕ
  | [] => Option.none
  | u :: rest =>
    if u.length ≤ ℓ then
      match bestLenLe? ℓ rest with
      | Option.none => some u.length
      | some b => some (max u.length b)
    else bestLenLe? ℓ rest

private theorem bestLenLe?_eq_none_iff {ℓ : ℕ} {avail : List (List Bool)} :
    bestLenLe? ℓ avail = Option.none ↔ ∀ u ∈ avail, ℓ < u.length := by
  induction avail with
  | nil => simp [bestLenLe?]
  | cons u rest ih =>
    simp only [bestLenLe?, List.mem_cons, forall_eq_or_imp]
    by_cases h : u.length ≤ ℓ
    · simp only [h, ↓reduceIte]
      cases hrest : bestLenLe? ℓ rest with
      | none => simp [Nat.not_lt_of_ge h]
      | some b => simp [Nat.not_lt_of_ge h]
    · simp [h, ih, Nat.lt_of_not_ge h]

private theorem bestLenLe?_eq_some {ℓ b : ℕ} {avail : List (List Bool)}
    (hb : bestLenLe? ℓ avail = some b) :
    b ≤ ℓ ∧ (∃ u ∈ avail, u.length = b) ∧ ∀ v ∈ avail, v.length ≤ ℓ → v.length ≤ b := by
  induction avail generalizing b with
  | nil => simp [bestLenLe?] at hb
  | cons u rest ih =>
    simp only [bestLenLe?] at hb
    by_cases h : u.length ≤ ℓ
    · simp only [h, ↓reduceIte] at hb
      cases hrest : bestLenLe? ℓ rest with
      | none =>
        rw [hrest] at hb
        simp only [Option.some.injEq] at hb
        subst hb
        have hnone := bestLenLe?_eq_none_iff.mp hrest
        refine ⟨h, ⟨u, List.mem_cons_self, rfl⟩, fun v hv hvle => ?_⟩
        rcases List.mem_cons.mp hv with rfl | hv'
        · exact le_rfl
        · exact absurd hvle (Nat.not_le_of_gt (hnone v hv'))
      | some b' =>
        rw [hrest] at hb
        simp only [Option.some.injEq] at hb
        obtain ⟨hb'le, ⟨w, hw, hwlen⟩, hmax⟩ := ih hrest
        subst hb
        refine ⟨max_le h hb'le, ?_, fun v hv hvle => ?_⟩
        · rcases le_total u.length b' with hle | hle
          · exact ⟨w, List.mem_cons_of_mem u hw, by rw [hwlen, max_eq_right hle]⟩
          · exact ⟨u, List.mem_cons_self, by rw [max_eq_left hle]⟩
        · rcases List.mem_cons.mp hv with rfl | hv'
          · exact le_max_left _ _
          · exact (hmax v hv' hvle).trans (le_max_right _ _)
    · simp only [h, ↓reduceIte] at hb
      obtain ⟨hble, ⟨w, hw, hwlen⟩, hmax⟩ := ih hb
      refine ⟨hble, ⟨w, List.mem_cons_of_mem u hw, hwlen⟩, fun v hv hvle => ?_⟩
      rcases List.mem_cons.mp hv with rfl | hv'
      · exact absurd hvle h
      · exact hmax v hv' hvle

private theorem primrec₂_bestLenLe? : Primrec₂ bestLenLe? := by
  have hh : Primrec₂ (fun (ℓL : ℕ × List (List Bool)) (p : List Bool × Option ℕ) =>
      if p.1.length ≤ ℓL.1 then
        match p.2 with
        | Option.none => some p.1.length
        | some b => some (max p.1.length b)
      else p.2) := by
    have hsome : Primrec fun arg : (ℕ × List (List Bool)) × (List Bool × Option ℕ) =>
        match arg.2.2 with
        | Option.none => some arg.2.1.length
        | some b => some (max arg.2.1.length b) := by
      have hmax_arm : Primrec₂ fun (arg : (ℕ × List (List Bool)) × (List Bool × Option ℕ))
          (b : ℕ) => some (max arg.2.1.length b) :=
        Primrec₂.mk <| Primrec.option_some.comp <|
          Primrec.nat_max.comp
            (Primrec.list_length.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
            Primrec.snd
      refine (Primrec.option_casesOn (Primrec.snd.comp Primrec.snd)
        (Primrec.option_some.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)))
        hmax_arm).of_eq fun arg => ?_
      cases arg.2.2 <;> rfl
    refine Primrec₂.mk <| (Primrec.ite
      (PrimrecRel.comp Primrec.nat_le
        (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.fst.comp Primrec.fst))
      hsome (Primrec.snd.comp Primrec.snd)).of_eq fun _ => rfl
  refine (Primrec.list_foldr Primrec.snd (Primrec.const Option.none) hh).to₂.of_eq fun ℓ avail => ?_
  induction avail with
  | nil => rfl
  | cons u rest ih =>
    simp only [bestLenLe?, List.foldr_cons]
    rw [ih]

/-- Splits the first block in `avail` of length `b` down to length `ℓ`. -/
@[expose] def splitAtLen (ℓ b : ℕ) : List (List Bool) → List (List Bool) × Option (List Bool)
  | [] => ([], Option.none)
  | u :: rest =>
    if u.length = b then
      let res := splitFrom u (ℓ - u.length)
      (rest ++ res.2, some res.1)
    else
      let next := splitAtLen ℓ b rest
      (u :: next.1, next.2)

private theorem primrec₂_splitAtLen :
    Primrec₂ fun (lb : ℕ × ℕ) (avail : List (List Bool)) => splitAtLen lb.1 lb.2 avail := by
  have hh : Primrec₂ fun (lb : ℕ × ℕ)
      (p : List Bool × List (List Bool) × (List (List Bool) × Option (List Bool))) =>
      if p.1.length = lb.2 then
        let res := splitFrom p.1 (lb.1 - p.1.length)
        (p.2.1 ++ res.2, some res.1)
      else (p.1 :: p.2.2.1, p.2.2.2) := by
    have hsplit : Primrec fun arg :
        (ℕ × ℕ) × (List Bool × List (List Bool) × (List (List Bool) × Option (List Bool))) =>
        splitFrom arg.2.1 (arg.1.1 - arg.2.1.length) :=
      primrec₂_splitFrom.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.fst)
          (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)))
    have hbranch1 : Primrec fun arg :
        (ℕ × ℕ) × (List Bool × List (List Bool) × (List (List Bool) × Option (List Bool))) =>
        (arg.2.2.1 ++ (splitFrom arg.2.1 (arg.1.1 - arg.2.1.length)).2,
          some (splitFrom arg.2.1 (arg.1.1 - arg.2.1.length)).1) := Primrec.pair
      (Primrec.list_append.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.snd.comp hsplit))
      (Primrec.option_some.comp (Primrec.fst.comp hsplit))
    have hbranch2 : Primrec fun arg :
        (ℕ × ℕ) × (List Bool × List (List Bool) × (List (List Bool) × Option (List Bool))) =>
        (arg.2.1 :: arg.2.2.2.1, arg.2.2.2.2) := Primrec.pair
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    exact Primrec₂.mk <| (Primrec.ite
      (Primrec.eq.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.fst))
      hbranch1 hbranch2).of_eq fun _ => rfl
  refine (Primrec.list_rec Primrec.snd (Primrec.const ([], Option.none))
      (hh.comp₂ (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right)).to₂.of_eq fun lb avail => ?_
  induction avail with
  | nil => rfl
  | cons u rest ih =>
    rw [splitAtLen, ← ih]

private theorem splitAtLen_spec {ℓ b : ℕ} {avail : List (List Bool)}
    (hpair : avail.Pairwise PrefixDisjoint)
    (hnodup : (avail.map List.length).Nodup)
    (hble : b ≤ ℓ)
    (hex : ∃ u ∈ avail, u.length = b)
    (hmax : ∀ v ∈ avail, v.length ≤ ℓ → v.length ≤ b) :
    ∃ code,
      (splitAtLen ℓ b avail).2 = some code ∧
      code.length = ℓ ∧
      (code :: (splitAtLen ℓ b avail).1).Pairwise PrefixDisjoint ∧
      ((splitAtLen ℓ b avail).1.map List.length).Nodup ∧
      listWeight (splitAtLen ℓ b avail).1 + wordWeight code = listWeight avail ∧
      (∀ x ∈ code :: (splitAtLen ℓ b avail).1, ∃ u ∈ avail, u <+: x) ∧
      (∀ x ∈ (splitAtLen ℓ b avail).1, x ∈ avail ∨ (b < x.length ∧ x.length ≤ ℓ)) := by
  induction avail with
  | nil =>
    obtain ⟨_, hmem, _⟩ := hex
    simp at hmem
  | cons u rest ih =>
    simp only [splitAtLen]
    by_cases hu : u.length = b
    · subst hu
      simp only [↓reduceIte]
      set res := splitFrom u (ℓ - u.length)
      refine ⟨res.1, by simp [res], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [res]
        omega
      · have hp_rest : rest.Pairwise PrefixDisjoint := (List.pairwise_cons.mp hpair).2
        have hp_u_rest : ∀ v ∈ rest, PrefixDisjoint u v := (List.pairwise_cons.mp hpair).1
        have hp_res := pairwise_prefixDisjoint_splitFrom u (ℓ - u.length)
        have hp_split_rest : ∀ x ∈ res.1 :: res.2, ∀ v ∈ rest, PrefixDisjoint x v := by
          intro x hx v hv
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact (hp_u_rest v hv).of_prefix_left (prefix_splitFrom_fst u _)
          · exact (hp_u_rest v hv).of_prefix_left (prefix_of_mem_splitFrom_snd hx')
        rw [List.pairwise_cons]
        refine ⟨fun v hv => ?_,
          List.pairwise_append.mpr ⟨hp_rest, (List.pairwise_cons.mp hp_res).2,
            fun v hv w hw => (hp_split_rest w (List.mem_cons_of_mem _ hw) v hv).symm⟩⟩
        rcases List.mem_append.mp hv with hv_rest | hv_res
        · exact hp_split_rest res.1 List.mem_cons_self v hv_rest
        · exact (List.pairwise_cons.mp hp_res).1 v hv_res
      · have hn_rest : (rest.map List.length).Nodup :=
          (List.nodup_cons.mp (by simpa using hnodup)).2
        have hdisj : ∀ a ∈ rest.map List.length, ∀ c ∈ res.2.map List.length, a ≠ c := by
          intro a ha c hc heq
          subst heq
          obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
          obtain ⟨w, hw, hvw⟩ := List.mem_map.mp hc
          have hw_bounds := length_mem_splitFrom_snd hw
          have hv_max := hmax v (List.mem_cons_of_mem u hv) (by omega)
          omega
        simp only [List.map_append]
        exact List.nodup_append.mpr ⟨hn_rest, nodup_map_length_splitFrom_snd u _, hdisj⟩
      · have hw := weight_splitFrom u (ℓ - u.length)
        simp only [listWeight_cons, listWeight_append]
        linarith
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact ⟨u, List.mem_cons_self, prefix_splitFrom_fst u _⟩
        · rcases List.mem_append.mp hx' with hx_rest | hx_res
          · exact ⟨x, List.mem_cons_of_mem u hx_rest, List.prefix_rfl⟩
          · exact ⟨u, List.mem_cons_self, prefix_of_mem_splitFrom_snd hx_res⟩
      · intro x hx
        rcases List.mem_append.mp hx with hx_rest | hx_res
        · exact Or.inl (List.mem_cons_of_mem u hx_rest)
        · have hb := length_mem_splitFrom_snd hx_res
          exact Or.inr ⟨hb.1, by omega⟩
    · simp only [hu, ↓reduceIte]
      have hpair_rest : rest.Pairwise PrefixDisjoint := (List.pairwise_cons.mp hpair).2
      have hnodup_rest : (rest.map List.length).Nodup :=
          (List.nodup_cons.mp (by simpa using hnodup)).2
      have hex_rest : ∃ w ∈ rest, w.length = b := by
        obtain ⟨w, hw, hwb⟩ := hex
        rcases List.mem_cons.mp hw with rfl | hw'
        · exact absurd hwb hu
        · exact ⟨w, hw', hwb⟩
      have hmax_rest : ∀ v ∈ rest, v.length ≤ ℓ → v.length ≤ b :=
        fun v hv => hmax v (List.mem_cons_of_mem u hv)
      obtain ⟨code, hcode, hlen, hp', hn', hw', hext, hmem'⟩ :=
        ih hpair_rest hnodup_rest hex_rest hmax_rest
      have hp_u : ∀ x ∈ code :: (splitAtLen ℓ b rest).1, PrefixDisjoint u x := by
        intro x hx
        obtain ⟨w, hw, hwx⟩ := hext x hx
        exact ((List.pairwise_cons.mp hpair).1 w hw).symm.of_prefix_left hwx |>.symm
      refine ⟨code, hcode, hlen, ?_, ?_, ?_, ?_, ?_⟩
      · exact (List.pairwise_cons.mpr ⟨hp_u, hp'⟩).perm (.swap _ _ _) PrefixDisjoint.symm
      · simp only [List.map_cons, List.nodup_cons]
        refine ⟨fun h => ?_, hn'⟩
        obtain ⟨x, hx, hxu⟩ := List.mem_map.mp h
        rcases hmem' x hx with hx_rest | hbounds
        · have hu_not := (List.nodup_cons.mp (by rw [← List.map_cons]; exact hnodup)).1
          exact hu_not (List.mem_map.mpr ⟨x, hx_rest, hxu⟩)
        · have hu_max := hmax u List.mem_cons_self (by omega)
          omega
      · simp only [listWeight_cons] at hw' ⊢
        linarith
      · intro x hx
        by_cases hxu : x = u
        · exact ⟨u, List.mem_cons_self, hxu ▸ List.prefix_rfl⟩
        · obtain ⟨w, hw, hwx⟩ := hext x (by simpa [hxu] using hx)
          exact ⟨w, List.mem_cons_of_mem u hw, hwx⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact Or.inl List.mem_cons_self
        · exact (hmem' x hx').imp_left (List.mem_cons_of_mem u)

private theorem two_pow_sum_range_lt (m : ℕ) : ∑ k ∈ Finset.range m, 2 ^ k < 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

private theorem inv_two_pow_mul_two_pow {k M : ℕ} (hk : k ≤ M) :
    (2 : ℚ)⁻¹ ^ k * (2 : ℚ) ^ M = ((2 ^ (M - k) : ℕ) : ℚ) := by
  have hM : k + (M - k) = M := Nat.add_sub_of_le hk
  conv_lhs => rw [← hM, pow_add, ← mul_assoc, inv_pow, inv_mul_cancel₀ (by positivity), one_mul]
  push_cast
  rfl

private theorem eq_of_length_eq_of_nodup_map {L : List (List Bool)}
    (h : (L.map List.length).Nodup) {u v : List Bool} (hu : u ∈ L) (hv : v ∈ L)
    (huv : u.length = v.length) : u = v := by
  induction L with
  | nil => simp at hu
  | cons a rest ih =>
    simp only [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp hu with rfl | hu' <;> rcases List.mem_cons.mp hv with rfl | hv'
    · rfl
    · exact absurd (List.mem_map.mpr ⟨v, hv', huv.symm⟩) h.1
    · exact absurd (List.mem_map.mpr ⟨u, hu', huv⟩) h.1
    · exact ih h.2 hu' hv'

private theorem foldr_max_bounds (L : List (List Bool)) (init : ℕ) :
    (∀ u ∈ L, u.length ≤ L.foldr (fun u m => max u.length m) init) ∧
      init ≤ L.foldr (fun u m => max u.length m) init := by
  induction L with
  | nil => simp
  | cons a rest ih =>
    simp only [List.foldr_cons]
    refine ⟨fun u hu => ?_, ih.2.trans (le_max_right _ _)⟩
    rcases List.mem_cons.mp hu with rfl | hu'
    · exact le_max_left _ _
    · exact (ih.1 u hu').trans (le_max_right _ _)

private theorem listWeight_mul_two_pow {L : List (List Bool)} {M : ℕ}
    (hM : ∀ u ∈ L, u.length ≤ M) :
    listWeight L * (2 : ℚ) ^ M = (L.map fun u => ((2 ^ (M - u.length) : ℕ) : ℚ)).sum := by
  induction L with
  | nil => simp [listWeight]
  | cons a rest ih =>
    simp only [listWeight_cons, add_mul, List.map_cons, List.sum_cons]
    rw [wordWeight, inv_two_pow_mul_two_pow (hM a List.mem_cons_self),
      ih (fun u hu => hM u (List.mem_cons_of_mem a hu))]

/-- If `avail` has distinct block lengths and total dyadic weight at least `2⁻¹ ^ ℓ`, then at least
one available block has length at most `ℓ`. -/
private theorem exists_length_le_of_inv_pow_le_listWeight {avail : List (List Bool)} {ℓ : ℕ}
    (hnodup : (avail.map List.length).Nodup) (hle : (2 : ℚ)⁻¹ ^ ℓ ≤ listWeight avail) :
    (bestLenLe? ℓ avail).isSome := by
  by_contra hnone_isSome
  have hnone : bestLenLe? ℓ avail = Option.none := Option.not_isSome_iff_eq_none.mp hnone_isSome
  have hgt : ∀ u ∈ avail, ℓ < u.length := bestLenLe?_eq_none_iff.mp hnone
  let M : ℕ := avail.foldr (fun u m => max u.length m) (ℓ + 1)
  have hM_ge : ∀ u ∈ avail, u.length ≤ M := (foldr_max_bounds avail (ℓ + 1)).1
  have hM_gt : ℓ < M := Nat.lt_of_succ_le (foldr_max_bounds avail (ℓ + 1)).2
  have hnodup_avail : avail.Nodup := List.Nodup.of_map List.length hnodup
  have hinj : Set.InjOn (fun u : List Bool => M - u.length) (avail.toFinset : Set (List Bool)) := by
    intro u hu v hv huv
    have hu' := List.mem_toFinset.mp (Finset.mem_coe.mp hu)
    have hv' := List.mem_toFinset.mp (Finset.mem_coe.mp hv)
    have hlu := hM_ge u hu'
    have hlv := hM_ge v hv'
    dsimp only at huv
    exact eq_of_length_eq_of_nodup_map hnodup hu' hv' (by omega)
  have hnat_sum : ∑ u ∈ avail.toFinset, 2 ^ (M - u.length) < 2 ^ (M - ℓ) := by
    have himg_sub : avail.toFinset.image (fun u => M - u.length) ⊆ Finset.range (M - ℓ) := by
      intro k hk
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hk
      have hu' := List.mem_toFinset.mp hu
      have h1 := hgt u hu'
      have h2 := hM_ge u hu'
      exact Finset.mem_range.mpr (by omega)
    calc ∑ u ∈ avail.toFinset, 2 ^ (M - u.length)
      _ = ∑ k ∈ avail.toFinset.image (fun u => M - u.length), 2 ^ k := by
          rw [Finset.sum_image (fun u hu v hv => hinj hu hv)]
      _ ≤ ∑ k ∈ Finset.range (M - ℓ), 2 ^ k := Finset.sum_le_sum_of_subset himg_sub
      _ < 2 ^ (M - ℓ) := two_pow_sum_range_lt (M - ℓ)
  have hscaled_avail :
      listWeight avail * (2 : ℚ) ^ M =
        ((∑ u ∈ avail.toFinset, 2 ^ (M - u.length) : ℕ) : ℚ) := by
    rw [listWeight_mul_two_pow hM_ge, Nat.cast_sum,
      ← List.sum_toFinset (fun u : List Bool => ((2 ^ (M - u.length) : ℕ) : ℚ)) hnodup_avail]
  have hscaled_lt : listWeight avail * (2 : ℚ) ^ M < (2 : ℚ)⁻¹ ^ ℓ * (2 : ℚ) ^ M := by
    rw [hscaled_avail, inv_two_pow_mul_two_pow hM_gt.le]
    exact_mod_cast hnat_sum
  have hpow_pos : (0 : ℚ) < (2 : ℚ) ^ M := by positivity
  exact absurd (lt_of_mul_lt_mul_right hscaled_lt hpow_pos.le) (not_lt.mpr hle)

/-- One online step of the Kraft–Chaitin allocator. -/
@[expose] def kcStep (avail : List (List Bool)) :
    Option ℕ → List (List Bool) × Option (List Bool)
  | Option.none => (avail, Option.none)
  | some ℓ =>
    match bestLenLe? ℓ avail with
    | Option.none => (avail, Option.none)
    | some b => splitAtLen ℓ b avail

/-- One online step of the Kraft–Chaitin allocator is primitive recursive. -/
theorem primrec₂_kcStep : Primrec₂ kcStep := by
  have hsome : Primrec₂ fun (avail : List (List Bool)) (ℓ : ℕ) =>
      match bestLenLe? ℓ avail with
      | Option.none => (avail, Option.none)
      | some b => splitAtLen ℓ b avail := by
    have hbest : Primrec fun arg : List (List Bool) × ℕ => bestLenLe? arg.2 arg.1 :=
      primrec₂_bestLenLe?.comp Primrec.snd Primrec.fst
    have hsplit : Primrec₂ fun (arg : List (List Bool) × ℕ) (b : ℕ) =>
        splitAtLen arg.2 b arg.1 :=
      Primrec₂.mk <| primrec₂_splitAtLen.comp
        (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)
        (Primrec.fst.comp Primrec.fst)
    refine Primrec₂.mk <| (Primrec.option_casesOn hbest
      (Primrec.pair Primrec.fst (Primrec.const Option.none)) hsplit).of_eq fun arg => ?_
    cases bestLenLe? arg.2 arg.1 <;> rfl
  refine Primrec₂.mk <| (Primrec.option_casesOn Primrec.snd
    (Primrec.pair Primrec.fst (Primrec.const Option.none))
    (hsome.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).of_eq fun arg => ?_
  cases arg.2 <;> rfl

/-- Loop invariant for the online Kraft–Chaitin allocator: remaining free intervals `avail` and
allocated codewords `allocs` are collectively pairwise prefix-disjoint, all available intervals have
distinct lengths, and total dyadic weight is conserved to `1`. -/
private def KCInv (avail allocs : List (List Bool)) : Prop :=
  (avail ++ allocs).Pairwise PrefixDisjoint ∧
  (avail.map List.length).Nodup ∧
  listWeight avail + listWeight allocs = 1

private theorem kcInv_init : KCInv [[]] [] := by
  simp [KCInv, wordWeight]

private theorem kcStep_some_spec {avail allocs : List (List Bool)} {ℓ : ℕ}
    (hinv : KCInv avail allocs) (hsum : listWeight allocs + (2 : ℚ)⁻¹ ^ ℓ ≤ 1) :
    ∃ avail' code,
      kcStep avail (some ℓ) = (avail', some code) ∧
      code.length = ℓ ∧
      KCInv avail' (code :: allocs) := by
  rcases hinv with ⟨hpair_all, hnodup, hweight⟩
  have hle_avail : (2 : ℚ)⁻¹ ^ ℓ ≤ listWeight avail := by linarith
  have hisSome := exists_length_le_of_inv_pow_le_listWeight hnodup hle_avail
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hisSome
  obtain ⟨hble, hex, hmax⟩ := bestLenLe?_eq_some hb
  have hpair_avail : avail.Pairwise PrefixDisjoint := (List.pairwise_append.mp hpair_all).1
  have hpair_cross : ∀ v ∈ avail, ∀ y ∈ allocs, PrefixDisjoint v y :=
    (List.pairwise_append.mp hpair_all).2.2
  have hpair_allocs : allocs.Pairwise PrefixDisjoint := (List.pairwise_append.mp hpair_all).2.1
  obtain ⟨code, hcode, hlen, hpair', hnodup', hweight', hext, _⟩ :=
    splitAtLen_spec hpair_avail hnodup hble hex hmax
  refine ⟨(splitAtLen ℓ b avail).1, code, ?_, hlen, ?_, hnodup', ?_⟩
  · simp [kcStep, hb, Prod.ext_iff, hcode]
  · have hc_pair : (code :: allocs).Pairwise PrefixDisjoint := by
      refine List.pairwise_cons.mpr ⟨fun y hy => ?_, hpair_allocs⟩
      obtain ⟨u, hu, huc⟩ := hext code List.mem_cons_self
      exact (hpair_cross u hu y hy).of_prefix_left huc
    have ha_pair : (splitAtLen ℓ b avail).1.Pairwise PrefixDisjoint :=
      (List.pairwise_cons.mp hpair').2
    have hcross' : ∀ v ∈ (splitAtLen ℓ b avail).1, ∀ z ∈ code :: allocs, PrefixDisjoint v z := by
      intro v hv z hz
      rcases List.mem_cons.mp hz with rfl | hz'
      · exact ((List.pairwise_cons.mp hpair').1 v hv).symm
      · obtain ⟨u, hu, huv⟩ := hext v (List.mem_cons_of_mem _ hv)
        exact (hpair_cross u hu z hz').of_prefix_left huv
    exact List.pairwise_append.mpr ⟨ha_pair, hc_pair, hcross'⟩
  · simp only [listWeight_cons]
    linarith

/-- Executable finite Kraft–Chaitin allocator taking a list of target lengths. -/
@[expose] def kcAllocListAux (avail acc : List (List Bool)) :
    List ℕ → Option (List (List Bool))
  | [] => some acc.reverse
  | ℓ :: reqs =>
    match kcStep avail (some ℓ) with
    | (_, Option.none) => Option.none
    | (avail', some code) => kcAllocListAux avail' (code :: acc) reqs

/-- Allocates prefix-free codewords of the specified lengths whenever the Kraft sum is at most
`1`. -/
@[expose] def kcAllocList (reqs : List ℕ) : Option (List (List Bool)) :=
  kcAllocListAux [[]] [] reqs

private theorem kcAllocListAux_eq_some_of_inv {avail acc : List (List Bool)} {reqs : List ℕ}
    (hinv : KCInv avail acc)
    (hsum : listWeight acc + (reqs.map fun ℓ => (2 : ℚ)⁻¹ ^ ℓ).sum ≤ 1) :
    ∃ codes,
      kcAllocListAux avail acc reqs = some codes ∧
      codes.map List.length = acc.reverse.map List.length ++ reqs ∧
      codes.Pairwise PrefixDisjoint := by
  induction reqs generalizing avail acc with
  | nil =>
    refine ⟨acc.reverse, rfl, by simp, List.pairwise_reverse.mpr ?_⟩
    exact (List.pairwise_append.mp hinv.1).2.1.imp fun h => h.symm
  | cons ℓ rest ih =>
    have hstep_sum : listWeight acc + (2 : ℚ)⁻¹ ^ ℓ ≤ 1 := by
      have hrest_nonneg : 0 ≤ (rest.map fun k => (2 : ℚ)⁻¹ ^ k).sum :=
        List.sum_nonneg fun x hx => by
          obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
          positivity
      simp only [List.map_cons, List.sum_cons] at hsum
      linarith
    obtain ⟨avail', code, hkc, hlen, hinv'⟩ := kcStep_some_spec hinv hstep_sum
    have hsum' : listWeight (code :: acc) + (rest.map fun k => (2 : ℚ)⁻¹ ^ k).sum ≤ 1 := by
      simp only [listWeight_cons, wordWeight, hlen]
      simp only [List.map_cons, List.sum_cons] at hsum
      linarith
    obtain ⟨codes, hcodes, hmap, hpair⟩ := ih hinv' hsum'
    refine ⟨codes, ?_, ?_, hpair⟩
    · simp only [kcAllocListAux, hkc]
      exact hcodes
    · simpa [hlen] using hmap

/-- Finite executable Kraft–Chaitin correctness: any list of lengths `reqs` with dyadic Kraft sum
at most `1` is realized by a pairwise prefix-disjoint list of codewords of exact lengths `reqs`. -/
theorem kcAllocList_eq_some_of_sum_le_one {reqs : List ℕ}
    (hsum : (reqs.map fun ℓ => (2 : ℚ)⁻¹ ^ ℓ).sum ≤ 1) :
    ∃ codes,
      kcAllocList reqs = some codes ∧
      codes.map List.length = reqs ∧
      codes.Pairwise PrefixDisjoint := by
  have hsum' : listWeight [] + (reqs.map fun ℓ => (2 : ℚ)⁻¹ ^ ℓ).sum ≤ 1 := by simpa using hsum
  obtain ⟨codes, hcodes, hmap, hpair⟩ := kcAllocListAux_eq_some_of_inv kcInv_init hsum'
  exact ⟨codes, hcodes, by simpa using hmap, hpair⟩

/-- Online Kraft–Chaitin trace on request stream `reqs : ℕ → Option ℕ`. -/
@[expose] def kcTrace (reqs : ℕ → Option ℕ) : ℕ → List (List Bool) × Option (List Bool)
  | 0 => ([[]], Option.none)
  | n + 1 => kcStep (kcTrace reqs n).1 (reqs n)

/-- The codeword assigned at step `n` by the online Kraft–Chaitin trace. -/
@[expose] def kcCode (reqs : ℕ → Option ℕ) (n : ℕ) : Option (List Bool) :=
  (kcTrace reqs (n + 1)).2

/-- Ghost list of codewords allocated by `kcTrace reqs` strictly before step `n`. -/
private def kcAllocs (reqs : ℕ → Option ℕ) : ℕ → List (List Bool)
  | 0 => []
  | n + 1 =>
    match kcCode reqs n with
    | Option.none => kcAllocs reqs n
    | some w => w :: kcAllocs reqs n

private theorem reqPrefix_eq_listWeight_allocs {reqs : ℕ → Option ℕ}
    (hbound : ∀ n : ℕ, ∑ i ∈ Finset.range n,
      (match reqs i with | Option.none => (0 : ℚ) | some ℓ => (2 : ℚ)⁻¹ ^ ℓ) ≤ 1) (n : ℕ) :
    KCInv (kcTrace reqs n).1 (kcAllocs reqs n) ∧
      listWeight (kcAllocs reqs n) = ∑ i ∈ Finset.range n,
        (match reqs i with | Option.none => (0 : ℚ) | some ℓ => (2 : ℚ)⁻¹ ^ ℓ) ∧
      ∀ i < n, ∀ ℓ, reqs i = some ℓ → ∃ w, kcCode reqs i = some w ∧ w.length = ℓ ∧
        w ∈ kcAllocs reqs n := by
  induction n with
  | zero =>
    refine ⟨kcInv_init, by simp [kcAllocs], fun i hi => by omega⟩
  | succ n ih =>
    obtain ⟨hinv, hweight, hprev⟩ := ih
    have hmem_mono : ∀ w ∈ kcAllocs reqs n, w ∈ kcAllocs reqs (n + 1) := by
      intro w hw
      simp only [kcAllocs]
      cases kcCode reqs n <;> simp [hw]
    cases hreq : reqs n with
    | none =>
      have hkc : kcCode reqs n = Option.none := by simp [kcCode, kcTrace, kcStep, hreq]
      refine ⟨?_, ?_, ?_⟩
      · simpa [kcTrace, kcStep, hreq, kcAllocs, hkc] using hinv
      · rw [kcAllocs, hkc, Finset.sum_range_succ, hreq]
        simpa using hweight
      · intro i hi ℓ hi_eq
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
        · obtain ⟨w, hw, hlen, hw_mem⟩ := hprev i hlt ℓ hi_eq
          exact ⟨w, hw, hlen, hmem_mono w hw_mem⟩
        · simp [hreq] at hi_eq
    | some ℓ =>
      have hstep_sum : listWeight (kcAllocs reqs n) + (2 : ℚ)⁻¹ ^ ℓ ≤ 1 := by
        have hb := hbound (n + 1)
        rw [Finset.sum_range_succ, hreq, ← hweight] at hb
        exact hb
      obtain ⟨avail', code, hkc, hlen, hinv'⟩ := kcStep_some_spec hinv hstep_sum
      have htrace_succ : kcTrace reqs (n + 1) = (avail', some code) := by
        simp only [kcTrace, hreq]
        exact hkc
      have hcode_n : kcCode reqs n = some code := by simp [kcCode, htrace_succ]
      have hallocs_succ : kcAllocs reqs (n + 1) = code :: kcAllocs reqs n := by
        simp [kcAllocs, hcode_n]
      refine ⟨?_, ?_, ?_⟩
      · simpa [htrace_succ, hallocs_succ] using hinv'
      · rw [hallocs_succ, listWeight_cons, wordWeight, hlen, Finset.sum_range_succ, hreq, hweight]
        ring
      · intro i hi ℓ' hi_eq
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
        · obtain ⟨w, hw, hlen', hw_mem⟩ := hprev i hlt ℓ' hi_eq
          exact ⟨w, hw, hlen', by rw [hallocs_succ]; exact List.mem_cons_of_mem _ hw_mem⟩
        · rw [hreq, Option.some.injEq] at hi_eq
          subst hi_eq
          exact ⟨code, hcode_n, hlen, by rw [hallocs_succ]; exact List.mem_cons_self⟩

/-- Every request `reqs i = some ℓ` in a stream with partial dyadic Kraft sums at most `1` is
allocated a codeword `kcCode reqs i = some w` of exact length `ℓ`. -/
theorem exists_kcCode_eq_some_of_sum_le_one {reqs : ℕ → Option ℕ}
    (hbound : ∀ n : ℕ, ∑ i ∈ Finset.range n,
      (match reqs i with | Option.none => (0 : ℚ) | some ℓ => (2 : ℚ)⁻¹ ^ ℓ) ≤ 1)
    {i ℓ : ℕ} (hi : reqs i = some ℓ) :
    ∃ w, kcCode reqs i = some w ∧ w.length = ℓ := by
  obtain ⟨w, hw, hlen, _⟩ :=
    (reqPrefix_eq_listWeight_allocs hbound (i + 1)).2.2 i (Nat.lt_succ_self i) ℓ hi
  exact ⟨w, hw, hlen⟩

/-- Distinct steps of `kcCode` produce prefix-disjoint codewords whenever partial dyadic Kraft
sums stay at most `1`. -/
theorem kcCode_prefixDisjoint_of_ne {reqs : ℕ → Option ℕ}
    (hbound : ∀ n : ℕ, ∑ i ∈ Finset.range n,
      (match reqs i with | Option.none => (0 : ℚ) | some ℓ => (2 : ℚ)⁻¹ ^ ℓ) ≤ 1)
    {i j : ℕ} (hne : i ≠ j) {p q : List Bool}
    (hi : kcCode reqs i = some p) (hj : kcCode reqs j = some q) :
    PrefixDisjoint p q := by
  wlog hlt : i < j generalizing i j p q
  · have hlt' : j < i := lt_of_le_of_ne (not_lt.mp hlt) hne.symm
    exact (this hne.symm hj hi hlt').symm
  have hcode_mem : ∀ k w, kcCode reqs k = some w → w ∈ kcAllocs reqs (k + 1) := by
    intro k w hk
    simp [kcAllocs, hk]
  have hmono : ∀ m n w, m ≤ n → w ∈ kcAllocs reqs m → w ∈ kcAllocs reqs n := by
    intro m n w hmn hw
    induction hmn with
    | refl => exact hw
    | step _ ih =>
      simp only [kcAllocs]
      cases kcCode reqs _ <;> simp [ih]
  have hp_mem : p ∈ kcAllocs reqs j := hmono (i + 1) j p hlt (hcode_mem i p hi)
  have hpair_succ : (kcAllocs reqs (j + 1)).Pairwise PrefixDisjoint :=
    (List.pairwise_append.mp (reqPrefix_eq_listWeight_allocs hbound (j + 1)).1.1).2.1
  have halloc_j : kcAllocs reqs (j + 1) = q :: kcAllocs reqs j := by simp [kcAllocs, hj]
  rw [halloc_j, List.pairwise_cons] at hpair_succ
  exact (hpair_succ.1 p hp_mem).symm

namespace DescriptionMethod

/-- Bounded-step evaluator searching the online Kraft–Chaitin code stream `req` for program `p`. -/
@[expose] def kcStreamEval {α : Type*} (req : ℕ → Option (ℕ × α)) (p : List Bool) : ℕ → Option α
  | 0 => Option.none
  | t + 1 =>
    match kcStreamEval req p t with
    | some x => some x
    | Option.none =>
      if kcCode (fun i => (req i).map Prod.fst) t = some p then (req t).map Prod.snd
      else Option.none

theorem kcStreamEval_mono {α : Type*} (req : ℕ → Option (ℕ × α)) (p : List Bool) :
    ∀ {m n : ℕ} {x : α}, m ≤ n → kcStreamEval req p m = some x → kcStreamEval req p n = some x := by
  intro m n x hmn hm
  induction hmn with
  | refl => exact hm
  | step _ ih =>
    simp only [kcStreamEval, ih]

theorem mem_kcStreamEval_iff {α : Type*} (req : ℕ → Option (ℕ × α))
    (hbound : ∀ n : ℕ, ∑ i ∈ Finset.range n,
      (match (req i).map Prod.fst with
      | Option.none => (0 : ℚ) | some ℓ => (2 : ℚ)⁻¹ ^ ℓ) ≤ 1)
    (p : List Bool) {t : ℕ} {x : α} :
    kcStreamEval req p t = some x ↔
      ∃ i < t, kcCode (fun j => (req j).map Prod.fst) i = some p ∧
        (req i).map Prod.snd = some x := by
  induction t generalizing x with
  | zero => simp [kcStreamEval]
  | succ t ih =>
    simp only [kcStreamEval]
    cases h : kcStreamEval req p t with
    | some y =>
      rw [Option.some.injEq]
      obtain ⟨i, hit, hcode, hval⟩ := (@ih y).mp h
      constructor
      · rintro rfl
        exact ⟨i, hit.trans (Nat.lt_succ_self t), hcode, hval⟩
      · rintro ⟨j, hjt, hjcode, hjval⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hjt with hjlt | rfl
        · have hy := ih.mpr ⟨j, hjlt, hjcode, hjval⟩
          rw [h] at hy
          exact Option.some.inj hy
        · exact absurd (kcCode_prefixDisjoint_of_ne hbound (by omega) hcode hjcode)
            (PrefixDisjoint.irrefl p)
    | none =>
      refine ⟨fun hx => ?_, fun ⟨i, hit, hcode, hval⟩ => ?_⟩
      · by_cases hkc : kcCode (fun i => (req i).map Prod.fst) t = some p
        · simp only [hkc, ↓reduceIte] at hx
          exact ⟨t, Nat.lt_succ_self t, hkc, hx⟩
        · simp [hkc] at hx
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hit with hilt | rfl
        · simpa [h] using ih.mpr ⟨i, hilt, hcode, hval⟩
        · simpa [hcode] using hval

/-- Joint computability of `kcStreamEval` across any uniformly computable family of request streams
`req : β → ℕ → Option (ℕ × α)`. -/
theorem computable_kcStreamEval {α β : Type*} [Primcodable α] [Primcodable β]
    {req : β → ℕ → Option (ℕ × α)} (hreq : Computable₂ req) :
    Computable₂ fun (bp : β × List Bool) (t : ℕ) => kcStreamEval (req bp.1) bp.2 t := by
  let reqs : β → ℕ → Option ℕ := fun b i => (req b i).map Prod.fst
  have hreqs : Computable₂ reqs :=
    Computable₂.mk <| (Computable.option_casesOn hreq (Computable.const Option.none)
      (Computable.option_some.comp (Computable.fst.comp Computable.snd)).to₂).of_eq fun arg => by
        dsimp only [reqs]
        cases req arg.1 arg.2 <;> rfl
  have htrace : Computable₂ fun b n => kcTrace (reqs b) n :=
    Computable₂.mk <| (Computable.nat_rec Computable.snd (Computable.const ([[]], Option.none))
      (primrec₂_kcStep.to_comp.comp
        (Computable.fst.comp (Computable.snd.comp Computable.snd))
        (hreqs.comp (Computable.fst.comp Computable.fst)
          (Computable.fst.comp Computable.snd))).to₂).of_eq fun ⟨b, n⟩ => by
      induction n with
      | zero => rfl
      | succ m ih => exact congrArg (fun st => kcStep st.1 (reqs b m)) ih
  have hkcCode : Computable₂ fun b i => kcCode (reqs b) i :=
    Computable.snd.comp (htrace.comp Computable.fst (Computable.succ.comp Computable.snd)) |>.to₂
  have hval : Computable₂ fun b i => (req b i).map Prod.snd :=
    Computable₂.mk <| (Computable.option_casesOn hreq (Computable.const Option.none)
      (Computable.option_some.comp (Computable.snd.comp Computable.snd)).to₂).of_eq
      fun arg => by dsimp only; cases req arg.1 arg.2 <;> rfl
  have helse : Computable fun arg : (β × List Bool) × (ℕ × Option α) =>
      bif decide (kcCode (reqs arg.1.1) arg.2.1 = some arg.1.2) then
        (req arg.1.1 arg.2.1).map Prod.snd else Option.none :=
    Computable.cond
      (Primrec.eq.decide.to_comp.comp
        (hkcCode.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd))
        (Computable.option_some.comp (Computable.snd.comp Computable.fst)))
      (hval.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd))
      (Computable.const Option.none)
  have hstep : Computable₂ fun (bpt : (β × List Bool) × ℕ) (a : ℕ × Option α) =>
      match a.2 with
      | some x => some x
      | Option.none =>
        bif decide (kcCode (reqs bpt.1.1) a.1 = some bpt.1.2) then (req bpt.1.1 a.1).map Prod.snd
        else Option.none :=
    (Computable.option_casesOn (Computable.snd.comp Computable.snd)
      (helse.comp (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd))
      (Computable.option_some.comp Computable.snd).to₂).of_eq fun arg => by
        rcases arg with ⟨⟨⟨_, _⟩, _⟩, ⟨_, _ | _⟩⟩ <;> rfl
  exact Computable₂.mk <| (Computable.nat_rec Computable.snd (Computable.const Option.none)
    hstep).of_eq fun ⟨⟨b, p⟩, n⟩ => by
      induction n with
      | zero => rfl
      | succ m ih =>
        dsimp only at ih ⊢
        rw [ih, kcStreamEval]
        cases kcStreamEval (req b) p m with
        | none => by_cases hkc : kcCode (reqs b) m = some p <;> simp [reqs, hkc]
        | some v => rfl

/-- Prefix-freeness of the halting domain of `Nat.rfindOpt (kcStreamEval req ·)` whenever partial
dyadic Kraft sums stay at most `1`. -/
theorem isPrefixFree_rfindOpt_kcStreamEval {α : Type*} (req : ℕ → Option (ℕ × α))
    (hbound : ∀ n : ℕ, ∑ i ∈ Finset.range n,
      (match (req i).map Prod.fst with
      | Option.none => (0 : ℚ) | some ℓ => (2 : ℚ)⁻¹ ^ ℓ) ≤ 1) :
    InformationTheory.IsPrefixFree {p | (Nat.rfindOpt (kcStreamEval req p)).Dom} := by
  intro p₁ h₁ p₂ h₂ hpref
  obtain ⟨x₁, hx₁⟩ := Part.dom_iff_mem.mp h₁
  obtain ⟨x₂, hx₂⟩ := Part.dom_iff_mem.mp h₂
  obtain ⟨t₁, ht₁⟩ := (Nat.rfindOpt_mono fun hmn => kcStreamEval_mono req p₁ hmn).mp hx₁
  obtain ⟨t₂, ht₂⟩ := (Nat.rfindOpt_mono fun hmn => kcStreamEval_mono req p₂ hmn).mp hx₂
  obtain ⟨i₁, -, hi₁, _⟩ := (mem_kcStreamEval_iff req hbound p₁).mp ht₁
  obtain ⟨i₂, -, hi₂, _⟩ := (mem_kcStreamEval_iff req hbound p₂).mp ht₂
  by_contra hne
  have hine : i₁ ≠ i₂ := by
    rintro rfl
    exact hne (Option.some.inj (hi₁.symm.trans hi₂))
  exact (kcCode_prefixDisjoint_of_ne hbound hine hi₁ hi₂).1 hpref

/-- **Kraft–Chaitin theorem** (finite-partial-sum form) [LiVitanyi2019,
ShenUspenskyVereshchagin2017]: every computable sequence of requests `(ℓ_i, y_i)` whose partial
Kraft sums stay at most `1` is realized by a prefix-free partial recursive `DescriptionMethod α`. -/
theorem kraftChaitin_of_sum_le_one {α : Type*} [Primcodable α] {req : ℕ → Option (ℕ × α)}
    (hreq : Computable req)
    (hbound : ∀ n : ℕ, ∑ i ∈ Finset.range n,
      (match req i with | Option.none => (0 : ℝ) | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ) ≤ 1) :
    ∃ M : DescriptionMethod α,
      M.IsPrefixFree ∧
      (∃ eval : List Bool →. α, Partrec eval ∧ ∀ p x, M.Produces p x ↔ x ∈ eval p) ∧
      ∀ i ℓ y, req i = some (ℓ, y) → ∃ p : List Bool, p.length = ℓ ∧ M.Produces p y := by
  have hbound_rat : ∀ n : ℕ, ∑ i ∈ Finset.range n,
      (match (req i).map Prod.fst with | Option.none => (0 : ℚ) | some ℓ => (2 : ℚ)⁻¹ ^ ℓ) ≤ 1 := by
    intro n
    let f : ℕ → ℚ := fun i =>
      match (req i).map Prod.fst with | Option.none => (0 : ℚ) | some ℓ => (2 : ℚ)⁻¹ ^ ℓ
    have hcast : ((∑ i ∈ Finset.range n, f i : ℚ) : ℝ) =
        ∑ i ∈ Finset.range n,
          (match req i with | Option.none => (0 : ℝ) | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ) :=
      (map_sum (Rat.castHom ℝ) _ _).trans <| Finset.sum_congr rfl fun i _ => by
        dsimp only [f]
        cases req i <;> simp
    exact_mod_cast (hcast ▸ hbound n)
  have hreq₂ : Computable₂ fun (_ : Unit) (i : ℕ) => req i :=
    Computable₂.mk <| hreq.comp Computable.snd
  have hstream : Computable₂ (kcStreamEval req) :=
    Computable₂.mk <| (computable_kcStreamEval hreq₂).comp
      (Computable.pair (Computable.const ()) Computable.fst) Computable.snd
  let eval : List Bool →. α := fun p => Nat.rfindOpt (kcStreamEval req p)
  have heval : Partrec eval := Partrec.rfindOpt hstream
  let M : DescriptionMethod α :=
    { run p := ⟨fun t => kcStreamEval req p t,
        fun t _ h => kcStreamEval_mono req p (Nat.le_succ t) h⟩ }
  have hprod : ∀ p x, M.Produces p x ↔ x ∈ eval p := by
    intro p x
    rw [produces_iff_exists_mem_runFor]
    exact (Nat.rfindOpt_mono fun {y m n} hmn hy => kcStreamEval_mono req p hmn hy).symm
  have hpf_dom := isPrefixFree_rfindOpt_kcStreamEval req hbound_rat
  have hpf : M.IsPrefixFree := by
    rintro p₁ ⟨x₁, h₁⟩ p₂ ⟨x₂, h₂⟩ hpref
    exact hpf_dom p₁ (Part.dom_iff_mem.mpr ⟨x₁, (hprod p₁ x₁).mp h₁⟩)
      p₂ (Part.dom_iff_mem.mpr ⟨x₂, (hprod p₂ x₂).mp h₂⟩) hpref
  refine ⟨M, hpf, ⟨eval, heval, hprod⟩, fun i ℓ y hiy => ?_⟩
  obtain ⟨w, hw, hlen⟩ :=
    exists_kcCode_eq_some_of_sum_le_one hbound_rat (i := i) (ℓ := ℓ) (by simp [hiy])
  refine ⟨w, hlen, produces_iff_exists_mem_runFor.mpr ⟨i + 1, ?_⟩⟩
  exact (mem_kcStreamEval_iff req hbound_rat w).mpr
    ⟨i, Nat.lt_succ_self i, hw, by simp [hiy]⟩

/-- **Kraft–Chaitin theorem** (`tsum` form) [LiVitanyi2019, ShenUspenskyVereshchagin2017]: every
computable sequence of requests `(ℓ_i, y_i)` whose Kraft sum `∑' i, 2⁻¹ ^ ℓ_i` is summable and
at most `1` is realized by a prefix-free partial recursive `DescriptionMethod α`. -/
theorem kraftChaitin {α : Type*} [Primcodable α] {req : ℕ → Option (ℕ × α)}
    (hreq : Computable req)
    (hsummable : Summable fun i : ℕ =>
      match req i with | Option.none => (0 : ℝ) | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ)
    (hbound : ∑' i : ℕ,
      (match req i with | Option.none => (0 : ℝ) | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ) ≤ 1) :
    ∃ M : DescriptionMethod α,
      M.IsPrefixFree ∧
      (∃ eval : List Bool →. α, Partrec eval ∧ ∀ p x, M.Produces p x ↔ x ∈ eval p) ∧
      ∀ i ℓ y, req i = some (ℓ, y) → ∃ p : List Bool, p.length = ℓ ∧ M.Produces p y := by
  refine kraftChaitin_of_sum_le_one hreq fun n => ?_
  refine (hsummable.sum_le_tsum (Finset.range n) fun i _ => ?_).trans hbound
  cases req i <;> positivity

/-- Prefix-free minorization form of the **Kraft–Chaitin theorem** (finite partial sums): any
computable request stream `(ℓ_i, y_i)` with partial Kraft sums at most `1` gives
`K_U(y_i) ≤ ℓ_i + c` for a uniform constant `c`. -/
theorem MinorizesPrefixPartrec.kraftChaitin_of_sum_le_one {α : Type*} [Primcodable α]
    {U : DescriptionMethod α} (hU : U.MinorizesPrefixPartrec) {req : ℕ → Option (ℕ × α)}
    (hreq : Computable req)
    (hbound : ∀ n : ℕ, ∑ i ∈ Finset.range n,
      (match req i with | Option.none => (0 : ℝ) | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ) ≤ 1) :
    ∃ c : ℕ, ∀ i ℓ y, req i = some (ℓ, y) → U.ecomplexity y ≤ ℓ + c := by
  obtain ⟨M, hpf, ⟨eval, heval, hprod⟩, hreal⟩ :=
    _root_.Cslib.Kolmogorov.DescriptionMethod.kraftChaitin_of_sum_le_one hreq hbound
  obtain ⟨c, hc⟩ := hU.exists_ecomplexity_le_of_partrec_eval hpf heval hprod
  refine ⟨c, fun i ℓ y hiy => ?_⟩
  obtain ⟨p, hlen, hp⟩ := hreal i ℓ y hiy
  calc U.ecomplexity y ≤ M.ecomplexity y + c := hc y
    _ ≤ (ℓ : ℕ∞) + c := by
      gcongr
      simpa [hlen] using M.ecomplexity_le_length hp

/-- Prefix-free minorization form of the **Kraft–Chaitin theorem** (`tsum` form). -/
theorem MinorizesPrefixPartrec.kraftChaitin {α : Type*} [Primcodable α]
    {U : DescriptionMethod α} (hU : U.MinorizesPrefixPartrec) {req : ℕ → Option (ℕ × α)}
    (hreq : Computable req)
    (hsummable : Summable fun i : ℕ =>
      match req i with | Option.none => (0 : ℝ) | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ)
    (hbound : ∑' i : ℕ,
      (match req i with | Option.none => (0 : ℝ) | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ) ≤ 1) :
    ∃ c : ℕ, ∀ i ℓ y, req i = some (ℓ, y) → U.ecomplexity y ≤ ℓ + c := by
  refine hU.kraftChaitin_of_sum_le_one hreq fun n => ?_
  refine (hsummable.sum_le_tsum (Finset.range n) fun i _ => ?_).trans hbound
  cases req i <;> positivity

end DescriptionMethod

end Cslib.Kolmogorov


