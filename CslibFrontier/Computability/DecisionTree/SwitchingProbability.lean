/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.DecisionTree.Switching
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Computability.DecisionTree.NormalForm
import CslibFrontier.Computability.DecisionTree.Restrict
import CslibFrontier.Foundations.Data.BitString.Agree
import CslibFrontier.Foundations.Data.Nat.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Rify

/-!
# The switching lemma as a probability bound

Arora and Barak state Håstad's switching lemma as a probability bound (Lemma 13.2 of the web
draft dated 2007-01-08, p. 236/252): if `f` is expressible as a `k`-DNF on `n` variables and `ρ`
is a random restriction that assigns random values to `t` randomly selected input bits, then for
every `s ≥ 2`,
`Pr_ρ[f|ρ is not expressible as an s-CNF] ≤ ((n - t) k ^ 10 / n) ^ (s / 2)`.
The draft leaves "verifying the exact bound" from its counting to Exercise 3 of Chapter 13.

This file proves that bound for every `k`. For `k ≠ 1` it is derived from the counting form of the
switching lemma (`DNF.card_switching_le`): at most `#R(ℓ - s) (4k)^s` restrictions leaving
`ℓ = n - t` variables free leave decision tree complexity at least `s`, and a decision tree of depth
below `s` gives an `s`-CNF (`DecisionTree.toCNF`). The random restriction is a uniform element of
`PartialAssignment.withFree (Fin n) (n - t)`, which leaves `n - t` (truncated subtraction) variables
free and so fixes `min t n` of them: exactly `t` when `t ≤ n`, the draft's setting, and all `n` when
`t > n` (for example, `n = 1` and `t = 2` fix one bit). The theorem is stated for every `t`. The
ratio `#R(ℓ - s) / #R(ℓ)` is bounded directly with `Nat.choose_sub_mul_pow_le`, which gives
`C(n, ℓ - s) / C(n, ℓ) ≤ (ℓ / (n - ℓ + 1)) ^ s`; this is a stronger form of the corrected Exercise
13.3(a) (`Nat.choose_add_le_choose_mul_div_pow`, which this file does not use). The result is
`Pr ≤ (8 k (n - t) / (t + 1)) ^ s` for `t ≤ n`, which is at most the draft's bound when
`(n - t) k ^ 10 < n` and `k ≥ 2`; otherwise the draft's bound is at least `1`.

**The case `k = 1`.** Here the counting bound has the factor `8 ^ s`, which `k ^ 10 = 1` does not
absorb, and the draft's proof (an encoding into `{0, 1, ⋆}^{2ks}`) does not give the bound
either. A direct argument does. A bad restriction of a formula whose terms have at most one literal
fixes every literal of the formula to false (otherwise the restricted function is `true`) and
leaves more than `s` of its variables free (otherwise a decision tree on them gives an `s`-CNF).
Drawing the restriction as a free set `J` of size `u = n - t` and a word, the word is forced on the
fixed variables of the formula. Weighting `J` by `y ^ (#(J ∩ V) - s - 1) ≥ 1` with
`y = (n + u) / (2u)` and expanding `(2y) ^ #(J ∩ V)` over the subsets of the variables `V` of the
formula bounds the probability by `(2u / (n + u)) ^ (s + 1)` (`sum_ite_half_pow_le`), and
`2u / (n + u) ≤ √(u / n)`.

## Main results

* `Cslib.Logic.PL.DNF.card_filter_not_cnf_div_card_le`: Arora–Barak, Lemma 13.2.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft 2007-01-08,
  Lemma 13.2][AroraBarak07]
* [J. Håstad, *Almost optimal lower bounds for small depth circuits*][Hastad1986]
-/

public section

open Finset

namespace Cslib.Logic.PL

open BitString DecisionTree

namespace DNF

variable {ι : Type*}

/-- Every formula in disjunctive normal form with terms of at most `k` literals has an equivalent
one whose terms also read each variable once: remove repeated literals, and the terms containing
a variable with both signs, which are never satisfied. -/
private theorem exists_nodup_of_length_le {k : ℕ} {F : DNF ι} (hk : ∀ T ∈ F, T.length ≤ k) :
    ∃ F' : DNF ι, (∀ T ∈ F', T.length ≤ k) ∧ (∀ T ∈ F', (T.map Prod.fst).Nodup) ∧
      ∀ x, DNF.eval x F' = DNF.eval x F := by
  classical
  refine ⟨(F.map List.dedup).filter fun T => (T.map Prod.fst).Nodup, fun T hT => ?_,
    fun T hT => by simpa using (List.mem_filter.1 hT).2, fun x => ?_⟩
  · obtain ⟨T₀, h₀, rfl⟩ := List.mem_map.1 (List.mem_filter.1 hT).1
    exact (List.dedup_sublist T₀).length_le.trans (hk T₀ h₀)
  · rw [Bool.eq_iff_iff, DNF.eval_eq_true_iff, DNF.eval_eq_true_iff]
    constructor
    · rintro ⟨T, hT, hx⟩
      obtain ⟨T₀, h₀, rfl⟩ := List.mem_map.1 (List.mem_filter.1 hT).1
      refine ⟨T₀, h₀, ?_⟩
      rw [Term.eval_eq_true_iff] at hx ⊢
      exact fun l hl => hx l (List.mem_dedup.2 hl)
    · rintro ⟨T₀, h₀, hx⟩
      rw [Term.eval_eq_true_iff] at hx
      refine ⟨T₀.dedup, List.mem_filter.2 ⟨List.mem_map_of_mem h₀, ?_⟩, ?_⟩
      · refine decide_eq_true (List.Nodup.map_on (fun a ha b hb hab => ?_) (List.nodup_dedup T₀))
        have ha' := hx a (List.mem_dedup.1 ha)
        have hb' := hx b (List.mem_dedup.1 hb)
        exact Prod.ext hab (by rw [← ha', ← hb', hab])
      · rw [Term.eval_eq_true_iff]
        exact fun l hl => hx l (List.mem_dedup.1 hl)

variable [Fintype ι]

/-- A restricted function depends only on the free variables, so it has decision tree complexity
at most their number. -/
private theorem complexity_fill_le_card_free (ρ : PartialAssignment ι) (f : (ι → Bool) → Bool) :
    complexity (fun x => f (ρ.fill x)) ≤ #ρ.free := by
  classical
  refine complexity_le_iff.2 ⟨queryAll (fun x => f (ρ.fill x)) ρ.free.toList fun _ => false,
    fun x => ?_, (depth_queryAll_le _ _ _).trans_eq (length_toList _)⟩
  rw [eval_queryAll]
  congr 1
  funext i
  by_cases hi : ρ i = none
  · simp [hi]
  · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 hi
    simp [hb]

/-! ### Terms of one literal -/

omit [Fintype ι] in
/-- A formula in disjunctive normal form reads only the variables of its literals. -/
private theorem eval_congr {F : DNF ι} {σ σ' : ι → Bool}
    (h : ∀ T ∈ F, ∀ l ∈ T, σ l.1 = σ' l.1) : DNF.eval σ F = DNF.eval σ' F := by
  rw [Bool.eq_iff_iff, DNF.eval_eq_true_iff, DNF.eval_eq_true_iff]
  refine exists_congr fun T => and_congr_right fun hT => ?_
  rw [Term.eval_eq_true_iff, Term.eval_eq_true_iff]
  exact forall₂_congr fun l hl => by rw [h T hT l hl]

/-- The `u`-subsets of an `n`-set containing a fixed set `T` number at most
`C(n, u) (u / n) ^ #T`. -/
private theorem card_filter_subset_le {n u : ℕ} (hun : u ≤ n) (T : Finset (Fin n)) :
    (#{J ∈ (univ : Finset (Fin n)).powersetCard u | T ⊆ J} : ℝ) ≤
      n.choose u * ((u : ℝ) / n) ^ #T := by
  rcases lt_or_ge u #T with htu | htu
  · have h0 : {J ∈ (univ : Finset (Fin n)).powersetCard u | T ⊆ J} = ∅ := by
      refine filter_false_of_mem fun J hJ hTJ => ?_
      have := card_le_card hTJ
      rw [(mem_powersetCard.1 hJ).2] at this
      omega
    rw [h0, card_empty, Nat.cast_zero]
    positivity
  have hT : #T ≤ n := by simpa using card_le_univ T
  have hcard : #{J ∈ (univ : Finset (Fin n)).powersetCard u | T ⊆ J} =
      (n - #T).choose (u - #T) := by
    rw [show n - #T = #Tᶜ by rw [card_compl, Fintype.card_fin], ← card_powersetCard]
    refine card_nbij' (fun J => J \ T) (fun K => K ∪ T) (fun J hJ => ?_) (fun K hK => ?_)
      (fun J hJ => ?_) (fun K hK => ?_)
    · obtain ⟨hJ, hTJ⟩ := mem_filter.1 hJ
      refine mem_powersetCard.2 ⟨fun i hi => mem_compl.2 (mem_sdiff.1 hi).2, ?_⟩
      rw [card_sdiff_of_subset hTJ, (mem_powersetCard.1 hJ).2]
    · obtain ⟨hKT, hK⟩ := mem_powersetCard.1 hK
      have hdis : Disjoint K T := disjoint_left.2 fun i hi => mem_compl.1 (hKT hi)
      refine mem_filter.2 ⟨mem_powersetCard.2 ⟨subset_univ _, ?_⟩, subset_union_right⟩
      rw [card_union_of_disjoint hdis, hK]
      omega
    · exact sdiff_union_of_subset (mem_filter.1 hJ).2
    · have hdis : Disjoint K T :=
        disjoint_left.2 fun i hi => mem_compl.1 ((mem_powersetCard.1 hK).1 hi)
      change (K ∪ T) \ T = K
      rw [union_sdiff_right, sdiff_eq_self_of_disjoint hdis]
  rw [hcard]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain rfl : u = 0 := by omega
    have hT0 : #T = 0 := by omega
    simp [hT0]
  -- `C(n - t, u - t) n ^ t ≤ C(n, u) u ^ t`, from `C(n, u) C(u, t) = C(n, t) C(n - t, u - t)`
  have hmul : n.choose u * u.choose #T = n.choose #T * (n - #T).choose (u - #T) :=
    Nat.choose_mul htu
  have hle := Nat.choose_mul_pow_le hun #T
  have hpos : 0 < n.choose #T := Nat.choose_pos hT
  have key : (n - #T).choose (u - #T) * n ^ #T ≤ n.choose u * u ^ #T := by
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    calc n.choose #T * ((n - #T).choose (u - #T) * n ^ #T)
        = n.choose u * (u.choose #T * n ^ #T) := by rw [← mul_assoc, ← hmul]; ring
      _ ≤ n.choose u * (n.choose #T * u ^ #T) := Nat.mul_le_mul_left _ hle
      _ = n.choose #T * (n.choose u * u ^ #T) := by ring
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_pow, ← mul_div_assoc, le_div_iff₀ (by positivity)]
  exact_mod_cast key

/-- **The counting core of the case `k = 1`.** Summing `(1/2) ^ #(V \ J)` over the `u`-subsets `J`
of an `n`-set that contain at least `r` points of `V` gives at most `C(n, u) (2u / (n + u)) ^ r`.
Weight each `J` by `y ^ (#(J ∩ V) - r) ≥ 1` with `y = (n + u) / (2u)` and expand
`(2y) ^ #(J ∩ V)` binomially: the subsets `T ⊆ V` contribute `(n / u) ^ #T` times the number of
`J ⊇ T`, at most `C(n, u) (u / n) ^ #T`. -/
private theorem sum_ite_half_pow_le {n u r : ℕ} (hu : 0 < u) (hun : u ≤ n) (V : Finset (Fin n)) :
    ∑ J ∈ (univ : Finset (Fin n)).powersetCard u,
        (if r ≤ #(J ∩ V) then ((1 : ℝ) / 2) ^ #(V \ J) else 0) ≤
      n.choose u * (2 * u / (n + u) : ℝ) ^ r := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  have hun' : (u : ℝ) ≤ n := by exact_mod_cast hun
  set y : ℝ := (n + u) / (2 * u) with hy
  have hy0 : 0 < y := by positivity
  have hy1 : 1 ≤ y := by rw [hy, le_div_iff₀ (by positivity)]; linarith
  have hyinv : (2 * u / (n + u) : ℝ) = y⁻¹ := by rw [hy, inv_div]
  have h2y : (2 * y - 1) * ((u : ℝ) / n) = 1 := by
    rw [hy]; field_simp; ring
  -- each term is at most `y ^ (-r) (1/2) ^ #V (2y) ^ #(J ∩ V)`
  have hterm (J : Finset (Fin n)) :
      (if r ≤ #(J ∩ V) then ((1 : ℝ) / 2) ^ #(V \ J) else 0) ≤
        (y ^ r)⁻¹ * ((1 : ℝ) / 2) ^ #V * (2 * y) ^ #(J ∩ V) := by
    have hsplit : #(V \ J) + #(J ∩ V) = #V := by
      rw [inter_comm]; exact card_sdiff_add_card_inter V J
    split_ifs with hr
    · have hyj : y ^ r ≤ y ^ #(J ∩ V) := pow_le_pow_right₀ hy1 hr
      have he : (y ^ r)⁻¹ * ((1 : ℝ) / 2) ^ #V * (2 * y) ^ #(J ∩ V) =
          ((1 : ℝ) / 2) ^ #(V \ J) * (y ^ #(J ∩ V) / y ^ r) := by
        rw [← hsplit, mul_pow, pow_add]
        field_simp
        rw [← mul_pow]
        norm_num
      rw [he]
      exact le_mul_of_one_le_right (by positivity) ((one_le_div (by positivity)).2 hyj)
    · positivity
  -- the binomial expansion of `(2y) ^ #(J ∩ V)`, regrouped by `T ⊆ V`
  have hexp (J : Finset (Fin n)) : (2 * y) ^ #(J ∩ V) =
      ∑ T ∈ V.powerset, if T ⊆ J then (2 * y - 1) ^ #T else 0 := by
    have h := sum_pow_mul_eq_add_pow (2 * y - 1) 1 (J ∩ V)
    simp only [one_pow, mul_one, sub_add_cancel] at h
    rw [← h, ← sum_filter]
    refine sum_congr (ext fun T => ?_) fun _ _ => rfl
    simp only [mem_powerset, mem_filter, subset_inter_iff]
    tauto
  have hsum : ∑ J ∈ (univ : Finset (Fin n)).powersetCard u, (2 * y) ^ #(J ∩ V) ≤
      n.choose u * 2 ^ #V := by
    simp only [hexp]
    rw [sum_comm]
    calc ∑ T ∈ V.powerset, ∑ J ∈ (univ : Finset (Fin n)).powersetCard u,
          (if T ⊆ J then (2 * y - 1) ^ #T else 0)
        = ∑ T ∈ V.powerset,
            (#{J ∈ (univ : Finset (Fin n)).powersetCard u | T ⊆ J} : ℝ) * (2 * y - 1) ^ #T := by
          refine sum_congr rfl fun T _ => ?_
          rw [← sum_filter, sum_const, nsmul_eq_mul]
      _ ≤ ∑ T ∈ V.powerset, (n.choose u * ((u : ℝ) / n) ^ #T) * (2 * y - 1) ^ #T :=
          sum_le_sum fun T _ => mul_le_mul_of_nonneg_right (card_filter_subset_le hun T)
            (pow_nonneg (by linarith) _)
      _ = n.choose u * ∑ T ∈ V.powerset, ((2 * y - 1) * ((u : ℝ) / n)) ^ #T * 1 ^ (#V - #T) := by
          rw [mul_sum]
          refine sum_congr rfl fun T _ => ?_
          rw [one_pow, mul_one, mul_pow]
          ring
      _ = n.choose u * 2 ^ #V := by
          rw [sum_pow_mul_eq_add_pow, h2y]
          norm_num
  calc ∑ J ∈ (univ : Finset (Fin n)).powersetCard u,
        (if r ≤ #(J ∩ V) then ((1 : ℝ) / 2) ^ #(V \ J) else 0)
      ≤ ∑ J ∈ (univ : Finset (Fin n)).powersetCard u,
          (y ^ r)⁻¹ * ((1 : ℝ) / 2) ^ #V * (2 * y) ^ #(J ∩ V) := sum_le_sum fun J _ => hterm J
    _ = (y ^ r)⁻¹ * ((1 : ℝ) / 2) ^ #V *
          ∑ J ∈ (univ : Finset (Fin n)).powersetCard u, (2 * y) ^ #(J ∩ V) := by
        rw [mul_sum]
    _ ≤ (y ^ r)⁻¹ * ((1 : ℝ) / 2) ^ #V * (n.choose u * 2 ^ #V) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (y ^ r)⁻¹ * n.choose u * (((1 : ℝ) / 2) ^ #V * 2 ^ #V) := by ring
    _ = n.choose u * (2 * u / (n + u) : ℝ) ^ r := by
        rw [← mul_pow, hyinv, inv_pow]
        norm_num
        ring

open Classical in
/-- **Lemma 13.2 for `k = 1`.** A function given by a formula in disjunctive normal form whose
terms have at most one literal fails to restrict to an `s`-CNF with probability at most
`((n - t) / n) ^ (s / 2)`.

If a fixed literal is true, the restricted function is the constant `true`; otherwise it reads
only the free variables of the formula, and a decision tree querying them gives a CNF with clauses
of at most that many literals. So a bad restriction fixes every literal of the formula to false
and leaves more than `s` of its variables free. Drawing the restriction as a free set `J` and a
word (`PartialAssignment.sum_card_filter_outside`), the word is forced on the fixed variables of
the formula, and `sum_ite_half_pow_le` bounds the probability by `(2u / (n + u)) ^ (s + 1)` with
`u = n - t`. Since `2u / (n + u) ≤ √(u / n)` and `2u / (n + u) ≤ 1`, this is at most
`(u / n) ^ (s / 2)`. -/
private theorem card_filter_not_cnf_div_card_le_of_length_le_one {n s t : ℕ}
    {f : (Fin n → Bool) → Bool}
    (hf : ∃ F : DNF (Fin n), (∀ T ∈ F, T.length ≤ 1) ∧ ∀ x, DNF.eval x F = f x) :
    (#{ρ ∈ PartialAssignment.withFree (Fin n) (n - t) |
        ¬ ∃ G : CNF (Fin n), (∀ c ∈ G, c.length ≤ s) ∧ ∀ x, CNF.eval x G = f (ρ.fill x)} : ℝ) /
      #(PartialAssignment.withFree (Fin n) (n - t)) ≤
    (((n - t : ℕ) : ℝ) / n) ^ ((s : ℝ) / 2) := by
  classical
  obtain ⟨F, hk, hF⟩ := hf
  set u := n - t with hu
  set W := PartialAssignment.withFree (Fin n) u
  set B := {ρ ∈ W | ¬ ∃ G : CNF (Fin n), (∀ c ∈ G, c.length ≤ s) ∧
    ∀ x, CNF.eval x G = f (ρ.fill x)}
  set L : Finset (Literal (Fin n)) := F.flatten.toFinset
  set V : Finset (Fin n) := L.image Prod.fst
  have hrhs : (0 : ℝ) ≤ (((u : ℕ) : ℝ) / n) ^ ((s : ℝ) / 2) := by positivity
  have hmemL {T : Term (Fin n)} {l : Literal (Fin n)} (hT : T ∈ F) (hl : l ∈ T) : l ∈ L :=
    List.mem_toFinset.2 (List.mem_flatten.2 ⟨T, hT, hl⟩)
  -- a bad restriction fixes no literal of `F` to true and leaves more than `s` variables free
  set E : PartialAssignment (Fin n) → Prop :=
    fun ρ => (∀ l ∈ L, ρ l.1 ≠ some l.2) ∧ s < #(ρ.free ∩ V)
  have hsub : B ⊆ W.filter E := by
    intro ρ hρ
    obtain ⟨hρW, hbad⟩ := mem_filter.1 hρ
    refine mem_filter.2 ⟨hρW, fun l hl hρl => hbad ⟨[], by simp, fun x => ?_⟩, ?_⟩
    · obtain ⟨T, hT, hlT⟩ := List.mem_flatten.1 (List.mem_toFinset.1 hl)
      rw [CNF.eval_nil, ← hF, eq_comm, DNF.eval_eq_true_iff]
      refine ⟨T, hT, (Term.eval_eq_true_iff _ _).2 fun l' hl' => ?_⟩
      obtain rfl : l' = l := by
        rcases T with _ | ⟨a, _ | ⟨b, T⟩⟩
        · simp at hlT
        · simp only [List.mem_singleton] at hl' hlT; rw [hl', hlT]
        · have := hk _ hT; simp at this
      exact PartialAssignment.fill_of_eq_some hρl x
    · by_contra hle
      replace hle := not_lt.1 hle
      set A := ρ.free ∩ V
      refine hbad ⟨(queryAll (fun x => f (ρ.fill x)) A.toList fun _ => false).toCNF,
        fun c hc => (length_le_depth_of_mem_toCNF hc).trans
          ((depth_queryAll_le _ _ _).trans (by rw [length_toList]; exact hle)), fun x => ?_⟩
      rw [eval_toCNF, eval_queryAll, ← hF, ← hF]
      refine eval_congr fun T hT l hl => ?_
      rcases hρl : ρ l.1 with _ | c
      · have hA : l.1 ∈ A := mem_inter.2 ⟨PartialAssignment.mem_free.2 hρl,
          mem_image.2 ⟨l, hmemL hT hl, rfl⟩⟩
        rw [PartialAssignment.fill_of_eq_none hρl, PartialAssignment.fill_of_eq_none hρl]
        simp only [mem_toList.2 hA, ↓reduceIte]
      · simp [PartialAssignment.fill_of_eq_some hρl]
  rcases Nat.eq_zero_or_pos u with hu0 | hupos
  · -- no free variables: nothing is bad
    have hB : B = ∅ := by
      refine eq_empty_of_forall_notMem fun ρ hρ => ?_
      obtain ⟨hρW, -, hs⟩ := mem_filter.1 (hsub hρ)
      have := card_le_card (inter_subset_left (s₁ := ρ.free) (s₂ := V))
      rw [PartialAssignment.mem_withFree.1 hρW] at this
      omega
    rw [hB, card_empty, Nat.cast_zero, zero_div]
    exact hrhs
  have hun : u ≤ n := by omega
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  -- the words completing a free set `J` to a restriction in `E`
  set w : Fin n → Bool := fun i => if h : ∃ l ∈ L, l.1 = i then !h.choose.2 else false
  have hword (J : Finset (Fin n)) :
      #{z : Fin n → Bool | E (PartialAssignment.outside J z)} ≤
        if s < #(J ∩ V) then 2 ^ (n - #(V \ J)) else 0 := by
    split_ifs with hs
    · calc #{z : Fin n → Bool | E (PartialAssignment.outside J z)}
          ≤ #{z : Fin n → Bool | ∀ i ∉ (V \ J)ᶜ, z i = w i} := by
            refine card_le_card fun z hz => mem_filter.2 ⟨mem_univ _, fun i hi => ?_⟩
            have hi' := mem_sdiff.1 (by simpa using hi)
            have h : ∃ l ∈ L, l.1 = i := by simpa [V] using hi'.1
            obtain ⟨hl, hli⟩ := h.choose_spec
            have hne := (mem_filter.1 hz).2.1 _ hl
            simp only [PartialAssignment.outside, hli, hi'.2, ite_false, ne_eq,
              Option.some.injEq] at hne
            simp only [w, h, ↓reduceDIte]
            cases hzi : z i <;> cases hc : h.choose.2 <;> simp_all
        _ = 2 ^ (n - #(V \ J)) := by
            rw [card_filter_forall_notMem_eq, card_compl, Fintype.card_fin]
    · refine (card_eq_zero.2 (filter_false_of_mem fun z _ hz => hs ?_)).le
      simpa [PartialAssignment.free_outside] using hz.2
  have hcount : (2 ^ u * #(W.filter E) : ℝ) ≤ ∑ J ∈ (univ : Finset (Fin n)).powersetCard u,
      (if s < #(J ∩ V) then (2 : ℝ) ^ (n - #(V \ J)) else 0) := by
    have h : ∑ J ∈ (univ : Finset (Fin n)).powersetCard u,
        #{z : Fin n → Bool | E (PartialAssignment.outside J z)} = 2 ^ u * #(W.filter E) :=
      PartialAssignment.sum_card_filter_outside E u
    have h' : ((2 ^ u * #(W.filter E) : ℕ) : ℝ) ≤ ∑ J ∈ (univ : Finset (Fin n)).powersetCard u,
        (if s < #(J ∩ V) then (2 : ℝ) ^ (n - #(V \ J)) else 0) := by
      rw [← h]
      push_cast
      refine sum_le_sum fun J _ => ?_
      have := hword J
      split_ifs at this ⊢ <;> exact_mod_cast this
    exact_mod_cast h'
  have hW : (#W : ℝ) = n.choose u * 2 ^ (n - u) := by
    rw [PartialAssignment.card_withFree, Fintype.card_fin]; push_cast; ring
  have hhalf (J : Finset (Fin n)) :
      (if s < #(J ∩ V) then (2 : ℝ) ^ (n - #(V \ J)) else 0) =
        2 ^ n * (if s + 1 ≤ #(J ∩ V) then ((1 : ℝ) / 2) ^ #(V \ J) else 0) := by
    have hVJ : #(V \ J) ≤ n := by simpa using card_le_univ (V \ J)
    by_cases hs : s < #(J ∩ V)
    · have hs' : s + 1 ≤ #(J ∩ V) := hs
      simp only [hs, hs', ↓reduceIte]
      rw [div_pow, one_pow, ← div_eq_mul_one_div, pow_sub₀ _ (by norm_num) hVJ, div_eq_mul_inv]
    · have hs' : ¬ s + 1 ≤ #(J ∩ V) := hs
      simp only [hs, hs', ↓reduceIte, mul_zero]
  have hcore := sum_ite_half_pow_le (r := s + 1) hupos hun V
  -- the probability is at most `g ^ (s + 1)` with `g = 2u / (n + u)`
  set g : ℝ := 2 * u / (n + u)
  have hg0 : 0 ≤ g := by positivity
  have hP : (#(W.filter E) : ℝ) / #W ≤ g ^ (s + 1) := by
    have hu2 : (2 : ℝ) ^ u * 2 ^ (n - u) = 2 ^ n := by rw [← pow_add]; congr 1; omega
    have hWpos : (0 : ℝ) < #W := by
      rw [hW]; exact mul_pos (by exact_mod_cast Nat.choose_pos hun) (by positivity)
    rw [div_le_iff₀ hWpos, hW]
    have h1 : (2 : ℝ) ^ u * #(W.filter E) ≤ 2 ^ n * (n.choose u * g ^ (s + 1)) := by
      refine hcount.trans ?_
      simp only [hhalf, ← mul_sum]
      exact mul_le_mul_of_nonneg_left hcore (by positivity)
    have h2 : (2 : ℝ) ^ u * #(W.filter E) ≤ 2 ^ u * (g ^ (s + 1) * (n.choose u * 2 ^ (n - u))) := by
      refine h1.trans_eq ?_
      rw [← hu2]; ring
    exact le_of_mul_le_mul_left h2 (by positivity)
  -- `g ≤ 1` and `g ^ 2 ≤ u / n`
  have hu' : (u : ℝ) ≤ n := by exact_mod_cast hun
  have hg1 : g ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hg2 : g ^ 2 ≤ (u : ℝ) / n := by
    rw [div_pow, div_le_div_iff₀ (by positivity) hn]
    nlinarith [sq_nonneg ((n : ℝ) - u)]
  calc (#B : ℝ) / #W ≤ (#(W.filter E) : ℝ) / #W :=
        div_le_div_of_nonneg_right (by exact_mod_cast card_le_card hsub) (by positivity)
    _ ≤ g ^ (s + 1) := hP
    _ ≤ g ^ s := pow_le_pow_of_le_one hg0 hg1 (by omega)
    _ = (g ^ 2) ^ ((s : ℝ) / 2) := by
        rw [← Real.rpow_natCast g 2, ← Real.rpow_mul hg0, ← Real.rpow_natCast g s]
        congr 1; push_cast; ring
    _ ≤ _ := Real.rpow_le_rpow (by positivity) hg2 (by positivity)

open Classical in
/-- **Arora–Barak, Lemma 13.2, for `k ≠ 1`** (Håstad's switching lemma; web draft 2007-01-08,
p. 236/252), from the counting form of the switching lemma. `card_filter_not_cnf_div_card_le`
combines it with the case `k = 1`. Let `f` be expressible as a `k`-DNF on
`n` variables and let `ρ` be a uniform element of `PartialAssignment.withFree (Fin n) (n - t)`:
a uniform set of `min t n` fixed positions with uniform values. For `t ≤ n`, the draft's setting,
this fixes exactly `t` variables; for `t > n` it fixes all `n`. Then the probability that the
restricted function `x ↦ f (ρ.fill x)` is not computed by a CNF with clauses of at most `s`
literals is at most `((n - t) k ^ 10 / n) ^ (s / 2)`. The draft assumes `s ≥ 2`; the bound holds
for every `s`. -/
private theorem card_filter_not_cnf_div_card_le_of_ne_one {n k s t : ℕ} (hk : k ≠ 1)
    {f : (Fin n → Bool) → Bool}
    (hf : ∃ F : DNF (Fin n), (∀ T ∈ F, T.length ≤ k) ∧ ∀ x, DNF.eval x F = f x) :
    (#{ρ ∈ PartialAssignment.withFree (Fin n) (n - t) |
        ¬ ∃ G : CNF (Fin n), (∀ c ∈ G, c.length ≤ s) ∧ ∀ x, CNF.eval x G = f (ρ.fill x)} : ℝ) /
      #(PartialAssignment.withFree (Fin n) (n - t)) ≤
    (((n - t : ℕ) : ℝ) * k ^ 10 / n) ^ ((s : ℝ) / 2) := by
  obtain ⟨F₀, hk₀, hF₀⟩ := hf
  obtain ⟨F, hkF, hnd, hFe⟩ := exists_nodup_of_length_le hk₀
  set u := n - t with hu
  set W := PartialAssignment.withFree (Fin n) u
  set B := {ρ ∈ W | ¬ ∃ G : CNF (Fin n), (∀ c ∈ G, c.length ≤ s) ∧
    ∀ x, CNF.eval x G = f (ρ.fill x)}
  have hbase : (0 : ℝ) ≤ (u : ℝ) * k ^ 10 / n := by positivity
  have hrhs : (0 : ℝ) ≤ ((u : ℝ) * k ^ 10 / n) ^ ((s : ℝ) / 2) := Real.rpow_nonneg hbase _
  -- a restriction leaving `F` with decision tree complexity at most `s` makes `f` an `s`-CNF
  have hsub : B ⊆ W.filter fun ρ => s ≤ complexity fun x => DNF.eval (ρ.fill x) F := by
    intro ρ hρ
    obtain ⟨hρW, hbad⟩ := mem_filter.1 hρ
    refine mem_filter.2 ⟨hρW, ?_⟩
    by_contra hlt
    obtain ⟨tr, htr, hd⟩ := complexity_le_iff.1 (le_refl (complexity fun x =>
      DNF.eval (ρ.fill x) F))
    refine hbad ⟨tr.toCNF, fun c hc => (length_le_depth_of_mem_toCNF hc).trans (by omega),
      fun x => ?_⟩
    rw [eval_toCNF, htr]
    exact (hFe _).trans (hF₀ _)
  rcases lt_or_ge u s with hus | hsu
  · -- fewer than `s` free variables: the restricted function is always shallow
    have hB : B = ∅ := by
      refine eq_empty_of_forall_notMem fun ρ hρ => ?_
      have h := mem_filter.1 (hsub hρ)
      have hfree := (PartialAssignment.mem_extensions.1 h.1).2
      have := complexity_fill_le_card_free ρ fun y => DNF.eval y F
      omega
    rw [hB, card_empty, Nat.cast_zero, zero_div]
    exact hrhs
  -- the switching lemma: `#B (t' + 1) ^ s ≤ #W (8 k u) ^ s` with `t' = n - u`
  have hun : u ≤ n := by omega
  have hcount : #B * (n - u + 1) ^ s ≤ #W * (8 * k * u) ^ s := by
    have hsw := card_switching_le hkF hnd PartialAssignment.empty u s
    have hch := Nat.choose_sub_mul_pow_le hsu hun
    rw [PartialAssignment.card_withFree, Fintype.card_fin]
    have h2 : 2 ^ (n - (u - s)) = 2 ^ (n - u) * 2 ^ s := by rw [← pow_add]; congr 1; omega
    calc #B * (n - u + 1) ^ s
        ≤ #(PartialAssignment.withFree (Fin n) (u - s)) * (4 * k) ^ s * (n - u + 1) ^ s :=
          Nat.mul_le_mul_right _ ((card_le_card hsub).trans hsw)
      _ = n.choose (u - s) * (n - u + 1) ^ s * (2 ^ (n - u) * (8 * k) ^ s) := by
          rw [PartialAssignment.card_withFree, Fintype.card_fin, h2, mul_pow, mul_pow,
            show (8 : ℕ) ^ s = 2 ^ s * 4 ^ s by rw [← mul_pow]; norm_num]
          ring
      _ ≤ n.choose u * u ^ s * (2 ^ (n - u) * (8 * k) ^ s) := Nat.mul_le_mul_right _ hch
      _ = n.choose u * 2 ^ (n - u) * (8 * k * u) ^ s := by rw [mul_pow]; ring
  have hWpos : 0 < #W := by
    rw [PartialAssignment.card_withFree, Fintype.card_fin]
    exact Nat.mul_pos (Nat.choose_pos hun) (by positivity)
  -- the probability is at most `r ^ s` with `r = 8 k u / (n - u + 1)`, and at most `1`
  set r : ℝ := 8 * k * u / ((n - u : ℕ) + 1)
  have hr : (0 : ℝ) ≤ r := by positivity
  have hP : (#B : ℝ) / #W ≤ r ^ s := by
    rw [div_le_iff₀ (by exact_mod_cast hWpos), div_pow, div_mul_eq_mul_div,
      le_div_iff₀ (by positivity)]
    exact_mod_cast (by simpa [mul_comm] using hcount : #B * (n - u + 1) ^ s ≤ (8 * k * u) ^ s * #W)
  have hP1 : (#B : ℝ) / #W ≤ 1 :=
    div_le_one_of_le₀ (by exact_mod_cast card_le_card (filter_subset _ _)) (by positivity)
  rcases Nat.eq_zero_or_pos s with hs0 | hs0
  · rw [hs0, Nat.cast_zero, zero_div, Real.rpow_zero]
    exact hP1
  rcases le_or_gt 1 ((u : ℝ) * k ^ 10 / n) with h1 | h1
  · exact hP1.trans (Real.one_le_rpow h1 (by positivity))
  -- otherwise `u k ^ 10 < n`, so `k = 0` or `t` is most of `n`, and `r ^ 2 ≤ u k ^ 10 / n`
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hr2 : r ^ 2 ≤ (u : ℝ) * k ^ 10 / n := by
    rw [div_lt_one hnpos] at h1
    rcases Nat.eq_zero_or_pos k with hk0 | hk2
    · simp [r, hk0]
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
    have hk8 : (256 : ℝ) ≤ (k : ℝ) ^ 8 := by
      calc (256 : ℝ) = 2 ^ 8 := by norm_num
        _ ≤ (k : ℝ) ^ 8 := pow_le_pow_left₀ (by norm_num) hk2 8
    have hu' : (u : ℝ) * 1024 ≤ u * k ^ 10 := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc (1024 : ℝ) = 2 ^ 10 := by norm_num
        _ ≤ (k : ℝ) ^ 10 := pow_le_pow_left₀ (by norm_num) hk2 10
    have hcast : ((n - u : ℕ) : ℝ) = n - u := by push_cast [Nat.cast_sub hun]; ring
    -- `t' + 1 ≥ n / 2`, so `64 n u ≤ 256 (t' + 1) ^ 2 ≤ k ^ 8 (t' + 1) ^ 2`
    have ht' : (n : ℝ) ≤ 2 * ((n - u : ℕ) + 1) := by rw [hcast]; nlinarith
    have hun' : (u : ℝ) ≤ n := by exact_mod_cast hun
    rw [div_pow, div_le_div_iff₀ (by positivity) hnpos]
    have hkey : 64 * (n : ℝ) * u ≤ (k : ℝ) ^ 8 * (((n - u : ℕ) : ℝ) + 1) ^ 2 := by
      have hq : (0 : ℝ) ≤ ((n - u : ℕ) : ℝ) + 1 := by positivity
      nlinarith [mul_le_mul ht' ht' (by positivity) (by positivity)]
    have hku : (0 : ℝ) ≤ (k : ℝ) ^ 2 * u := by positivity
    calc (8 * k * u : ℝ) ^ 2 * n = (k ^ 2 * u) * (64 * n * u) := by ring
      _ ≤ (k ^ 2 * u) * ((k : ℝ) ^ 8 * (((n - u : ℕ) : ℝ) + 1) ^ 2) :=
          mul_le_mul_of_nonneg_left hkey hku
      _ = u * k ^ 10 * (((n - u : ℕ) : ℝ) + 1) ^ 2 := by ring
  calc (#B : ℝ) / #W ≤ r ^ s := hP
    _ = (r ^ 2) ^ ((s : ℝ) / 2) := by
        rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr, ← Real.rpow_natCast r s]
        congr 1; push_cast; ring
    _ ≤ _ := Real.rpow_le_rpow (by positivity) hr2 (by positivity)

open Classical in
/-- **Arora–Barak, Lemma 13.2** (Håstad's switching lemma; web draft 2007-01-08, p. 236/252). Let
`f` be expressible as a `k`-DNF on `n` variables and let `ρ` be a uniformly random restriction
fixing `t` variables, i.e. a uniform element of `PartialAssignment.withFree (Fin n) (n - t)`: a
uniform set of `t` positions with uniform values (all `n` positions when `t > n`). Then the
probability that the restricted function `x ↦ f (ρ.fill x)` is not computed by a CNF with clauses
of at most `s` literals is at most `((n - t) k ^ 10 / n) ^ (s / 2)`. The draft assumes `s ≥ 2`;
the bound holds for every `s`. -/
theorem card_filter_not_cnf_div_card_le {n k s t : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : ∃ F : DNF (Fin n), (∀ T ∈ F, T.length ≤ k) ∧ ∀ x, DNF.eval x F = f x) :
    (#{ρ ∈ PartialAssignment.withFree (Fin n) (n - t) |
        ¬ ∃ G : CNF (Fin n), (∀ c ∈ G, c.length ≤ s) ∧ ∀ x, CNF.eval x G = f (ρ.fill x)} : ℝ) /
      #(PartialAssignment.withFree (Fin n) (n - t)) ≤
    (((n - t : ℕ) : ℝ) * k ^ 10 / n) ^ ((s : ℝ) / 2) := by
  rcases eq_or_ne k 1 with rfl | hk
  · rw [Nat.cast_one, one_pow, mul_one]
    exact card_filter_not_cnf_div_card_le_of_length_le_one hf
  · exact card_filter_not_cnf_div_card_le_of_ne_one hk hf

end DNF

end Cslib.Logic.PL
