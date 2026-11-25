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
import CslibFrontier.Foundations.Combinatorics.Hypergeometric.Superset
import CslibFrontier.Logics.Propositional.DNF.ModelCount
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
either. A direct argument does. Under a bad restriction of a formula whose terms have at most one
literal, every fixed literal of the formula is false (otherwise the restricted function is `true`),
and more than `s` of its variables stay free (otherwise a decision tree on them gives an `s`-CNF).
Drawing the restriction as a free set `J` of size `u = n - t` and a word, the word is forced on the
fixed variables of the formula. Weighting `J` by `y ^ (#(J ∩ V) - s - 1) ≥ 1` with
`y = (n + u) / (2u)` and expanding `(2y) ^ #(J ∩ V)` over the subsets of the variables `V` of the
formula bounds the probability by `(2u / (n + u)) ^ (s + 1)`
(`Cslib.sum_powersetCard_ite_half_pow_le`), and `2u / (n + u) ≤ √(u / n)`.

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
      exact ⟨T₀, h₀, (Term.eval_eq_true_iff _ _).2 fun l hl =>
        (Term.eval_eq_true_iff _ _).1 hx l (List.mem_dedup.2 hl)⟩
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
  cases hi : ρ i <;> simp [hi]

/-! ### Terms of one literal -/

open Classical in
/-- **Lemma 13.2 for `k = 1`.** A function given by a formula in disjunctive normal form whose
terms have at most one literal fails to restrict to an `s`-CNF with probability at most
`((n - t) / n) ^ (s / 2)`.

If a fixed literal is true, the restricted function is the constant `true`; otherwise it reads
only the free variables of the formula, and a decision tree querying them gives a CNF with clauses
of at most that many literals. So under a bad restriction every fixed literal of the formula is
false, and more than `s` of its variables stay free. Drawing the restriction as a free set `J` and a
word (`PartialAssignment.sum_card_filter_outside`), the word is forced on the fixed variables of
the formula, and `Cslib.sum_powersetCard_ite_half_pow_le` bounds the probability by
`(2u / (n + u)) ^ (s + 1)` with `u = n - t`. Since `2u / (n + u) ≤ √(u / n)` and
`2u / (n + u) ≤ 1`, this is at most `(u / n) ^ (s / 2)`. -/
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
      refine DNF.eval_congr fun v hv => ?_
      obtain ⟨T, hT, b, hl⟩ := CNF.mem_vars.1 hv
      rcases hρl : ρ v with _ | c
      · have hA : v ∈ A := mem_inter.2 ⟨PartialAssignment.mem_free.2 hρl,
          mem_image.2 ⟨(v, b), hmemL hT hl, rfl⟩⟩
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
      (#{z : Fin n → Bool | E (PartialAssignment.outside J z)} : ℝ) ≤
        2 ^ n * if s + 1 ≤ #(J ∩ V) then ((1 : ℝ) / 2) ^ #(V \ J) else 0 := by
    split_ifs with hs
    · have hVJ : #(V \ J) ≤ n := by simpa using card_le_univ (V \ J)
      rw [div_pow, one_pow, ← div_eq_mul_one_div, div_eq_mul_inv, ← pow_sub₀ _ two_ne_zero hVJ]
      have hc : #{z : Fin n → Bool | E (PartialAssignment.outside J z)} ≤ 2 ^ (n - #(V \ J)) :=
        calc #{z : Fin n → Bool | E (PartialAssignment.outside J z)}
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
      exact_mod_cast hc
    · rw [mul_zero, Nat.cast_nonpos, card_eq_zero]
      exact filter_false_of_mem fun z _ hz =>
        hs (by simpa [PartialAssignment.free_outside] using hz.2 : s < #(J ∩ V))
  have hW : (#W : ℝ) = n.choose u * 2 ^ (n - u) := by
    rw [PartialAssignment.card_withFree, Fintype.card_fin]; push_cast; ring
  have hcore := Cslib.sum_powersetCard_ite_half_pow_le (r := s + 1) hupos hun V
  -- the probability is at most `g ^ (s + 1)` with `g = 2u / (n + u)`
  set g : ℝ := 2 * u / (n + u)
  have hg0 : 0 ≤ g := by positivity
  have hP : (#(W.filter E) : ℝ) / #W ≤ g ^ (s + 1) := by
    have hcount : (2 ^ u * #(W.filter E) : ℝ) ≤ 2 ^ n * (n.choose u * g ^ (s + 1)) :=
      calc (2 ^ u * #(W.filter E) : ℝ)
          = ∑ J ∈ (univ : Finset (Fin n)).powersetCard u,
              (#{z : Fin n → Bool | E (PartialAssignment.outside J z)} : ℝ) := by
            exact_mod_cast (PartialAssignment.sum_card_filter_outside E u).symm
        _ ≤ 2 ^ n * ∑ J ∈ (univ : Finset (Fin n)).powersetCard u,
              (if s + 1 ≤ #(J ∩ V) then ((1 : ℝ) / 2) ^ #(V \ J) else 0) := by
            rw [mul_sum]; exact sum_le_sum fun J _ => hword J
        _ ≤ 2 ^ n * (n.choose u * g ^ (s + 1)) := mul_le_mul_of_nonneg_left hcore (by positivity)
    have hu2 : (2 : ℝ) ^ u * 2 ^ (n - u) = 2 ^ n := by rw [← pow_add]; congr 1; omega
    have hWpos : (0 : ℝ) < #W := by
      rw [hW]; exact mul_pos (by exact_mod_cast Nat.choose_pos hun) (by positivity)
    rw [div_le_iff₀ hWpos, hW]
    refine le_of_mul_le_mul_left (hcount.trans_eq ?_) (by positivity : (0 : ℝ) < 2 ^ u)
    rw [← hu2]; ring
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
    have hk8 : (256 : ℝ) ≤ (k : ℝ) ^ 8 :=
      (by norm_num : (256 : ℝ) = 2 ^ 8).trans_le (pow_le_pow_left₀ (by norm_num) hk2 8)
    have hu' : (u : ℝ) * 1024 ≤ u * k ^ 10 := mul_le_mul_of_nonneg_left
      ((by norm_num : (1024 : ℝ) = 2 ^ 10).trans_le (pow_le_pow_left₀ (by norm_num) hk2 10))
      (by positivity)
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
      _ ≤ (k ^ 2 * u) * ((k : ℝ) ^ 8 * (((n - u : ℕ) : ℝ) + 1) ^ 2) := by gcongr
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
