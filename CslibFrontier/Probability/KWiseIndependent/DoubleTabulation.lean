/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Binary
public import CslibFrontier.Init
public import CslibFrontier.Probability.KWiseIndependent
import CslibFrontier.Foundations.Data.BitString.Sum
import CslibFrontier.Foundations.Data.Nat.SummationByParts
import CslibFrontier.Probability.Uniform
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Sort
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Double Tabulation and High Independence (`[Thorup2013]`)

This module formalizes the double tabulation hash family and its universal `k`-uniqueness analysis
following Mikkel Thorup, *"Simple Tabulation, Fast Expanders, Double Tabulation, and High
Independence"*, *Proc. 54th IEEE Symposium on Foundations of Computer Science (FOCS 2013)*,
pp. 90–99, 2013 (`arXiv:1311.3121v2`, 16 October 2018) [Thorup2013].

Given keys split into `c` characters from `Φ = Fin (2 ^ b)`, a first-level simple tabulation table
`T₁ : Fin c → Fin d → Fin (2 ^ b) → Fin (2 ^ b)` maps each key `x : Fin c → Fin (2 ^ b)` to an
intermediate `d`-tuple `simpleTabTuple T₁ x : Fin d → Fin (2 ^ b)` by XORing the `c` character
table lookups in each output coordinate `j : Fin d`. Composing `simpleTabTuple T₁` with an
independent second-level simple tabulation table `T₂ : Fin d → Fin (2 ^ b) → Fin (2 ^ M)` yields
the double tabulation hash `doubleTabHash c d b U M T₁ T₂ : Fin U → Fin (2 ^ M)`.

## Source statements and notation mapping

In Thorup [Thorup2013] (`arXiv:1311.3121v2`):
* **`k`-uniqueness (`IsKUnique`, Section 1.1, p. 4)**: For an output alphabet `Ψ = Fin (2 ^ b)`, a
  function `f : U → Ψ ^ d` is *`k`-unique* if every non-empty subset `X ⊆ U` of size `|X| ≤ k` has a
  unique output position character `(j₀, f(x₀)_{j₀})`, i.e., some `x₀ ∈ X` and `j₀ ∈ [d]` such that
  `f(x₀)_{j₀} ≠ f(x)_{j₀}` for all `x ∈ X \ {x₀}`.
* **Siegel's peeling lemma (`isKWiseIndependentHash_of_isKUnique`, Section 1.1, Lemma 2, p. 5;
  Appendix A, p. 19)**: If `f : α → (Fin d → β)` is `k`-unique and `r : Fin d → β → Fin (2 ^ M)` is
  a uniformly random simple tabulation table, then `r ∘ f : α → Fin (2 ^ M)` is `k`-wise
  independent (`IsKWiseIndependentHash k`).
* **Derivable output characters and efficient coding (Section 2, Definition 6, pp. 9–10;
  Eqs. (6)–(7), p. 11)**: For a list `L` of `ℓ` distinct input position characters in
  `[c] × Φ`, an output index `(α, j) ∈ L × [d]` is *derivable* if there exist `x, y ∈ X` whose
  symmetric difference `A = x △ y ⊆ L` has `α` as its last element in `L` and satisfies
  `h(x)_j = h(y)_j` (equivalently `h(α)_j = ⨁_{β ∈ A \ {α}} h(β)_j`). Fixing `L` (`≤ (c |Φ|) ^ ℓ`
  choices) and `q ℓ` equations `(A_r, j_r)` (`≤ (ℓ ^ (2 c) d) ^ (q ℓ)` choices) with distinct
  last-in-`L` output indices determines `q ℓ` entries of `T₁` in terms of earlier entries in `L`,
  leaving at most `|Θ_top| / |Ψ| ^ (q ℓ)` compatible tables `T₁` (Eqs. (6)–(7), p. 11).
* **Many derivable output characters (Section 3, Theorem 7(a) and Lemma 8, p. 12; Lemma 9 and
  Eqs. (8)–(11), pp. 12–13)**: For a violating set `X` (`|X| ≤ k`), order its `ℓ* ≤ c |X|` active
  input position characters `α₁, …, α_{ℓ*}` by decreasing frequency `n₁ ≥ … ≥ n_{ℓ*} ≥ 1`
  (`∑ n_i = c |X|`). Letting `γ_{≤ ℓ}` count pairs `(x, j) ∈ X × [d]` whose symmetric-difference
  witness `x △ y` with `h(x)_j = h(y)_j` lies in the prefix `L_{≤ ℓ} = {α₁, …, α_ℓ}` and letting
  `ϕ_ℓ` count derivable output indices `(α_ℓ, j)` at step `ℓ`, Lemma 8 (p. 12) gives
  `γ_{≤ ℓ*} = d |X|` and Lemma 9 (Eq. (8), p. 12) gives `γ_{≤ ℓ} - γ_{≤ ℓ - 1} ≤ 2 ϕ_ℓ n_ℓ`. By
  summation by parts (Eqs. (9)–(11), pp. 12–13), when `d = 2 q c`, some prefix `L_{≤ ℓ}`
  (`2 ≤ ℓ ≤ c k`) has `∑_{i=1}^ℓ ϕ_i ≥ q ℓ` derivable output characters.
* **Original adaptations**:
  - In Theorem 1(a) and Section 2 (pp. 4, 11), Thorup states the failure probability asymptotically
    as `o(|Φ| ^ 2 / |Ψ| ^ (d / (2 c)))` under `c = |Φ| ^ o(1)` and `(c + d) ^ c = |Ψ| ^ o(1)`.
    Here `card_not_isKUnique_le` and `card_not_isKUnique_eight_mul_le` establish an explicit
    non-asymptotic finite-seed bound for all `c, q, b ≥ 1` and `d = 2 q c` whenever
    `2 * (c * ((c * k) ^ (2 * c) * d) ^ q) ≤ 2 ^ ((q - 1) * b)`.
  - Each non-empty symmetric difference `A ⊆ range(L)` of size `|A| ≤ 2 c` is parameterized in
    Section 4 by a tuple `g : Fin (2 * c) → Fin ℓ` whose image in `Fin ℓ` has maximum index
    `lastIdx g`, giving an exact `Fintype.card` count `(ℓ ^ (2 * c) * d) ^ (q * ℓ)`.

## Main definitions

* `Cslib.Probability.IsKUnique`: `k`-uniqueness of a tuple-valued function `f : α → Fin d → β`
  ([Thorup2013], Section 1.1, p. 4).
* `Cslib.Probability.simpleTabAddHom`, `Cslib.Probability.simpleTabEval`: simple tabulation over an
  additive commutative group and over `Fin (2 ^ M)` via bitwise XOR (`BitString.equivFin M`).
* `Cslib.Probability.charDigits`: base-`2 ^ b` character extraction `Fin U → Fin c → Fin (2 ^ b)`.
* `Cslib.Probability.simpleTabTuple`: first-level simple tabulation
  `(Fin c → Fin d → Fin (2 ^ b) → Fin (2 ^ b)) → (Fin c → Fin (2 ^ b)) → (Fin d → Fin (2 ^ b))`.
* `Cslib.Probability.DoubleTabTopSeed`, `Cslib.Probability.DoubleTabBotSeed`,
  `Cslib.Probability.doubleTabHash`, `Cslib.Probability.doubleTabCodeBound`,
  `Cslib.Probability.doubleTabMinB`, `Cslib.Probability.doubleTabThreshold`: seed types, composed
  double tabulation hash `Fin U → Fin (2 ^ M)`, per-step code-counting factor
  `c * ((c * k) ^ (2 * c) * d) ^ q`, minimum character bit-width `doubleTabMinB c_exp`, and
  capacity threshold `doubleTabThreshold c_exp = 2 ^ (2 * doubleTabMinB c_exp)`.

## Main results

* `Cslib.Probability.isKWiseIndependentHash_of_isKUnique`: Siegel's peeling lemma ([Thorup2013],
  Lemma 2, p. 5 & Appendix A, p. 19).
* `Cslib.Probability.charDigits_injective`: `charDigits c b` is injective when `U ≤ 2 ^ (c * b)`.
* `Cslib.Probability.isKWiseIndependentHash_doubleTabHash_of_isKUnique`: when `T₁` is `k`-unique and
  `U ≤ 2 ^ (c * b)`, `T₂ ↦ doubleTabHash c d b U M T₁ T₂` is `k`-wise independent.
* `Cslib.Probability.card_not_isKUnique_le`,
  `Cslib.Probability.card_not_isKUnique_eight_mul_le`,
  `Cslib.Probability.four_le_doubleTabThreshold`: explicit universal `k`-uniqueness bounds for
  `simpleTabTuple T₁` ([Thorup2013], Theorem 1(a), Section 2 Eqs. (6)–(7), Section 3 Theorem 7(a)
  and Lemmas 8–9) and threshold lower bound `4 ≤ doubleTabThreshold c_exp`.

## References

* [M. Thorup, *Simple Tabulation, Fast Expanders, Double Tabulation,
  and High Independence*][Thorup2013]
-/

public section

namespace Cslib.Probability

open BitString Finset
open scoped BigOperators

/-! ## Section 1: `k`-uniqueness and Siegel's peeling lemma -/

/-- **`k`-uniqueness** ([Thorup2013], Section 1.1, p. 4): a tuple map `f : α → Fin d → β` is
`k`-unique if every non-empty subset `X ⊆ α` of size `#X ≤ k` contains a key `x₀ ∈ X` and output
coordinate `j₀ : Fin d` whose value `f x₀ j₀` differs from `f x j₀` for all other `x ∈ X`. -/
@[expose] def IsKUnique {α β : Type*} {d : ℕ} (k : ℕ) (f : α → Fin d → β) : Prop :=
  ∀ X : Finset α, X.Nonempty → #X ≤ k →
    ∃ x₀ ∈ X, ∃ j₀ : Fin d, ∀ x ∈ X, x ≠ x₀ → f x₀ j₀ ≠ f x j₀

instance {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β] {d : ℕ} (k : ℕ)
    (f : α → Fin d → β) : Decidable (IsKUnique k f) :=
  decidable_of_iff
    (∀ X ∈ (Finset.univ : Finset α).powerset, 0 < #X → #X ≤ k →
      ∃ x₀ ∈ X, ∃ j₀ : Fin d, ∀ x ∈ X, x ≠ x₀ → f x₀ j₀ ≠ f x j₀)
    ⟨fun h X hne hX => h X (Finset.mem_powerset.mpr (Finset.subset_univ X))
      (Finset.card_pos.mpr hne) hX,
     fun h X _ hpos hX => h X (Finset.card_pos.mp hpos) hX⟩

/-- Monotonicity of `IsKUnique` in `k`: if `f` is `k`-unique and `k' ≤ k`, then `f` is
`k'`-unique. -/
theorem IsKUnique.mono {α β : Type*} {d k k' : ℕ} {f : α → Fin d → β}
    (hf : IsKUnique k f) (hk : k' ≤ k) : IsKUnique k' f :=
  fun X hne hX => hf X hne (hX.trans hk)

/-- Precomposing a `k`-unique function `f : α → Fin d → β` with an injective map `g : α' → α`
preserves `k`-uniqueness. -/
theorem IsKUnique.comp_injective {α' α β : Type*} {d k : ℕ} {f : α → Fin d → β}
    (hf : IsKUnique k f) {g : α' → α} (hg : Function.Injective g) :
    IsKUnique k (fun x => f (g x)) := by
  classical
  intro X hne hX
  obtain ⟨y₀, hy₀, j₀, huniq⟩ := hf (X.image g) (hne.image g) (Finset.card_image_le.trans hX)
  obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hy₀
  exact ⟨x₀, hx₀, j₀, fun x hx hne_x =>
    huniq (g x) (Finset.mem_image_of_mem g hx) (hg.ne hne_x)⟩

/-- Simple tabulation evaluation over an additive commutative group `γ` as an additive homomorphism
`(Fin d → β → γ) →+ (α → γ)`. -/
@[expose] def simpleTabAddHom {α β γ : Type*} [AddCommGroup γ] {d : ℕ}
    (f : α → Fin d → β) : (Fin d → β → γ) →+ (α → γ) where
  toFun r x := ∑ j : Fin d, r j (f x j)
  map_zero' := by ext x; simp
  map_add' r₁ r₂ := by ext x; simp [Finset.sum_add_distrib]

/-- Simple tabulation evaluation over `Fin (2 ^ M)`, XORing `(r j (y j)).val` across `j : Fin d` via
`BitString.equivFin M`. -/
@[expose] def simpleTabEval {β : Type*} {d M : ℕ}
    (r : Fin d → β → Fin (2 ^ M)) (y : Fin d → β) : Fin (2 ^ M) :=
  BitString.equivFin M (∑ j : Fin d, (BitString.equivFin M).symm (r j (y j)))

/-- General peeling surjectivity over an additive commutative group: if every non-empty subset
`S ⊆ T` has an element `x₀ ∈ S` and a variable `u₀ ∈ supp x₀` absent from `supp x` for all
`x ∈ S \ {x₀}`, then restricting the subset-sum map `w ↦ fun x => ∑ u ∈ supp x, w u` to `T` is
surjective. -/
private theorem surjective_restrict_sum_of_peeling {α κ γ : Type*}
    [AddCommGroup γ] (supp : α → Finset κ) {T : Finset α}
    (hpeel : ∀ S ⊆ T, S.Nonempty → ∃ x₀ ∈ S, ∃ u₀ ∈ supp x₀, ∀ x ∈ S, x ≠ x₀ → u₀ ∉ supp x) :
    Function.Surjective (fun (w : κ → γ) => T.restrict (fun x => ∑ u ∈ supp x, w u)) := by
  classical
  induction hn : #T generalizing T with
  | zero =>
    obtain rfl := Finset.card_eq_zero.mp hn
    exact fun _ => ⟨0, funext fun ⟨x, hx⟩ => (Finset.notMem_empty x hx).elim⟩
  | succ n ih =>
    intro y
    obtain ⟨x₀, hx₀, u₀, hu₀, huniq⟩ :=
      hpeel T Finset.Subset.rfl (Finset.card_pos.mp (by omega))
    have hcard : #(T.erase x₀) = n := by rw [Finset.card_erase_of_mem hx₀, hn, Nat.add_sub_cancel]
    obtain ⟨w', hw'⟩ := ih (fun S hS => hpeel S (hS.trans (Finset.erase_subset x₀ T))) hcard
      (fun x => y ⟨x.val, Finset.mem_of_mem_erase x.property⟩)
    let δ : γ := y ⟨x₀, hx₀⟩ - ∑ u ∈ supp x₀, w' u
    refine ⟨fun u => w' u + if u = u₀ then δ else 0, funext fun ⟨x, hx⟩ => ?_⟩
    change ∑ u ∈ supp x, (w' u + if u = u₀ then δ else 0) = y ⟨x, hx⟩
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (supp x) u₀]
    by_cases hxx₀ : x = x₀
    · subst hxx₀; simp [hu₀, δ]
    · rw [ite_eq_right (huniq x hx hxx₀), add_zero]
      exact congrFun hw' ⟨x, Finset.mem_erase.mpr ⟨hxx₀, hx⟩⟩

/-- **Siegel's Peeling Lemma ([Thorup2013], Section 1.1, Lemma 2, p. 5 & Appendix A, p. 19)**:
If `f : α → Fin d → β` is `k`-unique (`IsKUnique k f`), then composing `f` with a uniformly random
simple tabulation table `r : Fin d → β → Fin (2 ^ M)` yields a `k`-wise independent hash family
`α → Fin (2 ^ M)`. -/
theorem isKWiseIndependentHash_of_isKUnique {α β : Type*} [Fintype β] [DecidableEq β]
    {d M k : ℕ} {f : α → Fin d → β} (hf : IsKUnique k f) :
    IsKWiseIndependentHash k (fun (r : Fin d → β → Fin (2 ^ M)) (x : α) =>
      simpleTabEval r (f x)) := by
  have hbits : IsKWiseIndependentHash k
      (fun r : Fin d → β → BitString M => simpleTabAddHom f r) := by
    refine isKWiseIndependentHash_of_surjective (simpleTabAddHom (γ := BitString M) f)
      fun T hT y => ?_
    let supp (x : α) : Finset (Fin d × β) := Finset.univ.image fun j => (j, f x j)
    obtain ⟨w, hw⟩ := surjective_restrict_sum_of_peeling supp (T := T) (fun S hS hSne => by
      obtain ⟨x₀, hx₀, j₀, huniq⟩ := hf S hSne ((Finset.card_le_card hS).trans hT)
      refine ⟨x₀, hx₀, (j₀, f x₀ j₀), Finset.mem_image_of_mem _ (Finset.mem_univ _),
        fun x hx hne hmem => ?_⟩
      obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hmem
      exact huniq x hx hne ((Prod.mk.inj hj).1 ▸ (Prod.mk.inj hj).2.symm)) y
    refine ⟨fun j b => w (j, b), hw.symm.trans (funext fun ⟨x, _⟩ => ?_) |>.symm⟩
    exact Finset.sum_image (f := fun u : Fin d × β => w (u.1, u.2)) fun _ _ _ _ h =>
      congrArg Prod.fst h
  exact (hbits.comp_seedEquiv
    (Equiv.piCongrRight fun _ : Fin d =>
      Equiv.piCongrRight fun _ : β => (BitString.equivFin M).symm)).map_equiv
    (BitString.equivFin M)

/-! ## Section 2: Base-`2 ^ b` character extraction and double tabulation -/

/-- Base-`2 ^ b` character extraction: splits `u : Fin U` into `c` characters in `Fin (2 ^ b)` via
`(u.val >>> (i.val * b)) &&& (2 ^ b - 1)`. -/
@[expose] def charDigits (c b : ℕ) {U : ℕ} (u : Fin U) (i : Fin c) : Fin (2 ^ b) :=
  ⟨(u.val >>> (i.val * b)) &&& (2 ^ b - 1), by
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (Nat.two_pow_pos b)⟩

/-- **Injectivity of `charDigits`**: when `U ≤ 2 ^ (c * b)`, distinct keys in `Fin U` have distinct
`c`-tuples of `b`-bit characters. -/
theorem charDigits_injective {c b U : ℕ} (hU : U ≤ 2 ^ (c * b)) :
    Function.Injective (charDigits c b (U := U)) := by
  intro u₁ u₂ heq
  apply Fin.ext
  apply Nat.eq_of_testBit_eq; intro t
  by_cases ht : t < c * b
  · have hb : 0 < b := Nat.pos_of_ne_zero fun h => by simp [h] at ht
    have hi : t / b < c := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
    simpa only [charDigits, Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.mod_lt t hb,
      decide_true, Bool.and_true, Nat.testBit_shiftRight, Nat.mul_comm (t / b) b,
      Nat.div_add_mod] using congrArg (fun f => (f ⟨t / b, hi⟩).val.testBit (t % b)) heq
  · have hlt (u : Fin U) : u.val < 2 ^ t :=
      u.isLt.trans_le (hU.trans (Nat.pow_le_pow_right two_pos (not_lt.mp ht)))
    rw [Nat.testBit_lt_two_pow (hlt u₁), Nat.testBit_lt_two_pow (hlt u₂)]

/-- Top-level simple tabulation seed space `Fin c → Fin d → Fin (2 ^ b) → Fin (2 ^ b)`. -/
abbrev DoubleTabTopSeed (c d b : ℕ) : Type :=
  Fin c → Fin d → Fin (2 ^ b) → Fin (2 ^ b)

/-- Bottom-level simple tabulation seed space `Fin d → Fin (2 ^ b) → Fin (2 ^ M)`. -/
abbrev DoubleTabBotSeed (d b M : ℕ) : Type :=
  Fin d → Fin (2 ^ b) → Fin (2 ^ M)

/-- First-level simple tabulation (`[Thorup2013]`, Eq. (2), p. 3 & Theorem 1, p. 4): maps each
character tuple `x : Fin c → Fin (2 ^ b)` to an intermediate `d`-tuple `Fin d → Fin (2 ^ b)` by
XORing `T₁ i j (x i)` across `i : Fin c` in each output coordinate `j : Fin d`. -/
@[expose] def simpleTabTuple {c d b : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (x : Fin c → Fin (2 ^ b)) (j : Fin d) : Fin (2 ^ b) :=
  simpleTabEval (fun i a => T₁ i j a) x

/-- **Mikkel Thorup's Double Tabulation hash function ([Thorup2013], Section 1.1, p. 5)**:
extracts `c` base-`2 ^ b` characters from `u : Fin U`, applies `simpleTabTuple T₁` to obtain `d`
intermediate `b`-bit characters, and applies `simpleTabEval T₂` to produce an `M`-bit hash in
`Fin (2 ^ M)`. -/
@[expose] def doubleTabHash (c d b U M : ℕ)
    (T₁ : DoubleTabTopSeed c d b) (T₂ : DoubleTabBotSeed d b M) (u : Fin U) : Fin (2 ^ M) :=
  simpleTabEval T₂ (simpleTabTuple T₁ (charDigits c b u))

/-- When the top-level table `T₁` is `k`-unique (`IsKUnique k (simpleTabTuple T₁)`) and
`U ≤ 2 ^ (c * b)`, the bottom-level family `fun T₂ => doubleTabHash c d b U M T₁ T₂` is `k`-wise
independent ([Thorup2013], Section 1.1, Lemma 2, p. 5). -/
theorem isKWiseIndependentHash_doubleTabHash_of_isKUnique {c d b U M k : ℕ}
    {T₁ : DoubleTabTopSeed c d b} (hU : U ≤ 2 ^ (c * b))
    (huniq : IsKUnique k (simpleTabTuple T₁)) :
    IsKWiseIndependentHash k (fun T₂ : DoubleTabBotSeed d b M => doubleTabHash c d b U M T₁ T₂) :=
  isKWiseIndependentHash_of_isKUnique (huniq.comp_injective (charDigits_injective hU))

/-! ## Section 3: Position-character sets, symmetric differences, and `BitString` XOR laws -/

/-- Set of `c` input position characters `{(i, x i) | i : Fin c}` of a key `x : Fin c → Fin (2 ^ b)`
([Thorup2013], Section 2, p. 9). -/
private def posSet {c b : ℕ} (x : Fin c → Fin (2 ^ b)) : Finset (Fin c × Fin (2 ^ b)) :=
  Finset.univ.image fun i : Fin c => (i, x i)

@[simp]
private theorem mem_posSet {c b : ℕ} {x : Fin c → Fin (2 ^ b)} {α : Fin c × Fin (2 ^ b)} :
    α ∈ posSet x ↔ x α.1 = α.2 := by
  simp only [posSet, Finset.mem_image, Finset.mem_univ, true_and, Prod.ext_iff]
  exact ⟨fun ⟨i, hi, hx⟩ => hi ▸ hx, fun h => ⟨α.1, rfl, h⟩⟩

@[simp]
private theorem card_posSet {c b : ℕ} (x : Fin c → Fin (2 ^ b)) : #(posSet x) = c := by
  rw [posSet, Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h),
    Finset.card_univ, Fintype.card_fin]

/-- Symmetric difference `x △ y = symmDiff (posSet x) (posSet y)` of two keys' position-character
sets ([Thorup2013], Definition 6, p. 10). -/
private def posSymmDiff {c b : ℕ} (x y : Fin c → Fin (2 ^ b)) : Finset (Fin c × Fin (2 ^ b)) :=
  symmDiff (posSet x) (posSet y)

private theorem card_posSymmDiff_le {c b : ℕ} (x y : Fin c → Fin (2 ^ b)) :
    #(posSymmDiff x y) ≤ 2 * c :=
  (Finset.card_le_card symmDiff_subset_union).trans <|
    (Finset.card_union_le _ _).trans_eq (by rw [card_posSet, card_posSet, two_mul])

/-- Any two distinct keys `x ≠ y` differ in at least one coordinate `i : Fin c`, contributing two
distinct position characters `(i, x i) ≠ (i, y i)` to `posSymmDiff x y`. -/
private theorem two_le_card_posSymmDiff_of_ne {c b : ℕ} {x y : Fin c → Fin (2 ^ b)} (hne : x ≠ y) :
    2 ≤ #(posSymmDiff x y) := by
  obtain ⟨i, hxy⟩ := Function.ne_iff.mp hne
  exact Finset.one_lt_card_iff.mpr ⟨(i, x i), (i, y i),
    Finset.mem_symmDiff.mpr (Or.inl ⟨mem_posSet.mpr rfl, mt mem_posSet.mp hxy.symm⟩),
    Finset.mem_symmDiff.mpr (Or.inr ⟨mem_posSet.mpr rfl, mt mem_posSet.mp hxy⟩),
    fun h => hxy (congrArg Prod.snd h)⟩

/-- Triangle inclusion for symmetric difference of position-character sets:
`posSymmDiff y z ⊆ posSymmDiff x y ∪ posSymmDiff x z`. -/
private theorem posSymmDiff_subset_union {c b : ℕ} (x y z : Fin c → Fin (2 ^ b)) :
    posSymmDiff y z ⊆ posSymmDiff x y ∪ posSymmDiff x z := by
  intro α hα
  simp only [posSymmDiff, Finset.mem_union, Finset.mem_symmDiff] at hα ⊢
  by_cases hx : α ∈ posSet x <;> tauto

/-- Two keys `x, y` collide in coordinate `j` under `simpleTabTuple T₁` iff the `BitString b` sum of
`T₁` over `posSymmDiff x y` is `0` ([Thorup2013], Definition 6, p. 10). -/
private theorem simpleTabTuple_eq_iff_sum_posSymmDiff_eq_zero {c d b : ℕ}
    (T₁ : DoubleTabTopSeed c d b) (x y : Fin c → Fin (2 ^ b)) (j : Fin d) :
    simpleTabTuple T₁ x j = simpleTabTuple T₁ y j ↔
      ∑ α ∈ posSymmDiff x y, (BitString.equivFin b).symm (T₁ α.1 j α.2) = 0 := by
  have hsum (z : Fin c → Fin (2 ^ b)) :
      ∑ α ∈ posSet z, (BitString.equivFin b).symm (T₁ α.1 j α.2) =
        ∑ i : Fin c, (BitString.equivFin b).symm (T₁ i j (z i)) :=
    Finset.sum_image fun _ _ _ _ h => congrArg Prod.fst h
  rw [simpleTabTuple, simpleTabTuple, simpleTabEval, simpleTabEval,
    (BitString.equivFin b).injective.eq_iff, ← hsum x, ← hsum y]
  exact sum_bitString_eq_iff_sum_symmDiff_eq_zero (posSet x) (posSet y) _

/-! ## Section 4: Derivable output characters and Theorem 7(a) (`[Thorup2013]`, §3) -/

/-- Maximum index in `Fin ℓ` attained by a tuple `g : Fin m → Fin ℓ` (`m > 0`). -/
private def lastIdx {m ℓ : ℕ} [NeZero m] (g : Fin m → Fin ℓ) : Fin ℓ :=
  (Finset.univ.image g).max' (Finset.univ_nonempty.image g)

private theorem lastIdx_mem_image {m ℓ : ℕ} [NeZero m] (g : Fin m → Fin ℓ) :
    lastIdx g ∈ Finset.univ.image g :=
  Finset.max'_mem _ _

/-- Predicate that `T₁` satisfies the efficient code `(L, M)` of length `ℓ` and `q * ℓ` equations
([Thorup2013], Section 2, Definition 6 & Eqs. (6)–(7), pp. 9–11). -/
private def SatisfiesCode {c d b q ℓ : ℕ} [NeZero (2 * c)]
    (T₁ : DoubleTabTopSeed c d b) (L : Fin ℓ → Fin c × Fin (2 ^ b))
    (M : Fin (q * ℓ) → (Fin (2 * c) → Fin ℓ) × Fin d) : Prop :=
  Function.Injective L ∧
    Function.Injective (fun r : Fin (q * ℓ) => (lastIdx (M r).1, (M r).2)) ∧
    ∀ r : Fin (q * ℓ),
      ∑ idx ∈ Finset.univ.image (M r).1,
        (BitString.equivFin b).symm (T₁ (L idx).1 (M r).2 (L idx).2) = 0

private instance {c d b q ℓ : ℕ} [NeZero (2 * c)]
    (T₁ : DoubleTabTopSeed c d b) (L : Fin ℓ → Fin c × Fin (2 ^ b))
    (M : Fin (q * ℓ) → (Fin (2 * c) → Fin ℓ) × Fin d) :
    Decidable (SatisfiesCode T₁ L M) := by
  unfold SatisfiesCode
  infer_instance

/-- Frequency `n_α = #{x ∈ X | α ∈ posSet x}` of an input position character `α` in `X`
([Thorup2013], Section 3, p. 11). -/
private def freq {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b)))
    (α : Fin c × Fin (2 ^ b)) : ℕ :=
  #(X.filter fun x => α ∈ posSet x)

/-- Active input position characters `⋃_{x ∈ X} posSet x` of `X` ([Thorup2013], Section 3,
p. 11). -/
private def activeChars {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b))) :
    Finset (Fin c × Fin (2 ^ b)) :=
  X.biUnion posSet

/-- Active input position characters of `X` sorted in decreasing order of frequency `freq X`
([Thorup2013], Section 3, p. 11). -/
private noncomputable def sortedChars {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b))) :
    List (Fin c × Fin (2 ^ b)) :=
  (activeChars X).toList.mergeSort (fun α β => decide (freq X β ≤ freq X α))

/-- First `r` active input position characters `L_{≤ r}` of `sortedChars X` as a finset. -/
private noncomputable def prefixChars {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b))) (r : ℕ) :
    Finset (Fin c × Fin (2 ^ b)) :=
  ((sortedChars X).take r).toFinset

private theorem nodup_sortedChars {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b))) :
    (sortedChars X).Nodup :=
  (List.mergeSort_perm (activeChars X).toList _).nodup_iff.mpr (Finset.nodup_toList _)

private theorem length_sortedChars {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b))) :
    (sortedChars X).length = #(activeChars X) := by
  rw [sortedChars, List.length_mergeSort, Finset.length_toList]

private theorem mem_sortedChars {c b : ℕ} {X : Finset (Fin c → Fin (2 ^ b))}
    {α : Fin c × Fin (2 ^ b)} :
    α ∈ sortedChars X ↔ α ∈ activeChars X := by
  rw [sortedChars, List.mem_mergeSort, Finset.mem_toList]

private theorem card_activeChars_le {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b))) :
    #(activeChars X) ≤ c * #X := by
  refine Finset.card_biUnion_le.trans ?_
  simp [card_posSet, Nat.mul_comm]

private theorem sum_freq_activeChars {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b))) :
    ∑ α ∈ activeChars X, freq X α = c * #X := by
  simp only [freq, Finset.card_filter]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun x hx => by
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr
      (show posSet x ⊆ activeChars X from Finset.subset_biUnion_of_mem posSet hx), card_posSet]]
  simp [Nat.mul_comm]

private theorem pairwise_sortedChars {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b))) :
    (sortedChars X).Pairwise (fun α β => freq X β ≤ freq X α) :=
  letI : Std.Total (fun α β : Fin c × Fin (2 ^ b) => freq X β ≤ freq X α) :=
    ⟨fun _ _ => le_total _ _⟩
  letI : IsTrans (Fin c × Fin (2 ^ b)) (fun α β => freq X β ≤ freq X α) :=
    ⟨fun _ _ _ h₁ h₂ => h₂.trans h₁⟩
  List.pairwise_mergeSort' (fun α β => freq X β ≤ freq X α) (activeChars X).toList

/-- `i`-th frequency `n_i` in the decreasing order `sortedChars X` (`0` out of bounds). -/
private noncomputable def sortedFreq {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b))) (i : ℕ) : ℕ :=
  if hi : i < (sortedChars X).length then freq X ((sortedChars X)[i]) else 0

private theorem sortedFreq_antitone {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b)))
    {i j : ℕ} (hj : j < (sortedChars X).length) (hij : i ≤ j) :
    sortedFreq X j ≤ sortedFreq X i := by
  have hi : i < (sortedChars X).length := lt_of_le_of_lt hij hj
  simp only [sortedFreq, hi, hj, ↓reduceDIte]
  rcases eq_or_lt_of_le hij with rfl | hlt
  exacts [le_rfl, List.pairwise_iff_getElem.mp (pairwise_sortedChars X) i j hi hj hlt]

private theorem one_le_sortedFreq {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b)))
    {i : ℕ} (hi : i < (sortedChars X).length) :
    1 ≤ sortedFreq X i := by
  simp only [sortedFreq, hi, ↓reduceDIte]
  obtain ⟨x, hx, hxα⟩ := Finset.mem_biUnion.mp (mem_sortedChars.mp (List.getElem_mem hi))
  exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hxα⟩⟩

private theorem sum_sortedFreq {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b))) :
    ∑ i ∈ Finset.range (sortedChars X).length, sortedFreq X i = c * #X := by
  rw [← Fin.sum_univ_eq_sum_range]
  have hget : (∑ i : Fin (sortedChars X).length, sortedFreq X i) =
      ((sortedChars X).map (freq X)).sum := by
    conv_rhs => rw [← List.ofFn_get (sortedChars X), List.map_ofFn, List.sum_ofFn]
    exact Finset.sum_congr rfl fun i _ => by simp [sortedFreq, i.isLt]
  rw [hget, sortedChars, ((List.mergeSort_perm (activeChars X).toList _).map (freq X)).sum_eq,
    Finset.sum_map_toList, sum_freq_activeChars]

private theorem card_prefixChars_le {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b))) (r : ℕ) :
    #(prefixChars X r) ≤ r :=
  (List.toFinset_card_le _).trans (List.length_take_le r _)

private theorem prefixChars_length {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b))) :
    prefixChars X (sortedChars X).length = activeChars X := by
  ext α; simp [prefixChars, List.take_length, mem_sortedChars]

private theorem prefixChars_succ {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b))) {r : ℕ}
    (hr : r < (sortedChars X).length) :
    prefixChars X (r + 1) = insert ((sortedChars X)[r]) (prefixChars X r) := by
  ext α
  simp only [prefixChars, List.mem_toFinset, List.take_add_one, List.mem_append,
    List.getElem?_eq_getElem hr, Option.toList_some, List.mem_singleton, Finset.mem_insert]
  exact Or.comm

private theorem prefixChars_mono {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b))) {r₁ r₂ : ℕ}
    (h : r₁ ≤ r₂) : prefixChars X r₁ ⊆ prefixChars X r₂ := fun _ hα => by
  simp only [prefixChars, List.mem_toFinset] at hα ⊢
  exact List.Sublist.mem hα (List.take_sublist_take_left h)

/-- A character of the prefix `L_{≤ r}` is `(sortedChars X)[i]` for some index `i < r`. -/
private theorem exists_lt_of_mem_prefixChars {c b : ℕ} {X : Finset (Fin c → Fin (2 ^ b))}
    {r : ℕ} {α : Fin c × Fin (2 ^ b)} (hα : α ∈ prefixChars X r) :
    ∃ (i : ℕ) (hi : i < (sortedChars X).length), i < r ∧ (sortedChars X)[i] = α := by
  simp only [prefixChars, List.mem_toFinset, List.mem_take_iff_getElem] at hα
  obtain ⟨i, hi, heq⟩ := hα
  exact ⟨i, lt_of_lt_of_le hi (Nat.min_le_right _ _), lt_of_lt_of_le hi (Nat.min_le_left _ _), heq⟩

/-- Set `Γ_{≤ r}` of pairs `(y, j) ∈ X × Fin d` whose output `simpleTabTuple T₁ y j` collides with
some `x ∈ X \ {y}` such that `posSymmDiff x y ⊆ prefixChars X r` ([Thorup2013], Section 3,
p. 11). -/
private noncomputable def GammaSet {c d b : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (X : Finset (Fin c → Fin (2 ^ b))) (r : ℕ) :
    Finset ((Fin c → Fin (2 ^ b)) × Fin d) :=
  (X ×ˢ Finset.univ).filter fun p =>
    ∃ x ∈ X, x ≠ p.1 ∧ posSymmDiff x p.1 ⊆ prefixChars X r ∧
      simpleTabTuple T₁ x p.2 = simpleTabTuple T₁ p.1 p.2

@[simp]
private theorem mem_gammaSet {c d b : ℕ} {T₁ : DoubleTabTopSeed c d b}
    {X : Finset (Fin c → Fin (2 ^ b))} {r : ℕ} {p : (Fin c → Fin (2 ^ b)) × Fin d} :
    p ∈ GammaSet T₁ X r ↔ p.1 ∈ X ∧ ∃ x ∈ X, x ≠ p.1 ∧ posSymmDiff x p.1 ⊆ prefixChars X r ∧
      simpleTabTuple T₁ x p.2 = simpleTabTuple T₁ p.1 p.2 := by
  simp [GammaSet]

/-- Count `γ_{≤ r} = #(GammaSet T₁ X r)` ([Thorup2013], Section 3, p. 11). -/
private noncomputable def gamma {c d b : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (X : Finset (Fin c → Fin (2 ^ b))) (r : ℕ) : ℕ :=
  #(GammaSet T₁ X r)

private theorem gammaSet_mono {c d b : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (X : Finset (Fin c → Fin (2 ^ b))) {r₁ r₂ : ℕ} (h : r₁ ≤ r₂) :
    GammaSet T₁ X r₁ ⊆ GammaSet T₁ X r₂ := by
  rintro p; simp only [mem_gammaSet]
  rintro ⟨hpX, x, hxX, hne, hsub, heq⟩
  exact ⟨hpX, x, hxX, hne, hsub.trans (prefixChars_mono X h), heq⟩

private theorem gamma_eq_zero_of_le_one {c d b : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (X : Finset (Fin c → Fin (2 ^ b))) {r : ℕ} (hr : r ≤ 1) :
    gamma T₁ X r = 0 := by
  rw [gamma, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  rintro p hp
  rcases mem_gammaSet.mp hp with ⟨_, x, _, hne, hsub, _⟩
  have := two_le_card_posSymmDiff_of_ne hne
  have := (Finset.card_le_card hsub).trans ((card_prefixChars_le X r).trans hr)
  omega

/-- **Lemma 8 ([Thorup2013], Section 3, p. 12)**: if `X` violates `k`-uniqueness under
`simpleTabTuple T₁`, then `γ_{≤ ℓ*} = d * #X`. -/
private theorem gamma_length_eq {c d b : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (X : Finset (Fin c → Fin (2 ^ b)))
    (hviol : ∀ y ∈ X, ∀ j : Fin d, ∃ x ∈ X, x ≠ y ∧
      simpleTabTuple T₁ y j = simpleTabTuple T₁ x j) :
    gamma T₁ X (sortedChars X).length = d * #X := by
  have hGamma : GammaSet T₁ X (sortedChars X).length = X ×ˢ Finset.univ := by
    ext ⟨y, j⟩
    simp only [mem_gammaSet, Finset.mem_product, Finset.mem_univ, and_true, and_iff_left_iff_imp]
    intro hy
    obtain ⟨x, hx, hne, heq⟩ := hviol y hy j
    exact ⟨x, hx, hne, prefixChars_length X ▸ symmDiff_subset_union.trans
      (Finset.union_subset (Finset.subset_biUnion_of_mem posSet hx)
        (Finset.subset_biUnion_of_mem posSet hy)), heq.symm⟩
  rw [gamma, hGamma, Finset.card_product, Finset.card_univ, Fintype.card_fin, Nat.mul_comm]

/-- Set `Φ_r` of output coordinates `j : Fin d` such that `((sortedChars X)[r], j)` is derivable
from `prefixChars X (r + 1)` ([Thorup2013], Section 3, p. 12). -/
private noncomputable def PhiSet {c d b : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (X : Finset (Fin c → Fin (2 ^ b))) (r : ℕ) : Finset (Fin d) :=
  if hr : r < (sortedChars X).length then
    Finset.univ.filter fun j : Fin d =>
      ∃ x ∈ X, ∃ y ∈ X, (sortedChars X)[r] ∈ posSymmDiff x y ∧
        posSymmDiff x y ⊆ prefixChars X (r + 1) ∧
        simpleTabTuple T₁ x j = simpleTabTuple T₁ y j
  else ∅

/-- Count `ϕ_r = #(PhiSet T₁ X r)` of derivable output coordinates for `(sortedChars X)[r]`
([Thorup2013], Section 3, p. 12). -/
private noncomputable def phi {c d b : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (X : Finset (Fin c → Fin (2 ^ b))) (r : ℕ) : ℕ :=
  #(PhiSet T₁ X r)

private theorem phi_zero_eq_zero {c d b : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (X : Finset (Fin c → Fin (2 ^ b))) :
    phi T₁ X 0 = 0 := by
  simp only [phi, PhiSet, Finset.card_eq_zero]
  split_ifs with hr <;> simp only [Finset.filter_eq_empty_iff, Finset.mem_univ, forall_true_left]
  rintro j ⟨x, _, y, _, hmem, hsub, _⟩
  have := two_le_card_posSymmDiff_of_ne (x := x) (y := y)
    (by rintro rfl; simp [posSymmDiff] at hmem)
  have := (Finset.card_le_card hsub).trans (card_prefixChars_le X 1)
  omega

/-- A position-character set inside the prefix of length `r + 1` that misses the `r`-th sorted
character lies inside the prefix of length `r`. -/
private theorem subset_prefixChars_of_subset_succ {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b)))
    {r : ℕ} (hr : r < (sortedChars X).length) {A : Finset (Fin c × Fin (2 ^ b))}
    (hsub : A ⊆ prefixChars X (r + 1)) (hnot : (sortedChars X)[r] ∉ A) :
    A ⊆ prefixChars X r := fun β hβ =>
  (Finset.mem_insert.mp (prefixChars_succ X hr ▸ hsub hβ)).resolve_left
    (by rintro rfl; exact hnot hβ)

/-- A pair `p` that enters `Γ_{≤ r + 1}` at step `r` has a colliding key `x ≠ p.1` whose symmetric
difference with `p.1` contains the `r`-th sorted character; in particular `p.2 ∈ Φ_r`. -/
private theorem exists_witness_of_mem_gammaSet_sdiff {c d b : ℕ}
    (T₁ : DoubleTabTopSeed c d b) (X : Finset (Fin c → Fin (2 ^ b))) {r : ℕ}
    (hr : r < (sortedChars X).length)
    {p : (Fin c → Fin (2 ^ b)) × Fin d}
    (hp : p ∈ GammaSet T₁ X (r + 1) \ GammaSet T₁ X r) :
    p.1 ∈ X ∧ p.2 ∈ PhiSet T₁ X r ∧
      ∃ x ∈ X, x ≠ p.1 ∧ (sortedChars X)[r] ∈ posSymmDiff x p.1 ∧
        posSymmDiff x p.1 ⊆ prefixChars X (r + 1) ∧
        simpleTabTuple T₁ x p.2 = simpleTabTuple T₁ p.1 p.2 := by
  obtain ⟨hp_in, hp_out⟩ := Finset.mem_sdiff.mp hp
  rcases mem_gammaSet.mp hp_in with ⟨hpX, x, hxX, hne, hsub, heq⟩
  have hmem_r : (sortedChars X)[r] ∈ posSymmDiff x p.1 := by
    by_contra hnot
    exact hp_out (mem_gammaSet.mpr
      ⟨hpX, x, hxX, hne, subset_prefixChars_of_subset_succ X hr hsub hnot, heq⟩)
  refine ⟨hpX, ?_, x, hxX, hne, hmem_r, hsub, heq⟩
  simp only [PhiSet, hr, ↓reduceDIte, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨x, hxX, p.1, hpX, hmem_r, hsub, heq⟩

/-- **Lemma 9 ([Thorup2013], Section 3, Eq. (8), pp. 12–13)**: for each step `r < ℓ*`,
`γ_{≤ r + 1} - γ_{≤ r} ≤ 2 * ϕ_r * n_r`.

Write `α_r` for the `r`-th sorted character and `S_r` for the `n_r` keys containing it. A pair
`p = (y, j)` new at step `r` collides with a key `x` with `α_r ∈ x △ y`, so `j ∈ Φ_r` and exactly
one of `x`, `y` lies in `S_r`. The pairs with `y ∈ S_r` lie in `S_r × Φ_r`; each pair with `y ∉ S_r`
is determined by `(x, j) ∈ S_r × Φ_r`, since two such pairs with the same `x` and `j` would collide
with each other below `α_r` and so would not be new. -/
private theorem gamma_succ_sub_le {c d b : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (X : Finset (Fin c → Fin (2 ^ b))) {r : ℕ} (hr : r < (sortedChars X).length) :
    gamma T₁ X (r + 1) - gamma T₁ X r ≤ 2 * (phi T₁ X r * sortedFreq X r) := by
  classical
  let α_r := (sortedChars X)[r]
  let D := GammaSet T₁ X (r + 1) \ GammaSet T₁ X r
  let P := (X.filter fun x => α_r ∈ posSet x) ×ˢ PhiSet T₁ X r
  have hP : #P = phi T₁ X r * sortedFreq X r := by
    simp only [P, Finset.card_product, sortedFreq, hr, ↓reduceDIte, Nat.mul_comm]; rfl
  have hD₁_le : #(D.filter fun p => α_r ∈ posSet p.1) ≤ #P :=
    Finset.card_le_card fun p hp => by
      rcases Finset.mem_filter.mp hp with ⟨hpD, hp_pos⟩
      have hw := exists_witness_of_mem_gammaSet_sdiff T₁ X hr hpD
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hw.1, hp_pos⟩, hw.2.1⟩
  have hD₂_le : #(D.filter fun p => α_r ∉ posSet p.1) ≤ #P := by
    refine Finset.card_le_card_of_forall_subsingleton
      (fun p q => q.2 = p.2 ∧ posSymmDiff q.1 p.1 ⊆ prefixChars X (r + 1) ∧
        simpleTabTuple T₁ q.1 p.2 = simpleTabTuple T₁ p.1 p.2)
      (fun p hp => ?_) fun q _ => ?_
    · rcases Finset.mem_filter.mp hp with ⟨hpD, hp_not⟩
      obtain ⟨-, hj, x, hxX, -, hmem, hsub, htab⟩ :=
        exists_witness_of_mem_gammaSet_sdiff T₁ X hr hpD
      have hx_pos : α_r ∈ posSet x :=
        (Finset.mem_symmDiff.mp hmem).elim And.left fun h => (hp_not h.1).elim
      exact ⟨(x, p.2), Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hxX, hx_pos⟩, hj⟩,
        rfl, hsub, htab⟩
    · rintro p₁ ⟨hp₁, hj₁, hsub₁, htab₁⟩ p₂ ⟨hp₂, hj₂, hsub₂, htab₂⟩
      rcases Finset.mem_filter.mp hp₁ with ⟨hp₁D, hp₁_not⟩
      rcases Finset.mem_filter.mp hp₂ with ⟨hp₂D, hp₂_not⟩
      have hj : p₁.2 = p₂.2 := hj₁.symm.trans hj₂
      refine Prod.ext ?_ hj
      by_contra hne
      have hsub : posSymmDiff p₂.1 p₁.1 ⊆ prefixChars X r :=
        subset_prefixChars_of_subset_succ X hr
          ((posSymmDiff_subset_union q.1 p₂.1 p₁.1).trans (Finset.union_subset hsub₂ hsub₁))
          fun hα => (Finset.mem_symmDiff.mp hα).elim (fun h => hp₂_not h.1) (fun h => hp₁_not h.1)
      exact (Finset.mem_sdiff.mp hp₁D).2 (mem_gammaSet.mpr
        ⟨(mem_gammaSet.mp (Finset.mem_sdiff.mp hp₁D).1).1, p₂.1,
          (mem_gammaSet.mp (Finset.mem_sdiff.mp hp₂D).1).1, Ne.symm hne, hsub,
          (hj ▸ htab₂).symm.trans htab₁⟩)
  have hsplit := Finset.card_filter_add_card_filter_not (s := D) (p := fun p => α_r ∈ posSet p.1)
  rw [gamma, gamma, ← Finset.card_sdiff_of_subset (gammaSet_mono T₁ X (Nat.le_succ r)), ← hP]
  change #D ≤ _
  omega

/-- If every prefix `1 ≤ ℓ ≤ ℓ*` has `< q * ℓ` derivable outputs, summation by parts yields
`∑_{i < ℓ*} ϕ_i * n_i < q * ∑_{i < ℓ*} n_i` ([Thorup2013], Section 3, Eqs. (9)–(11),
pp. 12–13). -/
private theorem sum_phi_mul_sortedFreq_lt {c d b q : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (X : Finset (Fin c → Fin (2 ^ b))) (hlen : 0 < (sortedChars X).length)
    (hsmall : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ (sortedChars X).length →
      ∑ i ∈ Finset.range ℓ, phi T₁ X i < q * ℓ) :
    ∑ i ∈ Finset.range (sortedChars X).length, phi T₁ X i * sortedFreq X i <
      q * ∑ i ∈ Finset.range (sortedChars X).length, sortedFreq X i := by
  obtain ⟨m, hm⟩ : ∃ m, (sortedChars X).length = m + 1 := ⟨(sortedChars X).length - 1, by omega⟩
  rw [hm]
  have hmono : ∀ i < m, sortedFreq X (i + 1) ≤ sortedFreq X i := fun i hi =>
    sortedFreq_antitone X (by omega) (Nat.le_succ i)
  rw [Nat.sum_mul_eq_sum_prefix_sub (phi T₁ X) (sortedFreq X) m hmono, Finset.mul_sum,
    Nat.sum_mul_eq_sum_prefix_sub (fun _ => q) (sortedFreq X) m hmono]
  refine add_lt_add_of_le_of_lt (Finset.sum_le_sum fun i hi => Nat.mul_le_mul_right _ ?_) ?_
  · have := Finset.mem_range.mp hi
    simpa [Nat.mul_comm] using (hsmall (i + 1) (by omega) (by omega)).le
  · simpa [Nat.mul_comm] using
      Nat.mul_lt_mul_of_pos_right (hsmall (m + 1) (by omega) (by omega))
        (one_le_sortedFreq X (by omega))

private theorem gamma_le_two_mul_sum_phi_sortedFreq {c d b : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (X : Finset (Fin c → Fin (2 ^ b))) :
    ∀ r ≤ (sortedChars X).length,
      gamma T₁ X r ≤ 2 * ∑ i ∈ Finset.range r, phi T₁ X i * sortedFreq X i
  | 0, _ => by simp [gamma_eq_zero_of_le_one T₁ X (by decide : 0 ≤ 1)]
  | r + 1, hr => by
    have ih := gamma_le_two_mul_sum_phi_sortedFreq T₁ X r (Nat.le_of_succ_le hr)
    have hstep := gamma_succ_sub_le T₁ X (Nat.lt_of_succ_le hr)
    rw [Finset.sum_range_succ, Nat.mul_add]
    omega

/-- **Theorem 7(a) prefix existence ([Thorup2013], Section 3, pp. 12–13)**: when `c ≥ 1`, `q ≥ 1`,
`d = 2 * q * c`, and `X` is a non-empty key set violating `k`-uniqueness, some prefix `L_{≤ ℓ}` of
length `2 ≤ ℓ ≤ ℓ*` has at least `q * ℓ` derivable output characters. -/
private theorem exists_prefix_le_sum_phi {c d b q : ℕ} (hc : 1 ≤ c) (hq : 1 ≤ q)
    (hd : d = 2 * q * c) (T₁ : DoubleTabTopSeed c d b)
    (X : Finset (Fin c → Fin (2 ^ b))) (hX_ne : X.Nonempty)
    (hviol : ∀ y ∈ X, ∀ j : Fin d, ∃ x ∈ X, x ≠ y ∧
      simpleTabTuple T₁ y j = simpleTabTuple T₁ x j) :
    ∃ ℓ, 2 ≤ ℓ ∧ ℓ ≤ (sortedChars X).length ∧ q * ℓ ≤ ∑ i ∈ Finset.range ℓ, phi T₁ X i := by
  have hX_pos : 0 < #X := Finset.card_pos.mpr hX_ne
  have hsum_freq := sum_sortedFreq X
  have hlen_pos : 0 < (sortedChars X).length := by
    by_contra h0
    rw [Nat.eq_zero_of_not_pos h0, Finset.range_zero, Finset.sum_empty] at hsum_freq
    have := Nat.mul_pos hc hX_pos
    omega
  have hex : ∃ ℓ, 1 ≤ ℓ ∧ ℓ ≤ (sortedChars X).length ∧
      q * ℓ ≤ ∑ i ∈ Finset.range ℓ, phi T₁ X i := by
    by_contra! hsmall
    have hlt := sum_phi_mul_sortedFreq_lt T₁ X hlen_pos hsmall
    have hgamma_eq := gamma_length_eq T₁ X hviol
    have hgamma_le := gamma_le_two_mul_sum_phi_sortedFreq T₁ X (sortedChars X).length le_rfl
    rw [hsum_freq] at hlt
    subst hd; nlinarith
  rcases hex with ⟨ℓ, hℓ₁, hℓ_hi, hqℓ⟩
  refine ⟨ℓ, ?_, hℓ_hi, hqℓ⟩
  by_contra hlt2
  obtain rfl : ℓ = 1 := by omega
  simp [phi_zero_eq_zero] at hqℓ; omega

private theorem exists_eq_tuple_of_mem_phiSet {c d b ℓ : ℕ} [NeZero (2 * c)]
    (T₁ : DoubleTabTopSeed c d b) (X : Finset (Fin c → Fin (2 ^ b)))
    (hℓ_hi : ℓ ≤ (sortedChars X).length) (r : Fin ℓ) {j : Fin d}
    (hj : j ∈ PhiSet T₁ X r.val) :
    let L : Fin ℓ → Fin c × Fin (2 ^ b) := fun idx =>
      (sortedChars X)[idx.val]'(lt_of_lt_of_le idx.isLt hℓ_hi)
    ∃ g : Fin (2 * c) → Fin ℓ,
      lastIdx g = r ∧
      ∑ idx ∈ Finset.univ.image g,
        (BitString.equivFin b).symm (T₁ (L idx).1 j (L idx).2) = 0 := by
  classical
  intro L
  have hr_lt : r.val < (sortedChars X).length := lt_of_lt_of_le r.isLt hℓ_hi
  have hL_inj : Function.Injective L := fun _ _ h =>
    Fin.ext ((nodup_sortedChars X).getElem_inj_iff.mp h)
  simp only [PhiSet, hr_lt, ↓reduceDIte, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  rcases hj with ⟨x, _, y, _, hr_mem, hsub, htab⟩
  let B : Finset (Fin ℓ) := Finset.univ.filter fun idx => L idx ∈ posSymmDiff x y
  have hr_B : r ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ r, hr_mem⟩
  have hB_img : B.image L = posSymmDiff x y := by
    ext α
    simp only [B, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun ⟨_, hα, heq⟩ => heq ▸ hα, fun hα => ?_⟩
    obtain ⟨i, _, hi_lt, heq⟩ := exists_lt_of_mem_prefixChars (hsub hα)
    exact ⟨⟨i, by omega⟩, heq ▸ hα, heq⟩
  have hB_le_r : ∀ idx ∈ B, idx ≤ r := fun idx hidx => by
    obtain ⟨i, _, hi_lt, heq⟩ := exists_lt_of_mem_prefixChars (hsub (Finset.mem_filter.mp hidx).2)
    have : i = idx.val := (nodup_sortedChars X).getElem_inj_iff.mp heq
    exact Fin.le_iff_val_le_val.mpr (by omega)
  have hB_card : #B ≤ 2 * c :=
    Finset.card_image_of_injective B hL_inj ▸ hB_img.symm ▸ card_posSymmDiff_le x y
  let g : Fin (2 * c) → Fin ℓ := fun t =>
    if ht : t.val < #B then (B.equivFin.symm ⟨t.val, ht⟩).val else r
  have hg_img : Finset.univ.image g = B := by
    ext idx
    simp only [Finset.mem_image, Finset.mem_univ, true_and, g]
    refine ⟨fun ⟨t, h⟩ => ?_, fun hidx => ?_⟩
    · subst h; split_ifs with ht
      exacts [(B.equivFin.symm ⟨t.val, ht⟩).property, hr_B]
    · let t' := B.equivFin ⟨idx, hidx⟩
      refine ⟨⟨t'.val, t'.isLt.trans_le hB_card⟩, ?_⟩
      simp only [t'.isLt, ↓reduceDIte, Fin.eta]
      exact congrArg Subtype.val (B.equivFin.symm_apply_apply ⟨idx, hidx⟩)
  refine ⟨g, le_antisymm (Finset.max'_le _ _ _ fun idx hidx => hB_le_r idx (hg_img ▸ hidx))
    (Finset.le_max' _ r (hg_img.symm ▸ hr_B)), ?_⟩
  rw [hg_img, ← Finset.sum_image (f := fun α : Fin c × Fin (2 ^ b) =>
    (BitString.equivFin b).symm (T₁ α.1 j α.2)) (fun _ _ _ _ h => hL_inj h), hB_img]
  exact (simpleTabTuple_eq_iff_sum_posSymmDiff_eq_zero T₁ x y j).mp htab

/-- **Violation of `IsKUnique` yields a satisfied efficient code (`[Thorup2013]`, Section 2 &
Theorem 7(a), pp. 10–13)**: if `c ≥ 1`, `q ≥ 1`, `d = 2 * q * c`, and
`¬ IsKUnique k (simpleTabTuple T₁)`, then there exist `2 ≤ ℓ ≤ c * k`,
`L : Fin ℓ → Fin c × Fin (2 ^ b)`, and `M : Fin (q * ℓ) → (Fin (2 * c) → Fin ℓ) × Fin d` such that
`SatisfiesCode T₁ L M`. -/
private theorem exists_satisfiesCode_of_not_isKUnique {c d b q k : ℕ} [NeZero (2 * c)]
    (hc : 1 ≤ c) (hq : 1 ≤ q) (hd : d = 2 * q * c) {T₁ : DoubleTabTopSeed c d b}
    (hnot : ¬ IsKUnique k (simpleTabTuple T₁)) :
    ∃ ℓ ∈ Finset.Icc 2 (c * k),
      ∃ (L : Fin ℓ → Fin c × Fin (2 ^ b)) (M : Fin (q * ℓ) → (Fin (2 * c) → Fin ℓ) × Fin d),
        SatisfiesCode T₁ L M := by
  classical
  unfold IsKUnique at hnot; push Not at hnot
  rcases hnot with ⟨X, hX_ne, hX_le, hviol⟩
  obtain ⟨ℓ, hℓ_lo, hℓ_hi, hqℓ⟩ := exists_prefix_le_sum_phi hc hq hd T₁ X hX_ne hviol
  have hℓ_ck : ℓ ≤ c * k := hℓ_hi.trans ((length_sortedChars X).trans_le
    ((card_activeChars_le X).trans (Nat.mul_le_mul_left c hX_le)))
  let L : Fin ℓ → Fin c × Fin (2 ^ b) := fun idx =>
    (sortedChars X)[idx.val]'(lt_of_lt_of_le idx.isLt hℓ_hi)
  let Pairs : Finset (Σ _ : Fin ℓ, Fin d) := Finset.univ.sigma fun r => PhiSet T₁ X r.val
  have hcard : q * ℓ ≤ #Pairs := by
    rwa [Finset.card_sigma, Fin.sum_univ_eq_sum_range (fun i => #(PhiSet T₁ X i))]
  let pair (s : Fin (q * ℓ)) : Pairs := Pairs.equivFin.symm (Fin.castLE hcard s)
  have hpair_inj : Function.Injective pair :=
    Pairs.equivFin.symm.injective.comp (Fin.castLE_injective hcard)
  choose g hg_last hg_sum using fun s =>
    exists_eq_tuple_of_mem_phiSet T₁ X hℓ_hi (pair s).val.1
      (Finset.mem_sigma.mp (pair s).property).2
  refine ⟨ℓ, Finset.mem_Icc.mpr ⟨hℓ_lo, hℓ_ck⟩, L, fun s => (g s, (pair s).val.2),
    fun _ _ h => Fin.ext ((nodup_sortedChars X).getElem_inj_iff.mp h), fun s₁ s₂ heq => ?_, hg_sum⟩
  obtain ⟨hlast, hj⟩ := Prod.ext_iff.mp heq
  exact hpair_inj (Subtype.ext (Sigma.ext ((hg_last s₁).symm.trans (hlast.trans (hg_last s₂)))
    (heq_of_eq hj)))

/-! ## Section 5: Efficient-code seed counting (`[Thorup2013]`, §2, Eqs. (6)–(7)) -/

/-- **Equation-system seed count ([Thorup2013], Section 2, p. 11)**: for any `(L, M)`, at most
`|Θ_top| / (2 ^ b) ^ (q * ℓ)` top-level tables `T₁` satisfy `SatisfiesCode T₁ L M`. -/
private theorem card_filter_satisfiesCode_le {c d b q ℓ : ℕ} [NeZero (2 * c)]
    (L : Fin ℓ → Fin c × Fin (2 ^ b))
    (M : Fin (q * ℓ) → (Fin (2 * c) → Fin ℓ) × Fin d) :
    (2 ^ b) ^ (q * ℓ) *
      #(Finset.univ.filter fun T₁ : DoubleTabTopSeed c d b => SatisfiesCode T₁ L M) ≤
    Fintype.card (DoubleTabTopSeed c d b) := by
  classical
  by_cases hLM : Function.Injective L ∧
      Function.Injective (fun r : Fin (q * ℓ) => (lastIdx (M r).1, (M r).2))
  · rcases hLM with ⟨hL, hM⟩
    let supp (r : Fin (q * ℓ)) : Finset ((Fin c × Fin (2 ^ b)) × Fin d) :=
      (Finset.univ.image (M r).1).image fun idx => (L idx, (M r).2)
    have hsurj := surjective_restrict_sum_of_peeling (γ := BitString b) supp
      (T := Finset.univ) fun S _ hSne => by
        let lastOf (r : Fin (q * ℓ)) := lastIdx (M r).1
        obtain ⟨r₀, hr₀, hr₀_eq⟩ := Finset.mem_image.mp
          (Finset.max'_mem (S.image lastOf) (hSne.image lastOf))
        refine ⟨r₀, hr₀, (L (lastOf r₀), (M r₀).2),
          Finset.mem_image_of_mem _ (lastIdx_mem_image _), fun r hr hne hmem => hne ?_⟩
        obtain ⟨idx, hidx, heq⟩ := Finset.mem_image.mp hmem
        have hidx_eq : idx = lastOf r₀ := hL (Prod.mk.inj heq).1
        have hle₁ : lastOf r₀ ≤ lastOf r := hidx_eq ▸ Finset.le_max' _ idx hidx
        have hle₂ : lastOf r ≤ lastOf r₀ :=
          hr₀_eq ▸ Finset.le_max' (S.image lastOf) (lastOf r) (Finset.mem_image_of_mem lastOf hr)
        exact hM (Prod.ext (le_antisymm hle₂ hle₁) (Prod.mk.inj heq).2)
    let e : DoubleTabTopSeed c d b ≃ (((Fin c × Fin (2 ^ b)) × Fin d) → BitString b) :=
      { toFun T₁ u := (BitString.equivFin b).symm (T₁ u.1.1 u.2 u.1.2)
        invFun w i j a := BitString.equivFin b (w ((i, a), j))
        left_inv _ := funext fun _ => funext fun _ => funext fun _ => Equiv.apply_symm_apply _ _
        right_inv _ := funext fun _ => Equiv.symm_apply_apply _ _ }
    let eval (T₁ : DoubleTabTopSeed c d b) (r : Fin (q * ℓ)) : BitString b :=
      ∑ u ∈ supp r, e T₁ u
    have hshift (y : Fin (q * ℓ) → BitString b) :
        ∃ σ : Equiv.Perm (DoubleTabTopSeed c d b), ∀ T₁, eval (σ T₁) = eval T₁ + y := by
      obtain ⟨w₀, hw₀⟩ := hsurj (fun r => y r.val)
      refine ⟨e.trans (Equiv.addRight w₀) |>.trans e.symm, fun T₁ => funext fun r => ?_⟩
      simpa [eval, Finset.sum_add_distrib] using congrFun hw₀ ⟨r, Finset.mem_univ r⟩
    have hsum (T₁ : DoubleTabTopSeed c d b) (r : Fin (q * ℓ)) :
        eval T₁ r = ∑ idx ∈ Finset.univ.image (M r).1,
          (BitString.equivFin b).symm (T₁ (L idx).1 (M r).2 (L idx).2) :=
      Finset.sum_image (f := e T₁) fun _ _ _ _ h => hL (Prod.mk.inj h).1
    have hfilt : (Finset.univ.filter fun T₁ : DoubleTabTopSeed c d b => SatisfiesCode T₁ L M) =
        Finset.univ.filter fun T₁ => eval T₁ = 0 := by
      ext T₁
      simp only [SatisfiesCode, hL, hM, true_and, Finset.mem_filter, Finset.mem_univ, funext_iff,
        Pi.zero_apply, hsum]
    rw [hfilt, show (2 ^ b) ^ (q * ℓ) = Fintype.card (Fin (q * ℓ) → BitString b) by simp]
    exact (card_mul_card_filter_eq_of_shift (f := eval) hshift 0).le
  · rw [Finset.filter_eq_empty_iff.mpr fun _ _ h => hLM ⟨h.1, h.2.1⟩, Finset.card_empty]
    exact Nat.zero_le _

/-- Union bound over all codes `(L, M)` of length `ℓ` ([Thorup2013], Section 2, Eq. (6), p. 11). -/
private theorem card_filter_exists_satisfiesCode_le {c d b q ℓ : ℕ} [NeZero (2 * c)]
    (hq : 1 ≤ q) :
    (2 ^ ((q - 1) * b)) ^ ℓ *
      #(Finset.univ.filter fun T₁ : DoubleTabTopSeed c d b =>
        ∃ (L : Fin ℓ → Fin c × Fin (2 ^ b))
          (M : Fin (q * ℓ) → (Fin (2 * c) → Fin ℓ) × Fin d),
          SatisfiesCode T₁ L M) ≤
    (c * (ℓ ^ (2 * c) * d) ^ q) ^ ℓ * Fintype.card (DoubleTabTopSeed c d b) := by
  classical
  let CodeType := (Fin ℓ → Fin c × Fin (2 ^ b)) × (Fin (q * ℓ) → (Fin (2 * c) → Fin ℓ) × Fin d)
  let E := Finset.univ.filter fun T₁ : DoubleTabTopSeed c d b =>
    ∃ (L : Fin ℓ → Fin c × Fin (2 ^ b)) (M : Fin (q * ℓ) → (Fin (2 * c) → Fin ℓ) × Fin d),
      SatisfiesCode T₁ L M
  have hE_le : #E ≤ ∑ p : CodeType,
      #(Finset.univ.filter fun T₁ : DoubleTabTopSeed c d b => SatisfiesCode T₁ p.1 p.2) :=
    (Finset.card_le_card fun T₁ hT₁ => by
      rcases (Finset.mem_filter.mp hT₁).2 with ⟨L, M, hcode⟩
      exact Finset.mem_biUnion.mpr ⟨(L, M), Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcode⟩⟩).trans Finset.card_biUnion_le
  have hsum_le : (2 ^ b) ^ (q * ℓ) * #E ≤
      Fintype.card CodeType * Fintype.card (DoubleTabTopSeed c d b) :=
    (Nat.mul_le_mul_left _ hE_le).trans <| by
      rw [Finset.mul_sum]
      exact (Finset.sum_le_sum fun p _ => card_filter_satisfiesCode_le p.1 p.2).trans_eq (by simp)
  have hcard_code : Fintype.card CodeType =
      (2 ^ b) ^ ℓ * (c * (ℓ ^ (2 * c) * d) ^ q) ^ ℓ := by
    simp only [CodeType, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    rw [Nat.mul_pow c (2 ^ b) ℓ, Nat.mul_pow c _ ℓ, ← Nat.pow_mul _ q ℓ]; ring
  have hpow_lhs : (2 ^ b) ^ (q * ℓ) = (2 ^ b) ^ ℓ * (2 ^ ((q - 1) * b)) ^ ℓ := by
    simp only [← Nat.pow_mul, ← Nat.pow_add]
    exact congrArg (2 ^ ·) (by (conv_lhs => rw [← Nat.sub_add_cancel hq]); ring)
  rw [hpow_lhs, hcard_code, Nat.mul_assoc, Nat.mul_assoc] at hsum_le
  exact Nat.le_of_mul_le_mul_left hsum_le (by positivity)

/-- Geometric-series tail bound in `ℕ`: when `2 * B ≤ W` and `W ^ ℓ * g ℓ ≤ B ^ ℓ * N`,
`W ^ m * ∑_{i < s} g (m + i) ≤ 2 * B ^ m * N`. -/
private theorem tail_sum_bound {B W N : ℕ} (hW : 0 < W) (hBW : 2 * B ≤ W) (g : ℕ → ℕ)
    (hg : ∀ ℓ, W ^ ℓ * g ℓ ≤ B ^ ℓ * N) :
    ∀ (s m : ℕ), W ^ m * (∑ i ∈ Finset.range s, g (m + i)) ≤ 2 * B ^ m * N
  | 0, _ => by simp
  | s + 1, m => by
    have ih := tail_sum_bound hW hBW g hg s (m + 1)
    have hshift : (∑ i ∈ Finset.range s, g (m + (i + 1))) =
        ∑ i ∈ Finset.range s, g (m + 1 + i) :=
      Finset.sum_congr rfl fun i _ => congrArg g (Nat.add_right_comm m i 1)
    refine Nat.le_of_mul_le_mul_left ?_ hW
    rw [Finset.sum_range_succ', Nat.add_zero, hshift, Nat.mul_add, Nat.mul_add,
      show W * (2 * B ^ m * N) = W * (B ^ m * N) + W * (B ^ m * N) by ring]
    refine Nat.add_le_add ?_ (Nat.mul_le_mul_left W (hg m))
    calc W * (W ^ m * ∑ i ∈ Finset.range s, g (m + 1 + i))
        = W ^ (m + 1) * ∑ i ∈ Finset.range s, g (m + 1 + i) := by rw [← Nat.mul_assoc, ← pow_succ']
      _ ≤ 2 * B ^ (m + 1) * N := ih
      _ = (2 * B) * (B ^ m * N) := by rw [pow_succ']; ring
      _ ≤ W * (B ^ m * N) := Nat.mul_le_mul_right _ hBW

/-- Per-step efficient-code counting factor `c * ((c * k) ^ (2 * c) * d) ^ q` from
[Thorup2013], Section 2, Eqs. (6)–(7), p. 11. -/
@[expose] def doubleTabCodeBound (c d q k : ℕ) : ℕ :=
  c * ((c * k) ^ (2 * c) * d) ^ q

/-- **Thorup's Universal `k`-Uniqueness Bound ([Thorup2013], Theorem 1(a), Section 2 Eqs. (6)–(7),
and Section 3 Theorem 7(a), pp. 4, 11–13)**:
For `c ≥ 1`, `q ≥ 1`, `d = 2 * q * c`, and `2 * doubleTabCodeBound c d q k ≤ 2 ^ ((q - 1) * b)`,
the number of top-level tables `T₁ : DoubleTabTopSeed c d b` for which `simpleTabTuple T₁` fails to
be `k`-unique satisfies
`(2 ^ ((q - 1) * b)) ^ 2 * #{T₁ | ¬ IsKUnique k (simpleTabTuple T₁)} ≤
  2 * (doubleTabCodeBound c d q k) ^ 2 * Fintype.card (DoubleTabTopSeed c d b)`. -/
theorem card_not_isKUnique_le {c d b q k : ℕ} (hc : 1 ≤ c) (hq : 1 ≤ q) (hd : d = 2 * q * c)
    (hbound : 2 * doubleTabCodeBound c d q k ≤ 2 ^ ((q - 1) * b)) :
    (2 ^ ((q - 1) * b)) ^ 2 *
      #(Finset.univ.filter fun T₁ : DoubleTabTopSeed c d b =>
        ¬ IsKUnique k (simpleTabTuple T₁)) ≤
    2 * (doubleTabCodeBound c d q k) ^ 2 * Fintype.card (DoubleTabTopSeed c d b) := by
  classical
  have : NeZero (2 * c) := ⟨by omega⟩
  let BadAt (ℓ : ℕ) := Finset.univ.filter fun T₁ : DoubleTabTopSeed c d b =>
    ℓ ≤ c * k ∧ ∃ (L : Fin ℓ → Fin c × Fin (2 ^ b))
      (M : Fin (q * ℓ) → (Fin (2 * c) → Fin ℓ) × Fin d), SatisfiesCode T₁ L M
  have hg (ℓ : ℕ) :
      (2 ^ ((q - 1) * b)) ^ ℓ * #(BadAt ℓ) ≤
        (doubleTabCodeBound c d q k) ^ ℓ * Fintype.card (DoubleTabTopSeed c d b) := by
    by_cases hℓ : ℓ ≤ c * k
    · refine (Nat.mul_le_mul_left _ (Finset.card_le_card fun T₁ hT₁ =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hT₁).2.2⟩)).trans ?_
      refine (card_filter_exists_satisfiesCode_le hq).trans ?_
      dsimp only [doubleTabCodeBound]; gcongr
    · simp [BadAt, hℓ]
  have hsub : (Finset.univ.filter fun T₁ : DoubleTabTopSeed c d b =>
      ¬ IsKUnique k (simpleTabTuple T₁)) ⊆ (Finset.range (c * k)).biUnion fun i => BadAt (2 + i) :=
    fun T₁ hT₁ => by
      obtain ⟨ℓ, hℓ_Icc, L, M, hcode⟩ :=
        exists_satisfiesCode_of_not_isKUnique hc hq hd (Finset.mem_filter.mp hT₁).2
      rcases Finset.mem_Icc.mp hℓ_Icc with ⟨hℓ_lo, hℓ_hi⟩
      refine Finset.mem_biUnion.mpr ⟨ℓ - 2, Finset.mem_range.mpr (by omega), ?_⟩
      rw [show 2 + (ℓ - 2) = ℓ by omega]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hℓ_hi, L, M, hcode⟩
  exact (Nat.mul_le_mul_left _ ((Finset.card_le_card hsub).trans Finset.card_biUnion_le)).trans
    (tail_sum_bound (Nat.two_pow_pos _) hbound (fun ℓ => #(BadAt ℓ)) hg (c * k) 2)

/-- Specialization of `card_not_isKUnique_le` to `q = 4` (`d = 8 * c`, `[Thorup2013]`, Theorem 1(a),
p. 4): when `2 * doubleTabCodeBound c (8 * c) 4 k ≤ 2 ^ (3 * b)`, at most a
`2 * (doubleTabCodeBound c (8 * c) 4 k) ^ 2 / 2 ^ (6 * b)` fraction of top-level tables fail to be
`k`-unique. -/
theorem card_not_isKUnique_eight_mul_le {c b k : ℕ} (hc : 1 ≤ c)
    (hbound : 2 * doubleTabCodeBound c (8 * c) 4 k ≤ 2 ^ (3 * b)) :
    2 ^ (6 * b) *
      #(Finset.univ.filter fun T₁ : DoubleTabTopSeed c (8 * c) b =>
        ¬ IsKUnique k (simpleTabTuple T₁)) ≤
    2 * (doubleTabCodeBound c (8 * c) 4 k) ^ 2 * Fintype.card (DoubleTabTopSeed c (8 * c) b) := by
  have h := card_not_isKUnique_le (d := 8 * c) (q := 4) hc (by decide) (by ring) hbound
  rwa [← Nat.pow_mul, show (4 - 1) * b * 2 = 6 * b by ring] at h

/-- Minimum character bit-width `doubleTabMinB c_exp` for polynomial universe exponent `c_exp : ℕ`,
bounding the character bit-width `b = (1 + Nat.clog 2 (max n_max 4)) / 2` from below when
`doubleTabThreshold c_exp ≤ n_max` (`n_max` = capacity bound) so `doubleTabHash` satisfies the
high-probability logarithmic `k`-uniqueness bound via `Nat.pow_le_two_pow`. -/
@[expose] def doubleTabMinB (c_exp : ℕ) : ℕ :=
  let z := 8 + 48 * max c_exp 1
  4 * (z * z)

theorem doubleTabMinB_eq (c_exp : ℕ) :
    doubleTabMinB c_exp = 4 * (24 * (2 * max c_exp 1) + 8) ^ 2 := by
  unfold doubleTabMinB; ring

/-- Capacity threshold `2 ^ (2 * doubleTabMinB c_exp)` for polynomial universe exponent `c_exp : ℕ`
above which Double Tabulation with `c = 2 * max c_exp 1` characters of bit-width
`b = (1 + Nat.clog 2 (max n_max 4)) / 2` achieves logarithmic `k`-wise independence with
inverse-polynomial failure probability. -/
@[expose] def doubleTabThreshold (c_exp : ℕ) : ℕ :=
  2 ^ (2 * doubleTabMinB c_exp)

theorem doubleTabThreshold_eq (c_exp : ℕ) :
    doubleTabThreshold c_exp = 2 ^ (2 * doubleTabMinB c_exp) :=
  rfl

theorem four_le_doubleTabThreshold (c_exp : ℕ) :
    4 ≤ doubleTabThreshold c_exp := by
  have : 0 < doubleTabMinB c_exp := by dsimp only [doubleTabMinB]; positivity
  exact Nat.pow_le_pow_right two_pos (by omega : 2 ≤ 2 * doubleTabMinB c_exp)

end Cslib.Probability
