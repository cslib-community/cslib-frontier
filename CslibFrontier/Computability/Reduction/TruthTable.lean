/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Reduction.ManyOne
public import Mathlib.Data.List.Forall2
public import Mathlib.Data.List.OfFn
import CslibFrontier.Foundations.Data.List.Counting
import CslibFrontier.Foundations.Data.List.Filter

/-!
# Truth-table reductions and autoreductions by admissible data

A truth-table reduction of `A` to `B` fixes, for each input `a`, a number `r a` of queries
`q (a, 0), …, q (a, r a - 1)` and decides `a ∈ A` by applying a combiner `d` to `a` and the answer
word `truthTableAnswers (q ⁻¹' B) r a`. Positive truth-table reductions restrict the combiner to be
monotone in the answer word under `List.Forall₂ (· ≤ ·)`, and disjunctive and conjunctive reductions
replace the combiner by "some query is in `B`" and "every query is in `B`". Self-query-avoiding
autoreductions specialize `B = A` and adjoin `∀ a i, i < r a → q (a, i) ≠ a` to the admissible
data, mirroring `Cslib.Complexity.ManyOneAutoreducibleBy`.

Here the admissible data `(r, q, d)` or `(r, q)` are an arbitrary predicate `Good`. No machine model
or encoding is built in. Polynomial-time and logspace truth-table reductions and autoreductions
instantiate these kernels directly.

## Main definitions

* `Cslib.Complexity.truthTableAnswers`: the answer word of an indexed batch of queries.
* `Cslib.Complexity.TruthTableReducibleBy`, `Cslib.Complexity.PTTReducibleBy`: general and positive
  truth-table reducibility by admissible data.
* `Cslib.Complexity.DTTReducibleBy`, `Cslib.Complexity.CTTReducibleBy`: disjunctive and
  conjunctive truth-table reducibility by admissible data.
* `Cslib.Complexity.truthTableCompQuery`, `Cslib.Complexity.truthTableCompCombiner`,
  `Cslib.Complexity.truthTableCompPairs`, `Cslib.Complexity.dttCompQuery`: composite query maps and
  combiner for block-indexed and flattened nonadaptive composition.
* `Cslib.Complexity.ManyOneAutoreducibleBy`,
  `Cslib.Complexity.TruthTableAutoreducibleBy`, `Cslib.Complexity.PTTAutoreducibleBy`,
  `Cslib.Complexity.DTTAutoreducibleBy`, `Cslib.Complexity.CTTAutoreducibleBy`: query-avoiding
  many-one and truth-table autoreducibility by admissible data.

## Main results

* `Cslib.Complexity.TruthTableReducibleBy.mono`, `Cslib.Complexity.PTTReducibleBy.mono`,
  `Cslib.Complexity.DTTReducibleBy.mono`, `Cslib.Complexity.CTTReducibleBy.mono`: more admissible
  data give more reductions.
* `Cslib.Complexity.TruthTableReducibleBy.compl_left`,
  `Cslib.Complexity.TruthTableReducibleBy.compl_right`,
  `Cslib.Complexity.TruthTableReducibleBy.compl`: negating the combiner, the answers it reads, or
  both reduces between complements.
* `Cslib.Complexity.ManyOneReducibleBy.truthTableReducibleBy`,
  `Cslib.Complexity.ManyOneReducibleBy.pttReducibleBy`,
  `Cslib.Complexity.ManyOneReducibleBy.dttReducibleBy`,
  `Cslib.Complexity.ManyOneReducibleBy.cttReducibleBy`: a many-one reduction asks one query.
* `Cslib.Complexity.DTTReducibleBy.pttReducibleBy`,
  `Cslib.Complexity.CTTReducibleBy.pttReducibleBy`,
  `Cslib.Complexity.PTTReducibleBy.truthTableReducibleBy`: disjunctive and conjunctive reductions
  are positive truth-table reductions with combiner `List.any id` or `List.all id`.
* `Cslib.Complexity.dttReducibleBy_iff_cttReducibleBy_compl`: De Morgan duality.
* `Cslib.Complexity.truthTableAnswers_drop_take`,
  `Cslib.Complexity.mem_iff_truthTableCompCombiner`,
  `Cslib.Complexity.truthTableCompCombiner_mono`: block-slice identity, correctness and
  monotonicity of the composite combiner.
* `Cslib.Complexity.TruthTableReducibleBy.trans`,
  `Cslib.Complexity.TruthTableReducibleBy.trans_bounded`,
  `Cslib.Complexity.PTTReducibleBy.trans`, `Cslib.Complexity.PTTReducibleBy.trans_bounded`,
  `Cslib.Complexity.DTTReducibleBy.trans`, `Cslib.Complexity.DTTReducibleBy.trans_bounded`,
  `Cslib.Complexity.CTTReducibleBy.trans`, `Cslib.Complexity.CTTReducibleBy.trans_bounded`:
  resource-parametric and `(k₁ * k₂)`-bounded composition.
* `Cslib.Complexity.not_manyOneAutoreducibleBy_singleton`,
  `Cslib.Complexity.not_manyOneAutoreducibleBy_compl_singleton`,
  `Cslib.Complexity.TruthTableAutoreducibleBy.compl`,
  `Cslib.Complexity.TruthTableAutoreducibleBy.of_decide`,
  `Cslib.Complexity.ManyOneReducibleBy.truthTableAutoreducibleBy_of_compl`,
  `Cslib.Complexity.dttAutoreducibleBy_iff_cttAutoreducibleBy_compl`: singleton/co-singleton
  obstructions for many-one autoreductions, complement closure, zero-query decider autoreductions,
  one-query complement-witness autoreductions, and De Morgan duality for autoreductions.

## References

* [K. Ambos-Spies, *P-mitotic sets*][AmbosSpies1984]
* [R. E. Ladner, N. A. Lynch, A. L. Selman, *A comparison of polynomial time
  reducibilities*][LadnerLynchSelman1975]
-/

@[expose] public section

namespace Cslib.Complexity

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

open Classical in
/-- The semantic answers to a fixed indexed batch, in increasing index order. This definition
does not assert that membership in the indexed language is computable. -/
noncomputable def truthTableAnswers (A : Set (α × ℕ)) (r : α → ℕ) (a : α) : List Bool :=
  List.ofFn fun i : Fin (r a) => decide ((a, i.val) ∈ A)

/-- The answer word has one bit per query. -/
@[simp]
theorem length_truthTableAnswers (A : Set (α × ℕ)) (r : α → ℕ) (a : α) :
    (truthTableAnswers A r a).length = r a := by
  simp [truthTableAnswers]

/-- For a decidable indexed family, the answer word is the decided membership of each index below
the query count. -/
theorem truthTableAnswers_eq_map_range (A : Set (α × ℕ)) [DecidablePred (· ∈ A)] (r : α → ℕ)
    (a : α) : truthTableAnswers A r a = (List.range (r a)).map fun i => decide ((a, i) ∈ A) :=
  List.ext_getElem (by simp [truthTableAnswers]) fun _ _ _ => by simp [truthTableAnswers]

/-- Answers for the complemented family are the negated answers. -/
theorem truthTableAnswers_compl (A : Set (α × ℕ)) (r : α → ℕ) (a : α) :
    truthTableAnswers Aᶜ r a = (truthTableAnswers A r a).map (!·) := by
  classical
  exact List.ext_getElem (by simp [truthTableAnswers]) fun _ _ _ => by simp [truthTableAnswers]

/-- Slice `i` of a block-indexed answer word of total length `N a`, with block stride `k`, recovers
the inner answer word for `q (a, i)` whenever `i * k + r' (q (a, i)) ≤ N a` and block `i` begins
with the inner queries of `q (a, i)`. -/
theorem truthTableAnswers_drop_take {Q : α × ℕ → γ} {C : Set γ} {N : α → ℕ}
    {q : α × ℕ → β} {r' : β → ℕ} {q' : β × ℕ → γ} {k : ℕ} {a : α} {i : ℕ}
    (hN : i * k + r' (q (a, i)) ≤ N a)
    (hQ : ∀ j < r' (q (a, i)), Q (a, i * k + j) = q' (q (a, i), j)) :
    ((truthTableAnswers (Q ⁻¹' C) N a).drop (i * k)).take (r' (q (a, i))) =
      truthTableAnswers (q' ⁻¹' C) r' (q (a, i)) := by
  refine List.ext_getElem (by simp only [List.length_take, List.length_drop,
    length_truthTableAnswers]; omega) fun j hj₁ hj₂ => ?_
  rw [length_truthTableAnswers] at hj₂
  simp [truthTableAnswers, hQ j hj₂]

/-! ### Reduction kernels -/

/-- `A` truth-table reduces to `B` by admissible data: some query count `r`, query map `q` and
combiner `d` satisfying `Good` decide `a ∈ A` from `a` and the answers to `q (a, i)`, `i < r a`. -/
def TruthTableReducibleBy (Good : (α → ℕ) → (α × ℕ → β) → (α × List Bool → Bool) → Prop)
    (A : Set α) (B : Set β) : Prop :=
  ∃ r q d, Good r q d ∧ ∀ a, a ∈ A ↔ d (a, truthTableAnswers (q ⁻¹' B) r a) = true

/-- `A` positively truth-table reduces to `B` by admissible data: some query count `r`, query map
`q` and combiner `d` satisfying `Good`, with `d` monotone in the answer word under
`List.Forall₂ (· ≤ ·)`, decide `a ∈ A` from `a` and the answers to `q (a, i)`, `i < r a`. -/
def PTTReducibleBy (Good : (α → ℕ) → (α × ℕ → β) → (α × List Bool → Bool) → Prop)
    (A : Set α) (B : Set β) : Prop :=
  ∃ r q d, (Good r q d ∧ ∀ a u v, List.Forall₂ (· ≤ ·) u v → d (a, u) ≤ d (a, v)) ∧
    ∀ a, a ∈ A ↔ d (a, truthTableAnswers (q ⁻¹' B) r a) = true

/-- `A` disjunctively reduces to `B` by admissible data: `a ∈ A` exactly when some query
`q (a, i)` with `i < r a` is in `B`. -/
def DTTReducibleBy (Good : (α → ℕ) → (α × ℕ → β) → Prop) (A : Set α) (B : Set β) : Prop :=
  ∃ r q, Good r q ∧ ∀ a, a ∈ A ↔ ∃ i < r a, q (a, i) ∈ B

/-- `A` conjunctively reduces to `B` by admissible data: `a ∈ A` exactly when every query
`q (a, i)` with `i < r a` is in `B`. -/
def CTTReducibleBy (Good : (α → ℕ) → (α × ℕ → β) → Prop) (A : Set α) (B : Set β) : Prop :=
  ∃ r q, Good r q ∧ ∀ a, a ∈ A ↔ ∀ i < r a, q (a, i) ∈ B

variable {A : Set α} {B : Set β} {C : Set γ}

/-- Pointwise order of Boolean answer words is preserved by `List.headD false`. -/
theorem headD_false_le_of_forall₂ {u v : List Bool} (h : List.Forall₂ (· ≤ ·) u v) :
    u.headD false ≤ v.headD false := by
  cases h with
  | nil => exact le_rfl
  | cons hab _ => exact hab

namespace TruthTableReducibleBy

variable {Good : (α → ℕ) → (α × ℕ → β) → (α × List Bool → Bool) → Prop}

/-- More admissible data give more reductions. -/
theorem mono {Good' : (α → ℕ) → (α × ℕ → β) → (α × List Bool → Bool) → Prop}
    (hle : ∀ r q d, Good r q d → Good' r q d) (h : TruthTableReducibleBy Good A B) :
    TruthTableReducibleBy Good' A B :=
  let ⟨r, q, d, hg, hA⟩ := h
  ⟨r, q, d, hle r q d hg, hA⟩

/-- Negating the combiner reduces `Aᶜ` to `B`, when negated combiners are admissible. -/
theorem compl_left (hneg : ∀ r q d, Good r q d → Good r q fun x => !d x)
    (h : TruthTableReducibleBy Good A B) : TruthTableReducibleBy Good Aᶜ B :=
  let ⟨r, q, d, hg, hA⟩ := h
  ⟨r, q, _, hneg r q d hg, fun a => by simp [hA a]⟩

/-- Negating the answers before the combiner reads them reduces `A` to `Bᶜ`, when such
combiners are admissible. -/
theorem compl_right (hneg : ∀ r q d, Good r q d → Good r q fun x => d (x.1, x.2.map (!·)))
    (h : TruthTableReducibleBy Good A B) : TruthTableReducibleBy Good A Bᶜ :=
  let ⟨r, q, d, hg, hA⟩ := h
  ⟨r, q, _, hneg r q d hg, fun a => by
    rw [hA a, show q ⁻¹' Bᶜ = (q ⁻¹' B)ᶜ from rfl, truthTableAnswers_compl]
    simp [List.map_map, Function.comp_def]⟩

/-- Negating both the answers and the output of the combiner reduces `Aᶜ` to `Bᶜ`, when such
combiners are admissible. -/
theorem compl (hneg : ∀ r q d, Good r q d → Good r q fun x => !d (x.1, x.2.map (!·)))
    (h : TruthTableReducibleBy Good A B) : TruthTableReducibleBy Good Aᶜ Bᶜ :=
  let ⟨r, q, d, hg, hA⟩ := h
  ⟨r, q, _, hneg r q d hg, fun a => by
    rw [Set.mem_compl_iff, hA a, show q ⁻¹' Bᶜ = (q ⁻¹' B)ᶜ from rfl, truthTableAnswers_compl]
    simp [List.map_map, Function.comp_def]⟩

end TruthTableReducibleBy

/-- A many-one reduction is a truth-table reduction asking the single query `f a` and returning
its answer, when that data is admissible. -/
theorem ManyOneReducibleBy.truthTableReducibleBy {GoodF : (α → β) → Prop}
    {Good : (α → ℕ) → (α × ℕ → β) → (α × List Bool → Bool) → Prop}
    (hgood : ∀ f, GoodF f → Good (fun _ => 1) (fun x => f x.1) fun x => x.2.headD false)
    (h : ManyOneReducibleBy GoodF A B) : TruthTableReducibleBy Good A B :=
  let ⟨f, hf, hA⟩ := h
  ⟨_, _, _, hgood f hf, fun a => by simp [truthTableAnswers, hA a]⟩

/-- A many-one reduction is a positive truth-table reduction asking the single query `f a` and
returning its answer, when that data is admissible. -/
theorem ManyOneReducibleBy.pttReducibleBy {GoodF : (α → β) → Prop}
    {Good : (α → ℕ) → (α × ℕ → β) → (α × List Bool → Bool) → Prop}
    (hgood : ∀ f, GoodF f → Good (fun _ => 1) (fun x => f x.1) fun x => x.2.headD false)
    (h : ManyOneReducibleBy GoodF A B) : PTTReducibleBy Good A B :=
  h.truthTableReducibleBy fun f hf => ⟨hgood f hf, fun _ _ _ => headD_false_le_of_forall₂⟩

namespace PTTReducibleBy

variable {Good : (α → ℕ) → (α × ℕ → β) → (α × List Bool → Bool) → Prop}

/-- More admissible data give more positive truth-table reductions. -/
theorem mono {Good' : (α → ℕ) → (α × ℕ → β) → (α × List Bool → Bool) → Prop}
    (hle : ∀ r q d, Good r q d → Good' r q d) (h : PTTReducibleBy Good A B) :
    PTTReducibleBy Good' A B :=
  TruthTableReducibleBy.mono (fun r q d ⟨hg, hm⟩ => ⟨hle r q d hg, hm⟩) h

/-- Forgetting positivity gives an ordinary truth-table reduction, transferring admissibility
along `hgood`. -/
theorem truthTableReducibleBy
    {Good' : (α → ℕ) → (α × ℕ → β) → (α × List Bool → Bool) → Prop}
    (hgood : ∀ r q d, Good r q d →
      (∀ a u v, List.Forall₂ (· ≤ ·) u v → d (a, u) ≤ d (a, v)) → Good' r q d)
    (h : PTTReducibleBy Good A B) : TruthTableReducibleBy Good' A B :=
  TruthTableReducibleBy.mono (fun r q d ⟨hg, hm⟩ => hgood r q d hg hm) h

/-- Forgetting positivity with unchanged admissible data `Good`. -/
theorem toTruthTableReducibleBy (h : PTTReducibleBy Good A B) :
    TruthTableReducibleBy Good A B :=
  h.truthTableReducibleBy fun _ _ _ hg _ => hg

end PTTReducibleBy

namespace DTTReducibleBy

variable {Good : (α → ℕ) → (α × ℕ → β) → Prop}

/-- More admissible data give more reductions. -/
theorem mono {Good' : (α → ℕ) → (α × ℕ → β) → Prop} (hle : ∀ r q, Good r q → Good' r q)
    (h : DTTReducibleBy Good A B) : DTTReducibleBy Good' A B :=
  let ⟨r, q, hg, hA⟩ := h
  ⟨r, q, hle r q hg, hA⟩

/-- A disjunctive reduction is a truth-table reduction with combiner `List.any id`, when that
combiner is admissible. -/
theorem truthTableReducibleBy
    {Good' : (α → ℕ) → (α × ℕ → β) → (α × List Bool → Bool) → Prop}
    (hgood : ∀ r q, Good r q → Good' r q fun x => x.2.any id) (h : DTTReducibleBy Good A B) :
    TruthTableReducibleBy Good' A B :=
  let ⟨r, q, hg, hA⟩ := h
  ⟨r, q, _, hgood r q hg, fun a => by
    simp [hA a, truthTableAnswers, List.any_eq_true, List.mem_ofFn, Fin.exists_iff]⟩

/-- A disjunctive reduction is a positive truth-table reduction with combiner `List.any id`, when
that combiner is admissible. -/
theorem pttReducibleBy
    {Good' : (α → ℕ) → (α × ℕ → β) → (α × List Bool → Bool) → Prop}
    (hgood : ∀ r q, Good r q → Good' r q fun x => x.2.any id) (h : DTTReducibleBy Good A B) :
    PTTReducibleBy Good' A B :=
  h.truthTableReducibleBy fun r q hg =>
    ⟨hgood r q hg, fun _ _ _ => List.any_id_le_of_forall₂⟩

end DTTReducibleBy

namespace CTTReducibleBy

variable {Good : (α → ℕ) → (α × ℕ → β) → Prop}

/-- More admissible data give more reductions. -/
theorem mono {Good' : (α → ℕ) → (α × ℕ → β) → Prop} (hle : ∀ r q, Good r q → Good' r q)
    (h : CTTReducibleBy Good A B) : CTTReducibleBy Good' A B :=
  let ⟨r, q, hg, hA⟩ := h
  ⟨r, q, hle r q hg, hA⟩

/-- A conjunctive reduction is a truth-table reduction with combiner `List.all id`, when that
combiner is admissible. -/
theorem truthTableReducibleBy
    {Good' : (α → ℕ) → (α × ℕ → β) → (α × List Bool → Bool) → Prop}
    (hgood : ∀ r q, Good r q → Good' r q fun x => x.2.all id) (h : CTTReducibleBy Good A B) :
    TruthTableReducibleBy Good' A B :=
  let ⟨r, q, hg, hA⟩ := h
  ⟨r, q, _, hgood r q hg, fun a => by
    simp [hA a, truthTableAnswers, List.all_eq_true, List.mem_ofFn, Fin.forall_iff]⟩

/-- A conjunctive reduction is a positive truth-table reduction with combiner `List.all id`, when
that combiner is admissible. -/
theorem pttReducibleBy
    {Good' : (α → ℕ) → (α × ℕ → β) → (α × List Bool → Bool) → Prop}
    (hgood : ∀ r q, Good r q → Good' r q fun x => x.2.all id) (h : CTTReducibleBy Good A B) :
    PTTReducibleBy Good' A B :=
  h.truthTableReducibleBy fun r q hg =>
    ⟨hgood r q hg, fun _ _ _ => List.all_id_le_of_forall₂⟩

end CTTReducibleBy

/-- A many-one reduction is a disjunctive reduction asking the single query `f a`, when that data
is admissible. -/
theorem ManyOneReducibleBy.dttReducibleBy {GoodF : (α → β) → Prop}
    {Good : (α → ℕ) → (α × ℕ → β) → Prop} (hgood : ∀ f, GoodF f → Good (fun _ => 1) fun x => f x.1)
    (h : ManyOneReducibleBy GoodF A B) : DTTReducibleBy Good A B :=
  let ⟨f, hf, hA⟩ := h
  ⟨_, _, hgood f hf, fun a => by simp [hA a]⟩

/-- A many-one reduction is a conjunctive reduction asking the single query `f a`, when that data
is admissible. -/
theorem ManyOneReducibleBy.cttReducibleBy {GoodF : (α → β) → Prop}
    {Good : (α → ℕ) → (α × ℕ → β) → Prop} (hgood : ∀ f, GoodF f → Good (fun _ => 1) fun x => f x.1)
    (h : ManyOneReducibleBy GoodF A B) : CTTReducibleBy Good A B :=
  let ⟨f, hf, hA⟩ := h
  ⟨_, _, hgood f hf, fun a => by simp [hA a]⟩

/-- **De Morgan duality.** The disjunctive reductions of `A` to `B` are the conjunctive reductions
of `Aᶜ` to `Bᶜ`, with the same data. -/
theorem dttReducibleBy_iff_cttReducibleBy_compl {Good : (α → ℕ) → (α × ℕ → β) → Prop} :
    DTTReducibleBy Good A B ↔ CTTReducibleBy Good Aᶜ Bᶜ :=
  exists₂_congr fun _ _ => and_congr_right fun _ => forall_congr' fun _ =>
    ⟨fun h => by simp [h], fun h => by simpa [not_forall] using not_congr h⟩

/-! ### Nonadaptive composition -/

/-- Composite query generator with block stride `M a`: query index `t` asks inner query `t % M a`
of outer query `q (a, t / M a)`. -/
def truthTableCompQuery (q : α × ℕ → β) (q' : β × ℕ → γ) (M : α → ℕ) (p : α × ℕ) : γ :=
  q' (q (p.1, p.2 / M p.1), p.2 % M p.1)

/-- Within block `i` of stride `M a`, offset `j < M a` recovers `q' (q (a, i), j)`. -/
theorem truthTableCompQuery_mul_add (q : α × ℕ → β) (q' : β × ℕ → γ) (M : α → ℕ)
    (a : α) (i : ℕ) {j : ℕ} (hj : j < M a) :
    truthTableCompQuery q q' M (a, i * M a + j) = q' (q (a, i), j) := by
  simp [truthTableCompQuery, mul_comm i, Nat.mul_add_div (Nat.zero_lt_of_lt hj),
    Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj]

/-- The combiner of a composite truth-table reduction: block `i` of the answer word, of length
`r' (q (a, i))` and starting at `i * M a`, is decided by `d'`, and `d` combines the `r a`
decisions. -/
def truthTableCompCombiner (r : α → ℕ) (q : α × ℕ → β) (d : α × List Bool → Bool)
    (r' : β → ℕ) (d' : β × List Bool → Bool) (M : α → ℕ) (x : α × List Bool) : Bool :=
  d (x.1, (List.range (r x.1)).map fun i =>
    d' (q (x.1, i), (x.2.drop (i * M x.1)).take (r' (q (x.1, i)))))

/-- **Correctness of the composite combiner.** If block `i` of the composite queries `Q`, of
length `M a`, starts with the `r' (q (a, i))` second-stage queries of `q (a, i)`, then the
composite combiner decides `L` from the answers to the `r a * M a` composite queries. -/
theorem mem_iff_truthTableCompCombiner {L : Set α} {r : α → ℕ} {q : α × ℕ → β}
    {d : α × List Bool → Bool} {r' : β → ℕ} {q' : β × ℕ → γ} {d' : β × List Bool → Bool}
    {M : α → ℕ} {Q : α × ℕ → γ}
    (hL : ∀ a, a ∈ L ↔ d (a, truthTableAnswers (q ⁻¹' B) r a) = true)
    (hB : ∀ b, b ∈ B ↔ d' (b, truthTableAnswers (q' ⁻¹' C) r' b) = true)
    (hM : ∀ a, ∀ i < r a, r' (q (a, i)) ≤ M a)
    (hQ : ∀ a, ∀ i < r a, ∀ j < r' (q (a, i)), Q (a, i * M a + j) = q' (q (a, i), j)) (a : α) :
    a ∈ L ↔ truthTableCompCombiner r q d r' d' M
      (a, truthTableAnswers (Q ⁻¹' C) (fun a => r a * M a) a) = true := by
  classical
  rw [hL a, truthTableCompCombiner, truthTableAnswers_eq_map_range]
  dsimp only
  suffices hmap : ((List.range (r a)).map fun i => d' (q (a, i),
      ((truthTableAnswers (Q ⁻¹' C) (fun a => r a * M a) a).drop (i * M a)).take
        (r' (q (a, i))))) = (List.range (r a)).map fun i => decide ((a, i) ∈ q ⁻¹' B) by
    rw [hmap]
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  have hend : i * M a + r' (q (a, i)) ≤ r a * M a :=
    calc i * M a + r' (q (a, i)) ≤ i * M a + M a := Nat.add_le_add_left (hM a i hi) _
      _ = (i + 1) * M a := (Nat.succ_mul i (M a)).symm
      _ ≤ r a * M a := Nat.mul_le_mul_right _ hi
  rw [truthTableAnswers_drop_take hend (hQ a i hi)]
  cases h : d' (q (a, i), truthTableAnswers (q' ⁻¹' C) r' (q (a, i))) <;> simp [hB, h]

/-- The composite combiner is monotone in the answers when both combiners are. -/
theorem truthTableCompCombiner_mono {r : α → ℕ} {q : α × ℕ → β}
    {d : α × List Bool → Bool} {r' : β → ℕ} {d' : β × List Bool → Bool} {M : α → ℕ}
    (hd : ∀ a u v, List.Forall₂ (· ≤ ·) u v → d (a, u) ≤ d (a, v))
    (hd' : ∀ b u v, List.Forall₂ (· ≤ ·) u v → d' (b, u) ≤ d' (b, v)) (a : α)
    (u v : List Bool) (huv : List.Forall₂ (· ≤ ·) u v) :
    truthTableCompCombiner r q d r' d' M (a, u) ≤ truthTableCompCombiner r q d r' d' M (a, v) :=
  hd _ _ _ <| (List.forall₂_map_left_iff.trans List.forall₂_map_right_iff).mpr <|
    List.forall₂_same.mpr fun _ _ => hd' _ _ _ (List.forall₂_take _ (List.forall₂_drop _ huv))

/-- Truth-table reductions compose whenever each admissible pair admits a block stride `M` making
the composite count, quotient/remainder query map and composite combiner admissible. -/
theorem TruthTableReducibleBy.trans
    {Good₁ : (α → ℕ) → (α × ℕ → β) → (α × List Bool → Bool) → Prop}
    {Good₂ : (β → ℕ) → (β × ℕ → γ) → (β × List Bool → Bool) → Prop}
    {Good₃ : (α → ℕ) → (α × ℕ → γ) → (α × List Bool → Bool) → Prop}
    (hcomp : ∀ r₁ q₁ d₁ r₂ q₂ d₂, Good₁ r₁ q₁ d₁ → Good₂ r₂ q₂ d₂ →
      ∃ M : α → ℕ, (∀ a, ∀ i < r₁ a, r₂ (q₁ (a, i)) ≤ M a) ∧
        Good₃ (fun a => r₁ a * M a) (truthTableCompQuery q₁ q₂ M)
          (truthTableCompCombiner r₁ q₁ d₁ r₂ d₂ M))
    (hAB : TruthTableReducibleBy Good₁ A B) (hBC : TruthTableReducibleBy Good₂ B C) :
    TruthTableReducibleBy Good₃ A C := by
  obtain ⟨r₁, q₁, d₁, hg₁, hA⟩ := hAB
  obtain ⟨r₂, q₂, d₂, hg₂, hB⟩ := hBC
  obtain ⟨M, hM, hg₃⟩ := hcomp r₁ q₁ d₁ r₂ q₂ d₂ hg₁ hg₂
  exact ⟨_, _, _, hg₃, mem_iff_truthTableCompCombiner hA hB hM fun a i hi _ hj =>
    truthTableCompQuery_mul_add q₁ q₂ M a i (hj.trans_le (hM a i hi))⟩

/-- Bounded-query truth-table reductions with query bounds `k₁` and `k₂` compose with query bound
`k₁ * k₂`, using constant block stride `k₂` and `(i / k₂, i % k₂)` query indexing. -/
theorem TruthTableReducibleBy.trans_bounded {k₁ k₂ : ℕ}
    {Good₁ : (α → ℕ) → (α × ℕ → β) → (α × List Bool → Bool) → Prop}
    {Good₂ : (β → ℕ) → (β × ℕ → γ) → (β × List Bool → Bool) → Prop}
    {Good₃ : (α → ℕ) → (α × ℕ → γ) → (α × List Bool → Bool) → Prop}
    (hk₁ : ∀ r₁ q₁ d₁, Good₁ r₁ q₁ d₁ → ∀ a, r₁ a ≤ k₁)
    (hk₂ : ∀ r₂ q₂ d₂, Good₂ r₂ q₂ d₂ → ∀ b, r₂ b ≤ k₂)
    (hcomp : ∀ r₁ q₁ d₁ r₂ q₂ d₂, Good₁ r₁ q₁ d₁ → Good₂ r₂ q₂ d₂ →
      (∀ a, r₁ a * k₂ ≤ k₁ * k₂) →
      Good₃ (fun a => r₁ a * k₂) (truthTableCompQuery q₁ q₂ fun _ => k₂)
        (truthTableCompCombiner r₁ q₁ d₁ r₂ d₂ fun _ => k₂))
    (hAB : TruthTableReducibleBy Good₁ A B) (hBC : TruthTableReducibleBy Good₂ B C) :
    TruthTableReducibleBy Good₃ A C :=
  hAB.trans (fun r₁ q₁ d₁ r₂ q₂ d₂ hg₁ hg₂ =>
    ⟨fun _ => k₂, fun _ _ _ => hk₂ r₂ q₂ d₂ hg₂ _,
      hcomp r₁ q₁ d₁ r₂ q₂ d₂ hg₁ hg₂ fun a => Nat.mul_le_mul_right k₂ (hk₁ r₁ q₁ d₁ hg₁ a)⟩)
    hBC

/-- Positive truth-table reductions compose, preserving monotonicity of the combiner. -/
theorem PTTReducibleBy.trans
    {Good₁ : (α → ℕ) → (α × ℕ → β) → (α × List Bool → Bool) → Prop}
    {Good₂ : (β → ℕ) → (β × ℕ → γ) → (β × List Bool → Bool) → Prop}
    {Good₃ : (α → ℕ) → (α × ℕ → γ) → (α × List Bool → Bool) → Prop}
    (hcomp : ∀ r₁ q₁ d₁ r₂ q₂ d₂, Good₁ r₁ q₁ d₁ → Good₂ r₂ q₂ d₂ →
      ∃ M : α → ℕ, (∀ a, ∀ i < r₁ a, r₂ (q₁ (a, i)) ≤ M a) ∧
        Good₃ (fun a => r₁ a * M a) (truthTableCompQuery q₁ q₂ M)
          (truthTableCompCombiner r₁ q₁ d₁ r₂ d₂ M))
    (hAB : PTTReducibleBy Good₁ A B) (hBC : PTTReducibleBy Good₂ B C) :
    PTTReducibleBy Good₃ A C :=
  TruthTableReducibleBy.trans (fun r₁ q₁ d₁ r₂ q₂ d₂ ⟨hg₁, hm₁⟩ ⟨hg₂, hm₂⟩ =>
    let ⟨M, hM, hg₃⟩ := hcomp r₁ q₁ d₁ r₂ q₂ d₂ hg₁ hg₂
    ⟨M, hM, hg₃, truthTableCompCombiner_mono hm₁ hm₂⟩) hAB hBC

/-- Bounded-query positive truth-table reductions with query bounds `k₁` and `k₂` compose with
query bound `k₁ * k₂`, preserving monotonicity of the combiner. -/
theorem PTTReducibleBy.trans_bounded {k₁ k₂ : ℕ}
    {Good₁ : (α → ℕ) → (α × ℕ → β) → (α × List Bool → Bool) → Prop}
    {Good₂ : (β → ℕ) → (β × ℕ → γ) → (β × List Bool → Bool) → Prop}
    {Good₃ : (α → ℕ) → (α × ℕ → γ) → (α × List Bool → Bool) → Prop}
    (hk₁ : ∀ r₁ q₁ d₁, Good₁ r₁ q₁ d₁ → ∀ a, r₁ a ≤ k₁)
    (hk₂ : ∀ r₂ q₂ d₂, Good₂ r₂ q₂ d₂ → ∀ b, r₂ b ≤ k₂)
    (hcomp : ∀ r₁ q₁ d₁ r₂ q₂ d₂, Good₁ r₁ q₁ d₁ → Good₂ r₂ q₂ d₂ →
      (∀ a, r₁ a * k₂ ≤ k₁ * k₂) →
      Good₃ (fun a => r₁ a * k₂) (truthTableCompQuery q₁ q₂ fun _ => k₂)
        (truthTableCompCombiner r₁ q₁ d₁ r₂ d₂ fun _ => k₂))
    (hAB : PTTReducibleBy Good₁ A B) (hBC : PTTReducibleBy Good₂ B C) :
    PTTReducibleBy Good₃ A C :=
  TruthTableReducibleBy.trans_bounded
    (fun r₁ q₁ d₁ h => hk₁ r₁ q₁ d₁ h.1) (fun r₂ q₂ d₂ h => hk₂ r₂ q₂ d₂ h.1)
    (fun r₁ q₁ d₁ r₂ q₂ d₂ ⟨hg₁, hm₁⟩ ⟨hg₂, hm₂⟩ hmul =>
      ⟨hcomp r₁ q₁ d₁ r₂ q₂ d₂ hg₁ hg₂ hmul, truthTableCompCombiner_mono hm₁ hm₂⟩)
    hAB hBC

/-- Active `(outerIndex, innerIndex)` pairs of a two-stage query batch `(r, q)` followed by `r'`.
Unlike fixed-stride padding, this list contains only active second-stage indices, so disjunctive and
conjunctive quantifiers over all indices below its length remain exact even when some inner counts
are zero or smaller than the maximum. -/
def truthTableCompPairs (r : α → ℕ) (q : α × ℕ → β) (r' : β → ℕ) (a : α) : List (ℕ × ℕ) :=
  (List.range (r a)).flatMap fun i => (List.range (r' (q (a, i)))).map fun j => (i, j)

/-- Flattened query generator reading the `t`-th active `(outerIndex, innerIndex)` pair of
`truthTableCompPairs`. -/
def dttCompQuery (r : α → ℕ) (q : α × ℕ → β) (r' : β → ℕ) (q' : β × ℕ → γ)
    (x : α × ℕ) : γ :=
  let ij := (truthTableCompPairs r q r' x.1)[x.2]?.getD (0, 0)
  q' (q (x.1, ij.1), ij.2)

/-- When `r a ≤ k₁` and every active inner count is at most `k₂`, there are at most `k₁ * k₂`
active composite query pairs. -/
theorem length_truthTableCompPairs_le {r : α → ℕ} {q : α × ℕ → β} {r' : β → ℕ}
    {k₁ k₂ : ℕ} {a : α} (hr : r a ≤ k₁) (hr' : ∀ i < r a, r' (q (a, i)) ≤ k₂) :
    (truthTableCompPairs r q r' a).length ≤ k₁ * k₂ :=
  (List.length_flatMap_le fun i hi => by
    simpa using hr' i (List.mem_range.mp hi)).trans (by simpa using Nat.mul_le_mul_right k₂ hr)

/-- Disjunctive truth-table reductions compose by flattening the active query pairs. -/
theorem DTTReducibleBy.trans
    {Good₁ : (α → ℕ) → (α × ℕ → β) → Prop}
    {Good₂ : (β → ℕ) → (β × ℕ → γ) → Prop}
    {Good₃ : (α → ℕ) → (α × ℕ → γ) → Prop}
    (hcomp : ∀ r₁ q₁ r₂ q₂, Good₁ r₁ q₁ → Good₂ r₂ q₂ →
      Good₃ (fun a => (truthTableCompPairs r₁ q₁ r₂ a).length) (dttCompQuery r₁ q₁ r₂ q₂))
    (hAB : DTTReducibleBy Good₁ A B) (hBC : DTTReducibleBy Good₂ B C) :
    DTTReducibleBy Good₃ A C := by
  obtain ⟨r₁, q₁, hg₁, hA⟩ := hAB
  obtain ⟨r₂, q₂, hg₂, hB⟩ := hBC
  refine ⟨_, _, hcomp r₁ q₁ r₂ q₂ hg₁ hg₂, fun a => (hA a).trans ⟨?_, ?_⟩⟩
  · rintro ⟨i, hi, hq₁B⟩
    obtain ⟨j, hj, hq₂C⟩ := (hB (q₁ (a, i))).mp hq₁B
    obtain ⟨t, ht, hget⟩ := List.getElem_of_mem (l := truthTableCompPairs r₁ q₁ r₂ a)
      (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi,
        List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩⟩)
    exact ⟨t, ht, by simpa [dttCompQuery, List.getElem?_eq_getElem ht, hget] using hq₂C⟩
  · rintro ⟨t, ht, htC⟩
    obtain ⟨i, hi_mem, hmem'⟩ := List.mem_flatMap.mp
      (List.getElem_mem ht : (truthTableCompPairs r₁ q₁ r₂ a)[t] ∈ _)
    obtain ⟨j, hj_mem, hij⟩ := List.mem_map.mp hmem'
    exact ⟨i, List.mem_range.mp hi_mem, (hB (q₁ (a, i))).mpr ⟨j, List.mem_range.mp hj_mem, by
      simpa [dttCompQuery, List.getElem?_eq_getElem ht, ← hij] using htC⟩⟩

/-- Bounded disjunctive truth-table reductions with query bounds `k₁` and `k₂` compose with query
bound `k₁ * k₂`. -/
theorem DTTReducibleBy.trans_bounded {k₁ k₂ : ℕ}
    {Good₁ : (α → ℕ) → (α × ℕ → β) → Prop}
    {Good₂ : (β → ℕ) → (β × ℕ → γ) → Prop}
    {Good₃ : (α → ℕ) → (α × ℕ → γ) → Prop}
    (hk₁ : ∀ r₁ q₁, Good₁ r₁ q₁ → ∀ a, r₁ a ≤ k₁)
    (hk₂ : ∀ r₂ q₂, Good₂ r₂ q₂ → ∀ b, r₂ b ≤ k₂)
    (hcomp : ∀ r₁ q₁ r₂ q₂, Good₁ r₁ q₁ → Good₂ r₂ q₂ →
      (∀ a, (truthTableCompPairs r₁ q₁ r₂ a).length ≤ k₁ * k₂) →
      Good₃ (fun a => (truthTableCompPairs r₁ q₁ r₂ a).length) (dttCompQuery r₁ q₁ r₂ q₂))
    (hAB : DTTReducibleBy Good₁ A B) (hBC : DTTReducibleBy Good₂ B C) :
    DTTReducibleBy Good₃ A C :=
  hAB.trans (fun r₁ q₁ r₂ q₂ hg₁ hg₂ => hcomp r₁ q₁ r₂ q₂ hg₁ hg₂ fun a =>
    length_truthTableCompPairs_le (hk₁ r₁ q₁ hg₁ a) fun _ _ => hk₂ r₂ q₂ hg₂ _) hBC

/-- Conjunctive truth-table reductions compose, by De Morgan duality with `DTTReducibleBy.trans`. -/
theorem CTTReducibleBy.trans
    {Good₁ : (α → ℕ) → (α × ℕ → β) → Prop}
    {Good₂ : (β → ℕ) → (β × ℕ → γ) → Prop}
    {Good₃ : (α → ℕ) → (α × ℕ → γ) → Prop}
    (hcomp : ∀ r₁ q₁ r₂ q₂, Good₁ r₁ q₁ → Good₂ r₂ q₂ →
      Good₃ (fun a => (truthTableCompPairs r₁ q₁ r₂ a).length) (dttCompQuery r₁ q₁ r₂ q₂))
    (hAB : CTTReducibleBy Good₁ A B) (hBC : CTTReducibleBy Good₂ B C) :
    CTTReducibleBy Good₃ A C := by
  have h := dttReducibleBy_iff_cttReducibleBy_compl (Good := Good₃) (A := Aᶜ) (B := Cᶜ)
  rw [compl_compl, compl_compl] at h
  exact h.mp (DTTReducibleBy.trans (B := Bᶜ) hcomp
    (by rwa [dttReducibleBy_iff_cttReducibleBy_compl, compl_compl, compl_compl])
    (by rwa [dttReducibleBy_iff_cttReducibleBy_compl, compl_compl, compl_compl]))

/-- Bounded conjunctive truth-table reductions with query bounds `k₁` and `k₂` compose with query
bound `k₁ * k₂`. -/
theorem CTTReducibleBy.trans_bounded {k₁ k₂ : ℕ}
    {Good₁ : (α → ℕ) → (α × ℕ → β) → Prop}
    {Good₂ : (β → ℕ) → (β × ℕ → γ) → Prop}
    {Good₃ : (α → ℕ) → (α × ℕ → γ) → Prop}
    (hk₁ : ∀ r₁ q₁, Good₁ r₁ q₁ → ∀ a, r₁ a ≤ k₁)
    (hk₂ : ∀ r₂ q₂, Good₂ r₂ q₂ → ∀ b, r₂ b ≤ k₂)
    (hcomp : ∀ r₁ q₁ r₂ q₂, Good₁ r₁ q₁ → Good₂ r₂ q₂ →
      (∀ a, (truthTableCompPairs r₁ q₁ r₂ a).length ≤ k₁ * k₂) →
      Good₃ (fun a => (truthTableCompPairs r₁ q₁ r₂ a).length) (dttCompQuery r₁ q₁ r₂ q₂))
    (hAB : CTTReducibleBy Good₁ A B) (hBC : CTTReducibleBy Good₂ B C) :
    CTTReducibleBy Good₃ A C :=
  hAB.trans (fun r₁ q₁ r₂ q₂ hg₁ hg₂ => hcomp r₁ q₁ r₂ q₂ hg₁ hg₂ fun a =>
    length_truthTableCompPairs_le (hk₁ r₁ q₁ hg₁ a) fun _ _ => hk₂ r₂ q₂ hg₂ _) hBC

/-! ### Self-query-avoiding autoreductions -/

/-- `A` is many-one autoreducible by an admissible map: some fixed-point-free `f` satisfying `Good`
reduces `A` to itself. -/
def ManyOneAutoreducibleBy (Good : (α → α) → Prop) (A : Set α) : Prop :=
  ManyOneReducibleBy (fun f => Good f ∧ ∀ a, f a ≠ a) A A

namespace ManyOneAutoreducibleBy

variable {Good Good' : (α → α) → Prop}

/-- Forgetting fixed-point-freeness gives an ordinary many-one self-reduction. -/
theorem manyOneReducibleBy (h : ManyOneAutoreducibleBy Good A) : ManyOneReducibleBy Good A A :=
  ManyOneReducibleBy.mono (fun _ hf => hf.1) h

/-- Enlarging the admissible maps preserves many-one autoreducibility. -/
theorem mono (hle : ∀ f, Good f → Good' f) (h : ManyOneAutoreducibleBy Good A) :
    ManyOneAutoreducibleBy Good' A :=
  ManyOneReducibleBy.mono (fun f hf => ⟨hle f hf.1, hf.2⟩) h

/-- A many-one autoreduction of `A` is also one of `Aᶜ`. -/
theorem compl (h : ManyOneAutoreducibleBy Good A) : ManyOneAutoreducibleBy Good Aᶜ :=
  ManyOneReducibleBy.compl h

/-- Every member of a many-one autoreducible set maps to a distinct member. -/
theorem exists_mem_ne (h : ManyOneAutoreducibleBy Good A) : ∀ a ∈ A, ∃ y ∈ A, y ≠ a :=
  let ⟨f, ⟨_, hne⟩, hA⟩ := h
  fun a ha => ⟨f a, (hA a).mp ha, hne a⟩

/-- Every non-member of a many-one autoreducible set maps to a distinct non-member. -/
theorem exists_notMem_ne (h : ManyOneAutoreducibleBy Good A) : ∀ a ∉ A, ∃ n ∉ A, n ≠ a :=
  fun a ha => h.compl.exists_mem_ne a ha

end ManyOneAutoreducibleBy

/-- A singleton set is never fixed-point-free many-one autoreducible. -/
theorem not_manyOneAutoreducibleBy_singleton {Good : (α → α) → Prop} (a₀ : α) :
    ¬ ManyOneAutoreducibleBy Good ({a₀} : Set α) := fun h => by
  obtain ⟨y, hy, hne⟩ := h.exists_mem_ne a₀ (Set.mem_singleton a₀)
  exact hne (Set.mem_singleton_iff.mp hy)

/-- A co-singleton set is never fixed-point-free many-one autoreducible. -/
theorem not_manyOneAutoreducibleBy_compl_singleton {Good : (α → α) → Prop} (a₀ : α) :
    ¬ ManyOneAutoreducibleBy Good ({a₀}ᶜ : Set α) := fun h => by
  obtain ⟨n, hn, hne⟩ := h.exists_notMem_ne a₀ (fun ha => ha (Set.mem_singleton a₀))
  exact hne (Set.mem_singleton_iff.mp (Classical.not_not.mp hn))

/-- `A` is truth-table autoreducible by admissible data: a truth-table reduction of `A` to itself
whose active queries avoid the input (`∀ a i, i < r a → q (a, i) ≠ a`). -/
def TruthTableAutoreducibleBy
    (Good : (α → ℕ) → (α × ℕ → α) → (α × List Bool → Bool) → Prop) (A : Set α) : Prop :=
  TruthTableReducibleBy (fun r q d => Good r q d ∧ ∀ a i, i < r a → q (a, i) ≠ a) A A

/-- `A` is positively truth-table autoreducible by admissible data: a positive truth-table reduction
of `A` to itself whose active queries avoid the input. -/
def PTTAutoreducibleBy
    (Good : (α → ℕ) → (α × ℕ → α) → (α × List Bool → Bool) → Prop) (A : Set α) : Prop :=
  PTTReducibleBy (fun r q d => Good r q d ∧ ∀ a i, i < r a → q (a, i) ≠ a) A A

/-- `A` is disjunctively truth-table autoreducible by admissible data: a disjunctive reduction of
`A` to itself whose active queries avoid the input. -/
def DTTAutoreducibleBy (Good : (α → ℕ) → (α × ℕ → α) → Prop) (A : Set α) : Prop :=
  DTTReducibleBy (fun r q => Good r q ∧ ∀ a i, i < r a → q (a, i) ≠ a) A A

/-- `A` is conjunctively truth-table autoreducible by admissible data: a conjunctive reduction of
`A` to itself whose active queries avoid the input. -/
def CTTAutoreducibleBy (Good : (α → ℕ) → (α × ℕ → α) → Prop) (A : Set α) : Prop :=
  CTTReducibleBy (fun r q => Good r q ∧ ∀ a i, i < r a → q (a, i) ≠ a) A A

namespace TruthTableAutoreducibleBy

variable {Good Good' : (α → ℕ) → (α × ℕ → α) → (α × List Bool → Bool) → Prop}

/-- Forgetting query avoidance gives an ordinary truth-table self-reduction. -/
theorem truthTableReducibleBy (h : TruthTableAutoreducibleBy Good A) :
    TruthTableReducibleBy Good A A :=
  TruthTableReducibleBy.mono (fun _ _ _ hg => hg.1) h

/-- Enlarging the admissible data preserves truth-table autoreducibility. -/
theorem mono (hle : ∀ r q d, Good r q d → Good' r q d) (h : TruthTableAutoreducibleBy Good A) :
    TruthTableAutoreducibleBy Good' A :=
  TruthTableReducibleBy.mono (fun r q d ⟨hg, hne⟩ => ⟨hle r q d hg, hne⟩) h

/-- Negating both the answers and output of the combiner reduces `Aᶜ` to `Aᶜ` without changing the
queries, so query avoidance is preserved automatically. -/
theorem compl (hneg : ∀ r q d, Good r q d → Good r q fun x => !d (x.1, x.2.map (!·)))
    (h : TruthTableAutoreducibleBy Good A) : TruthTableAutoreducibleBy Good Aᶜ :=
  TruthTableReducibleBy.compl (fun r q d ⟨hg, hne⟩ => ⟨hneg r q d hg, hne⟩) h

/-- A decision predicate `g` for `A` gives a zero-query truth-table autoreduction whenever the
zero-query data `(fun _ => 0, Prod.fst, fun x => g x.1)` is admissible. -/
theorem of_decide {g : α → Bool} (hAg : ∀ a, a ∈ A ↔ g a = true)
    (hg : Good (fun _ => 0) Prod.fst fun x => g x.1) :
    TruthTableAutoreducibleBy Good A :=
  ⟨fun _ => 0, Prod.fst, fun x => g x.1, ⟨hg, fun _ _ hi => (Nat.not_lt_zero _ hi).elim⟩, hAg⟩

end TruthTableAutoreducibleBy

namespace PTTAutoreducibleBy

variable {Good Good' : (α → ℕ) → (α × ℕ → α) → (α × List Bool → Bool) → Prop}

/-- Forgetting query avoidance gives an ordinary positive truth-table self-reduction. -/
theorem pttReducibleBy (h : PTTAutoreducibleBy Good A) : PTTReducibleBy Good A A :=
  PTTReducibleBy.mono (fun _ _ _ hg => hg.1) h

/-- Enlarging the admissible data preserves positive truth-table autoreducibility. -/
theorem mono (hle : ∀ r q d, Good r q d → Good' r q d) (h : PTTAutoreducibleBy Good A) :
    PTTAutoreducibleBy Good' A :=
  PTTReducibleBy.mono (fun r q d ⟨hg, hne⟩ => ⟨hle r q d hg, hne⟩) h

/-- Forgetting positivity gives a truth-table autoreduction. -/
theorem truthTableAutoreducibleBy (h : PTTAutoreducibleBy Good A) :
    TruthTableAutoreducibleBy Good A :=
  PTTReducibleBy.toTruthTableReducibleBy h

/-- A decision predicate `g` for `A` gives a zero-query positive truth-table autoreduction, since
`fun x => g x.1` ignores the answer word and is therefore monotone in it. -/
theorem of_decide {g : α → Bool} (hAg : ∀ a, a ∈ A ↔ g a = true)
    (hg : Good (fun _ => 0) Prod.fst fun x => g x.1) :
    PTTAutoreducibleBy Good A :=
  ⟨fun _ => 0, Prod.fst, fun x => g x.1,
    ⟨⟨hg, fun _ _ hi => (Nat.not_lt_zero _ hi).elim⟩, fun _ _ _ _ => le_rfl⟩, hAg⟩

end PTTAutoreducibleBy

namespace DTTAutoreducibleBy

variable {Good Good' : (α → ℕ) → (α × ℕ → α) → Prop}

/-- Forgetting query avoidance gives an ordinary disjunctive self-reduction. -/
theorem dttReducibleBy (h : DTTAutoreducibleBy Good A) : DTTReducibleBy Good A A :=
  DTTReducibleBy.mono (fun _ _ hg => hg.1) h

/-- Enlarging the admissible data preserves disjunctive autoreducibility. -/
theorem mono (hle : ∀ r q, Good r q → Good' r q) (h : DTTAutoreducibleBy Good A) :
    DTTAutoreducibleBy Good' A :=
  DTTReducibleBy.mono (fun r q ⟨hg, hne⟩ => ⟨hle r q hg, hne⟩) h

/-- A disjunctive autoreduction is a positive truth-table autoreduction with combiner
`List.any id`. -/
theorem pttAutoreducibleBy
    {GoodT : (α → ℕ) → (α × ℕ → α) → (α × List Bool → Bool) → Prop}
    (hgood : ∀ r q, Good r q → GoodT r q fun x => x.2.any id)
    (h : DTTAutoreducibleBy Good A) : PTTAutoreducibleBy GoodT A :=
  DTTReducibleBy.pttReducibleBy (fun r q ⟨hg, hne⟩ => ⟨hgood r q hg, hne⟩) h

/-- A disjunctive autoreduction is a truth-table autoreduction with combiner `List.any id`. -/
theorem truthTableAutoreducibleBy
    {GoodT : (α → ℕ) → (α × ℕ → α) → (α × List Bool → Bool) → Prop}
    (hgood : ∀ r q, Good r q → GoodT r q fun x => x.2.any id)
    (h : DTTAutoreducibleBy Good A) : TruthTableAutoreducibleBy GoodT A :=
  (h.pttAutoreducibleBy hgood).truthTableAutoreducibleBy

end DTTAutoreducibleBy

namespace CTTAutoreducibleBy

variable {Good Good' : (α → ℕ) → (α × ℕ → α) → Prop}

/-- Forgetting query avoidance gives an ordinary conjunctive self-reduction. -/
theorem cttReducibleBy (h : CTTAutoreducibleBy Good A) : CTTReducibleBy Good A A :=
  CTTReducibleBy.mono (fun _ _ hg => hg.1) h

/-- Enlarging the admissible data preserves conjunctive autoreducibility. -/
theorem mono (hle : ∀ r q, Good r q → Good' r q) (h : CTTAutoreducibleBy Good A) :
    CTTAutoreducibleBy Good' A :=
  CTTReducibleBy.mono (fun r q ⟨hg, hne⟩ => ⟨hle r q hg, hne⟩) h

/-- A conjunctive autoreduction is a positive truth-table autoreduction with combiner
`List.all id`. -/
theorem pttAutoreducibleBy
    {GoodT : (α → ℕ) → (α × ℕ → α) → (α × List Bool → Bool) → Prop}
    (hgood : ∀ r q, Good r q → GoodT r q fun x => x.2.all id)
    (h : CTTAutoreducibleBy Good A) : PTTAutoreducibleBy GoodT A :=
  CTTReducibleBy.pttReducibleBy (fun r q ⟨hg, hne⟩ => ⟨hgood r q hg, hne⟩) h

/-- A conjunctive autoreduction is a truth-table autoreduction with combiner `List.all id`. -/
theorem truthTableAutoreducibleBy
    {GoodT : (α → ℕ) → (α × ℕ → α) → (α × List Bool → Bool) → Prop}
    (hgood : ∀ r q, Good r q → GoodT r q fun x => x.2.all id)
    (h : CTTAutoreducibleBy Good A) : TruthTableAutoreducibleBy GoodT A :=
  (h.pttAutoreducibleBy hgood).truthTableAutoreducibleBy

end CTTAutoreducibleBy

/-- **De Morgan duality for autoreductions.** Disjunctive autoreductions of `A` are the conjunctive
autoreductions of `Aᶜ`, with the same queries. -/
theorem dttAutoreducibleBy_iff_cttAutoreducibleBy_compl
    {Good : (α → ℕ) → (α × ℕ → α) → Prop} :
    DTTAutoreducibleBy Good A ↔ CTTAutoreducibleBy Good Aᶜ :=
  dttReducibleBy_iff_cttReducibleBy_compl

/-- A fixed-point-free many-one autoreduction is a one-query truth-table autoreduction. -/
theorem ManyOneAutoreducibleBy.truthTableAutoreducibleBy {GoodF : (α → α) → Prop}
    {Good : (α → ℕ) → (α × ℕ → α) → (α × List Bool → Bool) → Prop}
    (hgood : ∀ f, GoodF f → Good (fun _ => 1) (fun x => f x.1) fun x => x.2.headD false)
    (h : ManyOneAutoreducibleBy GoodF A) : TruthTableAutoreducibleBy Good A :=
  ManyOneReducibleBy.truthTableReducibleBy
    (fun f ⟨hf, hne⟩ => ⟨hgood f hf, fun a _ _ => hne a⟩) h

/-- A fixed-point-free many-one autoreduction is a one-query positive truth-table autoreduction. -/
theorem ManyOneAutoreducibleBy.pttAutoreducibleBy {GoodF : (α → α) → Prop}
    {Good : (α → ℕ) → (α × ℕ → α) → (α × List Bool → Bool) → Prop}
    (hgood : ∀ f, GoodF f → Good (fun _ => 1) (fun x => f x.1) fun x => x.2.headD false)
    (h : ManyOneAutoreducibleBy GoodF A) : PTTAutoreducibleBy Good A :=
  ManyOneReducibleBy.pttReducibleBy
    (fun f ⟨hf, hne⟩ => ⟨hgood f hf, fun a _ _ => hne a⟩) h

/-- A fixed-point-free many-one autoreduction is a one-query disjunctive autoreduction. -/
theorem ManyOneAutoreducibleBy.dttAutoreducibleBy {GoodF : (α → α) → Prop}
    {Good : (α → ℕ) → (α × ℕ → α) → Prop}
    (hgood : ∀ f, GoodF f → Good (fun _ => 1) fun x => f x.1)
    (h : ManyOneAutoreducibleBy GoodF A) : DTTAutoreducibleBy Good A :=
  ManyOneReducibleBy.dttReducibleBy (fun f ⟨hf, hne⟩ => ⟨hgood f hf, fun a _ _ => hne a⟩) h

/-- A fixed-point-free many-one autoreduction is a one-query conjunctive autoreduction. -/
theorem ManyOneAutoreducibleBy.cttAutoreducibleBy {GoodF : (α → α) → Prop}
    {Good : (α → ℕ) → (α × ℕ → α) → Prop}
    (hgood : ∀ f, GoodF f → Good (fun _ => 1) fun x => f x.1)
    (h : ManyOneAutoreducibleBy GoodF A) : CTTAutoreducibleBy Good A :=
  ManyOneReducibleBy.cttReducibleBy (fun f ⟨hf, hne⟩ => ⟨hgood f hf, fun a _ _ => hne a⟩) h

/-- A many-one reduction of `Aᶜ` to `A` cannot fix any input (`a ∉ A ↔ a ∈ A` is impossible);
asking its single query `f a` and negating the answer gives a one-query truth-table autoreduction of
`A`. -/
theorem ManyOneReducibleBy.truthTableAutoreducibleBy_of_compl {GoodF : (α → α) → Prop}
    {Good : (α → ℕ) → (α × ℕ → α) → (α × List Bool → Bool) → Prop}
    (hgood : ∀ f, GoodF f → Good (fun _ => 1) (fun x => f x.1) fun x => !x.2.headD false)
    (h : ManyOneReducibleBy GoodF Aᶜ A) : TruthTableAutoreducibleBy Good A := by
  obtain ⟨f, hf, hA⟩ := h
  have hne : ∀ a, f a ≠ a := fun a heq => by simpa [Set.mem_compl_iff, heq] using hA a
  exact ⟨_, _, _, ⟨hgood f hf, fun a _ _ => hne a⟩,
    fun a => by simpa [truthTableAnswers, Set.mem_compl_iff] using not_congr (hA a)⟩

end Cslib.Complexity
