/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, beside `Nat.rfindOpt` in `Mathlib/Computability/Partrec.lean`)

public import CslibFrontier.Init
public import Mathlib.Computability.Partrec
public import Mathlib.Data.Set.Card
import Mathlib.Computability.Primrec.List

/-!
# Enumerating the distinct values of a sequence of partial outputs

A sequence `f : ℕ → Option β` lists, possibly with repetitions and gaps, the elements of its range
`{b | ∃ n, f n = some b}`. Typically `f n` decodes `n` as a program and a time bound and reports
the output of the program if it halts in time, so the range is a computably enumerable set.
`Nat.distinctValues f n` lists the distinct values among `f 0, …, f (n - 1)` in order of first
appearance, and `Nat.nthDistinctValue f i` is the `i`-th distinct value of the whole sequence,
found by an unbounded search over `n`. When the range is finite, every element has an index below
the size of the range. When `f` depends primitive recursively on a parameter, both are
computable in the parameter: this is the enumeration step in counting arguments of Kolmogorov
complexity, which describe an element of a computably enumerable set by its index.

## Main definitions

* `Nat.distinctValues`: the distinct values of a sequence up to a bound, in order of first
  appearance.
* `Nat.nthDistinctValue`: the `i`-th distinct value of a sequence, if there is one.

## Main results

* `Nat.mem_distinctValues`, `Nat.nodup_distinctValues`, `Nat.distinctValues_prefix`: the lists
  contain exactly the values seen so far, without repetitions, and grow by extension.
* `Nat.length_distinctValues_le_ncard`, `Nat.exists_length_distinctValues_eq_ncard`: for a finite
  range, the lists are no longer than the range and eventually as long as it.
* `Nat.mem_nthDistinctValue_iff`, `Nat.exists_eq_some_of_mem_nthDistinctValue`,
  `Nat.exists_mem_nthDistinctValue_of_finite`: the `i`-th distinct value is in the range, and, for
  a finite range, every element of it is the `i`-th distinct value for some `i` below its size.
* `Primrec.distinctValues`, `Partrec.nthDistinctValue`: computability in a parameter.
-/

public section

namespace Nat

variable {α β : Type*} [DecidableEq β]

/-- The distinct values among `f 0, …, f (n - 1)`, in order of first appearance. The body is
exposed so that concrete lists can be evaluated by `decide`. -/
@[expose] def distinctValues (f : ℕ → Option β) : ℕ → List β
  | 0 => []
  | n + 1 =>
    match f n with
    | none => distinctValues f n
    | some b => if b ∈ distinctValues f n then distinctValues f n else distinctValues f n ++ [b]

/-- Fold a partial output into a list of distinct values. -/
private def insertNew (L : List β) : Option β → List β
  | none => L
  | some b => if b ∈ L then L else L ++ [b]

@[simp]
theorem distinctValues_zero (f : ℕ → Option β) : distinctValues f 0 = [] := rfl

/-- The lists of distinct values grow by extension. -/
theorem distinctValues_prefix (f : ℕ → Option β) {m n : ℕ} (h : m ≤ n) :
    distinctValues f m <+: distinctValues f n := by
  induction h with
  | refl => exact List.prefix_refl _
  | @step n _ ih =>
    rw [distinctValues]
    cases f n with
    | none => exact ih
    | some b =>
      dsimp only
      split_ifs
      · exact ih
      · exact ih.trans (List.prefix_append _ _)

/-- The distinct values up to `n` are the values `f j = some b` with `j < n`. -/
theorem mem_distinctValues {f : ℕ → Option β} {n : ℕ} {b : β} :
    b ∈ distinctValues f n ↔ ∃ j < n, f j = some b := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : b ∈ distinctValues f (n + 1) ↔ b ∈ distinctValues f n ∨ f n = some b := by
      rw [distinctValues]
      cases f n with
      | none => simp
      | some c =>
        dsimp only
        split_ifs with hc <;> simp [eq_comm]
        grind
    rw [hstep, ih]
    exact ⟨fun | .inl ⟨j, hj, h⟩ => ⟨j, by omega, h⟩ | .inr h => ⟨n, by omega, h⟩,
      fun ⟨j, hj, h⟩ => match Nat.lt_succ_iff_lt_or_eq.mp hj with
        | .inl hj => .inl ⟨j, hj, h⟩ | .inr rfl => .inr h⟩

theorem nodup_distinctValues (f : ℕ → Option β) (n : ℕ) : (distinctValues f n).Nodup := by
  induction n with
  | zero => exact List.nodup_nil
  | succ n ih =>
    rw [distinctValues]
    cases f n with
    | none => exact ih
    | some c =>
      dsimp only
      split_ifs with hc
      · exact ih
      · exact ih.append (List.nodup_singleton c) (by simpa using hc)

/-- For a finite range, the lists of distinct values are no longer than the range. -/
theorem length_distinctValues_le_ncard {f : ℕ → Option β} (hf : {b | ∃ n, f n = some b}.Finite)
    (n : ℕ) : (distinctValues f n).length ≤ {b | ∃ n, f n = some b}.ncard := by
  rw [← List.toFinset_card_of_nodup (nodup_distinctValues f n), Set.ncard_eq_toFinset_card _ hf]
  exact Finset.card_le_card fun c hc => by
    obtain ⟨j, -, hj⟩ := mem_distinctValues.mp (List.mem_toFinset.mp hc)
    exact hf.mem_toFinset.mpr ⟨j, hj⟩

/-- For a finite range, the list of distinct values eventually contains the whole range. -/
theorem exists_length_distinctValues_eq_ncard {f : ℕ → Option β}
    (hf : {b | ∃ n, f n = some b}.Finite) :
    ∃ N, (distinctValues f N).length = {b | ∃ n, f n = some b}.ncard := by
  choose g hg using fun x : hf.toFinset => hf.mem_toFinset.mp x.2
  let N := Finset.univ.sup g + 1
  refine ⟨N, le_antisymm (length_distinctValues_le_ncard hf N) ?_⟩
  rw [← List.toFinset_card_of_nodup (nodup_distinctValues f N), Set.ncard_eq_toFinset_card _ hf]
  exact Finset.card_le_card fun b hb => List.mem_toFinset.mpr <|
    mem_distinctValues.mpr ⟨g ⟨b, hb⟩,
      Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ (⟨b, hb⟩ : hf.toFinset))), hg ⟨b, hb⟩⟩

/-- The `i`-th distinct value of the sequence `f`, in order of first appearance: the search for a
bound `n` such that `distinctValues f n` has an `i`-th entry. -/
def nthDistinctValue (f : ℕ → Option β) (i : ℕ) : Part β :=
  Nat.rfindOpt fun n => (distinctValues f n)[i]?

theorem mem_nthDistinctValue_iff {f : ℕ → Option β} {i : ℕ} {b : β} :
    b ∈ nthDistinctValue f i ↔ ∃ n, (distinctValues f n)[i]? = some b := by
  refine Nat.rfindOpt_mono fun {b m n} hmn h => ?_
  obtain ⟨t, ht⟩ := distinctValues_prefix f hmn
  rw [← ht, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

/-- The distinct values of `f` are in its range. -/
theorem exists_eq_some_of_mem_nthDistinctValue {f : ℕ → Option β} {i : ℕ} {b : β}
    (h : b ∈ nthDistinctValue f i) : ∃ n, f n = some b := by
  obtain ⟨n, hn⟩ := mem_nthDistinctValue_iff.mp h
  obtain ⟨j, -, hj⟩ := mem_distinctValues.mp (List.mem_of_getElem? hn)
  exact ⟨j, hj⟩

/-- For a finite range, the indices of the distinct values are below the size of the range. -/
theorem lt_ncard_of_mem_nthDistinctValue {f : ℕ → Option β} (hf : {b | ∃ n, f n = some b}.Finite)
    {i : ℕ} {b : β} (h : b ∈ nthDistinctValue f i) : i < {b | ∃ n, f n = some b}.ncard := by
  obtain ⟨n, hn⟩ := mem_nthDistinctValue_iff.mp h
  exact (List.getElem?_eq_some_iff.mp hn).1.trans_le (length_distinctValues_le_ncard hf n)

/-- For a finite range, every element of the range is the `i`-th distinct value for some `i` below
the size of the range. -/
theorem exists_mem_nthDistinctValue_of_finite {f : ℕ → Option β}
    (hf : {b | ∃ n, f n = some b}.Finite) {b : β} {n : ℕ} (hb : f n = some b) :
    ∃ i < {b | ∃ n, f n = some b}.ncard, b ∈ nthDistinctValue f i := by
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem (mem_distinctValues.mpr ⟨n, n.lt_succ_self, hb⟩)
  exact ⟨i, hi.trans_le (length_distinctValues_le_ncard hf _),
    mem_nthDistinctValue_iff.mpr ⟨n + 1, List.getElem?_eq_some_iff.mpr ⟨hi, hget⟩⟩⟩

end Nat

variable {α β : Type*} [Primcodable α] [Primcodable β] [DecidableEq β]

private theorem primrec₂_insertNew : Primrec₂ (Nat.insertNew : List β → Option β → List β) := by
  have hmem : PrimrecRel fun (L : List β) (b : β) => b ∈ L :=
    (PrimrecRel.exists_mem_list Primrec.eq).of_eq fun L b => by simp
  refine Primrec₂.mk ?_
  refine (Primrec.option_casesOn Primrec.snd Primrec.fst
    (Primrec₂.mk (f := fun (p : List β × Option β) (b : β) => if b ∈ p.1 then p.1 else p.1 ++ [b])
      (Primrec.ite (hmem.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      (Primrec.fst.comp Primrec.fst)
      (Primrec.list_concat.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)))).of_eq ?_
  rintro ⟨L, _ | b⟩ <;> rfl

/-- The distinct values of a sequence depending primitive recursively on a parameter are primitive
recursive in the parameter and the bound. -/
theorem Primrec.distinctValues {f : α → ℕ → Option β} (hf : Primrec₂ f) :
    Primrec₂ fun a n => Nat.distinctValues (f a) n := by
  refine (Primrec.nat_rec (f := fun _ => ([] : List β))
    (g := fun a (p : ℕ × List β) => Nat.insertNew p.2 (f a p.1)) (Primrec.const [])
    (primrec₂_insertNew.comp₂ (Primrec.snd.comp₂ Primrec₂.right)
      (hf.comp₂ Primrec₂.left (Primrec.fst.comp₂ Primrec₂.right)))).of_eq fun a n => ?_
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp only
    rw [Nat.distinctValues, ← ih]
    cases f a n <;> rfl

/-- The `i`-th distinct value of a sequence depending primitive recursively on a parameter is
partial recursive in the parameter and `i`. -/
theorem Partrec.nthDistinctValue {f : α → ℕ → Option β} (hf : Primrec₂ f) :
    Partrec₂ fun a i => Nat.nthDistinctValue (f a) i := by
  have h : Computable₂ fun (ai : α × ℕ) (n : ℕ) => (Nat.distinctValues (f ai.1) n)[ai.2]? :=
    (Primrec.list_getElem?.comp ((Primrec.distinctValues hf).comp (Primrec.fst.comp Primrec.fst)
      Primrec.snd) (Primrec.snd.comp Primrec.fst)).to_comp
  exact (Partrec.rfindOpt h).of_eq fun _ => rfl
