/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.DSteps
public import Mathlib.Data.Fintype.Basic

/-!
# States with named values

The dealing program of [AnthropicVPVNP2026] keeps its values in a state of the interpreter, a
function from paths to trees. A value with the name `x` sits at the path `nm x`, for an injective
code `nm` of the names, so a state by names `st` is the state `Function.extend nm st fun _ => .nil`,
which is empty at the paths that code no name. The steps of the interpreter act on such states by
names: an operation and a guess write one name (`exec_op`, `exec_bits`), and a pick writes the
names of the option that it chooses (`exec_pick`). After a list of assignments in which every name
gets one fixed value, the state is known (`foldl_assignAll`).

The operations of the dealing program look their results up in tries: `trieOf code f` has the
value `f a` at the path `code a` (`tget_trieOf`).

## Main definitions

* `optionTree`, `assignAll`: an option of a pick (a list of assignments to names) as a tree, and
  the state by names after its assignments.
* `trieOf`: the trie of a function on a finite type.

## Main results

* `exec_pick`, `exec_op`, `exec_bits`: the steps of the interpreter on states by names.
* `foldl_assignAll`: the state after assignments that give every name one value.
* `tget_trieOf`, `size_trieOf_le`: the values of a trie of a function, and its size.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3: the program `G` in the proof
of Theorem J.3 (p. 54). Ported from the source module `Nc.Dl.Names`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Dealing

open Function Interpreter Interpreter.Tree

section Names

variable {ν : Type*} [DecidableEq ν] {nm : ν → List Bool}

/-- An option of a pick, the assignments `o` of values to names, as a tree: the list of the
pairs of the code of a name and its value. -/
@[expose] def optionTree (nm : ν → List Bool) (o : List (ν × Tree)) : Tree :=
  listT (o.map fun a => .cons (ofBits (nm a.1)) a.2)

/-- The state by names after the assignments `o`, in their order. -/
@[expose] def assignAll (st : ν → Tree) (o : List (ν × Tree)) : ν → Tree :=
  o.foldl (fun st a => update st a.1 a.2) st

/-- The assignments of a list in which every name gets the value `w` of it. -/
theorem assignAll_apply {w : ν → Tree} {o : List (ν × Tree)} (h : ∀ a ∈ o, a.2 = w a.1)
    (st : ν → Tree) (x : ν) :
    assignAll st o x = if ∃ a ∈ o, a.1 = x then w x else st x := by
  induction o generalizing st with
  | nil => simp [assignAll]
  | cons b o ih =>
    rw [assignAll, List.foldl_cons, ← assignAll, ih fun a ha => h a (List.mem_cons_of_mem _ ha)]
    rcases eq_or_ne b.1 x with rfl | hb
    · simp [h b List.mem_cons_self]
    · rw [update_of_ne hb.symm]
      exact if_congr (by simp [or_and_right, exists_or, hb]) rfl rfl

/-- **Assignments of fixed values.** Every assignment of the option `o i` is to a name `x` of
`i` (`own x = some i`), of the value `w x`, and every name of `i` is assigned in `o i`. After the
options of the indices of `s`, a name of an index of `s` has its value `w x`, and every other
name its value in `st`. -/
theorem foldl_assignAll {ι : Type*} [DecidableEq ι] {own : ν → Option ι} {o : ι → List (ν × Tree)}
    {w : ν → Tree} (ho : ∀ i, ∀ a ∈ o i, own a.1 = some i ∧ a.2 = w a.1)
    (hall : ∀ i x, own x = some i → ∃ a ∈ o i, a.1 = x) (s : List ι) (st : ν → Tree) (x : ν) :
    s.foldl (fun st i => assignAll st (o i)) st x =
      if ∃ i ∈ s, own x = some i then w x else st x := by
  induction s generalizing st with
  | nil => simp
  | cons i s ih =>
    rw [List.foldl_cons, ih, assignAll_apply fun a ha => (ho i a ha).2]
    have : (∃ a ∈ o i, a.1 = x) ↔ own x = some i :=
      ⟨fun ⟨a, ha, e⟩ => e ▸ (ho i a ha).1, hall i x⟩
    by_cases h1 : ∃ j ∈ s, own x = some j <;> by_cases h2 : own x = some i <;> simp [this, h1, h2]

variable (hnm : Injective nm)
include hnm

private theorem assignS_extend (st : ν → Tree) (o : List (ν × Tree)) :
    assignS (extend nm st fun _ => .nil) (optionTree nm o) =
      extend nm (assignAll st o) fun _ => .nil := by
  unfold assignS optionTree assignAll
  rw [toList_listT]
  induction o generalizing st with
  | nil => rfl
  | cons a o ih =>
    simp only [List.map_cons, List.foldl_cons, hd_cons, tl_cons, path_ofBits,
      ← hnm.extend_update, ih]

/-- A pick at the name `x`, whose table lists the options `opts` at the value of `x`. -/
theorem exec_pick {m : ℕ} {st : ν → Tree} {x : ν} {tab : Tree} {opts : List (List (ν × Tree))}
    (h : (tget (st x).path tab).toList = opts.map (optionTree nm)) :
    (DStep.pick (nm x) tab).exec m (extend nm st fun _ => .nil) =
      opts.map fun o => extend nm (assignAll st o) fun _ => .nil := by
  simp [DStep.exec, hnm.extend_apply, h, assignS_extend hnm]

/-- An operation writes the value of its table at the values of `x` and `y` to `z`. -/
theorem exec_op {m : ℕ} {st : ν → Tree} {x y z : ν} {φ : Tree} :
    (DStep.op (nm x) (nm y) (nm z) φ).exec m (extend nm st fun _ => .nil) =
      [extend nm (update st z (tget (st y).path (tget (st x).path φ))) fun _ => .nil] := by
  simp [DStep.exec, hnm.extend_apply, hnm.extend_update]

/-- A guess at `y` of the reversed bit lists of length `m`, if the value of `x` is not empty. -/
theorem exec_bits {m : ℕ} {st : ν → Tree} {x y : ν} :
    (DStep.bits (nm x) (nm y)).exec m (extend nm st fun _ => .nil) =
      if st x = .nil then [extend nm st fun _ => .nil] else
        (allBits m).map fun u => extend nm (update st y (ofBits u.reverse)) fun _ => .nil := by
  simp [DStep.exec, hnm.extend_apply, hnm.extend_update]

end Names

section Tries

variable {α : Type*} [Fintype α] {code : α → List Bool}

/-- The trie with the value `f a` at the path `code a`, for every `a`. -/
@[expose] noncomputable def trieOf (code : α → List Bool) (f : α → Tree) : Tree :=
  (Finset.univ : Finset α).toList.foldr (fun a t => tset (code a) (f a) t) .nil

theorem tget_trieOf (hc : Injective code) (f : α → Tree) (a : α) :
    tget (code a) (trieOf code f) = f a := by
  suffices ∀ l : List α, a ∈ l → tget (code a) (l.foldr (fun a t => tset (code a) (f a) t) .nil) =
      f a from this _ (by simp)
  intro l hl
  induction l with
  | nil => simp at hl
  | cons b l ih => by_cases hab : a = b <;> simp_all [tget_tset, hc.eq_iff]

private theorem size_hd_add_size_tl (t : Tree) : t.hd.size + t.tl.size ≤ t.size + 1 := by
  cases t <;> simp only [hd, tl, size] <;> omega

private theorem size_tset (p : List Bool) (v t : Tree) :
    (tset p v t).size ≤ t.size + v.size + 4 * p.length + 4 := by
  induction p generalizing t with
  | nil => have := size_tl_le t; simp only [tset, size, List.length_nil]; omega
  | cons b p ih =>
    have h1 := size_hd_add_size_tl t
    have h2 := size_hd_add_size_tl t.tl
    cases b
    · have := ih t.tl.hd; simp only [tset, size, List.length_cons]; omega
    · have := ih t.tl.tl; simp only [tset, size, List.length_cons]; omega

/-- The size of the trie of a function with values of size at most `s`, for codes of length at
most `L`. -/
theorem size_trieOf_le {f : α → Tree} {L s : ℕ} (hL : ∀ a, (code a).length ≤ L)
    (hs : ∀ a, (f a).size ≤ s) :
    (trieOf code f).size ≤ Fintype.card α * (s + 4 * L + 4) + 1 := by
  rw [← Finset.card_univ, ← Finset.length_toList, trieOf]
  induction (Finset.univ : Finset α).toList with
  | nil => simp [size]
  | cons a l ih =>
    have := size_tset (code a) (f a) (l.foldr (fun a t => tset (code a) (f a) t) .nil)
    have := hL a
    have := hs a
    simp only [List.foldr_cons, List.length_cons, add_mul, one_mul]; omega

end Tries

end Cslib.Circuits.Arithmetic.Separation.Dealing
