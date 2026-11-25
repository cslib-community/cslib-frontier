/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF
public import Std.Data.HashMap.Lemmas

/-! # Renaming the variables of a formula to `0, …, k - 1`, with a hash map

A formula over `ℕ` may use arbitrary variable names, such as `0` and `10⁹`. A solver that keeps
arrays indexed by variable would then allocate by the largest name.
`Cslib.Logic.PL.CNF.denseRenaming` numbers the `k` distinct variables of `φ` as `0, …, k - 1`, in
order of first occurrence (the numbering of `Cslib.Logic.PL.CNF.denseRelabel`), in one pass over
the occurrences with a hash map. It returns the renaming `toDense` and a map `fromDense` back:

* `fromDense` undoes `toDense` on the variables of `φ`
  (`Cslib.Logic.PL.CNF.DenseRenaming.fromDense_toDense`), so renaming `φ` along `toDense` and then
  along `fromDense` gives `φ` back (`Cslib.Logic.PL.CNF.DenseRenaming.relabel_relabel`);
* `fromDense` is injective (`Cslib.Logic.PL.CNF.DenseRenaming.fromDense_injective`), so it carries
  certificates for the renamed formula back to `φ`;
* the renamed variables are below `k` (`Cslib.Logic.PL.CNF.DenseRenaming.toDense_lt`).

The kernel does not evaluate the hash map; this renaming is for compiled code.

## Main definitions

* `Cslib.Logic.PL.CNF.denseRenaming`: the renaming of a formula, with the map back.
-/

@[expose] public section

namespace Cslib.Logic.PL

/-- The state of the renaming pass: the number given to each variable seen so far, and the
variables in the order of their numbers. -/
structure CNF.DenseNames where
  /-- The number of each variable seen so far. -/
  index : Std.HashMap ℕ ℕ
  /-- The variables seen so far, in the order of their numbers. -/
  names : Array ℕ

namespace CNF.DenseNames

/-- Give `v` the next number, unless it already has one. -/
def add (s : DenseNames) (v : ℕ) : DenseNames :=
  if s.index.contains v then s else ⟨s.index.insert v s.names.size, s.names.push v⟩

/-- The numbers and the names are inverse to each other. -/
structure Inv (s : DenseNames) : Prop where
  /-- A numbered variable is the name at its number. -/
  name : ∀ v i, s.index[v]? = some i → ∃ h : i < s.names.size, s.names[i] = v
  /-- Every name has its own number. -/
  index : ∀ i (h : i < s.names.size), s.index[s.names[i]]? = some i

theorem inv_empty : Inv ⟨∅, #[]⟩ :=
  ⟨fun v i h => by simp at h, fun i h => by simp at h⟩

theorem Inv.add {s : DenseNames} (hs : s.Inv) (v : ℕ) : (s.add v).Inv := by
  unfold DenseNames.add
  split
  · exact hs
  · rename_i hv
    have hnone : s.index[v]? = none :=
      Std.HashMap.getElem?_eq_none_of_contains_eq_false (by simpa using hv)
    refine ⟨fun w i h => ?_, fun i hi => ?_⟩
    · simp only [Std.HashMap.getElem?_insert, beq_iff_eq] at h
      split at h
      · obtain ⟨rfl, rfl⟩ : v = w ∧ s.names.size = i := ⟨‹_›, Option.some.inj h⟩
        exact ⟨by simp, by simp⟩
      · obtain ⟨hi, hw⟩ := hs.name w i h
        exact ⟨by simp; omega, by simp [Array.getElem_push_lt hi, hw]⟩
    · simp only [Array.size_push] at hi
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | rfl
      · have hidx := hs.index i hlt
        have hne : v ≠ s.names[i] := fun h => by simp [← h, hnone] at hidx
        simp [Array.getElem_push_lt hlt, Std.HashMap.getElem?_insert, hne, hidx]
      · simp

/-- Adding a variable keeps the numbers already given. -/
theorem getElem?_add_of_isSome {s : DenseNames} {w : ℕ} (hw : (s.index[w]?).isSome)
    (v : ℕ) : (s.add v).index[w]? = s.index[w]? := by
  unfold DenseNames.add
  split
  · rfl
  · rename_i hv
    have hnone : s.index[v]? = none :=
      Std.HashMap.getElem?_eq_none_of_contains_eq_false (by simpa using hv)
    simp [Std.HashMap.getElem?_insert, show v ≠ w from fun h => by simp [h ▸ hnone] at hw]

theorem isSome_add (s : DenseNames) (v : ℕ) : ((s.add v).index[v]?).isSome := by
  unfold DenseNames.add
  split
  · exact Std.HashMap.contains_eq_isSome_getElem?.symm.trans (by simpa using ‹_›)
  · simp

/-- Adding a list of variables keeps the invariant and numbers every variable of the list. -/
theorem Inv.foldl {s : DenseNames} (hs : s.Inv) (vs : List ℕ) :
    (vs.foldl DenseNames.add s).Inv ∧
      (∀ w : ℕ, (s.index[w]?).isSome → (vs.foldl DenseNames.add s).index[w]? = s.index[w]?) ∧
      ∀ v ∈ vs, ((vs.foldl DenseNames.add s).index[v]?).isSome := by
  induction vs generalizing s with
  | nil => exact ⟨hs, fun _ _ => rfl, by simp⟩
  | cons v vs ih =>
    obtain ⟨h₁, h₂, h₃⟩ := ih (hs.add v)
    refine ⟨h₁, fun w hw => ?_, fun u hu => ?_⟩
    · simpa only [List.foldl_cons, getElem?_add_of_isSome hw] using
        h₂ w (by rwa [getElem?_add_of_isSome hw])
    · rcases List.mem_cons.1 hu with rfl | hu
      · simpa only [List.foldl_cons, h₂ u (isSome_add s u)] using isSome_add s u
      · exact h₃ u hu

end CNF.DenseNames

/-- The renaming of the variables of a formula to `0, …, k - 1`, with the map back. -/
structure CNF.DenseRenaming where
  /-- The number of each variable, `0` for a variable not in the formula. -/
  toDense : ℕ → ℕ
  /-- The variable of each number: the `i`-th variable for `i < k`, and above every variable
  otherwise, so that the map is injective. -/
  fromDense : ℕ → ℕ
  /-- The number of distinct variables. -/
  size : ℕ

/-- The numbering of the variables of `φ`, in order of first occurrence. -/
def CNF.denseNames (φ : CNF ℕ) : CNF.DenseNames := φ.vars.foldl CNF.DenseNames.add ⟨∅, #[]⟩

/-- **The renaming of the variables of `φ` to `0, …, k - 1`.** -/
def CNF.denseRenaming (φ : CNF ℕ) : CNF.DenseRenaming :=
  let s := φ.denseNames
  { toDense := fun v => s.index.getD v 0
    fromDense := fun i => if h : i < s.names.size then s.names[i] else s.names.foldl max 0 + 1 + i
    size := s.names.size }

namespace CNF.DenseRenaming

variable {φ : CNF ℕ}

theorem denseNames_inv (φ : CNF ℕ) : φ.denseNames.Inv :=
  (DenseNames.inv_empty.foldl φ.vars).1

theorem isSome_denseNames {v : ℕ} (hv : v ∈ φ.vars) : (φ.denseNames.index[v]?).isSome :=
  (DenseNames.inv_empty.foldl φ.vars).2.2 v hv

/-- **The map back undoes the renaming** on the variables of `φ`. -/
theorem fromDense_toDense {v : ℕ} (hv : v ∈ φ.vars) :
    φ.denseRenaming.fromDense (φ.denseRenaming.toDense v) = v := by
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 (isSome_denseNames hv)
  obtain ⟨hlt, hname⟩ := (denseNames_inv φ).name v i hi
  simp [CNF.denseRenaming, Std.HashMap.getD_eq_getD_getElem?, hi, hlt, hname]

/-- **The renamed variables are below the number of distinct variables.** -/
theorem toDense_lt {v : ℕ} (hv : v ∈ φ.vars) :
    φ.denseRenaming.toDense v < φ.denseRenaming.size := by
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 (isSome_denseNames hv)
  obtain ⟨hlt, -⟩ := (denseNames_inv φ).name v i hi
  simpa [CNF.denseRenaming, Std.HashMap.getD_eq_getD_getElem?, hi] using hlt

theorem le_foldl_max (a : Array ℕ) (i : ℕ) (h : i < a.size) : a[i] ≤ a.foldl max 0 := by
  rw [← Array.foldl_toList]
  have hle (l : List ℕ) : ∀ b, (∀ x ∈ l, x ≤ l.foldl max b) ∧ b ≤ l.foldl max b := by
    induction l with
    | nil => simp
    | cons y l ih =>
      intro b; simp only [List.foldl_cons]
      exact ⟨fun x hx => (List.mem_cons.1 hx).elim
        (fun h => h ▸ (le_max_right b y).trans (ih _).2) ((ih (max b y)).1 x),
        (le_max_left b y).trans (ih _).2⟩
  exact (hle a.toList 0).1 _ (Array.getElem_mem_toList h)

/-- **The map back is injective.** -/
theorem fromDense_injective (φ : CNF ℕ) : Function.Injective φ.denseRenaming.fromDense := by
  have hinv := denseNames_inv φ
  intro i j h
  simp only [CNF.denseRenaming] at h
  split at h <;> split at h
  · rename_i hi hj
    exact Option.some.inj ((hinv.index i hi).symm.trans (h ▸ hinv.index j hj))
  · have := le_foldl_max φ.denseNames.names i ‹_›; omega
  · have := le_foldl_max φ.denseNames.names j ‹_›; omega
  · omega

/-- **Renaming along `toDense` and back gives `φ`.** -/
theorem relabel_relabel (φ : CNF ℕ) :
    (φ.relabel φ.denseRenaming.toDense).relabel φ.denseRenaming.fromDense = φ := by
  simp only [CNF.relabel, List.map_map]
  refine (List.map_congr_left fun c hc => ?_).trans (List.map_id φ)
  simp only [Function.comp_apply, Clause.relabel, List.map_map]
  exact (List.map_congr_left fun ⟨v, b⟩ hl => by
    simp [fromDense_toDense (CNF.mem_vars.2 ⟨c, hc, b, hl⟩)]).trans (List.map_id c)

end CNF.DenseRenaming

end Cslib.Logic.PL
