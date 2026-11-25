/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.Basic

/-!
# Mistake trees and the Littlestone dimension

A complete `d`-mistake tree for a concept class `C : ConceptClass α β`
[Littlestone1988, §3, Definition 2; DanielySabatoBenDavidShalevShwartz2015] is a complete binary
tree of height `d`. Its root is `C`, each internal node `C'` is labelled with an instance `x` and
two distinct branch labels `y₀ ≠ y₁` in `β`, the two children of `C'` are the restrictions
`versionSpace C' [(x, y₀)]` and `versionSpace C' [(x, y₁)]`, and every leaf is nonempty. When
`β = Bool`, the two distinct branch labels are necessarily `false` and `true`
(`hasMistakeTree_succ_bool`), recovering Littlestone's binary mistake trees. `HasMistakeTree d C`
states by recursion on `d` that such a tree of height `d` exists. `hasMistakeTree_iff_exists_tree`
identifies it with the explicit shattered-tree presentation (`MistakeTree` and
`MistakeTree.Shatters`) of [ShalevShwartzBenDavid2014, §21.1] and
[DanielySabatoBenDavidShalevShwartz2015]: a complete binary tree of height `d` with instances at
internal nodes and distinct labels on sibling edges whose `2 ^ d` root-to-leaf paths are all
realizable by `C`.

The **Littlestone dimension** `littlestoneDim C : ℕ∞` is the supremum of the heights of the
complete mistake trees for `C` (called the multiclass Littlestone dimension when `|β| > 2`).
Littlestone writes the binary quantity `K(C)` and sets `K(∅) = -1`; here `littlestoneDim ∅ = 0`,
and a class with complete mistake trees of every height has dimension `⊤`.

**Lower bound** [Littlestone1988, §3, Lemma 1; DanielySabatoBenDavidShalevShwartz2015]. An
adversary walking down a complete `d`-mistake tree forces every deterministic learner to err `d`
times: at a node `(x, y₀, y₁)` with `y₀ ≠ y₁`, at least one of `y₀` and `y₁` differs from the
learner's prediction `A h x` (`exists_realizable_mistakes_eq`). Hence
`littlestoneDim C ≤ mistakeBound A C` for every learner `A` (`littlestoneDim_le_mistakeBound`), and
`littlestoneDim C ≤ optimalMistakeBound C`. The matching upper bound, attained by the multiclass
standard optimal algorithm, is in `CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.SOA`.

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.MistakeBound.HasMistakeTree`: existence of a complete
  mistake tree of a given height.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.MistakeTree`: explicit complete binary mistake
  trees of height `d` with distinct sibling edge labels, together with `MistakeTree.path` and
  `MistakeTree.Shatters`.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.littlestoneDim`: the (binary or multiclass)
  Littlestone dimension.

## Main results

* `Cslib.MachineLearning.OnlineLearning.MistakeBound.hasMistakeTree_iff_exists_tree`: equivalence
  between recursive `HasMistakeTree` and explicit shattered mistake trees (`MistakeTree.Shatters`).
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.exists_realizable_mistakes_eq`: a complete
  `d`-mistake tree forces `d` mistakes on a realizable sequence of length `d`.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.littlestoneDim_le_mistakeBound`:
  [Littlestone1988, §3, Lemma 1; DanielySabatoBenDavidShalevShwartz2015], every deterministic
  learner makes at least `littlestoneDim C` mistakes in the worst case.

## References

* [A. Daniely, S. Sabato, S. Ben-David, S. Shalev-Shwartz, *Multiclass Learnability and the ERM
  Principle*][DanielySabatoBenDavidShalevShwartz2015]
* [N. Littlestone, *Learning quickly when irrelevant attributes abound: a new linear-threshold
  algorithm*][Littlestone1988]
* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.MistakeBound

open PACLearning (ConceptClass)

universe u v
variable {α : Type u} {β : Type v}

/-- `HasMistakeTree d C`: the class `C : ConceptClass α β` has a complete mistake tree of height `d`
[Littlestone1988, §3, Definition 2; DanielySabatoBenDavidShalevShwartz2015]. A tree of height `0` is
a nonempty root; a tree of height `d + 1` labels the root with an instance `x` and two distinct
labels `y₀ ≠ y₁` such that both restrictions `versionSpace C [(x, y₀)]` and
`versionSpace C [(x, y₁)]` have complete mistake trees of height `d`. -/
@[expose] def HasMistakeTree : ℕ → ConceptClass α β → Prop
  | 0, C => C.Nonempty
  | d + 1, C =>
    ∃ (x : α) (y₀ y₁ : β), y₀ ≠ y₁ ∧
      HasMistakeTree d (versionSpace C [(x, y₀)]) ∧
      HasMistakeTree d (versionSpace C [(x, y₁)])

@[simp] theorem hasMistakeTree_zero {C : ConceptClass α β} :
    HasMistakeTree 0 C ↔ C.Nonempty := Iff.rfl

theorem hasMistakeTree_succ {d : ℕ} {C : ConceptClass α β} :
    HasMistakeTree (d + 1) C ↔
      ∃ (x : α) (y₀ y₁ : β), y₀ ≠ y₁ ∧
        HasMistakeTree d (versionSpace C [(x, y₀)]) ∧
        HasMistakeTree d (versionSpace C [(x, y₁)]) :=
  Iff.rfl

/-- For Boolean labels, a root with two distinct branch labels is simply an instance `x` whose
`false` and `true` restrictions both admit trees of height `d`. -/
theorem hasMistakeTree_succ_bool {d : ℕ} {C : ConceptClass α Bool} :
    HasMistakeTree (d + 1) C ↔ ∃ x : α, ∀ y : Bool, HasMistakeTree d (versionSpace C [(x, y)]) :=
  ⟨fun ⟨x, y₀, y₁, _, _, _⟩ => ⟨x, fun y => by cases y₀ <;> cases y₁ <;> cases y <;> simp_all⟩,
    fun ⟨x, hx⟩ => ⟨x, false, true, Bool.false_ne_true, hx false, hx true⟩⟩

theorem HasMistakeTree.nonempty {d : ℕ} {C : ConceptClass α β} (h : HasMistakeTree d C) :
    C.Nonempty :=
  match d, h with
  | 0, h => h
  | _ + 1, ⟨_, _, _, _, h0, _⟩ => h0.nonempty.mono (versionSpace_subset _ _)

theorem HasMistakeTree.mono {d : ℕ} {C C' : ConceptClass α β} (h : HasMistakeTree d C)
    (hCC' : C ⊆ C') : HasMistakeTree d C' :=
  match d, h with
  | 0, h => Set.Nonempty.mono hCC' h
  | _ + 1, ⟨x, y₀, y₁, hne, h0, h1⟩ =>
    ⟨x, y₀, y₁, hne, h0.mono (versionSpace_mono hCC' _), h1.mono (versionSpace_mono hCC' _)⟩

/-- Pruning a complete mistake tree gives complete mistake trees of every smaller height. -/
theorem HasMistakeTree.of_le {d e : ℕ} {C : ConceptClass α β} (h : HasMistakeTree d C)
    (hed : e ≤ d) : HasMistakeTree e C :=
  match e, d, h, hed with
  | 0, _, h, _ => h.nonempty
  | _ + 1, 0, _, hed => absurd hed (Nat.not_succ_le_zero _)
  | _ + 1, _ + 1, ⟨x, y₀, y₁, hne, h0, h1⟩, hed =>
    ⟨x, y₀, y₁, hne, h0.of_le (Nat.le_of_succ_le_succ hed), h1.of_le (Nat.le_of_succ_le_succ hed)⟩

/-! ### Explicit shattered mistake trees -/

/-- An explicit complete binary mistake tree of height `d` with instances in `α` and edge labels in
`β` [Littlestone1988, §3, Definition 2; ShalevShwartzBenDavid2014, §21.1;
DanielySabatoBenDavidShalevShwartz2015]. A leaf has height `0`; an internal node of height `d + 1`
queries an instance `x` and branches on two distinct labels `y₀ ≠ y₁` into subtrees of height
`d`. -/
inductive MistakeTree (α : Type u) (β : Type v) : ℕ → Type (max u v)
  /-- The empty tree of height `0`. -/
  | leaf : MistakeTree α β 0
  /-- An internal node querying `x` with distinct branch labels `y₀ ≠ y₁` on its `false` and `true`
  children. -/
  | node {d : ℕ} (x : α) (y₀ y₁ : β) (hne : y₀ ≠ y₁)
      (left right : MistakeTree α β d) : MistakeTree α β (d + 1)

/-- The labelled sequence of length `d` along the root-to-leaf path `bs : Fin d → Bool` of a
complete mistake tree `T`. At each step `false` follows the `left` (`y₀`) branch and `true` follows
the `right` (`y₁`) branch. -/
@[expose] def MistakeTree.path : {d : ℕ} → MistakeTree α β d → (Fin d → Bool) → List (α × β)
  | 0, .leaf, _ => []
  | _ + 1, .node x y₀ y₁ _ left right, bs =>
    if bs 0 then (x, y₁) :: right.path (bs ∘ Fin.succ)
    else (x, y₀) :: left.path (bs ∘ Fin.succ)

@[simp] theorem MistakeTree.path_leaf (bs : Fin 0 → Bool) :
    (MistakeTree.leaf : MistakeTree α β 0).path bs = [] := rfl

@[simp] theorem MistakeTree.path_node {d : ℕ} (x : α) (y₀ y₁ : β) (hne : y₀ ≠ y₁)
    (left right : MistakeTree α β d) (bs : Fin (d + 1) → Bool) :
    (MistakeTree.node x y₀ y₁ hne left right).path bs =
      if bs 0 then (x, y₁) :: right.path (bs ∘ Fin.succ)
      else (x, y₀) :: left.path (bs ∘ Fin.succ) := rfl

@[simp] theorem MistakeTree.length_path {d : ℕ} (T : MistakeTree α β d) (bs : Fin d → Bool) :
    (T.path bs).length = d :=
  match d, T with
  | 0, .leaf => rfl
  | _ + 1, .node _ _ _ _ l r => by
      simp only [MistakeTree.path]; split <;> simp [l.length_path, r.length_path]

/-- A mistake tree `T` *shatters* `C` when every root-to-leaf path of `T` is realizable by `C`
[DanielySabatoBenDavidShalevShwartz2015; ShalevShwartzBenDavid2014, §21.1]. -/
@[expose] def MistakeTree.Shatters {d : ℕ} (T : MistakeTree α β d) (C : ConceptClass α β) : Prop :=
  ∀ bs : Fin d → Bool, Realizable C (T.path bs)

/-- Equivalence between recursive `HasMistakeTree` and explicit shattered mistake trees
[ShalevShwartzBenDavid2014, §21.1; DanielySabatoBenDavidShalevShwartz2015]: `C` has a complete
mistake tree of height `d` iff some `MistakeTree α β d` shatters `C`. -/
theorem hasMistakeTree_iff_exists_tree {d : ℕ} {C : ConceptClass α β} :
    HasMistakeTree d C ↔ ∃ T : MistakeTree α β d, T.Shatters C := by
  induction d generalizing C with
  | zero => exact ⟨fun hC => ⟨.leaf, fun _ => realizable_nil.mpr hC⟩,
      fun ⟨T, hT⟩ => by cases T; exact realizable_nil.mp (hT Fin.elim0)⟩
  | succ d ih =>
    refine ⟨fun ⟨x, y₀, y₁, hne, h0, h1⟩ =>
        let ⟨T₀, hT₀⟩ := ih.mp h0; let ⟨T₁, hT₁⟩ := ih.mp h1
        ⟨.node x y₀ y₁ hne T₀ T₁, fun bs => by
          simp only [MistakeTree.path]; split
          exacts [realizable_cons.mpr (hT₁ _), realizable_cons.mpr (hT₀ _)]⟩,
      fun ⟨.node x y₀ y₁ hne left right, hT⟩ =>
        ⟨x, y₀, y₁, hne,
          ih.mpr ⟨left, fun bs => realizable_cons.mp <| by
            simpa only [MistakeTree.path, Fin.cons_zero, Bool.false_eq_true, ↓reduceIte,
              Fin.cons_comp_succ] using hT (Fin.cons false bs)⟩,
          ih.mpr ⟨right, fun bs => realizable_cons.mp <| by
            simpa only [MistakeTree.path, Fin.cons_zero, ↓reduceIte,
              Fin.cons_comp_succ] using hT (Fin.cons true bs)⟩⟩⟩

/-! ### The Littlestone dimension -/

/-- The Littlestone dimension [Littlestone1988, §3; DanielySabatoBenDavidShalevShwartz2015]: the
supremum of the heights of the complete mistake trees for `C`, in `ℕ∞`. It is `0` for the empty
class, where Littlestone sets `K(∅) = -1`. -/
noncomputable def littlestoneDim (C : ConceptClass α β) : ℕ∞ :=
  ⨆ (d : ℕ) (_ : HasMistakeTree d C), (d : ℕ∞)

theorem le_littlestoneDim_of_hasMistakeTree {d : ℕ} {C : ConceptClass α β}
    (h : HasMistakeTree d C) : (d : ℕ∞) ≤ littlestoneDim C :=
  le_iSup₂ (f := fun (d : ℕ) (_ : HasMistakeTree d C) => (d : ℕ∞)) d h

theorem littlestoneDim_le_iff {C : ConceptClass α β} {m : ℕ∞} :
    littlestoneDim C ≤ m ↔ ∀ d : ℕ, HasMistakeTree d C → (d : ℕ∞) ≤ m := by
  simp [littlestoneDim]

theorem hasMistakeTree_of_le_littlestoneDim {d : ℕ} {C : ConceptClass α β} (hC : C.Nonempty)
    (hd : (d : ℕ∞) ≤ littlestoneDim C) : HasMistakeTree d C := by
  by_contra hnot
  rcases d with _ | d
  · exact hnot hC
  · have hle : littlestoneDim C ≤ d := littlestoneDim_le_iff.mpr fun e he => by
      exact_mod_cast Nat.lt_succ_iff.mp (lt_of_not_ge fun hed => hnot (he.of_le hed))
    have := hd.trans hle
    norm_cast at this; omega

/-- For a nonempty class, `d ≤ littlestoneDim C` iff `C` has a complete mistake tree of
height `d`. -/
theorem natCast_le_littlestoneDim_iff {d : ℕ} {C : ConceptClass α β} (hC : C.Nonempty) :
    (d : ℕ∞) ≤ littlestoneDim C ↔ HasMistakeTree d C :=
  ⟨hasMistakeTree_of_le_littlestoneDim hC, le_littlestoneDim_of_hasMistakeTree⟩

theorem littlestoneDim_mono {C C' : ConceptClass α β} (h : C ⊆ C') :
    littlestoneDim C ≤ littlestoneDim C' :=
  littlestoneDim_le_iff.mpr fun _ hd => le_littlestoneDim_of_hasMistakeTree (hd.mono h)

@[simp] theorem littlestoneDim_empty : littlestoneDim (∅ : ConceptClass α β) = 0 :=
  le_antisymm
    (littlestoneDim_le_iff.mpr fun _ hd => absurd hd.nonempty Set.not_nonempty_empty) bot_le

/-- If `y₀ ≠ y₁` and both restrictions of `C` at `(x, y₀)` and `(x, y₁)` are nonempty, the
Littlestone dimension of `C` exceeds the smaller of their dimensions: complete trees for both
combine under a root labelled `(x, y₀, y₁)`. -/
theorem min_littlestoneDim_add_one_le (C : ConceptClass α β) (x : α) {y₀ y₁ : β} (hne : y₀ ≠ y₁)
    (h0 : (versionSpace C [(x, y₀)]).Nonempty) (h1 : (versionSpace C [(x, y₁)]).Nonempty) :
    min (littlestoneDim (versionSpace C [(x, y₀)]))
        (littlestoneDim (versionSpace C [(x, y₁)])) + 1 ≤ littlestoneDim C := by
  have key (n : ℕ) (hn : (n : ℕ∞) ≤ min (littlestoneDim (versionSpace C [(x, y₀)]))
      (littlestoneDim (versionSpace C [(x, y₁)]))) : ((n + 1 : ℕ) : ℕ∞) ≤ littlestoneDim C :=
    le_littlestoneDim_of_hasMistakeTree ⟨x, y₀, y₁, hne,
      hasMistakeTree_of_le_littlestoneDim h0 (le_min_iff.mp hn).1,
      hasMistakeTree_of_le_littlestoneDim h1 (le_min_iff.mp hn).2⟩
  generalize min (littlestoneDim (versionSpace C [(x, y₀)]))
    (littlestoneDim (versionSpace C [(x, y₁)])) = m at key ⊢
  cases m with
  | top => rw [top_add, top_le_iff]; exact ENat.eq_top_iff_forall_ge.mpr fun n =>
      (key n le_top).trans' (by exact_mod_cast Nat.le_succ n)
  | coe m => exact_mod_cast key m le_rfl

/-! ### The lower bound -/

section LowerBound

variable [DecidableEq β]

/-- From a complete `d`-mistake tree, an adversary forces any learner, after any history, to err
on each of `d` rounds of a sequence realizable by `C`
[Littlestone1988, §3, proof of Lemma 1; DanielySabatoBenDavidShalevShwartz2015]. -/
theorem exists_realizable_mistakesFrom_eq (A : OnlineLearner α β) {d : ℕ}
    {C : ConceptClass α β} (hd : HasMistakeTree d C) (h : List (α × β)) :
    ∃ S : List (α × β), S.length = d ∧ Realizable C S ∧ mistakesFrom A h S = d := by
  induction d generalizing C h with
  | zero => exact ⟨[], rfl, realizable_nil.mpr hd, rfl⟩
  | succ d ih =>
    obtain ⟨x, y₀, y₁, hne, h0, h1⟩ := hd
    let y : β := if A h x = y₀ then y₁ else y₀
    have hy_tree : HasMistakeTree d (versionSpace C [(x, y)]) := by
      dsimp only [y]; split <;> assumption
    have hy_ne : A h x ≠ y := by
      dsimp only [y]
      split; exacts [‹_› ▸ hne, ‹_›]
    obtain ⟨S, hlen, hreal, hmis⟩ := ih hy_tree (h ++ [(x, y)])
    exact ⟨(x, y) :: S, by simp [hlen], realizable_cons.mpr hreal, by
      rw [mistakesFrom_cons, ite_eq_right hy_ne, hmis]; omega⟩

/-- A complete `d`-mistake tree for `C` forces every deterministic learner to err on all `d`
rounds of some sequence of length `d` realizable by `C`. -/
theorem exists_realizable_mistakes_eq (A : OnlineLearner α β) {d : ℕ}
    {C : ConceptClass α β} (hd : HasMistakeTree d C) :
    ∃ S : List (α × β), S.length = d ∧ Realizable C S ∧ mistakes A S = d :=
  exists_realizable_mistakesFrom_eq A hd []

/-- **Littlestone's lower bound** [Littlestone1988, §3, Lemma 1;
DanielySabatoBenDavidShalevShwartz2015]: every deterministic learner makes at least
`littlestoneDim C` mistakes in the worst case. -/
theorem littlestoneDim_le_mistakeBound (A : OnlineLearner α β) (C : ConceptClass α β) :
    littlestoneDim C ≤ mistakeBound A C := littlestoneDim_le_iff.mpr fun _ hd =>
  let ⟨_, _, hS, hm⟩ := exists_realizable_mistakes_eq A hd; hm ▸ mistakes_le_mistakeBound hS

theorem littlestoneDim_le_optimalMistakeBound (C : ConceptClass α β) :
    littlestoneDim C ≤ optimalMistakeBound C :=
  le_optimalMistakeBound_iff.mpr fun A => littlestoneDim_le_mistakeBound A C

end LowerBound

end Cslib.MachineLearning.OnlineLearning.MistakeBound
