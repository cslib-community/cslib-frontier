/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.Submodular.Basic
public import CslibFrontier.Foundations.Combinatorics.WeightedCut.MinCutBetween
public import Cslib.Foundations.Control.Monad.IsMonadHom
import CslibFrontier.Foundations.Data.List.EraseDups
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Queyranne's Algorithm for Symmetric Submodular Minimization

Queyranne's algorithm ([Queyranne1998]) finds a non-trivial subset minimizing an arbitrary
symmetric submodular set function `f : Finset V → β` (`f Xᶜ = f X` and
`f (A ∪ B) + f (A ∩ B) ≤ f A + f B`) over a finite ground set `V` with `|V| ≥ 2`. The comparison
and ordering condition are formulated without subtraction so the algorithm and proof apply uniformly
to `ℕ`, `ℤ`, `ℚ`, `ℝ`, and any `[AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]`.

Each phase contracts the ground set into a partition of active supervertices (`blocks`), greedily
builds a Queyranne ordering maximizing `f {x} - f (A ∪ {x})` (equivalently minimizing
`f (insert x A) + f {y}` against `f (insert y A) + f {x}`), records the singleton cut `{t}` of the
last block, and merges the last two blocks `(s, t)`. By Queyranne's pendent-pair lemma
([Queyranne1998]), `f t ≤ f C` for every cut separating `s` and `t`; cuts not separating `s` and
`t` survive merging them, yielding the phase recursion across `|V| - 1` phases.

* `CslibFrontier.Algorithms.Lean.Query.Submodular.Queyranne` lifts `queyranneM` into
  `FreeM (ValueQuery V β)` and proves the `O(|V|³)` value-oracle query bound.
* Applications at the bottom of this file specialize `queyranne` to **real/ordered-monoid-weighted
  Stoer–Wagner global minimum cut** ([StoerWagner1997], covering `ℚ`, `ℝ`, `ℤ`, `ℕ`) and
  **hypergraph global minimum cut**. Note that evaluating a dense graph's `cutWeight` via the
  set-function oracle evaluates full sums on each query (unlike an incremental adjacency array);
  only value-oracle queries are charged in the query-complexity companion module.

## Main definitions

* `Cslib.Algorithms.Lean.Submodular.IsSymmetric`: `f Xᶜ = f X` for all `X`.
* `Cslib.Algorithms.Lean.Submodular.IsQOrdering`: a full Queyranne ordering of `V`.
* `Cslib.Algorithms.Lean.Submodular.QScanResult`,
  `Cslib.Algorithms.Lean.Submodular.QPendentPair`,
  `Cslib.Algorithms.Lean.Submodular.QCutResult`: named output records for scan, phase pendent
  pair, and global cut results.
* `Cslib.Algorithms.Lean.Submodular.queyranneM`,
  `Cslib.Algorithms.Lean.Submodular.queyranne`: monadic and pure Queyranne symmetric submodular
  minimization algorithms.
* `Cslib.Algorithms.Lean.Submodular.hyperCutWeight`: total weight of hyperedges crossing a cut.

## Main results

* `IsSymmetric.posimodular`: every symmetric submodular function is posimodular.
* `pendentPair_le` (**Queyranne's pendent-pair lemma**, [Queyranne1998]): if `(s, t)` are the last
  two elements of a Queyranne ordering of a symmetric submodular `f`, then `f {t} ≤ f C` for every
  cut `C` separating `s` and `t`.
* `queyranne_spec` (**Queyranne's minimization theorem**, [Queyranne1998]): `queyranne f vs` returns
  a non-trivial cut minimizing `f` over all non-trivial subsets of `V`.
* `queyranne_cutWeight_spec`, `queyranne_minCut_eq` (**real/ordered-monoid Stoer–Wagner**,
  [StoerWagner1997]): global minimum cut for symmetric nonnegative edge weights in any
  `[AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]` (`ℚ`, `ℝ`, `ℤ`, `ℕ`).
* `isSymmetric_hyperCutWeight`, `isSubmodular_hyperCutWeight`, `queyranne_hyperCutWeight_spec`:
  global minimum cut of a nonnegative weighted hypergraph.

## References

* [M. Queyranne, *Minimizing symmetric submodular functions*][Queyranne1998]
* [M. Stoer and F. Wagner, *A Simple Min-Cut Algorithm*][StoerWagner1997]
-/

public section

open Cslib (IsMonadHom)
open Cslib.WeightedCut (IsNonTrivialCut cutWeight cutWeight_compl_of_symm
  cutWeight_union_add_cutWeight_inter_le_of_nonneg minCut minCut_le_cutWeight
  exists_minCut_achiever)

namespace Cslib.Algorithms.Lean.Submodular

/-! ## Symmetry, posimodularity, and the pendent-pair lemma -/

section PendentPair

/-- A set function `f : Finset V → β` on a finite type `V` is **symmetric** if `f Xᶜ = f X` for
every subset `X : Finset V`. -/
@[expose] def IsSymmetric {V β : Type*} [DecidableEq V] [Fintype V] (f : Finset V → β) : Prop :=
  ∀ X : Finset V, f Xᶜ = f X

/-- Every symmetric submodular function is posimodular: `f (A \ B) + f (B \ A) ≤ f A + f B`. -/
theorem IsSymmetric.posimodular {V β : Type*} [DecidableEq V] [Fintype V]
    [AddCommMonoid β] [Preorder β] {f : Finset V → β}
    (hf : IsSubmodular f) (hsym : IsSymmetric f) (A B : Finset V) :
    f (A \ B) + f (B \ A) ≤ f A + f B := by
  have h := hf A Bᶜ
  have hu : A ∪ Bᶜ = (B \ A)ᶜ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_compl, Finset.mem_sdiff]
    tauto
  rw [hsym B, hu, hsym (B \ A), ← Finset.sdiff_eq_inter_compl] at h
  rwa [add_comm (f (A \ B))]

/-- `IsQOrderingFrom f A l`: ordering `l` after prefix `A`, each element `x` minimizes
`f (insert y A) - f {y}` among remaining elements `y`, stated without subtraction as
`f (insert x A) + f {y} ≤ f (insert y A) + f {x}`. -/
@[expose] def IsQOrderingFrom {V β : Type*} [DecidableEq V] [Add β] [LE β]
    (f : Finset V → β) : Finset V → List V → Prop
  | _, [] => True
  | A, x :: l => (∀ y ∈ l, f (insert x A) + f {y} ≤ f (insert y A) + f {x}) ∧
      IsQOrderingFrom f (insert x A) l

/-- A full **Queyranne ordering** of the finite type `V` with respect to `f`. -/
structure IsQOrdering {V β : Type*} [DecidableEq V] [Fintype V] [Add β] [LE β]
    (f : Finset V → β) (l : List V) : Prop where
  /-- No element is listed twice. -/
  nodup : l.Nodup
  /-- Every element of `V` is listed. -/
  mem : ∀ v, v ∈ l
  /-- Every prefix minimizes marginal insertion cost minus singleton value. -/
  isQOrderingFrom : IsQOrderingFrom f ∅ l

private theorem pairLe_trans {β : Type*} [AddCommMonoid β] [LinearOrder β]
    [IsOrderedCancelAddMonoid β] {v₁ s₁ v₂ s₂ v₃ s₃ : β}
    (h12 : v₁ + s₂ ≤ v₂ + s₁) (h23 : v₂ + s₃ ≤ v₃ + s₂) :
    v₁ + s₃ ≤ v₃ + s₁ := by
  have hsum : (v₁ + s₃) + (v₂ + s₂) ≤ (v₃ + s₁) + (v₂ + s₂) := by
    calc (v₁ + s₃) + (v₂ + s₂) = (v₁ + s₂) + (v₂ + s₃) := by ac_rfl
      _ ≤ (v₂ + s₁) + (v₃ + s₂) := add_le_add h12 h23
      _ = (v₃ + s₁) + (v₂ + s₂) := by ac_rfl
  exact le_of_add_le_add_right hsum

section Inv

variable {V β : Type*} [DecidableEq V]

private def qSameSide (C A : Finset V) (x : V) : Finset V :=
  A.filter fun a => (a ∈ C ↔ x ∈ C)

private def qOtherSide (C A : Finset V) (x : V) : Finset V :=
  A.filter fun a => ¬ (a ∈ C ↔ x ∈ C)

private def QInv [Add β] [LE β] (f : Finset V → β) (C A : Finset V) (last : V)
    (R : List V) : Prop :=
  ∀ x ∈ R, ¬ (x ∈ C ↔ last ∈ C) →
    f A + f {x} ≤ f (insert x (qSameSide C A x)) + f (qOtherSide C A x)

private theorem qInv_cons [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]
    {f : Finset V → β} (hf : IsSubmodular f) (C : Finset V) {A : Finset V} {last x : V}
    {l : List V} (hx : x ∉ A) (hdisj : ∀ z ∈ l, z ∉ A)
    (hma : ∀ y ∈ l, f (insert x A) + f {y} ≤ f (insert y A) + f {x})
    (hinv : QInv f C A last (x :: l)) :
    QInv f C (insert x A) x l := by
  intro y hy hyx
  have hsame : qSameSide C (insert x A) y = qSameSide C A y := by
    unfold qSameSide
    rw [Finset.filter_insert, ite_eq_right fun h => hyx h.symm]
  have hother : qOtherSide C (insert x A) y = insert x (qOtherSide C A y) := by
    unfold qOtherSide
    rw [Finset.filter_insert, ite_eq_left fun h => hyx h.symm]
  rw [hsame, hother]
  by_cases hxl : x ∈ C ↔ last ∈ C
  · have hyl : ¬ (y ∈ C ↔ last ∈ C) := fun h => hyx (h.trans hxl.symm)
    exact pairLe_trans (hf.insert_add_le x (Finset.filter_subset _ _) hx)
      (hinv y (List.mem_cons_of_mem x hy) hyl)
  · have hsameSwap : qSameSide C A y = qOtherSide C A x := by
      unfold qSameSide qOtherSide
      refine Finset.filter_congr fun a _ => ?_
      tauto
    have hotherSwap : qOtherSide C A y = qSameSide C A x := by
      unfold qOtherSide qSameSide
      refine Finset.filter_congr fun a _ => ?_
      tauto
    rw [hsameSwap, hotherSwap, add_comm (f (insert y _))]
    exact (hma y hy).trans (pairLe_trans
      (hf.insert_add_le y (Finset.filter_subset _ _) (hdisj y hy)) (hinv x List.mem_cons_self hxl))

private theorem qInv_append [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]
    {f : Finset V → β} (hf : IsSubmodular f) (C : Finset V) :
    ∀ (p : List V) {A : Finset V} {last : V} {R : List V},
      (∀ z ∈ p ++ R, z ∉ A) → (p ++ R).Nodup → IsQOrderingFrom f A (p ++ R) →
      QInv f C A last (p ++ R) →
      QInv f C (p.toFinset ∪ A) (p.getLastD last) R
  | [], A, last, R, _, _, _, hinv => by simpa using hinv
  | x :: p, A, last, R, hdisj, hnd, hord, hinv => by
    rw [List.cons_append] at hdisj hnd hord hinv
    have hcons : IsQOrderingFrom f A (x :: (p ++ R)) := hord
    have hstep := qInv_cons hf C (hdisj x List.mem_cons_self)
      (fun z hz => hdisj z (List.mem_cons_of_mem x hz)) hcons.1 hinv
    have hdisj' : ∀ z ∈ p ++ R, z ∉ insert x A := by
      intro z hz hzx
      rcases Finset.mem_insert.mp hzx with rfl | hzA
      · exact (List.nodup_cons.mp hnd).1 hz
      · exact hdisj z (List.mem_cons_of_mem x hz) hzA
    have h := qInv_append hf C p hdisj' (List.nodup_cons.mp hnd).2 hcons.2 hstep
    have hset : p.toFinset ∪ insert x A = (x :: p).toFinset ∪ A := by
      ext a
      simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]
      tauto
    rwa [List.getLastD_cons, ← hset]

private theorem qInv_empty [AddCommMonoid β] [Preorder β] (f : Finset V → β) (C : Finset V)
    (last : V) (R : List V) : QInv f C ∅ last R := by
  intro x _ _
  simp [qSameSide, qOtherSide, add_comm]

end Inv

/-- **Queyranne's pendent-pair lemma** ([Queyranne1998]): if `(s, t)` are the last two elements of
a Queyranne ordering of a symmetric submodular function `f`, then `f {t} ≤ f C` for every cut `C`
separating `s` and `t`. -/
theorem pendentPair_le {V β : Type*} [DecidableEq V] [Fintype V]
    [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]
    {f : Finset V → β} (hf : IsSubmodular f) (hsym : IsSymmetric f)
    {p : List V} {s t : V} (hl : IsQOrdering f (p ++ [s, t])) {C : Finset V}
    (hsep : s ∈ C ↔ t ∉ C) :
    f {t} ≤ f C := by
  have hnd := hl.nodup
  have hinv := qInv_append hf C (p ++ [s]) (A := ∅) (last := t) (R := [t])
    (fun _ _ => Finset.notMem_empty _)
    (by simpa [List.append_assoc] using hnd)
    (by simpa [List.append_assoc] using hl.isQOrderingFrom)
    (qInv_empty f C t _)
  rw [List.getLastD_concat, Finset.union_empty] at hinv
  set A := (p ++ [s]).toFinset with hA
  have htA : t ∉ A := by
    rw [hA, List.mem_toFinset]
    intro ht
    have h := List.nodup_append.mp hnd
    rcases List.mem_append.mp ht with ht | ht
    · exact h.2.2 t ht t (by simp) rfl
    · have hst : s ≠ t := by simpa using h.2.1
      exact hst (List.mem_singleton.mp ht).symm
  have hAt : A = {t}ᶜ := by
    ext a
    by_cases hat : a = t
    · subst hat
      simp [htA]
    · have ha := hl.mem a
      simp only [hA, List.mem_toFinset, Finset.mem_compl, Finset.mem_singleton, hat,
        not_false_eq_true, iff_true]
      simpa [hat] using ha
  have hts : ¬ (t ∈ C ↔ s ∈ C) := by tauto
  have hkey := hinv t List.mem_cons_self hts
  rw [hAt, hsym {t}] at hkey
  have hrhs : f (insert t (qSameSide C {t}ᶜ t)) + f (qOtherSide C {t}ᶜ t) = f C + f C := by
    have hs : insert t (qSameSide C {t}ᶜ t) = if t ∈ C then C else Cᶜ := by
      ext a; by_cases hat : a = t <;> split_ifs with htC <;> simp [qSameSide, hat, htC]
    have ho : qOtherSide C {t}ᶜ t = if t ∈ C then Cᶜ else C := by
      ext a; by_cases hat : a = t <;> split_ifs with htC <;> simp [qOtherSide, hat, htC]
    rw [hs, ho]
    split_ifs <;> rw [hsym C]
  rw [hrhs] at hkey
  by_contra hlt
  have hstrict := lt_of_not_ge hlt
  exact absurd hkey (not_le.mpr (add_lt_add hstrict hstrict))

end PendentPair

/-! ## Monadic and pure Queyranne minimization algorithms -/

section Algorithm

/-- Remove the first pair whose block equals `p`. -/
@[expose] def eraseBlock {V β : Type} [DecidableEq V] (p : Finset V) :
    List (Finset V × β) → List (Finset V × β)
  | [] => []
  | (b, sb) :: cs => if b = p then cs else (b, sb) :: eraseBlock p cs

/-- Precompute `ask b` for every active block `b ∈ bs`. -/
@[expose] def qSingletonsM {m : Type → Type*} [Monad m] {V β : Type}
    (ask : Finset V → m β) : List (Finset V) → m (List (Finset V × β))
  | [] => pure []
  | b :: bs => do
    let v ← ask b
    let rest ← qSingletonsM ask bs
    pure ((b, v) :: rest)

/-- Output of one scan round choosing the next block in a Queyranne ordering. -/
@[ext]
structure QScanResult (V β : Type) where
  /-- Selected candidate block minimizing marginal value `f (A ∪ best) - f best`. -/
  best : Finset V
  /-- Precomputed singleton query value `f best`. -/
  bestVal : β
  /-- Queried union value `f (A ∪ best)`. -/
  unionVal : β

instance {V β : Type} [DecidableEq V] [DecidableEq β] : DecidableEq (QScanResult V β) :=
  fun a b =>
    match decEq a.best b.best, decEq a.bestVal b.bestVal, decEq a.unionVal b.unionVal with
    | .isTrue hb, .isTrue hbv, .isTrue huv => .isTrue (QScanResult.ext hb hbv huv)
    | .isFalse hb, _, _ => .isFalse (fun h => hb (congrArg QScanResult.best h))
    | _, .isFalse hbv, _ => .isFalse (fun h => hbv (congrArg QScanResult.bestVal h))
    | _, _, .isFalse huv => .isFalse (fun h => huv (congrArg QScanResult.unionVal h))

/-- Pendent pair `(fst, snd)` returned by one ordering phase together with `f snd`. -/
@[ext]
structure QPendentPair (V β : Type) where
  /-- Penultimate block of the phase's Queyranne ordering. -/
  fst : Finset V
  /-- Last block of the phase's Queyranne ordering. -/
  snd : Finset V
  /-- Singleton query value `f snd` of the last block. -/
  sndVal : β

instance {V β : Type} [DecidableEq V] [DecidableEq β] : DecidableEq (QPendentPair V β) :=
  fun a b =>
    match decEq a.fst b.fst, decEq a.snd b.snd, decEq a.sndVal b.sndVal with
    | .isTrue hf, .isTrue hs, .isTrue hsv => .isTrue (QPendentPair.ext hf hs hsv)
    | .isFalse hf, _, _ => .isFalse (fun h => hf (congrArg QPendentPair.fst h))
    | _, .isFalse hs, _ => .isFalse (fun h => hs (congrArg QPendentPair.snd h))
    | _, _, .isFalse hsv => .isFalse (fun h => hsv (congrArg QPendentPair.sndVal h))

/-- Cut and objective value returned by Queyranne's algorithm. -/
@[ext]
structure QCutResult (V β : Type) where
  /-- Selected vertex subset. -/
  cut : Finset V
  /-- Value `f cut` achieved on the selected subset. -/
  val : β

instance {V β : Type} [DecidableEq V] [DecidableEq β] : DecidableEq (QCutResult V β) :=
  fun a b =>
    match decEq a.cut b.cut, decEq a.val b.val with
    | .isTrue hc, .isTrue hv => .isTrue (QCutResult.ext hc hv)
    | .isFalse hc, _ => .isFalse (fun h => hc (congrArg QCutResult.cut h))
    | _, .isFalse hv => .isFalse (fun h => hv (congrArg QCutResult.val h))

/-- Scan candidates `cs` left-to-right, minimizing `f (A ∪ b) - f b` (without subtraction) and
breaking ties toward earlier candidates. -/
@[expose] def qScanM {m : Type → Type*} [Monad m] {V β : Type} [DecidableEq V]
    [Add β] [LT β] [DecidableLT β]
    (ask : Finset V → m β) (A : Finset V) (best : Finset V) (sBest vBest : β) :
    List (Finset V × β) → m (QScanResult V β)
  | [] => pure ⟨best, sBest, vBest⟩
  | (b, sb) :: cs => do
    let vb ← ask (A ∪ b)
    if vb + sBest < vBest + sb then
      qScanM ask A b sb vb cs
    else
      qScanM ask A best sBest vBest cs

/-- Extend the Queyranne ordering for `k` remaining selection rounds, returning the last two blocks
`(prev, t)` and the singleton value `f t`. When only one candidate `(t, st)` remains (`cs = []`),
no query is performed. -/
@[expose] def qSearchStepsM {m : Type → Type*} [Monad m] {V β : Type} [DecidableEq V]
    [Add β] [LT β] [DecidableLT β] (ask : Finset V → m β) :
    ℕ → Finset V → Finset V → Finset V × β → List (Finset V × β) → m (QPendentPair V β)
  | 0, _, prev, (t, st), _ => pure ⟨prev, t, st⟩
  | _ + 1, _, prev, (t, st), [] => pure ⟨prev, t, st⟩
  | k + 1, A, prev, c₀, c₁ :: cs => do
    let v₀ ← ask (A ∪ c₀.1)
    let scan ← qScanM ask A c₀.1 c₀.2 v₀ (c₁ :: cs)
    match eraseBlock scan.best (c₀ :: c₁ :: cs) with
    | [] => pure ⟨prev, c₀.1, c₀.2⟩
    | d₀ :: ds => qSearchStepsM ask k (A ∪ scan.best) scan.best d₀ ds

/-- Compute the pendent pair and last singleton value for active blocks `b₀ :: b₁ :: bs`. -/
@[expose] def qSearchM {m : Type → Type*} [Monad m] {V β : Type} [DecidableEq V]
    [Add β] [LT β] [DecidableLT β] (ask : Finset V → m β)
    (b₀ b₁ : Finset V) (bs : List (Finset V)) : m (QPendentPair V β) := do
  let cands ← qSingletonsM ask (b₁ :: bs)
  match cands with
  | [] => do
    let v ← ask b₁
    pure ⟨b₀, b₁, v⟩
  | c₀ :: cs => qSearchStepsM ask bs.length b₀ b₀ c₀ cs

/-- Contract blocks `s` and `t` into `s ∪ t` in the active partition list. -/
@[expose] def mergeBlocks {V : Type*} [DecidableEq V]
    (s t : Finset V) (blocks : List (Finset V)) : List (Finset V) :=
  (s ∪ t) :: ((blocks.erase s).erase t)

/-- Execute `steps + 1` contraction phases of Queyranne's algorithm on `blocks`, returning a
non-trivial cut minimizing `f` together with its value. -/
@[expose] def queyranneRecM {m : Type → Type*} [Monad m] {V β : Type} [DecidableEq V]
    [Add β] [LT β] [DecidableLT β] (ask : Finset V → m β) :
    ℕ → List (Finset V) → m (QCutResult V β)
  | 0, _ :: b₁ :: _ => do
    let v₁ ← ask b₁
    pure ⟨b₁, v₁⟩
  | steps + 1, b₀ :: b₁ :: bs => do
    let pair ← qSearchM ask b₀ b₁ bs
    let recRes ← queyranneRecM ask steps (mergeBlocks pair.fst pair.snd (b₀ :: b₁ :: bs))
    if recRes.val < pair.sndVal then pure recRes else pure ⟨pair.snd, pair.sndVal⟩
  | _, _ => do
    let v ← ask ∅
    pure ⟨∅, v⟩

/-- Monadic Queyranne algorithm ([Queyranne1998]) on ground list `vs`, deduplicating `vs` via
`List.eraseDups` and contracting through `|vs.eraseDups| - 1` phases. -/
@[expose] def queyranneM {m : Type → Type*} [Monad m] {V β : Type} [DecidableEq V]
    [Add β] [LT β] [DecidableLT β] (ask : Finset V → m β) (vs : List V) :
    m (QCutResult V β) :=
  let u := vs.eraseDups
  queyranneRecM ask (u.length - 2) (u.map ({·}))

/-- Pure executable Queyranne algorithm ([Queyranne1998]) minimizing a symmetric submodular
function `f : Finset V → β` over `vs : List V`. -/
@[expose] def queyranne {V β : Type} [DecidableEq V] [Add β] [LT β] [DecidableLT β]
    (f : Finset V → β) (vs : List V) : QCutResult V β :=
  Id.run (queyranneM (m := Id) (fun S => pure (f S)) vs)

end Algorithm

/-! ## Monad homomorphism naturality bridges -/

section Bridges

variable {V β : Type} {m : Type → Type*} {n : Type → Type*} [Monad m] [Monad n]

private theorem map_qSingletonsM
    {φ : {γ : Type} → m γ → n γ} (hφ : IsMonadHom m n φ)
    (ask : Finset V → m β) (bs : List (Finset V)) :
    φ (qSingletonsM ask bs) = qSingletonsM (fun S => φ (ask S)) bs := by
  induction bs with
  | nil => simp [qSingletonsM, hφ.map_pure]
  | cons b bs ih =>
    simp only [qSingletonsM, hφ.map_bind]
    congr 1 with v : 1
    simp only [ih, hφ.map_pure]

private theorem map_qScanM [DecidableEq V] [Add β] [LT β] [DecidableLT β]
    {φ : {γ : Type} → m γ → n γ} (hφ : IsMonadHom m n φ)
    (ask : Finset V → m β) (A best : Finset V) (sBest vBest : β) (cs : List (Finset V × β)) :
    φ (qScanM ask A best sBest vBest cs) =
      qScanM (fun S => φ (ask S)) A best sBest vBest cs := by
  induction cs generalizing best sBest vBest with
  | nil => simp [qScanM, hφ.map_pure]
  | cons c cs ih =>
    rcases c with ⟨b, sb⟩
    simp only [qScanM, hφ.map_bind]
    congr 1 with vb : 1
    split_ifs <;> exact ih _ _ _

variable [DecidableEq V] [Add β] [LT β] [DecidableLT β]

private theorem map_qSearchStepsM
    {φ : {γ : Type} → m γ → n γ} (hφ : IsMonadHom m n φ)
    (ask : Finset V → m β) (k : ℕ) (A prev : Finset V) (c₀ : Finset V × β)
    (cs : List (Finset V × β)) :
    φ (qSearchStepsM ask k A prev c₀ cs) =
      qSearchStepsM (fun S => φ (ask S)) k A prev c₀ cs := by
  induction k generalizing A prev c₀ cs with
  | zero =>
    rcases c₀ with ⟨t, st⟩
    simp [qSearchStepsM, hφ.map_pure]
  | succ k ih =>
    cases cs with
    | nil =>
      rcases c₀ with ⟨t, st⟩
      simp [qSearchStepsM, hφ.map_pure]
    | cons c₁ cs' =>
      simp only [qSearchStepsM, hφ.map_bind]
      congr 1 with v₀ : 1
      simp only [map_qScanM hφ]
      congr 1 with res : 1
      cases eraseBlock res.best (c₀ :: c₁ :: cs') with
      | nil => simp [hφ.map_pure]
      | cons d₀ ds => exact ih _ _ _ _

private theorem map_qSearchM
    {φ : {γ : Type} → m γ → n γ} (hφ : IsMonadHom m n φ)
    (ask : Finset V → m β) (b₀ b₁ : Finset V) (bs : List (Finset V)) :
    φ (qSearchM ask b₀ b₁ bs) = qSearchM (fun S => φ (ask S)) b₀ b₁ bs := by
  simp only [qSearchM, hφ.map_bind, map_qSingletonsM hφ]
  congr 1 with cands : 1
  cases cands with
  | nil =>
    simp only [hφ.map_bind]
    congr 1 with v : 1
    exact hφ.map_pure _
  | cons c₀ cs => exact map_qSearchStepsM hφ _ _ _ _ _ _

private theorem map_queyranneRecM
    {φ : {γ : Type} → m γ → n γ} (hφ : IsMonadHom m n φ)
    (ask : Finset V → m β) (steps : ℕ) (blocks : List (Finset V)) :
    φ (queyranneRecM ask steps blocks) =
      queyranneRecM (fun S => φ (ask S)) steps blocks := by
  induction steps generalizing blocks with
  | zero =>
    rcases blocks with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> simp only [queyranneRecM, hφ.map_bind] <;>
      congr 1 with v : 1 <;> exact hφ.map_pure _
  | succ steps ih =>
    rcases blocks with _ | ⟨_, _ | ⟨_, _⟩⟩ <;>
      simp only [queyranneRecM, hφ.map_bind, map_qSearchM hφ] <;> congr 1 with p : 1
    iterate 2 exact hφ.map_pure _
    simp only [ih]
    congr 1 with q : 1
    split_ifs <;> exact hφ.map_pure _

@[grind .]
theorem _root_.Cslib.IsMonadHom.map_queyranneM
    {φ : {γ : Type} → m γ → n γ} (hφ : IsMonadHom m n φ)
    (ask : Finset V → m β) (vs : List V) :
    φ (queyranneM ask vs) = queyranneM (fun S => φ (ask S)) vs :=
  map_queyranneRecM hφ ask (vs.eraseDups.length - 2) (vs.eraseDups.map ({·}))

end Bridges

/-! ## Correctness of Queyranne's algorithm -/

section Correctness

private theorem nodup_of_pairwise_disjoint_nonempty {V : Type} :
    ∀ {blocks : List (Finset V)},
      (∀ b ∈ blocks, b.Nonempty) → blocks.Pairwise Disjoint → blocks.Nodup
  | [], _, _ => List.nodup_nil
  | b :: bs, hne, hp => by
    obtain ⟨hpair, hrest⟩ := List.pairwise_cons.mp hp
    refine List.nodup_cons.mpr ⟨fun hb => ?_, nodup_of_pairwise_disjoint_nonempty
      (fun c hc => hne c (List.mem_cons_of_mem b hc)) hrest⟩
    exact (Finset.not_disjoint_iff.mpr (by
      obtain ⟨x, hx⟩ := hne b List.mem_cons_self
      exact ⟨x, hx, hx⟩)) (hpair b hb)

private structure BlockPart {V : Type} [DecidableEq V] [Fintype V]
    (blocks : List (Finset V)) : Prop where
  nonempty : ∀ b ∈ blocks, b.Nonempty
  disjoint : blocks.Pairwise Disjoint
  cover : blocks.toFinset.biUnion id = Finset.univ

private theorem blockPart_nodup {V : Type} [DecidableEq V] [Fintype V]
    {blocks : List (Finset V)} (hp : BlockPart blocks) : blocks.Nodup :=
  nodup_of_pairwise_disjoint_nonempty hp.nonempty hp.disjoint

private theorem BlockPart.exists_mem {V : Type} [DecidableEq V] [Fintype V]
    {blocks : List (Finset V)} (hp : BlockPart blocks) (v : V) : ∃ b ∈ blocks, v ∈ b := by
  have hv : v ∈ blocks.toFinset.biUnion id := hp.cover ▸ Finset.mem_univ v
  simpa using hv

private theorem BlockPart.eq_of_mem {V : Type} [DecidableEq V] [Fintype V]
    {blocks : List (Finset V)} (hp : BlockPart blocks) {a b : Finset V} {v : V}
    (ha : a ∈ blocks) (hb : b ∈ blocks) (hva : v ∈ a) (hvb : v ∈ b) : a = b := by
  by_contra hne
  exact Finset.disjoint_left.mp (hp.disjoint.forall ha hb hne) hva hvb

private theorem blockPart_singletons {V : Type} [DecidableEq V] [Fintype V]
    {u : List V} (hnd : u.Nodup) (hmem : ∀ v, v ∈ u) :
    BlockPart (u.map ({·})) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hb
    exact Finset.singleton_nonempty v
  · exact List.pairwise_map.mpr (hnd.imp fun {a b} hab => Finset.disjoint_singleton.mpr hab)
  · apply Finset.eq_univ_of_forall
    intro v
    rw [Finset.mem_biUnion]
    exact ⟨{v}, List.mem_toFinset.mpr (List.mem_map.mpr ⟨v, hmem v, rfl⟩),
      Finset.mem_singleton_self v⟩

private theorem mergeBlocks_nonempty_disjoint {V : Type} [DecidableEq V]
    {blocks : List (Finset V)} (hne : ∀ b ∈ blocks, b.Nonempty) (hdisj : blocks.Pairwise Disjoint)
    {s t : Finset V} (hs : s ∈ blocks) (ht : t ∈ blocks) (hst : s ≠ t) :
    (∀ b ∈ mergeBlocks s t blocks, b.Nonempty) ∧ (mergeBlocks s t blocks).Pairwise Disjoint := by
  have hnd := nodup_of_pairwise_disjoint_nonempty hne hdisj
  have hsub : ∀ b ∈ (blocks.erase s).erase t, b ∈ blocks ∧ b ≠ s ∧ b ≠ t := by
    intro b hb
    have hb1 : b ∈ blocks.erase s := List.mem_of_mem_erase hb
    have hb0 : b ∈ blocks := List.mem_of_mem_erase hb1
    have hbt : b ≠ t := fun h => by
      subst h
      exact (hnd.erase s).not_mem_erase hb
    have hbs : b ≠ s := fun h => by
      subst h
      exact hnd.not_mem_erase hb1
    exact ⟨hb0, hbs, hbt⟩
  refine ⟨?_, List.pairwise_cons.mpr ⟨?_, (hdisj.sublist List.erase_sublist).sublist
    List.erase_sublist⟩⟩
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact (hne s hs).mono Finset.subset_union_left
    · exact hne b (hsub b hb').1
  · intro b hb
    obtain ⟨hb0, hbs, hbt⟩ := hsub b hb
    exact Finset.disjoint_union_left.mpr
      ⟨hdisj.forall hs hb0 hbs.symm, hdisj.forall ht hb0 hbt.symm⟩

private theorem blockPart_mergeBlocks {V : Type} [DecidableEq V] [Fintype V]
    {blocks : List (Finset V)} (hp : BlockPart blocks)
    {s t : Finset V} (hs : s ∈ blocks) (ht : t ∈ blocks) (hst : s ≠ t) :
    BlockPart (mergeBlocks s t blocks) := by
  have hmd := mergeBlocks_nonempty_disjoint hp.nonempty hp.disjoint hs ht hst
  refine ⟨hmd.1, hmd.2, ?_⟩
  apply Finset.eq_univ_of_forall
  intro v
  obtain ⟨b, hb_list, hvb⟩ := hp.exists_mem v
  rw [Finset.mem_biUnion]
  by_cases hbs : b = s
  · rw [hbs] at hvb
    exact ⟨s ∪ t, List.mem_toFinset.mpr (by simp [mergeBlocks]),
      Finset.mem_union_left _ hvb⟩
  · by_cases hbt : b = t
    · rw [hbt] at hvb
      exact ⟨s ∪ t, List.mem_toFinset.mpr (by simp [mergeBlocks]),
        Finset.mem_union_right _ hvb⟩
    · refine ⟨b, List.mem_toFinset.mpr (List.mem_cons_of_mem _ ?_), hvb⟩
      exact (List.mem_erase_of_ne hbt).mpr ((List.mem_erase_of_ne hbs).mpr hb_list)

private theorem length_mergeBlocks {V : Type} [DecidableEq V]
    {blocks : List (Finset V)} {s t : Finset V} (hs : s ∈ blocks) (ht : t ∈ blocks)
    (hst : s ≠ t) :
    (mergeBlocks s t blocks).length + 1 = blocks.length := by
  have ht' : t ∈ blocks.erase s := (List.mem_erase_of_ne hst.symm).mpr ht
  have hpos2 : 0 < (blocks.erase s).length := List.length_pos_of_mem ht'
  have h1 := List.length_erase_of_mem ht'
  have h2 := List.length_erase_of_mem hs
  rw [h2] at hpos2
  simp only [mergeBlocks, List.length_cons, h1, h2]
  omega

private theorem block_isNonTrivialCut {V : Type} [DecidableEq V] [Fintype V]
    {blocks : List (Finset V)} (hp : BlockPart blocks) (hlen : 2 ≤ blocks.length)
    {t : Finset V} (ht : t ∈ blocks) : IsNonTrivialCut t := by
  refine ⟨hp.nonempty t ht, fun htu => ?_⟩
  have hnd := blockPart_nodup hp
  obtain ⟨b, hb, hbt⟩ : ∃ b ∈ blocks, b ≠ t := by
    cases blocks with
    | nil => simp at hlen
    | cons x xs =>
      by_cases hxt : x = t
      · subst hxt
        cases xs with
        | nil => simp at hlen
        | cons y ys =>
          refine ⟨y, List.mem_cons_of_mem x List.mem_cons_self, fun hy => ?_⟩
          subst hy
          exact (List.nodup_cons.mp hnd).1 List.mem_cons_self
      · exact ⟨x, List.mem_cons_self, hxt⟩
  have hdisj := hp.disjoint.forall hb ht hbt
  obtain ⟨x, hx⟩ := hp.nonempty b hb
  exact Finset.disjoint_left.mp hdisj hx (htu ▸ Finset.mem_univ x)

private def RespectsBlocks {V : Type} (blocks : List (Finset V)) (C : Finset V) : Prop :=
  ∀ b ∈ blocks, b ⊆ C ∨ Disjoint b C

private theorem respectsBlocks_singletons {V : Type} (u : List V)
    (C : Finset V) : RespectsBlocks (u.map ({·})) C := by
  intro b hb
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hb
  by_cases hv : v ∈ C
  · exact .inl (Finset.singleton_subset_iff.mpr hv)
  · exact .inr (Finset.disjoint_singleton_left.mpr hv)

private theorem respectsBlocks_mergeBlocks {V : Type} [DecidableEq V] [Fintype V]
    {blocks : List (Finset V)} (hp : BlockPart blocks) {s t : Finset V}
    (hs : s ∈ blocks) (ht : t ∈ blocks) {C : Finset V}
    (hC : RespectsBlocks blocks C) (hsame : ¬ (s ⊆ C ↔ ¬ t ⊆ C)) :
    RespectsBlocks (mergeBlocks s t blocks) C := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb'
  · rcases hC s hs with hsC | hsdisj
    · have htC : t ⊆ C := by tauto
      exact .inl (Finset.union_subset hsC htC)
    · have hsnot : ¬ s ⊆ C := fun hsC => by
        obtain ⟨x, hx⟩ := hp.nonempty s hs
        exact Finset.disjoint_left.mp hsdisj hx (hsC hx)
      have htnot : ¬ t ⊆ C := by tauto
      rcases hC t ht with htC | htdisj
      · exact (htnot htC).elim
      · exact .inr (Finset.disjoint_union_left.mpr ⟨hsdisj, htdisj⟩)
  · exact hC b (List.mem_of_mem_erase (List.mem_of_mem_erase hb'))

private def blockUnion {V : Type} [DecidableEq V] (blocks : List (Finset V))
    (S : Finset {b : Finset V // b ∈ blocks.toFinset}) : Finset V :=
  S.biUnion Subtype.val

private theorem blockUnion_union {V : Type} [DecidableEq V] (blocks : List (Finset V))
    (S T : Finset {b : Finset V // b ∈ blocks.toFinset}) :
    blockUnion blocks (S ∪ T) = blockUnion blocks S ∪ blockUnion blocks T := by
  ext v
  simp [blockUnion, or_and_right, exists_or]

private theorem blockUnion_inter {V : Type} [DecidableEq V] [Fintype V]
    {blocks : List (Finset V)} (hp : BlockPart blocks)
    (S T : Finset {b : Finset V // b ∈ blocks.toFinset}) :
    blockUnion blocks (S ∩ T) = blockUnion blocks S ∩ blockUnion blocks T := by
  ext v
  simp only [blockUnion, Finset.mem_biUnion, Finset.mem_inter]
  constructor
  · rintro ⟨a, ⟨haS, haT⟩, hva⟩
    exact ⟨⟨a, haS, hva⟩, ⟨a, haT, hva⟩⟩
  · rintro ⟨⟨a, haS, hva⟩, ⟨b, hbT, hvb⟩⟩
    obtain rfl := Subtype.ext (hp.eq_of_mem (List.mem_toFinset.mp a.2)
      (List.mem_toFinset.mp b.2) hva hvb)
    exact ⟨a, ⟨haS, hbT⟩, hva⟩

private theorem blockUnion_compl {V : Type} [DecidableEq V] [Fintype V]
    {blocks : List (Finset V)} (hp : BlockPart blocks)
    (S : Finset {b : Finset V // b ∈ blocks.toFinset}) :
    blockUnion blocks Sᶜ = (blockUnion blocks S)ᶜ := by
  ext v
  simp only [blockUnion, Finset.mem_compl, Finset.mem_biUnion, not_exists, not_and]
  obtain ⟨b, hb, hvb⟩ := hp.exists_mem v
  refine ⟨fun ⟨a, haS, hva⟩ c hcS hvc => haS ?_,
    fun h => ⟨⟨b, List.mem_toFinset.mpr hb⟩, fun hbS => h _ hbS hvb, hvb⟩⟩
  rwa [Subtype.ext (hp.eq_of_mem (List.mem_toFinset.mp a.2) (List.mem_toFinset.mp c.2) hva hvc)]

@[simp] private theorem blockUnion_singleton {V : Type} [DecidableEq V] (blocks : List (Finset V))
    (b : {b : Finset V // b ∈ blocks.toFinset}) :
    blockUnion blocks {b} = b.1 := by
  simp [blockUnion]

@[simp] private theorem blockUnion_empty {V : Type} [DecidableEq V] (blocks : List (Finset V)) :
    blockUnion blocks ∅ = ∅ := by
  simp [blockUnion]

@[simp] private theorem blockUnion_insert {V : Type} [DecidableEq V] (blocks : List (Finset V))
    (b : {b : Finset V // b ∈ blocks.toFinset})
    (S : Finset {b : Finset V // b ∈ blocks.toFinset}) :
    blockUnion blocks (insert b S) = blockUnion blocks S ∪ b.1 := by
  rw [Finset.insert_eq, blockUnion_union, blockUnion_singleton, Finset.union_comm]

private theorem isSubmodular_blockUnion {V β : Type} [DecidableEq V] [Fintype V]
    [AddCommMonoid β] [Preorder β] {f : Finset V → β} (hf : IsSubmodular f)
    {blocks : List (Finset V)} (hp : BlockPart blocks) :
    IsSubmodular (fun S => f (blockUnion blocks S)) := by
  intro A B
  dsimp only
  rw [blockUnion_union, blockUnion_inter hp]
  exact hf _ _

private theorem isSymmetric_blockUnion {V β : Type} [DecidableEq V] [Fintype V]
    {f : Finset V → β} (hsym : IsSymmetric f) {blocks : List (Finset V)} (hp : BlockPart blocks) :
    IsSymmetric (fun S => f (blockUnion blocks S)) := by
  intro X
  dsimp only
  rw [blockUnion_compl hp]
  exact hsym _

private theorem blockUnion_filter_subset {V : Type} [DecidableEq V] [Fintype V]
    {blocks : List (Finset V)} (hp : BlockPart blocks) {C : Finset V}
    (hC : RespectsBlocks blocks C) :
    blockUnion blocks (Finset.univ.filter fun b => b.1 ⊆ C) = C := by
  ext v
  simp only [blockUnion, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    Subtype.exists]
  constructor
  · rintro ⟨b, _, hbC, hvb⟩
    exact hbC hvb
  · intro hvC
    obtain ⟨b, hb, hvb⟩ := hp.exists_mem v
    refine ⟨b, List.mem_toFinset.mpr hb, ?_, hvb⟩
    rcases hC b hb with hbC | hbdisj
    · exact hbC
    · exact False.elim (Finset.disjoint_left.mp hbdisj hvb hvC)

/-! ### Pure `Id.run` specifications for scan, search, and recursion -/

private theorem idRun_qSingletons {V β : Type} (f : Finset V → β) (bs : List (Finset V)) :
    Id.run (qSingletonsM (m := Id) (fun S => pure (f S)) bs) = bs.map fun b => (b, f b) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    change (b, f b) :: Id.run (qSingletonsM (m := Id) (fun S => pure (f S)) bs) = _
    rw [ih]
    rfl

private theorem mem_eraseBlock_iff {V β : Type} [DecidableEq V] {p : Finset V} :
    ∀ {cs : List (Finset V × β)}, (cs.map Prod.fst).Nodup →
      ∀ {c : Finset V × β}, c ∈ eraseBlock p cs ↔ c ∈ cs ∧ c.1 ≠ p
  | [], _, _ => by simp [eraseBlock]
  | (b, sb) :: cs, hnd, (x, sx) => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [eraseBlock]
    by_cases hbp : b = p
    · subst hbp
      simp only [↓reduceIte, List.mem_cons, Prod.mk.injEq, ne_eq]
      constructor
      · intro hx
        refine ⟨.inr hx, fun hxp => ?_⟩
        subst hxp
        exact hnd.1 (List.mem_map.mpr ⟨(x, sx), hx, rfl⟩)
      · rintro ⟨⟨rfl, rfl⟩ | hx, hne⟩
        · exact absurd rfl hne
        · exact hx
    · simp only [hbp, ↓reduceIte, List.mem_cons, Prod.mk.injEq, ne_eq]
      rw [mem_eraseBlock_iff hnd.2]
      refine ⟨?_, ?_⟩
      · rintro (⟨rfl, rfl⟩ | ⟨hx, hne⟩)
        · exact ⟨.inl ⟨rfl, rfl⟩, hbp⟩
        · exact ⟨.inr hx, hne⟩
      · rintro ⟨⟨rfl, rfl⟩ | hx, hne⟩
        · exact .inl ⟨rfl, rfl⟩
        · exact .inr ⟨hx, hne⟩

private theorem length_eraseBlock {V β : Type} [DecidableEq V] {p : Finset V} :
    ∀ {cs : List (Finset V × β)}, (∃ sb, (p, sb) ∈ cs) →
      (eraseBlock p cs).length + 1 = cs.length
  | [], ⟨_, h⟩ => by simp at h
  | (b, sb) :: cs, ⟨sb', h⟩ => by
    rw [eraseBlock]
    by_cases hbp : b = p
    · simp [hbp]
    · simp only [hbp, ↓reduceIte, List.length_cons]
      have h' : ∃ sb, (p, sb) ∈ cs := by
        rcases List.mem_cons.mp h with heq | hc
        · exact absurd (Prod.mk.inj heq).1.symm hbp
        · exact ⟨sb', hc⟩
      have ih := length_eraseBlock h'
      omega

private theorem nodup_fst_eraseBlock {V β : Type} [DecidableEq V] (p : Finset V)
    {cs : List (Finset V × β)} (hnd : (cs.map Prod.fst).Nodup) :
    ((eraseBlock p cs).map Prod.fst).Nodup := by
  induction cs with
  | nil => simp [eraseBlock]
  | cons c cs ih =>
    rcases c with ⟨b, sb⟩
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [eraseBlock]
    by_cases hbp : b = p
    · simpa [hbp] using hnd.2
    · simp only [hbp, ↓reduceIte, List.map_cons]
      refine List.nodup_cons.mpr ⟨fun hmem => ?_, ih hnd.2⟩
      obtain ⟨⟨x, sx⟩, hx, rfl⟩ := List.mem_map.mp hmem
      exact hnd.1 (List.mem_map.mpr ⟨(x, sx), ((mem_eraseBlock_iff hnd.2).mp hx).1, rfl⟩)

private theorem qScan_spec {V β : Type} [DecidableEq V]
    [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β] (f : Finset V → β)
    (A : Finset V) :
    ∀ (cs : List (Finset V × β)) (best : Finset V) (sBest vBest : β),
      (∀ c ∈ cs, c.2 = f c.1) → sBest = f best → vBest = f (A ∪ best) →
      let res := Id.run (qScanM (m := Id) (fun S => pure (f S)) A best sBest vBest cs)
      (res.best, res.bestVal) ∈ (best, sBest) :: cs ∧ res.bestVal = f res.best ∧
        res.unionVal = f (A ∪ res.best) ∧
        ∀ c ∈ (best, sBest) :: cs, res.unionVal + c.2 ≤ f (A ∪ c.1) + res.bestVal
  | [], best, sBest, vBest, _, hsb, hvb => by
    have hres :
        Id.run (qScanM (m := Id) (fun S => pure (f S)) A best sBest vBest []) =
          ⟨best, sBest, vBest⟩ := rfl
    dsimp only
    rw [hres]
    refine ⟨List.mem_cons_self, hsb, hvb, fun c hc => ?_⟩
    rcases List.mem_singleton.mp hc with rfl
    rw [hvb]
  | (b, sb) :: cs, best, sBest, vBest, hcs, hsb, hvb => by
    have hsb_b : sb = f b := hcs (b, sb) List.mem_cons_self
    have hcs' : ∀ c ∈ cs, c.2 = f c.1 := fun c hc => hcs c (List.mem_cons_of_mem _ hc)
    have hrun :
        Id.run (qScanM (m := Id) (fun S => pure (f S)) A best sBest vBest ((b, sb) :: cs)) =
        if f (A ∪ b) + sBest < vBest + sb then
          Id.run (qScanM (m := Id) (fun S => pure (f S)) A b sb (f (A ∪ b)) cs)
        else
          Id.run (qScanM (m := Id) (fun S => pure (f S)) A best sBest vBest cs) := rfl
    dsimp only
    rw [hrun]
    split_ifs with hlt
    · have ih := qScan_spec f A cs b sb (f (A ∪ b)) hcs' hsb_b rfl
      refine ⟨List.mem_cons_of_mem _ ih.1, ih.2.1, ih.2.2.1, fun c hc => ?_⟩
      rcases List.mem_cons.mp hc with rfl | hc'
      · rw [hvb] at hlt
        exact pairLe_trans (ih.2.2.2 (b, sb) List.mem_cons_self) (le_of_lt hlt)
      · exact ih.2.2.2 c hc'
    · have hge : vBest + sb ≤ f (A ∪ b) + sBest := le_of_not_gt hlt
      have ih := qScan_spec f A cs best sBest vBest hcs' hsb hvb
      refine ⟨?_, ih.2.1, ih.2.2.1, fun c hc => ?_⟩
      · rcases List.mem_cons.mp ih.1 with heq | hmem
        · rw [heq]
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmem)
      · rcases List.mem_cons.mp hc with rfl | hc'
        · exact ih.2.2.2 (best, sBest) List.mem_cons_self
        · rcases List.mem_cons.mp hc' with rfl | hc''
          · exact pairLe_trans (ih.2.2.2 (best, sBest) List.mem_cons_self) (by rwa [← hvb])
          · exact ih.2.2.2 c (List.mem_cons_of_mem _ hc'')

private theorem qSearchSteps_spec {V β : Type} [DecidableEq V] [Fintype V]
    [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]
    (f : Finset V → β) {blocks : List (Finset V)} (hp : BlockPart blocks) :
    ∀ (k : ℕ) (S_pref : Finset {b : Finset V // b ∈ blocks.toFinset})
      (prev : {b : Finset V // b ∈ blocks.toFinset})
      (c₀ : Finset V × β) (cs : List (Finset V × β)),
      cs.length = k →
      prev ∈ S_pref →
      ((c₀ :: cs).map Prod.fst).Nodup →
      (∀ p ∈ c₀ :: cs, p.1 ∈ blocks.toFinset ∧ p.2 = f p.1) →
      (∀ b : {b : Finset V // b ∈ blocks.toFinset},
        b ∉ S_pref ↔ b.1 ∈ (c₀ :: cs).map Prod.fst) →
      let res := Id.run (qSearchStepsM (m := Id) (fun S => pure (f S)) k
        (blockUnion blocks S_pref) prev.1 c₀ cs)
      res.fst ∈ blocks ∧ res.snd ∈ blocks ∧ res.fst ≠ res.snd ∧ res.sndVal = f res.snd ∧
        ∃ q : List {b : Finset V // b ∈ blocks.toFinset},
          q.Nodup ∧ (∀ b, b ∉ S_pref ↔ b ∈ q) ∧
          IsQOrderingFrom (fun X => f (blockUnion blocks X)) S_pref q ∧
          ((k = 0 ∧ ∃ tP : {b : Finset V // b ∈ blocks.toFinset},
              q = [tP] ∧ res.fst = prev.1 ∧ tP.1 = res.snd) ∨
           (1 ≤ k ∧ ∃ q₀ sP tP, q = q₀ ++ [sP, tP] ∧ sP.1 = res.fst ∧ tP.1 = res.snd))
  | 0, S_pref, prev, (t, st), [], _, hprevS, _, hmem, hcover => by
    have ht_mem : t ∈ blocks.toFinset := (hmem (t, st) List.mem_cons_self).1
    have ht_eq : st = f t := (hmem (t, st) List.mem_cons_self).2
    let tP : {b : Finset V // b ∈ blocks.toFinset} := ⟨t, ht_mem⟩
    have hne : prev.1 ≠ t := by
      intro heq
      have hpeq : prev = tP := Subtype.ext heq
      have hnt : tP ∉ S_pref := (hcover tP).mpr (by simp [tP])
      exact hnt (hpeq ▸ hprevS)
    refine ⟨List.mem_toFinset.mp prev.2, List.mem_toFinset.mp ht_mem, hne, ht_eq, [tP],
      List.nodup_singleton tP, fun b => ?_, ?_, .inl ⟨rfl, tP, rfl, rfl, rfl⟩⟩
    · rw [hcover b]
      simp [tP, Subtype.ext_iff]
    · simp [IsQOrderingFrom]
  | 0, _, _, _, _ :: _, hlen, _, _, _, _ => by simp at hlen
  | k + 1, S_pref, prev, c₀, [], hlen, _, _, _, _ => by simp at hlen
  | k + 1, S_pref, prev, c₀, c₁ :: cs, hlen, _, hnd, hmem, hcover => by
    have hscan := qScan_spec f (blockUnion blocks S_pref) (c₁ :: cs) c₀.1 c₀.2
      (f (blockUnion blocks S_pref ∪ c₀.1))
      (fun c hc => (hmem c (List.mem_cons_of_mem _ hc)).2)
      (hmem c₀ List.mem_cons_self).2 rfl
    set scanRes := Id.run (qScanM (m := Id) (fun S => pure (f S))
      (blockUnion blocks S_pref) c₀.1 c₀.2 (f (blockUnion blocks S_pref ∪ c₀.1)) (c₁ :: cs))
    set best := scanRes.best
    set sBest := scanRes.bestVal
    have hbest_in : (best, sBest) ∈ c₀ :: c₁ :: cs := hscan.1
    have hbest_mem : best ∈ blocks.toFinset := (hmem (best, sBest) hbest_in).1
    let bP : {b : Finset V // b ∈ blocks.toFinset} := ⟨best, hbest_mem⟩
    have hlen_er := length_eraseBlock (p := best) ⟨sBest, hbest_in⟩
    cases her : eraseBlock best (c₀ :: c₁ :: cs) with
    | nil =>
      rw [her, List.length_nil] at hlen_er
      simp at hlen_er
    | cons d₀ ds =>
      have hds_len : ds.length = k := by
        simp only [her, List.length_cons] at hlen hlen_er
        omega
      have hnd' : ((d₀ :: ds).map Prod.fst).Nodup := her ▸ nodup_fst_eraseBlock best hnd
      have hsub_er : ∀ p ∈ d₀ :: ds, p ∈ c₀ :: c₁ :: cs ∧ p.1 ≠ best := by
        intro p hp'
        rw [← her] at hp'
        exact (mem_eraseBlock_iff hnd).mp hp'
      have hmem' : ∀ p ∈ d₀ :: ds, p.1 ∈ blocks.toFinset ∧ p.2 = f p.1 :=
        fun p hp' => hmem p (hsub_er p hp').1
      have hcover' : ∀ b : {b : Finset V // b ∈ blocks.toFinset},
          b ∉ insert bP S_pref ↔ b.1 ∈ (d₀ :: ds).map Prod.fst := by
        intro b
        rw [Finset.mem_insert, not_or, hcover b, List.mem_map, List.mem_map]
        constructor
        · rintro ⟨hne, p, hp_mem, hpb⟩
          refine ⟨p, ?_, hpb⟩
          rw [← her]
          exact (mem_eraseBlock_iff hnd).mpr ⟨hp_mem, fun he => hne (Subtype.ext (hpb ▸ he))⟩
        · rintro ⟨p, hp_mem, hpb⟩
          obtain ⟨hp_orig, hne⟩ := hsub_er p hp_mem
          exact ⟨fun he => hne (hpb ▸ congrArg Subtype.val he), p, hp_orig, hpb⟩
      have ih := qSearchSteps_spec f hp k (insert bP S_pref) bP d₀ ds hds_len
        (Finset.mem_insert_self _ _) hnd' hmem' hcover'
      have hunion : blockUnion blocks (insert bP S_pref) = blockUnion blocks S_pref ∪ best :=
        blockUnion_insert blocks bP S_pref
      have hstep :
          Id.run (qSearchStepsM (m := Id) (fun S => pure (f S)) (k + 1)
            (blockUnion blocks S_pref) prev.1 c₀ (c₁ :: cs)) =
          Id.run (qSearchStepsM (m := Id) (fun S => pure (f S)) k
            (blockUnion blocks (insert bP S_pref)) bP.1 d₀ ds) := by
        change (match eraseBlock scanRes.best (c₀ :: c₁ :: cs) with
          | [] => QPendentPair.mk prev.1 c₀.1 c₀.2
          | d₀' :: ds' => Id.run (qSearchStepsM (m := Id) (fun S => pure (f S)) k
              (blockUnion blocks S_pref ∪ scanRes.best) scanRes.best d₀' ds')) = _
        rw [her]
        simp only [hunion, bP, best]
      dsimp only
      rw [hstep]
      obtain ⟨h1, h2, h3, h4, q', hq'nd, hq'cov, hq'ord, hq'tail⟩ := ih
      refine ⟨h1, h2, h3, h4, bP :: q', List.nodup_cons.mpr ⟨?_, hq'nd⟩, ?_, ?_, ?_⟩
      · rw [← hq'cov bP]
        simp
      · intro b
        rw [List.mem_cons, ← hq'cov b, Finset.mem_insert]
        by_cases hb : b = bP
        · subst hb
          refine ⟨fun _ => .inl rfl, fun _ => ?_⟩
          have hb_in : bP.1 ∈ (c₀ :: c₁ :: cs).map Prod.fst :=
            List.mem_map.mpr ⟨(best, sBest), hbest_in, rfl⟩
          exact (hcover bP).mpr hb_in
        · simp [hb]
      · refine ⟨fun y hy => ?_, hq'ord⟩
        have hy' : y ∉ insert bP S_pref := (hq'cov y).mpr hy
        rw [Finset.mem_insert, not_or] at hy'
        have hy_map : y.1 ∈ (c₀ :: c₁ :: cs).map Prod.fst := (hcover y).mp hy'.2
        obtain ⟨c, hc_mem, hc_eq⟩ := List.mem_map.mp hy_map
        have hc_all := hscan.2.2.2 c hc_mem
        have hc2 : c.2 = f y.1 := hc_eq ▸ (hmem c hc_mem).2
        have hbP_eq : bP.1 = best := rfl
        rw [hscan.2.1, hscan.2.2.1, hc2, hc_eq] at hc_all
        simpa only [blockUnion_insert, blockUnion_singleton, hbP_eq] using hc_all
      · refine .inr ?_
        rcases hq'tail with ⟨_, tP, rfl, hs_eq, ht_eq⟩ | ⟨_, q₀', sP', tP', rfl, hs_eq, ht_eq⟩
        · exact ⟨by omega, [], bP, tP, rfl, hs_eq.symm, ht_eq⟩
        · exact ⟨by omega, bP :: q₀', sP', tP', rfl, hs_eq, ht_eq⟩

private theorem qSearch_spec {V β : Type} [DecidableEq V] [Fintype V]
    [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]
    (f : Finset V → β) {blocks : List (Finset V)} (hp : BlockPart blocks)
    (b₀ b₁ : Finset V) (bs : List (Finset V)) (hblocks : blocks = b₀ :: b₁ :: bs) :
    let res := Id.run (qSearchM (m := Id) (fun S => pure (f S)) b₀ b₁ bs)
    res.fst ∈ blocks ∧ res.snd ∈ blocks ∧ res.fst ≠ res.snd ∧ res.sndVal = f res.snd ∧
      ∃ (p : List {b : Finset V // b ∈ blocks.toFinset})
        (sP tP : {b : Finset V // b ∈ blocks.toFinset}),
        sP.1 = res.fst ∧ tP.1 = res.snd ∧
        IsQOrdering (fun X => f (blockUnion blocks X)) (p ++ [sP, tP]) := by
  have hnd_list := blockPart_nodup hp
  rw [hblocks, List.nodup_cons] at hnd_list
  have hb₀_mem : b₀ ∈ blocks.toFinset := List.mem_toFinset.mpr (by simp [hblocks])
  let b₀P : {b : Finset V // b ∈ blocks.toFinset} := ⟨b₀, hb₀_mem⟩
  have hc_nd : (((b₁ :: bs).map fun b => (b, f b)).map Prod.fst).Nodup := by
    simpa [List.map_map, Function.comp_def] using hnd_list.2
  have hc_mem : ∀ p ∈ (b₁ :: bs).map fun b => (b, f b),
      p.1 ∈ blocks.toFinset ∧ p.2 = f p.1 := by
    intro p hp'
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hp'
    exact ⟨List.mem_toFinset.mpr (by simp [hblocks, hb]), rfl⟩
  have hcover : ∀ b : {b : Finset V // b ∈ blocks.toFinset},
      b ∉ ({b₀P} : Finset _) ↔ b.1 ∈ (((b₁ :: bs).map fun x => (x, f x)).map Prod.fst) := by
    intro b
    simp only [Finset.mem_singleton, List.map_map, Function.comp_def, List.map_id',
      Subtype.ext_iff, b₀P]
    have hb : b.1 ∈ b₀ :: b₁ :: bs := hblocks ▸ List.mem_toFinset.mp b.2
    exact ⟨(List.mem_cons.mp hb).resolve_left, fun hb' heq => hnd_list.1 (heq ▸ hb')⟩
  have hsteps := qSearchSteps_spec f hp bs.length {b₀P} b₀P (b₁, f b₁)
    (bs.map fun b => (b, f b)) (by simp) (Finset.mem_singleton_self _)
    (by simpa using hc_nd) (by simpa using hc_mem) (by simpa using hcover)
  have hsearch_eq : Id.run (qSearchM (m := Id) (fun S => pure (f S)) b₀ b₁ bs) =
      Id.run (qSearchStepsM (m := Id) (fun S => pure (f S)) bs.length
        (blockUnion blocks {b₀P}) b₀P.1 (b₁, f b₁) (bs.map fun b => (b, f b))) := by
    change (match Id.run (qSingletonsM (m := Id) (fun S => pure (f S)) (b₁ :: bs)) with
      | [] => QPendentPair.mk b₀ b₁ (f b₁)
      | c₀ :: cs => Id.run (qSearchStepsM (m := Id) (fun S => pure (f S)) bs.length b₀ b₀ c₀ cs)) =
      _
    rw [idRun_qSingletons]
    simp only [List.map_cons, blockUnion_singleton, b₀P]
  dsimp only
  rw [hsearch_eq]
  obtain ⟨h1, h2, h3, h4, q, hq_nd, hq_cov, hq_ord, hq_tail⟩ := hsteps
  refine ⟨h1, h2, h3, h4, ?_⟩
  have hfull_nd : (b₀P :: q).Nodup := List.nodup_cons.mpr ⟨by simp [← hq_cov], hq_nd⟩
  have hfull_mem : ∀ v, v ∈ b₀P :: q := fun v => by
    by_cases hv : v = b₀P
    · subst hv; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ ((hq_cov v).mp (by simpa using hv))
  have hfull_ord : IsQOrderingFrom (fun X => f (blockUnion blocks X)) ∅ (b₀P :: q) := by
    have hins : (insert b₀P ∅ : Finset {b : Finset V // b ∈ blocks.toFinset}) = {b₀P} := rfl
    refine ⟨fun y _ => ?_, ?_⟩
    · dsimp only
      rw [hins, blockUnion_singleton]
      exact le_of_eq (add_comm _ _)
    · rwa [hins]
  rcases hq_tail with ⟨_, tP, rfl, hs_eq, ht_eq⟩ | ⟨_, q₀, sP, tP, rfl, hs_eq, ht_eq⟩
  · refine ⟨[], b₀P, tP, hs_eq.symm, ht_eq, ⟨hfull_nd, hfull_mem, hfull_ord⟩⟩
  · refine ⟨b₀P :: q₀, sP, tP, hs_eq, ht_eq, ⟨hfull_nd, hfull_mem, hfull_ord⟩⟩

private theorem queyranneRec_spec {V β : Type} [DecidableEq V] [Fintype V]
    [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]
    {f : Finset V → β} (hf : IsSubmodular f) (hsym : IsSymmetric f) :
    ∀ (steps : ℕ) (blocks : List (Finset V)),
      BlockPart blocks → blocks.length = steps + 2 →
      let res := Id.run (queyranneRecM (m := Id) (fun S => pure (f S)) steps blocks)
      IsNonTrivialCut res.cut ∧ res.val = f res.cut ∧
        ∀ C : Finset V, IsNonTrivialCut C → RespectsBlocks blocks C → f res.cut ≤ f C
  | 0, blocks, hp, hlen => by
    rcases blocks with _ | ⟨b₀, _ | ⟨b₁, bs⟩⟩
    · simp at hlen
    · simp at hlen
    · have hnil : bs = [] := by
        simp only [List.length_cons] at hlen
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst hnil
      have hres : Id.run (queyranneRecM (m := Id) (fun S => pure (f S)) 0 [b₀, b₁]) =
          ⟨b₁, f b₁⟩ := rfl
      dsimp only
      rw [hres]
      refine ⟨block_isNonTrivialCut hp (by simp) (by simp), rfl, fun C hCnt hC => ?_⟩
      have hcov : ∀ v, v ∈ b₀ ∨ v ∈ b₁ := fun v => by simpa using hp.exists_mem v
      rcases hC b₀ (by simp) with hb₀C | hb₀D <;> rcases hC b₁ (by simp) with hb₁C | hb₁D
      · exact absurd (Finset.eq_univ_of_forall fun v => (hcov v).elim (@hb₀C v) (@hb₁C v)) hCnt.2
      · have hCb₁ : C = b₁ᶜ := by
          ext v
          rw [Finset.mem_compl]
          exact ⟨fun hvC hvb₁ => Finset.disjoint_left.mp hb₁D hvb₁ hvC,
            fun hnb₁ => hb₀C ((hcov v).resolve_right hnb₁)⟩
        rw [hCb₁, hsym b₁]
      · rw [Finset.Subset.antisymm (fun v hvC => (hcov v).resolve_left
          fun hvb => Finset.disjoint_left.mp hb₀D hvb hvC) hb₁C]
      · exact absurd (Finset.eq_empty_iff_forall_notMem.mpr fun v hvC => (hcov v).elim
          (Finset.disjoint_left.mp hb₀D · hvC) (Finset.disjoint_left.mp hb₁D · hvC))
          hCnt.1.ne_empty
  | steps + 1, blocks, hp, hlen => by
    rcases blocks with _ | ⟨b₀, _ | ⟨b₁, bs⟩⟩
    · simp at hlen
    · simp at hlen
    · have hsearch := qSearch_spec f hp b₀ b₁ bs rfl
      set sr := Id.run (qSearchM (m := Id) (fun S => pure (f S)) b₀ b₁ bs)
      obtain ⟨hs_mem, ht_mem, hst_ne, hst_val, p, sP, tP, hsP, htP, hord⟩ := hsearch
      have hp' := blockPart_mergeBlocks hp hs_mem ht_mem hst_ne
      have hlen' : (mergeBlocks sr.fst sr.snd (b₀ :: b₁ :: bs)).length = steps + 2 := by
        have := length_mergeBlocks hs_mem ht_mem hst_ne
        omega
      have ih := queyranneRec_spec hf hsym steps
        (mergeBlocks sr.fst sr.snd (b₀ :: b₁ :: bs)) hp' hlen'
      set recRes := Id.run (queyranneRecM (m := Id) (fun S => pure (f S)) steps
        (mergeBlocks sr.fst sr.snd (b₀ :: b₁ :: bs)))
      have ht_nontriv : IsNonTrivialCut sr.snd := block_isNonTrivialCut hp (by omega) ht_mem
      have hsep_bound : ∀ C : Finset V, RespectsBlocks (b₀ :: b₁ :: bs) C →
          (sr.fst ⊆ C ↔ ¬ sr.snd ⊆ C) → f sr.snd ≤ f C := by
        intro C hC hsep
        let X : Finset {b : Finset V // b ∈ (b₀ :: b₁ :: bs).toFinset} :=
          Finset.univ.filter fun b => b.1 ⊆ C
        have hX_sep : sP ∈ X ↔ tP ∉ X := by
          simp only [X, Finset.mem_filter, Finset.mem_univ, true_and, hsP, htP, hsep]
        have hp_le := pendentPair_le (isSubmodular_blockUnion hf hp)
          (isSymmetric_blockUnion hsym hp) hord hX_sep
        have hX_eq : blockUnion (b₀ :: b₁ :: bs) X = C := blockUnion_filter_subset hp hC
        have ht_eq : blockUnion (b₀ :: b₁ :: bs) {tP} = sr.snd := by
          simp [blockUnion_singleton, htP]
        simpa [hX_eq, ht_eq] using hp_le
      change (let res := if recRes.val < sr.sndVal then recRes else ⟨sr.snd, sr.sndVal⟩
        IsNonTrivialCut res.cut ∧ res.val = f res.cut ∧
          ∀ C : Finset V, IsNonTrivialCut C → RespectsBlocks (b₀ :: b₁ :: bs) C → f res.cut ≤ f C)
      split_ifs with hlt
      · refine ⟨ih.1, ih.2.1, fun C hCnt hC => ?_⟩
        by_cases hsep : sr.fst ⊆ C ↔ ¬ sr.snd ⊆ C
        · have hle_t : f recRes.cut ≤ f sr.snd := by
            rw [← ih.2.1, ← hst_val]
            exact le_of_lt hlt
          exact hle_t.trans (hsep_bound C hC hsep)
        · exact ih.2.2 C hCnt (respectsBlocks_mergeBlocks hp hs_mem ht_mem hC hsep)
      · have hle_rec : f sr.snd ≤ f recRes.cut := by
          rw [← ih.2.1, ← hst_val]
          exact le_of_not_gt hlt
        refine ⟨ht_nontriv, hst_val, fun C hCnt hC => ?_⟩
        by_cases hsep : sr.fst ⊆ C ↔ ¬ sr.snd ⊆ C
        · exact hsep_bound C hC hsep
        · exact hle_rec.trans (ih.2.2 C hCnt (respectsBlocks_mergeBlocks hp hs_mem ht_mem hC hsep))

end Correctness

/-! ## Main minimization theorem and combinatorial cut applications -/

section Main

/-- **Queyranne's theorem** ([Queyranne1998]): on any finite ground type `V` with `2 ≤ |V|`, for
any list `vs` containing every vertex and any symmetric submodular function `f : Finset V → β` with
values in `[AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]`, `queyranne f vs`
returns a non-trivial subset `S` achieving the global minimum of `f` over all non-trivial subsets
of `V`. -/
theorem queyranne_spec {V β : Type} [DecidableEq V] [Fintype V]
    [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]
    {f : Finset V → β} (hf : IsSubmodular f) (hsym : IsSymmetric f)
    (hV : 2 ≤ Fintype.card V) {vs : List V} (hcov : ∀ v, v ∈ vs) :
    let res := queyranne f vs
    IsNonTrivialCut res.cut ∧ res.val = f res.cut ∧
      ∀ C : Finset V, IsNonTrivialCut C → f res.cut ≤ f C := by
  have hu_nd : vs.eraseDups.Nodup := List.nodup_eraseDups vs
  have hu_cov : ∀ v, v ∈ vs.eraseDups := fun v => (List.mem_eraseDups).mpr (hcov v)
  have hp := blockPart_singletons hu_nd hu_cov
  have hcard : vs.eraseDups.length = Fintype.card V := by
    rw [List.length_eraseDups]
    have hset : vs.toFinset = Finset.univ := Finset.eq_univ_of_forall fun v =>
      List.mem_toFinset.mpr (hcov v)
    rw [hset, Finset.card_univ]
  have hlen : (vs.eraseDups.map ({·} : V → Finset V)).length =
      (vs.eraseDups.length - 2) + 2 := by
    rw [List.length_map]
    omega
  have hrec := queyranneRec_spec hf hsym (vs.eraseDups.length - 2) _ hp hlen
  refine ⟨hrec.1, hrec.2.1, fun C hCnt => ?_⟩
  exact hrec.2.2 C hCnt (respectsBlocks_singletons vs.eraseDups C)

/-- **Real / ordered-monoid Stoer–Wagner global minimum cut** ([StoerWagner1997], via
[Queyranne1998]): for symmetric nonnegative edge weights `W : V → V → β` in any ordered
commutative cancellative monoid (`ℚ`, `ℝ`, `ℤ`, `ℕ`), `queyranne (cutWeight W) vs` computes a
non-trivial cut of minimum `cutWeight`. -/
theorem queyranne_cutWeight_spec {V β : Type} [DecidableEq V] [Fintype V]
    [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]
    {W : V → V → β} (hWsym : ∀ u v, W u v = W v u) (hWnonneg : ∀ u v, 0 ≤ W u v)
    (hV : 2 ≤ Fintype.card V) {vs : List V} (hcov : ∀ v, v ∈ vs) :
    let res := queyranne (cutWeight W) vs
    IsNonTrivialCut res.cut ∧ res.val = cutWeight W res.cut ∧
      ∀ C : Finset V, IsNonTrivialCut C → cutWeight W res.cut ≤ cutWeight W C :=
  queyranne_spec (cutWeight_union_add_cutWeight_inter_le_of_nonneg W hWnonneg)
    (fun X => cutWeight_compl_of_symm hWsym X) hV hcov

/-- On natural-number weighted multigraphs (`IsMultigraph W`), the value returned by `queyranne`
equals `Cslib.WeightedCut.minCut W`. -/
theorem queyranne_minCut_eq {V : Type} [DecidableEq V] [Fintype V]
    {W : V → V → ℕ} (hW : Cslib.WeightedCut.IsMultigraph W)
    (hV : 2 ≤ Fintype.card V) {vs : List V} (hcov : ∀ v, v ∈ vs) :
    (queyranne (cutWeight W) vs).val = minCut W := by
  obtain ⟨hnt, hval, hle⟩ := queyranne_cutWeight_spec hW.1 (fun _ _ => Nat.zero_le _) hV hcov
  obtain ⟨C, hCnt, hC⟩ := exists_minCut_achiever hV W
  apply le_antisymm
  · rw [hval, ← hC]
    exact hle C hCnt
  · rw [hval]
    exact minCut_le_cutWeight W hnt

/-- Cut weight of a weighted hypergraph `(H, w)` across vertex subset `X`: total weight of all
hyperedges `e ∈ H` having at least one vertex in `X` and at least one vertex outside `X`. -/
@[expose] def hyperCutWeight {V β : Type*} [DecidableEq V] [Fintype V] [AddCommMonoid β]
    (H : Finset (Finset V)) (w : Finset V → β) (X : Finset V) : β :=
  ∑ e ∈ H, if (e ∩ X).Nonempty ∧ (e ∩ Xᶜ).Nonempty then w e else 0

/-- The hypergraph cut function is symmetric. -/
theorem isSymmetric_hyperCutWeight {V β : Type*} [DecidableEq V] [Fintype V] [AddCommMonoid β]
    (H : Finset (Finset V)) (w : Finset V → β) :
    IsSymmetric (hyperCutWeight H w) := by
  intro X
  unfold hyperCutWeight
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h1 : (e ∩ X).Nonempty <;> by_cases h2 : (e ∩ Xᶜ).Nonempty <;> simp [h1, h2]

/-- Nonnegative hypergraph cut functions are submodular. -/
theorem isSubmodular_hyperCutWeight {V β : Type*} [DecidableEq V] [Fintype V]
    [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
    (H : Finset (Finset V)) {w : Finset V → β} (hw : ∀ e ∈ H, 0 ≤ w e) :
    IsSubmodular (hyperCutWeight H w) := by
  intro A B
  unfold hyperCutWeight
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun e he => ?_
  have hwe := hw e he
  have h_union :
      ((e ∩ (A ∪ B)).Nonempty ∧ (e ∩ (A ∪ B)ᶜ).Nonempty) →
      ((e ∩ A).Nonempty ∧ (e ∩ Aᶜ).Nonempty) ∨ ((e ∩ B).Nonempty ∧ (e ∩ Bᶜ).Nonempty) := by
    simp only [Finset.Nonempty, Finset.mem_inter, Finset.mem_compl, Finset.mem_union]
    grind
  have h_inter :
      ((e ∩ (A ∩ B)).Nonempty ∧ (e ∩ (A ∩ B)ᶜ).Nonempty) →
      ((e ∩ A).Nonempty ∧ (e ∩ Aᶜ).Nonempty) ∨ ((e ∩ B).Nonempty ∧ (e ∩ Bᶜ).Nonempty) := by
    simp only [Finset.Nonempty, Finset.mem_inter, Finset.mem_compl]
    grind
  have h_both :
      ((e ∩ (A ∪ B)).Nonempty ∧ (e ∩ (A ∪ B)ᶜ).Nonempty) →
      ((e ∩ (A ∩ B)).Nonempty ∧ (e ∩ (A ∩ B)ᶜ).Nonempty) →
      ((e ∩ A).Nonempty ∧ (e ∩ Aᶜ).Nonempty) ∧ ((e ∩ B).Nonempty ∧ (e ∩ Bᶜ).Nonempty) := by
    simp only [Finset.Nonempty, Finset.mem_inter, Finset.mem_compl, Finset.mem_union]
    grind
  split_ifs <;>
    (try simp only [add_zero, zero_add]) <;>
    first
    | exact le_refl _
    | exact hwe
    | exact le_add_of_nonneg_right hwe
    | exact add_nonneg hwe hwe
    | (exfalso
       rename_i hU hI hA hB
       first
       | exact hB (h_both hU hI).2
       | exact hA (h_both hU hI).1
       | exact (h_union hU).elim hA hB
       | exact (h_inter hI).elim hA hB)

/-- **Hypergraph global minimum cut** ([Queyranne1998]): `queyranne (hyperCutWeight H w) vs` finds
a non-trivial cut of minimum total weight of crossing hyperedges. -/
theorem queyranne_hyperCutWeight_spec {V β : Type} [DecidableEq V] [Fintype V]
    [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]
    (H : Finset (Finset V)) {w : Finset V → β} (hw : ∀ e ∈ H, 0 ≤ w e)
    (hV : 2 ≤ Fintype.card V) {vs : List V} (hcov : ∀ v, v ∈ vs) :
    let res := queyranne (hyperCutWeight H w) vs
    IsNonTrivialCut res.cut ∧ res.val = hyperCutWeight H w res.cut ∧
      ∀ C : Finset V, IsNonTrivialCut C → hyperCutWeight H w res.cut ≤ hyperCutWeight H w C :=
  queyranne_spec (isSubmodular_hyperCutWeight H hw) (isSymmetric_hyperCutWeight H w) hV hcov

end Main

end Cslib.Algorithms.Lean.Submodular

