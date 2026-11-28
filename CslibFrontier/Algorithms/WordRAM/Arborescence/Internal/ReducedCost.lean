/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Arborescence.Table
import Mathlib.Tactic.Linarith

/-!
# Edmonds §4 reduced exit costs and row-potential equivalence (internal)

Pure table-level lemmas proving row-potential equivalence (`RowPotEq`) between unreduced
`edmondsTableAux` costs and the reduced exit-cost contraction (`contractReducedCostTable`), plus
weight magnitude bounds (`[-M₀, (k + 1) * M₀]`).
-/

namespace Cslib.Algorithms.WordRAM.Arborescence.Internal

open Cslib.Algorithms.Lean.Arborescence

/-! ### Edmonds §4 reduced exit costs and row-potential equivalence -/

/-- A step of `List.argAux` returns either the new candidate or the accumulator. -/
private theorem argAux_eq_some {α : Type*} {r : α → α → Prop} [DecidableRel r]
    {acc : Option α} {i a : α} (h : List.argAux r acc i = some a) : i = a ∨ acc = some a := by
  cases acc with
  | none => simp only [List.argAux, Option.some.injEq] at h; exact Or.inl h
  | some z =>
    simp only [List.argAux] at h
    split_ifs at h <;> simp only [Option.some.injEq] at h
    · exact Or.inl h
    · exact Or.inr (congrArg some h)

public theorem argMinFin_of_lt_iff {β γ : Type*} [LinearOrder β] [LinearOrder γ] {n : ℕ}
    (pred : Fin n → Bool) (f : Fin n → β) (g : Fin n → γ)
    (h : ∀ x y, pred x = true → pred y = true → (f x < f y ↔ g x < g y)) :
    argMinFin n pred f = argMinFin n pred g := by
  unfold argMinFin
  suffices ∀ (l : List (Fin n)) (acc : Option (Fin n)),
      (∀ y, acc = some y → pred y = true) →
      l.foldl (fun a i => if pred i then List.argAux (fun x y => f x < f y) a i else a) acc =
        l.foldl (fun a i => if pred i then List.argAux (fun x y => g x < g y) a i else a) acc from
    this (List.finRange n) none (fun _ h => by cases h)
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons i ls ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    cases hp : pred i
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact ih acc hacc
    · simp only [↓reduceIte]
      have harg_eq : List.argAux (fun x y => f x < f y) acc i =
          List.argAux (fun x y => g x < g y) acc i := by
        cases acc with
        | none => rfl
        | some z => simp [List.argAux, h i z hp (hacc z rfl)]
      rw [harg_eq]
      exact ih _ fun y hy => (argAux_eq_some hy).elim (· ▸ hp) (hacc y)

private theorem argMinFin_spec {β : Type*} [LinearOrder β] {n : ℕ} (pred : Fin n → Bool)
    (val : Fin n → β) {x : Fin n} (hx : argMinFin n pred val = some x) :
    pred x = true ∧ ∀ y : Fin n, pred y = true → val x ≤ val y := by
  have hgen : ∀ (l : List (Fin n)) (acc : Option (Fin n)),
      (∀ a, acc = some a → pred a = true) →
      ∀ x, l.foldl (fun a i => if pred i then List.argAux (fun u v => val u < val v) a i else a)
        acc = some x →
      pred x = true ∧ (∀ a, acc = some a → val x ≤ val a) ∧
        ∀ y ∈ l, pred y = true → val x ≤ val y := by
    intro l
    induction l with
    | nil =>
      intro acc hacc x hx'
      simp only [List.foldl_nil] at hx'
      exact ⟨hacc x hx', fun a ha => by rw [hx'] at ha; cases ha; exact le_rfl,
        fun _ hy => by cases hy⟩
    | cons i ls ih =>
      intro acc hacc x hx'
      simp only [List.foldl_cons] at hx'
      cases hp : pred i
      · simp only [hp, Bool.false_eq_true, ↓reduceIte] at hx'
        obtain ⟨hpx, hacc_le, hls_le⟩ := ih acc hacc x hx'
        refine ⟨hpx, hacc_le, fun y hy hpy => ?_⟩
        rcases List.mem_cons.mp hy with rfl | hmem
        · simp [hp] at hpy
        · exact hls_le y hmem hpy
      · simp only [hp, ↓reduceIte] at hx'
        have hacc' : ∀ a, List.argAux (fun u v => val u < val v) acc i = some a → pred a = true :=
          fun a ha => (argAux_eq_some ha).elim (· ▸ hp) (hacc a)
        obtain ⟨hpx, hacc'_le, hls_le⟩ := ih _ hacc' x hx'
        refine ⟨hpx, ?_, ?_⟩
        · intro a ha
          subst ha
          by_cases hlt : val i < val a
          · exact (hacc'_le i (by simp [List.argAux, hlt])).trans (le_of_lt hlt)
          · exact hacc'_le a (by simp [List.argAux, hlt])
        · intro y hy hpy
          rcases List.mem_cons.mp hy with rfl | hmem
          · cases acc with
            | none => exact hacc'_le y rfl
            | some a =>
              by_cases hlt : val y < val a
              · exact hacc'_le y (by simp [List.argAux, hlt])
              · exact (hacc'_le a (by simp [List.argAux, hlt])).trans (le_of_not_gt hlt)
          · exact hls_le y hmem hpy
  obtain ⟨hpx, _, hall⟩ := hgen (List.finRange n) none (fun _ h => by cases h) x hx
  exact ⟨hpx, fun y hpy => hall y (List.mem_finRange y) hpy⟩

private theorem foldl_and_eq_true {α : Type*} (p : α → Bool) (l : List α) (b : Bool) :
    l.foldl (fun acc x => acc && p x) b = true ↔ b = true ∧ ∀ x ∈ l, p x = true := by
  induction l generalizing b with
  | nil => simp
  | cons x ls ih =>
    simp only [List.foldl_cons, ih, Bool.and_eq_true, List.mem_cons]
    constructor
    · rintro ⟨⟨hb, hpx⟩, hls⟩
      exact ⟨hb, fun y hy => by rcases hy with rfl | hmem; exacts [hpx, hls y hmem]⟩
    · rintro ⟨hb, hall⟩
      exact ⟨⟨hb, hall x (Or.inl rfl)⟩, fun y hy => hall y (Or.inr hy)⟩

public theorem selectParents_feasible_spec {n : ℕ} (a : AdjTable n) (c : CostTable ℤ n)
    (r : Fin n) (hfeas : (selectParents a c r).feasible = true) :
    let f := (selectParents a c r).parents
    f[r.val] = r ∧
      ∀ v : Fin n, v ≠ r →
        a[v.val][(f[v.val]).val] = true ∧ f[v.val] ≠ v ∧
          ∀ w : Fin n, a[v.val][w.val] = true → w ≠ v →
            c[v.val][(f[v.val]).val] ≤ c[v.val][w.val] := by
  unfold selectParents at hfeas ⊢
  dsimp only at hfeas ⊢
  rw [foldl_and_eq_true] at hfeas
  refine ⟨by simp, fun v hvr => ?_⟩
  have hsome := hfeas.2 v (List.mem_finRange v)
  simp only [Vector.getElem_ofFn, Fin.eta, hvr, ↓reduceIte] at hsome ⊢
  obtain ⟨fv, harg⟩ := Option.isSome_iff_exists.mp hsome
  have hfv : (argMinFin n (fun w => a[v.val][w.val] && w != v)
      (fun w => c[v.val][w.val])).getD v = fv := by
    rw [harg]; rfl
  obtain ⟨hpred, hmin⟩ := argMinFin_spec _ _ harg
  simp only [Bool.and_eq_true, bne_iff_ne] at hpred
  simp only [hfv]
  exact ⟨hpred.1, hpred.2, fun w haw hne => hmin w (by simp [haw, hne])⟩

private theorem findCycleTable_spec {n : ℕ} (r : Fin n) (f : ParentTable n) {x0 : Fin n}
    (hx0 : findCycleTable r f = some x0) : x0 ≠ r ∧ hasCycleFrom x0 f = true := by
  have hgen : ∀ (l : List (Fin n)) (acc : Option (Fin n)),
      (∀ y, acc = some y → y ≠ r ∧ hasCycleFrom y f = true) →
      ∀ x0, l.foldl (fun acc x => match acc with
        | some a => some a
        | none => if x == r then none else if hasCycleFrom x f then some x else none)
        acc = some x0 →
      x0 ≠ r ∧ hasCycleFrom x0 f = true := by
    intro l
    induction l with
    | nil => intro acc hacc x0 hx; exact hacc x0 hx
    | cons x ls ih =>
      intro acc hacc x0 hx
      simp only [List.foldl_cons] at hx
      cases acc with
      | some a => exact ih (some a) hacc x0 hx
      | none =>
        refine ih _ (fun y hy => ?_) x0 hx
        by_cases hxr : x == r
        · simp [hxr] at hy
        · simp only [hxr, Bool.false_eq_true, ↓reduceIte] at hy
          by_cases hcy : hasCycleFrom x f = true
          · simp only [hcy, ↓reduceIte, Option.some.injEq] at hy
            subst hy
            exact ⟨by simpa [beq_iff_eq] using hxr, hcy⟩
          · simp [hcy] at hy
  exact hgen (List.finRange n) none (fun _ h => by cases h) x0 hx0

public theorem not_inCycle_root {n : ℕ} (r : Fin n) (f : ParentTable n) {x0 : Fin n}
    (hfr : f[r.val] = r) (hx0 : findCycleTable r f = some x0) :
    (cycleMask f x0)[x0.val] = true ∧ ∀ x : Fin n, (cycleMask f x0)[x.val] = true → x ≠ r := by
  refine ⟨(getElem_cycleMask f x0 x0).mpr ⟨0, r.pos, rfl⟩, ?_⟩
  obtain ⟨hx0_ne, hcy⟩ := findCycleTable_spec r f hx0
  rw [hasCycleFrom_eq] at hcy
  simp only [List.any_eq_true, List.mem_range, beq_iff_eq] at hcy
  obtain ⟨t, _, ht⟩ := hcy
  let g : Fin n → Fin n := fun i => f[i.val]
  have hfix : ∀ m, g^[m] r = r := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', ih]; exact hfr
  have hper : ∀ q, g^[q * (t + 1)] x0 = x0 := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.succ_mul, Nat.add_comm, Function.iterate_add_apply, ih]
      exact ht
  intro x hx hxr
  subst hxr
  obtain ⟨j, _, hj⟩ := (getElem_cycleMask f x0 x).mp hx
  have hjle : j ≤ (j + 1) * (t + 1) := by nlinarith
  have hxeq : x0 = x := by
    calc x0 = g^[(j + 1) * (t + 1)] x0 := (hper (j + 1)).symm
      _ = g^[((j + 1) * (t + 1) - j) + j] x0 := by rw [Nat.sub_add_cancel hjle]
      _ = g^[(j + 1) * (t + 1) - j] (g^[j] x0) := Function.iterate_add_apply _ _ _ _
      _ = g^[(j + 1) * (t + 1) - j] x := by rw [hj]
      _ = x := hfix _
  exact hx0_ne hxeq

/-- Row-potential equivalence between an unreduced cost table `cUnred` and a reduced cost table
`cRed` on active arcs of `a`. -/
@[expose] public def RowPotEq {n : ℕ} (a : AdjTable n) (cUnred cRed : CostTable ℤ n) : Prop :=
  ∃ φ : Fin n → ℤ, ∀ u w : Fin n, a[u.val][w.val] = true →
    cUnred[u.val][w.val] = cRed[u.val][w.val] + φ u

private def cycleSum {n : ℕ} (c : CostTable ℤ n) (f : ParentTable n)
    (inCycle : Vector Bool n) : ℤ :=
  (List.finRange n).foldl
    (fun acc y => if inCycle[y.val] then acc + c[y.val][f[y.val].val] else acc) 0

/-- For each target column `w`, selects a cycle vertex `x` minimizing reduced exit cost
`c[x][w] - c[x][f[x]]` among active arcs `a[x][w]`. -/
@[expose] public def reducedBestExitTable {n : ℕ} (a : AdjTable n) (c : CostTable ℤ n)
    (f : ParentTable n) (inCycle : Vector Bool n) : Vector (Option (Fin n)) n :=
  Vector.ofFn fun w : Fin n =>
    argMinFin n (fun x => inCycle[x.val] && a[x.val][w.val])
      (fun x => c[x.val][w.val] - c[x.val][f[x.val].val])

/-- Contracted cost matrix storing reduced exit costs `c[x][w] - c[x][f[x]]` out of `x0` and zeroing
inactive cells. -/
@[expose] public def contractReducedCostTable {n : ℕ} (a : AdjTable n) (c : CostTable ℤ n)
    (f : ParentTable n) (inCycle : Vector Bool n)
    (bEntry bExit : Vector (Option (Fin n)) n) (x0 : Fin n) : CostTable ℤ n :=
  Vector.ofFn fun u : Fin n => Vector.ofFn fun w : Fin n =>
    if inCycle[u.val] then
      if u == x0 then
        if !(inCycle[w.val]) then
          match bExit[w.val] with
          | some x => c[x.val][w.val] - c[x.val][f[x.val].val]
          | none => 0
        else 0
      else 0
    else
      if inCycle[w.val] then
        if w == x0 then
          match bEntry[u.val] with
          | some y => c[u.val][y.val]
          | none => 0
        else 0
      else if a[u.val][w.val] then c[u.val][w.val]
      else 0

public theorem getElem_contractReducedCostTable {n : ℕ} (a : AdjTable n) (c : CostTable ℤ n)
    (f : ParentTable n) (inCycle : Vector Bool n)
    (bEntry bExit : Vector (Option (Fin n)) n) (x0 u w : Fin n) :
    (contractReducedCostTable a c f inCycle bEntry bExit x0)[u.val][w.val] =
      if inCycle[u.val] then
        if u == x0 then
          if !(inCycle[w.val]) then
            match bExit[w.val] with
            | some x => c[x.val][w.val] - c[x.val][f[x.val].val]
            | none => 0
          else 0
        else 0
      else
        if inCycle[w.val] then
          if w == x0 then
            match bEntry[u.val] with
            | some y => c[u.val][y.val]
            | none => 0
          else 0
        else if a[u.val][w.val] then c[u.val][w.val]
        else 0 := by
  simp [contractReducedCostTable]

private theorem otherCycleCost_add_self {n : ℕ} (c : CostTable ℤ n) (f : ParentTable n)
    (inCycle : Vector Bool n) {x : Fin n} (hx : inCycle[x.val] = true) :
    c[x.val][f[x.val].val] + (otherCycleCost c f inCycle)[x.val] = cycleSum c f inCycle := by
  have hshift : ∀ (l : List (Fin n)) (p : Fin n → Bool) (val : Fin n → ℤ) (a b : ℤ),
      l.foldl (fun acc y => if p y then acc + val y else acc) (a + b) =
        a + l.foldl (fun acc y => if p y then acc + val y else acc) b := by
    intro l p val
    induction l with
    | nil => intro _ _; rfl
    | cons y ls ih =>
      intro a b
      simp only [List.foldl_cons]
      split_ifs
      · rw [add_assoc, ih]
      · exact ih a b
  have hnotmem : ∀ (l : List (Fin n)) (init : ℤ), x ∉ l →
      l.foldl (fun acc y =>
          if inCycle[y.val] && y != x then acc + c[y.val][f[y.val].val] else acc) init =
        l.foldl (fun acc y =>
          if inCycle[y.val] then acc + c[y.val][f[y.val].val] else acc) init := by
    intro l
    induction l with
    | nil => intro _ _; rfl
    | cons y ls ih =>
      intro init hmem
      simp only [List.mem_cons, not_or] at hmem
      have hne : (y != x) = true := bne_iff_ne.mpr (Ne.symm hmem.1)
      simp only [List.foldl_cons, hne, Bool.and_true]
      exact ih _ hmem.2
  have hmem : ∀ (l : List (Fin n)) (init : ℤ), l.Nodup → x ∈ l →
      c[x.val][f[x.val].val] +
        l.foldl (fun acc y =>
            if inCycle[y.val] && y != x then acc + c[y.val][f[y.val].val] else acc) init =
        l.foldl (fun acc y =>
            if inCycle[y.val] then acc + c[y.val][f[y.val].val] else acc) init := by
    intro l
    induction l with
    | nil => intro _ _ hm; cases hm
    | cons y ls ih =>
      intro init hnd hm
      rw [List.nodup_cons] at hnd
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hm with rfl | hls
      · simp only [bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte, hx]
        rw [hnotmem ls init hnd.1, ← hshift ls _ _ c[x.val][f[x.val].val] init, add_comm]
      · have hne : (y != x) = true := bne_iff_ne.mpr (fun heq => hnd.1 (heq ▸ hls))
        simp only [hne, Bool.and_true]
        exact ih _ hnd.2 hls
  unfold otherCycleCost cycleSum
  simp only [Vector.getElem_ofFn, hx, ↓reduceIte]
  exact hmem (List.finRange n) 0 (List.nodup_finRange n) (List.mem_finRange x)

public theorem selectParents_of_rowPotEq {n : ℕ} {a : AdjTable n} {cUnred cRed : CostTable ℤ n}
    (r : Fin n) (hpot : RowPotEq a cUnred cRed) :
    selectParents a cRed r = selectParents a cUnred r := by
  obtain ⟨φ, hφ⟩ := hpot
  unfold selectParents
  have hopts :
      (Vector.ofFn fun v : Fin n =>
        if v = r then some r
        else argMinFin n (fun w => a[v.val][w.val] && w != v) (fun w => cRed[v.val][w.val])) =
      (Vector.ofFn fun v : Fin n =>
        if v = r then some r
        else argMinFin n (fun w => a[v.val][w.val] && w != v) (fun w => cUnred[v.val][w.val])) := by
    apply Vector.ext
    intro v hv
    simp only [Vector.getElem_ofFn]
    split_ifs
    · rfl
    · exact argMinFin_of_lt_iff _ _ _ fun x y hx hy => by
        simp only [Bool.and_eq_true] at hx hy
        have h1 := hφ ⟨v, hv⟩ x hx.1
        have h2 := hφ ⟨v, hv⟩ y hy.1
        dsimp only at h1 h2
        omega
  simp only [hopts]

public theorem bestEntryTable_of_rowPotEq {n : ℕ} {a : AdjTable n} {cUnred cRed : CostTable ℤ n}
    (inCycle : Vector Bool n) (hpot : RowPotEq a cUnred cRed) :
    bestEntryTable a cRed inCycle = bestEntryTable a cUnred inCycle := by
  obtain ⟨φ, hφ⟩ := hpot
  unfold bestEntryTable
  apply Vector.ext
  intro u hu
  simp only [Vector.getElem_ofFn]
  exact argMinFin_of_lt_iff _ _ _ fun x y hx hy => by
    simp only [Bool.and_eq_true] at hx hy
    have h1 := hφ ⟨u, hu⟩ x hx.2
    have h2 := hφ ⟨u, hu⟩ y hy.2
    dsimp only at h1 h2
    omega

private theorem exitCost_eq_reduced_add_cycleSum {n : ℕ} {a : AdjTable n}
    {cUnred cRed : CostTable ℤ n} {f : ParentTable n} {inCycle : Vector Bool n}
    (hpot : RowPotEq a cUnred cRed)
    (hact : ∀ x : Fin n, inCycle[x.val] = true → a[x.val][f[x.val].val] = true)
    {x w : Fin n} (hx : inCycle[x.val] = true) (haw : a[x.val][w.val] = true) :
    cUnred[x.val][w.val] + (otherCycleCost cUnred f inCycle)[x.val] =
      (cRed[x.val][w.val] - cRed[x.val][f[x.val].val]) + cycleSum cUnred f inCycle := by
  obtain ⟨φ, hφ⟩ := hpot
  have hsum := otherCycleCost_add_self cUnred f inCycle hx
  have h1 := hφ x w haw
  have h2 := hφ x f[x.val] (hact x hx)
  omega

public theorem reducedBestExitTable_eq_bestExitTable {n : ℕ} {a : AdjTable n}
    {cUnred cRed : CostTable ℤ n} {f : ParentTable n} {inCycle : Vector Bool n}
    (hpot : RowPotEq a cUnred cRed)
    (hact : ∀ x : Fin n, inCycle[x.val] = true → a[x.val][f[x.val].val] = true) :
    reducedBestExitTable a cRed f inCycle =
      bestExitTable a cUnred inCycle (otherCycleCost cUnred f inCycle) := by
  unfold reducedBestExitTable bestExitTable
  apply Vector.ext
  intro w hw
  simp only [Vector.getElem_ofFn]
  exact argMinFin_of_lt_iff _ _ _ fun x y hx hy => by
    simp only [Bool.and_eq_true] at hx hy
    have h1 := exitCost_eq_reduced_add_cycleSum hpot hact (w := ⟨w, hw⟩) hx.1 hx.2
    have h2 := exitCost_eq_reduced_add_cycleSum hpot hact (w := ⟨w, hw⟩) hy.1 hy.2
    dsimp only at h1 h2
    omega

public theorem rowPotEq_contractReduced {n : ℕ} {a : AdjTable n}
    {cUnred cRed : CostTable ℤ n} {f : ParentTable n} {inCycle : Vector Bool n}
    {x0 r : Fin n} (hpot : RowPotEq a cUnred cRed) (hx0_in : inCycle[x0.val] = true)
    (hact : ∀ x : Fin n, inCycle[x.val] = true → a[x.val][f[x.val].val] = true) :
    let other := otherCycleCost cUnred f inCycle
    let bEntry := bestEntryTable a cRed inCycle
    let bExit := reducedBestExitTable a cRed f inCycle
    RowPotEq (contractAdjTable a inCycle bEntry bExit x0 r)
      (contractCostTable cUnred inCycle other bEntry bExit x0)
      (contractReducedCostTable a cRed f inCycle bEntry bExit x0) := by
  obtain ⟨φ, hφ⟩ := hpot
  refine ⟨fun u =>
      if inCycle[u.val] then (if u = x0 then cycleSum cUnred f inCycle else 0) else φ u,
    fun u w ha' => ?_⟩
  rw [getElem_contractAdjTable] at ha'
  rw [getElem_contractCostTable, getElem_contractReducedCostTable]
  by_cases hu : inCycle[u.val] = true
  · simp only [hu, ↓reduceIte] at ha' ⊢
    by_cases hux : u = x0
    · subst hux
      simp only [beq_self_eq_true, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true'] at ha' ⊢
      obtain ⟨hw_out, hbx_some⟩ := ha'
      simp only [hw_out, ↓reduceIte]
      cases hbx : (reducedBestExitTable a cRed f inCycle)[w.val] with
      | none => simp [hbx] at hbx_some
      | some x =>
        have hbx' : argMinFin n (fun z => inCycle[z.val] && a[z.val][w.val])
            (fun z => cRed[z.val][w.val] - cRed[z.val][f[z.val].val]) = some x := by
          simpa [reducedBestExitTable] using hbx
        obtain ⟨hpred, _⟩ := argMinFin_spec _ _ hbx'
        simp only [Bool.and_eq_true] at hpred
        exact exitCost_eq_reduced_add_cycleSum ⟨φ, hφ⟩ hact hpred.1 hpred.2
    · have hux_b : (u == x0) = false := beq_false_of_ne hux
      simp [hux, hux_b]
  · simp only [hu, Bool.false_eq_true, ↓reduceIte] at ha' ⊢
    by_cases hw : inCycle[w.val] = true
    · simp only [hw, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at ha' ⊢
      obtain ⟨rfl, hbe_some⟩ := ha'
      simp only [↓reduceIte]
      cases hbe : (bestEntryTable a cRed inCycle)[u.val] with
      | none => simp [hbe] at hbe_some
      | some y =>
        have hbe' : argMinFin n (fun z => inCycle[z.val] && a[u.val][z.val])
            (fun z => cRed[u.val][z.val]) = some y := by
          simpa [bestEntryTable] using hbe
        obtain ⟨hpred, _⟩ := argMinFin_spec _ _ hbe'
        simp only [Bool.and_eq_true] at hpred
        exact hφ u y hpred.2
    · simp only [hw, Bool.false_eq_true, ↓reduceIte] at ha' ⊢
      have hwx : w ≠ x0 := fun heq => hw (heq ▸ hx0_in)
      have hwx_b : (w == x0) = false := beq_false_of_ne hwx
      simp only [hwx_b, Bool.false_eq_true, ↓reduceIte, ha']
      exact hφ u w ha'

public theorem contractReducedCostTable_bounds {n k M₀ : ℕ} {a : AdjTable n}
    {c : CostTable ℤ n} {f : ParentTable n} {inCycle : Vector Bool n}
    {bEntry : Vector (Option (Fin n)) n} {x0 : Fin n}
    (hbnd : ∀ u w : Fin n, -(M₀ : ℤ) ≤ c[u.val][w.val] ∧ c[u.val][w.val] ≤ (k + 1 : ℤ) * M₀)
    (hopt : ∀ x : Fin n, inCycle[x.val] = true →
      ∀ w : Fin n, a[x.val][w.val] = true → w ≠ x → c[x.val][f[x.val].val] ≤ c[x.val][w.val])
    (u w : Fin n) :
    let bExit := reducedBestExitTable a c f inCycle
    let c' := contractReducedCostTable a c f inCycle bEntry bExit x0
    (-(M₀ : ℤ) ≤ c'[u.val][w.val] ∧ c'[u.val][w.val] ≤ (k + 2 : ℤ) * M₀) := by
  dsimp only
  rw [getElem_contractReducedCostTable]
  have hzero : -(M₀ : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ (k + 2 : ℤ) * M₀ := ⟨by omega, by positivity⟩
  have hle_step : ∀ x y : Fin n,
      -(M₀ : ℤ) ≤ c[x.val][y.val] ∧ c[x.val][y.val] ≤ (k + 2 : ℤ) * M₀ := by
    intro x y
    obtain ⟨hlo, hhi⟩ := hbnd x y
    exact ⟨hlo, by nlinarith only [hhi]⟩
  split_ifs with hu hux hw_out hw hwx haw
  · cases hbx : (reducedBestExitTable a c f inCycle)[w.val] with
    | none => exact hzero
    | some x =>
      have hbx' : argMinFin n (fun z => inCycle[z.val] && a[z.val][w.val])
          (fun z => c[z.val][w.val] - c[z.val][f[z.val].val]) = some x := by
        simpa [reducedBestExitTable] using hbx
      obtain ⟨hpred, _⟩ := argMinFin_spec _ _ hbx'
      simp only [Bool.and_eq_true] at hpred
      have hwx_ne : w ≠ x := by
        intro heq
        subst heq
        simp [hpred.1] at hw_out
      have hnonneg : c[x.val][f[x.val].val] ≤ c[x.val][w.val] := hopt x hpred.1 w hpred.2 hwx_ne
      obtain ⟨_, hhi_w⟩ := hbnd x w
      obtain ⟨hlo_f, _⟩ := hbnd x f[x.val]
      have hM0 : (0 : ℤ) ≤ M₀ := Int.natCast_nonneg M₀
      dsimp only
      exact ⟨by linarith only [hM0, hnonneg], by linarith only [hhi_w, hlo_f]⟩
  all_goals first
    | exact hzero
    | exact hle_step u w
    | cases bEntry[u.val] <;> first | exact hzero | exact hle_step u ‹_›

public theorem contractReducedCostTable_natAbs_le {n B_k : ℕ} (a : AdjTable n) (c : CostTable ℤ n)
    (f : ParentTable n) (inCycle : Vector Bool n) (bEntry bExit : Vector (Option (Fin n)) n)
    (x0 : Fin n) (hB : ∀ u col : Fin n, (c[u.val][col.val]).natAbs ≤ B_k) (u col : Fin n) :
    ((contractReducedCostTable a c f inCycle bEntry bExit x0)[u.val][col.val]).natAbs ≤
      2 * B_k := by
  rw [getElem_contractReducedCostTable]
  have hz : (0 : ℤ).natAbs ≤ 2 * B_k := Nat.zero_le _
  have h2 : B_k ≤ 2 * B_k := by omega
  split_ifs
  · cases bExit[col.val] with
    | none => exact hz
    | some xs => exact (Int.natAbs_sub_le _ _).trans (by linarith only [hB xs col, hB xs f[xs.val]])
  all_goals first
    | exact hz
    | exact (hB u col).trans h2
    | cases bEntry[u.val] <;> first | exact hz | exact (hB u ‹_›).trans h2

end Cslib.Algorithms.WordRAM.Arborescence.Internal
