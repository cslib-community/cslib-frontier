/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.TwoSAT
public import CslibFrontier.Algorithms.WordRAM.ClauseCode
public import CslibFrontier.Computability.WordRAM.ListOutput
public import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.MemFrame
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FinCases

/-!
# Linear-time 2-SAT on the word RAM

The [Aspvall–Plass–Tarjan][AspvallPlassTarjan1979] linear-time 2-SAT decision and
satisfying-assignment algorithm on the standard-basis word RAM (`Cslib.WordRAM.Basis.standard`),
running in `O(n + |φ|)` instructions on formulas `φ : CNF (Fin n)`.

## Representation

An instance (`Cslib.Algorithms.WordRAM.TwoSAT.Instance`) consists of a variable count `n : ℕ` and
a formula `φ : CNF (Fin n)`. Its input word list (`Instance.encode`) stores `n`, the clause count
`|φ|`, and each clause via `Cslib.Algorithms.WordRAM.ClauseCode.encodeClauseBy Fin.val` (its
length followed by literal codes `2 * v.val + b.toNat`).

Under `Cslib.WordRAM.ExecutesList`, the output word list (`answerWords G`) is:
* `[]` when `φ` violates the width-`2` bound or is unsatisfiable (`TwoSAT.solveFin G.n G.φ = none`);
* `1 :: [(σ 0).toNat, …, (σ (n - 1)).toNat]` when `TwoSAT.solveFin G.n G.φ = some σ`.
Prefixing `1` distinguishes a satisfying empty assignment on `n = 0` (`[1]`) from rejection (`[]`),
so `decodeAnswer G (answerWords G) = TwoSAT.solveFin G.n G.φ` holds unconditionally for all `n` and
`φ`.

## Main definitions

* `Cslib.Algorithms.WordRAM.TwoSAT.Instance`: 2-SAT problem instance `(n, φ)`.
* `Cslib.Algorithms.WordRAM.TwoSAT.Instance.encode`,
  `Cslib.Algorithms.WordRAM.TwoSAT.Instance.wordBound`: input word list and linear word-width bound.
* `Cslib.Algorithms.WordRAM.TwoSAT.answerWords`,
  `Cslib.Algorithms.WordRAM.TwoSAT.decodeAnswer`: output word list and lossless decoder to
  `Option (Fin G.n → Bool)`.
* `Cslib.Algorithms.WordRAM.TwoSAT.solver`,
  `Cslib.Algorithms.WordRAM.TwoSAT.program`: structured and flat word-RAM programs.

## Main results

* `Cslib.Algorithms.WordRAM.TwoSAT.decodeAnswer_answerWords`: lossless output decoding.
* `Cslib.Algorithms.WordRAM.TwoSAT.answerWords_eq_nil_iff`,
  `Cslib.Algorithms.WordRAM.TwoSAT.eval_of_decodeAnswer_eq_some`: decision characterization and
  witness soundness.
* `Cslib.Algorithms.WordRAM.TwoSAT.program_spec`,
  `Cslib.Algorithms.WordRAM.TwoSAT.computesListInTime_program`: execution within
  `600 * (G.n + G.φ.length + 1)` instructions at every word width `w` with `Fits w G.wordBound`.

## References

* [B. Aspvall, M. F. Plass, R. E. Tarjan, *A linear-time algorithm for testing the truth of
  certain quantified boolean formulas*][AspvallPlassTarjan1979]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

public section

namespace Cslib.Algorithms.WordRAM.TwoSAT

open Cslib.Logic.PL Cslib.WordRAM
open Cslib.Algorithms.Lean.DFS Cslib.Algorithms.Lean.TwoSAT
open Cslib.Algorithms.WordRAM.ClauseCode

/-! ### Problem instances, encoding, and output specification -/

/-- A `CNF (Fin n)` instance for the word-RAM 2-SAT solver. -/
structure Instance where
  /-- Number of Boolean variables. -/
  n : ℕ
  /-- Input formula over `Fin n`. -/
  φ : CNF (Fin n)

namespace Instance

/-- Total literal occurrences across all clauses of `G.φ`. -/
@[expose] def totalLits (G : Instance) : ℕ :=
  (G.φ.map List.length).sum

/-- Word-list encoding `[n, |φ|] ++ φ.flatMap (encodeClauseBy Fin.val)`. -/
@[expose] def encode (G : Instance) : List ℕ :=
  G.n :: G.φ.length :: G.φ.flatMap (encodeClauseBy Fin.val)

/-- Output header address `G.encode.length + 1`, immediately past the input in `State.init`. -/
@[expose] def outAddrBase (G : Instance) : ℕ :=
  G.encode.length + 1

/-- Linear word-size envelope covering input length, literal codes, and scratch memory addresses. -/
@[expose] def wordBound (G : Instance) : ℕ :=
  32 * (G.n + G.φ.length + G.totalLits + 1)

private theorem length_flatMap_encodeClauseBy {n : ℕ} :
    ∀ cs : CNF (Fin n),
      (cs.flatMap (encodeClauseBy Fin.val)).length = cs.length + (cs.map List.length).sum
  | [] => rfl
  | c :: cs => by
    simp only [List.flatMap_cons, List.length_append, length_encodeClauseBy, List.length_cons,
      List.map_cons, List.sum_cons, length_flatMap_encodeClauseBy cs]
    omega

/-- Length of `G.encode` in words. -/
theorem encode_length (G : Instance) :
    G.encode.length = 2 + G.φ.length + G.totalLits := by
  simp only [encode, totalLits, List.length_cons, length_flatMap_encodeClauseBy]
  omega

private theorem totalLits_le_of_width (G : Instance) (hw : ∀ c ∈ G.φ, c.length ≤ 2) :
    G.totalLits ≤ 2 * G.φ.length := by
  unfold totalLits
  induction G.φ with
  | nil => simp
  | cons c cs ih =>
    have hc : c.length ≤ 2 := hw c List.mem_cons_self
    have hcs := ih fun c' hc' => hw c' (List.mem_cons_of_mem c hc')
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

private theorem fits_of_le {G : Instance} {w x : ℕ} (hfit : Fits w G.wordBound)
    (hle : x ≤ G.wordBound) : Fits w x :=
  hfit.of_le hle

end Instance

/-- Encode an assignment `σ : Fin n → Bool` as `1 :: [(σ 0).toNat, …, (σ (n - 1)).toNat]`. -/
@[expose] def encodeAssignment {n : ℕ} (σ : Fin n → Bool) : List ℕ :=
  1 :: (List.finRange n).map fun v => (σ v).toNat

/-- Canonical word-list output of the 2-SAT solver on `G`. -/
@[expose] def answerWords (G : Instance) : List ℕ :=
  match solveFin G.n G.φ with
  | none => []
  | some σ => encodeAssignment σ

/-- Decode a word list returned by `program` back to `Option (Fin G.n → Bool)`. -/
@[expose] def decodeAnswer (G : Instance) : List ℕ → Option (Fin G.n → Bool)
  | [] => none
  | _ :: bits => some fun v => bits.getD v.val 0 != 0

/-- Decoding `answerWords G` recovers `TwoSAT.solveFin G.n G.φ` losslessly. -/
@[simp]
theorem decodeAnswer_answerWords (G : Instance) :
    decodeAnswer G (answerWords G) = solveFin G.n G.φ := by
  unfold answerWords
  cases h : solveFin G.n G.φ with
  | none => rfl
  | some σ =>
    simp only [encodeAssignment, decodeAnswer, Option.some.injEq]
    funext v
    have hv : v.val < ((List.finRange G.n).map fun u => (σ u).toNat).length := by
      simp [v.isLt]
    rw [List.getD_eq_getElem _ 0 hv]
    simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk, Fin.eta]
    cases σ v <;> rfl

/-- `answerWords G` is empty if and only if `G.φ` is either not width-at-most-`2` or
unsatisfiable. -/
theorem answerWords_eq_nil_iff (G : Instance) :
    answerWords G = [] ↔ ¬ ((∀ c ∈ G.φ, c.length ≤ 2) ∧ G.φ.Satisfiable) := by
  rw [← isSome_solveFin_iff]
  unfold answerWords
  cases solveFin G.n G.φ <;> simp [encodeAssignment]

/-- Any assignment decoded from `answerWords G` witnesses width `≤ 2` and satisfies `G.φ`. -/
theorem eval_of_decodeAnswer_eq_some {G : Instance} {σ : Fin G.n → Bool}
    (h : decodeAnswer G (answerWords G) = some σ) :
    (∀ c ∈ G.φ, c.length ≤ 2) ∧ G.φ.eval σ = true := by
  rw [decodeAnswer_answerWords] at h
  exact solveFin_eq_some h

private theorem length_answerWords_le (G : Instance) : (answerWords G).length ≤ G.n + 1 := by
  unfold answerWords
  cases solveFin G.n G.φ <;> simp [encodeAssignment]

/-! ### Bijection `Literal (Fin n) ≃ Fin (2 * n)` and `DFS` transport -/

private theorem litCodeBy_fin_lt {n : ℕ} (ℓ : Literal (Fin n)) :
    litCodeBy Fin.val ℓ < 2 * n := by
  have hv := ℓ.1.isLt
  have hb := Bool.toNat_le ℓ.2
  unfold litCodeBy
  omega

/-- Bijection identifying `Literal (Fin n)` with `Fin (2 * n)` via `2 * v.val + b.toNat`. -/
private def litEquiv (n : ℕ) : Literal (Fin n) ≃ Fin (2 * n) where
  toFun ℓ := ⟨litCodeBy Fin.val ℓ, litCodeBy_fin_lt ℓ⟩
  invFun u := (⟨u.val / 2, by omega⟩, decide (u.val % 2 = 1))
  left_inv := by
    rintro ⟨⟨v, hv⟩, b⟩
    cases b <;> simp only [litCodeBy, Bool.toNat_false, Bool.toNat_true, Prod.mk.injEq,
      Fin.mk.injEq] <;> omega
  right_inv := by
    rintro ⟨u, hu⟩
    simp only [litCodeBy, Fin.mk.injEq]
    by_cases hmod : u % 2 = 1
    · simp only [hmod, decide_true, Bool.toNat_true]
      omega
    · simp only [hmod, decide_false, Bool.toNat_false]
      omega

private theorem getElem_literalList {V : Type*} :
    ∀ (vs : List V) (k : ℕ) (hk : k < (literalList vs).length),
      (literalList vs)[k] =
        (vs[k / 2]'(by rw [length_literalList] at hk; omega), decide (k % 2 = 1))
  | [], k, hk => by simp [literalList] at hk
  | v :: vs, 0, _ => rfl
  | v :: vs, 1, _ => rfl
  | v :: vs, k + 2, hk => by
    simp only [literalList, List.length_cons] at hk
    have hk' : k < (literalList vs).length := by omega
    have hdiv : (k + 2) / 2 = k / 2 + 1 := by omega
    have hmod : (k + 2) % 2 = k % 2 := by omega
    change (literalList vs)[k] = _
    rw [getElem_literalList vs k hk']
    simp only [hmod, Prod.mk.injEq, and_true]
    simp [hdiv]

private theorem map_litEquiv_literalList_finRange (n : ℕ) :
    (literalList (List.finRange n)).map (litEquiv n) = List.finRange (2 * n) := by
  refine List.ext_getElem ?_ fun k hk₁ hk₂ => ?_
  · simp [length_literalList]
  · simp only [List.getElem_map, List.getElem_finRange]
    rw [getElem_literalList]
    simp only [List.getElem_finRange]
    exact (litEquiv n).apply_symm_apply ⟨k, by simpa using hk₂⟩

section EquivDFS

private def mapAdj {α β : Type*} (e : α ≃ β) (g : α → List α) : β → List β :=
  fun u => (g (e.symm u)).map e

private theorem mapAdj_apply {α β : Type*} (e : α ≃ β) (g : α → List α) (x : α) :
    mapAdj e g (e x) = (g x).map e := by
  simp [mapAdj]

private theorem visit_mapAdj {α β : Type*} [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (g : α → List α) :
    ∀ (k : ℕ) (u : α) (s : Cslib.Algorithms.Lean.DFS.State α),
      visit (mapAdj e g) k (e u) ⟨s.visited.map e.toEmbedding, s.finished.map e⟩ =
        ⟨(visit g k u s).visited.map e.toEmbedding, (visit g k u s).finished.map e⟩
  | 0, _, _ => rfl
  | k + 1, u, s => by
    by_cases hu : u ∈ s.visited
    · have heu : e u ∈ s.visited.map e.toEmbedding := Finset.mem_map_of_mem e.toEmbedding hu
      simp only [visit, hu, heu, ↓reduceIte]
    · have heu : e u ∉ s.visited.map e.toEmbedding := by
        simpa only [Finset.mem_map_equiv, Equiv.symm_apply_apply] using hu
      have hfold : ∀ (l : List α) (t : Cslib.Algorithms.Lean.DFS.State α),
          (l.map e).foldl (fun st w => visit (mapAdj e g) k w st)
              ⟨t.visited.map e.toEmbedding, t.finished.map e⟩ =
            ⟨(l.foldl (fun st v => visit g k v st) t).visited.map e.toEmbedding,
              (l.foldl (fun st v => visit g k v st) t).finished.map e⟩ := by
        intro l
        induction l with
        | nil => intro _; rfl
        | cons v l ih =>
          intro t
          simp only [List.map_cons, List.foldl_cons, visit_mapAdj e g k v t]
          exact ih (visit g k v t)
      have hins : insert (e u) (s.visited.map e.toEmbedding) =
          (insert u s.visited).map e.toEmbedding :=
        (Finset.map_insert e.toEmbedding u s.visited).symm
      have hstep := hfold (g u) ⟨insert u s.visited, s.finished⟩
      simp only [visit, hu, heu, ↓reduceIte, mapAdj_apply, hins]
      rw [hstep]
      rfl

private theorem dfs_mapAdj {α β : Type*} [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (g : α → List α) (k : ℕ) (rs : List α) :
    dfs (mapAdj e g) k (rs.map e) =
      ⟨(dfs g k rs).visited.map e.toEmbedding, (dfs g k rs).finished.map e⟩ := by
  unfold dfs
  have h : ∀ (l : List α) (s : Cslib.Algorithms.Lean.DFS.State α),
      (l.map e).foldl (fun st w => visit (mapAdj e g) k w st)
          ⟨s.visited.map e.toEmbedding, s.finished.map e⟩ =
        ⟨(l.foldl (fun st v => visit g k v st) s).visited.map e.toEmbedding,
          (l.foldl (fun st v => visit g k v st) s).finished.map e⟩ := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons v l ih =>
      intro s
      simp only [List.map_cons, List.foldl_cons, visit_mapAdj e g k v s]
      exact ih (visit g k v s)
  simpa using h rs ⟨∅, []⟩

private theorem topologicalSort_mapAdj {α β : Type*} [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (g : α → List α) (vs : List α) :
    topologicalSort (mapAdj e g) (vs.map e) = (topologicalSort g vs).map e := by
  simp [topologicalSort, dfs_mapAdj]

private theorem mapAdj_update_cons {α β : Type*} [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (rev : α → List α) (v u : α) :
    Function.update (mapAdj e rev) (e v) (e u :: mapAdj e rev (e v)) =
      mapAdj e (Function.update rev v (u :: rev v)) := by
  funext w
  by_cases hw : w = e v
  · subst hw
    simp [mapAdj]
  · have hsym : e.symm w ≠ v := fun h => hw (by rw [← h, e.apply_symm_apply])
    simp [mapAdj, Function.update_of_ne hw, Function.update_of_ne hsym]

private theorem transposeAdj_mapAdj {α β : Type*} [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (g : α → List α) (vs : List α) :
    transposeAdj (mapAdj e g) (vs.map e) = mapAdj e (transposeAdj g vs) := by
  unfold transposeAdj
  have hinner : ∀ (u : α) (l : List α) (rev : α → List α),
      (l.map e).foldl (fun r w => Function.update r w (e u :: r w)) (mapAdj e rev) =
        mapAdj e (l.foldl (fun r v => Function.update r v (u :: r v)) rev) := by
    intro u l
    induction l with
    | nil => intro _; rfl
    | cons v l ih =>
      intro rev
      simp only [List.map_cons, List.foldl_cons, mapAdj_update_cons]
      exact ih _
  have houter : ∀ (l : List α) (rev : α → List α),
      (l.map e).foldl
          (fun r u => (mapAdj e g u).foldl (fun r w => Function.update r w (u :: r w)) r)
          (mapAdj e rev) =
        mapAdj e (l.foldl
          (fun r u => (g u).foldl (fun r v => Function.update r v (u :: r v)) r) rev) := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons u l ih =>
      intro rev
      simp only [List.map_cons, List.foldl_cons, mapAdj_apply, hinner]
      exact ih _
  have h0 : (fun _ : β => ([] : List β)) = mapAdj e (fun _ => []) := rfl
  rw [h0]
  exact houter vs (fun _ => [])

private theorem peelSCCs_mapAdj {α β : Type*} [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (rev : α → List α) (k : ℕ) :
    ∀ (vis : Finset α) (rs : List α),
      peelSCCs (mapAdj e rev) k (vis.map e.toEmbedding) (rs.map e) =
        (peelSCCs rev k vis rs).map (List.map e)
  | _, [] => rfl
  | vis, r :: rs => by
    have hv := visit_mapAdj e rev k r ⟨vis, []⟩
    change (let s := visit (mapAdj e rev) k (e r) ⟨vis.map e.toEmbedding, ([] : List α).map e⟩
        if s.finished.isEmpty then peelSCCs (mapAdj e rev) k s.visited (rs.map e)
        else s.finished :: peelSCCs (mapAdj e rev) k s.visited (rs.map e)) = _
    rw [hv]
    dsimp only [peelSCCs]
    rw [List.isEmpty_map]
    split_ifs <;> simp [peelSCCs_mapAdj e rev k (visit rev k r ⟨vis, []⟩).visited rs]

private theorem sccs_mapAdj {α β : Type*} [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (g : α → List α) (vs : List α) :
    sccs (mapAdj e g) (vs.map e) = (sccs g vs).map (List.map e) := by
  simp only [sccs, List.length_map, transposeAdj_mapAdj, topologicalSort_mapAdj]
  simpa using peelSCCs_mapAdj e (transposeAdj g vs) vs.length ∅ (topologicalSort g vs)

private theorem indexComponentsAux_map {α β : Type*} [DecidableEq α] [DecidableEq β] (e : α ≃ β) :
    ∀ (idx : ℕ) (cs : List (List α)) (f : α → ℕ) (x : α),
      indexComponentsAux idx (cs.map (List.map e)) (f ∘ e.symm) (e x) =
        indexComponentsAux idx cs f x
  | _, [], f, x => by simp [indexComponentsAux]
  | idx, c :: cs, f, x => by
    have hfold : ((c.map e).foldl (fun g w => Function.update g w idx) (f ∘ e.symm)) =
        (c.foldl (fun g v => Function.update g v idx) f) ∘ e.symm := by
      induction c generalizing f with
      | nil => rfl
      | cons v c ih =>
        simp only [List.map_cons, List.foldl_cons]
        have hstep : Function.update (f ∘ e.symm) (e v) idx =
            Function.update f v idx ∘ e.symm := by
          funext w
          by_cases hw : w = e v
          · subst hw; simp
          · have hsym : e.symm w ≠ v := fun h => hw (by rw [← h, e.apply_symm_apply])
            simp [Function.update_of_ne hw, Function.update_of_ne hsym]
        rw [hstep]
        exact ih _
    simp only [List.map_cons, indexComponentsAux, hfold]
    exact indexComponentsAux_map e (idx + 1) cs _ x

private theorem indexComponents_sccs_mapAdj {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (g : α → List α) (vs : List α) (x : α) :
    indexComponents (sccs (mapAdj e g) (vs.map e)) (e x) = indexComponents (sccs g vs) x := by
  rw [sccs_mapAdj]
  exact indexComponentsAux_map e 0 (sccs g vs) (fun _ => 0) x

end EquivDFS

/-- Implication graph of `G` pushed forward along `litEquiv G.n` to `Fin (2 * G.n)`. -/
private def Instance.adjFin (G : Instance) : Fin (2 * G.n) → List (Fin (2 * G.n)) :=
  mapAdj (litEquiv G.n) (implicationAdj G.φ)

private theorem Instance.indexComponents_adjFin (G : Instance) (ℓ : Literal (Fin G.n)) :
    indexComponents (sccs G.adjFin (List.finRange (2 * G.n))) (litEquiv G.n ℓ) =
      indexComponents (sccs (implicationAdj G.φ) (literalList (List.finRange G.n))) ℓ := by
  rw [← map_litEquiv_literalList_finRange]
  exact indexComponents_sccs_mapAdj (litEquiv G.n) (implicationAdj G.φ)
    (literalList (List.finRange G.n)) ℓ

/-! ### Registers and scratch memory layout -/

namespace Reg

private abbrev cZero : Fin 28 := 0
private abbrev cOne : Fin 28 := 1
private abbrev cTwo : Fin 28 := 2
private abbrev cThree : Fin 28 := 3
private abbrev nv : Fin 28 := 4
private abbrev mClauses : Fin 28 := 5
private abbrev nVerts : Fin 28 := 6
private abbrev outBase : Fin 28 := 7
private abbrev offB : Fin 28 := 8
private abbrev edgeB : Fin 28 := 9
private abbrev visB : Fin 28 := 10
private abbrev finB : Fin 28 := 11
private abbrev stkB : Fin 28 := 12
private abbrev curB : Fin 28 := 13
private abbrev revOffB : Fin 28 := 14
private abbrev revEdgeB : Fin 28 := 15
private abbrev ordB : Fin 28 := 16
private abbrev compB : Fin 28 := 17
private abbrev iReg : Fin 28 := 18
private abbrev pReg : Fin 28 := 19
private abbrev finCnt : Fin 28 := 20
private abbrev compIdxReg : Fin 28 := 21
private abbrev oldFinReg : Fin 28 := 22
private abbrev uReg : Fin 28 := 23
private abbrev vReg : Fin 28 := 24
private abbrev jReg : Fin 28 := 25
private abbrev jEndReg : Fin 28 := 26
private abbrev addr : Fin 28 := 27

end Reg

open Reg

private def kOffAddr (wb : ℕ) : ℕ := wb
private def kEdgeAddr (wb N : ℕ) : ℕ := wb + N + 1
private def kRevOffAddr (wb N Mc : ℕ) : ℕ := wb + N + 1 + Mc
private def kRevEdgeAddr (wb N Mc : ℕ) : ℕ := wb + 2 * N + 2 + Mc
private def kCurAddr (wb N Mc : ℕ) : ℕ := wb + 2 * N + 2 + 2 * Mc
private def kVisAddr (wb N Mc : ℕ) : ℕ := wb + 3 * N + 3 + 2 * Mc
private def kOrdAddr (wb N Mc : ℕ) : ℕ := wb + 4 * N + 3 + 2 * Mc
private def kFinAddr (wb N Mc : ℕ) : ℕ := wb + 5 * N + 3 + 2 * Mc
private def kStkAddr (wb N Mc : ℕ) : ℕ := wb + 6 * N + 3 + 2 * Mc
private def kCompAddr (wb N Mc : ℕ) : ℕ := wb + 9 * N + 3 + 2 * Mc
private def kTopAddr (wb N Mc : ℕ) : ℕ := wb + 10 * N + 3 + 2 * Mc

namespace Instance

private def workBase (G : Instance) : ℕ := G.outAddrBase + G.n + 2

private theorem kTopAddr_le_wordBound (G : Instance) :
    kTopAddr G.workBase (2 * G.n) (2 * G.φ.length) ≤ G.wordBound := by
  simp only [kTopAddr, workBase, outAddrBase, encode_length, wordBound]
  omega

end Instance

/-! ### Input memory readback and `O(|φ|)` clause-width check -/

private def ClauseMemAt {n : ℕ} (mem : ℕ → ℕ) (p : ℕ) (cs : CNF (Fin n)) : Prop :=
  let ws := cs.flatMap (encodeClauseBy Fin.val)
  ∀ k (hk : k < ws.length), mem (p + k) = ws[k]

private theorem clauseMemAt_init (G : Instance) :
    ClauseMemAt (Data.init G.encode : Data 28).mem 3 G.φ := by
  intro k hk
  have h1 : 3 + k = (k + 2) + 1 := by omega
  rw [h1, Data.init_mem_succ]
  have hlen : k + 2 < G.encode.length := by
    rw [Instance.length_flatMap_encodeClauseBy] at hk
    rw [G.encode_length]
    unfold Instance.totalLits
    omega
  rw [List.getD_eq_getElem _ 0 hlen]
  simp [Instance.encode]

private theorem clauseMemAt_cons {n : ℕ} {mem : ℕ → ℕ} {p : ℕ} {c : Clause (Fin n)}
    {cs : CNF (Fin n)} (h : ClauseMemAt mem p (c :: cs)) :
    mem p = c.length ∧
      (∀ i (hi : i < c.length), mem (p + 1 + i) = litCodeBy Fin.val c[i]) ∧
      ClauseMemAt mem (p + 1 + c.length) cs := by
  refine ⟨?_, fun i hi => ?_, fun k hk => ?_⟩
  · have h0 := h 0 (by simp [encodeClauseBy])
    simpa [encodeClauseBy] using h0
  · have hi' : i + 1 < ((c :: cs).flatMap (encodeClauseBy Fin.val)).length := by
      simp only [List.flatMap_cons, List.length_append, length_encodeClauseBy]
      omega
    have h1 := h (i + 1) hi'
    rw [show p + (i + 1) = p + 1 + i by omega] at h1
    rw [h1]
    simp only [List.flatMap_cons, encodeClauseBy, List.cons_append, List.getElem_cons_succ]
    rw [List.getElem_append_left (by simp [hi])]
    simp
  · have hk' : c.length + 1 + k < ((c :: cs).flatMap (encodeClauseBy Fin.val)).length := by
      simp only [List.flatMap_cons, List.length_append, length_encodeClauseBy]
      omega
    have h2 := h (c.length + 1 + k) hk'
    rw [show p + (c.length + 1 + k) = p + 1 + c.length + k by omega] at h2
    rw [h2]
    simp only [List.flatMap_cons]
    rw [List.getElem_append_right (by simp [length_encodeClauseBy])]
    simp [length_encodeClauseBy]

/-- Setup constants, input dimensions, and `outBase`. -/
private def headerSetupCode : Code .standard 28 := ram[
  cZero ← #0; cOne ← #1; cTwo ← #2; cThree ← #3;
  outBase ← *cZero; outBase ← outBase + cOne;
  nv ← *cOne; mClauses ← *cTwo ]

/-- Body checking `1 ≤ c.length ≤ 2` and advancing `pReg` by `c.length + 1` in `O(1)` steps. -/
private def checkClauseBody : Code .standard 28 := ram[
  jReg ← *pReg;
  if jReg = cZero then [ compIdxReg ← cZero ]
  else [
    if cTwo < jReg then [ compIdxReg ← cZero ] else [ compIdxReg ← compIdxReg ] ];
  pReg ← pReg + jReg; pReg ← pReg + cOne;
  iReg ← iReg + cOne ]

private def checkClausesCode : Code .standard 28 :=
  (ram[ compIdxReg ← cOne; pReg ← cThree; iReg ← cZero ]).seq
    (.loop (.lt iReg mClauses) checkClauseBody)

private theorem checkClausesLoop_spec (G : Instance) {w : ℕ} (hfit : Fits w G.wordBound) :
    ∀ (cs : CNF (Fin G.n)) (idx p : ℕ) (ok : Bool) (x : Data 28),
      idx + cs.length = G.φ.length →
      p + (cs.flatMap (encodeClauseBy Fin.val)).length = G.encode.length + 1 →
      ClauseMemAt x.mem p cs →
      x.regs cZero = 0 → x.regs cOne = 1 → x.regs cTwo = 2 →
      x.regs mClauses = G.φ.length →
      x.regs iReg = idx → x.regs pReg = p → x.regs compIdxReg = ok.toNat →
      ∃ y, ExecWithin w (.loop (.lt iReg mClauses) checkClauseBody) x y (12 * cs.length + 2) ∧
        y.mem = x.mem ∧
        y.regs compIdxReg = (cs.foldl (fun acc c => acc && isValidTwoClause c) ok).toNat ∧
        (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r)
  | [], idx, _, ok, x, hidx, _, _, _, _, _, hm, hi, _, hok => by
    simp only [List.length_nil] at hidx
    have hend : ¬ (Cond.lt iReg mClauses).Holds x := by
      change ¬ x.regs iReg < x.regs mClauses
      omega
    refine ⟨x, ⟨2, by omega, Exec.loop_exit hend⟩, rfl, hok, fun _ _ => rfl⟩
  | c :: cs, idx, p, ok, x, hidx, hp, hcm, hc0, hc1, hc2, hm, hi, hpR, hok => by
    obtain ⟨hlen_p, -, hcm_rest⟩ := clauseMemAt_cons hcm
    have hflat_cons : ((c :: cs).flatMap (encodeClauseBy Fin.val)).length =
        c.length + 1 + (cs.flatMap (encodeClauseBy Fin.val)).length := by
      simp [List.flatMap_cons, length_encodeClauseBy, Nat.add_assoc]
    have hp_bound : Fits w (p + c.length) :=
      G.fits_of_le hfit (by have := G.encode_length; unfold Instance.wordBound; omega)
    have hp_bound1 : Fits w (p + c.length + 1) :=
      G.fits_of_le hfit (by have := G.encode_length; unfold Instance.wordBound; omega)
    have hi_bound : Fits w (idx + 1) :=
      G.fits_of_le hfit (by unfold Instance.wordBound; omega)
    let StepPost (x₁ : Data 28) : Prop :=
      x₁.mem = x.mem ∧
        x₁.regs iReg = idx + 1 ∧
        x₁.regs pReg = p + 1 + c.length ∧
        x₁.regs compIdxReg = (ok && isValidTwoClause c).toNat ∧
        (∀ r : Fin 28, r.val < 18 → x₁.regs r = x.regs r)
    have hstep : ∃ x₁, ExecWithin w checkClauseBody x x₁ 10 ∧ StepPost x₁ := by
      unfold checkClauseBody
      wram_exec [hc0, hc1, hc2, hi, hpR, hok, hlen_p, hp_bound, hp_bound1, hi_bound]
      · dsimp only [StepPost]
        refine ⟨rfl, by wram_simp, by wram_simp; omega, ?_, fun r hr => ?_⟩
        · try wram_simp
          simp [isValidTwoClause, ‹c.length = 0›]
        · wram_simp; fin_cases r <;> simp_all
      · dsimp only [StepPost]
        refine ⟨rfl, by wram_simp, by wram_simp; omega, ?_, fun r hr => ?_⟩
        · try wram_simp
          have hc_gt : ¬ c.length ≤ 2 := by omega
          simp [isValidTwoClause, hc_gt]
        · wram_simp; fin_cases r <;> simp_all
      · dsimp only [StepPost]
        refine ⟨rfl, by wram_simp, by wram_simp; omega, ?_, fun r hr => ?_⟩
        · try wram_simp
          have hc_ok : 1 ≤ c.length ∧ c.length ≤ 2 := by omega
          simp [isValidTwoClause, hc_ok]
        · wram_simp; fin_cases r <;> simp_all
    obtain ⟨x₁, hx₁_ex, hx₁_mem, hx₁_i, hx₁_p, hx₁_ok, hx₁_fr⟩ := hstep
    have hlt : (Cond.lt iReg mClauses).Holds x := by
      change x.regs iReg < x.regs mClauses
      simp only [List.length_cons] at hidx
      omega
    obtain ⟨y, hy_ex, hy_mem, hy_ok, hy_fr⟩ := checkClausesLoop_spec G hfit cs (idx + 1)
      (p + 1 + c.length) (ok && isValidTwoClause c) x₁
      (by simp only [List.length_cons] at hidx; omega)
      (by rw [hflat_cons] at hp; omega)
      (hx₁_mem ▸ hcm_rest)
      ((hx₁_fr cZero (by decide)).trans hc0)
      ((hx₁_fr cOne (by decide)).trans hc1)
      ((hx₁_fr cTwo (by decide)).trans hc2)
      ((hx₁_fr mClauses (by decide)).trans hm)
      hx₁_i hx₁_p hx₁_ok
    obtain ⟨t₁, ht₁, he₁⟩ := hx₁_ex
    obtain ⟨t₂, ht₂, he₂⟩ := hy_ex
    refine ⟨y, ⟨t₁ + t₂ + 2, by simp only [List.length_cons]; omega,
        Exec.loop_iter hlt he₁ he₂⟩, hy_mem.trans hx₁_mem, hy_ok,
      fun r hr => (hy_fr r hr).trans (hx₁_fr r hr)⟩

/-! ### Reusable CSR representation and shared array/CSR primitives -/

private def csrOffset {N : ℕ} (adj : Fin N → List (Fin N)) (u : ℕ) : ℕ :=
  (((List.finRange N).take u).map fun w => (adj w).length).sum

@[simp]
private theorem csrOffset_zero {N : ℕ} (adj : Fin N → List (Fin N)) :
    csrOffset adj 0 = 0 := rfl

private theorem csrOffset_succ {N : ℕ} (adj : Fin N → List (Fin N)) {u : ℕ} (hu : u < N) :
    csrOffset adj (u + 1) = csrOffset adj u + (adj ⟨u, hu⟩).length := by
  unfold csrOffset
  have hlen : u < (List.finRange N).length := by simpa using hu
  rw [List.take_add_one, List.getElem?_eq_getElem hlen]
  simp

private theorem csrOffset_mono {N : ℕ} (adj : Fin N → List (Fin N)) {a b : ℕ} (hab : a ≤ b) :
    csrOffset adj a ≤ csrOffset adj b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  induction d with
  | zero => simp
  | succ d ih =>
    by_cases hlt : a + d < N
    · rw [Nat.add_succ, csrOffset_succ adj hlt]
      exact ih.trans (Nat.le_add_right _ _)
    · have heq : csrOffset adj (a + (d + 1)) = csrOffset adj (a + d) := by
        unfold csrOffset
        rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp; omega)]
      rw [heq]
      exact ih

private theorem csrOffset_eq_outDegreeSum {N : ℕ} (adj : Fin N → List (Fin N)) :
    csrOffset adj N = outDegreeSum adj (List.finRange N) := by
  unfold csrOffset outDegreeSum
  rw [List.take_of_length_le (by simp)]

private def CSRAt {N : ℕ} (adj : Fin N → List (Fin N)) (offBase edgeBase : ℕ)
    (mem : ℕ → ℕ) : Prop :=
  (∀ u ≤ N, mem (offBase + u) = csrOffset adj u) ∧
    ∀ (u : Fin N) (k : ℕ) (hk : k < (adj u).length),
      mem (edgeBase + csrOffset adj u.val + k) = ((adj u)[k]).val

private def PartialCSRAt {N : ℕ} (targetAdj part : Fin N → List (Fin N))
    (curBase edgeBase : ℕ) (mem : ℕ → ℕ) : Prop :=
  (∀ w : Fin N, (part w).length ≤ (targetAdj w).length) ∧
    (∀ w : Fin N, mem (curBase + w.val) + (part w).length = csrOffset targetAdj (w.val + 1)) ∧
    ∀ (w : Fin N) (k : ℕ) (hk : k < (part w).length),
      mem (edgeBase + mem (curBase + w.val) + k) = ((part w)[k]).val

private theorem partialCSRAt_init {N : ℕ} (targetAdj : Fin N → List (Fin N))
    (curBase edgeBase : ℕ) (mem : ℕ → ℕ)
    (hcur : ∀ w : Fin N, mem (curBase + w.val) = csrOffset targetAdj (w.val + 1)) :
    PartialCSRAt targetAdj (fun _ => []) curBase edgeBase mem :=
  ⟨fun _ => Nat.zero_le _, fun w => by simp [hcur w], fun _ _ hk => by simp at hk⟩

private theorem csrAt_of_partialCSRAt {N : ℕ} (targetAdj : Fin N → List (Fin N))
    (offBase curBase edgeBase : ℕ) (mem : ℕ → ℕ)
    (hoff : ∀ u ≤ N, mem (offBase + u) = csrOffset targetAdj u)
    (hp : PartialCSRAt targetAdj targetAdj curBase edgeBase mem) :
    CSRAt targetAdj offBase edgeBase mem := by
  refine ⟨hoff, fun u k hk => ?_⟩
  have hcur_u := hp.2.1 u
  rw [csrOffset_succ targetAdj u.isLt] at hcur_u
  simp only [Fin.eta] at hcur_u
  have heq : mem (curBase + u.val) = csrOffset targetAdj u.val := by omega
  have hget := hp.2.2 u k hk
  rwa [heq] at hget

/-- Zero `[visB, visB + nVerts)` in `5 * N + 3` instructions. -/
private def zeroVisBody : Code .standard 28 := ram[
  addr ← visB + iReg; *addr ← cZero; iReg ← iReg + cOne ]

private def zeroVisCode : Code .standard 28 :=
  (ram[ iReg ← cZero ]).seq (.loop (.lt iReg nVerts) zeroVisBody)

private theorem zeroVisCode_spec {w : ℕ} (B N : ℕ) (hfit : Fits w (B + N + 1)) {x : Data 28}
    (hc0 : x.regs cZero = 0) (hc1 : x.regs cOne = 1)
    (hB : x.regs visB = B) (hN : x.regs nVerts = N) :
    ∃ y, ExecWithin w zeroVisCode x y (5 * N + 3) ∧
      (∀ i < N, y.mem (B + i) = 0) ∧
      (∀ a, ¬ (B ≤ a ∧ a < B + N) → y.mem a = x.mem a) ∧
      (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r) := by
  have hprep : ∃ x₀, ExecWithin (B := .standard) w (ram[ iReg ← cZero ]) x x₀ 1 ∧
      x₀.mem = x.mem ∧ x₀.regs iReg = 0 ∧
      (∀ r : Fin 28, r.val < 18 → x₀.regs r = x.regs r) := by
    let PrepPost (x₀ : Data 28) : Prop :=
      x₀.mem = x.mem ∧ x₀.regs iReg = 0 ∧
        (∀ r : Fin 28, r.val < 18 → x₀.regs r = x.regs r)
    change ∃ x₀, ExecWithin (B := .standard) w (ram[ iReg ← cZero ]) x x₀ 1 ∧ PrepPost x₀
    wram_exec [hc0]
    refine ⟨rfl, by try wram_simp, fun r hr => ?_⟩
    wram_simp; fin_cases r <;> simp_all
  obtain ⟨x₀, hx₀_ex, hx₀_mem, hx₀_i, hx₀_fr⟩ := hprep
  let P (k : ℕ) (y : Data 28) : Prop :=
    (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r) ∧
      (∀ i < k, y.mem (B + i) = 0) ∧
      (∀ a, ¬ (B ≤ a ∧ a < B + k) → y.mem a = x.mem a)
  have hbody : ∀ y, P (y.regs iReg) y → y.regs iReg < N →
      ∃ z, ExecWithin w zeroVisBody y z 3 ∧
        P (y.regs iReg + 1) z ∧ z.regs iReg = y.regs iReg + 1 := by
    intro y ⟨hy_fr, hy_zero, hy_out⟩ hlt
    have hy0 : y.regs cZero = 0 := (hy_fr cZero (by decide)).trans hc0
    have hy1 : y.regs cOne = 1 := (hy_fr cOne (by decide)).trans hc1
    have hyB : y.regs visB = B := (hy_fr visB (by decide)).trans hB
    have hf_addr : Fits w (B + y.regs iReg) := hfit.of_le (by omega)
    have hf_inc : Fits w (y.regs iReg + 1) := hfit.of_le (by omega)
    let BodyPost (z : Data 28) : Prop :=
      P (y.regs iReg + 1) z ∧ z.regs iReg = y.regs iReg + 1
    change ∃ z, ExecWithin w zeroVisBody y z 3 ∧ BodyPost z
    unfold zeroVisBody
    wram_exec [hy0, hy1, hyB, hf_addr, hf_inc]
    have hpw := prefix_write_step (e := fun _ => 0) hy_zero hy_out (z := Function.update y.mem
      (B + y.regs iReg) 0) rfl
    refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, by try wram_simp⟩
    · wram_simp
      have := hy_fr r hr
      fin_cases r <;> simp_all
    · try wram_simp
      exact hpw.1
    · try wram_simp
      exact hpw.2
  obtain ⟨y, hy_loop, hy_P, -⟩ := ExecWithin.loop_count P
    (fun y hy => (hy.1 nVerts (by decide)).trans hN) hbody
    (x := x₀) (by omega)
    ⟨hx₀_fr, fun i hi => by omega, fun a _ => congrFun hx₀_mem a⟩
  exact ⟨y, (hx₀_ex.seq hy_loop).mono (by omega), hy_P.2.1, hy_P.2.2, hy_P.1⟩

/-- Increment `mem[curB + vReg]` by `1` in `4` instructions. -/
private def incCurCode : Code .standard 28 := ram[
  addr ← curB + vReg; jEndReg ← *addr; jEndReg ← jEndReg + cOne; *addr ← jEndReg ]

private theorem incCurCode_spec {N w : ℕ} (curBase maxDeg : ℕ)
    (hfit : Fits w (curBase + N + maxDeg + 1))
    (deg : Fin N → ℕ) (src : Fin N) (hdeg_le : deg src + 1 ≤ maxDeg)
    {x : Data 28} (hc1 : x.regs cOne = 1) (hcur : x.regs curB = curBase)
    (hsrc : x.regs vReg = src.val)
    (hmem : ∀ u : Fin N, x.mem (curBase + u.val) = deg u) :
    ∃ y, ExecWithin w incCurCode x y 4 ∧
      (∀ u : Fin N, y.mem (curBase + u.val) = Function.update deg src (deg src + 1) u) ∧
      (∀ a, ¬ (curBase ≤ a ∧ a < curBase + N) → y.mem a = x.mem a) ∧
      (∀ r : Fin 28, r ≠ addr → r ≠ jEndReg → y.regs r = x.regs r) := by
  have hlt := src.isLt
  have hm_src := hmem src
  have hf_addr : Fits w (curBase + src.val) := hfit.of_le (by omega)
  have hf_val : Fits w (deg src + 1) := hfit.of_le (by omega)
  let IncPost (y : Data 28) : Prop :=
    (∀ u : Fin N, y.mem (curBase + u.val) = Function.update deg src (deg src + 1) u) ∧
      (∀ a, ¬ (curBase ≤ a ∧ a < curBase + N) → y.mem a = x.mem a) ∧
      (∀ r : Fin 28, r ≠ addr → r ≠ jEndReg → y.regs r = x.regs r)
  change ∃ y, ExecWithin w incCurCode x y 4 ∧ IncPost y
  unfold incCurCode
  wram_exec [hc1, hcur, hsrc, hm_src, hf_addr, hf_val]
  refine ⟨fun u => ?_, fun a ha => ?_, fun r h1 h2 => ?_⟩
  · wram_simp
    by_cases hu : u = src
    · subst hu; simp
    · have hne : curBase + u.val ≠ curBase + src.val := fun h => hu (Fin.ext (by omega))
      simp [Function.update_of_ne hne, Function.update_of_ne hu, hmem u]
  · wram_simp
    exact Function.update_of_ne (by omega) _ _
  · wram_simp; fin_cases r <;> simp_all

/-- Compute CSR prefix sums `offB[0..N]` from degrees in `curB[0..N)` and set
`curB[u] := offB[u + 1]` in `9 * N + 5` instructions. -/
private def prefixSumBody : Code .standard 28 := ram[
  addr ← curB + iReg; uReg ← *addr;
  pReg ← pReg + uReg;
  *addr ← pReg;
  iReg ← iReg + cOne;
  addr ← offB + iReg; *addr ← pReg ]

private def prefixSumCode : Code .standard 28 :=
  (ram[ *offB ← cZero; pReg ← cZero; iReg ← cZero ]).seq
    (.loop (.lt iReg nVerts) prefixSumBody)

private theorem prefixSumCode_spec {N w : ℕ} (targetAdj : Fin N → List (Fin N))
    (degBase offBase Mc : ℕ) (hdisj : offBase + N + 1 ≤ degBase)
    (hmc : csrOffset targetAdj N ≤ Mc)
    (hfit : Fits w (degBase + N + Mc + 2))
    {x : Data 28} (hc0 : x.regs cZero = 0) (hc1 : x.regs cOne = 1)
    (hdegB : x.regs curB = degBase) (hoffB : x.regs offB = offBase)
    (hL : x.regs nVerts = N)
    (hdeg : ∀ u : Fin N, x.mem (degBase + u.val) = (targetAdj u).length) :
    ∃ y, ExecWithin w prefixSumCode x y (9 * N + 5) ∧
      (∀ u ≤ N, y.mem (offBase + u) = csrOffset targetAdj u) ∧
      (∀ u : Fin N, y.mem (degBase + u.val) = csrOffset targetAdj (u.val + 1)) ∧
      (∀ a, ¬ ((offBase ≤ a ∧ a < offBase + N + 1) ∨ (degBase ≤ a ∧ a < degBase + N)) →
        y.mem a = x.mem a) ∧
      (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r) := by
  have hprep : ∃ x₀, ExecWithin (B := .standard) w
      (ram[ *offB ← cZero; pReg ← cZero; iReg ← cZero ]) x x₀ 3 ∧
      x₀.mem = Function.update x.mem offBase 0 ∧
      x₀.regs pReg = 0 ∧ x₀.regs iReg = 0 ∧
      (∀ r : Fin 28, r.val < 18 → x₀.regs r = x.regs r) := by
    let PrepPost (x₀ : Data 28) : Prop :=
      x₀.mem = Function.update x.mem offBase 0 ∧
        x₀.regs pReg = 0 ∧ x₀.regs iReg = 0 ∧
        (∀ r : Fin 28, r.val < 18 → x₀.regs r = x.regs r)
    change ∃ x₀, ExecWithin (B := .standard) w
      (ram[ *offB ← cZero; pReg ← cZero; iReg ← cZero ]) x x₀ 3 ∧ PrepPost x₀
    wram_exec [hc0, hoffB]
    refine ⟨by wram_simp, by try wram_simp, by try wram_simp, fun r hr => ?_⟩
    wram_simp; fin_cases r <;> simp_all
  obtain ⟨x₀, hx₀_ex, hx₀_mem, hx₀_p, hx₀_i, hx₀_fr⟩ := hprep
  let P (k : ℕ) (y : Data 28) : Prop :=
    (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r) ∧
      y.regs pReg = csrOffset targetAdj k ∧
      (∀ u ≤ k, y.mem (offBase + u) = csrOffset targetAdj u) ∧
      (∀ u : Fin N, y.mem (degBase + u.val) =
        if u.val < k then csrOffset targetAdj (u.val + 1) else (targetAdj u).length) ∧
      (∀ a, ¬ ((offBase ≤ a ∧ a ≤ offBase + k) ∨ (degBase ≤ a ∧ a < degBase + k)) →
        y.mem a = x.mem a)
  have hbody : ∀ y, P (y.regs iReg) y → y.regs iReg < N →
      ∃ z, ExecWithin w prefixSumBody y z 7 ∧
        P (y.regs iReg + 1) z ∧ z.regs iReg = y.regs iReg + 1 := by
    intro y ⟨hy_fr, hy_p, hy_off, hy_deg, hy_out⟩ hlt
    have hy1 : y.regs cOne = 1 := (hy_fr cOne (by decide)).trans hc1
    have hyD : y.regs curB = degBase := (hy_fr curB (by decide)).trans hdegB
    have hyO : y.regs offB = offBase := (hy_fr offB (by decide)).trans hoffB
    have hdeg_k : y.mem (degBase + y.regs iReg) = (targetAdj ⟨y.regs iReg, hlt⟩).length := by
      have := hy_deg ⟨y.regs iReg, hlt⟩
      simpa using this
    have hoff_succ : csrOffset targetAdj (y.regs iReg + 1) =
        csrOffset targetAdj (y.regs iReg) + (targetAdj ⟨y.regs iReg, hlt⟩).length :=
      csrOffset_succ targetAdj hlt
    have hoff_le : csrOffset targetAdj (y.regs iReg + 1) ≤ Mc :=
      (csrOffset_mono targetAdj (by omega : y.regs iReg + 1 ≤ N)).trans hmc
    have hf_daddr : Fits w (degBase + y.regs iReg) := hfit.of_le (by omega)
    have hf_psum : Fits w (csrOffset targetAdj (y.regs iReg) +
        (targetAdj ⟨y.regs iReg, hlt⟩).length) :=
      hfit.of_le (by omega)
    have hf_k1 : Fits w (y.regs iReg + 1) := hfit.of_le (by omega)
    have hf_oaddr : Fits w (offBase + (y.regs iReg + 1)) := hfit.of_le (by omega)
    let BodyPost (z : Data 28) : Prop :=
      P (y.regs iReg + 1) z ∧ z.regs iReg = y.regs iReg + 1
    change ∃ z, ExecWithin w prefixSumBody y z 7 ∧ BodyPost z
    unfold prefixSumBody
    wram_exec [hy1, hyD, hyO, hy_p, hdeg_k, hf_daddr, hf_psum, hf_k1, hf_oaddr]
    refine ⟨⟨fun r hr => ?_, ?_, fun u hu => ?_, fun u => ?_, fun a ha => ?_⟩, by try wram_simp⟩
    · wram_simp
      have := hy_fr r hr
      fin_cases r <;> simp_all
    · wram_simp; exact hoff_succ.symm
    · wram_simp
      by_cases huk : u = y.regs iReg + 1
      · subst huk; simp [hoff_succ]
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hy_off u (by omega)
    · wram_simp
      rw [Function.update_of_ne (by have := u.isLt; omega)]
      by_cases huk : u.val = y.regs iReg
      · rw [huk, Function.update_self]
        simp [hoff_succ]
      · rw [Function.update_of_ne (by omega), hy_deg u]
        by_cases hlt' : u.val < y.regs iReg
        · have hlt'' : u.val < y.regs iReg + 1 := by omega
          simp [hlt', hlt'']
        · have hlt'' : ¬ u.val < y.regs iReg + 1 := by omega
          simp [hlt', hlt'']
    · wram_simp
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hy_out a (by omega)
  have hx₀_P : P (x₀.regs iReg) x₀ := by
    rw [hx₀_i]
    refine ⟨hx₀_fr, hx₀_p, fun u hu => ?_, fun u => ?_, fun a ha => ?_⟩
    · have hu0 : u = 0 := by omega
      subst hu0; simp [hx₀_mem]
    · simp only [Nat.not_lt_zero, ↓reduceIte, hx₀_mem]
      rw [Function.update_of_ne (by omega)]
      exact hdeg u
    · rw [hx₀_mem, Function.update_of_ne (by omega)]
  obtain ⟨y, hy_loop, hy_P, -⟩ := ExecWithin.loop_count P
    (fun y hy => (hy.1 nVerts (by decide)).trans hL) hbody
    (x := x₀) (by omega) hx₀_P
  refine ⟨y, (hx₀_ex.seq hy_loop).mono (by omega), hy_P.2.2.1, fun u => ?_, fun a ha => ?_,
    hy_P.1⟩
  · simpa [u.isLt] using hy_P.2.2.2.1 u
  · exact hy_P.2.2.2.2 a (by omega)

/-- Decrement `curB[vReg]` and write `uReg` into `edgeB[curB[vReg]]` in `6` instructions. -/
private def backfillStepCode : Code .standard 28 := ram[
  addr ← curB + vReg;
  jEndReg ← *addr; jEndReg ← jEndReg - cOne;
  *addr ← jEndReg;
  addr ← edgeB + jEndReg; *addr ← uReg ]

private theorem csrOffset_disjoint {N : ℕ} (adj : Fin N → List (Fin N)) {u v : Fin N}
    (hne : u ≠ v) {p q : ℕ}
    (hp1 : csrOffset adj u.val ≤ p) (hp2 : p < csrOffset adj (u.val + 1))
    (hq1 : csrOffset adj v.val ≤ q) (hq2 : q < csrOffset adj (v.val + 1)) : p ≠ q := by
  have hval : u.val ≠ v.val := fun h => hne (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hval with hlt | hgt
  · have := csrOffset_mono adj (by omega : u.val + 1 ≤ v.val)
    omega
  · have := csrOffset_mono adj (by omega : v.val + 1 ≤ u.val)
    omega

private theorem partialCSRAt_step {N : ℕ}
    (targetAdj part : Fin N → List (Fin N))
    (curBase edgeBase Mc : ℕ)
    (hdisj : edgeBase + Mc ≤ curBase)
    (hmc : csrOffset targetAdj N ≤ Mc)
    (src dst : Fin N) (hroom : (part src).length + 1 ≤ (targetAdj src).length)
    (mem : ℕ → ℕ)
    (hp : PartialCSRAt targetAdj part curBase edgeBase mem) :
    let c := mem (curBase + src.val) - 1
    let mem' := Function.update (Function.update mem (curBase + src.val) c) (edgeBase + c) dst.val
    PartialCSRAt targetAdj (Function.update part src (dst :: part src)) curBase edgeBase mem' ∧
      (∀ a, ¬ ((curBase ≤ a ∧ a < curBase + N) ∨
          (edgeBase ≤ a ∧ a < edgeBase + csrOffset targetAdj N)) → mem' a = mem a) := by
  have hsrc_lt := src.isLt
  have hcur_eq := hp.2.1 src
  have hoff_src := csrOffset_succ targetAdj hsrc_lt
  have hoff_le_N := csrOffset_mono targetAdj (by omega : src.val + 1 ≤ N)
  set c := mem (curBase + src.val) - 1
  set mem₁ := Function.update mem (curBase + src.val) c
  set mem' := Function.update mem₁ (edgeBase + c) dst.val
  have hc_pos : 1 ≤ mem (curBase + src.val) := by omega
  have hc_low : csrOffset targetAdj src.val ≤ c := by omega
  have hc_high : c < csrOffset targetAdj (src.val + 1) := by omega
  have hc_lt_N : c < csrOffset targetAdj N := lt_of_lt_of_le hc_high hoff_le_N
  refine ⟨⟨fun u => ?_, fun u => ?_, fun u k hk => ?_⟩, fun a ha => ?_⟩
  · by_cases hu : u = src
    · subst hu; simp [hroom]
    · simp [Function.update_of_ne hu, hp.1 u]
  · have hm_ne : edgeBase + c ≠ curBase + u.val := by have := u.isLt; omega
    rw [show mem' (curBase + u.val) = mem₁ (curBase + u.val) from
      Function.update_of_ne hm_ne.symm _ _]
    by_cases hu : u = src
    · subst hu
      rw [Function.update_self, show mem₁ (curBase + src.val) = c from Function.update_self _ _ _,
        List.length_cons]
      omega
    · have hne : curBase + u.val ≠ curBase + src.val := fun h => hu (Fin.ext (by omega))
      rw [Function.update_of_ne hu,
        show mem₁ (curBase + u.val) = mem (curBase + u.val) from Function.update_of_ne hne _ _]
      exact hp.2.1 u
  · by_cases hu : u = src
    · subst hu
      have hlen_upd : (Function.update part src (dst :: part src) src).length =
          (part src).length + 1 := by simp
      have hm_cur : mem' (curBase + src.val) = c := by
        change Function.update mem₁ (edgeBase + c) dst.val (curBase + src.val) = c
        rw [Function.update_of_ne (by omega)]
        exact Function.update_self _ _ _
      rw [hm_cur]
      have hget_upd : ∀ j (hj : j < (Function.update part src (dst :: part src) src).length),
          (Function.update part src (dst :: part src) src)[j] =
            (dst :: part src)[j]'(by simpa [hlen_upd] using hj) := by
        intro j hj
        simp
      rw [hget_upd k hk]
      cases k with
      | zero =>
        change Function.update mem₁ (edgeBase + c) dst.val (edgeBase + c + 0) = dst.val
        rw [Nat.add_zero, Function.update_self]
      | succ k' =>
        have hk' : k' < (part src).length := by omega
        have hidx : edgeBase + c + (k' + 1) = edgeBase + mem (curBase + src.val) + k' := by omega
        change Function.update mem₁ (edgeBase + c) dst.val (edgeBase + c + (k' + 1)) =
          ((part src)[k']).val
        rw [hidx, Function.update_of_ne (by omega)]
        change Function.update mem (curBase + src.val) c (edgeBase + mem (curBase + src.val) + k') =
          ((part src)[k']).val
        rw [Function.update_of_ne (by omega)]
        exact hp.2.2 src k' hk'
    · have hget_upd : ∀ j (hj : j < (Function.update part src (dst :: part src) u).length),
          (Function.update part src (dst :: part src) u)[j] =
            (part u)[j]'(by simpa [Function.update_of_ne hu] using hj) := by
        intro j hj
        simp [Function.update_of_ne hu]
      rw [hget_upd k hk]
      have hk_u : k < (part u).length := by simpa [Function.update_of_ne hu] using hk
      have hne_c : curBase + u.val ≠ curBase + src.val := fun h => hu (Fin.ext (by omega))
      have hm_cur : mem' (curBase + u.val) = mem (curBase + u.val) := by
        change Function.update mem₁ (edgeBase + c) dst.val (curBase + u.val) = mem (curBase + u.val)
        rw [Function.update_of_ne (by have := u.isLt; omega)]
        exact Function.update_of_ne hne_c _ _
      rw [hm_cur]
      have hu_cur := hp.2.1 u
      have hu_len := hp.1 u
      have hu_off := csrOffset_succ targetAdj u.isLt
      have hq_low : csrOffset targetAdj u.val ≤ mem (curBase + u.val) + k := by omega
      have hq_high : mem (curBase + u.val) + k < csrOffset targetAdj (u.val + 1) := by omega
      have hne_edge : mem (curBase + u.val) + k ≠ c :=
        csrOffset_disjoint targetAdj hu hq_low hq_high hc_low hc_high
      have hq_lt_N : mem (curBase + u.val) + k < csrOffset targetAdj N :=
        lt_of_lt_of_le hq_high (csrOffset_mono targetAdj (by omega : u.val + 1 ≤ N))
      change Function.update mem₁ (edgeBase + c) dst.val (edgeBase + mem (curBase + u.val) + k) = _
      rw [Function.update_of_ne (by omega)]
      change Function.update mem (curBase + src.val) c (edgeBase + mem (curBase + u.val) + k) = _
      rw [Function.update_of_ne (by omega)]
      exact hp.2.2 u k hk_u
  · change Function.update (Function.update mem (curBase + src.val) c) (edgeBase + c) dst.val a =
      mem a
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

private theorem backfillStepCode_spec {N w : ℕ}
    (targetAdj part : Fin N → List (Fin N))
    (curBase edgeBase Mc : ℕ)
    (hdisj : edgeBase + Mc ≤ curBase)
    (hmc : csrOffset targetAdj N ≤ Mc)
    (hfit : Fits w (curBase + N + Mc + 1))
    (src dst : Fin N) (hroom : (part src).length + 1 ≤ (targetAdj src).length)
    {x : Data 28} (hc1 : x.regs cOne = 1)
    (hcurB : x.regs curB = curBase) (hedgeB : x.regs edgeB = edgeBase)
    (hsrc : x.regs vReg = src.val) (hdst : x.regs uReg = dst.val)
    (hp : PartialCSRAt targetAdj part curBase edgeBase x.mem) :
    ∃ y, ExecWithin w backfillStepCode x y 6 ∧
      PartialCSRAt targetAdj (Function.update part src (dst :: part src)) curBase edgeBase y.mem ∧
      (∀ a, ¬ ((curBase ≤ a ∧ a < curBase + N) ∨
          (edgeBase ≤ a ∧ a < edgeBase + csrOffset targetAdj N)) → y.mem a = x.mem a) ∧
      (∀ r : Fin 28, r ≠ addr → r ≠ jEndReg → y.regs r = x.regs r) := by
  have hsrc_lt := src.isLt
  have hcur_eq := hp.2.1 src
  have hoff_src := csrOffset_succ targetAdj hsrc_lt
  have hoff_le_N := csrOffset_mono targetAdj (by omega : src.val + 1 ≤ N)
  set c := x.mem (curBase + src.val) - 1
  have hc_pos : 1 ≤ x.mem (curBase + src.val) := by omega
  have hc_lt_N : c < csrOffset targetAdj N :=
    lt_of_lt_of_le (by omega : c < csrOffset targetAdj (src.val + 1)) hoff_le_N
  have hf_caddr : Fits w (curBase + src.val) := hfit.of_le (by omega)
  have hf_eaddr : Fits w (edgeBase + c) := hfit.of_le (by omega)
  have hstep := partialCSRAt_step targetAdj part curBase edgeBase Mc hdisj hmc src dst hroom
    x.mem hp
  let BfPost (y : Data 28) : Prop :=
    PartialCSRAt targetAdj (Function.update part src (dst :: part src)) curBase edgeBase y.mem ∧
      (∀ a, ¬ ((curBase ≤ a ∧ a < curBase + N) ∨
          (edgeBase ≤ a ∧ a < edgeBase + csrOffset targetAdj N)) → y.mem a = x.mem a) ∧
      (∀ r : Fin 28, r ≠ addr → r ≠ jEndReg → y.regs r = x.regs r)
  change ∃ y, ExecWithin w backfillStepCode x y 6 ∧ BfPost y
  unfold backfillStepCode
  wram_exec [hc1, hcurB, hedgeB, hsrc, hdst, hf_caddr, hf_eaddr]
  refine ⟨?_, fun a ha => ?_, fun r h1 h2 => ?_⟩
  · wram_simp; exact hstep.1
  · wram_simp; exact hstep.2 a ha
  · wram_simp; fin_cases r <;> simp_all

/-! ### Implication-graph CSR construction (`O(n + |φ|)`) -/

private theorem length_le_foldl_addClauseEdges {V : Type*} [DecidableEq V] :
    ∀ (cs : CNF V) (adj : Literal V → List (Literal V)) (w : Literal V),
      (adj w).length ≤ (cs.foldl addClauseEdges adj w).length
  | [], adj, w => le_rfl
  | c :: cs, adj, w => by
    have h1 : (adj w).length ≤ (addClauseEdges adj c w).length := by
      rcases c with _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩
      · exact le_rfl
      · dsimp only [addClauseEdges]
        by_cases h : w = a.negate <;> simp [h]
      · dsimp only [addClauseEdges]
        by_cases h2 : w = b.negate
        · subst h2
          by_cases h1 : b.negate = a.negate <;> simp [h1]
        · by_cases h1 : w = a.negate <;> simp [h2, h1]
      · exact le_rfl
    exact h1.trans (length_le_foldl_addClauseEdges cs (addClauseEdges adj c) w)

private theorem csrOffset_adjFin_le (G : Instance) :
    csrOffset G.adjFin (2 * G.n) ≤ 2 * G.φ.length := by
  rw [csrOffset_eq_outDegreeSum, outDegreeSum, ← Fin.sum_univ_def]
  have heq : (∑ u : Fin (2 * G.n), (G.adjFin u).length) =
      ∑ ℓ : Literal (Fin G.n), (implicationAdj G.φ ℓ).length := by
    refine Fintype.sum_equiv (litEquiv G.n).symm _ _ fun u => ?_
    simp [Instance.adjFin, mapAdj]
  rw [heq]
  exact sum_length_implicationAdj_le G.φ

private theorem mapAdj_addClauseEdges_one {n : ℕ} (g : Literal (Fin n) → List (Literal (Fin n)))
    (a : Literal (Fin n)) :
    mapAdj (litEquiv n) (addClauseEdges g [a]) =
      Function.update (mapAdj (litEquiv n) g) (litEquiv n a.negate)
        (litEquiv n a :: mapAdj (litEquiv n) g (litEquiv n a.negate)) :=
  (mapAdj_update_cons (litEquiv n) g a.negate a).symm

private theorem mapAdj_addClauseEdges_two {n : ℕ} (g : Literal (Fin n) → List (Literal (Fin n)))
    (a b : Literal (Fin n)) :
    mapAdj (litEquiv n) (addClauseEdges g [a, b]) =
      let p₁ := Function.update (mapAdj (litEquiv n) g) (litEquiv n a.negate)
        (litEquiv n b :: mapAdj (litEquiv n) g (litEquiv n a.negate))
      Function.update p₁ (litEquiv n b.negate) (litEquiv n a :: p₁ (litEquiv n b.negate)) := by
  dsimp only [addClauseEdges]
  rw [← mapAdj_update_cons, ← mapAdj_update_cons]

private def implDegBody : Code .standard 28 := ram[
  jReg ← *pReg;
  pReg ← pReg + cOne; uReg ← *pReg;
  if jReg = cOne then [
    vReg ← uReg ^^^ cOne;
    ⟪incCurCode⟫;
    pReg ← pReg + cOne ]
  else [
    pReg ← pReg + cOne; oldFinReg ← *pReg;
    vReg ← uReg ^^^ cOne;
    ⟪incCurCode⟫;
    vReg ← oldFinReg ^^^ cOne;
    ⟪incCurCode⟫;
    pReg ← pReg + cOne ];
  iReg ← iReg + cOne ]

private def implFillBody : Code .standard 28 := ram[
  jReg ← *pReg;
  pReg ← pReg + cOne; oldFinReg ← *pReg;
  if jReg = cOne then [
    vReg ← oldFinReg ^^^ cOne; uReg ← oldFinReg;
    ⟪backfillStepCode⟫;
    pReg ← pReg + cOne ]
  else [
    pReg ← pReg + cOne; jReg ← *pReg;
    vReg ← oldFinReg ^^^ cOne; uReg ← jReg;
    ⟪backfillStepCode⟫;
    vReg ← jReg ^^^ cOne; uReg ← oldFinReg;
    ⟪backfillStepCode⟫;
    pReg ← pReg + cOne ];
  iReg ← iReg + cOne ]

private theorem implDegLoop_spec (G : Instance) {w : ℕ} (hfit : Fits w G.wordBound) :
    ∀ (cs : CNF (Fin G.n)) (g : Literal (Fin G.n) → List (Literal (Fin G.n)))
      (idx p : ℕ) (x : Data 28),
      (∀ c ∈ cs, 1 ≤ c.length ∧ c.length ≤ 2) →
      G.φ = [] ∨ cs.foldl addClauseEdges g = implicationAdj G.φ →
      idx + cs.length = G.φ.length →
      p + (cs.flatMap (encodeClauseBy Fin.val)).length = G.encode.length + 1 →
      ClauseMemAt x.mem p cs →
      (∀ u : Fin (2 * G.n), x.mem (kCurAddr G.workBase (2 * G.n) (2 * G.φ.length) + u.val) =
        (mapAdj (litEquiv G.n) g u).length) →
      x.regs cOne = 1 → x.regs mClauses = G.φ.length →
      x.regs curB = kCurAddr G.workBase (2 * G.n) (2 * G.φ.length) →
      x.regs iReg = idx → x.regs pReg = p →
      ∃ y, ExecWithin w (.loop (.lt iReg mClauses) implDegBody) x y (18 * cs.length + 2) ∧
        (∀ u : Fin (2 * G.n), y.mem (kCurAddr G.workBase (2 * G.n) (2 * G.φ.length) + u.val) =
          (mapAdj (litEquiv G.n) (cs.foldl addClauseEdges g) u).length) ∧
        (∀ a, ¬ (kCurAddr G.workBase (2 * G.n) (2 * G.φ.length) ≤ a ∧
            a < kCurAddr G.workBase (2 * G.n) (2 * G.φ.length) + 2 * G.n) → y.mem a = x.mem a) ∧
        (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r)
  | [], g, idx, _, x, _, _, hidx, _, _, hdeg, _, hm, _, hi, _ => by
    simp only [List.length_nil] at hidx
    have hend : ¬ (Cond.lt iReg mClauses).Holds x := by
      change ¬ x.regs iReg < x.regs mClauses
      omega
    refine ⟨x, ⟨2, by omega, Exec.loop_exit hend⟩,
      hdeg, fun _ _ => rfl, fun _ _ => rfl⟩
  | c :: cs, g, idx, p, x, hcs, htarget, hidx, hp, hcm, hdeg, hc1, hm, hcur, hi, hpR => by
    have hc := hcs c List.mem_cons_self
    have hrest : ∀ c' ∈ cs, 1 ≤ c'.length ∧ c'.length ≤ 2 :=
      fun c' hc' => hcs c' (List.mem_cons_of_mem c hc')
    set curBase := kCurAddr G.workBase (2 * G.n) (2 * G.φ.length)
    have hfit_cur : Fits w (curBase + 2 * G.n + 2 * G.φ.length + 1) :=
      G.fits_of_le hfit (by
        simp only [curBase, kCurAddr, Instance.workBase, Instance.outAddrBase,
          G.encode_length, Instance.wordBound]
        omega)
    have hp_lt_cur : p + c.length + 1 ≤ curBase := by
      simp only [curBase, kCurAddr, Instance.workBase, Instance.outAddrBase]
      omega
    obtain ⟨hlen_p, hlit_p, hcm_rest⟩ := clauseMemAt_cons hcm
    have hflat_cons : ((c :: cs).flatMap (encodeClauseBy Fin.val)).length =
        c.length + 1 + (cs.flatMap (encodeClauseBy Fin.val)).length := by
      simp [List.flatMap_cons, length_encodeClauseBy, Nat.add_assoc]
    have hbound_imp : ∀ w_u : Fin (2 * G.n), (G.adjFin w_u).length ≤ 2 * G.φ.length := by
      intro w_u
      have h1 := csrOffset_succ G.adjFin w_u.isLt
      have h2 := csrOffset_mono G.adjFin (by omega : w_u.val + 1 ≤ 2 * G.n)
      have h3 := csrOffset_adjFin_le G
      simp only [Fin.eta] at h1
      omega
    have htarget' : cs.foldl addClauseEdges (addClauseEdges g c) = implicationAdj G.φ := by
      rcases htarget with hnil | hfold
      · simp [hnil] at hidx
      · simpa using hfold
    let DegStepPost (x₁ : Data 28) : Prop :=
      (∀ u : Fin (2 * G.n), x₁.mem (curBase + u.val) =
          (mapAdj (litEquiv G.n) (addClauseEdges g c) u).length) ∧
        (∀ a, ¬ (curBase ≤ a ∧ a < curBase + 2 * G.n) → x₁.mem a = x.mem a) ∧
        x₁.regs iReg = idx + 1 ∧ x₁.regs pReg = p + 1 + c.length ∧
        (∀ r : Fin 28, r.val < 18 → x₁.regs r = x.regs r)
    have hstep : ∃ x₁, ExecWithin w implDegBody x x₁ 16 ∧ DegStepPost x₁ := by
      rcases c with _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩
      · simp at hc
      · have hmem_a : x.mem (p + 1) = litCodeBy Fin.val a := by simpa using hlit_p 0 (by simp)
        have hxor_a : litCodeBy Fin.val a ^^^ 1 = (litEquiv G.n a.negate).val :=
          litCodeBy_xor_one Fin.val a
        have hroom_a : (mapAdj (litEquiv G.n) g (litEquiv G.n a.negate)).length + 1 ≤
            2 * G.φ.length := by
          have hle := length_le_foldl_addClauseEdges cs (addClauseEdges g [a]) a.negate
          rw [htarget'] at hle
          have hfin := hbound_imp (litEquiv G.n a.negate)
          simp only [Instance.adjFin, mapAdj, Equiv.symm_apply_apply, List.length_map,
            addClauseEdges, Function.update_self, List.length_cons] at hle hfin ⊢
          omega
        have hf_p1 : Fits w (p + 1) :=
          G.fits_of_le hfit (by have := G.encode_length; unfold Instance.wordBound; omega)
        have hf_p2 : Fits w (p + 1 + 1) :=
          G.fits_of_le hfit (by have := G.encode_length; unfold Instance.wordBound; omega)
        have hf_na : Fits w (litCodeBy Fin.val a ^^^ 1) :=
          G.fits_of_le hfit (by
            rw [hxor_a]
            have := (litEquiv G.n a.negate).isLt
            unfold Instance.wordBound
            omega)
        have hf_i1 : Fits w (idx + 1) := G.fits_of_le hfit (by unfold Instance.wordBound; omega)
        let st_pre := ((x.set jReg 1).set pReg (p + 1)).set uReg (litCodeBy Fin.val a)
        let st_v := st_pre.set vReg (litCodeBy Fin.val a ^^^ 1)
        obtain ⟨y₁, hy₁_ex, hy₁_deg, hy₁_out, hy₁_fr⟩ :=
          incCurCode_spec (N := 2 * G.n) curBase (2 * G.φ.length) hfit_cur
            (fun u => (mapAdj (litEquiv G.n) g u).length) (litEquiv G.n a.negate) hroom_a
            (x := st_v) (by simp [st_v, st_pre, hc1]) (by simp [st_v, st_pre, hcur])
            (by simp [st_v, hxor_a]) (by simp [st_v, st_pre]; exact hdeg)
        unfold implDegBody
        wram_exec [hc1, hpR, hi, hlen_p, hmem_a, hf_p1, hf_na]
        refine WP.of_execWithin hy₁_ex ?_
        have hy₁_1 : y₁.regs cOne = 1 :=
          (hy₁_fr cOne (by decide) (by decide)).trans (by simp [st_v, st_pre, hc1])
        have hy₁_p : y₁.regs pReg = p + 1 :=
          (hy₁_fr pReg (by decide) (by decide)).trans (by simp [st_v, st_pre])
        have hy₁_i : y₁.regs iReg = idx :=
          (hy₁_fr iReg (by decide) (by decide)).trans (by simp [st_v, st_pre, hi])
        wram_exec [hy₁_1, hy₁_p, hy₁_i, hf_p2, hf_i1]
        dsimp only [DegStepPost]
        refine ⟨fun u => ?_, fun addr_a ha => ?_, by wram_simp, by wram_simp; omega,
          fun r hr => ?_⟩
        · wram_simp
          rw [hy₁_deg u, mapAdj_addClauseEdges_one]
          by_cases hu : u = litEquiv G.n a.negate <;> simp [hu]
        · wram_simp; exact hy₁_out addr_a ha
        · wram_simp
          have := hy₁_fr r (by omega) (by omega)
          have hlt18 : r ≠ jReg ∧ r ≠ pReg ∧ r ≠ uReg ∧ r ≠ vReg := by
            fin_cases r <;> simp_all
          simpa [st_v, st_pre, hlt18.1, hlt18.2.1, hlt18.2.2.1, hlt18.2.2.2] using this
      · have hmem_a : x.mem (p + 1) = litCodeBy Fin.val a := by simpa using hlit_p 0 (by simp)
        have hmem_b : x.mem (p + 1 + 1) = litCodeBy Fin.val b := by
          simpa [Nat.add_assoc] using hlit_p 1 (by simp)
        have hxor_a : litCodeBy Fin.val a ^^^ 1 = (litEquiv G.n a.negate).val :=
          litCodeBy_xor_one Fin.val a
        have hxor_b : litCodeBy Fin.val b ^^^ 1 = (litEquiv G.n b.negate).val :=
          litCodeBy_xor_one Fin.val b
        let g₁ := Function.update g a.negate (b :: g a.negate)
        have hg₁_map : mapAdj (litEquiv G.n) g₁ =
            Function.update (mapAdj (litEquiv G.n) g) (litEquiv G.n a.negate)
              (litEquiv G.n b :: mapAdj (litEquiv G.n) g (litEquiv G.n a.negate)) :=
          (mapAdj_update_cons (litEquiv G.n) g a.negate b).symm
        have hroom_a : (mapAdj (litEquiv G.n) g (litEquiv G.n a.negate)).length + 1 ≤
            2 * G.φ.length := by
          have hle1 : (g₁ a.negate).length ≤ (addClauseEdges g [a, b] a.negate).length := by
            dsimp only [addClauseEdges, g₁]
            by_cases hab : a.negate = b.negate <;> simp [hab]
          have hle2 := length_le_foldl_addClauseEdges cs (addClauseEdges g [a, b]) a.negate
          rw [htarget'] at hle2
          have hfin := hbound_imp (litEquiv G.n a.negate)
          simp only [Instance.adjFin, mapAdj, Equiv.symm_apply_apply, List.length_map, g₁,
            Function.update_self, List.length_cons] at hle1 hle2 hfin ⊢
          omega
        have hroom_b : (mapAdj (litEquiv G.n) g₁ (litEquiv G.n b.negate)).length + 1 ≤
            2 * G.φ.length := by
          have hle2 := length_le_foldl_addClauseEdges cs (addClauseEdges g [a, b]) b.negate
          rw [htarget'] at hle2
          have hfin := hbound_imp (litEquiv G.n b.negate)
          simp only [Instance.adjFin, mapAdj, Equiv.symm_apply_apply, List.length_map,
            addClauseEdges, Function.update_self, List.length_cons] at hle2 hfin ⊢
          exact hle2.trans hfin
        have hf_p1 : Fits w (p + 1) :=
          G.fits_of_le hfit (by have := G.encode_length; unfold Instance.wordBound; omega)
        have hf_p2 : Fits w (p + 1 + 1) :=
          G.fits_of_le hfit (by have := G.encode_length; unfold Instance.wordBound; omega)
        have hf_p3 : Fits w (p + 1 + 1 + 1) :=
          G.fits_of_le hfit (by have := G.encode_length; unfold Instance.wordBound; omega)
        have hf_na : Fits w (litCodeBy Fin.val a ^^^ 1) :=
          G.fits_of_le hfit (by
            rw [hxor_a]
            have := (litEquiv G.n a.negate).isLt
            unfold Instance.wordBound
            omega)
        have hf_nb : Fits w (litCodeBy Fin.val b ^^^ 1) :=
          G.fits_of_le hfit (by
            rw [hxor_b]
            have := (litEquiv G.n b.negate).isLt
            unfold Instance.wordBound
            omega)
        have hf_i1 : Fits w (idx + 1) := G.fits_of_le hfit (by unfold Instance.wordBound; omega)
        let st_v1 := (((((x.set jReg 2).set pReg (p + 1)).set uReg (litCodeBy Fin.val a)).set
          pReg (p + 1 + 1)).set oldFinReg (litCodeBy Fin.val b)).set
          vReg (litCodeBy Fin.val a ^^^ 1)
        obtain ⟨y₁, hy₁_ex, hy₁_deg, hy₁_out, hy₁_fr⟩ :=
          incCurCode_spec (N := 2 * G.n) curBase (2 * G.φ.length) hfit_cur
            (fun u => (mapAdj (litEquiv G.n) g u).length) (litEquiv G.n a.negate) hroom_a
            (x := st_v1) (by dsimp only [st_v1]; wram_simp; exact hc1)
            (by dsimp only [st_v1]; wram_simp; exact hcur)
            (by dsimp only [st_v1]; wram_simp; exact hxor_a)
            (by dsimp only [st_v1]; exact hdeg)
        have hy₁_deg' : ∀ u : Fin (2 * G.n), y₁.mem (curBase + u.val) =
            (mapAdj (litEquiv G.n) g₁ u).length := by
          intro u
          rw [hy₁_deg u, hg₁_map]
          by_cases hu : u = litEquiv G.n a.negate <;> simp [hu]
        let st_v2 := y₁.set vReg (litCodeBy Fin.val b ^^^ 1)
        have hy₁_1 : y₁.regs cOne = 1 :=
          (hy₁_fr cOne (by decide) (by decide)).trans (by dsimp only [st_v1]; wram_simp; exact hc1)
        have hy₁_cur : y₁.regs curB = curBase :=
          (hy₁_fr curB (by decide) (by decide)).trans (by dsimp only [st_v1]; wram_simp; exact hcur)
        have hy₁_b : y₁.regs oldFinReg = litCodeBy Fin.val b :=
          (hy₁_fr oldFinReg (by decide) (by decide)).trans (by dsimp only [st_v1]; wram_simp)
        obtain ⟨y₂, hy₂_ex, hy₂_deg, hy₂_out, hy₂_fr⟩ :=
          incCurCode_spec (N := 2 * G.n) curBase (2 * G.φ.length) hfit_cur
            (fun u => (mapAdj (litEquiv G.n) g₁ u).length) (litEquiv G.n b.negate) hroom_b
            (x := st_v2) (by dsimp only [st_v2]; wram_simp; exact hy₁_1)
            (by dsimp only [st_v2]; wram_simp; exact hy₁_cur)
            (by dsimp only [st_v2]; wram_simp; exact hxor_b)
            (by dsimp only [st_v2]; exact hy₁_deg')
        unfold implDegBody
        wram_exec [hc1, hpR, hi, hlen_p, hmem_a, hmem_b, hf_p1, hf_p2, hf_na]
        refine WP.of_execWithin hy₁_ex ?_
        wram_exec [hy₁_1, hy₁_b, hf_nb]
        refine WP.of_execWithin hy₂_ex ?_
        have hy₂_1 : y₂.regs cOne = 1 :=
          (hy₂_fr cOne (by decide) (by decide)).trans (by simp [st_v2, hy₁_1])
        have hy₂_p : y₂.regs pReg = p + 1 + 1 :=
          (hy₂_fr pReg (by decide) (by decide)).trans
            ((hy₁_fr pReg (by decide) (by decide)).trans (by simp [st_v1]))
        have hy₂_i : y₂.regs iReg = idx :=
          (hy₂_fr iReg (by decide) (by decide)).trans
            ((hy₁_fr iReg (by decide) (by decide)).trans (by simp [st_v1, hi]))
        wram_exec [hy₂_1, hy₂_p, hy₂_i, hf_p3, hf_i1]
        dsimp only [DegStepPost]
        refine ⟨fun u => ?_, fun addr_a ha => ?_, by wram_simp, by wram_simp; omega,
          fun r hr => ?_⟩
        · wram_simp
          rw [hy₂_deg u, mapAdj_addClauseEdges_two, ← hg₁_map]
          by_cases hu : u = litEquiv G.n b.negate <;> simp [hu]
        · wram_simp; exact (hy₂_out addr_a ha).trans (hy₁_out addr_a ha)
        · wram_simp
          have h2 := hy₂_fr r (by omega) (by omega)
          have h1 := hy₁_fr r (by omega) (by omega)
          have hlt18 : r ≠ jReg ∧ r ≠ pReg ∧ r ≠ uReg ∧ r ≠ vReg ∧ r ≠ oldFinReg := by
            fin_cases r <;> simp_all
          rw [h2]
          simpa [st_v2, st_v1, hlt18.1, hlt18.2.1, hlt18.2.2.1, hlt18.2.2.2.1,
            hlt18.2.2.2.2] using h1
      · simp at hc
    obtain ⟨x₁, hx₁_ex, hx₁_deg, hx₁_out, hx₁_i, hx₁_p, hx₁_fr⟩ := hstep
    have hcm_x₁ : ClauseMemAt x₁.mem (p + 1 + c.length) cs := by
      intro k hk
      have hk_bound : p + 1 + c.length + k < curBase := by
        rw [hflat_cons] at hp
        simp only [curBase, kCurAddr, Instance.workBase, Instance.outAddrBase]
        omega
      rw [hx₁_out _ (by omega)]
      exact hcm_rest k hk
    have hlt : (Cond.lt iReg mClauses).Holds x := by
      change x.regs iReg < x.regs mClauses
      simp only [List.length_cons] at hidx
      omega
    obtain ⟨y, hy_ex, hy_deg, hy_out, hy_fr⟩ := implDegLoop_spec G hfit cs
      (addClauseEdges g c) (idx + 1) (p + 1 + c.length) x₁ hrest (.inr htarget')
      (by simp only [List.length_cons] at hidx; omega)
      (by rw [hflat_cons] at hp; omega) hcm_x₁ hx₁_deg
      ((hx₁_fr cOne (by decide)).trans hc1)
      ((hx₁_fr mClauses (by decide)).trans hm)
      ((hx₁_fr curB (by decide)).trans hcur)
      hx₁_i hx₁_p
    obtain ⟨t₁, ht₁, he₁⟩ := hx₁_ex
    obtain ⟨t₂, ht₂, he₂⟩ := hy_ex
    refine ⟨y, ⟨t₁ + t₂ + 2, by simp only [List.length_cons]; omega,
        Exec.loop_iter hlt he₁ he₂⟩, hy_deg,
      fun a ha => (hy_out a ha).trans (hx₁_out a ha),
      fun r hr => (hy_fr r hr).trans (hx₁_fr r hr)⟩

private theorem implFillLoop_spec (G : Instance) {w : ℕ} (hfit : Fits w G.wordBound) :
    ∀ (cs : CNF (Fin G.n)) (g : Literal (Fin G.n) → List (Literal (Fin G.n)))
      (idx p : ℕ) (x : Data 28),
      (∀ c ∈ cs, 1 ≤ c.length ∧ c.length ≤ 2) →
      G.φ = [] ∨ cs.foldl addClauseEdges g = implicationAdj G.φ →
      idx + cs.length = G.φ.length →
      p + (cs.flatMap (encodeClauseBy Fin.val)).length = G.encode.length + 1 →
      ClauseMemAt x.mem p cs →
      PartialCSRAt G.adjFin (mapAdj (litEquiv G.n) g)
        (kCurAddr G.workBase (2 * G.n) (2 * G.φ.length))
        (kEdgeAddr G.workBase (2 * G.n)) x.mem →
      x.regs cOne = 1 → x.regs mClauses = G.φ.length →
      x.regs curB = kCurAddr G.workBase (2 * G.n) (2 * G.φ.length) →
      x.regs edgeB = kEdgeAddr G.workBase (2 * G.n) →
      x.regs iReg = idx → x.regs pReg = p →
      ∃ y, ExecWithin w (.loop (.lt iReg mClauses) implFillBody) x y (28 * cs.length + 2) ∧
        PartialCSRAt G.adjFin (mapAdj (litEquiv G.n) (cs.foldl addClauseEdges g))
          (kCurAddr G.workBase (2 * G.n) (2 * G.φ.length))
          (kEdgeAddr G.workBase (2 * G.n)) y.mem ∧
        (∀ a, ¬ ((kCurAddr G.workBase (2 * G.n) (2 * G.φ.length) ≤ a ∧
              a < kCurAddr G.workBase (2 * G.n) (2 * G.φ.length) + 2 * G.n) ∨
            (kEdgeAddr G.workBase (2 * G.n) ≤ a ∧
              a < kEdgeAddr G.workBase (2 * G.n) + csrOffset G.adjFin (2 * G.n))) →
          y.mem a = x.mem a) ∧
        (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r)
  | [], g, idx, _, x, _, _, hidx, _, _, hpcsr, _, hm, _, _, hi, _ => by
    simp only [List.length_nil] at hidx
    have hend : ¬ (Cond.lt iReg mClauses).Holds x := by
      change ¬ x.regs iReg < x.regs mClauses
      omega
    refine ⟨x, ⟨2, by omega, Exec.loop_exit hend⟩,
      hpcsr, fun _ _ => rfl, fun _ _ => rfl⟩
  | c :: cs, g, idx, p, x, hcs, htarget, hidx, hp, hcm, hpcsr, hc1, hm, hcur, hedge, hi, hpR => by
    have hc := hcs c List.mem_cons_self
    have hrest : ∀ c' ∈ cs, 1 ≤ c'.length ∧ c'.length ≤ 2 :=
      fun c' hc' => hcs c' (List.mem_cons_of_mem c hc')
    set curBase := kCurAddr G.workBase (2 * G.n) (2 * G.φ.length)
    set edgeBase := kEdgeAddr G.workBase (2 * G.n)
    have hdisj : edgeBase + 2 * G.φ.length ≤ curBase := by
      simp only [edgeBase, curBase, kEdgeAddr, kCurAddr]; omega
    have hmc := csrOffset_adjFin_le G
    have hfit_bf : Fits w (curBase + 2 * G.n + 2 * G.φ.length + 1) :=
      G.fits_of_le hfit (by
        simp only [curBase, kCurAddr, Instance.workBase, Instance.outAddrBase,
          G.encode_length, Instance.wordBound]
        omega)
    obtain ⟨hlen_p, hlit_p, hcm_rest⟩ := clauseMemAt_cons hcm
    have hflat_cons : ((c :: cs).flatMap (encodeClauseBy Fin.val)).length =
        c.length + 1 + (cs.flatMap (encodeClauseBy Fin.val)).length := by
      simp [List.flatMap_cons, length_encodeClauseBy, Nat.add_assoc]
    have htarget' : cs.foldl addClauseEdges (addClauseEdges g c) = implicationAdj G.φ := by
      rcases htarget with hnil | hfold
      · simp [hnil] at hidx
      · simpa using hfold
    let FillStepPost (x₁ : Data 28) : Prop :=
      PartialCSRAt G.adjFin (mapAdj (litEquiv G.n) (addClauseEdges g c))
          curBase edgeBase x₁.mem ∧
        (∀ a, ¬ ((curBase ≤ a ∧ a < curBase + 2 * G.n) ∨
            (edgeBase ≤ a ∧ a < edgeBase + csrOffset G.adjFin (2 * G.n))) → x₁.mem a = x.mem a) ∧
        x₁.regs iReg = idx + 1 ∧ x₁.regs pReg = p + 1 + c.length ∧
        (∀ r : Fin 28, r.val < 18 → x₁.regs r = x.regs r)
    have hstep : ∃ x₁, ExecWithin w implFillBody x x₁ 26 ∧ FillStepPost x₁ := by
      rcases c with _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩
      · simp at hc
      · have hmem_a : x.mem (p + 1) = litCodeBy Fin.val a := by simpa using hlit_p 0 (by simp)
        have hxor_a : litCodeBy Fin.val a ^^^ 1 = (litEquiv G.n a.negate).val :=
          litCodeBy_xor_one Fin.val a
        have hroom_a : (mapAdj (litEquiv G.n) g (litEquiv G.n a.negate)).length + 1 ≤
            (G.adjFin (litEquiv G.n a.negate)).length := by
          have hle := length_le_foldl_addClauseEdges cs (addClauseEdges g [a]) a.negate
          rw [htarget'] at hle
          simpa [Instance.adjFin, mapAdj, addClauseEdges] using hle
        have hf_p1 : Fits w (p + 1) :=
          G.fits_of_le hfit (by have := G.encode_length; unfold Instance.wordBound; omega)
        have hf_p2 : Fits w (p + 1 + 1) :=
          G.fits_of_le hfit (by have := G.encode_length; unfold Instance.wordBound; omega)
        have hf_na : Fits w (litCodeBy Fin.val a ^^^ 1) :=
          G.fits_of_le hfit (by
            rw [hxor_a]
            have := (litEquiv G.n a.negate).isLt
            unfold Instance.wordBound
            omega)
        have hf_i1 : Fits w (idx + 1) := G.fits_of_le hfit (by unfold Instance.wordBound; omega)
        let st_v := ((((x.set jReg 1).set pReg (p + 1)).set oldFinReg (litCodeBy Fin.val a)).set
          vReg (litCodeBy Fin.val a ^^^ 1)).set uReg (litCodeBy Fin.val a)
        obtain ⟨y₁, hy₁_ex, hy₁_p, hy₁_out, hy₁_fr⟩ :=
          backfillStepCode_spec G.adjFin (mapAdj (litEquiv G.n) g) curBase edgeBase
            (2 * G.φ.length) hdisj hmc hfit_bf (litEquiv G.n a.negate) (litEquiv G.n a) hroom_a
            (x := st_v) (by dsimp only [st_v]; wram_simp; exact hc1)
            (by dsimp only [st_v]; wram_simp; exact hcur)
            (by dsimp only [st_v]; wram_simp; exact hedge)
            (by dsimp only [st_v]; wram_simp; exact hxor_a)
            (by dsimp only [st_v, litEquiv]; wram_simp; rfl)
            (by dsimp only [st_v]; exact hpcsr)
        have hlen_1 : x.mem p = 1 := by simpa using hlen_p
        unfold implFillBody
        wram_exec [hc1, hpR, hi, hlen_1, hmem_a, hf_p1, hf_na]
        refine WP.of_execWithin hy₁_ex ?_
        have hy₁_1 : y₁.regs cOne = 1 :=
          (hy₁_fr cOne (by decide) (by decide)).trans (by dsimp only [st_v]; wram_simp; exact hc1)
        have hy₁_pr : y₁.regs pReg = p + 1 :=
          (hy₁_fr pReg (by decide) (by decide)).trans (by dsimp only [st_v]; wram_simp)
        have hy₁_i : y₁.regs iReg = idx :=
          (hy₁_fr iReg (by decide) (by decide)).trans (by dsimp only [st_v]; wram_simp; exact hi)
        wram_exec [hy₁_1, hy₁_pr, hy₁_i, hf_p2, hf_i1]
        dsimp only [FillStepPost]
        refine ⟨?_, fun addr_a ha => ?_, by wram_simp, by wram_simp; omega, fun r hr => ?_⟩
        · try wram_simp
          rwa [mapAdj_addClauseEdges_one]
        · try wram_simp
          exact hy₁_out addr_a ha
        · wram_simp
          have h1 := hy₁_fr r (by omega) (by omega)
          have hlt18 : r ≠ jReg ∧ r ≠ pReg ∧ r ≠ oldFinReg ∧ r ≠ vReg ∧ r ≠ uReg := by
            fin_cases r <;> simp_all
          simpa [st_v, hlt18.1, hlt18.2.1, hlt18.2.2.1, hlt18.2.2.2.1, hlt18.2.2.2.2] using h1
      · have hmem_a : x.mem (p + 1) = litCodeBy Fin.val a := by simpa using hlit_p 0 (by simp)
        have hmem_b : x.mem (p + 1 + 1) = litCodeBy Fin.val b := by
          simpa [Nat.add_assoc] using hlit_p 1 (by simp)
        have hlen_2 : x.mem p = 2 := by simpa using hlen_p
        have hxor_a : litCodeBy Fin.val a ^^^ 1 = (litEquiv G.n a.negate).val :=
          litCodeBy_xor_one Fin.val a
        have hxor_b : litCodeBy Fin.val b ^^^ 1 = (litEquiv G.n b.negate).val :=
          litCodeBy_xor_one Fin.val b
        let g₁ := Function.update g a.negate (b :: g a.negate)
        have hg₁_map : mapAdj (litEquiv G.n) g₁ =
            Function.update (mapAdj (litEquiv G.n) g) (litEquiv G.n a.negate)
              (litEquiv G.n b :: mapAdj (litEquiv G.n) g (litEquiv G.n a.negate)) :=
          (mapAdj_update_cons (litEquiv G.n) g a.negate b).symm
        have hroom_a : (mapAdj (litEquiv G.n) g (litEquiv G.n a.negate)).length + 1 ≤
            (G.adjFin (litEquiv G.n a.negate)).length := by
          have hle1 : (g₁ a.negate).length ≤ (addClauseEdges g [a, b] a.negate).length := by
            dsimp only [addClauseEdges, g₁]
            by_cases hab : a.negate = b.negate <;> simp [hab]
          have hle2 := length_le_foldl_addClauseEdges cs (addClauseEdges g [a, b]) a.negate
          rw [htarget'] at hle2
          have htot := hle1.trans hle2
          simpa [Instance.adjFin, mapAdj, g₁] using htot
        have hroom_b : (mapAdj (litEquiv G.n) g₁ (litEquiv G.n b.negate)).length + 1 ≤
            (G.adjFin (litEquiv G.n b.negate)).length := by
          have hle2 := length_le_foldl_addClauseEdges cs (addClauseEdges g [a, b]) b.negate
          rw [htarget'] at hle2
          simpa [Instance.adjFin, mapAdj, addClauseEdges, g₁] using hle2
        have hf_p1 : Fits w (p + 1) :=
          G.fits_of_le hfit (by have := G.encode_length; unfold Instance.wordBound; omega)
        have hf_p2 : Fits w (p + 1 + 1) :=
          G.fits_of_le hfit (by have := G.encode_length; unfold Instance.wordBound; omega)
        have hf_p3 : Fits w (p + 1 + 1 + 1) :=
          G.fits_of_le hfit (by have := G.encode_length; unfold Instance.wordBound; omega)
        have hf_na : Fits w (litCodeBy Fin.val a ^^^ 1) :=
          G.fits_of_le hfit (by
            rw [hxor_a]
            have := (litEquiv G.n a.negate).isLt
            unfold Instance.wordBound
            omega)
        have hf_nb : Fits w (litCodeBy Fin.val b ^^^ 1) :=
          G.fits_of_le hfit (by
            rw [hxor_b]
            have := (litEquiv G.n b.negate).isLt
            unfold Instance.wordBound
            omega)
        have hf_i1 : Fits w (idx + 1) := G.fits_of_le hfit (by unfold Instance.wordBound; omega)
        let st_v1 := ((((((x.set jReg 2).set pReg (p + 1)).set oldFinReg (litCodeBy Fin.val a)).set
          pReg (p + 1 + 1)).set jReg (litCodeBy Fin.val b)).set
          vReg (litCodeBy Fin.val a ^^^ 1)).set uReg (litCodeBy Fin.val b)
        obtain ⟨y₁, hy₁_ex, hy₁_p, hy₁_out, hy₁_fr⟩ :=
          backfillStepCode_spec G.adjFin (mapAdj (litEquiv G.n) g) curBase edgeBase
            (2 * G.φ.length) hdisj hmc hfit_bf (litEquiv G.n a.negate) (litEquiv G.n b) hroom_a
            (x := st_v1) (by dsimp only [st_v1]; wram_simp; exact hc1)
            (by dsimp only [st_v1]; wram_simp; exact hcur)
            (by dsimp only [st_v1]; wram_simp; exact hedge)
            (by dsimp only [st_v1]; wram_simp; exact hxor_a)
            (by dsimp only [st_v1, litEquiv]; wram_simp; rfl)
            (by dsimp only [st_v1]; exact hpcsr)
        have hy₁_p' : PartialCSRAt G.adjFin (mapAdj (litEquiv G.n) g₁) curBase edgeBase y₁.mem := by
          rwa [hg₁_map]
        have hy₁_1 : y₁.regs cOne = 1 :=
          (hy₁_fr cOne (by decide) (by decide)).trans (by dsimp only [st_v1]; wram_simp; exact hc1)
        have hy₁_cur : y₁.regs curB = curBase :=
          (hy₁_fr curB (by decide) (by decide)).trans (by dsimp only [st_v1]; wram_simp; exact hcur)
        have hy₁_edge : y₁.regs edgeB = edgeBase :=
          (hy₁_fr edgeB (by decide) (by decide)).trans (by dsimp only [st_v1]; wram_simp; exact hedge)
        have hy₁_a : y₁.regs oldFinReg = litCodeBy Fin.val a :=
          (hy₁_fr oldFinReg (by decide) (by decide)).trans (by dsimp only [st_v1]; wram_simp)
        have hy₁_b : y₁.regs jReg = litCodeBy Fin.val b :=
          (hy₁_fr jReg (by decide) (by decide)).trans (by dsimp only [st_v1]; wram_simp)
        let st_v2 := (y₁.set vReg (litCodeBy Fin.val b ^^^ 1)).set uReg (litCodeBy Fin.val a)
        obtain ⟨y₂, hy₂_ex, hy₂_p, hy₂_out, hy₂_fr⟩ :=
          backfillStepCode_spec G.adjFin (mapAdj (litEquiv G.n) g₁) curBase edgeBase
            (2 * G.φ.length) hdisj hmc hfit_bf (litEquiv G.n b.negate) (litEquiv G.n a) hroom_b
            (x := st_v2) (by dsimp only [st_v2]; wram_simp; exact hy₁_1)
            (by dsimp only [st_v2]; wram_simp; exact hy₁_cur)
            (by dsimp only [st_v2]; wram_simp; exact hy₁_edge)
            (by dsimp only [st_v2]; wram_simp; exact hxor_b)
            (by dsimp only [st_v2, litEquiv]; wram_simp; rfl)
            (by dsimp only [st_v2]; exact hy₁_p')
        unfold implFillBody
        wram_exec [hc1, hpR, hi, hlen_2, hmem_a, hmem_b, hf_p1, hf_p2, hf_na]
        refine WP.of_execWithin hy₁_ex ?_
        wram_exec [hy₁_1, hy₁_a, hy₁_b, hf_nb]
        refine WP.of_execWithin hy₂_ex ?_
        have hy₂_1 : y₂.regs cOne = 1 :=
          (hy₂_fr cOne (by decide) (by decide)).trans (by dsimp only [st_v2]; wram_simp; exact hy₁_1)
        have hy₂_pr : y₂.regs pReg = p + 1 + 1 :=
          (hy₂_fr pReg (by decide) (by decide)).trans
            ((hy₁_fr pReg (by decide) (by decide)).trans (by dsimp only [st_v1]; wram_simp))
        have hy₂_i : y₂.regs iReg = idx :=
          (hy₂_fr iReg (by decide) (by decide)).trans
            ((hy₁_fr iReg (by decide) (by decide)).trans (by dsimp only [st_v1]; wram_simp; exact hi))
        wram_exec [hy₂_1, hy₂_pr, hy₂_i, hf_p3, hf_i1]
        dsimp only [FillStepPost]
        refine ⟨?_, fun addr_a ha => ?_, by wram_simp, by wram_simp; omega, fun r hr => ?_⟩
        · try wram_simp
          rwa [mapAdj_addClauseEdges_two, ← hg₁_map]
        · try wram_simp
          exact (hy₂_out addr_a ha).trans (hy₁_out addr_a ha)
        · wram_simp
          have h2 := hy₂_fr r (by omega) (by omega)
          have h1 := hy₁_fr r (by omega) (by omega)
          have hlt18 : r ≠ jReg ∧ r ≠ pReg ∧ r ≠ oldFinReg ∧ r ≠ vReg ∧ r ≠ uReg := by
            fin_cases r <;> simp_all
          rw [h2]
          simpa [st_v2, st_v1, hlt18.1, hlt18.2.1, hlt18.2.2.1, hlt18.2.2.2.1,
            hlt18.2.2.2.2] using h1
      · simp at hc
    obtain ⟨x₁, hx₁_ex, hx₁_p_csr, hx₁_out, hx₁_i, hx₁_p, hx₁_fr⟩ := hstep
    have hcm_x₁ : ClauseMemAt x₁.mem (p + 1 + c.length) cs := by
      intro k hk
      have hk_bound : p + 1 + c.length + k < G.workBase := by
        rw [hflat_cons] at hp
        simp only [Instance.workBase, Instance.outAddrBase]
        omega
      rw [hx₁_out _ (by simp only [curBase, edgeBase, kCurAddr, kEdgeAddr]; omega)]
      exact hcm_rest k hk
    have hlt : (Cond.lt iReg mClauses).Holds x := by
      change x.regs iReg < x.regs mClauses
      simp only [List.length_cons] at hidx
      omega
    obtain ⟨y, hy_ex, hy_p_csr, hy_out, hy_fr⟩ := implFillLoop_spec G hfit cs
      (addClauseEdges g c) (idx + 1) (p + 1 + c.length) x₁ hrest (.inr htarget')
      (by simp only [List.length_cons] at hidx; omega)
      (by rw [hflat_cons] at hp; omega) hcm_x₁ hx₁_p_csr
      ((hx₁_fr cOne (by decide)).trans hc1)
      ((hx₁_fr mClauses (by decide)).trans hm)
      ((hx₁_fr curB (by decide)).trans hcur)
      ((hx₁_fr edgeB (by decide)).trans hedge)
      hx₁_i hx₁_p
    obtain ⟨t₁, ht₁, he₁⟩ := hx₁_ex
    obtain ⟨t₂, ht₂, he₂⟩ := hy_ex
    refine ⟨y, ⟨t₁ + t₂ + 2, by simp only [List.length_cons]; omega,
        Exec.loop_iter hlt he₁ he₂⟩, hy_p_csr,
      fun a ha => (hy_out a ha).trans (hx₁_out a ha),
      fun r hr => (hy_fr r hr).trans (hx₁_fr r hr)⟩

/-! ### Explicit-stack iterative CSR depth-first search (`O(N + M)`) -/

private def foldEmpty {V : Type*} [DecidableEq V] (adj : V → List V) (k : ℕ)
    (es : List V) (vis : Finset V) : Cslib.Algorithms.Lean.DFS.State V :=
  es.foldl (fun t v => visit adj k v t) ⟨vis, []⟩

private theorem foldl_visit_append {V : Type*} [DecidableEq V] (adj : V → List V) (k : ℕ) :
    ∀ (es : List V) (vis : Finset V) (fin : List V),
      es.foldl (fun t v => visit adj k v t) ⟨vis, fin⟩ =
        ⟨(foldEmpty adj k es vis).visited, (foldEmpty adj k es vis).finished ++ fin⟩
  | [], _, _ => rfl
  | v :: es, vis, fin => by
    dsimp only [foldEmpty, List.foldl_cons]
    rw [visit_eq_of_nil k v vis fin, foldl_visit_append adj k es _ _,
      foldl_visit_append adj k es _ _, List.append_assoc]

private theorem foldEmpty_cons {V : Type*} [DecidableEq V] (adj : V → List V) (k : ℕ)
    (v : V) (es : List V) (vis : Finset V) :
    foldEmpty adj k (v :: es) vis =
      let s₁ := visit adj k v ⟨vis, []⟩
      let s₂ := foldEmpty adj k es s₁.visited
      ⟨s₂.visited, s₂.finished ++ s₁.finished⟩ := by
  dsimp only [foldEmpty, List.foldl_cons]
  exact foldl_visit_append adj k es (visit adj k v ⟨vis, []⟩).visited
    (visit adj k v ⟨vis, []⟩).finished

private theorem visit_eq_foldEmpty {V : Type*} [DecidableEq V] {adj : V → List V} {k : ℕ}
    {u : V} {vis : Finset V} (hu : u ∉ vis) :
    visit adj (k + 1) u ⟨vis, []⟩ =
      let s := foldEmpty adj k (adj u) (insert u vis)
      ⟨s.visited, u :: s.finished⟩ := by
  simp [visit, hu, foldEmpty]

private theorem visit_nil_struct {V : Type*} [DecidableEq V] (adj : V → List V) :
    ∀ (k : ℕ) (u : V) (vis : Finset V),
      let s := visit adj k u ⟨vis, []⟩
      s.finished.Nodup ∧ (∀ x ∈ s.finished, x ∉ vis) ∧
        (∀ x, x ∈ s.visited ↔ x ∈ vis ∨ x ∈ s.finished)
  | 0, _, vis => ⟨List.nodup_nil, by simp [visit], by simp [visit]⟩
  | k + 1, u, vis => by
    by_cases hu : u ∈ vis
    · simp [visit, hu]
    · have hfold : ∀ (es : List V) (v₀ : Finset V),
          let t := foldEmpty adj k es v₀
          t.finished.Nodup ∧ (∀ x ∈ t.finished, x ∉ v₀) ∧
            (∀ x, x ∈ t.visited ↔ x ∈ v₀ ∨ x ∈ t.finished) := by
        intro es
        induction es with
        | nil => intro v₀; exact ⟨List.nodup_nil, by simp [foldEmpty], by simp [foldEmpty]⟩
        | cons w es ih =>
          intro v₀
          obtain ⟨hnd₁, hdis₁, hvis₁⟩ := visit_nil_struct adj k w v₀
          obtain ⟨hnd₂, hdis₂, hvis₂⟩ := ih (visit adj k w ⟨v₀, []⟩).visited
          rw [foldEmpty_cons]
          dsimp only
          refine ⟨List.nodup_append.2 ⟨hnd₂, hnd₁, fun x hx₂ y hx₁ hxy => ?_⟩,
            fun x hx => ?_, fun x => ?_⟩
          · subst hxy
            exact hdis₂ x hx₂ ((hvis₁ x).2 (.inr hx₁))
          · rcases List.mem_append.1 hx with hx₂ | hx₁
            · exact fun hv => hdis₂ x hx₂ ((hvis₁ x).2 (.inl hv))
            · exact hdis₁ x hx₁
          · rw [hvis₂ x, hvis₁ x, List.mem_append]
            tauto
      obtain ⟨hnd, hdis, hvis⟩ := hfold (adj u) (insert u vis)
      rw [visit_eq_foldEmpty hu]
      dsimp only
      refine ⟨List.nodup_cons.2 ⟨fun hmem => hdis u hmem (Finset.mem_insert_self u vis), hnd⟩,
        fun x hx => ?_, fun x => ?_⟩
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact hu
        · exact fun hv => hdis x hx (Finset.mem_insert_of_mem hv)
      · rw [hvis x, Finset.mem_insert, List.mem_cons]
        tauto

private theorem card_visit_nil {V : Type*} [DecidableEq V] (adj : V → List V)
    (k : ℕ) (u : V) (vis : Finset V) :
    (visit adj k u ⟨vis, []⟩).visited.card =
      vis.card + (visit adj k u ⟨vis, []⟩).finished.length := by
  obtain ⟨hnd, hdis, hvis⟩ := visit_nil_struct adj k u vis
  have hdisj : Disjoint vis (visit adj k u ⟨vis, []⟩).finished.toFinset :=
    Finset.disjoint_right.2 fun x hx => hdis x (List.mem_toFinset.1 hx)
  have hunion : (visit adj k u ⟨vis, []⟩).visited =
      vis ∪ (visit adj k u ⟨vis, []⟩).finished.toFinset := by
    ext x
    simp [hvis x]
  rw [hunion, Finset.card_union_of_disjoint hdisj, List.toFinset_card_of_nodup hnd]

private theorem outDegreeSum_append_local {V : Type*} (g : V → List V) (a b : List V) :
    outDegreeSum g (a ++ b) = outDegreeSum g a + outDegreeSum g b := by
  simp [outDegreeSum, List.map_append, List.sum_append]

private def VisAt {N : ℕ} (vis : Finset (Fin N)) (visAddr : ℕ) (mem : ℕ → ℕ) : Prop :=
  ∀ w : Fin N, mem (visAddr + w.val) = (decide (w ∈ vis)).toNat

private structure DfsRegs (offAddr edgeAddr visAddr finAddr stkAddr : ℕ) (x : Data 28) : Prop where
  czero : x.regs cZero = 0
  cone : x.regs cOne = 1
  cthree : x.regs cThree = 3
  hoff : x.regs offB = offAddr
  hedge : x.regs edgeB = edgeAddr
  hvis : x.regs visB = visAddr
  hfin : x.regs finB = finAddr
  hstk : x.regs stkB = stkAddr

private theorem dfsRegs_of_frame {offAddr edgeAddr visAddr finAddr stkAddr : ℕ} {x y : Data 28}
    (hx : DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x)
    (hfr : ∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r) :
    DfsRegs offAddr edgeAddr visAddr finAddr stkAddr y :=
  { czero := (hfr cZero (by decide)).trans hx.czero
    cone := (hfr cOne (by decide)).trans hx.cone
    cthree := (hfr cThree (by decide)).trans hx.cthree
    hoff := (hfr offB (by decide)).trans hx.hoff
    hedge := (hfr edgeB (by decide)).trans hx.hedge
    hvis := (hfr visB (by decide)).trans hx.hvis
    hfin := (hfr finB (by decide)).trans hx.hfin
    hstk := (hfr stkB (by decide)).trans hx.hstk }

private def dfsPushRoot : Code .standard 28 := ram[
  *addr ← cOne;
  addr ← offB + uReg; jReg ← *addr;
  addr ← addr + cOne; jEndReg ← *addr;
  *stkB ← uReg;
  addr ← stkB + cOne; *addr ← jReg;
  addr ← addr + cOne; *addr ← jEndReg;
  pReg ← cOne ]

private def dfsStepBody : Code .standard 28 := ram[
  vReg ← pReg - cOne;
  addr ← cThree * vReg; addr ← stkB + addr;
  uReg ← *addr;
  addr ← addr + cOne; jReg ← *addr;
  addr ← addr + cOne; jEndReg ← *addr;
  if jReg < jEndReg then [
    addr ← cThree * vReg; addr ← stkB + addr; addr ← addr + cOne;
    jEndReg ← jReg + cOne; *addr ← jEndReg;
    addr ← edgeB + jReg; vReg ← *addr;
    addr ← visB + vReg; jReg ← *addr;
    if jReg = cZero then [
      *addr ← cOne;
      addr ← offB + vReg; jReg ← *addr;
      addr ← addr + cOne; jEndReg ← *addr;
      addr ← cThree * pReg; addr ← stkB + addr;
      *addr ← vReg;
      addr ← addr + cOne; *addr ← jReg;
      addr ← addr + cOne; *addr ← jEndReg;
      pReg ← pReg + cOne ]
    else [ pReg ← pReg ] ]
  else [
    pReg ← vReg;
    addr ← finB + finCnt; *addr ← uReg;
    finCnt ← finCnt + cOne ] ]

private def dfsLoop : Code .standard 28 :=
  .loop (.lt cZero pReg) dfsStepBody

private def visitRootCode : Code .standard 28 := ram[
  addr ← visB + uReg; jReg ← *addr;
  if jReg = cZero then [
    ⟪dfsPushRoot.seq dfsLoop⟫ ]
  else [ pReg ← cZero ] ]

private def dfsFrameTime {N : ℕ} (adj : Fin N → List (Fin N)) (es new : List (Fin N)) : ℕ :=
  20 + 36 * es.length + 60 * new.length + 36 * outDegreeSum adj new

private theorem card_lt_of_notMem {N : ℕ} {vis : Finset (Fin N)} {v : Fin N} (hv : v ∉ vis) :
    vis.card < N := by
  have hlt : vis.card < (Finset.univ : Finset (Fin N)).card :=
    Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.2
        ⟨Finset.subset_univ _, fun h => hv (h ▸ Finset.mem_univ v)⟩)
  simpa using hlt

private theorem visAt_insert {N : ℕ} {vis : Finset (Fin N)} {visAddr : ℕ} {mem : ℕ → ℕ}
    (h : VisAt vis visAddr mem) (v : Fin N) :
    VisAt (insert v vis) visAddr (Function.update mem (visAddr + v.val) 1) := by
  intro w
  by_cases hw : w = v
  · subst hw; simp
  · have hne : visAddr + w.val ≠ visAddr + v.val := fun heq => hw (Fin.ext (by omega))
    rw [Function.update_of_ne hne, h w]
    simp [hw]

private theorem dfsLoop_cps {N w : ℕ} (adj : Fin N → List (Fin N))
    (offAddr edgeAddr visAddr finAddr stkAddr Mc : ℕ)
    (hdisj1 : offAddr + N + 1 ≤ visAddr)
    (hdisj2 : edgeAddr + Mc ≤ visAddr)
    (hdisj3 : visAddr + N ≤ finAddr)
    (hdisj4 : finAddr + N ≤ stkAddr)
    (hmc : csrOffset adj N ≤ Mc)
    (hfit : Fits w (stkAddr + 3 * N + Mc + 4)) :
    ∀ (k : ℕ),
      ∀ (u : Fin N) (es : List (Fin N)) (idx d F₀ T_cont : ℕ)
        (vis : Finset (Fin N)) (x : Data 28) (Q : Data 28 → Prop)
        (_ : idx + es.length = (adj u).length),
        (∀ q (hq : q < es.length),
          (adj u)[idx + q]'(by omega) = es[q]) →
        N - vis.card ≤ k →
        F₀ + d + 1 + (N - vis.card) ≤ N →
        DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x →
        CSRAt adj offAddr edgeAddr x.mem →
        VisAt vis visAddr x.mem →
        x.regs pReg = d + 1 →
        x.regs finCnt = F₀ →
        x.mem (stkAddr + 3 * d) = u.val →
        x.mem (stkAddr + 3 * d + 1) = csrOffset adj u.val + idx →
        x.mem (stkAddr + 3 * d + 2) = csrOffset adj (u.val + 1) →
        (∀ y : Data 28,
          let s := foldEmpty adj k es vis
          DfsRegs offAddr edgeAddr visAddr finAddr stkAddr y →
          CSRAt adj offAddr edgeAddr y.mem →
          VisAt s.visited visAddr y.mem →
          y.regs pReg = d →
          y.regs finCnt = F₀ + s.finished.length + 1 →
          (∀ q (hq : q < s.finished.reverse.length),
            y.mem (finAddr + F₀ + q) = (s.finished.reverse[q]).val) →
          y.mem (finAddr + F₀ + s.finished.length) = u.val →
          (∀ a, ¬ ((visAddr ≤ a ∧ a < visAddr + N) ∨
              (finAddr + F₀ ≤ a ∧ a < finAddr + F₀ + s.finished.length + 1) ∨
              (stkAddr + 3 * d ≤ a ∧ a < stkAddr + 3 * N)) → y.mem a = x.mem a) →
          (∀ r : Fin 28, (r.val < 19 ∨ r = compIdxReg ∨ r = oldFinReg) → y.regs r = x.regs r) →
          ∃ z, ExecWithin w dfsLoop y z T_cont ∧ Q z) →
        ∃ z, ExecWithin w dfsLoop x z
          (dfsFrameTime adj es (foldEmpty adj k es vis).finished + T_cont) ∧ Q z := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih_k =>
    intro u es
    induction es with
    | nil =>
      intro idx d F₀ T_cont vis x Q hidx _ _ hcons hregs hcsr hvis hp hfc hstk0 hstk1 hstk2 hcont
      simp only [List.length_nil, Nat.add_zero] at hidx
      have hoff_u := csrOffset_succ adj u.isLt
      simp only [Fin.eta] at hoff_u
      have hjeq : csrOffset adj u.val + idx = csrOffset adj (u.val + 1) := by omega
      have hstk1' : x.mem (stkAddr + 3 * d + 1) = csrOffset adj (u.val + 1) := hstk1.trans hjeq
      have hu_lt := u.isLt
      have hf_3d : Fits w (3 * d) := hfit.of_le (by omega)
      have hf_s0 : Fits w (stkAddr + 3 * d) := hfit.of_le (by omega)
      have hf_s1 : Fits w (stkAddr + 3 * d + 1) := hfit.of_le (by omega)
      have hf_s2 : Fits w (stkAddr + 3 * d + 1 + 1) := hfit.of_le (by omega)
      have hf_fin : Fits w (finAddr + F₀) := hfit.of_le (by omega)
      have hf_fc1 : Fits w (F₀ + 1) := hfit.of_le (by omega)
      let PopPost (x₁ : Data 28) : Prop :=
        DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x₁ ∧
          CSRAt adj offAddr edgeAddr x₁.mem ∧
          VisAt vis visAddr x₁.mem ∧
          x₁.regs pReg = d ∧
          x₁.regs finCnt = F₀ + 1 ∧
          x₁.mem (finAddr + F₀) = u.val ∧
          (∀ a, ¬ (a = finAddr + F₀) → x₁.mem a = x.mem a) ∧
          (∀ r : Fin 28, (r.val < 19 ∨ r = compIdxReg ∨ r = oldFinReg) → x₁.regs r = x.regs r)
      have hstep : ∃ x₁, ExecWithin w dfsStepBody x x₁ 16 ∧ PopPost x₁ := by
        change ∃ x₁, ExecWithin w dfsStepBody x x₁ 16 ∧ PopPost x₁
        have hstk2' : x.mem (stkAddr + 3 * d + 1 + 1) = csrOffset adj (u.val + 1) := by
          simpa [Nat.add_assoc] using hstk2
        unfold dfsStepBody
        wram_exec [hregs.czero, hregs.cone, hregs.cthree, hregs.hoff, hregs.hedge, hregs.hvis,
          hregs.hfin, hregs.hstk, hp, hfc, hstk0, hstk1', hstk2',
          hf_3d, hf_s0, hf_s1, hf_s2, hf_fin, hf_fc1]
        dsimp only [PopPost]
        refine ⟨?_, ?_, ?_, by try wram_simp, by wram_simp, ?_, fun a ha => ?_, fun r hr => ?_⟩
        · refine dfsRegs_of_frame hregs fun r hr => ?_
          wram_simp; fin_cases r <;> simp_all
        · wram_simp
          refine ⟨fun u' hu' => ?_, fun u' q hq => ?_⟩
          · rw [Function.update_of_ne (by omega)]; exact hcsr.1 u' hu'
          · have hq_lt : csrOffset adj u'.val + q < csrOffset adj N := by
              have h1 := csrOffset_succ adj u'.isLt
              simp only [Fin.eta] at h1
              have h2 := csrOffset_mono adj (by omega : u'.val + 1 ≤ N)
              omega
            rw [Function.update_of_ne (by omega)]; exact hcsr.2 u' q hq
        · intro w_v; wram_simp
          rw [Function.update_of_ne (by have := w_v.isLt; omega)]; exact hvis w_v
        · wram_simp; exact Function.update_self _ _ _
        · wram_simp; exact Function.update_of_ne ha _ _
        · wram_simp; fin_cases r <;> simp_all
      obtain ⟨x₁, ⟨t₁, ht₁, he₁⟩, hx₁_r, hx₁_csr, hx₁_vis, hx₁_p, hx₁_fc, hx₁_fin0, hx₁_out,
        hx₁_fr⟩ := hstep
      obtain ⟨z, ⟨t₂, ht₂, he₂⟩, hQz⟩ := hcont x₁ hx₁_r hx₁_csr hx₁_vis hx₁_p
        (by simpa [foldEmpty] using hx₁_fc)
        (fun q hq => by simp [foldEmpty] at hq)
        (by simpa [foldEmpty] using hx₁_fin0)
        (fun a ha => hx₁_out a (by simp only [foldEmpty, List.length_nil] at ha; omega))
        hx₁_fr
      have hlt : (Cond.lt cZero pReg).Holds x := by
        change x.regs cZero < x.regs pReg; omega
      exact ⟨z, ⟨t₁ + t₂ + 2, by simp only [dfsFrameTime, foldEmpty, List.length_nil, outDegreeSum,
        List.map_nil, List.sum_nil]; omega, Exec.loop_iter hlt he₁ he₂⟩, hQz⟩
    | cons v es' ih_es =>
      intro idx d F₀ T_cont vis x Q hidx hes hk hcons hregs hcsr hvis hp hfc hstk0 hstk1 hstk2
        hcont
      simp only [List.length_cons] at hidx
      have hv_eq : (adj u)[idx]'(by omega) = v := by simpa using hes 0 (by simp)
      have hoff_u := csrOffset_succ adj u.isLt
      simp only [Fin.eta] at hoff_u
      set j := csrOffset adj u.val + idx
      have hj_lt_end : j < csrOffset adj (u.val + 1) := by omega
      have hj_lt_N : j < csrOffset adj N :=
        lt_of_lt_of_le hj_lt_end (csrOffset_mono adj (by omega : u.val + 1 ≤ N))
      have hedge_j : x.mem (edgeAddr + j) = v.val := by
        have := hcsr.2 u idx (by omega)
        rwa [hv_eq] at this
      have hvis_v : x.mem (visAddr + v.val) = (decide (v ∈ vis)).toNat := hvis v
      have hu_lt := u.isLt
      have hv_lt := v.isLt
      have hf_3d : Fits w (3 * d) := hfit.of_le (by omega)
      have hf_s0 : Fits w (stkAddr + 3 * d) := hfit.of_le (by omega)
      have hf_s1 : Fits w (stkAddr + 3 * d + 1) := hfit.of_le (by omega)
      have hf_s2 : Fits w (stkAddr + 3 * d + 1 + 1) := hfit.of_le (by omega)
      have hf_j1 : Fits w (j + 1) := hfit.of_le (by omega)
      have hf_ej : Fits w (edgeAddr + j) := hfit.of_le (by omega)
      have hf_vv : Fits w (visAddr + v.val) := hfit.of_le (by omega)
      have hstk2' : x.mem (stkAddr + 3 * d + 1 + 1) = csrOffset adj (u.val + 1) := by
        simpa [Nat.add_assoc] using hstk2
      by_cases hmem : v ∈ vis
      · -- Case 1: `v ∈ vis`
        have hvis_v1 : x.mem (visAddr + v.val) = 1 := by simpa [hmem] using hvis_v
        have hvisit_v : visit adj k v ⟨vis, []⟩ = ⟨vis, []⟩ := by
          cases k with
          | zero => rfl
          | succ k' => exact visit_of_mem hmem
        have hfold_eq : foldEmpty adj k (v :: es') vis = foldEmpty adj k es' vis := by
          rw [foldEmpty_cons, hvisit_v]
          simp
        let SkipPost (x₁ : Data 28) : Prop :=
          DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x₁ ∧
            CSRAt adj offAddr edgeAddr x₁.mem ∧
            VisAt vis visAddr x₁.mem ∧
            x₁.regs pReg = d + 1 ∧
            x₁.regs finCnt = F₀ ∧
            x₁.mem (stkAddr + 3 * d) = u.val ∧
            x₁.mem (stkAddr + 3 * d + 1) = csrOffset adj u.val + (idx + 1) ∧
            x₁.mem (stkAddr + 3 * d + 2) = csrOffset adj (u.val + 1) ∧
            (∀ a, a ≠ stkAddr + 3 * d + 1 → x₁.mem a = x.mem a) ∧
            (∀ r : Fin 28, (r.val < 19 ∨ r = compIdxReg ∨ r = oldFinReg) → x₁.regs r = x.regs r)
        have hstep : ∃ x₁, ExecWithin w dfsStepBody x x₁ 24 ∧ SkipPost x₁ := by
          change ∃ x₁, ExecWithin w dfsStepBody x x₁ 24 ∧ SkipPost x₁
          unfold dfsStepBody
          wram_exec [hregs.czero, hregs.cone, hregs.cthree, hregs.hoff, hregs.hedge, hregs.hvis,
            hregs.hfin, hregs.hstk, hp, hfc, hstk0, hstk1, hstk2', hedge_j, hvis_v1, hj_lt_end,
            hf_3d, hf_s0, hf_s1, hf_s2, hf_j1, hf_ej, hf_vv]
          dsimp only [SkipPost]
          refine ⟨?_, ?_, ?_, by try wram_simp, by wram_simp; exact hfc, ?_, ?_, ?_,
            fun a ha => ?_, fun r hr => ?_⟩
          · refine dfsRegs_of_frame hregs fun r hr => ?_
            wram_simp; fin_cases r <;> simp_all
          · wram_simp
            refine ⟨fun u' hu' => ?_, fun u' q hq => ?_⟩
            · rw [Function.update_of_ne (by omega)]; exact hcsr.1 u' hu'
            · have hq_lt : csrOffset adj u'.val + q < csrOffset adj N := by
                have h1 := csrOffset_succ adj u'.isLt
                simp only [Fin.eta] at h1
                have h2 := csrOffset_mono adj (by omega : u'.val + 1 ≤ N)
                omega
              rw [Function.update_of_ne (by omega)]; exact hcsr.2 u' q hq
          · intro w_v; wram_simp
            rw [Function.update_of_ne (by have := w_v.isLt; omega)]; exact hvis w_v
          · wram_simp; rw [Function.update_of_ne (by omega)]; exact hstk0
          · wram_simp; rw [Function.update_self]; omega
          · wram_simp; rw [Function.update_of_ne (by omega)]; exact hstk2
          · wram_simp; exact Function.update_of_ne ha _ _
          · wram_simp; fin_cases r <;> simp_all
        obtain ⟨x₁, ⟨t₁, ht₁, he₁⟩, hx₁_r, hx₁_csr, hx₁_vis, hx₁_p, hx₁_fc, hx₁_s0, hx₁_s1,
          hx₁_s2, hx₁_out, hx₁_fr⟩ := hstep
        have hes' : ∀ q (hq : q < es'.length), (adj u)[idx + 1 + q]'(by omega) = es'[q] := by
          intro q hq
          have h := hes (q + 1) (by simp; omega)
          rw [show idx + (q + 1) = idx + 1 + q by omega] at h
          simpa using h
        obtain ⟨z, ⟨t₂, ht₂, he₂⟩, hQz⟩ := ih_es (idx + 1) d F₀ T_cont vis x₁ Q (by omega) hes'
          hk hcons hx₁_r hx₁_csr hx₁_vis hx₁_p hx₁_fc hx₁_s0 hx₁_s1 hx₁_s2
          (fun y hy_r hy_csr hy_vis hy_p hy_fc hy_fin hy_u hy_out hy_fr => by
            rw [hfold_eq] at hcont
            exact hcont y hy_r hy_csr hy_vis hy_p hy_fc hy_fin hy_u
              (fun a ha => (hy_out a ha).trans (hx₁_out a (by omega)))
              (fun r hr => (hy_fr r hr).trans (hx₁_fr r hr)))
        have hlt : (Cond.lt cZero pReg).Holds x := by
          change x.regs cZero < x.regs pReg; omega
        refine ⟨z, ⟨t₁ + t₂ + 2, ?_, Exec.loop_iter hlt he₁ he₂⟩, hQz⟩
        rw [hfold_eq]
        simp only [dfsFrameTime, List.length_cons] at ht₂ ⊢
        omega
      · -- Case 2: `v ∉ vis`
        have hcard_lt : vis.card < N := card_lt_of_notMem hmem
        rcases k with _ | k'
        · omega
        have hvis_v0 : x.mem (visAddr + v.val) = 0 := by simpa [hmem] using hvis_v
        set vis₁ := insert v vis
        have hcard_vis₁ : vis₁.card = vis.card + 1 := Finset.card_insert_of_notMem hmem
        have hcard_vis₁_le : vis₁.card ≤ N := by
          have := Finset.card_le_univ vis₁; simpa using this
        have hk' : N - vis₁.card ≤ k' := by omega
        have hcons_child : F₀ + (d + 1) + 1 + (N - vis₁.card) ≤ N := by omega
        have hoff_v0 : x.mem (offAddr + v.val) = csrOffset adj v.val :=
          hcsr.1 v.val (by omega)
        have hoff_v1 : x.mem (offAddr + v.val + 1) = csrOffset adj (v.val + 1) := by
          simpa [Nat.add_assoc] using hcsr.1 (v.val + 1) (by omega)
        have hf_ov0 : Fits w (offAddr + v.val) := hfit.of_le (by omega)
        have hf_ov1 : Fits w (offAddr + v.val + 1) := hfit.of_le (by omega)
        have hf_3d1 : Fits w (3 * (d + 1)) := hfit.of_le (by omega)
        have hf_c0 : Fits w (stkAddr + 3 * (d + 1)) := hfit.of_le (by omega)
        have hf_c1 : Fits w (stkAddr + 3 * (d + 1) + 1) := hfit.of_le (by omega)
        have hf_c2 : Fits w (stkAddr + 3 * (d + 1) + 1 + 1) := hfit.of_le (by omega)
        have hf_p2 : Fits w (d + 1 + 1) := hfit.of_le (by omega)
        let PushPost (x₁ : Data 28) : Prop :=
          DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x₁ ∧
            CSRAt adj offAddr edgeAddr x₁.mem ∧
            VisAt vis₁ visAddr x₁.mem ∧
            x₁.regs pReg = (d + 1) + 1 ∧
            x₁.regs finCnt = F₀ ∧
            x₁.mem (stkAddr + 3 * d) = u.val ∧
            x₁.mem (stkAddr + 3 * d + 1) = csrOffset adj u.val + (idx + 1) ∧
            x₁.mem (stkAddr + 3 * d + 2) = csrOffset adj (u.val + 1) ∧
            x₁.mem (stkAddr + 3 * (d + 1)) = v.val ∧
            x₁.mem (stkAddr + 3 * (d + 1) + 1) = csrOffset adj v.val + 0 ∧
            x₁.mem (stkAddr + 3 * (d + 1) + 2) = csrOffset adj (v.val + 1) ∧
            (∀ a, ¬ (a = visAddr + v.val ∨
                (stkAddr + 3 * d ≤ a ∧ a < stkAddr + 3 * N)) → x₁.mem a = x.mem a) ∧
            (∀ r : Fin 28, (r.val < 19 ∨ r = compIdxReg ∨ r = oldFinReg) → x₁.regs r = x.regs r)
        have hstep : ∃ x₁, ExecWithin w dfsStepBody x x₁ 34 ∧ PushPost x₁ := by
          change ∃ x₁, ExecWithin w dfsStepBody x x₁ 34 ∧ PushPost x₁
          unfold dfsStepBody
          wram_exec [hregs.czero, hregs.cone, hregs.cthree, hregs.hoff, hregs.hedge, hregs.hvis,
            hregs.hfin, hregs.hstk, hp, hfc, hstk0, hstk1, hstk2', hedge_j, hvis_v0, hj_lt_end,
            hoff_v0, hoff_v1, hf_3d, hf_s0, hf_s1, hf_s2, hf_j1, hf_ej, hf_vv,
            hf_ov0, hf_ov1, hf_3d1, hf_c0, hf_c1, hf_c2, hf_p2]
          dsimp only [PushPost]
          refine ⟨?_, ?_, ?_, by wram_simp, by wram_simp; exact hfc,
            ?_, ?_, ?_, ?_, ?_, ?_, fun a ha => ?_, fun r hr => ?_⟩
          · refine dfsRegs_of_frame hregs fun r hr => ?_
            wram_simp; fin_cases r <;> simp_all
          · wram_simp
            refine ⟨fun u' hu' => ?_, fun u' q hq => ?_⟩
            · repeat rw [Function.update_of_ne (by omega)]
              exact hcsr.1 u' hu'
            · have hq_lt : csrOffset adj u'.val + q < csrOffset adj N := by
                have h1 := csrOffset_succ adj u'.isLt
                simp only [Fin.eta] at h1
                have h2 := csrOffset_mono adj (by omega : u'.val + 1 ≤ N)
                omega
              repeat rw [Function.update_of_ne (by omega)]
              exact hcsr.2 u' q hq
          · intro w_v; wram_simp
            have hw_lt := w_v.isLt
            repeat rw [Function.update_of_ne (by omega)]
            have hins := visAt_insert hvis v w_v
            by_cases hwv : w_v = v
            · subst hwv
              rw [Function.update_self]
              simpa [vis₁] using hins
            · have hne : visAddr + w_v.val ≠ visAddr + v.val := fun h => hwv (Fin.ext (by omega))
              rw [Function.update_of_ne hne, Function.update_of_ne (by omega)]
              simpa [vis₁, hwv] using hvis w_v
          · wram_simp; repeat rw [Function.update_of_ne (by omega)]
            exact hstk0
          · wram_simp; repeat rw [Function.update_of_ne (by omega)]
            rw [Function.update_self]; omega
          · wram_simp; repeat rw [Function.update_of_ne (by omega)]
            exact hstk2
          · wram_simp
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_self]
          · wram_simp
            rw [Function.update_of_ne (by omega), Function.update_self]; omega
          · wram_simp
            change Function.update _ (stkAddr + 3 * (d + 1) + 1 + 1) _ (stkAddr + 3 * (d + 1) + 2) = _
            rw [show stkAddr + 3 * (d + 1) + 2 = stkAddr + 3 * (d + 1) + 1 + 1 by omega,
              Function.update_self]
          · wram_simp
            repeat rw [Function.update_of_ne (by omega)]
          · wram_simp; fin_cases r <;> simp_all
        obtain ⟨x₁, ⟨t₁, ht₁, he₁⟩, hx₁_r, hx₁_csr, hx₁_vis, hx₁_p, hx₁_fc, hx₁_d0, hx₁_d1,
          hx₁_d2, hx₁_c0, hx₁_c1, hx₁_c2, hx₁_out, hx₁_fr⟩ := hstep
        set s₁ := visit adj (k' + 1) v ⟨vis, []⟩
        set s_child := foldEmpty adj k' (adj v) vis₁
        have hs₁_eq : s₁ = ⟨s_child.visited, v :: s_child.finished⟩ :=
          visit_eq_foldEmpty hmem
        set s₂ := foldEmpty adj (k' + 1) es' s₁.visited
        have hfold_cons : foldEmpty adj (k' + 1) (v :: es') vis =
            ⟨s₂.visited, s₂.finished ++ s₁.finished⟩ :=
          foldEmpty_cons adj (k' + 1) v es' vis
        have hes' : ∀ q (hq : q < es'.length), (adj u)[idx + 1 + q]'(by omega) = es'[q] := by
          intro q hq
          have h := hes (q + 1) (by simp; omega)
          rw [show idx + (q + 1) = idx + 1 + q by omega] at h
          simpa using h
        have hcard_s₁ : s₁.visited.card = vis.card + s₁.finished.length :=
          card_visit_nil adj (k' + 1) v vis
        have hcard_s₁_le : s₁.visited.card ≤ N := by
          have := Finset.card_le_univ s₁.visited; simpa using this
        have hlen_s₁ : s₁.finished.length = s_child.finished.length + 1 := by
          simp [hs₁_eq]
        have hk_s₁ : N - s₁.visited.card ≤ k' + 1 := by omega
        have hcons_after : (F₀ + s₁.finished.length) + d + 1 + (N - s₁.visited.card) ≤ N := by
          omega
        obtain ⟨z, ⟨t₂, ht₂, he₂⟩, hQz⟩ := ih_k k' (Nat.lt_succ_self k') v (adj v) 0 (d + 1) F₀
          (dfsFrameTime adj es' s₂.finished + T_cont) vis₁ x₁ Q (by simp)
          (fun q hq => by simp) hk' hcons_child hx₁_r hx₁_csr hx₁_vis hx₁_p hx₁_fc
          hx₁_c0 hx₁_c1 hx₁_c2
          (fun y₁ hy₁_r hy₁_csr hy₁_vis hy₁_p hy₁_fc hy₁_fin hy₁_v hy₁_out hy₁_fr => by
            have hy₁_vis' : VisAt s₁.visited visAddr y₁.mem := by simpa [hs₁_eq] using hy₁_vis
            have hy₁_fc' : y₁.regs finCnt = F₀ + s₁.finished.length := by
              rw [hlen_s₁]; exact hy₁_fc
            have hy₁_d0 : y₁.mem (stkAddr + 3 * d) = u.val :=
              (hy₁_out _ (by omega)).trans hx₁_d0
            have hy₁_d1 : y₁.mem (stkAddr + 3 * d + 1) = csrOffset adj u.val + (idx + 1) :=
              (hy₁_out _ (by omega)).trans hx₁_d1
            have hy₁_d2 : y₁.mem (stkAddr + 3 * d + 2) = csrOffset adj (u.val + 1) :=
              (hy₁_out _ (by omega)).trans hx₁_d2
            exact ih_es (idx + 1) d (F₀ + s₁.finished.length) T_cont s₁.visited y₁ Q
              (by omega) hes' hk_s₁ hcons_after hy₁_r hy₁_csr hy₁_vis' hy₁_p hy₁_fc'
              hy₁_d0 hy₁_d1 hy₁_d2
              (fun y₂ hy₂_r hy₂_csr hy₂_vis hy₂_p hy₂_fc hy₂_fin hy₂_u hy₂_out hy₂_fr => by
                have hy₂_vis' : VisAt (foldEmpty adj (k' + 1) (v :: es') vis).visited
                    visAddr y₂.mem := by
                  simpa [hfold_cons] using hy₂_vis
                have hy₂_fc' : y₂.regs finCnt =
                    F₀ + (foldEmpty adj (k' + 1) (v :: es') vis).finished.length + 1 := by
                  rw [hfold_cons]; dsimp only; rw [List.length_append]; omega
                have hy₂_u' : y₂.mem (finAddr + F₀ +
                    (foldEmpty adj (k' + 1) (v :: es') vis).finished.length) = u.val := by
                  rw [hfold_cons]; dsimp only; rw [List.length_append]
                  simpa [Nat.add_assoc] using hy₂_u
                have hy₂_fin_all : ∀ q (hq : q < (foldEmpty adj (k' + 1) (v :: es') vis).finished.reverse.length),
                    y₂.mem (finAddr + F₀ + q) =
                      ((foldEmpty adj (k' + 1) (v :: es') vis).finished.reverse[q]).val := by
                  intro q hq
                  have hrev : (foldEmpty adj (k' + 1) (v :: es') vis).finished.reverse =
                      s_child.finished.reverse ++ [v] ++ s₂.finished.reverse := by
                    simp [hfold_cons, hs₁_eq, List.reverse_append, List.append_assoc]
                  have hq_tot : q < s_child.finished.length + 1 + s₂.finished.length := by
                    rw [hrev] at hq
                    simpa [List.length_append] using hq
                  by_cases hq1 : q < s_child.finished.length
                  · have hpres : y₂.mem (finAddr + F₀ + q) = y₁.mem (finAddr + F₀ + q) :=
                      hy₂_out _ (by omega)
                    rw [hpres, hy₁_fin q (by simpa using hq1)]
                    congr 1
                    simp only [hrev, List.append_assoc]
                    rw [List.getElem_append_left (by simpa using hq1)]
                  · by_cases hq2 : q = s_child.finished.length
                    · subst hq2
                      have hpres : y₂.mem (finAddr + F₀ + s_child.finished.length) =
                          y₁.mem (finAddr + F₀ + s_child.finished.length) :=
                        hy₂_out _ (by omega)
                      rw [hpres, hy₁_v]
                      congr 1
                      simp [hrev]
                    · set q' := q - s₁.finished.length
                      have hq'_lt : q' < s₂.finished.reverse.length := by
                        simp only [List.length_reverse]; omega
                      have haddr_eq : finAddr + F₀ + q = finAddr + (F₀ + s₁.finished.length) + q' := by
                        omega
                      rw [haddr_eq, hy₂_fin q' hq'_lt]
                      congr 1
                      have hrev2 : (foldEmpty adj (k' + 1) (v :: es') vis).finished.reverse =
                          s₁.finished.reverse ++ s₂.finished.reverse := by
                        simp [hfold_cons]
                      simp only [hrev2]
                      have hge : s₁.finished.reverse.length ≤ q := by simp; omega
                      rw [List.getElem_append_right hge]
                      simp [q']
                exact hcont y₂ hy₂_r hy₂_csr hy₂_vis' hy₂_p hy₂_fc' hy₂_fin_all hy₂_u'
                  (fun a ha => by
                    rw [hfold_cons] at ha; dsimp only at ha
                    rw [List.length_append] at ha
                    have h2 := hy₂_out a (by omega)
                    have h1 := hy₁_out a (by omega)
                    have h0 := hx₁_out a (by have := v.isLt; omega)
                    exact h2.trans (h1.trans h0))
                  (fun r hr => (hy₂_fr r hr).trans ((hy₁_fr r hr).trans (hx₁_fr r hr)))))
        have hlt : (Cond.lt cZero pReg).Holds x := by
          change x.regs cZero < x.regs pReg; omega
        refine ⟨z, ⟨t₁ + t₂ + 2, ?_, Exec.loop_iter hlt he₁ he₂⟩, hQz⟩
        have hout_eq : outDegreeSum adj (foldEmpty adj (k' + 1) (v :: es') vis).finished =
            outDegreeSum adj s₂.finished + ((adj v).length + outDegreeSum adj s_child.finished) := by
          rw [hfold_cons, hs₁_eq]
          dsimp only
          rw [outDegreeSum_append_local]
          simp [outDegreeSum]
        have hlen_eq : (foldEmpty adj (k' + 1) (v :: es') vis).finished.length =
            s₂.finished.length + (1 + s_child.finished.length) := by
          rw [hfold_cons, hs₁_eq]; simp [Nat.add_comm]
        simp only [dfsFrameTime, List.length_cons, hout_eq, hlen_eq] at ht₂ ⊢
        omega

private theorem visitRootCode_spec {N w : ℕ} (hN : 0 < N) (adj : Fin N → List (Fin N))
    (offAddr edgeAddr visAddr finAddr stkAddr Mc : ℕ)
    (hdisj1 : offAddr + N + 1 ≤ visAddr)
    (hdisj2 : edgeAddr + Mc ≤ visAddr)
    (hdisj3 : visAddr + N ≤ finAddr)
    (hdisj4 : finAddr + N ≤ stkAddr)
    (hmc : csrOffset adj N ≤ Mc)
    (hfit : Fits w (stkAddr + 3 * N + Mc + 4))
    (r : Fin N) (F₀ : ℕ) (vis : Finset (Fin N))
    (hcons : F₀ + (N - vis.card) ≤ N)
    {x : Data 28}
    (hregs : DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x)
    (hcsr : CSRAt adj offAddr edgeAddr x.mem)
    (hvis : VisAt vis visAddr x.mem)
    (hu : x.regs uReg = r.val)
    (hfc : x.regs finCnt = F₀) :
    let s := visit adj N r ⟨vis, []⟩
    ∃ y, ExecWithin w visitRootCode x y
        (16 + 60 * s.finished.length + 36 * outDegreeSum adj s.finished) ∧
      DfsRegs offAddr edgeAddr visAddr finAddr stkAddr y ∧
      CSRAt adj offAddr edgeAddr y.mem ∧
      VisAt s.visited visAddr y.mem ∧
      y.regs finCnt = F₀ + s.finished.length ∧
      (∀ q (hq : q < s.finished.reverse.length),
        y.mem (finAddr + F₀ + q) = (s.finished.reverse[q]).val) ∧
      (∀ a, ¬ ((visAddr ≤ a ∧ a < visAddr + N) ∨
          (finAddr + F₀ ≤ a ∧ a < finAddr + F₀ + s.finished.length) ∨
          (stkAddr ≤ a ∧ a < stkAddr + 3 * N)) → y.mem a = x.mem a) ∧
      (∀ reg : Fin 28, (reg.val < 19 ∨ reg = compIdxReg ∨ reg = oldFinReg) →
        y.regs reg = x.regs reg) := by
  have hr_lt := r.isLt
  have hvis_r : x.mem (visAddr + r.val) = (decide (r ∈ vis)).toNat := hvis r
  have hf_vr : Fits w (visAddr + r.val) := hfit.of_le (by omega)
  obtain ⟨k', hkN⟩ : ∃ k', N = k' + 1 := ⟨N - 1, by omega⟩
  let RootPost (y : Data 28) : Prop :=
    let s := visit adj N r ⟨vis, []⟩
    DfsRegs offAddr edgeAddr visAddr finAddr stkAddr y ∧
      CSRAt adj offAddr edgeAddr y.mem ∧
      VisAt s.visited visAddr y.mem ∧
      y.regs finCnt = F₀ + s.finished.length ∧
      (∀ q (hq : q < s.finished.reverse.length),
        y.mem (finAddr + F₀ + q) = (s.finished.reverse[q]).val) ∧
      (∀ a, ¬ ((visAddr ≤ a ∧ a < visAddr + N) ∨
          (finAddr + F₀ ≤ a ∧ a < finAddr + F₀ + s.finished.length) ∨
          (stkAddr ≤ a ∧ a < stkAddr + 3 * N)) → y.mem a = x.mem a) ∧
      (∀ reg : Fin 28, (reg.val < 19 ∨ reg = compIdxReg ∨ reg = oldFinReg) →
        y.regs reg = x.regs reg)
  change ∃ y, ExecWithin w visitRootCode x y _ ∧ RootPost y
  by_cases hmem : r ∈ vis
  · have hvis_1 : x.mem (visAddr + r.val) = 1 := by simpa [hmem] using hvis_r
    have hs_eq : visit adj N r ⟨vis, []⟩ = ⟨vis, []⟩ := by
      rw [hkN]; exact visit_of_mem hmem
    unfold visitRootCode
    wram_exec [hregs.czero, hregs.hvis, hu, hvis_1, hf_vr]
    dsimp only [RootPost]
    rw [hs_eq]
    refine ⟨?_, ?_, ?_, ?_, fun _ hq => by simp at hq, fun _ _ => rfl, fun reg hreg => ?_⟩
    · refine dfsRegs_of_frame hregs fun reg hreg => ?_
      wram_simp; fin_cases reg <;> simp_all
    · wram_simp; exact hcsr
    · intro w_v; wram_simp; exact hvis w_v
    · wram_simp; simpa using hfc
    · wram_simp; fin_cases reg <;> simp_all
  · have hvis_0 : x.mem (visAddr + r.val) = 0 := by simpa [hmem] using hvis_r
    set vis₁ := insert r vis
    have hcard_vis₁ : vis₁.card = vis.card + 1 := Finset.card_insert_of_notMem hmem
    have hcard_vis₁_le : vis₁.card ≤ N := by
      have := Finset.card_le_univ vis₁; simpa using this
    have hk' : N - vis₁.card ≤ k' := by omega
    have hcons_root : F₀ + 0 + 1 + (N - vis₁.card) ≤ N := by omega
    have hoff_r0 : x.mem (offAddr + r.val) = csrOffset adj r.val := hcsr.1 r.val (by omega)
    have hoff_r1 : x.mem (offAddr + r.val + 1) = csrOffset adj (r.val + 1) := by
      simpa [Nat.add_assoc] using hcsr.1 (r.val + 1) (by omega)
    have hf_or0 : Fits w (offAddr + r.val) := hfit.of_le (by omega)
    have hf_or1 : Fits w (offAddr + r.val + 1) := hfit.of_le (by omega)
    have hf_s1 : Fits w (stkAddr + 1) := hfit.of_le (by omega)
    have hf_s2 : Fits w (stkAddr + 1 + 1) := hfit.of_le (by omega)
    let PushRootPost (x₁ : Data 28) : Prop :=
      DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x₁ ∧
        CSRAt adj offAddr edgeAddr x₁.mem ∧
        VisAt vis₁ visAddr x₁.mem ∧
        x₁.regs pReg = 1 ∧
        x₁.regs finCnt = F₀ ∧
        x₁.mem (stkAddr + 3 * 0) = r.val ∧
        x₁.mem (stkAddr + 3 * 0 + 1) = csrOffset adj r.val + 0 ∧
        x₁.mem (stkAddr + 3 * 0 + 2) = csrOffset adj (r.val + 1) ∧
        (∀ a, ¬ (a = visAddr + r.val ∨ (stkAddr ≤ a ∧ a < stkAddr + 3 * N)) →
          x₁.mem a = x.mem a) ∧
        (∀ reg : Fin 28, (reg.val < 19 ∨ reg = compIdxReg ∨ reg = oldFinReg) →
          x₁.regs reg = x.regs reg)
    have hpush : ∃ x₁, ExecWithin w dfsPushRoot
        ((x.set addr (visAddr + r.val)).set jReg 0) x₁ 9 ∧ PushRootPost x₁ := by
      change ∃ x₁, ExecWithin w dfsPushRoot _ x₁ 9 ∧ PushRootPost x₁
      unfold dfsPushRoot
      wram_exec [hregs.cone, hregs.hoff, hregs.hstk, hu, hoff_r0, hoff_r1,
        hf_or0, hf_or1, hf_s1, hf_s2]
      dsimp only [PushRootPost]
      refine ⟨?_, ?_, ?_, by try wram_simp, by wram_simp; exact hfc,
        ?_, ?_, ?_, fun a ha => ?_, fun reg hreg => ?_⟩
      · refine dfsRegs_of_frame hregs fun reg hreg => ?_
        wram_simp; fin_cases reg <;> simp_all
      · wram_simp
        refine ⟨fun u' hu' => ?_, fun u' q hq => ?_⟩
        · repeat rw [Function.update_of_ne (by omega)]
          exact hcsr.1 u' hu'
        · have hq_lt : csrOffset adj u'.val + q < csrOffset adj N := by
            have h1 := csrOffset_succ adj u'.isLt
            simp only [Fin.eta] at h1
            have h2 := csrOffset_mono adj (by omega : u'.val + 1 ≤ N)
            omega
          repeat rw [Function.update_of_ne (by omega)]
          exact hcsr.2 u' q hq
      · intro w_v; wram_simp
        have hw_lt := w_v.isLt
        repeat rw [Function.update_of_ne (by omega)]
        exact visAt_insert hvis r w_v
      · wram_simp
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Nat.add_zero, Function.update_self]
      · wram_simp
        rw [Function.update_of_ne (by omega), Nat.mul_zero, Nat.add_zero, Function.update_self]
        omega
      · wram_simp
        change Function.update _ (stkAddr + 1 + 1) _ (stkAddr + 2) = _
        rw [show stkAddr + 2 = stkAddr + 1 + 1 by omega, Function.update_self]
      · wram_simp
        repeat rw [Function.update_of_ne (by omega)]
      · wram_simp; fin_cases reg <;> simp_all
    obtain ⟨x₁, hx₁_ex, hx₁_r, hx₁_csr, hx₁_vis, hx₁_p, hx₁_fc, hx₁_s0, hx₁_s1, hx₁_s2,
      hx₁_out, hx₁_fr⟩ := hpush
    have hs_eq : visit adj N r ⟨vis, []⟩ =
        ⟨(foldEmpty adj k' (adj r) vis₁).visited, r :: (foldEmpty adj k' (adj r) vis₁).finished⟩ := by
      rw [hkN]; exact visit_eq_foldEmpty hmem
    obtain ⟨z, ⟨t_loop, ht_loop, he_loop⟩, hRz⟩ := dfsLoop_cps adj offAddr edgeAddr visAddr
      finAddr stkAddr Mc hdisj1 hdisj2 hdisj3 hdisj4 hmc hfit k' r (adj r) 0 0 F₀ 2 vis₁ x₁
      RootPost (by simp) (fun q hq => by simp) hk' hcons_root hx₁_r hx₁_csr hx₁_vis hx₁_p hx₁_fc
      hx₁_s0 hx₁_s1 hx₁_s2
      (fun y hy_r hy_csr hy_vis hy_p hy_fc hy_fin hy_rval hy_out hy_fr => by
        have hend : ¬ (Cond.lt cZero pReg).Holds y := by
          change ¬ y.regs cZero < y.regs pReg
          have := hy_r.czero; omega
        refine ⟨y, ⟨2, le_rfl, Exec.loop_exit hend⟩, ?_⟩
        dsimp only [RootPost]
        rw [hs_eq]
        dsimp only
        refine ⟨hy_r, hy_csr, hy_vis, by simpa [List.length_cons] using hy_fc,
          fun q hq => ?_, fun a ha => ?_, fun reg hreg => (hy_fr reg hreg).trans (hx₁_fr reg hreg)⟩
        · simp only [List.reverse_cons, List.length_append, List.length_reverse,
            List.length_singleton] at hq
          by_cases hq_lt : q < (foldEmpty adj k' (adj r) vis₁).finished.length
          · rw [hy_fin q (by simpa using hq_lt)]
            congr 1
            simp only [List.reverse_cons]
            rw [List.getElem_append_left (by simpa using hq_lt)]
          · have hq_eq : q = (foldEmpty adj k' (adj r) vis₁).finished.length := by omega
            subst hq_eq
            rw [hy_rval]
            congr 1
            simp
        · simp only [List.length_cons] at ha
          have h1 := hy_out a (by simpa using ha)
          have h0 := hx₁_out a (by omega)
          exact h1.trans h0)
    have hcomb : ExecWithin w (dfsPushRoot.seq dfsLoop)
        ((x.set addr (visAddr + r.val)).set jReg 0) z
        (11 + dfsFrameTime adj (adj r) (foldEmpty adj k' (adj r) vis₁).finished) :=
      (hx₁_ex.seq ⟨t_loop, ht_loop, he_loop⟩).mono (by omega)
    have hbound : 2 + 1 + (11 + dfsFrameTime adj (adj r)
        (foldEmpty adj k' (adj r) vis₁).finished) ≤
        16 + 60 * (visit adj N r ⟨vis, []⟩).finished.length +
          36 * outDegreeSum adj (visit adj N r ⟨vis, []⟩).finished := by
      rw [hs_eq]
      dsimp only [dfsFrameTime, List.length_cons, outDegreeSum, List.map_cons, List.sum_cons]
      omega
    unfold visitRootCode
    wram_exec [hregs.czero, hregs.hvis, hu, hvis_0, hf_vr]
    refine WP.of_execWithin hcomb ?_
    exact ⟨hbound, hRz⟩


-- placeholder_part4
end Cslib.Algorithms.WordRAM.TwoSAT
