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
import CslibFrontier.Computability.WordRAM.Allocation
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec
import CslibFrontier.Foundations.Data.List.Fold
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Ring

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
* `Cslib.Algorithms.WordRAM.TwoSAT.Instance.totalLits`,
  `Cslib.Algorithms.WordRAM.TwoSAT.Instance.encode`,
  `Cslib.Algorithms.WordRAM.TwoSAT.Instance.outAddrBase`,
  `Cslib.Algorithms.WordRAM.TwoSAT.Instance.wordBound`: literal-occurrence count, input word list,
  output-list base address, and linear word-width bound.
* `Cslib.Algorithms.WordRAM.TwoSAT.encodeAssignment`,
  `Cslib.Algorithms.WordRAM.TwoSAT.answerWords`,
  `Cslib.Algorithms.WordRAM.TwoSAT.decodeAnswer`: output word list and lossless decoder to
  `Option (Fin G.n → Bool)`.
* `Cslib.Algorithms.WordRAM.TwoSAT.Reg.outBase`: output-list header register.
* `Cslib.Algorithms.WordRAM.TwoSAT.solver`,
  `Cslib.Algorithms.WordRAM.TwoSAT.program`: structured and flat word-RAM programs.

## Main results

* `Cslib.Algorithms.WordRAM.TwoSAT.Instance.encode_length`,
  `Cslib.Algorithms.WordRAM.TwoSAT.Instance.inputFits_encode`: encoded word count and input-fit
  certificate from `Fits w G.wordBound`.
* `Cslib.Algorithms.WordRAM.TwoSAT.decodeAnswer_answerWords`: lossless output decoding.
* `Cslib.Algorithms.WordRAM.TwoSAT.answerWords_eq_nil_iff`,
  `Cslib.Algorithms.WordRAM.TwoSAT.eval_of_decodeAnswer_eq_some`: decision characterization and
  witness soundness.
* `Cslib.Algorithms.WordRAM.TwoSAT.solver_spec`,
  `Cslib.Algorithms.WordRAM.TwoSAT.program_spec`,
  `Cslib.Algorithms.WordRAM.TwoSAT.computesListInTime_program`: execution within
  `512 * (G.n + G.φ.length + 1)` instructions at every word width `w` with `Fits w G.wordBound`.
* `Cslib.Algorithms.WordRAM.TwoSAT.not_readsWidth_program`,
  `Cslib.Algorithms.WordRAM.TwoSAT.isRandFree_program`: width-independence and determinism
  certificates for `program`.

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
  rcases G with ⟨n, φ⟩
  dsimp only [totalLits] at hw ⊢
  induction φ with
  | nil => simp
  | cons c cs ih =>
    have hc : c.length ≤ 2 := hw c List.mem_cons_self
    have hcs := ih fun c' hc' => hw c' (List.mem_cons_of_mem c hc')
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

private theorem fits_of_le {G : Instance} {w x : ℕ} (hfit : Fits w G.wordBound)
    (hle : x ≤ G.wordBound) : Fits w x :=
  hfit.of_le hle

/-- Every word of `G.encode`, together with its length, fits in any word width admitting
`G.wordBound`. -/
theorem inputFits_encode (G : Instance) {w : ℕ} (hfit : Fits w G.wordBound) :
    InputFits w G.encode := by
  refine ⟨hfit.of_le (by rw [G.encode_length]; unfold wordBound; omega), fun v hv => ?_⟩
  simp only [encode, List.mem_cons, List.mem_flatMap] at hv
  rcases hv with rfl | rfl | ⟨c, hc, hvc⟩
  · exact hfit.of_le (by unfold wordBound; omega)
  · exact hfit.of_le (by unfold wordBound; omega)
  · simp only [encodeClauseBy, List.mem_cons, List.mem_map] at hvc
    rcases hvc with rfl | ⟨ℓ, _, rfl⟩
    · have hle : c.length ≤ G.totalLits := List.le_sum_of_mem (List.mem_map_of_mem hc)
      exact hfit.of_le (by unfold wordBound; omega)
    · have hlt : litCodeBy Fin.val ℓ < 2 * G.n := by
        have := ℓ.1.isLt
        have := Bool.toNat_le ℓ.2
        unfold litCodeBy
        omega
      exact hfit.of_le (by unfold wordBound; omega)

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
    have hdiv1 : (2 * v + 1) / 2 = v := by omega
    have hmod1 : (2 * v + 1) % 2 = 1 := by omega
    cases b with
    | false => simp [litCodeBy]
    | true => simp [litCodeBy, hdiv1, hmod1]
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

private abbrev cZero : Fin 28 := ⟨0, by decide⟩
private abbrev cOne : Fin 28 := ⟨1, by decide⟩
private abbrev cTwo : Fin 28 := ⟨2, by decide⟩
private abbrev cThree : Fin 28 := ⟨3, by decide⟩
private abbrev nv : Fin 28 := ⟨4, by decide⟩
private abbrev mClauses : Fin 28 := ⟨5, by decide⟩
private abbrev nVerts : Fin 28 := ⟨6, by decide⟩
/-- Output-list header register (`G.outAddrBase`). -/
abbrev outBase : Fin 28 := ⟨7, by decide⟩
private abbrev offB : Fin 28 := ⟨8, by decide⟩
private abbrev edgeB : Fin 28 := ⟨9, by decide⟩
private abbrev visB : Fin 28 := ⟨10, by decide⟩
private abbrev finB : Fin 28 := ⟨11, by decide⟩
private abbrev stkB : Fin 28 := ⟨12, by decide⟩
private abbrev curB : Fin 28 := ⟨13, by decide⟩
private abbrev revOffB : Fin 28 := ⟨14, by decide⟩
private abbrev revEdgeB : Fin 28 := ⟨15, by decide⟩
private abbrev ordB : Fin 28 := ⟨16, by decide⟩
private abbrev compB : Fin 28 := ⟨17, by decide⟩
private abbrev iReg : Fin 28 := ⟨18, by decide⟩
private abbrev pReg : Fin 28 := ⟨19, by decide⟩
private abbrev finCnt : Fin 28 := ⟨20, by decide⟩
private abbrev compIdxReg : Fin 28 := ⟨21, by decide⟩
private abbrev oldFinReg : Fin 28 := ⟨22, by decide⟩
private abbrev uReg : Fin 28 := ⟨23, by decide⟩
private abbrev vReg : Fin 28 := ⟨24, by decide⟩
private abbrev jReg : Fin 28 := ⟨25, by decide⟩
private abbrev jEndReg : Fin 28 := ⟨26, by decide⟩
private abbrev addr : Fin 28 := ⟨27, by decide⟩

end Reg

open Reg

local macro "reg_ne" : tactic =>
  `(tactic| exact Fin.ne_of_val_ne (by
    simp only [ne_eq, Fin.ext_iff, cZero, cOne, cTwo, cThree, nv, mClauses, nVerts, outBase, offB,
      edgeB, visB, finB, stkB, curB, revOffB, revEdgeB, ordB, compB, iReg, pReg, finCnt,
      compIdxReg, oldFinReg, uReg, vReg, jReg, jEndReg, addr] at *
    omega))

local macro "regs_lt" : tactic =>
  `(tactic| (
    repeat (first
      | rw [Data.write_regs_apply]
      | rw [Data.set_regs_of_ne (by reg_ne)])
    try rfl))

local macro "mem_upd" : tactic =>
  `(tactic| simp only [Data.set_mem, Data.set_mem_apply, Data.write_mem])

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
        · wram_simp
          simp [isValidTwoClause, ‹c.length = 0›]
        · regs_lt
      · dsimp only [StepPost]
        refine ⟨rfl, by wram_simp, by wram_simp; omega, ?_, fun r hr => ?_⟩
        · wram_simp
          have hc_gt : ¬ c.length ≤ 2 := by omega
          simp [isValidTwoClause, hc_gt]
        · regs_lt
      · dsimp only [StepPost]
        refine ⟨rfl, by wram_simp, by wram_simp; omega, ?_, fun r hr => ?_⟩
        · wram_simp
          have hc_ok : 1 ≤ c.length ∧ c.length ≤ 2 := by omega
          simp [isValidTwoClause, hc_ok]
        · regs_lt
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

private theorem CSRAt.of_eqOn {N : ℕ} {adj : Fin N → List (Fin N)} {offBase edgeBase : ℕ}
    {mem₁ mem₂ : ℕ → ℕ} (h : CSRAt adj offBase edgeBase mem₁)
    (hoff : ∀ u ≤ N, mem₂ (offBase + u) = mem₁ (offBase + u))
    (hedge : ∀ e < csrOffset adj N, mem₂ (edgeBase + e) = mem₁ (edgeBase + e)) :
    CSRAt adj offBase edgeBase mem₂ := by
  refine ⟨fun u hu => (hoff u hu).trans (h.1 u hu), fun u k hk => ?_⟩
  have hk_lt : csrOffset adj u.val + k < csrOffset adj N := by
    have h1 := csrOffset_succ adj u.isLt
    simp only [Fin.eta] at h1
    have h2 := csrOffset_mono adj (by omega : u.val + 1 ≤ N)
    omega
  rw [Nat.add_assoc, hedge _ hk_lt, ← Nat.add_assoc]
  exact h.2 u k hk

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

/-- Zero `[baseReg, baseReg + nVerts)` in `4 * N + 4` instructions via `Cslib.WordRAM.zeroFill`. -/
private def zeroBlockCode (baseReg : Fin 28) : Code .standard 28 :=
  (ram[ addr ← baseReg; jEndReg ← baseReg + nVerts ]).seq
    (zeroFill addr jEndReg cZero cOne)

private theorem zeroBlockCode_spec {w : ℕ} (baseReg : Fin 28) (hbr : baseReg.val < 18)
    (B N : ℕ) (hfit : Fits w (B + N)) {x : Data 28}
    (hc0 : x.regs cZero = 0) (hc1 : x.regs cOne = 1)
    (hB : x.regs baseReg = B) (hN : x.regs nVerts = N) :
    ∃ y, ExecWithin w (zeroBlockCode baseReg) x y (4 * N + 4) ∧
      (∀ i < N, y.mem (B + i) = 0) ∧
      (∀ a, ¬ (B ≤ a ∧ a < B + N) → y.mem a = x.mem a) ∧
      (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r) := by
  let x₁ := (x.set addr B).set jEndReg (B + N)
  have hprep : ExecWithin (B := .standard) w
      (ram[ addr ← baseReg; jEndReg ← baseReg + nVerts ]) x x₁ 2 := by
    have hb_ne : baseReg ≠ addr := by reg_ne
    have hn_ne : nVerts ≠ addr := by reg_ne
    have heval : BinOp.add.eval ((x.set addr B).regs baseReg) ((x.set addr B).regs nVerts) =
        B + N := by
      rw [Data.set_regs_of_ne hb_ne, Data.set_regs_of_ne hn_ne, hB, hN]; rfl
    have he1 : Exec (B := .standard) w (ram[ addr ← baseReg ]) x (x.set addr B) 1 := by
      simpa [hB] using (Exec.copy (B := .standard) (w := w) (x := x) (d := addr) (s := baseReg))
    have he2 : Exec (B := .standard) w (ram[ jEndReg ← baseReg + nVerts ]) (x.set addr B) x₁ 1 := by
      have hfit' : Fits w (BinOp.add.eval ((x.set addr B).regs baseReg)
          ((x.set addr B).regs nVerts)) := by rwa [heval]
      have h : Exec (B := .standard) w (ram[ jEndReg ← baseReg + nVerts ]) (x.set addr B) _ 1 :=
        Exec.bin hfit'
      rwa [heval] at h
    exact ⟨2, le_rfl, he1.seq he2⟩
  have hx₁_addr : x₁.regs addr = B := by dsimp only [x₁]; wram_simp
  have hx₁_stop : x₁.regs jEndReg = B + N := by dsimp only [x₁]; wram_simp
  have hx₁_0 : x₁.regs cZero = 0 := by dsimp only [x₁]; wram_simp; exact hc0
  have hx₁_1 : x₁.regs cOne = 1 := by dsimp only [x₁]; wram_simp; exact hc1
  have hzf := zeroFill_exec (w := w) (cur := addr) (stop := jEndReg) (zero := cZero) (one := cOne)
    (x := x₁) (by decide) (by decide) (by decide) hx₁_0 hx₁_1
    (by rw [hx₁_addr, hx₁_stop]; omega) (by rw [hx₁_stop]; exact hfit)
  rw [hx₁_addr, hx₁_stop, Nat.add_sub_cancel_left] at hzf
  have hzf_w : ExecWithin w (zeroFill addr jEndReg cZero cOne) x₁
      ⟨Function.update x₁.regs addr (B + N), clear x₁.mem B N⟩ (4 * N + 2) :=
    ⟨4 * N + 2, le_rfl, hzf⟩
  refine ⟨_, (hprep.seq hzf_w).mono (by omega), fun i hi => ?_, fun a ha => ?_, fun r hr => ?_⟩
  · exact clear_of_owns ⟨Nat.le_add_right B i, Nat.add_lt_add_left hi B⟩
  · exact clear_of_not_owns ha
  · have hne1 : r ≠ addr := by reg_ne
    simp only [x₁, Function.update_of_ne hne1]
    regs_lt

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
  dsimp only [IncPost]
  refine ⟨fun u => ?_, fun a ha => ?_, fun r h1 h2 => ?_⟩
  · mem_upd
    by_cases hu : u = src
    · subst hu; simp
    · have hne : curBase + u.val ≠ curBase + src.val := fun h => hu (Fin.ext (by omega))
      simp [Function.update_of_ne hne, Function.update_of_ne hu, hmem u]
  · mem_upd
    exact Function.update_of_ne (by omega) _ _
  · regs_lt

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
    dsimp only [PrepPost]
    refine ⟨by wram_simp, by wram_simp, by wram_simp, fun r hr => ?_⟩
    regs_lt
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
    dsimp only [BodyPost, P]
    refine ⟨⟨fun r hr => ?_, ?_, fun u hu => ?_, fun u => ?_, fun a ha => ?_⟩, by wram_simp⟩
    · regs_lt; exact hy_fr r hr
    · wram_simp; exact hoff_succ.symm
    · mem_upd
      by_cases huk : u = y.regs iReg + 1
      · subst huk; simp [hoff_succ]
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hy_off u (by omega)
    · mem_upd
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
    · mem_upd
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
  dsimp only
  have hsrc_lt := src.isLt
  have hcur_eq := hp.2.1 src
  have hoff_src : csrOffset targetAdj (src.val + 1) =
      csrOffset targetAdj src.val + (targetAdj src).length := by
    simpa using csrOffset_succ targetAdj hsrc_lt
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
    rcases eq_or_ne src u with rfl | hu
    · rw [Function.update_self, show mem₁ (curBase + src.val) = c from Function.update_self _ _ _,
        List.length_cons]
      omega
    · have hne : curBase + u.val ≠ curBase + src.val := fun h => hu (Fin.ext (by omega)).symm
      rw [Function.update_of_ne hu.symm,
        show mem₁ (curBase + u.val) = mem (curBase + u.val) from Function.update_of_ne hne _ _]
      exact hp.2.1 u
  · rcases eq_or_ne src u with rfl | hu
    · have hlen_upd : (Function.update part src (dst :: part src) src).length =
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
    · have hu' : u ≠ src := hu.symm
      have hget_upd : ∀ j (hj : j < (Function.update part src (dst :: part src) u).length),
          (Function.update part src (dst :: part src) u)[j] =
            (part u)[j]'(by simpa [Function.update_of_ne hu'] using hj) := by
        intro j hj
        simp [Function.update_of_ne hu']
      rw [hget_upd k hk]
      have hk_u : k < (part u).length := by simpa [Function.update_of_ne hu'] using hk
      have hne_c : curBase + u.val ≠ curBase + src.val := fun h => hu' (Fin.ext (by omega))
      have hm_cur : mem' (curBase + u.val) = mem (curBase + u.val) := by
        change Function.update mem₁ (edgeBase + c) dst.val (curBase + u.val) = mem (curBase + u.val)
        rw [Function.update_of_ne (by have := u.isLt; omega)]
        exact Function.update_of_ne hne_c _ _
      rw [hm_cur]
      have hu_cur := hp.2.1 u
      have hu_len := hp.1 u
      have hu_off : csrOffset targetAdj (u.val + 1) =
          csrOffset targetAdj u.val + (targetAdj u).length := by
        simpa using csrOffset_succ targetAdj u.isLt
      have hq_low : csrOffset targetAdj u.val ≤ mem (curBase + u.val) + k := by omega
      have hq_high : mem (curBase + u.val) + k < csrOffset targetAdj (u.val + 1) := by omega
      have hne_edge : mem (curBase + u.val) + k ≠ c :=
        csrOffset_disjoint targetAdj hu' hq_low hq_high hc_low hc_high
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
  have hoff_src : csrOffset targetAdj (src.val + 1) =
      csrOffset targetAdj src.val + (targetAdj src).length := by
    simpa using csrOffset_succ targetAdj hsrc_lt
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
  dsimp only [BfPost]
  refine ⟨?_, fun a ha => ?_, fun r h1 h2 => ?_⟩
  · mem_upd; exact hstep.1
  · mem_upd; exact hstep.2 a ha
  · regs_lt

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
          by_cases h1 : b.negate = a.negate
          · rw [h1]; simp; omega
          · simp [h1]
        · by_cases h1 : w = a.negate
          · subst h1; simp [h2]
          · simp [h2, h1]
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
      ∃ y, ExecWithin w (.loop (.lt iReg mClauses) implDegBody) x y (21 * cs.length + 2) ∧
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
    have hstep : ∃ x₁, ExecWithin w implDegBody x x₁ 19 ∧ DegStepPost x₁ := by
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
            (x := st_v) (by dsimp only [st_v, st_pre]; wram_simp; exact hc1)
            (by dsimp only [st_v, st_pre]; wram_simp; exact hcur)
            (by dsimp only [st_v]; wram_simp; exact hxor_a)
            (by dsimp only [st_v, st_pre]; exact hdeg)
        have hlen_1 : x.mem p = 1 := by simpa using hlen_p
        unfold implDegBody
        wram_exec [hc1, hpR, hi, hlen_1, hmem_a, hf_p1, hf_na]
        refine WP.of_execWithin hy₁_ex ?_
        have hy₁_1 : y₁.regs cOne = 1 :=
          (hy₁_fr cOne (by decide) (by decide)).trans
            (by dsimp only [st_v, st_pre]; wram_simp; exact hc1)
        have hy₁_p : y₁.regs pReg = p + 1 :=
          (hy₁_fr pReg (by decide) (by decide)).trans (by dsimp only [st_v, st_pre]; wram_simp)
        have hy₁_i : y₁.regs iReg = idx :=
          (hy₁_fr iReg (by decide) (by decide)).trans
            (by dsimp only [st_v, st_pre]; wram_simp; exact hi)
        wram_exec [hy₁_1, hy₁_p, hy₁_i, hf_p2, hf_i1]
        dsimp only [DegStepPost]
        refine ⟨fun u => ?_, fun addr_a ha => ?_, by wram_simp, by wram_simp; omega,
          fun r hr => ?_⟩
        · wram_simp
          rw [hy₁_deg u, mapAdj_addClauseEdges_one]
          by_cases hu : u = litEquiv G.n a.negate <;> simp [hu]
        · wram_simp; exact hy₁_out addr_a ha
        · regs_lt
          rw [hy₁_fr r (by reg_ne) (by reg_ne)]
          dsimp only [st_v, st_pre]; regs_lt
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
        have hlen_2 : x.mem p = 2 := by simpa using hlen_p
        unfold implDegBody
        wram_exec [hc1, hpR, hi, hlen_2, hmem_a, hmem_b, hf_p1, hf_p2, hf_na]
        refine WP.of_execWithin hy₁_ex ?_
        wram_exec [hy₁_1, hy₁_b, hf_nb]
        refine WP.of_execWithin hy₂_ex ?_
        have hy₂_1 : y₂.regs cOne = 1 :=
          (hy₂_fr cOne (by decide) (by decide)).trans
            (by dsimp only [st_v2]; wram_simp; exact hy₁_1)
        have hy₂_p : y₂.regs pReg = p + 1 + 1 :=
          (hy₂_fr pReg (by decide) (by decide)).trans
            ((hy₁_fr pReg (by decide) (by decide)).trans (by dsimp only [st_v1]; wram_simp))
        have hy₂_i : y₂.regs iReg = idx :=
          (hy₂_fr iReg (by decide) (by decide)).trans
            ((hy₁_fr iReg (by decide) (by decide)).trans
              (by dsimp only [st_v1]; wram_simp; exact hi))
        wram_exec [hy₂_1, hy₂_p, hy₂_i, hf_p3, hf_i1]
        dsimp only [DegStepPost]
        refine ⟨fun u => ?_, fun addr_a ha => ?_, by wram_simp, by wram_simp; omega,
          fun r hr => ?_⟩
        · wram_simp
          rw [hy₂_deg u, mapAdj_addClauseEdges_two, ← hg₁_map]
          by_cases hu : u = litEquiv G.n b.negate <;> simp [hu]
        · wram_simp; exact (hy₂_out addr_a ha).trans (hy₁_out addr_a ha)
        · regs_lt
          rw [hy₂_fr r (by reg_ne) (by reg_ne)]
          dsimp only [st_v2]; regs_lt
          rw [hy₁_fr r (by reg_ne) (by reg_ne)]
          dsimp only [st_v1]; regs_lt
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
        · wram_simp
          rwa [mapAdj_addClauseEdges_one]
        · wram_simp
          exact hy₁_out addr_a ha
        · regs_lt
          rw [hy₁_fr r (by reg_ne) (by reg_ne)]
          dsimp only [st_v]; regs_lt
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
          (hy₁_fr edgeB (by decide) (by decide)).trans
            (by dsimp only [st_v1]; wram_simp; exact hedge)
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
          (hy₂_fr cOne (by decide) (by decide)).trans
            (by dsimp only [st_v2]; wram_simp; exact hy₁_1)
        have hy₂_pr : y₂.regs pReg = p + 1 + 1 :=
          (hy₂_fr pReg (by decide) (by decide)).trans
            ((hy₁_fr pReg (by decide) (by decide)).trans (by dsimp only [st_v1]; wram_simp))
        have hy₂_i : y₂.regs iReg = idx :=
          (hy₂_fr iReg (by decide) (by decide)).trans
            ((hy₁_fr iReg (by decide) (by decide)).trans
              (by dsimp only [st_v1]; wram_simp; exact hi))
        wram_exec [hy₂_1, hy₂_pr, hy₂_i, hf_p3, hf_i1]
        dsimp only [FillStepPost]
        refine ⟨?_, fun addr_a ha => ?_, by wram_simp, by wram_simp; omega, fun r hr => ?_⟩
        · wram_simp
          rwa [mapAdj_addClauseEdges_two, ← hg₁_map]
        · wram_simp
          exact (hy₂_out addr_a ha).trans (hy₁_out addr_a ha)
        · regs_lt
          rw [hy₂_fr r (by reg_ne) (by reg_ne)]
          dsimp only [st_v2]; regs_lt
          rw [hy₁_fr r (by reg_ne) (by reg_ne)]
          dsimp only [st_v1]; regs_lt
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

private theorem dfsStepBody_pop {N w : ℕ} (adj : Fin N → List (Fin N))
    (offAddr edgeAddr visAddr finAddr stkAddr Mc : ℕ)
    (hdisj1 : offAddr + N + 1 ≤ visAddr)
    (hdisj2 : edgeAddr + Mc ≤ visAddr)
    (hdisj3 : visAddr + N ≤ finAddr)
    (hdisj4 : finAddr + N ≤ stkAddr)
    (hmc : csrOffset adj N ≤ Mc)
    (hfit : Fits w (stkAddr + 3 * N + Mc + 4))
    (u : Fin N) (idx d F₀ : ℕ) (vis : Finset (Fin N)) {x : Data 28}
    (hidx : idx = (adj u).length)
    (hcons : F₀ + d + 1 + (N - vis.card) ≤ N)
    (hregs : DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x)
    (hcsr : CSRAt adj offAddr edgeAddr x.mem)
    (hvis : VisAt vis visAddr x.mem)
    (hp : x.regs pReg = d + 1)
    (hfc : x.regs finCnt = F₀)
    (hstk0 : x.mem (stkAddr + 3 * d) = u.val)
    (hstk1 : x.mem (stkAddr + 3 * d + 1) = csrOffset adj u.val + idx)
    (hstk2 : x.mem (stkAddr + 3 * d + 2) = csrOffset adj (u.val + 1)) :
    ∃ x₁, ExecWithin w dfsStepBody x x₁ 16 ∧
      DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x₁ ∧
      CSRAt adj offAddr edgeAddr x₁.mem ∧
      VisAt vis visAddr x₁.mem ∧
      x₁.regs pReg = d ∧
      x₁.regs finCnt = F₀ + 1 ∧
      x₁.mem (finAddr + F₀) = u.val ∧
      (∀ a, ¬ (a = finAddr + F₀) → x₁.mem a = x.mem a) ∧
      (∀ r : Fin 28, (r.val < 19 ∨ r = compIdxReg ∨ r = oldFinReg) → x₁.regs r = x.regs r) := by
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
  change ∃ x₁, ExecWithin w dfsStepBody x x₁ 16 ∧ PopPost x₁
  have hstk2' : x.mem (stkAddr + 3 * d + 1 + 1) = csrOffset adj (u.val + 1) := by
    simpa [Nat.add_assoc] using hstk2
  unfold dfsStepBody
  wram_exec [hregs.czero, hregs.cone, hregs.cthree, hregs.hoff, hregs.hedge, hregs.hvis,
    hregs.hfin, hregs.hstk, hp, hfc, hstk0, hstk1', hstk2',
    hf_3d, hf_s0, hf_s1, hf_s2, hf_fin, hf_fc1]
  dsimp only [PopPost]
  refine ⟨?_, ?_, ?_, by wram_simp, by wram_simp, ?_, fun a ha => ?_, fun r hr => ?_⟩
  · refine dfsRegs_of_frame hregs fun r hr => ?_
    regs_lt
  · mem_upd
    exact hcsr.of_eqOn
      (fun _ _ => Function.update_of_ne (by omega) _ _)
      (fun _ _ => Function.update_of_ne (by omega) _ _)
  · intro w_v; mem_upd
    rw [Function.update_of_ne (by have := w_v.isLt; omega)]; exact hvis w_v
  · mem_upd; exact Function.update_self _ _ _
  · mem_upd; exact Function.update_of_ne ha _ _
  · have hv : r ≠ vReg := by reg_ne
    have ha : r ≠ addr := by reg_ne
    have hu' : r ≠ uReg := by reg_ne
    have hj : r ≠ jReg := by reg_ne
    have hje : r ≠ jEndReg := by reg_ne
    have hp' : r ≠ pReg := by reg_ne
    have hfc' : r ≠ finCnt := by reg_ne
    simp only [Data.write_regs_apply, Data.set_regs_of_ne hv, Data.set_regs_of_ne ha,
      Data.set_regs_of_ne hu', Data.set_regs_of_ne hj, Data.set_regs_of_ne hje,
      Data.set_regs_of_ne hp', Data.set_regs_of_ne hfc']

private theorem dfsStepBody_skip {N w : ℕ} (adj : Fin N → List (Fin N))
    (offAddr edgeAddr visAddr finAddr stkAddr Mc : ℕ)
    (hdisj1 : offAddr + N + 1 ≤ visAddr)
    (hdisj2 : edgeAddr + Mc ≤ visAddr)
    (hdisj3 : visAddr + N ≤ finAddr)
    (hdisj4 : finAddr + N ≤ stkAddr)
    (hmc : csrOffset adj N ≤ Mc)
    (hfit : Fits w (stkAddr + 3 * N + Mc + 4))
    (u v : Fin N) (idx d F₀ : ℕ) (vis : Finset (Fin N)) {x : Data 28}
    (hidx_lt : idx < (adj u).length)
    (hv_eq : (adj u)[idx]'hidx_lt = v)
    (hmem : v ∈ vis)
    (hcons : F₀ + d + 1 + (N - vis.card) ≤ N)
    (hregs : DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x)
    (hcsr : CSRAt adj offAddr edgeAddr x.mem)
    (hvis : VisAt vis visAddr x.mem)
    (hp : x.regs pReg = d + 1)
    (hfc : x.regs finCnt = F₀)
    (hstk0 : x.mem (stkAddr + 3 * d) = u.val)
    (hstk1 : x.mem (stkAddr + 3 * d + 1) = csrOffset adj u.val + idx)
    (hstk2 : x.mem (stkAddr + 3 * d + 2) = csrOffset adj (u.val + 1)) :
    ∃ x₁, ExecWithin w dfsStepBody x x₁ 24 ∧
      DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x₁ ∧
      CSRAt adj offAddr edgeAddr x₁.mem ∧
      VisAt vis visAddr x₁.mem ∧
      x₁.regs pReg = d + 1 ∧
      x₁.regs finCnt = F₀ ∧
      x₁.mem (stkAddr + 3 * d) = u.val ∧
      x₁.mem (stkAddr + 3 * d + 1) = csrOffset adj u.val + (idx + 1) ∧
      x₁.mem (stkAddr + 3 * d + 2) = csrOffset adj (u.val + 1) ∧
      (∀ a, a ≠ stkAddr + 3 * d + 1 → x₁.mem a = x.mem a) ∧
      (∀ r : Fin 28, (r.val < 19 ∨ r = compIdxReg ∨ r = oldFinReg) → x₁.regs r = x.regs r) := by
  have hoff_u := csrOffset_succ adj u.isLt
  simp only [Fin.eta] at hoff_u
  set j := csrOffset adj u.val + idx
  have hj_lt_end : j < csrOffset adj (u.val + 1) := by omega
  have hj_lt_N : j < csrOffset adj N :=
    lt_of_lt_of_le hj_lt_end (csrOffset_mono adj (by have := u.isLt; omega : u.val + 1 ≤ N))
  have hedge_j : x.mem (edgeAddr + j) = v.val := by
    rw [show edgeAddr + j = edgeAddr + csrOffset adj u.val + idx by dsimp only [j]; omega,
      hcsr.2 u idx hidx_lt, hv_eq]
  have hvis_v1 : x.mem (visAddr + v.val) = 1 := by simpa [hmem] using hvis v
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
  change ∃ x₁, ExecWithin w dfsStepBody x x₁ 24 ∧ SkipPost x₁
  unfold dfsStepBody
  wram_exec [hregs.czero, hregs.cone, hregs.cthree, hregs.hoff, hregs.hedge, hregs.hvis,
    hregs.hfin, hregs.hstk, hp, hfc, hstk0, hstk1, hstk2', hedge_j, hvis_v1, hj_lt_end,
    hf_3d, hf_s0, hf_s1, hf_s2, hf_j1, hf_ej, hf_vv]
  dsimp only [SkipPost]
  refine ⟨?_, ?_, ?_, by wram_simp, by wram_simp; exact hfc, ?_, ?_, ?_,
    fun a ha => ?_, fun r hr => ?_⟩
  · refine dfsRegs_of_frame hregs fun r hr => ?_
    regs_lt
  · mem_upd
    exact hcsr.of_eqOn
      (fun _ _ => Function.update_of_ne (by omega) _ _)
      (fun _ _ => Function.update_of_ne (by omega) _ _)
  · intro w_v; mem_upd
    rw [Function.update_of_ne (by have := w_v.isLt; omega)]; exact hvis w_v
  · mem_upd; rw [Function.update_of_ne (by omega)]; exact hstk0
  · mem_upd; rw [Function.update_self]; omega
  · mem_upd; rw [Function.update_of_ne (by omega)]; exact hstk2
  · mem_upd; exact Function.update_of_ne ha _ _
  · have hv : r ≠ vReg := by reg_ne
    have ha : r ≠ addr := by reg_ne
    have hu' : r ≠ uReg := by reg_ne
    have hj : r ≠ jReg := by reg_ne
    have hje : r ≠ jEndReg := by reg_ne
    have hp' : r ≠ pReg := by reg_ne
    simp only [Data.write_regs_apply, Data.set_regs_of_ne hv, Data.set_regs_of_ne ha,
      Data.set_regs_of_ne hu', Data.set_regs_of_ne hj, Data.set_regs_of_ne hje,
      Data.set_regs_of_ne hp']

private theorem dfsStepBody_push {N w : ℕ} (adj : Fin N → List (Fin N))
    (offAddr edgeAddr visAddr finAddr stkAddr Mc : ℕ)
    (hdisj1 : offAddr + N + 1 ≤ visAddr)
    (hdisj2 : edgeAddr + Mc ≤ visAddr)
    (hdisj3 : visAddr + N ≤ finAddr)
    (hdisj4 : finAddr + N ≤ stkAddr)
    (hmc : csrOffset adj N ≤ Mc)
    (hfit : Fits w (stkAddr + 3 * N + Mc + 4))
    (u v : Fin N) (idx d F₀ : ℕ) (vis : Finset (Fin N)) {x : Data 28}
    (hidx_lt : idx < (adj u).length)
    (hv_eq : (adj u)[idx]'hidx_lt = v)
    (hmem : v ∉ vis)
    (hcons_child : F₀ + (d + 1) + 1 + (N - (insert v vis).card) ≤ N)
    (hregs : DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x)
    (hcsr : CSRAt adj offAddr edgeAddr x.mem)
    (hvis : VisAt vis visAddr x.mem)
    (hp : x.regs pReg = d + 1)
    (hfc : x.regs finCnt = F₀)
    (hstk0 : x.mem (stkAddr + 3 * d) = u.val)
    (hstk1 : x.mem (stkAddr + 3 * d + 1) = csrOffset adj u.val + idx)
    (hstk2 : x.mem (stkAddr + 3 * d + 2) = csrOffset adj (u.val + 1)) :
    ∃ x₁, ExecWithin w dfsStepBody x x₁ 34 ∧
      DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x₁ ∧
      CSRAt adj offAddr edgeAddr x₁.mem ∧
      VisAt (insert v vis) visAddr x₁.mem ∧
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
      (∀ r : Fin 28, (r.val < 19 ∨ r = compIdxReg ∨ r = oldFinReg) → x₁.regs r = x.regs r) := by
  have hoff_u := csrOffset_succ adj u.isLt
  simp only [Fin.eta] at hoff_u
  set j := csrOffset adj u.val + idx
  have hj_lt_end : j < csrOffset adj (u.val + 1) := by omega
  have hj_lt_N : j < csrOffset adj N :=
    lt_of_lt_of_le hj_lt_end (csrOffset_mono adj (by have := u.isLt; omega : u.val + 1 ≤ N))
  have hedge_j : x.mem (edgeAddr + j) = v.val := by
    rw [show edgeAddr + j = edgeAddr + csrOffset adj u.val + idx by dsimp only [j]; omega,
      hcsr.2 u idx hidx_lt, hv_eq]
  have hvis_v0 : x.mem (visAddr + v.val) = 0 := by simpa [hmem] using hvis v
  set vis₁ := insert v vis
  have hcard_vis₁_le : vis₁.card ≤ N := by
    have := Finset.card_le_univ vis₁; simpa using this
  have hu_lt := u.isLt
  have hv_lt := v.isLt
  have hoff_v0 : x.mem (offAddr + v.val) = csrOffset adj v.val := hcsr.1 v.val (by omega)
  have hoff_v1 : x.mem (offAddr + v.val + 1) = csrOffset adj (v.val + 1) := by
    simpa [Nat.add_assoc] using hcsr.1 (v.val + 1) (by omega)
  have hf_3d : Fits w (3 * d) := hfit.of_le (by omega)
  have hf_s0 : Fits w (stkAddr + 3 * d) := hfit.of_le (by omega)
  have hf_s1 : Fits w (stkAddr + 3 * d + 1) := hfit.of_le (by omega)
  have hf_s2 : Fits w (stkAddr + 3 * d + 1 + 1) := hfit.of_le (by omega)
  have hf_j1 : Fits w (j + 1) := hfit.of_le (by omega)
  have hf_ej : Fits w (edgeAddr + j) := hfit.of_le (by omega)
  have hf_vv : Fits w (visAddr + v.val) := hfit.of_le (by omega)
  have hf_ov0 : Fits w (offAddr + v.val) := hfit.of_le (by omega)
  have hf_ov1 : Fits w (offAddr + v.val + 1) := hfit.of_le (by omega)
  have hf_3d1 : Fits w (3 * (d + 1)) := hfit.of_le (by omega)
  have hf_c0 : Fits w (stkAddr + 3 * (d + 1)) := hfit.of_le (by omega)
  have hf_c1 : Fits w (stkAddr + 3 * (d + 1) + 1) := hfit.of_le (by omega)
  have hf_c2 : Fits w (stkAddr + 3 * (d + 1) + 1 + 1) := hfit.of_le (by omega)
  have hf_p2 : Fits w (d + 1 + 1) := hfit.of_le (by omega)
  have hstk2' : x.mem (stkAddr + 3 * d + 1 + 1) = csrOffset adj (u.val + 1) := by
    simpa [Nat.add_assoc] using hstk2
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
    regs_lt
  · mem_upd
    exact hcsr.of_eqOn
      (fun _ _ => by repeat rw [Function.update_of_ne (by omega)])
      (fun _ _ => by repeat rw [Function.update_of_ne (by omega)])
  · intro w_v; mem_upd
    have hw_lt := w_v.isLt
    repeat rw [Function.update_of_ne (by omega)]
    by_cases hwv : w_v = v
    · subst hwv
      rw [Function.update_self]
      simp [vis₁]
    · have hne : visAddr + w_v.val ≠ visAddr + v.val := fun h => hwv (Fin.ext (by omega))
      rw [Function.update_of_ne hne, Function.update_of_ne (by omega)]
      simpa [vis₁, hwv] using hvis w_v
  · mem_upd; repeat rw [Function.update_of_ne (by omega)]
    exact hstk0
  · mem_upd; repeat rw [Function.update_of_ne (by omega)]
    rw [Function.update_self]; omega
  · mem_upd; repeat rw [Function.update_of_ne (by omega)]
    exact hstk2
  · mem_upd
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
  · mem_upd
    rw [Function.update_of_ne (by omega), Function.update_self]; omega
  · mem_upd
    rw [show stkAddr + 3 * (d + 1) + 2 = stkAddr + 3 * (d + 1) + 1 + 1 by omega,
      Function.update_self]
  · mem_upd
    repeat rw [Function.update_of_ne (by omega)]
  · have hv : r ≠ vReg := by reg_ne
    have ha : r ≠ addr := by reg_ne
    have hu' : r ≠ uReg := by reg_ne
    have hj : r ≠ jReg := by reg_ne
    have hje : r ≠ jEndReg := by reg_ne
    have hp' : r ≠ pReg := by reg_ne
    simp only [Data.write_regs_apply, Data.set_regs_of_ne hv, Data.set_regs_of_ne ha,
      Data.set_regs_of_ne hu', Data.set_regs_of_ne hj, Data.set_regs_of_ne hje,
      Data.set_regs_of_ne hp']

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
      obtain ⟨x₁, ⟨t₁, ht₁, he₁⟩, hx₁_r, hx₁_csr, hx₁_vis, hx₁_p, hx₁_fc, hx₁_fin0, hx₁_out,
        hx₁_fr⟩ :=
        dfsStepBody_pop adj offAddr edgeAddr visAddr finAddr stkAddr Mc
          hdisj1 hdisj2 hdisj3 hdisj4 hmc hfit u idx d F₀ vis hidx hcons
          hregs hcsr hvis hp hfc hstk0 hstk1 hstk2
      obtain ⟨z, ⟨t₂, ht₂, he₂⟩, hQz⟩ := hcont x₁ hx₁_r hx₁_csr hx₁_vis hx₁_p
        (by simpa [foldEmpty] using hx₁_fc)
        (fun q hq => by simp [foldEmpty] at hq)
        (by simpa [foldEmpty] using hx₁_fin0)
        (fun a ha => hx₁_out a (by dsimp only [foldEmpty, List.length_nil] at ha; omega))
        hx₁_fr
      have hlt : (Cond.lt cZero pReg).Holds x := by
        have := hregs.czero
        change x.regs cZero < x.regs pReg; omega
      exact ⟨z, ⟨t₁ + t₂ + 2, by dsimp only [dfsFrameTime, foldEmpty, outDegreeSum]; omega,
        Exec.loop_iter hlt he₁ he₂⟩, hQz⟩
    | cons v es' ih_es =>
      intro idx d F₀ T_cont vis x Q hidx hes hk hcons hregs hcsr hvis hp hfc hstk0 hstk1 hstk2
        hcont
      simp only [List.length_cons] at hidx
      have hv_eq : (adj u)[idx]'(by omega) = v := by
        have h0 := hes 0 (by simp)
        simpa only [Nat.add_zero, List.getElem_cons_zero] using h0
      have hes' : ∀ q (hq : q < es'.length), (adj u)[idx + 1 + q]'(by omega) = es'[q] := by
        intro q hq
        have h := hes (q + 1) (by simp only [List.length_cons]; omega)
        have hcongr : (adj u)[idx + 1 + q]'(by omega) = (adj u)[idx + (q + 1)]'(by omega) := by
          congr 1; omega
        exact hcongr.trans (by simpa only [List.getElem_cons_succ] using h)
      by_cases hmem : v ∈ vis
      · -- Case 1: `v ∈ vis`
        have hvisit_v : visit adj k v ⟨vis, []⟩ = ⟨vis, []⟩ := by
          cases k with
          | zero => rfl
          | succ k' => exact visit_of_mem hmem
        have hfold_eq : foldEmpty adj k (v :: es') vis = foldEmpty adj k es' vis := by
          rw [foldEmpty_cons, hvisit_v]
          simp
        obtain ⟨x₁, ⟨t₁, ht₁, he₁⟩, hx₁_r, hx₁_csr, hx₁_vis, hx₁_p, hx₁_fc, hx₁_s0, hx₁_s1,
          hx₁_s2, hx₁_out, hx₁_fr⟩ :=
          dfsStepBody_skip adj offAddr edgeAddr visAddr finAddr stkAddr Mc
            hdisj1 hdisj2 hdisj3 hdisj4 hmc hfit u v idx d F₀ vis (by omega) hv_eq hmem hcons
            hregs hcsr hvis hp hfc hstk0 hstk1 hstk2
        obtain ⟨z, ⟨t₂, ht₂, he₂⟩, hQz⟩ := ih_es (idx + 1) d F₀ T_cont vis x₁ Q (by omega) hes'
          hk hcons hx₁_r hx₁_csr hx₁_vis hx₁_p hx₁_fc hx₁_s0 hx₁_s1 hx₁_s2
          (fun y hy_r hy_csr hy_vis hy_p hy_fc hy_fin hy_u hy_out hy_fr => by
            rw [hfold_eq] at hcont
            exact hcont y hy_r hy_csr hy_vis hy_p hy_fc hy_fin hy_u
              (fun a ha => (hy_out a ha).trans (hx₁_out a (by omega)))
              (fun r hr => (hy_fr r hr).trans (hx₁_fr r hr)))
        have hlt : (Cond.lt cZero pReg).Holds x := by
          have := hregs.czero
          change x.regs cZero < x.regs pReg; omega
        refine ⟨z, ⟨t₁ + t₂ + 2, ?_, Exec.loop_iter hlt he₁ he₂⟩, hQz⟩
        rw [hfold_eq]
        simp only [dfsFrameTime, List.length_cons] at ht₂ ⊢
        omega
      · -- Case 2: `v ∉ vis`
        have hcard_lt : vis.card < N := card_lt_of_notMem hmem
        rcases k with _ | k'
        · omega
        set vis₁ := insert v vis
        have hcard_vis₁ : vis₁.card = vis.card + 1 := Finset.card_insert_of_notMem hmem
        have hcard_vis₁_le : vis₁.card ≤ N := by
          have := Finset.card_le_univ vis₁; simpa using this
        have hk' : N - vis₁.card ≤ k' := by omega
        have hcons_child : F₀ + (d + 1) + 1 + (N - vis₁.card) ≤ N := by omega
        obtain ⟨x₁, ⟨t₁, ht₁, he₁⟩, hx₁_r, hx₁_csr, hx₁_vis, hx₁_p, hx₁_fc, hx₁_d0, hx₁_d1,
          hx₁_d2, hx₁_c0, hx₁_c1, hx₁_c2, hx₁_out, hx₁_fr⟩ :=
          dfsStepBody_push adj offAddr edgeAddr visAddr finAddr stkAddr Mc
            hdisj1 hdisj2 hdisj3 hdisj4 hmc hfit u v idx d F₀ vis (by omega) hv_eq hmem
            hcons_child hregs hcsr hvis hp hfc hstk0 hstk1 hstk2
        obtain ⟨s₁, hs₁_def⟩ : ∃ s₁, visit adj (k' + 1) v ⟨vis, []⟩ = s₁ := ⟨_, rfl⟩
        obtain ⟨s_child, hsc_def⟩ : ∃ s_child, foldEmpty adj k' (adj v) vis₁ = s_child := ⟨_, rfl⟩
        have hs₁_eq : s₁ = ⟨s_child.visited, v :: s_child.finished⟩ := by
          rw [← hs₁_def, ← hsc_def]; exact visit_eq_foldEmpty hmem
        obtain ⟨s₂, hs₂_def⟩ : ∃ s₂, foldEmpty adj (k' + 1) es' s₁.visited = s₂ := ⟨_, rfl⟩
        have hfold_cons : foldEmpty adj (k' + 1) (v :: es') vis =
            ⟨s₂.visited, s₂.finished ++ s₁.finished⟩ := by
          rw [← hs₂_def, ← hs₁_def]; exact foldEmpty_cons adj (k' + 1) v es' vis
        have hcard_s₁ : s₁.visited.card = vis.card + s₁.finished.length := by
          rw [← hs₁_def]; exact card_visit_nil adj (k' + 1) v vis
        have hcard_s₁_le : s₁.visited.card ≤ N := by
          have := Finset.card_le_univ s₁.visited; simpa only [Fintype.card_fin] using this
        have hlen_s₁ : s₁.finished.length = s_child.finished.length + 1 := by
          rw [hs₁_eq]; rfl
        have hk_s₁ : N - s₁.visited.card ≤ k' + 1 := by omega
        have hcons_after : (F₀ + s₁.finished.length) + d + 1 + (N - s₁.visited.card) ≤ N := by
          omega
        obtain ⟨z, ⟨t₂, ht₂, he₂⟩, hQz⟩ := ih_k k' (Nat.lt_succ_self k') v (adj v) 0 (d + 1) F₀
          (dfsFrameTime adj es' s₂.finished + T_cont) vis₁ x₁ Q (Nat.zero_add _)
          (fun q hq => by simp only [Nat.zero_add]) hk' hcons_child hx₁_r hx₁_csr hx₁_vis hx₁_p
          hx₁_fc hx₁_c0 hx₁_c1 hx₁_c2
          (fun y₁ hy₁_r hy₁_csr hy₁_vis hy₁_p hy₁_fc hy₁_fin hy₁_v hy₁_out hy₁_fr => by
            rw [hsc_def] at hy₁_vis hy₁_fc hy₁_fin hy₁_v hy₁_out
            have hy₁_vis' : VisAt s₁.visited visAddr y₁.mem := by rw [hs₁_eq]; exact hy₁_vis
            have hy₁_fc' : y₁.regs finCnt = F₀ + s₁.finished.length := by
              rw [hlen_s₁]; exact hy₁_fc
            have hy₁_d0 : y₁.mem (stkAddr + 3 * d) = u.val :=
              (hy₁_out (stkAddr + 3 * d) (by omega)).trans hx₁_d0
            have hy₁_d1 : y₁.mem (stkAddr + 3 * d + 1) = csrOffset adj u.val + (idx + 1) :=
              (hy₁_out (stkAddr + 3 * d + 1) (by omega)).trans hx₁_d1
            have hy₁_d2 : y₁.mem (stkAddr + 3 * d + 2) = csrOffset adj (u.val + 1) :=
              (hy₁_out (stkAddr + 3 * d + 2) (by omega)).trans hx₁_d2
            rw [← hs₂_def]
            exact ih_es (idx + 1) d (F₀ + s₁.finished.length) T_cont s₁.visited y₁ Q
              (by omega) hes' hk_s₁ hcons_after hy₁_r hy₁_csr hy₁_vis' hy₁_p hy₁_fc'
              hy₁_d0 hy₁_d1 hy₁_d2
              (fun y₂ hy₂_r hy₂_csr hy₂_vis hy₂_p hy₂_fc hy₂_fin hy₂_u hy₂_out hy₂_fr => by
                rw [hs₂_def] at hy₂_vis hy₂_fc hy₂_fin hy₂_u hy₂_out
                have hy₂_vis' : VisAt (foldEmpty adj (k' + 1) (v :: es') vis).visited
                    visAddr y₂.mem := by
                  rw [hfold_cons]; exact hy₂_vis
                have hy₂_fc' : y₂.regs finCnt =
                    F₀ + (foldEmpty adj (k' + 1) (v :: es') vis).finished.length + 1 := by
                  rw [hfold_cons]; dsimp only; rw [List.length_append]; omega
                have hy₂_u' : y₂.mem (finAddr + F₀ +
                    (foldEmpty adj (k' + 1) (v :: es') vis).finished.length) = u.val := by
                  rw [hfold_cons]; dsimp only; rw [List.length_append]
                  rw [show finAddr + F₀ + (s₂.finished.length + s₁.finished.length) =
                    finAddr + (F₀ + s₁.finished.length) + s₂.finished.length by omega]
                  exact hy₂_u
                have hy₂_fin_all :
                    ∀ q (hq : q < (foldEmpty adj (k' + 1) (v :: es') vis).finished.reverse.length),
                      y₂.mem (finAddr + F₀ + q) =
                        ((foldEmpty adj (k' + 1) (v :: es') vis).finished.reverse[q]).val := by
                  intro q hq
                  have hrev : (foldEmpty adj (k' + 1) (v :: es') vis).finished.reverse =
                      s_child.finished.reverse ++ [v] ++ s₂.finished.reverse := by
                    rw [hfold_cons, hs₁_eq]
                    simp only [List.reverse_append, List.reverse_cons, List.append_assoc]
                  have hrev2 : (foldEmpty adj (k' + 1) (v :: es') vis).finished.reverse =
                      s₁.finished.reverse ++ s₂.finished.reverse := by
                    rw [hfold_cons]; dsimp only; exact List.reverse_append
                  have hq_tot : q < s_child.finished.length + 1 + s₂.finished.length := by
                    rw [hrev] at hq
                    simp only [List.length_append, List.length_reverse,
                      List.length_singleton] at hq
                    omega
                  by_cases hq1 : q < s_child.finished.length
                  · have hpres : y₂.mem (finAddr + F₀ + q) = y₁.mem (finAddr + F₀ + q) :=
                      hy₂_out (finAddr + F₀ + q) (by omega)
                    rw [hpres, hy₁_fin q (by rw [List.length_reverse]; exact hq1)]
                    congr 1
                    simp only [hrev, List.append_assoc]
                    rw [List.getElem_append_left (by rw [List.length_reverse]; exact hq1)]
                  · by_cases hq2 : q = s_child.finished.length
                    · subst hq2
                      have hpres : y₂.mem (finAddr + F₀ + s_child.finished.length) =
                          y₁.mem (finAddr + F₀ + s_child.finished.length) :=
                        hy₂_out (finAddr + F₀ + s_child.finished.length) (by omega)
                      rw [hpres, hy₁_v]
                      congr 1
                      simp only [hrev, List.append_assoc]
                      rw [List.getElem_append_right (by rw [List.length_reverse])]
                      simp only [List.length_reverse, Nat.sub_self, List.singleton_append,
                        List.getElem_cons_zero]
                    · set q' := q - s₁.finished.length
                      have hq'_lt : q' < s₂.finished.reverse.length := by
                        rw [List.length_reverse]; omega
                      have haddr_eq :
                          finAddr + F₀ + q = finAddr + (F₀ + s₁.finished.length) + q' := by
                        omega
                      rw [haddr_eq, hy₂_fin q' hq'_lt]
                      congr 1
                      simp only [hrev2]
                      have hge : s₁.finished.reverse.length ≤ q := by
                        rw [List.length_reverse]; omega
                      rw [List.getElem_append_right hge]
                      congr 1
                      rw [List.length_reverse]
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
          have := hregs.czero
          change x.regs cZero < x.regs pReg; omega
        refine ⟨z, ⟨t₁ + t₂ + 2, ?_, Exec.loop_iter hlt he₁ he₂⟩, hQz⟩
        rw [hsc_def] at ht₂
        have hout_eq : outDegreeSum adj (foldEmpty adj (k' + 1) (v :: es') vis).finished =
            outDegreeSum adj s₂.finished +
              ((adj v).length + outDegreeSum adj s_child.finished) := by
          rw [hfold_cons, hs₁_eq]
          dsimp only
          rw [outDegreeSum_append]
          simp only [outDegreeSum, List.map_cons, List.sum_cons]
        have hlen_eq : (foldEmpty adj (k' + 1) (v :: es') vis).finished.length =
            s₂.finished.length + (1 + s_child.finished.length) := by
          rw [hfold_cons, hs₁_eq]; dsimp only; rw [List.length_append, List.length_cons]; omega
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
    have hs_eq : visit adj N r ⟨vis, []⟩ = ⟨vis, []⟩ :=
      (congrArg (fun fuel => visit adj fuel r ⟨vis, []⟩) hkN).trans (visit_of_mem hmem)
    unfold visitRootCode
    wram_exec [hregs.czero, hregs.hvis, hu, hvis_1, hf_vr]
    dsimp only [RootPost]
    rw [hs_eq]
    refine ⟨?_, ?_, ?_, ?_, fun _ hq => by simp at hq, fun _ _ => rfl, fun reg hreg => ?_⟩
    · refine dfsRegs_of_frame hregs fun reg hreg => ?_
      regs_lt
    · mem_upd; exact hcsr
    · intro w_v; mem_upd; exact hvis w_v
    · wram_simp; simpa using hfc
    · regs_lt
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
        ((x.set addr (visAddr + r.val)).set jReg 0) x₁ 11 ∧ PushRootPost x₁ := by
      unfold dfsPushRoot
      wram_exec [hregs.cone, hregs.hoff, hregs.hstk, hu, hoff_r0, hoff_r1,
        hf_or0, hf_or1, hf_s1, hf_s2]
      dsimp only [PushRootPost]
      refine ⟨?_, ?_, ?_, by wram_simp, by wram_simp; exact hfc,
        ?_, ?_, ?_, fun a ha => ?_, fun reg hreg => ?_⟩
      · refine dfsRegs_of_frame hregs fun reg hreg => ?_
        regs_lt
      · mem_upd
        exact hcsr.of_eqOn
          (fun _ _ => by repeat rw [Function.update_of_ne (by omega)])
          (fun _ _ => by repeat rw [Function.update_of_ne (by omega)])
      · intro w_v; mem_upd
        have hw_lt := w_v.isLt
        repeat rw [Function.update_of_ne (by omega)]
        exact visAt_insert hvis r w_v
      · mem_upd
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Nat.add_zero, Function.update_self]
      · mem_upd
        rw [Function.update_of_ne (by omega), Nat.mul_zero, Nat.add_zero, Function.update_self]
        omega
      · mem_upd
        rw [show stkAddr + 2 = stkAddr + 1 + 1 by omega, Function.update_self]
      · mem_upd
        repeat rw [Function.update_of_ne (by omega)]
      · have ha : reg ≠ addr := by reg_ne
        have hj : reg ≠ jReg := by reg_ne
        have hje : reg ≠ jEndReg := by reg_ne
        have hp' : reg ≠ pReg := by reg_ne
        simp only [Data.write_regs_apply, Data.set_regs_of_ne ha, Data.set_regs_of_ne hj,
          Data.set_regs_of_ne hje, Data.set_regs_of_ne hp']
    obtain ⟨x₁, hx₁_ex, hx₁_r, hx₁_csr, hx₁_vis, hx₁_p, hx₁_fc, hx₁_s0, hx₁_s1, hx₁_s2,
      hx₁_out, hx₁_fr⟩ := hpush
    have hs_eq : visit adj N r ⟨vis, []⟩ =
        ⟨(foldEmpty adj k' (adj r) vis₁).visited,
          r :: (foldEmpty adj k' (adj r) vis₁).finished⟩ :=
      (congrArg (fun fuel => visit adj fuel r ⟨vis, []⟩) hkN).trans (visit_eq_foldEmpty hmem)
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
        refine ⟨hy_r, hy_csr, hy_vis, by rw [List.length_cons, hy_fc]; omega,
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
          have h1 := hy_out a (by omega)
          have h0 := hx₁_out a (by omega)
          exact h1.trans h0)
    have hbound : 2 + 1 + 11 + t_loop ≤
        16 + 60 * (visit adj N r ⟨vis, []⟩).finished.length +
          36 * outDegreeSum adj (visit adj N r ⟨vis, []⟩).finished := by
      rw [hs_eq]
      simp only [dfsFrameTime, List.length_cons, outDegreeSum, List.map_cons,
        List.sum_cons] at ht_loop ⊢
      omega
    unfold visitRootCode
    wram_exec [hregs.czero, hregs.hvis, hu, hvis_0, hf_vr]
    refine WP.of_execWithin hx₁_ex ?_
    refine WP.of_execWithin ⟨t_loop, le_rfl, he_loop⟩ ?_
    exact ⟨by omega, hRz⟩


/-! ### Pass 1: Forward DFS finishing order (`O(N + M)`) -/

private def forwardDFSBody : Code .standard 28 :=
  (ram[ uReg ← iReg ]).seq (visitRootCode.seq (ram[ iReg ← iReg + cOne ]))

private def forwardDFSCode : Code .standard 28 :=
  (zeroBlockCode visB).seq
    ((ram[ finCnt ← cZero; iReg ← cZero ]).seq
      (.loop (.lt iReg nVerts) forwardDFSBody))

private theorem forwardDFSLoop_spec {N w : ℕ} (hN : 0 < N) (adj : Fin N → List (Fin N))
    (wb Mc : ℕ) (hmc : csrOffset adj N ≤ Mc)
    (hfit : Fits w (kTopAddr wb N Mc + Mc + 4)) :
    ∀ (rs : List (Fin N)) (idx : ℕ) (vis : Finset (Fin N)) (F₀ : ℕ) (x : Data 28)
      (_ : idx + rs.length = N),
      (∀ q (hq : q < rs.length), rs[q].val = idx + q) →
      F₀ = vis.card →
      DfsRegs (kOffAddr wb) (kEdgeAddr wb N) (kVisAddr wb N Mc) (kOrdAddr wb N Mc)
        (kStkAddr wb N Mc) x →
      CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x.mem →
      VisAt vis (kVisAddr wb N Mc) x.mem →
      x.regs nVerts = N →
      x.regs iReg = idx →
      x.regs finCnt = F₀ →
      ∃ y,
        let s := foldEmpty adj N rs vis
        ExecWithin w (.loop (.lt iReg nVerts) forwardDFSBody) x y
          (22 * rs.length + 60 * s.finished.length + 36 * outDegreeSum adj s.finished + 2) ∧
        DfsRegs (kOffAddr wb) (kEdgeAddr wb N) (kVisAddr wb N Mc) (kOrdAddr wb N Mc)
          (kStkAddr wb N Mc) y ∧
        CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) y.mem ∧
        VisAt s.visited (kVisAddr wb N Mc) y.mem ∧
        y.regs finCnt = F₀ + s.finished.length ∧
        (∀ q (hq : q < s.finished.reverse.length),
          y.mem (kOrdAddr wb N Mc + F₀ + q) = (s.finished.reverse[q]).val) ∧
        (∀ a, ¬ ((kVisAddr wb N Mc ≤ a ∧ a < kVisAddr wb N Mc + N) ∨
            (kOrdAddr wb N Mc + F₀ ≤ a ∧ a < kOrdAddr wb N Mc + F₀ + s.finished.length) ∨
            (kStkAddr wb N Mc ≤ a ∧ a < kStkAddr wb N Mc + 3 * N)) → y.mem a = x.mem a) ∧
        (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r)
  | [], idx, vis, F₀, x, hidx, _, _, hregs, hcsr, hvis, hNv, hi, hfc => by
    simp only [List.length_nil, Nat.add_zero] at hidx
    have hend : ¬ (Cond.lt iReg nVerts).Holds x := by
      change ¬ x.regs iReg < x.regs nVerts; omega
    refine ⟨x, ⟨2, by simp [foldEmpty, outDegreeSum], Exec.loop_exit hend⟩,
      hregs, hcsr, hvis, by simpa [foldEmpty] using hfc,
      fun _ hq => by simp [foldEmpty] at hq, fun _ _ => rfl, fun _ _ => rfl⟩
  | r :: rs, idx, vis, F₀, x, hidx, hrs, hF₀, hregs, hcsr, hvis, hNv, hi, hfc => by
    simp only [List.length_cons] at hidx
    have hr_val : r.val = idx := by
      have h0 := hrs 0 (by simp)
      rwa [List.getElem_cons_zero, Nat.add_zero] at h0
    have hcard_le : vis.card ≤ N := by have := Finset.card_le_univ vis; simpa using this
    have hcons : F₀ + (N - vis.card) ≤ N := by omega
    have hfit_stk : Fits w (kStkAddr wb N Mc + 3 * N + Mc + 4) :=
      hfit.of_le (by simp only [kStkAddr, kTopAddr]; omega)
    let st_u := x.set uReg idx
    obtain ⟨y₁, hy₁_ex, hy₁_r, hy₁_csr, hy₁_vis, hy₁_fc, hy₁_ord, hy₁_out, hy₁_fr⟩ :=
      visitRootCode_spec hN adj (kOffAddr wb) (kEdgeAddr wb N) (kVisAddr wb N Mc)
        (kOrdAddr wb N Mc) (kStkAddr wb N Mc) Mc
        (by simp only [kOffAddr, kVisAddr]; omega)
        (by simp only [kEdgeAddr, kVisAddr]; omega)
        (by simp only [kVisAddr, kOrdAddr]; omega)
        (by simp only [kOrdAddr, kStkAddr]; omega)
        hmc hfit_stk r F₀ vis hcons (x := st_u)
        (dfsRegs_of_frame hregs fun reg hreg => by
          dsimp only [st_u]; regs_lt)
        hcsr hvis (by dsimp only [st_u]; wram_simp; omega)
        (by dsimp only [st_u]; wram_simp; exact hfc)
    set s₁ := visit adj N r ⟨vis, []⟩
    have hy₁_i : y₁.regs iReg = idx :=
      (hy₁_fr iReg (.inl (by decide))).trans (by dsimp only [st_u]; wram_simp; exact hi)
    have hy₁_1 : y₁.regs cOne = 1 := hy₁_r.cone
    have hf_i1 : Fits w (idx + 1) := hfit.of_le (by simp only [kTopAddr]; omega)
    have hbody_ex : ExecWithin w forwardDFSBody x (y₁.set iReg (idx + 1))
        (18 + 60 * s₁.finished.length + 36 * outDegreeSum adj s₁.finished) := by
      have h1 : ExecWithin (B := .standard) w (ram[ uReg ← iReg ]) x st_u 1 := by
        have htriv : st_u = x.set uReg idx := rfl
        wram_exec [hi]
      have h2 : ExecWithin w (ram[ iReg ← iReg + cOne ]) y₁ (y₁.set iReg (idx + 1)) 1 := by
        wram_exec [hy₁_i, hy₁_1, hf_i1]
      exact (h1.seq (hy₁_ex.seq h2)).mono (by omega)
    set x₂ := y₁.set iReg (idx + 1)
    have hcard_s₁ : s₁.visited.card = vis.card + s₁.finished.length :=
      card_visit_nil adj N r vis
    have hcard_s₁_le : s₁.visited.card ≤ N := by
      have := Finset.card_le_univ s₁.visited; simpa using this
    have hrs' : ∀ q (hq : q < rs.length), rs[q].val = (idx + 1) + q := by
      intro q hq
      have h := hrs (q + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 q] using h
    obtain ⟨y, hy_ex, hy_r, hy_csr, hy_vis, hy_fc, hy_ord, hy_out, hy_fr⟩ :=
      forwardDFSLoop_spec hN adj wb Mc hmc hfit rs (idx + 1) s₁.visited
        (F₀ + s₁.finished.length) x₂ (by omega) hrs' (by omega)
        (dfsRegs_of_frame hy₁_r fun reg hreg => by
          dsimp only [x₂]; regs_lt)
        hy₁_csr hy₁_vis
        (by
          dsimp only [x₂]; wram_simp
          exact (hy₁_fr nVerts (.inl (by decide))).trans
            (by dsimp only [st_u]; wram_simp; exact hNv))
        (by dsimp only [x₂]; wram_simp)
        (by dsimp only [x₂]; wram_simp; exact hy₁_fc)
    set s₂ := foldEmpty adj N rs s₁.visited
    have hfold_cons : foldEmpty adj N (r :: rs) vis =
        ⟨s₂.visited, s₂.finished ++ s₁.finished⟩ :=
      foldEmpty_cons adj N r rs vis
    obtain ⟨t₁, ht₁, he₁⟩ := hbody_ex
    obtain ⟨t₂, ht₂, he₂⟩ := hy_ex
    have hlt : (Cond.lt iReg nVerts).Holds x := by
      change x.regs iReg < x.regs nVerts; omega
    refine ⟨y, ⟨t₁ + t₂ + 2, ?_, Exec.loop_iter hlt he₁ he₂⟩, hy_r, hy_csr,
      by simpa [hfold_cons] using hy_vis,
      by rw [hfold_cons]; dsimp only; rw [List.length_append]; omega,
      fun q hq => ?_, fun a ha => ?_, fun reg hreg => ?_⟩
    · rw [hfold_cons]; dsimp only
      rw [List.length_cons, List.length_append, outDegreeSum_append]
      omega
    · have hrev : (foldEmpty adj N (r :: rs) vis).finished.reverse =
          s₁.finished.reverse ++ s₂.finished.reverse := by
        simp [hfold_cons]
      simp only [hrev, List.length_append, List.length_reverse] at hq
      by_cases hq1 : q < s₁.finished.length
      · have hpres : y.mem (kOrdAddr wb N Mc + F₀ + q) = y₁.mem (kOrdAddr wb N Mc + F₀ + q) :=
          hy_out (kOrdAddr wb N Mc + F₀ + q) (by
            dsimp only [kVisAddr, kOrdAddr, kStkAddr] at *; omega)
        rw [hpres, hy₁_ord q (by simpa using hq1)]
        congr 1
        simp only [hrev]
        rw [List.getElem_append_left (by simpa using hq1)]
      · set q' := q - s₁.finished.length
        have hq'_lt : q' < s₂.finished.reverse.length := by simp; omega
        have haddr : kOrdAddr wb N Mc + F₀ + q =
            kOrdAddr wb N Mc + (F₀ + s₁.finished.length) + q' := by omega
        rw [haddr, hy_ord q' hq'_lt]
        congr 1
        simp only [hrev]
        rw [List.getElem_append_right (by simp; omega)]
        simp [q']
    · rw [hfold_cons] at ha; dsimp only at ha; rw [List.length_append] at ha
      have h2 := hy_out a (by dsimp only [kVisAddr, kOrdAddr, kStkAddr] at *; omega)
      have h1 := hy₁_out a (by dsimp only [kVisAddr, kOrdAddr, kStkAddr] at *; omega)
      exact h2.trans h1
    · have h2 := hy_fr reg hreg
      have h1 := hy₁_fr reg (.inl (by omega))
      have hne_i : reg ≠ iReg := by reg_ne
      have hne_u : reg ≠ uReg := by reg_ne
      dsimp only [x₂] at h2
      rw [h2, Data.set_regs_of_ne hne_i, h1]
      dsimp only [st_u]
      exact Data.set_regs_of_ne hne_u _

private theorem length_topologicalSort_finRange {N : ℕ} (adj : Fin N → List (Fin N)) :
    (topologicalSort adj (List.finRange N)).length = N := by
  have hnd := nodup_topologicalSort (adj := adj) List.mem_finRange
  have huniv : (topologicalSort adj (List.finRange N)).toFinset = Finset.univ := by
    ext v; simp [mem_topologicalSort List.mem_finRange]
  rw [← List.toFinset_card_of_nodup hnd, huniv]
  simp

private theorem forwardDFSCode_spec {N w : ℕ} (hN : 0 < N) (adj : Fin N → List (Fin N))
    (wb Mc : ℕ) (hmc : csrOffset adj N ≤ Mc)
    (hfit : Fits w (kTopAddr wb N Mc + Mc + 4)) {x : Data 28}
    (hregs : DfsRegs (kOffAddr wb) (kEdgeAddr wb N) (kVisAddr wb N Mc) (kOrdAddr wb N Mc)
      (kStkAddr wb N Mc) x)
    (hNv : x.regs nVerts = N)
    (hcsr : CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x.mem) :
    let ord := topologicalSort adj (List.finRange N)
    ∃ y, ExecWithin w forwardDFSCode x y (87 * N + 36 * Mc + 10) ∧
      ord.length = N ∧
      (∀ idx (hidx : idx < N),
        y.mem (kOrdAddr wb N Mc + (N - 1 - idx)) =
          (ord[idx]'(by rw [length_topologicalSort_finRange]; exact hidx)).val) ∧
      CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) y.mem ∧
      (∀ a, ¬ ((kVisAddr wb N Mc ≤ a ∧ a < kVisAddr wb N Mc + N) ∨
          (kOrdAddr wb N Mc ≤ a ∧ a < kOrdAddr wb N Mc + N) ∨
          (kStkAddr wb N Mc ≤ a ∧ a < kStkAddr wb N Mc + 3 * N)) → y.mem a = x.mem a) ∧
      (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r) := by
  have hfit_vis : Fits w (kVisAddr wb N Mc + N) :=
    hfit.of_le (by simp only [kVisAddr, kTopAddr]; omega)
  obtain ⟨x₁, hx₁_ex, hx₁_zero, hx₁_out, hx₁_fr⟩ :=
    zeroBlockCode_spec visB (by decide) (kVisAddr wb N Mc) N hfit_vis hregs.czero hregs.cone
      hregs.hvis hNv
  have hx₁_csr : CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x₁.mem :=
    hcsr.of_eqOn
      (fun _ _ => hx₁_out _ (by dsimp only [kOffAddr, kVisAddr]; omega))
      (fun _ _ => hx₁_out _ (by dsimp only [kEdgeAddr, kVisAddr]; omega))
  have hx₁_vis : VisAt (∅ : Finset (Fin N)) (kVisAddr wb N Mc) x₁.mem := by
    intro w_v; simp [hx₁_zero w_v.val w_v.isLt]
  have hx₁_r := dfsRegs_of_frame hregs hx₁_fr
  let x₂ := (x₁.set finCnt 0).set iReg 0
  have hprep : ExecWithin (B := .standard) w (ram[ finCnt ← cZero; iReg ← cZero ]) x₁ x₂ 2 := by
    have hc0 := hx₁_r.czero
    wram_exec [hc0]
  obtain ⟨y, hy_ex, -, hy_csr, -, -, hy_ord, hy_out, hy_fr⟩ :=
    forwardDFSLoop_spec hN adj wb Mc hmc hfit (List.finRange N) 0 ∅ 0 x₂ (by simp)
      (fun q hq => by simp) rfl
      (dfsRegs_of_frame hx₁_r fun reg hreg => by
        dsimp only [x₂]; regs_lt)
      hx₁_csr hx₁_vis
      (by dsimp only [x₂]; wram_simp; exact (hx₁_fr nVerts (by decide)).trans hNv)
      (by dsimp only [x₂]; wram_simp)
      (by dsimp only [x₂]; wram_simp)
  set ord := topologicalSort adj (List.finRange N)
  have hfold_eq : (foldEmpty adj N (List.finRange N) ∅).finished = ord := by
    simp [foldEmpty, ord, topologicalSort, dfs]
  have hnd_ord : ord.Nodup := nodup_topologicalSort List.mem_finRange
  have hmem_ord : ∀ v : Fin N, v ∈ ord := mem_topologicalSort List.mem_finRange
  have huniv_ord : ord.toFinset = Finset.univ := by ext v; simp [hmem_ord v]
  have hlen_ord : ord.length = N := length_topologicalSort_finRange adj
  have hout_ord : outDegreeSum adj ord = csrOffset adj N := by
    rw [csrOffset_eq_outDegreeSum]
    unfold outDegreeSum
    rw [← List.sum_toFinset _ hnd_ord, ← List.sum_toFinset _ (List.nodup_finRange N), huniv_ord]
    have huniv2 : (List.finRange N).toFinset = Finset.univ := by ext v; simp
    rw [huniv2]
  rw [hfold_eq] at hy_ex hy_ord hy_out
  rw [hlen_ord, hout_ord] at hy_ex
  simp only [List.length_finRange, Nat.add_zero] at hy_ex hy_ord hy_out
  refine ⟨y, (hx₁_ex.seq (hprep.seq hy_ex)).mono (by omega), hlen_ord,
    fun idx hidx => ?_, hy_csr, fun a ha => ?_, fun r hr => ?_⟩
  · have hrev_idx : N - 1 - idx < ord.reverse.length := by simp [hlen_ord]; omega
    rw [hy_ord (N - 1 - idx) hrev_idx]
    congr 1
    rw [List.getElem_reverse]
    congr 1
    omega
  · rw [hlen_ord] at hy_out
    exact (hy_out a ha).trans (hx₁_out a (by omega))
  · have h2 := hy_fr r hr
    dsimp only [x₂] at h2
    have hne1 : r ≠ iReg := by reg_ne
    have hne2 : r ≠ finCnt := by reg_ne
    rw [h2, Data.set_regs_of_ne hne1, Data.set_regs_of_ne hne2]
    exact hx₁_fr r hr

/-! ### Building the implication-graph CSR (`O(n + |φ|)`) -/

private def buildImplCSRCode : Code .standard 28 :=
  (zeroBlockCode curB).seq
    ((ram[ iReg ← cZero; pReg ← cThree ]).seq
      ((Code.loop (.lt iReg mClauses) implDegBody).seq
        (prefixSumCode.seq
          ((ram[ iReg ← cZero; pReg ← cThree ]).seq
            (Code.loop (.lt iReg mClauses) implFillBody)))))

private theorem buildImplCSRCode_spec (G : Instance) {w : ℕ} (hfit : Fits w G.wordBound)
    (hcs : ∀ c ∈ G.φ, 1 ≤ c.length ∧ c.length ≤ 2) {x : Data 28}
    (hcm : ClauseMemAt x.mem 3 G.φ)
    (hc0 : x.regs cZero = 0) (hc1 : x.regs cOne = 1) (hc3 : x.regs cThree = 3)
    (hm : x.regs mClauses = G.φ.length) (hNv : x.regs nVerts = 2 * G.n)
    (hoffB : x.regs offB = kOffAddr G.workBase)
    (hedgeB : x.regs edgeB = kEdgeAddr G.workBase (2 * G.n))
    (hcurB : x.regs curB = kCurAddr G.workBase (2 * G.n) (2 * G.φ.length)) :
    ∃ y, ExecWithin w buildImplCSRCode x y (26 * G.n + 49 * G.φ.length + 18) ∧
      CSRAt G.adjFin (kOffAddr G.workBase) (kEdgeAddr G.workBase (2 * G.n)) y.mem ∧
      (∀ a, a < G.workBase → y.mem a = x.mem a) ∧
      (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r) := by
  set N := 2 * G.n
  set Mc := 2 * G.φ.length
  set curBase := kCurAddr G.workBase N Mc
  set offBase := kOffAddr G.workBase
  set edgeBase := kEdgeAddr G.workBase N
  have hfit_cur : Fits w (curBase + N) :=
    G.fits_of_le hfit (by
      simp only [curBase, N, Mc, kCurAddr, Instance.workBase, Instance.outAddrBase,
        G.encode_length, Instance.wordBound]; omega)
  obtain ⟨x₁, hx₁_ex, hx₁_zero, hx₁_out, hx₁_fr⟩ :=
    zeroBlockCode_spec curB (by decide) curBase N hfit_cur hc0 hc1 hcurB hNv
  have hcm₁ : ClauseMemAt x₁.mem 3 G.φ := by
    intro k hk
    rw [hx₁_out _ (by
      rw [Instance.length_flatMap_encodeClauseBy] at hk
      simp only [curBase, kCurAddr, Instance.workBase, Instance.outAddrBase, G.encode_length]
      unfold Instance.totalLits at *; omega)]
    exact hcm k hk
  let x₂ := (x₁.set iReg 0).set pReg 3
  have hp₁ : ExecWithin (B := .standard) w (ram[ iReg ← cZero; pReg ← cThree ]) x₁ x₂ 2 := by
    have h0' : x₁.regs cZero = 0 := (hx₁_fr cZero (by decide)).trans hc0
    have h3' : x₁.regs cThree = 3 := (hx₁_fr cThree (by decide)).trans hc3
    wram_exec [h0', h3']
  have hlen_enc : 3 + (G.φ.flatMap (encodeClauseBy Fin.val)).length = G.encode.length + 1 := by
    rw [Instance.length_flatMap_encodeClauseBy, G.encode_length]
    unfold Instance.totalLits; omega
  obtain ⟨x₃, hx₃_ex, hx₃_deg, hx₃_out, hx₃_fr⟩ :=
    implDegLoop_spec G hfit G.φ (fun _ => []) 0 3 x₂ hcs (.inr rfl) (by simp) hlen_enc hcm₁
      (fun u => by dsimp only [x₂]; simpa [mapAdj] using hx₁_zero u.val u.isLt)
      (by dsimp only [x₂]; wram_simp; exact (hx₁_fr cOne (by decide)).trans hc1)
      (by dsimp only [x₂]; wram_simp; exact (hx₁_fr mClauses (by decide)).trans hm)
      (by dsimp only [x₂]; wram_simp; exact (hx₁_fr curB (by decide)).trans hcurB)
      (by dsimp only [x₂]; wram_simp)
      (by dsimp only [x₂]; wram_simp)
  have hx₃_fr0 : ∀ r : Fin 28, r.val < 18 → x₃.regs r = x.regs r := fun r hr => by
    have h3 := hx₃_fr r hr
    have hne1 : r ≠ pReg := by reg_ne
    have hne2 : r ≠ iReg := by reg_ne
    dsimp only [x₂] at h3
    rw [h3, Data.set_regs_of_ne hne1, Data.set_regs_of_ne hne2]
    exact hx₁_fr r hr
  have hfit_ps : Fits w (curBase + N + Mc + 2) :=
    G.fits_of_le hfit (by
      simp only [curBase, N, Mc, kCurAddr, Instance.workBase, Instance.outAddrBase,
        G.encode_length, Instance.wordBound]; omega)
  obtain ⟨x₄, hx₄_ex, hx₄_off, hx₄_cur, hx₄_out, hx₄_fr⟩ :=
    prefixSumCode_spec G.adjFin curBase offBase Mc
      (by simp only [offBase, curBase, kOffAddr, kCurAddr]; omega)
      (csrOffset_adjFin_le G) hfit_ps
      ((hx₃_fr0 cZero (by decide)).trans hc0)
      ((hx₃_fr0 cOne (by decide)).trans hc1)
      ((hx₃_fr0 curB (by decide)).trans hcurB)
      ((hx₃_fr0 offB (by decide)).trans hoffB)
      ((hx₃_fr0 nVerts (by decide)).trans hNv)
      hx₃_deg
  have hx₄_fr0 : ∀ r : Fin 28, r.val < 18 → x₄.regs r = x.regs r :=
    fun r hr => (hx₄_fr r hr).trans (hx₃_fr0 r hr)
  have hcm₄ : ClauseMemAt x₄.mem 3 G.φ := by
    intro k hk
    have hk_lt : 3 + k < G.workBase := by
      rw [Instance.length_flatMap_encodeClauseBy] at hk
      simp only [Instance.workBase, Instance.outAddrBase, G.encode_length]
      unfold Instance.totalLits at *; omega
    rw [hx₄_out _ (by dsimp only [offBase, curBase, N, Mc]; simp only [kOffAddr, kCurAddr]; omega),
      hx₃_out _ (by dsimp only [kCurAddr]; omega)]
    exact hcm₁ k hk
  let x₅ := (x₄.set iReg 0).set pReg 3
  have hp₂ : ExecWithin (B := .standard) w (ram[ iReg ← cZero; pReg ← cThree ]) x₄ x₅ 2 := by
    have h0' : x₄.regs cZero = 0 := (hx₄_fr0 cZero (by decide)).trans hc0
    have h3' : x₄.regs cThree = 3 := (hx₄_fr0 cThree (by decide)).trans hc3
    wram_exec [h0', h3']
  have hmap_empty : mapAdj (litEquiv G.n) (fun _ => []) = (fun _ => []) := funext fun _ => rfl
  obtain ⟨y, hy_ex, hy_pcsr, hy_out, hy_fr⟩ :=
    implFillLoop_spec G hfit G.φ (fun _ => []) 0 3 x₅ hcs (.inr rfl) (by simp) hlen_enc hcm₄
      (hmap_empty ▸ partialCSRAt_init G.adjFin curBase edgeBase x₄.mem hx₄_cur)
      (by dsimp only [x₅]; wram_simp; exact (hx₄_fr0 cOne (by decide)).trans hc1)
      (by dsimp only [x₅]; wram_simp; exact (hx₄_fr0 mClauses (by decide)).trans hm)
      (by dsimp only [x₅]; wram_simp; exact (hx₄_fr0 curB (by decide)).trans hcurB)
      (by dsimp only [x₅]; wram_simp; exact (hx₄_fr0 edgeB (by decide)).trans hedgeB)
      (by dsimp only [x₅]; wram_simp)
      (by dsimp only [x₅]; wram_simp)
  have hy_off : ∀ u ≤ N, y.mem (offBase + u) = csrOffset G.adjFin u := fun u hu => by
    rw [hy_out _ (by dsimp only [offBase, N, kOffAddr, kCurAddr, kEdgeAddr]; omega)]
    exact hx₄_off u hu
  have hy_csr : CSRAt G.adjFin offBase edgeBase y.mem :=
    csrAt_of_partialCSRAt G.adjFin offBase curBase edgeBase y.mem hy_off hy_pcsr
  refine ⟨y,
    (hx₁_ex.seq (hp₁.seq (hx₃_ex.seq (hx₄_ex.seq (hp₂.seq hy_ex))))).mono
      (by dsimp only [N]; omega),
    hy_csr, fun a ha => ?_, fun r hr => ?_⟩
  · rw [hy_out _ (by dsimp only [kCurAddr, kEdgeAddr]; omega)]
    dsimp only [x₅]; mem_upd
    rw [hx₄_out _ (by dsimp only [offBase, curBase, N, Mc, kOffAddr, kCurAddr]; omega),
      hx₃_out _ (by dsimp only [kCurAddr]; omega)]
    dsimp only [x₂]; mem_upd
    exact hx₁_out _ (by dsimp only [curBase, N, Mc, kCurAddr]; omega)
  · have h5 := hy_fr r hr
    have hne1 : r ≠ pReg := by reg_ne
    have hne2 : r ≠ iReg := by reg_ne
    dsimp only [x₅] at h5
    rw [h5, Data.set_regs_of_ne hne1, Data.set_regs_of_ne hne2]
    exact hx₄_fr0 r hr

/-! ### Pass 2: CSR transpose construction (`O(N + M)`) -/

private def revDegInnerBody : Code .standard 28 :=
  (ram[ addr ← edgeB + jReg; vReg ← *addr ]).seq
    (incCurCode.seq (ram[ jReg ← jReg + cOne ]))

private def revDegOuterBody : Code .standard 28 :=
  (ram[ addr ← offB + iReg; jReg ← *addr; addr ← addr + cOne; oldFinReg ← *addr ]).seq
    ((Code.loop (.lt jReg oldFinReg) revDegInnerBody).seq
      (ram[ iReg ← iReg + cOne ]))

private def revFillInnerBody : Code .standard 28 :=
  (ram[ addr ← finCnt + jReg; vReg ← *addr ]).seq
    (backfillStepCode.seq (ram[ jReg ← jReg + cOne ]))

private def revFillOuterBody : Code .standard 28 :=
  (ram[ addr ← offB + uReg; jReg ← *addr; addr ← addr + cOne; oldFinReg ← *addr ]).seq
    ((Code.loop (.lt jReg oldFinReg) revFillInnerBody).seq
      (ram[ uReg ← uReg + cOne ]))

private def transposeCSRCode : Code .standard 28 :=
  (zeroBlockCode curB).seq
    ((ram[ iReg ← cZero ]).seq
      ((Code.loop (.lt iReg nVerts) revDegOuterBody).seq
        ((ram[ compIdxReg ← offB; offB ← revOffB ]).seq
          (prefixSumCode.seq
            ((ram[ offB ← compIdxReg; finCnt ← edgeB; edgeB ← revEdgeB; uReg ← cZero ]).seq
              ((Code.loop (.lt uReg nVerts) revFillOuterBody).seq
                (ram[ offB ← revOffB ])))))))

private theorem length_foldl_rev_le {N : ℕ} (u : Fin N) :
    ∀ (es : List (Fin N)) (rev : Fin N → List (Fin N)) (w : Fin N),
      (rev w).length ≤
        (es.foldl (fun r v => Function.update r v (u :: r v)) rev w).length
  | [], _, _ => le_rfl
  | v :: es, rev, w => by
    have h1 : (rev w).length ≤ (Function.update rev v (u :: rev v) w).length := by
      by_cases hw : w = v <;> simp [hw]
    exact h1.trans (length_foldl_rev_le u es (Function.update rev v (u :: rev v)) w)

private theorem length_foldl_vs_rev_le {N : ℕ} (adj : Fin N → List (Fin N)) :
    ∀ (us : List (Fin N)) (rev : Fin N → List (Fin N)) (w : Fin N),
      (rev w).length ≤
        (us.foldl (fun r u => (adj u).foldl (fun r v => Function.update r v (u :: r v)) r)
          rev w).length
  | [], _, _ => le_rfl
  | u :: us, rev, w =>
    (length_foldl_rev_le u (adj u) rev w).trans
      (length_foldl_vs_rev_le adj us _ w)

private abbrev revGraph {N : ℕ} (adj : Fin N → List (Fin N)) : Fin N → List (Fin N) :=
  transposeAdj adj (List.finRange N)

private theorem csrOffset_transposeAdj_eq {N : ℕ} (adj : Fin N → List (Fin N)) :
    csrOffset (transposeAdj adj (List.finRange N)) N = csrOffset adj N := by
  rw [csrOffset_eq_outDegreeSum, csrOffset_eq_outDegreeSum, outDegreeSum, ← Fin.sum_univ_def,
    sum_length_transposeAdj]

private theorem revDegInner_spec {N w : ℕ} (adj : Fin N → List (Fin N))
    (wb Mc : ℕ) (hmc : csrOffset adj N ≤ Mc)
    (hfit : Fits w (kTopAddr wb N Mc + Mc + 4)) (u : Fin N) :
    ∀ (es : List (Fin N)) (k : ℕ) (rev : Fin N → List (Fin N)) (x : Data 28)
      (_ : k + es.length = (adj u).length),
      (∀ q (hq : q < es.length), (adj u)[k + q]'(by omega) = es[q]) →
      (∀ z : Fin N,
        (es.foldl (fun r v => Function.update r v (u :: r v)) rev z).length ≤ Mc) →
      (∀ z : Fin N, x.mem (kCurAddr wb N Mc + z.val) = (rev z).length) →
      CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x.mem →
      x.regs cOne = 1 →
      x.regs edgeB = kEdgeAddr wb N →
      x.regs curB = kCurAddr wb N Mc →
      x.regs jReg = csrOffset adj u.val + k →
      x.regs oldFinReg = csrOffset adj u.val + (adj u).length →
      ∃ y, ExecWithin w (.loop (.lt jReg oldFinReg) revDegInnerBody) x y (9 * es.length + 2) ∧
        (∀ z : Fin N, y.mem (kCurAddr wb N Mc + z.val) =
          (es.foldl (fun r v => Function.update r v (u :: r v)) rev z).length) ∧
        (∀ a, ¬ (kCurAddr wb N Mc ≤ a ∧ a < kCurAddr wb N Mc + N) → y.mem a = x.mem a) ∧
        (∀ r : Fin 28, r ≠ addr → r ≠ jEndReg → r ≠ vReg → r ≠ jReg → y.regs r = x.regs r)
  | [], k, rev, x, hk, _, _, hdeg, _, _, _, _, hj, hof => by
    simp only [List.length_nil, Nat.add_zero] at hk
    have hend : ¬ (Cond.lt jReg oldFinReg).Holds x := by
      change ¬ x.regs jReg < x.regs oldFinReg; omega
    exact ⟨x, ⟨2, by simp, Exec.loop_exit hend⟩, hdeg, fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  | v :: es, k, rev, x, hk, hget, hroom_all, hdeg, hcsr, hc1, hedge, hcur, hj, hof => by
    simp only [List.length_cons] at hk
    have hk_lt : k < (adj u).length := by omega
    have hv_eq : (adj u)[k] = v := by
      have h0 := hget 0 (by simp)
      simpa only [Nat.add_zero, List.getElem_cons_zero] using h0
    have hmem_e : x.mem (kEdgeAddr wb N + (csrOffset adj u.val + k)) = v.val := by
      rw [← Nat.add_assoc, hcsr.2 u k hk_lt, hv_eq]
    have hj_lt_M : csrOffset adj u.val + k < csrOffset adj N := by
      have h1 := csrOffset_succ adj u.isLt; simp only [Fin.eta] at h1
      have h2 := csrOffset_mono adj (by omega : u.val + 1 ≤ N); omega
    have hf_eaddr : Fits w (kEdgeAddr wb N + (csrOffset adj u.val + k)) :=
      hfit.of_le (by simp only [kEdgeAddr, kTopAddr]; omega)
    have hf_j1 : Fits w (csrOffset adj u.val + k + 1) :=
      hfit.of_le (by simp only [kTopAddr]; omega)
    have hf_cur : Fits w (kCurAddr wb N Mc + N + Mc + 1) :=
      hfit.of_le (by simp only [kCurAddr, kTopAddr]; omega)
    have hroom_v : (rev v).length + 1 ≤ Mc := by
      have hle := length_foldl_rev_le u es (Function.update rev v (u :: rev v)) v
      have hall := hroom_all v
      simp only [List.foldl_cons] at hall
      simpa using hle.trans hall
    let st_v := (x.set addr (kEdgeAddr wb N + (csrOffset adj u.val + k))).set vReg v.val
    obtain ⟨y₁, hy₁_ex, hy₁_deg, hy₁_out, hy₁_fr⟩ :=
      incCurCode_spec (N := N) (kCurAddr wb N Mc) Mc hf_cur (fun z => (rev z).length) v hroom_v
        (x := st_v)
        (by dsimp only [st_v]; wram_simp; exact hc1)
        (by dsimp only [st_v]; wram_simp; exact hcur)
        (by dsimp only [st_v]; wram_simp)
        (by dsimp only [st_v]; exact hdeg)
    have hp1 : ExecWithin w (ram[ addr ← edgeB + jReg; vReg ← *addr ]) x st_v 2 := by
      have htriv :
          st_v = (x.set addr (kEdgeAddr wb N + (csrOffset adj u.val + k))).set vReg v.val := rfl
      wram_exec [hedge, hj, hmem_e, hf_eaddr]
    have hy₁_1 : y₁.regs cOne = 1 :=
      (hy₁_fr cOne (by decide) (by decide)).trans (by dsimp only [st_v]; wram_simp; exact hc1)
    have hy₁_j : y₁.regs jReg = csrOffset adj u.val + k :=
      (hy₁_fr jReg (by decide) (by decide)).trans (by dsimp only [st_v]; wram_simp; exact hj)
    let x₂ := y₁.set jReg (csrOffset adj u.val + (k + 1))
    have hp2 : ExecWithin w (ram[ jReg ← jReg + cOne ]) y₁ x₂ 1 := by
      have htriv : x₂ = y₁.set jReg (csrOffset adj u.val + k + 1) := by
        simp [x₂, Nat.add_assoc]
      rw [htriv]
      wram_exec [hy₁_j, hy₁_1, hf_j1]
    have hx₂_csr : CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x₂.mem :=
      hcsr.of_eqOn
        (fun _ _ => hy₁_out _ (by dsimp only [kOffAddr, kCurAddr]; omega))
        (fun _ _ => hy₁_out _ (by dsimp only [kEdgeAddr, kCurAddr]; omega))
    have hx₂_deg : ∀ z : Fin N, x₂.mem (kCurAddr wb N Mc + z.val) =
        (Function.update rev v (u :: rev v) z).length := by
      intro z; dsimp only [x₂]; mem_upd; rw [hy₁_deg z]
      by_cases hz : z = v <;> simp [hz]
    obtain ⟨y, hy_ex, hy_deg, hy_out, hy_fr⟩ :=
      revDegInner_spec adj wb Mc hmc hfit u es (k + 1) (Function.update rev v (u :: rev v)) x₂
        (by omega)
        (fun q hq => by
          have h := hget (q + 1) (by simp; omega)
          simpa [Nat.add_assoc, Nat.add_comm 1 q] using h)
        (fun z => by simpa [List.foldl_cons] using hroom_all z)
        hx₂_deg hx₂_csr
        (by dsimp only [x₂]; wram_simp; exact hy₁_1)
        (by
          dsimp only [x₂]; wram_simp
          exact (hy₁_fr edgeB (by decide) (by decide)).trans
            (by dsimp only [st_v]; wram_simp; exact hedge))
        (by
          dsimp only [x₂]; wram_simp
          exact (hy₁_fr curB (by decide) (by decide)).trans
            (by dsimp only [st_v]; wram_simp; exact hcur))
        (by dsimp only [x₂]; wram_simp)
        (by
          dsimp only [x₂]; wram_simp
          exact (hy₁_fr oldFinReg (by decide) (by decide)).trans
            (by dsimp only [st_v]; wram_simp; exact hof))
    have hbody_ex : ExecWithin w revDegInnerBody x x₂ 7 :=
      (hp1.seq (hy₁_ex.seq hp2)).mono (by omega)
    obtain ⟨t₁, ht₁, he₁⟩ := hbody_ex
    obtain ⟨t₂, ht₂, he₂⟩ := hy_ex
    have hlt : (Cond.lt jReg oldFinReg).Holds x := by
      change x.regs jReg < x.regs oldFinReg; omega
    refine ⟨y, ⟨t₁ + t₂ + 2, by simp only [List.length_cons]; omega, Exec.loop_iter hlt he₁ he₂⟩,
      hy_deg, fun a ha => (hy_out a ha).trans (hy₁_out a ha), fun r h1 h2 h3 h4 => ?_⟩
    rw [hy_fr r h1 h2 h3 h4]
    dsimp only [x₂]
    rw [Data.set_regs_of_ne h4, hy₁_fr r h1 h2]
    dsimp only [st_v]
    rw [Data.set_regs_of_ne h3, Data.set_regs_of_ne h1]

private theorem revDegOuter_spec {N w : ℕ} (adj : Fin N → List (Fin N))
    (wb Mc : ℕ) (hmc : csrOffset adj N ≤ Mc)
    (hfit : Fits w (kTopAddr wb N Mc + Mc + 4)) :
    ∀ (us : List (Fin N)) (idx : ℕ) (rev : Fin N → List (Fin N)) (x : Data 28)
      (_ : idx + us.length = N),
      (∀ q (hq : q < us.length), us[q].val = idx + q) →
      (∀ z : Fin N,
        (us.foldl (fun r u => (adj u).foldl (fun r v => Function.update r v (u :: r v)) r)
          rev z).length ≤ Mc) →
      (∀ z : Fin N, x.mem (kCurAddr wb N Mc + z.val) = (rev z).length) →
      CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x.mem →
      x.regs cOne = 1 → x.regs nVerts = N →
      x.regs offB = kOffAddr wb → x.regs edgeB = kEdgeAddr wb N →
      x.regs curB = kCurAddr wb N Mc → x.regs iReg = idx →
      ∃ y, ExecWithin w (.loop (.lt iReg nVerts) revDegOuterBody) x y
          (9 * us.length + 9 * outDegreeSum adj us + 2) ∧
        (∀ z : Fin N, y.mem (kCurAddr wb N Mc + z.val) =
          (us.foldl (fun r u => (adj u).foldl (fun r v => Function.update r v (u :: r v)) r)
            rev z).length) ∧
        (∀ a, ¬ (kCurAddr wb N Mc ≤ a ∧ a < kCurAddr wb N Mc + N) → y.mem a = x.mem a) ∧
        (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r)
  | [], idx, rev, x, hidx, _, _, hdeg, _, _, _, _, _, _, _ => by
    simp only [List.length_nil, Nat.add_zero] at hidx
    have hend : ¬ (Cond.lt iReg nVerts).Holds x := by
      change ¬ x.regs iReg < x.regs nVerts; omega
    exact ⟨x, ⟨2, by simp [outDegreeSum], Exec.loop_exit hend⟩,
      hdeg, fun _ _ => rfl, fun _ _ => rfl⟩
  | u :: us, idx, rev, x, hidx, hus, hroom_all, hdeg, hcsr, hc1, hNv, hoff, hedge, hcur, hi => by
    simp only [List.length_cons] at hidx
    have hu_val : u.val = idx := by
      have h0 := hus 0 (by simp)
      rwa [List.getElem_cons_zero, Nat.add_zero] at h0
    have hoff_u : x.mem (kOffAddr wb + idx) = csrOffset adj u.val := by
      rw [← hu_val]; exact hcsr.1 u.val (by omega)
    have hoff_u1 : x.mem (kOffAddr wb + idx + 1) = csrOffset adj u.val + (adj u).length := by
      simpa [← hu_val, Nat.add_assoc, csrOffset_succ adj u.isLt] using
        hcsr.1 (u.val + 1) (by omega)
    have hf_oa : Fits w (kOffAddr wb + idx) :=
      hfit.of_le (by simp only [kOffAddr, kTopAddr]; omega)
    have hf_oa1 : Fits w (kOffAddr wb + idx + 1) :=
      hfit.of_le (by simp only [kOffAddr, kTopAddr]; omega)
    have hf_i1 : Fits w (idx + 1) := hfit.of_le (by simp only [kTopAddr]; omega)
    let x₁ := (((x.set addr (kOffAddr wb + idx)).set jReg (csrOffset adj u.val)).set
      addr (kOffAddr wb + idx + 1)).set oldFinReg (csrOffset adj u.val + (adj u).length)
    have hp1 : ExecWithin w
        (ram[ addr ← offB + iReg; jReg ← *addr; addr ← addr + cOne; oldFinReg ← *addr ])
        x x₁ 4 := by
      have htriv : x₁ = (((x.set addr (kOffAddr wb + idx)).set jReg (csrOffset adj u.val)).set
        addr (kOffAddr wb + idx + 1)).set oldFinReg (csrOffset adj u.val + (adj u).length) := rfl
      wram_exec [hoff, hi, hc1, hoff_u, hoff_u1, hf_oa, hf_oa1]
    have hroom_u : ∀ z : Fin N,
        ((adj u).foldl (fun r v => Function.update r v (u :: r v)) rev z).length ≤ Mc := by
      intro z
      exact (length_foldl_vs_rev_le adj us _ z).trans
        (by simpa [List.foldl_cons] using hroom_all z)
    obtain ⟨y₁, hy₁_ex, hy₁_deg, hy₁_out, hy₁_fr⟩ :=
      revDegInner_spec adj wb Mc hmc hfit u (adj u) 0 rev x₁ (by simp) (fun q _ => by simp)
        hroom_u (by dsimp only [x₁]; exact hdeg) (by dsimp only [x₁]; exact hcsr)
        (by dsimp only [x₁]; wram_simp; exact hc1)
        (by dsimp only [x₁]; wram_simp; exact hedge)
        (by dsimp only [x₁]; wram_simp; exact hcur)
        (by dsimp only [x₁]; wram_simp)
        (by dsimp only [x₁]; wram_simp)
    have hy₁_i : y₁.regs iReg = idx :=
      (hy₁_fr iReg (by decide) (by decide) (by decide) (by decide)).trans
        (by dsimp only [x₁]; wram_simp; exact hi)
    have hy₁_1 : y₁.regs cOne = 1 :=
      (hy₁_fr cOne (by decide) (by decide) (by decide) (by decide)).trans
        (by dsimp only [x₁]; wram_simp; exact hc1)
    let x₂ := y₁.set iReg (idx + 1)
    have hp2 : ExecWithin w (ram[ iReg ← iReg + cOne ]) y₁ x₂ 1 := by
      wram_exec [hy₁_i, hy₁_1, hf_i1]
    have hx₂_csr : CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x₂.mem :=
      hcsr.of_eqOn
        (fun _ _ => hy₁_out _ (by dsimp only [kOffAddr, kCurAddr]; omega))
        (fun _ _ => hy₁_out _ (by dsimp only [kEdgeAddr, kCurAddr]; omega))
    have hx₂_fr0 : ∀ r : Fin 28, r.val < 18 → x₂.regs r = x.regs r := fun r hr => by
      have hne_i : r ≠ iReg := by reg_ne
      have hne_of : r ≠ oldFinReg := by reg_ne
      have hne_a : r ≠ addr := by reg_ne
      have hne_j : r ≠ jReg := by reg_ne
      dsimp only [x₂]
      rw [Data.set_regs_of_ne hne_i, hy₁_fr r hne_a (by reg_ne) (by reg_ne) hne_j]
      dsimp only [x₁]
      simp [Data.set_regs_of_ne hne_of, Data.set_regs_of_ne hne_a, Data.set_regs_of_ne hne_j]
    obtain ⟨y, hy_ex, hy_deg, hy_out, hy_fr⟩ :=
      revDegOuter_spec adj wb Mc hmc hfit us (idx + 1)
        ((adj u).foldl (fun r v => Function.update r v (u :: r v)) rev) x₂ (by omega)
        (fun q hq => by
          have h := hus (q + 1) (by simp; omega)
          simpa [Nat.add_assoc, Nat.add_comm 1 q] using h)
        (fun z => by simpa [List.foldl_cons] using hroom_all z)
        hy₁_deg hx₂_csr
        ((hx₂_fr0 cOne (by decide)).trans hc1)
        ((hx₂_fr0 nVerts (by decide)).trans hNv)
        ((hx₂_fr0 offB (by decide)).trans hoff)
        ((hx₂_fr0 edgeB (by decide)).trans hedge)
        ((hx₂_fr0 curB (by decide)).trans hcur)
        (by dsimp only [x₂]; wram_simp)
    have hbody_ex : ExecWithin w revDegOuterBody x x₂ (9 * (adj u).length + 7) :=
      (hp1.seq (hy₁_ex.seq hp2)).mono (by omega)
    obtain ⟨t₁, ht₁, he₁⟩ := hbody_ex
    obtain ⟨t₂, ht₂, he₂⟩ := hy_ex
    have hlt : (Cond.lt iReg nVerts).Holds x := by
      change x.regs iReg < x.regs nVerts; omega
    refine ⟨y, ⟨t₁ + t₂ + 2, ?_, Exec.loop_iter hlt he₁ he₂⟩,
      hy_deg, fun a ha => (hy_out a ha).trans (hy₁_out a ha),
      fun r hr => (hy_fr r hr).trans (hx₂_fr0 r hr)⟩
    simp only [List.length_cons, outDegreeSum, List.map_cons, List.sum_cons] at ht₂ ⊢
    omega

private theorem revFillInner_spec {N w : ℕ} (adj : Fin N → List (Fin N))
    (wb Mc : ℕ) (hmc : csrOffset adj N ≤ Mc)
    (hfit : Fits w (kTopAddr wb N Mc + Mc + 4)) (u : Fin N) :
    ∀ (es : List (Fin N)) (k : ℕ) (rev : Fin N → List (Fin N)) (x : Data 28)
      (_ : k + es.length = (adj u).length),
      (∀ q (hq : q < es.length), (adj u)[k + q]'(by omega) = es[q]) →
      (∀ z : Fin N,
        (es.foldl (fun r v => Function.update r v (u :: r v)) rev z).length ≤
          (revGraph adj z).length) →
      PartialCSRAt (revGraph adj) rev (kCurAddr wb N Mc) (kRevEdgeAddr wb N Mc) x.mem →
      CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x.mem →
      x.regs cOne = 1 →
      x.regs finCnt = kEdgeAddr wb N →
      x.regs edgeB = kRevEdgeAddr wb N Mc →
      x.regs curB = kCurAddr wb N Mc →
      x.regs uReg = u.val →
      x.regs jReg = csrOffset adj u.val + k →
      x.regs oldFinReg = csrOffset adj u.val + (adj u).length →
      ∃ y, ExecWithin w (.loop (.lt jReg oldFinReg) revFillInnerBody) x y (11 * es.length + 2) ∧
        PartialCSRAt (revGraph adj) (es.foldl (fun r v => Function.update r v (u :: r v)) rev)
          (kCurAddr wb N Mc) (kRevEdgeAddr wb N Mc) y.mem ∧
        (∀ a, ¬ ((kCurAddr wb N Mc ≤ a ∧ a < kCurAddr wb N Mc + N) ∨
            (kRevEdgeAddr wb N Mc ≤ a ∧ a < kRevEdgeAddr wb N Mc + csrOffset (revGraph adj) N)) →
          y.mem a = x.mem a) ∧
        (∀ r : Fin 28, r ≠ addr → r ≠ jEndReg → r ≠ vReg → r ≠ jReg → y.regs r = x.regs r)
  | [], k, rev, x, hk, _, _, hpcsr, _, _, _, _, _, _, hj, hof => by
    simp only [List.length_nil, Nat.add_zero] at hk
    have hend : ¬ (Cond.lt jReg oldFinReg).Holds x := by
      change ¬ x.regs jReg < x.regs oldFinReg; omega
    exact ⟨x, ⟨2, by simp, Exec.loop_exit hend⟩, hpcsr, fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  | v :: es, k, rev, x, hk, hget, hroom_all, hpcsr, hcsr, hc1, hfedge, hredge, hcur,
      huR, hj, hof => by
    set revAdj := revGraph adj
    simp only [List.length_cons] at hk
    have hk_lt : k < (adj u).length := by omega
    have hv_eq : (adj u)[k] = v := by
      have h0 := hget 0 (by simp)
      simpa only [Nat.add_zero, List.getElem_cons_zero] using h0
    have hmem_e : x.mem (kEdgeAddr wb N + (csrOffset adj u.val + k)) = v.val := by
      rw [← Nat.add_assoc, hcsr.2 u k hk_lt, hv_eq]
    have hj_lt_M : csrOffset adj u.val + k < csrOffset adj N := by
      have h1 := csrOffset_succ adj u.isLt; simp only [Fin.eta] at h1
      have h2 := csrOffset_mono adj (by omega : u.val + 1 ≤ N); omega
    have hf_eaddr : Fits w (kEdgeAddr wb N + (csrOffset adj u.val + k)) :=
      hfit.of_le (by simp only [kEdgeAddr, kTopAddr]; omega)
    have hf_j1 : Fits w (csrOffset adj u.val + k + 1) :=
      hfit.of_le (by simp only [kTopAddr]; omega)
    have hf_bf : Fits w (kCurAddr wb N Mc + N + Mc + 1) :=
      hfit.of_le (by simp only [kCurAddr, kTopAddr]; omega)
    have hmc_rev : csrOffset revAdj N ≤ Mc := by
      dsimp only [revAdj, revGraph]
      rwa [csrOffset_transposeAdj_eq]
    have hroom_v : (rev v).length + 1 ≤ (revAdj v).length := by
      have hle := length_foldl_rev_le u es (Function.update rev v (u :: rev v)) v
      have hall := hroom_all v
      simp only [List.foldl_cons] at hall
      simpa using hle.trans hall
    let st_v := (x.set addr (kEdgeAddr wb N + (csrOffset adj u.val + k))).set vReg v.val
    obtain ⟨y₁, hy₁_ex, hy₁_pcsr, hy₁_out, hy₁_fr⟩ :=
      backfillStepCode_spec revAdj rev (kCurAddr wb N Mc) (kRevEdgeAddr wb N Mc) Mc
        (by simp only [kRevEdgeAddr, kCurAddr]; omega) hmc_rev hf_bf v u hroom_v
        (x := st_v)
        (by dsimp only [st_v]; wram_simp; exact hc1)
        (by dsimp only [st_v]; wram_simp; exact hcur)
        (by dsimp only [st_v]; wram_simp; exact hredge)
        (by dsimp only [st_v]; wram_simp)
        (by dsimp only [st_v]; wram_simp; exact huR)
        (by dsimp only [st_v]; exact hpcsr)
    have hp1 : ExecWithin w (ram[ addr ← finCnt + jReg; vReg ← *addr ]) x st_v 2 := by
      have htriv :
          st_v = (x.set addr (kEdgeAddr wb N + (csrOffset adj u.val + k))).set vReg v.val := rfl
      wram_exec [hfedge, hj, hmem_e, hf_eaddr]
    have hy₁_1 : y₁.regs cOne = 1 :=
      (hy₁_fr cOne (by decide) (by decide)).trans (by dsimp only [st_v]; wram_simp; exact hc1)
    have hy₁_j : y₁.regs jReg = csrOffset adj u.val + k :=
      (hy₁_fr jReg (by decide) (by decide)).trans (by dsimp only [st_v]; wram_simp; exact hj)
    let x₂ := y₁.set jReg (csrOffset adj u.val + (k + 1))
    have hp2 : ExecWithin w (ram[ jReg ← jReg + cOne ]) y₁ x₂ 1 := by
      have htriv : x₂ = y₁.set jReg (csrOffset adj u.val + k + 1) := by
        simp [x₂, Nat.add_assoc]
      rw [htriv]
      wram_exec [hy₁_j, hy₁_1, hf_j1]
    have hx₂_csr : CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x₂.mem :=
      hcsr.of_eqOn
        (fun _ _ => hy₁_out _ (by dsimp only [kOffAddr, kCurAddr, kRevEdgeAddr]; omega))
        (fun _ _ => hy₁_out _ (by dsimp only [kEdgeAddr, kCurAddr, kRevEdgeAddr]; omega))
    obtain ⟨y, hy_ex, hy_pcsr, hy_out, hy_fr⟩ :=
      revFillInner_spec adj wb Mc hmc hfit u es (k + 1) (Function.update rev v (u :: rev v)) x₂
        (by omega)
        (fun q hq => by
          have h := hget (q + 1) (by simp; omega)
          simpa [Nat.add_assoc, Nat.add_comm 1 q] using h)
        (fun z => by simpa [List.foldl_cons] using hroom_all z)
        hy₁_pcsr hx₂_csr
        (by dsimp only [x₂]; wram_simp; exact hy₁_1)
        (by
          dsimp only [x₂]; wram_simp
          exact (hy₁_fr finCnt (by decide) (by decide)).trans
            (by dsimp only [st_v]; wram_simp; exact hfedge))
        (by
          dsimp only [x₂]; wram_simp
          exact (hy₁_fr edgeB (by decide) (by decide)).trans
            (by dsimp only [st_v]; wram_simp; exact hredge))
        (by
          dsimp only [x₂]; wram_simp
          exact (hy₁_fr curB (by decide) (by decide)).trans
            (by dsimp only [st_v]; wram_simp; exact hcur))
        (by
          dsimp only [x₂]; wram_simp
          exact (hy₁_fr uReg (by decide) (by decide)).trans
            (by dsimp only [st_v]; wram_simp; exact huR))
        (by dsimp only [x₂]; wram_simp)
        (by
          dsimp only [x₂]; wram_simp
          exact (hy₁_fr oldFinReg (by decide) (by decide)).trans
            (by dsimp only [st_v]; wram_simp; exact hof))
    have hbody_ex : ExecWithin w revFillInnerBody x x₂ 9 :=
      (hp1.seq (hy₁_ex.seq hp2)).mono (by omega)
    obtain ⟨t₁, ht₁, he₁⟩ := hbody_ex
    obtain ⟨t₂, ht₂, he₂⟩ := hy_ex
    have hlt : (Cond.lt jReg oldFinReg).Holds x := by
      change x.regs jReg < x.regs oldFinReg; omega
    refine ⟨y, ⟨t₁ + t₂ + 2, by simp only [List.length_cons]; omega, Exec.loop_iter hlt he₁ he₂⟩,
      hy_pcsr, fun a ha => (hy_out a ha).trans (hy₁_out a ha), fun r h1 h2 h3 h4 => ?_⟩
    rw [hy_fr r h1 h2 h3 h4]
    dsimp only [x₂]
    rw [Data.set_regs_of_ne h4, hy₁_fr r h1 h2]
    dsimp only [st_v]
    rw [Data.set_regs_of_ne h3, Data.set_regs_of_ne h1]

private theorem revFillOuter_spec {N w : ℕ} (adj : Fin N → List (Fin N))
    (wb Mc : ℕ) (hmc : csrOffset adj N ≤ Mc)
    (hfit : Fits w (kTopAddr wb N Mc + Mc + 4)) :
    ∀ (us : List (Fin N)) (idx : ℕ) (rev : Fin N → List (Fin N)) (x : Data 28)
      (_ : idx + us.length = N),
      (∀ q (hq : q < us.length), us[q].val = idx + q) →
      (∀ z : Fin N,
        (us.foldl (fun r u => (adj u).foldl (fun r v => Function.update r v (u :: r v)) r)
          rev z).length ≤ (revGraph adj z).length) →
      PartialCSRAt (revGraph adj) rev (kCurAddr wb N Mc) (kRevEdgeAddr wb N Mc) x.mem →
      CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x.mem →
      x.regs cOne = 1 → x.regs nVerts = N →
      x.regs offB = kOffAddr wb → x.regs finCnt = kEdgeAddr wb N →
      x.regs edgeB = kRevEdgeAddr wb N Mc → x.regs curB = kCurAddr wb N Mc →
      x.regs uReg = idx →
      ∃ y, ExecWithin w (.loop (.lt uReg nVerts) revFillOuterBody) x y
          (9 * us.length + 11 * outDegreeSum adj us + 2) ∧
        PartialCSRAt (revGraph adj)
          (us.foldl (fun r u => (adj u).foldl (fun r v => Function.update r v (u :: r v)) r) rev)
          (kCurAddr wb N Mc) (kRevEdgeAddr wb N Mc) y.mem ∧
        (∀ a, ¬ ((kCurAddr wb N Mc ≤ a ∧ a < kCurAddr wb N Mc + N) ∨
            (kRevEdgeAddr wb N Mc ≤ a ∧ a < kRevEdgeAddr wb N Mc + csrOffset (revGraph adj) N)) →
          y.mem a = x.mem a) ∧
        (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r)
  | [], idx, rev, x, hidx, _, _, hpcsr, _, _, _, _, _, _, _, _ => by
    simp only [List.length_nil, Nat.add_zero] at hidx
    have hend : ¬ (Cond.lt uReg nVerts).Holds x := by
      change ¬ x.regs uReg < x.regs nVerts; omega
    exact ⟨x, ⟨2, by simp [outDegreeSum], Exec.loop_exit hend⟩,
      hpcsr, fun _ _ => rfl, fun _ _ => rfl⟩
  | u :: us, idx, rev, x, hidx, hus, hroom_all, hpcsr, hcsr, hc1, hNv, hoff, hfedge,
      hredge, hcur, huR => by
    set revAdj := revGraph adj
    simp only [List.length_cons] at hidx
    have hu_val : u.val = idx := by
      have h0 := hus 0 (by simp)
      rwa [List.getElem_cons_zero, Nat.add_zero] at h0
    have hoff_u : x.mem (kOffAddr wb + idx) = csrOffset adj u.val := by
      rw [← hu_val]; exact hcsr.1 u.val (by omega)
    have hoff_u1 : x.mem (kOffAddr wb + idx + 1) = csrOffset adj u.val + (adj u).length := by
      simpa [← hu_val, Nat.add_assoc, csrOffset_succ adj u.isLt] using
        hcsr.1 (u.val + 1) (by omega)
    have hf_oa : Fits w (kOffAddr wb + idx) :=
      hfit.of_le (by simp only [kOffAddr, kTopAddr]; omega)
    have hf_oa1 : Fits w (kOffAddr wb + idx + 1) :=
      hfit.of_le (by simp only [kOffAddr, kTopAddr]; omega)
    have hf_i1 : Fits w (idx + 1) := hfit.of_le (by simp only [kTopAddr]; omega)
    let x₁ := (((x.set addr (kOffAddr wb + idx)).set jReg (csrOffset adj u.val)).set
      addr (kOffAddr wb + idx + 1)).set oldFinReg (csrOffset adj u.val + (adj u).length)
    have hp1 : ExecWithin w
        (ram[ addr ← offB + uReg; jReg ← *addr; addr ← addr + cOne; oldFinReg ← *addr ])
        x x₁ 4 := by
      have htriv : x₁ = (((x.set addr (kOffAddr wb + idx)).set jReg (csrOffset adj u.val)).set
        addr (kOffAddr wb + idx + 1)).set oldFinReg (csrOffset adj u.val + (adj u).length) := rfl
      wram_exec [hoff, huR, hc1, hoff_u, hoff_u1, hf_oa, hf_oa1]
    have hroom_u : ∀ z : Fin N,
        ((adj u).foldl (fun r v => Function.update r v (u :: r v)) rev z).length ≤
          (revAdj z).length := by
      intro z
      exact (length_foldl_vs_rev_le adj us _ z).trans
        (by simpa [List.foldl_cons] using hroom_all z)
    obtain ⟨y₁, hy₁_ex, hy₁_pcsr, hy₁_out, hy₁_fr⟩ :=
      revFillInner_spec adj wb Mc hmc hfit u (adj u) 0 rev x₁ (by simp) (fun q _ => by simp)
        hroom_u (by dsimp only [x₁]; exact hpcsr) (by dsimp only [x₁]; exact hcsr)
        (by dsimp only [x₁]; wram_simp; exact hc1)
        (by dsimp only [x₁]; wram_simp; exact hfedge)
        (by dsimp only [x₁]; wram_simp; exact hredge)
        (by dsimp only [x₁]; wram_simp; exact hcur)
        (by dsimp only [x₁]; wram_simp; omega)
        (by dsimp only [x₁]; wram_simp)
        (by dsimp only [x₁]; wram_simp)
    have hy₁_u : y₁.regs uReg = idx :=
      (hy₁_fr uReg (by decide) (by decide) (by decide) (by decide)).trans
        (by dsimp only [x₁]; wram_simp; exact huR)
    have hy₁_1 : y₁.regs cOne = 1 :=
      (hy₁_fr cOne (by decide) (by decide) (by decide) (by decide)).trans
        (by dsimp only [x₁]; wram_simp; exact hc1)
    let x₂ := y₁.set uReg (idx + 1)
    have hp2 : ExecWithin w (ram[ uReg ← uReg + cOne ]) y₁ x₂ 1 := by
      wram_exec [hy₁_u, hy₁_1, hf_i1]
    have hmc_rev : csrOffset revAdj N ≤ Mc := by
      dsimp only [revAdj, revGraph]; rwa [csrOffset_transposeAdj_eq]
    have hx₂_csr : CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x₂.mem :=
      hcsr.of_eqOn
        (fun _ _ => hy₁_out _ (by dsimp only [kOffAddr, kCurAddr, kRevEdgeAddr]; omega))
        (fun _ _ => hy₁_out _ (by dsimp only [kEdgeAddr, kCurAddr, kRevEdgeAddr]; omega))
    have hx₂_fr0 : ∀ r : Fin 28, r.val < 18 → x₂.regs r = x.regs r := fun r hr => by
      have hne_u : r ≠ uReg := by reg_ne
      have hne_of : r ≠ oldFinReg := by reg_ne
      have hne_a : r ≠ addr := by reg_ne
      have hne_j : r ≠ jReg := by reg_ne
      dsimp only [x₂]
      rw [Data.set_regs_of_ne hne_u, hy₁_fr r hne_a (by reg_ne) (by reg_ne) hne_j]
      dsimp only [x₁]
      simp [Data.set_regs_of_ne hne_of, Data.set_regs_of_ne hne_a, Data.set_regs_of_ne hne_j]
    have hx₂_fc : x₂.regs finCnt = kEdgeAddr wb N := by
      dsimp only [x₂]
      rw [Data.set_regs_of_ne (by decide),
        hy₁_fr finCnt (by decide) (by decide) (by decide) (by decide)]
      dsimp only [x₁]; wram_simp; exact hfedge
    obtain ⟨y, hy_ex, hy_pcsr, hy_out, hy_fr⟩ :=
      revFillOuter_spec adj wb Mc hmc hfit us (idx + 1)
        ((adj u).foldl (fun r v => Function.update r v (u :: r v)) rev) x₂ (by omega)
        (fun q hq => by
          have h := hus (q + 1) (by simp; omega)
          simpa [Nat.add_assoc, Nat.add_comm 1 q] using h)
        (fun z => by simpa [List.foldl_cons] using hroom_all z)
        hy₁_pcsr hx₂_csr
        ((hx₂_fr0 cOne (by decide)).trans hc1)
        ((hx₂_fr0 nVerts (by decide)).trans hNv)
        ((hx₂_fr0 offB (by decide)).trans hoff)
        hx₂_fc
        ((hx₂_fr0 edgeB (by decide)).trans hredge)
        ((hx₂_fr0 curB (by decide)).trans hcur)
        (by dsimp only [x₂]; wram_simp)
    have hbody_ex : ExecWithin w revFillOuterBody x x₂ (11 * (adj u).length + 7) :=
      (hp1.seq (hy₁_ex.seq hp2)).mono (by omega)
    obtain ⟨t₁, ht₁, he₁⟩ := hbody_ex
    obtain ⟨t₂, ht₂, he₂⟩ := hy_ex
    have hlt : (Cond.lt uReg nVerts).Holds x := by
      change x.regs uReg < x.regs nVerts; omega
    refine ⟨y, ⟨t₁ + t₂ + 2, ?_, Exec.loop_iter hlt he₁ he₂⟩,
      hy_pcsr, fun a ha => (hy_out a ha).trans (hy₁_out a ha),
      fun r hr => (hy_fr r hr).trans (hx₂_fr0 r hr)⟩
    simp only [List.length_cons, outDegreeSum, List.map_cons, List.sum_cons] at ht₂ ⊢
    omega

private theorem transposeCSRCode_spec {N w : ℕ} (adj : Fin N → List (Fin N))
    (wb Mc : ℕ) (hmc : csrOffset adj N ≤ Mc)
    (hfit : Fits w (kTopAddr wb N Mc + Mc + 4)) {x : Data 28}
    (hc0 : x.regs cZero = 0) (hc1 : x.regs cOne = 1) (hNv : x.regs nVerts = N)
    (hoff : x.regs offB = kOffAddr wb) (hedge : x.regs edgeB = kEdgeAddr wb N)
    (hcur : x.regs curB = kCurAddr wb N Mc)
    (hroff : x.regs revOffB = kRevOffAddr wb N Mc)
    (hredge : x.regs revEdgeB = kRevEdgeAddr wb N Mc)
    (hcsr : CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x.mem) :
    let revAdj := transposeAdj adj (List.finRange N)
    ∃ y, ExecWithin w transposeCSRCode x y (31 * N + 20 * Mc + 22) ∧
      CSRAt revAdj (kRevOffAddr wb N Mc) (kRevEdgeAddr wb N Mc) y.mem ∧
      y.regs offB = kRevOffAddr wb N Mc ∧
      y.regs edgeB = kRevEdgeAddr wb N Mc ∧
      (∀ a, ¬ ((kRevOffAddr wb N Mc ≤ a ∧ a < kRevOffAddr wb N Mc + N + 1) ∨
          (kRevEdgeAddr wb N Mc ≤ a ∧ a < kRevEdgeAddr wb N Mc + Mc) ∨
          (kCurAddr wb N Mc ≤ a ∧ a < kCurAddr wb N Mc + N)) → y.mem a = x.mem a) ∧
      (∀ r : Fin 28, r.val < 18 → r ≠ offB → r ≠ edgeB → y.regs r = x.regs r) := by
  set revAdj := transposeAdj adj (List.finRange N)
  have hmc_rev : csrOffset revAdj N ≤ Mc := by
    dsimp only [revAdj]; rwa [csrOffset_transposeAdj_eq]
  have hfit_cur : Fits w (kCurAddr wb N Mc + N) :=
    hfit.of_le (by simp only [kCurAddr, kTopAddr]; omega)
  obtain ⟨x₁, hx₁_ex, hx₁_zero, hx₁_out, hx₁_fr⟩ :=
    zeroBlockCode_spec curB (by decide) (kCurAddr wb N Mc) N hfit_cur hc0 hc1 hcur hNv
  have hx₁_csr : CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x₁.mem :=
    hcsr.of_eqOn
      (fun _ _ => hx₁_out _ (by dsimp only [kOffAddr, kCurAddr]; omega))
      (fun _ _ => hx₁_out _ (by dsimp only [kEdgeAddr, kCurAddr]; omega))
  let x₂ := x₁.set iReg 0
  have hp1 : ExecWithin (B := .standard) w (ram[ iReg ← cZero ]) x₁ x₂ 1 := by
    have h0' : x₁.regs cZero = 0 := (hx₁_fr cZero (by decide)).trans hc0
    wram_exec [h0']
  have hroom_rev : ∀ z : Fin N, (revAdj z).length ≤ Mc := by
    intro z
    have h1 := csrOffset_succ revAdj z.isLt; simp only [Fin.eta] at h1
    have h2 := csrOffset_mono revAdj (by omega : z.val + 1 ≤ N); omega
  obtain ⟨x₃, hx₃_ex, hx₃_deg, hx₃_out, hx₃_fr⟩ :=
    revDegOuter_spec adj wb Mc hmc hfit (List.finRange N) 0 (fun _ => []) x₂ (by simp)
      (fun q _ => by simp) (fun z => hroom_rev z)
      (fun z => by dsimp only [x₂]; exact hx₁_zero z.val z.isLt) hx₁_csr
      (by dsimp only [x₂]; wram_simp; exact (hx₁_fr cOne (by decide)).trans hc1)
      (by dsimp only [x₂]; wram_simp; exact (hx₁_fr nVerts (by decide)).trans hNv)
      (by dsimp only [x₂]; wram_simp; exact (hx₁_fr offB (by decide)).trans hoff)
      (by dsimp only [x₂]; wram_simp; exact (hx₁_fr edgeB (by decide)).trans hedge)
      (by dsimp only [x₂]; wram_simp; exact (hx₁_fr curB (by decide)).trans hcur)
      (by dsimp only [x₂]; wram_simp)
  have hx₃_fr0 : ∀ r : Fin 28, r.val < 18 → x₃.regs r = x.regs r := fun r hr => by
    have h3 := hx₃_fr r hr
    have hne : r ≠ iReg := by reg_ne
    dsimp only [x₂] at h3
    rw [h3, Data.set_regs_of_ne hne]
    exact hx₁_fr r hr
  let x₄ := (x₃.set compIdxReg (kOffAddr wb)).set offB (kRevOffAddr wb N Mc)
  have hp2 : ExecWithin (B := .standard) w (ram[ compIdxReg ← offB; offB ← revOffB ]) x₃ x₄ 2 := by
    have h_ob : x₃.regs offB = kOffAddr wb := (hx₃_fr0 offB (by decide)).trans hoff
    have h_rob : x₃.regs revOffB = kRevOffAddr wb N Mc := (hx₃_fr0 revOffB (by decide)).trans hroff
    wram_exec [h_ob, h_rob]
  have hfit_ps : Fits w (kCurAddr wb N Mc + N + Mc + 2) :=
    hfit.of_le (by simp only [kCurAddr, kTopAddr]; omega)
  obtain ⟨x₅, hx₅_ex, hx₅_roff, hx₅_cur, hx₅_out, hx₅_fr⟩ :=
    prefixSumCode_spec revAdj (kCurAddr wb N Mc) (kRevOffAddr wb N Mc) Mc
      (by simp only [kRevOffAddr, kCurAddr]; omega) hmc_rev hfit_ps (x := x₄)
      (by dsimp only [x₄]; wram_simp; exact (hx₃_fr0 cZero (by decide)).trans hc0)
      (by dsimp only [x₄]; wram_simp; exact (hx₃_fr0 cOne (by decide)).trans hc1)
      (by dsimp only [x₄]; wram_simp; exact (hx₃_fr0 curB (by decide)).trans hcur)
      (by dsimp only [x₄]; wram_simp)
      (by dsimp only [x₄]; wram_simp; exact (hx₃_fr0 nVerts (by decide)).trans hNv)
      hx₃_deg
  have hx₅_comp : x₅.regs compIdxReg = kOffAddr wb :=
    (hx₅_ex.regs_eq (by decide)).trans (by dsimp only [x₄]; wram_simp)
  have hx₅_fr0 : ∀ r : Fin 28, r.val < 18 → r ≠ offB → x₅.regs r = x.regs r := fun r hr hno => by
    rw [hx₅_fr r hr]
    dsimp only [x₄]
    have hne_c : r ≠ compIdxReg := by reg_ne
    rw [Data.set_regs_of_ne hno, Data.set_regs_of_ne hne_c]
    exact hx₃_fr0 r hr
  let x₆ := (((x₅.set offB (kOffAddr wb)).set finCnt (kEdgeAddr wb N)).set
    edgeB (kRevEdgeAddr wb N Mc)).set uReg 0
  have hp3 : ExecWithin (B := .standard) w
      (ram[ offB ← compIdxReg; finCnt ← edgeB; edgeB ← revEdgeB; uReg ← cZero ]) x₅ x₆ 4 := by
    have h_eb : x₅.regs edgeB = kEdgeAddr wb N :=
      (hx₅_fr0 edgeB (by decide) (by decide)).trans hedge
    have h_reb : x₅.regs revEdgeB = kRevEdgeAddr wb N Mc :=
      (hx₅_fr0 revEdgeB (by decide) (by decide)).trans hredge
    have h_c0 : x₅.regs cZero = 0 := (hx₅_fr0 cZero (by decide) (by decide)).trans hc0
    wram_exec [hx₅_comp, h_eb, h_reb, h_c0]
  have hx₅_csr : CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x₅.mem :=
    hx₁_csr.of_eqOn
      (fun _ _ => (hx₅_out _ (by dsimp only [kOffAddr, kRevOffAddr, kCurAddr]; omega)).trans
        (hx₃_out _ (by dsimp only [kOffAddr, kCurAddr]; omega)))
      (fun _ _ => (hx₅_out _ (by dsimp only [kEdgeAddr, kRevOffAddr, kCurAddr]; omega)).trans
        (hx₃_out _ (by dsimp only [kEdgeAddr, kCurAddr]; omega)))
  obtain ⟨x₇, hx₇_ex, hx₇_pcsr, hx₇_out, hx₇_fr⟩ :=
    revFillOuter_spec adj wb Mc hmc hfit (List.finRange N) 0 (fun _ => []) x₆ (by simp)
      (fun q _ => by simp) (fun z => le_rfl)
      (partialCSRAt_init revAdj (kCurAddr wb N Mc) (kRevEdgeAddr wb N Mc) x₅.mem hx₅_cur)
      hx₅_csr
      (by dsimp only [x₆]; wram_simp; exact (hx₅_fr0 cOne (by decide) (by decide)).trans hc1)
      (by dsimp only [x₆]; wram_simp; exact (hx₅_fr0 nVerts (by decide) (by decide)).trans hNv)
      (by dsimp only [x₆]; wram_simp)
      (by dsimp only [x₆]; wram_simp)
      (by dsimp only [x₆]; wram_simp)
      (by dsimp only [x₆]; wram_simp; exact (hx₅_fr0 curB (by decide) (by decide)).trans hcur)
      (by dsimp only [x₆]; wram_simp)
  have hx₇_roff : ∀ u ≤ N, x₇.mem (kRevOffAddr wb N Mc + u) = csrOffset revAdj u := fun u hu => by
    rw [hx₇_out _ (by simp only [kRevOffAddr, kCurAddr, kRevEdgeAddr]; omega)]
    exact hx₅_roff u hu
  have hx₇_rcsr : CSRAt revAdj (kRevOffAddr wb N Mc) (kRevEdgeAddr wb N Mc) x₇.mem :=
    csrAt_of_partialCSRAt revAdj (kRevOffAddr wb N Mc) (kCurAddr wb N Mc) (kRevEdgeAddr wb N Mc)
      x₇.mem hx₇_roff hx₇_pcsr
  have hx₇_rob : x₇.regs revOffB = kRevOffAddr wb N Mc := by
    rw [hx₇_fr revOffB (by decide)]
    dsimp only [x₆]; wram_simp
    exact (hx₅_fr0 revOffB (by decide) (by decide)).trans hroff
  let y := x₇.set offB (kRevOffAddr wb N Mc)
  have hp4 : ExecWithin (B := .standard) w (ram[ offB ← revOffB ]) x₇ y 1 := by
    wram_exec [hx₇_rob]
  have hout_sum : outDegreeSum adj (List.finRange N) = csrOffset adj N :=
    (csrOffset_eq_outDegreeSum adj).symm
  rw [List.length_finRange, hout_sum] at hx₃_ex hx₇_ex
  refine ⟨y,
    (hx₁_ex.seq (hp1.seq (hx₃_ex.seq (hp2.seq (hx₅_ex.seq (hp3.seq (hx₇_ex.seq hp4))))))).mono
      (by omega),
    hx₇_rcsr,
    by dsimp only [y]; wram_simp,
    by
      dsimp only [y]; wram_simp
      rw [hx₇_fr edgeB (by decide)]; dsimp only [x₆]; wram_simp,
    fun a ha => ?_,
    fun r hr hno hne => ?_⟩
  · dsimp only [y]; mem_upd
    rw [hx₇_out _ (by dsimp only [revAdj, revGraph] at *; omega)]
    dsimp only [x₆]; mem_upd
    rw [hx₅_out _ (by omega)]
    dsimp only [x₄]; mem_upd
    rw [hx₃_out _ (by omega)]
    dsimp only [x₂]; mem_upd
    exact hx₁_out _ (by omega)
  · dsimp only [y]
    rw [Data.set_regs_of_ne hno, hx₇_fr r hr]
    dsimp only [x₆]
    have hne_u : r ≠ uReg := by reg_ne
    have hne_fc : r ≠ finCnt := by reg_ne
    rw [Data.set_regs_of_ne hne_u, Data.set_regs_of_ne hne, Data.set_regs_of_ne hne_fc,
      Data.set_regs_of_ne hno]
    exact hx₅_fr0 r hr hno

/-! ### Pass 3: Kosaraju SCC peeling and component indexing (`O(N + M)`) -/

private def writeCompBody : Code .standard 28 := ram[
  addr ← finB + pReg; vReg ← *addr;
  addr ← compB + vReg; *addr ← compIdxReg;
  pReg ← pReg + cOne ]

private def peelStepBody : Code .standard 28 :=
  (ram[ addr ← nVerts - cOne; addr ← addr - iReg; addr ← ordB + addr; uReg ← *addr;
        oldFinReg ← finCnt ]).seq
    (visitRootCode.seq
      ((Code.branch (.lt oldFinReg finCnt)
          ((ram[ pReg ← oldFinReg ]).seq
            ((Code.loop (.lt pReg finCnt) writeCompBody).seq
              (ram[ compIdxReg ← compIdxReg + cOne ])))
          (ram[ compIdxReg ← compIdxReg ])).seq
        (ram[ iReg ← iReg + cOne ])))

private def kosarajuIndexCode : Code .standard 28 :=
  (zeroBlockCode visB).seq
    ((ram[ finCnt ← cZero; compIdxReg ← cZero; iReg ← cZero ]).seq
      (.loop (.lt iReg nVerts) peelStepBody))

private theorem writeCompLoop_spec {N w : ℕ} (finAddr compAddr : ℕ) (hdisj : finAddr + N ≤ compAddr)
    (F₀ L cIdx : ℕ) (hFL : F₀ + L ≤ N) (hfit : Fits w (compAddr + N + 2))
    (comp : List (Fin N)) (hnd : comp.Nodup) (hlen : comp.length = L) :
    ∀ (rem k : ℕ) (f : Fin N → ℕ) (x : Data 28)
      (_ : k + rem = L),
      (∀ q (hq : q < L), x.mem (finAddr + F₀ + q) = (comp[q]'(hlen ▸ hq)).val) →
      (∀ u : Fin N, x.mem (compAddr + u.val) =
        if u ∈ comp.take k then cIdx else f u) →
      x.regs cOne = 1 → x.regs finB = finAddr → x.regs compB = compAddr →
      x.regs compIdxReg = cIdx → x.regs finCnt = F₀ + L → x.regs pReg = F₀ + k →
      ∃ y, ExecWithin w (.loop (.lt pReg finCnt) writeCompBody) x y (7 * rem + 2) ∧
        (∀ u : Fin N, y.mem (compAddr + u.val) = if u ∈ comp then cIdx else f u) ∧
        (∀ a, ¬ (compAddr ≤ a ∧ a < compAddr + N) → y.mem a = x.mem a) ∧
        (∀ r : Fin 28, r ≠ addr → r ≠ vReg → r ≠ pReg → y.regs r = x.regs r)
  | 0, k, f, x, hk, _, hf_mem, _, _, _, _, hfc, hp => by
    have hk_eq : k = L := by omega
    subst hk_eq
    have hend : ¬ (Cond.lt pReg finCnt).Holds x := by
      change ¬ x.regs pReg < x.regs finCnt; omega
    refine ⟨x, ⟨2, by simp, Exec.loop_exit hend⟩, fun u => ?_, fun _ _ => rfl, fun _ _ _ _ => rfl⟩
    simpa [List.take_of_length_le (by omega : comp.length ≤ k)] using hf_mem u
  | rem + 1, k, f, x, hk, hfin_mem, hf_mem, hc1, hfb, hcb, hcIdx, hfc, hp => by
    have hk_lt : k < L := by omega
    set v := comp[k]'(by omega)
    have hm_v : x.mem (finAddr + (F₀ + k)) = v.val := by
      rw [← Nat.add_assoc]; exact hfin_mem k hk_lt
    have hf_fa : Fits w (finAddr + (F₀ + k)) := hfit.of_le (by omega)
    have hf_ca : Fits w (compAddr + v.val) := hfit.of_le (by have := v.isLt; omega)
    have hf_p1 : Fits w (F₀ + k + 1) := hfit.of_le (by omega)
    let StepPost (x₁ : Data 28) : Prop :=
      (∀ u : Fin N, x₁.mem (compAddr + u.val) =
          if u ∈ comp.take (k + 1) then cIdx else f u) ∧
        (∀ a, ¬ (compAddr ≤ a ∧ a < compAddr + N) → x₁.mem a = x.mem a) ∧
        x₁.regs pReg = F₀ + (k + 1) ∧
        (∀ r : Fin 28, r ≠ addr → r ≠ vReg → r ≠ pReg → x₁.regs r = x.regs r)
    have hstep : ∃ x₁, ExecWithin w writeCompBody x x₁ 5 ∧ StepPost x₁ := by
      unfold writeCompBody
      wram_exec [hc1, hfb, hcb, hcIdx, hp, hm_v, hf_fa, hf_ca, hf_p1]
      dsimp only [StepPost]
      refine ⟨fun u => ?_, fun a ha => ?_, by wram_simp; omega, fun r h1 h2 h3 => ?_⟩
      · mem_upd
        have htake : comp.take (k + 1) = comp.take k ++ [v] := by
          rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]
          rfl
        rw [htake]
        by_cases huv : u = v
        · subst huv; simp
        · have hne : compAddr + u.val ≠ compAddr + v.val := fun h => huv (Fin.ext (by omega))
          rw [Function.update_of_ne hne, hf_mem u]
          simp [huv]
      · mem_upd
        exact Function.update_of_ne (by have := v.isLt; omega) _ _
      · regs_lt
    obtain ⟨x₁, hx₁_ex, hx₁_f, hx₁_out, hx₁_p, hx₁_fr⟩ := hstep
    have hfin_mem₁ : ∀ q (hq : q < L), x₁.mem (finAddr + F₀ + q) = (comp[q]'(hlen ▸ hq)).val :=
      fun q hq => (hx₁_out _ (by omega)).trans (hfin_mem q hq)
    obtain ⟨y, hy_ex, hy_f, hy_out, hy_fr⟩ :=
      writeCompLoop_spec finAddr compAddr hdisj F₀ L cIdx hFL hfit comp hnd hlen rem (k + 1) f x₁
        (by omega) hfin_mem₁ hx₁_f
        ((hx₁_fr cOne (by decide) (by decide) (by decide)).trans hc1)
        ((hx₁_fr finB (by decide) (by decide) (by decide)).trans hfb)
        ((hx₁_fr compB (by decide) (by decide) (by decide)).trans hcb)
        ((hx₁_fr compIdxReg (by decide) (by decide) (by decide)).trans hcIdx)
        ((hx₁_fr finCnt (by decide) (by decide) (by decide)).trans hfc)
        hx₁_p
    obtain ⟨t₁, ht₁, he₁⟩ := hx₁_ex
    obtain ⟨t₂, ht₂, he₂⟩ := hy_ex
    have hlt : (Cond.lt pReg finCnt).Holds x := by
      change x.regs pReg < x.regs finCnt; omega
    refine ⟨y, ⟨t₁ + t₂ + 2, by omega, Exec.loop_iter hlt he₁ he₂⟩,
      hy_f, fun a ha => (hy_out a ha).trans (hx₁_out a ha),
      fun r h1 h2 h3 => (hy_fr r h1 h2 h3).trans (hx₁_fr r h1 h2 h3)⟩

private theorem peelLoop_spec {N w : ℕ} (hN : 0 < N) (revAdj : Fin N → List (Fin N))
    (ord : List (Fin N)) (hord_len : ord.length = N)
    (wb Mc : ℕ) (hmc : csrOffset revAdj N ≤ Mc)
    (hfit : Fits w (kTopAddr wb N Mc + Mc + 4)) :
    ∀ (rs : List (Fin N)) (idx F₀ cIdx : ℕ) (vis : Finset (Fin N)) (f : Fin N → ℕ) (x : Data 28)
      (_ : idx + rs.length = N),
      (∀ q (hq : q < rs.length), rs[q] = ord[idx + q]'(by omega)) →
      F₀ = vis.card →
      cIdx ≤ F₀ →
      DfsRegs (kRevOffAddr wb N Mc) (kRevEdgeAddr wb N Mc) (kVisAddr wb N Mc) (kFinAddr wb N Mc)
        (kStkAddr wb N Mc) x →
      x.regs nVerts = N → x.regs ordB = kOrdAddr wb N Mc → x.regs compB = kCompAddr wb N Mc →
      x.regs iReg = idx → x.regs finCnt = F₀ → x.regs compIdxReg = cIdx →
      CSRAt revAdj (kRevOffAddr wb N Mc) (kRevEdgeAddr wb N Mc) x.mem →
      (∀ q (hq : q < N), x.mem (kOrdAddr wb N Mc + (N - 1 - q)) = (ord[q]'(by omega)).val) →
      VisAt vis (kVisAddr wb N Mc) x.mem →
      (∀ u : Fin N, u ∈ vis → x.mem (kCompAddr wb N Mc + u.val) = f u) →
      ∃ y,
        let comps := peelSCCs revAdj N vis rs
        ExecWithin w (.loop (.lt iReg nVerts) peelStepBody) x y
          (30 * rs.length + 68 * comps.flatten.length +
            36 * outDegreeSum revAdj comps.flatten + 2) ∧
        (∀ u : Fin N, u ∈ vis ∨ u ∈ comps.flatten →
          y.mem (kCompAddr wb N Mc + u.val) = indexComponentsAux cIdx comps f u) ∧
        (∀ a, a < kVisAddr wb N Mc → y.mem a = x.mem a) ∧
        (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r)
  | [], idx, F₀, cIdx, vis, f, x, hidx, _, _, _, _, _, _, _, _, _, _, _, _, _, hf_vis => by
    simp only [List.length_nil, Nat.add_zero] at hidx
    have hend : ¬ (Cond.lt iReg nVerts).Holds x := by
      change ¬ x.regs iReg < x.regs nVerts; omega
    refine ⟨x, ⟨2, by simp [peelSCCs, outDegreeSum], Exec.loop_exit hend⟩,
      fun u hu => ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    simp only [peelSCCs, List.flatten_nil, List.not_mem_nil, or_false] at hu
    simpa [peelSCCs, indexComponentsAux] using hf_vis u hu
  | r :: rs, idx, F₀, cIdx, vis, f, x, hidx, hrs, hF₀, hcIdx_le, hregs, hNv, hordB, hcompB,
      hi, hfc, hcIdx, hcsr, hord_mem, hvis, hf_vis => by
    simp only [List.length_cons] at hidx
    have hr_eq : r = ord[idx]'(by omega) := by
      have h0 := hrs 0 (by simp)
      simpa only [Nat.add_zero, List.getElem_cons_zero] using h0
    have hm_ord : x.mem (kOrdAddr wb N Mc + (N - 1 - idx)) = r.val := by
      rw [hr_eq]; exact hord_mem idx (by omega)
    have hcard_le : vis.card ≤ N := by have := Finset.card_le_univ vis; simpa using this
    have hcons : F₀ + (N - vis.card) ≤ N := by omega
    have hf_n1 : Fits w (N - 1) := hfit.of_le (by simp only [kTopAddr]; omega)
    have hf_sub : Fits w (N - 1 - idx) := hfit.of_le (by simp only [kTopAddr]; omega)
    have hf_oa : Fits w (kOrdAddr wb N Mc + (N - 1 - idx)) :=
      hfit.of_le (by simp only [kOrdAddr, kTopAddr]; omega)
    have hfit_stk : Fits w (kStkAddr wb N Mc + 3 * N + Mc + 4) :=
      hfit.of_le (by simp only [kStkAddr, kTopAddr]; omega)
    let x₁ := ((((x.set addr (N - 1)).set addr (N - 1 - idx)).set
      addr (kOrdAddr wb N Mc + (N - 1 - idx))).set uReg r.val).set oldFinReg F₀
    have hp1 : ExecWithin w
        (ram[ addr ← nVerts - cOne; addr ← addr - iReg; addr ← ordB + addr; uReg ← *addr;
              oldFinReg ← finCnt ]) x x₁ 5 := by
      have hc1 := hregs.cone
      have htriv : x₁ = ((((x.set addr (N - 1)).set addr (N - 1 - idx)).set
        addr (kOrdAddr wb N Mc + (N - 1 - idx))).set uReg r.val).set oldFinReg F₀ := rfl
      wram_exec [hNv, hc1, hi, hordB, hm_ord, hfc, hf_n1, hf_oa]
    obtain ⟨y₁, hy₁_ex, hy₁_r, hy₁_csr, hy₁_vis, hy₁_fc, hy₁_fin_mem, hy₁_out, hy₁_fr⟩ :=
      visitRootCode_spec hN revAdj (kRevOffAddr wb N Mc) (kRevEdgeAddr wb N Mc)
        (kVisAddr wb N Mc) (kFinAddr wb N Mc) (kStkAddr wb N Mc) Mc
        (by simp only [kRevOffAddr, kVisAddr]; omega)
        (by simp only [kRevEdgeAddr, kVisAddr]; omega)
        (by simp only [kVisAddr, kFinAddr]; omega)
        (by simp only [kFinAddr, kStkAddr]; omega)
        hmc hfit_stk r F₀ vis hcons (x := x₁)
        (dfsRegs_of_frame hregs fun reg hreg => by
          dsimp only [x₁]; regs_lt)
        hcsr hvis (by dsimp only [x₁]; wram_simp) (by dsimp only [x₁]; wram_simp; exact hfc)
    set s := visit revAdj N r ⟨vis, []⟩
    obtain ⟨hnd_s, hdis_s, hvis_s⟩ := visit_nil_struct revAdj N r vis
    have hcard_s : s.visited.card = vis.card + s.finished.length := card_visit_nil revAdj N r vis
    have hy₁_of : y₁.regs oldFinReg = F₀ :=
      (hy₁_fr oldFinReg (.inr (.inr rfl))).trans (by dsimp only [x₁]; wram_simp)
    have hy₁_cIdx : y₁.regs compIdxReg = cIdx :=
      (hy₁_fr compIdxReg (.inr (.inl rfl))).trans (by dsimp only [x₁]; wram_simp; exact hcIdx)
    have hy₁_i : y₁.regs iReg = idx :=
      (hy₁_fr iReg (.inl (by decide))).trans (by dsimp only [x₁]; wram_simp; exact hi)
    have hy₁_fr0 : ∀ reg : Fin 28, reg.val < 18 → y₁.regs reg = x.regs reg := fun reg hreg => by
      rw [hy₁_fr reg (.inl (by omega))]
      dsimp only [x₁]; regs_lt
    let f' : Fin N → ℕ :=
      if s.finished.isEmpty then f
      else s.finished.foldl (fun g v => Function.update g v cIdx) f
    let cIdx' : ℕ := if s.finished.isEmpty then cIdx else cIdx + 1
    have hf_i1 : Fits w (idx + 1) := hfit.of_le (by simp only [kTopAddr]; omega)
    have hbranch : ∃ y₂,
        ExecWithin w
          ((Code.branch (.lt oldFinReg finCnt)
              ((ram[ pReg ← oldFinReg ]).seq
                ((Code.loop (.lt pReg finCnt) writeCompBody).seq
                  (ram[ compIdxReg ← compIdxReg + cOne ])))
              (ram[ compIdxReg ← compIdxReg ])).seq
            (ram[ iReg ← iReg + cOne ]))
          y₁ y₂ (7 * s.finished.length + 7) ∧
        y₂.regs iReg = idx + 1 ∧ y₂.regs finCnt = F₀ + s.finished.length ∧
        y₂.regs compIdxReg = cIdx' ∧
        (∀ u : Fin N, u ∈ s.visited → y₂.mem (kCompAddr wb N Mc + u.val) = f' u) ∧
        (∀ a, ¬ (kCompAddr wb N Mc ≤ a ∧ a < kCompAddr wb N Mc + N) → y₂.mem a = y₁.mem a) ∧
        (∀ reg : Fin 28, reg.val < 18 → y₂.regs reg = y₁.regs reg) := by
      have hFL : F₀ + s.finished.length ≤ N := by
        have := Finset.card_le_univ s.visited
        simp only [Fintype.card_fin] at this
        omega
      by_cases hempty : s.finished.isEmpty
      · have hlen0 : s.finished = [] := List.isEmpty_iff.1 hempty
        have hnlt : ¬ (Cond.lt oldFinReg finCnt).Holds y₁ := by
          change ¬ y₁.regs oldFinReg < y₁.regs finCnt
          simp [hy₁_of, hy₁_fc, hlen0]
        let y₂ := (y₁.set compIdxReg cIdx).set iReg (idx + 1)
        have hb : ExecWithin w
            (.branch (.lt oldFinReg finCnt)
              ((ram[ pReg ← oldFinReg ]).seq
                ((Code.loop (.lt pReg finCnt) writeCompBody).seq
                  (ram[ compIdxReg ← compIdxReg + cOne ])))
              (ram[ compIdxReg ← compIdxReg ]))
            y₁ (y₁.set compIdxReg cIdx) 3 := by
          have hnop : Exec (B := .standard) w (ram[ compIdxReg ← compIdxReg ])
              y₁ (y₁.set compIdxReg cIdx) 1 := by
            simpa [hy₁_cIdx] using
              Exec.op (B := .standard) (o := .copy compIdxReg compIdxReg) (x := y₁) (w := w) rfl
          exact ⟨3, le_rfl, Exec.branch_neg hnlt hnop⟩
        have hinc : ExecWithin w (ram[ iReg ← iReg + cOne ]) (y₁.set compIdxReg cIdx) y₂ 1 := by
          have hc1' := hy₁_r.cone
          wram_exec [hy₁_i, hc1', hf_i1]
        refine ⟨y₂, (hb.seq hinc).mono (by omega),
          by dsimp only [y₂]; wram_simp,
          by dsimp only [y₂]; wram_simp; exact hy₁_fc,
          by dsimp only [y₂, cIdx']; wram_simp; simp [hempty],
          fun u hu => ?_, fun _ _ => rfl, fun reg hreg => ?_⟩
        · dsimp only [y₂, f']; mem_upd
          simp only [hempty, ↓reduceIte]
          have huv : u ∈ vis := by simpa [s, hlen0] using (hvis_s u).1 hu
          rw [hy₁_out (kCompAddr wb N Mc + u.val) (by
            have := u.isLt
            dsimp only [s, kVisAddr, kFinAddr, kStkAddr, kCompAddr] at hFL ⊢
            omega)]
          exact hf_vis u huv
        · dsimp only [y₂]
          have hne1 : reg ≠ iReg := by reg_ne
          have hne2 : reg ≠ compIdxReg := by reg_ne
          simp [Data.set_regs_of_ne hne1, Data.set_regs_of_ne hne2]
      · have hpos : 0 < s.finished.length := by
          cases hs_eq : s.finished with
          | nil => simp [hs_eq] at hempty
          | cons _ _ => simp
        have hlt_br : (Cond.lt oldFinReg finCnt).Holds y₁ := by
          change y₁.regs oldFinReg < y₁.regs finCnt
          omega
        let z₀ := y₁.set pReg F₀
        have hp_z₀ : ExecWithin (B := .standard) w (ram[ pReg ← oldFinReg ]) y₁ z₀ 1 := by
          wram_exec [hy₁_of]
        have hf_comp : Fits w (kCompAddr wb N Mc + N + 2) :=
          hfit.of_le (by simp only [kCompAddr, kTopAddr]; omega)
        obtain ⟨z₁, hz₁_ex, hz₁_mem, hz₁_out, hz₁_fr⟩ :=
          writeCompLoop_spec (kFinAddr wb N Mc) (kCompAddr wb N Mc)
            (by simp only [kFinAddr, kCompAddr]; omega) F₀ s.finished.length cIdx hFL hf_comp
            s.finished.reverse (List.nodup_reverse.2 hnd_s) (by simp) s.finished.length 0
            (fun u => y₁.mem (kCompAddr wb N Mc + u.val)) z₀ (by simp)
            (fun q hq => by dsimp only [z₀]; exact hy₁_fin_mem q (by simpa using hq))
            (fun u => by dsimp only [z₀]; simp)
            (by dsimp only [z₀]; wram_simp; exact hy₁_r.cone)
            (by dsimp only [z₀]; wram_simp; exact hy₁_r.hfin)
            (by dsimp only [z₀]; wram_simp; exact (hy₁_fr0 compB (by decide)).trans hcompB)
            (by dsimp only [z₀]; wram_simp; exact hy₁_cIdx)
            (by dsimp only [z₀]; wram_simp; exact hy₁_fc)
            (by dsimp only [z₀]; wram_simp)
        have hz₁_cIdx : z₁.regs compIdxReg = cIdx :=
          (hz₁_fr compIdxReg (by decide) (by decide) (by decide)).trans
            (by dsimp only [z₀]; wram_simp; exact hy₁_cIdx)
        have hz₁_1 : z₁.regs cOne = 1 :=
          (hz₁_fr cOne (by decide) (by decide) (by decide)).trans
            (by dsimp only [z₀]; wram_simp; exact hy₁_r.cone)
        have hz₁_i : z₁.regs iReg = idx :=
          (hz₁_fr iReg (by decide) (by decide) (by decide)).trans
            (by dsimp only [z₀]; wram_simp; exact hy₁_i)
        have hf_c1 : Fits w (cIdx + 1) := hfit.of_le (by simp only [kTopAddr]; omega)
        let y₂ := (z₁.set compIdxReg (cIdx + 1)).set iReg (idx + 1)
        have hp_tail : ExecWithin w
            ((ram[ compIdxReg ← compIdxReg + cOne ]).seq (ram[ iReg ← iReg + cOne ]))
            z₁ y₂ 2 := by
          have htriv : y₂ = (z₁.set compIdxReg (cIdx + 1)).set iReg (idx + 1) := rfl
          wram_exec [hz₁_cIdx, hz₁_1, hz₁_i, hf_c1, hf_i1]
        obtain ⟨tb, htb, heb⟩ := hp_z₀.seq (hz₁_ex.seq
          (show ExecWithin w (ram[ compIdxReg ← compIdxReg + cOne ]) z₁
              (z₁.set compIdxReg (cIdx + 1)) 1 by wram_exec [hz₁_cIdx, hz₁_1, hf_c1]))
        have hbr_ex : ExecWithin w
            (.branch (.lt oldFinReg finCnt)
              ((ram[ pReg ← oldFinReg ]).seq
                ((Code.loop (.lt pReg finCnt) writeCompBody).seq
                  (ram[ compIdxReg ← compIdxReg + cOne ])))
              (ram[ compIdxReg ← compIdxReg ]))
            y₁ (z₁.set compIdxReg (cIdx + 1)) (7 * s.finished.length + 5) :=
          ⟨tb + 1, by omega, Exec.branch_pos hlt_br heb⟩
        have hinc_i : ExecWithin w (ram[ iReg ← iReg + cOne ])
            (z₁.set compIdxReg (cIdx + 1)) y₂ 1 := by
          wram_exec [hz₁_i, hz₁_1, hf_i1]
        refine ⟨y₂, (hbr_ex.seq hinc_i).mono (by omega),
          by dsimp only [y₂]; wram_simp,
          by
            dsimp only [y₂]; wram_simp
            exact (hz₁_fr finCnt (by decide) (by decide) (by decide)).trans
              (by dsimp only [z₀]; wram_simp; exact hy₁_fc),
          by dsimp only [y₂, cIdx']; wram_simp; simp [hempty],
          fun u hu => ?_, fun a ha => hz₁_out a ha, fun reg hreg => ?_⟩
        · dsimp only [y₂, f']; mem_upd
          simp only [hempty, Bool.false_eq_true, ↓reduceIte, hz₁_mem u, List.mem_reverse,
            foldl_update_const]
          by_cases huf : u ∈ s.finished
          · simp [huf]
          · simp only [huf, ↓reduceIte]
            have huv : u ∈ vis := ((hvis_s u).1 hu).resolve_right huf
            rw [hy₁_out (kCompAddr wb N Mc + u.val) (by
              have := u.isLt; dsimp only [kVisAddr, kFinAddr, kStkAddr, kCompAddr]; omega)]
            exact hf_vis u huv
        · dsimp only [y₂]
          have hne1 : reg ≠ iReg := by reg_ne
          have hne2 : reg ≠ compIdxReg := by reg_ne
          have hne3 : reg ≠ addr := by reg_ne
          have hne4 : reg ≠ vReg := by reg_ne
          have hne5 : reg ≠ pReg := by reg_ne
          rw [Data.set_regs_of_ne hne1, Data.set_regs_of_ne hne2, hz₁_fr reg hne3 hne4 hne5]
          dsimp only [z₀]
          exact Data.set_regs_of_ne hne5 _
    obtain ⟨y₂, hy₂_ex, hy₂_i, hy₂_fc, hy₂_cIdx, hy₂_comp, hy₂_out, hy₂_fr⟩ := hbranch
    have hy₂_fr0 : ∀ reg : Fin 28, reg.val < 18 → y₂.regs reg = x.regs reg :=
      fun reg hreg => (hy₂_fr reg hreg).trans (hy₁_fr0 reg hreg)
    have hy₂_csr : CSRAt revAdj (kRevOffAddr wb N Mc) (kRevEdgeAddr wb N Mc) y₂.mem :=
      hy₁_csr.of_eqOn
        (fun _ _ => hy₂_out _ (by dsimp only [kRevOffAddr, kCompAddr]; omega))
        (fun _ _ => hy₂_out _ (by dsimp only [kRevEdgeAddr, kCompAddr]; omega))
    have hy₂_ord : ∀ q (hq : q < N), y₂.mem (kOrdAddr wb N Mc + (N - 1 - q)) =
        (ord[q]'(by omega)).val := fun q hq => by
      rw [hy₂_out _ (by simp only [kOrdAddr, kCompAddr]; omega),
        hy₁_out _ (by simp only [kVisAddr, kOrdAddr, kFinAddr, kStkAddr]; omega)]
      exact hord_mem q hq
    have hy₂_vis : VisAt s.visited (kVisAddr wb N Mc) y₂.mem := fun z => by
      rw [hy₂_out _ (by have := z.isLt; simp only [kVisAddr, kCompAddr]; omega)]
      exact hy₁_vis z
    have hcIdx'_le : cIdx' ≤ F₀ + s.finished.length := by
      dsimp only [cIdx']
      split_ifs with he
      · omega
      · have hpos : 0 < s.finished.length := by
          cases hs_eq : s.finished with
          | nil => simp [hs_eq] at he
          | cons _ _ => simp
        omega
    obtain ⟨y, hy_ex, hy_comp, hy_out, hy_fr⟩ :=
      peelLoop_spec hN revAdj ord hord_len wb Mc hmc hfit rs (idx + 1)
        (F₀ + s.finished.length) cIdx' s.visited f' y₂ (by omega)
        (fun q hq => by
          have h := hrs (q + 1) (by simp; omega)
          simpa [Nat.add_assoc, Nat.add_comm 1 q] using h)
        (by omega) hcIdx'_le
        (dfsRegs_of_frame hy₁_r hy₂_fr)
        ((hy₂_fr0 nVerts (by decide)).trans hNv)
        ((hy₂_fr0 ordB (by decide)).trans hordB)
        ((hy₂_fr0 compB (by decide)).trans hcompB)
        hy₂_i hy₂_fc hy₂_cIdx hy₂_csr hy₂_ord hy₂_vis hy₂_comp
    have hbody_ex : ExecWithin w peelStepBody x y₂
        (28 + 67 * s.finished.length + 36 * outDegreeSum revAdj s.finished) :=
      (hp1.seq (hy₁_ex.seq hy₂_ex)).mono (by omega)
    obtain ⟨t₁, ht₁, he₁⟩ := hbody_ex
    obtain ⟨t₂, ht₂, he₂⟩ := hy_ex
    have hlt : (Cond.lt iReg nVerts).Holds x := by
      change x.regs iReg < x.regs nVerts; omega
    refine ⟨y, ⟨t₁ + t₂ + 2, ?_, Exec.loop_iter hlt he₁ he₂⟩,
      fun u hu => ?_, fun a ha => ?_, fun reg hreg => (hy_fr reg hreg).trans (hy₂_fr0 reg hreg)⟩
    · rw [peelSCCs, show visit revAdj N r ⟨vis, []⟩ = s from rfl]
      split_ifs with he
      · have hlen0 : s.finished = [] := List.isEmpty_iff.1 he
        simp only [hlen0, List.length_nil, outDegreeSum, List.map_nil, List.sum_nil] at ht₁
        simp only [List.length_cons]
        omega
      · simp only [List.length_cons, List.flatten_cons, List.length_append,
          outDegreeSum_append]
        omega
    · rw [peelSCCs, show visit revAdj N r ⟨vis, []⟩ = s from rfl] at hu ⊢
      split_ifs with he
      · simp only [he, ↓reduceIte] at hu
        dsimp only [cIdx', f'] at hy_comp
        simp only [he, ↓reduceIte] at hy_comp
        exact hy_comp u (hu.imp (fun h => (hvis_s u).2 (.inl h)) id)
      · simp only [he, Bool.false_eq_true, ↓reduceIte] at hu
        dsimp only [cIdx', f', indexComponentsAux] at hy_comp ⊢
        simp only [he, Bool.false_eq_true, ↓reduceIte] at hy_comp
        refine hy_comp u ?_
        rcases hu with huv | hflat
        · exact .inl ((hvis_s u).2 (.inl huv))
        · rcases List.mem_append.1 (by rwa [List.flatten_cons] at hflat) with huf | hrest
          · exact .inl ((hvis_s u).2 (.inr huf))
          · exact .inr hrest
    · rw [hy_out a ha, hy₂_out a (by dsimp only [kVisAddr, kCompAddr] at *; omega),
        hy₁_out a (by dsimp only [kVisAddr, kFinAddr, kStkAddr] at *; omega)]
      dsimp only [x₁]; mem_upd

private theorem kosarajuIndexCode_spec {N w : ℕ} (hN : 0 < N) (adj : Fin N → List (Fin N))
    (wb Mc : ℕ) (hmc : csrOffset adj N ≤ Mc)
    (hfit : Fits w (kTopAddr wb N Mc + Mc + 4)) {x : Data 28}
    (hregs : DfsRegs (kRevOffAddr wb N Mc) (kRevEdgeAddr wb N Mc) (kVisAddr wb N Mc)
      (kFinAddr wb N Mc) (kStkAddr wb N Mc) x)
    (hNv : x.regs nVerts = N) (hordB : x.regs ordB = kOrdAddr wb N Mc)
    (hcompB : x.regs compB = kCompAddr wb N Mc)
    (hcsr : CSRAt (transposeAdj adj (List.finRange N))
      (kRevOffAddr wb N Mc) (kRevEdgeAddr wb N Mc) x.mem)
    (hord_len : (topologicalSort adj (List.finRange N)).length = N)
    (hord_mem : ∀ idx (hidx : idx < N),
      x.mem (kOrdAddr wb N Mc + (N - 1 - idx)) =
        ((topologicalSort adj (List.finRange N))[idx]'(by
          rw [length_topologicalSort_finRange]; exact hidx)).val) :
    ∃ y, ExecWithin w kosarajuIndexCode x y (102 * N + 36 * Mc + 9) ∧
      (∀ u : Fin N, y.mem (kCompAddr wb N Mc + u.val) =
        indexComponents (sccs adj (List.finRange N)) u) ∧
      (∀ a, a < kVisAddr wb N Mc → y.mem a = x.mem a) ∧
      (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r) := by
  set revAdj := transposeAdj adj (List.finRange N)
  set ord := topologicalSort adj (List.finRange N)
  have hmc_rev : csrOffset revAdj N ≤ Mc := by
    dsimp only [revAdj]; rwa [csrOffset_transposeAdj_eq]
  have hfit_vis : Fits w (kVisAddr wb N Mc + N) :=
    hfit.of_le (by simp only [kVisAddr, kTopAddr]; omega)
  obtain ⟨x₁, hx₁_ex, hx₁_zero, hx₁_out, hx₁_fr⟩ :=
    zeroBlockCode_spec visB (by decide) (kVisAddr wb N Mc) N hfit_vis
      hregs.czero hregs.cone hregs.hvis hNv
  have hx₁_csr : CSRAt revAdj (kRevOffAddr wb N Mc) (kRevEdgeAddr wb N Mc) x₁.mem :=
    hcsr.of_eqOn
      (fun _ _ => hx₁_out _ (by dsimp only [kRevOffAddr, kVisAddr]; omega))
      (fun _ _ => hx₁_out _ (by dsimp only [kRevEdgeAddr, kVisAddr]; omega))
  have hx₁_ord : ∀ idx (hidx : idx < N),
      x₁.mem (kOrdAddr wb N Mc + (N - 1 - idx)) =
        (ord[idx]'(by rw [hord_len]; exact hidx)).val :=
    fun idx hidx =>
      (hx₁_out _ (by dsimp only [kVisAddr, kOrdAddr]; omega)).trans (hord_mem idx hidx)
  have hx₁_vis : VisAt (∅ : Finset (Fin N)) (kVisAddr wb N Mc) x₁.mem := fun u => by
    simp [hx₁_zero u.val u.isLt]
  let x₂ := ((x₁.set finCnt 0).set compIdxReg 0).set iReg 0
  have hp : ExecWithin (B := .standard) w
      (ram[ finCnt ← cZero; compIdxReg ← cZero; iReg ← cZero ]) x₁ x₂ 3 := by
    have hc0 : x₁.regs cZero = 0 := (hx₁_fr cZero (by decide)).trans hregs.czero
    wram_exec [hc0]
  have hx₂_fr0 : ∀ r : Fin 28, r.val < 18 → x₂.regs r = x.regs r := fun r hr => by
    have h1 : r ≠ iReg := by reg_ne
    have h2 : r ≠ compIdxReg := by reg_ne
    have h3 : r ≠ finCnt := by reg_ne
    dsimp only [x₂]
    rw [Data.set_regs_of_ne h1, Data.set_regs_of_ne h2, Data.set_regs_of_ne h3]
    exact hx₁_fr r hr
  obtain ⟨y, hy_ex, hy_comp, hy_out, hy_fr⟩ :=
    peelLoop_spec hN revAdj ord hord_len wb Mc hmc_rev hfit ord 0 0 0 ∅ (fun _ => 0) x₂
      (by omega) (fun q _ => by simp) rfl (le_refl 0)
      (dfsRegs_of_frame hregs hx₂_fr0)
      ((hx₂_fr0 nVerts (by decide)).trans hNv)
      ((hx₂_fr0 ordB (by decide)).trans hordB)
      ((hx₂_fr0 compB (by decide)).trans hcompB)
      (by dsimp only [x₂]; wram_simp)
      (by dsimp only [x₂]; wram_simp)
      (by dsimp only [x₂]; wram_simp)
      hx₁_csr hx₁_ord hx₁_vis (fun _ hu => by simp at hu)
  have hsccs_eq : peelSCCs revAdj N ∅ ord = sccs adj (List.finRange N) := by
    simp [sccs, revAdj, ord]
  have hcond : IsSCCCondensation adj (sccs adj (List.finRange N)) :=
    isSCCCondensation_sccs List.mem_finRange
  have hflat_len : (sccs adj (List.finRange N)).flatten.length = N := by
    simpa using hcond.length_flatten_eq_card
  have hout_flat : outDegreeSum revAdj (sccs adj (List.finRange N)).flatten = csrOffset adj N := by
    rw [outDegreeSum, ← List.sum_toFinset _ hcond.nodup_flatten]
    have huniv : (sccs adj (List.finRange N)).flatten.toFinset = Finset.univ := by
      ext v; simp [hcond.mem_flatten v]
    rw [huniv, sum_length_transposeAdj, ← csrOffset_eq_outDegreeSum]
  rw [hsccs_eq, hord_len, hflat_len, hout_flat] at hy_ex
  refine ⟨y, (hx₁_ex.seq (hp.seq hy_ex)).mono (by omega), fun u => ?_, fun a ha => ?_,
    fun r hr => (hy_fr r hr).trans (hx₂_fr0 r hr)⟩
  · rw [hsccs_eq] at hy_comp
    exact hy_comp u (.inr (hcond.mem_flatten u))
  · exact (hy_out a ha).trans (hx₁_out a (by omega))

/-! ### Pass 4: Witness extraction and top-level Word-RAM solver (`O(n + |φ|)`) -/

private def extractVarBody : Code .standard 28 := ram[
  uReg ← cTwo * iReg;
  addr ← compB + uReg; jReg ← *addr;
  addr ← addr + cOne; jEndReg ← *addr;
  if jReg = jEndReg then [ compIdxReg ← cZero ]
  else [
    if jReg < jEndReg then [ vReg ← cOne ] else [ vReg ← cZero ];
    addr ← outBase + cTwo; addr ← addr + iReg; *addr ← vReg ];
  iReg ← iReg + cOne ]

private def extractAssignmentCode : Code .standard 28 :=
  (ram[ compIdxReg ← cOne; iReg ← cZero ]).seq
    ((Code.loop (.lt iReg nv) extractVarBody).seq
      (.branch (.eq compIdxReg cOne)
        (ram[ addr ← nv + cOne; *outBase ← addr; addr ← outBase + cOne; *addr ← cOne ])
        (ram[ *outBase ← cZero ])))

private theorem extractVarLoop_spec (G : Instance) {w : ℕ} (hfit : Fits w G.wordBound)
    (compIdx : Literal (Fin G.n) → ℕ) :
    ∀ (vs : List (Fin G.n)) (idx : ℕ) (ok : Bool) (x : Data 28)
      (_ : idx + vs.length = G.n),
      (∀ q (hq : q < vs.length), vs[q].val = idx + q) →
      (∀ u : Fin (2 * G.n),
        x.mem (kCompAddr G.workBase (2 * G.n) (2 * G.φ.length) + u.val) =
          compIdx ((litEquiv G.n).symm u)) →
      (∀ q : Fin G.n, q.val < idx → compIdx (q, true) ≠ compIdx (q, false) →
        x.mem (G.outAddrBase + 2 + q.val) =
          (decide (compIdx (q, false) < compIdx (q, true))).toNat) →
      x.regs cZero = 0 → x.regs cOne = 1 → x.regs cTwo = 2 → x.regs nv = G.n →
      x.regs outBase = G.outAddrBase →
      x.regs compB = kCompAddr G.workBase (2 * G.n) (2 * G.φ.length) →
      x.regs iReg = idx → x.regs compIdxReg = ok.toNat →
      ∃ y, ExecWithin w (.loop (.lt iReg nv) extractVarBody) x y (16 * vs.length + 2) ∧
        y.regs outBase = G.outAddrBase ∧ y.regs nv = G.n ∧
        y.regs cZero = 0 ∧ y.regs cOne = 1 ∧
        y.regs compIdxReg =
          (vs.foldl (fun acc v => acc && decide (compIdx (v, true) ≠ compIdx (v, false)))
            ok).toNat ∧
        (∀ v : Fin G.n, compIdx (v, true) ≠ compIdx (v, false) →
          y.mem (G.outAddrBase + 2 + v.val) =
            (decide (compIdx (v, false) < compIdx (v, true))).toNat)
  | [], idx, ok, x, hidx, _, _, hout_prev, hc0, hc1, _, hnv, hob, _, hi, hok => by
    simp only [List.length_nil, Nat.add_zero] at hidx
    have hend : ¬ (Cond.lt iReg nv).Holds x := by
      change ¬ x.regs iReg < x.regs nv; omega
    refine ⟨x, ⟨2, by simp, Exec.loop_exit hend⟩, hob, hnv, hc0, hc1, hok, fun v hne => ?_⟩
    exact hout_prev v (by have := v.isLt; omega) hne
  | v :: vs, idx, ok, x, hidx, hvs, hcomp, hout_prev, hc0, hc1, hc2, hnv, hob, hcb, hi, hok => by
    simp only [List.length_cons] at hidx
    have hv_val : v.val = idx := by
      have h0 := hvs 0 (by simp)
      rwa [List.getElem_cons_zero, Nat.add_zero] at h0
    set compBase := kCompAddr G.workBase (2 * G.n) (2 * G.φ.length)
    have hm_f : x.mem (compBase + 2 * idx) = compIdx (v, false) := by
      have hu := hcomp (litEquiv G.n (v, false))
      rw [Equiv.symm_apply_apply] at hu
      simpa [litEquiv, litCodeBy, hv_val] using hu
    have hm_t : x.mem (compBase + 2 * idx + 1) = compIdx (v, true) := by
      have hu := hcomp (litEquiv G.n (v, true))
      rw [Equiv.symm_apply_apply] at hu
      simpa [litEquiv, litCodeBy, hv_val, Nat.add_assoc] using hu
    have hf_2i : Fits w (2 * idx) := G.fits_of_le hfit (by unfold Instance.wordBound; omega)
    have hf_cf : Fits w (compBase + 2 * idx) :=
      G.fits_of_le hfit (by
        simp only [compBase, kCompAddr, Instance.workBase, Instance.outAddrBase,
          G.encode_length, Instance.wordBound]; omega)
    have hf_ct : Fits w (compBase + 2 * idx + 1) :=
      G.fits_of_le hfit (by
        simp only [compBase, kCompAddr, Instance.workBase, Instance.outAddrBase,
          G.encode_length, Instance.wordBound]; omega)
    have hf_ob2 : Fits w (G.outAddrBase + 2) :=
      G.fits_of_le hfit (by
        simp only [Instance.outAddrBase, G.encode_length, Instance.wordBound]; omega)
    have hf_ob2i : Fits w (G.outAddrBase + 2 + idx) :=
      G.fits_of_le hfit (by
        simp only [Instance.outAddrBase, G.encode_length, Instance.wordBound]; omega)
    have hf_i1 : Fits w (idx + 1) := G.fits_of_le hfit (by unfold Instance.wordBound; omega)
    let VarPost (x₁ : Data 28) : Prop :=
      (∀ u : Fin (2 * G.n), x₁.mem (compBase + u.val) = compIdx ((litEquiv G.n).symm u)) ∧
        (∀ q : Fin G.n, q.val < idx + 1 → compIdx (q, true) ≠ compIdx (q, false) →
          x₁.mem (G.outAddrBase + 2 + q.val) =
            (decide (compIdx (q, false) < compIdx (q, true))).toNat) ∧
        x₁.regs cZero = 0 ∧ x₁.regs cOne = 1 ∧ x₁.regs cTwo = 2 ∧ x₁.regs nv = G.n ∧
        x₁.regs outBase = G.outAddrBase ∧ x₁.regs compB = compBase ∧
        x₁.regs iReg = idx + 1 ∧
        x₁.regs compIdxReg = (ok && decide (compIdx (v, true) ≠ compIdx (v, false))).toNat
    have hstep : ∃ x₁, ExecWithin w extractVarBody x x₁ 14 ∧ VarPost x₁ := by
      unfold extractVarBody
      wram_exec [hc0, hc1, hc2, hnv, hob, hcb, hi, hok, hm_f, hm_t,
        hf_2i, hf_cf, hf_ct, hf_ob2, hf_ob2i, hf_i1]
      · -- equal components: compIdx (v, false) = compIdx (v, true)
        dsimp only [VarPost]
        refine ⟨hcomp, fun q hq hne_q => ?_, by wram_simp; exact hc0, by wram_simp; exact hc1,
          by wram_simp; exact hc2, by wram_simp; exact hnv, by wram_simp; exact hob,
          by wram_simp; exact hcb, by wram_simp, ?_⟩
        · by_cases hqi : q = v
          · subst hqi
            exact absurd ‹compIdx (q, false) = compIdx (q, true)›.symm hne_q
          · have hqv : q.val ≠ idx := fun h => hqi (Fin.ext (h.trans hv_val.symm))
            exact hout_prev q (by omega) hne_q
        · wram_simp
          simp [‹compIdx (v, false) = compIdx (v, true)›]
      · -- compIdx (v, false) < compIdx (v, true)
        dsimp only [VarPost]
        refine ⟨fun u => ?_, fun q hq hne_q => ?_, by wram_simp; exact hc0,
          by wram_simp; exact hc1, by wram_simp; exact hc2, by wram_simp; exact hnv,
          by wram_simp; exact hob, by wram_simp; exact hcb, by wram_simp, ?_⟩
        · mem_upd
          rw [Function.update_of_ne (by
            simp only [compBase, kCompAddr, Instance.workBase]; omega)]
          exact hcomp u
        · mem_upd
          by_cases hqi : q = v
          · subst hqi
            rw [hv_val, Function.update_self]
            simp [‹compIdx (q, false) < compIdx (q, true)›]
          · have hqv : q.val ≠ idx := fun h => hqi (Fin.ext (h.trans hv_val.symm))
            rw [Function.update_of_ne (by omega)]
            exact hout_prev q (by omega) hne_q
        · wram_simp
          have hne_v : compIdx (v, true) ≠ compIdx (v, false) := by omega
          simp [hne_v, hok]
      · -- compIdx (v, false) > compIdx (v, true)
        dsimp only [VarPost]
        refine ⟨fun u => ?_, fun q hq hne_q => ?_, by wram_simp; exact hc0,
          by wram_simp; exact hc1, by wram_simp; exact hc2, by wram_simp; exact hnv,
          by wram_simp; exact hob, by wram_simp; exact hcb, by wram_simp, ?_⟩
        · mem_upd
          rw [Function.update_of_ne (by
            simp only [compBase, kCompAddr, Instance.workBase]; omega)]
          exact hcomp u
        · mem_upd
          by_cases hqi : q = v
          · subst hqi
            rw [hv_val, Function.update_self]
            simp [‹¬ compIdx (q, false) < compIdx (q, true)›]
          · have hqv : q.val ≠ idx := fun h => hqi (Fin.ext (h.trans hv_val.symm))
            rw [Function.update_of_ne (by omega)]
            exact hout_prev q (by omega) hne_q
        · wram_simp
          have hne_v : compIdx (v, true) ≠ compIdx (v, false) :=
            fun h => ‹compIdx (v, false) ≠ compIdx (v, true)› h.symm
          simp [hne_v, hok]
    obtain ⟨x₁, hx₁_ex, hx₁_comp, hx₁_prev, hx₁_0, hx₁_1, hx₁_2, hx₁_nv, hx₁_ob, hx₁_cb,
      hx₁_i, hx₁_ok⟩ := hstep
    obtain ⟨y, hy_ex, hy_ob, hy_nv, hy_0, hy_1, hy_ok, hy_bits⟩ :=
      extractVarLoop_spec G hfit compIdx vs (idx + 1)
        (ok && decide (compIdx (v, true) ≠ compIdx (v, false))) x₁ (by omega)
        (fun q hq => by
          have h := hvs (q + 1) (by simp; omega)
          simpa [Nat.add_assoc, Nat.add_comm 1 q] using h)
        hx₁_comp hx₁_prev hx₁_0 hx₁_1 hx₁_2 hx₁_nv hx₁_ob hx₁_cb hx₁_i hx₁_ok
    obtain ⟨t₁, ht₁, he₁⟩ := hx₁_ex
    obtain ⟨t₂, ht₂, he₂⟩ := hy_ex
    have hlt : (Cond.lt iReg nv).Holds x := by
      change x.regs iReg < x.regs nv; omega
    exact ⟨y, ⟨t₁ + t₂ + 2, by simp only [List.length_cons]; omega, Exec.loop_iter hlt he₁ he₂⟩,
      hy_ob, hy_nv, hy_0, hy_1, hy_ok, hy_bits⟩

private def setupWorkRegsCode : Code .standard 28 := ram[
  nVerts ← cTwo * nv;
  uReg ← cTwo * mClauses;
  offB ← outBase + nv; offB ← offB + cTwo;
  edgeB ← offB + nVerts; edgeB ← edgeB + cOne;
  revOffB ← edgeB + uReg;
  revEdgeB ← revOffB + nVerts; revEdgeB ← revEdgeB + cOne;
  curB ← revEdgeB + uReg;
  visB ← curB + nVerts; visB ← visB + cOne;
  ordB ← visB + nVerts;
  finB ← ordB;
  stkB ← ordB + nVerts; stkB ← stkB + nVerts;
  compB ← stkB + nVerts; compB ← compB + nVerts; compB ← compB + nVerts ]

/-- Structured standard-basis Word-RAM solver for 2-SAT. -/
def solver : Code .standard 28 :=
  headerSetupCode.seq
    (checkClausesCode.seq
      (.branch (.eq compIdxReg cOne)
        (.branch (.eq nv cZero)
          (ram[ *outBase ← cOne; addr ← outBase + cOne; *addr ← cOne ])
          (setupWorkRegsCode.seq
            (buildImplCSRCode.seq
              (forwardDFSCode.seq
                (transposeCSRCode.seq
                  ((ram[ finB ← ordB + nVerts ]).seq
                    (kosarajuIndexCode.seq
                      extractAssignmentCode)))))))
        (ram[ *outBase ← cZero ])))

/-- Flat standard-basis Word-RAM 2-SAT program returning `answerWords G` via `ExecutesList`. -/
def program : Program .standard 28 := solver.program outBase

/-- Structured execution of `solver` computes `answerWords G` at `outAddrBase` within
`512 * (G.n + G.φ.length + 1) - 1` instructions. -/
theorem solver_spec (G : Instance) {w : ℕ} (hfit : Fits w G.wordBound) :
    ∃ y, ExecWithin w solver (Data.init G.encode) y (512 * (G.n + G.φ.length + 1) - 1) ∧
      y.regs outBase = G.outAddrBase ∧ outputList y.mem (y.regs outBase) = answerWords G := by
  have hm0 : (Data.init G.encode : Data 28).mem 0 = G.encode.length := Data.init_mem_zero _
  have hm1 : (Data.init G.encode : Data 28).mem 1 = G.n := rfl
  have hm2 : (Data.init G.encode : Data 28).mem 2 = G.φ.length := rfl
  have hf1 : Fits w 1 := G.fits_of_le hfit (by unfold Instance.wordBound; omega)
  have hf2 : Fits w 2 := G.fits_of_le hfit (by unfold Instance.wordBound; omega)
  have hf3 : Fits w 3 := G.fits_of_le hfit (by unfold Instance.wordBound; omega)
  have hf_ob : Fits w (G.encode.length + 1) :=
    G.fits_of_le hfit (by simp only [G.encode_length, Instance.wordBound]; omega)
  have hsetup0 : ∃ s₀, ExecWithin w headerSetupCode (Data.init G.encode) s₀ 8 ∧
      s₀.mem = (Data.init G.encode : Data 28).mem ∧
      s₀.regs cZero = 0 ∧ s₀.regs cOne = 1 ∧ s₀.regs cTwo = 2 ∧ s₀.regs cThree = 3 ∧
      s₀.regs outBase = G.outAddrBase ∧ s₀.regs nv = G.n ∧ s₀.regs mClauses = G.φ.length := by
    let Setup0Post (s₀ : Data 28) : Prop :=
      s₀.mem = (Data.init G.encode : Data 28).mem ∧
        s₀.regs cZero = 0 ∧ s₀.regs cOne = 1 ∧ s₀.regs cTwo = 2 ∧ s₀.regs cThree = 3 ∧
        s₀.regs outBase = G.outAddrBase ∧ s₀.regs nv = G.n ∧ s₀.regs mClauses = G.φ.length
    change ∃ s₀, ExecWithin w headerSetupCode (Data.init G.encode) s₀ 8 ∧ Setup0Post s₀
    unfold headerSetupCode
    wram_exec [Data.init_regs, hm0, hm1, hm2, hf1, hf2, hf3, hf_ob]
    dsimp only [Setup0Post]
    exact ⟨rfl, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
      by wram_simp; rfl, by wram_simp, by wram_simp⟩
  obtain ⟨s₀, hsetup, hs₀_mem, hs₀_0, hs₀_1, hs₀_2, hs₀_3, hs₀_ob, hs₀_nv, hs₀_mc⟩ := hsetup0
  let s₁ := ((s₀.set compIdxReg 1).set pReg 3).set iReg 0
  have hchk_prep : ExecWithin (B := .standard) w
      (ram[ compIdxReg ← cOne; pReg ← cThree; iReg ← cZero ]) s₀ s₁ 3 := by
    wram_exec [hs₀_1, hs₀_3, hs₀_0]
  have hlen_enc : 3 + (G.φ.flatMap (encodeClauseBy Fin.val)).length = G.encode.length + 1 := by
    rw [Instance.length_flatMap_encodeClauseBy, G.encode_length]
    unfold Instance.totalLits; omega
  obtain ⟨s₂, hs₂_ex, hs₂_mem, hs₂_ok, hs₂_fr⟩ :=
    checkClausesLoop_spec G hfit G.φ 0 3 true s₁ (by simp) hlen_enc
      (hs₀_mem ▸ clauseMemAt_init G)
      (by dsimp only [s₁]; wram_simp; exact hs₀_0)
      (by dsimp only [s₁]; wram_simp; exact hs₀_1)
      (by dsimp only [s₁]; wram_simp; exact hs₀_2)
      (by dsimp only [s₁]; wram_simp; exact hs₀_mc)
      (by dsimp only [s₁]; wram_simp)
      (by dsimp only [s₁]; wram_simp)
      (by dsimp only [s₁]; wram_simp; rfl)
  have hchk_ex : ExecWithin w checkClausesCode s₀ s₂ (12 * G.φ.length + 5) :=
    (hchk_prep.seq hs₂_ex).mono (by omega)
  have hs₂_fr0 : ∀ r : Fin 28, r.val < 18 → s₂.regs r = s₀.regs r := fun r hr => by
    rw [hs₂_fr r hr]
    dsimp only [s₁]
    have h1 : r ≠ iReg := by reg_ne
    have h2 : r ≠ pReg := by reg_ne
    have h3 : r ≠ compIdxReg := by reg_ne
    simp [Data.set_regs_of_ne h1, Data.set_regs_of_ne h2, Data.set_regs_of_ne h3]
  have hs₂_0 : s₂.regs cZero = 0 := (hs₂_fr0 cZero (by decide)).trans hs₀_0
  have hs₂_1 : s₂.regs cOne = 1 := (hs₂_fr0 cOne (by decide)).trans hs₀_1
  have hs₂_2 : s₂.regs cTwo = 2 := (hs₂_fr0 cTwo (by decide)).trans hs₀_2
  have hs₂_3 : s₂.regs cThree = 3 := (hs₂_fr0 cThree (by decide)).trans hs₀_3
  have hs₂_ob : s₂.regs outBase = G.outAddrBase := (hs₂_fr0 outBase (by decide)).trans hs₀_ob
  have hs₂_nv : s₂.regs nv = G.n := (hs₂_fr0 nv (by decide)).trans hs₀_nv
  have hs₂_mc : s₂.regs mClauses = G.φ.length := (hs₂_fr0 mClauses (by decide)).trans hs₀_mc
  cases hchk : checkClauses G.φ
  · -- Invalid clause width: return `[]`
    have hs₂_ok0 : s₂.regs compIdxReg = 0 := by
      rw [hs₂_ok, show G.φ.foldl (fun acc c => acc && isValidTwoClause c) true =
        checkClauses G.φ from rfl, hchk]
      rfl
    have hncond : ¬ (Cond.eq compIdxReg cOne).Holds s₂ := by
      change ¬ s₂.regs compIdxReg = s₂.regs cOne; omega
    have hneg : Exec (B := .standard) w (ram[ *outBase ← cZero ])
        s₂ (s₂.write G.outAddrBase 0) 1 := by
      have hst := Exec.store (B := .standard) (w := w) (x := s₂) (a := outBase) (s := cZero)
      rwa [hs₂_ob, hs₂_0] at hst
    have hbr : ExecWithin w
        (.branch (.eq compIdxReg cOne)
          (.branch (.eq nv cZero)
            (ram[ *outBase ← cOne; addr ← outBase + cOne; *addr ← cOne ])
            (setupWorkRegsCode.seq
              (buildImplCSRCode.seq
                (forwardDFSCode.seq
                  (transposeCSRCode.seq
                    ((ram[ finB ← ordB + nVerts ]).seq
                      (kosarajuIndexCode.seq
                        extractAssignmentCode)))))))
          (ram[ *outBase ← cZero ]))
        s₂ (s₂.write G.outAddrBase 0) 3 :=
      ⟨3, le_rfl, Exec.branch_neg hncond hneg⟩
    refine ⟨s₂.write G.outAddrBase 0,
      (hsetup.seq (hchk_ex.seq hbr)).mono (by omega),
      hs₂_ob, ?_⟩
    rw [Data.write_regs_apply, hs₂_ob, outputList_eq_iff]
    have hans : answerWords G = [] := by simp [answerWords, solveFin, solve, hchk]
    rw [hans]
    exact ⟨Data.write_mem_self _ _ _, Block.holdsList_nil _ _⟩
  · -- Valid 2-CNF: every clause has `1 ≤ length ≤ 2`
    have hs₂_ok1 : s₂.regs compIdxReg = 1 := by
      rw [hs₂_ok, show G.φ.foldl (fun acc c => acc && isValidTwoClause c) true =
        checkClauses G.φ from rfl, hchk]
      rfl
    have hcond_chk : (Cond.eq compIdxReg cOne).Holds s₂ := by
      change s₂.regs compIdxReg = s₂.regs cOne; omega
    obtain ⟨hw_φ, hnil_φ⟩ := (checkClauses_eq_true_iff G.φ).1 hchk
    have hcs_φ : ∀ c ∈ G.φ, 1 ≤ c.length ∧ c.length ≤ 2 := fun c hc => by
      refine ⟨?_, hw_φ c hc⟩
      cases c with
      | nil => exact absurd hc hnil_φ
      | cons _ _ => simp
    by_cases hn0 : G.n = 0
    · -- `G.n = 0`: `G.φ = []`, `answerWords G = [1]`
      have hφ_nil : G.φ = [] := by
        cases hφ : G.φ with
        | nil => rfl
        | cons c cs =>
          have hc1 := (hcs_φ c (by simp [hφ])).1
          cases c with
          | nil => simp at hc1
          | cons ℓ _ =>
            have := ℓ.1.isLt
            omega
      have hcond_n0 : (Cond.eq nv cZero).Holds s₂ := by
        change s₂.regs nv = s₂.regs cZero; omega
      have hf_ob1 : Fits w (G.outAddrBase + 1) :=
        G.fits_of_le hfit (by
          simp only [Instance.outAddrBase, G.encode_length, Instance.wordBound]; omega)
      let y_n0 := ((s₂.write G.outAddrBase 1).set addr (G.outAddrBase + 1)).write
        (G.outAddrBase + 1) 1
      have hpos_n0 : ExecWithin w
          (ram[ *outBase ← cOne; addr ← outBase + cOne; *addr ← cOne ]) s₂ y_n0 3 := by
        have htriv : y_n0 = ((s₂.write G.outAddrBase 1).set addr (G.outAddrBase + 1)).write
          (G.outAddrBase + 1) 1 := rfl
        wram_exec [hs₂_ob, hs₂_1, hf_ob1]
      obtain ⟨tn0, htn0, hen0⟩ := hpos_n0
      have hbr_inner : Exec w
          (.branch (.eq nv cZero)
            (ram[ *outBase ← cOne; addr ← outBase + cOne; *addr ← cOne ])
            (setupWorkRegsCode.seq
              (buildImplCSRCode.seq
                (forwardDFSCode.seq
                  (transposeCSRCode.seq
                    ((ram[ finB ← ordB + nVerts ]).seq
                      (kosarajuIndexCode.seq
                        extractAssignmentCode)))))))
          s₂ y_n0 (tn0 + 1) :=
        Exec.branch_pos hcond_n0 hen0
      have hbr_outer : ExecWithin w
          (.branch (.eq compIdxReg cOne)
            (.branch (.eq nv cZero)
              (ram[ *outBase ← cOne; addr ← outBase + cOne; *addr ← cOne ])
              (setupWorkRegsCode.seq
                (buildImplCSRCode.seq
                  (forwardDFSCode.seq
                    (transposeCSRCode.seq
                      ((ram[ finB ← ordB + nVerts ]).seq
                        (kosarajuIndexCode.seq
                          extractAssignmentCode)))))))
            (ram[ *outBase ← cZero ]))
          s₂ y_n0 5 :=
        ⟨tn0 + 2, by omega, Exec.branch_pos hcond_chk hbr_inner⟩
      refine ⟨y_n0, (hsetup.seq (hchk_ex.seq hbr_outer)).mono (by omega),
        by dsimp only [y_n0]; wram_simp; exact hs₂_ob, ?_⟩
      have hob_y : y_n0.regs outBase = G.outAddrBase := by
        dsimp only [y_n0]; wram_simp; exact hs₂_ob
      rw [hob_y, outputList_eq_iff]
      have hans : answerWords G = [1] := by
        cases G with
        | mk n φ =>
          dsimp only at hn0 hφ_nil
          subst hn0 hφ_nil
          rfl
      rw [hans]
      refine ⟨?_, fun i => ?_⟩
      · dsimp only [y_n0]
        rw [Data.write_mem_of_ne (by omega), Data.set_mem, Data.write_mem_self]
        rfl
      · rcases i with ⟨_ | k, hlt⟩
        · dsimp only [Block.read, y_n0]
          rw [Nat.add_zero, Data.write_mem_self]
          rfl
        · change k + 1 < 1 at hlt
          omega
    · -- `0 < G.n`: full Kosaraju + witness extraction
      have hn_pos : 0 < G.n := Nat.pos_of_ne_zero hn0
      have hN_pos : 0 < 2 * G.n := by omega
      have hncond_n0 : ¬ (Cond.eq nv cZero).Holds s₂ := by
        change ¬ s₂.regs nv = s₂.regs cZero; omega
      set wb := G.workBase
      set N := 2 * G.n
      set Mc := 2 * G.φ.length
      have hfit_top : Fits w (kTopAddr wb N Mc + Mc + 4) :=
        G.fits_of_le hfit (by
          simp only [wb, N, Mc, kTopAddr, Instance.workBase, Instance.outAddrBase,
            G.encode_length, Instance.wordBound]; omega)
      have hsetup_regs : ∃ s₃, ExecWithin w setupWorkRegsCode s₂ s₃ 19 ∧
          s₃.mem = s₂.mem ∧
          s₃.regs cZero = 0 ∧ s₃.regs cOne = 1 ∧ s₃.regs cTwo = 2 ∧ s₃.regs cThree = 3 ∧
          s₃.regs nv = G.n ∧ s₃.regs mClauses = G.φ.length ∧ s₃.regs nVerts = N ∧
          s₃.regs outBase = G.outAddrBase ∧
          s₃.regs offB = kOffAddr wb ∧ s₃.regs edgeB = kEdgeAddr wb N ∧
          s₃.regs revOffB = kRevOffAddr wb N Mc ∧ s₃.regs revEdgeB = kRevEdgeAddr wb N Mc ∧
          s₃.regs curB = kCurAddr wb N Mc ∧ s₃.regs visB = kVisAddr wb N Mc ∧
          s₃.regs ordB = kOrdAddr wb N Mc ∧ s₃.regs finB = kOrdAddr wb N Mc ∧
          s₃.regs stkB = kStkAddr wb N Mc ∧ s₃.regs compB = kCompAddr wb N Mc := by
        let SetupPost (s₃ : Data 28) : Prop :=
          s₃.mem = s₂.mem ∧
            s₃.regs cZero = 0 ∧ s₃.regs cOne = 1 ∧ s₃.regs cTwo = 2 ∧ s₃.regs cThree = 3 ∧
            s₃.regs nv = G.n ∧ s₃.regs mClauses = G.φ.length ∧ s₃.regs nVerts = N ∧
            s₃.regs outBase = G.outAddrBase ∧
            s₃.regs offB = kOffAddr wb ∧ s₃.regs edgeB = kEdgeAddr wb N ∧
            s₃.regs revOffB = kRevOffAddr wb N Mc ∧ s₃.regs revEdgeB = kRevEdgeAddr wb N Mc ∧
            s₃.regs curB = kCurAddr wb N Mc ∧ s₃.regs visB = kVisAddr wb N Mc ∧
            s₃.regs ordB = kOrdAddr wb N Mc ∧ s₃.regs finB = kOrdAddr wb N Mc ∧
            s₃.regs stkB = kStkAddr wb N Mc ∧ s₃.regs compB = kCompAddr wb N Mc
        change ∃ s₃, ExecWithin w setupWorkRegsCode s₂ s₃ 19 ∧ SetupPost s₃
        unfold setupWorkRegsCode
        wram_exec [hs₂_0, hs₂_1, hs₂_2, hs₂_3, hs₂_ob, hs₂_nv, hs₂_mc]
        · dsimp only [SetupPost]
          refine ⟨rfl, by wram_simp; exact hs₂_0, by wram_simp; exact hs₂_1,
            by wram_simp; exact hs₂_2, by wram_simp; exact hs₂_3,
            by wram_simp; exact hs₂_nv, by wram_simp; exact hs₂_mc, by wram_simp; rfl,
            by wram_simp; exact hs₂_ob, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          all_goals wram_simp
          all_goals
            dsimp only [wb, N, Mc, Instance.workBase, kOffAddr, kEdgeAddr, kRevOffAddr,
              kRevEdgeAddr, kCurAddr, kVisAddr, kOrdAddr, kStkAddr, kCompAddr]
          all_goals omega
        all_goals
          exact hfit_top.of_le (by
            dsimp only [wb, N, Mc, Instance.workBase, kTopAddr]
            omega)
      obtain ⟨s₃, hs₃_ex, hs₃_mem, hs₃_0, hs₃_1, hs₃_2, hs₃_3, hs₃_nv, hs₃_mc, hs₃_Nv, hs₃_ob,
        hs₃_off, hs₃_edge, hs₃_roff, hs₃_redge, hs₃_cur, hs₃_vis, hs₃_ord, hs₃_fin,
        hs₃_stk, hs₃_comp⟩ := hsetup_regs
      have hcm₃ : ClauseMemAt s₃.mem 3 G.φ :=
        hs₃_mem ▸ hs₂_mem ▸ hs₀_mem ▸ clauseMemAt_init G
      obtain ⟨s₄, hs₄_ex, hs₄_csr, _, hs₄_fr⟩ :=
        buildImplCSRCode_spec G hfit hcs_φ hcm₃ hs₃_0 hs₃_1 hs₃_3 hs₃_mc hs₃_Nv
          hs₃_off hs₃_edge hs₃_cur
      have hmc_adj : csrOffset G.adjFin N ≤ Mc := csrOffset_adjFin_le G
      have hs₄_dregs : DfsRegs (kOffAddr wb) (kEdgeAddr wb N) (kVisAddr wb N Mc)
          (kOrdAddr wb N Mc) (kStkAddr wb N Mc) s₄ :=
        { czero := (hs₄_fr cZero (by decide)).trans hs₃_0
          cone := (hs₄_fr cOne (by decide)).trans hs₃_1
          cthree := (hs₄_fr cThree (by decide)).trans hs₃_3
          hoff := (hs₄_fr offB (by decide)).trans hs₃_off
          hedge := (hs₄_fr edgeB (by decide)).trans hs₃_edge
          hvis := (hs₄_fr visB (by decide)).trans hs₃_vis
          hfin := (hs₄_fr finB (by decide)).trans hs₃_fin
          hstk := (hs₄_fr stkB (by decide)).trans hs₃_stk }
      obtain ⟨s₅, hs₅_ex, hs₅_olen, hs₅_omem, hs₅_csr, _, hs₅_fr⟩ :=
        forwardDFSCode_spec hN_pos G.adjFin wb Mc hmc_adj hfit_top hs₄_dregs
          ((hs₄_fr nVerts (by decide)).trans hs₃_Nv) hs₄_csr
      have hs₅_fr3 : ∀ r : Fin 28, r.val < 18 → s₅.regs r = s₃.regs r :=
        fun r hr => (hs₅_fr r hr).trans (hs₄_fr r hr)
      obtain ⟨s₆, hs₆_ex, hs₆_rcsr, hs₆_off, hs₆_edge, hs₆_out, hs₆_fr⟩ :=
        transposeCSRCode_spec G.adjFin wb Mc hmc_adj hfit_top
          ((hs₅_fr3 cZero (by decide)).trans hs₃_0)
          ((hs₅_fr3 cOne (by decide)).trans hs₃_1)
          ((hs₅_fr3 nVerts (by decide)).trans hs₃_Nv)
          ((hs₅_fr3 offB (by decide)).trans hs₃_off)
          ((hs₅_fr3 edgeB (by decide)).trans hs₃_edge)
          ((hs₅_fr3 curB (by decide)).trans hs₃_cur)
          ((hs₅_fr3 revOffB (by decide)).trans hs₃_roff)
          ((hs₅_fr3 revEdgeB (by decide)).trans hs₃_redge)
          hs₅_csr
      have hs₆_fr3 : ∀ r : Fin 28, r.val < 18 → r ≠ offB → r ≠ edgeB → s₆.regs r = s₃.regs r :=
        fun r hr hno hne => (hs₆_fr r hr hno hne).trans (hs₅_fr3 r hr)
      have hf_finB : Fits w (kFinAddr wb N Mc) :=
        hfit_top.of_le (by simp only [kFinAddr, kTopAddr]; omega)
      let s₆' := s₆.set finB (kFinAddr wb N Mc)
      have hp_finB : ExecWithin w (ram[ finB ← ordB + nVerts ]) s₆ s₆' 1 := by
        have h_ordB : s₆.regs ordB = kOrdAddr wb N Mc :=
          (hs₆_fr3 ordB (by decide) (by decide) (by decide)).trans hs₃_ord
        have h_Nv : s₆.regs nVerts = N :=
          (hs₆_fr3 nVerts (by decide) (by decide) (by decide)).trans hs₃_Nv
        have htriv : s₆' = s₆.set finB (kOrdAddr wb N Mc + N) := by
          simp [s₆', kOrdAddr, kFinAddr]; ring_nf
        rw [htriv]
        have hf_on : Fits w (kOrdAddr wb N Mc + N) :=
          hfit_top.of_le (by simp only [kOrdAddr, kTopAddr]; omega)
        wram_exec [h_ordB, h_Nv, hf_on]
      have hs₆'_dregs : DfsRegs (kRevOffAddr wb N Mc) (kRevEdgeAddr wb N Mc)
          (kVisAddr wb N Mc) (kFinAddr wb N Mc) (kStkAddr wb N Mc) s₆' :=
        { czero := by
            dsimp only [s₆']; wram_simp
            exact (hs₆_fr3 cZero (by decide) (by decide) (by decide)).trans hs₃_0
          cone := by
            dsimp only [s₆']; wram_simp
            exact (hs₆_fr3 cOne (by decide) (by decide) (by decide)).trans hs₃_1
          cthree := by
            dsimp only [s₆']; wram_simp
            exact (hs₆_fr3 cThree (by decide) (by decide) (by decide)).trans hs₃_3
          hoff := by dsimp only [s₆']; wram_simp; exact hs₆_off
          hedge := by dsimp only [s₆']; wram_simp; exact hs₆_edge
          hvis := by
            dsimp only [s₆']; wram_simp
            exact (hs₆_fr3 visB (by decide) (by decide) (by decide)).trans hs₃_vis
          hfin := by dsimp only [s₆']; wram_simp
          hstk := by
            dsimp only [s₆']; wram_simp
            exact (hs₆_fr3 stkB (by decide) (by decide) (by decide)).trans hs₃_stk }
      have hs₆'_omem : ∀ idx (hidx : idx < N),
          s₆'.mem (kOrdAddr wb N Mc + (N - 1 - idx)) =
            ((topologicalSort G.adjFin (List.finRange N))[idx]'(by
              rw [length_topologicalSort_finRange]; exact hidx)).val :=
        fun idx hidx => by
          dsimp only [s₆']; mem_upd
          rw [hs₆_out _ (by dsimp only [kRevOffAddr, kRevEdgeAddr, kCurAddr, kOrdAddr]; omega)]
          exact hs₅_omem idx hidx
      obtain ⟨s₇, hs₇_ex, hs₇_comp, _, hs₇_fr⟩ :=
        kosarajuIndexCode_spec hN_pos G.adjFin wb Mc hmc_adj hfit_top hs₆'_dregs
          (by
            dsimp only [s₆']; wram_simp
            exact (hs₆_fr3 nVerts (by decide) (by decide) (by decide)).trans hs₃_Nv)
          (by
            dsimp only [s₆']; wram_simp
            exact (hs₆_fr3 ordB (by decide) (by decide) (by decide)).trans hs₃_ord)
          (by
            dsimp only [s₆']; wram_simp
            exact (hs₆_fr3 compB (by decide) (by decide) (by decide)).trans hs₃_comp)
          hs₆_rcsr hs₅_olen hs₆'_omem
      have hs₇_fr3 : ∀ r : Fin 28, r.val < 18 → r ≠ offB → r ≠ edgeB → r ≠ finB →
          s₇.regs r = s₃.regs r := fun r hr h1 h2 h3 => by
        rw [hs₇_fr r hr]
        dsimp only [s₆']
        rw [Data.set_regs_of_ne h3]
        exact hs₆_fr3 r hr h1 h2
      set compIdx := indexComponents (sccs (implicationAdj G.φ) (literalList (List.finRange G.n)))
      have hs₇_comp' : ∀ u : Fin (2 * G.n),
          s₇.mem (kCompAddr wb N Mc + u.val) = compIdx ((litEquiv G.n).symm u) := fun u => by
        rw [hs₇_comp u]
        have htr := G.indexComponents_adjFin ((litEquiv G.n).symm u)
        rwa [Equiv.apply_symm_apply] at htr
      let s₇' := (s₇.set compIdxReg 1).set iReg 0
      have hp_ext : ExecWithin (B := .standard) w (ram[ compIdxReg ← cOne; iReg ← cZero ])
          s₇ s₇' 2 := by
        have h1' : s₇.regs cOne = 1 :=
          (hs₇_fr3 cOne (by decide) (by decide) (by decide) (by decide)).trans hs₃_1
        have h0' : s₇.regs cZero = 0 :=
          (hs₇_fr3 cZero (by decide) (by decide) (by decide) (by decide)).trans hs₃_0
        wram_exec [h1', h0']
      obtain ⟨s₈, hs₈_ex, hs₈_ob, hs₈_nv, hs₈_0, hs₈_1, hs₈_ok, hs₈_bits⟩ :=
        extractVarLoop_spec G hfit compIdx (List.finRange G.n) 0 true s₇' (by simp)
          (fun q _ => by simp) hs₇_comp' (fun _ hq _ => by omega)
          (by
            dsimp only [s₇']; wram_simp
            exact (hs₇_fr3 cZero (by decide) (by decide) (by decide) (by decide)).trans hs₃_0)
          (by
            dsimp only [s₇']; wram_simp
            exact (hs₇_fr3 cOne (by decide) (by decide) (by decide) (by decide)).trans hs₃_1)
          (by
            dsimp only [s₇']; wram_simp
            exact (hs₇_fr3 cTwo (by decide) (by decide) (by decide) (by decide)).trans hs₃_2)
          (by
            dsimp only [s₇']; wram_simp
            exact (hs₇_fr3 nv (by decide) (by decide) (by decide) (by decide)).trans hs₃_nv)
          (by
            dsimp only [s₇']; wram_simp
            exact (hs₇_fr3 outBase (by decide) (by decide) (by decide) (by decide)).trans hs₃_ob)
          (by
            dsimp only [s₇']; wram_simp
            exact (hs₇_fr3 compB (by decide) (by decide) (by decide) (by decide)).trans hs₃_comp)
          (by dsimp only [s₇']; wram_simp)
          (by dsimp only [s₇']; wram_simp; rfl)
      rw [List.length_finRange] at hs₈_ex
      have hfin_ext : ∃ y, ExecWithin w
          (.branch (.eq compIdxReg cOne)
            (ram[ addr ← nv + cOne; *outBase ← addr; addr ← outBase + cOne; *addr ← cOne ])
            (ram[ *outBase ← cZero ]))
          s₈ y 5 ∧ y.regs outBase = G.outAddrBase ∧
          outputList y.mem G.outAddrBase = answerWords G := by
        set ok_all := (List.finRange G.n).foldl
          (fun acc v => acc && decide (compIdx (v, true) ≠ compIdx (v, false))) true
        cases hok_all : ok_all
        · have hs₈_ok0 : s₈.regs compIdxReg = 0 := by rw [hs₈_ok, hok_all]; rfl
          have hncond_ok : ¬ (Cond.eq compIdxReg cOne).Holds s₈ := by
            change ¬ s₈.regs compIdxReg = s₈.regs cOne; omega
          have hneg : Exec (B := .standard) w (ram[ *outBase ← cZero ])
              s₈ (s₈.write G.outAddrBase 0) 1 := by
            have hst := Exec.store (B := .standard) (w := w) (x := s₈) (a := outBase) (s := cZero)
            rwa [hs₈_ob, hs₈_0] at hst
          refine ⟨s₈.write G.outAddrBase 0, ⟨3, by omega, Exec.branch_neg hncond_ok hneg⟩,
            hs₈_ob, ?_⟩
          rw [outputList_eq_iff]
          have hans : answerWords G = [] := by
            dsimp only [answerWords, solveFin, solve, extractAssignment]
            have hfold_eq :
                (List.finRange G.n).foldl
                  (fun ok v => ok && decide (compIdx (v, true) ≠ compIdx (v, false))) true =
                ok_all := rfl
            rw [hchk, hfold_eq, hok_all]
            rfl
          rw [hans]
          exact ⟨Data.write_mem_self _ _ _, Block.holdsList_nil _ _⟩
        · have hs₈_ok1 : s₈.regs compIdxReg = 1 := by rw [hs₈_ok, hok_all]; rfl
          have hcond_ok : (Cond.eq compIdxReg cOne).Holds s₈ := by
            change s₈.regs compIdxReg = s₈.regs cOne; omega
          have hf_n1 : Fits w (G.n + 1) :=
            G.fits_of_le hfit (by unfold Instance.wordBound; omega)
          have hf_ob1 : Fits w (G.outAddrBase + 1) :=
            G.fits_of_le hfit (by
              simp only [Instance.outAddrBase, G.encode_length, Instance.wordBound]; omega)
          let y_sat := (((s₈.set addr (G.n + 1)).write G.outAddrBase (G.n + 1)).set
            addr (G.outAddrBase + 1)).write (G.outAddrBase + 1) 1
          have hpos_sat : ExecWithin w
              (ram[ addr ← nv + cOne; *outBase ← addr; addr ← outBase + cOne; *addr ← cOne ])
              s₈ y_sat 4 := by
            have htriv : y_sat = (((s₈.set addr (G.n + 1)).write G.outAddrBase (G.n + 1)).set
              addr (G.outAddrBase + 1)).write (G.outAddrBase + 1) 1 := rfl
            wram_exec [hs₈_nv, hs₈_1, hs₈_ob, hf_n1, hf_ob1]
          obtain ⟨ts, hts, hes⟩ := hpos_sat
          have hdist_all : ∀ v : Fin G.n, compIdx (v, true) ≠ compIdx (v, false) := by
            have hall : (List.finRange G.n).foldl
                (fun acc v => acc && decide (compIdx (v, true) ≠ compIdx (v, false))) true =
                  true := hok_all
            rw [foldl_and_eq_and_all, Bool.true_and, List.all_eq_true] at hall
            exact fun v => of_decide_eq_true (hall v (List.mem_finRange v))
          refine ⟨y_sat, ⟨ts + 1, by omega, Exec.branch_pos hcond_ok hes⟩,
            by dsimp only [y_sat]; wram_simp; exact hs₈_ob, ?_⟩
          rw [outputList_eq_iff]
          have hans : answerWords G =
              1 :: (List.finRange G.n).map
                (fun v => (decide (compIdx (v, false) < compIdx (v, true))).toNat) := by
            dsimp only [answerWords, solveFin, solve, extractAssignment, encodeAssignment]
            have hfold_eq :
                (List.finRange G.n).foldl
                  (fun ok v => ok && decide (compIdx (v, true) ≠ compIdx (v, false))) true =
                ok_all := rfl
            rw [hchk, hfold_eq, hok_all]
            rfl
          rw [hans]
          refine ⟨?_, fun i => ?_⟩
          · dsimp only [y_sat]
            rw [Data.write_mem_of_ne (by omega), Data.set_mem, Data.write_mem_self]
            simp
          · dsimp only [Block.read, y_sat]
            cases hi_eq : i.val with
            | zero =>
              rw [Nat.add_zero, Data.write_mem_self]
              simp [hi_eq]
            | succ q =>
              have hq_lt : q < G.n := by have := i.isLt; simp at this; omega
              rw [show G.outAddrBase + 1 + (q + 1) = G.outAddrBase + 2 + q by omega,
                Data.write_mem_of_ne (by omega), Data.set_mem,
                Data.write_mem_of_ne (by omega), Data.set_mem,
                hs₈_bits ⟨q, hq_lt⟩ (hdist_all ⟨q, hq_lt⟩)]
              simp [hi_eq]
      obtain ⟨y, hy_br, hy_ob, hy_list⟩ := hfin_ext
      have hext_ex : ExecWithin w extractAssignmentCode s₇ y (16 * G.n + 9) :=
        (hp_ext.seq (hs₈_ex.seq hy_br)).mono (by omega)
      have hfull_pos : ExecWithin w
          (setupWorkRegsCode.seq
            (buildImplCSRCode.seq
              (forwardDFSCode.seq
                (transposeCSRCode.seq
                  ((ram[ finB ← ordB + nVerts ]).seq
                    (kosarajuIndexCode.seq
                      extractAssignmentCode))))))
          s₂ y (498 * G.n + 245 * G.φ.length + 88) :=
        (hs₃_ex.seq (hs₄_ex.seq (hs₅_ex.seq (hs₆_ex.seq (hp_finB.seq (hs₇_ex.seq hext_ex)))))).mono
          (by dsimp only [N, Mc] at *; omega)
      obtain ⟨tf, htf, hef⟩ := hfull_pos
      have hbr_inner : Exec w
          (.branch (.eq nv cZero)
            (ram[ *outBase ← cOne; addr ← outBase + cOne; *addr ← cOne ])
            (setupWorkRegsCode.seq
              (buildImplCSRCode.seq
                (forwardDFSCode.seq
                  (transposeCSRCode.seq
                    ((ram[ finB ← ordB + nVerts ]).seq
                      (kosarajuIndexCode.seq
                        extractAssignmentCode)))))))
          s₂ y (tf + 2) :=
        Exec.branch_neg hncond_n0 hef
      have hbr_outer : ExecWithin w
          (.branch (.eq compIdxReg cOne)
            (.branch (.eq nv cZero)
              (ram[ *outBase ← cOne; addr ← outBase + cOne; *addr ← cOne ])
              (setupWorkRegsCode.seq
                (buildImplCSRCode.seq
                  (forwardDFSCode.seq
                    (transposeCSRCode.seq
                      ((ram[ finB ← ordB + nVerts ]).seq
                        (kosarajuIndexCode.seq
                           extractAssignmentCode)))))))
            (ram[ *outBase ← cZero ]))
          s₂ y (498 * G.n + 245 * G.φ.length + 91) :=
        ⟨tf + 3, by omega, Exec.branch_pos hcond_chk hbr_inner⟩
      exact ⟨y, (hsetup.seq (hchk_ex.seq hbr_outer)).mono (by omega), hy_ob,
        by rwa [hy_ob]⟩

/-- **Linear-time 2-SAT on the word RAM (`O(n + |φ|)`).** At every word width `w` with
`Fits w G.wordBound`, `program` halts within `512 * (G.n + G.φ.length + 1)` instructions and
outputs `answerWords G`: `[]` if `G.φ` is either not a 2-CNF or unsatisfiable, and
`1 :: [(σ 0).toNat, …, (σ (n - 1)).toNat]` for the canonical satisfying assignment `σ`
otherwise. -/
theorem program_spec (G : Instance) {w : ℕ} (hfit : Fits w G.wordBound) :
    ∃ steps ≤ 512 * (G.n + G.φ.length + 1),
      ExecutesList w program (State.init G.encode) (answerWords G) steps := by
  obtain ⟨y, ⟨steps, hsteps, hexec⟩, hyout, hylist⟩ := solver_spec G hfit
  have hlen := length_answerWords_le G
  have hfit_out : Fits w (y.regs outBase + (outputList y.mem (y.regs outBase)).length) := by
    rw [hylist, hyout]
    exact G.fits_of_le hfit
      (by simp only [Instance.outAddrBase, G.encode_length, Instance.wordBound]; omega)
  refine ⟨steps + 1, by omega, ?_⟩
  have hex := hexec.executesList outBase hfit_out
  rwa [hylist] at hex

/-- Fixed-program `Program.ComputesListInTime` certificate for Word-RAM 2-SAT. -/
theorem computesListInTime_program :
    program.ComputesListInTime (fun _ G => G.encode)
      (fun G _ => 512 * (G.n + G.φ.length + 1))
      (fun G w => Fits w G.wordBound)
      answerWords := by
  intro G w hfit _
  obtain ⟨steps, hle, hex⟩ := program_spec G hfit
  exact ⟨steps, hex, hle⟩

/-- `program` does not read the word width (`width%`). -/
theorem not_readsWidth_program : ¬ program.ReadsWidth := by
  apply Code.not_readsWidth_program
  decide +kernel

/-- `program` is deterministic (`rand`-free). -/
theorem isRandFree_program : program.IsRandFree := by
  rw [program, Code.isRandFree_program]
  decide +kernel

end Cslib.Algorithms.WordRAM.TwoSAT

