/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.TwoSAT
public import CslibFrontier.Algorithms.WordRAM.ClauseCode
public import CslibFrontier.Algorithms.WordRAM.DFS
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

The implication graph is built in compressed sparse row form in the scratch layout of
`CslibFrontier.Algorithms.WordRAM.DFS`, whose `sccIndexCode` computes the topological component
index of every literal (forward iterative DFS, CSR transposition, and Kosaraju peeling).

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

private abbrev cTwo : Fin 28 := ⟨2, by decide⟩
private abbrev nv : Fin 28 := ⟨4, by decide⟩
private abbrev mClauses : Fin 28 := ⟨5, by decide⟩
/-- Output-list header register (`G.outAddrBase`). -/
abbrev outBase : Fin 28 := ⟨7, by decide⟩

end Reg

open Reg Cslib.Algorithms.WordRAM.DFS Cslib.Algorithms.WordRAM.DFS.Reg

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
              (sccIndexCode.seq extractAssignmentCode))))
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
                (sccIndexCode.seq extractAssignmentCode))))
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
                (sccIndexCode.seq extractAssignmentCode))))
          s₂ y_n0 (tn0 + 1) :=
        Exec.branch_pos hcond_n0 hen0
      have hbr_outer : ExecWithin w
          (.branch (.eq compIdxReg cOne)
            (.branch (.eq nv cZero)
              (ram[ *outBase ← cOne; addr ← outBase + cOne; *addr ← cOne ])
              (setupWorkRegsCode.seq
                (buildImplCSRCode.seq
                  (sccIndexCode.seq extractAssignmentCode))))
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
      obtain ⟨s₇, hs₇_ex, hs₇_comp, -, hs₇_fr⟩ :=
        sccIndexCode_spec hN_pos G.adjFin wb Mc hmc_adj hfit_top hs₄_dregs
          ((hs₄_fr nVerts (by decide)).trans hs₃_Nv)
          ((hs₄_fr curB (by decide)).trans hs₃_cur)
          ((hs₄_fr revOffB (by decide)).trans hs₃_roff)
          ((hs₄_fr revEdgeB (by decide)).trans hs₃_redge)
          ((hs₄_fr ordB (by decide)).trans hs₃_ord)
          ((hs₄_fr compB (by decide)).trans hs₃_comp)
          hs₄_csr
      have hs₇_fr3 : ∀ r : Fin 28, r.val < 18 → r ≠ offB → r ≠ edgeB → r ≠ finB →
          s₇.regs r = s₃.regs r := fun r hr h1 h2 h3 =>
        (hs₇_fr r hr h1 h2 h3).trans (hs₄_fr r hr)
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
              (sccIndexCode.seq extractAssignmentCode)))
          s₂ y (498 * G.n + 245 * G.φ.length + 88) :=
        (hs₃_ex.seq (hs₄_ex.seq (hs₇_ex.seq hext_ex))).mono
          (by dsimp only [N, Mc] at *; omega)
      obtain ⟨tf, htf, hef⟩ := hfull_pos
      have hbr_inner : Exec w
          (.branch (.eq nv cZero)
            (ram[ *outBase ← cOne; addr ← outBase + cOne; *addr ← cOne ])
            (setupWorkRegsCode.seq
              (buildImplCSRCode.seq
                (sccIndexCode.seq extractAssignmentCode))))
          s₂ y (tf + 2) :=
        Exec.branch_neg hncond_n0 hef
      have hbr_outer : ExecWithin w
          (.branch (.eq compIdxReg cOne)
            (.branch (.eq nv cZero)
              (ram[ *outBase ← cOne; addr ← outBase + cOne; *addr ← cOne ])
              (setupWorkRegsCode.seq
                (buildImplCSRCode.seq
                  (sccIndexCode.seq extractAssignmentCode))))
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
  simp [solver, headerSetupCode, checkClausesCode, checkClauseBody, setupWorkRegsCode,
    buildImplCSRCode, implDegBody, implFillBody, extractAssignmentCode, extractVarBody,
    Code.ReadsWidth, Op.ReadsWidth, Op.bin,
    not_readsWidth_zeroBlockCode, not_readsWidth_incCurCode, not_readsWidth_prefixSumCode,
    not_readsWidth_backfillStepCode, not_readsWidth_sccIndexCode]

/-- `program` is deterministic (`rand`-free). -/
theorem isRandFree_program : program.IsRandFree := by
  rw [program, Code.isRandFree_program]
  simp only [solver, headerSetupCode, checkClausesCode, checkClauseBody, setupWorkRegsCode,
    buildImplCSRCode, implDegBody, implFillBody, extractAssignmentCode, extractVarBody,
    Code.IsRandFree,
    isRandFree_zeroBlockCode, isRandFree_incCurCode, isRandFree_prefixSumCode,
    isRandFree_backfillStepCode, isRandFree_sccIndexCode, and_self]

end Cslib.Algorithms.WordRAM.TwoSAT

