/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.MaxFlow.EdmondsKarp
public import CslibFrontier.Algorithms.WordRAM.EdmondsKarp.Core
public import CslibFrontier.Algorithms.WordRAM.Karger.Contract
-- `import all`: reads `private theorem ekProg_flow_spec` without exporting it from `EdmondsKarp`.
import all CslibFrontier.Algorithms.WordRAM.EdmondsKarp.Spec
import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
import CslibFrontier.Foundations.Data.List.RowMajor
import CslibFrontier.Tactic.Realize
import Mathlib.Tactic.Linarith

/-!
# Uniform Word-RAM program for dense Edmonds–Karp maximum flow and minimum cut

Uniform `Basis.exact` flat program and `O((n + 1) ^ 5)` runtime bound for dense maximum flow and
minimum `s`–`t` cut (`exists_edmondsKarp_program`).

## Main definitions

* `Cslib.Algorithms.WordRAM.EdmondsKarp.encodeFlowInput`, `ekFlowAddr`, `ekCutAddr`,
  `ekWorkspace`: input encoding, output flow and cut addresses, and workspace frontier.

## Main results

* `Cslib.Algorithms.WordRAM.EdmondsKarp.exists_edmondsKarp_program`: uniform `O((n + 1) ^ 5)`
  Word-RAM maximum flow and minimum cut program.

## References

* [EdmondsKarp1972]
* [CLRS2009]
-/

public section

namespace Cslib.Algorithms.WordRAM.EdmondsKarp

open Cslib.Algorithms.Lean.MaxFlow Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.Algorithms.WordRAM.Karger
open StateTransitionSpec (clientResult_bind clientState_bind clientResult_pure clientState_pure)

/-! ### Uniform dense Edmonds–Karp flat program -/

section UniformEK

/-- Word-RAM input `n :: s :: t :: flattenMatrix N.cap`: vertex count at address `1`, source at `2`,
sink at `3`, and row-major capacity matrix `N.cap u v` at `4 + u * n + v`. -/
@[expose] def encodeFlowInput {n : ℕ} (N : Network (Fin n)) : List ℕ :=
  n :: N.s.1 :: N.t.1 :: flattenMatrix N.cap

/-- Output address of the final flow value `f u v` left by `exists_edmondsKarp_program`. -/
@[expose] def ekFlowAddr (n u v : ℕ) : ℕ := 4 + n * n + u * n + v

/-- Output address of the final residual distance of `x` (`< n` iff `x` lies in the minimum cut)
left by `exists_edmondsKarp_program`. -/
@[expose] def ekCutAddr (n x : ℕ) : ℕ := 4 + n * n + n * n + x

/-- Memory frontier required by `exists_edmondsKarp_program`: `4 + 2 * n^2 + 2 * n`. -/
@[expose] def ekWorkspace (n : ℕ) : ℕ := 4 + 2 * (n * n) + 2 * n

private def ekMaxStep (d : ℕ × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let x ← Memory.read (d.1 + d.2.1)
  if d.2.2 < x then pure (d.2.1 + 1, x) else pure (d.2.1 + 1, d.2.2)

private def ekFullMain (d : ℕ × ℕ × ℕ) : Memory.Prog ℕ := do
  let n := d.1
  let s := d.2.1
  let t := d.2.2
  let _ ← Memory.alloc (ekScratch n)
  if s < n ∧ t < n then
    let m ← iterate ekMaxStep 4 (n * n) (0, 0)
    ekProg (⟨n, 4, 4 + n * n, m.2⟩, (s, t))
  else
    pure 0

private def ekFullProg (_ : Unit) : Memory.Prog ℕ := do
  let n ← Memory.read 1
  let s ← Memory.read 2
  let t ← Memory.read 3
  ekFullMain (n, s, t)

private theorem ekMaxStep_realizes :
    Realizes .exact ekMaxStep (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w d _ => Fits w (d.1 + d.2.1) ∧ Fits w (d.2.1 + 1)) (fun _ _ => 0) := by
  unfold ekMaxStep
  realize
  · exact h.1
  · exact h.2
  · exact h.2

private theorem ekMaxScan_spec {base len B : ℕ} {st : Memory.State}
    (hB : ∀ i < len, st.mem (base + i) ≤ B) :
    let r := (Memory.spec 0).clientResult st (iterate ekMaxStep base len (0, 0))
    r.2 ≤ B ∧ ∀ i < len, st.mem (base + i) ≤ r.2 := by
  have hst : ∀ a t, (Memory.spec 0).clientState t (ekMaxStep (base, a)) = t := fun a t => by
    unfold ekMaxStep
    rw [clientState_bind_read]
    split_ifs <;> rfl
  have hinv := iterate_invariant_of ekMaxStep base
    (fun rem (p : ℕ × ℕ) t => t = st ∧ p.1 + rem = len ∧ p.2 ≤ B ∧
      ∀ i < p.1, st.mem (base + i) ≤ p.2)
    (fun rem p t ⟨ht, hsum, hle, hall⟩ => by
      subst ht
      refine ⟨hst p t, ?_⟩
      unfold ekMaxStep
      rw [clientResult_bind_read]
      dsimp only
      split_ifs with hlt
      · rw [clientResult_pure]
        dsimp only
        refine ⟨by omega, hB p.1 (by omega), fun i hi => ?_⟩
        by_cases hip : i = p.1
        · subst hip; exact le_rfl
        · exact (hall i (by omega)).trans (Nat.le_of_lt hlt)
      · rw [clientResult_pure]
        dsimp only
        refine ⟨by omega, hle, fun i hi => ?_⟩
        by_cases hip : i = p.1
        · subst hip; omega
        · exact hall i (by omega))
    (n := len) (a := (0, 0)) (s := st)
    ⟨rfl, Nat.zero_add _, Nat.zero_le _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  exact ⟨hinv.2.2.1, fun i hi => hinv.2.2.2 i (by omega)⟩

private theorem ekMaxScan_state (base len : ℕ) (st : Memory.State) :
    (Memory.spec 0).clientState st (iterate ekMaxStep base len (0, 0)) = st :=
  clientState_iterate_eq_of ekMaxStep base (fun _ t => by
    unfold ekMaxStep
    rw [clientState_bind_read]
    split_ifs <;> rfl) len (0, 0) st

private theorem clientResult_ekMaxStep_fst (d : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).clientResult s (ekMaxStep d)).1 = d.2.1 + 1 := by
  unfold ekMaxStep
  rw [clientResult_bind_read]
  split_ifs <;> rfl

private theorem ekFullMain_realizes :
    Realizes .exact ekFullMain (WordEncoding.encode (α := ℕ × ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d st => st.frontier = 4 + d.1 * d.1 ∧ Fits w (ekWorkspace d.1) ∧
        ∃ B, (∀ i < d.1 * d.1, st.mem (4 + i) ≤ B) ∧ Fits w (ekBound d.1 B))
      (fun _ _ => 0) := by
  unfold ekFullMain
  realize [ekMaxStep_realizes, ekProg_realizes]
  all_goals
    obtain ⟨hfr, hw, B, hB, hwB⟩ := h
    dsimp -failIfUnchanged only [CtxFits, ekScratch, ekWorkspace] at *
    try assumption
    try (apply hw.of_le; omega)
  · refine iterationSafe_of_stepInv _ _ w _
      (fun rem (p : ℕ × ℕ) _ => p.1 + rem = d.1 * d.1) ?_ (Nat.zero_add _)
    intro rem p t hsum
    dsimp only at hsum ⊢
    refine ⟨⟨hw.of_le (by omega), hw.of_le (by omega), hw.of_le (by omega)⟩, ?_⟩
    rw [clientResult_ekMaxStep_fst]
    dsimp only
    omega
  · have hal : ∀ i < d.1 * d.1,
        ((Memory.spec 0).clientState s (Memory.alloc (ekScratch d.1))).mem (4 + i) ≤ B :=
      fun i hi => (Memory.mem_step_of_lt_frontier s (.alloc (ekScratch d.1))
        (by rw [hfr]; omega) (by simp)).trans_le (hB i hi)
    have hM := (ekMaxScan_spec hal).1
    refine ⟨by omega, hw.of_le (by omega), hwB.of_le (by unfold ekBound; gcongr <;> exact hM)⟩

private theorem ekFullProg_realizes :
    Realizes .exact ekFullProg (WordEncoding.encode (α := Unit)) (WordEncoding.encode (α := ℕ))
      (fun w _ st => st.frontier = 4 + st.mem 1 * st.mem 1 ∧ Fits w (ekWorkspace (st.mem 1)) ∧
        ∃ B, (∀ i < st.mem 1 * st.mem 1, st.mem (4 + i) ≤ B) ∧ Fits w (ekBound (st.mem 1) B))
      (fun _ _ => 0) := by
  unfold ekFullProg
  realize [ekFullMain_realizes]
  all_goals
    obtain ⟨hfr, hw, B, hB, hwB⟩ := h
    first
    | exact hw.of_le (by dsimp only [ekWorkspace]; omega)
    | exact hfr
    | exact ⟨B, hB, hwB⟩

private theorem memoryCost_ekFullProg_le (s : Memory.State) :
    memoryCost (ekFullProg ()) s ≤ 25 * (s.mem 1 + 1) ^ 5 := by
  unfold ekFullProg
  rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
    memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
    memoryCost_bind', memoryCost_read, clientResult_read, clientState_read]
  unfold ekFullMain
  dsimp only
  set n := s.mem 1
  have hstep : ∀ (p : ℕ × ℕ) t, memoryCost (ekMaxStep (4, p)) t ≤ 1 := fun p t => by
    unfold ekMaxStep
    exact memoryCost_read_bind_le fun _ _ => memoryCost_ite_le (by simp) (by simp)
  have hmain : memoryCost (do
      let _ ← Memory.alloc (ekScratch n)
      if s.mem 2 < n ∧ s.mem 3 < n then
        let m ← iterate ekMaxStep 4 (n * n) (0, 0)
        ekProg (⟨n, 4, 4 + n * n, m.2⟩, (s.mem 2, s.mem 3))
      else pure 0) s ≤ (ekScratch n + 1) + (n * n + ekCost n) := by
    refine memoryCost_bind_le (memoryCost_alloc _ _).le fun _ t => ?_
    refine memoryCost_ite_le ?_ (by simp)
    exact memoryCost_bind_le
      (by simpa [Nat.one_mul] using memoryCost_iterate_le_of ekMaxStep 1 4 hstep (n * n) (0, 0) t)
      fun m t' => memoryCost_ekProg_le ⟨n, 4, 4 + n * n, m.2⟩ (s.mem 2) (s.mem 3) t'
  have h1 : (n + 1) ^ 2 ≤ (n + 1) ^ 5 := Nat.pow_le_pow_right (Nat.succ_pos n) (by decide)
  have h2 : 1 ≤ (n + 1) ^ 5 := Nat.one_le_pow _ _ (Nat.succ_pos n)
  dsimp only [ekScratch, ekCost] at hmain
  nlinarith

private theorem flowInit_mem_matrix {n : ℕ} (N : Network (Fin n)) {i : ℕ} (hi : i < n * n) :
    (Memory.State.init (encodeFlowInput N)).mem (4 + i) =
      (flattenMatrix N.cap)[i]'(by rw [length_flattenMatrix]; exact hi) := by
  change (if 4 + i = 0 then (encodeFlowInput N).length
    else (encodeFlowInput N).getD (4 + i - 1) 0) = _
  rw [ite_eq_right (by omega), show 4 + i - 1 = i + 3 by omega]
  change (flattenMatrix N.cap).getD i 0 = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some]

private theorem flowInit_mat_eq {n : ℕ} (N : Network (Fin n)) (u v : Fin n) :
    (Memory.State.init (encodeFlowInput N)).mem (4 + u.1 * n + v.1) = N.cap u v := by
  have hlt := List.mul_add_lt_sq u.2 v.2
  rw [Nat.add_assoc, flowInit_mem_matrix N hlt, getElem_flattenMatrix]

private theorem flowInit_le {n B : ℕ} {N : Network (Fin n)} (hB : ∀ u v, N.cap u v ≤ B)
    {i : ℕ} (hi : i < n * n) : (Memory.State.init (encodeFlowInput N)).mem (4 + i) ≤ B := by
  have hn : 0 < n := Nat.pos_of_ne_zero fun h => by simp [h] at hi
  have hu : i / n < n := Nat.div_lt_of_lt_mul hi
  have hv : i % n < n := Nat.mod_lt i hn
  have hidx : 4 + i = 4 + (⟨i / n, hu⟩ : Fin n).1 * n + (⟨i % n, hv⟩ : Fin n).1 := by
    dsimp only
    rw [Nat.add_assoc, Nat.div_add_mod']
  rw [hidx, flowInit_mat_eq N]
  exact hB _ _

private theorem inputFits_encodeFlowInput {n B w : ℕ} (N : Network (Fin n))
    (hB : ∀ u v, N.cap u v ≤ B) (hw : Fits w (ekWorkspace n)) (hwB : Fits w (ekBound n B)) :
    InputFits w (encodeFlowInput N) := by
  have hBw : Fits w B := hwB.of_le (by dsimp only [ekBound]; omega)
  refine ⟨hw.of_le ?_, fun x hx => ?_⟩
  · simp only [encodeFlowInput, List.length_cons, length_flattenMatrix, ekWorkspace]
    omega
  · simp only [encodeFlowInput, List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | hx
    · exact hw.of_le (by dsimp only [ekWorkspace]; omega)
    · exact hw.of_le (by have := N.s.2; dsimp only [ekWorkspace]; omega)
    · exact hw.of_le (by have := N.t.2; dsimp only [ekWorkspace]; omega)
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      rw [length_flattenMatrix] at hi
      rw [← flowInit_mem_matrix N hi]
      exact hBw.of_le (flowInit_le hB hi)

private theorem validHistory_ekFullProg {n B w : ℕ} (N : Network (Fin n))
    (hB : ∀ u v, N.cap u v ≤ B) (hw : Fits w (ekWorkspace n)) (hwB : Fits w (ekBound n B)) :
    (Memory.spec w).ValidHistory (Memory.State.init (encodeFlowInput N))
      ((Memory.spec w).clientHistory (Memory.State.init (encodeFlowInput N)) (ekFullProg ())) := by
  set st := Memory.State.init (encodeFlowInput N)
  have hfr : st.frontier = 4 + n * n := by
    simp only [st, Memory.State.init, encodeFlowInput, List.length_cons, length_flattenMatrix]
    omega
  have hwf : Memory.WellFormed w st :=
    Memory.wellFormed_init (inputFits_encodeFlowInput N hB hw hwB)
      (hw.of_le (by simp only [encodeFlowInput, List.length_cons, length_flattenMatrix,
        ekWorkspace]; omega))
  have h1 : st.mem 1 = n := by simp [st, Memory.State.init, encodeFlowInput]
  have h2 : st.mem 2 = N.s.1 := by simp [st, Memory.State.init, encodeFlowInput]
  have h3 : st.mem 3 = N.t.1 := by simp [st, Memory.State.init, encodeFlowInput]
  unfold ekFullProg
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_read_bind (by omega) ?_
  rw [h1, h2, h3]
  unfold ekFullMain
  dsimp only
  have halloc : (Memory.spec w).ValidHistory st
      ((Memory.spec w).clientHistory st (Memory.alloc (ekScratch n))) :=
    validHistory_alloc (by rw [hfr]; exact hw.of_le (by dsimp only [ekScratch, ekWorkspace]; omega))
  refine validHistory_bind_step halloc ?_
  set st1 := (Memory.spec 0).clientState st (Memory.alloc (ekScratch n))
  have hwf1 : Memory.WellFormed w st1 := wellFormed_clientState hwf halloc
  have hfr1 : ekWorkspace n ≤ st1.frontier := by
    change ekWorkspace n ≤ st.frontier + ekScratch n
    rw [hfr]; dsimp only [ekScratch, ekWorkspace]; omega
  refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
  have hmx : (Memory.spec w).ValidHistory st1
      ((Memory.spec w).clientHistory st1 (iterate ekMaxStep 4 (n * n) (0, 0))) := by
    refine validHistory_iterate_fst (Inv := fun t => Memory.WellFormed w t ∧
        ekWorkspace n ≤ t.frontier) (n * n) 0 0 (fun i hi b t ht => ⟨?_, ?_⟩) ⟨hwf1, hfr1⟩
    · unfold ekMaxStep
      refine validHistory_read_bind (by have := ht.2; dsimp only [ekWorkspace] at this ⊢; omega) ?_
      exact validHistory_ite (fun _ => validHistory_pure _ _ _) (fun _ => validHistory_pure _ _ _)
    · exact clientResult_ekMaxStep_fst _ t
  refine validHistory_bind_step hmx ?_
  rw [ekMaxScan_state]
  have hal : ∀ i < n * n, st1.mem (4 + i) ≤ B := fun i hi =>
    (Memory.mem_step_of_lt_frontier st (.alloc (ekScratch n)) (by rw [hfr]; omega)
      (by simp)).trans_le (flowInit_le hB hi)
  have hM := (ekMaxScan_spec hal).1
  exact validHistory_ekProg
    (c := ⟨n, 4, 4 + n * n,
      ((Memory.spec 0).clientResult st1 (iterate ekMaxStep 4 (n * n) (0, 0))).2⟩)
    ⟨by dsimp only; omega,
      hw.of_le (by dsimp only [ekScratch, ekWorkspace]; omega),
      hwB.of_le (by dsimp only [ekBound]; gcongr)⟩
    N.s.2 N.t.2 hwf1
    (by dsimp only [ekScratch, ekWorkspace] at hfr1 ⊢; omega)

/-- **Dense Edmonds–Karp on the Word-RAM** ([EdmondsKarp1972], Theorem 1; [CLRS2009],
Theorem 26.8): one uniform flat program over `Basis.exact` that, on `encodeFlowInput N` for any
network `N : Network (Fin n)` with `N.s ≠ N.t` and capacities at most `B`, halts within
`C * (n + 1) ^ 5` instructions at every word width fitting `ekWorkspace n` and `ekBound n B`.
This formalizes the dense `O((n + 1) ^ 5)` adjacency-matrix variant rather than the sparse
`O(|V| |E| ^ 2)` adjacency-list bound of [CLRS2009], Theorem 26.8. It returns the maximum flow
value `N.cutCapacity C_cut`, stores a maximum flow `f` at `ekFlowAddr`, and marks the minimum cut
`C_cut = f.reachableCut` at `ekCutAddr < n`. -/
theorem exists_edmondsKarp_program :
    ∃ (R C pc : ℕ), 0 < C ∧ ∃ prog : Program .exact R,
      ∀ {n : ℕ} (N : Network (Fin n)) (B w : ℕ), N.s ≠ N.t →
        (∀ u v, N.cap u v ≤ B) → Fits w (ekWorkspace n) → Fits w (ekBound n B) →
        ∃ (y : Data R) (steps res : ℕ) (f : N.Flow),
          let C_cut : Finset (Fin n) := Finset.univ.filter fun x => y.mem (ekCutAddr n x.1) < n
          Runs w prog (State.init (encodeFlowInput N)) ⟨pc, y⟩ steps ∧
          step w prog ⟨pc, y⟩ = .halt res ∧
          steps + 1 ≤ C * (n + 1) ^ 5 ∧
          (∀ u v : Fin n, y.mem (ekFlowAddr n u.1 v.1) = f u v) ∧
          f.IsMaxFlow ∧ N.IsMinCut C_cut ∧ C_cut = f.reachableCut ∧
          f.value = (N.cutCapacity C_cut : ℤ) ∧ res = N.cutCapacity C_cut := by
  obtain ⟨R, C₀, pc, prog, _, _, hprog⟩ :=
    ekFullProg_realizes.exists_standard_init_program_state_from_words 0
  refine ⟨R, 26 * C₀ + 2, pc, by omega, prog, ?_⟩
  intro n N B w hst hB hw hwB
  set st := Memory.State.init (encodeFlowInput N)
  have hfr : st.frontier = 4 + n * n := by
    simp only [st, Memory.State.init, encodeFlowInput, List.length_cons, length_flattenMatrix]
    omega
  have h1 : st.mem 1 = n := by simp [st, Memory.State.init, encodeFlowInput]
  have h2 : st.mem 2 = N.s.1 := by simp [st, Memory.State.init, encodeFlowInput]
  have h3 : st.mem 3 = N.t.1 := by simp [st, Memory.State.init, encodeFlowInput]
  have hlen : Fits w ((encodeFlowInput N).length + 1) := hw.of_le (by
    simp only [encodeFlowInput, List.length_cons, length_flattenMatrix, ekWorkspace]; omega)
  obtain ⟨y, steps, hruns, hhalt, hmem, _, hbound⟩ :=
    hprog w () (encodeFlowInput N) (fun j => Fin.elim0 j) (Nat.zero_le _) hlen
      (inputFits_encodeFlowInput N hB hw hwB)
      ⟨by rw [h1]; exact hfr, by rw [h1]; exact hw, B,
        by rw [h1]; exact fun i hi => flowInit_le hB hi, by rw [h1]; exact hwB⟩
      (validHistory_ekFullProg N hB hw hwB)
  rw [clientState_width w (ekFullProg ())] at hmem
  rw [clientResult_width w (ekFullProg ())] at hhalt
  set st1 := (Memory.spec 0).clientState st (Memory.alloc (ekScratch n))
  have hmat1 : ∀ u v : Fin n, st1.mem (4 + u.1 * n + v.1) = N.cap u v := fun u v => by
    have hidx := List.mul_add_lt_sq u.2 v.2
    exact (Memory.mem_step_of_lt_frontier st (.alloc (ekScratch n)) (by rw [hfr]; omega)
      (by simp)).trans (flowInit_mat_eq N u v)
  have hal : ∀ i < n * n, st1.mem (4 + i) ≤ B := fun i hi =>
    (Memory.mem_step_of_lt_frontier st (.alloc (ekScratch n)) (by rw [hfr]; omega)
      (by simp)).trans_le (flowInit_le hB hi)
  set M := ((Memory.spec 0).clientResult st1 (iterate ekMaxStep 4 (n * n) (0, 0))).2
  have hM_ge : ∀ u v : Fin n, N.cap u v ≤ M := fun u v => by
    have h := (ekMaxScan_spec hal).2 (u.1 * n + v.1) (List.mul_add_lt_sq u.2 v.2)
    rw [show 4 + (u.1 * n + v.1) = 4 + u.1 * n + v.1 by omega, hmat1 u v] at h
    exact h
  have hst_ek : (Memory.spec 0).clientState st (ekFullProg ()) =
      (Memory.spec 0).clientState st1 (ekProg (⟨n, 4, 4 + n * n, M⟩, (N.s.1, N.t.1))) := by
    unfold ekFullProg
    rw [clientState_bind_read, clientState_bind_read, clientState_bind_read, h1, h2, h3]
    unfold ekFullMain
    dsimp only
    rw [clientState_bind, ite_eq_left ⟨N.s.2, N.t.2⟩, clientState_bind, ekMaxScan_state]
  have hres_ek : (Memory.spec 0).clientResult st (ekFullProg ()) =
      (Memory.spec 0).clientResult st1 (ekProg (⟨n, 4, 4 + n * n, M⟩, (N.s.1, N.t.1))) := by
    unfold ekFullProg
    rw [clientResult_bind_read, clientResult_bind_read, clientResult_bind_read, h1, h2, h3]
    unfold ekFullMain
    dsimp only
    rw [clientResult_bind, ite_eq_left ⟨N.s.2, N.t.2⟩, clientResult_bind, ekMaxScan_state]
  obtain ⟨_, f, hflow, _, hmax, hmin, hC_eq, hval, hres⟩ :=
    ekProg_flow_spec N hst hM_ge (le_refl (4 + n * n)) hmat1
  have hymem : y.mem =
      ((Memory.spec 0).clientState st1 (ekProg (⟨n, 4, 4 + n * n, M⟩, (N.s.1, N.t.1)))).mem := by
    rw [← hst_ek]
    exact congrArg Memory.State.mem hmem
  have hmc : memoryCost (ekFullProg ()) st ≤ 25 * (n + 1) ^ 5 := by
    have := memoryCost_ekFullProg_le st
    rwa [h1] at this
  have hp : 1 ≤ (n + 1) ^ 5 := Nat.one_le_pow _ _ (Nat.succ_pos n)
  refine ⟨y, steps, (Memory.spec 0).clientResult st (ekFullProg ()), f, hruns, hhalt, ?_,
    ?_, hmax, ?_, ?_, ?_, ?_⟩
  · calc steps + 1
        ≤ C₀ * (memoryCost (ekFullProg ()) st + 0 + 1) + 1 := hbound
      _ ≤ C₀ * (25 * (n + 1) ^ 5 + 1) + 1 :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 1
      _ ≤ (26 * C₀ + 2) * (n + 1) ^ 5 := by nlinarith
  · intro u v
    rw [hymem]
    exact hflow u v
  · simpa only [hymem, ekCutAddr, distAddr] using hmin
  · simpa only [hymem, ekCutAddr, distAddr] using hC_eq
  · simpa only [hymem, ekCutAddr, distAddr] using hval
  · rw [hres_ek]
    simpa only [hymem, ekCutAddr, distAddr] using hres

end UniformEK

end Cslib.Algorithms.WordRAM.EdmondsKarp
