/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.MaxFlow.BipartiteMatching
public import CslibFrontier.Algorithms.WordRAM.EdmondsKarp.Core
import CslibFrontier.Algorithms.WordRAM.EdmondsKarp.Internal
-- `import all`: reads `private theorem ekProg_flow_spec` without exporting it from `EdmondsKarp`.
import all CslibFrontier.Algorithms.WordRAM.EdmondsKarp.Spec
import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
import CslibFrontier.Foundations.Data.List.RowMajor
import CslibFrontier.Tactic.Realize
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Uniform Word-RAM programs for bipartite matching and König vertex cover

Uniform `Basis.exact` flat programs and `O((m + r + 1) ^ 5)` / `O((n + 1) ^ 5)` runtime bounds for
maximum bipartite matching with König minimum vertex cover (`exists_bipartiteMatching_program`) and
perfect matching decision (`exists_perfectMatching_program`) by reduction to `ekProg`.

## Main definitions

* `Cslib.Algorithms.WordRAM.EdmondsKarp.encodeBipartiteMatrix`, `encodeBipartiteInput`,
  `bmMatchAddr`, `bmCovLAddr`, `bmCovRAddr`: input encoding and output matching/cover addresses.

## Main results

* `Cslib.Algorithms.WordRAM.EdmondsKarp.exists_bipartiteMatching_program`,
  `Cslib.Algorithms.WordRAM.EdmondsKarp.exists_perfectMatching_program`: uniform exact-basis
  bipartite matching and perfect matching programs.

## References

* [Koenig1931]
* [CLRS2009]
-/

public section

namespace Cslib.Algorithms.WordRAM.EdmondsKarp

open Cslib.Algorithms.Lean.MaxFlow Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.Algorithms.WordRAM.EdmondsKarp.Internal
open StateTransitionSpec (clientResult_bind clientState_bind clientResult_pure clientState_pure)

/-! ### Uniform bipartite matching, König vertex cover, and perfect matching -/

section UniformBipartite

/-- Row-major `0`/`1` encoding of `G : Fin m × Fin r → Bool`. -/
@[expose] def encodeBipartiteMatrix {m r : ℕ} (G : Fin m × Fin r → Bool) : List ℕ :=
  (List.finRange m).flatMap fun u => (List.finRange r).map fun v => if G (u, v) then 1 else 0

/-- Word-RAM input `m :: r :: encodeBipartiteMatrix G`: left count at address `1`, right count at
`2`, and `G (u, v)` (`0` or `1`) at `3 + u * r + v`. -/
@[expose] def encodeBipartiteInput {m r : ℕ} (G : Fin m × Fin r → Bool) : List ℕ :=
  m :: r :: encodeBipartiteMatrix G

private abbrev bmNodes (m r : ℕ) : ℕ := 2 + (m + r)
private abbrev bmMatBase (m r : ℕ) : ℕ := 3 + m * r
private abbrev bmScrBase (m r : ℕ) : ℕ := bmMatBase m r + bmNodes m r * bmNodes m r
private abbrev bmCovLBase (m r : ℕ) : ℕ := bmScrBase m r + ekScratch (bmNodes m r)
private abbrev bmCovRBase (m r : ℕ) : ℕ := bmCovLBase m r + m
private abbrev bmScratch (m r : ℕ) : ℕ :=
  bmNodes m r * bmNodes m r + ekScratch (bmNodes m r) + m + r

/-- Output address of the matching indicator for `(u, v)` (`1` iff `(u, v) ∈ M`). -/
@[expose] def bmMatchAddr (m r u v : ℕ) : ℕ :=
  3 + m * r + (2 + (m + r)) * (2 + (m + r)) + (2 + u) * (2 + (m + r)) + (2 + m + v)

/-- Output address of the König left-cover indicator for `u` (`1` iff `u ∈ C.left`). -/
@[expose] def bmCovLAddr (m r u : ℕ) : ℕ :=
  3 + m * r + 2 * ((2 + (m + r)) * (2 + (m + r))) + 2 * (2 + (m + r)) + u

/-- Output address of the König right-cover indicator for `v` (`1` iff `v ∈ C.right`). -/
@[expose] def bmCovRAddr (m r v : ℕ) : ℕ :=
  3 + m * r + 2 * ((2 + (m + r)) * (2 + (m + r))) + 2 * (2 + (m + r)) + m + v

private abbrev bmWorkspace (m r : ℕ) : ℕ :=
  3 + m * r + 2 * ((2 + (m + r)) * (2 + (m + r))) + 2 * (2 + (m + r)) + m + r

private theorem length_encodeBipartiteMatrix {m r : ℕ} (G : Fin m × Fin r → Bool) :
    (encodeBipartiteMatrix G).length = m * r := by
  simp [encodeBipartiteMatrix, List.length_flatMap, List.map_const', List.sum_replicate]

private theorem getElem_encodeBipartiteMatrix {m r : ℕ} (G : Fin m × Fin r → Bool)
    (u : Fin m) (v : Fin r) :
    (encodeBipartiteMatrix G)[u.1 * r + v.1]'(by
      rw [length_encodeBipartiteMatrix]
      exact Nat.mul_comm r u.1 ▸ Nat.mul_add_lt_mul_of_lt_of_lt u.2 v.2) =
      if G (u, v) then 1 else 0 := by
  have hlen : ∀ x ∈ List.finRange m,
      ((List.finRange r).map fun w => if G (x, w) then 1 else 0).length = r := fun _ _ => by
    simp
  have hq := List.getElem?_flatMap_mul_add (List.finRange m)
    (fun x => (List.finRange r).map fun w => if G (x, w) then 1 else 0) r hlen
    (i := u.1) (j := v.1) (by simp [u.2]) v.2
  have hlt : u.1 * r + v.1 < (encodeBipartiteMatrix G).length := by
    rw [length_encodeBipartiteMatrix]
    exact Nat.mul_comm r u.1 ▸ Nat.mul_add_lt_mul_of_lt_of_lt u.2 v.2
  have h1 : (encodeBipartiteMatrix G)[u.1 * r + v.1]? = some (if G (u, v) then 1 else 0) := by
    simpa [encodeBipartiteMatrix] using hq
  rw [List.getElem?_eq_getElem hlt] at h1
  exact Option.some.inj h1

private theorem bmInit_mem_edge {m r : ℕ} (G : Fin m × Fin r → Bool) (u : Fin m) (v : Fin r) :
    (Memory.State.init (encodeBipartiteInput G)).mem (3 + u.1 * r + v.1) =
      if G (u, v) then 1 else 0 := by
  have hlt : u.1 * r + v.1 < (encodeBipartiteMatrix G).length := by
    rw [length_encodeBipartiteMatrix]
    exact Nat.mul_comm r u.1 ▸ Nat.mul_add_lt_mul_of_lt_of_lt u.2 v.2
  change (if 3 + u.1 * r + v.1 = 0 then (encodeBipartiteInput G).length
    else (encodeBipartiteInput G).getD (3 + u.1 * r + v.1 - 1) 0) = _
  rw [ite_eq_right (by omega), show 3 + u.1 * r + v.1 - 1 = (u.1 * r + v.1) + 2 by omega]
  change (encodeBipartiteMatrix G).getD (u.1 * r + v.1) 0 = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
  exact getElem_encodeBipartiteMatrix G u v

private theorem inputFits_encodeBipartiteInput {m r w : ℕ} (G : Fin m × Fin r → Bool)
    (hw : Fits w (bmWorkspace m r)) : InputFits w (encodeBipartiteInput G) := by
  refine ⟨hw.of_le ?_, fun x hx => ?_⟩
  · simp only [encodeBipartiteInput, List.length_cons, length_encodeBipartiteMatrix, bmWorkspace]
    omega
  · simp only [encodeBipartiteInput, List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact hw.of_le (by dsimp only [bmWorkspace]; omega)
    · exact hw.of_le (by dsimp only [bmWorkspace]; omega)
    · simp only [encodeBipartiteMatrix, List.mem_flatMap, List.mem_map] at hx
      obtain ⟨_, _, _, _, rfl⟩ := hx
      split_ifs
      · exact hw.of_le (by dsimp only [bmWorkspace]; omega)
      · exact fits_zero w

private def bmSrcStep (d : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  Memory.write (bmMatBase d.1.1 d.1.2 + (2 + d.2)) 1
  pure (d.2 + 1)

private def bmSnkStep (d : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  let m := d.1.1
  let r := d.1.2
  Memory.write (bmMatBase m r + (2 + m + d.2) * bmNodes m r + 1) 1
  pure (d.2 + 1)

private def bmEdgeInner (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ := do
  let m := d.1.1.1
  let r := d.1.1.2
  let u := d.1.2
  let v := d.2
  let g ← Memory.read (3 + u * r + v)
  let cap := if g = 0 then 0 else 1
  Memory.write (bmMatBase m r + (2 + u) * bmNodes m r + (2 + m + v)) cap
  pure (v + 1)

private def bmEdgeOuter (d : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  let _ ← Memory.read 0
  let _ ← iterate bmEdgeInner (d.1, d.2) d.1.2 0
  pure (d.2 + 1)

private def bmCovRStep (d : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  let m := d.1.1
  let r := d.1.2
  let v := d.2
  let nv := bmNodes m r
  let dv ← Memory.read (bmScrBase m r + nv * nv + (2 + m + v))
  let bit := if dv < nv then 1 else 0
  Memory.write (bmCovRBase m r + v) bit
  pure (v + 1)

private def bmCovLInner (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ := do
  let m := d.1.1.1
  let r := d.1.1.2
  let u := d.1.2
  let v := d.2
  let nv := bmNodes m r
  let g ← Memory.read (3 + u * r + v)
  let dv ← Memory.read (bmScrBase m r + nv * nv + (2 + m + v))
  if g ≠ 0 ∧ dv = nv then
    Memory.write (bmCovLBase m r + u) 1
    pure (v + 1)
  else
    pure (v + 1)

private def bmCovLOuter (d : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  let m := d.1.1
  let r := d.1.2
  let u := d.2
  let nv := bmNodes m r
  let du ← Memory.read (bmScrBase m r + nv * nv + (2 + u))
  let bit := if du = nv then 1 else 0
  Memory.write (bmCovLBase m r + u) bit
  let _ ← iterate bmCovLInner ((m, r), u) r 0
  pure (u + 1)

private def bmMain (d : ℕ × ℕ) : Memory.Prog ℕ := do
  let m := d.1
  let r := d.2
  let nv := bmNodes m r
  let _ ← Memory.alloc (bmScratch m r)
  fillRange ((bmMatBase m r, 0), nv * nv)
  let _ ← iterate bmSrcStep (m, r) m 0
  let _ ← iterate bmSnkStep (m, r) r 0
  let _ ← iterate bmEdgeOuter (m, r) m 0
  let res ← ekProg (⟨nv, bmMatBase m r, bmScrBase m r, 1⟩, (0, 1))
  let _ ← iterate bmCovRStep (m, r) r 0
  let _ ← iterate bmCovLOuter (m, r) m 0
  pure res

private def bmProg (_ : Unit) : Memory.Prog ℕ := do
  let m ← Memory.read 1
  let r ← Memory.read 2
  bmMain (m, r)

private def pmProg (_ : Unit) : Memory.Prog ℕ := do
  let m ← Memory.read 1
  let r ← Memory.read 2
  let res ← bmMain (m, r)
  if m = r ∧ res = m then pure 1 else pure 0

local macro "bm_omega" : tactic => `(tactic| (
  dsimp -failIfUnchanged only [bmWorkspace, bmScratch, bmCovRAddr, bmCovLAddr, bmMatchAddr,
    bmCovRBase, bmCovLBase, bmScrBase, bmMatBase, bmNodes, ekScratch, ekBound, CtxFits] at *
  first | omega | nlinarith))

private theorem clientResult_bmEdgeInner (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bmEdgeInner d) = d.2 + 1 :=
  rfl

private theorem clientResult_bmEdgeOuter (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bmEdgeOuter d) = d.2 + 1 := by
  unfold bmEdgeOuter
  rw [clientResult_bind_read, clientResult_bind, clientResult_pure]

private theorem clientResult_bmCovLInner (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bmCovLInner d) = d.2 + 1 := by
  unfold bmCovLInner
  rw [clientResult_bind_read, clientResult_bind_read]
  split_ifs <;> simp only [clientResult_bind_write, clientResult_pure]

private theorem clientResult_bmCovLOuter (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bmCovLOuter d) = d.2 + 1 := by
  unfold bmCovLOuter
  rw [clientResult_bind_read, clientResult_bind_write, clientResult_bind, clientResult_pure]

private theorem bmSrcStep_realizes :
    Realizes .exact bmSrcStep (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (bmWorkspace d.1.1 d.1.2) ∧ d.2 < d.1.1) (fun _ _ => 0) := by
  unfold bmSrcStep
  realize
  all_goals
    obtain ⟨hw, hu⟩ := h
    apply hw.of_le; bm_omega

private theorem bmSnkStep_realizes :
    Realizes .exact bmSnkStep (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (bmWorkspace d.1.1 d.1.2) ∧ d.2 < d.1.2) (fun _ _ => 0) := by
  unfold bmSnkStep
  realize
  all_goals
    obtain ⟨hw, hv⟩ := h
    apply hw.of_le
    have h1 : (2 + d.1.1 + d.2) * (2 + (d.1.1 + d.1.2)) + 1 <
        (2 + (d.1.1 + d.1.2)) * (2 + (d.1.1 + d.1.2)) :=
      List.mul_add_lt_sq (by omega) (by omega)
    bm_omega

private theorem bmEdgeInner_realizes :
    Realizes .exact bmEdgeInner (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (bmWorkspace d.1.1.1 d.1.1.2) ∧ d.1.2 < d.1.1.1 ∧ d.2 < d.1.1.2)
      (fun _ _ => 0) := by
  unfold bmEdgeInner
  realize
  all_goals
    obtain ⟨hw, hu, hv⟩ := h
    apply hw.of_le
    have h1 : d.1.2 * d.1.1.2 + d.2 < d.1.1.1 * d.1.1.2 :=
      Nat.mul_comm d.1.1.2 d.1.2 ▸ Nat.mul_add_lt_mul_of_lt_of_lt hu hv
    have h2 : (2 + d.1.2) * (2 + (d.1.1.1 + d.1.1.2)) + (2 + d.1.1.1 + d.2) <
        (2 + (d.1.1.1 + d.1.1.2)) * (2 + (d.1.1.1 + d.1.1.2)) :=
      List.mul_add_lt_sq (by omega) (by omega)
    bm_omega

private theorem bmEdgeOuter_realizes :
    Realizes .exact bmEdgeOuter (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (bmWorkspace d.1.1 d.1.2) ∧ d.2 < d.1.1) (fun _ _ => 0) := by
  unfold bmEdgeOuter
  realize [bmEdgeInner_realizes]
  all_goals
    obtain ⟨hw, hu⟩ := h
    try (apply hw.of_le; bm_omega)
  refine iterationSafe_of_stepInv _ _ w _ (fun rem (v : ℕ) _ => v + rem = d.1.2) ?_ (Nat.zero_add _)
  intro rem v t hsum
  dsimp only at hsum ⊢
  refine ⟨⟨hw, hu, by omega⟩, ?_⟩
  rw [clientResult_bmEdgeInner]
  dsimp only
  omega

private theorem bmCovRStep_realizes :
    Realizes .exact bmCovRStep (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (bmWorkspace d.1.1 d.1.2) ∧ d.2 < d.1.2) (fun _ _ => 0) := by
  unfold bmCovRStep
  realize
  all_goals
    obtain ⟨hw, hv⟩ := h
    apply hw.of_le; bm_omega

private theorem bmCovLInner_realizes :
    Realizes .exact bmCovLInner (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (bmWorkspace d.1.1.1 d.1.1.2) ∧ d.1.2 < d.1.1.1 ∧ d.2 < d.1.1.2)
      (fun _ _ => 0) := by
  unfold bmCovLInner
  realize
  all_goals
    obtain ⟨hw, hu, hv⟩ := h
    apply hw.of_le
    have h1 : d.1.2 * d.1.1.2 + d.2 < d.1.1.1 * d.1.1.2 :=
      Nat.mul_comm d.1.1.2 d.1.2 ▸ Nat.mul_add_lt_mul_of_lt_of_lt hu hv
    bm_omega

private theorem bmCovLOuter_realizes :
    Realizes .exact bmCovLOuter (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (bmWorkspace d.1.1 d.1.2) ∧ d.2 < d.1.1) (fun _ _ => 0) := by
  unfold bmCovLOuter
  realize [bmCovLInner_realizes]
  all_goals
    obtain ⟨hw, hu⟩ := h
    try (apply hw.of_le; bm_omega)
  refine iterationSafe_of_stepInv _ _ w _ (fun rem (v : ℕ) _ => v + rem = d.1.2) ?_ (Nat.zero_add _)
  intro rem v t hsum
  dsimp only at hsum ⊢
  refine ⟨⟨hw, hu, by omega⟩, ?_⟩
  rw [clientResult_bmCovLInner]
  dsimp only
  omega

private theorem bmMain_realizes :
    Realizes .exact bmMain (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (bmWorkspace d.1 d.2) ∧ Fits w (ekBound (2 + (d.1 + d.2)) 1))
      (fun _ _ => 0) := by
  unfold bmMain
  realize [fillRange_realizes, bmSrcStep_realizes, bmSnkStep_realizes, bmEdgeOuter_realizes,
    ekProg_realizes, bmCovRStep_realizes, bmCovLOuter_realizes]
  all_goals
    obtain ⟨hw, hwB⟩ := h
    try (apply hw.of_le; bm_omega)
    try bm_omega
  · refine iterationSafe_of_stepInv _ _ w _ (fun rem (u : ℕ) _ => u + rem = d.1) ?_ (Nat.zero_add _)
    intro rem u t hsum
    dsimp only at hsum ⊢
    refine ⟨⟨hw, by omega⟩, ?_⟩
    change u + 1 + rem = d.1; omega
  · refine iterationSafe_of_stepInv _ _ w _ (fun rem (v : ℕ) _ => v + rem = d.2) ?_ (Nat.zero_add _)
    intro rem v t hsum
    dsimp only at hsum ⊢
    refine ⟨⟨hw, by omega⟩, ?_⟩
    change v + 1 + rem = d.2; omega
  · refine iterationSafe_of_stepInv _ _ w _ (fun rem (u : ℕ) _ => u + rem = d.1) ?_ (Nat.zero_add _)
    intro rem u t hsum
    dsimp only at hsum ⊢
    refine ⟨⟨hw, by omega⟩, ?_⟩
    rw [clientResult_bmEdgeOuter]; dsimp only; omega
  · refine ⟨by bm_omega, hw.of_le (by bm_omega), hwB⟩
  · refine iterationSafe_of_stepInv _ _ w _ (fun rem (v : ℕ) _ => v + rem = d.2) ?_ (Nat.zero_add _)
    intro rem v t hsum
    dsimp only at hsum ⊢
    refine ⟨⟨hw, by omega⟩, ?_⟩
    change v + 1 + rem = d.2; omega
  · refine iterationSafe_of_stepInv _ _ w _ (fun rem (u : ℕ) _ => u + rem = d.1) ?_ (Nat.zero_add _)
    intro rem u t hsum
    dsimp only at hsum ⊢
    refine ⟨⟨hw, by omega⟩, ?_⟩
    rw [clientResult_bmCovLOuter]; dsimp only; omega

private theorem bmProg_realizes :
    Realizes .exact bmProg (WordEncoding.encode (α := Unit)) (WordEncoding.encode (α := ℕ))
      (fun w _ st => Fits w (bmWorkspace (st.mem 1) (st.mem 2)) ∧
        Fits w (ekBound (2 + (st.mem 1 + st.mem 2)) 1)) (fun _ _ => 0) := by
  unfold bmProg
  realize [bmMain_realizes]
  all_goals
    obtain ⟨hw, hwB⟩ := h
    first
    | exact hw.of_le (by bm_omega)
    | exact hwB

private theorem pmProg_realizes :
    Realizes .exact pmProg (WordEncoding.encode (α := Unit)) (WordEncoding.encode (α := ℕ))
      (fun w _ st => Fits w (bmWorkspace (st.mem 1) (st.mem 2)) ∧
        Fits w (ekBound (2 + (st.mem 1 + st.mem 2)) 1)) (fun _ _ => 0) := by
  unfold pmProg
  realize [bmMain_realizes]
  all_goals
    obtain ⟨hw, hwB⟩ := h
    first
    | exact hw.of_le (by bm_omega)
    | exact hwB

private theorem memoryCost_bmMain_le (m r : ℕ) (s : Memory.State) :
    memoryCost (bmMain (m, r)) s ≤ 5200 * (m + r + 1) ^ 5 := by
  unfold bmMain
  dsimp only
  have hsrc : ∀ (u : ℕ) t, memoryCost (bmSrcStep ((m, r), u)) t ≤ 1 := fun _ _ => by
    unfold bmSrcStep; exact le_refl 1
  have hsnk : ∀ (v : ℕ) t, memoryCost (bmSnkStep ((m, r), v)) t ≤ 1 := fun _ _ => by
    unfold bmSnkStep; exact le_refl 1
  have hei : ∀ u v t, memoryCost (bmEdgeInner (((m, r), u), v)) t ≤ 2 := fun _ _ _ => by
    unfold bmEdgeInner
    exact memoryCost_read_bind_le fun _ _ => le_refl 1
  have heo : ∀ (u : ℕ) t, memoryCost (bmEdgeOuter ((m, r), u)) t ≤ 1 + 2 * r := fun u t => by
    unfold bmEdgeOuter
    refine (memoryCost_read_bind_le (k := 2 * r) fun _ t' => ?_).trans (by omega)
    have hit := memoryCost_iterate_le_of bmEdgeInner 2 ((m, r), u) (hei u) r 0 t'
    exact (memoryCost_bind_le (k₂ := 0) hit fun _ _ => le_refl 0).trans (by omega)
  have hcr : ∀ (v : ℕ) t, memoryCost (bmCovRStep ((m, r), v)) t ≤ 2 := fun _ _ => by
    unfold bmCovRStep
    exact memoryCost_read_bind_le fun _ _ => le_refl 1
  have hcli : ∀ u v t, memoryCost (bmCovLInner (((m, r), u), v)) t ≤ 3 := fun _ _ _ => by
    unfold bmCovLInner
    refine (memoryCost_read_bind_le (k := 2) fun _ _ =>
      (memoryCost_read_bind_le (k := 1) fun _ _ =>
        memoryCost_ite_le (memoryCost_write_bind_le fun _ _ => by simp) (by simp)).trans
      (by omega)).trans (by omega)
  have hclo : ∀ (u : ℕ) t, memoryCost (bmCovLOuter ((m, r), u)) t ≤ 2 + 3 * r := fun u t => by
    unfold bmCovLOuter
    refine (memoryCost_read_bind_le (k := 1 + 3 * r) fun _ _ =>
      (memoryCost_write_bind_le (k := 3 * r) fun _ t' => ?_).trans (by omega)).trans (by omega)
    have hit := memoryCost_iterate_le_of bmCovLInner 3 ((m, r), u) (hcli u) r 0 t'
    exact (memoryCost_bind_le (k₂ := 0) hit fun _ _ => le_refl 0).trans (by omega)
  have htot : memoryCost (bmMain (m, r)) s ≤
      (bmScratch m r + 1) + (bmNodes m r * bmNodes m r + (m + (r + ((1 + 2 * r) * m +
        (ekCost (bmNodes m r) + (2 * r + ((2 + 3 * r) * m + 0))))))) := by
    unfold bmMain
    dsimp only
    refine memoryCost_bind_le (memoryCost_alloc _ _).le fun _ t1 => ?_
    refine memoryCost_bind_le (memoryCost_fillRange_le _ _ _ t1) fun _ t2 => ?_
    refine memoryCost_bind_le
      (by simpa [Nat.one_mul] using memoryCost_iterate_le_of bmSrcStep 1 (m, r) hsrc m 0 t2)
      fun _ t3 => ?_
    refine memoryCost_bind_le
      (by simpa [Nat.one_mul] using memoryCost_iterate_le_of bmSnkStep 1 (m, r) hsnk r 0 t3)
      fun _ t4 => ?_
    refine memoryCost_bind_le
      (memoryCost_iterate_le_of bmEdgeOuter (1 + 2 * r) (m, r) heo m 0 t4) fun _ t5 => ?_
    refine memoryCost_bind_le (memoryCost_ekProg_le _ 0 1 t5) fun _ t6 => ?_
    refine memoryCost_bind_le
      (memoryCost_iterate_le_of bmCovRStep 2 (m, r) hcr r 0 t6) fun _ t7 => ?_
    refine memoryCost_bind_le
      (memoryCost_iterate_le_of bmCovLOuter (2 + 3 * r) (m, r) hclo m 0 t7) fun _ _ => by simp
  refine htot.trans ?_
  dsimp only [bmScratch, bmNodes, ekScratch, ekCost]
  set k := m + r + 1
  have hm : m ≤ k := by omega
  have hr : r ≤ k := by omega
  have hnv : 2 + (m + r) + 1 ≤ 3 * k := by omega
  have hpow5 : (2 + (m + r) + 1) ^ 5 ≤ (3 * k) ^ 5 := Nat.pow_le_pow_left hnv 5
  have h35 : (3 * k) ^ 5 = 243 * k ^ 5 := by ring
  have hk2 : k ^ 2 ≤ k ^ 5 := Nat.pow_le_pow_right (by omega) (by decide)
  have hk1 : 1 ≤ k ^ 5 := Nat.one_le_pow _ _ (by omega)
  have hmr : m * r ≤ k ^ 2 := by nlinarith
  have hnv2 : (2 + (m + r)) * (2 + (m + r)) ≤ 9 * k ^ 2 := by nlinarith
  nlinarith

private abbrev BmReady (w m r : ℕ) (s : Memory.State) : Prop :=
  Memory.WellFormed w s ∧ bmWorkspace m r ≤ s.frontier

private theorem validHistory_bmMain {w m r : ℕ} {st : Memory.State}
    (hwf : Memory.WellFormed w st) (hfr : st.frontier = 3 + m * r)
    (hw : Fits w (bmWorkspace m r)) (hwB : Fits w (ekBound (bmNodes m r) 1)) :
    (Memory.spec w).ValidHistory st ((Memory.spec w).clientHistory st (bmMain (m, r))) := by
  unfold bmMain
  dsimp only
  have halloc : (Memory.spec w).ValidHistory st
      ((Memory.spec w).clientHistory st (Memory.alloc (bmScratch m r))) :=
    validHistory_alloc (by rw [hfr]; exact hw.of_le (by bm_omega))
  refine validHistory_bind_step halloc ?_
  set s1 := (Memory.spec 0).clientState st (Memory.alloc (bmScratch m r))
  have hs1 : BmReady w m r s1 :=
    ⟨wellFormed_clientState hwf halloc,
      by change bmWorkspace m r ≤ st.frontier + bmScratch m r; rw [hfr]; bm_omega⟩
  have hfill := validHistory_fillRange (base := bmMatBase m r) (val := 0)
    (len := bmNodes m r * bmNodes m r) hs1.1 (by have := hs1.2; bm_omega) (fits_zero w)
  refine validHistory_bind_step hfill ?_
  set s2 := (Memory.spec 0).clientState s1
    (fillRange ((bmMatBase m r, 0), bmNodes m r * bmNodes m r))
  have hs2 : BmReady w m r s2 := MonotoneMemInv.pres hs1 hfill
  have hsrc : (Memory.spec w).ValidHistory s2
      ((Memory.spec w).clientHistory s2 (iterate bmSrcStep (m, r) m 0)) := by
    refine validHistory_iterate_nat (Inv := BmReady w m r) m 0 (fun u hu t ht => ⟨?_, ?_⟩) hs2
    · unfold bmSrcStep
      exact validHistory_write_bind (by have := ht.2; bm_omega)
        (hw.of_le (by bm_omega)) (validHistory_pure _ _ _)
    · rfl
  refine validHistory_bind_step hsrc ?_
  set s3 := (Memory.spec 0).clientState s2 (iterate bmSrcStep (m, r) m 0)
  have hs3 : BmReady w m r s3 := MonotoneMemInv.pres hs2 hsrc
  have hsnk : (Memory.spec w).ValidHistory s3
      ((Memory.spec w).clientHistory s3 (iterate bmSnkStep (m, r) r 0)) := by
    refine validHistory_iterate_nat (Inv := BmReady w m r) r 0 (fun v hv t ht => ⟨?_, ?_⟩) hs3
    · unfold bmSnkStep
      have h1 : (2 + m + v) * bmNodes m r + 1 < bmNodes m r * bmNodes m r :=
        List.mul_add_lt_sq (by dsimp only [bmNodes]; omega) (by dsimp only [bmNodes]; omega)
      exact validHistory_write_bind (by have := ht.2; bm_omega)
        (hw.of_le (by bm_omega)) (validHistory_pure _ _ _)
    · rfl
  refine validHistory_bind_step hsnk ?_
  set s4 := (Memory.spec 0).clientState s3 (iterate bmSnkStep (m, r) r 0)
  have hs4 : BmReady w m r s4 := MonotoneMemInv.pres hs3 hsnk
  have hedge : (Memory.spec w).ValidHistory s4
      ((Memory.spec w).clientHistory s4 (iterate bmEdgeOuter (m, r) m 0)) := by
    refine validHistory_iterate_nat (Inv := BmReady w m r) m 0 (fun u hu t ht => ⟨?_, ?_⟩) hs4
    · unfold bmEdgeOuter
      refine validHistory_read_bind (by have := ht.2; bm_omega) ?_
      refine validHistory_bind_step
        (validHistory_iterate_nat (Inv := BmReady w m r) r 0 (fun v hv t' ht' => ⟨?_, ?_⟩) ht)
        (validHistory_pure _ _ _)
      · unfold bmEdgeInner
        have h1 : u * r + v < m * r :=
          Nat.mul_comm r u ▸ Nat.mul_add_lt_mul_of_lt_of_lt (by omega) (by omega)
        have h2 : (2 + u) * bmNodes m r + (2 + m + v) < bmNodes m r * bmNodes m r :=
          List.mul_add_lt_sq (by dsimp only [bmNodes]; omega) (by dsimp only [bmNodes]; omega)
        refine validHistory_read_bind (by have := ht'.2; bm_omega) ?_
        exact validHistory_write_bind (by have := ht'.2; bm_omega)
          (hw.of_le (by split_ifs <;> bm_omega)) (validHistory_pure _ _ _)
      · exact clientResult_bmEdgeInner _ t'
    · exact clientResult_bmEdgeOuter _ t
  refine validHistory_bind_step hedge ?_
  set s5 := (Memory.spec 0).clientState s4 (iterate bmEdgeOuter (m, r) m 0)
  have hs5 : BmReady w m r s5 := MonotoneMemInv.pres hs4 hedge
  have hek := validHistory_ekProg (c := ⟨bmNodes m r, bmMatBase m r, bmScrBase m r, 1⟩)
    (src := 0) (snk := 1) ⟨by bm_omega, hw.of_le (by bm_omega), hwB⟩
    (by bm_omega) (by bm_omega) hs5.1 (by have := hs5.2; bm_omega)
  refine validHistory_bind_step hek ?_
  set s6 := (Memory.spec 0).clientState s5
    (ekProg (⟨bmNodes m r, bmMatBase m r, bmScrBase m r, 1⟩, (0, 1)))
  have hs6 : BmReady w m r s6 := MonotoneMemInv.pres hs5 hek
  have hcr : (Memory.spec w).ValidHistory s6
      ((Memory.spec w).clientHistory s6 (iterate bmCovRStep (m, r) r 0)) := by
    refine validHistory_iterate_nat (Inv := BmReady w m r) r 0 (fun v hv t ht => ⟨?_, ?_⟩) hs6
    · unfold bmCovRStep
      refine validHistory_read_bind (by have := ht.2; bm_omega) ?_
      exact validHistory_write_bind (by have := ht.2; bm_omega)
        (hw.of_le (by split_ifs <;> bm_omega)) (validHistory_pure _ _ _)
    · rfl
  refine validHistory_bind_step hcr ?_
  set s7 := (Memory.spec 0).clientState s6 (iterate bmCovRStep (m, r) r 0)
  have hs7 : BmReady w m r s7 := MonotoneMemInv.pres hs6 hcr
  have hcl : (Memory.spec w).ValidHistory s7
      ((Memory.spec w).clientHistory s7 (iterate bmCovLOuter (m, r) m 0)) := by
    refine validHistory_iterate_nat (Inv := BmReady w m r) m 0 (fun u hu t ht => ⟨?_, ?_⟩) hs7
    · unfold bmCovLOuter
      refine validHistory_read_bind (by have := ht.2; bm_omega) ?_
      have hw0 : (Memory.spec w).ValidHistory t
          ((Memory.spec w).clientHistory t (Memory.write (bmCovLBase m r + u)
            (if t.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + u)) = bmNodes m r
             then 1 else 0))) :=
        validHistory_write (by have := ht.2; bm_omega) (hw.of_le (by split_ifs <;> bm_omega))
      refine validHistory_bind_step hw0 ?_
      have ht1 := MonotoneMemInv.pres ht hw0
      refine validHistory_bind_step
        (validHistory_iterate_nat (Inv := BmReady w m r) r 0 (fun v hv t' ht' => ⟨?_, ?_⟩) ht1)
        (validHistory_pure _ _ _)
      · unfold bmCovLInner
        have h1 : u * r + v < m * r :=
          Nat.mul_comm r u ▸ Nat.mul_add_lt_mul_of_lt_of_lt (by omega) (by omega)
        refine validHistory_read_bind (by have := ht'.2; bm_omega) ?_
        refine validHistory_read_bind (by have := ht'.2; bm_omega) ?_
        refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
        exact validHistory_write_bind (by have := ht'.2; bm_omega)
          (hw.of_le (by bm_omega)) (validHistory_pure _ _ _)
      · exact clientResult_bmCovLInner _ t'
    · exact clientResult_bmCovLOuter _ t
  exact validHistory_bind_step hcl (validHistory_pure _ _ _)

private theorem bipartiteFinEquiv_val {m r : ℕ} :
    (bipartiteFinEquiv m r .source).1 = 0 ∧
    (bipartiteFinEquiv m r .sink).1 = 1 ∧
    (∀ u : Fin m, (bipartiteFinEquiv m r (.left u)).1 = 2 + u.1) ∧
    (∀ v : Fin r, (bipartiteFinEquiv m r (.right v)).1 = 2 + m + v.1) := by
  refine ⟨rfl, rfl, fun u => ?_, fun v => ?_⟩
  · simp [bipartiteFinEquiv, bipartiteVertexEquiv]
  · simp [bipartiteFinEquiv, bipartiteVertexEquiv]; omega

private theorem bmBuild_spec {m r : ℕ} (G : Fin m × Fin r → Bool) {st : Memory.State}
    (hG : ∀ u : Fin m, ∀ v : Fin r, st.mem (3 + u.1 * r + v.1) = if G (u, v) then 1 else 0) :
    let st1 := (Memory.spec 0).clientState st
      (fillRange ((bmMatBase m r, 0), bmNodes m r * bmNodes m r))
    let st2 := (Memory.spec 0).clientState st1 (iterate bmSrcStep (m, r) m 0)
    let st3 := (Memory.spec 0).clientState st2 (iterate bmSnkStep (m, r) r 0)
    let st4 := (Memory.spec 0).clientState st3 (iterate bmEdgeOuter (m, r) m 0)
    (∀ u : Fin m, ∀ v : Fin r, st4.mem (3 + u.1 * r + v.1) = if G (u, v) then 1 else 0) ∧
      ∀ x y : Fin (bmNodes m r),
        st4.mem (bmMatBase m r + x.1 * bmNodes m r + y.1) = (bipartiteFinNetwork G).cap x y := by
  intro st1 st2 st3 st4
  have h1 := fillRange_spec (bmMatBase m r) 0 (bmNodes m r * bmNodes m r) st
  have hG1 : ∀ u : Fin m, ∀ v : Fin r, st1.mem (3 + u.1 * r + v.1) = if G (u, v) then 1 else 0 := by
    intro u v
    have hlt : u.1 * r + v.1 < m * r := Nat.mul_comm r u.1 ▸ Nat.mul_add_lt_mul_of_lt_of_lt u.2 v.2
    rw [h1.2 _ (Or.inl (by dsimp only [bmMatBase]; omega))]
    exact hG u v
  -- `E u v` is the capacity of the arc `left u → right v` read from the input matrix.
  obtain ⟨E, hE⟩ : ∃ E : ℕ → ℕ → ℕ, ∀ u v, E u v = if st1.mem (3 + u * r + v) = 0 then 0 else 1 :=
    ⟨_, fun _ _ => rfl⟩
  -- Capacity matrix once the source arcs into the first `k₁` left vertices, the sink arcs out of
  -- the first `k₂` right vertices, the edge rows `< ku` and the first `kv` cells of row `ku`
  -- are set.
  let F (k₁ k₂ ku kv x y : ℕ) : ℕ :=
    if (x = 0 ∧ 2 ≤ y ∧ y < 2 + k₁) ∨ (2 + m ≤ x ∧ x < 2 + m + k₂ ∧ y = 1) then 1
    else if (2 ≤ x ∧ x < 2 + ku ∧ 2 + m ≤ y ∧ y < 2 + m + r) ∨
        (x = 2 + ku ∧ 2 + m ≤ y ∧ y < 2 + m + kv) then E (x - 2) (y - (2 + m))
    else 0
  let Inv (k₁ k₂ ku kv : ℕ) (t : Memory.State) : Prop :=
    (∀ a < bmMatBase m r, t.mem a = st1.mem a) ∧ ∀ x y : Fin (bmNodes m r),
      t.mem (bmMatBase m r + x.1 * bmNodes m r + y.1) = F k₁ k₂ ku kv x.1 y.1
  have hcongr : ∀ {k₁ k₂ ku kv k₁' k₂' ku' kv' t}, Inv k₁ k₂ ku kv t →
      (∀ x y, x < bmNodes m r → y < bmNodes m r → F k₁ k₂ ku kv x y = F k₁' k₂' ku' kv' x y) →
      Inv k₁' k₂' ku' kv' t :=
    fun hI hF => ⟨hI.1, fun x y => (hI.2 x y).trans (hF x y x.2 y.2)⟩
  -- Writing the single cell `(a, b)` keeps the invariant when it changes `F` only there.
  have hwrite : ∀ {k₁ k₂ ku kv k₁' k₂' ku' kv' addr a b v} {t : Memory.State},
      addr = bmMatBase m r + a * bmNodes m r + b → a < bmNodes m r → b < bmNodes m r →
      Inv k₁ k₂ ku kv t →
      (∀ x y, x < bmNodes m r → y < bmNodes m r →
        (if x = a ∧ y = b then v else F k₁ k₂ ku kv x y) = F k₁' k₂' ku' kv' x y) →
      Inv k₁' k₂' ku' kv' ⟨Function.update t.mem addr v, t.frontier⟩ := by
    intro _ _ _ _ _ _ _ _ addr a b v t haddr ha hb ⟨hlo, hmat⟩ hF
    subst haddr
    refine ⟨fun a' ha' => ?_, fun x y => ?_⟩
    · exact (Function.update_of_ne (by omega) _ _).trans (hlo a' ha')
    · have hc : bmMatBase m r + x.1 * bmNodes m r + y.1 = bmMatBase m r + a * bmNodes m r + b ↔
          x.1 = a ∧ y.1 = b :=
        ⟨fun h => (List.fin_mul_add_inj (x₂ := ⟨a, ha⟩) (y₂ := ⟨b, hb⟩)
          (by dsimp only; omega)).imp (congrArg Fin.val) (congrArg Fin.val),
          fun ⟨h1, h2⟩ => by rw [h1, h2]⟩
      simp only [Function.update_apply, hc, hmat]
      exact hF x.1 y.1 x.2 y.2
  have h2 := iterate_invariant_of bmSrcStep (m, r)
    (fun rem (k : ℕ) t => k + rem = m ∧ Inv k 0 0 0 t)
    (fun rem k t ⟨hsum, hI⟩ => by
      unfold bmSrcStep
      rw [clientResult_bind_write, clientState_bind_write, clientResult_pure, clientState_pure]
      refine ⟨by omega, hwrite (a := 0) (b := 2 + k) (by rw [Nat.zero_mul, Nat.add_zero])
        (by bm_omega) (by bm_omega) hI fun x y _ _ => ?_⟩
      dsimp only [F]; split_ifs <;> omega)
    (n := m) (a := 0) (s := st1) ⟨Nat.zero_add _, fun _ _ => rfl, fun x y => by
      rw [Nat.add_assoc, h1.1 _ (List.mul_add_lt_sq x.2 y.2)]
      dsimp only [F]; split_ifs <;> omega⟩
  have h3 := iterate_invariant_of bmSnkStep (m, r)
    (fun rem (k : ℕ) t => k + rem = r ∧ Inv m k 0 0 t)
    (fun rem k t ⟨hsum, hI⟩ => by
      unfold bmSnkStep
      rw [clientResult_bind_write, clientState_bind_write, clientResult_pure, clientState_pure]
      refine ⟨by omega, hwrite (a := 2 + m + k) (b := 1) rfl (by bm_omega) (by bm_omega) hI
        fun x y _ _ => ?_⟩
      dsimp only [F]; split_ifs <;> omega)
    (n := r) (a := 0) (s := st2) ⟨Nat.zero_add _, hcongr h2.2 fun x y _ _ => by
      have := h2.1; dsimp only [F]; split_ifs <;> omega⟩
  have h4 := iterate_invariant_of bmEdgeOuter (m, r)
    (fun rem (ku : ℕ) t => ku + rem = m ∧ Inv m r ku 0 t)
    (fun rem ku t ⟨hsum, hI⟩ => by
      have hku : ku < m := by omega
      have hinner := iterate_invariant_of bmEdgeInner ((m, r), ku)
        (fun remv (kv : ℕ) t' => kv + remv = r ∧ Inv m r ku kv t')
        (fun remv kv t' ⟨hsumv, hI'⟩ => by
          have hlt : ku * r + kv < m * r :=
            Nat.mul_comm r ku ▸ Nat.mul_add_lt_mul_of_lt_of_lt hku (by omega)
          unfold bmEdgeInner
          rw [clientResult_bind_read, clientState_bind_read, clientResult_bind_write,
            clientState_bind_write, clientResult_pure, clientState_pure]
          dsimp only
          rw [hI'.1 _ (by dsimp only [bmMatBase]; omega), ← hE]
          refine ⟨by omega, hwrite (a := 2 + ku) (b := 2 + m + kv) rfl (by bm_omega) (by bm_omega)
            hI' fun x y _ _ => ?_⟩
          dsimp only [F]; split_ifs <;> first | rfl | omega | (congr 1 <;> omega))
        (n := r) (a := 0) (s := t) ⟨Nat.zero_add _, hI⟩
      unfold bmEdgeOuter
      rw [clientResult_bind_read, clientResult_bind, clientResult_pure,
        clientState_bind_read, clientState_bind, clientState_pure]
      refine ⟨by omega, hcongr hinner.2 fun x y _ _ => ?_⟩
      have := hinner.1; dsimp only [F]; split_ifs <;> first | rfl | omega)
    (n := m) (a := 0) (s := st3) ⟨Nat.zero_add _, hcongr h3.2 fun x y _ _ => by
      have := h3.1; dsimp only [F]; split_ifs <;> first | rfl | omega⟩
  obtain ⟨hlo4, hmat4⟩ := hcongr h4.2 (k₁' := m) (k₂' := r) (ku' := m) (kv' := 0)
    fun x y _ _ => by have := h4.1; dsimp only [F]; split_ifs <;> first | rfl | omega
  refine ⟨fun u v => ?_, fun x y => ?_⟩
  · have hlt : u.1 * r + v.1 < m * r := Nat.mul_comm r u.1 ▸ Nat.mul_add_lt_mul_of_lt_of_lt u.2 v.2
    rw [hlo4 _ (by dsimp only [bmMatBase]; omega)]
    exact hG1 u v
  · rw [hmat4 x y]
    obtain ⟨hsrc0, hsnk1, hleft, hright⟩ := bipartiteFinEquiv_val (m := m) (r := r)
    have hx_eq : x = bipartiteFinEquiv m r ((bipartiteFinEquiv m r).symm x) :=
      ((bipartiteFinEquiv m r).apply_symm_apply x).symm
    have hy_eq : y = bipartiteFinEquiv m r ((bipartiteFinEquiv m r).symm y) :=
      ((bipartiteFinEquiv m r).apply_symm_apply y).symm
    change _ = (bipartiteNetwork G).cap ((bipartiteFinEquiv m r).symm x)
        ((bipartiteFinEquiv m r).symm y)
    generalize (bipartiteFinEquiv m r).symm x = bx at hx_eq
    generalize (bipartiteFinEquiv m r).symm y = by_ at hy_eq
    have hxval : x.1 = (bipartiteFinEquiv m r bx).1 := congrArg Fin.val hx_eq
    have hyval : y.1 = (bipartiteFinEquiv m r by_).1 := congrArg Fin.val hy_eq
    cases bx <;> cases by_ <;>
      simp only [hsrc0, hsnk1, hleft, hright, bipartiteNetwork] at hxval hyval ⊢ <;>
      dsimp only [F]
    all_goals try (split_ifs <;> omega)
    -- Remaining case: left u, right v
    rename_i u v
    have := u.2; have := v.2
    rw [ite_eq_right (by omega), ite_eq_left (Or.inl (by omega)), show x.1 - 2 = u.1 by omega,
      show y.1 - (2 + m) = v.1 by omega, hE, hG1]
    cases G (u, v) <;> rfl

private theorem bmCovR_spec {m r : ℕ} (st : Memory.State) :
    let st' := (Memory.spec 0).clientState st (iterate bmCovRStep (m, r) r 0)
    (∀ a < bmCovRBase m r, st'.mem a = st.mem a) ∧
      (∀ v : Fin r, st'.mem (bmCovRBase m r + v.1) =
        if st.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + m + v.1)) < bmNodes m r
        then 1 else 0) := by
  have h := iterate_invariant_of bmCovRStep (m, r)
    (fun rem (k : ℕ) t => k + rem = r ∧
      (∀ a < bmCovRBase m r, t.mem a = st.mem a) ∧
      (∀ v : Fin r, v.1 < k → t.mem (bmCovRBase m r + v.1) =
        if st.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + m + v.1)) < bmNodes m r
        then 1 else 0))
    (fun rem k t ⟨hsum, hlo, hcov⟩ => by
      unfold bmCovRStep
      rw [clientResult_bind_read, clientState_bind_read, clientResult_bind_write,
        clientState_bind_write, clientResult_pure, clientState_pure]
      dsimp only
      have hread : t.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + m + k)) =
          st.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + m + k)) :=
        hlo _ (by bm_omega)
      refine ⟨by omega, fun a ha => ?_, fun v hv => ?_⟩
      · rw [Function.update_of_ne (by omega)]; exact hlo a ha
      · by_cases hvk : v.1 = k
        · rw [hvk, Function.update_self, hread]
        · rw [Function.update_of_ne (by omega)]; exact hcov v (by omega))
    (n := r) (a := 0) (s := st)
      ⟨Nat.zero_add _, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  exact ⟨h.2.1, fun v => h.2.2 v (by omega)⟩

private theorem bmCovL_spec {m r : ℕ} (G : Fin m × Fin r → Bool) {st : Memory.State}
    (hG : ∀ u : Fin m, ∀ v : Fin r, st.mem (3 + u.1 * r + v.1) = if G (u, v) then 1 else 0) :
    let st' := (Memory.spec 0).clientState st (iterate bmCovLOuter (m, r) m 0)
    (∀ a, (a < bmCovLBase m r ∨ bmCovRBase m r ≤ a) → st'.mem a = st.mem a) ∧
      (∀ u : Fin m, st'.mem (bmCovLBase m r + u.1) =
        if st.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + u.1)) = bmNodes m r ∨
           ∃ v : Fin r, G (u, v) = true ∧
             st.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + m + v.1)) = bmNodes m r
        then 1 else 0) := by
  have h := iterate_invariant_of bmCovLOuter (m, r)
    (fun rem (ku : ℕ) t => ku + rem = m ∧
      (∀ a, (a < bmCovLBase m r ∨ bmCovRBase m r ≤ a) → t.mem a = st.mem a) ∧
      (∀ u : Fin m, u.1 < ku → t.mem (bmCovLBase m r + u.1) =
        if st.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + u.1)) = bmNodes m r ∨
           ∃ v : Fin r, G (u, v) = true ∧
             st.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + m + v.1)) = bmNodes m r
        then 1 else 0))
    (fun rem ku t ⟨hsum, hfr, hcov⟩ => by
      have hku : ku < m := by omega
      have hdu : t.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + ku)) =
          st.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + ku)) :=
        hfr _ (Or.inl (by bm_omega))
      set t1 : Memory.State := ⟨Function.update t.mem (bmCovLBase m r + ku)
        (if t.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + ku)) = bmNodes m r
         then 1 else 0), t.frontier⟩
      have hinner := iterate_invariant_of bmCovLInner ((m, r), ku)
        (fun remv (kv : ℕ) t' => kv + remv = r ∧
          (∀ a, a ≠ bmCovLBase m r + ku → t'.mem a = t.mem a) ∧
          t'.mem (bmCovLBase m r + ku) =
            if st.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + ku)) = bmNodes m r ∨
               ∃ v : Fin r, v.1 < kv ∧ G (⟨ku, hku⟩, v) = true ∧
                 st.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + m + v.1)) = bmNodes m r
            then 1 else 0)
        (fun remv kv t' ⟨hsumv, hne, hcur⟩ => by
          have hkv : kv < r := by omega
          have hlt : ku * r + kv < m * r :=
            Nat.mul_comm r ku ▸ Nat.mul_add_lt_mul_of_lt_of_lt hku hkv
          have hg : t'.mem (3 + ku * r + kv) = if G (⟨ku, hku⟩, ⟨kv, hkv⟩) then 1 else 0 := by
            rw [hne _ (by bm_omega), hfr _ (Or.inl (by bm_omega))]
            exact hG ⟨ku, hku⟩ ⟨kv, hkv⟩
          have hdv : t'.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + m + kv)) =
              st.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + m + kv)) := by
            rw [hne _ (by bm_omega), hfr _ (Or.inl (by bm_omega))]
          unfold bmCovLInner
          rw [clientResult_bind_read, clientResult_bind_read, clientState_bind_read,
            clientState_bind_read, hg, hdv]
          by_cases hcond : (if G (⟨ku, hku⟩, ⟨kv, hkv⟩) = true then 1 else 0) ≠ 0 ∧
              st.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + m + kv)) = bmNodes m r
          · rw [ite_eq_left hcond, clientResult_bind_write, clientResult_pure,
              clientState_bind_write, clientState_pure]
            have hGkv : G (⟨ku, hku⟩, ⟨kv, hkv⟩) = true := by simpa using hcond.1
            refine ⟨by omega, fun a ha => ?_, ?_⟩
            · dsimp only; rw [Function.update_of_ne ha]; exact hne a ha
            · dsimp only; rw [Function.update_self, ite_eq_left]
              exact Or.inr ⟨⟨kv, hkv⟩, by dsimp only; omega, hGkv, hcond.2⟩
          · rw [ite_eq_right hcond, clientResult_pure, clientState_pure, hcur]
            refine ⟨by omega, hne, if_congr (or_congr_right ⟨fun ⟨v, hv, h⟩ => ⟨v, by omega, h⟩,
              fun ⟨v, hv, h1, h2⟩ => ⟨v, Nat.lt_of_le_of_ne (by omega) fun hvk => hcond ?_, h1,
                h2⟩⟩) rfl rfl⟩
            obtain rfl : v = ⟨kv, hkv⟩ := Fin.ext hvk
            exact ⟨by simp [h1], h2⟩)
        (n := r) (a := 0) (s := t1) ⟨Nat.zero_add _, fun a ha => by
          dsimp only [t1]; rw [Function.update_of_ne ha], by
          dsimp only [t1]; rw [Function.update_self, hdu]
          exact if_congr (or_iff_left fun ⟨_, hv, _⟩ => Nat.not_lt_zero _ hv).symm rfl rfl⟩
      unfold bmCovLOuter
      rw [clientResult_bind_read, clientResult_bind_write, clientResult_bind, clientResult_pure,
        clientState_bind_read, clientState_bind_write, clientState_bind, clientState_pure]
      refine ⟨by omega, fun a ha => ?_, fun u hu => ?_⟩
      · rw [hinner.2.1 a (by rcases ha with ha | ha <;> bm_omega)]
        exact hfr a ha
      · by_cases huk : u.1 = ku
        · obtain rfl : u = ⟨ku, hku⟩ := Fin.ext huk
          have := hinner.1
          rw [hinner.2.2]
          exact if_congr (or_congr_right ⟨fun ⟨v, _, h⟩ => ⟨v, h⟩,
            fun ⟨v, h⟩ => ⟨v, by have := v.2; omega, h⟩⟩) rfl rfl
        · rw [hinner.2.1 _ (by omega)]
          exact hcov u (by omega))
    (n := m) (a := 0) (s := st)
    ⟨Nat.zero_add _, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  exact ⟨h.2.1, fun u => h.2.2 u (by omega)⟩

private theorem bmMain_spec {m r : ℕ} (G : Fin m × Fin r → Bool) {st : Memory.State}
    (hG : ∀ u : Fin m, ∀ v : Fin r, st.mem (3 + u.1 * r + v.1) = if G (u, v) then 1 else 0)
    (hfr : st.frontier = 3 + m * r) :
    let st' := (Memory.spec 0).clientState st (bmMain (m, r))
    let res := (Memory.spec 0).clientResult st (bmMain (m, r))
    ∃ (M : Finset (Fin m × Fin r)) (C : VertexCover (Fin m) (Fin r)),
      IsMaxMatching G M ∧ IsMinVertexCover G C ∧ M.card = C.size ∧ res = M.card ∧
      (∀ u : Fin m, ∀ v : Fin r, st'.mem (bmMatchAddr m r u.1 v.1) = if (u, v) ∈ M then 1 else 0) ∧
      (∀ u : Fin m, st'.mem (bmCovLAddr m r u.1) = if u ∈ C.left then 1 else 0) ∧
      (∀ v : Fin r, st'.mem (bmCovRAddr m r v.1) = if v ∈ C.right then 1 else 0) := by
  set st0 := (Memory.spec 0).clientState st (Memory.alloc (bmScratch m r))
  have hG0 : ∀ u : Fin m, ∀ v : Fin r, st0.mem (3 + u.1 * r + v.1) = if G (u, v) then 1 else 0 := by
    intro u v
    have hlt : u.1 * r + v.1 < m * r := Nat.mul_comm r u.1 ▸ Nat.mul_add_lt_mul_of_lt_of_lt u.2 v.2
    exact (Memory.mem_step_of_lt_frontier st (.alloc (bmScratch m r)) (by rw [hfr]; omega)
      (by simp)).trans (hG u v)
  obtain ⟨hG4, hmat4⟩ := bmBuild_spec G hG0
  set st1 := (Memory.spec 0).clientState st0
    (fillRange ((bmMatBase m r, 0), bmNodes m r * bmNodes m r))
  set st2 := (Memory.spec 0).clientState st1 (iterate bmSrcStep (m, r) m 0)
  set st3 := (Memory.spec 0).clientState st2 (iterate bmSnkStep (m, r) r 0)
  set st4 := (Memory.spec 0).clientState st3 (iterate bmEdgeOuter (m, r) m 0)
  have hst_ne : (bipartiteFinNetwork G).s ≠ (bipartiteFinNetwork G).t := fun h =>
    bipartiteNetwork_s_ne_t G ((bipartiteFinEquiv m r).injective h)
  have hcap_le1 : ∀ x y : Fin (bmNodes m r), (bipartiteFinNetwork G).cap x y ≤ 1 := fun x y => by
    change (bipartiteNetwork G).cap ((bipartiteFinEquiv m r).symm x)
      ((bipartiteFinEquiv m r).symm y) ≤ 1
    cases (bipartiteFinEquiv m r).symm x <;> cases (bipartiteFinEquiv m r).symm y <;>
      simp [bipartiteNetwork]
    split_ifs <;> omega
  have hst0_eq : (bipartiteFinNetwork G).s.1 = 0 ∧ (bipartiteFinNetwork G).t.1 = 1 :=
    ⟨bipartiteFinEquiv_val.1, bipartiteFinEquiv_val.2.1⟩
  have hEk := ekProg_flow_spec (mb := bmMatBase m r) (sb := bmScrBase m r) (B := 1)
    (bipartiteFinNetwork G) hst_ne hcap_le1 (le_refl _) hmat4
  rw [hst0_eq.1, hst0_eq.2] at hEk
  obtain ⟨hEk_frame, fFin, hflow, hdist_le, _, hmin, hC_eq, hval, hres⟩ := hEk
  set st5 := (Memory.spec 0).clientState st4
    (ekProg (⟨bmNodes m r, bmMatBase m r, bmScrBase m r, 1⟩, (0, 1)))
  set CFin : Finset (Fin (bmNodes m r)) :=
    Finset.univ.filter fun x =>
      st5.mem (distAddr ⟨bmNodes m r, bmMatBase m r, bmScrBase m r, 1⟩ x.1) < bmNodes m r
  obtain ⟨hR_fr, hR_cov⟩ := bmCovR_spec (m := m) (r := r) st5
  set st6 := (Memory.spec 0).clientState st5 (iterate bmCovRStep (m, r) r 0)
  have hG6 : ∀ u : Fin m, ∀ v : Fin r, st6.mem (3 + u.1 * r + v.1) = if G (u, v) then 1 else 0 := by
    intro u v
    have hlt : u.1 * r + v.1 < m * r := Nat.mul_comm r u.1 ▸ Nat.mul_add_lt_mul_of_lt_of_lt u.2 v.2
    rw [hR_fr _ (by bm_omega), hEk_frame _ (Or.inl (by bm_omega))]
    exact hG4 u v
  obtain ⟨hL_fr, hL_cov⟩ := bmCovL_spec G hG6
  set st7 := (Memory.spec 0).clientState st6 (iterate bmCovLOuter (m, r) m 0)
  have hst_main : (Memory.spec 0).clientState st (bmMain (m, r)) = st7 := by
    unfold bmMain; dsimp only
    rw [clientState_bind, clientState_bind, clientState_bind, clientState_bind,
      clientState_bind, clientState_bind, clientState_bind, clientState_bind, clientState_pure]
  have hres_main : (Memory.spec 0).clientResult st (bmMain (m, r)) =
      (Memory.spec 0).clientResult st4
        (ekProg (⟨bmNodes m r, bmMatBase m r, bmScrBase m r, 1⟩, (0, 1))) := by
    unfold bmMain; dsimp only
    rw [clientResult_bind, clientResult_bind, clientResult_bind, clientResult_bind,
      clientResult_bind, clientResult_bind, clientResult_bind, clientResult_bind, clientResult_pure]
  let f := fFin.ofReindex (bipartiteFinEquiv m r)
  let S := Network.cutOfReindex (bipartiteFinEquiv m r) CFin
  have hS_cut : (bipartiteNetwork G).IsCut S :=
    Network.isCut_cutOfReindex (bipartiteFinEquiv m r) hmin.1
  have hcap_eq : (bipartiteNetwork G).cutCapacity S = (bipartiteFinNetwork G).cutCapacity CFin :=
    Network.cutCapacity_cutOfReindex (bipartiteFinEquiv m r) (bipartiteNetwork G) CFin
  have hf_val : f.value = fFin.value := Network.Flow.value_ofReindex (bipartiteFinEquiv m r) fFin
  obtain ⟨hM_max, hC_min, hMC_eq⟩ :=
    bipartiteMatching_of_maxFlow_minCut hS_cut (by rw [hf_val, hval, hcap_eq])
  refine ⟨flowToMatching f, cutToVertexCover G S, hM_max, hC_min, hMC_eq, ?_, ?_, ?_, ?_⟩
  · rw [hres_main, hres, ← hcap_eq]
    have hcoe := card_flowToMatching_coe f
    omega
  · intro u v
    rw [hst_main]
    have h1 : (2 + u.1) * bmNodes m r + (2 + m + v.1) < bmNodes m r * bmNodes m r :=
      List.mul_add_lt_sq (by have := u.2; dsimp only [bmNodes]; omega)
        (by have := v.2; dsimp only [bmNodes]; omega)
    rw [hL_fr _ (Or.inl (by dsimp only [bmMatchAddr]; bm_omega)),
      hR_fr _ (by dsimp only [bmMatchAddr]; bm_omega)]
    have hfl := hflow (bipartiteFinEquiv m r (.left u)) (bipartiteFinEquiv m r (.right v))
    obtain ⟨_, _, hleft, hright⟩ := bipartiteFinEquiv_val (m := m) (r := r)
    rw [hleft u, hright v] at hfl
    have haddr_m : bmMatchAddr m r u.1 v.1 =
        flowAddr ⟨bmNodes m r, bmMatBase m r, bmScrBase m r, 1⟩ (2 + u.1) (2 + m + v.1) := rfl
    rw [haddr_m, hfl]
    have hf_eq : fFin (bipartiteFinEquiv m r (.left u)) (bipartiteFinEquiv m r (.right v)) =
        f (.left u) (.right v) := rfl
    rw [hf_eq]
    have hle1 : f (.left u) (.right v) ≤ 1 := by
      have := f.le_cap (.left u) (.right v)
      simp only [bipartiteNetwork] at this
      split_ifs at this <;> omega
    simp only [flowToMatching, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs <;> omega
  · intro u
    rw [hst_main]
    have haddr_l : bmCovLAddr m r u.1 = bmCovLBase m r + u.1 := by
      dsimp only [bmCovLAddr, bmCovLBase, bmScrBase, bmMatBase, bmNodes, ekScratch]; ring
    rw [haddr_l, hL_cov u]
    have hdist_iff : ∀ x : Fin (bmNodes m r),
        st6.mem (bmScrBase m r + bmNodes m r * bmNodes m r + x.1) = bmNodes m r ↔ x ∉ CFin := by
      intro x
      rw [hR_fr _ (by have := x.2; bm_omega)]
      have hl := hdist_le x
      dsimp only [distAddr, bmNodes] at hl ⊢
      simp only [CFin, Finset.mem_filter, Finset.mem_univ, true_and, distAddr, bmNodes]
      omega
    obtain ⟨_, _, hleft, hright⟩ := bipartiteFinEquiv_val (m := m) (r := r)
    have hlu : st6.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + u.1)) = bmNodes m r ↔
        BipartiteVertex.left u ∉ S := by
      rw [← hleft u, hdist_iff]
      simp [S, Network.cutOfReindex]
    have hrv : ∀ v : Fin r,
        st6.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + m + v.1)) = bmNodes m r ↔
          BipartiteVertex.right v ∉ S := fun v => by
      rw [← hright v, hdist_iff]
      simp [S, Network.cutOfReindex]
    simp only [cutToVertexCover, Finset.mem_filter, Finset.mem_univ, true_and]
    exact if_congr (or_congr hlu (exists_congr fun v => and_congr_right fun _ => hrv v)) rfl rfl
  · intro v
    rw [hst_main]
    have haddr_r : bmCovRAddr m r v.1 = bmCovRBase m r + v.1 := by
      dsimp only [bmCovRAddr, bmCovRBase, bmCovLBase, bmScrBase, bmMatBase, bmNodes, ekScratch]
      ring
    rw [haddr_r, hL_fr _ (Or.inr (by omega)), hR_cov v]
    obtain ⟨_, _, _, hright⟩ := bipartiteFinEquiv_val (m := m) (r := r)
    have hrv : st5.mem (bmScrBase m r + bmNodes m r * bmNodes m r + (2 + m + v.1)) < bmNodes m r ↔
        BipartiteVertex.right v ∈ S := by
      rw [← hright v]
      simp [S, Network.cutOfReindex, CFin, distAddr]
    simp only [cutToVertexCover, Finset.mem_filter, Finset.mem_univ, true_and]
    exact if_congr hrv rfl rfl

private theorem bmInit_setup {m r w : ℕ} (G : Fin m × Fin r → Bool)
    (hw : Fits w (bmWorkspace m r)) :
    let st := Memory.State.init (encodeBipartiteInput G)
    st.frontier = 3 + m * r ∧ st.mem 1 = m ∧ st.mem 2 = r ∧
      Fits w ((encodeBipartiteInput G).length + 1) ∧ Memory.WellFormed w st := by
  have hfr : (Memory.State.init (encodeBipartiteInput G)).frontier = 3 + m * r := by
    simp only [Memory.State.init, encodeBipartiteInput, List.length_cons,
      length_encodeBipartiteMatrix]; omega
  have hlen : Fits w ((encodeBipartiteInput G).length + 1) := hw.of_le (by
    simp only [encodeBipartiteInput, List.length_cons, length_encodeBipartiteMatrix,
      bmWorkspace]; omega)
  exact ⟨hfr, by simp [Memory.State.init, encodeBipartiteInput],
    by simp [Memory.State.init, encodeBipartiteInput], hlen,
    Memory.wellFormed_init (inputFits_encodeBipartiteInput G hw) hlen⟩

/-- **Maximum bipartite matching and König vertex cover on the Word-RAM** ([Koenig1931];
[CLRS2009], Section 26.3): one uniform flat program over `Basis.exact` that, on
`encodeBipartiteInput G` for any `G : Fin m × Fin r → Bool`, halts within `C * (m + r + 1) ^ 5`
instructions at every word width fitting `ekBound (2 + (m + r)) 1`. It returns the maximum
matching cardinality `M.card = C.size`, stores `M` at `bmMatchAddr`, and stores a minimum König
vertex cover `C` at `bmCovLAddr` and `bmCovRAddr`. -/
theorem exists_bipartiteMatching_program :
    ∃ (R C pc : ℕ), 0 < C ∧ ∃ prog : Program .exact R,
      ∀ {m r w : ℕ} (G : Fin m × Fin r → Bool),
        Fits w (ekBound (2 + (m + r)) 1) →
        ∃ (y : Data R) (steps res : ℕ) (M : Finset (Fin m × Fin r))
          (cov : VertexCover (Fin m) (Fin r)),
          Runs w prog (State.init (encodeBipartiteInput G)) ⟨pc, y⟩ steps ∧
          step w prog ⟨pc, y⟩ = .halt res ∧
          steps + 1 ≤ C * (m + r + 1) ^ 5 ∧
          IsMaxMatching G M ∧ IsMinVertexCover G cov ∧ M.card = cov.size ∧ res = M.card ∧
          (∀ u : Fin m, ∀ v : Fin r,
            y.mem (bmMatchAddr m r u.1 v.1) = if (u, v) ∈ M then 1 else 0) ∧
          (∀ u : Fin m, y.mem (bmCovLAddr m r u.1) = if u ∈ cov.left then 1 else 0) ∧
          (∀ v : Fin r, y.mem (bmCovRAddr m r v.1) = if v ∈ cov.right then 1 else 0) := by
  obtain ⟨R, C₀, pc, prog, _, _, hprog⟩ :=
    bmProg_realizes.exists_standard_init_program_state_from_words 0
  refine ⟨R, 5204 * C₀ + 2, pc, by omega, prog, ?_⟩
  intro m r w G hwB
  have hw : Fits w (bmWorkspace m r) := hwB.of_le (by dsimp only [bmWorkspace, ekBound]; nlinarith)
  set st := Memory.State.init (encodeBipartiteInput G)
  obtain ⟨hfr, h1, h2, hlen, hwf⟩ := bmInit_setup G hw
  have hvh : (Memory.spec w).ValidHistory st ((Memory.spec w).clientHistory st (bmProg ())) := by
    unfold bmProg
    refine validHistory_read_bind (by rw [hfr]; omega) ?_
    refine validHistory_read_bind (by rw [hfr]; omega) ?_
    rw [h1, h2]
    exact validHistory_bmMain hwf hfr hw hwB
  obtain ⟨y, steps, hruns, hhalt, hmem, _, hbound⟩ :=
    hprog w () (encodeBipartiteInput G) (fun j => Fin.elim0 j) (Nat.zero_le _) hlen
      (inputFits_encodeBipartiteInput G hw) ⟨by rw [h1, h2]; exact hw, by rw [h1, h2]; exact hwB⟩
      hvh
  rw [clientState_width w (bmProg ())] at hmem
  rw [clientResult_width w (bmProg ())] at hhalt
  have hst_eq : (Memory.spec 0).clientState st (bmProg ()) =
      (Memory.spec 0).clientState st (bmMain (m, r)) := by
    unfold bmProg; rw [clientState_bind_read, clientState_bind_read, h1, h2]
  have hres_eq : (Memory.spec 0).clientResult st (bmProg ()) =
      (Memory.spec 0).clientResult st (bmMain (m, r)) := by
    unfold bmProg; rw [clientResult_bind_read, clientResult_bind_read, h1, h2]
  obtain ⟨M, cov, hM, hC, hMC, hres, hm_mem, hcl_mem, hcr_mem⟩ :=
    bmMain_spec G (bmInit_mem_edge G) hfr
  have hymem : y.mem = ((Memory.spec 0).clientState st (bmMain (m, r))).mem := by
    rw [← hst_eq]; exact congrArg Memory.State.mem hmem
  have hmc : memoryCost (bmProg ()) st ≤ 5202 * (m + r + 1) ^ 5 := by
    unfold bmProg
    rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
      memoryCost_bind', memoryCost_read, clientResult_read, clientState_read, h1, h2]
    have h1p : 1 ≤ (m + r + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
    have := memoryCost_bmMain_le m r st
    omega
  have hp : 1 ≤ (m + r + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  refine ⟨y, steps, _, M, cov, hruns, hhalt, ?_, hM, hC, hMC, hres_eq.trans hres,
    fun u v => by rw [hymem]; exact hm_mem u v,
    fun u => by rw [hymem]; exact hcl_mem u,
    fun v => by rw [hymem]; exact hcr_mem v⟩
  calc steps + 1
      ≤ C₀ * (memoryCost (bmProg ()) st + 0 + 1) + 1 := hbound
    _ ≤ C₀ * (5202 * (m + r + 1) ^ 5 + 1) + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 1
    _ ≤ (5204 * C₀ + 2) * (m + r + 1) ^ 5 := by nlinarith

/-- **Bipartite perfect matching decision on the Word-RAM:** one uniform flat program over
`Basis.exact` that, on `encodeBipartiteInput G` for any `G : Fin n × Fin n → Bool`, halts within
`C * (n + 1) ^ 5` instructions at every word width fitting `ekBound (2 + (n + n)) 1`, returning `1`
iff `Cslib.Circuits.BipartiteMatching.HasPerfectMatching G` and `0` otherwise. -/
theorem exists_perfectMatching_program :
    ∃ (R C pc : ℕ), 0 < C ∧ ∃ prog : Program .exact R,
      ∀ {n w : ℕ} (G : Fin n × Fin n → Bool),
        Fits w (ekBound (2 + (n + n)) 1) →
        ∃ (y : Data R) (steps res : ℕ),
          Runs w prog (State.init (encodeBipartiteInput G)) ⟨pc, y⟩ steps ∧
          step w prog ⟨pc, y⟩ = .halt res ∧
          steps + 1 ≤ C * (n + 1) ^ 5 ∧
          (res = 1 ↔ Cslib.Circuits.BipartiteMatching.HasPerfectMatching G) ∧
          res ≤ 1 := by
  obtain ⟨R, C₀, pc, prog, _, _, hprog⟩ :=
    pmProg_realizes.exists_standard_init_program_state_from_words 0
  refine ⟨R, 168000 * C₀ + 2, pc, by omega, prog, ?_⟩
  intro n w G hwB
  have hw : Fits w (bmWorkspace n n) := hwB.of_le (by dsimp only [bmWorkspace, ekBound]; nlinarith)
  set st := Memory.State.init (encodeBipartiteInput G)
  obtain ⟨hfr, h1, h2, hlen, hwf⟩ := bmInit_setup G hw
  have hvh : (Memory.spec w).ValidHistory st ((Memory.spec w).clientHistory st (pmProg ())) := by
    unfold pmProg
    refine validHistory_read_bind (by rw [hfr]; omega) ?_
    refine validHistory_read_bind (by rw [hfr]; omega) ?_
    rw [h1, h2]
    exact validHistory_bind_step (validHistory_bmMain hwf hfr hw hwB)
      (validHistory_ite (fun _ => validHistory_pure _ _ _) (fun _ => validHistory_pure _ _ _))
  obtain ⟨y, steps, hruns, hhalt, _, _, hbound⟩ :=
    hprog w () (encodeBipartiteInput G) (fun j => Fin.elim0 j) (Nat.zero_le _) hlen
      (inputFits_encodeBipartiteInput G hw) ⟨by rw [h1, h2]; exact hw, by rw [h1, h2]; exact hwB⟩
      hvh
  rw [clientResult_width w (pmProg ())] at hhalt
  obtain ⟨M, _, hM, _, _, hres, _, _, _⟩ := bmMain_spec G (bmInit_mem_edge G) hfr
  have hres_pm : (Memory.spec 0).clientResult st (pmProg ()) =
      if M.card = n then 1 else 0 := by
    unfold pmProg
    rw [clientResult_bind_read, clientResult_bind_read, h1, h2, clientResult_bind, hres]
    by_cases hc : M.card = n
    · rw [ite_eq_left ⟨rfl, hc⟩, ite_eq_left hc, clientResult_pure]
    · rw [ite_eq_right (fun h => hc h.2), ite_eq_right hc, clientResult_pure]
  have hmc : memoryCost (pmProg ()) st ≤ 167000 * (n + 1) ^ 5 := by
    unfold pmProg
    rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
      memoryCost_bind', memoryCost_read, clientResult_read, clientState_read, h1, h2]
    have hmain : memoryCost (bmMain (n, n) >>= fun res =>
        if n = n ∧ res = n then pure 1 else pure 0) st ≤ 5200 * (n + n + 1) ^ 5 + 0 :=
      memoryCost_bind_le (memoryCost_bmMain_le n n st) fun _ _ => by
        rw [memoryCost_ite]; split_ifs <;> exact le_refl 0
    have h2 : (n + n + 1) ^ 5 ≤ (2 * (n + 1)) ^ 5 := Nat.pow_le_pow_left (by omega) 5
    have h25 : (2 * (n + 1)) ^ 5 = 32 * (n + 1) ^ 5 := by ring
    have h1p : 1 ≤ (n + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have hp : 1 ≤ (n + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  refine ⟨y, steps, (Memory.spec 0).clientResult st (pmProg ()), hruns, hhalt, ?_, ?_, ?_⟩
  · calc steps + 1
        ≤ C₀ * (memoryCost (pmProg ()) st + 0 + 1) + 1 := hbound
      _ ≤ C₀ * (167000 * (n + 1) ^ 5 + 1) + 1 :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 1
      _ ≤ (168000 * C₀ + 2) * (n + 1) ^ 5 := by nlinarith
  · rw [hres_pm, hasPerfectMatching_iff_exists_matching_card, Fintype.card_fin]
    constructor
    · intro h
      have hcard : M.card = n := by split_ifs at h with hc; exact hc
      exact ⟨M, hM.1, hcard⟩
    · rintro ⟨M', hM', hcard⟩
      have hle₁ : n ≤ M.card := le_trans (le_of_eq hcard.symm) (hM.2 M' hM')
      have htriv : IsVertexCover G ⟨Finset.univ, ∅⟩ := fun u _ _ => .inl (Finset.mem_univ u)
      have hle₂ : M.card ≤ n := by
        simpa [VertexCover.size] using card_le_size_of_matching_vertexCover hM.1 htriv
      rw [ite_eq_left (by omega)]
  · rw [hres_pm]; split_ifs <;> omega

end UniformBipartite

end Cslib.Algorithms.WordRAM.EdmondsKarp
