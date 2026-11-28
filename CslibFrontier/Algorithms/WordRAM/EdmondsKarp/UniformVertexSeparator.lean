/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.MaxFlow.VertexSeparator
public import CslibFrontier.Algorithms.WordRAM.EdmondsKarp.Core
public import CslibFrontier.Algorithms.WordRAM.Karger.Contract
-- `import all`: reads `private theorem ekProg_flow_spec` without exporting it from `EdmondsKarp`.
import all CslibFrontier.Algorithms.WordRAM.EdmondsKarp.Spec
import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
import CslibFrontier.Foundations.Data.List.RowMajor
import CslibFrontier.Tactic.Realize
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Uniform Word-RAM program for minimum vertex separators

Uniform `Basis.exact` flat program and `O((n + 1) ^ 5)` runtime bound for minimum vertex
separators with side-labelling certificates (`exists_minSeparator_program`) by vertex splitting and
reduction to `ekProg`.

## Main definitions

* `Cslib.Algorithms.WordRAM.EdmondsKarp.encodeBoolVec`, `encodeSepInput`, `sepOutAddr`,
  `sepSideAddr`: input encoding and output separator/side-labelling addresses.

## Main results

* `Cslib.Algorithms.WordRAM.EdmondsKarp.exists_minSeparator_program`: uniform `O((n + 1) ^ 5)`
  Word-RAM minimum vertex separator program.

## References

* [Menger1927]
-/

public section

namespace Cslib.Algorithms.WordRAM.EdmondsKarp

open Cslib.Algorithms.Lean.MaxFlow Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.Algorithms.WordRAM.Karger
open StateTransitionSpec (clientResult_bind clientState_bind clientResult_pure clientState_pure)

/-! ### Uniform minimum vertex separator by vertex splitting -/

section UniformVertexSeparator

/-- Encode a Boolean vector of length `n` as `n` words (`1` for `true`, `0` for `false`). -/
@[expose] def encodeBoolVec {n : ℕ} (v : Vector Bool n) : List ℕ :=
  (List.finRange n).map fun i => if vget v i then 1 else 0

/-- Word-RAM input for minimum vertex separator: `n :: (encodeBoolVec Z ++ encodeBoolVec A ++
encodeBoolVec B ++ flattenMatrix (fun u v => if G.Adj u v then 1 else 0))`. Address `1` stores `n`;
`2 + v` stores `Z[v]`; `2 + n + v` stores `A[v]`; `2 + 2 * n + v` stores `B[v]`; and
`2 + 3 * n + u * n + v` stores `G.Adj u v`. -/
@[expose] def encodeSepInput {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Z A B : Vector Bool n) : List ℕ :=
  n :: (encodeBoolVec Z ++ encodeBoolVec A ++ encodeBoolVec B ++
    flattenMatrix (fun u v : Fin n => if G.Adj u v then 1 else 0))

private abbrev sepNodes (n : ℕ) : ℕ := n + n + 2
private abbrev sepMatBase (n : ℕ) : ℕ := 2 + 3 * n + n * n
private abbrev sepScrBase (n : ℕ) : ℕ := sepMatBase n + sepNodes n * sepNodes n
private abbrev sepOutBase (n : ℕ) : ℕ := sepScrBase n + ekScratch (sepNodes n)
private abbrev sepSideBase (n : ℕ) : ℕ := sepOutBase n + n
private abbrev sepScratch (n : ℕ) : ℕ :=
  sepNodes n * sepNodes n + ekScratch (sepNodes n) + n + n

/-- Output address of the separator indicator for `v` (`1` iff `v ∈ out.sep`). -/
@[expose] def sepOutAddr (n v : ℕ) : ℕ :=
  2 + 3 * n + n * n + 2 * ((n + n + 2) * (n + n + 2)) + 2 * (n + n + 2) + v

/-- Output address of the side-labelling indicator for `v` (`1` iff `vget out.side v = true`). -/
@[expose] def sepSideAddr (n v : ℕ) : ℕ :=
  2 + 3 * n + n * n + 2 * ((n + n + 2) * (n + n + 2)) + 2 * (n + n + 2) + n + v

private abbrev sepWorkspace (n : ℕ) : ℕ :=
  2 + 3 * n + n * n + 2 * ((n + n + 2) * (n + n + 2)) + 2 * (n + n + 2) + n + n

private theorem length_encodeBoolVec {n : ℕ} (v : Vector Bool n) :
    (encodeBoolVec v).length = n := by
  simp [encodeBoolVec]

private theorem getElem_encodeBoolVec {n : ℕ} (v : Vector Bool n) (i : Fin n) :
    (encodeBoolVec v)[i.1]'(by rw [length_encodeBoolVec]; exact i.2) =
      if vget v i then 1 else 0 := by
  simp [encodeBoolVec]

private theorem length_encodeSepInput {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Z A B : Vector Bool n) :
    (encodeSepInput G Z A B).length = 1 + 3 * n + n * n := by
  simp only [encodeSepInput, List.length_cons, List.length_append, length_encodeBoolVec,
    length_flattenMatrix]
  omega

private theorem sepInit_mem_Z {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Z A B : Vector Bool n) (v : Fin n) :
    (Memory.State.init (encodeSepInput G Z A B)).mem (2 + v.1) =
      if vget Z v then 1 else 0 := by
  have hv : v.1 < (encodeBoolVec Z).length := by rw [length_encodeBoolVec]; exact v.2
  change (if 2 + v.1 = 0 then (encodeSepInput G Z A B).length
    else (encodeSepInput G Z A B).getD (2 + v.1 - 1) 0) = _
  rw [ite_eq_right (by omega), show 2 + v.1 - 1 = v.1 + 1 by omega]
  change (encodeBoolVec Z ++ encodeBoolVec A ++ encodeBoolVec B ++
    flattenMatrix (fun u w : Fin n => if G.Adj u w then 1 else 0)).getD v.1 0 = _
  rw [List.getD_eq_getElem?_getD, List.append_assoc, List.append_assoc,
    List.getElem?_append_left hv, List.getElem?_eq_getElem hv, Option.getD_some,
    getElem_encodeBoolVec]

private theorem sepInit_mem_A {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Z A B : Vector Bool n) (v : Fin n) :
    (Memory.State.init (encodeSepInput G Z A B)).mem (2 + n + v.1) =
      if vget A v then 1 else 0 := by
  have hv : v.1 < (encodeBoolVec A).length := by rw [length_encodeBoolVec]; exact v.2
  change (if 2 + n + v.1 = 0 then (encodeSepInput G Z A B).length
    else (encodeSepInput G Z A B).getD (2 + n + v.1 - 1) 0) = _
  rw [ite_eq_right (by omega), show 2 + n + v.1 - 1 = (n + v.1) + 1 by omega]
  change (encodeBoolVec Z ++ encodeBoolVec A ++ encodeBoolVec B ++
    flattenMatrix (fun u w : Fin n => if G.Adj u w then 1 else 0)).getD (n + v.1) 0 = _
  rw [List.getD_eq_getElem?_getD, List.append_assoc, List.append_assoc,
    List.getElem?_append_right (by rw [length_encodeBoolVec]; omega),
    length_encodeBoolVec, Nat.add_sub_cancel_left,
    List.getElem?_append_left hv, List.getElem?_eq_getElem hv, Option.getD_some,
    getElem_encodeBoolVec]

private theorem sepInit_mem_B {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Z A B : Vector Bool n) (v : Fin n) :
    (Memory.State.init (encodeSepInput G Z A B)).mem (2 + 2 * n + v.1) =
      if vget B v then 1 else 0 := by
  have hv : v.1 < (encodeBoolVec B).length := by rw [length_encodeBoolVec]; exact v.2
  change (if 2 + 2 * n + v.1 = 0 then (encodeSepInput G Z A B).length
    else (encodeSepInput G Z A B).getD (2 + 2 * n + v.1 - 1) 0) = _
  rw [ite_eq_right (by omega), show 2 + 2 * n + v.1 - 1 = (2 * n + v.1) + 1 by omega]
  change (encodeBoolVec Z ++ encodeBoolVec A ++ encodeBoolVec B ++
    flattenMatrix (fun u w : Fin n => if G.Adj u w then 1 else 0)).getD (2 * n + v.1) 0 = _
  rw [List.getD_eq_getElem?_getD, List.append_assoc, List.append_assoc,
    List.getElem?_append_right (by rw [length_encodeBoolVec]; omega),
    length_encodeBoolVec, show 2 * n + v.1 - n = n + v.1 by omega,
    List.getElem?_append_right (by rw [length_encodeBoolVec]; omega),
    length_encodeBoolVec, Nat.add_sub_cancel_left,
    List.getElem?_append_left hv, List.getElem?_eq_getElem hv, Option.getD_some,
    getElem_encodeBoolVec]

private theorem sepInit_mem_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Z A B : Vector Bool n) (u v : Fin n) :
    (Memory.State.init (encodeSepInput G Z A B)).mem (2 + 3 * n + u.1 * n + v.1) =
      if G.Adj u v then 1 else 0 := by
  have hlt :
      u.1 * n + v.1 < (flattenMatrix (fun a b : Fin n => if G.Adj a b then 1 else 0)).length := by
    rw [length_flattenMatrix]; exact List.mul_add_lt_sq u.2 v.2
  change (if 2 + 3 * n + u.1 * n + v.1 = 0 then (encodeSepInput G Z A B).length
    else (encodeSepInput G Z A B).getD (2 + 3 * n + u.1 * n + v.1 - 1) 0) = _
  rw [ite_eq_right (by omega), show 2 + 3 * n + u.1 * n + v.1 - 1 =
    (3 * n + (u.1 * n + v.1)) + 1 by omega]
  change (encodeBoolVec Z ++ encodeBoolVec A ++ encodeBoolVec B ++
    flattenMatrix (fun a b : Fin n => if G.Adj a b then 1 else 0)).getD
      (3 * n + (u.1 * n + v.1)) 0 = _
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp only [List.length_append, length_encodeBoolVec]; omega),
    show (encodeBoolVec Z ++ encodeBoolVec A ++ encodeBoolVec B).length = 3 * n by
      simp only [List.length_append, length_encodeBoolVec]; omega,
    Nat.add_sub_cancel_left, List.getElem?_eq_getElem hlt, Option.getD_some,
    getElem_flattenMatrix]

private theorem inputFits_encodeSepInput {n w : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Z A B : Vector Bool n) (hw : Fits w (sepWorkspace n)) :
    InputFits w (encodeSepInput G Z A B) := by
  have h1 : Fits w 1 := hw.of_le (by dsimp only [sepWorkspace]; omega)
  have hbv : ∀ (v : Vector Bool n) x, x ∈ encodeBoolVec v → Fits w x := by
    intro v x hx
    simp only [encodeBoolVec, List.mem_map] at hx
    obtain ⟨_, _, rfl⟩ := hx
    split_ifs
    · exact h1
    · exact fits_zero w
  refine ⟨hw.of_le (by rw [length_encodeSepInput]; dsimp only [sepWorkspace]; omega),
    fun x hx => ?_⟩
  simp only [encodeSepInput, List.mem_cons, List.mem_append] at hx
  rcases hx with rfl | (((hx | hx) | hx) | hx)
  · exact hw.of_le (by dsimp only [sepWorkspace]; omega)
  · exact hbv Z x hx
  · exact hbv A x hx
  · exact hbv B x hx
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    rw [length_flattenMatrix] at hi
    have hn : 0 < n := Nat.pos_of_ne_zero fun h => by simp [h] at hi
    have hu : i / n < n := Nat.div_lt_of_lt_mul hi
    have hv : i % n < n := Nat.mod_lt i hn
    have hidx : i = (⟨i / n, hu⟩ : Fin n).1 * n + (⟨i % n, hv⟩ : Fin n).1 :=
      (Nat.div_add_mod' i n).symm
    have he := getElem_flattenMatrix (W := fun a b : Fin n => if G.Adj a b then 1 else 0)
      ⟨i / n, hu⟩ ⟨i % n, hv⟩
    have hval : (flattenMatrix (fun a b : Fin n => if G.Adj a b then 1 else 0))[i] =
        if G.Adj ⟨i / n, hu⟩ ⟨i % n, hv⟩ then 1 else 0 := by
      rw [← he]; congr 1
    rw [hval]
    split_ifs
    · exact h1
    · exact fits_zero w

private def sepVertStep (d : ℕ × ℕ) : Memory.Prog ℕ := do
  let n := d.1
  let v := d.2
  let nv := sepNodes n
  let z ← Memory.read (2 + v)
  let a ← Memory.read (2 + n + v)
  let b ← Memory.read (2 + 2 * n + v)
  let capA := if a = 0 then 0 else n + 1
  let capB := if b = 0 then 0 else n + 1
  let capZ := if z = 0 then 1 else 0
  Memory.write (sepMatBase n + (v + 2)) capA
  Memory.write (sepMatBase n + (v + n + 2) * nv + 1) capB
  Memory.write (sepMatBase n + (v + 2) * nv + (v + n + 2)) capZ
  pure (v + 1)

private def sepEdgeInner (d : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  let n := d.1.1
  let u := d.1.2
  let v := d.2
  let nv := sepNodes n
  let e ← Memory.read (2 + 3 * n + u * n + v)
  let cap := if e = 0 then 0 else n + 1
  Memory.write (sepMatBase n + (u + n + 2) * nv + (v + 2)) cap
  pure (v + 1)

private def sepEdgeOuter (d : ℕ × ℕ) : Memory.Prog ℕ := do
  let _ ← Memory.read 0
  let _ ← iterate sepEdgeInner d d.1 0
  pure (d.2 + 1)

private def sepExtractStep (d : ℕ × ℕ) : Memory.Prog ℕ := do
  let n := d.1
  let v := d.2
  let nv := sepNodes n
  let z ← Memory.read (2 + v)
  let din ← Memory.read (sepScrBase n + nv * nv + (v + 2))
  let dout ← Memory.read (sepScrBase n + nv * nv + (v + n + 2))
  let inSep := if z = 0 ∧ din < nv ∧ dout = nv then 1 else 0
  let inSide := if dout < nv then 1 else 0
  Memory.write (sepOutBase n + v) inSep
  Memory.write (sepSideBase n + v) inSide
  pure (v + 1)

private def sepMain (n : ℕ) : Memory.Prog ℕ := do
  let nv := sepNodes n
  let _ ← Memory.alloc (sepScratch n)
  fillRange ((sepMatBase n, 0), nv * nv)
  let _ ← iterate sepVertStep n n 0
  let _ ← iterate sepEdgeOuter n n 0
  let res ← ekProg (⟨nv, sepMatBase n, sepScrBase n, n + 1⟩, (0, 1))
  let _ ← iterate sepExtractStep n n 0
  pure res

private def sepProg (_ : Unit) : Memory.Prog ℕ := do
  let n ← Memory.read 1
  sepMain n

local macro "sep_omega" : tactic => `(tactic| (
  dsimp -failIfUnchanged only [sepWorkspace, sepScratch, sepOutAddr, sepSideAddr,
    sepSideBase, sepOutBase, sepScrBase, sepMatBase, sepNodes, ekScratch, ekBound, CtxFits] at *
  first | omega | nlinarith))

private theorem clientResult_sepEdgeOuter (d : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (sepEdgeOuter d) = d.2 + 1 := by
  unfold sepEdgeOuter
  rw [clientResult_bind_read, clientResult_bind, clientResult_pure]

private theorem sepVertStep_realizes :
    Realizes .exact sepVertStep (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (sepWorkspace d.1) ∧ d.2 < d.1) (fun _ _ => 0) := by
  unfold sepVertStep
  realize
  all_goals
    obtain ⟨hw, hv⟩ := h
    apply hw.of_le
    have h1 : (d.2 + d.1 + 2) * (d.1 + d.1 + 2) + 1 <
        (d.1 + d.1 + 2) * (d.1 + d.1 + 2) := List.mul_add_lt_sq (by omega) (by omega)
    have h2 : (d.2 + 2) * (d.1 + d.1 + 2) + (d.2 + d.1 + 2) <
        (d.1 + d.1 + 2) * (d.1 + d.1 + 2) := List.mul_add_lt_sq (by omega) (by omega)
    sep_omega

private theorem sepEdgeInner_realizes :
    Realizes .exact sepEdgeInner (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (sepWorkspace d.1.1) ∧ d.1.2 < d.1.1 ∧ d.2 < d.1.1)
      (fun _ _ => 0) := by
  unfold sepEdgeInner
  realize
  all_goals
    obtain ⟨hw, hu, hv⟩ := h
    apply hw.of_le
    have h1 : d.1.2 * d.1.1 + d.2 < d.1.1 * d.1.1 := List.mul_add_lt_sq hu hv
    have h2 : (d.1.2 + d.1.1 + 2) * (d.1.1 + d.1.1 + 2) + (d.2 + 2) <
        (d.1.1 + d.1.1 + 2) * (d.1.1 + d.1.1 + 2) := List.mul_add_lt_sq (by omega) (by omega)
    sep_omega

private theorem sepEdgeOuter_realizes :
    Realizes .exact sepEdgeOuter (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (sepWorkspace d.1) ∧ d.2 < d.1) (fun _ _ => 0) := by
  unfold sepEdgeOuter
  realize [sepEdgeInner_realizes]
  all_goals
    obtain ⟨hw, hu⟩ := h
    try (apply hw.of_le; sep_omega)
  refine iterationSafe_of_stepInv _ _ w _ (fun rem (v : ℕ) _ => v + rem = d.1) ?_ (Nat.zero_add _)
  intro rem v t hsum
  dsimp only at hsum ⊢
  refine ⟨⟨hw, hu, by omega⟩, ?_⟩
  change v + 1 + rem = d.1; omega

private theorem sepExtractStep_realizes :
    Realizes .exact sepExtractStep (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (sepWorkspace d.1) ∧ d.2 < d.1) (fun _ _ => 0) := by
  unfold sepExtractStep
  realize
  all_goals
    obtain ⟨hw, hv⟩ := h
    apply hw.of_le; sep_omega

private theorem sepMain_realizes :
    Realizes .exact sepMain (WordEncoding.encode (α := ℕ)) (WordEncoding.encode (α := ℕ))
      (fun w n _ => Fits w (sepWorkspace n) ∧ Fits w (ekBound (n + n + 2) (n + 1)))
      (fun _ _ => 0) := by
  unfold sepMain
  realize [fillRange_realizes, sepVertStep_realizes, sepEdgeOuter_realizes,
    ekProg_realizes, sepExtractStep_realizes]
  all_goals
    obtain ⟨hw, hwB⟩ := h
    try (apply hw.of_le; sep_omega)
    try sep_omega
  · refine iterationSafe_of_stepInv _ _ w _ (fun rem (v : ℕ) _ => v + rem = d) ?_ (Nat.zero_add _)
    intro rem v t hsum
    dsimp only at hsum ⊢
    refine ⟨⟨hw, by omega⟩, ?_⟩
    change v + 1 + rem = d; omega
  · refine iterationSafe_of_stepInv _ _ w _ (fun rem (u : ℕ) _ => u + rem = d) ?_ (Nat.zero_add _)
    intro rem u t hsum
    dsimp only at hsum ⊢
    refine ⟨⟨hw, by omega⟩, ?_⟩
    rw [clientResult_sepEdgeOuter]; dsimp only; omega
  · refine ⟨by sep_omega, hw.of_le (by sep_omega), hwB⟩
  · refine iterationSafe_of_stepInv _ _ w _ (fun rem (v : ℕ) _ => v + rem = d) ?_ (Nat.zero_add _)
    intro rem v t hsum
    dsimp only at hsum ⊢
    refine ⟨⟨hw, by omega⟩, ?_⟩
    change v + 1 + rem = d; omega

private theorem sepProg_realizes :
    Realizes .exact sepProg (WordEncoding.encode (α := Unit)) (WordEncoding.encode (α := ℕ))
      (fun w _ st => Fits w (sepWorkspace (st.mem 1)) ∧
        Fits w (ekBound (st.mem 1 + st.mem 1 + 2) (st.mem 1 + 1))) (fun _ _ => 0) := by
  unfold sepProg
  realize [sepMain_realizes]
  all_goals
    obtain ⟨hw, hwB⟩ := h
    first
    | exact hw.of_le (by sep_omega)
    | exact hwB

private theorem memoryCost_sepMain_le (n : ℕ) (s : Memory.State) :
    memoryCost (sepMain n) s ≤ 5200 * (n + 1) ^ 5 := by
  have hv : ∀ (v : ℕ) t, memoryCost (sepVertStep (n, v)) t ≤ 6 := fun _ _ => by
    unfold sepVertStep
    refine (memoryCost_read_bind_le (k := 5) fun _ _ =>
      (memoryCost_read_bind_le (k := 4) fun _ _ =>
        (memoryCost_read_bind_le (k := 3) fun _ _ =>
          (memoryCost_write_bind_le (k := 2) fun _ _ =>
            (memoryCost_write_bind_le (k := 1) fun _ _ => le_refl 1).trans
              (by omega)).trans (by omega)).trans (by omega)).trans (by omega)).trans (by omega)
  have hei : ∀ u v t, memoryCost (sepEdgeInner ((n, u), v)) t ≤ 2 := fun _ _ _ => by
    unfold sepEdgeInner
    exact memoryCost_read_bind_le fun _ _ => le_refl 1
  have heo : ∀ (u : ℕ) t, memoryCost (sepEdgeOuter (n, u)) t ≤ 1 + 2 * n := fun u t => by
    unfold sepEdgeOuter
    refine (memoryCost_read_bind_le (k := 2 * n) fun _ t' => ?_).trans (by omega)
    have hit := memoryCost_iterate_le_of sepEdgeInner 2 (n, u) (hei u) n 0 t'
    exact (memoryCost_bind_le (k₂ := 0) hit fun _ _ => le_refl 0).trans (by omega)
  have hex : ∀ (v : ℕ) t, memoryCost (sepExtractStep (n, v)) t ≤ 5 := fun _ _ => by
    unfold sepExtractStep
    refine (memoryCost_read_bind_le (k := 4) fun _ _ =>
      (memoryCost_read_bind_le (k := 3) fun _ _ =>
        (memoryCost_read_bind_le (k := 2) fun _ _ =>
          (memoryCost_write_bind_le (k := 1) fun _ _ => le_refl 1).trans
            (by omega)).trans (by omega)).trans (by omega)).trans (by omega)
  have htot : memoryCost (sepMain n) s ≤
      (sepScratch n + 1) + (sepNodes n * sepNodes n + (6 * n + ((1 + 2 * n) * n +
        (ekCost (sepNodes n) + (5 * n + 0))))) := by
    unfold sepMain
    dsimp only
    refine memoryCost_bind_le (memoryCost_alloc _ _).le fun _ t1 => ?_
    refine memoryCost_bind_le (memoryCost_fillRange_le _ _ _ t1) fun _ t2 => ?_
    refine memoryCost_bind_le (memoryCost_iterate_le_of sepVertStep 6 n hv n 0 t2) fun _ t3 => ?_
    refine memoryCost_bind_le
      (memoryCost_iterate_le_of sepEdgeOuter (1 + 2 * n) n heo n 0 t3) fun _ t4 => ?_
    refine memoryCost_bind_le (memoryCost_ekProg_le _ 0 1 t4) fun _ t5 => ?_
    refine memoryCost_bind_le
      (memoryCost_iterate_le_of sepExtractStep 5 n hex n 0 t5) fun _ _ => le_refl 0
  refine htot.trans ?_
  dsimp only [sepScratch, sepNodes, ekScratch, ekCost]
  set k := n + 1 with hk
  have hnv : n + n + 2 + 1 ≤ 3 * k := by omega
  have hpow5 : (n + n + 2 + 1) ^ 5 ≤ (3 * k) ^ 5 := Nat.pow_le_pow_left hnv 5
  have h35 : (3 * k) ^ 5 = 243 * k ^ 5 := by ring
  have hk2 : k ^ 2 ≤ k ^ 5 := Nat.pow_le_pow_right (by omega) (by decide)
  have hk1 : 1 ≤ k ^ 5 := Nat.one_le_pow _ _ (by omega)
  have hn2 : n * n ≤ k ^ 2 := by rw [hk]; nlinarith
  have hnv2 : (n + n + 2) * (n + n + 2) ≤ 9 * k ^ 2 := by rw [hk]; nlinarith
  nlinarith

private abbrev SepReady (w n : ℕ) (s : Memory.State) : Prop :=
  Memory.WellFormed w s ∧ sepWorkspace n ≤ s.frontier

private theorem validHistory_sepMain {w n : ℕ} {st : Memory.State}
    (hwf : Memory.WellFormed w st) (hfr : st.frontier = 2 + 3 * n + n * n)
    (hw : Fits w (sepWorkspace n)) (hwB : Fits w (ekBound (sepNodes n) (n + 1))) :
    (Memory.spec w).ValidHistory st ((Memory.spec w).clientHistory st (sepMain n)) := by
  unfold sepMain
  dsimp only
  have halloc : (Memory.spec w).ValidHistory st
      ((Memory.spec w).clientHistory st (Memory.alloc (sepScratch n))) :=
    validHistory_alloc (by rw [hfr]; exact hw.of_le (by sep_omega))
  refine validHistory_bind_step halloc ?_
  set s1 := (Memory.spec 0).clientState st (Memory.alloc (sepScratch n))
  have hs1 : SepReady w n s1 :=
    ⟨wellFormed_clientState hwf halloc,
      by change sepWorkspace n ≤ st.frontier + sepScratch n; rw [hfr]; sep_omega⟩
  have hfill := validHistory_fillRange (base := sepMatBase n) (val := 0)
    (len := sepNodes n * sepNodes n) hs1.1 (by have := hs1.2; sep_omega) (fits_zero w)
  refine validHistory_bind_step hfill ?_
  set s2 := (Memory.spec 0).clientState s1
    (fillRange ((sepMatBase n, 0), sepNodes n * sepNodes n))
  have hs2 : SepReady w n s2 := MonotoneMemInv.pres hs1 hfill
  have h1fit : Fits w 1 := hw.of_le (by sep_omega)
  have hn1fit : Fits w (n + 1) := hw.of_le (by sep_omega)
  have hvert : (Memory.spec w).ValidHistory s2
      ((Memory.spec w).clientHistory s2 (iterate sepVertStep n n 0)) := by
    refine validHistory_iterate_nat (Inv := SepReady w n) n 0 (fun v hv t ht => ⟨?_, ?_⟩) hs2
    · unfold sepVertStep
      have h1 : (v + n + 2) * sepNodes n + 1 < sepNodes n * sepNodes n :=
        List.mul_add_lt_sq (by dsimp only [sepNodes]; omega) (by dsimp only [sepNodes]; omega)
      have h2 : (v + 2) * sepNodes n + (v + n + 2) < sepNodes n * sepNodes n :=
        List.mul_add_lt_sq (by dsimp only [sepNodes]; omega) (by dsimp only [sepNodes]; omega)
      iterate 3 refine validHistory_read_bind (by have := ht.2; sep_omega) ?_
      refine validHistory_write_bind (by have := ht.2; sep_omega)
        (by split_ifs <;> first | exact fits_zero w | exact hn1fit) ?_
      refine validHistory_write_bind (by have := ht.2; sep_omega)
        (by split_ifs <;> first | exact fits_zero w | exact hn1fit) ?_
      exact validHistory_write_bind (by have := ht.2; sep_omega)
        (by split_ifs <;> first | exact h1fit | exact fits_zero w) (validHistory_pure _ _ _)
    · rfl
  refine validHistory_bind_step hvert ?_
  set s3 := (Memory.spec 0).clientState s2 (iterate sepVertStep n n 0)
  have hs3 : SepReady w n s3 := MonotoneMemInv.pres hs2 hvert
  have hedge : (Memory.spec w).ValidHistory s3
      ((Memory.spec w).clientHistory s3 (iterate sepEdgeOuter n n 0)) := by
    refine validHistory_iterate_nat (Inv := SepReady w n) n 0 (fun u hu t ht => ⟨?_, ?_⟩) hs3
    · unfold sepEdgeOuter
      refine validHistory_read_bind (by have := ht.2; sep_omega) ?_
      refine validHistory_bind_step
        (validHistory_iterate_nat (Inv := SepReady w n) n 0 (fun v hv t' ht' => ⟨?_, ?_⟩) ht)
        (validHistory_pure _ _ _)
      · unfold sepEdgeInner
        have h1 : u * n + v < n * n := List.mul_add_lt_sq (by omega) (by omega)
        have h2 : (u + n + 2) * sepNodes n + (v + 2) < sepNodes n * sepNodes n :=
          List.mul_add_lt_sq (by dsimp only [sepNodes]; omega) (by dsimp only [sepNodes]; omega)
        refine validHistory_read_bind (by have := ht'.2; sep_omega) ?_
        exact validHistory_write_bind (by have := ht'.2; sep_omega)
          (by split_ifs <;> first | exact fits_zero w | exact hn1fit) (validHistory_pure _ _ _)
      · rfl
    · exact clientResult_sepEdgeOuter _ t
  refine validHistory_bind_step hedge ?_
  set s4 := (Memory.spec 0).clientState s3 (iterate sepEdgeOuter n n 0)
  have hs4 : SepReady w n s4 := MonotoneMemInv.pres hs3 hedge
  have hek := validHistory_ekProg (c := ⟨sepNodes n, sepMatBase n, sepScrBase n, n + 1⟩)
    (src := 0) (snk := 1) ⟨by sep_omega, hw.of_le (by sep_omega), hwB⟩
    (by sep_omega) (by sep_omega) hs4.1 (by have := hs4.2; sep_omega)
  refine validHistory_bind_step hek ?_
  set s5 := (Memory.spec 0).clientState s4
    (ekProg (⟨sepNodes n, sepMatBase n, sepScrBase n, n + 1⟩, (0, 1)))
  have hs5 : SepReady w n s5 := MonotoneMemInv.pres hs4 hek
  have hex : (Memory.spec w).ValidHistory s5
      ((Memory.spec w).clientHistory s5 (iterate sepExtractStep n n 0)) := by
    refine validHistory_iterate_nat (Inv := SepReady w n) n 0 (fun v hv t ht => ⟨?_, ?_⟩) hs5
    · unfold sepExtractStep
      iterate 3 refine validHistory_read_bind (by have := ht.2; sep_omega) ?_
      refine validHistory_write_bind (by have := ht.2; sep_omega)
        (by split_ifs <;> first | exact h1fit | exact fits_zero w) ?_
      exact validHistory_write_bind (by have := ht.2; sep_omega)
        (by split_ifs <;> first | exact h1fit | exact fits_zero w) (validHistory_pure _ _ _)
    · rfl
  exact validHistory_bind_step hex (validHistory_pure _ _ _)

private theorem splitNode_equivFin_val {n : ℕ} :
    (SplitNode.equivFin n .src).1 = 0 ∧
    (SplitNode.equivFin n .snk).1 = 1 ∧
    (∀ v : Fin n, (SplitNode.equivFin n (.inV v)).1 = v.1 + 2) ∧
    (∀ v : Fin n, (SplitNode.equivFin n (.outV v)).1 = v.1 + n + 2) :=
  ⟨rfl, rfl, fun _ => rfl, fun _ => rfl⟩

private theorem sepBuild_spec {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Z A B : Vector Bool n) {st : Memory.State}
    (hZ : ∀ v : Fin n, st.mem (2 + v.1) = if vget Z v then 1 else 0)
    (hA : ∀ v : Fin n, st.mem (2 + n + v.1) = if vget A v then 1 else 0)
    (hB : ∀ v : Fin n, st.mem (2 + 2 * n + v.1) = if vget B v then 1 else 0)
    (hG : ∀ u v : Fin n, st.mem (2 + 3 * n + u.1 * n + v.1) = if G.Adj u v then 1 else 0) :
    let st1 := (Memory.spec 0).clientState st
      (fillRange ((sepMatBase n, 0), sepNodes n * sepNodes n))
    let st2 := (Memory.spec 0).clientState st1 (iterate sepVertStep n n 0)
    let st3 := (Memory.spec 0).clientState st2 (iterate sepEdgeOuter n n 0)
    (∀ a < sepMatBase n, st3.mem a = st.mem a) ∧
      ∀ x y : Fin (sepNodes n),
        st3.mem (sepMatBase n + x.1 * sepNodes n + y.1) =
          ((vertexSplitNetwork G Z A B).reindex (SplitNode.equivFin n)).cap x y := by
  intro st1 st2 st3
  have h1 := fillRange_spec (sepMatBase n) 0 (sepNodes n * sepNodes n) st
  -- Capacities read from the input: `cA v`, `cB v` and `cZ v` for the source, sink and split arcs
  -- of the vertex `v`, and `cE u v` for the arc `outV u → inV v`.
  obtain ⟨cA, hcA⟩ : ∃ c : ℕ → ℕ, ∀ v, c v = if st.mem (2 + n + v) = 0 then 0 else n + 1 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨cB, hcB⟩ : ∃ c : ℕ → ℕ, ∀ v, c v = if st.mem (2 + 2 * n + v) = 0 then 0 else n + 1 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨cZ, hcZ⟩ : ∃ c : ℕ → ℕ, ∀ v, c v = if st.mem (2 + v) = 0 then 1 else 0 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨cE, hcE⟩ : ∃ c : ℕ → ℕ → ℕ,
      ∀ u v, c u v = if st.mem (2 + 3 * n + u * n + v) = 0 then 0 else n + 1 :=
    ⟨_, fun _ _ => rfl⟩
  -- Capacity matrix once the source, sink and split arcs of the first `kA`, `kB` and `kZ`
  -- vertices, the edge rows `< ku` and the first `kv` cells of row `ku` are set.
  let F (kA kB kZ ku kv x y : ℕ) : ℕ :=
    if x = 0 ∧ 2 ≤ y ∧ y < kA + 2 then cA (y - 2)
    else if n + 2 ≤ x ∧ x < kB + n + 2 ∧ y = 1 then cB (x - n - 2)
    else if 2 ≤ x ∧ x < kZ + 2 ∧ y = x + n then cZ (x - 2)
    else if (n + 2 ≤ x ∧ x < ku + n + 2 ∧ 2 ≤ y ∧ y < n + 2) ∨
        (x = ku + n + 2 ∧ 2 ≤ y ∧ y < kv + 2) then cE (x - n - 2) (y - 2)
    else 0
  -- `Inv f t`: `t` agrees with `st` below the matrix and holds the matrix `f`.
  obtain ⟨Inv, hInv⟩ : ∃ Inv : (ℕ → ℕ → ℕ) → Memory.State → Prop, ∀ f t, Inv f t ↔
      (∀ a < sepMatBase n, t.mem a = st.mem a) ∧ ∀ x y : Fin (sepNodes n),
        t.mem (sepMatBase n + x.1 * sepNodes n + y.1) = f x.1 y.1 :=
    ⟨_, fun _ _ => Iff.rfl⟩
  -- Writing `v` to the cell `(a, b)` turns the matrix `f` into `f'` when they differ only there.
  have hwrite : ∀ {f f' : ℕ → ℕ → ℕ} {addr a b v} {t : Memory.State},
      addr = sepMatBase n + a * sepNodes n + b → a < sepNodes n → b < sepNodes n → Inv f t →
      f' a b = v → (∀ x y, ¬(x = a ∧ y = b) → f x y = f' x y) →
      Inv f' ⟨Function.update t.mem addr v, t.frontier⟩ := by
    intro f f' addr a b v t haddr ha hb hI hv hF
    obtain ⟨hlo, hmat⟩ := (hInv _ _).1 hI
    subst haddr
    refine (hInv _ _).2 ⟨fun a' ha' => (Function.update_of_ne (by omega) _ _).trans (hlo a' ha'),
      fun x y => ?_⟩
    have hc : sepMatBase n + x.1 * sepNodes n + y.1 = sepMatBase n + a * sepNodes n + b ↔
        x.1 = a ∧ y.1 = b :=
      ⟨fun h => (List.fin_mul_add_inj (x₂ := ⟨a, ha⟩) (y₂ := ⟨b, hb⟩)
        (by dsimp only; omega)).imp (congrArg Fin.val) (congrArg Fin.val),
        fun ⟨h1, h2⟩ => by rw [h1, h2]⟩
    refine (Function.update_apply _ _ _ _).trans <| (if_congr hc rfl (hmat x y)).trans ?_
    by_cases h : x.1 = a ∧ y.1 = b
    · rw [ite_eq_left h, h.1, h.2, hv]
    · exact (ite_eq_right h).trans (hF _ _ h)
  have h2 := iterate_invariant_of sepVertStep n
    (fun rem (k : ℕ) t => k + rem = n ∧ Inv (F k k k 0 0) t)
    (fun rem k t ⟨hsum, hI⟩ => by
      unfold sepVertStep
      rw [clientResult_bind_read, clientResult_bind_read, clientResult_bind_read,
        clientResult_bind_write, clientResult_bind_write, clientResult_bind_write,
        clientResult_pure,
        clientState_bind_read, clientState_bind_read, clientState_bind_read,
        clientState_bind_write, clientState_bind_write, clientState_bind_write,
        clientState_pure]
      dsimp only
      have hlo := ((hInv _ _).1 hI).1
      rw [hlo (2 + k) (by sep_omega), hlo (2 + n + k) (by sep_omega),
        hlo (2 + 2 * n + k) (by sep_omega), ← hcA, ← hcB, ← hcZ]
      have hA := hwrite (a := 0) (b := k + 2) (v := cA k) (f' := F (k + 1) k k 0 0)
        (by rw [Nat.zero_mul, Nat.add_zero]) (by sep_omega) (by sep_omega) hI
        (by dsimp only [F]; split_ifs <;> first | omega | congr 1)
        fun x y h => if_congr (by omega) rfl rfl
      have hB := hwrite (a := k + n + 2) (b := 1) (v := cB k) (f' := F (k + 1) (k + 1) k 0 0)
        rfl (by sep_omega) (by sep_omega) hA
        (by dsimp only [F]; split_ifs <;> first | omega | (congr 1; omega))
        fun x y h => if_congr Iff.rfl rfl (if_congr (by omega) rfl rfl)
      exact ⟨by omega, hwrite (a := k + 2) (b := k + n + 2) (v := cZ k)
        (f' := F (k + 1) (k + 1) (k + 1) 0 0) rfl (by sep_omega) (by sep_omega) hB
        (by dsimp only [F]; split_ifs <;> first | omega | congr 1)
        fun x y h => if_congr Iff.rfl rfl (if_congr Iff.rfl rfl (if_congr (by omega) rfl rfl))⟩)
    (n := n) (a := 0) (s := st1) ⟨Nat.zero_add _, (hInv _ _).2 ⟨fun a ha => h1.2 a (Or.inl ha),
      fun x y => by
        rw [Nat.add_assoc, h1.1 _ (List.mul_add_lt_sq x.2 y.2)]
        dsimp only [F]; split_ifs <;> omega⟩⟩
  obtain ⟨hk2, hI2⟩ := h2
  rw [Nat.add_zero] at hk2
  rw [hk2] at hI2
  have h3 := iterate_invariant_of sepEdgeOuter n
    (fun rem (ku : ℕ) t => ku + rem = n ∧ Inv (F n n n ku 0) t)
    (fun rem ku t ⟨hsum, hI⟩ => by
      have hku : ku < n := by omega
      obtain ⟨hkv, hI'⟩ := iterate_invariant_of sepEdgeInner (n, ku)
        (fun remv (kv : ℕ) t' => kv + remv = n ∧ Inv (F n n n ku kv) t')
        (fun remv kv t' ⟨hsumv, hI'⟩ => by
          have hlt : ku * n + kv < n * n := List.mul_add_lt_sq hku (by omega)
          unfold sepEdgeInner
          rw [clientResult_bind_read, clientState_bind_read, clientResult_bind_write,
            clientState_bind_write, clientResult_pure, clientState_pure]
          dsimp only
          rw [((hInv _ _).1 hI').1 _ (by dsimp only [sepMatBase]; omega), ← hcE]
          exact ⟨by omega, hwrite (a := ku + n + 2) (b := kv + 2) (v := cE ku kv)
            (f' := F n n n ku (kv + 1)) rfl (by sep_omega) (by sep_omega) hI'
            (by dsimp only [F]; split_ifs <;> first | omega | (congr 1; omega) | simp_all)
            fun x y h => if_congr Iff.rfl rfl <| if_congr Iff.rfl rfl <| if_congr Iff.rfl rfl <|
              if_congr (by omega) rfl rfl⟩)
        (n := n) (a := 0) (s := t) ⟨Nat.zero_add _, hI⟩
      unfold sepEdgeOuter
      rw [clientResult_bind_read, clientResult_bind, clientResult_pure,
        clientState_bind_read, clientState_bind, clientState_pure]
      refine ⟨by omega, (hInv _ _).2 ⟨((hInv _ _).1 hI').1, fun x y => ?_⟩⟩
      refine (((hInv _ _).1 hI').2 x y).trans <| if_congr Iff.rfl rfl <| if_congr Iff.rfl rfl <|
        if_congr Iff.rfl rfl <| if_congr (by omega) rfl rfl)
    (n := n) (a := 0) (s := st2) ⟨Nat.zero_add _, hI2⟩
  obtain ⟨hk3, hI3⟩ := h3
  rw [Nat.add_zero] at hk3
  rw [hk3] at hI3
  obtain ⟨hlo3, hmat3⟩ := (hInv _ _).1 hI3
  refine ⟨hlo3, fun x y => ?_⟩
  rw [hmat3 x y]
  obtain ⟨hsrc0, hsnk1, hinV, houtV⟩ := splitNode_equivFin_val (n := n)
  have hx_eq : x = SplitNode.equivFin n ((SplitNode.equivFin n).symm x) :=
    ((SplitNode.equivFin n).apply_symm_apply x).symm
  have hy_eq : y = SplitNode.equivFin n ((SplitNode.equivFin n).symm y) :=
    ((SplitNode.equivFin n).apply_symm_apply y).symm
  change _ = (vertexSplitNetwork G Z A B).cap ((SplitNode.equivFin n).symm x)
    ((SplitNode.equivFin n).symm y)
  generalize (SplitNode.equivFin n).symm x = sx at hx_eq
  generalize (SplitNode.equivFin n).symm y = sy at hy_eq
  have hxval : x.1 = (SplitNode.equivFin n sx).1 := congrArg Fin.val hx_eq
  have hyval : y.1 = (SplitNode.equivFin n sy).1 := congrArg Fin.val hy_eq
  cases sx <;> cases sy <;>
    simp only [hsrc0, hsnk1, hinV, houtV, vertexSplitNetwork, vertexSplitCap] at hxval hyval ⊢ <;>
    dsimp only [F]
  all_goals try (split_ifs <;> omega)
  · rename_i v
    have := v.2
    rw [ite_eq_left (by omega), show y.1 - 2 = v.1 by omega, hcA, hA v]
    cases vget A v <;> rfl
  · rename_i u v
    have := u.2; have := v.2
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    by_cases huv : u = v
    · subst huv
      rw [ite_eq_left (by omega), show x.1 - 2 = u.1 by omega, hcZ, hZ u]
      cases vget Z u <;> simp
    · have hne : u.1 ≠ v.1 := fun h => huv (Fin.ext h)
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (fun h => huv h.1)]
  · rename_i u
    have := u.2
    rw [ite_eq_right (by omega), ite_eq_left (by omega), show x.1 - n - 2 = u.1 by omega, hcB,
      hB u]
    cases vget B u <;> rfl
  · rename_i u v
    have := u.2; have := v.2
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left (Or.inl (by omega)), show x.1 - n - 2 = u.1 by omega,
      show y.1 - 2 = v.1 by omega, hcE, hG u v]
    by_cases h : G.Adj u v <;> simp [h]

private theorem sepExtract_spec {n : ℕ} (st : Memory.State) :
    let st' := (Memory.spec 0).clientState st (iterate sepExtractStep n n 0)
    (∀ v : Fin n, st'.mem (sepOutBase n + v.1) =
      if st.mem (2 + v.1) = 0 ∧
         st.mem (sepScrBase n + sepNodes n * sepNodes n + (v.1 + 2)) < sepNodes n ∧
         st.mem (sepScrBase n + sepNodes n * sepNodes n + (v.1 + n + 2)) = sepNodes n
      then 1 else 0) ∧
    (∀ v : Fin n, st'.mem (sepSideBase n + v.1) =
      if st.mem (sepScrBase n + sepNodes n * sepNodes n + (v.1 + n + 2)) < sepNodes n
      then 1 else 0) := by
  have h := iterate_invariant_of sepExtractStep n
    (fun rem (k : ℕ) t => k + rem = n ∧
      (∀ a < sepOutBase n, t.mem a = st.mem a) ∧
      (∀ v : Fin n, v.1 < k → t.mem (sepOutBase n + v.1) =
        if st.mem (2 + v.1) = 0 ∧
           st.mem (sepScrBase n + sepNodes n * sepNodes n + (v.1 + 2)) < sepNodes n ∧
           st.mem (sepScrBase n + sepNodes n * sepNodes n + (v.1 + n + 2)) = sepNodes n
        then 1 else 0) ∧
      (∀ v : Fin n, v.1 < k → t.mem (sepSideBase n + v.1) =
        if st.mem (sepScrBase n + sepNodes n * sepNodes n + (v.1 + n + 2)) < sepNodes n
        then 1 else 0))
    (fun rem k t ⟨hsum, hlo, hout, hside⟩ => by
      have hz : t.mem (2 + k) = st.mem (2 + k) := hlo _ (by sep_omega)
      have hdin : t.mem (sepScrBase n + sepNodes n * sepNodes n + (k + 2)) =
          st.mem (sepScrBase n + sepNodes n * sepNodes n + (k + 2)) := hlo _ (by sep_omega)
      have hdout : t.mem (sepScrBase n + sepNodes n * sepNodes n + (k + n + 2)) =
          st.mem (sepScrBase n + sepNodes n * sepNodes n + (k + n + 2)) := hlo _ (by sep_omega)
      unfold sepExtractStep
      rw [clientResult_bind_read, clientResult_bind_read, clientResult_bind_read,
        clientResult_bind_write, clientResult_bind_write, clientResult_pure,
        clientState_bind_read, clientState_bind_read, clientState_bind_read,
        clientState_bind_write, clientState_bind_write, clientState_pure]
      dsimp only
      refine ⟨by omega, fun a ha => ?_, fun v hv => ?_, fun v hv => ?_⟩
      · rw [Function.update_of_ne (by dsimp only [sepSideBase]; omega),
          Function.update_of_ne (by omega)]
        exact hlo a ha
      · rw [Function.update_of_ne (by have := v.2; dsimp only [sepSideBase]; omega)]
        by_cases hvk : v.1 = k
        · rw [hvk, Function.update_self, hz, hdin, hdout]
        · rw [Function.update_of_ne (by omega)]; exact hout v (by omega)
      · by_cases hvk : v.1 = k
        · rw [hvk, Function.update_self, hdout]
        · rw [Function.update_of_ne (by omega),
            Function.update_of_ne (by dsimp only [sepSideBase]; omega)]
          exact hside v (by omega))
    (n := n) (a := 0) (s := st)
    ⟨Nat.zero_add _, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _)⟩
  exact ⟨fun v => h.2.2.1 v (by omega), fun v => h.2.2.2 v (by omega)⟩

/-- **Minimum vertex separator by vertex splitting on the Word-RAM:** one uniform flat program over
`Basis.exact` that, on `encodeSepInput G Z A B` for any `G : SimpleGraph (Fin n)` and `Z A B :
Vector Bool n`, halts within `C * (n + 1) ^ 5` instructions at every word width fitting
`ekBound (n + n + 2) (n + 1)`. It returns the minimum separator size `out.sep.length`, stores the
`0`/`1` separator indicator at `sepOutAddr`, and stores the side labelling certificate `out.side` at
`sepSideAddr`. -/
theorem exists_minSeparator_program :
    ∃ (R C pc : ℕ), 0 < C ∧ ∃ prog : Program .exact R,
      ∀ {n w : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (Z A B : Vector Bool n),
        Fits w (ekBound (n + n + 2) (n + 1)) →
        ∃ (y : Data R) (steps res : ℕ) (out : SeparatorOutput n),
          Runs w prog (State.init (encodeSepInput G Z A B)) ⟨pc, y⟩ steps ∧
          step w prog ⟨pc, y⟩ = .halt res ∧
          steps + 1 ≤ C * (n + 1) ^ 5 ∧
          out.sep.Nodup ∧
          (∀ v ∈ out.sep, vget Z v = false) ∧
          G.IsSeparator {v | vget A v = true} {v | vget B v = true}
            ({v | vget Z v = true} ∪ {v | v ∈ out.sep}) ∧
          (∀ Y : Finset (Fin n),
            G.IsSeparator {v | vget A v = true} {v | vget B v = true}
              ({v | vget Z v = true} ∪ ↑Y) → out.sep.length ≤ Y.card) ∧
          (∀ {u v : Fin n}, G.Adj u v → vget Z u = false → vget Z v = false →
            u ∉ out.sep → v ∉ out.sep → vget out.side u = vget out.side v) ∧
          (∀ {v : Fin n}, vget A v = true → vget Z v = false → v ∉ out.sep →
            vget out.side v = true) ∧
          (∀ {v : Fin n}, vget B v = true → vget out.side v = false) ∧
          res = out.sep.length ∧
          (∀ v : Fin n, y.mem (sepOutAddr n v.1) = if v ∈ out.sep then 1 else 0) ∧
          (∀ v : Fin n, y.mem (sepSideAddr n v.1) = if vget out.side v then 1 else 0) := by
  obtain ⟨R, C₀, pc, prog, _, _, hprog⟩ :=
    sepProg_realizes.exists_standard_init_program_state_from_words 0
  refine ⟨R, 5204 * C₀ + 2, pc, by omega, prog, ?_⟩
  intro n w G _ Z A B hwB
  have hw : Fits w (sepWorkspace n) := hwB.of_le (by dsimp only [sepWorkspace, ekBound]; nlinarith)
  set st := Memory.State.init (encodeSepInput G Z A B)
  have hfr : st.frontier = 2 + 3 * n + n * n := by
    simp only [st, Memory.State.init, length_encodeSepInput]; omega
  have h1 : st.mem 1 = n := by simp [st, Memory.State.init, encodeSepInput]
  have hlen : Fits w ((encodeSepInput G Z A B).length + 1) := hw.of_le (by
    rw [length_encodeSepInput]; dsimp only [sepWorkspace]; omega)
  have hwf : Memory.WellFormed w st :=
    Memory.wellFormed_init (inputFits_encodeSepInput G Z A B hw) hlen
  have hvh : (Memory.spec w).ValidHistory st ((Memory.spec w).clientHistory st (sepProg ())) := by
    unfold sepProg
    refine validHistory_read_bind (by omega) ?_
    rw [h1]
    exact validHistory_sepMain hwf hfr hw hwB
  obtain ⟨y, steps, hruns, hhalt, hmem, _, hbound⟩ :=
    hprog w () (encodeSepInput G Z A B) (fun j => Fin.elim0 j) (Nat.zero_le _) hlen
      (inputFits_encodeSepInput G Z A B hw) ⟨by rw [h1]; exact hw, by rw [h1]; exact hwB⟩ hvh
  rw [clientState_width w (sepProg ())] at hmem
  rw [clientResult_width w (sepProg ())] at hhalt
  set st0 := (Memory.spec 0).clientState st (Memory.alloc (sepScratch n))
  have hlo0 : ∀ a < sepMatBase n, st0.mem a = st.mem a := fun a ha =>
    Memory.mem_step_of_lt_frontier st (.alloc (sepScratch n))
      (by rw [hfr]; dsimp only [sepMatBase] at ha; omega) (by simp)
  have hZ0 : ∀ v : Fin n, st0.mem (2 + v.1) = if vget Z v then 1 else 0 := fun v => by
    rw [hlo0 _ (by have := v.2; dsimp only [sepMatBase]; omega)]; exact sepInit_mem_Z G Z A B v
  have hA0 : ∀ v : Fin n, st0.mem (2 + n + v.1) = if vget A v then 1 else 0 := fun v => by
    rw [hlo0 _ (by have := v.2; dsimp only [sepMatBase]; omega)]; exact sepInit_mem_A G Z A B v
  have hB0 : ∀ v : Fin n, st0.mem (2 + 2 * n + v.1) = if vget B v then 1 else 0 := fun v => by
    rw [hlo0 _ (by have := v.2; dsimp only [sepMatBase]; omega)]; exact sepInit_mem_B G Z A B v
  have hG0 : ∀ u v : Fin n, st0.mem (2 + 3 * n + u.1 * n + v.1) = if G.Adj u v then 1 else 0 := by
    intro u v
    have hlt := List.mul_add_lt_sq u.2 v.2
    rw [hlo0 _ (by dsimp only [sepMatBase]; omega)]; exact sepInit_mem_edge G Z A B u v
  obtain ⟨hlo3, hmat3⟩ := sepBuild_spec G Z A B hZ0 hA0 hB0 hG0
  set st1 := (Memory.spec 0).clientState st0
    (fillRange ((sepMatBase n, 0), sepNodes n * sepNodes n))
  set st2 := (Memory.spec 0).clientState st1 (iterate sepVertStep n n 0)
  set st3 := (Memory.spec 0).clientState st2 (iterate sepEdgeOuter n n 0)
  set NFin := (vertexSplitNetwork G Z A B).reindex (SplitNode.equivFin n)
  have hst_ne : NFin.s ≠ NFin.t :=
    (SplitNode.equivFin n).injective.ne (by simp [vertexSplitNetwork])
  have hcap_le : ∀ x y : Fin (sepNodes n), NFin.cap x y ≤ n + 1 := fun x y => by
    change vertexSplitCap G Z A B ((SplitNode.equivFin n).symm x)
      ((SplitNode.equivFin n).symm y) ≤ n + 1
    cases (SplitNode.equivFin n).symm x <;> cases (SplitNode.equivFin n).symm y <;>
      simp only [vertexSplitCap] <;> first | omega | (split_ifs <;> omega)
  have hEk := ekProg_flow_spec (mb := sepMatBase n) (sb := sepScrBase n) (B := n + 1)
    NFin hst_ne hcap_le (le_refl _) hmat3
  have hs0 : NFin.s.1 = 0 := rfl
  have ht1 : NFin.t.1 = 1 := rfl
  rw [hs0, ht1] at hEk
  obtain ⟨hEk_frame, _, _, hdist_le, _, hminFin, _, _, hres_ek⟩ := hEk
  set st4 := (Memory.spec 0).clientState st3
    (ekProg (⟨sepNodes n, sepMatBase n, sepScrBase n, n + 1⟩, (0, 1)))
  set CFin : Finset (Fin (sepNodes n)) :=
    Finset.univ.filter fun x =>
      st4.mem (distAddr ⟨sepNodes n, sepMatBase n, sepScrBase n, n + 1⟩ x.1) < sepNodes n
  set S : Finset (SplitNode n) := Network.cutOfReindex (SplitNode.equivFin n) CFin
  have hS_min : (vertexSplitNetwork G Z A B).IsMinCut S :=
    Network.isMinCut_cutOfReindex (SplitNode.equivFin n) hminFin
  set out := separatorOfCut Z S
  obtain ⟨hOut_mem, hSide_mem⟩ := sepExtract_spec (n := n) st4
  set st5 := (Memory.spec 0).clientState st4 (iterate sepExtractStep n n 0)
  have hst_prog : (Memory.spec 0).clientState st (sepProg ()) = st5 := by
    unfold sepProg; rw [clientState_bind_read, h1]
    unfold sepMain; dsimp only
    rw [clientState_bind, clientState_bind, clientState_bind, clientState_bind,
      clientState_bind, clientState_bind, clientState_pure]
  have hres_prog : (Memory.spec 0).clientResult st (sepProg ()) =
      (Memory.spec 0).clientResult st3
        (ekProg (⟨sepNodes n, sepMatBase n, sepScrBase n, n + 1⟩, (0, 1))) := by
    unfold sepProg; rw [clientResult_bind_read, h1]
    unfold sepMain; dsimp only
    rw [clientResult_bind, clientResult_bind, clientResult_bind, clientResult_bind,
      clientResult_bind, clientResult_bind, clientResult_pure]
  have hymem : y.mem = st5.mem := by
    rw [← hst_prog]; exact congrArg Memory.State.mem hmem
  have hmc : memoryCost (sepProg ()) st ≤ 5202 * (n + 1) ^ 5 := by
    unfold sepProg
    rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read, h1]
    have h1p : 1 ≤ (n + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
    have := memoryCost_sepMain_le n st
    omega
  have hp : 1 ≤ (n + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  refine ⟨y, steps, (Memory.spec 0).clientResult st (sepProg ()), out, hruns, hhalt, ?_,
    separatorOfCut_nodup_sep Z S,
    fun v hv => separatorOfCut_vget_eq_false_of_mem_sep hv,
    separatorOfCut_isSeparator hS_min,
    fun Y hY => separatorOfCut_length_sep_le hS_min hY,
    fun huv hu hv hus hvs => separatorOfCut_side_eq_of_adj hS_min huv hu hv hus hvs,
    fun hA hZ hvs => separatorOfCut_side_eq_true hS_min hA hZ hvs,
    fun hB => separatorOfCut_side_eq_false hS_min hB, ?_, ?_, ?_⟩
  · calc steps + 1
        ≤ C₀ * (memoryCost (sepProg ()) st + 0 + 1) + 1 := hbound
      _ ≤ C₀ * (5202 * (n + 1) ^ 5 + 1) + 1 :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 1
      _ ≤ (5204 * C₀ + 2) * (n + 1) ^ 5 := by nlinarith
  · rw [hres_prog, hres_ek, ← Network.cutCapacity_cutOfReindex (SplitNode.equivFin n),
      separatorOfCut_length_sep_eq_cutCapacity hS_min]
  · intro v
    rw [hymem]
    have haddr : sepOutAddr n v.1 = sepOutBase n + v.1 := by
      dsimp only [sepOutAddr, sepOutBase, sepScrBase, sepMatBase, sepNodes, ekScratch]; ring
    rw [haddr, hOut_mem v]
    have hZ4 : st4.mem (2 + v.1) = if vget Z v then 1 else 0 := by
      rw [hEk_frame _ (Or.inl (by have := v.2; sep_omega)),
        hlo3 _ (by have := v.2; dsimp only [sepMatBase]; omega)]
      exact hZ0 v
    have hin_iff : st4.mem (sepScrBase n + sepNodes n * sepNodes n + (v.1 + 2)) < sepNodes n ↔
        SplitNode.inV v ∈ S := by
      have : (SplitNode.equivFin n (.inV v)).1 = v.1 + 2 := rfl
      rw [← this]
      simp [S, Network.cutOfReindex, CFin, distAddr]
    have hout_iff : st4.mem (sepScrBase n + sepNodes n * sepNodes n + (v.1 + n + 2)) = sepNodes n ↔
        SplitNode.outV v ∉ S := by
      have hle := hdist_le (SplitNode.equivFin n (.outV v))
      have : (SplitNode.equivFin n (.outV v)).1 = v.1 + n + 2 := rfl
      rw [this] at hle
      dsimp only [distAddr] at hle
      have hlt_iff : st4.mem (sepScrBase n + sepNodes n * sepNodes n + (v.1 + n + 2)) <
          sepNodes n ↔ SplitNode.outV v ∈ S := by
        rw [← this]; simp [S, Network.cutOfReindex, CFin, distAddr]
      rw [← hlt_iff]
      dsimp only [sepNodes] at hle ⊢
      omega
    have hZ_iff : st4.mem (2 + v.1) = 0 ↔ vget Z v = false := by
      rw [hZ4]; cases vget Z v <;> simp
    have hmem_sep : v ∈ out.sep ↔
        vget Z v = false ∧ SplitNode.inV v ∈ S ∧ SplitNode.outV v ∉ S := by
      simp only [out, separatorOfCut, List.mem_filter, List.mem_finRange, true_and,
        Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not, and_assoc]
    exact if_congr ((and_congr hZ_iff (and_congr hin_iff hout_iff)).trans hmem_sep.symm) rfl rfl
  · intro v
    rw [hymem]
    have haddr : sepSideAddr n v.1 = sepSideBase n + v.1 := by
      dsimp only [sepSideAddr, sepSideBase, sepOutBase, sepScrBase, sepMatBase, sepNodes,
        ekScratch]
      ring
    rw [haddr, hSide_mem v]
    have hout_iff : st4.mem (sepScrBase n + sepNodes n * sepNodes n + (v.1 + n + 2)) <
        sepNodes n ↔ vget out.side v = true := by
      have : (SplitNode.equivFin n (.outV v)).1 = v.1 + n + 2 := rfl
      rw [← this]
      simp [out, separatorOfCut, vget, S, Network.cutOfReindex, CFin, distAddr]
    exact if_congr hout_iff rfl rfl

end UniformVertexSeparator

end Cslib.Algorithms.WordRAM.EdmondsKarp
