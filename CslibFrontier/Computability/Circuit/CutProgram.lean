/-
Copyright (c) 2026 Uladzislau Artsemyeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uladzislau Artsemyeu
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Depth
public import CslibFrontier.Computability.Circuit.Program
public import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Sort

/-!
# Replacing circuit gates with inputs

Replacing cut gates with extra inputs carrying their original values preserves the full wire
trace. The rebuilt program preserves fan-in bounds and realizes the residual wire depths.

## Main definitions

* `Cslib.Circuits.Program.residualDepths`: gate depths with cut gates at depth `0`.
* `Cslib.Circuits.Program.residualWireDepths`: the corresponding depths of all wires.

## Main results

* `Cslib.Circuits.Program.residualWireDepths_empty`: the empty cut recovers the original depths.
* `Cslib.Circuits.Program.residualWireDepths_gate`: the gate recurrence for residual depths.
* `Cslib.Circuits.Program.exists_cutProgram`: a program with cut gates replaced by extra inputs,
  with the same bounded fan-in and wire trace and with the specified residual depths.
-/

public section

namespace Cslib.Circuits

section ResidualDepths

variable {σ : Signature} {n g : ℕ}

/-- Gate depths of `p` after turning every gate in `cut` into a depth-`0` input. -/
@[expose] def Program.residualDepths : {g : ℕ} → Program σ n g → Finset (Fin g) → Fin g → ℕ
  | _, .empty, _ => Fin.elim0
  | _, .gate p line, cut =>
    let priorCut : Finset (Fin _) := Finset.univ.filter fun j => j.castSucc ∈ cut
    let priorWireDepths := Wire.elim (fun _ => 0) (p.residualDepths priorCut)
    let lastDepth := if Fin.last _ ∈ cut then 0 else line.depth priorWireDepths
    Fin.lastCases lastDepth (p.residualDepths priorCut)

/-- Wire depths of `p` after turning every gate in `cut` into a depth-`0` input. -/
@[expose] def Program.residualWireDepths (p : Program σ n g) (cut : Finset (Fin g)) :
    Wire n g → ℕ :=
  Wire.elim (fun _ => 0) (p.residualDepths cut)

/-- Every input wire has residual depth `0`. -/
@[simp] theorem Program.residualWireDepths_input (p : Program σ n g) (cut : Finset (Fin g))
    (i : Fin n) : p.residualWireDepths cut (.input i) = 0 :=
  rfl

/-- Every gate wire's residual depth is given by `Program.residualDepths`. -/
@[simp] theorem Program.residualWireDepths_gateWire (p : Program σ n g) (cut : Finset (Fin g))
    (j : Fin g) : p.residualWireDepths cut (.gate j) = p.residualDepths cut j :=
  rfl

private theorem Program.residualWireDepths_gate_castSucc (p : Program σ n g)
    (line : Line σ n g) (cut : Finset (Fin (g + 1))) (w : Wire n g) :
    (p.gate line).residualWireDepths cut w.castSucc =
      p.residualWireDepths (Finset.univ.filter fun j => j.castSucc ∈ cut) w := by
  cases w <;> simp [Program.residualWireDepths, Program.residualDepths]

/-- Gate equation for `Program.residualWireDepths`: cut gates have residual depth `0`, while
uncut gates evaluate `Line.depth` over `residualWireDepths` (charging `1` to `0`-ary gates). -/
theorem Program.residualWireDepths_gate (p : Program σ n g) (cut : Finset (Fin g)) (j : Fin g) :
    p.residualWireDepths cut (.gate j) =
      if j ∈ cut then 0 else (p.lines j).depth (p.residualWireDepths cut) := by
  induction p with
  | empty => exact j.elim0
  | @gate g p line ih =>
    let priorCut : Finset (Fin g) := Finset.univ.filter fun i => i.castSucc ∈ cut
    have hWires : (fun w => (p.gate line).residualWireDepths cut (Wire.Renaming.castSucc w)) =
        p.residualWireDepths priorCut :=
      funext fun w => p.residualWireDepths_gate_castSucc line cut w
    induction j using Fin.lastCases with
    | last =>
      have hLast : (p.gate line).residualWireDepths cut (.gate (Fin.last g)) =
          if Fin.last g ∈ cut then 0 else line.depth (p.residualWireDepths priorCut) := by
        simp [Program.residualWireDepths, Program.residualDepths, priorCut]
      rw [Program.lines_gate_last, hLast]
      congr 1
      exact congrArg line.depth hWires.symm
    | cast k =>
      have hk : k ∈ priorCut ↔ k.castSucc ∈ cut := by
        simp [priorCut]
      have hCast : (p.gate line).residualWireDepths cut (.gate k.castSucc) =
          p.residualWireDepths priorCut (.gate k) := by
        simpa using p.residualWireDepths_gate_castSucc line cut (.gate k)
      rw [Program.lines_gate_castSucc, hCast, ih priorCut k]
      simp only [hk]
      congr 1
      exact congrArg (p.lines k).depth hWires.symm

/-- With an empty cut, `residualWireDepths` agrees identically with `Program.wireDepths`. -/
@[simp] theorem Program.residualWireDepths_empty (p : Program σ n g) :
    p.residualWireDepths ∅ = p.wireDepths := by
  funext w
  refine p.wire_induction (P := fun w => p.residualWireDepths ∅ w = p.wireDepths w)
    (fun _ => rfl) (fun k ih => ?_) w
  have hNot : k ∉ (∅ : Finset (Fin g)) := Finset.notMem_empty k
  rw [p.residualWireDepths_gate, ite_eq_right hNot, Program.wireDepths_gateWire,
    p.depths_eq_depth_lines]
  dsimp only [Line.depth]
  rw [Fin.foldl_max_eq_max_sup, Fin.foldl_max_eq_max_sup]
  exact congrArg (fun d => max 0 d + 1) (Finset.sup_congr rfl fun a _ => ih a)

end ResidualDepths

section CutProgram

variable {σ : Signature} {n m g : ℕ}

/-- Lift wires from `n` inputs to `n + m` inputs, routing old gates through `gates`. -/
private def liftWire {s s' : ℕ} (gates : Fin s → Wire (n + m) s') : Wire n s → Wire (n + m) s' :=
  Wire.elim (fun i => Wire.input (Fin.castAdd m i)) gates

private theorem liftWire_wireDepths {s s' : ℕ} {p : Program σ n s} {q : Program σ (n + m) s'}
    {cut : Finset (Fin s)} {gates : Fin s → Wire (n + m) s'}
    (hgates : ∀ j, q.wireDepths (gates j) = p.residualWireDepths cut (.gate j))
    (w : Wire n s) :
    q.wireDepths (liftWire gates w) = p.residualWireDepths cut w := by
  cases w with
  | input i => simp [liftWire]
  | gate j => exact hgates j

private theorem liftWire_trace {s s' : ℕ} {U : Type*} {I : Interpretation σ U} {x : Fin n → U}
    {y : Fin m → U} {p : Program σ n s} {q : Program σ (n + m) s'}
    {gates : Fin s → Wire (n + m) s'}
    (hgates : ∀ j, q.trace I (Fin.append x y) (gates j) = p.eval I x j)
    (w : Wire n s) :
    q.trace I (Fin.append x y) (liftWire gates w) = p.trace I x w := by
  cases w with
  | input i => simp [liftWire]
  | gate j => exact hgates j

private theorem exists_cut_program_aux :
    ∀ {s : ℕ} (p : Program σ n s) (cutIdx : Fin s → Option (Fin m)),
      ∃ (s' : ℕ) (q : Program σ (n + m) s') (gates : Fin s → Wire (n + m) s'),
        s' + (Finset.univ.filter fun j => (cutIdx j).isSome).card = s ∧
        (∀ r, p.FanInAtMost r → q.FanInAtMost r) ∧
        (∀ j, q.wireDepths (gates j) =
          p.residualWireDepths (Finset.univ.filter fun j => (cutIdx j).isSome) (.gate j)) ∧
        (∀ k, ∃ j, gates j = .gate k) ∧
        (∀ {U : Type*} (I : Interpretation σ U) (x : Fin n → U) (y : Fin m → U),
          (∀ j k, cutIdx j = some k → y k = p.eval I x j) →
          ∀ j, q.trace I (Fin.append x y) (gates j) = p.eval I x j)
  | 0, .empty, _ =>
    ⟨0, .empty, Fin.elim0, by simp, fun _ _ => trivial, fun j => j.elim0,
      fun k => k.elim0, fun _ _ _ _ j => j.elim0⟩
  | s + 1, .gate p line, cutIdx => by
    let priorIdx : Fin s → Option (Fin m) := fun j => cutIdx j.castSucc
    let cut : Finset (Fin (s + 1)) := Finset.univ.filter fun j => (cutIdx j).isSome
    let priorCut : Finset (Fin s) := Finset.univ.filter fun j => (priorIdx j).isSome
    have hPriorEq : priorCut = Finset.univ.filter fun j => j.castSucc ∈ cut := by
      ext j
      simp [priorCut, cut, priorIdx]
    obtain ⟨s', q, gates, hCard, hFan, hDepth, hSurj, hTrace⟩ :=
      exists_cut_program_aux p priorIdx
    change s' + priorCut.card = s at hCard
    have hSplit : cut.card = priorCut.card + if (cutIdx (Fin.last s)).isSome then 1 else 0 := by
      simp only [cut, priorCut, priorIdx, Finset.card_filter, Fin.sum_univ_castSucc]
    have hResCast (j : Fin s) :
        (p.gate line).residualWireDepths cut (.gate j.castSucc) =
          p.residualWireDepths priorCut (.gate j) := by
      simpa [← hPriorEq] using p.residualWireDepths_gate_castSucc line cut (.gate j)
    cases hLast : cutIdx (Fin.last s) with
    | some k =>
      have hLastMem : Fin.last s ∈ cut := by simp [cut, hLast]
      refine ⟨s', q, Fin.lastCases (.input (Fin.natAdd n k)) gates, ?_, ?_, ?_, ?_, ?_⟩
      · change s' + cut.card = s + 1
        rw [hSplit]
        simp [hLast]
        omega
      · intro r hr
        exact hFan r hr.1
      · intro j
        refine Fin.lastCases ?_ (fun j' => ?_) j
        · dsimp only
          rw [Fin.lastCases_last, Program.wireDepths_input,
            (p.gate line).residualWireDepths_gate, ite_eq_left hLastMem]
        · dsimp only
          rw [Fin.lastCases_castSucc, hResCast]
          exact hDepth j'
      · intro k'
        obtain ⟨j, hj⟩ := hSurj k'
        exact ⟨j.castSucc, by simp [hj]⟩
      · intro U I x y hy j
        refine Fin.lastCases ?_ (fun j' => ?_) j
        · simp [hy (Fin.last s) k hLast]
        · dsimp only
          rw [Fin.lastCases_castSucc, Program.eval_gate_castSucc]
          exact hTrace I x y (fun j₀ k₀ hj₀ => by
            simpa [Program.eval_gate_castSucc] using hy j₀.castSucc k₀ hj₀) j'
    | none =>
      have hLastNotMem : Fin.last s ∉ cut := by simp [cut, hLast]
      let line' := line.mapWires (liftWire gates)
      refine ⟨s' + 1, q.gate line', Fin.lastCases (.gate (Fin.last s'))
        (fun j => (gates j).castSucc), ?_, ?_, ?_, ?_, ?_⟩
      · change s' + 1 + cut.card = s + 1
        rw [hSplit]
        simp [hLast]
        omega
      · intro r hr
        exact ⟨hFan r hr.1, hr.2⟩
      · intro j
        refine Fin.lastCases ?_ (fun j' => ?_) j
        · dsimp only
          rw [Fin.lastCases_last, Program.wireDepths_gateWire, Program.depths_gate_last,
            (p.gate line).residualWireDepths_gate, ite_eq_right hLastNotMem,
            Program.lines_gate_last]
          have hLift : (fun w => q.wireDepths (liftWire gates w)) =
              fun w => (p.gate line).residualWireDepths cut (Wire.Renaming.castSucc w) := by
            funext w
            rw [liftWire_wireDepths (hDepth ·), Wire.Renaming.castSucc_apply,
              p.residualWireDepths_gate_castSucc line cut w, ← hPriorEq]
          exact congrArg line.depth hLift
        · dsimp only
          rw [Fin.lastCases_castSucc, Program.wireDepths_gate_castSucc, hResCast]
          exact hDepth j'
      · intro k'
        refine Fin.lastCases ⟨Fin.last s, by simp⟩ (fun k₀ => ?_) k'
        obtain ⟨j, hj⟩ := hSurj k₀
        exact ⟨j.castSucc, by simp [hj]⟩
      · intro U I x y hy j
        refine Fin.lastCases ?_ (fun j' => ?_) j
        · dsimp only
          rw [Fin.lastCases_last, Program.trace_gate_last, Program.eval_gate_last]
          exact line.eval_mapWires (liftWire gates) I x (Fin.append x y)
            (p.eval I x) (q.eval I (Fin.append x y))
            (liftWire_trace (hTrace I x y fun j₀ k₀ hj₀ => by
              simpa [Program.eval_gate_castSucc] using hy j₀.castSucc k₀ hj₀))
        · dsimp only
          rw [Fin.lastCases_castSucc, Program.trace_gate_castSucc, Program.eval_gate_castSucc]
          exact hTrace I x y (fun j₀ k₀ hj₀ => by
            simpa [Program.eval_gate_castSucc] using hy j₀.castSucc k₀ hj₀) j'

/-- Turning the gates in `cut` into `cut.card` extra inputs yields a program of `g - cut.card`
gates with the same bounded fan-in, wire depths equal to `p.residualWireDepths cut`, and identical
traces on `Fin.append x (cut gate values)`. -/
theorem Program.exists_cutProgram (p : Program σ n g) (cut : Finset (Fin g)) :
    ∃ (q : Program σ (n + cut.card) (g - cut.card))
      (wireMap : Wire n g → Wire (n + cut.card) (g - cut.card))
      (cutGate : Fin cut.card → Fin g),
      (∀ i, cutGate i ∈ cut) ∧
      (∀ r, p.FanInAtMost r → q.FanInAtMost r) ∧
      (∀ w, q.wireDepths (wireMap w) = p.residualWireDepths cut w) ∧
      (∀ k, ∃ j, wireMap (.gate j) = .gate k) ∧
      (∀ {U : Type*} (I : Interpretation σ U) (x : Fin n → U) (w : Wire n g),
        q.trace I (Fin.append x (fun i => p.eval I x (cutGate i))) (wireMap w) =
          p.trace I x w) := by
  let e : Fin cut.card ≃o cut := cut.orderIsoOfFin rfl
  let cutGate : Fin cut.card → Fin g := fun i => (e i).val
  let cutIdx : Fin g → Option (Fin cut.card) := fun j =>
    if hj : j ∈ cut then some (e.symm ⟨j, hj⟩) else none
  have hFilter : (Finset.univ.filter fun j => (cutIdx j).isSome) = cut := by
    ext j
    simp only [cutIdx, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hj : j ∈ cut <;> simp [hj]
  obtain ⟨s', q, gates, hCard, hFan, hDepth, hSurj, hTrace⟩ := exists_cut_program_aux p cutIdx
  rw [hFilter] at hCard hDepth
  have hCutLe : cut.card ≤ g := (Finset.card_le_univ cut).trans_eq (Fintype.card_fin g)
  obtain rfl : s' = g - cut.card := by omega
  refine ⟨q, liftWire gates, cutGate, fun i => (e i).property, hFan,
    liftWire_wireDepths hDepth, hSurj, fun I x w => ?_⟩
  refine liftWire_trace (hTrace I x (fun i => p.eval I x (cutGate i)) ?_) w
  intro j k hjk
  by_cases hj : j ∈ cut
  · simp only [cutIdx, hj, ↓reduceDIte, Option.some.injEq] at hjk
    have heq : cutGate k = j := by
      dsimp [cutGate]
      rw [← hjk, e.apply_symm_apply]
    rw [heq]
  · simp [cutIdx, hj] at hjk

end CutProgram

end Cslib.Circuits
