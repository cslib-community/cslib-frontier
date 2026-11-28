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
import CslibFrontier.Foundations.Combinatorics.DepthReduction
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Ring

/-!
# Valiant depth reduction for bounded-fan-in programs

Specializes `Cslib.IsGrading.exists_sdiff`
(`CslibFrontier.Foundations.Combinatorics.DepthReduction`)
[Valiant1977; Jukna2012, Lemma 1.4; AroraBarak09, Lemma 13.14; Lokam2009, Lemma 2.2]
to
arbitrary bounded-fan-in straight-line programs `p : Program σ n g` (`p.FanInAtMost r`). For any
`t ≤ k` and `p.depth < 2 ^ k`, cutting at most `r * t * g / k` gates leaves every wire with
residual gate depth at most `2 ^ (k - t)` (`Program.valiantDepthReduction`), and turning those
cut gates into extra inputs produces a fan-in-preserving cut program of depth at most `2 ^ (k - t)`
with the exact same wire trace (`Program.exists_cutProgram`, `Program.exists_depthReduced_program`).

## Main definitions

* `Cslib.Circuits.Program.residualDepths`: gate depths of `p` after resetting gates in `cut` to
  depth `0`.
* `Cslib.Circuits.Program.residualWireDepths`: wire depths of `p` after resetting gates in `cut`
  to depth `0`.

## Main results

* `Cslib.Circuits.Program.residualWireDepths_empty`: the empty cut recovers `p.wireDepths`.
* `Cslib.Circuits.Program.residualWireDepths_gate`: gate recurrence for `residualWireDepths`.
* `Cslib.Circuits.Program.exists_cutProgram`: turning any gate set `cut` into extra inputs
  preserves bounded fan-in, realizes `residualWireDepths cut` as wire depth, and preserves the
  semantic trace `Program.trace`.
* `Cslib.Circuits.Program.valiantDepthReduction`: cuts at most `r * t * g / k` gates so every wire
  has residual depth at most `2 ^ (k - t)`.
* `Cslib.Circuits.Program.exists_depthReduced_program`: combines `valiantDepthReduction` and
  `exists_cutProgram` into a fan-in-preserving program of depth at most `2 ^ (k - t)` on `m` extra
  cut-gate inputs (`m ≤ r * t * g / k`).

## References

* [L. G. Valiant, *Graph-Theoretic Arguments in Low-Level Complexity*][Valiant1977]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [S. V. Lokam, *Complexity Lower Bounds using Linear Algebra*][Lokam2009]
-/

@[expose] public section

namespace Cslib.Circuits

section ResidualDepths

variable {σ : Signature} {n g : ℕ}

/-- Gate depths of `p` after turning every gate in `cut` into a depth-`0` input. -/
def Program.residualDepths : {g : ℕ} → Program σ n g → Finset (Fin g) → Fin g → ℕ
  | _, .empty, _ => Fin.elim0
  | _, .gate p line, cut =>
    let priorCut : Finset (Fin _) := Finset.univ.filter fun j => j.castSucc ∈ cut
    let priorWireDepths := Wire.elim (fun _ => 0) (p.residualDepths priorCut)
    let lastDepth := if Fin.last _ ∈ cut then 0 else line.depth priorWireDepths
    Fin.lastCases lastDepth (p.residualDepths priorCut)

/-- Wire depths of `p` after turning every gate in `cut` into a depth-`0` input. -/
def Program.residualWireDepths (p : Program σ n g) (cut : Finset (Fin g)) : Wire n g → ℕ :=
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

section ValiantReduction

variable {σ : Signature} {n g : ℕ}

/-- **Valiant Depth-Reduction Lemma** ([Valiant1977]; [Jukna2012, Lemma 1.4];
[AroraBarak09, Lemma 13.14]; [Lokam2009, Lemma 2.2]), specialized from
`Cslib.IsGrading.exists_sdiff`
to bounded-fan-in straight-line programs: for `t ≤ k` and `p.depth < 2 ^ k`, cutting at most
`r * t * g / k` gates makes every wire's residual gate depth at most `2 ^ (k - t)`. -/
theorem Program.valiantDepthReduction (p : Program σ n g) {r k t : ℕ}
    (hr : p.FanInAtMost r) (ht : t ≤ k) (hdepth : p.depth < 2 ^ k) :
    ∃ cut : Finset (Fin g),
      cut.card ≤ r * t * g / k ∧
      ∀ w : Wire n g, p.residualWireDepths cut w ≤ 2 ^ (k - t) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · obtain rfl : t = 0 := Nat.eq_zero_of_le_zero ht
    refine ⟨∅, by simp, fun w => ?_⟩
    rw [p.residualWireDepths_empty, Nat.sub_zero, pow_zero]
    have hlt := (p.wireDepths_le_depth w).trans_lt hdepth
    omega
  · let E : Finset (Wire n g × Wire n g) :=
      Finset.univ.biUnion fun j : Fin g =>
        Finset.univ.image fun a => ((p.lines j).wires a, Wire.gate j)
    have hEcard : E.card ≤ r * g := by
      calc E.card
          ≤ ∑ j : Fin g, (Finset.univ.image fun a =>
              ((p.lines j).wires a, (Wire.gate j : Wire n g))).card := Finset.card_biUnion_le
        _ ≤ ∑ _j : Fin g, r := Finset.sum_le_sum fun j _ =>
            Finset.card_image_le.trans ((Finset.card_univ.trans (Fintype.card_fin _)).trans_le
              (Program.fanInAtMost_iff.1 hr j))
        _ = r * g := by simp [mul_comm]
    have hgrade : Cslib.IsGrading E (2 ^ k) p.wireDepths := by
      refine ⟨fun w => (p.wireDepths_le_depth w).trans_lt hdepth, fun e he => ?_⟩
      simp only [E, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at he
      obtain ⟨j, a, -, rfl⟩ := he
      exact p.wireDepths_lines_lt j a
    obtain ⟨F, -, hFcard, g', hg'⟩ := hgrade.exists_sdiff ht
    let cut : Finset (Fin g) := Finset.univ.filter fun j : Fin g => Wire.gate j ∈ F.image Prod.snd
    have hcutF : cut.card ≤ F.card := by
      have hInj : cut.card ≤ (F.image Prod.snd).card := by
        apply Finset.card_le_card_of_injOn Wire.gate
        · intro j hj
          exact (Finset.mem_filter.1 hj).2
        · intro j₁ _ j₂ _ h
          exact Wire.gate.inj h
      exact hInj.trans Finset.card_image_le
    refine ⟨cut, ?_, fun w => ?_⟩
    · rw [Nat.le_div_iff_mul_le hk]
      calc cut.card * k
          ≤ F.card * k := Nat.mul_le_mul_right k hcutF
        _ = k * F.card := mul_comm _ _
        _ ≤ t * E.card := hFcard
        _ ≤ t * (r * g) := Nat.mul_le_mul_left t hEcard
        _ = r * t * g := by ring
    · have hResLe : ∀ u : Wire n g, p.residualWireDepths cut u ≤ g' u + 1 := by
        intro u
        refine p.wire_induction (P := fun u => p.residualWireDepths cut u ≤ g' u + 1)
          (fun _ => by simp) (fun j ih => ?_) u
        rw [p.residualWireDepths_gate]
        by_cases hj : j ∈ cut
        · simp [hj]
        · rw [ite_eq_right hj, Line.depth_le_add_one_iff]
          intro a
          have hmem : ((p.lines j).wires a, Wire.gate j) ∈ E :=
            Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _,
              Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩⟩
          have hnotF : ((p.lines j).wires a, Wire.gate j) ∉ F := fun hF =>
            hj (Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.mem_image.2 ⟨_, hF, rfl⟩⟩)
          have hlt := hg'.2 _ (Finset.mem_sdiff.2 ⟨hmem, hnotF⟩)
          dsimp only at hlt
          have := ih a
          omega
      have hg'lt := hg'.1 w
      have := hResLe w
      omega

/-- Every bounded-fan-in program `p` of depth `< 2 ^ k` admits `m ≤ r * t * g / k` cut gates
whose replacement by extra inputs yields a `FanInAtMost r` program of depth at most `2 ^ (k - t)`
computing the same wire trace. -/
theorem Program.exists_depthReduced_program (p : Program σ n g) {r k t : ℕ}
    (hr : p.FanInAtMost r) (ht : t ≤ k) (hdepth : p.depth < 2 ^ k) :
    ∃ (m : ℕ) (q : Program σ (n + m) (g - m))
      (wireMap : Wire n g → Wire (n + m) (g - m)) (cutGate : Fin m → Fin g),
      m ≤ r * t * g / k ∧
      q.FanInAtMost r ∧
      q.depth ≤ 2 ^ (k - t) ∧
      (∀ {U : Type*} (I : Interpretation σ U) (x : Fin n → U) (w : Wire n g),
        q.trace I (Fin.append x (fun i => p.eval I x (cutGate i))) (wireMap w) =
          p.trace I x w) := by
  obtain ⟨cut, hCard, hRes⟩ := p.valiantDepthReduction hr ht hdepth
  obtain ⟨q, wireMap, cutGate, _, hFan, hDepth, hSurj, hTrace⟩ := p.exists_cutProgram cut
  refine ⟨cut.card, q, wireMap, cutGate, hCard, hFan r hr, ?_, hTrace⟩
  rw [Program.depth_le_iff]
  intro k'
  obtain ⟨j, hj⟩ := hSurj k'
  rw [← Program.wireDepths_gateWire, ← hj, hDepth]
  exact hRes (.gate j)

end ValiantReduction

end Cslib.Circuits
