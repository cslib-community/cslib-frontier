/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.Program
import CslibFrontier.Computability.WordRAM.MapOp
import CslibFrontier.Tactic.FinIndex

/-!
# Initialized flat programs with a fixed register layout

Choose the frontier, input bank and fresh scratch bank once, before every runtime width and
argument. Clients supply the same encoded-input, fit, domain and memory-history premises as
`Realizes.exists_init_program`, without proving register-placement conditions themselves.
The real `Data.init` prefix, native body and trailing halt are all charged. Its positive
next-free address must fit even for an empty input; this is not a width-zero initialization.

## Main definitions

* `Realization.stripRand`: replaces unreachable `.rand` instructions with no-op register copies so
  a deterministic `Program B r` satisfies `Program.IsRandFree`.

## Main results

* `Realization.isRandFree_stripRand`, `Realization.not_readsWidth_stripRand`,
  `Realization.step_stripRand_of_halt`, `Realization.runs_stripRand`: `stripRand` produces a
  rand-free program preserving `¬ReadsWidth`, halting steps, and deterministic `Runs`.
* `Realizes.exists_standard_init_program_state_from_words`: one flat program for independent
  raw memory and register arguments, related by their input prefix.
* `Realizes.exists_standard_basis_init_program_state_from_words`: standard-basis width-blind
  (`Program .standard r`, `¬prog.ReadsWidth`) translation of the same initialized flat program.
* `Realizes.exists_standard_init_program_state`: the argument-indexed specialization, retaining
  the exact whole-memory, frontier and all encoded result words at its fixed halting location.
* `Realizes.exists_standard_init_program`: the scalar `Executes` projection of that same run.

The observed coordinate is static, as in the existing scalar export. Zero-output Unit clients
continue to use the separate charged Unit-observation API.

## References

This is original infrastructure over the existing realization certificate, charged input prefix
and native `Code.program` compiler. It introduces no execution model or client language.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization

open Cslib.DataStructure

/-- Replace unreachable `.rand` instructions in `p` with no-op register copies so the resulting
flat program satisfies `Program.IsRandFree` while preserving all deterministic runs. -/
def stripRand {B : Basis} {r : ℕ} (p : Program B r) : Program B r :=
  p.map fun
    | .rand dst _ => .op (.copy dst dst)
    | i => i

/-- `stripRand p` contains no `.rand` instructions. -/
theorem isRandFree_stripRand {B : Basis} {r : ℕ} (p : Program B r) :
    (stripRand p).IsRandFree := by
  intro i hi
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
  cases j <;> trivial

/-- `stripRand` preserves width-blindness (`¬Program.ReadsWidth`). -/
theorem not_readsWidth_stripRand {B : Basis} {r : ℕ} {p : Program B r}
    (hp : ¬p.ReadsWidth) : ¬(stripRand p).ReadsWidth := by
  rintro ⟨i, hi, hrw⟩
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  cases j with
  | rand _ _ => exact hrw
  | _ => exact hp ⟨_, hj, hrw⟩

private theorem step_stripRand_of_ne_fault {B : Basis} {r w : ℕ} {p : Program B r}
    {s : State r} (hne : step w p s ≠ .fault) :
    step w (stripRand p) s = step w p s := by
  unfold step at hne ⊢
  rw [stripRand, List.getElem?_map]
  cases hp : p[s.pc]? with
  | none => simp [hp] at hne
  | some ins =>
    cases ins with
    | rand _ _ => simp [hp] at hne
    | _ => rfl

/-- Halting steps of `p` transfer unchanged to `stripRand p`. -/
theorem step_stripRand_of_halt {B : Basis} {r w v : ℕ} {p : Program B r} {s : State r}
    (h : step w p s = .halt v) : step w (stripRand p) s = .halt v := by
  rw [step_stripRand_of_ne_fault (by rw [h]; exact nofun), h]

/-- Deterministic `Runs` of `p` transfer unchanged to `stripRand p`. -/
theorem runs_stripRand {B : Basis} {r w : ℕ} {p : Program B r}
    {s t : State r} {m : ℕ} (h : Runs w p s t m) : Runs w (stripRand p) s t m := by
  induction h with
  | refl => exact .refl _
  | tail _ _ _ _ hstep ih =>
    unfold Next at hstep
    exact .tail _ _ _ _ ih ((step_stripRand_of_ne_fault (by rw [hstep]; exact nofun)).trans hstep)

private abbrev registers (k l n : ℕ) : ℕ := 1 + (k + (l + n + 1))

private def standardFrontier {k l n : ℕ} : Fin (registers k l n) :=
  ⟨0, by unfold registers; omega⟩

private def standardInput {k l n : ℕ} (i : Fin k) : Fin (registers k l n) :=
  Fin.natAdd 1 (Fin.castAdd (l + n + 1) i)

private def standardScratch {k l n : ℕ} (i : Fin (l + n + 1)) : Fin (registers k l n) :=
  Fin.natAdd 1 (Fin.natAdd k i)

private theorem standardPlacement (k l n : ℕ) :
    Function.Injective (standardInput (k := k) (l := l) (n := n)) ∧
    Function.Injective (standardScratch (k := k) (l := l) (n := n)) ∧
    (∀ i j, standardInput (l := l) (n := n) i ≠ standardScratch (k := k) j) ∧
    (∀ j, standardScratch (k := k) (l := l) (n := n) j ≠ standardFrontier) ∧
    (∀ i, standardInput (k := k) (l := l) (n := n) i ≠ standardFrontier) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> fin_index [standardInput, standardScratch, standardFrontier]

namespace Realizes

variable {k l : ℕ} {δ α : Type} {p : δ → Memory.Prog α}
  {input : δ ↪ (Fin k → ℕ)} {output : α ↪ (Fin l → ℕ)}
  {safe : ℕ → δ → Memory.State → Prop} {work : δ → Memory.State → ℕ}

/-- One statically laid-out flat program includes charged input installation and its halt.
The witnessed native state is the actual final state of the flat run, retaining the entire
source memory and frontier and every result coordinate. The raw input words vary independently
of the register-encoded argument: only their input prefix must agree. All witnesses precede
both kinds of runtime data. -/
theorem exists_standard_init_program_state_from_words
    (h : Realizes .exact p input output safe work) (i : Fin l) :
    ∃ r C pc : ℕ, ∃ prog : Program .exact r,
      ∃ frontier : Fin r, ∃ out : Fin l → Fin r,
      ∀ w d words, (∀ j : Fin k, words.getD j.val 0 = input d j) →
        k ≤ words.length → Fits w (words.length + 1) → InputFits w words →
        safe w d (Memory.State.init words) →
        (Memory.spec w).ValidHistory (Memory.State.init words)
          ((Memory.spec w).clientHistory (Memory.State.init words) (p d)) →
        ∃ y n, Runs w prog (State.init words) ⟨pc, y⟩ n ∧
          step w prog ⟨pc, y⟩ =
            .halt (output ((Memory.spec w).clientResult (Memory.State.init words) (p d)) i) ∧
          memoryState frontier y = (Memory.spec w).clientState (Memory.State.init words) (p d) ∧
          (∀ j, y.regs (out j) =
            output ((Memory.spec w).clientResult (Memory.State.init words) (p d)) j) ∧
          n + 1 ≤ C * (memoryCost (p d) (Memory.State.init words) +
            work d (Memory.State.init words) + 1) + 1 := by
  obtain ⟨n, C, emit, he⟩ := h
  let r := registers k l n
  let frontier : Fin r := standardFrontier
  let src : Fin k → Fin r := standardInput
  let tmp : Fin (l + n + 1) → Fin r := standardScratch
  obtain ⟨hsrc, htmp, hd, hf, hs⟩ := standardPlacement k l n
  let code := Code.seq (inputPrefix frontier (tmp (Fin.last (l + n))) src)
    (emit frontier src tmp)
  let prog := code.program (tmp (Fin.castAdd (n + 1) i))
  refine ⟨r, C + (2 * k + 5), code.size, prog, frontier,
    (fun j => tmp (Fin.castAdd (n + 1) j)), ?_⟩
  intro w d words hlayout hk hw hin hsafe hv
  obtain ⟨x, ex, hx, hm, hwords, _⟩ := inputPrefix_exec frontier (tmp (Fin.last (l + n)))
    src words hsrc (hf _) (fun j => hd j _) hs hk hw hin
  have harg : x.regs ∘ src = input d := funext fun j => (hwords j).trans (hlayout j)
  obtain ⟨y, ey, hmem, hout, _⟩ := (he frontier src tmp htmp hd hf hs).2 w d x hx harg
    (hm.symm ▸ hsafe) (hm.symm ▸ hv)
  rw [hm] at ey hmem hout
  obtain ⟨steps, hsteps, erun⟩ := ex.seq ey
  have hr := erun.runs (pc := 0) (p := prog) (Program.Contains.self _).append_left
  refine ⟨y, steps, ?_, ?_, hmem, hout, ?_⟩
  · simpa only [Nat.zero_add, State.init, code] using hr
  · rw [← hout i]
    exact step_halt (by simp [prog, Code.program])
  · have := Nat.mul_le_mul_left (2 * k + 5) (Nat.le_add_left 1
      (memoryCost (p d) (Memory.State.init words) + work d (Memory.State.init words)))
    rw [Nat.add_mul]
    omega

/-- One statically laid-out flat program includes charged input installation and its halt.
The witnessed native state is the actual final state of the flat run, retaining the entire
source memory and frontier and every result coordinate. All witnesses precede runtime data. -/
theorem exists_standard_init_program_state (h : Realizes .exact p input output safe work)
    (raw : δ → List ℕ) (hlayout : ∀ d (i : Fin k), (raw d).getD i.val 0 = input d i)
    (i : Fin l) :
    ∃ r C pc : ℕ, ∃ prog : Program .exact r,
      ∃ frontier : Fin r, ∃ out : Fin l → Fin r,
      ∀ w d, k ≤ (raw d).length → Fits w ((raw d).length + 1) → InputFits w (raw d) →
        safe w d (Memory.State.init (raw d)) →
        (Memory.spec w).ValidHistory (Memory.State.init (raw d))
          ((Memory.spec w).clientHistory (Memory.State.init (raw d)) (p d)) →
        ∃ y n, Runs w prog (State.init (raw d)) ⟨pc, y⟩ n ∧
          step w prog ⟨pc, y⟩ =
            .halt (output ((Memory.spec w).clientResult (Memory.State.init (raw d)) (p d)) i) ∧
          memoryState frontier y = (Memory.spec w).clientState (Memory.State.init (raw d)) (p d) ∧
          (∀ j, y.regs (out j) =
            output ((Memory.spec w).clientResult (Memory.State.init (raw d)) (p d)) j) ∧
          n + 1 ≤ C * (memoryCost (p d) (Memory.State.init (raw d)) +
            work d (Memory.State.init (raw d)) + 1) + 1 := by
  obtain ⟨r, C, pc, prog, frontier, out, he⟩ :=
    h.exists_standard_init_program_state_from_words i
  exact ⟨r, C, pc, prog, frontier, out, fun w d => he w d (raw d) (hlayout d)⟩

/-- The canonical initialized export requires no caller-written register layout. Its bound
includes the actual prefix, body and final halt, with code fixed before every width and input. -/
theorem exists_standard_init_program (h : Realizes .exact p input output safe work)
    (raw : δ → List ℕ) (hlayout : ∀ d (i : Fin k), (raw d).getD i.val 0 = input d i)
    (i : Fin l) :
    ∃ r C : ℕ, ∃ prog : Program .exact r,
      ∀ w d, k ≤ (raw d).length → Fits w ((raw d).length + 1) → InputFits w (raw d) →
        safe w d (Memory.State.init (raw d)) →
        (Memory.spec w).ValidHistory (Memory.State.init (raw d))
          ((Memory.spec w).clientHistory (Memory.State.init (raw d)) (p d)) →
        ∃ t, Executes w prog (State.init (raw d))
            (output ((Memory.spec w).clientResult (Memory.State.init (raw d)) (p d)) i) t ∧
          t ≤ C * (memoryCost (p d) (Memory.State.init (raw d)) +
            work d (Memory.State.init (raw d)) + 1) + 1 := by
  obtain ⟨r, C, pc, prog, _, _, he⟩ := h.exists_standard_init_program_state raw hlayout i
  refine ⟨r, C, prog, ?_⟩
  intro w d hk hw hin hsafe hv
  obtain ⟨y, n, hr, hh, _, _, hn⟩ := he w d hk hw hin hsafe hv
  exact ⟨n + 1, ⟨⟨pc, y⟩, n, hr, hh, rfl⟩, hn⟩

private theorem inputLoads_not_readsWidth {r k : ℕ} (ptr : Fin r) (src : Fin k → Fin r)
    (offset : ℕ) : ¬(inputLoads ptr src offset).ReadsWidth := by
  induction k generalizing offset with
  | zero => simp [inputLoads, Code.ReadsWidth, Op.ReadsWidth]
  | succ k ih =>
    simp [inputLoads, Code.ReadsWidth, Op.ReadsWidth, ih]

private theorem inputPrefix_not_readsWidth {r k : ℕ} (frontier ptr : Fin r)
    (src : Fin k → Fin r) : ¬(inputPrefix frontier ptr src).ReadsWidth := by
  simp [inputPrefix, Code.ReadsWidth, Op.ReadsWidth, Op.exactBin, Basis.exact,
    inputLoads_not_readsWidth]

/-- Standard-basis width-blind analogue of `exists_standard_init_program_state_from_words`:
translates the realized `Basis.exact` structured code along `Basis.Simulates.exactStandard` into
a `Program .standard r` satisfying `¬prog.ReadsWidth`, preserving exact memory, frontier, result
coordinates, and step bounds on every admitted run. -/
theorem exists_standard_basis_init_program_state_from_words
    (h : Realizes .exact p input output safe work) (i : Fin l) :
    ∃ r C pc : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧
      ∃ frontier : Fin r, ∃ out : Fin l → Fin r,
      ∀ w d words, (∀ j : Fin k, words.getD j.val 0 = input d j) →
        k ≤ words.length → Fits w (words.length + 1) → InputFits w words →
        safe w d (Memory.State.init words) →
        (Memory.spec w).ValidHistory (Memory.State.init words)
          ((Memory.spec w).clientHistory (Memory.State.init words) (p d)) →
        ∃ y n, Runs w prog (State.init words) ⟨pc, y⟩ n ∧
          step w prog ⟨pc, y⟩ =
            .halt (output ((Memory.spec w).clientResult (Memory.State.init words) (p d)) i) ∧
          memoryState frontier y = (Memory.spec w).clientState (Memory.State.init words) (p d) ∧
          (∀ j, y.regs (out j) =
            output ((Memory.spec w).clientResult (Memory.State.init words) (p d)) j) ∧
          n + 1 ≤ C * (memoryCost (p d) (Memory.State.init words) +
            work d (Memory.State.init words) + 1) + 1 := by
  obtain ⟨n, C, emit, he⟩ := h
  let r := registers k l n
  let frontier : Fin r := standardFrontier
  let src : Fin k → Fin r := standardInput
  let tmp : Fin (l + n + 1) → Fin r := standardScratch
  obtain ⟨hsrc, htmp, hd, hf, hs⟩ := standardPlacement k l n
  let code := Code.seq (inputPrefix frontier (tmp (Fin.last (l + n))) src)
    (emit frontier src tmp)
  let codeStd := code.mapSimulates .exactStandard
  let prog := codeStd.program (tmp (Fin.castAdd (n + 1) i))
  have hnw_exact : ¬code.ReadsWidth := by
    simp only [code, Code.ReadsWidth, not_or]
    exact ⟨inputPrefix_not_readsWidth _ _ _, (he frontier src tmp htmp hd hf hs).1⟩
  have hnw_std : ¬prog.ReadsWidth :=
    Code.not_readsWidth_program
      (fun h => hnw_exact (Code.readsWidth_of_mapSimulates .exactStandard h)) _
  refine ⟨r, C + (2 * k + 5), codeStd.size, prog, hnw_std, frontier,
    (fun j => tmp (Fin.castAdd (n + 1) j)), ?_⟩
  intro w d words hlayout hk hw hin hsafe hv
  obtain ⟨x, ex, hx, hm, hwords, _⟩ := inputPrefix_exec frontier (tmp (Fin.last (l + n)))
    src words hsrc (hf _) (fun j => hd j _) hs hk hw hin
  have harg : x.regs ∘ src = input d := funext fun j => (hwords j).trans (hlayout j)
  obtain ⟨y, ey, hmem, hout, _⟩ := (he frontier src tmp htmp hd hf hs).2 w d x hx harg
    (hm.symm ▸ hsafe) (hm.symm ▸ hv)
  rw [hm] at ey hmem hout
  obtain ⟨steps, hsteps, erun⟩ := ex.seq ey
  have erunStd := erun.mapSimulates .exactStandard
  have hr := erunStd.runs (pc := 0) (p := prog) (Program.Contains.self _).append_left
  refine ⟨y, steps, ?_, ?_, hmem, hout, ?_⟩
  · simpa only [Nat.zero_add, State.init, codeStd, code] using hr
  · rw [← hout i]
    exact step_halt (by simp [prog, Code.program])
  · have := Nat.mul_le_mul_left (2 * k + 5) (Nat.le_add_left 1
      (memoryCost (p d) (Memory.State.init words) + work d (Memory.State.init words)))
    rw [Nat.add_mul]
    omega

end Realizes
end Cslib.WordRAM.Realization
