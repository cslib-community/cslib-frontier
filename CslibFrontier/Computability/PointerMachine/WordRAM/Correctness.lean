/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.WordRAM.Effect
public import CslibFrontier.Computability.PointerMachine.WordRAM.Encoding
import Mathlib.Data.List.MinMax

/-!
# Correctness of pointer-machine compilation to word RAM

Given implementations of the scalar primitives, the compiler transfers valid pointer-machine
runs to the standard word RAM. All represented data and addresses must fit the chosen word width
throughout the source run; scalar calls must satisfy their implementations' headroom conditions.
The target starts with a represented source state, so input preparation is not charged here.

`Scalars.runs_compile` preserves the complete represented state with constant overhead per
source instruction. `Scalars.executes_compile` includes the final halt and retains the represented
final state. The target halt returns zero; the machine's data and heap remain in the final state.
These are forward simulation results, not a correspondence between source and target faults.
-/

public section

namespace Cslib.PointerMachine.WordRAM.Scalars

variable {M : Model} {L : Layout} (S : Scalars M L)

private theorem blockSize_bound {code : List (Instr M L)} {i : Instr M L} (hi : i ∈ code) :
    (S.effect i).size + 2 ≤ S.blockSize code := by
  have h := List.le_max_of_le' 1
    (List.mem_map.mpr ⟨i, hi, rfl⟩ :
      (S.effect i).size + 2 ∈ code.map (fun j => (S.effect j).size + 2))
    (le_refl ((S.effect i).size + 2))
  simpa only [blockSize, List.foldr_map, Function.comp_def] using h

private theorem overhead_bound {code : List (Instr M L)} {i : Instr M L} (hi : i ∈ code) :
    S.effectTime i + 2 ≤ S.overhead code := by
  have h := List.le_max_of_le' 1
    (List.mem_map.mpr ⟨i, hi, rfl⟩ : S.effectTime i + 2 ∈ code.map (fun j => S.effectTime j + 2))
    (le_refl (S.effectTime i + 2))
  simpa only [overhead, List.foldr_map, Function.comp_def] using h

private theorem length_block {code : List (Instr M L)} {i : Instr M L} (hi : i ∈ code) (pc : ℕ) :
    (S.block (S.blockSize code) pc i).length = S.blockSize code := by
  have h := S.blockSize_bound hi
  have hr : (S.rawBlock (S.blockSize code) pc i).length ≤ S.blockSize code := by
    cases i <;> simp only [rawBlock, List.length_append, Cslib.WordRAM.Code.length_assemble,
      List.length_cons, List.length_nil] <;> omega
  simp only [block, List.length_append, List.length_replicate]
  omega

private theorem contains_raw {code : List (Instr M L)} {pc : ℕ} {i : Instr M L}
    (hi : code[pc]? = some i) :
    (S.compile code).Contains (S.blockSize code * pc) (S.rawBlock (S.blockSize code) pc i) := by
  have hstart := Cslib.WordRAM.Program.Contains.self (S.compile code)
  change (S.compile code).Contains 0
    (Cslib.Program.compileBlocks (S.block (S.blockSize code)) 0 code) at hstart
  have h := hstart.block (fun pc _ hi => S.length_block hi pc) hi
  simpa only [Nat.zero_add] using h.append_left

/-- The compiled program occupies a fixed number of target slots per source instruction. -/
theorem length_compile (code : List (Instr M L)) :
    (S.compile code).length = S.blockSize code * code.length :=
  Cslib.Program.length_compileBlocks (fun pc _ hi => S.length_block hi pc) 0

private theorem branch_jump_runs {w pc yes no : ℕ}
    {p : Cslib.WordRAM.Program .standard (regCount L)}
    {c : Cslib.WordRAM.Cond (regCount L)} {z : Cslib.WordRAM.Data (regCount L)}
    (hc : p.Contains pc [.branch c yes, .jump no]) :
    ∃ n ≤ 2, Cslib.WordRAM.Runs w p ⟨pc, z⟩ ⟨if c.Holds z then yes else no, z⟩ n := by
  by_cases hb : c.Holds z
  · refine ⟨1, by decide, .single ?_⟩
    simpa only [Cslib.WordRAM.Next, hb, ite_true] using
      (Cslib.WordRAM.step_branch (w := w) (s := ⟨pc, z⟩) hc.head)
  · have hs : Cslib.WordRAM.Next w p ⟨pc, z⟩ ⟨pc + 1, z⟩ := by
      simpa only [Cslib.WordRAM.Next, hb, ite_false] using
        (Cslib.WordRAM.step_branch (w := w) (s := ⟨pc, z⟩) hc.head)
    have hj : Cslib.WordRAM.Next w p ⟨pc + 1, z⟩ ⟨no, z⟩ :=
      Cslib.WordRAM.step_jump hc.cons_tail.head
    refine ⟨2, le_rfl, ?_⟩
    simpa only [hb, ite_false] using (Relation.RelatesInSteps.single hs).tail _ _ _ _ hj

private theorem step_compile {w : ℕ} {code : List (Instr M L)}
    {x x' : State M L} {y : Cslib.WordRAM.Data (regCount L)}
    (hv : x.Valid) (hy : Repr S.encode x y)
    (hfit : Fits S.encode w x) (hfit' : Fits S.encode w x')
    (hsafe : ∀ i, code[x.pc]? = some i → S.Safe w x i)
    (hs : PointerMachine.step code x = some x') :
    ∃ z n, n ≤ S.overhead code ∧
      Cslib.WordRAM.Runs w (S.compile code) ⟨S.blockSize code * x.pc, y⟩
        ⟨S.blockSize code * x'.pc, z⟩ n ∧ Repr S.encode x' z := by
  obtain ⟨i, hi, hne, rfl⟩ := step_eq_some_iff.mp hs
  obtain ⟨z, ⟨n, hn, he⟩, hz, ht⟩ := S.effect_correct i hv hy hfit
    ⟨hfit'.free, hfit'.data, hfit'.heapData⟩ (hsafe i hi)
  have hc := S.contains_raw hi
  have hcost := S.overhead_bound (List.mem_of_getElem? hi)
  cases i with
  | halt => exact (hne rfl).elim
  | goto t =>
    simp only [rawBlock] at hc
    have hr := he.runs hc.append_left
    refine ⟨z, n + 1, by omega, hr.tail _ _ _ _ ?_, hz.with_pc _⟩
    exact Cslib.WordRAM.step_jump
      (by simpa only [Cslib.WordRAM.Code.length_assemble, Instr.next] using hc.append_right.head)
  | ifPtrEq a b t =>
    simp only [rawBlock] at hc
    have hr := he.runs hc.append_left
    obtain ⟨m, hm, hmrun⟩ := branch_jump_runs (w := w) (z := z)
      (by simpa only [Cslib.WordRAM.Code.length_assemble] using hc.append_right)
    have hcond : (Cslib.WordRAM.Cond.eq (ptrReg L a) (ptrReg L b)).Holds z ↔ x.ptr a = x.ptr b := by
      simp only [Cslib.WordRAM.Cond.holds_eq, hz.ptr, Instr.effect]
      exact ptrWord_injective.eq_iff
    refine ⟨z, n + m, by omega, ?_, hz.with_pc _⟩
    simpa only [Instr.next, hcond, mul_ite] using hr.trans hmrun
  | ifTest p a b t =>
    simp only [rawBlock] at hc
    have hr := he.runs hc.append_left
    obtain ⟨m, hm, hmrun⟩ := branch_jump_runs (w := w) (z := z)
      (by simpa only [Cslib.WordRAM.Code.length_assemble] using hc.append_right)
    have hcond : (Cslib.WordRAM.Cond.lt (zeroReg L) (valueReg L)).Holds z ↔
        M.evalTest p (x.data a) (x.data b) = true := by
      simp only [Cslib.WordRAM.Cond.holds_lt, hz.zero, ht]
      cases M.evalTest p (x.data a) (x.data b) <;> simp
    refine ⟨z, n + m, by omega, ?_, hz.with_pc _⟩
    simpa only [Instr.next, hcond, mul_ite] using hr.trans hmrun
  | _ =>
    simp only [rawBlock] at hc
    have hr := he.runs hc.append_left
    refine ⟨z, n + 1, by omega, hr.tail _ _ _ _ ?_, hz.with_pc _⟩
    exact Cslib.WordRAM.step_jump
        (by simpa only [Cslib.WordRAM.Code.length_assemble, Instr.next] using hc.append_right.head)

/-- Compile a run from represented input, preserving the complete final state. The overhead is
constant for a fixed source program and scalar implementation. Fitting words are required at
every source boundary; scalar admissibility is required only for instructions that execute. -/
theorem runs_compile {w n : ℕ} {code : List (Instr M L)} {x x' : State M L}
    {y : Cslib.WordRAM.Data (regCount L)} (hv : x.Valid) (hy : Repr S.encode x y)
    (hr : Runs code x x' n)
    (hfit : ∀ z m, Runs code x z m → m ≤ n → Fits S.encode w z)
    (hsafe : ∀ z m, Runs code x z m → m < n →
      ∀ i, code[z.pc]? = some i → S.Safe w z i) :
    ∃ z k, k ≤ S.overhead code * n ∧
      Cslib.WordRAM.Runs w (S.compile code) ⟨S.blockSize code * x.pc, y⟩
        ⟨S.blockSize code * x'.pc, z⟩ k ∧ Repr S.encode x' z := by
  induction hr with
  | refl => exact ⟨y, 0, by omega, .refl _, hy⟩
  | tail s t n hsteps hnext ih =>
    obtain ⟨z, k, hk, hrun, hzr⟩ := ih
      (fun z m hz hm => hfit z m hz (by omega))
      (fun z m hz hm => hsafe z m hz (by omega))
    obtain ⟨z', l, hl, hlast, hz'r⟩ := S.step_compile (PointerMachine.Runs.valid hsteps hv) hzr
      (hfit s n hsteps (by omega)) (hfit t (n + 1) (hsteps.tail _ _ _ _ hnext) le_rfl)
      (hsafe s n hsteps (by omega)) hnext
    exact ⟨z', k + l, by simpa only [Nat.mul_succ] using Nat.add_le_add hk hl,
      hrun.trans hlast, hz'r⟩

/-- A successful source execution yields a target run ending at a represented final state and
then halting with zero. The bound includes that halt. The target starts with the canonical
`encodeState` representation; constructing this preencoded input is not charged here. -/
theorem executes_compile {w time : ℕ} {code : List (Instr M L)} {x x' : State M L}
    (hv : x.Valid) (he : Executes code x x' time)
    (hfit : ∀ z m, Runs code x z m → m < time → Fits S.encode w z)
    (hsafe : ∀ z m, Runs code x z m → m + 1 < time →
      ∀ i, code[z.pc]? = some i → S.Safe w z i) :
    ∃ z k, k + 1 ≤ S.overhead code * time ∧
      Cslib.WordRAM.Runs w (S.compile code) ⟨S.blockSize code * x.pc, encodeState S.encode x⟩
        ⟨S.blockSize code * x'.pc, z⟩ k ∧ Repr S.encode x' z ∧
      Cslib.WordRAM.step w (S.compile code) ⟨S.blockSize code * x'.pc, z⟩ = .halt 0 := by
  obtain ⟨n, hr, hh, rfl⟩ := he
  obtain ⟨z, k, hk, hrun, hzr⟩ := S.runs_compile hv (repr_encodeState S.encode x) hr
    (fun z m hz hm => hfit z m hz (by omega))
    (fun z m hz hm => hsafe z m hz (by omega))
  have hcost := S.overhead_bound (List.mem_of_getElem? hh)
  have hhalt := (S.contains_raw hh).head
  refine ⟨z, k, ?_, hrun, hzr, ?_⟩
  · simp only [Nat.mul_succ]
    simp only [effectTime] at hcost
    omega
  · simpa only [hzr.zero] using
      (Cslib.WordRAM.step_halt (w := w) (s := ⟨S.blockSize code * x'.pc, z⟩) hhalt)

end Cslib.PointerMachine.WordRAM.Scalars
