/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.VanEmdeBoas.Elements
public import CslibFrontier.DataStructure.VanEmdeBoas.WordRAM.Init
public import CslibFrontier.DataStructure.VanEmdeBoas.WordRAM.Insert
public import CslibFrontier.DataStructure.VanEmdeBoas.WordRAM.Member
public import CslibFrontier.DataStructure.VanEmdeBoas.WordRAM.Successor
public import CslibFrontier.Computability.WordRAM.Dynamic
public import CslibFrontier.DataStructure.OrderedSet.Basic
public import Mathlib.Data.Nat.Log

import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame
import CslibFrontier.Computability.WordRAM.SymbolicExec.Havoc

/-!
# Complete native van Emde Boas calls and adaptive dynamic realization

All three operations — `insert` (`tag = 0`), `member` (`tag = 1`), and strict `successor`
(`tag = 2`) — execute on the same fixed 32-register dispatcher `program`, charging constant
setup, dispatch branches, every loop instruction, and the final `halt`.

In addition, this module connects `program` to the shared
`DataStructure.StateTransitionSpec` / `DynamicProgram` /
`DynamicCertificate` interface on finite sets (`Finset ℕ`) and combines the uniform native
initializer `initProgram` with arbitrary adaptive client histories (`run_initialized`).
Native dynamic calls append a checked eight-instruction result conversion. Membership copies its
answer into the shared flag register, and flags are normalized before canonical structural
parsing. Their
uniform halt-inclusive bound is `65 * (d + 1) + 30`.

## Main definitions

* `Operation`, `Operation.Result`, `spec`, `dynamicProgram`, `SetRep`, `certificate`: the
  stateful finite-set specification and its fixed-program Word-RAM realization.

## Main results

* `insert_dispatch_spec`, `insert_call`, `insert_executes`, `insert_executes_generic`,
  `insert_executes_log`: complete native insertion calls in `39 * (d + 1) + 16` instructions.
* `member_dispatch_spec`, `member_call`, `member_executes`, `member_executes_generic`,
  `member_executes_log`: complete native membership calls in `28 * (d + 1) + 18` instructions.
* `successor_dispatch_spec`, `successor_call`, `successor_executes`,
  `successor_executes_generic`, `successor_executes_log`: complete native strict-successor calls
  in `65 * (d + 1) + 22` instructions.
* `instruction_bound`, `instruction_bound_log`, `client_spec`, `run_initialized`: adaptive
  history execution and combined initialization-plus-client execution certificates.

## References

* [P. van Emde Boas, R. Kaas and E. Zijlstra, *Design and implementation of an efficient
  priority queue*][VanEmdeBoasKaasZijlstra1977]
* [E. Demaine, *Divide and conquer: van Emde Boas trees*, Lecture 4][Demaine2015VanEmdeBoas]
-/

public section

namespace Cslib.DataStructure.VanEmdeBoas.WordRAM

open Cslib.WordRAM
open Cslib.DataStructure Cslib.DataStructure.VanEmdeBoas

@[wram_simps]
private theorem insertEntry_iff {base key : ℕ} {s : Data 32} :
    InsertEntry base key s ↔
      s.regs zero = 0 ∧ s.regs one = 1 ∧ s.regs two = 2 ∧ s.regs three = 3 ∧
        s.regs four = 4 ∧ s.regs five = 5 ∧ s.regs p = base ∧ s.regs x = key ∧
        s.regs runFlag = 1 :=
  ⟨fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i⟩,
   fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i⟩⟩

@[wram_simps]
private theorem memberEntry_iff {base query : ℕ} {s : Data 32} :
    MemberEntry base query s ↔
      s.regs zero = 0 ∧ s.regs one = 1 ∧ s.regs two = 2 ∧ s.regs three = 3 ∧
        s.regs four = 4 ∧ s.regs five = 5 ∧ s.regs p = base ∧ s.regs x = query ∧
        s.regs out = 0 ∧ s.regs runFlag = 1 :=
  ⟨fun ⟨a, b, c, d, e, f, g, h, i, j⟩ => ⟨a, b, c, d, e, f, g, h, i, j⟩,
   fun ⟨a, b, c, d, e, f, g, h, i, j⟩ => ⟨a, b, c, d, e, f, g, h, i, j⟩⟩

@[wram_simps]
private theorem successorEntry_iff {stackBase₀ sp₀ base query : ℕ} {s : Data 32} :
    SuccessorEntry stackBase₀ sp₀ base query s ↔
      s.regs zero = 0 ∧ s.regs one = 1 ∧ s.regs two = 2 ∧ s.regs three = 3 ∧
        s.regs four = 4 ∧ s.regs five = 5 ∧ s.regs stackBase = stackBase₀ ∧ s.regs sp = sp₀ ∧
        s.regs p = base ∧ s.regs x = query ∧ s.regs runFlag = 1 :=
  ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, k⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k⟩,
   fun ⟨a, b, c, d, e, f, g, h, i, j, k⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k⟩⟩

/-- The single compiled program contains 212 ordinary instructions and a final halt. -/
theorem compiled_program_length : (program.program out).length = 213 := by
  simp only [Code.program, List.length_append, Code.length_assemble, program_size,
    List.length_cons, List.length_nil]

/-- Compiling the fixed dispatcher introduces no word-width instruction. -/
theorem compiled_program_not_readsWidth : ¬(program.program out).ReadsWidth :=
  Code.not_readsWidth_program program_not_readsWidth out

/-- The supported double-exponential universe has exactly `d` iterated binary logarithms. -/
theorem log_log_universeSize (d : ℕ) : Nat.log 2 (Nat.log 2 (universeSize d)) = d := by
  simp only [universeSize_eq_two_pow, Nat.log_pow Nat.one_lt_two]

/-- Lift a bounded `ExecWithin` run of `program` to an exact `Exec` witness while preserving
boundedness and the persistent `root` and `stackBase` registers. -/
private theorem program_call_of_execWithin {w T : ℕ} {s : Data 32} {P : Data 32 → Prop}
    (hs : s.Bounded w) (h : ∃ z, ExecWithin w program s z T ∧ P z) :
    ∃ z n, n + 1 ≤ T + 1 ∧ Exec w program s z n ∧ z.Bounded w ∧
      z.regs root = s.regs root ∧ z.regs stackBase = s.regs stackBase ∧ P z := by
  obtain ⟨z, ⟨n, hn, he⟩, hP⟩ := h
  exact ⟨z, n, Nat.succ_le_succ hn, he, he.bounded hs, by regs_frame, by regs_frame, hP⟩

/-! ## Complete native insertion calls -/

/-- A complete insertion dispatch (`tag = 0`), including setup and all control flow but not final
halt, executes in at most `39 * (d + 1) + 15` instructions, updates the represented tree to
`tree.insert key`, leaves `out = 0`, and preserves all memory outside `[base, base + span d)`. -/
theorem insert_dispatch_spec {d w base key : ℕ} {tree : Tree d} {s : Data 32}
    (ht : tree.Valid) (hr : Rep tree base s.mem) (hx : key < universeSize d)
    (ha : Fits w (base + span d)) (hroot : s.regs root = base)
    (harg : s.regs arg = key) (htag : s.regs tag = 0) :
    ∃ z, ExecWithin w program s z (39 * (d + 1) + 15) ∧
      Rep (tree.insert key) base z.mem ∧
      z.regs out = 0 ∧
      (∀ a, a < base ∨ base + span d ≤ a → z.mem a = s.mem a) := by
  have hw : Fits w 5 := ha.of_le (by have := five_le_span d; omega)
  apply WP.exists_execWithin
  unfold program setup
  wram_exec [hroot, harg, htag]
  wram_call (insertLoop_spec (base := base) (key := key) (tree := tree) ..) framed [hr]
    with v m ⟨hrep, hframe⟩
  exact ⟨by omega, hrep, hframe⟩

/-- A bounded caller invoking insertion (`tag = 0`) obtains a bounded state representing
`tree.insert key`, with unchanged persistent `root` and `stackBase` registers and all memory
outside `[base, base + span d)` preserved. -/
theorem insert_call {d w base key : ℕ} {tree : Tree d} {s : Data 32}
    (hs : s.Bounded w) (ht : tree.Valid) (hr : Rep tree base s.mem)
    (hx : key < universeSize d) (ha : Fits w (base + span d))
    (hroot : s.regs root = base) (harg : s.regs arg = key) (htag : s.regs tag = 0) :
    ∃ z n, n + 1 ≤ 39 * (d + 1) + 16 ∧ Exec w program s z n ∧
      z.Bounded w ∧ Rep (tree.insert key) base z.mem ∧
      z.regs root = base ∧ z.regs stackBase = s.regs stackBase ∧
      z.regs out = 0 ∧
      (∀ a, a < base ∨ base + span d ≤ a → z.mem a = s.mem a) := by
  obtain ⟨z, n, hn, he, hb, hroot', hstk', hrep, hout, hframe⟩ :=
    program_call_of_execWithin hs (insert_dispatch_spec ht hr hx ha hroot harg htag)
  exact ⟨z, n, hn, he, hb, hrep, hroot'.trans hroot, hstk', hout, hframe⟩

/-- Actual flat bounded-word insertion execution, including its final halt, in
`39 * (d + 1) + 16` instructions. -/
theorem insert_executes {d w base key : ℕ} {tree : Tree d} {s : Data 32}
    (hs : s.Bounded w) (ht : tree.Valid) (hr : Rep tree base s.mem)
    (hx : key < universeSize d) (ha : Fits w (base + span d))
    (hroot : s.regs root = base) (harg : s.regs arg = key) (htag : s.regs tag = 0) :
    ∃ n ≤ 39 * (d + 1) + 16,
      Cslib.WordRAM.Executes w (program.program out) ⟨0, s⟩ 0 n := by
  obtain ⟨z, n, hn, he, _, _, _, _, hout, _⟩ :=
    insert_call hs ht hr hx ha hroot harg htag
  exact ⟨n + 1, hn, hout ▸ he.executes out⟩

/-- Exact transfer of the flat insertion call into the shared generic RAM model. -/
theorem insert_executes_generic {d w base key : ℕ} {tree : Tree d} {s : Data 32}
    (hs : s.Bounded w) (ht : tree.Valid) (hr : Rep tree base s.mem)
    (hx : key < universeSize d) (ha : Fits w (base + span d))
    (hroot : s.regs root = base) (harg : s.regs arg = key) (htag : s.regs tag = 0) :
    ∃ n ≤ 39 * (d + 1) + 16,
      GenericRAM.Executes w (program.program out).toGeneric
        ((⟨0, s⟩ : State 32).toGeneric .standard) 0 n := by
  obtain ⟨n, hn, he⟩ := insert_executes hs ht hr hx ha hroot harg htag
  exact ⟨n, hn, executes_toGeneric_iff.mpr he⟩

/-- The charged native insertion bound written directly in terms of the universe size. -/
theorem insert_executes_log {d w base key : ℕ} {tree : Tree d} {s : Data 32}
    (hs : s.Bounded w) (ht : tree.Valid) (hr : Rep tree base s.mem)
    (hx : key < universeSize d) (ha : Fits w (base + span d))
    (hroot : s.regs root = base) (harg : s.regs arg = key) (htag : s.regs tag = 0) :
    ∃ n ≤ 39 * (Nat.log 2 (Nat.log 2 (universeSize d)) + 1) + 16,
      Cslib.WordRAM.Executes w (program.program out) ⟨0, s⟩ 0 n := by
  simpa only [log_log_universeSize] using insert_executes hs ht hr hx ha hroot harg htag

/-! ## Complete native membership calls -/

/-- A complete membership dispatch, including setup and all control flow but not final halt.
No query-universe restriction and no zero-filled outside-memory assumption are imposed. -/
theorem member_dispatch_spec {d w base query : ℕ} {tree : Tree d} {s : Data 32}
    (ht : tree.Valid) (hr : Rep tree base s.mem) (ha : Fits w (base + span d))
    (hroot : s.regs root = base) (harg : s.regs arg = query) (htag : s.regs tag = 1) :
    ∃ z, ExecWithin w program s z (28 * (d + 1) + 17) ∧
      z.regs out = (if tree.member query then 1 else 0) ∧ z.mem = s.mem := by
  have hw : Fits w 5 := ha.of_le (by have := five_le_span d; omega)
  apply WP.exists_execWithin
  unfold program setup
  wram_exec [hroot, harg, htag]
  wram_call (memberLoop_spec (base := base) (query := query) (tree := tree) ..) framed [hr]
    with v m ⟨hout, hmem⟩
  exact ⟨by omega, hout, hmem⟩

/-- A bounded caller obtains a bounded result, identical represented memory and an unchanged
persistent root. Its query fits the machine word because every caller register does. -/
theorem member_call {d w base query : ℕ} {tree : Tree d} {s : Data 32}
    (hs : s.Bounded w) (ht : tree.Valid) (hr : Rep tree base s.mem)
    (ha : Fits w (base + span d)) (hroot : s.regs root = base)
    (harg : s.regs arg = query) (htag : s.regs tag = 1) :
    ∃ z n, n + 1 ≤ 28 * (d + 1) + 18 ∧ Exec w program s z n ∧
      z.Bounded w ∧ Rep tree base z.mem ∧ z.regs root = base ∧
      z.regs out = (if tree.member query then 1 else 0) ∧ z.mem = s.mem := by
  obtain ⟨z, n, hn, he, hb, hroot', _, hout, hmem⟩ :=
    program_call_of_execWithin hs (member_dispatch_spec ht hr ha hroot harg htag)
  exact ⟨z, n, hn, he, hb, hmem ▸ hr, hroot'.trans hroot, hout, hmem⟩

/-- Actual flat bounded-word execution, including its final halt, in `28 (d+1) + 18`
instructions. The selected fixed program has no depth or word-width parameter. -/
theorem member_executes {d w base query : ℕ} {tree : Tree d} {s : Data 32}
    (hs : s.Bounded w) (ht : tree.Valid) (hr : Rep tree base s.mem)
    (ha : Fits w (base + span d)) (hroot : s.regs root = base)
    (harg : s.regs arg = query) (htag : s.regs tag = 1) :
    ∃ n ≤ 28 * (d + 1) + 18,
      Cslib.WordRAM.Executes w (program.program out) ⟨0, s⟩
        (if tree.member query then 1 else 0) n := by
  obtain ⟨z, n, hn, he, _, _, _, hout, _⟩ := member_call hs ht hr ha hroot harg htag
  exact ⟨n + 1, hn, hout ▸ he.executes out⟩

/-- Exact transfer of the actual flat call into the shared generic RAM model; this adds no
semantic operation or uncharged oracle instruction. -/
theorem member_executes_generic {d w base query : ℕ} {tree : Tree d} {s : Data 32}
    (hs : s.Bounded w) (ht : tree.Valid) (hr : Rep tree base s.mem)
    (ha : Fits w (base + span d)) (hroot : s.regs root = base)
    (harg : s.regs arg = query) (htag : s.regs tag = 1) :
    ∃ n ≤ 28 * (d + 1) + 18,
      GenericRAM.Executes w (program.program out).toGeneric
        ((⟨0, s⟩ : State 32).toGeneric .standard) (if tree.member query then 1 else 0) n := by
  obtain ⟨n, hn, he⟩ := member_executes hs ht hr ha hroot harg htag
  exact ⟨n, hn, executes_toGeneric_iff.mpr he⟩

/-- The charged native membership bound written directly in terms of the universe size. -/
theorem member_executes_log {d w base query : ℕ} {tree : Tree d} {s : Data 32}
    (hs : s.Bounded w) (ht : tree.Valid) (hr : Rep tree base s.mem)
    (ha : Fits w (base + span d)) (hroot : s.regs root = base)
    (harg : s.regs arg = query) (htag : s.regs tag = 1) :
    ∃ n ≤ 28 * (Nat.log 2 (Nat.log 2 (universeSize d)) + 1) + 18,
      Cslib.WordRAM.Executes w (program.program out) ⟨0, s⟩
        (if tree.member query then 1 else 0) n := by
  simpa only [log_log_universeSize] using member_executes hs ht hr ha hroot harg htag

/-! ## Complete native strict-successor calls -/

/-- A complete strict-successor dispatch (`tag = 2`), including setup, descent, and stack unwind
but not final halt, executes in at most `65 * (d + 1) + 21` instructions, preserves the
represented tree at `base`, restores `sp = stackBase₀`, and modifies no memory outside the
`4 * d`-word stack region `[stackBase₀, stackBase₀ + 4 * d)`. -/
theorem successor_dispatch_spec {d w base stackBase₀ query : ℕ} {tree : Tree d} {s : Data 32}
    (ht : tree.Valid) (hr : Rep tree base s.mem)
    (hstk_lo : base + span d ≤ stackBase₀) (hstk_fit : Fits w (stackBase₀ + 4 * d))
    (hroot : s.regs root = base) (hstk : s.regs stackBase = stackBase₀)
    (harg : s.regs arg = query) (htag : s.regs tag = 2) :
    ∃ z, ExecWithin w program s z (65 * (d + 1) + 21) ∧
      (if z.regs found = 0 then none else some (z.regs out)) = tree.successor query ∧
      Rep tree base z.mem ∧
      z.regs sp = stackBase₀ ∧
      (∀ a, a < stackBase₀ ∨ stackBase₀ + 4 * d ≤ a → z.mem a = s.mem a) := by
  have hw : Fits w 5 := hstk_fit.of_le (by have := five_le_span d; omega)
  apply WP.exists_execWithin
  unfold program setup
  wram_exec [hroot, hstk, harg, htag]
  wram_call (successor_loop_spec (stackBase₀ := stackBase₀) (base := base) (query := query)
    (tree := tree) ..) framed [hr, hstk] with v m ⟨hans, hsp, hrep, hframe⟩
  exact ⟨by omega, hans, hrep, hsp, hframe⟩

/-- A bounded caller invoking strict successor (`tag = 2`) obtains a bounded state with the
exact optional successor encoded by `(found, out)`, unchanged persistent `root` and `stackBase`
registers, preserved tree representation, and unchanged memory outside
`[stackBase₀, stackBase₀ + 4 * d)`. -/
theorem successor_call {d w base stackBase₀ query : ℕ} {tree : Tree d} {s : Data 32}
    (hs : s.Bounded w) (ht : tree.Valid) (hr : Rep tree base s.mem)
    (hstk_lo : base + span d ≤ stackBase₀) (hstk_fit : Fits w (stackBase₀ + 4 * d))
    (hroot : s.regs root = base) (hstk : s.regs stackBase = stackBase₀)
    (harg : s.regs arg = query) (htag : s.regs tag = 2) :
    ∃ z n, n + 1 ≤ 65 * (d + 1) + 22 ∧ Exec w program s z n ∧
      z.Bounded w ∧ Rep tree base z.mem ∧
      z.regs root = base ∧ z.regs stackBase = stackBase₀ ∧ z.regs sp = stackBase₀ ∧
      (if z.regs found = 0 then none else some (z.regs out)) = tree.successor query ∧
      (∀ a, a < stackBase₀ ∨ stackBase₀ + 4 * d ≤ a → z.mem a = s.mem a) := by
  obtain ⟨z, n, hn, he, hb, hroot', hstk', hans, hrep, hsp, hframe⟩ :=
    program_call_of_execWithin hs
      (successor_dispatch_spec ht hr hstk_lo hstk_fit hroot hstk harg htag)
  exact ⟨z, n, hn, he, hb, hrep, hroot'.trans hroot, hstk'.trans hstk, hsp, hans, hframe⟩

/-- Actual flat bounded-word strict-successor execution, including its final halt, in
`65 * (d + 1) + 22` instructions. -/
theorem successor_executes {d w base stackBase₀ query : ℕ} {tree : Tree d} {s : Data 32}
    (hs : s.Bounded w) (ht : tree.Valid) (hr : Rep tree base s.mem)
    (hstk_lo : base + span d ≤ stackBase₀) (hstk_fit : Fits w (stackBase₀ + 4 * d))
    (hroot : s.regs root = base) (hstk : s.regs stackBase = stackBase₀)
    (harg : s.regs arg = query) (htag : s.regs tag = 2) :
    ∃ (z : Data 32) (n : ℕ), n ≤ 65 * (d + 1) + 22 ∧
      Cslib.WordRAM.Executes w (program.program out) ⟨0, s⟩ (z.regs out) n ∧
      (if z.regs found = 0 then none else some (z.regs out)) = tree.successor query ∧
      Rep tree base z.mem ∧
      (∀ a, a < stackBase₀ ∨ stackBase₀ + 4 * d ≤ a → z.mem a = s.mem a) := by
  obtain ⟨z, n, hn, he, _, hrep, _, _, _, hans, hframe⟩ :=
    successor_call hs ht hr hstk_lo hstk_fit hroot hstk harg htag
  exact ⟨z, n + 1, hn, he.executes out, hans, hrep, hframe⟩

/-- Exact transfer of the flat strict-successor call into the shared generic RAM model. -/
theorem successor_executes_generic {d w base stackBase₀ query : ℕ} {tree : Tree d} {s : Data 32}
    (hs : s.Bounded w) (ht : tree.Valid) (hr : Rep tree base s.mem)
    (hstk_lo : base + span d ≤ stackBase₀) (hstk_fit : Fits w (stackBase₀ + 4 * d))
    (hroot : s.regs root = base) (hstk : s.regs stackBase = stackBase₀)
    (harg : s.regs arg = query) (htag : s.regs tag = 2) :
    ∃ (z : Data 32) (n : ℕ), n ≤ 65 * (d + 1) + 22 ∧
      GenericRAM.Executes w (program.program out).toGeneric
        ((⟨0, s⟩ : State 32).toGeneric .standard) (z.regs out) n ∧
      (if z.regs found = 0 then none else some (z.regs out)) = tree.successor query ∧
      Rep tree base z.mem ∧
      (∀ a, a < stackBase₀ ∨ stackBase₀ + 4 * d ≤ a → z.mem a = s.mem a) := by
  obtain ⟨z, n, hn, he, hans, hrep, hframe⟩ :=
    successor_executes hs ht hr hstk_lo hstk_fit hroot hstk harg htag
  exact ⟨z, n, hn, executes_toGeneric_iff.mpr he, hans, hrep, hframe⟩

/-- The charged native strict-successor bound written directly in terms of the universe size. -/
theorem successor_executes_log {d w base stackBase₀ query : ℕ} {tree : Tree d} {s : Data 32}
    (hs : s.Bounded w) (ht : tree.Valid) (hr : Rep tree base s.mem)
    (hstk_lo : base + span d ≤ stackBase₀) (hstk_fit : Fits w (stackBase₀ + 4 * d))
    (hroot : s.regs root = base) (hstk : s.regs stackBase = stackBase₀)
    (harg : s.regs arg = query) (htag : s.regs tag = 2) :
    ∃ (z : Data 32) (n : ℕ), n ≤ 65 * (Nat.log 2 (Nat.log 2 (universeSize d)) + 1) + 22 ∧
      Cslib.WordRAM.Executes w (program.program out) ⟨0, s⟩ (z.regs out) n ∧
      (if z.regs found = 0 then none else some (z.regs out)) = tree.successor query ∧
      Rep tree base z.mem ∧
      (∀ a, a < stackBase₀ ∨ stackBase₀ + 4 * d ≤ a → z.mem a = s.mem a) := by
  simpa only [log_log_universeSize] using
    successor_executes hs ht hr hstk_lo hstk_fit hroot hstk harg htag

/-! ## Finite-set `DataStructure.StateTransitionSpec` and `DynamicCertificate` realization -/

/-- `Tree.successor` on a valid tree computes the mathematical `OrderedSet.least` of the stored
elements strictly greater than the query. -/
theorem successor_eq_least {d : ℕ} {t : Tree d} (ht : t.Valid) (q : ℕ) :
    t.successor q = OrderedSet.least (t.elements.filter (q < ·)) := by
  apply OrderedSet.LeastResult.eq_least
  cases hs : t.successor q with
  | none =>
    simp only [OrderedSet.LeastResult, Finset.filter_eq_empty_iff]
    exact fun z hz => not_lt_of_ge ((Tree.successor_elements_none_iff ht q).mp hs z hz)
  | some y =>
    simp only [OrderedSet.LeastResult, Finset.mem_filter]
    obtain ⟨hy_mem, hqy, hmin⟩ := (Tree.successor_elements_some_iff ht q y).mp hs
    exact ⟨⟨hy_mem, hqy⟩, fun z ⟨hz_mem, hqz⟩ => hmin z hz_mem hqz⟩

/-- Dynamic ordered-set operations supported by the van Emde Boas dispatcher. -/
inductive Operation where
  /-- Insert a bounded universe key into the set. -/
  | insert (key : ℕ)
  /-- Query whether a fitting word belongs to the set. -/
  | member (query : ℕ)
  /-- Return the least stored key strictly greater than a fitting query, if any. -/
  | successor (query : ℕ)
  deriving DecidableEq, Repr

/-- Typed observation returned by each van Emde Boas operation. -/
abbrev Operation.Result : Operation → Type
  | .insert _ => PUnit
  | .member _ => Bool
  | .successor _ => Option ℕ

/-- Abstract finite-set specification on the universe `[0, universeSize d)`. -/
abbrev spec (d w : ℕ) : DataStructure.StateTransitionSpec :=
  DataStructure.StateTransitionSpec.ofFn (State := Finset ℕ) (Op := Operation)
    (Result := Operation.Result)
    (fun s => fun
      | .insert k => (Insert.insert k s, PUnit.unit)
      | .member q => (s, decide (q ∈ s))
      | .successor q => (s, OrderedSet.least (s.filter (q < ·))))
    (fun _ => fun
      | .insert k => k < universeSize d
      | .member q => Fits w q
      | .successor q => Fits w q)

/-- Canonical native result formats: unit, exact Boolean, or tag followed by a natural word. -/
@[expose] def nativeResultType : Operation → ResultType
  | .insert _ => .unit
  | .member _ => .bool
  | .successor _ => .option .nat

/-- The result format presents each operation's existing observation type by equality. -/
theorem nativeResultType_eq (o : Operation) : Operation.Result o = (nativeResultType o).Value := by
  cases o <;> rfl

/-- A fixed bank shared by every operation: presence/Boolean flag, then successor payload. -/
@[expose] def nativeResultBank (i : ℕ) : Fin 32 := if i = 0 then found else out

/-- Native result conversion stages real constants, copies membership's answer to the shared
flag register, and normalizes that register to exactly zero or one. -/
@[expose] def nativeResultCode : Code .standard 32 := ram[
  zero ← #0; one ← #1;
  if tag = one then [ found ← out ] else [ found ← found ];
  if found = zero then [ found ← #0 ] else [ found ← #1 ] ]

/-- The fixed dispatcher followed by its paid canonical result suffix, with a register-only
calling convention (`tag` and `arg`) and one fixed output bank. -/
@[expose] def dynamicProgram (d w : ℕ) : DynamicProgram (spec d w) 32 where
  code := .seq program nativeResultCode
  output := out
  input j := j == tag || j == arg
  encode o j := match o with
    | .insert k => if j = tag then 0 else k
    | .member q => if j = tag then 1 else q
    | .successor q => if j = tag then 2 else q
  resultBank := nativeResultBank
  resultType := nativeResultType
  resultType_eq := nativeResultType_eq

/-- Persistent machine representation of an abstract finite set `s : Finset ℕ` by a valid tree
at `base` and scratch stack pointer at `stackBase₀`. -/
structure SetRep (d base stackBase₀ w : ℕ) (s : Finset ℕ) (x : Data 32) : Prop where
  bounded : x.Bounded w
  root_eq : x.regs root = base
  stackBase_eq : x.regs stackBase = stackBase₀
  tree : ∃ t : Tree d, t.Valid ∧ t.elements = s ∧ Rep t base x.mem

/-- Every encoded argument of a valid van Emde Boas operation fits the machine word width. -/
theorem arguments_fit {d w base stackBase₀ : ℕ}
    (hstk_lo : base + span d ≤ stackBase₀) (hstk_fit : Fits w (stackBase₀ + 4 * d))
    {s : Finset ℕ} (o : Operation) (ho : (spec d w).valid s o) (j : Fin 32) :
    Fits w ((dynamicProgram d w).encode o j) := by
  have h5_le := five_le_span d
  have hu_le := universeSize_le_span d
  have h2 : Fits w 2 := hstk_fit.of_le (by omega)
  cases o <;> simp only [dynamicProgram] <;> split
  · exact fits_zero w
  · exact hstk_fit.of_le (by dsimp only [spec] at ho; omega)
  · exact h2.of_le (by decide)
  · exact ho
  · exact h2
  · exact ho

/-- Every admitted native call executes the original dispatcher and the paid canonical result
suffix, retaining the represented set and all original memory framing guarantees. -/
theorem dispatch_spec {d w base stackBase₀ : ℕ} {s : Finset ℕ} {x : Data 32}
    (hstk_lo : base + span d ≤ stackBase₀) (hstk_fit : Fits w (stackBase₀ + 4 * d))
    (o : Operation) (hx : SetRep d base stackBase₀ w s x) (ho : (spec d w).valid s o) :
    ∃ y, ExecWithin w (dynamicProgram d w).code ((dynamicProgram d w).prepare o x) y
        (65 * (d + 1) + 29) ∧
      (dynamicProgram d w).decode o y.regs = some ((spec d w).stepFn s o).2 ∧
      SetRep d base stackBase₀ w ((spec d w).stepFn s o).1 y ∧
      (∀ a, (a < base ∨ base + span d ≤ a) →
        (a < stackBase₀ ∨ stackBase₀ + 4 * d ≤ a) → y.mem a = x.mem a) := by
  obtain ⟨t, hvalid, rfl, hrep⟩ := hx.tree
  have ha : Fits w (base + span d) := hstk_fit.of_le (by omega)
  have h1 : Fits w 1 := ha.of_le (by have := five_le_span d; omega)
  have hprep_bounded : ((dynamicProgram d w).prepare o x).Bounded w :=
    (dynamicProgram d w).prepare_bounded hx.bounded
      (fun j _ => arguments_fit hstk_lo hstk_fit o ho j)
  have hprep_rep : Rep t base ((dynamicProgram d w).prepare o x).mem := hrep
  have hprep_root : ((dynamicProgram d w).prepare o x).regs root = base :=
    ((dynamicProgram d w).prepare_regs_of_not_input rfl o x).trans hx.root_eq
  have hprep_stk : ((dynamicProgram d w).prepare o x).regs stackBase = stackBase₀ :=
    ((dynamicProgram d w).prepare_regs_of_not_input rfl o x).trans hx.stackBase_eq
  apply WP.exists_execWithin
  apply WP.bounded hprep_bounded
  change WP w (.seq program nativeResultCode) _ _
  apply WP.seq
  cases o with
  | insert k =>
    have hprep_tag : ((dynamicProgram d w).prepare (.insert k) x).regs tag = 0 := rfl
    wram_call (insert_dispatch_spec (key := k) hvalid hprep_rep ho ha hprep_root rfl hprep_tag)
      framed with v m ⟨hy_rep, -, hy_frame⟩
    wram_exec [nativeResultCode, hprep_tag] <;>
      exact fun hy_b => ⟨by omega, rfl,
        ⟨hy_b, by wram_simp [hprep_root], by wram_simp [hprep_stk],
          t.insert k, Tree.valid_insert hvalid ho, Tree.elements_insert hvalid ho,
          by wram_simp; exact hy_rep⟩,
        fun a ha_t _ => by wram_simp; exact hy_frame a ha_t⟩
  | member q =>
    have hprep_tag : ((dynamicProgram d w).prepare (.member q) x).regs tag = 1 := rfl
    wram_call (member_dispatch_spec (query := q) hvalid hprep_rep ha hprep_root rfl hprep_tag)
      framed with v m ⟨hy_out, hy_mem⟩
    have hm_eq : t.member q = decide (q ∈ t.elements) :=
      Bool.eq_iff_iff.mpr ((Tree.member_iff_contains hvalid q).trans
        ((Tree.mem_elements_iff hvalid q).symm.trans decide_eq_true_iff.symm))
    unfold nativeResultCode
    cases hmem : t.member q <;> simp only [hmem, Bool.false_eq_true, ↓reduceIte] at hy_out <;>
    · wram_exec [hprep_tag, hy_out]
      intro hy_b
      refine ⟨by omega, ?_, ⟨hy_b, by wram_simp [hprep_root], by wram_simp [hprep_stk],
        t, hvalid, rfl, by wram_simp [hy_mem]; exact hrep⟩,
        fun a _ _ => by wram_simp [hy_mem]; rfl⟩
      dsimp only [dynamicProgram, DynamicProgram.decode, nativeResultType, ResultType.decode,
        Function.comp_apply, nativeResultBank]
      wram_simp
      simp only [Option.map_some]
      exact congrArg some (hm_eq.symm.trans hmem).symm
  | successor q =>
    have hprep_tag : ((dynamicProgram d w).prepare (.successor q) x).regs tag = 2 := rfl
    wram_call (successor_dispatch_spec (query := q) hvalid hprep_rep hstk_lo hstk_fit
      hprep_root hprep_stk rfl hprep_tag) framed with v m ⟨hy_ans, hy_rep, -, hy_frame⟩
    wram_exec [nativeResultCode, hprep_tag] <;>
    · intro hy_b
      refine ⟨by omega, ?_, ⟨hy_b, by wram_simp [hprep_root], by wram_simp [hprep_stk],
        t, hvalid, rfl, by wram_simp; exact hy_rep⟩,
        fun a _ ha_s => by wram_simp; exact hy_frame a ha_s⟩
      dsimp only [dynamicProgram, DynamicProgram.decode, nativeResultType, ResultType.decode,
        Function.comp_apply, nativeResultBank, spec]
      wram_simp
      simp only [Option.map_some, ← successor_eq_least hvalid q, ← hy_ans, hc, ↓reduceIte]
      rfl

/-- Semantic correctness and totality certificate for the fixed bounded-word van Emde Boas
implementation. -/
@[expose] def certificate {d w base stackBase₀ : ℕ}
    (hstk_lo : base + span d ≤ stackBase₀) (hstk_fit : Fits w (stackBase₀ + 4 * d)) :
    DynamicCertificate (dynamicProgram d w) w :=
  DynamicCertificate.ofFn
    (rep := SetRep d base stackBase₀ w)
    (bounded := SetRep.bounded)
    (arguments_fit := fun o ho j _ => arguments_fit hstk_lo hstk_fit o ho j)
    (execute := fun o hx ho => by
      obtain ⟨y, ⟨n, _, he⟩, hans, hy, _⟩ := dispatch_spec hstk_lo hstk_fit o hx ho
      exact ⟨y, n, he, hans, hy⟩)

/-- Separate worst-case per-operation instruction certificate, counting the final halt:
every admissible `insert`, `member`, or `successor` call executes in at most `65 * (d + 1) + 30`
instructions. -/
theorem instruction_bound {d w base stackBase₀ : ℕ}
    (hstk_lo : base + span d ≤ stackBase₀) (hstk_fit : Fits w (stackBase₀ + 4 * d)) :
    DataStructure.Bound (certificate hstk_lo hstk_fit).impl
      DynamicProgram.OperationTrace.instructions (fun _ _ => 65 * (d + 1) + 30) := by
  refine (certificate hstk_lo hstk_fit).instruction_bound_const _ fun {s x} o hx ho => ?_
  obtain ⟨z, ⟨k, hk, he'⟩, _, _⟩ := dispatch_spec hstk_lo hstk_fit o hx ho
  exact ⟨z, k, he', by omega⟩

/-- The per-operation instruction certificate written in terms of the universe size. -/
theorem instruction_bound_log {d w base stackBase₀ : ℕ}
    (hstk_lo : base + span d ≤ stackBase₀) (hstk_fit : Fits w (stackBase₀ + 4 * d)) :
    DataStructure.Bound (certificate hstk_lo hstk_fit).impl
      DynamicProgram.OperationTrace.instructions
      (fun _ _ => 65 * (Nat.log 2 (Nat.log 2 (universeSize d)) + 1) + 30) := by
  rw [log_log_universeSize]
  exact instruction_bound hstk_lo hstk_fit

/-- Every actual call preserves memory outside the tree region `[base, base + span d)` and
the scratch stack `[stackBase₀, stackBase₀ + 4 * d)`. -/
theorem execOp_frame {d w base stackBase₀ : ℕ}
    (hstk_lo : base + span d ≤ stackBase₀) (hstk_fit : Fits w (stackBase₀ + 4 * d))
    {s : Finset ℕ} {o : Operation} {x y : Data 32} {a : (spec d w).Result o}
    {trace : DynamicProgram.OperationTrace}
    (hx : SetRep d base stackBase₀ w s x) (ho : (spec d w).valid s o)
    (he : (dynamicProgram d w).ExecOp w x o a y trace) {j : ℕ}
    (hj_tree : j < base ∨ base + span d ≤ j)
    (hj_stk : j < stackBase₀ ∨ stackBase₀ + 4 * d ≤ j) : y.mem j = x.mem j := by
  obtain ⟨z, ⟨_, _, hk⟩, _, _, hf⟩ := dispatch_spec hstk_lo hstk_fit o hx ho
  exact (he.eq_of_exec hk).1 ▸ hf j hj_tree hj_stk

/-- Every admissible adaptive client execution preserves memory outside the tree and stack
regions across the entire interaction history. -/
theorem executes_client_frame {d w base stackBase₀ : ℕ}
    (hstk_lo : base + span d ≤ stackBase₀) (hstk_fit : Fits w (stackBase₀ + 4 * d))
    {α : Type} {p : (spec d w).Client α} {s : Finset ℕ} {x y : Data 32} {val : α}
    {traces : List DynamicProgram.OperationTrace}
    (hx : SetRep d base stackBase₀ w s x)
    (hv : (spec d w).ValidHistory s ((spec d w).clientHistory s p))
    (he : DataStructure.Executes ((dynamicProgram d w).ExecOp w) p x val y traces) {j : ℕ}
    (hj_tree : j < base ∨ base + span d ≤ j)
    (hj_stk : j < stackBase₀ ∨ stackBase₀ + 4 * d ≤ j) : y.mem j = x.mem j :=
  (certificate hstk_lo hstk_fit).executes_client_frame
    (fun hx' ho' he' => execOp_frame hstk_lo hstk_fit hx' ho' he' hj_tree hj_stk) hx hv he

/-- Every admissible adaptive client has a concrete execution with the specified answers and
final finite set, at most `65 * (d + 1) + 30` instructions per operation, and unchanged memory
outside the tree and stack regions. -/
theorem client_spec {d w base stackBase₀ : ℕ}
    (hstk_lo : base + span d ≤ stackBase₀) (hstk_fit : Fits w (stackBase₀ + 4 * d))
    {α : Type} (p : (spec d w).Client α) {s : Finset ℕ} {x : Data 32}
    (hx : SetRep d base stackBase₀ w s x)
    (hv : (spec d w).ValidHistory s ((spec d w).clientHistory s p)) :
    ∃ y traces, DataStructure.Executes ((dynamicProgram d w).ExecOp w) p x
        ((spec d w).clientResult s p) y traces ∧
      SetRep d base stackBase₀ w ((spec d w).clientState s p) y ∧
      DataStructure.total DynamicProgram.OperationTrace.instructions traces ≤
        ((spec d w).clientHistory s p).length * (65 * (d + 1) + 30) ∧
      (∀ j, (j < base ∨ base + span d ≤ j) →
        (j < stackBase₀ ∨ stackBase₀ + 4 * d ≤ j) → y.mem j = x.mem j) := by
  obtain ⟨y, traces, he, hr, hcost⟩ :=
    (certificate hstk_lo hstk_fit).run_client_const (instruction_bound hstk_lo hstk_fit) p hx hv
  exact ⟨y, traces, he, hr, hcost, fun j hjt hjs =>
    executes_client_frame hstk_lo hstk_fit hx hv he hjt hjs⟩

/-- Combined native initialization and adaptive client execution: starting from any bounded
machine state `s₀` with `s₀.regs root = base`, `s₀.regs depth = d`, and
`Fits w (base + span d + 4 * (d + 1))` (with arbitrary initial memory), `initProgram` executes
in at most `8 * span d + 20 * d + 25` instructions to produce an empty represented set `x₀`,
from which any admissible adaptive client `p` executes to `y` with at most `65 * (d + 1) + 30`
instructions per operation and no memory modified outside `[base, base + span d + 4 * (d + 1))`.
-/
theorem run_initialized {d w base : ℕ} {s₀ : Data 32}
    (hs₀ : s₀.Bounded w) (ha : Fits w (base + span d + 4 * (d + 1)))
    (hroot : s₀.regs root = base) (hdepth : s₀.regs depth = d)
    {α : Type} (p : (spec d w).Client α)
    (hv : (spec d w).ValidHistory (∅ : Finset ℕ)
      ((spec d w).clientHistory (∅ : Finset ℕ) p)) :
    ∃ x₀ n_init y traces,
      n_init + 1 ≤ 8 * span d + 20 * d + 25 ∧
      Exec w initProgram s₀ x₀ n_init ∧
      SetRep d base (base + span d) w (∅ : Finset ℕ) x₀ ∧
      DataStructure.Executes ((dynamicProgram d w).ExecOp w) p x₀
        ((spec d w).clientResult (∅ : Finset ℕ) p) y traces ∧
      SetRep d base (base + span d) w ((spec d w).clientState (∅ : Finset ℕ) p) y ∧
      DataStructure.total DynamicProgram.OperationTrace.instructions traces ≤
        ((spec d w).clientHistory (∅ : Finset ℕ) p).length * (65 * (d + 1) + 30) ∧
      (∀ j, j < base ∨ base + span d + 4 * (d + 1) ≤ j → y.mem j = s₀.mem j) := by
  obtain ⟨x₀, n_init, hn_init, he_init, hbounded₀, hrep₀, hroot₀, hstk₀, _, hframe₀⟩ :=
    init_call hs₀ ha hroot hdepth
  have hx₀ : SetRep d base (base + span d) w (∅ : Finset ℕ) x₀ :=
    ⟨hbounded₀, hroot₀, hstk₀, Tree.empty d, Tree.valid_empty d, Tree.elements_empty d, hrep₀⟩
  have hstk_fit : Fits w (base + span d + 4 * d) := ha.of_le (by omega)
  obtain ⟨y, traces, he_client, hy, hcost, hframe_client⟩ :=
    client_spec le_rfl hstk_fit p hx₀ hv
  refine ⟨x₀, n_init, y, traces, hn_init, he_init, hx₀, he_client, hy, hcost, ?_⟩
  intro j hj
  rw [hframe_client j (by omega) (by omega), hframe₀ j hj]

end Cslib.DataStructure.VanEmdeBoas.WordRAM
