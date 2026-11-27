/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.SymbolicExec.Havoc
import CslibFrontier.Computability.WordRAM.SymbolicExec.MemFrame
import CslibFrontier.Computability.WordRAM.SymbolicExec.StructFrame
import Mathlib.Order.Interval.Finset.Nat

/-!
# Memory and mixed-record frame tests

Regressions for `mem_frame`, `Code.StoreFree`, and `struct_frame`: whole-memory equations, `Data`
state equations, pointwise frames (single- and multi-premise), `Set.EqOn`, `Modifies`
(`Block.footprint`, `Finset.Ico`, unions, singletons), `Exec.mem_eq` / `ExecWithin.mem_eq` (closed
and parameterized programs, plus renamed programs and rejected storing programs), `Data.set` /
`Data.write` / `Data.comap` / `Data.extend` / `Data.havoc` and chained `Function.update`,
`let`-bound states, concrete cell equations and indexed slice equations, conjunctions,
`Prop`-valued structures, user-unfolded `def` predicates (`mem_frame [P]`), polymorphic hint
frames, `struct_frame` across mixed register + `Block.Realizes` + memory + bound records, silent
`@[wram_arith]` unfolding without triggering `linter.unnecessaryWramOmega`, open metavariables,
overlapping-frame search, failure diagnostics, and a check that no leftover axioms remain in the
environment after rejecting `Code.StoreFree`.
-/

namespace CslibFrontierTests.WordRAMMemFrame

open Cslib.WordRAM

/-- Local arithmetic layout definitions tagged `@[wram_arith]`. -/
@[wram_arith] def hdrSize : ℕ := 8
/-- Local table offset definition tagged `@[wram_arith]`. -/
@[wram_arith] def tabBase (base k : ℕ) : ℕ := base + hdrSize + k
/-- Local total footprint size tagged `@[wram_arith]`. -/
@[wram_arith] def totalSpace (k m : ℕ) : ℕ := hdrSize + k + m

/-! ## Whole-memory equations, `let` states, and wrappers -/

/-- Whole-memory equation chain across calls and `Data.set` / `comap` / `extend`. -/
example (x y z : Data 4) (hxy : y.mem = x.mem) (hyz : z.mem = y.mem) :
    z.mem = x.mem := by
  mem_frame

/-- Swapped whole-memory equality and `Data.set` / `comap` / `extend` / `havoc` wrappers. -/
example (x y z : Data 4) (f : Fin 2 → Fin 4) (c : Code .standard 4) (rv : Fin 4 → ℕ)
    (h : x.mem = y.mem) (h' : z = (y.set 0 7)) :
    (z.comap f).mem = x.mem ∧ ((z.comap f).extend f x).mem = x.mem ∧
      (x.havoc c rv z.mem).mem = x.mem := by
  mem_frame

/-- Bare `Data` equality `hs : s1 = ...` gives memory framing without `subst`. -/
example (x s1 : Data 4) (base v : ℕ)
    (hs1 : s1 = (x.set 0 base).write (base + 1) v) :
    s1.mem (base + 1) = v ∧ (∀ a, a ≠ base + 1 → s1.mem a = x.mem a) := by
  mem_frame

/-- `let`-bound intermediate states with stacked `Data.write` and `Data.set`. -/
example (x : Data 4) (base u v : ℕ) (hx : x.mem base = 42) :
    let y := ((x.write (base + 1) u).set 0 9).write (base + 2) v
    y.mem base = 42 ∧ y.mem (base + 1) = u ∧ y.mem (base + 2) = v ∧
      y.mem (base + 1 + 1) = v := by
  mem_frame

/-- Chained `Function.update` on a bare `ℕ → ℕ` map. -/
example (m : ℕ → ℕ) (base a b c : ℕ) (hm : m (base + 5) = 99) :
    let m1 := Function.update m (base + 1) a
    let m2 := Function.update m1 (base + 2) b
    let m3 := Function.update m2 (base + 3) c
    m3 (base + 1) = a ∧ m3 (base + 2) = b ∧ m3 (base + 3) = c ∧
      m3 (base + 5) = 99 ∧ (∀ p, p < base + 1 ∨ base + 4 ≤ p → m3 p = m p) := by
  mem_frame

/-! ## Pointwise frames, `Modifies`, and `Set.EqOn` -/

/-- Chained multi-premise frames with `@[wram_arith]` unfolding (must emit no warning). -/
example (x d1 d2 d3 : Data 4) (base k m : ℕ)
    (h1 : d1.mem = x.mem)
    (h2 : ∀ a, a < base ∨ base + 6 ≤ a → d2.mem a = d1.mem a)
    (h3 : ∀ a, a < tabBase base k ∨ tabBase base k + m ≤ a → d3.mem a = d2.mem a)
    (hm0 : d2.mem base = 11) (hm5 : d2.mem (base + 5) = 22) :
    d3.mem base = 11 ∧ d3.mem (base + 5) = 22 ∧
      (∀ a, a < base ∨ base + totalSpace k m ≤ a → d3.mem a = x.mem a) := by
  mem_frame

/-- `Modifies` block footprints and `Finset.Ico` compose as both hypothesis and goal. -/
example (x y z : Data 4) (base k m : ℕ)
    (hy : Modifies (Block.mk base 6).footprint x.mem y.mem)
    (hz : Modifies (Finset.Ico (tabBase base k) (tabBase base k + m)) y.mem z.mem) :
    Modifies (Finset.Ico base (base + totalSpace k m)) x.mem z.mem := by
  mem_frame

/-- `Modifies` with a singleton and union footprint. -/
example (m0 m1 m2 : ℕ → ℕ) (base v : ℕ)
    (h1 : Modifies ({base} : Finset ℕ) m0 m1)
    (h2 : Modifies ({base + 1} : Finset ℕ) m1 m2)
    (h0 : m0 (base + 2) = v) :
    m2 (base + 2) = v ∧ Modifies ({base} ∪ {base + 1} : Finset ℕ) m0 m2 := by
  mem_frame

/-- `Set.EqOn` as both hypothesis and goal (`Set.Ico`, `Set.Iio`, `Set.Ici`). -/
example (m0 m1 m2 : ℕ → ℕ) (base n : ℕ)
    (h1 : Set.EqOn m1 m0 (Set.Iio (base + n)))
    (h2 : ∀ a, a < base + n → m2 a = m1 a) :
    Set.EqOn m2 m0 (Set.Ico base (base + n)) := by
  mem_frame

/-- Overlapping frames on the same state: BFS finds the value regardless of hypothesis order. -/
example (x y z : Data 4) (base v : ℕ) (hy : y.mem (base + 1) = v)
    (hzy : ∀ a, a ≠ base + 2 → z.mem a = y.mem a)
    (_hzx : ∀ a, a ≠ base + 2 → a ≠ base + 3 → z.mem a = x.mem a) :
    z.mem (base + 1) = v := by
  mem_frame

example (x y z : Data 4) (base v : ℕ) (hy : y.mem (base + 1) = v)
    (_hzx : ∀ a, a ≠ base + 2 → a ≠ base + 3 → z.mem a = x.mem a)
    (hzy : ∀ a, a ≠ base + 2 → z.mem a = y.mem a) :
    z.mem (base + 1) = v := by
  mem_frame

/-! ## `Code.StoreFree` and `Exec.mem_eq` / `ExecWithin.mem_eq` -/

/-- Register abbreviations for test code. -/
abbrev r0 : Fin 4 := 0
/-- Register abbreviations for test code. -/
abbrev r1 : Fin 4 := 1
/-- Register abbreviations for test code. -/
abbrev r2 : Fin 4 := 2

/-- A closed store-free program (only loads and arithmetic). -/
def readOnlyCode : Code .standard 4 :=
  .seq (.op (.const r0 5))
    (.seq (.op (.load r1 r0))
          (.op (.bin .add r2 r1 r0)))

/-- A parameterized store-free program (`k` is a free variable). -/
def paramReadCode (k : ℕ) : Code .exact 4 :=
  .seq (.op (.const 1 k))
       (.op (.load 2 1))

/-- A program that contains a store instruction. -/
def storeCode : Code .standard 4 :=
  .op (.store r0 r1)

/-- Closed store-free executions are decided in the kernel via `Exec.mem_eq` /
`ExecWithin.mem_eq`. -/
example (w : ℕ) (x y z : Data 4) (a v : ℕ) (hx : x.mem a = v)
    (he1 : Exec w readOnlyCode x y 3) (he2 : ExecWithin w readOnlyCode y z 5) :
    z.mem = x.mem ∧ z.mem a = v := by
  mem_frame

/-- Parameterized and renamed store-free code works even with free variable `k`. -/
example (w k : ℕ) (x y z : Data 8) (f : Fin 4 → Fin 8)
    (he1 : Exec w ((paramReadCode k).rename f) x y 2)
    (he2 : ExecWithin w (paramReadCode k) (y.comap f) (z.comap f) 2) :
    z.mem = x.mem := by
  mem_frame

/-- Rejected store-containing execution leaves no axiom and falls back to explicit frame. -/
theorem rejected_store_exec (w : ℕ) (x y z : Data 4) (base v : ℕ) (hx : x.mem (base + 5) = v)
    (zf : ∀ a, a ≠ base → z.mem a = x.mem a) (_he : ExecWithin w storeCode y z 1) :
    z.mem (base + 5) = v := by
  mem_frame

/-- Same test with opposite hypothesis order. -/
theorem rejected_store_exec' (w : ℕ) (x y z : Data 4) (base v : ℕ) (hx : x.mem (base + 5) = v)
    (_he : ExecWithin w storeCode y z 1) (zf : ∀ a, a ≠ base → z.mem a = x.mem a) :
    z.mem (base + 5) = v := by
  mem_frame

/-- Custom execution judgment supporting `J.mem_eq` extensibility. -/
def CustomReadOnly (x y : Data 4) : Prop := y.mem = x.mem

/-- Memory preservation lemma for `CustomReadOnly`. -/
theorem CustomReadOnly.mem_eq {x y : Data 4} (h : CustomReadOnly x y) : y.mem = x.mem := h

example (x y : Data 4) (a v : ℕ) (hx : x.mem a = v) (h : CustomReadOnly x y) :
    y.mem a = v := by
  mem_frame

/-! ## Structures, `def` predicates, slices, hints, and open metavariables -/

/-- A `Prop`-valued structure holding concrete memory equations and a slice. -/
structure HeaderBundle (base n : ℕ) (mem : ℕ → ℕ) : Prop where
  /-- Header cell 0. -/
  hdr0 : mem base = n
  /-- Header cell 1. -/
  hdr1 : mem (base + 1) = n + 1
  /-- Slice cells. -/
  slice : ∀ i < n, mem (base + 10 + i) = i * 2

/-- Preserving a `Prop`-valued structure across a frame. -/
example (x y : Data 4) (base n : ℕ) (hb : HeaderBundle base n x.mem)
    (hy : ∀ a, a ≠ base + 5 → y.mem a = x.mem a) :
    HeaderBundle base n y.mem := by
  mem_frame

/-- A `def`-based `Prop` predicate with `let`-bindings (like `KWise.TableRep`). -/
def ToyTableRep (base k : ℕ) (mem : ℕ → ℕ) : Prop :=
  let s := base + 2
  mem base = 10 ∧
  mem (base + 1) = k ∧
  ∀ idx < 4, mem (s + k + idx) = idx + 1

/-- Unfolding `ToyTableRep` via `mem_frame [ToyTableRep]`. -/
example (d3 d4 d5 : Data 4) (base k : ℕ)
    (hm0 : d3.mem base = 10)
    (hm1 : d4.mem (base + 1) = k)
    (hd4 : ∀ a, a < base + 1 ∨ base + 2 ≤ a → d4.mem a = d3.mem a)
    (hd5 : ∀ a, a < base + 2 + k ∨ base + 2 + k + 4 ≤ a → d5.mem a = d4.mem a)
    (htab : ∀ idx < 4, d5.mem (base + 2 + k + idx) = idx + 1) :
    ToyTableRep base k (d5.set 0 99).mem := by
  mem_frame [ToyTableRep]

/-- Transporting an arbitrary predicate across a whole-memory equality chain. -/
example (P : (ℕ → ℕ) → Prop) (x y z : Data 4)
    (hP : P x.mem) (hy : y.mem = x.mem) (hz : z.mem = y.mem) : P z.mem := by
  mem_frame

/-- Polymorphic user lemma supplied in `mem_frame [...]`. -/
def customPatch (m : ℕ → ℕ) (p v : ℕ) : ℕ → ℕ := Function.update m p v

/-- Patch agrees outside `p`. -/
theorem customPatch_ne {m : ℕ → ℕ} {p v a : ℕ} (h : a ≠ p) :
    customPatch m p v a = m a := by
  simp [customPatch, Function.update_of_ne h]

example (x y : Data 4) (base p v : ℕ) (hp : p = base + 3)
    (hy : y.mem = customPatch x.mem p v) (hx : x.mem base = 7) :
    y.mem base = 7 := by
  mem_frame [customPatch_ne]

/-- Open metavariable value is inferred automatically (`y.mem a = ?v`). -/
theorem needs_cell (x : Data 4) (a : ℕ) {v : ℕ} (_ : x.mem a = v) :
    ∃ u, u = v + 1 :=
  ⟨v + 1, rfl⟩

example (x y : Data 4) (base n : ℕ) (hx : x.mem base = n)
    (hy : ∀ a, a ≠ base + 1 → y.mem a = x.mem a) : ∃ u, u = n + 1 :=
  needs_cell y base (by mem_frame)

/-- `def` register-count alias (`Data regAlias` vs `Data 4`) shares a hash key. -/
private def regAlias : ℕ := 4

example (x : Data regAlias) (y : Data regAlias) (z : Data regAlias)
    (hy : (y : Data 4).mem = x.mem) (hz : z.mem = y.mem) : z.mem = x.mem := by
  mem_frame

/-- `match` expression whose scrutinee is a constructor reduces in both hypotheses and goals. -/
example (x y : Data 4) (base v : ℕ)
    (h : match (some v : Option ℕ) with | some u => x.mem base = u | none => True)
    (hf : ∀ a, a ≠ base + 1 → y.mem a = x.mem a) :
    match (some v : Option ℕ) with | some u => y.mem base = u | none => True := by
  mem_frame

/-- Unfolding a `ℕ`-returning wrapper `def` via `mem_frame [cellAt]`. -/
private def cellAt (base : ℕ) (m : ℕ → ℕ) (i : ℕ) : ℕ := m (base + i)

example (x y : Data 4) (base : ℕ)
    (hx : cellAt base x.mem 2 = 42)
    (hf : ∀ a, a ≠ base + 5 → y.mem a = x.mem a) :
    cellAt base y.mem 2 = 42 := by
  mem_frame [cellAt]

/-! ## `struct_frame` across mixed records and conjunctions -/

/-- Mixed `Prop`-valued structure combining registers, `Block.HoldsList`, quantified cells, and
bounds. -/
structure MixedFrame (base db : ℕ) (xs : List ℕ) (s : Data 4) : Prop where
  /-- Register 0. -/
  r0_eq : s.regs r0 = base
  /-- Register 1. -/
  r1_eq : s.regs r1 = db
  /-- List view below `db`. -/
  list_view : Block.HoldsList base xs s.mem
  /-- Stored cell below `db`. -/
  hdr_cell : ∀ k : Fin 4, s.mem (base + xs.length + k.val) = k.val + 1
  /-- Layout bound. -/
  span_le : base + xs.length + 4 ≤ db

/-- `struct_frame` transports `MixedFrame` across register updates, memory frames, and `Data.havoc`
while discovering `h.span_le` and `Fin.isLt` automatically. -/
example (xs : List ℕ) (base db : ℕ) (x y z : Data 4) (rv : Fin 4 → ℕ)
    (hx : MixedFrame base db xs x)
    (hy : y = (x.set r2 99).write (db + 3) 42)
    (hzr : ∀ i : Fin 4, i ≠ r2 → z.regs i = (y.havoc storeCode rv y.mem).regs i)
    (hzm : ∀ a < db, z.mem a = y.mem a) :
    MixedFrame base db xs z := by
  struct_frame hx

/-- Conjunction `def` with `base + 0` header cell and nested `some (m a)` read under
`@[wram_arith]`. -/
def DictHeaderAndVals (base k : ℕ) (f : ℕ → Option ℕ) (mem : ℕ → ℕ) : Prop :=
  mem base = k ∧
  mem (base + 1) = 7 ∧
  ∀ idx < k, f idx = some (mem (tabBase base k + idx))

example (base k : ℕ) (f : ℕ → Option ℕ) (m m' : ℕ → ℕ)
    (h : DictHeaderAndVals base k f m)
    (hmem : ∀ a ∈ (Block.mk base (totalSpace k k)).footprint, m' a = m a) :
    DictHeaderAndVals base k f m' := by
  struct_frame h

example (base k : ℕ) (f : ℕ → Option ℕ) (m m' : ℕ → ℕ)
    (h : DictHeaderAndVals base k f m)
    (heq : ∀ j ≤ 1, m' (base + j) = m (base + j))
    (hv : ∀ idx < k, m' (tabBase base k + idx) = m (tabBase base k + idx)) :
    DictHeaderAndVals base k f m' := by
  struct_frame h

/-! ## Failure diagnostics -/

/-- error: mem_frame: could not prove
  z.mem base = n
Following the frames leaves
  y.mem base = n
`yf` does not give `y.mem base`: it needs
  base ≠ base -/
#guard_msgs (whitespace := lax) in
example (x y z : Data 4) (base n : ℕ) (hx : x.mem base = n)
    (yf : ∀ a, a ≠ base → y.mem a = x.mem a)
    (zf : ∀ a, a ≠ base + 1 → z.mem a = y.mem a) :
    z.mem base = n := by
  mem_frame

/-- error: mem_frame: could not prove
  y.mem a = n
`he.mem_eq` does not give `y.mem a`: it needs
  storeCode.StoreFree -/
#guard_msgs (whitespace := lax) in
example (w : ℕ) (x y : Data 4) (a n : ℕ) (hx : x.mem a = n)
    (he : ExecWithin w storeCode x y 1) :
    y.mem a = n := by
  mem_frame

/-- error: mem_frame: could not prove
  y.mem a = n
No hypothesis gives `y.mem a` or a frame of its memory. -/
#guard_msgs (whitespace := lax) in
example (w : ℕ) (x y : Data 4) (a n : ℕ) (hx : x.mem a = n) : y.mem a = n := by
  mem_frame

/-! ## Nothing is left behind

Checking `Code.StoreFree` in the kernel creates an auxiliary lemma and restores the environment on
rejection. Verify no axiom was left behind in the environment. -/

open Lean Elab Command in
run_cmd do
  let leftover := (← getEnv).checked.get.constants.map₂.foldl (init := #[]) fun acc name info =>
    if info matches .axiomInfo _ then acc.push name else acc
  unless leftover.isEmpty do
    throwError "mem_frame left axioms in the environment: {leftover}"

end CslibFrontierTests.WordRAMMemFrame
