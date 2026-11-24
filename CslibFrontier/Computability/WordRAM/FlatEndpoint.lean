/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.WordRAM.Compile
public import CslibFrontier.Computability.WordRAM.Width

/-!
# Flat-program endpoints and wide-width prefix envelopes

Structured word-RAM proofs establish bounded-time executions `ExecWithin w c x y T` on `Code B r`,
while final machine endpoints speak about flat instruction lists `c.program out`, halting runs
`Executes`, step-indexed prefixes `Runs`, and physical-width-independent memory envelopes across
all wider word sizes `W ≥ w`.

This module packages that transition once (alongside width monotonicity `Data.Bounded.mono` and
the `[simp]` length equation `Code.length_program`):

* lifting `ExecWithin` to `Runs`, `Executes` (charging `halt out`), and `Data.Bounded`;
* lifting minimum-width `ExecWithin` certificates of width-blind programs (`¬c.ReadsWidth`) to
  prefix word and address-support bounds at every wider physical width `W ≥ w`;
* `FlatEndpoint`: a single minimum-width structured certificate for an initialized program family,
  yielding `InputFits`, flat `Runs`, halting `Executes`, `Data.Bounded`, and initialized prefix
  envelope bounds at every `W ≥ wMin a`.

## Main definitions

* `Cslib.WordRAM.FlatEndpoint`: minimum-width structured execution and envelope certificate for an
  initialized width-independent program.

## Main results

* `Cslib.WordRAM.ExecWithin.to_program`, `Cslib.WordRAM.ExecWithin.to_program_init`: lift bounded
  structured executions to flat `Runs` and halting `Executes`.
* `Cslib.WordRAM.ExecWithin.prefix_bounds_program`,
  `Cslib.WordRAM.ExecWithin.prefix_bounds_program_init`: bound every wider flat prefix from a
  minimum-width structured execution.
* `Cslib.WordRAM.FlatEndpoint.inputFits`, `Cslib.WordRAM.FlatEndpoint.runs`,
  `Cslib.WordRAM.FlatEndpoint.prefix_bounds`: wide-width flat execution and prefix-envelope
  corollaries of `FlatEndpoint`.
-/

public section

namespace Cslib.WordRAM

/-- Machine data bounded at word size `w` remains bounded at every larger word size `W`. -/
theorem Data.Bounded.mono {r w W : ℕ} {x : Data r} (hx : x.Bounded w) (hw : w ≤ W) :
    x.Bounded W :=
  ⟨fun i => (hx.1 i).mono hw, fun a => (hx.2 a).mono hw⟩

/-- Compiling a structured program appends one `halt` instruction to its assembled body. -/
@[simp]
theorem Code.length_program {B : Basis} {r : ℕ} (c : Code B r) (out : Fin r) :
    (c.program out).length = c.size + 1 := by
  simp [Code.program]

/-- Lift a bounded structured execution to a flat prefix `Runs` reaching `c.size` and a halting
`Executes` run charging one additional `halt` instruction. -/
theorem ExecWithin.to_program {B : Basis} {r W T : ℕ} {c : Code B r} {x y : Data r}
    (he : ExecWithin W c x y T) (out : Fin r) :
    ∃ n ≤ T, Runs W (c.program out) ⟨0, x⟩ ⟨c.size, y⟩ n ∧
      Executes W (c.program out) ⟨0, x⟩ (y.regs out) (n + 1) := by
  obtain ⟨n, hn, hex⟩ := he
  refine ⟨n, hn, ?_, hex.executes out⟩
  simpa only [Nat.zero_add] using
    hex.runs (pc := 0) (p := c.program out) (Program.Contains.self _).append_left

/-- Lift an initialized bounded structured execution at an admitted input width to flat `Runs`,
halting `Executes`, and word-bounded final data. -/
theorem ExecWithin.to_program_init {B : Basis} {r W T : ℕ} {c : Code B r}
    {input : List ℕ} {y : Data r} (he : ExecWithin W c (.init input) y T)
    (hi : InputFits W input) (out : Fin r) :
    ∃ n ≤ T, Runs W (c.program out) (State.init input) ⟨c.size, y⟩ n ∧
      Executes W (c.program out) (State.init input) (y.regs out) (n + 1) ∧
      y.Bounded W := by
  obtain ⟨n, hn, hruns, hexec⟩ := he.to_program out
  exact ⟨n, hn, hruns, hexec, he.bounded (Data.Bounded.init hi)⟩

/-- A structured execution of a width-independent program at minimum width `w` bounds every
reachable prefix of `c.program out` at any wider physical width `W ≥ w` by `P` (`2 ^ w ≤ P`),
preserving caller memory from `P` onward. -/
theorem ExecWithin.prefix_bounds_program {B : Basis} {r w W P T k : ℕ} {c : Code B r}
    {out : Fin r} {x y : Data r} {s : State r}
    (he : ExecWithin w c x y T) (hc : ¬c.ReadsWidth) (hw : w ≤ W)
    (hx : x.Bounded w) (hP : 2 ^ w ≤ P)
    (hr : Runs W (c.program out) ⟨0, x⟩ s k) :
    (∀ i, s.data.regs i < P) ∧ (∀ a, s.data.mem a < P) ∧
      ∀ a, P ≤ a → s.data.mem a = x.mem a := by
  obtain ⟨_, _, hex⟩ := he
  exact hr.prefix_bounds (Code.not_readsWidth_program hc out) hw hx (hex.executes out) hP

/-- Initialized form of `ExecWithin.prefix_bounds_program`: every wider reachable prefix of
`c.program out` has words below `P` and zero memory from `P` onward. -/
theorem ExecWithin.prefix_bounds_program_init {B : Basis} {r w W P T k : ℕ} {c : Code B r}
    {out : Fin r} {input : List ℕ} {y : Data r} {s : State r}
    (he : ExecWithin w c (.init input) y T) (hc : ¬c.ReadsWidth) (hw : w ≤ W)
    (hi : InputFits w input) (hP : 2 ^ w ≤ P)
    (hr : Runs W (c.program out) (State.init input) s k) :
    (∀ i, s.data.regs i < P) ∧ (∀ a, s.data.mem a < P) ∧
      ∀ a, P ≤ a → s.data.mem a = 0 := by
  obtain ⟨_, _, hex⟩ := he
  exact hr.prefix_bounds_init (Code.not_readsWidth_program hc out) hw hi (hex.executes out) hP

/-- Certificate that a width-independent structured program `code` halts from `State.init (inp a)`
at minimum width `wMin a` within `time a` instructions in a state satisfying `post a`, with
minimum-width word universe `2 ^ wMin a` bounded by `wordEnv a`. -/
structure FlatEndpoint {B : Basis} {r : ℕ} {α : Type*}
    (code : Code B r) (out : Fin r) (wMin wordEnv : α → ℕ)
    (inp : α → List ℕ) (time : α → ℕ) (post : α → Data r → Prop) : Prop where
  /-- The structured program never inspects the physical word width. -/
  not_readsWidth : ¬code.ReadsWidth
  /-- Every instance's encoded input fits at its minimum admitted width. -/
  inputFits_min (a : α) : InputFits (wMin a) (inp a)
  /-- The minimum width's word universe is bounded by the physical-width-independent envelope. -/
  two_pow_wMin_le (a : α) : 2 ^ wMin a ≤ wordEnv a
  /-- At `wMin a`, the structured program reaches a state satisfying `post a` within `time a`. -/
  exec_min (a : α) : ∃ y, ExecWithin (wMin a) code (.init (inp a)) y (time a) ∧ post a y

namespace FlatEndpoint

variable {B : Basis} {r : ℕ} {α : Type*} {code : Code B r} {out : Fin r}
  {wMin wordEnv : α → ℕ} {inp : α → List ℕ} {time : α → ℕ} {post : α → Data r → Prop}

/-- The compiled flat program never inspects the physical word width. -/
theorem program_not_readsWidth
    (E : FlatEndpoint code out wMin wordEnv inp time post) :
    ¬(code.program out).ReadsWidth :=
  Code.not_readsWidth_program E.not_readsWidth out

/-- Every physical width `W ≥ wMin a` admits the encoded input `inp a`. -/
theorem inputFits (E : FlatEndpoint code out wMin wordEnv inp time post)
    (a : α) {W : ℕ} (hW : wMin a ≤ W) : InputFits W (inp a) :=
  (E.inputFits_min a).mono hW

/-- At every physical width `W ≥ wMin a`, the compiled flat program runs from `State.init (inp a)`
to a `W`-bounded terminal state satisfying `post a` within `time a` instructions and halts in one
further instruction. -/
theorem runs (E : FlatEndpoint code out wMin wordEnv inp time post)
    (a : α) {W : ℕ} (hW : wMin a ≤ W) :
    ∃ y n, n ≤ time a ∧
      Runs W (code.program out) (State.init (inp a)) ⟨code.size, y⟩ n ∧
      Executes W (code.program out) (State.init (inp a)) (y.regs out) (n + 1) ∧
      y.Bounded W ∧ post a y := by
  obtain ⟨y, hy, hpost⟩ := E.exec_min a
  have hyW : ExecWithin W code (.init (inp a)) y (time a) :=
    hy.mono_width E.not_readsWidth hW
  obtain ⟨n, hn, hruns, hexec⟩ := hyW.to_program out
  exact ⟨y, n, hn, hruns, hexec,
    (hy.bounded (Data.Bounded.init (E.inputFits_min a))).mono hW, hpost⟩

/-- At every physical width `W ≥ wMin a`, every reachable prefix of `code.program out` from
`State.init (inp a)` has register and memory words below `wordEnv a` and zero memory from
`wordEnv a` onward. -/
theorem prefix_bounds (E : FlatEndpoint code out wMin wordEnv inp time post)
    (a : α) {W k : ℕ} {s : State r} (hW : wMin a ≤ W)
    (hr : Runs W (code.program out) (State.init (inp a)) s k) :
    (∀ i, s.data.regs i < wordEnv a) ∧ (∀ q, s.data.mem q < wordEnv a) ∧
      ∀ q, wordEnv a ≤ q → s.data.mem q = 0 := by
  obtain ⟨_, hy, -⟩ := E.exec_min a
  exact hy.prefix_bounds_program_init E.not_readsWidth hW (E.inputFits_min a)
    (E.two_pow_wMin_le a) hr

end FlatEndpoint

end Cslib.WordRAM
