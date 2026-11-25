/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Run
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Equivalence
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas
public import Mathlib.Data.Fin.Tuple.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Run.FirstStep
import Mathlib.Algebra.BigOperators.Fin

/-!
# Shadowing the work tapes of a machine

`shadow m₀ m₁ tm` runs `tm` on its first `k` work tapes, while work tape `k + i` *shadows* work
tape `i`: its head moves with the head of tape `i` and marks every cell it reads, the start cell
with `m₀` and the other cells with `m₁` (`shadowTape`). When `tm` halts, the marks record the cells
the head of tape `i` visited before the halting step; only the cell under the head after the
halting step may be unmarked. A machine cannot tell these cells from the tape of `tm` alone, since
`tm` may leave blanks among the cells it wrote, but a machine that cleans up after `tm` can sweep
the marked cells (`Turing.MultiTapeTM.clearShadowed`).

The first step of `shadow m₀ m₁ tm` marks the start cells; after it, the machine mirrors `tm` step
by step (`Shadow.runFrom_cfg`), and if `tm` first halts at step `u` it has halted at step `u + 1`
(`runFrom_shadow`).

## Main definitions

* `Turing.MultiTapeTM.shadowTape`: the marks of a set of cells.
* `Turing.MultiTapeTM.shadow`: the shadowing machine.
* `Turing.MultiTapeMachine.shadow`: its choice-free explicit transition table.

## Main results

* `Turing.MultiTapeTM.runFrom_shadow`: the configuration of `shadow m₀ m₁ tm` when `tm` has
  halted.
* `Turing.MultiTapeTM.space_shadow`: `shadow m₀ m₁ tm` uses twice the space of `tm`.
* `Turing.MultiTapeMachine.toTM_shadow`: forgetting the explicit table recovers the legacy
  shadowing machine.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- The work tape a tape of `k + k` belongs to: tape `i` and its shadow `k + i` belong to `i`. -/
def pairIdx (j : Fin (k + k)) : Fin k :=
  Fin.addCases (motive := fun _ => Fin k) id id j

@[simp] theorem pairIdx_castAdd (i : Fin k) : pairIdx (Fin.castAdd k i) = i := by
  rw [pairIdx, Fin.addCases_left]; rfl

theorem pairIdx_natAdd (i : Fin k) : pairIdx (Fin.natAdd k i) = i := by
  rw [pairIdx, Fin.addCases_right]; rfl

/-- `pairIdx_natAdd` in simp normal form, since `Fin.natAdd k i` simplifies to `i.addNat k`. -/
@[simp] theorem pairIdx_addNat (i : Fin k) : pairIdx (i.addNat k) = i := by
  rw [← Fin.natAdd_eq_addNat, pairIdx_natAdd]

/-! ### The shadowing machine -/

variable (m₀ m₁ : Symbol)

/-- The shadow tape marking the cells `V`: `m₀` on the start cell, `m₁` on the other cells of `V`,
blank elsewhere. -/
def shadowTape (V : Finset ℤ) : ℤ → Option Symbol :=
  fun x => if x = 0 then some m₀ else if x ∈ V then some m₁ else none

variable {m₀ m₁}

/-- A shadow tape is blank exactly away from the start cell and the marked cells. -/
theorem shadowTape_eq_none_iff {V : Finset ℤ} {x : ℤ} :
    shadowTape m₀ m₁ V x = none ↔ x ≠ 0 ∧ x ∉ V := by
  unfold shadowTape
  split_ifs <;> simp_all

/-- Recording one more cell marks it, unless it is marked already. -/
theorem shadowTape_insert (V : Finset ℤ) (x : ℤ) :
    shadowTape m₀ m₁ (insert x V) = if (shadowTape m₀ m₁ V x).isNone
      then Function.update (shadowTape m₀ m₁ V) x (some m₁) else shadowTape m₀ m₁ V := by
  funext y
  by_cases hx : shadowTape m₀ m₁ V x = none
  · rw [hx, Option.isNone_none, ite_eq_left rfl]
    rw [shadowTape_eq_none_iff] at hx
    by_cases hy : y = x <;> simp [shadowTape, hy, hx.1]
  · rw [ite_eq_right (mt Option.isNone_iff_eq_none.1 hx)]
    rw [shadowTape_eq_none_iff, not_and_or, not_not, not_not] at hx
    by_cases hy : y = x
    · subst hy
      rcases hx with rfl | hx <;> simp_all [shadowTape]
    · simp [shadowTape, hy]

variable (m₀ m₁)

/-- `tm` on the first `k` of `k + k` work tapes, with tape `k + i` shadowing tape `i`. The state
`none` marks the start cells of the shadow tapes with `m₀`; in state `some q` the machine runs `tm`
in state `q` and marks the cells under the shadow heads that are not yet marked with `m₁`. -/
noncomputable def shadow (tm : MultiTapeTM k Symbol State) :
    MultiTapeTM (k + k) Symbol (Option State) :=
  ofTr none fun q inp work =>
    match q with
    | none =>
      ⟨0, Fin.append (fun _ => (none, 0)) fun _ => (some (some m₀), 0), none, some (some tm.q₀)⟩
    | some q =>
      let a := tm.tr q inp fun i => work (Fin.castAdd k i)
      ⟨a.inputTape, Fin.append a.workTapes fun i =>
          (if (work (Fin.natAdd k i)).isNone then some (some m₁) else none, (a.workTapes i).2),
        a.output, a.state.map some⟩

variable {m₀ m₁}

namespace Shadow

/-- The cells visited by the head of work tape `i` in the first `n` steps from `c`, not counting
the cell it is on after them. -/
noncomputable def visited (tm : MultiTapeTM k Symbol State) (c : Cfg k Symbol State input) (n : ℕ)
    (i : Fin k) : Finset ℤ :=
  (Finset.range n).image fun m => (tm.runFrom c m).workTapePos i

variable {tm : MultiTapeTM k Symbol State}

/-- One more step visits the cell the head was on. -/
theorem visited_succ (c : Cfg k Symbol State input) (n : ℕ) (i : Fin k) :
    visited tm c (n + 1) i = insert ((tm.runFrom c n).workTapePos i) (visited tm c n i) := by
  simp only [visited, Finset.range_add_one, Finset.image_insert]

/-- The cells visited up to step `n` are the cells visited before step `n` and the cell the head is
on at step `n`. -/
theorem visitedByTapeHead_eq_insert (c : Cfg k Symbol State input) (n : ℕ) (i : Fin k) :
    (MultiTapeNTM.RunPath.ofDeterministic tm c n).visitedByTapeHead i =
      insert ((tm.runFrom c n).workTapePos i) (visited tm c n i) := by
  ext x
  simp only [MultiTapeNTM.RunPath.mem_visitedByTapeHead_ofDeterministic, Finset.mem_insert,
    visited, Finset.mem_image, Finset.mem_range]
  exact ⟨by rintro ⟨m, hm, rfl⟩
            exact (Nat.lt_or_eq_of_le hm).elim (fun hlt => .inr ⟨m, hlt, rfl⟩)
              (by rintro rfl; exact .inl rfl),
    by rintro (rfl | ⟨m, hm, rfl⟩)
       exacts [⟨n, le_rfl, rfl⟩, ⟨m, hm.le, rfl⟩]⟩

variable (m₀ m₁)

/-- The configuration of `shadow m₀ m₁ tm` mirroring the configuration `c` of `tm`, with shadow
tape `i` marking the cells `V i`. -/
def cfg (c : Cfg k Symbol State input) (V : Fin k → Finset ℤ) :
    Cfg (k + k) Symbol (Option State) input :=
  ⟨c.state.map some, c.inputPos, Fin.append c.workTapes fun i => shadowTape m₀ m₁ (V i),
    Fin.append c.workTapePos c.workTapePos, c.output⟩

variable {m₀ m₁}

@[simp] theorem inputSymbol_cfg (c : Cfg k Symbol State input) (V : Fin k → Finset ℤ) :
    (cfg m₀ m₁ c V).inputSymbol = c.inputSymbol := rfl

/-- The first step marks the start cells. -/
theorem step_initCfg :
    (shadow m₀ m₁ tm).step ((shadow m₀ m₁ tm).initCfg input) =
      cfg m₀ m₁ (tm.initCfg input) fun _ => ∅ := by
  rw [step_of_state (q := none) rfl]
  simp only [shadow, tr_ofTr]
  refine Cfg.ext rfl (by simp [cfg, MultiTapeNTM.initCfg])
    (funext fun l => Fin.addCases
      (fun _ => by simp only [Action.apply, Fin.append_left, cfg, MultiTapeNTM.initCfg, Cfg.init])
      (fun _ => funext fun y => by
        simp only [Action.apply, Fin.append_right, cfg, MultiTapeNTM.initCfg, Cfg.init]
        by_cases hy : y = 0 <;> simp [shadowTape, hy]) l)
    (funext fun l => by
      refine Fin.addCases (fun _ => ?_) (fun _ => ?_) l <;>
        simp only [Action.apply, Fin.append_left, Fin.append_right, cfg, MultiTapeNTM.initCfg,
          Cfg.init] <;> rfl)
    (by simp [cfg, MultiTapeNTM.initCfg])

/-- A live step of `tm` is mirrored by one step of `shadow m₀ m₁ tm`, which marks the cells under
the heads. -/
theorem step_cfg {c : Cfg k Symbol State input} {q : State} (hq : c.state = some q)
    (V : Fin k → Finset ℤ) :
    (shadow m₀ m₁ tm).step (cfg m₀ m₁ c V) =
      cfg m₀ m₁ (tm.step c) fun i => insert (c.workTapePos i) (V i) := by
  have hsym : (cfg m₀ m₁ c V).workTapeSymbols = Fin.append c.workTapeSymbols
      fun i => shadowTape m₀ m₁ (V i) (c.workTapePos i) :=
    funext fun l => by
      refine Fin.addCases (fun _ => ?_) (fun _ => ?_) l <;>
        simp only [cfg, Cfg.workTapeSymbols, Fin.append_left, Fin.append_right]
  rw [step_of_state (q := some q) (by simp [cfg, hq]), step_of_state hq]
  simp only [shadow, tr_ofTr, hsym, inputSymbol_cfg, Fin.append_left, Fin.append_right]
  refine Cfg.ext rfl rfl
    (funext fun l => Fin.addCases (fun _ => by simp only [Action.apply, Fin.append_left, cfg])
      (fun _ => by
        simp only [Action.apply, Fin.append_right, cfg, shadowTape_insert]
        split_ifs <;> rfl) l)
    (funext fun l => by
      refine Fin.addCases (fun _ => ?_) (fun _ => ?_) l <;>
        simp only [Action.apply, cfg, Fin.append_left, Fin.append_right]) rfl

/-- While `tm` runs, `shadow m₀ m₁ tm` mirrors it, marking the visited cells. -/
theorem runFrom_cfg (c : Cfg k Symbol State input) (V : Fin k → Finset ℤ) (n : ℕ)
    (h : ∀ m < n, (tm.runFrom c m).state ≠ none) :
    (shadow m₀ m₁ tm).runFrom (cfg m₀ m₁ c V) n =
      cfg m₀ m₁ (tm.runFrom c n) fun i => V i ∪ visited tm c n i := by
  induction n with
  | zero =>
    simp only [visited, Finset.range_zero, Finset.image_empty, Finset.union_empty]
    rfl
  | succ n ih =>
    obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.1 (h n (by omega))
    rw [runFrom_succ, ih fun m hm => h m (by omega), step_cfg hq, runFrom_succ]
    congr 1 with i : 1
    rw [visited_succ, Finset.union_insert]

/-- After its first step, `shadow m₀ m₁ tm` mirrors the run of `tm` until `tm` halts. -/
theorem runFrom_succ_initCfg {u : ℕ} (h : ∀ m < u, ¬(tm.runFrom (tm.initCfg input) m).Halted)
    {m : ℕ} (hm : m ≤ u) :
    (shadow m₀ m₁ tm).runFrom ((shadow m₀ m₁ tm).initCfg input) (m + 1) =
      cfg m₀ m₁ (tm.runFrom (tm.initCfg input) m) (visited tm (tm.initCfg input) m) := by
  rw [runFrom_succ_eq_step, step_initCfg,
    runFrom_cfg _ _ _ fun m' hm' => h m' (by omega)]
  simp only [Finset.empty_union]

end Shadow

open Shadow

/-- If `tm` has not halted before step `u`, then after `u + 1` steps `shadow m₀ m₁ tm` holds the
configuration of `tm` after `u` steps, and shadow tape `i` marks the cells visited by the head of
tape `i` before step `u`. In particular, if `tm` halts at step `u`, so has `shadow m₀ m₁ tm` at
step `u + 1`. -/
theorem runFrom_shadow {tm : MultiTapeTM k Symbol State} {u : ℕ}
    (h : ∀ m < u, ¬(tm.runFrom (tm.initCfg input) m).Halted) :
    (shadow m₀ m₁ tm).runFrom ((shadow m₀ m₁ tm).initCfg input) (u + 1) =
      cfg m₀ m₁ (tm.runFrom (tm.initCfg input) u) (visited tm (tm.initCfg input) u) :=
  runFrom_succ_initCfg h le_rfl

/-- Until `tm` halts, `shadow m₀ m₁ tm` uses twice the space of `tm`. -/
theorem space_shadow {tm : MultiTapeTM k Symbol State} {u : ℕ}
    (h : ∀ m < u, ¬(tm.runFrom (tm.initCfg input) m).Halted) :
    (MultiTapeNTM.RunPath.ofDeterministic (shadow m₀ m₁ tm) ((shadow m₀ m₁ tm).initCfg input)
        (u + 1)).space =
      2 * (MultiTapeNTM.RunPath.ofDeterministic tm (tm.initCfg input) u).space := by
  have hpos (m) (hm : m ≤ u) :
      ((shadow m₀ m₁ tm).runFrom ((shadow m₀ m₁ tm).initCfg input) (m + 1)).workTapePos =
        Fin.append (tm.runFrom (tm.initCfg input) m).workTapePos
          (tm.runFrom (tm.initCfg input) m).workTapePos := by
    rw [runFrom_succ_initCfg h hm]
    rfl
  have hvis (l : Fin (k + k)) :
      (MultiTapeNTM.RunPath.ofDeterministic (shadow m₀ m₁ tm) ((shadow m₀ m₁ tm).initCfg input)
          (u + 1)).visitedByTapeHead l =
        (MultiTapeNTM.RunPath.ofDeterministic tm (tm.initCfg input) u).visitedByTapeHead
          (pairIdx l) := by
    ext x
    simp only [MultiTapeNTM.RunPath.mem_visitedByTapeHead_ofDeterministic]
    refine ⟨?_, fun ⟨m, hm, hx⟩ => ⟨m + 1, by omega, ?_⟩⟩
    · rintro ⟨_ | m, hm, rfl⟩
      · exact ⟨0, by omega, Fin.addCases (fun _ => by simp only [pairIdx_castAdd]; rfl)
          (fun _ => by simp only [pairIdx_natAdd]; rfl) l⟩
      · refine ⟨m, by omega, ?_⟩
        rw [hpos m (by omega)]
        refine Fin.addCases (fun _ => ?_) (fun _ => ?_) l <;>
          simp only [pairIdx_castAdd, pairIdx_natAdd, Fin.append_left, Fin.append_right]
    · rw [← hx, hpos m (by omega)]
      refine Fin.addCases (fun _ => ?_) (fun _ => ?_) l <;>
        simp only [pairIdx_castAdd, pairIdx_natAdd, Fin.append_left, Fin.append_right]
  simp only [MultiTapeNTM.RunPath.space, MultiTapeNTM.RunPath.spaceUsedByTape, hvis,
    Fin.sum_univ_add, pairIdx_castAdd, pairIdx_natAdd, two_mul]

end Turing.MultiTapeTM

namespace Turing.MultiTapeMachine

variable {k : ℕ} {Symbol State : Type*}

/-- Run an explicit transition table on the first half of doubled work tapes while the second
half records every visited cell. This is the choice-free table underlying the legacy shadow
machine. -/
def shadow (m₀ m₁ : Symbol) (machine : MultiTapeMachine k Symbol State Empty Id) :
    MultiTapeMachine (k + k) Symbol (Option State) Empty Id :=
  ofTr none fun state input work =>
    match state with
    | none =>
      ⟨0, Fin.append (fun _ => (none, 0)) fun _ => (some (some m₀), 0), none,
        some (some machine.initial)⟩
    | some state =>
      let action := Action.emptyOracleEquiv
        (machine.tr state input (fun i => work (Fin.castAdd k i)) Empty.elim)
      ⟨action.inputTape, Fin.append action.workTapes fun i =>
          (if (work (Fin.natAdd k i)).isNone then some (some m₁) else none,
            (action.workTapes i).2),
        action.output, action.state.map some⟩

/-- Forgetting the explicit shadow table recovers the legacy deterministic shadow machine. -/
theorem toTM_shadow (m₀ m₁ : Symbol)
    (machine : MultiTapeMachine k Symbol State Empty Id) :
    (machine.shadow m₀ m₁).toTM = MultiTapeTM.shadow m₀ m₁ machine.toTM := by
  simp only [shadow, toTM_ofTr, MultiTapeTM.shadow]
  congr 1 with state input work : 3
  cases state with
  | none => rfl
  | some state =>
      simp only [toTM, MultiTapeTM.tr_ofTr]

end Turing.MultiTapeMachine
