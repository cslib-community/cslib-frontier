/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Distributed.ConcurrentObjects.Linearizability
import CslibFrontier.Computability.Distributed.ConcurrentObjects.Progress
import CslibFrontier.Computability.Distributed.ConcurrentObjects.TreiberStack

/-! Herlihy–Wing linearizability, the non-blocking progress hierarchy, and Treiber's lock-free `CAS`
stack (checked as a `module` client with ordinary imports):
* positive and negative checks for `History.WellFormed`, `History.complete`, and real-time
  precedence `History.prec`;
* heterogeneous multi-object composition combining an atomic `Bool` register and a LIFO `ℕ` stack,
  proved linearizable via Herlihy–Wing Theorem 1 (`isLinearizable_iff_forall_obj`) and extended on
  a pending total invocation via Herlihy–Wing Theorem 2
  (`exists_linearizable_append_resp_of_total`);
* sequential consistency separations (`exists_sequentiallyConsistent_not_linearizable` and
  `exists_obj_sequentiallyConsistent_not_global`);
* non-blocking progress hierarchy checks (`IsWaitFree → IsLockFree → IsObstructionFree`, including
  `IsWaitFree → IsObstructionFree` over infinite `ℕ`), `decide`-checked 4-step `CAS` starvation on
  `casCounterSystem Bool`, and `decide`-checked 4-step livelock on `racingClaimSystem Bool`;
* multi-step interleaved traces of `treiberFreshNodeSystem` exercising `CAS` contention + retry,
  `treiberFreshNode_cas_fail_witnesses_intervening_cas`, an `H_3`-style early `pop` returning a
  concurrently pushed value before `push` emits its response, and
  `treiberFreshNode_isLinearizable` / `treiberFreshNode_isLockFree` over both concrete `ℕ` and
  non-`DecidableEq` function values `ℕ → ℕ`. -/
set_option linter.privateModule false

namespace CslibFrontierTests.Distributed.ConcurrentObjects

open Cslib Cslib.Distributed.ConcurrentObjects

/-! ### 1. Histories, `WellFormed`, `complete`, and real-time precedence `<_H` -/

/-- Well-formed 2-process register history with one completed write, one overlapping completed read,
and one trailing pending read. -/
def sampleRegHistory : History Bool (fun _ : Unit => RegOp ℕ) (fun _ : Unit => RegResp ℕ) :=
  [.inv false () (.write 7),
   .inv true () .read,
   .resp false () .writeAck,
   .resp true () (.readRet 7),
   .inv false () .read]

theorem sampleRegHistory_wellFormed : History.WellFormed sampleRegHistory := by
  intro b
  cases b <;> trivial

/-- Ill-formed history where process `false` invokes twice consecutively without a response. -/
def doubleInvHistory : History Bool (fun _ : Unit => RegOp ℕ) (fun _ : Unit => RegResp ℕ) :=
  [.inv false () (.write 1), .inv false () .read]

theorem doubleInvHistory_not_wellFormed : ¬ History.WellFormed doubleInvHistory := by
  intro hwf
  exact hwf false

/-- `History.complete` drops trailing pending invocations while keeping completed call pairs in
exact history order. -/
theorem sampleRegHistory_complete :
    History.complete sampleRegHistory =
      [.inv false () (.write 7),
       .inv true () .read,
       .resp false () .writeAck,
       .resp true () (.readRet 7)] := by
  decide

theorem sampleRegHistory_complete_wellFormed :
    History.WellFormed (History.complete sampleRegHistory) :=
  History.complete_wellFormed sampleRegHistory_wellFormed

/-- Overlapping operations `⟨false, 0⟩` and `⟨true, 0⟩` in `sampleRegHistory` are incomparable under
real-time precedence `History.prec`. -/
theorem sampleRegHistory_overlapping_incomparable :
    ¬ History.prec sampleRegHistory ⟨false, 0⟩ ⟨true, 0⟩ ∧
      ¬ History.prec sampleRegHistory ⟨true, 0⟩ ⟨false, 0⟩ := by
  refine ⟨?_, ?_⟩ <;>
    (rintro ⟨r, i, hr, hi, hlt⟩
     simp only [sampleRegHistory, History.respPos, History.invPos, History.nthProcPos,
       List.nthFilterPos, Event.proc_inv, Event.proc_resp, Bool.true_eq_false, decide_true,
       decide_false, Bool.false_eq_true, ↓reduceIte, Nat.mul_zero, Nat.zero_add, Option.map_some,
       Option.some.injEq] at hr hi
     omega)

/-- Sequential operations in `sampleRegHistory`: operation `⟨false, 0⟩` (`resp` at index `2`)
strictly precedes `⟨false, 1⟩` (`inv` at index `4`). -/
theorem sampleRegHistory_sequential_prec :
    History.prec sampleRegHistory ⟨false, 0⟩ ⟨false, 1⟩ :=
  ⟨2, 4, rfl, rfl, by omega⟩

/-! ### 2. Herlihy–Wing Theorem 1 (Locality) & Theorem 2 (Nonblocking) on Register + Stack -/

/-- Heterogeneous 2-object family over `Obj = Bool`:
* `false`: atomic `Bool` register (`RegOp Bool` / `RegResp Bool`),
* `true`: LIFO `ℕ` stack (`StackOp ℕ` / `StackResp ℕ`). -/
abbrev HetOp : Bool → Type
  | false => RegOp Bool
  | true => StackOp ℕ

abbrev HetResp : Bool → Type
  | false => RegResp Bool
  | true => StackResp ℕ

instance : ∀ x : Bool, DecidableEq (HetOp x)
  | false => inferInstanceAs (DecidableEq (RegOp Bool))
  | true => inferInstanceAs (DecidableEq (StackOp ℕ))

instance : ∀ x : Bool, DecidableEq (HetResp x)
  | false => inferInstanceAs (DecidableEq (RegResp Bool))
  | true => inferInstanceAs (DecidableEq (StackResp ℕ))

def hetSpec : (x : Bool) → SeqSpec Bool HetOp HetResp x
  | false => SeqSpec.ofMachine false false registerStep
  | true => SeqSpec.ofMachine true ([] : List ℕ) stackStep

/-- Concurrent 2-process history across BOTH the `Bool` register (`false`) and `ℕ` stack (`true`),
including overlapping calls and a trailing pending `push 99` on the stack:
1. `false` invokes `push 10` on stack `true`,
2. `true` writes `true` to register `false` (and receives `.writeAck`),
3. `false` completes `push 10` on stack `true`,
4. `true` pops `some 10` from stack `true`,
5. `false` reads `true` from register `false`,
6. `true` invokes `push 99` on stack `true` (left pending). -/
def hetHistory : History Bool HetOp HetResp :=
  [.inv false true (.push 10),
   .inv true false (.write true),
   .resp true false .writeAck,
   .resp false true .pushAck,
   .inv true true .pop,
   .resp true true (.popRet (some 10)),
   .inv false false .read,
   .resp false false (.readRet true),
   .inv true true (.push 99)]

theorem hetHistory_wellFormed : History.WellFormed hetHistory := by
  intro b
  cases b <;> trivial

/-- Per-object subhistory `hetHistory | false` (register) is linearizable. -/
theorem hetHistory_reg_linearizable :
    IsLinearizable hetSpec (History.objSubhistory hetHistory false) := by
  let Hreg := History.objSubhistory hetHistory false
  have hwf : History.WellFormed Hreg := hetHistory_wellFormed.objSubhistory false
  refine ⟨Hreg, History.IsExtension.refl hwf, Hreg, ⟨rfl, rfl, rfl, rfl, trivial⟩, ?_, ?_, ?_⟩
  · intro x
    cases x <;> rw [hetSpec, SeqSpec.mem_ofMachine_allowed]
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
    · trivial
  · intro b
    cases b <;> rfl
  · intro _ _ _ _ hpr
    exact hpr

/-- Per-object subhistory `hetHistory | true` (stack, with trailing pending `push 99` dropped by
`complete`) is linearizable. -/
theorem hetHistory_stack_linearizable :
    IsLinearizable hetSpec (History.objSubhistory hetHistory true) := by
  let Hstk := History.objSubhistory hetHistory true
  have hwf : History.WellFormed Hstk := hetHistory_wellFormed.objSubhistory true
  let Sstk : History Bool HetOp HetResp :=
    [.inv false true (.push 10),
     .resp false true .pushAck,
     .inv true true .pop,
     .resp true true (.popRet (some 10))]
  refine ⟨Hstk, History.IsExtension.refl hwf, Sstk, ⟨rfl, rfl, rfl, rfl, trivial⟩, ?_, ?_, ?_⟩
  · intro x
    cases x <;> rw [hetSpec, SeqSpec.mem_ofMachine_allowed]
    · trivial
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  · intro b
    cases b <;> decide
  · intro e₀ e₁ hc₀ hc₁ hpr
    have hlenF : (History.procSubhistory Hstk false).length = 2 := rfl
    have hlenT : (History.procSubhistory Hstk true).length = 3 := rfl
    have he₀ : e₀ = ⟨false, 0⟩ := by
      rcases e₀ with ⟨b, idx⟩
      cases b
      · have hlen := (History.isCompletedOp_iff_lt_length Hstk ⟨false, idx⟩).mp hc₀
        dsimp only at hlen; rw [hlenF] at hlen
        exact congrArg (OpId.mk false) (by omega)
      · exfalso
        obtain ⟨r, i, hr, hi, hlt⟩ := hpr
        have hlen := (History.isCompletedOp_iff_lt_length Hstk ⟨true, idx⟩).mp hc₀
        dsimp only at hlen; rw [hlenT] at hlen
        have hidx : idx = 0 := by omega
        subst hidx
        have hr_val : History.respPos Hstk ⟨true, 0⟩ = some 3 := rfl
        rw [hr_val] at hr
        injection hr with hr_eq
        rcases e₁ with ⟨b₁, idx₁⟩
        cases b₁
        · have hc₁_len := (History.isCompletedOp_iff_lt_length Hstk ⟨false, idx₁⟩).mp hc₁
          dsimp only at hc₁_len; rw [hlenF] at hc₁_len
          have h1 : idx₁ = 0 := by omega
          subst h1
          have hi_val : History.invPos Hstk ⟨false, 0⟩ = some 0 := rfl
          rw [hi_val] at hi
          injection hi with hi_eq
          omega
        · have hc₁_len := (History.isCompletedOp_iff_lt_length Hstk ⟨true, idx₁⟩).mp hc₁
          dsimp only at hc₁_len; rw [hlenT] at hc₁_len
          have h1 : idx₁ = 0 := by omega
          subst h1
          have hi_val : History.invPos Hstk ⟨true, 0⟩ = some 2 := rfl
          rw [hi_val] at hi
          injection hi with hi_eq
          omega
    have he₁ : e₁ = ⟨true, 0⟩ := by
      subst he₀
      rcases e₁ with ⟨b₁, idx₁⟩
      cases b₁
      · have hlen := (History.isCompletedOp_iff_lt_length Hstk ⟨false, idx₁⟩).mp hc₁
        dsimp only at hlen; rw [hlenF] at hlen
        have h1 : idx₁ = 0 := by omega
        subst h1
        exact False.elim (History.prec_irrefl Hstk ⟨false, 0⟩ hpr)
      · have hlen := (History.isCompletedOp_iff_lt_length Hstk ⟨true, idx₁⟩).mp hc₁
        dsimp only at hlen; rw [hlenT] at hlen
        exact congrArg (OpId.mk true) (by omega)
    subst he₀; subst he₁
    exact ⟨1, 2, rfl, rfl, by omega⟩

/-- **Herlihy–Wing Theorem 1 (Locality)** composes the independent register and stack linearizations
into a global linearization of `hetHistory`, which also implies sequential consistency. -/
theorem hetHistory_isLinearizable : IsLinearizable hetSpec hetHistory :=
  (isLinearizable_iff_forall_obj hetSpec hetHistory_wellFormed).mpr fun x => by
    cases x
    · exact hetHistory_reg_linearizable
    · exact hetHistory_stack_linearizable

theorem hetHistory_isSequentiallyConsistent : IsSequentiallyConsistent hetSpec hetHistory :=
  hetHistory_isLinearizable.isSequentiallyConsistent

/-- **Herlihy–Wing Theorem 2 (Nonblocking)** produces a valid response for the pending `push 99`
invocation of process `true` in `hetHistory` without blocking. -/
theorem hetHistory_nonblocking_pending_push :
    ∃ res : HetResp true, IsLinearizable hetSpec (hetHistory ++ [.resp true true res]) :=
  exists_linearizable_append_resp_of_total (Op := HetOp) (Resp := HetResp) (x := true)
    (op := StackOp.push 99) hetHistory_isLinearizable
    (by
      rw [hetSpec]
      exact SeqSpec.isTotalOp_ofMachine (P := Bool) (Op := HetOp) (Resp := HetResp)
        true ([] : List ℕ) stackStep (StackOp.push 99))
    ⟨[⟨true, false, .write true, .writeAck⟩, ⟨true, true, .pop, .popRet (some 10)⟩], rfl⟩

/-- Separations between linearizability, sequential consistency, and locality (`H_7` and `H_8`). -/
theorem sc_separations_witnessed :
    (∃ H : History Bool (fun _ : Unit => RegOp Bool) (fun _ : Unit => RegResp Bool),
      History.WellFormed H ∧
      IsSequentiallyConsistent (fun x => registerSeqSpec x false) H ∧
      ¬ IsLinearizable (fun x => registerSeqSpec x false) H) ∧
    (∃ H : History Bool (fun _ : Bool => RegOp Bool) (fun _ : Bool => RegResp Bool),
      History.WellFormed H ∧
      (∀ x : Bool, IsSequentiallyConsistent (fun y => registerSeqSpec y false)
        (History.objSubhistory H x)) ∧
      ¬ IsSequentiallyConsistent (fun y => registerSeqSpec y false) H) :=
  ⟨exists_sequentiallyConsistent_not_linearizable, exists_obj_sequentiallyConsistent_not_global⟩

/-! ### 3. Non-Blocking Progress Hierarchy (`IsWaitFree → IsLockFree → IsObstructionFree`) -/

/-- On finite process sets (`Fin 3`), `atomicIncSystem` satisfies all three progress levels. -/
theorem atomicInc_fin3_hierarchy :
    (atomicIncSystem (Fin 3)).IsWaitFree ∧
      (atomicIncSystem (Fin 3)).IsLockFree ∧
      (atomicIncSystem (Fin 3)).IsObstructionFree := by
  have hwf := atomicIncSystem_isWaitFree (Fin 3)
  exact ⟨hwf, hwf.isLockFree, hwf.isObstructionFree⟩

/-- `IsWaitFree.isObstructionFree` holds over infinite process sets (`ℕ`) without `[Finite P]`. -/
theorem atomicInc_nat_waitFree_and_obstructionFree :
    (atomicIncSystem ℕ).IsWaitFree ∧ (atomicIncSystem ℕ).IsObstructionFree := by
  have hwf := atomicIncSystem_isWaitFree ℕ
  exact ⟨hwf, hwf.isObstructionFree⟩

/-- Concrete 4-step starvation round on `casCounterSystem Bool`: `false` reads `0`, `true` reads `0`
and wins the `CAS` (`counter = 1`, `done = true`), and `false`'s `CAS` fails (`done = false`) and
retries from `.readCounter`. -/
theorem casCounter_starvation_round_trace :
    let s₀ : CASCounterState Bool :=
      { counter := 0, threads := fun b => if b then .readCounter else .readCounter }
    let r₁ := (casCounterSystem Bool).step s₀ false
    let r₂ := (casCounterSystem Bool).step r₁.1 true
    let r₃ := (casCounterSystem Bool).step r₂.1 true
    let r₄ := (casCounterSystem Bool).step r₃.1 false
    r₁.2 = false ∧ r₂.2 = false ∧ r₃.2 = true ∧ r₄.2 = false ∧
      r₄.1.counter = 1 ∧ r₄.1.threads false = .readCounter ∧ r₄.1.threads true = .idle := by
  decide

/-- Concrete 4-step livelock cycle on `racingClaimSystem Bool` returning to the exact starting state
with zero completions, contrasted with 1-step solo completion from the same state. -/
theorem racingClaim_livelock_vs_solo :
    let s₀ : RacingClaimState Bool :=
      { owner := some false, threads := fun b => if b then .writeClaim else .verifyClaim }
    let r₁ := (racingClaimSystem Bool).step s₀ true
    let r₂ := (racingClaimSystem Bool).step r₁.1 false
    let r₃ := (racingClaimSystem Bool).step r₂.1 false
    let r₄ := (racingClaimSystem Bool).step r₃.1 true
    let solo₀ := (racingClaimSystem Bool).step s₀ false
    r₁.2 = false ∧ r₂.2 = false ∧ r₃.2 = false ∧ r₄.2 = false ∧
      r₄.1.owner = s₀.owner ∧
      r₄.1.threads false = s₀.threads false ∧
      r₄.1.threads true = s₀.threads true ∧
      solo₀.2 = true ∧ solo₀.1.threads false = .idle := by
  decide

theorem progress_strict_hierarchy_witnessed :
    (∃ sys : ProgressSystem Bool, sys.IsLockFree ∧ ¬ sys.IsWaitFree) ∧
      (∃ sys : ProgressSystem Bool, sys.IsObstructionFree ∧ ¬ sys.IsLockFree) :=
  ⟨exists_lockFree_not_waitFree, exists_obstructionFree_not_lockFree⟩

/-! ### 4. Treiber's Lock-Free `CAS` Stack: Contention, Early Pop, and Higher-Order Values -/

/-- Executable test action for driving `treiberFreshNodeSystem` along concrete schedules. -/
inductive TreiberAction (P V : Type) where
  | invokePush (p : P) (v : V)
  | invokePop (p : P)
  | step (p : P)

/-- Apply one `TreiberAction` when enabled (no-op if disabled), preserving reachability without
requiring `[DecidableEq V]`. -/
def applyTreiberAction {P V : Type} [DecidableEq P]
    (s : TreiberFreshNodeState P V) : TreiberAction P V → TreiberFreshNodeState P V
  | .invokePush p v =>
    match s.threads p with
    | .idle =>
      { s with
          threads := Function.update s.threads p (.pushAlloc v)
          history := s.history ++ [.inv p () (.push v)] }
    | _ => s
  | .invokePop p =>
    match s.threads p with
    | .idle =>
      { s with
          threads := Function.update s.threads p .popRead
          history := s.history ++ [.inv p () .pop] }
    | _ => s
  | .step p =>
    match s.threads p with
    | .idle => s
    | _ => (treiberFreshNodeStep s p).1

def runTreiberTrace {P V : Type} [DecidableEq P]
    (acts : List (TreiberAction P V)) : TreiberFreshNodeState P V :=
  acts.foldl applyTreiberAction (treiberFreshNodeInit P V)

theorem applyTreiberAction_reachable {P V : Type} [DecidableEq P]
    {s : TreiberFreshNodeState P V} (hs : (treiberFreshNodeSystem P V).Reachable s)
    (act : TreiberAction P V) :
    (treiberFreshNodeSystem P V).Reachable (applyTreiberAction s act) := by
  cases act with
  | invokePush p v =>
    cases htp : s.threads p <;> simp only [applyTreiberAction, htp]
    any_goals exact hs
    exact hs.step (lbl := .invoke p) ⟨htp, Or.inl ⟨v, rfl⟩⟩
  | invokePop p =>
    cases htp : s.threads p <;> simp only [applyTreiberAction, htp]
    any_goals exact hs
    exact hs.step (lbl := .invoke p) ⟨htp, Or.inr rfl⟩
  | step p =>
    cases htp : s.threads p <;> simp only [applyTreiberAction, htp]
    · exact hs
    all_goals
      exact hs.step (lbl := .exec p (treiberFreshNodeStep s p).2)
        ⟨(by dsimp only [treiberFreshNodeSystem]; rw [htp]; intro h; nomatch h), rfl⟩

theorem runTreiberTrace_reachable {P V : Type} [DecidableEq P]
    (acts : List (TreiberAction P V)) :
    (treiberFreshNodeSystem P V).Reachable (runTreiberTrace acts) := by
  suffices ∀ s, (treiberFreshNodeSystem P V).Reachable s →
      (treiberFreshNodeSystem P V).Reachable (acts.foldl applyTreiberAction s) from
    this _ (ProgressSystem.Reachable.init _)
  intro s hs
  induction acts generalizing s with
  | nil => exact hs
  | cons a rest ih => exact ih _ (applyTreiberAction_reachable hs a)

/-- Interleaved 2-thread contention trace on `treiberFreshNodeSystem Bool ℕ`:
1. `false` invokes `push 10`, allocates node `0`, and reads `head = none`;
2. `true` invokes `push 20`, allocates node `1`, reads `head = none`, wins `pushCAS`
   (`head = some 1`), and returns `.pushAck`;
3. `false`'s `pushCAS` now **fails** (`some 1 ≠ none`), retries `pushRead` (`head = some 1`), wins
   its second `pushCAS` (`head = some 0`), and returns `.pushAck`;
4. `true` pops `some 10`, then `some 20`, then `none` (LIFO order!). -/
def treiberContentionActions : List (TreiberAction Bool ℕ) :=
  [ -- `false` starts `push 10` up to `pushCAS 10 0 none`
    .invokePush false 10, .step false, .step false,
    -- `true` completes `push 20`, changing `head` to `some 1`
    .invokePush true 20, .step true, .step true, .step true, .step true,
    -- `false` fails `pushCAS`, retries `pushRead`, succeeds `pushCAS`, and returns
    .step false, .step false, .step false, .step false,
    -- `true` pops `some 10` (4 steps: `popRead`, `popNext`, `popCAS`, `returning`)
    .invokePop true, .step true, .step true, .step true, .step true,
    -- `true` pops `some 20`
    .invokePop true, .step true, .step true, .step true, .step true,
    -- `true` pops `none` (2 steps: empty `popRead`, `returning`)
    .invokePop true, .step true, .step true ]

theorem treiberContention_history_lifo :
    (runTreiberTrace treiberContentionActions).history =
      [.inv false () (.push 10),
       .inv true () (.push 20),
       .resp true () .pushAck,
       .resp false () .pushAck,
       .inv true () .pop, .resp true () (.popRet (some 10)),
       .inv true () .pop, .resp true () (.popRet (some 20)),
       .inv true () .pop, .resp true () (.popRet none)] := by
  decide

theorem treiberContention_isLinearizable :
    IsLinearizable (fun _ : Unit => stackSeqSpec ℕ)
      (runTreiberTrace treiberContentionActions).history :=
  treiberFreshNode_isLinearizable (runTreiberTrace_reachable treiberContentionActions)

/-- Direct check of `treiberFreshNode_cas_fail_witnesses_intervening_cas` on the 4-step contention
window between `false`'s `pushRead` (`head = none`) and `false`'s failed `pushCAS`
(`head = some 1`). -/
theorem treiberContention_intervening_cas_witness :
    let sBase : TreiberFreshNodeState Bool ℕ :=
      runTreiberTrace [.invokePush false 10, .step false, .step false]
    let s₁ : TreiberFreshNodeState Bool ℕ := applyTreiberAction sBase (.invokePush true 20)
    let s₂ : TreiberFreshNodeState Bool ℕ := applyTreiberAction s₁ (.step true)
    let s₃ : TreiberFreshNodeState Bool ℕ := applyTreiberAction s₂ (.step true)
    let s₄ : TreiberFreshNodeState Bool ℕ := applyTreiberAction s₃ (.step true)
    let states : ℕ → TreiberFreshNodeState Bool ℕ
      | 0 => sBase | 1 => s₁ | 2 => s₂ | 3 => s₃ | _ => s₄
    let labels : ℕ → StepLabel Bool
      | 0 => .invoke true
      | 1 => .exec true false
      | 2 => .exec true false
      | _ => .exec true false
    ∃ (j : ℕ) (q : Bool) (resp : StackResp ℕ),
      j < 4 ∧ q ≠ false ∧ labels j = .exec q false ∧
        (states (j + 1)).head ≠ (states j).head ∧
        (states (j + 1)).threads q = .returning resp := by
  intro sBase s₁ s₂ s₃ s₄ states labels
  refine treiberFreshNode_cas_fail_witnesses_intervening_cas (k := 4) (p := false)
    (expected := none) ?_ (by decide) (by decide) ?_
  · intro i hi
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · exact ⟨by decide, Or.inl ⟨20, rfl⟩⟩
    · exact ⟨by dsimp only [treiberFreshNodeSystem]; decide, rfl⟩
    · exact ⟨by dsimp only [treiberFreshNodeSystem]; decide, rfl⟩
    · exact ⟨by dsimp only [treiberFreshNodeSystem]; decide, rfl⟩
  · intro i hi hproc
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hcases with rfl | rfl | rfl | rfl <;> exact Bool.noConfusion hproc

/-- `H_3`-style concurrent early-pop trace: `false` invokes `push 42` and executes `pushCAS` into
`.returning .pushAck` (pausing before emitting `.resp`), while `true` invokes `pop`, pops `42`, and
returns `some 42`! Even though `push 42` has no `.resp` in `s.history` yet,
`treiberFreshNode_isLinearizable` proves `s.history` is linearizable (via response extension
`R = [.resp false () .pushAck]`). -/
def treiberEarlyPopActions : List (TreiberAction Bool ℕ) :=
  [ .invokePush false 42, .step false, .step false, .step false,
    .invokePop true, .step true, .step true, .step true, .step true ]

theorem treiberEarlyPop_history_eq :
    (runTreiberTrace treiberEarlyPopActions).history =
      [.inv false () (.push 42),
       .inv true () .pop,
       .resp true () (.popRet (some 42))] := by
  decide

theorem treiberEarlyPop_isLinearizable :
    IsLinearizable (fun _ : Unit => stackSeqSpec ℕ)
      (runTreiberTrace treiberEarlyPopActions).history :=
  treiberFreshNode_isLinearizable (runTreiberTrace_reachable treiberEarlyPopActions)

/-- Both `treiberFreshNode_isLockFree` and `treiberFreshNode_isLinearizable` apply over higher-order
element types `V = ℕ → ℕ` that lack `DecidableEq`. -/
theorem treiber_higherOrder_lockFree_and_linearizable :
    (treiberFreshNodeSystem (Fin 4) (ℕ → ℕ)).IsLockFree ∧
      (treiberFreshNodeSystem (Fin 4) (ℕ → ℕ)).IsObstructionFree ∧
      IsLinearizable (fun _ : Unit => stackSeqSpec (ℕ → ℕ))
        (runTreiberTrace
          ([.invokePush (0 : Fin 4) Nat.succ, .step 0, .step 0, .step 0, .step 0])).history := by
  have hlf := treiberFreshNode_isLockFree (Fin 4) (ℕ → ℕ)
  exact ⟨hlf, hlf.isObstructionFree, treiberFreshNode_isLinearizable (runTreiberTrace_reachable _)⟩

end CslibFrontierTests.Distributed.ConcurrentObjects
