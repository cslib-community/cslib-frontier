/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Nondeterministic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.OutView

/-!
# Runs of nondeterministic machines as sequences of step records

A computation path of a nondeterministic multi-tape machine is described here by one record per
time step, with no copy of the work tapes. A record (`StepRecord`) holds the state, the input head,
the work heads, the symbols read on the work tapes, the view of the output
(`Turing.OutView`) and the action taken. The work tapes are recovered from the records: before
step `t`, a cell holds what the latest earlier step at that cell left there, or a blank if no step
visited it (`StepRecord.tapeAt`).

A sequence of `N` records is *valid* (`StepRecord.Valid`) when it starts in the initial
configuration, each record follows from the previous one, the action of a running record is a
transition of the machine on the symbols it reads, every symbol read is what the tape holds, and
the last record has halted with output `[true]`. The machine accepts exactly when some valid
sequence exists, as soon as `N` exceeds a time bound of the machine
(`StepRecord.accepts_iff_exists_valid`).

This is the first step of a quasilinear version of the Cook–Levin reduction: the records have
`O(log N)` bits each, so a formula about them can have `N` times a polylogarithmic number of
clauses, while the tableau of `Cslib.Complexity.CookLevin.tableau` describes every cell at every
time. The tape condition refers to the latest earlier visit of a cell; checking it with a
sorting network is left to the formula.

## Main definitions

* `Cslib.Complexity.CookLevin.Quasilinear.StepRecord`: what a run does at one time.
* `Cslib.Complexity.CookLevin.Quasilinear.StepRecord.tapeAt`: the work tapes recovered from the
  records.
* `Cslib.Complexity.CookLevin.Quasilinear.StepRecord.Valid`: a valid sequence of records.

## Main results

* `Cslib.Complexity.CookLevin.Quasilinear.StepRecord.tapeAt_eq_of_latest`,
  `Cslib.Complexity.CookLevin.Quasilinear.StepRecord.tapeAt_eq_none`: a cell holds what its
  latest earlier visit left there, or a blank.
* `Cslib.Complexity.CookLevin.Quasilinear.StepRecord.accepts_of_valid`: a valid sequence gives an
  accepting computation path.
* `Cslib.Complexity.CookLevin.Quasilinear.StepRecord.exists_valid_of_accepts`: an accepting
  machine within time `T` has a valid sequence of every length `N > T`.
* `Cslib.Complexity.CookLevin.Quasilinear.StepRecord.accepts_iff_exists_valid`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 2.3.
-/

@[expose] public section

namespace Cslib.Complexity.CookLevin.Quasilinear

open Turing

variable {k : ℕ} {State : Type}

/-- What a run does at one time: the state, the input head (shifted by one, as in
`Turing.Cfg.inputPos`), the work heads, the symbols read on the work tapes, the view of the output
written so far, and the action taken. The action matters only when the state is running. -/
structure StepRecord (k : ℕ) (State : Type) where
  /-- the state, or `none` once halted -/
  state : Option State
  /-- the position of the input head, shifted by one -/
  inPos : ℕ
  /-- the positions of the work heads -/
  pos : Fin k → ℤ
  /-- the symbols read on the work tapes -/
  reads : Fin k → Option Bool
  /-- the view of the output written so far -/
  out : OutView
  /-- the action taken, when running -/
  action : Action k Bool State

namespace StepRecord

/-- The input-head position after a move on an input of length `n`, clamped to `[0, n + 1]` as in
`Turing.moveInputPos`. -/
def moveIn (n p : ℕ) (m : SignType) : ℕ :=
  (min ((n : ℤ) + 1) (max 0 ((p : ℤ) + (m : ℤ)))).toNat

/-- The symbol under the input head at the shifted position `p` on input `x`. -/
def inSym (x : List Bool) (p : ℕ) : Option Bool := if p = 0 then none else x[p - 1]?

/-- The contents of the cell under work head `j` after the step: what the action writes, or what
was read when it writes nothing or the record has halted. -/
def cellAfter (r : StepRecord k State) (j : Fin k) : Option Bool :=
  match r.state with
  | none => r.reads j
  | some _ => (r.action.workTapes j).1.getD (r.reads j)

/-- The fields of `r'` that the step of `r` determines: a halted record stays where it is, and a
running record applies its action. -/
def Follows (n : ℕ) (r r' : StepRecord k State) : Prop :=
  match r.state with
  | none => r'.state = none ∧ r'.inPos = r.inPos ∧ r'.pos = r.pos ∧ r'.out = r.out
  | some _ => r'.state = r.action.state ∧ r'.inPos = moveIn n r.inPos r.action.inputTape ∧
      r'.pos = (fun j => r.pos j + ((r.action.workTapes j).2 : ℤ)) ∧
      r'.out = r.out.push r.action.output

/-- Cell `z` of work tape `j` before step `t`: what the latest earlier step at that cell left
there, or a blank. -/
def tapeAt (R : ℕ → StepRecord k State) (j : Fin k) : ℕ → ℤ → Option Bool
  | 0, _ => none
  | t + 1, z => if (R t).pos j = z then (R t).cellAfter j else tapeAt R j t z

/-- A cell holds what its latest earlier visit left there. -/
theorem tapeAt_eq_of_latest {R : ℕ → StepRecord k State} {j : Fin k} {t t' : ℕ} {z : ℤ}
    (ht' : t' < t) (hz : (R t').pos j = z)
    (hmax : ∀ s, t' < s → s < t → (R s).pos j ≠ z) : tapeAt R j t z = (R t').cellAfter j := by
  induction t with
  | zero => omega
  | succ t ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht' with h | rfl
    · rw [tapeAt, ite_eq_right (hmax t h (by omega))]
      exact ih h fun s hs hst => hmax s hs (by omega)
    · rw [tapeAt, ite_eq_left hz]

/-- A cell that no earlier step visited is blank. -/
theorem tapeAt_eq_none {R : ℕ → StepRecord k State} {j : Fin k} {t : ℕ} {z : ℤ}
    (h : ∀ s < t, (R s).pos j ≠ z) : tapeAt R j t z = none := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [tapeAt, ite_eq_right (h t (by omega))]
    exact ih fun s hs => h s (by omega)

/-- A valid sequence of `N` records for `ntm` on input `x`: it starts in the initial configuration,
each record follows from the previous one, the action of a running record is a transition on the
symbols it reads, every symbol read is what the tape holds, and the last record has halted with
output `[true]`. -/
structure Valid (ntm : MultiTapeNTM k Bool State) (x : List Bool) (N : ℕ)
    (R : ℕ → StepRecord k State) : Prop where
  /-- the machine starts in its initial state -/
  init_state : (R 0).state = some ntm.q₀
  /-- the input head starts on the first cell -/
  init_inPos : (R 0).inPos = 1
  /-- the work heads start at `0` -/
  init_pos : ∀ j, (R 0).pos j = 0
  /-- the output starts empty -/
  init_out : (R 0).out = .empty
  /-- each record follows from the previous one -/
  follows : ∀ t, t + 1 < N → (R t).Follows x.length (R (t + 1))
  /-- the action of a running record is a transition on the symbols it reads -/
  trans : ∀ t < N, ∀ q, (R t).state = some q →
    ntm.Tr q (inSym x (R t).inPos) (R t).reads (R t).action
  /-- every symbol read is what the tape holds -/
  reads_eq : ∀ t < N, ∀ j, (R t).reads j = tapeAt R j t ((R t).pos j)
  /-- the last record has halted -/
  final_state : (R (N - 1)).state = none
  /-- the last record has output `[true]` -/
  final_out : (R (N - 1)).out = .one true

/-! ### From records to configurations -/

section Soundness

variable {ntm : MultiTapeNTM k Bool State} {x : List Bool} {N : ℕ} {R : ℕ → StepRecord k State}

/-- The output written before step `t`. -/
private def outList (R : ℕ → StepRecord k State) : ℕ → List Bool
  | 0 => []
  | t + 1 => outList R t ++
      match (R t).state with
      | none => []
      | some _ => (R t).action.output.toList

/-- The input head stays within the input after a move. -/
theorem moveIn_le (n p : ℕ) (m : SignType) : moveIn n p m ≤ n + 1 := by
  unfold moveIn
  omega

/-- The input position after a move agrees with `StepRecord.moveIn`. -/
theorem val_moveInputPos {n : ℕ} (p : Fin (n + 2)) (m : SignType) :
    (moveInputPos p m).val = moveIn n p.val m := by
  have h := val_moveInputPos_eq p m
  unfold moveIn
  omega

/-- The input head of a valid sequence of records stays within the input. -/
theorem inPos_le (hR : Valid ntm x N R) : ∀ t, t < N → (R t).inPos ≤ x.length + 1
  | 0, _ => by rw [hR.init_inPos]; omega
  | t + 1, ht => by
    have hf := hR.follows t ht
    unfold Follows at hf
    split at hf
    · rw [hf.2.1]; exact inPos_le hR t (by omega)
    · rw [hf.2.1]; exact moveIn_le _ _ _

private theorem ofList_outList (hR : Valid ntm x N R) :
    ∀ t, t < N → OutView.ofList (outList R t) = (R t).out
  | 0, _ => by rw [hR.init_out]; rfl
  | t + 1, ht => by
    have hf := hR.follows t ht
    have ih := ofList_outList hR t (by omega)
    rw [outList]
    rcases hs : (R t).state with _ | q <;> simp only [Follows, hs] at hf <;> simp only []
    · rw [List.append_nil, ih, hf.2.2.2]
    · rw [OutView.ofList_append_toList, ih, hf.2.2.2]

/-- The configuration before step `t`, with the input head clamped into range. -/
private def cfgOf (R : ℕ → StepRecord k State) (x : List Bool) (t : ℕ) : Cfg k Bool State x where
  state := (R t).state
  inputPos := ⟨min (R t).inPos (x.length + 1), by omega⟩
  workTapes j := tapeAt R j t
  workTapePos j := (R t).pos j
  output := outList R t

private theorem inputPos_cfgOf (hR : Valid ntm x N R) {t : ℕ} (ht : t < N) :
    ((cfgOf R x t).inputPos : ℕ) = (R t).inPos := by
  simp [cfgOf, inPos_le hR t ht]

/-- The symbol under the input head of a configuration, read off its shifted position. -/
private theorem inputSymbol_eq_inSym (c : Cfg k Bool State x) :
    c.inputSymbol = inSym x c.inputPos.val := by
  have hlt := c.inputPos.isLt
  unfold inSym
  by_cases h0 : c.inputPos.val = 0
  · rw [ite_eq_left h0, inputSymbol_eq_none_of_boundary (.inl h0)]
  · rw [ite_eq_right h0]
    by_cases h1 : c.inputPos.val = x.length + 1
    · rw [inputSymbol_eq_none_of_boundary (.inr h1), List.getElem?_eq_none (by omega)]
    · rw [inputSymbolInner (c.inputPos.val - 1) (by omega) (by omega),
        List.getElem?_eq_getElem (by omega)]

private theorem inputSymbol_cfgOf (hR : Valid ntm x N R) {t : ℕ} (ht : t < N) :
    (cfgOf R x t).inputSymbol = inSym x (R t).inPos := by
  rw [inputSymbol_eq_inSym, inputPos_cfgOf hR ht]

private theorem workTapeSymbols_cfgOf (hR : Valid ntm x N R) {t : ℕ} (ht : t < N) (j : Fin k) :
    (cfgOf R x t).workTapeSymbols j = (R t).reads j :=
  (hR.reads_eq t ht j).symm

private theorem tapeAt_succ_halted (hR : Valid ntm x N R) {t : ℕ} (ht : t < N) (j : Fin k)
    (h : (R t).state = none) : tapeAt R j (t + 1) = tapeAt R j t := by
  funext z
  rw [tapeAt]
  split_ifs with hz
  · rw [cellAfter, h, hR.reads_eq t ht j, hz]
  · rfl

private theorem step_cfgOf (hR : Valid ntm x N R) {t : ℕ} (ht : t + 1 < N) :
    ntm.Step (cfgOf R x t) (cfgOf R x (t + 1)) := by
  have hf := hR.follows t ht
  rcases hs : (R t).state with _ | q
  · have hst : (cfgOf R x t).state = none := hs
    simp only [Follows, hs] at hf
    obtain ⟨h1, h2, h3, h4⟩ := hf
    rw [MultiTapeNTM.step_of_halt hst]
    refine Cfg.ext (h1.trans hs.symm) ?_ ?_ ?_ ?_
    · simp [cfgOf, h2]
    · funext j
      exact tapeAt_succ_halted hR (by omega) j hs
    · funext j
      simp [cfgOf, h3]
    · simp [cfgOf, outList, hs]
  · have hst : (cfgOf R x t).state = some q := hs
    simp only [Follows, hs] at hf
    obtain ⟨h1, h2, h3, h4⟩ := hf
    unfold MultiTapeNTM.Step
    rw [hst]
    refine ⟨(R t).action, ?_, ?_⟩
    · rw [inputSymbol_cfgOf hR (by omega)]
      convert hR.trans t (by omega) q hs using 1
      funext j
      exact workTapeSymbols_cfgOf hR (by omega) j
    · refine Cfg.ext h1 ?_ ?_ ?_ ?_
      · apply Fin.ext
        rw [Action.apply_inputPos, val_moveInputPos, inputPos_cfgOf hR ht,
          inputPos_cfgOf hR (t := t) (by omega), h2]
      · funext j z
        simp only [cfgOf, Action.apply_workTapes, tapeAt]
        by_cases hz : (R t).pos j = z
        · rw [ite_eq_left hz, cellAfter, hs]
          rcases hw : ((R t).action.workTapes j).1 with _ | s
          · simp only [Option.getD_none]
            rw [hR.reads_eq t (by omega) j, hz]
          · simp [hz]
        · rw [ite_eq_right hz]
          rcases ((R t).action.workTapes j).1 with _ | s
          · rfl
          · simp [Function.update_of_ne (Ne.symm hz)]
      · funext j
        simp [cfgOf, h3]
      · simp [cfgOf, outList, hs]

private theorem cfgOf_zero (hR : Valid ntm x N R) : cfgOf R x 0 = ntm.initCfg x := by
  refine Cfg.ext hR.init_state ?_ ?_ ?_ rfl
  · apply Fin.ext
    simp [cfgOf, hR.init_inPos]
  · funext j z
    rfl
  · funext j
    simp [cfgOf, hR.init_pos]

/-- **A valid sequence of records gives an accepting computation path.** -/
theorem accepts_of_valid (hR : Valid ntm x N R) (hN : 0 < N) : ntm.Accepts x := by
  let p : ntm.RunPath x :=
    { length := N - 1
      toFun := fun i => cfgOf R x i
      step := fun i => step_cfgOf hR (t := i) (by omega) }
  refine ⟨⟨p, cfgOf_zero hR⟩, hR.final_state, ?_⟩
  change outList R (N - 1) = [true]
  exact OutView.ofList_eq_one_iff.1 ((ofList_outList hR _ (by omega)).trans hR.final_out)

end Soundness

/-! ### From configurations to records -/

section Completeness

variable {ntm : MultiTapeNTM k Bool State} {x : List Bool}

/-- An action that writes nothing, stays and halts. -/
private def idleAction : Action k Bool State := ⟨0, fun _ => (none, 0), none, none⟩

/-- The record of a configuration and an action. -/
private def ofCfg (c : Cfg k Bool State x) (a : Action k Bool State) : StepRecord k State :=
  ⟨c.state, c.inputPos.val, c.workTapePos, c.workTapeSymbols, OutView.ofList c.output, a⟩

/-- The configuration at time `t` of a run path, clamped to its last configuration. -/
private noncomputable def cfgAt (p : ntm.RunPath x) (t : ℕ) : Cfg k Bool State x :=
  p ⟨min t p.length, by omega⟩

/-- An action that the step from time `t` of a run path takes, when it is running. -/
private noncomputable def actionAt (p : ntm.RunPath x) (t : ℕ) : Action k Bool State := by
  classical
  exact if h : ∃ a : Action k Bool State, ∀ q, (cfgAt p t).state = some q →
      ntm.Tr q (cfgAt p t).inputSymbol (cfgAt p t).workTapeSymbols a ∧
        cfgAt p (t + 1) = a.apply (cfgAt p t)
    then h.choose else idleAction

private theorem actionAt_spec (p : ntm.RunPath x) {t : ℕ} (ht : t < p.length) {q : State}
    (hq : (cfgAt p t).state = some q) :
    ntm.Tr q (cfgAt p t).inputSymbol (cfgAt p t).workTapeSymbols (actionAt p t) ∧
      cfgAt p (t + 1) = (actionAt p t).apply (cfgAt p t) := by
  have hstep : ntm.Step (cfgAt p t) (cfgAt p (t + 1)) := by
    have := p.step ⟨t, ht⟩
    simpa [cfgAt, Nat.min_eq_left ht.le, Nat.min_eq_left ht] using this
  have hex : ∃ a : Action k Bool State, ∀ q, (cfgAt p t).state = some q →
      ntm.Tr q (cfgAt p t).inputSymbol (cfgAt p t).workTapeSymbols a ∧
        cfgAt p (t + 1) = a.apply (cfgAt p t) := by
    unfold MultiTapeNTM.Step at hstep
    rw [hq] at hstep
    obtain ⟨a, ha, he⟩ := hstep
    exact ⟨a, fun q' hq' => by
      rw [hq] at hq'
      cases hq'
      exact ⟨ha, he⟩⟩
  unfold actionAt
  rw [dite_eq_left hex]
  exact hex.choose_spec q hq

private theorem cfgAt_zero (p : ntm.RunPath x) : cfgAt p 0 = p.head := by
  unfold cfgAt RelSeries.head
  congr 1

/-- The records of a run path. -/
private noncomputable def recordsOf (p : ntm.RunPath x) (t : ℕ) : StepRecord k State :=
  ofCfg (cfgAt p t) (actionAt p t)

private theorem step_cfgAt_halted (p : ntm.RunPath x) {t : ℕ} (ht : t < p.length)
    (h : (cfgAt p t).state = none) : cfgAt p (t + 1) = cfgAt p t := by
  have hstep : ntm.Step (cfgAt p t) (cfgAt p (t + 1)) := by
    have := p.step ⟨t, ht⟩
    simpa [cfgAt, Nat.min_eq_left ht.le, Nat.min_eq_left ht] using this
  exact (MultiTapeNTM.step_of_halt h).1 hstep

private theorem workTapes_cfgAt (p : ntm.RunPath x) (hp : p.head = ntm.initCfg x) (j : Fin k) :
    ∀ t, t ≤ p.length → (cfgAt p t).workTapes j = tapeAt (recordsOf p) j t
  | 0, _ => by
    rw [cfgAt_zero, hp]
    rfl
  | t + 1, ht => by
    have ih := workTapes_cfgAt p hp j t (by omega)
    funext z
    have hpos : (recordsOf p t).pos j = (cfgAt p t).workTapePos j := rfl
    rw [tapeAt, hpos]
    rcases hs : (cfgAt p t).state with _ | q
    · have hcell : (recordsOf p t).cellAfter j = (cfgAt p t).workTapeSymbols j := by
        simp [recordsOf, ofCfg, cellAfter, hs]
      rw [step_cfgAt_halted p (by omega) hs, ih, hcell]
      by_cases hz : (cfgAt p t).workTapePos j = z
      · rw [ite_eq_left hz, Cfg.workTapeSymbols, ih, hz]
      · rw [ite_eq_right hz]
    · rw [(actionAt_spec p (by omega) hs).2]
      have hcell : (recordsOf p t).cellAfter j =
          ((actionAt p t).workTapes j).1.getD ((cfgAt p t).workTapeSymbols j) := by
        simp [recordsOf, ofCfg, cellAfter, hs]
      rw [hcell]
      rcases hw : ((actionAt p t).workTapes j).1 with _ | s
      · simp only [Action.apply_workTapes, hw, Option.getD_none]
        by_cases hz : (cfgAt p t).workTapePos j = z
        · rw [ite_eq_left hz, Cfg.workTapeSymbols, hz]
        · rw [ite_eq_right hz, ih]
      · simp only [Action.apply_workTapes, hw, Option.getD_some]
        by_cases hz : (cfgAt p t).workTapePos j = z
        · rw [ite_eq_left hz, hz, Function.update_self]
        · rw [ite_eq_right hz, Function.update_of_ne (Ne.symm hz), ih]

private theorem follows_recordsOf (p : ntm.RunPath x) {t : ℕ} (ht : t < p.length) :
    (recordsOf p t).Follows x.length (recordsOf p (t + 1)) := by
  unfold Follows
  simp only [recordsOf, ofCfg]
  rcases hs : (cfgAt p t).state with _ | q
  · simp only
    rw [step_cfgAt_halted p ht hs]
    exact ⟨hs, rfl, rfl, rfl⟩
  · simp only
    rw [(actionAt_spec p ht hs).2]
    refine ⟨rfl, val_moveInputPos _ _, rfl, ?_⟩
    simp [Action.apply_output, OutView.ofList_append_toList]

private theorem inSym_recordsOf (p : ntm.RunPath x) (t : ℕ) :
    inSym x (recordsOf p t).inPos = (cfgAt p t).inputSymbol :=
  (inputSymbol_eq_inSym _).symm

/-- **An accepting machine within time `T` has a valid sequence of every length `N > T`.** -/
theorem exists_valid_of_accepts {T N : ℕ} (hT : ntm.RunsInTime x T) (hN : T < N)
    (hacc : ntm.Accepts x) : ∃ R : ℕ → StepRecord k State, Valid ntm x N R := by
  have hT' := hT.mono (show T ≤ N - 1 by omega)
  obtain ⟨p, hp, hout⟩ := (MultiTapeNTM.accepts_iff_exists_time_eq hT').1 hacc
  have hlen : p.length = N - 1 := hp
  have hhalt : p.last.Halted := hT' p (by rw [hp])
  have hlast : cfgAt p.toRunPath (N - 1) = p.last := by
    unfold cfgAt RelSeries.last
    congr 1
    ext
    simp [hlen]
  have h0 : cfgAt p.toRunPath 0 = ntm.initCfg x := (cfgAt_zero _).trans p.head_eq
  refine ⟨recordsOf p.toRunPath, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp [recordsOf, ofCfg, h0]
  · simp [recordsOf, ofCfg, h0]
  · intro j
    simp [recordsOf, ofCfg, h0]
  · simp [recordsOf, ofCfg, h0]
  · intro t ht
    exact follows_recordsOf p.toRunPath (by omega)
  · intro t ht q hq
    have hlt : t < p.length := by
      rcases Nat.lt_or_ge t (N - 1) with h | h
      · omega
      · exfalso
        have : t = N - 1 := by omega
        subst this
        simp only [recordsOf, ofCfg, hlast] at hq
        exact absurd hhalt (by rw [Cfg.Halted, hq]; simp)
    rw [inSym_recordsOf]
    exact (actionAt_spec p.toRunPath hlt hq).1
  · intro t ht j
    simp only [recordsOf, ofCfg, Cfg.workTapeSymbols]
    rw [workTapes_cfgAt p.toRunPath p.head_eq j t (by omega)]
  · simp only [recordsOf, ofCfg, hlast]
    exact hhalt
  · simp only [recordsOf, ofCfg, hlast, hout]
    rfl

end Completeness

/-- **A machine running within time `T` accepts exactly when it has a valid sequence of `N`
records**, for any `N > T`. -/
theorem accepts_iff_exists_valid {ntm : MultiTapeNTM k Bool State} {x : List Bool} {T N : ℕ}
    (hT : ntm.RunsInTime x T) (hN : T < N) :
    ntm.Accepts x ↔ ∃ R : ℕ → StepRecord k State, Valid ntm x N R :=
  ⟨exists_valid_of_accepts hT hN, fun ⟨_, hR⟩ => accepts_of_valid hR (by omega)⟩

/-- A work head is at most `t` cells from its start at time `t` of a valid sequence. -/
theorem abs_pos_le {ntm : MultiTapeNTM k Bool State} {x : List Bool} {N : ℕ}
    {R : ℕ → StepRecord k State} (hR : Valid ntm x N R) :
    ∀ t < N, ∀ j, |(R t).pos j| ≤ t := by
  intro t ht j
  induction t with
  | zero => rw [hR.init_pos j]; simp
  | succ t ih =>
    have ih := ih (by omega)
    have hf := hR.follows t ht
    unfold Follows at hf
    split at hf
    · rw [hf.2.2.1]
      omega
    · rw [hf.2.2.1]
      simp only
      have hm : |((((R t).action.workTapes j).2 : SignType) : ℤ)| ≤ 1 := by
        rcases ((R t).action.workTapes j).2 with _ | _ | _ <;> decide
      rw [abs_le] at ih hm ⊢
      push_cast
      omega

end StepRecord

end Cslib.Complexity.CookLevin.Quasilinear
