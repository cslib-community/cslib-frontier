/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Time.AcceptCount
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.HaltedReplay

/-!
# Detecting halting by an accepting count

The decider of the transfer theorem tries the clocks `τ = t₀, 2t₀, …` and stops at the first
clock at which every computation has halted. This module supplies the counting test for that
stopping rule in Complexitylib's model of fair-coin tables.

For a closed fair-coin table `m`, its *halt marker* `haltMark m` makes the same moves as `m`,
emits nothing while running, and emits `true` on the step on which it halts. Its replay on a
choice string therefore outputs `[true]` exactly when the replay of `m` has halted
(`runClosedCoins_haltMark`), so its accepting count on `τ` bits is `2 ^ τ` exactly when every
choice string of length `τ` makes `m` halt within `τ` steps (`acceptCount_haltMark_eq_two_pow_iff`).

For the choice table of a nondeterministic decider running within `t`, every choice string of
length greater than `N * t` halts, for the number `N` of actions
(`stepCoins_choiceTable_halted`): each simulated step costs at most `N` coins. Once every choice
string of length `τ` halts, a halted table ignores further coins, so an accepting computation of
any length is witnessed by a choice string of length exactly `τ`, and membership is a positive
accepting count at `τ` (`mem_iff_acceptCount_choiceTable_pos_of_halted`). Unlike Complexitylib's
`Turing.MultiTapeNTM.DecidesInTime.mem_iff_acceptCount_choiceTable_pos`, this needs no lower
bound on `τ` in terms of `t`: the counting test replaces knowledge of the time bound.

## Main definitions

* `Cslib.Complexity.NtimeDspace.HaltCount.haltMark`: the table accepting exactly the halting choice
strings.

## Main results

* `Cslib.Complexity.NtimeDspace.HaltCount.acceptCount_haltMark_eq_two_pow_iff`: the halt marker
accepts all
  `2 ^ τ` strings exactly when every replay of length `τ` has halted.
* `Cslib.Complexity.NtimeDspace.HaltCount.exists_haltCount_of_mem_NTIME`: the packaged statement for
a problem in
  `NTIME enc T` with an arbitrary bound `T`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.HaltCount

open _root_.Turing Cslib

section Marker

variable {k : ℕ} {S : Type} {input : List Bool}

/-- The action that moves like `a`, emitting `true` exactly when it halts. -/
def markAction (a : Turing.Action k Bool S) : Turing.Action k Bool S :=
  { a with output := if a.state.isNone then some true else none }

/-- **The halt marker** of a closed fair-coin table: the same moves, emitting `true` exactly on
the halting step and nothing otherwise. -/
def haltMark (m : MultiTapePTM k Bool S) : MultiTapePTM k Bool S where
  initial := m.initial
  tr s symbol work answer bit :=
    .step (markAction (MultiTapeMachine.Action.emptyOracleEquiv (m.tr s symbol work answer bit)))
      Empty.elim Empty.elim

/-- A configuration whose output records only whether it has halted. -/
def markCfg (c : Cfg k Bool S input) : Cfg k Bool S input :=
  { c with output := if c.state.isNone then [true] else [] }

/-- One step of the marker on a marked configuration is the marked step of the table. -/
theorem step_haltMark (m : MultiTapePTM k Bool S) (bit : Bool) (c : Cfg k Bool S input) :
    ((haltMark m).withCoin bit).toTM.step (markCfg c) =
      markCfg ((m.withCoin bit).toTM.step c) := by
  rcases hs : c.state with _ | q
  · have hs' : (markCfg c).state = none := hs
    rw [MultiTapeTM.step_of_halt hs', MultiTapeTM.step_of_halt hs]
  · have hs' : (markCfg c).state = some q := hs
    rw [MultiTapeTM.step_of_state hs', MultiTapeTM.step_of_state hs]
    simp only [MultiTapeMachine.toTM, MultiTapeTM.tr_ofTr]
    change (markAction (MultiTapeMachine.Action.emptyOracleEquiv
      (m.tr q c.inputSymbol c.workTapeSymbols Empty.elim bit))).apply (markCfg c) =
      markCfg ((MultiTapeMachine.Action.emptyOracleEquiv
        (m.tr q c.inputSymbol c.workTapeSymbols Empty.elim bit)).apply c)
    generalize MultiTapeMachine.Action.emptyOracleEquiv
      (m.tr q c.inputSymbol c.workTapeSymbols Empty.elim bit) = a
    rcases ha : a.state with _ | q' <;>
      simp [markCfg, markAction, Action.apply, hs, ha]

/-- Replaying coins on the marker marks the replay of the table. -/
theorem stepCoins_haltMark (m : MultiTapePTM k Bool S) (coins : List Bool)
    (c : Cfg k Bool S input) :
    (haltMark m).stepCoins coins (markCfg c) = markCfg (m.stepCoins coins c) := by
  induction coins generalizing c with
  | nil => rfl
  | cons bit coins ih =>
    rw [MultiTapePTM.stepCoins_cons, MultiTapePTM.stepCoins_cons, step_haltMark, ih]

/-- **The marker's output** on a choice string is `[true]` if the table's replay has halted,
and empty otherwise. -/
theorem runClosedCoins_haltMark (m : MultiTapePTM k Bool S) (coins : List Bool)
    (input : List Bool) :
    (haltMark m).runClosedCoins coins input =
      if (m.stepCoins coins (Cfg.init m.initial input)).state.isNone then [true] else [] := by
  rw [MultiTapePTM.runClosedCoins_eq_output_stepCoins]
  have hinit : (Cfg.init (haltMark m).initial input : Cfg k Bool S input) =
      markCfg (Cfg.init m.initial input) := rfl
  rw [hinit, stepCoins_haltMark]
  rfl

theorem runClosedCoins_haltMark_eq_iff (m : MultiTapePTM k Bool S) (coins : List Bool)
    (input : List Bool) :
    (haltMark m).runClosedCoins coins input = [true] ↔
      (m.stepCoins coins (Cfg.init m.initial input)).state = none := by
  rw [runClosedCoins_haltMark]
  rcases (m.stepCoins coins (Cfg.init m.initial input)).state with _ | q <;> simp

/-- All `2 ^ n` strings are accepted exactly when every string of length `n` is. -/
theorem acceptCount_eq_two_pow_iff {α : Type} (V : α × List Bool → Bool) (a : α) (n : ℕ) :
    Complexity.acceptCount V a n = 2 ^ n ↔ ∀ w : List Bool, w.length = n → V (a, w) = true := by
  have hle := Complexity.acceptCount_le_two_pow (V := V) (a := a) (n := n)
  have hnot := Complexity.acceptCount_not V a n
  have hpos := Complexity.acceptCount_pos_iff (V := fun x => !V x) (a := a) (n := n)
  constructor
  · intro h w hw
    by_contra hV
    have : 0 < Complexity.acceptCount (fun x => !V x) a n := hpos.mpr ⟨w, hw, by simpa using hV⟩
    omega
  · intro h
    have : ¬ 0 < Complexity.acceptCount (fun x => !V x) a n := by
      rintro hlt
      obtain ⟨w, hw, hV⟩ := hpos.mp hlt
      simp [h w hw] at hV
    omega

/-- **The halting count.** The marker accepts all `2 ^ τ` choice strings exactly when every
choice string of length `τ` makes the table halt within `τ` steps. -/
theorem acceptCount_haltMark_eq_two_pow_iff (m : MultiTapePTM k Bool S) (input : List Bool)
    (τ : ℕ) :
    (haltMark m).acceptCount input τ = 2 ^ τ ↔
      ∀ coins : List Bool, coins.length = τ →
        (m.stepCoins coins (Cfg.init m.initial input)).state = none := by
  rw [MultiTapePTM.acceptCount, acceptCount_eq_two_pow_iff]
  simp only [decide_eq_true_eq, runClosedCoins_haltMark_eq_iff]

/-- A halted replay ignores further coins. -/
theorem stepCoins_of_halted (m : MultiTapePTM k Bool S) (coins : List Bool)
    {c : Cfg k Bool S input} (h : c.state = none) : m.stepCoins coins c = c := by
  induction coins with
  | nil => rfl
  | cons bit coins ih => rw [MultiTapePTM.stepCoins_cons, MultiTapeTM.step_of_halt h, ih]

theorem stepCoins_append_of_halted (m : MultiTapePTM k Bool S) (coins more : List Bool)
    {c : Cfg k Bool S input} (h : (m.stepCoins coins c).state = none) :
    m.stepCoins (coins ++ more) c = m.stepCoins coins c := by
  rw [MultiTapePTM.stepCoins_append, stepCoins_of_halted m more h]

end Marker

section ChoiceTable

open MultiTapeNTM MultiTapeNTM.ChoiceTable

variable {k : ℕ} {State : Type} [Finite State] {ntm : MultiTapeNTM k Bool State}
  {input : List Bool}

/-- The replayed configurations, with a lower bound on the coins they consume: a halted table,
or the simulation of a computation path before a candidate `j`, after at most
`N * time + j` coins, where `N` is the number of actions. -/
def Charged (ntm : MultiTapeNTM k Bool State) (input : List Bool) (n : ℕ)
    (b : Cfg k Bool (ScanState k State) input) : Prop :=
  b.state = none ∨ ∃ (p : ntm.ComputationPath input) (state : State)
    (j : Fin (Nat.card (Turing.Action k Bool State) + 1)),
    p.last.state = some state ∧ b = scanCfg p.last state j ∧
      n ≤ Nat.card (Turing.Action k Bool State) * p.time + j.val

theorem Charged.step {n : ℕ} {b : Cfg k Bool (ScanState k State) input}
    (h : Charged ntm input n b) (bit : Bool) :
    Charged ntm input (n + 1) ((ntm.choiceTable.withCoin bit).toTM.step b) := by
  rcases h with hhalt | ⟨p, state, j, hstate, rfl, hn⟩
  · exact .inl (by rw [MultiTapeTM.step_of_halt hhalt]; exact hhalt)
  rcases hj : (ntm.actions state p.last.inputSymbol p.last.workTapeSymbols)[j.val]? with
    _ | action
  · rw [step_scanCfg_reject hj]
    exact .inl rfl
  have hlt := (List.getElem?_eq_some_iff.mp hj).1
  have hlen := ntm.length_actions_le state p.last.inputSymbol p.last.workTapeSymbols
  have hmem := List.mem_of_getElem? hj
  have hstep : ntm.Step p.last (action.apply p.last) := by
    simp only [Step, hstate]
    exact ⟨action, (ntm.mem_actions).mp hmem, rfl⟩
  obtain ⟨q, hqtime, hq⟩ := ComputationPath.exists_snoc p hstep
  have htake : ∀ bit : Bool,
      bit = true ∨ j.val + 1 = (ntm.actions state p.last.inputSymbol
        p.last.workTapeSymbols).length →
      Charged ntm input (n + 1)
        ((ntm.choiceTable.withCoin bit).toTM.step (scanCfg p.last state j)) := by
    intro bit hbit
    rw [step_scanCfg_take hj hbit, ← hq]
    rcases hs : q.last.state with _ | next
    · left
      simp only [simCfg, hs, haltCfg]
    · right
      refine ⟨q, next, 0, hs, by simp only [simCfg, hs], ?_⟩
      rw [hqtime, Nat.mul_succ]
      simp only [Fin.val_zero, Nat.add_zero]
      omega
  by_cases hlast : j.val + 1 = (ntm.actions state p.last.inputSymbol
      p.last.workTapeSymbols).length
  · exact htake bit (.inr hlast)
  · cases bit
    · rw [step_scanCfg_skip hj hlast]
      exact .inr ⟨p, state, _, hstate, rfl, by simp only; omega⟩
    · exact htake true (.inl rfl)

theorem Charged.stepCoins {n : ℕ} {b : Cfg k Bool (ScanState k State) input}
    (h : Charged ntm input n b) (coins : List Bool) :
    Charged ntm input (n + coins.length) (ntm.choiceTable.stepCoins coins b) := by
  induction coins generalizing n b with
  | nil => exact h
  | cons bit coins ih =>
    rw [MultiTapePTM.stepCoins_cons, List.length_cons,
      show n + (coins.length + 1) = n + 1 + coins.length by omega]
    exact ih (h.step bit)

/-- **The choice table runs within `N * t + 1` coins.** If `ntm` runs within `t`, its choice
table halts on every choice string of more than `N * t` coins, for the number `N` of actions. -/
theorem stepCoins_choiceTable_halted {t : ℕ} (ht : ntm.RunsInTime input t) (coins : List Bool)
    (hlen : Nat.card (Turing.Action k Bool State) * t < coins.length) :
    (ntm.choiceTable.stepCoins coins (Cfg.init ntm.choiceTable.initial input)).state = none := by
  have hinit : Charged ntm input 0 (Cfg.init ntm.choiceTable.initial input) :=
    .inr ⟨⟨RelSeries.singleton _ (ntm.initCfg input), rfl⟩, ntm.q₀, 0, rfl, rfl, Nat.zero_le _⟩
  rcases (hinit.stepCoins coins) with hhalt | ⟨p, state, j, hstate, -, hn⟩
  · exact hhalt
  · exfalso
    have hp : p.time < t := by
      by_contra hge
      have := ht p (Nat.le_of_not_lt hge)
      rw [Cfg.Halted, hstate] at this
      exact Option.some_ne_none _ this
    have hj := j.isLt
    have : Nat.card (Turing.Action k Bool State) * p.time + j.val ≤
        Nat.card (Turing.Action k Bool State) * t := by
      calc _ ≤ Nat.card (Turing.Action k Bool State) * p.time +
              Nat.card (Turing.Action k Bool State) := by omega
        _ = Nat.card (Turing.Action k Bool State) * (p.time + 1) := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ hp
    omega

/-- **Membership at a halting clock.** Once every choice string of length `τ` makes the choice
table halt, the machine accepts exactly when some choice string of length `τ` makes the table
accept. No relation between `τ` and a time bound is assumed. -/
theorem accepts_iff_acceptCount_choiceTable_pos_of_halted {τ : ℕ}
    (hhalt : ∀ coins : List Bool, coins.length = τ →
      (ntm.choiceTable.stepCoins coins (Cfg.init ntm.choiceTable.initial input)).state = none) :
    ntm.Accepts input ↔ 0 < ntm.choiceTable.acceptCount input τ := by
  rw [MultiTapePTM.acceptCount, Complexity.acceptCount_pos_iff]
  constructor
  · rintro ⟨p, hp, hout⟩
    obtain ⟨coins, -, hcoins⟩ := exists_runClosedCoins_choiceTable p hp hout
    set full := coins ++ List.replicate τ false
    have hfull : τ ≤ full.length := by simp [full]
    refine ⟨full.take τ, by simp [List.length_take, hfull], ?_⟩
    have hrun : ntm.choiceTable.runClosedCoins full input = [true] := hcoins _
    refine decide_eq_true ?_
    rw [MultiTapePTM.runClosedCoins_eq_output_stepCoins] at hrun ⊢
    have htake := hhalt (full.take τ) (by simp [List.length_take, hfull])
    rw [← List.take_append_drop τ full, stepCoins_append_of_halted _ _ _ htake] at hrun
    exact hrun
  · rintro ⟨w, -, hw⟩
    exact accepts_of_runClosedCoins_choiceTable (coins := w) (by simpa using hw)

end ChoiceTable

open Cslib.Complexity in
/-- **Halting counts for `NTIME`.** A problem in `NTIME enc T`, for an arbitrary bound `T`, has
a choice table `M` and its halt marker `Mh` over a binary alphabet with finitely many states such
that, on `τ` choice bits:

* `Mh` accepts all `2 ^ τ` strings exactly when every replay of `M` on `τ` coins has halted;
* this holds whenever `τ ≥ c₁ * T n + c₂`, for constants `c₁` and `c₂`, on instances of encoded
  length `n`;
* when it holds, membership is a positive accepting count of `M`;
* both counts are at most `2 ^ τ`. -/
theorem exists_haltCount_of_mem_NTIME {α : Type} {enc : α ↪ List Bool} {T : ℕ → ℕ} {A : Set α}
    (h : A ∈ NTIME enc T) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (M Mh : MultiTapePTM k Bool State) (c₁ c₂ : ℕ),
      (∀ a τ, Mh.acceptCount (enc a) τ = 2 ^ τ ↔
        ∀ coins : List Bool, coins.length = τ →
          (M.stepCoins coins (Cfg.init M.initial (enc a))).state = none) ∧
      (∀ a τ, c₁ * T (enc a).length + c₂ ≤ τ → Mh.acceptCount (enc a) τ = 2 ^ τ) ∧
      (∀ a τ, Mh.acceptCount (enc a) τ = 2 ^ τ → (a ∈ A ↔ 0 < M.acceptCount (enc a) τ)) ∧
      (∀ a τ, M.acceptCount (enc a) τ ≤ 2 ^ τ ∧ Mh.acceptCount (enc a) τ ≤ 2 ^ τ) := by
  obtain ⟨c₁, c₂, k, State, hfinite, ntm, hntm⟩ := h
  set N := Nat.card (Turing.Action k Bool State)
  refine ⟨k, _, inferInstance, ntm.choiceTable, haltMark ntm.choiceTable, N * c₁, N * c₂ + 1,
    fun a τ => acceptCount_haltMark_eq_two_pow_iff _ _ _, fun a τ hτ => ?_, fun a τ hτ => ?_,
    fun a τ => ⟨acceptCount_le_two_pow, acceptCount_le_two_pow⟩⟩
  · rw [acceptCount_haltMark_eq_two_pow_iff]
    intro coins hcoins
    refine stepCoins_choiceTable_halted (hntm a).1 coins ?_
    rw [hcoins]
    nlinarith
  · rw [acceptCount_haltMark_eq_two_pow_iff] at hτ
    rw [(hntm a).2]
    exact accepts_iff_acceptCount_choiceTable_pos_of_halted hτ

end Cslib.Complexity.NtimeDspace.HaltCount
