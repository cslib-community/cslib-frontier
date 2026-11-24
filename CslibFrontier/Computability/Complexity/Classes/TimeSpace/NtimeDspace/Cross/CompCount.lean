/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.CountingPP
import CslibFrontier.Foundations.Data.BitString.WordCount

/-!
# Counting computations

A closed fair-coin table `m : MultiTapePTM k Bool S` is a nondeterministic machine making a binary
choice at every step; a *computation* is the sequence of choices of a run up to its halting step.
A computation of length `h ≤ τ` is represented by its *canonical* coin string of length `τ`: the
`h` choices followed by `false`s (`CanonFrom`: every coin read after the halting step is `false`).
`compCount m out x τ` counts the canonical coin strings of length `τ` whose run halts with output
`out`, i.e. the computations of length at most `τ` with that output. This is the variant count of
the paper's Lemma 2.2 (d), over choice strings with a zero bit at every step after the machine has
halted. Once every run of length `τ₁` has
halted, the count no longer depends on the clock (`compCount_eq_of_halted`).

Two tables reduce these counts to accept counts, to which the clocked bits (`ClockedBits`) apply:

* the *drain* table `drain m` runs `m`, and when `m` halts keeps reading coins, failing (emitting
  `false`) at the first `true`; its accepting coin strings are the canonical strings with output
  `[true]` (`acceptCount_drain`);
* the *flip* table `flip m` negates every emitted bit, so its computations with output `[true]` are
  those of `m` with output `[false]` (`compCount_flip`).
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross.CompCount

open _root_.Turing Cslib

variable {k : ℕ} {S : Type} {input : List Bool}

/-! ### Canonical coin strings -/

section Canon

variable (m : MultiTapePTM k Bool S)

/-- Every coin read while the run has already halted is `false`. -/
def CanonFrom : Cfg k Bool S input → List Bool → Prop
  | _, [] => True
  | c, b :: cs => (c.state = none → b = false) ∧ CanonFrom ((m.withCoin b).toTM.step c) cs

theorem canonFrom_append (c : Cfg k Bool S input) (u v : List Bool) :
    CanonFrom m c (u ++ v) ↔ CanonFrom m c u ∧ CanonFrom m (m.stepCoins u c) v := by
  induction u generalizing c with
  | nil => simp [CanonFrom]
  | cons b u
      ih => simp only [List.cons_append, CanonFrom, ih, MultiTapePTM.stepCoins_cons, and_assoc]

theorem canonFrom_of_halted {c : Cfg k Bool S input} (h : c.state = none) (v : List Bool) :
    CanonFrom m c v ↔ ∀ b ∈ v, b = false := by
  induction v with
  | nil => simp [CanonFrom]
  | cons b v ih => simp [CanonFrom, h, ih]

end Canon

open Classical in
/-- **The computations of length at most `τ` with output `out`**, counted by their canonical coin
strings of length `τ`: the run halts within the `τ` coins with output `out`, and every coin read
after the halting step is `false`. -/
noncomputable def compCount (m : MultiTapePTM k Bool S) (out : List Bool) (x : List Bool)
    (τ : ℕ) : ℕ :=
  Complexity.acceptCount (fun p : List Bool × List Bool =>
    decide (CanonFrom m (Cfg.init m.initial p.1) p.2 ∧
      (m.stepCoins p.2 (Cfg.init m.initial p.1)).state = none ∧
      (m.stepCoins p.2 (Cfg.init m.initial p.1)).output = out)) x τ

/-- Every run on `T` coins has halted. -/
def HaltsWithin (m : MultiTapePTM k Bool S) (x : List Bool) (T : ℕ) : Prop :=
  ∀ coins : List Bool, coins.length = T → (m.stepCoins coins (Cfg.init m.initial x)).state = none

theorem HaltsWithin.mono {m : MultiTapePTM k Bool S} {x : List Bool} {T T' : ℕ}
    (h : HaltsWithin m x T) (hT : T ≤ T') : HaltsWithin m x T' :=
  halted_mono m x hT h

open Classical in
/-- **The count does not depend on the clock** once every run has halted. -/
theorem compCount_eq_of_halted {m : MultiTapePTM k Bool S} {x : List Bool} {τ₁ τ₂ : ℕ}
    (h : HaltsWithin m x τ₁) (hle : τ₁ ≤ τ₂) (out : List Bool) :
    compCount m out x τ₂ = compCount m out x τ₁ := by
  obtain ⟨d, rfl⟩ : ∃ d, τ₂ = τ₁ + d := ⟨τ₂ - τ₁, by omega⟩
  unfold compCount
  rw [Complexity.acceptCount_add, Complexity.acceptCount, Finset.card_filter]
  refine Finset.sum_congr rfl fun u _ => ?_
  set c := m.stepCoins (List.ofFn u) (Cfg.init m.initial x)
  have hc : c.state = none := h _ (by simp)
  have key : ∀ v : List Bool,
      (CanonFrom m (Cfg.init m.initial x) (List.ofFn u ++ v) ∧
        (m.stepCoins (List.ofFn u ++ v) (Cfg.init m.initial x)).state = none ∧
        (m.stepCoins (List.ofFn u ++ v) (Cfg.init m.initial x)).output = out) ↔
      ((CanonFrom m (Cfg.init m.initial x) (List.ofFn u) ∧ c.state = none ∧ c.output = out) ∧
        ∀ b ∈ v, b = false) := by
    intro v
    rw [canonFrom_append, MultiTapePTM.stepCoins_append, HaltCount.stepCoins_of_halted m v hc,
      canonFrom_of_halted m hc]
    tauto
  by_cases hP : CanonFrom m (Cfg.init m.initial x) (List.ofFn u) ∧ c.state = none ∧
      c.output = out
  · rw [ite_eq_left (decide_eq_true hP)]
    rw [Complexity.acceptCount_congr (W := fun p => decide (∀ b ∈ p.2, b = false))
      (fun v => by
        rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq, key v]
        exact ⟨fun h => h.2, fun h => ⟨hP, h⟩⟩)]
    have hw : ∀ w : Fin d → Bool, (decide (∀ b ∈ List.ofFn w, b = false) = true) ↔
        ((!(List.ofFn w).any fun b => b) = true) := fun w => by simp
    unfold Complexity.acceptCount
    rw [← BitString.card_filter_not_any d]
    exact congrArg Finset.card (Finset.filter_congr fun w _ => hw w)
  · rw [ite_eq_right (fun h => hP (of_decide_eq_true h))]
    rw [Complexity.acceptCount_congr (W := fun _ => false)
      (fun v => by
        rw [Bool.eq_iff_iff, decide_eq_true_eq, key v]
        simp only [Bool.false_eq_true, iff_false, not_and]
        exact fun h' => absurd h' hP)]
    exact Complexity.acceptCount_false _ _

/-! ### The drain table -/

section Drain

variable (m : MultiTapePTM k Bool S)

/-- An action of `m`, continuing into the drain state `none` instead of halting. -/
def liftAction (a : Turing.Action k Bool S) : Turing.Action k Bool (Option S) :=
  { inputTape := a.inputTape, workTapes := a.workTapes, output := a.output, state := some a.state }

/-- In the drain state, a `false` coin changes nothing. -/
def stayAction : Turing.Action k Bool (Option S) := ⟨0, fun _ => (none, 0), none, some none⟩

/-- In the drain state, a `true` coin emits `false` and halts. -/
def failAction : Turing.Action k Bool (Option S) := ⟨0, fun _ => (none, 0), some false, none⟩

/-- **The drain table**: run `m`; once `m` halts, keep reading coins and fail at the first `true`.
-/
def drain : MultiTapePTM k Bool (Option S) where
  initial := some m.initial
  tr s symbol work answer bit :=
    .step (match s with
      | some
          q => liftAction (MultiTapeMachine.Action.emptyOracleEquiv (m.tr q symbol work answer bit))
      | none => if bit then failAction else stayAction) Empty.elim Empty.elim

/-- A configuration of `m` as one of the drain table (`none` becomes the drain state). -/
def liftCfg (c : Cfg k Bool S input) : Cfg k Bool (Option S) input := c.mapState some

theorem step_drain {c : Cfg k Bool S input} {b : Bool} (h : ¬ (c.state = none ∧ b = true)) :
    ((drain m).withCoin b).toTM.step (liftCfg c) = liftCfg ((m.withCoin b).toTM.step c) := by
  rcases hs : c.state with _ | q
  · have hb : b = false := by simpa [hs] using h
    subst hb
    have hs' : (liftCfg c).state = some none := by simp [liftCfg, hs]
    rw [MultiTapeTM.step_of_state hs', MultiTapeTM.step_of_halt hs]
    simp only [MultiTapeMachine.toTM, MultiTapeTM.tr_ofTr]
    change (stayAction (k := k) (S := S)).apply (liftCfg c) = liftCfg c
    ext <;> simp [stayAction, Action.apply, liftCfg, hs]
  · have hs' : (liftCfg c).state = some (some q) := by simp [liftCfg, hs]
    rw [MultiTapeTM.step_of_state hs', MultiTapeTM.step_of_state hs]
    simp only [MultiTapeMachine.toTM, MultiTapeTM.tr_ofTr]
    change (liftAction (MultiTapeMachine.Action.emptyOracleEquiv
      (m.tr q c.inputSymbol c.workTapeSymbols Empty.elim b))).apply (liftCfg c) =
      liftCfg ((MultiTapeMachine.Action.emptyOracleEquiv
        (m.tr q c.inputSymbol c.workTapeSymbols Empty.elim b)).apply c)
    generalize MultiTapeMachine.Action.emptyOracleEquiv
      (m.tr q c.inputSymbol c.workTapeSymbols Empty.elim b) = a
    rfl

theorem step_drain_fail {c : Cfg k Bool S input} (hs : c.state = none) :
    (((drain m).withCoin true).toTM.step (liftCfg c)).state = none ∧
      (((drain m).withCoin true).toTM.step (liftCfg c)).output = c.output ++ [false] := by
  have hs' : (liftCfg c).state = some none := by simp [liftCfg, hs]
  rw [MultiTapeTM.step_of_state hs']
  simp only [MultiTapeMachine.toTM, MultiTapeTM.tr_ofTr]
  change ((failAction (k := k) (S := S)).apply (liftCfg c)).state = none ∧
    ((failAction (k := k) (S := S)).apply (liftCfg c)).output = c.output ++ [false]
  simp [failAction, Action.apply, liftCfg]

theorem append_false_ne (l : List Bool) : l ++ [false] ≠ [true] := by
  intro h
  have := congrArg List.getLast? h
  simp at this

/-- **The drain table accepts the canonical strings with output `[true]`.** -/
theorem output_drain (cs : List Bool) (c : Cfg k Bool S input) :
    ((drain m).stepCoins cs (liftCfg c)).output = [true] ↔
      CanonFrom m c cs ∧ (m.stepCoins cs c).output = [true] := by
  induction cs generalizing c with
  | nil => simp [CanonFrom, liftCfg]
  | cons b cs ih =>
    rw [MultiTapePTM.stepCoins_cons, MultiTapePTM.stepCoins_cons]
    by_cases hf : c.state = none ∧ b = true
    · obtain ⟨hs, rfl⟩ := hf
      obtain ⟨h1, h2⟩ := step_drain_fail m hs
      rw [HaltCount.stepCoins_of_halted _ cs h1, h2]
      simp only [CanonFrom, hs, forall_const]
      exact iff_of_false (append_false_ne _) (by simp)
    · rw [step_drain m hf, ih]
      simp only [CanonFrom]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨fun hs => by cases b <;> simp_all, h1⟩, h2⟩
      · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h1, h2⟩

open Classical in
/-- **The accept count of the drain table is the number of accepting computations**, once every
run has halted. -/
theorem acceptCount_drain {x : List Bool} {τ : ℕ} (h : HaltsWithin m x τ) :
    (drain m).acceptCount x τ = compCount m [true] x τ := by
  unfold MultiTapePTM.acceptCount compCount Complexity.acceptCount
  congr 1
  refine Finset.filter_congr fun r _ => ?_
  simp only [decide_eq_true_eq]
  rw [MultiTapePTM.runClosedCoins_eq_output_stepCoins,
    show (Cfg.init (drain m).initial x : Cfg k Bool (Option S) x) = liftCfg (Cfg.init m.initial x)
      from rfl, output_drain]
  have hh := h (List.ofFn r) (by simp)
  tauto

end Drain

/-! ### The flip table -/

section Flip

variable (m : MultiTapePTM k Bool S)

/-- An action with its emitted bit negated. -/
def flipAction (a : Turing.Action k Bool S) : Turing.Action k Bool S :=
  { a with output := a.output.map not }

/-- **The flip table**: the moves of `m`, with every emitted bit negated. -/
def flip : MultiTapePTM k Bool S where
  initial := m.initial
  tr s symbol work answer bit :=
    .step (flipAction (MultiTapeMachine.Action.emptyOracleEquiv (m.tr s symbol work answer bit)))
      Empty.elim Empty.elim

/-- A configuration with its output negated. -/
def flipCfg (c : Cfg k Bool S input) : Cfg k Bool S input := { c with output := c.output.map not }

theorem step_flip (b : Bool) (c : Cfg k Bool S input) :
    ((flip m).withCoin b).toTM.step (flipCfg c) = flipCfg ((m.withCoin b).toTM.step c) := by
  rcases hs : c.state with _ | q
  · have hs' : (flipCfg c).state = none := hs
    rw [MultiTapeTM.step_of_halt hs', MultiTapeTM.step_of_halt hs]
  · have hs' : (flipCfg c).state = some q := hs
    rw [MultiTapeTM.step_of_state hs', MultiTapeTM.step_of_state hs]
    simp only [MultiTapeMachine.toTM, MultiTapeTM.tr_ofTr]
    change (flipAction (MultiTapeMachine.Action.emptyOracleEquiv
      (m.tr q c.inputSymbol c.workTapeSymbols Empty.elim b))).apply (flipCfg c) =
      flipCfg ((MultiTapeMachine.Action.emptyOracleEquiv
        (m.tr q c.inputSymbol c.workTapeSymbols Empty.elim b)).apply c)
    generalize MultiTapeMachine.Action.emptyOracleEquiv
      (m.tr q c.inputSymbol c.workTapeSymbols Empty.elim b) = a
    rcases ho : a.output with _ | o <;> simp [flipAction, flipCfg, Action.apply, ho]

theorem stepCoins_flip (cs : List Bool) (c : Cfg k Bool S input) :
    (flip m).stepCoins cs (flipCfg c) = flipCfg (m.stepCoins cs c) := by
  induction cs generalizing c with
  | nil => rfl
  | cons b cs ih => rw [MultiTapePTM.stepCoins_cons, MultiTapePTM.stepCoins_cons, step_flip, ih]

theorem canonFrom_flip (cs : List Bool) (c : Cfg k Bool S input) :
    CanonFrom (flip m) (flipCfg c) cs ↔ CanonFrom m c cs := by
  induction cs generalizing c with
  | nil => rfl
  | cons b cs ih =>
    simp only [CanonFrom, step_flip, ih]
    rfl

theorem map_not_eq_true_iff (l : List Bool) : l.map not = [true] ↔ l = [false] := by
  rcases l with _ | ⟨b, _ | ⟨c, l⟩⟩ <;> simp

theorem init_flip (x : List Bool) :
    (Cfg.init (flip m).initial x : Cfg k Bool S x) = flipCfg (Cfg.init m.initial x) := rfl

open Classical in
/-- **The computations of the flip table with output `[true]` are those of `m` with output
`[false]`.** -/
theorem compCount_flip (x : List Bool) (τ : ℕ) :
    compCount (flip m) [true] x τ = compCount m [false] x τ := by
  unfold compCount
  refine Complexity.acceptCount_congr (fun v => ?_) τ
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq, init_flip, stepCoins_flip,
    canonFrom_flip]
  change _ ∧ _ ∧ (m.stepCoins v (Cfg.init m.initial x)).output.map not = [true] ↔ _
  rw [map_not_eq_true_iff]
  rfl

theorem haltsWithin_flip {x : List Bool} {T : ℕ} : HaltsWithin (flip m) x T ↔
    HaltsWithin m x T := by
  unfold HaltsWithin
  simp only [init_flip, stepCoins_flip]
  rfl

end Flip

end Cslib.Complexity.NtimeDspace.Cross.CompCount
