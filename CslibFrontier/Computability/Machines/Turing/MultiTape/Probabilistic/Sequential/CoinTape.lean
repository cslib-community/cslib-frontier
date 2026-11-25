/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Sequential
import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Nondeterministic

/-!
# Fixed-coin steps of sequential probabilistic machines

## Main results

* `Turing.MultiTapePTM.step_withCoin_seq_left`: a running first phase follows its own step.
* `Turing.MultiTapePTM.step_withCoin_seq_right`: the second phase follows its own step.
* `Turing.MultiTapePTM.replay_seq_cases`: identify the active phase of a sequential machine,
  using the closed-replay concatenation law `Turing.MultiTapePTM.replay_append`.
* `Turing.MultiTapePTM.output_length_le_replay`, `Turing.MultiTapePTM.replay_halted`: output length
  is monotone along a replay, and halted configurations remain fixed.
* `Turing.MultiTapePTM.completed_replay_mem_support`,
  `Turing.MultiTapePTM.replay_output_length_le`: connect completed replays to run support and
  transfer support-wise output bounds to arbitrary replay prefixes.
-/

public section

namespace Turing.MultiTapePTM

open Cslib MultiTapeMachine

variable {k : ℕ} {Symbol : Type} {input : List Symbol}

/-- With a fixed coin, a running first phase of a sequential machine steps as the first machine. -/
theorem step_withCoin_seq_left {S₀ S₁ : Type} (first : MultiTapePTM k Symbol S₀)
    (second : MultiTapePTM k Symbol S₁) (bit : Bool) (c : Config k Symbol S₀ Empty input)
    (hc : c.tapes.state ≠ none) :
    ((first.seq second).withCoin bit).step (Sequential.left second c) =
      Sequential.left second ((first.withCoin bit).step c) := by
  rcases c with ⟨⟨_ | q, _, _, _, _⟩, _⟩
  · exact (hc rfl).elim
  · rw [Config.eq_iff_tapes_eq]
    dsimp only [MultiTapeMachine.step, Sequential.left, Cfg.mapState, Option.elim, Cfg.inputSymbol,
      withCoin, seq, MultiTapeMachine.seq, Functor.map]
    unfold Cfg.workTapeSymbols Config.answerSymbols
    cases first.tr q _ _ _ bit with
    | step a s m => simp [Sequential.leftAction, Config.step, Turing.Action.apply, Option.elim]
    | query op _ => exact op.elim

/-- With a fixed coin, the second phase of a sequential machine steps as the second machine. -/
theorem step_withCoin_seq_right {S₀ S₁ : Type} (first : MultiTapePTM k Symbol S₀)
    (second : MultiTapePTM k Symbol S₁) (bit : Bool) (c : Config k Symbol S₁ Empty input) :
    ((first.seq second).withCoin bit).step (Sequential.right (State₀ := S₀) c) =
      Sequential.right ((second.withCoin bit).step c) := by
  rcases c with ⟨⟨_ | q, _, _, _, _⟩, _⟩
  · rfl
  · rw [Config.eq_iff_tapes_eq]
    dsimp only [MultiTapeMachine.step, Sequential.right, Cfg.mapState, Option.map, Cfg.inputSymbol,
      withCoin, seq, MultiTapeMachine.seq, Functor.map]
    unfold Cfg.workTapeSymbols Config.answerSymbols
    cases second.tr q _ _ _ bit with
    | step a s m => simp [Sequential.rightAction, Config.step, Turing.Action.apply, Option.map]
    | query op _ => exact op.elim


variable {k : ℕ} {Symbol State : Type} {input : List Symbol}

/-- Replaying a sequence of coins on a sequentially composed machine either stays in the
first phase or transitions to the second. -/
theorem replay_seq_cases {State₀ State₁ : Type}
    (first : MultiTapePTM k Symbol State₀) (second : MultiTapePTM k Symbol State₁)
    (initial : Config k Symbol State₀ Empty input) (coins : List Bool) :
    (∃ before, (first.seq second).runClosedConfigFromCoins coins (Sequential.left second initial) =
      Sequential.left second (first.runClosedConfigFromCoins before initial)) ∨
    ∃ before after,
      (first.runClosedConfigFromCoins before initial).tapes.state = none ∧
      (first.seq second).runClosedConfigFromCoins coins (Sequential.left second initial) =
        Sequential.right (second.runClosedConfigFromCoins after
          (Sequential.start second (first.runClosedConfigFromCoins before initial))) := by
  induction coins using List.reverseRecOn with
  | nil => exact Or.inl ⟨[], rfl⟩
  | append_singleton coins bit ih =>
    rw [replay_append]
    rcases ih with ⟨before, hp⟩ | ⟨before, after, hh, hs⟩
    · rw [hp]
      by_cases hh : (first.runClosedConfigFromCoins before initial).tapes.state = none
      · right
        refine ⟨before, [bit], hh, ?_⟩
        rw [Sequential.left_halted second _ hh]
        simpa only [runClosedConfigFromCoins, List.foldl_cons, List.foldl_nil] using
          step_withCoin_seq_right first second bit
            (Sequential.start second (first.runClosedConfigFromCoins before initial))
      · left
        refine ⟨before ++ [bit], ?_⟩
        rw [replay_append]
        exact step_withCoin_seq_left first second bit _ hh
    · right
      refine ⟨before, after ++ [bit], hh, ?_⟩
      rw [hs, replay_append]
      exact step_withCoin_seq_right first second bit _

/-- The output tape length is monotonically non-decreasing during a run. -/
theorem output_length_le_replay (machine : MultiTapePTM k Symbol State)
    (coins : List Bool) (cfg : Config k Symbol State Empty input) :
    cfg.tapes.output.length ≤
      (machine.runClosedConfigFromCoins coins cfg).tapes.output.length := by
  obtain ⟨p, hhead, _, hlast⟩ := (machine.exists_runPath_toNTM_iff (c := cfg.tapes)).mpr
    ⟨coins, rfl, rfl⟩
  have h : p.head.output.length ≤ p.last.output.length :=
    p.length_output_mono (Fin.zero_le (Fin.last p.length))
  simpa only [hhead, hlast, tapes_runClosedConfigFromCoins] using h

/-- A halted configuration does not change when further coins are replayed. -/
theorem replay_halted (machine : MultiTapePTM k Symbol State)
    (coins : List Bool) (cfg : Config k Symbol State Empty input)
    (h : cfg.tapes.state = none) : machine.runClosedConfigFromCoins coins cfg = cfg := by
  induction coins with
  | nil => rfl
  | cons bit coins ih =>
    change machine.runClosedConfigFromCoins coins ((machine.withCoin bit).step cfg) = cfg
    rw [show (machine.withCoin bit).step cfg = cfg by simp only [MultiTapeMachine.step, h], ih]

/-- A replay that halts belongs to the support of the closed run evaluation. -/
theorem completed_replay_mem_support (machine : MultiTapePTM k Symbol State)
    (initial : Config k Symbol State Empty input) (time : ℕ)
    (hhalt : ∀ final ∈ (ProbComp.eval
      (machine.runClosedConfigFrom time initial)).support,
      final.tapes.state = none)
    (coins : List Bool)
    (hcoins : (machine.runClosedConfigFromCoins coins
      initial).tapes.state = none) :
    machine.runClosedConfigFromCoins coins initial ∈
      (ProbComp.eval (machine.runClosedConfigFrom time initial)).support := by
  by_cases hle : time ≤ coins.length
  · simpa only [← eval_runClosedConfigFrom_eq_of_halted machine _ hle hhalt] using
      machine.runClosedConfigFromCoins_mem_support coins initial
  · have h := machine.runClosedConfigFromCoins_mem_support
      (coins ++ List.replicate (time - coins.length) false) initial
    rw [show (coins ++ List.replicate (time - coins.length) false).length = time by grind,
      replay_append, replay_halted machine _ _ hcoins] at h
    exact h

/-- Bounds the output length of any replay given a bound on the support of the closed run. -/
theorem replay_output_length_le (machine : MultiTapePTM k Symbol State)
    (time bound : ℕ)
    (hhalt : ∀ final ∈ (ProbComp.eval
      (machine.runClosedConfigFrom time (machine.initialConfig input))).support,
      final.tapes.state = none)
    (hbound : ∀ word ∈ (ProbComp.eval (machine.runClosed time input)).support,
      word.length ≤ bound) (coins : List Bool) :
    (machine.runClosedConfigFromCoins coins (machine.initialConfig input)).tapes.output.length ≤
      bound := by
  let extra := List.replicate (time - coins.length) false
  have hfull := machine.runClosedConfigFromCoins_mem_support (coins ++ extra)
    (machine.initialConfig input)
  rw [eval_runClosedConfigFrom_eq_of_halted machine _ (by grind) hhalt] at hfull
  refine (replay_append machine coins extra _ ▸ output_length_le_replay machine extra _).trans
    (hbound _ ?_)
  rw [runClosed_eq_map, ProbComp.eval_map]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨_, hfull, rfl⟩

end Turing.MultiTapePTM
