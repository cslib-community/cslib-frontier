/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarryLookaheadCountingContext
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.TwoWordInput

/-!
# Count-bit queries from a single external input

The counter's predicate context and its binary count, width, bit and claim arrive as one
framed input. The loader puts the two fields at their actual destinations and leaves its work
heads and the input head where counting initialization expects them. Its scan contributes
linearly to the same bound as the subsequent alternating computation.
-/

public section

namespace Turing.MultiTapeATM.CarryLookaheadCountingPair

open MultiTapeTM Cslib.Circuits.Boolean.CarryLookahead.Query
open CarryLookaheadCountingPrepare (size)

/-- The context tape in the evaluator block, after its reusable scratch. -/
abbrev contextTape (s k r q : ℕ) : Fin (size s k r q) :=
  (Fin.natAdd s (CarryLookaheadCountingInitialLayout.contextTape k r q)).castAdd 2

/-- The penultimate tape carries the serialized count and bit query. -/
abbrev paramTape (s k r q : ℕ) : Fin (size s k r q) :=
  Fin.natAdd (s + CarryLookaheadCountingLayout.size k r q) 0

theorem contextTape_ne_paramTape (s k r q : ℕ) : contextTape s k r q ≠ paramTape s k r q :=
  Fin.castAdd_ne_natAdd _ _

private theorem ambientWords_initial (s k r q : ℕ) (context : List Bool) (a : CountingInput.Input) :
    CarryLookaheadCountingPrepare.ambientWords s k r q context a {} =
      TwoWordInput.words (contextTape s k r q) (paramTape s k r q) context
        (CountingInput.encInput a) := by
  funext i
  cases i using Fin.addCases with
  | left i =>
    cases i using Fin.addCases with
    | left i =>
      simp only [CarryLookaheadCountingPrepare.ambientWords, Fin.append_left, TwoWordInput.words,
        contextTape, paramTape, Fin.castAdd_inj, Fin.castAdd_ne_natAdd, ↓reduceIte]
    | right i =>
      simp only [CarryLookaheadCountingPrepare.ambientWords, Fin.append_left, Fin.append_right,
        CarryLookaheadCountingInitialLayout.words_empty, TwoWordInput.words, contextTape, paramTape,
        Fin.castAdd_inj, Fin.natAdd_inj, Fin.castAdd_ne_natAdd, ↓reduceIte, Function.update_apply]
  | right i =>
    have hn := (Fin.castAdd_ne_natAdd
      (Fin.natAdd s (CarryLookaheadCountingInitialLayout.contextTape k r q)) i).symm
    simp only [CarryLookaheadCountingPrepare.ambientWords, Fin.append_right, TwoWordInput.words,
      contextTape, paramTape, hn, ↓reduceIte, Fin.natAdd_inj]
    fin_cases i <;> rfl

/-- With the input head at the left blank, the two loaded words are exactly the counting
initializer's starting layout; every other work tape is empty. -/
theorem initial_eq_ready (s k r q : ℕ) (input context : List Bool) (a : CountingInput.Input) :
    CarryLookaheadCountingPrepare.initial s k r q input context a =
      TwoWordInput.ready (contextTape s k r q) (paramTape s k r q) input context
        (CountingInput.encInput a) := by
  unfold CarryLookaheadCountingPrepare.initial CarryLookaheadCountingPrepare.config
    TwoWordInput.ready
  rw [ambientWords_initial]
  apply Cfg.ext <;> try rfl
  funext i z
  simp [tapesCfg, wordsCfg]

/-- External representation with the context framed and the parameter word following it. -/
abbrev encInput := encPair encBits CountingInput.encInput

/-- One alternating machine starts on the serialized context and bit query with blank work tapes.
Its time is linear in the long part of the represented input plus a fixed polynomial in the
short part and binary query parameters. -/
theorem exists_evaluator_on_pair {α : Type*}
    (word : α → List Bool) (raw short : α → ℕ) (P : List Bool × ℕ → Bool)
    {T W : List Bool × ℕ → ℕ} (hp : ComputableInO P (encPair encBits encNat) encBool T W)
    (d : ℕ) (hL : ∀ a, (word a).length ≤ 2 * raw a + 2 * short a + 4)
    (hT : ∀ a j, T (word a, j) ≤ (encPair encBits encNat (word a, j)).length +
      raw a + (short a + j.size) ^ d) :
    ∃ (tapes : ℕ) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM tapes Bool Q) (C E : ℕ),
      ∀ (a : α) (n w : ℕ) (bit : Fin w) (claim : Bool),
        let params : CountingInput.Input := ⟨n, ⟨w, bit.val, claim⟩⟩
        let start := atm.toPTM.toNTM.initCfg (encInput (word a, params))
        let time := C * (raw a + (short a + n.size + w.size + 1) ^ E + 1)
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
          (∑ j ∈ Finset.range n, (P (word a, j)).toNat).testBit bit.val = claim) := by
  obtain ⟨s, k, r, q, S, hS, leaf, A, D, hleaf⟩ :=
    CarryLookaheadCountingFromParametersCost.exists_evaluator_on_context word raw short P hp d hL hT
  let := hS
  obtain ⟨u, Q, hQ, atm, c, hrun⟩ := TwoWordInput.exists_prepend encBits CountingInput.encInput
    (contextTape s k r q) (paramTape s k r q) (contextTape_ne_paramTape s k r q) leaf
  refine ⟨u, Q, hQ, atm, c * 14 + 1 + A, max D 1, ?_⟩
  intro a n w bit claim
  let params : CountingInput.Input := ⟨n, ⟨w, bit.val, claim⟩⟩
  let input := encInput (word a, params)
  let z := short a + n.size + w.size + 1
  let cost := A * (raw a + z ^ D + 1)
  let B := raw a + z ^ max D 1 + 1
  obtain ⟨hh, ha⟩ := hleaf input a n w bit claim
  rw [initial_eq_ready] at hh ha
  obtain ⟨hl, hal⟩ := hrun (word a, params) cost hh
  have hz : 1 ≤ z := by dsimp only [z]; omega
  have hz' : z ≤ z ^ max D 1 := by simpa using Nat.pow_le_pow_right hz (Nat.le_max_right D 1)
  have he : input.length + 1 ≤ 14 * B := by
    have hctx := hL a
    have hparams := CountingInput.length_encInput_le params bit.isLt
    change _ ≤ 2 * n.size + 4 * w.size + 4 at hparams
    simp only [input, encInput, length_encPair, encBits_apply]
    dsimp only [B, z] at *
    omega
  have hcost : cost ≤ A * B := by
    apply Nat.mul_le_mul_left
    exact Nat.add_le_add_right (Nat.add_le_add_left
      (Nat.pow_le_pow_right hz (Nat.le_max_left D 1)) _) _
  have htime : c * (input.length + 1) + 1 + cost ≤ (c * 14 + 1 + A) * B := by
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
    exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left c he)
      (Nat.succ_le_succ (Nat.zero_le _)))
      hcost
  refine ⟨hl.mono htime, ?_⟩
  exact ⟨fun hacc => ha.mp (hal.mp (hacc.of_halted_stepCoins hl)),
    fun hbit => (hal.mpr (ha.mpr hbit)).mono htime⟩

end Turing.MultiTapeATM.CarryLookaheadCountingPair
