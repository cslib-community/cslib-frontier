/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.ScheduleFields
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.Prepend
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.TwoWordInput

/-!
# Native initialization of the outer schedule sum

A single finite deterministic controller fills the seven evaluator tapes from the short parameter
word while preserving the protected context and the host input. The two long fields have length
twice the raw half-length up to one extra bit. Each field machine is charged once.
-/

public section

namespace Turing.MultiTapeATM.ScheduleCountPrepare

open MultiTapeTM Cslib.Circuits.Boolean.CarryLookahead.Query
open CarryLookaheadCountingPrepare CarryLookaheadCountingInitialLayout ScheduleFields

private def total (f : Field → ℕ) : ℕ :=
  f (.stored .count) + f (.stored .width) + f (.stored .metadata) + f (.stored .header) +
    f (.stored .status) + f .height + f .unary

private theorem le_total (f : Field → ℕ) (i : Field) : f i ≤ total f := by
  cases i with
  | stored i => cases i <;> dsimp [total] <;> omega
  | height => dsimp [total]; omega
  | unary => dsimp [total]; omega

/-- Prepare the actual count of all binary schedule words, with an additive linear charge
in the schedule length and polynomial overhead in the binary parameters. -/
theorem exists_prepare (k r q : ℕ) :
    ∃ (scratch : ℕ) (Q : Type) (_ : Finite Q)
      (tm : MultiTapeTM (CarryLookaheadCountingPrepare.size scratch k r q) Bool Q) (c d : ℕ),
      ∀ (input context : List Bool) (a : CountingInput.Input),
        tm.runFrom ((initial scratch k r q input context a).withState (some tm.q₀))
          (c * (budget d a + 1)) =
          (config scratch k r q input context a (canonical (expanded a))).withState none := by
  classical
  choose deg hdeg using computable_word
  have cert (i : Field) := WordFunctionLayout.exists_of_inO (hdeg i)
  choose tape Q hQ machine coeff hmachine using cert
  let (i : Field) : Finite (Q i) := hQ i
  let scratch := total tape
  let E := CarryLookaheadCountingLayout.size k r q
  let write := fun i =>
    ((machine i).extendTapes
      (WordFunctionLayout.outputTapes (le_total tape i) (slot k r q i))).fromLeftBlank
  let tm := (write (.stored .count)).seq ((write (.stored .width)).seq
    ((write (.stored .metadata)).seq ((write (.stored .header)).seq
      ((write (.stored .status)).seq ((write .height).seq (write .unary))))))
  refine ⟨scratch, _, inferInstance, tm, 7 * (total coeff + 2), total deg, ?_⟩
  intro input context a
  let tick (i : Field) := coeff i * (budget (deg i) a + 1) + 2
  have write_spec (i : Field) (v : Fields) (hblank : get v i = []) :
      RunsBetween (write i) (config scratch k r q input context a v)
        (config scratch k r q input context a (ScheduleFields.set v i (word i a)))
        (tick i) ((scratch + E + 2) * (coeff i * (budget (deg i) a + 1) + 1) +
          4 * (scratch + E + 2)) := by
    have hr := hmachine i scratch E (le_total tape i) (slot k r q i) input a
      (ambientWords scratch k r q context a v) [] (by intro j; simp [ambientWords, E])
      (by simpa [ambientWords, words_slot] using hblank)
      (by simp [ambientWords, E]) (by simp [ambientWords, E])
    simp only [encBits_apply] at hr
    rw [show (Fin.natAdd scratch (slot k r q i)).castAdd 2 =
      evaluatorTapes scratch k r q (slot k r q i) from rfl,
      ambientWords_update_of_eq _ _ _ _ _ _ _ _ _ _ (words_set k r q context v i _)] at hr
    exact hr
  let v₀ : Fields := {}
  let v₁ := ScheduleFields.set v₀ (.stored .count) (word (.stored .count) a)
  let v₂ := ScheduleFields.set v₁ (.stored .width) (word (.stored .width) a)
  let v₃ := ScheduleFields.set v₂ (.stored .metadata) (word (.stored .metadata) a)
  let v₄ := ScheduleFields.set v₃ (.stored .header) (word (.stored .header) a)
  let v₅ := ScheduleFields.set v₄ (.stored .status) (word (.stored .status) a)
  let v₆ := ScheduleFields.set v₅ .height (word .height a)
  have hr := (write_spec (.stored .count) v₀ rfl).seq
    ((write_spec (.stored .width) v₁ rfl).seq ((write_spec (.stored .metadata) v₂ rfl).seq
      ((write_spec (.stored .header) v₃ rfl).seq ((write_spec (.stored .status) v₄ rfl).seq
        ((write_spec .height v₅ rfl).seq (write_spec .unary v₆ rfl))))))
  have hfinal : ScheduleFields.set v₆ .unary (word .unary a) = canonical (expanded a) := by
    simp [v₆, v₅, v₄, v₃, v₂, v₁, v₀, ScheduleFields.set, Fields.set, word,
      CountingInput.word, canonical, expanded, Nat.clog_pow _ _ (by decide : 1 < 2)]
  have ht (i : Field) : tick i ≤ (total coeff + 2) * (budget (total deg) a + 1) := by
    have ha : budget (deg i) a ≤ budget (total deg) a :=
      Nat.add_le_add_right (Nat.pow_le_pow_right (by omega) (le_total deg i)) _
    have hm := Nat.mul_le_mul (le_total coeff i) (Nat.add_le_add_right ha 1)
    dsimp only [tick]
    nlinarith
  have := ht (.stored .count)
  have := ht (.stored .width)
  have := ht (.stored .metadata)
  have := ht (.stored .header)
  have := ht (.stored .status)
  have := ht .height
  have := ht .unary
  rw [hfinal] at hr
  exact (hr.mono (t' := 7 * (total coeff + 2) * (budget (total deg) a + 1))
    (by rw [Nat.mul_assoc]; omega) (Nat.le_refl _)).1

/-- Launch any native alternating evaluator after installing the seven fields. The evaluator
sees the same input and context and pays its own branch clock exactly once. -/
theorem exists_prepend {k r q : ℕ} {S : Type} [Finite S]
    (evaluator : MultiTapeATM (CarryLookaheadCountingLayout.size k r q) Bool S) :
    ∃ (scratch : ℕ) (Q : Type) (_ : Finite Q)
      (atm : MultiTapeATM (CarryLookaheadCountingPrepare.size scratch k r q) Bool Q) (c d : ℕ),
      ∀ (input context : List Bool) (a : CountingInput.Input) (time : ℕ),
        let b := expanded a
        let ec := (CarryLookaheadCounting.initial k r q input context b.count b.query.width
          b.query.bit b.query.claim).withState (some evaluator.toPTM.initial)
        let start := (initial scratch k r q input context a).withState (some atm.toPTM.initial)
        evaluator.HaltsWithin time ec →
          atm.HaltsWithin (c * (budget d a + 1) + time) start ∧
          (atm.AcceptsWithin (c * (budget d a + 1) + time) start ↔
            evaluator.AcceptsWithin time ec) := by
  obtain ⟨scratch, P, hP, prepare, c, d, hp⟩ := exists_prepare k r q
  let := hP
  let e := evaluatorTapes scratch k r q
  let leaf := evaluator.extendTapes e
  refine ⟨scratch, _, inferInstance, prependTM prepare leaf, c, d, ?_⟩
  intro input context a time b ec start hh
  let finish := config scratch k r q input context a (canonical b)
  have hv : viewCfg e (finish.withState (some leaf.toPTM.initial)) = ec := by
    change (viewCfg e finish).withState (some evaluator.toPTM.initial) = _
    rw [view_prepared_of_retained]
  have hl : leaf.HaltsWithin time (finish.withState (some leaf.toPTM.initial)) := by
    rw [haltsWithin_extendTapes_iff, hv]
    exact hh
  have hs := prependTM_spec prepare leaf (initial scratch k r q input context a)
    finish _ time (hp input context a) hl
  refine ⟨hs.1, hs.2.trans ?_⟩
  rw [acceptsWithin_extendTapes_iff]
  exact Iff.of_eq (congrArg (evaluator.AcceptsWithin time) hv)

end Turing.MultiTapeATM.ScheduleCountPrepare
