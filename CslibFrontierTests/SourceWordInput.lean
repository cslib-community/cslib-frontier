import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SourceWordInput

open Turing Turing.MultiTapeTM Turing.MultiTapeATM

private def readFirst : MultiTapeTM 1 Bool Bool :=
  ofTr false fun phase symbol _ => if phase then
    ⟨0, fun _ => (none, 0), some (symbol.getD false), none⟩
    else ⟨1, fun _ => (none, 0), none, some true⟩

private noncomputable def child : MultiTapeATM 1 Bool Bool :=
  ofTMs (fun _ => readFirst) (fun _ => false)

private theorem read_first (x ch : List Bool) :
    let start := SharedWordFork.start 0 child x ch 0
    child.HaltsWithin 2 start ∧ (child.AcceptsWithin 2 start ↔ x.head? = some true) := by
  intro start
  have h (b : Bool) (c : Cfg 1 Bool Bool x) : child.next b c = readFirst.step c :=
    next_ofTMs _ _ b c
  have hs : start.state = some false := by simp [start, child, SharedWordFork.start,
    WordGameLeaf.config, ofTMs, readFirst]
  have h₁ : (readFirst.step start).state = some true := by
    simp [step_of_state hs, readFirst, Action.apply]
  have h₂ : (readFirst.step (readFirst.step start)).state = none := by
    rw [step_of_state h₁]
    simp [readFirst, Action.apply]
  refine ⟨by simp [haltsWithin_succ, h, haltsWithin_zero, h₂], ?_⟩
  simp only [AcceptsWithin, hs, h₁, h₂, h, true_and]
  change (if false then _ else _) ↔ _
  simp only [Bool.false_eq_true, ↓reduceIte, exists_const]
  rw [step_of_state h₁, step_of_state hs]
  cases x with
  | nil => simp [readFirst, start, Cfg.inputSymbol, Action.apply, moveInputPos,
      SharedWordFork.start, WordGameLeaf.config, TwoWordLoad.blank, tapesCfg]
  | cons a as =>
    cases a <;> simp [readFirst, start, Cfg.inputSymbol, Action.apply, moveInputPos,
      SharedWordFork.start, WordGameLeaf.config, TwoWordLoad.blank, tapesCfg]

-- The two possible first source symbols and the empty source are all covered by one external ATM.
example : ∃ (u : ℕ) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM u Bool Q) (C : ℕ),
    ∀ (ch x : List Bool),
      let input := encPair encBits encBits (ch, x)
      let time := C * (x.length + ch.length + 1) + 2
      atm.HaltsWithin time (atm.toPTM.toNTM.initCfg input) ∧
        (atm.AcceptsWithin time (atm.toPTM.toNTM.initCfg input) ↔ x.head? = some true) := by
  obtain ⟨u, Q, hQ, atm, C, h⟩ := SourceWordInput.exists_prepend encBits 0 child
  refine ⟨u, Q, hQ, atm, C, fun ch x => ?_⟩
  obtain ⟨ht, ha⟩ := h ch x 2 (read_first x ch).1
  exact ⟨ht, ha.trans (read_first x ch).2⟩
