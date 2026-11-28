/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Nondeterministic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Counting

/-!
# Accepting counts of counting machines within a space bound

`Turing.MultiTapeCTM.CountsInSpace M enc f s` says that the counting machine `M` realizes the
accepting count `f` within work space `s`. On every encoded instance each computation prefix
visits at most `s a` work-tape cells, some clock bounds every branch, and `f a` is the number of
accepting transition-occurrence traces at that clock. The space bound is an arbitrary function of
the instance; input and output are uncharged, as in `Turing.MultiTapeNTM.RunsInSpace`.

Forgetting transition multiplicity turns such a witness into a nondeterministic decider, within
the same space, for the instances whose count is positive.

## Main definitions

* `Turing.MultiTapeCTM.CountsInSpace`: an accepting-count witness within a space bound.

## Main results

* `Turing.MultiTapeCTM.CountsInSpace.decidesInSpace`: the instances with a positive count are
  decided within the same space by the machine without multiplicities.
-/

public section

namespace Turing.MultiTapeCTM

variable {α : Type} {k : ℕ} {State : Type} {M : MultiTapeCTM k Bool State}
  {enc : α ↪ List Bool} {f : α → ℕ} {s s' : α → ℕ}

/-- The counting machine `M` realizes the accepting count `f` within work space `s`: on each
encoded instance every computation prefix visits at most `s a` work-tape cells, and at a clock
bounding every branch the number of accepting occurrence traces is `f a`. The clock is chosen for
each instance, because the count is stable once every branch has halted. -/
@[expose] def CountsInSpace (M : MultiTapeCTM k Bool State) (enc : α ↪ List Bool) (f : α → ℕ)
    (s : α → ℕ) : Prop :=
  ∀ a, M.toNTM.RunsInSpace (enc a) (s a) ∧
    ∃ t, M.HaltsWithin t (Cfg.init M.initial (enc a)) ∧
      f a = M.acceptCount t (Cfg.init M.initial (enc a))

/-- Space bounds can be increased. -/
theorem CountsInSpace.mono (h : M.CountsInSpace enc f s) (hs : ∀ a, s a ≤ s' a) :
    M.CountsInSpace enc f s' :=
  fun a => ⟨(h a).1.mono (hs a), (h a).2⟩

/-- **Forgetting multiplicity gives a nondeterministic decider.** If `M` realizes the count `f`
within space `s`, then the machine without transition multiplicities decides, within space `s`
and with every branch halting, the instances whose count is positive. -/
theorem CountsInSpace.decidesInSpace {A : Set α} (h : M.CountsInSpace enc f s)
    (hA : ∀ a, a ∈ A ↔ 0 < f a) : M.toNTM.DecidesInSpace enc A s := by
  refine ⟨fun a => ?_, fun a => ?_⟩
  · obtain ⟨hspace, t, hclock, hf⟩ := h a
    refine ⟨hspace, (hA a).trans ?_⟩
    rw [hf]
    constructor
    · intro ha
      obtain ⟨p, hp, hh, hout⟩ := (hclock.branchCount_pos_iff (· == [true])).mp ha
      exact ⟨⟨p, hp⟩, hh, beq_iff_eq.mp hout⟩
    · rintro ⟨p, hh, hout⟩
      exact (hclock.branchCount_pos_iff (· == [true])).mpr
        ⟨p.toRunPath, p.head_eq, hh, beq_iff_eq.mpr hout⟩
  · obtain ⟨_, t, hclock, _⟩ := h a
    exact ⟨t, fun p hp => hclock.paths_halted p.toRunPath p.head_eq hp⟩

end Turing.MultiTapeCTM
