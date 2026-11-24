/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Vector
public import CslibFrontier.Computability.Probabilistic.PPT
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.DPi
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Tactic.PolyTime.Init

/-!
# Strict PPT finite-tuple repetition

`OracleComp.replicateFin n` collects `n` independent runs in a `Fin n`-indexed vector. Because
`encFinFn n output` encodes a tuple as the framed list `List.ofFn`, the list-valued repetition
certificate `IsPPTOn.replicate` directly certifies fixed-length tuple sampling.

## Main results

* `Cslib.Probability.IsPPTOn.replicateFin`: collect `n` independent runs in `Fin n → β`.
-/

public section

namespace Cslib.Probability

open Turing.MultiTapeTM

/-- Collect a fixed number of independent runs in a `Fin n`-indexed tuple under `encFinFn`. -/
@[program_certificate]
theorem IsPPTOn.replicateFin {α β : Type} {input : α ↪ List Bool} {output : β ↪ List Bool}
    {program : α → ProbComp β} (h : IsPPTOn input output program) (n : ℕ) :
    IsPPTOn input (encFinFn n output) (fun a => OracleComp.replicateFin n (program a)) := by
  have hr := h.replicate (ComputableInPolyTime.const (encIn := input) n)
  rw [isPPTOn_iff_encoded] at hr ⊢
  apply hr.congr
  intro a
  rw [← OracleComp.map_ofFn_replicateFin, Functor.map_map]
  rfl

end Cslib.Probability
