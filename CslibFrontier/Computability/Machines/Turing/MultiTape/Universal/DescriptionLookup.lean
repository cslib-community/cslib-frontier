/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Correct
import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Hardwire

/-!
# Transition lookup in a machine description

`Turing.MultiTapeTM.Universal.find?_desc` characterizes the transition found in the
public description of a finite machine. It requires no machine normal-form premise.
-/

public section

namespace Turing.MultiTapeTM.Universal

open Redirect

section Desc

variable {k : ℕ} {S Y : Type} [Fintype S] [Fintype Y] (eS : S ↪ ℕ) (eY : Y ↪ ℕ)

/-- The transition found in the description of a machine is the renamed transition of the
machine. -/
theorem find?_desc (tm : MultiTapeTM k Y S) (q : S) (inp : Option Y) (work : Fin k → Option Y) :
    (desc eS eY tm).table.find? (·.1 = key (eS q) (inp.map eY) (Option.map eY ∘ work)) =
      some (key (eS q) (inp.map eY) (Option.map eY ∘ work),
        .ofAction ((tm.tr q inp work).map eS eY)) := by
  refine find?_eq_some_of_mem (l := (desc eS eY tm).table)
    (e := (key (eS q) (inp.map eY) (Option.map eY ∘ work),
      .ofAction ((tm.tr q inp work).map eS eY)))
    (List.mem_map.mpr ⟨(q, inp, work), Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩)
    fun e' he' hk => ?_
  obtain ⟨⟨q', i', w'⟩, -, rfl⟩ := List.mem_map.mp he'
  cases key_injective eS eY (a₁ := (q', i', w')) (a₂ := (q, inp, work)) hk
  rfl

end Desc

end Turing.MultiTapeTM.Universal
