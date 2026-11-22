/-
Copyright (c) 2026 Sparsa Roychowdhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sparsa Roychowdhury
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Computability.Automata.MPDA.Witness
public meta import CslibFrontier.Computability.Automata.MPDA.Witness
public meta import Mathlib.Data.FinEnum

/-! Clients of witness generation under module encapsulation. On two stacks, the MPDA `cross4`
pushes on stack `0`, then once or more on stack `1`, pops stack `0`, and pops stack `1` until it
accepts: its accepting runs are `↓₀ ↓₁ᵏ ↑₀ ↑₁ᵏ` with `k ≥ 1`. Each crosses two holes, so there is no
`1`-hole-bounded witness and there is a `2`-hole-bounded one. The witness is checked by evaluation,
and the theorems are applied to it: the returned run is accepting and `2`-hole-bounded. The
well-nested search of Algorithm 5, repaired with fuel, unrolls a nested pair. -/

set_option linter.hashCommand false

public section

namespace CslibFrontierTests.MPDA.Witness

open Cslib Cslib.Automata Cslib.Automata.MPDA

/-- `↓₀`, then `↓₁` once or more, then `↑₀`, then `↑₁` until acceptance, on the states
`0 → 1 → 2 → 3`. -/
@[expose] def cross4 : MPDA 2 (Fin 4) Unit Unit where
  Tr s μ s' := match s.val, μ.2, s'.val with
    | 0, .push i _, 1 => i = 0
    | 1, .push i _, 2 => i = 1
    | 2, .push i _, 2 => i = 1
    | 2, .pop i _, 3 => i = 0
    | 3, .pop i _, 3 => i = 1
    | _, _, _ => False
  start := {0}
  accept := {3}

instance (s : Fin 4) (μ : Unit × Op 2 Unit) (s' : Fin 4) :
    Decidable (cross4.Tr s μ s') := by
  unfold cross4
  dsimp only
  split <;> infer_instance

instance : DecidablePred (· ∈ cross4.start) := fun s =>
  inferInstanceAs (Decidable (s = 0))

instance : DecidablePred (· ∈ cross4.accept) := fun s =>
  inferInstanceAs (Decidable (s = 3))

-- No accepting run of `cross4` has at most one open hole.
#guard (cross4.witness 1).isNone

-- With two holes, the witness is an accepting run `↓₀ ↓₁ᵏ ↑₀ ↑₁ᵏ`.
#guard (cross4.witness 2).map (·.map Prod.snd) =
  some [.push 0 (), .push 1 (), .push 1 (), .push 1 (), .pop 0 (), .pop 1 (), .pop 1 (), .pop 1 ()]

/-- Any returned run is accepting and `2`-hole-bounded. -/
example {w : List (Unit × Op 2 Unit)} (h : cross4.witness 2 = some w) :
    ∃ s₀ ∈ cross4.start, ∃ f ∈ cross4.accept,
      cross4.configLTS.MTr ⟨s₀, Stacks.empty⟩ w ⟨f, Stacks.empty⟩ ∧ HoleBounded 2 w :=
  witness_spec h

/-- The witness exists exactly when the search answers `false`. -/
example : (cross4.witness 2).isSome ↔ cross4.isEmpty 2 = false := isSome_witness_iff

/-- `↓₀ ↓₁ ↑₁ ↑₀` along `0 → 1 → 2 → 3 → 4`. -/
@[expose] def nested : MPDA 2 (Fin 5) Unit Unit where
  Tr s μ s' := match s.val, μ.2, s'.val with
    | 0, .push i _, 1 => i = 0
    | 1, .push i _, 2 => i = 1
    | 2, .pop i _, 3 => i = 1
    | 3, .pop i _, 4 => i = 0
    | _, _, _ => False
  start := {0}
  accept := {4}

instance (s : Fin 5) (μ : Unit × Op 2 Unit) (s' : Fin 5) :
    Decidable (nested.Tr s μ s') := by
  unfold nested
  dsimp only
  split <;> infer_instance

-- The repaired Algorithm 5 unrolls the nested pair `(0, 4)` of `WR`.
#guard (nested.wrWitness 0 4).map (·.map Prod.snd) =
  some [.push 0 (), .push 1 (), .pop 1 (), .pop 0 ()]

-- The pair `(1, 4)` is not in `WR`: from state `1`, the pop of stack `0` has no matching push.
#guard (nested.wrWitness 1 4).isNone

end CslibFrontierTests.MPDA.Witness
