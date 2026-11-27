/-
Copyright (c) 2026 Sparsa Roychowdhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sparsa Roychowdhury
-/

module

import CslibFrontier.Computability.Automata.MPDA.ScopeHoles
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-! Clients of the scope and round bounds under module encapsulation. On three stacks, the
complete run `↓₀ ↓₁ ↓₂ ↑₀ ↑₁ ↑₂` has two rounds but three open holes after its third push. So
complete runs with `K` rounds need not be `K`-hole-bounded, and the bound `K * n` of
`RoundBounded.holeBounded` cannot be replaced by `K`. -/

set_option linter.privateModule false

namespace CslibFrontierTests.MPDA.ScopeHoles

open Cslib Cslib.Automata Cslib.Automata.MPDA

/-- One control state, one input letter, and every stack operation on three stacks. -/
private def anyOp : MPDA 3 Unit Unit Unit where
  Tr _ _ _ := True
  start := {()}
  accept := {()}

/-- Pushes on stacks `0, 1, 2`, then pops in the same order. -/
private def crossing3 : List (Unit × Op 3 Unit) :=
  [((), .push 0 ()), ((), .push 1 ()), ((), .push 2 ()),
    ((), .pop 0 ()), ((), .pop 1 ()), ((), .pop 2 ())]

private theorem crossing3_run :
    anyOp.configLTS.MTr ⟨(), Stacks.empty⟩ crossing3 ⟨(), Stacks.empty⟩ := by
  refine .stepL (s2 := ⟨(), ![[()], [], []]⟩) ?_ <|
    .stepL (s2 := ⟨(), ![[()], [()], []]⟩) ?_ <|
    .stepL (s2 := ⟨(), ![[()], [()], [()]]⟩) ?_ <|
    .stepL (s2 := ⟨(), ![[], [()], [()]]⟩) ?_ <|
    .stepL (s2 := ⟨(), ![[], [], [()]]⟩) ?_ <|
    .stepL ?_ .refl <;>
  refine configLTS_tr.mpr ⟨trivial, ?_⟩ <;>
  simp only [Op.apply_push, Op.apply_pop] <;>
  funext k <;> fin_cases k <;> simp [Stacks.empty]

/-- Two rounds: `↓₀ ↓₁ ↓₂` and `↑₀ ↑₁ ↑₂`. -/
private theorem crossing3_roundBounded : RoundBounded 2 crossing3 := by
  refine ⟨[[((), .push 0 ()), ((), .push 1 ()), ((), .push 2 ())],
    [((), .pop 0 ()), ((), .pop 1 ()), ((), .pop 2 ())]], le_rfl, rfl, ?_⟩
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl
  · refine ⟨![[((), .push 0 ())], [((), .push 1 ())], [((), .push 2 ())]], rfl, fun i => ?_⟩
    fin_cases i <;> simp [IsContextOf, Op.stack]
  · refine ⟨![[((), .pop 0 ())], [((), .pop 1 ())], [((), .pop 2 ())]], rfl, fun i => ?_⟩
    fin_cases i <;> simp [IsContextOf, Op.stack]

/-- Each push of `crossing3` is a hole push: its matching pop closes a factor that is not
balanced on another stack. -/
private theorem crossing3_holePush {q : ℕ} (hq : q < 3) : HolePush crossing3 q := by
  refine ⟨⟨⟨q, by omega⟩, (), (), by interval_cases q <;> rfl⟩, ?_⟩
  rintro ⟨m, ⟨hqm, i, ⟨a, γ, hp⟩, ⟨b, δ, hpop⟩, -, -⟩, hwn⟩
  have h₀ := hwn.net_eq_zero 0
  have h₁ := hwn.net_eq_zero 1
  have h₂ := hwn.net_eq_zero 2
  have hm : m < 6 := (List.getElem?_eq_some_iff.mp hpop).1
  interval_cases q <;> interval_cases m <;>
    simp_all [crossing3, List.extract_eq_take_drop, net, Op.net, eq_comm (b := i)]

private theorem crossing3_openHolePush {q : ℕ} (hq : q < 3) : OpenHolePush crossing3 2 q := by
  refine ⟨crossing3_holePush hq, by omega, by decide, ⟨q, by omega⟩, ⟨(), (), ?_⟩, ?_⟩
  · interval_cases q <;> rfl
  · intro k
    interval_cases q <;> rcases k with _ | _ | _ | k <;>
      simp [crossing3, List.extract_eq_take_drop, net, Op.net]

/-- After the third push, the three pushes are first pending pushes of three distinct holes. -/
private theorem three_le_openHoles : 3 ≤ openHoles crossing3 2 := by
  have hsub : ({0, 1, 2} : Set ℕ) ⊆
      {q | OpenHolePush crossing3 2 q ∧ ¬∃ p, SameHole crossing3 2 p q} := by
    intro q hq
    have hq3 : q < 3 := by simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq; omega
    refine ⟨crossing3_openHolePush hq3, ?_⟩
    rintro ⟨p, hpq, -, -, ⟨i, ⟨a, γ, hp⟩, ⟨a', γ', hq'⟩⟩, -⟩
    interval_cases q <;> interval_cases p <;> simp_all [crossing3, eq_comm (b := i)]
  have hfin : {q | OpenHolePush crossing3 2 q ∧ ¬∃ p, SameHole crossing3 2 p q}.Finite :=
    (Set.finite_le_nat 2).subset fun q hq => hq.1.2.1
  calc 3 = ({0, 1, 2} : Set ℕ).ncard := by simp [Set.ncard_insert_of_notMem, Set.ncard_singleton]
    _ ≤ _ := Set.ncard_le_ncard hsub hfin

/-- Two rounds, but not `2`-hole-bounded. -/
example : ¬HoleBounded 2 crossing3 := fun h => by
  have := h 2 (by decide)
  have := three_le_openHoles
  omega

/-- The bound for rounds: two rounds on three stacks give at most `2 * 3` open holes. -/
example : HoleBounded (2 * 3) crossing3 := crossing3_roundBounded.holeBounded crossing3_run

end CslibFrontierTests.MPDA.ScopeHoles
