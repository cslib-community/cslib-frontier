/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Complexity.Classes.LogSpace.Counting
import CslibFrontier.Computability.Complexity.Classes.LogSpace.Function
import CslibFrontier.Computability.Complexity.Classes.LogSpace.NondeterministicOracle
import CslibFrontier.Computability.Complexity.Classes.NP.Logarithmic
import CslibFrontierTests.CountingAmbiguity

open Cslib.Complexity Turing Turing.MultiTapeTM

-- For a zero-or-one branch count, the same witness is also a valid parity count.
example {α : Type} {enc : α ↪ List Bool} {A : Set α} (hA : A ∈ UL enc) :
    A ∈ ParityL enc := by
  obtain ⟨f, hf, hle, hpos⟩ := hA
  refine ⟨f, hf, fun a => (hpos a).trans ?_⟩
  have h : f a = 0 ∨ f a = 1 := by have := hle a; omega
  obtain h | h := h <;> rw [h] <;> decide

-- Two occurrences of the same accepting action violate weak unambiguity.
example : ¬ (CslibFrontierTests.CountingAmbiguity.machine 2).WeaklyUnambiguousFrom
    (Cfg.init () [true]) := by
  intro h
  have collision := h (first := [0]) (second := [1]) rfl rfl rfl rfl
  cases collision

-- The global one-branch bound implies the terminal configuration condition.
example {α : Type} {enc : α ↪ List Bool} {A : Set α} (hA : A ∈ UL enc) :
    A ∈ LogFewNL enc :=
  UL_subset_LogFewNL hA

-- A constant gap of one has nonzero residue modulo two, so this witness accepts every input.
example {α : Type} {enc : α ↪ List Bool}
    (hf : (fun _ : α => (1 : ℤ)) ∈ GapL enc)
    (hg : ComputableInLogSpace (fun _ : α => [false, false]) enc encBits) :
    (Set.univ : Set α) ∈ ModL enc := by
  refine ⟨_, hf, _, hg, fun a => ⟨⟨2, 1, Nat.prime_two, by decide, rfl⟩, ?_⟩⟩
  exact iff_of_true (Set.mem_univ a) (by decide)

-- The verifier can feed a tagged end marker to the NL bit-graph machine.
example (x : List Bool) (i : ℕ) :
    encFNLQuery encBits ⟨x, i, none⟩ = encPair encBits (encPair encNat (encOption encBool))
      (x, i, none) := rfl

-- The always-true first-order matrix satisfies the local LOGNP pattern.
example {L : FirstOrder.Language.{0, 0}} :
    LOGNP0 (Set.univ : Set (Cslib.Logic.FO.Ordered.Structure L)) := by
  refine ⟨0, 0, ⊤, FirstOrder.Language.BoundedFormula.IsQF.top, fun M => ?_⟩
  refine iff_of_true trivial ⟨Fin.castLE (Nat.log2_le_self M.size), ?_, ?_⟩
  · exact fun _ _ h => h
  · exact fun _ => ⟨Fin.elim0, fun _ => by simp⟩

-- Two nondeterministic choices on the same input write different oracle query bits.
example (A : Set (List Bool)) (x : List Bool) :
    let chooseQueryBit : MultiTapeMachine 0 Bool Unit Unit List :=
      { initial := ()
        tr := fun _ _ _ _ => [false, true].map fun bit =>
          .step ⟨0, Fin.elim0, none, none⟩ (fun _ => some bit) (fun _ => 0) }
    (∃ cfg : MultiTapeMachine.Config 0 Bool Unit Unit x,
      OracleReaches chooseQueryBit A [0] cfg ∧ (cfg.channels ()).queryBuffer = [false]) ∧
    (∃ cfg : MultiTapeMachine.Config 0 Bool Unit Unit x,
      OracleReaches chooseQueryBit A [1] cfg ∧ (cfg.channels ()).queryBuffer = [true]) :=
  ⟨⟨_, ⟨[0], rfl⟩, rfl⟩, ⟨_, ⟨[1], rfl⟩, rfl⟩⟩
