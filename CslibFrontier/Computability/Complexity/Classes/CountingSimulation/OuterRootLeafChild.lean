/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.OuterRootLeaf

/-!
# Correctness of the rooted continuation on each active movement-word path

Every seed, including an unbalanced choice, must halt. Only balanced choices are used to
establish the contraction bit. The selected schedule and original read-only input determine
the represented source block network.
-/

public section

namespace Cslib.Complexity.CountingSimulation

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapePTM _root_.Turing.MultiTapeATM
open Cslib.BitString Circuits.Boolean.CarrySaveQuery Circuits.Frontier.ContractionSchedule
open RootSeedChoice OuterRootLeafRequest

/-- Required behavior of a contraction continuation after the outer verifier chooses one seed.
The same finite continuation handles every schedule, bit and sign. -/
@[expose] def ChecksSeededContractions {K k states : ℕ} {R State : Type}
    (i j : Fin K) (right : MultiTapeATM K Bool R) (M : MultiTapePTM k Bool State)
    (st : State ≃ Fin states) (input : List Bool) (t budget : ℕ) : Prop :=
  let q := numBlocks t
  let m := rootCopies k states t
  let U := rootVertices k states t
  let a := slotBits (rootEdges k states t) 0
  ∀ (σ : ℕ) (bit : Fin (paddedTime t + 1)) (claim : Bool) (seed),
    let cfg := continuationStart i j right input (queryPublic k q m σ a seed bit.val claim)
    let balanced := PacketPacking.Seeded.Balanced U a (explicitVertexEquiv k q m).toEmbedding
      (RootPredecessorGraph.rowOf M input (blockLength t) σ (letterCode st))
      (RootPredecessorGraph.colOf k q m) seed
    right.HaltsWithin budget cfg ∧ (balanced → (right.AcceptsWithin budget cfg ↔
      (blockNetworkOf M st (input, t, σ)).2.contraction.testBit bit.val = claim))

namespace OuterRootLeaf

/-- On each enabled physical request the root game satisfies both the clock and the actual
carry-save bit claim. Its clock also holds on arbitrarily padded physical bit words. -/
theorem child_spec {W K k s : ℕ} {S R State : Type} (src : Fin W) (root : MultiTapeATM W Bool S)
    (i j : Fin K) (right : MultiTapeATM K Bool R) (M : MultiTapePTM k Bool State)
    (st : State ≃ Fin s) (input : List Bool) (t budget C : ℕ)
    (hr : ∀ n (bit : Fin (paddedTime t + 1)) claim,
      RunsRootContraction src root i j right M st input t n (slotBits (rootEdges k s t) 0)
        bit.val claim budget C)
    (hseed : ChecksSeededContractions i j right M st input t budget)
    (path bits : List Bool) (carry claim : Bool) :
    let x := source k s t path carry bits
    let cfg := SharedWordFork.start src root input
      (RootBalanceRequest.encPublic (publicRequest k claim x)) 0
    let time := C * (t / (Nat.log 2 (t + 2)).sqrt + 2) + budget
    active (data k x) = true → root.HaltsWithin time cfg ∧
      (lsbValue bits < paddedTime t + 1 → (root.AcceptsWithin time cfg ↔
        value (RawScheduleSum.contractionLeaf M st input t) ⟨path, 0, carry, lsbValue bits⟩ =
          claim)) := by
  intro x cfg time ha
  obtain ⟨rfl, ⟨n, hp⟩, hi⟩ := (active_iff k s t path bits carry).1 ha
  let bit : Fin (paddedTime t + 1) := ⟨ofBits (bits.take x.width.length), hi⟩
  have h := hr n bit claim (hseed n bit claim) 0 (Nat.zero_le _)
  dsimp only [cfg]
  rw [request_eq k s t n path bits false claim hp]
  refine ⟨h.1, fun hb => h.2.trans ?_⟩
  rw [value_schedule M st input t n path bits hp hb]
  have he : bit.val = lsbValue bits := ofBits_take_of_lt bits _ hb
  rw [he]

end OuterRootLeaf

end Cslib.Complexity.CountingSimulation
