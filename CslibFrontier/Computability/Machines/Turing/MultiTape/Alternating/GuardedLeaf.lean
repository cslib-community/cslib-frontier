/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveLeafATM
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.GuardedWord
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.WorkTapeFamily

/-!
# A guarded continuation from physical carry-save leaves

Both bit claims share one finite state type and one scratch layout. The machine serializes
the actual six physical fields, computes a guarded child request, then either returns the
constant answer or invokes the child once. The exact clock keeps serialization, preparation,
and the one child run separate so each caller can supply its own size bound.
-/

public section

namespace Turing.MultiTapeATM.GuardedLeaf

open MultiTapeTM Cslib.CountingLeaf

/-- Compile two guarded request preparers into one physical carry-save leaf family. The typed
input is only an overlay of the serializer's six raw fields. Disabled requests require no child
halting premise, and every enabled branch charges the child's running time exactly once. -/
theorem exists_runner {α S : Type} {K : ℕ} [Finite S] (src : Fin K)
    (child : MultiTapeATM K Bool S) {enc : α ↪ List Bool} (raw : α → RawInput)
    (henc : ∀ x, encRawInput (raw x) = enc x)
    (active answer : Bool → α → Bool) (word : Bool → α → List Bool) (T : Bool → α → ℕ)
    (hf : ∀ claim, ComputableInO
      (fun x => [active claim x, false, answer claim x] ++ word claim x)
      enc encBits (T claim) (T claim)) :
    ∃ (a : ℕ) (Q : Type) (_ : Finite Q)
      (leaf : Bool → Bool → MultiTapeATM (a + 12) Bool Q) (A : Bool → ℕ),
      ∀ (host : List Bool) (x : α) (height unary : List Bool) (frontier : ℤ)
        (status claim : Bool) (t : ℕ),
        let q := raw x
        let target := SharedWordFork.start src child host (word claim x) 0
        let atm := leaf q.carry claim
        let start := (CarrySaveLeaf.initial a host q.context q.count q.width
          height q.bit q.path unary frontier status).withState (some atm.toPTM.initial)
        let time := q.path.length + 3 + (2 * (enc x).length + 5) +
          (A claim * (T claim x + 1) + (2 * (word claim x).length + 16)) + t
        (active claim x = true → child.HaltsWithin t target) →
          atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
            if active claim x then child.AcceptsWithin t target else answer claim x = true) := by
  classical
  have guarded (claim : Bool) := GuardedWord.exists_guarded_runner src child
    (active claim) (answer claim) (word claim) (T claim) (hf claim)
  choose u R hR runner A hr using guarded
  let : ∀ claim, Finite (R claim) := hR
  obtain ⟨a, Q, hQ, family, hfamily⟩ := WorkTapeFamily.exists_family u R runner
  let := hQ
  refine ⟨a, _, inferInstance, fun carry claim => CarrySaveLeafATM.machine (family claim) carry,
    A, ?_⟩
  intro host x height unary frontier status claim t q target atm start time hchild
  let n := A claim * (T claim x + 1) + (2 * (word claim x).length + 16) + t
  obtain ⟨hh, ha⟩ := hr claim host x t hchild
  have hs := hfamily claim host (enc x) n
  have hraw : encRawInput (CarrySaveLeaf.query q.context q.count q.width q.path q.bit q.carry) =
      enc x := henc x
  have hp := CarrySaveLeafATM.spec (family claim) host q.context q.count q.width
    height q.bit q.path unary frontier status q.carry n (by
      simpa only [hraw] using hs.1.mpr hh)
  simp only [hraw] at hp
  simpa only [time, n, Nat.add_assoc] using
    And.intro hp.1 (hp.2.trans (hs.2.trans ha))

end Turing.MultiTapeATM.GuardedLeaf
