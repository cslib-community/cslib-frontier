/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveLeaf
import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SharedFork
import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.ExtendTapes
import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveLeafLayout

/-!
# A common finite family on physical carry-save leaf storage

Two independently compiled leaf families may have different scratch-tape counts and state
types. `exists_family` places both in one larger tape layout and one finite state type. The
controller and metadata tapes retain their indices, and the chosen child sees exactly its
original leaf configuration. Halting and acceptance are preserved at the same clock.
-/

public section

namespace Turing.MultiTapeATM.CarrySaveLeafFamily

open MultiTapeTM

private theorem view_initial {k K : ℕ} (hk : k ≤ K) {S : Type} (s : S)
    (input context count width height bits path unary : List Bool) (frontier : ℤ) (status : Bool) :
    viewCfg (Fin.castLEEmb (Nat.add_le_add_right hk 12))
      ((CarrySaveLeaf.initial K input context count width height bits path unary frontier
        status).withState (some s)) =
      (CarrySaveLeaf.initial k input context count width height bits path unary frontier
        status).withState (some s) := by
  rw [CarrySaveLeafLayout.initial_eq_tapesCfg, CarrySaveLeafLayout.initial_eq_tapesCfg]
  rfl

/-- Two physical leaf families share a finite controller and the larger scratch block.
The first selector chooses a child without adding transitions; the second remains available
to choose an operand within it. All persistent words and head positions are retained, for
either carry selector and either Boolean claim. -/
theorem exists_family (u : Bool → ℕ) (S : Bool → Type) [∀ b, Finite (S b)]
    (leaf : (b : Bool) → Bool → Bool → Bool → MultiTapeATM (u b + 12) Bool (S b)) :
    ∃ (k : ℕ) (Q : Type) (_ : Finite Q)
      (family : Bool → Bool → Bool → Bool → MultiTapeATM (k + 12) Bool Q),
      ∀ (b side carry claim : Bool) (input context count width height bits path unary : List Bool)
        (frontier : ℤ) (status : Bool) (t : ℕ),
        let start := (CarrySaveLeaf.initial k input context count width height bits path unary
          frontier status).withState (some (family b side carry claim).toPTM.initial)
        let child := (CarrySaveLeaf.initial (u b) input context count width height bits path unary
          frontier status).withState (some (leaf b side carry claim).toPTM.initial)
        ((family b side carry claim).HaltsWithin t start ↔
          (leaf b side carry claim).HaltsWithin t child) ∧
          ((family b side carry claim).AcceptsWithin t start ↔
            (leaf b side carry claim).AcceptsWithin t child) := by
  classical
  let k := max (u false) (u true)
  have hle (b : Bool) : u b ≤ k := by
    cases b
    · exact Nat.le_max_left ..
    · exact Nat.le_max_right ..
  let e (b : Bool) : Fin (u b + 12) ↪ Fin (k + 12) :=
    Fin.castLEEmb (Nat.add_le_add_right (hle b) 12)
  let lifted (side carry claim b : Bool) := (leaf b side carry claim).extendTapes (e b)
  refine ⟨k, _, inferInstance, fun b side carry claim =>
    SharedFork.selected (lifted side carry claim) b, ?_⟩
  intro b side carry claim input context count width height bits path unary f status t start child
  have hs := SharedFork.selected_spec (lifted side carry claim) b
    (CarrySaveLeaf.initial k input context count width height bits path unary f status) t
  have hv := view_initial (hle b) (leaf b side carry claim).toPTM.initial
    input context count width height bits path unary f status
  exact ⟨hs.1.trans (((leaf b side carry claim).haltsWithin_extendTapes_iff (e b) t _).trans
      (hv ▸ Iff.rfl)),
    hs.2.trans (((leaf b side carry claim).acceptsWithin_extendTapes_iff (e b) t _).trans
      (hv ▸ Iff.rfl))⟩

end Turing.MultiTapeATM.CarrySaveLeafFamily
