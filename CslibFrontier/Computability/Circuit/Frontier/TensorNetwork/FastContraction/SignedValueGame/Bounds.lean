/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import
  CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.SignedValueGame
public import CslibFrontier.Computability.Circuit.Boolean.CarryLookahead.Query.Bounds

/-!
# Bounded addresses inside a signed product

Finishing-adder indices and rounds remain within their original precision. In the carry-save
tree, the path length plus the remaining height never exceeds the initial height. Each signed
operand port therefore carries only a logarithmic path and a valid precision bit.
-/

public section

namespace Cslib.Circuits.Frontier.FastContraction.SignedValueGame

open Boolean LocalValueGame

/-- Bounds on every live signed-product macro address, including its operand ports. -/
@[expose] def WellFormed (q p : ℕ) : Node → Prop
  | .finish a => CarryLookahead.Query.WellFormed p (rounds p) a
  | .tree a => a.path.length + a.remaining ≤ height q p ∧ a.bit < p
  | .port path _ bit _ => path.length ≤ height q p ∧ bit < p

private theorem finishSource_wellFormed {q p : ℕ} {a : CarryLookahead.Query.Address}
    (ha : WellFormed q p (.finish a)) (port : Fin 7) (b : Node)
    (h : finishSource p a port = some b) : WellFormed q p b := by
  have haddr : CarryLookahead.Query.WellFormed p (rounds p) a := ha
  cases ho : (finishDecoder p).op a <;> simp only [finishSource, ho] at h
  · simp at h
  · split at h
    · cases h
      exact haddr.child (fun _ => false) false
    · simp at h
  all_goals
    split at h
    · cases h
      exact haddr.child (fun _ => false) false
    · split at h
      · cases h
        exact haddr.child (fun _ => false) true
      · simp at h

/-- Every declared signed source preserves the precision, round and total-path bounds. -/
theorem WellFormed.source {q p : ℕ} {a : Node} (ha : WellFormed q p a)
    (port : Fin 7) (b : Node) (h : source q p a port = some b) : WellFormed q p b := by
  cases a with
  | finish a =>
    cases a
    case input j =>
      simp only [SignedValueGame.source] at h
      split at h
      · rename_i hj
        cases h
        simp only [WellFormed, List.length_nil, Nat.zero_add, le_refl, true_and]
        split <;> omega
      · simp at h
    all_goals exact finishSource_wellFormed ha port b h
  | tree a =>
    simp only [SignedValueGame.source] at h
    split at h
    · split at h
      · rename_i hz
        cases h
        exact ⟨by simpa only [hz, Nat.add_zero] using ha.1, ha.2⟩
      · obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
        exact ⟨(CarrySaveQuery.descend_height hc).trans_le ha.1,
          (CarrySaveQuery.descend_bit hc).1.trans_lt ha.2⟩
    · simp at h
  | port path carry bit index => simp [SignedValueGame.source] at h

end Cslib.Circuits.Frontier.FastContraction.SignedValueGame
