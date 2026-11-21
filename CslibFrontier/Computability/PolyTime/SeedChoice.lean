/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.SeededPredecessorFinish
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.OfBits
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Four consecutive coefficient fields for a shared seed

Each field has the degree of the chosen binary extension field. Every number in that
fixed width is a valid field coefficient. Decoding installs all four coefficients in the
shared hash context and returns the untouched following bits for the balance challenge.
-/

public section

namespace Cslib.SeedChoice

open Turing.MultiTapeTM ComputableInPolyTime BitString
open SeededPredecessor (Context encContext)

/-- Number of binary coefficient digits for a single seed component. -/
@[expose] def width (c : Context) : ℕ := Probability.trinomialDeg c.universeSize (6 * c.labelLength)

/-- Every component is chosen least-significant bit first. -/
@[expose] def word {U a : ℕ} (seed : BalancedSchedules.SeededLabels.Seed U (6 * a)) : List Bool :=
  let d := Probability.trinomialDeg U (6 * a)
  lowBits d (seed 0).val ++ (lowBits d (seed 1).val ++
    (lowBits d (seed 2).val ++ lowBits d (seed 3).val))

/-- All four coefficient choices have exactly the field degree in bits. -/
@[simp] theorem length_word {U a : ℕ} (seed : BalancedSchedules.SeededLabels.Seed U (6 * a)) :
    (word seed).length = 4 * Probability.trinomialDeg U (6 * a) := by
  simp [word]
  omega

/-- Framed shared hash context followed by all remaining branch choices. -/
abbrev encData := encPair encContext encBits

/-- Install four little-endian fields without consuming the following challenge word. -/
@[expose] def install (p : Context × List Bool) : Context × List Bool :=
  let c := p.1
  let d := width c
  let w₁ := p.2.drop d
  let w₂ := w₁.drop d
  let w₃ := w₂.drop d
  let seeded := { c with
    c0 := ofBits (p.2.take d)
    c1 := ofBits (w₁.take d)
    c2 := ofBits (w₂.take d)
    c3 := ofBits (w₃.take d) }
  (seeded, w₃.drop d)

/-- Every coefficient of a decoded word lies in the selected field, even on short words. -/
theorem install_coefficients_lt (c : Context) (bits : List Bool) :
    let c' := (install (c, bits)).1
    c'.c0 < 2 ^ width c ∧ c'.c1 < 2 ^ width c ∧
      c'.c2 < 2 ^ width c ∧ c'.c3 < 2 ^ width c := by
  have h (xs : List Bool) : ofBits (xs.take (width c)) < 2 ^ width c := by
    rw [ofBits_eq_lsbValue]
    exact (lsbValue_lt _).trans_le (Nat.pow_le_pow_right (by decide) (List.length_take_le _ _))
  exact ⟨h _, h _, h _, h _⟩

/-- Every genuine seed is installed exactly, and its four choices persist for the entire
remaining suffix. -/
theorem install_word (c : Context)
    (seed : BalancedSchedules.SeededLabels.Seed c.universeSize (6 * c.labelLength))
    (rest : List Bool) :
    install (c, word seed ++ rest) =
      ({c with c0 := seed 0, c1 := seed 1, c2 := seed 2, c3 := seed 3}, rest) := by
  have ht (d x : ℕ) (tail : List Bool) : (lowBits d x ++ tail).take d = lowBits d x := by
    conv_lhs => arg 1; rw [← length_lowBits d x]
    exact List.take_left
  have hd (d x : ℕ) (tail : List Bool) : (lowBits d x ++ tail).drop d = tail := by
    conv_lhs => arg 1; rw [← length_lowBits d x]
    exact List.drop_left
  simp only [install, width, word, List.append_assoc, ht, hd, ofBits_eq_lsbValue,
    lsbValue_lowBits (seed 0).isLt, lsbValue_lowBits (seed 1).isLt,
    lsbValue_lowBits (seed 2).isLt, lsbValue_lowBits (seed 3).isLt]

/-- The field degree is computed in unary from a binary universe size and unary label length. -/
theorem computableInPolyTime_width {α : Type} {enc : α ↪ List Bool} {c : α → Context}
    (hc : ComputableInPolyTime c enc encContext) :
    ComputableInPolyTime (fun x => width (c x)) enc encUnary :=
  unary_mul' (const 2) (TrinomialArithmetic.computableInPolyTime_limb
    (SeededPredecessor.encContext_universeSize_polyTime hc)
    (unary_mul' (const 6) (SeededPredecessor.encContext_labelLength_polyTime hc)))

/-- Decoding the chosen coefficients and retaining the later player moves is polynomial time
on the short shared context and choice word. -/
theorem computableInPolyTime_install : ComputableInPolyTime install encData encData := by
  have hc := fst encContext encBits
  have hd := computableInPolyTime_width hc
  have h₀ := snd encContext encBits
  have h₁ := bitsDropWithInput h₀ hd
  have h₂ := bitsDropWithInput h₁ hd
  have h₃ := bitsDropWithInput h₂ hd
  exact (SeededPredecessor.encContext_mk_polyTime
    (SeededPredecessor.encContext_universeSize_polyTime hc)
    (SeededPredecessor.encContext_labelLength_polyTime hc)
    (bitsToNat.comp (bitsTakeWithInput h₀ hd)) (bitsToNat.comp (bitsTakeWithInput h₁ hd))
    (bitsToNat.comp (bitsTakeWithInput h₂ hd)) (bitsToNat.comp (bitsTakeWithInput h₃ hd))
    (SeededPredecessor.encContext_edge_polyTime hc)
    (SeededPredecessor.encContext_candidate_polyTime hc)).prod (bitsDropWithInput h₃ hd)

end Cslib.SeedChoice
