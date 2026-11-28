/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Interactive.Sumcheck
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Polynomial.Modular
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import Mathlib.Algebra.Field.ZMod
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq

/-!
# A sumcheck round on binary words

Each prover polynomial is a list of binary coefficients in increasing order of degree.
The verifier checks the current claim at zero and one and then evaluates at the new challenge.

## Main definitions

* `Cslib.Interactive.Sumcheck.WordState.advance` performs the verifier's deterministic update.

## Main results

* `Cslib.Interactive.Sumcheck.WordState.advance_ok_iff` characterizes the accumulated check bit.
* `Cslib.Interactive.Sumcheck.WordState.computableInPolyTime_advance` certifies the update.
-/

public section

namespace Cslib.Interactive.Sumcheck

open Turing.MultiTapeTM Polynomial

/-- The verifier's accumulated challenges, partial-sum claim and check bit. -/
structure WordState where
  /-- Previously sampled challenges, in round order. -/
  challenges : List ℕ
  /-- Current claimed partial sum modulo the field size. -/
  claim : ℕ
  /-- Whether all rounds checked so far have passed. -/
  ok : Bool

/-- Framed list of binary challenges, binary claim, and Boolean check bit in that order. -/
enc_structure encWordState : WordState where
  challenges : (encList encNat),
  claim : encNat,
  ok : encBool

/-- Check the row against the old claim and update the claim at challenge `r`. -/
@[expose] def WordState.advance (s : WordState) (p : ℕ) (coeffs : List ℕ) (r : ℕ) : WordState :=
  let checked := decide ((evalCoeffListMod p 0 coeffs + evalCoeffListMod p 1 coeffs) % p =
    s.claim % p)
  ⟨s.challenges ++ [r], evalCoeffListMod p r coeffs, s.ok && checked⟩

/-- The new check bit records acceptance of this polynomial in the field sumcheck protocol,
provided its degree is within the prescribed limit. -/
theorem WordState.advance_ok_iff {p d : ℕ} [Fact p.Prime] (s : WordState) (cs : List ℕ) (r : ℕ)
    (hd : (ofCoeffList (cs.map (Nat.cast : ℕ → ZMod p))).natDegree ≤ d) :
    (s.advance p cs r).ok = true ↔ s.ok = true ∧
      accepts d (s.claim : ZMod p) (ofCoeffList (cs.map Nat.cast)) := by
  simp only [advance, Bool.and_eq_true, decide_eq_true_eq, accepts, hd, true_and]
  rw [← ZMod.natCast_eq_natCast_iff', Nat.cast_add, natCast_evalCoeffListMod,
    natCast_evalCoeffListMod, Nat.cast_zero, Nat.cast_one]

/-- A binary-input verifier computes its entire deterministic round update in polynomial time. -/
@[fun_prop] theorem WordState.computableInPolyTime_advance {α : Type} {e : α ↪ List Bool}
    {s : α → WordState} {p r : α → ℕ} {coeffs : α → List ℕ}
    (hs : ComputableInPolyTime s e encWordState) (hp : ComputableInPolyTime p e encNat)
    (hc : ComputableInPolyTime coeffs e (encList encNat)) (hr : ComputableInPolyTime r e encNat) :
    ComputableInPolyTime (fun x => (s x).advance (p x) (coeffs x) (r x)) e encWordState :=
  open ComputableInPolyTime in
  encWordState_mk_polyTime
    ((encWordState_challenges_polyTime hs).listAppend' (hr.cons' (const [])))
    (evalCoeffListMod hp hr hc)
    ((encWordState_ok_polyTime hs).bool_and' (decide_eq'
      (binary_mod' (binary_add' (evalCoeffListMod hp (const 0) hc)
        (evalCoeffListMod hp (const 1) hc)) hp)
      (binary_mod' (encWordState_claim_polyTime hs) hp)))

end Cslib.Interactive.Sumcheck
