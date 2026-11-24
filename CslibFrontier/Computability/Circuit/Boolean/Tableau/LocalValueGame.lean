/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Tableau.ValueGame
import Mathlib.Data.Nat.Size
import CslibFrontier.Tactic.EncLen

/-!
# Claims of logarithmic length in the circuit-value game on the tableau

The circuit-value game on the tableau of a machine (`Cslib.Circuits.Boolean.Tableau.ValueGame`)
stores a claim `⟨x, T, w, v⟩` with the whole input `x`, which is what the alternating
polynomial-space machine of `Cslib.Complexity.EXP_subset_APSPACE` keeps on a work tape. An
alternating machine within space `s` cannot store `x` when `s` is sublinear, but it does not need
to: on an input `x`, every position reachable from a claim about `x` is the position of a claim
about `x` (`Cslib.Circuits.Boolean.Tableau.ValueGame.reach_position`), and the input stays on the
read-only input tape. The encoding of claims relative to `x`
(`Cslib.Circuits.Boolean.Tableau.ValueGame.encLocal`) therefore stores a claim about `x` by the
length of `x`, its step count and wire in binary, and its value, but not the bits of `x`. Since
the game is stated for an arbitrary injective encoding of claims, at `encC := encLocal x` the
existential player still wins exactly the true claims
(`Cslib.Circuits.Boolean.Tableau.ValueGame.wins_position_iff`), so the game on the output claim
still decides the run of the machine
(`Cslib.Circuits.Boolean.Tableau.ValueGame.wins_position_outWire_iff`), and every play still ends;
now every reachable position has length `O(log n + log T)` for inputs of length `n`
(`Cslib.Circuits.Boolean.Tableau.ValueGame.exists_length_le_of_reach_encLocal`).

This is a step towards the inclusion `DTIME(2 ^ O(s)) ⊆ ASPACE(s)` of
[Chandra, Kozen and Stockmeyer, Section 3][ChandraKozenStockmeyer1981]
[Sipser, Section 10.3][Sipser2013], and not that inclusion: for a machine within time
`T = 2 ^ O(s n)` and `log₂ n ≤ s n`, the claims of this game have `O(s n)` bits. What remains for
the inclusion (#4086) is an alternating machine that plays this game within space `O(s n)`: its
round must read the input bit under a claimed input wire from the input tape, by an index of
`O(log n)` bits, instead of from a stored copy, and its preparation must write the step count `T`,
which needs a constructibility hypothesis on `s`.

## Main definitions

* `Cslib.Circuits.Boolean.Tableau.ValueGame.encLocal`: the encoding of claims relative to an input.

## Main results

* `Cslib.Circuits.Boolean.Tableau.ValueGame.length_position_encLocal_le`: the position of a claim
  about `x` has length linear in the binary lengths of `x.length`, its step count and its wire.
* `Cslib.Circuits.Boolean.Tableau.ValueGame.exists_length_le_of_reach_encLocal`: every position
  reachable from a claim about a wire of the tableau of `T` steps on `x` has length
  `O(log x.length + log T)`.

## References

* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*][ChandraKozenStockmeyer1981]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

public section

namespace Cslib.Circuits.Boolean.Tableau

namespace ValueGame

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeATM WordGame

variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]
  {tm : _root_.Turing.MultiTapeTM k Bool State}

/-- **Claims relative to the input `x`.** A claim `⟨x, T, w, v⟩` about `x` is encoded as the tag
bit `false` followed by the framed length of `x`, the framed step count `T` and the framed wire
`w`, all three in binary (`encNat`), and the claimed bit `v`. The bits of `x` are not stored: the
gate of a wire (`Cslib.Circuits.Boolean.Tableau.gateCode`) depends only on the length of the input,
the step count and the wire, so only the outcome of a claim about an input wire reads `x`, at that
one position. A claim about another input is encoded as the tag bit `true` followed by
`encClaim`. -/
def encLocal (x : List Bool) : Claim ↪ List Bool where
  toFun c :=
    if c.input = x then
      false :: encPair encNat (encPair encNat (encPair encNat encBool))
        (c.input.length, c.steps, c.wire, c.value)
    else true :: encClaim c
  inj' c d h := by
    by_cases hc : c.input = x <;> by_cases hd : d.input = x <;>
      simp only [hc, hd, ↓reduceIte, List.cons.injEq, Bool.false_eq_true,
        Bool.true_eq_false, false_and, true_and] at h
    · have h' := (encPair encNat (encPair encNat (encPair encNat encBool))).injective h
      simp only [Prod.mk.injEq] at h'
      exact Claim.ext (hc.trans hd.symm) h'.2.1 h'.2.2.1 h'.2.2.2
    · exact encClaim.injective h

/-- A claim about `x` is encoded relative to `x` by the length of `x`, its step count, wire and
value. -/
@[simp]
theorem encLocal_self (x : List Bool) (T w : ℕ) (v : Bool) :
    encLocal x ⟨x, T, w, v⟩ =
      false :: encPair encNat (encPair encNat (encPair encNat encBool)) (x.length, T, w, v) := by
  simp [encLocal]

/-- A claim about another input is encoded relative to `x` by `encClaim`, after the tag bit
`true`. -/
theorem encLocal_of_ne {x : List Bool} {c : Claim} (h : c.input ≠ x) :
    encLocal x c = true :: encClaim c := by
  simp [encLocal, h]

/-- The position of a claim about `x`, encoded relative to `x`, has length linear in the binary
lengths of the length of `x`, the step count and the wire. -/
theorem length_position_encLocal_le (x : List Bool) (T w : ℕ) (v : Bool) :
    (position tm (encLocal x) ⟨x, T, w, v⟩).length ≤
      2 * Nat.size x.length + 2 * Nat.size T + 2 * Nat.size w + 10 := by
  refine (length_position_le _).trans ?_
  have hn : (encNat x.length).length = Nat.size x.length := by
    simp [encNat_apply, Nat.size_eq_bits_len]
  have hT : (encNat T).length = Nat.size T := by simp [encNat_apply, Nat.size_eq_bits_len]
  have hw : (encNat w).length = Nat.size w := by simp [encNat_apply, Nat.size_eq_bits_len]
  rw [encLocal_self]
  enc_len [hn, hT, hw, List.length_cons]

omit [DecidableEq State] in
/-- The tableau of `T` steps has at most `c * (T + 1) ^ 2` gates, for a constant `c` of the
machine's shape. -/
private theorem exists_numGates_le : ∃ c, ∀ T, numGates k State T ≤ c * (T + 1) ^ 2 := by
  refine ⟨2 * (scanWidth k + colWidth k) + globWidth k State + gfWidth State + 2, fun T => ?_⟩
  unfold numGates blockSize colStart gfStart globStart numCols
  have h1 : 1 ≤ T + 1 := by omega
  nlinarith [Nat.zero_le (scanWidth k), Nat.zero_le (colWidth k), Nat.zero_le (globWidth k State),
    Nat.zero_le (gfWidth State), Nat.mul_le_mul_left (T + 1) h1]

omit [DecidableEq State] in
/-- The binary length of the number of wires of the tableau of `T` steps on inputs of length `n`
is `log n + 2 log T + O(1)`. -/
private theorem exists_size_add_numGates_le :
    ∃ c, ∀ n T, Nat.size (n + numGates k State T) ≤ Nat.size n + 2 * Nat.size T + c := by
  obtain ⟨C, hC⟩ := exists_numGates_le (k := k) (State := State)
  refine ⟨Nat.size C + 1, fun n T => ?_⟩
  rw [Nat.size_le]
  have hn : n < 2 ^ Nat.size n := Nat.lt_size_self n
  have hT : T + 1 ≤ 2 ^ Nat.size T := Nat.lt_size_self T
  have hCs : C < 2 ^ Nat.size C := Nat.lt_size_self C
  have hG : numGates k State T < 2 ^ Nat.size C * (2 ^ Nat.size T) ^ 2 + 1 := by
    have := hC T
    have : C * (T + 1) ^ 2 ≤ 2 ^ Nat.size C * (2 ^ Nat.size T) ^ 2 :=
      Nat.mul_le_mul hCs.le (Nat.pow_le_pow_left hT 2)
    omega
  have h1 : 1 ≤ 2 ^ Nat.size n := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ Nat.size C * (2 ^ Nat.size T) ^ 2 :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hpow : 2 ^ (Nat.size n + 2 * Nat.size T + (Nat.size C + 1)) =
      2 * (2 ^ Nat.size n * (2 ^ Nat.size C * (2 ^ Nat.size T) ^ 2)) := by
    rw [← pow_mul, mul_comm (Nat.size T) 2, ← pow_add, ← pow_add, ← pow_succ']
    ring_nf
  rw [hpow]
  nlinarith

/-- **Positions of logarithmic length.** On an input `x` of length `n`, every position of the
circuit-value game reachable from a claim about a wire of the tableau of `T` steps has length at
most `4 * Nat.size n + 6 * Nat.size T + c`, when claims are encoded relative to `x`; the constant
`c` depends only on the number of tapes and states of the machine. With
`Cslib.Circuits.Boolean.Tableau.ValueGame.wins_position_iff` and
`Cslib.Circuits.Boolean.Tableau.ValueGame.ends_position` at `encC := encLocal x`, this is the game,
on claims of `O(log n + log T)` bits, that an alternating machine plays in the step
`DTIME(2 ^ O(s)) ⊆ ASPACE(s)` of
[Chandra, Kozen and Stockmeyer, Section 3][ChandraKozenStockmeyer1981]. -/
theorem exists_length_le_of_reach_encLocal :
    ∃ c, ∀ (x : List Bool) (T w₀ : ℕ) (v₀ : Bool) (w : List Bool),
      w₀ < x.length + numGates k State T →
      Reach (update tm (encLocal x)) (position tm (encLocal x) ⟨x, T, w₀, v₀⟩) w →
      w.length ≤ 4 * Nat.size x.length + 6 * Nat.size T + c := by
  obtain ⟨c, hc⟩ := exists_size_add_numGates_le (k := k) (State := State)
  refine ⟨2 * c + 10, fun x T w₀ v₀ w hw₀ h => ?_⟩
  obtain ⟨w', v, hw', rfl⟩ := reach_position (tm := tm) (encLocal x) hw₀ h
  have hs : Nat.size w' ≤ Nat.size (x.length + numGates k State T) := Nat.size_le_size hw'.le
  have := hc x.length T
  have := length_position_encLocal_le (tm := tm) x T w' v
  omega

end ValueGame

end Cslib.Circuits.Boolean.Tableau
