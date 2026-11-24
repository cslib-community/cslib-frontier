/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Tableau.ValueGame
import Mathlib.Data.Nat.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.BitList
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Cases
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.ListSlice
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

The game reads the input once per round. On a claim about `x`, the update after a move is the
position of the next claim, which depends on `x` only through the one bit `x[w]?` at the wire `w`
of the next claim (`Cslib.Circuits.Boolean.Tableau.ValueGame.update_encLocal`). Everything else is
a function of the local data of the claim
(`Cslib.Circuits.Boolean.Tableau.ValueGame.LocalClaim`): the length of `x`, the step count, the
wire and the value. The next local claim and the position given the read bit are computed within
linear space in the local data
(`Cslib.Circuits.Boolean.Tableau.ValueGame.LocalClaim.next_inSpace`,
`Cslib.Circuits.Boolean.Tableau.ValueGame.localPosition_inSpace`). A round is thus a round of a
query machine (`Turing.QueryMachine`): a state of `O(log n + log T)` bits, the position of the
input bit it reads, and the next state given that bit. `Turing.MultiTapeTM.ComputableInSpace` does
not charge the read-only input, so the read itself costs `O(log n)` work space
(`Turing.MultiTapeTM.ComputableInSpace.inputBit`).

This is a step towards the inclusion `DTIME(2 ^ O(s)) ⊆ ASPACE(s)` of
[Chandra, Kozen and Stockmeyer, Section 3][ChandraKozenStockmeyer1981]
[Sipser, Section 10.3][Sipser2013], and not that inclusion: for a machine within time
`T = 2 ^ O(s n)` and `log₂ n ≤ s n`, the claims of this game have `O(s n)` bits and its rounds read
one input bit each. What remains for the inclusion (#4086) is an alternating machine that plays a
game with such rounds within space `O(s n)`, keeping the state on a work tape and reading the input
in place (an alternating counterpart of `Turing.NondeterministicQueryMachine.exists_routines`), and
a preparation that writes the step count `T`, which needs a constructibility hypothesis on `s`.

## Main definitions

* `Cslib.Circuits.Boolean.Tableau.ValueGame.LocalClaim`: the data of a claim without its input.
* `Cslib.Circuits.Boolean.Tableau.ValueGame.encLocal`: the encoding of claims relative to an input.
* `Cslib.Circuits.Boolean.Tableau.ValueGame.localPosition`: the position of a local claim, given
  the input bit at its wire.

## Main results

* `Cslib.Circuits.Boolean.Tableau.ValueGame.length_position_encLocal_le`: the position of a claim
  about `x` has length linear in the binary lengths of `x.length`, its step count and its wire.
* `Cslib.Circuits.Boolean.Tableau.ValueGame.exists_length_le_of_reach_encLocal`: every position
  reachable from a claim about a wire of the tableau of `T` steps on `x` has length
  `O(log x.length + log T)`.
* `Cslib.Circuits.Boolean.Tableau.ValueGame.update_encLocal`: the update reads one input bit, at
  the wire of the next claim.
* `Cslib.Circuits.Boolean.Tableau.ValueGame.LocalClaim.next_inSpace`,
  `Cslib.Circuits.Boolean.Tableau.ValueGame.localPosition_inSpace`: the rest of a round within
  linear space in the local data.

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

/-- **The data of a claim about an input that does not repeat it**: the length of the input, the
step count, the wire and the claimed value. -/
@[ext]
structure LocalClaim where
  /-- The length `n` of the machine input. -/
  length : ℕ
  /-- The step count `T` of the tableau. -/
  steps : ℕ
  /-- The wire index `w` in the tableau circuit. -/
  wire : ℕ
  /-- The claimed Boolean value `v` on wire `w`. -/
  value : Bool

/-- The encoding of local claims: the framed length, the framed step count and the framed wire, all
three in binary (`encNat`), then the claimed bit. These are the encoded words of
`encPair encNat (encPair encNat (encPair encNat encBool))`. -/
enc_structure encLocalClaim : LocalClaim where
  length : encNat, steps : encNat, wire : encNat, value : encBool

/-- The local data of a claim: the length of its input, its step count, wire and value. -/
def Claim.toLocal (c : Claim) : LocalClaim := ⟨c.input.length, c.steps, c.wire, c.value⟩

/-- The local data of a claim `⟨x, T, w, v⟩` is `⟨x.length, T, w, v⟩`. -/
@[simp]
theorem Claim.toLocal_mk (x : List Bool) (T w : ℕ) (v : Bool) :
    Claim.toLocal ⟨x, T, w, v⟩ = ⟨x.length, T, w, v⟩ := by
  rw [Claim.toLocal]

/-- **Claims relative to the input `x`.** A claim about `x` is encoded as the tag bit `false`
followed by its local data (`encLocalClaim`): the length of `x`, the step count `T` and the wire
`w`, all three in binary, and the claimed bit `v`. The bits of `x` are not stored: the gate of a
wire (`Cslib.Circuits.Boolean.Tableau.gateCode`) depends only on the length of the input, the step
count and the wire, so only the outcome of a claim about an input wire reads `x`, at that one
position. A claim about another input is encoded as the tag bit `true` followed by `encClaim`. -/
def encLocal (x : List Bool) : Claim ↪ List Bool where
  toFun c := if c.input = x then false :: encLocalClaim c.toLocal else true :: encClaim c
  inj' c d h := by
    by_cases hc : c.input = x <;> by_cases hd : d.input = x <;>
      simp only [hc, hd, ↓reduceIte, List.cons.injEq, Bool.false_eq_true,
        Bool.true_eq_false, false_and, true_and] at h
    · have h' := encLocalClaim.injective h
      simp only [Claim.toLocal, LocalClaim.mk.injEq] at h'
      exact Claim.ext (hc.trans hd.symm) h'.2.1 h'.2.2.1 h'.2.2.2
    · exact encClaim.injective h

/-- A claim about `x` is encoded relative to `x` by its local data. -/
theorem encLocal_of_eq {x : List Bool} {c : Claim} (h : c.input = x) :
    encLocal x c = false :: encLocalClaim c.toLocal := by
  simp [encLocal, h]

/-- A claim about `x` is encoded relative to `x` by the length of `x`, its step count, wire and
value. -/
@[simp]
theorem encLocal_self (x : List Bool) (T w : ℕ) (v : Bool) :
    encLocal x ⟨x, T, w, v⟩ = false :: encLocalClaim ⟨x.length, T, w, v⟩ :=
  encLocal_of_eq rfl

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
  enc_len [hn, hT, hw, List.length_cons, encLocalClaim_apply, List.length_singleton]

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

/-! ### The round reads one input bit -/

section Round

variable (tm) in
/-- The gate of the wire of a local claim (`Cslib.Circuits.Boolean.Tableau.ValueGame.Claim.gate`).
-/
noncomputable def LocalClaim.gate (lc : LocalClaim) : Op × List ℕ :=
  gateCode tm lc.length lc.steps (lc.wire - lc.length)

variable (tm) in
/-- The local claim after the move `b`
(`Cslib.Circuits.Boolean.Tableau.ValueGame.Claim.next`). -/
noncomputable def LocalClaim.next (lc : LocalClaim) (b : Bool) : LocalClaim :=
  ⟨lc.length, lc.steps,
    if b then (lc.gate tm).2.reverse.headD 0 else (lc.gate tm).2.headD 0,
    if (lc.gate tm).1 = .not then !lc.value else lc.value⟩

variable (tm) in
/-- The position, relative to an input `x`, of a claim about `x` with local data `lc`, given the
read `r = x[lc.wire]?` of the input at its wire (`none` past the end of `x`): the won or lost
terminal position when the claim has an outcome, and otherwise the player, a move cell and the
claim encoded relative to `x`. -/
noncomputable def localPosition : LocalClaim × Option Bool → List Bool
  | (lc, r) =>
    if (outcomeOf (decide (lc.wire < lc.length), r.getD false, (lc.gate tm).1, lc.value)).isSome
    then
      if (outcomeOf (decide (lc.wire < lc.length), r.getD false, (lc.gate tm).1,
        lc.value)).getD false then [true] else []
    else playerOf ((lc.gate tm).1, lc.value) :: false :: false :: encLocalClaim lc

/-- The local data of the claim after a move is the local claim after that move. -/
private theorem toLocal_next (c : Claim) (b : Bool) :
    (Claim.next tm c b).toLocal = c.toLocal.next tm b := by
  rw [Claim.next_eq]
  simp only [Claim.toLocal, LocalClaim.next, LocalClaim.gate, Claim.gate_eq]
  rfl

private theorem headD_drop (x : List Bool) (i : ℕ) : (x.drop i).headD false = x[i]?.getD false := by
  rw [List.headD_eq_head?_getD, List.head?_drop]

/-- The position of a claim about `x`, relative to `x`, is the local position of its local data,
given the input bit at its wire. -/
theorem position_encLocal {x : List Bool} {c : Claim} (h : c.input = x) :
    position tm (encLocal x) c = localPosition tm (c.toLocal, x[c.toLocal.wire]?) := by
  rw [position_eq_ite, outcome_eq_outcomeOf, player_eq_playerOf, encLocal_of_eq h, h, headD_drop]
  simp only [localPosition, Claim.toLocal, LocalClaim.gate, Claim.gate_eq, h]

/-- **The round of the local circuit-value game reads one input bit.** On a claim `c` about `x`,
the update after the move `b`, with claims encoded relative to `x`, is the local position of the
local claim `lc` after the move, given the one input bit `x[lc.wire]?`. Both the next local claim
(`Cslib.Circuits.Boolean.Tableau.ValueGame.LocalClaim.next_inSpace`) and the local position
(`Cslib.Circuits.Boolean.Tableau.ValueGame.localPosition_inSpace`) are computed within linear space
in the local data, which has `O(log n + log T)` bits, and the read is
`Turing.MultiTapeTM.ComputableInSpace.inputBit`. This is the shape of a round of a query machine
(`Turing.QueryMachine`): a state, the position of the bit it reads, and the next state given that
bit. It is a step towards `DTIME(2 ^ O(s)) ⊆ ASPACE(s)`
[Chandra, Kozen and Stockmeyer, Section 3][ChandraKozenStockmeyer1981], not that inclusion: no
alternating machine plays this game yet. -/
theorem update_encLocal {x : List Bool} {c : Claim} (h : c.input = x) (u b : Bool) :
    update tm (encLocal x) (u :: b :: encLocal x c) =
      localPosition tm (c.toLocal.next tm b, x[(c.toLocal.next tm b).wire]?) := by
  have hn : (Claim.next tm c b).input = x := by rw [Claim.next_eq]; exact h
  rw [update_position_cons, position_encLocal hn, toLocal_next]

open ComputableInSpace

/-- The gate of a local claim, within any budget that covers the local claim. -/
private theorem gate_budget {γ : Type} {encIn : γ ↪ List Bool} {Bs : γ → ℕ} {f : γ → LocalClaim}
    (hf : ComputableInSpace f encIn encLocalClaim Bs) :
    ComputableInSpace (fun g => (f g).gate tm) encIn encGate Bs :=
  gateCode_inSpace tm (encLocalClaim_length_budget hf) (encLocalClaim_steps_budget hf)
    (budget_natSub (encLocalClaim_wire_budget hf) (encLocalClaim_length_budget hf))

/-- The local claim after a move is computed within linear space in the encoded local claim. -/
theorem LocalClaim.next_inSpace (b : Bool) :
    ComputableInSpace (fun lc : LocalClaim => lc.next tm b) encLocalClaim encLocalClaim
      fun lc => (encLocalClaim lc).length := by
  have hid := budget_id (enc := encLocalClaim) (.refl _)
  have hgate := gate_budget (tm := tm) hid
  have hargs := snd' hgate
  have hop := fst' hgate
  have hsel : ComputableInSpace
      (fun lc : LocalClaim => if b then (lc.gate tm).2.reverse.headD 0 else (lc.gate tm).2.headD 0)
      encLocalClaim encNat fun lc => (encLocalClaim lc).length := by
    cases b
    · simpa using budget_headD 0 hargs
    · simpa using budget_headD 0 (budget_comp_linear (listReverse encNat) hargs)
  have hv : ComputableInSpace
      (fun lc : LocalClaim => if (lc.gate tm).1 = .not then !lc.value else lc.value)
      encLocalClaim encBool fun lc => (encLocalClaim lc).length :=
    budget_finite (fun p : Op × Bool => if p.1 = .not then !p.2 else p.2)
      (budget_prod hop (encLocalClaim_value_budget hid))
  exact encLocalClaim_mk_budget (encLocalClaim_length_budget hid)
    (encLocalClaim_steps_budget hid) hsel hv

/-- The local position of a local claim, given the read input bit, is computed within linear
space in the encoded local claim and read. -/
theorem localPosition_inSpace :
    ComputableInSpace (localPosition tm) (encPair encLocalClaim (encOption encBool)) encBits
      fun p => (encPair encLocalClaim (encOption encBool) p).length := by
  have hlc := fst encLocalClaim (encOption encBool)
  have hop := fst' (gate_budget (tm := tm) hlc)
  have hw := encLocalClaim_wire_budget hlc
  have hn := encLocalClaim_length_budget hlc
  have hv := encLocalClaim_value_budget hlc
  have hbit := budget_optionGetD false (snd encLocalClaim (encOption encBool))
  have hq : ComputableInSpace
      (fun p : LocalClaim × Option Bool => (decide (p.1.wire < p.1.length), p.2.getD false,
        (p.1.gate tm).1, p.1.value)) (encPair encLocalClaim (encOption encBool))
      (encPair encBool (encPair encBool (encPair (encFinite Op) encBool)))
      fun p => (encPair encLocalClaim (encOption encBool) p).length :=
    budget_prod (budget_natLt hw hn) (budget_prod hbit (budget_prod (budget_finite id hop) hv))
  have hsome := budget_finite (encC := encBool) (fun q => (outcomeOf q).isSome) hq
  have hres := budget_finite (encC := encBits)
    (fun q => if (outcomeOf q).getD false then [true] else []) hq
  have hplayer := budget_finite (encC := encList encBool)
    (fun q : Op × Bool => [playerOf q, false, false]) (budget_prod hop hv)
  have hid : ComputableInSpace (fun p : LocalClaim × Option Bool => encLocalClaim p.1)
      (encPair encLocalClaim (encOption encBool)) encBits
      fun p => (encPair encLocalClaim (encOption encBool) p).length :=
    budget_comp_linear ((of_inO ComputableInDegree.id'.inO_one).of_enc_eq
      (g := fun lc : LocalClaim => encLocalClaim lc) (encC := encBits) fun _ => rfl) hlc
  have hcons := ((budget_comp_linear listToBits hplayer).append hid
    (g := fun p : LocalClaim × Option Bool =>
      playerOf ((p.1.gate tm).1, p.1.value) :: false :: false :: encLocalClaim p.1)
    (encD := encBits) fun p => by simp).weaken (.add (.refl _) (.refl _))
  exact (budget_ite hsome hres hcons).of_enc_eq fun p => by
    obtain ⟨lc, r⟩ := p
    simp only [localPosition]

end Round

end ValueGame

end Cslib.Circuits.Boolean.Tableau
