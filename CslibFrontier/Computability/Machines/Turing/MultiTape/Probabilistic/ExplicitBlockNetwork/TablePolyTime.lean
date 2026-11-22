/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.ExplicitBlockNetwork.Table
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.ExplicitBlockNetwork.GraphPolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.IntervalCount.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Fin
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.OfBits
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryDivision
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPower
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListLookup
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimePiPrimitives

/-!
# Compiling entries and constructing explicit block-counting tables

A single table entry compiles to one interval record or a Boolean constant
(`Turing.MultiTapePTM.tableEntryPlan`). The compiler computes and validates the letter codes at
the selected vertex from its binary local assignment, without listing coin strings or table
entries. `tableEntryPlan_spec` identifies the result with the existing numeric tensor entry.
The native alternating entry evaluator consumes this program directly.

The explicit block-counting network on numbers (`Turing.MultiTapePTM.explicitNetworkNum`) is
computable in polynomial time from the input, the block length and the number of intervals in
unary, and the schedule number in binary, provided that `2 ^ b` is bounded by a computed unary
number. Its tables have `2 ^ (number of ports)` entries, at most `(2 ^ b) ^ (2 (3 k + 1) (s + k +
4))`, and each entry decodes letters by arithmetic and evaluates an interval count
(`Turing.MultiTapePTM.computableInPolyTime_localIntervalCount`).

## Main results

* `Turing.MultiTapePTM.computableInPolyTime_decodeControlData`,
  `Turing.MultiTapePTM.computableInPolyTime_contentsCellNum`: decoding letters.
* `Turing.MultiTapePTM.tableEntryPlan_spec`,
  `Turing.MultiTapePTM.computableInPolyTime_tableEntryPlan`: one entry compiled to an interval
  count or a Boolean constant, without an exponential enumeration budget.
* `Turing.MultiTapePTM.computableInPolyTime_intervalEntryNum`: the tensor of an interval on
  numbers, under the deterministic enumeration budget.
* `Turing.MultiTapePTM.computableInPolyTime_explicitNetworkNum`: the explicit network on numbers,
  as its number of edges in unary and its vertices, with ports and table entries in binary.
-/

public section

namespace Turing.MultiTapePTM

open MultiTapeTM ComputableInPolyTime MultiTapeNTM.ChoiceTable

variable {k s : ℕ} {State : Type} {α : Type} {inp : α ↪ List Bool}

/-! ### Small numbers and digits -/

/-- A binary number reduced modulo `3`, as an element of `Fin 3`. -/
private theorem fin3 {v : α → ℕ} (hv : ComputableInPolyTime v inp encNat) :
    ComputableInPolyTime (fun a => (⟨v a % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3)) inp
      (encFinite (Fin 3)) := by
  have hu : ComputableInPolyTime (fun a => v a % 3) inp encUnary :=
    binary_to_unary_bounded (binary_mod.comp (hv.prod (const 3))) (const 2) fun a => by omega
  have h := (unary_finMod (by norm_num : 0 < 3) (encFinite (Fin 3))).comp hu
  simpa only [Function.comp_def, Nat.mod_mod] using h

/-- The number of control records, in binary. -/
private theorem controlCount' {b : α → ℕ} (hb : ComputableInPolyTime b inp encUnary) :
    ComputableInPolyTime (fun a => controlCount k s (b a)) inp encNat := by
  unfold controlCount
  exact binary_mul' (const _) (binary_mul' (binary_pow' (unary_to_binary.comp hb) (const _))
    (const 3))

/-- The number of letters, in binary. -/
private theorem letterCount' {b : α → ℕ} (hb : ComputableInPolyTime b inp encUnary) :
    ComputableInPolyTime (fun a => letterCount k s (b a)) inp encNat := by
  unfold letterCount
  exact binary_add.comp ((controlCount' hb).prod (binary_pow' (const 3) hb))

/-! ### Decoding letters -/

/-- **Cells of block contents are polynomial-time.** -/
theorem computableInPolyTime_contentsCellNum {b n r : α → ℕ}
    (hb : ComputableInPolyTime b inp encUnary) (hn : ComputableInPolyTime n inp encNat)
    (hr : ComputableInPolyTime r inp encUnary) :
    ComputableInPolyTime (fun a => contentsCellNum k s (b a) (n a) (r a)) inp
      (encOption encBool) := by
  have hC := controlCount' (k := k) (s := s) hb
  unfold contentsCellNum
  refine ite_decide (binary_lt' hn hC) (const none) ?_
  exact (of_finite (encIn := encFinite (Fin 3)) (encOut := encOption encBool)
    cellEquiv.symm).comp (fin3 (binary_div.comp ((binary_sub' hn hC).prod
      (binary_pow' (const 3) hr))))

variable [Finite State]

/-- **Control records of numbers are polynomial-time**, on plain data. -/
theorem computableInPolyTime_decodeControlData (e : State ≃ Fin s) {b n : α → ℕ}
    (hb : ComputableInPolyTime b inp encUnary) (hb0 : ∀ a, 0 < b a)
    (hn : ComputableInPolyTime n inp encNat) :
    ComputableInPolyTime (fun a => decodeControlData (k := k) e (b a) (n a)) inp
      encControlData := by
  have hbB : ComputableInPolyTime b inp encNat := unary_to_binary.comp hb
  have hD : ComputableInPolyTime (fun a => b a ^ (k + 1) * 3) inp encNat :=
    binary_mul' (binary_pow' hbB (const _)) (const 3)
  have hrem : ComputableInPolyTime (fun a => n a % (b a ^ (k + 1) * 3)) inp encNat :=
    binary_mod.comp (hn.prod hD)
  have hstate : ComputableInPolyTime (fun a => stateOfFin e
      ⟨min s (n a / (b a ^ (k + 1) * 3)) % (s + 1), Nat.mod_lt _ (by omega)⟩) inp
      (encFinite (Option State)) :=
    (of_finite (encIn := encFinite (Fin (s + 1))) (encOut := encFinite (Option State))
      (stateOfFin e)).comp ((unary_finMod (Nat.succ_pos s) (encFinite (Fin (s + 1)))).comp
        (binary_min_unary' (const s) (binary_div.comp (hn.prod hD))))
  have hoff : ComputableInPolyTime (fun a (head : Option (Fin k)) =>
      n a % (b a ^ (k + 1) * 3) / 3 / b a ^ ((finSuccEquiv k).symm head : ℕ) % b a) inp
      (encPi encUnary) := by
    refine pi fun head => binary_to_unary_bounded ?_ hb fun a => (Nat.mod_lt _ (hb0 a)).le
    exact binary_mod.comp ((binary_div.comp ((binary_div.comp (hrem.prod (const 3))).prod
      (binary_pow' hbB (const _)))).prod hbB)
  have htrack : ComputableInPolyTime (fun a => OutputTrack.equivFin.symm
      ⟨n a % (b a ^ (k + 1) * 3) % 3, Nat.mod_lt _ (by norm_num)⟩) inp
      (encFinite OutputTrack) :=
    (of_finite (encIn := encFinite (Fin 3)) (encOut := encFinite OutputTrack)
      OutputTrack.equivFin.symm).comp (fin3 hrem)
  exact ControlData.computableInPolyTime_mk hstate hoff htrack

/-- Entering control records from letter numbers are polynomial-time. -/
theorem computableInPolyTime_controlDataOfNum (e : State ≃ Fin s) {b n : α → ℕ}
    (hb : ComputableInPolyTime b inp encUnary) (hb0 : ∀ a, 0 < b a)
    (hn : ComputableInPolyTime n inp encNat) :
    ComputableInPolyTime (fun a => controlDataOfNum (k := k) e (b a) (n a)) inp
      encControlData := by
  unfold controlDataOfNum
  exact ite_decide (binary_lt' hn (controlCount' hb))
    (computableInPolyTime_decodeControlData e hb hb0 hn) (const _)

/-! ### Block indices, movements and the entering window -/

/-- Block indices as digit counts are polynomial-time. -/
theorem computableInPolyTime_blockIndexNum {σ i : α → ℕ}
    (hσ : ComputableInPolyTime σ inp encNat) (hi : ComputableInPolyTime i inp encUnary) :
    ComputableInPolyTime (fun a => blockIndexNum k (σ a) (i a)) inp (encPi encIntBin) := by
  refine pi fun head => ?_
  have hcount := fun δ => computableInPolyTime_digitCount (k := k) hσ
    (const ((finSuccEquiv k).symm head : ℕ)) (const δ) hi
  exact intBin_sub.comp ((intBin_natCast.comp (unary_to_binary.comp (hcount 2))).prod
    (intBin_natCast.comp (unary_to_binary.comp (hcount 0))))

/-- Block movements of a schedule number are polynomial-time. -/
theorem computableInPolyTime_blockMoveNum {σ i : α → ℕ}
    (hσ : ComputableInPolyTime σ inp encNat) (hi : ComputableInPolyTime i inp encUnary) :
    ComputableInPolyTime (fun a => blockMoveNum k (σ a) (i a)) inp
      (encFinite (Option (Fin k) → SignType)) := by
  have hpi : ComputableInPolyTime (fun a => blockMoveNum k (σ a) (i a)) inp
      (encPi (encFinite SignType)) := by
    refine pi fun head => ?_
    have hpos : ComputableInPolyTime (fun a => ((finSuccEquiv k).symm head : ℕ) + (k + 1) * i a)
        inp encUnary := unary_add' (const _) (unary_mul' (const _) hi)
    exact (of_finite (encIn := encFinite (Fin 3)) (encOut := encFinite SignType)
      signEquiv.symm).comp (fin3 (binary_div.comp (hσ.prod (binary_pow' (const 3) hpos))))
  exact (of_finite (encIn := encPi (encFinite SignType))
    (encOut := encFinite (Option (Fin k) → SignType)) id).comp hpi

/-- Previous appearances on numbers are polynomial-time. -/
theorem computableInPolyTime_lastBeforeNum {σ c i δ : α → ℕ}
    (hσ : ComputableInPolyTime σ inp encNat) (hc : ComputableInPolyTime c inp encUnary)
    (hi : ComputableInPolyTime i inp encUnary) (hδ : ComputableInPolyTime δ inp encUnary) :
    ComputableInPolyTime (fun a => lastBeforeNum k (σ a) (c a) (i a) (δ a)) inp
      (encOption encUnary) := by
  unfold lastBeforeNum
  have hi1 : ComputableInPolyTime (fun p : α × ℕ => i p.1 - 1 - p.2) (encPair inp encUnary)
      encUnary := unary_sub' (unary_sub' (hi.comp (fst _ _)) (const 1)) (snd _ _)
  refine optionMapWithInput (findWithInput (range.comp hi) ?_) hi1
  exact computableInPolyTime_inWindowNum (hσ.comp (fst _ _)) (hc.comp (fst _ _))
    (hi.comp (fst _ _)) (hδ.comp (fst _ _)) hi1

/-- Window entries on numbers are polynomial-time. -/
theorem computableInPolyTime_portOfNum {σ c i i' δ : α → ℕ}
    (hσ : ComputableInPolyTime σ inp encNat) (hc : ComputableInPolyTime c inp encUnary)
    (hi : ComputableInPolyTime i inp encUnary) (hi' : ComputableInPolyTime i' inp encUnary)
    (hδ : ComputableInPolyTime δ inp encUnary) :
    ComputableInPolyTime (fun a => portOfNum k (σ a) (c a) (i a) (i' a) (δ a)) inp encUnary := by
  have hcount := fun {j : α → ℕ} (hj : ComputableInPolyTime j inp encUnary) (d : ℕ) =>
    computableInPolyTime_digitCount (k := k) hσ hc (const d) hj
  unfold portOfNum
  exact unary_mod.comp ((unary_sub' (unary_add' (unary_add' (hcount hi 2) (hcount hi' 0)) hδ)
    (unary_add' (hcount hi 0) (hcount hi' 2))).prod (const 3))

/-! ### The tensor of an interval -/

/-- A computed unary bound on `2 ^ b` gives the budget of the interval counts. -/
private theorem budget_of_cap {b cap : α → ℕ} (hcap : ComputableInPolyTime cap inp encUnary)
    (h2b : ∀ a, 2 ^ b a ≤ cap a) :
    ∃ size : ℕ → ℕ, Cslib.PolynomiallyBounded size ∧
      ∀ a, 2 ^ b a * (2 * b a + 1) ≤ size (inp a).length := by
  obtain ⟨bound, hbound, hle⟩ := polyBounded hcap
  refine ⟨fun n => bound n * (2 * bound n + 1), by fun_prop, fun a => ?_⟩
  have h1 : 2 ^ b a ≤ bound (inp a).length := (h2b a).trans (hle a)
  have h2 : b a < 2 ^ b a := Nat.lt_two_pow_self
  exact Nat.mul_le_mul h1 (by omega)

/-- A letter number at a computed edge number. -/
private theorem letter_comp {β : Type} {encβ : β ↪ List Bool} {L : α → ℕ → ℕ}
    (hL : ComputableInPolyTime (fun p : α × ℕ => L p.1 p.2) (encPair inp encUnary) encNat)
    {g : β → α} {n : β → ℕ} (hg : ComputableInPolyTime g encβ inp)
    (hn : ComputableInPolyTime n encβ encUnary) :
    ComputableInPolyTime (fun c => L (g c) (n c)) encβ encNat :=
  hL.comp (hg.prod hn)

section Interval

variable [DecidableEq State] (e : State ≃ Fin s) (machine : MultiTapePTM k Bool State)
  {x : α → List Bool} {b q σ cap : α → ℕ} {L : α → ℕ → ℕ}

/-- The cells of a window entering an interval are polynomial-time. -/
theorem computableInPolyTime_inCellsNum (h : ℕ) {i : α → ℕ}
    (hb : ComputableInPolyTime b inp encUnary) (hq : ComputableInPolyTime q inp encUnary)
    (hσ : ComputableInPolyTime σ inp encNat)
    (hL : ComputableInPolyTime (fun p : α × ℕ => L p.1 p.2) (encPair inp encUnary) encNat)
    (hi : ComputableInPolyTime i inp encUnary) :
    ComputableInPolyTime (fun a => inCellsNum k (q a) s (b a) (σ a) (L a) (i a) h) inp
      (encList (encOption encBool)) := by
  unfold inCellsNum
  have hcb : ComputableInPolyTime (fun p : α × ℕ => p.2 / b p.1) (encPair inp encUnary)
      encUnary := unary_div.comp ((snd _ _).prod (hb.comp (fst _ _)))
  refine mapWithInput (range.comp (unary_mul' (const 3) hb))
    (optionElimWithInput (computableInPolyTime_lastBeforeNum (hσ.comp (fst _ _)) (const _)
      (hi.comp (fst _ _)) hcb) (const none) ?_)
  have ha : ComputableInPolyTime (fun r : (α × ℕ) × ℕ => r.1.1)
      (encPair (encPair inp encUnary) encUnary) inp := (fst _ _).comp (fst _ _)
  have hc : ComputableInPolyTime (fun r : (α × ℕ) × ℕ => r.1.2)
      (encPair (encPair inp encUnary) encUnary) encUnary := (snd _ _).comp (fst _ _)
  have hi' : ComputableInPolyTime (fun r : (α × ℕ) × ℕ => r.2)
      (encPair (encPair inp encUnary) encUnary) encUnary := snd _ _
  refine computableInPolyTime_contentsCellNum (hb.comp ha) (letter_comp hL ha ?_)
    (unary_mod.comp (hc.prod (hb.comp ha)))
  exact unary_add' (hq.comp ha) (unary_add' (unary_add' (computableInPolyTime_portOfNum
    (hσ.comp ha) (const _) (hi.comp ha) hi' (unary_div.comp (hc.prod (hb.comp ha)))) (const _))
    (unary_mul' (const _) hi'))

/-- The cells of a window leaving an interval are polynomial-time. -/
theorem computableInPolyTime_outCellsNum (h : ℕ) {i : α → ℕ}
    (hb : ComputableInPolyTime b inp encUnary) (hq : ComputableInPolyTime q inp encUnary)
    (hL : ComputableInPolyTime (fun p : α × ℕ => L p.1 p.2) (encPair inp encUnary) encNat)
    (hi : ComputableInPolyTime i inp encUnary) :
    ComputableInPolyTime (fun a => outCellsNum k (q a) s (b a) (L a) (i a) h) inp
      (encList (encOption encBool)) := by
  unfold outCellsNum
  have ha : ComputableInPolyTime (fun p : α × ℕ => p.1) (encPair inp encUnary) inp := fst _ _
  have hc : ComputableInPolyTime (fun p : α × ℕ => p.2) (encPair inp encUnary) encUnary :=
    snd _ _
  refine mapWithInput (range.comp (unary_mul' (const 3) hb))
    (computableInPolyTime_contentsCellNum (hb.comp ha) (letter_comp hL ha ?_)
      (unary_mod.comp (hc.prod (hb.comp ha))))
  exact unary_add' (hq.comp ha) (unary_add' (unary_add' (unary_div.comp (hc.prod (hb.comp ha)))
    (const _)) (unary_mul' (const _) (hi.comp ha)))

/-- The interval record decoded from the adjacent letter numbers. -/
private def intervalDataNum (b : ℕ) (input : List Bool) (q σ : ℕ) (L : ℕ → ℕ) (i : ℕ) :
    IntervalData k State :=
  ⟨input, b, blockIndexNum k σ i, blockMoveNum k σ i,
    inControlNum e b machine.initial L i, fun h => inCellsNum k q s b σ L i h,
    decodeControlData e b (L i), fun h => outCellsNum k q s b L i h⟩

omit [DecidableEq State] in
private theorem intervalDataNum_polyTime {i : α → ℕ}
    (hx : ComputableInPolyTime x inp encBits) (hb : ComputableInPolyTime b inp encUnary)
    (hb0 : ∀ a, 0 < b a) (hq : ComputableInPolyTime q inp encUnary)
    (hσ : ComputableInPolyTime σ inp encNat)
    (hL : ComputableInPolyTime (fun p : α × ℕ => L p.1 p.2) (encPair inp encUnary) encNat)
    (hi : ComputableInPolyTime i inp encUnary) :
    ComputableInPolyTime
      (fun a => intervalDataNum e machine (b a) (x a) (q a) (σ a) (L a) (i a))
      inp encIntervalData := by
  have hcIn : ComputableInPolyTime
      (fun a => (inControlNum e (b a) machine.initial (L a) (i a) : ControlData k State)) inp
      encControlData := by
    unfold inControlNum
    exact ite_decide (decide_eq' hi (const 0)) (const _)
      (computableInPolyTime_controlDataOfNum e hb hb0
        (letter_comp hL id' (unary_sub' hi (const 1))))
  exact IntervalData.computableInPolyTime_mk hx hb
    (computableInPolyTime_blockIndexNum hσ hi) (computableInPolyTime_blockMoveNum hσ hi) hcIn
    (pi fun h : Fin k => computableInPolyTime_inCellsNum (k := k) (s := s) h.val hb hq hσ hL hi)
    (computableInPolyTime_decodeControlData e hb hb0 (letter_comp hL id' hi))
    (pi fun h : Fin k => computableInPolyTime_outCellsNum (k := k) (s := s) h.val hb hq hL hi)

private def intervalTypedNum (b q : ℕ) (L : ℕ → ℕ) (i : ℕ) : Bool :=
  decide (L i < controlCount k s b ∧ ∀ h : Fin k, ∀ δ : Fin 3,
    ¬ L (q + (δ + 3 * h + k * 3 * i)) < controlCount k s b)

private theorem intervalTypedNum_polyTime {i : α → ℕ}
    (hb : ComputableInPolyTime b inp encUnary) (hq : ComputableInPolyTime q inp encUnary)
    (hL : ComputableInPolyTime (fun p : α × ℕ => L p.1 p.2) (encPair inp encUnary) encNat)
    (hi : ComputableInPolyTime i inp encUnary) :
    ComputableInPolyTime (fun a => intervalTypedNum (k := k) (s := s) (b a) (q a) (L a) (i a))
      inp encBool := by
  have hC := controlCount' (k := k) (s := s) hb
  have hLat : ∀ {n : α → ℕ}, ComputableInPolyTime n inp encUnary →
      ComputableInPolyTime (fun a => L a (n a)) inp encNat := fun hn => letter_comp hL id' hn
  have hcond : ∀ a, intervalTypedNum (k := k) (s := s) (b a) (q a) (L a) (i a) =
      (decide (L a (i a) < controlCount k s (b a)) && (List.finRange k).all fun h =>
        (List.finRange 3).all fun δ =>
          !decide (L a (q a + (δ + 3 * h + k * 3 * i a)) < controlCount k s (b a))) := by
    intro a
    rw [Bool.eq_iff_iff]
    simp [intervalTypedNum, List.all_eq_true]
  have hc := bool_and' (binary_lt' (hLat hi) hC) (allConst (List.finRange k) fun h _ =>
    allConst (List.finRange 3) fun δ _ => bool_not.comp
      (binary_lt' (hLat (unary_add' hq (unary_add' (const (δ.val + 3 * h.val))
        (unary_mul' (const (k * 3)) hi)))) hC))
  exact hc.of_enc_eq fun a => congrArg encBool (hcond a)

/-- **The tensor of an interval on numbers is polynomial-time**, from the letter numbers of the
edges, when `2 ^ b` is bounded by a computed unary number. -/
theorem computableInPolyTime_intervalEntryNum {i : α → ℕ}
    (hx : ComputableInPolyTime x inp encBits) (hb : ComputableInPolyTime b inp encUnary)
    (hb0 : ∀ a, 0 < b a) (hq : ComputableInPolyTime q inp encUnary)
    (hσ : ComputableInPolyTime σ inp encNat) (hcap : ComputableInPolyTime cap inp encUnary)
    (h2b : ∀ a, 2 ^ b a ≤ cap a)
    (hL : ComputableInPolyTime (fun p : α × ℕ => L p.1 p.2) (encPair inp encUnary) encNat)
    (hi : ComputableInPolyTime i inp encUnary) :
    ComputableInPolyTime (fun a => intervalEntryNum e (b a) machine (x a) (q a) (σ a) (L a) (i a))
      inp encUnary := by
  obtain ⟨size, hsize, hbudget⟩ := budget_of_cap hcap h2b
  have hd := intervalDataNum_polyTime e machine hx hb hb0 hq hσ hL hi
  have hcount := computableInPolyTime_localIntervalCount machine hd hsize hbudget
  have h := ite (intervalTypedNum_polyTime (k := k) (s := s) hb hq hL hi) hcount (const 0)
  exact h.of_enc_eq fun a => by
    simp only [intervalTypedNum, decide_eq_true_eq, intervalDataNum, IntervalData.count,
      intervalEntryNum]


end Interval

/-! ### Reading letters and the tables -/

/-- **Letter numbers read from table indices are polynomial-time.** -/
theorem computableInPolyTime_readNum {m j base : α → ℕ} {P : α → List ℕ}
    (hm : ComputableInPolyTime m inp encUnary) (hP : ComputableInPolyTime P inp (encList encNat))
    (hj : ComputableInPolyTime j inp encNat) (hbase : ComputableInPolyTime base inp encUnary) :
    ComputableInPolyTime (fun a => readNum (m a) (P a) (j a) (base a)) inp encNat := by
  have hlist : ComputableInPolyTime
      (fun a => (List.range (m a)).map fun r => (j a).testBit ((P a).idxOf (base a + r))) inp
      (encList encBool) :=
    mapWithInput (range.comp hm) (binary_testBit (hj.comp (fst _ _))
      (idxOfWithInput (hP.comp (fst _ _))
        (unary_to_binary.comp (unary_add' (hbase.comp (fst _ _)) (snd _ _)))))
  have hbits := (bits_encList_polyTime encBool).2.comp hlist
  have hnum := (ComputableInPolyTime.bitsToNat).comp hbits
  simpa only [readNum, ← ofBits_eq_lsbValue, Function.comp_def] using hnum

private theorem blockSrcNum' {q n : α → ℕ} (hq : ComputableInPolyTime q inp encUnary)
    (hn : ComputableInPolyTime n inp encUnary) :
    ComputableInPolyTime (fun a => blockSrcNum k (q a) (n a)) inp encUnary := by
  unfold blockSrcNum
  exact ite_decide (unary_lt' hn hq) hn (unary_div.comp ((unary_sub' hn hq).prod (const _)))

/-- The letter numbers read at an old vertex are polynomial-time, at a computed edge number. -/
theorem computableInPolyTime_lettersAt {q m v j : α → ℕ} {P : α → List ℕ}
    (hq : ComputableInPolyTime q inp encUnary) (hm : ComputableInPolyTime m inp encUnary)
    (hP : ComputableInPolyTime P inp (encList encNat)) (hj : ComputableInPolyTime j inp encNat)
    (hv : ComputableInPolyTime v inp encUnary) :
    ComputableInPolyTime (fun p : α × ℕ => lettersAt k (q p.1) (m p.1) (P p.1) (j p.1) (v p.1) p.2)
      (encPair inp encUnary) encNat := by
  have ha : ComputableInPolyTime (fun p : α × ℕ => p.1) (encPair inp encUnary) inp := fst _ _
  have hn : ComputableInPolyTime (fun p : α × ℕ => p.2) (encPair inp encUnary) encUnary :=
    snd _ _
  unfold lettersAt halfBase
  refine computableInPolyTime_readNum (hm.comp ha) (hP.comp ha) (hj.comp ha)
    (ite_decide (decide_eq' (blockSrcNum' (hq.comp ha) hn) (hv.comp ha))
      (unary_mul' (hm.comp ha) hn) ?_)
  exact unary_add' (unary_mul' (unary_mul' (hq.comp ha) (const _)) (hm.comp ha))
    (unary_mul' (hm.comp ha) hn)

private theorem validNum_polyTime {b q σ v j : α → ℕ} {P : α → List ℕ}
    (hb : ComputableInPolyTime b inp encUnary) (hq : ComputableInPolyTime q inp encUnary)
    (hσ : ComputableInPolyTime σ inp encNat) (hv : ComputableInPolyTime v inp encUnary)
    (hP : ComputableInPolyTime P inp (encList encNat)) (hj : ComputableInPolyTime j inp encNat) :
    ComputableInPolyTime (fun a => validNum k (q a) s (b a) (σ a) (P a) (j a) (v a))
      inp encBool := by
  have hm : ComputableInPolyTime (fun a => letterBits k s (b a)) inp encUnary :=
    unary_mul' (const _) hb
  have hL := computableInPolyTime_lettersAt (k := k) hq hm hP hj hv
  have hE : ComputableInPolyTime (fun a => q a * (3 * k + 1)) inp encUnary :=
    unary_mul' hq (const _)
  unfold validNum
  have ha : ComputableInPolyTime (fun p : α × ℕ => p.1) (encPair inp encUnary) inp := fst _ _
  have hn : ComputableInPolyTime (fun p : α × ℕ => p.2) (encPair inp encUnary) encUnary :=
    snd _ _
  refine allWithInput (range.comp hE) (bool_or.comp ((bool_not.comp ?_).prod ?_))
  · exact decide_or (decide_eq' (blockSrcNum' (hq.comp ha) hn) (hv.comp ha))
      (decide_eq' (computableInPolyTime_edgeTargetNum (hq.comp ha) (hσ.comp ha) hn) (hv.comp ha))
  · exact binary_lt' hL ((letterCount' hb).comp ha)

section Tables

variable [DecidableEq State] (e : State ≃ Fin s) (machine : MultiTapePTM k Bool State)
  {x : α → List Bool} {b q σ cap : α → ℕ}

/-- A local table-entry program either requests one interval count or returns a Boolean
constant. This program contains no table and does not enumerate coin strings. -/
def tableEntryPlan (b : ℕ) (input : List Bool) (q σ v : ℕ) (P : List ℕ) (j : ℕ) :
    IntervalData k State ⊕ Bool :=
  if v < q * (3 * k + 2) then
    if validNum k q s b σ P j v then
      let L := lettersAt k q (letterBits k s b) P j v
      if v < q then
        if intervalTypedNum (k := k) (s := s) b q L v then
          .inl (intervalDataNum e machine b input q σ L v)
        else .inr false
      else .inr (if v - q + 1 = q then decide (acceptNum k s b (L (v - q)) = 1) else true)
    else .inr false
  else .inr (decide (j.testBit (P.idxOf (v - q * (3 * k + 2))) =
    j.testBit (P.idxOf (q * (3 * k + 1) * letterBits k s b + (v - q * (3 * k + 2))))))

omit [Finite State] [DecidableEq State] in
/-- The compiler reads the source only to attach it to the selected interval. Every branch
decision and every other interval field is independent of the source word. -/
theorem tableEntryPlan_input (b : ℕ) (input input' : List Bool) (q σ v : ℕ)
    (P : List ℕ) (j : ℕ) :
    tableEntryPlan e machine b input q σ v P j =
      (tableEntryPlan e machine b input' q σ v P j).map
        (fun d => { d with input := input }) id := by
  simp only [tableEntryPlan]
  split_ifs <;> rfl

/-- The left tag contains the existing framed interval record; the right tag a single Boolean. -/
noncomputable abbrev encTableEntryPlan : (IntervalData k State ⊕ Bool) ↪ List Bool :=
  encSum encIntervalData encBool

omit [Finite State] in
/-- The compiler's selected interval has the original width and count; its constant branch is
exactly the table value. The assignment index is the existing binary bit assignment to ports. -/
theorem tableEntryPlan_spec (b : ℕ) (input : List Bool) (q σ v : ℕ) (P : List ℕ) (j : ℕ) :
    match tableEntryPlan e machine b input q σ v P j with
    | .inl d => d.b = b ∧ d.count machine = tableEntryNum e b machine input q σ v P j
    | .inr value => value.toNat = tableEntryNum e b machine input q σ v P j := by
  simp only [tableEntryPlan, tableEntryNum, oldEntryNum, intervalEntryNum, intervalTypedNum,
    decide_eq_true_eq]
  split_ifs <;> simp_all [intervalDataNum, IntervalData.count, acceptNum]
  split_ifs <;> simp_all

omit [DecidableEq State] in
/-- Compile a single table entry from binary assignments, unary width, interval and vertex
counts, and a binary schedule. Unlike full table construction, no `2 ^ b` budget is needed. -/
theorem computableInPolyTime_tableEntryPlan {v j : α → ℕ} {P : α → List ℕ}
    (hx : ComputableInPolyTime x inp encBits) (hb : ComputableInPolyTime b inp encUnary)
    (hb0 : ∀ a, 0 < b a) (hq : ComputableInPolyTime q inp encUnary)
    (hσ : ComputableInPolyTime σ inp encNat) (hv : ComputableInPolyTime v inp encUnary)
    (hP : ComputableInPolyTime P inp (encList encNat)) (hj : ComputableInPolyTime j inp encNat) :
    ComputableInPolyTime
      (fun a => tableEntryPlan e machine (b a) (x a) (q a) (σ a) (v a) (P a) (j a))
      inp encTableEntryPlan := by
  have hm : ComputableInPolyTime (fun a => letterBits k s (b a)) inp encUnary :=
    unary_mul' (const _) hb
  have hL := computableInPolyTime_lettersAt (k := k) hq hm hP hj hv
  have hR : ComputableInPolyTime (fun a => q a * (3 * k + 2)) inp encUnary :=
    unary_mul' hq (const _)
  have hE : ComputableInPolyTime (fun a => q a * (3 * k + 1)) inp encUnary :=
    unary_mul' hq (const _)
  have hC := controlCount' (k := k) (s := s) hb
  have hD : ComputableInPolyTime (fun a => b a ^ (k + 1) * 3) inp encNat :=
    binary_mul' (binary_pow' (unary_to_binary.comp hb) (const _)) (const 3)
  have hconst : ∀ {f : α → Bool}, ComputableInPolyTime f inp encBool →
      ComputableInPolyTime (fun a => (Sum.inr (f a) : IntervalData k State ⊕ Bool))
        inp encTableEntryPlan := fun hf => (sumInr encIntervalData encBool).comp hf
  have hn := letter_comp
    (L := fun a => lettersAt k (q a) (letterBits k s (b a)) (P a) (j a) (v a))
    hL id' (unary_sub' hv hq)
  have hsink := decide_and (binary_lt' hn hC) (decide_eq' (binary_mod.comp
    ((binary_mod.comp (hn.prod hD)).prod (const 3))) (const 1))
  have hsink' : ComputableInPolyTime
      (fun a => decide (acceptNum k s (b a)
        (lettersAt k (q a) (letterBits k s (b a)) (P a) (j a) (v a) (v a - q a)) = 1))
      inp encBool := hsink.of_enc_eq fun a => by simp [acceptNum]
  have hc : ComputableInPolyTime (fun a => v a - q a * (3 * k + 2)) inp encUnary :=
    unary_sub' hv hR
  unfold tableEntryPlan
  refine ite_decide (unary_lt' hv hR)
    (ite (validNum_polyTime (k := k) (s := s) hb hq hσ hv hP hj) ?_ (hconst (const false)))
    (hconst (decide_eq' (binary_testBit hj (idxOfWithInput hP (unary_to_binary.comp hc)))
      (binary_testBit hj (idxOfWithInput hP (unary_to_binary.comp
        (unary_add' (unary_mul' hE hm) hc))))))
  refine ite_decide (unary_lt' hv hq)
    (ite (intervalTypedNum_polyTime (k := k) (s := s) hb hq hL hv)
      ((sumInl encIntervalData encBool).comp
        (intervalDataNum_polyTime e machine hx hb hb0 hq hσ hL hv))
      (hconst (const false)))
    (hconst (ite_decide (decide_eq' (unary_add' (unary_sub' hv hq) (const 1)) hq)
      hsink' (const true)))

/-- **Table entries on numbers are polynomial-time.** -/
theorem computableInPolyTime_tableEntryNum {v j : α → ℕ} {P : α → List ℕ}
    (hx : ComputableInPolyTime x inp encBits) (hb : ComputableInPolyTime b inp encUnary)
    (hb0 : ∀ a, 0 < b a) (hq : ComputableInPolyTime q inp encUnary)
    (hσ : ComputableInPolyTime σ inp encNat) (hcap : ComputableInPolyTime cap inp encUnary)
    (h2b : ∀ a, 2 ^ b a ≤ cap a) (hv : ComputableInPolyTime v inp encUnary)
    (hP : ComputableInPolyTime P inp (encList encNat)) (hj : ComputableInPolyTime j inp encNat) :
    ComputableInPolyTime
      (fun a => tableEntryNum e (b a) machine (x a) (q a) (σ a) (v a) (P a) (j a)) inp encNat := by
  have hm : ComputableInPolyTime (fun a => letterBits k s (b a)) inp encUnary :=
    unary_mul' (const _) hb
  have hL := computableInPolyTime_lettersAt (k := k) hq hm hP hj hv
  have hp := computableInPolyTime_tableEntryPlan e machine hx hb hb0 hq hσ hv hP hj
  have hl := (ComputableInO.getLeft?_deg encIntervalData encBool).computableInPolyTime.comp hp
  have hd := optionGetDWithInput hl
    (intervalDataNum_polyTime (L := fun a =>
      lettersAt k (q a) (letterBits k s (b a)) (P a) (j a) (v a))
      e machine hx hb hb0 hq hσ hL hv)
  have hr := optionGetDWithInput
    ((ComputableInO.getRight?_deg encIntervalData encBool).computableInPolyTime.comp hp)
    (const false)
  obtain ⟨size, hsize, hbudget⟩ := budget_of_cap hcap h2b
  have hw a : ((tableEntryPlan e machine (b a) (x a) (q a) (σ a) (v a) (P a) (j a)).getLeft?.getD
      (intervalDataNum e machine (b a) (x a) (q a) (σ a)
        (lettersAt k (q a) (letterBits k s (b a)) (P a) (j a) (v a)) (v a))).b = b a := by
    have hs := tableEntryPlan_spec e machine (b a) (x a) (q a) (σ a) (v a) (P a) (j a)
    cases hplan : tableEntryPlan e machine (b a) (x a) (q a) (σ a) (v a) (P a) (j a) with
    | inl d =>
      simp only [hplan] at hs
      exact hs.1
    | inr value => rfl
  have hcount := computableInPolyTime_localIntervalCount machine hd hsize
    (fun a => by simpa only [Function.comp_def, hw] using hbudget a)
  have h := ite ((ComputableInO.isLeft_deg encIntervalData encBool).computableInPolyTime.comp hp)
    (unary_to_binary.comp hcount)
    ((of_finite (encIn := encBool) (encOut := encNat) Bool.toNat).comp hr)
  exact h.of_enc_eq fun a => by
    have hs := tableEntryPlan_spec e machine (b a) (x a) (q a) (σ a) (v a) (P a) (j a)
    cases hplan : tableEntryPlan e machine (b a) (x a) (q a) (σ a) (v a) (P a) (j a) with
    | inl d =>
      simp only [hplan] at hs
      simpa only [Function.comp_def, hplan, Sum.isLeft_inl, Sum.getLeft?_inl,
        Option.getD_some, ↓reduceIte] using congrArg encNat hs.2.symm
    | inr value =>
      simp only [hplan] at hs
      simpa only [Function.comp_def, hplan, Sum.isLeft_inr, Sum.getRight?_inr,
        Option.getD_some, Bool.false_eq_true, ↓reduceIte] using congrArg encNat hs.symm

/-- **Tables on numbers are polynomial-time.** -/
theorem computableInPolyTime_explicitTableNum {v : α → ℕ}
    (hx : ComputableInPolyTime x inp encBits) (hb : ComputableInPolyTime b inp encUnary)
    (hb0 : ∀ a, 0 < b a) (hq : ComputableInPolyTime q inp encUnary)
    (hσ : ComputableInPolyTime σ inp encNat) (hcap : ComputableInPolyTime cap inp encUnary)
    (h2b : ∀ a, 2 ^ b a ≤ cap a) (hv : ComputableInPolyTime v inp encUnary) :
    ComputableInPolyTime (fun a => explicitTableNum e (b a) machine (x a) (q a) (σ a) (v a)) inp
      (encList encNat) := by
  have hm : ComputableInPolyTime (fun a => letterBits k s (b a)) inp encUnary := by
    unfold letterBits
    exact unary_mul' (const _) hb
  have hP := computableInPolyTime_explicitPortsNum (k := k) hq hm hσ hv
  have hlen : ComputableInPolyTime
      (fun a => 2 ^ (explicitPortsNum k (q a) (letterBits k s (b a)) (σ a) (v a)).length) inp
      encUnary := by
    refine binary_to_unary_bounded (binary_two_pow.comp ((length_list encNat).comp hP))
      ((unary_pow (2 * (3 * k + 1) * (s + k + 4))).comp hcap) fun a => ?_
    have : NeZero (b a) := ⟨(hb0 a).ne'⟩
    have hdeg := length_explicitPortsNum_le (q := q a) machine (b a) e (σ a) (v a)
    calc 2 ^ (explicitPortsNum k (q a) (letterBits k s (b a)) (σ a) (v a)).length
        ≤ 2 ^ (b a * (2 * (3 * k + 1) * (s + k + 4))) := by
          refine Nat.pow_le_pow_right two_pos (hdeg.trans (le_of_eq ?_))
          unfold letterBits
          ring
      _ = (2 ^ b a) ^ (2 * (3 * k + 1) * (s + k + 4)) := pow_mul _ _ _
      _ ≤ cap a ^ (2 * (3 * k + 1) * (s + k + 4)) := Nat.pow_le_pow_left (h2b a) _
  unfold explicitTableNum
  have ha : ComputableInPolyTime (fun p : α × ℕ => p.1) (encPair inp encUnary) inp := fst _ _
  exact mapWithInput (range.comp hlen) (computableInPolyTime_tableEntryNum e machine
    (hx.comp ha) (hb.comp ha) (fun p => hb0 p.1) (hq.comp ha) (hσ.comp ha) (hcap.comp ha)
    (fun p => h2b p.1) (hv.comp ha) (hP.comp ha) (unary_to_binary.comp (snd _ _)))

/-- **A single table entry compiles to one interval record or a Boolean constant
(`Turing.MultiTapePTM.tableEntryPlan`). The compiler computes and validates the letter codes at
the selected vertex from its binary local assignment, without listing coin strings or table
entries. `tableEntryPlan_spec` identifies the result with the existing numeric tensor entry.
The native alternating entry evaluator consumes this program directly.

The explicit block-counting network on numbers is polynomial-time**, as its number of edges
in unary and its list of vertices, each the pair of its ports and its table as lists of binary
numbers. -/
theorem computableInPolyTime_explicitNetworkNum
    (hx : ComputableInPolyTime x inp encBits) (hb : ComputableInPolyTime b inp encUnary)
    (hb0 : ∀ a, 0 < b a) (hq : ComputableInPolyTime q inp encUnary)
    (hσ : ComputableInPolyTime σ inp encNat) (hcap : ComputableInPolyTime cap inp encUnary)
    (h2b : ∀ a, 2 ^ b a ≤ cap a) :
    ComputableInPolyTime (fun a => ((explicitNetworkNum e (b a) machine (x a) (q a) (σ a)).numEdges,
        (explicitNetworkNum e (b a) machine (x a) (q a) (σ a)).vertices)) inp
      (encPair encUnary (encList (encPair (encList encNat) (encList encNat)))) := by
  have hm : ComputableInPolyTime (fun a => letterBits k s (b a)) inp encUnary := by
    unfold letterBits
    exact unary_mul' (const _) hb
  have ha : ComputableInPolyTime (fun p : α × ℕ => p.1) (encPair inp encUnary) inp := fst _ _
  refine (unary_mul' (const 2) (unary_mul' (unary_mul' hq (const _)) hm)).prod ?_
  unfold explicitNetworkNum explicitVerticesNum
  refine mapWithInput (range.comp (unary_add' (unary_mul' hq (const _))
    (unary_mul' (unary_mul' hq (const _)) hm))) ((computableInPolyTime_explicitPortsNum
      (hq.comp ha) (hm.comp ha) (hσ.comp ha) (snd _ _)).prod ?_)
  exact computableInPolyTime_explicitTableNum e machine (hx.comp ha) (hb.comp ha) (fun p => hb0 p.1)
    (hq.comp ha) (hσ.comp ha) (hcap.comp ha) (fun p => h2b p.1) (snd _ _)

end Tables

end Turing.MultiTapePTM
