/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.BinaryField
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatSize
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinarySizeFacts
import CslibFrontier.Foundations.Data.Nat.BinarySize
import Mathlib.Data.Nat.Size

/-!
# Native binary-polynomial trial components

`divisorPasses_inSpace` certifies the exact trial predicate used by `isIrreducibleCode` and
its counter scan, on binary candidate/divisor codes. The native remainder call retains the two
codes and charges conversion of their coefficient words, the two remainder registers and its
scalar callees. Both live binary lengths are computed from binary encodings, without expanding
a code to unary or allocating a divisor table.

The counted trial run is uniform in its initial divisor and binary iteration count. Its native
workspace includes the retained candidate, moving divisor and Boolean accumulator at every
prefix. This is an original resource analysis of the existing trial predicate. Its complete counter
traversal returns exactly `isIrreducibleCode`; the private early-exit scan has that same value
by its existing agreement theorem. This does not identify their step traces or certify modulus
selection, Horner or seed composition, which remain open under #6747.

## Main results

* `Turing.BinaryField.divisorPasses_inSpace`: native linear space for one uniform divisor test.
* `Turing.BinaryField.trialRun_inSpace`: native binary-counted iteration of the exact predicate.
* `Turing.BinaryField.trialRun_good_iff`: exact predicate agreement at every iteration prefix.
* `Turing.BinaryField.isIrreducibleCode_inSpace`: native binary-input trial-division test.
-/

public section
namespace Turing.BinaryField

open MultiTapeTM MultiTapeTM.ComputableInSpace Cslib

/-- Candidate and divisor codes for a binary-polynomial trial. -/
structure DivisorInput where
  /-- Binary code of the polynomial whose divisors are tested. -/
  candidate : ℕ
  /-- Binary code of the possible divisor. -/
  divisor : ℕ

/-- Binary candidate, framed, followed by binary divisor. -/
enc_structure encDivisorInput : DivisorInput where candidate : encNat, divisor : encNat

private theorem binaryLog_inSpace :
    ComputableInSpace (Nat.log 2) encNat encNat (fun n => (encNat n).length) := by
  refine (budget_natPred natSize).of_enc_eq fun n => congrArg encNat ?_
  simp only [← Nat.log2_eq_log_two, Nat.log2_eq_size_sub_one]

private theorem coefficientBits_inSpace :
    ComputableInSpace Nat.bits encNat encCoefficients (fun n => (encNat n).length) := by
  have hbits : ComputableInSpace Nat.bits encNat encBits (fun n => (encNat n).length) :=
    of_inO (ComputableInO.of_eq fun _ => rfl)
  exact budget_comp_linear (g := fun w : List Bool => w)
    (of_inO ComputableInDegree.bitsToList.inO_one) hbits

private theorem any_inSpace :
    ComputableInSpace (fun w : List Bool => w.any id) encCoefficients encBool
      (fun w => (encCoefficients w).length) := by
  obtain ⟨t, c, h⟩ := ComputableInLogSpace.bitsAny id
  have hraw : ComputableInSpace (fun w : List Bool => w.any id) encBits encBool
      (fun w => (encBits w).length) := by
    refine ⟨t, c + 1, h.mono (fun _ => le_rfl) (fun w => ?_), fun w => ?_⟩
    · have := Nat.log2_le_self w.length
      simp only [encBits_apply]
      nlinarith
    · simp only [encBool_apply, List.length_singleton]
      nlinarith
  exact budget_comp_linear hraw (of_inO ComputableInDegree.listToBits.inO_one)

/-- The exact original divisor-pass predicate, in native work space linear in the two binary
codes. Live lengths, decoded coefficient words and the complete remainder callee are charged. -/
theorem divisorPasses_inSpace :
    ComputableInSpace (fun p : DivisorInput => divisorPasses p.candidate p.divisor)
      encDivisorInput encBool (fun p => (encDivisorInput p).length) := by
  have hid : ComputableInSpace (fun p : DivisorInput => p) encDivisorInput encDivisorInput
      (fun p => (encDivisorInput p).length) := of_inO ComputableInO.id'
  have hm := encDivisorInput_candidate_budget hid
  have hd := encDivisorInput_divisor_budget hid
  have htwo :=
    budget_const (Bs := fun a => (encDivisorInput a).length) (encIn := encDivisorInput)
      (encB := encNat) 2
  have hsmall := budget_natLt hd htwo
  have hdegree := budget_natLt
    (budget_natDiv (budget_comp_linear binaryLog_inSpace hm) htwo)
    (budget_comp_linear binaryLog_inSpace hd)
  have hrem := budget_comp_linear
    (g := fun p : RemainderInput => modBits p.modulus p.dividend) modBits_inSpace
    (encRemainderInput_mk_budget (budget_comp_linear coefficientBits_inSpace hd)
      (budget_comp_linear coefficientBits_inSpace hm))
  have hnz := budget_comp_linear any_inSpace hrem
  have hor := budget_finite (encC := encBool) (fun p : Bool × Bool => p.1 || p.2)
    (budget_prod hsmall hdegree)
  exact (budget_finite (encC := encBool) (fun p : Bool × Bool => p.1 || p.2)
    (budget_prod hor hnz)).of_enc_eq fun _ => rfl

/-- State of a counter trial: retained candidate, next divisor and accumulated pass bit. -/
structure TrialState where
  /-- Binary candidate, unchanged during the trial. -/
  candidate : ℕ
  /-- Next divisor code to test. -/
  divisor : ℕ
  /-- Whether every divisor tested so far passed the original predicate. -/
  good : Bool

/-- The counted native iteration calculus requires an initial inhabitant; runs use their
explicitly supplied state rather than this default. -/
private instance : Inhabited TrialState := ⟨⟨0, 0, true⟩⟩

/-- Binary candidate and divisor, each framed, followed by the accumulator bit. -/
enc_structure encTrialState : TrialState where
  candidate : encNat, divisor : encNat, good : encBool

/-- Test one divisor with the original predicate and increment the binary cursor. -/
@[expose] def trialStep (s : TrialState) : TrialState :=
  ⟨s.candidate, s.divisor + 1, s.good && divisorPasses s.candidate s.divisor⟩

/-- Native step space includes the retained candidate and the entire divisor-test callee. -/
theorem trialStep_inSpace :
    ComputableInSpace trialStep encTrialState encTrialState
      (fun s => (encTrialState s).length) := by
  have hid : ComputableInSpace (fun s : TrialState => s) encTrialState encTrialState
      (fun s => (encTrialState s).length) := of_inO ComputableInO.id'
  have hm := encTrialState_candidate_budget hid
  have hd := encTrialState_divisor_budget hid
  have hg := encTrialState_good_budget hid
  have hp := budget_comp_linear divisorPasses_inSpace (encDivisorInput_mk_budget hm hd)
  exact encTrialState_mk_budget hm (budget_natSucc hd)
    (budget_finite (encC := encBool) (fun p : Bool × Bool => p.1 && p.2) (budget_prod hg hp))

/-- Binary candidate, starting divisor and iteration count; no list of trials is stored. -/
structure TrialInput where
  /-- Candidate code. -/
  candidate : ℕ
  /-- First divisor code. -/
  first : ℕ
  /-- Number of consecutive divisor codes to test. -/
  count : ℕ

/-- Three binary naturals in field order, the first two framed. -/
enc_structure encTrialInput : TrialInput where candidate : encNat, first : encNat, count : encNat

/-- A counted trial run, implemented by repeated native scalar steps rather than `List.range`. -/
@[expose] def trialRun (p : TrialInput) : TrialState :=
  trialStep^[p.count] ⟨p.candidate, p.first, true⟩

private theorem trial_fields (m d k : ℕ) :
    (trialStep^[k] ⟨m, d, true⟩).candidate = m ∧
      (trialStep^[k] ⟨m, d, true⟩).divisor = d + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨ih.1, by simp only [trialStep, ih.2]; omega⟩

/-- Every tested divisor contributes the exact original predicate, including out-of-range and
zero codes; there are no monicity or candidate-size preconditions on this iteration contract. -/
theorem trialRun_good_iff (p : TrialInput) :
    (trialRun p).good = true ↔ ∀ i < p.count, divisorPasses p.candidate (p.first + i) = true := by
  rcases p with ⟨m, d, k⟩
  change (trialStep^[k] ⟨m, d, true⟩).good = true ↔
    ∀ i < k, divisorPasses m (d + i) = true
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    simp only [trialStep, (trial_fields m d k).1, (trial_fields m d k).2, Bool.and_eq_true, ih,
      ← Nat.forall_lt_succ_right]

/-- Uniform native counted trial space, linear in the binary candidate/start/count words.
The cursor is at most first + count at every prefix; the step certificate includes binary
length processing and polynomial-remainder workspace. Running time is left existential. -/
theorem trialRun_inSpace :
    ComputableInSpace trialRun encTrialInput encTrialState
      (fun p => (encTrialInput p).length) := by
  have hid : ComputableInSpace (fun p : TrialInput => p) encTrialInput encTrialInput
      (fun p => (encTrialInput p).length) := of_inO ComputableInO.id'
  have hm := encTrialInput_candidate_budget hid
  have hd := encTrialInput_first_budget hid
  have hk := encTrialInput_count_budget hid
  have hi := encTrialState_mk_budget hm hd (budget_const (encB := encBool) true)
  apply budget_iterate hk hi trialStep_inSpace
    (B := fun p => 16 * ((encTrialInput p).length + 1))
  · intro p k hkp
    have h := trial_fields p.candidate p.first k
    have hcursor := length_encNat_mono (show p.first + k ≤ p.first + p.count by omega)
    have hadd := length_encNat_add_le_add p.first p.count
    simp only [encTrialState_apply, encTrialStateFields, encTrialInput_apply,
      encTrialInputFields, length_encPair, encBool_apply, List.length_singleton, h.1, h.2] at *
    omega
  · exact .of_le_linear 16 16 fun _ => le_rfl

/-- Starting at code zero and testing exactly candidate-many codes gives the original
irreducibility predicate after its lower-bound test. The list appears only in the specification
of `isIrreducibleCode`, not in `trialRun` or its native implementation. -/
theorem trialRun_isIrreducibleCode (m : ℕ) :
    (decide (2 ≤ m) && (trialRun ⟨m, 0, m⟩).good) = isIrreducibleCode m := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, trialRun_good_iff, isIrreducibleCode,
    List.all_eq_true, List.mem_range, Nat.zero_add]

/-- The existing total irreducibility test on a binary code has a native linear-workspace
implementation by counted trial division. Both live binary lengths and every remainder call
are included; no unary candidate, divisor list or multiplication table is materialized. -/
theorem isIrreducibleCode_inSpace :
    ComputableInSpace isIrreducibleCode encNat encBool (fun m => (encNat m).length) := by
  have hid : ComputableInSpace (fun m : ℕ => m) encNat encNat
      (fun m => (encNat m).length) := of_inO ComputableInO.id'
  have hinit := encTrialInput_mk_budget hid
    (budget_const (encB := encNat) 0) hid
  have hrun := budget_comp_linear trialRun_inSpace hinit
  have hgood := encTrialState_good_budget hrun
  have hlower := budget_finite (encC := encBool) not
    (budget_natLt hid (budget_const (encB := encNat) 2))
  refine (budget_finite (encC := encBool) (fun p : Bool × Bool => p.1 && p.2)
    (budget_prod hlower hgood)).of_enc_eq fun m => ?_
  rw [← trialRun_isIrreducibleCode]
  congr 1
  by_cases h : m < 2 <;> simp [h, show (2 ≤ m) ↔ ¬m < 2 by omega]

end Turing.BinaryField
