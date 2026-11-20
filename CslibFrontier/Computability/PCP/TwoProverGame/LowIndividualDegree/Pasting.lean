/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.MvPolynomial.InterpolateLast
public import CslibFrontier.Foundations.Quantum.Algebra.MeasurementMixture
public import CslibFrontier.Foundations.Quantum.Algebra.SequentialMeasurement
public import CslibFrontier.Probability.PMF.Uniform
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi

/-!
# Polynomial outcomes in the low individual degree pasting step

The readout in [Ji, Natarajan, Vidick, Wright and Yuen, Definition 12.8]
[JNVWY2020LowIndividualDegree] accepts a tuple of slice outcomes when at least `d + 1` slices
succeeded and their polynomials are restrictions of a common polynomial of individual degree
at most `d`. Distinct slices make that common polynomial unique. Applying the readout to
a joint measurement of the slice outcomes groups precisely the contributing transcripts,
with all remaining outcomes assigned to failure.

## Main definitions

* `Cslib.PCP.LowIndividualDegree.BoundedPolynomial`: polynomials of individual degree at most
  a given bound.
* `Cslib.PCP.LowIndividualDegree.pasteOutcome`: the partial polynomial readout.
* `Cslib.PCP.LowIndividualDegree.pasteMeasurement`: the measurement after readout.
* `Cslib.PCP.LowIndividualDegree.pasteSlices`: the readout averaged over distinct slice tuples.

## Main results

* `Cslib.PCP.LowIndividualDegree.pasteOutcome_eq_some_iff`: the successful outcomes are exactly
  the compatible polynomials with enough successful slices.
* `Cslib.PCP.LowIndividualDegree.pasteOutcome_eq_some_of_card`: at exactly `d + 1` successes
  the interpolant always provides such a polynomial.
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Finset MvPolynomial Cslib.Quantum

/-- A polynomial whose degree in every coordinate is at most `d`. -/
abbrev BoundedPolynomial (F : Type*) [CommSemiring F] (m d : ℕ) :=
  {p : MvPolynomial (Fin m) F // ∀ i, p.degreeOf i ≤ d}

variable {F ι : Type*} {m d : ℕ} [Field F]

instance [Finite F] : Finite (BoundedPolynomial F m d) := by
  classical
  let exponents (a : Fin m → Fin (d + 1)) : Fin m →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm (fun i => (a i).val)
  let encode (p : BoundedPolynomial F m d) (a : Fin m → Fin (d + 1)) :=
    p.val.coeff (exponents a)
  refine Finite.of_injective encode fun p q h => Subtype.ext (MvPolynomial.ext _ _ fun e => ?_)
  by_cases he : ∀ i, e i ≤ d
  · let a (i : Fin m) : Fin (d + 1) := ⟨e i, Nat.lt_succ_of_le (he i)⟩
    have ha : exponents a = e := Finsupp.equivFunOnFinite_symm_coe e
    simpa only [encode, ha] using congrFun h a
  · have zeroCoeff (r : BoundedPolynomial F m d) : r.val.coeff e = 0 := by
      rw [← notMem_support_iff]
      exact fun hs => he fun i => (le_degreeOf_of_mem_support i hs).trans (r.prop i)
    rw [zeroCoeff p, zeroCoeff q]

noncomputable instance [Finite F] : Fintype (BoundedPolynomial F m d) :=
  Fintype.ofFinite _

/-- Restrict a bounded polynomial to a last-coordinate slice. -/
@[expose] noncomputable def BoundedPolynomial.specialize (x : F)
    (p : BoundedPolynomial F (m + 1) d) :
    BoundedPolynomial F m d :=
  ⟨specializeLast x p.val,
    fun i => (degreeOf_specializeLast_le x p.val i).trans (p.prop i.castSucc)⟩



/-- The transcript corresponding to a polynomial and a chosen success pattern. -/
noncomputable def sliceTranscript (x : ι → F) (p : BoundedPolynomial F (m + 1) d)
    (success : ι → Bool) (j : ι) : Option (BoundedPolynomial F m d) :=
  if success j then some (p.specialize (x j)) else none

variable [Fintype ι]

/-- The indices whose slice measurement returned a polynomial. -/
def successfulSlices (g : ι → Option (BoundedPolynomial F m d)) : Finset ι :=
  univ.filter fun j => (g j).isSome

@[simp] theorem mem_successfulSlices {g : ι → Option (BoundedPolynomial F m d)} {j : ι} :
    j ∈ successfulSlices g ↔ (g j).isSome := by
  unfold successfulSlices
  simp

/-- Each successful slice outcome is the indicated specialization of the global polynomial. -/
@[expose] def FitsSlices (x : ι → F) (g : ι → Option (BoundedPolynomial F m d))
    (p : BoundedPolynomial F (m + 1) d) : Prop :=
  ∀ j q, g j = some q → p.specialize (x j) = q

omit [Fintype ι] in
theorem fitsSlices_iff_eq_sliceTranscript (x : ι → F)
    (g : ι → Option (BoundedPolynomial F m d)) (p : BoundedPolynomial F (m + 1) d) :
    FitsSlices x g p ↔ g = sliceTranscript x p (fun j => (g j).isSome) := by
  constructor
  · intro h
    funext j
    cases hg : g j with
    | none => simp [hg, sliceTranscript]
    | some q => simp [hg, sliceTranscript, h j q hg]
  · intro h j q hq
    have hj := congrFun h j
    simpa [sliceTranscript, hq, eq_comm] using hj

theorem eq_of_fitsSlices {x : ι ↪ F} {g : ι → Option (BoundedPolynomial F m d)}
    (hcard : d < (successfulSlices g).card) {p q : BoundedPolynomial F (m + 1) d}
    (hp : FitsSlices x g p) (hq : FitsSlices x g q) : p = q := by
  apply Subtype.ext
  refine eq_of_specializeLast_eq x.injective.injOn
    ((p.prop (Fin.last m)).trans_lt hcard) ((q.prop (Fin.last m)).trans_lt hcard) ?_
  intro i hi
  have hi' : (g i).isSome := (mem_filter.mp hi).2
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hi'
  exact congrArg Subtype.val ((hp i r hr).trans (hq i r hr).symm)

/-- Decode a joint outcome to the uniquely matching polynomial when there are enough
successful slices. Discard the outcome when there are too few slices or they are incompatible. -/
noncomputable def pasteOutcome (x : ι ↪ F) (g : ι → Option (BoundedPolynomial F m d)) :
    Option (BoundedPolynomial F (m + 1) d) := by
  classical
  exact if h : d < (successfulSlices g).card ∧ ∃ p, FitsSlices x g p
    then some (Classical.choose h.2) else none

theorem pasteOutcome_eq_some_iff (x : ι ↪ F) (g : ι → Option (BoundedPolynomial F m d))
    (p : BoundedPolynomial F (m + 1) d) :
    pasteOutcome x g = some p ↔ d < (successfulSlices g).card ∧ FitsSlices x g p := by
  classical
  unfold pasteOutcome
  split
  · rename_i h
    have hp := Classical.choose_spec h.2
    constructor
    · intro he
      rw [Option.some.inj he] at hp
      exact ⟨h.1, hp⟩
    · exact fun he => congrArg some (eq_of_fitsSlices h.1 hp he.2)
  · rename_i h
    exact ⟨by simp, fun he => (h ⟨he.1, p, he.2⟩).elim⟩

/-- With exactly `d + 1` successful slice outcomes, interpolation fits all of them. -/
theorem pasteOutcome_eq_some_of_card (x : ι ↪ F) (g : ι → Option (BoundedPolynomial F m d))
    (hcard : (successfulSlices g).card = d + 1) : ∃ p, pasteOutcome x g = some p := by
  classical
  let s := successfulSlices g
  let f (j : ι) : BoundedPolynomial F m d := (g j).getD ⟨0, by simp⟩
  let p := interpolateLast s x fun j => (f j).val
  have hp (i : Fin (m + 1)) : p.degreeOf i ≤ d := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have h := degreeOf_last_interpolateLast_le (s := s) x.injective.injOn fun j => (f j).val
      exact h.trans (by simp [s, hcard])
    · exact degreeOf_castSucc_interpolateLast_le s x _ j fun k _ => (f k).prop j
  refine ⟨⟨p, hp⟩, (pasteOutcome_eq_some_iff _ _ _).mpr ⟨by omega, ?_⟩⟩
  intro j q hj
  have hjs : j ∈ s := by simp [s, successfulSlices, hj]
  apply Subtype.ext
  change specializeLast (x j) p = q.val
  have h := specializeLast_interpolateLast (m := m) x.injective.injOn (fun j => (f j).val) hjs
  simpa only [f, hj, Option.getD_some] using h

section Measurement

variable {A : Type*} [Ring A] [PartialOrder A] [IsOrderedAddMonoid A] [Finite F] [DecidableEq ι]

/-- Coarse-grain the joint slice measurement by the pasting readout. Its `none` effect
collects outcomes with too few successful slices or incompatible slice polynomials. -/
noncomputable def pasteMeasurement (x : ι ↪ F)
    (M : Measurement (ι → Option (BoundedPolynomial F m d)) A) :
    Measurement (Option (BoundedPolynomial F (m + 1) d)) A := by
  classical
  exact M.map (pasteOutcome x)

open scoped Classical in
theorem pasteMeasurement_effect_some (x : ι ↪ F)
    (M : Measurement (ι → Option (BoundedPolynomial F m d)) A)
    (p : BoundedPolynomial F (m + 1) d) :
    (pasteMeasurement x M).effect (some p) = ∑ g with
      d < (successfulSlices g).card ∧ FitsSlices x g p, M.effect g := by
  classical
  unfold pasteMeasurement
  rw [Measurement.map_effect]
  exact sum_congr (filter_congr fun g _ => pasteOutcome_eq_some_iff x g p) fun _ _ => rfl

variable [StarRing A] [StarOrderedRing A]

/-- Perform the completed slice measurements in index order and read out their pasted
polynomial. The outcome `none` is the complementary effect of the pasted sub-measurement. -/
noncomputable def pasteProjectiveSlices {k : ℕ} (x : Fin k ↪ F)
    (M : F → Measurement (Option (BoundedPolynomial F m d)) A)
    (hM : ∀ t, (M t).IsProjective) : Measurement (Option (BoundedPolynomial F (m + 1) d)) A :=
  pasteMeasurement x (Measurement.sequentialProjective (fun j => M (x j)) (fun j => hM (x j)))

open scoped Classical in
/-- A successful pasted effect sums the sequential effects of exactly the compatible
transcripts with at least `d + 1` successful slice outcomes. -/
theorem pasteProjectiveSlices_effect_some {k : ℕ} (x : Fin k ↪ F)
    (M : F → Measurement (Option (BoundedPolynomial F m d)) A)
    (hM : ∀ t, (M t).IsProjective) (p : BoundedPolynomial F (m + 1) d) :
    (pasteProjectiveSlices x M hM).effect (some p) = ∑ g with
      d < (successfulSlices g).card ∧ FitsSlices x g p,
        (Measurement.sequentialProjective (fun j => M (x j)) (fun j => hM (x j))).effect g := by
  unfold pasteProjectiveSlices
  exact pasteMeasurement_effect_some _ _ _

variable [Module ℝ A] [PosSMulMono ℝ A]

/-- The pasted measurement with an explicit failure outcome. Sample an ordered tuple of
distinct slices uniformly, perform their measurements and apply the polynomial readout. -/
noncomputable def pasteSlices (k : ℕ) [Nonempty (Fin k ↪ F)]
    (M : F → Measurement (Option (BoundedPolynomial F m d)) A)
    (hM : ∀ t, (M t).IsProjective) : Measurement (Option (BoundedPolynomial F (m + 1) d)) A := by
  classical
  let _ : Fintype (Fin k ↪ F) := Fintype.ofFinite _
  exact Measurement.mixture (Cslib.Probability.PMF.uniformOfFintype (Fin k ↪ F))
    (fun x => pasteProjectiveSlices x M hM)

theorem pasteSlices_effect (k : ℕ) [Nonempty (Fin k ↪ F)]
    (M : F → Measurement (Option (BoundedPolynomial F m d)) A)
    (hM : ∀ t, (M t).IsProjective) (a : Option (BoundedPolynomial F (m + 1) d)) :
    letI : Fintype (Fin k ↪ F) := Fintype.ofFinite _
    (pasteSlices k M hM).effect a = ∑ x,
      (Cslib.Probability.PMF.uniformOfFintype (Fin k ↪ F) x).toReal •
        (pasteProjectiveSlices x M hM).effect a := by
  unfold pasteSlices
  let _ : Fintype (Fin k ↪ F) := Fintype.ofFinite _
  exact Measurement.mixture_effect _ _ _

end Measurement

end Cslib.PCP.LowIndividualDegree
