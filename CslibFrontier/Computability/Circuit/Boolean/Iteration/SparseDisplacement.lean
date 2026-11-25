/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Word
public import CslibFrontier.Foundations.Combinatorics.FunctionalGraph.Commutation
public import Mathlib.Data.BitVec
public import Mathlib.Data.FinEnum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Group.End
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Circuits for maps commuting with sparse counter modifications

If an injective word map `h` commutes with a map `f` differing from the binary counter at `r`
inputs, then `h` has a native De Morgan circuit of at most `100 * (n + 1) * (r + 1)` gates.
The displacement `h x - x` changes at at most `2 * r` counter edges. A telescoping sum of
threshold corrections reconstructs it; comparisons, selectors, additions and constants are
all charged. In particular the bound holds for every signed fixed power of a permutation.

These are nonuniform existence results. The correction table is chosen from the whole map;
no efficient table-construction algorithm is asserted. A change of coordinates additionally
requires circuits for both directions, whose sizes are charged explicitly.

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.thresholdSum`: a sum of corrections at passed thresholds.
* `Cslib.Circuits.Boolean.Iteration.displacement`, `displacementCuts`: displacement and its changes.

## Main results

* `Cslib.Circuits.Boolean.Iteration.thresholdSum_displacement`: exact telescoping reconstruction.
* `Cslib.Circuits.Boolean.Iteration.sparse_counter_centralizer`: the sparse-counter circuit bound.
* `Cslib.Circuits.Boolean.Iteration.sparse_counter_power`: the bound for every integer power.
* `Cslib.Circuits.Boolean.Iteration.sparse_coordinate_power`: transfer through charged coordinates.

## References

* Adapted from lean/Proofs/SparseDisplacement.lean at revision `c4cfa198` of
  [S. Schlesinger, *Square-root circuit bounds for iterated functions*]
  [Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

open Cslib.FunctionalGraph

variable {n w : ℕ}

/-- Add the corrections whose thresholds precede the input word. -/
def thresholdSum (S : Finset ℕ) (coeff : ℕ → BitVec w) (base x : BitVec w) : BitVec w :=
  base + ∑ i ∈ S, if (BitVec.ofNat w i).ult x then coeff i else 0

/-- Each threshold uses one comparison, one word selector, and one shared-carry addition. -/
private theorem synthesis_thresholdSum (S : Finset ℕ) (coeff : ℕ → BitVec w) (base : BitVec w)
    (s : Set (BitString n → Bool)) (a : BitString n → BitVec w)
    (ha : ∀ i : Fin w, (fun x => (a x).getLsbD i.val) ∈ s)
    (hc : ∀ b : Bool, (fun _ : BitString n => b) ∈ s) :
    Synthesis Boolean.interpretation s
      (wordWires fun x => thresholdSum S coeff base (a x)) (S.card * (21 * w + 3)) := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.card_empty, Nat.zero_mul]
    apply Synthesis.of_subset; rintro _ ⟨i, rfl⟩
    simpa [thresholdSum] using hc (base.getLsbD i.val)
  | @insert j S hj ih =>
    let prev := fun x => thresholdSum S coeff base (a x)
    let flag := fun x => (BitVec.ofNat w j).ult (a x)
    let term := fun x => if flag x then coeff j else 0
    have ht := Synthesis.word_ult (s := s ∪ wordWires prev) (fun _ => BitVec.ofNat w j) a
      (fun _ => .inl (hc _)) (fun i => .inl (ha i))
    have hm := Synthesis.word_mux (s := (s ∪ wordWires prev) ∪ {flag}) (fun _ => coeff j)
      (fun _ => (0 : BitVec w)) flag (.inr rfl) (fun _ => .inl (.inl (hc _)))
      (fun _ => .inl (.inl (hc _)))
    have hadd := Synthesis.word_add (s := ((s ∪ wordWires prev) ∪ {flag}) ∪ wordWires term)
      prev term (fun i => .inl (.inl (.inr ⟨i, rfl⟩))) (fun i => .inr ⟨i, rfl⟩)
    have h := ih.trans (ht.trans (hm.trans hadd))
    rw [show (fun x => prev x + term x) = fun x => thresholdSum (insert j S) coeff base (a x) from
      funext fun _ => by
        simp only [prev, term, flag, thresholdSum, Finset.sum_insert hj]; abel] at h
    exact h.mono Set.Subset.rfl Set.Subset.rfl (by rw [Finset.card_insert_of_notMem hj]; lia)

/-- Word displacement relative to the counter coordinates. -/
def displacement (h : BitVec n → BitVec n) (x : BitVec n) : BitVec n := h x - x

/-- Changes of displacement, including the wraparound edge. -/
def displacementCuts (h : BitVec n → BitVec n) : Finset ℕ :=
  (Finset.range (2 ^ n)).filter fun i =>
    displacement h (BitVec.ofNat n (i + 1)) ≠ displacement h (BitVec.ofNat n i)

/-- The displacement of `h` changes across `x` and `x + 1` if and only if `h (x + 1) ≠ h x + 1`. -/
theorem displacement_change_iff (h : BitVec n → BitVec n) (x : BitVec n) :
    displacement h (x + 1) ≠ displacement h x ↔ h (x + 1) ≠ h x + 1 := by
  unfold displacement
  constructor <;> contrapose <;> intro he
  · rw [he]
    abel
  · have := congrArg (fun y => y + (x + 1)) he
    simpa only [sub_add_cancel] using this.trans (by abel)

/-- The sparse derivative reconstructs the entire word function by telescoping. -/
theorem thresholdSum_displacement (h : BitVec n → BitVec n) (x : BitVec n) :
    thresholdSum (displacementCuts h)
      (fun i => displacement h (BitVec.ofNat n (i + 1)) -
        displacement h (BitVec.ofNat n i)) (displacement h 0) x = displacement h x := by
  let d := fun i => displacement h (BitVec.ofNat n i)
  have hsum : (∑ i ∈ displacementCuts h,
      if (BitVec.ofNat n i).ult x then d (i + 1) - d i else 0) =
      ∑ i ∈ Finset.range x.toNat, (d (i + 1) - d i) := by
    rw [Finset.sum_subset (s₁ := displacementCuts h) (Finset.filter_subset _ _) fun i hi hn => by
      simp [show d (i + 1) = d i by
        simpa only [displacementCuts, Finset.mem_filter, hi, true_and, not_not, d] using hn]]
    rw [← Finset.sum_subset (Finset.range_mono x.isLt.le) fun i hi hn => by
      simp [BitVec.ult, Nat.mod_eq_of_lt (Finset.mem_range.mp hi), Finset.mem_range.not.mp hn]]
    exact Finset.sum_congr rfl fun i hi => by
      simp [BitVec.ult, Nat.mod_eq_of_lt ((Finset.mem_range.mp hi).trans x.isLt),
        Finset.mem_range.mp hi]
  unfold thresholdSum
  rw [hsum, Finset.sum_range_sub d]; simp [d]

/-- Counter-coordinate changes inject into the commutation-defect set. -/
private theorem displacementCuts_card (f h : BitVec n → BitVec n)
    (hc : Function.Commute h f) (hi : Function.Injective h) :
    (displacementCuts h).card ≤ 2 * (disagreement f (fun x => x + 1)).card := by
  classical
  refine (Finset.card_le_card_of_injOn (BitVec.ofNat n) (t :=
    disagreement (h ∘ (· + 1)) ((· + 1) ∘ h)) (fun i hi => ?_) fun i hi j hj he => ?_).trans
      (commutation_defect_card f (· + 1) h hc hi)
  · simp only [Finset.mem_coe, mem_disagreement, Function.comp_apply]
    exact (displacement_change_iff h (BitVec.ofNat n i)).mp
      (by simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat] using (Finset.mem_filter.mp hi).2)
  · simpa only [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp hi).1),
      Nat.mod_eq_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)] using
        congrArg BitVec.toNat he

/-- A sparse derivative gives an actual native Boolean circuit, including all selection gates. -/
private theorem displacement_circuit (h : BitVec n → BitVec n) :
    ∃ out : Circuit Boolean.signature n n,
      out.Computes Boolean.interpretation
        (fun x i => (h (BitString.equivBitVec x)).getLsbD i.val) ∧
      out.size ≤ 2 + (displacementCuts h).card * (21 * n + 3) + (12 * n + 1) := by
  let constants : Set (BitString n → Bool) := {fun _ => false, fun _ => true}
  let src := inputs n ∪ constants
  have hw (i : Fin n) : (fun x : BitString n => (BitString.equivBitVec x).getLsbD i.val) ∈ src := by
    simpa only [BitString.getLsbD_equivBitVec] using
      (show (fun x : BitString n => x i) ∈ src from .inl ⟨i, rfl⟩)
  have hs := synthesis_thresholdSum (displacementCuts h)
    (fun i => displacement h (BitVec.ofNat n (i + 1)) - displacement h (BitVec.ofNat n i))
    (displacement h 0) src (⇑BitString.equivBitVec) hw (by rintro (_ | _) <;> simp [src, constants])
  simp only [thresholdSum_displacement] at hs
  have hadd := Synthesis.word_add
    (s := src ∪ wordWires fun x => displacement h (BitString.equivBitVec x))
    (⇑BitString.equivBitVec) (fun x => displacement h (BitString.equivBitVec x))
    (fun i => .inl (hw i)) (fun i => .inr ⟨i, rfl⟩)
  simp only [show ∀ x : BitString n,
    BitString.equivBitVec x + displacement h (BitString.equivBitVec x) =
      h (BitString.equivBitVec x) from fun _ => by simp [displacement]] at hadd
  obtain ⟨out, hout, ho⟩ := (((Synthesis.const false).union (Synthesis.const true)).trans
    (hs.trans hadd)).exists_circuit_outputs
  exact ⟨out, hout, by simpa only [← Nat.add_assoc] using ho⟩

/-- Every injective map commuting with an `r`-edited counter has size `O(n(r+1))`.
No transition circuit or state-space enumeration is a hypothesis. -/
theorem sparse_counter_centralizer (f h : BitVec n → BitVec n)
    (hc : Function.Commute h f) (hi : Function.Injective h) :
    ∃ out : Circuit Boolean.signature n n,
      out.Computes Boolean.interpretation
        (fun x i => (h (BitString.equivBitVec x)).getLsbD i.val) ∧
      out.size ≤ 100 * (n + 1) * ((disagreement f (fun x => x + 1)).card + 1) := by
  obtain ⟨out, hout, ho⟩ := displacement_circuit h
  refine ⟨out, hout, ho.trans ?_⟩
  have hb := Nat.mul_le_mul_right (21 * n + 3) (displacementCuts_card f h hc hi)
  nlinarith

/-- The bound applies uniformly to all signed fixed powers of a permutation. -/
theorem sparse_counter_power (f : Equiv.Perm (BitVec n)) (T : ℤ) :
    ∃ out : Circuit Boolean.signature n n,
      out.Computes Boolean.interpretation
        (fun x i => ((f ^ T) (BitString.equivBitVec x)).getLsbD i.val) ∧
      out.size ≤ 100 * (n + 1) * ((disagreement f (fun x => x + 1)).card + 1) := by
  apply sparse_counter_centralizer f (⇑(f ^ T)) ?_ (f ^ T).injective
  intro x
  exact congrArg (fun p : Equiv.Perm (BitVec n) => p x) (Commute.zpow_self f T).eq

/-- Cheap orbit coordinates transfer the sparse bound, charging both conversion circuits. -/
theorem sparse_coordinate_power (f g e : Equiv.Perm (BitVec n))
    (hcycle : ∀ x, e (g x) = e x + 1)
    (encode decode : Circuit Boolean.signature n n)
    (he : encode.Computes Boolean.interpretation
      (fun x i => (e (BitString.equivBitVec x)).getLsbD i.val))
    (hd : decode.Computes Boolean.interpretation
      (fun x i => (e.symm (BitString.equivBitVec x)).getLsbD i.val))
    (T : ℤ) :
    ∃ out : Circuit Boolean.signature n n,
      out.Computes Boolean.interpretation
        (fun x i => ((f ^ T) (BitString.equivBitVec x)).getLsbD i.val) ∧
      out.size ≤ encode.size + decode.size + 100 * (n + 1) * ((disagreement f g).card + 1) := by
  obtain ⟨middle, hm, hs⟩ := sparse_counter_power (e.permCongrHom f) T
  refine ⟨decode.comp (middle.comp encode), fun x => ?_, ?_⟩
  · rw [Circuit.eval_comp, Circuit.eval_comp, he x, hm, hd, ← map_zpow]
    simp only [BitString.equivBitVec_getLsbD, Equiv.permCongrHom_coe, Equiv.permCongr_apply,
      Equiv.symm_apply_apply]
  · change middle.size ≤ 100 * (n + 1) * ((disagreement (e ∘ f ∘ e.symm) (· + 1)).card + 1) at hs
    rw [disagreement_semiconj_card (f : BitVec n → BitVec n) g e (· + 1) hcycle] at hs
    simp only [Circuit.size_comp]; lia

end Cslib.Circuits.Boolean.Iteration
