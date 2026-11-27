/-
Copyright (c) 2026 vhalan anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vhalan anandarajah
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SAT
public import CslibFrontier.Computability.Machines.Turing.SingleTape.FoolingSet
import CslibFrontier.Computability.Communication.Functions
import CslibFrontier.Computability.Complexity.Problems.SAT.Units
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Logics.Propositional.CNF.Encoding
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# A single-tape lower bound for SAT under the CNF encoding

This module bounds the time to decide `Cslib.Complexity.encCNF '' Cslib.Complexity.SAT` on
a deterministic single-tape machine with a finite alphabet and head output. The machine may use
its entire tape.

Two sign vectors are written as unit clauses separated by tautological clauses. The formula
is satisfiable exactly when the vectors agree. Framing preserves concatenation and gives all
family members at a fixed vector width the same bit length. Applying
`Cslib.Turing.SingleTapeTM.crossing_foolingSet_bit_bound` to this equality family gives an
original lower bound for the encoded SAT language.

## Main definitions

* `Cslib.Complexity.satEqualityFamilyLength`: the exact encoded length of the equality family.

## Main results

* `Cslib.Complexity.le_satEqualityFamilyLength`: the family length is at least the vector width.
* `Cslib.Complexity.satEqualityFamilyLength_le`: a logarithmic factor bounds the bit cost per digit.
* `Cslib.Complexity.singleTape_sat_clock_lower`: the crossing lower bound at family lengths.
* `Cslib.Complexity.singleTape_sat_quadratic_log_lower`: the quadratic-over-logarithmic time bound.
* `Cslib.Complexity.singleTape_sat_no_linear`: no linear worst-case clock suffices.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM Cslib.Turing

private def signLiterals {k : ℕ} (x : Fin k → Bool) : List (Literal ℕ) :=
  List.ofFn fun i : Fin k => (i.val, x i)

private def tautology : Clause ℕ := [(0, false), (0, true)]

private theorem padded_units_sat {k : ℕ} (x y : Fin k → Bool) (pad : ℕ) :
    SAT.units (signLiterals x) ++ List.replicate pad tautology ++ SAT.units (signLiterals y) ∈
      SAT ↔ x = y := by
  have ht (v : ℕ → Bool) : tautology.eval v = true := by
    cases h : v 0 <;> simp [tautology, Clause.eval, Literal.eval, h]
  have check (v : ℕ → Bool) :
      (SAT.units (signLiterals x) ++ List.replicate pad tautology ++
        SAT.units (signLiterals y)).eval v = true ↔
        (∀ i : Fin k, v i.val = x i) ∧ (∀ i : Fin k, v i.val = y i) := by
    have hp : (List.replicate pad tautology).all (Clause.eval v) = true := by
      simp [ht]
    rw [SAT.eval_append_units, SAT.eval_units_append]
    simp only [signLiterals, List.forall_mem_ofFn_iff, CNF.eval, hp, and_true]
  change (∃ v, _ = true) ↔ _
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨hx, hy⟩ := (check v).mp hv
    exact funext fun i => (hx i).symm.trans (hy i)
  · rintro rfl
    let v (j : ℕ) := if h : j < k then x ⟨j, h⟩ else false
    exact ⟨v, (check v).mpr ⟨fun i => dite_eq_left i.isLt, fun i => dite_eq_left i.isLt⟩⟩

private theorem encoded_mem (f : CNF ℕ) : encCNF f ∈ encCNF '' SAT ↔ f ∈ SAT := by
  simp only [Set.mem_image, encCNF.injective.eq_iff, exists_eq_right]

private theorem enc_append (f g : CNF ℕ) :
    encCNF (f ++ g) = encCNF f ++ encCNF g := by
  exact encList_append _ _ _

private theorem units_length_eq_sum (answers : List (Literal ℕ)) :
    (encCNF (SAT.units answers)).length =
      (answers.map fun l => 8 * (encNat l.1).length + 11).sum := by
  induction answers with
  | nil => rfl
  | cons l answers ih =>
    change (encCNF ([[l]] ++ SAT.units answers)).length = _
    rw [SAT.length_encCNF_append, SAT.length_encCNF_unit, ih, List.map_cons, List.sum_cons]

private def dataLength (k : ℕ) : ℕ :=
  (encCNF (SAT.units (signLiterals (fun _ : Fin k => false)))).length

private def padding (k : ℕ) : List Bool :=
  encCNF (List.replicate (2 * dataLength k) tautology)

/-- Exact bit length of the framed equality family at the given number of literals. -/
def satEqualityFamilyLength (k : ℕ) : ℕ := 2 * dataLength k + (padding k).length

private theorem dataLength_le (k : ℕ) :
    dataLength k ≤ k * (19 * (Nat.log2 k + 1)) := by
  rw [dataLength, units_length_eq_sum]
  refine (List.sum_le_length_nsmul _ (8 * (Nat.log2 k + 1) + 11) ?_).trans ?_
  · simp only [List.forall_mem_map, signLiterals, List.forall_mem_ofFn_iff]
    intro i
    have bits := length_encNat_le_log2 i.isLt.le
    omega
  · rw [List.length_map, signLiterals, List.length_ofFn, nsmul_eq_mul]
    exact Nat.mul_le_mul_left _ (by omega)

private theorem satEqualityFamilyLength_eq (k : ℕ) :
    satEqualityFamilyLength k = 44 * dataLength k := by
  have framed : 2 * (encClause encNat tautology).length + 1 = 21 := by decide
  simp only [satEqualityFamilyLength, padding, encCNF, length_encList, List.map_replicate,
    List.sum_replicate, smul_eq_mul]
  change 2 * dataLength k + 2 * dataLength k * (2 * (encClause encNat tautology).length + 1) = _
  rw [framed]
  omega

/-- A family with `k` equality bits has at least `k` input bits. -/
theorem le_satEqualityFamilyLength (k : ℕ) : k ≤ satEqualityFamilyLength k := by
  have h := SAT.length_vars_le (SAT.units (signLiterals (fun _ : Fin k => false)))
  rw [SAT.vars_units, List.length_map, signLiterals, List.length_ofFn] at h
  change k ≤ dataLength k at h
  rw [satEqualityFamilyLength_eq]
  exact h.trans (by omega)

/-- The family length is at most `836 (⌊log₂ k⌋ + 1)` bits per equality bit. -/
theorem satEqualityFamilyLength_le (k : ℕ) :
    satEqualityFamilyLength k ≤ 836 * k * (Nat.log2 k + 1) := by
  rw [satEqualityFamilyLength_eq]
  exact (Nat.mul_le_mul_left _ (dataLength_le k)).trans_eq (by ring)

/-- At these input lengths, a single-tape decider must spend time proportional
to the input length times the number of independent equality bits, with a
machine-dependent constant. Its tape use is unrestricted. -/
theorem singleTape_sat_clock_lower {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
    {tm : SingleTapeTM Symbol} {ι : Bool → Symbol} {yes : Symbol} {T : ℕ → ℕ}
    (decides : tm.DecidesByHeadInTime ι (encCNF '' SAT) yes T) (k : ℕ)
    (enough : 2 * Nat.clog 2 (Fintype.card tm.State + 2) ≤ k) :
    (satEqualityFamilyLength k + 1) * k ≤
      8 * Nat.clog 2 (Fintype.card tm.State + 2) * T (satEqualityFamilyLength k) := by
  classical
  let w (x : Fin k → Bool) := encCNF (SAT.units (signLiterals x))
  let m := dataLength k
  let middle := padding k
  let S : Finset ((Fin k → Bool) × (Fin k → Bool)) :=
    Finset.univ.image (fun x => (x, x))
  have cardS : S.card = 2 ^ k := by
    rw [Finset.card_image_of_injective _ (fun x y h => (Prod.mk.inj h).1)]
    simp
  have agrees (x y) : w x ++ middle ++ w y ∈ encCNF '' SAT ↔
      Communication.equality x y = true := by
    change encCNF (SAT.units (signLiterals x)) ++ encCNF (List.replicate (2 * m) tautology) ++
      encCNF (SAT.units (signLiterals y)) ∈ encCNF '' SAT ↔ _
    rw [← enc_append, ← enc_append, encoded_mem, padded_units_sat,
      Communication.equality, decide_eq_true_eq]
  have fixed (x : Fin k → Bool) : (w x).length = m := by
    dsimp only [w, m, dataLength]
    simp only [units_length_eq_sum, signLiterals, List.map_ofFn, Function.comp_def]
  have whole (p : (Fin k → Bool) × (Fin k → Bool)) :
      (w p.1 ++ middle ++ w p.2).length = 2 * m + middle.length := by
    simp only [List.length_append, fixed]
    omega
  have hmid : 2 * m ≤ middle.length := by
    change 2 * m ≤ (encCNFOver encNat (List.replicate (2 * m) tautology)).length
    rw [encCNFOver, length_encList, List.map_replicate, List.sum_replicate, smul_eq_mul]
    exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have bound := SingleTapeTM.crossing_foolingSet_bit_bound decides
    (Communication.isFoolingSet_equality (Finset.univ : Finset (Fin k → Bool)))
    w middle w agrees (fun p _ => fixed p.1) (fun p _ => whole p) k enough cardS.ge
  change (middle.length + 1) * k ≤
    4 * Nat.clog 2 (Fintype.card tm.State + 2) * T (satEqualityFamilyLength k) at bound
  have len : satEqualityFamilyLength k + 1 ≤ 2 * (middle.length + 1) := by
    change 2 * m + middle.length + 1 ≤ _
    omega
  calc
    _ ≤ (2 * (middle.length + 1)) * k := Nat.mul_le_mul_right _ len
    _ = 2 * ((middle.length + 1) * k) := by ring
    _ ≤ _ := (Nat.mul_le_mul_left 2 bound).trans_eq (by ring)

/-- On the constructed input lengths, the lower bound is quadratic up to a logarithmic divisor.
The inequality clears the divisor and uses the exact integer state-dependent constant. -/
theorem singleTape_sat_quadratic_log_lower {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
    {tm : SingleTapeTM Symbol} {ι : Bool → Symbol} {yes : Symbol} {T : ℕ → ℕ}
    (decides : tm.DecidesByHeadInTime ι (encCNF '' SAT) yes T) (k : ℕ)
    (enough : 2 * Nat.clog 2 (Fintype.card tm.State + 2) ≤ k) :
    satEqualityFamilyLength k ^ 2 ≤ 6688 * Nat.clog 2 (Fintype.card tm.State + 2) *
      (Nat.log2 (satEqualityFamilyLength k) + 1) * T (satEqualityFamilyLength k) := by
  let N := satEqualityFamilyLength k
  let D := Nat.clog 2 (Fintype.card tm.State + 2)
  let L := Nat.log2 N + 1
  have hlog : Nat.log2 k ≤ Nat.log2 N := by
    simpa only [Nat.log2_eq_log_two] using
      Nat.log_mono_right (b := 2) (le_satEqualityFamilyLength k)
  have hlen : N ≤ 836 * k * L :=
    (satEqualityFamilyLength_le k).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hlog 1))
  have time : (N + 1) * k ≤ 8 * D * T N := singleTape_sat_clock_lower decides k enough
  change N ^ 2 ≤ 6688 * D * L * T N
  calc
    N ^ 2 ≤ (N + 1) * (836 * k * L) := by
      rw [pow_two]
      exact Nat.mul_le_mul (Nat.le_succ N) hlen
    _ = (836 * L) * ((N + 1) * k) := by ring
    _ ≤ (836 * L) * (8 * D * T N) := Nat.mul_le_mul_left _ time
    _ = _ := by ring

/-- The crossing lower bound excludes every linear clock for a single-tape SAT decider. -/
theorem singleTape_sat_no_linear {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
    {tm : SingleTapeTM Symbol} {ι : Bool → Symbol} {yes : Symbol} {C : ℕ} :
    ¬ tm.DecidesByHeadInTime ι (encCNF '' SAT) yes (fun n => C * (n + 1)) := by
  intro decides
  let d := Nat.clog 2 (Fintype.card tm.State + 2)
  let k := 8 * d * C + 2 * d + 1
  have hk : 2 * d ≤ k := by omega
  have bound := singleTape_sat_clock_lower decides k hk
  change (satEqualityFamilyLength k + 1) * k ≤
    8 * d * (C * (satEqualityFamilyLength k + 1)) at bound
  have bad : (satEqualityFamilyLength k + 1) * k ≤ (satEqualityFamilyLength k + 1) * (8 * d * C) :=
    bound.trans_eq (by ring)
  have bad' : k ≤ 8 * d * C := Nat.le_of_mul_le_mul_left bad (Nat.succ_pos _)
  omega

end Cslib.Complexity
