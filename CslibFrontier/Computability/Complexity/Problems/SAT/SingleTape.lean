/-
Copyright (c) 2026 vhalan anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vhalan anandarajah
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SAT
public import CslibFrontier.Computability.Machines.Turing.SingleTape.FoolingSet
import CslibFrontier.Logics.Propositional.CNF.Encoding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-!
# A single-tape lower bound for framed SAT

The hard family puts two sign vectors in lists of unit clauses, with tautological clauses
in between. The formula is satisfiable exactly when the two vectors agree. The native
framed SAT encoding preserves concatenation and gives all members at a fixed width the
same bit length. The resulting equality fooling set forces many crossing sequences.

The model is the deterministic single tape with head output, a finite alphabet, and
unrestricted use of its tape. The proof uses the actual input bit length.

## Main results

* `singleTape_sat_clock_lower` bounds the native running time along the equality family.
* `singleTape_sat_no_linear` excludes every linear worst-case clock.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM Cslib.Turing

private def units {k : ℕ} (x : Fin k → Bool) : CNF ℕ :=
  List.ofFn fun i => [(i.val, x i)]

private def tautology : Clause ℕ := [(0, false), (0, true)]

private theorem units_eval {k : ℕ} (x : Fin k → Bool) (v : ℕ → Bool) :
    (units x).eval v = true ↔ ∀ i : Fin k, v i.val = x i := by
  simp [units, CNF.eval, Clause.eval, Literal.eval, List.all_eq_true, List.mem_ofFn,
    beq_iff_eq]

private theorem padded_units_sat {k : ℕ} (x y : Fin k → Bool) (pad : ℕ) :
    units x ++ List.replicate pad tautology ++ units y ∈ SAT ↔ x = y := by
  have ht (v : ℕ → Bool) : tautology.eval v = true := by
    cases h : v 0 <;> simp [tautology, Clause.eval, Literal.eval, h]
  have check (v : ℕ → Bool) :
      (units x ++ List.replicate pad tautology ++ units y).eval v = true ↔
        (∀ i : Fin k, v i.val = x i) ∧ (∀ i : Fin k, v i.val = y i) := by
    have hp : (List.replicate pad tautology).all (Clause.eval v) = true := by
      simp [ht]
    have h := and_congr (units_eval x v) (units_eval y v)
    simpa only [CNF.eval, List.all_append, hp, Bool.and_true, Bool.and_eq_true] using h
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

private theorem units_length {k : ℕ} (x y : Fin k → Bool) :
    (encCNF (units x)).length = (encCNF (units y)).length := by
  change (encCNFOver encNat (units x)).length = (encCNFOver encNat (units y)).length
  simp only [units, encCNFOver, length_encList, List.map_ofFn, Function.comp_def]
  congr 2
  funext i
  cases x i <;> cases y i <;> simp

private def dataLength (k : ℕ) : ℕ :=
  (encCNF (units (fun _ : Fin k => false))).length

private def padding (k : ℕ) : List Bool :=
  encCNF (List.replicate (2 * dataLength k) tautology)

/-- Exact bit length of the framed equality family at the given number of literals. -/
def satEqualityFamilyLength (k : ℕ) : ℕ := 2 * dataLength k + (padding k).length

private theorem dataLength_le (k u : ℕ) (hku : k ≤ u) :
    dataLength k ≤ k * (19 * (Nat.log2 u + 1)) := by
  let L := Nat.log2 u + 1
  have clauseLen (c : Clause ℕ) (hc : c ∈ units (fun _ : Fin k => false)) :
      (encClause encNat c).length ≤ 4 * L + 5 := by
    rw [units, List.mem_ofFn] at hc
    obtain ⟨i, rfl⟩ := hc
    have bits := length_encNat_le_log2 (i.isLt.le.trans hku)
    change (encList (encPair encNat encBool) [(i.val, false)]).length ≤ _
    simp only [encList_cons, encList_nil, List.append_nil, length_frame, length_encPair,
      encBool_apply, List.length_singleton]
    omega
  change (encList (encClause encNat) (units (fun _ : Fin k => false))).length ≤ _
  have h := length_encList_le (encClause encNat) _ clauseLen
  rw [units, List.length_ofFn] at h
  apply h.trans
  apply Nat.mul_le_mul_left
  dsimp only [L]
  omega

private theorem satEqualityFamilyLength_eq (k : ℕ) :
    satEqualityFamilyLength k = 44 * dataLength k := by
  have framed : 2 * (encClause encNat tautology).length + 1 = 21 := by decide
  simp only [satEqualityFamilyLength, padding, encCNF, length_encList, List.map_replicate,
    List.sum_replicate, smul_eq_mul]
  change 2 * dataLength k + 2 * dataLength k * (2 * (encClause encNat tautology).length + 1) = _
  rw [framed]
  omega

/-- Exact framing gives a uniform quadratic-over-log scale for the crossing lower bound. -/
theorem satEqualityFamilyLength_le (k u : ℕ) (hku : k ≤ u) :
    satEqualityFamilyLength k ≤ 836 * k * (Nat.log2 u + 1) := by
  rw [satEqualityFamilyLength_eq]
  exact (Nat.mul_le_mul_left _ (dataLength_le k u hku)).trans_eq (by ring)

private theorem le_satEqualityFamilyLength (k : ℕ) : k ≤ satEqualityFamilyLength k := by
  have h := SizedListEncoding.length_le (encA := encClause encNat)
    (encL := encList (encClause encNat)) (units (fun _ : Fin k => false))
  rw [units, List.length_ofFn] at h
  change k ≤ dataLength k at h
  rw [satEqualityFamilyLength_eq]
  exact h.trans (by omega)

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
  let w (x : Fin k → Bool) := encCNF (units x)
  let m := dataLength k
  let middle := padding k
  let S : Finset ((Fin k → Bool) × (Fin k → Bool)) :=
    Finset.univ.image (fun x => (x, x))
  have cardS : S.card = 2 ^ k := by
    rw [Finset.card_image_of_injective _ (fun x y h => (Prod.mk.inj h).1)]
    simp
  have fool : Communication.IsFoolingSet (fun x y : Fin k → Bool => decide (x = y)) true S := by
    constructor
    · intro p hp
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hp
      simp
    · intro p hp q hq hx _
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hq
      have eq : x = y := of_decide_eq_true hx
      subst y
      rfl
  have agrees (x y) : w x ++ middle ++ w y ∈ (encCNF '' SAT) ↔ decide (x = y) = true := by
    change encCNF (units x) ++ encCNF (List.replicate (2 * m) tautology) ++
      encCNF (units y) ∈ (encCNF '' SAT) ↔ _
    rw [← enc_append, ← enc_append, encoded_mem, padded_units_sat, decide_eq_true_eq]
  have fixed (x) : (w x).length = m := units_length x (fun _ => false)
  have whole (p : (Fin k → Bool) × (Fin k → Bool)) :
      (w p.1 ++ middle ++ w p.2).length = 2 * m + middle.length := by
    simp only [List.length_append, fixed]
    omega
  have hmid : 2 * m ≤ middle.length := by
    change 2 * m ≤ (encCNFOver encNat (List.replicate (2 * m) tautology)).length
    rw [encCNFOver, length_encList, List.map_replicate, List.sum_replicate, smul_eq_mul]
    exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have bound := SingleTapeTM.crossing_foolingSet_bit_bound decides fool w middle w agrees
    (fun p _ => fixed p.1) (fun p _ => whole p) k enough cardS.ge
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
    let N := satEqualityFamilyLength k
    N ^ 2 ≤ 6688 * Nat.clog 2 (Fintype.card tm.State + 2) * (Nat.log2 N + 1) * T N := by
  let N := satEqualityFamilyLength k
  let D := Nat.clog 2 (Fintype.card tm.State + 2)
  let L := Nat.log2 N + 1
  have hlen : N ≤ 836 * k * L := satEqualityFamilyLength_le k N (le_satEqualityFamilyLength k)
  have time : (N + 1) * k ≤ 8 * D * T N := singleTape_sat_clock_lower decides k enough
  change N ^ 2 ≤ 6688 * D * L * T N
  calc
    N ^ 2 ≤ (N + 1) * (836 * k * L) := by
      rw [pow_two]
      exact Nat.mul_le_mul (Nat.le_succ N) hlen
    _ = (836 * L) * ((N + 1) * k) := by ring
    _ ≤ (836 * L) * (8 * D * T N) := Nat.mul_le_mul_left _ time
    _ = _ := by ring

/-- The quantitative bound excludes all linear clocks on the native single-tape model. -/
theorem singleTape_sat_no_linear {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
    {tm : SingleTapeTM Symbol} {ι : Bool → Symbol} {yes : Symbol} {C : ℕ}
    (decides : tm.DecidesByHeadInTime ι (encCNF '' SAT) yes (fun n => C * (n + 1))) : False := by
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
