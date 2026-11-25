/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Fusion.Certificate
public import CslibFrontier.Computability.Circuit.Monotone.Formula

/-!
# Shared circuits for semi-ultrafilter certificates

Two auxiliary bits describe the components of each cover pair. A bank of one AND gate per
pair computes their intersection labels once, sharing them across every consistency test.
Negative intersection labels are free disjunctions of the negative component literals.
Only rejected component sets require their own consistency groups: a rejected intersection
can be charged to a rejected component containing it. Thus two further AND gates per pair
suffice, and the circuit has exactly three AND gates per pair.

Constants and OR gates are free. The primary source values and both auxiliary polarities
are supplied by zero-cost formulas. The construction includes an empty pair list.

## Main results

* `Cslib.Circuits.Fusion.PairCertificate.exists_circuit`: compile the compact certificate
  rejection test to a native circuit with three AND gates per pair.

## References

* [B. P. Cavalar and I. C. Oliveira, *Boolean Circuit Complexity and Two-Dimensional Cover
  Problems*][CavalarOliveira2025], Theorem 45. The explicit factor three follows from the
  shared certificate construction here; the source states an asymptotic characterization.
-/

public section

namespace Cslib.Circuits.Fusion.PairCertificate

private def HasFormula {X : Type*} {k : ℕ} (input : X → Fin k → Bool)
    (P : X → Prop) (cost : ℕ) : Prop :=
  ∃ F : Formula Monotone.signature k,
    (∀ x, F.eval Monotone.interpretation (input x) = true ↔ P x) ∧
    F.cost Monotone.andCost = cost

private theorem HasFormula.const {X : Type*} {k : ℕ} (input : X → Fin k → Bool) (b : Bool) :
    HasFormula input (fun _ => b = true) 0 :=
  ⟨Monotone.const b, fun _ => Iff.rfl, by simp [Monotone.const]⟩

private theorem HasFormula.or {X : Type*} {k a b : ℕ} {input : X → Fin k → Bool}
    {P Q : X → Prop} :
    HasFormula input P a → HasFormula input Q b → HasFormula input (fun x => P x ∨ Q x) (a + b)
  | ⟨F, hF, cF⟩, ⟨G, hG, cG⟩ => ⟨Monotone.or F G, fun x => by simp [hF x, hG x],
      by simp [Monotone.or, Fin.sum_univ_two, cF, cG]⟩

private theorem HasFormula.and {X : Type*} {k a b : ℕ} {input : X → Fin k → Bool}
    {P Q : X → Prop} :
    HasFormula input P a → HasFormula input Q b → HasFormula input (fun x => P x ∧ Q x) (a + b + 1)
  | ⟨F, hF, cF⟩, ⟨G, hG, cG⟩ => ⟨Monotone.and F G, fun x => by simp [hF x, hG x],
      by simp [Monotone.and, Fin.sum_univ_two, cF, cG]⟩

private theorem HasFormula.guard {X : Type*} {k : ℕ} {input : X → Fin k → Bool}
    {P : X → Prop} (hP : HasFormula input P 0) (Q : Prop) :
    HasFormula input (fun x => Q ∧ P x) 0 := by
  classical
  by_cases hQ : Q
  · simpa only [hQ, true_and] using hP
  · simpa only [hQ, false_and, Bool.false_eq_true] using HasFormula.const input false

private theorem HasFormula.exists_fintype {X α : Type*} [Fintype α] {k : ℕ}
    {input : X → Fin k → Bool} (P : α → X → Prop) (cost : α → ℕ)
    (h : ∀ i, HasFormula input (P i) (cost i)) :
    HasFormula input (fun x => ∃ i, P i x) (∑ i, cost i) := by
  classical
  suffices ∀ s : Finset α, HasFormula input (fun x => ∃ i ∈ s, P i x) (∑ i ∈ s, cost i) by
    simpa only [Finset.mem_univ, true_and] using this Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using HasFormula.const input false
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi, Finset.mem_insert, exists_eq_or_imp] using (h i).or ih

private theorem HasFormula.exists_zero {X α : Type*} [Finite α] {k : ℕ}
    {input : X → Fin k → Bool} {P : α → X → Prop}
    (h : ∀ i, HasFormula input (P i) 0) :
    HasFormula input (fun x => ∃ i, P i x) 0 := by
  cases nonempty_fintype α
  simpa only [Finset.sum_const_zero] using HasFormula.exists_fintype P (fun _ => 0) h

/-- Compile the compact consistency test with exactly three AND gates per pair. The
intersection of the two labels of each pair is computed once and shared; its negative polarity
is a free OR. Primary source values and both auxiliary polarities have zero-cost formulas. -/
theorem exists_circuit {U X : Type*} {n k : ℕ} (pairs : List (Set U × Set U))
    (sources : Fin n → Set U) (input : X → Fin k → Bool)
    (x : X → Fin n → Bool) (y : X → Fin (compactSize pairs) → Bool)
    (hx : ∀ l, ∃ F : Formula Monotone.signature k,
      (∀ z, F.eval Monotone.interpretation (input z) = true ↔ x z l = true) ∧
      F.cost Monotone.andCost = 0)
    (hy : ∀ i b, ∃ F : Formula Monotone.signature k,
      (∀ z, F.eval Monotone.interpretation (input z) = true ↔ y z i = b) ∧
      F.cost Monotone.andCost = 0) :
    ∃ c : Circuit Monotone.signature k 1,
      (∀ z, c.eval Monotone.interpretation (input z) 0 = true ↔
        compactInvalid pairs sources (x z) (y z)) ∧
      c.program.cost Monotone.andCost = 3 * pairs.length := by
  classical
  choose Y hY cY using hy
  let positive (i : Fin pairs.length) : Formula Monotone.signature k :=
    Monotone.and (Y (Fin.castAdd pairs.length i) true) (Y (Fin.natAdd pairs.length i) true)
  have hpositive (i : Fin pairs.length) (z : X) :
      (positive i).eval Monotone.interpretation (input z) =
        (y z (Fin.castAdd pairs.length i) && y z (Fin.natAdd pairs.length i)) :=
    Bool.eq_iff_iff.mpr (by simp only [positive, Monotone.eval_and, Bool.and_eq_true, hY])
  have cpositive (i : Fin pairs.length) : (positive i).cost Monotone.andCost = 1 := by
    simp [positive, Monotone.and, Fin.sum_univ_two, cY]
  let bank : Circuit Monotone.signature k (k + pairs.length) :=
    (Circuit.wiring Monotone.signature id).append (Circuit.pi fun i => (positive i).toCircuit)
  let values (z : X) : Fin (k + pairs.length) → Bool :=
    Fin.append (input z) fun i =>
      y z (Fin.castAdd pairs.length i) && y z (Fin.natAdd pairs.length i)
  have hbank (z : X) : bank.eval Monotone.interpretation (input z) = values z := by
    simp only [bank, Circuit.eval_append, Circuit.eval_wiring, Circuit.eval_pi,
      Formula.eval_toCircuit, hpositive, values, Function.comp_id]
  have cbank : bank.program.cost Monotone.andCost = pairs.length := by
    simp only [bank, Circuit.cost_program_append, Circuit.cost_program_wiring,
      Circuit.cost_program_pi, Formula.cost_toCircuit, cpositive, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_one, Nat.zero_add]
  have hlift {P : X → Prop} : HasFormula input P 0 → HasFormula values P 0
    | ⟨F, hF, cF⟩ => ⟨F.rename (Fin.castAdd pairs.length), fun z => by
        simpa only [Formula.eval_rename, values, Function.comp_def, Fin.append_left] using hF z,
        by simpa only [Formula.cost_rename] using cF⟩
  have haux (i : Fin (compactSize pairs)) (b : Bool) :
      HasFormula values (fun z => y z i = b) 0 := hlift ⟨Y i b, hY i b, cY i b⟩
  have hexpanded (i : Fin (size pairs)) (b : Bool) :
      HasFormula values (fun z => expandLabels pairs (y z) i = b) 0 := by
    refine Fin.addCases (fun j => ?_) (Fin.addCases (fun j => ?_) fun j => ?_) i
    · simpa only [expandLabels, Fin.append_left] using haux (Fin.castAdd pairs.length j) b
    · simpa only [expandLabels, Fin.append_right, Fin.append_left] using
        haux (Fin.natAdd pairs.length j) b
    · cases b
      · simpa only [expandLabels, Fin.append_right, Bool.and_eq_false_iff, Nat.add_zero] using
          (haux (Fin.castAdd pairs.length j) false).or (haux (Fin.natAdd pairs.length j) false)
      · exact ⟨.input (Fin.natAdd k j), fun z => by
          simp only [Formula.eval_input, values, expandLabels, Fin.append_right], rfl⟩
  have hlabel (i : Option (Fin (size pairs))) (b : Bool) :
      HasFormula values (fun z => label pairs (expandLabels pairs (y z)) i = b) 0 := by
    cases i with
    | none =>
      cases b
      · simpa only [label, eq_self] using HasFormula.const values true
      · exact HasFormula.const values false
    | some i => exact hexpanded i b
  have hconflicts (s : Set U) :
      HasFormula values (fun z => conflicts pairs sources (x z) (expandLabels pairs (y z)) s) 0 :=
    by simpa only [conflicts, Nat.add_zero] using
      (HasFormula.exists_zero fun i => (hlabel i true).guard (sets pairs i ⊆ s)).or
        ((HasFormula.exists_zero fun i => (hlabel i false).guard (s ∪ sets pairs i = Set.univ)).or
          (HasFormula.exists_zero fun l => (hlift (hx l)).guard (sources l ⊆ s)))
  have hside (idx : Fin pairs.length → Fin (compactSize pairs)) (side : Set U × Set U → Set U) :
      HasFormula values (fun z => ∃ i : Fin pairs.length, y z (idx i) = false ∧
        conflicts pairs sources (x z) (expandLabels pairs (y z)) (side (pairs.get i)))
      pairs.length := by
    simpa using HasFormula.exists_fintype _ (fun _ : Fin pairs.length => 1) fun i =>
      (haux (idx i) false).and (hconflicts (side (pairs.get i)))
  obtain ⟨F, hF, cF⟩ : HasFormula values
      (fun z => compactInvalid pairs sources (x z) (y z)) (2 * pairs.length) := by
    simpa only [compactInvalid, Nat.zero_add, two_mul] using
      (hconflicts ∅).or ((hside (Fin.castAdd _) Prod.fst).or (hside (Fin.natAdd _) Prod.snd))
  refine ⟨F.toCircuit.comp bank, fun z => ?_, ?_⟩
  · simpa only [Circuit.eval_comp, hbank, Formula.eval_toCircuit] using hF z
  · rw [Circuit.cost_program_comp, cbank, Formula.cost_toCircuit, cF]; omega

end Cslib.Circuits.Fusion.PairCertificate

