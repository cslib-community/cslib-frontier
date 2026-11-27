/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.MIP.Arithmetization
public import CslibFrontier.Computability.Complexity.Classes.PCP.Oracle
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Probability.PMF.BindFailure

/-!
# Checking the final arithmetized constraint with three local corrections

A succinct clause has three literals. The verifier rejects any failed local correction and
substitutes three successful values into the modular evaluator for the tableau polynomial.
If the sumcheck claim differs from the ideal polynomial evaluation, acceptance requires at
least one erroneous local correction.

## Main definitions

* `literalPoint` extracts the assignment-table address of one literal from the circuit wires.
* `verifyConstraint` runs the three corrections and tests the claim with `checkConstraintClaim`.

## Main results

* `isOraclePPTOn_verifyConstraint` certifies the verifier given strict polynomial-time corrections.
* `run_verifyConstraint_of_correct` identifies the verifier's answer when each correction returns
  the value of the assignment polynomial at its literal.
* `acceptProb_verifyConstraint_of_wrong_claim` bounds false acceptance by three times the common
  error bound for a literal correction.
-/

public section

namespace Cslib.Complexity.MIP

open Probability Circuits Circuits.Boolean Turing.MultiTapeTM
open scoped ENNReal

/-- The assignment-table address embedded in a vector of circuit wire values for literal `j`. -/
@[expose] def literalPoint {Q L : ℕ} {F : Type} (c : Circuit signature Q (3 * (L + 1)))
    (z : Fin (Q + c.size) → F) (j : Fin 3) : Fin L → F :=
  fun i => z ⟨(c.outputs (SuccinctVerifier.addressWire L j i)).toNat, Wire.toNat_lt _⟩

/-- Corrected evaluations of the three literals are required before testing the arithmetic claim. -/
def checkConstraintClaim (p Q : ℕ) (gates : List (Op × List ℕ))
    (r z signs : List ℕ) (claim : ℕ) (v : Fin 3 → Option ℕ) : Bool :=
  (v 0).isSome && (v 1).isSome && (v 2).isSome && decide
    (evalConstraintMod p Q gates r z signs [(v 0).getD 0, (v 1).getD 0, (v 2).getD 0] % p =
      claim % p)

private theorem computableInPolyTime_checkConstraintClaim {α : Type} {enc : α ↪ List Bool}
    {p Q claim : α → ℕ} {gates : α → List (Op × List ℕ)} {r z signs : α → List ℕ}
    {v : α → Fin 3 → Option ℕ} (hp : ComputableInPolyTime p enc encNat)
    (hQ : ComputableInPolyTime Q enc encNat)
    (hgates : ComputableInPolyTime gates enc (encList encGate))
    (hr : ComputableInPolyTime r enc (encList encNat))
    (hz : ComputableInPolyTime z enc (encList encNat))
    (hsigns : ComputableInPolyTime signs enc (encList encNat))
    (hclaim : ComputableInPolyTime claim enc encNat)
    (hv : ∀ j, ComputableInPolyTime (fun a => v a j) enc (encOption encUnary)) :
    ComputableInPolyTime
      (fun a => checkConstraintClaim (p a) (Q a) (gates a) (r a) (z a) (signs a) (claim a) (v a))
      enc encBool := by
  have val (j : Fin 3) := ComputableInPolyTime.unary_to_binary.comp
    (ComputableInPolyTime.optionGetDWithInput (hv j) (.const 0))
  have hvals : ComputableInPolyTime
      (fun a => [(v a 0).getD 0, (v a 1).getD 0, (v a 2).getD 0]) enc (encList encNat) :=
    (ComputableInPolyTime.cons encNat).comp ((val 0).prod ((ComputableInPolyTime.cons encNat).comp
      ((val 1).prod ((ComputableInPolyTime.cons encNat).comp ((val 2).prod (.const []))))))
  have t := ComputableInPolyTime.decide_eq'
    (ComputableInPolyTime.binary_mod'
      (computableInPolyTime_evalConstraintMod hp hQ hgates hr hz hsigns hvals) hp)
    (ComputableInPolyTime.binary_mod' hclaim hp)
  have state (j : Fin 3) := ComputableInPolyTime.optionIsSome (hv j)
  unfold checkConstraintClaim
  exact ComputableInPolyTime.bool_and.comp
    ((ComputableInPolyTime.bool_and.comp
      ((ComputableInPolyTime.bool_and.comp ((state 0).prod (state 1))).prod (state 2))).prod t)

/-- When the three successfully corrected field values are right, this check compares the
claimed residue to the arithmetized constraint at the verifier's sumcheck point. -/
private theorem checkConstraintClaim_eq {p Q L : ℕ} [NeZero p]
    (c : Circuit signature Q (3 * (L + 1))) (A : MvPolynomial (Fin L) (ZMod p))
    (r z : Fin (Q + c.size) → ZMod p) (claim : ℕ) (v : Fin 3 → ℕ)
    (hv : ∀ j, (v j : ZMod p) = MvPolynomial.eval (literalPoint c z j) A) :
    checkConstraintClaim p Q c.code.1 (List.ofFn fun i => (r i).val)
      (List.ofFn fun i => (z i).val)
      (List.ofFn fun j : Fin 3 => (c.outputs (SuccinctVerifier.signWire L j)).toNat)
      claim (fun j => some (v j)) =
      decide (MvPolynomial.eval z (tableauConstraintPoly c A r) = (claim : ZMod p)) := by
  unfold literalPoint at hv
  have h := natCast_evalConstraintMod (NeZero.pos p) c A (fun i => (r i).val)
    (fun i => (z i).val) v (by simpa only [ZMod.natCast_zmod_val] using hv)
  simp only [ZMod.natCast_zmod_val] at h
  have hvlist : List.ofFn v = [v 0, v 1, v 2] := by
    simp [List.ofFn_succ]
  rw [hvlist] at h
  simp only [checkConstraintClaim, Option.isSome_some, Bool.true_and, Option.getD_some,
    ← ZMod.natCast_eq_natCast_iff', h]

private theorem probability_three_errors {α β γ : Type} (a : PMF α) (b : PMF β) (c : PMF γ)
    (badA : Set α) (badB : Set β) (badC : Set γ) (check : α → β → γ → Bool)
    (h : ∀ x ∉ badA, ∀ y ∉ badB, ∀ z ∉ badC, check x y z = false) :
    (a.bind fun x => b.bind fun y => c.map (check x y)).toOuterMeasure {true} ≤
      a.toOuterMeasure badA + (b.toOuterMeasure badB + c.toOuterMeasure badC) := by
  refine PMF.toOuterMeasure_bind_le_add _ _ badA _ _ fun x _ hx => ?_
  refine PMF.toOuterMeasure_bind_le_add _ _ badB _ _ fun y _ hy => ?_
  rw [_root_.PMF.toOuterMeasure_map_apply]
  refine c.toOuterMeasure.mono ?_
  intro z hz
  by_contra hn
  have : check x y z = false := h x hx y hy z hn
  exact Bool.noConfusion (this.symm.trans (show check x y z = true from hz))

/-- Run the three local corrections, then compare the claimed value with the constraint. -/
def verifyConstraint (p Q : ℕ) (gates : List (Op × List ℕ)) (r z signs : List ℕ) (claim : ℕ)
    (read : Fin 3 → WordOracleComp Unit (Option ℕ)) : WordOracleComp Unit Bool := do
  let x ← read 0
  let y ← read 1
  (fun z' => checkConstraintClaim p Q gates r z signs claim ![x, y, z']) <$> read 2

/-- The final arithmetic comparison preserves strict polynomial time when its three
local correction calls have strict polynomial-time implementations. -/
theorem isOraclePPTOn_verifyConstraint {α : Type} {enc : α ↪ List Bool}
    {p Q claim : α → ℕ} {gates : α → List (Op × List ℕ)} {r z signs : α → List ℕ}
    {read : α → Fin 3 → WordOracleComp Unit (Option ℕ)} (hp : ComputableInPolyTime p enc encNat)
    (hQ : ComputableInPolyTime Q enc encNat)
    (hgates : ComputableInPolyTime gates enc (encList encGate))
    (hr : ComputableInPolyTime r enc (encList encNat))
    (hz : ComputableInPolyTime z enc (encList encNat))
    (hsigns : ComputableInPolyTime signs enc (encList encNat))
    (hclaim : ComputableInPolyTime claim enc encNat)
    (hread : ∀ j, IsOraclePPTOn enc (encOption encUnary) (fun a => read a j)) :
    IsOraclePPTOn enc encBool (fun a =>
      verifyConstraint (p a) (Q a) (gates a) (r a) (z a) (signs a) (claim a) (read a)) := by
  let encO := encOption encUnary
  let encX := encPair enc encO
  let encY := encPair encX encO
  have hx := ComputableInPolyTime.fst enc encO
  have hy := ComputableInPolyTime.fst encX encO
  have hf := ComputableInPolyTime.fst encY encO
  have base := (hx.comp hy).comp hf
  have h0 := ((ComputableInPolyTime.snd enc encO).comp hy).comp hf
  have h1 := (ComputableInPolyTime.snd encX encO).comp hf
  have h2 := ComputableInPolyTime.snd encY encO
  unfold verifyConstraint
  apply (hread 0).bind_with
  apply ((hread 1).preprocess hx).bind_with
  apply ((hread 2).preprocess (hx.comp hy)).map_with
  apply computableInPolyTime_checkConstraintClaim (hp.comp base) (hQ.comp base)
    (hgates.comp base) (hr.comp base) (hz.comp base) (hsigns.comp base) (hclaim.comp base)
  intro j
  fin_cases j
  · exact h0
  · exact h1
  · exact h2

private theorem run_verifyConstraint (π : List Bool → Bool)
    (p Q : ℕ) (gates : List (Op × List ℕ)) (r z signs : List ℕ) (claim : ℕ)
    (read : Fin 3 → WordOracleComp Unit (Option ℕ)) :
    let law (j : Fin 3) := ((Prover.ofProof π).run (read j) ()).map Prod.fst
    ((Prover.ofProof π).run (verifyConstraint p Q gates r z signs claim read) ()).map Prod.fst =
      (law 0).bind fun x => (law 1).bind fun y =>
        (law 2).map (fun w => checkConstraintClaim p Q gates r z signs claim ![x, y, w]) := by
  simp only [verifyConstraint, Prover.run_bind, Prover.run_map, _root_.PMF.map_bind,
    _root_.PMF.bind_map, _root_.PMF.map_comp]
  rfl

private theorem three_eq {α : Type} (f : Fin 3 → α) : ![f 0, f 1, f 2] = f := by
  funext j
  fin_cases j <;> rfl

/-- If the terminal claim is wrong, acceptance has probability at most the sum of the
error bounds of the three correction queries. An explicitly rejected query contributes no error. -/
theorem acceptProb_verifyConstraint_of_wrong_claim (π : List Bool → Bool)
    {p Q L : ℕ} [NeZero p] (c : Circuit signature Q (3 * (L + 1)))
    (A : MvPolynomial (Fin L) (ZMod p)) (r z : Fin (Q + c.size) → ZMod p) (claim : ℕ)
    (hclaim : MvPolynomial.eval z (tableauConstraintPoly c A r) ≠ (claim : ZMod p))
    (read : Fin 3 → WordOracleComp Unit (Option ℕ)) (error : ENNReal)
    (hread : ∀ j : Fin 3, (((Prover.ofProof π).run (read j) ()).map Prod.fst).toOuterMeasure
      {o | ∃ y, o = some y ∧ y ≠ (MvPolynomial.eval (literalPoint c z j) A).val}
        ≤ error) :
    acceptProb (verifyConstraint p Q c.code.1 (List.ofFn fun i => (r i).val)
      (List.ofFn fun i => (z i).val)
      (List.ofFn fun j : Fin 3 => (c.outputs (SuccinctVerifier.signWire L j)).toNat)
      claim read) (Prover.ofProof π) ≤ 3 * error := by
  let correct (j : Fin 3) := MvPolynomial.eval (literalPoint c z j) A
  let bad (j : Fin 3) : Set (Option ℕ) := {o | ∃ v, o = some v ∧ v ≠ (correct j).val}
  let test (x y w : Option ℕ) := checkConstraintClaim p Q c.code.1
    (List.ofFn fun i => (r i).val) (List.ofFn fun i => (z i).val)
    (List.ofFn fun j : Fin 3 => (c.outputs (SuccinctVerifier.signWire L j)).toNat)
    claim ![x, y, w]
  let law (j : Fin 3) := ((Prover.ofProof π).run (read j) ()).map Prod.fst
  have hfail : ∀ x ∉ bad 0, ∀ y ∉ bad 1, ∀ w ∉ bad 2, test x y w = false := by
    intro x hx y hy w hw
    have good (j : Fin 3) (v : ℕ) (h : some v ∉ bad j) : v = (correct j).val := by
      by_contra hn
      exact h ⟨v, rfl, hn⟩
    cases x with
    | none => rfl
    | some vx =>
      cases y with
      | none => rfl
      | some vy =>
        cases w with
        | none => rfl
        | some vw =>
          rw [good 0 vx hx, good 1 vy hy, good 2 vw hw]
          unfold test
          rw [three_eq (fun j => some (correct j).val),
            checkConstraintClaim_eq c A r z claim (fun j => (correct j).val)
            (fun j => ZMod.natCast_zmod_val _)]
          exact decide_eq_false hclaim
  unfold acceptProb
  change ((((Prover.ofProof π).run _ ()).map Prod.fst) true) ≤ _
  rw [run_verifyConstraint, ← _root_.PMF.toOuterMeasure_apply_singleton]
  exact (probability_three_errors (law 0) (law 1) (law 2) _ _ _ test hfail).trans (by
    calc _ ≤ error + (error + error) := add_le_add (hread 0) (add_le_add (hread 1) (hread 2))
         _ = 3 * error := by ring)

/-- Three successful, correct local evaluations yield the same verdict as the ideal sumcheck
final comparison, including when the encoded claim is not the canonical representative. -/
theorem run_verifyConstraint_of_correct (π : List Bool → Bool) {p Q L : ℕ} [NeZero p]
    (c : Circuit signature Q (3 * (L + 1))) (A : MvPolynomial (Fin L) (ZMod p))
    (r z : Fin (Q + c.size) → ZMod p) (claim : ℕ)
    (read : Fin 3 → WordOracleComp Unit (Option ℕ))
    (hread : ∀ j : Fin 3, (Prover.ofProof π).run (read j) () = PMF.pure
      (some (MvPolynomial.eval (literalPoint c z j) A).val, ())) :
    (Prover.ofProof π).run (verifyConstraint p Q c.code.1 (List.ofFn fun i => (r i).val)
      (List.ofFn fun i => (z i).val)
      (List.ofFn fun j : Fin 3 => (c.outputs (SuccinctVerifier.signWire L j)).toNat)
      claim read) () =
      PMF.pure (decide (MvPolynomial.eval z (tableauConstraintPoly c A r) =
        (claim : ZMod p)), ()) := by
  let correct (j : Fin 3) := MvPolynomial.eval (literalPoint c z j) A
  simp only [verifyConstraint, Prover.run_bind, hread, PMF.pure_bind, Prover.run_map, PMF.pure_map,
    Prod.map_apply, id_eq]
  change PMF.pure (checkConstraintClaim _ _ _ _ _ _ _
    ![some (correct 0).val, some (correct 1).val, some (correct 2).val], ()) = _
  rw [three_eq (fun j => some (correct j).val),
    checkConstraintClaim_eq c A r z claim (fun j => (correct j).val)
    (fun j => ZMod.natCast_zmod_val _)]

end Cslib.Complexity.MIP
