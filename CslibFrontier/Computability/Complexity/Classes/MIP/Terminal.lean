/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.MIP.CorrectionProbability
public import CslibFrontier.Computability.Complexity.Classes.MIP.ConstraintCheck
public import CslibFrontier.Computability.Complexity.Classes.MIP.SuccinctDecoder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# Checking the terminal sumcheck claim on a succinct decoder

The verifier reads the three variable addresses from a raw circuit description. Each address
selects field coordinates at the terminal sumcheck point and receives its own sampled line
correction before the arithmetic comparison.

## Main definitions

* `checkTerminal` performs this oracle computation on a raw succinct 3-CNF instance.

## Main results

* `isOraclePPTOn_checkTerminal` gives a strict polynomial-time implementation.
* `run_checkTerminal_of_correct` gives the ideal verdict when all directions correct exactly.
* `acceptProb_checkTerminal_of_wrong_claim` bounds false acceptance using the distance from a
  multilinear table and the finite precision of the direction sampler.
-/

public section

namespace Cslib.Complexity.MIP

open Cslib.Code Cslib.Circuits Cslib.Circuits.Boolean Cslib.Probability Turing.MultiTapeTM
open scoped ENNReal

/-- Check the claimed constraint value, correcting the assignment value at each of the three
literal addresses selected by the raw decoder. -/
noncomputable def checkTerminal (x : Succinct3CNFInstance) (p precision : ℕ)
    (r z : List ℕ) (claim : ℕ) : WordOracleComp Unit Bool :=
  verifyConstraint p x.clauseBits x.code.1 r z x.signWires claim fun j =>
    correctPoint p x.labelBits precision ((x.addressWires j).map fun w => z.getD w 0)

/-- The corrected literal check is strictly polynomial-time given the raw succinct decoder,
unary field size, precision and coordinate words, and a binary claim. -/
theorem isOraclePPTOn_checkTerminal {α : Type} {enc : α ↪ List Bool}
    {x : α → Succinct3CNFInstance} {p precision claim : α → ℕ} {r z : α → List ℕ}
    (hx : ComputableInPolyTime x enc encSuccinct3CNF)
    (hp : ComputableInPolyTime p enc encUnary) (hprec : ComputableInPolyTime precision enc encUnary)
    (hr : ComputableInPolyTime r enc (encList encUnary))
    (hz : ComputableInPolyTime z enc (encList encUnary))
    (hclaim : ComputableInPolyTime claim enc encNat) :
    IsOraclePPTOn enc encBool (fun a => checkTerminal (x a) (p a) (precision a) (r a) (z a)
      (claim a)) := by
  apply isOraclePPTOn_verifyConstraint (ComputableInPolyTime.unary_to_binary.comp hp)
    (ComputableInPolyTime.unary_to_binary.comp (encSuccinct3CNF_clauseBits_polyTime hx))
    ((ComputableInPolyTime.fst _ _).comp (encSuccinct3CNF_code_polyTime hx))
    (hr.reencodeList .unary_to_binary) (hz.reencodeList .unary_to_binary)
    (Succinct3CNFInstance.computableInPolyTime_signWires.comp hx) hclaim
  intro j
  apply isOraclePPTOn_correctPoint hp (encSuccinct3CNF_labelBits_polyTime hx) hprec
  apply ComputableInPolyTime.mapWithInput
    (Succinct3CNFInstance.computableInPolyTime_addressWires hx (.const j.val))
  exact ComputableInPolyTime.listGetD_binary 0 (hz.comp (ComputableInPolyTime.fst _ _))
    (ComputableInPolyTime.snd _ _)

variable (π : List Bool → Bool) {p : ℕ} [Fact p.Prime] {x : Succinct3CNFInstance}
    (c : Circuit signature x.clauseBits (3 * (x.labelBits + 1))) (hc : c.code = x.code)
    (A : MvPolynomial (Fin x.labelBits) (ZMod p))
    (r z : Fin (x.clauseBits + c.size) → ZMod p) (claim precision : ℕ)

include hc

omit [Fact p.Prime] in
private theorem addressPoint_eq (j : Fin 3) :
    (x.addressWires j).map (fun w => (List.ofFn fun i => (z i).val).getD w 0) =
      List.ofFn fun i => (literalPoint c z j i).val := by
  rw [Succinct3CNFInstance.addressWires_eq c hc, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  exact List.getD_ofFn _ ⟨_, Wire.toNat_lt _⟩ 0

/-- If every direction at each addressed literal gives the correct field value, the terminal
check returns exactly the truth of the claimed polynomial identity. -/
theorem run_checkTerminal_of_correct
    (hall : ∀ j v, correctionAnswer π (literalPoint c z j) v =
      some (MvPolynomial.eval (literalPoint c z j) A).val) :
    (Prover.ofProof π).run (checkTerminal x p precision (List.ofFn fun i => (r i).val)
      (List.ofFn fun i => (z i).val) claim) () =
        PMF.pure (decide (MvPolynomial.eval z (tableauConstraintPoly c A r) = (claim : ZMod p)),
          ()) := by
  unfold checkTerminal
  rw [Succinct3CNFInstance.signWires_eq c hc, ← hc]
  apply run_verifyConstraint_of_correct
  intro j
  rw [addressPoint_eq c hc z j]
  exact run_correctPoint_of_forall π _ _ (hall j) _

/-- For any fixed bit proof, accepting a false claim costs at most three correction errors.
Each error accounts for a multilinear disagreement and the finite sampling precision. -/
theorem acceptProb_checkTerminal_of_wrong_claim (hp : x.labelBits + 1 < p)
    (hm : IsMultilinear (fun y => MvPolynomial.eval y A))
    (hclaim : MvPolynomial.eval z (tableauConstraintPoly c A r) ≠ (claim : ZMod p)) :
    acceptProb (checkTerminal x p precision (List.ofFn fun i => (r i).val)
      (List.ofFn fun i => (z i).val) claim) (Prover.ofProof π) ≤
      3 * ((x.labelBits + 1 : ℝ≥0∞) *
        hammingDist (proofPoint π p) (fun y => MvPolynomial.eval y A) / p ^ x.labelBits +
        1 / 2 ^ precision) := by
  unfold checkTerminal
  rw [Succinct3CNFInstance.signWires_eq c hc, ← hc]
  apply acceptProb_verifyConstraint_of_wrong_claim π c A r z claim hclaim
  intro j
  rw [addressPoint_eq c hc z j]
  exact correctPoint_wrong_le π hp hm (literalPoint c z j) precision

end Cslib.Complexity.MIP
