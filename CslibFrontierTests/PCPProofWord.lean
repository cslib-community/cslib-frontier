/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Classes.MIP.SumcheckProof

/-! A single nonzero proof bit tests bit order, address framing, and zero-width access. -/

namespace CslibFrontierTests.PCPProofWord

open Cslib.Complexity Turing.MultiTapeTM

private def π (q : List Bool) : Bool := q == encPair encBits encNat ([], 1)

example :
    (Prover.ofProof π).run (ProofWord.readValue [] 3) () = PMF.pure (2, ()) ∧
    (Prover.ofProof π).run (ProofWord.readValue [false] 3) () = PMF.pure (0, ()) ∧
    (Prover.ofProof π).run (ProofWord.readValue [] 0) () = PMF.pure (0, ()) := by
  simp only [ProofWord.run_readValue, show ProofWord.value π [] 3 = 2 by decide,
    show ProofWord.value π [false] 3 = 0 by decide, show ProofWord.value π [] 0 = 0 by decide,
    and_self]

-- An identical concatenation with a different division into external and earlier challenges
-- must select a different polynomial.
example : MIP.SumcheckProof.coefficientKey ⟨[1], [2], 0⟩ ≠
    MIP.SumcheckProof.coefficientKey ⟨[1, 2], [], 0⟩ := by decide

-- A three-bit all-ones row supplies 7 as its constant coefficient, or 2 modulo 5.
example : MIP.SumcheckProof.rowPolynomial (fun _ => true) 5 [] [] 0 3 =
    Polynomial.C (2 : ZMod 5) := by
  change Polynomial.ofCoeffList ([((7 : ℕ) : ZMod 5)]) = _
  simp [Polynomial.ofCoeffList_cons, show (7 : ZMod 5) = 2 by decide]

end CslibFrontierTests.PCPProofWord
