/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.LineProof.SemanticDerivation
public import CslibFrontier.Logics.Propositional.Resolution.Proof

/-!
# Resolution refutations as semantic refutations

Reversing a propositional resolution refutation (`Cslib.Logic.PL.CNF.IsProof`) and mapping each
clause to its set of satisfying assignments yields a semantic refutation
(`Cslib.Logic.PL.CNF.IsProof.isSemanticRefutation`) of the same length in the sense of
[Krajíček, Definition 4.1][Krajicek1997].

## Main results

* `Cslib.Logic.PL.CNF.IsProof.isSemanticRefutation`: resolution refutations induce semantic
  refutations of the same length.

## References

* [J. Krajíček, *Interpolation theorems, lower bounds for proof systems, and independence results
  for bounded arithmetic*][Krajicek1997]
* [J. A. Robinson, *A machine-oriented logic based on the resolution principle*][Robinson1965]
-/

public section

namespace Cslib.Logic.PL

variable {V : Type*} [DecidableEq V]

/-- **Resolution refutations are semantic refutations** [Krajíček, Section 4][Krajicek1997]:
reading a resolution refutation from its first line and sending each clause to its satisfying
assignments gives a semantic refutation with the same number of lines. -/
theorem CNF.IsProof.isSemanticRefutation {φ : CNF V} {ls : List (Clause V)}
    {init : Set (Set (V → Bool))} (h : φ.IsProof ls)
    (hφ : ∀ c ∈ φ, {σ | c.eval σ = true} ∈ init) (hnil : [] ∈ ls) :
    IsSemanticRefutation init fun j : Fin ls.reverse.length => {σ | ls.reverse[j].eval σ = true} :=
  (CNF.isProof_iff_lineProof.1 h).toSemanticRefutation hφ
    (fun _ hr => CNF.resolutionRules_premises_length_le hr)
    (fun _ hr _ hp => CNF.resolutionRules_sound hr hp) hnil (by simp)

end Cslib.Logic.PL
