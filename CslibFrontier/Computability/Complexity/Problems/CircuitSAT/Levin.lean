/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CircuitSAT
public import CslibFrontier.Computability.Complexity.Problems.SAT.Relation
public import CslibFrontier.Computability.Complexity.Reduction.Levin
import CslibFrontier.Computability.Complexity.CookLevin.Levin
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.List.GetD

/-!
# The circuit satisfaction relation is PC-complete

`Cslib.Complexity.CircuitSAT.npRelation` is the NP relation of circuit satisfiability: a witness
for a De Morgan circuit with `n` inputs, encoded by `encCircuit 1`, is an input `z` on which it
outputs true, padded by arbitrary bits to the length of the encoded circuit. This is Goldreich's
relation $R_{\mathrm{CSAT}}=\{(C,z) : C(z)=1\}$ in the library's convention for NP relations,
whose certificates have exactly a prescribed polynomial length; the first `n` bits of a witness
are the source's `z`.

`Cslib.Complexity.SAT.toCircuitLevinReduction` upgrades the reduction `SAT.toCircuit` from `SAT`
to `CircuitSAT` to a Levin reduction. The circuit of a formula has one input for each literal
occurrence and reads each variable at the input of its first occurrence, exactly as the
certificates of `SAT.verifier` do, so both witness maps keep the first `n` bits of the witness and
pad with `false`. With the witness-preserving Cook–Levin theorem `CookLevin.SAT_levinHard`, the
relation is Levin-hard (`Cslib.Complexity.CircuitSAT_levinHard`): every NP relation, over every
encoded instance type, Levin-reduces to it.

## Main definitions

* `Cslib.Complexity.CircuitSAT.npRelation`: the NP relation of `CircuitSAT`.
* `Cslib.Complexity.SAT.toCircuitLevinReduction`: the Levin reduction from `SAT`.

## Main results

* `Cslib.Complexity.CircuitSAT.language_npRelation`: the language of the relation is `CircuitSAT`.
* `Cslib.Complexity.CircuitSAT_levinHard`: Goldreich, Theorem 2.21, search version.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*][Goldreich2008], Theorem 2.21
  (draft `r1.pdf` of 30 December 2006, PDF p. 103, printed p. 78).
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Circuits Circuits.Boolean Turing.MultiTapeTM ComputableInPolyTime

namespace CircuitSAT

/-- The NP relation of `CircuitSAT`: certificates as long as the encoded circuit, checked by
`Cslib.Complexity.CircuitSAT.verifier`, which evaluates the circuit on their first bits. -/
@[expose]
noncomputable def npRelation : NPRelation (encCircuit 1) :=
  ⟨Polynomial.X, verifier, computableInPolyTime_verifier⟩

theorem isWitness_npRelation_iff {c : Σ n, Circuit signature n 1} {w : List Bool} :
    npRelation.IsWitness c w ↔ w.length = (encCircuit 1 c).length ∧ verifier (c, w) = true := by
  simp [NPRelation.isWitness_iff, npRelation]

/-- The language of the NP relation of `CircuitSAT` is `CircuitSAT`. -/
theorem language_npRelation : npRelation.language = CircuitSAT :=
  npRelation.language_eq_of_isVerifier isVerifier

end CircuitSAT

namespace SAT

/-- The `SAT` verifier reads a certificate only below the number of literal occurrences. -/
private theorem verifier_congr {φ : CNF ℕ} {u u' : List Bool}
    (h : ∀ i < φ.vars.length, u.getD i false = u'.getD i false) :
    verifier (φ, u) = verifier (φ, u') := by
  simp only [verifier]
  exact CNF.eval_congr fun v hv => h _ (List.idxOf_lt_length_iff.2 hv)

/-- **The circuit of a formula verifies the formula's certificates**: on any word, the
`CircuitSAT` verifier for `toCircuit φ` agrees with the `SAT` verifier for `φ`. -/
theorem verifier_toCircuit (φ : CNF ℕ) (u : List Bool) :
    CircuitSAT.verifier (toCircuit φ, u) = verifier (φ, u) := by
  rw [CircuitSAT.verifier, eval_toCircuit]
  exact verifier_congr fun i hi => List.getD_ofFn_of_lt _ hi _

private theorem length_rightpad_take {n L : ℕ} (h : n ≤ L) (w : List Bool) :
    ((w.take n).rightpad L false).length = L := by
  simp only [List.rightpad, List.length_append, List.length_replicate, List.length_take]
  omega

/-- Keeping the first `n` bits and padding with `false` keeps the bits below `n`. -/
private theorem getD_rightpad_take {n L i : ℕ} (hi : i < n) (w : List Bool) :
    ((w.take n).rightpad L false).getD i false = w.getD i false := by
  simp only [List.rightpad, List.getD_eq_getElem?_getD, List.getElem?_append,
    List.getElem?_take, List.length_take, List.getElem?_replicate, hi, ite_true]
  by_cases hw : i < w.length
  · simp [hw, Nat.lt_min.2 ⟨hi, hw⟩]
  · simp only [hw, Nat.lt_min, and_false, ite_false, List.getElem?_eq_none (Nat.le_of_not_lt hw)]
    split <;> rfl

/-- The forward witness map: the first `n` bits of a certificate for `φ`, padded to the length of
the encoded circuit. -/
@[expose]
def toCircuitWitness (x : CNF ℕ × List Bool) : List Bool :=
  (x.2.take x.1.vars.length).rightpad (encCircuit 1 (toCircuit x.1)).length false

/-- The backward witness map: the first `n` bits of a certificate for `toCircuit φ`, padded to
the length of the encoded formula. -/
@[expose]
def ofCircuitWitness (x : CNF ℕ × List Bool) : List Bool :=
  padCertificate x.1 (x.2.take x.1.vars.length)

theorem isWitness_toCircuitWitness {φ : CNF ℕ} {w : List Bool}
    (h : npRelation.IsWitness φ w) :
    CircuitSAT.npRelation.IsWitness (toCircuit φ) (toCircuitWitness (φ, w)) := by
  refine CircuitSAT.isWitness_npRelation_iff.2
    ⟨length_rightpad_take (le_length_encCircuit (toCircuit φ)) w, ?_⟩
  rw [verifier_toCircuit, toCircuitWitness, verifier_congr fun i hi => getD_rightpad_take hi w]
  exact h.2

theorem isWitness_ofCircuitWitness {φ : CNF ℕ} {w : List Bool}
    (h : CircuitSAT.npRelation.IsWitness (toCircuit φ) w) :
    npRelation.IsWitness φ (ofCircuitWitness (φ, w)) := by
  refine isWitness_npRelation_iff.2 ⟨length_rightpad_take (length_vars_le φ) w, ?_⟩
  rw [ofCircuitWitness, padCertificate, verifier_congr fun i hi => getD_rightpad_take hi w,
    ← verifier_toCircuit]
  exact (CircuitSAT.isWitness_npRelation_iff.1 h).2

/-- The forward witness map is polynomial-time. -/
theorem computableInPolyTime_toCircuitWitness :
    ComputableInPolyTime toCircuitWitness (encPair encCNF encBits) encBits := by
  have := computableInPolyTime_vars
  have hcirc := (encoding_comp computableInPolyTime_toCircuit).comp (fst encCNF encBits)
  unfold toCircuitWitness List.rightpad
  exact (bitsTakeWithInput (snd _ _) (by fun_prop)).bitsAppend
    ((bitsReplicate false).comp (by fun_prop))

/-- The backward witness map is polynomial-time. -/
theorem computableInPolyTime_ofCircuitWitness :
    ComputableInPolyTime ofCircuitWitness (encPair encCNF encBits) encBits := by
  fun_prop [ofCircuitWitness]

/-- **SAT Levin-reduces to circuit satisfiability.** The instance map is `toCircuit`; both
witness maps keep the bits read for the literal occurrences and pad with `false`. -/
@[expose]
noncomputable def toCircuitLevinReduction : LevinReduction npRelation CircuitSAT.npRelation where
  toFun := toCircuit
  forwardWitness := toCircuitWitness
  backwardWitness := ofCircuitWitness
  computableInPolyTime_toFun := computableInPolyTime_toCircuit
  computableInPolyTime_forwardWitness := computableInPolyTime_toCircuitWitness
  computableInPolyTime_backwardWitness := computableInPolyTime_ofCircuitWitness
  isWitness_forwardWitness _ _ := isWitness_toCircuitWitness
  isWitness_backwardWitness _ _ := isWitness_ofCircuitWitness

end SAT

/-- **The circuit satisfaction relation is PC-complete** [Goldreich, Theorem 2.21][Goldreich2008],
search version: every NP relation, over every encoded instance type, Levin-reduces to
`CircuitSAT.npRelation`, which is itself an NP relation. The decision version is
`CircuitSAT_npComplete`.

Hardness is for the library's Levin reductions, which carry a forward witness map besides
Goldreich's backward one (Definition 2.12), and for NP relations with certificates of exactly a
prescribed polynomial length; a circuit's witnesses are its satisfying inputs padded to the
length of the encoded circuit. -/
theorem CircuitSAT_levinHard : LevinHard CircuitSAT.npRelation :=
  CookLevin.SAT_levinHard.trans SAT.toCircuitLevinReduction

end Cslib.Complexity
