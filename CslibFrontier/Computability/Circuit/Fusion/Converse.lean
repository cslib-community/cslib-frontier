/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Fusion.CertificateCircuit
public import CslibFrontier.Computability.Circuit.Fusion.Conondeterministic
public import CslibFrontier.Computability.Circuit.Boolean.Conondeterministic

/-!
# Universal verifiers from semi-ultrafilter covers

A cover of length `t` yields a native universal verifier with `2t` auxiliary bits and exactly
`3t` binary AND gates. The verifier rejects precisely consistent compressed certificates.
Intersection labels are computed once and shared, so every expanded certificate preserves pairs.
True primary inputs have no such certificate by the cover property; false inputs supply their
point-membership certificate. The construction includes empty covers and constant functions.

## Main results

* `Cslib.Circuits.Fusion.PairCover.exists_forallGuess`: the universal verifier with exact cost.
* `Cslib.Circuits.Fusion.conondeterministicAndComplexity_bounds`: minimum universal-verifier
  AND complexity lies between semi-ultrafilter cover complexity and three times that measure.

## References

* [B. P. Cavalar and I. C. Oliveira, *Boolean Circuit Complexity and Two-Dimensional Cover
  Problems*][CavalarOliveira2025], arXiv:2503.14117v1, Theorem 45, printed p. 22, credited there
  to Karchmer, states the characterization with an unspecified constant. The explicit factor
  three and the `2t` auxiliary-bit bound are an original sharpening of this library's
  certificate construction; no claim of optimality or publication priority is made.
-/

public section

namespace Cslib.Circuits.Fusion

open Cslib Boolean PairCertificate

private theorem exists_primary_literal_formula {n a : ℕ} (l : Fin (n + n)) :
    ∃ F : Formula Monotone.signature ((n + a) + (n + a)),
      (∀ z : BitString (n + a), F.eval Monotone.interpretation (AltFormula.literals z) = true ↔
        AltFormula.literals (fun i => z (Fin.castAdd a i)) l = true) ∧
      F.cost Monotone.andCost = 0 := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) l
  · exact ⟨.input (Fin.castAdd _ (Fin.castAdd a i)),
      fun _ => by simp only [Formula.eval_input, AltFormula.literals, Fin.append_left], rfl⟩
  · exact ⟨.input (Fin.natAdd _ (Fin.castAdd a i)),
      fun _ => by simp only [Formula.eval_input, AltFormula.literals, Fin.append_right], rfl⟩

private theorem exists_auxiliary_literal_formula {n a : ℕ} (i : Fin a) (b : Bool) :
    ∃ F : Formula Monotone.signature ((n + a) + (n + a)),
      (∀ z : BitString (n + a), F.eval Monotone.interpretation (AltFormula.literals z) = true ↔
        z (Fin.natAdd n i) = b) ∧ F.cost Monotone.andCost = 0 := by
  cases b
  · exact ⟨.input (Fin.natAdd _ (Fin.natAdd n i)),
      fun _ => by simp only [Formula.eval_input, AltFormula.literals, Fin.append_right,
        Bool.not_eq_true_eq_eq_false], rfl⟩
  · exact ⟨.input (Fin.castAdd _ (Fin.natAdd n i)),
      fun _ => by simp only [Formula.eval_input, AltFormula.literals, Fin.append_left], rfl⟩

/-- A cover of length `t` yields a verifier with `2t` auxiliary bits and exactly `3t` AND gates.
Constants, OR gates and supplied positive/negative literals are free. No nonempty-target,
nonempty-complement or positive-length assumption is imposed. -/
theorem PairCover.exists_forallGuess {n : ℕ} (f : BooleanFunction n)
    (cover : PairCover {x | f x = true} (fun i => {x | AltFormula.literals x i = true})
      Semifilter.IsUltra) :
    ∃ g : BooleanFunction (n + compactSize cover.pairs),
      ∃ c : Circuit Monotone.signature
        ((n + compactSize cover.pairs) + (n + compactSize cover.pairs)) 1,
        forallGuess g = f ∧ c.ComputesFrom Monotone.interpretation (single g)
          AltFormula.literals ∧ c.program.cost Monotone.andCost = 3 * cover.pairs.length := by
  classical
  let sources : Fin (n + n) → Set ↥({x | f x = true}ᶜ) :=
    fun i => Subtype.val ⁻¹' {x : BitString n | AltFormula.literals x i = true}
  obtain ⟨c, hc, cc⟩ := PairCertificate.exists_circuit cover.pairs sources AltFormula.literals
    (fun z : BitString (n + compactSize cover.pairs) =>
      AltFormula.literals (fun i => z (Fin.castAdd _ i)))
    (fun z i => z (Fin.natAdd n i)) exists_primary_literal_formula
    exists_auxiliary_literal_formula
  let g : BooleanFunction (n + compactSize cover.pairs) :=
    fun z => c.eval Monotone.interpretation (AltFormula.literals z) 0
  have hspec (x : BitString n) (y : BitString (compactSize cover.pairs)) :
      g (Fin.append x y) = true ↔
        compactInvalid cover.pairs sources (AltFormula.literals x) y := by
    simpa only [g, Fin.append_left, Fin.append_right] using hc (Fin.append x y)
  refine ⟨g, c, ?_, fun _ => funext fun i => Subsingleton.elim i 0 ▸ rfl, cc⟩
  funext x
  apply Bool.eq_iff_iff.mpr
  simp only [forallGuess, decide_eq_true_eq]
  constructor
  · intro h
    by_contra hx
    let u : ↥({x | f x = true}ᶜ) := ⟨x, hx⟩
    have hvalid := not_invalid_pointLabels cover.pairs sources (AltFormula.literals x) u
      (fun _ h => h)
    have hbad := (invalid_expandLabels_iff cover.pairs sources (AltFormula.literals x)
      (compactPointLabels cover.pairs u)).mpr
        ((hspec x (compactPointLabels cover.pairs u)).mp (h _))
    rw [expandLabels_compactPointLabels] at hbad
    exact hvalid hbad
  · intro hx y
    apply (hspec x y).mpr
    apply (invalid_expandLabels_iff cover.pairs sources (AltFormula.literals x) y).mp
    simpa only [Set.mem_ofPred_eq, Bool.decide_eq_true] using
      (cover.invalid_or_breaksPair ⟨x, hx⟩ (expandLabels cover.pairs y)).resolve_right
        (not_breaksPair_expandLabels cover.pairs y)

/-- The semi-ultrafilter bound applies after minimizing over all auxiliary counts and verifiers. -/
theorem pairCoverComplexity_le_econondeterministicAndComplexity {n : ℕ}
    (f : BooleanFunction n) :
    pairCoverComplexity {x | f x = true} (fun i => {x | AltFormula.literals x i = true})
      Semifilter.IsUltra ≤ econondeterministicAndComplexity f :=
  le_econondeterministicAndComplexity_iff.mpr fun _ g hg c hc =>
    hg ▸ pairCoverComplexity_forallGuess_le_cost g c hc

/-- A semi-ultrafilter cover gives a universal verifier at most three times as costly. -/
theorem econondeterministicAndComplexity_le_pairCoverComplexity {n : ℕ}
    (f : BooleanFunction n) :
    econondeterministicAndComplexity f ≤
      3 * pairCoverComplexity {x | f x = true}
        (fun i => {x | AltFormula.literals x i = true}) Semifilter.IsUltra := by
  rw [pairCoverComplexity, ENat.mul_iInf_of_ne (by decide : (3 : ℕ∞) ≠ 0)]
  refine le_iInf fun cover => ?_
  obtain ⟨g, c, hg, hc, hcost⟩ := cover.exists_forallGuess f
  simpa only [hcost, Nat.cast_mul, Nat.cast_ofNat] using
    econondeterministicAndComplexity_le_cost g hg c hc

/-- **Linear semi-ultrafilter characterization of conondeterministic AND complexity**,
with explicit factors one and three and unrestricted finite auxiliary input counts. -/
theorem conondeterministicAndComplexity_bounds {n : ℕ} (f : BooleanFunction n) :
    let ρ := pairCoverComplexity {x | f x = true}
      (fun i => {x | AltFormula.literals x i = true}) Semifilter.IsUltra
    ρ ≤ econondeterministicAndComplexity f ∧ econondeterministicAndComplexity f ≤ 3 * ρ :=
  ⟨pairCoverComplexity_le_econondeterministicAndComplexity f,
    econondeterministicAndComplexity_le_pairCoverComplexity f⟩

end Cslib.Circuits.Fusion

