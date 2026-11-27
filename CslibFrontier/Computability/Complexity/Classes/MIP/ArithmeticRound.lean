/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.MIP.Terminal
public import CslibFrontier.Computability.Complexity.Classes.MIP.Challenges
public import CslibFrontier.Computability.Complexity.Classes.MIP.SumcheckVerifier.Tableau
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Probability.PMF.BindFailure

/-!
# A bounded-coin word verifier for the arithmetized succinct tableau

The verifier tests a static transcript at random external and sumcheck challenges, then checks
the last claim against the three values corrected at the actual literal addresses. On an
unsatisfiable instance, the independent-vector ideal soundness bound, the three local
correction errors, and the fair-bit approximation bound add.
-/

public section

namespace Cslib.Complexity.MIP

open Probability Turing.MultiTapeTM Circuits Circuits.Boolean MvPolynomial
open Cslib.Interactive.Sumcheck
open scoped ENNReal

private noncomputable def verifyChallenges (x : Succinct3CNFInstance) (p precision : ℕ)
    (r z : List ℕ) : WordOracleComp Unit Bool := do
  let t ← SumcheckProof.verifyRounds p r x.sumcheckDegree p.size z
  if t.ok then checkTerminal x p precision r z t.claim else pure false

private theorem isOraclePPTOn_verifyChallenges {α : Type} {e : α ↪ List Bool}
    {x : α → Succinct3CNFInstance} {p precision : α → ℕ} {r z : α → List ℕ}
    (hx : ComputableInPolyTime x e encSuccinct3CNF) (hp : ComputableInPolyTime p e encUnary)
    (hprec : ComputableInPolyTime precision e encUnary)
    (hr : ComputableInPolyTime r e (encList encUnary))
    (hz : ComputableInPolyTime z e (encList encUnary)) :
    IsOraclePPTOn e encBool (fun a => verifyChallenges (x a) (p a) (precision a) (r a) (z a)) := by
  have pb := ComputableInPolyTime.unary_to_binary.comp hp
  have hfst := ComputableInPolyTime.fst e encWordState
  have hsnd := ComputableInPolyTime.snd e encWordState
  unfold verifyChallenges
  apply (SumcheckProof.isOraclePPTOn_verifyRounds pb (hr.reencodeList .unary_to_binary)
    (Succinct3CNFInstance.computableInPolyTime_sumcheckDegree.comp hx)
    (ComputableInPolyTime.binary_size.comp pb) (hz.reencodeList .unary_to_binary)).bind_with
  apply IsOraclePPTOn.cond (encWordState_ok_polyTime hsnd)
  · exact isOraclePPTOn_checkTerminal (hx.comp hfst) (hp.comp hfst) (hprec.comp hfst)
      (hr.comp hfst) (hz.comp hfst) (encWordState_claim_polyTime hsnd)
  · exact (ComputableInPolyTime.const false).isOraclePPTOn

/-- The arithmetic phase samples both vectors before running the static prefix-indexed
sumcheck verifier. The last comparison uses three independently corrected literal values. -/
noncomputable def arithmeticRound (x : Succinct3CNFInstance) (p precision : ℕ) :
    WordOracleComp Unit Bool := do
  let ⟨r, z⟩ ← ProbOracleComp.sample (sampleTableauChallenges x.sumcheckVars p precision)
  verifyChallenges x p precision r z

/-- The arithmetic phase is strict oracle polynomial time for unary modulus and precision. -/
theorem isOraclePPTOn_arithmeticRound {α : Type} {e : α ↪ List Bool}
    {x : α → Succinct3CNFInstance} {p precision : α → ℕ}
    (hx : ComputableInPolyTime x e encSuccinct3CNF) (hp : ComputableInPolyTime p e encUnary)
    (hprec : ComputableInPolyTime precision e encUnary) :
    IsOraclePPTOn e encBool (fun a => arithmeticRound (x a) (p a) (precision a)) := by
  unfold arithmeticRound
  have hs := isPPTOn_sampleTableauChallenges
    (Succinct3CNFInstance.computableInPolyTime_sumcheckVars.comp hx) hp hprec
  apply hs.isOraclePPTOn.bind_with
  apply isOraclePPTOn_verifyChallenges (hx.comp (.fst _ _)) (hp.comp (.fst _ _))
    (hprec.comp (.fst _ _)) ((ComputableInPolyTime.snd _ _).fst')
    ((ComputableInPolyTime.snd _ _).snd')

private theorem sumcheckVars_eq {x : Succinct3CNFInstance}
    (c : Circuit signature x.clauseBits (3 * (x.labelBits + 1))) (hc : c.code = x.code) :
    x.sumcheckVars = x.clauseBits + c.size := by
  rw [Succinct3CNFInstance.sumcheckVars, ← hc, Circuit.length_code_fst c]

private theorem sumcheckDegree_eq {x : Succinct3CNFInstance}
    (c : Circuit signature x.clauseBits (3 * (x.labelBits + 1))) (hc : c.code = x.code) :
    x.sumcheckDegree = 1 + 3 * c.size + 3 * (x.labelBits + 1) := by
  rw [Succinct3CNFInstance.sumcheckDegree, ← hc, Circuit.length_code_fst c]

/-- A proof with correct correction answers and consistent, accurate sumcheck rows at every
challenge is accepted on every fair-bit tape, including at zero sampling precision. -/
theorem run_arithmeticRound_of_honest (π : List Bool → Bool) {p : ℕ} [Fact p.Prime]
    {x : Succinct3CNFInstance} (c : Circuit signature x.clauseBits (3 * (x.labelBits + 1)))
    (hc : c.code = x.code) (A : MvPolynomial (Fin x.labelBits) (ZMod p))
    (hcorrect : ∀ y v, correctionAnswer π y v = some (eval y A).val)
    (ht : ∀ r z : Fin (x.clauseBits + c.size) → ZMod p,
      let t := SumcheckProof.transcript π p (List.ofFn fun i => (r i).val) x.sumcheckDegree p.size
        (List.ofFn fun i => (z i).val)
      t.ok = true ∧ (t.claim : ZMod p) = eval z (tableauConstraintPoly c A r)) (precision : ℕ) :
    (Prover.ofProof π).run (arithmeticRound x p precision) () = PMF.pure (true, ()) := by
  simp only [arithmeticRound, Prover.run_bind, Prover.run_sample, _root_.PMF.bind_map,
    sumcheckVars_eq c hc]
  apply bind_sampleTableauChallenges_of_forall
  intro r z
  let rv := List.ofFn fun i => (r i).val
  let zv := List.ofFn fun i => (z i).val
  let t := SumcheckProof.transcript π p rv x.sumcheckDegree p.size zv
  change (Prover.ofProof π).run (verifyChallenges x p precision rv zv) () = _
  obtain ⟨hok, hclaim⟩ := ht r z
  simp only [verifyChallenges, Prover.run_bind, SumcheckProof.run_verifyRounds,
    _root_.PMF.pure_bind]
  change (Prover.ofProof π).run (if t.ok then checkTerminal x p precision rv zv t.claim
    else pure false) () = PMF.pure (true, ())
  rw [show t.ok = true from hok, ite_eq_left rfl]
  have h := run_checkTerminal_of_correct π c hc A r z t.claim precision (fun j v => hcorrect _ v)
  simpa only [show eval z (tableauConstraintPoly c A r) = (t.claim : ZMod p) from hclaim.symm,
    decide_true] using h

/-- On an unsatisfiable succinct formula, the arithmetic phase can accept through a successful
ideal transcript, an erroneous local correction, or the error of the bounded challenge sampler. -/
theorem acceptProb_arithmeticRound_le (π : List Bool → Bool) {p : ℕ} [Fact p.Prime]
    {x : Succinct3CNFInstance} (c : Circuit signature x.clauseBits (3 * (x.labelBits + 1)))
    (hc : c.code = x.code) (hunsat : ¬ (SuccinctVerifier.toCNF c).Satisfiable)
    {A : MvPolynomial (Fin x.labelBits) (ZMod p)} (hA : A ∈ restrictDegree _ _ 1)
    (hp : x.labelBits + 1 < p) (precision : ℕ) :
    acceptProb (arithmeticRound x p precision) (Prover.ofProof π) ≤
      (x.sumcheckVars : ℝ≥0∞) * (x.sumcheckDegree + 1) / p +
        3 * ((x.labelBits + 1 : ℝ≥0∞) * hammingDist (proofPoint π p) (fun y => eval y A) /
          p ^ x.labelBits + 1 / 2 ^ precision) + (1 / 2 ^ precision + 1 / 2 ^ precision) := by
  let R := x.clauseBits + c.size
  let ν := PMF.uniformOfFintype ((Fin R → ZMod p) × (Fin R → ZMod p))
  let words (v : Fin R → ZMod p) := List.ofFn fun i => (v i).val
  let encode (v : (Fin R → ZMod p) × (Fin R → ZMod p)) := (words v.1, words v.2)
  let kernel (v : List ℕ × List ℕ) :=
    ((Prover.ofProof π).run (verifyChallenges x p precision v.1 v.2) ()).map Prod.fst
  let bad := {rz : (Fin R → ZMod p) × (Fin R → ZMod p) |
    let t := SumcheckProof.transcript π p (words rz.1) x.sumcheckDegree p.size (words rz.2)
    t.ok = true ∧ (t.claim : ZMod p) = eval rz.2 (tableauConstraintPoly c A rz.1)}
  let ε : ENNReal := (x.labelBits + 1 : ℝ≥0∞) *
    hammingDist (proofPoint π p) (fun y => eval y A) / p ^ x.labelBits + 1 / 2 ^ precision
  have htest := SumcheckProof.transcript_sound_of_unsatisfiable c hunsat hA
    (sumcheckDegree_eq c hc).ge π p.size
  have hbad : ν.toOuterMeasure bad ≤ (R : ℝ≥0∞) * (x.sumcheckDegree + 1) / p := htest
  have hideal : ((ν.map encode).bind kernel).toOuterMeasure {true} ≤
      ν.toOuterMeasure bad + 3 * ε := by
    rw [_root_.PMF.bind_map]
    apply Probability.PMF.toOuterMeasure_bind_le_add _ _ bad
    rintro ⟨r, z⟩ _ hg
    let rv := words r
    let zv := words z
    let t := SumcheckProof.transcript π p rv x.sumcheckDegree p.size zv
    change (((Prover.ofProof π).run (verifyChallenges x p precision rv zv) ()).map
      Prod.fst).toOuterMeasure {true} ≤ _
    rw [_root_.PMF.toOuterMeasure_apply_singleton]
    simp only [verifyChallenges, Prover.run_bind, SumcheckProof.run_verifyRounds,
      _root_.PMF.pure_bind]
    change (((Prover.ofProof π).run (if t.ok then _ else pure false) ()).map Prod.fst true) ≤ _
    cases hok : t.ok with
    | false => simp
    | true =>
      simp only [↓reduceIte]
      have hn : eval z (tableauConstraintPoly c A r) ≠ (t.claim : ZMod p) :=
        fun he => hg ⟨hok, he.symm⟩
      exact acceptProb_checkTerminal_of_wrong_claim π c hc A r z t.claim precision hp
        (Code.isMultilinear_eval_of_mem_restrictDegree hA) hn
  have hsample := (closeTo_sampleTableauChallenges R p precision).bind_left kernel {true}
  have hrun : acceptProb (arithmeticRound x p precision) (Prover.ofProof π) =
      ((ProbComp.eval (sampleTableauChallenges R p precision)).bind kernel).toOuterMeasure
        {true} := by
    simp only [acceptProb, arithmeticRound, Prover.run_bind, Prover.run_sample,
      _root_.PMF.toOuterMeasure_apply_singleton, _root_.PMF.map_bind, _root_.PMF.bind_map,
      sumcheckVars_eq c hc]
    rfl
  rw [hrun, sumcheckVars_eq c hc]
  exact hsample.trans (add_le_add (hideal.trans (add_le_add hbad le_rfl)) le_rfl)

end Cslib.Complexity.MIP
