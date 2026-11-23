/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomFunction.PrefixFree
public import CslibFrontier.Crypto.Computational.PseudorandomFunction.PrefixFreePair
public import CslibFrontier.Crypto.Primitives.UHF.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.PPT.Composition

/-!
# A prefix-free oracle wrapper for collision guesses

This is the two-query wrapper in the proof of [BonehShoup2023], v0.6, Theorem 7.3
(printed pp. 258–259). It runs the collision guesser on the public unary parameter, extends
each accepted word by the same full block, and checks equality of the two oracle replies.
The wrapper always extends an accepted pair. Its reply reads are capped at the declared width.

The certificate uses the library's domain-relative prefix condition. Definition 4.5
(printed p. 152) also requires every query to be nonempty and in the PRF input domain. Applying
the wrapper to that game requires showing that the extended messages fit the oracle domain.
Theorem 7.3 provides this room by giving the PRF domain one extra block of capacity.

## Main definitions

* `Cslib.Crypto.UHF.prefixFreeCollisionReduction`: compare oracle replies on extended queries.

## Main results

* `Cslib.Crypto.UHF.isPrefixFreeOraclePPT_prefixFreeCollisionReduction`: the wrapper for a strict
  PPT guesser is strict oracle PPT and makes prefix-incomparable queries.
-/

public section

namespace Cslib.Crypto.UHF

open Probability Turing.MultiTapeTM

/-- Reject invalid and repeated guesses. On an accepted pair, append the same separating block
to both words and compare the two oracle replies up to the declared reply width. -/
@[expose] def prefixFreeCollisionReduction (width outLen : ℕ → ℕ)
    (valid : ℕ → List Bool → Bool) (guessPair : ℕ × ℕ → ProbComp (CollisionGuess (List Bool))) :
    OracleDistinguisher :=
  fun n _ => do
    let guess ← ProbOracleComp.sample (guessPair (n, n))
    if valid n guess.first && valid n guess.second && decide (guess.first ≠ guess.second) then
      let block := PRF.separatingWordBlock (width n) guess.first guess.second
      let left ← List.take (outLen n) <$> ProbOracleComp.query ((), guess.first ++ block)
      let right ← List.take (outLen n) <$> ProbOracleComp.query ((), guess.second ++ block)
      return decide (left = right)
    else
      return false

private theorem isOraclePPT_prefixFreeCollisionReduction {width outLen : ℕ → ℕ}
    {valid : ℕ → List Bool → Bool} {guessPair : ℕ × ℕ → ProbComp (CollisionGuess (List Bool))}
    (hwidth : ComputableInPolyTime width encUnary encUnary)
    (hout : ComputableInPolyTime outLen encUnary encUnary)
    (hvalid : ComputableInPolyTime (fun p => valid p.1 p.2) (encPair encUnary encBits) encBool)
    (hguess : IsPPTOn (encPair encUnary encUnary) (encCollisionGuess encBits) guessPair) :
    IsOraclePPT encBool (prefixFreeCollisionReduction width outLen valid guessPair) := by
  let encGuess := encCollisionGuess encBits
  let encInput := encPair encUnary encBits
  let encStage := encPair encInput encGuess
  have hn := ComputableInPolyTime.fst encUnary encBits
  have hrun := hguess.preprocess (hn.prod hn)
  have hn' := hn.comp (ComputableInPolyTime.fst encInput encGuess)
  have hl := encCollisionGuess_first_polyTime encBits (ComputableInPolyTime.snd encInput encGuess)
  have hr := encCollisionGuess_second_polyTime encBits (ComputableInPolyTime.snd encInput encGuess)
  have hguard := ComputableInPolyTime.bool_and.comp
    ((ComputableInPolyTime.bool_and.comp
      ((hvalid.comp (hn'.prod hl)).prod (hvalid.comp (hn'.prod hr)))).prod
      (ComputableInPolyTime.decide_ne hl hr))
  have hblock := PRF.computableInPolyTime_separatingWordBlock.comp
    ((hwidth.comp hn').prod (hl.prod hr))
  have hleft := IsOraclePPTOn.query_take () (hl.bitsAppend hblock) (hout.comp hn')
  have hright := IsOraclePPTOn.query_take () (hr.bitsAppend hblock) (hout.comp hn')
  have hstage := ComputableInPolyTime.fst encStage encBits
  have hcompare := ComputableInPolyTime.decide_eq'
    ((ComputableInPolyTime.snd encStage encBits).comp
      (ComputableInPolyTime.fst (encPair encStage encBits) encBits))
    (ComputableInPolyTime.snd (encPair encStage encBits) encBits)
  refine hrun.isOraclePPTOn.bind_with
    (IsOraclePPTOn.cond hguard ?_ (ComputableInPolyTime.const false).isOraclePPTOn)
  apply hleft.bind_with
  simpa only [map_eq_bind_pure_comp, Function.comp_def] using
    (hright.preprocess hstage).map_with (f := fun p right => decide (p.2 = right)) hcompare

/-- If valid input words are aligned at a positive width, the wrapper for a strict PPT
collision guesser is a strict oracle-PPT distinguisher with prefix-incomparable queries.
The prefix condition is relative to `oracleValid`. Applying the certificate to the source
game also requires showing that the extended queries are nonempty and satisfy `oracleValid`,
as they do for the domain with one extra block in [BonehShoup2023], Theorem 7.3. -/
theorem isPrefixFreeOraclePPT_prefixFreeCollisionReduction {width outLen : ℕ → ℕ}
    {valid oracleValid : ℕ → List Bool → Bool}
    {guessPair : ℕ × ℕ → ProbComp (CollisionGuess (List Bool))}
    (hwidth : ComputableInPolyTime width encUnary encUnary)
    (hout : ComputableInPolyTime outLen encUnary encUnary)
    (hvalid : ComputableInPolyTime (fun p => valid p.1 p.2) (encPair encUnary encBits) encBool)
    (haligned : ∀ n w, valid n w = true → 0 < width n ∧ width n ∣ w.length)
    (hguess : IsPPTOn (encPair encUnary encUnary) (encCollisionGuess encBits) guessPair) :
    IsPrefixFreeOraclePPT oracleValid outLen
      (prefixFreeCollisionReduction width outLen valid guessPair) := by
  refine ⟨isOraclePPT_prefixFreeCollisionReduction hwidth hout hvalid hguess, ?_⟩
  intro n oracle _ _ result hres
  simp only [prefixFreeCollisionReduction, wordQueryRunDist_sample_bind,
    PMF.mem_support_bind_iff] at hres
  obtain ⟨guess, _, hguessRun⟩ := hres
  split at hguessRun
  next hg =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    obtain ⟨⟨hvalidLeft, hvalidRight⟩, hne⟩ := hg
    obtain ⟨hpositive, hl⟩ := haligned n guess.first hvalidLeft
    obtain ⟨_, hr⟩ := haligned n guess.second hvalidRight
    have hsep := PRF.separatingWordBlock_prefix_incomparable hpositive hl hr hne
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def,
      wordQueryRunDist_query_bind, wordQueryRunDist_pure, PMF.pure_map, PMF.mem_support_pure_iff]
      at hguessRun
    subst result
    intro x hx _ y hy _ hxy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact (hxy rfl).elim
    · exact hsep.1
    · exact hsep.2
    · exact (hxy rfl).elim
  next _ =>
    simp only [wordQueryRunDist_pure, PMF.mem_support_pure_iff] at hguessRun
    subst result
    intro x hx
    cases hx

end Cslib.Crypto.UHF
