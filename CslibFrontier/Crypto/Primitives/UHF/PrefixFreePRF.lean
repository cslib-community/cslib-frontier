/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomFunction.PrefixFree
public import CslibFrontier.Crypto.Computational.PseudorandomFunction.PrefixFreePair
public import CslibFrontier.Crypto.Primitives.UHF.Computational
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Crypto.Game.CloseTo
import CslibFrontier.Probability.PMF.Bind

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
* `Cslib.Crypto.UHF.succProbability_collisionGame_le_real_prefixFreeCollisionReduction`:
  the real-game comparison (7.7) for an extendable family on the chosen domains.
-/

public section

namespace Cslib.Crypto.UHF

open Probability Turing.MultiTapeTM
open scoped ENNReal

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

/-- The real-game step (7.7) in [BonehShoup2023], v0.6, Theorem 7.3 (printed p. 259).
Valid words remain valid for the PRF after a one-block extension. If that extension
preserves collisions, each winning collision guess also makes the real wrapper accept. -/
theorem succProbability_collisionGame_le_real_prefixFreeCollisionReduction
    {width outLen : ℕ → ℕ} {valid oracleValid : ℕ → List Bool → Bool}
    (family : List Bool → List Bool → List Bool)
    (guessPair : ℕ × ℕ → ProbComp (CollisionGuess (List Bool))) (n : ℕ)
    (hDomain : ∀ {word block}, valid n word = true → block.length = width n →
      oracleValid n (word ++ block) = true)
    (hExtend : ∀ {key left right block}, key.length = n →
      valid n left = true → valid n right = true → block.length = width n →
      family key left = family key right →
      family key (left ++ block) = family key (right ++ block)) :
    Game.succProbability (collisionGame pure (fun _ d => valid d)
      (fun _ d (key : BitString d) => family (List.ofFn key)) guessPair n) ≤
    Game.succProbability (ProbComp.eval (prfRealGameOn oracleValid family
      (prefixFreeCollisionReduction width outLen valid guessPair) n)) := by
  let accept (key : List Bool) (guess : CollisionGuess (List Bool)) :=
    if valid n guess.first && valid n guess.second && decide (guess.first ≠ guess.second) then
      let block := PRF.separatingWordBlock (width n) guess.first guess.second
      let reply := fun word =>
        (prfOracleOn (oracleValid n) family key (word ++ block)).take (outLen n)
      decide (reply guess.first = reply guess.second)
    else false
  have hRun (key : List Bool) :
      (prefixFreeCollisionReduction width outLen valid guessPair n []).run
        (fun req => pure (prfOracleOn (oracleValid n) family key req.2)) =
      ((guessPair (n, n)) >>= fun guess => pure (accept key guess)) := by
    simp only [prefixFreeCollisionReduction, ProbOracleComp.run_bind, ProbOracleComp.run_sample]
    congr 1
    funext guess
    by_cases hg :
        (valid n guess.first && valid n guess.second && decide (guess.first ≠ guess.second)) =
          true
    · simp only [accept, ite_eq_left hg, ProbOracleComp.run_bind, ProbOracleComp.run_map,
        ProbOracleComp.run_query, ProbOracleComp.run_pure, pure_bind, map_pure]
    · simp only [accept, ite_eq_right hg, ProbOracleComp.run_pure]
  apply ENNReal.coe_le_coe.mp
  simp only [Game.coe_succProbability_ennreal, collisionGame, Game.withSetup_pure,
    prfRealGameOn, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
    BitString.eval_sampleList, BitString.uniformList, PMF.bind_map, Function.comp_def, hRun]
  rw [PMF.bind_comm (PMF.uniformOfFintype (BitString n)) (ProbComp.eval (guessPair (n, n)))]
  apply PMF.bind_apply_mono_on_support _ true
  intro guess _
  apply PMF.bind_apply_mono_on_support _ true
  intro key _
  by_cases hWin : guess.first ≠ guess.second ∧ valid n guess.first = true ∧
      valid n guess.second = true ∧
      family (List.ofFn key) guess.first = family (List.ofFn key) guess.second
  · obtain ⟨hne, hl, hr, hEq⟩ := hWin
    have hBlock := PRF.length_separatingWordBlock (width n) guess.first guess.second
    have hLeft := hDomain hl hBlock
    have hRight := hDomain hr hBlock
    have hTags := hExtend List.length_ofFn hl hr hBlock hEq
    simp [accept, prfOracleOn, hne, hl, hr, hEq, hLeft, hRight, hTags]
  · simp [hWin]

end Cslib.Crypto.UHF
