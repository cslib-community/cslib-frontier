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
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Languages.Probabilistic.Oracle.Interaction
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.UniformPoint

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
* `Cslib.Crypto.UHF.eval_prfIdealGameOn_prefixFreeCollisionReduction_le`:
  the ideal-game bound corresponding to (7.8).
* `Cslib.Crypto.UHF.succProbability_collisionGame_le_prefixFreeCollisionReduction`:
  the concrete advantage inequality (7.6) in the word model.
-/

public section

namespace Cslib.Crypto.UHF

open Probability Turing.MultiTapeTM
open scoped ENNReal NNReal

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

/-- The ideal-game step of [BonehShoup2023], v0.6, Theorem 7.3, printed p. 259, (7.8).
Every accepted guess makes two distinct valid queries and their uniform replies are independent.
The probability is bounded above because invalid or repeated guesses are rejected. -/
theorem eval_prfIdealGameOn_prefixFreeCollisionReduction_le
    {width outLen : ℕ → ℕ} {valid oracleValid : ℕ → List Bool → Bool}
    (guessPair : ℕ × ℕ → ProbComp (CollisionGuess (List Bool))) (n : ℕ)
    (hDomain : ∀ {word block}, valid n word = true → block.length = width n →
      oracleValid n (word ++ block) = true) :
    ProbComp.eval (prfIdealGameOn oracleValid outLen
      (prefixFreeCollisionReduction width outLen valid guessPair) n) true ≤
      ((2 : ℝ≥0∞) ^ outLen n)⁻¹ := by
  simp only [prfIdealGameOn, ProbComp.eval_map, ProbOracleComp.eval_run_interpret_eq_runWith,
    cachedRandomFunctionOracle, eval_cachedSamplerOracle, BitString.eval_sampleList,
    prefixFreeCollisionReduction, ProbOracleComp.runWith_sample_bind, PMF.map_bind]
  apply PMF.bind_apply_le_on_support
  intro guess _
  by_cases hg :
      (valid n guess.first && valid n guess.second && decide (guess.first ≠ guess.second)) = true
  · have hg' := hg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg'
    obtain ⟨⟨hl, hr⟩, hne⟩ := hg'
    let block := PRF.separatingWordBlock (width n) guess.first guess.second
    let left := guess.first ++ block
    let right := guess.second ++ block
    have hBlock : block.length = width n := PRF.length_separatingWordBlock _ _ _
    have hLeft : oracleValid n left = true := hDomain hl hBlock
    have hRight : oracleValid n right = true := hDomain hr hBlock
    have hDistinct : left ≠ right := fun h => hne (List.append_cancel_right h)
    let dist := BitString.uniformList (outLen n)
    have hFresh {request : List Bool} {cache : List (List Bool × List Bool)}
        (hValid : oracleValid n request = true) (hMiss : cache.lookup request = none) :
        cachedDistOracle (oracleValid n) dist request cache =
          dist.map (fun reply => (reply, (request, reply) :: cache)) := by
      simp [cachedDistOracle, hValid, memoize, hMiss, PMF.map, Function.comp_def]
    have hFirst := hFresh (cache := []) hLeft rfl
    have hSecond (reply : List Bool) :
        cachedDistOracle (oracleValid n) dist right [(left, reply)] =
          dist.map (fun other => (other, [(right, other), (left, reply)])) := by
      apply hFresh hRight
      simp [List.lookup_cons, beq_eq_false_iff_ne.mpr hDistinct.symm]
    simp only [ite_eq_left hg, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def,
      ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure]
    change ((cachedDistOracle (oracleValid n) dist left []).bind (fun a =>
      (cachedDistOracle (oracleValid n) dist right a.2).bind (fun b =>
        PMF.pure (decide (a.1.take (outLen n) = b.1.take (outLen n)), b.2)))).map Prod.fst true ≤ _
    simp only [hFirst, PMF.bind_map, Function.comp_def, hSecond, PMF.map_bind, PMF.pure_map]
    apply PMF.bind_apply_le_on_support
    intro reply hReply
    rw [PMF.bind_congr_on_support dist _ (fun other => PMF.pure (decide (reply = other)))
      (fun other hOther => by
        rw [List.take_of_length_le (BitString.length_of_mem_support_uniformList hReply).le,
          List.take_of_length_le (BitString.length_of_mem_support_uniformList hOther).le]),
      PMF.bind_pure_decide_eq_apply_true]
    simpa only [one_div] using BitString.uniformList_apply_le (outLen n) reply
  · simp only [ite_eq_right hg, ProbOracleComp.runWith_pure, PMF.pure_map]
    simp

/-- The concrete bound (7.6) from [BonehShoup2023], v0.6, Theorem 7.3 (printed pp. 258–259)
for the word wrapper. Collision success is at most its PRF advantage plus the inverse
size of the output space. One full block is appended to every accepted pair. -/
theorem succProbability_collisionGame_le_prefixFreeCollisionReduction
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
    Game.advantage
      (ProbComp.eval (prfRealGameOn oracleValid family
        (prefixFreeCollisionReduction width outLen valid guessPair) n))
      (ProbComp.eval (prfIdealGameOn oracleValid outLen
        (prefixFreeCollisionReduction width outLen valid guessPair) n)) +
      ((2 : ℝ≥0) ^ outLen n)⁻¹ := by
  let I : Game := ProbComp.eval (prfIdealGameOn oracleValid outLen
    (prefixFreeCollisionReduction width outLen valid guessPair) n)
  have hIdeal : I.succProbability ≤ ((2 : ℝ≥0) ^ outLen n)⁻¹ := by
    apply ENNReal.coe_le_coe.mp
    rw [Game.coe_succProbability_ennreal, ENNReal.coe_inv (pow_ne_zero _ two_ne_zero),
      ENNReal.coe_pow, ENNReal.coe_ofNat]
    exact eval_prfIdealGameOn_prefixFreeCollisionReduction_le guessPair n hDomain
  refine (succProbability_collisionGame_le_real_prefixFreeCollisionReduction
    (outLen := outLen) family guessPair n hDomain hExtend).trans
    ((Game.succProbability_le_add_of_advantage_le (g₁ := I) le_rfl).trans ?_)
  rw [add_comm I.succProbability]
  exact add_le_add le_rfl hIdeal

end Cslib.Crypto.UHF
