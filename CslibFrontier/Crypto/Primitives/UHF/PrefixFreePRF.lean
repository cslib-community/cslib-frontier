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
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Traverse
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Crypto.Game.CloseTo
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Foundations.Data.List.EraseDupsBy
import CslibFrontier.Languages.Probabilistic.Oracle.Interaction
import CslibFrontier.Languages.Probabilistic.Traverse.SupportWith
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.UniformPoint

/-!
# Computational universal hashing from an extendable prefix-free PRF

The two-query wrapper proves [BonehShoup2023], v0.6, Theorem 7.3 (printed pp. 258–259),
in the word model. It runs the collision guesser on the public unary parameter, extends
each accepted word by the same full block, and checks equality of the two oracle replies.
The wrapper always extends an accepted pair. Its reply reads are capped at the declared width.

The certificate uses the library's domain-relative prefix condition. Definition 4.5
(printed p. 152) also requires every query to be nonempty and in the PRF input domain. Applying
the wrapper to that game requires showing that the extended messages fit the oracle domain.
Theorem 7.3 provides this room by giving the PRF domain one extra block of capacity.

For the direct multi-query reduction in Theorem 7.4, a bounded batch uses one block absent
from all its messages. The wrapper queries each retained distinct message once after extension.

## Main definitions

* `Cslib.Crypto.UHF.prefixFreeCollisionReduction`: compare oracle replies on extended queries.
* `Cslib.Crypto.UHF.prefixFreeCollisionReductionWithCap`: the shared program with a cap computed
  from the first extended query.
* `Cslib.Crypto.UHF.prefixFreeBatchQueries`: prepare a bounded list of extended words.
* `Cslib.Crypto.UHF.prefixFreeBatchReduction`: compare oracle replies on the prepared words.

## Main results

* `Cslib.Crypto.UHF.isPrefixFreeOraclePPT_prefixFreeCollisionReduction`: the wrapper for a strict
  PPT guesser is strict oracle PPT and makes prefix-incomparable queries.
* `Cslib.Crypto.UHF.isQueryBounded_prefixFreeCollisionReduction`: the wrapper makes at most
  two oracle queries.
* `Cslib.Crypto.UHF.succProbability_collisionGame_le_real_prefixFreeCollisionReduction`:
  the real-game comparison (7.7) for an extendable family on the chosen domains.
* `Cslib.Crypto.UHF.eval_prfIdealGameOn_prefixFreeCollisionReduction_le`:
  the ideal-game bound corresponding to (7.8).
* `Cslib.Crypto.UHF.succProbability_collisionGame_le_prefixFreeCollisionReduction`:
  the concrete advantage inequality (7.6) in the word model.
* `Cslib.Crypto.UHF.isComputationalUHF_of_extendable_prefixFreePRF`:
  the single-query security theorem for an extendable prefix-free PRF.
* `Cslib.Crypto.UHF.isQueryBounded_prefixFreeBatchReduction`: at most one query per retained word.
* `Cslib.Crypto.UHF.isOraclePPT_prefixFreeBatchReduction`: strict oracle PPT for the batch wrapper.
* `Cslib.Crypto.UHF.isPrefixFreeOraclePPT_prefixFreeBatchReduction`: the batch wrapper's traces
  are prefix-free when accepted guesses consist of complete positive-width blocks.
-/

public section

namespace Cslib.Crypto.UHF

open Probability Turing.MultiTapeTM
open scoped ENNReal NNReal

/-- Reject invalid and repeated guesses. On an accepted pair, append the same separating block
to both words and compare the two oracle replies, capped at the value of `cap` on the parameter
and first extended query. -/
@[expose] def prefixFreeCollisionReductionWithCap (width : ℕ → ℕ) (cap : ℕ → List Bool → ℕ)
    (valid : ℕ → List Bool → Bool) (guessPair : ℕ × ℕ → ProbComp (CollisionGuess (List Bool))) :
    OracleDistinguisher :=
  fun n _ => do
    let guess ← ProbOracleComp.sample (guessPair (n, n))
    if valid n guess.first && valid n guess.second && decide (guess.first ≠ guess.second) then
      let block := PRF.separatingWordBlock (width n) guess.first guess.second
      let limit := cap n (guess.first ++ block)
      let left ← List.take limit <$> ProbOracleComp.query ((), guess.first ++ block)
      let right ← List.take limit <$> ProbOracleComp.query ((), guess.second ++ block)
      return decide (left = right)
    else
      return false

/-- The prefix-free collision wrapper with both replies capped at the declared output width. -/
@[expose] def prefixFreeCollisionReduction (width outLen : ℕ → ℕ)
    (valid : ℕ → List Bool → Bool) (guessPair : ℕ × ℕ → ProbComp (CollisionGuess (List Bool))) :
    OracleDistinguisher :=
  prefixFreeCollisionReductionWithCap width (fun n _ => outLen n) valid guessPair

/-- The wrapper makes at most two external queries, regardless of the guess or the replies. -/
theorem isQueryBounded_prefixFreeCollisionReduction (width outLen : ℕ → ℕ)
    (valid : ℕ → List Bool → Bool) (guessPair : ℕ × ℕ → ProbComp (CollisionGuess (List Bool)))
    (n : ℕ) (aux : List Bool) :
    (prefixFreeCollisionReduction width outLen valid guessPair n aux).IsQueryBounded 2 := by
  rw [prefixFreeCollisionReduction, prefixFreeCollisionReductionWithCap, ← Nat.zero_add 2]
  refine (ProbOracleComp.IsQueryBounded.sample _).bind fun guess => ?_
  split
  · simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
    refine (ProbOracleComp.IsQueryBounded.query _).bind (m := 1) fun _ => ?_
    exact (ProbOracleComp.IsQueryBounded.query _).bind (m := 0) fun _ =>
      OracleComp.IsCostBounded.pure _ 0
  · exact OracleComp.IsCostBounded.pure _ 2

private theorem isOraclePPT_prefixFreeCollisionReduction {width outLen : ℕ → ℕ}
    {cap : ℕ → List Bool → ℕ}
    {valid : ℕ → List Bool → Bool} {guessPair : ℕ × ℕ → ProbComp (CollisionGuess (List Bool))}
    (hwidth : ComputableInPolyTime width encUnary encUnary)
    (hcap : ComputableInPolyTime (fun p => cap p.1 p.2) (encPair encUnary encBits) encUnary)
    (hcapEq : ∀ {n word block}, valid n word = true → block.length = width n →
      cap n (word ++ block) = outLen n)
    (hvalid : ComputableInPolyTime (fun p => valid p.1 p.2) (encPair encUnary encBits) encBool)
    (hguess : IsPPTOn (encPair encUnary encUnary) (encCollisionGuess encBits) guessPair) :
    IsOraclePPT encBool (prefixFreeCollisionReduction width outLen valid guessPair) := by
  have hcert : IsOraclePPT encBool
      (prefixFreeCollisionReductionWithCap width cap valid guessPair) := by
    let encGuess := encCollisionGuess encBits
    let encInput := encPair encUnary encBits
    let encStage := encPair encInput encGuess
    have hn := ComputableInPolyTime.fst encUnary encBits
    have hrun := hguess.preprocess (hn.prod hn)
    have hn' := hn.comp (ComputableInPolyTime.fst encInput encGuess)
    have hpair := ComputableInPolyTime.snd encInput encGuess
    have hl := encCollisionGuess_first_polyTime encBits hpair
    have hr := encCollisionGuess_second_polyTime encBits hpair
    have hguard := ComputableInPolyTime.bool_and.comp
      ((ComputableInPolyTime.bool_and.comp
        ((hvalid.comp (hn'.prod hl)).prod (hvalid.comp (hn'.prod hr)))).prod
        (ComputableInPolyTime.decide_ne hl hr))
    have hblock := PRF.computableInPolyTime_separatingWordBlock.comp
      ((hwidth.comp hn').prod (hl.prod hr))
    have hleftWord := hl.bitsAppend hblock
    have hlimit := hcap.comp (hn'.prod hleftWord)
    have hleft := IsOraclePPTOn.query_take () hleftWord hlimit
    have hright := IsOraclePPTOn.query_take () (hr.bitsAppend hblock) hlimit
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
  apply hcert.congr
  intro n aux State oracle state
  apply congrArg (fun program => ProbOracleComp.runWith oracle program state)
  simp only [prefixFreeCollisionReduction, prefixFreeCollisionReductionWithCap]
  congr 1
  funext guess
  by_cases hg :
      (valid n guess.first && valid n guess.second && decide (guess.first ≠ guess.second)) = true
  · have hLeft := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hg).1).1
    have hBlock := PRF.length_separatingWordBlock (width n) guess.first guess.second
    simp only [ite_eq_left hg, hcapEq hLeft hBlock]
  · simp only [ite_eq_right hg]

private theorem isPrefixFreeOn_prefixFreeCollisionReduction {width outLen : ℕ → ℕ}
    {valid oracleValid : ℕ → List Bool → Bool}
    {guessPair : ℕ × ℕ → ProbComp (CollisionGuess (List Bool))}
    (haligned : ∀ n w, valid n w = true → 0 < width n ∧ width n ∣ w.length)
    (n : ℕ) :
    IsPrefixFreeOn (oracleValid n) (outLen n)
      (prefixFreeCollisionReduction width outLen valid guessPair n []) := by
  intro oracle _ _ result hres
  simp only [prefixFreeCollisionReduction, prefixFreeCollisionReductionWithCap,
    wordQueryRunDist_sample_bind,
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
      (prefixFreeCollisionReduction width outLen valid guessPair) :=
  ⟨isOraclePPT_prefixFreeCollisionReduction
    (cap := fun n _ => outLen n) hwidth (hout.comp (ComputableInPolyTime.fst encUnary encBits))
    (fun _ _ => rfl) hvalid hguess, isPrefixFreeOn_prefixFreeCollisionReduction haligned⟩

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
    simp only [prefixFreeCollisionReduction, prefixFreeCollisionReductionWithCap,
      ProbOracleComp.run_bind, ProbOracleComp.run_sample]
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
    prefixFreeCollisionReduction, prefixFreeCollisionReductionWithCap,
    ProbOracleComp.runWith_sample_bind, PMF.map_bind]
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

/-- Boneh–Shoup v0.6, Theorem 7.3 (printed pp. 258–259), in the word model. An extendable
prefix-free PRF with negligible reciprocal reply-space size is a computational UHF on the
smaller domain. The uniform private key has `n` bits, and public setup is the unary parameter.
Valid hash inputs are whole blocks of positive width, and appending any one block puts them
in the PRF domain.

For positive-width bit blocks, the nonempty hash inputs of at most `ℓ` blocks lie in the
oracle domain of one to `ℓ + 1` blocks. The PRF's length clause therefore gives fixed-width
digests on those inputs. The word theorem also permits the zero-block hash input, whose
extension is a nonempty oracle query. If the oracle domain excludes the empty word, the family
supplies the digest width on that input separately, as in `length_cbcMacFamily`. The conclusion
uses raw `List Bool` digests, which at the declared width represent `BitString (outLen n)`.

The reduction obtains the reply width by evaluating the PRF at a public zero key on a valid
extended query. -/
theorem isComputationalUHF_of_extendable_prefixFreePRF
    {width outLen : ℕ → ℕ} {valid oracleValid : ℕ → List Bool → Bool}
    {family : List Bool → List Bool → List Bool}
    (hPRF : PrefixFreePseudorandomFunctionOn oracleValid outLen family)
    (hwidth : ComputableInPolyTime width encUnary encUnary)
    (hvalid : ComputableInPolyTime (fun p => valid p.1 p.2) (encPair encUnary encBits) encBool)
    (haligned : ∀ n word, valid n word = true → 0 < width n ∧ width n ∣ word.length)
    (hDomain : ∀ {n word block}, valid n word = true → block.length = width n →
      oracleValid n (word ++ block) = true)
    (hExtend : ∀ {n key left right block}, key.length = n →
      valid n left = true → valid n right = true → block.length = width n →
      family key left = family key right →
      family key (left ++ block) = family key (right ++ block))
    (hout : Negligible (fun n => ((2 : ℝ≥0) ^ outLen n)⁻¹)) :
    IsComputationalUHF encUnary encBits pure (fun _ d => valid d)
      (fun _ d (key : BitString d) => family (List.ofFn key)) := by
  apply Game.Indistinguishable.of_negligible_succProbability
  intro guessPair hguess
  let cap (n : ℕ) (query : List Bool) := (family (List.replicate n false) query).length
  have hcap : ComputableInPolyTime (fun p => cap p.1 p.2)
      (encPair encUnary encBits) encUnary := by
    have hzero := (ComputableInPolyTime.bitsReplicate false).comp
      (ComputableInPolyTime.fst encUnary encBits)
    have hquery := ComputableInPolyTime.snd encUnary encBits
    exact (hPRF.polyTime.comp (hzero.prod hquery)).length_bits_comp
  have hcapEq {n : ℕ} {word block : List Bool} (hw : valid n word = true)
      (hb : block.length = width n) : cap n (word ++ block) = outLen n := by
    have hv := hDomain hw hb
    have hlen := hPRF.length_eq (List.replicate n false) (word ++ block)
      (by simpa only [List.length_replicate] using hv)
    simpa only [cap, List.length_replicate] using hlen
  have hred : IsPrefixFreeOraclePPT oracleValid outLen
      (prefixFreeCollisionReduction width outLen valid guessPair) :=
    ⟨isOraclePPT_prefixFreeCollisionReduction hwidth hcap hcapEq hvalid hguess,
      isPrefixFreeOn_prefixFreeCollisionReduction haligned⟩
  exact negligible_of_le ((hPRF.secure _ hred).add hout) fun n =>
    succProbability_collisionGame_le_prefixFreeCollisionReduction family guessPair n hDomain
      hExtend

/-- Take at most `count` guesses, keep the first occurrence of each valid word, and extend each
with the same fresh block. An exhausted block search produces no queries. This prepares the batch
for the wrapper in [BonehShoup2023], v0.6, Theorem 7.4 (printed pp. 259–260). -/
@[expose] def prefixFreeBatchQueries (width count : ℕ) (valid : List Bool → Bool)
    (guesses : List (List Bool)) : List (List Bool) :=
  let messages := ((guesses.take count).filter valid).eraseDupsBy fun a b => decide (a = b)
  let block := PRF.freshBatchWordBlock width messages
  if block.isSome then messages.map (fun word => word ++ block.getD []) else []

/-- Each prepared word is distinct, including when the guesser repeats a message. -/
theorem nodup_prefixFreeBatchQueries (width count : ℕ) (valid : List Bool → Bool)
    (guesses : List (List Bool)) : (prefixFreeBatchQueries width count valid guesses).Nodup := by
  unfold prefixFreeBatchQueries
  dsimp only
  split
  · exact (List.nodup_eraseDupsBy_eq _).map fun _ _ => List.append_cancel_right
  · exact List.nodup_nil

private theorem isPrefixFree_prefixFreeBatchQueries {width count : ℕ}
    {valid : List Bool → Bool} (guesses : List (List Bool))
    (haligned : ∀ word, valid word = true → 0 < width ∧ width ∣ word.length) :
    InformationTheory.IsPrefixFree
      {word | word ∈ prefixFreeBatchQueries width count valid guesses} := by
  let messages := ((guesses.take count).filter valid).eraseDupsBy fun a b => decide (a = b)
  have hvalid (word : List Bool) (hm : word ∈ messages) : valid word = true :=
    (List.mem_filter.mp ((List.eraseDupsBy_sublist _).subset hm)).2
  change InformationTheory.IsPrefixFree {word | word ∈
    if (PRF.freshBatchWordBlock width messages).isSome then
      messages.map (fun msg => msg ++ (PRF.freshBatchWordBlock width messages).getD []) else []}
  cases hblock : PRF.freshBatchWordBlock width messages with
  | none =>
    intro _ hx
    cases hx
  | some block =>
    intro x hx y hy hpre
    change x ∈ messages.map (fun msg => msg ++ block) at hx
    change y ∈ messages.map (fun msg => msg ++ block) at hy
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
    have hprefix := PRF.isPrefixFree_append_of_freshBatchWordBlock_eq_some
      (haligned u (hvalid u hu)).1 (fun m hm => (haligned m (hvalid m hm)).2) hblock
    exact hprefix _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ hpre

/-- Run the multi-query guesser on the public unary parameter, query the extended words, and
accept if two capped replies coincide. The reply cap bounds the reading time for any oracle. -/
@[expose] def prefixFreeBatchReduction (width outLen Q : ℕ → ℕ)
    (valid : ℕ → List Bool → Bool) (guessBatch : ℕ × ℕ → ProbComp (List (List Bool))) :
    OracleDistinguisher := fun n _ => do
  let guesses ← ProbOracleComp.sample (guessBatch (n, n))
  let queries := prefixFreeBatchQueries (width n) (Q n) (valid n) guesses
  let replies ← queries.mapM fun query =>
    List.take (outLen n) <$> ProbOracleComp.query ((), query)
  return !decide replies.Nodup

/-- The batch wrapper makes at most `Q n` external queries for every oracle and guess list. -/
theorem isQueryBounded_prefixFreeBatchReduction (width outLen Q : ℕ → ℕ)
    (valid : ℕ → List Bool → Bool) (guessBatch : ℕ × ℕ → ProbComp (List (List Bool)))
    (n : ℕ) (aux : List Bool) :
    (prefixFreeBatchReduction width outLen Q valid guessBatch n aux).IsQueryBounded (Q n) := by
  rw [prefixFreeBatchReduction]
  nth_rw 2 [← Nat.zero_add (Q n)]
  refine (ProbOracleComp.IsQueryBounded.sample _).bind fun guesses => ?_
  let queries := prefixFreeBatchQueries (width n) (Q n) (valid n) guesses
  have hquery (word : List Bool) :
      (List.take (outLen n) <$> ProbOracleComp.query
        (spec := fun _ : Unit × List Bool => List Bool) ((), word)).IsQueryBounded 1 :=
    (OracleComp.isCostBounded_map_iff _ _ _).mpr (ProbOracleComp.IsQueryBounded.query _)
  have htraverse := OracleComp.IsCostBounded.mapM (inputs := queries) fun word _ => hquery word
  refine (htraverse.bind fun _ => OracleComp.IsCostBounded.pure _ 0).mono ?_
  simp only [Nat.mul_one, Nat.add_zero]
  unfold queries prefixFreeBatchQueries
  dsimp only
  split
  · rw [List.length_map]
    exact ((List.eraseDupsBy_sublist _).length_le.trans (List.length_filter_le _ _)).trans
      (List.length_take_le _ _)
  · simp

open ComputableInPolyTime in
private theorem computableInPolyTime_prefixFreeBatchQueries {α : Type}
    {input : α ↪ List Bool} {width count : α → ℕ} {valid : α → List Bool → Bool}
    {guesses : α → List (List Bool)}
    (hwidth : ComputableInPolyTime width input encUnary)
    (hcount : ComputableInPolyTime count input encUnary)
    (hvalid : ComputableInPolyTime (fun p => valid p.1 p.2) (encPair input encBits) encBool)
    (hguesses : ComputableInPolyTime guesses input (encList encBits)) :
    ComputableInPolyTime (fun a => prefixFreeBatchQueries (width a) (count a) (valid a) (guesses a))
      input (encList encBits) := by
  have hfiltered := filterWithInput (test := valid) (listTakeWithInput hguesses hcount) hvalid
  have hmessages := eraseDupsByWithInput (r := fun _ a b => decide (a = b)) hfiltered
    (decide_eq' (fst _ _).snd' (snd _ _))
  let block (a : α) := PRF.freshBatchWordBlock (width a)
    ((((guesses a).take (count a)).filter (valid a)).eraseDupsBy fun u v => decide (u = v))
  have hchoice : ComputableInPolyTime block input (encOption encBits) :=
    PRF.computableInPolyTime_freshBatchWordBlock.comp (hwidth.prod hmessages)
  have hblock := hchoice.optionGetDWithInput (const [])
  have hqueries := mapWithInput (f := fun a word => word ++ (block a).getD []) hmessages
    (bitsAppend (snd _ _) (hblock.comp (fst _ _)))
  simpa only [prefixFreeBatchQueries, Function.comp_def, block] using
    ite' hchoice.optionIsSome hqueries (const [])

open ComputableInPolyTime in
/-- The bounded batch wrapper is strict oracle PPT for a strict PPT guesser and
polynomial-time width, reply cap, query cap, and validity check. -/
theorem isOraclePPT_prefixFreeBatchReduction {width outLen Q : ℕ → ℕ}
    {valid : ℕ → List Bool → Bool} {guessBatch : ℕ × ℕ → ProbComp (List (List Bool))}
    (hwidth : ComputableInPolyTime width encUnary encUnary)
    (hout : ComputableInPolyTime outLen encUnary encUnary)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    (hvalid : ComputableInPolyTime (fun p => valid p.1 p.2) (encPair encUnary encBits) encBool)
    (hguess : IsPPTOn (encPair encUnary encUnary) (encList encBits) guessBatch) :
    IsOraclePPT encBool (prefixFreeBatchReduction width outLen Q valid guessBatch) := by
  let encInput := encPair encUnary encBits
  let encWords := encList encBits
  let encStage := encPair encInput encWords
  have hn := fst encUnary encBits
  have hrun := hguess.preprocess (hn.prod hn)
  have hn' := hn.comp (fst encInput encWords)
  have hvalid' := hvalid.comp ((hn'.comp (fst encStage encBits)).prod (snd encStage encBits))
  have hqueries := computableInPolyTime_prefixFreeBatchQueries
    (valid := fun (p : (ℕ × List Bool) × List (List Bool)) word => valid p.1.1 word)
    (hwidth.comp hn') (hQ.comp hn') hvalid' (snd encInput encWords)
  have htraverse := IsOraclePPTOn.mapM_query_take () hqueries (hout.comp hn')
  have hcollision := bool_not.comp (decide_nodup_bits (id' (encIn := encWords)))
  apply hrun.isOraclePPTOn.bind_with
  simpa only [map_eq_bind_pure_comp, Function.comp_def] using htraverse.map hcollision

/-- The batch wrapper is a strict prefix-free oracle-PPT distinguisher when each valid
message is a word of complete positive-width blocks. Prefix-freeness holds on every oracle
domain. To apply the bound of Theorem 7.4, the extended words also have to lie in the
chosen PRF domain, which in the book permits one extra block. -/
theorem isPrefixFreeOraclePPT_prefixFreeBatchReduction {width outLen Q : ℕ → ℕ}
    {valid oracleValid : ℕ → List Bool → Bool}
    {guessBatch : ℕ × ℕ → ProbComp (List (List Bool))}
    (hwidth : ComputableInPolyTime width encUnary encUnary)
    (hout : ComputableInPolyTime outLen encUnary encUnary)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    (hvalid : ComputableInPolyTime (fun p => valid p.1 p.2) (encPair encUnary encBits) encBool)
    (haligned : ∀ n word, valid n word = true → 0 < width n ∧ width n ∣ word.length)
    (hguess : IsPPTOn (encPair encUnary encUnary) (encList encBits) guessBatch) :
    IsPrefixFreeOraclePPT oracleValid outLen (prefixFreeBatchReduction width outLen Q valid
      guessBatch) := by
  refine ⟨isOraclePPT_prefixFreeBatchReduction hwidth hout hQ hvalid hguess, ?_⟩
  intro n oracle _ _ result hresult
  simp only [prefixFreeBatchReduction, wordQueryRunDist_sample_bind, PMF.mem_support_bind_iff,
    wordQueryRunDist_mapM_query_pure, PMF.mem_support_pure_iff] at hresult
  obtain ⟨guesses, _, rfl⟩ := hresult
  have hprefix := isPrefixFree_prefixFreeBatchQueries (count := Q n) guesses (haligned n)
  intro x hx _ y hy _ hne hpre
  exact hne (hprefix x hx y hy hpre)

end Cslib.Crypto.UHF
