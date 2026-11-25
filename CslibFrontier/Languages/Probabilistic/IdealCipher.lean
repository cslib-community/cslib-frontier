/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.RandomPermutation
public import CslibFrontier.Languages.Probabilistic.UntilBad.ChooseTwo
public import CslibFrontier.Languages.Probabilistic.Simulation
public import CslibFrontier.Probability.Product
public import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Tactic.SuppCases

/-!
# Ideal Cipher Model

This module formalizes the Ideal Cipher Model, consisting of independent random
permutations for each key, and defines its exact and forgetful lazy samplers.

## Main definitions
* `Query`: An ideal cipher query, combining a key and a permutation query.
* `Spec`: The ideal cipher specification.
* `lazyEvalPerm`, `answer`, `forgetfulAnswer`: Samplers for evaluating an ideal cipher.

## Main results
* `uniform_interpret_eq_lazy`: Eager random-permutation sampling matches lazy exact caching.
* `identicalUntilBad_exactWithBad_forgetfulWithBad`: Identical-until-bad coupling between exact
  and forgetful samplers.
* `toOuterMeasure_bad_forgetfulWithBad_le`: Quadratic birthday bound on the forgetful bad event.
* `abs_sub_uniformPerm_forgetful_le`: Ideal-cipher switching bound
  `Q.choose 2 * (Fintype.card Block)⁻¹`.

## References
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020], Section 7.3.1.
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 4.7.
-/

public section

namespace Cslib.IdealCipher

open Cslib.RandomPermutation Cslib.Probability Cslib.OracleComp
open scoped ENNReal NNReal BigOperators

variable {Key Block : Type}

/-- A query to the ideal cipher, consisting of a key and a block query. -/
abbrev Query (Key Block : Type) := Key × PermQuery Block

/-- The oracle specification for an ideal cipher. -/
abbrev Spec (Key Block : Type) : OracleSpec (Query Key Block) :=
  fun _ => Block

section Finite
variable [DecidableEq Key] [Fintype Key] [DecidableEq Block] [Fintype Block] [Nonempty Block]

/-- Evaluate an ideal cipher directly with a full permutation state. -/
@[expose]
noncomputable def lazyEvalPerm (q : Query Key Block) : StateT (Key → Equiv.Perm Block) PMF Block :=
  fun P => (·, P) <$> PMF.pure (evalPerm (P q.1) q.2)

/-- Evaluate an ideal cipher with a lazy cache. -/
@[expose]
noncomputable def answer (q : Query Key Block) :
    StateT (Key → Cache Block) PMF Block := fun st =>
  (RandomPermutation.answer q.2 (st q.1)).map fun (b, c) => (b, Function.update st q.1 c)

/-- Evaluate an ideal cipher with a forgetful cache that doesn't check consistency. -/
@[expose]
noncomputable def forgetfulAnswer (q : Query Key Block) :
    StateT (Key → Cache Block) PMF Block := fun st =>
  (RandomPermutation.forgetfulAnswer q.2 (st q.1)).map fun (b, c) => (b, Function.update st q.1 c)

/-- Generates a complete tuple of independent random permutations extending the given cache
function. -/
@[expose]
noncomputable def complete (st : Key → Cache Block) : PMF (Key → Equiv.Perm Block) :=
  PMF.pi (fun k => RandomPermutation.complete (st k))

omit [DecidableEq Key] [Nonempty Block] in
/-- Completing the empty cache samples an independent uniformly random permutation for every
key. -/
theorem complete_nil :
    complete (fun _ : Key => ([] : Cache Block)) =
      PMF.pi (fun _ : Key => PMF.uniformOfFintype (Equiv.Perm Block)) := by
  simp only [complete, RandomPermutation.complete_nil]

/-- An exact evaluation step for the ideal cipher model, with a bad flag that triggers
when a duplicate output is sampled. -/
noncomputable def exactWithBad (q : Query Key Block) :
    StateT ((Key → Cache Block) × Bool) PMF Block := fun (st, bad) =>
  (RandomPermutation.exactWithBad q.2 (st q.1, bad)).map fun (b, (c, bad')) =>
    (b, (Function.update st q.1 c, bad'))

/-- A forgetful evaluation step for the ideal cipher model, updating the cache and the bad flag. -/
noncomputable def forgetfulWithBad (q : Query Key Block) :
    StateT ((Key → Cache Block) × Bool) PMF Block := fun (st, bad) =>
  (RandomPermutation.forgetfulWithBad q.2 (st q.1, bad)).map fun (b, (c, bad')) =>
    (b, (Function.update st q.1 c, bad'))

omit [Fintype Key] in
/-- A query step of `answer` preserves the invariant that every key's cache is a partial
bijection. -/
theorem answer_preserve_isPartialBijection (q : Query Key Block) (st : Key → Cache Block)
    (hst : ∀ k, IsPartialBijection (st k)) (a : Block) (st' : Key → Cache Block)
    (hmem : (a, st') ∈ (answer q st).support) (k : Key) : IsPartialBijection (st' k) := by
  supp_cases hmem [answer] with ⟨⟨b, c'⟩, hmem, rfl, rfl⟩
  rcases eq_or_ne k q.1 with rfl | h
  · simpa using RandomPermutation.answer_preserve_isPartialBijection q.2 _ (hst q.1) b c' hmem
  · simpa [Function.update_of_ne h] using hst k

/-- Single-step simulation law for `answer` against `complete`: when every key's cache in `st` is
a partial bijection, answering `q` lazily and completing the updated caches yields the same joint
distribution of `(answer, permutations)` as completing `st` first and evaluating `q` under the
resulting permutation family. -/
theorem answer_complete (q : Query Key Block) (st : Key → Cache Block)
    (hst : ∀ k, IsPartialBijection (st k)) :
    (answer q st).bind (fun (a, st') => (complete st').map (a, ·)) =
      (complete st).bind (fun P => (fun x => (x, P)) <$> PMF.pure (evalPerm (P q.1) q.2)) := by
  let p : Key → PMF (Equiv.Perm Block) := fun k => RandomPermutation.complete (st k)
  have hupdate (c : Cache Block) :
      (fun k => RandomPermutation.complete (Function.update st q.1 c k)) =
        Function.update p q.1 (RandomPermutation.complete c) :=
    funext <| Function.apply_update (fun _ => RandomPermutation.complete) st q.1 c
  have hcomplete_update (c : Cache Block) :
      complete (Function.update st q.1 c) =
        (RandomPermutation.complete c).bind fun v =>
          PMF.pi (Function.update p q.1 (PMF.pure v)) := by
    change PMF.pi (fun k => RandomPermutation.complete (Function.update st q.1 c k)) = _
    rw [hupdate c]
    simpa only [Function.update_self, Function.update_idem] using
      (PMF.pi_bind_update (Function.update p q.1 (RandomPermutation.complete c)) q.1).symm
  calc
    (answer q st).bind (fun (a, st') => (complete st').map (a, ·))
        = (RandomPermutation.answer q.2 (st q.1)).bind fun (b, c) =>
            ((RandomPermutation.complete c).bind fun v =>
              PMF.pi (Function.update p q.1 (PMF.pure v))).map (b, ·) := by
          simp only [answer, PMF.bind_map, Function.comp_def, hcomplete_update]
      _ = ((RandomPermutation.answer q.2 (st q.1)).bind fun (b, c) =>
            (RandomPermutation.complete c).map (b, ·)).bind fun (b, v) =>
              (PMF.pi (Function.update p q.1 (PMF.pure v))).map (b, ·) := by
          rw [PMF.bind_bind]
          congr 1 with ⟨b, c⟩ : 1
          dsimp only
          rw [PMF.map_bind, PMF.bind_map]
          rfl
      _ = (RandomPermutation.complete (st q.1)).bind fun v =>
            (PMF.pi (Function.update p q.1 (PMF.pure v))).map (evalPerm v q.2, ·) := by
          rw [RandomPermutation.answer_complete q.2 (st q.1) (hst q.1)]
          simp only [pmf_norm]
      _ = (PMF.pi p).bind fun P => PMF.pure (evalPerm (P q.1) q.2, P) :=
          PMF.bind_pi_update p q.1 (fun v P => PMF.pure (evalPerm v q.2, P))
      _ = (complete st).bind
            (fun P => (fun x => (x, P)) <$> PMF.pure (evalPerm (P q.1) q.2)) := by
          simp only [complete, p, pmf_norm]

/-- Running `program` against independent uniformly random permutations
`P : Key → Equiv.Perm Block` yields the same output distribution as running `program` lazily under
`answer` from empty caches and projecting out the return value. -/
theorem uniform_interpret_eq_lazy {α : Type} (program : OracleComp (Spec Key Block) α) :
    (do
      let P ← PMF.pi (fun _ : Key => PMF.uniformOfFintype (Equiv.Perm Block))
      OracleComp.interpret (fun (q : Query Key Block) => PMF.pure (evalPerm (P q.1) q.2)) program) =
    ((OracleComp.interpret answer program).run (fun _ => [])).map Prod.fst := by
  have h := congrArg (PMF.map Prod.fst) <|
    OracleComp.run_interpret_simulation_of_invariant answer lazyEvalPerm complete
      (fun s => ∀ k, IsPartialBijection (s k)) answer_preserve_isPartialBijection
      answer_complete program (fun _ => []) (fun _ => isPartialBijection_nil)
  have h2 : ((OracleComp.interpret answer program).run (fun _ => [])).map Prod.fst =
      ((complete (fun _ : Key => [])).bind fun t =>
        (OracleComp.interpret lazyEvalPerm program).run t).map Prod.fst := by
    simpa only [pmf_norm, complete, PMF.map, PMF.bind_const] using h
  rw [h2]
  simp only [complete, RandomPermutation.complete_nil, pmf_norm, PMF.map_bind]
  refine congrArg _ (funext fun P => ?_)
  refine ((congrArg (PMF.map Prod.fst) (OracleComp.run_interpret_readOnly
    (fun (q : Query Key Block) (P : Key → Equiv.Perm Block) => PMF.pure (evalPerm (P q.1) q.2))
    program P)).trans ?_).symm
  rw [PMF.monad_map_eq_map, PMF.map_comp]
  exact PMF.map_id _

omit [Fintype Key] in
/-- `exactWithBad` and `forgetfulWithBad` are identical until the bad flag becomes `true`. -/
theorem identicalUntilBad_exactWithBad_forgetfulWithBad :
    IdenticalUntilBad (spec := Spec Key Block) exactWithBad forgetfulWithBad
      (fun st : (Key → Cache Block) × Bool => st.2 = true) where
  absorb_first a st h_bad st' hmem := by
    rcases st with ⟨st_map, bad⟩
    rcases st' with ⟨_, _, _⟩
    supp_cases hmem [exactWithBad] with ⟨⟨b, c, bad_new⟩, hmem3, rfl, rfl, rfl⟩
    exact RandomPermutation.identicalUntilBad_exactWithBad_forgetfulWithBad.absorb_first
      a.2 (st_map a.1, bad) h_bad (b, (c, bad_new)) hmem3
  absorb_second a st h_bad st' hmem := by
    rcases st with ⟨st_map, bad⟩
    rcases st' with ⟨_, _, _⟩
    supp_cases hmem [forgetfulWithBad] with ⟨⟨b, c, bad_new⟩, hmem3, rfl, rfl, rfl⟩
    exact RandomPermutation.identicalUntilBad_exactWithBad_forgetfulWithBad.absorb_second
      a.2 (st_map a.1, bad) h_bad (b, (c, bad_new)) hmem3
  agree a st hst b st' hst' := by
    obtain ⟨st_map, _ | _⟩ := st
    · obtain ⟨st'_map, _ | _⟩ := st'
      · simp only [exactWithBad, forgetfulWithBad, PMF.map_apply]
        refine tsum_congr fun ⟨b_out, c_out, bad_out⟩ => ?_
        split_ifs with h
        · injection h with h1 h2
          injection h2 with h3 h4
          subst h4
          exact RandomPermutation.identicalUntilBad_exactWithBad_forgetfulWithBad.agree a.2
            (st_map a.1, false) Bool.noConfusion b_out (c_out, false) Bool.noConfusion
        · rfl
      · exact (hst' rfl).elim
    · exact (hst rfl).elim

/-- Quadratic birthday bound on the bad-flag probability of `forgetfulWithBad`: starting from
initial key caches `cache` with `bad = false`, an `n`-query-bounded program sets `bad = true`
with probability at most `(n * ∑ k, (cache k).length + n.choose 2) * (Fintype.card Block)⁻¹`. -/
theorem toOuterMeasure_bad_forgetfulWithBad_le {β : Type}
    {program : OracleComp (Spec Key Block) β} {n : ℕ}
    (hn : IsQueryBounded program n) (cache : Key → Cache Block) :
    ((OracleComp.interpret forgetfulWithBad program).run (cache, false)).toOuterMeasure
      {x | let (_, _, bad) := x; bad = true} ≤
      (n * (Finset.univ.sum (fun k => (cache k).length)) + n.choose 2 : ℕ) *
      (Fintype.card Block : ℝ≥0∞)⁻¹ := by
  refine OracleComp.toOuterMeasure_bad_choose_two_le
      (bad := fun st : (Key → Cache Block) × Bool => st.2 = true)
    (fun st : (Key → Cache Block) × Bool => Finset.univ.sum (fun k => (st.1 k).length))
    (Fintype.card Block : ℝ≥0∞)⁻¹ ?_ ?_ hn Bool.noConfusion
  · intro q ⟨c, b⟩ hb
    obtain rfl : b = false := Bool.eq_false_iff.mpr hb
    simp only [forgetfulWithBad, PMF.toOuterMeasure_map_apply, Set.preimage_ofPred_eq]
    cases hq : cachedAnswer (c q.1) q.2 with
    | some a => simp [RandomPermutation.forgetfulWithBad, hq, PMF.toOuterMeasure_pure_apply]
    | none =>
      have hpre : (fun a : Block => (a, (PermQuery.toCacheEntry ⟨q.2, a⟩ :: c q.1,
          false || decide (a ∉ freshAnswers (c q.1) q.2)))) ⁻¹'
          {x : Block × (Cache Block × Bool) | x.2.2 = true} =
          {a : Block | a ∉ freshAnswers (c q.1) q.2} := by ext a; simp
      have hcard : (Finset.univ.filter fun a : Block => a ∉ freshAnswers (c q.1) q.2).card
          ≤ (c q.1).length := by
        cases h_q2 : q.2 with
        | forward x =>
          simpa [freshAnswers, invLookup, Option.ne_none_iff_isSome] using
            Cslib.RandomOracle.card_filter_lookup_isSome_le ((c q.1).map Prod.swap)
        | inverse y =>
          simpa [freshAnswers, Option.ne_none_iff_isSome] using
            Cslib.RandomOracle.card_filter_lookup_isSome_le (c q.1)
      simp only [RandomPermutation.forgetfulWithBad, hq]
      rw [PMF.toOuterMeasure_map_apply, hpre, PMF.toOuterMeasure_uniformOfFintype]
      gcongr
      exact (Nat.cast_le.mpr hcard).trans (Nat.cast_le.mpr (Finset.single_le_sum
          (fun (k : Key) _ => Nat.zero_le (List.length (c k))) (Finset.mem_univ q.1)))
  · rintro q ⟨c, b⟩ _ ⟨a, c', b'⟩ hp _
    supp_cases hp [forgetfulWithBad] with ⟨⟨a₀, c₀, b₀⟩, hx, rfl, rfl, rfl⟩
    rcases RandomPermutation.mem_support_forgetfulWithBad hx with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩
    · simp [Function.update_eq_self]
    · have h1 := Finset.add_sum_erase Finset.univ
        (fun k => (Function.update c q.1
          (PermQuery.toCacheEntry ⟨q.2, a₀⟩ :: c q.1) k).length) (Finset.mem_univ q.1)
      have h2 := Finset.add_sum_erase Finset.univ (fun k => (c k).length) (Finset.mem_univ q.1)
      have heq : ∑ k ∈ Finset.univ.erase q.1,
          (Function.update c q.1 (PermQuery.toCacheEntry ⟨q.2, a₀⟩ :: c q.1) k).length =
          ∑ k ∈ Finset.univ.erase q.1, (c k).length :=
        Finset.sum_congr rfl fun k hk => by simp [(Finset.mem_erase.mp hk).1]
      simp only [Function.update_self, List.length_cons] at h1
      dsimp only
      omega

omit [Fintype Key] in
/-- A query step of `exactWithBad` preserves the invariant that every key's cache is a partial
bijection. -/
theorem exactWithBad_preserve_isPartialBijection (q : Query Key Block)
    (st : (Key → Cache Block) × Bool) (hst : ∀ k, IsPartialBijection (st.1 k)) (a : Block)
    (st' : (Key → Cache Block) × Bool)
    (hmem : (a, st') ∈ (exactWithBad q st).support) (k : Key) : IsPartialBijection (st'.1 k) := by
  rcases st' with ⟨_, _⟩
  supp_cases hmem [exactWithBad] with ⟨⟨b, c', bad'⟩, hmem, rfl, rfl, rfl⟩
  rcases eq_or_ne k q.1 with rfl | h
  · simpa using RandomPermutation.exactWithBad_preserve_isPartialBijection q.2 (st.1 q.1, st.2)
      (hst q.1) b (c', bad') hmem
  · simpa [Function.update_of_ne h] using hst k

omit [Fintype Key] in
/-- Dropping the bad flag after a step of `exactWithBad` recovers the law of `answer`, provided
every key's cache in `st.1` is a partial bijection. -/
theorem exactWithBad_map_fst (q : Query Key Block) (st : (Key → Cache Block) × Bool)
    (hcache : ∀ k, IsPartialBijection (st.1 k)) :
    (exactWithBad q st).map (fun (a, st') => (a, st'.1)) = answer q st.1 := by
  simpa only [exactWithBad, answer, PMF.map_comp, Function.comp_def] using
    congrArg (PMF.map fun x => (x.1, Function.update st.1 q.1 x.2))
      (RandomPermutation.exactWithBad_map_fst q.2 (st.1 q.1, st.2) (hcache q.1))

omit [Fintype Key] in
/-- Dropping the bad flag after a step of `forgetfulWithBad` recovers the law of
`forgetfulAnswer`. -/
theorem forgetfulWithBad_map_fst (q : Query Key Block) (st : (Key → Cache Block) × Bool) :
    (forgetfulWithBad q st).map (fun (a, st') => (a, st'.1)) = forgetfulAnswer q st.1 := by
  simpa only [forgetfulWithBad, forgetfulAnswer, PMF.map_comp, Function.comp_def] using
    congrArg (PMF.map fun x => (x.1, Function.update st.1 q.1 x.2))
      (RandomPermutation.forgetfulWithBad_map_fst q.2 (st.1 q.1, st.2))

omit [Fintype Key] in
/-- Dropping the final bad flag after running `program` under `exactWithBad` recovers the run
under `answer`, provided every key's initial cache is a partial bijection. -/
theorem run_interpret_exactWithBad_map_fst {β : Type}
    (program : OracleComp (Spec Key Block) β) (cache : Key → Cache Block) (bad : Bool)
    (hcache : ∀ k, IsPartialBijection (cache k)) :
    ((OracleComp.interpret exactWithBad program).run (cache, bad)).map
      (fun (a, st') => (a, st'.1)) =
    (OracleComp.interpret answer program).run cache :=
  OracleComp.run_interpret_map_state_of_invariant exactWithBad answer Prod.fst
    (fun s => ∀ k, IsPartialBijection (s.1 k))
    (fun q s hs a s' hmem k => exactWithBad_preserve_isPartialBijection q s hs a s' hmem k)
    (fun q s hs => exactWithBad_map_fst q s hs)
    program (cache, bad) hcache

omit [Fintype Key] in
/-- Dropping the final bad flag after running `program` under `forgetfulWithBad` recovers the run
under `forgetfulAnswer`. -/
theorem run_interpret_forgetfulWithBad_map_fst {β : Type}
    (program : OracleComp (Spec Key Block) β) (cache : Key → Cache Block) (bad : Bool) :
    ((OracleComp.interpret forgetfulWithBad program).run (cache, bad)).map
      (fun (a, st') => (a, st'.1)) =
    (OracleComp.interpret forgetfulAnswer program).run cache :=
  OracleComp.run_interpret_map_state forgetfulWithBad forgetfulAnswer Prod.fst
    forgetfulWithBad_map_fst program (cache, bad)

/-- Ideal-cipher switching bound (`ℝ`, two-sided): for any `Q`-query-bounded program `program`,
postprocessing kernel `next : β → PMF γ`, and outcome `c : γ`, the probabilities of outputting
`c` under independent uniformly random permutations `P : Key → Equiv.Perm Block` and under the
forgetful lazy sampler `forgetfulAnswer` (starting from empty caches) differ by at most
`Q.choose 2 * (Fintype.card Block)⁻¹`. -/
theorem abs_sub_uniformPerm_forgetful_le {β γ : Type}
    {program : OracleComp (Spec Key Block) β} {Q : ℕ}
    (hQ : IsQueryBounded program Q) (next : β → PMF γ) (c : γ) :
    |((do
        let a ← (do
          let P ← PMF.pi (fun _ : Key => PMF.uniformOfFintype (Equiv.Perm Block))
          OracleComp.interpret (fun (q : Query Key Block) =>
            PMF.pure (evalPerm (P q.1) q.2)) program)
        next a) c).toReal -
      ((do
        let a ← ((OracleComp.interpret forgetfulAnswer program).run (fun _ => [])).map Prod.fst
        next a) c).toReal| ≤
      (Q.choose 2 : ℝ) * (Fintype.card Block : ℝ)⁻¹ := by
  rw [uniform_interpret_eq_lazy,
    ← run_interpret_exactWithBad_map_fst program (fun _ => []) false
        (fun _ => isPartialBijection_nil),
    ← run_interpret_forgetfulWithBad_map_fst program (fun _ => []) false]
  simp only [pmf_norm]
  have hdiff := identicalUntilBad_exactWithBad_forgetfulWithBad.abs_sub_le
    program ((fun _ => []), false) (fun x => next x.1) c
  rw [identicalUntilBad_exactWithBad_forgetfulWithBad.bad_eq] at hdiff
  refine hdiff.trans ?_
  have hbad := toOuterMeasure_bad_forgetfulWithBad_le hQ (fun _ => [])
  simp only [List.length_nil, Finset.sum_const_zero, mul_zero, zero_add] at hbad
  have htop : ((Q.choose 2 : ℕ) : ℝ≥0∞) * (Fintype.card Block : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_inv] using
    ENNReal.toReal_mono htop hbad

end Finite

end Cslib.IdealCipher
