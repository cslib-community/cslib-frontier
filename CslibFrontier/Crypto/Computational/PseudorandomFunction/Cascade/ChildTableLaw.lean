/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomFunction.Cascade.ChildRoutingLaw
public import CslibFrontier.Crypto.Computational.PseudorandomFunction.Cascade.ChildTables
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.RunWith
import CslibFrontier.Languages.Probabilistic.RandomOracle.Probabilistic
import CslibFrontier.Languages.Probabilistic.RandomOracle.Sum
import CslibFrontier.Probability.Product.Split

/-!
# Eager table law for cascade child routing

At a cut in the cascade, sampling the short labels and child functions on their first use gives
the same law as drawing both tables before the adaptive client runs. The short-word indices and
parent indices use separate random-oracle caches, even when both index the same word.

## Main results

* `Cslib.Crypto.cascadeChildPrefixGame_eq_childTableGame`: identify the prefix-indexed game with
  the eager table game for any common child-function distribution.

## References

* [BonehShoup2023], v0.6, Section 4.6.1 (printed pp. 152–154) and Section 6.4.2
  (printed pp. 229–230), for the adjacent-hybrid step.
-/

public section

namespace Cslib.Crypto

open Probability
open scoped Cslib

private abbrev ShortWord (cut : ℕ) := {word : List Bool // word.length ≤ cut}

private abbrev ShortSpec (cut n : ℕ) := fun _ : ShortWord cut => BitString n

private abbrev ChildSpec (cut width n : ℕ) :=
  ShortSpec cut n ⊕ₒ (fun _ : BitString cut => BitString width → BitString n)

private noncomputable def tableDist {cut width n : ℕ}
    (child : PMF (BitString width → BitString n)) :
    (q : ShortWord cut ⊕ BitString cut) → PMF (ChildSpec cut width n q) :=
  OracleComp.sumHandler (fun _ => PMF.uniformOfFintype (BitString n)) (fun _ => child)

private def shortCache {cut n : ℕ} (cache : List (List Bool × List Bool)) :
    RandomOracle.Cache (ShortSpec cut n) :=
  fun query => (cache.lookup query.val).map (BitString.ofList n)

private def tableCache {cut width n : ℕ} (state : CascadeChildPrefixState width n) :
    RandomOracle.Cache (ChildSpec cut width n) :=
  RandomOracle.Cache.sum (shortCache state.shortLabels)
    (fun parent => state.parentRows (List.ofFn parent))

private def tableQuery {n : ℕ} (valid : List Bool → Bool) (cut width : ℕ)
    (evaluate : List Bool → List Bool → List Bool) (request : Unit × List Bool) :
    ProbOracleComp (ChildSpec cut width n) (List Bool) :=
  let query := request.2
  if valid query then
    if h : query.length ≤ cut then
      List.ofFn <$> ProbOracleComp.query (spec := ChildSpec cut width n) (.inl ⟨query, h⟩)
    else
      (fun row => evaluate (List.ofFn (row (BitString.ofList width (query.drop cut))))
        (query.drop (cut + width))) <$>
        ProbOracleComp.query (spec := ChildSpec cut width n) (.inr (BitString.ofList cut query))
  else pure []

private theorem shortCache_cons {cut n : ℕ} (cache : List (List Bool × List Bool))
    (query : ShortWord cut) (label : BitString n) :
    shortCache ((query.val, List.ofFn label) :: cache) =
      Function.update (shortCache cache) query (some label) := by
  funext word
  by_cases h : word = query
  · subst word
    simp [shortCache, BitString.ofList_ofFn]
  · simp [shortCache, Function.update_of_ne h, List.lookup_cons,
      beq_eq_false_iff_ne.mpr fun hv => h (Subtype.ext hv)]

private theorem shortCall_map {cut n : ℕ} (query : ShortWord cut)
    (cache : List (List Bool × List Bool))
    (hlen : ∀ entry ∈ cache, entry.2.length = n) :
    (cachedDistOracle (fun _ => true) (BitString.uniformList n) query.val cache).map
      (fun (label, next) => (label, shortCache next)) =
      (RandomOracle.answer (fun _ => PMF.uniformOfFintype (BitString n)) query
        (shortCache cache)).map (fun (label, next) => (List.ofFn label, next)) := by
  cases hc : cache.lookup query.val with
  | none =>
    rw [cachedDistOracle, ite_eq_left rfl, memoize_of_none _ _ _ hc,
      RandomOracle.answer_of_none _ _ _ (by simp [shortCache, hc])]
    simp [BitString.uniformList, shortCache_cons, PMF.map, pmf_norm]
  | some label =>
    obtain ⟨_, _, hcache, _⟩ := List.lookup_eq_some_iff.mp hc
    simp [cachedDistOracle, memoize_of_some _ _ _ _ hc, RandomOracle.answer, shortCache,
      hc, BitString.ofFn_ofList (hlen (query.val, label) (by simp [hcache])), pmf_norm]

private theorem tableStep {n depth : ℕ} (valid : List Bool → Bool) (inLen : ℕ → ℕ)
    (family : List Bool → List Bool → List Bool) (child : PMF (BitString (inLen n) → BitString n))
    (request : Unit × List Bool) (state : CascadeChildPrefixState (inLen n) n)
    (hlen : ∀ entry ∈ state.shortLabels, entry.2.length = n) :
    (cascadeChildPrefixOracle valid inLen family n depth child request.2 state).map
      (fun (reply, next) => (reply, tableCache (cut := depth * inLen n) next)) =
      ProbOracleComp.runWith (RandomOracle.answer (tableDist child))
        (tableQuery valid (depth * inLen n) (inLen n) (cascadeFamily inLen family) request)
        (tableCache state) := by
  by_cases hv : valid request.2 = true
  · by_cases hl : request.2.length ≤ depth * inLen n
    · simp only [cascadeChildPrefixOracle, tableQuery, hv, ↓reduceIte, Nat.not_lt.mpr hl,
        dite_eq_left hl, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, tableCache,
        tableDist, RandomOracle.answer_sum_inl, PMF.map_comp, Function.comp_def, Prod.map_apply,
        id_eq]
      simpa only [PMF.map_comp, Function.comp_def] using congrArg
        (PMF.map fun (label, next) => (label, RandomOracle.Cache.sum next
          fun parent : BitString (depth * inLen n) => state.parentRows (List.ofFn parent)))
        (shortCall_map ⟨request.2, hl⟩ state.shortLabels hlen)
    · let parent := BitString.ofList (depth * inLen n) request.2
      have hparent : List.ofFn parent = request.2.take (depth * inLen n) :=
        (congrArg List.ofFn (BitString.ofList_take _ _).symm).trans
          (BitString.ofFn_ofList (by simp [Nat.min_eq_left (Nat.le_of_not_ge hl)]))
      simp only [cascadeChildPrefixOracle, tableQuery, hv, ↓reduceIte, Nat.lt_of_not_ge hl,
        dite_eq_right hl, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, tableCache,
        tableDist, RandomOracle.answer_sum_inr, PMF.map_comp, Function.comp_def, Prod.map_apply,
        id_eq, BitString.ofList_take, List.drop_drop]
      cases hc : state.parentRows (List.ofFn parent) with
      | none =>
        simp [RandomOracle.answer, parent, hc, hparent ▸ hc, ← hparent, PMF.map_comp,
          Function.comp_def,
          Function.update_comp_eq_of_injective' state.parentRows List.ofFn_injective]
      | some row => simp [RandomOracle.answer, parent, hc, hparent ▸ hc, pmf_norm]
  · simp [cascadeChildPrefixOracle, tableQuery, hv, pmf_norm]

private theorem tableStep_width {n depth : ℕ} (valid : List Bool → Bool) (inLen : ℕ → ℕ)
    (family : List Bool → List Bool → List Bool) (child : PMF (BitString (inLen n) → BitString n))
    (request : Unit × List Bool) (state : CascadeChildPrefixState (inLen n) n)
    (hlen : ∀ entry ∈ state.shortLabels, entry.2.length = n) (reply : List Bool)
    (next : CascadeChildPrefixState (inLen n) n)
    (hs : (reply, next) ∈
      (cascadeChildPrefixOracle valid inLen family n depth child request.2 state).support) :
    ∀ entry ∈ next.shortLabels, entry.2.length = n := by
  by_cases hv : valid request.2 = true
  · by_cases hl : depth * inLen n < request.2.length
    · simp only [cascadeChildPrefixOracle, hv, hl, ↓reduceIte, PMF.mem_support_map_iff] at hs
      obtain ⟨_, _, heq⟩ := hs
      exact (Prod.mk.inj heq).2 ▸ hlen
    · simp only [cascadeChildPrefixOracle, hv, hl, ↓reduceIte, PMF.mem_support_map_iff,
        cachedDistOracle] at hs
      obtain ⟨⟨label, cache⟩, hb, heq⟩ := hs
      exact (Prod.mk.inj heq).2 ▸ (RandomOracle.memoize_invariant
        (fun _ : List Bool => BitString.uniformList n) (fun _ l => l.length = n) request.2
        state.shortLabels hlen (fun _ => BitString.length_of_mem_support_uniformList)
        (label, cache) hb).2
  · simp only [cascadeChildPrefixOracle, ite_eq_right hv, PMF.mem_support_pure_iff] at hs
    exact (Prod.mk.inj hs).2 ▸ hlen

/-- The lazy prefix game has the eager child-table law with independent child functions.
This holds for adaptive clients with private coins and repeated queries. -/
theorem cascadeChildPrefixGame_eq_childTableGame (valid : ℕ → List Bool → Bool)
    (inLen : ℕ → ℕ) (family : List Bool → List Bool → List Bool)
    (adversary : OracleDistinguisher) (n depth : ℕ)
    [Fintype {word : List Bool // word.length ≤ depth * inLen n}]
    (child : PMF (BitString (inLen n) → BitString n)) :
    cascadeChildPrefixGame (valid n) inLen family n depth child (adversary n []) =
      cascadeChildTableGame valid inLen family adversary n depth (PMF.pi (fun _ => child)) := by
  let cut := depth * inLen n
  let adapt := tableQuery (n := n) (valid n) cut (inLen n) (cascadeFamily inLen family)
  let distribution := tableDist (cut := cut) child
  let program := ProbOracleComp.simulate adapt (adversary n [])
  let initial : CascadeChildPrefixState (inLen n) n := ⟨[], fun _ => none⟩
  have hnil : tableCache (cut := cut) initial = fun _ => none := funext fun k => by cases k <;> rfl
  have hsim := ProbOracleComp.runWith_map_state_of_invariant
    (fun request : Unit × List Bool => cascadeChildPrefixOracle (valid n) inLen family n depth
      child request.2)
    (fun request => ProbOracleComp.runWith (RandomOracle.answer distribution) (adapt request))
    (tableCache (cut := cut)) (fun state => ∀ entry ∈ state.shortLabels, entry.2.length = n)
    (tableStep_width (valid n) inLen family child)
    (tableStep (valid n) inLen family child) (adversary n []) initial (by simp [initial])
  calc
    _ = (ProbOracleComp.runWith (RandomOracle.answer distribution) program
          (fun _ => none)).map Prod.fst := by
      simpa only [cascadeChildPrefixGame, PMF.map_comp, Function.comp_def, hnil, program,
        ProbOracleComp.runWith_simulate] using congrArg (PMF.map Prod.fst) hsim
    _ = (PMF.pi distribution).bind (fun table =>
          OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
            (fun key => PMF.pure (table key))) program) :=
      (RandomOracle.interpret_prob_eq_lazy distribution program).symm
    _ = _ := by
      have hreply (table : (key : ShortWord cut ⊕ BitString cut) →
          ChildSpec cut (inLen n) n key) (request : Unit × List Bool) :
          OracleComp.interpret
            (OracleComp.sumHandler ProbComp.unifOracle (fun key => PMF.pure (table key)))
            (adapt request) = PMF.pure (if valid n request.2 then
              prefixHybridSplitAnswer (cascadeFamily inLen family)
                (fun word => table (.inl word)) (fun parent => table (.inr parent)) request.2
            else []) := by
        by_cases hv : valid n request.2 = true
        · by_cases hl : request.2.length ≤ cut
          · simp [adapt, tableQuery, hv, hl, prefixHybridSplitAnswer_of_length_le hl, pmf_norm]
          · simp [adapt, tableQuery, hv, hl,
              prefixHybridSplitAnswer_of_lt_length (Nat.lt_of_not_ge hl), pmf_norm]
        · simp [adapt, tableQuery, hv, pmf_norm]
      simp only [program, ProbOracleComp.interpret_simulate, hreply]
      let eager (short : ShortWord cut → BitString n)
          (children : BitString cut → BitString (inLen n) → BitString n) :=
        OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle (fun request =>
          PMF.pure (if valid n request.2 then
            prefixHybridSplitAnswer (cascadeFamily inLen family) short children request.2
          else []))) (adversary n [])
      rw [PMF.bind_pi_sum (β := ChildSpec cut (inLen n) n) distribution eager]
      change ((PMF.pi fun _ : ShortWord cut => PMF.uniformOfFintype (BitString n)).bind
        fun short => (PMF.pi fun _ : BitString cut => child).bind (eager short)) = _
      rw [PMF.pi_uniformOfFintype]; rfl

end Cslib.Crypto
