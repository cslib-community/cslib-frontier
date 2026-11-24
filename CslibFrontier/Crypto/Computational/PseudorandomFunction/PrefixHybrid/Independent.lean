/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomFunction.PrefixFree
public import CslibFrontier.Crypto.Computational.PseudorandomFunction.PrefixHybrid.Eager
import CslibFrontier.Probability.PMF.Uniform

/-!
# Independent short and parent labels in the real prefix hybrid

A query ending at the cut can read a label directly. A strict extension of that query
would use the same label as its parent key, so prefix-free admissibility excludes
both uses on a single run. The real hybrid can therefore draw its short labels and
parent labels independently, including when queries depend on earlier answers.

This is the independence step for the real side of the cascade hybrid in [BonehShoup2023],
v0.6, Sections 4.6.1 (printed pp. 152–154) and 6.4.2 (printed pp. 229–230).
The later reduction uses the parent labels as keys for the next-block PRF calls.
-/

public section

namespace Cslib.Crypto

open Probability

/-- Use the short table at or before the cut and the parent table beyond it. Invalid queries
receive the empty word. The parent table is indexed by bounded prefixes for convenience. Only
its entries at the full cut length can be read. -/
@[expose]
def prefixHybridIndependentLabelOracle {n cut : ℕ} (valid : List Bool → Bool)
    (family : List Bool → List Bool → List Bool)
    (short parents : {word : List Bool // word.length ≤ cut} → BitString n)
    (query : List Bool) : List Bool :=
  if valid query then
    let key : {word : List Bool // word.length ≤ cut} := ⟨query.take cut, by simp⟩
    let label := if cut < query.length then parents key else short key
    family (List.ofFn label) (query.drop cut)
  else []

private theorem wordQueryRunDist_independentLabels {α : Type} {valid : List Bool → Bool}
    {family : List Bool → List Bool → List Bool} {n cut : ℕ}
    [Fintype {word : List Bool // word.length ≤ cut}] (program : WordOracleComp Unit α)
    (hlen : ∀ seed suffix, seed.length = n → (family seed suffix).length = n)
    (hpf : IsPrefixFreeOn valid n program) :
    let Table := {word : List Bool // word.length ≤ cut} → BitString n
    (PMF.uniformOfFintype (Table × Table)).bind (fun tables =>
      wordQueryRunDist (prefixHybridIndependentLabelOracle valid family tables.1 tables.1)
        program) =
    (PMF.uniformOfFintype (Table × Table)).bind (fun tables =>
      wordQueryRunDist (prefixHybridIndependentLabelOracle valid family tables.1 tables.2)
        program) := by
  classical
  let Key := {word : List Bool // word.length ≤ cut}
  let Table := Key → BitString n
  ext result
  by_cases hlog : WordPrefixFree valid result.2
  · -- Exchange the two labels only at prefixes used as parents in this log.
    let usedAsParent (key : Key) : Prop :=
      ∃ q ∈ result.2, valid q = true ∧ cut < q.length ∧ q.take cut = key.val
    let swap (tables : Table × Table) : Table × Table :=
      (fun key => if usedAsParent key then tables.2 key else tables.1 key,
        fun key => if usedAsParent key then tables.1 key else tables.2 key)
    have hswap : Function.Involutive swap := by
      intro tables
      apply Prod.ext <;> funext key <;> by_cases h : usedAsParent key <;> simp [swap, h]
    conv_rhs => rw [← PMF.uniformOfFintype_map_equiv hswap.toPerm, PMF.bind_map]
    simp only [PMF.bind_apply, Function.comp_def]
    apply tsum_congr
    intro tables
    congr 1
    apply wordQueryRunDist_apply_eq_of_agree
    intro query hquery
    cases hv : valid query
    · simp [prefixHybridIndependentLabelOracle, hv]
    · by_cases hcut : cut < query.length
      · have hused : usedAsParent ⟨query.take cut, by simp⟩ :=
          ⟨query, hquery, hv, hcut, rfl⟩
        simp [prefixHybridIndependentLabelOracle, hv, hcut, Function.Involutive.toPerm, swap, hused]
      · have hused : ¬ usedAsParent ⟨query.take cut, by simp⟩ := by
          rintro ⟨other, hother, hvalid, hlong, hsame⟩
          have hne : query ≠ other := by
            rintro rfl
            exact hcut hlong
          have hprefix : query.IsPrefix other := by
            have heq := hsame.trans (List.take_of_length_le (Nat.le_of_not_gt hcut))
            rw [← heq]
            exact List.take_prefix _ _
          exact hlog query hquery hv other hother hvalid hne hprefix
        simp [prefixHybridIndependentLabelOracle, hv, hcut, Function.Involutive.toPerm, swap, hused]
  · have hzero (short parents : Table) :
        wordQueryRunDist (prefixHybridIndependentLabelOracle valid family short parents)
          program result = 0 := by
      rw [PMF.apply_eq_zero_iff]
      intro hmem
      apply hlog
      refine hpf _ (fun q hq => by simp [prefixHybridIndependentLabelOracle, hq]) ?_ result hmem
      intro q hq
      simp only [prefixHybridIndependentLabelOracle, hq, ↓reduceIte]
      exact hlen _ _ List.length_ofFn
    simp [PMF.bind_apply, hzero]

/-- For an adaptive prefix-free client, the hybrid at the old cut has the same law with
independent short-label and parent-label tables. Correctly sized replies let the prefix-free
condition apply to every fixed table. -/
theorem eval_prefixHybridGame_eq_independentLabels (valid : ℕ → List Bool → Bool)
    (family : List Bool → List Bool → List Bool) (adversary : OracleDistinguisher) (n cut : ℕ)
    [Fintype {word : List Bool // word.length ≤ cut}]
    (hlen : ∀ seed suffix, seed.length = n → (family seed suffix).length = n)
    (hpf : IsPrefixFreeOn (valid n) n (adversary n [])) :
    let Table := {word : List Bool // word.length ≤ cut} → BitString n
    ProbComp.eval (prefixHybridGame valid family adversary n cut) =
      (PMF.uniformOfFintype (Table × Table)).bind fun tables =>
        OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
          (fun request => PMF.pure
            (prefixHybridIndependentLabelOracle (valid n) family tables.1 tables.2 request.2)))
          (adversary n []) := by
  let Table := {word : List Bool // word.length ≤ cut} → BitString n
  have hfst : (PMF.uniformOfFintype (Table × Table)).map Prod.fst =
      PMF.uniformOfFintype Table := PMF.uniformOfFintype_prod_map_fst
  have horacle (table : Table) (query : List Bool) :
      (if valid n query then family (List.ofFn (table ⟨query.take cut, by simp⟩))
        (query.drop cut) else []) =
      prefixHybridIndependentLabelOracle (valid n) family table table query := by
    by_cases h : cut < query.length <;> simp [prefixHybridIndependentLabelOracle, h]
  rw [eval_prefixHybridGame_eq_eager, ← hfst, PMF.bind_map]
  simp only [Function.comp_def, horacle, ← map_fst_wordQueryRunDist, ← PMF.map_bind]
  exact congrArg (PMF.map Prod.fst) (wordQueryRunDist_independentLabels (cut := cut)
    (adversary n []) hlen hpf)

end Cslib.Crypto
