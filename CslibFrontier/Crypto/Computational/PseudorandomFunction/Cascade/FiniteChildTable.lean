/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomFunction.Cascade.ChildRoutingLaw
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.QueryBoundedSimulation

/-!
# Finite channel tables for cascade routing

A client with at most `q` external child queries can presample `q` independent child
functions. The finite oracle starts with no assigned channels, reads the sampled function
for the next channel when it is first used, and uses that same function on repeats.

## Main definitions

* `Cslib.Crypto.cascadeChildFiniteOracle` answers from a finite table in first-use order.

## Main results

* `Cslib.Crypto.runWith_cascadeChildChannelOracle_eq_finite` identifies the output law of the
  lazy channel oracle with its finite independent table for a query-bounded client.

## References

* [BonehShoup2023], v0.6, Section 4.6.1 (printed pp. 152–154) and Section 6.4.2
  (printed pp. 229–230), for the adjacent-hybrid step.
-/

public section

namespace Cslib.Crypto

open Probability

/-- Answer a child query from a finite table. The state counts the assigned channels.
Only the next unused channel may be assigned. A request outside the table or skipping ahead
returns the empty word and preserves the state. -/
@[expose]
noncomputable def cascadeChildFiniteOracle {count width n : ℕ}
    (table : Fin count → BitString width → BitString n) (request : ℕ × List Bool) :
    StateT ℕ PMF (List Bool) := fun assigned =>
  if h : request.1 < count ∧ request.1 ≤ assigned then
    PMF.pure
      (List.ofFn (table ⟨request.1, h.1⟩ (BitString.ofList width request.2)),
        max assigned (request.1 + 1))
  else PMF.pure ([], assigned)

private theorem channelCache_append {Row : Type} {count : ℕ} (rows : List Row) (row : Row)
    (hlen : rows.length < count) :
    (fun index : Fin count => (rows ++ [row])[index.val]?) =
      Function.update (fun index : Fin count => rows[index.val]?)
        ⟨rows.length, hlen⟩ (some row) := by
  funext index
  by_cases heq : index.val = rows.length
  · obtain rfl : index = ⟨rows.length, hlen⟩ := Fin.ext heq
    simp
  · rw [Function.update_of_ne (fun h => heq (congrArg Fin.val h))]
    by_cases hlt : index.val < rows.length
    · exact List.getElem?_append_left hlt
    · rw [List.getElem?_eq_none (Nat.le_of_not_gt hlt), List.getElem?_eq_none (by simp; omega)]

private noncomputable def completeChannels {Row : Type} [Finite Row] (count : ℕ)
    (source : PMF Row) (rows : List Row) : PMF (Fin count → Row) :=
  RandomOracle.complete (fun _ => source) (fun index => rows[index.val]?)

private theorem finiteStep {count width n : ℕ}
    (source : PMF (BitString width → BitString n))
    (remaining : ℕ) (request : ℕ × List Bool) (rows : List (BitString width → BitString n))
    (hinv : rows.length + (remaining + 1) ≤ count) :
    ((cascadeChildChannelOracle source request rows).bind fun x =>
        (completeChannels count source x.2).map fun table => (table, x.1, x.2.length)) =
      ((completeChannels count source rows).bind fun table =>
        (cascadeChildFiniteOracle table request rows.length).map fun y => (table, y.1, y.2)) ∧
    ∀ reply next, (reply, next) ∈ (cascadeChildChannelOracle source request rows).support →
      next.length + remaining ≤ count := by
  let respond (row : BitString width → BitString n) :=
    List.ofFn (row (BitString.ofList width request.2))
  cases hrow : rows[request.1]? with
  | some row =>
    have hindex : request.1 < rows.length := (List.getElem?_eq_some_iff.mp hrow).choose
    have hcap : request.1 < count := by omega
    refine ⟨?_, fun reply next hmem => ?_⟩
    · simp only [cascadeChildChannelOracle, hrow, cascadeChildFiniteOracle,
        dite_eq_left (And.intro hcap hindex.le), max_eq_left (Nat.succ_le_of_lt hindex),
        PMF.pure_bind, PMF.pure_map]
      change _ = (completeChannels count source rows).map
        fun table => (table, respond (table ⟨request.1, hcap⟩), rows.length)
      refine PMF.map_congr_on_support _ _ _ fun table htable => ?_
      rw [RandomOracle.complete_agrees (fun _ : Fin count => source)
        (fun index => rows[index.val]?) table htable ⟨request.1, hcap⟩ row hrow]
    · simp only [cascadeChildChannelOracle, hrow, PMF.mem_support_pure_iff] at hmem
      have := congrArg List.length (Prod.mk.inj hmem).2
      omega
  | none =>
    by_cases hnew : request.1 = rows.length
    · have hcap : rows.length < count := by omega
      let index : Fin count := ⟨rows.length, hcap⟩
      let cache : RandomOracle.Cache (fun _ : Fin count => BitString width → BitString n) :=
        fun index => rows[index.val]?
      have hmiss : cache index = none := List.getElem?_eq_none le_rfl
      have hread := RandomOracle.answer_complete (fun _ => source) cache index
      rw [RandomOracle.answer_of_none _ _ _ hmiss] at hread
      refine ⟨?_, fun reply next hmem => ?_⟩
      · simp only [cascadeChildChannelOracle, hnew, show rows[rows.length]? = none from hmiss,
          ↓reduceIte, PMF.bind_map, cascadeChildFiniteOracle, dite_eq_left (And.intro hcap le_rfl),
          max_eq_right (Nat.le_succ _), PMF.pure_map, List.length_append, List.length_singleton,
          Function.comp_def, completeChannels, channelCache_append rows _ hcap]
        simpa only [pmf_norm, cache, index, respond, PMF.map] using congrArg (PMF.map fun
          (e : (BitString width → BitString n) × (Fin count → BitString width → BitString n)) =>
          (e.2, respond e.1, rows.length + 1)) hread
      · simp only [cascadeChildChannelOracle, hnew, show rows[rows.length]? = none from hmiss,
          ↓reduceIte, PMF.mem_support_map_iff] at hmem
        obtain ⟨row, _, heq⟩ := hmem
        have hlen := congrArg List.length (Prod.mk.inj heq).2
        simp only [List.length_append, List.length_singleton] at hlen; omega
    · have hskip : ¬ (request.1 < count ∧ request.1 ≤ rows.length) := by
        have := List.getElem?_eq_none_iff.mp hrow
        omega
      refine ⟨by simp [cascadeChildChannelOracle, hrow, hnew, cascadeChildFiniteOracle, hskip,
        PMF.map, Function.comp_def], fun reply next hmem => ?_⟩
      simp only [cascadeChildChannelOracle, hrow, hnew, ↓reduceIte, PMF.mem_support_pure_iff]
        at hmem
      have := congrArg List.length (Prod.mk.inj hmem).2
      omega

/-- At most `count` child queries can consume at most `count` independent functions.
Drawing all of them up front preserves the output distribution, including adaptive calls,
repeated channels, and requests that skip an unseen channel. -/
theorem runWith_cascadeChildChannelOracle_eq_finite {α : Type} {count width n : ℕ}
    (source : PMF (BitString width → BitString n)) {program : WordOracleComp ℕ α}
    (hbudget : program.IsQueryBounded count) :
    (ProbOracleComp.runWith (cascadeChildChannelOracle source) program []).map Prod.fst =
      (PMF.pi (fun _ : Fin count => source)).bind fun table =>
        (ProbOracleComp.runWith (cascadeChildFiniteOracle table) program 0).map Prod.fst := by
  have hmap := congrArg (PMF.map fun output : (Fin count → BitString width → BitString n) ×
    α × ℕ => output.2.1) (hbudget.run_interpret_bind_comm_of_invariant
      (cascadeChildChannelOracle source) (fun table => cascadeChildFiniteOracle table)
      (completeChannels count source) List.length (fun rem rows => rows.length + rem ≤ count)
      (fun _ _ h => by omega) (finiteStep source) (s := []) (by simp)).1
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def,
    ← ProbOracleComp.runWith_eq_run_interpret] at hmap
  change (ProbOracleComp.runWith (cascadeChildChannelOracle source) program []).bind
      (fun x => (completeChannels count source x.2).map (Function.const _ x.1)) = _ at hmap
  simp only [PMF.map_const, completeChannels, List.getElem?_nil, RandomOracle.complete_empty,
    List.length_nil] at hmap
  simpa only [PMF.map, Function.comp_def] using hmap

end Cslib.Crypto
