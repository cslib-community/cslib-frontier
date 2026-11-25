/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomFunction.Cascade.ChildRouting
public import CslibFrontier.Languages.Probabilistic.RandomOracle
import CslibFrontier.Languages.Probabilistic.Oracle.Norm

/-!
# Distribution of adaptive cascade child routing

When child functions are independently sampled in channel order, the cascade router has
the same law as sampling them by parent prefix. This is a distribution-level step of the
adjacent-hybrid argument in [BonehShoup2023], v0.6, Sections 4.6.1 (printed pp. 152–154)
and 6.4.2 (printed pp. 229–230).

## Main definitions

* `Cslib.Crypto.cascadeChildChannelOracle`: assign child functions to successive channels.
* `Cslib.Crypto.CascadeChildPrefixState`: the two caches of the prefix-indexed game.
* `Cslib.Crypto.cascadeChildPrefixOracle`: answer a query using its prefix and these caches.
* `Cslib.Crypto.cascadeChildPrefixGame`: run an adaptive client against this oracle.

## Main results

* `Cslib.Crypto.runWith_cascadeChildRouter_eq_prefixGame`: assigning independent child functions
  to first-use channel numbers preserves the output law of the adaptive client.
-/

public section

namespace Cslib.Crypto

open Probability

/-- The child oracle assigns an independent function to the next channel on its first use.
It reuses earlier functions and gives an empty reply to a channel that skips this order. -/
@[expose]
noncomputable def cascadeChildChannelOracle {width n : ℕ}
    (distribution : PMF (BitString width → BitString n)) (request : ℕ × List Bool) :
    StateT (List (BitString width → BitString n)) PMF (List Bool) := fun rows =>
  let respond := fun row : BitString width → BitString n =>
    List.ofFn (row (BitString.ofList width request.2))
  match rows[request.1]? with
  | some row => PMF.pure (respond row, rows)
  | none => if request.1 = rows.length then
      distribution.map fun row => (respond row, rows ++ [row])
    else PMF.pure ([], rows)

/-- The cached assignments in the prefix-indexed child game.
`width` is the input size of each child function and `n` is its output size. -/
structure CascadeChildPrefixState (width n : ℕ) where
  /-- Labels already assigned to valid queries at or before the cut. -/
  shortLabels : List (List Bool × List Bool)
  /-- Child functions already assigned to parents, keyed by the parent prefix word. -/
  parentRows : RandomOracle.Cache (fun _ : List Bool => BitString width → BitString n)

/-- Read or sample a short label or the child function for a long query's parent.
Invalid queries return the empty word and leave both caches untouched. -/
@[expose]
noncomputable def cascadeChildPrefixOracle (valid : List Bool → Bool) (inLen : ℕ → ℕ)
    (family : List Bool → List Bool → List Bool) (n depth : ℕ)
    (distribution : PMF (BitString (inLen n) → BitString n)) (query : List Bool) :
    StateT (CascadeChildPrefixState (inLen n) n) PMF (List Bool) := fun cache =>
  if valid query then
    let width := inLen n
    let cut := depth * width
    if cut < query.length then
      let suffix := query.drop cut
      (RandomOracle.answer (fun _ => distribution) (query.take cut) cache.parentRows).map
        fun (row, rows) =>
          (cascadeFamily inLen family (List.ofFn (row (BitString.ofList width (suffix.take width))))
            (suffix.drop width), { cache with parentRows := rows })
    else
      (cachedDistOracle (fun _ => true) (BitString.uniformList n) query cache.shortLabels).map
        fun (label, short) => (label, { cache with shortLabels := short })
  else PMF.pure ([], cache)

/-- Sample each valid short word's label independently, and each long query's child function
independently at its parent prefix. Both assignments are retained for subsequent queries.
The child's input is the next block padded to width if the caller allows a partial block. -/
@[expose]
noncomputable def cascadeChildPrefixGame (valid : List Bool → Bool) (inLen : ℕ → ℕ)
    (family : List Bool → List Bool → List Bool) (n depth : ℕ)
    (distribution : PMF (BitString (inLen n) → BitString n))
    (program : WordOracleComp Unit Bool) : PMF Bool :=
  (ProbOracleComp.runWith (fun request =>
    cascadeChildPrefixOracle valid inLen family n depth distribution request.2)
      program ⟨[], fun _ => none⟩).map Prod.fst

private theorem cache_append {α : Type} (parents : List (List Bool)) (rows : List α)
    (hlen : parents.length = rows.length) (parent : List Bool) (hfresh : parent ∉ parents)
    (row : α) :
    (fun key => (rows ++ [row])[(parents ++ [parent]).idxOf key]?) =
      Function.update (fun key => rows[parents.idxOf key]?) parent (some row) := by
  funext key
  by_cases heq : key = parent
  · subst key
    simp [List.idxOf_append_of_notMem hfresh, hlen]
  · rw [Function.update_of_ne heq]
    by_cases hmem : key ∈ parents
    · rw [List.idxOf_append_of_mem hmem,
        List.getElem?_append_left (hlen ▸ List.idxOf_lt_length_iff.mpr hmem)]
    · simp [List.idxOf_append_of_notMem hmem, List.idxOf_eq_length_iff.mpr hmem, heq, hlen]

private abbrev RoutedState (width n : ℕ) :=
  CascadeChildRouterState × List (BitString width → BitString n)

private def toPrefixState {width n : ℕ} (state : RoutedState width n) :
    CascadeChildPrefixState width n :=
  ⟨state.1.shortLabels, fun key => state.2[state.1.parents.idxOf key]?⟩

private def alignedState {width n : ℕ} (state : RoutedState width n) : Prop :=
  state.1.parents.length = state.2.length

private noncomputable def routedOracle (valid : List Bool → Bool) (inLen : ℕ → ℕ)
    (family : List Bool → List Bool → List Bool) (n depth : ℕ)
    (distribution : PMF (BitString (inLen n) → BitString n))
    (query : List Bool) : StateT (RoutedState (inLen n) n) PMF (List Bool) := fun state =>
  (ProbOracleComp.runWith (cascadeChildChannelOracle distribution)
    (cascadeChildRoute valid inLen family n depth query state.1) state.2).map
      (fun ((reply, router), rows) => (reply, router, rows))

private theorem routedOracle_step (valid : List Bool → Bool) (inLen : ℕ → ℕ)
    (family : List Bool → List Bool → List Bool) (n depth : ℕ)
    (distribution : PMF (BitString (inLen n) → BitString n)) (query : List Bool)
    (state : RoutedState (inLen n) n) (hstate : alignedState state) :
    ((routedOracle valid inLen family n depth distribution query state).map
      (fun (reply, next) => (reply, toPrefixState next)) =
      cascadeChildPrefixOracle valid inLen family n depth distribution query
        (toPrefixState state)) ∧
    ∀ reply next, (reply, next) ∈
      (routedOracle valid inLen family n depth distribution query state).support →
        alignedState next := by
  obtain ⟨⟨parents, short⟩, rows⟩ := state
  change parents.length = rows.length at hstate
  by_cases hv : valid query = true
  · by_cases hl : depth * inLen n < query.length
    · let parent := query.take (depth * inLen n)
      let suffix := query.drop (depth * inLen n)
      let respond (row : BitString (inLen n) → BitString n) :=
        cascadeFamily inLen family
          (List.ofFn (row (BitString.ofList (inLen n) (suffix.take (inLen n)))))
          (suffix.drop (inLen n))
      by_cases hmem : parent ∈ parents
      · have hi : parents.idxOf parent < parents.length := List.idxOf_lt_length_iff.mpr hmem
        have hrow : rows[parents.idxOf parent]? = some (rows[parents.idxOf parent]'(hstate ▸ hi)) :=
          List.getElem?_eq_getElem (hstate ▸ hi)
        rw [show routedOracle valid inLen family n depth distribution query
              (⟨parents, short⟩, rows) =
            PMF.pure (respond (rows[parents.idxOf parent]'(hstate ▸ hi)),
              ⟨parents, short⟩, rows) by
          simp [routedOracle, cascadeChildRoute, hv, hl, parent, suffix, hi.ne, hrow,
            cascadeChildChannelOracle, pmf_norm, respond, List.take_of_length_le]]
        refine ⟨by simp [cascadeChildPrefixOracle, hv, hl, toPrefixState, RandomOracle.answer,
            parent, suffix, hrow, respond, pmf_norm], fun _ _ hnext => ?_⟩
        exact (Prod.mk.inj ((PMF.mem_support_pure_iff _ _).mp hnext)).2 ▸ hstate
      · have hi : parents.idxOf parent = parents.length := List.idxOf_eq_length_iff.mpr hmem
        have hrow : rows[parents.idxOf parent]? = none := List.getElem?_eq_none (hi.trans hstate).ge
        rw [show routedOracle valid inLen family n depth distribution query
              (⟨parents, short⟩, rows) =
            distribution.map (fun row => (respond row, ⟨parents ++ [parent], short⟩,
              rows ++ [row])) by
          simp [routedOracle, cascadeChildRoute, hv, hl, cascadeChildChannelOracle,
            parent, suffix, hi, hstate, respond, List.take_of_length_le, pmf_norm]]
        refine ⟨by simp [cascadeChildPrefixOracle, hv, hl, toPrefixState, RandomOracle.answer,
            hrow, parent, suffix, cache_append parents rows hstate parent hmem, respond,
            PMF.map_comp, Function.comp_def], fun _ _ hnext => ?_⟩
        obtain ⟨_, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hnext
        obtain rfl := (Prod.mk.inj heq).2
        simp [alignedState, hstate]
    · rw [show routedOracle valid inLen family n depth distribution query
            (⟨parents, short⟩, rows) =
          (cachedDistOracle (fun _ => true) (BitString.uniformList n) query short).map
            (fun (reply, short') => (reply, ⟨parents, short'⟩, rows)) by
        simp [routedOracle, cascadeChildRoute, hv, hl, cachedRandomFunctionOracle,
          eval_cachedSamplerOracle, BitString.eval_sampleList, PMF.map_comp, Function.comp_def,
          pmf_norm]]
      refine ⟨by simp [cascadeChildPrefixOracle, hv, hl, toPrefixState, PMF.map_comp,
          Function.comp_def], fun _ _ hnext => ?_⟩
      obtain ⟨⟨_, _⟩, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hnext
      exact (Prod.mk.inj heq).2 ▸ hstate
  · simp [routedOracle, cascadeChildRoute, cascadeChildPrefixOracle, hv, hstate, alignedState,
      PMF.pure_map]

/-- The first-use numbering of child functions preserves the output law for arbitrary adaptive
cascade clients. The channel oracle is used in order even though its interface accepts any
natural number. -/
theorem runWith_cascadeChildRouter_eq_prefixGame (valid : List Bool → Bool) (inLen : ℕ → ℕ)
    (family : List Bool → List Bool → List Bool) (n depth : ℕ)
    (distribution : PMF (BitString (inLen n) → BitString n))
    (program : WordOracleComp Unit Bool) :
    (ProbOracleComp.runWith (cascadeChildChannelOracle distribution)
      (cascadeChildRouter valid inLen family n depth program) []).map Prod.fst =
      cascadeChildPrefixGame valid inLen family n depth distribution program := by
  unfold cascadeChildRouter cascadeChildPrefixGame
  rw [ProbOracleComp.runWith_map, ProbOracleComp.runWith_run_interpret]
  simpa only [routedOracle, toPrefixState, StateT.run, List.getElem?_nil, PMF.map_comp,
    Function.comp_def, Prod.map_apply, id_eq] using congrArg (PMF.map Prod.fst)
      (ProbOracleComp.runWith_map_state_of_invariant
        (fun (req : Unit × List Bool) s =>
          routedOracle valid inLen family n depth distribution req.2 s)
        (fun req => cascadeChildPrefixOracle valid inLen family n depth distribution req.2)
        toPrefixState alignedState
        (fun req s hs => (routedOracle_step valid inLen family n depth distribution req.2 s hs).2)
        (fun req s hs => (routedOracle_step valid inLen family n depth distribution req.2 s hs).1)
        program (⟨[], []⟩, []) rfl)

end Cslib.Crypto
