/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomFunction.Cascade.ChildRouting
public import CslibFrontier.Languages.Probabilistic.UniformNat

/-!
# Single-key challenge program for cascade child channels

A client uses natural-number channels in order of first visit. The program draws a challenge
index using fair bits and rejects indices outside the channel budget. It memoizes random replies
on earlier channels, forwards the selected channel to a single external word oracle, and uses
independent private keys for later channels. Inputs are read as fixed-width blocks and replies
are capped at the state width.

## Main definitions

* `Cslib.Crypto.CascadeChildChallengeState`: first-use cursor and lazy answer cache.
* `Cslib.Crypto.cascadeChildChallengeHandler`: one simulated child query.
* `Cslib.Crypto.cascadeChildChallengeAtProgram`: simulate the client at a fixed index and key word.
* `Cslib.Crypto.cascadeChildChallengeProgram`: sample the challenge index and private keys,
  then simulate the client.

## Main results

* `Cslib.Crypto.isQueryBounded_cascadeChildChallengeProgram`: the simulation preserves
  the client's external query bound. The game law and strict oracle-PPT certificate for the
  program remain open (#5801).

## References

* [BonehShoup2023], v0.6, Section 4.6.1 (printed pp. 152–154) and Section 6.4.2
  (printed pp. 229–230), for the adjacent-hybrid step.
-/

public section

namespace Cslib.Crypto

open Probability

/-- State of the single-key simulation. The cursor counts channels already assigned, and
only channels before the challenge need an answer cache. -/
structure CascadeChildChallengeState where
  /-- Number of child channels assigned in first-use order. -/
  assigned : ℕ
  /-- Sampled ideal answers, keyed by channel number and normalized block. -/
  idealAnswers : List ((ℕ × List Bool) × List Bool)

/-- Answer a request for an already assigned channel or the next unused channel, below
`count`. Earlier channels have independent lazy random functions, `selected` calls the
external oracle, and later channels use separate `n`-bit rows of `keys`. -/
@[expose]
noncomputable def cascadeChildChallengeHandler
    (family : List Bool → List Bool → List Bool) (width n count selected : ℕ)
    (keys : List Bool) (request : ℕ × List Bool) (state : CascadeChildChallengeState) :
    WordOracleComp Unit (List Bool × CascadeChildChallengeState) :=
  if request.1 < count ∧ request.1 ≤ state.assigned then
    let block := BitString.listRow width 0 request.2
    let next := { state with assigned := max state.assigned (request.1 + 1) }
    if request.1 < selected then do
      let (reply, cache) ← ProbOracleComp.sample
        (memoize (fun _ => BitString.sampleList n) (request.1, block) state.idealAnswers)
      return (reply, { next with idealAnswers := cache })
    else if request.1 = selected then do
      let reply ← ProbOracleComp.query ((), block)
      return (reply.take n, next)
    else pure ((family (BitString.listRow n request.1 keys) block).take n, next)
  else pure ([], state)

/-- Run the simulated child oracle from an empty state with a fixed challenge channel and
key word. The sampled wrapper rejects out-of-range channels before calling this program. -/
@[expose]
noncomputable def cascadeChildChallengeAtProgram
    (family : List Bool → List Bool → List Bool) (width n count selected : ℕ)
    (keys : List Bool) (program : WordOracleComp ℕ Bool) : WordOracleComp Unit Bool :=
  Prod.fst <$> (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
      (cascadeChildChallengeHandler family width n count selected keys))
    program).run ⟨0, []⟩

/-- Sample a challenge index from `indexBits` fair bits. If it is in range, draw one private
`n`-bit key per channel and run the client with the simulated child oracle. An out-of-range
index returns `false` before the client runs. -/
@[expose]
noncomputable def cascadeChildChallengeProgram
    (family : List Bool → List Bool → List Bool) (width n count indexBits : ℕ)
    (program : WordOracleComp ℕ Bool) : WordOracleComp Unit Bool := do
  let selected ← ProbOracleComp.sample (ProbComp.sampleBinaryNat indexBits)
  if selected < count then
    let keys ← ProbOracleComp.sample (BitString.sampleList (count * n))
    cascadeChildChallengeAtProgram family width n count selected keys program
  else pure false

private theorem isQueryBounded_cascadeChildChallengeHandler
    (family : List Bool → List Bool → List Bool) (width n count selected : ℕ)
    (keys : List Bool) (request : ℕ × List Bool) (state : CascadeChildChallengeState) :
    ProbOracleComp.IsQueryBounded
      (cascadeChildChallengeHandler family width n count selected keys request state) 1 := by
  unfold cascadeChildChallengeHandler
  split
  · dsimp only
    split
    · exact ((ProbOracleComp.IsQueryBounded.sample _).bind fun _ => .pure _ 0).mono (by decide)
    · split
      · exact (ProbOracleComp.IsQueryBounded.query _).bind fun _ => .pure _ 0
      · exact .pure _ 1
  · exact .pure _ 1

/-- Local key and answer sampling consumes no external queries. The challenge channel forwards
at most one external query per client query. -/
theorem isQueryBounded_cascadeChildChallengeProgram
    (family : List Bool → List Bool → List Bool) (width n count indexBits : ℕ)
    {program : WordOracleComp ℕ Bool} {budget : ℕ}
    (hbudget : program.IsQueryBounded budget) :
    ProbOracleComp.IsQueryBounded
      (cascadeChildChallengeProgram family width n count indexBits program) budget := by
  unfold cascadeChildChallengeProgram
  refine ((ProbOracleComp.IsQueryBounded.sample _).bind (m := budget) fun selected => ?_).mono
    (by simp)
  split
  · refine ((ProbOracleComp.IsQueryBounded.sample _).bind (m := budget) fun keys => ?_).mono
      (by simp)
    unfold cascadeChildChallengeAtProgram
    apply (OracleComp.isCostBounded_map_iff _ _ _).mpr
    refine OracleComp.IsCostBounded.run_interpret (fun query state => ?_) hbudget _
    cases query with
    | inl k =>
      change ((StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k))).run state).IsQueryBounded 0
      rw [StateT.run_lift, bind_pure_comp]
      exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
        (ProbOracleComp.IsQueryBounded.sample _)
    | inr request =>
      exact isQueryBounded_cascadeChildChallengeHandler family width n count selected keys
        request state
  · exact .pure _ budget

end Cslib.Crypto
