/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomFunction.Cascade.FiniteChildTable
public import CslibFrontier.Crypto.Game
import CslibFrontier.Crypto.Game.Hybrid
import CslibFrontier.Probability.Product

/-!
# Sampled child-channel challenge for cascade routing

To compare the two child-function laws for a query-bounded cascade router, order its channels
by first use. Pick one channel for the challenge, with ideal rows before it and real rows after
it. Compared with changing all rows, choosing the challenge channel uniformly loses exactly
the size of the sampled range. Indices beyond the query budget reject in both experiments,
allowing a power-of-two sampling range.

## Main definitions

* `Cslib.Crypto.cascadeChildChallengeAt`: run the finite child oracle with one externally
  supplied child function.
* `Cslib.Crypto.cascadeChildChallengeGame`: sample the channel and challenge function.

## Main results

* `Cslib.Crypto.advantage_cascadeChildChannelOracle_eq`: exact loss for a sampled challenge
  channel. This is the distribution step. The word oracle implementation and its strict
  oracle-PPT certificate are part of the remaining reduction (#5801).

## References

* [BonehShoup2023], v0.6, Section 4.6.1 (printed pp. 152–154) and Section 6.4.2
  (printed pp. 229–230), for the adjacent-hybrid step.
-/

public section

namespace Cslib.Crypto

open Probability

/-- Run the client with the supplied challenge function at `channel`, independent ideal
functions at earlier channels, and independent real functions at later channels. All calls
go through the first-use rule of the finite child oracle. -/
@[expose]
noncomputable def cascadeChildChallengeAt {α : Type} {count width n : ℕ}
    (real ideal : PMF (BitString width → BitString n)) (channel : Fin count)
    (challenge : BitString width → BitString n) (program : WordOracleComp ℕ α) : PMF α :=
  (PMF.pi (Function.update (fun i : Fin count => if i < channel then ideal else real)
    channel (PMF.pure challenge))).bind fun table =>
    (ProbOracleComp.runWith (cascadeChildFiniteOracle table) program 0).map Prod.fst

/-- Draw a uniform challenge index from `Fin capacity`. Reject indices outside the
`count` child channels. The challenge law is used at exactly the selected channel. -/
@[expose]
noncomputable def cascadeChildChallengeGame {width n : ℕ} (count capacity : ℕ) [NeZero capacity]
    (real ideal challenge : PMF (BitString width → BitString n))
    (program : WordOracleComp ℕ Bool) : PMF Bool :=
  (PMF.uniformOfFintype (Fin capacity)).bind fun index =>
    if h : index.val < count then
      challenge.bind fun row => cascadeChildChallengeAt real ideal ⟨index.val, h⟩ row program
    else PMF.pure false

private noncomputable def childHybrid {α : Type} {count width n : ℕ}
    (real ideal : PMF (BitString width → BitString n)) (cut : ℕ)
    (program : WordOracleComp ℕ α) : PMF α :=
  (PMF.pi (fun i : Fin count => if i.val < cut then ideal else real)).bind fun table =>
    (ProbOracleComp.runWith (cascadeChildFiniteOracle table) program 0).map Prod.fst

/-- Drawing the selected row from the real or ideal source gives the two adjacent hybrids. -/
private theorem bind_cascadeChildChallengeAt {α : Type} {count width n : ℕ}
    (real ideal : PMF (BitString width → BitString n)) (channel : Fin count)
    (program : WordOracleComp ℕ α) (replace : Bool) :
    (if replace then ideal else real).bind
        (fun row => cascadeChildChallengeAt real ideal channel row program) =
      childHybrid (count := count) real ideal (channel.val + replace.toNat) program := by
  let law (i : Fin count) := if i.val < channel.val + replace.toNat then ideal else real
  have hlaw : law channel = if replace then ideal else real := by
    cases replace <;> simp [law]
  have hupdate (row : BitString width → BitString n) :
      Function.update (fun i : Fin count => if i < channel then ideal else real)
          channel (PMF.pure row) = Function.update law channel (PMF.pure row) := by
    funext i
    rcases eq_or_ne i channel with rfl | hi
    · simp only [Function.update_self]
    · cases replace
      · simp [law, hi]
      · simp [law, hi, le_iff_lt_or_eq, Fin.val_inj]
  simp only [cascadeChildChallengeAt, hupdate]
  rw [← hlaw, ← PMF.bind_bind, PMF.pi_bind_update]
  rfl

/-- For a client with at most `count` child calls, sampling a single challenge channel gives
the full child-oracle advantage divided by the sampling range. Padding the range to
`capacity ≥ count` contributes the same rejecting output on both sides. -/
theorem advantage_cascadeChildChannelOracle_eq {count capacity width n : ℕ} [NeZero capacity]
    (real ideal : PMF (BitString width → BitString n)) {program : WordOracleComp ℕ Bool}
    (hbudget : program.IsQueryBounded count) (hcapacity : count ≤ capacity) :
    Game.advantage
        ((ProbOracleComp.runWith (cascadeChildChannelOracle real) program []).map Prod.fst)
        ((ProbOracleComp.runWith (cascadeChildChannelOracle ideal) program []).map Prod.fst) =
      capacity * Game.advantage
        (cascadeChildChallengeGame count capacity real ideal real program)
        (cascadeChildChallengeGame count capacity real ideal ideal program) := by
  have hreal : childHybrid (count := count) real ideal 0 program =
      (ProbOracleComp.runWith (cascadeChildChannelOracle real) program []).map Prod.fst := by
    rw [runWith_cascadeChildChannelOracle_eq_finite real hbudget]
    simp only [childHybrid, Nat.not_lt_zero, ↓reduceIte]
  have hideal : childHybrid (count := count) real ideal count program =
      (ProbOracleComp.runWith (cascadeChildChannelOracle ideal) program []).map Prod.fst := by
    rw [runWith_cascadeChildChannelOracle_eq_finite ideal hbudget]
    simp only [childHybrid, Fin.is_lt, ↓reduceIte]
  rw [← hreal, ← hideal, cascadeChildChallengeGame, cascadeChildChallengeGame]
  have hrealAt (i : Fin capacity) (h : i.val < count) :=
    bind_cascadeChildChallengeAt real ideal ⟨i.val, h⟩ program false
  have hidealAt (i : Fin capacity) (h : i.val < count) :=
    bind_cascadeChildChallengeAt real ideal ⟨i.val, h⟩ program true
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, add_zero, Bool.toNat_true]
    at hrealAt hidealAt
  simp only [hrealAt, hidealAt]
  exact Game.advantage_hybrid_average (fun cut => childHybrid (count := count) real ideal cut
    program) count capacity hcapacity

end Cslib.Crypto
