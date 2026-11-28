/-
Copyright (c) 2026 Phillipp Schoppmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Phillipp Schoppmann
-/

module

import CslibFrontier.Crypto.Protocols.MPC.ProductRelation.AuthenticatedTriple

/-!
# Concrete Tests for Two-Party Authenticated Beaver Triples over `ZMod 17`

Exercises `Cslib.Crypto.Protocols.MPC.ProductRelation.AuthenticatedTriple` on concrete instances
over the prime modulus `q = 17` (`14 < 17`, soundness bound `14 / (17 - 8) = 14 / 9`), together
with boundary checks at `q = 13` (`¬ (14 < 13)`):

1. **Honest valid triple (`q = 17`):** MAC keys `α = 3`, `β = 5`, `a = 4`, `b = 6`, `c = 7`,
   `SPDZ.AuthShare` and `VOLECorrelation` bridge checks, `productRelations_toTripleShares_iff`,
   completeness `eval_checkAuthTriple_eq_pure`, single-element opening `1 / 17` soundness,
   corrupt-`P₁` and corrupt-`P₂` exact simulation privacy, and authenticated online Beaver
   multiplication closure.
2. **Failing case (`a * b ≠ c`, `q = 17`):** MAC tags match `α, β` on `a, b, c`, yet `c` is not
   `a * b`, failing `ProductRelations` and triggering the `14 / 9` bound.
3. **Failing case (single tampered MAC tag, `q = 17`):** `a * b = c` holds and 5 of 6 MAC tags are
   valid, while a single tag (`t_{c2}`) is tampered by `+ 1`, failing `ProductRelations` and
   triggering the `14 / 9` bound.
4. **Boundary check (`q = 13` vs `q = 17`):** `14 < 17` and
   `(14 : ENNReal) / ((17 - 8 : ℕ) : ENNReal) = 14 / 9`, whereas `¬ (14 < 13)`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.MPCAuthenticatedTriple

open Cslib Cslib.Probability Cslib.ProbComp
open Cslib.Crypto.Protocols.MPC Cslib.Crypto.Protocols.MPC.Beaver
open Cslib.Crypto.Protocols.MPC.SPDZ Cslib.Crypto.Protocols.VOLE
open Cslib.Crypto.Protocols.MPC.ProductRelation
open scoped ENNReal

private local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

private def α17 : ZMod 17 := 3
private def β17 : ZMod 17 := 5

/-- Honest shares for `a = 1 + 3 = 4`, `b = 2 + 4 = 6`, `c = 5 + 2 = 7 = 4 * 6 (mod 17)`:
- `α * a = 3 * 4 = 12 = 7 + 5`, `β * a = 5 * 4 = 3 = 1 + 2`
- `α * b = 3 * 6 = 1 = 9 + 9`, `β * b = 5 * 6 = 13 = 6 + 7`
- `α * c = 3 * 7 = 4 = 10 + 11`, `β * c = 5 * 7 = 1 = 8 + 10` -/
private def honestTr1 : PartyAuthTriple (ZMod 17) where
  a := ⟨1, 7, 1⟩
  b := ⟨2, 9, 6⟩
  c := ⟨5, 10, 8⟩

private def honestTr2 : PartyAuthTriple (ZMod 17) where
  a := ⟨3, 5, 2⟩
  b := ⟨4, 9, 7⟩
  c := ⟨2, 11, 10⟩

/-! ### 1. Positive `q = 17` checks: bridges, 7-relation check, completeness, privacy, closure -/

example : PartyAuthTriple.Valid α17 β17 honestTr1 honestTr2 := by decide

example : ProductRelations (toTripleShares₁ α17 honestTr1) (toTripleShares₂ β17 honestTr2) :=
  (productRelations_toTripleShares_iff α17 β17 honestTr1 honestTr2).mpr (by decide)

example :
    (honestTr1.a.toSPDZ₁ honestTr2.a).Valid α17 ∧
    (honestTr1.a.toSPDZ₂ honestTr2.a).Valid β17 ∧
    (honestTr1.a.toVOLEForP1 α17 honestTr2.a).Valid ∧
    (honestTr1.a.toVOLEForP2 β17 honestTr2.a).Valid := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ((PartyAuthShare.valid_iff_spdz α17 β17 honestTr1.a honestTr2.a).mp (by decide)).1
  · exact ((PartyAuthShare.valid_iff_spdz α17 β17 honestTr1.a honestTr2.a).mp (by decide)).2
  · exact (PartyAuthShare.voleValid_toVOLEForP1_iff α17 honestTr1.a honestTr2.a).mpr (by decide)
  · exact (PartyAuthShare.voleValid_toVOLEForP2_iff β17 honestTr1.a honestTr2.a).mpr (by decide)

example : ProbComp.eval (checkAuthTriple 17 (by decide) α17 β17 honestTr1 honestTr2) =
    PMF.pure (true, true) :=
  eval_checkAuthTriple_eq_pure (by decide) (by decide)

/-- Single-element opening completeness and `1 / 17` MAC forgery bound for a forged share `2 ≠ 1`.
-/
example :
    verifyOpening β17 honestTr2.a.val honestTr2.a.mac2 honestTr1.a.val honestTr1.a.mac2 ∧
    (PMF.uniformOfFintype (ZMod 17)).toOuterMeasure
      { key : ZMod 17 |
        verifyOpening key honestTr2.a.val
          (key * (honestTr1.a.val + honestTr2.a.val) - honestTr1.a.mac2) 2 9 } ≤
      (17 : ℝ≥0∞)⁻¹ :=
  ⟨by decide,
   toOuterMeasure_verifyOpening_le (q := 17) (by decide : (2 : ZMod 17) ≠ honestTr1.a.val)⟩

/-- Authenticated online Beaver multiplication closure on `x = 10`, `y = 11` (`x * y = 8` mod 17).
-/
private def shareX1 : PartyAuthShare (ZMod 17) := ⟨4, 1, 2⟩
private def shareX2 : PartyAuthShare (ZMod 17) := ⟨6, 12, 14⟩
private def shareY1 : PartyAuthShare (ZMod 17) := ⟨7, 5, 10⟩
private def shareY2 : PartyAuthShare (ZMod 17) := ⟨4, 11, 11⟩

example :
    PartyAuthShare.Valid α17 β17 shareX1 shareX2 ∧
    PartyAuthShare.Valid α17 β17 shareY1 shareY2 := by
  decide

example :
    let d : ZMod 17 := (shareX1.val + shareX2.val) - (honestTr1.a.val + honestTr2.a.val)
    let e : ZMod 17 := (shareY1.val + shareY2.val) - (honestTr1.b.val + honestTr2.b.val)
    let z₁ := PartyAuthShare.mulOnlineP1 α17 d e honestTr1.a honestTr1.b honestTr1.c
    let z₂ := PartyAuthShare.mulOnlineP2 β17 d e honestTr2.a honestTr2.b honestTr2.c
    PartyAuthShare.Valid α17 β17 z₁ z₂ ∧
      z₁.val + z₂.val = (shareX1.val + shareX2.val) * (shareY1.val + shareY2.val) :=
  PartyAuthTriple.mulOnline_valid_and_eq_mul
    (by decide : PartyAuthTriple.Valid α17 β17 honestTr1 honestTr2)
    shareX1 shareX2 shareY1 shareY2 rfl rfl

private def honestInst17 : AuthTripleInstance (ZMod 17) where
  key1 := α17
  key2 := β17
  triple1 := honestTr1
  triple2 := honestTr2

private def sampleAuthP1Adv : AuthCorruptP1Adversary 17 Unit where
  chooseInputs := return (honestInst17, ())
  chooseChallenge _ _ := return (8, ())
  sendOpening _ open₂ := return (open₂, ())
  finish _ res := return (res == some true)

example :
    ProbComp.eval (experiment0P1 17 7 sampleAuthP1Adv.toProductAdversary) =
      ProbComp.eval (experiment1P1 17 7 sampleAuthP1Adv.toProductAdversary) := by
  refine eval_authExperiment0P1_eq_experiment1P1 (by decide) sampleAuthP1Adv fun inst _ hx => ?_
  simp only [sampleAuthP1Adv, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq] at hx
  rcases hx with ⟨rfl, _⟩
  decide

private def sampleAuthP2Adv : AuthCorruptP2Adversary 17 Unit where
  chooseInputs := return (honestInst17, ())
  sendOpening _ _ _ open₁ := return (open₁, ())
  finish _ res := return res

example :
    ProbComp.eval (experiment0P2 17 7 (by decide) sampleAuthP2Adv.toProductAdversary) =
      ProbComp.eval (experiment1P2 17 7 (by decide) sampleAuthP2Adv.toProductAdversary) := by
  refine eval_authExperiment0P2_eq_experiment1P2 (by decide) sampleAuthP2Adv fun inst _ hx => ?_
  simp only [sampleAuthP2Adv, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq] at hx
  rcases hx with ⟨rfl, _⟩
  decide

/-! ### 2. Failing case: `a * b ≠ c` with valid MAC tags (`q = 17`) -/

/-- Shares with `a = 4`, `b = 6`, `c = 8 ≠ 4 * 6 = 7 (mod 17)`, with all 6 MAC tags valid for
`c = 8` (`α * 8 = 3 * 8 = 7 = 10 + 14`, `β * 8 = 5 * 8 = 6 = 8 + 15`). -/
private def badMulTr2 : PartyAuthTriple (ZMod 17) where
  a := honestTr2.a
  b := honestTr2.b
  c := ⟨3, 14, 15⟩

private def badMulDeal1 : PartyDeal 17 7 :=
  (⟨0, 0, 0, 0⟩ : DealerExtra 17 7).toDeal (toTripleShares₁ α17 honestTr1)

private def badMulDeal2 : PartyDeal 17 7 :=
  (⟨0, 0, 0, 0⟩ : DealerExtra 17 7).toDeal (toTripleShares₂ β17 badMulTr2)

example :
    PartyAuthShare.Valid α17 β17 honestTr1.c badMulTr2.c ∧
    ¬ PartyAuthTriple.Valid α17 β17 honestTr1 badMulTr2 ∧
    ¬ ProductRelations (toTripleShares₁ α17 honestTr1) (toTripleShares₂ β17 badMulTr2) := by
  refine ⟨by decide, by decide, ?_⟩
  rw [productRelations_toTripleShares_iff]
  decide

example :
    (ProbComp.eval
        (honestAuthPartiesRun 17 (by decide) α17 β17 badMulDeal1 badMulDeal2)).toOuterMeasure
        { res : Bool × Bool | res.1 = true ∨ res.2 = true } ≤
      (14 : ℝ≥0∞) / 9 := by
  have hnot :
      ¬ PartyAuthTriple.Valid α17 β17 (extractTriple badMulDeal1.triples)
          (extractTriple badMulDeal2.triples) := by
    simp only [badMulDeal1, badMulDeal2, DealerExtra.toDeal_triples,
      extractTriple_toTripleShares₁, extractTriple_toTripleShares₂]
    decide
  simpa using eval_honestAuthPartiesRun_accept_le (by decide : 14 < 17) hnot

/-! ### 3. Failing case: single MAC tag tampered while `a * b = c` holds (`q = 17`) -/

/-- Identical to `honestTr2` except `c.mac1` is tampered from `11` to `12` (`t_{c2} + 1`). -/
private def badMacTr2 : PartyAuthTriple (ZMod 17) where
  a := honestTr2.a
  b := honestTr2.b
  c := ⟨honestTr2.c.val, honestTr2.c.mac1 + 1, honestTr2.c.mac2⟩

private def badMacDeal2 : PartyDeal 17 7 :=
  (⟨0, 0, 0, 0⟩ : DealerExtra 17 7).toDeal (toTripleShares₂ β17 badMacTr2)

example :
    (honestTr1.a.val + badMacTr2.a.val) * (honestTr1.b.val + badMacTr2.b.val) =
      honestTr1.c.val + badMacTr2.c.val ∧
    ¬ PartyAuthTriple.Valid α17 β17 honestTr1 badMacTr2 ∧
    ¬ ProductRelations (toTripleShares₁ α17 honestTr1) (toTripleShares₂ β17 badMacTr2) := by
  refine ⟨by decide, by decide, ?_⟩
  rw [productRelations_toTripleShares_iff]
  decide

example :
    (ProbComp.eval
        (honestAuthPartiesRun 17 (by decide) α17 β17 badMulDeal1 badMacDeal2)).toOuterMeasure
        { res : Bool × Bool | res.1 = true ∨ res.2 = true } ≤
      (14 : ℝ≥0∞) / 9 := by
  have hnot :
      ¬ PartyAuthTriple.Valid α17 β17 (extractTriple badMulDeal1.triples)
          (extractTriple badMacDeal2.triples) := by
    simp only [badMulDeal1, badMacDeal2, DealerExtra.toDeal_triples,
      extractTriple_toTripleShares₁, extractTriple_toTripleShares₂]
    decide
  simpa using eval_honestAuthPartiesRun_accept_le (by decide : 14 < 17) hnot

/-! ### 4. Soundness numerator/denominator and boundary checks (`14 < 17` vs `q = 13`) -/

example :
    (14 : ℕ) < 17 ∧ ¬ ((14 : ℕ) < 13) ∧
    ((14 : ℝ≥0∞) / ((17 - 8 : ℕ) : ℝ≥0∞)) = 14 / 9 := by
  norm_num

/-- Key-inconsistency boundary: when the corrupt dealer places a wrong key `α17 + 1` in `d₁`,
`honestAuthPartiesRun` aborts immediately with probability `1`. -/
example :
    let badKeyDeal1 : PartyDeal 17 7 :=
      (⟨0, 0, 0, 0⟩ : DealerExtra 17 7).toDeal (toTripleShares₁ (α17 + 1) honestTr1)
    ProbComp.eval (honestAuthPartiesRun 17 (by decide) α17 β17 badKeyDeal1 badMacDeal2) =
      PMF.pure (false, false) := by
  intro badKeyDeal1
  have hne :
      ¬ (badKeyDeal1.triples = toTripleShares₁ α17 (extractTriple badKeyDeal1.triples) ∧
         badMacDeal2.triples = toTripleShares₂ β17 (extractTriple badMacDeal2.triples)) := by
    intro h
    have h1 := congrFun h.1 1
    simp only [badKeyDeal1, DealerExtra.toDeal_triples, extractTriple_toTripleShares₁,
      toTripleShares₁] at h1
    have ha : α17 + 1 = α17 := congrArg TripleShare.a h1
    revert ha
    decide
  dsimp only [honestAuthPartiesRun]
  split_ifs
  rfl

end CslibFrontierTests.Crypto.MPCAuthenticatedTriple
