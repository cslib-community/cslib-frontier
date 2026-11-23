/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Protocols.MPC.ProductRelation
import CslibFrontier.Crypto.Protocols.MPC.ProductRelation.Privacy
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.EventBind
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Algebra.Polynomial.Roots

/-!
# Concrete Tests and Counterexamples for Protocol 23.5 and Lemma 23.1

Checks `Cslib.Crypto.Protocols.MPC.ProductRelation` on finite instances over `ZMod 5` and
`ZMod 6`:

1. **Positive `q = 5, m = 1` instantiation:** concrete triple shares satisfying
   `ProductRelations`, `Fintype.card (Challenge 5 1) = 3`, polynomial identity `(23.8)` via
   `discrepancyPoly_eq_zero_of_productRelations`, verification acceptance via `verifyPair`, and
   honest completeness `eval_honestProtocol_eq_pure`.
2. **Tight Lemma 23.1 instantiation (`q = 5, m = 1`):** corrupt dealer messages `(badD₁, badD₂)`
   with `¬ ProductRelations badD₁.triples badD₂.triples` achieving exact acceptance probability
   `2 / 3`, matching `eval_honestPartiesRun_accept_le`.
3. **Randomized corrupt dealer bound:** `toOuterMeasure_bind_le` lifts
   `eval_honestPartiesRun_accept_le` to any randomized corrupt dealer distribution `D`.
4. **Why the book's conditions matter:** `q = 6, m = 1` shows a bare polynomial root count over
   composite `ZMod 6` (`3` of `4` challenges in `Challenge 6 1` are roots of a degree-`2`
   polynomial), and `q = 5, m = 3` shows `(23.8)` failing when `m + 1 < q` holds (`Challenge 5 3`
   nonempty) but `2 * m < q` fails.
5. **Fact 23.2 privacy (`q = 5, m = 1`):** positive checks for `Lagrange.eval_basis_ne_zero`,
   `productRelations_comm`, `bind_honestOpening_eq_bind_uniform`, `eval_deal_swap`,
   `eval_experiment0P1_eq_experiment1P1`, and `eval_experiment0P2_eq_experiment1P2`.
6. **Necessity of `ProductRelations` (`hrel`):** `counterAdversaryNoRel_separates` separates
   `experiment0P1` (`0`) from `experiment1P1` (`1`) when chosen inputs violate `(23.7)`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.ProductRelation

open Polynomial Finset Cslib Cslib.Probability Cslib.ProbComp
open Cslib.Crypto.Protocols.MPC.Beaver Cslib.Crypto.Protocols.MPC.ProductRelation
open scoped ENNReal

private local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-! ### 1. Positive `q = 5, m = 1` checks -/

private def sampleT1 : Fin 1 → TripleShare (ZMod 5) := ![⟨2, 1, 3⟩]
private def sampleT2 : Fin 1 → TripleShare (ZMod 5) := ![⟨3, 1, 2⟩]

example : Fintype.card (Challenge 5 1) = 3 := by decide

example : ProductRelations sampleT1 sampleT2 := by decide

example :
    let e₁ : DealerExtra 5 1 := ⟨1, 2, 3, ![4]⟩
    discrepancyPoly (e₁.toDeal sampleT1)
      ((honestC2 sampleT1 sampleT2 e₁ 1 4).toDeal sampleT2) = 0 :=
  discrepancyPoly_eq_zero_of_productRelations (by decide) (by decide) ⟨1, 2, 3, ![4]⟩ 1 4

example :
    let e₁ : DealerExtra 5 1 := ⟨1, 2, 3, ![4]⟩
    verifyPair (e₁.toDeal sampleT1)
      ((honestC2 sampleT1 sampleT2 e₁ 1 4).toDeal sampleT2) 2 = (true, true) := by
  have hpoly := congrArg (Polynomial.eval (2 : ZMod 5))
    (discrepancyPoly_eq_zero_of_productRelations (by decide)
      (by decide : ProductRelations sampleT1 sampleT2) (⟨1, 2, 3, ![4]⟩ : DealerExtra 5 1) 1 4)
  simp only [discrepancyPoly, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_zero, sub_eq_zero] at hpoly
  have hr : ∀ k : Fin (1 + 1), (2 : ZMod 5) ≠ (k.val : ZMod 5) := by decide
  dsimp only [verifyPair]
  rw [decide_eq_true hpoly, decide_eq_true hr]
  rfl

example :
    let e₁ : DealerExtra 5 1 := ⟨1, 2, 3, ![4]⟩
    verifyPair (e₁.toDeal sampleT1)
      ((honestC2 sampleT1 sampleT2 e₁ 1 4).toDeal sampleT2) 1 = (true, false) := by
  have hpoly := congrArg (Polynomial.eval (1 : ZMod 5))
    (discrepancyPoly_eq_zero_of_productRelations (by decide)
      (by decide : ProductRelations sampleT1 sampleT2) (⟨1, 2, 3, ![4]⟩ : DealerExtra 5 1) 1 4)
  simp only [discrepancyPoly, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_zero, sub_eq_zero] at hpoly
  have hr : ¬ (∀ k : Fin (1 + 1), (1 : ZMod 5) ≠ (k.val : ZMod 5)) := by decide
  dsimp only [verifyPair]
  rw [decide_eq_true hpoly, decide_eq_false hr]
  rfl

example :
    ProbComp.eval (do
        let dd ← deal sampleT1 sampleT2
        honestPartiesRun 5 1 (by decide) dd.1 dd.2) =
      PMF.pure (true, true) :=
  eval_honestProtocol_eq_pure (by decide) (by decide)

/-! ### 2. Tight Lemma 23.1 instantiation (`q = 5, m = 1`, acceptance `2 / 3`) -/

private def badD1 : PartyDeal 5 1 := ⟨![3, 4], ![2, 3], ![0, 0, 0]⟩
private def badD2 : PartyDeal 5 1 := ⟨![0, 0], ![0, 0], ![0, 0, 0]⟩

example : ¬ ProductRelations badD1.triples badD2.triples := by decide

example :
    (ProbComp.eval (honestPartiesRun 5 1 (by decide) badD1 badD2)).toOuterMeasure
        { res : Bool × Bool | res.1 = true ∨ res.2 = true } ≤
      (2 : ℝ≥0∞) / 3 := by
  have h := eval_honestPartiesRun_accept_le (by decide : 2 * 1 < 5)
    (show ¬ ProductRelations badD1.triples badD2.triples by decide)
  simpa using h

example :
    (ProbComp.eval (honestPartiesRun 5 1 (by decide) badD1 badD2)).toOuterMeasure
        { res : Bool × Bool | res.1 = true ∨ res.2 = true } =
      (2 : ℝ≥0∞) / 3 := by
  have hA1 : badD1.polyA = X - 2 := by
    refine (Lagrange.eq_interpolate_of_eval_eq badD1.a (injOn_natNodes 5 2 (by decide)) ?_ ?_).symm
    · calc (X - 2 : (ZMod 5)[X]).degree ≤ 1 := by
            exact le_trans (Polynomial.degree_sub_le _ _)
              (max_le Polynomial.degree_X_le (Polynomial.degree_C_le.trans (by simp)))
        _ < #(Finset.univ : Finset (Fin 2)) := by simp
    · intro k _
      simp only [natNodes, eval_sub, eval_X, eval_ofNat]
      fin_cases k <;> decide
  have hB1 : badD1.polyB = X - 3 := by
    refine (Lagrange.eq_interpolate_of_eval_eq badD1.b (injOn_natNodes 5 2 (by decide)) ?_ ?_).symm
    · calc (X - 3 : (ZMod 5)[X]).degree ≤ 1 := by
            exact le_trans (Polynomial.degree_sub_le _ _)
              (max_le Polynomial.degree_X_le (Polynomial.degree_C_le.trans (by simp)))
        _ < #(Finset.univ : Finset (Fin 2)) := by simp
    · intro k _
      simp only [natNodes, eval_sub, eval_X, eval_ofNat]
      fin_cases k <;> decide
  have hZero : ∀ (d : PartyDeal 5 1), (∀ k, d.c k = 0) → d.polyC = 0 := by
    intro d hc
    refine (Lagrange.eq_interpolate_of_eval_eq d.c (injOn_natNodes 5 3 (by decide)) ?_ ?_).symm
    · rw [Polynomial.degree_zero, Finset.card_univ, Fintype.card_fin]
      exact WithBot.bot_lt_coe 3
    · intro k _
      simp only [eval_zero, hc]
  have hA2 : badD2.polyA = 0 := by
    refine (Lagrange.eq_interpolate_of_eval_eq badD2.a (injOn_natNodes 5 2 (by decide)) ?_ ?_).symm
    · rw [Polynomial.degree_zero, Finset.card_univ, Fintype.card_fin]
      exact WithBot.bot_lt_coe 2
    · intro k _
      simp only [eval_zero]
      fin_cases k <;> rfl
  have hB2 : badD2.polyB = 0 := by
    refine (Lagrange.eq_interpolate_of_eval_eq badD2.b (injOn_natNodes 5 2 (by decide)) ?_ ?_).symm
    · rw [Polynomial.degree_zero, Finset.card_univ, Fintype.card_fin]
      exact WithBot.bot_lt_coe 2
    · intro k _
      simp only [eval_zero]
      fin_cases k <;> rfl
  have hC1 : badD1.polyC = 0 := hZero badD1 fun k => by fin_cases k <;> rfl
  have hC2 : badD2.polyC = 0 := hZero badD2 fun k => by fin_cases k <;> rfl
  have : Nonempty (Challenge 5 1) := nonempty_challenge 5 1 (by decide)
  have hmap : ProbComp.eval (honestPartiesRun 5 1 (by decide) badD1 badD2) =
      (PMF.uniformOfFintype (Challenge 5 1)).map (fun r => verifyPair badD1 badD2 r.val) := by
    simp only [honestPartiesRun, bind_pure_comp, ProbComp.eval_map, ProbComp.eval_uniform]
  have hfilter :
      (Finset.univ.filter fun r : Challenge 5 1 =>
          (verifyPair badD1 badD2 r.val).1 = true ∨
            (verifyPair badD1 badD2 r.val).2 = true).card = 2 := by
    have heq :
        Finset.univ.filter (fun r : Challenge 5 1 =>
          (verifyPair badD1 badD2 r.val).1 = true ∨ (verifyPair badD1 badD2 r.val).2 = true) =
        Finset.univ.filter (fun r : Challenge 5 1 =>
          (r.val - 2) * (r.val - 3) = 0) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        verifyPair, hA1, hB1, hC1, hA2, hB2, hC2, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_zero, add_zero,
        decide_eq_true_eq, Bool.and_eq_true]
      exact ⟨fun h => h.elim id And.right, Or.inl⟩
    rw [heq]
    decide
  classical
  rw [hmap, PMF.toOuterMeasure_map_apply,
    Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype]
  have hfilter' :
      (Finset.univ.filter (· ∈ (fun r : Challenge 5 1 => verifyPair badD1 badD2 r.val) ⁻¹'
          { res : Bool × Bool | res.1 = true ∨ res.2 = true })).card = 2 := by
    rw [← hfilter]
    congr 1
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_preimage, Set.mem_ofPred_eq]
  rw [hfilter', card_challenge 5 1 (by decide)]
  norm_num [div_eq_mul_inv]

/-! ### 3. Randomized corrupt dealer bound via `toOuterMeasure_bind_le` -/

example {q m : ℕ} [Fact (Nat.Prime q)] (hm : 2 * m < q)
    (D : ProbComp (PartyDeal q m × PartyDeal q m)) :
    let corruptDealerRun : ProbComp ((PartyDeal q m × PartyDeal q m) × (Bool × Bool)) := do
      let dd ← D
      let res ← honestPartiesRun q m hm dd.1 dd.2
      return (dd, res)
    (ProbComp.eval corruptDealerRun).toOuterMeasure
        { x | ¬ ProductRelations x.1.1.triples x.1.2.triples ∧
          (x.2.1 = true ∨ x.2.2 = true) } ≤
      (2 * m : ℝ≥0∞) / ((q - m - 1 : ℕ) : ℝ≥0∞) := by
  intro corruptDealerRun
  have hbind : ProbComp.eval corruptDealerRun =
      (ProbComp.eval D).bind fun dd =>
        (ProbComp.eval (honestPartiesRun q m hm dd.1 dd.2)).map (fun res => (dd, res)) := by
    simp only [corruptDealerRun, ProbComp.eval_bind, ProbComp.eval_pure]
    rfl
  rw [hbind]
  refine Cslib.Probability.PMF.toOuterMeasure_bind_le _ _ _ fun dd => ?_
  rw [PMF.toOuterMeasure_map_apply]
  by_cases hrel : ProductRelations dd.1.triples dd.2.triples
  · have hempty : ((fun res : Bool × Bool => (dd, res)) ⁻¹'
        { x | ¬ ProductRelations x.1.1.triples x.1.2.triples ∧
          (x.2.1 = true ∨ x.2.2 = true) }) = ∅ := by
      ext res
      simp [hrel]
    rw [hempty]
    simp
  · exact le_trans ((ProbComp.eval (honestPartiesRun q m hm dd.1 dd.2)).toOuterMeasure.mono
      fun res hres => hres.2) (eval_honestPartiesRun_accept_le hm hrel)

/-! ### 4. Why the book's conditions matter -/

/- For composite `q = 6` and `m = 1`, `A₁(X) = 2X + 2`, `B₁(X) = X + 3`, `C₁ = 0`,
`A₂ = B₂ = C₂ = 0` violates `(23.7)` at `k = 1` (`4 * 4 = 4 ≠ 0` in `ZMod 6`), yet accepts on
`3` of the `4` challenges in `ℤ_6 \ {0, 1}` (`r ∈ {2, 3, 5}`), exceeding `2m = 2`. -/
example :
    let A₁ : (ZMod 6)[X] := 2 * X + 2
    let B₁ : (ZMod 6)[X] := X + 3
    A₁.eval 1 * B₁.eval 1 ≠ 0 ∧
    (Finset.univ.filter (fun r : Challenge 6 1 => A₁.eval r.val * B₁.eval r.val = 0)).card > 2 * 1 ∧
    Fintype.card (Challenge 6 1) = 4 := by
  refine ⟨?_, ?_, by decide⟩
  · suffices (2 * (1 : ZMod 6) + 2) * (1 + 3) ≠ 0 by
      simpa only [eval_add, eval_mul, eval_ofNat, eval_X, eval_one] using this
    decide
  · have hfilt :
        Finset.univ.filter (fun r : Challenge 6 1 =>
          ((2 * X + 2 : (ZMod 6)[X]).eval r.val) * ((X + 3 : (ZMod 6)[X]).eval r.val) = 0) =
        Finset.univ.filter (fun r : Challenge 6 1 =>
          (2 * r.val + 2) * (r.val + 3) = 0) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, eval_add, eval_mul,
        eval_ofNat, eval_X]
    have hcount :
        (Finset.univ.filter (fun r : Challenge 6 1 =>
          (2 * r.val + 2) * (r.val + 3) = 0)).card = 3 := by
      decide
    rw [hfilt, hcount]
    omega

/- When `m + 1 < q` holds (`Challenge 5 3` nonempty) but `2 * m < q` fails (`q = 5, m = 3`),
`natNodes 5 (2 * 3 + 1)` collides (`0 ≡ 5 mod 5`) and identity `(23.8)` fails on valid `(23.7)`
inputs. -/
example :
    (3 : ℕ) + 1 < 5 ∧ ¬ (2 * 3 < 5) ∧ Nonempty (Challenge 5 3) ∧
    ∃ (t₁ t₂ : Fin 3 → TripleShare (ZMod 5)) (e₁ : DealerExtra 5 3) (a02 b02 : ZMod 5),
      ProductRelations t₁ t₂ ∧
      discrepancyPoly (e₁.toDeal t₁) ((honestC2 t₁ t₂ e₁ a02 b02).toDeal t₂) ≠ 0 := by
  let t₁ : Fin 3 → TripleShare (ZMod 5) := fun k => if k.val = 0 then ⟨1, 1, 1⟩ else ⟨0, 0, 0⟩
  let t₂ : Fin 3 → TripleShare (ZMod 5) := fun _ => ⟨0, 0, 0⟩
  let e₁ : DealerExtra 5 3 := ⟨0, 0, 0, 0⟩
  refine ⟨by omega, by omega, nonempty_challenge 5 3 (by omega),
    ⟨t₁, t₂, e₁, 0, 0, ?_, ?_⟩⟩
  · intro k
    fin_cases k <;> simp [t₁, t₂]
  · intro heq
    have hev := congrArg (Polynomial.eval (1 : ZMod 5)) heq
    have hA1 : (e₁.toDeal t₁).polyA.eval 1 = 1 := by
      have h := eval_interpPoly ((e₁.toDeal t₁).a) (by omega) (Fin.succ 0)
      simpa only [PartyDeal.polyA, Fin.val_succ, Fin.val_zero, zero_add, Nat.cast_one,
        DealerExtra.toDeal_a, Fin.cons_succ, t₁, ↓reduceIte] using h
    have hB1 : (e₁.toDeal t₁).polyB.eval 1 = 1 := by
      have h := eval_interpPoly ((e₁.toDeal t₁).b) (by omega) (Fin.succ 0)
      simpa only [PartyDeal.polyB, Fin.val_succ, Fin.val_zero, zero_add, Nat.cast_one,
        DealerExtra.toDeal_b, Fin.cons_succ, t₁, ↓reduceIte] using h
    have hA2 : ((honestC2 t₁ t₂ e₁ 0 0).toDeal t₂).polyA.eval 1 = 0 := by
      have h := eval_interpPoly (((honestC2 t₁ t₂ e₁ 0 0).toDeal t₂).a) (by omega) (Fin.succ 0)
      simpa only [PartyDeal.polyA, Fin.val_succ, Fin.val_zero, zero_add, Nat.cast_one,
        DealerExtra.toDeal_a, Fin.cons_succ, t₂] using h
    have hB2 : ((honestC2 t₁ t₂ e₁ 0 0).toDeal t₂).polyB.eval 1 = 0 := by
      have h := eval_interpPoly (((honestC2 t₁ t₂ e₁ 0 0).toDeal t₂).b) (by omega) (Fin.succ 0)
      simpa only [PartyDeal.polyB, Fin.val_succ, Fin.val_zero, zero_add, Nat.cast_one,
        DealerExtra.toDeal_b, Fin.cons_succ, t₂] using h
    have hpolyC_at_1 : ∀ d : PartyDeal 5 3, d.polyC.eval (1 : ZMod 5) = 0 := by
      intro d
      simp only [PartyDeal.polyC, interpPoly, Lagrange.interpolate_apply,
        ← Polynomial.coe_evalRingHom, map_sum, map_mul]
      refine Finset.sum_eq_zero fun k _ => ?_
      have hk : (Lagrange.basis (Finset.univ : Finset (Fin 7)) (natNodes 5 7) k).eval 1 = 0 := by
        rw [Lagrange.eval_basis]
        by_cases hk1 : k = 1
        · subst hk1
          refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨by decide, Finset.mem_univ 6⟩) ?_
          have hsub : (1 : ZMod 5) - natNodes 5 7 6 = 0 := by decide
          simp [hsub]
        · refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hk1, Finset.mem_univ 1⟩) ?_
          have hsub : (1 : ZMod 5) - natNodes 5 7 1 = 0 := by decide
          simp [hsub]
      simp [hk]
    simp only [discrepancyPoly, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_zero, sub_eq_zero] at hev
    rw [hA1, hA2, hB1, hB2, hpolyC_at_1, hpolyC_at_1] at hev
    norm_num at hev

/-! ### 5. Positive `q = 5, m = 1` Fact 23.2 privacy checks -/

example : (Lagrange.basis Finset.univ (natNodes 5 2) 0).eval (2 : ZMod 5) ≠ 0 :=
  Lagrange.eval_basis_ne_zero (injOn_natNodes 5 2 (by decide)) (Finset.mem_univ 0)
    (fun j _ _ => by fin_cases j <;> decide)

example : (Lagrange.basis Finset.univ (natNodes 5 2) 0).eval (0 : ZMod 5) ≠ 0 :=
  Lagrange.eval_basis_ne_zero (injOn_natNodes 5 2 (by decide)) (Finset.mem_univ 0)
    (fun j _ hj => by fin_cases j <;> [exact absurd rfl hj; decide])

example : ProductRelations sampleT2 sampleT1 :=
  productRelations_comm.mp (by decide : ProductRelations sampleT1 sampleT2)

example :
    (PMF.uniformOfFintype (ZMod 5)).bind (fun a02 =>
      (PMF.uniformOfFintype (ZMod 5)).bind (fun b02 =>
        let d₂ := (honestC2 sampleT1 sampleT2 ⟨1, 2, 3, ![4]⟩ a02 b02).toDeal sampleT2
        PMF.pure (d₂.polyA.eval 2, d₂.polyB.eval 2, d₂.polyC.eval 2))) =
    (PMF.uniformOfFintype (ZMod 5)).bind (fun α₂ =>
      (PMF.uniformOfFintype (ZMod 5)).bind (fun β₂ =>
        let d₁ := (⟨1, 2, 3, ![4]⟩ : DealerExtra 5 1).toDeal sampleT1
        let γ₂ := (d₁.polyA.eval 2 + α₂) * (d₁.polyB.eval 2 + β₂) - d₁.polyC.eval 2
        PMF.pure (α₂, β₂, γ₂))) :=
  bind_honestOpening_eq_bind_uniform (by decide) (by decide : ProductRelations sampleT1 sampleT2)
    ⟨1, 2, 3, ![4]⟩ (fun k => by fin_cases k <;> decide) PMF.pure

example :
    (ProbComp.eval (deal sampleT1 sampleT2)).map Prod.swap =
      ProbComp.eval (deal sampleT2 sampleT1) :=
  eval_deal_swap sampleT1 sampleT2

private def sampleP1Adv : CorruptP1Adversary 5 1 Unit where
  chooseInputs := return (sampleT1, sampleT2, ())
  chooseChallenge _ _ := return (2, ())
  sendOpening _ open₂ := return (open₂, ())
  finish _ res := return (res == some true)

example :
    ProbComp.eval (experiment0P1 5 1 sampleP1Adv) =
      ProbComp.eval (experiment1P1 5 1 sampleP1Adv) := by
  refine eval_experiment0P1_eq_experiment1P1 (by decide) sampleP1Adv fun t₁ t₂ _ hx => ?_
  simp only [sampleP1Adv, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq] at hx
  rcases hx with ⟨rfl, rfl, _⟩
  decide

private def sampleP2Adv : CorruptP2Adversary 5 1 Unit where
  chooseInputs := return (sampleT1, sampleT2, ())
  sendOpening _ _ _ open₁ := return (open₁, ())
  finish _ res := return res

example :
    ProbComp.eval (experiment0P2 5 1 (by decide) sampleP2Adv) =
      ProbComp.eval (experiment1P2 5 1 (by decide) sampleP2Adv) := by
  refine eval_experiment0P2_eq_experiment1P2 (by decide) sampleP2Adv fun t₁ t₂ _ hx => ?_
  simp only [sampleP2Adv, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq] at hx
  rcases hx with ⟨rfl, rfl, _⟩
  decide

/-! ### 6. Separating adversary when `ProductRelations` (`hrel`) fails -/

private def badRelT1 : Fin 1 → TripleShare (ZMod 5) := ![⟨1, 1, 0⟩]
private def badRelT2 : Fin 1 → TripleShare (ZMod 5) := ![⟨0, 0, 0⟩]

private noncomputable def counterAdversaryNoRel : CorruptP1Adversary 5 1 (PartyDeal 5 1) where
  chooseInputs := return (badRelT1, badRelT2, ⟨![0, 0], ![0, 0], ![0, 0, 0]⟩)
  chooseChallenge _ d₁ := return (3, d₁)
  sendOpening d₁ _ := return ((d₁.polyA.eval 3, d₁.polyB.eval 3, d₁.polyC.eval 3), d₁)
  finish _ res := return (res == some true)

example : ¬ ProductRelations badRelT1 badRelT2 := by decide

/-- Dropping `hrel` breaks Fact 23.2: on inputs violating `(23.7)`, `experiment0P1` outputs `true`
with probability `0` whereas `experiment1P1` outputs `true` with probability `1`. -/
theorem counterAdversaryNoRel_separates :
    (ProbComp.eval (experiment0P1 5 1 counterAdversaryNoRel)) true = 0 ∧
    (ProbComp.eval (experiment1P1 5 1 counterAdversaryNoRel)) true = 1 ∧
    (ProbComp.eval (experiment0P1 5 1 counterAdversaryNoRel)) true ≠
      (ProbComp.eval (experiment1P1 5 1 counterAdversaryNoRel)) true := by
  have hr : ∀ k : Fin (1 + 1), (3 : ZMod 5) ≠ (k.val : ZMod 5) := by decide
  have hexp0 : ProbComp.eval (experiment0P1 5 1 counterAdversaryNoRel) = PMF.pure false := by
    simp only [experiment0P1, counterAdversaryNoRel, deal, pmf_norm, ProbComp.eval_uniform]
    simp only [eq_true hr, ite_true, pmf_norm]
    have hacc : ∀ (e₁ : DealerExtra 5 1) (a02 b02 : ZMod 5),
        let d₁ := e₁.toDeal badRelT1
        let d₂ := (honestC2 badRelT1 badRelT2 e₁ a02 b02).toDeal badRelT2
        decide ((d₁.polyA.eval 3 + d₂.polyA.eval 3) * (d₁.polyB.eval 3 + d₂.polyB.eval 3) =
          d₁.polyC.eval 3 + d₂.polyC.eval 3) = false := by
      intro e₁ a02 b02
      dsimp only []
      set d₁ := e₁.toDeal badRelT1
      set d₂ := (honestC2 badRelT1 badRelT2 e₁ a02 b02).toDeal badRelT2
      let qPoly : (ZMod 5)[X] := discrepancyPoly d₁ d₂ + X * (X - 2)
      have hdeg : qPoly.natDegree < Fintype.card (Fin 3) := by
        rw [Fintype.card_fin]
        have hdiscDeg : (discrepancyPoly d₁ d₂).natDegree ≤ 2 :=
          discrepancyPoly_natDegree_le d₁ d₂ (by decide)
        have hquadDeg : (X * (X - 2) : (ZMod 5)[X]).natDegree ≤ 2 := by
          refine (Polynomial.natDegree_mul_le).trans ?_
          have h1 : (X : (ZMod 5)[X]).natDegree ≤ 1 := Polynomial.natDegree_X_le
          have h2 : (X - 2 : (ZMod 5)[X]).natDegree ≤ 1 :=
            (Polynomial.natDegree_sub_le _ _).trans (max_le Polynomial.natDegree_X_le
              (by simp))
          omega
        exact Nat.lt_succ_of_le ((Polynomial.natDegree_add_le _ _).trans (max_le hdiscDeg hquadDeg))
      have hinj : Function.Injective (natNodes 5 3) := fun i j hij =>
        injOn_natNodes 5 3 (by decide) (Finset.mem_univ i) (Finset.mem_univ j) hij
      have heval : ∀ k : Fin 3, qPoly.eval (natNodes 5 3 k) = 0 := by
        intro k
        fin_cases k
        · change qPoly.eval (natNodes 5 3 0) = 0
          simp only [qPoly, eval_add]
          have hA1 : d₁.polyA.eval (natNodes 5 3 0) = e₁.a0 := by
            simpa [d₁, PartyDeal.polyA, natNodes, DealerExtra.toDeal_a] using
              eval_interpPoly d₁.a (by decide : 1 + 1 ≤ 5) 0
          have hB1 : d₁.polyB.eval (natNodes 5 3 0) = e₁.b0 := by
            simpa [d₁, PartyDeal.polyB, natNodes, DealerExtra.toDeal_b] using
              eval_interpPoly d₁.b (by decide : 1 + 1 ≤ 5) 0
          have hC1 : d₁.polyC.eval (natNodes 5 3 0) = e₁.c0 := by
            simpa [d₁, PartyDeal.polyC, natNodes, DealerExtra.toDeal_c_zero] using
              eval_interpPoly d₁.c (by decide : 2 * 1 + 1 ≤ 5) 0
          have hA2 : d₂.polyA.eval (natNodes 5 3 0) = a02 := by
            simpa [d₂, PartyDeal.polyA, natNodes, DealerExtra.toDeal_a, honestC2_a0] using
              eval_interpPoly d₂.a (by decide : 1 + 1 ≤ 5) 0
          have hB2 : d₂.polyB.eval (natNodes 5 3 0) = b02 := by
            simpa [d₂, PartyDeal.polyB, natNodes, DealerExtra.toDeal_b, honestC2_b0] using
              eval_interpPoly d₂.b (by decide : 1 + 1 ≤ 5) 0
          have hC2 : d₂.polyC.eval (natNodes 5 3 0) =
              (e₁.a0 + a02) * (e₁.b0 + b02) - e₁.c0 := by
            simpa [d₂, PartyDeal.polyC, natNodes, DealerExtra.toDeal_c_zero, honestC2_c0] using
              eval_interpPoly d₂.c (by decide : 2 * 1 + 1 ≤ 5) 0
          simp only [discrepancyPoly, eval_sub, eval_mul, eval_add]
          rw [hA1, hB1, hC1, hA2, hB2, hC2]
          simp only [natNodes, Fin.val_zero, Nat.cast_zero, eval_X, eval_ofNat]
          ring
        · change qPoly.eval (natNodes 5 3 1) = 0
          simp only [qPoly, eval_add]
          have hA1 : d₁.polyA.eval (natNodes 5 3 1) = (badRelT1 0).a := by
            simpa [d₁, PartyDeal.polyA, natNodes, DealerExtra.toDeal_a] using
              eval_interpPoly d₁.a (by decide : 1 + 1 ≤ 5) (Fin.succ 0)
          have hB1 : d₁.polyB.eval (natNodes 5 3 1) = (badRelT1 0).b := by
            simpa [d₁, PartyDeal.polyB, natNodes, DealerExtra.toDeal_b] using
              eval_interpPoly d₁.b (by decide : 1 + 1 ≤ 5) (Fin.succ 0)
          have hC1 : d₁.polyC.eval (natNodes 5 3 1) = (badRelT1 0).c := by
            have h := eval_interpPoly d₁.c (by decide : 2 * 1 + 1 ≤ 5) ⟨1, by decide⟩
            rw [DealerExtra.toDeal_c_of_le badRelT1 e₁ (by decide) (by decide)] at h
            simpa [d₁, PartyDeal.polyC, natNodes] using h
          have hA2 : d₂.polyA.eval (natNodes 5 3 1) = (badRelT2 0).a := by
            simpa [d₂, PartyDeal.polyA, natNodes, DealerExtra.toDeal_a] using
              eval_interpPoly d₂.a (by decide : 1 + 1 ≤ 5) (Fin.succ 0)
          have hB2 : d₂.polyB.eval (natNodes 5 3 1) = (badRelT2 0).b := by
            simpa [d₂, PartyDeal.polyB, natNodes, DealerExtra.toDeal_b] using
              eval_interpPoly d₂.b (by decide : 1 + 1 ≤ 5) (Fin.succ 0)
          have hC2 : d₂.polyC.eval (natNodes 5 3 1) = (badRelT2 0).c := by
            have h := eval_interpPoly d₂.c (by decide : 2 * 1 + 1 ≤ 5) ⟨1, by decide⟩
            rw [DealerExtra.toDeal_c_of_le badRelT2
              (honestC2 badRelT1 badRelT2 e₁ a02 b02) (by decide) (by decide)] at h
            simpa [d₂, PartyDeal.polyC, natNodes] using h
          simp only [discrepancyPoly, eval_sub, eval_mul, eval_add]
          rw [hA1, hB1, hC1, hA2, hB2, hC2]
          simp only [natNodes, Fin.val_one, Nat.cast_one, eval_X, eval_ofNat]
          decide
        · change qPoly.eval (natNodes 5 3 2) = 0
          simp only [qPoly, eval_add]
          have hC1 : d₁.polyC.eval (natNodes 5 3 2) = e₁.cTail 0 := by
            have h := eval_interpPoly d₁.c (by decide : 2 * 1 + 1 ≤ 5) ⟨2, by decide⟩
            rw [DealerExtra.toDeal_c_of_lt badRelT1 e₁ (by decide)] at h
            simpa [d₁, PartyDeal.polyC, natNodes] using h
          have hC2 : d₂.polyC.eval (natNodes 5 3 2) =
              ((d₁.polyA + d₂.polyA) * (d₁.polyB + d₂.polyB)).eval (natNodes 5 3 2) -
                e₁.cTail 0 := by
            have h := eval_interpPoly d₂.c (by decide : 2 * 1 + 1 ≤ 5) ⟨2, by decide⟩
            rw [DealerExtra.toDeal_c_of_lt badRelT2
              (honestC2 badRelT1 badRelT2 e₁ a02 b02) (by decide)] at h
            simpa [d₂, d₁, PartyDeal.polyC, PartyDeal.polyA, PartyDeal.polyB, natNodes,
              honestC2_cTail, DealerExtra.toDeal_a, DealerExtra.toDeal_b,
              honestC2_a0, honestC2_b0] using h
          simp only [discrepancyPoly, eval_sub, eval_mul, eval_add]
          rw [hC1, hC2]
          simp only [natNodes, Fin.isValue, Fin.val_two, Nat.cast_ofNat, eval_mul, eval_add,
            eval_X, eval_ofNat]
          ring
      have hQ0 : qPoly = 0 :=
        Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hinj heval hdeg
      have h3 : (discrepancyPoly d₁ d₂).eval 3 = 2 := by
        have h := congrArg (Polynomial.eval (3 : ZMod 5)) hQ0
        simp only [qPoly, eval_add, eval_mul, eval_sub, eval_X, eval_ofNat, eval_zero] at h
        have hsub : ((discrepancyPoly d₁ d₂).eval 3) + 3 * (3 - 2) = 0 := h
        have hcalc : (3 : ZMod 5) * (3 - 2) = 3 := by decide
        rw [hcalc] at hsub
        calc (discrepancyPoly d₁ d₂).eval 3
            = (discrepancyPoly d₁ d₂).eval 3 + 3 - 3 := (add_sub_cancel_right _ _).symm
          _ = 0 - 3 := by rw [hsub]
          _ = 2 := by decide
      have hne : (d₁.polyA.eval 3 + d₂.polyA.eval 3) * (d₁.polyB.eval 3 + d₂.polyB.eval 3) ≠
          d₁.polyC.eval 3 + d₂.polyC.eval 3 := by
        intro h
        have hz : (discrepancyPoly d₁ d₂).eval 3 = 0 := by
          simp only [discrepancyPoly, eval_sub, eval_mul, eval_add, h, sub_self]
        rw [hz] at h3
        exact absurd h3 (by decide)
      simp [hne]
    have hbool : (some false == some true) = false := rfl
    simp only [hacc, hbool, PMF.bind_const]
  have hexp1 : ProbComp.eval (experiment1P1 5 1 counterAdversaryNoRel) = PMF.pure true := by
    simp only [experiment1P1, counterAdversaryNoRel, simDeal, sim1Eval, pmf_norm,
      ProbComp.eval_uniform]
    simp only [eq_true hr, ite_true, pmf_norm]
    have hacc : ∀ (e₁ : DealerExtra 5 1) (α₂ β₂ : ZMod 5),
        let d₁ := e₁.toDeal badRelT1
        decide ((d₁.polyA.eval 3 + α₂) * (d₁.polyB.eval 3 + β₂) =
          d₁.polyC.eval 3 + ((d₁.polyA.eval 3 + α₂) * (d₁.polyB.eval 3 + β₂) -
            d₁.polyC.eval 3)) = true := by
      intro e₁ α₂ β₂
      have hsub : ∀ x y : ZMod 5, y + (x - y) = x := fun x y => by ring
      simp only [hsub, decide_true]
    have hbool : (some true == some true) = true := rfl
    simp only [hacc, hbool, PMF.bind_const]
  rw [hexp0, hexp1]
  simp

end CslibFrontierTests.Crypto.ProductRelation
