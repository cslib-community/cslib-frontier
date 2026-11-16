/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Protocols.MPC.ProductRelation
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
  have hr : ∀ k : Fin (1 + 1), (2 : ZMod 5) ≠ (k.1 : ZMod 5) := by decide
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
  have hr : ¬ (∀ k : Fin (1 + 1), (1 : ZMod 5) ≠ (k.1 : ZMod 5)) := by decide
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
      (PMF.uniformOfFintype (Challenge 5 1)).map (fun r => verifyPair badD1 badD2 r.1) := by
    simp only [honestPartiesRun, bind_pure_comp, ProbComp.eval_map, ProbComp.eval_uniform]
  have hfilter :
      (Finset.univ.filter fun r : Challenge 5 1 =>
          (verifyPair badD1 badD2 r.1).1 = true ∨
            (verifyPair badD1 badD2 r.1).2 = true).card = 2 := by
    have heq :
        Finset.univ.filter (fun r : Challenge 5 1 =>
          (verifyPair badD1 badD2 r.1).1 = true ∨ (verifyPair badD1 badD2 r.1).2 = true) =
        Finset.univ.filter (fun r : Challenge 5 1 =>
          (r.1 - 2) * (r.1 - 3) = 0) := by
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
      (Finset.univ.filter (· ∈ (fun r : Challenge 5 1 => verifyPair badD1 badD2 r.1) ⁻¹'
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
    (Finset.univ.filter (fun r : Challenge 6 1 => A₁.eval r.1 * B₁.eval r.1 = 0)).card > 2 * 1 ∧
    Fintype.card (Challenge 6 1) = 4 := by
  refine ⟨?_, ?_, by decide⟩
  · suffices (2 * (1 : ZMod 6) + 2) * (1 + 3) ≠ 0 by
      simpa only [eval_add, eval_mul, eval_ofNat, eval_X, eval_one] using this
    decide
  · have hfilt :
        Finset.univ.filter (fun r : Challenge 6 1 =>
          ((2 * X + 2 : (ZMod 6)[X]).eval r.1) * ((X + 3 : (ZMod 6)[X]).eval r.1) = 0) =
        Finset.univ.filter (fun r : Challenge 6 1 =>
          (2 * r.1 + 2) * (r.1 + 3) = 0) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, eval_add, eval_mul,
        eval_ofNat, eval_X]
    have hcount :
        (Finset.univ.filter (fun r : Challenge 6 1 =>
          (2 * r.1 + 2) * (r.1 + 3) = 0)).card = 3 := by
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
  let t₁ : Fin 3 → TripleShare (ZMod 5) := fun k => if k.1 = 0 then ⟨1, 1, 1⟩ else ⟨0, 0, 0⟩
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

end CslibFrontierTests.Crypto.ProductRelation
