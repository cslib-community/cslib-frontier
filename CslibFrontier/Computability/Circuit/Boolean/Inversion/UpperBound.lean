/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Inversion.Basic
public import CslibFrontier.Computability.Circuit.SourceComplexity
import CslibFrontier.Computability.Circuit.Monotone.Formula

/-!
# Synthesis from a bounded descent rank

A target with a descent rank below `2 ^ k` can be computed with at most `k` NOT gates.
The circuit uses exactly the supplied sources and may share all its computed values between
outputs. AND, OR and constants are free under `negationCost`.

The construction halves the rank range. Its upper-half predicate is monotone on the supplied
values, so a monotone circuit computes it. One negation of this bit is adjoined to the inputs.
Comparable augmented inputs lie in the same half, and subtracting the half's offset yields a
rank below `2 ^ (k - 1)`. Induction supplies the remaining circuit. At rank zero, a monotone
extension of the partial target is synthesized in the existing monotone basis.

This is the synthesis direction of [Markov1963, Theorem 4.1]. A descent rank is an invariant
supplied to this lemma; the companion chain theorem constructs it from the target itself.

## Main results

* `Cslib.Circuits.Boolean.exists_computesFrom_of_descentRank`: native circuit synthesis from
  a rank below a power of two, charging only negations.

## References

* [A. A. Markov, *On the Inversion Complexity of a System of Boolean Functions*][Markov1963],
  Theorem 4.1 and Lemma 5.1, printed p. 478. The supplied-source induction here peels the
  highest rank bit instead of writing all threshold and binary-digit functions at once.
-/

public section

namespace Cslib.Circuits.Boolean

variable {X : Type*} {n m : ℕ}

private theorem exists_zero_negations_of_monotone
    (sources : X → BitString n) (target : X → BitString m)
    (h : ∀ ⦃x y⦄, sources x ≤ sources y → target x ≤ target y) :
    ∃ C : Circuit signature n m,
      C.ComputesFrom interpretation target sources ∧ C.program.cost negationCost = 0 := by
  classical
  let extension (z : BitString n) (j : Fin m) : Bool :=
    decide (∃ x, sources x ≤ z ∧ target x j = true)
  have hext (x : X) : extension (sources x) = target x := by
    funext j
    apply Bool.eq_iff_iff.mpr
    simp only [extension, decide_eq_true_eq]
    exact ⟨fun ⟨y, hy, htrue⟩ => Bool.eq_true_of_true_le (htrue ▸ h hy j),
      fun htrue => ⟨x, le_rfl, htrue⟩⟩
  have hmono (j : Fin m) : Monotone (fun z => extension z j) := by
    intro a b hab
    rw [Bool.le_iff_imp]
    simp only [extension, decide_eq_true_eq]
    exact fun ⟨x, hx, hj⟩ => ⟨x, hx.trans hab, hj⟩
  choose formulas hformulas using fun j => Monotone.exists_computes_of_monotone (hmono j)
  let circuits (j : Fin m) : Circuit signature n 1 :=
    (formulas j).toCircuit.mapOp Monotone.toDeMorgan
  have hcost (j : Fin m) : (circuits j).program.cost negationCost = 0 := by
    change ((formulas j).toCircuit.program.mapOp Monotone.toDeMorgan).cost negationCost = 0
    rw [Program.cost_mapOp]
    have hz : negationCost ∘ Monotone.toDeMorgan = fun _ => 0 := by
      funext op
      cases op <;> rfl
    rw [hz, Program.cost_const, zero_mul]
  refine ⟨Circuit.pi circuits, ?_, ?_⟩
  · intro x
    rw [Circuit.eval_pi]
    funext j
    change ((formulas j).toCircuit.mapOp Monotone.toDeMorgan).eval interpretation (sources x) 0 = _
    rw [Circuit.eval_mapOp (I := Monotone.interpretation), Formula.eval_toCircuit, hformulas j]
    exact congrFun (hext x) j
  · rw [Circuit.cost_program_pi]
    simp only [hcost, Finset.sum_const_zero]

/-- A rank below `2 ^ k` yields a native circuit with at most `k` negations. The source family
is the complete set of available inputs, and the target may have any finite number of outputs.
This is the rank-based synthesis step of Markov's theorem, not a premise that a suitable circuit
already exists. -/
theorem exists_computesFrom_of_descentRank (sources : X → BitString n)
    (target : X → BitString m) (rank : X → ℕ) {k : ℕ}
    (hrank : IsDescentRank sources target rank) (hbound : ∀ x, rank x < 2 ^ k) :
    ∃ C : Circuit signature n m,
      C.ComputesFrom interpretation target sources ∧ C.program.cost negationCost ≤ k := by
  classical
  induction k generalizing n rank with
  | zero =>
    obtain ⟨C, hC, hcost⟩ := exists_zero_negations_of_monotone sources target
      (fun {x y} hxy => hrank.preserves_eq hxy (by have := hbound x; have := hbound y; simp_all))
    exact ⟨C, hC, hcost.le⟩
  | succ k ih =>
    let half := 2 ^ k
    let high (x : X) : Bool := decide (half ≤ rank x)
    let augmented (x : X) : BitString (n + 1) := Fin.snoc (sources x) (!(high x))
    let reduced (x : X) : ℕ := if half ≤ rank x then rank x - half else rank x
    have hhalf : 0 < half := Nat.two_pow_pos k
    have hrange (x : X) : rank x < 2 * half := by
      simpa only [Nat.pow_succ, Nat.mul_comm] using hbound x
    have hsame {x y : X} (hxy : augmented x ≤ augmented y) :
        sources x ≤ sources y ∧ high x = high y := by
      have hsource : sources x ≤ sources y := fun i => by
        simpa only [augmented, Fin.snoc_castSucc] using hxy i.castSucc
      have hlow := hxy (Fin.last n)
      simp only [augmented, Fin.snoc_last] at hlow
      have hhigh : high x ≤ high y := by
        rw [Bool.le_iff_imp]
        simp only [high, decide_eq_true_eq]
        exact fun hx => hx.trans (hrank.monotone hsource)
      refine ⟨hsource, ?_⟩
      cases hx : high x <;> cases hy : high y <;> simp_all [Bool.le_iff_imp]
    have hreduced : IsDescentRank augmented target reduced := by
      constructor
      · intro x y hxy
        obtain ⟨hsource, heq⟩ := hsame hxy
        have horder := hrank.monotone hsource
        have heq' : (half ≤ rank x) ↔ half ≤ rank y := by
          simpa only [high, decide_eq_decide] using heq
        dsimp only [reduced]
        split_ifs <;> omega
      · intro x y hxy heqrank
        obtain ⟨hsource, heq⟩ := hsame hxy
        apply hrank.preserves_eq hsource
        have heq' : (half ≤ rank x) ↔ half ≤ rank y := by
          simpa only [high, decide_eq_decide] using heq
        dsimp only [reduced] at heqrank
        split_ifs at heqrank <;> omega
    have hsmall (x : X) : reduced x < 2 ^ k := by
      have := hrange x
      dsimp only [reduced]
      split_ifs <;> omega
    obtain ⟨D, hD, hDcost⟩ := ih augmented reduced hreduced hsmall
    have hhighmono : ∀ ⦃x y⦄, sources x ≤ sources y →
        (fun _ : Fin 1 => high x) ≤ (fun _ : Fin 1 => high y) := by
      intro x y hxy j
      rw [Bool.le_iff_imp]
      simp only [high, decide_eq_true_eq]
      exact fun hx => hx.trans (hrank.monotone hxy)
    obtain ⟨H, hH, hHcost⟩ := exists_zero_negations_of_monotone sources
      (fun x _ => high x) hhighmono
    let negate : Circuit signature 1 1 := Circuit.oneGate .not id
    let step : Circuit signature n (n + 1) :=
      (Circuit.wiring signature id).append (negate.comp H)
    have hstep : step.ComputesFrom interpretation augmented sources := by
      intro x
      simp only [step, Circuit.eval_append, Circuit.eval_wiring, Circuit.eval_comp, hH x]
      rw [Fin.append_right_eq_snoc]
      rfl
    have hstepcost : step.program.cost negationCost = 1 := by
      rw [Circuit.cost_program_append, Circuit.cost_program_wiring,
        Circuit.cost_program_comp, hHcost, Circuit.cost_program_oneGate]
      rfl
    refine ⟨D.comp step, hstep.comp hD, ?_⟩
    rw [Circuit.cost_program_comp, hstepcost]
    omega

end Cslib.Circuits.Boolean
