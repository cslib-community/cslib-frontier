/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Compiler.GateSweep.Uniform
public import CslibFrontier.Computability.Circuit.Frontier.Correlation.Rectangle
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.SubmatrixRobust
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Computability.Circuit.Frontier.Correlation.Asymptotics
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Nat.Log
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Quadratic-form correlation via disjoint-block-robust polar matrices and node cuts

For circuits of bounded fan-in `r ≥ 3`, a single gate may read `r` inputs at once, so a layout need
not have any layer that has read an exact bisection of the inputs. Instead, a two-coloring
`A ⊆ Compiler.Node c` splits the reachable inputs into three disjoint sets:

* `L`, whose consumer supports lie wholly inside `A`;
* `R'`, whose consumer supports lie wholly inside `Aᶜ`;
* `O`, whose consumer supports straddle the cut.

Fixing any assignment `a : O → Bool` to the straddling inputs reduces `BitString.quadForm Q` on the
remaining coordinates `Oᶜ` to a quadratic form `Q_a` whose polar matrix is the principal submatrix
`(Q + Qᵀ).submatrix (↑) (↑)` (`Matrix.dotProduct_mulVec_self_eq_add` together with `z * z = z` and
`z + z = 0` over `𝔽₂`). On each slice `a`, inputs sharing the circuit output and the trace values of
straddling inner gates `G_cut` form a rectangle across `(L, R')` by
`Compiler.eval_splice_signalFrontier` and `Compiler.trace_gate_splice_signalFrontier`. Lindsey's
lemma and Cauchy–Schwarz across slices then give

`correlation² · 2 ^ ((Q + Qᵀ).blockRank L R') ≤ 2 · 2 ^ |G_cut|`

(`sq_correlation_quadForm_mul_le_of_node_cut`).

When the polar matrix `Q + Qᵀ` has high rank on every square block `S × T` with `Disjoint S T`
(`Matrix.DisjointBlockRobust`, shown to exist with deficiency `2 ⌊√n⌋ + 1` in
`Matrix.exists_disjointBlockRobust`), combining `Compiler.exists_node_cut_margin` with the unread
input bound yields `2 ^ (-γ n)` correlation below `((k₀ + 1) / (r + 2 ^ k₀ - k₀ - 1) - ε) n` inner
gates for all `r ≥ 2` and `k₀ ≥ 1`, hence `Ω(log r) · n` in `(r - 1) * c.innerSize`. Both the
disjoint-block-robust slice reduction across computation-node cuts and the resulting fan-in-`r`
quadratic-form correlation bounds are original to this library.

## Main definitions

* `Cslib.Circuits.Frontier.symmHardForm n`: a nonconstructively chosen `n × n` matrix over `𝔽₂`
  whose polar matrix is disjoint-block-robust with deficiency `2 ⌊√n⌋ + 1`.
* `Cslib.Circuits.Frontier.quadFormGateSweepCoefficient r k₀`: the gate-count threshold
  `(k₀ + 1) / (r + 2 ^ k₀ - k₀ - 1)`.

## Main results

* `Cslib.Circuits.Frontier.sq_correlation_quadForm_mul_le_of_node_cut`: slice correlation bound
  across any node cut `A ⊆ Compiler.Node c`.
* `Cslib.Circuits.Frontier.exists_eventually_abs_correlation_quadForm_le_gateSweep`: exponential
  correlation bound below `quadFormGateSweepCoefficient r k₀` for all `r ≥ 2` and `k₀ ≥ 1`.
* `Cslib.Circuits.Frontier.exists_eventually_abs_correlation_symmHardForm_le_log`: unconditional
  `(log₂ r - log₂ log₂ r - 2 - ε) n` correlation bound against `symmHardForm`.
-/

public section

/-! ### Chosen disjoint-block-robust witness and slice correlation bounds -/

namespace Cslib.Circuits.Frontier

open Set Filter Asymptotics Matrix
open scoped BigOperators

/-- An `n × n` strict upper-triangular matrix over `𝔽₂` (chosen nonconstructively via
`Matrix.exists_polarUpper_disjointBlockRobust`) whose polar matrix is disjoint-block-robust with
deficiency `2 ⌊√n⌋ + 1`. -/
noncomputable def symmHardForm (n : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.toUpper (Matrix.exists_polarUpper_disjointBlockRobust n).choose

/-- The polar matrix of `symmHardForm n` is disjoint-block-robust with deficiency `2 ⌊√n⌋ + 1`. -/
theorem disjointBlockRobust_symmHardForm (n : ℕ) :
    (symmHardForm n + (symmHardForm n)ᵀ).DisjointBlockRobust (2 * Nat.sqrt n + 1) := by
  rw [symmHardForm, ← Matrix.polarUpper_eq]
  exact (Matrix.exists_polarUpper_disjointBlockRobust n).choose_spec

universe v

private theorem zmod_two_mul_self (z : ZMod 2) : z * z = z := by
  decide +revert

private theorem zmod_two_add_self (z : ZMod 2) : z + z = 0 := by
  decide +revert

private def sliceEquiv {n : ℕ} (O : Set (Fin n)) [DecidablePred (· ∈ O)] :
    (Fin n → Bool) ≃ (O → Bool) × (↥Oᶜ → Bool) where
  toFun x := (fun i => x i.val, fun j => x j.val)
  invFun p i := if h : i ∈ O then p.1 ⟨i, h⟩ else p.2 ⟨i, h⟩
  left_inv x := funext fun i => by by_cases h : i ∈ O <;> simp [h]
  right_inv := fun ⟨a, y⟩ => Prod.ext
    (funext fun ⟨i, hi⟩ => dite_eq_left hi)
    (funext fun ⟨j, hj⟩ => dite_eq_right hj)

private theorem sliceEquiv_symm_of_mem {n : ℕ} {O : Set (Fin n)} [DecidablePred (· ∈ O)]
    (a : O → Bool) (y : ↥Oᶜ → Bool) {i : Fin n} (hi : i ∈ O) :
    (sliceEquiv O).symm (a, y) i = a ⟨i, hi⟩ :=
  dite_eq_left hi

private theorem sliceEquiv_symm_of_not_mem {n : ℕ} {O : Set (Fin n)} [DecidablePred (· ∈ O)]
    (a : O → Bool) (y : ↥Oᶜ → Bool) {i : Fin n} (hi : i ∉ O) :
    (sliceEquiv O).symm (a, y) i = y ⟨i, hi⟩ :=
  dite_eq_right hi

/-- **Slice quadratic form.** Fixing `a : O → Bool` on a coordinate set `O ⊆ Fin n` turns
`BitString.quadForm Q` on the remaining coordinates `Oᶜ` into either `BitString.quadForm Q_a` or
its negation, where `Q_a + Q_aᵀ = (Q + Qᵀ).submatrix (↑) (↑)`. -/
private theorem exists_slice_quadForm {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2))
    (O : Set (Fin n)) [DecidablePred (· ∈ O)] (a : O → Bool) :
    ∃ Q_a : Matrix ↥Oᶜ ↥Oᶜ (ZMod 2),
      Q_a + Q_aᵀ = (Q + Qᵀ).submatrix ((↑) : ↥Oᶜ → Fin n) ((↑) : ↥Oᶜ → Fin n) ∧
      ({y : ↥Oᶜ → Bool | BitString.quadForm Q ((sliceEquiv O).symm (a, y))} =
          {y | BitString.quadForm Q_a y} ∨
        {y : ↥Oᶜ → Bool | BitString.quadForm Q ((sliceEquiv O).symm (a, y))} =
          {y | BitString.quadForm Q_a y}ᶜ) := by
  let bit := BitString.bitVal (ZMod 2)
  let u : O → ZMod 2 := fun i => bit (a i)
  let C : Matrix O ↥Oᶜ (ZMod 2) := (Q + Qᵀ).submatrix ((↑) : O → Fin n) ((↑) : ↥Oᶜ → Fin n)
  let d : ↥Oᶜ → ZMod 2 := Cᵀ *ᵥ u
  let Q_a : Matrix ↥Oᶜ ↥Oᶜ (ZMod 2) :=
    Q.submatrix ((↑) : ↥Oᶜ → Fin n) ((↑) : ↥Oᶜ → Fin n) + Matrix.diagonal d
  refine ⟨Q_a, ?_, ?_⟩
  · ext i j
    simp only [Q_a, Matrix.add_apply, Matrix.transpose_apply, Matrix.submatrix_apply]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      have hd0 : d i + d i = 0 := zmod_two_add_self (d i)
      linear_combination hd0
    · have hji : j ≠ i := Ne.symm hij
      simp only [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hji, add_zero]
  · let c₀ : ZMod 2 := u ⬝ᵥ Q.submatrix ((↑) : O → Fin n) ((↑) : O → Fin n) *ᵥ u
    have hval (y : ↥Oᶜ → Bool) :
        (fun i => BitString.bitVal (ZMod 2) ((sliceEquiv O).symm (a, y) i)) ⬝ᵥ
            Q *ᵥ (fun i => BitString.bitVal (ZMod 2) ((sliceEquiv O).symm (a, y) i)) =
          c₀ + (fun j => BitString.bitVal (ZMod 2) (y j)) ⬝ᵥ
            Q_a *ᵥ (fun j => BitString.bitVal (ZMod 2) (y j)) := by
      let v : Fin n → ZMod 2 := fun i => bit ((sliceEquiv O).symm (a, y) i)
      let w : ↥Oᶜ → ZMod 2 := fun j => bit (y j)
      have hvO : O.domRestrict v = u :=
        funext fun ⟨i, hi⟩ => congrArg bit (sliceEquiv_symm_of_mem a y hi)
      have hvOc : Oᶜ.domRestrict v = w :=
        funext fun ⟨j, hj⟩ => congrArg bit (sliceEquiv_symm_of_not_mem a y hj)
      have hsplit := Matrix.dotProduct_mulVec_self_eq_add Q O v
      rw [hvO, hvOc] at hsplit
      have hdiag : u ⬝ᵥ C *ᵥ w = w ⬝ᵥ Matrix.diagonal d *ᵥ w := by
        have hL : u ⬝ᵥ C *ᵥ w = ∑ j : ↥Oᶜ, d j * w j := by
          simp only [d, dotProduct, mulVec, Matrix.transpose_apply, Finset.mul_sum,
            Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
        have hR : w ⬝ᵥ Matrix.diagonal d *ᵥ w = ∑ j : ↥Oᶜ, d j * w j := by
          simp only [dotProduct, mulVec, Matrix.diagonal_apply, ite_mul, zero_mul,
            Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
          refine Finset.sum_congr rfl fun j _ => ?_
          calc w j * (d j * w j) = d j * (w j * w j) := by ring
            _ = d j * w j := by rw [zmod_two_mul_self]
        exact hL.trans hR.symm
      have hQa : w ⬝ᵥ Q_a *ᵥ w =
          w ⬝ᵥ Q.submatrix ((↑) : ↥Oᶜ → Fin n) ((↑) : ↥Oᶜ → Fin n) *ᵥ w +
            w ⬝ᵥ Matrix.diagonal d *ᵥ w := by
        simp only [Q_a, Matrix.add_mulVec, dotProduct_add]
      change v ⬝ᵥ Q *ᵥ v = c₀ + w ⬝ᵥ Q_a *ᵥ w
      rw [hsplit, hdiag, hQa]
      ring
    rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) c₀ with hc₀ | hc₀
    · refine Or.inl (Set.ext fun y => ?_)
      simp only [mem_ofPred_eq, BitString.quadForm_eq_true_iff]
      rw [hval y, hc₀, zero_add]
    · refine Or.inr (Set.ext fun y => ?_)
      simp only [mem_compl_iff, mem_ofPred_eq, BitString.quadForm_eq_true_iff]
      rw [hval y, hc₀]
      exact (by decide : ∀ z : ZMod 2, (1 + z = 1) ↔ ¬ (z = 1)) _

/-- Correlation decomposes as the uniform average of slice correlations across `O → Bool`. -/
private theorem correlation_mul_card_slice {n : ℕ} (S T : Set (Fin n → Bool))
    (O : Set (Fin n)) [DecidablePred (· ∈ O)]
    (e : (Fin n → Bool) ≃ (O → Bool) × (↥Oᶜ → Bool)) :
    correlation S T * Fintype.card (O → Bool) =
      ∑ a : O → Bool, correlation {y | e.symm (a, y) ∈ S} {y | e.symm (a, y) ∈ T} := by
  classical
  have hY : (0 : ℝ) < Fintype.card (↥Oᶜ → Bool) := by positivity
  have hcard : (Fintype.card (Fin n → Bool) : ℝ) =
      (Fintype.card (O → Bool) : ℝ) * Fintype.card (↥Oᶜ → Bool) := by
    have hnat : Fintype.card (Fin n → Bool) =
        Fintype.card (O → Bool) * Fintype.card (↥Oᶜ → Bool) :=
      (Fintype.card_congr e).trans (Fintype.card_prod _ _)
    exact_mod_cast hnat
  have htot := correlation_mul_card_eq_sum S T
  rw [← e.symm.sum_comp, Fintype.sum_prod_type] at htot
  have hslice (a : O → Bool) :
      (∑ y : ↥Oᶜ → Bool, if (e.symm (a, y) ∈ S ↔ e.symm (a, y) ∈ T) then (1 : ℝ) else -1) =
        correlation {y | e.symm (a, y) ∈ S} {y | e.symm (a, y) ∈ T} *
          Fintype.card (↥Oᶜ → Bool) :=
    (correlation_mul_card_eq_sum {y | e.symm (a, y) ∈ S} {y | e.symm (a, y) ∈ T}).symm
  simp_rw [hslice] at htot
  rw [← Finset.sum_mul, hcard] at htot
  nlinarith

/-- **Correlation across a circuit node cut.** For any node cut `A ⊆ Compiler.Node c`, let `L` and
`R'` be the reachable inputs whose consumer supports lie wholly in `A` and wholly in `Aᶜ`, and let
`G_cut` be the inner gates whose support straddles `A`. Then

`correlation² · 2 ^ ((Q + Qᵀ).blockRank L R') ≤ 2 · 2 ^ |G_cut|`. -/
theorem sq_correlation_quadForm_mul_le_of_node_cut {σ : Signature.{v}} {n : ℕ}
    (I : Interpretation σ Bool) (Acc : Set Bool) (c : Circuit σ n 1)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (A : Set (Compiler.Node c)) :
    let L := {i : Fin n | ∃ hi : Compiler.Reach c (.input i),
      Compiler.support c (.input i hi) ⊆ A}
    let R' := {i : Fin n | ∃ hi : Compiler.Reach c (.input i),
      Compiler.support c (.input i hi) ⊆ Aᶜ}
    let G_cut := {g : Compiler.InnerGate c |
      Compiler.ActiveSignal.gate g ∈ Compiler.signalFrontier c A}
    correlation {x | BitString.quadForm Q x} {x | c.eval I x 0 ∈ Acc} ^ 2 *
        2 ^ (Q + Qᵀ).blockRank L R' ≤
      2 * 2 ^ G_cut.ncard := by
  classical
  intro L R' G_cut
  have := Fintype.ofFinite G_cut
  set O : Set (Fin n) := (L ∪ R')ᶜ
  let e := sliceEquiv O
  set S : Set (Fin n → Bool) := {x | BitString.quadForm Q x}
  set T : Set (Fin n → Bool) := {x | c.eval I x 0 ∈ Acc}
  have hLR_disj : Disjoint L R' := by
    refine Set.disjoint_left.mpr fun i ⟨hi, hsubA⟩ ⟨_, hsubAc⟩ => ?_
    obtain ⟨u, hu⟩ := Compiler.support_nonempty (.input i hi)
    exact hsubAc hu (hsubA hu)
  let X_cut : Set ↥Oᶜ := {j : ↥Oᶜ | j.val ∈ L}
  have himgL : (Subtype.val '' X_cut : Set (Fin n)) = L := by
    ext i
    simp only [mem_image, X_cut, mem_ofPred_eq, Subtype.exists]
    exact ⟨fun ⟨_, _, hiL, rfl⟩ => hiL,
      fun hiL => ⟨i, fun hiO => hiO (Or.inl hiL), hiL, rfl⟩⟩
  have himgR : (Subtype.val '' X_cutᶜ : Set (Fin n)) = R' := by
    ext i
    simp only [mem_image, mem_compl_iff, X_cut, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨j, hjOc⟩, hnjL, rfl⟩
      have hLR : j ∈ L ∪ R' := not_not.mp hjOc
      exact hLR.resolve_left hnjL
    · intro hiR
      exact ⟨⟨i, not_not.mpr (Or.inr hiR)⟩, Set.disjoint_right.mp hLR_disj hiR, rfl⟩
  have hslice_bound (a : O → Bool) :
      correlation {y | e.symm (a, y) ∈ S} {y | e.symm (a, y) ∈ T} ^ 2 *
          2 ^ (Q + Qᵀ).blockRank L R' ≤
        2 * 2 ^ G_cut.ncard := by
    obtain ⟨Q_a, hpolar, hSa⟩ := exists_slice_quadForm Q O a
    have hrank : (Q_a + Q_aᵀ).cutRank X_cut = (Q + Qᵀ).blockRank L R' := by
      rw [hpolar, Matrix.cutRank,
        (Q + Qᵀ).blockRank_submatrix Subtype.val_injective Subtype.val_injective X_cut X_cutᶜ,
        himgL, himgR]
    let T_a : Set (↥Oᶜ → Bool) := {y | e.symm (a, y) ∈ T}
    let msg : (↥Oᶜ → Bool) → Bool × (G_cut → Bool) := fun y =>
      (decide (c.eval I (e.symm (a, y)) 0 ∈ Acc),
        fun g => c.program.trace I (e.symm (a, y)) (Compiler.ActiveSignal.gate g.val).wire)
    have hT_msg : ∀ y₁ y₂, msg y₁ = msg y₂ → (y₁ ∈ T_a ↔ y₂ ∈ T_a) := fun y₁ y₂ h => by
      simpa [T_a, T] using (Prod.mk.inj h).1
    have hrect_msg : ∀ y₀ : ↥Oᶜ → Bool, ∃ (B₁ : Set (X_cut → Bool)) (B₂ : Set (↥X_cutᶜ → Bool)),
        {y | msg y = msg y₀} = rectangle X_cut B₁ B₂ := by
      intro y₀
      let cls : Set (↥Oᶜ → Bool) := {y | msg y = msg y₀}
      refine ⟨X_cut.domRestrict '' cls, X_cutᶜ.domRestrict '' cls, ?_⟩
      ext y
      constructor
      · intro hy
        exact ⟨⟨y, hy, rfl⟩, ⟨y, hy, rfl⟩⟩
      · rintro ⟨⟨y₁, hy₁, hdom₁⟩, ⟨y₂, hy₂, hdom₂⟩⟩
        change msg y = msg y₀
        have hcut : ∀ w ∈ Compiler.signalFrontier c A,
            c.program.trace I (e.symm (a, y₁)) w.wire =
              c.program.trace I (e.symm (a, y₂)) w.wire := by
          intro w hw
          cases w with
          | input i hi =>
            have hiO : i ∈ O := by
              rintro (⟨_, hsubA⟩ | ⟨_, hsubAc⟩)
              · obtain ⟨u, hu, huAc⟩ := hw.2
                exact huAc (hsubA hu)
              · obtain ⟨u, hu, huA⟩ := hw.1
                exact hsubAc hu huA
            change (sliceEquiv O).symm (a, y₁) i = (sliceEquiv O).symm (a, y₂) i
            rw [sliceEquiv_symm_of_mem a y₁ hiO, sliceEquiv_symm_of_mem a y₂ hiO]
          | gate g =>
            have hg₁ := congrFun (Prod.mk.inj hy₁).2 ⟨g, hw⟩
            have hg₂ := congrFun (Prod.mk.inj hy₂).2 ⟨g, hw⟩
            exact hg₁.trans hg₂.symm
        have hzx : EqOn (e.symm (a, y)) (e.symm (a, y₁)) (Compiler.nodeReadIn c A) := by
          intro i ⟨hi, u, hu, huA⟩
          change (sliceEquiv O).symm (a, y) i = (sliceEquiv O).symm (a, y₁) i
          by_cases hiO : i ∈ O
          · rw [sliceEquiv_symm_of_mem a y hiO, sliceEquiv_symm_of_mem a y₁ hiO]
          · have hiL : i ∈ L :=
              (not_not.mp hiO : i ∈ L ∪ R').resolve_right fun ⟨_, hsubAc⟩ => hsubAc hu huA
            rw [sliceEquiv_symm_of_not_mem a y hiO, sliceEquiv_symm_of_not_mem a y₁ hiO]
            exact (congrFun hdom₁ ⟨⟨i, hiO⟩, hiL⟩).symm
        have hzy : EqOn (e.symm (a, y)) (e.symm (a, y₂)) (Compiler.nodeReadIn c A)ᶜ := by
          intro i hni
          change (sliceEquiv O).symm (a, y) i = (sliceEquiv O).symm (a, y₂) i
          by_cases hiO : i ∈ O
          · rw [sliceEquiv_symm_of_mem a y hiO, sliceEquiv_symm_of_mem a y₂ hiO]
          · have hniL : i ∉ L := by
              rintro ⟨hi, hsubA⟩
              obtain ⟨u, hu⟩ := Compiler.support_nonempty (.input i hi)
              exact hni ⟨hi, u, hu, hsubA hu⟩
            rw [sliceEquiv_symm_of_not_mem a y hiO, sliceEquiv_symm_of_not_mem a y₂ hiO]
            exact (congrFun hdom₂ ⟨⟨i, hiO⟩, hniL⟩).symm
        have heval := Compiler.eval_splice_signalFrontier I hcut hzx hzy 0
        have hdec : decide (c.eval I (e.symm (a, y)) 0 ∈ Acc) =
            decide (c.eval I (e.symm (a, y₀)) 0 ∈ Acc) := by
          by_cases hoA : Compiler.Node.output 0 ∈ A
          · rw [heval.1 hoA]
            exact (Prod.mk.inj hy₁).1
          · rw [heval.2 hoA]
            exact (Prod.mk.inj hy₂).1
        have htr : (fun g : G_cut =>
            c.program.trace I (e.symm (a, y)) (Compiler.ActiveSignal.gate g.val).wire) =
            fun g : G_cut =>
              c.program.trace I (e.symm (a, y₀)) (Compiler.ActiveSignal.gate g.val).wire := by
          funext g
          have hstep := Compiler.trace_gate_splice_signalFrontier I hcut hzx hzy g.val
          by_cases hgA : Compiler.Node.gate g.val ∈ A
          · rw [hstep.1 hgA]
            exact congrFun (Prod.mk.inj hy₁).2 g
          · rw [hstep.2 hgA]
            exact congrFun (Prod.mk.inj hy₂).2 g
        exact Prod.ext hdec htr
    have hbase := sq_correlation_quadForm_mul_le Q_a T_a msg X_cut hT_msg hrect_msg
    rw [hrank] at hbase
    have hrange : ((range msg).ncard : ℝ) ≤ 2 * 2 ^ G_cut.ncard := by
      have hle := ncard_le_card (range msg)
      rw [Nat.card_prod, Nat.card_fun, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool,
        Nat.card_coe_set_eq] at hle
      exact_mod_cast hle
    have hcorr_sq :
        correlation {y | e.symm (a, y) ∈ S} T_a ^ 2 =
          correlation {y | BitString.quadForm Q_a y} T_a ^ 2 := by
      change correlation {y | BitString.quadForm Q ((sliceEquiv O).symm (a, y))} T_a ^ 2 = _
      rcases hSa with hpos | hneg
      · rw [hpos]
      · rw [hneg, correlation_compl_left, neg_sq]
    change correlation {y | e.symm (a, y) ∈ S} T_a ^ 2 * _ ≤ _
    rw [hcorr_sq]
    exact hbase.trans hrange
  set M_card : ℝ := (Fintype.card (O → Bool) : ℝ)
  have hM_pos : 0 < M_card := by positivity
  have havg := correlation_mul_card_slice S T O e
  have hCS := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (O → Bool)))
    (f := fun a : O → Bool => correlation {y | e.symm (a, y) ∈ S} {y | e.symm (a, y) ∈ T})
  rw [Finset.card_univ] at hCS
  set ρ := (Q + Qᵀ).blockRank L R'
  have hρ_pos : (0 : ℝ) < 2 ^ ρ := by positivity
  have hsum_le := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => hslice_bound a
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.sum_mul] at hsum_le
  have htot_le : (correlation S T * M_card) ^ 2 * 2 ^ ρ ≤
      M_card * (M_card * (2 * 2 ^ G_cut.ncard)) := by
    rw [havg]
    refine (mul_le_mul_of_nonneg_right hCS hρ_pos.le).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hsum_le hM_pos.le
  refine le_of_mul_le_mul_right ?_ (mul_pos hM_pos hM_pos)
  linarith

/-- Unreachable inputs are unread: if `D` contains no reachable input of `c`, then
`correlation² · 2 ^ cutRank D ≤ 2`. -/
theorem sq_correlation_quadForm_mul_le_of_not_reach {σ : Signature.{v}} {n : ℕ}
    (I : Interpretation σ Bool) (Acc : Set Bool) (c : Circuit σ n 1)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) {D : Set (Fin n)}
    (hD : ∀ i ∈ D, ¬ Compiler.Reach c (.input i)) :
    correlation {x | BitString.quadForm Q x} {x | c.eval I x 0 ∈ Acc} ^ 2 *
        2 ^ (Q + Qᵀ).cutRank D ≤ 2 := by
  refine sq_correlation_quadForm_mul_le_of_unread I Acc c Q fun i hi => ?_
  rw [mem_compl_iff, Compiler.read_network]
  exact hD i hi

/-! ### Asymptotic gate-sweep correlation bounds -/

/-- The gate-sweep coefficient `(k₀ + 1) / (r + 2 ^ k₀ - k₀ - 1)` for quadratic-form correlation at
fan-in `r`. -/
@[expose] noncomputable def quadFormGateSweepCoefficient (r k₀ : ℕ) : ℝ :=
  (k₀ + 1 : ℝ) / ((r : ℝ) + (2 : ℝ) ^ k₀ - k₀ - 1)

theorem quadFormGateSweep_denom_ge (r k₀ : ℕ) :
    (r : ℝ) ≤ (r : ℝ) + (2 : ℝ) ^ k₀ - k₀ - 1 := by
  have hk : (k₀ + 1 : ℝ) ≤ (2 : ℝ) ^ k₀ := by
    exact_mod_cast Nat.succ_le_of_lt k₀.lt_two_pow_self
  linarith

theorem quadFormGateSweepCoefficient_pos {r : ℕ} (hr : 1 ≤ r) (k₀ : ℕ) :
    0 < quadFormGateSweepCoefficient r k₀ :=
  div_pos (by positivity) (by
    linarith [quadFormGateSweep_denom_ge r k₀, (by exact_mod_cast hr : (1 : ℝ) ≤ r)])

/-- **Exponentially small correlation with quadratic forms at fan-in `r`.** For every `r ≥ 2`,
`k₀ ≥ 1`, and `ε > 0`, there is `γ > 0` such that if `(Q n + (Q n)ᵀ)` is disjoint-block-robust with
sublinear deficiency `t n = o(n)`, every circuit of fan-in at most `r` with at most
`(quadFormGateSweepCoefficient r k₀ - ε) n` inner gates has correlation at most `2 ^ (-γ n)` with
`BitString.quadForm (Q n)`. -/
theorem exists_eventually_abs_correlation_quadForm_le_gateSweep {r k₀ : ℕ} (hr : 2 ≤ r)
    (hk₀ : 1 ≤ k₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (Q : ∀ n, Matrix (Fin n) (Fin n) (ZMod 2)) (t : ℕ → ℕ),
      (∀ᶠ n in atTop, (Q n + (Q n)ᵀ).DisjointBlockRobust (t n)) →
      (fun n => (t n : ℝ)) =o[atTop] (fun n => (n : ℝ)) →
      ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
        (c : Circuit σ n 1), c.FanInAtMost r →
          (c.innerSize : ℝ) ≤ (quadFormGateSweepCoefficient r k₀ - ε) * n →
          |correlation {x | BitString.quadForm (Q n) x} {x | c.eval I x 0 ∈ Acc}| ≤
            (2 : ℝ) ^ (-γ * n) := by
  set D_r : ℝ := (r : ℝ) + (2 : ℝ) ^ k₀ - k₀ - 1
  have hDr_ge : (2 : ℝ) ≤ D_r :=
    (by exact_mod_cast hr : (2 : ℝ) ≤ r).trans (quadFormGateSweep_denom_ge r k₀)
  have hDr_pos : 0 < D_r := by linarith
  set Q_c := quadFormGateSweepCoefficient r k₀
  have hQc_pos : 0 < Q_c := quadFormGateSweepCoefficient_pos (by omega) k₀
  have hDr_Qc : D_r * Q_c = (k₀ + 1 : ℝ) := by
    dsimp only [Q_c, quadFormGateSweepCoefficient, D_r]
    exact mul_div_cancel₀ _ hDr_pos.ne'
  set θ : ℝ := min (1 / 2) (D_r * ε / (2 * (k₀ + 1 : ℝ)))
  have hθ_pos : 0 < θ := lt_min (by norm_num) (by positivity)
  have hθ_half : θ ≤ 1 / 2 := min_le_left _ _
  set μ₀ : ℝ := D_r * ε / (2 * (2 : ℝ) ^ k₀)
  have hμ₀_pos : 0 < μ₀ := by positivity
  set μ : ℝ := min θ μ₀
  have hμ_pos : 0 < μ := lt_min hθ_pos hμ₀_pos
  refine ⟨μ / 4, by positivity, fun Q t hQ ht => ?_⟩
  set C_err : ℝ := 2 * (r + 1 : ℝ) * √(3 * (Q_c + 1))
  have hCerr_nn : 0 ≤ C_err := by positivity
  filter_upwards [hQ, ht.bound (show 0 < μ / 8 by positivity), eventually_ge_atTop 2,
    eventually_ge_atTop ⌈16 / μ⌉₊,
    eventually_ge_atTop (⌈(8 * C_err / μ) ^ 2⌉₊ + 1)] with n hQn htn hn2 hn_const hn_sqrt
  intro σ I Acc c hfan hsize
  classical
  have := Fintype.ofFinite {i : Fin n // Compiler.Reach c (.input i)}
  have := Fintype.ofFinite (Compiler.InnerGate c)
  have := Fintype.ofFinite (Compiler.ActiveSignal c)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have htn' : (t n : ℝ) ≤ (μ / 8) * n := by simpa only [Real.norm_eq_abs, Nat.abs_cast] using htn
  have hconst_n : 2 ≤ (μ / 8) * n := by
    have : 16 / μ ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn_const)
    linarith [(div_le_iff₀ hμ_pos).mp this]
  apply abs_le_two_rpow_of_sq_le
  let R_in : Set (Fin n) := {i : Fin n | Compiler.Reach c (.input i)}
  set d_un := R_inᶜ.ncard
  have hcompl_in : (R_in.ncard : ℝ) + d_un = n := by
    rw [← Nat.cast_add, ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  by_cases hd : θ * n ≤ d_un
  · -- Case 1: many unreachable (unread) inputs.
    set m_un := min d_un (n / 2)
    obtain ⟨D, hD_sub, hD_card⟩ := Set.exists_subset_card_eq (min_le_left d_un (n / 2))
    have hD_compl : m_un ≤ Dᶜ.ncard := by
      have htot := ncard_add_ncard_compl D
      rw [Nat.card_eq_fintype_card, Fintype.card_fin, hD_card] at htot
      have hm_half : m_un ≤ n / 2 := min_le_right _ _
      omega
    have hcutD : m_un ≤ (Q n + (Q n)ᵀ).cutRank D + t n := by
      have h := hQn.min_le_cutRank_add D
      rwa [hD_card, min_eq_left hD_compl] at h
    have hcorrD := sq_correlation_quadForm_mul_le_of_not_reach I Acc c (Q n)
      fun i hi => hD_sub hi
    have hcorrD' :
        correlation {x | BitString.quadForm (Q n) x} {x | c.eval I x 0 ∈ Acc} ^ 2 *
          2 ^ (Q n + (Q n)ᵀ).cutRank D ≤ 2 * 2 ^ (0 : ℕ) := by
      simpa using hcorrD
    have hstep := le_rpow_of_mul_two_pow_le hcorrD' (r := (m_un : ℝ) - t n) (by
      have : (m_un : ℝ) ≤ (Q n + (Q n)ᵀ).cutRank D + t n := by exact_mod_cast hcutD
      linarith)
    refine hstep.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    have hhalf_lb : (n : ℝ) / 2 - 1 / 2 ≤ ((n / 2 : ℕ) : ℝ) := by
      have : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by
        exact_mod_cast (show n ≤ 2 * (n / 2) + 1 by omega)
      linarith
    have hm_lb : θ * n - 1 / 2 ≤ (m_un : ℝ) := by
      have hθn : θ * n ≤ (n : ℝ) / 2 := by
        have := mul_le_mul_of_nonneg_right hθ_half hn0
        linarith
      dsimp only [m_un]
      rcases min_choice d_un (n / 2) with hmin | hmin <;> rw [hmin] <;> linarith
    have hμ_le_θ : μ ≤ θ := min_le_left _ _
    nlinarith
  · -- Case 2: few unreachable inputs; apply the two-coloring margin on `Node c`.
    push Not at hd
    obtain ⟨A, hLA, hRA, hGA⟩ := Compiler.exists_node_cut_margin c hfan
    let L := {i : Fin n | ∃ hi : Compiler.Reach c (.input i),
      Compiler.support c (.input i hi) ⊆ A}
    let R' := {i : Fin n | ∃ hi : Compiler.Reach c (.input i),
      Compiler.support c (.input i hi) ⊆ Aᶜ}
    let G_cut := {g : Compiler.InnerGate c |
      Compiler.ActiveSignal.gate g ∈ Compiler.signalFrontier c A}
    have hLR_disj : Disjoint L R' := by
      refine Set.disjoint_left.mpr fun i ⟨hi, hsubA⟩ ⟨_, hsubAc⟩ => ?_
      obtain ⟨u, hu⟩ := Compiler.support_nonempty (.input i hi)
      exact hsubAc hu (hsubA hu)
    -- Bound the input sum from below and the gate sum from above via the `k₀`-tangents.
    have hin_lb :
        ∑ i : {i : Fin n // Compiler.Reach c (.input i)},
          (((k₀ + 1 : ℝ) - (Compiler.support c (.input i.val i.property)).ncard) / (2 : ℝ) ^ k₀) ≤
        ∑ i : {i : Fin n // Compiler.Reach c (.input i)},
          (1 / 2 : ℝ) ^ (Compiler.support c (.input i.val i.property)).ncard :=
      Finset.sum_le_sum fun i _ => Compiler.two_pow_neg_ge_tangent hk₀
        ((ncard_pos (toFinite _)).mpr (Compiler.support_nonempty (.input i.val i.property)))
    have hgt_ub :
        ∑ g : Compiler.InnerGate c,
          (1 - (1 / 2 : ℝ) ^ ((Compiler.support c (.gate g)).ncard - 1)) ≤
        ∑ g : Compiler.InnerGate c,
          ((1 - (k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) +
            ((Compiler.support c (.gate g)).ncard : ℝ) / (2 : ℝ) ^ k₀) :=
      Finset.sum_le_sum fun g _ => Compiler.one_sub_two_pow_le_tangent k₀
        ((Compiler.two_le_ncard_support_gate g).trans' (by decide))
    -- Combine the support sums into `∑ w : ActiveSignal c, (support c w).ncard`.
    have htot_supp :
        (∑ i : {i : Fin n // Compiler.Reach c (.input i)},
          ((Compiler.support c (.input i.val i.property)).ncard : ℝ)) +
        (∑ g : Compiler.InnerGate c, ((Compiler.support c (.gate g)).ncard : ℝ)) ≤
        (r + 1 : ℝ) * Nat.card (Compiler.InnerGate c) + 1 := by
      have hnat := Compiler.sum_ncard_support_le_card_innerGate (c := c) hfan
      rw [← (Compiler.ActiveSignal.equiv c).symm.sum_comp (fun w => (Compiler.support c w).ncard),
        Fintype.sum_sum_type] at hnat
      exact_mod_cast hnat
    have hcard_Rin : (Fintype.card {i : Fin n // Compiler.Reach c (.input i)} : ℝ) =
        R_in.ncard := by
      rw [← Nat.card_eq_fintype_card]
      exact_mod_cast (Nat.card_coe_set_eq R_in)
    have hcard_G : (Fintype.card (Compiler.InnerGate c) : ℝ) =
        Nat.card (Compiler.InnerGate c) := by
      rw [Nat.card_eq_fintype_card]
    have hG_le_s : (Nat.card (Compiler.InnerGate c) : ℝ) ≤ c.innerSize := by
      exact_mod_cast Compiler.card_innerGate_le (c := c)
    have hpos2 : (0 : ℝ) < (2 : ℝ) ^ k₀ := by positivity
    have hexp_diff :
        ((k₀ + 1 : ℝ) * R_in.ncard - D_r * Nat.card (Compiler.InnerGate c) - 1) / (2 : ℝ) ^ k₀ ≤
          (∑ i : {i : Fin n // Compiler.Reach c (.input i)},
            (1 / 2 : ℝ) ^ (Compiler.support c (.input i.val i.property)).ncard) -
          (∑ g : Compiler.InnerGate c,
            (1 - (1 / 2 : ℝ) ^ ((Compiler.support c (.gate g)).ncard - 1))) := by
      have hsum_in :
          ∑ i : {i : Fin n // Compiler.Reach c (.input i)},
            (((k₀ + 1 : ℝ) - (Compiler.support c (.input i.val i.property)).ncard) / (2 : ℝ) ^ k₀) =
          ((k₀ + 1 : ℝ) * R_in.ncard -
            ∑ i : {i : Fin n // Compiler.Reach c (.input i)},
              ((Compiler.support c (.input i.val i.property)).ncard : ℝ)) / (2 : ℝ) ^ k₀ := by
        simp_rw [sub_div]
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard_Rin,
          ← Finset.sum_div, mul_div_assoc']
        ring
      have hsum_gt :
          ∑ g : Compiler.InnerGate c,
            ((1 - (k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) +
              ((Compiler.support c (.gate g)).ncard : ℝ) / (2 : ℝ) ^ k₀) =
          (((2 : ℝ) ^ k₀ - k₀ - 2) * Nat.card (Compiler.InnerGate c) +
            ∑ g : Compiler.InnerGate c,
              ((Compiler.support c (.gate g)).ncard : ℝ)) / (2 : ℝ) ^ k₀ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard_G,
          ← Finset.sum_div]
        field_simp
        ring
      refine le_trans ?_ (sub_le_sub hin_lb hgt_ub)
      rw [hsum_in, hsum_gt, ← sub_div]
      refine div_le_div_of_nonneg_right ?_ hpos2.le
      dsimp only [D_r]
      linarith [htot_supp]
    -- Bound the numerator using `d_un < θ * n` and `s ≤ (Q_c - ε) * n`.
    have hnum_lb : μ₀ * n - 1 / (2 : ℝ) ^ k₀ ≤
        ((k₀ + 1 : ℝ) * R_in.ncard - D_r * Nat.card (Compiler.InnerGate c) - 1) / (2 : ℝ) ^ k₀ := by
      have hd_prod : (k₀ + 1 : ℝ) * d_un ≤ (D_r * ε / 2) * n := by
        have hθ_ub : θ ≤ D_r * ε / (2 * (k₀ + 1 : ℝ)) := min_le_right _ _
        have h1 : (d_un : ℝ) ≤ D_r * ε / (2 * (k₀ + 1 : ℝ)) * n :=
          hd.le.trans (mul_le_mul_of_nonneg_right hθ_ub hn0)
        have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ k₀ + 1)
        have hcancel : (k₀ + 1 : ℝ) * (D_r * ε / (2 * (k₀ + 1 : ℝ)) * n) = (D_r * ε / 2) * n := by
          field_simp
        linarith
      have hs_prod : D_r * Nat.card (Compiler.InnerGate c) ≤ (k₀ + 1 : ℝ) * n - D_r * ε * n := by
        have h2 := mul_le_mul_of_nonneg_left (hG_le_s.trans hsize) hDr_pos.le
        rwa [show D_r * ((Q_c - ε) * n) = D_r * Q_c * n - D_r * ε * n by ring, hDr_Qc] at h2
      have hdiv_eq : μ₀ * n - 1 / (2 : ℝ) ^ k₀ = ((D_r * ε / 2) * n - 1) / (2 : ℝ) ^ k₀ := by
        dsimp only [μ₀]
        field_simp
      rw [hdiv_eq]
      refine div_le_div_of_nonneg_right ?_ hpos2.le
      have hRin_eq : (k₀ + 1 : ℝ) * R_in.ncard = (k₀ + 1 : ℝ) * n - (k₀ + 1 : ℝ) * d_un := by
        linarith [congrArg ((k₀ + 1 : ℝ) * ·) hcompl_in]
      linarith
    -- Bound the `O(√n)` deviation term.
    have herr_ub : 2 * ((r + 1 : ℝ) * √(3 * (Nat.card (Compiler.Node c) : ℝ))) ≤ (μ / 8) * n := by
      have hs_qc : (c.innerSize : ℝ) ≤ Q_c * n := by linarith [mul_nonneg hε.le hn0]
      have hnode_le : (Nat.card (Compiler.Node c) : ℝ) ≤ (Q_c + 1) * n := by
        have hnat : (Nat.card (Compiler.Node c) : ℝ) ≤ c.innerSize + 1 := by
          exact_mod_cast (Compiler.card_node_le c)
        linarith
      have hdev1 : 2 * ((r + 1 : ℝ) * √(3 * (Nat.card (Compiler.Node c) : ℝ))) ≤ C_err * √n := by
        have h3 : 3 * (Nat.card (Compiler.Node c) : ℝ) ≤ (3 * (Q_c + 1)) * n := by linarith
        calc 2 * ((r + 1 : ℝ) * √(3 * (Nat.card (Compiler.Node c) : ℝ)))
            ≤ 2 * ((r + 1 : ℝ) * √((3 * (Q_c + 1)) * n)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h3)
                (by positivity)) (by norm_num)
          _ = C_err * √n := by
              rw [Real.sqrt_mul (by positivity)]
              dsimp only [C_err]
              ring
      have hsq_n : (8 * C_err / μ) ^ 2 ≤ n :=
        (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_of_succ_le hn_sqrt)
      have hCerr_le : C_err ≤ (μ / 8) * √n := by
        linarith [(div_le_iff₀ hμ_pos).mp (Real.le_sqrt_of_sq_le hsq_n)]
      calc 2 * ((r + 1 : ℝ) * √(3 * (Nat.card (Compiler.Node c) : ℝ)))
          ≤ C_err * √n := hdev1
        _ ≤ ((μ / 8) * √n) * √n := mul_le_mul_of_nonneg_right hCerr_le (Real.sqrt_nonneg _)
        _ = (μ / 8) * n := by rw [mul_assoc, Real.mul_self_sqrt hn0]
    -- Combine into `min |L| |R'| - |G_cut|` and apply `sq_correlation_quadForm_mul_le_of_node_cut`.
    have hmin_LR :
        μ₀ * n - 1 / (2 : ℝ) ^ k₀ - (μ / 8) * n ≤
          (min L.ncard R'.ncard : ℝ) - G_cut.ncard := by
      rcases min_choice (L.ncard : ℝ) (R'.ncard : ℝ) with hm | hm <;> rw [hm]
      · linarith [hLA, hGA, hexp_diff, hnum_lb, herr_ub]
      · linarith [hRA, hGA, hexp_diff, hnum_lb, herr_ub]
    have hrank_lb : min L.ncard R'.ncard ≤ (Q n + (Q n)ᵀ).blockRank L R' + t n :=
      hQn.min_le hLR_disj
    have hcorr_cut := sq_correlation_quadForm_mul_le_of_node_cut I Acc c (Q n) A
    have hstep := le_rpow_of_mul_two_pow_le hcorr_cut
      (r := (min L.ncard R'.ncard : ℝ) - t n) (by
        have : (min L.ncard R'.ncard : ℝ) ≤ (Q n + (Q n)ᵀ).blockRank L R' + t n := by
          exact_mod_cast hrank_lb
        linarith)
    refine hstep.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    have hpow2_le : 1 / (2 : ℝ) ^ k₀ ≤ 1 := div_le_one_of_le₀
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) (by positivity)
    have hμn_le : μ * n ≤ μ₀ * n := mul_le_mul_of_nonneg_right (min_le_right _ _) hn0
    dsimp only [L, R', G_cut] at hmin_LR
    linarith

/-- The deficiency `2 ⌊√n⌋ + 1` of `symmHardForm` is `o(n)`. -/
theorem isLittleO_sqrt_deficiency :
    (fun n : ℕ => ((2 * Nat.sqrt n + 1 : ℕ) : ℝ)) =o[atTop] fun n => (n : ℝ) := by
  refine IsLittleO.of_bound fun δ hδ => ?_
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop ⌈9 / δ ^ 2⌉₊] with n hn1 hnC
  have h2s : ((2 * Nat.sqrt n + 1 : ℕ) : ℝ) ≤ 3 * (Nat.sqrt n : ℝ) := by
    exact_mod_cast (show 2 * Nat.sqrt n + 1 ≤ 3 * Nat.sqrt n by
      have := Nat.sqrt_pos.mpr hn1
      omega)
  have hsq_le : ((Nat.sqrt n : ℝ)) * (Nat.sqrt n : ℝ) ≤ n := by exact_mod_cast Nat.sqrt_le n
  have h9 : 9 ≤ δ ^ 2 * n :=
    (div_le_iff₀' (by positivity)).mp ((Nat.le_ceil _).trans (by exact_mod_cast hnC))
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  refine (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (by positivity) two_ne_zero).mp ?_
  nlinarith [pow_le_pow_left₀ (Nat.cast_nonneg _) h2s 2,
    mul_le_mul_of_nonneg_right h9 (Nat.cast_nonneg (α := ℝ) n)]

/-- **Unconditional correlation bound against `symmHardForm`.** For every `r ≥ 2`, `k₀ ≥ 1`, and
`ε > 0`, some `γ > 0` bounds the correlation of `BitString.quadForm (symmHardForm n)` with every
circuit of fan-in at most `r` and at most `(quadFormGateSweepCoefficient r k₀ - ε) n` inner gates by
`2 ^ (-γ n)`. -/
theorem exists_eventually_abs_correlation_symmHardForm_le_gateSweep {r k₀ : ℕ} (hr : 2 ≤ r)
    (hk₀ : 1 ≤ k₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop,
      ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
        (c : Circuit σ n 1), c.FanInAtMost r →
          (c.innerSize : ℝ) ≤ (quadFormGateSweepCoefficient r k₀ - ε) * n →
          |correlation {x | BitString.quadForm (symmHardForm n) x}
            {x | c.eval I x 0 ∈ Acc}| ≤ (2 : ℝ) ^ (-γ * n) := by
  obtain ⟨γ, hγ, H⟩ := exists_eventually_abs_correlation_quadForm_le_gateSweep.{v} hr hk₀ hε
  exact ⟨γ, hγ, H symmHardForm (fun n => 2 * Nat.sqrt n + 1)
    (Eventually.of_forall disjointBlockRobust_symmHardForm) isLittleO_sqrt_deficiency⟩

/-- Dyadic tangent parameter `k₀ = ⌊log₂ (r / ⌊log₂ r⌋)⌋` for `r ≥ 4`, satisfying `1 ≤ k₀`,
`k₀ · 2 ^ k₀ ≤ r`, and `log₂ r - log₂ log₂ r ≤ k₀ + 1`. -/
theorem exists_mul_two_pow_le_and_logb_sub_logb_le {r : ℕ} (hr : 4 ≤ r) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧ k₀ * 2 ^ k₀ ≤ r ∧
      Real.logb 2 r - Real.logb 2 (Real.logb 2 r) ≤ k₀ + 1 := by
  set ℓ := Nat.log 2 r
  have hℓ2 : 2 ≤ ℓ := Nat.le_log_of_pow_le one_lt_two hr
  have hpow_ℓ : 2 ^ ℓ ≤ r := Nat.pow_log_le_self 2 (by omega)
  have hdiv_ge2 : 2 ≤ r / ℓ := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    have h := Nat.lt_two_pow_self (n := ℓ - 1)
    have h2 : 2 ^ ℓ = 2 * 2 ^ (ℓ - 1) := by rw [← pow_succ', Nat.sub_add_cancel (by omega)]
    omega
  set k₀ := Nat.log 2 (r / ℓ)
  have hk₀1 : 1 ≤ k₀ := Nat.le_log_of_pow_le one_lt_two hdiv_ge2
  have hk₀_le_r : 2 ^ k₀ * ℓ ≤ r := by
    have h := Nat.pow_log_le_self 2 (show r / ℓ ≠ 0 by omega)
    exact (Nat.mul_le_mul_right ℓ h).trans (Nat.div_mul_le_self r ℓ)
  have hr_lt_succ : r < 2 ^ (k₀ + 1) * ℓ := by
    have h : r / ℓ < 2 ^ (k₀ + 1) := by
      simpa [k₀, Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self (b := 2) (by decide) (r / ℓ)
    have hdiv := Nat.div_add_mod r ℓ
    have hmod : r % ℓ < ℓ := Nat.mod_lt r (by omega)
    nlinarith
  have hk₀_le_ℓ : k₀ ≤ ℓ := by
    by_contra hgt
    push Not at hgt
    have : r < 2 ^ k₀ * ℓ := by
      have h : r < 2 ^ (ℓ + 1) := by
        simpa [ℓ, Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self (b := 2) (by decide) r
      have h2 : 2 ^ (ℓ + 1) ≤ 2 ^ k₀ := Nat.pow_le_pow_right (by decide) hgt
      nlinarith
    omega
  have hk₀_pow : k₀ * 2 ^ k₀ ≤ r :=
    (Nat.mul_le_mul_right _ hk₀_le_ℓ).trans ((mul_comm _ _).trans_le hk₀_le_r)
  have hℓ_le_log : (ℓ : ℝ) ≤ Real.logb 2 r := by
    rw [← Real.logb_two_pow ℓ]
    exact Real.logb_le_logb_of_le (by norm_num) (by positivity) (by exact_mod_cast hpow_ℓ)
  have hlog_r_le : Real.logb 2 r ≤ (k₀ : ℝ) + 1 + Real.logb 2 ℓ := by
    have hr_le_real : (r : ℝ) ≤ (2 : ℝ) ^ (k₀ + 1) * ℓ := by exact_mod_cast hr_lt_succ.le
    calc Real.logb 2 r
        ≤ Real.logb 2 ((2 : ℝ) ^ (k₀ + 1) * ℓ) :=
          Real.logb_le_logb_of_le (by norm_num) (by positivity) hr_le_real
      _ = (k₀ : ℝ) + 1 + Real.logb 2 ℓ := by
          rw [Real.logb_mul (by positivity) (by positivity), Real.logb_two_pow]
          push_cast
          ring
  have hll_mono : Real.logb 2 ℓ ≤ Real.logb 2 (Real.logb 2 r) :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) hℓ_le_log
  exact ⟨k₀, hk₀1, hk₀_pow, by linarith⟩

/-- Explicit `Ω(log r)` choice of `k₀ ≥ 1` for `quadFormGateSweepCoefficient`: for all `r ≥ 2`,
some `k₀ ≥ 1` satisfies `log₂ r - log₂ log₂ r - 2 ≤ (r - 1) · quadFormGateSweepCoefficient r k₀`. -/
theorem exists_log_sub_log_log_le_mul_quadFormGateSweepCoefficient {r : ℕ} (hr : 2 ≤ r) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧
      Real.logb 2 r - Real.logb 2 (Real.logb 2 r) - 2 ≤
        (r - 1 : ℝ) * quadFormGateSweepCoefficient r k₀ := by
  rcases lt_or_ge r 4 with hsmall | hr4
  · refine ⟨1, le_rfl, ?_⟩
    have hr_cases : r = 2 ∨ r = 3 := by omega
    rcases hr_cases with rfl | rfl
    · rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) ^ (1 : ℕ) by norm_num, Real.logb_two_pow, Nat.cast_one,
        Real.logb_one]
      unfold quadFormGateSweepCoefficient
      norm_num
    · have hlog3_ge : 1 ≤ Real.logb 2 (3 : ℝ) := by
        rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
        exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by norm_num)
      have hlog3_le : Real.logb 2 (3 : ℝ) ≤ 2 := by
        calc Real.logb 2 (3 : ℝ)
            ≤ Real.logb 2 ((2 : ℝ) ^ (2 : ℕ)) :=
              Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by norm_num)
          _ = 2 := by rw [Real.logb_two_pow]; norm_num
      have hll_nn : 0 ≤ Real.logb 2 (Real.logb 2 (3 : ℝ)) :=
        Real.logb_nonneg (by norm_num) hlog3_ge
      have hrhs : ((3 : ℕ) - 1 : ℝ) * quadFormGateSweepCoefficient 3 1 = 4 / 3 := by
        unfold quadFormGateSweepCoefficient
        norm_num
      push_cast at hrhs ⊢
      linarith
  · obtain ⟨k₀, hk₀1, hk₀_pow, hlog⟩ := exists_mul_two_pow_le_and_logb_sub_logb_le hr4
    refine ⟨k₀, hk₀1, ?_⟩
    have hk₀_alg : (k₀ - 1 : ℝ) ≤ (r - 1 : ℝ) * quadFormGateSweepCoefficient r k₀ := by
      unfold quadFormGateSweepCoefficient
      have hr4_r : (4 : ℝ) ≤ r := by exact_mod_cast hr4
      rw [mul_div_assoc', le_div_iff₀ (by linarith [quadFormGateSweep_denom_ge r k₀])]
      have hk₀_pow_r : (k₀ : ℝ) * (2 : ℝ) ^ k₀ ≤ r := by exact_mod_cast hk₀_pow
      have hk₀1_r : (1 : ℝ) ≤ k₀ := by exact_mod_cast hk₀1
      nlinarith [sq_nonneg ((k₀ : ℝ) - 1)]
    linarith

/-- **Unconditional `Ω(log r)` quadratic-form correlation bound.** For every `r ≥ 2` and `ε > 0`,
some `γ > 0` ensures that every circuit of fan-in at most `r` with
`(r - 1) * c.innerSize ≤ (log₂ r - log₂ log₂ r - 2 - ε) * n` has correlation at most `2 ^ (-γ n)`
with `BitString.quadForm (symmHardForm n)`. -/
theorem exists_eventually_abs_correlation_symmHardForm_le_log {r : ℕ} (hr : 2 ≤ r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop,
      ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
        (c : Circuit σ n 1), c.FanInAtMost r →
          ((r - 1 : ℝ) * c.innerSize) ≤
            (Real.logb 2 r - Real.logb 2 (Real.logb 2 r) - 2 - ε) * n →
          |correlation {x | BitString.quadForm (symmHardForm n) x}
            {x | c.eval I x 0 ∈ Acc}| ≤ (2 : ℝ) ^ (-γ * n) := by
  obtain ⟨k₀, hk₀1, hk₀_le⟩ := exists_log_sub_log_log_le_mul_quadFormGateSweepCoefficient hr
  have hr1_pos : (0 : ℝ) < (r : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast hr)
  obtain ⟨γ, hγ, H⟩ := exists_eventually_abs_correlation_symmHardForm_le_gateSweep.{v} hr hk₀1
    (ε := ε / (r - 1 : ℝ)) (div_pos hε hr1_pos)
  refine ⟨γ, hγ, ?_⟩
  filter_upwards [H] with n hn σ I Acc c hfan hsize
  refine hn σ I Acc c hfan ?_
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hmul : (r - 1 : ℝ) * c.innerSize ≤
      (r - 1 : ℝ) * ((quadFormGateSweepCoefficient r k₀ - ε / (r - 1 : ℝ)) * n) := by
    have hsub :
        Real.logb 2 r - Real.logb 2 (Real.logb 2 r) - 2 - ε ≤
          (r - 1 : ℝ) * (quadFormGateSweepCoefficient r k₀ - ε / (r - 1 : ℝ)) := by
      have hid : (r - 1 : ℝ) * (ε / (r - 1 : ℝ)) = ε := mul_div_cancel₀ ε hr1_pos.ne'
      linarith
    exact hsize.trans ((mul_le_mul_of_nonneg_right hsub hn0).trans_eq (mul_assoc _ _ _))
  exact le_of_mul_le_mul_left hmul hr1_pos

end Cslib.Circuits.Frontier
