/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.FineGrained.CountingSparsificationUniform
public import CslibFrontier.Logics.Propositional.ClauseSet.Sparsification.CountingQuantitative
import CslibFrontier.Logics.Propositional.ClauseSet.Sparsification.CountingParametersPolyTime
import CslibFrontier.Tactic.EncLen

/-!
# Native search with an input-dependent counting budget

For a fixed width and inverse saving denominator, one deterministic multitape search computes
the disjoint sparse-leaf sum over the original declared variables. The certificate charges
the encoded input, including the unary declared size, and the supplied leaf computation.
Its round factor uses the power saving from [MITHardnessGroup2026SH, Lemma 2.2, §2.2].
The leaf routine is a parameter of this traversal theorem.
-/

public section

namespace Cslib.Complexity.CountingSparsify

open Cslib.Logic.PL Cslib.Logic.PL.CNF.Sparsification Cslib.Logic.PL.ClauseSet.Sparsification
open Cslib.Logic.PL.CNF (validDeclaredInput validDeclaredInput_eq_true_iff)
open Turing.MultiTapeTM
open Sparsify (rounds rounds_add_one_le)

private abbrev budget {C : Type} (d : ℕ) (p : C × ℕ) :=
  countingPowerBudget d p.2

private abbrev base {C : Type} (k d : ℕ) (p : C × ℕ) :=
  countingThresholdBase k (budget d p)

private theorem depth_polyBounded {C : Type} (encC : C ↪ List Bool)
    {k : ℕ} (hk : 2 ≤ k) (d : ℕ) :
    PolyBounded (fun x : C × ℕ × CNF ℕ => (encPair encC (encPair encUnary encCNF) x).length)
      (fun x => countingDepthCoeff k (base k d (x.1, x.2.1))) := by
  have hN : PolyBounded
      (fun x : C × ℕ × CNF ℕ => (encPair encC (encPair encUnary encCNF) x).length)
      (fun x => x.2.1) := PolyBounded.self.mono fun x => by enc_len
  have hB := ((PolyBounded.const 2).mul (hN.add (.const 1))).mono
    (u := fun x => countingPowerBudget d x.2.1) fun x => by
      unfold countingPowerBudget
      exact (Nat.pow_le_pow_right (by decide) (Nat.div_le_self _ _)).trans
        (Nat.pow_clog_le_mul (by decide) (Nat.succ_ne_zero _))
  obtain ⟨A, hA⟩ := exists_countingThresholdBase_le_mul_clog hk
  have hM := (((PolyBounded.const A).mul hB).mul (hB.add (.const 1))).mono
    (u := fun x => base k d (x.1, x.2.1)) fun x =>
      (hA _ (one_le_countingPowerBudget d x.2.1)).trans
        (Nat.mul_le_mul_left _
          (Nat.add_le_add_right (Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le) 1))
  exact ((PolyBounded.const (countingBChoiceCoeff k)).mul (hM.pow (k - 2))).mono
    fun _ => countingDepthCoeff_le_mul_pow
      ((by decide : 1 ≤ 2).trans (two_le_countingThresholdBase _ _))

private theorem rounds_bound {d : ℕ} (hd : 1 ≤ d) {φ : CNF ℕ} {n : ℕ}
    (hn : φ.numVars ≤ n) :
    ((rounds (countingPowerBudget d n) φ + 1 : ℕ) : ℝ) ≤
      5 * 2 ^ (3 * (n + 1 : ℝ) ^ (1 - (d : ℝ)⁻¹)) := by
  have hq : ((φ.numVars / countingPowerBudget d n : ℕ) : ℝ) ≤
      3 * (n + 1 : ℝ) ^ (1 - (d : ℝ)⁻¹) :=
    (Nat.cast_le.mpr ((Nat.div_le_div_right hn).trans (Nat.le_succ _))).trans
      (countingPowerBudget_quotient_le hd n)
  calc
    _ ≤ ((5 * 2 ^ (φ.numVars / countingPowerBudget d n) : ℕ) : ℝ) :=
      Nat.cast_le.mpr (rounds_add_one_le _ _)
    _ ≤ _ := by
      push_cast
      rw [← Real.rpow_natCast]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le one_le_two hq)
        (by norm_num)

/-- A fixed power budget gives a native declared-variable counter from a native width-bounded
leaf counter. On valid inputs the time is a polynomial in the input length plus the leaf-time
allowance, multiplied by a power-saving round factor. Workspace is polynomial if the leaf
workspace allowance is polynomial. The input encodes the declared size in unary. -/
theorem exists_computableInO_searchDeclared_powerBudget {C : Type} (encC : C ↪ List Bool)
    {k d : ℕ} (hk : 2 ≤ k) (hd : 2 ≤ d)
    {g t s : (C × ℕ) × CNF ℕ → ℕ} {R Q : C × ℕ × CNF ℕ → ℕ}
    (hcounter : ComputableInO g (encPair (encPair encC encUnary) encCNF) encNat t s)
    (hcorrect : ∀ p ψ, (∀ c ∈ ψ, c.length ≤ k) → g (p, ψ) = ψ.modelCount)
    (hresources : ∀ (x : C × ℕ × CNF ℕ) (ψ : CNF ℕ), (∀ c ∈ ψ, c.length ≤ k) →
      ψ.vars.toFinset ⊆ Finset.range x.2.1 →
      ψ.length ≤ occBound k (countingThresholdBase k (countingPowerBudget d x.2.1)) * x.2.1 + 1 →
      t ((x.1, x.2.1), ψ) ≤ R x ∧ s ((x.1, x.2.1), ψ) ≤ Q x)
    (hQ : PolyBounded (fun x => (encPair encC (encPair encUnary encCNF) x).length) Q) :
    let encInput := encPair encC (encPair encUnary encCNF)
    ∃ (count T S : C × ℕ × CNF ℕ → ℕ) (c e : ℕ),
      ComputableInO count encInput encNat T S ∧
      PolyBounded (fun x => (encInput x).length) S ∧
      (∀ x, count x = if validDeclaredInput k x.2.1 x.2.2 then
        x.2.2.modelCountOn (Finset.range x.2.1) else 0) ∧
      ∀ x, validDeclaredInput k x.2.1 x.2.2 = true →
        (T x : ℝ) ≤ 6 * 2 ^ (3 * (x.2.1 + 1 : ℝ) ^ (1 - (d : ℝ)⁻¹)) *
          (c * (((encInput x).length : ℝ) + 1) ^ e + R x) := by
  intro encInput
  have hB : ComputableInPolyTime (budget (C := C) d) (encPair encC encUnary) encNat :=
    (computableInPolyTime_countingPowerBudget d).comp
      (ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd _ _))
  have hθ : ComputableInPolyTime
      (fun x : (C × ℕ) × ℕ × ℕ => decide (countingThreshold (base k d x.1) x.2.1 ≤ x.2.2))
      (encPair (encPair encC encUnary) (encPair encUnary encUnary)) encBool :=
    computableInPolyTime_countingThreshold_le_binary.comp
      ((((computableInPolyTime_countingThresholdBase k).comp hB).comp
        (ComputableInPolyTime.fst _ (encPair encUnary encUnary))).prod
        (ComputableInPolyTime.snd _ (encPair encUnary encUnary)))
  have hM2 (p : C × ℕ) : 2 ≤ base k d p := two_le_countingThresholdBase _ _
  have hK : 1 ≤ k := by omega
  have hM (p : C × ℕ) : 1 ≤ base k d p := (by decide : 1 ≤ 2).trans (hM2 p)
  have htree (p : C × ℕ) := countingTreeBound_countingThresholdBase hK
    (one_le_countingPowerBudget d p.2)
  have hvars (x : C × ℕ × CNF ℕ) (hx : validDeclaredInput k x.2.1 x.2.2 = true) :
      x.2.2.numVars ≤ x.2.1 := by
    simpa only [CNF.numVars, Finset.card_range] using
      Finset.card_le_card (validDeclaredInput_eq_true_iff.mp hx).2
  have hleaf (x : C × ℕ × CNF ℕ) (hx : validDeclaredInput k x.2.1 x.2.2 = true) (i : ℕ) :
      let p := (x.1, x.2.1)
      let st := (step (base k d p) k (fun ψ => g (p, ψ)))^[i] (init k x.2.2)
      st.2.1.isEmpty = false ∧ isSparse (countingThreshold (base k d p)) k (st.2.1.headD []) =
        true →
      let ψ := st.2.1.headD []
      g (p, ψ) ≤ 2 ^ ψ.numVars ∧ t (p, ψ) ≤ R x ∧ s (p, ψ) ≤ Q x := by
    intro p st hactive ψ
    obtain ⟨hw, hv, _, hl, _⟩ := (iterate_step_prefix_bounds
      (hM p) hK (hM2 p) le_rfl (htree p) (fun ψ => g (p, ψ)) x.2.2 i).2.2.2 hactive
    refine ⟨?_, hresources x ψ hw (hv.trans (validDeclaredInput_eq_true_iff.mp hx).2)
      (hl.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (hvars x hx)) 1))⟩
    rw [hcorrect p ψ hw]
    exact CNF.modelCount_le_two_pow_numVars ψ
  obtain ⟨c, e, hc, hs⟩ := exists_computableInO_searchDeclaredWith (MOf := base k d) hB hθ
    hM hK hM2 le_rfl htree (depth_polyBounded encC hk d) hcounter
    (fun x hx i _ hi => (hleaf x hx i hi).1)
    (fun x hx i _ hi => (hleaf x hx i hi).2.1)
    (fun x hx i _ hi => (hleaf x hx i hi).2.2) hQ
  refine ⟨_, _, _, c, e, hc, hs, ?_, ?_⟩
  · intro x
    exact searchDeclaredWith_eq_ite_modelCountOn_of_normalized
      (hM _) hK (hM2 _) le_rfl (htree _) (fun ψ _ hw _ _ _ => hcorrect _ ψ hw) x.2.2
  · intro x hx
    have hr := rounds_bound (show 1 ≤ d by omega) (hvars x hx)
    let Y : ℝ := 2 ^ (3 * (x.2.1 + 1 : ℝ) ^ (1 - (d : ℝ)⁻¹))
    let W : ℝ := c * (((encInput x).length : ℝ) + 1) ^ e + R x
    have hY : 1 ≤ Y := Real.one_le_rpow one_le_two (by positivity)
    have hW : 0 ≤ W := by dsimp [W]; positivity
    push_cast
    change c * (((encInput x).length : ℝ) + 1) ^ e +
      ((rounds (budget d (x.1, x.2.1)) x.2.2 : ℝ) + 1) * W ≤ 6 * Y * W
    push_cast at hr
    have hp := mul_le_mul_of_nonneg_right hr hW
    change ((rounds (budget d (x.1, x.2.1)) x.2.2 : ℝ) + 1) * W ≤ 5 * Y * W at hp
    have hfirst : (c : ℝ) * (((encInput x).length : ℝ) + 1) ^ e ≤ Y * W :=
      (le_add_of_nonneg_right (Nat.cast_nonneg (R x))).trans (le_mul_of_one_le_left hW hY)
    linarith

end Cslib.Complexity.CountingSparsify
