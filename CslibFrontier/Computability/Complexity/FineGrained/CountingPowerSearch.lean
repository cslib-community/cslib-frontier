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
The variable-count equivalence remains open in #8457.

## Main results

* `polyBounded_nodeBound_powerBudget`: a polynomial bound on the encoded leaf formulas.
* `exists_computableInO_searchDeclared_powerBudget`: exact declared counting and separate time
  and workspace bounds from a certified leaf counter.

## References

* [MITHardnessGroup2026SH], §2.2, Lemma 2.2 and Corollary 2.3.
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

/-- The bit length bound for each active leaf formula is polynomial in the full encoded input,
including its unary declared variable count. -/
theorem polyBounded_nodeBound_powerBudget {C : Type} (encC : C ↪ List Bool)
    {k : ℕ} (hk : 2 ≤ k) (d : ℕ) :
    PolyBounded (fun x => (encPair encC (encPair encUnary encCNF) x).length)
      (fun (_, declared, formula) => nodeBound k
        (countingDepthCoeff k (countingThresholdBase k (countingPowerBudget d declared)))
        formula) :=
  nodeBound_polyBounded k (PolyBounded.self.mono fun x =>
    (length_le_encPair_right encUnary encCNF x.2).trans
      (length_le_encPair_right encC (encPair encUnary encCNF) x)) (depth_polyBounded encC hk d)

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

/-- For unary declared variable counts, a fixed power budget gives a native counter from
a certified leaf counter exact on sparse, supported leaves. The time bound holds on all inputs:
a polynomial-time guard rejects invalid formulas before incurring traversal costs. Workspace is
polynomial whenever the leaf workspace allowance is polynomial. -/
theorem exists_computableInO_searchDeclared_powerBudget {C : Type} (encC : C ↪ List Bool)
    {k d : ℕ} (hk : 2 ≤ k) (hd : 1 ≤ d)
    {g t s : (C × ℕ) × CNF ℕ → ℕ} {R Q : C × ℕ × CNF ℕ → ℕ}
    (hcounter : ComputableInO g (encPair (encPair encC encUnary) encCNF) encNat t s)
    (hcorrect : ∀ (p : C × ℕ) (ψ : CNF ℕ),
      let (_, declared) := p
      let M := countingThresholdBase k (countingPowerBudget d declared)
      (∀ c ∈ ψ, c.length ≤ k) → isSparse (countingThreshold M) k ψ = true →
      ψ.vars.toFinset ⊆ Finset.range declared → ψ.length ≤ occBound k M * declared + 1 →
      g (p, ψ) = ψ.modelCount)
    (hresources : ∀ (x : C × ℕ × CNF ℕ) (ψ : CNF ℕ),
      let (context, declared, formula) := x
      let M := countingThresholdBase k (countingPowerBudget d declared)
      (∀ c ∈ ψ, c.length ≤ k) → isSparse (countingThreshold M) k ψ = true →
      ψ.vars.toFinset ⊆ Finset.range declared → ψ.length ≤ occBound k M * declared + 1 →
      (encCNF ψ).length ≤ nodeBound k (countingDepthCoeff k M) formula →
      t ((context, declared), ψ) ≤ R x ∧ s ((context, declared), ψ) ≤ Q x) :
    let encInput := encPair encC (encPair encUnary encCNF)
    ∃ (count T S : C × ℕ × CNF ℕ → ℕ) (c e : ℕ),
      ComputableInO count encInput encNat T S ∧
      (PolyBounded (fun x => (encInput x).length) Q →
        PolyBounded (fun x => (encInput x).length) S) ∧
      (∀ x, let (_, declared, formula) := x
        count x = if validDeclaredInput k declared formula then
          formula.modelCountOn (Finset.range declared) else 0) ∧
      ∀ x, let (_, declared, _) := x
        (T x : ℝ) ≤ 6 * 2 ^ (3 * (declared + 1 : ℝ) ^ (1 - (d : ℝ)⁻¹)) *
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
    obtain ⟨hw, hv, _, hl, hlen⟩ := (iterate_step_prefix_bounds
      (hM p) hK (hM2 p) le_rfl (htree p) (fun ψ => g (p, ψ)) x.2.2 i).2.2.2 hactive
    have hsupport := hv.trans (validDeclaredInput_eq_true_iff.mp hx).2
    have hclause := hl.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (hvars x hx)) 1)
    refine ⟨?_, hresources x ψ hw hactive.2 hsupport hclause hlen⟩
    rw [hcorrect p ψ hw hactive.2 hsupport hclause]
    exact CNF.modelCount_le_two_pow_numVars ψ
  obtain ⟨c, e, hc, hs⟩ := exists_computableInO_searchDeclaredWith (MOf := base k d) hB hθ
    hM hK hM2 le_rfl htree (depth_polyBounded encC hk d) hcounter
    (fun x hx i _ hi => (hleaf x hx i hi).1)
    (fun x hx i _ hi => (hleaf x hx i hi).2.1)
    (fun x hx i _ hi => (hleaf x hx i hi).2.2)
  refine ⟨_, _, _, c, e, hc, hs, ?_, ?_⟩
  · rintro ⟨context, declared, formula⟩
    exact searchDeclaredWith_eq_ite_modelCountOn_of_normalized
      (hM _) hK (hM2 _) le_rfl (htree _)
      (fun ψ _ hw hsp hsub hlen => hcorrect _ ψ hw hsp hsub hlen) formula
  · rintro ⟨context, declared, formula⟩
    let x : C × ℕ × CNF ℕ := (context, declared, formula)
    let W := c * ((encInput x).length + 1) ^ e
    let Y : ℝ := 2 ^ (3 * (declared + 1 : ℝ) ^ (1 - (d : ℝ)⁻¹))
    let E : ℝ := (W : ℝ) + R x
    have hY : 1 ≤ Y := Real.one_le_rpow one_le_two (by positivity)
    have hE : 0 ≤ E := by dsimp [E]; positivity
    have hfirst : (W : ℝ) ≤ Y * E :=
      (le_add_of_nonneg_right (Nat.cast_nonneg (R x))).trans (le_mul_of_one_le_left hE hY)
    have hE_eq : E = (c : ℝ) * (((encInput x).length : ℝ) + 1) ^ e + R x := by
      dsimp only [E, W]
      push_cast
      rfl
    change ((W + (if validDeclaredInput k declared formula then
      (rounds (budget d (context, declared)) formula + 1) * (W + R x) else 0) : ℕ) : ℝ) ≤
      6 * Y * _
    rw [← hE_eq]
    by_cases hx : validDeclaredInput k declared formula = true
    · have hr := rounds_bound hd (hvars x hx)
      let q := rounds (budget d (context, declared)) formula + 1
      rw [ite_eq_left hx, Nat.cast_add W (q * (W + R x)), Nat.cast_mul q (W + R x),
        Nat.cast_add W (R x)]
      calc
        _ ≤ Y * E + 5 * Y * E := add_le_add hfirst
          (mul_le_mul hr (show (W : ℝ) + R x ≤ E from le_rfl) (by positivity) (by positivity))
        _ = _ := by ring
    · rw [ite_eq_right hx, Nat.add_zero]
      exact hfirst.trans (by nlinarith [mul_nonneg (zero_le_one.trans hY) hE])

end Cslib.Complexity.CountingSparsify
