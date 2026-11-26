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
import CslibFrontier.Computability.PolyTime.CNF.DeclaredInput
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
  let valid (x : C × ℕ × CNF ℕ) := validDeclaredInput k x.2.1 x.2.2
  let count (x : C × ℕ × CNF ℕ) :=
    searchDeclaredWith Prod.snd (base k d) (budget d) k k g (x.1, x.2.1) x.2.2
  let L (x : C × ℕ × CNF ℕ) := (encInput x).length
  let W (x : C × ℕ × CNF ℕ) := c * (L x + 1) ^ e
  let T₀ (x : C × ℕ × CNF ℕ) :=
    W x + (rounds (budget d (x.1, x.2.1)) x.2.2 + 1) * (W x + R x)
  let S₀ (x : C × ℕ × CNF ℕ) := W x + Q x
  change ComputableInO count encInput encNat T₀ S₀ at hc
  have hv : ComputableInPolyTime valid encInput encBool :=
    (CNF.computableInPolyTime_validDeclaredInput k ComputableInPolyTime.id').comp
      (ComputableInPolyTime.snd encC (encPair encUnary encCNF))
  obtain ⟨b, _, hb⟩ := hv.exists_degree
  have hguard := hb.inO.ite hc (ComputableInO.const (encIn := encInput) 0)
  refine ⟨_, _, _, c + 2, b + e + 1, hguard, ?_, ?_, ?_⟩
  · intro hQ
    exact (((PolyBounded.self.add (.const 1)).pow b).add ((hs hQ).add PolyBounded.self)).mono
      fun x => by
        change (L x + 1) ^ b + (if valid x then S₀ x else L x) ≤
          (L x + 1) ^ b + (S₀ x + L x)
        split <;> omega
  · intro x
    change (if valid x then count x else 0) =
      (if valid x then x.2.2.modelCountOn (Finset.range x.2.1) else 0)
    have hvalue : count x = if valid x then x.2.2.modelCountOn (Finset.range x.2.1) else 0 :=
      searchDeclaredWith_eq_ite_modelCountOn_of_normalized
        (hM _) hK (hM2 _) le_rfl (htree _)
        (fun ψ _ hw hsp hsub hlen => hcorrect _ ψ hw hsp hsub hlen) x.2.2
    rw [hvalue]
    split_ifs <;> rfl
  · rintro ⟨context, declared, formula⟩
    let x : C × ℕ × CNF ℕ := (context, declared, formula)
    let Z := (L x + 1) ^ (b + e + 1)
    let P := (c + 2) * Z
    let Y : ℝ := 2 ^ (3 * (x.2.1 + 1 : ℝ) ^ (1 - (d : ℝ)⁻¹))
    let E : ℝ := (P : ℝ) + R x
    have hY : 1 ≤ Y := Real.one_le_rpow one_le_two (by positivity)
    have hE : 0 ≤ E := by dsimp [E]; positivity
    have hYE : E ≤ Y * E := le_mul_of_one_le_left hE hY
    have hbZ : (L x + 1) ^ b ≤ Z :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have heZ : (L x + 1) ^ e ≤ Z :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hLZ : L x ≤ Z := (Nat.le_succ _).trans (Nat.le_self_pow (by omega) _)
    have hP : (L x + 1) ^ b + (W x + L x) ≤ P := by
      calc
        _ ≤ Z + (c * Z + Z) :=
          Nat.add_le_add hbZ (Nat.add_le_add (Nat.mul_le_mul_left c heZ) hLZ)
        _ = P := by dsimp only [P]; ring
    have hbound : (((L x + 1) ^ b + (W x + L x) : ℕ) : ℝ) ≤ E :=
      (Nat.cast_le.mpr hP).trans (le_add_of_nonneg_right (Nat.cast_nonneg (R x)))
    have hleafBound : ((W x + R x : ℕ) : ℝ) ≤ E := by
      have h : ((W x + R x : ℕ) : ℝ) ≤ ((P + R x : ℕ) : ℝ) :=
        Nat.cast_le.mpr (Nat.add_le_add_right (show W x ≤ P by omega) (R x))
      exact h.trans_eq (Nat.cast_add _ _ : ((P + R x : ℕ) : ℝ) = E)
    have hE_eq : E = (↑(c + 2) : ℝ) * ((L x : ℝ) + 1) ^ (b + e + 1) + R x := by
      dsimp only [E, P, Z]
      push_cast
      rfl
    change (((L x + 1) ^ b + (if valid x then T₀ x else L x) : ℕ) : ℝ) ≤ 6 * Y * _
    rw [← hE_eq]
    by_cases hx : valid x = true
    · have hr := rounds_bound hd (hvars x hx)
      have hprod := mul_le_mul hr hleafBound (by positivity) (by positivity)
      have hfirst : (((L x + 1) ^ b + W x : ℕ) : ℝ) ≤ Y * E :=
        (Nat.cast_le.mpr (Nat.add_le_add_left (Nat.le_add_right _ _) _)).trans
          (hbound.trans hYE)
      rw [ite_eq_left hx]
      calc
        _ = (((L x + 1) ^ b + W x : ℕ) : ℝ) +
          ((rounds (budget d (x.1, x.2.1)) x.2.2 + 1 : ℕ) : ℝ) * ((W x + R x : ℕ) : ℝ) := by
            simp only [T₀, Nat.cast_add, Nat.cast_mul]
            ring
        _ ≤ Y * E + 5 * Y * E := add_le_add hfirst hprod
        _ = _ := by ring
    · rw [ite_eq_right hx]
      have hcost : (((L x + 1) ^ b + L x : ℕ) : ℝ) ≤ E :=
        (Nat.cast_le.mpr (Nat.add_le_add_left (Nat.le_add_left _ _) _)).trans hbound
      exact (hcost.trans hYE).trans (by nlinarith [mul_nonneg (zero_le_one.trans hY) hE])

end Cslib.Complexity.CountingSparsify
