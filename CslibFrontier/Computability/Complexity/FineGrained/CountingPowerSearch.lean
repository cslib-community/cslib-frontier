/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.FineGrained.CountingExponents
public import CslibFrontier.Computability.Complexity.FineGrained.PowerTime
public import CslibFrontier.Computability.Complexity.FineGrained.CountingSparsificationUniform
public import CslibFrontier.Logics.Propositional.ClauseSet.Sparsification.CountingQuantitative
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Logics.Propositional.ClauseSet.Sparsification.CountingParametersPolyTime
import CslibFrontier.Logics.Propositional.CNF.ModelCount.DenseRelabel
import CslibFrontier.Tactic.EncLen

/-!
# Native search with an input-dependent counting budget

For a fixed width and inverse saving denominator, one deterministic multitape search computes
the disjoint sparse-leaf sum over the original declared variables. The certificate charges
the encoded input, including the unary declared size, and the supplied leaf computation.
Its round factor uses the power saving from [MITHardnessGroup2026SH, Lemma 2.2, §2.2].
A size-based power saving transfers to the occurring variable count for both counting
and decision after polynomial-time dense relabeling. The decision hypothesis
equivalences remain open in #8457.

## Main results

* `polyBounded_nodeBound_powerBudget`: a polynomial bound on the encoded leaf formulas.
* `exists_computableInO_searchDeclared_powerBudget`: exact declared counting and separate time
  and workspace bounds from a certified leaf counter.
* `ComputableInPowerExpTime.SharpKSAT_numVars_of_size`: transfer a size-based power saving
  to a power saving in occurring variables.
* `DecidableInPowerExpTime.KSAT_numVars_of_size`: the decision transfer using positive
  answers from the same sparse-leaf traversal.

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

private abbrev declaredSearch {C : Type} (k d : ℕ) (g : (C × ℕ) × CNF ℕ → ℕ)
    (x : C × ℕ × CNF ℕ) : ℕ :=
  searchDeclaredWith Prod.snd (base k d) (budget d) k k g (x.1, x.2.1) x.2.2

private theorem declaredSearch_resources {C : Type} (encC : C ↪ List Bool)
    {k d : ℕ} (hk : 2 ≤ k) (hd : 1 ≤ d)
    {g t s : (C × ℕ) × CNF ℕ → ℕ} {R Q : C × ℕ × CNF ℕ → ℕ}
    (hcounter : ComputableInO g (encPair (encPair encC encUnary) encCNF) encNat t s)
    (hcap : ∀ (p : C × ℕ) (ψ : CNF ℕ),
      let (_, declared) := p
      let M := countingThresholdBase k (countingPowerBudget d declared)
      (∀ c ∈ ψ, c.length ≤ k) → isSparse (countingThreshold M) k ψ = true →
      ψ.vars.toFinset ⊆ Finset.range declared → ψ.length ≤ occBound k M * declared + 1 →
      g (p, ψ) ≤ 2 ^ ψ.numVars)
    (hresources : ∀ (x : C × ℕ × CNF ℕ) (ψ : CNF ℕ),
      let (context, declared, formula) := x
      let M := countingThresholdBase k (countingPowerBudget d declared)
      (∀ c ∈ ψ, c.length ≤ k) → isSparse (countingThreshold M) k ψ = true →
      ψ.vars.toFinset ⊆ Finset.range declared → ψ.length ≤ occBound k M * declared + 1 →
      (encCNF ψ).length ≤ nodeBound k (countingDepthCoeff k M) formula →
      t ((context, declared), ψ) ≤ R x ∧ s ((context, declared), ψ) ≤ Q x) :
    let encInput := encPair encC (encPair encUnary encCNF)
    ∃ (T S : C × ℕ × CNF ℕ → ℕ) (c e : ℕ),
      ComputableInO (declaredSearch k d g) encInput encNat T S ∧
      (PolyBounded (fun x => (encInput x).length) Q →
        PolyBounded (fun x => (encInput x).length) S) ∧
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
    exact ⟨hcap p ψ hw hactive.2 hsupport hclause,
      hresources x ψ hw hactive.2 hsupport hclause hlen⟩
  obtain ⟨c, e, hc, hs⟩ := exists_computableInO_searchDeclaredWith (MOf := base k d) hB hθ
    hM hK hM2 le_rfl htree (depth_polyBounded encC hk d) hcounter
    (fun x hx i _ hi => (hleaf x hx i hi).1)
    (fun x hx i _ hi => (hleaf x hx i hi).2.1)
    (fun x hx i _ hi => (hleaf x hx i hi).2.2)
  refine ⟨_, _, c, e, hc, hs, ?_⟩
  rintro ⟨context, declared, formula⟩
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
  obtain ⟨T, S, c, e, h, hs, ht⟩ := declaredSearch_resources encC hk hd
    (g := g) (t := t) (s := s) (R := R) (Q := Q) hcounter
    (fun p ψ hw hsp hsub hlen => by
      rw [hcorrect p ψ hw hsp hsub hlen]
      exact CNF.modelCount_le_two_pow_numVars ψ) hresources
  refine ⟨declaredSearch k d g, T, S, c, e, h, hs, ?_, ht⟩
  rintro ⟨context, declared, formula⟩
  have hK : 1 ≤ k := by omega
  have hM2 := two_le_countingThresholdBase k (countingPowerBudget d declared)
  exact searchDeclaredWith_eq_ite_modelCountOn_of_normalized
    (NOf := Prod.snd) (MOf := base k d) (BOf := budget d) (p := (context, declared)) (g := g)
    ((by decide : 1 ≤ 2).trans hM2) hK hM2 le_rfl
    (countingTreeBound_countingThresholdBase hK (one_le_countingPowerBudget d declared))
    (fun ψ _ hw hsp hsub hlen => hcorrect _ ψ hw hsp hsub hlen) formula

private theorem exists_budget_power_lt_one {p : ℝ} (hp1 : p < 1) (k : ℕ) :
    ∃ d : ℕ, 1 ≤ d ∧ (1 + (2 * k : ℝ) / d) * p < 1 := by
  obtain ⟨d, hd⟩ := exists_nat_gt (max 1 ((2 * k : ℝ) * p / (1 - p)))
  have h1 : (1 : ℝ) < d := (le_max_left _ _).trans_lt hd
  have hd0 : (0 : ℝ) < d := zero_lt_one.trans h1
  have hprod := (div_lt_iff₀ (sub_pos.mpr hp1)).mp ((le_max_right _ _).trans_lt hd)
  have hfrac : (2 * k : ℝ) * p / d < 1 - p :=
    (div_lt_iff₀ hd0).mpr (by simpa only [mul_comm] using hprod)
  refine ⟨d, by exact_mod_cast h1.le, ?_⟩
  rw [add_mul, one_mul, div_mul_eq_mul_div]
  linarith

private theorem computableInPowerExpTime_declaredSearch_of_size {k : ℕ} (hk : 2 ≤ k)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {g : CNF ℕ → ℕ}
    (hcap : ∀ φ, g φ ≤ 2 ^ φ.numVars)
    (h : ComputableInPowerExpTime g encCNF encNat (fun φ => φ.numVars + φ.length) p) :
    ∃ (d : ℕ) (q : ℝ), 1 ≤ d ∧ 0 < q ∧ q < 1 ∧
      ComputableInPowerExpTime (declaredSearch k d (g ∘ Prod.snd))
        (encPair encUnit (encPair encUnary encCNF)) encNat
        (fun x : Unit × ℕ × CNF ℕ => x.2.1) q := by
  let encInput := encPair encUnit (encPair encUnary encCNF)
  let encLeaf := encPair (encPair encUnit encUnary) encCNF
  obtain ⟨d, hd, hdensity⟩ := exists_budget_power_lt_one hp1 k
  let b : ℝ := 1 + (2 * k : ℝ) / d
  let q : ℝ := max (1 - (d : ℝ)⁻¹) (b * p)
  have hb : (1 : ℝ) ≤ b := le_add_of_nonneg_right (by positivity)
  have hd0 : (0 : ℝ) < d := zero_lt_one.trans_le (by exact_mod_cast hd)
  refine ⟨d, q, hd, (mul_pos (zero_lt_one.trans_le hb) hp).trans_le (le_max_right _ _),
    max_lt_iff.mpr ⟨sub_lt_self _ (inv_pos.mpr hd0), hdensity⟩, ?_⟩
  have hproj : ComputableInPolyTime (Prod.snd : (Unit × ℕ) × CNF ℕ → CNF ℕ) encLeaf encCNF :=
    ComputableInPolyTime.snd _ _
  have hleaf : ComputableInPowerExpTime (g ∘ Prod.snd) encLeaf encNat
      (fun x => x.2.numVars + x.2.length) p := by
    simpa only [one_mul] using h.comp_polyTime hproj (K := 0) (b := 1)
      (μA := fun x => x.2.numVars + x.2.length) (fun _ => by simp) zero_le_one hp.le
  obtain ⟨C, e, hleaf⟩ := hleaf
  obtain ⟨t, a, hclock, ht⟩ := hleaf.exists_computableInO
  obtain ⟨A, hA⟩ := exists_countingPowerBudget_clauseBound_le hk
  let D : ℕ := ⌈(C : ℝ) * (A + 1 : ℝ) ^ p⌉₊
  let X (x : Unit × ℕ × CNF ℕ) : ℝ := x.2.1 + 1
  let Z (x : Unit × ℕ × CNF ℕ) : ℝ := 2 ^ ((D : ℝ) * (X x) ^ (b * p))
  let B (x : Unit × ℕ × CNF ℕ) : ℕ :=
    let (context, declared, formula) := x
    2 * ((encPair encUnit encUnary) (context, declared)).length + 1 +
      nodeBound k (countingDepthCoeff k (base k d (context, declared))) formula
  have hB : PolyBounded (fun x => (encInput x).length) B := by
    have hctx : PolyBounded (fun x : Unit × ℕ × CNF ℕ => (encInput x).length)
        (fun x => ((encPair encUnit encUnary) (x.1, x.2.1)).length) :=
      PolyBounded.self.mono fun x => by enc_len [encInput, encUnit_apply]
    refine ((((PolyBounded.const 2).mul hctx).add (.const 1)).add
      (polyBounded_nodeBound_powerBudget encUnit hk d)).mono ?_
    rintro ⟨context, declared, formula⟩
    exact le_rfl
  let L (x : Unit × ℕ × CNF ℕ) := (encInput x).length
  let P (x : Unit × ℕ × CNF ℕ) := a * (B x + 1) ^ e + a + 1
  have hP : PolyBounded L P :=
    (((PolyBounded.const a).mul ((hB.add (.const 1)).pow e)).add (.const a)).add (.const 1)
  let E (x : Unit × ℕ × CNF ℕ) : ℝ := (a : ℝ) * Z x * ((B x : ℝ) + 1) ^ e + a
  let R (x : Unit × ℕ × CNF ℕ) := ⌈E x⌉₊
  have hZ (x : Unit × ℕ × CNF ℕ) : 1 ≤ Z x :=
    Real.one_le_rpow one_le_two (by positivity)
  have hX (x : Unit × ℕ × CNF ℕ) : 1 ≤ X x :=
    le_add_of_nonneg_left (Nat.cast_nonneg _)
  obtain ⟨T, S, c, f, hm, _, htime⟩ :=
    declaredSearch_resources encUnit hk hd (R := R) (Q := R)
      hclock (fun _ ψ _ _ _ _ => hcap ψ) (by
        rintro ⟨context, declared, formula⟩ ψ _ _ hsupport hclauses hbits
        let x : Unit × ℕ × CNF ℕ := (context, declared, formula)
        have hvars : ψ.numVars ≤ declared := by
          simpa only [CNF.numVars, Finset.card_range] using Finset.card_le_card hsupport
        have hclauses' : (ψ.length : ℝ) ≤ A * (X x) ^ b :=
          (Nat.cast_le.mpr hclauses).trans (hA hd declared)
        have hn : X x ≤ (X x) ^ b := by
          simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (hX x) hb
        have hvars' : (ψ.numVars : ℝ) + 1 ≤ X x :=
          add_le_add (Nat.cast_le.mpr hvars) le_rfl
        have hsize : (ψ.numVars + ψ.length + 1 : ℝ) ≤ (A + 1 : ℝ) * (X x) ^ b := by
          linarith [hvars'.trans hn]
        have hpow := Real.rpow_le_rpow (by positivity) hsize hp.le
        rw [Real.mul_rpow (by positivity) (by positivity),
          ← Real.rpow_mul (zero_le_one.trans (hX x))] at hpow
        have hexp : (2 : ℝ) ^ (C * (ψ.numVars + ψ.length + 1 : ℝ) ^ p) ≤ Z x := by
          apply Real.rpow_le_rpow_of_exponent_le one_le_two
          exact (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg C)).trans
            (by
              rw [← mul_assoc]
              exact mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity))
        have hlen : (encLeaf ((context, declared), ψ)).length ≤ B x := by
          change ((encPair (encPair encUnit encUnary) encCNF) ((context, declared), ψ)).length ≤ _
          rw [length_encPair]
          exact Nat.add_le_add_left hbits _
        have hrun : (t ((context, declared), ψ) : ℝ) ≤ E x := by
          refine (ht ((context, declared), ψ)).trans ?_
          change (a : ℝ) * ((2 : ℝ) ^ (C * ((↑(ψ.numVars + ψ.length) : ℝ) + 1) ^ p) *
            (((encLeaf ((context, declared), ψ)).length : ℝ) + 1) ^ e) + a ≤ E x
          rw [Nat.cast_add]
          have hlen' : ((encLeaf ((context, declared), ψ)).length : ℝ) + 1 ≤
              (B x : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hlen 1
          dsimp only [E]
          rw [mul_assoc]
          exact add_le_add (mul_le_mul_of_nonneg_left
            (mul_le_mul hexp (pow_le_pow_left₀ (by positivity) hlen' _) (by positivity)
              (zero_le_one.trans (hZ x))) (Nat.cast_nonneg a)) le_rfl
        have hR : t ((context, declared), ψ) ≤ R x :=
          Nat.cast_le.mp (hrun.trans (Nat.le_ceil _))
        exact ⟨hR, hR⟩)
  have hPR (x : Unit × ℕ × CNF ℕ) : (R x : ℝ) ≤ Z x * P x := by
    have hceil := (Nat.ceil_lt_add_one (show 0 ≤ E x by dsimp [E]; positivity)).le
    refine hceil.trans ?_
    dsimp only [E, P]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right (hZ x) (show 0 ≤ (a : ℝ) + 1 by positivity)]
  obtain ⟨m, f', hpoly⟩ := (((PolyBounded.const c).mul
    ((PolyBounded.self.add (.const 1)).pow f)).add hP).exists_le
  let F (x : Unit × ℕ × CNF ℕ) : ℝ :=
    2 ^ ((3 + D : ℝ) * (X x) ^ q) * ((L x : ℝ) + 1) ^ f'
  have htime' (x : Unit × ℕ × CNF ℕ) : (T x : ℝ) ≤ (6 * m : ℕ) * F x := by
    obtain ⟨context, declared, formula⟩ := x
    let x : Unit × ℕ × CNF ℕ := (context, declared, formula)
    let Y : ℝ := 2 ^ (3 * (X x) ^ (1 - (d : ℝ)⁻¹))
    let W : ℝ := c * ((L x : ℝ) + 1) ^ f
    have hW : W ≤ Z x * W := le_mul_of_one_le_left (by dsimp [W]; positivity) (hZ x)
    have hWP : W + P x ≤ m * ((L x : ℝ) + 1) ^ f' := by
      dsimp only [W]
      exact_mod_cast hpoly x
    have hYZ : Y * Z x ≤ (2 : ℝ) ^ ((3 + D : ℝ) * (X x) ^ q) := by
      dsimp only [Y, Z]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      apply Real.rpow_le_rpow_of_exponent_le one_le_two
      have h₁ := Real.rpow_le_rpow_of_exponent_le (hX x)
        (le_max_left (1 - (d : ℝ)⁻¹) (b * p))
      have h₂ := Real.rpow_le_rpow_of_exponent_le (hX x)
        (le_max_right (1 - (d : ℝ)⁻¹) (b * p))
      dsimp only [q]
      nlinarith [mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg D)]
    calc
      (T x : ℝ) ≤ 6 * Y * (W + R x) := htime (context, declared, formula)
      _ ≤ 6 * Y * (Z x * (W + P x)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [mul_add]
        exact add_le_add hW (hPR x)
      _ ≤ 6 * Y * (Z x * (m * ((L x : ℝ) + 1) ^ f')) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hWP (by dsimp [Z]; positivity))
          (by positivity)
      _ = 6 * m * ((Y * Z x) * ((L x : ℝ) + 1) ^ f') := by ring
      _ ≤ _ := by
        push_cast
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hYZ (by positivity)) (by positivity)
  refine ⟨3 + D, f', ?_⟩
  exact (ComputableInTimeO.of_computableInO hm htime').mono (6 * m)
    (fun x => by push_cast; exact le_add_of_nonneg_right (by positivity)) (fun _ => by positivity)

/-- A power-saving counter for fixed-width CNF measured by variables plus clauses gives a
power-saving counter measured by the unary declared variable count. The formula may omit
declared variables. Invalid width or support yields zero, with the same time bound.

This is the declared-input counting step of [MITHardnessGroup2026SH, §2.2, Corollary 2.3].
The polynomial factor uses the complete binary encoding with a unary declared count. -/
private theorem computableInPowerExpTime_declaredCount_of_size {k : ℕ} (hk : 2 ≤ k) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1)
    (h : ComputableInPowerExpTime (SharpKSAT k) encCNF encNat (fun φ => φ.numVars + φ.length) p) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ComputableInPowerExpTime
      (fun x : Unit × ℕ × CNF ℕ =>
        let (_, declared, formula) := x
        if validDeclaredInput k declared formula then formula.modelCountOn (Finset.range declared)
        else 0)
      (encPair encUnit (encPair encUnary encCNF)) encNat
      (fun x : Unit × ℕ × CNF ℕ => x.2.1) q := by
  obtain ⟨d, q, _, hq, hq1, hsearch⟩ :=
    computableInPowerExpTime_declaredSearch_of_size hk hp hp1 (SharpKSAT_le_two_pow_numVars k) h
  refine ⟨q, hq, hq1, ?_⟩
  have hK : 1 ≤ k := by omega
  have hcorrect : declaredSearch k d (SharpKSAT k ∘ Prod.snd) =
      (fun x : Unit × ℕ × CNF ℕ =>
        let (_, declared, formula) := x
        if validDeclaredInput k declared formula then formula.modelCountOn (Finset.range declared)
        else 0) := by
    funext x
    obtain ⟨context, declared, formula⟩ := x
    have hM2 := two_le_countingThresholdBase k (countingPowerBudget d declared)
    exact searchDeclaredWith_eq_ite_modelCountOn
      (NOf := Prod.snd) (MOf := base k d) (BOf := budget d) (p := (context, declared))
      (g := SharpKSAT k ∘ Prod.snd) ((by decide : 1 ≤ 2).trans hM2) hK hM2 le_rfl
      (countingTreeBound_countingThresholdBase hK (one_le_countingPowerBudget d declared))
      (fun _ hw _ _ => SharpKSAT_of_width hw) formula
  rwa [hcorrect] at hsearch

private abbrev declaredSat (k : ℕ) : Set (Unit × ℕ × CNF ℕ) :=
  {x | let (_, declared, formula) := x
       validDeclaredInput k declared formula = true ∧ formula.Satisfiable}

private theorem decidableInPowerExpTime_declaredSat_of_size {k : ℕ} (hk : 2 ≤ k) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1)
    (h : DecidableInPowerExpTime (KSAT k) encCNF (fun φ => φ.numVars + φ.length) p) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ DecidableInPowerExpTime (declaredSat k)
      (encPair encUnit (encPair encUnary encCNF)) (fun x => x.2.1) q := by
  let encInput := encPair encUnit (encPair encUnary encCNF)
  obtain ⟨C, e, h⟩ := h
  obtain ⟨answer, hanswer, ha⟩ := decidableInTimeO_iff_exists_computableInTimeO.mp h
  have hb : ComputableInPowerExpTime answer encCNF encBool
      (fun φ => φ.numVars + φ.length) p := ⟨C, e, ha⟩
  have hnat : ComputableInPowerExpTime Bool.toNat encBool encNat (fun _ => 0) 0 := by
    have hc : ComputableInPolyTime Bool.toNat encBool encNat := .of_finite _
    obtain ⟨f, hf⟩ := ComputableInExpTime.of_computableInPolyTime (μ := fun _ => 0) hc
    exact ⟨0, f, by simpa [ComputableInExpTime] using hf⟩
  let g := Bool.toNat ∘ answer
  have hg : ComputableInPowerExpTime g encCNF encNat (fun φ => φ.numVars + φ.length) p := by
    simpa only [mul_zero, max_eq_left hp.le] using
      hnat.comp hb (K := 0) (b := 0) (fun _ => by norm_num) le_rfl
  have hcap (φ : CNF ℕ) : g φ ≤ 2 ^ φ.numVars :=
    (Bool.toNat_le (answer φ)).trans Nat.one_le_two_pow
  have hpos (φ : CNF ℕ) : 0 < g φ ↔ φ ∈ KSAT k := by
    rw [hanswer φ]
    change 0 < (answer φ).toNat ↔ answer φ = true
    cases answer φ <;> decide
  obtain ⟨d, q, _, hq, hq1, hsearch⟩ :=
    computableInPowerExpTime_declaredSearch_of_size hk hp hp1 hcap hg
  let search := declaredSearch (C := Unit) k d (g ∘ Prod.snd)
  have hK : 1 ≤ k := by omega
  have hlen : PolyBounded (fun x => (encInput x).length)
      (fun x => (encNat (search x)).length) := by
    refine (PolyBounded.self.add (.const 1)).mono ?_
    rintro ⟨context, declared, formula⟩
    have hM2 := two_le_countingThresholdBase k (countingPowerBudget d declared)
    apply (length_encNat_searchDeclaredWith_le
      (NOf := Prod.snd) (MOf := base k d) (BOf := budget d) (p := (context, declared))
      ((by decide : 1 ≤ 2).trans hM2) hK hM2 le_rfl
      (countingTreeBound_countingThresholdBase hK (one_le_countingPowerBudget d declared))
      (g ∘ Prod.snd) formula).trans
    enc_len [encInput]
  have hset : {x | decide (0 < search x) = true} = declaredSat k := by
    ext x
    obtain ⟨context, declared, formula⟩ := x
    change (decide (0 < search (context, declared, formula)) = true) ↔
      validDeclaredInput k declared formula = true ∧ formula.Satisfiable
    rw [decide_eq_true_eq]
    have hM2 := two_le_countingThresholdBase k (countingPowerBudget d declared)
    refine searchDeclaredWith_pos_iff_of_normalized
      (NOf := Prod.snd) (MOf := base k d) (BOf := budget d) (p := (context, declared))
      ((by decide : 1 ≤ 2).trans hM2) hK hM2 le_rfl
      (countingTreeBound_countingThresholdBase hK (one_le_countingPowerBudget d declared))
      (g := g ∘ Prod.snd) ?_ formula
    intro ψ _ hw _ _ _
    exact (hpos ψ).trans (and_iff_right hw)
  obtain ⟨D, f, hsearch⟩ := hsearch
  obtain ⟨f', hdec⟩ := DecidableInTimeO.of_computableInTimeO_polyBounded
    (fun _ => by positivity) hsearch hlen ComputableInPolyTime.binary_pos
  rw [hset] at hdec
  exact ⟨q, hq, hq1, D, f', hdec⟩

end Cslib.Complexity.CountingSparsify

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

private abbrev prepareDense (φ : CNF ℕ) : Unit × ℕ × CNF ℕ :=
  ((), φ.numVars, φ.denseRelabel)

private theorem computableInPolyTime_prepareDense :
    ComputableInPolyTime prepareDense encCNF (encPair encUnit (encPair encUnary encCNF)) :=
  (ComputableInPolyTime.const ()).prod
    (SAT.computableInPolyTime_numVars.prod SAT.computableInPolyTime_denseRelabel)

private theorem valid_dense_iff_width {k : ℕ} (φ : CNF ℕ) :
    CNF.validDeclaredInput k φ.numVars φ.denseRelabel = true ↔
      ∀ c ∈ φ, c.length ≤ k := by
  rw [CNF.validDeclaredInput_eq_true_iff, CNF.vars_denseRelabel_toFinset,
    and_iff_left (Finset.Subset.refl _), CNF.all_length_le_denseRelabel]

/-- The contrapositive size-to-variable counting step of
[MITHardnessGroup2026SH, v2, §2.2, Corollary 2.3], extended to fixed widths `k ≥ 2`.
A power saving in variables plus clauses yields a power saving in occurring variables.

Polynomial-time dense relabeling preserves clause width and model count. The polynomial factor
charges the original encoded length, including large labels and repeated clauses. -/
theorem ComputableInPowerExpTime.SharpKSAT_numVars_of_size {k : ℕ} (hk : 2 ≤ k) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1)
    (h : ComputableInPowerExpTime (SharpKSAT k) encCNF encNat (fun φ => φ.numVars + φ.length) p) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧
      ComputableInPowerExpTime (SharpKSAT k) encCNF encNat CNF.numVars q := by
  obtain ⟨q, hq, hq1, hcount⟩ := CountingSparsify.computableInPowerExpTime_declaredCount_of_size
    hk hp hp1 h
  have hcomp := hcount.comp_polyTime computableInPolyTime_prepareDense
    (K := 0) (b := 1) (μA := CNF.numVars) (fun _ => by simp) zero_le_one hq.le
  have hcount_eq : (fun x : Unit × ℕ × CNF ℕ =>
      let (_, declared, formula) := x
      if CNF.validDeclaredInput k declared formula then
        formula.modelCountOn (Finset.range declared) else 0) ∘ prepareDense = SharpKSAT k := by
    funext φ
    change (if CNF.validDeclaredInput k φ.numVars φ.denseRelabel then
      φ.denseRelabel.modelCountOn (Finset.range φ.numVars) else 0) = SharpKSAT k φ
    have hv := valid_dense_iff_width (k := k) φ
    by_cases hw : ∀ c ∈ φ, c.length ≤ k
    · rw [ite_eq_left (hv.mpr hw), CNF.modelCountOn_denseRelabel, SharpKSAT_of_width hw]
    · rw [ite_eq_right (fun hvalid => hw (hv.mp hvalid)), SharpKSAT_of_not_width hw]
  refine ⟨q, hq, hq1, ?_⟩
  simpa only [one_mul, hcount_eq] using hcomp

/-- The contrapositive size-to-variable decision step of
[MITHardnessGroup2026SH, v2, §2.2, Corollary 2.3], for fixed widths `k ≥ 2`.
A solver with a fixed power saving in occurring variables plus clauses yields a solver with a
fixed power saving in occurring variables. The polynomial factor charges the original encoded
length. The decision hypothesis equivalences remain open in #8457. -/
theorem DecidableInPowerExpTime.KSAT_numVars_of_size {k : ℕ} (hk : 2 ≤ k) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1)
    (h : DecidableInPowerExpTime (KSAT k) encCNF (fun φ => φ.numVars + φ.length) p) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ DecidableInPowerExpTime (KSAT k) encCNF CNF.numVars q := by
  obtain ⟨q, hq, hq1, hdec⟩ := CountingSparsify.decidableInPowerExpTime_declaredSat_of_size
    hk hp hp1 h
  have hmem (φ : CNF ℕ) : φ ∈ KSAT k ↔ prepareDense φ ∈ CountingSparsify.declaredSat k := by
    change ((∀ c ∈ φ, c.length ≤ k) ∧ φ.Satisfiable) ↔
      (CNF.validDeclaredInput k φ.numVars φ.denseRelabel = true ∧ φ.denseRelabel.Satisfiable)
    rw [valid_dense_iff_width, CNF.satisfiable_denseRelabel]
  refine ⟨q, hq, hq1, ?_⟩
  simpa only [one_mul] using DecidableInPowerExpTime.of_polyTime_reduction
    (μA := CNF.numVars) computableInPolyTime_prepareDense hmem (K := 0) (b := 1)
    (fun _ => by simp) zero_le_one hq.le hdec

end Cslib.Complexity
