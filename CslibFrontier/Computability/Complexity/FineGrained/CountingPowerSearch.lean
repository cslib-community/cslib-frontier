/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.FineGrained.CountingExponents
public import CslibFrontier.Computability.Complexity.FineGrained.RandomizedPowerTime
public import CslibFrontier.Computability.Complexity.FineGrained.CountingSparsificationUniform
public import CslibFrontier.Logics.Propositional.ClauseSet.Sparsification.CountingQuantitative
public import CslibFrontier.Computability.Complexity.Problems.SAT.Declared
import CslibFrontier.Computability.Complexity.FineGrained.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.BitString.Cut
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
and decision after polynomial-time dense relabeling. For bounded-error decision, majority
amplification supplies sufficiently accurate leaf verifiers for a shared-seed search.

## Main results

* `polyBounded_nodeBound_powerBudget`: a polynomial bound on the encoded leaf formulas.
* `exists_computableInO_searchDeclared_powerBudget`: exact declared counting and separate time
  and workspace bounds from a certified leaf counter.
* `exists_computableInO_seededSearch_powerBudget`: a seed-carrying decision machine and
  its error bound from a certified leaf verifier.
* `solvesWithErrorInPowerExpTime_of_powerBudgetLeaves`: allocate a shared seed and combine
  leaf verifiers whose clocks, seed widths, and errors meet the sparsification bounds.
* `ComputableInPowerExpTime.SharpKSAT_numVars_of_size`: transfer a size-based power saving
  to a power saving in occurring variables.
* `DecidableInPowerExpTime.KSAT_numVars_of_size`: the decision transfer using positive
  answers from the same sparse-leaf traversal.
* `SolvesWithErrorInPowerExpTime.KSAT_numVars_of_size`: the bounded-error decision transfer
  using amplified leaf verifiers and a single shared seed.

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

/-- Compile a declared-variable verifier with a shared seed into the power-budget search.
The machine truncates the shared seed to the width requested by each leaf and tests the search
output for positivity. The clock includes the framed seed length and the allowance for computing
a leaf width and running the leaf verifier. Invalid declared formulas are rejected, and on valid
formulas the error fraction is bounded by the leaf error times the leaf-count bound. -/
theorem exists_computableInO_seededSearch_powerBudget {k d : ℕ} (hk : 2 ≤ k) (hd : 1 ≤ d)
    {width : DeclaredCNF → ℕ} {V : DeclaredCNF × List Bool → Bool}
    {Tw Sw : DeclaredCNF → ℕ} {Tv Sv : DeclaredCNF × List Bool → ℕ}
    (hwidth : ComputableInO width encDeclaredCNF encUnary Tw Sw)
    (hV : ComputableInO V (encPair encDeclaredCNF encBits) encBool Tv Sv)
    {R Q : DeclaredCNF × List Bool → ℕ}
    (hresources : ∀ (seed : List Bool) (a : DeclaredCNF) (ψ : CNF ℕ),
      let M := countingThresholdBase k (countingPowerBudget d a.numVars)
      let leaf : DeclaredCNF := ⟨a.numVars, ψ⟩
      let leafSize := (encPair encDeclaredCNF encBits (leaf, seed)).length
      let query := (leaf, seed.take (width leaf))
      (∀ c ∈ ψ, c.length ≤ k) → isSparse (countingThreshold M) k ψ = true →
      ψ.vars.toFinset ⊆ Finset.range a.numVars → ψ.length ≤ occBound k M * a.numVars + 1 →
      (encCNF ψ).length ≤ nodeBound k (countingDepthCoeff k M) a.formula →
      20 * leafSize + Tw leaf + Tv query ≤ R (a, seed) ∧
      20 * leafSize + Sw leaf + Sv query ≤ Q (a, seed)) :
    let encInput := encPair encDeclaredCNF encBits
    ∃ (verify : DeclaredCNF × List Bool → Bool) (T S : DeclaredCNF × List Bool → ℕ) (c e : ℕ),
      ComputableInO verify encInput encBool T S ∧
      (∀ p, (T p : ℝ) ≤ 6 * 2 ^ (3 * (p.1.numVars + 1 : ℝ) ^ (1 - (d : ℝ)⁻¹)) *
        (c * (((encInput p).length : ℝ) + 1) ^ e + R p)) ∧
      (∀ p, validDeclaredInput k p.1.numVars p.1.formula = false → verify p = false) ∧
      ∀ (a : DeclaredCNF) (n : ℕ) (ε : ℝ), 0 ≤ ε →
        validDeclaredInput k a.numVars a.formula = true →
        (∀ ψ : CNF ℕ,
          let M := countingThresholdBase k (countingPowerBudget d a.numVars)
          let leaf : DeclaredCNF := ⟨a.numVars, ψ⟩
          CountingNormalized k ψ → (∀ c ∈ ψ, c.length ≤ k) →
          isSparse (countingThreshold M) k ψ = true →
          ψ.vars.toFinset ⊆ Finset.range a.numVars → ψ.length ≤ occBound k M * a.numVars + 1 →
          (encCNF ψ).length ≤ nodeBound k (countingDepthCoeff k M) a.formula →
          width leaf ≤ n ∧
            (acceptCount (fun p => V p != decide (0 < p.1.formula.modelCount))
              leaf (width leaf) : ℝ) ≤ ε * (2 : ℝ) ^ width leaf) →
        (acceptCount (fun p => verify p !=
          decide (0 < p.1.formula.modelCount)) a n : ℝ) ≤
          (2 : ℝ) ^ (a.formula.numVars / countingPowerBudget d a.numVars + 1) *
            (ε * (2 : ℝ) ^ n) := by
  intro encInput
  let encContext := encPair encBits encUnary
  let encLeaf := encPair encContext encCNF
  let input (x : (List Bool × ℕ) × CNF ℕ) : DeclaredCNF :=
    let ((_, declared), formula) := x
    ⟨declared, formula⟩
  let seed (x : (List Bool × ℕ) × CNF ℕ) := x.1.1
  let query (x : (List Bool × ℕ) × CNF ℕ) :=
    (input x, (seed x).take (width (input x)))
  let g (x : (List Bool × ℕ) × CNF ℕ) := (V (query x)).toNat
  have hinput : ComputableInO input encLeaf encDeclaredCNF
      (fun x => 2 * (encLeaf x).length) (fun x => 2 * (encLeaf x).length) := by
    have hctx := ComputableInO.fst encContext encCNF
    have hf := ComputableInO.snd encContext encCNF
    simpa only [two_mul] using (hctx.snd'.prod hf).of_enc_eq (g := input) fun _ => rfl
  have hseed : ComputableInO seed encLeaf encBits
      (fun x => (encLeaf x).length) (fun x => (encLeaf x).length) :=
    (ComputableInO.fst encContext encCNF).fst'
  have htake := ComputableInO.of_linear ComputableInDegree.bitsTake
  have hquery := hinput.prod (htake.comp_linear (hseed.prod (hwidth.comp hinput)))
  have hnat : ComputableInO Bool.toNat encBool encNat
      (fun x => (encBool x).length) (fun x => (encBool x).length) :=
    ComputableInO.of_linear (ComputableInDegree.of_finite Bool.toNat)
  have hg : ComputableInO g encLeaf encNat
      (fun x => 5 * (encLeaf x).length + Tw (input x) + Tv (query x))
      (fun x => 5 * (encLeaf x).length + Sw (input x) + Sv (query x)) := by
    convert hnat.comp_linear (hV.comp hquery) using 1 <;> funext x <;> dsimp [query] <;> omega
  let toSearch (p : DeclaredCNF × List Bool) :=
    (p.2, p.1.numVars, p.1.formula)
  let fromSearch (x : List Bool × ℕ × CNF ℕ) : DeclaredCNF × List Bool :=
    let (seed, declared, formula) := x
    (⟨declared, formula⟩, seed)
  obtain ⟨Tc, Sc, c, e, hcount, _, htime⟩ := declaredSearch_resources encBits hk hd
    (R := R ∘ fromSearch) (Q := Q ∘ fromSearch) hg
    (fun p ψ _ _ _ _ => (Bool.toNat_le (V (query (p, ψ)))).trans Nat.one_le_two_pow) (by
      rintro ⟨seed, declared, formula⟩ ψ hw hs hv hl hlen
      have h := hresources seed ⟨declared, formula⟩ ψ hw hs hv hl hlen
      have hsize : 5 * (encLeaf ((seed, declared), ψ)).length ≤
          20 * (encInput (⟨declared, ψ⟩, seed)).length := by
        change 5 * (encLeaf ((seed, declared), ψ)).length ≤
          20 * (encPair (encPair encUnary encCNF) encBits ((declared, ψ), seed)).length
        simp only [encLeaf, encContext, length_encPair, encBits_apply]
        omega
      exact ⟨(Nat.add_le_add_right (Nat.add_le_add_right hsize _) _).trans h.1,
        (Nat.add_le_add_right (Nat.add_le_add_right hsize _) _).trans h.2⟩)
  have hunpack : ComputableInO (fun a : DeclaredCNF => (a.numVars, a.formula))
      encDeclaredCNF (encPair encUnary encCNF) (fun a => (encDeclaredCNF a).length)
      (fun a => (encDeclaredCNF a).length) := ComputableInO.of_eq fun _ => rfl
  have hprep : ComputableInO toSearch encInput (encPair encBits (encPair encUnary encCNF))
      (fun p => 2 * (encInput p).length) (fun p => 2 * (encInput p).length) := by
    simpa only [two_mul, toSearch, Function.comp_apply] using
      (ComputableInO.snd encDeclaredCNF encBits).prod
        (hunpack.comp_linear (ComputableInO.fst encDeclaredCNF encBits))
  obtain ⟨b, _, hpos⟩ := ComputableInPolyTime.binary_pos.exists_degree
  let verify (p : DeclaredCNF × List Bool) := decide (0 < declaredSearch k d g (toSearch p))
  let E := max e (max b 1)
  refine ⟨verify, _, _, c * 2 ^ e + 3, E, (hpos.inO.comp hcount).comp hprep, ?_, ?_, ?_⟩
  · intro p
    let L : ℝ := (encInput p).length + 1
    let factor : ℝ := 6 * 2 ^ (3 * (p.1.numVars + 1 : ℝ) ^ (1 - (d : ℝ)⁻¹))
    let x := toSearch p
    have hL : 1 ≤ L := le_add_of_nonneg_left (Nat.cast_nonneg _)
    have hfactor : 1 ≤ factor := by
      have htwo : (1 : ℝ) ≤ 2 ^ (3 * (p.1.numVars + 1 : ℝ) ^ (1 - (d : ℝ)⁻¹)) :=
        Real.one_le_rpow one_le_two (by positivity)
      dsimp only [factor]
      linarith
    have hM2 := two_le_countingThresholdBase k (countingPowerBudget d p.1.numVars)
    have hK : 1 ≤ k := by omega
    have hlen := length_encNat_searchDeclaredWith_le
      (NOf := Prod.snd) (MOf := base k d) (BOf := budget d) (p := (p.2, p.1.numVars))
      ((by decide : 1 ≤ 2).trans hM2) hK hM2 le_rfl
      (countingTreeBound_countingThresholdBase hK (one_le_countingPowerBudget d p.1.numVars))
      g p.1.formula
    have hdecl : encDeclaredCNF p.1 = encPair encUnary encCNF (p.1.numVars, p.1.formula) := rfl
    have hnative : ((encPair encBits (encPair encUnary encCNF) x).length + 1 : ℕ) ≤
        2 * ((encInput p).length + 1) := by
      simp only [x, toSearch, encInput, length_encPair, hdecl, encBits_apply]
      omega
    have hnum : p.1.numVars + 2 ≤ (encInput p).length + 1 := by
      simp only [encInput, length_encPair, hdecl, encUnary_apply, List.length_replicate]
      omega
    have hout : ((encNat (declaredSearch k d g x)).length + 1 : ℝ) ≤ L := by
      have h : (encNat (declaredSearch k d g x)).length + 1 ≤ (encInput p).length + 1 :=
        (Nat.add_le_add_right hlen 1).trans hnum
      simpa only [L, Nat.cast_add, Nat.cast_one] using (Nat.cast_le.mpr h : (_ : ℝ) ≤ _)
    have hLpow : L ≤ L ^ E := by
      simpa only [pow_one] using pow_le_pow_right₀ hL
        (show 1 ≤ E from (le_max_right b 1).trans (le_max_right e _))
    have hposClock : ((encNat (declaredSearch k d g x)).length + 1 : ℝ) ^ b ≤ L ^ E :=
      (pow_le_pow_left₀ (by positivity) hout _).trans
        (pow_le_pow_right₀ hL ((le_max_left b 1).trans (le_max_right e _)))
    have hpoly : (c : ℝ) * ((encPair encBits (encPair encUnary encCNF) x).length + 1 : ℝ) ^ e ≤
        ((c * 2 ^ e : ℕ) : ℝ) * L ^ E := by
      have hcast : ((encPair encBits (encPair encUnary encCNF) x).length + 1 : ℝ) ≤ 2 * L := by
        simpa only [L, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
          (Nat.cast_le.mpr hnative : (_ : ℝ) ≤ _)
      calc
        _ ≤ c * (2 * L) ^ e :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hcast _) (by positivity)
        _ = ((c * 2 ^ e : ℕ) : ℝ) * L ^ e := by push_cast; rw [mul_pow, mul_assoc]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hL (le_max_left e _)) (by positivity)
    have ht : (Tc x : ℝ) ≤ factor *
        (c * ((encPair encBits (encPair encUnary encCNF) x).length + 1 : ℝ) ^ e + R p) := htime x
    change ((2 * (encInput p).length + (Tc x +
      ((encNat (declaredSearch k d g x)).length + 1) ^ b) : ℕ) : ℝ) ≤ _
    push_cast
    calc
      _ ≤ 2 * L ^ E + (factor * (((c * 2 ^ e : ℕ) : ℝ) * L ^ E + R p) + L ^ E) := by
        have hprepClock : ((encInput p).length : ℝ) ≤ L ^ E :=
          (le_add_of_nonneg_right zero_le_one).trans hLpow
        have hsearchClock := ht.trans
          (mul_le_mul_of_nonneg_left (add_le_add_left hpoly _) (zero_le_one.trans hfactor))
        exact add_le_add (mul_le_mul_of_nonneg_left hprepClock (by norm_num))
          (add_le_add hsearchClock hposClock)
      _ = factor * (((c * 2 ^ e : ℕ) : ℝ) * L ^ E + R p) + 3 * L ^ E := by ring
      _ ≤ factor * (((c * 2 ^ e : ℕ) : ℝ) * L ^ E + R p) + factor * (3 * L ^ E) :=
        add_le_add_right
          (le_mul_of_one_le_left (show 0 ≤ 3 * L ^ E by positivity) hfactor) _
      _ = _ := by
        change _ = factor * (((c : ℝ) * 2 ^ e + 3) * L ^ E + R p)
        push_cast
        ring
  · intro p ha
    simp only [verify, toSearch, declaredSearch, searchDeclaredWith_eq_ite_mul, ha,
      Bool.false_eq_true, ite_false, lt_self_iff_false, decide_false]
  · intro a n ε hε ha hleaf
    obtain ⟨hw, hv⟩ := validDeclaredInput_eq_true_iff.mp ha
    have hK : 1 ≤ k := by omega
    have hM2 := two_le_countingThresholdBase k (countingPowerBudget d a.numVars)
    have hvars : a.formula.numVars ≤ a.numVars := by
      simpa only [CNF.numVars, Finset.card_range] using Finset.card_le_card hv
    let W (p : CNF ℕ × List Bool) := decide (0 < search
      (countingThresholdBase k (countingPowerBudget d a.numVars)) k k
      (countingPowerBudget d a.numVars) (fun ψ =>
        (V (⟨a.numVars, ψ⟩, p.2.take (width ⟨a.numVars, ψ⟩))).toNat) p.1) !=
      decide (0 < p.1.modelCount)
    have hW := acceptCount_search_pos_error_le ((by decide : 1 ≤ 2).trans hM2) hK hM2 le_rfl
      (countingTreeBound_countingThresholdBase hK (one_le_countingPowerBudget d a.numVars)) hw
      (fun p => (V (⟨a.numVars, p.1⟩, p.2)).toNat) (fun ψ => width ⟨a.numVars, ψ⟩)
      n hε (by
        intro ψ hnorm hw hsp hsub hl hlen
        obtain ⟨hwidth', herr⟩ := hleaf ψ hnorm hw hsp (hsub.trans hv)
          (hl.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hvars) 1)) hlen
        refine ⟨hwidth', ?_⟩
        have hcountEq : acceptCount (fun p : CNF ℕ × List Bool =>
            decide (0 < (V (⟨a.numVars, p.1⟩, p.2)).toNat) != decide (0 < p.1.modelCount))
            ψ (width ⟨a.numVars, ψ⟩) =
            acceptCount (fun p => V p != decide (0 < p.1.formula.modelCount))
              ⟨a.numVars, ψ⟩ (width ⟨a.numVars, ψ⟩) := by
          unfold acceptCount
          congr 1
          ext bits
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          cases V (⟨a.numVars, ψ⟩, List.ofFn bits) <;> rfl
        rw [hcountEq]
        exact herr)
    have hcongr : acceptCount (fun p => verify p !=
        decide (0 < p.1.formula.modelCount)) a n = acceptCount W a.formula n := by
      unfold acceptCount
      congr 1
      ext bits
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, verify, toSearch, declaredSearch,
        searchDeclaredWith_eq_ite_mul, ha, ↓reduceIte, CanonicallyOrderedAdd.mul_pos,
        Nat.two_pow_pos, W, g, query, input, seed, base, budget]
    rw [hcongr]
    exact hW

/-- The shared-seed assembly step of [MITHardnessGroup2026SH, v2, §7, Theorem 7.1(a)].
Given leaf verifiers with a power-saving clock, a common bound on their seed widths, and
error at most one third of the reciprocal leaf-count bound, the native sparsifier decides
declared width-`k` satisfiability with bounded error. The leaf error allowance depends on the
declared variable count. The unary seed allocation and the full seeded search both run
with a fixed power saving in that count. -/
theorem solvesWithErrorInPowerExpTime_of_powerBudgetLeaves {k d : ℕ} (hk : 2 ≤ k) (hd : 1 ≤ d)
    {width : DeclaredCNF → ℕ} {V : DeclaredCNF × List Bool → Bool}
    {Tw Sw : DeclaredCNF → ℕ} {Tv Sv : DeclaredCNF × List Bool → ℕ}
    (hwidth : ComputableInO width encDeclaredCNF encUnary Tw Sw)
    (hV : ComputableInO V (encPair encDeclaredCNF encBits) encBool Tv Sv)
    {p : ℝ} (hp : p < 1) (A e : ℕ) :
    let encInput := encPair encDeclaredCNF encBits
    let rate (a : DeclaredCNF) := (2 : ℝ) ^ (A * (a.numVars + 1 : ℝ) ^ p)
    let admissible (a : DeclaredCNF) (ψ : CNF ℕ) :=
      let M := countingThresholdBase k (countingPowerBudget d a.numVars)
      (∀ c ∈ ψ, c.length ≤ k) ∧ isSparse (countingThreshold M) k ψ = true ∧
        ψ.vars.toFinset ⊆ Finset.range a.numVars ∧ ψ.length ≤ occBound k M * a.numVars + 1 ∧
        (encCNF ψ).length ≤ nodeBound k (countingDepthCoeff k M) a.formula
    (∀ (a : DeclaredCNF) (ψ : CNF ℕ) (seed : List Bool), admissible a ψ →
      let leaf : DeclaredCNF := ⟨a.numVars, ψ⟩
      let cost := 20 * (encInput (leaf, seed)).length
      let query := (leaf, seed.take (width leaf))
      let bound := rate a * ((encInput (a, seed)).length + 1 : ℝ) ^ e
      ((cost + Tw leaf + Tv query : ℕ) : ℝ) ≤ bound ∧
        ((cost + Sw leaf + Sv query : ℕ) : ℝ) ≤ bound) →
    (∀ (a : DeclaredCNF) (ψ : CNF ℕ), CountingNormalized k ψ → admissible a ψ →
      let leaf : DeclaredCNF := ⟨a.numVars, ψ⟩
      (width leaf : ℝ) ≤ rate a * ((encDeclaredCNF a).length + 1 : ℝ) ^ e ∧
        (acceptCount (fun x => V x != decide (0 < x.1.formula.modelCount))
          leaf (width leaf) : ℝ) ≤
          ((1 / 3 : ℝ) / 2 ^ (a.numVars / countingPowerBudget d a.numVars + 1)) *
            (2 : ℝ) ^ width leaf) →
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ SolvesWithErrorInPowerExpTime
      (PromiseProblem.ofSet {a : DeclaredCNF |
        validDeclaredInput k a.numVars a.formula = true ∧ a.formula.Satisfiable})
      encDeclaredCNF ErrorModel.bounded DeclaredCNF.numVars q := by
  intro encInput rate admissible hresources hleaf
  let L (x : DeclaredCNF × List Bool) : ℝ := (encInput x).length + 1
  let R (x : DeclaredCNF × List Bool) := ⌈rate x.1 * L x ^ e⌉₊
  obtain ⟨verify, T, S, c, f, hverify, hT, hreject, herror⟩ :=
    exists_computableInO_seededSearch_powerBudget hk hd hwidth hV (R := R) (Q := R)
      (fun seed a ψ hw hs hv hl hlen => by
        obtain ⟨ht, hs'⟩ := hresources a ψ seed ⟨hw, hs, hv, hl, hlen⟩
        exact ⟨Nat.cast_le.mp (ht.trans (Nat.le_ceil _)),
          Nat.cast_le.mp (hs'.trans (Nat.le_ceil _))⟩)
  let q : ℝ := max (1 - (d : ℝ)⁻¹) p
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hq₁ : q < 1 := max_lt_iff.mpr ⟨sub_lt_self _ (inv_pos.mpr hd₀), hp⟩
  have hpq : p ≤ q := le_max_right _ _
  have hverify' : ComputableInPowerExpTime verify encInput encBool
      (DeclaredCNF.numVars ∘ Prod.fst) q := by
    let E := max e f
    let F (x : DeclaredCNF × List Bool) : ℝ :=
      2 ^ (((3 + A : ℕ) : ℝ) * (x.1.numVars + 1 : ℝ) ^ q) * L x ^ E
    have hbound (x : DeclaredCNF × List Bool) : (T x : ℝ) ≤ (6 * (c + 2) : ℕ) * F x := by
      let X : ℝ := x.1.numVars + 1
      let Y : ℝ := 2 ^ (3 * X ^ (1 - (d : ℝ)⁻¹))
      let Z := rate x.1
      have hX : 1 ≤ X := le_add_of_nonneg_left (Nat.cast_nonneg _)
      have hL : 1 ≤ L x := le_add_of_nonneg_left (Nat.cast_nonneg _)
      have hZ : 1 ≤ Z := Real.one_le_rpow one_le_two (by positivity)
      have hZE : 1 ≤ Z * L x ^ E :=
        one_le_mul_of_one_le_of_one_le hZ (one_le_pow₀ hL)
      have hRf : (R x : ℝ) ≤ Z * L x ^ E + Z * L x ^ E := by
        have h := (Nat.ceil_lt_add_one (show 0 ≤ Z * L x ^ e by positivity)).le
        exact h.trans (add_le_add
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (le_max_left e f))
            (zero_le_one.trans hZ)) hZE)
      have hf' : L x ^ f ≤ Z * L x ^ E :=
        (pow_le_pow_right₀ hL (le_max_right e f)).trans
          (le_mul_of_one_le_left (by positivity) hZ)
      have hrate : Y * Z ≤ (2 : ℝ) ^ (((3 + A : ℕ) : ℝ) * X ^ q) := by
        change 2 ^ (3 * X ^ (1 - (d : ℝ)⁻¹)) * 2 ^ (A * X ^ p) ≤ _
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        apply Real.rpow_le_rpow_of_exponent_le one_le_two
        have h₁ := Real.rpow_le_rpow_of_exponent_le hX (le_max_left (1 - (d : ℝ)⁻¹) p)
        have h₂ := Real.rpow_le_rpow_of_exponent_le hX hpq
        push_cast
        nlinarith [mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg A)]
      calc
        _ ≤ 6 * Y * (c * L x ^ f + R x) := hT x
        _ ≤ 6 * Y * (c * (Z * L x ^ E) + (Z * L x ^ E + Z * L x ^ E)) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (mul_le_mul_of_nonneg_left hf' (Nat.cast_nonneg c)) hRf) (by positivity)
        _ = ((6 * (c + 2) : ℕ) : ℝ) * ((Y * Z) * L x ^ E) := by push_cast; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrate (by positivity))
          (Nat.cast_nonneg _)
    refine ⟨3 + A, E, (ComputableInTimeO.of_computableInO hverify hbound).mono
      (6 * (c + 2)) (fun _ => le_add_of_nonneg_right (Nat.cast_nonneg _)) (fun _ => by positivity)⟩
  have hμ : ComputableInPolyTime DeclaredCNF.numVars encDeclaredCNF encUnary :=
    encDeclaredCNF_numVars_polyTime ComputableInPolyTime.id'
  let Q := PromiseProblem.ofSet {a : DeclaredCNF |
    validDeclaredInput k a.numVars a.formula = true ∧ a.formula.Satisfiable}
  have herr (a : DeclaredCNF) (n : ℕ)
      (hv : validDeclaredInput k a.numVars a.formula = true)
      (hn : (2 : ℝ) ^ (A * (a.numVars + 1 : ℝ) ^ q) * ((encDeclaredCNF a).length + 1) ^ e ≤ n) :
      (acceptCount (fun x => verify x != decide (0 < x.1.formula.modelCount)) a n : ℝ) ≤
        (1 / 3 : ℝ) * 2 ^ n := by
    let N := a.numVars / countingPowerBudget d a.numVars + 1
    let ε := (1 / 3 : ℝ) / 2 ^ N
    have he := herror a n ε (by positivity) hv (by
      intro ψ
      dsimp only
      intro hnorm hw hs hv' hl hlen
      obtain ⟨hseed, hcount⟩ := hleaf a ψ hnorm ⟨hw, hs, hv', hl, hlen⟩
      refine ⟨Nat.cast_le.mp (hseed.trans ?_), hcount⟩
      have hx : 1 ≤ (a.numVars + 1 : ℝ) := le_add_of_nonneg_left (Nat.cast_nonneg _)
      exact (two_rpow_mul_pow_le_two_rpow_mul_pow
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx hpq)
          (Nat.cast_nonneg A)) le_rfl).trans hn)
    have hvars : a.formula.numVars ≤ a.numVars := by
      simpa only [CNF.numVars, Finset.card_range] using
        Finset.card_le_card (validDeclaredInput_eq_true_iff.mp hv).2
    have hle : a.formula.numVars / countingPowerBudget d a.numVars + 1 ≤ N :=
      Nat.succ_le_succ (Nat.div_le_div_right hvars)
    refine (he.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hle)
      (by positivity))).trans_eq ?_
    change (2 : ℝ) ^ N * ((1 / 3 / 2 ^ N) * 2 ^ n) = _
    field_simp
  obtain ⟨q', _, hq'₀, hq'₁, h⟩ := SolvesWithErrorInPowerExpTime.of_seededVerifier
    (Q := Q) (E := ErrorModel.bounded) hμ hq₁ hverify' A e (by
      intro a ha n hn
      have ha' : validDeclaredInput k a.numVars a.formula = true ∧ a.formula.Satisfiable := ha
      have htruth : decide (0 < a.formula.modelCount) = true :=
        decide_eq_true (CNF.modelCount_pos_iff.mpr ha'.2)
      have he := herr a n ha'.1 hn
      rw [acceptCount_congr (W := fun x => !verify x) (fun w => by
        simpa only [Bool.bne_true] using congrArg (fun b => verify (a, w) != b) htruth) n] at he
      exact he)
    (by
      intro a ha n hn
      cases hv : validDeclaredInput k a.numVars a.formula with
      | false =>
        rw [acceptCount_eq_zero_iff.mpr fun w => hreject (a, List.ofFn w) hv, Nat.cast_zero]
        exact mul_nonneg ErrorModel.bounded.noErr_nonneg (by positivity)
      | true =>
        have htruth : decide (0 < a.formula.modelCount) = false :=
          decide_eq_false fun hpos => ha ⟨hv, CNF.modelCount_pos_iff.mp hpos⟩
        have he := herr a n hv hn
        rw [acceptCount_congr (W := verify) (fun w => by
          simpa only [Bool.bne_false] using congrArg (fun b => verify (a, w) != b) htruth) n] at he
        exact he)
  exact ⟨q', hq'₀, hq'₁, h⟩

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

private theorem sparseLeaf_size_le {ψ : CNF ℕ} {declared A : ℕ} {b : ℝ}
    (hb : 1 ≤ b) (hsupport : ψ.vars.toFinset ⊆ Finset.range declared)
    (hclauses : (ψ.length : ℝ) ≤ A * (declared + 1 : ℝ) ^ b) :
    (ψ.numVars + ψ.length + 1 : ℝ) ≤ (A + 1 : ℝ) * (declared + 1 : ℝ) ^ b := by
  have hvars : ψ.numVars ≤ declared := by
    simpa only [CNF.numVars, Finset.card_range] using Finset.card_le_card hsupport
  have hbase : (1 : ℝ) ≤ declared + 1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hn : (declared + 1 : ℝ) ≤ (declared + 1 : ℝ) ^ b := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hbase hb
  have hn' : (ψ.numVars + 1 : ℝ) ≤ (declared + 1 : ℝ) :=
    add_le_add_left (Nat.cast_le.mpr hvars) 1
  linarith [hn'.trans hn]

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
        have hsize : (ψ.numVars + ψ.length + 1 : ℝ) ≤ (A + 1 : ℝ) * (X x) ^ b :=
          sparseLeaf_size_le hb hsupport ((Nat.cast_le.mpr hclauses).trans (hA hd declared))
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

private theorem solvesWithErrorInPowerExpTime_declaredSat_of_size {k : ℕ} (hk : 2 ≤ k)
    {p : ℝ} (hp : 0 < p) (hp₁ : p < 1)
    (h : SolvesWithErrorInPowerExpTime (PromiseProblem.ofSet (KSAT k)) encCNF ErrorModel.bounded
      (fun φ => φ.numVars + φ.length) p) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ SolvesWithErrorInPowerExpTime
      (PromiseProblem.ofSet {a : DeclaredCNF |
        validDeclaredInput k a.numVars a.formula = true ∧ a.formula.Satisfiable})
      encDeclaredCNF ErrorModel.bounded DeclaredCNF.numVars q := by
  let μ (a : DeclaredCNF) := a.formula.numVars + a.formula.length
  let Q := PromiseProblem.ofSet {a : DeclaredCNF | a.formula ∈ KSAT k}
  have hformula : ComputableInPolyTime DeclaredCNF.formula encDeclaredCNF encCNF :=
    encDeclaredCNF_formula_polyTime ComputableInPolyTime.id'
  have hbase : SolvesWithErrorInPowerExpTime Q encDeclaredCNF ErrorModel.bounded μ p := by
    have hsize (a : DeclaredCNF) : (μ a + 1 : ℝ) ≤
        (↑(0 : ℕ) + 1 : ℝ) * (μ a + 1 : ℝ) ^ (1 : ℝ) := by
      simp only [Nat.cast_zero, zero_add, one_mul, Real.rpow_one, le_refl]
    simpa only [one_mul] using h.of_polyTime_promiseReduction (A := Q) hformula
      (fun _ ha => ha) (fun _ ha => ha) (K := 0) hsize zero_le_one hp.le
  have htarget : ComputableInPolyTime (fun a : DeclaredCNF => a.numVars + 1)
      encDeclaredCNF encUnary :=
    ComputableInPolyTime.unary_add' (encDeclaredCNF_numVars_polyTime ComputableInPolyTime.id')
      (ComputableInPolyTime.const 1)
  obtain ⟨width, V, ⟨Cw, ew, hw⟩, ⟨Cv, ev, hv⟩, hyes, hno⟩ :=
    hbase.exists_amplifiedVerifier htarget
  obtain ⟨Tw, cw, hw, htw⟩ := hw.exists_computableInO
  obtain ⟨Tv, cv, hv, htv⟩ := hv.exists_computableInO
  obtain ⟨cl, hlenWidth⟩ := hw.length_le_time
  obtain ⟨d, hd, hdensity⟩ := exists_budget_power_lt_one hp₁ k
  obtain ⟨J, hJ⟩ := exists_countingPowerBudget_clauseBound_le hk
  let b : ℝ := 1 + (2 * k : ℝ) / d
  let D : ℕ := ⌈((max Cw Cv : ℕ) : ℝ) * (J + 1 : ℝ) ^ p⌉₊
  let X (a : DeclaredCNF) : ℝ := (2 : ℝ) ^ (D * (a.numVars + 1 : ℝ) ^ (b * p))
  have hX (a : DeclaredCNF) : 1 ≤ X a := Real.one_le_rpow one_le_two (by positivity)
  have hb : 1 ≤ b := le_add_of_nonneg_right (by positivity)
  let encSeeded := encPair encDeclaredCNF encBits
  let L (x : DeclaredCNF × List Bool) := (encSeeded x).length
  let N (a : DeclaredCNF) :=
    nodeBound k (countingDepthCoeff k (countingThresholdBase k (countingPowerBudget d a.numVars)))
      a.formula
  let B (x : DeclaredCNF × List Bool) := 2 * N x.1 + 5 * L x + 3
  obtain ⟨K, e, hN⟩ := (polyBounded_nodeBound_powerBudget encBits hk d).exists_le
  have hB : PolyBounded L B := by
    have hnode : PolyBounded L (fun x => N x.1) := by
      refine ((PolyBounded.const K).mul
        ((((PolyBounded.const 2).mul (PolyBounded.self (size := L))).add (.const 1)).pow e)).mono
        (fun x => ?_)
      refine (hN (x.2, x.1.numVars, x.1.formula)).trans (Nat.mul_le_mul_left K
        (Nat.pow_le_pow_left (Nat.add_le_add_right ?_ 1) e))
      have he : encDeclaredCNF x.1 = encPair encUnary encCNF (x.1.numVars, x.1.formula) := rfl
      simp only [L, encSeeded, he, length_encPair, encBits_apply]
      omega
    exact (((PolyBounded.const 2).mul hnode).add ((PolyBounded.const 5).mul .self)).add (.const 3)
  let E := max ew ev
  let P (x : DeclaredCNF × List Bool) := 20 * B x + (cw + cv) * (B x + 1) ^ E + (cw + cv) + 1
  have hP : PolyBounded L P := (((((PolyBounded.const 20).mul hB).add
    ((PolyBounded.const (cw + cv)).mul ((hB.add (.const 1)).pow E))).add (.const (cw + cv))).add
      (.const 1))
  obtain ⟨M, f, hM⟩ := ((PolyBounded.const (2 * cl + 1)).mul hP).exists_le
  let A := D + M * 2 ^ f
  have habsorb (a : DeclaredCNF) : X a * (M * 2 ^ f : ℕ) ≤
      (2 : ℝ) ^ (A * (a.numVars + 1 : ℝ) ^ (b * p)) := by
    have hpow : (1 : ℝ) ≤ (a.numVars + 1 : ℝ) ^ (b * p) :=
      Real.one_le_rpow (le_add_of_nonneg_left (Nat.cast_nonneg _))
        (mul_nonneg (zero_le_one.trans hb) hp.le)
    calc
      _ ≤ X a * (2 : ℝ) ^ (M * 2 ^ f : ℕ) := by
        apply mul_le_mul_of_nonneg_left _ (by dsimp only [X]; positivity)
        exact_mod_cast (Nat.lt_two_pow_self (n := M * 2 ^ f)).le
      _ ≤ _ := by
        rw [← Real.rpow_natCast, show X a = 2 ^ (D * (a.numVars + 1 : ℝ) ^ (b * p)) from rfl,
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        apply Real.rpow_le_rpow_of_exponent_le one_le_two
        dsimp only [A]
        push_cast
        nlinarith [mul_le_mul_of_nonneg_left hpow
          (show 0 ≤ (M : ℝ) * 2 ^ f by positivity)]
  have hcharge (a : DeclaredCNF) (ψ : CNF ℕ) (seed : List Bool)
      (hsupport : ψ.vars.toFinset ⊆ Finset.range a.numVars)
      (hclauses : ψ.length ≤ occBound k
        (countingThresholdBase k (countingPowerBudget d a.numVars)) * a.numVars + 1)
      (hlen : (encCNF ψ).length ≤ N a) :
      let leaf : DeclaredCNF := ⟨a.numVars, ψ⟩
      ((20 * (encSeeded (leaf, seed)).length + Tw leaf +
        Tv (leaf, seed.take (width leaf)) : ℕ) : ℝ) ≤ X a * P (a, seed) := by
    intro leaf
    have hsize : (μ leaf + 1 : ℝ) ≤ (J + 1 : ℝ) * (a.numVars + 1 : ℝ) ^ b := by
      simp only [μ, leaf, Nat.cast_add]
      exact sparseLeaf_size_le hb hsupport ((Nat.cast_le.mpr hclauses).trans (hJ hd a.numVars))
    have hrate (C : ℕ) (hC : C ≤ max Cw Cv) :
        (2 : ℝ) ^ (C * (μ leaf + 1 : ℝ) ^ p) ≤ X a := by
      refine (two_rpow_mul_rpow_le_of_le_mul_rpow (C := C)
        (by positivity) (by positivity) (by positivity) hsize hp.le).trans ?_
      apply Real.rpow_le_rpow_of_exponent_le one_le_two
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hC) (by positivity)).trans (Nat.le_ceil _)
    have hlenSeed : (encSeeded (leaf, seed)).length ≤ B (a, seed) := by
      have hroot : encDeclaredCNF a = encPair encUnary encCNF (a.numVars, a.formula) := rfl
      have hleaf : encDeclaredCNF leaf = encPair encUnary encCNF (a.numVars, ψ) := rfl
      simp only [B, L, encSeeded, hroot, hleaf, length_encPair, encBits_apply,
        encUnary_apply, List.length_replicate]
      omega
    have hlenLeaf := (length_le_encPair_left encDeclaredCNF encBits (leaf, seed)).trans hlenSeed
    have hlenQuery : (encSeeded (leaf, seed.take (width leaf))).length ≤ B (a, seed) := by
      refine le_trans ?_ hlenSeed
      simp only [encSeeded, length_encPair, encBits_apply]
      exact Nat.add_le_add_left (List.length_take_le' ..) _
    have hpoly (l j : ℕ) (hl : l ≤ B (a, seed)) (hj : j ≤ E) :
        (l + 1 : ℝ) ^ j ≤ (B (a, seed) + 1 : ℝ) ^ E :=
      (pow_le_pow_left₀ (by positivity) (by exact_mod_cast (Nat.add_le_add_right hl 1)) _).trans
        (pow_le_pow_right₀ (le_add_of_nonneg_left (Nat.cast_nonneg _)) hj)
    have hwidth' : (Tw leaf : ℝ) ≤ cw * (X a * (B (a, seed) + 1 : ℝ) ^ E) + cw :=
      (htw leaf).trans (add_le_add_left (mul_le_mul_of_nonneg_left
        (mul_le_mul (hrate Cw (le_max_left _ _)) (hpoly _ _ hlenLeaf (le_max_left _ _))
          (by positivity) (zero_le_one.trans (hX a))) (Nat.cast_nonneg cw)) _)
    have hverify' : (Tv (leaf, seed.take (width leaf)) : ℝ) ≤
        cv * (X a * (B (a, seed) + 1 : ℝ) ^ E) + cv :=
      (htv (leaf, seed.take (width leaf))).trans (add_le_add_left (mul_le_mul_of_nonneg_left
        (mul_le_mul (hrate Cv (le_max_right _ _)) (hpoly _ _ hlenQuery (le_max_right _ _))
          (by positivity) (zero_le_one.trans (hX a))) (Nat.cast_nonneg cv)) _)
    have hseedReal : ((encSeeded (leaf, seed)).length : ℝ) ≤ B (a, seed) :=
      Nat.cast_le.mpr hlenSeed
    dsimp only [P]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right (hX a)
      (show 0 ≤ 20 * (B (a, seed) : ℝ) + cw + cv + 1 by positivity)]
  have hmajor (a : DeclaredCNF) (seed : List Bool) :
      ((2 * cl + 1) * P (a, seed) : ℝ) ≤ M * (L (a, seed) + 1 : ℝ) ^ f := by
    exact_mod_cast hM (a, seed)
  have hframe (a : DeclaredCNF) : (L (a, []) : ℝ) + 1 =
      2 * ((encDeclaredCNF a).length + 1 : ℝ) := by
    simp only [L, encSeeded, length_encPair, encBits_apply, List.length_nil, Nat.add_zero,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring
  apply solvesWithErrorInPowerExpTime_of_powerBudgetLeaves hk hd hw hv hdensity A f
  · intro a ψ seed ha
    have h := hcharge a ψ seed ha.2.2.1 ha.2.2.2.1 ha.2.2.2.2
    have hP' : (P (a, seed) : ℝ) ≤ M * (L (a, seed) + 1 : ℝ) ^ f := by
      exact (le_mul_of_one_le_left (Nat.cast_nonneg _)
        (le_add_of_nonneg_left (by positivity) : (1 : ℝ) ≤ 2 * cl + 1)).trans (hmajor a seed)
    have hM' : (M : ℝ) ≤ (M * 2 ^ f : ℕ) := by
      exact_mod_cast Nat.le_mul_of_pos_right _ (Nat.two_pow_pos f)
    have htotal := h.trans (mul_le_mul_of_nonneg_left hP' (zero_le_one.trans (hX a)))
    rw [← mul_assoc] at htotal
    have hcomp := (mul_le_mul_of_nonneg_left hM' (zero_le_one.trans (hX a))).trans (habsorb a)
    exact ⟨htotal.trans (mul_le_mul_of_nonneg_right hcomp (by positivity)),
      htotal.trans (mul_le_mul_of_nonneg_right hcomp (by positivity))⟩
  · intro a ψ _ ha
    let leaf : DeclaredCNF := ⟨a.numVars, ψ⟩
    refine ⟨?_, ?_⟩
    · have hwork := hcharge a ψ [] ha.2.2.1 ha.2.2.2.1 ha.2.2.2.2
      have ht : (Tw leaf : ℝ) ≤ X a * P (a, []) := by
        dsimp only at hwork
        push_cast at hwork
        linarith [Nat.cast_nonneg (α := ℝ) (Tv (leaf, [].take (width leaf))),
          Nat.cast_nonneg (α := ℝ) ((encSeeded (leaf, [])).length)]
      have hP₁ : 1 ≤ P (a, []) := by dsimp only [P]; omega
      have hU : 1 ≤ X a * P (a, []) := one_le_mul_of_one_le_of_one_le (hX a) (by exact_mod_cast hP₁)
      have hwidth' : (width leaf : ℝ) ≤ cl * ((Tw leaf : ℝ) + 1) := by
        have hf' := hlenWidth leaf
        rw [encUnary_apply, List.length_replicate] at hf'
        exact_mod_cast hf'
      have hW : (width leaf : ℝ) ≤ X a * ((2 * (cl : ℝ) + 1) * P (a, [])) := by
        have h := mul_le_mul_of_nonneg_left (show (Tw leaf : ℝ) + 1 ≤ 2 * (X a * P (a, [])) by
          linarith) (Nat.cast_nonneg cl)
        linarith [hwidth'.trans h]
      calc
        _ ≤ X a * (M * (L (a, []) + 1 : ℝ) ^ f) :=
          hW.trans (mul_le_mul_of_nonneg_left (hmajor a []) (zero_le_one.trans (hX a)))
        _ = (X a * (M * 2 ^ f : ℕ)) * ((encDeclaredCNF a).length + 1 : ℝ) ^ f := by
          rw [hframe, mul_pow]
          push_cast
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (habsorb a) (by positivity)
    · have herr : (acceptCount (fun x => V x != decide (0 < x.1.formula.modelCount))
          leaf (width leaf) : ℝ) ≤ ((1 / 3 : ℝ) / 2 ^ (a.numVars + 1)) * 2 ^ width leaf := by
        by_cases ht : 0 < ψ.modelCount
        · have htruth : decide (0 < leaf.formula.modelCount) = true := decide_eq_true ht
          rw [acceptCount_congr (W := fun x => !V x) (fun w => by
            simpa only [Bool.bne_true] using congrArg (fun z => V (leaf, w) != z) htruth) _]
          exact hyes leaf ⟨ha.1, CNF.modelCount_pos_iff.mp ht⟩
        · have htruth : decide (0 < leaf.formula.modelCount) = false := decide_eq_false ht
          rw [acceptCount_congr (W := V) (fun w => by
            simpa only [Bool.bne_false] using congrArg (fun z => V (leaf, w) != z) htruth) _]
          exact hno leaf (fun hyes => ht (CNF.modelCount_pos_iff.mpr hyes.2))
      have hpow : (2 : ℝ) ^ (a.numVars / countingPowerBudget d a.numVars + 1) ≤
          2 ^ (a.numVars + 1) :=
        pow_le_pow_right₀ one_le_two (Nat.succ_le_succ (Nat.div_le_self ..))
      exact herr.trans (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow) (by positivity))

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
length. -/
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


/-- The randomized size-to-variable decision transfer in
[MITHardnessGroup2026SH, v2, §7, Theorem 7.1(a)] for fixed widths `k ≥ 2`.
Dense relabeling preserves satisfiability and width. On the sparse leaves, amplification uses
a number of repetitions linear in the declared variable count, which preserves the power
saving. Every leaf reads a prefix of a single shared seed, and a union bound controls the
total error. The time bound charges the original encoded length. -/
theorem SolvesWithErrorInPowerExpTime.KSAT_numVars_of_size {k : ℕ} (hk : 2 ≤ k)
    {p : ℝ} (hp : 0 < p) (hp₁ : p < 1)
    (h : SolvesWithErrorInPowerExpTime (PromiseProblem.ofSet (KSAT k)) encCNF ErrorModel.bounded
      (fun φ => φ.numVars + φ.length) p) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ SolvesWithErrorInPowerExpTime
      (PromiseProblem.ofSet (KSAT k)) encCNF ErrorModel.bounded CNF.numVars q := by
  obtain ⟨q, hq, hq₁, hsolver⟩ := CountingSparsify.solvesWithErrorInPowerExpTime_declaredSat_of_size
    hk hp hp₁ h
  let prepare (φ : CNF ℕ) : DeclaredCNF := ⟨φ.numVars, φ.denseRelabel⟩
  have hprepare : ComputableInPolyTime prepare encCNF encDeclaredCNF :=
    encDeclaredCNF_mk_polyTime SAT.computableInPolyTime_numVars
      SAT.computableInPolyTime_denseRelabel
  have hmem (φ : CNF ℕ) : φ ∈ KSAT k ↔ CNF.validDeclaredInput k (prepare φ).numVars
      (prepare φ).formula = true ∧ (prepare φ).formula.Satisfiable := by
    change ((∀ c ∈ φ, c.length ≤ k) ∧ φ.Satisfiable) ↔
      (CNF.validDeclaredInput k φ.numVars φ.denseRelabel = true ∧ φ.denseRelabel.Satisfiable)
    rw [valid_dense_iff_width, CNF.satisfiable_denseRelabel]
  refine ⟨q, hq, hq₁, ?_⟩
  simpa only [one_mul] using hsolver.of_polyTime_promiseReduction
    (A := PromiseProblem.ofSet (KSAT k)) (μ := CNF.numVars) hprepare
    (fun φ hφ => (hmem φ).mp hφ) (fun φ hφ hmem' => hφ ((hmem φ).mpr hmem'))
    (K := 0) (b := 1) (fun _ => by simp [prepare]) zero_le_one hq.le

end Cslib.Complexity
