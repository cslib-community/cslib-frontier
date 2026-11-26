/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

public import CslibFrontier.Computability.Complexity.FineGrained.CountingPowerSearch
import CslibFrontier.Computability.Complexity.FineGrained.CountingNativeModelCount
import CslibFrontier.Computability.Complexity.FineGrained.SharpSatisfiabilityHypothesis
import CslibFrontier.Computability.Complexity.FineGrained.SparseCountingScale
import CslibFrontier.Tactic.EncLen

/-! Exercise the power-budget search on a native counter with a superpolynomial allowance
and use the size-to-variable transfer for a counting lower bound. -/

section

open Cslib Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

-- The decision hypothesis implies a square-root exponent lower bound for #3SAT in variables.
example (h : SH) :
    ¬ ComputableInPowerExpTime SharpThreeSAT encCNF encNat CNF.numVars (1 / 2) :=
  (SharpSH_iff_WeakSharpETH.mp h.sharpSH) _ (by norm_num) (by norm_num)

end

public section

namespace CslibFrontierTests.CountingPowerSearch

open Cslib Cslib.Logic.PL Cslib.Logic.PL.ClauseSet.Sparsification
open Cslib.Complexity Cslib.Complexity.CountingSparsify
open Cslib.Complexity.SubexponentialSAT (interpolationScale)
open Turing.MultiTapeTM

private abbrev Input := Unit × ℕ × CNF ℕ
private abbrev encInput := encPair encUnit (encPair encUnary encCNF)
private abbrev encLeaf := encPair (encPair encUnit encUnary) encCNF
private def inputSize (x : Input) : ℕ := (encInput x).length

private theorem not_polyBounded_of_self_power {Q : Input → ℕ}
    (hpower : ∀ x, (inputSize x + 1) ^ (inputSize x + 1) ≤ Q x) :
    ¬ PolyBounded inputSize Q := by
  intro hQ
  obtain ⟨c, e, hce⟩ := hQ.exists_le
  let x : Input := ((), c + e, [])
  have hn : c + e ≤ inputSize x := by enc_len [inputSize, encInput, x]
  have hc : c < inputSize x + 1 := by omega
  have he : e + 1 ≤ inputSize x + 1 := by omega
  have hpos : 0 < (inputSize x + 1) ^ e := by positivity
  have hle := (Nat.pow_le_pow_right (by omega : 0 < inputSize x + 1) he).trans
    ((hpower x).trans (hce x))
  rw [pow_succ, Nat.mul_comm ((inputSize x + 1) ^ e)] at hle
  exact (Nat.not_le_of_lt (Nat.mul_lt_mul_of_pos_right hc hpos)) hle

private def nodeSize : Input → ℕ := fun (_, declared, formula) =>
  nodeBound 2 (countingDepthCoeff 2 (countingThresholdBase 2 (countingPowerBudget 2 declared)))
    formula

private def leafSize (x : Input) : ℕ :=
  2 * ((encPair encUnit encUnary) (x.1, x.2.1)).length + 1 + nodeSize x

private noncomputable def expAllowance (A n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sup fun m => ⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale m)⌉₊

/-- A native width-two counter with a padded, superpolynomial workspace allowance yields exact
counts on the empty CNF with zero or three declared variables and satisfies the time envelope
when rejecting an out-of-range variable. -/
theorem powerBudget_counts_with_superpolynomial_allowance :
    ∃ (Q count T S : Unit × ℕ × CNF ℕ → ℕ) (c e r : ℕ),
      ¬ PolyBounded (fun x => (encPair encUnit (encPair encUnary encCNF) x).length) Q ∧
      ComputableInO count (encPair encUnit (encPair encUnary encCNF)) encNat T S ∧
      count ((), 0, []) = 1 ∧ count ((), 3, []) = 8 ∧
      let declared : ℕ := 0
      let d : ℕ := 2
      let invalid : Unit × ℕ × CNF ℕ := ((), declared, [[(0, true)]])
      let L := (encPair encUnit (encPair encUnary encCNF) invalid).length
      count invalid = 0 ∧
      (T invalid : ℝ) ≤ 6 * 2 ^ (3 * (declared + 1 : ℝ) ^ (1 - (d : ℝ)⁻¹)) *
        (c * ((L : ℝ) + 1) ^ e + r) := by
  obtain ⟨g, A, e, b, hg, hcounter⟩ := CountingNativeEndpoint.exists_modelCounter 2
  have hproj : ComputableInPolyTime
      (Prod.snd : (Unit × ℕ) × CNF ℕ → CNF ℕ) encLeaf encCNF :=
    ComputableInPolyTime.snd _ _
  obtain ⟨a, _, ha⟩ := hproj.exists_degree
  let R (x : Input) := (leafSize x + 1) ^ a + expAllowance A x.2.1 * (nodeSize x + 1) ^ e
  let Q (x : Input) := (leafSize x + 1) ^ a + (nodeSize x + 1) ^ b +
    (inputSize x + 1) ^ (inputSize x + 1)
  have hQ : ¬ PolyBounded inputSize Q :=
    not_polyBounded_of_self_power fun x => Nat.le_add_left _ _
  have hresult := exists_computableInO_searchDeclared_powerBudget encUnit (k := 2) (d := 2)
    (by decide) (by decide) (R := R) (Q := Q) (hcounter.comp ha.inO)
    (fun _ ψ hw _ _ _ => hg ψ hw)
  obtain ⟨count, T, S, c, e, hc, _, hspec, hT⟩ := hresult (by
    intro x ψ _ _ hsub _ hlen
    have hlen' : (encLeaf ((x.1, x.2.1), ψ)).length ≤ leafSize x := by
      rw [leafSize, length_encPair]
      exact Nat.add_le_add_left hlen _
    have hvars : ψ.numVars ≤ x.2.1 := by
      simpa only [CNF.numVars, Finset.card_range] using Finset.card_le_card hsub
    have htime : ⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale ψ.numVars)⌉₊ ≤
        expAllowance A x.2.1 :=
      Finset.le_sup (f := fun m => ⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale m)⌉₊)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hvars))
    refine ⟨?_, le_trans ?_ (Nat.le_add_right _ _)⟩
    · exact Nat.add_le_add (Nat.pow_le_pow_left (Nat.succ_le_succ hlen') a)
        (Nat.mul_le_mul htime (Nat.pow_le_pow_left (Nat.succ_le_succ hlen) e))
    · exact Nat.add_le_add (Nat.pow_le_pow_left (Nat.succ_le_succ hlen') a)
        (Nat.pow_le_pow_left (Nat.succ_le_succ hlen) b))
  let invalid : Input := ((), 0, [[(0, true)]])
  refine ⟨Q, count, T, S, c, e, R invalid, hQ, hc, ?_⟩
  have hempty (n : ℕ) : count ((), n, []) = 2 ^ n := by
    have hvalid : CNF.validDeclaredInput 2 n [] = true :=
      CNF.validDeclaredInput_eq_true_iff.mpr ⟨by simp, by simp [CNF.vars]⟩
    simpa only [hvalid, ↓reduceIte, CNF.modelCountOn_nil, Finset.card_range] using hspec ((), n, [])
  have hinvalid : CNF.validDeclaredInput 2 0 [[(0, true)]] ≠ true := by decide
  refine ⟨hempty 0, hempty 3, ?_, ?_⟩
  · have hvalue := hspec invalid
    change count invalid =
      (if CNF.validDeclaredInput 2 0 [[(0, true)]] then
        CNF.modelCountOn [[(0, true)]] (Finset.range 0) else 0) at hvalue
    rwa [ite_eq_right hinvalid] at hvalue
  · exact hT ((), 0, [[(0, true)]])

-- A variable-count lower bound rules out a square-root size exponent for #3SAT.
example (hhard : ∀ q : ℝ, 0 < q → q < 1 →
    ¬ ComputableInPowerExpTime SharpThreeSAT encCNF encNat CNF.numVars q) :
    ¬ ComputableInPowerExpTime SharpThreeSAT encCNF encNat
      (fun φ => φ.numVars + φ.length) (1 / 2) := by
  intro h
  have hthree : ComputableInPowerExpTime (SharpKSAT 3) encCNF encNat
      (fun φ => φ.numVars + φ.length) (1 / 2) := by
    simpa only [SharpKSAT_three] using h
  obtain ⟨q, hq, hq1, hcount⟩ :=
    hthree.SharpKSAT_numVars_of_size (by decide) (by norm_num) (by norm_num)
  exact hhard q hq hq1 (by simpa only [SharpKSAT_three] using hcount)

end CslibFrontierTests.CountingPowerSearch
