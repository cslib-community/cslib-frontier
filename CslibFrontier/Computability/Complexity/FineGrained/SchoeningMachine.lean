/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.FineGrained
public import CslibFrontier.Computability.Complexity.FineGrained.Schoening
public import CslibFrontier.Computability.Complexity.Problems.ThreeSAT
public import CslibFrontier.Computability.Complexity.Classes.Time
public import CslibFrontier.Computability.Probabilistic.ExponentialIterate
public import CslibFrontier.Algorithms.WordRAM.Schoening.TrialCount
public import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpBounds
public import CslibFrontier.Languages.Probabilistic.UniformNat
import CslibFrontier.Logics.Propositional.CNF.ModelCount.DenseRelabel
import CslibFrontier.Computability.Probabilistic.Adaptive
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Languages.Probabilistic.UniformNat.LowerBound
import CslibFrontier.Languages.Probabilistic.UniformNat.Support
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.EventBind
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Schöning's `k`-SAT algorithm on fair-coin multitape Turing machines

`Cslib.Complexity.Schoening` proves the `((k - 1) / k) ^ (k - 3) (k / (2 (k - 1))) ^ n / (3 n + 1)`
single-trial success bound for Schöning's local search under exact uniform clause-literal sampling,
and `Cslib.Algorithms.WordRAM.Schoening` realizes the amplified algorithm on the randomized word
RAM [Schoening1999].

A strict fair-coin multitape Turing machine (`Turing.MultiTapePTM`) draws only fair bits rather than
exact uniform residues modulo non-power-of-two clause lengths `m ≤ k`. Reducing `w` fair bits modulo
`m` (`Cslib.ProbComp.sampleModNat w m`) hits every residue `i < m` at least `2 ^ w / m` times, so
each transition dominates `(1 - k / 2 ^ w)` times the ideal uniform transition. Choosing
`w = 2 n + k + 3` (`O(n)` fair bits per step, `O(n ^ 2)` per trial) keeps the `3 n`-step
multiplicative loss `(1 - k / 2 ^ w) ^ (3 n) ≥ 1 / 2`, preserving the `((2 (k - 1)) / k) ^ n`
exponential base without rejection loops.

Running `2 * schoeningTrials k φ.numVars c` independent restarts via the binary-counter compiler
`Cslib.Probability.IsPPTOn.exists_multiTapePTM_repeatAnyBool_binary` gives one finite-control
fair-coin `MultiTapePTM` on `encCNF` that:

* halts on every branch within `O(((2 (k - 1)) / k) ^ n * (L + 1) ^ E)` steps
  (`n = φ.numVars`, `L = (encCNF φ).length`),
* uses polynomial workspace `O((L + 1) ^ E)` (`machine.toNTM.RunsInSpace`),
* has zero false positives (`PMF.pure [false]` whenever `φ ∉ KSAT k`),
* accepts every `φ ∈ KSAT k` with probability at least `1 - exp (-c)` (and at least `2 / 3` at
  `c = 2`, yielding `DecidesWithBoundedErrorInTime encCNF (KSAT k) T`).

## Main definitions

* `Cslib.Complexity.Schoening.fairFlipStep`, `Cslib.Complexity.Schoening.fairWalk`,
  `Cslib.Complexity.Schoening.fairTrial`: fair-coin Schöning walk and trial via `sampleModNat`.
* `Cslib.Complexity.Schoening.schoeningTrialProg`: strict PPT single-trial program on `CNF ℕ`.

## Main results

* `Cslib.Complexity.Schoening.half_mul_succeedProb_trial_le_fairTrial`: `w = 2 |V| + k + 3` fair
  bits per step preserve at least half of the ideal single-trial success probability.
* `Cslib.Complexity.Schoening.isPPTOn_schoeningTrialProg`: the single-trial program on `encCNF` is
  strict PPT.
* `Cslib.Complexity.Schoening.computableInPolyTime_two_mul_schoeningTrials`: the binary trial count
  `2 * schoeningTrials k φ.numVars c` is computable in polynomial time into `encNat`.
* `Cslib.Complexity.Schoening.exists_multiTapePTM_KSAT`: sub-`2 ^ n` worst-case halting time,
  polynomial workspace, zero false positives, and `1 - exp (-c)` soundness on `KSAT k` (`k ≥ 3`).
* `Cslib.Complexity.Schoening.exists_decidesWithBoundedErrorInTime_KSAT`,
  `Cslib.Complexity.Schoening.exists_decidesWithBoundedErrorInTime_ThreeSAT`: bounded-error
  multitape `k`-SAT and `3`-SAT deciders (`((2 (k - 1)) / k) ^ n` and `(4 / 3) ^ n`).

## References

* [U. Schöning, *A probabilistic algorithm for k-SAT and constraint satisfaction
  problems*][Schoening1999]
-/

public section

namespace Cslib.Complexity.Schoening

open scoped ENNReal
open Cslib.BitString Cslib.Logic.PL Cslib.Probability Cslib.Algorithms.WordRAM.Schoening
open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapePTM

/-! ### Fair-coin domination of the ideal Schöning walk -/

section FairWalk

variable {V : Type*} [DecidableEq V]

/-- Flip the variable at index `r ← sampleModNat w c.length` of `c` (leaving `σ` unchanged if `c`
is empty). -/
noncomputable def fairFlipStep (w : ℕ) (c : Clause V) (σ : V → Bool) : PMF (V → Bool) :=
  if h : c.length = 0 then PMF.pure σ else
    (ProbComp.eval (ProbComp.sampleModNat w c.length)).map fun r =>
      flipOn {(c.get ⟨r % c.length, Nat.mod_lt r (Nat.pos_of_ne_zero h)⟩).1} σ

/-- `t` steps of the fair-coin Schöning walk with bit width `w` per step. -/
noncomputable def fairWalk (w : ℕ) (φ : CNF V) : ℕ → (V → Bool) → PMF (V → Bool)
  | 0, σ => PMF.pure σ
  | t + 1, σ =>
    match firstUnsat φ σ with
    | none => PMF.pure σ
    | some c => (fairFlipStep w c σ).bind (fairWalk w φ t)

/-- One trial of the fair-coin Schöning walk: uniform initial assignment followed by `3 |V|` steps
of `fairWalk w`. -/
noncomputable def fairTrial [Fintype V] (w : ℕ) (φ : CNF V) : PMF (V → Bool) :=
  (PMF.uniformOfFintype (V → Bool)).bind (fairWalk w φ (3 * Fintype.card V))

/-- Pointwise domination of one transition when `c.length ≤ k`. -/
theorem le_fairFlipStep_toReal {w k : ℕ} {c : Clause V} (hclen : c.length ≤ k)
    (σ τ : V → Bool) :
    (1 - (k : ℝ) / (2 : ℝ) ^ w) * (flipStep c σ τ).toReal ≤ (fairFlipStep w c σ τ).toReal := by
  classical
  have hα_le : 1 - (k : ℝ) / (2 : ℝ) ^ w ≤ 1 := sub_le_self _ (by positivity)
  by_cases hc0 : c.length = 0
  · simp only [flipStep, fairFlipStep, hc0, ↓reduceDIte]
    exact mul_le_of_le_one_left ENNReal.toReal_nonneg hα_le
  · have hm : 0 < c.length := Nat.pos_of_ne_zero hc0
    have : NeZero c.length := ⟨hc0⟩
    have hα_m : 1 - (k : ℝ) / (2 : ℝ) ^ w ≤ 1 - (c.length : ℝ) / (2 : ℝ) ^ w := by
      have : (c.length : ℝ) ≤ k := by exact_mod_cast hclen
      gcongr
    let g (i : Fin c.length) : V → Bool := flipOn {(c.get i).1} σ
    have hunif : (flipStep c σ τ).toReal =
        ∑ i : Fin c.length, if τ = g i then (c.length : ℝ)⁻¹ else 0 := by
      simp only [flipStep, hc0, ↓reduceDIte, Cslib.Probability.PMF.map_apply_toReal,
        PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv, ENNReal.toReal_natCast, g]
    have hfair_le :
        (∑ i : Fin c.length, if τ = g i then
          (ProbComp.eval (ProbComp.sampleModNat w c.length) i.val).toReal else 0) ≤
        (fairFlipStep w c σ τ).toReal := by
      calc (∑ i : Fin c.length, if τ = g i then
              (ProbComp.eval (ProbComp.sampleModNat w c.length) i.val).toReal else 0)
          = (∑ i : Fin c.length, (if τ = g i then
              ProbComp.eval (ProbComp.sampleModNat w c.length) i.val else 0).toReal) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              split_ifs <;> simp
        _ = (∑ i : Fin c.length, if τ = g i then
              ProbComp.eval (ProbComp.sampleModNat w c.length) i.val else 0).toReal :=
              (ENNReal.toReal_sum fun _ _ => by split_ifs <;> simp [PMF.apply_ne_top]).symm
        _ ≤ (fairFlipStep w c σ τ).toReal := by
              refine ENNReal.toReal_mono (PMF.apply_ne_top _ _) ?_
              simp only [fairFlipStep, hc0, ↓reduceDIte, PMF.map_apply]
              calc (∑ i : Fin c.length, if τ = g i then
                      ProbComp.eval (ProbComp.sampleModNat w c.length) i.val else 0)
                  = ∑ r ∈ Finset.range c.length, if τ = g ⟨r % c.length, Nat.mod_lt r hm⟩ then
                      ProbComp.eval (ProbComp.sampleModNat w c.length) r else 0 := by
                      rw [← Fin.sum_univ_eq_sum_range]
                      refine Finset.sum_congr rfl fun i _ => ?_
                      have hmod : (⟨i.val % c.length, Nat.mod_lt i.val hm⟩ : Fin c.length) = i :=
                        Fin.ext (Nat.mod_eq_of_lt i.isLt)
                      rw [hmod]
                _ ≤ _ := sum_le_tsum (Finset.range c.length)
    rw [hunif, Finset.mul_sum]
    refine (Finset.sum_le_sum fun i _ => ?_).trans hfair_le
    split_ifs
    · exact (mul_le_mul_of_nonneg_right hα_m (by positivity)).trans
        (ProbComp.le_eval_sampleModNat_toReal i.isLt)
    · simp

/-- Pointwise domination across `t` steps of the walk. -/
theorem le_fairWalk_toReal [Finite V] {w k : ℕ} {φ : CNF V} (hlen : ∀ c ∈ φ, c.length ≤ k)
    (hkw : (k : ℝ) ≤ (2 : ℝ) ^ w) (t : ℕ) (σ τ : V → Bool) :
    (1 - (k : ℝ) / (2 : ℝ) ^ w) ^ t * (walk φ t σ τ).toReal ≤ (fairWalk w φ t σ τ).toReal := by
  cases nonempty_fintype V
  have h2w : (0 : ℝ) < (2 : ℝ) ^ w := by positivity
  have hα0 : 0 ≤ 1 - (k : ℝ) / (2 : ℝ) ^ w := sub_nonneg.mpr ((div_le_one h2w).mpr hkw)
  have hα1 : 1 - (k : ℝ) / (2 : ℝ) ^ w ≤ 1 := sub_le_self _ (by positivity)
  induction t generalizing σ with
  | zero => simp only [pow_zero, one_mul, walk, fairWalk, le_refl]
  | succ t ih =>
    simp only [walk, fairWalk]
    cases hfind : firstUnsat φ σ with
    | none => exact mul_le_of_le_one_left ENNReal.toReal_nonneg (pow_le_one₀ hα0 hα1)
    | some c =>
      rw [Cslib.Probability.PMF.bind_apply_toReal, Cslib.Probability.PMF.bind_apply_toReal,
        pow_succ, Finset.mul_sum]
      refine Finset.sum_le_sum fun σ' _ => ?_
      have h1 := le_fairFlipStep_toReal (w := w) (hlen c (List.mem_of_find?_eq_some hfind)) σ σ'
      have h2 := ih σ'
      calc ((1 - (k : ℝ) / (2 : ℝ) ^ w) ^ t * (1 - (k : ℝ) / (2 : ℝ) ^ w)) *
            ((flipStep c σ σ').toReal * (walk φ t σ' τ).toReal)
          = ((1 - (k : ℝ) / (2 : ℝ) ^ w) * (flipStep c σ σ').toReal) *
              ((1 - (k : ℝ) / (2 : ℝ) ^ w) ^ t * (walk φ t σ' τ).toReal) := by ring
        _ ≤ _ := mul_le_mul h1 h2 (mul_nonneg (pow_nonneg hα0 t) ENNReal.toReal_nonneg)
            ENNReal.toReal_nonneg

private theorem half_le_bernoulli_factor (n k : ℕ) :
    (1 / 2 : ℝ) ≤ (1 - (k : ℝ) / (2 : ℝ) ^ (2 * n + k + 3)) ^ (3 * n) := by
  set δ : ℝ := (k : ℝ) / (2 : ℝ) ^ (2 * n + k + 3)
  have h3n : 3 * n < 2 ^ (2 * n + 2) := by
    have hpow : 4 * 2 ^ n ≤ 2 ^ (2 * n + 2) := by
      calc 4 * 2 ^ n = 2 ^ (n + 2) := by ring
        _ ≤ 2 ^ (2 * n + 2) := Nat.pow_le_pow_right (by decide) (by omega)
    have := Nat.lt_two_pow_self (n := n)
    omega
  have hprod_le : (3 * n) * k ≤ 2 ^ (2 * n + k + 2) := by
    calc 3 * n * k ≤ 2 ^ (2 * n + 2) * 2 ^ k := by gcongr; exact Nat.lt_two_pow_self.le
      _ = 2 ^ (2 * n + k + 2) := by rw [← Nat.pow_add]; ring_nf
  have hk_le : (k : ℝ) ≤ (2 : ℝ) ^ (2 * n + k + 3) := by
    exact_mod_cast (Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide) (by omega)))
  have hδ1 : δ ≤ 1 := (div_le_one (by positivity)).mpr hk_le
  have hprod_half : (3 * n : ℝ) * δ ≤ 1 / 2 := by
    have hR : (3 * n : ℝ) * k ≤ (2 : ℝ) ^ (2 * n + k + 2) := by exact_mod_cast hprod_le
    dsimp only [δ]
    rw [show (2 : ℝ) ^ (2 * n + k + 3) = 2 * (2 : ℝ) ^ (2 * n + k + 2) by ring, mul_div_assoc',
      div_le_iff₀ (by positivity)]
    linarith
  have hbern := one_add_mul_le_pow (a := -δ) (by linarith) (3 * n)
  push_cast at hbern
  linarith [show (1 - δ) ^ (3 * n) = (1 + -δ) ^ (3 * n) by ring]

/-- **Fair-coin Schöning trial domination.** Using `w = 2 |V| + k + 3` fair bits per step preserves
at least half of the ideal single-trial success probability. -/
theorem half_mul_succeedProb_trial_le_fairTrial [Fintype V] {k : ℕ} {φ : CNF V}
    (hlen : ∀ c ∈ φ, c.length ≤ k) :
    (1 / 2 : ℝ) * succeedProb φ (trial φ) ≤
      succeedProb φ (fairTrial (2 * Fintype.card V + k + 3) φ) := by
  set n := Fintype.card V
  set w := 2 * n + k + 3
  have hkw : (k : ℝ) ≤ (2 : ℝ) ^ w := by
    exact_mod_cast (Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide) (by omega)))
  have hwalk_succ (σ : V → Bool) :
      (1 - (k : ℝ) / (2 : ℝ) ^ w) ^ (3 * n) * succeedProb φ (walk φ (3 * n) σ) ≤
        succeedProb φ (fairWalk w φ (3 * n) σ) := by
    simp only [succeedProb, Cslib.Probability.PMF.toOuterMeasure_apply_toReal, Finset.mul_sum]
    refine Finset.sum_le_sum fun τ _ => ?_
    split_ifs
    · exact le_fairWalk_toReal hlen hkw (3 * n) σ τ
    · simp
  have htrial_dom :
      (1 - (k : ℝ) / (2 : ℝ) ^ w) ^ (3 * n) * succeedProb φ (trial φ) ≤
        succeedProb φ (fairTrial w φ) := by
    simp only [trial, fairTrial, succeedProb, Cslib.Probability.PMF.toOuterMeasure_bind_toReal,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun σ _ => ?_
    calc (1 - (k : ℝ) / (2 : ℝ) ^ w) ^ (3 * n) *
          ((PMF.uniformOfFintype (V → Bool) σ).toReal * _)
        = (PMF.uniformOfFintype (V → Bool) σ).toReal *
            ((1 - (k : ℝ) / (2 : ℝ) ^ w) ^ (3 * n) * succeedProb φ (walk φ (3 * n) σ)) := by
          simp only [succeedProb]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hwalk_succ σ) ENNReal.toReal_nonneg
  exact (mul_le_mul_of_nonneg_right (half_le_bernoulli_factor n k)
    (by rw [succeedProb]; exact ENNReal.toReal_nonneg)).trans htrial_dom

end FairWalk

/-! ### Strict PPT single-trial realization on `CNF ℕ` (`encCNF`) -/

section TrialProgram

/-- Boolean guard checking that every clause of `φ` is nonempty and has length at most `k`. -/
def guardKSAT (k : ℕ) (φ : CNF ℕ) : Bool :=
  φ.all fun c => !c.isEmpty && decide (c.length ≤ k)

/-- Read an assignment `ℕ → Bool` from a bit list by index (`false` out of bounds). -/
def bitsAssign (bits : List Bool) (v : ℕ) : Bool :=
  bits.getD v false

/-- Flip bit `v` of `bits`, preserving `bits.length`. -/
def flipBitAt (bits : List Bool) (v : ℕ) : List Bool :=
  (List.range bits.length).map fun i =>
    if i == v then !(bits.getD i false) else bits.getD i false

@[simp]
theorem length_flipBitAt (bits : List Bool) (v : ℕ) :
    (flipBitAt bits v).length = bits.length := by
  simp only [flipBitAt, List.length_map, List.length_range]

/-- First unsatisfied clause of `ψ` under `bitsAssign bits`, returning `[]` when none exists. -/
def firstUnsatClauseBits (ψ : CNF ℕ) (bits : List Bool) : Clause ℕ :=
  (ψ.filter fun c => !Clause.eval (bitsAssign bits) c).headD []

/-- One fair-coin walk step on a densely relabeled formula `ψ` with bit width `w`. -/
noncomputable def walkStepBits (ψ : CNF ℕ) (w : ℕ) (bits : List Bool) : ProbComp (List Bool) :=
  let c := firstUnsatClauseBits ψ bits
  if c.isEmpty then
    pure bits
  else do
    let r ← ProbComp.sampleModNat w c.length
    let idx := min c.length r
    let v := (c.getD idx (0, false)).1
    pure (flipBitAt bits v)

/-- Unchecked body of one Schöning trial on `φ : CNF ℕ`: densely relabel `φ`, sample `n = φ.numVars`
fair bits, run `3 n` steps of `walkStepBits` with width `2 n + k + 3`, and evaluate `ψ`. -/
noncomputable def schoeningBodyProg (k : ℕ) (φ : CNF ℕ) : ProbComp Bool := do
  let ψ := φ.denseRelabel
  let n := φ.numVars
  let w := 2 * n + k + 3
  let bits₀ ← BitString.sampleList n
  let bitsFinal ← OracleComp.iterate (3 * n) (walkStepBits ψ w) bits₀
  pure (CNF.eval (bitsAssign bitsFinal) ψ)

/-- **Certified single-trial Schöning program on `CNF ℕ`.** Rejects immediately with `false` if any
clause of `φ` is empty or longer than `k`; otherwise runs `schoeningBodyProg k φ`. -/
noncomputable def schoeningTrialProg (k : ℕ) (φ : CNF ℕ) : ProbComp Bool :=
  if guardKSAT k φ then schoeningBodyProg k φ else pure false

private theorem computableInPolyTime_guardKSAT (k : ℕ) :
    ComputableInPolyTime (guardKSAT k) encCNF encBool := by
  unfold guardKSAT
  fun_prop

private theorem computableInPolyTime_firstUnsatClauseBits :
    ComputableInPolyTime (fun p : CNF ℕ × List Bool => firstUnsatClauseBits p.1 p.2)
      (encPair (encCNFOver encUnary) encBits) (encClause encUnary) := by
  unfold firstUnsatClauseBits bitsAssign
  fun_prop

private theorem computableInPolyTime_flipBitAt :
    ComputableInPolyTime (fun p : List Bool × ℕ => flipBitAt p.1 p.2)
      (encPair encBits encUnary) encBits := by
  unfold flipBitAt
  exact ComputableInPolyTime.listToBits.comp (by fun_prop)

private theorem isPPTOn_walkStepBits :
    IsPPTOn (encPair (encPair (encCNFOver encUnary) encUnary) encBits) encBits
      (fun p : (CNF ℕ × ℕ) × List Bool => walkStepBits p.1.1 p.1.2 p.2) := by
  let InEnc := encPair (encPair (encCNFOver encUnary) encUnary) encBits
  have hc : ComputableInPolyTime
      (fun p : (CNF ℕ × ℕ) × List Bool => firstUnsatClauseBits p.1.1 p.2)
      InEnc (encClause encUnary) :=
    computableInPolyTime_firstUnsatClauseBits.comp
      (((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _)).prod
        (ComputableInPolyTime.snd _ _))
  have hempty : ComputableInPolyTime
      (fun p : (CNF ℕ × ℕ) × List Bool => (firstUnsatClauseBits p.1.1 p.2).isEmpty)
      InEnc encBool := (ComputableInPolyTime.listIsEmpty' (encPair encUnary encBool)).comp hc
  have hw : ComputableInPolyTime (fun p : (CNF ℕ × ℕ) × List Bool => p.1.2) InEnc encUnary := by
    fun_prop
  have hclen_unary : ComputableInPolyTime
      (fun p : (CNF ℕ × ℕ) × List Bool => (firstUnsatClauseBits p.1.1 p.2).length)
      InEnc encUnary := Clause.computableInPolyTime_length hc
  have hmod : IsPPTOn InEnc encNat
      (fun p : (CNF ℕ × ℕ) × List Bool =>
        ProbComp.sampleModNat p.1.2 (firstUnsatClauseBits p.1.1 p.2).length) :=
    isPPTOn_sampleModNat hw (ComputableInPolyTime.unary_to_binary.comp hclen_unary)
  have hpost : ComputableInPolyTime
      (fun q : ((CNF ℕ × ℕ) × List Bool) × ℕ =>
        let c := firstUnsatClauseBits q.1.1.1 q.1.2
        flipBitAt q.1.2 (c.getD (min c.length q.2) (0, false)).1)
      (encPair InEnc encNat) encBits := by
    have hv := (ComputableInPolyTime.fst encUnary encBool).comp
      (ComputableInPolyTime.listGetDWithInput (hc.comp (ComputableInPolyTime.fst _ _))
        (ComputableInPolyTime.binary_min_unary'
          (hclen_unary.comp (ComputableInPolyTime.fst _ _)) (ComputableInPolyTime.snd _ _))
        (0, false))
    exact computableInPolyTime_flipBitAt.comp
      (((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _)).prod hv)
  refine IsPPTOn.cond hempty (ComputableInPolyTime.snd _ _).isPPTOn ?_
  simpa only [bind_pure_comp] using hmod.map_with hpost

private theorem length_eq_of_mem_support_walkStepBits {ψ : CNF ℕ} {w : ℕ} {bits next : List Bool}
    (hnext : next ∈ (ProbComp.eval (walkStepBits ψ w bits)).support) :
    next.length = bits.length := by
  dsimp only [walkStepBits] at hnext
  split_ifs at hnext with h
  · simp only [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hnext
    rw [hnext]
  · simp only [ProbComp.eval_bind, PMF.mem_support_bind_iff, ProbComp.eval_pure,
      PMF.support_pure, Set.mem_singleton_iff] at hnext
    obtain ⟨_, _, rfl⟩ := hnext
    exact length_flipBitAt bits _

private theorem isPPTOn_iterateBitsOfStep {P : Type} (encP : P ↪ List Bool)
    {stepFn : P → List Bool → ProbComp (List Bool)}
    (hstepFn : IsPPTOn (encPair encP encBits) encBits (fun q => stepFn q.1 q.2))
    (hlen_eq : ∀ p bits next, next ∈ (ProbComp.eval (stepFn p bits)).support →
      next.length = bits.length) :
    IsPPTOn (encPair (encPair encP encUnary) encBits) encBits
      (fun x : (P × ℕ) × List Bool => OracleComp.iterate x.1.2 (stepFn x.1.1) x.2) := by
  let encIn := encPair (encPair encP encUnary) encBits
  have hparam : ComputableInPolyTime (fun q : ((P × ℕ) × List Bool) × List Bool => (q.1.1.1, q.2))
      (encPair encIn encBits) (encPair encP encBits) := by
    fun_prop
  exact (IsPPTOn.iterateWith_spec
    (input := encIn) (stateEncoding := encBits)
    (initial := Prod.snd) (count := fun x => x.1.2)
    (step := fun x bits => stepFn x.1.1 bits)
    (by fun_prop) (ComputableInPolyTime.snd _ _) (hstepFn.preprocess hparam)
    (fun x _ bits => bits.length = x.2.length) (fun _ => rfl)
    (fun x _ _ _ hlen _ hnext => (hlen_eq x.1.1 _ _ hnext).trans hlen)
    (size := fun x => (encIn x).length) PolyBounded.self
    (fun x _ bits _ hlen => by
      change bits.length ≤ (encIn x).length
      rw [hlen, length_encPair]; exact Nat.le_add_left _ _)).1

private theorem isPPTOn_walkLoopPair (k : ℕ) :
    IsPPTOn (encPair encCNF encBits) encBits
      (fun p : CNF ℕ × List Bool =>
        OracleComp.iterate (3 * p.1.numVars)
          (walkStepBits p.1.denseRelabel (2 * p.1.numVars + k + 3)) p.2) := by
  have hgen := isPPTOn_iterateBitsOfStep (encPair (encCNFOver encUnary) encUnary)
    (stepFn := fun pw : CNF ℕ × ℕ => walkStepBits pw.1 pw.2)
    isPPTOn_walkStepBits (fun _ _ _ hnext => length_eq_of_mem_support_walkStepBits hnext)
  have hn : ComputableInPolyTime (CNF.numVars (V := ℕ)) encCNF encUnary :=
    SAT.computableInPolyTime_numVars
  have hw : ComputableInPolyTime (fun φ : CNF ℕ => 2 * φ.numVars + k + 3) encCNF encUnary :=
    ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_mul' (.const 2) hn) (.const k))
      (.const 3)
  have hφ := ComputableInPolyTime.fst encCNF encBits
  exact hgen.preprocess
    ((((((CNF.computableInPolyTime_denseRelabel_unary encNat).comp hφ).prod (hw.comp hφ)).prod
      ((ComputableInPolyTime.unary_mul' (.const 3) hn).comp hφ))).prod
      (ComputableInPolyTime.snd encCNF encBits))

private theorem computableInPolyTime_evalDensePair :
    ComputableInPolyTime
      (fun q : CNF ℕ × List Bool => CNF.eval (bitsAssign q.2) q.1.denseRelabel)
      (encPair encCNF encBits) encBool :=
  CNF.computableInPolyTime_eval
    ((CNF.computableInPolyTime_denseRelabel_unary encNat).comp (ComputableInPolyTime.fst _ _))
    (ComputableInPolyTime.bitsGetDWithInput
      ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _))
      (ComputableInPolyTime.snd _ _) false)

private theorem isPPTOn_schoeningBodyProg (k : ℕ) :
    IsPPTOn encCNF encBool (schoeningBodyProg k) := by
  have hwalk : IsPPTOn encCNF encBits
      (fun φ : CNF ℕ => do
        let bits₀ ← BitString.sampleList φ.numVars
        OracleComp.iterate (3 * φ.numVars)
          (walkStepBits φ.denseRelabel (2 * φ.numVars + k + 3)) bits₀) :=
    (isPPTOn_sampleList.preprocess SAT.computableInPolyTime_numVars).bind_with
      (isPPTOn_walkLoopPair k)
  refine (hwalk.map_with (f := fun φ bits => CNF.eval (bitsAssign bits) φ.denseRelabel)
    computableInPolyTime_evalDensePair).congr fun φ => ?_
  dsimp only [schoeningBodyProg]
  rw [ProbComp.eval_map, ProbComp.eval_bind, ProbComp.eval_bind, PMF.map_bind]
  refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun bits₀ _ => ?_
  rw [PMF.map, ProbComp.eval_bind]
  refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun bitsF _ => ?_
  rw [Function.comp_apply, ProbComp.eval_pure]

/-- **Strict PPT certificate for one Schöning trial on `CNF ℕ` (`encCNF`).** -/
theorem isPPTOn_schoeningTrialProg (k : ℕ) :
    IsPPTOn encCNF encBool (schoeningTrialProg k) :=
  IsPPTOn.cond (computableInPolyTime_guardKSAT k) (isPPTOn_schoeningBodyProg k)
    (ComputableInPolyTime.const (encIn := encCNF) false).isPPTOn

/-! ### Connecting `schoeningTrialProg` to `fairTrial` on `CNF (Fin φ.numVars)` -/

private def toFinClause {n : ℕ} (c : Clause ℕ) (hc : ∀ l ∈ c, l.1 < n) : Clause (Fin n) :=
  c.attach.map fun ⟨l, hl⟩ => (⟨l.1, hc l hl⟩, l.2)

private def toFinCNF {n : ℕ} (ψ : CNF ℕ) (hvars : ∀ v ∈ ψ.vars, v < n) : CNF (Fin n) :=
  ψ.attach.map fun ⟨c, hc⟩ =>
    toFinClause c fun l hl => hvars l.1 (CNF.mem_vars.mpr ⟨c, hc, l.2, hl⟩)

private theorem length_toFinClause {n : ℕ} (c : Clause ℕ) (hc : ∀ l ∈ c, l.1 < n) :
    (toFinClause c hc).length = c.length := by
  simp only [toFinClause, List.length_map, List.length_attach]

private theorem getD_ofFn_eq {n : ℕ} (σ : Fin n → Bool) {v : ℕ} (hv : v < n) :
    (List.ofFn σ).getD v false = σ ⟨v, hv⟩ := by
  have hlen : v < (List.ofFn σ).length := by simpa only [List.length_ofFn] using hv
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, List.getElem_ofFn,
    Option.getD_some]

private theorem eval_toFinClause {n : ℕ} (c : Clause ℕ) (hc : ∀ l ∈ c, l.1 < n)
    (σ : Fin n → Bool) :
    Clause.eval σ (toFinClause c hc) = Clause.eval (bitsAssign (List.ofFn σ)) c := by
  apply Bool.eq_iff_iff.mpr
  simp only [Clause.eval_eq_true_iff, toFinClause, List.mem_map, List.mem_attach, true_and,
    Subtype.exists]
  constructor
  · rintro ⟨_, ⟨l, hl, rfl⟩, hev⟩
    refine ⟨l, hl, ?_⟩
    simpa only [Literal.eval, bitsAssign, getD_ofFn_eq σ (hc l hl)] using hev
  · rintro ⟨l, hl, hev⟩
    refine ⟨(⟨l.1, hc l hl⟩, l.2), ⟨l, hl, rfl⟩, ?_⟩
    simpa only [Literal.eval, bitsAssign, getD_ofFn_eq σ (hc l hl)] using hev

private theorem eval_toFinCNF {n : ℕ} (ψ : CNF ℕ) (hvars : ∀ v ∈ ψ.vars, v < n)
    (σ : Fin n → Bool) :
    CNF.eval σ (toFinCNF ψ hvars) = CNF.eval (bitsAssign (List.ofFn σ)) ψ := by
  apply Bool.eq_iff_iff.mpr
  simp only [CNF.eval_eq_true_iff, toFinCNF, List.mem_map, List.mem_attach, true_and,
    Subtype.exists]
  constructor
  · intro h c hc
    rw [← eval_toFinClause c (fun l hl => hvars l.1 (CNF.mem_vars.mpr ⟨c, hc, l.2, hl⟩)) σ]
    exact h _ ⟨c, hc, rfl⟩
  · rintro h _ ⟨c, hc, rfl⟩
    rw [eval_toFinClause]
    exact h c hc

private theorem satisfiable_toFinCNF {n : ℕ} (ψ : CNF ℕ) (hvars : ∀ v ∈ ψ.vars, v < n) :
    (toFinCNF ψ hvars).Satisfiable ↔ ψ.Satisfiable := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨bitsAssign (List.ofFn σ), by rwa [← eval_toFinCNF ψ hvars σ]⟩
  · rintro ⟨τ, hτ⟩
    refine ⟨fun i => τ i.val, ?_⟩
    rw [eval_toFinCNF]
    refine (CNF.eval_congr fun v hv => ?_).trans hτ
    simp only [bitsAssign, getD_ofFn_eq (fun i : Fin n => τ i.val) (hvars v hv)]

private theorem flipBitAt_ofFn {n : ℕ} (σ : Fin n → Bool) {v : ℕ} (hv : v < n) :
    flipBitAt (List.ofFn σ) v = List.ofFn (flipOn {⟨v, hv⟩} σ) := by
  refine List.ext_getElem (by simp only [length_flipBitAt, List.length_ofFn]) fun i h₁ h₂ => ?_
  have hi : i < n := by simpa only [List.length_ofFn] using h₂
  simp only [flipBitAt, List.length_ofFn, List.getElem_map, List.getElem_range, List.getElem_ofFn,
    getD_ofFn_eq σ hi, flipOn, Finset.mem_singleton, Fin.ext_iff]
  by_cases hiv : i = v
  · simp only [hiv, beq_self_eq_true, ↓reduceIte]
  · have hbeq : (i == v) = false := beq_false_of_ne hiv
    simp only [hbeq, Bool.false_eq_true, hiv, ↓reduceIte]

private theorem headD_filter_eq_nil_of_find?_eq_none {α : Type*} {l : List (List α)}
    {p : List α → Bool} (h : l.find? p = none) :
    (l.filter p).headD [] = [] := by
  rw [List.filter_eq_nil_iff.mpr fun x hx => by
    simpa only [Bool.not_eq_true] using List.find?_eq_none.mp h x hx]
  rfl

private theorem headD_filter_eq_of_find?_eq_some {α : Type*} {l : List (List α)}
    (hne : ∀ c ∈ l, c ≠ []) {p : List α → Bool} {c : List α} (h : l.find? p = some c) :
    (l.filter p).headD [] = c ∧ c ≠ [] := by
  induction l with
  | nil => simp at h
  | cons a as ih =>
    cases hpa : p a <;> simp only [List.find?_cons, hpa, Option.some.injEq] at h
    · rw [List.filter_cons_of_neg (by simp [hpa])]
      exact ih (fun x hx => hne x (List.mem_cons_of_mem a hx)) h
    · subst h; rw [List.filter_cons_of_pos hpa, List.headD_cons]
      exact ⟨rfl, hne a List.mem_cons_self⟩

private theorem find?_attach {α : Type*} (l : List α) (p : α → Bool) :
    (l.attach.find? fun x => p x.val).map Subtype.val = l.find? p := by
  have hid : l = l.attach.map Subtype.val := (List.attach_map_subtype_val l).symm
  conv_rhs => rw [hid, List.find?_map]
  rfl

private theorem eval_walkStepBits_ofFn {n : ℕ} (ψ : CNF ℕ) (hvars : ∀ v ∈ ψ.vars, v < n)
    (hne : ∀ c ∈ ψ, c ≠ []) (w : ℕ) (σ : Fin n → Bool) :
    ProbComp.eval (walkStepBits ψ w (List.ofFn σ)) =
      (match firstUnsat (toFinCNF ψ hvars) σ with
        | none => PMF.pure σ
        | some c => fairFlipStep w c σ).map List.ofFn := by
  let p (c : Clause ℕ) : Bool := !Clause.eval (bitsAssign (List.ofFn σ)) c
  have hfind_eq : firstUnsat (toFinCNF ψ hvars) σ =
      (ψ.attach.find? (fun x => p x.val)).map
        (fun x => toFinClause x.val fun l hl =>
          hvars l.1 (CNF.mem_vars.mpr ⟨x.val, x.property, l.2, hl⟩)) := by
    simp only [firstUnsat, toFinCNF, List.find?_map]
    congr 2 with ⟨c, hc⟩
    simp only [Function.comp_apply, eval_toFinClause, p]
  rw [hfind_eq]
  cases hfa : ψ.attach.find? (fun x => p x.val) with
  | none =>
    have hf : ψ.find? p = none := by rw [← find?_attach, hfa]; rfl
    have hfc : firstUnsatClauseBits ψ (List.ofFn σ) = [] :=
      headD_filter_eq_nil_of_find?_eq_none hf
    simp only [walkStepBits, hfc, List.isEmpty_nil, ↓reduceIte, Option.map_none,
      ProbComp.eval_pure, PMF.pure_map]
  | some x =>
    rcases x with ⟨c, hc_mem⟩
    have hf : ψ.find? p = some c := by rw [← find?_attach, hfa]; rfl
    obtain ⟨hfc, hc_ne⟩ := headD_filter_eq_of_find?_eq_some hne hf
    have hc_pos : 0 < c.length := List.length_pos_iff.mpr hc_ne
    let hc_vars : ∀ l ∈ c, l.1 < n :=
      fun l hl => hvars l.1 (CNF.mem_vars.mpr ⟨c, hc_mem, l.2, hl⟩)
    have hfin_len : (toFinClause c hc_vars).length = c.length := length_toFinClause c hc_vars
    simp only [walkStepBits, show firstUnsatClauseBits ψ (List.ofFn σ) = c from hfc,
      List.isEmpty_eq_false_iff.mpr hc_ne, Bool.false_eq_true, ↓reduceIte, Option.map_some,
      fairFlipStep, show (toFinClause c hc_vars).length ≠ 0 from hfin_len ▸ hc_pos.ne',
      ↓reduceDIte, ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_comp]
    calc (ProbComp.eval (ProbComp.sampleModNat w c.length)).bind
          (fun r => PMF.pure (flipBitAt (List.ofFn σ) (c.getD (min c.length r) (0, false)).1))
        = (ProbComp.eval (ProbComp.sampleModNat w (toFinClause c hc_vars).length)).bind
          (fun r => PMF.pure (List.ofFn (flipOn
            {((toFinClause c hc_vars).get ⟨r % (toFinClause c hc_vars).length,
              Nat.mod_lt r (Nat.pos_of_ne_zero (hfin_len ▸ hc_pos.ne'))⟩).1} σ))) := by
          simp only [hfin_len]
          refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun r hr => ?_
          have hr_lt : r < c.length := ProbComp.lt_of_mem_support_sampleModNat hc_pos hr
          have hgetD : c.getD (min c.length r) (0, false) = c[r] := by
            rw [Nat.min_eq_right hr_lt.le, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem hr_lt, Option.getD_some]
          have hv_lt : c[r].1 < n :=
            hvars c[r].1 (CNF.mem_vars.mpr ⟨c, hc_mem, c[r].2, List.getElem_mem hr_lt⟩)
          rw [hgetD, flipBitAt_ofFn σ hv_lt]
          congr 3
          simp only [toFinClause, List.get_eq_getElem, List.getElem_map, List.getElem_attach,
            Nat.mod_eq_of_lt hr_lt]
      _ = (ProbComp.eval (ProbComp.sampleModNat w (toFinClause c hc_vars).length)).map _ := rfl

private theorem fairWalk_eq_pure_of_firstUnsat_none {V : Type*} [DecidableEq V]
    (w : ℕ) (φ : CNF V) (t : ℕ) {σ : V → Bool} (hnone : firstUnsat φ σ = none) :
    fairWalk w φ t σ = PMF.pure σ := by
  cases t with
  | zero => rfl
  | succ t => simp only [fairWalk, hnone]

private theorem eval_iterate_walkStepBits_ofFn {n : ℕ} (ψ : CNF ℕ) (hvars : ∀ v ∈ ψ.vars, v < n)
    (hne : ∀ c ∈ ψ, c ≠ []) (w t : ℕ) (σ : Fin n → Bool) :
    ProbComp.eval (OracleComp.iterate t (walkStepBits ψ w) (List.ofFn σ)) =
      (fairWalk w (toFinCNF ψ hvars) t σ).map List.ofFn := by
  induction t generalizing σ with
  | zero =>
    simp only [OracleComp.iterate_zero, ProbComp.eval_pure, fairWalk, PMF.pure_map]
  | succ t ih =>
    rw [OracleComp.iterate_succ_bind, ProbComp.eval_bind,
      eval_walkStepBits_ofFn ψ hvars hne w σ, PMF.bind_map]
    simp only [fairWalk]
    cases hfu : firstUnsat (toFinCNF ψ hvars) σ with
    | none =>
      simp only [PMF.pure_bind, Function.comp_apply, ih,
        fairWalk_eq_pure_of_firstUnsat_none w _ t hfu, PMF.pure_map]
    | some c =>
      rw [PMF.map_bind]
      apply Cslib.Probability.PMF.bind_congr_on_support
      intro σ' _
      exact ih σ'

private theorem eval_schoeningBodyProg_eq_map_fairTrial (k : ℕ) (φ : CNF ℕ)
    (hne : ∀ c ∈ φ.denseRelabel, c ≠ []) :
    let n := φ.numVars
    let w := 2 * n + k + 3
    let ψFin := toFinCNF φ.denseRelabel (fun _ hv => CNF.mem_vars_denseRelabel_lt φ hv)
    ProbComp.eval (schoeningBodyProg k φ) =
      (fairTrial w ψFin).map (fun σ => CNF.eval σ ψFin) := by
  intro n w ψFin
  dsimp only [schoeningBodyProg]
  rw [ProbComp.eval_bind, BitString.eval_sampleList, BitString.uniformList, PMF.bind_map]
  dsimp only [fairTrial]
  rw [Fintype.card_fin, PMF.map_bind]
  apply Cslib.Probability.PMF.bind_congr_on_support
  intro σ _
  rw [Function.comp_apply, ProbComp.eval_bind,
    eval_iterate_walkStepBits_ofFn φ.denseRelabel
      (fun _ hv => CNF.mem_vars_denseRelabel_lt φ hv) hne w (3 * n) σ,
    PMF.bind_map, PMF.map]
  apply Cslib.Probability.PMF.bind_congr_on_support
  intro τ _
  simp only [Function.comp_def, ProbComp.eval_pure]
  exact congrArg PMF.pure (eval_toFinCNF _ _ τ).symm

/-- **Zero false positives for `schoeningTrialProg`.** If `φ ∉ KSAT k`, one trial returns `true`
with probability `0`. -/
theorem eval_schoeningTrialProg_true_eq_zero_of_not_mem_KSAT {k : ℕ} {φ : CNF ℕ}
    (hnot : φ ∉ KSAT k) :
    ProbComp.eval (schoeningTrialProg k φ) true = 0 := by
  dsimp only [schoeningTrialProg]
  by_cases hg : guardKSAT k φ = true
  · simp only [hg, ↓reduceIte]
    have hlen : ∀ c ∈ φ, c.length ≤ k := by
      intro c hc
      simp only [guardKSAT, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hg
      exact (hg c hc).2
    have hunsat : ¬φ.Satisfiable := fun hsat => hnot ⟨hlen, hsat⟩
    have hunsat_dense : ¬φ.denseRelabel.Satisfiable := by
      rwa [CNF.satisfiable_denseRelabel]
    by_contra hpos
    have hmem : true ∈ (ProbComp.eval (schoeningBodyProg k φ)).support :=
      (PMF.mem_support_iff _ _).mpr hpos
    dsimp only [schoeningBodyProg] at hmem
    rw [ProbComp.eval_bind, PMF.mem_support_bind_iff] at hmem
    obtain ⟨bits₀, _, hmem⟩ := hmem
    rw [ProbComp.eval_bind, PMF.mem_support_bind_iff] at hmem
    obtain ⟨bitsF, _, hmem⟩ := hmem
    rw [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hmem
    exact hunsat_dense ⟨bitsAssign bitsF, hmem.symm⟩
  · have hg' : guardKSAT k φ = false := Bool.eq_false_iff.mpr hg
    simp only [hg', Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure, PMF.pure_apply,
      Bool.true_eq_false]

/-- **Single-trial success lower bound on `KSAT k`.** For `k ≥ 3` and `φ ∈ KSAT k`, one execution
of `schoeningTrialProg k φ` returns `true` with probability at least half of Schöning's bound. -/
theorem succeedProb_le_schoeningTrialProg {k : ℕ} (hk : 3 ≤ k) {φ : CNF ℕ} (hφ : φ ∈ KSAT k) :
    (1 / 2 : ℝ) * ((((k : ℝ) - 1) / k) ^ (k - 3) *
        ((k : ℝ) / (2 * ((k : ℝ) - 1))) ^ φ.numVars / (3 * φ.numVars + 1)) ≤
      (ProbComp.eval (schoeningTrialProg k φ) true).toReal := by
  obtain ⟨hlen, hsat⟩ := hφ
  have ne_nil_of_sat : ∀ (ψ : CNF ℕ), ψ.Satisfiable → ∀ c ∈ ψ, c ≠ [] :=
    fun _ ⟨σ, hσ⟩ c hc hnil => by
      rw [CNF.eval_eq_true_iff] at hσ
      have hce := hσ c hc
      simp [hnil] at hce
  have hg : guardKSAT k φ = true := by
    simp only [guardKSAT, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true',
      List.isEmpty_eq_false_iff, decide_eq_true_eq]
    exact fun c hc => ⟨ne_nil_of_sat φ hsat c hc, hlen c hc⟩
  let ψFin := toFinCNF φ.denseRelabel (fun _ hv => CNF.mem_vars_denseRelabel_lt φ hv)
  have hsat_dense := (CNF.satisfiable_denseRelabel φ).mpr hsat
  have hsat_fin : ψFin.Satisfiable := (satisfiable_toFinCNF φ.denseRelabel _).mpr hsat_dense
  have hlen_fin : ∀ c ∈ ψFin, c.length ≤ k := by
    rintro c hc
    simp only [ψFin, toFinCNF, List.mem_map, List.mem_attach, true_and, Subtype.exists] at hc
    obtain ⟨c₀, hc₀, rfl⟩ := hc
    rw [length_toFinClause]
    exact ((CNF.all_length_le_denseRelabel φ).mpr hlen) c₀ hc₀
  have htrue_eq : (ProbComp.eval (schoeningTrialProg k φ) true).toReal =
      succeedProb ψFin (fairTrial (2 * φ.numVars + k + 3) ψFin) := by
    rw [schoeningTrialProg, ite_eq_left hg,
      eval_schoeningBodyProg_eq_map_fairTrial k φ (ne_nil_of_sat φ.denseRelabel hsat_dense),
      succeedProb, PMF.map_apply, PMF.toOuterMeasure_apply]
    congr 2 with σ
    by_cases hσ : CNF.eval σ ψFin = true
    · simp [hσ, ψFin]
    · have hσf : CNF.eval σ ψFin = false := Bool.eq_false_iff.mpr hσ
      simp [hσf, ψFin]
  rw [htrue_eq]
  have h1 := trial_success_of_length_le hk hsat_fin hlen_fin
  have h2 := half_mul_succeedProb_trial_le_fairTrial hlen_fin
  simp only [Fintype.card_fin] at h1 h2
  exact (mul_le_mul_of_nonneg_left h1 (by positivity)).trans h2

end TrialProgram

/-! ### Polynomial-time binary trial count and multitape Schöning decider -/

section MachineDecider

/-- **Polynomial-time binary trial count.** For fixed `k ≥ 3` and confidence `c : ℕ`, computing
`2 * schoeningTrials k φ.numVars c` from `encCNF φ` into binary (`encNat`) runs in polynomial
time. -/
theorem computableInPolyTime_two_mul_schoeningTrials {k : ℕ} (hk : 3 ≤ k) (c : ℕ) :
    ComputableInPolyTime (fun φ : CNF ℕ => 2 * schoeningTrials k φ.numVars c) encCNF encNat := by
  simp_rw [schoeningTrials_eq hk]
  open ComputableInPolyTime in
  have hn_u : ComputableInPolyTime (CNF.numVars (V := ℕ)) encCNF encUnary :=
    SAT.computableInPolyTime_numVars
  have h3n1 := binary_add' (binary_mul' (.const 3) (unary_to_binary.comp hn_u)) (.const 1)
  have hden := binary_mul' (binary_pow' (.const k) hn_u) (.const ((k - 1) ^ (k - 3)))
  have hnum := binary_sub' (binary_add'
    (binary_mul' (binary_mul' h3n1 (binary_pow' (.const (2 * (k - 1))) hn_u))
      (.const (k ^ (k - 3))))
    hden) (.const 1)
  exact binary_mul' (.const 2) (binary_mul' (binary_div' hnum hden) (.const c))

private theorem numVars_le_length_encCNF (φ : CNF ℕ) :
    φ.numVars ≤ (encCNF φ).length := by
  calc φ.numVars = φ.vars.toFinset.card := rfl
    _ ≤ φ.vars.length := List.toFinset_card_le φ.vars
    _ ≤ (encCNF φ).length := SAT.length_vars_le φ

private theorem schoening_clock_le {k : ℕ} (hk : 3 ≤ k) (c C₀ E₀ : ℕ) (φ : CNF ℕ) :
    (C₀ * ((2 * schoeningTrials k φ.numVars c + 1) * ((encCNF φ).length + 1) ^ E₀) : ℝ) ≤
      ((C₀ * (18 * c + 1) : ℕ) : ℝ) *
        (((2 * ((k : ℝ) - 1)) / k) ^ φ.numVars *
          ((encCNF φ).length + 1 : ℝ) ^ (E₀ + 1)) := by
  set n := φ.numVars
  set L := (encCNF φ).length
  set base := (2 * ((k : ℝ) - 1)) / k
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hr1 : 1 ≤ base := (le_div_iff₀ (by linarith)).mpr (by linarith)
  have h1_le : (1 : ℝ) ≤ base ^ n * (L + 1) := by
    have : 1 ≤ base ^ n := one_le_pow₀ hr1
    have : (1 : ℝ) ≤ (L : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) L]
    nlinarith
  have h9 : (9 * (n : ℝ) + 4) * base ^ n * c ≤ 9 * ((L : ℝ) + 1) * base ^ n * c := by
    have : (n : ℝ) ≤ L := by exact_mod_cast numVars_le_length_encCNF φ
    have : (0 : ℝ) ≤ base ^ n := by positivity
    have : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    gcongr; linarith
  have htrials_R :
      (2 * (schoeningTrials k n c : ℝ) + 1) ≤ (18 * (c : ℝ) + 1) * base ^ n * (L + 1) := by
    linarith [schoeningTrials_le hk n c]
  push_cast
  rw [pow_succ']
  have : (0 : ℝ) ≤ (C₀ : ℝ) * ((L : ℝ) + 1) ^ E₀ := by positivity
  calc (C₀ : ℝ) * ((2 * (schoeningTrials k n c : ℝ) + 1) * ((L : ℝ) + 1) ^ E₀)
      = (2 * (schoeningTrials k n c : ℝ) + 1) * ((C₀ : ℝ) * ((L : ℝ) + 1) ^ E₀) := by ring
    _ ≤ ((18 * (c : ℝ) + 1) * base ^ n * (L + 1)) * ((C₀ : ℝ) * ((L : ℝ) + 1) ^ E₀) := by gcongr
    _ = _ := by ring

private theorem schoening_soundness_le {k c : ℕ} (hk : 3 ≤ k) {φ : CNF ℕ} (hφ : φ ∈ KSAT k) :
    1 - Real.exp (-(c : ℝ)) ≤
      ((ProbComp.eval (OracleComp.iterate (2 * schoeningTrials k φ.numVars c)
        (repeatAnyStep (schoeningTrialProg k φ)) false)).map encBool [true]).toReal := by
  let μ := ProbComp.eval (OracleComp.iterate (2 * schoeningTrials k φ.numVars c)
    (repeatAnyStep (schoeningTrialProg k φ)) false)
  have hmap_true : (μ.map encBool) [true] = μ true := by
    rw [PMF.map_apply, tsum_bool]; simp [encBool_apply]
  rw [hmap_true, Cslib.Probability.PMF.toReal_true_eq_one_sub,
    eval_iterate_repeatAnyStep_false_toReal]
  set p := (ProbComp.eval (schoeningTrialProg k φ) true).toReal
  set n := φ.numVars
  set P₀ := (((k : ℝ) - 1) / k) ^ (k - 3) * ((k : ℝ) / (2 * ((k : ℝ) - 1))) ^ n / (3 * n + 1)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hP₀pos : 0 < P₀ := by positivity
  have hinv : (3 * n + 1 : ℝ) * (2 * ((k : ℝ) - 1) / k) ^ n *
      ((k : ℝ) / ((k : ℝ) - 1)) ^ (k - 3) = P₀⁻¹ := by
    simp only [P₀, inv_div, div_pow]
    field_simp
  have hprod_ge : (c : ℝ) ≤ ((2 * schoeningTrials k n c : ℕ) : ℝ) * p := by
    rw [schoeningTrials, hinv]
    push_cast
    calc (c : ℝ) = (P₀⁻¹ * c) * P₀ := by field_simp
      _ ≤ (⌈P₀⁻¹⌉₊ * c) * P₀ := by gcongr; exact Nat.le_ceil _
      _ = (2 * (⌈P₀⁻¹⌉₊ * c)) * ((1 / 2 : ℝ) * P₀) := by ring
      _ ≤ (2 * (⌈P₀⁻¹⌉₊ * c)) * p := by gcongr; exact succeedProb_le_schoeningTrialProg hk hφ
  have hp_le_one : p ≤ 1 := Cslib.Probability.PMF.toReal_apply_le_one _ _
  linarith [Real.one_sub_pow_le_exp hp_le_one hprod_ge]

/-- **Schöning's `k`-SAT algorithm on a fair-coin multitape Turing machine.** For every `k ≥ 3`
and confidence parameter `c : ℕ`, there exist a finite-control fair-coin `MultiTapePTM`, a clock
`T : CNF ℕ → ℕ`, and polynomial constants `C E : ℕ` such that for every `φ : CNF ℕ`
(`n = φ.numVars`, `L = (encCNF φ).length`):

1. **Deterministic worst-case halting:** every branch halts within `T φ` steps
   (`machine.toNTM.RunsInTime (encCNF φ) (T φ)`),
2. **Sub-`2 ^ n` runtime:** `(T φ : ℝ) ≤ C * (((2 * (k - 1)) / k) ^ n * (L + 1) ^ E)`,
3. **Polynomial workspace:** `machine.toNTM.RunsInSpace (encCNF φ) (C * (L + 1) ^ E)`,
4. **Zero false positives:** if `φ ∉ KSAT k`, `ProbComp.eval (machine.runClosed (T φ) (encCNF φ)) =
   PMF.pure [false]`,
5. **Amplified soundness:** if `φ ∈ KSAT k`, the acceptance probability `[true]` is at least
   `1 - exp (-c)`. -/
theorem exists_multiTapePTM_KSAT {k : ℕ} (hk : 3 ≤ k) (c : ℕ) :
    ∃ (K : ℕ) (Control : Type) (_ : Finite Control)
      (machine : MultiTapePTM K Bool Control) (T : CNF ℕ → ℕ) (C E : ℕ),
      ∀ φ : CNF ℕ,
        (∀ final ∈ (ProbComp.eval
            (machine.runClosedConfigFrom (T φ) (machine.initialConfig (encCNF φ)))).support,
            final.tapes.state = none) ∧
          machine.toNTM.RunsInTime (encCNF φ) (T φ) ∧
          ((T φ : ℝ) ≤
            (C : ℝ) * (((2 * ((k : ℝ) - 1)) / k) ^ φ.numVars *
              ((encCNF φ).length + 1 : ℝ) ^ E)) ∧
          machine.toNTM.RunsInSpace (encCNF φ) (C * ((encCNF φ).length + 1) ^ E) ∧
          (φ ∉ KSAT k →
            ProbComp.eval (machine.runClosed (T φ) (encCNF φ)) = PMF.pure [false]) ∧
          (φ ∈ KSAT k →
            1 - Real.exp (-(c : ℝ)) ≤
              (ProbComp.eval (machine.runClosed (T φ) (encCNF φ)) [true]).toReal) := by
  obtain ⟨K, Control, hfin, machine, C₀, E₀, hM⟩ :=
    IsPPTOn.exists_multiTapePTM_repeatAnyBool_binary
      (isPPTOn_schoeningTrialProg k)
      (computableInPolyTime_two_mul_schoeningTrials hk c)
  refine ⟨K, Control, hfin, machine,
    fun φ => C₀ * ((2 * schoeningTrials k φ.numVars c + 1) * ((encCNF φ).length + 1) ^ E₀),
    C₀ * (18 * c + 1), E₀ + 1, fun φ => ?_⟩
  obtain ⟨hhalt, heval, hspace₀⟩ := hM φ
  refine ⟨hhalt, machine.runsInTime_toNTM hhalt, by simpa using schoening_clock_le hk c C₀ E₀ φ,
    fun p => (hspace₀ p).trans (Nat.mul_le_mul (Nat.le_mul_of_pos_right _ (by omega))
      (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ _))),
    fun hnot => by rw [heval, eval_iterate_repeatAnyStep_eq_pure_false _ _
      (eval_schoeningTrialProg_true_eq_zero_of_not_mem_KSAT hnot), PMF.pure_map, encBool_apply],
    fun hmem => heval ▸ schoening_soundness_le hk hmem⟩

/-- **Bounded-error multitape `k`-SAT decider (`DecidesWithBoundedErrorInTime`).** Specializing
`exists_multiTapePTM_KSAT` to confidence `c = 2` (`exp (-2) ≤ 1 / 3`) yields a fair-coin
`MultiTapePTM` deciding `KSAT k` (`k ≥ 3`) with bounded error, zero false positives, polynomial
workspace, and `O(((2 (k - 1)) / k) ^ n * (L + 1) ^ E)` worst-case halting time. -/
theorem exists_decidesWithBoundedErrorInTime_KSAT {k : ℕ} (hk : 3 ≤ k) :
    ∃ (K : ℕ) (Control : Type) (_ : Finite Control)
      (machine : MultiTapePTM K Bool Control) (T : CNF ℕ → ℕ) (C E : ℕ),
      machine.DecidesWithBoundedErrorInTime encCNF (KSAT k) T ∧
      (∀ φ : CNF ℕ,
        ((T φ : ℝ) ≤
          (C : ℝ) * (((2 * ((k : ℝ) - 1)) / k) ^ φ.numVars *
            ((encCNF φ).length + 1 : ℝ) ^ E)) ∧
        machine.toNTM.RunsInSpace (encCNF φ) (C * ((encCNF φ).length + 1) ^ E) ∧
        (φ ∉ KSAT k →
          ProbComp.eval (machine.runClosed (T φ) (encCNF φ)) = PMF.pure [false])) := by
  obtain ⟨K, Control, hfin, machine, T, C, E, hspec⟩ := exists_multiTapePTM_KSAT hk 2
  refine ⟨K, Control, hfin, machine, T, C, E, fun φ => ?_,
    fun φ => ⟨(hspec φ).2.2.1, (hspec φ).2.2.2.1, (hspec φ).2.2.2.2.1⟩⟩
  obtain ⟨hhalt, -, -, -, hno, hyes⟩ := hspec φ
  refine ⟨hhalt, ?_⟩
  by_cases hmem : φ ∈ KSAT k
  · rw [show indicator (KSAT k) φ = true by simp [indicator, hmem]]
    have hreal :
        (2 / 3 : ℝ) ≤ (ProbComp.eval (machine.runClosed (T φ) (encCNF φ)) [true]).toReal := by
      have hy := hyes hmem; norm_num at hy; linarith [Real.exp_neg_two_le_one_third]
    simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3), ENNReal.ofReal_ofNat] using
      (ENNReal.ofReal_le_iff_le_toReal (_root_.PMF.apply_ne_top _ _)).mpr hreal
  · rw [show indicator (KSAT k) φ = false by simp [indicator, hmem], hno hmem, PMF.pure_apply_self]
    rw [ENNReal.div_le_iff_le_mul (Or.inl (by norm_num)) (Or.inl ENNReal.ofNat_ne_top)]; norm_num

/-- **Schöning's `(4 / 3) ^ n` bounded-error multitape `3`-SAT decider.** -/
theorem exists_decidesWithBoundedErrorInTime_ThreeSAT :
    ∃ (K : ℕ) (Control : Type) (_ : Finite Control)
      (machine : MultiTapePTM K Bool Control) (T : CNF ℕ → ℕ) (C E : ℕ),
      machine.DecidesWithBoundedErrorInTime encCNF ThreeSAT T ∧
      (∀ φ : CNF ℕ,
        ((T φ : ℝ) ≤
          (C : ℝ) * ((4 / 3 : ℝ) ^ φ.numVars * ((encCNF φ).length + 1 : ℝ) ^ E)) ∧
        machine.toNTM.RunsInSpace (encCNF φ) (C * ((encCNF φ).length + 1) ^ E) ∧
        (φ ∉ ThreeSAT →
          ProbComp.eval (machine.runClosed (T φ) (encCNF φ)) = PMF.pure [false])) := by
  obtain ⟨K, Control, hfin, machine, T, C, E, hdec, hbounds⟩ :=
    exists_decidesWithBoundedErrorInTime_KSAT (le_refl 3)
  refine ⟨K, Control, hfin, machine, T, C, E, hdec, fun φ => ?_⟩
  obtain ⟨hT, hspace, hno⟩ := hbounds φ
  exact ⟨by convert hT using 4; norm_num, hspace, hno⟩

end MachineDecider

end Cslib.Complexity.Schoening
