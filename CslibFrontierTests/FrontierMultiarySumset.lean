/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Computability.Circuit.Frontier.BoundedFanIn
public import CslibFrontier.Computability.Circuit.Frontier.Correlation
public import CslibFrontier.Computability.Circuit.Frontier.FanInTwo
public import CslibFrontier.Computability.Circuit.Frontier.SumsetBridge
public import CslibFrontier.Computability.Circuit.Frontier.Unconditional
import Mathlib.Logic.Equiv.Fin.Basic

/-! Checked `module` clients for `Circuit.multiarySize`, unary/constant gate deduplication
(`Circuit.exists_eval_eq_multiarySize_size_le`), the upgraded `multiarySize` frontier lower bounds,
and `CslibFrontier.Computability.Circuit.Frontier.SumsetBridge`. -/

@[expose] public section

namespace CslibFrontierTests.FrontierMultiarySumset

open Cslib Cslib.Circuits Cslib.Circuits.Frontier
open Cslib.AffineDisperser.Li Cslib.Probability
open scoped Cslib.Probability.PMF
open Filter Real

/-! ### 1. Concrete circuit with unary and constant gate bloat (`multiarySize = 1`) -/

/-- A 3-operation Boolean signature with nullary `false`, unary `not`, and binary `xor`. -/
inductive ToyOp : Type
  | constFalse
  | not
  | xor
  deriving DecidableEq

/-- Signature assigning arities `0`, `1`, and `2` to `constFalse`, `not`, and `xor`. -/
abbrev toySig : Signature where
  Op := ToyOp
  Arity
    | .constFalse => 0
    | .not => 1
    | .xor => 2

/-- Standard Boolean interpretation of `toySig`. -/
def toyInterp : Interpretation toySig Bool
  | .constFalse, _ => false
  | .not, w => !(w 0)
  | .xor, w => xor (w 0) (w 1)

/-- Append a `constFalse` gate and two `not` gates on the last wire of a nonempty program. -/
def addBloatStep {g : ℕ} (p : Program toySig 2 (g + 1)) : Program toySig 2 (g + 1 + 3) :=
  let p1 := p.gate ⟨.constFalse, Fin.elim0⟩
  let p2 := p1.gate ⟨.not, fun _ => .gate (Fin.castSucc (Fin.last g))⟩
  p2.gate ⟨.not, fun _ => .gate (Fin.last (g + 2))⟩

/-- Program computing `xor (x 0) (x 1)` followed by `k` rounds of `(constFalse, not, not)` bloat. -/
def bloatedXorProg : (k : ℕ) → Program toySig 2 (3 * k + 1)
  | 0 => Program.empty.gate ⟨.xor, ![.input 0, .input 1]⟩
  | k + 1 => addBloatStep (bloatedXorProg k)

/-- Circuit on 2 inputs with `3 * k + 1` total gates, `2 * k + 1` inner gates, and only `1`
multiary gate (`xor`). -/
def bloatedXorCircuit (k : ℕ) : Circuit toySig 2 1 :=
  ⟨bloatedXorProg k, fun _ => .gate (Fin.last (3 * k))⟩

example : (bloatedXorCircuit 1).size = 4 :=
  rfl

example : (bloatedXorCircuit 1).innerSize = 3 := by
  decide

example : (bloatedXorCircuit 1).multiarySize = 1 := by
  decide

example : (bloatedXorCircuit 1).eval toyInterp ![true, false] 0 = true := by
  decide

example : (bloatedXorCircuit 1).eval toyInterp ![true, true] 0 = false := by
  decide

private theorem mem_multiaryGates_gate_val_zero {g : ℕ} {p : Program toySig 2 (g + 1)}
    {line : Line toySig 2 (g + 1)} (hl : ¬ 2 ≤ toySig.Arity line.op)
    (hp : ∀ j : Fin (g + 1), 2 ≤ toySig.Arity (p.lines j).op ↔ j.val = 0)
    (j : Fin (g + 2)) :
    2 ≤ toySig.Arity ((p.gate line).lines j).op ↔ j.val = 0 := by
  refine Fin.lastCases ?_ (fun j' => ?_) j
  · simp [Program.lines_gate_last, Line.mapWires, hl]
  · simp [Program.lines_gate_castSucc, Line.mapWires, hp j']

theorem multiarySize_bloatedXorCircuit (k : ℕ) : (bloatedXorCircuit k).multiarySize = 1 := by
  have hmem : ∀ (k : ℕ) (j : Fin (3 * k + 1)),
      2 ≤ toySig.Arity ((bloatedXorProg k).lines j).op ↔ j.val = 0 := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      unfold bloatedXorProg addBloatStep
      intro j
      exact mem_multiaryGates_gate_val_zero (by simp)
        (mem_multiaryGates_gate_val_zero (by simp)
          (mem_multiaryGates_gate_val_zero (by simp) ih)) j
  have hset : (bloatedXorProg k).multiaryGates = {⟨0, Nat.succ_pos _⟩} := by
    ext j
    simp only [Program.mem_multiaryGates, hmem k j, Finset.mem_singleton, Fin.ext_iff]
  simp [Circuit.multiarySize, bloatedXorCircuit, hset]

/-- Even with `k = 1000` (`size = 3001`), deduplicating unary and constant gates over `toySig`
produces an equivalent circuit over `toySig` with at most `1` multiary gate and at most `15` total
gates. -/
example : ∃ c' : Circuit toySig 2 1,
    c'.eval toyInterp = (bloatedXorCircuit 1000).eval toyInterp ∧
    c'.FanInAtMost 2 ∧ c'.multiarySize ≤ 1 ∧ c'.size ≤ 15 := by
  have hmult : (bloatedXorCircuit 1000).multiarySize = 1 := multiarySize_bloatedXorCircuit 1000
  have hfan : (bloatedXorCircuit 1000).FanInAtMost 2 :=
    (bloatedXorCircuit 1000).fanInAtMost_of_forall_arity_le fun op => by cases op <;> decide
  obtain ⟨c', heval, hfan', hmult', hsize'⟩ :=
    (bloatedXorCircuit 1000).exists_eval_eq_multiarySize_size_le toyInterp
  have hbool : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_bool]
  rw [hmult] at hmult' hsize'
  rw [hbool] at hsize'
  exact ⟨c', heval, hfan' 2 hfan, hmult', by omega⟩

/-- The compiled network of `bloatedXorCircuit 1000` has `cycleRank + |read| ≤ 2` because the
`2000` unary `not` gates and `1000` constant gates contribute `0` to `multiarySize`. -/
example : (Compiler.graph (bloatedXorCircuit 1000)).cycleRank +
    (Compiler.network (bloatedXorCircuit 1000) toyInterp fun _ => {true}).read.ncard ≤ 2 := by
  have hmult : (bloatedXorCircuit 1000).multiarySize = 1 := multiarySize_bloatedXorCircuit 1000
  have hfan : (bloatedXorCircuit 1000).FanInAtMost 2 :=
    (bloatedXorCircuit 1000).fanInAtMost_of_forall_arity_le fun op => by cases op <;> decide
  have h := Compiler.cycleRank_add_ncard_read_le_multiarySize toyInterp (fun _ => {true})
    hfan (Compiler.connected (bloatedXorCircuit 1000))
  rw [hmult] at h
  omega

/-! ### 2. Concrete non-vacuous `IsSumsetExtractor` and `RectangleBias` witness on `BitString 1` -/

/-- On `BitString 1`, the identity map is an exact `(1, 1, 0)` sumset extractor: any source `B` on
`BitString 1` with `1 ≤ minEntropy B` is uniform, so `A + B` is uniform. -/
theorem isSumsetExtractor_id_one : IsSumsetExtractor (id : BitString 1 → BitString 1) 1 1 0 := by
  intro A B _ hB
  let e : BitString 1 ≃ Bool := Equiv.funUnique (Fin 1) Bool
  have hB_le : ∀ b : Bool, ((B.map e) b).toReal ≤ 1 / 2 := fun b => by
    have heq : (B.map e) b = B (e.symm b) := PMF.map_equiv_apply B e b
    have hm := (PMF.le_minEntropy_iff B).mp hB (e.symm b)
    rw [heq]
    exact hm.trans_eq (by norm_num [Real.rpow_neg])
  have hsum : ((B.map e) true).toReal + ((B.map e) false).toReal = 1 := by
    simpa [Fintype.sum_bool] using PMF.sum_toReal (B.map e)
  have htrue : ((B.map e) true).toReal = 1 / 2 := by
    linarith [hB_le true, hB_le false]
  have hdist0 : dist (B.map e) (PMF.uniformOfFintype Bool) ≤ 0 := by
    rw [PMF.dist_uniformOfFintype_bool, htrue]
    norm_num
  have hBe : B.map e = PMF.uniformOfFintype Bool := dist_le_zero.mp hdist0
  have hBunif : B = PMF.uniformOfFintype (BitString 1) := by
    calc B = (B.map e).map e.symm := by rw [PMF.map_comp, Equiv.symm_comp_self, PMF.map_id]
      _ = (PMF.uniformOfFintype Bool).map e.symm := by rw [hBe]
      _ = PMF.uniformOfFintype (BitString 1) := PMF.uniformOfFintype_map_equiv e.symm
  have hbind : (A.bind fun a => B.map fun b => a + b) = PMF.uniformOfFintype (BitString 1) := by
    rw [hBunif]
    have hshift : (fun a : BitString 1 =>
        (PMF.uniformOfFintype (BitString 1)).map fun b => a + b) =
        fun _ => PMF.uniformOfFintype (BitString 1) :=
      funext fun a => PMF.uniformOfFintype_map_equiv (Equiv.addLeft a)
    rw [hshift, PMF.bind_const]
  rw [PMF.map_id, hbind, dist_self]

example : RectangleBias {x : BitString 1 | x 0 = true} 2 0 :=
  rectangleBias_of_isSumsetExtractor isSumsetExtractor_id_one 0 true

example : RectangleFree {x : BitString 1 | x 0 = true} 2 :=
  (rectangleBias_of_isSumsetExtractor isSumsetExtractor_id_one 0 true).rectangleFree
    (by norm_num) (by norm_num)

/-- Every 1-bit map `ext : BitString n → BitString 1` is trivially a `(k, k, 1 / 2)` sumset
extractor, allowing `rectangleBias_of_isSumsetExtractor` to be exercised on concrete rectangles of
side size `2 ^ k` at small `n`. -/
theorem isSumsetExtractor_one_half {n k : ℕ} (ext : BitString n → BitString 1) :
    IsSumsetExtractor ext k k (1 / 2) := by
  intro A B _ _
  let e : BitString 1 ≃ Bool := Equiv.funUnique (Fin 1) Bool
  let p := (A.bind fun a => B.map fun b => a + b).map ext
  have hp : p = (p.map e).map e.symm := by
    rw [PMF.map_comp, Equiv.symm_comp_self, PMF.map_id]
  have hu : PMF.uniformOfFintype (BitString 1) = (PMF.uniformOfFintype Bool).map e.symm :=
    (PMF.uniformOfFintype_map_equiv e.symm).symm
  have hsum : ((p.map e) true).toReal + ((p.map e) false).toReal = 1 := by
    simpa [Fintype.sum_bool] using PMF.sum_toReal (p.map e)
  have h0 : 0 ≤ ((p.map e) true).toReal := ENNReal.toReal_nonneg
  have h1 : ((p.map e) true).toReal ≤ 1 := by
    linarith [ENNReal.toReal_nonneg (a := (p.map e) false)]
  calc dist p (PMF.uniformOfFintype (BitString 1))
      = dist ((p.map e).map e.symm) ((PMF.uniformOfFintype Bool).map e.symm) := by rw [← hp, ← hu]
    _ ≤ dist (p.map e) (PMF.uniformOfFintype Bool) := PMF.dist_map_le _ _ e.symm
    _ = |((p.map e) true).toReal - 1 / 2| := PMF.dist_uniformOfFintype_bool (p.map e)
    _ ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩

/-- Non-vacuous rectangle-bridge check on `BitString 2` at `k = 1`, `X = {0}`, `A = univ`,
`B = univ`, where both side cardinalities meet `2 ^ 1 = 2` and the rectangle has `4` elements. -/
example :
    let X : Set (Fin 2) := {0}
    let A : Set (X → Bool) := Set.univ
    let B : Set (↥Xᶜ → Bool) := Set.univ
    2 ^ 1 ≤ A.ncard ∧ 2 ^ 1 ≤ B.ncard ∧ (rectangle X A B).ncard = 4 ∧
      |((rectangle X A B ∩ {x : BitString 2 | (x 0 && x 1) = true}).ncard : ℝ) -
        (rectangle X A B).ncard / 2| ≤ 1 / 2 * (rectangle X A B).ncard := by
  dsimp only
  have hXc : ({0} : Set (Fin 2))ᶜ = {1} := by
    ext i
    fin_cases i <;> simp
  have hA : (Set.univ : Set (({0} : Set (Fin 2)) → Bool)).ncard = 2 := by
    rw [Set.ncard_univ, Nat.card_fun, Nat.card_coe_set_eq, Set.ncard_singleton,
      Nat.card_eq_fintype_card, Fintype.card_bool, pow_one]
  have hB : (Set.univ : Set (↥({0} : Set (Fin 2))ᶜ → Bool)).ncard = 2 := by
    rw [Set.ncard_univ, Nat.card_fun, Nat.card_coe_set_eq, hXc, Set.ncard_singleton,
      Nat.card_eq_fintype_card, Fintype.card_bool, pow_one]
  have hR : (rectangle (U := Bool) ({0} : Set (Fin 2)) Set.univ Set.univ).ncard = 4 := by
    rw [ncard_rectangle, hA, hB]
  have hbias := rectangleBias_of_isSumsetExtractor
    (isSumsetExtractor_one_half (n := 2) (k := 1) fun x => fun _ => x 0 && x 1)
    0 true {0} Set.univ Set.univ (by omega) (by omega)
  exact ⟨by omega, by omega, hR, hbias⟩

/-! ### 3. Asymptotic `multiarySize` and `SumsetBridge` client instantiations -/

example : MultiaryLowerBound.{0, 0} (457597 / 100000) :=
  multiaryLowerBound_457597_div_100000

example : MultiaryAverageCaseBound.{0, 0} (457597 / 100000) :=
  multiaryAverageCaseBound_457597_div_100000

example : MultiaryLowerBound.{0, 0} 2 :=
  multiaryLowerBound_two

example : MultiaryAverageCaseBound.{0, 0} 2 :=
  multiaryAverageCaseBound_two

example : ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop,
    ∀ (σ : Signature.{0}) (I : Interpretation σ Bool) (Acc : Set Bool) (C : Circuit σ n 1),
      C.FanInAtMost 2 → (C.multiarySize : ℝ) ≤ 2787 / 1000 * n →
        |correlation {x | hardForm n x} {x | C.eval I x 0 ∈ Acc}| ≤ (2 : ℝ) ^ (-γ * n) :=
  exists_eventually_abs_correlation_hardForm_le_2787_multiarySize

end CslibFrontierTests.FrontierMultiarySumset
