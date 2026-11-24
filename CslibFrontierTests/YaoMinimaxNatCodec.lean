/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Computability.Communication.NOF.Randomized
import CslibFrontier.Computability.CellProbe.Randomized
import CslibFrontier.Computability.Complexity.NatCodec
import CslibFrontier.Computability.Complexity.Problems.DominatingSet
import CslibFrontier.Computability.Complexity.Problems.ThreeSAT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import CslibFrontier.Computability.QueryComplexity.Yao
import CslibFrontier.Computability.RandomizedCost
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal

/-!
# Tests for `RandomizedCost` Yao minimax and `NatCodec`

Concrete `module`-surface checks for:
* `Cslib.RandomizedCost`: Yao minimax on both `PMF` and `StdSimplex`, and expected-cost coin fixing;
* `Cslib.Communication.NOF`: hard Yao minimax and majority error amplification on a concrete
  3-player finite promise relation;
* `Cslib.Complexity.NatCodec`: exact `decode?` partial inversion, `sum`/`finSum` range disjointness,
  sharp `Nat.size_pair_le` bounds, and `Decoder`- and `Inhabited`-free `ComputableInPolyTime` via
  `fun_prop`.
-/

public section

namespace CslibFrontierTests.YaoMinimaxNatCodec

open scoped ENNReal NNReal
open Convexity Cslib Cslib.Communication Cslib.Complexity Probability Turing.MultiTapeTM

/-! ### Concrete 3-player NOF promise relation: hard Yao minimax and amplification -/

/-- Constant 3-player inputs: all three foreheads carry `false`, or all three carry `true`. -/
def constPromise : Set (Fin 3 → Bool) :=
  Set.range fun b : Bool => fun _ : Fin 3 => b

instance : Finite constPromise :=
  Set.finite_range _

/-- Output the common forehead bit on `constPromise`. -/
def commonBitRel (x : Fin 3 → Bool) (z : Bool) : Prop :=
  x 0 = z

/-- Player `1` sees player `0`'s forehead (`0 ≠ 1`) and announces it in 1 bit. -/
private def announceZero : NOF.Protocol (fun _ : Fin 3 => Bool) Bool :=
  .speak 1 (fun v => v ⟨0, by decide⟩) (.output false) (.output true)

private theorem announceZero_solves : announceZero.Solves commonBitRel constPromise := by
  rintro x ⟨b, rfl⟩
  cases b <;> rfl

private theorem announceZero_depth : announceZero.depth = 1 := by
  simp [announceZero]

/-- Any depth-0 NOF protocol outputs a fixed bit independent of the foreheads, so it errs with
probability `1 / 2` under the uniform distribution on `constPromise`. -/
private theorem depth_pos_of_distributionalError_le
    {p : NOF.Protocol (fun _ : Fin 3 => Bool) Bool}
    (hp : p.distributionalError
      ((PMF.uniformOfFintype Bool).map fun b : Bool => fun _ : Fin 3 => b)
      commonBitRel ≤ 1 / 4) :
    1 ≤ (p.depth : ℕ∞) := by
  by_contra hlt
  have hd0 : p.depth = 0 := by
    revert hlt
    cases p.depth <;> simp
  have hconst : ∃ z₀, ∀ x, p.run x = z₀ := by
    cases p with
    | output z₀ => exact ⟨z₀, fun _ => rfl⟩
    | speak i f p₀ p₁ => simp [NOF.Protocol.depth] at hd0
  obtain ⟨z₀, hz₀⟩ := hconst
  have herr : p.distributionalError
      ((PMF.uniformOfFintype Bool).map fun b : Bool => fun _ : Fin 3 => b)
      commonBitRel = 1 / 2 := by
    rw [NOF.Protocol.distributionalError, Probability.PMF.errorProb, PMF.toOuterMeasure_map_apply,
      Probability.PMF.toOuterMeasure_apply_toReal]
    simp only [Fintype.sum_bool, Set.preimage_ofPred_eq, commonBitRel, hz₀, Set.mem_ofPred_eq,
      PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat, ENNReal.toReal_inv,
      ENNReal.toReal_ofNat]
    cases z₀ <;> norm_num
  linarith

/-- Hard Yao on the finite 3-player promise set `constPromise`: proving distributional complexity
`≤ 1` against every promise distribution yields `ecomplexity ≤ 1`, and matching the uniform
promise distribution gives exact equality `= 1` for both `ecomplexity` and the Yao supremum. -/
theorem nof_constPromise_yao :
    NOF.PublicCoin.ecomplexity (1 / 4) commonBitRel constPromise = 1 ∧
      (⨆ (ν : PMF (Fin 3 → Bool)) (_ : ∀ x ∈ ν.support, x ∈ constPromise),
        NOF.Protocol.distributionalComplexity (1 / 4) commonBitRel ν) = 1 := by
  have hle : NOF.PublicCoin.ecomplexity (1 / 4) commonBitRel constPromise ≤ (1 : ℕ) := by
    refine NOF.PublicCoin.ecomplexity_le_of_forall_distributionalComplexity_le fun ν hν => ?_
    have herr : announceZero.distributionalError ν commonBitRel ≤ 1 / 4 := by
      have hpure := NOF.PublicCoin.solves_pure announceZero_solves (by norm_num : (0 : ℝ) ≤ 1 / 4)
      obtain ⟨q, hq, hqerr⟩ := hpure.exists_distributionalError_le ν hν
      obtain rfl := (PMF.mem_support_pure_iff announceZero q).mp hq
      exact hqerr
    exact (NOF.Protocol.distributionalComplexity_le_depth herr).trans
      (by simp [announceZero_depth])
  let ν₀ : PMF (Fin 3 → Bool) := (PMF.uniformOfFintype Bool).map fun b : Bool => fun _ : Fin 3 => b
  have hν₀ : ∀ x ∈ ν₀.support, x ∈ constPromise := by
    intro x hx
    rcases (PMF.mem_support_map_iff _ _ _).mp hx with ⟨b, -, rfl⟩
    exact ⟨b, rfl⟩
  have hge : (1 : ℕ∞) ≤ NOF.PublicCoin.ecomplexity (1 / 4) commonBitRel constPromise := by
    refine le_trans ?_ (NOF.PublicCoin.distributionalComplexity_le_ecomplexity hν₀)
    exact NOF.Protocol.le_distributionalComplexity_iff.mpr fun _ hp =>
      depth_pos_of_distributionalError_le hp
  have heq : NOF.PublicCoin.ecomplexity (1 / 4) commonBitRel constPromise = 1 :=
    le_antisymm hle hge
  exact ⟨heq, (NOF.PublicCoin.ecomplexity_eq_iSup_distributionalComplexity).symm.trans heq⟩

-- Concrete NOF majority amplification: 4 (= 2 * 2) independent runs of a 1-bit protocol solving
-- with error `1 / 3` amplify error down to `(4 * (1 / 3) * (1 - 1 / 3)) ^ 2 = 64 / 81` at depth
-- at most `4`.
example (μ : NOF.PublicCoin (fun _ : Fin 3 => Bool) Bool)
    (hμ : μ.Solves (1 / 3) (fun x b => x 0 = b) constPromise) (hd : μ.depth ≤ (1 : ℕ)) :
    (μ.amplify 2).Solves (64 / 81) (fun x b => x 0 = b) constPromise ∧
      (μ.amplify 2).depth ≤ (4 : ℕ) := by
  have hsol := hμ.amplify (by norm_num : (1 / 3 : ℝ) ≤ 1 / 2) 2
  have hnum : ((4 * (1 / 3 : ℝ) * (1 - 1 / 3)) ^ 2 : ℝ) = 64 / 81 := by norm_num
  rw [hnum] at hsol
  refine ⟨hsol, ?_⟩
  exact (NOF.PublicCoin.depth_amplify_le hd 2).trans (by decide)

/-! ### Model-generic `RandomizedCost`: `StdSimplex` Yao minimax and coin fixing -/

/-- Toy model on `Bool`: machine `false` guesses `false` at cost `0`; machine `true` reads the input
at cost `1`. -/
private def toyModel : RandomizedCost Bool Bool Bool where
  eval m x := if m then x else false
  cost m := if m then 1 else 0

-- On `StdSimplex`, Yao minimax equates randomized complexity at error `1 / 4` with the supremum
-- of distributional complexities, and both equal `1`.
example :
    toyModel.simplexComplexity (1 / 4) (fun x z => z = x) = 1 ∧
      (⨆ ν : StdSimplex ℝ Bool,
        toyModel.simplexDistributionalComplexity (1 / 4) ν (fun x z => z = x)) = 1 := by
  have hex : ∃ m : Bool, ∀ x : Bool, toyModel.eval m x = x := ⟨true, fun _ => rfl⟩
  have hub : toyModel.simplexComplexity (1 / 4) (fun x z => z = x) ≤ 1 := by
    refine (toyModel.simplexComplexity_le_maxCost (μ := StdSimplex.single true) fun x => ?_).trans
      (by simp [toyModel])
    rw [StdSimplex.errorProb_single_of_pos (Acc := fun m => toyModel.eval m x = x) rfl]
    exact NNReal.coe_nonneg _
  let hard : StdSimplex ℝ Bool := StdSimplex.single true
  have hlb : 1 ≤ toyModel.simplexComplexity (1 / 4) (fun x z => z = x) := by
    refine le_trans ?_ (toyModel.simplexDistributionalComplexity_le_simplexComplexity hard hex)
    obtain ⟨m, herr, hm⟩ :=
      toyModel.exists_simplexDistributionalComplexity_eq
        (R := fun x z => z = x) (ε := 1 / 4) hard hex
    rw [← hm]
    cases m with
    | true => simp [toyModel]
    | false =>
      exfalso
      rw [StdSimplex.errorProb_single_of_neg (Acc := fun x => toyModel.eval false x = x)
        (by simp [toyModel])] at herr
      norm_num [NNReal.coe_div] at herr
  have heq : toyModel.simplexComplexity (1 / 4) (fun x z => z = x) = 1 :=
    le_antisymm hub hlb
  exact ⟨heq, (toyModel.simplexComplexity_eq_iSup_simplexDistributionalComplexity hex).symm.trans
    heq⟩

-- Zero-error expected-cost coin fixing extracts a concrete deterministic solver from `μ.support`
-- meeting the worst-case expected cost bound against any input distribution `ν`.
example (ν : PMF Bool) :
    ∃ m ∈ (PMF.pure true : PMF Bool).support,
      (∀ x ∈ (Set.univ : Set Bool), toyModel.eval m x = x) ∧
        (∑' x, ν x * ((if m then 1 else 0 : ℕ) : ℝ≥0∞)) ≤ 1 := by
  refine RandomizedCost.exists_mem_support_tsum_mul_le_of_coinFixing
    (PMF.pure true) ν (fun x => (PMF.pure true).bind fun m =>
      PMF.pure (toyModel.eval m x, if m then 1 else 0))
    toyModel.eval (fun m _ => if m then 1 else 0) Set.univ (fun x y => y = x)
    (fun x _ y hy => ?_) (fun _ _ => rfl) (fun _ _ => rfl) (fun x _ => ?_)
  · simp only [PMF.pure_map, PMF.pure_bind, PMF.mem_support_pure_iff, toyModel, ↓reduceIte] at hy
    exact hy
  · rw [RandomizedCost.tsum_snd_eq_of_bind_pure (PMF.pure true) (fun m => toyModel.eval m x)
      (fun m => if m then 1 else 0) rfl, tsum_eq_single true]
    · simp
    · intro m hm
      simp [PMF.pure_apply, hm]

/-! ### `NatCodec`: exact partial inversion, disjoint ranges, bit-length bounds, and `fun_prop` -/

private def demoCodec : NatCodec (Fin 2 ⊕ (ℕ × ℕ)) :=
  (NatCodec.nat.pair .nat).finSum 2

-- Exact round-trip and out-of-range rejection on `fin`, `finSum`, `sum`, and `pair`.
example :
    demoCodec (.inl 0) = 0 ∧
      demoCodec (.inl 1) = 1 ∧
      demoCodec (.inr (2, 1)) = 9 ∧
      demoCodec.decode? 0 = some (.inl 0) ∧
      demoCodec.decode? 9 = some (.inr (2, 1)) ∧
      (NatCodec.fin 2).decode? 3 = none ∧
      ((NatCodec.fin 2).sum (NatCodec.fin 2)).decode? 5 = none ∧
      ((NatCodec.fin 2).pair (NatCodec.fin 2)).decode? 8 = none := by
  refine ⟨by decide, by decide, by decide, by decide, demoCodec.decode?_eq_some_iff.mpr (by decide),
    by decide, by decide, ((NatCodec.fin 2).pair (NatCodec.fin 2)).decode?_eq_none_iff.mpr ?_⟩
  rintro ⟨p, h⟩
  revert p h
  decide

-- Range disjointness for `finSum` and `sum`, and concrete non-collision in `VertexCover`.
example :
    Disjoint (Set.range fun i : Fin 2 => demoCodec (.inl i))
      (Set.range fun p : ℕ × ℕ => demoCodec (.inr p)) ∧
    Disjoint (Set.range fun v : ℕ => splitVarCodec (.inl v))
      (Set.range fun p : ℕ × ℕ => splitVarCodec (.inr p)) ∧
    VertexCover.vertexCodec (.inr (.inl 0)) = 1 ∧
    VertexCover.vertexCodec (.inr (.inl 1)) = 3 ∧
    VertexCover.edgeVertex (0, 1) = 7 :=
  ⟨NatCodec.disjoint_range_finSum 2 _, NatCodec.disjoint_range_sum _ _,
    by decide, by decide, by decide⟩

-- Sharpness of `Nat.size_pair_le`: `(3 : ℕ).size = 2` and `(Nat.pair 3 3).size = 4 = 2 * 2`,
-- plus concrete `size_sum_le` and `size_finSum_le` bounds.
example :
    (Nat.pair 3 3).size = 4 ∧
      2 * max (3 : ℕ).size (3 : ℕ).size = 4 ∧
      ∀ x : Fin 2 ⊕ (ℕ × ℕ),
        (demoCodec x).size ≤
          Sum.elim (fun _ => (2 : ℕ).size)
            (fun p => max (2 * max p.1.size p.2.size) (2 : ℕ).size + 1) x := by
  refine ⟨by decide, by decide, fun x => (NatCodec.size_finSum_le 2 _ x).trans ?_⟩
  cases x with
  | inl _ => exact le_rfl
  | inr p =>
    simp only [Sum.elim_inr]
    exact Nat.add_le_add_right (max_le_max_right _ (NatCodec.size_pair_le _ _ p)) 1

-- `ComputableInPolyTime` via `by fun_prop` across nested `sum`/`finSum`/`pair`/`nat_unary`,
-- and `ComputableInPolyTime.sumElim` on an infinite summand `OpaqueIdx` with neither `Inhabited`,
-- `Finite`, nor `Decoder` instances, plus an uninhabited summand `Empty ⊕ ℕ`.
private def encFin2 : Fin 2 ↪ List Bool :=
  (NatCodec.fin 2).toEmbedding.trans encNat

private structure OpaqueIdx where
  raw : ℕ

private def encOpaqueIdx : OpaqueIdx ↪ List Bool where
  toFun x := encNat x.raw
  inj' a b h := by
    cases a
    cases b
    exact congrArg OpaqueIdx.mk (encNat.injective h)

private theorem computableInPolyTime_opaqueRaw :
    ComputableInPolyTime OpaqueIdx.raw encOpaqueIdx encNat :=
  ComputableInPolyTime.of_eq fun _ => rfl

private def encEmpty : Empty ↪ List Bool :=
  ⟨Empty.elim, fun a => Empty.elim a⟩

example :
    ComputableInPolyTime
      (fun x : ℕ ⊕ (Fin 2 ⊕ (ℕ × ℕ)) =>
        (NatCodec.nat.sum ((NatCodec.nat.pair .nat).finSum 2)) x)
      (encSum encNat (encSum encFin2 (encPair encUnary encNat))) encNat := by
  fun_prop

example :
    ComputableInPolyTime
      (Sum.elim (fun x : OpaqueIdx => 2 * x.raw) (fun n : ℕ => 2 * n + 1))
      (encSum encOpaqueIdx encUnary) encNat :=
  ComputableInPolyTime.sumElim
    (have := computableInPolyTime_opaqueRaw; by fun_prop) (by fun_prop)

example :
    ComputableInPolyTime
      (Sum.elim (fun e : Empty => Empty.elim e) (fun n : ℕ => 2 * n + 1))
      (encSum encEmpty encUnary) encNat :=
  ComputableInPolyTime.sumElim (ComputableInPolyTime.of_finite _) (by fun_prop)

end CslibFrontierTests.YaoMinimaxNatCodec
