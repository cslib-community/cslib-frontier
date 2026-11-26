/-
Copyright (c) 2026 Samuel Schlesinger, Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game
public import Mathlib.LinearAlgebra.Matrix.Rank
public import CslibFrontier.Languages.Probabilistic.Oracle.Run
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
public import Mathlib.Algebra.Field.ZMod
import CslibFrontier.Foundations.LinearAlgebra.Matrix.LeftKernel
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Algebra.CharP.Two

/-!
# FAEST v3 CRT witness-reuse hazard and witness-order repair for VOLE-ACT

This module formalizes the linear-algebraic parity leakage arising when FAEST-style CRT VOLE masks
reuse the first `lam` bits of a prover's witness as Free-XOR garbled-circuit label offsets,
together with the Issue-to-Spend and Spend-prefix unlinkability breaks under draft witness
ordering and the witness-order repair that places fresh uniform opening randomness first.

In `[VOLEACT2026]` (Protocol Specification / Initial Issuance and Spending), the Issuance witness
is listed as `(nf, r)` and the Spend witness as `(t, r, x, s, nf', t', r')`, without mandating
witness byte offsets or addressing CRT mask reuse (`[VOLEACT2026]` `#proof-status` leaves the
unlinkability proof open). When FAEST-style CRT VOLE masks (`[BaumEtAl2026FAEST]`, §§3.1–3.3 pp.
13–18, §6 pp. 35–43 / Figs. 6.1–6.3, and §10.10 Games `G6`–`G11` pp. 115–121 as background) reuse
the first `lam` witness bits as Free-XOR garbled-circuit label offsets, an `H5`-style garbling mask
check compressing `nMult` gate tables across `nMask` masks introduces an
`F : Matrix (Fin nMult) (Fin lam) (ZMod 2)` linear map. Whenever `F.rank < nMult` (in particular
whenever `lam < nMult`), `Fᵀ` has a nontrivial kernel of dimension at least `nMult - lam`, exposing
linear parity equations satisfied identically by any valid witness prefix and rejecting independent
random guesses with probability `(2 : ℝ≥0∞)⁻¹ ^ (nMask * r)` across `r` independent parity checks
(for example, `nMult = 312`, `lam = 128`, `nMask = 12`, `r = 14`, `kGates = 27` in illustrative CRT
parameters; FAEST-128s uses `nmult = 312` and `nmask = dzk + 3`).

This formalization, its matrix bounds, random-oracle `H5` distinguishers, query bounds,
unlinkability games, and witness-order repair statements are original to this library as finite,
query-bounded steps (`#7068`); asymptotic PPT certificates and concrete circuit lookup tables
are outside this module's scope. Empty/zero-width parameterizations (`nMask = 0`, `rSub = 0`, or
`nMult ≤ lam`) are admitted and degenerate to trivial `0 ≤ advantage` or `0 ≤ leftKernelDim`
bounds.

## Main definitions

* `CRTMaskTable`, `honestCRTMaskTable`, `candidateLabel`: CRT garbled mask table model and
  active/complementary Free-XOR label reconstruction from prefix guess `wStar`.
* `crtPrefixEval`, `crtPrefixTest`: deterministic evaluation and `kGates`-query `H5` parity test.
* `crtIssueSpendGame`, `crtIssueSpendAdversary`: Issue-to-Spend unlinkability break when `nf`
  occupies the CRT prefix.
* `crtSpendPrefixTest`, `packBalancePrefix`, `balancePrefixGuesses`,
  `crtSpendBalancePrefixGame`: Spend-time brute-force distinguisher over trailing randomness
  when public balance `t` enters the CRT prefix.
* `rFirstCRTMaskView`, `rFirstDecoupledView`: witness-order repair placing fresh uniform opening
  `r` in the first `lam` prefix bits.

## Main results

* `parityCheck_map_uniformOfFintype`, `parityCheck_uniform_zero_prob`,
  `multiMask_parityCheck_uniform_zero_prob`: exact uniform false-positive rates `(|K|⁻¹) ^ r` and
  `(2 : ℝ≥0∞)⁻¹ ^ (nMask * r)` (relying on generic `[Field K]` left-kernel results from
  `CslibFrontier.Foundations.LinearAlgebra.Matrix.LeftKernel`).
* `crtPrefixTest_isQueryBounded`, `crtPrefixTest_honest_true`, `crtPrefixTest_wrong_guess_prob`:
  `kGates`-query soundness and completeness of the `H5` prefix distinguisher.
* `crtIssueSpendAdversary_isQueryBounded`, `crtIssueSpendAdversary_advantage_ge`: Issue-to-Spend
  unlinkability break when `nf` sits in the CRT prefix (accounting for the `d₀ = nf₁` collision).
* `crtSpendPrefixTest_isQueryBounded`, `crtSpendPrefixTest_correct`,
  `crtSpendPrefixTest_wrong_t_le`, `crtSpendBalancePrefix_advantage_ge`: Spend-time `(t, r_lo)`
  brute-force distinguishing bound.
* `rFirstCRTMaskView_eq_decoupled`, `rFirstCRTMaskView_eq`, `rFirst_breaks_witnessKnowingZK`:
  placing uniform `r` first makes the `H5`-unqueried CRT view equal `rFirstDecoupledView`
  and independent of semantic metadata (`Game.advantage = 0`), while a witness-knowing
  distinguisher given `r` still distinguishes real tables from uniform ones.

## References

* [*VOLE-ACT*][VOLEACT2026], Protocol Specification / Initial Issuance (`#issuance`), Spending
  (`#spending`), and Proof status (`#proof-status`).
* [C. Baum et al., *FAEST v3: Algorithm Specifications*][BaumEtAl2026FAEST], §§3.1–3.3 (pp. 13–18),
  §6 (pp. 35–43, Figs. 6.1–6.3), and §10.10 (pp. 115–121) for CRT VOLE masks and Free-XOR label
  derivation.
-/

public section

namespace Cslib.Crypto.AnonymousToken.CRTHazard

open Probability
open Probability.PMF (uniformOfFintype uniformOfFintype_apply uniformOfFintype_bind_equiv
  uniformOfFintype_map_equiv uniformOfFintype_pi_map_comp_embedding uniformOfFintype_prod_map_snd)
open scoped Matrix ENNReal NNReal

/-! ### Uniform parity rejection over surjective parity-check matrices -/

section UniformParity

variable {K : Type*} [Field K] {m r : ℕ} [Fintype K]

/-- Decomposition `(Fin m → K) ≃ ker H.mulVecLin × (Fin r → K)` from surjectivity of `H`. -/
private noncomputable def kernelSliceEquiv {H : Matrix (Fin r) (Fin m) K}
    (hsurj : Function.Surjective H.mulVecLin) :
    (Fin m → K) ≃ (LinearMap.ker H.mulVecLin) × (Fin r → K) :=
  let sec : (Fin r → K) → (Fin m → K) := fun z => Classical.choose (hsurj z)
  have hsec : ∀ z, H *ᵥ (sec z) = z := fun z => Classical.choose_spec (hsurj z)
  { toFun := fun y =>
      (⟨y - sec (H *ᵥ y), by
        change H.mulVecLin (y - sec (H *ᵥ y)) = 0
        rw [map_sub]
        change H *ᵥ y - H *ᵥ sec (H *ᵥ y) = 0
        rw [hsec, sub_self]⟩, H *ᵥ y)
    invFun := fun p => p.1.val + sec p.2
    left_inv := fun y => sub_add_cancel _ _
    right_inv := fun p => by
      have hp : H *ᵥ (p.1.val + sec p.2) = p.2 := by
        change H.mulVecLin (p.1.val + sec p.2) = p.2
        rw [map_add, (LinearMap.mem_ker.mp p.1.property), zero_add]
        exact hsec p.2
      apply Prod.ext
      · apply Subtype.ext
        change (p.1.val + sec p.2) - sec (H *ᵥ (p.1.val + sec p.2)) = p.1.val
        rw [hp, add_sub_cancel_right]
      · exact hp }

/-- Pushing a uniform input vector through a surjective matrix gives the uniform output law. -/
theorem parityCheck_map_uniformOfFintype {H : Matrix (Fin r) (Fin m) K}
    (hsurj : Function.Surjective H.mulVecLin) :
    (uniformOfFintype (Fin m → K)).map H.mulVec = uniformOfFintype (Fin r → K) := by
  classical
  have : Fintype ↥H.mulVecLin.ker := Fintype.ofFinite _
  let e := kernelSliceEquiv hsurj
  have hcomp : H.mulVec = Prod.snd ∘ e := rfl
  rw [hcomp, ← _root_.PMF.map_comp, uniformOfFintype_map_equiv e]
  exact uniformOfFintype_prod_map_snd

/-- Pushing `nMask` i.i.d. uniform vectors through a surjective matrix gives `nMask` i.i.d.
uniform syndromes. -/
theorem multiMask_parityCheck_map_uniformOfFintype {nMask : ℕ}
    {H : Matrix (Fin r) (Fin m) K} (hsurj : Function.Surjective H.mulVecLin) :
    (uniformOfFintype (Fin nMask → Fin m → K)).map (fun y mask => H *ᵥ y mask) =
      uniformOfFintype (Fin nMask → Fin r → K) := by
  classical
  have : Fintype ↥H.mulVecLin.ker := Fintype.ofFinite _
  let e := kernelSliceEquiv hsurj
  let ePi : (Fin nMask → Fin m → K) ≃
      (Fin nMask → LinearMap.ker H.mulVecLin) × (Fin nMask → Fin r → K) :=
    { toFun := fun y => (fun mask => (e (y mask)).1, fun mask => (e (y mask)).2)
      invFun := fun p mask => e.symm (p.1 mask, p.2 mask)
      left_inv := fun y => funext fun mask => e.left_inv (y mask)
      right_inv := fun p => Prod.ext
        (funext fun mask => congrArg Prod.fst (e.right_inv (p.1 mask, p.2 mask)))
        (funext fun mask => congrArg Prod.snd (e.right_inv (p.1 mask, p.2 mask))) }
  have hcomp : (fun (y : Fin nMask → Fin m → K) mask => H *ᵥ y mask) = Prod.snd ∘ ePi := rfl
  rw [hcomp, ← _root_.PMF.map_comp, uniformOfFintype_map_equiv ePi]
  exact uniformOfFintype_prod_map_snd

variable [DecidableEq K]

/-- A uniform vector passes `r` independent parity checks with probability `(|K|⁻¹) ^ r`. -/
theorem parityCheck_uniform_zero_prob {H : Matrix (Fin r) (Fin m) K}
    (hsurj : Function.Surjective H.mulVecLin) :
    ((uniformOfFintype (Fin m → K)).map (fun y => decide (H *ᵥ y = 0))) true =
      ((Fintype.card K : ℝ≥0∞)⁻¹) ^ r := by
  have hmap : (fun y : Fin m → K => decide (H *ᵥ y = 0)) =
      (fun z : Fin r → K => decide (z = 0)) ∘ H.mulVec := rfl
  rw [hmap, ← _root_.PMF.map_comp, parityCheck_map_uniformOfFintype hsurj, _root_.PMF.map_apply]
  rw [tsum_eq_single (0 : Fin r → K)]
  · simp [uniformOfFintype_apply, ENNReal.inv_pow]
  · intro z hz
    simp [hz]

/-- Across `nMask` i.i.d. uniform vectors over `ZMod 2`, all `nMask * r` parity checks pass
simultaneously with probability `2⁻¹ ^ (nMask * r)`. -/
theorem multiMask_parityCheck_uniform_zero_prob {nMask : ℕ}
    {H : Matrix (Fin r) (Fin m) (ZMod 2)} (hsurj : Function.Surjective H.mulVecLin) :
    ((uniformOfFintype (Fin nMask → Fin m → ZMod 2)).map
        (fun y => decide (∀ mask, H *ᵥ y mask = 0))) true =
      (2 : ℝ≥0∞)⁻¹ ^ (nMask * r) := by
  have hmap : (fun y : Fin nMask → Fin m → ZMod 2 => decide (∀ mask, H *ᵥ y mask = 0)) =
      (fun z : Fin nMask → Fin r → ZMod 2 => decide (z = 0)) ∘ (fun y mask => H *ᵥ y mask) := by
    funext y
    simp [funext_iff]
  rw [hmap, ← _root_.PMF.map_comp, multiMask_parityCheck_map_uniformOfFintype hsurj,
    _root_.PMF.map_apply]
  rw [tsum_eq_single (0 : Fin nMask → Fin r → ZMod 2)]
  · simp [uniformOfFintype_apply, ZMod.card, ENNReal.inv_pow, ← pow_mul, mul_comm]
  · intro z hz
    simp [hz]

end UniformParity

/-! ### CRT garbled mask tables and query-bounded `H5` distinguishers -/

section CRTTables

/-- Query record for the `H5` random oracle `(iv, gate, label) ↦ maskBits`. -/
structure H5Query (IV : Type) (nMult lam : ℕ) where
  /-- Per-proof initialization vector `iv`. -/
  iv : IV
  /-- CRT multiplication gate index `e`. -/
  gate : Fin nMult
  /-- Candidate Free-XOR wire label `L`. -/
  label : Fin lam → ZMod 2
  deriving DecidableEq

/-- Equivalence between `H5Query` and its flat tuple, for `Fintype` enumeration. -/
def H5Query.equivProd (IV : Type) (nMult lam : ℕ) :
    H5Query IV nMult lam ≃ IV × Fin nMult × (Fin lam → ZMod 2) where
  toFun q := (q.iv, q.gate, q.label)
  invFun | (iv, gate, label) => ⟨iv, gate, label⟩
  left_inv _ := rfl
  right_inv | (_, _, _) => rfl

instance (IV : Type) [Fintype IV] (nMult lam : ℕ) : Fintype (H5Query IV nMult lam) :=
  Fintype.ofEquiv _ (H5Query.equivProd IV nMult lam).symm

/-- Oracle specification for `H5`. -/
abbrev H5Spec (IV : Type) (nMult lam nMask : ℕ) :
    OracleSpec (H5Query IV nMult lam) :=
  fun _ => Fin nMask → ZMod 2

/-- A CRT garbled mask table generated under witness prefix `wPrefix`. -/
structure CRTMaskTable (IV : Type) (nMult lam nMask : ℕ) where
  /-- Per-proof initialization vector `iv`. -/
  iv : IV
  /-- Verifier-reconstructed active Free-XOR label `L'_e` for each gate `e`. -/
  activeLabel : Fin nMult → (Fin lam → ZMod 2)
  /-- Prefix correction string `d[0..lam) = w[0..lam) ⊕ u[0..lam)`. -/
  dPrefix : Fin lam → ZMod 2
  /-- Encrypted CRT multiplication-mask rows `cmult[m, e]`. -/
  cmult : Fin nMask → Fin nMult → ZMod 2

/-- Construct an honest CRT mask table from zero-labels `L0`, offset `uPrefix`, witness prefix
`wPrefix`, active gate bits `active`, CRT gate matrix `F`, mask inputs `maskInput`, and `H5`. -/
def honestCRTMaskTable {IV : Type} {nMult lam nMask : ℕ}
    (iv : IV) (L0 : Fin nMult → (Fin lam → ZMod 2))
    (uPrefix wPrefix : Fin lam → ZMod 2) (active : Fin nMult → Bool)
    (F : Matrix (Fin nMult) (Fin lam) (ZMod 2))
    (maskInput : Fin nMask → (Fin lam → ZMod 2))
    (h5 : H5Query IV nMult lam → Fin nMask → ZMod 2) :
    CRTMaskTable IV nMult lam nMask where
  iv := iv
  activeLabel := fun e => if active e then L0 e + uPrefix else L0 e
  dPrefix := wPrefix + uPrefix
  cmult := fun mask e =>
    h5 ⟨iv, e, L0 e⟩ mask + h5 ⟨iv, e, L0 e + uPrefix⟩ mask + (F *ᵥ maskInput mask) e

/-- Candidate complementary Free-XOR label derived from `tbl` and prefix guess `wStar`. -/
def candidateLabel {IV : Type} {nMult lam nMask : ℕ}
    (tbl : CRTMaskTable IV nMult lam nMask) (wStar : Fin lam → ZMod 2)
    (e : Fin nMult) : Fin lam → ZMod 2 :=
  tbl.activeLabel e + tbl.dPrefix + wStar

private theorem zmod2_vec_add_self {lam : ℕ} (x : Fin lam → ZMod 2) : x + x = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (x i)

private theorem zmod2_vec_add_cancel_right {lam : ℕ} (x y : Fin lam → ZMod 2) :
    x + y + y = x := by
  rw [add_assoc, zmod2_vec_add_self, add_zero]

private theorem zmod2_vec_add_eq_zero_iff {lam : ℕ} (x y : Fin lam → ZMod 2) :
    x + y = 0 ↔ x = y := by
  constructor
  · intro h
    calc x = x + y + y := (zmod2_vec_add_cancel_right x y).symm
      _ = 0 + y := by rw [h]
      _ = y := zero_add y
  · rintro rfl
    exact zmod2_vec_add_self x

/-- For `wStar = wPrefix`, the candidate label equals the complementary label of
`honestCRTMaskTable`, so active and candidate `H5` values recover `F *ᵥ maskInput mask`
exactly. -/
theorem honestCRTMaskTable_reconstruct_true {IV : Type} {nMult lam nMask : ℕ}
    (iv : IV) (L0 : Fin nMult → (Fin lam → ZMod 2))
    (uPrefix wPrefix : Fin lam → ZMod 2) (active : Fin nMult → Bool)
    (F : Matrix (Fin nMult) (Fin lam) (ZMod 2))
    (maskInput : Fin nMask → (Fin lam → ZMod 2))
    (h5 : H5Query IV nMult lam → Fin nMask → ZMod 2) (mask : Fin nMask) (e : Fin nMult) :
    let tbl := honestCRTMaskTable iv L0 uPrefix wPrefix active F maskInput h5
    tbl.cmult mask e + h5 ⟨iv, e, tbl.activeLabel e⟩ mask +
        h5 ⟨iv, e, candidateLabel tbl wPrefix e⟩ mask =
      (F *ᵥ maskInput mask) e := by
  intro tbl
  have hcand : candidateLabel tbl wPrefix e = tbl.activeLabel e + uPrefix := by
    simp only [candidateLabel, tbl, honestCRTMaskTable]
    rw [add_comm wPrefix uPrefix, ← add_assoc, zmod2_vec_add_cancel_right]
  rw [hcand]
  have hpair : h5 ⟨iv, e, tbl.activeLabel e⟩ mask +
      h5 ⟨iv, e, tbl.activeLabel e + uPrefix⟩ mask =
      h5 ⟨iv, e, L0 e⟩ mask + h5 ⟨iv, e, L0 e + uPrefix⟩ mask := by
    cases hact : active e
    · simp [tbl, honestCRTMaskTable, hact]
    · simp only [tbl, honestCRTMaskTable, hact, ↓reduceIte, zmod2_vec_add_cancel_right]
      exact add_comm _ _
  rw [add_assoc _ (h5 _ _) (h5 _ _), hpair]
  dsimp only [tbl, honestCRTMaskTable]
  rw [add_right_comm, CharTwo.add_self_eq_zero, zero_add]

/-- Whenever a guess `wStar ≠ wPrefix` and `tbl.dPrefix + wStar ≠ 0`, its candidate label differs
from both `L0 e` and `L0 e + uPrefix` at every gate `e`. -/
theorem candidateLabel_ne_of_ne {IV : Type} {nMult lam nMask : ℕ}
    (iv : IV) (L0 : Fin nMult → (Fin lam → ZMod 2))
    (uPrefix wPrefix wStar : Fin lam → ZMod 2) (active : Fin nMult → Bool)
    (F : Matrix (Fin nMult) (Fin lam) (ZMod 2))
    (maskInput : Fin nMask → (Fin lam → ZMod 2))
    (h5 : H5Query IV nMult lam → Fin nMask → ZMod 2)
    (hne : wStar ≠ wPrefix)
    (hnonzero :
      (honestCRTMaskTable iv L0 uPrefix wPrefix active F maskInput h5).dPrefix + wStar ≠ 0)
    (e : Fin nMult) :
    let tbl := honestCRTMaskTable iv L0 uPrefix wPrefix active F maskInput h5
    candidateLabel tbl wStar e ≠ L0 e ∧ candidateLabel tbl wStar e ≠ L0 e + uPrefix := by
  intro tbl
  have hact_diff : candidateLabel tbl wStar e ≠ tbl.activeLabel e := fun heq => by
    rw [candidateLabel, add_assoc] at heq
    exact hnonzero (add_left_cancel (heq.trans (add_zero _).symm))
  have hother : candidateLabel tbl wStar e ≠ tbl.activeLabel e + uPrefix := fun heq => by
    rw [candidateLabel, add_assoc] at heq
    have hw : wPrefix + uPrefix + wStar = uPrefix := add_left_cancel heq
    rw [add_comm wPrefix uPrefix, add_assoc] at hw
    have hdiff : wPrefix + wStar = 0 := add_left_cancel (hw.trans (add_zero _).symm)
    exact hne ((zmod2_vec_add_eq_zero_iff wPrefix wStar).mp hdiff).symm
  cases hact : active e <;>
    simp only [tbl, honestCRTMaskTable, hact, Bool.false_eq_true, ↓reduceIte,
      zmod2_vec_add_cancel_right] at hact_diff hother
  · exact ⟨hact_diff, hother⟩
  · exact ⟨hother, hact_diff⟩

/-- Deterministic parity evaluation of a candidate prefix `wStar` against `kGates` subcircuit gates
given an `H5` oracle function. -/
def crtPrefixEval {IV : Type} {nMult lam nMask kGates rSub : ℕ}
    (sub : Fin kGates ↪ Fin nMult) (Hsub : Matrix (Fin rSub) (Fin kGates) (ZMod 2))
    (tbl : CRTMaskTable IV nMult lam nMask) (hActive : Fin kGates → Fin nMask → ZMod 2)
    (h5 : H5Query IV nMult lam → Fin nMask → ZMod 2) (wStar : Fin lam → ZMod 2) : Bool :=
  let cand : Fin nMask → Fin kGates → ZMod 2 := fun mask i =>
    tbl.cmult mask (sub i) + hActive i mask +
      h5 ⟨tbl.iv, sub i, candidateLabel tbl wStar (sub i)⟩ mask
  decide (∀ mask, Hsub *ᵥ cand mask = 0)

/-- Auxiliary recursion querying `H5` on the first `m` selected gates. -/
private def queryH5Prefix {IV : Type} {nMult lam : ℕ} (nMask : ℕ) {kGates : ℕ}
    (q : Fin kGates → H5Query IV nMult lam) :
    (m : ℕ) → m ≤ kGates →
      ProbOracleComp (H5Spec IV nMult lam nMask) (Fin m → Fin nMask → ZMod 2)
  | 0, _ => pure Fin.elim0
  | m + 1, hm => do
      let prev ← queryH5Prefix nMask q m (Nat.le_of_succ_le hm)
      let cur ← ProbOracleComp.query (q ⟨m, hm⟩)
      return Fin.snoc prev cur

private theorem queryH5Prefix_isQueryBounded {IV : Type} {nMult lam : ℕ} (nMask : ℕ) {kGates : ℕ}
    (q : Fin kGates → H5Query IV nMult lam) :
    ∀ (m : ℕ) (hm : m ≤ kGates), (queryH5Prefix nMask q m hm).IsQueryBounded m
  | 0, _ => by simpa [queryH5Prefix] using OracleComp.IsCostBounded.pure Fin.elim0 0
  | m + 1, hm => by
      have ih := queryH5Prefix_isQueryBounded nMask q m (Nat.le_of_succ_le hm)
      have hq : (ProbOracleComp.query (spec := H5Spec IV nMult lam nMask)
          (q ⟨m, hm⟩)).IsQueryBounded 1 := ProbOracleComp.isCostBounded_query _ _
      dsimp only [queryH5Prefix]
      exact ih.bind fun prev => hq.bind fun cur =>
        OracleComp.IsCostBounded.pure (Fin.snoc (α := fun _ => Fin nMask → ZMod 2) prev cur) 0

private theorem queryH5Prefix_run {IV : Type} {nMult lam nMask kGates : ℕ}
    (q : Fin kGates → H5Query IV nMult lam) (h5 : H5Query IV nMult lam → Fin nMask → ZMod 2) :
    ∀ (m : ℕ) (hm : m ≤ kGates),
      (queryH5Prefix nMask q m hm).run (fun x => pure (h5 x)) =
        pure fun i : Fin m => h5 (q ⟨i.val, lt_of_lt_of_le i.isLt hm⟩)
  | 0, _ => by
      simp only [queryH5Prefix, ProbOracleComp.run_pure]
      congr 1
      ext i
      exact i.elim0
  | m + 1, hm => by
      simp only [queryH5Prefix, ProbOracleComp.run_bind,
        queryH5Prefix_run q h5 m (Nat.le_of_succ_le hm),
        ProbOracleComp.run_query, ProbOracleComp.run_pure, pure_bind]
      congr 1
      funext i
      cases i using Fin.lastCases with
      | last => simp
      | cast j => simp

/-- The `kGates`-query `H5` prefix distinguisher: queries `H5` on each gate `sub i` with
candidate label `candidateLabel tbl wStar (sub i)` and checks all `nMask * rSub` parities. -/
def crtPrefixTest {IV : Type} {nMult lam nMask kGates rSub : ℕ}
    (sub : Fin kGates ↪ Fin nMult) (Hsub : Matrix (Fin rSub) (Fin kGates) (ZMod 2))
    (tbl : CRTMaskTable IV nMult lam nMask) (hActive : Fin kGates → Fin nMask → ZMod 2)
    (wStar : Fin lam → ZMod 2) : ProbOracleComp (H5Spec IV nMult lam nMask) Bool := do
  let hStars ← queryH5Prefix nMask (fun i => ⟨tbl.iv, sub i, candidateLabel tbl wStar (sub i)⟩)
    kGates le_rfl
  let cand : Fin nMask → Fin kGates → ZMod 2 := fun mask i =>
    tbl.cmult mask (sub i) + hActive i mask + hStars i mask
  return decide (∀ mask, Hsub *ᵥ cand mask = 0)

/-- `crtPrefixTest` makes at most `kGates` queries to `H5`. -/
theorem crtPrefixTest_isQueryBounded {IV : Type} {nMult lam nMask kGates rSub : ℕ}
    (sub : Fin kGates ↪ Fin nMult) (Hsub : Matrix (Fin rSub) (Fin kGates) (ZMod 2))
    (tbl : CRTMaskTable IV nMult lam nMask) (hActive : Fin kGates → Fin nMask → ZMod 2)
    (wStar : Fin lam → ZMod 2) :
    (crtPrefixTest sub Hsub tbl hActive wStar).IsQueryBounded kGates := by
  dsimp only [crtPrefixTest]
  exact (queryH5Prefix_isQueryBounded nMask _ kGates le_rfl).bind fun _ =>
    OracleComp.IsCostBounded.pure _ 0

/-- Deterministic execution of `crtPrefixTest` against `h5` computes `crtPrefixEval`. -/
theorem crtPrefixTest_run {IV : Type} {nMult lam nMask kGates rSub : ℕ}
    (sub : Fin kGates ↪ Fin nMult) (Hsub : Matrix (Fin rSub) (Fin kGates) (ZMod 2))
    (tbl : CRTMaskTable IV nMult lam nMask) (hActive : Fin kGates → Fin nMask → ZMod 2)
    (h5 : H5Query IV nMult lam → Fin nMask → ZMod 2) (wStar : Fin lam → ZMod 2) :
    (crtPrefixTest sub Hsub tbl hActive wStar).run (fun q => pure (h5 q)) =
      pure (crtPrefixEval sub Hsub tbl hActive h5 wStar) := by
  simp only [crtPrefixTest, crtPrefixEval, ProbOracleComp.run_bind, queryH5Prefix_run,
    ProbOracleComp.run_pure, pure_bind]

/-- Completeness: on the true witness prefix `wPrefix`, `crtPrefixTest` accepts with probability
`1` under any `H5` function provided `Hsub` annihilates `F.submatrix sub id`. -/
theorem crtPrefixTest_honest_true {IV : Type} {nMult lam nMask kGates rSub : ℕ}
    (sub : Fin kGates ↪ Fin nMult) (Hsub : Matrix (Fin rSub) (Fin kGates) (ZMod 2))
    (F : Matrix (Fin nMult) (Fin lam) (ZMod 2))
    (hHF : Hsub * F.submatrix sub id = 0)
    (iv : IV) (L0 : Fin nMult → (Fin lam → ZMod 2))
    (uPrefix wPrefix : Fin lam → ZMod 2) (active : Fin nMult → Bool)
    (maskInput : Fin nMask → (Fin lam → ZMod 2))
    (h5 : H5Query IV nMult lam → Fin nMask → ZMod 2) :
    let tbl := honestCRTMaskTable iv L0 uPrefix wPrefix active F maskInput h5
    let hActive : Fin kGates → Fin nMask → ZMod 2 :=
      fun i => h5 ⟨iv, sub i, tbl.activeLabel (sub i)⟩
    ProbComp.eval ((crtPrefixTest sub Hsub tbl hActive wPrefix).run (fun q => pure (h5 q))) =
      PMF.pure true := by
  intro tbl hActive
  rw [crtPrefixTest_run, ProbComp.eval_pure]
  congr 1
  simp only [crtPrefixEval, decide_eq_true_eq]
  intro mask
  have hvec : (fun i : Fin kGates => tbl.cmult mask (sub i) + hActive i mask +
      h5 ⟨tbl.iv, sub i, candidateLabel tbl wPrefix (sub i)⟩ mask) =
      F.submatrix sub id *ᵥ maskInput mask := by
    funext i
    have hrec := honestCRTMaskTable_reconstruct_true iv L0 uPrefix wPrefix active F maskInput h5
      mask (sub i)
    simpa [tbl, hActive, honestCRTMaskTable, Matrix.submatrix_apply, Matrix.mulVec,
      dotProduct] using hrec
  rw [hvec]
  exact Matrix.parityCheck_mulVec_of_eq_zero hHF (maskInput mask)

/-- Helper factoring `Fin kGates ↪ H5Query IV nMult lam` for distinct `sub` gates. -/
private def gateQueryEmbedding {IV : Type} {nMult lam kGates : ℕ}
    (iv : IV) (sub : Fin kGates ↪ Fin nMult) (cand : Fin nMult → Fin lam → ZMod 2) :
    Fin kGates ↪ H5Query IV nMult lam where
  toFun i := ⟨iv, sub i, cand (sub i)⟩
  inj' i j hij := by
    have hsub : sub i = sub j := congrArg H5Query.gate hij
    exact sub.injective hsub

/-- Soundness against wrong guesses: in the uniform `H5` random-oracle model, conditioned on fixed
non-queried entries (outside the candidate labels), a wrong guess `wStar ≠ wPrefix` with
`dPrefix + wStar ≠ 0` passes all `nMask * rSub` parity checks with probability
`2⁻¹ ^ (nMask * rSub)`. -/
theorem crtPrefixTest_wrong_guess_prob {IV : Type} [Fintype IV] [DecidableEq IV]
    {nMult lam nMask kGates rSub : ℕ}
    (sub : Fin kGates ↪ Fin nMult) (Hsub : Matrix (Fin rSub) (Fin kGates) (ZMod 2))
    (hsurj : Function.Surjective Hsub.mulVecLin)
    (iv : IV) (L0 : Fin nMult → (Fin lam → ZMod 2))
    (uPrefix wPrefix wStar : Fin lam → ZMod 2) (active : Fin nMult → Bool)
    (F : Matrix (Fin nMult) (Fin lam) (ZMod 2))
    (maskInput : Fin nMask → (Fin lam → ZMod 2))
    (hne : wStar ≠ wPrefix)
    (hnonzero : wPrefix + uPrefix + wStar ≠ 0) :
    ((uniformOfFintype (H5Query IV nMult lam → Fin nMask → ZMod 2)).bind fun h5 =>
      let tbl := honestCRTMaskTable iv L0 uPrefix wPrefix active F maskInput h5
      let hActive : Fin kGates → Fin nMask → ZMod 2 :=
        fun i => h5 ⟨iv, sub i, tbl.activeLabel (sub i)⟩
      ProbComp.eval ((crtPrefixTest sub Hsub tbl hActive wStar).run (fun q => pure (h5 q))))
        true =
      (2 : ℝ≥0∞)⁻¹ ^ (nMask * rSub) := by
  classical
  let candFun : Fin nMult → Fin lam → ZMod 2 := fun e =>
    (if active e then L0 e + uPrefix else L0 e) + (wPrefix + uPrefix) + wStar
  let emb := gateQueryEmbedding iv sub candFun
  -- Split `H5` along the finite image `I = range emb` vs complement `Iᶜ`. Since neither `L0 e`,
  -- `L0 e + uPrefix`, nor `activeLabel e` lands in `I`, `tbl` and `hActive` depend only on `Iᶜ`.
  set I : Finset (H5Query IV nMult lam) :=
    Finset.univ.image (emb : Fin kGates → H5Query IV nMult lam)
  let eSplit := Equiv.piEquivPiSubtypeProd (fun q => q ∈ I)
    (fun _ : H5Query IV nMult lam => Fin nMask → ZMod 2)
  let unsplit : (∀ q : I, Fin nMask → ZMod 2) × (∀ q : {q // q ∉ I}, Fin nMask → ZMod 2) →
      H5Query IV nMult lam → Fin nMask → ZMod 2 := eSplit.symm
  have hnotMem₀ (e : Fin nMult) : (⟨iv, e, L0 e⟩ : H5Query IV nMult lam) ∉ I := by
    intro hmem
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
    obtain rfl : sub i = e := congrArg H5Query.gate hi
    exact (candidateLabel_ne_of_ne iv L0 uPrefix wPrefix wStar active F maskInput
      (fun _ _ => 0) hne hnonzero (sub i)).1 (congrArg H5Query.label hi)
  have hnotMem₁ (e : Fin nMult) : (⟨iv, e, L0 e + uPrefix⟩ : H5Query IV nMult lam) ∉ I := by
    intro hmem
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
    obtain rfl : sub i = e := congrArg H5Query.gate hi
    exact (candidateLabel_ne_of_ne iv L0 uPrefix wPrefix wStar active F maskInput
      (fun _ _ => 0) hne hnonzero (sub i)).2 (congrArg H5Query.label hi)
  have hnotMemAct (e : Fin nMult) :
      (⟨iv, e, if active e then L0 e + uPrefix else L0 e⟩ : H5Query IV nMult lam) ∉ I := by
    cases active e <;> simp [hnotMem₀, hnotMem₁]
  have hunsplit_notMem {p : (∀ q : I, Fin nMask → ZMod 2) ×
      (∀ q : {q // q ∉ I}, Fin nMask → ZMod 2)} {q : H5Query IV nMult lam} (hq : q ∉ I) :
      unsplit p q = p.2 ⟨q, hq⟩ := by
    simp [unsplit, eSplit, hq]
  have hunsplit_mem {p : (∀ q : I, Fin nMask → ZMod 2) ×
      (∀ q : {q // q ∉ I}, Fin nMask → ZMod 2)} {q : H5Query IV nMult lam} (hq : q ∈ I) :
      unsplit p q = p.1 ⟨q, hq⟩ := by
    simp [unsplit, eSplit, hq]
  have hbindSplit :
      ((uniformOfFintype (H5Query IV nMult lam → Fin nMask → ZMod 2)).bind fun h5 =>
        let tbl := honestCRTMaskTable iv L0 uPrefix wPrefix active F maskInput h5
        let hActive : Fin kGates → Fin nMask → ZMod 2 :=
          fun i => h5 ⟨iv, sub i, tbl.activeLabel (sub i)⟩
        ProbComp.eval ((crtPrefixTest sub Hsub tbl hActive wStar).run (fun q => pure (h5 q)))) =
      (uniformOfFintype ((∀ q : {q // q ∉ I}, Fin nMask → ZMod 2))).bind fun hOut =>
        (uniformOfFintype (∀ q : I, Fin nMask → ZMod 2)).bind fun hIn =>
          let h5 := unsplit (hIn, hOut)
          let tbl := honestCRTMaskTable iv L0 uPrefix wPrefix active F maskInput h5
          let hActive : Fin kGates → Fin nMask → ZMod 2 :=
            fun i => h5 ⟨iv, sub i, tbl.activeLabel (sub i)⟩
          ProbComp.eval
            ((crtPrefixTest sub Hsub tbl hActive wStar).run (fun q => pure (h5 q))) := by
    rw [← uniformOfFintype_map_equiv eSplit.symm, PMF.bind_map]
    rw [← Probability.PMF.uniformOfFintype_prod, PMF.bind_bind]
    simp_rw [PMF.bind_map, Function.comp_def]
    exact PMF.bind_comm _ _ _
  rw [hbindSplit, PMF.bind_apply]
  have hconst : ∀ hOut : ∀ q : {q // q ∉ I}, Fin nMask → ZMod 2,
      ((uniformOfFintype (∀ q : I, Fin nMask → ZMod 2)).bind fun hIn =>
        let h5 := unsplit (hIn, hOut)
        let tbl := honestCRTMaskTable iv L0 uPrefix wPrefix active F maskInput h5
        let hActive : Fin kGates → Fin nMask → ZMod 2 :=
          fun i => h5 ⟨iv, sub i, tbl.activeLabel (sub i)⟩
        ProbComp.eval ((crtPrefixTest sub Hsub tbl hActive wStar).run (fun q => pure (h5 q))))
          true =
        (2 : ℝ≥0∞)⁻¹ ^ (nMask * rSub) := by
    intro hOut
    let base : Fin nMask → Fin kGates → ZMod 2 := fun mask i =>
      hOut ⟨⟨iv, sub i, L0 (sub i)⟩, hnotMem₀ _⟩ mask +
      hOut ⟨⟨iv, sub i, L0 (sub i) + uPrefix⟩, hnotMem₁ _⟩ mask +
      (F *ᵥ maskInput mask) (sub i) +
      hOut ⟨⟨iv, sub i, if active (sub i) then L0 (sub i) + uPrefix else L0 (sub i)⟩,
        hnotMemAct _⟩ mask
    let eIdx : Fin kGates ≃ I := Equiv.ofBijective
      (fun i => ⟨emb i, Finset.mem_image_of_mem emb (Finset.mem_univ i)⟩) (by
        rw [Fintype.bijective_iff_injective_and_card, Fintype.card_coe,
          Finset.card_image_of_injective _ emb.injective, Finset.card_univ]
        exact ⟨fun _ _ h => emb.injective (congrArg Subtype.val h), rfl⟩)
    let eFlip : (∀ q : I, Fin nMask → ZMod 2) ≃ (Fin nMask → Fin kGates → ZMod 2) :=
      { toFun := fun hIn mask i => base mask i + hIn (eIdx i) mask
        invFun := fun y q => fun mask => base mask (eIdx.symm q) + y mask (eIdx.symm q)
        left_inv := fun hIn => funext fun q => funext fun mask => by
          dsimp only
          have : eIdx (eIdx.symm q) = q := eIdx.apply_symm_apply q
          rw [this, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
        right_inv := fun y => funext fun mask => funext fun i => by
          dsimp only
          have : eIdx.symm (eIdx i) = i := eIdx.symm_apply_apply i
          rw [this, ← add_assoc, CharTwo.add_self_eq_zero, zero_add] }
    have hinner : ∀ hIn : ∀ q : I, Fin nMask → ZMod 2,
        (let h5 := unsplit (hIn, hOut)
        let tbl := honestCRTMaskTable iv L0 uPrefix wPrefix active F maskInput h5
        let hActive : Fin kGates → Fin nMask → ZMod 2 :=
          fun i => h5 ⟨iv, sub i, tbl.activeLabel (sub i)⟩
        ProbComp.eval ((crtPrefixTest sub Hsub tbl hActive wStar).run (fun q => pure (h5 q)))) =
          PMF.pure (decide (∀ mask, Hsub *ᵥ eFlip hIn mask = 0)) := by
      intro hIn
      dsimp only
      rw [crtPrefixTest_run, ProbComp.eval_pure]
      have hcol : ∀ mask i,
          (honestCRTMaskTable iv L0 uPrefix wPrefix active F maskInput (unsplit (hIn, hOut))).cmult
              mask (sub i) +
            unsplit (hIn, hOut) ⟨iv, sub i,
              (honestCRTMaskTable iv L0 uPrefix wPrefix active F maskInput
                (unsplit (hIn, hOut))).activeLabel (sub i)⟩ mask +
            unsplit (hIn, hOut) ⟨(honestCRTMaskTable iv L0 uPrefix wPrefix active F maskInput
                (unsplit (hIn, hOut))).iv, sub i,
              candidateLabel (honestCRTMaskTable iv L0 uPrefix wPrefix active F maskInput
                (unsplit (hIn, hOut))) wStar (sub i)⟩ mask =
            eFlip hIn mask i := by
        intro mask i
        have hemb : emb i = ⟨iv, sub i,
            (if active (sub i) = true then L0 (sub i) + uPrefix else L0 (sub i)) +
              (wPrefix + uPrefix) + wStar⟩ := rfl
        have hsubMem : emb i ∈ I := Finset.mem_image_of_mem emb (Finset.mem_univ i)
        simp only [honestCRTMaskTable, hunsplit_notMem (hnotMem₀ _), hunsplit_notMem (hnotMem₁ _),
          hunsplit_notMem (hnotMemAct _), candidateLabel]
        rw [← hemb, hunsplit_mem hsubMem]
        rfl
      simp only [crtPrefixEval, hcol]
    have hstep :
        ((uniformOfFintype (∀ q : I, Fin nMask → ZMod 2)).bind fun hIn =>
          PMF.pure (decide (∀ mask, Hsub *ᵥ eFlip hIn mask = 0))) =
        (uniformOfFintype (Fin nMask → Fin kGates → ZMod 2)).map
          (fun y => decide (∀ mask, Hsub *ᵥ y mask = 0)) := by
      rw [← uniformOfFintype_map_equiv eFlip, _root_.PMF.map_comp]
      rfl
    simp_rw [hinner]
    rw [hstep, multiMask_parityCheck_uniform_zero_prob hsurj]
  simp_rw [hconst]
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Single-guess false-accept bound in the random `uPrefix` and `H5` model: for any `wStar ≠
wPrefix`, conditioning away the `2⁻¹ ^ lam` collision `wPrefix + uPrefix = wStar` bounds the
`crtPrefixTest` acceptance probability by `2⁻¹ ^ (nMask * rSub) + 2⁻¹ ^ lam`. -/
private theorem crtPrefixTest_wrong_guess_le {IV : Type} [Fintype IV] [DecidableEq IV]
    {nMult lam nMask kGates rSub : ℕ}
    (sub : Fin kGates ↪ Fin nMult) (Hsub : Matrix (Fin rSub) (Fin kGates) (ZMod 2))
    (hsurj : Function.Surjective Hsub.mulVecLin)
    (iv : IV) (L0 : Fin nMult → (Fin lam → ZMod 2))
    (wPrefix wStar : Fin lam → ZMod 2) (active : Fin nMult → Bool)
    (F : Matrix (Fin nMult) (Fin lam) (ZMod 2))
    (maskInput : Fin nMask → (Fin lam → ZMod 2)) (hne : wStar ≠ wPrefix) :
    ((uniformOfFintype (H5Query IV nMult lam → Fin nMask → ZMod 2)).bind fun h5 =>
      (uniformOfFintype (Fin lam → ZMod 2)).bind fun uPrefix =>
        let tbl := honestCRTMaskTable iv L0 uPrefix wPrefix active F maskInput h5
        let hActive : Fin kGates → Fin nMask → ZMod 2 :=
          fun i => h5 ⟨iv, sub i, tbl.activeLabel (sub i)⟩
        ProbComp.eval ((crtPrefixTest sub Hsub tbl hActive wStar).run (fun q => pure (h5 q))))
      true ≤
      (2 : ℝ≥0∞)⁻¹ ^ (nMask * rSub) + (2 : ℝ≥0∞)⁻¹ ^ lam := by
  rw [PMF.bind_comm, PMF.bind_apply]
  let badU : Fin lam → ZMod 2 := wPrefix + wStar
  calc (∑' uPrefix : Fin lam → ZMod 2,
        (uniformOfFintype (Fin lam → ZMod 2)) uPrefix *
        ((uniformOfFintype (H5Query IV nMult lam → Fin nMask → ZMod 2)).bind fun h5 =>
          let tbl := honestCRTMaskTable iv L0 uPrefix wPrefix active F maskInput h5
          let hActive : Fin kGates → Fin nMask → ZMod 2 :=
            fun i => h5 ⟨iv, sub i, tbl.activeLabel (sub i)⟩
          ProbComp.eval ((crtPrefixTest sub Hsub tbl hActive wStar).run
            (fun q => pure (h5 q)))) true)
      ≤ ∑' uPrefix : Fin lam → ZMod 2,
          (uniformOfFintype (Fin lam → ZMod 2)) uPrefix *
            ((2 : ℝ≥0∞)⁻¹ ^ (nMask * rSub) + if uPrefix = badU then 1 else 0) := by
        refine tsum_le_tsum fun uPrefix => mul_le_mul_of_nonneg_left ?_ zero_le
        by_cases hu : uPrefix = badU
        · simp only [hu, ↓reduceIte]
          exact le_add_of_le_right (PMF.coe_le_one _ _)
        · have hnz : wPrefix + uPrefix + wStar ≠ 0 := by
            intro h0
            apply hu
            have hsum : uPrefix + badU = 0 := by
              rw [show badU = wPrefix + wStar from rfl, ← add_assoc, add_comm uPrefix wPrefix]
              exact h0
            exact (zmod2_vec_add_eq_zero_iff uPrefix badU).mp hsum
          have hp := crtPrefixTest_wrong_guess_prob sub Hsub hsurj iv L0 uPrefix wPrefix wStar
            active F maskInput hne hnz
          rw [hp]
          simp only [hu, ↓reduceIte, add_zero, le_rfl]
    _ = (2 : ℝ≥0∞)⁻¹ ^ (nMask * rSub) + (uniformOfFintype (Fin lam → ZMod 2)) badU := by
        simp_rw [mul_add, mul_ite, mul_one, mul_zero]
        rw [tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, tsum_ite_eq, add_comm]
    _ = (2 : ℝ≥0∞)⁻¹ ^ (nMask * rSub) + (2 : ℝ≥0∞)⁻¹ ^ lam := by
        simp [uniformOfFintype_apply, ZMod.card, ENNReal.inv_pow]

end CRTTables

/-! ### Issue-to-Spend & Spend-prefix unlinkability breaks, and `r`-first repair -/

section UnlinkabilityBreaks

/-- The Issue-to-Spend prefix-leakage experiment when `nf` sits in the first `lam` bits of the
issuance witness: two distinct nullifiers `nf₀ ≠ nf₁` are issued using random `u₀, u₁` and `H5`;
then `nf_b` (`nf₀` when `b = false`, `nf₁` when `b = true`) is revealed to the adversary together
with both issuance CRT tables and verifier active-label hashes. -/
noncomputable def crtIssueSpendGame {IV : Type} [Fintype IV] [DecidableEq IV]
    {nMult lam nMask kGates : ℕ}
    (sub : Fin kGates ↪ Fin nMult) (iv₀ iv₁ : IV)
    (L0₀ L0₁ : Fin nMult → (Fin lam → ZMod 2))
    (active₀ active₁ : Fin nMult → Bool)
    (F : Matrix (Fin nMult) (Fin lam) (ZMod 2))
    (maskInput₀ maskInput₁ : Fin nMask → (Fin lam → ZMod 2))
    (nf₀ nf₁ : Fin lam → ZMod 2)
    (A : CRTMaskTable IV nMult lam nMask → (Fin kGates → Fin nMask → ZMod 2) →
      CRTMaskTable IV nMult lam nMask → (Fin kGates → Fin nMask → ZMod 2) →
      (Fin lam → ZMod 2) → ProbOracleComp (H5Spec IV nMult lam nMask) Bool)
    (b : Bool) : Game :=
  (uniformOfFintype (H5Query IV nMult lam → Fin nMask → ZMod 2)).bind fun h5 =>
    (uniformOfFintype (Fin lam → ZMod 2)).bind fun u₀ =>
      (uniformOfFintype (Fin lam → ZMod 2)).bind fun u₁ =>
        let tbl₀ := honestCRTMaskTable iv₀ L0₀ u₀ nf₀ active₀ F maskInput₀ h5
        let tbl₁ := honestCRTMaskTable iv₁ L0₁ u₁ nf₁ active₁ F maskInput₁ h5
        let hAct₀ : Fin kGates → Fin nMask → ZMod 2 :=
          fun i => h5 ⟨iv₀, sub i, tbl₀.activeLabel (sub i)⟩
        let hAct₁ : Fin kGates → Fin nMask → ZMod 2 :=
          fun i => h5 ⟨iv₁, sub i, tbl₁.activeLabel (sub i)⟩
        ProbComp.eval
          ((A tbl₀ hAct₀ tbl₁ hAct₁ (if b then nf₁ else nf₀)).run fun q => pure (h5 q))

/-- The `kGates`-query Issue-to-Spend distinguisher testing the revealed spend nullifier `nf`
against client `0`'s issuance CRT table `tbl₀`. -/
def crtIssueSpendAdversary {IV : Type} {nMult lam nMask kGates rSub : ℕ}
    (sub : Fin kGates ↪ Fin nMult) (Hsub : Matrix (Fin rSub) (Fin kGates) (ZMod 2)) :
    CRTMaskTable IV nMult lam nMask → (Fin kGates → Fin nMask → ZMod 2) →
    CRTMaskTable IV nMult lam nMask → (Fin kGates → Fin nMask → ZMod 2) →
    (Fin lam → ZMod 2) → ProbOracleComp (H5Spec IV nMult lam nMask) Bool :=
  fun tbl₀ hAct₀ _ _ nf => crtPrefixTest sub Hsub tbl₀ hAct₀ nf

/-- `crtIssueSpendAdversary` makes at most `kGates` queries to `H5`. -/
theorem crtIssueSpendAdversary_isQueryBounded {IV : Type} {nMult lam nMask kGates rSub : ℕ}
    (sub : Fin kGates ↪ Fin nMult) (Hsub : Matrix (Fin rSub) (Fin kGates) (ZMod 2))
    (tbl₀ : CRTMaskTable IV nMult lam nMask) (hAct₀ : Fin kGates → Fin nMask → ZMod 2)
    (tbl₁ : CRTMaskTable IV nMult lam nMask) (hAct₁ : Fin kGates → Fin nMask → ZMod 2)
    (nf : Fin lam → ZMod 2) :
    (crtIssueSpendAdversary sub Hsub tbl₀ hAct₀ tbl₁ hAct₁ nf).IsQueryBounded kGates :=
  crtPrefixTest_isQueryBounded sub Hsub tbl₀ hAct₀ nf

/-- Issue-to-Spend CRT prefix break: whenever `nf₀ ≠ nf₁` and `Hsub * (F.submatrix sub id) = 0`
with surjective `Hsub.mulVecLin`, `crtIssueSpendAdversary` accepts `b = false` with probability `1`
and accepts `b = true` with probability at most `(2⁻¹) ^ (nMask * rSub) + (2⁻¹) ^ lam`, achieving
two-world advantage at least `1 - ((2⁻¹) ^ (nMask * rSub) + (2⁻¹) ^ lam)`. -/
theorem crtIssueSpendAdversary_advantage_ge {IV : Type} [Fintype IV] [DecidableEq IV]
    {nMult lam nMask kGates rSub : ℕ}
    (sub : Fin kGates ↪ Fin nMult) (Hsub : Matrix (Fin rSub) (Fin kGates) (ZMod 2))
    (F : Matrix (Fin nMult) (Fin lam) (ZMod 2))
    (hHF : Hsub * F.submatrix sub id = 0)
    (hsurj : Function.Surjective Hsub.mulVecLin)
    (iv₀ iv₁ : IV) (L0₀ L0₁ : Fin nMult → (Fin lam → ZMod 2))
    (active₀ active₁ : Fin nMult → Bool)
    (maskInput₀ maskInput₁ : Fin nMask → (Fin lam → ZMod 2))
    {nf₀ nf₁ : Fin lam → ZMod 2} (hne : nf₁ ≠ nf₀) :
    let g := crtIssueSpendGame sub iv₀ iv₁ L0₀ L0₁ active₀ active₁ F maskInput₀ maskInput₁
      nf₀ nf₁ (crtIssueSpendAdversary sub Hsub)
    1 - ((2 : ℝ)⁻¹ ^ (nMask * rSub) + (2 : ℝ)⁻¹ ^ lam) ≤
      (Game.advantage (g false) (g true) : ℝ) := by
  intro g
  have hfalse_succ : Game.succProbability (g false) = 1 := by
    have hstep (h5 u₀) :=
      crtPrefixTest_honest_true sub Hsub F hHF iv₀ L0₀ u₀ nf₀ active₀ maskInput₀ h5
    simp [g, crtIssueSpendGame, crtIssueSpendAdversary, hstep, PMF.bind_const, Game.succProbability]
  have htrue_le : (g true true) ≤ (2 : ℝ≥0∞)⁻¹ ^ (nMask * rSub) + (2 : ℝ≥0∞)⁻¹ ^ lam := by
    simp only [g, crtIssueSpendGame, crtIssueSpendAdversary, ↓reduceIte, PMF.bind_const]
    exact crtPrefixTest_wrong_guess_le sub Hsub hsurj iv₀ L0₀ nf₀ nf₁ active₀ F maskInput₀ hne
  have htrue_succR : (Game.succProbability (g true) : ℝ) ≤
      (2 : ℝ)⁻¹ ^ (nMask * rSub) + (2 : ℝ)⁻¹ ^ lam := by
    rw [Game.coe_succProbability]
    have hto := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨ENNReal.pow_ne_top (by norm_num), ENNReal.pow_ne_top (by norm_num)⟩)
      htrue_le
    simpa [ENNReal.toReal_add, ENNReal.toReal_pow] using hto
  rw [Game.coe_advantage, hfalse_succ]
  simp only [NNReal.coe_one]
  exact le_trans (by linarith) (le_abs_self _)

/-- Pack a `wBal`-bit balance prefix `tBits` and a `wRand`-bit randomness slice `rBits` into
`(wBal + wRand)` CRT witness prefix bits. -/
def packBalancePrefix {wBal wRand : ℕ}
    (tBits : Fin wBal → ZMod 2) (rBits : Fin wRand → ZMod 2) :
    Fin (wBal + wRand) → ZMod 2 :=
  Fin.append tBits rBits

/-- Left-injectivity of `packBalancePrefix`: equal encodings imply `t₀ = t₁`. -/
theorem packBalancePrefix_inj_left {wBal wRand : ℕ}
    {t₀ t₁ : Fin wBal → ZMod 2} {r₀ r₁ : Fin wRand → ZMod 2}
    (h : packBalancePrefix t₀ r₀ = packBalancePrefix t₁ r₁) : t₀ = t₁ := by
  funext i
  have hi := congrFun h (Fin.castAdd wRand i)
  simpa [packBalancePrefix, Fin.append_left] using hi

/-- Exhaustive Spend-prefix parity test across a list of `lam`-bit prefix guesses `guesses`. -/
def crtSpendPrefixTest {IV : Type} {nMult lam nMask kGates rSub : ℕ}
    (sub : Fin kGates ↪ Fin nMult) (Hsub : Matrix (Fin rSub) (Fin kGates) (ZMod 2))
    (tbl : CRTMaskTable IV nMult lam nMask) (hActive : Fin kGates → Fin nMask → ZMod 2) :
    List (Fin lam → ZMod 2) → ProbOracleComp (H5Spec IV nMult lam nMask) Bool
  | [] => pure false
  | w :: ws => do
      let hit ← crtPrefixTest sub Hsub tbl hActive w
      if hit then pure true else crtSpendPrefixTest sub Hsub tbl hActive ws

/-- `crtSpendPrefixTest` issues at most `guesses.length * kGates` `H5` queries. -/
theorem crtSpendPrefixTest_isQueryBounded {IV : Type} {nMult lam nMask kGates rSub : ℕ}
    (sub : Fin kGates ↪ Fin nMult) (Hsub : Matrix (Fin rSub) (Fin kGates) (ZMod 2))
    (tbl : CRTMaskTable IV nMult lam nMask) (hActive : Fin kGates → Fin nMask → ZMod 2)
    (guesses : List (Fin lam → ZMod 2)) :
    (crtSpendPrefixTest sub Hsub tbl hActive guesses).IsQueryBounded
      (guesses.length * kGates) := by
  induction guesses with
  | nil => simpa [crtSpendPrefixTest] using OracleComp.IsCostBounded.pure false 0
  | cons w ws ih =>
      simp only [crtSpendPrefixTest, List.length_cons, Nat.succ_mul]
      have h1 := crtPrefixTest_isQueryBounded sub Hsub tbl hActive w
      refine (h1.bind fun hit => ?_).mono (Nat.le_of_eq (Nat.add_comm _ _))
      cases hit
      · simpa only [Bool.false_eq_true, ↓reduceIte] using ih
      · exact (OracleComp.IsCostBounded.pure true 0).mono (Nat.zero_le _)

/-- Deterministic execution of `crtSpendPrefixTest` returns `guesses.any (crtPrefixEval ...)`. -/
theorem crtSpendPrefixTest_run {IV : Type} {nMult lam nMask kGates rSub : ℕ}
    (sub : Fin kGates ↪ Fin nMult) (Hsub : Matrix (Fin rSub) (Fin kGates) (ZMod 2))
    (tbl : CRTMaskTable IV nMult lam nMask) (hActive : Fin kGates → Fin nMask → ZMod 2)
    (h5 : H5Query IV nMult lam → Fin nMask → ZMod 2) (guesses : List (Fin lam → ZMod 2)) :
    (crtSpendPrefixTest sub Hsub tbl hActive guesses).run (fun q => pure (h5 q)) =
      pure (guesses.any fun w => crtPrefixEval sub Hsub tbl hActive h5 w) := by
  induction guesses with
  | nil => simp [crtSpendPrefixTest]
  | cons w ws ih =>
      simp only [crtSpendPrefixTest, ProbOracleComp.run_bind, crtPrefixTest_run, pure_bind,
        List.any_cons]
      cases hhit : crtPrefixEval sub Hsub tbl hActive h5 w
      · simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_or]
        exact ih
      · simp [ProbOracleComp.run_pure]

/-- Enumerate all `2 ^ wRand` guesses `packBalancePrefix tStar r` in deterministic order. -/
noncomputable def balancePrefixGuesses (wBal wRand : ℕ) (tStar : Fin wBal → ZMod 2) :
    List (Fin (wBal + wRand) → ZMod 2) :=
  (List.finRange (2 ^ wRand)).map fun idx =>
    packBalancePrefix tStar
      ((Fintype.equivFin (Fin wRand → ZMod 2)).symm
        (Fin.cast (by simp [ZMod.card]) idx))

/-- `balancePrefixGuesses wBal wRand tStar` has length `2 ^ wRand`. -/
@[simp] theorem length_balancePrefixGuesses (wBal wRand : ℕ) (tStar : Fin wBal → ZMod 2) :
    (balancePrefixGuesses wBal wRand tStar).length = 2 ^ wRand := by
  simp [balancePrefixGuesses]

/-- Every `packBalancePrefix tStar r` is listed in `balancePrefixGuesses wBal wRand tStar`. -/
theorem mem_balancePrefixGuesses {wBal wRand : ℕ} (tStar : Fin wBal → ZMod 2)
    (r : Fin wRand → ZMod 2) :
    packBalancePrefix tStar r ∈ balancePrefixGuesses wBal wRand tStar := by
  simp only [balancePrefixGuesses, List.mem_map, List.mem_finRange, true_and]
  refine ⟨Fin.cast (by simp [ZMod.card])
    (Fintype.equivFin (Fin wRand → ZMod 2) r), ?_⟩
  simp

/-- Candidates in `balancePrefixGuesses wBal wRand tStar` are disjoint from
`packBalancePrefix tReal rReal` whenever `tStar ≠ tReal`. -/
theorem mem_balancePrefixGuesses_ne {wBal wRand : ℕ} {tStar tReal : Fin wBal → ZMod 2}
    (hne : tStar ≠ tReal) (rReal : Fin wRand → ZMod 2) :
    ∀ w ∈ balancePrefixGuesses wBal wRand tStar, w ≠ packBalancePrefix tReal rReal := by
  intro w hw heq
  simp only [balancePrefixGuesses, List.mem_map, List.mem_finRange, true_and] at hw
  obtain ⟨idx, rfl⟩ := hw
  exact hne (packBalancePrefix_inj_left heq)

/-- When `tStar = tReal`, `crtSpendPrefixTest` over `balancePrefixGuesses` succeeds with probability
`1` in at most `2 ^ wRand * kGates` queries. -/
theorem crtSpendPrefixTest_correct {IV : Type} {nMult wBal wRand nMask kGates rSub : ℕ}
    (sub : Fin kGates ↪ Fin nMult) (Hsub : Matrix (Fin rSub) (Fin kGates) (ZMod 2))
    (F : Matrix (Fin nMult) (Fin (wBal + wRand)) (ZMod 2))
    (hHF : Hsub * F.submatrix sub id = 0)
    (iv : IV) (L0 : Fin nMult → (Fin (wBal + wRand) → ZMod 2))
    (uPrefix : Fin (wBal + wRand) → ZMod 2) (tReal : Fin wBal → ZMod 2)
    (rReal : Fin wRand → ZMod 2) (active : Fin nMult → Bool)
    (maskInput : Fin nMask → (Fin (wBal + wRand) → ZMod 2))
    (h5 : H5Query IV nMult (wBal + wRand) → Fin nMask → ZMod 2) :
    let wPrefix := packBalancePrefix tReal rReal
    let tbl := honestCRTMaskTable iv L0 uPrefix wPrefix active F maskInput h5
    let hActive : Fin kGates → Fin nMask → ZMod 2 :=
      fun i => h5 ⟨iv, sub i, tbl.activeLabel (sub i)⟩
    ProbComp.eval ((crtSpendPrefixTest sub Hsub tbl hActive
      (balancePrefixGuesses wBal wRand tReal)).run (fun q => pure (h5 q))) = PMF.pure true := by
  intro wPrefix tbl hActive
  rw [crtSpendPrefixTest_run, ProbComp.eval_pure]
  congr 1
  rw [List.any_eq_true]
  refine ⟨wPrefix, mem_balancePrefixGuesses tReal rReal, ?_⟩
  have h1 := crtPrefixTest_honest_true sub Hsub F hHF iv L0 uPrefix wPrefix active maskInput h5
  dsimp only at h1
  rw [crtPrefixTest_run, ProbComp.eval_pure] at h1
  simpa [wPrefix, tbl, hActive] using congrArg (· true) h1

/-- When `tReal` differs from every balance candidate in `guesses`, a `crtSpendPrefixTest` scan
false-accepts with probability at most
`guesses.length * ((2⁻¹) ^ (nMask * rSub) + (2⁻¹) ^ (wBal + wRand))` in the random `uPrefix` +
`H5` model. -/
theorem crtSpendPrefixTest_wrong_t_le {IV : Type} [Fintype IV] [DecidableEq IV]
    {nMult wBal wRand nMask kGates rSub : ℕ}
    (sub : Fin kGates ↪ Fin nMult) (Hsub : Matrix (Fin rSub) (Fin kGates) (ZMod 2))
    (hsurj : Function.Surjective Hsub.mulVecLin)
    (iv : IV) (L0 : Fin nMult → (Fin (wBal + wRand) → ZMod 2))
    (tReal : Fin wBal → ZMod 2) (rReal : Fin wRand → ZMod 2)
    (active : Fin nMult → Bool) (F : Matrix (Fin nMult) (Fin (wBal + wRand)) (ZMod 2))
    (maskInput : Fin nMask → (Fin (wBal + wRand) → ZMod 2))
    (guesses : List (Fin (wBal + wRand) → ZMod 2))
    (hguesses : ∀ w ∈ guesses, w ≠ packBalancePrefix tReal rReal) :
    ((uniformOfFintype (H5Query IV nMult (wBal + wRand) → Fin nMask → ZMod 2)).bind fun h5 =>
      (uniformOfFintype (Fin (wBal + wRand) → ZMod 2)).bind fun uPrefix =>
        let wPrefix := packBalancePrefix tReal rReal
        let tbl := honestCRTMaskTable iv L0 uPrefix wPrefix active F maskInput h5
        let hActive : Fin kGates → Fin nMask → ZMod 2 :=
          fun i => h5 ⟨iv, sub i, tbl.activeLabel (sub i)⟩
        ProbComp.eval ((crtSpendPrefixTest sub Hsub tbl hActive guesses).run
          (fun q => pure (h5 q)))) true ≤
      (guesses.length : ℝ≥0∞) *
        ((2 : ℝ≥0∞)⁻¹ ^ (nMask * rSub) + (2 : ℝ≥0∞)⁻¹ ^ (wBal + wRand)) := by
  let wPrefix := packBalancePrefix tReal rReal
  let H5T := H5Query IV nMult (wBal + wRand) → Fin nMask → ZMod 2
  let UT := Fin (wBal + wRand) → ZMod 2
  let evalProg (c : H5T → UT → ProbOracleComp (H5Spec IV nMult (wBal + wRand) nMask) Bool) :
      Game :=
    (uniformOfFintype H5T).bind fun h5 =>
      (uniformOfFintype UT).bind fun uPrefix =>
        ProbComp.eval ((c h5 uPrefix).run (fun q => pure (h5 q)))
  let tbl (h5 : H5T) (uPrefix : UT) :=
    honestCRTMaskTable iv L0 uPrefix wPrefix active F maskInput h5
  let hAct (h5 : H5T) (uPrefix : UT) : Fin kGates → Fin nMask → ZMod 2 :=
    fun i => h5 ⟨iv, sub i, (tbl h5 uPrefix).activeLabel (sub i)⟩
  change evalProg (fun h5 u => crtSpendPrefixTest sub Hsub (tbl h5 u) (hAct h5 u) guesses) true ≤ _
  induction guesses with
  | nil =>
      simp [evalProg, crtSpendPrefixTest, ProbOracleComp.run_pure, ProbComp.eval_pure]
  | cons w ws ih =>
      have hw : w ≠ wPrefix := hguesses w List.mem_cons_self
      have ih_ws := ih fun u hu => hguesses u (List.mem_cons_of_mem w hu)
      have hpt_le (h5 : H5T) (u : UT) :
          (ProbComp.eval ((crtSpendPrefixTest sub Hsub (tbl h5 u) (hAct h5 u) (w :: ws)).run
            (fun q => pure (h5 q)))) true ≤
          (ProbComp.eval ((crtPrefixTest sub Hsub (tbl h5 u) (hAct h5 u) w).run
            (fun q => pure (h5 q)))) true +
          (ProbComp.eval ((crtSpendPrefixTest sub Hsub (tbl h5 u) (hAct h5 u) ws).run
            (fun q => pure (h5 q)))) true := by
        rw [crtSpendPrefixTest_run, crtPrefixTest_run, crtSpendPrefixTest_run,
          ProbComp.eval_pure, ProbComp.eval_pure, ProbComp.eval_pure]
        simp only [List.any_cons, PMF.pure_apply]
        cases crtPrefixEval sub Hsub _ _ h5 w <;>
          cases List.any ws _ <;> simp
      have hterm_le :
          evalProg (fun h5 u => crtSpendPrefixTest sub Hsub (tbl h5 u) (hAct h5 u) (w :: ws))
            true ≤
          evalProg (fun h5 u => crtPrefixTest sub Hsub (tbl h5 u) (hAct h5 u) w) true +
          evalProg (fun h5 u => crtSpendPrefixTest sub Hsub (tbl h5 u) (hAct h5 u) ws) true := by
        simp only [evalProg, PMF.bind_apply]
        rw [← tsum_add]
        refine tsum_le_tsum fun h5 => ?_
        rw [← mul_add, ← tsum_add]
        refine mul_le_mul_of_nonneg_left (tsum_le_tsum fun u => ?_) zero_le
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (hpt_le h5 u) zero_le
      have hw_bound :=
        crtPrefixTest_wrong_guess_le sub Hsub hsurj iv L0 wPrefix w active F maskInput hw
      calc evalProg (fun h5 u => crtSpendPrefixTest sub Hsub (tbl h5 u) (hAct h5 u) (w :: ws)) true
          ≤ ((2 : ℝ≥0∞)⁻¹ ^ (nMask * rSub) + (2 : ℝ≥0∞)⁻¹ ^ (wBal + wRand)) +
              (ws.length : ℝ≥0∞) *
                ((2 : ℝ≥0∞)⁻¹ ^ (nMask * rSub) + (2 : ℝ≥0∞)⁻¹ ^ (wBal + wRand)) :=
            hterm_le.trans (add_le_add hw_bound ih_ws)
        _ = ((w :: ws).length : ℝ≥0∞) *
              ((2 : ℝ≥0∞)⁻¹ ^ (nMask * rSub) + (2 : ℝ≥0∞)⁻¹ ^ (wBal + wRand)) := by
            simp [List.length_cons, Nat.cast_add, add_mul, one_mul, add_comm]

/-- Spend-balance CRT prefix experiment: two distinct candidate balances `t₀ ≠ t₁` pack into the
leading `wBal` bits of `(t_b, r)` (`wBal + wRand` prefix bits), and the distinguisher receives the
resulting Spend CRT table and tests `t₀` by enumerating all `2 ^ wRand` trailing randomness
slices. -/
noncomputable def crtSpendBalancePrefixGame {IV : Type} [Fintype IV] [DecidableEq IV]
    {nMult wBal wRand nMask kGates rSub : ℕ}
    (sub : Fin kGates ↪ Fin nMult) (Hsub : Matrix (Fin rSub) (Fin kGates) (ZMod 2))
    (iv : IV) (L0 : Fin nMult → (Fin (wBal + wRand) → ZMod 2))
    (active : Fin nMult → Bool) (F : Matrix (Fin nMult) (Fin (wBal + wRand)) (ZMod 2))
    (maskInput : Fin nMask → (Fin (wBal + wRand) → ZMod 2))
    (t₀ t₁ : Fin wBal → ZMod 2) (rReal : Fin wRand → ZMod 2) (b : Bool) : Game :=
  (uniformOfFintype (H5Query IV nMult (wBal + wRand) → Fin nMask → ZMod 2)).bind fun h5 =>
    (uniformOfFintype (Fin (wBal + wRand) → ZMod 2)).bind fun u =>
      let wPrefix := packBalancePrefix (if b then t₁ else t₀) rReal
      let tbl := honestCRTMaskTable iv L0 u wPrefix active F maskInput h5
      let hAct : Fin kGates → Fin nMask → ZMod 2 :=
        fun i => h5 ⟨iv, sub i, tbl.activeLabel (sub i)⟩
      ProbComp.eval ((crtSpendPrefixTest sub Hsub tbl hAct
        (balancePrefixGuesses wBal wRand t₀)).run (fun q => pure (h5 q)))

/-- When `t₀ ≠ t₁`, testing `balancePrefixGuesses wBal wRand t₀` (`2 ^ wRand * kGates` `H5`
queries) accepts `b = false` with probability `1` and false-accepts `b = true` with probability at
most `2 ^ wRand * ((2⁻¹) ^ (nMask * rSub) + (2⁻¹) ^ (wBal + wRand))`. -/
theorem crtSpendBalancePrefix_advantage_ge {IV : Type} [Fintype IV] [DecidableEq IV]
    {nMult wBal wRand nMask kGates rSub : ℕ}
    (sub : Fin kGates ↪ Fin nMult) (Hsub : Matrix (Fin rSub) (Fin kGates) (ZMod 2))
    (F : Matrix (Fin nMult) (Fin (wBal + wRand)) (ZMod 2))
    (hHF : Hsub * F.submatrix sub id = 0)
    (hsurj : Function.Surjective Hsub.mulVecLin)
    (iv : IV) (L0 : Fin nMult → (Fin (wBal + wRand) → ZMod 2))
    (active : Fin nMult → Bool)
    (maskInput : Fin nMask → (Fin (wBal + wRand) → ZMod 2))
    {t₀ t₁ : Fin wBal → ZMod 2} (hne : t₀ ≠ t₁) (rReal : Fin wRand → ZMod 2) :
    let g := crtSpendBalancePrefixGame sub Hsub iv L0 active F maskInput t₀ t₁ rReal
    1 - (2 : ℝ) ^ wRand * ((2 : ℝ)⁻¹ ^ (nMask * rSub) + (2 : ℝ)⁻¹ ^ (wBal + wRand)) ≤
      (Game.advantage (g false) (g true) : ℝ) := by
  intro g
  have hfalse_succ : Game.succProbability (g false) = 1 := by
    have h1 (h5 u) :=
      crtSpendPrefixTest_correct sub Hsub F hHF iv L0 u t₀ rReal active maskInput h5
    simp [g, crtSpendBalancePrefixGame, h1, PMF.bind_const, Game.succProbability]
  have htrue_le : (g true true) ≤
      ((2 ^ wRand : ℕ) : ℝ≥0∞) *
        ((2 : ℝ≥0∞)⁻¹ ^ (nMask * rSub) + (2 : ℝ≥0∞)⁻¹ ^ (wBal + wRand)) := by
    simpa only [g, crtSpendBalancePrefixGame, ↓reduceIte, length_balancePrefixGuesses] using
      crtSpendPrefixTest_wrong_t_le sub Hsub hsurj iv L0 t₁ rReal active F maskInput
        (balancePrefixGuesses wBal wRand t₀) (mem_balancePrefixGuesses_ne hne rReal)
  have htrue_succR : (Game.succProbability (g true) : ℝ) ≤
      (2 : ℝ) ^ wRand * ((2 : ℝ)⁻¹ ^ (nMask * rSub) + (2 : ℝ)⁻¹ ^ (wBal + wRand)) := by
    rw [Game.coe_succProbability]
    have hto := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        (ENNReal.add_ne_top.mpr
          ⟨ENNReal.pow_ne_top (by norm_num), ENNReal.pow_ne_top (by norm_num)⟩))
      htrue_le
    simpa [ENNReal.toReal_mul, ENNReal.toReal_add, ENNReal.toReal_pow] using hto
  rw [Game.coe_advantage, hfalse_succ]
  simp only [NNReal.coe_one]
  exact le_trans (by linarith) (le_abs_self _)

/-- Witness-order repair view (in the witness-reuse CRT mode that reuses the witness prefix as the
CRT mask offset, placing fresh uniform opening `r` at
bytes `0..lam` and `H5` unqueried on complementary labels): given public `L0` and `active`, the
uniform opening `r`, uniform VOLE secret `u`, and uniform `H5` mask padding `hXor` produce
`dPrefix := r + u` and `cmult` shifted by `F *ᵥ maskInput metaData`. -/
noncomputable def rFirstCRTMaskView {IV Meta : Type} {nMult lam nMask : ℕ}
    (iv : IV) (L0 : Fin nMult → (Fin lam → ZMod 2)) (active : Fin nMult → Bool)
    (F : Matrix (Fin nMult) (Fin lam) (ZMod 2))
    (maskInput : Meta → Fin nMask → (Fin lam → ZMod 2))
    (metaData : Meta) : PMF (CRTMaskTable IV nMult lam nMask) := do
  let r ← uniformOfFintype (Fin lam → ZMod 2)
  let u ← uniformOfFintype (Fin lam → ZMod 2)
  let hXor ← uniformOfFintype (Fin nMask → Fin nMult → ZMod 2)
  return {
    iv := iv
    activeLabel := fun e => if active e then L0 e + u else L0 e
    dPrefix := r + u
    cmult := fun mask e => hXor mask e + (F *ᵥ maskInput metaData mask) e }

/-- Idealized decoupled CRT table distribution (`G8.5`, this library's intermediate hop between
FAEST v3.0 Theorem 10.42's `G8` and `G9` in [BaumEtAl2026FAEST]) with uniform `dPrefix` and
`cmult`, independent of the witness opening `r`. -/
noncomputable def rFirstDecoupledView {IV : Type} {nMult lam nMask : ℕ}
    (iv : IV) (activeLabel : Fin nMult → (Fin lam → ZMod 2)) :
    PMF (CRTMaskTable IV nMult lam nMask) := do
  let d ← uniformOfFintype (Fin lam → ZMod 2)
  let c ← uniformOfFintype (Fin nMask → Fin nMult → ZMod 2)
  return ⟨iv, activeLabel, d, c⟩

/-- When `H5` answers on active and complementary labels are uniform and fresh uniform opening
`r` is placed first, both `r ↦ r + u` and `hXor ↦ hXor + F *ᵥ maskInput metaData` are uniform
bijections, so `rFirstCRTMaskView` equals `(uniformOfFintype _).bind (fun u => rFirstDecoupledView
...)`, completely decoupling `(dPrefix, cmult)` from `u` and `metaData`. -/
theorem rFirstCRTMaskView_eq_decoupled {IV Meta : Type} {nMult lam nMask : ℕ}
    (iv : IV) (L0 : Fin nMult → (Fin lam → ZMod 2)) (active : Fin nMult → Bool)
    (F : Matrix (Fin nMult) (Fin lam) (ZMod 2))
    (maskInput : Meta → Fin nMask → (Fin lam → ZMod 2))
    (metaData : Meta) :
    rFirstCRTMaskView iv L0 active F maskInput metaData =
      (uniformOfFintype (Fin lam → ZMod 2)).bind fun u =>
        rFirstDecoupledView iv (fun e => if active e then L0 e + u else L0 e) := by
  dsimp only [rFirstCRTMaskView, rFirstDecoupledView, bind, pure]
  rw [PMF.bind_comm]
  refine congrArg (PMF.bind (uniformOfFintype (Fin lam → ZMod 2))) (funext fun u => ?_)
  let eD : (Fin lam → ZMod 2) ≃ (Fin lam → ZMod 2) :=
    { toFun := fun r => r + u
      invFun := fun d => d + u
      left_inv := fun r => zmod2_vec_add_cancel_right r u
      right_inv := fun d => zmod2_vec_add_cancel_right d u }
  refine (uniformOfFintype_bind_equiv eD (fun d =>
    (uniformOfFintype (Fin nMask → Fin nMult → ZMod 2)).bind fun hXor =>
      PMF.pure (CRTMaskTable.mk iv (fun e => if active e then L0 e + u else L0 e) d
        fun mask e => hXor mask e + (F *ᵥ maskInput metaData mask) e))).trans ?_
  refine congrArg (PMF.bind (uniformOfFintype (Fin lam → ZMod 2))) (funext fun d => ?_)
  let eC : (Fin nMask → Fin nMult → ZMod 2) ≃ (Fin nMask → Fin nMult → ZMod 2) :=
    { toFun := fun hXor mask e => hXor mask e + (F *ᵥ maskInput metaData mask) e
      invFun := fun cmult mask e => cmult mask e + (F *ᵥ maskInput metaData mask) e
      left_inv := fun hXor => funext fun mask =>
        zmod2_vec_add_cancel_right (hXor mask) (F *ᵥ maskInput metaData mask)
      right_inv := fun cmult => funext fun mask =>
        zmod2_vec_add_cancel_right (cmult mask) (F *ᵥ maskInput metaData mask) }
  exact uniformOfFintype_bind_equiv eC fun c =>
    PMF.pure (CRTMaskTable.mk iv (fun e => if active e then L0 e + u else L0 e) d c)

/-- Corollary: `rFirstCRTMaskView` is identically distributed across arbitrary semantic metadata
`meta₀` and `meta₁` once `r` is placed first and `H5` answers are unqueried. -/
theorem rFirstCRTMaskView_eq {IV Meta : Type} {nMult lam nMask : ℕ}
    (iv : IV) (L0 : Fin nMult → (Fin lam → ZMod 2)) (active : Fin nMult → Bool)
    (F : Matrix (Fin nMult) (Fin lam) (ZMod 2))
    (maskInput : Meta → Fin nMask → (Fin lam → ZMod 2))
    (meta₀ meta₁ : Meta) :
    rFirstCRTMaskView iv L0 active F maskInput meta₀ =
      rFirstCRTMaskView iv L0 active F maskInput meta₁ := by
  rw [rFirstCRTMaskView_eq_decoupled, rFirstCRTMaskView_eq_decoupled]

/-- Even when `r` is placed first, a **witness-knowing** ZK distinguisher (supplied with `r`) runs
`crtPrefixTest` on `w* = r` and distinguishes real `honestCRTMaskTable` tables from uniform
`cmult` simulations with probability `1` vs `2⁻¹ ^ (nMask * rSub)` (`advantage = 1 - ...`). -/
theorem rFirst_breaks_witnessKnowingZK {IV : Type} [Fintype IV] [DecidableEq IV]
    {nMult lam nMask kGates rSub : ℕ}
    (sub : Fin kGates ↪ Fin nMult) (Hsub : Matrix (Fin rSub) (Fin kGates) (ZMod 2))
    (F : Matrix (Fin nMult) (Fin lam) (ZMod 2))
    (hHF : Hsub * F.submatrix sub id = 0)
    (hsurj : Function.Surjective Hsub.mulVecLin)
    (iv : IV) (L0 : Fin nMult → (Fin lam → ZMod 2))
    (uPrefix r : Fin lam → ZMod 2) (active : Fin nMult → Bool)
    (maskInput : Fin nMask → (Fin lam → ZMod 2)) :
    let gReal : Game :=
      (uniformOfFintype (H5Query IV nMult lam → Fin nMask → ZMod 2)).bind fun h5 =>
        let tbl := honestCRTMaskTable iv L0 uPrefix r active F maskInput h5
        let hActive : Fin kGates → Fin nMask → ZMod 2 :=
          fun i => h5 ⟨iv, sub i, tbl.activeLabel (sub i)⟩
        ProbComp.eval ((crtPrefixTest sub Hsub tbl hActive r).run (fun q => pure (h5 q)))
    let gSim : Game :=
      (uniformOfFintype (Fin nMask → Fin nMult → ZMod 2)).bind fun cmultSim =>
        (uniformOfFintype (Fin lam → ZMod 2)).bind fun dSim =>
          (uniformOfFintype (H5Query IV nMult lam → Fin nMask → ZMod 2)).bind fun h5 =>
            let actL : Fin nMult → Fin lam → ZMod 2 :=
              fun e => if active e then L0 e + uPrefix else L0 e
            let tbl : CRTMaskTable IV nMult lam nMask := ⟨iv, actL, dSim, cmultSim⟩
            let hActive : Fin kGates → Fin nMask → ZMod 2 :=
              fun i => h5 ⟨iv, sub i, actL (sub i)⟩
            ProbComp.eval ((crtPrefixTest sub Hsub tbl hActive r).run (fun q => pure (h5 q)))
    1 - (2 : ℝ)⁻¹ ^ (nMask * rSub) ≤ (Game.advantage gReal gSim : ℝ) := by
  intro gReal gSim
  have hreal_succ : Game.succProbability gReal = 1 := by
    have h1 (h5) := crtPrefixTest_honest_true sub Hsub F hHF iv L0 uPrefix r active maskInput h5
    simp [gReal, h1, PMF.bind_const, Game.succProbability]
  -- Under `gSim`, `cmultSim` is uniform and independent of `(hActive, h5 at L*)`.
  have hsim_val : gSim true ≤ (2 : ℝ≥0∞)⁻¹ ^ (nMask * rSub) := by
    have hinner : ∀ (dSim : Fin lam → ZMod 2)
        (h5 : H5Query IV nMult lam → Fin nMask → ZMod 2),
        ((uniformOfFintype (Fin nMask → Fin nMult → ZMod 2)).bind fun cmultSim =>
          let actL : Fin nMult → Fin lam → ZMod 2 :=
            fun e => if active e then L0 e + uPrefix else L0 e
          let tbl : CRTMaskTable IV nMult lam nMask := ⟨iv, actL, dSim, cmultSim⟩
          let hActive : Fin kGates → Fin nMask → ZMod 2 :=
            fun i => h5 ⟨iv, sub i, actL (sub i)⟩
          ProbComp.eval ((crtPrefixTest sub Hsub tbl hActive r).run (fun q => pure (h5 q))))
            true = (2 : ℝ≥0∞)⁻¹ ^ (nMask * rSub) := by
      intro dSim h5
      let actL : Fin nMult → Fin lam → ZMod 2 :=
        fun e => if active e then L0 e + uPrefix else L0 e
      let hActive : Fin kGates → Fin nMask → ZMod 2 :=
        fun i => h5 ⟨iv, sub i, actL (sub i)⟩
      let base : Fin nMask → Fin kGates → ZMod 2 := fun mask i =>
        hActive i mask + h5 ⟨iv, sub i, actL (sub i) + dSim + r⟩ mask
      have hres : ∀ cmultSim : Fin nMask → Fin nMult → ZMod 2,
          ProbComp.eval ((crtPrefixTest sub Hsub ⟨iv, actL, dSim, cmultSim⟩ hActive r).run
            (fun q => pure (h5 q))) =
          PMF.pure
            (decide (∀ mask, Hsub *ᵥ (fun i => cmultSim mask (sub i) + base mask i) = 0)) := by
        intro cmultSim
        rw [crtPrefixTest_run, ProbComp.eval_pure]
        have hcol : ∀ mask i,
            cmultSim mask (sub i) + hActive i mask +
              h5 ⟨iv, sub i, candidateLabel ⟨iv, actL, dSim, cmultSim⟩ r (sub i)⟩ mask =
              cmultSim mask (sub i) + base mask i := fun mask i => by
          simp only [candidateLabel, actL, base, add_assoc]
        simp only [crtPrefixEval, hcol]
      dsimp only [actL, hActive] at hres ⊢
      simp_rw [hres]
      have hmap :
          ((uniformOfFintype (Fin nMask → Fin nMult → ZMod 2)).bind fun cmultSim =>
            PMF.pure
              (decide (∀ mask, Hsub *ᵥ (fun i => cmultSim mask (sub i) + base mask i) = 0))) =
          ((uniformOfFintype (Fin nMask → Fin kGates → ZMod 2)).map
            fun y => decide (∀ mask, Hsub *ᵥ y mask = 0)) := by
        -- Restrict each `cmultSim mask` to `sub` via `uniformOfFintype_pi_map_comp_embedding`.
        have hperm :
            ((uniformOfFintype (Fin nMask → Fin nMult → ZMod 2)).map
              fun cmultSim mask i => cmultSim mask (sub i)) =
            uniformOfFintype (Fin nMask → Fin kGates → ZMod 2) := by
          let eSwap : (Fin nMask → Fin nMult → ZMod 2) ≃ (Fin nMult → Fin nMask → ZMod 2) :=
            Equiv.piComm _
          let eSwapK : (Fin kGates → Fin nMask → ZMod 2) ≃ (Fin nMask → Fin kGates → ZMod 2) :=
            Equiv.piComm _
          have hpull := uniformOfFintype_pi_map_comp_embedding (α := Fin nMask → ZMod 2) sub
          have hcomp1 : (fun (cmultSim : Fin nMask → Fin nMult → ZMod 2) mask i =>
              cmultSim mask (sub i)) =
              eSwapK ∘ (fun f i => f (sub i)) ∘ eSwap := rfl
          rw [hcomp1, ← _root_.PMF.map_comp, ← _root_.PMF.map_comp,
            uniformOfFintype_map_equiv eSwap, hpull, uniformOfFintype_map_equiv eSwapK]
        let eShift : (Fin nMask → Fin kGates → ZMod 2) ≃ (Fin nMask → Fin kGates → ZMod 2) :=
          { toFun := fun y mask i => y mask i + base mask i
            invFun := fun y mask i => y mask i + base mask i
            left_inv := fun y => funext fun mask =>
              zmod2_vec_add_cancel_right (y mask) (base mask)
            right_inv := fun y => funext fun mask =>
              zmod2_vec_add_cancel_right (y mask) (base mask) }
        calc ((uniformOfFintype (Fin nMask → Fin nMult → ZMod 2)).bind fun cmultSim =>
                PMF.pure (decide (∀ mask,
                  Hsub *ᵥ (fun i => cmultSim mask (sub i) + base mask i) = 0)))
            = ((uniformOfFintype (Fin nMask → Fin nMult → ZMod 2)).map
                fun cmultSim mask i => cmultSim mask (sub i)).map
                (fun y => decide (∀ mask, Hsub *ᵥ (fun i => y mask i + base mask i) = 0)) := by
              rw [_root_.PMF.map_comp]; rfl
          _ = (uniformOfFintype (Fin nMask → Fin kGates → ZMod 2)).map
                (fun y => decide (∀ mask, Hsub *ᵥ (fun i => y mask i + base mask i) = 0)) := by
              rw [hperm]
          _ = ((uniformOfFintype (Fin nMask → Fin kGates → ZMod 2)).map eShift).map
                (fun y => decide (∀ mask, Hsub *ᵥ y mask = 0)) := by
              rw [_root_.PMF.map_comp]; rfl
          _ = (uniformOfFintype (Fin nMask → Fin kGates → ZMod 2)).map
                (fun y => decide (∀ mask, Hsub *ᵥ y mask = 0)) := by
              rw [uniformOfFintype_map_equiv eShift]
      rw [hmap, multiMask_parityCheck_uniform_zero_prob hsurj]
    have hreorder : gSim =
        (uniformOfFintype (Fin lam → ZMod 2)).bind fun dSim =>
          (uniformOfFintype (H5Query IV nMult lam → Fin nMask → ZMod 2)).bind fun h5 =>
            (uniformOfFintype (Fin nMask → Fin nMult → ZMod 2)).bind fun cmultSim =>
              let actL : Fin nMult → Fin lam → ZMod 2 :=
                fun e => if active e then L0 e + uPrefix else L0 e
              let tbl : CRTMaskTable IV nMult lam nMask := ⟨iv, actL, dSim, cmultSim⟩
              let hActive : Fin kGates → Fin nMask → ZMod 2 :=
                fun i => h5 ⟨iv, sub i, actL (sub i)⟩
              ProbComp.eval
                ((crtPrefixTest sub Hsub tbl hActive r).run (fun q => pure (h5 q))) := by
      simp only [gSim]
      rw [PMF.bind_comm]
      congr 1 with dSim : 1
      rw [PMF.bind_comm]
    rw [hreorder, PMF.bind_apply]
    refine le_of_eq ?_
    simp_rw [PMF.bind_apply (uniformOfFintype (H5Query IV nMult lam → Fin nMask → ZMod 2)),
      hinner, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have hsim_succR : (Game.succProbability gSim : ℝ) ≤ (2 : ℝ)⁻¹ ^ (nMask * rSub) := by
    rw [Game.coe_succProbability]
    simpa [ENNReal.toReal_pow] using
      ENNReal.toReal_mono (ENNReal.pow_ne_top (by norm_num)) hsim_val
  rw [Game.coe_advantage, hreal_succ]
  simp only [NNReal.coe_one]
  exact le_trans (by linarith) (le_abs_self _)

end UnlinkabilityBreaks

end Cslib.Crypto.AnonymousToken.CRTHazard
