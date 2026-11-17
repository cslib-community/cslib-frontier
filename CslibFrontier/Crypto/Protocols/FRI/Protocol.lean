/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.BCS.ROM
public import CslibFrontier.Crypto.Protocols.FRI.Folding
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn

/-!
# Multi-Round FRI as a Public-Coin Interactive Oracle Proof

This module instantiates the multi-round 2-to-1 Fast Reed–Solomon Interactive Oracle Proof of
Proximity (FRI) ([BenSassonBentovHoreshRiabzev2018]; [BenSassonCarmonIshaiKoppartySaraf2020],
Section 8) directly as a `Cslib.Crypto.Protocols.BCS.PublicCoinIOP` compatible with the
Ben-Sasson–Chiesa–Spooner (BCS) random-oracle compiler ([BenSassonChiesaSpooner2016]).

## Protocol layout

Given `params : FRIParams F` with initial coset size `2 ^ d`, `m ≤ d` 2-to-1 folding rounds, final
Reed–Solomon dimension `1 ≤ kFinal ≤ 2 ^ (d - m)`, and `q` independent query repetitions:

* **Rounds & tables.** The IOP runs for `m + 1` rounds over depth-`d` oracle tables
  `OracleTable d F = Fin (2 ^ d) → F`. The active domain of round `j` has size `2 ^ (d - j)` and
  sits in the prefix `< 2 ^ (d - j)` of the table (padded by `0` outside).
* **Challenges.** Each round draws a uniform challenge `FRIChal F d q` carrying both a folding
  scalar `foldScalar : F` and a batch of `q` query starting positions
  `queryIdxs : Fin q → Fin (2 ^ d)`. Commit rounds `0, ..., m - 1` use only `foldScalar`, while the
  final round `m` uses `queryIdxs`. Bundling all `q` independent query positions into the single
  final round preserves exponential `(1 - δ) ^ q` query-phase soundness under the uniform
  per-round escape bound of `Cslib.Crypto.Protocols.BCS.bcsROMSoundness_bound`.
* **Round-0 binding and succinct verification.** The verifier reads the first `kFinal` entries of
  the final oracle `π_m` to define a degree-`< kFinal` Reed–Solomon codeword by Lagrange
  interpolation, and for each of the `q` queried starting positions `s : Fin (2 ^ d)` checks:
  1. explicit round-0 binding `π_0(s) = stmt(s)` against the input word `stmt`,
  2. all `m` 2-to-1 coset folding equations along the squaring path of `s`, and
  3. agreement of `π_m(s % 2 ^ (d - m))` with the interpolated final codeword.
  The total query count is `kFinal + q * (3 * m + 2)`, independent of `2 ^ d`.

## Main definitions

* `Cslib.Crypto.Protocols.FRI.FRIParams`, `Cslib.Crypto.Protocols.FRI.FRIChal`: parameter bundle
  and public-coin challenge structure for multi-round 2-to-1 FRI.
* `Cslib.Crypto.Protocols.FRI.lagrangeBasisEval`, `Cslib.Crypto.Protocols.FRI.evalLagrange`,
  `Cslib.Crypto.Protocols.FRI.lagrangePoly`: computable Lagrange evaluation and polynomial
  interpolation for the final low-degree check.
* `Cslib.Crypto.Protocols.FRI.padOracle`, `Cslib.Crypto.Protocols.FRI.restrictOracle`,
  `Cslib.Crypto.Protocols.FRI.friHonestWord`: active-domain oracle padding and iterated 2-to-1
  honest prover folding.
* `Cslib.Crypto.Protocols.FRI.friFinalCodeword`, `Cslib.Crypto.Protocols.FRI.friSingleAccepts`:
  interpolated final-round codeword and single-query verifier acceptance predicate.
* `Cslib.Crypto.Protocols.FRI.friIOP`: the `(m + 1)`-round `PublicCoinIOP` instantiation of FRI.

## Main results

* `Cslib.Crypto.Protocols.FRI.evalLagrange_mem_reedSolomon`,
  `Cslib.Crypto.Protocols.FRI.evalLagrange_eq_of_mem_reedSolomon`: Reed–Solomon membership and
  exact recovery of the final Lagrange interpolant.
* `Cslib.Crypto.Protocols.FRI.friHonestWord_mem_rsCode`: iterated honest folding preserves
  Reed–Solomon membership across all `m` rounds.
* `Cslib.Crypto.Protocols.FRI.length_friIOP_queries`,
  `Cslib.Crypto.Protocols.FRI.iopVerify_friIOP_eq_true_iff`: exact query complexity
  `kFinal + q * (3 * m + 2)` and exact characterization of `iopVerify` acceptance.
* `Cslib.Crypto.Protocols.FRI.friIOP_complete`,
  `Cslib.Crypto.Protocols.FRI.friBCS_verify_prove_eq_true`,
  `Cslib.Crypto.Protocols.FRI.friBCS_honestROMGame_eq_pure_true`: perfect completeness of FRI as
  an IOP, under deterministic BCS, and in the two-channel BCS random-oracle model.
* `Cslib.Crypto.Protocols.FRI.isCostBounded_bcsMTCost_friVerifyROM`: verifier Merkle hash query
  cost bound for BCS-compiled FRI.

## References

* [E. Ben-Sasson, I. Bentov, Y. Horesh, M. Riabzev, *Fast Reed–Solomon Interactive Oracle Proofs
  of Proximity*][BenSassonBentovHoreshRiabzev2018]
* [E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf, *Proximity Gaps for Reed–Solomon
  Codes*][BenSassonCarmonIshaiKoppartySaraf2020]
* [E. Ben-Sasson, A. Chiesa, N. Spooner, *Interactive Oracle Proofs*][BenSassonChiesaSpooner2016]
-/

public section

namespace Cslib.Crypto.Protocols.FRI

open Finset Polynomial Cslib.Code Cslib.Crypto.Protocols.BCS Cslib.OracleComp
open scoped BigOperators

section ParamsAndChallenges

/-- Public parameters for an `(m + 1)`-round 2-to-1 FRI protocol over a field `F`:
initial multiplicative coset `g * ⟨ω⟩` of size `2 ^ d`, `m ≤ d` folding rounds, final Reed–Solomon
dimension `1 ≤ kFinal ≤ 2 ^ (d - m)`, and `q` batched query repetitions. -/
structure FRIParams (F : Type) [Field F] where
  /-- Log-size of the initial multiplicative coset (`|L_0| = 2 ^ d`). -/
  d : ℕ
  /-- Number of 2-to-1 folding rounds (`m ≤ d`). -/
  m : ℕ
  /-- Final Reed–Solomon dimension after `m` folding rounds (`1 ≤ kFinal ≤ 2 ^ (d - m)`). -/
  kFinal : ℕ
  /-- Number of independent query starting indices sampled in the final round. -/
  q : ℕ
  /-- Nonzero multiplicative coset offset. -/
  g : F
  /-- Primitive `2 ^ d`-th root of unity generating the initial evaluation subgroup. -/
  ω : F
  /-- Folding rounds do not exceed the initial domain log-size. -/
  hm : m ≤ d
  /-- The final Reed–Solomon dimension is at least `1`. -/
  hkPos : 1 ≤ kFinal
  /-- The final Reed–Solomon dimension fits within the final domain `2 ^ (d - m)`. -/
  hkLe : kFinal ≤ 2 ^ (d - m)
  /-- The coset offset is nonzero. -/
  hg : g ≠ 0
  /-- The field does not have characteristic `2`. -/
  h2 : (2 : F) ≠ 0
  /-- `ω` is a primitive `2 ^ d`-th root of unity. -/
  hω : IsPrimitiveRoot ω (2 ^ d)

variable {F : Type} [Field F]

namespace FRIParams

/-- Active domain size `2 ^ (d - i)` at round `i`. -/
abbrev domainSize (params : FRIParams F) (i : ℕ) : ℕ :=
  2 ^ (params.d - i)

/-- Reed–Solomon dimension `kFinal * 2 ^ (m - i)` at round `i`. -/
abbrev dim (params : FRIParams F) (i : ℕ) : ℕ :=
  params.kFinal * 2 ^ (params.m - i)

/-- Coset evaluation map at round `i`. -/
abbrev eval (params : FRIParams F) (i : ℕ) : Fin (2 ^ (params.d - i)) → F :=
  cosetEval params.g params.ω params.d i

/-- Round-`i` Reed–Solomon code `RS[F, L_i, dim i]`. -/
noncomputable abbrev rsCode (params : FRIParams F) (i : ℕ) :
    Submodule F (Fin (2 ^ (params.d - i)) → F) :=
  reedSolomon (params.eval i) (params.dim i)

/-- Initial Reed–Solomon code on `OracleTable params.d F`. -/
noncomputable abbrev initialCode (params : FRIParams F) : Submodule F (OracleTable params.d F) :=
  params.rsCode 0

/-- Proximity language of input words at Hamming distance at most `e` from `initialCode`. -/
@[expose] def proximityLang [DecidableEq F] (params : FRIParams F) (e : ℕ) :
    Set (OracleTable params.d F) :=
  {f₀ | ∃ c ∈ params.initialCode, hammingDist f₀ c ≤ e}

/-- Honest completeness relation: input word `f₀` lies in `initialCode`. -/
@[expose] def completenessRel (params : FRIParams F) : OracleTable params.d F → Unit → Prop :=
  fun f₀ _ => f₀ ∈ params.initialCode

/-- Total number of oracle queries issued by the FRI verifier: `kFinal + q * (3 * m + 2)`. -/
abbrev queryCount (params : FRIParams F) : ℕ :=
  params.kFinal + params.q * (3 * params.m + 2)

/-- First `kFinal` evaluation points of the final coset `L_m`. -/
@[expose] def finalAnchorPoints (params : FRIParams F) : Fin params.kFinal → F :=
  fun t => params.eval params.m ⟨t.val, lt_of_lt_of_le t.isLt params.hkLe⟩

theorem finalAnchorPoints_injective (params : FRIParams F) :
    Function.Injective params.finalAnchorPoints := by
  intro t₁ t₂ h
  have hfin := cosetEval_injective params.hg params.hω params.hm h
  exact Fin.ext (Fin.mk.inj hfin)

theorem dim_eq_two_mul_succ (params : FRIParams F) {i : ℕ} (hi : i < params.m) :
    params.dim i = 2 * params.dim (i + 1) := by
  have hsub : params.m - i = (params.m - (i + 1)) + 1 := by omega
  simp only [dim, hsub, pow_succ']
  ring

theorem domainSize_eq_two_mul_succ (params : FRIParams F) {i : ℕ} (hi : i < params.d) :
    params.domainSize i = 2 * params.domainSize (i + 1) := by
  have hsub : params.d - i = (params.d - (i + 1)) + 1 := by omega
  simp only [domainSize, hsub, pow_succ']

end FRIParams

/-- Public-coin verifier challenge for each round of `friIOP`: carries a folding scalar
`foldScalar : F` (consumed in commit rounds `0, ..., m - 1`) and a batch of `q` query starting
positions `queryIdxs : Fin q → Fin (2 ^ d)` (consumed in the final round `m`). -/
@[ext] structure FRIChal (F : Type) (d q : ℕ) where
  /-- Folding challenge scalar used in commit rounds. -/
  foldScalar : F
  /-- Batch of `q` query starting indices used in the final round. -/
  queryIdxs : Fin q → Fin (2 ^ d)

/-- Equivalence between `FRIChal F d q` and `F × (Fin q → Fin (2 ^ d))`. -/
@[expose] def FRIChal.equivProd (F : Type) (d q : ℕ) :
    FRIChal F d q ≃ F × (Fin q → Fin (2 ^ d)) where
  toFun c := (c.foldScalar, c.queryIdxs)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [DecidableEq F] {d q : ℕ} : DecidableEq (FRIChal F d q) :=
  (FRIChal.equivProd F d q).decidableEq

instance [Fintype F] {d q : ℕ} : Fintype (FRIChal F d q) :=
  Fintype.ofEquiv _ (FRIChal.equivProd F d q).symm

instance [Nonempty F] {d q : ℕ} : Nonempty (FRIChal F d q) :=
  ⟨⟨Classical.choice ‹Nonempty F›, fun _ => ⟨0, Nat.pow_pos (by omega)⟩⟩⟩

omit [Field F] in
theorem card_friChal [Fintype F] (d q : ℕ) :
    Fintype.card (FRIChal F d q) = Fintype.card F * (2 ^ d) ^ q := by
  rw [Fintype.card_congr (FRIChal.equivProd F d q), Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin]

end ParamsAndChallenges

section LagrangeInterpolation

variable {F : Type} [Field F]

/-- Computable evaluation of the `t`-th Lagrange basis polynomial for nodes `pts : Fin k → F` at
`x : F`. -/
@[expose] def lagrangeBasisEval {k : ℕ} (pts : Fin k → F) (t : Fin k) (x : F) : F :=
  ∏ u ∈ Finset.univ.erase t, (x - pts u) / (pts t - pts u)

/-- Computable Lagrange interpolation evaluation at `x : F` from nodes `pts` and values `vals`. -/
@[expose] def evalLagrange {k : ℕ} (pts vals : Fin k → F) (x : F) : F :=
  ∑ t : Fin k, vals t * lagrangeBasisEval pts t x

/-- The `t`-th Lagrange basis polynomial for nodes `pts : Fin k → F`. -/
@[expose] noncomputable def lagrangeBasisPoly {k : ℕ} (pts : Fin k → F) (t : Fin k) : F[X] :=
  ∏ u ∈ Finset.univ.erase t, C (pts t - pts u)⁻¹ * (X - C (pts u))

/-- The Lagrange interpolating polynomial of degree `< k` for nodes `pts` and values `vals`. -/
@[expose] noncomputable def lagrangePoly {k : ℕ} (pts vals : Fin k → F) : F[X] :=
  ∑ t : Fin k, C (vals t) * lagrangeBasisPoly pts t

theorem eval_lagrangeBasisPoly {k : ℕ} (pts : Fin k → F) (t : Fin k) (x : F) :
    (lagrangeBasisPoly pts t).eval x = lagrangeBasisEval pts t x := by
  simp only [lagrangeBasisPoly, lagrangeBasisEval, eval_prod, eval_mul, eval_C, eval_sub, eval_X]
  refine Finset.prod_congr rfl fun u _ => ?_
  rw [div_eq_inv_mul]

theorem eval_lagrangePoly {k : ℕ} (pts vals : Fin k → F) (x : F) :
    (lagrangePoly pts vals).eval x = evalLagrange pts vals x := by
  simp only [lagrangePoly, evalLagrange, eval_finsetSum, eval_mul, eval_C, eval_lagrangeBasisPoly]

theorem degree_lagrangePoly_lt {k : ℕ} (hk : 1 ≤ k) (pts vals : Fin k → F) :
    (lagrangePoly pts vals).degree < k := by
  have hnat : (lagrangePoly pts vals).natDegree ≤ k - 1 := by
    refine natDegree_sum_le_of_forall_le _ _ fun t _ => ?_
    refine (natDegree_mul_le).trans ?_
    rw [natDegree_C, zero_add]
    calc (lagrangeBasisPoly pts t).natDegree
        ≤ ∑ u ∈ Finset.univ.erase t, (C (pts t - pts u)⁻¹ * (X - C (pts u))).natDegree := by
          dsimp only [lagrangeBasisPoly]
          exact natDegree_prod_le _ _
      _ ≤ ∑ _u ∈ Finset.univ.erase t, 1 := by
          refine Finset.sum_le_sum fun u _ => ?_
          refine (natDegree_mul_le).trans ?_
          rw [natDegree_C, zero_add]
          exact natDegree_X_sub_C_le (pts u)
      _ = (Finset.univ.erase t).card := by simp
      _ = k - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ t), Finset.card_univ,
          Fintype.card_fin]
  rw [degree_lt_iff_coeff_zero]
  intro n hn
  exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- Evaluating `evalLagrange pts vals` on any evaluation map `α : Fin n → F` always produces a
Reed–Solomon codeword of dimension `k` (provided `1 ≤ k`). -/
theorem evalLagrange_mem_reedSolomon {k n : ℕ} (hk : 1 ≤ k) (pts vals : Fin k → F)
    (α : Fin n → F) :
    (fun j => evalLagrange pts vals (α j)) ∈ reedSolomon α k := by
  refine mem_reedSolomon.mpr ⟨lagrangePoly pts vals, degree_lagrangePoly_lt hk pts vals, ?_⟩
  ext j
  exact eval_lagrangePoly pts vals (α j)

private theorem lagrangeBasisEval_self {k : ℕ} {pts : Fin k → F}
    (hpts : Function.Injective pts) (t : Fin k) :
    lagrangeBasisEval pts t (pts t) = 1 := by
  unfold lagrangeBasisEval
  refine Finset.prod_eq_one fun u hu => ?_
  have hne : u ≠ t := (Finset.mem_erase.mp hu).1
  have hsub : pts t - pts u ≠ 0 := sub_ne_zero.mpr (fun h => hne (hpts h.symm))
  exact div_self hsub

private theorem lagrangeBasisEval_of_ne {k : ℕ} {pts : Fin k → F} {t s : Fin k} (hst : s ≠ t) :
    lagrangeBasisEval pts t (pts s) = 0 := by
  unfold lagrangeBasisEval
  refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hst, Finset.mem_univ s⟩) ?_
  simp only [sub_self, zero_div]

theorem evalLagrange_node {k : ℕ} {pts : Fin k → F} (hpts : Function.Injective pts)
    (vals : Fin k → F) (s : Fin k) :
    evalLagrange pts vals (pts s) = vals s := by
  unfold evalLagrange
  have hterm : ∀ t : Fin k, vals t * lagrangeBasisEval pts t (pts s) =
      if t = s then vals s else 0 := by
    intro t
    by_cases hts : t = s
    · subst hts
      simp only [lagrangeBasisEval_self hpts, mul_one, ↓reduceIte]
    · simp only [lagrangeBasisEval_of_ne (Ne.symm hts), mul_zero, hts, ↓reduceIte]
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- For injective nodes `pts : Fin k → F` and any polynomial `p` of degree `< k`, Lagrange
interpolation from `(pts t, p.eval (pts t))` recovers `p` identically. -/
theorem lagrangePoly_eq_of_degree_lt {k : ℕ} (hk : 1 ≤ k) {pts : Fin k → F}
    (hpts : Function.Injective pts) {p : F[X]} (hp : p.degree < k) :
    lagrangePoly pts (fun t => p.eval (pts t)) = p := by
  classical
  set q : F[X] := lagrangePoly pts (fun t => p.eval (pts t)) - p
  have hq_deg : q.degree < k :=
    lt_of_le_of_lt (degree_sub_le _ _) (max_lt (degree_lagrangePoly_lt hk _ _) hp)
  by_contra hne
  have hq_ne : q ≠ 0 := sub_ne_zero.mpr hne
  have hsub : Finset.univ.image pts ⊆ q.roots.toFinset := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨s, -, rfl⟩
    rw [Multiset.mem_toFinset, mem_roots hq_ne, IsRoot.def]
    simp only [q, eval_sub, eval_lagrangePoly, evalLagrange_node hpts, sub_self]
  have hcard_img : (Finset.univ.image pts).card = k := by
    rw [Finset.card_image_of_injective _ hpts, Finset.card_univ, Fintype.card_fin]
  have hnat_lt : q.natDegree < k := natDegree_lt_iff_degree_lt hq_ne |>.mpr hq_deg
  have hle : k ≤ q.natDegree := by
    calc k = (Finset.univ.image pts).card := hcard_img.symm
      _ ≤ q.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ q.roots.card := Multiset.toFinset_card_le _
      _ ≤ q.natDegree := card_roots' q
  omega

/-- Exact recovery for codewords of `reedSolomon α k` interpolated from the first `k` nodes of `α`.
-/
theorem evalLagrange_eq_of_mem_reedSolomon {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    {α : Fin n → F} (hα : Function.Injective α) {f : Fin n → F} (hf : f ∈ reedSolomon α k)
    (j : Fin n) :
    evalLagrange (fun t : Fin k => α ⟨t.val, lt_of_lt_of_le t.isLt hkn⟩)
      (fun t : Fin k => f ⟨t.val, lt_of_lt_of_le t.isLt hkn⟩) (α j) = f j := by
  obtain ⟨p, hp, rfl⟩ := mem_reedSolomon.mp hf
  have hpts_inj : Function.Injective (fun t : Fin k => α ⟨t.val, lt_of_lt_of_le t.isLt hkn⟩) := by
    intro t₁ t₂ h
    exact Fin.ext (Fin.mk.inj (hα h))
  rw [← eval_lagrangePoly, lagrangePoly_eq_of_degree_lt hk hpts_inj hp]

end LagrangeInterpolation

section OraclePaddingAndHonestProver

variable {F : Type} [Field F]

/-- Pad a round-`i` word `f : Fin (2 ^ (d - i)) → F` with zeros to a depth-`d` `OracleTable d F`.
-/
@[expose] def padOracle {d i : ℕ} (f : Fin (2 ^ (d - i)) → F) : OracleTable d F :=
  fun idx => if h : idx.val < 2 ^ (d - i) then f ⟨idx.val, h⟩ else 0

/-- Restrict a depth-`d` `OracleTable d F` to the active round-`i` domain `Fin (2 ^ (d - i))`. -/
@[expose] def restrictOracle {d i : ℕ} (π : OracleTable d F) : Fin (2 ^ (d - i)) → F :=
  fun j => π ⟨j.val, lt_of_lt_of_le j.isLt (Nat.pow_le_pow_right (by omega) (Nat.sub_le d i))⟩

theorem padOracle_apply_of_lt {d i : ℕ} (f : Fin (2 ^ (d - i)) → F) (idx : Fin (2 ^ d))
    (hlt : idx.val < 2 ^ (d - i)) :
    padOracle (i := i) f idx = f ⟨idx.val, hlt⟩ := by
  simp only [padOracle, hlt, ↓reduceDIte]

theorem restrictOracle_padOracle {d i : ℕ} (f : Fin (2 ^ (d - i)) → F) :
    restrictOracle (i := i) (padOracle (d := d) f) = f := by
  ext j
  simp only [restrictOracle, padOracle, j.isLt, ↓reduceDIte, Fin.eta]

/-- Helper embedding `Fin (2 * 2 ^ (d - (j + 1))) → Fin (2 ^ (d - j))` for `j < d`. -/
@[expose] def reindexDouble {d j : ℕ} (hj : j < d) (idx : Fin (2 * 2 ^ (d - (j + 1)))) :
    Fin (2 ^ (d - j)) :=
  ⟨idx.val, by
    have hsplit : 2 ^ (d - j) = 2 * 2 ^ (d - (j + 1)) := by
      have hsub : d - j = (d - (j + 1)) + 1 := by omega
      rw [hsub, pow_succ']
    omega⟩

/-- Iterated 2-to-1 honest FRI prover word at round `j ≤ m`, computed causally from the initial
oracle `f₀` and the first `j` folding scalars `zs : Fin j → F`. -/
@[expose] def friHonestWord (params : FRIParams F) (f₀ : OracleTable params.d F) :
    (j : ℕ) → j ≤ params.m → (Fin j → F) → Fin (2 ^ (params.d - j)) → F
  | 0, _, _ => f₀
  | j + 1, hj, zs =>
    let prev := friHonestWord params f₀ j (Nat.le_of_succ_le hj) (fun i => zs i.castSucc)
    have hjd : j < params.d := lt_of_lt_of_le (Nat.lt_of_succ_le hj) params.hm
    fold2 (params.g ^ (2 ^ j)) (params.ω ^ (2 ^ j))
      (fun idx : Fin (2 * 2 ^ (params.d - (j + 1))) => prev (reindexDouble hjd idx))
      (zs (Fin.last j))

/-- Honest folding satisfies the local 2-to-1 fiber equation at every coordinate of round `j + 1`.
-/
theorem friHonestWord_succ_apply (params : FRIParams F) (f₀ : OracleTable params.d F)
    {j : ℕ} (hj : j + 1 ≤ params.m) (zs : Fin (j + 1) → F)
    (idx : Fin (2 ^ (params.d - (j + 1)))) :
    friHonestWord params f₀ (j + 1) hj zs idx =
      fold2Fiber
        (friHonestWord params f₀ j (Nat.le_of_succ_le hj) (fun i => zs i.castSucc)
          ⟨idx.val, lt_of_lt_of_le idx.isLt
            (Nat.pow_le_pow_right (by omega) (by omega))⟩)
        (friHonestWord params f₀ j (Nat.le_of_succ_le hj) (fun i => zs i.castSucc)
          ⟨idx.val + 2 ^ (params.d - (j + 1)), by
            have hjd : j < params.d := lt_of_lt_of_le (Nat.lt_of_succ_le hj) params.hm
            have hsplit := params.domainSize_eq_two_mul_succ hjd
            dsimp only [FRIParams.domainSize] at hsplit
            omega⟩)
        (params.eval j ⟨idx.val, lt_of_lt_of_le idx.isLt
          (Nat.pow_le_pow_right (by omega) (by omega))⟩)
        (zs (Fin.last j)) := by
  rfl

/-- **Reed–Solomon invariance of honest FRI folding**: if `f₀ ∈ params.initialCode`, then every
honest prover round word `friHonestWord params f₀ j hj zs` lies in `params.rsCode j`. -/
theorem friHonestWord_mem_rsCode (params : FRIParams F) {f₀ : OracleTable params.d F}
    (hf₀ : f₀ ∈ params.initialCode) :
    ∀ (j : ℕ) (hj : j ≤ params.m) (zs : Fin j → F),
      friHonestWord params f₀ j hj zs ∈ params.rsCode j
  | 0, _, _ => hf₀
  | j + 1, hj, zs => by
    have ih := friHonestWord_mem_rsCode params hf₀ j (Nat.le_of_succ_le hj)
      (fun i => zs i.castSucc)
    have hjd : j < params.d := lt_of_lt_of_le (Nat.lt_of_succ_le hj) params.hm
    have hjm : j < params.m := Nat.lt_of_succ_le hj
    have hsplit : 2 ^ (params.d - j) = 2 * 2 ^ (params.d - (j + 1)) :=
      params.domainSize_eq_two_mul_succ hjd
    have hdim : params.dim j = 2 * params.dim (j + 1) := params.dim_eq_two_mul_succ hjm
    have hprev_rs :
        (fun idx : Fin (2 * 2 ^ (params.d - (j + 1))) =>
          friHonestWord params f₀ j (Nat.le_of_succ_le hj) (fun i => zs i.castSucc)
            (reindexDouble hjd idx)) ∈
        reedSolomon
          (cosetPoint (params.g ^ (2 ^ j)) (params.ω ^ (2 ^ j)) (2 * 2 ^ (params.d - (j + 1))))
          (2 * params.dim (j + 1)) := by
      obtain ⟨p, hp, hpeq⟩ := mem_reedSolomon.mp ih
      refine mem_reedSolomon.mpr ⟨p, hdim ▸ hp, ?_⟩
      ext idx
      have hval := congrFun hpeq (reindexDouble hjd idx)
      exact hval
    have hωj : IsPrimitiveRoot (params.ω ^ (2 ^ j)) (2 * 2 ^ (params.d - (j + 1))) :=
      hsplit ▸ isPrimitiveRoot_pow_two_pow params.hω hjd.le
    have hfolded := fold2_mem_reedSolomon (pow_ne_zero _ params.hg) params.h2
      (Nat.pow_pos (by omega)) hωj hprev_rs (zs (Fin.last j))
    have hgpow : (params.g ^ (2 ^ j)) ^ 2 = params.g ^ (2 ^ (j + 1)) := by
      rw [← pow_mul, ← pow_succ]
    have hωpow : (params.ω ^ (2 ^ j)) ^ 2 = params.ω ^ (2 ^ (j + 1)) := by
      rw [← pow_mul, ← pow_succ]
    simpa only [friHonestWord, FRIParams.rsCode, FRIParams.eval, cosetEval, hgpow, hωpow] using
      hfolded

/-- Prefix challenge independence: `friHonestWord` depends only on `zs` up to round `j`. -/
theorem friHonestWord_congr (params : FRIParams F) (f₀ : OracleTable params.d F) :
    ∀ (j : ℕ) (hj : j ≤ params.m) {zs₁ zs₂ : Fin j → F},
      (∀ i : Fin j, zs₁ i = zs₂ i) →
        friHonestWord params f₀ j hj zs₁ = friHonestWord params f₀ j hj zs₂
  | 0, _, _, _, _ => rfl
  | j + 1, hj, zs₁, zs₂, h => by
    simp only [friHonestWord]
    have ih := friHonestWord_congr params f₀ j (Nat.le_of_succ_le hj)
      (fun i => h i.castSucc)
    rw [ih, h (Fin.last j)]

end OraclePaddingAndHonestProver

section FRIProtocol

variable {F : Type} [Field F]

/-- Active-domain folded index `s % 2 ^ (d - (i + 1))` for folding round `i : Fin m`. -/
@[expose] def friFoldedFin (params : FRIParams F) (i : Fin params.m) (s : Fin (2 ^ params.d)) :
    Fin (2 ^ (params.d - (i.val + 1))) :=
  ⟨s.val % 2 ^ (params.d - (i.val + 1)), Nat.mod_lt _ (Nat.pow_pos (by omega))⟩

/-- Positive fiber index `s % 2 ^ (d - (i + 1))` inside `Fin (2 ^ d)`. -/
@[expose] def friRoundPosIdx (params : FRIParams F) (i : Fin params.m) (s : Fin (2 ^ params.d)) :
    Fin (2 ^ params.d) :=
  ⟨s.val % 2 ^ (params.d - (i.val + 1)),
    lt_of_lt_of_le (Nat.mod_lt _ (Nat.pow_pos (by omega)))
      (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))⟩

/-- Negative fiber index `s % 2 ^ (d - (i + 1)) + 2 ^ (d - (i + 1))` inside `Fin (2 ^ d)`. -/
@[expose] def friRoundNegIdx (params : FRIParams F) (i : Fin params.m) (s : Fin (2 ^ params.d)) :
    Fin (2 ^ params.d) :=
  ⟨s.val % 2 ^ (params.d - (i.val + 1)) + 2 ^ (params.d - (i.val + 1)), by
    have hid : i.val < params.d := lt_of_lt_of_le i.isLt params.hm
    have hsplit := params.domainSize_eq_two_mul_succ hid
    dsimp only [FRIParams.domainSize] at hsplit
    have hmod := Nat.mod_lt s.val (Nat.pow_pos (a := 2) (n := params.d - (i.val + 1)) (by omega))
    have hle : 2 ^ (params.d - i.val) ≤ 2 ^ params.d :=
      Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
    omega⟩

/-- Active-domain positive fiber index inside `Fin (2 ^ (d - i))`. -/
@[expose] def friRoundPosFin (params : FRIParams F) (i : Fin params.m) (s : Fin (2 ^ params.d)) :
    Fin (2 ^ (params.d - i.val)) :=
  ⟨s.val % 2 ^ (params.d - (i.val + 1)),
    lt_of_lt_of_le (Nat.mod_lt _ (Nat.pow_pos (by omega)))
      (Nat.pow_le_pow_right (by omega) (by omega))⟩

/-- Final-round active index `s % 2 ^ (d - m)` inside `Fin (2 ^ (d - m))`. -/
@[expose] def friFinalFin (params : FRIParams F) (s : Fin (2 ^ params.d)) :
    Fin (2 ^ (params.d - params.m)) :=
  ⟨s.val % 2 ^ (params.d - params.m), Nat.mod_lt _ (Nat.pow_pos (by omega))⟩

/-- Final-round query index `s % 2 ^ (d - m)` inside `Fin (2 ^ d)`. -/
@[expose] def friFinalIdx (params : FRIParams F) (s : Fin (2 ^ params.d)) :
    Fin (2 ^ params.d) :=
  ⟨s.val % 2 ^ (params.d - params.m),
    lt_of_lt_of_le (Nat.mod_lt _ (Nat.pow_pos (by omega)))
      (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))⟩

/-- Header queries reading the first `kFinal` entries of the final oracle `π_m`. -/
@[expose] def friHeaderQueries (params : FRIParams F) :
    List (Fin (params.m + 1) × Fin (2 ^ params.d)) :=
  List.ofFn fun t : Fin params.kFinal =>
    (Fin.last params.m,
      ⟨t.val, lt_of_lt_of_le (lt_of_lt_of_le t.isLt params.hkLe)
        (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))⟩)

@[simp]
theorem length_friHeaderQueries (params : FRIParams F) :
    (friHeaderQueries params).length = params.kFinal := by
  simp [friHeaderQueries]

/-- Folding-chain queries along a list of rounds `rounds` followed by the final-round check at
`friFinalIdx params s`. -/
@[expose] def friFoldQueriesList (params : FRIParams F) (s : Fin (2 ^ params.d)) :
    List (Fin params.m) → List (Fin (params.m + 1) × Fin (2 ^ params.d))
  | [] => [(Fin.last params.m, friFinalIdx params s)]
  | i :: is =>
    (i.castSucc, friRoundPosIdx params i s) ::
    (i.castSucc, friRoundNegIdx params i s) ::
    (i.succ, friRoundPosIdx params i s) ::
    friFoldQueriesList params s is

theorem length_friFoldQueriesList (params : FRIParams F) (s : Fin (2 ^ params.d))
    (rounds : List (Fin params.m)) :
    (friFoldQueriesList params s rounds).length = 3 * rounds.length + 1 := by
  induction rounds with
  | nil => rfl
  | cons _ _ ih =>
    simp only [friFoldQueriesList, List.length_cons, ih]
    omega

/-- All oracle queries for a single query repetition starting at `s : Fin (2 ^ d)`:
round-0 binding query `(0, s)`, all `m` folding triples, and the final-round query. -/
@[expose] def friSingleQueries (params : FRIParams F) (s : Fin (2 ^ params.d)) :
    List (Fin (params.m + 1) × Fin (2 ^ params.d)) :=
  (⟨0, Nat.zero_lt_succ params.m⟩, s) :: friFoldQueriesList params s (List.finRange params.m)

@[simp]
theorem length_friSingleQueries (params : FRIParams F) (s : Fin (2 ^ params.d)) :
    (friSingleQueries params s).length = 3 * params.m + 2 := by
  simp only [friSingleQueries, List.length_cons, length_friFoldQueriesList, List.length_finRange]

/-- Concatenated queries for a list of repetition indices `reps : List (Fin q)`. -/
@[expose] def friRepQueriesList (params : FRIParams F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q) :
    List (Fin params.q) → List (Fin (params.m + 1) × Fin (2 ^ params.d))
  | [] => []
  | a :: as =>
    friSingleQueries params ((chals (Fin.last params.m)).queryIdxs a) ++
      friRepQueriesList params chals as

theorem length_friRepQueriesList (params : FRIParams F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q) (reps : List (Fin params.q)) :
    (friRepQueriesList params chals reps).length = reps.length * (3 * params.m + 2) := by
  induction reps with
  | nil => simp [friRepQueriesList]
  | cons _ _ ih =>
    simp only [friRepQueriesList, List.length_append, length_friSingleQueries, ih, List.length_cons]
    ring

/-- Full query list of the FRI verifier: `kFinal` final-oracle interpolation anchors followed by `q`
query repetitions. -/
@[expose] def friQueries (params : FRIParams F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q) :
    List (Fin (params.m + 1) × Fin (2 ^ params.d)) :=
  friHeaderQueries params ++ friRepQueriesList params chals (List.finRange params.q)

theorem length_friQueries (params : FRIParams F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q) :
    (friQueries params chals).length = params.queryCount := by
  simp only [friQueries, List.length_append, length_friHeaderQueries, length_friRepQueriesList,
    List.length_finRange, FRIParams.queryCount]

/-- Final-round Reed–Solomon codeword interpolated from the first `kFinal` entries of `πFinal`. -/
@[expose] def friFinalCodeword (params : FRIParams F) (πFinal : OracleTable params.d F) :
    Fin (2 ^ (params.d - params.m)) → F :=
  fun j =>
    evalLagrange params.finalAnchorPoints
      (fun t : Fin params.kFinal =>
        πFinal ⟨t.val, lt_of_lt_of_le (lt_of_lt_of_le t.isLt params.hkLe)
          (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))⟩)
      (params.eval params.m j)

/-- For ANY arbitrary oracle table `πFinal`, `friFinalCodeword params πFinal` lies in
`params.rsCode params.m`. -/
theorem friFinalCodeword_mem_rsCode (params : FRIParams F) (πFinal : OracleTable params.d F) :
    friFinalCodeword params πFinal ∈ params.rsCode params.m := by
  have hdim : params.dim params.m = params.kFinal := by simp [FRIParams.dim]
  rw [FRIParams.rsCode, hdim]
  exact evalLagrange_mem_reedSolomon params.hkPos _ _ _

/-- Check the folding chain and final Lagrange equation against the answer list for a single
repetition starting at `s`. -/
@[expose] def friCheckFoldList [DecidableEq F] (params : FRIParams F)
    (headerVals : Fin params.kFinal → F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q)
    (s : Fin (2 ^ params.d)) : List (Fin params.m) → List F → Bool
  | [], [yFinal] =>
    decide (yFinal = evalLagrange params.finalAnchorPoints headerVals
      (params.eval params.m (friFinalFin params s)))
  | i :: is, yPos :: yNeg :: yNext :: rest =>
    decide (fold2Fiber yPos yNeg (params.eval i.val (friRoundPosFin params i s))
      (chals i.castSucc).foldScalar = yNext) &&
      friCheckFoldList params headerVals chals s is rest
  | _, _ => false

/-- Check a single repetition's answer block: round-0 binding to `stmt s` plus all folding and
final-codeword checks. -/
@[expose] def friCheckSingle [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F) (headerVals : Fin params.kFinal → F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q)
    (s : Fin (2 ^ params.d)) : List F → Bool
  | y0 :: rest =>
    decide (y0 = stmt s) &&
      friCheckFoldList params headerVals chals s (List.finRange params.m) rest
  | [] => false

/-- Check all repetitions in `reps` by consuming fixed-size blocks of length `3 * m + 2`. -/
@[expose] def friCheckRepsList [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F) (headerVals : Fin params.kFinal → F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q) :
    List (Fin params.q) → List F → Bool
  | [], [] => true
  | a :: as, ans =>
    let blockLen := 3 * params.m + 2
    friCheckSingle params stmt headerVals chals ((chals (Fin.last params.m)).queryIdxs a)
        (ans.take blockLen) &&
      friCheckRepsList params stmt headerVals chals as (ans.drop blockLen)
  | _, _ => false

/-- FRI verifier decision procedure operating purely on `stmt`, `chals`, and the flat list of
queried oracle answers. -/
@[expose] def friDecide [DecidableEq F] (params : FRIParams F) (stmt : OracleTable params.d F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q) (answers : List F) : Bool :=
  decide (answers.length = params.queryCount) &&
    let headerVals : Fin params.kFinal → F := fun t => (answers.take params.kFinal).getD t.val 0
    friCheckRepsList params stmt headerVals chals (List.finRange params.q)
      (answers.drop params.kFinal)

/-- **Multi-round 2-to-1 FRI as a `PublicCoinIOP`**:
* `m + 1` rounds over depth-`d` oracle tables `OracleTable d F`.
* Honest prover sends `padOracle (friHonestWord ...)` using the previous rounds' `foldScalar`s.
* Verifier queries `kFinal + q * (3 * m + 2)` entries and checks round-0 binding to `stmt`,
  all `m` folding checks, and the final degree-`< kFinal` Lagrange check. -/
@[expose] def friIOP [DecidableEq F] (params : FRIParams F) :
    PublicCoinIOP (params.m + 1) params.d (OracleTable params.d F) Unit F
      (FRIChal F params.d params.q) where
  proveRound j stmt _ prevChals :=
    padOracle (friHonestWord params stmt j.val (Nat.le_of_lt_succ j.isLt)
      (fun i => (prevChals i).foldScalar))
  queries _ chals := friQueries params chals
  decide stmt chals answers := friDecide params stmt chals answers

/-- Exact query length of `friIOP`: `kFinal + q * (3 * m + 2)` for every statement and challenge
vector. -/
theorem length_friIOP_queries [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q) :
    ((friIOP params).queries stmt chals).length = params.queryCount :=
  length_friQueries params chals

/-- Clean mathematical acceptance predicate for a single query starting index `s : Fin (2 ^ d)`:
round-0 binding `oracles 0 s = stmt s`, all `m` 2-to-1 folding checks along the squaring chain of
`s`, and final-round agreement with `friFinalCodeword params (oracles (Fin.last m))`. -/
@[expose] def friSingleAccepts (params : FRIParams F) (stmt : OracleTable params.d F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q)
    (oracles : Fin (params.m + 1) → OracleTable params.d F) (s : Fin (2 ^ params.d)) : Prop :=
  oracles ⟨0, Nat.zero_lt_succ params.m⟩ s = stmt s ∧
  (∀ i : Fin params.m,
    fold2Fiber
      (oracles i.castSucc (friRoundPosIdx params i s))
      (oracles i.castSucc (friRoundNegIdx params i s))
      (params.eval i.val (friRoundPosFin params i s))
      (chals i.castSucc).foldScalar =
    oracles i.succ (friRoundPosIdx params i s)) ∧
  oracles (Fin.last params.m) (friFinalIdx params s) =
    friFinalCodeword params (oracles (Fin.last params.m)) (friFinalFin params s)

private theorem friCheckFoldList_map [DecidableEq F] (params : FRIParams F)
    (headerVals : Fin params.kFinal → F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q)
    (oracles : Fin (params.m + 1) → OracleTable params.d F) (s : Fin (2 ^ params.d))
    (rounds : List (Fin params.m)) :
    friCheckFoldList params headerVals chals s rounds
        ((friFoldQueriesList params s rounds).map fun p => oracles p.1 p.2) = true ↔
      (∀ i ∈ rounds,
        fold2Fiber
          (oracles i.castSucc (friRoundPosIdx params i s))
          (oracles i.castSucc (friRoundNegIdx params i s))
          (params.eval i.val (friRoundPosFin params i s))
          (chals i.castSucc).foldScalar =
        oracles i.succ (friRoundPosIdx params i s)) ∧
      oracles (Fin.last params.m) (friFinalIdx params s) =
        evalLagrange params.finalAnchorPoints headerVals
          (params.eval params.m (friFinalFin params s)) := by
  induction rounds with
  | nil =>
    simp [friFoldQueriesList, friCheckFoldList]
  | cons i is ih =>
    simp only [friFoldQueriesList, List.map_cons, friCheckFoldList, Bool.and_eq_true,
      decide_eq_true_eq, ih, List.mem_cons, forall_eq_or_imp, and_assoc]

private theorem friCheckSingle_map [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q)
    (oracles : Fin (params.m + 1) → OracleTable params.d F) (s : Fin (2 ^ params.d)) :
    friCheckSingle params stmt
        (fun t : Fin params.kFinal =>
          oracles (Fin.last params.m)
            ⟨t.val, lt_of_lt_of_le (lt_of_lt_of_le t.isLt params.hkLe)
              (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))⟩)
        chals s ((friSingleQueries params s).map fun p => oracles p.1 p.2) = true ↔
      friSingleAccepts params stmt chals oracles s := by
  simp only [friSingleQueries, List.map_cons, friCheckSingle, Bool.and_eq_true, decide_eq_true_eq,
    friCheckFoldList_map, List.mem_finRange, true_implies, friSingleAccepts, friFinalCodeword]

private theorem friCheckRepsList_map [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q)
    (oracles : Fin (params.m + 1) → OracleTable params.d F) (reps : List (Fin params.q)) :
    friCheckRepsList params stmt
        (fun t : Fin params.kFinal =>
          oracles (Fin.last params.m)
            ⟨t.val, lt_of_lt_of_le (lt_of_lt_of_le t.isLt params.hkLe)
              (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))⟩)
        chals reps ((friRepQueriesList params chals reps).map fun p => oracles p.1 p.2) = true ↔
      ∀ a ∈ reps,
        friSingleAccepts params stmt chals oracles ((chals (Fin.last params.m)).queryIdxs a) := by
  induction reps with
  | nil =>
    simp [friRepQueriesList, friCheckRepsList]
  | cons a as ih =>
    have hlen :
        ((friSingleQueries params ((chals (Fin.last params.m)).queryIdxs a)).map
          fun p => oracles p.1 p.2).length = 3 * params.m + 2 := by
      simp [length_friSingleQueries]
    simp only [friRepQueriesList, List.map_append, friCheckRepsList, List.take_left' hlen,
      List.drop_left' hlen, Bool.and_eq_true, friCheckSingle_map, ih, List.mem_cons,
      forall_eq_or_imp]

/-- **Exact characterization of FRI IOP verification**: `iopVerify (friIOP params)` accepts
`oracles` on `(stmt, chals)` if and only if every queried starting position
`(chals (Fin.last m)).queryIdxs a` satisfies `friSingleAccepts`. -/
theorem iopVerify_friIOP_eq_true_iff [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q)
    (oracles : Fin (params.m + 1) → OracleTable params.d F) :
    iopVerify (friIOP params) stmt chals oracles = true ↔
      ∀ a : Fin params.q,
        friSingleAccepts params stmt chals oracles ((chals (Fin.last params.m)).queryIdxs a) := by
  have hhdr_len :
      ((friHeaderQueries params).map fun p => oracles p.1 p.2).length = params.kFinal := by
    simp [length_friHeaderQueries]
  have hhdr_getD :
      (fun t : Fin params.kFinal =>
        (((friHeaderQueries params).map fun p => oracles p.1 p.2)).getD t.val 0) =
      fun t : Fin params.kFinal =>
        oracles (Fin.last params.m)
          ⟨t.val, lt_of_lt_of_le (lt_of_lt_of_le t.isLt params.hkLe)
            (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))⟩ := by
    funext t
    have hlt : t.val < ((friHeaderQueries params).map fun p => oracles p.1 p.2).length := by
      simpa only [hhdr_len] using t.isLt
    rw [List.getD_eq_getElem _ _ hlt]
    simp [friHeaderQueries]
  have hlen_all :
      ((friQueries params chals).map fun p => oracles p.1 p.2).length = params.queryCount := by
    simp [length_friQueries]
  simp only [iopVerify, iopAnswers, friIOP, friDecide, hlen_all, decide_true, Bool.true_and]
  simp only [friQueries, List.map_append, List.take_left' hhdr_len, List.drop_left' hhdr_len,
    hhdr_getD, friCheckRepsList_map, List.mem_finRange, true_implies]

/-- **Perfect completeness of the FRI IOP**: for every codeword `f₀ ∈ params.initialCode` and every
challenge vector `chals`, the FRI verifier accepts the honest prover's oracle tables. -/
theorem friIOP_complete [DecidableEq F] (params : FRIParams F) :
    IOPCompleteness (friIOP params) params.completenessRel := by
  intro f₀ _ hf₀ chals
  rw [iopVerify_friIOP_eq_true_iff]
  intro a
  set s := (chals (Fin.last params.m)).queryIdxs a
  refine ⟨?_, ?_, ?_⟩
  · simp only [iopProverOracles, friIOP, padOracle, Nat.sub_zero, s.isLt, ↓reduceDIte,
      friHonestWord, Fin.eta]
  · intro i
    have hi_le : i.val + 1 ≤ params.m := i.isLt
    have hpos_lt : (friRoundPosIdx params i s).val < 2 ^ (params.d - i.val) :=
      (friRoundPosFin params i s).isLt
    have hneg_lt : (friRoundNegIdx params i s).val < 2 ^ (params.d - i.val) := by
      have hid : i.val < params.d := lt_of_lt_of_le i.isLt params.hm
      have hsplit := params.domainSize_eq_two_mul_succ hid
      dsimp only [FRIParams.domainSize] at hsplit
      have hmod := Nat.mod_lt s.val (Nat.pow_pos (a := 2) (n := params.d - (i.val + 1)) (by omega))
      dsimp only [friRoundNegIdx]
      omega
    have hnext_lt : (friRoundPosIdx params i s).val < 2 ^ (params.d - (i.val + 1)) :=
      (friFoldedFin params i s).isLt
    simp only [iopProverOracles, friIOP, Fin.val_castSucc, Fin.val_succ,
      padOracle_apply_of_lt _ _ hpos_lt, padOracle_apply_of_lt _ _ hneg_lt,
      padOracle_apply_of_lt _ _ hnext_lt]
    rw [friHonestWord_succ_apply]
    have hcongr :
        friHonestWord params f₀ i.val (Nat.le_of_succ_le hi_le)
          (fun k : Fin i.val => (prefixChallenges chals i.succ k.castSucc).foldScalar) =
        friHonestWord params f₀ i.val (Nat.le_of_lt_succ i.castSucc.isLt)
          (fun k : Fin i.val => (prefixChallenges chals i.castSucc k).foldScalar) :=
      friHonestWord_congr params f₀ i.val _ fun k => rfl
    rw [hcongr]
    rfl
  · have hfin_lt : (friFinalIdx params s).val < 2 ^ (params.d - params.m) :=
      (friFinalFin params s).isLt
    have hmem :
        friHonestWord params f₀ params.m le_rfl
          (fun k => (prefixChallenges chals (Fin.last params.m) k).foldScalar) ∈
        params.rsCode params.m :=
      friHonestWord_mem_rsCode params hf₀ params.m le_rfl _
    have hdim : params.dim params.m = params.kFinal := by simp [FRIParams.dim]
    rw [FRIParams.rsCode, hdim] at hmem
    simp only [iopProverOracles, friIOP, Fin.val_last, padOracle_apply_of_lt _ _ hfin_lt,
      friFinalCodeword]
    have hhdr :
        (fun t : Fin params.kFinal =>
          padOracle (i := params.m)
            (friHonestWord params f₀ params.m le_rfl
              (fun k => (prefixChallenges chals (Fin.last params.m) k).foldScalar))
            ⟨t.val, lt_of_lt_of_le (lt_of_lt_of_le t.isLt params.hkLe)
              (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))⟩) =
        fun t : Fin params.kFinal =>
          friHonestWord params f₀ params.m le_rfl
            (fun k => (prefixChallenges chals (Fin.last params.m) k).foldScalar)
            ⟨t.val, lt_of_lt_of_le t.isLt params.hkLe⟩ := by
      funext t
      exact padOracle_apply_of_lt _ _ (lt_of_lt_of_le t.isLt params.hkLe)
    rw [hhdr]
    exact (evalLagrange_eq_of_mem_reedSolomon params.hkPos params.hkLe
      (cosetEval_injective params.hg params.hω params.hm) hmem (friFinalFin params s)).symm

/-- **Perfect deterministic BCS completeness for FRI**: for any hash function `H k`, any
Fiat–Shamir function `hFS`, and any symbol encoding `encSym`, `bcsVerify` accepts `bcsProve` on
every codeword `f₀ ∈ params.initialCode`. -/
theorem friBCS_verify_prove_eq_true [DecidableEq F] (params : FRIParams F)
    (H : List Bool → List Bool → List Bool) (k : List Bool) (encSym : F → List Bool)
    (hFS : OracleTable params.d F → List (List Bool) → FRIChal F params.d params.q)
    {f₀ : OracleTable params.d F} (hf₀ : f₀ ∈ params.initialCode) :
    bcsVerify (friIOP params) H k encSym hFS f₀
      (bcsProve (friIOP params) H k encSym hFS f₀ ()) = true :=
  bcsVerify_bcsProve_eq_true (friIOP_complete params) H k encSym hFS hf₀

/-- **Perfect BCS ROM completeness for FRI**: in the lazy two-channel random-oracle model with any
digest length `σ`, the honest BCS-FRI game outputs `PMF.pure true` for every codeword
`f₀ ∈ params.initialCode`. -/
theorem friBCS_honestROMGame_eq_pure_true [DecidableEq F] [Fintype F] (params : FRIParams F)
    (encSym : F → List Bool) {f₀ : OracleTable params.d F} (hf₀ : f₀ ∈ params.initialCode)
    (σ : ℕ) :
    bcsHonestROMGame (friIOP params) encSym f₀ () σ = PMF.pure true :=
  bcsHonestROMGame_eq_pure_true (friIOP_complete params) encSym hf₀ σ

/-- **Succinct verifier Merkle query cost bound for BCS-compiled FRI**: for any proof `prf` whose
opening paths have length at most `L_path`, `bcsVerifyROM` makes at most
`params.queryCount * (L_path + 1) = (kFinal + q * (3 * m + 2)) * (L_path + 1)` Merkle hash queries.
-/
theorem isCostBounded_bcsMTCost_friVerifyROM [DecidableEq F] (params : FRIParams F)
    (encSym : F → List Bool) (stmt : OracleTable params.d F)
    (prf : BCSProof (params.m + 1) F) {L_path : ℕ}
    (hops : ∀ op ∈ prf.openings, op.path.length ≤ L_path) :
    IsCostBounded bcsMTCost (bcsVerifyROM (friIOP params) encSym stmt prf)
      (params.queryCount * (L_path + 1)) :=
  isCostBounded_bcsMTCost_bcsVerifyROM_of_queries_le (friIOP params) encSym stmt prf
    (fun chals => (length_friIOP_queries params stmt chals).le) hops

end FRIProtocol

end Cslib.Crypto.Protocols.FRI
