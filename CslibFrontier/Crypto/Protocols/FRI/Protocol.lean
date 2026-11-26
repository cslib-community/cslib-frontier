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
public import CslibFrontier.Foundations.Data.Polynomial.LagrangeEval
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn

/-!
# Multi-Round Smooth and 2-to-1 FRI as a Public-Coin Interactive Oracle Proof

This module instantiates multi-round Fast Reed–Solomon Interactive Oracle Proofs of Proximity
(FRI) with arbitrary per-round strict 2-smooth folding arities `l⁽ⁱ⁾ = 2 ^ stepLog i ≥ 2`
(`FRISmoothParams`, `friSmoothIOP`) together with the fixed 2-to-1 specialization (`FRIParams`,
`friIOP`) ([BenSassonBentovHoreshRiabzev2018], with fixed localization parameter in the full
version ECCC TR17-134, Remark 3.1, p. 13; [BenSassonCarmonIshaiKoppartySaraf2020], Section 8.2 on
printed pp. 36–38 for round-dependent arities, with the fibers of Eq. (8.1), the interpolation map
defined right after it, and its evaluation in Eq. (8.2) on printed p. 37, and the first-entries
final anchor convention on printed p. 38) directly as a `Cslib.Crypto.Protocols.BCS.PublicCoinIOP`
compatible with the Ben-Sasson–Chiesa–Spooner (BCS) random-oracle compiler
([BenSassonChiesaSpooner2016]).

## Protocol layout

Given `params : FRISmoothParams F` with initial coset size `2 ^ d`, `m` folding rounds with
per-round log-arities `stepLog : Fin m → ℕ` (`1 ≤ stepLog i`, cumulative log-reduction
`totalLog = ∑ i, stepLog i ≤ d`), final Reed–Solomon dimension
`1 ≤ kFinal ≤ 2 ^ (d - totalLog)`, and `q` independent query repetitions (and specializing to
2-to-1 `FRIParams` via `FRIParams.toSmooth` with `stepLog := fun _ => 1` and
`friIOP_eq_friSmoothIOP`):

* **Rounds & tables.** The IOP runs for `m + 1` rounds over depth-`d` oracle tables
  `OracleTable d F = Fin (2 ^ d) → F`. The active domain of round `j` has size
  `2 ^ (d - cumLog j)` and sits in the prefix `< 2 ^ (d - cumLog j)` of the table (padded by `0`
  outside), with invariant Reed–Solomon rate `dim j / domainSize j = dim 0 / 2 ^ d`.
* **Challenges.** Each round draws a uniform challenge `FRIChal F d q` carrying both a folding
  scalar `foldScalar : F` and a batch of `q` query starting positions
  `queryIdxs : Fin q → Fin (2 ^ d)`. Commit rounds `0, ..., m - 1` use only `foldScalar`, while the
  final round `m` uses `queryIdxs`. Bundling all `q` independent query positions into the single
  final round preserves exponential `(1 - δ) ^ q` query-phase soundness under the uniform
  per-round escape bound of `Cslib.Crypto.Protocols.BCS.bcsROMSoundness_bound`.
* **Round-0 binding, final anchor convention, and query accounting.** Rather than sending explicit
  final polynomial coefficients, the verifier reads the first `kFinal` entries of the final oracle
  `π_m` as interpolation anchors to define a degree-`< kFinal` Reed–Solomon codeword by Lagrange
  interpolation (the convention described on printed p. 38 of
  [BenSassonCarmonIshaiKoppartySaraf2020]), and for each of the `q` queried starting positions
  `s : Fin (2 ^ d)` checks:
  1. explicit round-0 binding `π_0(s) = stmt(s)` against the input word `stmt`,
  2. all `m` local `l⁽ⁱ⁾`-to-1 coset folding equations (`foldFiber`) along the powering chain of `s`
     (opening all `l⁽ⁱ⁾` fiber points in `π_i` and `1` folded point in `π_{i + 1}`), and
  3. agreement of `π_m(s % 2 ^ (d - totalLog))` with the interpolated final codeword.
  The committed-proof-oracle opening list exposed through `PublicCoinIOP.queries` has exact length
  `params.proofOracleQueries = kFinal + q * (aritySum + m + 2)` (specializing to
  `kFinal + q * (3 * m + 2)` for 2-to-1 folding, which governs BCS Merkle verification cost).
  Separately, outside `PublicCoinIOP.queries`, `friSmoothInputQueries` (and `friInputQueries`)
  lists `q` scheduled input positions, with multiplicity (`params.inputWordReads = q`, certified
  sufficient by `friSmoothDecide_congr_inputQueries` / `friDecide_congr_inputQueries`). Because
  `friSmoothDecide` can reject on an unexpected answer-list length before accessing `stmt`,
  repetitions short-circuit on earlier failures (`&&`), and query challenges may repeat indices,
  `params.inputWordReads = q` is a direct-read schedule / upper-bound budget rather than a count of
  distinct reads performed on every execution. Pairing this input-read budget with the exact
  committed-opening count gives the combined word-query budget
  `params.totalWordQueries = kFinal + q * (aritySum + m + 3)` (`kFinal + q * (3 * m + 3)` for
  2-to-1 folding, aligned with counting both input-word and prover-table queries in
  [BenSassonBentovHoreshRiabzev2018], pp. 14:3–14:4), independent of `2 ^ d`.

## Main definitions

* `Cslib.Crypto.Protocols.FRI.friCumLog`, `Cslib.Crypto.Protocols.FRI.FRISmoothParams`,
  `Cslib.Crypto.Protocols.FRI.FRIParams`, `Cslib.Crypto.Protocols.FRI.FRIParams.toSmooth`,
  `Cslib.Crypto.Protocols.FRI.FRIChal`: per-round smooth folding schedule, smooth and binary
  parameter bundles, embedding of binary parameters into smooth parameters, and public-coin
  challenge structure.
* `Cslib.Crypto.Protocols.FRI.evalLagrange`: computable Lagrange interpolation evaluator bridged
  to Mathlib's `Lagrange.interpolate` via `Lagrange.eval_basis`.
* `Cslib.Crypto.Protocols.FRI.padOracle`, `Cslib.Crypto.Protocols.FRI.restrictOracle`,
  `Cslib.Crypto.Protocols.FRI.friSmoothHonestWord`, `Cslib.Crypto.Protocols.FRI.friHonestWord`:
  active-domain oracle padding and iterated smooth / 2-to-1 honest prover folding.
* `Cslib.Crypto.Protocols.FRI.friSmoothQueries`,
  `Cslib.Crypto.Protocols.FRI.friSmoothInputQueries`,
  `Cslib.Crypto.Protocols.FRI.friQueries`, `Cslib.Crypto.Protocols.FRI.friInputQueries`:
  committed-proof-oracle openings and direct input-word read positions.
* `Cslib.Crypto.Protocols.FRI.friSmoothFinalCodeword`,
  `Cslib.Crypto.Protocols.FRI.friSmoothSingleAccepts`,
  `Cslib.Crypto.Protocols.FRI.friFinalCodeword`, `Cslib.Crypto.Protocols.FRI.friSingleAccepts`:
  interpolated final-round codeword and single-query verifier acceptance predicates.
* `Cslib.Crypto.Protocols.FRI.friSmoothIOP`, `Cslib.Crypto.Protocols.FRI.friIOP`: the
  `(m + 1)`-round `PublicCoinIOP` instantiations of smooth and 2-to-1 FRI.

## Main results

* `Cslib.Crypto.Protocols.FRI.FRISmoothParams.sum_arity_sub_one_mul_domainSize`,
  `Cslib.Crypto.Protocols.FRI.FRISmoothParams.arity_sub_one_mul_domainSize_le_first`: exact
  smooth curve-degree telescoping identity `∑ (l⁽ⁱ⁾ - 1) * n_{i+1} = 2 ^ d - 2 ^ (d - totalLog)`
  and round-`0` maximality bound.
* `Cslib.Crypto.Protocols.FRI.evalLagrange_eq_eval_interpolate`,
  `Cslib.Crypto.Protocols.FRI.evalLagrange_mem_reedSolomon`,
  `Cslib.Crypto.Protocols.FRI.evalLagrange_eq_of_mem_reedSolomon`: bridge to `Lagrange.interpolate`,
  Reed–Solomon membership, and exact recovery of the final Lagrange interpolant.
* `Cslib.Crypto.Protocols.FRI.friSmoothHonestWord_mem_rsCode`,
  `Cslib.Crypto.Protocols.FRI.friHonestWord_mem_rsCode`: iterated honest folding preserves
  Reed–Solomon membership across all `m` rounds.
* `Cslib.Crypto.Protocols.FRI.friIOP_eq_friSmoothIOP`: exact equality between binary `friIOP` and
  `friSmoothIOP params.toSmooth` across `proveRound`, `queries`, and `decide`.
* `Cslib.Crypto.Protocols.FRI.length_friSmoothIOP_queries`,
  `Cslib.Crypto.Protocols.FRI.length_friSmoothInputQueries`,
  `Cslib.Crypto.Protocols.FRI.friSmoothDecide_congr_inputQueries`,
  `Cslib.Crypto.Protocols.FRI.iopVerify_friSmoothIOP_eq_true_iff`,
  `Cslib.Crypto.Protocols.FRI.length_friIOP_queries`,
  `Cslib.Crypto.Protocols.FRI.length_friInputQueries`,
  `Cslib.Crypto.Protocols.FRI.friDecide_congr_inputQueries`,
  `Cslib.Crypto.Protocols.FRI.iopVerify_friIOP_eq_true_iff`: exact committed-proof-oracle opening
  counts, input-word read locality, and exact characterizations of `iopVerify` acceptance.
* `Cslib.Crypto.Protocols.FRI.friSmoothIOP_complete`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBCS_verify_prove_eq_true`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBCS_honestROMGame_eq_pure_true`,
  `Cslib.Crypto.Protocols.FRI.friIOP_complete`,
  `Cslib.Crypto.Protocols.FRI.friBCS_verify_prove_eq_true`,
  `Cslib.Crypto.Protocols.FRI.friBCS_honestROMGame_eq_pure_true`: perfect completeness of smooth
  and binary FRI as IOPs, under deterministic BCS, and in the two-channel BCS random-oracle model.
* `Cslib.Crypto.Protocols.FRI.isCostBounded_bcsMTCost_friSmoothVerifyROM`,
  `Cslib.Crypto.Protocols.FRI.isCostBounded_bcsMTCost_friVerifyROM`: verifier Merkle hash query
  cost bounds for BCS-compiled smooth and binary FRI.

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

/-! ### Binary `FRIParams` Parameters -/

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

/-- Exact length of the committed-proof-oracle opening list issued by the FRI verifier via
`PublicCoinIOP.queries`: `kFinal + q * (3 * m + 2)`. This excludes the `q` scheduled input
positions, with multiplicity, tracked by `inputWordReads`, and is the opening count that governs
BCS Merkle verification cost. -/
abbrev proofOracleQueries (params : FRIParams F) : ℕ :=
  params.kFinal + params.q * (3 * params.m + 2)

/-- Direct input-word read budget: `q` scheduled input positions, with multiplicity (listed by
`friInputQueries` outside `PublicCoinIOP.queries`). Because `friDecide` can reject on answer-list
length before accessing `stmt`, repetitions short-circuit on earlier failures, and query challenges
may repeat indices, `q` is a schedule / upper-bound budget. -/
abbrev inputWordReads (params : FRIParams F) : ℕ :=
  params.q

/-- Combined word-query budget `inputWordReads + proofOracleQueries = kFinal + q * (3 * m + 3)`,
pairing the `q` scheduled input positions (with multiplicity) with the exact committed-proof-oracle
opening list length `proofOracleQueries` ([BenSassonBentovHoreshRiabzev2018], pp. 14:3–14:4). -/
abbrev totalWordQueries (params : FRIParams F) : ℕ :=
  params.inputWordReads + params.proofOracleQueries

/-- Closed-form expression `kFinal + q * (3 * m + 3)` for `totalWordQueries`. -/
theorem totalWordQueries_eq (params : FRIParams F) :
    params.totalWordQueries = params.kFinal + params.q * (3 * params.m + 3) := by
  simp only [totalWordQueries, inputWordReads, proofOracleQueries]
  ring

/-- First `kFinal` evaluation points of the final coset `L_m`. -/
@[expose] def finalAnchorPoints (params : FRIParams F) : Fin params.kFinal → F :=
  fun t => params.eval params.m ⟨t.val, lt_of_lt_of_le t.isLt params.hkLe⟩

/-- Injectivity of the `kFinal` anchor points of the final coset `L_m`. -/
theorem finalAnchorPoints_injective (params : FRIParams F) :
    Function.Injective params.finalAnchorPoints :=
  fun _ _ h => Fin.ext (Fin.mk.inj (cosetEval_injective params.hg params.hω params.hm h))

/-- Each 2-to-1 folding round halves the Reed–Solomon code dimension. -/
theorem dim_eq_two_mul_succ (params : FRIParams F) {i : ℕ} (hi : i < params.m) :
    params.dim i = 2 * params.dim (i + 1) := by
  have hsub : params.m - i = (params.m - (i + 1)) + 1 := by omega
  rw [dim, dim, hsub, pow_succ', mul_left_comm]

/-- Each 2-to-1 folding round halves the evaluation domain size. -/
theorem domainSize_eq_two_mul_succ (params : FRIParams F) {i : ℕ} (hi : i < params.d) :
    params.domainSize i = 2 * params.domainSize (i + 1) := by
  have hsub : params.d - i = (params.d - (i + 1)) + 1 := by omega
  simp only [domainSize, hsub, pow_succ']

end FRIParams

/-! ### Cumulative Log-Arities & Smooth `FRISmoothParams` -/

/-- Cumulative folding log-arity `∑_{k < i} stepLog k` after the first `i` rounds (`i ≤ m`). -/
@[expose] def friCumLog {m : ℕ} (stepLog : Fin m → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => friCumLog stepLog i + if h : i < m then stepLog ⟨i, h⟩ else 0

/-- At round `0`, the cumulative folding log-arity `friCumLog stepLog 0` is `0`. -/
@[simp]
theorem friCumLog_zero {m : ℕ} (stepLog : Fin m → ℕ) : friCumLog stepLog 0 = 0 := rfl

/-- One-step recurrence for `friCumLog` at `i < m`. -/
theorem friCumLog_succ_of_lt {m : ℕ} (stepLog : Fin m → ℕ) {i : ℕ} (hi : i < m) :
    friCumLog stepLog (i + 1) = friCumLog stepLog i + stepLog ⟨i, hi⟩ := by
  simp only [friCumLog, hi, ↓reduceDIte]

/-- Monotonicity of `friCumLog` in the round index. -/
theorem friCumLog_mono {m : ℕ} (stepLog : Fin m → ℕ) {i j : ℕ} (hij : i ≤ j) :
    friCumLog stepLog i ≤ friCumLog stepLog j := by
  induction hij with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (Nat.le_add_right _ _)

/-- Total cumulative log-arity `friCumLog stepLog m` equals the finite sum `∑ i, stepLog i`. -/
theorem friCumLog_eq_sum_fin {m : ℕ} (stepLog : Fin m → ℕ) :
    friCumLog stepLog m = ∑ i : Fin m, stepLog i := by
  suffices ∀ (k : ℕ) (hk : k ≤ m),
      friCumLog stepLog k = ∑ i : Fin k, stepLog ⟨i.val, lt_of_lt_of_le i.isLt hk⟩ from
    this m le_rfl
  intro k hk
  induction k with
  | zero => simp [friCumLog]
  | succ k ih =>
    rw [friCumLog_succ_of_lt stepLog (Nat.lt_of_succ_le hk), Fin.sum_univ_castSucc,
      ih (Nat.le_of_succ_le hk)]
    rfl

/-- For the constant schedule `stepLog = 1` (binary 2-to-1 folding), `friCumLog` is the identity. -/
theorem friCumLog_const_one {m : ℕ} : ∀ {i : ℕ}, i ≤ m → friCumLog (fun _ : Fin m => 1) i = i
  | 0, _ => rfl
  | i + 1, hi => by
    rw [friCumLog_succ_of_lt _ (Nat.lt_of_succ_le hi),
      friCumLog_const_one (Nat.le_of_succ_le hi)]

/-- Public parameters for an `(m + 1)`-round smooth FRI protocol over a field `F` with per-round
strict 2-smooth folding arity `l⁽ⁱ⁾ = 2 ^ stepLog i ≥ 2` ([BenSassonCarmonIshaiKoppartySaraf2020],
Section 8.2, printed p. 37): initial multiplicative coset `g * ⟨ω⟩` of size `2 ^ d`, `m` folding
rounds with total log-reduction `totalLog = ∑ i, stepLog i ≤ d`, final Reed–Solomon dimension
`1 ≤ kFinal ≤ 2 ^ (d - totalLog)`, and `q` batched query repetitions. -/
structure FRISmoothParams (F : Type) [Field F] where
  /-- Log-size of the initial multiplicative coset (`|L_0| = 2 ^ d`). -/
  d : ℕ
  /-- Number of smooth folding rounds. -/
  m : ℕ
  /-- Per-round folding log-arity `sᵢ` (`l⁽ⁱ⁾ = 2 ^ sᵢ ≥ 2`). -/
  stepLog : Fin m → ℕ
  /-- Final Reed–Solomon dimension after all `m` folding rounds. -/
  kFinal : ℕ
  /-- Number of independent query starting indices sampled in the final round. -/
  q : ℕ
  /-- Nonzero multiplicative coset offset. -/
  g : F
  /-- Primitive `2 ^ d`-th root of unity generating the initial evaluation subgroup. -/
  ω : F
  /-- Each folding round shrinks the domain strictly (`l⁽ⁱ⁾ = 2 ^ stepLog i ≥ 2`). -/
  hstepPos : ∀ i : Fin m, 1 ≤ stepLog i
  /-- Total folding log-reduction does not exceed the initial domain log-size. -/
  htotal : friCumLog stepLog m ≤ d
  /-- The final Reed–Solomon dimension is at least `1`. -/
  hkPos : 1 ≤ kFinal
  /-- The final Reed–Solomon dimension fits within the final domain `2 ^ (d - totalLog)`. -/
  hkLe : kFinal ≤ 2 ^ (d - friCumLog stepLog m)
  /-- The coset offset is nonzero. -/
  hg : g ≠ 0
  /-- The field does not have characteristic `2` (sufficient for all `2 ^ s`-to-1 folding). -/
  h2 : (2 : F) ≠ 0
  /-- `ω` is a primitive `2 ^ d`-th root of unity. -/
  hω : IsPrimitiveRoot ω (2 ^ d)

namespace FRISmoothParams

/-- Cumulative folding log-arity after the first `i` rounds (`i ≤ m`). -/
abbrev cumLog (params : FRISmoothParams F) (i : ℕ) : ℕ :=
  friCumLog params.stepLog i

/-- Total folding log-reduction `∑ i : Fin m, stepLog i` across all `m` rounds. -/
abbrev totalLog (params : FRISmoothParams F) : ℕ :=
  params.cumLog params.m

/-- Folding arity `l⁽ⁱ⁾ = 2 ^ stepLog i` of round `i : Fin m`. -/
abbrev arity (params : FRISmoothParams F) (i : Fin params.m) : ℕ :=
  2 ^ params.stepLog i

/-- Sum of per-round folding arities `∑ i : Fin m, l⁽ⁱ⁾`. -/
abbrev aritySum (params : FRISmoothParams F) : ℕ :=
  ∑ i : Fin params.m, params.arity i

/-- First-round log-arity `stepLog 0` (defaulting to `1` when `m = 0`). -/
abbrev firstStepLog (params : FRISmoothParams F) : ℕ :=
  if h : 0 < params.m then params.stepLog ⟨0, h⟩ else 1

/-- Active domain size `2 ^ (d - cumLog i)` at round `i`. -/
abbrev domainSize (params : FRISmoothParams F) (i : ℕ) : ℕ :=
  2 ^ (params.d - params.cumLog i)

/-- Reed–Solomon dimension `kFinal * 2 ^ (totalLog - cumLog i)` at round `i`. -/
abbrev dim (params : FRISmoothParams F) (i : ℕ) : ℕ :=
  params.kFinal * 2 ^ (params.totalLog - params.cumLog i)

/-- Coset evaluation map at round `i`. -/
abbrev eval (params : FRISmoothParams F) (i : ℕ) : Fin (2 ^ (params.d - params.cumLog i)) → F :=
  cosetEval params.g params.ω params.d (params.cumLog i)

/-- Round-`i` Reed–Solomon code `RS[F, L_i, dim i]`. -/
noncomputable abbrev rsCode (params : FRISmoothParams F) (i : ℕ) :
    Submodule F (Fin (2 ^ (params.d - params.cumLog i)) → F) :=
  reedSolomon (params.eval i) (params.dim i)

/-- Initial Reed–Solomon code on `OracleTable params.d F`. -/
noncomputable abbrev initialCode (params : FRISmoothParams F) :
    Submodule F (OracleTable params.d F) :=
  params.rsCode 0

/-- Proximity language of input words at Hamming distance at most `e` from `initialCode`. -/
@[expose] def proximityLang [DecidableEq F] (params : FRISmoothParams F) (e : ℕ) :
    Set (OracleTable params.d F) :=
  {f₀ | ∃ c ∈ params.initialCode, hammingDist f₀ c ≤ e}

/-- Honest completeness relation: input word `f₀` lies in `initialCode`. -/
@[expose] def completenessRel (params : FRISmoothParams F) : OracleTable params.d F → Unit → Prop :=
  fun f₀ _ => f₀ ∈ params.initialCode

/-- Committed-proof-oracle openings per query repetition: `1` round-`0` entry, `l⁽ⁱ⁾ + 1` entries
per folding round `i`, and `1` final-round entry (`aritySum + m + 2`). -/
abbrev singleRepQueries (params : FRISmoothParams F) : ℕ :=
  params.aritySum + params.m + 2

/-- Exact length of the committed-proof-oracle opening list issued by the smooth FRI verifier via
`PublicCoinIOP.queries`: `kFinal + q * (aritySum + m + 2)`. -/
abbrev proofOracleQueries (params : FRISmoothParams F) : ℕ :=
  params.kFinal + params.q * params.singleRepQueries

/-- Direct input-word read budget: `q` scheduled input positions, with multiplicity (listed by
`friSmoothInputQueries` outside `PublicCoinIOP.queries`). Because `friSmoothDecide` can reject on
answer-list length before accessing `stmt`, repetitions short-circuit on earlier failures, and
query challenges may repeat indices, `q` is a schedule / upper-bound budget. -/
abbrev inputWordReads (params : FRISmoothParams F) : ℕ :=
  params.q

/-- Combined word-query budget `inputWordReads + proofOracleQueries =
kFinal + q * (aritySum + m + 3)`, pairing the `q` scheduled input positions (with multiplicity)
with the exact committed-proof-oracle opening list length `proofOracleQueries`. -/
abbrev totalWordQueries (params : FRISmoothParams F) : ℕ :=
  params.inputWordReads + params.proofOracleQueries

/-- Closed-form expression `kFinal + q * (aritySum + m + 3)` for `totalWordQueries`. -/
theorem totalWordQueries_eq (params : FRISmoothParams F) :
    params.totalWordQueries = params.kFinal + params.q * (params.aritySum + params.m + 3) := by
  simp only [totalWordQueries, inputWordReads, proofOracleQueries, singleRepQueries]
  ring

/-- First `kFinal` evaluation points of the final coset `L_m`. -/
@[expose] def finalAnchorPoints (params : FRISmoothParams F) : Fin params.kFinal → F :=
  fun t => params.eval params.m ⟨t.val, lt_of_lt_of_le t.isLt params.hkLe⟩

/-- Injectivity of the `kFinal` anchor points of the final coset `L_m`. -/
theorem finalAnchorPoints_injective (params : FRISmoothParams F) :
    Function.Injective params.finalAnchorPoints :=
  fun _ _ h => Fin.ext (Fin.mk.inj (cosetEval_injective params.hg params.hω params.htotal h))

/-- Any prefix cumulative log-arity `cumLog i` (`i ≤ m`) is at most `totalLog`. -/
theorem cumLog_le_totalLog (params : FRISmoothParams F) {i : ℕ} (hi : i ≤ params.m) :
    params.cumLog i ≤ params.totalLog :=
  friCumLog_mono params.stepLog hi

/-- Any prefix cumulative log-arity `cumLog i` (`i ≤ m`) is at most `d`. -/
theorem cumLog_le_d (params : FRISmoothParams F) {i : ℕ} (hi : i ≤ params.m) :
    params.cumLog i ≤ params.d :=
  (params.cumLog_le_totalLog hi).trans params.htotal

/-- One-step recurrence for `cumLog` at folding round `i : Fin params.m`. -/
theorem cumLog_succ (params : FRISmoothParams F) (i : Fin params.m) :
    params.cumLog (i.val + 1) = params.cumLog i.val + params.stepLog i :=
  friCumLog_succ_of_lt params.stepLog i.isLt

/-- Bound `cumLog i + stepLog i ≤ d` for every folding round `i : Fin params.m`. -/
theorem cumLog_add_stepLog_le_d (params : FRISmoothParams F) (i : Fin params.m) :
    params.cumLog i.val + params.stepLog i ≤ params.d :=
  params.cumLog_succ i ▸ params.cumLog_le_d i.isLt

/-- Every smooth folding round has arity `2 ^ stepLog i ≥ 2`. -/
theorem two_le_arity (params : FRISmoothParams F) (i : Fin params.m) :
    2 ≤ params.arity i := by
  simpa only [arity, pow_one] using Nat.pow_le_pow_right (by omega : 0 < 2) (params.hstepPos i)

/-- The cast of each round's smooth folding arity `2 ^ stepLog i` into `F` is nonzero. -/
theorem arity_cast_ne_zero (params : FRISmoothParams F) (i : Fin params.m) :
    ((params.arity i : ℕ) : F) ≠ 0 := by
  simpa only [arity, Nat.cast_pow, Nat.cast_ofNat] using pow_ne_zero (params.stepLog i) params.h2

/-- Folding round `i` shrinks the evaluation domain by a factor of `arity i`. -/
theorem domainSize_eq_arity_mul_succ (params : FRISmoothParams F) (i : Fin params.m) :
    params.domainSize i.val = params.arity i * params.domainSize (i.val + 1) := by
  have := params.cumLog_add_stepLog_le_d i
  have := params.cumLog_succ i
  rw [domainSize, arity, domainSize, ← pow_add]
  exact congrArg (2 ^ ·) (by omega)

/-- Folding round `i` shrinks the Reed–Solomon code dimension by a factor of `arity i`. -/
theorem dim_eq_arity_mul_succ (params : FRISmoothParams F) (i : Fin params.m) :
    params.dim i.val = params.arity i * params.dim (i.val + 1) := by
  have := params.cumLog_succ i
  have : params.cumLog (i.val + 1) ≤ params.totalLog := params.cumLog_le_totalLog i.isLt
  rw [dim, arity, dim, mul_left_comm, ← pow_add]
  exact congrArg (params.kFinal * 2 ^ ·) (by omega)

/-- The final-round Reed–Solomon code dimension `dim m` equals `kFinal`. -/
theorem dim_last (params : FRISmoothParams F) : params.dim params.m = params.kFinal := by
  simp [dim]

private theorem domainSize_anti (params : FRISmoothParams F) {i j : ℕ} (hij : i ≤ j) :
    params.domainSize j ≤ params.domainSize i :=
  Nat.pow_le_pow_right (by omega) (Nat.sub_le_sub_left (friCumLog_mono params.stepLog hij) _)

/-- Per-round curve-degree weight identity: `(l⁽ⁱ⁾ - 1) * n_{i+1} = nᵢ - n_{i+1}`. -/
theorem arity_sub_one_mul_domainSize (params : FRISmoothParams F) (i : Fin params.m) :
    (params.arity i - 1) * params.domainSize (i.val + 1) =
      params.domainSize i.val - params.domainSize (i.val + 1) := by
  rw [Nat.sub_mul, one_mul, params.domainSize_eq_arity_mul_succ i]

/-- **Exact smooth curve-degree telescoping**: summing `(l⁽ⁱ⁾ - 1) * n_{i+1}` across all `m`
folding rounds telescopes exactly to `2 ^ d - 2 ^ (d - totalLog)`. -/
theorem sum_arity_sub_one_mul_domainSize (params : FRISmoothParams F) :
    (∑ i : Fin params.m, (params.arity i - 1) * params.domainSize (i.val + 1)) =
      2 ^ params.d - 2 ^ (params.d - params.totalLog) := by
  simp_rw [params.arity_sub_one_mul_domainSize]
  suffices ∀ k, (∑ i : Fin k, (params.domainSize i.val - params.domainSize (i.val + 1))) =
      params.domainSize 0 - params.domainSize k from this params.m
  intro k
  induction k with
  | zero => simp [domainSize]
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih]
    have h1 : params.domainSize (k + 1) ≤ params.domainSize k :=
      params.domainSize_anti (Nat.le_succ k)
    have h0 : params.domainSize k ≤ params.domainSize 0 := params.domainSize_anti (Nat.zero_le k)
    omega

/-- **Round-`0` maximality across smooth folding rounds**: every round's curve-degree budget
`(l⁽ⁱ⁾ - 1) * n_{i+1}` is at most the round-`0` budget `2 ^ d - 2 ^ (d - firstStepLog)`. -/
theorem arity_sub_one_mul_domainSize_le_first (params : FRISmoothParams F) (i : Fin params.m) :
    (params.arity i - 1) * params.domainSize (i.val + 1) ≤
      2 ^ params.d - 2 ^ (params.d - params.firstStepLog) := by
  have hdom1 : params.domainSize 1 = 2 ^ (params.d - params.firstStepLog) := by
    simp [domainSize, cumLog, firstStepLog, i.pos, friCumLog_succ_of_lt _ i.pos]
  rw [params.arity_sub_one_mul_domainSize i, ← hdom1]
  change _ ≤ params.domainSize 0 - _
  rcases Nat.eq_zero_or_pos i.val with hi0 | hi_pos
  · rw [hi0]
  · have : params.domainSize i.val ≤ params.domainSize 1 := params.domainSize_anti hi_pos
    have : 2 * params.domainSize 1 ≤ params.domainSize 0 :=
      (Nat.mul_le_mul_right _ (params.two_le_arity ⟨0, i.pos⟩)).trans_eq
        (params.domainSize_eq_arity_mul_succ ⟨0, i.pos⟩).symm
    omega

end FRISmoothParams

/-! ### Embedding `FRIParams` into `FRISmoothParams` (`toSmooth`) -/

namespace FRIParams

/-- Embed binary 2-to-1 `FRIParams` into `FRISmoothParams` via the constant folding schedule
`stepLog := fun _ => 1` (preserving `d, m, kFinal, q, g, ω` at reducible transparency). -/
abbrev toSmooth (params : FRIParams F) : FRISmoothParams F where
  d := params.d
  m := params.m
  stepLog := fun _ => 1
  kFinal := params.kFinal
  q := params.q
  g := params.g
  ω := params.ω
  hstepPos := fun _ => le_rfl
  htotal := by rw [friCumLog_const_one le_rfl]; exact params.hm
  hkPos := params.hkPos
  hkLe := by rw [friCumLog_const_one le_rfl]; exact params.hkLe
  hg := params.hg
  h2 := params.h2
  hω := params.hω

/-- Under `toSmooth`, cumulative folding log-arity at round `i ≤ m` is `i`. -/
@[simp]
theorem toSmooth_cumLog (params : FRIParams F) {i : ℕ} (hi : i ≤ params.m) :
    params.toSmooth.cumLog i = i :=
  friCumLog_const_one hi

/-- Under `toSmooth`, total folding log-arity equals `params.m`. -/
theorem toSmooth_totalLog (params : FRIParams F) :
    params.toSmooth.totalLog = params.m :=
  friCumLog_const_one le_rfl

/-- Under `toSmooth`, every folding round has arity `2`. -/
@[simp]
theorem toSmooth_arity (params : FRIParams F) (i : Fin params.m) :
    params.toSmooth.arity i = 2 := by
  simp [FRISmoothParams.arity]

/-- Under `toSmooth`, the sum of per-round arities equals `2 * params.m`. -/
@[simp]
theorem toSmooth_aritySum (params : FRIParams F) :
    params.toSmooth.aritySum = 2 * params.m := by
  simp only [FRISmoothParams.aritySum, FRISmoothParams.arity, pow_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]

/-- Under `toSmooth`, the first-round log-arity `firstStepLog` is `1`. -/
theorem toSmooth_firstStepLog (params : FRIParams F) :
    params.toSmooth.firstStepLog = 1 := by
  dsimp only [FRISmoothParams.firstStepLog]
  split_ifs <;> rfl

/-- Under `toSmooth`, round-`i` domain size matches `params.domainSize i` for `i ≤ m`. -/
@[simp]
theorem toSmooth_domainSize (params : FRIParams F) {i : ℕ} (hi : i ≤ params.m) :
    params.toSmooth.domainSize i = params.domainSize i := by
  simp only [FRISmoothParams.domainSize, FRISmoothParams.cumLog, friCumLog_const_one hi, domainSize]

/-- Under `toSmooth`, round-`i` RS code dimension matches `params.dim i` for `i ≤ m`. -/
@[simp]
theorem toSmooth_dim (params : FRIParams F) {i : ℕ} (hi : i ≤ params.m) :
    params.toSmooth.dim i = params.dim i := by
  simp only [FRISmoothParams.dim, FRISmoothParams.totalLog, FRISmoothParams.cumLog,
    friCumLog_const_one le_rfl, friCumLog_const_one hi, dim]

/-- Under `toSmooth`, the initial Reed–Solomon code matches `params.initialCode`. -/
@[simp]
theorem toSmooth_initialCode (params : FRIParams F) :
    params.toSmooth.initialCode = params.initialCode := by
  simp only [FRISmoothParams.initialCode, FRISmoothParams.rsCode, FRISmoothParams.eval,
    FRISmoothParams.dim, FRISmoothParams.totalLog, FRISmoothParams.cumLog, friCumLog_zero,
    friCumLog_const_one le_rfl, initialCode, rsCode, eval, dim]

/-- Under `toSmooth`, the proximity language at radius `e` matches `params.proximityLang e`. -/
@[simp]
theorem toSmooth_proximityLang [DecidableEq F] (params : FRIParams F) (e : ℕ) :
    params.toSmooth.proximityLang e = params.proximityLang e := by
  simp only [FRISmoothParams.proximityLang, proximityLang, params.toSmooth_initialCode]

/-- Under `toSmooth`, the completeness relation matches `params.completenessRel`. -/
@[simp]
theorem toSmooth_completenessRel (params : FRIParams F) :
    params.toSmooth.completenessRel = params.completenessRel := by
  funext f₀ _
  simp only [FRISmoothParams.completenessRel, completenessRel, params.toSmooth_initialCode]

/-- Under `toSmooth`, a single repetition takes `3 * params.m + 2` oracle openings. -/
@[simp]
theorem toSmooth_singleRepQueries (params : FRIParams F) :
    params.toSmooth.singleRepQueries = 3 * params.m + 2 := by
  simp only [FRISmoothParams.singleRepQueries, params.toSmooth_aritySum]
  omega

/-- Under `toSmooth`, total committed proof oracle openings match `params.proofOracleQueries`. -/
@[simp]
theorem toSmooth_proofOracleQueries (params : FRIParams F) :
    params.toSmooth.proofOracleQueries = params.proofOracleQueries := by
  rw [FRISmoothParams.proofOracleQueries, params.toSmooth_singleRepQueries]

/-- Under `toSmooth`, scheduled input word reads match `params.inputWordReads`. -/
@[simp]
theorem toSmooth_inputWordReads (params : FRIParams F) :
    params.toSmooth.inputWordReads = params.inputWordReads := rfl

/-- Under `toSmooth`, combined word queries match `params.totalWordQueries`. -/
@[simp]
theorem toSmooth_totalWordQueries (params : FRIParams F) :
    params.toSmooth.totalWordQueries = params.totalWordQueries := by
  simp only [FRISmoothParams.totalWordQueries, toSmooth_inputWordReads, toSmooth_proofOracleQueries]

/-- Under `toSmooth`, the final anchor points match `params.finalAnchorPoints`. -/
@[simp]
theorem toSmooth_finalAnchorPoints (params : FRIParams F) :
    params.toSmooth.finalAnchorPoints = params.finalAnchorPoints := by
  funext t
  simp only [FRISmoothParams.finalAnchorPoints, FRISmoothParams.eval, FRISmoothParams.cumLog,
    finalAnchorPoints, eval, cosetEval, cosetPoint, friCumLog_const_one le_rfl]

end FRIParams

/-! ### Verifier Challenge Alphabet (`FRIChal`) -/

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
/-- Cardinality of the challenge space `FRIChal F d q`. -/
theorem card_friChal [Fintype F] (d q : ℕ) :
    Fintype.card (FRIChal F d q) = Fintype.card F * (2 ^ d) ^ q := by
  rw [Fintype.card_congr (FRIChal.equivProd F d q), Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin]

end ParamsAndChallenges

/-! ### Lagrange Interpolation on Final Anchor Points -/

section LagrangeInterpolation

variable {F : Type} [Field F]

/-- Computable Lagrange interpolation evaluation at `x : F` from nodes `pts` and values `vals`. -/
@[expose] def evalLagrange {k : ℕ} (pts vals : Fin k → F) (x : F) : F :=
  ∑ t : Fin k, vals t * ∏ u ∈ Finset.univ.erase t, (x - pts u) / (pts t - pts u)

/-- Bridge between the computable evaluator `evalLagrange` and Mathlib's `Lagrange.interpolate`,
via `Lagrange.eval_basis`. -/
theorem evalLagrange_eq_eval_interpolate {k : ℕ} (pts vals : Fin k → F) (x : F) :
    evalLagrange pts vals x = (Lagrange.interpolate Finset.univ pts vals).eval x := by
  simp only [evalLagrange, Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C,
    Lagrange.eval_basis]

/-- `evalLagrange` recovers `vals s` at every distinct interpolation node `pts s`. -/
theorem evalLagrange_node {k : ℕ} {pts : Fin k → F} (hpts : Function.Injective pts)
    (vals : Fin k → F) (s : Fin k) :
    evalLagrange pts vals (pts s) = vals s := by
  rw [evalLagrange_eq_eval_interpolate]
  exact Lagrange.eval_interpolate_at_node vals (Set.injOn_of_injective hpts) (Finset.mem_univ s)

/-- Evaluating `evalLagrange pts vals` on any evaluation map `α : Fin n → F` always produces a
Reed–Solomon codeword of dimension `k` for injective nodes `pts : Fin k → F`. -/
theorem evalLagrange_mem_reedSolomon {k n : ℕ} {pts : Fin k → F} (hpts : Function.Injective pts)
    (vals : Fin k → F) (α : Fin n → F) :
    (fun j => evalLagrange pts vals (α j)) ∈ reedSolomon α k := by
  refine mem_reedSolomon.mpr ⟨Lagrange.interpolate Finset.univ pts vals, ?_, ?_⟩
  · simpa only [Finset.card_univ, Fintype.card_fin] using
      Lagrange.degree_interpolate_lt (s := Finset.univ) vals (Set.injOn_of_injective hpts)
  · ext j
    exact (evalLagrange_eq_eval_interpolate pts vals (α j)).symm

/-- Exact recovery for codewords of `reedSolomon α k` interpolated from the first `k` nodes of `α`.
-/
theorem evalLagrange_eq_of_mem_reedSolomon {k n : ℕ} (hkn : k ≤ n)
    {α : Fin n → F} (hα : Function.Injective α) {f : Fin n → F} (hf : f ∈ reedSolomon α k)
    (j : Fin n) :
    evalLagrange (fun t : Fin k => α ⟨t.val, lt_of_lt_of_le t.isLt hkn⟩)
      (fun t : Fin k => f ⟨t.val, lt_of_lt_of_le t.isLt hkn⟩) (α j) = f j := by
  obtain ⟨p, hp, rfl⟩ := mem_reedSolomon.mp hf
  have hpts_inj : Function.Injective fun t : Fin k => α ⟨t.val, lt_of_lt_of_le t.isLt hkn⟩ :=
    fun _ _ h => Fin.ext (Fin.mk.inj (hα h))
  rw [evalLagrange_eq_eval_interpolate,
    ← Lagrange.eq_interpolate (Set.injOn_of_injective hpts_inj)
      (by simpa only [Finset.card_univ, Fintype.card_fin] using hp)]

end LagrangeInterpolation

/-! ### Oracle Padding and Honest FRI Prover Words -/

section OraclePaddingAndHonestProver

variable {F : Type} [Field F]

/-- Pad a round-`i` word `f : Fin (2 ^ (d - i)) → F` with zeros to a depth-`d` `OracleTable d F`.
-/
@[expose] def padOracle {d i : ℕ} (f : Fin (2 ^ (d - i)) → F) : OracleTable d F :=
  fun idx => if h : idx.val < 2 ^ (d - i) then f ⟨idx.val, h⟩ else 0

/-- Restrict a depth-`d` `OracleTable d F` to the active round-`i` domain `Fin (2 ^ (d - i))`. -/
@[expose] def restrictOracle {d i : ℕ} (π : OracleTable d F) : Fin (2 ^ (d - i)) → F :=
  fun j => π ⟨j.val, lt_of_lt_of_le j.isLt (Nat.pow_le_pow_right (by omega) (Nat.sub_le d i))⟩

/-- Within the active prefix `idx < 2 ^ (d - i)`, `padOracle` returns the entry of `f`. -/
theorem padOracle_apply_of_lt {d i : ℕ} (f : Fin (2 ^ (d - i)) → F) (idx : Fin (2 ^ d))
    (hlt : idx.val < 2 ^ (d - i)) :
    padOracle (i := i) f idx = f ⟨idx.val, hlt⟩ := by
  simp only [padOracle, hlt, ↓reduceDIte]

/-- Restricting a padded round-`i` word recovers the original word `f`. -/
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

/-- Iterated smooth honest FRI prover word at round `j ≤ m`, computed causally from the initial
oracle `f₀` and the first `j` folding scalars `zs : Fin j → F` using per-round arities
`l⁽ⁱ⁾ = 2 ^ stepLog i`. -/
@[expose] def friSmoothHonestWord (params : FRISmoothParams F) (f₀ : OracleTable params.d F) :
    (j : ℕ) → j ≤ params.m → (Fin j → F) → Fin (2 ^ (params.d - params.cumLog j)) → F
  | 0, _, _ => f₀
  | j + 1, hj, zs =>
    let i : Fin params.m := ⟨j, Nat.lt_of_succ_le hj⟩
    let prev := friSmoothHonestWord params f₀ j (Nat.le_of_succ_le hj) (fun k => zs k.castSucc)
    have hsplit : 2 ^ (params.d - params.cumLog j) =
        params.arity i * 2 ^ (params.d - params.cumLog (j + 1)) :=
      params.domainSize_eq_arity_mul_succ i
    foldWord (params.g ^ (2 ^ params.cumLog j)) (params.ω ^ (2 ^ params.cumLog j))
      (fun idx : Fin (params.arity i * 2 ^ (params.d - params.cumLog (j + 1))) =>
        prev ⟨idx.val, lt_of_lt_of_eq idx.isLt hsplit.symm⟩)
      (zs (Fin.last j))

/-- Honest smooth folding satisfies the local `l⁽ʲ⁾`-to-1 fiber equation at every coordinate of
round `j + 1`. -/
theorem friSmoothHonestWord_succ_apply (params : FRISmoothParams F)
    (f₀ : OracleTable params.d F) {j : ℕ} (hj : j + 1 ≤ params.m) (zs : Fin (j + 1) → F)
    (idx : Fin (2 ^ (params.d - params.cumLog (j + 1)))) :
    friSmoothHonestWord params f₀ (j + 1) hj zs idx =
      foldFiber (params.g ^ (2 ^ params.cumLog j)) (params.ω ^ (2 ^ params.cumLog j))
        (fun t : Fin (params.arity ⟨j, Nat.lt_of_succ_le hj⟩) =>
          friSmoothHonestWord params f₀ j (Nat.le_of_succ_le hj) (fun k => zs k.castSucc)
            ⟨idx.val + t.val * 2 ^ (params.d - params.cumLog (j + 1)), by
              have hsplit := params.domainSize_eq_arity_mul_succ ⟨j, Nat.lt_of_succ_le hj⟩
              dsimp only [FRISmoothParams.domainSize] at hsplit
              have hfib := (fiberIdx idx t).isLt
              dsimp only [fiberIdx] at hfib
              omega⟩)
        idx (zs (Fin.last j)) :=
  rfl

/-- **Reed–Solomon invariance of honest smooth FRI folding**: if `f₀ ∈ params.initialCode`, then
every honest prover round word `friSmoothHonestWord params f₀ j hj zs` lies in `params.rsCode j`.
-/
theorem friSmoothHonestWord_mem_rsCode (params : FRISmoothParams F)
    {f₀ : OracleTable params.d F} (hf₀ : f₀ ∈ params.initialCode) :
    ∀ (j : ℕ) (hj : j ≤ params.m) (zs : Fin j → F),
      friSmoothHonestWord params f₀ j hj zs ∈ params.rsCode j
  | 0, _, _ => hf₀
  | j + 1, hj, zs => by
    let i : Fin params.m := ⟨j, Nat.lt_of_succ_le hj⟩
    have hsplit := params.domainSize_eq_arity_mul_succ i
    obtain ⟨p, hp, hpeq⟩ := mem_reedSolomon.mp
      (friSmoothHonestWord_mem_rsCode params hf₀ j (Nat.le_of_succ_le hj) (fun k => zs k.castSucc))
    have hprev_rs :
        (fun idx : Fin (params.arity i * 2 ^ (params.d - params.cumLog (j + 1))) =>
          friSmoothHonestWord params f₀ j (Nat.le_of_succ_le hj) (fun k => zs k.castSucc)
            ⟨idx.val, lt_of_lt_of_eq idx.isLt hsplit.symm⟩) ∈
        reedSolomon
          (cosetPoint (params.g ^ (2 ^ params.cumLog j)) (params.ω ^ (2 ^ params.cumLog j)) _)
          (params.arity i * params.dim (j + 1)) :=
      mem_reedSolomon.mpr ⟨p, params.dim_eq_arity_mul_succ i ▸ hp,
        funext fun idx => congrFun hpeq ⟨idx.val, lt_of_lt_of_eq idx.isLt hsplit.symm⟩⟩
    have hωj : IsPrimitiveRoot (params.ω ^ (2 ^ params.cumLog j))
        (params.arity i * 2 ^ (params.d - params.cumLog (j + 1))) :=
      hsplit ▸ isPrimitiveRoot_pow_two_pow params.hω (params.cumLog_le_d (Nat.le_of_succ_le hj))
    have hpow (x : F) : (x ^ (2 ^ params.cumLog j)) ^ params.arity i =
        x ^ (2 ^ params.cumLog (j + 1)) := by
      rw [params.cumLog_succ i, FRISmoothParams.arity, ← pow_mul, ← pow_add]
    simpa only [friSmoothHonestWord, FRISmoothParams.rsCode, FRISmoothParams.eval, cosetEval,
      hpow] using foldWord_mem_reedSolomon (pow_ne_zero _ params.hg)
      (params.arity_cast_ne_zero i) (Nat.pow_pos (by omega)) hωj hprev_rs (zs (Fin.last j))

/-- Prefix challenge independence: `friSmoothHonestWord` depends only on `zs` up to round `j`. -/
theorem friSmoothHonestWord_congr (params : FRISmoothParams F) (f₀ : OracleTable params.d F) :
    ∀ (j : ℕ) (hj : j ≤ params.m) {zs₁ zs₂ : Fin j → F},
      (∀ k : Fin j, zs₁ k = zs₂ k) →
        friSmoothHonestWord params f₀ j hj zs₁ = friSmoothHonestWord params f₀ j hj zs₂
  | 0, _, _, _, _ => rfl
  | j + 1, hj, zs₁, zs₂, h => by
    simp only [friSmoothHonestWord]
    rw [friSmoothHonestWord_congr params f₀ j (Nat.le_of_succ_le hj) (fun k => h k.castSucc),
      h (Fin.last j)]

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

private theorem foldFiber_toSmooth_eq_fold2Fiber_at (params : FRIParams F) (i : Fin params.m)
    (ys : Fin (params.toSmooth.arity i) → F)
    (idx : Fin (2 ^ (params.d - params.toSmooth.cumLog (i.val + 1)))) (z : F) :
    foldFiber (params.g ^ (2 ^ params.toSmooth.cumLog i.val))
        (params.ω ^ (2 ^ params.toSmooth.cumLog i.val)) ys idx z =
      fold2Fiber (ys ⟨0, by simp⟩) (ys ⟨1, by simp⟩)
        (params.eval i.val ⟨idx.val, lt_of_lt_of_le
          (by simpa only [params.toSmooth_cumLog i.isLt] using idx.isLt)
          (Nat.pow_le_pow_right (by omega) (by omega))⟩) z := by
  have hci1 : params.toSmooth.cumLog (i.val + 1) = i.val + 1 := params.toSmooth_cumLog i.isLt
  have hid : i.val < params.d := lt_of_lt_of_le i.isLt params.hm
  have hωi : IsPrimitiveRoot (params.ω ^ (2 ^ i.val)) (2 * 2 ^ (params.d - (i.val + 1))) :=
    params.domainSize_eq_two_mul_succ hid ▸ isPrimitiveRoot_pow_two_pow params.hω hid.le
  refine Eq.trans (b := foldFiber (params.g ^ (2 ^ i.val)) (params.ω ^ (2 ^ i.val))
    (fun t : Fin 2 => ys ⟨t.val, t.isLt⟩)
    ⟨idx.val, by simpa only [hci1] using idx.isLt⟩ z) ?_ ?_
  · simp only [foldFiber, foldFiberComp, params.toSmooth_cumLog i.isLt.le, hci1,
      FRISmoothParams.arity, pow_one]
    rfl
  · rw [foldFiber_two_eq_fold2Fiber (Nat.pow_pos (by omega)) hωi]
    simp [FRIParams.eval, cosetEval, cosetPoint]

private theorem padOracle_eq_apply {d i j : ℕ} {f : Fin (2 ^ (d - i)) → F}
    {g : Fin (2 ^ (d - j)) → F} (hpad : padOracle f = padOracle g)
    {a : Fin (2 ^ (d - i))} {b : Fin (2 ^ (d - j))} (hab : a.val = b.val) :
    f a = g b := by
  rcases a with ⟨v, ha⟩
  rcases b with ⟨_, hb⟩
  subst hab
  have h := congrFun hpad ⟨v, lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))⟩
  rwa [padOracle_apply_of_lt f _ ha, padOracle_apply_of_lt g _ hb] at h

/-- The padded honest prover oracle tables of binary `friHonestWord` and smooth
`friSmoothHonestWord params.toSmooth` coincide identically at every round `j ≤ m`. -/
theorem padOracle_friHonestWord_eq_smooth (params : FRIParams F) (f₀ : OracleTable params.d F) :
    ∀ (j : ℕ) (hj : j ≤ params.m) (zs : Fin j → F),
      padOracle (friHonestWord params f₀ j hj zs) =
        padOracle (friSmoothHonestWord params.toSmooth f₀ j hj zs)
  | 0, _, _ => rfl
  | j + 1, hj, zs => by
    have hj_le : j ≤ params.m := Nat.le_of_succ_le hj
    have ih := padOracle_friHonestWord_eq_smooth params f₀ j hj_le (fun k => zs k.castSucc)
    have hcj1 : params.toSmooth.cumLog (j + 1) = j + 1 := params.toSmooth_cumLog hj
    ext idx
    by_cases hlt : idx.val < 2 ^ (params.d - (j + 1))
    · have hlt' : idx.val < 2 ^ (params.d - params.toSmooth.cumLog (j + 1)) := by
        simpa only [hcj1] using hlt
      rw [padOracle_apply_of_lt _ _ hlt, padOracle_apply_of_lt _ _ hlt',
        friHonestWord_succ_apply, friSmoothHonestWord_succ_apply,
        foldFiber_toSmooth_eq_fold2Fiber_at params ⟨j, Nat.lt_of_succ_le hj⟩ _ ⟨idx.val, hlt'⟩]
      congr 1
      · exact padOracle_eq_apply ih (by simp)
      · exact padOracle_eq_apply ih (by simp [hcj1])
    · simp [padOracle, hlt, hcj1]

/-- **Reed–Solomon invariance of honest FRI folding** (corollary of
`friSmoothHonestWord_mem_rsCode`): if `f₀ ∈ params.initialCode`, then every honest prover round
word `friHonestWord params f₀ j hj zs` lies in `params.rsCode j`. -/
theorem friHonestWord_mem_rsCode (params : FRIParams F) {f₀ : OracleTable params.d F}
    (hf₀ : f₀ ∈ params.initialCode) (j : ℕ) (hj : j ≤ params.m) (zs : Fin j → F) :
    friHonestWord params f₀ j hj zs ∈ params.rsCode j := by
  obtain ⟨p, hp, hpeq⟩ := mem_reedSolomon.mp <| friSmoothHonestWord_mem_rsCode params.toSmooth
    (by simpa only [FRIParams.toSmooth_initialCode] using hf₀) j hj zs
  have hcj : params.toSmooth.cumLog j = j := params.toSmooth_cumLog hj
  refine mem_reedSolomon.mpr ⟨p, params.toSmooth_dim hj ▸ hp, funext fun k => ?_⟩
  have hk' : k.val < 2 ^ (params.d - params.toSmooth.cumLog j) := by simpa only [hcj] using k.isLt
  rw [padOracle_eq_apply (padOracle_friHonestWord_eq_smooth params f₀ j hj zs)
      (b := ⟨k.val, hk'⟩) rfl, ← congrFun hpeq ⟨k.val, hk'⟩]
  simp [FRIParams.eval, FRISmoothParams.eval, cosetEval, cosetPoint, hcj]

/-- Prefix challenge independence: `friHonestWord` depends only on `zs` up to round `j`. -/
theorem friHonestWord_congr (params : FRIParams F) (f₀ : OracleTable params.d F) :
    ∀ (j : ℕ) (hj : j ≤ params.m) {zs₁ zs₂ : Fin j → F},
      (∀ i : Fin j, zs₁ i = zs₂ i) →
        friHonestWord params f₀ j hj zs₁ = friHonestWord params f₀ j hj zs₂
  | 0, _, _, _, _ => rfl
  | j + 1, hj, zs₁, zs₂, h => by
    simp only [friHonestWord]
    rw [friHonestWord_congr params f₀ j (Nat.le_of_succ_le hj) (fun i => h i.castSucc),
      h (Fin.last j)]

end OraclePaddingAndHonestProver

/-! ### Smooth FRI Query Indices and Schedules -/

section FRISmoothProtocol

variable {F : Type} [Field F]

/-- Active-domain folded index `s % 2 ^ (d - cumLog (i + 1))` for smooth folding round
`i : Fin m`. -/
@[expose] def friSmoothFoldedFin (params : FRISmoothParams F) (i : Fin params.m)
    (s : Fin (2 ^ params.d)) : Fin (2 ^ (params.d - params.cumLog (i.val + 1))) :=
  ⟨s.val % 2 ^ (params.d - params.cumLog (i.val + 1)), Nat.mod_lt _ (Nat.pow_pos (by omega))⟩

/-- Folded target index `s % 2 ^ (d - cumLog (i + 1))` inside `Fin (2 ^ d)`. -/
@[expose] def friSmoothFoldedIdx (params : FRISmoothParams F) (i : Fin params.m)
    (s : Fin (2 ^ params.d)) : Fin (2 ^ params.d) :=
  ⟨s.val % 2 ^ (params.d - params.cumLog (i.val + 1)),
    lt_of_lt_of_le (Nat.mod_lt _ (Nat.pow_pos (by omega)))
      (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))⟩

/-- Fiber index `s % n_{i+1} + t * n_{i+1}` inside `Fin (2 ^ d)` for `t : Fin (params.arity i)`
at smooth folding round `i : Fin m`. -/
@[expose] def friSmoothFiberIdx (params : FRISmoothParams F) (i : Fin params.m)
    (s : Fin (2 ^ params.d)) (t : Fin (params.arity i)) : Fin (2 ^ params.d) :=
  ⟨s.val % 2 ^ (params.d - params.cumLog (i.val + 1)) +
      t.val * 2 ^ (params.d - params.cumLog (i.val + 1)), by
    have hsplit := params.domainSize_eq_arity_mul_succ i
    dsimp only [FRISmoothParams.domainSize] at hsplit
    have hfib := (fiberIdx (friSmoothFoldedFin params i s) t).isLt
    dsimp only [fiberIdx, friSmoothFoldedFin] at hfib
    have hle : 2 ^ (params.d - params.cumLog i.val) ≤ 2 ^ params.d :=
      Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
    omega⟩

/-- Every smooth fiber query index lies inside `Fin (2 ^ (d - cumLog i))`. -/
theorem friSmoothFiberIdx_val_lt (params : FRISmoothParams F) (i : Fin params.m)
    (s : Fin (2 ^ params.d)) (t : Fin (params.arity i)) :
    (friSmoothFiberIdx params i s t).val < 2 ^ (params.d - params.cumLog i.val) :=
  lt_of_lt_of_eq (fiberIdx (friSmoothFoldedFin params i s) t).isLt
    (params.domainSize_eq_arity_mul_succ i).symm

/-- Final-round active index `s % 2 ^ (d - totalLog)` inside `Fin (2 ^ (d - totalLog))`. -/
@[expose] def friSmoothFinalFin (params : FRISmoothParams F) (s : Fin (2 ^ params.d)) :
    Fin (2 ^ (params.d - params.totalLog)) :=
  ⟨s.val % 2 ^ (params.d - params.totalLog), Nat.mod_lt _ (Nat.pow_pos (by omega))⟩

/-- Final-round query index `s % 2 ^ (d - totalLog)` inside `Fin (2 ^ d)`. -/
@[expose] def friSmoothFinalIdx (params : FRISmoothParams F) (s : Fin (2 ^ params.d)) :
    Fin (2 ^ params.d) :=
  ⟨s.val % 2 ^ (params.d - params.totalLog),
    lt_of_lt_of_le (Nat.mod_lt _ (Nat.pow_pos (by omega)))
      (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))⟩

/-- Header queries reading the first `kFinal` entries of the final oracle `π_m`. -/
@[expose] def friSmoothHeaderQueries (params : FRISmoothParams F) :
    List (Fin (params.m + 1) × Fin (2 ^ params.d)) :=
  List.ofFn fun t : Fin params.kFinal =>
    (Fin.last params.m,
      ⟨t.val, lt_of_lt_of_le (lt_of_lt_of_le t.isLt params.hkLe)
        (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))⟩)

/-- The smooth header query schedule reads `params.kFinal` entries of the final oracle. -/
@[simp]
theorem length_friSmoothHeaderQueries (params : FRISmoothParams F) :
    (friSmoothHeaderQueries params).length = params.kFinal := by
  simp [friSmoothHeaderQueries]

/-- Smooth folding-chain queries along a list of rounds `rounds` (opening all `l⁽ⁱ⁾` fiber points
in `π_i` and `1` folded point in `π_{i + 1}`) followed by the final-round check. -/
@[expose] def friSmoothFoldQueriesList (params : FRISmoothParams F) (s : Fin (2 ^ params.d)) :
    List (Fin params.m) → List (Fin (params.m + 1) × Fin (2 ^ params.d))
  | [] => [(Fin.last params.m, friSmoothFinalIdx params s)]
  | i :: is =>
    (List.ofFn fun t : Fin (params.arity i) => (i.castSucc, friSmoothFiberIdx params i s t)) ++
      (i.succ, friSmoothFoldedIdx params i s) :: friSmoothFoldQueriesList params s is

/-- Number of smooth folding-chain queries generated along `rounds`. -/
theorem length_friSmoothFoldQueriesList (params : FRISmoothParams F) (s : Fin (2 ^ params.d))
    (rounds : List (Fin params.m)) :
    (friSmoothFoldQueriesList params s rounds).length =
      (rounds.map fun i => params.arity i + 1).sum + 1 := by
  induction rounds with
  | nil => rfl
  | cons i is ih =>
    simp only [friSmoothFoldQueriesList, List.length_append, List.length_ofFn, List.length_cons,
      List.map_cons, List.sum_cons, ih]
    omega

/-- All committed-proof-oracle queries for a single smooth query repetition starting at `s`. -/
@[expose] def friSmoothSingleQueries (params : FRISmoothParams F) (s : Fin (2 ^ params.d)) :
    List (Fin (params.m + 1) × Fin (2 ^ params.d)) :=
  (⟨0, Nat.zero_lt_succ params.m⟩, s) :: friSmoothFoldQueriesList params s (List.finRange params.m)

/-- A single smooth query repetition contains `params.singleRepQueries` proof-oracle openings. -/
@[simp]
theorem length_friSmoothSingleQueries (params : FRISmoothParams F) (s : Fin (2 ^ params.d)) :
    (friSmoothSingleQueries params s).length = params.singleRepQueries := by
  simp only [friSmoothSingleQueries, List.length_cons, length_friSmoothFoldQueriesList,
    ← Fin.sum_univ_def, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one, FRISmoothParams.singleRepQueries,
    FRISmoothParams.aritySum]

/-- Concatenated smooth queries for a list of repetition indices `reps : List (Fin q)`. -/
@[expose] def friSmoothRepQueriesList (params : FRISmoothParams F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q) :
    List (Fin params.q) → List (Fin (params.m + 1) × Fin (2 ^ params.d))
  | [] => []
  | a :: as =>
    friSmoothSingleQueries params ((chals (Fin.last params.m)).queryIdxs a) ++
      friSmoothRepQueriesList params chals as

/-- Total length of concatenated smooth queries across `reps`. -/
theorem length_friSmoothRepQueriesList (params : FRISmoothParams F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q) (reps : List (Fin params.q)) :
    (friSmoothRepQueriesList params chals reps).length = reps.length * params.singleRepQueries := by
  induction reps with
  | nil => simp [friSmoothRepQueriesList]
  | cons _ _ ih =>
    simp only [friSmoothRepQueriesList, List.length_append, length_friSmoothSingleQueries, ih,
      List.length_cons]
    ring

/-- Full committed-proof-oracle opening list of the smooth FRI verifier: `kFinal` final-oracle
interpolation anchors followed by `q` query repetitions. -/
@[expose] def friSmoothQueries (params : FRISmoothParams F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q) :
    List (Fin (params.m + 1) × Fin (2 ^ params.d)) :=
  friSmoothHeaderQueries params ++ friSmoothRepQueriesList params chals (List.finRange params.q)

/-- Total length of `friSmoothQueries` matches `params.proofOracleQueries`. -/
theorem length_friSmoothQueries (params : FRISmoothParams F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q) :
    (friSmoothQueries params chals).length = params.proofOracleQueries := by
  simp only [friSmoothQueries, List.length_append, length_friSmoothHeaderQueries,
    length_friSmoothRepQueriesList, List.length_finRange, FRISmoothParams.proofOracleQueries]

/-- Schedule of `q` scheduled input positions, with multiplicity, at which `stmt` suffices to
determine `friSmoothDecide` outside `PublicCoinIOP.queries`. -/
@[expose] def friSmoothInputQueries (params : FRISmoothParams F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q) :
    List (Fin (2 ^ params.d)) :=
  (List.finRange params.q).map (chals (Fin.last params.m)).queryIdxs

/-- Total length of `friSmoothInputQueries` matches `params.inputWordReads`. -/
theorem length_friSmoothInputQueries (params : FRISmoothParams F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q) :
    (friSmoothInputQueries params chals).length = params.inputWordReads := by
  simp only [friSmoothInputQueries, List.length_map, List.length_finRange,
    FRISmoothParams.inputWordReads]

/-! ### Smooth FRI Final Codeword, Verifier Decisions, and `friSmoothIOP` -/

/-- Final-round Reed–Solomon codeword interpolated from the first `kFinal` entries of `πFinal`. -/
@[expose] def friSmoothFinalCodeword (params : FRISmoothParams F)
    (πFinal : OracleTable params.d F) :
    Fin (2 ^ (params.d - params.totalLog)) → F :=
  fun j =>
    evalLagrange params.finalAnchorPoints
      (fun t : Fin params.kFinal =>
        πFinal ⟨t.val, lt_of_lt_of_le (lt_of_lt_of_le t.isLt params.hkLe)
          (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))⟩)
      (params.eval params.m j)

/-- For ANY arbitrary oracle table `πFinal`, `friSmoothFinalCodeword params πFinal` lies in
`params.rsCode params.m`. -/
theorem friSmoothFinalCodeword_mem_rsCode (params : FRISmoothParams F)
    (πFinal : OracleTable params.d F) :
    friSmoothFinalCodeword params πFinal ∈ params.rsCode params.m := by
  rw [FRISmoothParams.rsCode, params.dim_last]
  exact evalLagrange_mem_reedSolomon params.finalAnchorPoints_injective _ _

/-- Check the smooth folding chain and final Lagrange equation against the flat answer list for a
single repetition starting at `s`. Matching `ans.drop (params.arity i)` against `yNext :: rest`
enforces `params.arity i + 1 ≤ ans.length` identically on malformed short lists. -/
@[expose] def friSmoothCheckFoldList [DecidableEq F] (params : FRISmoothParams F)
    (headerVals : Fin params.kFinal → F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q)
    (s : Fin (2 ^ params.d)) : List (Fin params.m) → List F → Bool
  | [], [yFinal] =>
    decide (yFinal = evalLagrange params.finalAnchorPoints headerVals
      (params.eval params.m (friSmoothFinalFin params s)))
  | i :: is, ans =>
    let a := params.arity i
    match ans.drop a with
    | yNext :: rest =>
      let fiberVals : Fin a → F := fun t => (ans.take a).getD t.val 0
      decide (foldFiber (params.g ^ (2 ^ params.cumLog i.val))
          (params.ω ^ (2 ^ params.cumLog i.val)) fiberVals (friSmoothFoldedFin params i s)
          (chals i.castSucc).foldScalar = yNext) &&
        friSmoothCheckFoldList params headerVals chals s is rest
    | [] => false
  | _, _ => false

/-- Check a single smooth repetition's answer block: round-0 binding to `stmt s` plus all folding
and final-codeword checks. -/
@[expose] def friSmoothCheckSingle [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F) (headerVals : Fin params.kFinal → F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q)
    (s : Fin (2 ^ params.d)) : List F → Bool
  | y0 :: rest =>
    decide (y0 = stmt s) &&
      friSmoothCheckFoldList params headerVals chals s (List.finRange params.m) rest
  | [] => false

/-- Check all smooth repetitions in `reps` by consuming fixed-size blocks of length
`params.singleRepQueries`. -/
@[expose] def friSmoothCheckRepsList [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F) (headerVals : Fin params.kFinal → F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q) :
    List (Fin params.q) → List F → Bool
  | [], [] => true
  | a :: as, ans =>
    let blockLen := params.singleRepQueries
    friSmoothCheckSingle params stmt headerVals chals ((chals (Fin.last params.m)).queryIdxs a)
        (ans.take blockLen) &&
      friSmoothCheckRepsList params stmt headerVals chals as (ans.drop blockLen)
  | _, _ => false

/-- Smooth FRI verifier decision procedure operating purely on `stmt` (determined by the `q`
scheduled input positions, with multiplicity, in `friSmoothInputQueries params chals`), `chals`,
and the flat list of `params.proofOracleQueries` queried prover-oracle answers. -/
@[expose] def friSmoothDecide [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q) (answers : List F) : Bool :=
  decide (answers.length = params.proofOracleQueries) &&
    let headerVals : Fin params.kFinal → F := fun t => (answers.take params.kFinal).getD t.val 0
    friSmoothCheckRepsList params stmt headerVals chals (List.finRange params.q)
      (answers.drop params.kFinal)

private theorem friSmoothCheckSingle_congr_stmt [DecidableEq F] (params : FRISmoothParams F)
    {stmt₁ stmt₂ : OracleTable params.d F} (headerVals : Fin params.kFinal → F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q)
    (s : Fin (2 ^ params.d)) (hs : stmt₁ s = stmt₂ s) (ans : List F) :
    friSmoothCheckSingle params stmt₁ headerVals chals s ans =
      friSmoothCheckSingle params stmt₂ headerVals chals s ans := by
  cases ans <;> simp [friSmoothCheckSingle, hs]

private theorem friSmoothCheckRepsList_congr_stmt [DecidableEq F] (params : FRISmoothParams F)
    {stmt₁ stmt₂ : OracleTable params.d F} (headerVals : Fin params.kFinal → F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q)
    (reps : List (Fin params.q))
    (hagree : ∀ a ∈ reps,
      stmt₁ ((chals (Fin.last params.m)).queryIdxs a) =
        stmt₂ ((chals (Fin.last params.m)).queryIdxs a))
    (ans : List F) :
    friSmoothCheckRepsList params stmt₁ headerVals chals reps ans =
      friSmoothCheckRepsList params stmt₂ headerVals chals reps ans := by
  induction reps generalizing ans with
  | nil => cases ans <;> rfl
  | cons a as ih =>
    simp only [friSmoothCheckRepsList]
    rw [friSmoothCheckSingle_congr_stmt params headerVals chals _ (hagree a List.mem_cons_self),
      ih (fun b hb => hagree b (List.mem_cons_of_mem a hb))]

/-- `friSmoothDecide` depends on the input word `stmt` only at the `q` scheduled input positions,
with multiplicity, in `friSmoothInputQueries params chals` (`params.inputWordReads = q` budget). -/
theorem friSmoothDecide_congr_inputQueries [DecidableEq F] (params : FRISmoothParams F)
    {stmt₁ stmt₂ : OracleTable params.d F}
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q)
    (hagree : ∀ s ∈ friSmoothInputQueries params chals, stmt₁ s = stmt₂ s)
    (answers : List F) :
    friSmoothDecide params stmt₁ chals answers = friSmoothDecide params stmt₂ chals answers := by
  simp only [friSmoothDecide]
  congr 1
  exact friSmoothCheckRepsList_congr_stmt params _ chals (List.finRange params.q)
    (fun a ha => hagree _ (List.mem_map.mpr ⟨a, ha, rfl⟩)) _

/-- **Multi-round smooth `2^{sᵢ}`-to-1 FRI as a `PublicCoinIOP`**
([BenSassonCarmonIshaiKoppartySaraf2020], Section 8.2, printed pp. 36–38):
* `m + 1` rounds over depth-`d` oracle tables `OracleTable d F`.
* Honest prover sends `padOracle (friSmoothHonestWord ...)` using previous rounds' `foldScalar`s.
* Verifier opens `params.proofOracleQueries = kFinal + q * (aritySum + m + 2)` entries in the
  committed prover oracles, schedules `params.inputWordReads = q` input positions (with
  multiplicity) of `stmt`, and checks round-0 binding, all `m` `l⁽ⁱ⁾`-to-1 folding checks, and the
  final degree-`< kFinal` Lagrange-anchor check. -/
@[expose] def friSmoothIOP [DecidableEq F] (params : FRISmoothParams F) :
    PublicCoinIOP (params.m + 1) params.d (OracleTable params.d F) Unit F
      (FRIChal F params.d params.q) where
  proveRound j stmt _ prevChals :=
    padOracle (friSmoothHonestWord params stmt j.val (Nat.le_of_lt_succ j.isLt)
      (fun i => (prevChals i).foldScalar))
  queries _ chals := friSmoothQueries params chals
  decide stmt chals answers := friSmoothDecide params stmt chals answers

/-- Exact committed-proof-oracle opening count of `friSmoothIOP`:
`params.proofOracleQueries = kFinal + q * (aritySum + m + 2)` for every statement and challenge
vector. -/
theorem length_friSmoothIOP_queries [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q) :
    ((friSmoothIOP params).queries stmt chals).length = params.proofOracleQueries :=
  length_friSmoothQueries params chals

/-- Clean mathematical acceptance predicate for a single smooth FRI query repetition starting at
`s : Fin (2 ^ d)`: round-0 binding `oracles 0 s = stmt s`, all `m` `l⁽ⁱ⁾`-to-1 folding checks
along the powering chain of `s`, and final-round agreement with `friSmoothFinalCodeword`. -/
@[expose] def friSmoothSingleAccepts (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q)
    (oracles : Fin (params.m + 1) → OracleTable params.d F) (s : Fin (2 ^ params.d)) : Prop :=
  oracles ⟨0, Nat.zero_lt_succ params.m⟩ s = stmt s ∧
  (∀ i : Fin params.m,
    foldFiber (params.g ^ (2 ^ params.cumLog i.val))
      (params.ω ^ (2 ^ params.cumLog i.val))
      (fun t : Fin (params.arity i) => oracles i.castSucc (friSmoothFiberIdx params i s t))
      (friSmoothFoldedFin params i s)
      (chals i.castSucc).foldScalar =
    oracles i.succ (friSmoothFoldedIdx params i s)) ∧
  oracles (Fin.last params.m) (friSmoothFinalIdx params s) =
    friSmoothFinalCodeword params (oracles (Fin.last params.m)) (friSmoothFinalFin params s)

private theorem getD_map_ofFn {α β : Type*} {n : ℕ} (f : Fin n → α) (g : α → β) (d : β) :
    (fun t : Fin n => ((List.ofFn f).map g).getD t.val d) = fun t => g (f t) := by
  funext t
  simp [List.length_ofFn, t.isLt]

private theorem friSmoothCheckFoldList_map [DecidableEq F] (params : FRISmoothParams F)
    (headerVals : Fin params.kFinal → F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q)
    (oracles : Fin (params.m + 1) → OracleTable params.d F) (s : Fin (2 ^ params.d))
    (rounds : List (Fin params.m)) :
    friSmoothCheckFoldList params headerVals chals s rounds
        ((friSmoothFoldQueriesList params s rounds).map fun p => oracles p.1 p.2) = true ↔
      (∀ i ∈ rounds,
        foldFiber (params.g ^ (2 ^ params.cumLog i.val))
          (params.ω ^ (2 ^ params.cumLog i.val))
          (fun t : Fin (params.arity i) => oracles i.castSucc (friSmoothFiberIdx params i s t))
          (friSmoothFoldedFin params i s)
          (chals i.castSucc).foldScalar =
        oracles i.succ (friSmoothFoldedIdx params i s)) ∧
      oracles (Fin.last params.m) (friSmoothFinalIdx params s) =
        evalLagrange params.finalAnchorPoints headerVals
          (params.eval params.m (friSmoothFinalFin params s)) := by
  induction rounds with
  | nil => simp [friSmoothFoldQueriesList, friSmoothCheckFoldList]
  | cons i is ih =>
    have hlen : ((List.ofFn fun t : Fin (params.arity i) =>
        (i.castSucc, friSmoothFiberIdx params i s t)).map fun p => oracles p.1 p.2).length =
        params.arity i := by simp
    simp only [friSmoothFoldQueriesList, List.map_append, List.map_cons, friSmoothCheckFoldList,
      List.drop_left' hlen, List.take_left' hlen, getD_map_ofFn, Bool.and_eq_true,
      decide_eq_true_eq, ih, List.mem_cons, forall_eq_or_imp, and_assoc]

private theorem friSmoothCheckSingle_map [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q)
    (oracles : Fin (params.m + 1) → OracleTable params.d F) (s : Fin (2 ^ params.d)) :
    friSmoothCheckSingle params stmt
        (fun t : Fin params.kFinal =>
          oracles (Fin.last params.m)
            ⟨t.val, lt_of_lt_of_le (lt_of_lt_of_le t.isLt params.hkLe)
              (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))⟩)
        chals s ((friSmoothSingleQueries params s).map fun p => oracles p.1 p.2) = true ↔
      friSmoothSingleAccepts params stmt chals oracles s := by
  simp only [friSmoothSingleQueries, List.map_cons, friSmoothCheckSingle, Bool.and_eq_true,
    decide_eq_true_eq, friSmoothCheckFoldList_map, List.mem_finRange, true_implies,
    friSmoothSingleAccepts, friSmoothFinalCodeword]

private theorem friSmoothCheckRepsList_map [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q)
    (oracles : Fin (params.m + 1) → OracleTable params.d F) (reps : List (Fin params.q)) :
    friSmoothCheckRepsList params stmt
        (fun t : Fin params.kFinal =>
          oracles (Fin.last params.m)
            ⟨t.val, lt_of_lt_of_le (lt_of_lt_of_le t.isLt params.hkLe)
              (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))⟩)
        chals reps ((friSmoothRepQueriesList params chals reps).map fun p => oracles p.1 p.2) =
        true ↔
      ∀ a ∈ reps,
        friSmoothSingleAccepts params stmt chals oracles
          ((chals (Fin.last params.m)).queryIdxs a) := by
  induction reps with
  | nil => simp [friSmoothRepQueriesList, friSmoothCheckRepsList]
  | cons a as ih =>
    have hlen : ((friSmoothSingleQueries params ((chals (Fin.last params.m)).queryIdxs a)).map
        fun p => oracles p.1 p.2).length = params.singleRepQueries := by
      simp [length_friSmoothSingleQueries]
    simp only [friSmoothRepQueriesList, List.map_append, friSmoothCheckRepsList,
      List.take_left' hlen, List.drop_left' hlen, Bool.and_eq_true, friSmoothCheckSingle_map, ih,
      List.mem_cons, forall_eq_or_imp]

/-! ### Smooth FRI Completeness and BCS-ROM Compilation -/

/-- **Exact characterization of smooth FRI IOP verification**: `iopVerify (friSmoothIOP params)`
accepts `oracles` on `(stmt, chals)` if and only if every queried starting position
`(chals (Fin.last m)).queryIdxs a` satisfies `friSmoothSingleAccepts`. -/
theorem iopVerify_friSmoothIOP_eq_true_iff [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q)
    (oracles : Fin (params.m + 1) → OracleTable params.d F) :
    iopVerify (friSmoothIOP params) stmt chals oracles = true ↔
      ∀ a : Fin params.q,
        friSmoothSingleAccepts params stmt chals oracles
          ((chals (Fin.last params.m)).queryIdxs a) := by
  have hhdr_len : ((friSmoothHeaderQueries params).map fun p => oracles p.1 p.2).length =
      params.kFinal := by simp
  simp only [iopVerify, iopAnswers, friSmoothIOP, friSmoothDecide, List.length_map,
    length_friSmoothQueries, decide_true, Bool.true_and]
  rw [friSmoothQueries, List.map_append, List.take_left' hhdr_len, List.drop_left' hhdr_len]
  simp [friSmoothHeaderQueries, friSmoothCheckRepsList_map]

/-- **Perfect completeness of the smooth FRI IOP**: for every codeword `f₀ ∈ params.initialCode`
and every challenge vector `chals`, the smooth FRI verifier accepts the honest prover's tables. -/
theorem friSmoothIOP_complete [DecidableEq F] (params : FRISmoothParams F) :
    IOPCompleteness (friSmoothIOP params) params.completenessRel := by
  intro f₀ _ hf₀ chals
  rw [iopVerify_friSmoothIOP_eq_true_iff]
  intro a
  set s := (chals (Fin.last params.m)).queryIdxs a
  refine ⟨?_, fun i => ?_, ?_⟩
  · simp only [iopProverOracles, friSmoothIOP, padOracle, FRISmoothParams.cumLog, friCumLog_zero,
      Nat.sub_zero, s.isLt, ↓reduceDIte, friSmoothHonestWord]
  · simp only [iopProverOracles, friSmoothIOP, Fin.val_castSucc, Fin.val_succ,
      padOracle_apply_of_lt _ _ (friSmoothFiberIdx_val_lt params i s _)]
    rw [padOracle_apply_of_lt _ (friSmoothFoldedIdx params i s)
        (friSmoothFoldedFin params i s).isLt, friSmoothHonestWord_succ_apply,
      friSmoothHonestWord_congr params f₀ i.val (Nat.le_of_succ_le i.isLt) fun _ => rfl]
    rfl
  · have hmem := friSmoothHonestWord_mem_rsCode params hf₀ params.m le_rfl
      (fun k => (prefixChallenges chals (Fin.last params.m) k).foldScalar)
    rw [FRISmoothParams.rsCode, params.dim_last] at hmem
    simp only [iopProverOracles, friSmoothIOP, Fin.val_last, friSmoothFinalCodeword,
      padOracle_apply_of_lt _ (friSmoothFinalIdx params s) (friSmoothFinalFin params s).isLt]
    conv_rhs => arg 2; ext t; rw [padOracle_apply_of_lt _ _ (lt_of_lt_of_le t.isLt params.hkLe)]
    exact (evalLagrange_eq_of_mem_reedSolomon params.hkLe
      (cosetEval_injective params.hg params.hω params.htotal) hmem
      (friSmoothFinalFin params s)).symm

/-- **Perfect deterministic BCS completeness for smooth FRI**: for any fixed-length hash `H k`,
Fiat–Shamir function `hFS`, and symbol encoding `encSym`, `bcsVerify` accepts `bcsProve` on every
codeword `f₀ ∈ params.initialCode`. -/
theorem friSmoothBCS_verify_prove_eq_true [DecidableEq F] (params : FRISmoothParams F)
    (H : List Bool → List Bool → List Bool) (k : List Bool) {ℓ : ℕ}
    (hlen : ∀ y, (H k y).length = ℓ) (encSym : F → List Bool)
    (hFS : OracleTable params.d F → List (List Bool) → FRIChal F params.d params.q)
    {f₀ : OracleTable params.d F} (hf₀ : f₀ ∈ params.initialCode) :
    bcsVerify (friSmoothIOP params) H k encSym hFS f₀
      (bcsProve (friSmoothIOP params) H k encSym hFS f₀ ()) = true :=
  bcsVerify_bcsProve_eq_true (friSmoothIOP_complete params) H k hlen encSym hFS hf₀

/-- **Perfect BCS ROM completeness for smooth FRI**: in the lazy two-channel random-oracle model
with any digest length `σ`, the honest BCS-FRI game outputs `PMF.pure true` for every codeword
`f₀ ∈ params.initialCode`. -/
theorem friSmoothBCS_honestROMGame_eq_pure_true [DecidableEq F] [Fintype F]
    (params : FRISmoothParams F) (encSym : F → List Bool) {f₀ : OracleTable params.d F}
    (hf₀ : f₀ ∈ params.initialCode) (σ : ℕ) :
    bcsHonestROMGame (friSmoothIOP params) encSym f₀ () σ = PMF.pure true :=
  bcsHonestROMGame_eq_pure_true (friSmoothIOP_complete params) encSym hf₀ σ

/-- **Succinct verifier Merkle query cost bound for BCS-compiled smooth FRI**: for any proof `prf`
whose opening paths have length at most `L_path`, `bcsVerifyROM` makes at most
`params.proofOracleQueries * (L_path + 1) = (kFinal + q * (aritySum + m + 2)) * (L_path + 1)`
Merkle hash queries. -/
theorem isCostBounded_bcsMTCost_friSmoothVerifyROM [DecidableEq F] (params : FRISmoothParams F)
    (encSym : F → List Bool) (stmt : OracleTable params.d F)
    (prf : BCSProof (params.m + 1) F) {L_path : ℕ}
    (hops : ∀ op ∈ prf.openings, op.path.length ≤ L_path) :
    IsCostBounded bcsMTCost (bcsVerifyROM (friSmoothIOP params) encSym stmt prf)
      (params.proofOracleQueries * (L_path + 1)) :=
  isCostBounded_bcsMTCost_bcsVerifyROM_of_queries_le (friSmoothIOP params) encSym stmt prf
    (fun chals => (length_friSmoothIOP_queries params stmt chals).le) hops

end FRISmoothProtocol

/-! ### Binary 2-to-1 FRI Query Schedules and `friIOP` -/

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

/-- Header queries reading the first `kFinal` entries of the final oracle `π_m` (derived directly
from `friSmoothHeaderQueries params.toSmooth`). -/
@[expose] def friHeaderQueries (params : FRIParams F) :
    List (Fin (params.m + 1) × Fin (2 ^ params.d)) :=
  friSmoothHeaderQueries params.toSmooth

/-- The binary header query schedule reads `params.kFinal` entries of the final oracle. -/
@[simp]
theorem length_friHeaderQueries (params : FRIParams F) :
    (friHeaderQueries params).length = params.kFinal :=
  length_friSmoothHeaderQueries params.toSmooth

/-- Folding-chain queries along a list of rounds `rounds` followed by the final-round check
(derived directly from `friSmoothFoldQueriesList params.toSmooth`). -/
@[expose] def friFoldQueriesList (params : FRIParams F) (s : Fin (2 ^ params.d)) :
    List (Fin params.m) → List (Fin (params.m + 1) × Fin (2 ^ params.d)) :=
  friSmoothFoldQueriesList params.toSmooth s

/-- Number of binary folding-chain queries generated along `rounds` (`3 * rounds.length + 1`). -/
theorem length_friFoldQueriesList (params : FRIParams F) (s : Fin (2 ^ params.d))
    (rounds : List (Fin params.m)) :
    (friFoldQueriesList params s rounds).length = 3 * rounds.length + 1 := by
  rw [friFoldQueriesList, length_friSmoothFoldQueriesList]
  simp [params.toSmooth_arity, List.map_const', List.sum_replicate, mul_comm]

/-- All oracle queries for a single query repetition starting at `s : Fin (2 ^ d)` (derived
directly from `friSmoothSingleQueries params.toSmooth`). -/
@[expose] def friSingleQueries (params : FRIParams F) (s : Fin (2 ^ params.d)) :
    List (Fin (params.m + 1) × Fin (2 ^ params.d)) :=
  friSmoothSingleQueries params.toSmooth s

/-- A single binary query repetition contains `3 * params.m + 2` proof-oracle openings. -/
@[simp]
theorem length_friSingleQueries (params : FRIParams F) (s : Fin (2 ^ params.d)) :
    (friSingleQueries params s).length = 3 * params.m + 2 := by
  rw [friSingleQueries, length_friSmoothSingleQueries, params.toSmooth_singleRepQueries]

/-- Concatenated queries for a list of repetition indices `reps : List (Fin q)` (derived directly
from `friSmoothRepQueriesList params.toSmooth`). -/
@[expose] def friRepQueriesList (params : FRIParams F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q) :
    List (Fin params.q) → List (Fin (params.m + 1) × Fin (2 ^ params.d)) :=
  friSmoothRepQueriesList params.toSmooth chals

/-- Total length of concatenated binary queries across `reps`. -/
theorem length_friRepQueriesList (params : FRIParams F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q) (reps : List (Fin params.q)) :
    (friRepQueriesList params chals reps).length = reps.length * (3 * params.m + 2) := by
  rw [friRepQueriesList, length_friSmoothRepQueriesList, params.toSmooth_singleRepQueries]

/-- Full committed-proof-oracle opening list of the FRI verifier: `kFinal` final-oracle
interpolation anchors followed by `q` query repetitions (derived directly from
`friSmoothQueries params.toSmooth`). This excludes the `q` scheduled input positions, with
multiplicity, tracked by `friInputQueries`. -/
@[expose] def friQueries (params : FRIParams F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q) :
    List (Fin (params.m + 1) × Fin (2 ^ params.d)) :=
  friSmoothQueries params.toSmooth chals

/-- Total length of `friQueries` matches `params.proofOracleQueries`. -/
theorem length_friQueries (params : FRIParams F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q) :
    (friQueries params chals).length = params.proofOracleQueries := by
  rw [friQueries, length_friSmoothQueries, params.toSmooth_proofOracleQueries]

/-- Schedule of `q` scheduled input positions, with multiplicity, at which `stmt` suffices to
determine `friDecide` outside `PublicCoinIOP.queries` (derived directly from
`friSmoothInputQueries params.toSmooth`). -/
@[expose] def friInputQueries (params : FRIParams F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q) :
    List (Fin (2 ^ params.d)) :=
  friSmoothInputQueries params.toSmooth chals

/-- Total length of `friInputQueries` matches `params.inputWordReads`. -/
theorem length_friInputQueries (params : FRIParams F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q) :
    (friInputQueries params chals).length = params.inputWordReads :=
  length_friSmoothInputQueries params.toSmooth chals

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
  simp only [FRIParams.rsCode, FRIParams.dim, Nat.sub_self, pow_zero, mul_one]
  exact evalLagrange_mem_reedSolomon params.finalAnchorPoints_injective _ _

/-- Check the folding chain and final Lagrange equation against the answer list for a single
repetition starting at `s` (derived directly from `friSmoothCheckFoldList params.toSmooth`). -/
@[expose] def friCheckFoldList [DecidableEq F] (params : FRIParams F)
    (headerVals : Fin params.kFinal → F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q)
    (s : Fin (2 ^ params.d)) : List (Fin params.m) → List F → Bool :=
  friSmoothCheckFoldList params.toSmooth headerVals chals s

/-- Check a single repetition's answer block: round-0 binding to `stmt s` plus all folding and
final-codeword checks (derived directly from `friSmoothCheckSingle params.toSmooth`). -/
@[expose] def friCheckSingle [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F) (headerVals : Fin params.kFinal → F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q)
    (s : Fin (2 ^ params.d)) : List F → Bool :=
  friSmoothCheckSingle params.toSmooth stmt headerVals chals s

/-- Check all repetitions in `reps` by consuming fixed-size blocks of length `3 * m + 2` (derived
directly from `friSmoothCheckRepsList params.toSmooth`). -/
@[expose] def friCheckRepsList [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F) (headerVals : Fin params.kFinal → F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q) :
    List (Fin params.q) → List F → Bool :=
  friSmoothCheckRepsList params.toSmooth stmt headerVals chals

/-- FRI verifier decision procedure operating purely on `stmt` (determined by the `q` scheduled
input positions, with multiplicity, in `friInputQueries params chals`), `chals`, and the flat list
of `params.proofOracleQueries` queried prover-oracle answers (derived directly from
`friSmoothDecide params.toSmooth`). -/
@[expose] def friDecide [DecidableEq F] (params : FRIParams F) (stmt : OracleTable params.d F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q) (answers : List F) : Bool :=
  friSmoothDecide params.toSmooth stmt chals answers

/-- **Multi-round 2-to-1 FRI as a `PublicCoinIOP`**:
* `m + 1` rounds over depth-`d` oracle tables `OracleTable d F`.
* Honest prover sends `padOracle (friHonestWord ...)` using the previous rounds' `foldScalar`s.
* Verifier opens `params.proofOracleQueries = kFinal + q * (3 * m + 2)` entries in the committed
  prover oracles (via `queries`), schedules `params.inputWordReads = q` input positions, with
  multiplicity, of `stmt` (tracked by `friInputQueries`, for the combined word-query budget
  `params.totalWordQueries = kFinal + q * (3 * m + 3)`), and checks round-0 binding to `stmt`, all
  `m` folding checks, and the final degree-`< kFinal` Lagrange-anchor check. -/
@[expose] def friIOP [DecidableEq F] (params : FRIParams F) :
    PublicCoinIOP (params.m + 1) params.d (OracleTable params.d F) Unit F
      (FRIChal F params.d params.q) where
  proveRound j stmt _ prevChals :=
    padOracle (friHonestWord params stmt j.val (Nat.le_of_lt_succ j.isLt)
      (fun i => (prevChals i).foldScalar))
  queries _ chals := friQueries params chals
  decide stmt chals answers := friDecide params stmt chals answers

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

/-! ### Binary-to-Smooth Bridges, Completeness, and BCS-ROM Compilation -/

/-- At `params.toSmooth`, the smooth folded target index `friSmoothFoldedIdx` equals the binary
positive index `friRoundPosIdx`. -/
theorem friSmoothFoldedIdx_toSmooth (params : FRIParams F) (i : Fin params.m)
    (s : Fin (2 ^ params.d)) :
    friSmoothFoldedIdx params.toSmooth i s = friRoundPosIdx params i s :=
  Fin.ext (by simp [friSmoothFoldedIdx, friRoundPosIdx, params.toSmooth_cumLog i.isLt])

/-- At `params.toSmooth`, fiber point `0` of `friSmoothFiberIdx` equals `friRoundPosIdx`. -/
theorem friSmoothFiberIdx_toSmooth_zero (params : FRIParams F) (i : Fin params.m)
    (s : Fin (2 ^ params.d)) :
    friSmoothFiberIdx params.toSmooth i s ⟨0, by simp⟩ = friRoundPosIdx params i s :=
  Fin.ext (by simp [friSmoothFiberIdx, friRoundPosIdx, params.toSmooth_cumLog i.isLt])

/-- At `params.toSmooth`, fiber point `1` of `friSmoothFiberIdx` equals `friRoundNegIdx`. -/
theorem friSmoothFiberIdx_toSmooth_one (params : FRIParams F) (i : Fin params.m)
    (s : Fin (2 ^ params.d)) :
    friSmoothFiberIdx params.toSmooth i s ⟨1, by simp⟩ = friRoundNegIdx params i s :=
  Fin.ext (by simp [friSmoothFiberIdx, friRoundNegIdx, params.toSmooth_cumLog i.isLt])

/-- At `params.toSmooth`, the smooth final-domain index `friSmoothFinalIdx` equals `friFinalIdx`. -/
theorem friSmoothFinalIdx_toSmooth (params : FRIParams F) (s : Fin (2 ^ params.d)) :
    friSmoothFinalIdx params.toSmooth s = friFinalIdx params s :=
  Fin.ext (by simp [friSmoothFinalIdx, friFinalIdx, params.toSmooth_totalLog])

/-- At `params.toSmooth`, final-round domain evaluation coincides with `FRIParams.eval`. -/
theorem eval_toSmooth_final (params : FRIParams F) (s : Fin (2 ^ params.d)) :
    params.toSmooth.eval params.m (friSmoothFinalFin params.toSmooth s) =
      params.eval params.m (friFinalFin params s) := by
  simp [FRISmoothParams.eval, FRIParams.eval, friSmoothFinalFin, friFinalFin, cosetEval,
    cosetPoint, params.toSmooth_totalLog]

/-- At `params.toSmooth`, the general smooth fiber fold `foldFiber` coincides with binary
`fold2Fiber`. -/
theorem foldFiber_toSmooth_eq_fold2Fiber (params : FRIParams F) (i : Fin params.m)
    (ys : Fin (params.toSmooth.arity i) → F) (s : Fin (2 ^ params.d)) (z : F) :
    foldFiber (params.g ^ (2 ^ params.toSmooth.cumLog i.val))
        (params.ω ^ (2 ^ params.toSmooth.cumLog i.val)) ys
        (friSmoothFoldedFin params.toSmooth i s) z =
      fold2Fiber (ys ⟨0, by simp⟩) (ys ⟨1, by simp⟩)
        (params.eval i.val (friRoundPosFin params i s)) z := by
  rw [foldFiber_toSmooth_eq_fold2Fiber_at params i ys (friSmoothFoldedFin params.toSmooth i s) z]
  congr 2
  exact Fin.ext (by simp [friSmoothFoldedFin, friRoundPosFin, params.toSmooth_cumLog i.isLt])

/-- **Exact IOP equality**: binary 2-to-1 `friIOP params` coincides identically with
`friSmoothIOP params.toSmooth` across `proveRound`, `queries`, and `decide`. -/
theorem friIOP_eq_friSmoothIOP [DecidableEq F] (params : FRIParams F) :
    friIOP params = friSmoothIOP params.toSmooth := by
  dsimp only [friIOP, friSmoothIOP]
  congr 1
  funext j stmt _ prevChals
  exact padOracle_friHonestWord_eq_smooth params stmt j.val (Nat.le_of_lt_succ j.isLt) _

/-- Exact equivalence between binary `friSingleAccepts` and smooth
`friSmoothSingleAccepts params.toSmooth`. -/
theorem friSingleAccepts_iff_friSmoothSingleAccepts (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q)
    (oracles : Fin (params.m + 1) → OracleTable params.d F) (s : Fin (2 ^ params.d)) :
    friSingleAccepts params stmt chals oracles s ↔
      friSmoothSingleAccepts params.toSmooth stmt chals oracles s := by
  simp only [friSingleAccepts, friSmoothSingleAccepts, friSmoothFoldedIdx_toSmooth,
    friSmoothFinalIdx_toSmooth, friFinalCodeword, friSmoothFinalCodeword,
    params.toSmooth_finalAnchorPoints, eval_toSmooth_final]
  refine and_congr_right fun _ => and_congr_left fun _ => forall_congr' fun i => ?_
  rw [foldFiber_toSmooth_eq_fold2Fiber params i
    (fun t : Fin (params.toSmooth.arity i) =>
      oracles i.castSucc (friSmoothFiberIdx params.toSmooth i s t)) s
    (chals i.castSucc).foldScalar, friSmoothFiberIdx_toSmooth_zero, friSmoothFiberIdx_toSmooth_one]

/-- `friDecide` depends on the input word `stmt` only at the `q` scheduled input positions, with
multiplicity, in `friInputQueries params chals` (corollary of
`friSmoothDecide_congr_inputQueries`). -/
theorem friDecide_congr_inputQueries [DecidableEq F] (params : FRIParams F)
    {stmt₁ stmt₂ : OracleTable params.d F}
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q)
    (hagree : ∀ s ∈ friInputQueries params chals, stmt₁ s = stmt₂ s)
    (answers : List F) :
    friDecide params stmt₁ chals answers = friDecide params stmt₂ chals answers :=
  friSmoothDecide_congr_inputQueries params.toSmooth chals hagree answers

/-- Exact committed-proof-oracle opening count of `friIOP`:
`params.proofOracleQueries = kFinal + q * (3 * m + 2)` for every statement and challenge vector
(excluding the `params.inputWordReads = q` scheduled input positions, with multiplicity, tracked
by `friInputQueries`). -/
theorem length_friIOP_queries [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q) :
    ((friIOP params).queries stmt chals).length = params.proofOracleQueries := by
  rw [friIOP_eq_friSmoothIOP, length_friSmoothIOP_queries, params.toSmooth_proofOracleQueries]

/-- **Exact characterization of FRI IOP verification** (corollary of
`iopVerify_friSmoothIOP_eq_true_iff`): `iopVerify (friIOP params)` accepts `oracles` on
`(stmt, chals)` if and only if every queried starting position `(chals (Fin.last m)).queryIdxs a`
satisfies `friSingleAccepts`. -/
theorem iopVerify_friIOP_eq_true_iff [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q)
    (oracles : Fin (params.m + 1) → OracleTable params.d F) :
    iopVerify (friIOP params) stmt chals oracles = true ↔
      ∀ a : Fin params.q,
        friSingleAccepts params stmt chals oracles ((chals (Fin.last params.m)).queryIdxs a) := by
  rw [friIOP_eq_friSmoothIOP, iopVerify_friSmoothIOP_eq_true_iff]
  exact forall_congr' fun a => (friSingleAccepts_iff_friSmoothSingleAccepts params stmt chals
    oracles _).symm

/-- **Perfect completeness of the FRI IOP** (corollary of `friSmoothIOP_complete`): for every
codeword `f₀ ∈ params.initialCode` and every challenge vector `chals`, the FRI verifier accepts the
honest prover's oracle tables. -/
theorem friIOP_complete [DecidableEq F] (params : FRIParams F) :
    IOPCompleteness (friIOP params) params.completenessRel := by
  rw [friIOP_eq_friSmoothIOP, ← params.toSmooth_completenessRel]
  exact friSmoothIOP_complete params.toSmooth

/-- **Perfect deterministic BCS completeness for FRI** (corollary of
`friSmoothBCS_verify_prove_eq_true`): for any hash function `H k` whose digests all have one
length, any Fiat–Shamir function `hFS`, and any symbol encoding `encSym`, `bcsVerify` accepts
`bcsProve` on every codeword `f₀ ∈ params.initialCode`. -/
theorem friBCS_verify_prove_eq_true [DecidableEq F] (params : FRIParams F)
    (H : List Bool → List Bool → List Bool) (k : List Bool) {ℓ : ℕ}
    (hlen : ∀ y, (H k y).length = ℓ) (encSym : F → List Bool)
    (hFS : OracleTable params.d F → List (List Bool) → FRIChal F params.d params.q)
    {f₀ : OracleTable params.d F} (hf₀ : f₀ ∈ params.initialCode) :
    bcsVerify (friIOP params) H k encSym hFS f₀
      (bcsProve (friIOP params) H k encSym hFS f₀ ()) = true :=
  friIOP_eq_friSmoothIOP params ▸ friSmoothBCS_verify_prove_eq_true params.toSmooth H k hlen
    encSym hFS (params.toSmooth_initialCode.symm ▸ hf₀)

/-- **Perfect BCS ROM completeness for FRI** (corollary of
`friSmoothBCS_honestROMGame_eq_pure_true`): in the lazy two-channel random-oracle model with any
digest length `σ`, the honest BCS-FRI game outputs `PMF.pure true` for every codeword
`f₀ ∈ params.initialCode`. -/
theorem friBCS_honestROMGame_eq_pure_true [DecidableEq F] [Fintype F] (params : FRIParams F)
    (encSym : F → List Bool) {f₀ : OracleTable params.d F} (hf₀ : f₀ ∈ params.initialCode)
    (σ : ℕ) :
    bcsHonestROMGame (friIOP params) encSym f₀ () σ = PMF.pure true :=
  friIOP_eq_friSmoothIOP params ▸ friSmoothBCS_honestROMGame_eq_pure_true params.toSmooth encSym
    (params.toSmooth_initialCode.symm ▸ hf₀) σ

/-- **Succinct verifier Merkle query cost bound for BCS-compiled FRI** (corollary of
`isCostBounded_bcsMTCost_friSmoothVerifyROM`): for any proof `prf` whose opening paths have length
at most `L_path`, `bcsVerifyROM` makes at most
`params.proofOracleQueries * (L_path + 1) = (kFinal + q * (3 * m + 2)) * (L_path + 1)` Merkle hash
queries. -/
theorem isCostBounded_bcsMTCost_friVerifyROM [DecidableEq F] (params : FRIParams F)
    (encSym : F → List Bool) (stmt : OracleTable params.d F)
    (prf : BCSProof (params.m + 1) F) {L_path : ℕ}
    (hops : ∀ op ∈ prf.openings, op.path.length ≤ L_path) :
    IsCostBounded bcsMTCost (bcsVerifyROM (friIOP params) encSym stmt prf)
      (params.proofOracleQueries * (L_path + 1)) := by
  rw [friIOP_eq_friSmoothIOP, ← params.toSmooth_proofOracleQueries]
  exact isCostBounded_bcsMTCost_friSmoothVerifyROM params.toSmooth encSym stmt prf hops

end FRIProtocol

end Cslib.Crypto.Protocols.FRI
