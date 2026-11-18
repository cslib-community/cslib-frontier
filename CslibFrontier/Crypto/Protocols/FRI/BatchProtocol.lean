/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.FRI.Protocol
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import CslibFrontier.Foundations.Data.Hamming
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Batched Multi-Round FRI as a Public-Coin Interactive Oracle Proof

This module instantiates the batched Fast Reed–Solomon Interactive Oracle Proof of Proximity (FRI)
of [BenSassonCarmonIshaiKoppartySaraf2020] (accepted *Journal of the ACM* 2023 manuscript, Section
8.2, printed pp. 36–38: affine batching Eq. (8.3) on p. 37 and batched QUERY steps (1)–(4) on
p. 38) directly as a `(params.m + 2)`-round `Cslib.Crypto.Protocols.BCS.PublicCoinIOP` delegating
its folding and query phases to `Cslib.Crypto.Protocols.FRI.friIOP`
([BenSassonBentovHoreshRiabzev2018]; [BenSassonChiesaSpooner2016]), proves perfect IOP / BCS /
random-oracle completeness together with exact committed-opening counts and direct-read schedule
locality, and defines the tuple correlated-agreement languages and real-to-integer threshold
bridges used in the setting of Lemma 8.2 and Theorem 8.3 (printed pp. 38–39; soundness of batched
FRI remains tracked in #5968).

## Protocol layout and causal delegation

Given `params : FRIParams F`, batch size `t : ℕ`, and an affine batch statement
`stmt : FRIBatchStmt F params.d t` representing `(t + 1)` initial words
`f₀⁽⁰⁾ = stmt.base` and `f₁⁽⁰⁾, …, f_t⁽⁰⁾ = stmt.terms` on the coset of size `2 ^ d` (with
homogeneous linear batching `f₀⁽⁰⁾ = 0` given by `FRIBatchStmt.linear`):

* **Causal `(m + 2)`-round schedule.** In `PublicCoinIOP`, `proveRound 0` executes prior to
  sampling `chals 0`, whereas the honest batched oracle
  `stmt.eval x = stmt.base + ∑ j : Fin t, x j • stmt.terms j` (Eq. (8.3), p. 37) depends on the
  verifier's random batching vector `x : Fin t → F` and must be committed before the first folding
  scalar `z⁽⁰⁾`. Accordingly, `friBatchIOP params t` runs for `params.m + 2` rounds over
  `FRIBatchChal F params.d params.q t`:
  - **Round `0`:** the honest prover outputs the zero announcement table (`0` openings in
    `PublicCoinIOP.queries`), and the verifier samples `(chals 0).batchCoeffs : Fin t → F`.
  - **Rounds `1, …, m + 1`:** the protocol delegates `proveRound`, `queries` (shifted by
    `Fin.succ`), and `decide` directly to `friIOP params` evaluated on the combined word
    `stmt.eval (chals 0).batchCoeffs` and challenge tail `friTailChals chals`.
* **Batched query check, committed-opening count, and direct-read schedule.** By
  `iopVerify_friBatchIOP_eq_iopVerify_friIOP` and `iopVerify_friBatchIOP_eq_true_iff`,
  `friBatchSingleAccepts` delegates directly to `friSingleAccepts` on the evaluated batch
  `stmt.eval (chals 0).batchCoeffs`, challenge tail `friTailChals chals`, and shifted oracle family
  `fun j => oracles j.succ` (checking the round-`1` batching equation, all `m` 2-to-1 folding steps,
  and final codeword consistency; Section 8.2, p. 38, steps (2)–(4)). The committed-proof-oracle
  opening list exposed via `PublicCoinIOP.queries` has **exact** length
  `params.proofOracleQueries = kFinal + q * (3 * m + 2)` (`length_friBatchIOP_queries`, with zero
  openings against round `0`). Outside `PublicCoinIOP.queries`, `friBatchInputQueries` schedules `q`
  input positions at which `t + 1` input symbols suffice (`friBatchDecide_congr_inputQueries`
  proves that agreement at these scheduled positions determines `friBatchDecide`). Because a
  wrong-length answer list or an unsuccessful earlier repetition can reject before inspecting later
  positions, `params.batchInputWordReads t = (t + 1) * q` records the full direct-read schedule /
  budget, giving the combined word-query budget
  `params.batchTotalWordQueries t = kFinal + q * (3 * m + t + 3)`.
* **Tuple correlated-agreement languages and real-to-integer threshold bridges.**
  `FRIParams.batchProximityLang` expresses simultaneous correlated agreement of `(stmt.base,
  stmt.terms)` with `params.initialCode` on at least `2 ^ d - e` coordinates (matching the witness
  shape of `CslibFrontier/Foundations/Data/Code/ProximityGap/Curve.lean`), while
  `FRIParams.batchCorrAgreeLang` states real-density correlated agreement `α ≤ (#D' : ℝ) / 2 ^ d`
  (matching the correlated-agreement target of Theorem 8.3, p. 39). For `α ≤ 1`, the ceiling
  threshold `e = 2 ^ d - ⌈α * 2 ^ d⌉₊` yields exact set equality
  `batchCorrAgreeLang = batchProximityLang` (`batchCorrAgreeLang_eq_batchProximityLang`), with
  strict single-query ratio `< α` for `0 < α ≤ 1` (`batchCeilThreshold_bounds`); for `0 ≤ α < 1`,
  the floor threshold `B = ⌊α * 2 ^ d⌋₊`, `e = 2 ^ d - 1 - B` characterizes maximal
  correlated-agreement density `≤ α` with strict Johnson slack `(e : ℝ) / 2 ^ d < 1 - α` even when
  `α * 2 ^ d ∈ ℤ` (`batchFloorThreshold_bounds`).

## Main definitions

* `Cslib.Crypto.Protocols.FRI.FRIBatchStmt`, `Cslib.Crypto.Protocols.FRI.FRIBatchStmt.linear`,
  `Cslib.Crypto.Protocols.FRI.FRIBatchStmt.eval`: affine `(t + 1)`-word batch statement,
  homogeneous linear constructor, and affine combination evaluator.
* `Cslib.Crypto.Protocols.FRI.FRIBatchChal`, `Cslib.Crypto.Protocols.FRI.FRIBatchChal.toFRIChal`,
  `Cslib.Crypto.Protocols.FRI.friTailChals`: per-round public-coin challenge for batched FRI and
  challenge-tail projection to `FRIChal`.
* `Cslib.Crypto.Protocols.FRI.FRIParams.batchCompletenessRel`,
  `Cslib.Crypto.Protocols.FRI.FRIParams.batchProximityLang`,
  `Cslib.Crypto.Protocols.FRI.FRIParams.batchCorrAgreeLang`,
  `Cslib.Crypto.Protocols.FRI.FRIParams.batchInputWordReads`,
  `Cslib.Crypto.Protocols.FRI.FRIParams.batchTotalWordQueries`: batched completeness relation,
  integer and real-density tuple correlated-agreement languages, and direct-read / combined
  word-query budget abbreviations.
* `Cslib.Crypto.Protocols.FRI.friBatchQueries`, `Cslib.Crypto.Protocols.FRI.friBatchInputQueries`,
  `Cslib.Crypto.Protocols.FRI.friBatchDecide`, `Cslib.Crypto.Protocols.FRI.friBatchSingleAccepts`,
  `Cslib.Crypto.Protocols.FRI.friBatchIOP`: committed-oracle query list, scheduled input-word
  positions, verifier decision procedure, single-repetition acceptance predicate, and
  `(m + 2)`-round `PublicCoinIOP` instantiation of batched FRI.

## Main results

* `Cslib.Crypto.Protocols.FRI.card_friBatchChal`: exact challenge-space cardinality
  `|F| ^ (t + 1) * (2 ^ d) ^ q`.
* `Cslib.Crypto.Protocols.FRI.mem_batchProximityLang_zero_iff`,
  `Cslib.Crypto.Protocols.FRI.batchCorrAgreeLang_eq_batchProximityLang`,
  `Cslib.Crypto.Protocols.FRI.batchCeilThreshold_bounds`,
  `Cslib.Crypto.Protocols.FRI.batchFloorThreshold_bounds`: `t = 0` equivalence with single-word
  `proximityLang`, exact ceiling `Set` equality between `batchCorrAgreeLang` and
  `batchProximityLang`, and zero-loss ceiling/floor real-to-integer threshold bridges.
* `Cslib.Crypto.Protocols.FRI.round_ne_zero_of_mem_friBatchQueries`,
  `Cslib.Crypto.Protocols.FRI.length_friBatchIOP_queries`,
  `Cslib.Crypto.Protocols.FRI.friBatchDecide_congr_inputQueries`: round-`0` non-opening guarantee,
  exact committed-proof-oracle opening count `kFinal + q * (3 * m + 2)`, and input-query locality.
* `Cslib.Crypto.Protocols.FRI.iopVerify_friBatchIOP_eq_iopVerify_friIOP`,
  `Cslib.Crypto.Protocols.FRI.iopVerify_friBatchIOP_eq_true_iff`: exact verification reduction to
  `friIOP` and pointwise characterization via `friBatchSingleAccepts`.
* `Cslib.Crypto.Protocols.FRI.friBatchIOP_complete`,
  `Cslib.Crypto.Protocols.FRI.friBatchBCS_verify_prove_eq_true`,
  `Cslib.Crypto.Protocols.FRI.friBatchBCS_honestROMGame_eq_pure_true`,
  `Cslib.Crypto.Protocols.FRI.isCostBounded_bcsMTCost_friBatchVerifyROM`: perfect completeness of
  batched FRI as an IOP, under deterministic BCS, and in the two-channel BCS random-oracle model,
  together with the verifier Merkle hash query cost bound.

## References

* [E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf, *Proximity Gaps for Reed–Solomon
  Codes*][BenSassonCarmonIshaiKoppartySaraf2020]
* [E. Ben-Sasson, I. Bentov, Y. Horesh, M. Riabzev, *Fast Reed–Solomon Interactive Oracle Proofs
  of Proximity*][BenSassonBentovHoreshRiabzev2018]
* [E. Ben-Sasson, A. Chiesa, N. Spooner, *Interactive Oracle Proofs*][BenSassonChiesaSpooner2016]
-/

public section

namespace Cslib.Crypto.Protocols.FRI

open Finset Cslib.Code Cslib.Crypto.Protocols.BCS Cslib.OracleComp
open scoped BigOperators

section BatchStatementsAndChallenges

/-- `(t + 1)`-word affine batch statement `f₀⁽⁰⁾, f₁⁽⁰⁾, …, f_t⁽⁰⁾ : Fin (2 ^ d) → F` for batched
FRI ([BenSassonCarmonIshaiKoppartySaraf2020], Section 8.2, Eq. (8.3) on printed p. 37). -/
@[ext] structure FRIBatchStmt (F : Type) (d t : ℕ) where
  /-- Affine base word `f₀⁽⁰⁾` (set to `0` for homogeneous linear batching via
  `FRIBatchStmt.linear`). -/
  base : OracleTable d F
  /-- `t` generator words `f₁⁽⁰⁾, …, f_t⁽⁰⁾` combined with verifier scalars `x : Fin t → F`. -/
  terms : Fin t → OracleTable d F

namespace FRIBatchStmt

/-- Homogeneous linear batching statement (`f₀⁽⁰⁾ = 0`, [BenSassonCarmonIshaiKoppartySaraf2020],
Section 8.2, printed p. 37). -/
@[expose] def linear {F : Type} [Zero F] {d t : ℕ}
    (terms : Fin t → OracleTable d F) : FRIBatchStmt F d t :=
  ⟨0, terms⟩

/-- Affine combination word `f₀⁽⁰⁾ + ∑ j : Fin t, x j • f_{j+1}⁽⁰⁾` evaluated at batching challenge
`x : Fin t → F` ([BenSassonCarmonIshaiKoppartySaraf2020], Eq. (8.3)). -/
@[expose] def eval {F : Type} [Semiring F] {d t : ℕ}
    (stmt : FRIBatchStmt F d t) (x : Fin t → F) : OracleTable d F :=
  stmt.base + ∑ j : Fin t, x j • stmt.terms j

@[simp]
theorem eval_apply {F : Type} [Semiring F] {d t : ℕ}
    (stmt : FRIBatchStmt F d t) (x : Fin t → F) (s : Fin (2 ^ d)) :
    stmt.eval x s = stmt.base s + ∑ j : Fin t, x j * stmt.terms j s := by
  simp only [eval, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

@[simp]
theorem eval_linear {F : Type} [Semiring F] {d t : ℕ}
    (terms : Fin t → OracleTable d F) (x : Fin t → F) :
    (linear terms).eval x = ∑ j : Fin t, x j • terms j := by
  simp only [linear, eval, zero_add]

@[simp]
theorem eval_zero {F : Type} [Semiring F] {d : ℕ}
    (stmt : FRIBatchStmt F d 0) (x : Fin 0 → F) :
    stmt.eval x = stmt.base := by
  simp only [eval, Finset.univ_eq_empty, Finset.sum_empty, add_zero]

/-- Equivalence between `FRIBatchStmt F d t` and `OracleTable d F × (Fin t → OracleTable d F)`. -/
@[expose] def equivProd (F : Type) (d t : ℕ) :
    FRIBatchStmt F d t ≃ OracleTable d F × (Fin t → OracleTable d F) where
  toFun s := (s.base, s.terms)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance {F : Type} [DecidableEq F] {d t : ℕ} : DecidableEq (FRIBatchStmt F d t) :=
  (equivProd F d t).decidableEq

instance {F : Type} [Fintype F] {d t : ℕ} : Fintype (FRIBatchStmt F d t) :=
  Fintype.ofEquiv _ (equivProd F d t).symm

instance {F : Type} [Nonempty F] {d t : ℕ} : Nonempty (FRIBatchStmt F d t) :=
  ⟨let x := Classical.choice ‹Nonempty F›; ⟨fun _ => x, fun _ _ => x⟩⟩

end FRIBatchStmt

/-- Public-coin verifier challenge per round of `(params.m + 2)`-round `friBatchIOP`:
* `batchCoeffs : Fin t → F` is consumed in round `0` to form `stmt.eval batchCoeffs`,
* `foldScalar : F` is consumed in folding rounds `1, …, m`, and
* `queryIdxs : Fin q → Fin (2 ^ d)` is consumed in the final query round `m + 1`. -/
@[ext] structure FRIBatchChal (F : Type) (d q t : ℕ) where
  /-- Batching challenge scalars `(x₁, …, x_t) ∈ F^t` used in round `0`. -/
  batchCoeffs : Fin t → F
  /-- Folding challenge scalar `z⁽ⁱ⁾ ∈ F` used in folding rounds `1, …, m`. -/
  foldScalar : F
  /-- Batch of `q` query starting indices used in the final round `m + 1`. -/
  queryIdxs : Fin q → Fin (2 ^ d)

/-- Project a batched FRI challenge to the underlying single-word `FRIChal F d q`. -/
@[expose] def FRIBatchChal.toFRIChal {F : Type} {d q t : ℕ}
    (c : FRIBatchChal F d q t) : FRIChal F d q :=
  ⟨c.foldScalar, c.queryIdxs⟩

/-- Equivalence between `FRIBatchChal F d q t` and `(Fin t → F) × FRIChal F d q`, with first
projection `batchCoeffs` and second projection `toFRIChal` definitionally. -/
@[expose] def FRIBatchChal.equivProd (F : Type) (d q t : ℕ) :
    FRIBatchChal F d q t ≃ (Fin t → F) × FRIChal F d q where
  toFun c := (c.batchCoeffs, c.toFRIChal)
  invFun p := ⟨p.1, p.2.foldScalar, p.2.queryIdxs⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance {F : Type} [DecidableEq F] {d q t : ℕ} : DecidableEq (FRIBatchChal F d q t) :=
  (FRIBatchChal.equivProd F d q t).decidableEq

instance {F : Type} [Fintype F] {d q t : ℕ} : Fintype (FRIBatchChal F d q t) :=
  Fintype.ofEquiv _ (FRIBatchChal.equivProd F d q t).symm

instance {F : Type} [Nonempty F] {d q t : ℕ} : Nonempty (FRIBatchChal F d q t) :=
  ⟨let x := Classical.choice ‹Nonempty F›
   ⟨fun _ => x, x, fun _ => ⟨0, Nat.pow_pos (by omega)⟩⟩⟩

/-- Exact cardinality of `FRIBatchChal F d q t`: `|F| ^ (t + 1) * (2 ^ d) ^ q`. -/
theorem card_friBatchChal {F : Type} [Fintype F] (d q t : ℕ) :
    Fintype.card (FRIBatchChal F d q t) = Fintype.card F ^ (t + 1) * (2 ^ d) ^ q := by
  rw [Fintype.card_congr (FRIBatchChal.equivProd F d q t), Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, card_friChal]
  rw [pow_succ]
  ring

end BatchStatementsAndChallenges

section LanguagesAndThresholds

variable {F : Type} [Field F]

namespace FRIParams

/-- Honest completeness relation for batched FRI: both `stmt.base` and all `t` generator words
`stmt.terms j` belong to `params.initialCode`. -/
@[expose] def batchCompletenessRel (params : FRIParams F) (t : ℕ) :
    FRIBatchStmt F params.d t → Unit → Prop :=
  fun stmt _ => stmt.base ∈ params.initialCode ∧ ∀ j : Fin t, stmt.terms j ∈ params.initialCode

/-- Every affine combination `stmt.eval x` of an honest batch statement lies in
`params.initialCode`. -/
theorem eval_mem_initialCode (params : FRIParams F) {t : ℕ}
    {stmt : FRIBatchStmt F params.d t} (hrel : params.batchCompletenessRel t stmt ())
    (x : Fin t → F) :
    stmt.eval x ∈ params.initialCode :=
  params.initialCode.add_mem hrel.1
    (params.initialCode.sum_mem fun j _ => params.initialCode.smul_mem (x j) (hrel.2 j))

/-- Integer-threshold tuple correlated-agreement language for `(t + 1)`-word batched FRI:
`stmt.base` and all `t` words `stmt.terms j` simultaneously agree with codewords in
`params.initialCode` on a common subset `D' ⊆ Fin (2 ^ d)` of cardinality at least `2 ^ d - e`
(matching [BenSassonCarmonIshaiKoppartySaraf2020], Theorem 1.6 and Section 8.2). -/
@[expose] def batchProximityLang (params : FRIParams F) (t e : ℕ) :
    Set (FRIBatchStmt F params.d t) :=
  {stmt | ∃ D' : Finset (Fin (2 ^ params.d)), 2 ^ params.d - e ≤ D'.card ∧
    ∃ v₀ ∈ params.initialCode, ∃ v : Fin t → OracleTable params.d F,
      (∀ j, v j ∈ params.initialCode) ∧
      ∀ s ∈ D', stmt.base s = v₀ s ∧ ∀ j, stmt.terms j s = v j s}

/-- Real-density tuple correlated-agreement language for `(t + 1)`-word batched FRI: `stmt.base` and
all `t` words `stmt.terms j` simultaneously agree with codewords in `params.initialCode` on a common
domain `D' ⊆ Fin (2 ^ d)` of relative density `α ≤ (#D' : ℝ) / 2 ^ d`
([BenSassonCarmonIshaiKoppartySaraf2020], Theorem 8.3 on printed p. 39). -/
@[expose] def batchCorrAgreeLang (params : FRIParams F) (t : ℕ) (α : ℝ) :
    Set (FRIBatchStmt F params.d t) :=
  {stmt | ∃ D' : Finset (Fin (2 ^ params.d)),
    α ≤ (D'.card : ℝ) / (2 ^ params.d : ℝ) ∧
    ∃ v₀ ∈ params.initialCode, ∃ v : Fin t → OracleTable params.d F,
      (∀ j, v j ∈ params.initialCode) ∧
      ∀ s ∈ D', stmt.base s = v₀ s ∧ ∀ j, stmt.terms j s = v j s}

/-- Full direct-read schedule / input-symbol budget `(t + 1) * q` across `stmt.base` and
`stmt.terms 0, …, stmt.terms (t - 1)`: `friBatchInputQueries` schedules `q` positions, with `t + 1`
input symbols sufficient at each (`friBatchDecide_congr_inputQueries`). A call with a wrong-length
answer list or an unsuccessful earlier repetition can reject before inspecting later positions. -/
abbrev batchInputWordReads (params : FRIParams F) (t : ℕ) : ℕ :=
  (t + 1) * params.q

/-- Combined word-query budget `batchInputWordReads t + proofOracleQueries =
kFinal + q * (3 * m + t + 3)`, pairing the full `(t + 1) * q` direct-read schedule with the exact
committed-proof-oracle opening list length `proofOracleQueries`. -/
abbrev batchTotalWordQueries (params : FRIParams F) (t : ℕ) : ℕ :=
  params.batchInputWordReads t + params.proofOracleQueries

theorem batchTotalWordQueries_eq (params : FRIParams F) (t : ℕ) :
    params.batchTotalWordQueries t = params.kFinal + params.q * (3 * params.m + t + 3) := by
  simp only [batchTotalWordQueries, batchInputWordReads, proofOracleQueries]
  ring

/-- Any statement satisfying `batchCompletenessRel` belongs to `batchProximityLang t e` for every
`e : ℕ` (witnessed on `D' = Finset.univ`). -/
theorem mem_batchProximityLang_of_batchCompletenessRel (params : FRIParams F) {t : ℕ} (e : ℕ)
    {stmt : FRIBatchStmt F params.d t} (hrel : params.batchCompletenessRel t stmt ()) :
    stmt ∈ params.batchProximityLang t e := by
  refine ⟨Finset.univ, ?_, stmt.base, hrel.1, stmt.terms, hrel.2, fun _ _ => ⟨rfl, fun _ => rfl⟩⟩
  simp only [Finset.card_univ, Fintype.card_fin]
  exact Nat.sub_le _ _

/-- When `2 ^ params.d ≤ e`, `2 ^ params.d - e = 0`, so `D' = ∅` witnesses membership in
`batchProximityLang` for every statement; contrapositively, `stmt ∉ params.batchProximityLang t e`
implies `e < 2 ^ params.d` with no extra radius premise. -/
theorem lt_two_pow_of_not_mem_batchProximityLang (params : FRIParams F) {t e : ℕ}
    {stmt : FRIBatchStmt F params.d t} (hnot : stmt ∉ params.batchProximityLang t e) :
    e < 2 ^ params.d := by
  by_contra hge
  have hsub : 2 ^ params.d - e = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_lt hge)
  exact hnot ⟨∅, by simp [hsub], 0, params.initialCode.zero_mem, fun _ => 0,
    fun _ => params.initialCode.zero_mem, fun _ hs => False.elim (Finset.notMem_empty _ hs)⟩

end FRIParams

/-- At batch size `t = 0`, tuple correlated agreement `batchProximityLang 0 e` coincides with the
single-word `proximityLang e` on `stmt.base`. -/
theorem mem_batchProximityLang_zero_iff [DecidableEq F] (params : FRIParams F) (e : ℕ)
    (stmt : FRIBatchStmt F params.d 0) :
    stmt ∈ params.batchProximityLang 0 e ↔ stmt.base ∈ params.proximityLang e := by
  constructor
  · rintro ⟨D', hcard, v₀, hv₀, _, _, hagree⟩
    refine ⟨v₀, hv₀, ?_⟩
    have hsub : D' ⊆ Finset.univ.filter (fun s : Fin (2 ^ params.d) => stmt.base s = v₀ s) :=
      fun s hs => Finset.mem_filter.mpr ⟨Finset.mem_univ s, (hagree s hs).1⟩
    have hle := hcard.trans (Finset.card_le_card hsub)
    have htot := card_filter_eq_add_hammingDist stmt.base v₀
    rw [Fintype.card_fin] at htot
    omega
  · rintro ⟨c, hc, hdist⟩
    refine ⟨Finset.univ.filter (fun s => stmt.base s = c s), ?_, c, hc, Fin.elim0,
      fun j => Fin.elim0 j, fun s hs => ⟨(Finset.mem_filter.mp hs).2, fun j => Fin.elim0 j⟩⟩
    have htot := card_filter_eq_add_hammingDist stmt.base c
    rw [Fintype.card_fin] at htot
    have hdist' : hammingDist stmt.base c ≤ e := hdist
    omega

/-- **Exact ceiling `Set` equality (`α ≤ 1`)**: for `e = 2 ^ d - ⌈α * 2 ^ d⌉₊`, the real-density
language `params.batchCorrAgreeLang t α` equals `params.batchProximityLang t e` literally as a `Set`
(enabling direct `rw` substitution in `bcsSoundnessGame` and `bcsSoundnessProg`). -/
theorem batchCorrAgreeLang_eq_batchProximityLang (params : FRIParams F) (t : ℕ)
    {α : ℝ} (hα_le : α ≤ 1) :
    params.batchCorrAgreeLang t α =
      params.batchProximityLang t (2 ^ params.d - ⌈α * (2 ^ params.d : ℝ)⌉₊) := by
  set n : ℕ := 2 ^ params.d
  have hnR_pos : (0 : ℝ) < (n : ℝ) := by simp only [n, Nat.cast_pow, Nat.cast_ofNat]; positivity
  have hceil_le : ⌈α * (n : ℝ)⌉₊ ≤ n := by
    refine Nat.ceil_le.mpr ?_
    calc α * (n : ℝ) ≤ 1 * (n : ℝ) := mul_le_mul_of_nonneg_right hα_le hnR_pos.le
      _ = (n : ℝ) := one_mul _
  have hsub : n - (n - ⌈α * (n : ℝ)⌉₊) = ⌈α * (n : ℝ)⌉₊ := Nat.sub_sub_self hceil_le
  ext stmt
  simp only [FRIParams.batchCorrAgreeLang, FRIParams.batchProximityLang, Set.mem_ofPred_eq]
  refine exists_congr fun D' => and_congr_left fun _ => ?_
  have hdiv : α ≤ (D'.card : ℝ) / (n : ℝ) ↔ α * (n : ℝ) ≤ (D'.card : ℝ) := by
    rw [le_div_iff₀ hnR_pos]
  have hceil : α * (n : ℝ) ≤ (D'.card : ℝ) ↔ ⌈α * (n : ℝ)⌉₊ ≤ D'.card :=
    Nat.ceil_le.symm
  have hnR_eq : ((2 : ℝ) ^ params.d) = (n : ℝ) := by simp only [n, Nat.cast_pow, Nat.cast_ofNat]
  change α ≤ (D'.card : ℝ) / ((2 : ℝ) ^ params.d) ↔
    n - (n - ⌈α * ((2 : ℝ) ^ params.d)⌉₊) ≤ D'.card
  rw [hnR_eq, hsub, hdiv, hceil]

/-- **Ceiling threshold bounds (`0 < α ≤ 1`)**: with `e = 2 ^ d - ⌈α * 2 ^ d⌉₊`, `e < 2 ^ d`, the
single-query acceptance ratio `(2 ^ d - e - 1) / 2 ^ d` is strictly `< α`, and the relative error
radius `e / 2 ^ d` is at most `1 - α` with zero rounding loss. -/
theorem batchCeilThreshold_bounds (params : FRIParams F) {α : ℝ}
    (hα_pos : 0 < α) (hα_le : α ≤ 1) :
    let e := 2 ^ params.d - ⌈α * (2 ^ params.d : ℝ)⌉₊
    e < 2 ^ params.d ∧
      (((2 ^ params.d - e - 1 : ℕ) : ℝ) / (2 ^ params.d : ℝ)) < α ∧
      (e : ℝ) / (2 ^ params.d : ℝ) ≤ 1 - α := by
  set n : ℕ := 2 ^ params.d
  have hnR_pos : (0 : ℝ) < (n : ℝ) := by simp only [n, Nat.cast_pow, Nat.cast_ofNat]; positivity
  have hnR_eq : ((2 : ℝ) ^ params.d) = (n : ℝ) := by simp only [n, Nat.cast_pow, Nat.cast_ofNat]
  set C : ℕ := ⌈α * (n : ℝ)⌉₊
  have hαn_pos : 0 < α * (n : ℝ) := mul_pos hα_pos hnR_pos
  have hC_pos : 0 < C := Nat.ceil_pos.mpr hαn_pos
  have hC_le : C ≤ n := by
    refine Nat.ceil_le.mpr ?_
    calc α * (n : ℝ) ≤ 1 * (n : ℝ) := mul_le_mul_of_nonneg_right hα_le hnR_pos.le
      _ = (n : ℝ) := one_mul _
  dsimp only
  simp only [hnR_eq]
  change n - C < n ∧ (((n - (n - C) - 1 : ℕ) : ℝ) / (n : ℝ)) < α ∧
    ((n - C : ℕ) : ℝ) / (n : ℝ) ≤ 1 - α
  have hsub : n - (n - C) = C := Nat.sub_sub_self hC_le
  refine ⟨by omega, ?_, ?_⟩
  · rw [hsub, Nat.cast_sub hC_pos, Nat.cast_one, div_lt_iff₀ hnR_pos]
    have hlt := Nat.ceil_lt_add_one hαn_pos.le
    change (C : ℝ) < α * (n : ℝ) + 1 at hlt
    linarith
  · rw [Nat.cast_sub hC_le, div_le_iff₀ hnR_pos]
    have hge : α * (n : ℝ) ≤ (C : ℝ) := Nat.le_ceil _
    linarith

/-- **Floor threshold bounds (`0 ≤ α < 1`)** (real-to-integer threshold bridge toward
[BenSassonCarmonIshaiKoppartySaraf2020], Lemma 8.2 on printed pp. 38–39, Eq. (8.5); soundness
tracked in #5968): setting `B = ⌊α * 2 ^ d⌋₊` and `e = 2 ^ d - 1 - B` characterizes maximal
correlated-agreement density `≤ α` via `stmt ∉ params.batchProximityLang t e`, while satisfying
`(B : ℝ) / 2 ^ d ≤ α` and the **strict** radius inequality `(e : ℝ) / 2 ^ d < 1 - α` (even when
`α * 2 ^ d` is an integer). -/
theorem batchFloorThreshold_bounds (params : FRIParams F) (t : ℕ)
    (stmt : FRIBatchStmt F params.d t) {α : ℝ}
    (hα_nn : 0 ≤ α) (hα_lt : α < 1) :
    let B := ⌊α * (2 ^ params.d : ℝ)⌋₊
    let e := 2 ^ params.d - 1 - B
    ((∀ (D' : Finset (Fin (2 ^ params.d))) (v₀ : OracleTable params.d F),
        v₀ ∈ params.initialCode →
        ∀ v : Fin t → OracleTable params.d F,
          (∀ j, v j ∈ params.initialCode) →
          (∀ s ∈ D', stmt.base s = v₀ s ∧ ∀ j, stmt.terms j s = v j s) →
          (D'.card : ℝ) / (2 ^ params.d : ℝ) ≤ α) ↔
      stmt ∉ params.batchProximityLang t e) ∧
      B < 2 ^ params.d ∧
      2 ^ params.d - e - 1 = B ∧
      (B : ℝ) / (2 ^ params.d : ℝ) ≤ α ∧
      (e : ℝ) / (2 ^ params.d : ℝ) < 1 - α := by
  set n : ℕ := 2 ^ params.d
  have hnR_pos : (0 : ℝ) < (n : ℝ) := by simp only [n, Nat.cast_pow, Nat.cast_ofNat]; positivity
  have hnR_eq : ((2 : ℝ) ^ params.d) = (n : ℝ) := by simp only [n, Nat.cast_pow, Nat.cast_ofNat]
  have hαn_nn : 0 ≤ α * (n : ℝ) := mul_nonneg hα_nn hnR_pos.le
  have hαn_lt : α * (n : ℝ) < (n : ℝ) := by
    calc α * (n : ℝ) < 1 * (n : ℝ) := mul_lt_mul_of_pos_right hα_lt hnR_pos
      _ = (n : ℝ) := one_mul _
  set B : ℕ := ⌊α * (n : ℝ)⌋₊
  have hB_lt : B < n := (Nat.floor_lt hαn_nn).mpr hαn_lt
  set e : ℕ := n - 1 - B
  have hne : n - e = B + 1 := by omega
  have hne1 : n - e - 1 = B := by omega
  dsimp only
  simp only [hnR_eq]
  change ((∀ (D' : Finset (Fin n)) (v₀ : OracleTable params.d F),
        v₀ ∈ params.initialCode →
        ∀ v : Fin t → OracleTable params.d F,
          (∀ j, v j ∈ params.initialCode) →
          (∀ s ∈ D', stmt.base s = v₀ s ∧ ∀ j, stmt.terms j s = v j s) →
          (D'.card : ℝ) / (n : ℝ) ≤ α) ↔
      stmt ∉ params.batchProximityLang t e) ∧
      B < n ∧ n - e - 1 = B ∧ (B : ℝ) / (n : ℝ) ≤ α ∧ (e : ℝ) / (n : ℝ) < 1 - α
  have hcard_le_iff : ∀ D' : Finset (Fin n),
      (D'.card : ℝ) / (n : ℝ) ≤ α ↔ D'.card ≤ B := by
    intro D'
    rw [div_le_iff₀ hnR_pos, ← Nat.le_floor_iff hαn_nn]
  refine ⟨?_, hB_lt, hne1, ?_, ?_⟩
  · simp only [FRIParams.batchProximityLang, Set.mem_ofPred_eq]
    change (∀ (D' : Finset (Fin n)) (v₀ : OracleTable params.d F),
        v₀ ∈ params.initialCode →
        ∀ v : Fin t → OracleTable params.d F,
          (∀ j, v j ∈ params.initialCode) →
          (∀ s ∈ D', stmt.base s = v₀ s ∧ ∀ j, stmt.terms j s = v j s) →
          (D'.card : ℝ) / (n : ℝ) ≤ α) ↔
      ¬ ∃ D' : Finset (Fin n), n - e ≤ D'.card ∧
        ∃ v₀ ∈ params.initialCode, ∃ v : Fin t → OracleTable params.d F,
          (∀ j, v j ∈ params.initialCode) ∧
          ∀ s ∈ D', stmt.base s = v₀ s ∧ ∀ j, stmt.terms j s = v j s
    rw [hne]
    constructor
    · rintro hall ⟨D', hge, v₀, hv₀, v, hv, hagree⟩
      have hle := (hcard_le_iff D').mp (hall D' v₀ hv₀ v hv hagree)
      omega
    · intro hnot D' v₀ hv₀ v hv hagree
      rw [hcard_le_iff]
      by_contra hgt
      exact hnot ⟨D', by omega, v₀, hv₀, v, hv, hagree⟩
  · rw [div_le_iff₀ hnR_pos]
    exact Nat.floor_le hαn_nn
  · rw [div_lt_iff₀ hnR_pos]
    have hlt_succ : α * (n : ℝ) < (B : ℝ) + 1 := Nat.lt_floor_add_one (α * (n : ℝ))
    have he_cast : (e : ℝ) + ((B : ℝ) + 1) = (n : ℝ) := by
      exact_mod_cast (show e + (B + 1) = n by omega)
    linarith

end LanguagesAndThresholds

section BatchedFRIProtocol

variable {F : Type} [Field F]

/-- Project an `(r + 1)`-round batched challenge vector to its `r`-round single-word `FRIChal` tail
(rounds `1, …, r`). -/
@[expose] def friTailChals {d q t r : ℕ}
    (chals : Fin (r + 1) → FRIBatchChal F d q t) : Fin r → FRIChal F d q :=
  fun j => (chals j.succ).toFRIChal

/-- Committed-proof-oracle opening list of the batched FRI verifier: shifts every query `(j, idx)`
of `friQueries params (friTailChals chals)` to `(j.succ, idx)` in `Fin (params.m + 2)`. Round `0` is
never opened; all `params.proofOracleQueries = kFinal + q * (3 * m + 2)` openings target the
committed prover tables `f⁽⁰⁾, …, f⁽ᵐ⁾` in rounds `1, …, m + 1`. -/
@[expose] def friBatchQueries (params : FRIParams F) (t : ℕ)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t) :
    List (Fin (params.m + 2) × Fin (2 ^ params.d)) :=
  (friQueries params (friTailChals chals)).map fun (j, idx) => (j.succ, idx)

/-- No query in `friBatchQueries` ever opens the round-`0` announcement table. -/
theorem round_ne_zero_of_mem_friBatchQueries (params : FRIParams F) (t : ℕ)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t)
    {p : Fin (params.m + 2) × Fin (2 ^ params.d)} (hp : p ∈ friBatchQueries params t chals) :
    p.1 ≠ 0 := by
  rcases List.mem_map.mp hp with ⟨⟨j, _⟩, _, rfl⟩
  exact Fin.succ_ne_zero j

theorem length_friBatchQueries (params : FRIParams F) (t : ℕ)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t) :
    (friBatchQueries params t chals).length = params.proofOracleQueries := by
  simp only [friBatchQueries, List.length_map, length_friQueries]

/-- Schedule of `q` evaluation positions at which agreement of the `t + 1` input words
`(stmt.base, stmt.terms 0, …, stmt.terms (t - 1))` suffices to determine `friBatchDecide` outside
`PublicCoinIOP.queries`. -/
@[expose] def friBatchInputQueries (params : FRIParams F) (t : ℕ)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t) :
    List (Fin (2 ^ params.d)) :=
  friInputQueries params (friTailChals chals)

theorem length_friBatchInputQueries (params : FRIParams F) (t : ℕ)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t) :
    (friBatchInputQueries params t chals).length = params.q :=
  length_friInputQueries params (friTailChals chals)

/-- Batched FRI verifier decision procedure: delegates directly to `friDecide` on the affine
combination `stmt.eval (chals 0).batchCoeffs` and challenge tail `friTailChals chals`. -/
@[expose] def friBatchDecide [DecidableEq F] (params : FRIParams F) (t : ℕ)
    (stmt : FRIBatchStmt F params.d t)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t) (answers : List F) : Bool :=
  friDecide params (stmt.eval (chals 0).batchCoeffs) (friTailChals chals) answers

/-- Input-query locality: agreement of `(stmt.base, stmt.terms)` at the `q` scheduled positions in
`friBatchInputQueries params t chals` (full direct-read budget `(t + 1) * q =
params.batchInputWordReads t`) guarantees the same decision in `friBatchDecide`. -/
theorem friBatchDecide_congr_inputQueries [DecidableEq F] (params : FRIParams F) (t : ℕ)
    {stmt₁ stmt₂ : FRIBatchStmt F params.d t}
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t)
    (hagree : ∀ s ∈ friBatchInputQueries params t chals,
      stmt₁.base s = stmt₂.base s ∧ ∀ j : Fin t, stmt₁.terms j s = stmt₂.terms j s)
    (answers : List F) :
    friBatchDecide params t stmt₁ chals answers = friBatchDecide params t stmt₂ chals answers := by
  refine friDecide_congr_inputQueries params (friTailChals chals) (fun s hs => ?_) answers
  obtain ⟨hbase, hterms⟩ := hagree s hs
  simp only [FRIBatchStmt.eval_apply, hbase]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [hterms j]

/-- **Batched multi-round 2-to-1 FRI as a `(params.m + 2)`-round `PublicCoinIOP`**
([BenSassonCarmonIshaiKoppartySaraf2020], Section 8.2, printed pp. 37–38):
* Round `0` commits the zero announcement table (`0` openings in `queries`) and samples the random
  batching vector `(chals 0).batchCoeffs : Fin t → F`.
* Rounds `1, …, m + 1` run `friIOP params` on `stmt.eval (chals 0).batchCoeffs`, issuing an exact
  list of `params.proofOracleQueries = kFinal + q * (3 * m + 2)` committed-oracle openings via
  `queries`, with direct input access scheduled at the `q` positions of `friBatchInputQueries`
  (budget `params.batchInputWordReads t = (t + 1) * q`). -/
@[expose] def friBatchIOP [DecidableEq F] (params : FRIParams F) (t : ℕ) :
    PublicCoinIOP (params.m + 2) params.d (FRIBatchStmt F params.d t) Unit F
      (FRIBatchChal F params.d params.q t) where
  proveRound := Fin.cases
    (fun _ _ _ => fun _ => 0)
    (fun j stmt _ prev =>
      (friIOP params).proveRound j
        (stmt.eval (prev ⟨0, Nat.zero_lt_succ j.val⟩).batchCoeffs) ()
        (fun i => (prev i.succ).toFRIChal))
  queries _ chals := friBatchQueries params t chals
  decide stmt chals answers := friBatchDecide params t stmt chals answers

/-- Exact committed-proof-oracle opening count of `friBatchIOP`:
`params.proofOracleQueries = kFinal + q * (3 * m + 2)` for every statement and challenge vector. -/
theorem length_friBatchIOP_queries [DecidableEq F] (params : FRIParams F) (t : ℕ)
    (stmt : FRIBatchStmt F params.d t)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t) :
    ((friBatchIOP params t).queries stmt chals).length = params.proofOracleQueries :=
  length_friBatchQueries params t chals

@[simp]
theorem iopProverOracles_friBatchIOP_zero [DecidableEq F] (params : FRIParams F) (t : ℕ)
    (stmt : FRIBatchStmt F params.d t)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t) :
    iopProverOracles (friBatchIOP params t) stmt () chals 0 = fun _ => 0 := by
  simp only [iopProverOracles, friBatchIOP, Fin.cases_zero]

@[simp]
theorem iopProverOracles_friBatchIOP_succ [DecidableEq F] (params : FRIParams F) (t : ℕ)
    (stmt : FRIBatchStmt F params.d t)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t)
    (j : Fin (params.m + 1)) :
    iopProverOracles (friBatchIOP params t) stmt () chals j.succ =
      iopProverOracles (friIOP params) (stmt.eval (chals 0).batchCoeffs) ()
        (friTailChals chals) j := by
  simp only [iopProverOracles, friBatchIOP, Fin.cases_succ, prefixChallenges]
  rfl

/-- **Exact verification reduction from `friBatchIOP` to single-word `friIOP`**:
evaluating `iopVerify (friBatchIOP params t)` on `(stmt, chals, oracles)` is identical to evaluating
`iopVerify (friIOP params)` on the affine combination `stmt.eval (chals 0).batchCoeffs`, challenge
tail `friTailChals chals`, and shifted oracle tables `fun j => oracles j.succ`. -/
theorem iopVerify_friBatchIOP_eq_iopVerify_friIOP [DecidableEq F] (params : FRIParams F) (t : ℕ)
    (stmt : FRIBatchStmt F params.d t)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t)
    (oracles : Fin (params.m + 2) → OracleTable params.d F) :
    iopVerify (friBatchIOP params t) stmt chals oracles =
      iopVerify (friIOP params) (stmt.eval (chals 0).batchCoeffs)
        (friTailChals chals) (fun j => oracles j.succ) := by
  simp only [iopVerify, iopAnswers, friBatchIOP, friBatchQueries, friBatchDecide, List.map_map]
  rfl

/-- Pointwise acceptance predicate for a single batched FRI query repetition starting at
`s : Fin (2 ^ d)` ([BenSassonCarmonIshaiKoppartySaraf2020], Section 8.2, printed p. 38, steps
(2)–(4)), expressed directly via `friSingleAccepts` on the evaluated batch
`stmt.eval (chals 0).batchCoeffs`, challenge tail `friTailChals chals`, and shifted oracle family
`fun j => oracles j.succ`. -/
@[expose] def friBatchSingleAccepts (params : FRIParams F) (t : ℕ)
    (stmt : FRIBatchStmt F params.d t)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t)
    (oracles : Fin (params.m + 2) → OracleTable params.d F) (s : Fin (2 ^ params.d)) : Prop :=
  friSingleAccepts params (stmt.eval (chals 0).batchCoeffs) (friTailChals chals)
    (fun j => oracles j.succ) s

/-- **Exact characterization of batched FRI IOP verification**: `iopVerify (friBatchIOP params t)`
accepts `oracles` on `(stmt, chals)` if and only if every queried starting position
`(chals (Fin.last (m + 1))).queryIdxs a` satisfies `friBatchSingleAccepts`. -/
theorem iopVerify_friBatchIOP_eq_true_iff [DecidableEq F] (params : FRIParams F) (t : ℕ)
    (stmt : FRIBatchStmt F params.d t)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t)
    (oracles : Fin (params.m + 2) → OracleTable params.d F) :
    iopVerify (friBatchIOP params t) stmt chals oracles = true ↔
      ∀ a : Fin params.q,
        friBatchSingleAccepts params t stmt chals oracles
          ((chals (Fin.last (params.m + 1))).queryIdxs a) := by
  rw [iopVerify_friBatchIOP_eq_iopVerify_friIOP, iopVerify_friIOP_eq_true_iff,
    ← Fin.succ_last params.m]
  rfl

/-- **Perfect completeness of the batched FRI IOP**: whenever `stmt.base` and all `t` words
`stmt.terms j` belong to `params.initialCode`, the batched FRI verifier accepts the honest prover's
oracle tables for every challenge vector `chals`. -/
theorem friBatchIOP_complete [DecidableEq F] (params : FRIParams F) (t : ℕ) :
    IOPCompleteness (friBatchIOP params t) (params.batchCompletenessRel t) := by
  intro stmt _ hrel chals
  rw [iopVerify_friBatchIOP_eq_iopVerify_friIOP]
  have horacles :
      (fun j : Fin (params.m + 1) =>
        iopProverOracles (friBatchIOP params t) stmt () chals j.succ) =
      iopProverOracles (friIOP params) (stmt.eval (chals 0).batchCoeffs) ()
        (friTailChals chals) := by
    funext j
    exact iopProverOracles_friBatchIOP_succ params t stmt chals j
  rw [horacles]
  exact friIOP_complete params (stmt.eval (chals 0).batchCoeffs) ()
    (params.eval_mem_initialCode hrel (chals 0).batchCoeffs) (friTailChals chals)

/-- **Perfect deterministic BCS completeness for batched FRI**: for any hash function `H k` whose
digests all have one length, any Fiat–Shamir function `hFS`, and any symbol encoding `encSym`,
`bcsVerify` accepts `bcsProve` on every honest tuple satisfying `params.batchCompletenessRel t`. -/
theorem friBatchBCS_verify_prove_eq_true [DecidableEq F] (params : FRIParams F) (t : ℕ)
    (H : List Bool → List Bool → List Bool) (k : List Bool) {ℓ : ℕ}
    (hlen : ∀ y, (H k y).length = ℓ) (encSym : F → List Bool)
    (hFS : FRIBatchStmt F params.d t → List (List Bool) →
      FRIBatchChal F params.d params.q t)
    {stmt : FRIBatchStmt F params.d t} (hrel : params.batchCompletenessRel t stmt ()) :
    bcsVerify (friBatchIOP params t) H k encSym hFS stmt
      (bcsProve (friBatchIOP params t) H k encSym hFS stmt ()) = true :=
  bcsVerify_bcsProve_eq_true (friBatchIOP_complete params t) H k hlen encSym hFS hrel

/-- **Perfect BCS ROM completeness for batched FRI**: in the lazy two-channel random-oracle model
with any digest length `σ`, the honest BCS-compiled batched FRI game outputs `PMF.pure true` for
every tuple satisfying `params.batchCompletenessRel t`. -/
theorem friBatchBCS_honestROMGame_eq_pure_true [DecidableEq F] [Fintype F]
    (params : FRIParams F) (t : ℕ) (encSym : F → List Bool)
    {stmt : FRIBatchStmt F params.d t} (hrel : params.batchCompletenessRel t stmt ()) (σ : ℕ) :
    bcsHonestROMGame (friBatchIOP params t) encSym stmt () σ = PMF.pure true :=
  bcsHonestROMGame_eq_pure_true (friBatchIOP_complete params t) encSym hrel σ

/-- **Succinct verifier Merkle query cost bound for BCS-compiled batched FRI**: for any proof `prf`
whose opening paths have length at most `L_path`, `bcsVerifyROM` makes at most
`params.proofOracleQueries * (L_path + 1) = (kFinal + q * (3 * m + 2)) * (L_path + 1)` Merkle hash
queries (independent of batch size `t`, since direct access to `stmt` along the `(t + 1) * q` input
schedule is not Merkle-authenticated through `PublicCoinIOP.queries`). -/
theorem isCostBounded_bcsMTCost_friBatchVerifyROM [DecidableEq F] (params : FRIParams F) (t : ℕ)
    (encSym : F → List Bool) (stmt : FRIBatchStmt F params.d t)
    (prf : BCSProof (params.m + 2) F) {L_path : ℕ}
    (hops : ∀ op ∈ prf.openings, op.path.length ≤ L_path) :
    IsCostBounded bcsMTCost (bcsVerifyROM (friBatchIOP params t) encSym stmt prf)
      (params.proofOracleQueries * (L_path + 1)) :=
  isCostBounded_bcsMTCost_bcsVerifyROM_of_queries_le (friBatchIOP params t) encSym stmt prf
    (fun chals => (length_friBatchIOP_queries params t stmt chals).le) hops

end BatchedFRIProtocol

end Cslib.Crypto.Protocols.FRI
