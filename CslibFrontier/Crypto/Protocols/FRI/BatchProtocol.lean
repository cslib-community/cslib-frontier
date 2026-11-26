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
# Batched Multi-Round Smooth and 2-to-1 FRI as a Public-Coin Interactive Oracle Proof

This module instantiates the batched Fast Reed–Solomon Interactive Oracle Proof of Proximity (FRI)
of [BenSassonCarmonIshaiKoppartySaraf2020] (accepted *Journal of the ACM* 2023 manuscript, Section
8.2, printed pp. 36–38: affine batching Eq. (8.3) on p. 37 and batched QUERY steps (1)–(4) on
p. 38) for arbitrary per-round strict 2-smooth folding schedules `l⁽ⁱ⁾ = 2 ^ stepLog i ≥ 2`
(`FRISmoothParams`, `friSmoothBatchIOP`) together with the fixed 2-to-1 specialization (`FRIParams`,
`friBatchIOP`) directly as a `(params.m + 2)`-round `Cslib.Crypto.Protocols.BCS.PublicCoinIOP`
delegating its folding and query phases to `friSmoothIOP` / `friIOP`
([BenSassonBentovHoreshRiabzev2018]; [BenSassonChiesaSpooner2016]), proves perfect IOP / BCS /
random-oracle completeness together with exact committed-opening counts and direct-read schedule
locality, and defines the tuple correlated-agreement languages and real-to-integer threshold
bridges used in the setting of Lemma 8.2 and Theorem 8.3 (printed pp. 38–39).

## Protocol layout and causal delegation

Given `params : FRISmoothParams F` (or `params : FRIParams F`, embedded via `FRIParams.toSmooth`
with `friBatchIOP_eq_friSmoothBatchIOP`), batch size `t : ℕ`, and an affine batch statement
`stmt : FRIBatchStmt F params.d t` representing `(t + 1)` initial words
`f₀⁽⁰⁾ = stmt.base` and `f₁⁽⁰⁾, …, f_t⁽⁰⁾ = stmt.terms` on the coset of size `2 ^ d` (with
homogeneous linear batching `f₀⁽⁰⁾ = 0` given by `FRIBatchStmt.linear`):

* **Causal `(m + 2)`-round schedule.** In `PublicCoinIOP`, `proveRound 0` executes prior to
  sampling `chals 0`, whereas the honest batched oracle
  `stmt.eval x = stmt.base + ∑ j : Fin t, x j • stmt.terms j` (Eq. (8.3), p. 37) depends on the
  verifier's random batching vector `x : Fin t → F` and must be committed before the first folding
  scalar `z⁽⁰⁾`. Accordingly, `friSmoothBatchIOP params t` runs for `params.m + 2` rounds over
  `FRIBatchChal F params.d params.q t`:
  - **Round `0`:** the honest prover outputs the zero announcement table (`0` openings in
    `PublicCoinIOP.queries`), and the verifier samples `(chals 0).batchCoeffs : Fin t → F`.
  - **Rounds `1, …, m + 1`:** the protocol delegates `proveRound`, `queries` (shifted by
    `Fin.succ`), and `decide` directly to `friSmoothIOP params` evaluated on the combined word
    `stmt.eval (chals 0).batchCoeffs` and challenge tail `friTailChals chals`.
* **Batched query check, committed-opening count, and direct-read schedule.** By
  `iopVerify_friSmoothBatchIOP_eq_iopVerify_friSmoothIOP` and
  `iopVerify_friSmoothBatchIOP_eq_true_iff`, `friSmoothBatchSingleAccepts` delegates directly to
  `friSmoothSingleAccepts` on the evaluated batch `stmt.eval (chals 0).batchCoeffs`, challenge tail
  `friTailChals chals`, and shifted oracle family `fun j => oracles j.succ` (checking the round-`1`
  batching equation, all `m` `l⁽ⁱ⁾`-to-1 folding steps, and final codeword consistency; Section
  8.2, p. 38, steps (2)–(4)). The committed-proof-oracle opening list exposed via
  `PublicCoinIOP.queries` has **exact** length
  `params.proofOracleQueries = kFinal + q * (aritySum + m + 2)` (specializing to
  `kFinal + q * (3 * m + 2)` for binary folding, with zero openings against round `0`). Outside
  `PublicCoinIOP.queries`, `friSmoothBatchInputQueries` lists `q` scheduled input positions, with
  multiplicity, at which `t + 1` input symbols suffice (`friSmoothBatchDecide_congr_inputQueries`
  proves that agreement at these scheduled positions determines `friSmoothBatchDecide`). Because
  `friSmoothBatchDecide` can reject on an unexpected answer-list length before accessing `stmt`,
  repetitions short-circuit on earlier failures, and query challenges may repeat indices,
  `params.batchInputWordReads t = (t + 1) * q` records the full direct-read schedule / budget,
  giving the combined word-query budget
  `params.batchTotalWordQueries t = kFinal + q * (aritySum + m + t + 3)`.
* **Tuple correlated-agreement languages and real-to-integer threshold bridges.**
  The shared code-parameterized definitions `friBatchCompletenessRel`, `friBatchProximityLang`, and
  `friBatchCorrAgreeLang` (instantiated at `params.initialCode` for both `FRISmoothParams` and
  `FRIParams`) express honest tuple membership, simultaneous correlated agreement of
  `(stmt.base, stmt.terms)` on at least `2 ^ d - e` coordinates (matching
  `CslibFrontier/Foundations/Data/Code/ProximityGap/Curve.lean`), and real-density correlated
  agreement `α ≤ (#D' : ℝ) / 2 ^ d` (matching Theorem 8.3, p. 39). One shared set of threshold
  bridges covers both smooth and binary parameters: for `α ≤ 1`, the ceiling threshold
  `e = 2 ^ d - ⌈α * 2 ^ d⌉₊` yields exact set equality `friBatchCorrAgreeLang_eq_proximityLang`,
  with strict single-query ratio `< α` for `0 < α ≤ 1` (`friBatchCeilThreshold_bounds`); for
  `0 ≤ α < 1`, the floor threshold `B = ⌊α * 2 ^ d⌋₊`, `e = 2 ^ d - 1 - B` characterizes maximal
  correlated-agreement density `≤ α` with strict Johnson slack `(e : ℝ) / 2 ^ d < 1 - α` even when
  `α * 2 ^ d ∈ ℤ` (`friBatchFloorThreshold_bounds`).

## Main definitions

* `Cslib.Crypto.Protocols.FRI.FRIBatchStmt`, `Cslib.Crypto.Protocols.FRI.FRIBatchStmt.linear`,
  `Cslib.Crypto.Protocols.FRI.FRIBatchStmt.eval`: affine `(t + 1)`-word batch statement,
  homogeneous linear constructor, and affine combination evaluator.
* `Cslib.Crypto.Protocols.FRI.FRIBatchChal`, `Cslib.Crypto.Protocols.FRI.FRIBatchChal.toFRIChal`,
  `Cslib.Crypto.Protocols.FRI.friTailChals`: per-round public-coin challenge for batched FRI and
  challenge-tail projection to `FRIChal`.
* `Cslib.Crypto.Protocols.FRI.friBatchCompletenessRel`,
  `Cslib.Crypto.Protocols.FRI.friBatchProximityLang`,
  `Cslib.Crypto.Protocols.FRI.friBatchCorrAgreeLang`,
  `Cslib.Crypto.Protocols.FRI.FRISmoothParams.batchCompletenessRel`,
  `Cslib.Crypto.Protocols.FRI.FRISmoothParams.batchProximityLang`,
  `Cslib.Crypto.Protocols.FRI.FRISmoothParams.batchCorrAgreeLang`,
  `Cslib.Crypto.Protocols.FRI.FRISmoothParams.batchInputWordReads`,
  `Cslib.Crypto.Protocols.FRI.FRISmoothParams.batchTotalWordQueries`,
  `Cslib.Crypto.Protocols.FRI.FRIParams.batchCompletenessRel`,
  `Cslib.Crypto.Protocols.FRI.FRIParams.batchProximityLang`,
  `Cslib.Crypto.Protocols.FRI.FRIParams.batchCorrAgreeLang`,
  `Cslib.Crypto.Protocols.FRI.FRIParams.batchInputWordReads`,
  `Cslib.Crypto.Protocols.FRI.FRIParams.batchTotalWordQueries`: shared code-parameterized batched
  completeness relation and integer / real-density tuple correlated-agreement languages, together
  with smooth and binary parameter specializations and direct-read / combined word-query budget
  abbreviations.
* `Cslib.Crypto.Protocols.FRI.friSmoothBatchQueries`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchInputQueries`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchDecide`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchSingleAccepts`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchIOP`,
  `Cslib.Crypto.Protocols.FRI.friBatchQueries`, `Cslib.Crypto.Protocols.FRI.friBatchInputQueries`,
  `Cslib.Crypto.Protocols.FRI.friBatchDecide`, `Cslib.Crypto.Protocols.FRI.friBatchSingleAccepts`,
  `Cslib.Crypto.Protocols.FRI.friBatchIOP`: committed-oracle query lists, scheduled input-word
  positions, verifier decision procedures, single-repetition acceptance predicates, and
  `(m + 2)`-round `PublicCoinIOP` instantiations of smooth and binary batched FRI.

## Main results

* `Cslib.Crypto.Protocols.FRI.card_friBatchChal`: exact challenge-space cardinality
  `|F| ^ (t + 1) * (2 ^ d) ^ q`.
* `Cslib.Crypto.Protocols.FRI.eval_mem_of_friBatchCompletenessRel`,
  `Cslib.Crypto.Protocols.FRI.mem_friBatchProximityLang_of_completenessRel`,
  `Cslib.Crypto.Protocols.FRI.lt_two_pow_of_not_mem_friBatchProximityLang`,
  `Cslib.Crypto.Protocols.FRI.mem_friBatchProximityLang_zero_iff`,
  `Cslib.Crypto.Protocols.FRI.friBatchCorrAgreeLang_eq_proximityLang`,
  `Cslib.Crypto.Protocols.FRI.friBatchCeilThreshold_bounds`,
  `Cslib.Crypto.Protocols.FRI.friBatchFloorThreshold_bounds`,
  `Cslib.Crypto.Protocols.FRI.mem_batchProximityLang_zero_iff`,
  `Cslib.Crypto.Protocols.FRI.batchCorrAgreeLang_eq_batchProximityLang`,
  `Cslib.Crypto.Protocols.FRI.batchCeilThreshold_bounds`,
  `Cslib.Crypto.Protocols.FRI.batchFloorThreshold_bounds`: shared code-parameterized completeness,
  `t = 0` single-word equivalence, exact ceiling `Set` equality, and zero-loss ceiling/floor
  real-to-integer threshold bridges (together with binary `FRIParams` specializations).
* `Cslib.Crypto.Protocols.FRI.friBatchIOP_eq_friSmoothBatchIOP`: exact equality between binary
  `friBatchIOP` and `friSmoothBatchIOP params.toSmooth`.
* `Cslib.Crypto.Protocols.FRI.round_ne_zero_of_mem_friSmoothBatchQueries`,
  `Cslib.Crypto.Protocols.FRI.length_friSmoothBatchIOP_queries`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchDecide_congr_inputQueries`,
  `Cslib.Crypto.Protocols.FRI.round_ne_zero_of_mem_friBatchQueries`,
  `Cslib.Crypto.Protocols.FRI.length_friBatchIOP_queries`,
  `Cslib.Crypto.Protocols.FRI.friBatchDecide_congr_inputQueries`: round-`0` non-opening guarantees,
  exact committed-proof-oracle opening counts, and input-query locality.
* `Cslib.Crypto.Protocols.FRI.iopVerify_friSmoothBatchIOP_eq_iopVerify_friSmoothIOP`,
  `Cslib.Crypto.Protocols.FRI.iopVerify_friSmoothBatchIOP_eq_true_iff`,
  `Cslib.Crypto.Protocols.FRI.iopVerify_friBatchIOP_eq_iopVerify_friIOP`,
  `Cslib.Crypto.Protocols.FRI.iopVerify_friBatchIOP_eq_true_iff`: exact verification reductions to
  single-word FRI and pointwise characterizations.
* `Cslib.Crypto.Protocols.FRI.friSmoothBatchIOP_complete`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchBCS_verify_prove_eq_true`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchBCS_honestROMGame_eq_pure_true`,
  `Cslib.Crypto.Protocols.FRI.isCostBounded_bcsMTCost_friSmoothBatchVerifyROM`,
  `Cslib.Crypto.Protocols.FRI.friBatchIOP_complete`,
  `Cslib.Crypto.Protocols.FRI.friBatchBCS_verify_prove_eq_true`,
  `Cslib.Crypto.Protocols.FRI.friBatchBCS_honestROMGame_eq_pure_true`,
  `Cslib.Crypto.Protocols.FRI.isCostBounded_bcsMTCost_friBatchVerifyROM`: perfect completeness of
  smooth and binary batched FRI as IOPs, under deterministic BCS, and in the two-channel BCS
  random-oracle model, together with verifier Merkle hash query cost bounds.

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
    Fintype.card_fin, card_friChal, pow_succ]
  ring

end BatchStatementsAndChallenges

section LanguagesAndThresholds

variable {F : Type} [Field F]

/-- Honest completeness relation for batched FRI relative to an initial linear code
`C : Submodule F (OracleTable d F)`: both `stmt.base` and all `t` generator words `stmt.terms j`
belong to `C`. -/
abbrev friBatchCompletenessRel {d : ℕ} (C : Submodule F (OracleTable d F)) (t : ℕ) :
    FRIBatchStmt F d t → Unit → Prop :=
  fun stmt _ => stmt.base ∈ C ∧ ∀ j : Fin t, stmt.terms j ∈ C

/-- Every affine combination `stmt.eval x` of an honest batch statement lies in `C`. -/
theorem eval_mem_of_friBatchCompletenessRel {d t : ℕ} {C : Submodule F (OracleTable d F)}
    {stmt : FRIBatchStmt F d t} (hrel : friBatchCompletenessRel C t stmt ()) (x : Fin t → F) :
    stmt.eval x ∈ C :=
  C.add_mem hrel.1 (C.sum_mem fun j _ => C.smul_mem (x j) (hrel.2 j))

/-- Integer-threshold tuple correlated-agreement language for `(t + 1)`-word batched FRI relative to
an initial linear code `C`: `stmt.base` and all `t` words `stmt.terms j` simultaneously agree with
codewords in `C` on a common subset `D' ⊆ Fin (2 ^ d)` of cardinality at least `2 ^ d - e`
([BenSassonCarmonIshaiKoppartySaraf2020], Theorem 1.6 and Section 8.2). -/
abbrev friBatchProximityLang {d : ℕ} (C : Submodule F (OracleTable d F)) (t e : ℕ) :
    Set (FRIBatchStmt F d t) :=
  {stmt | ∃ D' : Finset (Fin (2 ^ d)), 2 ^ d - e ≤ D'.card ∧
    ∃ v₀ ∈ C, ∃ v : Fin t → OracleTable d F,
      (∀ j, v j ∈ C) ∧
      ∀ s ∈ D', stmt.base s = v₀ s ∧ ∀ j, stmt.terms j s = v j s}

/-- Real-density tuple correlated-agreement language for `(t + 1)`-word batched FRI relative to an
initial linear code `C`: `stmt.base` and all `t` words `stmt.terms j` simultaneously agree with
codewords in `C` on a common domain `D' ⊆ Fin (2 ^ d)` of relative density
`α ≤ (#D' : ℝ) / 2 ^ d` ([BenSassonCarmonIshaiKoppartySaraf2020], Theorem 8.3 on printed p. 39). -/
abbrev friBatchCorrAgreeLang {d : ℕ} (C : Submodule F (OracleTable d F)) (t : ℕ) (α : ℝ) :
    Set (FRIBatchStmt F d t) :=
  {stmt | ∃ D' : Finset (Fin (2 ^ d)),
    α ≤ (D'.card : ℝ) / (2 ^ d : ℝ) ∧
    ∃ v₀ ∈ C, ∃ v : Fin t → OracleTable d F,
      (∀ j, v j ∈ C) ∧
      ∀ s ∈ D', stmt.base s = v₀ s ∧ ∀ j, stmt.terms j s = v j s}

/-- Any statement satisfying `friBatchCompletenessRel C t` belongs to `friBatchProximityLang C t e`
for every `e : ℕ` (witnessed on `D' = Finset.univ`). -/
theorem mem_friBatchProximityLang_of_completenessRel {d t : ℕ} {C : Submodule F (OracleTable d F)}
    (e : ℕ) {stmt : FRIBatchStmt F d t} (hrel : friBatchCompletenessRel C t stmt ()) :
    stmt ∈ friBatchProximityLang C t e := by
  refine ⟨Finset.univ, ?_, stmt.base, hrel.1, stmt.terms, hrel.2, fun _ _ => ⟨rfl, fun _ => rfl⟩⟩
  simp

/-- Contrapositively, `stmt ∉ friBatchProximityLang C t e` implies `e < 2 ^ d`. -/
theorem lt_two_pow_of_not_mem_friBatchProximityLang {d t e : ℕ} {C : Submodule F (OracleTable d F)}
    {stmt : FRIBatchStmt F d t} (hnot : stmt ∉ friBatchProximityLang C t e) :
    e < 2 ^ d := by
  by_contra hge
  exact hnot ⟨∅, by simp [Nat.sub_eq_zero_of_le (Nat.le_of_not_lt hge)], 0, C.zero_mem,
    fun _ => 0, fun _ => C.zero_mem, fun _ hs => (Finset.notMem_empty _ hs).elim⟩

/-- At batch size `t = 0`, tuple correlated agreement `friBatchProximityLang C 0 e` coincides with
single-word Hamming proximity `∃ c ∈ C, hammingDist stmt.base c ≤ e`. -/
theorem mem_friBatchProximityLang_zero_iff [DecidableEq F] {d : ℕ}
    (C : Submodule F (OracleTable d F)) (e : ℕ) (stmt : FRIBatchStmt F d 0) :
    stmt ∈ friBatchProximityLang C 0 e ↔ ∃ c ∈ C, hammingDist stmt.base c ≤ e := by
  have htot (c : OracleTable d F) :
      #(univ.filter fun s => stmt.base s = c s) + hammingDist stmt.base c = 2 ^ d :=
    (card_filter_eq_add_hammingDist stmt.base c).trans (Fintype.card_fin _)
  constructor
  · rintro ⟨D', hcard, v₀, hv₀, _, _, hagree⟩
    have hle := hcard.trans (card_le_card fun s hs => mem_filter.mpr ⟨mem_univ s, (hagree s hs).1⟩)
    have := htot v₀
    exact ⟨v₀, hv₀, by omega⟩
  · rintro ⟨c, hc, hdist⟩
    have := htot c
    exact ⟨univ.filter fun s => stmt.base s = c s, by omega, c, hc, Fin.elim0, fun j => j.elim0,
      fun s hs => ⟨(mem_filter.mp hs).2, fun j => j.elim0⟩⟩

/-- **Exact ceiling `Set` equality (`α ≤ 1`)**: for `e = 2 ^ d - ⌈α * 2 ^ d⌉₊`,
`friBatchCorrAgreeLang C t α = friBatchProximityLang C t e`. -/
theorem friBatchCorrAgreeLang_eq_proximityLang {d : ℕ} (C : Submodule F (OracleTable d F)) (t : ℕ)
    {α : ℝ} (hα_le : α ≤ 1) :
    friBatchCorrAgreeLang C t α =
      friBatchProximityLang C t (2 ^ d - ⌈α * (2 ^ d : ℝ)⌉₊) := by
  have hnR_pos : (0 : ℝ) < (2 ^ d : ℝ) := by positivity
  have hceil_le : ⌈α * (2 ^ d : ℝ)⌉₊ ≤ 2 ^ d :=
    Nat.ceil_le.mpr (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      mul_le_of_le_one_left hnR_pos.le hα_le)
  ext stmt
  simp only [friBatchCorrAgreeLang, friBatchProximityLang, Set.mem_ofPred_eq,
    Nat.sub_sub_self hceil_le]
  refine exists_congr fun D' => and_congr_left fun _ => ?_
  rw [le_div_iff₀ hnR_pos, ← Nat.ceil_le]

/-- **Ceiling threshold bounds (`0 < α ≤ 1`)** for domain size `2 ^ d`. -/
theorem friBatchCeilThreshold_bounds (d : ℕ) {α : ℝ} (hα_pos : 0 < α) (hα_le : α ≤ 1) :
    let e := 2 ^ d - ⌈α * (2 ^ d : ℝ)⌉₊
    e < 2 ^ d ∧
      (((2 ^ d - e - 1 : ℕ) : ℝ) / (2 ^ d : ℝ)) < α ∧
      (e : ℝ) / (2 ^ d : ℝ) ≤ 1 - α := by
  have hnR_pos : (0 : ℝ) < (2 ^ d : ℝ) := by positivity
  set C : ℕ := ⌈α * (2 ^ d : ℝ)⌉₊
  have hαn_pos : 0 < α * (2 ^ d : ℝ) := mul_pos hα_pos hnR_pos
  have hC_pos : 0 < C := Nat.ceil_pos.mpr hαn_pos
  have hC_le : C ≤ 2 ^ d :=
    Nat.ceil_le.mpr (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      mul_le_of_le_one_left hnR_pos.le hα_le)
  refine ⟨by omega, ?_, ?_⟩
  · rw [Nat.sub_sub_self hC_le, Nat.cast_sub hC_pos, Nat.cast_one, div_lt_iff₀ hnR_pos]
    linarith [Nat.ceil_lt_add_one hαn_pos.le]
  · rw [Nat.cast_sub hC_le, Nat.cast_pow, Nat.cast_ofNat, div_le_iff₀ hnR_pos]
    linarith [Nat.le_ceil (α * (2 ^ d : ℝ))]

/-- **Floor threshold bounds (`0 ≤ α < 1`)** relative to an initial linear code `C`
([BenSassonCarmonIshaiKoppartySaraf2020], Lemma 8.2, printed pp. 38–39, Eq. (8.5)). -/
theorem friBatchFloorThreshold_bounds {d : ℕ} (C : Submodule F (OracleTable d F)) (t : ℕ)
    (stmt : FRIBatchStmt F d t) {α : ℝ} (hα_nn : 0 ≤ α) (hα_lt : α < 1) :
    let B := ⌊α * (2 ^ d : ℝ)⌋₊
    let e := 2 ^ d - 1 - B
    ((∀ (D' : Finset (Fin (2 ^ d))) (v₀ : OracleTable d F),
        v₀ ∈ C →
        ∀ v : Fin t → OracleTable d F,
          (∀ j, v j ∈ C) →
          (∀ s ∈ D', stmt.base s = v₀ s ∧ ∀ j, stmt.terms j s = v j s) →
          (D'.card : ℝ) / (2 ^ d : ℝ) ≤ α) ↔
      stmt ∉ friBatchProximityLang C t e) ∧
      B < 2 ^ d ∧
      2 ^ d - e - 1 = B ∧
      (B : ℝ) / (2 ^ d : ℝ) ≤ α ∧
      (e : ℝ) / (2 ^ d : ℝ) < 1 - α := by
  have hnR_pos : (0 : ℝ) < (2 ^ d : ℝ) := by positivity
  have hαn_nn : 0 ≤ α * (2 ^ d : ℝ) := mul_nonneg hα_nn hnR_pos.le
  set B : ℕ := ⌊α * (2 ^ d : ℝ)⌋₊
  have hB_lt : B < 2 ^ d := (Nat.floor_lt hαn_nn).mpr <| by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using mul_lt_of_lt_one_left hnR_pos hα_lt
  set e : ℕ := 2 ^ d - 1 - B
  have hcard_le_iff (D' : Finset (Fin (2 ^ d))) :
      (D'.card : ℝ) / (2 ^ d : ℝ) ≤ α ↔ D'.card ≤ B := by
    rw [div_le_iff₀ hnR_pos, ← Nat.le_floor_iff hαn_nn]
  refine ⟨?_, hB_lt, by omega, ?_, ?_⟩
  · simp only [friBatchProximityLang, Set.mem_ofPred_eq]
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
    have he_cast : (e : ℝ) + ((B : ℝ) + 1) = (2 ^ d : ℝ) := by
      exact_mod_cast (show e + (B + 1) = 2 ^ d by omega)
    linarith [Nat.lt_floor_add_one (α * (2 ^ d : ℝ))]

namespace FRISmoothParams

/-- Honest completeness relation for smooth batched FRI (`friBatchCompletenessRel` on
`params.initialCode`). -/
abbrev batchCompletenessRel (params : FRISmoothParams F) (t : ℕ) :
    FRIBatchStmt F params.d t → Unit → Prop :=
  friBatchCompletenessRel params.initialCode t

/-- Integer-threshold tuple correlated-agreement language for `(t + 1)`-word smooth batched FRI
(`friBatchProximityLang` on `params.initialCode`). -/
noncomputable abbrev batchProximityLang (params : FRISmoothParams F) (t e : ℕ) :
    Set (FRIBatchStmt F params.d t) :=
  friBatchProximityLang params.initialCode t e

/-- Real-density tuple correlated-agreement language for `(t + 1)`-word smooth batched FRI
(`friBatchCorrAgreeLang` on `params.initialCode`). -/
noncomputable abbrev batchCorrAgreeLang (params : FRISmoothParams F) (t : ℕ) (α : ℝ) :
    Set (FRIBatchStmt F params.d t) :=
  friBatchCorrAgreeLang params.initialCode t α

/-- Full direct-read schedule / input-symbol budget `(t + 1) * q` across `stmt.base` and
`stmt.terms`: `friSmoothBatchInputQueries` lists `q` scheduled input positions, with multiplicity,
with `t + 1` input symbols sufficient at each (`friSmoothBatchDecide_congr_inputQueries`). Because
`friSmoothBatchDecide` can reject on answer-list length before accessing `stmt`, repetitions
short-circuit on earlier failures, and query challenges may repeat indices, `(t + 1) * q` is a
schedule / upper-bound budget. -/
abbrev batchInputWordReads (params : FRISmoothParams F) (t : ℕ) : ℕ :=
  (t + 1) * params.q

/-- Combined word-query budget `batchInputWordReads t + proofOracleQueries =
kFinal + q * (aritySum + m + t + 3)`. -/
abbrev batchTotalWordQueries (params : FRISmoothParams F) (t : ℕ) : ℕ :=
  params.batchInputWordReads t + params.proofOracleQueries

theorem batchTotalWordQueries_eq (params : FRISmoothParams F) (t : ℕ) :
    params.batchTotalWordQueries t =
      params.kFinal + params.q * (params.aritySum + params.m + t + 3) := by
  simp only [batchTotalWordQueries, batchInputWordReads, proofOracleQueries, singleRepQueries]
  ring

end FRISmoothParams

namespace FRIParams

/-- Honest completeness relation for batched FRI (`friBatchCompletenessRel` on
`params.initialCode`). -/
abbrev batchCompletenessRel (params : FRIParams F) (t : ℕ) :
    FRIBatchStmt F params.d t → Unit → Prop :=
  friBatchCompletenessRel params.initialCode t

/-- Every affine combination `stmt.eval x` of an honest batch statement lies in
`params.initialCode`. -/
theorem eval_mem_initialCode (params : FRIParams F) {t : ℕ}
    {stmt : FRIBatchStmt F params.d t} (hrel : params.batchCompletenessRel t stmt ())
    (x : Fin t → F) :
    stmt.eval x ∈ params.initialCode :=
  eval_mem_of_friBatchCompletenessRel hrel x

/-- Integer-threshold tuple correlated-agreement language for `(t + 1)`-word batched FRI
(`friBatchProximityLang` on `params.initialCode`). -/
noncomputable abbrev batchProximityLang (params : FRIParams F) (t e : ℕ) :
    Set (FRIBatchStmt F params.d t) :=
  friBatchProximityLang params.initialCode t e

/-- Real-density tuple correlated-agreement language for `(t + 1)`-word batched FRI
(`friBatchCorrAgreeLang` on `params.initialCode`). -/
noncomputable abbrev batchCorrAgreeLang (params : FRIParams F) (t : ℕ) (α : ℝ) :
    Set (FRIBatchStmt F params.d t) :=
  friBatchCorrAgreeLang params.initialCode t α

/-- Full direct-read schedule / input-symbol budget `(t + 1) * q` across `stmt.base` and
`stmt.terms 0, …, stmt.terms (t - 1)`: `friBatchInputQueries` lists `q` scheduled input positions,
with multiplicity, with `t + 1` input symbols sufficient at each
(`friBatchDecide_congr_inputQueries`). Because `friBatchDecide` can reject on answer-list length
before accessing `stmt`, repetitions short-circuit on earlier failures, and query challenges may
repeat indices, `(t + 1) * q` is a schedule / upper-bound budget. -/
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

@[simp]
theorem toSmooth_batchCompletenessRel (params : FRIParams F) (t : ℕ) :
    params.toSmooth.batchCompletenessRel t = params.batchCompletenessRel t :=
  congrArg (friBatchCompletenessRel · t) params.toSmooth_initialCode

@[simp]
theorem toSmooth_batchProximityLang (params : FRIParams F) (t e : ℕ) :
    params.toSmooth.batchProximityLang t e = params.batchProximityLang t e :=
  congrArg (friBatchProximityLang · t e) params.toSmooth_initialCode

@[simp]
theorem toSmooth_batchCorrAgreeLang (params : FRIParams F) (t : ℕ) (α : ℝ) :
    params.toSmooth.batchCorrAgreeLang t α = params.batchCorrAgreeLang t α :=
  congrArg (friBatchCorrAgreeLang · t α) params.toSmooth_initialCode

@[simp]
theorem toSmooth_batchInputWordReads (params : FRIParams F) (t : ℕ) :
    params.toSmooth.batchInputWordReads t = params.batchInputWordReads t := rfl

@[simp]
theorem toSmooth_batchTotalWordQueries (params : FRIParams F) (t : ℕ) :
    params.toSmooth.batchTotalWordQueries t = params.batchTotalWordQueries t := by
  rw [FRISmoothParams.batchTotalWordQueries, params.toSmooth_batchInputWordReads,
    params.toSmooth_proofOracleQueries]

/-- Any statement satisfying `batchCompletenessRel` belongs to `batchProximityLang t e` for every
`e : ℕ` (specialization of `mem_friBatchProximityLang_of_completenessRel`). -/
theorem mem_batchProximityLang_of_batchCompletenessRel (params : FRIParams F) {t : ℕ} (e : ℕ)
    {stmt : FRIBatchStmt F params.d t} (hrel : params.batchCompletenessRel t stmt ()) :
    stmt ∈ params.batchProximityLang t e :=
  mem_friBatchProximityLang_of_completenessRel e hrel

/-- Contrapositively, `stmt ∉ params.batchProximityLang t e` implies `e < 2 ^ params.d`
(specialization of `lt_two_pow_of_not_mem_friBatchProximityLang`). -/
theorem lt_two_pow_of_not_mem_batchProximityLang (params : FRIParams F) {t e : ℕ}
    {stmt : FRIBatchStmt F params.d t} (hnot : stmt ∉ params.batchProximityLang t e) :
    e < 2 ^ params.d :=
  lt_two_pow_of_not_mem_friBatchProximityLang hnot

end FRIParams

/-- At batch size `t = 0`, tuple correlated agreement `batchProximityLang 0 e` coincides with the
single-word `proximityLang e` on `stmt.base` (specialization of
`mem_friBatchProximityLang_zero_iff`). -/
theorem mem_batchProximityLang_zero_iff [DecidableEq F] (params : FRIParams F) (e : ℕ)
    (stmt : FRIBatchStmt F params.d 0) :
    stmt ∈ params.batchProximityLang 0 e ↔ stmt.base ∈ params.proximityLang e :=
  mem_friBatchProximityLang_zero_iff params.initialCode e stmt

/-- **Exact ceiling `Set` equality (`α ≤ 1`)** (specialization of
`friBatchCorrAgreeLang_eq_proximityLang`). -/
theorem batchCorrAgreeLang_eq_batchProximityLang (params : FRIParams F) (t : ℕ)
    {α : ℝ} (hα_le : α ≤ 1) :
    params.batchCorrAgreeLang t α =
      params.batchProximityLang t (2 ^ params.d - ⌈α * (2 ^ params.d : ℝ)⌉₊) :=
  friBatchCorrAgreeLang_eq_proximityLang params.initialCode t hα_le

/-- **Ceiling threshold bounds (`0 < α ≤ 1`)** (specialization of `friBatchCeilThreshold_bounds`).
-/
theorem batchCeilThreshold_bounds (params : FRIParams F) {α : ℝ}
    (hα_pos : 0 < α) (hα_le : α ≤ 1) :
    let e := 2 ^ params.d - ⌈α * (2 ^ params.d : ℝ)⌉₊
    e < 2 ^ params.d ∧
      (((2 ^ params.d - e - 1 : ℕ) : ℝ) / (2 ^ params.d : ℝ)) < α ∧
      (e : ℝ) / (2 ^ params.d : ℝ) ≤ 1 - α :=
  friBatchCeilThreshold_bounds params.d hα_pos hα_le

/-- **Floor threshold bounds (`0 ≤ α < 1`)** (specialization of `friBatchFloorThreshold_bounds`).
-/
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
      (e : ℝ) / (2 ^ params.d : ℝ) < 1 - α :=
  friBatchFloorThreshold_bounds params.initialCode t stmt hα_nn hα_lt

end LanguagesAndThresholds

section BatchedFRIProtocol

variable {F : Type} [Field F]

/-- Project an `(r + 1)`-round batched challenge vector to its `r`-round single-word `FRIChal` tail
(rounds `1, …, r`). -/
@[expose] def friTailChals {d q t r : ℕ}
    (chals : Fin (r + 1) → FRIBatchChal F d q t) : Fin r → FRIChal F d q :=
  fun j => (chals j.succ).toFRIChal

/-- Committed-proof-oracle opening list of the smooth batched FRI verifier: shifts every query
`(j, idx)` of `friSmoothQueries params (friTailChals chals)` to `(j.succ, idx)` in
`Fin (params.m + 2)`. -/
@[expose] def friSmoothBatchQueries (params : FRISmoothParams F) (t : ℕ)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t) :
    List (Fin (params.m + 2) × Fin (2 ^ params.d)) :=
  (friSmoothQueries params (friTailChals chals)).map fun (j, idx) => (j.succ, idx)

/-- No query in `friSmoothBatchQueries` ever opens the round-`0` announcement table. -/
theorem round_ne_zero_of_mem_friSmoothBatchQueries (params : FRISmoothParams F) (t : ℕ)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t)
    {p : Fin (params.m + 2) × Fin (2 ^ params.d)}
    (hp : p ∈ friSmoothBatchQueries params t chals) :
    p.1 ≠ 0 := by
  rcases List.mem_map.mp hp with ⟨⟨j, _⟩, _, rfl⟩
  exact Fin.succ_ne_zero j

theorem length_friSmoothBatchQueries (params : FRISmoothParams F) (t : ℕ)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t) :
    (friSmoothBatchQueries params t chals).length = params.proofOracleQueries := by
  simp only [friSmoothBatchQueries, List.length_map, length_friSmoothQueries]

/-- Schedule of `q` scheduled input positions, with multiplicity, at which agreement of the
`t + 1` input words `(stmt.base, stmt.terms)` suffices to determine `friSmoothBatchDecide`. -/
@[expose] def friSmoothBatchInputQueries (params : FRISmoothParams F) (t : ℕ)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t) :
    List (Fin (2 ^ params.d)) :=
  friSmoothInputQueries params (friTailChals chals)

theorem length_friSmoothBatchInputQueries (params : FRISmoothParams F) (t : ℕ)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t) :
    (friSmoothBatchInputQueries params t chals).length = params.q :=
  length_friSmoothInputQueries params (friTailChals chals)

/-- Smooth batched FRI verifier decision procedure: delegates directly to `friSmoothDecide` on
`stmt.eval (chals 0).batchCoeffs` and `friTailChals chals`. -/
@[expose] def friSmoothBatchDecide [DecidableEq F] (params : FRISmoothParams F) (t : ℕ)
    (stmt : FRIBatchStmt F params.d t)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t) (answers : List F) : Bool :=
  friSmoothDecide params (stmt.eval (chals 0).batchCoeffs) (friTailChals chals) answers

/-- Input-query locality for smooth batched FRI: agreement of `(stmt.base, stmt.terms)` at the `q`
scheduled positions in `friSmoothBatchInputQueries` guarantees the same decision. -/
theorem friSmoothBatchDecide_congr_inputQueries [DecidableEq F] (params : FRISmoothParams F)
    (t : ℕ) {stmt₁ stmt₂ : FRIBatchStmt F params.d t}
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t)
    (hagree : ∀ s ∈ friSmoothBatchInputQueries params t chals,
      stmt₁.base s = stmt₂.base s ∧ ∀ j : Fin t, stmt₁.terms j s = stmt₂.terms j s)
    (answers : List F) :
    friSmoothBatchDecide params t stmt₁ chals answers =
      friSmoothBatchDecide params t stmt₂ chals answers := by
  refine friSmoothDecide_congr_inputQueries params (friTailChals chals) (fun s hs => ?_) answers
  obtain ⟨hbase, hterms⟩ := hagree s hs
  simp only [FRIBatchStmt.eval_apply, hbase]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [hterms j]

/-- **Batched multi-round smooth `2^{sᵢ}`-to-1 FRI as a `(params.m + 2)`-round `PublicCoinIOP`**
([BenSassonCarmonIshaiKoppartySaraf2020], Section 8.2, printed pp. 37–38). -/
@[expose] def friSmoothBatchIOP [DecidableEq F] (params : FRISmoothParams F) (t : ℕ) :
    PublicCoinIOP (params.m + 2) params.d (FRIBatchStmt F params.d t) Unit F
      (FRIBatchChal F params.d params.q t) where
  proveRound := Fin.cases
    (fun _ _ _ => fun _ => 0)
    (fun j stmt _ prev =>
      (friSmoothIOP params).proveRound j
        (stmt.eval (prev ⟨0, Nat.zero_lt_succ j.val⟩).batchCoeffs) ()
        (fun i => (prev i.succ).toFRIChal))
  queries _ chals := friSmoothBatchQueries params t chals
  decide stmt chals answers := friSmoothBatchDecide params t stmt chals answers

/-- Exact committed-proof-oracle opening count of `friSmoothBatchIOP`:
`params.proofOracleQueries = kFinal + q * (aritySum + m + 2)`. -/
theorem length_friSmoothBatchIOP_queries [DecidableEq F] (params : FRISmoothParams F) (t : ℕ)
    (stmt : FRIBatchStmt F params.d t)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t) :
    ((friSmoothBatchIOP params t).queries stmt chals).length = params.proofOracleQueries :=
  length_friSmoothBatchQueries params t chals

@[simp]
theorem iopProverOracles_friSmoothBatchIOP_zero [DecidableEq F] (params : FRISmoothParams F)
    (t : ℕ) (stmt : FRIBatchStmt F params.d t)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t) :
    iopProverOracles (friSmoothBatchIOP params t) stmt () chals 0 = fun _ => 0 := by
  simp only [iopProverOracles, friSmoothBatchIOP, Fin.cases_zero]

@[simp]
theorem iopProverOracles_friSmoothBatchIOP_succ [DecidableEq F] (params : FRISmoothParams F)
    (t : ℕ) (stmt : FRIBatchStmt F params.d t)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t)
    (j : Fin (params.m + 1)) :
    iopProverOracles (friSmoothBatchIOP params t) stmt () chals j.succ =
      iopProverOracles (friSmoothIOP params) (stmt.eval (chals 0).batchCoeffs) ()
        (friTailChals chals) j := by
  simp only [iopProverOracles, friSmoothBatchIOP, Fin.cases_succ, prefixChallenges]
  rfl

/-- **Exact verification reduction from `friSmoothBatchIOP` to single-word `friSmoothIOP`**. -/
theorem iopVerify_friSmoothBatchIOP_eq_iopVerify_friSmoothIOP [DecidableEq F]
    (params : FRISmoothParams F) (t : ℕ)
    (stmt : FRIBatchStmt F params.d t)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t)
    (oracles : Fin (params.m + 2) → OracleTable params.d F) :
    iopVerify (friSmoothBatchIOP params t) stmt chals oracles =
      iopVerify (friSmoothIOP params) (stmt.eval (chals 0).batchCoeffs)
        (friTailChals chals) (fun j => oracles j.succ) := by
  simp only [iopVerify, iopAnswers, friSmoothBatchIOP, friSmoothBatchQueries, friSmoothBatchDecide,
    List.map_map]
  rfl

/-- Pointwise acceptance predicate for a single smooth batched FRI query repetition starting at
`s : Fin (2 ^ d)`. -/
@[expose] def friSmoothBatchSingleAccepts (params : FRISmoothParams F) (t : ℕ)
    (stmt : FRIBatchStmt F params.d t)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t)
    (oracles : Fin (params.m + 2) → OracleTable params.d F) (s : Fin (2 ^ params.d)) : Prop :=
  friSmoothSingleAccepts params (stmt.eval (chals 0).batchCoeffs) (friTailChals chals)
    (fun j => oracles j.succ) s

/-- **Exact characterization of smooth batched FRI IOP verification**. -/
theorem iopVerify_friSmoothBatchIOP_eq_true_iff [DecidableEq F] (params : FRISmoothParams F)
    (t : ℕ) (stmt : FRIBatchStmt F params.d t)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t)
    (oracles : Fin (params.m + 2) → OracleTable params.d F) :
    iopVerify (friSmoothBatchIOP params t) stmt chals oracles = true ↔
      ∀ a : Fin params.q,
        friSmoothBatchSingleAccepts params t stmt chals oracles
          ((chals (Fin.last (params.m + 1))).queryIdxs a) := by
  rw [iopVerify_friSmoothBatchIOP_eq_iopVerify_friSmoothIOP, iopVerify_friSmoothIOP_eq_true_iff,
    ← Fin.succ_last params.m]
  rfl

/-- **Perfect completeness of the smooth batched FRI IOP**. -/
theorem friSmoothBatchIOP_complete [DecidableEq F] (params : FRISmoothParams F) (t : ℕ) :
    IOPCompleteness (friSmoothBatchIOP params t) (params.batchCompletenessRel t) := by
  intro stmt ⟨⟩ hrel chals
  rw [iopVerify_friSmoothBatchIOP_eq_iopVerify_friSmoothIOP]
  simp only [iopProverOracles_friSmoothBatchIOP_succ]
  exact friSmoothIOP_complete params (stmt.eval (chals 0).batchCoeffs) ()
    (eval_mem_of_friBatchCompletenessRel hrel (chals 0).batchCoeffs) (friTailChals chals)

/-- **Perfect deterministic BCS completeness for smooth batched FRI**. -/
theorem friSmoothBatchBCS_verify_prove_eq_true [DecidableEq F] (params : FRISmoothParams F)
    (t : ℕ) (H : List Bool → List Bool → List Bool) (k : List Bool) {ℓ : ℕ}
    (hlen : ∀ y, (H k y).length = ℓ) (encSym : F → List Bool)
    (hFS : FRIBatchStmt F params.d t → List (List Bool) →
      FRIBatchChal F params.d params.q t)
    {stmt : FRIBatchStmt F params.d t} (hrel : params.batchCompletenessRel t stmt ()) :
    bcsVerify (friSmoothBatchIOP params t) H k encSym hFS stmt
      (bcsProve (friSmoothBatchIOP params t) H k encSym hFS stmt ()) = true :=
  bcsVerify_bcsProve_eq_true (friSmoothBatchIOP_complete params t) H k hlen encSym hFS hrel

/-- **Perfect BCS ROM completeness for smooth batched FRI**. -/
theorem friSmoothBatchBCS_honestROMGame_eq_pure_true [DecidableEq F] [Fintype F]
    (params : FRISmoothParams F) (t : ℕ) (encSym : F → List Bool)
    {stmt : FRIBatchStmt F params.d t} (hrel : params.batchCompletenessRel t stmt ()) (σ : ℕ) :
    bcsHonestROMGame (friSmoothBatchIOP params t) encSym stmt () σ = PMF.pure true :=
  bcsHonestROMGame_eq_pure_true (friSmoothBatchIOP_complete params t) encSym hrel σ

/-- **Succinct verifier Merkle query cost bound for BCS-compiled smooth batched FRI**. -/
theorem isCostBounded_bcsMTCost_friSmoothBatchVerifyROM [DecidableEq F]
    (params : FRISmoothParams F) (t : ℕ)
    (encSym : F → List Bool) (stmt : FRIBatchStmt F params.d t)
    (prf : BCSProof (params.m + 2) F) {L_path : ℕ}
    (hops : ∀ op ∈ prf.openings, op.path.length ≤ L_path) :
    IsCostBounded bcsMTCost (bcsVerifyROM (friSmoothBatchIOP params t) encSym stmt prf)
      (params.proofOracleQueries * (L_path + 1)) :=
  isCostBounded_bcsMTCost_bcsVerifyROM_of_queries_le (friSmoothBatchIOP params t) encSym stmt prf
    (fun chals => (length_friSmoothBatchIOP_queries params t stmt chals).le) hops

/-- Committed-proof-oracle opening list of the batched FRI verifier (derived directly from
`friSmoothBatchQueries params.toSmooth`). Round `0` is never opened; all
`params.proofOracleQueries = kFinal + q * (3 * m + 2)` openings target the committed prover tables
`f⁽⁰⁾, …, f⁽ᵐ⁾` in rounds `1, …, m + 1`. -/
@[expose] def friBatchQueries (params : FRIParams F) (t : ℕ)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t) :
    List (Fin (params.m + 2) × Fin (2 ^ params.d)) :=
  friSmoothBatchQueries params.toSmooth t chals

/-- No query in `friBatchQueries` ever opens the round-`0` announcement table (corollary of
`round_ne_zero_of_mem_friSmoothBatchQueries`). -/
theorem round_ne_zero_of_mem_friBatchQueries (params : FRIParams F) (t : ℕ)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t)
    {p : Fin (params.m + 2) × Fin (2 ^ params.d)} (hp : p ∈ friBatchQueries params t chals) :
    p.1 ≠ 0 :=
  round_ne_zero_of_mem_friSmoothBatchQueries params.toSmooth t chals hp

theorem length_friBatchQueries (params : FRIParams F) (t : ℕ)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t) :
    (friBatchQueries params t chals).length = params.proofOracleQueries := by
  rw [friBatchQueries, length_friSmoothBatchQueries, params.toSmooth_proofOracleQueries]

/-- Schedule of `q` scheduled input positions, with multiplicity, at which agreement of the
`t + 1` input words `(stmt.base, stmt.terms 0, …, stmt.terms (t - 1))` suffices to determine
`friBatchDecide` outside `PublicCoinIOP.queries` (derived directly from
`friSmoothBatchInputQueries params.toSmooth`). -/
@[expose] def friBatchInputQueries (params : FRIParams F) (t : ℕ)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t) :
    List (Fin (2 ^ params.d)) :=
  friSmoothBatchInputQueries params.toSmooth t chals

theorem length_friBatchInputQueries (params : FRIParams F) (t : ℕ)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t) :
    (friBatchInputQueries params t chals).length = params.q :=
  length_friSmoothBatchInputQueries params.toSmooth t chals

/-- Batched FRI verifier decision procedure (derived directly from
`friSmoothBatchDecide params.toSmooth`). -/
@[expose] def friBatchDecide [DecidableEq F] (params : FRIParams F) (t : ℕ)
    (stmt : FRIBatchStmt F params.d t)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t) (answers : List F) : Bool :=
  friSmoothBatchDecide params.toSmooth t stmt chals answers

/-- Input-query locality (corollary of `friSmoothBatchDecide_congr_inputQueries`). -/
theorem friBatchDecide_congr_inputQueries [DecidableEq F] (params : FRIParams F) (t : ℕ)
    {stmt₁ stmt₂ : FRIBatchStmt F params.d t}
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t)
    (hagree : ∀ s ∈ friBatchInputQueries params t chals,
      stmt₁.base s = stmt₂.base s ∧ ∀ j : Fin t, stmt₁.terms j s = stmt₂.terms j s)
    (answers : List F) :
    friBatchDecide params t stmt₁ chals answers = friBatchDecide params t stmt₂ chals answers :=
  friSmoothBatchDecide_congr_inputQueries params.toSmooth t chals hagree answers

/-- **Batched multi-round 2-to-1 FRI as a `(params.m + 2)`-round `PublicCoinIOP`**
([BenSassonCarmonIshaiKoppartySaraf2020], Section 8.2, printed pp. 37–38). -/
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

/-- **Exact batched IOP equality**: binary 2-to-1 `friBatchIOP params t` coincides identically with
`friSmoothBatchIOP params.toSmooth t`. -/
theorem friBatchIOP_eq_friSmoothBatchIOP [DecidableEq F] (params : FRIParams F) (t : ℕ) :
    friBatchIOP params t = friSmoothBatchIOP params.toSmooth t := by
  simp only [friBatchIOP, friSmoothBatchIOP, friIOP_eq_friSmoothIOP, friBatchQueries,
    friBatchDecide]

/-- Exact committed-proof-oracle opening count of `friBatchIOP` (corollary of
`length_friSmoothBatchIOP_queries`). -/
theorem length_friBatchIOP_queries [DecidableEq F] (params : FRIParams F) (t : ℕ)
    (stmt : FRIBatchStmt F params.d t)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t) :
    ((friBatchIOP params t).queries stmt chals).length = params.proofOracleQueries := by
  rw [friBatchIOP_eq_friSmoothBatchIOP, length_friSmoothBatchIOP_queries,
    params.toSmooth_proofOracleQueries]

@[simp]
theorem iopProverOracles_friBatchIOP_zero [DecidableEq F] (params : FRIParams F) (t : ℕ)
    (stmt : FRIBatchStmt F params.d t)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t) :
    iopProverOracles (friBatchIOP params t) stmt () chals 0 = fun _ => 0 := by
  rw [friBatchIOP_eq_friSmoothBatchIOP]
  exact iopProverOracles_friSmoothBatchIOP_zero params.toSmooth t stmt chals

@[simp]
theorem iopProverOracles_friBatchIOP_succ [DecidableEq F] (params : FRIParams F) (t : ℕ)
    (stmt : FRIBatchStmt F params.d t)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t)
    (j : Fin (params.m + 1)) :
    iopProverOracles (friBatchIOP params t) stmt () chals j.succ =
      iopProverOracles (friIOP params) (stmt.eval (chals 0).batchCoeffs) ()
        (friTailChals chals) j := by
  rw [friBatchIOP_eq_friSmoothBatchIOP, friIOP_eq_friSmoothIOP]
  exact iopProverOracles_friSmoothBatchIOP_succ params.toSmooth t stmt chals j

/-- **Exact verification reduction from `friBatchIOP` to single-word `friIOP`** (corollary of
`iopVerify_friSmoothBatchIOP_eq_iopVerify_friSmoothIOP`). -/
theorem iopVerify_friBatchIOP_eq_iopVerify_friIOP [DecidableEq F] (params : FRIParams F) (t : ℕ)
    (stmt : FRIBatchStmt F params.d t)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t)
    (oracles : Fin (params.m + 2) → OracleTable params.d F) :
    iopVerify (friBatchIOP params t) stmt chals oracles =
      iopVerify (friIOP params) (stmt.eval (chals 0).batchCoeffs)
        (friTailChals chals) (fun j => oracles j.succ) := by
  rw [friBatchIOP_eq_friSmoothBatchIOP, friIOP_eq_friSmoothIOP]
  exact iopVerify_friSmoothBatchIOP_eq_iopVerify_friSmoothIOP params.toSmooth t stmt chals oracles

/-- Pointwise acceptance predicate for a single batched FRI query repetition starting at
`s : Fin (2 ^ d)`. -/
@[expose] def friBatchSingleAccepts (params : FRIParams F) (t : ℕ)
    (stmt : FRIBatchStmt F params.d t)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t)
    (oracles : Fin (params.m + 2) → OracleTable params.d F) (s : Fin (2 ^ params.d)) : Prop :=
  friSingleAccepts params (stmt.eval (chals 0).batchCoeffs) (friTailChals chals)
    (fun j => oracles j.succ) s

/-- Exact equivalence between binary `friBatchSingleAccepts` and smooth
`friSmoothBatchSingleAccepts params.toSmooth`. -/
theorem friBatchSingleAccepts_iff_friSmoothBatchSingleAccepts (params : FRIParams F) (t : ℕ)
    (stmt : FRIBatchStmt F params.d t)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t)
    (oracles : Fin (params.m + 2) → OracleTable params.d F) (s : Fin (2 ^ params.d)) :
    friBatchSingleAccepts params t stmt chals oracles s ↔
      friSmoothBatchSingleAccepts params.toSmooth t stmt chals oracles s :=
  friSingleAccepts_iff_friSmoothSingleAccepts params (stmt.eval (chals 0).batchCoeffs)
    (friTailChals chals) (fun j => oracles j.succ) s

/-- **Exact characterization of batched FRI IOP verification** (corollary of
`iopVerify_friSmoothBatchIOP_eq_true_iff`). -/
theorem iopVerify_friBatchIOP_eq_true_iff [DecidableEq F] (params : FRIParams F) (t : ℕ)
    (stmt : FRIBatchStmt F params.d t)
    (chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t)
    (oracles : Fin (params.m + 2) → OracleTable params.d F) :
    iopVerify (friBatchIOP params t) stmt chals oracles = true ↔
      ∀ a : Fin params.q,
        friBatchSingleAccepts params t stmt chals oracles
          ((chals (Fin.last (params.m + 1))).queryIdxs a) := by
  rw [friBatchIOP_eq_friSmoothBatchIOP, iopVerify_friSmoothBatchIOP_eq_true_iff]
  exact forall_congr' fun a =>
    (friBatchSingleAccepts_iff_friSmoothBatchSingleAccepts params t stmt chals oracles _).symm

/-- **Perfect completeness of the batched FRI IOP** (corollary of `friSmoothBatchIOP_complete`). -/
theorem friBatchIOP_complete [DecidableEq F] (params : FRIParams F) (t : ℕ) :
    IOPCompleteness (friBatchIOP params t) (params.batchCompletenessRel t) := by
  rw [friBatchIOP_eq_friSmoothBatchIOP, ← params.toSmooth_batchCompletenessRel]
  exact friSmoothBatchIOP_complete params.toSmooth t

/-- **Perfect deterministic BCS completeness for batched FRI** (corollary of
`friSmoothBatchBCS_verify_prove_eq_true`). -/
theorem friBatchBCS_verify_prove_eq_true [DecidableEq F] (params : FRIParams F) (t : ℕ)
    (H : List Bool → List Bool → List Bool) (k : List Bool) {ℓ : ℕ}
    (hlen : ∀ y, (H k y).length = ℓ) (encSym : F → List Bool)
    (hFS : FRIBatchStmt F params.d t → List (List Bool) →
      FRIBatchChal F params.d params.q t)
    {stmt : FRIBatchStmt F params.d t} (hrel : params.batchCompletenessRel t stmt ()) :
    bcsVerify (friBatchIOP params t) H k encSym hFS stmt
      (bcsProve (friBatchIOP params t) H k encSym hFS stmt ()) = true := by
  rw [friBatchIOP_eq_friSmoothBatchIOP]
  exact friSmoothBatchBCS_verify_prove_eq_true params.toSmooth t H k hlen encSym hFS
    (by rwa [params.toSmooth_batchCompletenessRel])

/-- **Perfect BCS ROM completeness for batched FRI** (corollary of
`friSmoothBatchBCS_honestROMGame_eq_pure_true`). -/
theorem friBatchBCS_honestROMGame_eq_pure_true [DecidableEq F] [Fintype F]
    (params : FRIParams F) (t : ℕ) (encSym : F → List Bool)
    {stmt : FRIBatchStmt F params.d t} (hrel : params.batchCompletenessRel t stmt ()) (σ : ℕ) :
    bcsHonestROMGame (friBatchIOP params t) encSym stmt () σ = PMF.pure true := by
  rw [friBatchIOP_eq_friSmoothBatchIOP]
  exact friSmoothBatchBCS_honestROMGame_eq_pure_true params.toSmooth t encSym
    (by rwa [params.toSmooth_batchCompletenessRel]) σ

/-- **Succinct verifier Merkle query cost bound for BCS-compiled batched FRI** (corollary of
`isCostBounded_bcsMTCost_friSmoothBatchVerifyROM`). -/
theorem isCostBounded_bcsMTCost_friBatchVerifyROM [DecidableEq F] (params : FRIParams F) (t : ℕ)
    (encSym : F → List Bool) (stmt : FRIBatchStmt F params.d t)
    (prf : BCSProof (params.m + 2) F) {L_path : ℕ}
    (hops : ∀ op ∈ prf.openings, op.path.length ≤ L_path) :
    IsCostBounded bcsMTCost (bcsVerifyROM (friBatchIOP params t) encSym stmt prf)
      (params.proofOracleQueries * (L_path + 1)) := by
  rw [friBatchIOP_eq_friSmoothBatchIOP, ← params.toSmooth_proofOracleQueries]
  exact isCostBounded_bcsMTCost_friSmoothBatchVerifyROM params.toSmooth t encSym stmt prf hops

end BatchedFRIProtocol

end Cslib.Crypto.Protocols.FRI
