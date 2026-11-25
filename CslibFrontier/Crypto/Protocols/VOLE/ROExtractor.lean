/-
Copyright (c) 2026 Samuel Schlesinger, Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.AnonymousToken.Basic
public import CslibFrontier.Crypto.Protocols.AnonymousToken.Conservation
public import CslibFrontier.Crypto.Protocols.FAEST.Conversion
public import CslibFrontier.Crypto.Protocols.VOLE.Basic
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
public import CslibFrontier.Languages.Probabilistic.RandomOracle.Sum
public import CslibFrontier.Languages.Probabilistic.UntilBad.Flag
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Foundations.Control.Monad.Memoize
import CslibFrontier.Languages.Probabilistic.Memoize
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.InterpNorm
import CslibFrontier.Languages.Probabilistic.Oracle.RunState
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.QueryCount
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.RunLog
import CslibFrontier.Languages.Probabilistic.QueryCount.Scale
import CslibFrontier.Languages.Probabilistic.QueryCount.Sum
import CslibFrontier.Languages.Probabilistic.UntilBad.TwoCost
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.BindFailure
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Support
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.UniformBound
import CslibFrontier.Tactic.SuppCases
import Mathlib.Data.Finset.Card

/-!
# Straight-line ROM VOLE-in-the-head leaf extraction and AnonymousToken bridges

This module formalizes straight-line knowledge extraction in the classical random oracle model
(ROM) for flat all-but-one `2 ^ d`-leaf (one-repetition) `leaf_hash::shake`-style VOLE-in-the-head
vector commitments, explicit query-bounded reductions to `AnonymousToken.extractedExperiment` and
`AnonymousToken.Conservation.extractedConservationExperiment`, and separation witnesses showing why
PRG-based leaf commitments (`leaf_hash::aes_ctr`) do not have a leaf-query-log extractor in the
plain ROM.

## Protocol model and extraction mechanism

* **Two-channel ROM (`VOLEITHROSpec`)**: a leaf commitment oracle `H_leaf(k, iv, idx) ↦ (sd, com)`
  ([BaumEtAl2023FAEST], v1.0 `H0` (`SHAKE`) leaf commitments; `faest-arch-opt` `leaf_hash::shake`)
  paired with a Fiat–Shamir challenge oracle `H_FS(stmt, iv, coms, d_corr, preMsg) ↦ Δ`
  (`FSQuery`). Including `d_corr` and `preMsg` inside `H_FS` binds `w* = d_corr + u` and `preMsg`
  before `Δ` is drawn, matching [BaumBMRS2023Eprint] and [BaumEtAl2026FAEST].
* **`FAEST.Conversion` reconstruction**: verifying the `2 ^ d - 1` opened indices `pIdx = i ^^^ Δ`
  (`collectOpenRows`) produces `FAEST.verifierRows`, so `FAEST.convertExpandedRows` satisfies
  `FAEST.convertExpandedRows_correlation` ([BaumEtAl2026FAEST], Section 5.4, Figure 5.6 /
  Proposition 5.2) whenever the prover's `H_leaf` queries uniquely determine all `2 ^ d` leaves.
* **Zero-rewinding extraction (`extractWitnessFromTrace`)**: reading only the `H_leaf` query trace
  recorded *prior* to running verification recovers all `2 ^ d` leaves and `u`, yielding the witness
  `decWit (d_corr + u)` straight-line. Using a two-channel sticky bad-state handler
  (`voleithStickyMemoize`) via `OracleComp.toOuterMeasure_bad_le_two`, extraction failure across a
  single proof or an adaptive `m`-call verification oracle is bounded by
  `Q_leaf * (Q_leaf + 2 ^ d * Q_FS) / 2 ^ comLen + Q_FS * ε_rel`.
* **AnonymousToken bridges (`Basic` & `Conservation`)**: because a VOLE-ACT Issuer only verifies
  client proofs (`IssueRequest`, `SpendRequest`) and never simulates proofs for the adversary
  ([VOLEACT2026], Initial Issuance / Spending; specialising [BaumBMRS2023Eprint], Lemma 4,
  pp. 19–20, to a single challenge repetition and an RO leaf commitment), plain straight-line
  multi-verify ROM extraction suffices without simulation-extractability. Unextracted ROM
  adversaries reduce explicitly to `AnonymousToken.extractedExperiment` and
  `AnonymousToken.Conservation.extractedConservationExperiment` with additive loss `ε_KS` and
  preserved signing/issuer query budgets.
* **PRG leaf separation (`leaf_hash::aes_ctr`)**: a local PRG prover (`prgLeafProver`, modeling
  `leaf_hash::aes_ctr` as used in [VoleMole2026], `src/act/issue.hpp:121`, `src/act/spend.hpp:289`)
  makes `0` `H_leaf` queries (`tr_leaf = []`) and accepts with probability `1` under deterministic
  PRG verification (`prgLeafVerify`), defeating any statement- and proof-less leaf-query-log
  extractor `extLog : LeafTrace → Option Wit` with probability `1` against disjoint-witness
  statements (`exists_valid_prgLeaf_queryLog_fails_Rel_eq_one`; this extractor class excludes
  `extractWitnessFromTrace`, which reads `(tr, prf)` and is covered by the proof-only separation
  below). When two distinct key vectors collide on `PRG` commitments (`hComEq`) yet produce
  distinct expanded `u` masks (`hUNe`, unsatisfiable for any injective `prgLeaf`, motivating
  almost-injective PRGs in [BaumEtAl2026FAESTer], Definition 27, pp. 17–18, and Lemma 32,
  pp. 25–26) and colliding `d_corr` (`hdCorrEq`) across disjoint-witness statements, every
  deterministic preimage-table seed extractor `extPre : coms → iv → idx → Seed` fails `Rel` with
  probability `1` (`prgLeaf_preimage_extractor_fails`), and any unbounded proof-only extractor
  `ext : LeafTrace → VOLEITHProof → Option Wit` omitting `stmt` fails `Rel` with probability at
  least `1 / |Chal|` at depth `d ≥ 1` (`exists_valid_prgLeaf_proofOnly_extract_fails_ge`).

## Scope and gaps

* Models a single-repetition flat `2 ^ d`-leaf `leaf_hash::shake` commitment with arbitrary relation
  soundness `ε_rel`; multi-tree BAVC (`T_open`, grinding bits), full `VOLEHash`/`ZKHash`
  reductions (#4987), ideal-cipher AES-CTR extraction, full FAESTer ([BaumEtAl2026FAESTer],
  Definition 27 / Lemma 32) post-challenge equivocation for unbounded extractors that also receive
  `stmt`, and machine-checked PPT/`TimeM` runtime certificates remain open under #7068. All
  reductions are explicit `ProbComp`/`ProbOracleComp` programs with query-cost bounds, not
  Word-RAM or Turing-machine time bounds.

## References

* [C. Baum et al., *Publicly Verifiable Zero-Knowledge and Post-Quantum Signatures from
  VOLE-in-the-Head* (full version, ePrint 2023/996)][BaumBMRS2023Eprint], Section 4 (Lemma 4,
  pp. 19–20, specialised here to one challenge round and RO leaf commitments).
* [C. Baum et al., *FAEST: Algorithm Specifications*, version 1.0][BaumEtAl2023FAEST]: `H0`
  (`SHAKE`) leaf hashing.
* [C. Baum et al., *FAEST v3: Algorithm Specifications*, version 3.0][BaumEtAl2026FAEST],
  Section 5.4 (Figure 5.6 / Proposition 5.2) and Section 5.5 (Figure 5.7).
* [C. Baum et al., *Shorter, Tighter, FAESTer: Optimizations and Improved (QROM) Analysis for
  VOLE-in-the-Head Signatures* (ePrint 2026/164)][BaumEtAl2026FAESTer], Section 3 (Definition 27,
  pp. 17–18) and Section 3.3 (Lemmas 32–33, pp. 25–26).
* [T. Zhang, C. Patton, S. Schlesinger, *VOLE-ACT*][VOLEACT2026], Parameters, Tag, Initial Issuance,
  and Spending.
* [C. Patton, T. Zhang, *vole-mole* (commit `87af6871f`)][VoleMole2026], `src/act/issue.hpp:121`,
  `src/act/spend.hpp:289`, `src/ihat/circuit.hpp:33`, `src/pomfrit/redeem.hpp:75`.
-/

public section

namespace Cslib.Crypto.Protocols.VOLE

open Cslib Cslib.Probability Cslib.OracleComp
open Cslib.Crypto.FAEST Cslib.Crypto.AnonymousToken
open scoped BigOperators ENNReal NNReal

/-! ### Two-Channel `leaf_hash::shake` ROM Interface and `FAEST.Conversion` Extraction -/

section ROProtocol

/-- Input query `(k, iv, idx)` to the `leaf_hash::shake`-style random oracle `H_leaf`. -/
structure LeafQuery (d : ℕ) (Seed IV : Type) where
  /-- Leaf root seed key `k_idx`. -/
  seed : Seed
  /-- Proof initialization vector `iv`. -/
  iv : IV
  /-- Leaf index `idx : Fin (2 ^ d)`. -/
  index : Fin (2 ^ d)
  deriving DecidableEq

/-- Output `(sd, com)` of `H_leaf(k, iv, idx)`. -/
structure LeafOutput (sdLen comLen : ℕ) where
  /-- Expanded leaf seed bits `sd_idx`. -/
  seedOut : BitString sdLen
  /-- Leaf commitment digest `com_idx`. -/
  com : BitString comLen
  deriving DecidableEq

/-- Reorder `LeafOutput sdLen comLen` so the commitment digest is the first coordinate. -/
private def leafOutputEquiv (sdLen comLen : ℕ) :
    LeafOutput sdLen comLen ≃ BitString comLen × BitString sdLen where
  toFun out := (out.com, out.seedOut)
  invFun p := ⟨p.2, p.1⟩
  left_inv out := by cases out; rfl
  right_inv p := by cases p; rfl

instance (sdLen comLen : ℕ) : Fintype (LeafOutput sdLen comLen) :=
  Fintype.ofEquiv (BitString comLen × BitString sdLen)
    { toFun := fun p => ⟨p.2, p.1⟩
      invFun := fun out => (out.com, out.seedOut)
      left_inv := fun p => by cases p; rfl
      right_inv := fun out => by cases out; rfl }

instance (sdLen comLen : ℕ) : Nonempty (LeafOutput sdLen comLen) :=
  ⟨⟨0, 0⟩⟩

/-- Input query to the Fiat–Shamir oracle `H_FS`, hashing `(stmt, iv, coms, dCorr, preMsg)` before
drawing challenge `Δ`. -/
structure FSQuery (d comLen rowLen : ℕ) (Stmt IV PreMsg : Type) where
  /-- Public instance statement. -/
  stmt : Stmt
  /-- Proof initialization vector `iv`. -/
  iv : IV
  /-- Committed leaf digests `coms`. -/
  coms : Fin (2 ^ d) → BitString comLen
  /-- Witness correction `d_corr` binding `w* = decWit (dCorr + u)` prior to `Δ`. -/
  dCorr : BitString rowLen
  /-- Any pre-challenge check commitments fixed prior to `Δ`. -/
  preMsg : PreMsg
  deriving DecidableEq

/-- Combined non-interactive `leaf_hash::shake` VOLEitH proof. -/
structure VOLEITHProof (d comLen rowLen : ℕ) (Seed IV PreMsg : Type) where
  /-- Proof initialization vector `iv`. -/
  iv : IV
  /-- Leaf commitments `coms`. -/
  coms : Fin (2 ^ d) → BitString comLen
  /-- Witness correction `d_corr`. -/
  dCorr : BitString rowLen
  /-- Pre-challenge check message. -/
  preMsg : PreMsg
  /-- Opened keys `k_idx` (checked by verifier for all `idx ≠ Δ`). -/
  openKeys : Fin (2 ^ d) → Seed
  deriving DecidableEq

/-- Leaf random-oracle specification `H_leaf`. -/
abbrev VOLEITHLeafSpec (d sdLen comLen : ℕ) (Seed IV : Type) :
    OracleSpec (LeafQuery d Seed IV) :=
  fun _ => LeafOutput sdLen comLen

/-- Fiat–Shamir random-oracle specification `H_FS`. -/
abbrev VOLEITHFSSpec (d comLen rowLen : ℕ) (Stmt IV PreMsg Chal : Type) :
    OracleSpec (FSQuery d comLen rowLen Stmt IV PreMsg) :=
  fun _ => Chal

/-- Two-channel VOLEitH ROM oracle specification: leaf oracle on `Sum.inl`, Fiat–Shamir oracle on
`Sum.inr`. -/
abbrev VOLEITHROSpec (d sdLen comLen rowLen : ℕ) (Stmt Seed IV PreMsg Chal : Type) :=
  VOLEITHLeafSpec d sdLen comLen Seed IV ⊕ₒ VOLEITHFSSpec d comLen rowLen Stmt IV PreMsg Chal

/-- Association-list trace recorded by `H_leaf`. -/
abbrev LeafTrace (d sdLen comLen : ℕ) (Seed IV : Type) :=
  List (LeafQuery d Seed IV × LeafOutput sdLen comLen)

/-- Association-list trace recorded by `H_FS`. -/
abbrev FSTrace (d comLen rowLen : ℕ) (Stmt IV PreMsg Chal : Type) :=
  List (FSQuery d comLen rowLen Stmt IV PreMsg × Chal)

/-- Combined two-channel lazy ROM trace `(tr_leaf, tr_FS)`. -/
abbrev VOLEITHTraceState (d sdLen comLen rowLen : ℕ) (Stmt Seed IV PreMsg Chal : Type) :=
  LeafTrace d sdLen comLen Seed IV × FSTrace d comLen rowLen Stmt IV PreMsg Chal

/-- Extract the Fiat–Shamir query corresponding to `(stmt, prf)`. -/
@[expose] def VOLEITHProof.fsQuery {d comLen rowLen : ℕ} {Stmt Seed IV PreMsg : Type}
    (stmt : Stmt) (prf : VOLEITHProof d comLen rowLen Seed IV PreMsg) :
    FSQuery d comLen rowLen Stmt IV PreMsg :=
  ⟨stmt, prf.iv, prf.coms, prf.dCorr, prf.preMsg⟩

/-- Query-cost indicator charging `1` per `H_leaf` query (`0` on `H_FS`). -/
@[expose] def voleithLeafCost {d : ℕ} {comLen rowLen : ℕ} {Stmt Seed IV PreMsg : Type} :
    LeafQuery d Seed IV ⊕ FSQuery d comLen rowLen Stmt IV PreMsg → ℕ
  | .inl _ => 1
  | .inr _ => 0

/-- Query-cost indicator charging `1` per `H_FS` query (`0` on `H_leaf`). -/
@[expose] def voleithFSCost {d : ℕ} {comLen rowLen : ℕ} {Stmt Seed IV PreMsg : Type} :
    LeafQuery d Seed IV ⊕ FSQuery d comLen rowLen Stmt IV PreMsg → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- Two-channel association-list memoizer inside `ProbComp`, evaluating to
`RandomOracle.memoizeSum`. -/
@[expose] noncomputable def voleithMemoizeProg {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [Fintype Chal] [Nonempty Chal] :
    (q : LeafQuery d Seed IV ⊕ FSQuery d comLen rowLen Stmt IV PreMsg) →
      StateT (VOLEITHTraceState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) ProbComp
        (VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal q) :=
  OracleComp.sumHandler
    (fun q => RandomOracle.zoomStateT Prod.fst (fun st tr₁ => (tr₁, st.2))
      (Cslib.memoize (fun _ => ProbComp.uniform (LeafOutput sdLen comLen)) q))
    (fun q => RandomOracle.zoomStateT Prod.snd (fun st tr₂ => (st.1, tr₂))
      (Cslib.memoize (fun _ => ProbComp.uniform Chal) q))

/-- PMF-level two-channel lazy random-oracle handler for `VOLEITHROSpec`. -/
@[expose] noncomputable def voleithMemoize {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [Fintype Chal] [Nonempty Chal] :
    (q : LeafQuery d Seed IV ⊕ FSQuery d comLen rowLen Stmt IV PreMsg) →
      StateT (VOLEITHTraceState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) PMF
        (VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal q) :=
  RandomOracle.memoizeSum
    (fun _ : LeafQuery d Seed IV => PMF.uniformOfFintype (LeafOutput sdLen comLen))
    (fun _ : FSQuery d comLen rowLen Stmt IV PreMsg => PMF.uniformOfFintype Chal)

private theorem eval_voleithMemoizeProg {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [Fintype Chal] [Nonempty Chal]
    (q : LeafQuery d Seed IV ⊕ FSQuery d comLen rowLen Stmt IV PreMsg)
    (st : VOLEITHTraceState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) :
    ProbComp.eval (voleithMemoizeProg q st) = voleithMemoize q st := by
  rcases st with ⟨tr₁, tr₂⟩
  rcases q with q | q
  · simp only [voleithMemoizeProg, voleithMemoize, OracleComp.sumHandler,
      RandomOracle.memoizeSum_inl, RandomOracle.eval_zoomStateT_memoize]
    have hdist₁ :
        (fun _ : LeafQuery d Seed IV =>
          ProbComp.eval (ProbComp.uniform (LeafOutput sdLen comLen))) =
          fun _ => PMF.uniformOfFintype (LeafOutput sdLen comLen) :=
      funext fun _ => ProbComp.eval_uniform _
    rw [hdist₁]
  · simp only [voleithMemoizeProg, voleithMemoize, OracleComp.sumHandler,
      RandomOracle.memoizeSum_inr, RandomOracle.eval_zoomStateT_memoize]
    have hdist₂ :
        (fun _ : FSQuery d comLen rowLen Stmt IV PreMsg => ProbComp.eval (ProbComp.uniform Chal)) =
          fun _ => PMF.uniformOfFintype Chal :=
      funext fun _ => ProbComp.eval_uniform _
    rw [hdist₂]

/-- Query `H_leaf` for indices `i = 1, ..., k - 1` (`vIdx ≠ 0`) at prover positions
`pIdx = FAEST.xorIndex i hidden`, matching `FAEST.verifierRows` (`0` at position `0`). -/
@[expose] def collectOpenRows {d sdLen comLen rowLen : ℕ} {Seed IV : Type}
    (expand : BitString sdLen → BitString rowLen)
    (iv : IV) (openKeys : Fin (2 ^ d) → Seed) (coms : Fin (2 ^ d) → BitString comLen)
    (hidden : Fin (2 ^ d)) :
    (k : ℕ) → k ≤ 2 ^ d →
    OracleComp (VOLEITHLeafSpec d sdLen comLen Seed IV) (Option (Fin (2 ^ d) → BitString rowLen))
  | 0, _ => pure (some (fun _ => 0))
  | k + 1, hk => do
    let vIdx : Fin (2 ^ d) := ⟨k, hk⟩
    let rest ← collectOpenRows expand iv openKeys coms hidden k (Nat.le_of_lt hk)
    if vIdx = 0 then
      pure rest
    else do
      let pIdx := FAEST.xorIndex vIdx hidden
      let out ← OracleComp.query ⟨openKeys pIdx, iv, pIdx⟩
      if out.com = coms pIdx then
        pure (rest.map fun rows => Function.update rows vIdx (expand out.seedOut))
      else
        pure none

private theorem isCostBounded_collectOpenRows {d sdLen comLen rowLen : ℕ} {Seed IV : Type}
    (expand : BitString sdLen → BitString rowLen)
    (iv : IV) (openKeys : Fin (2 ^ d) → Seed) (coms : Fin (2 ^ d) → BitString comLen)
    (hidden : Fin (2 ^ d)) (k : ℕ) (hk : k ≤ 2 ^ d) :
    (collectOpenRows expand iv openKeys coms hidden k hk).IsQueryBounded (k - 1) := by
  induction k with
  | zero => exact IsCostBounded.pure _ 0
  | succ k ih =>
    unfold collectOpenRows
    by_cases hk0 : (⟨k, hk⟩ : Fin (2 ^ d)) = 0
    · have hk_eq : k = 0 := congrArg Fin.val hk0
      subst hk_eq
      simpa only [Nat.zero_sub, Nat.zero_add, hk0, ↓reduceIte] using
        (ih (Nat.le_of_lt hk)).bind fun rest => IsCostBounded.pure rest 0
    · have hkne : k ≠ 0 := fun h => hk0 (Fin.ext h)
      have hsub : k + 1 - 1 = (k - 1) + 1 := by omega
      rw [hsub]
      refine (ih (Nat.le_of_lt hk)).bind fun rest => ?_
      simp only [hk0, ↓reduceIte]
      rw [← Nat.add_zero 1]
      refine (IsCostBounded.query (spec := VOLEITHLeafSpec d sdLen comLen Seed IV) _).bind
        fun out => ?_
      split_ifs <;> exact IsCostBounded.pure _ 0

/-- `collectOpenRows` at full width `2 ^ d` makes at most `2 ^ d - 1` `H_leaf` queries. -/
theorem isQueryBounded_collectOpenRows {d sdLen comLen rowLen : ℕ} {Seed IV : Type}
    (expand : BitString sdLen → BitString rowLen)
    (iv : IV) (openKeys : Fin (2 ^ d) → Seed) (coms : Fin (2 ^ d) → BitString comLen)
    (hidden : Fin (2 ^ d)) :
    (collectOpenRows expand iv openKeys coms hidden (2 ^ d) le_rfl).IsQueryBounded
      (2 ^ d - 1) :=
  isCostBounded_collectOpenRows expand iv openKeys coms hidden (2 ^ d) le_rfl

/-- VOLEitH verifier in the two-channel ROM (`VOLEITHROSpec`): queries `H_FS` on `prf.fsQuery stmt`
to draw `Δ`, opens the `2 ^ d - 1` non-hidden leaves via `collectOpenRows`, runs
`FAEST.convertExpandedRows` to compute `qCols`, and evaluates `checkRel`. -/
@[expose] def voleithVerifyROM {d sdLen comLen rowLen : ℕ} {Stmt Seed IV PreMsg Chal : Type}
    (expand : BitString sdLen → BitString rowLen)
    (chalToIdx : Chal → Fin (2 ^ d))
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (stmt : Stmt) (prf : VOLEITHProof d comLen rowLen Seed IV PreMsg) :
    ProbOracleComp (VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) Bool := do
  let delta ← OracleComp.liftRight (spec₁ := unifSpec)
    (OracleComp.liftRight (spec₁ := VOLEITHLeafSpec d sdLen comLen Seed IV)
      (OracleComp.query (prf.fsQuery stmt)))
  let hidden := chalToIdx delta
  let vRows ← OracleComp.liftRight (spec₁ := unifSpec)
    (OracleComp.liftLeft (spec₂ := VOLEITHFSSpec d comLen rowLen Stmt IV PreMsg Chal)
      (collectOpenRows expand prf.iv prf.openKeys prf.coms hidden (2 ^ d) le_rfl))
  match vRows with
  | none => return false
  | some rows =>
    let qCols := (FAEST.convertExpandedRows d rows).columns
    return checkRel stmt qCols prf.dCorr prf.preMsg delta

theorem isCostBounded_leaf_voleithVerifyROM {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal : Type}
    (expand : BitString sdLen → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (stmt : Stmt) (prf : VOLEITHProof d comLen rowLen Seed IV PreMsg) :
    IsCostBounded (Sum.elim (fun _ => 0) (voleithLeafCost (Stmt := Stmt) (PreMsg := PreMsg)))
      (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel stmt prf) (2 ^ d - 1) := by
  unfold voleithVerifyROM
  have hz : IsCostBounded
      (Sum.elim (fun _ => 0) (voleithLeafCost (Stmt := Stmt) (PreMsg := PreMsg)))
      (OracleComp.liftRight (spec₁ := unifSpec)
        (OracleComp.liftRight (spec₁ := VOLEITHLeafSpec d sdLen comLen Seed IV)
          (OracleComp.query (prf.fsQuery stmt))) :
        ProbOracleComp (VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) Chal) 0 := by
    refine IsCostBounded.liftRight
      (IsCostBounded.liftRight_of_cost_inr_eq_zero (fun _ => rfl) _)
      (fun _ => le_rfl)
  rw [← Nat.zero_add (2 ^ d - 1)]
  refine hz.bind fun delta => ?_
  have hleft : IsCostBounded
      (Sum.elim (fun _ => 0) (voleithLeafCost (Stmt := Stmt) (PreMsg := PreMsg)))
      (OracleComp.liftRight (spec₁ := unifSpec)
        (OracleComp.liftLeft (spec₂ := VOLEITHFSSpec d comLen rowLen Stmt IV PreMsg Chal)
          (collectOpenRows expand prf.iv prf.openKeys prf.coms (chalToIdx delta)
            (2 ^ d) le_rfl)))
      (2 ^ d - 1) := by
    refine IsCostBounded.liftRight
      ((isQueryBounded_collectOpenRows expand prf.iv prf.openKeys prf.coms _).liftLeft
        fun _ => le_rfl)
      (fun _ => le_rfl)
  rw [← Nat.add_zero (2 ^ d - 1)]
  refine hleft.bind fun vRows => ?_
  cases vRows <;> exact IsCostBounded.pure _ 0

theorem isCostBounded_fs_voleithVerifyROM {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal : Type}
    (expand : BitString sdLen → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (stmt : Stmt) (prf : VOLEITHProof d comLen rowLen Seed IV PreMsg) :
    IsCostBounded (Sum.elim (fun _ => 0) (voleithFSCost (Stmt := Stmt) (PreMsg := PreMsg)))
      (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel stmt prf) 1 := by
  unfold voleithVerifyROM
  have hq : IsCostBounded
      (Sum.elim (fun _ => 0) (voleithFSCost (Stmt := Stmt) (PreMsg := PreMsg)))
      (OracleComp.liftRight (spec₁ := unifSpec)
        (OracleComp.liftRight (spec₁ := VOLEITHLeafSpec d sdLen comLen Seed IV)
          (OracleComp.query (prf.fsQuery stmt))) :
        ProbOracleComp (VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) Chal) 1 := by
    refine IsCostBounded.liftRight
      (IsCostBounded.liftRight (IsCostBounded.query _) fun _ => le_rfl)
      (fun _ => le_rfl)
  rw [← Nat.add_zero 1]
  refine hq.bind fun delta => ?_
  have hz : IsCostBounded
      (Sum.elim (fun _ => 0) (voleithFSCost (Stmt := Stmt) (PreMsg := PreMsg)))
      (OracleComp.liftRight (spec₁ := unifSpec)
        (OracleComp.liftLeft (spec₂ := VOLEITHFSSpec d comLen rowLen Stmt IV PreMsg Chal)
          (collectOpenRows expand prf.iv prf.openKeys prf.coms (chalToIdx delta)
            (2 ^ d) le_rfl))) 0 := by
    refine IsCostBounded.liftRight
      (IsCostBounded.liftLeft_of_cost_inl_eq_zero (fun _ => rfl) _)
      (fun _ => le_rfl)
  rw [← Nat.zero_add 0]
  refine hz.bind fun vRows => ?_
  cases vRows <;> exact IsCostBounded.pure _ 0

/-- Look up a `leaf_hash::shake` leaf query `(k, iv, idx) ↦ (sd, com)` in `tr_leaf` matching
`iv`, `idx`, and target commitment `coms idx`. -/
@[expose] def extractLeafFromTrace {d sdLen comLen : ℕ} {Seed IV : Type} [DecidableEq IV]
    (tr : LeafTrace d sdLen comLen Seed IV) (iv : IV)
    (coms : Fin (2 ^ d) → BitString comLen) (idx : Fin (2 ^ d)) :
    Option (Seed × BitString sdLen) :=
  (tr.find? fun e => decide (e.1.iv = iv ∧ e.1.index = idx ∧ e.2.com = coms idx)).map
    fun e => (e.1.seed, e.2.seedOut)

/-- Straight-line extraction of all `2 ^ d` expanded VOLE rows from `tr_leaf` using `expand`,
defaulting unqueried leaves to `0`. -/
@[expose] def extractRowsFromTrace {d sdLen comLen rowLen : ℕ} {Seed IV : Type} [DecidableEq IV]
    (expand : BitString sdLen → BitString rowLen)
    (tr : LeafTrace d sdLen comLen Seed IV) (iv : IV)
    (coms : Fin (2 ^ d) → BitString comLen) :
    Fin (2 ^ d) → BitString rowLen :=
  fun idx => (extractLeafFromTrace tr iv coms idx).elim 0 (fun p => expand p.2)

/-- Straight-line extraction of the binary VOLE `(u, v₀, ..., v_{d-1})` conversion from
`tr_leaf` using `FAEST.convertExpandedRows`. -/
@[expose] def extractVOLEFromTrace {d sdLen comLen rowLen : ℕ} {Seed IV : Type} [DecidableEq IV]
    (expand : BitString sdLen → BitString rowLen)
    (tr : LeafTrace d sdLen comLen Seed IV) (iv : IV)
    (coms : Fin (2 ^ d) → BitString comLen) :
    FAEST.Conversion d rowLen :=
  FAEST.convertExpandedRows d (extractRowsFromTrace expand tr iv coms)

/-- Zero-rewinding straight-line witness extractor: reads ONLY `tr_leaf` and `prf`, recovering
`decWit (prf.dCorr + u)`. -/
@[expose] def extractWitnessFromTrace {d sdLen comLen rowLen : ℕ} {Seed IV PreMsg Wit : Type}
    [DecidableEq IV]
    (expand : BitString sdLen → BitString rowLen)
    (decWit : BitString rowLen → Wit)
    (tr : LeafTrace d sdLen comLen Seed IV) (prf : VOLEITHProof d comLen rowLen Seed IV PreMsg) :
    Wit :=
  decWit (prf.dCorr + (extractVOLEFromTrace expand tr prf.iv prf.coms).u)

/-- Every trace-extracted row vector induces valid binary `VOLECorrelation` columns via
`FAEST.conversionCorrelation` ([BaumEtAl2026FAEST], Section 5.4 Proposition 5.2). -/
theorem extractRowsFromTrace_conversionCorrelation_valid {d sdLen comLen rowLen : ℕ}
    {Seed IV : Type} [DecidableEq IV]
    (expand : BitString sdLen → BitString rowLen)
    (tr : LeafTrace d sdLen comLen Seed IV) (iv : IV)
    (coms : Fin (2 ^ d) → BitString comLen) (hidden : Fin (2 ^ d)) (j : Fin d) :
    (FAEST.conversionCorrelation (extractRowsFromTrace expand tr iv coms) hidden j).Valid :=
  FAEST.conversionCorrelation_valid _ hidden j

private theorem xorIndex_ne_right {d : ℕ} {i hidden : Fin (2 ^ d)} (hi : i ≠ 0) :
    FAEST.xorIndex i hidden ≠ hidden := by
  intro h
  apply hi
  apply Fin.ext
  have hv : i.val ^^^ hidden.val = hidden.val := congrArg Fin.val h
  calc
    i.val = (i.val ^^^ hidden.val) ^^^ hidden.val := by
      rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    _ = hidden.val ^^^ hidden.val := by rw [hv]
    _ = 0 := Nat.xor_self _

/-- When every non-hidden leaf `(openKeys idx, iv, idx)` is already memoized in `tr₁` with the
matching commitment `coms idx` and expanded row `rows idx`, `collectOpenRows` hits only the leaf
cache and returns `FAEST.verifierRows rows hidden` without modifying the ROM trace. -/
private theorem collectOpenRows_of_trace {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen)
    (iv : IV) (openKeys : Fin (2 ^ d) → Seed) (coms : Fin (2 ^ d) → BitString comLen)
    (rows : Fin (2 ^ d) → BitString rowLen) (hidden : Fin (2 ^ d))
    (tr₁ : LeafTrace d sdLen comLen Seed IV) (tr₂ : FSTrace d comLen rowLen Stmt IV PreMsg Chal)
    (htr : ∀ idx : Fin (2 ^ d), idx ≠ hidden →
      ∃ out, tr₁.lookup ⟨openKeys idx, iv, idx⟩ = some out ∧
        out.com = coms idx ∧ expand out.seedOut = rows idx) :
    ∀ (k : ℕ) (hk : k ≤ 2 ^ d),
      (OracleComp.interpret
        (voleithMemoize (d := d) (sdLen := sdLen) (comLen := comLen) (rowLen := rowLen)
          (Stmt := Stmt) (Seed := Seed) (IV := IV) (PreMsg := PreMsg) (Chal := Chal))
        (OracleComp.liftLeft (spec₂ := VOLEITHFSSpec d comLen rowLen Stmt IV PreMsg Chal)
          (collectOpenRows expand iv openKeys coms hidden k hk))).run (tr₁, tr₂) =
        PMF.pure
          (some (fun i : Fin (2 ^ d) =>
            if (i : ℕ) < k then FAEST.verifierRows rows hidden i else 0),
            (tr₁, tr₂)) := by
  intro k hk
  induction k with
  | zero =>
    simp [collectOpenRows, OracleComp.liftLeft_pure, PMF.monad_pure_eq_pure]
  | succ k ih =>
    unfold collectOpenRows
    rw [OracleComp.liftLeft_bind, OracleComp.run_interpret_bind, ih (Nat.le_of_lt hk),
      PMF.monad_bind_eq_bind, PMF.pure_bind]
    by_cases hk0 : (⟨k, hk⟩ : Fin (2 ^ d)) = 0
    · have hk_eq : k = 0 := congrArg Fin.val hk0
      subst hk_eq
      simp only [hk0, ↓reduceIte, OracleComp.liftLeft_pure, OracleComp.run_interpret_pure,
        PMF.monad_pure_eq_pure]
      refine congrArg (fun f => PMF.pure (some f, (tr₁, tr₂))) ?_
      funext i
      by_cases hi : (i : ℕ) < 1
      · have hi0 : i = 0 := by
          apply Fin.ext
          simp only [Fin.val_zero]
          omega
        subst hi0
        simp [FAEST.verifierRows]
      · simp [hi]
    · simp only [hk0, ↓reduceIte, OracleComp.liftLeft_bind, OracleComp.liftLeft_query,
        OracleComp.run_interpret_bind, OracleComp.run_interpret_query,
        voleithMemoize, RandomOracle.memoizeSum_inl]
      set pIdx := FAEST.xorIndex ⟨k, hk⟩ hidden
      have hpne : pIdx ≠ hidden := xorIndex_ne_right hk0
      obtain ⟨out, hlook, hcom, hrow⟩ := htr pIdx hpne
      have hmem :
          Cslib.memoize (fun _ : LeafQuery d Seed IV =>
            PMF.uniformOfFintype (LeafOutput sdLen comLen))
            ⟨openKeys pIdx, iv, pIdx⟩ tr₁ = PMF.pure (out, tr₁) := by
        simp [Cslib.memoize, hlook, PMF.monad_pure_eq_pure]
      rw [hmem, PMF.pure_map, PMF.monad_bind_eq_bind, PMF.pure_bind]
      simp only [hcom, ↓reduceIte, OracleComp.liftLeft_pure, OracleComp.run_interpret_pure,
        PMF.monad_pure_eq_pure]
      refine congrArg (fun f => PMF.pure (some f, (tr₁, tr₂))) ?_
      funext i
      by_cases hik : i = ⟨k, hk⟩
      · subst hik
        simp [pIdx, FAEST.verifierRows, hk0, hrow]
      · have hne_val : (i : ℕ) ≠ k := fun h => hik (Fin.ext h)
        have hlt_iff : ((i : ℕ) < k + 1) ↔ ((i : ℕ) < k) := by omega
        simp [Function.update, hik, hlt_iff]

/-- Query `H_leaf` across all `k` leaves `0, ..., k - 1` under fresh `keys`, returning the
expanded rows `rows` and leaf commitment digests `coms`. -/
@[expose] def honestCommitLeaves {d sdLen comLen rowLen : ℕ} {Seed IV : Type}
    (expand : BitString sdLen → BitString rowLen)
    (iv : IV) (keys : Fin (2 ^ d) → Seed) :
    (k : ℕ) → k ≤ 2 ^ d →
    OracleComp (VOLEITHLeafSpec d sdLen comLen Seed IV)
      ((Fin (2 ^ d) → BitString rowLen) × (Fin (2 ^ d) → BitString comLen))
  | 0, _ => pure (fun _ => 0, fun _ => 0)
  | k + 1, hk => do
    let (rows, coms) ← honestCommitLeaves expand iv keys k (Nat.le_of_lt hk)
    let idx : Fin (2 ^ d) := ⟨k, hk⟩
    let out ← OracleComp.query ⟨keys idx, iv, idx⟩
    return (Function.update rows idx (expand out.seedOut), Function.update coms idx out.com)

/-- Leaf-and-FS oracle program for the honest `leaf_hash::shake` prover: commits all `2 ^ d` leaves
via `H_leaf`, masks the witness with `conv.u`, queries `H_FS` on `(stmt, iv, coms, dCorr, preMsg)`,
and outputs `openKeys` for all `idx ≠ hidden`. -/
@[expose] def voleithProveLeafFS {d sdLen comLen rowLen : ℕ} {Stmt Seed IV PreMsg Chal Wit : Type}
    (expand : BitString sdLen → BitString rowLen)
    (encWit : Wit → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (mkPreMsg : (Fin d → BitString rowLen) → BitString rowLen → BitString rowLen → PreMsg)
    (defaultSeed : Seed) (iv : IV) (keys : Fin (2 ^ d) → Seed) (stmt : Stmt) (w : Wit) :
    OracleComp (VOLEITHLeafSpec d sdLen comLen Seed IV ⊕ₒ
      VOLEITHFSSpec d comLen rowLen Stmt IV PreMsg Chal)
      (VOLEITHProof d comLen rowLen Seed IV PreMsg) := do
  let (rows, coms) ← OracleComp.liftLeft
    (honestCommitLeaves expand iv keys (2 ^ d) le_rfl)
  let conv := FAEST.convertExpandedRows d rows
  let dCorr := encWit w + conv.u
  let preMsg := mkPreMsg conv.columns conv.u dCorr
  let delta ← OracleComp.liftRight (OracleComp.query ⟨stmt, iv, coms, dCorr, preMsg⟩)
  let hidden := chalToIdx delta
  let openKeys : Fin (2 ^ d) → Seed := fun idx => if idx = hidden then defaultSeed else keys idx
  return ⟨iv, coms, dCorr, preMsg, openKeys⟩

/-- Honest `leaf_hash::shake` prover in `VOLEITHROSpec`. -/
@[expose] def voleithProveROM {d sdLen comLen rowLen : ℕ} {Stmt Seed IV PreMsg Chal Wit : Type}
    (expand : BitString sdLen → BitString rowLen)
    (encWit : Wit → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (mkPreMsg : (Fin d → BitString rowLen) → BitString rowLen → BitString rowLen → PreMsg)
    (defaultSeed : Seed) (iv : IV) (keys : Fin (2 ^ d) → Seed) (stmt : Stmt) (w : Wit) :
    ProbOracleComp (VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal)
      (VOLEITHProof d comLen rowLen Seed IV PreMsg) :=
  OracleComp.liftRight (spec₁ := unifSpec)
    (voleithProveLeafFS expand encWit chalToIdx mkPreMsg defaultSeed iv keys stmt w)

/-- `honestCommitLeaves` makes exactly `k` `H_leaf` queries. -/
theorem isCostBounded_honestCommitLeaves {d sdLen comLen rowLen : ℕ} {Seed IV : Type}
    (expand : BitString sdLen → BitString rowLen) (iv : IV) (keys : Fin (2 ^ d) → Seed) :
    ∀ (k : ℕ) (hk : k ≤ 2 ^ d),
      IsCostBounded (fun _ : LeafQuery d Seed IV => 1)
        (honestCommitLeaves (comLen := comLen) expand iv keys k hk) k
  | 0, _ => OracleComp.IsCostBounded.pure _ 0
  | k + 1, hk => by
    unfold honestCommitLeaves
    refine (isCostBounded_honestCommitLeaves expand iv keys k (Nat.le_of_lt hk)).bind
      fun _ => ?_
    rw [show (1 : ℕ) = 1 + 0 from rfl]
    exact (OracleComp.IsCostBounded.query (spec := VOLEITHLeafSpec d sdLen comLen Seed IV)
      ⟨keys ⟨k, hk⟩, iv, ⟨k, hk⟩⟩).bind fun _ => OracleComp.IsCostBounded.pure _ 0

/-- `voleithProveLeafFS` makes at most `2 ^ d` `H_leaf` queries. -/
theorem isCostBounded_leaf_voleithProveLeafFS {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit : Type}
    (expand : BitString sdLen → BitString rowLen)
    (encWit : Wit → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (mkPreMsg : (Fin d → BitString rowLen) → BitString rowLen → BitString rowLen → PreMsg)
    (defaultSeed : Seed) (iv : IV) (keys : Fin (2 ^ d) → Seed) (stmt : Stmt) (w : Wit) :
    IsCostBounded (voleithLeafCost (Stmt := Stmt) (PreMsg := PreMsg))
      (voleithProveLeafFS expand encWit chalToIdx mkPreMsg defaultSeed iv keys stmt w :
        OracleComp (VOLEITHLeafSpec d sdLen comLen Seed IV ⊕ₒ
          VOLEITHFSSpec d comLen rowLen Stmt IV PreMsg Chal)
          (VOLEITHProof d comLen rowLen Seed IV PreMsg))
      (2 ^ d) := by
  unfold voleithProveLeafFS
  change IsCostBounded _ _ (2 ^ d + 0)
  refine ((isCostBounded_honestCommitLeaves expand iv keys (2 ^ d) le_rfl).liftLeft
    fun _ => le_rfl).bind fun _ => ?_
  change IsCostBounded _ _ (0 + 0)
  exact (IsCostBounded.liftRight_of_cost_inr_eq_zero (fun _ => rfl) _).bind fun _ =>
    IsCostBounded.pure _ 0

/-- `voleithProveLeafFS` makes at most `1` `H_FS` query. -/
theorem isCostBounded_fs_voleithProveLeafFS {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit : Type}
    (expand : BitString sdLen → BitString rowLen)
    (encWit : Wit → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (mkPreMsg : (Fin d → BitString rowLen) → BitString rowLen → BitString rowLen → PreMsg)
    (defaultSeed : Seed) (iv : IV) (keys : Fin (2 ^ d) → Seed) (stmt : Stmt) (w : Wit) :
    IsCostBounded (voleithFSCost (Stmt := Stmt) (PreMsg := PreMsg))
      (voleithProveLeafFS expand encWit chalToIdx mkPreMsg defaultSeed iv keys stmt w :
        OracleComp (VOLEITHLeafSpec d sdLen comLen Seed IV ⊕ₒ
          VOLEITHFSSpec d comLen rowLen Stmt IV PreMsg Chal)
          (VOLEITHProof d comLen rowLen Seed IV PreMsg))
      1 := by
  unfold voleithProveLeafFS
  change IsCostBounded _ _ (0 + 1)
  refine (IsCostBounded.liftLeft_of_cost_inl_eq_zero (fun _ => rfl) _).bind fun _ => ?_
  change IsCostBounded _ _ (1 + 0)
  exact (IsCostBounded.liftRight (IsCostBounded.query _) fun _ => le_rfl).bind fun _ =>
    IsCostBounded.pure _ 0

/-- Honest prover-then-verifier execution in `VOLEITHROSpec`. -/
@[expose] def voleithHonestGame {d sdLen comLen rowLen : ℕ} {Stmt Seed IV PreMsg Chal Wit : Type}
    (expand : BitString sdLen → BitString rowLen)
    (encWit : Wit → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (mkPreMsg : (Fin d → BitString rowLen) → BitString rowLen → BitString rowLen → PreMsg)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (defaultSeed : Seed) (iv : IV) (keys : Fin (2 ^ d) → Seed) (stmt : Stmt) (w : Wit) :
    ProbOracleComp (VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) Bool := do
  let prf ← voleithProveROM expand encWit chalToIdx mkPreMsg defaultSeed iv keys stmt w
  voleithVerifyROM expand chalToIdx checkRel stmt prf

private theorem honestCommitLeaves_trace_invariant {d sdLen comLen rowLen : ℕ}
    {Seed IV : Type} [BEq (LeafQuery d Seed IV)] [LawfulBEq (LeafQuery d Seed IV)]
    (expand : BitString sdLen → BitString rowLen)
    (iv : IV) (keys : Fin (2 ^ d) → Seed) (tr₁₀ : LeafTrace d sdLen comLen Seed IV)
    (hiv₁₀ : ∀ e ∈ tr₁₀, e.1.iv ≠ iv) :
    ∀ (k : ℕ) (hk : k ≤ 2 ^ d)
      (rows : Fin (2 ^ d) → BitString rowLen) (coms : Fin (2 ^ d) → BitString comLen)
      (tr₁ : LeafTrace d sdLen comLen Seed IV),
      ((rows, coms), tr₁) ∈
        ((OracleComp.interpret
          (Cslib.memoize (fun _ : LeafQuery d Seed IV =>
            PMF.uniformOfFintype (LeafOutput sdLen comLen)))
          (honestCommitLeaves expand iv keys k hk)).run tr₁₀).support →
      (∀ idx : Fin (2 ^ d), (idx : ℕ) < k →
        ∃ out, tr₁.lookup ⟨keys idx, iv, idx⟩ = some out ∧
          out.com = coms idx ∧ expand out.seedOut = rows idx) ∧
      (∀ e ∈ tr₁, (e.1.iv = iv ∧ (e.1.index : ℕ) < k) ∨ e ∈ tr₁₀) := by
  intro k
  induction k with
  | zero =>
    intro hk rows coms tr₁ hsupp
    simp only [honestCommitLeaves, OracleComp.run_interpret_pure, PMF.monad_pure_eq_pure,
      PMF.mem_support_pure_iff, Prod.mk.injEq] at hsupp
    obtain ⟨_, rfl⟩ := hsupp
    exact ⟨fun idx hlt => absurd hlt (Nat.not_lt_zero _), fun e he => Or.inr he⟩
  | succ k ih =>
    intro hk rows coms tr₁ hsupp
    unfold honestCommitLeaves at hsupp
    rw [OracleComp.run_interpret_bind, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hsupp
    obtain ⟨⟨⟨rows₀, coms₀⟩, tr₀⟩, hsupp₀, hsupp₁⟩ := hsupp
    obtain ⟨hlook₀, hbound₀⟩ := ih (Nat.le_of_lt hk) rows₀ coms₀ tr₀ hsupp₀
    rw [OracleComp.run_interpret_bind, OracleComp.run_interpret_query,
      PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hsupp₁
    obtain ⟨⟨out, tr_next⟩, hmem_out, hpure⟩ := hsupp₁
    simp only [OracleComp.run_interpret_pure, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff,
      Prod.mk.injEq] at hpure
    obtain ⟨hrc, htr_eq⟩ := hpure
    obtain ⟨rfl, rfl⟩ := hrc
    dsimp only at htr_eq hmem_out
    have hnone : tr₀.lookup ⟨keys ⟨k, hk⟩, iv, ⟨k, hk⟩⟩ = none := by
      cases h : tr₀.lookup ⟨keys ⟨k, hk⟩, iv, ⟨k, hk⟩⟩ with
      | none => rfl
      | some v =>
        obtain ⟨before, after, heq⟩ := List.lookup_eq_some_iff.mp h
        have hkmem : (⟨keys ⟨k, hk⟩, iv, ⟨k, hk⟩⟩, v) ∈ tr₀ := by simp [heq.1]
        rcases hbound₀ _ hkmem with ⟨_, hlt⟩ | hmem₁₀
        · dsimp only at hlt
          omega
        · exact absurd rfl (hiv₁₀ _ hmem₁₀)
    rw [RandomOracle.mem_support_memoize_iff] at hmem_out
    rcases hmem_out with ⟨hsome, _⟩ | ⟨_, _, htr_cons⟩
    · simp [hnone] at hsome
    · dsimp only at htr_cons
      rw [htr_eq, htr_cons]
      constructor
      · intro idx hlt
        by_cases hik : idx = ⟨k, hk⟩
        · subst hik
          refine ⟨out, ?_, by simp, by simp⟩
          simp
        · have hlt' : (idx : ℕ) < k := by
            have : (idx : ℕ) ≠ k := fun h => hik (Fin.ext h)
            omega
          obtain ⟨out', hlook', hcom', hrow'⟩ := hlook₀ idx hlt'
          have hqne : ((⟨keys idx, iv, idx⟩ : LeafQuery d Seed IV) ==
              (⟨keys ⟨k, hk⟩, iv, ⟨k, hk⟩⟩ : LeafQuery d Seed IV)) = false := by
            apply beq_false_of_ne
            intro heq
            exact hik (congrArg LeafQuery.index heq)
          refine ⟨out', ?_, by simp [Function.update, hik, hcom'],
            by simp [Function.update, hik, hrow']⟩
          simp [List.lookup_cons, hqne, hlook']
      · intro e he
        simp only [List.mem_cons] at he
        rcases he with rfl | he₀
        · exact Or.inl ⟨rfl, Nat.lt_succ_self k⟩
        · rcases hbound₀ e he₀ with ⟨hiv, hlt⟩ | hmem₁₀
          · exact Or.inl ⟨hiv, Nat.lt_succ_of_lt hlt⟩
          · exact Or.inr hmem₁₀

/-- Generalized completeness of `voleithProveLeafFS` followed by `voleithVerifyROM` from any ROM
trace `st₀` free of prior queries tagged with `iv`. Every generated proof verifies to `true`
without modifying `st_mid`, and all newly added trace entries carry `iv`. -/
theorem voleithProveLeafFS_verify_of_fresh {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit : Type}
    [BEq (LeafQuery d Seed IV)] [LawfulBEq (LeafQuery d Seed IV)]
    [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [LawfulBEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen)
    (encWit : Wit → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (mkPreMsg : (Fin d → BitString rowLen) → BitString rowLen → BitString rowLen → PreMsg)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (defaultSeed : Seed) (iv : IV) (keys : Fin (2 ^ d) → Seed) (stmt : Stmt) (w : Wit)
    (hRel : ∀ (pCols : Fin d → BitString rowLen) (u : BitString rowLen) (delta : Chal),
      checkRel stmt
        (fun j => pCols j + fun k => (BitString.equivFin d).symm (chalToIdx delta) j * u k)
        (encWit w + u) (mkPreMsg pCols u (encWit w + u)) delta = true)
    (st₀ : VOLEITHTraceState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal)
    (hiv₁ : ∀ e ∈ st₀.1, e.1.iv ≠ iv) (hiv₂ : ∀ e ∈ st₀.2, e.1.iv ≠ iv)
    {prf : VOLEITHProof d comLen rowLen Seed IV PreMsg}
    {st_mid : VOLEITHTraceState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal}
    (hprove : (prf, st_mid) ∈
      ((OracleComp.interpret
        (voleithMemoize (d := d) (sdLen := sdLen) (comLen := comLen) (rowLen := rowLen)
          (Stmt := Stmt) (Seed := Seed) (IV := IV) (PreMsg := PreMsg) (Chal := Chal))
        (voleithProveLeafFS expand encWit chalToIdx mkPreMsg defaultSeed iv keys stmt w)).run
        st₀).support) :
    ProbOracleComp.runWith
        (voleithMemoize (d := d) (sdLen := sdLen) (comLen := comLen) (rowLen := rowLen)
          (Stmt := Stmt) (Seed := Seed) (IV := IV) (PreMsg := PreMsg) (Chal := Chal))
        (voleithVerifyROM expand chalToIdx checkRel stmt prf) st_mid =
      PMF.pure (true, st_mid) ∧
    (∀ e ∈ st_mid.1, e.1.iv = iv ∨ e ∈ st₀.1) ∧
    (∀ e ∈ st_mid.2, e.1.iv = iv ∨ e ∈ st₀.2) := by
  rcases st₀ with ⟨tr₁₀, tr₂₀⟩
  unfold voleithProveLeafFS at hprove
  rw [OracleComp.run_interpret_bind] at hprove
  change (prf, st_mid) ∈ (PMF.bind _ _).support at hprove
  rw [PMF.mem_support_bind_iff] at hprove
  obtain ⟨⟨⟨rows, coms⟩, st_leaf⟩, hleaf, hfs⟩ := hprove
  rw [voleithMemoize, RandomOracle.run_interpret_memoizeSum_liftLeft,
    PMF.mem_support_map_iff] at hleaf
  obtain ⟨⟨rc, tr₁⟩, hleaf_supp, hrc_eq⟩ := hleaf
  cases hrc_eq
  obtain ⟨hlook₁, hbound₁⟩ := honestCommitLeaves_trace_invariant expand iv keys tr₁₀ hiv₁
    (2 ^ d) le_rfl rows coms tr₁ hleaf_supp
  rw [OracleComp.run_interpret_bind, OracleComp.liftRight_query,
    OracleComp.run_interpret_query, voleithMemoize, RandomOracle.memoizeSum_inr] at hfs
  change (prf, st_mid) ∈ (PMF.bind _ _).support at hfs
  rw [PMF.mem_support_bind_iff] at hfs
  obtain ⟨⟨delta, tr₂'⟩, hfs_mem, hprf_pure⟩ := hfs
  rw [PMF.mem_support_map_iff] at hfs_mem
  obtain ⟨⟨delta₀, tr₂_inner⟩, hmemo_fs, hpair_eq⟩ := hfs_mem
  cases hpair_eq
  have hnone₂ : tr₂₀.lookup
      ⟨stmt, iv, coms, encWit w + (FAEST.convertExpandedRows d rows).u,
        mkPreMsg (FAEST.convertExpandedRows d rows).columns
          (FAEST.convertExpandedRows d rows).u
          (encWit w + (FAEST.convertExpandedRows d rows).u)⟩ = none := by
    cases h : tr₂₀.lookup
        ⟨stmt, iv, coms, encWit w + (FAEST.convertExpandedRows d rows).u,
          mkPreMsg (FAEST.convertExpandedRows d rows).columns
            (FAEST.convertExpandedRows d rows).u
            (encWit w + (FAEST.convertExpandedRows d rows).u)⟩ with
    | none => rfl
    | some v =>
      obtain ⟨before, after, heq⟩ := List.lookup_eq_some_iff.mp h
      have hmem : (⟨stmt, iv, coms, encWit w + (FAEST.convertExpandedRows d rows).u,
          mkPreMsg (FAEST.convertExpandedRows d rows).columns
            (FAEST.convertExpandedRows d rows).u
            (encWit w + (FAEST.convertExpandedRows d rows).u)⟩, v) ∈ tr₂₀ := by
        simp [heq.1]
      exact absurd rfl (hiv₂ _ hmem)
  rw [RandomOracle.mem_support_memoize_iff] at hmemo_fs
  rcases hmemo_fs with ⟨hsome, _⟩ | ⟨_, _, htr₂_eq⟩
  · simp [hnone₂] at hsome
  · dsimp only at htr₂_eq
    rw [htr₂_eq] at hprf_pure
    simp only [OracleComp.run_interpret_pure, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff,
      Prod.mk.injEq] at hprf_pure
    obtain ⟨rfl, rfl⟩ := hprf_pure
    refine ⟨?_, ?_, ?_⟩
    · unfold voleithVerifyROM
      rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith,
        OracleComp.runWith_sumHandler_liftRight, OracleComp.runWith_eq_run_interpret,
        OracleComp.liftRight_query, OracleComp.run_interpret_query, voleithMemoize,
        RandomOracle.memoizeSum_inr]
      have hmemo_v :
          Cslib.memoize (fun _ : FSQuery d comLen rowLen Stmt IV PreMsg =>
            PMF.uniformOfFintype Chal)
            ⟨stmt, iv, coms, encWit w + (FAEST.convertExpandedRows d rows).u,
              mkPreMsg (FAEST.convertExpandedRows d rows).columns
                (FAEST.convertExpandedRows d rows).u
                (encWit w + (FAEST.convertExpandedRows d rows).u)⟩
            ((⟨stmt, iv, coms, encWit w + (FAEST.convertExpandedRows d rows).u,
              mkPreMsg (FAEST.convertExpandedRows d rows).columns
                (FAEST.convertExpandedRows d rows).u
                (encWit w + (FAEST.convertExpandedRows d rows).u)⟩, delta) :: tr₂₀) =
          PMF.pure (delta,
            ((⟨stmt, iv, coms, encWit w + (FAEST.convertExpandedRows d rows).u,
              mkPreMsg (FAEST.convertExpandedRows d rows).columns
                (FAEST.convertExpandedRows d rows).u
                (encWit w + (FAEST.convertExpandedRows d rows).u)⟩, delta) :: tr₂₀)) := by
        simp [Cslib.memoize, PMF.monad_pure_eq_pure]
      have hmemo_v' :
          Cslib.memoize (fun _ : FSQuery d comLen rowLen Stmt IV PreMsg =>
            PMF.uniformOfFintype Chal)
            (VOLEITHProof.fsQuery stmt
              (⟨iv, coms, encWit w + (FAEST.convertExpandedRows d rows).u,
                mkPreMsg (FAEST.convertExpandedRows d rows).columns
                  (FAEST.convertExpandedRows d rows).u
                  (encWit w + (FAEST.convertExpandedRows d rows).u),
                fun idx => if idx = chalToIdx delta then defaultSeed else keys idx⟩ :
                VOLEITHProof d comLen rowLen Seed IV PreMsg))
            ((⟨stmt, iv, coms, encWit w + (FAEST.convertExpandedRows d rows).u,
              mkPreMsg (FAEST.convertExpandedRows d rows).columns
                (FAEST.convertExpandedRows d rows).u
                (encWit w + (FAEST.convertExpandedRows d rows).u)⟩, delta) :: tr₂₀) =
          PMF.pure (delta,
            ((⟨stmt, iv, coms, encWit w + (FAEST.convertExpandedRows d rows).u,
              mkPreMsg (FAEST.convertExpandedRows d rows).columns
                (FAEST.convertExpandedRows d rows).u
                (encWit w + (FAEST.convertExpandedRows d rows).u)⟩, delta) :: tr₂₀)) :=
        hmemo_v
      rw [hmemo_v', PMF.pure_map, PMF.pure_bind]
      dsimp only
      rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith,
        OracleComp.runWith_sumHandler_liftRight, OracleComp.runWith_eq_run_interpret]
      have hopen : ∀ idx : Fin (2 ^ d), idx ≠ chalToIdx delta →
          ∃ out, tr₁.lookup
            ⟨(fun i => if i = chalToIdx delta then defaultSeed else keys i) idx, iv, idx⟩ =
              some out ∧ out.com = coms idx ∧ expand out.seedOut = rows idx := by
        intro idx hne
        simp only [hne, ↓reduceIte]
        exact hlook₁ idx idx.isLt
      have hcollect := collectOpenRows_of_trace (Stmt := Stmt) (PreMsg := PreMsg) (Chal := Chal)
        expand iv _ coms rows (chalToIdx delta) tr₁
        ((⟨stmt, iv, coms, encWit w + (FAEST.convertExpandedRows d rows).u,
          mkPreMsg (FAEST.convertExpandedRows d rows).columns
            (FAEST.convertExpandedRows d rows).u
            (encWit w + (FAEST.convertExpandedRows d rows).u)⟩, delta) :: tr₂₀)
        hopen (2 ^ d) le_rfl
      change (interpret voleithMemoize _).run _ = _ at hcollect
      dsimp only [voleithMemoize] at hcollect
      rw [hcollect, PMF.pure_bind]
      dsimp only
      have hv_eq : (fun i : Fin (2 ^ d) =>
          if (i : ℕ) < 2 ^ d then FAEST.verifierRows rows (chalToIdx delta) i else 0) =
          FAEST.verifierRows rows (chalToIdx delta) := by
        funext i
        simp [i.isLt]
      rw [hv_eq, ProbOracleComp.runWith_pure]
      refine congrArg (fun b => PMF.pure (b, (tr₁, _))) ?_
      have hcols :
          (FAEST.convertExpandedRows d (FAEST.verifierRows rows (chalToIdx delta))).columns =
          fun j => (FAEST.convertExpandedRows d rows).columns j +
            fun k => (BitString.equivFin d).symm (chalToIdx delta) j *
              (FAEST.convertExpandedRows d rows).u k := by
        funext j
        exact FAEST.convertExpandedRows_correlation rows (chalToIdx delta) j
      rw [hcols]
      exact hRel (FAEST.convertExpandedRows d rows).columns
        (FAEST.convertExpandedRows d rows).u delta
    · intro e he
      rcases hbound₁ e he with ⟨hiv, _⟩ | hmem₁₀
      · exact Or.inl hiv
      · exact Or.inr hmem₁₀
    · intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he₀
      · exact Or.inl rfl
      · exact Or.inr he₀

/-- Exact completeness of the `leaf_hash::shake` VOLEitH protocol in the two-channel lazy ROM:
running the honest prover and verifier against `voleithMemoize` from an empty trace accepts with
probability `1`. -/
theorem voleithHonestGame_eq_pure_true {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit : Type}
    [BEq (LeafQuery d Seed IV)] [LawfulBEq (LeafQuery d Seed IV)]
    [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [LawfulBEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen)
    (encWit : Wit → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (mkPreMsg : (Fin d → BitString rowLen) → BitString rowLen → BitString rowLen → PreMsg)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (defaultSeed : Seed) (iv : IV) (keys : Fin (2 ^ d) → Seed) (stmt : Stmt) (w : Wit)
    (hRel : ∀ (pCols : Fin d → BitString rowLen) (u : BitString rowLen) (delta : Chal),
      checkRel stmt
        (fun j => pCols j + fun k => (BitString.equivFin d).symm (chalToIdx delta) j * u k)
        (encWit w + u) (mkPreMsg pCols u (encWit w + u)) delta = true) :
    ((ProbOracleComp.runWith
      (voleithMemoize (d := d) (sdLen := sdLen) (comLen := comLen) (rowLen := rowLen)
        (Stmt := Stmt) (Seed := Seed) (IV := IV) (PreMsg := PreMsg) (Chal := Chal))
      (voleithHonestGame expand encWit chalToIdx mkPreMsg checkRel defaultSeed iv keys stmt w)
      ([], [])).map Prod.fst) = PMF.pure true := by
  refine PMF.map_eq_pure_iff.mpr ?_
  rintro ⟨b, st_end⟩ hsupp
  rw [voleithHonestGame, ProbOracleComp.runWith_bind, PMF.mem_support_bind_iff] at hsupp
  obtain ⟨⟨prf, st_mid⟩, hprove, hver⟩ := hsupp
  rw [voleithProveROM, ProbOracleComp.runWith, OracleComp.runWith_sumHandler_liftRight,
    OracleComp.runWith_eq_run_interpret] at hprove
  have hres := (voleithProveLeafFS_verify_of_fresh expand encWit chalToIdx mkPreMsg checkRel
    defaultSeed iv keys stmt w hRel ([], []) (by simp) (by simp) hprove).1
  rw [hres, PMF.mem_support_pure_iff, Prod.mk.injEq] at hver
  exact hver.1

end ROProtocol

/-! ### Sticky Two-Channel Bad-Event Bound and Straight-Line Knowledge Extraction -/

section StickySoundness

/-- Combined trace-and-bad-flag state `(tr, bad)` for sticky ROM soundness accounting. -/
private abbrev VOLEITHStickyState (d sdLen comLen rowLen : ℕ)
    (Stmt Seed IV PreMsg Chal : Type) :=
  VOLEITHTraceState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal × Bool

/-- Concrete knowledge-soundness error bound `ε_KS` for `leaf_hash::shake` VOLEitH in the
two-channel ROM: leaf collision + post-`H_FS` preimage hit + Fiat–Shamir unsound challenge hit. -/
@[expose] noncomputable def voleithKSBound (d comLen Q_leaf Q_FS : ℕ) (ε_rel : ℝ≥0) : ℝ≥0 :=
  ((Q_leaf : ℝ≥0) * ((Q_leaf : ℝ≥0) + (2 ^ d : ℝ≥0) * (Q_FS : ℝ≥0)) / (2 ^ comLen : ℝ≥0)) +
    (Q_FS : ℝ≥0) * ε_rel

/-- All leaf commitments recorded in `tr₁` and inside `FSQuery.coms` entries of `tr₂`. -/
private def seenComList {d sdLen comLen rowLen : ℕ} {Stmt Seed IV PreMsg Chal : Type}
    (st : VOLEITHTraceState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) :
    List (BitString comLen) :=
  (st.1.map fun e => e.2.com) ++ (st.2.flatMap fun e => List.ofFn e.1.coms)

private theorem seenComList_length {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal : Type}
    (st : VOLEITHTraceState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) :
    (seenComList st).length = st.1.length + 2 ^ d * st.2.length := by
  rcases st with ⟨tr₁, tr₂⟩
  simp only [seenComList, List.length_append, List.length_map]
  congr 1
  induction tr₂ with
  | nil => simp
  | cons hd tl ih =>
    simp [List.flatMap_cons, List.length_append, List.length_ofFn, ih]
    ring

/-- Bad event on a fresh `H_FS` query `(stmt, iv, coms, dCorr, preMsg) ↦ Δ`: the witness already
determined in `tr₁` fails `Rel`, yet `checkRel` accepts `Δ` on `FAEST.verifierRows`. -/
private def fsLuckyBad {d sdLen comLen rowLen : ℕ} {Stmt Seed IV PreMsg Chal Wit : Type}
    [DecidableEq IV]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (tr₁ : LeafTrace d sdLen comLen Seed IV)
    (q : FSQuery d comLen rowLen Stmt IV PreMsg) (delta : Chal) : Bool :=
  let rows := extractRowsFromTrace expand tr₁ q.iv q.coms
  let w := decWit (q.dCorr + (FAEST.convertExpandedRows d rows).u)
  !Rel q.stmt w &&
    checkRel q.stmt
      (FAEST.convertExpandedRows d (FAEST.verifierRows rows (chalToIdx delta))).columns
      q.dCorr q.preMsg delta

/-- Soundness error assumption on the underlying non-ROM check predicate `checkRel`: whenever the
reconstructed witness `w* = decWit (dCorr + conv.u)` fails `Rel stmt`, a uniform challenge
`Δ ← Chal` passes `checkRel` on `FAEST.verifierRows rows (chalToIdx Δ)` with probability at
most `ε_rel : ℝ≥0`. -/
@[expose] def VOLEITHSoundnessError {d rowLen : ℕ}
    {Stmt PreMsg Chal Wit : Type} [Fintype Chal] [Nonempty Chal]
    (decWit : BitString rowLen → Wit) (chalToIdx : Chal → Fin (2 ^ d))
    (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (ε_rel : ℝ≥0) : Prop :=
  ∀ (stmt : Stmt) (rows : Fin (2 ^ d) → BitString rowLen)
    (dCorr : BitString rowLen) (preMsg : PreMsg),
    Rel stmt (decWit (dCorr + (FAEST.convertExpandedRows d rows).u)) = false →
    (PMF.uniformOfFintype Chal).toOuterMeasure
      {delta : Chal |
        checkRel stmt
          (FAEST.convertExpandedRows d (FAEST.verifierRows rows (chalToIdx delta))).columns
          dCorr preMsg delta = true} ≤ (ε_rel : ℝ≥0∞)

/-- Step kernel flagging leaf commitment collisions (`out.com ∈ seenComList`) on `H_leaf` and
unsound Fiat–Shamir challenges (`fsLuckyBad`) on `H_FS`. -/
private noncomputable def voleithStepKernel {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool) :
    (q : LeafQuery d Seed IV ⊕ FSQuery d comLen rowLen Stmt IV PreMsg) →
      VOLEITHTraceState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal →
      PMF (VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal q ×
        VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal)
  | .inl ql, (tr₁, tr₂) =>
    match tr₁.lookup ql with
    | some out => PMF.pure (out, ((tr₁, tr₂), false))
    | none =>
      (PMF.uniformOfFintype (LeafOutput sdLen comLen)).map fun out =>
        (out, (((ql, out) :: tr₁, tr₂), decide (out.com ∈ seenComList (tr₁, tr₂))))
  | .inr qf, (tr₁, tr₂) =>
    match tr₂.lookup qf with
    | some delta => PMF.pure (delta, ((tr₁, tr₂), false))
    | none =>
      (PMF.uniformOfFintype Chal).map fun delta =>
        (delta, ((tr₁, (qf, delta) :: tr₂),
          fsLuckyBad expand decWit chalToIdx Rel checkRel tr₁ qf delta))

/-- Sticky two-channel ROM handler built with `OracleComp.withBadFlag`. -/
private noncomputable def voleithStickyMemoize {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool) :
    (q : LeafQuery d Seed IV ⊕ FSQuery d comLen rowLen Stmt IV PreMsg) →
      StateT (VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) PMF
        (VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal q) :=
  OracleComp.withBadFlag (voleithStepKernel expand decWit chalToIdx Rel checkRel)

private theorem voleithStepKernel_map_fst {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (q : LeafQuery d Seed IV ⊕ FSQuery d comLen rowLen Stmt IV PreMsg)
    (st : VOLEITHTraceState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) :
    (voleithStepKernel expand decWit chalToIdx Rel checkRel q st).map (Prod.map id Prod.fst) =
      voleithMemoize q st := by
  rcases st with ⟨tr₁, tr₂⟩
  rcases q with ql | qf
  · cases h : tr₁.lookup ql <;>
      simp [voleithStepKernel, voleithMemoize, RandomOracle.memoizeSum_inl, Cslib.memoize, h,
        PMF.map, PMF.bind_bind, Function.comp_def, PMF.pure_bind]
  · cases h : tr₂.lookup qf <;>
      simp [voleithStepKernel, voleithMemoize, RandomOracle.memoizeSum_inr, Cslib.memoize, h,
        PMF.map, PMF.bind_bind, Function.comp_def, PMF.pure_bind]

/-- Dropping the sticky bad flag from `voleithStickyMemoize` recovers `voleithMemoize`. -/
private theorem voleithStickyMemoize_map_forget {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit α : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (program : ProbOracleComp (VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) α)
    (st : VOLEITHTraceState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) (b : Bool) :
    (ProbOracleComp.runWith (voleithStickyMemoize expand decWit chalToIdx Rel checkRel)
        program (st, b)).map (Prod.map id Prod.fst) =
      ProbOracleComp.runWith voleithMemoize program st :=
  ProbOracleComp.runWith_withBadFlag_map_fst
    (voleithStepKernel expand decWit chalToIdx Rel checkRel)
    voleithMemoize (voleithStepKernel_map_fst expand decWit chalToIdx Rel checkRel) program st b

/-- Structural trace invariant preserved by every unflagged transition of `voleithStickyMemoize`:
`tr₁` is commitment-collision-free, and every `FSQuery` in `tr₂` either decodes a valid `Rel`
witness or fails `checkRel`. -/
private def VOLEITHGoodInv {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit : Type} [DecidableEq IV]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (tr : VOLEITHTraceState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) : Prop :=
  tr.1.Pairwise (fun a b => a.2.com ≠ b.2.com) ∧
  ∀ e ∈ tr.2,
    let rows := extractRowsFromTrace expand tr.1 e.1.iv e.1.coms
    let w := decWit (e.1.dCorr + (FAEST.convertExpandedRows d rows).u)
    Rel e.1.stmt w = true ∨
      checkRel e.1.stmt
        (FAEST.convertExpandedRows d (FAEST.verifierRows rows (chalToIdx e.2))).columns
        e.1.dCorr e.1.preMsg e.2 = false

private theorem extractLeafFromTrace_cons_of_ne {d sdLen comLen : ℕ} {Seed IV : Type}
    [DecidableEq IV]
    (ql : LeafQuery d Seed IV) (out : LeafOutput sdLen comLen)
    (tr : LeafTrace d sdLen comLen Seed IV) (iv : IV) (coms : Fin (2 ^ d) → BitString comLen)
    (idx : Fin (2 ^ d)) (hne : out.com ≠ coms idx) :
    extractLeafFromTrace ((ql, out) :: tr) iv coms idx =
      extractLeafFromTrace tr iv coms idx := by
  unfold extractLeafFromTrace
  have hf : decide (ql.iv = iv ∧ ql.index = idx ∧ out.com = coms idx) = false := by
    simp [hne]
  simp [List.find?, hf]

private theorem extractLeafFromTrace_eq_of_mem_pairwise {d sdLen comLen : ℕ} {Seed IV : Type}
    [DecidableEq IV]
    {tr : LeafTrace d sdLen comLen Seed IV} (hpw : tr.Pairwise (fun a b => a.2.com ≠ b.2.com))
    {q : LeafQuery d Seed IV} {out : LeafOutput sdLen comLen} (hmem : (q, out) ∈ tr)
    {iv : IV} {coms : Fin (2 ^ d) → BitString comLen} {idx : Fin (2 ^ d)}
    (hiv : q.iv = iv) (hidx : q.index = idx) (hcom : out.com = coms idx) :
    extractLeafFromTrace tr iv coms idx = some (q.seed, out.seedOut) := by
  unfold extractLeafFromTrace
  suffices h : tr.find? (fun e => decide (e.1.iv = iv ∧ e.1.index = idx ∧ e.2.com = coms idx)) =
      some (q, out) by
    rw [h]
    rfl
  induction tr with
  | nil => simp at hmem
  | cons hd tl ih =>
    rw [List.pairwise_cons] at hpw
    rcases hpw with ⟨hhead, htl⟩
    rw [List.mem_cons] at hmem
    by_cases hp : decide (hd.1.iv = iv ∧ hd.1.index = idx ∧ hd.2.com = coms idx) = true
    · simp only [List.find?_cons, hp]
      rcases hmem with rfl | hmem_tl
      · rfl
      · exfalso
        have hdcom : hd.2.com = coms idx := by
          simp only [decide_eq_true_eq] at hp
          exact hp.2.2
        exact hhead (q, out) hmem_tl (hdcom.trans hcom.symm)
    · have hpf : decide (hd.1.iv = iv ∧ hd.1.index = idx ∧ hd.2.com = coms idx) = false :=
        Bool.eq_false_iff.mpr hp
      simp only [List.find?_cons, hpf]
      rcases hmem with rfl | hmem_tl
      · exfalso
        apply hp
        simp [hiv, hidx, hcom]
      · exact ih htl hmem_tl

private theorem extractRowsFromTrace_of_not_mem_seenComList {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal : Type} [DecidableEq IV]
    (expand : BitString sdLen → BitString rowLen)
    {tr₁ : LeafTrace d sdLen comLen Seed IV}
    {tr₂ : FSTrace d comLen rowLen Stmt IV PreMsg Chal}
    {ql : LeafQuery d Seed IV} {out : LeafOutput sdLen comLen}
    (hnot : out.com ∉ seenComList (tr₁, tr₂))
    {e : FSQuery d comLen rowLen Stmt IV PreMsg × Chal} (he : e ∈ tr₂) :
    extractRowsFromTrace expand ((ql, out) :: tr₁) e.1.iv e.1.coms =
      extractRowsFromTrace expand tr₁ e.1.iv e.1.coms := by
  funext idx
  simp only [extractRowsFromTrace]
  rw [extractLeafFromTrace_cons_of_ne]
  intro hcom_eq
  apply hnot
  simp only [seenComList, List.mem_append, List.mem_flatMap, List.mem_ofFn]
  exact Or.inr ⟨e, he, ⟨idx, hcom_eq.symm⟩⟩

private theorem voleithStickyMemoize_preserves_goodInv {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (q : LeafQuery d Seed IV ⊕ FSQuery d comLen rowLen Stmt IV PreMsg)
    (st : VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal)
    (hinv : st.2 = false → VOLEITHGoodInv expand decWit chalToIdx Rel checkRel st.1)
    (a : VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal q)
    (st' : VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal)
    (hsupp : (a, st') ∈ (voleithStickyMemoize expand decWit chalToIdx Rel checkRel q st).support)
    (hclean : st'.2 = false) :
    VOLEITHGoodInv expand decWit chalToIdx Rel checkRel st'.1 := by
  rcases st with ⟨⟨tr₁, tr₂⟩, b⟩
  cases b with
  | true =>
    have hbad : OracleComp.FlagBad st' :=
      OracleComp.isFlagMonotone_withBadFlag _ q (tr₁, tr₂) (a, st') hsupp
    simp [OracleComp.FlagBad, hclean] at hbad
  | false =>
    obtain ⟨hpw, hfsInv⟩ := hinv rfl
    simp only [voleithStickyMemoize, OracleComp.withBadFlag_false] at hsupp
    rcases q with ql | qf
    · dsimp only [voleithStepKernel] at hsupp
      cases hlook : tr₁.lookup ql with
      | some out =>
        simp only [hlook, PMF.mem_support_pure_iff, Prod.mk.injEq] at hsupp
        obtain ⟨_, rfl⟩ := hsupp
        exact ⟨hpw, hfsInv⟩
      | none =>
        simp only [hlook, PMF.mem_support_map_iff, Prod.mk.injEq] at hsupp
        obtain ⟨out, _, heq⟩ := hsupp
        obtain ⟨rfl, rfl⟩ := heq
        simp only at hclean
        have hnot : out.com ∉ seenComList (tr₁, tr₂) := by
          simpa only [decide_eq_false_iff_not] using hclean
        constructor
        · rw [List.pairwise_cons]
          refine ⟨fun e he heq => hnot ?_, hpw⟩
          simp only [seenComList, List.mem_append, List.mem_map]
          left
          exact ⟨e, he, heq.symm⟩
        · intro e he
          have hrows := extractRowsFromTrace_of_not_mem_seenComList (ql := ql) expand hnot he
          dsimp only
          rw [hrows]
          exact hfsInv e he
    · dsimp only [voleithStepKernel] at hsupp
      cases hlook : tr₂.lookup qf with
      | some delta =>
        simp only [hlook, PMF.mem_support_pure_iff, Prod.mk.injEq] at hsupp
        obtain ⟨_, rfl⟩ := hsupp
        exact ⟨hpw, hfsInv⟩
      | none =>
        simp only [hlook, PMF.mem_support_map_iff, Prod.mk.injEq] at hsupp
        obtain ⟨delta, _, heq⟩ := hsupp
        obtain ⟨rfl, rfl⟩ := heq
        simp only at hclean
        refine ⟨hpw, fun e he => ?_⟩
        simp only [List.mem_cons] at he
        rcases he with rfl | he_tl
        · dsimp only [fsLuckyBad] at hclean
          by_cases hrel :
              Rel qf.stmt (decWit (qf.dCorr + (FAEST.convertExpandedRows d
                (extractRowsFromTrace expand tr₁ qf.iv qf.coms)).u)) = true
          · exact Or.inl hrel
          · right
            have hrel_f :
                Rel qf.stmt (decWit (qf.dCorr + (FAEST.convertExpandedRows d
                  (extractRowsFromTrace expand tr₁ qf.iv qf.coms)).u)) = false :=
              Bool.eq_false_iff.mpr hrel
            simpa [hrel_f] using hclean
        · exact hfsInv e he_tl

/-- Budget on `VOLEITHStickyState` counting `|tr₁| + 2 ^ d * |tr₂|` divided by `2 ^ comLen`. -/
private noncomputable def voleithBudget {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal : Type}
    (st : VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) : ℝ≥0∞ :=
  ((st.1.1.length + 2 ^ d * st.1.2.length : ℕ) : ℝ≥0∞) / (2 ^ comLen : ℝ≥0∞)

private theorem toOuterMeasure_voleithStickyMemoize_step_le {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    {ε_rel : ℝ≥0}
    (hSound : VOLEITHSoundnessError decWit chalToIdx Rel checkRel ε_rel)
    (q : LeafQuery d Seed IV ⊕ FSQuery d comLen rowLen Stmt IV PreMsg)
    (st : VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal)
    (hst : ¬ OracleComp.FlagBad st) :
    (voleithStickyMemoize expand decWit chalToIdx Rel checkRel q st).toOuterMeasure
        {x | OracleComp.FlagBad x.2} ≤
      (voleithLeafCost q : ℝ≥0∞) * voleithBudget st +
        (voleithFSCost q : ℝ≥0∞) * (ε_rel : ℝ≥0∞) := by
  rcases st with ⟨⟨tr₁, tr₂⟩, b⟩
  have hb : b = false := Bool.eq_false_iff.mpr hst
  subst hb
  simp only [voleithStickyMemoize, OracleComp.withBadFlag_false]
  rcases q with ql | qf
  · simp only [voleithStepKernel, voleithLeafCost, voleithFSCost, Nat.cast_one, one_mul,
      Nat.cast_zero, zero_mul, add_zero]
    cases hlook : tr₁.lookup ql with
    | some out =>
      have hz : ((PMF.pure (out, ((tr₁, tr₂), false)) : PMF _).toOuterMeasure
          {x | OracleComp.FlagBad x.2}) = 0 := by
        rw [PMF.toOuterMeasure_apply_eq_zero_iff]
        refine Set.disjoint_left.mpr fun x hx hbad => ?_
        rw [PMF.mem_support_pure_iff] at hx
        rw [hx] at hbad
        simp [OracleComp.FlagBad] at hbad
      exact hz.trans_le zero_le
    | none =>
      rw [PMF.toOuterMeasure_map_apply]
      have hset :
          (fun out : LeafOutput sdLen comLen =>
              (out, (((ql, out) :: tr₁, tr₂), decide (out.com ∈ seenComList (tr₁, tr₂))))) ⁻¹'
            {x | OracleComp.FlagBad x.2} =
            {out : LeafOutput sdLen comLen |
              (leafOutputEquiv sdLen comLen out).1 ∈ seenComList (tr₁, tr₂)} := by
        ext out
        simp [OracleComp.FlagBad, leafOutputEquiv]
      rw [hset, Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_fst
        (leafOutputEquiv sdLen comLen)]
      refine (Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_mem_list_le
        (seenComList (tr₁, tr₂))).trans ?_
      have hcard : Fintype.card (BitString comLen) = 2 ^ comLen := by
        simp [BitString]
      rw [hcard, seenComList_length]
      simp only [voleithBudget, one_div, ← div_eq_mul_inv, Nat.cast_pow, Nat.cast_ofNat, le_refl]
  · simp only [voleithStepKernel, voleithLeafCost, voleithFSCost, Nat.cast_zero, zero_mul,
      Nat.cast_one, one_mul, zero_add]
    cases hlook : tr₂.lookup qf with
    | some delta =>
      have hz : ((PMF.pure (delta, ((tr₁, tr₂), false)) : PMF _).toOuterMeasure
          {x | OracleComp.FlagBad x.2}) = 0 := by
        rw [PMF.toOuterMeasure_apply_eq_zero_iff]
        refine Set.disjoint_left.mpr fun x hx hbad => ?_
        rw [PMF.mem_support_pure_iff] at hx
        rw [hx] at hbad
        simp [OracleComp.FlagBad] at hbad
      exact hz.trans_le zero_le
    | none =>
      rw [PMF.toOuterMeasure_map_apply]
      let rows := extractRowsFromTrace expand tr₁ qf.iv qf.coms
      by_cases hrel :
          Rel qf.stmt (decWit (qf.dCorr + (FAEST.convertExpandedRows d rows).u)) = true
      · have hz : (PMF.uniformOfFintype Chal).toOuterMeasure
            ((fun delta : Chal => (delta, ((tr₁, (qf, delta) :: tr₂),
              fsLuckyBad expand decWit chalToIdx Rel checkRel tr₁ qf delta))) ⁻¹'
              {x | OracleComp.FlagBad x.2}) = 0 := by
          rw [PMF.toOuterMeasure_apply_eq_zero_iff]
          refine Set.disjoint_left.mpr fun delta hmem hpre => ?_
          change fsLuckyBad expand decWit chalToIdx Rel checkRel tr₁ qf delta = true at hpre
          simp [fsLuckyBad, rows, hrel] at hpre
        exact hz.trans_le zero_le
      · have hrel_f :
            Rel qf.stmt (decWit (qf.dCorr + (FAEST.convertExpandedRows d rows).u)) = false :=
          Bool.eq_false_iff.mpr hrel
        have hsub :
            (fun delta : Chal =>
                (delta, ((tr₁, (qf, delta) :: tr₂),
                  fsLuckyBad expand decWit chalToIdx Rel checkRel tr₁ qf delta))) ⁻¹'
              {x | OracleComp.FlagBad x.2} ⊆
              {delta : Chal |
                checkRel qf.stmt
                  (FAEST.convertExpandedRows d (FAEST.verifierRows rows (chalToIdx delta))).columns
                  qf.dCorr qf.preMsg delta = true} := by
          intro delta hdelta
          change fsLuckyBad expand decWit chalToIdx Rel checkRel tr₁ qf delta = true at hdelta
          simpa [fsLuckyBad, rows, hrel_f] using hdelta
        exact ((PMF.uniformOfFintype Chal).toOuterMeasure.mono hsub).trans
          (hSound qf.stmt rows qf.dCorr qf.preMsg hrel_f)

private theorem voleithBudget_grow {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (q : LeafQuery d Seed IV ⊕ FSQuery d comLen rowLen Stmt IV PreMsg)
    (st : VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal)
    (hst : ¬ OracleComp.FlagBad st)
    (x : VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal q ×
      VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal)
    (hx : x ∈ (voleithStickyMemoize expand decWit chalToIdx Rel checkRel q st).support)
    (hgood : ¬ OracleComp.FlagBad x.2) :
    voleithBudget x.2 ≤
      voleithBudget st +
        (voleithLeafCost q : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ comLen) +
        (voleithFSCost q : ℝ≥0∞) * ((2 ^ d : ℝ≥0∞) / 2 ^ comLen) := by
  rcases st with ⟨⟨tr₁, tr₂⟩, b⟩
  have hb : b = false := Bool.eq_false_iff.mpr hst
  subst hb
  simp only [voleithStickyMemoize, OracleComp.withBadFlag_false] at hx
  rcases q with ql | qf
  · dsimp only [voleithStepKernel] at hx
    cases hlook : tr₁.lookup ql with
    | some out =>
      simp only [hlook, PMF.mem_support_pure_iff] at hx
      rw [hx]
      simp [voleithBudget, voleithLeafCost, voleithFSCost]
    | none =>
      simp only [hlook, PMF.mem_support_map_iff] at hx
      obtain ⟨out, -, rfl⟩ := hx
      simp only [voleithBudget, voleithLeafCost, voleithFSCost, Nat.cast_one, one_mul,
        Nat.cast_zero, zero_mul, add_zero, List.length_cons]
      have hnum : ((tr₁.length + 1 + 2 ^ d * tr₂.length : ℕ) : ℝ≥0∞) =
          ((tr₁.length + 2 ^ d * tr₂.length : ℕ) : ℝ≥0∞) + 1 := by
        push_cast
        ring
      simp only [div_eq_mul_inv] at hnum ⊢
      rw [hnum]
      exact le_of_eq (by ring)
  · dsimp only [voleithStepKernel] at hx
    cases hlook : tr₂.lookup qf with
    | some delta =>
      simp only [hlook, PMF.mem_support_pure_iff] at hx
      rw [hx]
      simp [voleithBudget, voleithLeafCost, voleithFSCost]
    | none =>
      simp only [hlook, PMF.mem_support_map_iff] at hx
      obtain ⟨delta, -, rfl⟩ := hx
      simp only [voleithBudget, voleithLeafCost, voleithFSCost, Nat.cast_zero, zero_mul,
        add_zero, Nat.cast_one, one_mul, List.length_cons]
      have hnum : ((tr₁.length + 2 ^ d * (tr₂.length + 1) : ℕ) : ℝ≥0∞) =
          ((tr₁.length + 2 ^ d * tr₂.length : ℕ) : ℝ≥0∞) + (2 ^ d : ℝ≥0∞) := by
        push_cast
        ring
      simp only [div_eq_mul_inv] at hnum ⊢
      rw [hnum]
      exact le_of_eq (by ring)

/-- Two-budget bad-state probability bound for any `VOLEITHROSpec` program starting at an
arbitrary clean state `(st, false)` under `voleithStickyMemoize`. -/
private theorem toOuterMeasure_runWith_voleithStickyMemoize_bad_le_of_state
    {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit α : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    {ε_rel : ℝ≥0}
    (hSound : VOLEITHSoundnessError decWit chalToIdx Rel checkRel ε_rel)
    {program : ProbOracleComp (VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) α}
    {Q_leaf Q_FS : ℕ}
    (hleaf : IsCostBounded (Sum.elim (fun _ => 0) voleithLeafCost) program Q_leaf)
    (hfs : IsCostBounded (Sum.elim (fun _ => 0) voleithFSCost) program Q_FS)
    (st : VOLEITHTraceState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) :
    (ProbOracleComp.runWith (voleithStickyMemoize expand decWit chalToIdx Rel checkRel)
        program (st, false)).toOuterMeasure {x | OracleComp.FlagBad x.2} ≤
      (Q_leaf : ℝ≥0∞) *
          ((((st.1.length + 2 ^ d * st.2.length : ℕ) : ℝ≥0∞) / 2 ^ comLen) +
            (Q_leaf : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ comLen) +
            (Q_FS : ℝ≥0∞) * ((2 ^ d : ℝ≥0∞) / 2 ^ comLen)) +
        (Q_FS : ℝ≥0∞) * (ε_rel : ℝ≥0∞) := by
  rw [ProbOracleComp.runWith_eq_run_interpret]
  refine OracleComp.toOuterMeasure_bad_le_two
    (handler := OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n))
      (voleithStickyMemoize expand decWit chalToIdx Rel checkRel))
    (bad := fun s => OracleComp.FlagBad s)
    (Sum.elim (fun _ => 0) voleithLeafCost) (Sum.elim (fun _ => 0) voleithFSCost)
    voleithBudget ((1 : ℝ≥0∞) / 2 ^ comLen) ((2 ^ d : ℝ≥0∞) / 2 ^ comLen) (ε_rel : ℝ≥0∞)
    (fun q s hs => by
      cases q with
      | inl m =>
        simp only [Sum.elim_inl, Nat.cast_zero, zero_mul, add_zero]
        change (StateT.lift (ProbComp.unifOracle m) s).toOuterMeasure
          {x : Fin (m + 1) × _ | OracleComp.FlagBad x.2} ≤ 0
        rw [nonpos_iff_eq_zero, PMF.toOuterMeasure_apply_eq_zero_iff]
        refine Set.disjoint_left.mpr fun x hx hbad => hs ?_
        obtain ⟨_, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
        exact hbad
      | inr q =>
        exact toOuterMeasure_voleithStickyMemoize_step_le expand decWit chalToIdx Rel checkRel
          hSound q s hs)
    (fun q s hs x hx hgood => by
      cases q with
      | inl m =>
        change x ∈ ((ProbComp.unifOracle m).map (·, s)).support at hx
        obtain ⟨_, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
        simp
      | inr q =>
        exact voleithBudget_grow expand decWit chalToIdx Rel checkRel q s hs x hx hgood)
    hleaf hfs (by simp [OracleComp.FlagBad])

private theorem voleithKSBound_coe {d comLen Q_leaf Q_FS : ℕ} {ε_rel : ℝ≥0} :
    ((voleithKSBound d comLen Q_leaf Q_FS ε_rel : ℝ≥0) : ℝ≥0∞) =
      (Q_leaf : ℝ≥0∞) *
          ((Q_leaf : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ comLen) +
            (Q_FS : ℝ≥0∞) * ((2 ^ d : ℝ≥0∞) / 2 ^ comLen)) +
        (Q_FS : ℝ≥0∞) * (ε_rel : ℝ≥0∞) := by
  have hpow : (2 ^ comLen : ℝ≥0) ≠ 0 := by positivity
  simp only [voleithKSBound, ENNReal.coe_add, ENNReal.coe_div hpow, ENNReal.coe_mul,
    ENNReal.coe_natCast, ENNReal.coe_pow]
  simp only [div_eq_mul_inv]
  push_cast
  ring

/-- Two-budget bad-state bound `voleithKSBound d comLen Q_leaf Q_FS ε_rel : ℝ≥0` starting from an
empty trace `(([], []), false)`. -/
private theorem toOuterMeasure_runWith_voleithStickyMemoize_bad_le
    {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit α : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    {ε_rel : ℝ≥0}
    (hSound : VOLEITHSoundnessError decWit chalToIdx Rel checkRel ε_rel)
    {program : ProbOracleComp (VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) α}
    {Q_leaf Q_FS : ℕ}
    (hleaf : IsCostBounded (Sum.elim (fun _ => 0) voleithLeafCost) program Q_leaf)
    (hfs : IsCostBounded (Sum.elim (fun _ => 0) voleithFSCost) program Q_FS) :
    (ProbOracleComp.runWith (voleithStickyMemoize expand decWit chalToIdx Rel checkRel)
        program (([], []), false)).toOuterMeasure {x | OracleComp.FlagBad x.2} ≤
      (voleithKSBound d comLen Q_leaf Q_FS ε_rel : ℝ≥0∞) := by
  rw [voleithKSBound_coe]
  simpa using toOuterMeasure_runWith_voleithStickyMemoize_bad_le_of_state
    expand decWit chalToIdx Rel checkRel hSound hleaf hfs ([], [])

private theorem runWith_sticky_flagBad_false {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit α : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    {prog : ProbOracleComp (VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) α}
    {st_mid st' : VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal}
    {b : α}
    (hsupp : (b, st') ∈
      (ProbOracleComp.runWith (voleithStickyMemoize expand decWit chalToIdx Rel checkRel)
        prog st_mid).support)
    (hclean' : st'.2 = false) :
    st_mid.2 = false := by
  by_contra htrue
  have hbad_mid : OracleComp.FlagBad st_mid := by
    cases hsm : st_mid.2 <;> simp_all [OracleComp.FlagBad]
  have hbad_end : OracleComp.FlagBad st' :=
    ProbOracleComp.runWith_invariant _ (fun s => OracleComp.FlagBad s)
      (fun q s hs a next hx => by
        rcases s with ⟨s₁, sb⟩
        dsimp only [OracleComp.FlagBad] at hs
        subst hs
        exact OracleComp.isFlagMonotone_withBadFlag _ q s₁ (a, next) hx)
      _ st_mid hbad_mid b st' hsupp
  simp [OracleComp.FlagBad, hclean'] at hbad_end

private theorem collectOpenRows_sound_of_clean {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit : Type}
    [BEq (LeafQuery d Seed IV)] [LawfulBEq (LeafQuery d Seed IV)]
    [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (iv : IV) (openKeys : Fin (2 ^ d) → Seed) (coms : Fin (2 ^ d) → BitString comLen)
    (hidden : Fin (2 ^ d)) :
    ∀ (k : ℕ) (hk : k ≤ 2 ^ d)
      (st st' : VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal)
      (openedRows : Fin (2 ^ d) → BitString rowLen),
      st.2 = false →
      VOLEITHGoodInv expand decWit chalToIdx Rel checkRel st.1 →
      (∃ e ∈ st.1.2, e.1.iv = iv ∧ e.1.coms = coms) →
      (some openedRows, st') ∈
        (ProbOracleComp.runWith (voleithStickyMemoize expand decWit chalToIdx Rel checkRel)
          (OracleComp.liftRight (spec₁ := unifSpec)
            (OracleComp.liftLeft (spec₂ := VOLEITHFSSpec d comLen rowLen Stmt IV PreMsg Chal)
              (collectOpenRows expand iv openKeys coms hidden k hk))) st).support →
      st'.2 = false →
      VOLEITHGoodInv expand decWit chalToIdx Rel checkRel st'.1 ∧
        st'.1.2 = st.1.2 ∧
        (∀ idx : Fin (2 ^ d),
          extractLeafFromTrace st'.1.1 iv coms idx =
            extractLeafFromTrace st.1.1 iv coms idx) ∧
        (∀ i : Fin (2 ^ d), (i : ℕ) < k →
          openedRows i =
            FAEST.verifierRows (extractRowsFromTrace expand st.1.1 iv coms) hidden i) := by
  intro k
  induction k with
  | zero =>
    intro hk st st' openedRows _ hinv _ hsupp hclean'
    simp only [collectOpenRows, OracleComp.liftLeft_pure, OracleComp.liftRight_pure,
      ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff, Prod.mk.injEq, Option.some.injEq]
      at hsupp
    obtain ⟨_, rfl⟩ := hsupp
    exact ⟨hinv, rfl, fun _ => rfl, fun i hlt => absurd hlt (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hk st st' openedRows hclean hinv hfsMem hsupp hclean'
    unfold collectOpenRows at hsupp
    rw [OracleComp.liftLeft_bind, OracleComp.liftRight_bind, ProbOracleComp.runWith_bind,
      PMF.mem_support_bind_iff] at hsupp
    obtain ⟨⟨rest, st_mid⟩, hrest, hstep⟩ := hsupp
    have hclean_mid : st_mid.2 = false :=
      runWith_sticky_flagBad_false expand decWit chalToIdx Rel checkRel hstep hclean'
    cases rest with
    | none =>
      by_cases hk0 : (⟨k, hk⟩ : Fin (2 ^ d)) = 0
      · simp [hk0, ProbOracleComp.runWith_pure] at hstep
      · simp only [hk0, ↓reduceIte, OracleComp.liftLeft_bind, OracleComp.liftLeft_query,
          OracleComp.liftRight_bind, OracleComp.liftRight_query, ProbOracleComp.runWith_bind,
          PMF.mem_support_bind_iff] at hstep
        obtain ⟨⟨out, st₁⟩, _, hite⟩ := hstep
        split_ifs at hite <;> simp [ProbOracleComp.runWith_pure] at hite
    | some prevRows =>
      obtain ⟨hinv_mid, htr2_mid, hleaf_mid, hprev⟩ :=
        ih (Nat.le_of_lt hk) st st_mid prevRows hclean hinv hfsMem hrest hclean_mid
      by_cases hk0 : (⟨k, hk⟩ : Fin (2 ^ d)) = 0
      · have hk_eq : k = 0 := congrArg Fin.val hk0
        subst hk_eq
        simp only [collectOpenRows, OracleComp.liftLeft_pure, OracleComp.liftRight_pure,
          ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff, Prod.mk.injEq,
          Option.some.injEq] at hrest
        obtain ⟨rfl, rfl⟩ := hrest
        simp only [hk0, ↓reduceIte, OracleComp.liftLeft_pure, OracleComp.liftRight_pure,
          ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff, Prod.mk.injEq, Option.some.injEq]
          at hstep
        obtain ⟨rfl, rfl⟩ := hstep
        refine ⟨hinv_mid, htr2_mid, hleaf_mid, fun i hi => ?_⟩
        have hi0 : i = 0 := by
          apply Fin.ext
          simp only [Fin.val_zero]
          omega
        subst hi0
        simp [FAEST.verifierRows]
      · simp only [hk0, ↓reduceIte, OracleComp.liftLeft_bind, OracleComp.liftLeft_query,
          OracleComp.liftRight_bind, OracleComp.liftRight_query, ProbOracleComp.runWith_bind,
          PMF.mem_support_bind_iff] at hstep
        obtain ⟨⟨out, st_after⟩, hq_supp, hite⟩ := hstep
        rw [ProbOracleComp.runWith_eq_run_interpret, OracleComp.run_interpret_query,
          OracleComp.sumHandler_inr] at hq_supp
        split_ifs at hite with hcom
        · simp only [OracleComp.liftLeft_pure, OracleComp.liftRight_pure,
            ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff, Prod.mk.injEq,
            Option.map_some, Option.some.injEq] at hite
          obtain ⟨hopen_eq, hst_eq⟩ := hite
          subst hst_eq
          have hinv_after : VOLEITHGoodInv expand decWit chalToIdx Rel checkRel st'.1 :=
            voleithStickyMemoize_preserves_goodInv expand decWit chalToIdx Rel checkRel
              (.inl _) st_mid (fun _ => hinv_mid) out st' hq_supp hclean'
          rcases st_mid with ⟨⟨tr₁_m, tr₂_m⟩, bm⟩
          dsimp only at hclean_mid
          subst hclean_mid
          simp only [voleithStickyMemoize, OracleComp.withBadFlag_false] at hq_supp
          dsimp only [voleithStepKernel] at hq_supp
          cases hlook_q : tr₁_m.lookup ⟨openKeys (FAEST.xorIndex ⟨k, hk⟩ hidden), iv,
              FAEST.xorIndex ⟨k, hk⟩ hidden⟩ with
          | some cached =>
            rw [hlook_q] at hq_supp
            simp only [PMF.mem_support_pure_iff, Prod.mk.injEq] at hq_supp
            obtain ⟨rfl, rfl⟩ := hq_supp
            have hmem_cached : (⟨openKeys (FAEST.xorIndex ⟨k, hk⟩ hidden), iv,
                FAEST.xorIndex ⟨k, hk⟩ hidden⟩, out) ∈ tr₁_m := by
              obtain ⟨b_, a_, heq⟩ := List.lookup_eq_some_iff.mp hlook_q
              simp [heq.1]
            have hleaf_pIdx := extractLeafFromTrace_eq_of_mem_pairwise hinv_mid.1 hmem_cached
              rfl rfl hcom
            refine ⟨hinv_mid, htr2_mid, hleaf_mid, fun i hi => ?_⟩
            rw [hopen_eq]
            by_cases hik : i = ⟨k, hk⟩
            · subst hik
              simp [FAEST.verifierRows, hk0, extractRowsFromTrace, ← hleaf_mid _, hleaf_pIdx]
            · have hi_lt : (i : ℕ) < k := by
                have : (i : ℕ) ≠ k := fun h => hik (Fin.ext h)
                omega
              simp [Function.update, hik, hprev i hi_lt]
          | none =>
            exfalso
            rw [hlook_q] at hq_supp
            simp only [PMF.mem_support_map_iff, Prod.mk.injEq] at hq_supp
            obtain ⟨out₀, -, heq⟩ := hq_supp
            obtain ⟨hout_eq, hst_after_eq⟩ := heq
            rw [← hst_after_eq] at hclean'
            dsimp only at hclean'
            have hnot : out₀.com ∉ seenComList (tr₁_m, tr₂_m) := by
              simpa only [decide_eq_false_iff_not] using hclean'
            apply hnot
            obtain ⟨efs, hefs, hiv_fs, hcoms_fs⟩ := hfsMem
            simp only [seenComList, List.mem_append, List.mem_flatMap, List.mem_ofFn]
            right
            refine ⟨efs, ?_, ⟨FAEST.xorIndex ⟨k, hk⟩ hidden, ?_⟩⟩
            · dsimp only at htr2_mid
              rw [htr2_mid]
              exact hefs
            · rw [hcoms_fs, ← hcom, hout_eq]
        · simp [OracleComp.liftLeft_pure, OracleComp.liftRight_pure,
            ProbOracleComp.runWith_pure] at hite

/-- Straight-line extraction soundness along a single clean execution of `voleithVerifyROM`:
if `voleithVerifyROM` accepts from trace `roSt` under `voleithStickyMemoize` without flipping
the bad flag (`st'.2 = false`), then `extractWitnessFromTrace` applied to the leaf trace `roSt.1`
**prior** to verification already satisfies `Rel stmt w* = true`. -/
private theorem voleithVerifyROM_sound_of_clean {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit : Type}
    [BEq (LeafQuery d Seed IV)] [LawfulBEq (LeafQuery d Seed IV)]
    [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [LawfulBEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (stmt : Stmt) (prf : VOLEITHProof d comLen rowLen Seed IV PreMsg)
    (roSt : VOLEITHTraceState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal)
    (st' : VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal)
    (hinv : VOLEITHGoodInv expand decWit chalToIdx Rel checkRel roSt)
    (hsupp : (true, st') ∈
      (ProbOracleComp.runWith (voleithStickyMemoize expand decWit chalToIdx Rel checkRel)
        (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel stmt prf)
        (roSt, false)).support)
    (hclean' : st'.2 = false) :
    Rel stmt (extractWitnessFromTrace expand decWit roSt.1 prf) = true := by
  unfold voleithVerifyROM at hsupp
  rw [ProbOracleComp.runWith_bind, PMF.mem_support_bind_iff] at hsupp
  obtain ⟨⟨delta, st_mid⟩, hfs_supp, hrest⟩ := hsupp
  have hclean_mid : st_mid.2 = false :=
    runWith_sticky_flagBad_false expand decWit chalToIdx Rel checkRel hrest hclean'
  simp only [OracleComp.liftRight_query] at hfs_supp
  rw [ProbOracleComp.runWith_eq_run_interpret, OracleComp.run_interpret_query,
    OracleComp.sumHandler_inr] at hfs_supp
  have hinv_mid : VOLEITHGoodInv expand decWit chalToIdx Rel checkRel st_mid.1 :=
    voleithStickyMemoize_preserves_goodInv expand decWit chalToIdx Rel checkRel
      (.inr _) (roSt, false) (fun _ => hinv) delta st_mid hfs_supp hclean_mid
  rcases roSt with ⟨tr₁, tr₂⟩
  simp only [voleithStickyMemoize, OracleComp.withBadFlag_false,
    voleithStepKernel] at hfs_supp
  have hst_mid_tr1 : st_mid.1.1 = tr₁ := by
    cases hlook : tr₂.lookup (prf.fsQuery stmt) with
    | some d0 =>
      simp only [hlook, PMF.mem_support_pure_iff, Prod.mk.injEq] at hfs_supp
      obtain ⟨_, rfl⟩ := hfs_supp
      rfl
    | none =>
      simp only [hlook, PMF.mem_support_map_iff, Prod.mk.injEq] at hfs_supp
      obtain ⟨d0, _, heq⟩ := hfs_supp
      obtain ⟨_, rfl⟩ := heq
      rfl
  have hfs_in_mid : (prf.fsQuery stmt, delta) ∈ st_mid.1.2 := by
    cases hlook : tr₂.lookup (prf.fsQuery stmt) with
    | some d0 =>
      simp only [hlook, PMF.mem_support_pure_iff, Prod.mk.injEq] at hfs_supp
      obtain ⟨rfl, rfl⟩ := hfs_supp
      obtain ⟨b_, a_, heq⟩ := List.lookup_eq_some_iff.mp hlook
      simp [heq.1]
    | none =>
      simp only [hlook, PMF.mem_support_map_iff, Prod.mk.injEq] at hfs_supp
      obtain ⟨d0, _, heq⟩ := hfs_supp
      obtain ⟨rfl, rfl⟩ := heq
      simp
  rw [ProbOracleComp.runWith_bind, PMF.mem_support_bind_iff] at hrest
  obtain ⟨⟨vRows, st_open⟩, hopen_supp, hcheck⟩ := hrest
  cases vRows with
  | none =>
    simp only [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hcheck
    simp at hcheck
  | some openedRows =>
    simp only [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hcheck
    obtain ⟨hcheck_eq, rfl⟩ := hcheck
    obtain ⟨hinv_end, htr2_end, hleaf_end, hrows_eq⟩ := collectOpenRows_sound_of_clean
      expand decWit chalToIdx Rel checkRel prf.iv prf.openKeys prf.coms (chalToIdx delta)
      (2 ^ d) le_rfl st_mid st' openedRows hclean_mid hinv_mid
      ⟨(prf.fsQuery stmt, delta), hfs_in_mid, rfl, rfl⟩ hopen_supp hclean'
    have hfs_in_end : (prf.fsQuery stmt, delta) ∈ st'.1.2 := htr2_end ▸ hfs_in_mid
    have hinv_fs := hinv_end.2 (prf.fsQuery stmt, delta) hfs_in_end
    have hrows_same :
        extractRowsFromTrace expand st'.1.1 prf.iv prf.coms =
          extractRowsFromTrace expand tr₁ prf.iv prf.coms := by
      funext idx
      simp only [extractRowsFromTrace, hleaf_end idx, hst_mid_tr1]
    have hopened_same :
        openedRows =
          FAEST.verifierRows (extractRowsFromTrace expand tr₁ prf.iv prf.coms)
            (chalToIdx delta) := by
      funext i
      simpa only [hst_mid_tr1] using hrows_eq i i.isLt
    dsimp only [VOLEITHProof.fsQuery, extractWitnessFromTrace, extractVOLEFromTrace]
      at hinv_fs ⊢
    rw [hrows_same] at hinv_fs
    rw [hopened_same] at hcheck_eq
    rcases hinv_fs with hrel_true | hcheck_false
    · exact hrel_true
    · exact absurd hcheck_eq (by simp [hcheck_false])

/-- Probability that an adaptive prover `P` followed by `voleithVerifyROM` succeeds (`ok = true`)
while `extractWitnessFromTrace` on `P`'s pre-verification trace `tr_P` fails `Rel`. -/
@[expose] noncomputable def voleithKSFailurePMF {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (P : ProbOracleComp (VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal)
      (Stmt × VOLEITHProof d comLen rowLen Seed IV PreMsg)) : PMF Bool :=
  (ProbOracleComp.runWith voleithMemoize P ([], [])).bind fun ((stmt, prf), st_mid) =>
    (ProbOracleComp.runWith voleithMemoize
      (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel stmt prf) st_mid).map
      fun (ok, _) => ok && !Rel stmt (extractWitnessFromTrace expand decWit st_mid.1 prf)

/-- **Straight-line single-proof knowledge soundness** (cf. [BaumBMRS2023Eprint], Lemma 4,
pp. 19–20, specialised to a single challenge repetition and an RO leaf commitment;
`leaf_hash::shake`): running prover `P` and extracting `w* = extractWitnessFromTrace tr_P prf`
without rewinding prior to `voleithVerifyROM` fails with probability at most
`voleithKSBound d comLen (Q_leaf + (2 ^ d - 1)) (Q_FS + 1) ε_rel : ℝ≥0`. -/
theorem voleithKnowledgeSoundness_bound {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit : Type}
    [BEq (LeafQuery d Seed IV)] [LawfulBEq (LeafQuery d Seed IV)]
    [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [LawfulBEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    {ε_rel : ℝ≥0}
    (hSound : VOLEITHSoundnessError decWit chalToIdx Rel checkRel ε_rel)
    (P : ProbOracleComp (VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal)
      (Stmt × VOLEITHProof d comLen rowLen Seed IV PreMsg))
    {Q_leaf Q_FS : ℕ}
    (hleaf : IsCostBounded (Sum.elim (fun _ => 0) voleithLeafCost) P Q_leaf)
    (hfs : IsCostBounded (Sum.elim (fun _ => 0) voleithFSCost) P Q_FS) :
    (voleithKSFailurePMF expand decWit chalToIdx Rel checkRel P) true ≤
      (voleithKSBound d comLen (Q_leaf + (2 ^ d - 1)) (Q_FS + 1) ε_rel : ℝ≥0∞) := by
  let S := voleithStickyMemoize (d := d) (sdLen := sdLen) (comLen := comLen)
    (rowLen := rowLen) (Stmt := Stmt) (Seed := Seed) (IV := IV) (PreMsg := PreMsg)
    (Chal := Chal) expand decWit chalToIdx Rel checkRel
  let combined : ProbOracleComp (VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal)
      Bool := do
    let (stmt, prf) ← P
    voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel stmt prf
  have hcomb_leaf : IsCostBounded (Sum.elim (fun _ => 0) voleithLeafCost) combined
      (Q_leaf + (2 ^ d - 1)) :=
    hleaf.bind fun ⟨stmt, prf⟩ => isCostBounded_leaf_voleithVerifyROM _ _ _ stmt prf
  have hcomb_fs : IsCostBounded (Sum.elim (fun _ => 0) voleithFSCost) combined (Q_FS + 1) :=
    hfs.bind fun ⟨stmt, prf⟩ => isCostBounded_fs_voleithVerifyROM _ _ _ stmt prf
  have hbad_bound :
      (ProbOracleComp.runWith S combined (([], []), false)).toOuterMeasure
        {x | OracleComp.FlagBad x.2} ≤
        (voleithKSBound d comLen (Q_leaf + (2 ^ d - 1)) (Q_FS + 1) ε_rel : ℝ≥0∞) :=
    toOuterMeasure_runWith_voleithStickyMemoize_bad_le expand decWit chalToIdx Rel checkRel hSound
      hcomb_leaf hcomb_fs
  have hforget1 :
      (ProbOracleComp.runWith S P (([], []), false)).map (Prod.map id Prod.fst) =
        ProbOracleComp.runWith voleithMemoize P ([], []) :=
    voleithStickyMemoize_map_forget expand decWit chalToIdx Rel checkRel P ([], []) false
  have hks_eq :
      voleithKSFailurePMF expand decWit chalToIdx Rel checkRel P =
        (ProbOracleComp.runWith S P (([], []), false)).bind fun ((stmt, prf), st_mid) =>
          (ProbOracleComp.runWith S (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel
              stmt prf) st_mid).map fun (ok, _) =>
            ok && !Rel stmt (extractWitnessFromTrace expand decWit st_mid.1.1 prf) := by
    unfold voleithKSFailurePMF
    rw [← hforget1, PMF.bind_map]
    congr 1
    funext x
    rcases x with ⟨⟨stmt, prf⟩, st_mid⟩
    dsimp only [Function.comp_apply, Prod.map, id_eq]
    have hforget2 :=
      voleithStickyMemoize_map_forget expand decWit chalToIdx Rel checkRel
        (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel stmt prf) st_mid.1 st_mid.2
    rw [← hforget2, PMF.map_comp]
    rfl
  have hinvP : ∀ (res : Stmt × VOLEITHProof d comLen rowLen Seed IV PreMsg)
      (st_mid : VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal),
      (res, st_mid) ∈ (ProbOracleComp.runWith S P (([], []), false)).support →
      st_mid.2 = false →
      VOLEITHGoodInv expand decWit chalToIdx Rel checkRel st_mid.1 := by
    intro res st_mid hmem hclean
    exact ProbOracleComp.runWith_invariant S
      (fun s => s.2 = false → VOLEITHGoodInv expand decWit chalToIdx Rel checkRel s.1)
      (fun q s hs a next hnext => voleithStickyMemoize_preserves_goodInv expand decWit chalToIdx
        Rel checkRel q s hs a next hnext)
      P (([], []), false) (fun _ => ⟨List.Pairwise.nil, by simp⟩) res st_mid hmem hclean
  have hle_comb :
      (voleithKSFailurePMF expand decWit chalToIdx Rel checkRel P) true ≤
        (ProbOracleComp.runWith S combined (([], []), false)).toOuterMeasure
          {x | OracleComp.FlagBad x.2} := by
    rw [hks_eq, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_bind_apply,
      show combined = P >>= (fun sp => voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel
        sp.1 sp.2) from rfl,
      ProbOracleComp.runWith_bind, PMF.toOuterMeasure_bind_apply]
    refine tsum_le_tsum fun x => ?_
    rcases x with ⟨⟨stmt, prf⟩, st_mid⟩
    by_cases hsupp1 : ((stmt, prf), st_mid) ∈ (ProbOracleComp.runWith S P (([], []), false)).support
    · gcongr
      rw [PMF.toOuterMeasure_map_apply]
      simp only [PMF.toOuterMeasure_apply, OracleComp.FlagBad]
      refine tsum_le_tsum fun y => ?_
      rcases y with ⟨ok, st_end⟩
      by_cases hsupp2 : (ok, st_end) ∈
          (ProbOracleComp.runWith S (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel
            stmt prf) st_mid).support
      · by_cases heq :
            (ok && !Rel stmt (extractWitnessFromTrace expand decWit st_mid.1.1 prf)) = true
        · have hok : ok = true := by simp_all
          have hrel_f :
              Rel stmt (extractWitnessFromTrace expand decWit st_mid.1.1 prf) = false := by
            simp_all
          have hbad_end : st_end.2 = true := by
            by_contra hclean_end
            have hc_end : st_end.2 = false := Bool.eq_false_iff.mpr hclean_end
            have hc_mid : st_mid.2 = false := by
              by_contra htm
              have hbm : OracleComp.FlagBad st_mid := by
                cases hsm : st_mid.2 <;> simp_all [OracleComp.FlagBad]
              have hbe := ProbOracleComp.runWith_invariant _ (fun s => OracleComp.FlagBad s)
                (fun q s hs a next hx => by
                  rcases s with ⟨s₁, sb⟩
                  dsimp only [OracleComp.FlagBad] at hs
                  subst hs
                  exact OracleComp.isFlagMonotone_withBadFlag _ q s₁ (a, next) hx)
                _ st_mid hbm ok st_end hsupp2
              simp [OracleComp.FlagBad, hc_end] at hbe
            have hinv_mid := hinvP (stmt, prf) st_mid hsupp1 hc_mid
            rcases st_mid with ⟨ro_mid, b_mid⟩
            dsimp only at hc_mid hinv_mid hrel_f
            subst hc_mid
            have hgood_rel := voleithVerifyROM_sound_of_clean expand decWit chalToIdx Rel checkRel
              stmt prf ro_mid st_end hinv_mid (hok ▸ hsupp2) hc_end
            exact absurd (hgood_rel.symm.trans hrel_f) (by decide)
          simp [heq, hbad_end]
        · simp [heq]
      · have hz : (ProbOracleComp.runWith S (voleithVerifyROM (Chal := Chal) expand chalToIdx
            checkRel stmt prf) st_mid) (ok, st_end) = 0 :=
          (PMF.apply_eq_zero_iff _ _).mpr hsupp2
        simp [Set.indicator_apply, hz]
    · have hz : (ProbOracleComp.runWith S P (([], []), false)) ((stmt, prf), st_mid) = 0 :=
        (PMF.apply_eq_zero_iff _ _).mpr hsupp1
      simp [hz]
  exact hle_comb.trans hbad_bound

/-- Oracle specification for an adaptive `m`-call `VOLEitH` verification oracle alongside
`VOLEITHROSpec`. -/
abbrev VOLEITHVerifyOracleSpec (d comLen rowLen : ℕ) (Stmt Seed IV PreMsg : Type) :
    OracleSpec (Stmt × VOLEITHProof d comLen rowLen Seed IV PreMsg) :=
  fun _ => Bool

/-- Combined oracle allowing adaptive queries to both `Verify` (`Sum.inl`) and `VOLEITHROSpec`
(`Sum.inr`). -/
abbrev VOLEITHMultiVerifySpec (d sdLen comLen rowLen : ℕ)
    (Stmt Seed IV PreMsg Chal : Type) :=
  VOLEITHVerifyOracleSpec d comLen rowLen Stmt Seed IV PreMsg ⊕ₒ
    VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal

/-- State of the multi-verify tracking oracle: `(roState, anyExtractFailure)`. -/
abbrev VOLEITHMultiVerifyState (d sdLen comLen rowLen : ℕ)
    (Stmt Seed IV PreMsg Chal : Type) :=
  VOLEITHTraceState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal × Bool

/-- Adaptive multi-verify handler running `voleithVerifyROM` on shared lazy ROM `voleithMemoize`
and recording `anyExtractFailure = true` if any verified proof fails straight-line witness
extraction against the `H_leaf` trace captured *before* verification. -/
@[expose] noncomputable def voleithMultiVerifyHandler {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool) :
    (q : (Stmt × VOLEITHProof d comLen rowLen Seed IV PreMsg) ⊕
        (LeafQuery d Seed IV ⊕ FSQuery d comLen rowLen Stmt IV PreMsg)) →
      StateT (VOLEITHMultiVerifyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) PMF
        (VOLEITHMultiVerifySpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal q)
  | .inl (stmt, prf), (roSt, failed) =>
    (ProbOracleComp.runWith voleithMemoize
      (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel stmt prf) roSt).map
      fun (ok, roSt') =>
        let stepFail := ok && !Rel stmt (extractWitnessFromTrace expand decWit roSt.1 prf)
        (ok, (roSt', failed || stepFail))
  | .inr qRO, (roSt, failed) =>
    (voleithMemoize qRO roSt).map fun (ans, roSt') => (ans, (roSt', failed))

private noncomputable def voleithMultiVerifyStickyHandler {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool) :
    (q : (Stmt × VOLEITHProof d comLen rowLen Seed IV PreMsg) ⊕
        (LeafQuery d Seed IV ⊕ FSQuery d comLen rowLen Stmt IV PreMsg)) →
      StateT (VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal × Bool) PMF
        (VOLEITHMultiVerifySpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal q)
  | .inl (stmt, prf), (s, failed) =>
    (ProbOracleComp.runWith (voleithStickyMemoize expand decWit chalToIdx Rel checkRel)
      (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel stmt prf) s).map
      fun (ok, s') =>
        let stepFail := ok && !Rel stmt (extractWitnessFromTrace expand decWit s.1.1 prf)
        (ok, (s', failed || stepFail))
  | .inr qRO, (s, failed) =>
    (voleithStickyMemoize expand decWit chalToIdx Rel checkRel qRO s).map
      fun (ans, s') => (ans, (s', failed))

private def mvDropFlag {d sdLen comLen rowLen : ℕ} {Stmt Seed IV PreMsg Chal : Type}
    (x : VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal × Bool) :
    VOLEITHMultiVerifyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal :=
  (x.1.1, x.2)

private theorem voleithMultiVerifyStickyHandler_map_forget {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (q : (Stmt × VOLEITHProof d comLen rowLen Seed IV PreMsg) ⊕
        (LeafQuery d Seed IV ⊕ FSQuery d comLen rowLen Stmt IV PreMsg))
    (x : VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal × Bool) :
    (voleithMultiVerifyStickyHandler expand decWit chalToIdx Rel checkRel q x).map
        (Prod.map id mvDropFlag) =
      voleithMultiVerifyHandler expand decWit chalToIdx Rel checkRel q (mvDropFlag x) := by
  rcases x with ⟨⟨roSt, b⟩, failed⟩
  rcases q with ⟨stmt, prf⟩ | qRO
  · simp only [voleithMultiVerifyStickyHandler, voleithMultiVerifyHandler, mvDropFlag,
      PMF.map_comp]
    have hforget := voleithStickyMemoize_map_forget expand decWit chalToIdx Rel checkRel
      (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel stmt prf) roSt b
    calc
      (ProbOracleComp.runWith (voleithStickyMemoize expand decWit chalToIdx Rel checkRel)
          (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel stmt prf) (roSt, b)).map
          (Prod.map id mvDropFlag ∘ fun (ok, s') =>
            (ok, (s', failed || (ok && !Rel stmt
              (extractWitnessFromTrace expand decWit roSt.1 prf))))) =
        ((ProbOracleComp.runWith (voleithStickyMemoize expand decWit chalToIdx Rel checkRel)
            (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel stmt prf) (roSt, b)).map
            (Prod.map id Prod.fst)).map
          (fun (ok, roSt') => (ok, (roSt', failed || (ok && !Rel stmt
            (extractWitnessFromTrace expand decWit roSt.1 prf))))) := by
        rw [PMF.map_comp]
        rfl
      _ = _ := by rw [hforget]
  · simp only [voleithMultiVerifyStickyHandler, voleithMultiVerifyHandler, mvDropFlag,
      voleithStickyMemoize]
    have hstep := OracleComp.withBadFlag_map_fst
      (voleithStepKernel expand decWit chalToIdx Rel checkRel) qRO roSt b
    have hk := voleithStepKernel_map_fst expand decWit chalToIdx Rel checkRel qRO roSt
    calc
      ((OracleComp.withBadFlag (voleithStepKernel expand decWit chalToIdx Rel checkRel) qRO
          (roSt, b)).map fun (ans, s') => (ans, (s', failed))).map (Prod.map id mvDropFlag) =
        ((OracleComp.withBadFlag (voleithStepKernel expand decWit chalToIdx Rel checkRel) qRO
            (roSt, b)).map (Prod.map id Prod.fst)).map fun (ans, roSt') =>
          (ans, (roSt', failed)) := by
        rw [PMF.map_comp, PMF.map_comp]
        rfl
      _ = _ := by rw [hstep, hk]

private theorem voleithMultiVerifyStickyHandler_invariant {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit : Type}
    [BEq (LeafQuery d Seed IV)] [LawfulBEq (LeafQuery d Seed IV)]
    [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [LawfulBEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (q : (Stmt × VOLEITHProof d comLen rowLen Seed IV PreMsg) ⊕
        (LeafQuery d Seed IV ⊕ FSQuery d comLen rowLen Stmt IV PreMsg))
    (x : VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal × Bool)
    (hinv : x.1.2 = false →
      x.2 = false ∧ VOLEITHGoodInv expand decWit chalToIdx Rel checkRel x.1.1)
    (a : VOLEITHMultiVerifySpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal q)
    (x' : VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal × Bool)
    (hx' : (a, x') ∈
      (voleithMultiVerifyStickyHandler expand decWit chalToIdx Rel checkRel q x).support)
    (hclean' : x'.1.2 = false) :
    x'.2 = false ∧ VOLEITHGoodInv expand decWit chalToIdx Rel checkRel x'.1.1 := by
  rcases x with ⟨s, failed⟩
  rcases q with ⟨stmt, prf⟩ | qRO
  · simp only [voleithMultiVerifyStickyHandler, PMF.mem_support_map_iff, Prod.mk.injEq] at hx'
    obtain ⟨⟨ok, s'⟩, hs'_mem, ha_eq, hx'_eq⟩ := hx'
    rw [← hx'_eq] at hclean' ⊢
    dsimp only at hclean' ⊢
    have hclean_s : s.2 = false := by
      by_contra hts
      have hbs : OracleComp.FlagBad s := by cases hsb : s.2 <;> simp_all [OracleComp.FlagBad]
      have hbe := ProbOracleComp.runWith_invariant _ (fun st => OracleComp.FlagBad st)
        (fun q' st' hst' a' next' hnext' => by
          rcases st' with ⟨s₁, sb⟩
          dsimp only [OracleComp.FlagBad] at hst'
          subst hst'
          exact OracleComp.isFlagMonotone_withBadFlag _ q' s₁ (a', next') hnext')
        _ s hbs ok s' hs'_mem
      simp [OracleComp.FlagBad, hclean'] at hbe
    obtain ⟨hfail_f, hinv_s⟩ := hinv hclean_s
    dsimp only at hfail_f hinv_s
    have hinv_s' : VOLEITHGoodInv expand decWit chalToIdx Rel checkRel s'.1 :=
      ProbOracleComp.runWith_invariant _
        (fun st => st.2 = false → VOLEITHGoodInv expand decWit chalToIdx Rel checkRel st.1)
        (fun q' st' hst' a' next' hnext' => voleithStickyMemoize_preserves_goodInv expand decWit
          chalToIdx Rel checkRel q' st' hst' a' next' hnext')
        _ s (fun _ => hinv_s) ok s' hs'_mem hclean'
    refine ⟨?_, hinv_s'⟩
    cases ok with
    | false => simp [hfail_f]
    | true =>
      rcases s with ⟨ro_s, b_s⟩
      dsimp only at hclean_s hinv_s
      subst hclean_s
      have hrel := voleithVerifyROM_sound_of_clean expand decWit chalToIdx Rel checkRel stmt prf
        ro_s s' hinv_s hs'_mem hclean'
      simp [hfail_f, hrel]
  · simp only [voleithMultiVerifyStickyHandler, PMF.mem_support_map_iff, Prod.mk.injEq] at hx'
    obtain ⟨⟨ans, s'⟩, hs'_mem, _, hx'_eq⟩ := hx'
    rw [← hx'_eq] at hclean' ⊢
    dsimp only at hclean' ⊢
    have hclean_s : s.2 = false := by
      by_contra hts
      have hbs : OracleComp.FlagBad s := by cases hsb : s.2 <;> simp_all [OracleComp.FlagBad]
      have hbe := OracleComp.isFlagMonotone_withBadFlag
        (voleithStepKernel expand decWit chalToIdx Rel checkRel) qRO s.1 (ans, s')
        (hbs ▸ hs'_mem)
      simp [OracleComp.FlagBad, hclean'] at hbe
    obtain ⟨hfail_f, hinv_s⟩ := hinv hclean_s
    dsimp only at hfail_f hinv_s
    exact ⟨hfail_f, voleithStickyMemoize_preserves_goodInv expand decWit chalToIdx Rel checkRel
      qRO s (fun _ => hinv_s) ans s' hs'_mem hclean'⟩

private def mvLeafCost {d comLen rowLen : ℕ} {Stmt Seed IV PreMsg : Type} :
    (Stmt × VOLEITHProof d comLen rowLen Seed IV PreMsg) ⊕
      (LeafQuery d Seed IV ⊕ FSQuery d comLen rowLen Stmt IV PreMsg) → ℕ
  | .inl _ => 2 ^ d - 1
  | .inr qRO => voleithLeafCost qRO

private def mvFSCost {d comLen rowLen : ℕ} {Stmt Seed IV PreMsg : Type} :
    (Stmt × VOLEITHProof d comLen rowLen Seed IV PreMsg) ⊕
      (LeafQuery d Seed IV ⊕ FSQuery d comLen rowLen Stmt IV PreMsg) → ℕ
  | .inl _ => 1
  | .inr qRO => voleithFSCost qRO

private theorem voleithStepKernel_trace_len_le {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (q : LeafQuery d Seed IV ⊕ FSQuery d comLen rowLen Stmt IV PreMsg)
    (tr : VOLEITHTraceState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal)
    (a : VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal q)
    (s' : VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal)
    (hs' : (a, s') ∈
      (voleithStepKernel expand decWit chalToIdx Rel checkRel q tr).support) :
    s'.1.1.length ≤ tr.1.length + voleithLeafCost q ∧
      s'.1.2.length ≤ tr.2.length + voleithFSCost q := by
  rcases tr with ⟨tr₁, tr₂⟩
  rcases q with ql | qf
  · dsimp only [voleithStepKernel] at hs'
    cases hlook : tr₁.lookup ql
    · rw [hlook] at hs'
      simp only [PMF.mem_support_map_iff, Prod.mk.injEq] at hs'
      obtain ⟨_, -, _, rfl⟩ := hs'
      simp [voleithLeafCost, voleithFSCost]
    · rw [hlook] at hs'
      simp only [PMF.mem_support_pure_iff, Prod.mk.injEq] at hs'
      obtain ⟨_, rfl⟩ := hs'
      simp [voleithLeafCost, voleithFSCost]
  · dsimp only [voleithStepKernel] at hs'
    cases hlook : tr₂.lookup qf
    · rw [hlook] at hs'
      simp only [PMF.mem_support_map_iff, Prod.mk.injEq] at hs'
      obtain ⟨_, -, _, rfl⟩ := hs'
      simp [voleithLeafCost, voleithFSCost]
    · rw [hlook] at hs'
      simp only [PMF.mem_support_pure_iff, Prod.mk.injEq] at hs'
      obtain ⟨_, rfl⟩ := hs'
      simp [voleithLeafCost, voleithFSCost]

private theorem voleithStickyMemoize_trace_len_le {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit β : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    {prog : ProbOracleComp (VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) β}
    {k₁ k₂ : ℕ}
    (h1 : IsCostBounded (Sum.elim (fun _ => 0) voleithLeafCost) prog k₁)
    (h2 : IsCostBounded (Sum.elim (fun _ => 0) voleithFSCost) prog k₂)
    (s s' : VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal)
    (r : β)
    (hsupp : (r, s') ∈
      (ProbOracleComp.runWith (voleithStickyMemoize expand decWit chalToIdx Rel checkRel)
        prog s).support) :
    s'.1.1.length ≤ s.1.1.length + k₁ ∧ s'.1.2.length ≤ s.1.2.length + k₂ := by
  rw [ProbOracleComp.runWith_eq_run_interpret] at hsupp
  have hstep :
      ∀ (q : ℕ ⊕ (LeafQuery d Seed IV ⊕ FSQuery d comLen rowLen Stmt IV PreMsg))
        (t : VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal)
        a t',
      (a, t') ∈ (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n))
        (voleithStickyMemoize (Seed := Seed) (IV := IV)
          expand decWit chalToIdx Rel checkRel) q t).support →
      t'.1.1.length ≤ t.1.1.length + (Sum.elim (fun _ => 0) voleithLeafCost) q ∧
        t'.1.2.length ≤ t.1.2.length + (Sum.elim (fun _ => 0) voleithFSCost) q := by
    intro q t a t' ht
    rcases q with m | qRO
    · change (a, t') ∈ ((ProbComp.unifOracle m).map (·, t)).support at ht
      rcases (PMF.mem_support_map_iff _ _ _).mp ht with ⟨_, -, heq⟩
      obtain ⟨_, rfl⟩ := Prod.mk.inj heq
      simp
    · rcases t with ⟨tr, b⟩
      cases b
      · simp only [OracleComp.sumHandler, voleithStickyMemoize,
          OracleComp.withBadFlag_false] at ht
        exact voleithStepKernel_trace_len_le expand decWit chalToIdx Rel checkRel qRO tr a t' ht
      · simp only [OracleComp.sumHandler, voleithStickyMemoize, OracleComp.withBadFlag,
          PMF.mem_support_map_iff] at ht
        obtain ⟨⟨ans, st_k⟩, hk_mem, heq⟩ := ht
        obtain ⟨_, rfl⟩ := Prod.mk.inj heq
        exact voleithStepKernel_trace_len_le expand decWit chalToIdx Rel checkRel qRO tr ans st_k
          hk_mem
  exact ⟨OracleComp.IsCostBounded.measure_le h1 _
      (fun st : VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal => st.1.1.length)
      (fun q t a t' ht => (hstep q t a t' ht).1) hsupp,
    OracleComp.IsCostBounded.measure_le h2 _
      (fun st : VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal => st.1.2.length)
      (fun q t a t' ht => (hstep q t a t' ht).2) hsupp⟩

private theorem toOuterMeasure_run_mvSticky_bad_le {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit α : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    {ε_rel : ℝ≥0}
    (hSound : VOLEITHSoundnessError decWit chalToIdx Rel checkRel ε_rel)
    (prog : ProbOracleComp (VOLEITHMultiVerifySpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal)
      α) :
    ∀ {k₁ k₂ : ℕ},
      IsCostBounded (Sum.elim (fun _ => 0) mvLeafCost) prog k₁ →
      IsCostBounded (Sum.elim (fun _ => 0) mvFSCost) prog k₂ →
      ∀ (s : VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) (failed : Bool),
        s.2 = false →
        (ProbOracleComp.runWith
            (voleithMultiVerifyStickyHandler expand decWit chalToIdx Rel checkRel)
            prog (s, failed)).toOuterMeasure {x | OracleComp.FlagBad x.2.1} ≤
          (k₁ : ℝ≥0∞) *
              (voleithBudget s +
                (k₁ : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ comLen) +
                (k₂ : ℝ≥0∞) * ((2 ^ d : ℝ≥0∞) / 2 ^ comLen)) +
            (k₂ : ℝ≥0∞) * (ε_rel : ℝ≥0∞) := by
  induction prog using OracleComp.induction with
  | pure a =>
    intro k₁ k₂ _ _ s failed hclean
    simp [ProbOracleComp.runWith_pure, OracleComp.FlagBad, hclean]
  | query_bind q cont ih =>
    intro k₁ k₂ hk₁ hk₂ s failed hclean
    rw [PFunctor.FreeM.bind_eq_bind] at hk₁ hk₂ ⊢
    obtain ⟨hq1, hcont1⟩ := IsCostBounded.liftBind_iff.mp hk₁
    obtain ⟨hq2, hcont2⟩ := IsCostBounded.liftBind_iff.mp hk₂
    rw [ProbOracleComp.runWith_bind]
    have hsplit : ∀ {κ : Type}
        (μ : PMF (κ ×
          (VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal × Bool)))
        (nxt : κ × (VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal × Bool) →
          PMF (α × (VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal × Bool))),
        (μ.bind nxt).toOuterMeasure {x | OracleComp.FlagBad x.2.1} ≤
        μ.toOuterMeasure {y | OracleComp.FlagBad y.2.1} +
          ∑' y, μ y * if OracleComp.FlagBad y.2.1 then 0 else
            (nxt y).toOuterMeasure {x | OracleComp.FlagBad x.2.1} := by
      intro κ μ nxt
      rw [PMF.toOuterMeasure_bind_apply]
      calc
        (∑' y, μ y * (nxt y).toOuterMeasure {x | OracleComp.FlagBad x.2.1}) ≤
            ∑' y, ((if OracleComp.FlagBad y.2.1 then μ y else 0) +
              μ y * if OracleComp.FlagBad y.2.1 then 0 else
                (nxt y).toOuterMeasure {x | OracleComp.FlagBad x.2.1}) := by
          refine tsum_le_tsum fun y => ?_
          dsimp only [OracleComp.FlagBad]
          by_cases hbad : y.2.1.2 = true
          · rw [ite_eq_left_iff.mpr (fun h => absurd hbad h),
              ite_eq_left_iff.mpr (fun h => absurd hbad h), mul_zero, add_zero]
            exact mul_le_of_le_one_right zero_le (PMF.toOuterMeasure_le_one _ _)
          · rw [ite_eq_right_iff.mpr (fun h => absurd h hbad),
              ite_eq_right_iff.mpr (fun h => absurd h hbad), zero_add]
        _ = μ.toOuterMeasure {y | OracleComp.FlagBad y.2.1} +
              ∑' y, μ y * if OracleComp.FlagBad y.2.1 then 0 else
                (nxt y).toOuterMeasure {x | OracleComp.FlagBad x.2.1} := by
          rw [tsum_add]
          congr 1
          simp only [PMF.toOuterMeasure_apply, Set.indicator_apply, Set.mem_ofPred_eq]
    have htsum : ∀ {κ : Type}
        (M : PMF (κ ×
          (VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal × Bool)))
        (nxt : κ → ProbOracleComp (VOLEITHMultiVerifySpec d sdLen comLen rowLen
          Stmt Seed IV PreMsg Chal) α)
        {C : ℝ≥0∞},
        (∀ y s' f', (y, (s', f')) ∈ M.support → s'.2 = false →
          (ProbOracleComp.runWith
            (voleithMultiVerifyStickyHandler expand decWit chalToIdx Rel checkRel)
            (nxt y) (s', f')).toOuterMeasure {x | OracleComp.FlagBad x.2.1} ≤ C) →
        (∑' y, M y * if OracleComp.FlagBad y.2.1 then 0 else
          (ProbOracleComp.runWith
            (voleithMultiVerifyStickyHandler expand decWit chalToIdx Rel checkRel)
            (nxt y.1) y.2).toOuterMeasure {x | OracleComp.FlagBad x.2.1}) ≤ C := by
      intro κ M nxt C hstep
      refine (tsum_le_tsum (g := fun y => M y * C) fun ⟨y, ⟨s', f'⟩⟩ => ?_).trans ?_
      · by_cases hy : (y, (s', f')) ∈ M.support
        · by_cases hclean' : s'.2 = false
          · simp only [OracleComp.FlagBad, hclean', Bool.false_eq_true, ↓reduceIte]
            gcongr
            exact hstep y s' f' hy hclean'
          · have htrue : s'.2 = true := by cases hsp : s'.2 <;> simp_all
            simp [OracleComp.FlagBad, htrue]
        · have hz := (PMF.apply_eq_zero_iff _ _).mpr hy
          simp [hz]
      · rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    cases q with
    | inl m =>
      have hbad0 :
          (ProbOracleComp.runWith
            (voleithMultiVerifyStickyHandler expand decWit chalToIdx Rel checkRel)
            (OracleComp.query (Sum.inl m)) (s, failed)).toOuterMeasure
            {y | OracleComp.FlagBad y.2.1} = 0 := by
        rw [PMF.toOuterMeasure_apply_eq_zero_iff]
        refine Set.disjoint_left.mpr fun y hy hbad => ?_
        change y ∈ (ProbOracleComp.runWith _ (ProbOracleComp.sample (ProbComp.unifFin m))
          (s, failed)).support at hy
        rw [ProbOracleComp.runWith_sample, PMF.mem_support_map_iff] at hy
        obtain ⟨_, -, rfl⟩ := hy
        simp [OracleComp.FlagBad, hclean] at hbad
      refine (hsplit _ _).trans ?_
      rw [hbad0, zero_add]
      have hsum_le :
          (∑' y, (ProbOracleComp.runWith
            (voleithMultiVerifyStickyHandler expand decWit chalToIdx Rel checkRel)
            (OracleComp.query (Sum.inl m)) (s, failed)) y *
              if OracleComp.FlagBad y.2.1 then 0 else
                (ProbOracleComp.runWith
                  (voleithMultiVerifyStickyHandler expand decWit chalToIdx Rel checkRel)
                  (cont y.1) y.2).toOuterMeasure {x | OracleComp.FlagBad x.2.1}) ≤
            ∑' y, (ProbOracleComp.runWith
              (voleithMultiVerifyStickyHandler expand decWit chalToIdx Rel checkRel)
              (OracleComp.query (Sum.inl m)) (s, failed)) y *
              ((k₁ : ℝ≥0∞) * (voleithBudget s +
                (k₁ : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ comLen) +
                (k₂ : ℝ≥0∞) * ((2 ^ d : ℝ≥0∞) / 2 ^ comLen)) +
                (k₂ : ℝ≥0∞) * (ε_rel : ℝ≥0∞)) := by
        refine tsum_le_tsum fun y => ?_
        by_cases hmem : y ∈ (ProbOracleComp.runWith
            (voleithMultiVerifyStickyHandler expand decWit chalToIdx Rel checkRel)
            (OracleComp.query (Sum.inl m)) (s, failed)).support
        · change y ∈ (ProbOracleComp.runWith _ (ProbOracleComp.sample (ProbComp.unifFin m))
            (s, failed)).support at hmem
          rw [ProbOracleComp.runWith_sample, PMF.mem_support_map_iff] at hmem
          obtain ⟨r, -, rfl⟩ := hmem
          simp only [OracleComp.FlagBad, hclean, Bool.false_eq_true, ↓reduceIte]
          have hc1 := hcont1 r
          have hc2 := hcont2 r
          simp only [Sum.elim_inl, Nat.sub_zero] at hc1 hc2
          gcongr
          exact ih r hc1 hc2 s failed hclean
        · have hz := (PMF.apply_eq_zero_iff _ _).mpr hmem
          simp [hz]
      refine hsum_le.trans ?_
      rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    | inr qext =>
      rcases qext with ⟨stmt, prf⟩ | qRO
      · have hk1_le : 2 ^ d - 1 ≤ k₁ := by
          dsimp only [Sum.elim_inr, mvLeafCost] at hq1
          exact hq1
        have hk2_le : 1 ≤ k₂ := by
          dsimp only [Sum.elim_inr, mvFSCost] at hq2
          exact hq2
        rcases s with ⟨tr, b⟩
        dsimp only at hclean
        subst hclean
        rw [ProbOracleComp.runWith_eq_run_interpret, OracleComp.run_interpret_query,
          OracleComp.sumHandler_inr]
        dsimp only [voleithMultiVerifyStickyHandler]
        let V := voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel stmt prf
        let hV_leaf := isCostBounded_leaf_voleithVerifyROM (Chal := Chal) expand chalToIdx
          checkRel stmt prf
        let hV_fs := isCostBounded_fs_voleithVerifyROM (Chal := Chal) expand chalToIdx
          checkRel stmt prf
        let δ₁ : ℝ≥0∞ := (1 : ℝ≥0∞) / 2 ^ comLen
        let δ₂ : ℝ≥0∞ := (2 ^ d : ℝ≥0∞) / 2 ^ comLen
        let Δ : ℝ≥0∞ := (2 ^ d - 1 : ℕ) * δ₁ + (1 : ℝ≥0∞) * δ₂
        have hstep_bad :
            ((ProbOracleComp.runWith (voleithStickyMemoize expand decWit chalToIdx Rel checkRel)
                V (tr, false)).map
              fun (ok, s') => (ok, (s', failed || (ok && !Rel stmt
                (extractWitnessFromTrace expand decWit tr.1 prf))))).toOuterMeasure
                {y | OracleComp.FlagBad y.2.1} ≤
              ((2 ^ d - 1 : ℕ) : ℝ≥0∞) * (voleithBudget (tr, false) + Δ) +
                (1 : ℝ≥0∞) * (ε_rel : ℝ≥0∞) := by
          rw [PMF.toOuterMeasure_map_apply]
          have hsub : (fun (ok, s') => (ok, (s', failed || (ok && !Rel stmt
              (extractWitnessFromTrace expand decWit tr.1 prf))))) ⁻¹'
                {y | OracleComp.FlagBad y.2.1} ⊆
              {x : Bool × VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal |
                OracleComp.FlagBad x.2} := fun ⟨_, _⟩ hx => hx
          refine ((ProbOracleComp.runWith
            (voleithStickyMemoize expand decWit chalToIdx Rel checkRel)
            V (tr, false)).toOuterMeasure.mono hsub).trans ?_
          simpa [Δ, δ₁, δ₂, voleithBudget, Nat.cast_one, add_assoc] using
            toOuterMeasure_runWith_voleithStickyMemoize_bad_le_of_state expand decWit chalToIdx
              Rel checkRel hSound hV_leaf hV_fs tr
        have hgrow_V : ∀ ok s', (ok, s') ∈
            (ProbOracleComp.runWith (voleithStickyMemoize expand decWit chalToIdx Rel checkRel)
              V (tr, false)).support →
            voleithBudget s' ≤ voleithBudget (tr, false) + Δ := by
          intro ok s' hs'
          obtain ⟨hlen1, hlen2⟩ := voleithStickyMemoize_trace_len_le expand decWit chalToIdx Rel
            checkRel hV_leaf hV_fs (tr, false) s' ok hs'
          dsimp only [voleithBudget, Δ, δ₁, δ₂]
          have hnum : ((s'.1.1.length + 2 ^ d * s'.1.2.length : ℕ) : ℝ≥0∞) ≤
              ((tr.1.length + 2 ^ d * tr.2.length : ℕ) : ℝ≥0∞) +
                ((2 ^ d - 1 : ℕ) : ℝ≥0∞) * 1 + (2 ^ d : ℝ≥0∞) := by
            have hnat : s'.1.1.length + 2 ^ d * s'.1.2.length ≤
                (tr.1.length + (2 ^ d - 1)) + 2 ^ d * (tr.2.length + 1) := by
              have hmul := Nat.mul_le_mul_left (2 ^ d) hlen2
              dsimp only at hlen1 hmul
              exact Nat.add_le_add hlen1 hmul
            calc
              ((s'.1.1.length + 2 ^ d * s'.1.2.length : ℕ) : ℝ≥0∞) ≤
                  (((tr.1.length + (2 ^ d - 1)) + 2 ^ d * (tr.2.length + 1) : ℕ) : ℝ≥0∞) := by
                exact_mod_cast hnat
              _ = ((tr.1.length + 2 ^ d * tr.2.length : ℕ) : ℝ≥0∞) +
                    ((2 ^ d - 1 : ℕ) : ℝ≥0∞) * 1 + (2 ^ d : ℝ≥0∞) := by
                push_cast
                ring
          calc
            ((s'.1.1.length + 2 ^ d * s'.1.2.length : ℕ) : ℝ≥0∞) / 2 ^ comLen ≤
                (((tr.1.length + 2 ^ d * tr.2.length : ℕ) : ℝ≥0∞) +
                  ((2 ^ d - 1 : ℕ) : ℝ≥0∞) * 1 + (2 ^ d : ℝ≥0∞)) / 2 ^ comLen := by
              gcongr
            _ = _ := by
              simp only [div_eq_mul_inv, one_mul]
              ring
        refine (hsplit _ _).trans ?_
        have hcont_sum :
            (∑' y, ((ProbOracleComp.runWith
                (voleithStickyMemoize expand decWit chalToIdx Rel checkRel) V (tr, false)).map
                fun (ok, s') => (ok, (s', failed || (ok && !Rel stmt
                  (extractWitnessFromTrace expand decWit tr.1 prf))))) y *
              if OracleComp.FlagBad y.2.1 then 0 else
                (ProbOracleComp.runWith
                  (voleithMultiVerifyStickyHandler expand decWit chalToIdx Rel checkRel)
                  (cont y.1) y.2).toOuterMeasure {x | OracleComp.FlagBad x.2.1}) ≤
            ((k₁ - (2 ^ d - 1) : ℕ) : ℝ≥0∞) *
              (voleithBudget (tr, false) + (k₁ : ℝ≥0∞) * δ₁ + (k₂ : ℝ≥0∞) * δ₂) +
              ((k₂ - 1 : ℕ) : ℝ≥0∞) * (ε_rel : ℝ≥0∞) := by
          refine htsum _ cont fun ok s' _ hy hclean' => ?_
          rw [PMF.mem_support_map_iff] at hy
          obtain ⟨⟨ok0, s0⟩, hs'_mem, heq⟩ := hy
          simp only [Prod.mk.injEq] at heq
          rcases heq with ⟨rfl, rfl, rfl⟩
          have hc1 := hcont1 ok0
          have hc2 := hcont2 ok0
          simp only [Sum.elim_inr, mvLeafCost, mvFSCost] at hc1 hc2
          have hih := ih ok0 hc1 hc2 s0 (failed || (ok0 && !Rel stmt
            (extractWitnessFromTrace expand decWit tr.1 prf))) hclean'
          have hg := hgrow_V ok0 s0 hs'_mem
          have hbud : voleithBudget s0 +
              ((k₁ - (2 ^ d - 1) : ℕ) : ℝ≥0∞) * δ₁ + ((k₂ - 1 : ℕ) : ℝ≥0∞) * δ₂ ≤
              voleithBudget (tr, false) + (k₁ : ℝ≥0∞) * δ₁ + (k₂ : ℝ≥0∞) * δ₂ := by
            have hk1_cast : ((k₁ - (2 ^ d - 1) : ℕ) : ℝ≥0∞) + ((2 ^ d - 1 : ℕ) : ℝ≥0∞) =
                (k₁ : ℝ≥0∞) := by
              exact_mod_cast Nat.sub_add_cancel hk1_le
            have hk2_cast : ((k₂ - 1 : ℕ) : ℝ≥0∞) + (1 : ℝ≥0∞) = (k₂ : ℝ≥0∞) := by
              exact_mod_cast Nat.sub_add_cancel hk2_le
            calc
              voleithBudget s0 + ((k₁ - (2 ^ d - 1) : ℕ) : ℝ≥0∞) * δ₁ +
                  ((k₂ - 1 : ℕ) : ℝ≥0∞) * δ₂ ≤
                (voleithBudget (tr, false) + Δ) + ((k₁ - (2 ^ d - 1) : ℕ) : ℝ≥0∞) * δ₁ +
                  ((k₂ - 1 : ℕ) : ℝ≥0∞) * δ₂ := by gcongr
              _ = voleithBudget (tr, false) +
                    (((k₁ - (2 ^ d - 1) : ℕ) : ℝ≥0∞) + ((2 ^ d - 1 : ℕ) : ℝ≥0∞)) * δ₁ +
                    (((k₂ - 1 : ℕ) : ℝ≥0∞) + (1 : ℝ≥0∞)) * δ₂ := by
                  dsimp only [Δ]
                  ring
              _ = voleithBudget (tr, false) + (k₁ : ℝ≥0∞) * δ₁ + (k₂ : ℝ≥0∞) * δ₂ := by
                  rw [hk1_cast, hk2_cast]
          exact hih.trans (by
            rw [show (1 : ℝ≥0∞) / 2 ^ comLen = δ₁ from rfl,
              show (2 ^ d : ℝ≥0∞) / 2 ^ comLen = δ₂ from rfl]
            gcongr)
        have hΔ_le : Δ ≤ (k₁ : ℝ≥0∞) * δ₁ + (k₂ : ℝ≥0∞) * δ₂ := by
          dsimp only [Δ]
          have h1 : ((2 ^ d - 1 : ℕ) : ℝ≥0∞) ≤ (k₁ : ℝ≥0∞) := by exact_mod_cast hk1_le
          have h2 : (1 : ℝ≥0∞) ≤ (k₂ : ℝ≥0∞) := by exact_mod_cast hk2_le
          gcongr
        have hk1_cast : ((2 ^ d - 1 : ℕ) : ℝ≥0∞) + ((k₁ - (2 ^ d - 1) : ℕ) : ℝ≥0∞) =
            (k₁ : ℝ≥0∞) := by
          exact_mod_cast Nat.add_sub_of_le hk1_le
        have hk2_cast : (1 : ℝ≥0∞) + ((k₂ - 1 : ℕ) : ℝ≥0∞) = (k₂ : ℝ≥0∞) := by
          exact_mod_cast Nat.add_sub_of_le hk2_le
        calc
          _ ≤ (((2 ^ d - 1 : ℕ) : ℝ≥0∞) * (voleithBudget (tr, false) + Δ) +
                (1 : ℝ≥0∞) * (ε_rel : ℝ≥0∞)) +
              (((k₁ - (2 ^ d - 1) : ℕ) : ℝ≥0∞) *
                (voleithBudget (tr, false) + (k₁ : ℝ≥0∞) * δ₁ + (k₂ : ℝ≥0∞) * δ₂) +
                ((k₂ - 1 : ℕ) : ℝ≥0∞) * (ε_rel : ℝ≥0∞)) := add_le_add hstep_bad hcont_sum
          _ ≤ (((2 ^ d - 1 : ℕ) : ℝ≥0∞) *
                (voleithBudget (tr, false) + (k₁ : ℝ≥0∞) * δ₁ + (k₂ : ℝ≥0∞) * δ₂) +
                (1 : ℝ≥0∞) * (ε_rel : ℝ≥0∞)) +
              (((k₁ - (2 ^ d - 1) : ℕ) : ℝ≥0∞) *
                (voleithBudget (tr, false) + (k₁ : ℝ≥0∞) * δ₁ + (k₂ : ℝ≥0∞) * δ₂) +
                ((k₂ - 1 : ℕ) : ℝ≥0∞) * (ε_rel : ℝ≥0∞)) := by
              have hle : voleithBudget (tr, false) + Δ ≤
                  voleithBudget (tr, false) + (k₁ : ℝ≥0∞) * δ₁ + (k₂ : ℝ≥0∞) * δ₂ := by
                rw [add_assoc]
                gcongr
              gcongr
          _ = (((2 ^ d - 1 : ℕ) : ℝ≥0∞) + ((k₁ - (2 ^ d - 1) : ℕ) : ℝ≥0∞)) *
                (voleithBudget (tr, false) + (k₁ : ℝ≥0∞) * δ₁ + (k₂ : ℝ≥0∞) * δ₂) +
              ((1 : ℝ≥0∞) + ((k₂ - 1 : ℕ) : ℝ≥0∞)) * (ε_rel : ℝ≥0∞) := by ring
          _ = _ := by rw [hk1_cast, hk2_cast]
      · have hc1_le : voleithLeafCost qRO ≤ k₁ := by
          dsimp only [Sum.elim_inr, mvLeafCost] at hq1
          exact hq1
        have hc2_le : voleithFSCost qRO ≤ k₂ := by
          dsimp only [Sum.elim_inr, mvFSCost] at hq2
          exact hq2
        have hnotbad : ¬ OracleComp.FlagBad s := by simp [OracleComp.FlagBad, hclean]
        rw [ProbOracleComp.runWith_eq_run_interpret, OracleComp.run_interpret_query,
          OracleComp.sumHandler_inr]
        dsimp only [voleithMultiVerifyStickyHandler]
        let δ₁ : ℝ≥0∞ := (1 : ℝ≥0∞) / 2 ^ comLen
        let δ₂ : ℝ≥0∞ := (2 ^ d : ℝ≥0∞) / 2 ^ comLen
        have hstep_bad :
            ((voleithStickyMemoize expand decWit chalToIdx Rel checkRel qRO s).map
              fun (ans, s') => (ans, (s', failed))).toOuterMeasure
                {y | OracleComp.FlagBad y.2.1} ≤
              (voleithLeafCost qRO : ℝ≥0∞) * voleithBudget s +
                (voleithFSCost qRO : ℝ≥0∞) * (ε_rel : ℝ≥0∞) := by
          rw [PMF.toOuterMeasure_map_apply]
          have hsub : (fun x : VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal qRO ×
              VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal =>
              (x.1, (x.2, failed))) ⁻¹' {y | OracleComp.FlagBad y.2.1} =
              {x | OracleComp.FlagBad x.2} := rfl
          rw [hsub]
          exact toOuterMeasure_voleithStickyMemoize_step_le expand decWit chalToIdx Rel checkRel
            hSound qRO s hnotbad
        refine (hsplit _ _).trans ?_
        have hcont_sum :
            (∑' y, ((voleithStickyMemoize expand decWit chalToIdx Rel checkRel qRO s).map
                fun (ans, s') => (ans, (s', failed))) y *
              if OracleComp.FlagBad y.2.1 then 0 else
                (ProbOracleComp.runWith
                  (voleithMultiVerifyStickyHandler expand decWit chalToIdx Rel checkRel)
                  (cont y.1) y.2).toOuterMeasure {x | OracleComp.FlagBad x.2.1}) ≤
            ((k₁ - voleithLeafCost qRO : ℕ) : ℝ≥0∞) *
              (voleithBudget s + (k₁ : ℝ≥0∞) * δ₁ + (k₂ : ℝ≥0∞) * δ₂) +
              ((k₂ - voleithFSCost qRO : ℕ) : ℝ≥0∞) * (ε_rel : ℝ≥0∞) := by
          refine htsum _ cont fun ans s' _ hy hclean' => ?_
          rw [PMF.mem_support_map_iff] at hy
          obtain ⟨⟨ans0, s0⟩, hs'_mem, heq⟩ := hy
          simp only [Prod.mk.injEq] at heq
          rcases heq with ⟨rfl, rfl, rfl⟩
          have hc1 := hcont1 ans0
          have hc2 := hcont2 ans0
          simp only [Sum.elim_inr, mvLeafCost, mvFSCost] at hc1 hc2
          have hih := ih ans0 hc1 hc2 s0 failed hclean'
          have hg := voleithBudget_grow expand decWit chalToIdx Rel checkRel qRO s hnotbad
            (ans0, s0) hs'_mem (by simp [OracleComp.FlagBad, hclean'])
          have hbud : voleithBudget s0 +
              ((k₁ - voleithLeafCost qRO : ℕ) : ℝ≥0∞) * δ₁ +
              ((k₂ - voleithFSCost qRO : ℕ) : ℝ≥0∞) * δ₂ ≤
              voleithBudget s + (k₁ : ℝ≥0∞) * δ₁ + (k₂ : ℝ≥0∞) * δ₂ := by
            have hk1_cast : ((k₁ - voleithLeafCost qRO : ℕ) : ℝ≥0∞) +
                (voleithLeafCost qRO : ℝ≥0∞) = (k₁ : ℝ≥0∞) := by
              exact_mod_cast Nat.sub_add_cancel hc1_le
            have hk2_cast : ((k₂ - voleithFSCost qRO : ℕ) : ℝ≥0∞) +
                (voleithFSCost qRO : ℝ≥0∞) = (k₂ : ℝ≥0∞) := by
              exact_mod_cast Nat.sub_add_cancel hc2_le
            calc
              voleithBudget s0 + ((k₁ - voleithLeafCost qRO : ℕ) : ℝ≥0∞) * δ₁ +
                  ((k₂ - voleithFSCost qRO : ℕ) : ℝ≥0∞) * δ₂ ≤
                (voleithBudget s + (voleithLeafCost qRO : ℝ≥0∞) * δ₁ +
                  (voleithFSCost qRO : ℝ≥0∞) * δ₂) +
                  ((k₁ - voleithLeafCost qRO : ℕ) : ℝ≥0∞) * δ₁ +
                  ((k₂ - voleithFSCost qRO : ℕ) : ℝ≥0∞) * δ₂ := by
                  gcongr
              _ = voleithBudget s +
                    (((k₁ - voleithLeafCost qRO : ℕ) : ℝ≥0∞) +
                      (voleithLeafCost qRO : ℝ≥0∞)) * δ₁ +
                    (((k₂ - voleithFSCost qRO : ℕ) : ℝ≥0∞) +
                      (voleithFSCost qRO : ℝ≥0∞)) * δ₂ := by ring
              _ = voleithBudget s + (k₁ : ℝ≥0∞) * δ₁ + (k₂ : ℝ≥0∞) * δ₂ := by
                  rw [hk1_cast, hk2_cast]
          exact hih.trans (by
            rw [show (1 : ℝ≥0∞) / 2 ^ comLen = δ₁ from rfl,
              show (2 ^ d : ℝ≥0∞) / 2 ^ comLen = δ₂ from rfl]
            gcongr)
        have hk1_cast : (voleithLeafCost qRO : ℝ≥0∞) +
            ((k₁ - voleithLeafCost qRO : ℕ) : ℝ≥0∞) = (k₁ : ℝ≥0∞) := by
          exact_mod_cast Nat.add_sub_of_le hc1_le
        have hk2_cast : (voleithFSCost qRO : ℝ≥0∞) +
            ((k₂ - voleithFSCost qRO : ℕ) : ℝ≥0∞) = (k₂ : ℝ≥0∞) := by
          exact_mod_cast Nat.add_sub_of_le hc2_le
        calc
          _ ≤ ((voleithLeafCost qRO : ℝ≥0∞) * voleithBudget s +
                (voleithFSCost qRO : ℝ≥0∞) * (ε_rel : ℝ≥0∞)) +
              (((k₁ - voleithLeafCost qRO : ℕ) : ℝ≥0∞) *
                (voleithBudget s + (k₁ : ℝ≥0∞) * δ₁ + (k₂ : ℝ≥0∞) * δ₂) +
                ((k₂ - voleithFSCost qRO : ℕ) : ℝ≥0∞) * (ε_rel : ℝ≥0∞)) :=
              add_le_add hstep_bad hcont_sum
          _ ≤ ((voleithLeafCost qRO : ℝ≥0∞) *
                (voleithBudget s + (k₁ : ℝ≥0∞) * δ₁ + (k₂ : ℝ≥0∞) * δ₂) +
                (voleithFSCost qRO : ℝ≥0∞) * (ε_rel : ℝ≥0∞)) +
              (((k₁ - voleithLeafCost qRO : ℕ) : ℝ≥0∞) *
                (voleithBudget s + (k₁ : ℝ≥0∞) * δ₁ + (k₂ : ℝ≥0∞) * δ₂) +
                ((k₂ - voleithFSCost qRO : ℕ) : ℝ≥0∞) * (ε_rel : ℝ≥0∞)) := by
              have hle : voleithBudget s ≤
                  voleithBudget s + (k₁ : ℝ≥0∞) * δ₁ + (k₂ : ℝ≥0∞) * δ₂ := by
                rw [add_assoc]
                exact le_self_add
              gcongr
          _ = ((voleithLeafCost qRO : ℝ≥0∞) + ((k₁ - voleithLeafCost qRO : ℕ) : ℝ≥0∞)) *
                (voleithBudget s + (k₁ : ℝ≥0∞) * δ₁ + (k₂ : ℝ≥0∞) * δ₂) +
              ((voleithFSCost qRO : ℝ≥0∞) + ((k₂ - voleithFSCost qRO : ℕ) : ℝ≥0∞)) *
                (ε_rel : ℝ≥0∞) := by ring
          _ = _ := by rw [hk1_cast, hk2_cast]

private theorem isCostBounded_mvLeafCost_add {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal α : Type}
    {P : ProbOracleComp (VOLEITHMultiVerifySpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) α}
    {Q_leaf m : ℕ}
    (hm : IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 0))) P m)
    (hleaf : IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 0) (voleithLeafCost (d := d) (comLen := comLen) (rowLen := rowLen)
        (Stmt := Stmt) (Seed := Seed) (IV := IV) (PreMsg := PreMsg)))) P Q_leaf) :
    IsCostBounded (Sum.elim (fun _ => 0)
      (mvLeafCost (d := d) (comLen := comLen) (rowLen := rowLen)
        (Stmt := Stmt) (Seed := Seed) (IV := IV) (PreMsg := PreMsg))) P
      (Q_leaf + m * (2 ^ d - 1)) := by
  refine (hleaf.add (IsCostBounded.mul_of_le
    (cost' := Sum.elim (fun _ => 0) (Sum.elim (fun _ => 2 ^ d - 1) (fun _ => 0)))
    hm fun q => ?_)).of_le fun q => ?_
  · rcases q with k | (⟨_, _⟩ | qRO) <;> simp
  · rcases q with k | (⟨_, _⟩ | qRO) <;> simp [mvLeafCost]

private theorem isCostBounded_mvFSCost_add {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal α : Type}
    {P : ProbOracleComp (VOLEITHMultiVerifySpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) α}
    {Q_FS m : ℕ}
    (hm : IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 0))) P m)
    (hfs : IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 0) (voleithFSCost (d := d) (comLen := comLen) (rowLen := rowLen)
        (Stmt := Stmt) (Seed := Seed) (IV := IV) (PreMsg := PreMsg)))) P Q_FS) :
    IsCostBounded (Sum.elim (fun _ => 0)
      (mvFSCost (d := d) (comLen := comLen) (rowLen := rowLen)
        (Stmt := Stmt) (Seed := Seed) (IV := IV) (PreMsg := PreMsg))) P (Q_FS + m) := by
  refine (hfs.add hm).of_le fun q => ?_
  rcases q with k | (⟨_, _⟩ | qRO) <;> simp [mvFSCost]

/-- **Adaptive multi-verify straight-line ROM extraction bound** (cf. [VOLEACT2026], Initial
Issuance / Spending): if an adaptive adversary `A` with access to a `Verify` oracle and
`VOLEITHROSpec` makes at most `m` verification queries, `Q_leaf` direct `H_leaf` queries, and
`Q_FS` direct `H_FS` queries, then along any run against `voleithMultiVerifyHandler`, the
probability that *any* verified-accepted proof fails `Rel` witness extraction from `tr_leaf` prior
to that verification call is at most
`voleithKSBound d comLen (Q_leaf + m * (2 ^ d - 1)) (Q_FS + m) ε_rel : ℝ≥0`. -/
theorem voleithMultiVerifyROM_sound_bound {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit α : Type}
    [BEq (LeafQuery d Seed IV)] [LawfulBEq (LeafQuery d Seed IV)]
    [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [LawfulBEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    {ε_rel : ℝ≥0}
    (hSound : VOLEITHSoundnessError decWit chalToIdx Rel checkRel ε_rel)
    (A : ProbOracleComp (VOLEITHMultiVerifySpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) α)
    {m Q_leaf Q_FS : ℕ}
    (hm : IsCostBounded
      (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 0))) A m)
    (hleaf : IsCostBounded
      (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) voleithLeafCost)) A Q_leaf)
    (hfs : IsCostBounded
      (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) voleithFSCost)) A Q_FS) :
    ((ProbOracleComp.runWith (voleithMultiVerifyHandler expand decWit chalToIdx Rel checkRel)
        A (([], []), false)).map fun (_, _, bad) => bad) true ≤
      (voleithKSBound d comLen (Q_leaf + m * (2 ^ d - 1)) (Q_FS + m) ε_rel : ℝ≥0∞) := by
  have hleaf_tot :
      IsCostBounded (Sum.elim (fun _ => 0) mvLeafCost) A (Q_leaf + m * (2 ^ d - 1)) :=
    isCostBounded_mvLeafCost_add hm hleaf
  have hfs_tot : IsCostBounded (Sum.elim (fun _ => 0) mvFSCost) A (Q_FS + m) :=
    isCostBounded_mvFSCost_add hm hfs
  have hmap :
      ((ProbOracleComp.runWith
          (voleithMultiVerifyStickyHandler expand decWit chalToIdx Rel checkRel)
          A ((([], []), false), false)).map (Prod.map id mvDropFlag)) =
        ProbOracleComp.runWith (voleithMultiVerifyHandler expand decWit chalToIdx Rel checkRel)
          A (([], []), false) :=
    ProbOracleComp.runWith_map_state _ _ mvDropFlag
      (voleithMultiVerifyStickyHandler_map_forget expand decWit chalToIdx Rel checkRel)
      A ((([], []), false), false)
  have hprob_eq :
      ((ProbOracleComp.runWith (voleithMultiVerifyHandler expand decWit chalToIdx Rel checkRel)
          A (([], []), false)).map fun (_, _, bad) => bad) true =
        ((ProbOracleComp.runWith
          (voleithMultiVerifyStickyHandler expand decWit chalToIdx Rel checkRel)
          A ((([], []), false), false)).map fun (_, _, bad) => bad) true := by
    rw [← hmap, PMF.map_comp]
    rfl
  rw [hprob_eq, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  have hinv_A :
      ∀ (a : α)
        (x' : VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal × Bool),
        (a, x') ∈
          (ProbOracleComp.runWith
            (voleithMultiVerifyStickyHandler expand decWit chalToIdx Rel checkRel)
            A ((([], []), false), false)).support →
        x'.1.2 = false → x'.2 = false := by
    intro a x' hx' hclean'
    exact (ProbOracleComp.runWith_invariant _
      (fun x => x.1.2 = false →
        x.2 = false ∧ VOLEITHGoodInv expand decWit chalToIdx Rel checkRel x.1.1)
      (voleithMultiVerifyStickyHandler_invariant expand decWit chalToIdx Rel checkRel)
      A ((([], []), false), false) (fun _ => ⟨rfl, List.Pairwise.nil, by simp⟩)
      a x' hx' hclean').1
  have hle_bad :
      (ProbOracleComp.runWith
          (voleithMultiVerifyStickyHandler expand decWit chalToIdx Rel checkRel)
          A ((([], []), false), false)).toOuterMeasure
            ((fun (_, (_, bad)) => bad :
              α × (VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal × Bool) →
                Bool) ⁻¹' {true}) ≤
        (ProbOracleComp.runWith
          (voleithMultiVerifyStickyHandler expand decWit chalToIdx Rel checkRel)
          A ((([], []), false), false)).toOuterMeasure {x | OracleComp.FlagBad x.2.1} := by
    simp only [PMF.toOuterMeasure_apply, OracleComp.FlagBad]
    refine tsum_le_tsum fun ⟨a, x'⟩ => ?_
    by_cases hmem : (a, x') ∈ (ProbOracleComp.runWith
        (voleithMultiVerifyStickyHandler expand decWit chalToIdx Rel checkRel)
        A ((([], []), false), false)).support
    · by_cases hfail : x'.2 = true
      · have hnotclean : x'.1.2 ≠ false := fun hc => by simp [hinv_A a x' hmem hc] at hfail
        have hbad : x'.1.2 = true := by cases hsb : x'.1.2 <;> simp_all
        simp [hfail, hbad]
      · simp [hfail]
    · have hz := (PMF.apply_eq_zero_iff _ _).mpr hmem
      simp [Set.indicator_apply, hz]
  refine hle_bad.trans ?_
  rw [voleithKSBound_coe]
  simpa [voleithBudget] using
    toOuterMeasure_run_mvSticky_bad_le expand decWit chalToIdx Rel checkRel hSound A
      hleaf_tot hfs_tot (([], []), false) false rfl

private theorem voleithStickyMemoize_goodInv_backwards {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (q : LeafQuery d Seed IV ⊕ FSQuery d comLen rowLen Stmt IV PreMsg)
    (s s' : VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal)
    (a : VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal q)
    (hs' : (a, s') ∈
      (voleithStickyMemoize expand decWit chalToIdx Rel checkRel q s).support)
    (hclean' : s'.2 = false)
    (hinv' : VOLEITHGoodInv expand decWit chalToIdx Rel checkRel s'.1) :
    s.2 = false ∧ VOLEITHGoodInv expand decWit chalToIdx Rel checkRel s.1 := by
  have hclean : s.2 = false := by
    by_contra htrue
    have hbad : OracleComp.FlagBad s := by
      cases hs2 : s.2 <;> simp_all [OracleComp.FlagBad]
    rcases s with ⟨tr, b⟩
    dsimp only [OracleComp.FlagBad] at hbad
    subst hbad
    have hbad' := OracleComp.isFlagMonotone_withBadFlag
      (voleithStepKernel expand decWit chalToIdx Rel checkRel) q tr (a, s') hs'
    simp [OracleComp.FlagBad, hclean'] at hbad'
  refine ⟨hclean, ?_⟩
  rcases s with ⟨⟨tr₁, tr₂⟩, b⟩
  dsimp only at hclean
  subst hclean
  simp only [voleithStickyMemoize, OracleComp.withBadFlag_false] at hs'
  rcases q with ql | qf
  · dsimp only [voleithStepKernel] at hs'
    cases hlook : tr₁.lookup ql with
    | some out =>
      simp only [hlook, PMF.mem_support_pure_iff, Prod.mk.injEq] at hs'
      obtain ⟨_, rfl⟩ := hs'
      exact hinv'
    | none =>
      simp only [hlook, PMF.mem_support_map_iff, Prod.mk.injEq] at hs'
      obtain ⟨out, -, _, rfl⟩ := hs'
      simp only at hclean'
      have hnot : out.com ∉ seenComList (tr₁, tr₂) := by
        simpa only [decide_eq_false_iff_not] using hclean'
      refine ⟨(List.pairwise_cons.mp hinv'.1).2, fun e he => ?_⟩
      have hsub := extractRowsFromTrace_of_not_mem_seenComList (ql := ql) expand hnot he
      have he' := hinv'.2 e he
      dsimp only at he' ⊢
      rwa [hsub] at he'
  · dsimp only [voleithStepKernel] at hs'
    cases hlook : tr₂.lookup qf with
    | some delta =>
      simp only [hlook, PMF.mem_support_pure_iff, Prod.mk.injEq] at hs'
      obtain ⟨_, rfl⟩ := hs'
      exact hinv'
    | none =>
      simp only [hlook, PMF.mem_support_map_iff, Prod.mk.injEq] at hs'
      obtain ⟨delta, -, _, rfl⟩ := hs'
      exact ⟨hinv'.1, fun e he => hinv'.2 e (List.mem_cons_of_mem _ he)⟩

private theorem runWith_voleithStickyMemoize_goodInv_backwards {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit α : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (prog : ProbOracleComp (VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) α)
    (s s' : VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal)
    (a : α)
    (hs' : (a, s') ∈ (ProbOracleComp.runWith
      (voleithStickyMemoize expand decWit chalToIdx Rel checkRel) prog s).support)
    (hclean' : s'.2 = false)
    (hinv' : VOLEITHGoodInv expand decWit chalToIdx Rel checkRel s'.1) :
    s.2 = false ∧ VOLEITHGoodInv expand decWit chalToIdx Rel checkRel s.1 := by
  induction prog using ProbOracleComp.induction generalizing s with
  | pure r =>
    simp only [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hs'
    obtain ⟨_, rfl⟩ := hs'
    exact ⟨hclean', hinv'⟩
  | sample_bind n cont ih =>
    rw [ProbOracleComp.runWith_bind, PMF.mem_support_bind_iff] at hs'
    obtain ⟨⟨r, sm⟩, hsm, hrest⟩ := hs'
    rw [ProbOracleComp.runWith_sample, PMF.mem_support_map_iff] at hsm
    obtain ⟨w, -, heq⟩ := hsm
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    exact ih w s hrest
  | query_bind q cont ih =>
    rw [ProbOracleComp.runWith_bind, PMF.mem_support_bind_iff] at hs'
    obtain ⟨⟨r, sm⟩, hsm, hrest⟩ := hs'
    rw [ProbOracleComp.runWith_query] at hsm
    obtain ⟨hcm, him⟩ := ih r sm hrest
    exact voleithStickyMemoize_goodInv_backwards expand decWit chalToIdx Rel checkRel
      q s sm r hsm hcm him

private theorem run_interpret_sumUnif_isCostBounded
    {ιReq ιRO : Type} {ReqSpec : ιReq → Type} {ROSpec : ιRO → Type}
    {ιOut : Type} {OutSpec : ιOut → Type} {S α : Type}
    (inner : (q : ιReq ⊕ ιRO) → StateT S (ProbOracleComp OutSpec) ((ReqSpec ⊕ₒ ROSpec) q))
    (reqCost : ιReq → ℕ) (roCost : ιRO → ℕ) (outCost : ιOut → ℕ)
    (hReq : ∀ req (s : S), IsCostBounded (Sum.elim (fun _ => 0) outCost)
      ((inner (.inl req)).run s) (reqCost req))
    (hRO : ∀ qRO (s : S), IsCostBounded (Sum.elim (fun _ => 0) outCost)
      ((inner (.inr qRO)).run s) (roCost qRO))
    (prog : ProbOracleComp ((ReqSpec ⊕ₒ ROSpec)) α) (s₀ : S) {B : ℕ}
    (hB : IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim reqCost roCost)) prog B) :
    IsCostBounded (Sum.elim (fun _ => 0) outCost)
      ((OracleComp.interpret
        (OracleComp.sumHandler
          (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
          inner)
        prog).run s₀) B := by
  refine OracleComp.IsCostBounded.run_interpret
    (cost := Sum.elim (fun _ => 0) (Sum.elim reqCost roCost))
    (cost' := Sum.elim (fun _ => 0) outCost) ?_ hB s₀
  intro q s
  rcases q with n | (req | qRO)
  · simp only [StateT.run_lift, Sum.elim_inl]
    rw [show (0 : ℕ) = 0 + 0 from rfl]
    refine (ProbOracleComp.isCostBounded_sample _ _).bind fun _ =>
      OracleComp.IsCostBounded.pure _ 0
  · exact hReq req s
  · exact hRO qRO s

private theorem isCostBounded_sample_ite_query {ι R S : Type} {spec : OracleSpec ι}
    (m : ProbComp (Bool × S)) (q : ι) (f : S → spec q → R × S) (g : S → R × S) :
    IsCostBounded (Sum.elim (fun _ => 0) (fun _ => 1))
      (ProbOracleComp.sample m >>= fun (ok, s') =>
        if ok then ProbOracleComp.query q >>= fun r => pure (f s' r) else pure (g s')) 1 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl]
  refine (ProbOracleComp.isCostBounded_sample _ _).bind fun (ok, s') => ?_
  cases ok
  · exact OracleComp.IsCostBounded.pure _ 1
  · dsimp only
    simp only [↓reduceIte]
    rw [show (1 : ℕ) = 1 + 0 from rfl]
    exact (OracleComp.IsCostBounded.query (spec := probOracleSpec _) (Sum.inr _)).bind
      fun _ => OracleComp.IsCostBounded.pure _ 0

private theorem stickyVerify_inr_map_forget {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit Extra : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (qRO : LeafQuery d Seed IV ⊕ FSQuery d comLen rowLen Stmt IV PreMsg)
    (roSt : VOLEITHTraceState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal)
    (extra : Extra) (b : Bool) :
    (((voleithStickyMemoize expand decWit chalToIdx Rel checkRel qRO (roSt, b)).map
        fun (ans, s') => (ans, ((s'.1, extra), s'.2))).map (Prod.map id Prod.fst)) =
      (voleithMemoize qRO roSt).map fun (ans, roSt') => (ans, (roSt', extra)) := by
  simp only [voleithStickyMemoize]
  have hstep := OracleComp.withBadFlag_map_fst
    (voleithStepKernel expand decWit chalToIdx Rel checkRel) qRO roSt b
  have hk := voleithStepKernel_map_fst expand decWit chalToIdx Rel checkRel qRO roSt
  calc
    ((OracleComp.withBadFlag
        (voleithStepKernel expand decWit chalToIdx Rel checkRel) qRO
        (roSt, b)).map fun (ans, s') => (ans, ((s'.1, extra), s'.2))).map
        (Prod.map id Prod.fst) =
      ((OracleComp.withBadFlag
          (voleithStepKernel expand decWit chalToIdx Rel checkRel) qRO
          (roSt, b)).map (Prod.map id Prod.fst)).map
          fun (ans, roSt') => (ans, (roSt', extra)) := by
      rw [PMF.map_comp, PMF.map_comp]
      rfl
    _ = _ := by rw [hstep, hk]

end StickySoundness

/-! ### Shared Verify-Gated Sticky ROM Bridge -/

section VerifyGatedBridge

/-- Executable two-channel ROM oracle handler that gates external requests on `voleithVerifyROM`
before sampling `onAccept`. -/
@[expose] noncomputable def verifyGatedHandlerProg {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Req Resp Log : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (toStmt : Req → Stmt) (toProof : Req → VOLEITHProof d comLen rowLen Seed IV PreMsg)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (onReject : Resp) (onAccept : Req → Log → ProbComp (Resp × Log)) :
    (q : Req ⊕ (LeafQuery d Seed IV ⊕ FSQuery d comLen rowLen Stmt IV PreMsg)) →
      StateT (VOLEITHTraceState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal × Log) ProbComp
        (((fun _ : Req => Resp) ⊕ₒ
          VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) q)
  | .inl req, (roSt, log) => do
    let (ok, roSt') ← (ProbOracleComp.runState
      (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel (toStmt req) (toProof req))
      voleithMemoizeProg).run roSt
    if ok then
      let (resp, log') ← onAccept req log
      pure (resp, (roSt', log'))
    else
      pure (onReject, (roSt', log))
  | .inr qRO, (roSt, log) => do
    let (ans, roSt') ← (voleithMemoizeProg qRO).run roSt
    pure (ans, (roSt', log))

/-- `PMF` semantics of `verifyGatedHandlerProg`, passing the current `H_leaf` trace `roSt.1` to
`onAccept`. -/
@[expose] noncomputable def verifyGatedHandler {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Req Resp Log : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (toStmt : Req → Stmt) (toProof : Req → VOLEITHProof d comLen rowLen Seed IV PreMsg)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (onReject : Resp)
    (onAccept : LeafTrace d sdLen comLen Seed IV → Req → Log → ProbComp (Resp × Log)) :
    (q : Req ⊕ (LeafQuery d Seed IV ⊕ FSQuery d comLen rowLen Stmt IV PreMsg)) →
      StateT (VOLEITHTraceState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal × Log) PMF
        (((fun _ : Req => Resp) ⊕ₒ
          VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) q)
  | .inl req, (roSt, log) =>
    (ProbOracleComp.runWith voleithMemoize
      (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel (toStmt req) (toProof req))
      roSt).bind fun (ok, roSt') =>
      if ok then
        (ProbComp.eval (onAccept roSt.1 req log)).map fun (resp, log') => (resp, (roSt', log'))
      else
        PMF.pure (onReject, (roSt', log))
  | .inr qRO, (roSt, log) =>
    (voleithMemoize qRO roSt).map fun (ans, roSt') => (ans, (roSt', log))

/-- Evaluating `verifyGatedHandlerProg` on any query/state reduces to `verifyGatedHandler`. -/
theorem verifyGatedHandlerProg_eval {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Req Resp Log : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (toStmt : Req → Stmt) (toProof : Req → VOLEITHProof d comLen rowLen Seed IV PreMsg)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (onReject : Resp) (onAccept : Req → Log → ProbComp (Resp × Log))
    (q : Req ⊕ (LeafQuery d Seed IV ⊕ FSQuery d comLen rowLen Stmt IV PreMsg))
    (st : VOLEITHTraceState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal × Log) :
    ProbComp.eval
        (verifyGatedHandlerProg (comLen := comLen) (Seed := Seed) (IV := IV)
          expand chalToIdx toStmt toProof checkRel onReject onAccept q st) =
      verifyGatedHandler (comLen := comLen) (Seed := Seed) (IV := IV)
        expand chalToIdx toStmt toProof checkRel onReject (fun _ => onAccept) q st := by
  rcases st with ⟨roSt, log⟩
  rcases q with req | qRO
  · simp only [verifyGatedHandlerProg, verifyGatedHandler, ProbComp.eval_bind,
      ProbOracleComp.eval_runState]
    have hev :
        (fun q s => ProbComp.eval (voleithMemoizeProg q s)) =
          (voleithMemoize (d := d) (sdLen := sdLen) (comLen := comLen) (rowLen := rowLen)
            (Stmt := Stmt) (Seed := Seed) (IV := IV) (PreMsg := PreMsg) (Chal := Chal)) :=
      funext fun q => funext fun s => eval_voleithMemoizeProg q s
    rw [hev]
    congr 1
    funext ⟨ok, roSt'⟩
    cases ok
    · simp [ProbComp.eval_pure]
    · simp only [↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure]
      rfl
  · simp only [verifyGatedHandlerProg, verifyGatedHandler, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.map]
    change (((voleithMemoizeProg qRO roSt).eval).bind fun a =>
        PMF.pure (a.1, (a.2, log))) = _
    rw [eval_voleithMemoizeProg]
    rfl

/-- Lifting a `VOLEITHLeafSpec ⊕ₒ VOLEITHFSSpec` subprogram into `verifyGatedHandler` runs
against `voleithMemoize` on `roSt` and preserves `log` unchanged. -/
theorem runWith_verifyGatedHandler_liftRight {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Req Resp Log α : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (toStmt : Req → Stmt) (toProof : Req → VOLEITHProof d comLen rowLen Seed IV PreMsg)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (onReject : Resp)
    (onAccept : LeafTrace d sdLen comLen Seed IV → Req → Log → ProbComp (Resp × Log))
    (prog : OracleComp (VOLEITHLeafSpec d sdLen comLen Seed IV ⊕ₒ
      VOLEITHFSSpec d comLen rowLen Stmt IV PreMsg Chal) α)
    (roSt : VOLEITHTraceState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) (log : Log) :
    ProbOracleComp.runWith
        (verifyGatedHandler (comLen := comLen) (Seed := Seed) (IV := IV)
          expand chalToIdx toStmt toProof checkRel onReject onAccept)
        (OracleComp.liftRight (spec₁ := unifSpec)
          (OracleComp.liftRight (spec₁ := fun _ : Req => Resp) prog)) (roSt, log) =
      ((OracleComp.interpret
        (voleithMemoize (d := d) (sdLen := sdLen) (comLen := comLen) (rowLen := rowLen)
          (Stmt := Stmt) (Seed := Seed) (IV := IV) (PreMsg := PreMsg) (Chal := Chal))
        prog).run roSt).map fun (a, roSt') => (a, (roSt', log)) := by
  rw [ProbOracleComp.runWith, OracleComp.runWith_sumHandler_liftRight,
    OracleComp.runWith_eq_run_interpret]
  induction prog using OracleComp.induction generalizing roSt with
  | pure a =>
    simp [OracleComp.liftRight_pure, PMF.monad_pure_eq_pure, PMF.pure_map]
  | query_bind q cont ih =>
    rw [PFunctor.FreeM.bind_eq_bind, OracleComp.liftRight_bind, OracleComp.liftRight_query,
      OracleComp.run_interpret_bind, OracleComp.run_interpret_query,
      OracleComp.run_interpret_bind, OracleComp.run_interpret_query]
    simp only [verifyGatedHandler, PMF.monad_bind_eq_bind, PMF.bind_map, PMF.map_bind,
      Function.comp_def]
    congr 1
    funext ⟨ans, roSt'⟩
    exact ih ans roSt'

private noncomputable def verifyGatedStickyHandler {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit Req Resp Log : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (toStmt : Req → Stmt) (toProof : Req → VOLEITHProof d comLen rowLen Seed IV PreMsg)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (onReject : Resp)
    (onAccept : LeafTrace d sdLen comLen Seed IV → Req → Log → ProbComp (Resp × Log)) :
    (q : Req ⊕ (LeafQuery d Seed IV ⊕ FSQuery d comLen rowLen Stmt IV PreMsg)) →
      StateT ((VOLEITHTraceState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal × Log) × Bool)
        PMF (((fun _ : Req => Resp) ⊕ₒ
          VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) q)
  | .inl req, ((roSt, log), b) =>
    (ProbOracleComp.runWith (voleithStickyMemoize expand decWit chalToIdx Rel checkRel)
      (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel (toStmt req) (toProof req))
      (roSt, b)).bind fun (ok, st_res) =>
      if ok then
        (ProbComp.eval (onAccept roSt.1 req log)).map fun (resp, log') =>
          (resp, ((st_res.1, log'), st_res.2))
      else
        PMF.pure (onReject, ((st_res.1, log), st_res.2))
  | .inr qRO, ((roSt, log), b) =>
    (voleithStickyMemoize expand decWit chalToIdx Rel checkRel qRO (roSt, b)).map
      fun (ans, st_res) => (ans, ((st_res.1, log), st_res.2))

private theorem verifyGatedStickyHandler_map_forget {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit Req Resp Log : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (toStmt : Req → Stmt) (toProof : Req → VOLEITHProof d comLen rowLen Seed IV PreMsg)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (onReject : Resp)
    (onAccept : LeafTrace d sdLen comLen Seed IV → Req → Log → ProbComp (Resp × Log)) :
    ∀ q st,
      ((verifyGatedStickyHandler (comLen := comLen) (Seed := Seed) (IV := IV)
          expand decWit chalToIdx Rel toStmt toProof checkRel onReject onAccept q st).map
        (Prod.map id Prod.fst)) =
      verifyGatedHandler (comLen := comLen) (Seed := Seed) (IV := IV)
        expand chalToIdx toStmt toProof checkRel onReject onAccept q st.1 := by
  intro q ⟨⟨roSt, log⟩, b⟩
  rcases q with req | qRO
  · simp only [verifyGatedStickyHandler, verifyGatedHandler, PMF.map_bind]
    have hforget := voleithStickyMemoize_map_forget expand decWit chalToIdx Rel checkRel
      (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel (toStmt req) (toProof req))
      roSt b
    rw [← hforget, PMF.bind_map]
    congr 1
    funext ⟨ok, s'⟩
    cases ok
    · simp
    · simp only [↓reduceIte, PMF.map_comp, Function.comp_def]
      rfl
  · simp only [verifyGatedStickyHandler, verifyGatedHandler]
    exact stickyVerify_inr_map_forget expand decWit chalToIdx Rel checkRel qRO roSt log b

private def verifyGatedBad {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit Log : Type}
    [DecidableEq IV]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (st : (VOLEITHTraceState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal × Log) × Bool) :
    Prop :=
  st.2 = true ∨ ¬ VOLEITHGoodInv expand decWit chalToIdx Rel checkRel st.1.1

private theorem verifyGatedSticky_inl_tail_clean {α Resp Log : Type}
    {ok : Bool} {st_res : α × Bool} {onReject : Resp} {dist : PMF (Resp × Log)}
    {log log' : Log} {roSt' : α} {a : Resp}
    (htail : (a, ((roSt', log'), false)) ∈
      (if ok then dist.map (fun (resp, l') => (resp, ((st_res.1, l'), st_res.2)))
       else PMF.pure (onReject, ((st_res.1, log), st_res.2))).support) :
    st_res.2 = false ∧ st_res.1 = roSt' := by
  cases ok
  · simp only [Bool.false_eq_true, ↓reduceIte, PMF.mem_support_pure_iff, Prod.mk.injEq] at htail
    exact ⟨htail.2.2.symm, htail.2.1.1.symm⟩
  · simp only [↓reduceIte, PMF.mem_support_map_iff, Prod.mk.injEq] at htail
    obtain ⟨⟨_, _⟩, -, _, ⟨hro, _⟩, hst2⟩ := htail
    exact ⟨hst2, hro⟩

private theorem verifyGatedSticky_step_backwards {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit Req Resp Log : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (toStmt : Req → Stmt) (toProof : Req → VOLEITHProof d comLen rowLen Seed IV PreMsg)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (onReject : Resp)
    (onAccept : LeafTrace d sdLen comLen Seed IV → Req → Log → ProbComp (Resp × Log))
    {q : Req ⊕ (LeafQuery d Seed IV ⊕ FSQuery d comLen rowLen Stmt IV PreMsg)}
    {s s' : (VOLEITHTraceState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal × Log) × Bool}
    {a : ((fun _ : Req => Resp) ⊕ₒ
      VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) q}
    (hnot : ¬ verifyGatedBad expand decWit chalToIdx Rel checkRel s')
    (hmem : (a, s') ∈ (verifyGatedStickyHandler (comLen := comLen) (Seed := Seed) (IV := IV)
      expand decWit chalToIdx Rel toStmt toProof checkRel onReject onAccept q s).support) :
    ¬ verifyGatedBad expand decWit chalToIdx Rel checkRel s := by
  simp only [verifyGatedBad, not_or, not_not] at hnot ⊢
  have hs'2 : s'.2 = false := Bool.eq_false_iff.mpr hnot.1
  rcases s with ⟨⟨roSt, log⟩, bs⟩
  rcases s' with ⟨⟨roSt', log'⟩, bs'⟩
  dsimp only at hs'2 hnot
  subst bs'
  rcases q with req | qRO
  · simp only [verifyGatedStickyHandler, PMF.mem_support_bind_iff] at hmem
    obtain ⟨⟨ok, st_res⟩, hst_mem, htail⟩ := hmem
    dsimp only at htail
    obtain ⟨hres2, hro_eq⟩ := verifyGatedSticky_inl_tail_clean htail
    obtain ⟨hbs, hinv_ro⟩ := runWith_voleithStickyMemoize_goodInv_backwards expand decWit
      chalToIdx Rel checkRel
      (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel (toStmt req) (toProof req))
      (roSt, bs) st_res ok hst_mem hres2 (hro_eq ▸ hnot.2)
    exact ⟨hbs ▸ Bool.false_ne_true, hinv_ro⟩
  · simp only [verifyGatedStickyHandler, PMF.mem_support_map_iff] at hmem
    obtain ⟨⟨ans, st_res⟩, hst_mem, heq⟩ := hmem
    simp only [Prod.mk.injEq] at heq
    obtain ⟨_, ⟨hro_eq, _⟩, hres2⟩ := heq
    obtain ⟨hbs, hinv_ro⟩ := voleithStickyMemoize_goodInv_backwards expand decWit chalToIdx Rel
      checkRel qRO (roSt, bs) st_res ans hst_mem hres2 (hro_eq ▸ hnot.2)
    exact ⟨hbs ▸ Bool.false_ne_true, hinv_ro⟩

private theorem verifyGatedSticky_identicalUntilBad {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit Req Resp Log : Type}
    [BEq (LeafQuery d Seed IV)] [LawfulBEq (LeafQuery d Seed IV)]
    [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [LawfulBEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (toStmt : Req → Stmt) (toProof : Req → VOLEITHProof d comLen rowLen Seed IV PreMsg)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (onReject : Resp)
    (onAccept₁ onAccept₂ : LeafTrace d sdLen comLen Seed IV → Req → Log → ProbComp (Resp × Log))
    (hAgree : ∀ tr req log,
      Rel (toStmt req) (extractWitnessFromTrace expand decWit tr (toProof req)) = true →
      onAccept₁ tr req log = onAccept₂ tr req log) :
    ProbOracleComp.IdenticalUntilBad
      (verifyGatedStickyHandler (comLen := comLen) (Seed := Seed) (IV := IV)
        expand decWit chalToIdx Rel toStmt toProof checkRel onReject onAccept₁)
      (verifyGatedStickyHandler (comLen := comLen) (Seed := Seed) (IV := IV)
        expand decWit chalToIdx Rel toStmt toProof checkRel onReject onAccept₂)
      (verifyGatedBad (comLen := comLen) (Seed := Seed) (IV := IV)
        expand decWit chalToIdx Rel checkRel) := by
  refine OracleComp.IdenticalUntilBad.probOracleComp ⟨?_, ?_, ?_⟩
  · intro q s hs a s' hs'
    simp only [verifyGatedBad, not_or] at hs hs'
    have hs2 : s.2 = false := Bool.eq_false_iff.mpr hs.1
    have hs'2 : s'.2 = false := Bool.eq_false_iff.mpr hs'.1
    rcases s with ⟨⟨roSt, log⟩, bs⟩
    rcases s' with ⟨⟨roSt', log'⟩, bs'⟩
    dsimp only at hs2 hs'2 hs hs'
    subst hs2 bs'
    rcases q with req | qRO
    · simp only [verifyGatedStickyHandler, PMF.bind_apply]
      refine tsum_congr fun ⟨ok, st_res⟩ => ?_
      by_cases hmem : (ok, st_res) ∈ (ProbOracleComp.runWith
          (voleithStickyMemoize expand decWit chalToIdx Rel checkRel)
          (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel (toStmt req) (toProof req))
          (roSt, false)).support
      · cases ok
        · simp
        · rcases st_res with ⟨ro_end, b_end⟩
          cases b_end
          · have hrel := voleithVerifyROM_sound_of_clean expand decWit chalToIdx Rel checkRel
              (toStmt req) (toProof req) roSt (ro_end, false) (not_not.mp hs.2) hmem rfl
            simp [hAgree roSt.1 req log hrel]
          · have hzero : ∀ (c : ProbComp (Resp × Log)),
                ((ProbComp.eval c).map fun x => (x.1, ((ro_end, x.2), true)))
                  (a, ((roSt', log'), false)) = 0 := by
              intro c
              exact (PMF.apply_eq_zero_iff _ _).mpr fun hm => by
                rw [PMF.mem_support_map_iff] at hm
                obtain ⟨⟨_, _⟩, -, heq⟩ := hm
                cases heq
            simp [hzero]
      · have hz := (PMF.apply_eq_zero_iff _ _).mpr hmem
        simp [hz]
    · rfl
  · intro q s hs ⟨a, s'⟩ hmem
    exact not_imp_not.mp (fun hnot =>
      verifyGatedSticky_step_backwards expand decWit chalToIdx Rel toStmt toProof checkRel
        onReject onAccept₁ hnot hmem) hs
  · intro q s hs ⟨a, s'⟩ hmem
    exact not_imp_not.mp (fun hnot =>
      verifyGatedSticky_step_backwards expand decWit chalToIdx Rel toStmt toProof checkRel
        onReject onAccept₂ hnot hmem) hs

private noncomputable def verifyGatedToMVInner {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Req Resp Log : Type}
    (toStmt : Req → Stmt) (toProof : Req → VOLEITHProof d comLen rowLen Seed IV PreMsg)
    (onReject : Resp) (onAccept : Req → Log → ProbComp (Resp × Log)) :
    (q : Req ⊕ (LeafQuery d Seed IV ⊕ FSQuery d comLen rowLen Stmt IV PreMsg)) →
      StateT Log (ProbOracleComp (VOLEITHMultiVerifySpec d sdLen comLen rowLen
        Stmt Seed IV PreMsg Chal))
        (((fun _ : Req => Resp) ⊕ₒ
          VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) q)
  | .inl req, log => do
    let ok : Bool ← ProbOracleComp.query
      (spec := VOLEITHMultiVerifySpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal)
      (Sum.inl (toStmt req, toProof req))
    if ok then
      ProbOracleComp.sample (onAccept req log)
    else
      pure (onReject, log)
  | .inr qRO, log => do
    let ans : ((fun _ : Req => Resp) ⊕ₒ
        VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) (Sum.inr qRO) ←
      ProbOracleComp.query
        (spec := VOLEITHMultiVerifySpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal)
        (Sum.inr qRO)
    pure (ans, log)

private theorem verifyGatedToMVInner_cost {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Req Resp Log α : Type}
    (toStmt : Req → Stmt) (toProof : Req → VOLEITHProof d comLen rowLen Seed IV PreMsg)
    (onReject : Resp) (onAccept : Req → Log → ProbComp (Resp × Log))
    (reqCost : ℕ)
    (roCost : LeafQuery d Seed IV ⊕ FSQuery d comLen rowLen Stmt IV PreMsg → ℕ)
    (prog : ProbOracleComp ((fun _ : Req => Resp) ⊕ₒ
      VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) α)
    (log₀ : Log) {B : ℕ}
    (hB : IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => reqCost) roCost)) prog B) :
    IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => reqCost) roCost))
      ((OracleComp.interpret
        (OracleComp.sumHandler
          (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
          (verifyGatedToMVInner (d := d) (sdLen := sdLen) (Chal := Chal)
            toStmt toProof onReject onAccept))
        prog).run log₀) B := by
  refine run_interpret_sumUnif_isCostBounded
    (verifyGatedToMVInner (d := d) (sdLen := sdLen) (Chal := Chal)
      toStmt toProof onReject onAccept)
    (fun _ => reqCost) roCost (Sum.elim (fun _ => reqCost) roCost)
    (fun req log => ?_) (fun qRO log => ?_) prog log₀ hB
  · simp only [StateT.run, verifyGatedToMVInner]
    change IsCostBounded _ _ (reqCost + 0)
    refine (OracleComp.IsCostBounded.query (spec := probOracleSpec _)
      (Sum.inr (Sum.inl _))).bind fun ok => ?_
    cases ok
    · exact OracleComp.IsCostBounded.pure _ 0
    · exact ProbOracleComp.isCostBounded_sample _ _
  · simp only [StateT.run, verifyGatedToMVInner]
    change IsCostBounded _ _ (roCost qRO + 0)
    refine (OracleComp.IsCostBounded.query (spec := probOracleSpec _)
      (Sum.inr (Sum.inr _))).bind fun _ => OracleComp.IsCostBounded.pure _ 0

private noncomputable def verifyGatedRoOnlyStickyHandler {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit Req Resp Log : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (toStmt : Req → Stmt) (toProof : Req → VOLEITHProof d comLen rowLen Seed IV PreMsg)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (onReject : Resp) (onAccept : Req → Log → ProbComp (Resp × Log)) :
    (q : Req ⊕ (LeafQuery d Seed IV ⊕ FSQuery d comLen rowLen Stmt IV PreMsg)) →
      StateT (VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal × Log) PMF
        (((fun _ : Req => Resp) ⊕ₒ
          VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) q)
  | .inl req, (st, log) =>
    (ProbOracleComp.runWith (voleithStickyMemoize expand decWit chalToIdx Rel checkRel)
      (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel (toStmt req) (toProof req))
      st).bind fun (ok, st') =>
      if ok then
        (ProbComp.eval (onAccept req log)).map fun (resp, log') => (resp, (st', log'))
      else
        PMF.pure (onReject, (st', log))
  | .inr qRO, (st, log) =>
    (voleithStickyMemoize expand decWit chalToIdx Rel checkRel qRO st).map
      fun (ans, st') => (ans, (st', log))

private theorem verifyGatedSticky_bad_le {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit Req Resp Log α : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (toStmt : Req → Stmt) (toProof : Req → VOLEITHProof d comLen rowLen Seed IV PreMsg)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    {ε_rel : ℝ≥0}
    (hSound : VOLEITHSoundnessError decWit chalToIdx Rel checkRel ε_rel)
    (onReject : Resp) (onAccept : Req → Log → ProbComp (Resp × Log)) (log₀ : Log)
    (prog : ProbOracleComp ((fun _ : Req => Resp) ⊕ₒ
      VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) α)
    {m Q_leaf Q_FS : ℕ}
    (hm : IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 1) (fun _ => 0))) prog m)
    (hleaf : IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 0) voleithLeafCost)) prog Q_leaf)
    (hfs : IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 0) voleithFSCost)) prog Q_FS) :
    (ProbOracleComp.runWith
        (verifyGatedStickyHandler (comLen := comLen) (Seed := Seed) (IV := IV)
          expand decWit chalToIdx Rel toStmt toProof checkRel onReject (fun _ => onAccept))
        prog ((([], []), log₀), false)).toOuterMeasure
        {x | verifyGatedBad (comLen := comLen) (Seed := Seed) (IV := IV)
          expand decWit chalToIdx Rel checkRel x.2} ≤
      (voleithKSBound d comLen (Q_leaf + m * (2 ^ d - 1)) (Q_FS + m) ε_rel : ℝ≥0∞) := by
  have hinv_bad : ∀ (a : α)
      (st : (VOLEITHTraceState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal × Log) × Bool),
      (a, st) ∈ (ProbOracleComp.runWith
        (verifyGatedStickyHandler (comLen := comLen) (Seed := Seed) (IV := IV)
          expand decWit chalToIdx Rel toStmt toProof checkRel onReject (fun _ => onAccept))
        prog ((([], []), log₀), false)).support →
      st.2 = false →
      VOLEITHGoodInv expand decWit chalToIdx Rel checkRel st.1.1 := by
    intro a st hsupp hclean
    refine ProbOracleComp.runWith_invariant _
      (fun s => s.2 = false → VOLEITHGoodInv expand decWit chalToIdx Rel checkRel s.1.1)
      (fun q s hs a' s' hs' hclean' => ?_)
      prog ((([], []), log₀), false) (fun _ => ⟨List.Pairwise.nil, by simp⟩) a st hsupp hclean
    rcases s with ⟨⟨roSt, log⟩, bs⟩
    rcases s' with ⟨⟨roSt', log'⟩, bs'⟩
    dsimp only at hclean' hs
    subst bs'
    rcases q with req | qRO
    · simp only [verifyGatedStickyHandler, PMF.mem_support_bind_iff] at hs'
      obtain ⟨⟨ok, st_res⟩, hst_mem, htail⟩ := hs'
      dsimp only at htail
      obtain ⟨hres2, hro_eq⟩ := verifyGatedSticky_inl_tail_clean htail
      have hbs : bs = false :=
        runWith_sticky_flagBad_false expand decWit chalToIdx Rel checkRel hst_mem hres2
      have hin := ProbOracleComp.runWith_invariant _
        (fun u => u.2 = false → VOLEITHGoodInv expand decWit chalToIdx Rel checkRel u.1)
        (fun q' u hu a0 u' hu' => voleithStickyMemoize_preserves_goodInv expand decWit chalToIdx
          Rel checkRel q' u hu a0 u' hu')
        _ (roSt, bs) (fun h => hs (hbs ▸ h)) ok st_res hst_mem hres2
      exact hro_eq ▸ hin
    · simp only [verifyGatedStickyHandler, PMF.mem_support_map_iff, Prod.mk.injEq] at hs'
      obtain ⟨⟨ans, st_res⟩, hst_mem, _, ⟨hro_eq, _⟩, hres2⟩ := hs'
      dsimp only at hro_eq hres2
      have hbs : bs = false := by
        by_contra htrue
        have hbad : OracleComp.FlagBad (roSt, bs) := by
          cases h : bs <;> simp_all [OracleComp.FlagBad]
        dsimp only [OracleComp.FlagBad] at hbad
        subst hbad
        have hbad' := OracleComp.isFlagMonotone_withBadFlag
          (voleithStepKernel expand decWit chalToIdx Rel checkRel)
          qRO roSt (ans, st_res) hst_mem
        dsimp only [OracleComp.FlagBad] at hbad'
        exact Bool.false_ne_true (hres2.symm.trans hbad')
      exact hro_eq ▸ voleithStickyMemoize_preserves_goodInv expand decWit chalToIdx
        Rel checkRel qRO (roSt, bs) (fun h => hs (hbs ▸ h)) ans st_res hst_mem hres2
  have hle_flag :
      (ProbOracleComp.runWith
          (verifyGatedStickyHandler (comLen := comLen) (Seed := Seed) (IV := IV)
            expand decWit chalToIdx Rel toStmt toProof checkRel onReject (fun _ => onAccept))
          prog ((([], []), log₀), false)).toOuterMeasure
          {x | verifyGatedBad (comLen := comLen) (Seed := Seed) (IV := IV)
            expand decWit chalToIdx Rel checkRel x.2} ≤
        (ProbOracleComp.runWith
          (verifyGatedStickyHandler (comLen := comLen) (Seed := Seed) (IV := IV)
            expand decWit chalToIdx Rel toStmt toProof checkRel onReject (fun _ => onAccept))
          prog ((([], []), log₀), false)).toOuterMeasure {x | x.2.2 = true} := by
    simp only [PMF.toOuterMeasure_apply]
    refine tsum_le_tsum fun ⟨a, st⟩ => ?_
    by_cases hmem : (a, st) ∈ (ProbOracleComp.runWith
        (verifyGatedStickyHandler (comLen := comLen) (Seed := Seed) (IV := IV)
          expand decWit chalToIdx Rel toStmt toProof checkRel onReject (fun _ => onAccept))
        prog ((([], []), log₀), false)).support
    · by_cases hst2 : st.2 = true
      · simp [verifyGatedBad, hst2]
      · have hclean : st.2 = false := Bool.eq_false_iff.mpr hst2
        have hg := hinv_bad a st hmem hclean
        simp [verifyGatedBad, hst2, hg]
    · have hz := (PMF.apply_eq_zero_iff _ _).mpr hmem
      simp [Set.indicator_apply, hz]
  refine hle_flag.trans ?_
  let mvProg : ProbOracleComp (VOLEITHMultiVerifySpec d sdLen comLen rowLen
      Stmt Seed IV PreMsg Chal) (α × Log) :=
    (OracleComp.interpret
      (OracleComp.sumHandler
        (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
        (verifyGatedToMVInner (d := d) (sdLen := sdLen) (Chal := Chal)
          toStmt toProof onReject onAccept))
      prog).run log₀
  have hmv_m :
      IsCostBounded (Sum.elim (fun _ => 0)
        (Sum.elim (fun _ => 1) (fun _ => 0))) mvProg m :=
    verifyGatedToMVInner_cost (d := d) (sdLen := sdLen) (Chal := Chal)
      toStmt toProof onReject onAccept 1 (fun _ => 0) prog log₀ hm
  have hmv_leaf := verifyGatedToMVInner_cost (d := d) (sdLen := sdLen) (Chal := Chal)
    toStmt toProof onReject onAccept 0 voleithLeafCost prog log₀ hleaf
  have hmv_fs := verifyGatedToMVInner_cost (d := d) (sdLen := sdLen) (Chal := Chal)
    toStmt toProof onReject onAccept 0 voleithFSCost prog log₀ hfs
  have hleaf_tot :
      IsCostBounded (Sum.elim (fun _ => 0) mvLeafCost) mvProg (Q_leaf + m * (2 ^ d - 1)) :=
    isCostBounded_mvLeafCost_add hmv_m hmv_leaf
  have hfs_tot : IsCostBounded (Sum.elim (fun _ => 0) mvFSCost) mvProg (Q_FS + m) :=
    isCostBounded_mvFSCost_add hmv_m hmv_fs
  have hmv_bad := toOuterMeasure_run_mvSticky_bad_le expand decWit chalToIdx Rel checkRel
    hSound mvProg hleaf_tot hfs_tot (([], []), false) false rfl
  let dropLog : (VOLEITHTraceState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal × Log) × Bool →
      VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal × Log :=
    fun ((roSt, log), b) => ((roSt, b), log)
  have hleft :
      ((ProbOracleComp.runWith
          (verifyGatedStickyHandler (comLen := comLen) (Seed := Seed) (IV := IV)
            expand decWit chalToIdx Rel toStmt toProof checkRel onReject (fun _ => onAccept))
          prog ((([], []), log₀), false)).map (Prod.map id dropLog)) =
        ProbOracleComp.runWith
          (verifyGatedRoOnlyStickyHandler (comLen := comLen) (Seed := Seed) (IV := IV)
            expand decWit chalToIdx Rel toStmt toProof checkRel onReject onAccept)
          prog ((([], []), false), log₀) := by
    refine ProbOracleComp.runWith_map_state _ _ dropLog (fun q x => ?_)
      prog ((([], []), log₀), false)
    rcases x with ⟨⟨roSt, log⟩, b⟩
    rcases q with req | qRO
    · simp only [verifyGatedStickyHandler, verifyGatedRoOnlyStickyHandler, dropLog, PMF.map_bind]
      congr 1
      funext ⟨ok, st'⟩
      cases ok <;> simp [PMF.map_comp, Function.comp_def]
    · simp only [verifyGatedStickyHandler, verifyGatedRoOnlyStickyHandler, dropLog,
        PMF.map_comp, Function.comp_def]
  let dropMV : Log × (VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal × Bool) →
      VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal × Log :=
    fun (log, st_mv) => (st_mv.1, log)
  have hright :
      ((ProbOracleComp.runWith
          (voleithMultiVerifyStickyHandler expand decWit chalToIdx Rel checkRel)
          mvProg ((([], []), false), false)).map
        fun ((a, log), st_mv) => (a, (st_mv.1, log))) =
        ProbOracleComp.runWith
          (verifyGatedRoOnlyStickyHandler (comLen := comLen) (Seed := Seed) (IV := IV)
            expand decWit chalToIdx Rel toStmt toProof checkRel onReject onAccept)
          prog ((([], []), false), log₀) := by
    have hrun := ProbOracleComp.runWith_run_interpret
      (verifyGatedToMVInner (d := d) (sdLen := sdLen) (Chal := Chal)
        toStmt toProof onReject onAccept)
      (voleithMultiVerifyStickyHandler expand decWit chalToIdx Rel checkRel)
      prog log₀ ((([], []), false), false)
    have hrun' :
        ((ProbOracleComp.runWith
            (voleithMultiVerifyStickyHandler expand decWit chalToIdx Rel checkRel)
            mvProg ((([], []), false), false)).map
          fun ((a, log), st_mv) => (a, (st_mv.1, log))) =
        ((ProbOracleComp.runWith
            (fun q state =>
              PMF.map (fun ⟨⟨a, b⟩, c⟩ => (a, b, c))
                (ProbOracleComp.runWith
                  (voleithMultiVerifyStickyHandler expand decWit chalToIdx Rel checkRel)
                  ((verifyGatedToMVInner (d := d) (sdLen := sdLen) (Chal := Chal)
                    toStmt toProof onReject onAccept q).run state.1) state.2))
            prog (log₀, ((([], []), false), false))).map
          (Prod.map id dropMV)) := by
      dsimp only [mvProg]
      rw [hrun, PMF.map_comp]
      rfl
    rw [hrun']
    refine ProbOracleComp.runWith_map_state _ _ dropMV (fun q x => ?_)
      prog (log₀, ((([], []), false), false))
    rcases x with ⟨log, ⟨s_mv, failed⟩⟩
    rcases q with req | qRO
    · simp only [verifyGatedToMVInner, dropMV, verifyGatedRoOnlyStickyHandler, StateT.run,
        ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
        voleithMultiVerifyStickyHandler, PMF.bind_map, PMF.map_bind, Function.comp_def]
      congr 1
      funext ⟨ok, s'⟩
      cases ok
      · simp [ProbOracleComp.runWith_pure, PMF.map, Function.comp_def, PMF.pure_bind]
      · simp only [↓reduceIte, ProbOracleComp.runWith_sample, PMF.map_comp, Function.comp_def]
    · simp only [verifyGatedToMVInner, dropMV, verifyGatedRoOnlyStickyHandler, StateT.run,
        ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure,
        voleithMultiVerifyStickyHandler, PMF.map, PMF.bind_bind, Function.comp_def, PMF.pure_bind]
  calc
    (ProbOracleComp.runWith
        (verifyGatedStickyHandler (comLen := comLen) (Seed := Seed) (IV := IV)
          expand decWit chalToIdx Rel toStmt toProof checkRel onReject (fun _ => onAccept))
        prog ((([], []), log₀), false)).toOuterMeasure {x | x.2.2 = true}
      = ((ProbOracleComp.runWith
          (verifyGatedStickyHandler (comLen := comLen) (Seed := Seed) (IV := IV)
            expand decWit chalToIdx Rel toStmt toProof checkRel onReject (fun _ => onAccept))
          prog ((([], []), log₀), false)).map (Prod.map id dropLog)).toOuterMeasure
          {x | OracleComp.FlagBad x.2.1} := by
        rw [PMF.toOuterMeasure_map_apply]
        rfl
    _ = ((ProbOracleComp.runWith
          (voleithMultiVerifyStickyHandler expand decWit chalToIdx Rel checkRel)
          mvProg ((([], []), false), false)).map
          fun ((a, log), st_mv) => (a, (st_mv.1, log))).toOuterMeasure
          {x | OracleComp.FlagBad x.2.1} := by
        rw [hleft, hright]
    _ = (ProbOracleComp.runWith
          (voleithMultiVerifyStickyHandler expand decWit chalToIdx Rel checkRel)
          mvProg ((([], []), false), false)).toOuterMeasure
          {x | OracleComp.FlagBad x.2.1} := by
        rw [PMF.toOuterMeasure_map_apply]
        rfl
    _ ≤ (voleithKSBound d comLen (Q_leaf + m * (2 ^ d - 1)) (Q_FS + m) ε_rel : ℝ≥0∞) := by
        simpa [voleithKSBound_coe, voleithBudget] using hmv_bad

private theorem bind_tsum_add_voleithKSBound_toNNReal {Keys : Type}
    (romGame extGame : Experiment)
    (keyDist : PMF Keys) (lhs rhs : Keys → PMF Bool) (bound : ℝ≥0)
    (hkey_le : ∀ k, (lhs k) true ≤ (rhs k) true + (bound : ℝ≥0∞))
    (hlhs : ProbComp.eval romGame = keyDist.bind lhs)
    (hrhs : ProbComp.eval extGame = keyDist.bind rhs) :
    romGame.succProbability ≤ extGame.succProbability + bound := by
  have hprob_le :
      ProbComp.eval romGame true ≤ ProbComp.eval extGame true + (bound : ℝ≥0∞) := by
    rw [hlhs, hrhs, PMF.bind_apply, PMF.bind_apply]
    calc
      (∑' k, keyDist k * (lhs k) true)
        ≤ ∑' k, keyDist k * ((rhs k) true + (bound : ℝ≥0∞)) := by
          refine tsum_le_tsum fun k => ?_
          gcongr
          exact hkey_le k
      _ = (∑' k, keyDist k * (rhs k) true) + ∑' k, keyDist k * (bound : ℝ≥0∞) := by
          simp_rw [mul_add]
          rw [tsum_add]
      _ = _ := by
          rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have hnn := ENNReal.toNNReal_mono
    (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, ENNReal.coe_ne_top⟩) hprob_le
  rw [ENNReal.toNNReal_add (PMF.apply_ne_top _ _) ENNReal.coe_ne_top, ENNReal.toNNReal_coe] at hnn
  exact hnn

end VerifyGatedBridge

/-! ### Bridge to `AnonymousToken.Basic` -/

section AnonymousTokenBridge

/-- Client signing request in the unextracted `leaf_hash::shake` ROM anonymous-token game: the
client asks the signer to certify a public `target` while proving knowledge of an opening via a
VOLEitH proof `proof`. -/
structure ROMTokenRequest (Message Target : Type) (d comLen rowLen : ℕ)
    (Seed IV PreMsg : Type) where
  /-- Semantic message bound into the token payload. -/
  message : Message
  /-- Blinded / committed target submitted to the signer. -/
  target : Target
  /-- Straight-line extractable VOLEitH proof for `(message, target)`. -/
  proof : VOLEITHProof d comLen rowLen Seed IV PreMsg
  deriving DecidableEq

/-- Public VOLEitH statement `(req.message, req.target)` proven by `ROMTokenRequest`. -/
@[expose] def ROMTokenRequest.stmt {Message Target : Type} {d comLen rowLen : ℕ}
    {Seed IV PreMsg : Type} (req : ROMTokenRequest Message Target d comLen rowLen Seed IV PreMsg) :
    Message × Target :=
  (req.message, req.target)

/-- Relation verified in the ROM anonymous-token signing request: `targetFn msg open_ = target`. -/
@[expose] def romTokenRel {Message Opening Target : Type} [DecidableEq Target]
    (targetFn : Message → Opening → Target)
    (stmt : Message × Target) (open_ : Opening) : Bool :=
  decide (targetFn stmt.1 open_ = stmt.2)

/-- Signing oracle specification returning `some sig` on proof acceptance and `none` otherwise. -/
abbrev ROMTokenSignSpec (Message Target : Type) (d comLen rowLen : ℕ)
    (Seed IV PreMsg Sig : Type) :
    OracleSpec (ROMTokenRequest Message Target d comLen rowLen Seed IV PreMsg) :=
  fun _ => Option Sig

/-- Combined oracle specification exposed to an unextracted ROM token adversary. -/
abbrev ROMTokenSpec (Message Target : Type) (d sdLen comLen rowLen : ℕ)
    (Seed IV PreMsg Chal Sig : Type) :=
  ROMTokenSignSpec Message Target d comLen rowLen Seed IV PreMsg Sig ⊕ₒ
    VOLEITHROSpec d sdLen comLen rowLen (Message × Target) Seed IV PreMsg Chal

/-- Transcript of an unextracted ROM anonymous-token adversary execution. -/
structure ROMTokenExecution (PK Message Opening Sig : Type) where
  /-- Signer public verification key. -/
  publicKey : PK
  /-- Final forged token emitted by the adversary. -/
  output : Token Message Opening Sig
  /-- Messages signed after VOLEitH proof verification succeeded. -/
  signedMessages : List Message

/-- Winning condition for the unextracted ROM token adversary: valid token on a fresh message. -/
@[expose] def romTokenAccept {PK SK Message Opening Target Sig : Type} [DecidableEq Message]
    (S : Signature.Scheme PK SK Target Sig) (targetFn : Message → Opening → Target)
    (run : ROMTokenExecution PK Message Opening Sig) : Bool :=
  Token.valid S targetFn run.publicKey run.output &&
    decide (run.output.payload.message ∉ run.signedMessages)

/-- Acceptance continuation for `ROMTokenSpec` that signs `req.target` and appends `req.message`
to `signedMessages`. -/
@[expose] noncomputable def romTokenAcceptReal {d comLen rowLen : ℕ}
    {PK SK Message Target Seed IV PreMsg Sig : Type}
    (S : Signature.Scheme PK SK Target Sig) (keys : PK × SK)
    (req : ROMTokenRequest Message Target d comLen rowLen Seed IV PreMsg)
    (msgs : List Message) : ProbComp (Option Sig × List Message) :=
  (S.sign keys.2 req.target).map fun sig => (some sig, msgs ++ [req.message])

/-- Execute an unextracted ROM token adversary against the verifier-checked signing oracle and lazy
two-channel ROM. -/
@[expose] noncomputable def runROMUnextractedToken {d sdLen comLen rowLen : ℕ}
    {PK SK Message Opening Target Seed IV PreMsg Chal Sig : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen (Message × Target) IV PreMsg)]
    [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (checkRel : Message × Target → (Fin d → BitString rowLen) → BitString rowLen →
      PreMsg → Chal → Bool)
    (S : Signature.Scheme PK SK Target Sig)
    (A : PK → ProbOracleComp (ROMTokenSpec Message Target d sdLen comLen rowLen Seed IV PreMsg
      Chal Sig) (Token Message Opening Sig)) :
    ProbComp (ROMTokenExecution PK Message Opening Sig) := do
  let keys ← S.keyGen
  let ⟨output, _, signedMessages⟩ ←
    ((A keys.1).runState (verifyGatedHandlerProg (comLen := comLen) (Seed := Seed) (IV := IV)
      expand chalToIdx ROMTokenRequest.stmt ROMTokenRequest.proof checkRel none
      (romTokenAcceptReal S keys))).run (([], []), [])
  pure { publicKey := keys.1, output := output, signedMessages := signedMessages }

/-- Unextracted ROM anonymous-token unforgeability game, original to this library (note that
`ROMTokenRequest.message` is sent publicly in the clear and logged against `signedMessages`,
modeling declared-message token issuance rather than blind issuance / OMUF). -/
@[expose] noncomputable def romUnextractedTokenExperiment {d sdLen comLen rowLen : ℕ}
    {PK SK Message Opening Target Seed IV PreMsg Chal Sig : Type}
    [DecidableEq Message]
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen (Message × Target) IV PreMsg)]
    [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (checkRel : Message × Target → (Fin d → BitString rowLen) → BitString rowLen →
      PreMsg → Chal → Bool)
    (S : Signature.Scheme PK SK Target Sig) (targetFn : Message → Opening → Target)
    (A : PK → ProbOracleComp (ROMTokenSpec Message Target d sdLen comLen rowLen Seed IV PreMsg
      Chal Sig) (Token Message Opening Sig)) : Experiment :=
  romTokenAccept S targetFn <$>
    runROMUnextractedToken expand chalToIdx checkRel S A

private noncomputable def romToExtractedInner {d sdLen comLen rowLen : ℕ}
    {Message Opening Target Seed IV PreMsg Chal Sig : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen (Message × Target) IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Opening)
    (chalToIdx : Chal → Fin (2 ^ d))
    (checkRel : Message × Target → (Fin d → BitString rowLen) → BitString rowLen →
      PreMsg → Chal → Bool) :
    (q : ROMTokenRequest Message Target d comLen rowLen Seed IV PreMsg ⊕
      (LeafQuery d Seed IV ⊕ FSQuery d comLen rowLen (Message × Target) IV PreMsg)) →
      StateT (VOLEITHTraceState d sdLen comLen rowLen (Message × Target) Seed IV PreMsg Chal)
        (ProbOracleComp (fun _ : Payload Message Opening => Sig))
        (ROMTokenSpec Message Target d sdLen comLen rowLen Seed IV PreMsg Chal Sig q)
  | .inl req, roSt => do
    let (ok, roSt') ← ProbOracleComp.sample ((ProbOracleComp.runState
      (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel req.stmt req.proof)
      voleithMemoizeProg).run roSt)
    if ok then
      let openStar := extractWitnessFromTrace expand decWit roSt.1 req.proof
      let sig ← ProbOracleComp.query ⟨req.message, openStar⟩
      pure (some sig, roSt')
    else
      pure (none, roSt')
  | .inr qRO, roSt => do
    let (ans, roSt') ← ProbOracleComp.sample ((voleithMemoizeProg qRO).run roSt)
    pure (ans, roSt')

/-- Straight-line extracted-model `ExtractedForger` constructed from an unextracted ROM adversary
`A`: simulates `VOLEITHROSpec` locally, checks `voleithVerifyROM`, and whenever a request
verifies, extracts `open* = extractWitnessFromTrace tr_leaf prf` without rewinding and forwards
`⟨req.message, open*⟩` to the `ExtractedForger` signing oracle. -/
noncomputable def extractedForgerOfROM {d sdLen comLen rowLen : ℕ}
    {PK Message Opening Target Seed IV PreMsg Chal Sig : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen (Message × Target) IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Opening)
    (chalToIdx : Chal → Fin (2 ^ d))
    (checkRel : Message × Target → (Fin d → BitString rowLen) → BitString rowLen →
      PreMsg → Chal → Bool)
    (A : PK → ProbOracleComp (ROMTokenSpec Message Target d sdLen comLen rowLen Seed IV PreMsg
      Chal Sig) (Token Message Opening Sig)) :
    ExtractedForger PK Message Opening Sig := fun pk =>
  Prod.fst <$> (OracleComp.interpret
    (OracleComp.sumHandler
      (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
      (romToExtractedInner expand decWit chalToIdx checkRel))
    (A pk)).run ([], [])

/-- `extractedForgerOfROM` preserves signing-query budgets: every `VOLEITHROSpec` call costs `0`
signing queries and every signing request calls the extracted signing oracle at most once. -/
theorem extractedForgerOfROM_isQueryBounded {d sdLen comLen rowLen : ℕ}
    {PK Message Opening Target Seed IV PreMsg Chal Sig : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen (Message × Target) IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Opening)
    (chalToIdx : Chal → Fin (2 ^ d))
    (checkRel : Message × Target → (Fin d → BitString rowLen) → BitString rowLen →
      PreMsg → Chal → Bool)
    (A : PK → ProbOracleComp (ROMTokenSpec Message Target d sdLen comLen rowLen Seed IV PreMsg
      Chal Sig) (Token Message Opening Sig))
    {m : ℕ}
    (hm : ∀ pk, IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 1) (fun _ => 0))) (A pk) m) :
    ∀ pk, (extractedForgerOfROM expand decWit chalToIdx checkRel A pk).IsQueryBounded m := by
  intro pk
  unfold extractedForgerOfROM
  rw [ProbOracleComp.IsQueryBounded, OracleComp.isCostBounded_map_iff]
  refine run_interpret_sumUnif_isCostBounded
    (romToExtractedInner expand decWit chalToIdx checkRel)
    (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun req roSt => ?_) (fun qRO roSt => ?_)
    (A pk) ([], []) (hm pk)
  · simpa only [StateT.run, romToExtractedInner] using
      isCostBounded_sample_ite_query
        (spec := fun _ : Payload Message Opening => Sig) (R := Option Sig)
        ((ProbOracleComp.runState
          (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel req.stmt req.proof)
          voleithMemoizeProg).run roSt)
        ⟨req.message, extractWitnessFromTrace expand decWit roSt.1 req.proof⟩
        (fun roSt' sig => (some sig, roSt')) (fun roSt' => (none, roSt'))
  · simp only [StateT.run, romToExtractedInner]
    rw [show (0 : ℕ) = 0 + 0 from rfl]
    exact (ProbOracleComp.isCostBounded_sample _ _).bind fun _ =>
      OracleComp.IsCostBounded.pure _ 0

private noncomputable def romTokenAcceptExt {d sdLen comLen rowLen : ℕ}
    {PK SK Message Opening Target Seed IV PreMsg Sig : Type}
    [DecidableEq IV]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Opening)
    (targetFn : Message → Opening → Target)
    (S : Signature.Scheme PK SK Target Sig) (keys : PK × SK)
    (tr₁ : LeafTrace d sdLen comLen Seed IV)
    (req : ROMTokenRequest Message Target d comLen rowLen Seed IV PreMsg)
    (msgs : List Message) : ProbComp (Option Sig × List Message) :=
  let openStar := extractWitnessFromTrace expand decWit tr₁ req.proof
  (S.sign keys.2 (targetFn req.message openStar)).map fun sig =>
    (some sig, msgs ++ [req.message])

/-- Concrete query-bounded advantage bound (not an asymptotic PPT security theorem):
any unextracted ROM adversary making at most `m` signing queries, `Q_leaf` leaf queries, and
`Q_FS` Fiat–Shamir queries reduces straight-line (no rewinding) to the extracted-model adversary
`extractedForgerOfROM ... A` with additive loss `voleithKSBound` in `Game.succProbability`. -/
theorem unextractedTokenExperiment_succProbability_le_extracted {d sdLen comLen rowLen : ℕ}
    {PK SK Message Opening Target Seed IV PreMsg Chal Sig : Type}
    [DecidableEq Message] [DecidableEq Target]
    [BEq (LeafQuery d Seed IV)] [LawfulBEq (LeafQuery d Seed IV)]
    [BEq (FSQuery d comLen rowLen (Message × Target) IV PreMsg)]
    [LawfulBEq (FSQuery d comLen rowLen (Message × Target) IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Opening)
    (chalToIdx : Chal → Fin (2 ^ d)) (S : Signature.Scheme PK SK Target Sig)
    (targetFn : Message → Opening → Target)
    (checkRel : Message × Target → (Fin d → BitString rowLen) → BitString rowLen →
      PreMsg → Chal → Bool)
    {ε_rel : ℝ≥0}
    (hSound : VOLEITHSoundnessError decWit chalToIdx (romTokenRel targetFn) checkRel ε_rel)
    (A : PK → ProbOracleComp (ROMTokenSpec Message Target d sdLen comLen rowLen Seed IV PreMsg
      Chal Sig) (Token Message Opening Sig))
    {m Q_leaf Q_FS : ℕ}
    (hm : ∀ pk, IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 1) (fun _ => 0))) (A pk) m)
    (hleaf : ∀ pk, IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 0) voleithLeafCost)) (A pk) Q_leaf)
    (hfs : ∀ pk, IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 0) voleithFSCost)) (A pk) Q_FS) :
    (romUnextractedTokenExperiment expand chalToIdx checkRel S targetFn A).succProbability ≤
      (extractedExperiment S targetFn
        (extractedForgerOfROM expand decWit chalToIdx checkRel A)).succProbability +
        voleithKSBound d comLen (Q_leaf + m * (2 ^ d - 1)) (Q_FS + m) ε_rel := by
  let romSticky := fun keys : PK × SK =>
    verifyGatedStickyHandler (comLen := comLen) (Seed := Seed) (IV := IV)
      expand decWit chalToIdx (romTokenRel targetFn) ROMTokenRequest.stmt ROMTokenRequest.proof
      checkRel (none : Option Sig) (fun _ => romTokenAcceptReal S keys)
  let extSticky := fun keys : PK × SK =>
    verifyGatedStickyHandler (comLen := comLen) (Seed := Seed) (IV := IV)
      expand decWit chalToIdx (romTokenRel targetFn) ROMTokenRequest.stmt ROMTokenRequest.proof
      checkRel (none : Option Sig) (romTokenAcceptExt expand decWit targetFn S keys)
  let extH := fun keys : PK × SK =>
    verifyGatedHandler (comLen := comLen) (Seed := Seed) (IV := IV)
      expand chalToIdx ROMTokenRequest.stmt ROMTokenRequest.proof checkRel (none : Option Sig)
      (romTokenAcceptExt expand decWit targetFn S keys)
  have hrom_eval :
      ProbComp.eval (romUnextractedTokenExperiment expand chalToIdx checkRel S targetFn A) =
        (ProbComp.eval S.keyGen).bind fun keys =>
          (ProbOracleComp.runWith (romSticky keys) (A keys.1) ((([], []), []), false)).map
            fun (tok, ((_, msgs), _)) =>
              Token.valid S targetFn keys.1 tok && decide (tok.payload.message ∉ msgs) := by
    simp only [romUnextractedTokenExperiment, runROMUnextractedToken, ProbComp.eval_map,
      ProbComp.eval_bind, ProbComp.eval_pure, ProbOracleComp.eval_runState, PMF.map_bind]
    congr 1
    funext keys
    have hev :
        (fun q st => ProbComp.eval (verifyGatedHandlerProg (comLen := comLen) (Seed := Seed)
            (IV := IV) expand chalToIdx ROMTokenRequest.stmt ROMTokenRequest.proof checkRel none
            (romTokenAcceptReal S keys) q st)) =
          verifyGatedHandler (comLen := comLen) (Seed := Seed) (IV := IV)
            expand chalToIdx ROMTokenRequest.stmt ROMTokenRequest.proof checkRel none
            (fun _ => romTokenAcceptReal S keys) :=
      funext fun q => funext fun st =>
        verifyGatedHandlerProg_eval expand chalToIdx ROMTokenRequest.stmt ROMTokenRequest.proof
          checkRel none (romTokenAcceptReal S keys) q st
    have hforget := ProbOracleComp.runWith_map_state _ _ Prod.fst
      (verifyGatedStickyHandler_map_forget expand decWit chalToIdx (romTokenRel targetFn)
        ROMTokenRequest.stmt ROMTokenRequest.proof checkRel none
        (fun _ => romTokenAcceptReal S keys))
      (A keys.1) ((([], []), []), false)
    rw [hev, ← hforget]
    simp only [PMF.map, PMF.bind_bind, Function.comp_def, PMF.pure_bind,
      romTokenAccept, romSticky]
  have hext_eval :
      ProbComp.eval (extractedExperiment S targetFn
        (extractedForgerOfROM expand decWit chalToIdx checkRel A)) =
        (ProbComp.eval S.keyGen).bind fun keys =>
          (ProbOracleComp.runWith (extSticky keys) (A keys.1) ((([], []), []), false)).map
            fun (tok, ((_, msgs), _)) =>
              Token.valid S targetFn keys.1 tok && decide (tok.payload.message ∉ msgs) := by
    simp only [extractedExperiment, runExtracted, extractedForgerOfROM, ProbComp.eval_map,
      ProbComp.eval_bind, ProbComp.eval_pure, PMF.map, PMF.bind_bind, Function.comp_def,
      PMF.pure_bind]
    congr 1
    funext keys
    let signO : Payload Message Opening → ProbComp Sig := fun p =>
      S.sign keys.2 (targetFn p.message p.opening)
    let signH : Payload Message Opening → StateT (List (Payload Message Opening × Sig)) PMF Sig :=
      fun p log => (ProbComp.eval (signO p)).map fun sig => (sig, log ++ [(p, sig)])
    have hlog_map :
        ProbComp.eval ((Prod.fst <$> (OracleComp.interpret
            (OracleComp.sumHandler
              (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
              (romToExtractedInner expand decWit chalToIdx checkRel))
            (A keys.1)).run ([], [])).runLog signO) =
          (ProbOracleComp.runWith signH ((OracleComp.interpret
              (OracleComp.sumHandler
                (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
                (romToExtractedInner expand decWit chalToIdx checkRel))
              (A keys.1)).run ([], [])) []).map (Prod.map Prod.fst id) := by
      simp only [ProbOracleComp.runLog, ProbOracleComp.runState_map, StateT.run_map,
        ProbOracleComp.eval_runState, ProbComp.eval_map]
      congr 2
    change (ProbComp.eval (ProbOracleComp.runLog (Prod.fst <$>
      (OracleComp.interpret
        (OracleComp.sumHandler
          (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
          (romToExtractedInner expand decWit chalToIdx checkRel))
        (A keys.1)).run ([], [])) signO)).bind _ = _
    rw [hlog_map]
    have hrun := ProbOracleComp.runWith_run_interpret
      (romToExtractedInner expand decWit chalToIdx checkRel) signH (A keys.1) ([], []) []
    let repMsg : VOLEITHTraceState d sdLen comLen rowLen (Message × Target) Seed IV PreMsg Chal ×
        List (Payload Message Opening × Sig) →
        VOLEITHTraceState d sdLen comLen rowLen (Message × Target) Seed IV PreMsg Chal ×
          List Message :=
      fun (roSt, log) => (roSt, log.map fun e => e.1.message)
    have hjoint_eq :
        ((ProbOracleComp.runWith
            (fun q state =>
              PMF.map (fun ⟨⟨a, b⟩, c⟩ => (a, b, c))
                (ProbOracleComp.runWith signH
                  ((romToExtractedInner expand decWit chalToIdx checkRel q).run state.1)
                  state.2))
            (A keys.1) (([], []), [])).map (Prod.map id repMsg)) =
          ProbOracleComp.runWith (extH keys) (A keys.1) (([], []), []) := by
      refine ProbOracleComp.runWith_map_state _ _ repMsg (fun q x => ?_)
        (A keys.1) (([], []), [])
      rcases x with ⟨roSt, log⟩
      rcases q with req | qRO
      · simp only [romToExtractedInner, StateT.run, ProbOracleComp.runWith_bind,
          ProbOracleComp.runWith_sample, extH, verifyGatedHandler]
        have hmem :
            ProbComp.eval ((ProbOracleComp.runState
                (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel req.stmt req.proof)
                voleithMemoizeProg) roSt) =
              ProbOracleComp.runWith voleithMemoize
                (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel req.stmt req.proof)
                roSt := by
          change ProbComp.eval (((ProbOracleComp.runState
            (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel req.stmt req.proof)
            voleithMemoizeProg).run roSt)) = _
          rw [ProbOracleComp.eval_runState]
          congr 2
          exact funext fun q' => funext fun s' => eval_voleithMemoizeProg q' s'
        rw [hmem]
        simp only [PMF.map, PMF.bind_bind, Function.comp_def, PMF.pure_bind]
        congr 1
        funext ⟨ok, roSt'⟩
        cases ok
        · simp only [Bool.false_eq_true, ↓reduceIte, ProbOracleComp.runWith_pure, PMF.pure_bind,
            repMsg]
        · simp only [↓reduceIte, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
            ProbOracleComp.runWith_pure, signH, signO, romTokenAcceptExt, ProbComp.eval_freeMMap,
            PMF.map, PMF.bind_bind, Function.comp_def, PMF.pure_bind, repMsg,
            List.map_append, List.map_cons, List.map_nil]
      · simp only [romToExtractedInner, StateT.run, ProbOracleComp.runWith_bind,
          ProbOracleComp.runWith_sample, ProbOracleComp.runWith_pure, repMsg, extH,
          verifyGatedHandler, PMF.map, PMF.bind_bind, Function.comp_def, PMF.pure_bind,
          eval_voleithMemoizeProg]
    have hforget := ProbOracleComp.runWith_map_state _ _ Prod.fst
      (verifyGatedStickyHandler_map_forget expand decWit chalToIdx (romTokenRel targetFn)
        ROMTokenRequest.stmt ROMTokenRequest.proof checkRel none
        (romTokenAcceptExt expand decWit targetFn S keys))
      (A keys.1) ((([], []), []), false)
    rw [hrun]
    have hleft :
        ((PMF.map (Prod.map Prod.fst id)
            (PMF.map (fun ⟨a, b, c⟩ => ((a, b), c))
              (ProbOracleComp.runWith
                (fun q state =>
                  PMF.map (fun ⟨⟨a, b⟩, c⟩ => (a, b, c))
                    (ProbOracleComp.runWith signH
                      ((romToExtractedInner expand decWit chalToIdx checkRel q).run state.1)
                      state.2))
                (A keys.1) (([], []), [])))).bind
          fun a => PMF.pure (extractedAccept S targetFn ⟨keys.1, a.1, a.2⟩)) =
        ((ProbOracleComp.runWith
            (fun q state =>
              PMF.map (fun ⟨⟨a, b⟩, c⟩ => (a, b, c))
                (ProbOracleComp.runWith signH
                  ((romToExtractedInner expand decWit chalToIdx checkRel q).run state.1)
                  state.2))
            (A keys.1) (([], []), [])).map (Prod.map id repMsg)).bind
          fun x => PMF.pure
            (Token.valid S targetFn keys.1 x.1 && decide (x.1.payload.message ∉ x.2.2)) := by
      simp only [PMF.map, PMF.bind_bind, Function.comp_def, PMF.pure_bind, extractedAccept,
        repMsg, Prod.map]
      rfl
    rw [hleft, hjoint_eq, ← hforget]
    simp only [PMF.map, PMF.bind_bind, Function.comp_def, PMF.pure_bind, extSticky]
  have hkey_le : ∀ keys : PK × SK,
      ((ProbOracleComp.runWith (romSticky keys) (A keys.1) ((([], []), []), false)).map
        fun (tok, ((_, msgs), _)) =>
          Token.valid S targetFn keys.1 tok && decide (tok.payload.message ∉ msgs)) true ≤
      ((ProbOracleComp.runWith (extSticky keys) (A keys.1) ((([], []), []), false)).map
        fun (tok, ((_, msgs), _)) =>
          Token.valid S targetFn keys.1 tok && decide (tok.payload.message ∉ msgs)) true +
        (voleithKSBound d comLen (Q_leaf + m * (2 ^ d - 1)) (Q_FS + m) ε_rel : ℝ≥0∞) := by
    intro keys
    have hiub := ProbOracleComp.IdenticalUntilBad.bind_apply_le
      (verifyGatedSticky_identicalUntilBad expand decWit chalToIdx (romTokenRel targetFn)
        ROMTokenRequest.stmt ROMTokenRequest.proof checkRel (none : Option Sig)
        (fun _ => romTokenAcceptReal S keys) (romTokenAcceptExt expand decWit targetFn S keys)
        (fun tr req msgs hrel => by
          have htarget :
              targetFn req.message (extractWitnessFromTrace expand decWit tr req.proof) =
                req.target := by
            simp only [romTokenRel, ROMTokenRequest.stmt] at hrel
            exact of_decide_eq_true hrel
          simp [romTokenAcceptReal, romTokenAcceptExt, htarget]))
      (A keys.1) ((([], []), []), false)
      (fun (tok, ((_, msgs), _)) =>
        PMF.pure (Token.valid S targetFn keys.1 tok && decide (tok.payload.message ∉ msgs)))
      true
    have hbad := verifyGatedSticky_bad_le expand decWit chalToIdx (romTokenRel targetFn)
      ROMTokenRequest.stmt ROMTokenRequest.proof checkRel hSound none (romTokenAcceptReal S keys)
      [] (A keys.1) (hm keys.1) (hleaf keys.1) (hfs keys.1)
    exact hiub.trans (add_le_add_right hbad _)
  exact bind_tsum_add_voleithKSBound_toNNReal _ _ (ProbComp.eval S.keyGen) _ _ _ hkey_le
    hrom_eval hext_eval

/-- Concrete query-bounded advantage bound (not an asymptotic PPT security theorem):
end-to-end ROM reduction for `AnonymousToken.Basic` composing straight-line leaf extraction
with `AnonymousToken.extracted_succProbability_le` to bound an unextracted ROM adversary's forgery
probability by EUF-CMA + target binding + `voleithKSBound`. -/
theorem unextractedTokenExperiment_succProbability_le {d sdLen comLen rowLen : ℕ}
    {PK SK Message Opening Target Seed IV PreMsg Chal Sig : Type}
    [DecidableEq Message] [DecidableEq Target] [Inhabited Sig]
    [BEq (LeafQuery d Seed IV)] [LawfulBEq (LeafQuery d Seed IV)]
    [BEq (FSQuery d comLen rowLen (Message × Target) IV PreMsg)]
    [LawfulBEq (FSQuery d comLen rowLen (Message × Target) IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Opening)
    (chalToIdx : Chal → Fin (2 ^ d)) (S : Signature.Scheme PK SK Target Sig)
    (targetFn : Message → Opening → Target)
    (checkRel : Message × Target → (Fin d → BitString rowLen) → BitString rowLen →
      PreMsg → Chal → Bool)
    {ε_rel : ℝ≥0}
    (hSound : VOLEITHSoundnessError decWit chalToIdx (romTokenRel targetFn) checkRel ε_rel)
    (A : PK → ProbOracleComp (ROMTokenSpec Message Target d sdLen comLen rowLen Seed IV PreMsg
      Chal Sig) (Token Message Opening Sig))
    {m Q_leaf Q_FS : ℕ}
    (hm : ∀ pk, IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 1) (fun _ => 0))) (A pk) m)
    (hleaf : ∀ pk, IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 0) voleithLeafCost)) (A pk) Q_leaf)
    (hfs : ∀ pk, IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 0) voleithFSCost)) (A pk) Q_FS) :
    (romUnextractedTokenExperiment expand chalToIdx checkRel S targetFn A).succProbability ≤
      (S.eufCmaExperiment (targetForger targetFn
          (extractedForgerOfROM expand decWit chalToIdx checkRel A))).succProbability +
        (bindingExperiment S targetFn
          (extractedForgerOfROM expand decWit chalToIdx checkRel A)).succProbability +
        voleithKSBound d comLen (Q_leaf + m * (2 ^ d - 1)) (Q_FS + m) ε_rel := by
  refine (unextractedTokenExperiment_succProbability_le_extracted expand decWit chalToIdx S
    targetFn checkRel hSound A hm hleaf hfs).trans ?_
  exact add_le_add_left (extracted_succProbability_le S targetFn _) _

end AnonymousTokenBridge

/-! ### Bridge to `AnonymousToken.Conservation` -/

section ConservationBridge

/-- Public issuance statement proven by a client in the unextracted ROM conservation game. -/
structure ROMIssueStatement (Context Commitment : Type) where
  /-- Issuer context bound into the issued note commitment. -/
  ctx : Context
  /-- Issued credit amount. -/
  amount : ℕ
  /-- Commitment hiding `(nullifier, opening)` under `ctx` and `amount`. -/
  commitment : Commitment
  deriving DecidableEq

/-- Public spend statement proven by a client in the unextracted ROM conservation game. -/
structure ROMSpendStatement (Nullifier Context Commitment : Type) where
  /-- Issuer context bound into both input note and change commitment. -/
  ctx : Context
  /-- Spent input nullifier revealed publicly to prevent double-spending. -/
  nullifier : Nullifier
  /-- Publicly debited credit amount. -/
  debit : ℕ
  /-- Public refund amount granted by the issuer on the change note. -/
  refund : ℕ
  /-- Commitment to the fresh change note `(newNullifier, ctx, newCredit, newOpening)`. -/
  changeCommitment : Commitment
  deriving DecidableEq

/-- Public issue or spend query sent to the unextracted ROM issuer oracle (without secret note
openings, old note balances, or the input signature). -/
inductive ROMConservationQuery (Nullifier Context Commitment : Type) where
  /-- Request to certify an issuance commitment for `(ctx, amount)`. -/
  | issue (stmt : ROMIssueStatement Context Commitment)
  /-- Request to spend `nullifier` for `debit` and certify `changeCommitment` with `refund`. -/
  | spend (stmt : ROMSpendStatement Nullifier Context Commitment)
  deriving DecidableEq

/-- Context targeted by a public conservation query. -/
@[expose] def ROMConservationQuery.ctx {Nullifier Context Commitment : Type} :
    ROMConservationQuery Nullifier Context Commitment → Context
  | .issue q => q.ctx
  | .spend q => q.ctx

/-- Signed output message produced when the issuer accepts a public conservation query. -/
@[expose] def ROMConservationQuery.signedMessage {Nullifier Context Commitment Target : Type}
    (tag : Commitment → ℕ → Target) :
    ROMConservationQuery Nullifier Context Commitment → Target
  | .issue q => tag q.commitment 0
  | .spend q => tag q.changeCommitment q.refund

/-- Public VOLEitH statement binding the issuer public key `publicKey` and public `query`. -/
structure ROMConservationStmt (PK Nullifier Context Commitment : Type) where
  /-- Issuer public verification key bound into the Fiat–Shamir query. -/
  publicKey : PK
  /-- Public issuance or spend statement proven in zero knowledge. -/
  query : ROMConservationQuery Nullifier Context Commitment
  deriving DecidableEq

/-- Secret witness extracted from a valid issuance proof. -/
structure ROMIssueWitness (Nullifier Opening : Type) where
  /-- Hidden nullifier committed inside the issued note. -/
  nullifier : Nullifier
  /-- Commitment randomness opening the issued commitment. -/
  opening : Opening
  deriving DecidableEq

/-- Secret witness extracted from a valid spend proof. -/
structure ROMSpendWitness (Nullifier Opening Sig : Type) where
  /-- Hidden credit balance on the spent input note. -/
  oldCredit : ℕ
  /-- Commitment opening for the spent input note. -/
  oldOpening : Opening
  /-- Hidden refund balance on the spent input note. -/
  oldRefund : ℕ
  /-- Issuer signature certifying the spent input note target. -/
  signature : Sig
  /-- Fresh nullifier hidden in the change commitment. -/
  newNullifier : Nullifier
  /-- Remaining credit balance committed in the change note. -/
  newCredit : ℕ
  /-- Commitment randomness for the change note. -/
  newOpening : Opening
  deriving DecidableEq

/-- Extracted conservation witness matching `ROMConservationQuery`. -/
inductive ROMConservationWitness (Nullifier Opening Sig : Type) where
  /-- Witness for an issuance proof. -/
  | issue (wit : ROMIssueWitness Nullifier Opening)
  /-- Witness for a spend proof. -/
  | spend (wit : ROMSpendWitness Nullifier Opening Sig)
  deriving DecidableEq

/-- Client request in the unextracted ROM conservation game, pairing a public query with its
straight-line extractable VOLEitH proof. -/
structure ROMConservationRequest (Nullifier Context Commitment : Type) (d comLen rowLen : ℕ)
    (Seed IV PreMsg : Type) where
  /-- Public issue or spend query visible to the issuer. -/
  query : ROMConservationQuery Nullifier Context Commitment
  /-- VOLEitH proof for `⟨pk, query⟩`. -/
  proof : VOLEITHProof d comLen rowLen Seed IV PreMsg
  deriving DecidableEq

/-- Public VOLEitH relation checked in the ROM credit-conservation game: an issuance proof opens
the issued commitment, and a spend proof proves a valid input signature, change commitment opening,
and note balance conservation `oldCredit + oldRefund = newCredit + debit`. -/
@[expose] def romConservationRel {PK SK Nullifier Context Opening Commitment Target Sig : Type}
    [DecidableEq Commitment]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig)
    (stmt : ROMConservationStmt PK Nullifier Context Commitment) :
    ROMConservationWitness Nullifier Opening Sig → Bool
  | wit =>
    match stmt.query, wit with
    | .issue q, .issue w => decide (com w.nullifier q.ctx q.amount w.opening = q.commitment)
    | .spend q, .spend w =>
      S.verify stmt.publicKey
          (Credit.target com tag ⟨q.nullifier, q.ctx, w.oldCredit, w.oldRefund⟩ w.oldOpening)
          w.signature &&
        decide (com w.newNullifier q.ctx w.newCredit w.newOpening = q.changeCommitment) &&
        decide (w.oldCredit + w.oldRefund = w.newCredit + q.debit)
    | _, _ => false

/-- Assemble a full `Conservation.Request` from a public ROM request and an extracted witness,
preserving all public fields unconditionally. -/
@[expose] def romConservationToExtractedRequest
    {Nullifier Context Commitment Opening Sig : Type}
    {d comLen rowLen : ℕ} {Seed IV PreMsg : Type}
    [Inhabited Nullifier] [Inhabited Opening] [Inhabited Sig]
    (req : ROMConservationRequest Nullifier Context Commitment d comLen rowLen Seed IV PreMsg)
    (wit : ROMConservationWitness Nullifier Opening Sig) :
    Conservation.Request Nullifier Context Opening Commitment Sig :=
  match req.query with
  | .issue q =>
    match wit with
    | .issue w => .issue ⟨q.ctx, q.amount, q.commitment, w.nullifier, w.opening⟩
    | .spend _ => .issue ⟨q.ctx, q.amount, q.commitment, default, default⟩
  | .spend q =>
    match wit with
    | .spend w =>
      .spend ⟨q.ctx, q.nullifier, q.debit, q.refund, q.changeCommitment,
        w.oldCredit, w.oldOpening, w.oldRefund, w.signature,
        w.newNullifier, w.newCredit, w.newOpening⟩
    | .issue _ =>
      .spend ⟨q.ctx, q.nullifier, q.debit, q.refund, q.changeCommitment,
        0, default, 0, default, default, 0, default⟩

/-- Project a full `Conservation.Request` onto its public `ROMConservationQuery`. -/
@[expose] def romConservationToPublicQuery {Nullifier Context Opening Commitment Sig : Type} :
    Conservation.Request Nullifier Context Opening Commitment Sig →
      ROMConservationQuery Nullifier Context Commitment
  | .issue r => .issue ⟨r.ctx, r.amount, r.commitment⟩
  | .spend r => .spend ⟨r.ctx, r.nullifier, r.debit, r.refund, r.changeCommitment⟩

private theorem romConservationToPublicQuery_toExtractedRequest
    {Nullifier Context Commitment Opening Sig : Type}
    {d comLen rowLen : ℕ} {Seed IV PreMsg : Type}
    [Inhabited Nullifier] [Inhabited Opening] [Inhabited Sig]
    (req : ROMConservationRequest Nullifier Context Commitment d comLen rowLen Seed IV PreMsg)
    (wit : ROMConservationWitness Nullifier Opening Sig) :
    romConservationToPublicQuery (romConservationToExtractedRequest req wit) = req.query := by
  rcases req with ⟨q, proof⟩
  cases q <;> cases wit <;> rfl

private theorem signedMessage_toExtractedRequest
    {Nullifier Context Commitment Opening Target Sig : Type}
    {d comLen rowLen : ℕ} {Seed IV PreMsg : Type}
    [Inhabited Nullifier] [Inhabited Opening] [Inhabited Sig]
    (tag : Commitment → ℕ → Target)
    (req : ROMConservationRequest Nullifier Context Commitment d comLen rowLen Seed IV PreMsg)
    (wit : ROMConservationWitness Nullifier Opening Sig) :
    (romConservationToExtractedRequest req wit).signedMessage tag =
    req.query.signedMessage tag := by
  rcases req with ⟨q, proof⟩
  cases q <;> cases wit <;> rfl

private theorem acceptLocal_toExtractedRequest_of_rel
    {PK SK Nullifier Context Opening Commitment Target Sig : Type}
    {d comLen rowLen : ℕ} {Seed IV PreMsg : Type}
    [DecidableEq Commitment] [Inhabited Nullifier] [Inhabited Opening] [Inhabited Sig]
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (pk : PK)
    (req : ROMConservationRequest Nullifier Context Commitment d comLen rowLen Seed IV PreMsg)
    (wit : ROMConservationWitness Nullifier Opening Sig)
    (hrel : romConservationRel com tag S ⟨pk, req.query⟩ wit = true) :
    Conservation.acceptLocal com tag S pk (romConservationToExtractedRequest req wit) = true := by
  rcases req with ⟨q, proof⟩
  cases q <;> cases wit <;>
    simp only [romConservationRel, romConservationToExtractedRequest, Conservation.acceptLocal,
      Conservation.SpendRequest.inputNote] at hrel ⊢
  · exact hrel
  · cases hrel
  · cases hrel
  · exact hrel

/-- Nullifier spend check on public conservation queries. -/
@[expose] def romHasSpentNullifier {Nullifier Context Commitment : Type}
    [DecidableEq Nullifier] [DecidableEq Context]
    (qs : List (ROMConservationQuery Nullifier Context Commitment))
    (ctx : Context) (nf : Nullifier) : Bool :=
  qs.any fun
    | .issue _ => false
    | .spend s => decide (s.ctx = ctx ∧ s.nullifier = nf)

/-- Public nullifier-freshness check applied by the ROM issuer after proof verification. -/
@[expose] def romAcceptQuery {Nullifier Context Commitment : Type}
    [DecidableEq Nullifier] [DecidableEq Context]
    (accepted : List (ROMConservationQuery Nullifier Context Commitment)) :
    ROMConservationQuery Nullifier Context Commitment → Bool
  | .issue _ => true
  | .spend s => !romHasSpentNullifier accepted s.ctx s.nullifier

/-- Total issued credit in `ctx` over public queries. -/
@[expose] def romIssuedAmount {Nullifier Context Commitment : Type} [DecidableEq Context]
    (qs : List (ROMConservationQuery Nullifier Context Commitment)) (ctx : Context) : ℕ :=
  (qs.filterMap fun
    | .issue q => if q.ctx = ctx then some q.amount else none
    | .spend _ => none).sum

/-- Total granted refunds in `ctx` over public queries. -/
@[expose] def romGrantedRefund {Nullifier Context Commitment : Type} [DecidableEq Context]
    (qs : List (ROMConservationQuery Nullifier Context Commitment)) (ctx : Context) : ℕ :=
  (qs.filterMap fun
    | .issue _ => none
    | .spend q => if q.ctx = ctx then some q.refund else none).sum

/-- Total spent debits in `ctx` over public queries. -/
@[expose] def romSpentDebit {Nullifier Context Commitment : Type} [DecidableEq Context]
    (qs : List (ROMConservationQuery Nullifier Context Commitment)) (ctx : Context) : ℕ :=
  (qs.filterMap fun
    | .issue _ => none
    | .spend q => if q.ctx = ctx then some q.debit else none).sum

private theorem romHasSpentNullifier_map {Nullifier Context Opening Commitment Sig : Type}
    [DecidableEq Nullifier] [DecidableEq Context]
    (reqs : List (Conservation.Request Nullifier Context Opening Commitment Sig))
    (ctx : Context) (nf : Nullifier) :
    romHasSpentNullifier (reqs.map romConservationToPublicQuery) ctx nf =
      Conservation.hasSpentNullifier reqs ctx nf := by
  simp only [romHasSpentNullifier, Conservation.hasSpentNullifier, List.any_map]
  congr 1
  funext x
  cases x <;> rfl

private theorem romIssuedAmount_map {Nullifier Context Opening Commitment Sig : Type}
    [DecidableEq Context]
    (reqs : List (Conservation.Request Nullifier Context Opening Commitment Sig))
    (ctx : Context) :
    romIssuedAmount (reqs.map romConservationToPublicQuery) ctx =
      Conservation.issuedAmount reqs ctx := by
  induction reqs with
  | nil => rfl
  | cons r rs ih =>
    cases r with
    | issue ir =>
      simp only [List.map_cons, romConservationToPublicQuery, romIssuedAmount,
        Conservation.issuedAmount, Conservation.issuesIn, List.filterMap_cons]
      by_cases hctx : ir.ctx = ctx
      · simp only [hctx, ↓reduceIte, List.map_cons, List.sum_cons]
        exact congrArg (ir.amount + ·) ih
      · simp only [hctx, ↓reduceIte]
        exact ih
    | spend sr =>
      change romIssuedAmount (rs.map romConservationToPublicQuery) ctx =
        Conservation.issuedAmount rs ctx
      exact ih

private theorem romGrantedRefund_map {Nullifier Context Opening Commitment Sig : Type}
    [DecidableEq Context]
    (reqs : List (Conservation.Request Nullifier Context Opening Commitment Sig))
    (ctx : Context) :
    romGrantedRefund (reqs.map romConservationToPublicQuery) ctx =
      Conservation.grantedRefund reqs ctx := by
  induction reqs with
  | nil => rfl
  | cons r rs ih =>
    cases r with
    | issue ir =>
      change romGrantedRefund (rs.map romConservationToPublicQuery) ctx =
        Conservation.grantedRefund rs ctx
      exact ih
    | spend sr =>
      simp only [List.map_cons, romConservationToPublicQuery, romGrantedRefund,
        List.filterMap_cons, Conservation.grantedRefund, Conservation.spendsIn, Conservation.spends,
        List.filter_cons, decide_eq_true_eq]
      by_cases hctx : sr.ctx = ctx
      · simp only [hctx, ↓reduceIte, List.map_cons, List.sum_cons]
        exact congrArg (sr.refund + ·) ih
      · simp only [hctx, ↓reduceIte]
        exact ih

private theorem romSpentDebit_map {Nullifier Context Opening Commitment Sig : Type}
    [DecidableEq Context]
    (reqs : List (Conservation.Request Nullifier Context Opening Commitment Sig))
    (ctx : Context) :
    romSpentDebit (reqs.map romConservationToPublicQuery) ctx =
      Conservation.spentDebit reqs ctx := by
  induction reqs with
  | nil => rfl
  | cons r rs ih =>
    cases r with
    | issue ir =>
      change romSpentDebit (rs.map romConservationToPublicQuery) ctx =
        Conservation.spentDebit rs ctx
      exact ih
    | spend sr =>
      simp only [List.map_cons, romConservationToPublicQuery, romSpentDebit, List.filterMap_cons,
        Conservation.spentDebit, Conservation.spendsIn, Conservation.spends,
        List.filter_cons, decide_eq_true_eq]
      by_cases hctx : sr.ctx = ctx
      · simp only [hctx, ↓reduceIte, List.map_cons, List.sum_cons]
        exact congrArg (sr.debit + ·) ih
      · simp only [hctx, ↓reduceIte]
        exact ih

/-- Signing oracle specification returning `some sig` on accepted ROM conservation requests and
`none` otherwise. -/
abbrev ROMConservationIssuerSpec (Nullifier Context Commitment : Type) (d comLen rowLen : ℕ)
    (Seed IV PreMsg Sig : Type) :
    OracleSpec
      (ROMConservationRequest Nullifier Context Commitment d comLen rowLen Seed IV PreMsg) :=
  fun _ => Option Sig

/-- Combined oracle specification exposed to an unextracted ROM conservation adversary. -/
abbrev ROMConservationSpec (Nullifier Context Commitment : Type) (d sdLen comLen rowLen : ℕ)
    (PK Seed IV PreMsg Chal Sig : Type) :=
  ROMConservationIssuerSpec Nullifier Context Commitment d comLen rowLen Seed IV PreMsg Sig ⊕ₒ
    VOLEITHROSpec d sdLen comLen rowLen
      (ROMConservationStmt PK Nullifier Context Commitment) Seed IV PreMsg Chal

/-- Transcript of an unextracted ROM credit-conservation adversary execution. -/
structure ROMConservationExecution (PK Nullifier Context Commitment : Type) where
  /-- Issuer public verification key. -/
  publicKey : PK
  /-- Target context output by the adversary. -/
  targetCtx : Context
  /-- Public queries accepted by the ROM issuer in order. -/
  acceptedQueries : List (ROMConservationQuery Nullifier Context Commitment)

/-- Winning condition for the unextracted ROM conservation adversary: overspending `run.targetCtx`
against `issuedAmount + grantedRefund`. -/
@[expose] def romConservationAccept {PK Nullifier Context Commitment : Type} [DecidableEq Context]
    (run : ROMConservationExecution PK Nullifier Context Commitment) : Bool :=
  decide (romIssuedAmount run.acceptedQueries run.targetCtx +
    romGrantedRefund run.acceptedQueries run.targetCtx <
      romSpentDebit run.acceptedQueries run.targetCtx)

/-- Acceptance continuation for `ROMConservationSpec` that checks `romAcceptQuery`, signs
`req.query.signedMessage tag`, and logs `req.query`. -/
@[expose] noncomputable def romConsAcceptReal {d comLen rowLen : ℕ}
    {PK SK Nullifier Context Commitment Target Seed IV PreMsg Sig : Type}
    [DecidableEq Nullifier] [DecidableEq Context]
    (tag : Commitment → ℕ → Target) (S : Signature.Scheme PK SK Target Sig) (keys : PK × SK)
    (req : ROMConservationRequest Nullifier Context Commitment d comLen rowLen Seed IV PreMsg)
    (accepted : List (ROMConservationQuery Nullifier Context Commitment)) :
    ProbComp (Option Sig × List (ROMConservationQuery Nullifier Context Commitment)) :=
  if romAcceptQuery accepted req.query then
    (S.sign keys.2 (req.query.signedMessage tag)).map fun sig =>
      (some sig, accepted ++ [req.query])
  else
    pure (none, accepted)

/-- Execute an unextracted ROM credit-conservation adversary against the VOLEitH-checked issuer
oracle and lazy two-channel ROM. -/
@[expose] noncomputable def runROMUnextractedConservation {d sdLen comLen rowLen : ℕ}
    {PK SK Nullifier Context Commitment Target Seed IV PreMsg Chal Sig : Type}
    [DecidableEq Nullifier] [DecidableEq Context]
    [BEq (LeafQuery d Seed IV)]
    [BEq (FSQuery d comLen rowLen (ROMConservationStmt PK Nullifier Context Commitment) IV PreMsg)]
    [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (tag : Commitment → ℕ → Target)
    (checkRel : ROMConservationStmt PK Nullifier Context Commitment →
      (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (S : Signature.Scheme PK SK Target Sig)
    (A : PK → ProbOracleComp (ROMConservationSpec Nullifier Context Commitment
      d sdLen comLen rowLen PK Seed IV PreMsg Chal Sig) Context) :
    ProbComp (ROMConservationExecution PK Nullifier Context Commitment) := do
  let keys ← S.keyGen
  let ⟨targetCtx, _, acceptedQueries⟩ ← ((A keys.1).runState
    (verifyGatedHandlerProg (comLen := comLen) (Seed := Seed) (IV := IV)
      expand chalToIdx (fun req => ⟨keys.1, req.query⟩) ROMConservationRequest.proof
      checkRel none (romConsAcceptReal tag S keys))).run (([], []), [])
  pure { publicKey := keys.1, targetCtx := targetCtx, acceptedQueries := acceptedQueries }

/-- Unextracted ROM credit-conservation experiment, original to this library (client `query`
fields are public, while note commitments, openings, old balances, and input signatures are
proven in zero knowledge): wins if the accepted ROM query transcript overspends
`run.targetCtx`. -/
@[expose] noncomputable def romUnextractedConservationExperiment {d sdLen comLen rowLen : ℕ}
    {PK SK Nullifier Context Commitment Target Seed IV PreMsg Chal Sig : Type}
    [DecidableEq Nullifier] [DecidableEq Context]
    [BEq (LeafQuery d Seed IV)]
    [BEq (FSQuery d comLen rowLen (ROMConservationStmt PK Nullifier Context Commitment) IV PreMsg)]
    [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (tag : Commitment → ℕ → Target)
    (checkRel : ROMConservationStmt PK Nullifier Context Commitment →
      (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (S : Signature.Scheme PK SK Target Sig)
    (A : PK → ProbOracleComp (ROMConservationSpec Nullifier Context Commitment
      d sdLen comLen rowLen PK Seed IV PreMsg Chal Sig) Context) : Experiment :=
  romConservationAccept <$>
    runROMUnextractedConservation expand chalToIdx tag checkRel S A

private noncomputable def consToExtractedInner {d sdLen comLen rowLen : ℕ}
    {PK Nullifier Context Opening Commitment Seed IV PreMsg Chal Sig : Type}
    [BEq (LeafQuery d Seed IV)]
    [BEq (FSQuery d comLen rowLen (ROMConservationStmt PK Nullifier Context Commitment) IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    [Inhabited Nullifier] [Inhabited Opening] [Inhabited Sig]
    (expand : BitString sdLen → BitString rowLen)
    (decWit : BitString rowLen → ROMConservationWitness Nullifier Opening Sig)
    (chalToIdx : Chal → Fin (2 ^ d))
    (checkRel : ROMConservationStmt PK Nullifier Context Commitment →
      (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (pk : PK) :
    (q : ROMConservationRequest Nullifier Context Commitment d comLen rowLen Seed IV PreMsg ⊕
      (LeafQuery d Seed IV ⊕
        FSQuery d comLen rowLen (ROMConservationStmt PK Nullifier Context Commitment) IV PreMsg)) →
      StateT (VOLEITHTraceState d sdLen comLen rowLen
          (ROMConservationStmt PK Nullifier Context Commitment) Seed IV PreMsg Chal)
        (ProbOracleComp (fun _ : Conservation.Request Nullifier Context Opening Commitment Sig =>
          Option Sig))
        (ROMConservationSpec Nullifier Context Commitment d sdLen comLen rowLen
          PK Seed IV PreMsg Chal Sig q)
  | .inl req, roSt => do
    let (ok, roSt') ← ProbOracleComp.sample ((ProbOracleComp.runState
      (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel
        ⟨pk, req.query⟩ req.proof)
      voleithMemoizeProg).run roSt)
    if ok then
      let wit := extractWitnessFromTrace expand decWit roSt.1 req.proof
      let sig ← ProbOracleComp.query (romConservationToExtractedRequest req wit)
      pure (sig, roSt')
    else
      pure (none, roSt')
  | .inr qRO, roSt => do
    let (ans, roSt') ← ProbOracleComp.sample ((voleithMemoizeProg qRO).run roSt)
    pure (ans, roSt')

/-- Straight-line extracted-model `Conservation.ExtractedAdversary` constructed from an
unextracted ROM conservation adversary `A`: simulates `VOLEITHROSpec` locally, checks
`voleithVerifyROM`, and whenever a request verifies, extracts the witness without rewinding and
forwards `romConservationToExtractedRequest req wit` to the extracted issuer oracle. -/
noncomputable def extractedAdversaryOfROM {d sdLen comLen rowLen : ℕ}
    {PK Nullifier Context Opening Commitment Seed IV PreMsg Chal Sig : Type}
    [BEq (LeafQuery d Seed IV)]
    [BEq (FSQuery d comLen rowLen (ROMConservationStmt PK Nullifier Context Commitment) IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    [Inhabited Nullifier] [Inhabited Opening] [Inhabited Sig]
    (expand : BitString sdLen → BitString rowLen)
    (decWit : BitString rowLen → ROMConservationWitness Nullifier Opening Sig)
    (chalToIdx : Chal → Fin (2 ^ d))
    (checkRel : ROMConservationStmt PK Nullifier Context Commitment →
      (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (A : PK → ProbOracleComp (ROMConservationSpec Nullifier Context Commitment
      d sdLen comLen rowLen PK Seed IV PreMsg Chal Sig) Context) :
    Conservation.ExtractedAdversary Nullifier Context Opening Commitment PK Sig := fun pk =>
  Prod.fst <$> (OracleComp.interpret
    (OracleComp.sumHandler
      (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
      (consToExtractedInner expand decWit chalToIdx checkRel pk))
    (A pk)).run ([], [])

/-- `extractedAdversaryOfROM` preserves issuer-query budgets: every `VOLEITHROSpec` call costs `0`
extracted issuer queries and every ROM request calls the extracted issuer at most once. -/
theorem extractedAdversaryOfROM_isQueryBounded {d sdLen comLen rowLen : ℕ}
    {PK Nullifier Context Opening Commitment Seed IV PreMsg Chal Sig : Type}
    [BEq (LeafQuery d Seed IV)]
    [BEq (FSQuery d comLen rowLen (ROMConservationStmt PK Nullifier Context Commitment) IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    [Inhabited Nullifier] [Inhabited Opening] [Inhabited Sig]
    (expand : BitString sdLen → BitString rowLen)
    (decWit : BitString rowLen → ROMConservationWitness Nullifier Opening Sig)
    (chalToIdx : Chal → Fin (2 ^ d))
    (checkRel : ROMConservationStmt PK Nullifier Context Commitment →
      (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (A : PK → ProbOracleComp (ROMConservationSpec Nullifier Context Commitment
      d sdLen comLen rowLen PK Seed IV PreMsg Chal Sig) Context)
    {m : ℕ}
    (hm : ∀ pk, IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 1) (fun _ => 0))) (A pk) m) :
    ∀ pk, (extractedAdversaryOfROM expand decWit chalToIdx checkRel A pk).IsQueryBounded m := by
  intro pk
  unfold extractedAdversaryOfROM
  rw [ProbOracleComp.IsQueryBounded, OracleComp.isCostBounded_map_iff]
  refine run_interpret_sumUnif_isCostBounded
    (consToExtractedInner expand decWit chalToIdx checkRel pk)
    (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun req roSt => ?_) (fun qRO roSt => ?_)
    (A pk) ([], []) (hm pk)
  · simpa only [StateT.run, consToExtractedInner] using
      isCostBounded_sample_ite_query
        (spec := fun _ : Conservation.Request Nullifier Context Opening Commitment Sig =>
          Option Sig)
        (R := Option Sig)
        ((ProbOracleComp.runState
          (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel ⟨pk, req.query⟩ req.proof)
          voleithMemoizeProg).run roSt)
        (romConservationToExtractedRequest req
          (extractWitnessFromTrace expand decWit roSt.1 req.proof))
        (fun roSt' sig => (sig, roSt')) (fun roSt' => (none, roSt'))
  · simp only [StateT.run, consToExtractedInner]
    rw [show (0 : ℕ) = 0 + 0 from rfl]
    exact (ProbOracleComp.isCostBounded_sample _ _).bind fun _ =>
      OracleComp.IsCostBounded.pure _ 0

private noncomputable def romConsAcceptExt {d sdLen comLen rowLen : ℕ}
    {PK SK Nullifier Context Opening Commitment Target Seed IV PreMsg Sig : Type}
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [DecidableEq IV] [Inhabited Nullifier] [Inhabited Opening] [Inhabited Sig]
    (expand : BitString sdLen → BitString rowLen)
    (decWit : BitString rowLen → ROMConservationWitness Nullifier Opening Sig)
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig) (keys : PK × SK)
    (tr₁ : LeafTrace d sdLen comLen Seed IV)
    (req : ROMConservationRequest Nullifier Context Commitment d comLen rowLen Seed IV PreMsg)
    (accepted : List (ROMConservationQuery Nullifier Context Commitment)) :
    ProbComp (Option Sig × List (ROMConservationQuery Nullifier Context Commitment)) :=
  let extReq := romConservationToExtractedRequest req
    (extractWitnessFromTrace expand decWit tr₁ req.proof)
  if Conservation.acceptLocal com tag S keys.1 extReq && romAcceptQuery accepted req.query then
    (S.sign keys.2 (extReq.signedMessage tag)).map fun sig =>
      (some sig, accepted ++ [req.query])
  else
    pure (none, accepted)

/-- Concrete query-bounded advantage bound (not an asymptotic PPT security theorem):
reduction from the unextracted ROM credit-conservation game to
`Conservation.extractedConservationExperiment`: an adversary making at most `m` signing queries,
`Q_leaf` leaf RO queries, and `Q_FS` Fiat–Shamir queries loses at most
`voleithKSBound d comLen (Q_leaf + m * (2 ^ d - 1)) (Q_FS + m) ε_rel` when lifted to the extracted
conservation experiment via `extractedAdversaryOfROM`. -/
theorem unextractedConservationExperiment_succProbability_le_extracted {d sdLen comLen rowLen : ℕ}
    {PK SK Nullifier Context Opening Commitment Target Seed IV PreMsg Chal Sig : Type}
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [Inhabited Nullifier] [Inhabited Opening] [Inhabited Sig]
    [BEq (LeafQuery d Seed IV)] [LawfulBEq (LeafQuery d Seed IV)]
    [BEq (FSQuery d comLen rowLen (ROMConservationStmt PK Nullifier Context Commitment) IV PreMsg)]
    [LawfulBEq (FSQuery d comLen rowLen
      (ROMConservationStmt PK Nullifier Context Commitment) IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen)
    (decWit : BitString rowLen → ROMConservationWitness Nullifier Opening Sig)
    (chalToIdx : Chal → Fin (2 ^ d))
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (tag : Commitment → ℕ → Target)
    (S : Signature.Scheme PK SK Target Sig)
    (checkRel : ROMConservationStmt PK Nullifier Context Commitment →
      (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    {ε_rel : ℝ≥0}
    (hSound : VOLEITHSoundnessError decWit chalToIdx (romConservationRel com tag S) checkRel ε_rel)
    (A : PK → ProbOracleComp (ROMConservationSpec Nullifier Context Commitment
      d sdLen comLen rowLen PK Seed IV PreMsg Chal Sig) Context)
    {m Q_leaf Q_FS : ℕ}
    (hm : ∀ pk, IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 1) (fun _ => 0))) (A pk) m)
    (hleaf : ∀ pk, IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 0) voleithLeafCost)) (A pk) Q_leaf)
    (hfs : ∀ pk, IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 0) voleithFSCost)) (A pk) Q_FS) :
    (romUnextractedConservationExperiment expand chalToIdx tag checkRel S A).succProbability ≤
      (Conservation.extractedConservationExperiment com tag S
        (extractedAdversaryOfROM expand decWit chalToIdx checkRel A)).succProbability +
        voleithKSBound d comLen (Q_leaf + m * (2 ^ d - 1)) (Q_FS + m) ε_rel := by
  let romSticky := fun keys : PK × SK =>
    verifyGatedStickyHandler (comLen := comLen) (Seed := Seed) (IV := IV)
      expand decWit chalToIdx (romConservationRel com tag S)
      (fun req => ⟨keys.1, req.query⟩) ROMConservationRequest.proof checkRel
      (none : Option Sig) (fun _ => romConsAcceptReal tag S keys)
  let extSticky := fun keys : PK × SK =>
    verifyGatedStickyHandler (comLen := comLen) (Seed := Seed) (IV := IV)
      expand decWit chalToIdx (romConservationRel com tag S)
      (fun req => ⟨keys.1, req.query⟩) ROMConservationRequest.proof checkRel
      (none : Option Sig) (romConsAcceptExt expand decWit com tag S keys)
  let extH := fun keys : PK × SK =>
    verifyGatedHandler (comLen := comLen) (Seed := Seed) (IV := IV)
      expand chalToIdx (fun req => ⟨keys.1, req.query⟩) ROMConservationRequest.proof checkRel
      (none : Option Sig) (romConsAcceptExt expand decWit com tag S keys)
  have hrom_eval :
      ProbComp.eval (romUnextractedConservationExperiment expand chalToIdx tag checkRel S A) =
        (ProbComp.eval S.keyGen).bind fun keys =>
          (ProbOracleComp.runWith (romSticky keys) (A keys.1) ((([], []), []), false)).map
            fun (ctx, ((_, accepted), _)) =>
              decide (romIssuedAmount accepted ctx + romGrantedRefund accepted ctx <
                romSpentDebit accepted ctx) := by
    simp only [romUnextractedConservationExperiment, runROMUnextractedConservation,
      ProbComp.eval_map, ProbComp.eval_bind, ProbComp.eval_pure, ProbOracleComp.eval_runState,
      PMF.map_bind]
    congr 1
    funext keys
    have hev :
        (fun q st => ProbComp.eval (verifyGatedHandlerProg (comLen := comLen) (Seed := Seed)
            (IV := IV) expand chalToIdx (fun req => ⟨keys.1, req.query⟩)
            ROMConservationRequest.proof checkRel none (romConsAcceptReal tag S keys) q st)) =
          verifyGatedHandler (comLen := comLen) (Seed := Seed) (IV := IV)
            expand chalToIdx (fun req => ⟨keys.1, req.query⟩) ROMConservationRequest.proof
            checkRel none (fun _ => romConsAcceptReal tag S keys) :=
      funext fun q => funext fun st =>
        verifyGatedHandlerProg_eval expand chalToIdx (fun req => ⟨keys.1, req.query⟩)
          ROMConservationRequest.proof checkRel none (romConsAcceptReal tag S keys) q st
    have hforget := ProbOracleComp.runWith_map_state _ _ Prod.fst
      (verifyGatedStickyHandler_map_forget expand decWit chalToIdx (romConservationRel com tag S)
        (fun req => ⟨keys.1, req.query⟩) ROMConservationRequest.proof checkRel none
        (fun _ => romConsAcceptReal tag S keys))
      (A keys.1) ((([], []), []), false)
    rw [hev, ← hforget]
    simp only [PMF.map, PMF.bind_bind, Function.comp_def, PMF.pure_bind,
      romConservationAccept, romSticky]
  have hext_eval :
      ProbComp.eval (Conservation.extractedConservationExperiment com tag S
        (extractedAdversaryOfROM expand decWit chalToIdx checkRel A)) =
        (ProbComp.eval S.keyGen).bind fun keys =>
          (ProbOracleComp.runWith (extSticky keys) (A keys.1) ((([], []), []), false)).map
            fun (ctx, ((_, accepted), _)) =>
              decide (romIssuedAmount accepted ctx + romGrantedRefund accepted ctx <
                romSpentDebit accepted ctx) := by
    simp only [Conservation.extractedConservationExperiment,
      Conservation.runExtractedConservation, extractedAdversaryOfROM, ProbComp.eval_map,
      ProbComp.eval_bind, ProbComp.eval_pure, PMF.map, PMF.bind_bind, Function.comp_def,
      PMF.pure_bind]
    congr 1
    funext keys
    let issuerH : Conservation.Request Nullifier Context Opening Commitment Sig →
        StateT (List (Conservation.Request Nullifier Context Opening Commitment Sig × Option Sig))
          PMF (Option Sig) := fun q log =>
      if Conservation.acceptRequest com tag S keys.1 (log.map Prod.fst) q then
        (ProbComp.eval (S.sign keys.2 (q.signedMessage tag))).map fun sig =>
          (some sig, log ++ [(q, some sig)])
      else
        PMF.pure (none, log)
    have hlog_map :
        ProbComp.eval ((Prod.fst <$> (OracleComp.interpret
            (OracleComp.sumHandler
              (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
              (consToExtractedInner expand decWit chalToIdx checkRel keys.1))
            (A keys.1)).run ([], [])).runLogWith
            (Conservation.extractedIssuerOracle com tag S keys)) =
          (ProbOracleComp.runWith issuerH ((OracleComp.interpret
              (OracleComp.sumHandler
                (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
                (consToExtractedInner expand decWit chalToIdx checkRel keys.1))
              (A keys.1)).run ([], [])) []).map (Prod.map Prod.fst id) := by
      simp only [ProbOracleComp.runLogWith, ProbOracleComp.runState_map, StateT.run_map,
        ProbOracleComp.eval_runState, ProbComp.eval_map]
      congr 2
      funext q log
      simp only [ProbOracleComp.logOracle, Conservation.extractedIssuerOracle, issuerH]
      by_cases hacc : Conservation.acceptRequest com tag S keys.1 (log.map Prod.fst) q
      · simp only [hacc, ↓reduceIte, ProbComp.eval_map, PMF.map_comp]
        rfl
      · simp only [hacc, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure]
        rfl
    change (ProbComp.eval (ProbOracleComp.runLogWith (Prod.fst <$>
      (OracleComp.interpret
        (OracleComp.sumHandler
          (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
          (consToExtractedInner expand decWit chalToIdx checkRel keys.1))
        (A keys.1)).run ([], []))
        (Conservation.extractedIssuerOracle com tag S keys))).bind _ = _
    rw [hlog_map]
    have hrun := ProbOracleComp.runWith_run_interpret
      (consToExtractedInner expand decWit chalToIdx checkRel keys.1) issuerH (A keys.1) ([], []) []
    let repCons : VOLEITHTraceState d sdLen comLen rowLen
          (ROMConservationStmt PK Nullifier Context Commitment) Seed IV PreMsg Chal ×
        List (Conservation.Request Nullifier Context Opening Commitment Sig × Option Sig) →
        VOLEITHTraceState d sdLen comLen rowLen
          (ROMConservationStmt PK Nullifier Context Commitment) Seed IV PreMsg Chal ×
          List (ROMConservationQuery Nullifier Context Commitment) :=
      fun (roSt, log) => (roSt, log.map (romConservationToPublicQuery ∘ Prod.fst))
    have hjoint_eq :
        ((ProbOracleComp.runWith
            (fun q state =>
              PMF.map (fun ⟨⟨a, b⟩, c⟩ => (a, b, c))
                (ProbOracleComp.runWith issuerH
                  ((consToExtractedInner expand decWit chalToIdx checkRel keys.1 q).run state.1)
                  state.2))
            (A keys.1) (([], []), [])).map (Prod.map id repCons)) =
          ProbOracleComp.runWith (extH keys) (A keys.1) (([], []), []) := by
      refine ProbOracleComp.runWith_map_state _ _ repCons (fun q x => ?_)
        (A keys.1) (([], []), [])
      rcases x with ⟨roSt, log⟩
      rcases q with req | qRO
      · simp only [consToExtractedInner, StateT.run, ProbOracleComp.runWith_bind,
          ProbOracleComp.runWith_sample, extH, verifyGatedHandler]
        have hmem :
            ProbComp.eval ((ProbOracleComp.runState
                (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel
                  ⟨keys.1, req.query⟩ req.proof)
                voleithMemoizeProg) roSt) =
              ProbOracleComp.runWith voleithMemoize
                (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel
                  ⟨keys.1, req.query⟩ req.proof)
                roSt := by
          change ProbComp.eval (((ProbOracleComp.runState
            (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel
              ⟨keys.1, req.query⟩ req.proof)
            voleithMemoizeProg).run roSt)) = _
          rw [ProbOracleComp.eval_runState]
          congr 2
          exact funext fun q' => funext fun s' => eval_voleithMemoizeProg q' s'
        rw [hmem]
        simp only [PMF.map, PMF.bind_bind, Function.comp_def, PMF.pure_bind]
        congr 1
        funext ⟨ok, roSt'⟩
        cases ok
        · simp only [Bool.false_eq_true, ↓reduceIte, ProbOracleComp.runWith_pure, PMF.pure_bind,
            repCons]
        · dsimp only
          simp only [↓reduceIte, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
            ProbOracleComp.runWith_pure, issuerH, repCons, Function.comp_def]
          set extReq := romConservationToExtractedRequest req
            (extractWitnessFromTrace expand decWit roSt.1 req.proof)
          have hacc_eq :
              Conservation.acceptRequest com tag S keys.1 (log.map Prod.fst) extReq =
                (Conservation.acceptLocal com tag S keys.1 extReq &&
                  romAcceptQuery (log.map fun x =>
                    romConservationToPublicQuery x.1) req.query) := by
            rcases req with ⟨q, proof⟩
            cases q with
            | issue iq =>
              simp only [extReq, romConservationToExtractedRequest, Conservation.acceptRequest,
                romAcceptQuery, Bool.and_true]
              cases extractWitnessFromTrace expand decWit roSt.1 proof <;> rfl
            | spend sq =>
              simp only [extReq, romConservationToExtractedRequest]
              cases hwt : extractWitnessFromTrace expand decWit roSt.1 proof <;>
                simp [Conservation.acceptRequest, romAcceptQuery, ← romHasSpentNullifier_map,
                  List.map_map, Function.comp_def]
          rw [hacc_eq]
          by_cases hacc :
              Conservation.acceptLocal com tag S keys.1 extReq &&
                romAcceptQuery
                  (log.map fun x => romConservationToPublicQuery x.1) req.query
          · simp only [hacc, ↓reduceIte, PMF.map, PMF.bind_bind, Function.comp_def,
              PMF.pure_bind, List.map_append, List.map_cons, List.map_nil,
              extReq, romConservationToPublicQuery_toExtractedRequest, romConsAcceptExt,
              ProbComp.eval_freeMMap]
          · simp only [romConsAcceptExt, extReq, Bool.eq_false_iff.mpr hacc, Bool.false_eq_true,
              ↓reduceIte, ProbComp.eval_pure, PMF.pure_bind]
      · simp only [consToExtractedInner, StateT.run, ProbOracleComp.runWith_bind,
          ProbOracleComp.runWith_sample, ProbOracleComp.runWith_pure, repCons, extH,
          verifyGatedHandler, PMF.map, PMF.bind_bind, Function.comp_def, PMF.pure_bind,
          eval_voleithMemoizeProg]
    have hforget := ProbOracleComp.runWith_map_state _ _ Prod.fst
      (verifyGatedStickyHandler_map_forget expand decWit chalToIdx (romConservationRel com tag S)
        (fun req => ⟨keys.1, req.query⟩) ROMConservationRequest.proof checkRel none
        (romConsAcceptExt expand decWit com tag S keys))
      (A keys.1) ((([], []), []), false)
    rw [hrun]
    have hleft :
        ((PMF.map (Prod.map Prod.fst id)
            (PMF.map (fun ⟨a, b, c⟩ => ((a, b), c))
              (ProbOracleComp.runWith
                (fun q state =>
                  PMF.map (fun ⟨⟨a, b⟩, c⟩ => (a, b, c))
                    (ProbOracleComp.runWith issuerH
                      ((consToExtractedInner expand decWit chalToIdx checkRel keys.1 q).run
                        state.1)
                      state.2))
                (A keys.1) (([], []), [])))).bind
          fun a => PMF.pure
            (Conservation.extractedConservationAccept ⟨keys.1, a.1, a.2⟩)) =
        ((ProbOracleComp.runWith
            (fun q state =>
              PMF.map (fun ⟨⟨a, b⟩, c⟩ => (a, b, c))
                (ProbOracleComp.runWith issuerH
                  ((consToExtractedInner expand decWit chalToIdx checkRel keys.1 q).run state.1)
                  state.2))
            (A keys.1) (([], []), [])).map (Prod.map id repCons)).bind
          fun x => PMF.pure
            (decide (romIssuedAmount x.2.2 x.1 + romGrantedRefund x.2.2 x.1 <
              romSpentDebit x.2.2 x.1)) := by
      simp only [PMF.map, PMF.bind_bind, Function.comp_def, PMF.pure_bind,
        Conservation.extractedConservationAccept, repCons, Prod.map, id_eq]
      congr 1
      funext ⟨ctx, roSt, log⟩
      rw [← romIssuedAmount_map, ← romGrantedRefund_map, ← romSpentDebit_map, List.map_map]
      rfl
    rw [hleft, hjoint_eq, ← hforget]
    simp only [PMF.map, PMF.bind_bind, Function.comp_def, PMF.pure_bind, extSticky]
  have hkey_le : ∀ keys : PK × SK,
      ((ProbOracleComp.runWith (romSticky keys) (A keys.1) ((([], []), []), false)).map
        fun (ctx, ((_, accepted), _)) =>
          decide (romIssuedAmount accepted ctx + romGrantedRefund accepted ctx <
            romSpentDebit accepted ctx)) true ≤
      ((ProbOracleComp.runWith (extSticky keys) (A keys.1) ((([], []), []), false)).map
        fun (ctx, ((_, accepted), _)) =>
          decide (romIssuedAmount accepted ctx + romGrantedRefund accepted ctx <
            romSpentDebit accepted ctx)) true +
        (voleithKSBound d comLen (Q_leaf + m * (2 ^ d - 1)) (Q_FS + m) ε_rel : ℝ≥0∞) := by
    intro keys
    have hiub := ProbOracleComp.IdenticalUntilBad.bind_apply_le
      (verifyGatedSticky_identicalUntilBad expand decWit chalToIdx (romConservationRel com tag S)
        (fun req => ⟨keys.1, req.query⟩) ROMConservationRequest.proof checkRel
        (none : Option Sig) (fun _ => romConsAcceptReal tag S keys)
        (romConsAcceptExt expand decWit com tag S keys)
        (fun tr req accepted hrel => by
          have hloc := acceptLocal_toExtractedRequest_of_rel com tag S keys.1 req
            (extractWitnessFromTrace expand decWit tr req.proof) hrel
          have hmsg := signedMessage_toExtractedRequest tag req
            (extractWitnessFromTrace expand decWit tr req.proof)
          simp [romConsAcceptReal, romConsAcceptExt, hloc, hmsg]))
      (A keys.1) ((([], []), []), false)
      (fun (ctx, ((_, accepted), _)) =>
        PMF.pure (decide (romIssuedAmount accepted ctx + romGrantedRefund accepted ctx <
          romSpentDebit accepted ctx)))
      true
    have hbad := verifyGatedSticky_bad_le expand decWit chalToIdx (romConservationRel com tag S)
      (fun req => ⟨keys.1, req.query⟩) ROMConservationRequest.proof checkRel hSound none
      (romConsAcceptReal tag S keys) [] (A keys.1) (hm keys.1) (hleaf keys.1) (hfs keys.1)
    exact hiub.trans (add_le_add_right hbad _)
  exact bind_tsum_add_voleithKSBound_toNNReal _ _ (ProbComp.eval S.keyGen) _ _ _ hkey_le
    hrom_eval hext_eval

/-- Concrete query-bounded advantage bound (not an asymptotic PPT security theorem):
end-to-end ROM reduction for `AnonymousToken.Conservation` composing straight-line leaf
extraction with `Conservation.extractedConservationExperiment_succProbability_le_prod_mk` to bound
an unextracted ROM conservation adversary's overspending probability by EUF-CMA against
`noteForger`, commitment binding against `commitmentBindingReduction`, and `voleithKSBound`. -/
theorem unextractedConservationExperiment_succProbability_le_prod_mk
    {d sdLen comLen rowLen : ℕ}
    {K PK SK Nullifier Context Opening Commitment Seed IV PreMsg Chal Sig : Type}
    [DecidableEq Nullifier] [DecidableEq Context] [DecidableEq Commitment]
    [Inhabited Nullifier] [Inhabited Context] [Inhabited Opening] [Inhabited Sig]
    [BEq (LeafQuery d Seed IV)] [LawfulBEq (LeafQuery d Seed IV)]
    [BEq (FSQuery d comLen rowLen (ROMConservationStmt PK Nullifier Context Commitment) IV PreMsg)]
    [LawfulBEq (FSQuery d comLen rowLen
      (ROMConservationStmt PK Nullifier Context Commitment) IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen)
    (decWit : BitString rowLen → ROMConservationWitness Nullifier Opening Sig)
    (chalToIdx : Chal → Fin (2 ^ d))
    (com : Nullifier → Context → ℕ → Opening → Commitment)
    (CS : Crypto.Commitment.Scheme K (Nullifier × Context × ℕ) Commitment Opening)
    (hverify : ∀ k nf ctx t c o, CS.verify k (nf, ctx, t) c o = decide (com nf ctx t o = c))
    (S : Signature.Scheme PK SK (Commitment × ℕ) Sig)
    (checkRel : ROMConservationStmt PK Nullifier Context Commitment →
      (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    {ε_rel : ℝ≥0}
    (hSound : VOLEITHSoundnessError decWit chalToIdx (romConservationRel com Prod.mk S)
      checkRel ε_rel)
    (A : PK → ProbOracleComp (ROMConservationSpec Nullifier Context Commitment
      d sdLen comLen rowLen PK Seed IV PreMsg Chal Sig) Context)
    {m Q_leaf Q_FS : ℕ}
    (hm : ∀ pk, IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 1) (fun _ => 0))) (A pk) m)
    (hleaf : ∀ pk, IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 0) voleithLeafCost)) (A pk) Q_leaf)
    (hfs : ∀ pk, IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 0) voleithFSCost)) (A pk) Q_FS) :
    (romUnextractedConservationExperiment expand chalToIdx Prod.mk checkRel S A).succProbability ≤
      (S.eufCmaExperiment (targetForger (Credit.target com Prod.mk)
          (Conservation.noteForger com Prod.mk S
            (extractedAdversaryOfROM expand decWit chalToIdx checkRel A)))).succProbability +
        (CS.bindingExperiment (Conservation.commitmentBindingReduction com S
          (extractedAdversaryOfROM expand decWit chalToIdx checkRel A))).succProbability +
        voleithKSBound d comLen (Q_leaf + m * (2 ^ d - 1)) (Q_FS + m) ε_rel := by
  refine (unextractedConservationExperiment_succProbability_le_extracted expand decWit chalToIdx
    com Prod.mk S checkRel hSound A hm hleaf hfs).trans ?_
  exact add_le_add_left
    (Conservation.extractedConservationExperiment_succProbability_le_prod_mk
      com CS hverify S _) _

end ConservationBridge

/-! ### PRG Leaf Commitment Separation (`leaf_hash::aes_ctr`) -/

section PRGSeparation

/-- Local deterministic PRG leaf verification (`leaf_hash::aes_ctr` style): checks the `2 ^ d - 1`
non-hidden commitments `prgLeaf (openKeys pIdx) iv pIdx` locally without querying `H_leaf`, and
reconstructs `verifierRows` (`0` at `vIdx = 0`). -/
@[expose] def prgLeafOpenRows {d sdLen comLen rowLen : ℕ} {Seed IV : Type}
    (expand : BitString sdLen → BitString rowLen)
    (prgLeaf : Seed → IV → Fin (2 ^ d) → LeafOutput sdLen comLen)
    (iv : IV) (openKeys : Fin (2 ^ d) → Seed) (coms : Fin (2 ^ d) → BitString comLen)
    (hidden : Fin (2 ^ d)) : Option (Fin (2 ^ d) → BitString rowLen) :=
  if ∀ vIdx : Fin (2 ^ d), vIdx = 0 ∨
      (prgLeaf (openKeys (FAEST.xorIndex vIdx hidden)) iv
        (FAEST.xorIndex vIdx hidden)).com = coms (FAEST.xorIndex vIdx hidden) then
    some fun vIdx =>
      if vIdx = 0 then 0 else
        expand (prgLeaf (openKeys (FAEST.xorIndex vIdx hidden)) iv
          (FAEST.xorIndex vIdx hidden)).seedOut
  else
    none

/-- Verifier for PRG-based leaf commitments in `VOLEITHROSpec`: queries only `H_FS` for `Δ` and
checks all `2 ^ d - 1` non-hidden leaves locally via `prgLeafOpenRows`. -/
@[expose] def prgLeafVerify {d sdLen comLen rowLen : ℕ} {Stmt Seed IV PreMsg Chal : Type}
    (expand : BitString sdLen → BitString rowLen)
    (prgLeaf : Seed → IV → Fin (2 ^ d) → LeafOutput sdLen comLen)
    (chalToIdx : Chal → Fin (2 ^ d))
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (stmt : Stmt) (prf : VOLEITHProof d comLen rowLen Seed IV PreMsg) :
    ProbOracleComp (VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) Bool := do
  let delta ← OracleComp.liftRight (spec₁ := unifSpec)
    (OracleComp.liftRight (spec₁ := VOLEITHLeafSpec d sdLen comLen Seed IV)
      (OracleComp.query (prf.fsQuery stmt)))
  let hidden := chalToIdx delta
  match prgLeafOpenRows expand prgLeaf prf.iv prf.openKeys prf.coms hidden with
  | none => return false
  | some rows =>
    let qCols := (FAEST.convertExpandedRows d rows).columns
    return checkRel stmt qCols prf.dCorr prf.preMsg delta

/-- Honest local-PRG prover (`leaf_hash::aes_ctr` style): commits all `2 ^ d` leaves locally via
`prgLeaf` with `0` queries to `H_leaf`, then queries `H_FS` once for `Δ`. -/
@[expose] def prgLeafProver {d sdLen comLen rowLen : ℕ} {Stmt Seed IV PreMsg Chal Wit : Type}
    (expand : BitString sdLen → BitString rowLen)
    (prgLeaf : Seed → IV → Fin (2 ^ d) → LeafOutput sdLen comLen)
    (encWit : Wit → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (mkPreMsg : (Fin d → BitString rowLen) → BitString rowLen → BitString rowLen → PreMsg)
    (defaultSeed : Seed) (iv : IV) (keys : Fin (2 ^ d) → Seed) (stmt : Stmt) (w : Wit) :
    ProbOracleComp (VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal)
      (VOLEITHProof d comLen rowLen Seed IV PreMsg) := do
  let rows : Fin (2 ^ d) → BitString rowLen :=
    fun idx => expand (prgLeaf (keys idx) iv idx).seedOut
  let coms : Fin (2 ^ d) → BitString comLen := fun idx => (prgLeaf (keys idx) iv idx).com
  let conv := FAEST.convertExpandedRows d rows
  let dCorr := encWit w + conv.u
  let preMsg := mkPreMsg conv.columns conv.u dCorr
  let delta ← OracleComp.liftRight (spec₁ := unifSpec)
    (OracleComp.liftRight (spec₁ := VOLEITHLeafSpec d sdLen comLen Seed IV)
      (OracleComp.query ⟨stmt, iv, coms, dCorr, preMsg⟩))
  let hidden := chalToIdx delta
  let openKeys : Fin (2 ^ d) → Seed := fun idx => if idx = hidden then defaultSeed else keys idx
  return ⟨iv, coms, dCorr, preMsg, openKeys⟩

/-- Honest PRG prover-then-verifier execution in `VOLEITHROSpec`. -/
@[expose] def prgLeafGame {d sdLen comLen rowLen : ℕ} {Stmt Seed IV PreMsg Chal Wit : Type}
    (expand : BitString sdLen → BitString rowLen)
    (prgLeaf : Seed → IV → Fin (2 ^ d) → LeafOutput sdLen comLen)
    (encWit : Wit → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (mkPreMsg : (Fin d → BitString rowLen) → BitString rowLen → BitString rowLen → PreMsg)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (defaultSeed : Seed) (iv : IV) (keys : Fin (2 ^ d) → Seed) (stmt : Stmt) (w : Wit) :
    ProbOracleComp (VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) Bool := do
  let prf ← prgLeafProver expand prgLeaf encWit chalToIdx mkPreMsg defaultSeed iv keys stmt w
  prgLeafVerify expand prgLeaf chalToIdx checkRel stmt prf

/-- `prgLeafProver` makes strictly zero queries to the leaf random oracle `H_leaf`. -/
theorem prgLeafProver_leafCost_zero {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit : Type}
    (expand : BitString sdLen → BitString rowLen)
    (prgLeaf : Seed → IV → Fin (2 ^ d) → LeafOutput sdLen comLen)
    (encWit : Wit → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (mkPreMsg : (Fin d → BitString rowLen) → BitString rowLen → BitString rowLen → PreMsg)
    (defaultSeed : Seed) (iv : IV) (keys : Fin (2 ^ d) → Seed) (stmt : Stmt) (w : Wit) :
    IsCostBounded
      (Sum.elim (fun _ => 0) (voleithLeafCost (d := d) (Seed := Seed) (IV := IV)
        (comLen := comLen) (rowLen := rowLen) (Stmt := Stmt) (PreMsg := PreMsg)))
      (prgLeafProver (Chal := Chal) expand prgLeaf encWit chalToIdx mkPreMsg defaultSeed iv keys
        stmt w) 0 := by
  unfold prgLeafProver
  have hz : IsCostBounded
      (Sum.elim (fun _ => 0) (voleithLeafCost (d := d) (Seed := Seed) (IV := IV)
        (comLen := comLen) (rowLen := rowLen) (Stmt := Stmt) (PreMsg := PreMsg)))
      (OracleComp.liftRight (spec₁ := unifSpec)
        (OracleComp.liftRight (spec₁ := VOLEITHLeafSpec d sdLen comLen Seed IV)
          (OracleComp.query
            (⟨stmt, iv, fun idx => (prgLeaf (keys idx) iv idx).com,
              encWit w + (FAEST.convertExpandedRows d
                (fun idx => expand (prgLeaf (keys idx) iv idx).seedOut)).u,
              mkPreMsg
                (FAEST.convertExpandedRows d
                  (fun idx => expand (prgLeaf (keys idx) iv idx).seedOut)).columns
                (FAEST.convertExpandedRows d
                  (fun idx => expand (prgLeaf (keys idx) iv idx).seedOut)).u
                (encWit w + (FAEST.convertExpandedRows d
                  (fun idx => expand (prgLeaf (keys idx) iv idx).seedOut)).u)⟩ :
              FSQuery d comLen rowLen Stmt IV PreMsg))) :
        ProbOracleComp (VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) Chal) 0 := by
    refine IsCostBounded.liftRight
      (IsCostBounded.liftRight_of_cost_inr_eq_zero (fun _ => rfl) _)
      (fun _ => le_rfl)
  simpa only [Nat.add_zero] using hz.bind fun _ => IsCostBounded.pure _ 0

/-- Deterministic PRG proof constructed for a challenge `delta`. -/
@[expose] def prgLeafProofOfDelta {d sdLen comLen rowLen : ℕ} {Seed IV PreMsg Chal Wit : Type}
    (expand : BitString sdLen → BitString rowLen)
    (prgLeaf : Seed → IV → Fin (2 ^ d) → LeafOutput sdLen comLen)
    (encWit : Wit → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (mkPreMsg : (Fin d → BitString rowLen) → BitString rowLen → BitString rowLen → PreMsg)
    (defaultSeed : Seed) (iv : IV) (keys : Fin (2 ^ d) → Seed) (w : Wit) (delta : Chal) :
    VOLEITHProof d comLen rowLen Seed IV PreMsg :=
  let rows := fun idx => expand (prgLeaf (keys idx) iv idx).seedOut
  let coms := fun idx => (prgLeaf (keys idx) iv idx).com
  let conv := FAEST.convertExpandedRows d rows
  let dCorr := encWit w + conv.u
  let preMsg := mkPreMsg conv.columns conv.u dCorr
  let openKeys := fun idx => if idx = chalToIdx delta then defaultSeed else keys idx
  ⟨iv, coms, dCorr, preMsg, openKeys⟩

private theorem prgLeafProver_runWith_eq_map {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen)
    (prgLeaf : Seed → IV → Fin (2 ^ d) → LeafOutput sdLen comLen)
    (encWit : Wit → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (mkPreMsg : (Fin d → BitString rowLen) → BitString rowLen → BitString rowLen → PreMsg)
    (defaultSeed : Seed) (iv : IV) (keys : Fin (2 ^ d) → Seed) (stmt : Stmt) (w : Wit) :
    ProbOracleComp.runWith
        (voleithMemoize (d := d) (sdLen := sdLen) (comLen := comLen) (rowLen := rowLen)
          (Stmt := Stmt) (Seed := Seed) (IV := IV) (PreMsg := PreMsg) (Chal := Chal))
        (prgLeafProver expand prgLeaf encWit chalToIdx mkPreMsg defaultSeed iv keys stmt w)
        ([], []) =
      (PMF.uniformOfFintype Chal).map fun delta =>
        let prf := prgLeafProofOfDelta expand prgLeaf encWit chalToIdx mkPreMsg defaultSeed iv
          keys w delta
        (prf, ([], [(prf.fsQuery stmt, delta)])) := by
  unfold prgLeafProver
  rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith,
    OracleComp.runWith_sumHandler_liftRight, OracleComp.runWith_eq_run_interpret,
    OracleComp.liftRight_query, OracleComp.run_interpret_query, voleithMemoize,
    RandomOracle.memoizeSum_inr]
  have hnil : Cslib.memoize (fun _ : FSQuery d comLen rowLen Stmt IV PreMsg =>
      PMF.uniformOfFintype Chal)
      ⟨stmt, iv, fun idx => (prgLeaf (keys idx) iv idx).com,
        encWit w + (FAEST.convertExpandedRows d
          (fun idx => expand (prgLeaf (keys idx) iv idx).seedOut)).u,
        mkPreMsg
          (FAEST.convertExpandedRows d
            (fun idx => expand (prgLeaf (keys idx) iv idx).seedOut)).columns
          (FAEST.convertExpandedRows d
            (fun idx => expand (prgLeaf (keys idx) iv idx).seedOut)).u
          (encWit w + (FAEST.convertExpandedRows d
            (fun idx => expand (prgLeaf (keys idx) iv idx).seedOut)).u)⟩ [] =
      (PMF.uniformOfFintype Chal).map fun delta => (delta,
        [(⟨stmt, iv, fun idx => (prgLeaf (keys idx) iv idx).com,
          encWit w + (FAEST.convertExpandedRows d
            (fun idx => expand (prgLeaf (keys idx) iv idx).seedOut)).u,
          mkPreMsg
            (FAEST.convertExpandedRows d
              (fun idx => expand (prgLeaf (keys idx) iv idx).seedOut)).columns
            (FAEST.convertExpandedRows d
              (fun idx => expand (prgLeaf (keys idx) iv idx).seedOut)).u
            (encWit w + (FAEST.convertExpandedRows d
              (fun idx => expand (prgLeaf (keys idx) iv idx).seedOut)).u)⟩, delta)]) := by
    simp [Cslib.memoize, PMF.map, Function.comp_def]
  rw [hnil, PMF.map_comp, PMF.bind_map]
  simp only [Function.comp_def, ProbOracleComp.runWith_pure, PMF.map]
  rfl

private theorem prgLeafVerify_runWith_of_delta {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [LawfulBEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen)
    (prgLeaf : Seed → IV → Fin (2 ^ d) → LeafOutput sdLen comLen)
    (encWit : Wit → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (mkPreMsg : (Fin d → BitString rowLen) → BitString rowLen → BitString rowLen → PreMsg)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (defaultSeed : Seed) (iv : IV) (keys : Fin (2 ^ d) → Seed) (stmt : Stmt) (w : Wit)
    (hRel : ∀ (pCols : Fin d → BitString rowLen) (u : BitString rowLen) (delta : Chal),
      checkRel stmt
        (fun j => pCols j + fun k => (BitString.equivFin d).symm (chalToIdx delta) j * u k)
        (encWit w + u) (mkPreMsg pCols u (encWit w + u)) delta = true)
    (delta : Chal) :
    let prf := prgLeafProofOfDelta expand prgLeaf encWit chalToIdx mkPreMsg defaultSeed iv keys w
      delta
    ProbOracleComp.runWith
        (voleithMemoize (d := d) (sdLen := sdLen) (comLen := comLen) (rowLen := rowLen)
          (Stmt := Stmt) (Seed := Seed) (IV := IV) (PreMsg := PreMsg) (Chal := Chal))
        (prgLeafVerify expand prgLeaf chalToIdx checkRel stmt prf)
        ([], [(prf.fsQuery stmt, delta)]) =
      PMF.pure (true, ([], [(prf.fsQuery stmt, delta)])) := by
  dsimp only
  let prf := prgLeafProofOfDelta expand prgLeaf encWit chalToIdx mkPreMsg defaultSeed iv keys w
    delta
  unfold prgLeafVerify
  rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith,
    OracleComp.runWith_sumHandler_liftRight, OracleComp.runWith_eq_run_interpret,
    OracleComp.liftRight_query, OracleComp.run_interpret_query, voleithMemoize,
    RandomOracle.memoizeSum_inr]
  have hfs : Cslib.memoize
      (fun _ : FSQuery d comLen rowLen Stmt IV PreMsg => PMF.uniformOfFintype Chal)
      (prf.fsQuery stmt) [(prf.fsQuery stmt, delta)] =
      PMF.pure (delta, [(prf.fsQuery stmt, delta)]) := by
    simp [Cslib.memoize]
  rw [hfs]
  simp only [PMF.map, PMF.pure_bind, Function.comp_def]
  have hopen : ∀ vIdx : Fin (2 ^ d), vIdx = 0 ∨
      (prgLeaf (prf.openKeys (FAEST.xorIndex vIdx (chalToIdx delta))) prf.iv
        (FAEST.xorIndex vIdx (chalToIdx delta))).com =
        prf.coms (FAEST.xorIndex vIdx (chalToIdx delta)) := by
    intro vIdx
    by_cases hv : vIdx = 0
    · exact Or.inl hv
    · right
      have hne := xorIndex_ne_right (hidden := chalToIdx delta) hv
      simp [prf, prgLeafProofOfDelta, hne]
  have hrows : prgLeafOpenRows expand prgLeaf prf.iv prf.openKeys prf.coms (chalToIdx delta) =
      some (FAEST.verifierRows (fun idx => expand (prgLeaf (keys idx) iv idx).seedOut)
        (chalToIdx delta)) := by
    unfold prgLeafOpenRows
    simp only [hopen, forall_const, ite_true]
    congr 1
    funext vIdx
    by_cases hv : vIdx = 0
    · subst hv
      simp [FAEST.verifierRows]
    · have hne := xorIndex_ne_right (hidden := chalToIdx delta) hv
      simp [FAEST.verifierRows, hv, prf, prgLeafProofOfDelta, hne]
  rw [hrows]
  dsimp only
  simp only [ProbOracleComp.runWith_pure]
  have hcols : (FAEST.convertExpandedRows d
      (FAEST.verifierRows (fun idx => expand (prgLeaf (keys idx) iv idx).seedOut)
        (chalToIdx delta))).columns =
      fun j => (FAEST.convertExpandedRows d
          (fun idx => expand (prgLeaf (keys idx) iv idx).seedOut)).columns j +
        fun k => (BitString.equivFin d).symm (chalToIdx delta) j *
          (FAEST.convertExpandedRows d
            (fun idx => expand (prgLeaf (keys idx) iv idx).seedOut)).u k := by
    funext j
    exact FAEST.convertExpandedRows_correlation _ (chalToIdx delta) j
  rw [hcols]
  exact congrArg PMF.pure (Prod.ext (hRel _ _ delta) rfl)

/-- Every supported run of `prgLeafGame` against `voleithMemoize` records an empty `H_leaf`
trace `tr₁ = []`. -/
theorem prgLeafGame_leafTrace_eq_nil {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [LawfulBEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen)
    (prgLeaf : Seed → IV → Fin (2 ^ d) → LeafOutput sdLen comLen)
    (encWit : Wit → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (mkPreMsg : (Fin d → BitString rowLen) → BitString rowLen → BitString rowLen → PreMsg)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (defaultSeed : Seed) (iv : IV) (keys : Fin (2 ^ d) → Seed) (stmt : Stmt) (w : Wit)
    (hRel : ∀ (pCols : Fin d → BitString rowLen) (u : BitString rowLen) (delta : Chal),
      checkRel stmt
        (fun j => pCols j + fun k => (BitString.equivFin d).symm (chalToIdx delta) j * u k)
        (encWit w + u) (mkPreMsg pCols u (encWit w + u)) delta = true)
    {b : Bool} {st : VOLEITHTraceState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal}
    (hmem : (b, st) ∈ (ProbOracleComp.runWith
      (voleithMemoize (d := d) (sdLen := sdLen) (comLen := comLen) (rowLen := rowLen)
        (Stmt := Stmt) (Seed := Seed) (IV := IV) (PreMsg := PreMsg) (Chal := Chal))
      (prgLeafGame expand prgLeaf encWit chalToIdx mkPreMsg checkRel defaultSeed iv keys stmt w)
      ([], [])).support) :
    st.1 = [] := by
  unfold prgLeafGame at hmem
  rw [ProbOracleComp.runWith_bind, prgLeafProver_runWith_eq_map,
    PMF.bind_map, PMF.mem_support_bind_iff] at hmem
  obtain ⟨delta, -, hmem_v⟩ := hmem
  dsimp only [Function.comp_apply] at hmem_v
  rw [prgLeafVerify_runWith_of_delta expand prgLeaf encWit chalToIdx mkPreMsg checkRel
    defaultSeed iv keys stmt w hRel delta, PMF.mem_support_pure_iff] at hmem_v
  cases hmem_v
  rfl

private theorem prgLeafProver_then_verify_map {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit γ : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [LawfulBEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen)
    (prgLeaf : Seed → IV → Fin (2 ^ d) → LeafOutput sdLen comLen)
    (encWit : Wit → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (mkPreMsg : (Fin d → BitString rowLen) → BitString rowLen → BitString rowLen → PreMsg)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (defaultSeed : Seed) (iv : IV) (keys : Fin (2 ^ d) → Seed) (stmt : Stmt) (w : Wit)
    (hRel : ∀ (pCols : Fin d → BitString rowLen) (u : BitString rowLen) (delta : Chal),
      checkRel stmt
        (fun j => pCols j + fun k => (BitString.equivFin d).symm (chalToIdx delta) j * u k)
        (encWit w + u) (mkPreMsg pCols u (encWit w + u)) delta = true)
    (f : Bool → VOLEITHProof d comLen rowLen Seed IV PreMsg →
      LeafTrace d sdLen comLen Seed IV → γ) :
    ((ProbOracleComp.runWith
      (voleithMemoize (d := d) (sdLen := sdLen) (comLen := comLen) (rowLen := rowLen)
        (Stmt := Stmt) (Seed := Seed) (IV := IV) (PreMsg := PreMsg) (Chal := Chal))
      (do
        let prf ← prgLeafProver expand prgLeaf encWit chalToIdx mkPreMsg defaultSeed iv keys stmt w
        let ok ← prgLeafVerify expand prgLeaf chalToIdx checkRel stmt prf
        return (ok, prf)) ([], [])).map fun ((ok, prf), st) => f ok prf st.1) =
      (PMF.uniformOfFintype Chal).map fun delta =>
        f true (prgLeafProofOfDelta expand prgLeaf encWit chalToIdx mkPreMsg defaultSeed iv keys
          w delta) [] := by
  rw [ProbOracleComp.runWith_bind, prgLeafProver_runWith_eq_map,
    PMF.bind_map, PMF.map_bind]
  congr 1 with delta : 1
  dsimp only [Function.comp_apply]
  rw [ProbOracleComp.runWith_bind, prgLeafVerify_runWith_of_delta expand prgLeaf encWit
    chalToIdx mkPreMsg checkRel defaultSeed iv keys stmt w hRel delta,
    PMF.pure_bind, ProbOracleComp.runWith_pure]
  simp only [PMF.map, PMF.pure_bind, Function.comp_def]

/-- Honest `leaf_hash::aes_ctr`-style PRG commitments pass `prgLeafVerify` with probability `1`
without touching `H_leaf`. -/
theorem prgLeafGame_eq_pure_true {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [LawfulBEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen)
    (prgLeaf : Seed → IV → Fin (2 ^ d) → LeafOutput sdLen comLen)
    (encWit : Wit → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (mkPreMsg : (Fin d → BitString rowLen) → BitString rowLen → BitString rowLen → PreMsg)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (defaultSeed : Seed) (iv : IV) (keys : Fin (2 ^ d) → Seed) (stmt : Stmt) (w : Wit)
    (hRel : ∀ (pCols : Fin d → BitString rowLen) (u : BitString rowLen) (delta : Chal),
      checkRel stmt
        (fun j => pCols j + fun k => (BitString.equivFin d).symm (chalToIdx delta) j * u k)
        (encWit w + u) (mkPreMsg pCols u (encWit w + u)) delta = true) :
    ((ProbOracleComp.runWith
      (voleithMemoize (d := d) (sdLen := sdLen) (comLen := comLen) (rowLen := rowLen)
        (Stmt := Stmt) (Seed := Seed) (IV := IV) (PreMsg := PreMsg) (Chal := Chal))
      (prgLeafGame expand prgLeaf encWit chalToIdx mkPreMsg checkRel defaultSeed iv keys stmt w)
      ([], [])).map Prod.fst) = PMF.pure true := by
  have h := prgLeafProver_then_verify_map expand prgLeaf encWit chalToIdx mkPreMsg checkRel
    defaultSeed iv keys stmt w hRel (fun ok _ _ => ok)
  have hgame :
      (ProbOracleComp.runWith
        (voleithMemoize (d := d) (sdLen := sdLen) (comLen := comLen) (rowLen := rowLen)
          (Stmt := Stmt) (Seed := Seed) (IV := IV) (PreMsg := PreMsg) (Chal := Chal))
        (prgLeafGame expand prgLeaf encWit chalToIdx mkPreMsg checkRel defaultSeed iv keys stmt w)
        ([], [])).map Prod.fst =
      (ProbOracleComp.runWith
        (voleithMemoize (d := d) (sdLen := sdLen) (comLen := comLen) (rowLen := rowLen)
          (Stmt := Stmt) (Seed := Seed) (IV := IV) (PreMsg := PreMsg) (Chal := Chal))
        (do
          let prf ← prgLeafProver expand prgLeaf encWit chalToIdx mkPreMsg defaultSeed iv keys
            stmt w
          let ok ← prgLeafVerify expand prgLeaf chalToIdx checkRel stmt prf
          return (ok, prf)) ([], [])).map fun ((ok, _), _) => ok := by
    rw [prgLeafGame]
    simp only [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_pure, PMF.map_bind]
    congr 1
    funext ⟨prf, st⟩
    simp [PMF.map, PMF.pure_bind, Function.comp_def]
  rw [hgame, h, show (fun _ : Chal => true) = Function.const Chal true from rfl, PMF.map_const]

private theorem convertExpandedRows_zero_u {rowLen : ℕ} :
    ∀ d : ℕ, (FAEST.convertExpandedRows d (fun _ : Fin (2 ^ d) => (0 : BitString rowLen))).u = 0
  | 0 => rfl
  | d + 1 => by
    have hp : FAEST.pairRows (fun _ : Fin (2 ^ (d + 1)) => (0 : BitString rowLen)) =
        fun _ => 0 := by
      funext i
      simp [FAEST.pairRows]
    simpa [FAEST.convertExpandedRows, hp] using convertExpandedRows_zero_u d

/-- Applying `extractWitnessFromTrace` to an empty `H_leaf` query log recovers only
`decWit prf.dCorr` (blind to any hidden leaf seed). -/
theorem extractWitnessFromTrace_nil {d sdLen comLen rowLen : ℕ} {Seed IV PreMsg Wit : Type}
    [DecidableEq IV]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (prf : VOLEITHProof d comLen rowLen Seed IV PreMsg) :
    extractWitnessFromTrace (d := d) (sdLen := sdLen) expand decWit ([] : LeafTrace d sdLen
      comLen Seed IV) prf = decWit prf.dCorr := by
  have hrows :
      extractRowsFromTrace (d := d) expand ([] : LeafTrace d sdLen comLen Seed IV) prf.iv prf.coms =
        0 := by
    funext idx
    simp [extractRowsFromTrace, extractLeafFromTrace]
  simp only [extractWitnessFromTrace, extractVOLEFromTrace, hrows]
  change decWit (prf.dCorr + (FAEST.convertExpandedRows d (fun _ => 0)).u) = decWit prf.dCorr
  rw [convertExpandedRows_zero_u d, add_zero]

private theorem toOuterMeasure_prgLeaf_queryLog_fails_of_nil_not_rel {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [LawfulBEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen)
    (prgLeaf : Seed → IV → Fin (2 ^ d) → LeafOutput sdLen comLen)
    (encWit : Wit → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (mkPreMsg : (Fin d → BitString rowLen) → BitString rowLen → BitString rowLen → PreMsg)
    (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (defaultSeed : Seed) (iv : IV) (keys : Fin (2 ^ d) → Seed) (stmt : Stmt) (w : Wit)
    (hRel : ∀ (pCols : Fin d → BitString rowLen) (u : BitString rowLen) (delta : Chal),
      checkRel stmt
        (fun j => pCols j + fun k => (BitString.equivFin d).symm (chalToIdx delta) j * u k)
        (encWit w + u) (mkPreMsg pCols u (encWit w + u)) delta = true)
    (extLog : LeafTrace d sdLen comLen Seed IV → Option Wit)
    (hbad : (extLog []).elim false (Rel stmt) = false) :
    ((ProbOracleComp.runWith
      (voleithMemoize (d := d) (sdLen := sdLen) (comLen := comLen) (rowLen := rowLen)
        (Stmt := Stmt) (Seed := Seed) (IV := IV) (PreMsg := PreMsg) (Chal := Chal))
      (prgLeafGame expand prgLeaf encWit chalToIdx mkPreMsg checkRel defaultSeed iv keys stmt w)
      ([], [])).map fun (b, st) =>
        decide (b = true ∧ (extLog st.1).elim false (Rel stmt) = false)).toOuterMeasure
        {true} = 1 := by
  have hpure : ((ProbOracleComp.runWith
      (voleithMemoize (d := d) (sdLen := sdLen) (comLen := comLen) (rowLen := rowLen)
        (Stmt := Stmt) (Seed := Seed) (IV := IV) (PreMsg := PreMsg) (Chal := Chal))
      (prgLeafGame expand prgLeaf encWit chalToIdx mkPreMsg checkRel defaultSeed iv keys stmt w)
      ([], [])).map fun (b, st) =>
        decide (b = true ∧ (extLog st.1).elim false (Rel stmt) = false)) = PMF.pure true := by
    refine PMF.map_eq_pure_iff.mpr ?_
    rintro ⟨b, st⟩ hsupp
    have htr : st.1 = [] := prgLeafGame_leafTrace_eq_nil expand prgLeaf encWit chalToIdx mkPreMsg
      checkRel defaultSeed iv keys stmt w hRel hsupp
    have hb_supp : b ∈ ((ProbOracleComp.runWith voleithMemoize
        (prgLeafGame expand prgLeaf encWit chalToIdx mkPreMsg checkRel defaultSeed iv keys stmt w)
        ([], [])).map Prod.fst).support := by
      rw [PMF.mem_support_map_iff]
      exact ⟨(b, st), hsupp, rfl⟩
    rw [prgLeafGame_eq_pure_true expand prgLeaf encWit chalToIdx mkPreMsg checkRel defaultSeed iv
      keys stmt w hRel, PMF.support_pure, Set.mem_singleton_iff] at hb_supp
    dsimp only
    rw [htr, hb_supp]
    exact decide_eq_true ⟨rfl, hbad⟩
  rw [hpure]
  simp

/-- **Disjoint-statement query-log separation for `leaf_hash::aes_ctr`**: given two statements
`stmt₀, stmt₁` with disjoint `Rel`-witness sets and valid witnesses `(w₀, w₁)`, **every**
leaf-query-log extractor `extLog : LeafTrace → Option Wit`—which sees neither the statement nor the
proof, and thus excludes the `(tr, prf)` extractor shape of `extractWitnessFromTrace` covered by
`exists_valid_prgLeaf_proofOnly_extract_fails_ge`—fails `Rel` with probability `1` on at least one
valid statement-witness pair `(stmt, w)`. -/
theorem exists_valid_prgLeaf_queryLog_fails_Rel_eq_one {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [LawfulBEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen)
    (prgLeaf : Seed → IV → Fin (2 ^ d) → LeafOutput sdLen comLen)
    (encWit : Wit → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (mkPreMsg : (Fin d → BitString rowLen) → BitString rowLen → BitString rowLen → PreMsg)
    (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (defaultSeed : Seed) (iv : IV) (keys : Fin (2 ^ d) → Seed)
    (stmt₀ stmt₁ : Stmt) (w₀ w₁ : Wit)
    (hValid₀ : Rel stmt₀ w₀ = true) (hValid₁ : Rel stmt₁ w₁ = true)
    (hDisj : ∀ w', ¬ (Rel stmt₀ w' = true ∧ Rel stmt₁ w' = true))
    (hRel₀ : ∀ (pCols : Fin d → BitString rowLen) (u : BitString rowLen) (delta : Chal),
      checkRel stmt₀
        (fun j => pCols j + fun k => (BitString.equivFin d).symm (chalToIdx delta) j * u k)
        (encWit w₀ + u) (mkPreMsg pCols u (encWit w₀ + u)) delta = true)
    (hRel₁ : ∀ (pCols : Fin d → BitString rowLen) (u : BitString rowLen) (delta : Chal),
      checkRel stmt₁
        (fun j => pCols j + fun k => (BitString.equivFin d).symm (chalToIdx delta) j * u k)
        (encWit w₁ + u) (mkPreMsg pCols u (encWit w₁ + u)) delta = true)
    (extLog : LeafTrace d sdLen comLen Seed IV → Option Wit) :
    ∃ stmt w, Rel stmt w = true ∧
      ((ProbOracleComp.runWith
        (voleithMemoize (d := d) (sdLen := sdLen) (comLen := comLen) (rowLen := rowLen)
          (Stmt := Stmt) (Seed := Seed) (IV := IV) (PreMsg := PreMsg) (Chal := Chal))
        (prgLeafGame expand prgLeaf encWit chalToIdx mkPreMsg checkRel defaultSeed iv keys stmt w)
        ([], [])).map fun (b, st) =>
          decide (b = true ∧ (extLog st.1).elim false (Rel stmt) = false)).toOuterMeasure
          {true} = 1 := by
  by_cases h0 : (extLog []).elim false (Rel stmt₀) = true
  · refine ⟨stmt₁, w₁, hValid₁, toOuterMeasure_prgLeaf_queryLog_fails_of_nil_not_rel expand
      prgLeaf encWit chalToIdx mkPreMsg Rel checkRel defaultSeed iv keys stmt₁ w₁ hRel₁ extLog ?_⟩
    cases hext : extLog [] with
    | none => simp [hext] at h0
    | some w' =>
      simp only [hext, Option.elim_some] at h0 ⊢
      exact Bool.eq_false_iff.mpr fun h1 => hDisj w' ⟨h0, h1⟩
  · exact ⟨stmt₀, w₀, hValid₀, toOuterMeasure_prgLeaf_queryLog_fails_of_nil_not_rel expand prgLeaf
      encWit chalToIdx mkPreMsg Rel checkRel defaultSeed iv keys stmt₀ w₀ hRel₀ extLog
      (Bool.eq_false_iff.mpr h0)⟩

/-- Helper showing when two colliding PRG executions emit the exact same `VOLEITHProof` at a
fixed challenge `delta*`. -/
theorem prgLeafProofOfDelta_eq_of {d sdLen comLen rowLen : ℕ} {Seed IV PreMsg Chal Wit : Type}
    (expand : BitString sdLen → BitString rowLen)
    (prgLeaf : Seed → IV → Fin (2 ^ d) → LeafOutput sdLen comLen)
    (encWit : Wit → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (mkPreMsg : (Fin d → BitString rowLen) → BitString rowLen → BitString rowLen → PreMsg)
    (defaultSeed : Seed) (iv : IV) (keys₀ keys₁ : Fin (2 ^ d) → Seed)
    (w₀ w₁ : Wit) (delta : Chal)
    (hcom : ∀ idx, (prgLeaf (keys₀ idx) iv idx).com = (prgLeaf (keys₁ idx) iv idx).com)
    (hdCorr : encWit w₀ +
        (FAEST.convertExpandedRows d (fun idx => expand (prgLeaf (keys₀ idx) iv idx).seedOut)).u =
      encWit w₁ +
        (FAEST.convertExpandedRows d (fun idx => expand (prgLeaf (keys₁ idx) iv idx).seedOut)).u)
    (hpre :
      mkPreMsg
        (FAEST.convertExpandedRows d
          (fun idx => expand (prgLeaf (keys₀ idx) iv idx).seedOut)).columns
        (FAEST.convertExpandedRows d (fun idx => expand (prgLeaf (keys₀ idx) iv idx).seedOut)).u
        (encWit w₀ + (FAEST.convertExpandedRows d
          (fun idx => expand (prgLeaf (keys₀ idx) iv idx).seedOut)).u) =
      mkPreMsg
        (FAEST.convertExpandedRows d
          (fun idx => expand (prgLeaf (keys₁ idx) iv idx).seedOut)).columns
        (FAEST.convertExpandedRows d (fun idx => expand (prgLeaf (keys₁ idx) iv idx).seedOut)).u
        (encWit w₁ + (FAEST.convertExpandedRows d
          (fun idx => expand (prgLeaf (keys₁ idx) iv idx).seedOut)).u))
    (hopen : ∀ idx, idx ≠ chalToIdx delta → keys₀ idx = keys₁ idx) :
    prgLeafProofOfDelta expand prgLeaf encWit chalToIdx mkPreMsg defaultSeed iv keys₀ w₀
      delta =
    prgLeafProofOfDelta expand prgLeaf encWit chalToIdx mkPreMsg defaultSeed iv keys₁ w₁
      delta := by
  simp only [prgLeafProofOfDelta]
  have hcoms : (fun idx => (prgLeaf (keys₀ idx) iv idx).com) =
      (fun idx => (prgLeaf (keys₁ idx) iv idx).com) := funext hcom
  have hkeys : (fun idx => if idx = chalToIdx delta then defaultSeed else keys₀ idx) =
      (fun idx => if idx = chalToIdx delta then defaultSeed else keys₁ idx) := by
    funext idx
    by_cases heq : idx = chalToIdx delta
    · simp [heq]
    · simp [heq, hopen idx heq]
  rw [hcoms, hpre, hdCorr, hkeys]

private theorem prgLeaf_preimage_extractor_fails_of_not_rel {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [LawfulBEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen)
    (prgLeaf : Seed → IV → Fin (2 ^ d) → LeafOutput sdLen comLen)
    (encWit : Wit → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d))
    (mkPreMsg : (Fin d → BitString rowLen) → BitString rowLen → BitString rowLen → PreMsg)
    (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (extPre : (Fin (2 ^ d) → BitString comLen) → IV → Fin (2 ^ d) → Seed)
    (defaultSeed : Seed) (iv : IV) (keys : Fin (2 ^ d) → Seed) (stmt : Stmt) (w : Wit)
    (hValid : Rel stmt w = true)
    (hRel : ∀ (pCols : Fin d → BitString rowLen) (u : BitString rowLen) (delta : Chal),
      checkRel stmt
        (fun j => pCols j + fun k => (BitString.equivFin d).symm (chalToIdx delta) j * u k)
        (encWit w + u) (mkPreMsg pCols u (encWit w + u)) delta = true)
    (hExtFail :
      Rel stmt (decWit
        ((encWit w +
          (FAEST.convertExpandedRows d
            (fun idx => expand (prgLeaf (keys idx) iv idx).seedOut)).u) +
        (FAEST.convertExpandedRows d
          (fun idx => expand (prgLeaf
            (extPre (fun j => (prgLeaf (keys j) iv j).com) iv idx) iv idx).seedOut)).u)) =
        false) :
    Rel stmt w = true ∧
      ((ProbOracleComp.runWith
        (voleithMemoize (d := d) (sdLen := sdLen) (comLen := comLen) (rowLen := rowLen)
          (Stmt := Stmt) (Seed := Seed) (IV := IV) (PreMsg := PreMsg) (Chal := Chal))
        (do
          let prf ← prgLeafProver expand prgLeaf encWit chalToIdx mkPreMsg defaultSeed iv keys
            stmt w
          let ok ← prgLeafVerify expand prgLeaf chalToIdx checkRel stmt prf
          return (ok, prf)) ([], [])).map fun ((ok, prf), _) =>
            let wExt := decWit (prf.dCorr +
              (FAEST.convertExpandedRows d
                (fun idx => expand (prgLeaf (extPre prf.coms prf.iv idx) prf.iv idx).seedOut)).u)
            decide (ok = true ∧ Rel stmt wExt = false)).toOuterMeasure {true} = 1 := by
  refine ⟨hValid, ?_⟩
  have hrun := prgLeafProver_then_verify_map expand prgLeaf encWit chalToIdx mkPreMsg checkRel
    defaultSeed iv keys stmt w hRel (fun ok prf _ =>
      let wExt := decWit (prf.dCorr +
        (FAEST.convertExpandedRows d
          (fun idx => expand (prgLeaf (extPre prf.coms prf.iv idx) prf.iv idx).seedOut)).u)
      decide (ok = true ∧ Rel stmt wExt = false))
  have hconst :
      ((PMF.uniformOfFintype Chal).map fun delta =>
        let prf := prgLeafProofOfDelta expand prgLeaf encWit chalToIdx mkPreMsg defaultSeed iv
          keys w delta
        let wExt := decWit (prf.dCorr +
          (FAEST.convertExpandedRows d
            (fun idx => expand (prgLeaf (extPre prf.coms prf.iv idx) prf.iv idx).seedOut)).u)
        decide (true = true ∧ Rel stmt wExt = false)) = PMF.pure true := by
    have hfun : (fun _ : Chal => true) = fun delta : Chal =>
        let prf := prgLeafProofOfDelta expand prgLeaf encWit chalToIdx mkPreMsg defaultSeed iv
          keys w delta
        let wExt := decWit (prf.dCorr +
          (FAEST.convertExpandedRows d
            (fun idx => expand (prgLeaf (extPre prf.coms prf.iv idx) prf.iv idx).seedOut)).u)
        decide (true = true ∧ Rel stmt wExt = false) := by
      funext delta
      exact (decide_eq_true ⟨rfl, hExtFail⟩).symm
    rw [← hfun, show (fun _ : Chal => true) = Function.const Chal true from rfl, PMF.map_const]
  rw [hrun, hconst]
  simp

/-- **Pre-challenge preimage-table failure under colliding PRG commitments** (modeling FAESTer
[BaumEtAl2026FAESTer], Definition 27, pp. 17–18, and Lemma 32, pp. 25–26): given two valid
executions `(stmt₀, w₀, keys₀)` and `(stmt₁, w₁, keys₁)` with disjoint `Rel`-witness sets
(`hDisj`), identical PRG commitments (`hComEq`), differing expanded `u` masks (`hUNe`, forcing
`keys₀ ≠ keys₁` and unsatisfiable for any injective `prgLeaf`), and colliding corrected masks
`d_corr` (`hdCorrEq`), **every** deterministic preimage-table seed extractor
`extPre : coms → iv → idx → Seed` fails `Rel` with probability `1` on at least one of the two
colliding executions. This holds at arbitrary depth `d ≥ 1`. -/
theorem prgLeaf_preimage_extractor_fails {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [LawfulBEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen)
    (prgLeaf : Seed → IV → Fin (2 ^ d) → LeafOutput sdLen comLen)
    (encWit : Wit → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d))
    (mkPreMsg : (Fin d → BitString rowLen) → BitString rowLen → BitString rowLen → PreMsg)
    (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (defaultSeed : Seed) (iv : IV) (keys₀ keys₁ : Fin (2 ^ d) → Seed)
    (stmt₀ stmt₁ : Stmt) (w₀ w₁ : Wit)
    (hValid₀ : Rel stmt₀ w₀ = true) (hValid₁ : Rel stmt₁ w₁ = true)
    (hDisj : ∀ w', ¬ (Rel stmt₀ w' = true ∧ Rel stmt₁ w' = true))
    (hRel₀ : ∀ (pCols : Fin d → BitString rowLen) (u : BitString rowLen) (delta : Chal),
      checkRel stmt₀
        (fun j => pCols j + fun k => (BitString.equivFin d).symm (chalToIdx delta) j * u k)
        (encWit w₀ + u) (mkPreMsg pCols u (encWit w₀ + u)) delta = true)
    (hRel₁ : ∀ (pCols : Fin d → BitString rowLen) (u : BitString rowLen) (delta : Chal),
      checkRel stmt₁
        (fun j => pCols j + fun k => (BitString.equivFin d).symm (chalToIdx delta) j * u k)
        (encWit w₁ + u) (mkPreMsg pCols u (encWit w₁ + u)) delta = true)
    (hComEq : ∀ idx, (prgLeaf (keys₀ idx) iv idx).com = (prgLeaf (keys₁ idx) iv idx).com)
    (hUNe :
      (FAEST.convertExpandedRows d
        (fun idx => expand (prgLeaf (keys₀ idx) iv idx).seedOut)).u ≠
      (FAEST.convertExpandedRows d
        (fun idx => expand (prgLeaf (keys₁ idx) iv idx).seedOut)).u)
    (hdCorrEq :
      encWit w₀ +
        (FAEST.convertExpandedRows d
          (fun idx => expand (prgLeaf (keys₀ idx) iv idx).seedOut)).u =
      encWit w₁ +
        (FAEST.convertExpandedRows d
          (fun idx => expand (prgLeaf (keys₁ idx) iv idx).seedOut)).u) :
    keys₀ ≠ keys₁ ∧
      ∀ extPre : (Fin (2 ^ d) → BitString comLen) → IV → Fin (2 ^ d) → Seed,
        ∃ stmt w keys, Rel stmt w = true ∧
          ((ProbOracleComp.runWith
            (voleithMemoize (d := d) (sdLen := sdLen) (comLen := comLen) (rowLen := rowLen)
              (Stmt := Stmt) (Seed := Seed) (IV := IV) (PreMsg := PreMsg) (Chal := Chal))
            (do
              let prf ← prgLeafProver expand prgLeaf encWit chalToIdx mkPreMsg defaultSeed iv keys
                stmt w
              let ok ← prgLeafVerify expand prgLeaf chalToIdx checkRel stmt prf
              return (ok, prf)) ([], [])).map fun ((ok, prf), _) =>
                let wExt := decWit (prf.dCorr +
                  (FAEST.convertExpandedRows d
                    (fun idx => expand
                      (prgLeaf (extPre prf.coms prf.iv idx) prf.iv idx).seedOut)).u)
                decide (ok = true ∧ Rel stmt wExt = false)).toOuterMeasure {true} = 1 := by
  refine ⟨fun h => hUNe (by rw [h]), fun extPre => ?_⟩
  let coms₀ : Fin (2 ^ d) → BitString comLen := fun j => (prgLeaf (keys₀ j) iv j).com
  let coms₁ : Fin (2 ^ d) → BitString comLen := fun j => (prgLeaf (keys₁ j) iv j).com
  have hcoms : coms₀ = coms₁ := funext hComEq
  let wExt := decWit ((encWit w₀ +
    (FAEST.convertExpandedRows d (fun idx => expand (prgLeaf (keys₀ idx) iv idx).seedOut)).u) +
    (FAEST.convertExpandedRows d
      (fun idx => expand (prgLeaf (extPre coms₀ iv idx) iv idx).seedOut)).u)
  by_cases h0 : Rel stmt₀ wExt = true
  · refine ⟨stmt₁, w₁, keys₁, prgLeaf_preimage_extractor_fails_of_not_rel expand prgLeaf encWit
      decWit chalToIdx mkPreMsg Rel checkRel extPre defaultSeed iv keys₁ stmt₁ w₁ hValid₁ hRel₁
      ?_⟩
    have h1_false : Rel stmt₁ wExt = false := Bool.eq_false_iff.mpr fun h1 => hDisj wExt ⟨h0, h1⟩
    change Rel stmt₁ (decWit ((encWit w₁ +
      (FAEST.convertExpandedRows d (fun idx => expand (prgLeaf (keys₁ idx) iv idx).seedOut)).u) +
      (FAEST.convertExpandedRows d
        (fun idx => expand (prgLeaf (extPre coms₁ iv idx) iv idx).seedOut)).u)) = false
    rw [← hdCorrEq, ← hcoms]
    exact h1_false
  · exact ⟨stmt₀, w₀, keys₀, prgLeaf_preimage_extractor_fails_of_not_rel expand prgLeaf encWit
      decWit chalToIdx mkPreMsg Rel checkRel extPre defaultSeed iv keys₀ stmt₀ w₀ hValid₀ hRel₀
      (Bool.eq_false_iff.mpr h0)⟩

/-- **Proof-only extraction separation at `d ≥ 1` under colliding PRG commitments**:
if two valid pairs `(stmt₀, w₀, keys₀)` and `(stmt₁, w₁, keys₁)` have disjoint `Rel`-witness
sets (`hDisj`) and emit the same `VOLEITHProof` at some challenge `delta* : Chal` (`hPrfEq`), then
any unbounded proof-only extractor `ext : LeafTrace → VOLEITHProof → Option Wit` (which omits
`stmt`) fails `Rel` with probability at least `1 / Fintype.card Chal` on at least one valid pair.
(Unlike `prgLeaf_preimage_extractor_fails`, a sound extractor *with* `stmt` can switch on `stmt`;
omitting `stmt` leaves a colliding challenge indistinguishable.) -/
theorem exists_valid_prgLeaf_proofOnly_extract_fails_ge {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [LawfulBEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen)
    (prgLeaf : Seed → IV → Fin (2 ^ d) → LeafOutput sdLen comLen)
    (encWit : Wit → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (mkPreMsg : (Fin d → BitString rowLen) → BitString rowLen → BitString rowLen → PreMsg)
    (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (defaultSeed : Seed) (iv : IV) (keys₀ keys₁ : Fin (2 ^ d) → Seed)
    (stmt₀ stmt₁ : Stmt) (w₀ w₁ : Wit)
    (hValid₀ : Rel stmt₀ w₀ = true) (hValid₁ : Rel stmt₁ w₁ = true)
    (hDisj : ∀ w', ¬ (Rel stmt₀ w' = true ∧ Rel stmt₁ w' = true))
    (hRel₀ : ∀ (pCols : Fin d → BitString rowLen) (u : BitString rowLen) (delta : Chal),
      checkRel stmt₀
        (fun j => pCols j + fun k => (BitString.equivFin d).symm (chalToIdx delta) j * u k)
        (encWit w₀ + u) (mkPreMsg pCols u (encWit w₀ + u)) delta = true)
    (hRel₁ : ∀ (pCols : Fin d → BitString rowLen) (u : BitString rowLen) (delta : Chal),
      checkRel stmt₁
        (fun j => pCols j + fun k => (BitString.equivFin d).symm (chalToIdx delta) j * u k)
        (encWit w₁ + u) (mkPreMsg pCols u (encWit w₁ + u)) delta = true)
    (deltaStar : Chal)
    (hPrfEq :
      prgLeafProofOfDelta expand prgLeaf encWit chalToIdx mkPreMsg defaultSeed iv keys₀ w₀
        deltaStar =
      prgLeafProofOfDelta expand prgLeaf encWit chalToIdx mkPreMsg defaultSeed iv keys₁ w₁
        deltaStar)
    (ext : LeafTrace d sdLen comLen Seed IV → VOLEITHProof d comLen rowLen Seed IV PreMsg →
      Option Wit) :
    ∃ stmt w keys, Rel stmt w = true ∧
      ((Fintype.card Chal : ℝ≥0∞)⁻¹ ≤
        ((ProbOracleComp.runWith
          (voleithMemoize (d := d) (sdLen := sdLen) (comLen := comLen) (rowLen := rowLen)
            (Stmt := Stmt) (Seed := Seed) (IV := IV) (PreMsg := PreMsg) (Chal := Chal))
          (do
            let prf ← prgLeafProver expand prgLeaf encWit chalToIdx mkPreMsg defaultSeed iv keys
              stmt w
            let ok ← prgLeafVerify expand prgLeaf chalToIdx checkRel stmt prf
            return (ok, prf)) ([], [])).map fun ((ok, prf), st) =>
              decide (ok = true ∧ (ext st.1 prf).elim false (Rel stmt) = false)).toOuterMeasure
            {true}) := by
  let prfStar := prgLeafProofOfDelta expand prgLeaf encWit chalToIdx mkPreMsg defaultSeed iv
    keys₀ w₀ deltaStar
  have hge : ∀ stmt w keys
      (hRel : ∀ (pCols : Fin d → BitString rowLen) (u : BitString rowLen) (delta : Chal),
        checkRel stmt
          (fun j => pCols j + fun k => (BitString.equivFin d).symm (chalToIdx delta) j * u k)
          (encWit w + u) (mkPreMsg pCols u (encWit w + u)) delta = true)
      (hp : prgLeafProofOfDelta expand prgLeaf encWit chalToIdx mkPreMsg defaultSeed iv keys w
        deltaStar = prfStar)
      (he : (ext [] prfStar).elim false (Rel stmt) = false),
      (Fintype.card Chal : ℝ≥0∞)⁻¹ ≤
        ((ProbOracleComp.runWith
          (voleithMemoize (d := d) (sdLen := sdLen) (comLen := comLen) (rowLen := rowLen)
            (Stmt := Stmt) (Seed := Seed) (IV := IV) (PreMsg := PreMsg) (Chal := Chal))
          (do
            let prf ← prgLeafProver expand prgLeaf encWit chalToIdx mkPreMsg defaultSeed iv keys
              stmt w
            let ok ← prgLeafVerify expand prgLeaf chalToIdx checkRel stmt prf
            return (ok, prf)) ([], [])).map fun ((ok, prf), st) =>
              decide (ok = true ∧ (ext st.1 prf).elim false (Rel stmt) = false)).toOuterMeasure
            {true} := by
    intro stmt w keys hRel hp he
    rw [prgLeafProver_then_verify_map expand prgLeaf encWit chalToIdx mkPreMsg checkRel
      defaultSeed iv keys stmt w hRel (f := fun ok prf tr =>
        decide (ok = true ∧ (ext tr prf).elim false (Rel stmt) = false))]
    rw [PMF.toOuterMeasure_map_apply]
    calc
      (Fintype.card Chal : ℝ≥0∞)⁻¹
        = (PMF.uniformOfFintype Chal) deltaStar := (PMF.uniformOfFintype_apply deltaStar).symm
      _ = (PMF.uniformOfFintype Chal).toOuterMeasure {deltaStar} := by
          rw [PMF.toOuterMeasure_apply_singleton]
      _ ≤ (PMF.uniformOfFintype Chal).toOuterMeasure
            ((fun delta => decide (true = true ∧
              (ext [] (prgLeafProofOfDelta expand prgLeaf encWit chalToIdx mkPreMsg defaultSeed iv
                keys w delta)).elim false (Rel stmt) = false)) ⁻¹' {true}) := by
          refine (PMF.uniformOfFintype Chal).toOuterMeasure.mono ?_
          intro delta hdelta
          rw [Set.mem_singleton_iff] at hdelta
          subst hdelta
          simp only [Set.mem_preimage, Set.mem_singleton_iff, hp, decide_eq_true_eq]
          exact ⟨trivial, he⟩
  by_cases h0 : (ext [] prfStar).elim false (Rel stmt₀) = true
  · refine ⟨stmt₁, w₁, keys₁, hValid₁, hge stmt₁ w₁ keys₁ hRel₁ hPrfEq.symm ?_⟩
    cases hext : ext [] prfStar with
    | none => simp [hext] at h0
    | some w' =>
      simp only [hext, Option.elim_some] at h0 ⊢
      exact Bool.eq_false_iff.mpr fun h1 => hDisj w' ⟨h0, h1⟩
  · exact ⟨stmt₀, w₀, keys₀, hValid₀, hge stmt₀ w₀ keys₀ hRel₀ rfl (Bool.eq_false_iff.mpr h0)⟩

end PRGSeparation

end Cslib.Crypto.Protocols.VOLE
