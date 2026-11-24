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
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Foundations.Control.Monad.Memoize
import CslibFrontier.Languages.Probabilistic.Memoize
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.InterpNorm
import CslibFrontier.Languages.Probabilistic.Oracle.RunState
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.QueryCount
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
(ROM) for single-tree depth-`d` `leaf_hash::shake`-style VOLE-in-the-head vector commitments,
explicit query-bounded reductions to `AnonymousToken.extractedExperiment` and
`AnonymousToken.Conservation.extractedConservationExperiment`, and a separation witness showing why
PRG-based leaf commitments (`leaf_hash::aes_ctr`) do not admit a query-log extractor in the plain
ROM.

## Protocol model and extraction mechanism

* **Two-channel ROM (`VOLEITHROSpec`)**: a leaf commitment oracle `H_leaf(k, iv, idx) ↦ (sd, com)`
  ([BaumEtAl2023FAEST], `H0`; `faest-arch-opt` `leaf_hash::shake`) paired with a Fiat–Shamir
  challenge oracle `H_FS(stmt, iv, coms, d_corr, preMsg) ↦ Δ` (`FSQuery`). Including the witness
  correction `d_corr` and pre-challenge commitment `preMsg` inside `H_FS` commits `w* = d_corr + u`
  and `preMsg` before `Δ` is drawn, matching [BaumBMRS2023] and [BaumEtAl2026FAEST].
* **`FAEST.Conversion` reconstruction**: verifying the `2 ^ d - 1` opened indices `pIdx = i ^^^ Δ`
  (`collectOpenRows`) produces `FAEST.verifierRows`, so `FAEST.convertExpandedRows` satisfies
  `FAEST.convertExpandedRows_correlation` (`FAEST.Conversion`, Prop. 5.2) whenever the prover's
  `H_leaf` queries uniquely determine all `2 ^ d` leaves.
* **Zero-rewinding extraction (`extractWitnessFromTrace`)**: reading only the `H_leaf` query trace
  recorded *prior* to running verification recovers all `2 ^ d` leaves and `u`, yielding the witness
  `decWit (d_corr + u)` straight-line. Using a two-channel sticky bad-state handler
  (`voleithStickyMemoize`) via `OracleComp.toOuterMeasure_bad_le_two`, extraction failure across a
  single proof or an adaptive `m`-call verification oracle is bounded by
  `Q_leaf * ((Q_leaf + Q_FS) / 2 ^ comLen) + Q_FS * max ε_chal ε_rel`.
* **AnonymousToken bridges (`Basic` & `Conservation`)**: because a VOLE-ACT Issuer only verifies
  client proofs (`IssueRequest`, `SpendRequest`) and never simulates proofs for the adversary
  ([VOLEACT2026], Initial Issuance / Spending; [BaumBMRS2023], Lemma 4 / Theorem 5), plain
  straight-line multi-verify ROM extraction suffices without simulation-extractability. Unextracted
  ROM adversaries reduce explicitly to `AnonymousToken.extractedExperiment` and
  `AnonymousToken.Conservation.extractedConservationExperiment` with additive loss `ε_KS` and
  preserved signing/issuer query budgets.
* **PRG leaf separation (`leaf_hash::aes_ctr`)**: a local PRG prover makes `0` `H_leaf` queries and
  accepts with probability `1` under deterministic PRG verification, defeating any RO-query-log
  extractor (`tr_leaf = []`) with probability `1`; when two seeds collide on `PRG` (`com_Δ`) yet
  yield distinct expanded `u` values (motivating FAESTer's Almost-Injective PRG, Definition 27 and
  Lemma 32), even unbounded full-proof extractors fail on at least one witness.

## Scope and gaps

* Models a single depth-`d` `leaf_hash::shake` tree with arbitrary relation soundness `ε_rel`;
  multi-tree BAVC (`T_open`, grinding bits), full `VOLEHash`/`ZKHash` reductions (#4987),
  ideal-cipher AES-CTR extraction, and machine-checked PPT/`TimeM` runtime certificates remain open
  under #7068. All reductions are explicit `ProbComp`/`ProbOracleComp` programs with query-cost
  bounds, not Word-RAM or Turing-machine time bounds.

## References

* [C. Baum et al., *Publicly Verifiable Zero-Knowledge and Post-Quantum Signatures from
  VOLE-in-the-Head*][BaumBMRS2023], Lemma 1, Lemma 4, Theorem 5.
* [C. Baum et al., *FAEST: Algorithm Specifications*, version 1.0][BaumEtAl2023FAEST], Section 2.3.2
  and `H0` (`SHAKE`) leaf commitment.
* [C. Baum et al., *FAEST v3: Algorithm Specifications*, version 3.0][BaumEtAl2026FAEST], Sec. 5.4
  (Figure 5.6 / Proposition 5.2) and Section 5.5 (Figure 5.7).
* *FAESTer* (ePrint 2026/164), Section 3.3 (Definition 27 and Lemma 32): cited for the unbounded
  `Simple` PRG-leaf soundness argument contrasted here against query-log ROM extraction.
* [T. Zhang, C. Patton, S. Schlesinger, *VOLE-ACT*][VOLEACT2026], Parameters, Tag, Initial Issuance,
  and Spending.
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
@[expose] def leafOutputEquiv (sdLen comLen : ℕ) :
    LeafOutput sdLen comLen ≃ BitString comLen × BitString sdLen where
  toFun out := (out.com, out.seedOut)
  invFun p := ⟨p.2, p.1⟩
  left_inv out := by cases out; rfl
  right_inv p := by cases p; rfl

instance (sdLen comLen : ℕ) : Fintype (LeafOutput sdLen comLen) :=
  Fintype.ofEquiv (BitString comLen × BitString sdLen) (leafOutputEquiv sdLen comLen).symm

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

theorem eval_voleithMemoizeProg {d sdLen comLen rowLen : ℕ}
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
theorem collectOpenRows_of_trace {d sdLen comLen rowLen : ℕ} {Stmt Seed IV PreMsg Chal : Type}
    [BEq (LeafQuery d Seed IV)] [LawfulBEq (LeafQuery d Seed IV)]
    [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
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

/-- Honest `leaf_hash::shake` prover: commits all `2 ^ d` leaves via `H_leaf`, masks the witness
with `conv.u`, queries `H_FS` on `(stmt, iv, coms, dCorr, preMsg)`, and outputs `openKeys` for
all `idx ≠ hidden`. -/
@[expose] def voleithProveROM {d sdLen comLen rowLen : ℕ} {Stmt Seed IV PreMsg Chal Wit : Type}
    (expand : BitString sdLen → BitString rowLen)
    (encWit : Wit → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (mkPreMsg : (Fin d → BitString rowLen) → BitString rowLen → BitString rowLen → PreMsg)
    (defaultSeed : Seed) (iv : IV) (keys : Fin (2 ^ d) → Seed) (stmt : Stmt) (w : Wit) :
    ProbOracleComp (VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal)
      (VOLEITHProof d comLen rowLen Seed IV PreMsg) := do
  let (rows, coms) ← OracleComp.liftRight (spec₁ := unifSpec)
    (OracleComp.liftLeft (spec₂ := VOLEITHFSSpec d comLen rowLen Stmt IV PreMsg Chal)
      (honestCommitLeaves expand iv keys (2 ^ d) le_rfl))
  let conv := FAEST.convertExpandedRows d rows
  let dCorr := encWit w + conv.u
  let preMsg := mkPreMsg conv.columns conv.u dCorr
  let delta ← OracleComp.liftRight (spec₁ := unifSpec)
    (OracleComp.liftRight (spec₁ := VOLEITHLeafSpec d sdLen comLen Seed IV)
      (OracleComp.query ⟨stmt, iv, coms, dCorr, preMsg⟩))
  let hidden := chalToIdx delta
  let openKeys : Fin (2 ^ d) → Seed := fun idx => if idx = hidden then defaultSeed else keys idx
  return ⟨iv, coms, dCorr, preMsg, openKeys⟩

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
    (iv : IV) (keys : Fin (2 ^ d) → Seed) :
    ∀ (k : ℕ) (hk : k ≤ 2 ^ d)
      (rows : Fin (2 ^ d) → BitString rowLen) (coms : Fin (2 ^ d) → BitString comLen)
      (tr₁ : LeafTrace d sdLen comLen Seed IV),
      ((rows, coms), tr₁) ∈
        ((OracleComp.interpret
          (Cslib.memoize (fun _ : LeafQuery d Seed IV =>
            PMF.uniformOfFintype (LeafOutput sdLen comLen)))
          (honestCommitLeaves expand iv keys k hk)).run []).support →
      (∀ idx : Fin (2 ^ d), (idx : ℕ) < k →
        ∃ out, tr₁.lookup ⟨keys idx, iv, idx⟩ = some out ∧
          out.com = coms idx ∧ expand out.seedOut = rows idx) ∧
      (∀ e ∈ tr₁, (e.1.index : ℕ) < k) := by
  intro k
  induction k with
  | zero =>
    intro hk rows coms tr₁ hsupp
    simp only [honestCommitLeaves, OracleComp.run_interpret_pure, PMF.monad_pure_eq_pure,
      PMF.mem_support_pure_iff, Prod.mk.injEq] at hsupp
    obtain ⟨_, rfl⟩ := hsupp
    exact ⟨fun idx hlt => absurd hlt (Nat.not_lt_zero _), by simp⟩
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
        have hmem_tr₀ := List.lookup_eq_some_iff.mp h
        obtain ⟨before, after, heq⟩ := hmem_tr₀
        have hkmem : (⟨keys ⟨k, hk⟩, iv, ⟨k, hk⟩⟩, v) ∈ tr₀ := by
          simp [heq.1]
        have hlt := hbound₀ _ hkmem
        dsimp only at hlt
        omega
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
        · exact Nat.lt_succ_self k
        · exact Nat.lt_succ_of_lt (hbound₀ e he₀)

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
  change (b, st_end) ∈
    (ProbOracleComp.runWith voleithMemoize
      (do
        let prf ← voleithProveROM expand encWit chalToIdx mkPreMsg defaultSeed iv keys stmt w
        voleithVerifyROM expand chalToIdx checkRel stmt prf) ([], [])).support at hsupp
  rw [ProbOracleComp.runWith_bind, PMF.mem_support_bind_iff] at hsupp
  obtain ⟨⟨prf, st_mid⟩, hprove, hver⟩ := hsupp
  unfold voleithProveROM at hprove
  rw [ProbOracleComp.runWith_bind, PMF.mem_support_bind_iff] at hprove
  obtain ⟨⟨⟨rows, coms⟩, st_leaf⟩, hleaf, hfs⟩ := hprove
  rw [ProbOracleComp.runWith, OracleComp.runWith_sumHandler_liftRight,
    OracleComp.runWith_eq_run_interpret, voleithMemoize,
    RandomOracle.run_interpret_memoizeSum_liftLeft, PMF.mem_support_map_iff] at hleaf
  obtain ⟨⟨rc, tr₁⟩, hleaf_supp, hrc_eq⟩ := hleaf
  cases hrc_eq
  obtain ⟨hlook₁, -⟩ := honestCommitLeaves_trace_invariant expand iv keys (2 ^ d) le_rfl
    rows coms tr₁ hleaf_supp
  rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith, OracleComp.runWith_sumHandler_liftRight,
    OracleComp.runWith_eq_run_interpret, OracleComp.liftRight_query,
    OracleComp.run_interpret_query, voleithMemoize, RandomOracle.memoizeSum_inr,
    PMF.mem_support_bind_iff] at hfs
  obtain ⟨⟨delta, tr₂'⟩, hfs_mem, hprf_pure⟩ := hfs
  rw [PMF.mem_support_map_iff] at hfs_mem
  obtain ⟨⟨delta₀, tr₂_inner⟩, hmemo_fs, hpair_eq⟩ := hfs_mem
  cases hpair_eq
  rw [RandomOracle.mem_support_memoize_iff] at hmemo_fs
  rcases hmemo_fs with ⟨hsome, _⟩ | ⟨_, _, htr₂_eq⟩
  · simp at hsome
  · dsimp only at htr₂_eq
    rw [htr₂_eq] at hprf_pure
    simp only [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hprf_pure
    obtain ⟨rfl, rfl⟩ := hprf_pure
    unfold voleithVerifyROM at hver
    rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith,
      OracleComp.runWith_sumHandler_liftRight, OracleComp.runWith_eq_run_interpret,
      OracleComp.liftRight_query, OracleComp.run_interpret_query, voleithMemoize,
      RandomOracle.memoizeSum_inr, PMF.mem_support_bind_iff] at hver
    obtain ⟨⟨delta_v, st_v⟩, hv_fs, hv_rest⟩ := hver
    rw [PMF.mem_support_map_iff] at hv_fs
    obtain ⟨⟨delta_v₀, tr₂_v⟩, hv_memo, hst_v⟩ := hv_fs
    cases hst_v
    have hfs_hit : ([( ⟨stmt, iv, coms, encWit w + (FAEST.convertExpandedRows d rows).u,
        mkPreMsg (FAEST.convertExpandedRows d rows).columns
          (FAEST.convertExpandedRows d rows).u
          (encWit w + (FAEST.convertExpandedRows d rows).u)⟩, delta )] :
        FSTrace d comLen rowLen Stmt IV PreMsg Chal).lookup
        (⟨stmt, iv, coms, encWit w + (FAEST.convertExpandedRows d rows).u,
          mkPreMsg (FAEST.convertExpandedRows d rows).columns
            (FAEST.convertExpandedRows d rows).u
            (encWit w + (FAEST.convertExpandedRows d rows).u)⟩) = some delta := by
      simp
    rw [RandomOracle.mem_support_memoize_iff] at hv_memo
    rcases hv_memo with ⟨hlook_v, htr₂_v⟩ | ⟨hnone_v, _⟩
    · dsimp only at hlook_v htr₂_v
      have hdelta_eq : delta = delta_v := (Option.some.inj (hlook_v.symm.trans hfs_hit)).symm
      subst hdelta_eq
      rw [htr₂_v, ProbOracleComp.runWith_bind, ProbOracleComp.runWith,
        OracleComp.runWith_sumHandler_liftRight, OracleComp.runWith_eq_run_interpret] at hv_rest
      dsimp only at hv_rest
      have hopen : ∀ idx : Fin (2 ^ d), idx ≠ chalToIdx delta →
          ∃ out, tr₁.lookup
            ⟨(fun i => if i = chalToIdx delta then defaultSeed else keys i) idx, iv, idx⟩ =
              some out ∧ out.com = coms idx ∧ expand out.seedOut = rows idx := by
        intro idx hne
        simp only [hne, ↓reduceIte]
        exact hlook₁ idx idx.isLt
      have hcollect := collectOpenRows_of_trace (Stmt := Stmt) (PreMsg := PreMsg) (Chal := Chal)
        expand iv _ coms rows (chalToIdx delta) tr₁
        [(⟨stmt, iv, coms, encWit w + (FAEST.convertExpandedRows d rows).u,
          mkPreMsg (FAEST.convertExpandedRows d rows).columns
            (FAEST.convertExpandedRows d rows).u
            (encWit w + (FAEST.convertExpandedRows d rows).u)⟩, delta)]
        hopen (2 ^ d) le_rfl
      change (interpret voleithMemoize _).run _ = _ at hcollect
      dsimp only [voleithMemoize] at hcollect
      rw [hcollect, PMF.mem_support_bind_iff] at hv_rest
      obtain ⟨⟨vRows, st_after⟩, hvRows_mem, hv_check⟩ := hv_rest
      rw [PMF.mem_support_pure_iff, Prod.mk.injEq] at hvRows_mem
      obtain ⟨rfl, rfl⟩ := hvRows_mem
      have hv_eq : (fun i : Fin (2 ^ d) =>
          if (i : ℕ) < 2 ^ d then FAEST.verifierRows rows (chalToIdx delta) i else 0) =
          FAEST.verifierRows rows (chalToIdx delta) := by
        funext i
        simp [i.isLt]
      rw [hv_eq] at hv_check
      simp only [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hv_check
      obtain ⟨rfl, -⟩ := hv_check
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
    · exfalso
      simp [VOLEITHProof.fsQuery] at hnone_v

end ROProtocol

end Cslib.Crypto.Protocols.VOLE
