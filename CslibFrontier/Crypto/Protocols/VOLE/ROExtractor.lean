/-
Copyright (c) 2026 Samuel Schlesinger, Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.FAEST.Conversion
public import CslibFrontier.Crypto.Protocols.VOLE.Basic
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
public import CslibFrontier.Languages.Probabilistic.Oracle.RunState
public import CslibFrontier.Languages.Probabilistic.RandomOracle.Sum
import CslibFrontier.Foundations.Control.Monad.Memoize
import CslibFrontier.Languages.Probabilistic.Memoize
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.InterpNorm
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.QueryCount
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.RunWith
import CslibFrontier.Languages.Probabilistic.QueryCount.Scale
import CslibFrontier.Languages.Probabilistic.QueryCount.Sum
import CslibFrontier.Languages.Probabilistic.UntilBad.Flag
import CslibFrontier.Languages.Probabilistic.UntilBad.TwoCost
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Support
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.UniformBound
import CslibFrontier.Tactic.SuppCases
import Mathlib.Data.Finset.Card

/-!
# Straight-line ROM VOLE-in-the-head leaf extraction

This module formalizes straight-line knowledge extraction in the classical random oracle model
(ROM) for flat all-but-one `2 ^ d`-leaf (one-repetition, `µ = 1`) `leaf_hash::shake`-style
VOLE-in-the-head vector commitments, together with an adaptive multi-verify bound and a shared
verify-gated handler soundness-transfer interface.

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
  (`voleithStickyMemoize`) via `OracleComp.toOuterMeasure_bad_le_two` (`TwoCost`), extraction
  failure across a single proof or an adaptive `m`-call verification oracle is bounded by
  `Q_leaf * (Q_leaf + 2 ^ d * Q_FS) / 2 ^ comLen + Q_FS * ε_rel`.
* **Verify-gated handler transfer (`VerifyGatedBridge`)**: `verifyGatedHandlerProg`,
  `verifyGatedHandler`, and `toOuterMeasure_runWith_verifyGatedHandler_le` package adaptive ROM
  verification gating cleanly so downstream protocol bridges (such as `AnonymousToken.ROBridge`)
  can transfer acceptance predicates to extracted-witness continuations without exposing internal
  sticky-flag state.

## Main definitions

* `LeafQuery`, `LeafOutput`, `FSQuery`, `VOLEITHProof`, `VOLEITHROSpec`, `LeafTrace`, `FSTrace`,
  `VOLEITHTraceState`: two-channel lazy ROM interface and traces.
* `voleithMemoizeProg`, `voleithMemoize`, `collectOpenRows`, `voleithVerifyROM`,
  `honestCommitLeaves`, `voleithProveLeafFS`, `voleithProveROM`, `voleithHonestGame`: lazy
  two-channel verifier and honest prover.
* `extractLeafFromTrace`, `extractRowsFromTrace`, `extractVOLEFromTrace`, `extractWitnessFromTrace`:
  straight-line witness extraction from `H_leaf` query logs.
* `voleithKSBound`, `VOLEITHSoundnessError`, `voleithKSFailurePMF`, `voleithMultiVerifyHandler`,
  `verifyGatedHandlerProg`, `verifyGatedHandler`: concrete error bound, multi-verify oracle, and
  verify-gated oracle handler.

## Main results

* `isCostBounded_leaf_voleithVerifyROM`, `isCostBounded_fs_voleithVerifyROM`,
  `isCostBounded_leaf_voleithProveLeafFS`, `isCostBounded_fs_voleithProveLeafFS`: exact prover and
  verifier RO query budgets.
* `voleithProveLeafFS_verify_of_fresh`, `voleithHonestGame_eq_pure_true`: honest completeness in the
  two-channel ROM.
* `voleithKnowledgeSoundness_bound`: bounded conditional single-proof extraction error bound.
* `voleithMultiVerifyROM_sound_bound`: bounded conditional adaptive multi-verify extraction bound.
* `verifyGatedHandlerProg_eval`, `runWith_verifyGatedHandler_liftRight`,
  `toOuterMeasure_runWith_verifyGatedHandler_le`: executable-to-PMF equivalence and verify-gated
  acceptance transfer.

## Scope and gaps

* Bounded conditional step toward #7068 (#4987): models a single-repetition flat `2 ^ d`-leaf
  `leaf_hash::shake` commitment taking `VOLEITHSoundnessError` (`ε_rel`) as a hypothesis;
  multi-tree BAVC (`T_open`, grinding bits), full `VOLEHash`/`ZKHash` reductions (#4987),
  ideal-cipher AES-CTR extraction, and machine-checked PPT/`TimeM` runtime certificates remain open
  under #7068. All reductions are explicit `ProbComp`/`ProbOracleComp` programs with query-cost
  bounds, not Word-RAM or Turing-machine time bounds.

## References

* [C. Baum et al., *Publicly Verifiable Zero-Knowledge and Post-Quantum Signatures from
  VOLE-in-the-Head* (full version, ePrint 2023/996)][BaumBMRS2023Eprint], Section 4 (Lemma 4,
  pp. 19–20, specialised here to one challenge round and RO leaf commitments).
* [C. Baum et al., *FAEST: Algorithm Specifications*, version 1.0][BaumEtAl2023FAEST]: `H0`
  (`SHAKE`) leaf hashing.
* [C. Baum et al., *FAEST v3: Algorithm Specifications*, version 3.0][BaumEtAl2026FAEST],
  Section 5.4 (Figure 5.6 / Proposition 5.2) and Section 5.5 (Figure 5.7).
-/

public section

namespace Cslib.Crypto.Protocols.VOLE

open Cslib Cslib.Probability Cslib.OracleComp
open Cslib.Crypto.FAEST
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


/-- Evaluating `voleithMemoizeProg` in `PMF` equals `voleithMemoize`. -/
theorem eval_voleithMemoizeProg {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [Fintype Chal] [Nonempty Chal]
    (q : LeafQuery d Seed IV ⊕ FSQuery d comLen rowLen Stmt IV PreMsg)
    (st : VOLEITHTraceState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) :
    ProbComp.eval (voleithMemoizeProg q st) = voleithMemoize q st := by
  rcases st with ⟨tr₁, tr₂⟩
  rcases q with q | q <;>
    simp only [voleithMemoizeProg, voleithMemoize, OracleComp.sumHandler,
      RandomOracle.memoizeSum_inl, RandomOracle.memoizeSum_inr,
      RandomOracle.eval_zoomStateT_memoize, ProbComp.eval_uniform]


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
  rw [← Nat.zero_add (2 ^ d - 1)]
  refine (IsCostBounded.liftRight
    (IsCostBounded.liftRight_of_cost_inr_eq_zero (fun _ => rfl) _)
    (fun _ => le_rfl)).bind fun delta => ?_
  rw [← Nat.add_zero (2 ^ d - 1)]
  refine (IsCostBounded.liftRight
    ((isCostBounded_collectOpenRows expand prf.iv prf.openKeys prf.coms _ (2 ^ d)
      le_rfl).liftLeft fun _ => le_rfl)
    (fun _ => le_rfl)).bind fun vRows => ?_
  cases vRows <;> exact IsCostBounded.pure _ 0

theorem isCostBounded_fs_voleithVerifyROM {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal : Type}
    (expand : BitString sdLen → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    (stmt : Stmt) (prf : VOLEITHProof d comLen rowLen Seed IV PreMsg) :
    IsCostBounded (Sum.elim (fun _ => 0) (voleithFSCost (Stmt := Stmt) (PreMsg := PreMsg)))
      (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel stmt prf) 1 := by
  unfold voleithVerifyROM
  rw [← Nat.add_zero 1]
  refine (IsCostBounded.liftRight
    (IsCostBounded.liftRight (IsCostBounded.query _) fun _ => le_rfl)
    (fun _ => le_rfl)).bind fun delta => ?_
  rw [← Nat.zero_add 0]
  refine (IsCostBounded.liftRight
    (IsCostBounded.liftLeft_of_cost_inl_eq_zero (fun _ => rfl) _)
    (fun _ => le_rfl)).bind fun vRows => ?_
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
      · obtain rfl : i = 0 := Fin.ext (Nat.lt_one_iff.mp hi)
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


/-- `honestCommitLeaves` makes at most `k` `H_leaf` queries. -/
private theorem isCostBounded_honestCommitLeaves {d sdLen comLen rowLen : ℕ} {Seed IV : Type}
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

private theorem mem_of_lookup_eq_some {α β : Type} [BEq α] [LawfulBEq α]
    {l : List (α × β)} {k : α} {v : β} (h : l.lookup k = some v) : (k, v) ∈ l := by
  obtain ⟨_, _, heq⟩ := List.lookup_eq_some_iff.mp h
  simp [heq.1]

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
    obtain ⟨⟨rfl, rfl⟩, htr_eq⟩ := hpure
    dsimp only at htr_eq hmem_out
    have hnone : tr₀.lookup ⟨keys ⟨k, hk⟩, iv, ⟨k, hk⟩⟩ = none := by
      by_contra h
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp h
      rcases hbound₀ _ (mem_of_lookup_eq_some hv) with ⟨_, hlt⟩ | hmem₁₀
      · simp at hlt
      · exact hiv₁₀ _ hmem₁₀ rfl
    rw [RandomOracle.mem_support_memoize_iff] at hmem_out
    rcases hmem_out with ⟨hsome, _⟩ | ⟨_, _, htr_cons⟩
    · simp [hnone] at hsome
    · dsimp only at htr_cons
      rw [htr_eq, htr_cons]
      constructor
      · intro idx hlt
        by_cases hik : idx = ⟨k, hk⟩
        · subst hik
          refine ⟨out, by simp, ?_, ?_⟩ <;> simp
        · have hlt' : (idx : ℕ) < k := by
            have : (idx : ℕ) ≠ k := fun h => hik (Fin.ext h)
            omega
          obtain ⟨out', hlook', hcom', hrow'⟩ := hlook₀ idx hlt'
          have hqne : ((⟨keys idx, iv, idx⟩ : LeafQuery d Seed IV) ==
              ⟨keys ⟨k, hk⟩, iv, ⟨k, hk⟩⟩) = false :=
            beq_false_of_ne fun heq => hik (congrArg LeafQuery.index heq)
          refine ⟨out', ?_, by simp [Function.update, hik, hcom'],
            by simp [Function.update, hik, hrow']⟩
          simp [List.lookup_cons, hqne, hlook']
      · rintro e he
        rcases List.mem_cons.mp he with rfl | he₀
        · exact Or.inl ⟨rfl, Nat.lt_succ_self k⟩
        · exact (hbound₀ e he₀).imp (fun ⟨hiv, hlt⟩ => ⟨hiv, Nat.lt_succ_of_lt hlt⟩) id

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
  obtain ⟨⟨_, tr₂'⟩, hfs_mem, hprf_pure⟩ := hfs
  rw [PMF.mem_support_map_iff] at hfs_mem
  obtain ⟨⟨delta, tr₂_inner⟩, hmemo_fs, hpair_eq⟩ := hfs_mem
  simp only [Prod.mk.injEq] at hpair_eq
  obtain ⟨rfl, rfl⟩ := hpair_eq
  let q_fs : FSQuery d comLen rowLen Stmt IV PreMsg :=
    ⟨stmt, iv, coms, encWit w + (FAEST.convertExpandedRows d rows).u,
      mkPreMsg (FAEST.convertExpandedRows d rows).columns
        (FAEST.convertExpandedRows d rows).u
        (encWit w + (FAEST.convertExpandedRows d rows).u)⟩
  have hnone₂ : tr₂₀.lookup q_fs = none := by
    by_contra h
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp h
    exact hiv₂ _ (mem_of_lookup_eq_some hv) rfl
  rw [RandomOracle.mem_support_memoize_iff] at hmemo_fs
  rcases hmemo_fs with ⟨hsome, _⟩ | ⟨_, _, htr₂_eq⟩
  · simp [hnone₂, q_fs] at hsome
  · dsimp only at htr₂_eq
    rw [htr₂_eq] at hprf_pure
    simp only [OracleComp.run_interpret_pure, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff,
      Prod.mk.injEq] at hprf_pure
    obtain ⟨rfl, rfl⟩ := hprf_pure
    refine ⟨?_, fun e he => (hbound₁ e he).imp And.left id, fun e he => ?_⟩
    · unfold voleithVerifyROM
      rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith,
        OracleComp.runWith_sumHandler_liftRight, OracleComp.runWith_eq_run_interpret,
        OracleComp.liftRight_query, OracleComp.run_interpret_query, voleithMemoize,
        RandomOracle.memoizeSum_inr]
      have hmemo_v :
          Cslib.memoize (fun _ : FSQuery d comLen rowLen Stmt IV PreMsg =>
            PMF.uniformOfFintype Chal)
            (VOLEITHProof.fsQuery stmt
              ⟨iv, coms, encWit w + (FAEST.convertExpandedRows d rows).u,
                mkPreMsg (FAEST.convertExpandedRows d rows).columns
                  (FAEST.convertExpandedRows d rows).u
                  (encWit w + (FAEST.convertExpandedRows d rows).u),
                fun idx => if idx = chalToIdx delta then defaultSeed else keys idx⟩)
            ((q_fs, delta) :: tr₂₀) =
          PMF.pure (delta, (q_fs, delta) :: tr₂₀) := by
        simp [VOLEITHProof.fsQuery, q_fs, Cslib.memoize, PMF.monad_pure_eq_pure]
      rw [hmemo_v, PMF.pure_map, PMF.pure_bind]
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
        expand iv _ coms rows (chalToIdx delta) tr₁ ((q_fs, delta) :: tr₂₀) hopen (2 ^ d) le_rfl
      change (interpret voleithMemoize _).run _ = _ at hcollect
      dsimp only [voleithMemoize] at hcollect
      rw [hcollect, PMF.pure_bind]
      dsimp only
      have hv_eq : (fun i : Fin (2 ^ d) =>
          if (i : ℕ) < 2 ^ d then FAEST.verifierRows rows (chalToIdx delta) i else 0) =
          FAEST.verifierRows rows (chalToIdx delta) :=
        funext fun i => ite_eq_left i.isLt
      rw [hv_eq, ProbOracleComp.runWith_pure]
      refine congrArg (fun b => PMF.pure (b, (tr₁, _))) ?_
      rw [funext (FAEST.convertExpandedRows_correlation rows (chalToIdx delta))]
      exact hRel (FAEST.convertExpandedRows d rows).columns
        (FAEST.convertExpandedRows d rows).u delta
    · rcases List.mem_cons.mp he with rfl | he₀
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
  simp only [seenComList, List.length_append, List.length_map, List.length_flatMap,
    List.length_ofFn, List.map_const', List.sum_replicate, smul_eq_mul, mul_comm]

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
  simp [extractLeafFromTrace, List.find?, hne]

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
    obtain ⟨hhead, htl⟩ := List.pairwise_cons.mp hpw
    by_cases hp : decide (hd.1.iv = iv ∧ hd.1.index = idx ∧ hd.2.com = coms idx) = true
    · simp only [List.find?_cons, hp]
      rcases List.mem_cons.mp hmem with rfl | hmem_tl
      · rfl
      · exact absurd ((of_decide_eq_true hp).2.2.trans hcom.symm) (hhead _ hmem_tl)
    · simp only [List.find?_cons, Bool.eq_false_iff.mpr hp]
      rcases List.mem_cons.mp hmem with rfl | hmem_tl
      · exact absurd (decide_eq_true ⟨hiv, hidx, hcom⟩) hp
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
    | some out => simp [PMF.toOuterMeasure_pure_apply, OracleComp.FlagBad]
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
      rw [seenComList_length]
      simp only [BitString, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, voleithBudget,
        one_div, ← div_eq_mul_inv, Nat.cast_pow, Nat.cast_ofNat, le_refl]
  · simp only [voleithStepKernel, voleithLeafCost, voleithFSCost, Nat.cast_zero, zero_mul,
      Nat.cast_one, one_mul, zero_add]
    cases hlook : tr₂.lookup qf with
    | some delta => simp [PMF.toOuterMeasure_pure_apply, OracleComp.FlagBad]
    | none =>
      rw [PMF.toOuterMeasure_map_apply]
      let rows := extractRowsFromTrace expand tr₁ qf.iv qf.coms
      cases hrel : Rel qf.stmt (decWit (qf.dCorr + (FAEST.convertExpandedRows d rows).u)) with
      | false =>
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
          simpa [OracleComp.FlagBad, fsLuckyBad, rows, hrel] using hdelta
        exact ((PMF.uniformOfFintype Chal).toOuterMeasure.mono hsub).trans
          (hSound qf.stmt rows qf.dCorr qf.preMsg hrel)
      | true =>
        refine le_trans (le_of_eq ?_) zero_le
        rw [PMF.toOuterMeasure_apply_eq_zero_iff]
        refine Set.disjoint_left.mpr fun delta _ hpre => ?_
        simp [OracleComp.FlagBad, fsLuckyBad, rows, hrel] at hpre

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
        Nat.cast_zero, zero_mul, add_zero, List.length_cons, div_eq_mul_inv]
      exact le_of_eq (by push_cast; ring)
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
        add_zero, Nat.cast_one, one_mul, List.length_cons, div_eq_mul_inv]
      exact le_of_eq (by push_cast; ring)

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
        exact (Cslib.Probability.PMF.toOuterMeasure_lift_eq_zero (ProbComp.unifOracle m) s hs).le
      | inr q =>
        exact toOuterMeasure_voleithStickyMemoize_step_le expand decWit chalToIdx Rel checkRel
          hSound q s hs)
    (fun q s hs x hx hgood => by
      cases q with
      | inl m =>
        simp [Cslib.Probability.PMF.snd_eq_of_mem_support_lift hx]
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

private theorem sticky_step_flagBad_false {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    {q : LeafQuery d Seed IV ⊕ FSQuery d comLen rowLen Stmt IV PreMsg}
    {s s' : VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal}
    {a : VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal q}
    (hs' : (a, s') ∈ (voleithStickyMemoize expand decWit chalToIdx Rel checkRel q s).support)
    (hclean' : s'.2 = false) :
    s.2 = false := by
  rcases s with ⟨tr, false | true⟩
  · rfl
  · have hbad' := OracleComp.isFlagMonotone_withBadFlag
      (voleithStepKernel expand decWit chalToIdx Rel checkRel) q tr (a, s') hs'
    simp [OracleComp.FlagBad, hclean'] at hbad'

private theorem runWith_sticky_preserves_goodInv {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit α : Type}
    [BEq (LeafQuery d Seed IV)] [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    {prog : ProbOracleComp (VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) α}
    {s s' : VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal}
    (hs : s.2 = false → VOLEITHGoodInv expand decWit chalToIdx Rel checkRel s.1)
    {a : α}
    (hs' : (a, s') ∈
      (ProbOracleComp.runWith (voleithStickyMemoize expand decWit chalToIdx Rel checkRel)
        prog s).support)
    (hclean' : s'.2 = false) :
    VOLEITHGoodInv expand decWit chalToIdx Rel checkRel s'.1 :=
  ProbOracleComp.runWith_invariant _
    (fun u => u.2 = false → VOLEITHGoodInv expand decWit chalToIdx Rel checkRel u.1)
    (fun q u hu b next hnext => voleithStickyMemoize_preserves_goodInv expand decWit chalToIdx
      Rel checkRel q u hu b next hnext)
    prog s hs a s' hs' hclean'

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
  have hbad_mid : OracleComp.FlagBad st_mid := Bool.eq_true_of_not_eq_false htrue
  have hbad_end : OracleComp.FlagBad st' :=
    ProbOracleComp.runWith_invariant _ (fun s => OracleComp.FlagBad s)
      (fun q s hs a next hx => Bool.eq_true_of_not_eq_false fun hnext =>
        Bool.false_ne_true ((sticky_step_flagBad_false (q := q) expand decWit chalToIdx Rel checkRel
          hx hnext).symm.trans hs))
      prog st_mid hbad_mid b st' hsupp
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
      · obtain rfl : k = 0 := congrArg Fin.val hk0
        simp only [collectOpenRows, OracleComp.liftLeft_pure, OracleComp.liftRight_pure,
          ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff, Prod.mk.injEq,
          Option.some.injEq] at hrest
        obtain ⟨rfl, rfl⟩ := hrest
        simp only [hk0, ↓reduceIte, OracleComp.liftLeft_pure, OracleComp.liftRight_pure,
          ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff, Prod.mk.injEq, Option.some.injEq]
          at hstep
        obtain ⟨rfl, rfl⟩ := hstep
        refine ⟨hinv_mid, htr2_mid, hleaf_mid, fun i hi => ?_⟩
        obtain rfl : i = 0 := Fin.ext (Nat.lt_one_iff.mp hi)
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
          obtain ⟨hopen_eq, rfl⟩ := hite
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
            have hleaf_pIdx := extractLeafFromTrace_eq_of_mem_pairwise hinv_mid.1
              (mem_of_lookup_eq_some hlook_q) rfl rfl hcom
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
  have ⟨hst_mid_tr1, hfs_in_mid⟩ : st_mid.1.1 = tr₁ ∧ (prf.fsQuery stmt, delta) ∈ st_mid.1.2 := by
    cases hlook : tr₂.lookup (prf.fsQuery stmt) with
    | some d0 =>
      simp only [hlook, PMF.mem_support_pure_iff, Prod.mk.injEq] at hfs_supp
      obtain ⟨rfl, rfl⟩ := hfs_supp
      exact ⟨rfl, mem_of_lookup_eq_some hlook⟩
    | none =>
      simp only [hlook, PMF.mem_support_map_iff, Prod.mk.injEq] at hfs_supp
      obtain ⟨_, -, rfl, rfl⟩ := hfs_supp
      exact ⟨rfl, List.mem_cons_self ..⟩
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


private theorem toOuterMeasure_mono_on_support {α : Type*} (p : PMF α) {s t : Set α}
    (h : ∀ x ∈ p.support, x ∈ s → x ∈ t) :
    p.toOuterMeasure s ≤ p.toOuterMeasure t := by
  have hzero : p.toOuterMeasure (s \ t) = 0 :=
    (PMF.toOuterMeasure_apply_eq_zero_iff p _).mpr
      (Set.disjoint_left.mpr fun x hx ⟨hxs, hxt⟩ => hxt (h x hx hxs))
  exact (MeasureTheory.measure_mono (μ := p.toOuterMeasure)
    fun x hx => (Classical.em (x ∈ t)).imp id (⟨hx, ·⟩)).trans
    ((MeasureTheory.measure_union_le t (s \ t)).trans (by simp [hzero]))

/-- Bounded, conditional step toward straight-line VOLEitH knowledge soundness (#7068, #4987), not
the cited lemma itself: conditional on `hSound : VOLEITHSoundnessError ... ε_rel` for a single
challenge repetition (`µ = 1`) over flat `2 ^ d`-leaf `leaf_hash::shake` RO commitments
(`ProbOracleComp` query bounds, not full multi-tree BAVC or runtime certificates), running prover
`P` and extracting `w* = extractWitnessFromTrace` from `tr_P` without rewinding prior to
`voleithVerifyROM` fails with probability at most
`voleithKSBound d comLen (Q_leaf + (2 ^ d - 1)) (Q_FS + 1) ε_rel : ℝ≥0`. After
[BaumBMRS2023Eprint], Lemma 4, pp. 19–20. -/
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
  have hks_eq :
      voleithKSFailurePMF expand decWit chalToIdx Rel checkRel P =
        (ProbOracleComp.runWith S P (([], []), false)).bind fun ((stmt, prf), st_mid) =>
          (ProbOracleComp.runWith S (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel
              stmt prf) st_mid).map fun (ok, _) =>
            ok && !Rel stmt (extractWitnessFromTrace expand decWit st_mid.1.1 prf) := by
    unfold voleithKSFailurePMF
    rw [← voleithStickyMemoize_map_forget expand decWit chalToIdx Rel checkRel P ([], []) false,
      PMF.bind_map]
    congr 1
    funext ⟨⟨stmt, prf⟩, st_mid⟩
    dsimp only [Function.comp_apply, Prod.map, id_eq]
    rw [← voleithStickyMemoize_map_forget expand decWit chalToIdx Rel checkRel
      (voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel stmt prf) st_mid.1 st_mid.2,
      PMF.map_comp]
    rfl
  have hinvP : ∀ (res : Stmt × VOLEITHProof d comLen rowLen Seed IV PreMsg)
      (st_mid : VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal),
      (res, st_mid) ∈ (ProbOracleComp.runWith S P (([], []), false)).support →
      st_mid.2 = false →
      VOLEITHGoodInv expand decWit chalToIdx Rel checkRel st_mid.1 :=
    fun _ _ hmem hclean =>
      runWith_sticky_preserves_goodInv expand decWit chalToIdx Rel checkRel
        (fun _ => ⟨List.Pairwise.nil, by simp⟩) hmem hclean
  have hle_comb :
      (voleithKSFailurePMF expand decWit chalToIdx Rel checkRel P) true ≤
        (ProbOracleComp.runWith S combined (([], []), false)).toOuterMeasure
          {x | OracleComp.FlagBad x.2} := by
    have hcomb_eq : combined = P >>= fun sp =>
        voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel sp.1 sp.2 := rfl
    rw [hks_eq, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_bind_apply, hcomb_eq,
      ProbOracleComp.runWith_bind, PMF.toOuterMeasure_bind_apply]
    refine tsum_le_tsum fun ⟨⟨stmt, prf⟩, st_mid⟩ => ?_
    by_cases hsupp1 : ((stmt, prf), st_mid) ∈ (ProbOracleComp.runWith S P (([], []), false)).support
    · gcongr
      rw [PMF.toOuterMeasure_map_apply]
      refine toOuterMeasure_mono_on_support _ fun ⟨ok, st_end⟩ hsupp2 heq => ?_
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Bool.and_eq_true,
        Bool.not_eq_true'] at heq
      refine Bool.eq_true_of_not_eq_false fun hc_end => ?_
      have hc_mid : st_mid.2 = false :=
        runWith_sticky_flagBad_false expand decWit chalToIdx Rel checkRel hsupp2 hc_end
      have hinv_mid := hinvP (stmt, prf) st_mid hsupp1 hc_mid
      rcases st_mid with ⟨ro_mid, b_mid⟩
      dsimp only at hc_mid hinv_mid heq
      subst hc_mid
      have hgood_rel := voleithVerifyROM_sound_of_clean expand decWit chalToIdx Rel checkRel
        stmt prf ro_mid st_end hinv_mid (heq.1 ▸ hsupp2) hc_end
      exact Bool.false_ne_true (heq.2.symm.trans hgood_rel)
    · simp [(PMF.apply_eq_zero_iff _ _).mpr hsupp1]
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
  rcases x with ⟨⟨ro_s, b_s⟩, failed⟩
  rcases q with ⟨stmt, prf⟩ | qRO
  · simp only [voleithMultiVerifyStickyHandler, PMF.mem_support_map_iff, Prod.mk.injEq] at hx'
    obtain ⟨⟨ok, s'⟩, hs'_mem, -, rfl⟩ := hx'
    have hclean_s : b_s = false :=
      runWith_sticky_flagBad_false expand decWit chalToIdx Rel checkRel hs'_mem hclean'
    obtain ⟨hfail_f, hinv_s⟩ := hinv hclean_s
    dsimp only at hfail_f hinv_s
    refine ⟨?_, runWith_sticky_preserves_goodInv expand decWit chalToIdx Rel checkRel
      (fun _ => hinv_s) hs'_mem hclean'⟩
    cases ok with
    | false => simp [hfail_f]
    | true =>
      subst hclean_s
      have hrel := voleithVerifyROM_sound_of_clean expand decWit chalToIdx Rel checkRel stmt prf
        ro_s s' hinv_s hs'_mem hclean'
      simp [hfail_f, hrel]
  · simp only [voleithMultiVerifyStickyHandler, PMF.mem_support_map_iff, Prod.mk.injEq] at hx'
    obtain ⟨⟨ans, s'⟩, hs'_mem, -, rfl⟩ := hx'
    have hclean_s : b_s = false :=
      sticky_step_flagBad_false expand decWit chalToIdx Rel checkRel hs'_mem hclean'
    obtain ⟨hfail_f, hinv_s⟩ := hinv hclean_s
    exact ⟨hfail_f, voleithStickyMemoize_preserves_goodInv expand decWit chalToIdx Rel checkRel
      qRO (ro_s, b_s) (fun _ => hinv_s) ans s' hs'_mem hclean'⟩

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


private noncomputable def mvToRO {d sdLen comLen rowLen : ℕ} {Stmt Seed IV PreMsg Chal : Type}
    (expand : BitString sdLen → BitString rowLen) (chalToIdx : Chal → Fin (2 ^ d))
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool) :
    (q : (Stmt × VOLEITHProof d comLen rowLen Seed IV PreMsg) ⊕
        (LeafQuery d Seed IV ⊕ FSQuery d comLen rowLen Stmt IV PreMsg)) →
      ProbOracleComp (VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal)
        (VOLEITHMultiVerifySpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal q)
  | .inl (stmt, prf) => voleithVerifyROM (Chal := Chal) expand chalToIdx checkRel stmt prf
  | .inr qRO => ProbOracleComp.query qRO

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
  intro k₁ k₂ hk₁ hk₂ ⟨tr, b⟩ failed hclean
  dsimp only at hclean
  subst hclean
  have hmap :
      ((ProbOracleComp.runWith
          (voleithMultiVerifyStickyHandler expand decWit chalToIdx Rel checkRel)
          prog ((tr, false), failed)).map (Prod.map id Prod.fst)) =
        ProbOracleComp.runWith (voleithStickyMemoize expand decWit chalToIdx Rel checkRel)
          (ProbOracleComp.simulate (mvToRO expand chalToIdx checkRel) prog) (tr, false) := by
    rw [ProbOracleComp.runWith_simulate]
    refine ProbOracleComp.runWith_map_state _ _ Prod.fst (fun q x => ?_) prog ((tr, false), failed)
    rcases x with ⟨st, f⟩
    rcases q with ⟨stmt, prf⟩ | qRO
    · simp only [voleithMultiVerifyStickyHandler, mvToRO, PMF.map_comp]
      exact PMF.map_id _
    · simp only [voleithMultiVerifyStickyHandler, mvToRO, ProbOracleComp.runWith_query,
        PMF.map_comp]
      exact PMF.map_id _
  have hleaf :
      IsCostBounded (Sum.elim (fun _ => 0) voleithLeafCost)
        (ProbOracleComp.simulate (mvToRO expand chalToIdx checkRel) prog) k₁ := by
    refine ProbOracleComp.isCostBounded_simulate (fun q => ?_) hk₁
    rcases q with ⟨stmt, prf⟩ | qRO
    · exact isCostBounded_leaf_voleithVerifyROM expand chalToIdx checkRel stmt prf
    · exact ProbOracleComp.isCostBounded_query voleithLeafCost qRO
  have hfs :
      IsCostBounded (Sum.elim (fun _ => 0) voleithFSCost)
        (ProbOracleComp.simulate (mvToRO expand chalToIdx checkRel) prog) k₂ := by
    refine ProbOracleComp.isCostBounded_simulate (fun q => ?_) hk₂
    rcases q with ⟨stmt, prf⟩ | qRO
    · exact isCostBounded_fs_voleithVerifyROM expand chalToIdx checkRel stmt prf
    · exact ProbOracleComp.isCostBounded_query voleithFSCost qRO
  have hev :
      ({x : α × (VOLEITHStickyState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal × Bool) |
          OracleComp.FlagBad x.2.1} : Set _) =
        (Prod.map id Prod.fst) ⁻¹' {y | OracleComp.FlagBad y.2} := rfl
  rw [hev, ← PMF.toOuterMeasure_map_apply, hmap]
  simpa [voleithBudget] using
    toOuterMeasure_runWith_voleithStickyMemoize_bad_le_of_state expand decWit chalToIdx Rel
      checkRel hSound hleaf hfs tr

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

/-- Bounded, conditional step toward adaptive multi-verify VOLEitH soundness (#7068, #4987), not the
cited lemma itself: conditional on `hSound : VOLEITHSoundnessError ... ε_rel` for
single-repetition flat `2 ^ d`-leaf `leaf_hash::shake` commitments (`ProbOracleComp` query bounds,
without full multi-tree BAVC or runtime certificates), if an adaptive adversary `A` with access to
`Verify` and `VOLEITHROSpec` makes at most `m` verification queries, `Q_leaf` direct `H_leaf`
queries, and `Q_FS` direct `H_FS` queries, then against `voleithMultiVerifyHandler` the probability
that *any* verified proof fails `Rel` extraction from `tr_leaf` prior to that call is at most
`voleithKSBound d comLen (Q_leaf + m * (2 ^ d - 1)) (Q_FS + m) ε_rel : ℝ≥0`. After
[BaumBMRS2023Eprint], Lemma 4, pp. 19–20, at `µ = 1`. -/
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
  have hprob_eq :
      ((ProbOracleComp.runWith (voleithMultiVerifyHandler expand decWit chalToIdx Rel checkRel)
          A (([], []), false)).map fun (_, _, bad) => bad) true =
        ((ProbOracleComp.runWith
          (voleithMultiVerifyStickyHandler expand decWit chalToIdx Rel checkRel)
          A ((([], []), false), false)).map fun (_, _, bad) => bad) true := by
    erw [← ProbOracleComp.runWith_map_state _ _ mvDropFlag
      (voleithMultiVerifyStickyHandler_map_forget expand decWit chalToIdx Rel checkRel)
      A ((([], []), false), false), PMF.map_comp]
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
          A ((([], []), false), false)).toOuterMeasure {x | OracleComp.FlagBad x.2.1} :=
    toOuterMeasure_mono_on_support _ fun ⟨a, x'⟩ hmem hfail =>
      Bool.eq_true_of_not_eq_false fun hc => by
        simp [Set.mem_preimage, hinv_A a x' hmem hc] at hfail
  refine hle_bad.trans ?_
  rw [voleithKSBound_coe]
  simpa [voleithBudget] using
    toOuterMeasure_run_mvSticky_bad_le expand decWit chalToIdx Rel checkRel hSound A
      (isCostBounded_mvLeafCost_add hm hleaf) (isCostBounded_mvFSCost_add hm hfs)
      (([], []), false) false rfl

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
  have hclean : s.2 = false :=
    sticky_step_flagBad_false expand decWit chalToIdx Rel checkRel hs' hclean'
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
      ProbOracleComp.eval_runState, eval_voleithMemoizeProg]
    congr 1
    funext ⟨ok, roSt'⟩
    cases ok <;> simp [ProbComp.eval_pure]
  · simp only [verifyGatedHandlerProg, verifyGatedHandler, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.map]
    erw [eval_voleithMemoizeProg]
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
  · simp only [verifyGatedStickyHandler, PMF.mem_support_map_iff, Prod.mk.injEq] at hmem
    obtain ⟨⟨ans, st_res⟩, hst_mem, -, ⟨hro_eq, -⟩, hres2⟩ := hmem
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
          · have hzero (c : ProbComp (Resp × Log)) :
                ((ProbComp.eval c).map fun x => (x.1, ((ro_end, x.2), true)))
                  (a, ((roSt', log'), false)) = 0 :=
              (PMF.apply_eq_zero_iff _ _).mpr <| by
                rw [PMF.mem_support_map_iff]
                rintro ⟨_, -, ⟨⟩⟩
            simp [hzero]
      · simp [(PMF.apply_eq_zero_iff _ _).mpr hmem]
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
  refine OracleComp.IsCostBounded.run_interpret
    (cost := Sum.elim (fun _ => 0) (Sum.elim (fun _ => reqCost) roCost))
    (cost' := Sum.elim (fun _ => 0) (Sum.elim (fun _ => reqCost) roCost)) (fun q log => ?_)
    hB log₀
  rcases q with n | (req | qRO)
  · simp only [StateT.run_lift, Sum.elim_inl]
    rw [show (0 : ℕ) = 0 + 0 from rfl]
    exact (ProbOracleComp.isCostBounded_sample _ _).bind fun _ => OracleComp.IsCostBounded.pure _ 0
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
      exact hro_eq ▸ runWith_sticky_preserves_goodInv expand decWit chalToIdx Rel checkRel
        hs hst_mem hres2
    · simp only [verifyGatedStickyHandler, PMF.mem_support_map_iff, Prod.mk.injEq] at hs'
      obtain ⟨⟨ans, st_res⟩, hst_mem, _, ⟨hro_eq, _⟩, hres2⟩ := hs'
      dsimp only at hro_eq hres2
      exact hro_eq ▸ voleithStickyMemoize_preserves_goodInv expand decWit chalToIdx
        Rel checkRel qRO (roSt, bs) hs ans st_res hst_mem hres2
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
          prog ((([], []), log₀), false)).toOuterMeasure {x | x.2.2 = true} :=
    toOuterMeasure_mono_on_support _ fun ⟨a, st⟩ hmem hbad =>
      Bool.eq_true_of_not_eq_false fun hclean =>
        hbad.elim (fun h => Bool.false_ne_true (hclean.symm.trans h))
          (fun h => h (hinv_bad a st hmem hclean))
  refine hle_flag.trans ?_
  let mvProg : ProbOracleComp (VOLEITHMultiVerifySpec d sdLen comLen rowLen
      Stmt Seed IV PreMsg Chal) (α × Log) :=
    (OracleComp.interpret
      (OracleComp.sumHandler
        (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
        (verifyGatedToMVInner (d := d) (sdLen := sdLen) (Chal := Chal)
          toStmt toProof onReject onAccept))
      prog).run log₀
  have hmv_m := verifyGatedToMVInner_cost (d := d) (sdLen := sdLen) (Chal := Chal)
    toStmt toProof onReject onAccept 1 (fun _ => 0) prog log₀ hm
  have hmv_leaf := verifyGatedToMVInner_cost (d := d) (sdLen := sdLen) (Chal := Chal)
    toStmt toProof onReject onAccept 0 voleithLeafCost prog log₀ hleaf
  have hmv_fs := verifyGatedToMVInner_cost (d := d) (sdLen := sdLen) (Chal := Chal)
    toStmt toProof onReject onAccept 0 voleithFSCost prog log₀ hfs
  have hmv_bad := toOuterMeasure_run_mvSticky_bad_le expand decWit chalToIdx Rel checkRel
    hSound mvProg (isCostBounded_mvLeafCost_add hmv_m hmv_leaf)
    (isCostBounded_mvFSCost_add hmv_m hmv_fs) (([], []), false) false rfl
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
    dsimp only [mvProg]
    rw [ProbOracleComp.runWith_run_interpret
      (verifyGatedToMVInner (d := d) (sdLen := sdLen) (Chal := Chal)
        toStmt toProof onReject onAccept)
      (voleithMultiVerifyStickyHandler expand decWit chalToIdx Rel checkRel)
      prog log₀ ((([], []), false), false), PMF.map_comp]
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


/-- **Verify-gated acceptance transfer**: running `prog` against `verifyGatedHandler` with
`onAccept₁` satisfies boolean predicate `pred` with probability at most running with `onAccept₂`
plus `voleithKSBound d comLen (Q_leaf + m * (2 ^ d - 1)) (Q_FS + m) ε_rel`, provided
`onAccept₁` and `onAccept₂` agree whenever straight-line trace extraction satisfies `Rel`. -/
theorem toOuterMeasure_runWith_verifyGatedHandler_le {d sdLen comLen rowLen : ℕ}
    {Stmt Seed IV PreMsg Chal Wit Req Resp Log α : Type}
    [BEq (LeafQuery d Seed IV)] [LawfulBEq (LeafQuery d Seed IV)]
    [BEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [LawfulBEq (FSQuery d comLen rowLen Stmt IV PreMsg)]
    [DecidableEq IV] [Fintype Chal] [Nonempty Chal]
    (expand : BitString sdLen → BitString rowLen) (decWit : BitString rowLen → Wit)
    (chalToIdx : Chal → Fin (2 ^ d)) (Rel : Stmt → Wit → Bool)
    (toStmt : Req → Stmt) (toProof : Req → VOLEITHProof d comLen rowLen Seed IV PreMsg)
    (checkRel : Stmt → (Fin d → BitString rowLen) → BitString rowLen → PreMsg → Chal → Bool)
    {ε_rel : ℝ≥0}
    (hSound : VOLEITHSoundnessError decWit chalToIdx Rel checkRel ε_rel)
    (onReject : Resp)
    (onAccept₁ : Req → Log → ProbComp (Resp × Log))
    (onAccept₂ : LeafTrace d sdLen comLen Seed IV → Req → Log → ProbComp (Resp × Log))
    (hAgree : ∀ tr req log,
      Rel (toStmt req) (extractWitnessFromTrace expand decWit tr (toProof req)) = true →
      onAccept₁ req log = onAccept₂ tr req log)
    (log₀ : Log)
    (prog : ProbOracleComp ((fun _ : Req => Resp) ⊕ₒ
      VOLEITHROSpec d sdLen comLen rowLen Stmt Seed IV PreMsg Chal) α)
    {m Q_leaf Q_FS : ℕ}
    (hm : IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 1) (fun _ => 0))) prog m)
    (hleaf : IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 0) voleithLeafCost)) prog Q_leaf)
    (hfs : IsCostBounded (Sum.elim (fun _ => 0)
      (Sum.elim (fun _ => 0) voleithFSCost)) prog Q_FS)
    (pred : α × (VOLEITHTraceState d sdLen comLen rowLen Stmt Seed IV PreMsg Chal × Log) → Bool) :
    ((ProbOracleComp.runWith
        (verifyGatedHandler (comLen := comLen) (Seed := Seed) (IV := IV)
          expand chalToIdx toStmt toProof checkRel onReject (fun _ => onAccept₁))
        prog (([], []), log₀)).map pred) true ≤
      ((ProbOracleComp.runWith
          (verifyGatedHandler (comLen := comLen) (Seed := Seed) (IV := IV)
            expand chalToIdx toStmt toProof checkRel onReject onAccept₂)
          prog (([], []), log₀)).map pred) true +
        (voleithKSBound d comLen (Q_leaf + m * (2 ^ d - 1)) (Q_FS + m) ε_rel : ℝ≥0∞) := by
  let s₁ := verifyGatedStickyHandler (comLen := comLen) (Seed := Seed) (IV := IV)
    expand decWit chalToIdx Rel toStmt toProof checkRel onReject (fun _ => onAccept₁)
  let s₂ := verifyGatedStickyHandler (comLen := comLen) (Seed := Seed) (IV := IV)
    expand decWit chalToIdx Rel toStmt toProof checkRel onReject onAccept₂
  have heq₁ :
      ((ProbOracleComp.runWith
          (verifyGatedHandler (comLen := comLen) (Seed := Seed) (IV := IV)
            expand chalToIdx toStmt toProof checkRel onReject (fun _ => onAccept₁))
          prog (([], []), log₀)).map pred) =
        ((ProbOracleComp.runWith s₁ prog ((([], []), log₀), false)).map
          fun x => pred (x.1, x.2.1)) := by
    rw [← ProbOracleComp.runWith_map_state _ _ Prod.fst
      (verifyGatedStickyHandler_map_forget expand decWit chalToIdx Rel toStmt toProof checkRel
        onReject (fun _ => onAccept₁))
      prog ((([], []), log₀), false), PMF.map_comp]
    rfl
  have heq₂ :
      ((ProbOracleComp.runWith
          (verifyGatedHandler (comLen := comLen) (Seed := Seed) (IV := IV)
            expand chalToIdx toStmt toProof checkRel onReject onAccept₂)
          prog (([], []), log₀)).map pred) =
        ((ProbOracleComp.runWith s₂ prog ((([], []), log₀), false)).map
          fun x => pred (x.1, x.2.1)) := by
    rw [← ProbOracleComp.runWith_map_state _ _ Prod.fst
      (verifyGatedStickyHandler_map_forget expand decWit chalToIdx Rel toStmt toProof checkRel
        onReject onAccept₂)
      prog ((([], []), log₀), false), PMF.map_comp]
    rfl
  rw [heq₁, heq₂]
  exact (ProbOracleComp.IdenticalUntilBad.bind_apply_le
    (verifyGatedSticky_identicalUntilBad expand decWit chalToIdx Rel toStmt toProof checkRel
      onReject (fun _ => onAccept₁) onAccept₂ hAgree)
    prog ((([], []), log₀), false) (fun x => PMF.pure (pred (x.1, x.2.1))) true).trans
    (add_le_add_right
      (verifyGatedSticky_bad_le expand decWit chalToIdx Rel toStmt toProof checkRel hSound
        onReject onAccept₁ log₀ prog hm hleaf hfs) _)

end VerifyGatedBridge

end Cslib.Crypto.Protocols.VOLE
