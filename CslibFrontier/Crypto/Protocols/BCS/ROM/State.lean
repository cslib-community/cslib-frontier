/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.BCS.ROM.Extract
public import CslibFrontier.Crypto.Protocols.BCS.ROM.Protocol
import Mathlib.Data.List.OfFn

/-!
# Two-channel list-trace ROM state and adaptive good-state invariant for BCS

Defines the two-channel association-list state `BCSTraceState`, the memoizing random-oracle handler
`bcsMemoize`, recorded Fiat–Shamir chains (`ValidFSChain`), partial IOP transcript extraction
(`bcsExtractTranscript`), and the adaptive good-state invariant `BCSGoodState` combining
`TraceCollisionFree` on the Merkle trace with `BCSChainDoomed` on all recorded Fiat–Shamir chains of
length at most `r` ([BenSassonChiesaSpooner2016]; [ChiesaYogev2024], Chapters 25–26 and 31).

## Main definitions

* `Cslib.Crypto.Protocols.BCS.BCSTraceState`, `Cslib.Crypto.Protocols.BCS.bcsMemoize`: two-channel
  association-list trace state and memoizing random-oracle handler.
* `Cslib.Crypto.Protocols.BCS.ValidFSChain`, `Cslib.Crypto.Protocols.BCS.bcsExtractTranscript`,
  `Cslib.Crypto.Protocols.BCS.BCSChainDoomed`, `Cslib.Crypto.Protocols.BCS.BCSGoodState`: recorded
  Fiat–Shamir chain predicate, straight-line partial IOP transcript reconstruction, and combined
  adaptive ROM good-state invariant.

## Main results

* `Cslib.Crypto.Protocols.BCS.bcsExtractTranscript_append_singleton`,
  `Cslib.Crypto.Protocols.BCS.bcsExtractTranscript_ofFn`,
  `Cslib.Crypto.Protocols.BCS.bcsExtractTranscript_cons_of_ne`: structural and non-inverting Merkle
  trace-extension lemmas for `bcsExtractTranscript`.
* `Cslib.Crypto.Protocols.BCS.bcsGoodState_nil`: the empty two-channel trace `([], [])` satisfies
  `BCSGoodState` whenever every target statement starts in `doomed` on the empty transcript.

## References

* [E. Ben-Sasson, A. Chiesa, N. Spooner, *Interactive Oracle Proofs*][BenSassonChiesaSpooner2016]
* [A. Chiesa, E. Yogev, *Building Cryptographic Proofs from Hash Functions*][ChiesaYogev2024],
  Chapters 18, 25, 26, and 31.
-/

public section

namespace Cslib.Crypto.Protocols.BCS

open Cslib.Crypto Turing.MultiTapeTM Cslib.Probability Cslib.OracleComp

/-- List-cache state for the two-channel BCS random oracle: a Merkle hash trace `st.1` and a
transcript-chained Fiat–Shamir trace `st.2`. -/
abbrev BCSTraceState (Stmt Chal : Type) : Type :=
  List (List Bool × List Bool) × List (BCSFSQuery Stmt Chal × Chal)

/-- Two-channel association-list handler implementing
`RandomOracle.answer (bcsOracleDist Stmt Chal σ)`: Merkle queries are memoized in the first trace
and Fiat–Shamir queries in the second. -/
noncomputable abbrev bcsMemoize {Stmt Chal : Type} [BEq Stmt] [BEq Chal]
    [Fintype Chal] [Nonempty Chal] (σ : ℕ) :
    (q : List Bool ⊕ BCSFSQuery Stmt Chal) →
      StateT (BCSTraceState Stmt Chal) PMF (BCSROMSpec Stmt Chal q) :=
  RandomOracle.memoizeSum (fun _ : List Bool => BitString.uniformList σ)
    (fun _ : BCSFSQuery Stmt Chal => PMF.uniformOfFintype Chal)

/-- A pair `(rts, chals)` of Merkle roots and challenges forms a valid recorded Fiat–Shamir chain
for statement `x` in `tr_FS` if `rts` and `chals` have equal length and, at every round index
`i < rts.length`, the transcript-chained query `(x, rts.take (i + 1), chals.take i)` is recorded in
`tr_FS` with answer `chals[i]`. -/
@[expose] def ValidFSChain {Stmt Chal : Type} (tr_FS : List (BCSFSQuery Stmt Chal × Chal))
    (x : Stmt) (rts : List (List Bool)) (chals : List Chal) : Prop :=
  ∃ hlen : rts.length = chals.length,
    ∀ (i : ℕ) (hi : i < rts.length),
      ((x, rts.take (i + 1), chals.take i), chals[i]'(hlen ▸ hi)) ∈ tr_FS

/-- Extract the partial IOP transcript `[(π_0, c_0), ..., (π_{k-1}, c_{k-1})]` associated with a
root prefix `rts` and challenge prefix `chals` from Merkle trace `tr_MT`. -/
@[expose] def bcsExtractTranscript {Sym Chal : Type} (decSym : List Bool → Sym)
    (defaultSym : Sym) (d : ℕ) (tr_MT : List (List Bool × List Bool))
    (rts : List (List Bool)) (chals : List Chal) : List (OracleTable d Sym × Chal) :=
  (rts.zip chals).map fun (rt, c) => (bcsExtractTable decSym defaultSym tr_MT d rt, c)

@[simp]
theorem bcsExtractTranscript_nil_left {Sym Chal : Type} (decSym : List Bool → Sym)
    (defaultSym : Sym) (d : ℕ) (tr_MT : List (List Bool × List Bool)) (chals : List Chal) :
    bcsExtractTranscript decSym defaultSym d tr_MT [] chals = [] :=
  rfl

theorem bcsExtractTranscript_append_singleton {Sym Chal : Type} (decSym : List Bool → Sym)
    (defaultSym : Sym) (d : ℕ) (tr_MT : List (List Bool × List Bool))
    {rts : List (List Bool)} {chals : List Chal} (hlen : rts.length = chals.length)
    (rt : List Bool) (c : Chal) :
    bcsExtractTranscript decSym defaultSym d tr_MT (rts ++ [rt]) (chals ++ [c]) =
      bcsExtractTranscript decSym defaultSym d tr_MT rts chals ++
        [(bcsExtractTable decSym defaultSym tr_MT d rt, c)] := by
  simp only [bcsExtractTranscript, List.zip_append hlen, List.zip_cons_cons, List.zip_nil_left,
    List.map_append, List.map_cons, List.map_nil]

theorem bcsExtractTranscript_ofFn {r d : ℕ} {Sym Chal : Type} (decSym : List Bool → Sym)
    (defaultSym : Sym) (tr_MT : List (List Bool × List Bool))
    (roots : Fin r → List Bool) (chals : Fin r → Chal) :
    bcsExtractTranscript decSym defaultSym d tr_MT (List.ofFn roots) (List.ofFn chals) =
      List.ofFn fun j : Fin r =>
        (bcsExtractOracles decSym defaultSym tr_MT d roots j, chals j) := by
  refine List.ext_getElem (by simp [bcsExtractTranscript]) fun k hk₁ hk₂ => ?_
  simp only [List.length_ofFn] at hk₂
  simp [bcsExtractTranscript, bcsExtractOracles]

theorem bcsExtractTranscript_cons_of_ne {Sym Chal : Type} (decSym : List Bool → Sym)
    (defaultSym : Sym) (d : ℕ) (tr_MT : List (List Bool × List Bool)) (q : List Bool)
    {ans : List Bool} {rts : List (List Bool)} (chals : List Chal)
    (hrts : ∀ rt ∈ rts, ans ≠ rt)
    (hchildren : ∀ p ∈ tr_MT, ans ≠ unframe p.1 ∧ ans ≠ dropFrame p.1) :
    bcsExtractTranscript decSym defaultSym d ((q, ans) :: tr_MT) rts chals =
      bcsExtractTranscript decSym defaultSym d tr_MT rts chals :=
  List.map_congr_left fun ⟨rt, _⟩ hmem =>
    congrArg (·, _) (bcsExtractTable_cons_of_ne decSym defaultSym tr_MT q
      (hrts rt (List.of_mem_zip hmem).1) hchildren)

/-- Every valid recorded Fiat–Shamir chain `(rts, chals)` of length `≤ r` for a statement `x ∈ S`
maps under `bcsExtractTranscript` to a doomed IOP transcript prefix. -/
@[expose] def BCSChainDoomed (r d : ℕ) {Stmt Sym Chal : Type} (S : Set Stmt)
    (doomed : Stmt → List (OracleTable d Sym × Chal) → Prop)
    (decSym : List Bool → Sym) (defaultSym : Sym)
    (tr_MT : List (List Bool × List Bool))
    (tr_FS : List (BCSFSQuery Stmt Chal × Chal)) : Prop :=
  ∀ x ∈ S, ∀ rts chals, rts.length ≤ r →
    ValidFSChain tr_FS x rts chals →
      doomed x (bcsExtractTranscript decSym defaultSym d tr_MT rts chals)

/-- Combined good-state invariant of the two-channel BCS random-oracle state `(tr_MT, tr_FS)`:
the Merkle trace `tr_MT` is collision-free and every valid recorded Fiat–Shamir chain of length
`≤ r` on `S` maps to a doomed IOP transcript prefix. -/
@[expose] def BCSGoodState (r d : ℕ) {Stmt Sym Chal : Type} (S : Set Stmt)
    (doomed : Stmt → List (OracleTable d Sym × Chal) → Prop)
    (decSym : List Bool → Sym) (defaultSym : Sym)
    (st : BCSTraceState Stmt Chal) : Prop :=
  TraceCollisionFree st.1 ∧ BCSChainDoomed r d S doomed decSym defaultSym st.1 st.2

theorem bcsGoodState_nil (r d : ℕ) {Stmt Sym Chal : Type} {S : Set Stmt}
    {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    (hinit : ∀ x ∈ S, doomed x [])
    (decSym : List Bool → Sym) (defaultSym : Sym) :
    BCSGoodState (Chal := Chal) r d S doomed decSym defaultSym ([], []) := by
  refine ⟨traceCollisionFree_nil, fun x hx rts chals _ ⟨hlen, hsteps⟩ => ?_⟩
  cases rts with
  | nil =>
    simpa only [bcsExtractTranscript_nil_left] using hinit x hx
  | cons rt rest =>
    exact False.elim (List.not_mem_nil (hsteps 0 (Nat.zero_lt_succ _)))


end Cslib.Crypto.Protocols.BCS
