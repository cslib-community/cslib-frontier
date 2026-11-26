/-
Copyright (c) 2026 Samuel Schlesinger, Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.VOLE.ROExtractor
import CslibFrontier.Languages.Probabilistic.Oracle.RunState
import CslibFrontier.Languages.Probabilistic.QueryCount.Sum
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Support
import CslibFrontier.Probability.PMF.Uniform

/-!
# Separation of PRG-based leaf commitments from plain-ROM leaf extraction

This module formalizes separation witnesses explaining why local PRG-based leaf commitments
(`leaf_hash::aes_ctr`, as used in [VoleMole2026], `src/act/issue.hpp:121`, `src/act/spend.hpp:289`,
and analyzed in [BaumEtAl2026FAESTer]) do not admit a plain-ROM `H_leaf` query-log witness
extractor:

* **Zero `H_leaf` query budget (`prgLeafProver`)**: a local PRG prover queries only `H_FS`, leaving
  `tr_leaf = []` (`prgLeafGame_leafTrace_eq_nil`), yet passes `prgLeafVerify` with probability `1`
  (`prgLeafGame_eq_pure_true`), so `extractWitnessFromTrace` recovers only `decWit prf.dCorr`
  (`extractWitnessFromTrace_nil`).
* **Query-log separation (`exists_valid_prgLeaf_queryLog_fails_Rel_eq_one`)**: any statement- and
  proof-less leaf-query-log extractor `extLog : LeafTrace → Option Wit` fails `Rel` with
  probability `1` on at least one of two disjoint-witness valid statements (this extractor class
  excludes `extractWitnessFromTrace`, which takes `(tr, prf)` and is covered by the proof-only
  separation below).
* **Deterministic preimage-table separation (`prgLeaf_preimage_extractor_fails`)**: conditional on
  colliding PRG leaf commitments (`hComEq`) with matching corrected masks (`hdCorrEq`) across two
  disjoint-witness statements and an injective witness encoding `encWit`, the seed vectors must
  differ (`keys₀ ≠ keys₁`), and every deterministic preimage-table seed extractor
  `extPre : coms → iv → idx → Seed` fails `Rel` with probability `1`.
* **Proof-only separation (`exists_valid_prgLeaf_proofOnly_extract_fails_ge`)**: conditional on
  two disjoint-witness valid pairs whose proofs collide at some challenge `deltaStar`, any unbounded
  proof-only extractor `ext : LeafTrace → VOLEITHProof → Option Wit` omitting `stmt` fails `Rel`
  with probability at least `1 / |Chal|` for arbitrary `d : ℕ` (with `d ≥ 1` giving non-degenerate
  `2 ^ d - 1 ≥ 1` opened leaves).

## Main definitions

* `prgLeafOpenRows`, `prgLeafVerify`, `prgLeafProver`, `prgLeafGame`, `prgLeafProofOfDelta`: local
  deterministic PRG leaf commitment (`leaf_hash::aes_ctr`-style) verifier, prover, and
  per-challenge proof formula.

## Main results

* `prgLeafProver_leafCost_zero`, `prgLeafGame_leafTrace_eq_nil`, `prgLeafGame_eq_pure_true`: zero
  `H_leaf` queries and honest completeness for PRG-leaf proofs.
* `extractWitnessFromTrace_nil`: `extractWitnessFromTrace` reduces to `decWit prf.dCorr` on empty
  leaf traces.
* `exists_valid_prgLeaf_queryLog_fails_Rel_eq_one`: query-log extractor separation
  (probability `1`).
* `prgLeaf_preimage_extractor_fails`: conditional preimage-table extractor separation under
  colliding PRG commitments (probability `1`).
* `exists_valid_prgLeaf_proofOnly_extract_fails_ge`: conditional proof-only extractor separation for
  arbitrary `d : ℕ` (probability `≥ 1 / |Chal|`).

## Scope and gaps

* Conditional separation step toward #7068 (#4987): demonstrates structural obstructions for
  plain-ROM `H_leaf`-trace, preimage-table, and statement-less extractors on `prgLeaf`
  instantiations. Full almost-injective PRG / post-challenge equivocation reductions
  ([BaumEtAl2026FAESTer], Definition 27, pp. 17–18, and Lemma 32, pp. 25–26) for unbounded
  extractors that also inspect `stmt` remain open under #7068 (#4987).

## References

* [C. Baum et al., *Shorter, Tighter, FAESTer: Optimizations and Improved (QROM) Analysis for
  VOLE-in-the-Head Signatures* (ePrint 2026/164)][BaumEtAl2026FAESTer], Section 3 (Definition 27,
  pp. 17–18) and Section 3.3 (Lemmas 32–33, pp. 25–26).
* [C. Patton, T. Zhang, *vole-mole* (commit `87af6871f`)][VoleMole2026], `src/act/issue.hpp:121`,
  `src/act/spend.hpp:289`, `src/ihat/circuit.hpp:33`, `src/pomfrit/redeem.hpp:75`.
-/

public section

namespace Cslib.Crypto.Protocols.VOLE

open Cslib Cslib.Probability Cslib.OracleComp
open Cslib.Crypto.FAEST
open scoped ENNReal NNReal
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
  simpa only [Nat.add_zero] using
    (IsCostBounded.liftRight
      (IsCostBounded.liftRight_of_cost_inr_eq_zero (fun _ => rfl) _)
      (fun _ => le_rfl)).bind fun _ => IsCostBounded.pure _ 0

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
    RandomOracle.memoizeSum_inr, Cslib.memoize_of_none _ _ _ rfl]
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, ProbOracleComp.runWith_pure,
    PMF.bind_bind, PMF.pure_bind, PMF.map, Function.comp_def]
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
    RandomOracle.memoizeSum_inr, Cslib.memoize_of_some _ _ _ delta (by simp)]
  simp only [PMF.monad_pure_eq_pure, PMF.map, PMF.pure_bind, Function.comp_def]
  have hne_chal {vIdx : Fin (2 ^ d)} (hv : vIdx ≠ 0) :
      FAEST.xorIndex vIdx (chalToIdx delta) ≠ chalToIdx delta := fun h =>
    hv (Fin.ext (by
      simpa [FAEST.xorIndex, Nat.xor_assoc, Nat.xor_self] using
        congrArg (fun x : Fin (2 ^ d) => x.val ^^^ (chalToIdx delta).val) h))
  have hopen : ∀ vIdx : Fin (2 ^ d), vIdx = 0 ∨
      (prgLeaf (prf.openKeys (FAEST.xorIndex vIdx (chalToIdx delta))) prf.iv
        (FAEST.xorIndex vIdx (chalToIdx delta))).com =
        prf.coms (FAEST.xorIndex vIdx (chalToIdx delta)) := fun vIdx =>
    (eq_or_ne vIdx 0).imp_right fun hv => by simp [prf, prgLeafProofOfDelta, hne_chal hv]
  have hrows : prgLeafOpenRows expand prgLeaf prf.iv prf.openKeys prf.coms (chalToIdx delta) =
      some (FAEST.verifierRows (fun idx => expand (prgLeaf (keys idx) iv idx).seedOut)
        (chalToIdx delta)) := by
    unfold prgLeafOpenRows
    simp only [hopen, forall_const, ite_true]
    congr 1
    funext vIdx
    by_cases hv : vIdx = 0 <;>
      simp [FAEST.verifierRows, hv, prf, prgLeafProofOfDelta, hne_chal]
  rw [hrows]
  simp only [ProbOracleComp.runWith_pure,
    funext (FAEST.convertExpandedRows_correlation _ (chalToIdx delta))]
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
  rw [prgLeafGame, ProbOracleComp.runWith_bind, prgLeafProver_runWith_eq_map,
    PMF.bind_map, PMF.map_bind]
  simp_rw [Function.comp_apply, prgLeafVerify_runWith_of_delta expand prgLeaf encWit chalToIdx
    mkPreMsg checkRel defaultSeed iv keys stmt w hRel, PMF.pure_map]
  exact PMF.bind_const _ _

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
  rw [(PMF.map_eq_pure_iff (b := true)).mpr]
  · simp
  · rintro ⟨b, st⟩ hsupp
    have htr := prgLeafGame_leafTrace_eq_nil expand prgLeaf encWit chalToIdx mkPreMsg
      checkRel defaultSeed iv keys stmt w hRel hsupp
    have hb : b ∈ ((ProbOracleComp.runWith voleithMemoize
        (prgLeafGame expand prgLeaf encWit chalToIdx mkPreMsg checkRel defaultSeed iv keys stmt w)
        ([], [])).map Prod.fst).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨(b, st), hsupp, rfl⟩
    rw [prgLeafGame_eq_pure_true expand prgLeaf encWit chalToIdx mkPreMsg checkRel defaultSeed iv
      keys stmt w hRel, PMF.support_pure, Set.mem_singleton_iff] at hb
    simpa only [htr, hb, true_and, decide_eq_true_eq] using hbad

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
  have hkeys : (fun idx => if idx = chalToIdx delta then defaultSeed else keys₀ idx) =
      fun idx => if idx = chalToIdx delta then defaultSeed else keys₁ idx :=
    funext fun idx => by by_cases heq : idx = chalToIdx delta <;> simp [heq, hopen idx]
  simp only [prgLeafProofOfDelta]
  rw [funext hcom, hpre, hdCorr, hkeys]

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
  rw [prgLeafProver_then_verify_map expand prgLeaf encWit chalToIdx mkPreMsg checkRel
    defaultSeed iv keys stmt w hRel (fun ok prf _ =>
      let wExt := decWit (prf.dCorr +
        (FAEST.convertExpandedRows d
          (fun idx => expand (prgLeaf (extPre prf.coms prf.iv idx) prf.iv idx).seedOut)).u)
      decide (ok = true ∧ Rel stmt wExt = false))]
  simp only [prgLeafProofOfDelta, true_and, hExtFail, decide_true]
  change ((PMF.uniformOfFintype Chal).map (Function.const Chal true)).toOuterMeasure {true} = 1
  simp [PMF.map_const]


/-- Conditional step toward a pre-challenge preimage-table separation (#7068, #4987), not the
cited equivocation result: conditional on two valid executions `(stmt₀, w₀, keys₀)` and
`(stmt₁, w₁, keys₁)` with disjoint `Rel`-witness sets (`hDisj`), an injective witness encoding
`encWit` (`hEncInj`), identical PRG commitments (`hComEq`), and colliding corrected masks
`d_corr` (`hdCorrEq`), the key vectors must differ (`keys₀ ≠ keys₁`, forcing a PRG commitment
collision; unsatisfiable for any injective `prgLeaf`) and every deterministic preimage-table seed
extractor `extPre : coms → iv → idx → Seed` fails `Rel` with probability `1` on at least one of
the two executions. Full post-challenge equivocation reductions ([BaumEtAl2026FAESTer],
Definition 27, pp. 17–18, and Lemma 32, pp. 25–26) for extractors with `stmt` remain open under
#7068 (#4987). -/
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
    (hEncInj : Function.Injective encWit)
    (hRel₀ : ∀ (pCols : Fin d → BitString rowLen) (u : BitString rowLen) (delta : Chal),
      checkRel stmt₀
        (fun j => pCols j + fun k => (BitString.equivFin d).symm (chalToIdx delta) j * u k)
        (encWit w₀ + u) (mkPreMsg pCols u (encWit w₀ + u)) delta = true)
    (hRel₁ : ∀ (pCols : Fin d → BitString rowLen) (u : BitString rowLen) (delta : Chal),
      checkRel stmt₁
        (fun j => pCols j + fun k => (BitString.equivFin d).symm (chalToIdx delta) j * u k)
        (encWit w₁ + u) (mkPreMsg pCols u (encWit w₁ + u)) delta = true)
    (hComEq : ∀ idx, (prgLeaf (keys₀ idx) iv idx).com = (prgLeaf (keys₁ idx) iv idx).com)
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
  have hkeys_ne : keys₀ ≠ keys₁ := by
    rintro rfl
    exact hDisj w₀ ⟨hValid₀, hEncInj (add_right_cancel hdCorrEq) ▸ hValid₁⟩
  refine ⟨hkeys_ne, fun extPre => ?_⟩
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
    change Rel stmt₁ (decWit ((encWit w₁ +
      (FAEST.convertExpandedRows d (fun idx => expand (prgLeaf (keys₁ idx) iv idx).seedOut)).u) +
      (FAEST.convertExpandedRows d
        (fun idx => expand (prgLeaf (extPre coms₁ iv idx) iv idx).seedOut)).u)) = false
    rw [← hdCorrEq, ← hcoms]
    exact Bool.eq_false_iff.mpr fun h1 => hDisj wExt ⟨h0, h1⟩
  · exact ⟨stmt₀, w₀, keys₀, prgLeaf_preimage_extractor_fails_of_not_rel expand prgLeaf encWit
      decWit chalToIdx mkPreMsg Rel checkRel extPre defaultSeed iv keys₀ stmt₀ w₀ hValid₀ hRel₀
      (Bool.eq_false_iff.mpr h0)⟩


/-- Conditional proof-only extraction separation step for arbitrary `d : ℕ` (#7068, #4987):
conditional on two valid pairs `(stmt₀, w₀, keys₀)` and `(stmt₁, w₁, keys₁)` with disjoint
`Rel`-witness sets (`hDisj`) that emit the same `VOLEITHProof` at some challenge `deltaStar : Chal`
(`hPrfEq`), any unbounded proof-only extractor `ext : LeafTrace → VOLEITHProof → Option Wit` (which
omits `stmt`) fails `Rel` with probability at least `1 / Fintype.card Chal` on at least one valid
pair. The bound holds for arbitrary `d : ℕ` (`d ≥ 1` opens `2 ^ d - 1 ≥ 1` commitments, as tested at
`d = 3`). (Unlike `prgLeaf_preimage_extractor_fails`, an extractor *with* `stmt` can switch on
`stmt`; omitting `stmt` leaves a colliding challenge indistinguishable.) -/
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
          refine (PMF.uniformOfFintype Chal).toOuterMeasure.mono (Set.singleton_subset_iff.mpr ?_)
          simp [hp, he]
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
