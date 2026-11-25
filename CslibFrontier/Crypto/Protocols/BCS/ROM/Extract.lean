/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.BCS.Basic
public import CslibFrontier.Crypto.Computational.MerkleTree.ROMExtract

/-!
# Straight-line multi-round oracle-table reconstruction for the BCS transform

Straight-line reconstruction of depth-`d` IOP oracle tables, witnesses, and Merkle hash collisions
from a recorded Merkle query-answer trace `tr_MT` for the multi-round Ben-Sasson–Chiesa–Spooner
(BCS) transformation ([BenSassonChiesaSpooner2016]; compare [ChiesaYogev2024], Chapter 18,
Construction 18.5.3 and Lemma 18.5.7, printed pp. 199 and 204–207, and Construction 26.1.3,
printed pp. 290–291).

## Main definitions

* `Cslib.Crypto.Protocols.BCS.bcsExtractTable`, `Cslib.Crypto.Protocols.BCS.bcsExtractOracles`,
  `Cslib.Crypto.Protocols.BCS.bcsExtractWitness`: straight-line reconstruction of a single round
  table, all `r` round tables, and a candidate IOP witness from a Merkle query trace `tr_MT`.
* `Cslib.Crypto.Protocols.BCS.BCSOpeningsQueriedInTrace`: predicate recording that every Merkle
  authentication path opened in a `BCSProof` has all of its hash steps present in `tr_MT`.
* `Cslib.Crypto.Protocols.BCS.bcsFindTraceConflict`,
  `Cslib.Crypto.Protocols.BCS.bcsExtractTraceCollision`: deterministic search for a conflicting
  BCS opening and extraction of an explicit Merkle hash collision from `tr_MT`.

## Main results

* `Cslib.Crypto.Protocols.BCS.bcsExtractTable_eq_of_merkleVerify`,
  `Cslib.Crypto.Protocols.BCS.iopVerify_bcsExtractOracles_of_bcsVerify`: on a collision-free trace
  covering all opened paths of an accepted BCS proof, `bcsExtractOracles` agrees with every opened
  symbol and is accepted by `iopVerify`.
* `Cslib.Crypto.Protocols.BCS.exists_collision_of_bcsVerify_of_iopVerify_eq_false`,
  `Cslib.Crypto.Protocols.BCS.bcs_trace_sound_or_collision`,
  `Cslib.Crypto.Protocols.BCS.isCollision_bcsExtractTraceCollision`: on a trace consistent with
  `H k` covering all opened paths of an accepted BCS proof, either `iopVerify` accepts
  `bcsExtractOracles` or `bcsExtractTraceCollision` deterministically outputs a collision for `H k`.
* `Cslib.Crypto.Protocols.BCS.bcsExtractTable_cons_of_ne`,
  `Cslib.Crypto.Protocols.BCS.bcsExtractOracles_cons_of_ne`: prepending a fresh Merkle query whose
  digest avoids target roots and existing child digests leaves straight-line extraction unchanged.

## References

* [E. Ben-Sasson, A. Chiesa, N. Spooner, *Interactive Oracle Proofs*][BenSassonChiesaSpooner2016]
* [A. Chiesa, E. Yogev, *Building Cryptographic Proofs from Hash Functions*][ChiesaYogev2024],
  Chapter 18 (Construction 18.5.3 and Lemma 18.5.7) and Chapter 26 (Construction 26.1.3).
-/

public section

namespace Cslib.Crypto.Protocols.BCS

open Cslib.Crypto Turing.MultiTapeTM

section Extract

variable {r d : ℕ} {Stmt Wit Sym Chal : Type}

/-- Straight-line extraction of a depth-`d` IOP oracle table over `Sym` committed under Merkle root
`rt` from a recorded Merkle hash trace `tr_MT`: decodes each leaf returned by
`extractLeafFromTrace` via `decSym`, defaulting to `defaultSym` on unqueried positions
([BenSassonChiesaSpooner2016]; [ChiesaYogev2024], Construction 18.5.3 and Lemma 18.5.7). -/
@[expose] def bcsExtractTable (decSym : List Bool → Sym) (defaultSym : Sym)
    (tr_MT : List (List Bool × List Bool)) (d : ℕ) (rt : List Bool) : OracleTable d Sym :=
  fun idx => match extractLeafFromTrace tr_MT d rt idx.val with
    | some bits => decSym bits
    | none => defaultSym

/-- Straight-line extraction of all `r` committed round oracle tables from a Merkle trace `tr_MT`
and root vector `roots : Fin r → List Bool`. -/
@[expose] def bcsExtractOracles (decSym : List Bool → Sym) (defaultSym : Sym)
    (tr_MT : List (List Bool × List Bool)) (d : ℕ) (roots : Fin r → List Bool) :
    Fin r → OracleTable d Sym :=
  fun j => bcsExtractTable decSym defaultSym tr_MT d (roots j)

/-- Straight-line BCS knowledge extractor: reconstructs the `r` committed IOP oracle tables from
`tr_MT` via `bcsExtractOracles` and applies the underlying straight-line IOP extractor `iopExtract`.
-/
@[expose] def bcsExtractWitness (iopExtract : Stmt → (Fin r → OracleTable d Sym) → Wit)
    (decSym : List Bool → Sym) (defaultSym : Sym)
    (tr_MT : List (List Bool × List Bool)) (x : Stmt) (roots : Fin r → List Bool) : Wit :=
  iopExtract x (bcsExtractOracles decSym defaultSym tr_MT d roots)

/-- Every Merkle opening `((j, idx), ⟨val, path⟩)` checked by `iop.queries x chals` against
`prf.openings` has all of its hash steps recorded in `tr_MT`. -/
@[expose] def BCSOpeningsQueriedInTrace (H : List Bool → List Bool → List Bool) (k : List Bool)
    (iop : PublicCoinIOP r d Stmt Wit Sym Chal) (encSym : Sym → List Bool)
    (tr_MT : List (List Bool × List Bool)) (x : Stmt) (chals : Fin r → Chal)
    (prf : BCSProof r Sym) : Prop :=
  ∀ j idx val path,
    ((j, idx), ⟨val, path⟩) ∈ (iop.queries x chals).zip prf.openings →
      PathQueriedInTrace H k tr_MT idx.val (encSym val) path

instance instDecidableBCSOpeningsQueriedInTrace (H : List Bool → List Bool → List Bool)
    (k : List Bool) (iop : PublicCoinIOP r d Stmt Wit Sym Chal) (encSym : Sym → List Bool)
    (tr_MT : List (List Bool × List Bool)) (x : Stmt) (chals : Fin r → Chal)
    (prf : BCSProof r Sym) :
    Decidable (BCSOpeningsQueriedInTrace H k iop encSym tr_MT x chals prf) :=
  decidable_of_iff
    (∀ e ∈ (iop.queries x chals).zip prf.openings,
      match e with
      | ((_, idx), ⟨val, path⟩) => PathQueriedInTrace H k tr_MT idx.val (encSym val) path)
    ⟨fun h j idx val path hmem => h ((j, idx), ⟨val, path⟩) hmem,
     fun h ⟨⟨j, idx⟩, ⟨val, path⟩⟩ hmem => h j idx val path hmem⟩

/-- If `tr_MT` is collision-free and records the authentication path of an opening `(val, path)` at
`idx` accepted by `merkleVerify`, then `bcsExtractTable` recovers `val`. -/
theorem bcsExtractTable_eq_of_merkleVerify {H : List Bool → List Bool → List Bool} {k : List Bool}
    {encSym : Sym → List Bool} {decSym : List Bool → Sym}
    (hdec : Function.LeftInverse decSym encSym) (defaultSym : Sym)
    {tr_MT : List (List Bool × List Bool)} {rt : List Bool} {idx : Fin (2 ^ d)} {val : Sym}
    {path : List (List Bool)} (hfree : TraceCollisionFree tr_MT)
    (hpath : PathQueriedInTrace H k tr_MT idx.val (encSym val) path)
    (hver : merkleVerify H k d rt idx.val (encSym val) path = true) :
    bcsExtractTable decSym defaultSym tr_MT d rt idx = val := by
  simp only [bcsExtractTable, extractLeafFromTrace_eq_some_of_merkleVerify hfree hpath hver,
    hdec val]

/-- **Fixed-trace consistency of `bcsExtractOracles`** ([ChiesaYogev2024], Lemma 18.5.7): if
`tr_MT` is collision-free and records all hash steps of the openings in `prf`, then whenever
`bcsVerify` accepts `prf`, `iopVerify` accepts the extracted oracle tables `bcsExtractOracles` at
`bcsChallenge hFS x prf.roots`. -/
theorem iopVerify_bcsExtractOracles_of_bcsVerify {H : List Bool → List Bool → List Bool}
    {k : List Bool} {iop : PublicCoinIOP r d Stmt Wit Sym Chal}
    {encSym : Sym → List Bool} {decSym : List Bool → Sym}
    (hdec : Function.LeftInverse decSym encSym) (defaultSym : Sym)
    {hFS : Stmt → List (List Bool) → Chal} {tr_MT : List (List Bool × List Bool)}
    {x : Stmt} {prf : BCSProof r Sym}
    (hfree : TraceCollisionFree tr_MT)
    (hpaths : BCSOpeningsQueriedInTrace H k iop encSym tr_MT x (bcsChallenge hFS x prf.roots) prf)
    (hver : bcsVerify iop H k encSym hFS x prf = true) :
    iopVerify iop x (bcsChallenge hFS x prf.roots)
      (bcsExtractOracles decSym defaultSym tr_MT d prf.roots) = true :=
  iopVerify_eq_true_of_bcsVerify_of_openings_eq hver fun j idx val path hmem =>
    (bcsExtractTable_eq_of_merkleVerify hdec defaultSym hfree
      (hpaths j idx val path hmem) (verify_of_bcsVerify hver hmem)).symm

/-- **Dual collision extraction for `bcsExtractOracles`**: if `tr_MT` is consistent with `H k` and
records all opened paths of a proof accepted by `bcsVerify`, yet `iopVerify` rejects
`bcsExtractOracles`, then `tr_MT` contains two distinct queries with the same hash under `H k`. -/
theorem exists_collision_of_bcsVerify_of_iopVerify_eq_false
    {H : List Bool → List Bool → List Bool} {k : List Bool}
    {iop : PublicCoinIOP r d Stmt Wit Sym Chal}
    {encSym : Sym → List Bool} {decSym : List Bool → Sym}
    (hdec : Function.LeftInverse decSym encSym) (defaultSym : Sym)
    {hFS : Stmt → List (List Bool) → Chal} {tr_MT : List (List Bool × List Bool)}
    {x : Stmt} {prf : BCSProof r Sym}
    (hcons : TraceConsistentWith (H k) tr_MT)
    (hpaths : BCSOpeningsQueriedInTrace H k iop encSym tr_MT x (bcsChallenge hFS x prf.roots) prf)
    (hver : bcsVerify iop H k encSym hFS x prf = true)
    (hrej : iopVerify iop x (bcsChallenge hFS x prf.roots)
      (bcsExtractOracles decSym defaultSym tr_MT d prf.roots) = false) :
    ∃ q₁ ∈ tr_MT.map Prod.fst, ∃ q₂ ∈ tr_MT.map Prod.fst, q₁ ≠ q₂ ∧ H k q₁ = H k q₂ := by
  by_contra! hno
  refine Bool.false_ne_true (hrej.symm.trans
    (iopVerify_eq_true_of_bcsVerify_of_openings_eq hver fun j idx val path hmem => ?_))
  by_contra hne
  obtain ⟨q₁, hq₁, q₂, hq₂, hneq, heq⟩ := exists_collision_of_extractLeafFromTrace_ne hcons
    (hpaths j idx val path hmem) (verify_of_bcsVerify hver hmem)
    fun h => hne (by simp [bcsExtractOracles, bcsExtractTable, h, hdec val])
  exact hno q₁ hq₁ q₂ hq₂ hneq heq

/-- Find the first query-opening pair `((j, idx), ⟨val, path⟩)` in a BCS proof where straight-line
Merkle leaf extraction `extractLeafFromTrace` disagrees with `some (encSym val)`. -/
@[expose] def bcsFindTraceConflict (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool) (hFS : Stmt → List (List Bool) → Chal)
    (tr_MT : List (List Bool × List Bool)) (x : Stmt) (prf : BCSProof r Sym) :
    Option ((Fin r × Fin (2 ^ d)) × MerkleOpening Sym) :=
  let chals := bcsChallenge hFS x prf.roots
  ((iop.queries x chals).zip prf.openings).find? fun ((j, idx), ⟨val, _⟩) =>
    extractLeafFromTrace tr_MT d (prf.roots j) idx.val != some (encSym val)

/-- **Deterministic trace collision extractor for the BCS transform**: find the first query
position where `prf` opens a symbol that disagrees with `extractLeafFromTrace tr_MT` and run
`extractTraceCollision` on that opening. -/
@[expose] def bcsExtractTraceCollision (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (H : List Bool → List Bool → List Bool) (k : List Bool) (encSym : Sym → List Bool)
    (hFS : Stmt → List (List Bool) → Chal) (tr_MT : List (List Bool × List Bool))
    (x : Stmt) (prf : BCSProof r Sym) : List Bool × List Bool :=
  match bcsFindTraceConflict iop encSym hFS tr_MT x prf with
  | none => ([], [])
  | some ((_, idx), ⟨val, path⟩) =>
    extractTraceCollision H k tr_MT idx.val (encSym val) path

/-- **Trace-extraction binding (`bcs_trace_sound_or_collision`)**: if `tr_MT` is consistent with
`H k` and records all opened authentication paths of an accepted BCS proof `prf`, then either the
IOP verifier accepts `bcsExtractOracles` at `bcsChallenge hFS x prf.roots`, or
`bcsExtractTraceCollision` deterministically extracts a hash collision for `H k`. -/
theorem bcs_trace_sound_or_collision
    {H : List Bool → List Bool → List Bool} {k : List Bool}
    {iop : PublicCoinIOP r d Stmt Wit Sym Chal}
    {encSym : Sym → List Bool} {decSym : List Bool → Sym}
    (hdec : Function.LeftInverse decSym encSym) (defaultSym : Sym)
    {hFS : Stmt → List (List Bool) → Chal} {tr_MT : List (List Bool × List Bool)}
    {x : Stmt} {prf : BCSProof r Sym}
    (hcons : TraceConsistentWith (H k) tr_MT)
    (hpaths : BCSOpeningsQueriedInTrace H k iop encSym tr_MT x (bcsChallenge hFS x prf.roots) prf)
    (hver : bcsVerify iop H k encSym hFS x prf = true) (n : ℕ) :
    iopVerify iop x (bcsChallenge hFS x prf.roots)
        (bcsExtractOracles decSym defaultSym tr_MT d prf.roots) = true ∨
      let col := bcsExtractTraceCollision iop H k encSym hFS tr_MT x prf
      isCollision H (fun _ _ => true) n k col.1 col.2 = true := by
  cases hfind : bcsFindTraceConflict iop encSym hFS tr_MT x prf with
  | some p =>
    rcases p with ⟨⟨j, idx⟩, ⟨val, path⟩⟩
    right
    have hmem := List.mem_of_find?_eq_some hfind
    simpa only [bcsExtractTraceCollision, hfind] using
      isCollision_extractTraceCollision hcons (hpaths j idx val path hmem)
        (verify_of_bcsVerify hver hmem)
        (by simpa only [bne_iff_ne, ne_eq] using List.find?_some hfind) n
  | none =>
    refine Or.inl <| iopVerify_eq_true_of_bcsVerify_of_openings_eq hver
      fun j idx val path hmem => ?_
    have hleaf : extractLeafFromTrace tr_MT d (prf.roots j) idx.val = some (encSym val) := by
      simpa using List.find?_eq_none.mp hfind ((j, idx), ⟨val, path⟩) hmem
    simp only [bcsExtractOracles, bcsExtractTable, hleaf, hdec val]

/-- If the IOP verifier rejects `bcsExtractOracles` on a consistent trace `tr_MT` covering all
opened paths of an accepted BCS proof `prf`, then `bcsExtractTraceCollision` deterministically
outputs a hash collision for `H k`. -/
theorem isCollision_bcsExtractTraceCollision
    {H : List Bool → List Bool → List Bool} {k : List Bool}
    {iop : PublicCoinIOP r d Stmt Wit Sym Chal}
    {encSym : Sym → List Bool} {decSym : List Bool → Sym}
    (hdec : Function.LeftInverse decSym encSym) (defaultSym : Sym)
    {hFS : Stmt → List (List Bool) → Chal} {tr_MT : List (List Bool × List Bool)}
    {x : Stmt} {prf : BCSProof r Sym}
    (hcons : TraceConsistentWith (H k) tr_MT)
    (hpaths : BCSOpeningsQueriedInTrace H k iop encSym tr_MT x (bcsChallenge hFS x prf.roots) prf)
    (hver : bcsVerify iop H k encSym hFS x prf = true)
    (hrej : iopVerify iop x (bcsChallenge hFS x prf.roots)
      (bcsExtractOracles decSym defaultSym tr_MT d prf.roots) = false) (n : ℕ) :
    let col := bcsExtractTraceCollision iop H k encSym hFS tr_MT x prf
    isCollision H (fun _ _ => true) n k col.1 col.2 = true :=
  (bcs_trace_sound_or_collision hdec defaultSym hcons hpaths hver n).resolve_left
    (by simp [hrej])

/-- Prepending `(q, ans)` to `tr_MT` leaves `bcsExtractTable` at `rt` unchanged whenever `ans ≠ rt`
and `ans` does not equal `unframe p.1` or `dropFrame p.1` for any `p ∈ tr_MT`. -/
theorem bcsExtractTable_cons_of_ne (decSym : List Bool → Sym) (defaultSym : Sym)
    (tr_MT : List (List Bool × List Bool)) (q : List Bool) {ans rt : List Bool}
    (hrt : ans ≠ rt) (hchildren : ∀ p ∈ tr_MT, ans ≠ unframe p.1 ∧ ans ≠ dropFrame p.1) :
    bcsExtractTable decSym defaultSym ((q, ans) :: tr_MT) d rt =
      bcsExtractTable decSym defaultSym tr_MT d rt := by
  funext idx
  simp only [bcsExtractTable, extractLeafFromTrace_cons_of_ne tr_MT q d idx.val hrt hchildren]

/-- Prepending `(q, ans)` to `tr_MT` leaves `bcsExtractOracles` on `roots` unchanged whenever `ans`
avoids all `roots j` and all left/right child digests of `tr_MT`. -/
theorem bcsExtractOracles_cons_of_ne (decSym : List Bool → Sym) (defaultSym : Sym)
    (tr_MT : List (List Bool × List Bool)) (q : List Bool) {ans : List Bool}
    {roots : Fin r → List Bool} (hroots : ∀ j : Fin r, ans ≠ roots j)
    (hchildren : ∀ p ∈ tr_MT, ans ≠ unframe p.1 ∧ ans ≠ dropFrame p.1) :
    bcsExtractOracles decSym defaultSym ((q, ans) :: tr_MT) d roots =
      bcsExtractOracles decSym defaultSym tr_MT d roots :=
  funext fun j => bcsExtractTable_cons_of_ne decSym defaultSym tr_MT q (hroots j) hchildren

end Extract

end Cslib.Crypto.Protocols.BCS
