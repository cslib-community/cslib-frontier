/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.BCS.Basic
public import CslibFrontier.Crypto.Computational.MerkleTree.Prog
public import CslibFrontier.Languages.Probabilistic.RandomOracle.Sum
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn

/-!
# Two-channel BCS random-oracle protocol, completeness, and RBR knowledge soundness

Defines the two-channel random-oracle interface `BCSROMSpec Stmt Chal := MerkleHashSpec ⊕ₒ
BCSFSSpec Stmt Chal`, the transcript-chained Fiat–Shamir bridge `chainedFS`, the oracle-program BCS
prover and verifier (`bcsProveROM`, `bcsVerifyROM`), perfect completeness in the lazy two-channel
random-oracle model (`bcsHonestROMGame_eq_pure_true`), per-channel query cost functions
(`bcsMTCost`, `bcsFSCost`), and the round-by-round IOP knowledge-soundness predicate
`IOPRoundByRoundKnowledgeSoundness` ([BenSassonChiesaSpooner2016]; compare [ChiesaYogev2024],
Construction 25.1.1, Remark 25.1.3, Chapter 26, and Chapter 31, Definition 31.1.6 and Theorem
31.3.1).

## Main definitions

* `Cslib.Crypto.Protocols.BCS.BCSFSQuery`, `Cslib.Crypto.Protocols.BCS.BCSFSSpec`,
  `Cslib.Crypto.Protocols.BCS.BCSROMSpec`, `Cslib.Crypto.Protocols.BCS.bcsOracle`,
  `Cslib.Crypto.Protocols.BCS.chainedFSChallenges`, `Cslib.Crypto.Protocols.BCS.chainedFS`:
  two-channel BCS random-oracle specification and transcript-chained Fiat–Shamir bridge.
* `Cslib.Crypto.Protocols.BCS.bcsChallengesProg`, `Cslib.Crypto.Protocols.BCS.bcsProveROM`,
  `Cslib.Crypto.Protocols.BCS.bcsVerifyOpeningsProg`, `Cslib.Crypto.Protocols.BCS.bcsVerifyROM`,
  `Cslib.Crypto.Protocols.BCS.bcsOracleDist`, `Cslib.Crypto.Protocols.BCS.bcsHonestROMProg`,
  `Cslib.Crypto.Protocols.BCS.bcsHonestROMGame`: oracle-program BCS prover, verifier, and honest
  lazy-ROM completeness game.
* `Cslib.Crypto.Protocols.BCS.IOPRoundByRoundKnowledgeSoundness`: round-by-round knowledge
  soundness of a `PublicCoinIOP` with a straight-line IOP extractor.
* `Cslib.Crypto.Protocols.BCS.bcsMTCost`, `Cslib.Crypto.Protocols.BCS.bcsFSCost`: per-call query
  costs on the Merkle and Fiat–Shamir channels.

## Main results

* `Cslib.Crypto.Protocols.BCS.evalPure_bcsChallengesProg`,
  `Cslib.Crypto.Protocols.BCS.evalPure_bcsProveROM`,
  `Cslib.Crypto.Protocols.BCS.evalPure_bcsVerifyOpeningsProg`,
  `Cslib.Crypto.Protocols.BCS.evalPure_bcsVerifyROM`,
  `Cslib.Crypto.Protocols.BCS.bcsVerifyROM_bcsProveROM_eq_true`,
  `Cslib.Crypto.Protocols.BCS.bcsHonestROMGame_eq_pure_true`: deterministic `OracleComp.evalPure`
  simulation against `chainedFS` and perfect completeness in the lazy two-channel ROM.
* `Cslib.Crypto.Protocols.BCS.IOPRoundByRoundKnowledgeSoundness.toRoundByRoundSoundness`,
  `Cslib.Crypto.Protocols.BCS.IOPRoundByRoundKnowledgeSoundness.rel_iopExtract_of_goodSteps`:
  reduction from round-by-round knowledge soundness to round-by-round soundness for the induced
  language and witness recovery along good challenge steps.

## References

* [E. Ben-Sasson, A. Chiesa, N. Spooner, *Interactive Oracle Proofs*][BenSassonChiesaSpooner2016]
* [A. Chiesa, E. Yogev, *Building Cryptographic Proofs from Hash Functions*][ChiesaYogev2024],
  Chapter 25 (Construction 25.1.1 and Remark 25.1.3) and Chapter 31 (Definition 31.1.6 and
  Theorem 31.3.1).
-/

public section

namespace Cslib.Crypto.Protocols.BCS

open Cslib.Crypto Turing.MultiTapeTM Cslib.Probability Cslib.OracleComp

/-- Query input to the transcript-chained BCS Fiat–Shamir oracle: statement `x`, root prefix `rts`
through the current round, and challenges `prevChals` from earlier rounds. -/
abbrev BCSFSQuery (Stmt Chal : Type) : Type :=
  Stmt × List (List Bool) × List Chal

/-- Oracle specification for the transcript-chained BCS Fiat–Shamir challenge oracle. -/
abbrev BCSFSSpec (Stmt Chal : Type) : OracleSpec (BCSFSQuery Stmt Chal) :=
  fun _ => Chal

/-- Combined two-channel random-oracle specification for the BCS transform: a Merkle hash oracle on
the left (`Sum.inl`) and a transcript-chained Fiat–Shamir challenge oracle on the right (`Sum.inr`).
-/
abbrev BCSROMSpec (Stmt Chal : Type) : OracleSpec (List Bool ⊕ BCSFSQuery Stmt Chal) :=
  MerkleHashSpec ⊕ₒ BCSFSSpec Stmt Chal

/-- Combine a deterministic Merkle hash `hTree` and a deterministic transcript-chained Fiat–Shamir
function `f` into a deterministic oracle for `BCSROMSpec Stmt Chal`. -/
abbrev bcsOracle {Stmt Chal : Type} (hTree : List Bool → List Bool)
    (f : BCSFSQuery Stmt Chal → Chal) :
    (q : List Bool ⊕ BCSFSQuery Stmt Chal) → BCSROMSpec Stmt Chal q :=
  OracleComp.sumPure (spec₁ := MerkleHashSpec) (spec₂ := BCSFSSpec Stmt Chal) hTree f

/-- Sequentially compute the transcript-chained Fiat–Shamir challenge list `[c_0, ..., c_{k-1}]`
associated with a Merkle root list `rts = [rt_0, ..., rt_{k-1}]` under `f`. -/
@[expose] def chainedFSChallenges {Stmt Chal : Type} (f : BCSFSQuery Stmt Chal → Chal)
    (x : Stmt) (rts : List (List Bool)) : List Chal :=
  (rts.foldl (fun (accRts, accChals) rt =>
    let rts' := accRts ++ [rt]
    (rts', accChals ++ [f (x, rts', accChals)])) ([], [])).2

/-- Deterministic bridge turning a transcript-chained Fiat–Shamir function
`f : Stmt × List (List Bool) × List Chal → Chal` into the root-prefix Fiat–Shamir interface
`Stmt → List (List Bool) → Chal` of `CslibFrontier/Crypto/Protocols/BCS/Basic.lean`. -/
@[expose] def chainedFS {Stmt Chal : Type} (f : BCSFSQuery Stmt Chal → Chal)
    (x : Stmt) (rts : List (List Bool)) : Chal :=
  f (x, rts, chainedFSChallenges f x rts.dropLast)

private theorem fst_foldl_chainedFSChallenges {Stmt Chal : Type}
    (f : BCSFSQuery Stmt Chal → Chal) (x : Stmt) (rts : List (List Bool))
    (initRts : List (List Bool)) (initChals : List Chal) :
    (rts.foldl (fun (accRts, accChals) rt =>
      let rts' := accRts ++ [rt]
      (rts', accChals ++ [f (x, rts', accChals)])) (initRts, initChals)).1 = initRts ++ rts := by
  induction rts generalizing initRts initChals with
  | nil => simp
  | cons rt rest ih =>
    simp only [List.foldl_cons, ih, List.append_assoc, List.singleton_append]

@[simp]
theorem chainedFSChallenges_nil {Stmt Chal : Type} (f : BCSFSQuery Stmt Chal → Chal) (x : Stmt) :
    chainedFSChallenges f x [] = [] :=
  rfl

theorem chainedFSChallenges_concat {Stmt Chal : Type} (f : BCSFSQuery Stmt Chal → Chal) (x : Stmt)
    (rts : List (List Bool)) (rt : List Bool) :
    chainedFSChallenges f x (rts ++ [rt]) =
      chainedFSChallenges f x rts ++ [chainedFS f x (rts ++ [rt])] := by
  unfold chainedFSChallenges chainedFS
  rw [List.foldl_concat, List.dropLast_concat]
  have h1 := fst_foldl_chainedFSChallenges f x rts [] []
  rw [List.nil_append] at h1
  exact congrArg (fun a => _ ++ [f (x, a ++ [rt], _)]) h1

private theorem rootPrefix_eq_take_append {r : ℕ} (roots : Fin r → List Bool) {m : ℕ}
    (hm : m + 1 ≤ r) :
    rootPrefix roots ⟨m, hm⟩ = (List.ofFn roots).take m ++ [roots ⟨m, hm⟩] := by
  rw [rootPrefix_eq_take_ofFn]
  have hlt : m < (List.ofFn roots).length := by simpa using hm
  simpa only [List.getElem_ofFn] using List.take_succ_eq_append_getElem hlt

/-- Structural round loop for `bcsChallengesProg`. -/
private def bcsChallengesAuxProg {r : ℕ} {Stmt Chal : Type} (x : Stmt)
    (roots : Fin r → List Bool) :
    (m : ℕ) → m ≤ r → OracleComp (BCSFSSpec Stmt Chal) (Fin m → Chal)
  | 0, _ => return Fin.elim0
  | m + 1, hm => do
    let prev ← bcsChallengesAuxProg x roots m (Nat.le_of_succ_le hm)
    let c ← OracleComp.query (spec := BCSFSSpec Stmt Chal)
      (x, rootPrefix roots ⟨m, hm⟩, List.ofFn prev)
    return Fin.snoc prev c

/-- Sequentially query the transcript-chained Fiat–Shamir oracle to derive all `r` round challenges
`(c_0, ..., c_{r-1})` from `(x, roots)`. -/
def bcsChallengesProg {r : ℕ} {Stmt Chal : Type} (x : Stmt)
    (roots : Fin r → List Bool) : OracleComp (BCSFSSpec Stmt Chal) (Fin r → Chal) :=
  bcsChallengesAuxProg x roots r le_rfl

private theorem snoc_eq_restrict {r m : ℕ} {α : Type} {f : Fin m → α} {a : α} {g : Fin r → α}
    (hm : m + 1 ≤ r)
    (hprev : ∀ i : Fin m, f i = g ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_of_succ_le hm)⟩)
    (hlast : a = g ⟨m, hm⟩) (i : Fin (m + 1)) :
    Fin.snoc (α := fun _ => α) f a i = g ⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩ :=
  Fin.lastCases (by simpa using hlast) (fun j => by simpa using hprev j) i

private theorem ofFn_snoc_chainedFS {r m : ℕ} {Stmt Chal : Type} (hm : m + 1 ≤ r)
    (f : BCSFSQuery Stmt Chal → Chal) (x : Stmt) (roots : Fin r → List Bool)
    {prev : Fin m → Chal} {c : Chal}
    (hprev : List.ofFn prev = chainedFSChallenges f x ((List.ofFn roots).take m))
    (hc : c = bcsChallenge (chainedFS f) x roots ⟨m, hm⟩) :
    List.ofFn (Fin.snoc prev c) = chainedFSChallenges f x ((List.ofFn roots).take (m + 1)) := by
  simp only [List.ofFn_succ_last, Fin.snoc_castSucc, Fin.snoc_last, hprev, hc, bcsChallenge]
  rw [rootPrefix_eq_take_append roots hm, ← chainedFSChallenges_concat,
    ← rootPrefix_eq_take_append roots hm, rootPrefix_eq_take_ofFn]

private theorem evalPure_bcsChallengesAuxProg {r : ℕ} {Stmt Chal : Type}
    (f : BCSFSQuery Stmt Chal → Chal) (x : Stmt) (roots : Fin r → List Bool) :
    ∀ (m : ℕ) (hm : m ≤ r),
      List.ofFn (OracleComp.evalPure f (bcsChallengesAuxProg x roots m hm)) =
        chainedFSChallenges f x ((List.ofFn roots).take m) ∧
      ∀ i : Fin m,
        OracleComp.evalPure f (bcsChallengesAuxProg x roots m hm) i =
          bcsChallenge (chainedFS f) x roots ⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩
  | 0, _ => ⟨by simp [bcsChallengesAuxProg], fun i => i.elim0⟩
  | m + 1, hm => by
    obtain ⟨hlist, hidx⟩ := evalPure_bcsChallengesAuxProg f x roots m (Nat.le_of_succ_le hm)
    simp only [bcsChallengesAuxProg, OracleComp.evalPure_bind, OracleComp.evalPure_query,
      OracleComp.evalPure_pure]
    have hc : f (x, rootPrefix roots ⟨m, hm⟩,
        List.ofFn (OracleComp.evalPure f (bcsChallengesAuxProg x roots m (Nat.le_of_succ_le hm)))) =
        bcsChallenge (chainedFS f) x roots ⟨m, hm⟩ := by
      rw [hlist, bcsChallenge, chainedFS, rootPrefix_eq_take_append roots hm, List.dropLast_concat]
    exact ⟨ofFn_snoc_chainedFS hm f x roots hlist hc, snoc_eq_restrict hm hidx hc⟩

@[simp]
theorem evalPure_bcsChallengesProg {r : ℕ} {Stmt Chal : Type}
    (f : BCSFSQuery Stmt Chal → Chal) (x : Stmt) (roots : Fin r → List Bool) :
    OracleComp.evalPure f (bcsChallengesProg x roots) =
      bcsChallenge (chainedFS f) x roots :=
  funext (evalPure_bcsChallengesAuxProg f x roots r le_rfl).2

section ROMProtocol

variable {r d : ℕ} {Stmt Wit Sym Chal : Type}

/-- Structural round loop for `bcsProveROM`: sequentially computes the first `m` IOP oracle tables,
commits to each with `merkleRootProg`, and derives each round's Fiat–Shamir challenge on the right
channel. -/
private def bcsProveRoundsProg (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool) (x : Stmt) (w : Wit) :
    (m : ℕ) → m ≤ r →
      OracleComp (BCSROMSpec Stmt Chal)
        ((Fin m → OracleTable d Sym) × (Fin m → List Bool) × (Fin m → Chal))
  | 0, _ => return (Fin.elim0, Fin.elim0, Fin.elim0)
  | m + 1, hm => do
    let (tables, roots, chals) ← bcsProveRoundsProg iop encSym x w m (Nat.le_of_succ_le hm)
    let π := iop.proveRound ⟨m, hm⟩ x w chals
    let rt ← OracleComp.liftLeft (spec₂ := BCSFSSpec Stmt Chal)
      (merkleRootProg (oracleLeaves encSym d π))
    let roots' : Fin (m + 1) → List Bool := Fin.snoc roots rt
    let c ← OracleComp.liftRight (spec₁ := MerkleHashSpec)
      (OracleComp.query (spec := BCSFSSpec Stmt Chal) (x, List.ofFn roots', List.ofFn chals))
    return (Fin.snoc tables π, roots', Fin.snoc chals c)

/-- **The BCS prover in the two-channel random-oracle model** (`bcsProveROM`): runs all `r`
commit-and-challenge rounds via `bcsProveRoundsProg` and opens every queried entry under
`merklePathProg` ([BenSassonChiesaSpooner2016]; compare [ChiesaYogev2024], Construction 25.1.1,
printed pp. 274–275). -/
def bcsProveROM (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool) (x : Stmt) (w : Wit) :
    OracleComp (BCSROMSpec Stmt Chal) (BCSProof r Sym) := do
  let (tables, roots, chals) ← bcsProveRoundsProg iop encSym x w r le_rfl
  let openings ← OracleComp.liftLeft (spec₂ := BCSFSSpec Stmt Chal)
    ((iop.queries x chals).mapM fun (j, idx) => do
      let path ← merklePathProg (oracleLeaves encSym d (tables j)) idx.val
      return ⟨tables j idx, path⟩)
  return { roots := roots, openings := openings }

/-- Verify all Merkle openings and the IOP decision predicate for a `BCSProof` given already
derived challenges `chals`. -/
@[expose] def bcsVerifyOpeningsProg (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool) (x : Stmt) (prf : BCSProof r Sym) (chals : Fin r → Chal) :
    OracleComp MerkleHashSpec Bool := do
  let qs := iop.queries x chals
  let checks ← (qs.zip prf.openings).mapM fun ((j, idx), ⟨val, path⟩) =>
    merkleVerifyProg d (prf.roots j) idx.val (encSym val) path
  return prf.openings.length == qs.length &&
    checks.all id &&
    iop.decide x chals (prf.openings.map MerkleOpening.leaf)

/-- **The BCS verifier in the two-channel random-oracle model** (`bcsVerifyROM`): re-derives all `r`
round challenges on the Fiat–Shamir channel via `bcsChallengesProg` and checks all Merkle openings
and `iop.decide` on the Merkle channel via `bcsVerifyOpeningsProg` ([BenSassonChiesaSpooner2016];
compare [ChiesaYogev2024], Construction 25.1.1, printed pp. 274–275). -/
@[expose] def bcsVerifyROM (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool) (x : Stmt) (prf : BCSProof r Sym) :
    OracleComp (BCSROMSpec Stmt Chal) Bool := do
  let chals ← OracleComp.liftRight (spec₁ := MerkleHashSpec) (bcsChallengesProg x prf.roots)
  OracleComp.liftLeft (spec₂ := BCSFSSpec Stmt Chal)
    (bcsVerifyOpeningsProg iop encSym x prf chals)

private theorem evalPure_bcsProveRoundsProg (hTree : List Bool → List Bool)
    (f : BCSFSQuery Stmt Chal → Chal) (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool) (x : Stmt) (w : Wit) :
    ∀ (m : ℕ) (hm : m ≤ r),
      let out := OracleComp.evalPure (bcsOracle hTree f)
        (bcsProveRoundsProg iop encSym x w m hm)
      let hTables := bcsHonestTables iop (fun _ => hTree) [] encSym (chainedFS f) x w
      let hRoots := bcsHonestRoots iop (fun _ => hTree) [] encSym (chainedFS f) x w
      let hChals := bcsHonestChallenges iop (fun _ => hTree) [] encSym (chainedFS f) x w
      (∀ i : Fin m, out.1 i = hTables ⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩) ∧
      (∀ i : Fin m, out.2.1 i = hRoots ⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩) ∧
      (∀ i : Fin m, out.2.2 i = hChals ⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩) ∧
      List.ofFn out.2.2 = chainedFSChallenges f x ((List.ofFn hRoots).take m)
  | 0, _ => ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      by simp [bcsProveRoundsProg]⟩
  | m + 1, hm => by
    obtain ⟨htab, hrt, hch, hchList⟩ :=
      evalPure_bcsProveRoundsProg hTree f iop encSym x w m (Nat.le_of_succ_le hm)
    rcases hp : OracleComp.evalPure (bcsOracle hTree f)
      (bcsProveRoundsProg iop encSym x w m (Nat.le_of_succ_le hm)) with ⟨tables, roots, chals⟩
    rw [hp] at htab hrt hch hchList
    dsimp only at htab hrt hch hchList ⊢
    have hπ : iop.proveRound ⟨m, hm⟩ x w chals =
        bcsHonestTables iop (fun _ => hTree) [] encSym (chainedFS f) x w ⟨m, hm⟩ := by
      have hon := congrFun (bcsHonestTables_eq_iopProverOracles iop (fun _ => hTree) [] encSym
        (chainedFS f) x w) ⟨m, hm⟩
      rw [show chals = prefixChallenges (bcsHonestChallenges iop (fun _ => hTree) [] encSym
        (chainedFS f) x w) ⟨m, hm⟩ from funext hch]
      exact hon.symm
    have hrt_m : merkleRoot (fun _ => hTree) []
        (oracleLeaves encSym d (iop.proveRound ⟨m, hm⟩ x w chals)) =
        bcsHonestRoots iop (fun _ => hTree) [] encSym (chainedFS f) x w ⟨m, hm⟩ := by
      rw [hπ]; rfl
    have hroots'_list :
        List.ofFn (Fin.snoc roots (merkleRoot (fun _ => hTree) []
          (oracleLeaves encSym d (iop.proveRound ⟨m, hm⟩ x w chals))) : Fin (m + 1) → List Bool) =
        rootPrefix (bcsHonestRoots iop (fun _ => hTree) [] encSym (chainedFS f) x w) ⟨m, hm⟩ := by
      rw [List.ofFn_succ_last, hrt_m, rootPrefix_eq_take_append _ hm]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact congrArg (· ++ _) (List.ext_getElem (by simp [Nat.le_of_succ_le hm]) fun k hk₁ _ => by
        simp [hrt ⟨k, by simpa using hk₁⟩])
    have hc_m : f (x, List.ofFn (Fin.snoc roots (merkleRoot (fun _ => hTree) []
          (oracleLeaves encSym d (iop.proveRound ⟨m, hm⟩ x w chals))) : Fin (m + 1) → List Bool),
        List.ofFn chals) =
        bcsHonestChallenges iop (fun _ => hTree) [] encSym (chainedFS f) x w ⟨m, hm⟩ := by
      rw [hroots'_list, hchList, bcsHonestChallenges, bcsChallenge, chainedFS,
        rootPrefix_eq_take_append _ hm, List.dropLast_concat]
    simp only [bcsProveRoundsProg, OracleComp.evalPure_bind, hp, OracleComp.evalPure_liftLeft,
      evalPure_merkleRootProg, OracleComp.evalPure_liftRight, OracleComp.evalPure_query,
      OracleComp.evalPure_pure]
    exact ⟨snoc_eq_restrict hm htab hπ, snoc_eq_restrict hm hrt hrt_m,
      snoc_eq_restrict hm hch hc_m, ofFn_snoc_chainedFS hm f x _ hchList hc_m⟩

@[simp]
theorem evalPure_bcsProveROM (hTree : List Bool → List Bool)
    (f : BCSFSQuery Stmt Chal → Chal) (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool) (x : Stmt) (w : Wit) :
    OracleComp.evalPure (bcsOracle hTree f) (bcsProveROM iop encSym x w) =
      bcsProve iop (fun _ => hTree) [] encSym (chainedFS f) x w := by
  obtain ⟨htab, hrt, hch, -⟩ := evalPure_bcsProveRoundsProg hTree f iop encSym x w r le_rfl
  rcases hout : OracleComp.evalPure (bcsOracle hTree f)
    (bcsProveRoundsProg iop encSym x w r le_rfl) with ⟨tables, roots, chals⟩
  rw [hout] at htab hrt hch
  rcases (⟨funext htab, funext hrt, funext hch⟩ :
    tables = _ ∧ roots = _ ∧ chals = _) with ⟨rfl, rfl, rfl⟩
  simp only [bcsProveROM, OracleComp.evalPure_bind, hout, OracleComp.evalPure_liftLeft,
    OracleComp.evalPure_mapM, evalPure_merklePathProg, OracleComp.evalPure_pure, bcsProve,
    bcsHonestOpenings]

@[simp]
theorem evalPure_bcsVerifyOpeningsProg (hTree : List Bool → List Bool)
    (iop : PublicCoinIOP r d Stmt Wit Sym Chal) (encSym : Sym → List Bool)
    (x : Stmt) (prf : BCSProof r Sym) (chals : Fin r → Chal) :
    OracleComp.evalPure hTree (bcsVerifyOpeningsProg iop encSym x prf chals) =
      (prf.openings.length == (iop.queries x chals).length &&
        ((iop.queries x chals).zip prf.openings).all (fun ((j, idx), o) =>
          o.verify (fun _ => hTree) [] encSym d (prf.roots j) idx.val) &&
        iop.decide x chals (prf.openings.map MerkleOpening.leaf)) := by
  simp only [bcsVerifyOpeningsProg, OracleComp.evalPure_bind, OracleComp.evalPure_mapM,
    OracleComp.evalPure_pure, List.all_map]
  exact congrArg (fun b => _ && b && _) (List.all_congr rfl (by
    rintro ⟨⟨_, _⟩, ⟨_, _⟩⟩
    simp [MerkleOpening.verify]))

@[simp]
theorem evalPure_bcsVerifyROM (hTree : List Bool → List Bool)
    (f : BCSFSQuery Stmt Chal → Chal) (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool) (x : Stmt) (prf : BCSProof r Sym) :
    OracleComp.evalPure (bcsOracle hTree f) (bcsVerifyROM iop encSym x prf) =
      bcsVerify iop (fun _ => hTree) [] encSym (chainedFS f) x prf := by
  simp [bcsVerifyROM, bcsVerify]

/-- **Perfect completeness of the BCS ROM programs (`OracleComp` simulation form)**: under any
deterministic Merkle hash `hTree` whose digests all have one length and any transcript-chained
Fiat–Shamir function `f`, `bcsVerifyROM` accepts `bcsProveROM` on every `(x, w)` satisfying
`rel x w`. -/
theorem bcsVerifyROM_bcsProveROM_eq_true {iop : PublicCoinIOP r d Stmt Wit Sym Chal}
    {rel : Stmt → Wit → Prop} (hcomp : IOPCompleteness iop rel)
    (hTree : List Bool → List Bool) {ℓ : ℕ} (hlen : ∀ y, (hTree y).length = ℓ)
    (f : BCSFSQuery Stmt Chal → Chal)
    (encSym : Sym → List Bool) {x : Stmt} {w : Wit} (hrel : rel x w) :
    OracleComp.evalPure (bcsOracle hTree f) (do
      let prf ← bcsProveROM iop encSym x w
      bcsVerifyROM iop encSym x prf) = true := by
  simp [bcsVerify_bcsProve_eq_true hcomp (fun _ => hTree) [] hlen encSym (chainedFS f) hrel]

/-- Per-query distribution of the two-channel BCS random oracle with `σ`-bit Merkle digests and
uniform challenges over `Chal`: Merkle hash queries (`Sum.inl`) sample `BitString.uniformList σ`,
and Fiat–Shamir queries (`Sum.inr`) sample `PMF.uniformOfFintype Chal`. -/
@[expose] noncomputable def bcsOracleDist (Stmt Chal : Type) [Fintype Chal] [Nonempty Chal]
    (σ : ℕ) : (q : List Bool ⊕ BCSFSQuery Stmt Chal) → PMF (BCSROMSpec Stmt Chal q)
  | .inl _ => BitString.uniformList σ
  | .inr _ => PMF.uniformOfFintype Chal

/-- The honest BCS execution as a two-channel `OracleComp` program: generate a proof via
`bcsProveROM` and verify it via `bcsVerifyROM` against the same oracle. -/
@[expose] def bcsHonestROMProg (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool) (x : Stmt) (w : Wit) :
    OracleComp (BCSROMSpec Stmt Chal) Bool := do
  let prf ← bcsProveROM iop encSym x w
  bcsVerifyROM iop encSym x prf

/-- The honest BCS random-oracle experiment with `σ`-bit Merkle digests: runs `bcsHonestROMProg`
against the shared lazy random oracle `RandomOracle.answer (bcsOracleDist Stmt Chal σ)` from an
empty cache. -/
@[expose] noncomputable def bcsHonestROMGame [DecidableEq Stmt] [DecidableEq Chal]
    [Fintype Chal] [Nonempty Chal] (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool) (x : Stmt) (w : Wit) (σ : ℕ) : PMF Bool :=
  (OracleComp.runWith (RandomOracle.answer (bcsOracleDist Stmt Chal σ))
    (bcsHonestROMProg iop encSym x w) (fun _ => none)).map Prod.fst

/-- **Perfect completeness of the BCS transform in the lazy two-channel random-oracle model**: if
`iop` satisfies `IOPCompleteness iop rel` and `rel x w` holds, then for every digest length `σ`,
`bcsHonestROMGame` outputs `true` with probability `1` ([BenSassonChiesaSpooner2016]; compare
[ChiesaYogev2024], Construction 25.1.1, printed pp. 274–275). -/
theorem bcsHonestROMGame_eq_pure_true [DecidableEq Stmt] [DecidableEq Chal]
    [Fintype Chal] [Nonempty Chal] {iop : PublicCoinIOP r d Stmt Wit Sym Chal}
    {rel : Stmt → Wit → Prop} (hcomp : IOPCompleteness iop rel)
    (encSym : Sym → List Bool) {x : Stmt} {w : Wit} (hrel : rel x w) (σ : ℕ) :
    bcsHonestROMGame iop encSym x w σ = PMF.pure true := by
  refine OracleComp.map_fst_runWith_answer_eq_pure (bcsOracleDist Stmt Chal σ)
    (bcsHonestROMProg iop encSym x w) true fun h hh => ?_
  rw [show h = bcsOracle (fun msg => h (.inl msg)) (fun fsq => h (.inr fsq)) from
    funext fun | .inl _ => rfl | .inr _ => rfl]
  exact bcsVerifyROM_bcsProveROM_eq_true hcomp _
    (fun y => BitString.length_of_mem_support_uniformList (hh (.inl y))) _ encSym hrel

end ROMProtocol

section RBRKnowledge

variable {r d : ℕ} {Stmt Wit Sym Chal : Type}

/-- **Round-by-round knowledge soundness** of a `PublicCoinIOP` for relation `rel` with
straight-line IOP extractor `iopExtract`, doomed-prefix predicate `doomed`, and non-escaping round
transitions `goodStep` (compare `IOPRoundByRoundSoundness` and [ChiesaYogev2024], Chapter 31,
Definition 31.1.6 and Theorem 31.3.1, as well as state-restoration knowledge soundness in
[BenSassonChiesaSpooner2016] and [ChiesaYogev2024], Chapter 26, Theorem 26.1.1; note that
`extract_of_doomed` here is deterministic on complete `doomed` transcripts):
1. Every statement `x` starts in `doomed x []` on the empty transcript prefix.
2. Every non-escaping challenge `goodStep x pref π c` preserves `doomed`.
3. On any complete transcript `List.ofFn (fun j => (oracles j, chals j))` that remains `doomed`, if
   `iopVerify` accepts `oracles` at `chals`, then `iopExtract x oracles` satisfies `rel x`. -/
structure IOPRoundByRoundKnowledgeSoundness (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (rel : Stmt → Wit → Prop) (iopExtract : Stmt → (Fin r → OracleTable d Sym) → Wit)
    (doomed : Stmt → List (OracleTable d Sym × Chal) → Prop)
    (goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop) :
    Prop where
  /-- Every statement starts in `doomed` on the empty transcript prefix. -/
  init_doomed : ∀ x, doomed x []
  /-- Every non-escaping challenge preserves `doomed`. -/
  step_doomed : ∀ x pref π c, doomed x pref → goodStep x pref π c → doomed x (pref ++ [(π, c)])
  /-- On any doomed complete transcript accepted by `iopVerify`, `iopExtract` recovers a valid
  witness for `x`. -/
  extract_of_doomed : ∀ x (oracles : Fin r → OracleTable d Sym) (chals : Fin r → Chal),
    doomed x (List.ofFn fun j : Fin r => (oracles j, chals j)) →
      iopVerify iop x chals oracles = true → rel x (iopExtract x oracles)

/-- `IOPRoundByRoundKnowledgeSoundness` for `rel` implies `IOPRoundByRoundSoundness` for the
associated language `{x | ∃ w, rel x w}` with the same `goodStep` relation. -/
theorem IOPRoundByRoundKnowledgeSoundness.toRoundByRoundSoundness
    {iop : PublicCoinIOP r d Stmt Wit Sym Chal} {rel : Stmt → Wit → Prop}
    {iopExtract : Stmt → (Fin r → OracleTable d Sym) → Wit}
    {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop}
    (hks : IOPRoundByRoundKnowledgeSoundness iop rel iopExtract doomed goodStep) :
    IOPRoundByRoundSoundness iop {x | ∃ w, rel x w}
      (fun x pref => x ∉ {x | ∃ w, rel x w} ∧ doomed x pref) goodStep where
  init_doomed x hx := ⟨hx, hks.init_doomed x⟩
  step_doomed x pref π c hd hgood := ⟨hd.1, hks.step_doomed x pref π c hd.2 hgood⟩
  reject_of_doomed x oracles chals hd :=
    Bool.eq_false_iff.mpr fun hver =>
      hd.1 ⟨iopExtract x oracles, hks.extract_of_doomed x oracles chals hd.2 hver⟩

/-- If every round's challenge satisfies `goodStep` under `IOPRoundByRoundKnowledgeSoundness` and
`iopVerify` accepts, then `iopExtract` recovers a valid witness for `x`. -/
theorem IOPRoundByRoundKnowledgeSoundness.rel_iopExtract_of_goodSteps
    {iop : PublicCoinIOP r d Stmt Wit Sym Chal} {rel : Stmt → Wit → Prop}
    {iopExtract : Stmt → (Fin r → OracleTable d Sym) → Wit}
    {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop}
    (hks : IOPRoundByRoundKnowledgeSoundness iop rel iopExtract doomed goodStep)
    (x : Stmt) (oracles : Fin r → OracleTable d Sym) (chals : Fin r → Chal)
    (hsteps : ∀ j : Fin r,
      goodStep x ((List.ofFn fun i : Fin r => (oracles i, chals i)).take j.val)
        (oracles j) (chals j))
    (hver : iopVerify iop x chals oracles = true) :
    rel x (iopExtract x oracles) :=
  hks.extract_of_doomed x oracles chals
    (doomed_ofFn_of_goodSteps (hks.init_doomed x) (hks.step_doomed x) oracles chals hsteps) hver

end RBRKnowledge

/-- Cost of a BCS oracle call on the Merkle hash channel (`Sum.inl`). -/
@[expose] def bcsMTCost {Stmt Chal : Type} : List Bool ⊕ BCSFSQuery Stmt Chal → ℕ
  | .inl _ => 1
  | .inr _ => 0

/-- Cost of a BCS oracle call on the Fiat–Shamir challenge channel (`Sum.inr`). -/
@[expose] def bcsFSCost {Stmt Chal : Type} : List Bool ⊕ BCSFSQuery Stmt Chal → ℕ
  | .inl _ => 0
  | .inr _ => 1


end Cslib.Crypto.Protocols.BCS
