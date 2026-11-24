/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.BCS.ROM.Extract
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# Polynomial-time BCS trace extraction and standard-model collision reduction

Machine-level `ComputableInPolyTime` certificates for straight-line BCS oracle-table, witness, and
collision extraction from a recorded Merkle trace, together with a tight standard-model reduction
from trace-extraction BCS binding to `CollisionResistant H` ([BenSassonChiesaSpooner2016];
[ChiesaYogev2024], Construction 18.5.3 and Lemma 18.5.7).

## Main definitions

* `Cslib.Crypto.Protocols.BCS.BCSTraceOutput`, `Cslib.Crypto.Protocols.BCS.encBCSTraceOutput`,
  `Cslib.Crypto.Protocols.BCS.BCSTraceAdversary`: output bundle, binary encoding, and adversary
  type for trace-recording BCS binding experiments.
* `Cslib.Crypto.Protocols.BCS.bcsTraceCollisionFinder`,
  `Cslib.Crypto.Protocols.BCS.bcsBreaksTraceBinding`,
  `Cslib.Crypto.Protocols.BCS.bcsTraceBindingGame`: collision-finding wrapper, trace-binding break
  predicate, and standard-model binding experiment.

## Main results

* `Cslib.Crypto.Protocols.BCS.computableInPolyTime_bcsExtractTable`,
  `Cslib.Crypto.Protocols.BCS.computableInPolyTime_bcsExtractOracles`,
  `Cslib.Crypto.Protocols.BCS.computableInPolyTime_bcsExtractWitness`,
  `Cslib.Crypto.Protocols.BCS.computableInPolyTime_bcsFindTraceConflict`,
  `Cslib.Crypto.Protocols.BCS.computableInPolyTime_bcsExtractTraceCollision`: multi-tape Turing
  machine polynomial-time certificates for straight-line BCS trace extraction and conflict finding.
* `Cslib.Crypto.Protocols.BCS.isCollision_of_bcsBreaksTraceBinding`,
  `Cslib.Crypto.Protocols.BCS.succProbability_bcsTraceBindingGame_le`,
  `Cslib.Crypto.Protocols.BCS.isPPT_bcsTraceCollisionFinder`,
  `Cslib.Crypto.Protocols.BCS.CollisionResistant.bcsTraceBinding_negligible`,
  `Cslib.Crypto.Protocols.BCS.HashFamily.bcsTraceBinding_negligible`: tight success-probability and
  uniform strict-PPT reductions from trace-extraction BCS binding to hash collision resistance.

## References

* [E. Ben-Sasson, A. Chiesa, N. Spooner, *Interactive Oracle Proofs*][BenSassonChiesaSpooner2016]
* [A. Chiesa, E. Yogev, *Building Cryptographic Proofs from Hash Functions*][ChiesaYogev2024],
  Chapter 18 (Construction 18.5.3 and Lemma 18.5.7).
-/

public section

namespace Cslib.Crypto.Protocols.BCS

open Cslib.Crypto Cslib.Probability Turing.MultiTapeTM

section PolyTimeAndReduction

variable {r d : ℕ} {Stmt Wit Sym Chal γ : Type}

/-- Straight-line extraction of a depth-`d` oracle table from a Merkle trace (`bcsExtractTable`)
runs in polynomial time. -/
@[program_certificate]
theorem computableInPolyTime_bcsExtractTable (d : ℕ)
    {encSym : Sym ↪ List Bool} {encIn : γ ↪ List Bool}
    {decSym : List Bool → Sym} (defaultSym : Sym)
    (hdec : ComputableInPolyTime decSym encBits encSym)
    {tr_MT : γ → List (List Bool × List Bool)} {rt : γ → List Bool}
    (htr : ComputableInPolyTime tr_MT encIn encMerkleTrace)
    (hrt : ComputableInPolyTime rt encIn encBits) :
    ComputableInPolyTime
      (fun a => bcsExtractTable decSym defaultSym (tr_MT a) d (rt a))
      encIn (encOracleTable d encSym) := by
  refine ComputableInPolyTime.finFn fun idx => ?_
  have hleaf := computableInPolyTime_extractLeafFromTrace d htr hrt
    (ComputableInPolyTime.const idx.val)
  convert hleaf.optionElimWithInput (body := fun _ bits => decSym bits)
    (ComputableInPolyTime.const defaultSym)
    (hdec.comp (ComputableInPolyTime.snd encIn encBits)) using 1
  funext a
  simp only [bcsExtractTable]
  cases extractLeafFromTrace (tr_MT a) d (rt a) idx.val <;> rfl

/-- Straight-line extraction of all `r` committed round oracle tables from a Merkle trace
(`bcsExtractOracles`) runs in polynomial time. -/
@[program_certificate]
theorem computableInPolyTime_bcsExtractOracles (r d : ℕ)
    {encSym : Sym ↪ List Bool} {encIn : γ ↪ List Bool}
    {decSym : List Bool → Sym} (defaultSym : Sym)
    (hdec : ComputableInPolyTime decSym encBits encSym)
    {tr_MT : γ → List (List Bool × List Bool)} {roots : γ → Fin r → List Bool}
    (htr : ComputableInPolyTime tr_MT encIn encMerkleTrace)
    (hroots : ComputableInPolyTime roots encIn (encFinFn r encBits)) :
    ComputableInPolyTime
      (fun a => bcsExtractOracles decSym defaultSym (tr_MT a) d (roots a))
      encIn (encFinFn r (encOracleTable d encSym)) :=
  ComputableInPolyTime.finFn fun j =>
    computableInPolyTime_bcsExtractTable d defaultSym hdec htr
      ((ComputableInPolyTime.finFn_apply encBits j).comp hroots)

/-- Straight-line BCS witness extraction (`bcsExtractWitness`) runs in polynomial time when the
underlying straight-line IOP extractor `iopExtract` and symbol decoder `decSym` run in polynomial
time. -/
@[program_certificate]
theorem computableInPolyTime_bcsExtractWitness (r d : ℕ)
    {encStmt : Stmt ↪ List Bool} {encWit : Wit ↪ List Bool}
    {encSym : Sym ↪ List Bool} {encIn : γ ↪ List Bool}
    {iopExtract : Stmt → (Fin r → OracleTable d Sym) → Wit}
    {decSym : List Bool → Sym} (defaultSym : Sym)
    (hiopExtract : ComputableInPolyTime
      (fun p : Stmt × (Fin r → OracleTable d Sym) => iopExtract p.1 p.2)
      (encPair encStmt (encFinFn r (encOracleTable d encSym))) encWit)
    (hdec : ComputableInPolyTime decSym encBits encSym)
    {tr_MT : γ → List (List Bool × List Bool)} {x : γ → Stmt}
    {roots : γ → Fin r → List Bool}
    (htr : ComputableInPolyTime tr_MT encIn encMerkleTrace)
    (hx : ComputableInPolyTime x encIn encStmt)
    (hroots : ComputableInPolyTime roots encIn (encFinFn r encBits)) :
    ComputableInPolyTime
      (fun a => bcsExtractWitness iopExtract decSym defaultSym (tr_MT a) (x a) (roots a))
      encIn encWit :=
  hiopExtract.comp
    (hx.prod (computableInPolyTime_bcsExtractOracles r d defaultSym hdec htr hroots))

/-- Finding the first opening in a BCS proof that disagrees with straight-line trace extraction
(`bcsFindTraceConflict`) runs in polynomial time. -/
@[program_certificate]
theorem computableInPolyTime_bcsFindTraceConflict
    {encStmt : Stmt ↪ List Bool} {encSym : Sym ↪ List Bool} {encChal : Chal ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {iop : PublicCoinIOP r d Stmt Wit Sym Chal} {hFS : Stmt → List (List Bool) → Chal}
    (hqueries : ComputableInPolyTime (fun p : Stmt × (Fin r → Chal) => iop.queries p.1 p.2)
      (encIOPTranscript r encStmt encChal) (encIOPQueryList r d))
    (hhFS : ComputableInPolyTime (fun p : Stmt × List (List Bool) => hFS p.1 p.2)
      (encFSTranscript encStmt) encChal)
    {tr_MT : γ → List (List Bool × List Bool)} {x : γ → Stmt} {prf : γ → BCSProof r Sym}
    (htr : ComputableInPolyTime tr_MT encIn encMerkleTrace)
    (hx : ComputableInPolyTime x encIn encStmt)
    (hprf : ComputableInPolyTime prf encIn (encBCSProof r Sym encSym)) :
    ComputableInPolyTime
      (fun a => bcsFindTraceConflict iop encSym hFS (tr_MT a) (x a) (prf a))
      encIn
      (encOption (encPair (encIOPQuery r d) (encMerkleOpeningOf Sym encSym))) :=
  ComputableInPolyTime.findWithInput
    ((ComputableInPolyTime.zip (encIOPQuery r d) (encMerkleOpeningOf Sym encSym)).comp
      ((hqueries.comp (hx.prod (computableInPolyTime_bcsChallenge hhFS hx
        (encBCSProof_roots_polyTime r Sym encSym hprf)))).prod
        (encBCSProof_openings_polyTime r Sym encSym hprf)))
    (ComputableInPolyTime.bne (encB := encOption encBits)
      (computableInPolyTime_extractLeafFromTrace d (htr.comp (.fst _ _))
        (ComputableInPolyTime.finFn_apply'
          ((encBCSProof_roots_polyTime r Sym encSym hprf).comp (.fst _ _)) (by fun_prop))
        (by fun_prop))
      (by fun_prop))

/-- Deterministic trace collision extraction for the BCS transform (`bcsExtractTraceCollision`)
runs in polynomial time. -/
@[program_certificate]
theorem computableInPolyTime_bcsExtractTraceCollision
    {encStmt : Stmt ↪ List Bool} {encSym : Sym ↪ List Bool} {encChal : Chal ↪ List Bool}
    {encIn : γ ↪ List Bool}
    {iop : PublicCoinIOP r d Stmt Wit Sym Chal} {H : List Bool → List Bool → List Bool}
    {hFS : Stmt → List (List Bool) → Chal}
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length)
    (hqueries : ComputableInPolyTime (fun p : Stmt × (Fin r → Chal) => iop.queries p.1 p.2)
      (encIOPTranscript r encStmt encChal) (encIOPQueryList r d))
    (hhFS : ComputableInPolyTime (fun p : Stmt × List (List Bool) => hFS p.1 p.2)
      (encFSTranscript encStmt) encChal)
    {k : γ → List Bool} {tr_MT : γ → List (List Bool × List Bool)}
    {x : γ → Stmt} {prf : γ → BCSProof r Sym}
    (hk : ComputableInPolyTime k encIn encBits)
    (htr : ComputableInPolyTime tr_MT encIn encMerkleTrace)
    (hx : ComputableInPolyTime x encIn encStmt)
    (hprf : ComputableInPolyTime prf encIn (encBCSProof r Sym encSym)) :
    ComputableInPolyTime
      (fun a => bcsExtractTraceCollision iop H (k a) encSym hFS (tr_MT a) (x a) (prf a))
      encIn (encPair encBits encBits) := by
  let encElem : ((Fin r × Fin (2 ^ d)) × MerkleOpening Sym) ↪ List Bool :=
    encPair (encIOPQuery r d) (encMerkleOpeningOf Sym encSym)
  have hfind := computableInPolyTime_bcsFindTraceConflict hqueries hhFS htr hx hprf
  have hfst := ComputableInPolyTime.fst encIn encElem
  have hcol : ComputableInPolyTime
      (fun p : γ × ((Fin r × Fin (2 ^ d)) × MerkleOpening Sym) =>
        extractTraceCollision H (k p.1) (tr_MT p.1) p.2.1.2.val (encSym p.2.2.leaf) p.2.2.path)
      (encPair encIn encElem) (encPair encBits encBits) :=
    computableInPolyTime_extractTraceCollision hH hlen
      (hk.comp hfst) (htr.comp hfst) (by fun_prop) (by fun_prop) (by fun_prop)
  convert hfind.optionElimWithInput
    (body := fun a (e : (Fin r × Fin (2 ^ d)) × MerkleOpening Sym) =>
      extractTraceCollision H (k a) (tr_MT a) e.1.2.val (encSym e.2.leaf) e.2.path)
    (ComputableInPolyTime.const ([], [])) hcol using 1
  funext a
  unfold bcsExtractTraceCollision
  cases bcsFindTraceConflict iop encSym hFS (tr_MT a) (x a) (prf a) <;> rfl

end PolyTimeAndReduction

/-- Output of a trace-recording BCS adversary: a Merkle query-answer trace `trace`, a statement
`stmt`, and a non-interactive BCS proof `proof`. -/
structure BCSTraceOutput (r : ℕ) (Stmt Sym : Type) where
  /-- The recorded Merkle query-answer trace. -/
  trace : List (List Bool × List Bool)
  /-- The statement chosen by the adversary. -/
  stmt : Stmt
  /-- The BCS proof. -/
  proof : BCSProof r Sym

/-- Encoding of `BCSTraceOutput r Stmt Sym`. -/
enc_structure encBCSTraceOutput (r : ℕ) (Stmt : Type) (Sym : Type)
    (encStmt : Stmt ↪ List Bool) (encSym : Sym ↪ List Bool) :
    BCSTraceOutput r Stmt Sym where
  trace : encMerkleTrace,
  stmt : encStmt,
  proof : (encBCSProof r Sym encSym)

/-- A trace-recording BCS adversary receives the unary security parameter `n` and the Merkle hash
key `k`, and outputs a Merkle query-answer trace, a statement, and a BCS proof. -/
abbrev BCSTraceAdversary (r : ℕ) (Stmt Sym : Type) :=
  ℕ → List Bool → ProbComp (BCSTraceOutput r Stmt Sym)

section TraceReduction

variable {r d : ℕ} {Stmt Wit Sym Chal : Type}

/-- The collision finder built from a trace-recording BCS adversary: run the adversary and extract
a Merkle collision from its trace with `bcsExtractTraceCollision`. -/
@[expose] def bcsTraceCollisionFinder (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (H : List Bool → List Bool → List Bool) (encSym : Sym → List Bool)
    (hFS : Stmt → List (List Bool) → Chal)
    (adversary : BCSTraceAdversary r Stmt Sym) : CollisionFinder := fun n k => do
  let out ← adversary n k
  return bcsExtractTraceCollision iop H k encSym hFS out.trace out.stmt out.proof

/-- Boolean predicate recording that `out` breaks trace-extraction BCS binding under `k`: the trace
is consistent with `H k` and covers all opened authentication paths of `out.proof`, `bcsVerify`
accepts `out.proof`, and `iopVerify` rejects the straight-line extracted tables
`bcsExtractOracles`. -/
@[expose] def bcsBreaksTraceBinding (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (H : List Bool → List Bool → List Bool) (k : List Bool) (encSym : Sym → List Bool)
    (decSym : List Bool → Sym) (defaultSym : Sym)
    (hFS : Stmt → List (List Bool) → Chal) (out : BCSTraceOutput r Stmt Sym) : Bool :=
  decide (TraceConsistentWith (H k) out.trace) &&
    decide (BCSOpeningsQueriedInTrace H k iop encSym out.trace out.stmt
      (bcsChallenge hFS out.stmt out.proof.roots) out.proof) &&
    bcsVerify iop H k encSym hFS out.stmt out.proof &&
    !iopVerify iop out.stmt (bcsChallenge hFS out.stmt out.proof.roots)
      (bcsExtractOracles decSym defaultSym out.trace d out.proof.roots)

/-- The trace-extraction BCS binding experiment at security parameter `n`: sample a uniform `n`-bit
hash key `k`, run `adversary n k`, and accept when `bcsBreaksTraceBinding` holds. -/
noncomputable def bcsTraceBindingGame (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (H : List Bool → List Bool → List Bool) (encSym : Sym → List Bool)
    (decSym : List Bool → Sym) (defaultSym : Sym)
    (hFS : Stmt → List (List Bool) → Chal)
    (adversary : BCSTraceAdversary r Stmt Sym) (n : ℕ) : ProbComp Bool := do
  let k ← BitString.sampleList n
  let out ← adversary n k
  return bcsBreaksTraceBinding iop H k encSym decSym defaultSym hFS out

/-- **A trace-extraction BCS binding break yields a hash collision**: if `bcsBreaksTraceBinding`
holds and `Function.LeftInverse decSym encSym`, then `bcsExtractTraceCollision` outputs a valid
collision for `H k`. -/
theorem isCollision_of_bcsBreaksTraceBinding {iop : PublicCoinIOP r d Stmt Wit Sym Chal}
    {H : List Bool → List Bool → List Bool} {k : List Bool} {encSym : Sym → List Bool}
    {decSym : List Bool → Sym} (hdec : Function.LeftInverse decSym encSym) (defaultSym : Sym)
    {hFS : Stmt → List (List Bool) → Chal} {out : BCSTraceOutput r Stmt Sym}
    (hbreak : bcsBreaksTraceBinding iop H k encSym decSym defaultSym hFS out = true) (n : ℕ) :
    let col := bcsExtractTraceCollision iop H k encSym hFS out.trace out.stmt out.proof
    isCollision H (fun _ _ => true) n k col.1 col.2 = true := by
  simp only [bcsBreaksTraceBinding, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
    at hbreak
  obtain ⟨⟨⟨hcons, hpaths⟩, hver⟩, hrej⟩ := hbreak
  exact isCollision_bcsExtractTraceCollision hdec defaultSym
    hcons hpaths hver hrej n

/-- **Tight reduction from trace-extraction BCS binding to collision finding**: at every security
parameter `n`, a trace-recording BCS adversary succeeds at most as often as its collision finder
`bcsTraceCollisionFinder`. -/
theorem succProbability_bcsTraceBindingGame_le (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (H : List Bool → List Bool → List Bool) {encSym : Sym → List Bool}
    {decSym : List Bool → Sym} (hdec : Function.LeftInverse decSym encSym) (defaultSym : Sym)
    (hFS : Stmt → List (List Bool) → Chal)
    (adversary : BCSTraceAdversary r Stmt Sym) (n : ℕ) :
    Game.succProbability
        (ProbComp.eval (bcsTraceBindingGame iop H encSym decSym defaultSym hFS adversary n)) ≤
      Game.succProbability (ProbComp.eval
        (collisionGame H (fun _ _ => true)
          (bcsTraceCollisionFinder iop H encSym hFS adversary) n)) := by
  refine Game.succProbability_mono ?_
  simp only [pmf_norm, bcsTraceBindingGame, collisionGame, bcsTraceCollisionFinder]
  refine PMF.bind_apply_mono_on_support _ _ fun k _ =>
    PMF.bind_apply_mono_on_support _ _ fun out _ => ?_
  cases hbreak : bcsBreaksTraceBinding iop H k encSym decSym defaultSym hFS out
  · simp
  · rw [isCollision_of_bcsBreaksTraceBinding hdec defaultSym hbreak n]

/-- **Efficiency of `bcsTraceCollisionFinder`**: for a polynomial-time hash `H` with `k.length`-bit
digests, polynomial-time `iop.queries`, and polynomial-time `hFS`, the collision finder of any
uniform strict PPT trace-recording BCS adversary is uniform strict PPT. -/
theorem isPPT_bcsTraceCollisionFinder {encStmt : Stmt ↪ List Bool} {encSym : Sym ↪ List Bool}
    {encChal : Chal ↪ List Bool}
    {iop : PublicCoinIOP r d Stmt Wit Sym Chal} {H : List Bool → List Bool → List Bool}
    {hFS : Stmt → List (List Bool) → Chal}
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length)
    (hqueries : ComputableInPolyTime (fun p : Stmt × (Fin r → Chal) => iop.queries p.1 p.2)
      (encIOPTranscript r encStmt encChal) (encIOPQueryList r d))
    (hhFS : ComputableInPolyTime (fun p : Stmt × List (List Bool) => hFS p.1 p.2)
      (encFSTranscript encStmt) encChal)
    {adversary : BCSTraceAdversary r Stmt Sym}
    (hadversary : IsPPT (encBCSTraceOutput r Stmt Sym encStmt encSym) adversary) :
    IsPPT (encPair encBits encBits) (bcsTraceCollisionFinder iop H encSym hFS adversary) :=
  hadversary.bind_with (computableInPolyTime_bcsExtractTraceCollision hH hlen hqueries hhFS
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)).isPPTOn

/-- **Standard-model trace-extraction BCS binding from collision resistance**: if `H` is
collision-resistant (`CollisionResistant H`), every uniform strict PPT trace-recording BCS adversary
breaks binding with negligible probability. -/
theorem CollisionResistant.bcsTraceBinding_negligible
    {encStmt : Stmt ↪ List Bool} {encSym : Sym ↪ List Bool} {encChal : Chal ↪ List Bool}
    {iop : PublicCoinIOP r d Stmt Wit Sym Chal} {H : List Bool → List Bool → List Bool}
    {decSym : List Bool → Sym} (hdec : Function.LeftInverse decSym encSym) (defaultSym : Sym)
    {hFS : Stmt → List (List Bool) → Chal}
    (hcr : CollisionResistant H)
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length)
    (hqueries : ComputableInPolyTime (fun p : Stmt × (Fin r → Chal) => iop.queries p.1 p.2)
      (encIOPTranscript r encStmt encChal) (encIOPQueryList r d))
    (hhFS : ComputableInPolyTime (fun p : Stmt × List (List Bool) => hFS p.1 p.2)
      (encFSTranscript encStmt) encChal)
    {adversary : BCSTraceAdversary r Stmt Sym}
    (hadversary : IsPPT (encBCSTraceOutput r Stmt Sym encStmt encSym) adversary) :
    Negligible fun n => Game.succProbability
      (ProbComp.eval (bcsTraceBindingGame iop H encSym decSym defaultSym hFS adversary n)) :=
  negligible_of_le
    (hcr.negligible _ (isPPT_bcsTraceCollisionFinder hH hlen hqueries hhFS hadversary))
    (succProbability_bcsTraceBindingGame_le iop H hdec defaultSym hFS adversary)

/-- **Collision-resistant `HashFamily` corollary for trace-extraction BCS binding**. -/
theorem HashFamily.bcsTraceBinding_negligible
    {encStmt : Stmt ↪ List Bool} {encSym : Sym ↪ List Bool} {encChal : Chal ↪ List Bool}
    {iop : PublicCoinIOP r d Stmt Wit Sym Chal} {H : List Bool → List Bool → List Bool}
    {decSym : List Bool → Sym} (hdec : Function.LeftInverse decSym encSym) (defaultSym : Sym)
    {hFS : Stmt → List (List Bool) → Chal}
    (hH : HashFamily H)
    (hqueries : ComputableInPolyTime (fun p : Stmt × (Fin r → Chal) => iop.queries p.1 p.2)
      (encIOPTranscript r encStmt encChal) (encIOPQueryList r d))
    (hhFS : ComputableInPolyTime (fun p : Stmt × List (List Bool) => hFS p.1 p.2)
      (encFSTranscript encStmt) encChal)
    {adversary : BCSTraceAdversary r Stmt Sym}
    (hadversary : IsPPT (encBCSTraceOutput r Stmt Sym encStmt encSym) adversary) :
    Negligible fun n => Game.succProbability
      (ProbComp.eval (bcsTraceBindingGame iop H encSym decSym defaultSym hFS adversary n)) :=
  CollisionResistant.bcsTraceBinding_negligible hdec defaultSym hH.collisionResistant hH.polyTime
    (fun k x => hH.length_eq k x) hqueries hhFS hadversary

end TraceReduction

end Cslib.Crypto.Protocols.BCS
