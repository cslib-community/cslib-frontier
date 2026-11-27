/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.BCS.ROM.PolyTime
public import CslibFrontier.Crypto.Protocols.BCS.ROM.StickyBad
public import CslibFrontier.Crypto.Protocols.BCS.ROM.VerifyBounds
public import CslibFrontier.Crypto.Protocols.BCS.ROM.Soundness
public import CslibFrontier.Crypto.Protocols.BCS.ROM.KnowledgeSoundness

/-!
# Soundness and straight-line knowledge soundness of the BCS transform in the random-oracle model

This facade re-exports the multi-round Ben-Sasson–Chiesa–Spooner (BCS) random-oracle
development (split across `ROM.Extract`, `ROM.PolyTime`, `ROM.Protocol`, `ROM.State`,
`ROM.StickyBad`, `ROM.VerifyBounds`, `ROM.Soundness`, and `ROM.KnowledgeSoundness`), lifting
(`CslibFrontier/Crypto/Protocols/BCS/Basic.lean`) to an explicit two-channel random-oracle model
([BenSassonChiesaSpooner2016]; compare [ChiesaYogev2024], Construction 25.1.1, Remark 25.1.3, and
Theorem 25.2.1, printed pp. 274–278, Theorem 26.1.1 and Construction 26.1.3, printed pp. 288–291,
Chapter 31, Definitions 31.1.1–31.1.2, Definition 31.1.6, Construction 31.1.8, Theorem 31.2.1, and
Theorem 31.3.1, composed with Merkle trace extraction from Chapter 18, Construction 18.5.3 and
Lemma 18.5.7, printed pp. 199 and 204–207), proving adaptive round-by-round ROM soundness and
straight-line knowledge-soundness bounds (`bcsROMSoundness_bound`,
`bcsROMKnowledgeSoundness_bound`; state-restoration BCS knowledge soundness as in
[ChiesaYogev2024], Theorem 26.1.1, is open in #6042) alongside standard-model Merkle trace-binding
reductions:

1. **Straight-line multi-round oracle-table reconstruction (`bcsExtractTable`, `bcsExtractOracles`,
   `bcsExtractWitness`).** Given a symbol decoder `decSym : List Bool → Sym` with
   `Function.LeftInverse decSym encSym`, a default symbol `defaultSym : Sym`, and a recorded Merkle
   query-answer trace `tr_MT : List (List Bool × List Bool)`, `bcsExtractTable` reconstructs the
   depth-`d` oracle table committed under any Merkle root `rt` via `extractLeafFromTrace` without
   rewinding, and `bcsExtractOracles` reconstructs all `r` round tables of a `BCSProof`. When
   `tr_MT` is collision-free and records every opened authentication path of an accepted proof,
   `iopVerify` accepts the extracted oracle tables (`iopVerify_bcsExtractOracles_of_bcsVerify`);
   conversely, if `iopVerify` rejects the extracted tables on a trace consistent with `H k`,
   `tr_MT` contains an explicit hash collision
   (`exists_collision_of_bcsVerify_of_iopVerify_eq_false`). Prepending a fresh Merkle query-answer
   pair `(q, ans)` leaves `bcsExtractTable` and `bcsExtractOracles` unchanged unless `ans` hits a
   target root or a child of an existing Merkle query (`bcsExtractTable_cons_of_ne`,
   `bcsExtractOracles_cons_of_ne`).
2. **Two-channel BCS random-oracle model & completeness (`BCSROMSpec`, `chainedFS`, `bcsProveROM`,
   `bcsVerifyROM`, `bcsHonestROMGame_eq_pure_true`).** Over `BCSROMSpec Stmt Chal :=
   MerkleHashSpec ⊕ₒ BCSFSSpec Stmt Chal`, the left channel (`Sum.inl`) answers Merkle hash queries
   lazily with uniform `σ`-bit digests (`BitString.uniformList σ`), while the right channel
   (`Sum.inr`) answers transcript-chained Fiat–Shamir queries `(x, rts, prevChals) ↦ Chal` lazily
   with `PMF.uniformOfFintype Chal`: in round `j`, the prover and verifier query
   `(x, rootPrefix roots j, [c_0, ..., c_{j-1}]) ↦ c_j`. Under any deterministic oracle pair
   `(hTree, f)`, `bcsProveROM` and `bcsVerifyROM` agree via `OracleComp.evalPure` with `bcsProve`
   and `bcsVerify` instantiated with `chainedFS f`, yielding perfect completeness in the lazy
   two-channel ROM (`bcsHonestROMGame_eq_pure_true`).
3. **Adaptive two-channel ROM soundness (`bcsROMSoundness_bound`,
   `bcsROMSoundness_bound_of_prover_verifier`).** Given `IOPRoundByRoundSoundness iop lang doomed
   goodStep` with per-round escape probability `≤ ε_rbr` under `PMF.uniformOfFintype Chal`, the
   combined state invariant `BCSGoodState` requires `TraceCollisionFree tr_MT` together with
   `BCSChainDoomed`: every recorded Fiat–Shamir chain `(rts, chals)` of length `≤ r` for `x ∉ lang`
   maps under `bcsExtractTranscript` to a doomed IOP transcript prefix. Restricting the Merkle
   forbidden-digest guard (`bcsForbiddenDigests`) to the first `r` roots of each Fiat–Shamir query
   keeps the Merkle preimage/root-hit budget bounded by `3 * |tr_MT| + r * |tr_FS|` regardless of
   adversarial Fiat–Shamir input lengths, while `fsOutOfOrderTargets` bounds out-of-order
   Fiat–Shamir chain guessing by `|tr_FS| / |Chal|` per query. Accumulating both growing channel
   budgets via `OracleComp.toOuterMeasure_bad_le_two_budgets` bounds adaptive cheating provers with
   `t_FS` Fiat–Shamir queries and `Q_MT` total Merkle queries by
   `(t_FS + r) * (ε_rbr + (t_FS + r) * (1 / |Chal|)) +`
   `Q_MT * ((3 * Q_MT + r * (t_FS + r)) * (1 / 2 ^ σ))`.
4. **Adaptive straight-line ROM knowledge soundness (`IOPRoundByRoundKnowledgeSoundness`,
   `bcsROMKnowledgeSoundness_bound`, `bcsROMKnowledgeSoundness_bound_of_prover_verifier`).** From
   `IOPRoundByRoundKnowledgeSoundness iop rel iopExtract doomed goodStep` (which also implies
   `IOPRoundByRoundSoundness` for `{x | ∃ w, rel x w}` via
   `IOPRoundByRoundKnowledgeSoundness.toRoundByRoundSoundness`), `bcsKnowledgeSoundnessGame`
   reconstructs `bcsExtractWitness iopExtract decSym defaultSym tr_P x prf.roots` straight-line
   from the prover's own Merkle query trace `tr_P` *before* running `bcsVerifyROM`, with zero
   rewinding, and bounds the probability that `bcsVerifyROM` accepts while `rel x w` fails by the
   same explicit two-channel ROM error bound.

**Source-to-Lean adaptation and scope notes:**
* *Oracle and transcript convention:* [ChiesaYogev2024], Construction 25.1.1 (printed pp. 274–275)
  already uses `2 * r` separate domain-separated per-round Merkle and Fiat–Shamir random oracles
  (with zero-knowledge salt lengths `s_MT`, `s_FS`; see Remark 25.1.3 on root-prefix vs. hash-chain
  Fiat–Shamir queries). Here (`s_MT = s_FS = 0`), `BCSROMSpec Stmt Chal := MerkleHashSpec ⊕ₒ
  BCSFSSpec Stmt Chal` uses two unindexed typed channels: one shared Merkle hash channel on
  `Sum.inl` (`List Bool → List Bool`, via `merkleRootProg` / `merklePathProg` / `merkleVerifyProg`
  with `encPair` node framing) and one transcript-chained Fiat–Shamir channel on `Sum.inr`
  (`BCSFSQuery Stmt Chal := Stmt × List (List Bool) × List Chal ↦ Chal`, querying
  `(x, rootPrefix roots j, [c_0, ..., c_{j-1}]) ↦ c_j` in round `j`).
* *Round-by-round vs. state-restoration hypotheses:* Both [BenSassonChiesaSpooner2016] and
  [ChiesaYogev2024], Theorem 25.2.1 and Theorem 26.1.1 (printed pp. 276–278 and 288–289) formulate
  BCS ROM soundness and straight-line knowledge soundness via IOP state-restoration soundness and
  state-restoration knowledge soundness, while [ChiesaYogev2024], Chapter 31 (Definitions
  31.1.1–31.1.2, Definition 31.1.6, Construction 31.1.8, Theorem 31.2.1, and Theorem 31.3.1)
  reduces state-restoration soundness and knowledge soundness to round-by-round hypotheses. This
  layer proves the ROM bounds directly from `IOPRoundByRoundSoundness` and
  `IOPRoundByRoundKnowledgeSoundness` (whose deterministic `extract_of_doomed` on complete `doomed`
  transcripts is stronger than Definition 31.1.6's two-phase per-round experiment) with per-round
  uniform challenge escape probability `≤ ε_rbr`, bounding adaptive Fiat–Shamir grinding directly
  via `ε_rbr` and out-of-order chain-guessing targets (`fsOutOfOrderTargets`).
* *Explicit additive loss and query budgets:* Accumulating growing budgets across both channels via
  `OracleComp.toOuterMeasure_bad_le_two_budgets` and
  `CslibFrontier/Crypto/Computational/MerkleTree/ROMExtract.lean` yields the explicit additive bound
  `(t_FS + r) * (ε_rbr + (t_FS + r) * (1 / Fintype.card Chal)) + Q_MT *
  ((3 * Q_MT + r * (t_FS + r)) * (1 / 2 ^ σ))` (rather than the book's state-restoration plus
  multi-instance Merkle extraction error expression). Query budgets count all Merkle and Fiat–Shamir
  oracle calls, including malformed opening paths; the separate-budget corollaries
  (`bcsROMSoundness_bound_of_prover_verifier`, `bcsROMKnowledgeSoundness_bound_of_prover_verifier`)
  bound verifier Merkle cost only on outputs in `P.support`.
* *Straight-line trace extraction and polynomial-time certificates:* `bcsKnowledgeSoundnessGame`
  reconstructs `bcsExtractWitness iopExtract decSym defaultSym tr_P x prf.roots` directly from the
  prover's pre-verifier Merkle query trace `tr_P` with zero rewinding (compare [ChiesaYogev2024],
  Construction 26.1.3). Part 5 provides machine-level `ComputableInPolyTime` certificates for
  `bcsExtractTable`, `bcsExtractOracles`, `bcsExtractWitness`, and `bcsExtractTraceCollision`
  together with a tight standard-model `CollisionResistant H` reduction (`bcsTraceCollisionFinder`,
  `isPPT_bcsTraceCollisionFinder`); digest truncation accounting, polynomial-time
  NP-witness-to-IOP encoding, and zero-knowledge simulation remain outside scope.

## Main definitions

* `Cslib.Crypto.Protocols.BCS.bcsExtractTable`, `Cslib.Crypto.Protocols.BCS.bcsExtractOracles`,
  `Cslib.Crypto.Protocols.BCS.bcsExtractWitness`,
  `Cslib.Crypto.Protocols.BCS.BCSOpeningsQueriedInTrace`,
  `Cslib.Crypto.Protocols.BCS.bcsFindTraceConflict`,
  `Cslib.Crypto.Protocols.BCS.bcsExtractTraceCollision`: straight-line oracle-table, witness, and
  collision extraction from a Merkle trace and path-coverage predicate for BCS openings.
* `Cslib.Crypto.Protocols.BCS.BCSTraceOutput`, `Cslib.Crypto.Protocols.BCS.encBCSTraceOutput`,
  `Cslib.Crypto.Protocols.BCS.BCSTraceAdversary`,
  `Cslib.Crypto.Protocols.BCS.bcsTraceCollisionFinder`,
  `Cslib.Crypto.Protocols.BCS.bcsBreaksTraceBinding`,
  `Cslib.Crypto.Protocols.BCS.bcsTraceBindingGame`: standard-model trace-extraction collision
  reduction and binding experiment.
* `Cslib.Crypto.Protocols.BCS.BCSFSQuery`, `Cslib.Crypto.Protocols.BCS.BCSFSSpec`,
  `Cslib.Crypto.Protocols.BCS.BCSROMSpec`, `Cslib.Crypto.Protocols.BCS.bcsOracle`,
  `Cslib.Crypto.Protocols.BCS.chainedFSChallenges`, `Cslib.Crypto.Protocols.BCS.chainedFS`:
  two-channel BCS random-oracle interface and transcript-chained Fiat–Shamir bridge.
* `Cslib.Crypto.Protocols.BCS.bcsChallengesProg`, `Cslib.Crypto.Protocols.BCS.bcsProveROM`,
  `Cslib.Crypto.Protocols.BCS.bcsVerifyOpeningsProg`, `Cslib.Crypto.Protocols.BCS.bcsVerifyROM`,
  `Cslib.Crypto.Protocols.BCS.bcsOracleDist`, `Cslib.Crypto.Protocols.BCS.bcsHonestROMProg`,
  `Cslib.Crypto.Protocols.BCS.bcsHonestROMGame`: oracle-program BCS prover, verifier, and honest
  ROM completeness experiment.
* `Cslib.Crypto.Protocols.BCS.IOPRoundByRoundKnowledgeSoundness`: round-by-round knowledge
  soundness of a `PublicCoinIOP` with a straight-line IOP extractor.
* `Cslib.Crypto.Protocols.BCS.BCSTraceState`, `Cslib.Crypto.Protocols.BCS.bcsMemoize`,
  `Cslib.Crypto.Protocols.BCS.ValidFSChain`, `Cslib.Crypto.Protocols.BCS.bcsExtractTranscript`,
  `Cslib.Crypto.Protocols.BCS.BCSChainDoomed`, `Cslib.Crypto.Protocols.BCS.BCSGoodState`,
  `Cslib.Crypto.Protocols.BCS.bcsForbiddenDigests`,
  `Cslib.Crypto.Protocols.BCS.fsOutOfOrderTargets`: list-trace ROM handler and adaptive soundness
  invariants.
* `Cslib.Crypto.Protocols.BCS.bcsMTCost`, `Cslib.Crypto.Protocols.BCS.bcsFSCost`,
  `Cslib.Crypto.Protocols.BCS.bcsOpeningsMerkleQueries`,
  `Cslib.Crypto.Protocols.BCS.bcsSoundnessProg`, `Cslib.Crypto.Protocols.BCS.bcsSoundnessGame`,
  `Cslib.Crypto.Protocols.BCS.bcsExecROM`,
  `Cslib.Crypto.Protocols.BCS.bcsKnowledgeSoundnessGame`,
  `Cslib.Crypto.Protocols.BCS.BCSExtractionFails`: per-channel query costs, ROM soundness and
  knowledge-soundness experiments, and the straight-line extraction-failure event.

## Main results

* `Cslib.Crypto.Protocols.BCS.iopVerify_bcsExtractOracles_of_bcsVerify`,
  `Cslib.Crypto.Protocols.BCS.exists_collision_of_bcsVerify_of_iopVerify_eq_false`,
  `Cslib.Crypto.Protocols.BCS.bcsExtractTable_cons_of_ne`,
  `Cslib.Crypto.Protocols.BCS.bcsExtractOracles_cons_of_ne`: fixed-trace consistency, dual
  collision extraction, and non-inverting Merkle extension invariance for `bcsExtractOracles`.
* `Cslib.Crypto.Protocols.BCS.evalPure_bcsChallengesProg`,
  `Cslib.Crypto.Protocols.BCS.evalPure_bcsProveROM`,
  `Cslib.Crypto.Protocols.BCS.evalPure_bcsVerifyROM`,
  `Cslib.Crypto.Protocols.BCS.bcsVerifyROM_bcsProveROM_eq_true`,
  `Cslib.Crypto.Protocols.BCS.bcsHonestROMGame_eq_pure_true`: deterministic simulation and perfect
  completeness of the BCS transform in the two-channel random-oracle model.
* `Cslib.Crypto.Protocols.BCS.IOPRoundByRoundKnowledgeSoundness.toRoundByRoundSoundness`,
  `Cslib.Crypto.Protocols.BCS.IOPRoundByRoundKnowledgeSoundness.rel_iopExtract_of_goodSteps`:
  round-by-round knowledge soundness implies round-by-round soundness for `{x | ∃ w, rel x w}` and
  witness recovery along good challenge steps.
* `Cslib.Crypto.Protocols.BCS.toOuterMeasure_bcsMemoize_not_goodState_step`,
  `Cslib.Crypto.Protocols.BCS.toOuterMeasure_run_bcsMemoize_not_goodState_le`: single-step and
  accumulated bad-state bounds for `bcsMemoize`.
* `Cslib.Crypto.Protocols.BCS.isCostBounded_bcsFSCost_bcsVerifyROM`,
  `Cslib.Crypto.Protocols.BCS.isCostBounded_bcsMTCost_bcsVerifyROM`,
  `Cslib.Crypto.Protocols.BCS.isCostBounded_bcsMTCost_bcsVerifyROM_of_queries_le`: verifier query
  cost bounds on both channels.
* `Cslib.Crypto.Protocols.BCS.bcsROMSoundness_bound`,
  `Cslib.Crypto.Protocols.BCS.bcsROMSoundness_bound_of_prover_verifier`: adaptive two-channel ROM
  soundness bounds for the BCS transform.
* `Cslib.Crypto.Protocols.BCS.bcsROMKnowledgeSoundness_trace_bound`,
  `Cslib.Crypto.Protocols.BCS.bcsROMKnowledgeSoundness_bound`,
  `Cslib.Crypto.Protocols.BCS.bcsROMKnowledgeSoundness_bound_of_prover_verifier`: adaptive
  straight-line ROM knowledge soundness bounds without rewinding.
* `Cslib.Crypto.Protocols.BCS.bcs_trace_sound_or_collision`,
  `Cslib.Crypto.Protocols.BCS.isCollision_bcsExtractTraceCollision`: deterministic trace-extraction
  binding and collision extraction.
* `Cslib.Crypto.Protocols.BCS.computableInPolyTime_bcsExtractTable`,
  `Cslib.Crypto.Protocols.BCS.computableInPolyTime_bcsExtractOracles`,
  `Cslib.Crypto.Protocols.BCS.computableInPolyTime_bcsExtractWitness`,
  `Cslib.Crypto.Protocols.BCS.computableInPolyTime_bcsFindTraceConflict`,
  `Cslib.Crypto.Protocols.BCS.computableInPolyTime_bcsExtractTraceCollision`,
  `Cslib.Crypto.Protocols.BCS.isPPT_bcsTraceCollisionFinder`,
  `Cslib.Crypto.Protocols.BCS.succProbability_bcsTraceBindingGame_le`,
  `Cslib.Crypto.Protocols.BCS.CollisionResistant.bcsTraceBinding_negligible`,
  `Cslib.Crypto.Protocols.BCS.HashFamily.bcsTraceBinding_negligible`: polynomial-time certificates
  for straight-line trace extraction and standard-model trace-binding reductions to
  `CollisionResistant H`.

## References

* [E. Ben-Sasson, A. Chiesa, N. Spooner, *Interactive Oracle Proofs*][BenSassonChiesaSpooner2016]
* [A. Chiesa, E. Yogev, *Building Cryptographic Proofs from Hash Functions*][ChiesaYogev2024],
  Chapter 18 (Construction 18.5.3 and Lemma 18.5.7, printed pp. 199, 207), Chapter 25
  (Construction 25.1.1, Remark 25.1.3, and Theorem 25.2.1, printed pp. 274–278), Chapter 26
  (Theorem 26.1.1 and Construction 26.1.3, printed pp. 288–289), and Chapter 31 (Definitions
  31.1.1–31.1.2, Definition 31.1.6, Construction 31.1.8, Theorem 31.2.1, and Theorem 31.3.1).
-/
