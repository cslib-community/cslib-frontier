/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Kilian.NP
public import CslibFrontier.Crypto.Computational.MerkleTree.Extract
public import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Computability.Complexity.Classes.SharpP.Probability
import CslibFrontier.Computability.PCP.Completeness
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Probabilistic.Traverse
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.EventBind
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.SuppCases
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.List.GetD

/-!
# Rewinding compact PCP-table extraction for Kilian's protocol

This module constructs an explicit, uniform strict probabilistic polynomial-time rewinding
extractor `kilianTableExtractor` for Kilian's succinct interactive argument over any
`O(log |enc x|)`-coin PCP verifier `V` (`CslibFrontier.Crypto.Computational.Kilian`) and keyed
hash `H`, paired with a strict-PPT Merkle position-binding reduction
`kilianExtractorBindingAdversary` (`CslibFrontier.Crypto.Computational.MerkleTree.Extract`).

Given security parameter `n`, key `k`, and prover `P : KilianProver α`:
1. `kilianTableExtractor` runs `P.commit n k` once to obtain `cm = { stmt, root, state }`.
2. Enumerating every `ρ₀ ∈ BitString.enumList (V.coins cm.stmt)` (of polynomial size `2 ^ r`
   under the logarithmic coin bound) and every repetition slot `i < n`, `kilianCollectRuns`
   rewinds `P.answer n cm.state` `T n` times with slot `i` fixed to `ρ₀` and independent uniform
   challenges in the remaining `n - 1` slots.
3. `kilianExtractTableFromRuns` invokes `merkleExtractVector` on the verified openings from all
   accepted transcripts to assemble a compact bit table `table` of length
   `(V.queryTable cm.stmt).length`.

## Honest scope ([BarakGoldreich2001], Construction 3.4 and Lemma 3.5)

* **Compact PCP-table extraction (a step toward Barak–Goldreich weak proof of knowledge):**
  Barak and Goldreich prove weak proof of knowledge against non-uniform provers with an implicit
  reverse-sampling oracle for superpolynomial PCPs. Here adversaries and extractors are uniform
  strict PPT (`KilianProver.IsPPT`, `IsPPT`), and the extracted object is an explicit compact PCP
  table `table` for the `O(log |enc x|)`-coin verifier. **No NP witness `w` is extracted** by
  `kilianTableExtractor`.
* **Rational coin-acceptance fractions `< 1` vs. exact 100% `V.tableVerifier`:** for any rational
  fraction `num / den < 1` and any noticeable inverse-polynomial slack `1 / (p n + 1)`,
  `HashFamily.kilianTableExtraction` shows that `kilianTableExtractor` runs in strict PPT and
  extracts `(x, table)` whose expanded proof `V.proofOfTable x table` passes strictly more than
  `(num / den) * 2 ^ V.coins x` coins up to `(num / den) ^ n + 1 / (p n + 1) + negl n` loss.
  Exact 100% agreement (`V.tableVerifier (x, table) = true`) is not claimed: a cheating prover
  with acceptance probability `1 - o(1)` can silently abort whenever a single designated rare coin
  `ρ₀` appears in its `n` challenges (`Pr[abort] ≤ n / 2^r = o(1)`), hiding `ρ₀`'s witness bit
  from any black-box rewinder.
* **Membership corollary (`kilianExtract_mem_of_isPCP`,
  `HashFamily.kilianTableExtraction_npRelation`):** at threshold `1 / 2`, every extracted table
  accepted on `> (2 ^ V.coins x) / 2` coins certifies `ext.stmt ∈ L` when `V` is a PCP verifier
  with soundness error `≤ 1 / 2`; for an `NPRelation`, `∃ w, R.IsWitness ext.stmt w` follows
  existentially from `ext.stmt ∈ R.language` without extracting an explicit NP witness `w`.

Locators in [BarakGoldreich2001] are not re-verified against the primary PDF in this checkout
(`locator not re-verified against primary PDF`).

## Main definitions

* `Cslib.Crypto.KilianChallengeRun`, `Cslib.Crypto.encKilianChallengeRun`: a challenge tuple paired
  with the prover's response, and its framed encoding.
* `Cslib.Crypto.KilianExtractedTable`, `Cslib.Crypto.encKilianExtractedTable`: the committed
  statement, Merkle root, and extracted compact table, and its framed encoding.
* `Cslib.Crypto.kilianAcceptGame`, `Cslib.Crypto.kilianExtractionFracGame`: single-run prover
  acceptance and strict-fraction table-extraction experiments.
* `Cslib.Crypto.kilianRunsToOpenings`, `Cslib.Crypto.kilianExtractTableFromRuns`,
  `Cslib.Crypto.kilianRunsBindingOutput`: deterministic transcript extraction and conflict
  detection.
* `Cslib.Crypto.kilianPlantedRun`, `Cslib.Crypto.kilianCollectRuns`,
  `Cslib.Crypto.kilianTableExtractor`, `Cslib.Crypto.kilianExtractorBindingAdversary`: the
  rewinding table extractor and its paired Merkle position-binding adversary.

## Main results

* `Cslib.Crypto.length_kilianExtractTableFromRuns`,
  `Cslib.Crypto.accepts_kilianExtractTableFromRuns_or_breaksBinding`: either
  `kilianRunsBindingOutput` breaks position binding, or every accepted transcript agrees with
  `V.proofOfTable x table`.
* `Cslib.Crypto.isPPT_kilianTableExtractor`,
  `Cslib.Crypto.isPPT_kilianExtractorBindingAdversary`: uniform strict PPT efficiency.
* `Cslib.Crypto.succProbability_kilianAcceptGame_le_extracted`: exact finite-parameter rewinding
  extraction bound for any threshold `num / den` and per-coin attempt count `T n`.
* `Cslib.Crypto.HashFamily.kilianTableExtraction`,
  `Cslib.Crypto.kilianExtract_mem_of_isPCP`,
  `Cslib.Crypto.HashFamily.kilianTableExtraction_npRelation`: rewinding compact PCP-table
  extraction bounds under `HashFamily` and existential `NP` membership consequences (without
  extracting an explicit NP witness `w`).

## References

* [B. Barak, O. Goldreich, *Universal Arguments and their Applications*][BarakGoldreich2001],
  Construction 3.4 and Lemma 3.5.
* [J. Kilian, *A note on efficient zero-knowledge proofs and arguments*][Kilian1992].
-/

@[expose] public section

namespace Cslib.Crypto

open Complexity Probability Turing.MultiTapeTM
open scoped ENNReal NNReal

variable {α : Type}

/-! ### Transcript structures and deterministic table extraction -/

/-- One verifier challenge tuple paired with the prover's opening response. -/
@[ext]
structure KilianChallengeRun where
  /-- The verifier's random challenge strings for the repetition. -/
  challenges : List (List Bool)
  /-- The prover's response to `challenges`. -/
  response : KilianResponse
  deriving DecidableEq, Repr, Inhabited

/-- Encoding of a `KilianChallengeRun`: framed challenges followed by the prover response. -/
enc_structure encKilianChallengeRun : KilianChallengeRun where
  challenges : (encList encBits), response : encKilianResponse

/-- The output of rewinding extraction: the chosen statement, committed Merkle root, and
reconstructed compact PCP bit table. -/
@[ext]
structure KilianExtractedTable (α : Type) where
  /-- The statement output by the prover's first stage. -/
  stmt : α
  /-- The Merkle root committed by the prover's first stage. -/
  root : List Bool
  /-- The extracted compact table indexed by `V.queryTable stmt`. -/
  table : List Bool
  deriving DecidableEq, Repr, Inhabited

/-- Encoding of `KilianExtractedTable`: the statement, Merkle root, and compact table. -/
enc_structure encKilianExtractedTable (enc : α ↪ List Bool) : KilianExtractedTable α where
  stmt : enc, root : encBits, table : encBits

/-- Single-run prover acceptance game (without checking `stmt ∉ L`): sample a uniform `n`-bit
hash key, commit with `P.commit`, sample `n` PCP challenges, run `P.answer`, and verify. -/
noncomputable def kilianAcceptGame (H : List Bool → List Bool → List Bool) (V : PCPVerifier α)
    (P : KilianProver α) (n : ℕ) : ProbComp Bool := do
  let k ← BitString.sampleList n
  let cm ← P.commit n k
  let ρs ← kilianChallenges V n cm.stmt
  let resp ← P.answer n cm.state ρs
  return kilianVerify H V k cm.stmt cm.root ρs resp

/-- Collect all verified Merkle openings from accepted `KilianChallengeRun`s, converted to
`MerkleIndexedOpening`s below `(V.queryTable x).length`. -/
def kilianRunsToOpenings (H : List Bool → List Bool → List Bool) (V : PCPVerifier α)
    (k : List Bool) (x : α) (root : List Bool) (runs : List KilianChallengeRun) :
    List MerkleIndexedOpening :=
  let raw := (runs.filter fun run =>
    kilianVerify H V k x root run.challenges run.response).flatMap fun run =>
      (kilianOpenings V x run.challenges run.response).map fun pair =>
        let (addr, opening) := pair
        { position := kilianPosition V x addr, opening := ⟨[opening.leaf], opening.path⟩ }
  merkleVerifiedOpenings H k (kilianDepth V x) (V.queryTable x).length root raw

/-- Reconstruct a compact PCP table from `runs` by collecting verified openings from accepted
runs via `merkleExtractVector`. -/
def kilianExtractTableFromRuns (H : List Bool → List Bool → List Bool) (V : PCPVerifier α)
    (k : List Bool) (x : α) (root : List Bool) (runs : List KilianChallengeRun) : List Bool :=
  (merkleExtractVector (V.queryTable x).length [false]
    (kilianRunsToOpenings H V k x root runs)).map fun word => word.headD false

/-- Extract a `MerkleBindingOutput` from any conflicting pair of verified openings in `runs`. -/
def kilianRunsBindingOutput (H : List Bool → List Bool → List Bool) (V : PCPVerifier α)
    (k : List Bool) (x : α) (root : List Bool) (runs : List KilianChallengeRun) :
    MerkleBindingOutput :=
  merkleVectorBindingOutput root (kilianRunsToOpenings H V k x root runs)

@[simp]
theorem length_kilianExtractTableFromRuns {H : List Bool → List Bool → List Bool}
    {V : PCPVerifier α} {k : List Bool} {x : α} {root : List Bool}
    {runs : List KilianChallengeRun} :
    (kilianExtractTableFromRuns H V k x root runs).length = (V.queryTable x).length := by
  simp [kilianExtractTableFromRuns]

private theorem mem_kilianRunsToOpenings_leaf_len {H : List Bool → List Bool → List Bool}
    {V : PCPVerifier α} {k : List Bool} {x : α} {root : List Bool}
    {runs : List KilianChallengeRun} {entry : MerkleIndexedOpening}
    (h : entry ∈ kilianRunsToOpenings H V k x root runs) :
    entry.opening.leaf.length = 1 := by
  simp only [kilianRunsToOpenings, mem_merkleVerifiedOpenings, List.mem_flatMap, List.mem_map]
    at h
  obtain ⟨⟨_, ⟨_, ⟨a, o⟩, _, rfl⟩⟩, -, -⟩ := h
  rfl

/-- **Deterministic transcript-extraction dichotomy**: for any list of runs, either
`kilianRunsBindingOutput` breaks `merkleBreaksBinding`, or every accepted run's valid-length
challenges accept the proof `V.proofOfTable x (kilianExtractTableFromRuns ...)`. -/
theorem accepts_kilianExtractTableFromRuns_or_breaksBinding
    {H : List Bool → List Bool → List Bool} {V : PCPVerifier α} {n : ℕ} {k : List Bool}
    {x : α} {root : List Bool} {runs : List KilianChallengeRun} :
    merkleBreaksBinding H (fun _ leaf => leaf.length == 1) n k
        (kilianRunsBindingOutput H V k x root runs) = true ∨
      ∀ run ∈ runs, kilianVerify H V k x root run.challenges run.response = true →
        ∀ ρ ∈ run.challenges, ρ.length = V.coins x →
          V.accepts x (V.proofOfTable x (kilianExtractTableFromRuns H V k x root runs)) ρ =
            true := by
  let raw := (runs.filter fun run =>
    kilianVerify H V k x root run.challenges run.response).flatMap fun run =>
      (kilianOpenings V x run.challenges run.response).map fun pair =>
        let (addr, opening) := pair
        ({ position := kilianPosition V x addr,
           opening := ⟨[opening.leaf], opening.path⟩ } : MerkleIndexedOpening)
  rcases getD_merkleExtractVector_or_merkleBreaksBinding (H := H)
      (leafSpace := fun _ leaf => leaf.length == 1) (n := n) (k := k) (d := kilianDepth V x)
      (len := (V.queryTable x).length) (root := root) [false] (openings := raw)
      (fun entry hent => by simp [mem_kilianRunsToOpenings_leaf_len hent]) with
    hbreak | hcons
  · exact Or.inl hbreak
  · refine Or.inr fun run hrun hver ρ hρ hρlen => ?_
    rw [PCPVerifier.accepts_proofOfTable x _ ρ hρlen]
    have hacc := hver
    simp only [kilianVerify, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hacc
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hρ
    have hi' : i < run.response.length := hacc.1 ▸ hi
    have hmem : (run.challenges[i], run.response[i]) ∈ run.challenges.zip run.response :=
      List.mem_iff_getElem.mpr ⟨i, by simp [hi, hi'], by simp⟩
    have hc := hacc.2 _ hmem
    simp only [kilianCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
    convert hc.2 using 3
    refine List.ext_getElem (by simp [hc.1.1]) fun m h₁ h₂ => ?_
    have hmq : m < (V.queries (x, run.challenges[i])).length := by simpa using h₁
    set q := (V.queries (x, run.challenges[i]))[m]
    have hko : (q, run.response[i][m]'(by simpa using h₂)) ∈
        kilianOpenings V x run.challenges run.response :=
      List.mem_flatMap.mpr ⟨_, hmem,
        List.mem_iff_getElem.mpr ⟨m, by simp [hmq, by simpa using h₂], by simp [q]⟩⟩
    have hqlt : kilianPosition V x q < (V.queryTable x).length :=
      kilianPosition_lt hρlen (List.getElem_mem hmq)
    let entry : MerkleIndexedOpening :=
      { position := kilianPosition V x q,
        opening := ⟨[run.response[i][m].leaf], run.response[i][m].path⟩ }
    have hentVer : entry ∈ merkleVerifiedOpenings H k (kilianDepth V x) (V.queryTable x).length
        root raw :=
      mem_merkleVerifiedOpenings.mpr
        ⟨List.mem_flatMap.mpr ⟨run, List.mem_filter.mpr ⟨hrun, hver⟩,
          List.mem_map.mpr ⟨_, hko, rfl⟩⟩, hqlt, merkleVerify_of_mem_kilianOpenings hver hko⟩
    have hvec : (merkleExtractVector (V.queryTable x).length [false]
        (kilianRunsToOpenings H V k x root runs)).getD (kilianPosition V x q) [false] =
      [run.response[i][m].leaf] := hcons entry hentVer
    have hltVec : kilianPosition V x q <
        (merkleExtractVector (V.queryTable x).length [false]
          (kilianRunsToOpenings H V k x root runs)).length := by
      simpa [length_merkleExtractVector] using hqlt
    rw [List.getElem_map, List.getElem_map]
    dsimp only [kilianExtractTableFromRuns, kilianPosition] at hvec hltVec ⊢
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hltVec, Option.getD_some] at hvec
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hltVec,
      Option.map_some, Option.getD_some]
    exact congrArg (fun l => l.headD false) hvec

/-! ### Rewinding table extractor and strict-PPT certificates -/

/-- Run `P.answer` once on `n` challenges with coordinate `i` fixed to `ρ₀` and the other `n - 1`
coordinates sampled independently from `BitString.sampleList (V.coins cm.stmt)`. -/
noncomputable def kilianPlantedRun (V : PCPVerifier α) (P : KilianProver α)
    (n : ℕ) (cm : KilianCommitment α) (ρ₀ : List Bool) (i : ℕ) :
    ProbComp KilianChallengeRun := do
  let ρs ← kilianChallenges V n cm.stmt
  let ρs' := ρs.set i ρ₀
  let resp ← P.answer n cm.state ρs'
  return { challenges := ρs', response := resp }

/-- Rewind `P.answer` across all `V.coins cm.stmt`-bit PCP coins `ρ₀`, all `n` slots
`i ∈ List.range n`, and `T n` fresh trials per `(ρ₀, i)`. -/
noncomputable def kilianCollectRuns (V : PCPVerifier α) (P : KilianProver α) (T : ℕ → ℕ)
    (n : ℕ) (cm : KilianCommitment α) : ProbComp (List KilianChallengeRun) := do
  let nested ← (BitString.enumList (V.coins cm.stmt)).mapM fun ρ₀ =>
    (List.range n).mapM fun i =>
      OracleComp.replicate (T n) (kilianPlantedRun V P n cm ρ₀ i)
  return nested.flatten.flatten

/-- Uniform strict-PPT rewinding table extractor for Kilian's protocol: commits once with
`P.commit`, collects rewound transcripts via `kilianCollectRuns`, and reconstructs a compact PCP
table via `kilianExtractTableFromRuns`. -/
noncomputable def kilianTableExtractor (H : List Bool → List Bool → List Bool) (V : PCPVerifier α)
    (P : KilianProver α) (T : ℕ → ℕ) (n : ℕ) (k : List Bool) :
    ProbComp (KilianExtractedTable α) := do
  let cm ← P.commit n k
  let runs ← kilianCollectRuns V P T n cm
  return { stmt := cm.stmt, root := cm.root,
           table := kilianExtractTableFromRuns H V k cm.stmt cm.root runs }

/-- Binding adversary paired with `kilianTableExtractor`: executes the identical rewinding
collection and emits any conflicting pair of accepted openings found in the transcripts. -/
noncomputable def kilianExtractorBindingAdversary (H : List Bool → List Bool → List Bool)
    (V : PCPVerifier α) (P : KilianProver α) (T : ℕ → ℕ) : MerkleBindingAdversary :=
  fun n k => do
    let cm ← P.commit n k
    let runs ← kilianCollectRuns V P T n cm
    return kilianRunsBindingOutput H V k cm.stmt cm.root runs

/-- Strict-fraction table-extraction experiment: runs `kilianTableExtractor` and returns `true`
iff the expanded proof `V.proofOfTable ext.stmt ext.table` passes strictly more than `num / den`
fraction of all `2 ^ V.coins ext.stmt` PCP coins. -/
noncomputable def kilianExtractionFracGame (H : List Bool → List Bool → List Bool)
    (V : PCPVerifier α) (P : KilianProver α) (T : ℕ → ℕ) (num den n : ℕ) : ProbComp Bool := do
  let k ← BitString.sampleList n
  let ext ← kilianTableExtractor H V P T n k
  return decide
    (num * 2 ^ V.coins ext.stmt <
      den * acceptCount
        (fun y => V.accepts y.1 (V.proofOfTable ext.stmt ext.table) y.2)
        ext.stmt (V.coins ext.stmt))

section Efficiency

private theorem listSet_eq_map_zipIdx {β : Type} (l : List β) (i : ℕ) (v : β) :
    l.set i v = l.zipIdx.map fun entry => if entry.2 == i then v else entry.1 := by
  apply List.ext_getElem (by simp)
  intro j hj₁ hj₂
  have hj : j < l.length := by simpa using hj₁
  simp only [List.getElem_set, List.getElem_map, List.getElem_zipIdx, Nat.zero_add, beq_iff_eq]
  by_cases heq : i = j
  · simp [heq]
  · have hne : j ≠ i := fun h => heq h.symm
    simp [heq, hne]

private theorem computableInPolyTime_listSet {β Γ : Type} {encB : β ↪ List Bool}
    {encIn : Γ ↪ List Bool} {l : Γ → List β} {i : Γ → ℕ} {v : Γ → β}
    (hl : ComputableInPolyTime l encIn (encList encB))
    (hi : ComputableInPolyTime i encIn encUnary)
    (hv : ComputableInPolyTime v encIn encB) :
    ComputableInPolyTime (fun x => (l x).set (i x) (v x)) encIn (encList encB) := by
  simp_rw [listSet_eq_map_zipIdx]
  have hzip : ComputableInPolyTime (fun x => (l x).zipIdx) encIn
      (encList (encPair encB encUnary)) :=
    (ComputableInPolyTime.zipIdx encB).comp hl
  refine ComputableInPolyTime.mapWithInput hzip ?_
  have htest : ComputableInPolyTime
      (fun p : Γ × (β × ℕ) => p.2.2 == i p.1)
      (encPair encIn (encPair encB encUnary)) encBool :=
    ComputableInPolyTime.beq (encB := encUnary) (by fun_prop)
      (hi.comp (ComputableInPolyTime.fst _ _))
  exact ComputableInPolyTime.ite htest (hv.comp (ComputableInPolyTime.fst _ _)) (by fun_prop)

private theorem computableInPolyTime_kilianRunsToOpenings {H : List Bool → List Bool → List Bool}
    {V : PCPVerifier α} {enc : α ↪ List Bool} {c : ℕ} {γ : Type} {encIn : γ ↪ List Bool}
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length)
    (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1))
    {k root : γ → List Bool} {x : γ → α} {runs : γ → List KilianChallengeRun}
    (hk : ComputableInPolyTime k encIn encBits)
    (hx : ComputableInPolyTime x encIn enc)
    (hroot : ComputableInPolyTime root encIn encBits)
    (hruns : ComputableInPolyTime runs encIn (encList encKilianChallengeRun)) :
    ComputableInPolyTime
      (fun a => kilianRunsToOpenings H V (k a) (x a) (root a) (runs a))
      encIn (encList encMerkleIndexedOpening) := by
  have htable := (PCPVerifier.isPolyTime_queryTable hV hcoins).comp hx
  have hlenVec := (ComputableInPolyTime.length_list encNat).comp htable
  have hd := (ComputableInPolyTime.unary_clog_const 2).comp hlenVec
  have ha := ComputableInPolyTime.fst encIn encKilianChallengeRun
  have hb := ComputableInPolyTime.snd encIn encKilianChallengeRun
  have hview : ComputableInPolyTime
      (fun p : γ × KilianChallengeRun =>
        ({ key := k p.1, stmt := x p.1, root := root p.1,
           challenges := p.2.challenges, response := p.2.response } : KilianView α))
      (encPair encIn encKilianChallengeRun) (encKilianView enc) := by fun_prop
  have hverRuns : ComputableInPolyTime
      (fun p : γ × KilianChallengeRun =>
        kilianVerify H V (k p.1) (x p.1) (root p.1) p.2.challenges p.2.response)
      (encPair encIn encKilianChallengeRun) encBool :=
    (computableInPolyTime_kilianVerify hH hlen hV hcoins).comp hview
  have hfiltered := ComputableInPolyTime.filterWithInput
    (test := fun a run => kilianVerify H V (k a) (x a) (root a) run.challenges run.response)
    hruns hverRuns
  have hko := (computableInPolyTime_kilianOpenings hV).comp
    ((hx.comp ha).prod ((encKilianChallengeRun_challenges_polyTime hb).prod
      (encKilianChallengeRun_response_polyTime hb)))
  have hq₁ := ComputableInPolyTime.fst (encPair encIn encKilianChallengeRun)
    (encPair encNat encKilianOpening)
  have hq₂ := ComputableInPolyTime.snd (encPair encIn encKilianChallengeRun)
    (encPair encNat encKilianOpening)
  have hop := (ComputableInPolyTime.snd encNat encKilianOpening).comp hq₂
  have hopenRuns : ComputableInPolyTime
      (fun p : γ × KilianChallengeRun =>
        (kilianOpenings V (x p.1) p.2.challenges p.2.response).map fun pair =>
          let (addr, opening) := pair
          ({ position := kilianPosition V (x p.1) addr,
             opening := ⟨[opening.leaf], opening.path⟩ } : MerkleIndexedOpening))
      (encPair encIn encKilianChallengeRun) (encList encMerkleIndexedOpening) :=
    ComputableInPolyTime.mapWithInput hko
      (encMerkleIndexedOpening_mk_polyTime
        (ComputableInPolyTime.idxOfWithInput (htable.comp (ha.comp hq₁))
          ((ComputableInPolyTime.fst encNat encKilianOpening).comp hq₂))
        (encMerkleOpening_mk_polyTime
          (ComputableInPolyTime.bitsCons (encKilianOpening_leaf_polyTime hop) (.const []))
          (encKilianOpening_path_polyTime hop)))
  exact computableInPolyTime_merkleVerifiedOpenings hH hlen hk hd hlenVec hroot
    (ComputableInPolyTime.flatMapWithInput hfiltered hopenRuns)

private theorem computableInPolyTime_kilianExtractTableFromRuns
    {H : List Bool → List Bool → List Bool} {V : PCPVerifier α} {enc : α ↪ List Bool} {c : ℕ}
    {γ : Type} {encIn : γ ↪ List Bool}
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length)
    (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1))
    {k root : γ → List Bool} {x : γ → α} {runs : γ → List KilianChallengeRun}
    (hk : ComputableInPolyTime k encIn encBits)
    (hx : ComputableInPolyTime x encIn enc)
    (hroot : ComputableInPolyTime root encIn encBits)
    (hruns : ComputableInPolyTime runs encIn (encList encKilianChallengeRun)) :
    ComputableInPolyTime
      (fun a => kilianExtractTableFromRuns H V (k a) (x a) (root a) (runs a))
      encIn encBits := by
  have hlenVec : ComputableInPolyTime (fun a => (V.queryTable (x a)).length) encIn encUnary :=
    (ComputableInPolyTime.length_list encNat).comp
      ((PCPVerifier.isPolyTime_queryTable hV hcoins).comp hx)
  have hopen := computableInPolyTime_kilianRunsToOpenings hH hlen hV hcoins hk hx hroot hruns
  have hvec := computableInPolyTime_merkleExtractVector hlenVec
    (ComputableInPolyTime.const [false]) hopen
  unfold kilianExtractTableFromRuns
  exact ComputableInPolyTime.mapToBitsWithInput hvec
    ((ComputableInPolyTime.headD (encA := encBool) (encL := encBits) false).comp
      (ComputableInPolyTime.snd encIn encBits))

private abbrev KilianStage0 (α : Type) := (ℕ × List Bool) × KilianCommitment α
private abbrev KilianStage1 (α : Type) := KilianStage0 α × List Bool
private abbrev KilianStage2 (α : Type) := KilianStage1 α × ℕ

private abbrev encKilianStage0 (enc : α ↪ List Bool) : KilianStage0 α ↪ List Bool :=
  encPair (encPair encUnary encBits) (encKilianCommitment enc)

private abbrev encKilianStage1 (enc : α ↪ List Bool) : KilianStage1 α ↪ List Bool :=
  encPair (encKilianStage0 enc) encBits

private abbrev encKilianStage2 (enc : α ↪ List Bool) : KilianStage2 α ↪ List Bool :=
  encPair (encKilianStage1 enc) encUnary

private theorem cpt_kilianStage0_n {enc : α ↪ List Bool} :
    ComputableInPolyTime (fun p : KilianStage0 α => p.1.1) (encKilianStage0 enc) encUnary :=
  (ComputableInPolyTime.fst encUnary encBits).comp
    (ComputableInPolyTime.fst (encPair encUnary encBits) (encKilianCommitment enc))

private theorem cpt_kilianStage0_cm {enc : α ↪ List Bool} :
    ComputableInPolyTime (fun p : KilianStage0 α => p.2) (encKilianStage0 enc)
      (encKilianCommitment enc) :=
  ComputableInPolyTime.snd (encPair encUnary encBits) (encKilianCommitment enc)

private theorem cpt_kilianStage0_stmt {enc : α ↪ List Bool} :
    ComputableInPolyTime (fun p : KilianStage0 α => p.2.stmt) (encKilianStage0 enc) enc :=
  encKilianMessage_stmt_polyTime enc
    (encKilianCommitment_toKilianMessage_polyTime enc cpt_kilianStage0_cm)

private theorem cpt_kilianStage2_n {enc : α ↪ List Bool} :
    ComputableInPolyTime (fun q : KilianStage2 α => q.1.1.1.1) (encKilianStage2 enc) encUnary :=
  cpt_kilianStage0_n.comp
    ((ComputableInPolyTime.fst (encKilianStage0 enc) encBits).comp
      (ComputableInPolyTime.fst (encKilianStage1 enc) encUnary))

attribute [local irreducible] ComputableInPolyTime IsPPTOn in
private theorem isPPTOn_kilianPlantedRun {V : PCPVerifier α} {enc : α ↪ List Bool} {c : ℕ}
    {P : KilianProver α}
    (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1))
    (hP : P.IsPPT enc) :
    IsPPTOn (encKilianStage2 enc) encKilianChallengeRun
      (fun q => kilianPlantedRun V P q.1.1.1.1 q.1.1.2 q.1.2 q.2) := by
  have hs₁_s0 := ComputableInPolyTime.fst (encKilianStage0 enc) encBits
  have hs₂_s₁ := ComputableInPolyTime.fst (encKilianStage1 enc) encUnary
  have hstmt₂ := cpt_kilianStage0_stmt.comp (hs₁_s0.comp hs₂_s₁)
  have hcm₂ := cpt_kilianStage0_cm.comp (hs₁_s0.comp hs₂_s₁)
  have hchal : IsPPTOn (encKilianStage2 enc) (encList encBits)
      (fun q => kilianChallenges V q.1.1.1.1 q.1.1.2.stmt) :=
    (isPPTOn_kilianChallenges hV hcoins).preprocess
      (prepare := fun q : KilianStage2 α => (q.1.1.1.1, q.1.1.2.stmt))
      (cpt_kilianStage2_n.prod hstmt₂)
  refine IsPPTOn.bind_with hchal ?_
  have hp1 := ComputableInPolyTime.fst (encKilianStage2 enc) (encList encBits)
  have hl := ComputableInPolyTime.snd (encKilianStage2 enc) (encList encBits)
  have hi := (ComputableInPolyTime.snd (encKilianStage1 enc) encUnary).comp hp1
  have hv := (ComputableInPolyTime.snd (encKilianStage0 enc) encBits).comp (hs₂_s₁.comp hp1)
  have hset : ComputableInPolyTime
      (fun p : KilianStage2 α × List (List Bool) => p.2.set p.1.2 p.1.1.2)
      (encPair (encKilianStage2 enc) (encList encBits)) (encList encBits) :=
    computableInPolyTime_listSet hl hi hv
  have hans : IsPPTOn (encPair (encKilianStage2 enc) (encList encBits)) encKilianResponse
      (fun p => P.answer p.1.1.1.1.1 p.1.1.1.2.state (p.2.set p.1.2 p.1.1.2)) :=
    hP.answer.preprocess
      (prepare := fun p : KilianStage2 α × List (List Bool) =>
        (p.1.1.1.1.1, p.1.1.1.2.state, p.2.set p.1.2 p.1.1.2))
      ((cpt_kilianStage2_n.comp hp1).prod
        ((encKilianCommitment_state_polyTime enc (hcm₂.comp hp1)).prod hset))
  refine IsPPTOn.bind_with hans (ComputableInPolyTime.isPPTOn ?_)
  have hq1 := ComputableInPolyTime.fst (encPair (encKilianStage2 enc) (encList encBits))
    encKilianResponse
  have hq2 := ComputableInPolyTime.snd (encPair (encKilianStage2 enc) (encList encBits))
    encKilianResponse
  exact encKilianChallengeRun_mk_polyTime (hset.comp hq1) hq2

attribute [local irreducible] ComputableInPolyTime IsPPTOn in
private theorem isPPTOn_kilianCollectRuns {V : PCPVerifier α} {enc : α ↪ List Bool} {c : ℕ}
    {P : KilianProver α} {T : ℕ → ℕ}
    (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1))
    (hP : P.IsPPT enc)
    (hT : ComputableInPolyTime T encUnary encUnary) :
    IsPPTOn (encKilianStage0 enc) (encList encKilianChallengeRun)
      (fun p => kilianCollectRuns V P T p.1.1 p.2) := by
  have hs₁_s0 := ComputableInPolyTime.fst (encKilianStage0 enc) encBits
  have hrep : IsPPTOn (encKilianStage2 enc) (encList encKilianChallengeRun)
      (fun q => OracleComp.replicate (T q.1.1.1.1)
        (kilianPlantedRun V P q.1.1.1.1 q.1.1.2 q.1.2 q.2)) :=
    IsPPTOn.replicate (isPPTOn_kilianPlantedRun hV hcoins hP) (hT.comp cpt_kilianStage2_n)
  have hinner : IsPPTOn (encKilianStage1 enc) (encList (encList encKilianChallengeRun))
      (fun p => (List.range p.1.1.1).mapM fun i =>
        OracleComp.replicate (T p.1.1.1) (kilianPlantedRun V P p.1.1.1 p.1.2 p.2 i)) :=
    IsPPTOn.mapMWith (element := encUnary) (program := fun p i =>
      OracleComp.replicate (T p.1.1.1) (kilianPlantedRun V P p.1.1.1 p.1.2 p.2 i))
      hrep (ComputableInPolyTime.range.comp (cpt_kilianStage0_n.comp hs₁_s0))
  have henumCoins : ComputableInPolyTime
      (fun a : KilianStage0 α => BitString.enumList (V.coins a.2.stmt))
      (encKilianStage0 enc) (encList encBits) :=
    (PCPVerifier.isPolyTime_enumCoins hV hcoins).comp cpt_kilianStage0_stmt
  have houter : IsPPTOn (encKilianStage0 enc) (encList (encList (encList encKilianChallengeRun)))
      (fun a => (BitString.enumList (V.coins a.2.stmt)).mapM fun ρ₀ =>
        (List.range a.1.1).mapM fun i =>
          OracleComp.replicate (T a.1.1) (kilianPlantedRun V P a.1.1 a.2 ρ₀ i)) :=
    IsPPTOn.mapMWith (element := encBits) (program := fun a ρ₀ =>
      (List.range a.1.1).mapM fun i =>
        OracleComp.replicate (T a.1.1) (kilianPlantedRun V P a.1.1 a.2 ρ₀ i))
      hinner henumCoins
  refine IsPPTOn.bind_with houter (ComputableInPolyTime.isPPTOn ?_)
  exact ((ComputableInPolyTime.flatten encKilianChallengeRun).comp
    (ComputableInPolyTime.flatten (encList encKilianChallengeRun))).comp
      (ComputableInPolyTime.snd (encKilianStage0 enc)
        (encList (encList (encList encKilianChallengeRun))))

private theorem isPPT_kilianCollectPost {V : PCPVerifier α} {enc : α ↪ List Bool} {c : ℕ}
    {P : KilianProver α} {T : ℕ → ℕ} {β : Type} {encOut : β ↪ List Bool}
    (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1))
    (hP : P.IsPPT enc)
    (hT : ComputableInPolyTime T encUnary encUnary)
    (post : List Bool → α → List Bool → List KilianChallengeRun → β)
    (hpost :
      let encE := encPair (encKilianStage0 enc) (encList encKilianChallengeRun)
      ∀ {k root : KilianStage0 α × List KilianChallengeRun → List Bool}
        {x : KilianStage0 α × List KilianChallengeRun → α}
        {runs : KilianStage0 α × List KilianChallengeRun → List KilianChallengeRun},
        ComputableInPolyTime k encE encBits →
        ComputableInPolyTime x encE enc →
        ComputableInPolyTime root encE encBits →
        ComputableInPolyTime runs encE (encList encKilianChallengeRun) →
        ComputableInPolyTime (fun q => post (k q) (x q) (root q) (runs q)) encE encOut) :
    IsPPT encOut (fun n k => do
      let cm ← P.commit n k
      let runs ← kilianCollectRuns V P T n cm
      return post k cm.stmt cm.root runs) := by
  change IsPPTOn (encPair encUnary encBits) encOut (fun p => do
    let cm ← P.commit p.1 p.2
    let runs ← kilianCollectRuns V P T p.1 cm
    return post p.2 cm.stmt cm.root runs)
  refine IsPPTOn.bind_with hP.commit.on ?_
  refine IsPPTOn.bind_with (isPPTOn_kilianCollectRuns hV hcoins hP hT) ?_
  refine ComputableInPolyTime.isPPTOn ?_
  let encE := encPair (encKilianStage0 enc) (encList encKilianChallengeRun)
  have h1 := ComputableInPolyTime.fst (encKilianStage0 enc) (encList encKilianChallengeRun)
  have hk : ComputableInPolyTime (fun q : KilianStage0 α × List KilianChallengeRun => q.1.1.2)
      encE encBits :=
    (ComputableInPolyTime.snd encUnary encBits).comp
      ((ComputableInPolyTime.fst (encPair encUnary encBits) (encKilianCommitment enc)).comp h1)
  have hmsg := encKilianCommitment_toKilianMessage_polyTime enc (cpt_kilianStage0_cm.comp h1)
  have hx := encKilianMessage_stmt_polyTime enc hmsg
  have hroot := encKilianMessage_root_polyTime enc hmsg
  have hruns := ComputableInPolyTime.snd (encKilianStage0 enc) (encList encKilianChallengeRun)
  exact hpost hk hx hroot hruns

/-- **Uniform strict-PPT efficiency of `kilianTableExtractor`**: when `H`, `V`, `P`, and the
rewind count `T` are polynomial-time / strict PPT (and `V` uses `O(log |enc x|)` coins),
`kilianTableExtractor` is uniform strict PPT. -/
theorem isPPT_kilianTableExtractor {H : List Bool → List Bool → List Bool} {V : PCPVerifier α}
    {enc : α ↪ List Bool} {c : ℕ} {P : KilianProver α} {T : ℕ → ℕ}
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length)
    (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1))
    (hP : P.IsPPT enc)
    (hT : ComputableInPolyTime T encUnary encUnary) :
    IsPPT (encKilianExtractedTable enc) (kilianTableExtractor H V P T) :=
  isPPT_kilianCollectPost hV hcoins hP hT
    (fun k x root runs => ({ stmt := x, root := root,
                             table := kilianExtractTableFromRuns H V k x root runs } :
      KilianExtractedTable α))
    fun hk hx hroot hruns =>
      encKilianExtractedTable_mk_polyTime enc hx hroot
        (computableInPolyTime_kilianExtractTableFromRuns hH hlen hV hcoins hk hx hroot hruns)

/-- **Uniform strict-PPT efficiency of `kilianExtractorBindingAdversary`**: the conflict-emitting
binding adversary paired with `kilianTableExtractor` is uniform strict PPT under the same
hypotheses. -/
theorem isPPT_kilianExtractorBindingAdversary {H : List Bool → List Bool → List Bool}
    {V : PCPVerifier α} {enc : α ↪ List Bool} {c : ℕ} {P : KilianProver α} {T : ℕ → ℕ}
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length)
    (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1))
    (hP : P.IsPPT enc)
    (hT : ComputableInPolyTime T encUnary encUnary) :
    IsPPT encMerkleBindingOutput (kilianExtractorBindingAdversary H V P T) :=
  isPPT_kilianCollectPost hV hcoins hP hT
    (fun k x root runs => kilianRunsBindingOutput H V k x root runs)
    fun hk hx hroot hruns =>
      computableInPolyTime_merkleVectorBindingOutput hroot
        (computableInPolyTime_kilianRunsToOpenings hH hlen hV hcoins hk hx hroot hruns)

end Efficiency

/-! ### Exact finite-parameter rewinding extraction bound -/

section Bound

private noncomputable def kilianCommitStage (P : KilianProver α) (n : ℕ) :
    ProbComp (List Bool × KilianCommitment α) := do
  let k ← BitString.sampleList n
  let cm ← P.commit n k
  return (k, cm)

private noncomputable def kilianSingleRun (V : PCPVerifier α) (P : KilianProver α)
    (n : ℕ) (cm : KilianCommitment α) : ProbComp KilianChallengeRun := do
  let ρs ← kilianChallenges V n cm.stmt
  let resp ← P.answer n cm.state ρs
  return { challenges := ρs, response := resp }

private theorem mem_support_kilianCommitStage {P : KilianProver α} {n : ℕ}
    {s : List Bool × KilianCommitment α}
    (hs : s ∈ (ProbComp.eval (kilianCommitStage P n)).support) :
    s.1.length = n ∧ s.2 ∈ (ProbComp.eval (P.commit n s.1)).support := by
  supp_cases hs [kilianCommitStage, BitString.eval_sampleList] with ⟨k, hk, cm, hcm, rfl⟩
  exact ⟨BitString.length_of_mem_support_uniformList hk, hcm⟩

private theorem eval_kilianAcceptGame (H : List Bool → List Bool → List Bool)
    (V : PCPVerifier α) (P : KilianProver α) (n : ℕ) :
    ProbComp.eval (kilianAcceptGame H V P n) =
      (ProbComp.eval (kilianCommitStage P n)).bind fun s =>
        (ProbComp.eval (kilianSingleRun V P n s.2)).map fun run =>
          kilianVerify H V s.1 s.2.stmt s.2.root run.challenges run.response := by
  simp [kilianAcceptGame, kilianCommitStage, kilianSingleRun, ProbComp.eval_bind,
    ProbComp.eval_map, PMF.bind_bind, PMF.map_bind, PMF.map_comp, Function.comp_def]

private theorem eval_merkleBindingGame_extractor (H : List Bool → List Bool → List Bool)
    (V : PCPVerifier α) (P : KilianProver α) (T : ℕ → ℕ) (n : ℕ) :
    ProbComp.eval (merkleBindingGame H (fun _ leaf => leaf.length == 1)
        (kilianExtractorBindingAdversary H V P T) n) =
      (ProbComp.eval (kilianCommitStage P n)).bind fun s =>
        (ProbComp.eval (kilianCollectRuns V P T n s.2)).map fun runs =>
          merkleBreaksBinding H (fun _ leaf => leaf.length == 1) n s.1
            (kilianRunsBindingOutput H V s.1 s.2.stmt s.2.root runs) := by
  simp [merkleBindingGame, kilianExtractorBindingAdversary, kilianCommitStage,
    ProbComp.eval_bind, ProbComp.eval_map, PMF.bind_bind, Function.comp_def]

private theorem eval_kilianExtractionFracGame (H : List Bool → List Bool → List Bool)
    (V : PCPVerifier α) (P : KilianProver α) (T : ℕ → ℕ) (num den n : ℕ) :
    ProbComp.eval (kilianExtractionFracGame H V P T num den n) =
      (ProbComp.eval (kilianCommitStage P n)).bind fun s =>
        (ProbComp.eval (kilianCollectRuns V P T n s.2)).map fun runs =>
          decide (num * 2 ^ V.coins s.2.stmt <
            den * acceptCount
              (fun y => V.accepts y.1
                (V.proofOfTable s.2.stmt
                  (kilianExtractTableFromRuns H V s.1 s.2.stmt s.2.root runs))
                y.2)
              s.2.stmt (V.coins s.2.stmt)) := by
  simp [kilianExtractionFracGame, kilianTableExtractor, kilianCommitStage,
    ProbComp.eval_bind, ProbComp.eval_map, PMF.bind_bind, Function.comp_def]

private theorem map_apply_true {γ : Type*} (p : PMF γ) (f : γ → Bool) :
    (p.map f) true = p.toOuterMeasure {x | f x = true} := by
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  rfl

private theorem listSet_append_cons {β : Type} (front : List β) (middle : β) (back : List β)
    (v : β) : (front ++ middle :: back).set front.length v = front ++ v :: back := by
  induction front with
  | nil => rfl
  | cons a front ih => simp [ih]

private theorem eval_kilianChallenges_set (V : PCPVerifier α) (n i : ℕ) (hi : i < n) (x : α) :
    ProbComp.eval (do
      let ρ₀ ← BitString.sampleList (V.coins x)
      let ρs ← kilianChallenges V n x
      pure (ρs.set i ρ₀)) =
      ProbComp.eval (kilianChallenges V n x) := by
  let src := BitString.sampleList (V.coins x)
  have hsp := ProbComp.eval_replicate_splice src i (n - 1 - i)
  rw [kilianChallenges, show n = i + ((n - 1 - i) + 1) by omega]
  simp only [ProbComp.eval_bind, ProbComp.eval_pure]
  conv_lhs => arg 2; ext ρ₀; rw [← hsp]
  rw [← hsp]
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  refine congrArg (PMF.bind (ProbComp.eval src)) (funext fun ρ₀ => ?_)
  rw [PMF.bind_comm (ProbComp.eval src) (ProbComp.eval (OracleComp.replicate i src))]
  refine Probability.PMF.bind_congr_on_support _ _ _ fun front hfront => ?_
  have hlen : front.length = i := ((ProbComp.mem_support_replicate_iff i src front).mp hfront).1
  simp only [← hlen, listSet_append_cons, PMF.bind_const]

private theorem eval_kilianSingleRun_eq_bind_planted (V : PCPVerifier α) (P : KilianProver α)
    (n i : ℕ) (hi : i < n) (cm : KilianCommitment α) :
    ProbComp.eval (kilianSingleRun V P n cm) =
      (ProbComp.eval (BitString.sampleList (V.coins cm.stmt))).bind fun ρ₀ =>
        ProbComp.eval (kilianPlantedRun V P n cm ρ₀ i) := by
  have hchal := eval_kilianChallenges_set V n i hi cm.stmt
  simp only [kilianSingleRun, kilianPlantedRun, ProbComp.eval_bind]
  conv_lhs => rw [← hchal]
  simp [ProbComp.eval_bind, PMF.bind_bind, Function.comp_def]

private theorem mem_of_mem_support_kilianPlantedRun {V : PCPVerifier α} {P : KilianProver α}
    {n i : ℕ} (hi : i < n) {cm : KilianCommitment α} {ρ₀ : List Bool}
    {run : KilianChallengeRun}
    (hrun : run ∈ (ProbComp.eval (kilianPlantedRun V P n cm ρ₀ i)).support) :
    run.challenges[i]? = some ρ₀ ∧ ρ₀ ∈ run.challenges := by
  supp_cases hrun [kilianPlantedRun] with ⟨ρs, hρs, resp, -, rfl⟩
  rw [kilianChallenges, ProbComp.mem_support_replicate_iff] at hρs
  have hi' : i < ρs.length := hρs.1.symm ▸ hi
  have hget : (ρs.set i ρ₀)[i]? = some ρ₀ := by simp [hi']
  exact ⟨hget, List.mem_of_getElem? hget⟩

private theorem toOuterMeasure_kilianSingleRun_getElem_le (V : PCPVerifier α) (P : KilianProver α)
    (n i : ℕ) (hi : i < n) (cm : KilianCommitment α) (ρ₀ : List Bool)
    (acc : KilianChallengeRun → Bool) :
    (ProbComp.eval (kilianSingleRun V P n cm)).toOuterMeasure
        {run | run.challenges[i]? = some ρ₀ ∧ acc run = true} ≤
      ((1 : ℝ≥0∞) / 2 ^ V.coins cm.stmt) *
        (ProbComp.eval (kilianPlantedRun V P n cm ρ₀ i)).toOuterMeasure {run | acc run = true} := by
  rw [eval_kilianSingleRun_eq_bind_planted V P n i hi cm, PMF.toOuterMeasure_bind_apply]
  have hsingle (ρ' : List Bool) :
      ProbComp.eval (BitString.sampleList (V.coins cm.stmt)) ρ' *
          (ProbComp.eval (kilianPlantedRun V P n cm ρ' i)).toOuterMeasure
            {run | run.challenges[i]? = some ρ₀ ∧ acc run = true} =
        if ρ' = ρ₀ then
          ProbComp.eval (BitString.sampleList (V.coins cm.stmt)) ρ₀ *
            (ProbComp.eval (kilianPlantedRun V P n cm ρ₀ i)).toOuterMeasure
              {run | run.challenges[i]? = some ρ₀ ∧ acc run = true}
        else 0 := by
    split_ifs with h
    · subst h; rfl
    · rw [← PMF.toOuterMeasure_apply_inter_support,
        show {run | run.challenges[i]? = some ρ₀ ∧ acc run = true} ∩
            (ProbComp.eval (kilianPlantedRun V P n cm ρ' i)).support = ∅ from
          Set.eq_empty_iff_forall_notMem.mpr fun run ⟨⟨hget, _⟩, hsup⟩ =>
            h (Option.some.inj ((mem_of_mem_support_kilianPlantedRun hi hsup).1.symm.trans hget)),
        MeasureTheory.measure_empty, mul_zero]
  rw [tsum_congr hsingle, tsum_ite_eq, BitString.eval_sampleList]
  exact mul_le_mul' (BitString.uniformList_apply_le _ _)
    (MeasureTheory.measure_mono fun _ h => h.2)

private theorem toOuterMeasure_mapM_all_le {β γ : Type} (bs : List β) (m : β → ProbComp γ)
    (Q : γ → Prop) {b₀ : β} (hb₀ : b₀ ∈ bs) :
    (ProbComp.eval (bs.mapM m)).toOuterMeasure {ys | ∀ y ∈ ys, Q y} ≤
      (ProbComp.eval (m b₀)).toOuterMeasure {y | Q y} := by
  induction bs with
  | nil => simp at hb₀
  | cons b bs ih =>
    have hmap : ProbComp.eval ((b :: bs).mapM m) =
        (ProbComp.eval (m b)).bind fun y =>
          (ProbComp.eval (bs.mapM m)).map fun ys => y :: ys := by
      simp [List.mapM_cons, ProbComp.eval_bind, ProbComp.eval_map, PMF.map, Function.comp_def]
    rw [hmap, PMF.toOuterMeasure_bind_apply]
    rcases List.mem_cons.mp hb₀ with rfl | hmem
    · rw [Probability.PMF.toOuterMeasure_eq_tsum_mul_indicator]
      refine tsum_le_tsum fun y => mul_le_mul_of_nonneg_left ?_ zero_le
      by_cases hy : Q y
      · simpa [Set.indicator_of_mem hy] using Probability.PMF.toOuterMeasure_le_one
          ((ProbComp.eval (bs.mapM m)).map (List.cons y)) {ys | ∀ z ∈ ys, Q z}
      · rw [PMF.toOuterMeasure_map_apply,
          show List.cons y ⁻¹' {ys | ∀ z ∈ ys, Q z} = ∅ by ext ys; simp [hy],
          MeasureTheory.measure_empty, Set.indicator_of_notMem hy]
    · refine Probability.PMF.tsum_mul_le_of_forall_le _ fun y => ?_
      rw [PMF.toOuterMeasure_map_apply]
      have hsub : List.cons y ⁻¹' {ys | ∀ z ∈ ys, Q z} ⊆ {ys | ∀ z ∈ ys, Q z} :=
        fun _ hys z hz => hys z (List.mem_cons_of_mem y hz)
      exact (MeasureTheory.measure_mono hsub).trans (ih hmem)

open Classical in
private noncomputable def kilianGoodCoins (H : List Bool → List Bool → List Bool)
    (V : PCPVerifier α) (P : KilianProver α) (n : ℕ) (k : List Bool) (cm : KilianCommitment α)
    (θ : ℝ) : List (List Bool) :=
  (BitString.enumList (V.coins cm.stmt)).filter fun ρ₀ =>
    decide (∃ i : Fin n, θ ≤
      ((ProbComp.eval (kilianPlantedRun V P n cm ρ₀ i.val)).toOuterMeasure
        {y | kilianVerify H V k cm.stmt cm.root y.challenges y.response = true}).toReal)

open Classical in
private theorem kilianSingleRun_bound_of_threshold
    (H : List Bool → List Bool → List Bool) (V : PCPVerifier α) (P : KilianProver α)
    (n : ℕ) (k : List Bool) (cm : KilianCommitment α) {θ : ℝ} (hθ0 : 0 ≤ θ) :
    let r := V.coins cm.stmt
    let acc : KilianChallengeRun → Bool :=
      fun run => kilianVerify H V k cm.stmt cm.root run.challenges run.response
    let good := kilianGoodCoins H V P n k cm θ
    (ProbComp.eval (kilianSingleRun V P n cm)).toOuterMeasure {y | acc y = true} ≤
      ((good.length : ℝ≥0∞) / 2 ^ r) ^ n + (n : ℝ≥0∞) * ENNReal.ofReal θ := by
  intro r acc good
  let run := ProbComp.eval (kilianSingleRun V P n cm)
  let bad := (BitString.enumList r).filter fun ρ₀ => decide (ρ₀ ∉ good)
  have hcov : {y | acc y = true} ∩ run.support ⊆
      {y | ∀ ρ ∈ y.challenges, ρ ∈ good} ∪
        ⋃ i : Fin n, ⋃ ρ₀ ∈ bad.toFinset,
          {y | y.challenges[i.val]? = some ρ₀ ∧ acc y = true} := by
    intro y ⟨hyacc, hysup⟩
    by_cases hgood : ∀ ρ ∈ y.challenges, ρ ∈ good
    · exact Or.inl hgood
    · refine Or.inr ?_
      push Not at hgood
      obtain ⟨ρ₀, hρ₀mem, hρ₀not⟩ := hgood
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hρ₀mem
      supp_cases hysup [run, kilianSingleRun] with ⟨ρs, hρs, resp, -, rfl⟩
      rw [kilianChallenges, ProbComp.mem_support_replicate_iff] at hρs
      have hbad : ρs[i] ∈ bad.toFinset := List.mem_toFinset.mpr <|
        List.mem_filter.mpr ⟨BitString.mem_enumList.mpr
          (BitString.length_of_mem_support_uniformList (by simpa using hρs.2 _ hρ₀mem)),
          decide_eq_true hρ₀not⟩
      exact Set.mem_iUnion.mpr ⟨⟨i, hρs.1 ▸ hi⟩, Set.mem_iUnion.mpr ⟨ρs[i],
        Set.mem_iUnion.mpr ⟨hbad, List.getElem?_eq_getElem hi, hyacc⟩⟩⟩
  have hsplit : run.toOuterMeasure {y | acc y = true} ≤
      run.toOuterMeasure {y | ∀ ρ ∈ y.challenges, ρ ∈ good} +
        ∑ i : Fin n, ∑ ρ₀ ∈ bad.toFinset,
          run.toOuterMeasure {y | y.challenges[i.val]? = some ρ₀ ∧ acc y = true} := by
    calc run.toOuterMeasure {y | acc y = true}
        = run.toOuterMeasure ({y | acc y = true} ∩ run.support) :=
          (PMF.toOuterMeasure_apply_inter_support _ _).symm
      _ ≤ run.toOuterMeasure ({y | ∀ ρ ∈ y.challenges, ρ ∈ good} ∪
            ⋃ i : Fin n, ⋃ ρ₀ ∈ bad.toFinset,
              {y | y.challenges[i.val]? = some ρ₀ ∧ acc y = true}) :=
          MeasureTheory.measure_mono hcov
      _ ≤ _ := (MeasureTheory.measure_union_le _ _).trans <| add_le_add le_rfl
          ((MeasureTheory.measure_iUnion_fintype_le _ _).trans
            (Finset.sum_le_sum fun _ _ => MeasureTheory.measure_biUnion_finset_le _ _))
  have hmap : run.map (fun y => y.challenges) = ProbComp.eval (kilianChallenges V n cm.stmt) := by
    simp only [run, kilianSingleRun, ProbComp.eval_bind, PMF.map_bind, ProbComp.eval_pure,
      PMF.pure_map, PMF.bind_const, PMF.bind_pure]
  have hpart1 : run.toOuterMeasure {y | ∀ ρ ∈ y.challenges, ρ ∈ good} ≤
      ((good.length : ℝ≥0∞) / 2 ^ r) ^ n := by
    calc run.toOuterMeasure {y | ∀ ρ ∈ y.challenges, ρ ∈ good}
        = (ProbComp.eval (kilianChallenges V n cm.stmt)).toOuterMeasure
            {ρs | ∀ ρ ∈ ρs, decide (ρ ∈ good) = true} := by
            rw [← hmap, PMF.toOuterMeasure_map_apply]
            congr 1
            ext y
            simp
      _ = ((ProbComp.eval (BitString.sampleList r)).toOuterMeasure
            {ρ | decide (ρ ∈ good) = true}) ^ n :=
            ProbComp.toOuterMeasure_replicate_forall _ _ n
      _ ≤ ((good.length : ℝ≥0∞) / 2 ^ r) ^ n := by
            refine pow_le_pow_left' ?_ n
            rw [BitString.eval_sampleList,
              show {ρ | decide (ρ ∈ good) = true} = (good.toFinset : Set (List Bool)) by ext; simp]
            refine (BitString.toOuterMeasure_uniformList_finset_le r good.toFinset).trans ?_
            rw [one_div, ← div_eq_mul_inv]
            gcongr; exact_mod_cast List.toFinset_card_le good
  have hpart2 : ∑ i : Fin n, ∑ ρ₀ ∈ bad.toFinset,
      run.toOuterMeasure {y | y.challenges[i.val]? = some ρ₀ ∧ acc y = true} ≤
      (n : ℝ≥0∞) * ENNReal.ofReal θ := by
    have hterm (i : Fin n) {ρ₀ : List Bool} (hρ₀ : ρ₀ ∈ bad.toFinset) :
        run.toOuterMeasure {y | y.challenges[i.val]? = some ρ₀ ∧ acc y = true} ≤
          ((1 : ℝ≥0∞) / 2 ^ r) * ENNReal.ofReal θ := by
      obtain ⟨hmemEnum, hnot⟩ := List.mem_filter.mp (List.mem_toFinset.mp hρ₀)
      have hlt : ((ProbComp.eval (kilianPlantedRun V P n cm ρ₀ i.val)).toOuterMeasure
          {y | acc y = true}).toReal < θ := by
        by_contra hge
        exact of_decide_eq_true hnot
          (List.mem_filter.mpr ⟨hmemEnum, decide_eq_true ⟨i, not_lt.mp hge⟩⟩)
      exact (toOuterMeasure_kilianSingleRun_getElem_le V P n i.val i.isLt cm ρ₀ acc).trans
        (mul_le_mul_of_nonneg_left
          ((ENNReal.le_ofReal_iff_toReal_le (Probability.PMF.toOuterMeasure_ne_top _ _) hθ0).mpr
            hlt.le) zero_le)
    calc ∑ i : Fin n, ∑ ρ₀ ∈ bad.toFinset,
            run.toOuterMeasure {y | y.challenges[i.val]? = some ρ₀ ∧ acc y = true}
        ≤ ∑ _ : Fin n, ∑ _ ∈ bad.toFinset, ((1 : ℝ≥0∞) / 2 ^ r) * ENNReal.ofReal θ :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun _ hρ₀ => hterm i hρ₀
      _ = (n : ℝ≥0∞) *
            ((bad.toFinset.card : ℝ≥0∞) * (((1 : ℝ≥0∞) / 2 ^ r) * ENNReal.ofReal θ)) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (n : ℝ≥0∞) * ((2 ^ r : ℝ≥0∞) * (((1 : ℝ≥0∞) / 2 ^ r) * ENNReal.ofReal θ)) := by
          gcongr
          exact_mod_cast (List.toFinset_card_le bad).trans
            ((List.length_filter_le _ _).trans (by rw [BitString.length_enumList]))
      _ = (n : ℝ≥0∞) * ENNReal.ofReal θ := by
          rw [← mul_assoc (2 ^ r : ℝ≥0∞), one_div,
            ENNReal.mul_inv_cancel (by positivity) (by finiteness), one_mul]
  exact hsplit.trans (add_le_add hpart1 hpart2)

open Classical in
private theorem kilianCollectRuns_cover_failure_le
    (H : List Bool → List Bool → List Bool) (V : PCPVerifier α) (P : KilianProver α)
    (T : ℕ → ℕ) (n M : ℕ) (k : List Bool) (cm : KilianCommitment α) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hM : 2 ^ V.coins cm.stmt ≤ M) :
    let acc : KilianChallengeRun → Bool :=
      fun run => kilianVerify H V k cm.stmt cm.root run.challenges run.response
    let good := kilianGoodCoins H V P n k cm θ
    (ProbComp.eval (kilianCollectRuns V P T n cm)).toOuterMeasure
        {runs | ∃ ρ₀ ∈ good, ∀ run ∈ runs, !(acc run && decide (ρ₀ ∈ run.challenges))} ≤
      (M : ℝ≥0∞) * ENNReal.ofReal ((1 - θ) ^ T n) := by
  intro acc good
  let r := V.coins cm.stmt
  let collected := ProbComp.eval (kilianCollectRuns V P T n cm)
  have hcovSet :
      {(runs : List KilianChallengeRun) |
          ∃ ρ₀ ∈ good, ∀ run ∈ runs, !(acc run && decide (ρ₀ ∈ run.challenges))} =
        ⋃ ρ₀ ∈ good.toFinset,
          {(runs : List KilianChallengeRun) |
            ∀ run ∈ runs, !(acc run && decide (ρ₀ ∈ run.challenges))} := by ext; simp
  rw [hcovSet]
  have hsingle (ρ₀ : List Bool) (hρ₀ : ρ₀ ∈ good.toFinset) :
      collected.toOuterMeasure {runs | ∀ run ∈ runs, !(acc run && decide (ρ₀ ∈ run.challenges))} ≤
        ENNReal.ofReal ((1 - θ) ^ T n) := by
    obtain ⟨hmem, hhex⟩ := List.mem_filter.mp (List.mem_toFinset.mp hρ₀)
    obtain ⟨i, hi⟩ := of_decide_eq_true hhex
    have hfailOne : (ProbComp.eval (kilianPlantedRun V P n cm ρ₀ i.val)).toOuterMeasure
        {y | !(acc y && decide (ρ₀ ∈ y.challenges)) = true} ≤ ENNReal.ofReal (1 - θ) := by
      have heqSupp : (ProbComp.eval (kilianPlantedRun V P n cm ρ₀ i.val)).toOuterMeasure
          {y | acc y = true} =
          (ProbComp.eval (kilianPlantedRun V P n cm ρ₀ i.val)).toOuterMeasure
            {y | (acc y && decide (ρ₀ ∈ y.challenges)) = true} := by
        rw [← PMF.toOuterMeasure_apply_inter_support (s := {y | acc y = true}),
          ← PMF.toOuterMeasure_apply_inter_support
            (s := {y | (acc y && decide (ρ₀ ∈ y.challenges)) = true})]
        refine congrArg (PMF.toOuterMeasure _) (Set.ext fun y => ⟨fun ⟨hy, hsup⟩ =>
          ⟨by simpa [Bool.and_eq_true] using
            And.intro hy (mem_of_mem_support_kilianPlantedRun i.isLt hsup).2, hsup⟩,
          fun ⟨hy, hsup⟩ => ⟨(Bool.and_eq_true _ _ |>.mp hy).1, hsup⟩⟩)
      rw [show {y : KilianChallengeRun | !(acc y && decide (ρ₀ ∈ y.challenges)) = true} =
          {y | (acc y && decide (ρ₀ ∈ y.challenges)) = true}ᶜ by
        ext y; by_cases hacc : acc y = true <;> simp [hacc]]
      refine (Probability.PMF.toOuterMeasure_compl_le_one_sub _ _
        (heqSupp ▸ ENNReal.ofReal_le_of_le_toReal hi)).trans_eq ?_
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hθ0]
    have hpre :
        ((fun nested : List (List (List KilianChallengeRun)) => nested.flatten.flatten) ⁻¹'
            {runs | ∀ run ∈ runs, !(acc run && decide (ρ₀ ∈ run.challenges))}) =
          {nested | ∀ x ∈ nested, ∀ z ∈ x, ∀ run ∈ z,
            !(acc run && decide (ρ₀ ∈ run.challenges))} := by
      ext nested
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, List.mem_flatten]
      exact ⟨fun h x hx z hz run hrun => h run ⟨z, ⟨x, hx, hz⟩, hrun⟩,
        fun h run ⟨z, ⟨x, hx, hz⟩, hrun⟩ => h x hx z hz run hrun⟩
    have hflat : collected =
        (ProbComp.eval ((BitString.enumList r).mapM fun ρ =>
          (List.range n).mapM fun j =>
            OracleComp.replicate (T n) (kilianPlantedRun V P n cm ρ j))).map
          (fun nested => nested.flatten.flatten) := by
      simp [collected, kilianCollectRuns, ProbComp.eval_map, r]
    calc collected.toOuterMeasure
          {runs | ∀ run ∈ runs, !(acc run && decide (ρ₀ ∈ run.challenges))}
        = (ProbComp.eval ((BitString.enumList r).mapM fun ρ =>
            (List.range n).mapM fun j =>
              OracleComp.replicate (T n) (kilianPlantedRun V P n cm ρ j))).toOuterMeasure
            {nested | ∀ x ∈ nested, ∀ z ∈ x, ∀ run ∈ z,
              !(acc run && decide (ρ₀ ∈ run.challenges))} := by
          rw [hflat, PMF.toOuterMeasure_map_apply, hpre]
      _ ≤ (ProbComp.eval ((List.range n).mapM fun j =>
            OracleComp.replicate (T n) (kilianPlantedRun V P n cm ρ₀ j))).toOuterMeasure
            {x | ∀ z ∈ x, ∀ run ∈ z, !(acc run && decide (ρ₀ ∈ run.challenges))} :=
          toOuterMeasure_mapM_all_le _ _ _ hmem
      _ ≤ (ProbComp.eval
            (OracleComp.replicate (T n) (kilianPlantedRun V P n cm ρ₀ i.val))).toOuterMeasure
            {z | ∀ run ∈ z, !(acc run && decide (ρ₀ ∈ run.challenges)) = true} := by
          simpa using toOuterMeasure_mapM_all_le _ _ _ (List.mem_range.mpr i.isLt)
      _ = ((ProbComp.eval (kilianPlantedRun V P n cm ρ₀ i.val)).toOuterMeasure
            {y | !(acc y && decide (ρ₀ ∈ y.challenges)) = true}) ^ T n :=
          ProbComp.toOuterMeasure_replicate_forall _ _ (T n)
      _ ≤ (ENNReal.ofReal (1 - θ)) ^ T n := pow_le_pow_left' hfailOne (T n)
      _ = ENNReal.ofReal ((1 - θ) ^ T n) :=
          (ENNReal.ofReal_pow (sub_nonneg.mpr hθ1) (T n)).symm
  calc collected.toOuterMeasure
        (⋃ ρ₀ ∈ good.toFinset, {runs | ∀ run ∈ runs, !(acc run && decide (ρ₀ ∈ run.challenges))})
      ≤ ∑ ρ₀ ∈ good.toFinset, collected.toOuterMeasure
          {runs | ∀ run ∈ runs, !(acc run && decide (ρ₀ ∈ run.challenges))} :=
        MeasureTheory.measure_biUnion_finset_le _ _
    _ ≤ ∑ _ ∈ good.toFinset, ENNReal.ofReal ((1 - θ) ^ T n) := Finset.sum_le_sum hsingle
    _ = (good.toFinset.card : ℝ≥0∞) * ENNReal.ofReal ((1 - θ) ^ T n) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (M : ℝ≥0∞) * ENNReal.ofReal ((1 - θ) ^ T n) := by
        gcongr
        exact_mod_cast (List.toFinset_card_le good).trans
          ((List.length_filter_le _ _).trans (by simpa [BitString.length_enumList] using hM))

/-- **Exact finite-parameter rewinding extraction bound** for Kilian's protocol: for any rational
threshold `num / den` (`0 < den`), per-coin attempt budget `T n`, per-instance acceptance threshold
`θ ∈ (0, 1]`, and coin-space bound `2 ^ V.coins cm.stmt ≤ M`, the prover's single-run acceptance
probability is bounded by `(num / den) ^ n + n * θ + M * (1 - θ) ^ T n` plus the binding error of
`kilianExtractorBindingAdversary` and the probability that `kilianTableExtractor` extracts a compact
table whose expanded proof accepts strictly more than a `num / den` fraction of PCP coins. -/
theorem succProbability_kilianAcceptGame_le_extracted
    {H : List Bool → List Bool → List Bool} {V : PCPVerifier α} {P : KilianProver α}
    (T : ℕ → ℕ) (num den n M : ℕ) {θ : ℝ}
    (hden : 0 < den) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hM : ∀ k : List Bool, k.length = n → ∀ cm ∈ (ProbComp.eval (P.commit n k)).support,
      2 ^ V.coins cm.stmt ≤ M) :
    (ProbComp.eval (kilianAcceptGame H V P n) true).toReal ≤
      ((num : ℝ) / den) ^ n + (n : ℝ) * θ + (M : ℝ) * (1 - θ) ^ T n +
        (ProbComp.eval (merkleBindingGame H (fun _ leaf => leaf.length == 1)
          (kilianExtractorBindingAdversary H V P T) n) true).toReal +
        (ProbComp.eval (kilianExtractionFracGame H V P T num den n) true).toReal := by
  classical
  let errConst : ℝ≥0∞ :=
    ((num : ℝ≥0∞) / den) ^ n + (n : ℝ≥0∞) * ENNReal.ofReal θ +
      (M : ℝ≥0∞) * ENNReal.ofReal ((1 - θ) ^ T n)
  let first := ProbComp.eval (kilianCommitStage P n)
  let bKernel : List Bool × KilianCommitment α → PMF Bool := fun s =>
    (ProbComp.eval (kilianCollectRuns V P T n s.2)).map fun runs =>
      merkleBreaksBinding H (fun _ leaf => leaf.length == 1) n s.1
        (kilianRunsBindingOutput H V s.1 s.2.stmt s.2.root runs)
  let eKernel : List Bool × KilianCommitment α → PMF Bool := fun s =>
    (ProbComp.eval (kilianCollectRuns V P T n s.2)).map fun runs =>
      decide (num * 2 ^ V.coins s.2.stmt <
        den * acceptCount
          (fun y => V.accepts y.1
            (V.proofOfTable s.2.stmt (kilianExtractTableFromRuns H V s.1 s.2.stmt s.2.root runs))
            y.2)
          s.2.stmt (V.coins s.2.stmt))
  have hpoint : ∀ s ∈ first.support,
      ((ProbComp.eval (kilianSingleRun V P n s.2)).map fun run =>
          kilianVerify H V s.1 s.2.stmt s.2.root run.challenges run.response) true ≤
        errConst + bKernel s true + eKernel s true := by
    intro s hs
    obtain ⟨hk, hcm⟩ := mem_support_kilianCommitStage hs
    have hMs := hM s.1 hk s.2 hcm
    let r := V.coins s.2.stmt
    let acc : KilianChallengeRun → Bool :=
      fun run => kilianVerify H V s.1 s.2.stmt s.2.root run.challenges run.response
    let good := kilianGoodCoins H V P n s.1 s.2 θ
    rw [map_apply_true]
    by_cases hcase : den * good.length ≤ num * 2 ^ r
    · have hfrac : (good.length : ℝ≥0∞) / 2 ^ r ≤ (num : ℝ≥0∞) / den := by
        rw [ENNReal.div_le_iff_le_mul (Or.inl (by positivity)) (Or.inl (by finiteness)),
          div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv,
          ENNReal.le_div_iff_mul_le (Or.inl (Nat.cast_ne_zero.mpr hden.ne'))
            (Or.inl (ENNReal.natCast_ne_top den)), mul_comm _ (den : ℝ≥0∞)]
        exact_mod_cast hcase
      calc (ProbComp.eval (kilianSingleRun V P n s.2)).toOuterMeasure {y | acc y = true}
          ≤ ((good.length : ℝ≥0∞) / 2 ^ r) ^ n + (n : ℝ≥0∞) * ENNReal.ofReal θ :=
            kilianSingleRun_bound_of_threshold H V P n s.1 s.2 hθ0
        _ ≤ ((num : ℝ≥0∞) / den) ^ n + (n : ℝ≥0∞) * ENNReal.ofReal θ := by gcongr
        _ ≤ errConst := le_add_of_nonneg_right zero_le
        _ ≤ errConst + bKernel s true + eKernel s true := by
            rw [add_assoc]; exact le_add_of_nonneg_right zero_le
    · have hlt : num * 2 ^ r < den * good.length := lt_of_not_ge hcase
      let collected := ProbComp.eval (kilianCollectRuns V P T n s.2)
      let Ecov : Set (List KilianChallengeRun) :=
        {runs | ∀ ρ₀ ∈ good, ∃ run ∈ runs, acc run = true ∧ ρ₀ ∈ run.challenges}
      let Ebind : Set (List KilianChallengeRun) :=
        {runs | merkleBreaksBinding H (fun _ leaf => leaf.length == 1) n s.1
          (kilianRunsBindingOutput H V s.1 s.2.stmt s.2.root runs) = true}
      let Eext : Set (List KilianChallengeRun) :=
        {runs | decide (num * 2 ^ r < den * acceptCount
          (fun y => V.accepts y.1
            (V.proofOfTable s.2.stmt (kilianExtractTableFromRuns H V s.1 s.2.stmt s.2.root runs))
            y.2)
          s.2.stmt r) = true}
      have huniv : (Set.univ : Set (List KilianChallengeRun)) ⊆ Ecovᶜ ∪ (Ebind ∪ Eext) := by
        intro runs _
        by_cases hcov : runs ∈ Ecov
        · refine Or.inr ?_
          rcases accepts_kilianExtractTableFromRuns_or_breaksBinding
              (H := H) (V := V) (n := n) (k := s.1) (x := s.2.stmt) (root := s.2.root)
              (runs := runs) with hbrk | hcons
          · exact Or.inl hbrk
          · refine Or.inr (decide_eq_true (hlt.trans_le (Nat.mul_le_mul_left den ?_)))
            have hfilter : good.length = (BitString.enumList r).countP (fun ρ₀ =>
                decide (∃ i : Fin n, θ ≤
                  ((ProbComp.eval (kilianPlantedRun V P n s.2 ρ₀ i.val)).toOuterMeasure
                    {y | acc y = true}).toReal)) := by
              simp only [good, kilianGoodCoins, r, acc, List.countP_eq_length_filter]
            have hac : acceptCount
                (fun y => V.accepts y.1 (V.proofOfTable s.2.stmt
                  (kilianExtractTableFromRuns H V s.1 s.2.stmt s.2.root runs)) y.2) s.2.stmt r =
                (BitString.enumList r).countP fun ρ₀ =>
                  V.accepts s.2.stmt (V.proofOfTable s.2.stmt
                    (kilianExtractTableFromRuns H V s.1 s.2.stmt s.2.root runs)) ρ₀ :=
              (BitString.countP_enumList r fun ρ₀ =>
                V.accepts s.2.stmt (V.proofOfTable s.2.stmt
                  (kilianExtractTableFromRuns H V s.1 s.2.stmt s.2.root runs)) ρ₀).symm
            rw [hfilter, hac]
            refine List.countP_mono_left fun ρ₀ hρ₀enum hpred => ?_
            obtain ⟨run, hrun, hrunAcc, hρ₀in⟩ := hcov ρ₀ (List.mem_filter.mpr ⟨hρ₀enum, hpred⟩)
            exact hcons run hrun hrunAcc ρ₀ hρ₀in (BitString.mem_enumList.mp hρ₀enum)
        · exact Or.inl hcov
      have hcompCov : Ecovᶜ =
          {runs | ∃ ρ₀ ∈ good, ∀ run ∈ runs, !(acc run && decide (ρ₀ ∈ run.challenges))} := by
        ext runs
        simp only [Set.mem_compl_iff, Ecov, Set.mem_ofPred_eq, Bool.not_and,
          not_forall, not_exists, not_and]
        exact ⟨fun ⟨ρ₀, hρ₀, hno⟩ => ⟨ρ₀, hρ₀, fun run hrun => by
            by_cases hacc : acc run = true <;> simp [hacc, hno run hrun]⟩,
          fun ⟨ρ₀, hρ₀, hno⟩ => ⟨ρ₀, hρ₀, fun run hrun hacc hmem => by
            simpa [hacc, hmem] using hno run hrun⟩⟩
      have hfail := kilianCollectRuns_cover_failure_le H V P T n M s.1 s.2 hθ0 hθ1 hMs
      have h1 : (1 : ℝ≥0∞) ≤ collected.toOuterMeasure Ecovᶜ +
          collected.toOuterMeasure Ebind + collected.toOuterMeasure Eext := by
        calc (1 : ℝ≥0∞) = collected.toOuterMeasure Set.univ := by
                rw [PMF.toOuterMeasure_apply]; simp
          _ ≤ collected.toOuterMeasure (Ecovᶜ ∪ (Ebind ∪ Eext)) := MeasureTheory.measure_mono huniv
          _ ≤ collected.toOuterMeasure Ecovᶜ +
                (collected.toOuterMeasure Ebind + collected.toOuterMeasure Eext) :=
              (MeasureTheory.measure_union_le _ _).trans
                (add_le_add le_rfl (MeasureTheory.measure_union_le _ _))
          _ = _ := by ring
      calc (ProbComp.eval (kilianSingleRun V P n s.2)).toOuterMeasure {y | acc y = true}
          ≤ 1 := Probability.PMF.toOuterMeasure_le_one _ _
        _ ≤ collected.toOuterMeasure Ecovᶜ + collected.toOuterMeasure Ebind +
              collected.toOuterMeasure Eext := h1
        _ ≤ (M : ℝ≥0∞) * ENNReal.ofReal ((1 - θ) ^ T n) + bKernel s true + eKernel s true := by
            rw [hcompCov, show collected.toOuterMeasure Ebind = bKernel s true from
                (map_apply_true collected _).symm,
              show collected.toOuterMeasure Eext = eKernel s true from
                (map_apply_true collected _).symm]
            gcongr
        _ ≤ errConst + bKernel s true + eKernel s true := by
            simp only [errConst]
            gcongr
            exact le_add_of_nonneg_left zero_le
  have hENN : ProbComp.eval (kilianAcceptGame H V P n) true ≤
      errConst +
        ProbComp.eval (merkleBindingGame H (fun _ leaf => leaf.length == 1)
          (kilianExtractorBindingAdversary H V P T) n) true +
        ProbComp.eval (kilianExtractionFracGame H V P T num den n) true := by
    rw [eval_kilianAcceptGame, eval_merkleBindingGame_extractor, eval_kilianExtractionFracGame]
    change (first.bind fun s => (ProbComp.eval (kilianSingleRun V P n s.2)).map fun run =>
        kilianVerify H V s.1 s.2.stmt s.2.root run.challenges run.response) true ≤
      errConst + (first.bind bKernel) true + (first.bind eKernel) true
    rw [add_assoc]
    simp only [PMF.bind_apply]
    calc ∑' s, first s * ((ProbComp.eval (kilianSingleRun V P n s.2)).map fun run =>
            kilianVerify H V s.1 s.2.stmt s.2.root run.challenges run.response) true
        ≤ ∑' s, (first s * errConst + (first s * bKernel s true + first s * eKernel s true)) := by
          refine tsum_le_tsum fun s => ?_
          by_cases hs : s ∈ first.support
          · calc first s * _ ≤ first s * (errConst + bKernel s true + eKernel s true) :=
                  mul_le_mul_of_nonneg_left (hpoint s hs) zero_le
              _ = _ := by ring
          · simp [show first s = 0 by simpa [PMF.mem_support_iff] using hs]
      _ = errConst + ((∑' s, first s * bKernel s true) + (∑' s, first s * eKernel s true)) := by
          rw [tsum_add, tsum_add, ENNReal.tsum_mul_right, first.tsum_coe, one_mul]
  have hpowTop : (((num : ℝ≥0∞) / den) ^ n) ≠ ⊤ :=
    ENNReal.pow_ne_top (ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
      (Nat.cast_ne_zero.mpr hden.ne'))
  have hmulTop {k : ℕ} {a : ℝ} : (k : ℝ≥0∞) * ENNReal.ofReal a ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
  have herrTop : errConst ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hpowTop, hmulTop⟩, hmulTop⟩
  have hreal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨herrTop, PMF.apply_ne_top _ _⟩,
      PMF.apply_ne_top _ _⟩) hENN
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨herrTop, PMF.apply_ne_top _ _⟩)
      (PMF.apply_ne_top _ _),
    ENNReal.toReal_add herrTop (PMF.apply_ne_top _ _)] at hreal
  have herrEq : errConst.toReal =
      ((num : ℝ) / den) ^ n + (n : ℝ) * θ + (M : ℝ) * (1 - θ) ^ T n := by
    simp only [errConst]
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hpowTop, hmulTop⟩) hmulTop,
      ENNReal.toReal_add hpowTop hmulTop]
    simp [ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hθ0, ENNReal.toReal_ofReal (pow_nonneg (sub_nonneg.mpr hθ1) (T n))]
  rwa [herrEq] at hreal

end Bound

/-! ### Asymptotic weak knowledge extraction and NP witness consequence -/

section Asymptotic

private theorem exists_coinsBound_of_isPPT {enc : α ↪ List Bool} {V : PCPVerifier α} {c : ℕ}
    {P : KilianProver α}
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1))
    (hP : P.IsPPT enc) :
    ∃ M : ℕ → ℕ, PolynomiallyBounded M ∧
      ∀ (n : ℕ) (k : List Bool), k.length = n →
        ∀ cm ∈ (ProbComp.eval (P.commit n k)).support, 2 ^ V.coins cm.stmt ≤ M n := by
  obtain ⟨c₁, d₁, hlen₁⟩ := hP.commit.on.length_le
  let M : ℕ → ℕ := fun n => (2 * (c₁ * (3 * n + 2) ^ d₁ + 1)) ^ c
  refine ⟨M, by dsimp only [M]; fun_prop, fun n k hk cm hcm => ?_⟩
  have h₁ := hlen₁ (n, k) cm hcm
  have hin : (encPair encUnary encBits (n, k)).length + 1 = 3 * n + 2 := by
    simp [hk]
    ring
  rw [hin] at h₁
  have hx : (enc cm.stmt).length ≤ c₁ * (3 * n + 2) ^ d₁ := by
    simp only [encKilianCommitment_apply, encKilianMessage_apply, length_encPair] at h₁
    omega
  calc 2 ^ V.coins cm.stmt
      ≤ 2 ^ (c * (Nat.log 2 (enc cm.stmt).length + 1)) :=
        Nat.pow_le_pow_right (by norm_num) (hcoins cm.stmt)
    _ = (2 ^ (Nat.log 2 (enc cm.stmt).length + 1)) ^ c := by rw [pow_mul']
    _ ≤ (2 * ((enc cm.stmt).length + 1)) ^ c := by
        refine Nat.pow_le_pow_left ?_ c
        by_cases hm : (enc cm.stmt).length = 0
        · simp [hm]
        · rw [pow_succ']
          exact Nat.mul_le_mul_left 2 ((Nat.pow_log_le_self 2 hm).trans (Nat.le_succ _))
    _ ≤ (2 * (c₁ * (3 * n + 2) ^ d₁ + 1)) ^ c := by gcongr

/-- **Rewinding compact PCP-table extraction theorem** for Kilian's protocol under any
collision-resistant `HashFamily` and `O(log |enc x|)`-coin PCP verifier `V` (a step toward
[BarakGoldreich2001], Construction 3.4 and Lemma 3.5, uniform strict-PPT compact-table counterpart;
locator not re-verified against primary PDF): for any prover `P : KilianProver α`, any strict
rational acceptance threshold `num / den < 1`, and any polynomial inverse slack `(p n + 1)⁻¹`, there
exists a polynomial-time attempt budget `T` such that `kilianTableExtractor H V P T` runs in uniform
strict PPT and succeeds in extracting a compact PCP table passing
`> (num / den) * 2 ^ V.coins ext.stmt` coins with probability at least
`Pr[P accepts] - 1 / (p n + 1) - ν n` for negligible `ν`. No NP witness `w` is extracted. -/
theorem HashFamily.kilianTableExtraction {H : List Bool → List Bool → List Bool}
    {V : PCPVerifier α} {enc : α ↪ List Bool} {c : ℕ} {P : KilianProver α}
    (hH : HashFamily H) (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1))
    (hP : P.IsPPT enc) (p : ℕ → ℕ) (hp : ComputableInPolyTime p encUnary encUnary)
    {num den : ℕ} (hnum : num < den) :
    ∃ T : ℕ → ℕ,
      ComputableInPolyTime T encUnary encUnary ∧
      IsPPT (encKilianExtractedTable enc) (kilianTableExtractor H V P T) ∧
      ∃ ν : ℕ → ℝ≥0, Negligible ν ∧
        ∀ n : ℕ,
          Game.succProbability (ProbComp.eval (kilianAcceptGame H V P n)) ≤
            Game.succProbability (ProbComp.eval (kilianExtractionFracGame H V P T num den n)) +
              ((p n + 1 : ℕ) : ℝ≥0)⁻¹ + ν n := by
  let T : ℕ → ℕ := fun n => n * ((p n + 1) * (n + 1))
  have hT : ComputableInPolyTime T encUnary encUnary := by
    dsimp only [T]
    fun_prop
  have hExtPPT : IsPPT (encKilianExtractedTable enc) (kilianTableExtractor H V P T) :=
    isPPT_kilianTableExtractor hH.polyTime hH.length_eq hV hcoins hP hT
  obtain ⟨M, hMpoly, hM⟩ := exists_coinsBound_of_isPPT hcoins hP
  have hden : 0 < den := by omega
  let ν₁ : ℕ → ℝ≥0 := fun n => ((num : ℝ≥0) / den) ^ n
  let ν₂ : ℕ → ℝ≥0 := fun n => (M n : ℝ≥0) * (1 / 2 : ℝ≥0) ^ n
  let ν₃ : ℕ → ℝ≥0 := fun n =>
    Game.succProbability (ProbComp.eval (merkleBindingGame H (fun _ leaf => leaf.length == 1)
      (kilianExtractorBindingAdversary H V P T) n))
  have hν₁ : Negligible ν₁ := by
    refine negligible_geometric ?_
    rw [div_lt_one (by exact_mod_cast hden)]
    exact_mod_cast hnum
  have hν₂ : Negligible ν₂ :=
    (negligible_geometric (by norm_num : (1 / 2 : ℝ≥0) < 1)).polynomiallyBounded_mul hMpoly
  have hν₃ : Negligible ν₃ :=
    (merklePositionBinding_of_hashFamily hH fun _ leaf => leaf.length == 1).negligible _
      (isPPT_kilianExtractorBindingAdversary hH.polyTime hH.length_eq hV hcoins hP hT)
  refine ⟨T, hT, hExtPPT, fun n => ν₁ n + ν₂ n + ν₃ n, (hν₁.add hν₂).add hν₃, fun n => ?_⟩
  let θ : ℝ := 1 / (((p n + 1) * (n + 1) : ℕ) : ℝ)
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ 1 := by
    dsimp only [θ]
    refine div_le_one_of_le₀ ?_ (by positivity)
    have hge1 : 1 ≤ (p n + 1) * (n + 1) := Nat.succ_le_succ (Nat.zero_le _)
    exact_mod_cast hge1
  have hfin := succProbability_kilianAcceptGame_le_extracted (H := H) (V := V) (P := P)
    T num den n (M n) hden hθ0 hθ1 (hM n)
  have hnθ : (n : ℝ) * θ ≤ 1 / ((p n + 1 : ℕ) : ℝ) := by
    dsimp only [θ]
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    nlinarith
  have hexpPow : (1 - θ) ^ T n ≤ (1 / 2 : ℝ) ^ n := by
    have h1θ : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
    have hstep1 : (1 - θ) ^ T n ≤ (Real.exp (-θ)) ^ T n :=
      pow_le_pow_left₀ h1θ (Real.one_sub_le_exp_neg θ) (T n)
    have hprod : (-θ) * (T n : ℝ) = (n : ℝ) * (-1) := by
      dsimp only [θ, T]
      push_cast
      field_simp
    have hstep2 : (Real.exp (-θ)) ^ T n = (Real.exp (-1)) ^ n := by
      rw [← Real.exp_nat_mul, mul_comm, hprod, Real.exp_nat_mul]
    have hstep3 : (Real.exp (-1)) ^ n ≤ (1 / 2 : ℝ) ^ n :=
      pow_le_pow_left₀ (Real.exp_pos (-1)).le Real.exp_neg_one_lt_half.le n
    exact hstep1.trans (hstep2 ▸ hstep3)
  rw [← NNReal.coe_le_coe]
  simp only [Game.succProbability, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_inv,
    NNReal.coe_natCast, ENNReal.coe_toNNReal_eq_toReal, ν₁, ν₂, ν₃, NNReal.coe_pow,
    NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] at hfin ⊢
  have hMtail : (M n : ℝ) * (1 - θ) ^ T n ≤ (M n : ℝ) * (1 / 2 : ℝ) ^ n :=
    mul_le_mul_of_nonneg_left hexpPow (Nat.cast_nonneg _)
  rw [one_div] at hnθ
  linarith

/-- **PCP soundness witness consequence for extracted compact tables**: whenever `V` is a PCP
verifier for `L` with soundness error `≤ 1 / 2` and an extracted `KilianExtractedTable` satisfies
the strict half-coin acceptance predicate (`1 * 2 ^ V.coins ext.stmt < 2 * acceptCount ...`), the
committed statement belongs to `L`. -/
theorem kilianExtract_mem_of_isPCP {enc : α ↪ List Bool} {r q : ℕ → ℕ} {V : PCPVerifier α}
    {L : Set α} (hpcp : IsPCPVerifier enc r q V L) (ext : KilianExtractedTable α)
    (hfrac : 1 * 2 ^ V.coins ext.stmt <
      2 * acceptCount
        (fun y => V.accepts y.1 (V.proofOfTable ext.stmt ext.table) y.2)
        ext.stmt (V.coins ext.stmt)) :
    ext.stmt ∈ L := by
  by_contra hx
  have hsound := hpcp.sound ext.stmt hx (V.proofOfTable ext.stmt ext.table)
  omega

/-- **Rewinding compact PCP-table extraction for arbitrary NP relations**: under a collision-
resistant `HashFamily`, every `R : NPRelation enc` admits a polynomial-time `O(log n)`-coin PCP
verifier `V` and witness compiler `compile` (from the PCP completeness bridge) such that every
uniform strict PPT prover's acceptance probability is upper-bounded by the `1 / 2`-coin table
extraction probability up to arbitrary inverse-polynomial slack and negligible cryptographic error.
No NP witness `w` is extracted constructively by `kilianTableExtractor`; the existential guarantee
`∃ w, R.IsWitness ext.stmt w` is a non-constructive PCP-soundness consequence of
`ext.stmt ∈ R.language` via `kilianExtract_mem_of_isPCP`. -/
theorem HashFamily.kilianTableExtraction_npRelation {H : List Bool → List Bool → List Bool}
    (hH : HashFamily H) (enc : α ↪ List Bool) (R : NPRelation enc) :
    ∃ (V : PCPVerifier α) (compile : α × List Bool → List Bool) (c d : ℕ),
      V.PolyTime enc ∧
      IsPCPVerifier enc (fun m => c * (Nat.log 2 m + 1)) (fun _ => d) V R.language ∧
      ComputableInPolyTime compile (encPair enc encBits) encBits ∧
      (∀ x w, R.IsWitness x w → V.tableVerifier (x, compile (x, w)) = true) ∧
      (∀ ext : KilianExtractedTable α,
        1 * 2 ^ V.coins ext.stmt <
          2 * acceptCount
            (fun y => V.accepts y.1 (V.proofOfTable ext.stmt ext.table) y.2)
            ext.stmt (V.coins ext.stmt) →
        ∃ w, R.IsWitness ext.stmt w) ∧
      ∀ (P : KilianProver α), P.IsPPT enc →
        ∀ p : ℕ → ℕ, ComputableInPolyTime p encUnary encUnary →
          ∃ T : ℕ → ℕ,
            ComputableInPolyTime T encUnary encUnary ∧
            IsPPT (encKilianExtractedTable enc) (kilianTableExtractor H V P T) ∧
            ∃ ν : ℕ → ℝ≥0, Negligible ν ∧
              ∀ n : ℕ,
                Game.succProbability (ProbComp.eval (kilianAcceptGame H V P n)) ≤
                  Game.succProbability (ProbComp.eval (kilianExtractionFracGame H V P T 1 2 n)) +
                    ((p n + 1 : ℕ) : ℝ≥0)⁻¹ + ν n := by
  obtain ⟨V, compile, c, d, hV, hpcp, hcompile, hcomp⟩ := exists_pcpVerifier_of_npRelation enc R
  refine ⟨V, compile, c, d, hV, hpcp, hcompile, hcomp, fun ext hfrac => ?_, ?_⟩
  · exact (R.mem_language).mp (kilianExtract_mem_of_isPCP hpcp ext hfrac)
  · intro P hP p hp
    exact hH.kilianTableExtraction hV hpcp.coins_le hP p hp (by norm_num : 1 < 2)

end Asymptotic

end Cslib.Crypto
