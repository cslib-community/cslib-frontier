/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Kilian.MicaliSoundness
-- Unfold `micaliSoundnessGame` and `micaliSoundnessProg` (`MicaliSoundness.lean`) inside
-- `micaliRawSoundness_bound`.
import all CslibFrontier.Crypto.Computational.Kilian.MicaliSoundness
public import CslibFrontier.Crypto.Computational.Kilian.RawVerifier
public import CslibFrontier.Computability.Probabilistic.Oracle.Time
public import CslibFrontier.Languages.Probabilistic.Oracle.Codec
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.BoundedPrefix
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Lists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.PCP.Completeness
import CslibFrontier.Computability.Probabilistic.Oracle.Traverse
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Languages.Probabilistic.QueryCount.Sum
import CslibFrontier.Languages.Probabilistic.UntilBad.TwoCost
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.EventBind
import CslibFrontier.Tactic.PolyTime

/-!
# Bounded-prefix raw Micali verification, native ROM verifier runtime, and raw ROM soundness

`CslibFrontier.Crypto.Computational.Kilian.MicaliSoundness` verifies structured `MicaliProof` values
under `MicaliSpec α` without charging message decoding, truncating oversized proof strings, or
certifying native oracle-machine verification runtime (`locator not re-verified against primary PDF`
for [Micali2000] and [ChiesaYogev2024]).

This module completes that verification-complexity and raw-proof layer cleanly on top of
`CslibFrontier.Crypto.Computational.Kilian.RawVerifier` and
`CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.BoundedPrefix`:

* **Framing decoder and uniform proof cap (`encMicaliProof`, `micaliProofDecoder`,
  `micaliMaxProofCap`):** reuses `kilianProverMsgDecoder` and `kilianRawProverCap`. Before querying
  the Fiat–Shamir oracle, the verifier decodes `root` from only the leading `2 * σ + 1` bits and
  enforces `micaliHasRootPrefix σ rawProof`. Any accepted raw proof fits inside
  `micaliMaxProofCap V σ m d x` (`computableInPolyTime_micaliMaxProofCap`), while honest proof
  payload bits satisfy the `O((σ + m + 1)^2 · (log₂ |enc x| + 1))` bound
  `micaliProofBits_micaliProvePure_le_log`.
* **Pure bounded-prefix verifier machine (`micaliVerifyRawBoundedPure`):** agrees unconditionally
  with `micaliVerifyPure` on every proof `prf : MicaliProof` with `prf.root.length ≤ σ`, depends
  only on `rawProof.take (micaliMaxProofCap V σ m d x + 1)`, and runs on one fixed binary
  `MultiTapeTM` in worst-case time and space polynomial in `m + |enc x|` for **all** unbounded raw
  inputs (`computableInTimeAndSpace_micaliVerifyRawBoundedPure_of_params`).
* **Native ROM verifier machine (`micaliVerifyRawBounded`, `micaliVerifyRawWord`):** verifies proofs
  against Micali's random oracle with at most `1` Fiat–Shamir query and at most
  `m * d * (kilianDepth V x + 1)` Merkle queries (`IsCostBounded`), bisimulates cleanly with the
  word-oracle interface `MicaliWordOp` (`micaliWordCodec`), and runs on one fixed halting oracle
  `MultiTapePTM` in worst-case step count polynomial in `σ + m + |enc x|` uniformly over **all**
  arbitrary unbounded `rawProof : List Bool`, all `(σ, m, x) : MicaliRawInput α`, and all
  stateful word handlers (`computesOracleInTimeAndQueriesOn_micaliVerifyRawWord`).
* **Adaptive raw-byte ROM soundness & NP CS proofs (`micaliRawSoundness_bound`,
  `exists_micaliRawCSProof_of_npRelation`):** proves adaptive two-channel ROM soundness against
  unbounded raw-byte cheating provers `P : OracleComp (MicaliSpec α) (α × List Bool)` by reducing
  to `micaliSoundness_bound_of_prover_verifier` with sanitized bounded proofs, and yields complete
  raw-verified CS proofs for arbitrary NP relations.

Locators in [Micali2000] and [ChiesaYogev2024] are carried from `Kilian.MicaliSoundness`
(`locator not re-verified against primary PDF`).

## Main definitions

* `Cslib.Crypto.MicaliRawInput`, `Cslib.Crypto.encMicaliRawInput`,
  `Cslib.Crypto.encMicaliProof`, `Cslib.Crypto.micaliProofDecoder`,
  `Cslib.Crypto.micaliHasRootPrefix`, `Cslib.Crypto.micaliFSReplyCap`,
  `Cslib.Crypto.micaliMaxProofCap`, `Cslib.Crypto.kilianStructValid`.
* `Cslib.Crypto.micaliVerifyRawBoundedPure`, `Cslib.Crypto.micaliVerifyRawBounded`.
* `Cslib.Crypto.MicaliWordOp`, `Cslib.Crypto.micaliWordCodec`,
  `Cslib.Crypto.micaliVerifyRawWord`.
* `Cslib.Crypto.micaliRawSoundnessProg`, `Cslib.Crypto.micaliRawSoundnessGame`.

## Main results

* `Cslib.Crypto.micaliVerifyRawBoundedPure_take_eq`,
  `Cslib.Crypto.micaliVerifyRawBoundedPure_enc_eq_of_root_le`,
  `Cslib.Crypto.computableInTimeAndSpace_micaliVerifyRawBoundedPure_of_params`.
* `Cslib.Crypto.evalPure_micaliVerifyRawBounded`,
  `Cslib.Crypto.isCostBounded_micaliFSCost_micaliVerifyRawBounded`,
  `Cslib.Crypto.isCostBounded_micaliMTCost_micaliVerifyRawBounded`.
* `Cslib.Crypto.runWith_wordOracle_micaliVerifyRawWord`,
  `Cslib.Crypto.computesOracleInTimeAndQueriesOn_micaliVerifyRawWord`.
* `Cslib.Crypto.micaliRawSoundness_bound`,
  `Cslib.Crypto.exists_micaliRawCSProof_of_npRelation`.

## References

* [S. Micali, *Computationally Sound Proofs*][Micali2000]
* [A. Chiesa, E. Yogev, *Building Cryptographic Proofs from Hash Functions*][ChiesaYogev2024],
  Construction 21.1.1 and Theorem 21.2.1.
-/

@[expose] public section

namespace Cslib.Crypto

open Complexity Probability Turing.MultiTapeTM
open scoped ENNReal NNReal

section EncodingsAndCaps

section
variable {α : Type}

/-- Public verifier header `(σ, reps, stmt)` for bounded-prefix raw Micali verification: digest
width `σ`, repetition count `reps`, and statement `stmt`. -/
@[ext]
structure MicaliRawInput (α : Type) where
  /-- Merkle digest bit length `σ`. -/
  sigma : ℕ
  /-- Number `reps` of Fiat–Shamir PCP repetitions. -/
  reps : ℕ
  /-- Public statement `stmt`. -/
  stmt : α
  deriving DecidableEq, Repr, Inhabited

/-- Framed encoding of `MicaliRawInput α` using unary `(sigma, reps)` and `enc` for `stmt`. -/
enc_structure encMicaliRawInput (enc : α ↪ List Bool) : MicaliRawInput α where
  sigma : encUnary, reps : encUnary, stmt : enc

attribute [fun_prop] encMicaliRawInput_sigma_polyTime encMicaliRawInput_reps_polyTime
  encMicaliRawInput_stmt_polyTime encMicaliRawInput_mk_polyTime

/-- Public verifier header and proof encoding for pure bounded-prefix raw Micali verification at a
fixed Merkle digest width `σ`. -/
abbrev encMicaliPureVerifierInput (enc : α ↪ List Bool) :
    (ℕ × α) × List Bool ↪ List Bool :=
  encPair (encPair encUnary enc) encBits

end

/-- Framed encoding of `MicaliProof`: the framed Merkle root, then the Kilian opening response. -/
enc_structure encMicaliProof : MicaliProof where
  root : encBits, response : encKilianResponse

attribute [fun_prop] encMicaliProof_root_polyTime encMicaliProof_response_polyTime
  encMicaliProof_mk_polyTime

/-- Total polynomial-time decoder for `MicaliProof`, reusing `kilianProverMsgDecoder`. -/
def micaliProofDecoder : Decoder encMicaliProof :=
  kilianProverMsgDecoder.map (fun p => ⟨p.1, p.2⟩) (fun prf => (prf.root, prf.response))
    (fun _ => rfl) (fun prf => by simp [encMicaliProof_apply])

/-- Predicate checking that `rawProof` begins with a complete framed bit string of at most `σ`
bits within its first `2 * σ + 1` bits. -/
def micaliHasRootPrefix (σ : ℕ) (rawProof : List Bool) : Bool :=
  let pfx := rawProof.take (2 * σ + 1)
  let root := unframe pfx
  decide (root.length ≤ σ) && (pfx.take (2 * root.length + 1) == frame root)

theorem micaliHasRootPrefix_encMicaliProof {σ : ℕ} (prf : MicaliProof)
    (hroot : prf.root.length ≤ σ) :
    micaliHasRootPrefix σ (encMicaliProof prf) = true := by
  have hpfx : (encMicaliProof prf).take (2 * σ + 1) =
      frame prf.root ++
        (encKilianResponse prf.response).take (2 * σ + 1 - (frame prf.root).length) := by
    simp only [encMicaliProof_apply, encPair_apply, encBits_apply]
    rw [List.take_append, List.take_of_length_le (by rw [length_frame]; omega)]
  simp only [micaliHasRootPrefix, hpfx, unframe_frame_append, hroot, decide_true, Bool.true_and,
    beq_iff_eq]
  rw [List.take_append, length_frame, Nat.sub_self, List.take_zero, List.append_nil,
    ← length_frame (w := prf.root), List.take_length]

theorem unframe_take_of_micaliHasRootPrefix {σ : ℕ} {rawProof : List Bool}
    (h : micaliHasRootPrefix σ rawProof = true) :
    let root := unframe (rawProof.take (2 * σ + 1))
    root.length ≤ σ ∧ frame root <+: rawProof ∧ unframe rawProof = root := by
  simp only [micaliHasRootPrefix, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  set root := unframe (rawProof.take (2 * σ + 1))
  have htake : rawProof.take (2 * root.length + 1) = frame root := by
    simpa only [List.take_take, Nat.min_eq_left (by omega : 2 * root.length + 1 ≤ 2 * σ + 1)]
      using h.2
  have hraw : frame root ++ rawProof.drop (2 * root.length + 1) = rawProof := by
    rw [← htake, List.take_append_drop]
  exact ⟨h.1, ⟨_, hraw⟩, by rw [← hraw, unframe_frame_append]⟩

theorem unframe_take_encMicaliProof {σ : ℕ} (prf : MicaliProof) (hroot : prf.root.length ≤ σ) :
    unframe ((encMicaliProof prf).take (2 * σ + 1)) = prf.root := by
  obtain ⟨-, -, heq⟩ :=
    unframe_take_of_micaliHasRootPrefix (micaliHasRootPrefix_encMicaliProof prf hroot)
  rw [← heq, encMicaliProof_apply, encPair_apply, encBits_apply, unframe_frame_append]

/-- Polynomial upper bound on `(encList encBits ρs).length` when `ρs` has length `m` and each
challenge has at most `c * (Nat.log 2 (enc x).length + 1)` bits. -/
def micaliFSReplyCap {α : Type} (enc : α ↪ List Bool) (c m : ℕ) (x : α) : ℕ :=
  m * (2 * (c * (Nat.log 2 (enc x).length + 1)) + 1)

theorem length_encList_le_micaliFSReplyCap {α : Type} (enc : α ↪ List Bool) {c m : ℕ}
    {V : PCPVerifier α} (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1))
    {x : α} {ρs : List (List Bool)} (hm : ρs.length = m)
    (hρs : ∀ ρ ∈ ρs, ρ.length = V.coins x) :
    (encList encBits ρs).length ≤ micaliFSReplyCap enc c m x := by
  rw [← hm, micaliFSReplyCap]
  refine length_encList_le encBits ρs fun ρ hρ => ?_
  simpa [encBits_apply, hρs ρ hρ] using hcoins x

/-- Deterministic upper bound on `kilianRawProverCap V (List.replicate σ false) x ρs` uniform
over all challenge lists `ρs` of length `m` for a `d`-query PCP verifier `V`. -/
def micaliMaxProofCap {α : Type} (V : PCPVerifier α) (σ m d : ℕ) (x : α) : ℕ :=
  (2 * σ + 1) + m * (2 * (d * (2 * kilianOpeningEncBound σ (kilianDepth V x) + 1)) + 1)

theorem kilianRawProverCap_le_micaliMaxProofCap {α : Type} (V : PCPVerifier α) {σ m d : ℕ}
    {x : α} {ρs : List (List Bool)} (hm : ρs.length = m)
    (hq : ∀ ρ ∈ ρs, (V.queries (x, ρ)).length ≤ d) :
    kilianRawProverCap V (List.replicate σ false) x ρs ≤ micaliMaxProofCap V σ m d x := by
  unfold kilianRawProverCap micaliMaxProofCap
  rw [List.length_replicate]
  refine Nat.add_le_add_left ?_ _
  have hsum := List.sum_le_length_nsmul
    (ρs.map fun ρ =>
      2 * ((V.queries (x, ρ)).length *
        (2 * kilianOpeningEncBound σ (kilianDepth V x) + 1)) + 1)
    (2 * (d * (2 * kilianOpeningEncBound σ (kilianDepth V x) + 1)) + 1)
    fun u hu => by
      obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.mp hu
      have hqd := hq ρ hρ
      gcongr
  simpa [List.length_map, hm, smul_eq_mul] using hsum

/-- Structural validity check on `resp` ensuring path lengths and digest lengths match `V` and
`root` before issuing any Merkle oracle queries. -/
def kilianStructValid {α : Type} (V : PCPVerifier α) (x : α) (root : List Bool)
    (ρs : List (List Bool)) (resp : KilianResponse) : Bool :=
  resp.length == ρs.length &&
    (ρs.zip resp).all fun (ρ, answers) =>
      answers.length == (V.queries (x, ρ)).length &&
        answers.all fun o =>
          o.path.length == kilianDepth V x && o.path.all fun s => s.length == root.length

private theorem mem_zip_of_mem_right {β γ : Type*} {xs : List β} {ys : List γ}
    (hlen : ys.length = xs.length) {y : γ} (hy : y ∈ ys) :
    ∃ x ∈ xs, (x, y) ∈ xs.zip ys := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hy
  have hix : i < xs.length := hlen ▸ hi
  have hiz : i < (xs.zip ys).length := by simp [hlen, hix]
  exact ⟨xs[i]'hix, List.getElem_mem hix, List.getElem_zip ▸ List.getElem_mem hiz⟩

theorem kilianStructValid_of_kilianVerify {α : Type} {H : List Bool → List Bool → List Bool}
    {V : PCPVerifier α} {k : List Bool} {x : α} {root : List Bool} {ρs : List (List Bool)}
    {resp : KilianResponse} (h : kilianVerify H V k x root ρs resp = true) :
    kilianStructValid V x root ρs resp = true := by
  simp only [kilianVerify, kilianStructValid, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h ⊢
  refine ⟨h.1, fun ⟨ρ, answers⟩ hmem => ?_⟩
  have hc := h.2 (ρ, answers) hmem
  simp only [kilianCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
  refine ⟨hc.1.1, fun o ho => ?_⟩
  obtain ⟨_, _, hzip⟩ := mem_zip_of_mem_right hc.1.1 ho
  have hm := merkleVerify_eq_true_iff.mp (hc.1.2 _ hzip)
  exact ⟨hm.1, fun s hs => hm.2.2.1 s hs⟩

end EncodingsAndCaps

section PureBoundedVerifier

variable {α : Type}

/-- Pure bounded-prefix Micali verifier: decodes `root` from the leading `2 * σ + 1` bits of
`rawProof`, queries `hFS (x, root)`, validates challenge and proof caps, and runs
`kilianVerifyRawBounded`. -/
def micaliVerifyRawBoundedPure (hTree : List Bool → List Bool)
    (hFS : α × List Bool → List (List Bool)) (V : PCPVerifier α) (σ m : ℕ)
    (x : α) (rawProof : List Bool) : Bool :=
  let root := unframe (rawProof.take (2 * σ + 1))
  let ρs := hFS (x, root)
  micaliHasRootPrefix σ rawProof &&
    (ρs.length == m && ρs.all fun ρ => ρ.length == V.coins x) &&
    kilianVerifyRawBounded (fun _ => hTree) V ⟨List.replicate σ false, x, ρs⟩ rawProof

theorem micaliVerifyRawBoundedPure_eq_false_of_maxCap_lt
    (hTree : List Bool → List Bool) (hFS : α × List Bool → List (List Bool))
    (V : PCPVerifier α) {σ m d : ℕ}
    (hq : ∀ x ρ, ρ.length = V.coins x → (V.queries (x, ρ)).length ≤ d)
    {x : α} {rawProof : List Bool} (hlt : micaliMaxProofCap V σ m d x < rawProof.length) :
    micaliVerifyRawBoundedPure hTree hFS V σ m x rawProof = false := by
  unfold micaliVerifyRawBoundedPure
  dsimp only
  set ρs := hFS (x, unframe (rawProof.take (2 * σ + 1)))
  by_cases hm : ρs.length = m ∧ ∀ ρ ∈ ρs, ρ.length = V.coins x
  · have hcap :=
      kilianRawProverCap_le_micaliMaxProofCap V (σ := σ) hm.1 fun ρ hρ => hq x ρ (hm.2 ρ hρ)
    rw [kilianVerifyRawBounded_eq_false_of_cap_lt _ V (lt_of_le_of_lt hcap hlt)]
    simp
  · have hbad : (ρs.length == m && ρs.all fun ρ => ρ.length == V.coins x) = false := by
      simpa [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] using hm
    simp [hbad]

/-- Prefix truncation invariance for `micaliVerifyRawBoundedPure`: verification depends only on the
first `micaliMaxProofCap V σ m d x + 1` bits of `rawProof`. -/
theorem micaliVerifyRawBoundedPure_take_eq
    (hTree : List Bool → List Bool) (hFS : α × List Bool → List (List Bool))
    (V : PCPVerifier α) {σ m d : ℕ}
    (hq : ∀ x ρ, ρ.length = V.coins x → (V.queries (x, ρ)).length ≤ d)
    (x : α) (rawProof : List Bool) :
    micaliVerifyRawBoundedPure hTree hFS V σ m x rawProof =
      micaliVerifyRawBoundedPure hTree hFS V σ m x
        (rawProof.take (micaliMaxProofCap V σ m d x + 1)) := by
  by_cases hle : rawProof.length ≤ micaliMaxProofCap V σ m d x
  · rw [List.take_of_length_le (hle.trans (Nat.le_succ _))]
  · rw [micaliVerifyRawBoundedPure_eq_false_of_maxCap_lt hTree hFS V hq (by omega),
      micaliVerifyRawBoundedPure_eq_false_of_maxCap_lt hTree hFS V hq (by simp; omega)]

private theorem merkleVerify_congr_hash {H₁ H₂ : List Bool → List Bool → List Bool}
    {k₁ k₂ : List Bool} {d : ℕ} {root : List Bool} {i : ℕ} {leaf : List Bool}
    {path : List (List Bool)} (h : H₁ k₁ = H₂ k₂) :
    merkleVerify H₁ k₁ d root i leaf path = merkleVerify H₂ k₂ d root i leaf path := by
  unfold merkleVerify merkleRootOfPath merkleInputs merkleInputsStep
  rw [h]

private theorem kilianVerify_congr_hash {H₁ H₂ : List Bool → List Bool → List Bool}
    {k₁ k₂ : List Bool} (V : PCPVerifier α) (x : α) (root : List Bool)
    (ρs : List (List Bool)) (resp : KilianResponse) (h : H₁ k₁ = H₂ k₂) :
    kilianVerify H₁ V k₁ x root ρs resp = kilianVerify H₂ V k₂ x root ρs resp := by
  unfold kilianVerify kilianCheck MerkleOpening.verify
  simp only [merkleVerify_congr_hash h]

/-- On any encoded `prf : MicaliProof` with `prf.root.length ≤ σ`, whenever `hFS (x, prf.root)`
returns `m` valid `V.coins x`-bit challenges, `micaliVerifyRawBoundedPure` agrees unconditionally
with `micaliVerifyPure`. -/
theorem micaliVerifyRawBoundedPure_enc_eq_of_root_le
    (hTree : List Bool → List Bool) (hFS : α × List Bool → List (List Bool))
    (V : PCPVerifier α) {σ m : ℕ} {x : α} (prf : MicaliProof)
    (hroot : prf.root.length ≤ σ)
    (hm : (hFS (x, prf.root)).length = m)
    (hρs : ∀ ρ ∈ hFS (x, prf.root), ρ.length = V.coins x) :
    micaliVerifyRawBoundedPure hTree hFS V σ m x (encMicaliProof prf) =
      micaliVerifyPure hTree hFS V x prf := by
  have hch : ((hFS (x, prf.root)).length == m &&
      (hFS (x, prf.root)).all fun ρ => ρ.length == V.coins x) = true := by
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
    exact ⟨hm, hρs⟩
  have hk := kilianVerifyRawBounded_enc_eq_of_root_le (fun _ => hTree) V
    ⟨List.replicate σ false, x, hFS (x, prf.root)⟩ prf.root prf.response
    (by simpa [List.length_replicate] using hroot)
  unfold micaliVerifyRawBoundedPure micaliVerifyPure
  dsimp only
  rw [unframe_take_encMicaliProof prf hroot, micaliHasRootPrefix_encMicaliProof prf hroot]
  simp only [hch, Bool.true_and]
  rw [show encMicaliProof prf = encPair encBits encKilianResponse (prf.root, prf.response) from rfl,
    hk]
  exact kilianVerify_congr_hash V x prf.root (hFS (x, prf.root)) prf.response rfl

/-- Honest completeness for `micaliVerifyRawBoundedPure`. -/
theorem micaliVerifyRawBoundedPure_micaliProvePure_eq_true
    {hTree : List Bool → List Bool} {hFS : α × List Bool → List (List Bool)}
    {V : PCPVerifier α} {σ m : ℕ} (hlen : ∀ y, (hTree y).length = σ) {x : α}
    {table : List Bool} (htable : V.tableVerifier (x, table) = true)
    (hm : (hFS (x, kilianCommit (fun _ => hTree) V [] x table)).length = m)
    (hρs : ∀ ρ ∈ hFS (x, kilianCommit (fun _ => hTree) V [] x table), ρ.length = V.coins x) :
    micaliVerifyRawBoundedPure hTree hFS V σ m x
      (encMicaliProof (micaliProvePure hTree hFS V x table)) = true := by
  have hroot : (micaliProvePure hTree hFS V x table).root.length ≤ σ := by
    simpa [micaliProvePure, kilianCommit] using (length_merkleRoot (H := fun _ => hTree) hlen _).le
  rw [micaliVerifyRawBoundedPure_enc_eq_of_root_le hTree hFS V _ hroot hm hρs]
  exact micaliVerifyPure_micaliProvePure_eq_true hlen htable hρs

end PureBoundedVerifier

section PureMachineComplexity

variable {α : Type} {enc : α ↪ List Bool}

private theorem computableInPolyTime_coins_unary {V : PCPVerifier α} (hV : V.PolyTime enc) {c : ℕ}
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1)) :
    ComputableInPolyTime V.coins enc encUnary :=
  ComputableInPolyTime.binary_to_unary_bounded hV.coins
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const c)
      (ComputableInPolyTime.unary_add'
        ((ComputableInPolyTime.unary_log_const 2).comp (ComputableInPolyTime.encoding_length enc))
        (ComputableInPolyTime.const 1)))
    hcoins

private theorem computableInPolyTime_kilianDepth {V : PCPVerifier α} (hV : V.PolyTime enc) {c : ℕ}
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1)) :
    ComputableInPolyTime (kilianDepth V) enc encUnary :=
  (ComputableInPolyTime.unary_clog_const 2).comp
    ((ComputableInPolyTime.length_list encNat).comp (PCPVerifier.isPolyTime_queryTable hV hcoins))

private theorem computableInPolyTime_micaliHasRootPrefix :
    ComputableInPolyTime (fun p : ℕ × List Bool => micaliHasRootPrefix p.1 p.2)
      (encPair encUnary encBits) encBool := by
  have hpfx : ComputableInPolyTime (fun p : ℕ × List Bool => p.2.take (2 * p.1 + 1))
      (encPair encUnary encBits) encBits :=
    ComputableInPolyTime.bitsTakeWithInput (ComputableInPolyTime.snd encUnary encBits)
      (ComputableInPolyTime.unary_add'
        (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2)
          (ComputableInPolyTime.fst encUnary encBits))
        (ComputableInPolyTime.const 1))
  have hroot := ComputableInPolyTime.unframe.comp hpfx
  exact ComputableInPolyTime.bool_and'
    (ComputableInPolyTime.unary_le.comp
      ((ComputableInPolyTime.length_bits.comp hroot).prod
        (ComputableInPolyTime.fst encUnary encBits)))
    (ComputableInPolyTime.beq
      (ComputableInPolyTime.bitsTakeWithInput hpfx
        (ComputableInPolyTime.unary_add'
          (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2)
            (ComputableInPolyTime.length_bits.comp hroot))
          (ComputableInPolyTime.const 1)))
      ((ComputableInPolyTime.bitsFrame encBits).comp hroot))

attribute [local irreducible] ComputableInPolyTime in
theorem computableInPolyTime_micaliMaxProofCap
    {V : PCPVerifier α} (hV : V.PolyTime enc) {c d : ℕ}
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1)) :
    ComputableInPolyTime
      (fun inp : MicaliRawInput α => micaliMaxProofCap V inp.sigma inp.reps d inp.stmt)
      (encMicaliRawInput enc) encUnary := by
  have htwoσ : ComputableInPolyTime (fun inp : MicaliRawInput α => 2 * inp.sigma + 1)
      (encMicaliRawInput enc) encUnary :=
    ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2) (by fun_prop))
      (ComputableInPolyTime.const 1)
  have hob : ComputableInPolyTime
      (fun inp : MicaliRawInput α => kilianOpeningEncBound inp.sigma (kilianDepth V inp.stmt))
      (encMicaliRawInput enc) encUnary :=
    ComputableInPolyTime.unary_add' (ComputableInPolyTime.const 3)
      (ComputableInPolyTime.unary_mul'
        ((computableInPolyTime_kilianDepth (enc := enc) hV hcoins).comp (by fun_prop)) htwoσ)
  exact ComputableInPolyTime.unary_add' htwoσ
    (ComputableInPolyTime.unary_mul' (by fun_prop)
      (ComputableInPolyTime.unary_add'
        (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2)
          (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const d)
            (ComputableInPolyTime.unary_add'
              (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2) hob)
              (ComputableInPolyTime.const 1))))
        (ComputableInPolyTime.const 1)))

private theorem kilianVerifyRawBounded_congr_key {H₁ H₂ : List Bool → List Bool → List Bool}
    (V : PCPVerifier α) (ch : KilianChallengeInput α) (rawProver : List Bool)
    (h : H₁ ch.key = H₂ ch.key) :
    kilianVerifyRawBounded H₁ V ch rawProver = kilianVerifyRawBounded H₂ V ch rawProver := by
  unfold kilianVerifyRawBounded
  rw [kilianVerify_congr_hash V ch.stmt _ ch.challenges _ h]

theorem computableInPolyTime_micaliVerifyRawBoundedPure
    {hTree : List Bool → List Bool} {hFS : α × List Bool → List (List Bool)}
    {V : PCPVerifier α} {σ c : ℕ}
    (hlen : ∀ y, (hTree y).length = σ)
    (hTreePoly : ComputableInPolyTime hTree encBits encBits)
    (hFSPoly : ComputableInPolyTime hFS (encPair enc encBits) (encList encBits))
    (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1)) :
    ComputableInPolyTime
      (fun p : (ℕ × α) × List Bool =>
        let (pars, rawProof) := p
        let (m, x) := pars
        micaliVerifyRawBoundedPure hTree hFS V σ m x rawProof)
      (encMicaliPureVerifierInput enc) encBool := by
  let H' : List Bool → List Bool → List Bool :=
    fun k y => if k.length == σ then hTree y else List.replicate k.length false
  have hH'_len : ∀ k y, (H' k y).length = k.length := fun k y => by
    dsimp only [H']
    split_ifs with h
    · rw [hlen y, beq_iff_eq.mp h]
    · simp
  have hH'_poly : ComputableInPolyTime (fun p : List Bool × List Bool => H' p.1 p.2)
      (encPair encBits encBits) encBits :=
    ComputableInPolyTime.ite
      (ComputableInPolyTime.beq
        (ComputableInPolyTime.length_bits.comp (ComputableInPolyTime.fst encBits encBits))
        (ComputableInPolyTime.const σ))
      (hTreePoly.comp (ComputableInPolyTime.snd encBits encBits))
      ((ComputableInPolyTime.bitsReplicate false).comp
        (ComputableInPolyTime.length_bits.comp (ComputableInPolyTime.fst encBits encBits)))
  let E := encMicaliPureVerifierInput enc
  have hpars := ComputableInPolyTime.fst (encPair encUnary enc) encBits
  have hraw := ComputableInPolyTime.snd (encPair encUnary enc) encBits
  have hm := (ComputableInPolyTime.fst encUnary enc).comp hpars
  have hx := (ComputableInPolyTime.snd encUnary enc).comp hpars
  have hroot : ComputableInPolyTime (fun p : (ℕ × α) × List Bool => unframe (p.2.take (2 * σ + 1)))
      E encBits :=
    ComputableInPolyTime.unframe.comp
      (ComputableInPolyTime.bitsTakeWithInput hraw (ComputableInPolyTime.const (2 * σ + 1)))
  have hρs : ComputableInPolyTime
      (fun p : (ℕ × α) × List Bool => hFS (p.1.2, unframe (p.2.take (2 * σ + 1))))
      E (encList encBits) :=
    hFSPoly.comp (hx.prod hroot)
  have hhas : ComputableInPolyTime (fun p : (ℕ × α) × List Bool => micaliHasRootPrefix σ p.2)
      E encBool :=
    computableInPolyTime_micaliHasRootPrefix.comp ((ComputableInPolyTime.const σ).prod hraw)
  have hcoinsU := computableInPolyTime_coins_unary hV hcoins
  have hkil := (computableInPolyTime_kilianVerifyRawBounded hH'_poly hH'_len hV hcoins).comp
    ((encKilianChallengeInput_mk_polyTime enc (ComputableInPolyTime.const (List.replicate σ false))
      hx hρs).prod hraw)
  have heq :
      (fun p : (ℕ × α) × List Bool =>
        let (pars, rawProof) := p
        let (m, x) := pars
        micaliVerifyRawBoundedPure hTree hFS V σ m x rawProof) =
      fun p : (ℕ × α) × List Bool =>
        let root := unframe (p.2.take (2 * σ + 1))
        let ρs := hFS (p.1.2, root)
        (micaliHasRootPrefix σ p.2 &&
          (ρs.length == p.1.1 && ρs.all fun ρ => ρ.length == V.coins p.1.2)) &&
        kilianVerifyRawBounded H' V ⟨List.replicate σ false, p.1.2, ρs⟩ p.2 := by
    funext ⟨⟨m, x⟩, rawProof⟩
    unfold micaliVerifyRawBoundedPure
    dsimp only
    congr 1
    exact kilianVerifyRawBounded_congr_key V _ rawProof (by funext y; simp [H'])
  rw [heq]
  exact ComputableInPolyTime.bool_and'
    (ComputableInPolyTime.bool_and' hhas
      (ComputableInPolyTime.bool_and'
        (ComputableInPolyTime.beq ((ComputableInPolyTime.length_list encBits).comp hρs) hm)
        (ComputableInPolyTime.allWithInput hρs
          (ComputableInPolyTime.beq
            (ComputableInPolyTime.length_bits.comp (ComputableInPolyTime.snd E encBits))
            (hcoinsU.comp (hx.comp (ComputableInPolyTime.fst E encBits)))))))
    hkil

/-- **Worst-case pure Micali verifier runtime and space on ALL unbounded raw proofs**: for any
polynomial-time fixed-digest hash `hTree` (`σ`-bit outputs), Fiat–Shamir oracle `hFS`, and PCP
verifier `V`, there is one fixed binary `MultiTapeTM` computing `micaliVerifyRawBoundedPure` whose
runtime and space are bounded polynomially in `m + |enc x|` uniformly over **every** `rawProof`
(including exponentially oversized or arbitrarily malformed proof strings). -/
theorem computableInTimeAndSpace_micaliVerifyRawBoundedPure_of_params
    {hTree : List Bool → List Bool} {hFS : α × List Bool → List (List Bool)}
    {V : PCPVerifier α} {σ c d : ℕ}
    (hlen : ∀ y, (hTree y).length = σ)
    (hTreePoly : ComputableInPolyTime hTree encBits encBits)
    (hFSPoly : ComputableInPolyTime hFS (encPair enc encBits) (encList encBits))
    (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1))
    (hq : ∀ x ρ, ρ.length = V.coins x → (V.queries (x, ρ)).length ≤ d) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : Turing.MultiTapeTM k Bool State)
      (t s tBound sBound : ℕ → ℕ),
      PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
      PolynomiallyBounded tBound ∧ PolynomiallyBounded sBound ∧
      tm.ComputesFunInTimeAndSpace (encMicaliPureVerifierInput enc) encBool
        (fun p =>
          let (pars, rawProof) := p
          let (m, x) := pars
          micaliVerifyRawBoundedPure hTree hFS V σ m x rawProof)
        (fun p => t (encPair encUnary enc p.1).length)
        (fun p => s (encPair encUnary enc p.1).length) ∧
      (∀ (m : ℕ) (x : α) (rawProof : List Bool),
        tm.ComputesInTimeAndSpace
          (encMicaliPureVerifierInput enc ((m, x), rawProof))
          (encBool (micaliVerifyRawBoundedPure hTree hFS V σ m x rawProof))
          (tBound (m + (enc x).length))
          (sBound (m + (enc x).length))) := by
  have hcap : ComputableInPolyTime
      (fun p : ℕ × α => micaliMaxProofCap V σ p.1 d p.2) (encPair encUnary enc) encUnary :=
    (computableInPolyTime_micaliMaxProofCap (enc := enc) hV (d := d) hcoins).comp
      (show ComputableInPolyTime (fun p : ℕ × α => MicaliRawInput.mk σ p.1 p.2)
          (encPair encUnary enc) (encMicaliRawInput enc) by fun_prop)
  obtain ⟨k, State, hfin, tm, t, s, ht_pb, hs_pb, htm⟩ :=
    computableInTimeAndSpace_boundedPrefix hcap
      (computableInPolyTime_micaliVerifyRawBoundedPure hlen hTreePoly hFSPoly hV hcoins)
      (fun ⟨m, x⟩ rawProof => micaliVerifyRawBoundedPure_take_eq hTree hFS V hq x rawProof)
  obtain ⟨ct, dt, htle⟩ := polynomiallyBounded_iff_le.mp ht_pb
  obtain ⟨cs, ds, hsle⟩ := polynomiallyBounded_iff_le.mp hs_pb
  let t' (u : ℕ) : ℕ := ct * (u + 1) ^ dt
  let s' (u : ℕ) : ℕ := cs * (u + 1) ^ ds
  let inBound (u : ℕ) : ℕ := 2 * u + 1
  have ht'_pb : PolynomiallyBounded t' := polynomiallyBounded_iff_le.mpr ⟨ct, dt, fun _ => le_rfl⟩
  have hs'_pb : PolynomiallyBounded s' := polynomiallyBounded_iff_le.mpr ⟨cs, ds, fun _ => le_rfl⟩
  have hin_pb : PolynomiallyBounded inBound := by
    dsimp only [inBound]
    fun_prop
  have htm' := htm.mono (fun p => htle _) (fun p => hsle _)
  refine ⟨k, State, hfin, tm, t', s', fun u => t' (inBound u), fun u => s' (inBound u),
    ht'_pb, hs'_pb, ht'_pb.comp hin_pb, hs'_pb.comp hin_pb, htm', fun m x rawProof => ?_⟩
  have hlen_in : (encPair encUnary enc (m, x)).length ≤ inBound (m + (enc x).length) := by
    simp only [length_encPair, encUnary_apply, List.length_replicate, inBound]; omega
  have hp := htm' ((m, x), rawProof)
  exact ⟨hp.1,
    hp.2.1.mono (Nat.mul_le_mul_left ct (Nat.pow_le_pow_left (Nat.succ_le_succ hlen_in) dt)),
    hp.2.2.mono (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left (Nat.succ_le_succ hlen_in) ds))⟩

end PureMachineComplexity

section NativeROMVerifier

variable {α : Type}

/-- Native two-channel Micali bounded-prefix verifier program over `MicaliSpec α`.
Checks `micaliHasRootPrefix` before issuing the single Fiat–Shamir query `(x, root)`, validates
the received challenge lengths, raw proof cap, and opening lengths before issuing any Merkle
queries, and delegates to `kilianVerifyProg`. -/
def micaliVerifyRawBounded (V : PCPVerifier α) (σ m : ℕ) (x : α)
    (rawProof : List Bool) : OracleComp (MicaliSpec α) Bool := do
  if !micaliHasRootPrefix σ rawProof then
    return false
  let root := unframe (rawProof.take (2 * σ + 1))
  let ρs ← OracleComp.liftRight (spec₁ := MerkleHashSpec)
    (OracleComp.query (spec := MicaliFSSpec α) (x, root))
  if !(ρs.length == m && ρs.all fun ρ => ρ.length == V.coins x) then
    return false
  if rawProof.length > kilianRawProverCap V (List.replicate σ false) x ρs then
    return false
  let resp := (micaliProofDecoder.decode rawProof).response
  if !kilianStructValid V x root ρs resp then
    return false
  OracleComp.liftLeft (spec₂ := MicaliFSSpec α) (kilianVerifyProg V x root ρs resp)

theorem evalPure_micaliVerifyRawBounded (hTree : List Bool → List Bool)
    (hFS : α × List Bool → List (List Bool)) (V : PCPVerifier α) (σ m : ℕ) (x : α)
    (rawProof : List Bool) :
    OracleComp.evalPure (micaliOracle hTree hFS)
        (micaliVerifyRawBounded V σ m x rawProof) =
      micaliVerifyRawBoundedPure hTree hFS V σ m x rawProof := by
  unfold micaliVerifyRawBounded micaliVerifyRawBoundedPure
  dsimp only
  by_cases hhas : micaliHasRootPrefix σ rawProof = true
  · obtain ⟨_, _, hunf⟩ := unframe_take_of_micaliHasRootPrefix hhas
    have hdec : kilianProverMsgDecoder.decode rawProof =
        (unframe (rawProof.take (2 * σ + 1)), (micaliProofDecoder.decode rawProof).response) := by
      simp [micaliProofDecoder, Decoder.map, kilianProverMsgDecoder, Decoder.pair, Decoder.bits,
        hunf]
    simp only [hhas, Bool.not_true, Bool.false_eq_true, ↓reduceIte, OracleComp.evalPure_bind,
      OracleComp.evalPure_liftRight, OracleComp.evalPure_query]
    set root := unframe (rawProof.take (2 * σ + 1))
    set ρs := hFS (x, root)
    by_cases hch : (ρs.length == m && ρs.all fun ρ => ρ.length == V.coins x) = true
    · simp only [hch, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.true_and, gt_iff_lt]
      by_cases hgt : kilianRawProverCap V (List.replicate σ false) x ρs < rawProof.length
      · have hle : ¬ rawProof.length ≤ kilianRawProverCap V (List.replicate σ false) x ρs := by
          omega
        simp [hgt, kilianVerifyRawBounded, hle]
      · have hle : rawProof.length ≤ kilianRawProverCap V (List.replicate σ false) x ρs := by
          omega
        simp only [hgt, ↓reduceIte, kilianVerifyRawBounded, hle, decide_true, Bool.true_and, hdec]
        by_cases hst :
            kilianStructValid V x root ρs (micaliProofDecoder.decode rawProof).response = true
        · simp only [hst, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            OracleComp.evalPure_liftLeft, evalPure_kilianVerifyProg]
          exact (kilianVerify_congr_hash V x root ρs _ rfl).symm
        · simp only [Bool.not_eq_true] at hst
          simp only [hst, Bool.not_false, ↓reduceIte, OracleComp.evalPure_pure]
          symm
          by_contra hver
          simp only [Bool.not_eq_false] at hver
          exact absurd (kilianStructValid_of_kilianVerify hver) (by simp [hst])
    · simp only [Bool.not_eq_true] at hch
      simp [hch]
  · simp only [Bool.not_eq_true] at hhas
    simp [hhas]

private theorem isCostBounded_mapM_le {ι β γ : Type} {spec : OracleSpec ι} {cost : ι → ℕ}
    {f : β → OracleComp spec γ} {xs : List β} {k : ℕ}
    (hf : ∀ x ∈ xs, OracleComp.IsCostBounded cost (f x) k) :
    OracleComp.IsCostBounded cost (xs.mapM f) (xs.length * k) := by
  induction xs with
  | nil => simpa using OracleComp.IsCostBounded.pure [] 0
  | cons hd tl ih =>
    simp only [List.mapM_cons, List.length_cons]
    have h1 := hf hd List.mem_cons_self
    have h2 := ih fun x hx => hf x (List.mem_cons_of_mem _ hx)
    have hb : OracleComp.IsCostBounded cost
        (do let y ← f hd; let ys ← tl.mapM f; pure (y :: ys)) (k + tl.length * k) :=
      h1.bind fun y => h2.bind fun ys => OracleComp.IsCostBounded.pure (y :: ys) 0
    simpa [Nat.succ_mul, Nat.add_comm] using hb

private theorem isCostBounded_mapM_zip_bind_pure {ι β γ δ ε : Type} {spec : OracleSpec ι}
    {cost : ι → ℕ} {xs : List β} {ys : List γ} {f : β × γ → OracleComp spec δ}
    {g : List δ → ε} {k n : ℕ}
    (hlen : (xs.zip ys).length ≤ n)
    (hf : ∀ p ∈ xs.zip ys, OracleComp.IsCostBounded cost (f p) k) :
    OracleComp.IsCostBounded cost ((xs.zip ys).mapM f >>= fun r => pure (g r)) (n * k) :=
  ((isCostBounded_mapM_le hf).bind fun _ => OracleComp.IsCostBounded.pure _ 0).mono
    (Nat.mul_le_mul_right k hlen)

/-- `micaliVerifyRawBounded` issues at most `1` Fiat–Shamir oracle query on every `rawProof`. -/
theorem isCostBounded_micaliFSCost_micaliVerifyRawBounded (V : PCPVerifier α) (σ m : ℕ) (x : α)
    (rawProof : List Bool) :
    OracleComp.IsCostBounded micaliFSCost (micaliVerifyRawBounded V σ m x rawProof) 1 := by
  unfold micaliVerifyRawBounded
  split_ifs
  · exact OracleComp.IsCostBounded.pure _ _
  · have hq : OracleComp.IsCostBounded micaliFSCost
        (OracleComp.liftRight (spec₁ := MerkleHashSpec)
          (OracleComp.query (spec := MicaliFSSpec α) (x, unframe (rawProof.take (2 * σ + 1))))) 1 :=
      OracleComp.IsCostBounded.query (spec := MicaliSpec α) (cost := micaliFSCost) (.inr _)
    refine hq.bind (m := 0) fun ρs => ?_
    dsimp only
    split_ifs <;> try exact OracleComp.IsCostBounded.pure _ _
    exact OracleComp.IsCostBounded.liftLeft_of_cost_inl_eq_zero (cost := micaliFSCost)
      (fun _ => rfl) _

private theorem isQueryBounded_kilianVerifyProg_of_structValid {V : PCPVerifier α} {d : ℕ}
    {x : α} {root : List Bool} {ρs : List (List Bool)} {resp : KilianResponse}
    (hq : ∀ ρ ∈ ρs, (V.queries (x, ρ)).length ≤ d)
    (hvalid : kilianStructValid V x root ρs resp = true) :
    OracleComp.IsQueryBounded (kilianVerifyProg V x root ρs resp)
      (ρs.length * (d * (kilianDepth V x + 1))) := by
  simp only [kilianStructValid, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hvalid
  refine isCostBounded_mapM_zip_bind_pure (by rw [List.length_zip, hvalid.1, min_self])
    fun ⟨ρ, answers⟩ hmem => ?_
  obtain ⟨hlenA, hallO⟩ := hvalid.2 (ρ, answers) hmem
  refine isCostBounded_mapM_zip_bind_pure (by
      rw [List.length_zip, hlenA, min_self]
      exact hq ρ (List.of_mem_zip hmem).1)
    fun ⟨a, o⟩ ho => ?_
  simpa only [(hallO o (List.of_mem_zip ho).2).1] using
    isQueryBounded_merkleVerifyProg (kilianDepth V x) root (kilianPosition V x a) [o.leaf] o.path

/-- `micaliVerifyRawBounded` issues at most `m * d * (kilianDepth V x + 1)` Merkle hash queries on
every raw input `rawProof` (even arbitrarily oversized or malformed inputs). -/
theorem isCostBounded_micaliMTCost_micaliVerifyRawBounded {V : PCPVerifier α} {σ m d : ℕ}
    (hq : ∀ x ρ, ρ.length = V.coins x → (V.queries (x, ρ)).length ≤ d)
    (x : α) (rawProof : List Bool) :
    OracleComp.IsCostBounded micaliMTCost (micaliVerifyRawBounded V σ m x rawProof)
      (m * d * (kilianDepth V x + 1)) := by
  unfold micaliVerifyRawBounded
  split_ifs
  · exact OracleComp.IsCostBounded.pure _ _
  · have hqfs : OracleComp.IsCostBounded micaliMTCost
        (OracleComp.liftRight (spec₁ := MerkleHashSpec)
          (OracleComp.query (spec := MicaliFSSpec α) (x, unframe (rawProof.take (2 * σ + 1))))) 0 :=
      OracleComp.IsCostBounded.query (spec := MicaliSpec α) (cost := micaliMTCost) (.inr _)
    simpa only [Nat.zero_add] using hqfs.bind (m := m * d * (kilianDepth V x + 1)) fun ρs => by
      split_ifs with hch _ hst <;> try exact OracleComp.IsCostBounded.pure _ _
      have hch' : ρs.length = m ∧ ∀ ρ ∈ ρs, ρ.length = V.coins x := by
        simpa [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] using hch
      have hkv := isQueryBounded_kilianVerifyProg_of_structValid
        (fun ρ hρ => hq x ρ (hch'.2 ρ hρ)) (by simpa using hst)
      rw [hch'.1, ← Nat.mul_assoc] at hkv
      exact hkv.liftLeft fun _ => le_rfl

end NativeROMVerifier

section WordOracleVerifier

/-- Finite operation tag for the native two-channel word-oracle Micali verifier. -/
inductive MicaliWordOp where
  | merkle : MicaliWordOp
  | fs : MicaliWordOp
  deriving DecidableEq, Repr, Inhabited

instance : Finite MicaliWordOp :=
  Finite.of_equiv Bool
    { toFun := fun b => if b then .fs else .merkle
      invFun := fun op => match op with | .merkle => false | .fs => true
      left_inv := fun b => by cases b <;> rfl
      right_inv := fun op => by cases op <;> rfl }

section WordPrograms

variable {α : Type}

/-- Word-oracle step matching `merkleInputsStepProg`: maintains `(remainingPath, curIn, pos)` so
every intermediate state fits within polynomial space and `IsOraclePPTOn.iterateWith_spec`
applies. -/
def merkleWordStep (σ : ℕ) (state : List (List Bool) × List Bool × ℕ) :
    WordOracleComp MicaliWordOp (List (List Bool) × List Bool × ℕ) := do
  let (rem, curIn, pos) := state
  let node ← List.take σ <$> ProbOracleComp.query
    (spec := fun _ : MicaliWordOp × List Bool => List Bool) (.merkle, curIn)
  let sib := rem.headD []
  let nextIn := if pos % 2 = 0 then encPair encBits encBits (node, sib)
    else encPair encBits encBits (sib, node)
  return (rem.tail, nextIn, pos / 2)

/-- Word-oracle Merkle verification matching `merkleVerifyProg` with digest length cap `σ`. -/
def merkleVerifyWord (σ depth : ℕ) (root : List Bool) (i : ℕ) (leaf : List Bool)
    (path : List (List Bool)) : WordOracleComp MicaliWordOp Bool := do
  let (_, finalIn, _) ← OracleComp.iterate path.length (merkleWordStep σ) (path, leaf, i)
  let cand ← List.take σ <$> ProbOracleComp.query
    (spec := fun _ : MicaliWordOp × List Bool => List Bool) (.merkle, finalIn)
  return path.length == depth && decide (i < 2 ^ depth) &&
    path.all (fun s => s.length == root.length) && cand == root

/-- Word-oracle Kilian single-repetition verification. -/
def kilianCheckWord (V : PCPVerifier α) (σ : ℕ) (x : α) (root ρ : List Bool)
    (answers : List (MerkleOpening Bool)) : WordOracleComp MicaliWordOp Bool := do
  let queries := V.queries (x, ρ)
  let depth := kilianDepth V x
  let checks ← (queries.zip answers).mapM fun (a, o) =>
    merkleVerifyWord σ depth root (kilianPosition V x a) [o.leaf] o.path
  return answers.length == queries.length &&
    checks.all id &&
    V.verdict ((x, ρ), answers.map MerkleOpening.leaf)

/-- Word-oracle Kilian multi-repetition verification. -/
def kilianVerifyWord (V : PCPVerifier α) (σ : ℕ) (x : α) (root : List Bool)
    (ρs : List (List Bool)) (resp : KilianResponse) : WordOracleComp MicaliWordOp Bool := do
  let checks ← (ρs.zip resp).mapM fun (ρ, answers) =>
    kilianCheckWord V σ x root ρ answers
  return resp.length == ρs.length && checks.all id

/-- Core native word-oracle Micali verifier taking explicit `((σ, m, x), rawProof)` and capping
both the `.fs` challenge reply at `micaliFSReplyCap enc c m x + 1` and every `.merkle` digest
reply at `σ`. Rejecting whenever `fsWord.length > micaliFSReplyCap enc c m x` guarantees no
malformed Fiat–Shamir reply is silently corrupted by prefix truncation. -/
def micaliVerifyRawWordCore (V : PCPVerifier α) (enc : α ↪ List Bool) (c : ℕ)
    (input : MicaliRawInput α × List Bool) : WordOracleComp MicaliWordOp Bool := do
  let (inp, rawProof) := input
  if !micaliHasRootPrefix inp.sigma rawProof then
    return false
  let root := unframe (rawProof.take (2 * inp.sigma + 1))
  let fsCap := micaliFSReplyCap enc c inp.reps inp.stmt
  let fsWord ← List.take (fsCap + 1) <$> ProbOracleComp.query
    (spec := fun _ : MicaliWordOp × List Bool => List Bool)
    (.fs, encPair enc encBits (inp.stmt, root))
  if fsWord.length > fsCap then
    return false
  let ρs := (Decoder.list Decoder.bits).decode fsWord
  if !(ρs.length == inp.reps && ρs.all fun ρ => ρ.length == V.coins inp.stmt) then
    return false
  if rawProof.length > kilianRawProverCap V (List.replicate inp.sigma false) inp.stmt ρs then
    return false
  let resp := (micaliProofDecoder.decode rawProof).response
  if !kilianStructValid V inp.stmt root ρs resp then
    return false
  kilianVerifyWord V inp.sigma inp.stmt root ρs resp

/-- Bounded-prefix wrapper around `micaliVerifyRawWordCore` that truncates `rawProof` to
`micaliMaxProofCap V inp.sigma inp.reps d inp.stmt + 1` bits first, achieving worst-case halting
oracle runtime polynomial in `σ + m + |enc x|` uniformly over **all** arbitrary unbounded
`rawProof`. -/
def micaliVerifyRawWord (V : PCPVerifier α) (enc : α ↪ List Bool) (c d : ℕ)
    (input : MicaliRawInput α × List Bool) : WordOracleComp MicaliWordOp Bool :=
  let (inp, rawProof) := input
  micaliVerifyRawWordCore V enc c
    (inp, rawProof.take (micaliMaxProofCap V inp.sigma inp.reps d inp.stmt + 1))

end WordPrograms

section WordBisimulation

variable {α : Type}

/-- Classical `OracleCodec` embedding `MicaliSpec α` into `MicaliWordOp × List Bool` using
`encPair enc encBits` for Fiat–Shamir queries `(x, root)`. -/
noncomputable def micaliWordCodec (enc : α ↪ List Bool) :
    OracleCodec MicaliWordOp (List Bool ⊕ (α × List Bool)) (MicaliSpec α) where
  encodeQuery q := match q with | .inl w => (.merkle, w) | .inr xr => (.fs, encPair enc encBits xr)
  decodeQuery req :=
    letI := Classical.propDecidable
    match req.1 with
    | .merkle => some (.inl req.2)
    | .fs =>
      if h : ∃ xr : α × List Bool, encPair enc encBits xr = req.2 then
        some (.inr (Classical.choose h))
      else none
  decodeQuery_eq_some_iff req q := by
    let this := Classical.propDecidable
    rcases req with ⟨op, w⟩
    rcases op with _ | _
    · rcases q with u | xr
      · simp [eq_comm]
      · simp
    · rcases q with u | xr
      · simp only
        constructor
        · intro h
          split_ifs at h; cases h
        · intro h
          cases h
      · simp only
        constructor
        · intro h
          split_ifs at h with hex
          · simp only [Option.some.injEq, Sum.inr.injEq] at h
            subst h
            exact congrArg (fun z => (MicaliWordOp.fs, z)) (Classical.choose_spec hex)
        · intro heq
          have hweq : encPair enc encBits xr = w := by simpa using heq
          have hex : ∃ xr' : α × List Bool, encPair enc encBits xr' = w := ⟨xr, hweq⟩
          simp only [hex, ↓reduceDIte, Option.some.injEq, Sum.inr.injEq]
          exact (encPair enc encBits).injective ((Classical.choose_spec hex).trans hweq.symm)
  encodeReply q :=
    match q with
    | .inl _ => encBits
    | .inr _ => encList encBits

private theorem runWith_wordOracle_merkle_take {State : Type}
    (oracle : (q : List Bool ⊕ (α × List Bool)) → StateT State PMF (MicaliSpec α q))
    {enc : α ↪ List Bool} {σ : ℕ}
    (hMT : ∀ w s d s', (d, s') ∈ (oracle (.inl w) s).support → d.length ≤ σ)
    (w : List Bool) (s : State) :
    ProbOracleComp.runWith ((micaliWordCodec enc).wordOracle oracle)
        (List.take σ <$> ProbOracleComp.query
          (spec := fun _ : MicaliWordOp × List Bool => List Bool) (.merkle, w)) s =
      OracleComp.runWith oracle (OracleComp.liftLeft (spec₂ := MicaliFSSpec α)
        (OracleComp.query (spec := MerkleHashSpec) w)) s := by
  simp only [ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
    OracleComp.liftLeft_query, OracleComp.runWith_query]
  have hw : ((micaliWordCodec enc).wordOracle oracle (.merkle, w) s) =
      PMF.map (Prod.map encBits id) (oracle (.inl w) s) := by
    have h := (micaliWordCodec enc).wordOracle_encodeQuery oracle (.inl w)
    exact congrFun h s
  rw [hw, PMF.map_comp]
  refine (PMF.map_congr_on_support _ _ _root_.id fun ⟨d, s'⟩ hmem => ?_).trans (PMF.map_id _)
  exact Prod.ext (List.take_of_length_le (hMT w s d s' hmem)) rfl

private theorem runWith_wordOracle_mapM_liftLeft {β State γ : Type}
    (woracle : MicaliWordOp × List Bool → StateT State PMF (List Bool))
    (oracle : (q : List Bool ⊕ (α × List Bool)) → StateT State PMF (MicaliSpec α q))
    (fW : β → WordOracleComp MicaliWordOp γ) (fO : β → OracleComp MerkleHashSpec γ)
    (hstep : ∀ b s, ProbOracleComp.runWith woracle (fW b) s =
      OracleComp.runWith oracle (OracleComp.liftLeft (spec₂ := MicaliFSSpec α) (fO b)) s)
    (xs : List β) (s : State) :
    ProbOracleComp.runWith woracle (xs.mapM fW) s =
      OracleComp.runWith oracle (OracleComp.liftLeft (spec₂ := MicaliFSSpec α) (xs.mapM fO)) s := by
  induction xs generalizing s with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.mapM_cons, ProbOracleComp.runWith_bind, hstep hd s, OracleComp.liftLeft_bind,
      OracleComp.runWith_bind]
    refine PMF.bind_congr_on_support _ _ _ fun ⟨_, s₁⟩ _ => ?_
    simp only [ProbOracleComp.runWith_pure, OracleComp.liftLeft_pure, OracleComp.runWith_pure,
      ih s₁]

private theorem runWith_merkleVerifyWord_eq {State : Type}
    (oracle : (q : List Bool ⊕ (α × List Bool)) → StateT State PMF (MicaliSpec α q))
    {enc : α ↪ List Bool} {σ : ℕ}
    (hMT : ∀ w s d s', (d, s') ∈ (oracle (.inl w) s).support → d.length ≤ σ)
    (depth : ℕ) (root : List Bool) (i : ℕ) (leaf : List Bool) (path : List (List Bool))
    (s : State) :
    ProbOracleComp.runWith ((micaliWordCodec enc).wordOracle oracle)
        (merkleVerifyWord σ depth root i leaf path) s =
      OracleComp.runWith oracle
        (OracleComp.liftLeft (spec₂ := MicaliFSSpec α)
          (merkleVerifyProg depth root i leaf path)) s := by
  have hind : ∀ (n : ℕ) (hist rem : List (List Bool)) (pos : ℕ),
      rem.length = n → ∀ st : State,
        ProbOracleComp.runWith ((micaliWordCodec enc).wordOracle oracle)
            ((fun stp => (stp.2.1, stp.2.2)) <$>
              OracleComp.iterate n (merkleWordStep σ) (rem, hist.headD [], pos)) st =
          OracleComp.runWith oracle
            (OracleComp.liftLeft (spec₂ := MicaliFSSpec α)
              ((fun res => (res.1.headD [], res.2)) <$>
                rem.foldlM merkleInputsStepProg (hist, pos))) st := by
    intro n
    induction n with
    | zero =>
      intro hist rem pos hlen st
      rcases List.length_eq_zero_iff.mp hlen with rfl
      simp
    | succ n ih =>
      intro hist rem pos hlen st
      rcases rem with _ | ⟨sib, rem'⟩
      · simp at hlen
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      rw [OracleComp.iterate_succ_bind, List.foldlM_cons, map_bind, map_bind,
        ProbOracleComp.runWith_bind, OracleComp.liftLeft_bind, OracleComp.runWith_bind]
      have hmw : ProbOracleComp.runWith ((micaliWordCodec enc).wordOracle oracle)
            (merkleWordStep σ (sib :: rem', hist.headD [], pos)) st =
          PMF.map (fun ⟨node, s'⟩ =>
              ((rem', if pos % 2 = 0 then encPair encBits encBits (node, sib)
                  else encPair encBits encBits (sib, node), pos / 2), s'))
            (oracle (.inl (hist.headD [])) st) := by
        simp only [merkleWordStep, ProbOracleComp.runWith_bind, List.headD_cons, List.tail_cons,
          ProbOracleComp.runWith_pure]
        rw [show ProbOracleComp.runWith ((micaliWordCodec enc).wordOracle oracle)
            (List.take σ <$> ProbOracleComp.query
              (spec := fun _ : MicaliWordOp × List Bool => List Bool) (.merkle, hist.headD [])) st =
            oracle (.inl (hist.headD [])) st from
          by simpa [OracleComp.liftLeft_query, OracleComp.runWith_query] using
            runWith_wordOracle_merkle_take oracle hMT (hist.headD []) st]
        rfl
      have hmi : OracleComp.runWith oracle
            (OracleComp.liftLeft (spec₂ := MicaliFSSpec α)
              (merkleInputsStepProg (hist, pos) sib)) st =
          PMF.map (fun ⟨node, s'⟩ =>
              (((if pos % 2 = 0 then encPair encBits encBits (node, sib)
                  else encPair encBits encBits (sib, node)) :: hist, pos / 2), s'))
            (oracle (.inl (hist.headD [])) st) := by
        simp only [merkleInputsStepProg, OracleComp.liftLeft_bind, OracleComp.liftLeft_query,
          OracleComp.liftLeft_pure, OracleComp.runWith_bind, OracleComp.runWith_query,
          OracleComp.runWith_pure]
        rfl
      rw [hmw, hmi, PMF.bind_map, PMF.bind_map]
      refine PMF.bind_congr_on_support _ _ _ fun ⟨node, s'⟩ _ => ?_
      simpa only [Function.comp_def, List.headD_cons] using ih (_ :: hist) rem' (pos / 2) hlen s'
  have hfold := hind path.length [leaf] path i rfl s
  simp only [List.headD_cons] at hfold
  have hlhs :
      merkleVerifyWord σ depth root i leaf path =
      ((fun stp : List (List Bool) × List Bool × ℕ => (stp.2.1, stp.2.2)) <$>
          OracleComp.iterate path.length (merkleWordStep σ) (path, leaf, i)) >>=
        fun fp => do
          let cand ← List.take σ <$> ProbOracleComp.query
            (spec := fun _ : MicaliWordOp × List Bool => List Bool) (.merkle, fp.1)
          return path.length == depth && decide (i < 2 ^ depth) &&
            path.all (fun s => s.length == root.length) && cand == root := by
    simp only [merkleVerifyWord, bind_map_left]
  have hrhs :
      OracleComp.liftLeft (spec₂ := MicaliFSSpec α) (merkleVerifyProg depth root i leaf path) =
      OracleComp.liftLeft (spec₂ := MicaliFSSpec α)
        (((fun res : List (List Bool) × ℕ => (res.1.headD [], res.2)) <$>
            path.foldlM merkleInputsStepProg ([leaf], i)) >>=
          fun fp => do
            let cand ← OracleComp.query (spec := MerkleHashSpec) fp.1
            return path.length == depth && decide (i < 2 ^ depth) &&
              path.all (fun s => s.length == root.length) && cand == root) := by
    simp only [merkleVerifyProg, merkleRootOfPathProg, merkleInputsProg, bind_assoc, pure_bind,
      bind_map_left]
  rw [hlhs, hrhs, ProbOracleComp.runWith_bind, OracleComp.liftLeft_bind, OracleComp.runWith_bind,
    hfold]
  refine PMF.bind_congr_on_support _ _ _ fun ⟨fp, s₁⟩ _ => ?_
  rw [ProbOracleComp.runWith_bind, runWith_wordOracle_merkle_take oracle hMT fp.1 s₁,
    OracleComp.liftLeft_bind, OracleComp.runWith_bind]
  refine PMF.bind_congr_on_support _ _ _ fun ⟨_, _⟩ _ => by simp

private theorem runWith_kilianCheckWord_eq {State : Type}
    (oracle : (q : List Bool ⊕ (α × List Bool)) → StateT State PMF (MicaliSpec α q))
    {enc : α ↪ List Bool} {σ : ℕ}
    (hMT : ∀ w s d s', (d, s') ∈ (oracle (.inl w) s).support → d.length ≤ σ)
    (V : PCPVerifier α) (x : α) (root ρ : List Bool) (answers : List (MerkleOpening Bool))
    (s : State) :
    ProbOracleComp.runWith ((micaliWordCodec enc).wordOracle oracle)
        (kilianCheckWord V σ x root ρ answers) s =
      OracleComp.runWith oracle
        (OracleComp.liftLeft (spec₂ := MicaliFSSpec α)
          (kilianCheckProg V x root ρ answers)) s := by
  unfold kilianCheckWord kilianCheckProg
  rw [ProbOracleComp.runWith_bind, OracleComp.liftLeft_bind, OracleComp.runWith_bind]
  have hm := runWith_wordOracle_mapM_liftLeft ((micaliWordCodec enc).wordOracle oracle) oracle
    (fun (a, o) => merkleVerifyWord σ (kilianDepth V x) root (kilianPosition V x a) [o.leaf] o.path)
    (fun (a, o) => merkleVerifyProg (kilianDepth V x) root (kilianPosition V x a) [o.leaf] o.path)
    (fun (a, o) st => runWith_merkleVerifyWord_eq oracle hMT (kilianDepth V x) root
      (kilianPosition V x a) [o.leaf] o.path st)
    ((V.queries (x, ρ)).zip answers) s
  rw [hm]
  refine PMF.bind_congr_on_support _ _ _ fun ⟨_, _⟩ _ => by simp

private theorem runWith_kilianVerifyWord_eq {State : Type}
    (oracle : (q : List Bool ⊕ (α × List Bool)) → StateT State PMF (MicaliSpec α q))
    {enc : α ↪ List Bool} {σ : ℕ}
    (hMT : ∀ w s d s', (d, s') ∈ (oracle (.inl w) s).support → d.length ≤ σ)
    (V : PCPVerifier α) (x : α) (root : List Bool) (ρs : List (List Bool))
    (resp : KilianResponse) (s : State) :
    ProbOracleComp.runWith ((micaliWordCodec enc).wordOracle oracle)
        (kilianVerifyWord V σ x root ρs resp) s =
      OracleComp.runWith oracle
        (OracleComp.liftLeft (spec₂ := MicaliFSSpec α)
          (kilianVerifyProg V x root ρs resp)) s := by
  unfold kilianVerifyWord kilianVerifyProg
  rw [ProbOracleComp.runWith_bind, OracleComp.liftLeft_bind, OracleComp.runWith_bind]
  have hm := runWith_wordOracle_mapM_liftLeft ((micaliWordCodec enc).wordOracle oracle) oracle
    (fun (ρ, answers) => kilianCheckWord V σ x root ρ answers)
    (fun (ρ, answers) => kilianCheckProg V x root ρ answers)
    (fun (ρ, answers) st => runWith_kilianCheckWord_eq oracle hMT V x root ρ answers st)
    (ρs.zip resp) s
  rw [hm]
  refine PMF.bind_congr_on_support _ _ _ fun ⟨_, _⟩ _ => by simp

/-- **Stateful ROM bisimulation for the native word-oracle Micali verifier**: under the word oracle
`((micaliWordCodec enc).wordOracle oracle)` of ANY stateful `(MicaliSpec α)` handler whose `.inl`
Merkle digests have length at most `σ` (with NO condition on its `.inr` Fiat–Shamir handler), both
`micaliVerifyRawWordCore` and `micaliVerifyRawWord` produce the exact same joint output and final
oracle state distribution as `micaliVerifyRawBounded`. -/
theorem runWith_wordOracle_micaliVerifyRawWordCore {State : Type}
    (oracle : (q : List Bool ⊕ (α × List Bool)) → StateT State PMF (MicaliSpec α q))
    {V : PCPVerifier α} {enc : α ↪ List Bool} {c σ m : ℕ}
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1))
    (hMT : ∀ w s d s', (d, s') ∈ (oracle (.inl w) s).support → d.length ≤ σ)
    (x : α) (rawProof : List Bool) (s : State) :
    ProbOracleComp.runWith ((micaliWordCodec enc).wordOracle oracle)
        (micaliVerifyRawWordCore V enc c (⟨σ, m, x⟩, rawProof)) s =
      OracleComp.runWith oracle (micaliVerifyRawBounded V σ m x rawProof) s := by
  unfold micaliVerifyRawWordCore micaliVerifyRawBounded
  dsimp only
  by_cases hhas : micaliHasRootPrefix σ rawProof = true
  · simp only [hhas, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    set root := unframe (rawProof.take (2 * σ + 1))
    set fsCap := micaliFSReplyCap enc c m x
    have hqfs : ProbOracleComp.runWith ((micaliWordCodec enc).wordOracle oracle)
          (List.take (fsCap + 1) <$> ProbOracleComp.query
            (spec := fun _ : MicaliWordOp × List Bool => List Bool)
            (.fs, encPair enc encBits (x, root))) s =
        PMF.map (Prod.map (fun ρs => (encList encBits ρs).take (fsCap + 1)) id)
          (oracle (.inr (x, root)) s) := by
      simp only [ProbOracleComp.runWith_map, ProbOracleComp.runWith_query]
      have hw : (micaliWordCodec enc).wordOracle oracle (.fs, encPair enc encBits (x, root)) s =
          PMF.map (Prod.map (encList encBits) id) (oracle (.inr (x, root)) s) :=
        congrFun ((micaliWordCodec enc).wordOracle_encodeQuery oracle (.inr (x, root))) s
      rw [hw, PMF.map_comp]; rfl
    rw [ProbOracleComp.runWith_bind, hqfs, PMF.bind_map, OracleComp.runWith_bind,
      OracleComp.liftRight_query, OracleComp.runWith_query]
    refine PMF.bind_congr_on_support _ _ _ fun ⟨ρs, s₁⟩ _ => ?_
    dsimp only [Function.comp_def, Prod.map_apply, id_eq]
    by_cases hfit : (encList encBits ρs).length ≤ fsCap
    · have htake : (encList encBits ρs).take (fsCap + 1) = encList encBits ρs :=
        List.take_of_length_le (hfit.trans (Nat.le_succ fsCap))
      have hgt : ¬ ((encList encBits ρs).take (fsCap + 1)).length > fsCap := by rw [htake]; omega
      have hdec : (Decoder.list Decoder.bits).decode ((encList encBits ρs).take (fsCap + 1)) =
          ρs := by
        rw [htake, (Decoder.list Decoder.bits).decode_enc]
      simp only [hgt, ↓reduceIte, hdec]
      split_ifs <;> try simp
      exact runWith_kilianVerifyWord_eq oracle hMT V x root ρs
        (micaliProofDecoder.decode rawProof).response s₁
    · have hgt : ((encList encBits ρs).take (fsCap + 1)).length > fsCap := by
        simp [List.length_take]; omega
      have hbad : (ρs.length == m && ρs.all fun ρ => ρ.length == V.coins x) = false := by
        by_contra htrue
        simp only [Bool.not_eq_false, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at htrue
        have := length_encList_le_micaliFSReplyCap enc hcoins htrue.1 htrue.2
        omega
      simp only [hgt, ↓reduceIte, hbad, Bool.not_false, ProbOracleComp.runWith_pure,
        OracleComp.runWith_pure]
  · simp [show micaliHasRootPrefix σ rawProof = false from Bool.eq_false_iff.mpr hhas]

theorem runWith_wordOracle_micaliVerifyRawWord {State : Type}
    (oracle : (q : List Bool ⊕ (α × List Bool)) → StateT State PMF (MicaliSpec α q))
    {V : PCPVerifier α} {enc : α ↪ List Bool} {c d σ m : ℕ}
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1))
    (hq : ∀ x ρ, ρ.length = V.coins x → (V.queries (x, ρ)).length ≤ d)
    (hMT : ∀ w s d' s', (d', s') ∈ (oracle (.inl w) s).support → d'.length ≤ σ)
    (x : α) (rawProof : List Bool) (s : State) :
    ProbOracleComp.runWith ((micaliWordCodec enc).wordOracle oracle)
        (micaliVerifyRawWord V enc c d (⟨σ, m, x⟩, rawProof)) s =
      OracleComp.runWith oracle (micaliVerifyRawBounded V σ m x rawProof) s := by
  unfold micaliVerifyRawWord
  dsimp only
  rw [runWith_wordOracle_micaliVerifyRawWordCore oracle hcoins hMT]
  set maxCap := micaliMaxProofCap V σ m d x
  by_cases hle : rawProof.length ≤ maxCap
  · rw [List.take_of_length_le (hle.trans (Nat.le_succ maxCap))]
  · have hpfxEq : (rawProof.take (maxCap + 1)).take (2 * σ + 1) = rawProof.take (2 * σ + 1) := by
      rw [List.take_take, Nat.min_eq_left
        ((show 2 * σ + 1 ≤ maxCap from Nat.le_add_right _ _).trans (Nat.le_succ _))]
    have hfalse (raw : List Bool) (hr : maxCap < raw.length) :
        OracleComp.runWith oracle (micaliVerifyRawBounded V σ m x raw) s =
          if micaliHasRootPrefix σ raw = true then
            (oracle (.inr (x, unframe (raw.take (2 * σ + 1)))) s).bind
              (fun p => PMF.pure (false, p.2))
          else PMF.pure (false, s) := by
      unfold micaliVerifyRawBounded
      dsimp only
      by_cases hhas : micaliHasRootPrefix σ raw = true
      · simp only [hhas, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          OracleComp.runWith_bind, OracleComp.liftRight_query, OracleComp.runWith_query]
        refine PMF.bind_congr_on_support _ _ _ fun ⟨ρs, s₁⟩ _ => ?_
        dsimp only
        by_cases hch : (ρs.length == m && ρs.all fun ρ => ρ.length == V.coins x) = true
        · have hch' : ρs.length = m ∧ ∀ ρ ∈ ρs, ρ.length = V.coins x := by
            simpa [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] using hch
          have hcap := kilianRawProverCap_le_micaliMaxProofCap V (σ := σ) hch'.1 fun ρ hρ =>
            hq x ρ (hch'.2 ρ hρ)
          simp [hch, show raw.length > kilianRawProverCap V (List.replicate σ false) x ρs by omega]
        · simp [hch]
      · simp [show micaliHasRootPrefix σ raw = false from Bool.eq_false_iff.mpr hhas]
    have hhasEq : micaliHasRootPrefix σ (rawProof.take (maxCap + 1)) =
        micaliHasRootPrefix σ rawProof := by
      simp only [micaliHasRootPrefix, hpfxEq]
    rw [hfalse _ (by simp; omega), hfalse rawProof (Nat.lt_of_not_ge hle), hhasEq, hpfxEq]

end WordBisimulation

section WordOracleComplexity

variable {α : Type} {enc : α ↪ List Bool}

private theorem isOraclePPTOn_merkleWordStep :
    IsOraclePPTOn (encPair encUnary (encPair (encList encBits) (encPair encBits encUnary)))
      (encPair (encList encBits) (encPair encBits encUnary))
      (fun p : ℕ × (List (List Bool) × List Bool × ℕ) => merkleWordStep p.1 p.2) := by
  let stateEnc := encPair (encList encBits) (encPair encBits encUnary)
  let E_s := encPair encUnary stateEnc
  have hq : IsOraclePPTOn E_s encBits (fun p =>
      List.take p.1 <$> ProbOracleComp.query
        (spec := fun _ : MicaliWordOp × List Bool => List Bool)
        (MicaliWordOp.merkle, p.2.2.1)) :=
    IsOraclePPTOn.query_take MicaliWordOp.merkle (by fun_prop) (by fun_prop)
  let stepPost : (ℕ × (List (List Bool) × List Bool × ℕ)) → List Bool →
      List (List Bool) × List Bool × ℕ := fun p node =>
    let (rem, _, pos) := p.2
    let sib := rem.headD []
    let nextIn := if pos % 2 == 0 then encPair encBits encBits (node, sib)
      else encPair encBits encBits (sib, node)
    (rem.tail, nextIn, pos / 2)
  have hpost : ComputableInPolyTime (fun q => stepPost q.1 q.2)
      (encPair E_s encBits) stateEnc := by
    have hsib : ComputableInPolyTime
        (fun q : (ℕ × (List (List Bool) × List Bool × ℕ)) × List Bool => q.1.2.1.headD [])
        (encPair E_s encBits) encBits :=
      (ComputableInPolyTime.headD (encA := encBits) (encL := encList encBits) []).comp (by fun_prop)
    have hpair : ComputableInPolyTime (fun p : List Bool × List Bool => encPair encBits encBits p)
        (encPair encBits encBits) encBits :=
      ComputableInPolyTime.of_eq (encOut := encBits) fun _ => rfl
    exact ((ComputableInPolyTime.tail (encA := encBits) (encL := encList encBits)).comp
        (by fun_prop)).prod
      ((ComputableInPolyTime.ite
        (ComputableInPolyTime.beq
          (ComputableInPolyTime.unary_mod' (by fun_prop) (ComputableInPolyTime.const 2))
          (ComputableInPolyTime.const 0))
        (hpair.comp ((by fun_prop : ComputableInPolyTime _ _ encBits).prod hsib))
        (hpair.comp (hsib.prod (by fun_prop)))).prod
        (ComputableInPolyTime.unary_div' (by fun_prop) (ComputableInPolyTime.const 2)))
  have hfn :
      (fun p : ℕ × (List (List Bool) × List Bool × ℕ) => merkleWordStep p.1 p.2) =
      fun p => stepPost p <$> List.take p.1 <$> ProbOracleComp.query
        (spec := fun _ : MicaliWordOp × List Bool => List Bool)
        (MicaliWordOp.merkle, p.2.2.1) := by
    funext p
    simp only [merkleWordStep, stepPost, map_eq_pure_bind, beq_iff_eq]
  rw [hfn]
  exact hq.map_with hpost

private abbrev merkleWordEnc :
    (ℕ × ℕ × List Bool) × (ℕ × List Bool × List (List Bool)) ↪ List Bool :=
  encPair (encPair encUnary (encPair encUnary encBits))
    (encPair encUnary (encPair encBits (encList encBits)))

private abbrev merkleStateEnc : List (List Bool) × List Bool × ℕ ↪ List Bool :=
  encPair (encList encBits) (encPair encBits encUnary)

private def merkleWordLoopInv
    (p : ℕ × (List (List Bool) × List Bool × ℕ)) (j : ℕ)
    (st : List (List Bool) × List Bool × ℕ) : Prop :=
  st.1 = p.2.1.drop j ∧ st.2.2 ≤ p.2.2.2 ∧
    st.2.1.length ≤ p.2.2.1.length + 2 * p.1 + 2 * (encList encBits p.2.1).length + 1

private theorem merkleWordStep_preserve (p : ℕ × (List (List Bool) × List Bool × ℕ))
    (j : ℕ) (st : List (List Bool) × List Bool × ℕ) (_ : j < p.2.1.length)
    (hinv : merkleWordLoopInv p j st) (next : List (List Bool) × List Bool × ℕ)
    (hnext : next ∈ OracleComp.support (merkleWordStep p.1 st)) :
    merkleWordLoopInv p (j + 1) next := by
  unfold merkleWordStep at hnext
  obtain ⟨node, hnode, rfl⟩ := OracleComp.mem_supportWith_bind_iff.mp hnext
  obtain ⟨reply, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnode
  have hsib : (st.1.headD []).length ≤ (encList encBits p.2.1).length := by
    cases hrem : st.1 with
    | nil => simp
    | cons h t =>
      have hmem : h ∈ p.2.1 :=
        List.mem_of_mem_drop (i := j) (by rw [← hinv.1, hrem]; exact List.mem_cons_self)
      have hle := SizedListEncoding.length_elem_le (encA := encBits) (encL := encList encBits)
        p.2.1 h hmem
      simp only [encBits_apply] at hle
      rw [List.headD_cons]
      omega
  have htakeLen : (reply.take p.1).length ≤ p.1 := List.length_take_le _ _
  refine ⟨by rw [hinv.1, List.tail_drop, Nat.add_comm], (Nat.div_le_self _ _).trans hinv.2.1, ?_⟩
  dsimp only
  split_ifs <;>
  · simp only [length_encPair, encBits_apply]
    omega

private theorem merkleWordLoop_bound (p : ℕ × (List (List Bool) × List Bool × ℕ))
    (j : ℕ) (st : List (List Bool) × List Bool × ℕ) (_ : j ≤ p.2.1.length)
    (hinv : merkleWordLoopInv p j st) :
    (merkleStateEnc st).length ≤
      14 * ((encPair encUnary merkleStateEnc) p).length + 14 := by
  have hremLen : (encList encBits st.1).length ≤ (encList encBits p.2.1).length :=
    hinv.1 ▸ SizedListEncoding.length_drop_le (encA := encBits) (encL := encList encBits) p.2.1 j
  simp only [merkleStateEnc, length_encPair, encUnary_apply, encBits_apply, List.length_replicate]
  have := hinv.2.1
  have := hinv.2.2
  omega

private theorem isOraclePPTOn_merkleWordLoop :
    IsOraclePPTOn (encPair encUnary merkleStateEnc) merkleStateEnc
      (fun p : ℕ × (List (List Bool) × List Bool × ℕ) =>
        OracleComp.iterate p.2.1.length (merkleWordStep p.1) p.2) :=
  (IsOraclePPTOn.iterateWith_spec
    (input := encPair encUnary merkleStateEnc) (stateEncoding := merkleStateEnc)
    (step := fun p st => merkleWordStep p.1 st)
    ((ComputableInPolyTime.length_list encBits).comp (by fun_prop)) (by fun_prop)
    (isOraclePPTOn_merkleWordStep.preprocess
      (prepare := fun q : (ℕ × (List (List Bool) × List Bool × ℕ)) ×
          (List (List Bool) × List Bool × ℕ) => (q.1.1, q.2)) (by fun_prop))
    merkleWordLoopInv (fun _ => ⟨rfl, le_rfl, by simp [Nat.add_assoc]⟩) merkleWordStep_preserve
    (size := fun p => 14 * ((encPair encUnary merkleStateEnc) p).length + 14)
    (PolyBounded.of_forall_le 14 1 fun _ => by rw [Nat.pow_one]; omega)
    merkleWordLoop_bound).1

private theorem isOraclePPTOn_merkleWordCand :
    IsOraclePPTOn merkleWordEnc encBits
      (fun w => do
        let stp ← OracleComp.iterate w.2.2.2.length (merkleWordStep w.1.1)
          (w.2.2.2, w.2.2.1, w.2.1)
        List.take w.1.1 <$> ProbOracleComp.query
          (spec := fun _ : MicaliWordOp × List Bool => List Bool)
          (MicaliWordOp.merkle, stp.2.1)) :=
  (isOraclePPTOn_merkleWordLoop.preprocess
    (prepare := fun w : (ℕ × ℕ × List Bool) × (ℕ × List Bool × List (List Bool)) =>
      (w.1.1, (w.2.2.2, w.2.2.1, w.2.1))) (by fun_prop)).bind_with
    (IsOraclePPTOn.query_take MicaliWordOp.merkle
      (request := fun p : ((ℕ × ℕ × List Bool) × (ℕ × List Bool × List (List Bool))) ×
          (List (List Bool) × List Bool × ℕ) => p.2.2.1)
      (limit := fun p => p.1.1.1) (by fun_prop) (by fun_prop))

private def merkleWordPost
    (w : (ℕ × ℕ × List Bool) × (ℕ × List Bool × List (List Bool))) (cand : List Bool) : Bool :=
  w.2.2.2.length == w.1.2.1 &&
    decide (Nat.clog 2 (w.2.1 + 1) ≤ w.1.2.1) &&
    w.2.2.2.all (fun s => s.length == w.1.2.2.length) &&
    cand == w.1.2.2

private theorem computableInPolyTime_merkleWordPost :
    ComputableInPolyTime (fun p => merkleWordPost p.1 p.2)
      (encPair merkleWordEnc encBits) encBool :=
  ComputableInPolyTime.bool_and'
    (ComputableInPolyTime.bool_and'
      (ComputableInPolyTime.bool_and'
        (ComputableInPolyTime.beq ((ComputableInPolyTime.length_list encBits).comp (by fun_prop))
          (by fun_prop))
        (ComputableInPolyTime.unary_le.comp
          (((ComputableInPolyTime.unary_clog_const 2).comp
            (ComputableInPolyTime.unary_add' (by fun_prop) (ComputableInPolyTime.const 1))).prod
            (by fun_prop))))
      (ComputableInPolyTime.allWithInput (by fun_prop)
        (ComputableInPolyTime.beq (ComputableInPolyTime.length_bits.comp (by fun_prop))
          (ComputableInPolyTime.length_bits.comp (by fun_prop)))))
    (ComputableInPolyTime.beq (by fun_prop) (by fun_prop))

private theorem isOraclePPTOn_merkleVerifyWord :
    IsOraclePPTOn merkleWordEnc encBool
      (fun w : (ℕ × ℕ × List Bool) × (ℕ × List Bool × List (List Bool)) =>
        merkleVerifyWord w.1.1 w.1.2.1 w.1.2.2 w.2.1 w.2.2.1 w.2.2.2) := by
  have hdec (i d : ℕ) : decide (i < 2 ^ d) = decide (Nat.clog 2 (i + 1) ≤ d) :=
    decide_eq_decide.mpr (by rw [Nat.clog_le_iff_le_pow (by norm_num), Nat.succ_le_iff])
  have hfn :
      (fun w : (ℕ × ℕ × List Bool) × (ℕ × List Bool × List (List Bool)) =>
        merkleVerifyWord w.1.1 w.1.2.1 w.1.2.2 w.2.1 w.2.2.1 w.2.2.2) =
      fun w => merkleWordPost w <$> (do
        let stp ← OracleComp.iterate w.2.2.2.length (merkleWordStep w.1.1)
          (w.2.2.2, w.2.2.1, w.2.1)
        List.take w.1.1 <$> ProbOracleComp.query
          (spec := fun _ : MicaliWordOp × List Bool => List Bool)
          (MicaliWordOp.merkle, stp.2.1)) := by
    funext w
    simp only [merkleVerifyWord, merkleWordPost, bind_assoc, map_eq_pure_bind, pure_bind, hdec]
  rw [hfn]
  exact isOraclePPTOn_merkleWordCand.map_with computableInPolyTime_merkleWordPost

private theorem isOraclePPTOn_kilianCheckWord
    {V : PCPVerifier α} (hV : V.PolyTime enc) {c : ℕ}
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1)) :
    IsOraclePPTOn
      (encPair (encPair encUnary enc)
        (encPair encBits (encPair encBits (encList encKilianOpening))))
      encBool
      (fun p : (ℕ × α) × (List Bool × List Bool × List (MerkleOpening Bool)) =>
        kilianCheckWord V p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2) := by
  let E_c := encPair (encPair encUnary enc)
    (encPair encBits (encPair encBits (encList encKilianOpening)))
  have htable := PCPVerifier.isPolyTime_queryTable hV hcoins
  have hdepth := computableInPolyTime_kilianDepth (enc := enc) hV hcoins
  have hzip := ComputableInPolyTime.zip encNat encKilianOpening
  have hlist : ComputableInPolyTime
      (fun p : (ℕ × α) × (List Bool × List Bool × List (MerkleOpening Bool)) =>
        (V.queries (p.1.2, p.2.2.1)).zip p.2.2.2)
      E_c (encList (encPair encNat encKilianOpening)) :=
    hzip.comp ((hV.queries.comp (by fun_prop)).prod (by fun_prop))
  have hitem : IsOraclePPTOn (encPair E_c (encPair encNat encKilianOpening)) encBool
      (Function.uncurry fun p it =>
        merkleVerifyWord p.1.1 (kilianDepth V p.1.2) p.2.1
          (kilianPosition V p.1.2 it.1) [it.2.leaf] it.2.path) :=
    isOraclePPTOn_merkleVerifyWord.preprocess
      (prepare := fun p : ((ℕ × α) × (List Bool × List Bool × List (MerkleOpening Bool))) ×
          (ℕ × MerkleOpening Bool) =>
        ((p.1.1.1, kilianDepth V p.1.1.2, p.1.2.1),
          (kilianPosition V p.1.1.2 p.2.1, [p.2.2.leaf], p.2.2.path)))
      (((by fun_prop : ComputableInPolyTime _ _ encUnary).prod
        ((hdepth.comp (by fun_prop)).prod (by fun_prop))).prod
        ((ComputableInPolyTime.idxOfWithInput (htable.comp (by fun_prop)) (by fun_prop)).prod
          ((ComputableInPolyTime.bitsCons (encKilianOpening_leaf_polyTime (by fun_prop))
            (ComputableInPolyTime.const [])).prod
            (encKilianOpening_path_polyTime (by fun_prop)))))
  have hmap := IsOraclePPTOn.mapM_with_of_bounded_output (output := encBool) (0, Inhabited.default)
    hlist hitem (ComputableInPolyTime.const 1) (fun _ _ b _ => by simp [encBool_apply])
  let checkPost : ((ℕ × α) × (List Bool × List Bool × List (MerkleOpening Bool))) →
      List Bool → Bool := fun p checks =>
    p.2.2.2.length == (V.queries (p.1.2, p.2.2.1)).length &&
      checks.all id &&
      V.verdict ((p.1.2, p.2.2.1), p.2.2.2.map MerkleOpening.leaf)
  have hpost : ComputableInPolyTime (fun q => checkPost q.1 q.2)
      (encPair E_c (encList encBool)) encBool := by
    have hbits : ComputableInPolyTime
        (fun q : ((ℕ × α) × (List Bool × List Bool × List (MerkleOpening Bool))) × List Bool =>
          q.1.2.2.2.map MerkleOpening.leaf)
        (encPair E_c (encList encBool)) encBits :=
      ComputableInPolyTime.listToBits.comp
        (ComputableInPolyTime.mapWithInput (by fun_prop)
          (encKilianOpening_leaf_polyTime (by fun_prop)))
    exact ComputableInPolyTime.bool_and'
      (ComputableInPolyTime.bool_and'
        (ComputableInPolyTime.beq
          ((ComputableInPolyTime.length_list encKilianOpening).comp (by fun_prop))
          ((ComputableInPolyTime.length_list encNat).comp (hV.queries.comp (by fun_prop))))
        (ComputableInPolyTime.allWithInput (by fun_prop) (by fun_prop)))
      (hV.verdict.comp ((by fun_prop : ComputableInPolyTime _ _ (encPair enc encBits)).prod hbits))
  have hfn :
      (fun p : (ℕ × α) × (List Bool × List Bool × List (MerkleOpening Bool)) =>
        kilianCheckWord V p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2) =
      fun p => checkPost p <$>
        ((V.queries (p.1.2, p.2.2.1)).zip p.2.2.2).mapM fun it =>
          merkleVerifyWord p.1.1 (kilianDepth V p.1.2) p.2.1
            (kilianPosition V p.1.2 it.1) [it.2.leaf] it.2.path := by
    funext p
    simp only [kilianCheckWord, checkPost, map_eq_pure_bind]
  rw [hfn]
  exact hmap.map_with hpost

private theorem isOraclePPTOn_kilianVerifyWord
    {V : PCPVerifier α} (hV : V.PolyTime enc) {c : ℕ}
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1)) :
    IsOraclePPTOn
      (encPair (encPair encUnary enc)
        (encPair encBits (encPair (encList encBits) encKilianResponse)))
      encBool
      (fun p : (ℕ × α) × (List Bool × List (List Bool) × KilianResponse) =>
        kilianVerifyWord V p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2) := by
  let E_v := encPair (encPair encUnary enc)
    (encPair encBits (encPair (encList encBits) encKilianResponse))
  have hzip := ComputableInPolyTime.zip encBits (encList encKilianOpening)
  have hlist : ComputableInPolyTime
      (fun p : (ℕ × α) × (List Bool × List (List Bool) × KilianResponse) => p.2.2.1.zip p.2.2.2)
      E_v (encList (encPair encBits (encList encKilianOpening))) :=
    hzip.comp (by fun_prop)
  have hitem : IsOraclePPTOn (encPair E_v (encPair encBits (encList encKilianOpening))) encBool
      (Function.uncurry fun p it => kilianCheckWord V p.1.1 p.1.2 p.2.1 it.1 it.2) :=
    (isOraclePPTOn_kilianCheckWord hV hcoins).preprocess
      (prepare := fun p : ((ℕ × α) × (List Bool × List (List Bool) × KilianResponse)) ×
          (List Bool × List (MerkleOpening Bool)) =>
        ((p.1.1.1, p.1.1.2), (p.1.2.1, p.2.1, p.2.2))) (by fun_prop)
  have hmap := IsOraclePPTOn.mapM_with_of_bounded_output (output := encBool) ([], [])
    hlist hitem (ComputableInPolyTime.const 1) (fun _ _ b _ => by simp [encBool_apply])
  let verPost : ((ℕ × α) × (List Bool × List (List Bool) × KilianResponse)) →
      List Bool → Bool := fun p checks =>
    p.2.2.2.length == p.2.2.1.length && checks.all id
  have hpost : ComputableInPolyTime (fun q => verPost q.1 q.2)
      (encPair E_v (encList encBool)) encBool :=
    ComputableInPolyTime.bool_and'
      (ComputableInPolyTime.beq
        ((ComputableInPolyTime.length_list (encList encKilianOpening)).comp (by fun_prop))
        ((ComputableInPolyTime.length_list encBits).comp (by fun_prop)))
      (ComputableInPolyTime.allWithInput (by fun_prop) (by fun_prop))
  have hfn :
      (fun p : (ℕ × α) × (List Bool × List (List Bool) × KilianResponse) =>
        kilianVerifyWord V p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2) =
      fun p => verPost p <$>
        (p.2.2.1.zip p.2.2.2).mapM fun it => kilianCheckWord V p.1.1 p.1.2 p.2.1 it.1 it.2 := by
    funext p
    simp only [kilianVerifyWord, verPost, map_eq_pure_bind]
  rw [hfn]
  exact hmap.map_with hpost

private theorem computableInPolyTime_kilianStructValid
    {V : PCPVerifier α} (hV : V.PolyTime enc) {c : ℕ}
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1)) :
    ComputableInPolyTime
      (fun p : α × List Bool × List (List Bool) × KilianResponse =>
        kilianStructValid V p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair enc (encPair encBits (encPair (encList encBits) encKilianResponse))) encBool := by
  let E_s := encPair enc (encPair encBits (encPair (encList encBits) encKilianResponse))
  have hdepth := computableInPolyTime_kilianDepth (enc := enc) hV hcoins
  have hzip := ComputableInPolyTime.zip encBits (encList encKilianOpening)
  unfold kilianStructValid
  refine ComputableInPolyTime.bool_and'
    (ComputableInPolyTime.beq
      ((ComputableInPolyTime.length_list (encList encKilianOpening)).comp (by fun_prop))
      ((ComputableInPolyTime.length_list encBits).comp (by fun_prop)))
    (ComputableInPolyTime.allWithInput (hzip.comp (by fun_prop)) ?_)
  refine ComputableInPolyTime.bool_and'
    (ComputableInPolyTime.beq
      ((ComputableInPolyTime.length_list encKilianOpening).comp (by fun_prop))
      ((ComputableInPolyTime.length_list encNat).comp (hV.queries.comp (by fun_prop))))
    (ComputableInPolyTime.allWithInput (by fun_prop) ?_)
  exact ComputableInPolyTime.bool_and'
    (ComputableInPolyTime.beq
      ((ComputableInPolyTime.length_list encBits).comp
        (encKilianOpening_path_polyTime (by fun_prop)))
      (hdepth.comp (by fun_prop)))
    (ComputableInPolyTime.allWithInput (encKilianOpening_path_polyTime (by fun_prop))
      (ComputableInPolyTime.beq (ComputableInPolyTime.length_bits.comp (by fun_prop))
        (ComputableInPolyTime.length_bits.comp (by fun_prop))))

/-- `micaliVerifyRawWordCore` is strict oracle PPT in its full input `(inp, rawProof)`. -/
theorem isOraclePPTOn_micaliVerifyRawWordCore
    {V : PCPVerifier α} (hV : V.PolyTime enc) {c : ℕ}
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1)) :
    IsOraclePPTOn (encPair (encMicaliRawInput enc) encBits) encBool
      (micaliVerifyRawWordCore V enc c) := by
  let E_in := encPair (encMicaliRawInput enc) encBits
  have hinp := ComputableInPolyTime.fst (encMicaliRawInput enc) encBits
  have hraw := ComputableInPolyTime.snd (encMicaliRawInput enc) encBits
  have hσ := encMicaliRawInput_sigma_polyTime enc hinp
  have hm := encMicaliRawInput_reps_polyTime enc hinp
  have hx := encMicaliRawInput_stmt_polyTime enc hinp
  have hhas := computableInPolyTime_micaliHasRootPrefix.comp (hσ.prod hraw)
  have hcoinsU := computableInPolyTime_coins_unary hV hcoins
  have hroot : ComputableInPolyTime
      (fun p : MicaliRawInput α × List Bool => unframe (p.2.take (2 * p.1.sigma + 1)))
      E_in encBits :=
    ComputableInPolyTime.unframe.comp (ComputableInPolyTime.bitsTakeWithInput hraw
      (ComputableInPolyTime.unary_add'
        (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2) hσ)
        (ComputableInPolyTime.const 1)))
  have hfsCap : ComputableInPolyTime
      (fun p : MicaliRawInput α × List Bool => micaliFSReplyCap enc c p.1.reps p.1.stmt)
      E_in encUnary :=
    ComputableInPolyTime.unary_mul' hm
      (ComputableInPolyTime.unary_add'
        (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2)
          (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const c)
            (ComputableInPolyTime.unary_add'
              ((ComputableInPolyTime.unary_log_const 2).comp
                ((ComputableInPolyTime.encoding_length enc).comp hx))
              (ComputableInPolyTime.const 1))))
        (ComputableInPolyTime.const 1))
  have hreq : ComputableInPolyTime
      (fun p : MicaliRawInput α × List Bool =>
        encPair enc encBits (p.1.stmt, unframe (p.2.take (2 * p.1.sigma + 1))))
      E_in encBits :=
    (ComputableInPolyTime.of_eq (encIn := encPair enc encBits) (encOut := encBits)
      fun _ => rfl).comp (hx.prod hroot)
  have hq : IsOraclePPTOn E_in encBits
      (fun p => List.take (micaliFSReplyCap enc c p.1.reps p.1.stmt + 1) <$>
        ProbOracleComp.query (spec := fun _ : MicaliWordOp × List Bool => List Bool)
          (MicaliWordOp.fs,
            encPair enc encBits (p.1.stmt, unframe (p.2.take (2 * p.1.sigma + 1))))) :=
    IsOraclePPTOn.query_take MicaliWordOp.fs hreq
      (ComputableInPolyTime.unary_add' hfsCap (ComputableInPolyTime.const 1))
  let cont : MicaliRawInput α × List Bool → List Bool → WordOracleComp MicaliWordOp Bool :=
    fun p fsWord =>
      let inp := p.1
      let rawProof := p.2
      let root := unframe (rawProof.take (2 * inp.sigma + 1))
      if fsWord.length > micaliFSReplyCap enc c inp.reps inp.stmt then return false
      else
        let ρs := (Decoder.list Decoder.bits).decode fsWord
        if !(ρs.length == inp.reps && ρs.all fun ρ => ρ.length == V.coins inp.stmt) then
          return false
        else if rawProof.length >
            kilianRawProverCap V (List.replicate inp.sigma false) inp.stmt ρs then
          return false
        else
          let resp := (micaliProofDecoder.decode rawProof).response
          if !kilianStructValid V inp.stmt root ρs resp then return false
          else kilianVerifyWord V inp.sigma inp.stmt root ρs resp
  have hcont : IsOraclePPTOn (encPair E_in encBits) encBool
      (fun q => cont q.1 q.2) := by
    let E₂ := encPair E_in encBits
    have hq₁ := ComputableInPolyTime.fst E_in encBits
    have hfsW := ComputableInPolyTime.snd E_in encBits
    have hσ₂ := hσ.comp hq₁
    have hx₂ := hx.comp hq₁
    have hraw₂ := hraw.comp hq₁
    have hroot₂ := hroot.comp hq₁
    have hρs := (Decoder.list Decoder.bits).computableInPolyTime.comp hfsW
    have hresp := encMicaliProof_response_polyTime
      (micaliProofDecoder.computableInPolyTime.comp hraw₂)
    have hrawCap' := (computableInPolyTime_kilianRawProverCap hV hcoins).comp
      (encKilianChallengeInput_mk_polyTime enc
        ((ComputableInPolyTime.bitsReplicate false).comp hσ₂) hx₂ hρs)
    have hfalse : IsOraclePPTOn E₂ encBool
        (fun _ => (pure false : WordOracleComp MicaliWordOp Bool)) :=
      (ComputableInPolyTime.const false).isOraclePPTOn
    have hgtFs := ComputableInPolyTime.unary_lt.comp
      ((hfsCap.comp hq₁).prod (ComputableInPolyTime.length_bits.comp hfsW))
    have hbadCh := ComputableInPolyTime.bool_not.comp (ComputableInPolyTime.bool_and'
      (ComputableInPolyTime.beq ((ComputableInPolyTime.length_list encBits).comp hρs) (hm.comp hq₁))
      (ComputableInPolyTime.allWithInput
        (test := fun (q : (MicaliRawInput α × List Bool) × List Bool) (ρ : List Bool) =>
          ρ.length == V.coins q.1.1.stmt)
        hρs
        (ComputableInPolyTime.beq
          (ComputableInPolyTime.length_bits.comp (ComputableInPolyTime.snd E₂ encBits))
          (hcoinsU.comp (hx₂.comp (ComputableInPolyTime.fst E₂ encBits))))))
    have hgtRaw := ComputableInPolyTime.unary_lt.comp
      (hrawCap'.prod (ComputableInPolyTime.length_bits.comp hraw₂))
    have hbadSt := ComputableInPolyTime.bool_not.comp
      ((computableInPolyTime_kilianStructValid hV hcoins).comp
        (hx₂.prod (hroot₂.prod (hρs.prod hresp))))
    refine IsOraclePPTOn.ite hgtFs hfalse (IsOraclePPTOn.cond hbadCh hfalse
      (IsOraclePPTOn.ite hgtRaw hfalse (IsOraclePPTOn.cond hbadSt hfalse
        ((isOraclePPTOn_kilianVerifyWord hV hcoins).preprocess
          (prepare := fun q : (MicaliRawInput α × List Bool) × List Bool =>
            ((q.1.1.sigma, q.1.1.stmt),
              (unframe (q.1.2.take (2 * q.1.1.sigma + 1)),
                (Decoder.list Decoder.bits).decode q.2,
                (micaliProofDecoder.decode q.1.2).response)))
          ((hσ₂.prod hx₂).prod (hroot₂.prod (hρs.prod hresp)))))))
  refine IsOraclePPTOn.cond (ComputableInPolyTime.bool_not.comp hhas)
    (ComputableInPolyTime.const false).isOraclePPTOn ?_
  convert hq.bind_with hcont using 1

private theorem isQueryBounded_iterate_merkleWordStep (σ n : ℕ)
    (st : List (List Bool) × List Bool × ℕ) :
    ProbOracleComp.IsQueryBounded (OracleComp.iterate n (merkleWordStep σ) st) n := by
  induction n generalizing st with
  | zero => simpa using OracleComp.IsCostBounded.pure st 0
  | succ n ih =>
    rw [OracleComp.iterate_succ_bind]
    have h1 : ProbOracleComp.IsQueryBounded (merkleWordStep σ st) 1 :=
      ((OracleComp.isCostBounded_map_iff _ _ _).mpr (ProbOracleComp.IsQueryBounded.query _)).bind
        fun _ => OracleComp.IsCostBounded.pure _ 0
    simpa [Nat.add_comm] using h1.bind fun st₁ => ih st₁

private theorem isQueryBounded_merkleVerifyWord (σ depth : ℕ) (root : List Bool) (i : ℕ)
    (leaf : List Bool) (path : List (List Bool)) :
    ProbOracleComp.IsQueryBounded (merkleVerifyWord σ depth root i leaf path)
      (path.length + 1) := by
  unfold merkleVerifyWord
  simpa only [Nat.add_zero] using
    (isQueryBounded_iterate_merkleWordStep σ path.length (path, leaf, i)).bind
      fun (_, finalIn, _) =>
        ((OracleComp.isCostBounded_map_iff (List.take σ)
          (ProbOracleComp.query (spec := fun _ : MicaliWordOp × List Bool => List Bool)
            (MicaliWordOp.merkle, finalIn)) 1).mpr (ProbOracleComp.IsQueryBounded.query _)).bind
          fun _ => OracleComp.IsCostBounded.pure _ 0

private theorem isQueryBounded_kilianVerifyWord_of_structValid {V : PCPVerifier α} {σ d : ℕ}
    {x : α} {root : List Bool} {ρs : List (List Bool)} {resp : KilianResponse}
    (hq : ∀ ρ ∈ ρs, (V.queries (x, ρ)).length ≤ d)
    (hvalid : kilianStructValid V x root ρs resp = true) :
    ProbOracleComp.IsQueryBounded (kilianVerifyWord V σ x root ρs resp)
      (ρs.length * (d * (kilianDepth V x + 1))) := by
  simp only [kilianStructValid, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hvalid
  refine isCostBounded_mapM_zip_bind_pure (by rw [List.length_zip, hvalid.1, min_self])
    fun ⟨ρ, answers⟩ hmem => ?_
  obtain ⟨hlenA, hallO⟩ := hvalid.2 (ρ, answers) hmem
  refine isCostBounded_mapM_zip_bind_pure (by
      rw [List.length_zip, hlenA, min_self]
      exact hq ρ (List.of_mem_zip hmem).1)
    fun ⟨a, o⟩ ho => ?_
  simpa only [(hallO o (List.of_mem_zip ho).2).1] using
    isQueryBounded_merkleVerifyWord σ (kilianDepth V x) root (kilianPosition V x a) [o.leaf] o.path

/-- `micaliVerifyRawWord` and `micaliVerifyRawWordCore` issue at most
`1 + m * d * (kilianDepth V x + 1)` word-oracle queries on every raw input `rawProof`. -/
theorem isQueryBounded_micaliVerifyRawWordCore {V : PCPVerifier α} {enc : α ↪ List Bool}
    {c d : ℕ} (hq : ∀ x ρ, ρ.length = V.coins x → (V.queries (x, ρ)).length ≤ d)
    (inp : MicaliRawInput α) (rawProof : List Bool) :
    ProbOracleComp.IsQueryBounded (micaliVerifyRawWordCore V enc c (inp, rawProof))
      (1 + inp.reps * d * (kilianDepth V inp.stmt + 1)) := by
  unfold micaliVerifyRawWordCore
  dsimp only
  split_ifs
  · exact OracleComp.IsCostBounded.pure _ _
  · have hqfs : ProbOracleComp.IsQueryBounded
        (List.take (micaliFSReplyCap enc c inp.reps inp.stmt + 1) <$> ProbOracleComp.query
          (spec := fun _ : MicaliWordOp × List Bool => List Bool)
          (MicaliWordOp.fs, encPair enc encBits
            (inp.stmt, unframe (rawProof.take (2 * inp.sigma + 1))))) 1 :=
      (OracleComp.isCostBounded_map_iff _ _ _).mpr (ProbOracleComp.IsQueryBounded.query _)
    simpa only [Nat.mul_assoc] using
      hqfs.bind (m := inp.reps * (d * (kilianDepth V inp.stmt + 1))) fun fsWord => by
        split_ifs with _ h2 _ h4 <;> try exact OracleComp.IsCostBounded.pure _ _
        have hch : ((Decoder.list Decoder.bits).decode fsWord).length = inp.reps ∧
            ∀ ρ ∈ (Decoder.list Decoder.bits).decode fsWord, ρ.length = V.coins inp.stmt := by
          simpa [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] using h2
        have hkv := isQueryBounded_kilianVerifyWord_of_structValid (σ := inp.sigma)
          (fun ρ hρ => hq inp.stmt ρ (hch.2 ρ hρ)) (by simpa using h4)
        rwa [hch.1] at hkv

theorem isQueryBounded_micaliVerifyRawWord {V : PCPVerifier α} {enc : α ↪ List Bool}
    {c d : ℕ} (hq : ∀ x ρ, ρ.length = V.coins x → (V.queries (x, ρ)).length ≤ d)
    (inp : MicaliRawInput α) (rawProof : List Bool) :
    ProbOracleComp.IsQueryBounded (micaliVerifyRawWord V enc c d (inp, rawProof))
      (1 + inp.reps * d * (kilianDepth V inp.stmt + 1)) :=
  isQueryBounded_micaliVerifyRawWordCore hq inp _

/-- **Uniform worst-case native ROM verifier halting time and query complexity**: there is one
fixed halting oracle machine `MultiTapePTM` computing `micaliVerifyRawWord` (hence matching
`micaliVerifyRawBounded` under `(micaliWordCodec enc).wordOracle` on every stateful handler) whose
halting step count is bounded polynomially in `inp.sigma + inp.reps + |enc inp.stmt|` uniformly over
**all** `(inp, rawProof)` and **all** stateful word handlers (independent of `rawProof.length`),
and whose query count is at most `1 + inp.reps * d * (kilianDepth V inp.stmt + 1)`. -/
theorem computesOracleInTimeAndQueriesOn_micaliVerifyRawWord
    {V : PCPVerifier α} (hV : V.PolyTime enc) {c d : ℕ}
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1))
    (hq : ∀ x ρ, ρ.length = V.coins x → (V.queries (x, ρ)).length ≤ d) :
    ∃ tBound : ℕ → ℕ, PolynomiallyBounded tBound ∧
      ComputesOracleInTimeAndQueriesOn (encPair (encMicaliRawInput enc) encBits) encBool
        (fun p => tBound (p.1.sigma + p.1.reps + (enc p.1.stmt).length))
        (fun p => 1 + p.1.reps * d * (kilianDepth V p.1.stmt + 1))
        (micaliVerifyRawWord V enc c d) := by
  let E_in := encPair (encMicaliRawInput enc) encBits
  obtain ⟨tp₀, htp₀_pb, hcore⟩ :=
    isOraclePPTOn_iff_exists_polyBounded_computesOracleInTimeOn.mp
      (isOraclePPTOn_micaliVerifyRawWordCore hV hcoins)
  obtain ⟨c₀, d₀, htp₀_le⟩ := htp₀_pb.exists_le
  have hcap := computableInPolyTime_micaliMaxProofCap (enc := enc) hV (d := d) hcoins
  obtain ⟨c₁, d₁, hcap_le⟩ := hcap.polyBounded_length.exists_le
  let prepare : MicaliRawInput α × List Bool → MicaliRawInput α × List Bool :=
    fun p => (p.1, p.2.take (micaliMaxProofCap V p.1.sigma p.1.reps d p.1.stmt + 1))
  have hprep_poly : ComputableInPolyTime prepare E_in E_in :=
    (ComputableInPolyTime.fst (encMicaliRawInput enc) encBits).prod
      (ComputableInPolyTime.bitsTakeWithInput
        (ComputableInPolyTime.snd (encMicaliRawInput enc) encBits)
        (ComputableInPolyTime.unary_add'
          (hcap.comp (ComputableInPolyTime.fst (encMicaliRawInput enc) encBits))
          (ComputableInPolyTime.const 1)))
  have hprep_take : ∀ (inp : MicaliRawInput α) (rawProof : List Bool),
      prepare (inp, rawProof) =
        prepare (inp, rawProof.take (micaliMaxProofCap V inp.sigma inp.reps d inp.stmt + 1)) := by
    intro inp rawProof
    simp [prepare, List.take_take]
  obtain ⟨k, State, hfin, tm, tf, sf, htf_pb, _, hprepare⟩ :=
    computableInTimeAndSpace_boundedPrefix hcap hprep_poly hprep_take
  obtain ⟨ctf, dtf, htf_le⟩ := polynomiallyBounded_iff_le.mp htf_pb
  have hcomp := hcore.preprocess ⟨k, State, hfin, tm, hprepare⟩
  let tBound : ℕ → ℕ := fun u =>
    2 * (ctf * (4 * u + 4 + 1) ^ dtf) +
      c₀ * (2 * (4 * u + 4) + 1 + (c₁ * (4 * u + 4 + 1) ^ d₁ + 1) + 1) ^ d₀ + 4
  have ht_pb : PolynomiallyBounded tBound := by
    dsimp only [tBound]
    fun_prop
  refine ⟨tBound, ht_pb, hcomp.mono ?_, fun p => isQueryBounded_micaliVerifyRawWord hq p.1 p.2⟩
  rintro ⟨inp, rawProof⟩
  set u := inp.sigma + inp.reps + (enc inp.stmt).length
  have hhdr : (encMicaliRawInput enc inp).length ≤ 4 * u + 4 := by
    simp only [encMicaliRawInput_apply, encPair_apply, encUnary_apply, length_frame,
      List.length_append, List.length_replicate, u]
    omega
  have htf_bound : tf (encMicaliRawInput enc inp).length ≤ ctf * (4 * u + 4 + 1) ^ dtf :=
    (htf_le _).trans (Nat.mul_le_mul_left ctf (Nat.pow_le_pow_left (by omega) dtf))
  have hcap_u : micaliMaxProofCap V inp.sigma inp.reps d inp.stmt ≤ c₁ * (4 * u + 4 + 1) ^ d₁ := by
    have hc := hcap_le inp
    simp only [encUnary_apply, List.length_replicate] at hc
    exact hc.trans (Nat.mul_le_mul_left c₁ (Nat.pow_le_pow_left (by omega) d₁))
  have hprep_len : (E_in (prepare (inp, rawProof))).length + 1 ≤
      2 * (4 * u + 4) + 1 + (c₁ * (4 * u + 4 + 1) ^ d₁ + 1) + 1 := by
    have htakeLen :
        (rawProof.take (micaliMaxProofCap V inp.sigma inp.reps d inp.stmt + 1)).length ≤
          micaliMaxProofCap V inp.sigma inp.reps d inp.stmt + 1 :=
      List.length_take_le _ _
    simp only [E_in, prepare, length_encPair, encBits_apply]
    omega
  have htp_bound :
      tp₀ (prepare (inp, rawProof)) ≤
        c₀ * (2 * (4 * u + 4) + 1 + (c₁ * (4 * u + 4 + 1) ^ d₁ + 1) + 1) ^ d₀ :=
    (htp₀_le _).trans (Nat.mul_le_mul_left c₀ (Nat.pow_le_pow_left hprep_len d₀))
  dsimp only [tBound]
  omega

end WordOracleComplexity

section RawSoundness

variable {α : Type}

/-- Honest Micali ROM experiment evaluating the raw bounded-prefix verifier
`micaliVerifyRawBounded` on the framed encoding `encMicaliProof proof` produced by `micaliProve`. -/
noncomputable def micaliHonestRawGame [DecidableEq α] (V : PCPVerifier α) (x : α)
    (table : List Bool) (σ m : ℕ) : PMF Bool :=
  (OracleComp.runWith (RandomOracle.answer (micaliOracleDist V σ m)) (do
    let proof ← micaliProve V x table
    micaliVerifyRawBounded V σ m x (encMicaliProof proof)) (fun _ => none)).map Prod.fst

/-- **Perfect raw completeness of Micali's construction in the random oracle model**: if
`V.tableVerifier (x, table) = true`, then for every digest width `σ` and repetition count `m`,
the honest raw bounded verifier `micaliVerifyRawBounded` accepts `encMicaliProof proof` with
probability `1`. -/
theorem micaliHonestRawGame_eq_pure_true [DecidableEq α] (V : PCPVerifier α) {x : α}
    {table : List Bool} (htable : V.tableVerifier (x, table) = true) (σ m : ℕ) :
    micaliHonestRawGame V x table σ m = PMF.pure true := by
  unfold micaliHonestRawGame
  refine OracleComp.map_fst_runWith_answer_eq_pure (micaliOracleDist V σ m) _ true fun h hh => ?_
  have hsplit : h = micaliOracle (fun msg => h (.inl msg)) (fun xrt => h (.inr xrt)) := by
    ext q
    cases q <;> rfl
  rw [hsplit]
  have hlen : ∀ y, (h (.inl y)).length = σ := fun y =>
    BitString.length_of_mem_support_uniformList (hh (.inl y))
  have hmem := hh (.inr (x, kilianCommit (fun _ => fun msg => h (.inl msg)) V [] x table))
  simp only [micaliOracleDist, kilianChallenges, ProbComp.mem_support_replicate_iff] at hmem
  have hm : (h (.inr (x, kilianCommit (fun _ => fun msg => h (.inl msg)) V [] x table))).length =
      m := hmem.1
  have hρs : ∀ ρ ∈ h (.inr (x, kilianCommit (fun _ => fun msg => h (.inl msg)) V [] x table)),
      ρ.length = V.coins x := fun ρ hρ =>
    BitString.length_of_mem_support_uniformList (by simpa using hmem.2 ρ hρ)
  simp only [OracleComp.evalPure_bind, evalPure_micaliProve, evalPure_micaliVerifyRawBounded]
  exact micaliVerifyRawBoundedPure_micaliProvePure_eq_true hlen htable hm hρs

open Classical in
/-- Native raw-byte Micali soundness program: runs a raw cheating prover
`P : OracleComp (MicaliSpec α) (α × List Bool)` returning `(x, rawProof)`, checks
`micaliVerifyRawBounded V σ m x rawProof`, and returns `true` when `x ∉ L` and the verifier
accepts. -/
noncomputable def micaliRawSoundnessProg (V : PCPVerifier α) (L : Set α) (σ m : ℕ)
    (P : OracleComp (MicaliSpec α) (α × List Bool)) : OracleComp (MicaliSpec α) Bool := do
  let (x, rawProof) ← P
  let ok ← micaliVerifyRawBounded V σ m x rawProof
  return decide (x ∉ L) && ok

/-- Native raw-byte Micali ROM soundness experiment against the shared lazy random oracle
`RandomOracle.answer (micaliOracleDist V σ m)` starting from an empty cache. -/
noncomputable def micaliRawSoundnessGame [DecidableEq α] (V : PCPVerifier α) (L : Set α)
    (P : OracleComp (MicaliSpec α) (α × List Bool)) (σ m : ℕ) : PMF Bool :=
  (OracleComp.runWith (RandomOracle.answer (micaliOracleDist V σ m))
    (micaliRawSoundnessProg V L σ m P) (fun _ => none)).map Prod.fst

private noncomputable def sanitizeRaw (V : PCPVerifier α) (σ m d : ℕ)
    (x : α) (rawProof : List Bool) : MicaliProof :=
  let prf := micaliProofDecoder.decode rawProof
  if micaliHasRootPrefix σ rawProof = true ∧
      rawProof.length ≤ micaliMaxProofCap V σ m d x ∧
      prf.response.length = m ∧
      ∀ ans ∈ prf.response, ans.length ≤ d ∧ ∀ o ∈ ans, o.path.length = kilianDepth V x then
    prf
  else
    ⟨unframe (rawProof.take (2 * σ + 1)), []⟩

private theorem isCostBounded_micaliMTCost_micaliVerify_sanitizeRaw (V : PCPVerifier α)
    (σ m d : ℕ) (x : α) (rawProof : List Bool) :
    OracleComp.IsCostBounded micaliMTCost
      (micaliVerify V x (sanitizeRaw V σ m d x rawProof))
      (m * d * (kilianDepth V x + 1)) := by
  classical
  set san := sanitizeRaw V σ m d x rawProof
  unfold micaliVerify
  have hq : OracleComp.IsCostBounded micaliMTCost
      (OracleComp.liftRight (spec₁ := MerkleHashSpec)
        (OracleComp.query (spec := MicaliFSSpec α) (x, san.root))) 0 :=
    OracleComp.IsCostBounded.query (spec := MicaliSpec α) (cost := micaliMTCost)
      (.inr (x, san.root))
  simpa only [Nat.zero_add] using hq.bind (m := m * d * (kilianDepth V x + 1)) fun ρs => by
      by_cases hsan : micaliHasRootPrefix σ rawProof = true ∧
          rawProof.length ≤ micaliMaxProofCap V σ m d x ∧
          (micaliProofDecoder.decode rawProof).response.length = m ∧
          ∀ ans ∈ (micaliProofDecoder.decode rawProof).response,
            ans.length ≤ d ∧ ∀ o ∈ ans, o.path.length = kilianDepth V x
      · have hsanEq : san = micaliProofDecoder.decode rawProof := by
          dsimp only [san, sanitizeRaw]
          split_ifs
          rfl
        rw [hsanEq]
        have hkv : OracleComp.IsQueryBounded
            (kilianVerifyProg V x (micaliProofDecoder.decode rawProof).root ρs
              (micaliProofDecoder.decode rawProof).response)
            (m * (d * (kilianDepth V x + 1))) :=
          isCostBounded_mapM_zip_bind_pure (by
              rw [List.length_zip, hsan.2.2.1]
              exact Nat.min_le_right _ _)
            fun ⟨ρ, answers⟩ hmem => by
              have hansProps := hsan.2.2.2 answers (List.of_mem_zip hmem).2
              refine isCostBounded_mapM_zip_bind_pure
                ((List.length_zip ▸ Nat.min_le_right _ _).trans hansProps.1)
                fun ⟨a, o⟩ ho => ?_
              simpa only [hansProps.2 o (List.of_mem_zip ho).2] using
                isQueryBounded_merkleVerifyProg (kilianDepth V x)
                  (micaliProofDecoder.decode rawProof).root (kilianPosition V x a)
                  [o.leaf] o.path
        exact (Nat.mul_assoc m d _ ▸ hkv).liftLeft fun _ => le_rfl
      · have hsanEq : san = ⟨unframe (rawProof.take (2 * σ + 1)), []⟩ := by
          dsimp only [san, sanitizeRaw]
          split_ifs
          rfl
        rw [hsanEq]
        have hkv : OracleComp.IsQueryBounded
            (kilianVerifyProg V x (unframe (rawProof.take (2 * σ + 1))) ρs []) 0 := by
          simp only [kilianVerifyProg, List.zip_nil_right, List.mapM_nil, pure_bind]
          exact OracleComp.IsCostBounded.pure _ 0
        exact (hkv.mono (Nat.zero_le _)).liftLeft fun _ => le_rfl

private theorem map_fst_runWith_micaliVerifyRawBounded_le {State : Type}
    (oracle : (q : List Bool ⊕ (α × List Bool)) → StateT State PMF (MicaliSpec α q))
    (V : PCPVerifier α) {σ m d : ℕ}
    (hq : ∀ x ρ, ρ.length = V.coins x → (V.queries (x, ρ)).length ≤ d)
    (x : α) (rawProof : List Bool) (s : State) :
    (OracleComp.runWith oracle (micaliVerifyRawBounded V σ m x rawProof) s).map Prod.fst true ≤
      (OracleComp.runWith oracle
        (micaliVerify V x (sanitizeRaw V σ m d x rawProof)) s).map Prod.fst true := by
  classical
  by_cases hsan : micaliHasRootPrefix σ rawProof = true ∧
      rawProof.length ≤ micaliMaxProofCap V σ m d x ∧
      (micaliProofDecoder.decode rawProof).response.length = m ∧
      ∀ ans ∈ (micaliProofDecoder.decode rawProof).response,
        ans.length ≤ d ∧ ∀ o ∈ ans, o.path.length = kilianDepth V x
  · have hsanEq : sanitizeRaw V σ m d x rawProof = micaliProofDecoder.decode rawProof := by
      dsimp only [sanitizeRaw]
      split_ifs
      rfl
    have hroot : (micaliProofDecoder.decode rawProof).root =
        unframe (rawProof.take (2 * σ + 1)) := by
      simpa [micaliProofDecoder, Decoder.map, kilianProverMsgDecoder, Decoder.pair, Decoder.bits]
        using (unframe_take_of_micaliHasRootPrefix hsan.1).2.2
    rw [hsanEq, micaliVerifyRawBounded, micaliVerify, hroot]
    simp only [hsan.1, Bool.not_true, Bool.false_eq_true, ↓reduceIte, OracleComp.runWith_bind,
      OracleComp.liftRight_query, OracleComp.runWith_query, PMF.map_bind, PMF.bind_apply]
    refine tsum_le_tsum fun ⟨ρs, s₁⟩ => mul_le_mul_right ?_ _
    split_ifs <;> simp
  · have hzero : ∀ s', (true, s') ∉
        (OracleComp.runWith oracle (micaliVerifyRawBounded V σ m x rawProof) s).support := by
      intro s' hmem
      apply hsan
      unfold micaliVerifyRawBounded at hmem
      split_ifs at hmem with hhas
      · simp at hmem
      · have hhas' : micaliHasRootPrefix σ rawProof = true := by simpa using hhas
        simp only [OracleComp.runWith_bind, OracleComp.liftRight_query, OracleComp.runWith_query,
          PMF.mem_support_bind_iff] at hmem
        obtain ⟨⟨ρs, s₁⟩, _, hrest⟩ := hmem
        dsimp only at hrest
        split_ifs at hrest with hch hgt hst
        · simp at hrest
        · simp at hrest
        · simp at hrest
        · have hch' : ρs.length = m ∧ ∀ ρ ∈ ρs, ρ.length = V.coins x := by
            simpa [Bool.not_eq_true, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] using hch
          have hcap := kilianRawProverCap_le_micaliMaxProofCap V (σ := σ) hch'.1 fun ρ hρ =>
            hq x ρ (hch'.2 ρ hρ)
          have hst' : kilianStructValid V x (unframe (rawProof.take (2 * σ + 1))) ρs
              (micaliProofDecoder.decode rawProof).response = true := by
            simpa using hst
          simp only [kilianStructValid, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hst'
          refine ⟨hhas', by omega, hst'.1.trans hch'.1, fun ans hans => ?_⟩
          obtain ⟨ρ, hρ, hmemZip⟩ := mem_zip_of_mem_right hst'.1 hans
          have hpair := hst'.2 _ hmemZip
          exact ⟨hpair.1 ▸ hq x ρ (hch'.2 ρ hρ), fun o ho => (hpair.2 o ho).1⟩
    have hL : (OracleComp.runWith oracle
        (micaliVerifyRawBounded V σ m x rawProof) s).map Prod.fst true = 0 := by
      rw [PMF.map_apply, tsum_eq_zero_iff]
      rintro ⟨b, s'⟩
      split_ifs with hb
      · subst hb
        exact by_contra (hzero s')
      · rfl
    rw [hL]
    exact bot_le

/-- **Adaptive two-channel ROM soundness for bounded-prefix raw Micali proofs**: for any PCP
verifier `V` with per-repetition soundness error `≤ 1 / 2` outside `L` and query complexity `≤ d`,
and any raw-byte cheating prover `P : OracleComp (MicaliSpec α) (α × List Bool)` making at most
`t_MT` Merkle hash queries and `t_FS` Fiat–Shamir queries such that every candidate output statement
satisfies `m * d * (kilianDepth V x + 1) ≤ q_V`, `micaliRawSoundnessGame` accepts a false
statement with probability at most
`(t_FS + 1) * (1 / 2) ^ m + (t_MT + q_V) * ((3 * (t_MT + q_V) + (t_FS + 1)) * (1 / 2 ^ σ))`. -/
theorem micaliRawSoundness_bound [DecidableEq α] (V : PCPVerifier α) (L : Set α) (σ m d : ℕ)
    (hsound : ∀ x ∉ L, ∀ π : List Bool,
      2 * acceptCount (fun y => V.accepts y.1 π y.2) x (V.coins x) ≤ 2 ^ V.coins x)
    (hq : ∀ x ρ, ρ.length = V.coins x → (V.queries (x, ρ)).length ≤ d)
    {P : OracleComp (MicaliSpec α) (α × List Bool)} {t_MT t_FS q_V : ℕ}
    (hMT : OracleComp.IsCostBounded micaliMTCost P t_MT)
    (hFS : OracleComp.IsCostBounded micaliFSCost P t_FS)
    (hdepth : ∀ x rawProof, (x, rawProof) ∈ P.support →
      m * d * (kilianDepth V x + 1) ≤ q_V) :
    micaliRawSoundnessGame V L P σ m true ≤
      ((t_FS + 1 : ℕ) : ℝ≥0∞) * (1 / 2) ^ m +
        ((t_MT + q_V : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + q_V) + (t_FS + 1) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) := by
  let P' : OracleComp (MicaliSpec α) (α × MicaliProof) := do
    let (x, rawProof) ← P
    return (x, sanitizeRaw V σ m d x rawProof)
  have hMT' : OracleComp.IsCostBounded micaliMTCost P' t_MT :=
    hMT.bind fun _ => OracleComp.IsCostBounded.pure _ 0
  have hFS' : OracleComp.IsCostBounded micaliFSCost P' t_FS :=
    hFS.bind fun _ => OracleComp.IsCostBounded.pure _ 0
  have hV' : ∀ x proof, (x, proof) ∈ P'.support →
      OracleComp.IsCostBounded micaliMTCost (micaliVerify V x proof) q_V := by
    intro x proof hmem
    obtain ⟨⟨x₀, rawProof⟩, hmemP, hEq⟩ := OracleComp.mem_supportWith_bind_iff.mp hmem
    have hEq' := OracleComp.eq_of_mem_supportWith_pure hEq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq'
    exact (isCostBounded_micaliMTCost_micaliVerify_sanitizeRaw V σ m d x rawProof).mono
      (hdepth x rawProof hmemP)
  have hbound := micaliSoundness_bound_of_prover_verifier V L σ m hsound hMT' hFS' hV'
  refine le_trans ?_ hbound
  unfold micaliRawSoundnessGame micaliSoundnessGame
  set oracle := RandomOracle.answer (micaliOracleDist V σ m)
  unfold micaliRawSoundnessProg micaliSoundnessProg P'
  simp only [OracleComp.runWith_bind, OracleComp.runWith_pure, PMF.bind_bind, PMF.pure_bind,
    PMF.map_bind]
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_le_tsum fun ⟨⟨x, rawProof⟩, s₁⟩ => ?_
  refine mul_le_mul_right ?_ _
  simp only [PMF.pure_map]
  by_cases hxL : x ∈ L
  · simp [hxL]
  · simp only [hxL, not_false_eq_true, decide_true, Bool.true_and]
    simpa [PMF.map_apply] using
      map_fst_runWith_micaliVerifyRawBounded_le oracle V hq x rawProof s₁

/-- **Native raw-byte Micali CS Proofs for arbitrary NP relations** (compare [Micali2000];
[ChiesaYogev2024], Construction 21.1.1 and Theorem 21.2.1; `locator not re-verified against primary
PDF`): every NP relation `R : NPRelation enc` admits a PCP verifier `V` (`≤ c * (log₂ |enc x| + 1)`
random coins, `≤ d` queries) and a polynomial-time witness compiler
`compile : α × List Bool → List Bool` such that:
1. `compile` compiles every `R`-witness into a compact table accepted by `V.tableVerifier`, and the
   raw bounded verifier `micaliVerifyRawBounded` accepts honest framed proofs with probability `1`
   (`micaliHonestRawGame_eq_pure_true`),
2. there is one fixed halting oracle machine (`MultiTapePTM`) implementing `micaliVerifyRawWord`
   whose worst-case runtime is bounded by a single polynomial `tWordBound (σ + m + |enc x|)`
   uniformly over **all** arbitrary unbounded `rawProof : List Bool` and **all** stateful word
   handlers, using at most `1 + m * d * (kilianDepth V x + 1)` queries,
3. `micaliRawSoundnessGame` satisfies the `micaliRawSoundness_bound` inequality against arbitrary
   adaptive two-channel raw cheating provers, and
4. honest proof payload bits `micaliProofBits (micaliProvePure hTree hFS V x table)` fit within
   `C * (σ + m + 1)^2 * (Nat.log 2 |enc x| + 1)`.

As immediate corollaries of applying `runWith_wordOracle_micaliVerifyRawWord` and
`computableInTimeAndSpace_micaliVerifyRawBoundedPure_of_params` to the returned `V`, `coins_le`,
and `queries_le`, `micaliVerifyRawWord` bisimulates `micaliVerifyRawBounded` on every stateful
handler via `(micaliWordCodec enc).wordOracle`, and any fixed digest-width polynomial-time `hTree`
and `hFS` yield one fixed halting binary `MultiTapeTM` for `micaliVerifyRawBoundedPure` running in
time and space polynomial in `m + |enc x|` for **all** `rawProof : List Bool`. -/
theorem exists_micaliRawCSProof_of_npRelation [DecidableEq α] {enc : α ↪ List Bool}
    (R : NPRelation enc) :
    ∃ (V : PCPVerifier α) (compile : α × List Bool → List Bool) (c d : ℕ)
      (tWordBound : ℕ → ℕ),
      V.PolyTime enc ∧
      (∀ x, V.coins x ≤ c * (Nat.log 2 (enc x).length + 1)) ∧
      (∀ x ρ, ρ.length = V.coins x → (V.queries (x, ρ)).length ≤ d) ∧
      ComputableInPolyTime compile (encPair enc encBits) encBits ∧
      (∀ x, x ∈ R.language ↔ ∃ table, V.tableVerifier (x, table) = true) ∧
      (∀ x w, R.IsWitness x w → V.tableVerifier (x, compile (x, w)) = true) ∧
      (∀ x w, R.IsWitness x w →
        ∀ σ m, micaliHonestRawGame V x (compile (x, w)) σ m = PMF.pure true) ∧
      PolynomiallyBounded tWordBound ∧
      ComputesOracleInTimeAndQueriesOn (encPair (encMicaliRawInput enc) encBits) encBool
        (fun p => tWordBound (p.1.sigma + p.1.reps + (enc p.1.stmt).length))
        (fun p => 1 + p.1.reps * d * (kilianDepth V p.1.stmt + 1))
        (micaliVerifyRawWord V enc c d) ∧
      (∀ (P : OracleComp (MicaliSpec α) (α × List Bool)) (t_MT t_FS q_V σ m : ℕ),
        OracleComp.IsCostBounded micaliMTCost P t_MT →
        OracleComp.IsCostBounded micaliFSCost P t_FS →
        (∀ x rawProof, (x, rawProof) ∈ P.support → m * d * (kilianDepth V x + 1) ≤ q_V) →
        micaliRawSoundnessGame V R.language P σ m true ≤
          ((t_FS + 1 : ℕ) : ℝ≥0∞) * (1 / 2) ^ m +
            ((t_MT + q_V : ℕ) : ℝ≥0∞) *
              (((3 * (t_MT + q_V) + (t_FS + 1) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ))) ∧
      ∃ C : ℕ, ∀ (σ m : ℕ) (hTree : List Bool → List Bool)
        (hFS : α × List Bool → List (List Bool)) (x : α) (table : List Bool),
        (∀ y, (hTree y).length = σ) →
        (hFS (x, kilianCommit (fun _ => hTree) V [] x table)).length = m →
        (∀ ρ ∈ hFS (x, kilianCommit (fun _ => hTree) V [] x table), ρ.length = V.coins x) →
          micaliProofBits (micaliProvePure hTree hFS V x table) ≤
            C * (σ + m + 1) ^ 2 * (Nat.log 2 (enc x).length + 1) := by
  obtain ⟨V, compile, c, d, hV, hpcp, hcompile, hacc⟩ := exists_pcpVerifier_of_npRelation enc R
  have hq : ∀ x ρ, ρ.length = V.coins x → (V.queries (x, ρ)).length ≤ d := by
    intro x ρ hρ
    simpa using hpcp.length_queries_le x ρ hρ
  obtain ⟨tWordBound, ht_pb, hword⟩ :=
    computesOracleInTimeAndQueriesOn_micaliVerifyRawWord hV hpcp.coins_le hq
  exact ⟨V, compile, c, d, tWordBound, hV, hpcp.coins_le, hq, hcompile,
    hpcp.mem_iff_exists_tableVerifier, hacc,
    fun x w hw σ m => micaliHonestRawGame_eq_pure_true V (hacc x w hw) σ m,
    ht_pb, hword,
    fun P t_MT t_FS q_V σ m hMT hFS hdepth =>
      micaliRawSoundness_bound V R.language σ m d hpcp.sound hq hMT hFS hdepth,
    _, fun σ m hTree hFS x table hlen hm hρs =>
      micaliProofBits_micaliProvePure_le_log hlen hm hρs (fun ρ hρ => hq x ρ hρ)
        (hpcp.coins_le x)⟩

end RawSoundness

end WordOracleVerifier

end Cslib.Crypto
