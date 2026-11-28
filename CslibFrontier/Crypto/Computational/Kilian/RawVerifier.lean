/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Kilian.Soundness
public import CslibFrontier.Crypto.Computational.Kilian.Succinct
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.BoundedPrefix
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Lists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Tactic.PolyTime

/-!
# Worst-case bounded-prefix raw verifier and raw prover soundness for Kilian's protocol

`kilianVerify` takes an already-decoded `KilianView α` and charges polynomial time in the full
length of the received view (`computableInPolyTime_kilianVerify`). Against an arbitrary unframed or
oversized cheating prover message, the encoded view itself could be arbitrarily long before
verification starts.

This module isolates the verifier's own inputs from the prover's untrusted raw transcript bits:

* **Challenge input vs. raw prover tape (`KilianChallengeInput`, `kilianVerifyRawBounded`):**
  The verifier's machine reads `(ch, rawProver)` under `encPair (encKilianChallengeInput enc)
  encBits`, where `ch = { key, stmt, challenges }` holds only the verifier-generated hash key,
  statement, and PCP challenge strings, while `rawProver : List Bool` holds the untrusted bytes
  supplied by the prover (`root` and `response` via `encPair encBits encKilianResponse`).
* **Deterministic length cap (`kilianRawProverCap`):**
  Any accepting transcript `(root, resp)` with `root.length ≤ ch.key.length` (in particular every
  honest transcript when `∀ k y, (H k y).length = k.length`) satisfies
  `(encPair encBits encKilianResponse (root, resp)).length ≤ kilianRawProverCap V ch.key ch.stmt
  ch.challenges` (`length_encKilianProverMsg_le_cap_of_kilianVerify`).
* **Single machine with worst-case `(n + |enc x|)^O(1)` complexity on all unbounded provers:**
  Composing `computableInPolyTime_kilianVerifyRawBounded` with
  `Turing.MultiTapeTM.computableInTimeAndSpace_boundedPrefix` yields one fixed binary
  `MultiTapeTM` computing `kilianVerifyRawBounded` that reads at most `cap + 1` bits of `rawProver`
  and runs in worst-case time and space polynomially bounded in `n + |enc ch.stmt|` for
  **every** `rawProver : List Bool`, regardless of length or framing validity
  (`computableInTimeAndSpace_kilianVerifyRawBounded_of_params`).
* **Raw prover model and soundness (`KilianRawProver`, `HashFamily.kilianRawSound`):**
  Every uniform strict PPT raw prover reduces via `KilianRawProver.toKilianProver` (using
  `kilianResponseDecoder`) to a uniform strict PPT `KilianProver`, yielding negligible soundness
  error under any `HashFamily`.

## Main definitions

* `Cslib.Crypto.KilianChallengeInput`, `Cslib.Crypto.encKilianChallengeInput`.
* `Cslib.Crypto.KilianRawCommitment`, `Cslib.Crypto.encKilianRawCommitment`.
* `Cslib.Crypto.KilianRawProver`, `Cslib.Crypto.KilianRawProver.IsPPT`,
  `Cslib.Crypto.KilianRawProver.toKilianProver`.
* `Cslib.Crypto.kilianOpeningDecoder`, `Cslib.Crypto.kilianResponseDecoder`,
  `Cslib.Crypto.kilianProverMsgDecoder`.
* `Cslib.Crypto.kilianOpeningEncBound`, `Cslib.Crypto.kilianRawProverCap`.
* `Cslib.Crypto.kilianVerifyRawBounded`, `Cslib.Crypto.kilianHonestRawBoundedGame`,
  `Cslib.Crypto.kilianRawSoundnessGame`, `Cslib.Crypto.KilianRawSound`.

## Main results

* `Cslib.Crypto.length_encKilianProverMsg_le_cap_of_kilianVerify`,
  `Cslib.Crypto.kilianVerifyRawBounded_enc_eq_of_root_le`,
  `Cslib.Crypto.eval_kilianHonestRawBoundedGame`.
* `Cslib.Crypto.computableInPolyTime_kilianVerifyRawBounded`,
  `Cslib.Crypto.computableInTimeAndSpace_kilianVerifyRawBounded`,
  `Cslib.Crypto.computableInTimeAndSpace_kilianVerifyRawBounded_of_params`.
* `Cslib.Crypto.succProbability_kilianRawSoundnessGame_le`,
  `Cslib.Crypto.HashFamily.kilianRawSound`.
-/

@[expose] public section

namespace Cslib.Crypto

open Complexity Probability Turing.MultiTapeTM
open scoped ENNReal NNReal

/-! ### Challenge inputs and raw prover types -/

section
variable {α : Type}

/-- The verifier's own inputs to Kilian verification: hash key, statement, and sampled PCP
challenges, keeping prover-controlled commitment/response bits in the raw prover tape. -/
@[ext]
structure KilianChallengeInput (α : Type) where
  /-- The hash key. -/
  key : List Bool
  /-- The statement. -/
  stmt : α
  /-- The verifier's PCP challenge strings, one per repetition. -/
  challenges : List (List Bool)
  deriving DecidableEq, Repr, Inhabited

/-- Encoding of `KilianChallengeInput`: framed hash key, framed statement, and challenges. -/
enc_structure encKilianChallengeInput (enc : α ↪ List Bool) : KilianChallengeInput α where
  key : encBits, stmt : enc, challenges : (encList encBits)

attribute [fun_prop] encKilianChallengeInput_key_polyTime encKilianChallengeInput_stmt_polyTime
  encKilianChallengeInput_challenges_polyTime encKilianChallengeInput_mk_polyTime

/-- A raw cheating prover's first-stage output: statement, raw root bitstring, and saved state. -/
@[ext]
structure KilianRawCommitment (α : Type) where
  /-- The statement chosen by the prover. -/
  stmt : α
  /-- The raw root bitstring sent in the commitment message. -/
  rawRoot : List Bool
  /-- The saved state passed to the second stage. -/
  state : List Bool
  deriving DecidableEq, Repr, Inhabited

/-- Encoding of `KilianRawCommitment`: framed statement, framed raw root, and saved state. -/
enc_structure encKilianRawCommitment (enc : α ↪ List Bool) : KilianRawCommitment α where
  stmt : enc, rawRoot : encBits, state : encBits

end

/-- A cheating prover sending raw bitstrings in Kilian's protocol (`rawRoot` in the first stage
and an arbitrary raw response bitstring in the second stage). -/
structure KilianRawProver (α : Type) where
  /-- First stage: output statement, raw root bitstring, and saved state. -/
  commit : ℕ → List Bool → ProbComp (KilianRawCommitment α)
  /-- Second stage: answer `ρs` from saved `state` with a raw bitstring response. -/
  answer : ℕ → List Bool → List (List Bool) → ProbComp (List Bool)

/-- A raw cheating prover is strict PPT if both stages run in polynomial time in their full
encoded inputs, saved state, and challenges. -/
structure KilianRawProver.IsPPT {α : Type} (enc : α ↪ List Bool)
    (P : KilianRawProver α) : Prop where
  /-- First stage is a strict PPT family from `(n, k)` to `KilianRawCommitment`. -/
  commit : Probability.IsPPT (encKilianRawCommitment enc) P.commit
  /-- Second stage is strict PPT on `(n, state, ρs)` outputting a raw bitstring. -/
  answer : IsPPTOn (encPair encUnary (encPair encBits (encList encBits))) encBits
    (fun ⟨n, state, ρs⟩ => P.answer n state ρs)

/-! ### Total decoders for raw transcripts -/

/-- Total polynomial-time decoder for a `MerkleOpening Bool`, inverting `encKilianOpening`. -/
def kilianOpeningDecoder : Decoder encKilianOpening :=
  (Decoder.pair Decoder.bool (Decoder.list Decoder.bits)).map
    (fun p => ⟨p.1, p.2⟩) (fun o => (o.leaf, o.path))
    (fun ⟨_, _⟩ => rfl) (fun p => encKilianOpening_apply ⟨p.1, p.2⟩)

/-- Total polynomial-time decoder for `KilianResponse`, inverting `encKilianResponse`. -/
def kilianResponseDecoder : Decoder encKilianResponse :=
  Decoder.list (Decoder.list kilianOpeningDecoder)

/-- Total polynomial-time decoder for `(root, resp)` from raw prover bits. -/
def kilianProverMsgDecoder : Decoder (encPair encBits encKilianResponse) :=
  Decoder.pair Decoder.bits kilianResponseDecoder

/-- `kilianProverMsgDecoder` recovers `(root, kilianResponseDecoder.decode rawResp)` from an
encoded pair of bit strings. -/
theorem kilianProverMsgDecoder_encPair_bits (root rawResp : List Bool) :
    kilianProverMsgDecoder.decode (encPair encBits encBits (root, rawResp)) =
      (root, kilianResponseDecoder.decode rawResp) := by
  simp [kilianProverMsgDecoder, Decoder.pair, Decoder.bits, encPair_apply,
    unframe_frame_append, dropFrame_frame_append]

/-! ### Deterministic transcript length cap and bounded-prefix verifier -/

/-- Upper bound on the encoded bit length of one `MerkleOpening Bool` whose authentication path
has `depth` sibling labels each of length at most `kLength`. -/
def kilianOpeningEncBound (kLength depth : ℕ) : ℕ :=
  3 + depth * (2 * kLength + 1)

/-- Deterministic cap on the encoded length of any valid raw prover message
`encPair encBits encKilianResponse (root, resp)` with `root.length ≤ k.length` against verifier
challenges `(k, x, ρs)`. Oversized messages exceeding this cap are rejected immediately by
`kilianVerifyRawBounded`. -/
def kilianRawProverCap {α : Type} (V : PCPVerifier α) (k : List Bool) (x : α)
    (ρs : List (List Bool)) : ℕ :=
  (2 * k.length + 1) +
    (ρs.map fun ρ =>
      2 * ((V.queries (x, ρ)).length *
        (2 * kilianOpeningEncBound k.length (kilianDepth V x) + 1)) + 1).sum

/-- The verifier decision operating directly on verifier inputs `ch` and an arbitrary unframed or
oversized raw prover bitstring `rawProver`. Rejects immediately if `rawProver.length > cap`, and
otherwise decodes `(root, resp)` via `kilianProverMsgDecoder` and runs `kilianVerify`. -/
def kilianVerifyRawBounded {α : Type} (H : List Bool → List Bool → List Bool) (V : PCPVerifier α)
    (ch : KilianChallengeInput α) (rawProver : List Bool) : Bool :=
  decide (rawProver.length ≤ kilianRawProverCap V ch.key ch.stmt ch.challenges) &&
    let p := kilianProverMsgDecoder.decode rawProver
    kilianVerify H V ch.key ch.stmt p.1 ch.challenges p.2

section CapBounds

variable {α : Type} {H : List Bool → List Bool → List Bool} {V : PCPVerifier α}

private lemma length_encKilianOpening_le_of_merkleVerify {k root : List Bool} {d i : ℕ}
    {o : MerkleOpening Bool}
    (hmv : merkleVerify H k d root i [o.leaf] o.path = true)
    (hroot : root.length ≤ k.length) :
    (encKilianOpening o).length ≤ kilianOpeningEncBound k.length d := by
  rw [merkleVerify_eq_true_iff] at hmv
  obtain ⟨hpathLen, -, hpathBits, -⟩ := hmv
  have hpathEnc : (encList encBits o.path).length ≤ d * (2 * k.length + 1) := by
    refine (length_encList_le encBits o.path fun s hs => ?_).trans (by rw [hpathLen])
    exact (hpathBits s hs).le.trans hroot
  simp only [encKilianOpening_apply, length_encPair, encBool_apply, List.length_singleton,
    kilianOpeningEncBound]
  omega

private lemma length_encList_opening_le_of_kilianCheck {k : List Bool} {x : α} {root ρ : List Bool}
    {answers : List (MerkleOpening Bool)}
    (hc : kilianCheck H V k x root ρ answers = true)
    (hroot : root.length ≤ k.length) :
    (encList encKilianOpening answers).length ≤
      (V.queries (x, ρ)).length * (2 * kilianOpeningEncBound k.length (kilianDepth V x) + 1) := by
  simp only [kilianCheck, MerkleOpening.verify, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true] at hc
  obtain ⟨⟨hlenEq, hall⟩, -⟩ := hc
  refine (length_encList_le encKilianOpening answers fun o ho => ?_).trans (by rw [hlenEq])
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ho
  have hzip : ((V.queries (x, ρ))[i]'(by omega), answers[i]) ∈ (V.queries (x, ρ)).zip answers := by
    rw [← List.getElem_zip]
    exact List.getElem_mem (by rw [List.length_zip, ← hlenEq, min_self]; exact hi)
  exact length_encKilianOpening_le_of_merkleVerify (hall _ hzip) hroot

private lemma length_encKilianResponse_le_sum {k : List Bool} {x : α} (ρs : List (List Bool))
    (resp : KilianResponse) (hlen : resp.length = ρs.length)
    (hrep : ∀ ρ answers, (ρ, answers) ∈ ρs.zip resp →
      (encList encKilianOpening answers).length ≤
        (V.queries (x, ρ)).length * (2 * kilianOpeningEncBound k.length (kilianDepth V x) + 1)) :
    (encKilianResponse resp).length ≤
      (ρs.map fun ρ =>
        2 * ((V.queries (x, ρ)).length *
          (2 * kilianOpeningEncBound k.length (kilianDepth V x) + 1)) + 1).sum := by
  induction ρs generalizing resp with
  | nil =>
    cases resp with
    | nil => simp [encKilianResponse]
    | cons _ _ => simp at hlen
  | cons ρ ρs ih =>
    cases resp with
    | nil => simp at hlen
    | cons answers resp' =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      have hhead := hrep ρ answers (by simp)
      have htail := ih resp' hlen fun ρ' a' hmem =>
        hrep ρ' a' (by simp [List.zip_cons_cons, hmem])
      dsimp only [encKilianResponse] at htail ⊢
      simp only [encList_cons, List.length_append, length_frame, List.map_cons, List.sum_cons]
      omega

/-- **Accepted transcripts fit under `kilianRawProverCap`**: any transcript accepted by
`kilianVerify` with `root.length ≤ k.length` has encoded pair length at most
`kilianRawProverCap V k x ρs`. -/
theorem length_encKilianProverMsg_le_cap_of_kilianVerify {k : List Bool} {x : α} {root : List Bool}
    {ρs : List (List Bool)} {resp : KilianResponse}
    (hver : kilianVerify H V k x root ρs resp = true)
    (hroot : root.length ≤ k.length) :
    (encPair encBits encKilianResponse (root, resp)).length ≤ kilianRawProverCap V k x ρs := by
  simp only [kilianVerify, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hver
  obtain ⟨hlenEq, hall⟩ := hver
  have hresp := length_encKilianResponse_le_sum (V := V) (k := k) (x := x) ρs resp hlenEq
    fun ρ answers hmem => length_encList_opening_le_of_kilianCheck (hall (ρ, answers) hmem) hroot
  simp only [length_encPair, encBits_apply, kilianRawProverCap]
  omega

/-- Honest prover transcripts for digest-length hash functions fit strictly under
`kilianRawProverCap`. -/
theorem length_encKilianProverMsg_honest_le_cap
    (hlen : ∀ k y, (H k y).length = k.length) {x : α} {table : List Bool}
    (htable : V.tableVerifier (x, table) = true) (k : List Bool) {ρs : List (List Bool)}
    (hρs : ∀ ρ ∈ ρs, ρ.length = V.coins x) :
    (encPair encBits encKilianResponse
      (kilianCommit H V k x table, kilianRespond H V k x table ρs)).length ≤
      kilianRawProverCap V k x ρs := by
  refine length_encKilianProverMsg_le_cap_of_kilianVerify
    (kilianVerify_kilianRespond htable k (hlen k) hρs) ?_
  rw [kilianCommit, length_merkleRoot (hlen k)]

/-- **Prefix truncation invariance**: `kilianVerifyRawBounded` depends only on the first
`kilianRawProverCap V ch.key ch.stmt ch.challenges + 1` bits of `rawProver`. -/
theorem kilianVerifyRawBounded_take_eq (H : List Bool → List Bool → List Bool) (V : PCPVerifier α)
    (ch : KilianChallengeInput α) (rawProver : List Bool) :
    kilianVerifyRawBounded H V ch rawProver =
      kilianVerifyRawBounded H V ch
        (rawProver.take (kilianRawProverCap V ch.key ch.stmt ch.challenges + 1)) := by
  set cap := kilianRawProverCap V ch.key ch.stmt ch.challenges
  by_cases hle : rawProver.length ≤ cap
  · rw [List.take_of_length_le (hle.trans (Nat.le_succ cap))]
  · have hgt : cap < rawProver.length := Nat.lt_of_not_ge hle
    have htakeLen : (rawProver.take (cap + 1)).length = cap + 1 := by
      simp [List.length_take, hgt]
    simp [kilianVerifyRawBounded, cap, hle, htakeLen]

/-- Oversized prover bitstrings exceeding `kilianRawProverCap` are always rejected. -/
theorem kilianVerifyRawBounded_eq_false_of_cap_lt (H : List Bool → List Bool → List Bool)
    (V : PCPVerifier α) {ch : KilianChallengeInput α} {rawProver : List Bool}
    (hlt : kilianRawProverCap V ch.key ch.stmt ch.challenges < rawProver.length) :
    kilianVerifyRawBounded H V ch rawProver = false := by
  simp [kilianVerifyRawBounded, Nat.not_le_of_gt hlt]

/-- On any encoded pair within `kilianRawProverCap`, `kilianVerifyRawBounded` agrees with
`kilianVerify`. -/
theorem kilianVerifyRawBounded_enc_eq (H : List Bool → List Bool → List Bool) (V : PCPVerifier α)
    (ch : KilianChallengeInput α) (root : List Bool) (resp : KilianResponse)
    (hle : (encPair encBits encKilianResponse (root, resp)).length ≤
      kilianRawProverCap V ch.key ch.stmt ch.challenges) :
    kilianVerifyRawBounded H V ch (encPair encBits encKilianResponse (root, resp)) =
      kilianVerify H V ch.key ch.stmt root ch.challenges resp := by
  rw [kilianVerifyRawBounded, kilianProverMsgDecoder.decode_enc]
  simp only [hle, decide_true, Bool.true_and]

/-- On any encoded pair `(root, resp)` with `root.length ≤ ch.key.length`, `kilianVerifyRawBounded`
agrees unconditionally with `kilianVerify`. -/
theorem kilianVerifyRawBounded_enc_eq_of_root_le (H : List Bool → List Bool → List Bool)
    (V : PCPVerifier α) (ch : KilianChallengeInput α) (root : List Bool) (resp : KilianResponse)
    (hroot : root.length ≤ ch.key.length) :
    kilianVerifyRawBounded H V ch (encPair encBits encKilianResponse (root, resp)) =
      kilianVerify H V ch.key ch.stmt root ch.challenges resp := by
  by_cases hver : kilianVerify H V ch.key ch.stmt root ch.challenges resp = true
  · have hle := length_encKilianProverMsg_le_cap_of_kilianVerify hver hroot
    rw [kilianVerifyRawBounded_enc_eq H V ch root resp hle, hver]
  · simp only [Bool.not_eq_true] at hver
    rw [hver]
    by_cases hle :
        (encPair encBits encKilianResponse (root, resp)).length ≤
          kilianRawProverCap V ch.key ch.stmt ch.challenges
    · rw [kilianVerifyRawBounded_enc_eq H V ch root resp hle, hver]
    · exact kilianVerifyRawBounded_eq_false_of_cap_lt H V (Nat.lt_of_not_ge hle)

/-- Honest execution evaluated by the bounded-prefix raw-wire verifier. -/
noncomputable def kilianHonestRawBoundedGame (H : List Bool → List Bool → List Bool)
    (V : PCPVerifier α) (x : α) (table : List Bool) (n : ℕ) : ProbComp Bool := do
  let k ← BitString.sampleList n
  let ρs ← kilianChallenges V n x
  return kilianVerifyRawBounded H V ⟨k, x, ρs⟩
    (encPair encBits encKilianResponse
      (kilianCommit H V k x table, kilianRespond H V k x table ρs))

/-- **Perfect completeness under the bounded-prefix raw verifier**: for a hash with key-length
digests and any accepted table, `kilianHonestRawBoundedGame` accepts with probability 1. -/
theorem eval_kilianHonestRawBoundedGame {H : List Bool → List Bool → List Bool} {V : PCPVerifier α}
    (hlen : ∀ k y, (H k y).length = k.length) {x : α} {table : List Bool}
    (htable : V.tableVerifier (x, table) = true) (n : ℕ) :
    ProbComp.eval (kilianHonestRawBoundedGame H V x table n) = PMF.pure true := by
  have heq : kilianHonestRawBoundedGame H V x table n = kilianHonestGame H V x table n := by
    refine congrArg (BitString.sampleList n >>= ·) (funext fun k => ?_)
    refine congrArg (kilianChallenges V n x >>= ·) (funext fun ρs => ?_)
    refine congrArg pure (kilianVerifyRawBounded_enc_eq_of_root_le H V ⟨k, x, ρs⟩ _ _ ?_)
    rw [kilianCommit, length_merkleRoot (hlen k)]
  rw [heq]
  exact eval_kilianHonestGame H V hlen htable n

end CapBounds

/-! ### Polynomial-time certificate and bounded-prefix machine execution -/

section MachineComplexity

variable {α : Type} {H : List Bool → List Bool → List Bool} {V : PCPVerifier α}
  {enc : α ↪ List Bool} {c : ℕ}

private theorem computableInPolyTime_listSumUnary :
    ComputableInPolyTime List.sum (encList encUnary) encUnary := by
  have hsum : ∀ l : List ℕ, List.sum l = l.foldl (fun acc u => acc + u) 0 := by
    intro l
    have hgen : ∀ acc : ℕ, l.foldl (fun x u => x + u) acc = acc + l.sum := by
      induction l with
      | nil => intro acc; simp
      | cons a l ih =>
        intro acc
        simp only [List.foldl_cons, List.sum_cons, ih (acc + a)]
        omega
    simpa using (hgen 0).symm
  have hfold := ComputableInPolyTime.foldlWith_of_bounded_growth
    (encP := encUnary) (encA := encUnary) (encL := encList encUnary) (encB := encUnary)
    (encIn := encList encUnary)
    (par := fun _ => 0) (list := fun l => l) (init := fun _ => 0) (step := fun _ acc u => acc + u)
    (ComputableInPolyTime.const 0) ComputableInPolyTime.id' (ComputableInPolyTime.const 0)
    (by fun_prop)
    (growth := fun l => (encList encUnary l).length)
    PolyBounded.self
    (fun l state value hmem => by
      have hlen := length_le_encList_of_mem encUnary hmem
      simp only [encUnary_apply, List.length_replicate] at hlen ⊢
      omega)
  have heq : (fun l : List ℕ => l.foldl (fun acc u => acc + u) 0) = List.sum :=
    funext fun l => (hsum l).symm
  rwa [heq] at hfold

/-- `kilianRawProverCap` is computable in polynomial time in unary from `KilianChallengeInput`. -/
@[program_certificate]
theorem computableInPolyTime_kilianRawProverCap
    (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1)) :
    ComputableInPolyTime
      (fun ch : KilianChallengeInput α => kilianRawProverCap V ch.key ch.stmt ch.challenges)
      (encKilianChallengeInput enc) encUnary := by
  have hk : ComputableInPolyTime (fun ch : KilianChallengeInput α => ch.key)
      (encKilianChallengeInput enc) encBits :=
    encKilianChallengeInput_key_polyTime enc ComputableInPolyTime.id'
  have hkLen : ComputableInPolyTime (fun ch : KilianChallengeInput α => ch.key.length)
      (encKilianChallengeInput enc) encUnary :=
    ComputableInPolyTime.length_bits.comp hk
  have hstmt : ComputableInPolyTime (fun ch : KilianChallengeInput α => ch.stmt)
      (encKilianChallengeInput enc) enc :=
    encKilianChallengeInput_stmt_polyTime enc ComputableInPolyTime.id'
  have hρs : ComputableInPolyTime (fun ch : KilianChallengeInput α => ch.challenges)
      (encKilianChallengeInput enc) (encList encBits) :=
    encKilianChallengeInput_challenges_polyTime enc ComputableInPolyTime.id'
  have htable := (PCPVerifier.isPolyTime_queryTable hV hcoins).comp hstmt
  have hdepth : ComputableInPolyTime (fun ch : KilianChallengeInput α => kilianDepth V ch.stmt)
      (encKilianChallengeInput enc) encUnary :=
    (ComputableInPolyTime.unary_clog_const 2).comp
      ((ComputableInPolyTime.length_list encNat).comp htable)
  have hprefix : ComputableInPolyTime
      (fun ch : KilianChallengeInput α => 2 * ch.key.length + 1)
      (encKilianChallengeInput enc) encUnary :=
    ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2) hkLen)
      (ComputableInPolyTime.const 1)
  have hob : ComputableInPolyTime
      (fun ch : KilianChallengeInput α =>
        kilianOpeningEncBound ch.key.length (kilianDepth V ch.stmt))
      (encKilianChallengeInput enc) encUnary := by
    unfold kilianOpeningEncBound
    exact ComputableInPolyTime.unary_add' (ComputableInPolyTime.const 3)
      (ComputableInPolyTime.unary_mul' hdepth hprefix)
  have hfst := ComputableInPolyTime.fst (encKilianChallengeInput enc) encBits
  have hsnd := ComputableInPolyTime.snd (encKilianChallengeInput enc) encBits
  have hq : ComputableInPolyTime
      (fun p : KilianChallengeInput α × List Bool => (V.queries (p.1.stmt, p.2)).length)
      (encPair (encKilianChallengeInput enc) encBits) encUnary :=
    (ComputableInPolyTime.length_list encNat).comp
      (hV.queries.comp ((hstmt.comp hfst).prod hsnd))
  have hterm : ComputableInPolyTime
      (fun p : KilianChallengeInput α × List Bool =>
        2 * ((V.queries (p.1.stmt, p.2)).length *
          (2 * kilianOpeningEncBound p.1.key.length (kilianDepth V p.1.stmt) + 1)) + 1)
      (encPair (encKilianChallengeInput enc) encBits) encUnary := by
    have hob' := ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2) (hob.comp hfst))
      (ComputableInPolyTime.const 1)
    exact ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2)
        (ComputableInPolyTime.unary_mul' hq hob'))
      (ComputableInPolyTime.const 1)
  have hmap := ComputableInPolyTime.mapWithInput
    (f := fun ch ρ =>
      2 * ((V.queries (ch.stmt, ρ)).length *
        (2 * kilianOpeningEncBound ch.key.length (kilianDepth V ch.stmt) + 1)) + 1)
    hρs hterm
  have hsum := computableInPolyTime_listSumUnary.comp hmap
  unfold kilianRawProverCap
  exact ComputableInPolyTime.unary_add' hprefix hsum

/-- **Polynomial-time certificate for `kilianVerifyRawBounded`**: decodes and verifies the raw
prover bitstring within polynomial time in `|(ch, rawProver)|`. -/
@[program_certificate]
theorem computableInPolyTime_kilianVerifyRawBounded
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length) (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1)) :
    ComputableInPolyTime
      (fun p : KilianChallengeInput α × List Bool => kilianVerifyRawBounded H V p.1 p.2)
      (encPair (encKilianChallengeInput enc) encBits) encBool := by
  have hch := ComputableInPolyTime.fst (encKilianChallengeInput enc) encBits
  have hraw := ComputableInPolyTime.snd (encKilianChallengeInput enc) encBits
  have hcap := (computableInPolyTime_kilianRawProverCap hV hcoins).comp hch
  have hle : ComputableInPolyTime
      (fun p : KilianChallengeInput α × List Bool =>
        decide (p.2.length ≤ kilianRawProverCap V p.1.key p.1.stmt p.1.challenges))
      (encPair (encKilianChallengeInput enc) encBits) encBool :=
    ComputableInPolyTime.unary_le.comp
      ((ComputableInPolyTime.length_bits.comp hraw).prod hcap)
  have hdec := kilianProverMsgDecoder.computableInPolyTime.comp hraw
  have hview : ComputableInPolyTime
      (fun p : KilianChallengeInput α × List Bool =>
        ({ key := p.1.key, stmt := p.1.stmt,
           root := (kilianProverMsgDecoder.decode p.2).1,
           challenges := p.1.challenges,
           response := (kilianProverMsgDecoder.decode p.2).2 } : KilianView α))
      (encPair (encKilianChallengeInput enc) encBits) (encKilianView enc) := by
    have hkey : ComputableInPolyTime (fun p : KilianChallengeInput α × List Bool => p.1.key)
        (encPair (encKilianChallengeInput enc) encBits) encBits := by fun_prop
    have hstmt : ComputableInPolyTime (fun p : KilianChallengeInput α × List Bool => p.1.stmt)
        (encPair (encKilianChallengeInput enc) encBits) enc := by fun_prop
    have hchal : ComputableInPolyTime
        (fun p : KilianChallengeInput α × List Bool => p.1.challenges)
        (encPair (encKilianChallengeInput enc) encBits) (encList encBits) := by fun_prop
    have hroot : ComputableInPolyTime
        (fun p : KilianChallengeInput α × List Bool => (kilianProverMsgDecoder.decode p.2).1)
        (encPair (encKilianChallengeInput enc) encBits) encBits :=
      (ComputableInPolyTime.fst encBits encKilianResponse).comp hdec
    have hresp : ComputableInPolyTime
        (fun p : KilianChallengeInput α × List Bool => (kilianProverMsgDecoder.decode p.2).2)
        (encPair (encKilianChallengeInput enc) encBits) encKilianResponse :=
      (ComputableInPolyTime.snd encBits encKilianResponse).comp hdec
    have hclaim : ComputableInPolyTime
        (fun p : KilianChallengeInput α × List Bool =>
          ({ key := p.1.key, stmt := p.1.stmt,
             root := (kilianProverMsgDecoder.decode p.2).1 } : KilianClaim α))
        (encPair (encKilianChallengeInput enc) encBits) (encKilianClaim enc) :=
      encKilianClaim_mk_polyTime enc hkey hstmt hroot
    exact encKilianView_mk_polyTime enc hclaim hchal hresp
  have hver := (computableInPolyTime_kilianVerify hH hlen hV hcoins).comp hview
  unfold kilianVerifyRawBounded
  exact ComputableInPolyTime.bool_and' hle hver

/-- **Worst-case verifier runtime and space on arbitrary unbounded raw provers (by verifier input
length)**: there is one fixed binary `MultiTapeTM` computing `kilianVerifyRawBounded` on every
`(ch, rawProver)` whose time and space depend *only* on `(encKilianChallengeInput enc ch).length`,
for **every** `rawProver : List Bool` (even exponentially long or malformed). -/
theorem computableInTimeAndSpace_kilianVerifyRawBounded
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length) (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1)) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : Turing.MultiTapeTM k Bool State)
      (t s : ℕ → ℕ),
      PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
      tm.ComputesFunInTimeAndSpace (encPair (encKilianChallengeInput enc) encBits) encBool
        (fun p => kilianVerifyRawBounded H V p.1 p.2)
        (fun p => t (encKilianChallengeInput enc p.1).length)
        (fun p => s (encKilianChallengeInput enc p.1).length) :=
  computableInTimeAndSpace_boundedPrefix
    (computableInPolyTime_kilianRawProverCap hV hcoins)
    (computableInPolyTime_kilianVerifyRawBounded hH hlen hV hcoins)
    (kilianVerifyRawBounded_take_eq H V)

/-- **Worst-case verifier runtime and space in `n + |enc x|` on ALL arbitrary raw provers**:
under a polynomial-time hash with key-length digests and a polynomial-time PCP verifier `V` with
`O(log |enc x|)` random bits, there is one fixed binary multi-tape Turing machine computing
`kilianVerifyRawBounded` whose step count and space on every `(ch, rawProver)` with key length `≤ n`
and `≤ n` challenges of length `≤ V.coins ch.stmt` are bounded by polynomials in
`n + |enc ch.stmt|`, uniformly over **all** arbitrary unbounded `rawProver : List Bool`. -/
theorem computableInTimeAndSpace_kilianVerifyRawBounded_of_params
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k x, (H k x).length = k.length) (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1)) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : Turing.MultiTapeTM k Bool State)
      (t s tBound sBound : ℕ → ℕ),
      PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
      PolynomiallyBounded tBound ∧ PolynomiallyBounded sBound ∧
      tm.ComputesFunInTimeAndSpace (encPair (encKilianChallengeInput enc) encBits) encBool
        (fun p => kilianVerifyRawBounded H V p.1 p.2)
        (fun p => t (encKilianChallengeInput enc p.1).length)
        (fun p => s (encKilianChallengeInput enc p.1).length) ∧
      (∀ (n : ℕ) (ch : KilianChallengeInput α) (rawProver : List Bool),
        ch.key.length ≤ n → ch.challenges.length ≤ n →
        (∀ ρ ∈ ch.challenges, ρ.length ≤ V.coins ch.stmt) →
          tm.ComputesInTimeAndSpace
            (encPair (encKilianChallengeInput enc) encBits (ch, rawProver))
            (encBool (kilianVerifyRawBounded H V ch rawProver))
            (tBound (n + (enc ch.stmt).length))
            (sBound (n + (enc ch.stmt).length))) := by
  obtain ⟨kTM, State, hfin, tm, t₀, s₀, ht₀, hs₀, htm⟩ :=
    computableInTimeAndSpace_kilianVerifyRawBounded (H := H) (V := V) (enc := enc) hH hlen hV hcoins
  obtain ⟨ct, dt, htle⟩ := polynomiallyBounded_iff_le.mp ht₀
  obtain ⟨cs, ds, hsle⟩ := polynomiallyBounded_iff_le.mp hs₀
  let t : ℕ → ℕ := fun m => ct * (m + 1) ^ dt
  let s : ℕ → ℕ := fun m => cs * (m + 1) ^ ds
  have ht_pb : PolynomiallyBounded t := polynomiallyBounded_iff_le.mpr ⟨ct, dt, fun _ => le_rfl⟩
  have hs_pb : PolynomiallyBounded s := polynomiallyBounded_iff_le.mpr ⟨cs, ds, fun _ => le_rfl⟩
  let inBound : ℕ → ℕ := fun u =>
    2 * (2 * u + 1) + 1 + (2 * u + 1 + u * (2 * (c * (u + 1)) + 1))
  have hin_pb : PolynomiallyBounded inBound := by
    dsimp only [inBound]
    fun_prop
  have htm' : tm.ComputesFunInTimeAndSpace (encPair (encKilianChallengeInput enc) encBits) encBool
      (fun p => kilianVerifyRawBounded H V p.1 p.2)
      (fun p => t (encKilianChallengeInput enc p.1).length)
      (fun p => s (encKilianChallengeInput enc p.1).length) :=
    htm.mono (fun _ => htle _) (fun _ => hsle _)
  let tBound : ℕ → ℕ := fun u => t (inBound u)
  let sBound : ℕ → ℕ := fun u => s (inBound u)
  refine ⟨kTM, State, hfin, tm, t, s, tBound, sBound, ht_pb, hs_pb,
    ht_pb.comp hin_pb, hs_pb.comp hin_pb, htm',
    fun n ch rawProver hk hn hρs => ?_⟩
  have hch_len :
      (encKilianChallengeInput enc ch).length ≤ inBound (n + (enc ch.stmt).length) := by
    have hchal_elem : ∀ ρ ∈ ch.challenges, ρ.length ≤ c * ((n + (enc ch.stmt).length) + 1) := by
      intro ρ hρ
      exact (hρs ρ hρ).trans ((hcoins ch.stmt).trans
        (Nat.mul_le_mul_left c (Nat.succ_le_succ
          ((Nat.log_le_self 2 _).trans (Nat.le_add_left _ _)))))
    have hchallenges :
        (encList encBits ch.challenges).length ≤
          (n + (enc ch.stmt).length) * (2 * (c * ((n + (enc ch.stmt).length) + 1)) + 1) :=
      (length_encList_le encBits ch.challenges hchal_elem).trans
        (Nat.mul_le_mul_right _ (hn.trans (Nat.le_add_right _ _)))
    have hkey_le : ch.key.length ≤ n + (enc ch.stmt).length := hk.trans (Nat.le_add_right _ _)
    have hstmt_le : (enc ch.stmt).length ≤ n + (enc ch.stmt).length := Nat.le_add_left _ _
    simp only [encKilianChallengeInput_apply, length_encPair, encBits_apply]
    dsimp only [inBound]
    omega
  have ht_mono :
      t (encKilianChallengeInput enc ch).length ≤ tBound (n + (enc ch.stmt).length) :=
    Nat.mul_le_mul_left ct (Nat.pow_le_pow_left (Nat.succ_le_succ hch_len) dt)
  have hs_mono :
      s (encKilianChallengeInput enc ch).length ≤ sBound (n + (enc ch.stmt).length) :=
    Nat.mul_le_mul_left cs (Nat.pow_le_pow_left (Nat.succ_le_succ hch_len) ds)
  have hp := htm' (ch, rawProver)
  exact ⟨hp.1, hp.2.1.mono ht_mono, hp.2.2.mono hs_mono⟩

end MachineComplexity

/-! ### Raw prover soundness -/

section RawSoundness

variable {α : Type}

/-- Convert a raw prover to a structured `KilianProver` by decoding its raw second-stage response
with `kilianResponseDecoder`. -/
def KilianRawProver.toKilianProver (P : KilianRawProver α) : KilianProver α where
  commit n k := do
    let cm ← P.commit n k
    return { stmt := cm.stmt, root := cm.rawRoot, state := cm.state }
  answer n state ρs := do
    let rawResp ← P.answer n state ρs
    return kilianResponseDecoder.decode rawResp

/-- Decoding a uniform strict PPT raw prover produces a uniform strict PPT `KilianProver`. -/
theorem KilianRawProver.IsPPT.toKilianProver {enc : α ↪ List Bool} {P : KilianRawProver α}
    (hP : P.IsPPT enc) :
    P.toKilianProver.IsPPT enc := by
  refine ⟨?_, ?_⟩
  · let f : KilianRawCommitment α → KilianCommitment α :=
      fun cm => { stmt := cm.stmt, root := cm.rawRoot, state := cm.state }
    have hf : ComputableInPolyTime f (encKilianRawCommitment enc) (encKilianCommitment enc) := by
      have hstmt : ComputableInPolyTime (fun cm : KilianRawCommitment α => cm.stmt)
          (encKilianRawCommitment enc) enc := by fun_prop
      have hroot : ComputableInPolyTime (fun cm : KilianRawCommitment α => cm.rawRoot)
          (encKilianRawCommitment enc) encBits := by fun_prop
      have hstate : ComputableInPolyTime (fun cm : KilianRawCommitment α => cm.state)
          (encKilianRawCommitment enc) encBits := by fun_prop
      have hmsg : ComputableInPolyTime
          (fun cm : KilianRawCommitment α =>
            ({ stmt := cm.stmt, root := cm.rawRoot } : KilianMessage α))
          (encKilianRawCommitment enc) (encKilianMessage enc) :=
        encKilianMessage_mk_polyTime enc hstmt hroot
      exact encKilianCommitment_mk_polyTime enc hmsg hstate
    simpa only [KilianRawProver.toKilianProver, bind_pure_comp, Functor.map] using
      (hP.commit.on.map hf).isPPT
  · simpa only [KilianRawProver.toKilianProver, bind_pure_comp, Functor.map] using
      hP.answer.map kilianResponseDecoder.computableInPolyTime

open Classical in
/-- Soundness experiment for a raw cheating prover verified by `kilianVerifyRawBounded`. -/
noncomputable def kilianRawSoundnessGame (H : List Bool → List Bool → List Bool)
    (V : PCPVerifier α) (L : Set α) (P : KilianRawProver α) (n : ℕ) : ProbComp Bool := do
  let k ← BitString.sampleList n
  let cm ← P.commit n k
  let ρs ← kilianChallenges V n cm.stmt
  let rawResp ← P.answer n cm.state ρs
  return (decide (cm.stmt ∉ L) &&
    kilianVerifyRawBounded H V ⟨k, cm.stmt, ρs⟩ (encPair encBits encBits (cm.rawRoot, rawResp)))

/-- **Computational soundness against raw provers**: every uniform strict PPT raw prover convinces
`kilianVerifyRawBounded` of a false statement with negligible probability. -/
def KilianRawSound (H : List Bool → List Bool → List Bool) (V : PCPVerifier α)
    (enc : α ↪ List Bool) (L : Set α) : Prop :=
  ∀ P : KilianRawProver α, P.IsPPT enc →
    Negligible fun n => Game.succProbability (ProbComp.eval (kilianRawSoundnessGame H V L P n))

/-- Every accepting run of `kilianRawSoundnessGame` also makes `kilianSoundnessGame` accept for
`P.toKilianProver`. -/
theorem succProbability_kilianRawSoundnessGame_le
    (H : List Bool → List Bool → List Bool) (V : PCPVerifier α)
    (L : Set α) (P : KilianRawProver α) (n : ℕ) :
    Game.succProbability (ProbComp.eval (kilianRawSoundnessGame H V L P n)) ≤
      Game.succProbability (ProbComp.eval (kilianSoundnessGame H V L P.toKilianProver n)) := by
  classical
  have hsound_eq :
      ProbComp.eval (kilianSoundnessGame H V L P.toKilianProver n) =
        ProbComp.eval do
          let k ← BitString.sampleList n
          let cm ← P.commit n k
          let ρs ← kilianChallenges V n cm.stmt
          let rawResp ← P.answer n cm.state ρs
          return (decide (cm.stmt ∉ L) &&
            kilianVerify H V k cm.stmt cm.rawRoot ρs (kilianResponseDecoder.decode rawResp)) := by
    simp [kilianSoundnessGame, KilianRawProver.toKilianProver]
  have hle :
      (ProbComp.eval (kilianRawSoundnessGame H V L P n)) true ≤
        (ProbComp.eval (kilianSoundnessGame H V L P.toKilianProver n)) true := by
    rw [hsound_eq]
    simp only [kilianRawSoundnessGame, ProbComp.eval_bind]
    refine Probability.PMF.bind_apply_mono_on_support _ _ fun k _ => ?_
    refine Probability.PMF.bind_apply_mono_on_support _ _ fun cm _ => ?_
    refine Probability.PMF.bind_apply_mono_on_support _ _ fun ρs _ => ?_
    refine Probability.PMF.bind_apply_mono_on_support _ _ fun rawResp _ => ?_
    have himpl :
        (decide (cm.stmt ∉ L) && kilianVerifyRawBounded H V ⟨k, cm.stmt, ρs⟩
          (encPair encBits encBits (cm.rawRoot, rawResp))) = true →
        (decide (cm.stmt ∉ L) &&
          kilianVerify H V k cm.stmt cm.rawRoot ρs (kilianResponseDecoder.decode rawResp)) =
          true := by
      simp only [Bool.and_eq_true, kilianVerifyRawBounded, kilianProverMsgDecoder_encPair_bits]
      exact fun h => ⟨h.1, h.2.2⟩
    rcases hb1 : decide (cm.stmt ∉ L) && kilianVerifyRawBounded H V ⟨k, cm.stmt, ρs⟩
        (encPair encBits encBits (cm.rawRoot, rawResp)) with _ | _
    · simp [ProbComp.eval_pure]
    · rw [himpl hb1]
  exact ENNReal.toNNReal_mono (PMF.apply_lt_top _ _).ne hle

/-- **Computational soundness of bounded-prefix raw Kilian** under any `HashFamily`, polynomial-time
`O(log n)`-coin PCP verifier `V`, and arbitrary uniform strict PPT raw provers. -/
theorem HashFamily.kilianRawSound {H : List Bool → List Bool → List Bool} (hH : HashFamily H)
    {V : PCPVerifier α} {enc : α ↪ List Bool} {L : Set α} {c : ℕ} {q : ℕ → ℕ}
    (hV : V.PolyTime enc) (hpcp : IsPCPVerifier enc (fun m => c * (Nat.log 2 m + 1)) q V L) :
    KilianRawSound H V enc L := by
  intro P hP
  refine negligible_of_le ((hH.kilianSound hV hpcp) P.toKilianProver hP.toKilianProver) fun n =>
    succProbability_kilianRawSoundnessGame_le H V L P n

end RawSoundness

end Cslib.Crypto
