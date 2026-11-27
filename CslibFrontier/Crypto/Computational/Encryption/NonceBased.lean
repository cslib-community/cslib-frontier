/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Frame.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
public import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
public import CslibFrontier.Crypto.Computational.TwoStage
public import CslibFrontier.Crypto.Game
public import CslibFrontier.Languages.Probabilistic.Oracle.Codec
import CslibFrontier.Languages.Probabilistic.Oracle.Interaction

/-!
# Nonce-based symmetric encryption and chosen-plaintext security

A nonce-based cipher ([BonehShoup2023], Section 5.5, printed pp. 201–202) consists of deterministic
encryption `c = E(k, m, N)` and deterministic decryption `m = D(k, c, N)` taking an explicit nonce
`N` alongside the message `m`, with correctness requiring `D(k, E(k, m, N), N) = m` (printed
p. 202). Section 9.5 (printed p. 378) extends both algorithms with an associated-data input `d`,
writing `c = E(k, m, d, N)` and `D(k, c, d, N)` (which outputs a message or `reject`).
`NonceCipher K M D C N` represents this general syntax with `Option M` decryption; plain
nonce-based encryption without associated data is the specialization `D = Unit`.

Unlike `symmetricCPAGameOn` / `SymmetricINDCPAOn` (`SymmetricCPA.lean`) and
`SymmetricCipher.cpaGame` / `SymmetricCipher.INDCPA` (`Authenticated.lean`), which model randomized
encryption without nonces (where multi-query CPA security requires ciphertext expansion,
`SymmetricCipher.not_indcpa_of_ciphertext_length_eq`), a `NonceCipher` is deterministic and relies
on nonce uniqueness across encryption queries to achieve CPA security with zero ciphertext
expansion.

Attack Game 5.3 ([BonehShoup2023], Section 5.5, printed p. 202) and its associated-data extension
(Section 9.5, Definition 9.7, printed p. 378) restrict encryption queries to equal-length message
pairs in `M` and pairwise distinct nonces `N_i ∈ N \ {N_1, …, N_{i-1}}`. To totalize this game for
arbitrary adversaries without partial oracles or `[Inhabited C]`, the typed left-or-right CPA
experiment `NonceCipher.cpaExperiment` maintains `(ok, seen) : Bool × List N`, starting from
`(true, [])`:
* While `ok = true`, on a query `(pair, d, nonce)` whose message pair satisfies
  `valid pair.msg₀ pair.msg₁ = true` and whose nonce satisfies `validNonce nonce = true` and
  `nonce ∉ seen`, the challenger records `nonce :: seen` and returns
  `some (E.encrypt k (pair.select b) d nonce)`.
* On any query with an inadmissible message pair, an invalid nonce, or a repeated nonce (or once
  `ok = false`), the challenger sets `ok := false` and returns `none` without invoking
  `E.encrypt`.
* When the adversary halts with `guess : Bool`, the experiment outputs `ok && guess`.

For every admissible, nonce-respecting adversary, `ok` stays `true` and every query returns
`some (E.encrypt k (pair.select b) d nonce)`. Any run that submits an out-of-domain message pair,
an out-of-domain nonce, or a repeated nonce sets `ok := false` independently of the challenge bit
`b`, never calls `E.encrypt` outside its valid domain, requires no `[Inhabited C]`, and outputs
`false` under both `b = false` and `b = true`, contributing zero distinguishing advantage.

`NonceCipher.INDCPA` defines asymptotic uniform chosen-plaintext security at `D = Unit` over bit
words (`List Bool`), adapting `IsOraclePPT encBool` distinguishers through the fixed canonical
word codec `NonceCipher.unitCPACodec`, which encodes `(pair, (), nonce)` as
`frame pair.msg₀ ++ frame pair.msg₁ ++ nonce` and encodes optional ciphertext replies via
`encOption encBits`. Fixing the codec avoids free codec parameters whose padding could make runtime
budgets vacuous.

This module provides definitions, the canonical word codec, and the `ProbOracleComp.runWith`
evaluation equation for `cpaExperiment`. Nonce-based counter mode, Theorem 5.6, and the
counter-overlap separation for unscaled nonces are in
`CslibFrontier.Crypto.Computational.Encryption.NonceCTR` (#5793); nonce-based ciphertext integrity
and AEAD (Attack Game 9.3, Definitions 9.8–9.9, printed p. 379) are deferred to their first
consumer in #5865.

## Main definitions

* `Cslib.Crypto.NonceCipher`: deterministic nonce-based cipher with associated data.
* `Cslib.Crypto.NonceCipher.Correct`: decryption inverts encryption on all inputs.
* `Cslib.Crypto.NonceCipher.cpaOracle`, `Cslib.Crypto.NonceCipher.cpaExperiment`: stateful
  left-or-right CPA challenger and experiment.
* `Cslib.Crypto.NonceCipher.decodeFramed`, `Cslib.Crypto.NonceCipher.unitCPACodec`: total
  frame-prefix parser and canonical word codec for `D = Unit` CPA queries.
* `Cslib.Crypto.NonceCipher.INDCPA`: asymptotic uniform CPA security for word-level nonce-based
  ciphers.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 5.5 (syntax, Attack Game 5.3, Definition 5.3, and equation (5.30), printed pp. 201–202)
  and Section 9.5 (associated-data syntax and Definition 9.7, printed p. 378).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-- A deterministic nonce-based symmetric cipher with key space `K`, message space `M`,
associated-data space `D`, ciphertext space `C`, and nonce space `N` ([BonehShoup2023],
Section 5.5, printed pp. 201–202, for `D = Unit`; Section 9.5, printed p. 378, with associated
data). -/
structure NonceCipher (K M D C N : Type) where
  /-- Deterministically encrypt message `m` with associated data `d` and nonce `nonce` under key
  `k`. -/
  encrypt : K → M → D → N → C
  /-- Deterministically decrypt ciphertext `c` with associated data `d` and nonce `nonce` under
  key `k`, returning `none` on rejection. -/
  decrypt : K → C → D → N → Option M

namespace NonceCipher

section Typed

variable {K M D C N : Type}

/-- Perfect decryption correctness ([BonehShoup2023], Section 5.5, printed p. 202; Section 9.5,
printed p. 378): decrypting a ciphertext under the same key, associated data, and nonce recovers
the plaintext. -/
@[expose]
def Correct (E : NonceCipher K M D C N) : Prop :=
  ∀ k m d nonce, E.decrypt k (E.encrypt k m d nonce) d nonce = some m

/-- Stateful left-or-right challenge oracle for `NonceCipher.cpaExperiment`, totalizing the
equal-length and unique-nonce query rules of [BonehShoup2023], Section 5.5, Attack Game 5.3
(printed p. 202) and Section 9.5, Definition 9.7 (printed p. 378). On state `(ok, seen)`:
* if `ok`, `valid pair.msg₀ pair.msg₁`, `validNonce nonce`, and `decide (nonce ∉ seen)` hold,
  record `nonce :: seen` and return `some (E.encrypt k (pair.select b) d nonce)`;
* otherwise set `ok := false` and return `none` without invoking `E.encrypt`. -/
@[expose]
def cpaOracle [DecidableEq N] (E : NonceCipher K M D C N)
    (valid : M → M → Bool) (validNonce : N → Bool) (k : K) (b : Bool)
    (query : MessagePair M × D × N) : StateT (Bool × List N) ProbComp (Option C)
  | (ok, seen) =>
    let (pair, d, nonce) := query
    if ok && valid pair.msg₀ pair.msg₁ && validNonce nonce && decide (nonce ∉ seen) then
      pure (some (E.encrypt k (pair.select b) d nonce), (true, nonce :: seen))
    else
      pure (none, (false, seen))

/-- Typed left-or-right chosen-plaintext experiment for a nonce-based cipher, totalizing
[BonehShoup2023], Section 5.5, Attack Game 5.3 (printed p. 202) and Section 9.5, Definition 9.7
(printed p. 378). Sample `k ← sampleKey`, run `adversary` from initial state `(true, [])` against
`E.cpaOracle valid validNonce k b`, and output `ok && guess` from the final `(guess, ok, seen)`.

For admissible, nonce-respecting executions, `ok` remains `true` and every query returns
`some (E.encrypt k (pair.select b) d nonce)`. Any execution submitting an inadmissible pair, an
invalid nonce, or a repeated nonce sets `ok := false` independently of `b`, never calls
`E.encrypt` outside its valid domain, requires no `[Inhabited C]`, and outputs `false` for both
challenge bits `b = false` and `b = true`, contributing zero distinguishing advantage. -/
@[expose]
noncomputable def cpaExperiment [DecidableEq N] (E : NonceCipher K M D C N)
    (sampleKey : ProbComp K) (valid : M → M → Bool) (validNonce : N → Bool)
    (adversary : ProbOracleComp (fun _ : MessagePair M × D × N => Option C) Bool)
    (b : Bool) : ProbComp Bool := do
  let k ← sampleKey
  let (guess, ok, _) ←
    (OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (E.cpaOracle valid validNonce k b))
      adversary).run (true, [])
  return (ok && guess)

/-- Output distribution of `NonceCipher.cpaExperiment` via `ProbOracleComp.runWith`. -/
theorem eval_cpaExperiment [DecidableEq N] (E : NonceCipher K M D C N)
    (sampleKey : ProbComp K) (valid : M → M → Bool) (validNonce : N → Bool)
    (adversary : ProbOracleComp (fun _ : MessagePair M × D × N => Option C) Bool)
    (b : Bool) :
    ProbComp.eval (E.cpaExperiment sampleKey valid validNonce adversary b) =
      (ProbComp.eval sampleKey).bind fun k =>
        (ProbOracleComp.runWith
          (fun q state => ProbComp.eval (E.cpaOracle valid validNonce k b q state))
          adversary (true, [])).map fun (guess, ok, _) => ok && guess := by
  simp only [cpaExperiment, ProbComp.eval_bind, ProbComp.eval_pure]
  refine congrArg (PMF.bind (ProbComp.eval sampleKey)) (funext fun k => ?_)
  rw [ProbOracleComp.eval_run_interpret_eq_runWith, PMF.map]
  rfl

end Typed

/-! ### Canonical word codec and asymptotic CPA security -/

/-- Parse one framed prefix `frame w` from `v`, returning `some (w, u)` when `frame w ++ u = v`
and `none` when `v` does not begin with a complete frame. -/
@[expose]
def decodeFramed (v : List Bool) : Option (List Bool × List Bool) :=
  let w := unframe v
  let u := dropFrame v
  if frame w ++ u == v then some (w, u) else none

/-- `decodeFramed` succeeds with `(w, u)` if and only if `frame w ++ u = v`. -/
@[simp]
theorem decodeFramed_eq_some_iff (v w u : List Bool) :
    decodeFramed v = some (w, u) ↔ frame w ++ u = v := by
  unfold decodeFramed
  dsimp only
  split_ifs with h
  · rw [beq_iff_eq] at h
    simp only [Option.some.injEq, Prod.mk.injEq]
    refine ⟨?_, fun hv => ?_⟩
    · rintro ⟨rfl, rfl⟩
      exact h
    · rw [← hv, unframe_frame_append, dropFrame_frame_append]
      exact ⟨rfl, rfl⟩
  · rw [beq_iff_eq] at h
    simp only [false_iff]
    intro hv
    apply h
    rw [← hv, unframe_frame_append, dropFrame_frame_append]

/-- Canonical parameter-free word codec for `D = Unit` nonce-based CPA queries:
encodes `(pair, (), nonce)` on the single word channel as
`frame pair.msg₀ ++ frame pair.msg₁ ++ nonce`, decodes two framed message prefixes followed by the
raw `nonce` suffix via `decodeFramed`, and encodes `Option (List Bool)` replies with
`encOption encBits` (`none ↦ []`, `some ct ↦ true :: ct`). -/
@[expose]
def unitCPACodec :
    OracleCodec Unit (MessagePair (List Bool) × Unit × List Bool)
      (fun _ => Option (List Bool)) where
  encodeQuery
    | (pair, _, nonce) => ((), frame pair.msg₀ ++ frame pair.msg₁ ++ nonce)
  decodeQuery request :=
    match decodeFramed request.2 with
    | some (m₀, rest) =>
      match decodeFramed rest with
      | some (m₁, nonce) => some (⟨m₀, m₁⟩, (), nonce)
      | none => none
    | none => none
  decodeQuery_eq_some_iff := by
    rintro ⟨⟨⟩, word⟩ ⟨⟨m₀, m₁⟩, ⟨⟩, nonce⟩
    constructor
    · intro h
      cases h₁ : decodeFramed word with
      | none => simp [h₁] at h
      | some p₁ =>
        rcases p₁ with ⟨w₀, rest⟩
        cases h₂ : decodeFramed rest with
        | none => simp [h₁, h₂] at h
        | some p₂ =>
          rcases p₂ with ⟨w₁, rem⟩
          simp only [h₁, h₂, Option.some.injEq, Prod.mk.injEq, MessagePair.mk.injEq,
            true_and] at h
          rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
          rw [decodeFramed_eq_some_iff] at h₁ h₂
          simp [← h₁, ← h₂, List.append_assoc]
    · rintro ⟨_, rfl⟩
      have h₁ : decodeFramed (frame m₀ ++ (frame m₁ ++ nonce)) = some (m₀, frame m₁ ++ nonce) := by
        rw [decodeFramed_eq_some_iff]
      have h₂ : decodeFramed (frame m₁ ++ nonce) = some (m₁, nonce) := by
        rw [decodeFramed_eq_some_iff]
      simp [List.append_assoc, h₁, h₂]
  encodeReply _ := encOption encBits

/-- Adaptive chosen-plaintext security for a family of word-level nonce-based ciphers without
associated data ([BonehShoup2023], Section 5.5, Attack Game 5.3 and Definition 5.3, printed p. 202),
against uniform strict `IsOraclePPT encBool` distinguishers adapted via `unitCPACodec`. -/
@[expose]
def INDCPA (E : ℕ → NonceCipher (List Bool) (List Bool) Unit (List Bool) (List Bool))
    (sampleKey : ℕ → ProbComp (List Bool))
    (valid : ℕ → List Bool → List Bool → Bool)
    (validNonce : ℕ → List Bool → Bool) : Prop :=
  Game.Indistinguishable
    (fun W n => ProbComp.eval
      ((E n).cpaExperiment (sampleKey n) (valid n) (validNonce n)
        (unitCPACodec.adapt (W n [])) false))
    (fun W n => ProbComp.eval
      ((E n).cpaExperiment (sampleKey n) (valid n) (validNonce n)
        (unitCPACodec.adapt (W n [])) true))
    (IsOraclePPT encBool)

end NonceCipher

end Cslib.Crypto
