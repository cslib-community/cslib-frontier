/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.PPT
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import Mathlib.Data.FinEnum

/-!
# Authenticated key exchange: protocol syntax

An authenticated key exchange (AKE) protocol ([BonehShoup2023], §21.9, p. 885) specifies a key
space—modeled here at security parameter `n` as all bit strings of length `keyLength n`—together
with algorithms for trusted third party (TTP) initialization, honest and corrupt user registration,
online TTP queries, and session key establishment steps.

All runtime values are bit strings (`List Bool`), and every algorithm carries a uniform strict
polynomial-time or `IsPPTOn` efficiency certificate over explicit structure encodings. Honest
registration is modeled as one joint step (`registerHonest`), whereas corrupt registration and
key establishment proceed step by step through explicit TTP and instance states.

A certificate for each call alone is not enough. It admits a TTP that doubles its state on every
call, and a TTP that echoes an arbitrarily long request; in both, the work and the replies are
not bounded by any polynomial in the security parameter and the number of calls. The book
excludes both:

* the TTP must be an efficient interface ([BonehShoup2023], footnote 1 on p. 885, and
  Definition 2.12, p. 33), whose total running time is polynomial in the security parameter and
  the number of interactions;
* the configuration of a running protocol instance is bounded by a fixed polynomial in the
  security parameter (§18.1.1, p. 718), which names the doubling as the reason.

A `Protocol` therefore carries a size bound `sizeBound`, computable in polynomial time in unary
and so polynomial in `n`. The bound limits three things:

* **TTP state.** Each TTP call lengthens the TTP state by at most `sizeBound n`.
* **Long-term keys and instance states.** Every long-term key that honest registration outputs,
  and every state that a session step outputs, has length at most `sizeBound n`.
* **Adversary words.** The challenger refuses any query that would hand a protocol algorithm a
  user identity or message longer than `sizeBound n` (`Protocol.TooLong`), as it refuses other
  disallowed queries.

Every input of a TTP call then has length polynomial in `n` and the number of earlier calls, and
every input of a session step has length polynomial in `n`. So the TTP runs in time polynomial in
`n` and the number of interactions, as Definition 2.12 requires, and each session step runs in
time polynomial in `n`, as §18.1.1 requires. A certificate that running the whole experiment is
PPT is not proved here.

The resulting model differs from the book's, so `Protocol.StaticallySecure` is a milestone toward
Definition 21.1, not that definition:

* **The guard is part of the semantics.** Over-long words are refused before any protocol
  algorithm runs, whereas the book's interface reads as much of a word as its time budget allows.
  Security behind the guard need not be security of the unguarded algorithms.
* **The bounds are narrower than Definition 2.12.** Each call may add at most `sizeBound n` to the
  TTP state, whereas Definition 2.12 bounds only the cumulative running time, and so also admits
  interfaces whose growth per call increases with the number of earlier calls. The bound is also
  worst-case, where Definition 2.12 lets it fail with negligible probability.
* **Rounds are unbounded.** The polynomial terminal-round condition of §18.1.1 is not required: a
  session may stay `running` forever.

## Main definitions

* `Cslib.Crypto.AKE.Role`: session role (`left` or `right`).
* `Cslib.Crypto.AKE.Phase`: execution status of an instance (`running`, `aborted`, or `finished`).
* `Cslib.Crypto.AKE.StepInput`, `Cslib.Crypto.AKE.StepOutput`: input and output records of a
  session key establishment step, with encodings `encStepInput` and `encStepOutput`.
* `Cslib.Crypto.AKE.TTPInput`, `Cslib.Crypto.AKE.TTPOutput`: input and output records of TTP
  queries, with encodings `encTTPInput` and `encTTPOutput`.
* `Cslib.Crypto.AKE.Protocol`: AKE protocol record with efficiency certificates, session-key
  length invariant and size bound.
* `Cslib.Crypto.AKE.Protocol.TooLong`: a word longer than the size bound, which the challenger
  refuses to hand to a protocol algorithm.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 21.9, pp. 885–886; Definition 2.12, p. 33; Section 18.1.1, p. 718.
-/

public section

namespace Cslib.Crypto.AKE

open Probability Turing.MultiTapeTM

/-- Role assigned to an honest user instance to break symmetry ([BonehShoup2023], §21.9,
p. 885). -/
inductive Role where
  /-- Initiator / left role. -/
  | left
  /-- Responder / right role. -/
  | right
  deriving DecidableEq, Repr

instance : FinEnum Role := FinEnum.ofList [.left, .right] (by rintro (_ | _) <;> decide)

/-- Status of a session key establishment instance ([BonehShoup2023], §21.9, pp. 885–886). -/
inductive Phase where
  /-- The instance has not yet terminated and still accepts incoming messages. -/
  | running
  /-- The instance aborted without deriving a session key. -/
  | aborted
  /-- The instance terminated successfully with a partner identity and session key. -/
  | finished
  deriving DecidableEq, Repr

instance : FinEnum Phase :=
  FinEnum.ofList [.running, .aborted, .finished] (by rintro (_ | _ | _) <;> decide)

/-- Input to one session key establishment step of an honest user instance. -/
structure StepInput where
  /-- Unary security parameter `n`. -/
  parameter : ℕ
  /-- Identity of the honest user owning the instance. -/
  user : List Bool
  /-- Long-term secret key established for `user` at registration. -/
  longTermKey : List Bool
  /-- Symmetry-breaking role of the instance. -/
  role : Role
  /-- Current local state word of the instance. -/
  state : List Bool
  /-- Incoming protocol message word (ignored on a role's initial outgoing flow). -/
  message : List Bool
  deriving DecidableEq, Repr

/-- Encoding of `StepInput` as its fields in declaration order. -/
enc_structure encStepInput : StepInput where
  parameter : encUnary,
  user : encBits,
  longTermKey : encBits,
  role : (encFinEnum Role),
  state : encBits,
  message : encBits

/-- Output of one session key establishment step of an honest user instance. -/
structure StepOutput where
  /-- Updated local state word of the instance. -/
  state : List Bool
  /-- Outgoing protocol message word. -/
  message : List Bool
  /-- Updated instance status (`running`, `aborted`, or `finished`). -/
  phase : Phase
  /-- Partner identity, read when `phase = .finished`. -/
  partner : List Bool
  /-- Derived session key, read when `phase = .finished`. -/
  key : List Bool
  deriving DecidableEq, Repr

/-- Encoding of `StepOutput` as its fields in declaration order. -/
enc_structure encStepOutput : StepOutput where
  state : encBits,
  message : encBits,
  phase : (encFinEnum Phase),
  partner : encBits,
  key : encBits

/-- Input to a TTP algorithm (honest registration, corrupt registration, or online TTP step). -/
structure TTPInput where
  /-- Unary security parameter `n`. -/
  parameter : ℕ
  /-- Current internal state word of the TTP. -/
  ttp : List Bool
  /-- User identity relevant to the query (unused for online TTP steps). -/
  user : List Bool
  /-- Incoming message word to the TTP (unused for honest registration). -/
  message : List Bool
  deriving DecidableEq, Repr

/-- Encoding of `TTPInput` as its fields in declaration order. -/
enc_structure encTTPInput : TTPInput where
  parameter : encUnary,
  ttp : encBits,
  user : encBits,
  message : encBits

/-- Output of a TTP algorithm. -/
structure TTPOutput where
  /-- Updated internal state word of the TTP. -/
  ttp : List Bool
  /-- Returned word: the long-term secret key for honest registration, or outgoing message. -/
  output : List Bool
  deriving DecidableEq, Repr

/-- Encoding of `TTPOutput` as its fields in declaration order. -/
enc_structure encTTPOutput : TTPOutput where
  ttp : encBits,
  output : encBits

/-- Syntactic specification of an authenticated key exchange protocol ([BonehShoup2023], §21.9,
pp. 885–886), packaged with uniform strict polynomial-time / `IsPPTOn` certificates, the
session-key length condition `k ∈ 𝒦` where `𝒦 = {0, 1}^{keyLength n}`, and the size bound that
makes the TTP an efficient interface (Definition 2.12, p. 33) and keeps instance configurations
polynomial in `n` (§18.1.1, p. 718). The module documentation compares this bound with the
book's conditions. -/
structure Protocol where
  /-- Session key length as a function of the security parameter. -/
  keyLength : ℕ → ℕ
  /-- Initializes the TTP internal state at security parameter `n`. -/
  ttpInit : ℕ → ProbComp (List Bool)
  /-- Joint honest registration protocol, updating TTP state and producing `U.ltk`. -/
  registerHonest : TTPInput → ProbComp TTPOutput
  /-- One interactive step of corrupt user registration directly with the TTP. -/
  registerCorrupt : TTPInput → ProbComp TTPOutput
  /-- Online TTP message handler (`deliverTTP`). -/
  ttpStep : TTPInput → ProbComp TTPOutput
  /-- One step of the interactive session key establishment algorithm. -/
  step : StepInput → ProbComp StepOutput
  /-- `keyLength` is computable in polynomial time in unary. -/
  keyLength_polyTime : ComputableInPolyTime keyLength encUnary encUnary
  /-- TTP initialization is uniform strict PPT. -/
  ttpInit_ppt : IsPPTOn encUnary encBits ttpInit
  /-- Honest registration is uniform strict PPT. -/
  registerHonest_ppt : IsPPTOn encTTPInput encTTPOutput registerHonest
  /-- Corrupt registration is uniform strict PPT. -/
  registerCorrupt_ppt : IsPPTOn encTTPInput encTTPOutput registerCorrupt
  /-- Online TTP processing is uniform strict PPT. -/
  ttpStep_ppt : IsPPTOn encTTPInput encTTPOutput ttpStep
  /-- Session key establishment steps are uniform strict PPT. -/
  step_ppt : IsPPTOn encStepInput encStepOutput step
  /-- Every finished step produces a key in `𝒦`, i.e., of length `keyLength input.parameter`. -/
  key_length : ∀ input, ∀ out ∈ (ProbComp.eval (step input)).support,
    out.phase = .finished → out.key.length = keyLength input.parameter
  /-- Size bound of the protocol at security parameter `n`: the most a TTP call may add to the TTP
  state, the length of every long-term key and instance state, and the length of every user
  identity and message the challenger hands to a protocol algorithm. -/
  sizeBound : ℕ → ℕ
  /-- `sizeBound` is computable in polynomial time in unary, so `sizeBound n` is polynomial in
  `n`. -/
  sizeBound_polyTime : ComputableInPolyTime sizeBound encUnary encUnary
  /-- Honest registration lengthens the TTP state by at most `sizeBound n`. -/
  registerHonest_ttp_length : ∀ input, ∀ out ∈ (ProbComp.eval (registerHonest input)).support,
    out.ttp.length ≤ input.ttp.length + sizeBound input.parameter
  /-- Honest registration outputs a long-term key of length at most `sizeBound n`. -/
  registerHonest_output_length : ∀ input, ∀ out ∈ (ProbComp.eval (registerHonest input)).support,
    out.output.length ≤ sizeBound input.parameter
  /-- Corrupt registration lengthens the TTP state by at most `sizeBound n`. -/
  registerCorrupt_ttp_length : ∀ input, ∀ out ∈ (ProbComp.eval (registerCorrupt input)).support,
    out.ttp.length ≤ input.ttp.length + sizeBound input.parameter
  /-- An online TTP step lengthens the TTP state by at most `sizeBound n`. -/
  ttpStep_ttp_length : ∀ input, ∀ out ∈ (ProbComp.eval (ttpStep input)).support,
    out.ttp.length ≤ input.ttp.length + sizeBound input.parameter
  /-- Every instance state a step outputs has length at most `sizeBound n`. -/
  step_state_length : ∀ input, ∀ out ∈ (ProbComp.eval (step input)).support,
    out.state.length ≤ sizeBound input.parameter

namespace Protocol

/-- A word is too long for `P` at security parameter `n` when it has more than `P.sizeBound n`
bits. The challenger refuses any query that would hand such a user identity or message to a
protocol algorithm. -/
@[expose] def TooLong (P : Protocol) (n : ℕ) (w : List Bool) : Prop :=
  P.sizeBound n < w.length

instance (P : Protocol) (n : ℕ) (w : List Bool) : Decidable (P.TooLong n w) :=
  inferInstanceAs (Decidable (_ < _))

@[simp] theorem not_tooLong_nil (P : Protocol) (n : ℕ) : ¬ P.TooLong n [] := by
  simp [TooLong]

end Protocol

end Cslib.Crypto.AKE
