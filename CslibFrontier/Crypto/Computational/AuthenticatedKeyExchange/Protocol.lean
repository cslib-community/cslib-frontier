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

## Main definitions

* `Cslib.Crypto.AKE.Role`: session role (`left` or `right`).
* `Cslib.Crypto.AKE.Phase`: execution status of an instance (`running`, `aborted`, or `finished`).
* `Cslib.Crypto.AKE.StepInput`, `Cslib.Crypto.AKE.StepOutput`: input and output records of a
  session key establishment step, with encodings `encStepInput` and `encStepOutput`.
* `Cslib.Crypto.AKE.TTPInput`, `Cslib.Crypto.AKE.TTPOutput`: input and output records of TTP
  queries, with encodings `encTTPInput` and `encTTPOutput`.
* `Cslib.Crypto.AKE.Protocol`: AKE protocol record with efficiency certificates and session-key
  length invariant.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 21.9, pp. 885–886.
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
pp. 885–886), packaged with uniform strict polynomial-time / `IsPPTOn` certificates and the
session-key length condition `k ∈ 𝒦` where `𝒦 = {0, 1}^{keyLength n}`. -/
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

end Cslib.Crypto.AKE
