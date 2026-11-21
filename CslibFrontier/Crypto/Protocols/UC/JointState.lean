/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.UC.MultiSession

/-!
# Lazy multi-session ideal functionality for joint-state UC

This module defines the named data structures (`SubSessionInput`, `SubSessionBackdoor`,
`MultiSessionState`) and the lazy multi-session ideal functionality
`IdealFunctionality.multiSession` (`F̂`), following Section 3 ("The Multi-session Extension of an
Ideal Functionality" and Theorem 1 (Universal Composition with Joint State)) of
[CanettiRabin2003] (CRYPTO 2003, LNCS 2729, pp. 265–281), adapted to static corruptions and this
library's call-bounded, pull-only UC execution model (see `Cslib.Crypto.Protocols.UC.Emulates`
for the call-budget model vs. PPT ITMs).

The generic lazy-vs-eager parallel-package initialization theorem (`SSP.parFinLazy`,
`SSP.run_parFinLazy_eq_parFin`) lives separately in `CslibFrontier.Crypto.Protocols.SSP.ParFinLazy`
(`SSP.Basic` supplies `UC.Machine` via `UC.Linking`), so SSP callers can import the bridge
without importing the UC ideal-functionality or execution modules.

## Modelling decisions and differences from [CanettiRabin2003]

1. **Named structures (zero projection chains).** `SubSessionInput`, `SubSessionBackdoor`, and
   `MultiSessionState` replace raw nested products and options.
2. **Lazy multi-session extension `F.multiSession` ([CanettiRabin2003], §3, "The Multi-session
   Extension of an Ideal Functionality").** For any `[DecidableEq SSID]`,
   `IdealFunctionality.multiSession SSID F` stores `(secParam, corrupted, sessions)` and creates a
   fresh copy of `F` with `F.init secParam corrupted` on the first party input or backdoor query
   for a given `ssid`, keeping distinct `ssid`s independent.
3. **Pull-model interface and scheduling differences.** In [CanettiRabin2003], §3, "The
   Multi-session Extension of an Ideal Functionality", whenever a copy of `F` sends `(ssid, v)` to
   some party `Pi`, `F̂` sends `(sid, ssid, v)` to `Pi` and sends `ssid` to the adversary. Here,
   `IdealFunctionality.multiSession` returns an untagged `Option SubOut` on the selected pull query
   `SubSessionInput SSID SubIn`, and provides an explicitly queried backdoor interface
   (`SubSessionBackdoor SSID BackQ`) returning `BackR` (exposing no raw copy state) rather than
   sending adversary notifications on honest-party activations or outputs. Because the interfaces,
   scheduling, and call-bounded vs. PPT ITM resource models differ, no implication between
   `Realizes` for this pull API and the source premise is claimed here.
4. **Scope and joint state vs. global setup.** Joint state here is internal to a single subroutine
   protocol, not a GUC/EUC global setup shared outside it. Relabelling (§3, "The Composition
   Operation", and the proof of Theorem 1, definition of `π̃`) and joint-state composition remain
   open.

## Main definitions

* `Cslib.Crypto.Protocols.UC.SubSessionInput`, `Cslib.Crypto.Protocols.UC.SubSessionBackdoor`,
  `Cslib.Crypto.Protocols.UC.MultiSessionState`: named data structures for multi-session
  functionalities.
* `Cslib.Crypto.Protocols.UC.IdealFunctionality.multiSession`: lazy multi-session extension `F̂`.

## References

* [R. Canetti and T. Rabin, *Universal Composition with Joint State*][CanettiRabin2003], CRYPTO
  2003, LNCS 2729, pp. 265–281 (§3, "The Composition Operation"; §3, "The Multi-session Extension
  of an Ideal Functionality"; Theorem 1 (Universal Composition with Joint State); and the proof of
  Theorem 1, definition of `π̃`).
-/

public section

namespace Cslib.Crypto.Protocols.UC

/-! ### Named structures and lazy multi-session functionality -/

/-- A party input to a multi-session functionality or joint-state protocol: sub-session `ssid`
with value `input` ([CanettiRabin2003], §3, "The Multi-session Extension of an Ideal
Functionality", the `(ssid, v)` part of `(sid, ssid, v)`). -/
structure SubSessionInput (SSID SubIn : Type) : Type where
  /-- Sub-session identifier. -/
  ssid : SSID
  /-- Party input (or poll token) for sub-session `ssid`. -/
  input : SubIn
  deriving DecidableEq

/-- An adversary backdoor query to copy `ssid` of the multi-session functionality. -/
structure SubSessionBackdoor (SSID BackQ : Type) : Type where
  /-- Target sub-session identifier. -/
  ssid : SSID
  /-- Backdoor query for sub-session `ssid`. -/
  query : BackQ
  deriving DecidableEq

/-- State of `F.multiSession`: the security parameter and corrupted set recorded at invocation
(so that copies can be created later) and the lazily created copies. -/
structure MultiSessionState (n : ℕ) (SSID FState : Type) : Type where
  /-- Security parameter fixed at functionality invocation. -/
  secParam : ℕ
  /-- Static corruption set fixed at functionality invocation. -/
  corrupted : Finset (Fin n)
  /-- Lazily initialized per-session states (`none` until first message). -/
  sessions : SSID → Option FState

/-- Multi-session extension `F̂` of an ideal functionality `F` for any `[DecidableEq SSID]`:
creates a fresh copy of `F` with `F.init secParam corrupted` on the first party input or backdoor
query for `ssid`, and activates that copy ([CanettiRabin2003], §3, "The Multi-session Extension of
an Ideal Functionality"). Unlike the source's `F̂` (which sends `(sid, ssid, v)` to `Pi` and sends
`ssid` to the adversary when a copy sends `(ssid, v)`), this pull API returns an untagged
`Option SubOut` on the selected pull and
provides an explicitly queried backdoor interface (`SubSessionBackdoor SSID BackQ`) returning
`BackR`, exposing no raw copy state. -/
@[expose] def IdealFunctionality.multiSession {n : ℕ} {SubIn SubOut BackQ BackR : Type}
    (SSID : Type) [DecidableEq SSID]
    (F : IdealFunctionality n SubIn SubOut BackQ BackR) :
    IdealFunctionality n (SubSessionInput SSID SubIn) SubOut
      (SubSessionBackdoor SSID BackQ) BackR where
  State := MultiSessionState n SSID F.State
  init κ C := pure { secParam := κ, corrupted := C, sessions := fun _ => none }
  onInput i req s := do
    let fState ← match s.sessions req.ssid with
      | some st => pure st
      | none => F.init s.secParam s.corrupted
    let (out, fState') ← (F.onInput i req.input).run fState
    return (out, { s with sessions := Function.update s.sessions req.ssid (some fState') })
  onBackdoor req s := do
    let fState ← match s.sessions req.ssid with
      | some st => pure st
      | none => F.init s.secParam s.corrupted
    let (resp, fState') ← (F.onBackdoor req.query).run fState
    return (resp, { s with sessions := Function.update s.sessions req.ssid (some fState') })

end Cslib.Crypto.Protocols.UC
