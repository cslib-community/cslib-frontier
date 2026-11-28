/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.AnonymousToken.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Extracted certified-state credit accounting

An ACT state carries a nullifier, a context, a committed credit `t`, and an issuer-granted refund
`x`. Its effective balance is `t + x`; spending `d` replaces it with committed credit
`t + x - d` and a newly granted refund ([VOLEACT2026], Overview and Spending). `target` composes
commitment of `(nullifier, context, credit)` with certification of its refund. It can be supplied
directly to the structured-target experiment and explicit reductions in `AnonymousToken.Basic`.

The ledger here is extracted certified-state bookkeeping: it knows the semantic states issued
by the authority. Its `spend` operation looks up the presented state, checks the range, atomically
records the spent nullifier, and adds the successor. `spend_conserves` proves exact conservation
of issued credit, paid credit, and the sum of remaining certificates. Repeated nullifiers need
not be fresh on issuance: they strand certificates, since every subsequent spend with that
nullifier is rejected. Counting stranded certificates only overestimates redeemable credit.
The arithmetic uses natural numbers; the protocol's upper bounds on credit are additional
restrictions on this ledger's permitted transitions.

This is an original accounting step, not a public implementation of the private ACT verifier.
Relating a real adaptive proof transcript to this extracted ledger requires witness extraction
and semantic certification; the explicit certification reduction is in `Basic`, while the
full VOLE/random-oracle extraction and runtime certificates remain tracked in issue #7068.

## Main definitions

* `Note`, `Note.balance`, `target`: semantic ACT credit state, effective balance, and two-stage
  commitment/tag target encoder.
* `Ledger`, `Ledger.empty`, `Ledger.outstanding`, `Ledger.Conserves`, `Ledger.fund`,
  `Ledger.spend`: extracted-state credit ledger, conservation predicate, and atomic transitions.

## Main results

* `Ledger.empty_conserves`: the initial empty ledger conserves credit.
* `Ledger.fund_conserves`: granting a state adds exactly its effective balance to the budget.
* `Ledger.spend_conserves`: accepted spending adds only the newly granted refund to the budget.
* `Ledger.spend_eq_none_of_spent`: even a different state with a used nullifier cannot be spent.
* `Ledger.Conserves.paid_le_granted`: every conserving ledger has paid at most the granted credit.

## References

* [*VOLE-ACT*][VOLEACT2026], Overview (`#overview`), Tag (`#tag`), and Spending (`#spending`).
-/

@[expose] public section

namespace Cslib.Crypto.AnonymousToken.Credit

/-- The complete semantic ACT state, including the separately granted refund. -/
structure Note (Nullifier Context : Type) where
  /-- The identifier checked against the spent-nullifier set. -/
  nullifier : Nullifier
  /-- The application context bound into the state. -/
  context : Context
  /-- Credit committed by the holder before the current refund is granted. -/
  credit : Nat
  /-- Additional credit granted by the issuer and certified with the commitment. -/
  refund : Nat
  deriving DecidableEq

variable {Nullifier Context Opening Commitment Target : Type}

/-- The amount a certified state authorizes, including its refund. -/
def Note.balance (note : Note Nullifier Context) : Nat := note.credit + note.refund

/-- Compose the ACT commitment and refund-binding target encoder. A commitment need not accept
the refund as part of its message: `tag` binds that separately granted amount to the commitment. -/
def target (commit : Nullifier → Context → Nat → Opening → Commitment)
    (tag : Commitment → Nat → Target) (note : Note Nullifier Context) (opening : Opening) :
    Target := tag (commit note.nullifier note.context note.credit opening) note.refund

/-- Bookkeeping after extraction: issued states not yet consumed, all spent nullifiers, and the
total granted and paid amounts. Several available states may share a nullifier. -/
structure Ledger (Nullifier Context : Type) where
  /-- Issued certificates that have not been selected for consumption. -/
  available : List (Note Nullifier Context)
  /-- Nullifiers consumed atomically by accepted spends. -/
  spent : List Nullifier
  /-- Initial funding plus every issuer-granted refund. -/
  granted : Nat
  /-- Total debit accepted by the application. -/
  paid : Nat
  deriving DecidableEq

namespace Ledger

/-- The ledger before any funding or spending. -/
def empty : Ledger Nullifier Context := ⟨[], [], 0, 0⟩

/-- Total credit in remaining certificates. A certificate with a spent nullifier is included;
such a certificate cannot be redeemed, so this is an upper bound on redeemable credit. -/
def outstanding (ledger : Ledger Nullifier Context) : Nat :=
  (ledger.available.map Note.balance).sum

/-- All granted credit is either paid or still represented in a remaining certificate. -/
def Conserves (ledger : Ledger Nullifier Context) : Prop :=
  ledger.paid + ledger.outstanding = ledger.granted

instance (ledger : Ledger Nullifier Context) : Decidable ledger.Conserves :=
  inferInstanceAs (Decidable (ledger.paid + ledger.outstanding = ledger.granted))

/-- Register an issuer-funded state. Its entire effective balance is new authorized funding. -/
def fund (ledger : Ledger Nullifier Context) (note : Note Nullifier Context) :
    Ledger Nullifier Context :=
  { ledger with
    available := note :: ledger.available
    granted := ledger.granted + note.balance }

/-- Consume a known certified state once and create its change state. The nullifier check and
the update occur in the same transition. An issuer may choose any new nullifier; choosing one
already spent creates a stranded state rather than authorizing a replay. -/
def spend [DecidableEq Nullifier] [DecidableEq Context] (ledger : Ledger Nullifier Context)
    (old : Note Nullifier Context) (nextNullifier : Nullifier) (debit refund : Nat) :
    Option (Ledger Nullifier Context) :=
  if old ∈ ledger.available ∧ old.nullifier ∉ ledger.spent ∧ debit ≤ old.balance then
    some
      { available := ⟨nextNullifier, old.context, old.balance - debit, refund⟩ ::
          ledger.available.erase old
        spent := old.nullifier :: ledger.spent
        granted := ledger.granted + refund
        paid := ledger.paid + debit }
  else none

/-- The empty ledger has no unpaid or granted credit. -/
@[simp] theorem empty_conserves : (empty : Ledger Nullifier Context).Conserves := by
  simp [Conserves, outstanding, empty]

/-- Registering funding preserves conservation, including when its nullifier was already used. -/
theorem fund_conserves {ledger : Ledger Nullifier Context} (hledger : ledger.Conserves)
    (note : Note Nullifier Context) : (ledger.fund note).Conserves := by
  simp only [Conserves, outstanding, fund, List.map_cons, List.sum_cons] at hledger ⊢
  omega

/-- An accepted spend preserves credit exactly: the old state finances the debit and its change;
only the new issuer refund is added to the total grant. Membership and range checks are executed
by `spend`, rather than supplied as assumptions about the adversary. -/
theorem spend_conserves [DecidableEq Nullifier] [DecidableEq Context]
    {ledger next : Ledger Nullifier Context} {old : Note Nullifier Context}
    {nextNullifier : Nullifier} {debit refund : Nat} (hledger : ledger.Conserves)
    (hstep : ledger.spend old nextNullifier debit refund = some next) : next.Conserves := by
  unfold spend at hstep
  split at hstep
  · rename_i hchecks
    have hnext := Option.some.inj hstep
    subst next
    have herase := List.sum_map_erase Note.balance hchecks.1
    have hrange := hchecks.2.2
    simp only [Conserves, outstanding, List.map_cons, List.sum_cons] at hledger ⊢
    change ledger.paid + debit +
      (old.balance - debit + refund +
        ((ledger.available.erase old).map Note.balance).sum) = ledger.granted + refund
    omega
  · simp at hstep

/-- A spent nullifier is rejected even if the ledger contains another certificate with that
nullifier, or the issuer later funds such a certificate. -/
theorem spend_eq_none_of_spent [DecidableEq Nullifier] [DecidableEq Context]
    (ledger : Ledger Nullifier Context) (old : Note Nullifier Context)
    (nextNullifier : Nullifier) (debit refund : Nat) (hspent : old.nullifier ∈ ledger.spent) :
    ledger.spend old nextNullifier debit refund = none := by
  simp [spend, hspent]

/-- The conservation invariant bounds accepted payouts by all issuer-granted credit. -/
theorem Conserves.paid_le_granted {ledger : Ledger Nullifier Context}
    (hledger : ledger.Conserves) : ledger.paid ≤ ledger.granted := by
  exact hledger ▸ Nat.le_add_right ledger.paid ledger.outstanding

end Ledger

end Cslib.Crypto.AnonymousToken.Credit
