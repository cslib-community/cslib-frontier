/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Physical clock synchronization and time-shift indistinguishability

Deterministic round-based message-passing synchronization of drift-free physical clocks on the
complete network of processes `P`, following the model of
[Lundelius and Lynch][LundeliusLynch1984].

Each process `p : P` has a drift-free hardware clock whose reading at real time `t : K` is
`hardwareClock c p t = t + c p`, where `c : P → K` is an unknown initial offset vector. Processes
have no direct access to real time `t`: in each round `r < R`, process `p` schedules outgoing
messages at chosen local hardware clock readings `τ` and records its own local hardware clock
reading upon receiving each incoming message. When `p` sends a message at local reading `τ` and
the message experiences transit delay `δ r p q`, it arrives at `q` at local reading
`arrivalReading c δ r p q τ = τ + δ r p q + c q - c p`.

Because `Protocol` passes full local observation histories (`LocalView P K r`) in every round, any
deterministic `R`-round message-passing protocol with arbitrary local states and message payloads
is represented without loss of generality: a process's state and outgoing payloads after `r` rounds
are deterministic functions of its identity and its `LocalView P K r`.

The central structural property of the model is **time-shift indistinguishability**
(`localView_shift_eq`, `adj_shift_eq`): shifting hardware offsets to
`shiftOffsets c s p = c p + s p` and transit delays to `shiftDelays δ s r p q = δ r p q + s p - s q`
leaves every arrival reading and hence every process's `LocalView` and computed adjustment `adj`
identically unchanged, while shifting each synchronized clock offset `syncOffset` by `+ s p`
(`syncOffset_shift_eq`).

This file also provides the midpoint-delay offset estimator `estDiff` and its error bound
`abs_add_estDiff_sub_le`, shared by the optimal fault-free averaging protocol in
`CslibFrontier.Computability.Distributed.ClockSync.LundeliusLynch` and the Byzantine
trimmed-midpoint convergence step in
`CslibFrontier.Computability.Distributed.ClockSync.ByzantineSync`.

## Main definitions

* `Cslib.Distributed.ClockSync.hardwareClock`: drift-free hardware clock reading `t + c p`.
* `Cslib.Distributed.ClockSync.arrivalReading`: local clock reading at `q` when a message sent by
  `p` at local reading `τ` arrives after transit delay `δ r p q`.
* `Cslib.Distributed.ClockSync.ValidDelays`: transit delays lie in `[d_min, d_max]`.
* `Cslib.Distributed.ClockSync.LocalView`: full local observation history after `r` rounds.
* `Cslib.Distributed.ClockSync.Protocol`: deterministic `R`-round clock synchronization protocols.
* `Cslib.Distributed.ClockSync.Protocol.localView`, `Protocol.adj`, `Protocol.syncOffset`:
  protocol execution, local clock adjustment, and synchronized clock offset `c p + adj p`.
* `Cslib.Distributed.ClockSync.AchievesSkew`: worst-case synchronized skew at most `γ` across all
  hardware offsets `c` and valid delays in `[d_min, d_max]`.
* `Cslib.Distributed.ClockSync.shiftOffsets`, `shiftDelays`: real-time shift transformation on
  hardware offsets and message transit delays.
* `Cslib.Distributed.ClockSync.estDiff`: midpoint-delay estimator of `c q - c p` from arrival
  timestamps of local-time-`0` broadcasts.

## Main results

* `Cslib.Distributed.ClockSync.localView_shift_eq`: time-shift indistinguishability of local views
  across all `r ≤ R` rounds.
* `Cslib.Distributed.ClockSync.adj_shift_eq`: time-shift invariance of protocol adjustments.
* `Cslib.Distributed.ClockSync.abs_add_estDiff_sub_le`: midpoint-delay estimation approximates
  each sender's hardware offset within `(d_max - d_min) / 2`.

## References

* [J. Lundelius, N. Lynch, *An upper and lower bound for clock synchronization*][LundeliusLynch1984]
-/

public section

namespace Cslib.Distributed.ClockSync

universe u v

section Model

variable {P : Type u} {K : Type v}

/-- The local reading `t + c p` of process `p`'s drift-free hardware clock at real time `t` under
initial hardware clock offsets `c : P → K`. -/
@[expose] def hardwareClock [Add K] (c : P → K) (p : P) (t : K) : K :=
  t + c p

/-- The local hardware clock reading observed at recipient `q` when a round-`r` message sent by
`p` at `p`'s local clock reading `τ` arrives after real-time transit delay `δ r p q`. -/
@[expose] def arrivalReading [AddCommGroup K] (c : P → K) (δ : ℕ → P → P → K) (r : ℕ) (p q : P)
    (τ : K) : K :=
  τ + δ r p q + c q - c p

/-- If `p` sends a message at real time `t` when its hardware clock reads `τ`, and the message has
transit delay `δ r p q`, then `q`'s hardware clock at arrival time `t + δ r p q` reads
`arrivalReading c δ r p q τ`. -/
theorem hardwareClock_arrival [AddCommGroup K] (c : P → K) (δ : ℕ → P → P → K) (r : ℕ) (p q : P)
    {t τ : K} (ht : hardwareClock c p t = τ) :
    hardwareClock c q (t + δ r p q) = arrivalReading c δ r p q τ := by
  rw [← ht]
  simp only [hardwareClock, arrivalReading]
  abel

/-- Every round's message transit delays lie within `[d_min, d_max]`. -/
@[expose] def ValidDelays [LE K] (d_min d_max : K) (δ : ℕ → P → P → K) : Prop :=
  ∀ r p q, d_min ≤ δ r p q ∧ δ r p q ≤ d_max

/-- The full local observation history of a process after `r` synchronous message-passing rounds.

Before communication begins (`init`), a process has observed no arrival timestamps. After round
`r + 1` (`step prev arrival relayed`), a process retains its prior view `prev`, records for each
sender `q : P` its own local clock reading `arrival q` upon receiving `q`'s round-`r` message, and
receives `q`'s relayed prior view `relayed q`. -/
inductive LocalView (P : Type u) (K : Type v) : ℕ → Type (max u v)
  | init : LocalView P K 0
  | step {r : ℕ} (prev : LocalView P K r) (arrival : P → K)
      (relayed : P → LocalView P K r) : LocalView P K (r + 1)

/-- Extract the vector of arrival timestamps observed in the final round of a non-empty view. -/
@[expose] def LocalView.lastArrival {r : ℕ} : LocalView P K (r + 1) → P → K
  | .step _ arrival _ => arrival

/-- `LocalView.lastArrival` returns the arrival vector of the most recent round. -/
@[simp] theorem LocalView.lastArrival_step {r : ℕ} (prev : LocalView P K r) (arrival : P → K)
    (relayed : P → LocalView P K r) :
    (LocalView.step prev arrival relayed).lastArrival = arrival :=
  rfl

/-- Decidable equality on `LocalView P K r` over finite process sets `P`. -/
instance instDecidableEqLocalView [Fintype P] [DecidableEq K] :
    ∀ {r : ℕ}, DecidableEq (LocalView P K r)
  | 0, .init, .init => isTrue rfl
  | r + 1, .step prev₁ arr₁ rel₁, .step prev₂ arr₂ rel₂ =>
    letI : DecidableEq (LocalView P K r) := instDecidableEqLocalView
    if hprev : prev₁ = prev₂ then
      if harr : ∀ q, arr₁ q = arr₂ q then
        if hrel : ∀ q, rel₁ q = rel₂ q then
          isTrue (by rw [hprev, funext harr, funext hrel])
        else
          isFalse (fun h => by cases h; exact hrel (fun _ => rfl))
      else
        isFalse (fun h => by cases h; exact harr (fun _ => rfl))
    else
      isFalse (fun h => by cases h; exact hprev rfl)

/-- A deterministic `R`-round full-information clock synchronization protocol on the complete
network of processes `P` with clock values in `K`.

In each round `r : Fin R`, process `p` with local history `v : LocalView P K r` sends its round-`r`
message to `q` when `p`'s local hardware clock reads `sendTime r p v q`. After `R` rounds, process
`p` with final history `v : LocalView P K R` shifts its hardware clock by `adjust p v`. -/
structure Protocol (P : Type u) (K : Type v) (R : ℕ) where
  /-- Local hardware clock reading at which `p` sends its round-`r` message to `q`. -/
  sendTime : (r : Fin R) → P → LocalView P K r.val → P → K
  /-- Local clock adjustment computed by `p` after `R` rounds. -/
  adjust : P → LocalView P K R → K

namespace Protocol

variable [AddCommGroup K] {R : ℕ} (π : Protocol P K R)

/-- Process `p`'s local observation history after `r ≤ R` rounds under hardware clock offsets `c`
and message transit delays `δ`. -/
@[expose] def localView (c : P → K) (δ : ℕ → P → P → K) :
    (r : ℕ) → r ≤ R → P → LocalView P K r
  | 0, _, _ => .init
  | r + 1, hr, p =>
    let prev := fun q => localView c δ r (Nat.le_of_succ_le hr) q
    .step (prev p) (fun q => arrivalReading c δ r q p (π.sendTime ⟨r, hr⟩ q (prev q) p)) prev

/-- The local clock adjustment vector computed by `π` after all `R` rounds. -/
@[expose] def adj (c : P → K) (δ : ℕ → P → P → K) (p : P) : K :=
  π.adjust p (π.localView c δ R le_rfl p)

/-- Process `p`'s synchronized clock offset `c p + π.adj c δ p` after `π` finishes: at real time
`t`, `p`'s adjusted clock reads `t + π.syncOffset c δ p`. -/
@[expose] def syncOffset (c : P → K) (δ : ℕ → P → P → K) (p : P) : K :=
  c p + π.adj c δ p

end Protocol

/-- Protocol `π` achieves worst-case synchronized clock skew at most `γ` across all initial
hardware clock offsets `c` and all message transit delays `δ` in `[d_min, d_max]`
[Lundelius and Lynch][LundeliusLynch1984]. -/
@[expose] def AchievesSkew [AddCommGroup K] [LinearOrder K] {R : ℕ} (π : Protocol P K R)
    (d_min d_max γ : K) : Prop :=
  ∀ (c : P → K) (δ : ℕ → P → P → K), ValidDelays d_min d_max δ →
    ∀ p q : P, |π.syncOffset c δ p - π.syncOffset c δ q| ≤ γ

/-- Achieving clock skew `γ` implies achieving any larger skew bound `γ' ≥ γ`. -/
theorem AchievesSkew.mono [AddCommGroup K] [LinearOrder K] {R : ℕ} {π : Protocol P K R}
    {d_min d_max γ γ' : K} (h : AchievesSkew π d_min d_max γ) (hγ : γ ≤ γ') :
    AchievesSkew π d_min d_max γ' :=
  fun c δ hδ p q => (h c δ hδ p q).trans hγ

/-! ### Time-shift indistinguishability -/

/-- Shift each process `p`'s hardware clock offset by `s p`, corresponding to advancing events at
`p` by `s p` units of real time while keeping `p`'s local clock readings unchanged. -/
@[expose] def shiftOffsets [Add K] (c s : P → K) (p : P) : K :=
  c p + s p

/-- Shift transit delays consistently with `shiftOffsets c s`: when `p`'s events occur `s p`
earlier and `q`'s events occur `s q` earlier, a message from `p` to `q` is in transit for
`δ r p q + s p - s q`. -/
@[expose] def shiftDelays [AddCommGroup K] (δ : ℕ → P → P → K) (s : P → K) (r : ℕ) (p q : P) :
    K :=
  δ r p q + s p - s q

/-- Shifting hardware offsets by `s` and transit delays by `s p - s q` preserves every local
arrival clock reading identically. -/
@[simp] theorem arrivalReading_shift_eq [AddCommGroup K] (c : P → K) (δ : ℕ → P → P → K)
    (s : P → K) (r : ℕ) (p q : P) (τ : K) :
    arrivalReading (shiftOffsets c s) (shiftDelays δ s) r p q τ = arrivalReading c δ r p q τ := by
  simp only [arrivalReading, shiftOffsets, shiftDelays]
  abel

/-- **Time-shift indistinguishability of local views**
[Lundelius and Lynch][LundeliusLynch1984]: shifting hardware offsets to `shiftOffsets c s` and
transit delays to `shiftDelays δ s` leaves every process's local view unchanged at every round
`r ≤ R`. -/
@[simp] theorem localView_shift_eq [AddCommGroup K] {R : ℕ} (π : Protocol P K R) (c : P → K)
    (δ : ℕ → P → P → K) (s : P → K) :
    ∀ (r : ℕ) (hr : r ≤ R) (p : P),
      π.localView (shiftOffsets c s) (shiftDelays δ s) r hr p = π.localView c δ r hr p
  | 0, _, _ => rfl
  | r + 1, hr, p => by
    have ih := localView_shift_eq π c δ s r (Nat.le_of_succ_le hr)
    dsimp only [Protocol.localView]
    congr 1
    · exact ih p
    · funext q
      rw [ih q, arrivalReading_shift_eq]
    · exact funext ih

/-- **Time-shift indistinguishability of adjustments**
[Lundelius and Lynch][LundeliusLynch1984]: every deterministic `R`-round protocol computes the
exact same clock adjustment vector under `(shiftOffsets c s, shiftDelays δ s)` as under `(c, δ)`. -/
@[simp] theorem adj_shift_eq [AddCommGroup K] {R : ℕ} (π : Protocol P K R) (c : P → K)
    (δ : ℕ → P → P → K) (s : P → K) :
    π.adj (shiftOffsets c s) (shiftDelays δ s) = π.adj c δ := by
  funext p
  simp only [Protocol.adj, localView_shift_eq]

/-- Under a real-time shift `s`, process `p`'s synchronized clock offset translates by `+ s p`. -/
@[simp] theorem syncOffset_shift_eq [AddCommGroup K] {R : ℕ} (π : Protocol P K R) (c : P → K)
    (δ : ℕ → P → P → K) (s : P → K) (p : P) :
    π.syncOffset (shiftOffsets c s) (shiftDelays δ s) p = π.syncOffset c δ p + s p := by
  simp only [Protocol.syncOffset, shiftOffsets, adj_shift_eq]
  abel

end Model

section MidpointEstimator

variable {P : Type u} [DecidableEq P] {K : Type v}

/-- Midpoint-delay estimator of `c q - c p`: given `p`'s local arrival readings `recv : P → K` for
messages broadcast at local reading `0`, estimates `0` for `q = p` and
`(d_min + d_max) / 2 - recv q` for `q ≠ p`. -/
@[expose] def estDiff [Field K] (d_min d_max : K) (p : P) (recv : P → K) (q : P) : K :=
  if q = p then 0 else (d_min + d_max) / 2 - recv q

/-- Adding `p`'s hardware offset `c p` to `estDiff d_min d_max p recv q` approximates sender `q`'s
hardware offset `c q` within `(d_max - d_min) / 2` whenever `q ≠ p` arrived with delay
`d ∈ [d_min, d_max]`. -/
theorem abs_add_estDiff_sub_le [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {d_min d_max : K} (hd : d_min ≤ d_max) (c : P → K) (p q : P) (recv : P → K) {d : K}
    (hrecv : q ≠ p → recv q = d + c p - c q) (hd_min : q ≠ p → d_min ≤ d)
    (hd_max : q ≠ p → d ≤ d_max) :
    |(c p + estDiff d_min d_max p recv q) - c q| ≤ (d_max - d_min) / 2 := by
  by_cases hqp : q = p
  · subst hqp
    simp only [estDiff, ↓reduceIte, add_zero, sub_self, abs_zero]
    linarith
  · simp only [estDiff, hqp, ↓reduceIte, hrecv hqp]
    have hlo := hd_min hqp
    have hhi := hd_max hqp
    exact abs_le.mpr ⟨by linarith, by linarith⟩

end MidpointEstimator

end Cslib.Distributed.ClockSync
