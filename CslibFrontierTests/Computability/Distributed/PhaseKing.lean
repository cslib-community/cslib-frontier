/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Distributed.Byzantine.PhaseKing
import CslibFrontier.Computability.Distributed.Byzantine.RecursiveOralMessages

/-! Two-round rotating-king protocol and multivalued-to-binary reduction steps (checked as an
ordinary `module` client):

* `decide`-checked executions of `phaseKing` on `Fin 5, t = 1` over `Bool` and `Fin 10` (with a
  faulty king in phase 0 and convergence under the honest king of phase 1, plus unanimity
  persistence across a faulty-king phase), and on `Fin 9, t = 2` across two consecutive faulty
  kings followed by an honest third king.
* Binary `Protocol` bridge (`MultivaluedProtocol.toProtocol`) and infinite/universe-polymorphic
  instantiations (`V = ℕ`, `exists_polyMsg_solvesByzantineAgreement.{u, v}`).
* Sharpness at `4 * t = n`: explicit `decide` trace on `Fin 4, t = 1` where `phaseKing` violates
  agreement while `om1` and `om` succeed, universal refutation `phaseKing_fails_four_one`, and
  `MultivaluedProtocol.not_solvesByzantineAgreement` on `Fin 3, t = 1` over `Fin 10`.
* `decide`-checked runs of `turpinCoan` on `Fin 4, t = 1` composed with `om1` and `om` over
  `Fin 10` (unanimous validity, split-perplexed recovery of the majority value, three-way fallback
  to `default`, and exact `(n - |F|) * n = 12` value-message count), and on `Fin 5, t = 1` composed
  with `(phaseKing 1 kings5).toProtocol` over `Fin 100`. -/
set_option linter.privateModule false

namespace CslibFrontierTests.Distributed.PhaseKing

open Cslib.Distributed.Byzantine

/-! ### `uniqueAboveOn` edge cases -/

-- Strict majority returns `some`; a tie above threshold returns `none`.
example : uniqueAboveOn Finset.univ 3 (![10, 10, 20, 10, 30] : Fin 5 → ℕ) = some 10 := by
  decide

example : uniqueAboveOn Finset.univ 2 (![true, true, false, false] : Fin 4 → Bool) = none := by
  decide

/-! ### `phaseKing` on `Fin 5, t = 1` (`4 * 1 < 5`, `R = 4`) -/

/-- Phase kings `0` (phase 0) and `1` (phase 1) on `Fin 5`. -/
def kings5 : Fin 2 ↪ Fin 5 := Fin.castLEEmb (by decide)

/-- Process `0` (the phase-0 king!) is faulty and equivocates based on round and recipient. -/
def adv5Bool : ℕ → Fin 5 → Fin 5 → Bool :=
  fun r _ i => decide ((r + i.val) % 2 = 0)

-- Phase 0 has faulty king `0`, splitting honest processes `1` and `2` after round 2; phase 1 has
-- honest king `1`, bringing all four honest processes `1, 2, 3, 4` into agreement by round 4.
example :
    let π := phaseKing 1 kings5 (V := Bool)
    let x : Fin 5 → Bool := ![true, true, false, false, true]
    π.decision {0} adv5Bool x 2 1 ≠ π.decision {0} adv5Bool x 2 2 ∧
    (∀ i : Fin 4, π.decision {0} adv5Bool x 4 i.succ = false) ∧
    (∀ i : Fin 4, π.decision {0} adv5Bool x 7 i.succ = false) := by
  decide

-- Unanimity among honest processes (`true`) persists through phase 0 despite faulty king `0`.
example :
    let π := phaseKing 1 kings5 (V := Bool)
    let x : Fin 5 → Bool := ![false, true, true, true, true]
    (∀ i : Fin 4, (π.state {0} adv5Bool x 2 i.succ).est = true) ∧
    (∀ i : Fin 4, π.decision {0} adv5Bool x 4 i.succ = true) := by
  decide

-- Direct binary `Cslib.Distributed.Byzantine.Protocol` instance (`Msg = Bool`, 1 bit per message).
example : (phaseKing 1 kings5 (V := Bool)).toProtocol.SolvesByzantineAgreement 1 4 :=
  (MultivaluedProtocol.toProtocol_solvesByzantineAgreement_iff _ 1 4).2
    (phaseKing_solvesByzantineAgreement kings5 (by simp) le_rfl)

/-- Faulty process `0` equivocates across values in `Fin 10`. -/
def adv5Fin10 : ℕ → Fin 5 → Fin 5 → Fin 10 :=
  fun r _ i => ⟨(3 * r + 2 * i.val + 1) % 10, Nat.mod_lt _ (by omega)⟩

-- Multivalued `Fin 10` agreement on `Fin 5, t = 1` (both mixed and unanimous honest inputs).
example :
    let π := phaseKing 1 kings5 (V := Fin 10)
    (∀ i j : Fin 4,
      π.decision {0} adv5Fin10 ![7, 3, 7, 9, 2] 4 i.succ =
        π.decision {0} adv5Fin10 ![7, 3, 7, 9, 2] 4 j.succ) ∧
    (∀ i : Fin 4, π.decision {0} adv5Fin10 ![2, 7, 7, 7, 7] 4 i.succ = 7) := by
  decide

/-! ### `phaseKing` on `Fin 9, t = 2` (`4 * 2 < 9`, `R = 6`) -/

/-- Phase kings `0, 1, 2` on `Fin 9`; when `F = {0, 1}`, both phases 0 and 1 have faulty kings and
honest king `2` resolves agreement in phase 2 (rounds 5–6). -/
def kings9 : Fin 3 ↪ Fin 9 := Fin.castLEEmb (by decide)

/-- Two colluding traitors `{0, 1}` equivocating across `Fin 5` in every round. -/
def adv9 : ℕ → Fin 9 → Fin 9 → Fin 5 :=
  fun r j i => ⟨(r + 2 * j.val + i.val) % 5, Nat.mod_lt _ (by omega)⟩

def inputs9 : Fin 9 → Fin 5 := ![4, 4, 1, 2, 3, 1, 2, 3, 4]

example :
    let π := phaseKing 2 kings9 (V := Fin 5)
    (∀ i j : Fin 7,
      π.decision {0, 1} adv9 inputs9 6 ⟨i.val + 2, by omega⟩ =
        π.decision {0, 1} adv9 inputs9 6 ⟨j.val + 2, by omega⟩) ∧
    (∀ i : Fin 7,
      π.decision {0, 1} adv9 (fun _ => (3 : Fin 5)) 6 ⟨i.val + 2, by omega⟩ = 3) := by
  decide

-- Infinite value domain `V = ℕ` and independent process/value universes.
example : (phaseKing 2 kings9 (V := ℕ)).SolvesByzantineAgreement 2 6 :=
  phaseKing_solvesByzantineAgreement kings9 (by simp) le_rfl

section Universes

universe u v

example (P : Type u) [Fintype P] [DecidableEq P] (V : Type v) (hn : 4 * 2 < Fintype.card P) :
    ∃ π : MultivaluedProtocol P (PhaseKingState V) V V, π.SolvesByzantineAgreement 2 6 :=
  exists_polyMsg_solvesByzantineAgreement V hn le_rfl

end Universes

/-! ### Sharpness at `4 * t = n`: `phaseKing` fails on `Fin 4, t = 1` while `om1` succeeds -/

/-- Kings `0` and `1` on `Fin 4`, with faulty process `1`. -/
def kings4 : Fin 2 ↪ Fin 4 := Fin.castLEEmb (by decide)

def adv4Fail : ℕ → Fin 4 → Fin 4 → Bool :=
  fun r _ i => if r = 2 then true else decide (i = 2)

def inputs4Fail : Fin 4 → Bool := ![false, true, true, true]

-- Concrete trace of the `Fin 4, t = 1` failure:
-- * After round 1: honest king `0` saw 2 `false`, 2 `true` (`kingProposal = false`), while honest
--   process `2` saw 3 `true`s (`overwhelming = some true`).
-- * After phase 0 (round 2): `0` and `3` hold `false`, while `2` holds `true`.
-- * After phase 1 (round 4): faulty king `1` splits honest `0` (`false`) and `2` (`true`),
--   whereas `om1 (Fin 4)` brings all honest processes `0, 2, 3` into agreement.
example :
    let π := phaseKing 1 kings4 (V := Bool)
    (π.state {1} adv4Fail inputs4Fail 1 0).kingProposal = false ∧
    (π.state {1} adv4Fail inputs4Fail 1 2).overwhelming = some true ∧
    (π.state {1} adv4Fail inputs4Fail 2 0).est = false ∧
    (π.state {1} adv4Fail inputs4Fail 2 2).est = true ∧
    π.decision {1} adv4Fail inputs4Fail 4 0 = false ∧
    π.decision {1} adv4Fail inputs4Fail 4 2 = true ∧
    (om1 (Fin 4)).decision {1} (fun r j i _ => adv4Fail r j i) inputs4Fail 2 0 =
      (om1 (Fin 4)).decision {1} (fun r j i _ => adv4Fail r j i) inputs4Fail 2 2 := by
  decide

example (kings : Fin 2 ↪ Fin 4) (R : ℕ) :
    ¬ (phaseKing 1 kings (V := Bool)).toProtocol.SolvesByzantineAgreement 1 R := by
  rw [MultivaluedProtocol.toProtocol_solvesByzantineAgreement_iff]
  exact phaseKing_fails_four_one kings R

-- `3t + 1` node bound for multivalued protocols on `Fin 3, t = 1` over `Fin 10`.
example {S M : Type} (π : MultivaluedProtocol (Fin 3) S M (Fin 10)) (R : ℕ) :
    ¬ π.SolvesByzantineAgreement 1 R :=
  π.not_solvesByzantineAgreement (by simp) (by simp)

/-! ### Turpin–Coan reduction on `Fin 4, t = 1` (with `om1` and `om`) and `Fin 5, t = 1` -/

/-- Adversary on `Fin 4` for `turpinCoan` with `om1`: in round 1 faulty `3` sends `5` to `0, 1` and
`9` to `2`; in round 2 it sends `perplexed = true` only to `0` (splitting `alert` between `0` and
`1, 2`); in rounds 3–4 it equivocates inside `om1`. -/
def advTC4 : ℕ → Fin 4 → Fin 4 → TurpinCoanMsg (Fin 10) (Fin 4 → Bool)
  | 0, _, i => .val (if i = 2 then 9 else 5)
  | 1, _, i => .perplexed (decide (i = 0))
  | r + 2, _, i => .bin fun k => decide ((r + i.val + k.val) % 2 = 0)

-- `turpinCoan` + `om1` on `Fin 4, t = 1` (`R = 4` rounds, where 2-round `phaseKing` fails!):
-- 1. Unanimous honest inputs `8` -> all honest `0, 1, 2` decide `8`.
-- 2. Split inputs `![5, 5, 9, 0]`: `0, 1` are content (`perplexed = false`), `2` is perplexed
--    (`perplexed = true`), `0` gets `alert = true` and `1, 2` get `alert = false`; `om1` decides
--    `false`, and perplexed `2` recovers `5` from `{0, 1}`, so all of `0, 1, 2` decide `5`.
-- 3. Three-way split `![3, 6, 9, 0]`: all honest processes are perplexed, `alert = true`, and all
--    decide `default = 0`.
-- 4. Value-bearing messages sent by the 3 honest processes across all 4 rounds: `12 = (4 - 1) * 4`.
example :
    let π := turpinCoan 1 (0 : Fin 10) (om1 (Fin 4))
    (∀ i : Fin 3, π.decision {3} advTC4 (fun _ => 8) 4 i.castSucc = 8) ∧
    (π.state {3} advTC4 ![5, 5, 9, 0] 1 0).perplexed = false ∧
    (π.state {3} advTC4 ![5, 5, 9, 0] 1 2).perplexed = true ∧
    (∀ i : Fin 3, π.decision {3} advTC4 ![5, 5, 9, 0] 4 i.castSucc = 5) ∧
    (∀ i : Fin 3, π.decision {3} advTC4 ![3, 6, 9, 0] 4 i.castSucc = 0) ∧
    turpinCoanValueMessagesSent 1 (0 : Fin 10) (om1 (Fin 4)) {3} advTC4 ![5, 5, 9, 0] 4 = 12 := by
  decide

-- `turpinCoan` + `om (Fin 4) 1` on `Fin 4, t = 1` (checked by `decide` and general theorem).
def advTCOM4 : ℕ → Fin 4 → Fin 4 → TurpinCoanMsg (Fin 10) (List (Fin 4) → Bool)
  | 0, _, i => .val (if i = 2 then 9 else 5)
  | 1, _, i => .perplexed (decide (i = 0))
  | _ + 2, _, i => .bin fun σ => decide ((i.val + σ.length) % 2 = 0)

example :
    let π := turpinCoan 1 (0 : Fin 10) (om (Fin 4) 1)
    ∀ i : Fin 3, π.decision {3} advTCOM4 ![5, 5, 9, 0] 4 i.castSucc = 5 := by
  decide

example (V : Type) [DecidableEq V] (default : V) :
    (turpinCoan 1 default (om (Fin 4) 1)).SolvesByzantineAgreement 1 4 :=
  turpinCoan_solvesByzantineAgreement default (by simp)
    (solvesByzantineAgreement_om (by simp) le_rfl)

-- Purely polynomial-message multivalued agreement on `Fin 5, t = 1` over `Fin 100` by composing
-- `turpinCoan` with `(phaseKing 1 kings5).toProtocol`: `Fin 100` values are sent in round 1 only
-- (`20 = (5 - 1) * 5` messages), and single bits (`Bool`) in rounds 2–6.
def advTCPK5 : ℕ → Fin 5 → Fin 5 → TurpinCoanMsg (Fin 100) Bool
  | 0, _, i => .val (if i.val ≤ 2 then 42 else 99)
  | 1, _, i => .perplexed (decide (i = 1))
  | r + 2, _, i => .bin (decide ((r + i.val) % 2 = 1))

example :
    let πBool := (phaseKing 1 kings5 (V := Bool)).toProtocol
    let π := turpinCoan 1 (0 : Fin 100) πBool
    (∀ i : Fin 4, π.decision {0} advTCPK5 ![99, 42, 42, 42, 7] 6 i.succ = 42) ∧
    (∀ i : Fin 4, π.decision {0} advTCPK5 (fun _ => 73) 6 i.succ = 73) ∧
    turpinCoanValueMessagesSent 1 (0 : Fin 100) πBool {0} advTCPK5 (fun _ => 73) 6 = 20 := by
  decide

example :
    let πBool := (phaseKing 1 kings5 (V := Bool)).toProtocol
    (turpinCoan 1 (0 : Fin 100) πBool).SolvesByzantineAgreement 1 6 :=
  turpinCoan_solvesByzantineAgreement 0 (by simp)
    ((MultivaluedProtocol.toProtocol_solvesByzantineAgreement_iff _ 1 4).2
      (phaseKing_solvesByzantineAgreement kings5 (by simp) le_rfl))

end CslibFrontierTests.Distributed.PhaseKing
