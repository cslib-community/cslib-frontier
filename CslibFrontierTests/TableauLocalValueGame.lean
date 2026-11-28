/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Circuit.Boolean.Tableau.LocalValueGame

/-!
# Tests: claims relative to the input in the circuit-value game on the tableau

The encoding `Cslib.Circuits.Boolean.Tableau.ValueGame.encLocal x` does not store the bits of the
input of a claim about `x`, only its length: claims about two different inputs of a thousand bits
have the same encoding relative to their inputs. A claim about another input takes the other tag
bit, so the encoding stays injective across inputs. With claims encoded relative to `x`, the game
on the claim that the output wire is true still decides the run of the machine
(`Cslib.Circuits.Boolean.Tableau.ValueGame.wins_position_outWire_iff`), and its reachable positions
have length logarithmic in the input length and the step count
(`Cslib.Circuits.Boolean.Tableau.ValueGame.exists_length_le_of_reach_encLocal`). The local data of a
claim is encoded by the words of the former right-nested tuple encoding, and at an input wire the
local position (`Cslib.Circuits.Boolean.Tableau.ValueGame.localPosition`) uses the bit it is given
as the read of the input there: the true claim is won and the false one lost.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.TableauLocalValueGame

open Cslib Cslib.Circuits.Boolean.Tableau Cslib.Circuits.Boolean.Tableau.ValueGame
open Turing Turing.MultiTapeTM Turing.MultiTapeATM.WordGame

/-- The bits of the input are not stored: claims about two inputs of the same length have the same
encoding relative to their inputs. -/
example : encLocal (List.replicate 1000 true) ⟨List.replicate 1000 true, 4, 7, true⟩ =
    encLocal (List.replicate 1000 false) ⟨List.replicate 1000 false, 4, 7, true⟩ := by
  simp only [encLocal_self, List.length_replicate]

-- `encLocalClaim` has the exact encoded words of the former right-nested tuple encoding.
example (n T w : ℕ) (v : Bool) :
    encLocalClaim ⟨n, T, w, v⟩ =
      encPair encNat (encPair encNat (encPair encNat encBool)) (n, T, w, v) :=
  rfl

/-- A claim about another input is tagged `true`, a claim about `x` is tagged `false`. -/
example : (encLocal [true] ⟨[false], 0, 0, true⟩).head? = some true ∧
    (encLocal [true] ⟨[true], 0, 0, true⟩).head? = some false := by
  rw [encLocal_of_ne (by decide), encLocal_self]
  exact ⟨rfl, rfl⟩

variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State] (tm : MultiTapeTM k Bool State)

/-- With claims encoded relative to the input, the game on the output claim decides the run. -/
example {x : List Bool} {T : ℕ} (hn : x.length < 2 * T) :
    Wins (update tm (encLocal x))
        (position tm (encLocal x) ⟨x, T, outWire k State x.length T, true⟩) ↔
      OutView.ofList (tm.runFrom (tm.initCfg x) T).output = .one true :=
  wins_position_outWire_iff (encLocal x) hn

/-- Positions reachable from the output claim have length `O(log x.length + log T)`. -/
example : ∃ c, ∀ (x : List Bool) (T : ℕ) (w : List Bool),
    Reach (update tm (encLocal x))
      (position tm (encLocal x) ⟨x, T, outWire k State x.length T, true⟩) w →
    w.length ≤ 4 * Nat.size x.length + 6 * Nat.size T + c := by
  obtain ⟨c, hc⟩ := exists_length_le_of_reach_encLocal (tm := tm)
  exact ⟨c, fun x T w h => hc x T _ true w (outWire_lt _ _) h⟩

/-- At an input wire, the local position reads the given input bit: with claims encoded relative
to the input, the true claim is won and the false one lost. -/
example (x : List Bool) (T i : ℕ) (hi : i < x.length) :
    Wins (update tm (encLocal x)) (localPosition tm (⟨x.length, T, i, x[i]⟩, x[i]?)) ∧
      ¬ Wins (update tm (encLocal x)) (localPosition tm (⟨x.length, T, i, !x[i]⟩, x[i]?)) := by
  have hw : i < x.length + numGates k State T := by omega
  have h₁ := position_encLocal (tm := tm) (c := ⟨x, T, i, x[i]⟩) rfl
  have h₂ := position_encLocal (tm := tm) (c := ⟨x, T, i, !x[i]⟩) rfl
  simp only [Claim.toLocal_mk] at h₁ h₂
  rw [← h₁, ← h₂, wins_position_iff x T i hw, wins_position_iff x T i hw, val_input tm hi]
  simp

/-- From an ordinary `module` client, `localMachine` decides the run of `tm` on `x` without
unfolding `localMachine`. -/
example {x : List Bool} {T : ℕ} (hn : x.length < 2 * T) :
    (localMachine tm ⟨x.length, T, outWire k State x.length T, true⟩).Accepts x ↔
      OutView.ofList (tm.runFrom (tm.initCfg x) T).output = .one true :=
  accepts_localMachine_iff (tm := tm) hn

/-- From an ordinary `module` client, all five linear-space callback bounds, the branch halting
clock, and the `O(log n + log T)` state-length bound hold directly on `localMachine tm lc₀`'s
fields and `run` / `replay`. -/
example (x : List Bool) (T w : ℕ) (v : Bool) (hw : w < x.length + numGates k State T) :
    let lc₀ : LocalClaim := ⟨x.length, T, w, v⟩
    let M := localMachine tm lc₀
    ComputableInSpace M.query encLocalState encNat (fun s => (encLocalState s).length) ∧
      ComputableInSpace M.halted encLocalState encBool (fun s => (encLocalState s).length) ∧
      ComputableInSpace M.accept encLocalState encBool (fun s => (encLocalState s).length) ∧
      ComputableInSpace M.universal encLocalState encBool (fun s => (encLocalState s).length) ∧
      ComputableInSpace M.next
        (encPair encLocalState (encPair (encOption encBool) encBool)) encLocalState
        (fun p => (encPair encLocalState (encPair (encOption encBool) encBool) p).length) ∧
      (∀ choices : List Bool, w < choices.length → M.halted (M.run x choices) = true) ∧
      (∃ c, ∀ choices : List Bool,
        (encLocalState (M.run x choices)).length ≤
          8 * Nat.size x.length + 12 * Nat.size T + c) := by
  intro lc₀ M
  refine ⟨localQuery_inSpace, localHalted_inSpace, localAccept_inSpace, localUniversal_inSpace,
    localNext_inSpace, ?_, ?_⟩
  · intro choices hlen
    change M.halted (M.replay x choices M.init) = true
    rw [localMachine_init]
    exact halted_replay_localMachine (tm := tm) lc₀ hw choices hlen
  · obtain ⟨c, hc⟩ := exists_length_le_of_replay_localMachine (tm := tm)
    refine ⟨c, fun choices => ?_⟩
    change (encLocalState (M.replay x choices M.init)).length ≤ _
    rw [localMachine_init]
    exact hc lc₀ x T w v choices hw

end CslibFrontierTests.TableauLocalValueGame
