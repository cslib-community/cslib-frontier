/-
Copyright (c) 2026 Christian Reitwiessner, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenWeightedSubdivision
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.CallReplay
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.DeterministicCall.Resource
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Cases

/-!
# Binary-choice Justesen-weighted adjacency

At valid seed and endpoint IDs, the initialized adjacency query takes three deterministic
steps. The binary-choice adapter has one successful first-halting selector list for it.
The reply parser reads the adjacency bit after those selectors and a false return selector,
then returns the untouched suffix.
Every selector run halts by the same clock and obeys a common logarithmic state bound.
The local operations and optional reply decoder use linear workspace in their encoded requests.
-/

public section

namespace Cslib.Complexity.STCON

open Cslib.Code.JustesenFamily Cslib.Reachability.Hoza
open _root_.Turing _root_.Turing.MultiTapeNTM.ConfigurationGraph

variable {k : ℕ} {State : Type} [Fintype State]

/-- At valid initialized ranks and endpoints, the weighted edge callback has one successful
first-halting selector list. That list takes all three deterministic steps on the original word. -/
theorem configurationJustesenSubdivisionEdge_firstHalting_iff
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (u v : Fin size.vertexCount)
      (bits : List Bool),
      let ctx := configurationJustesenSubdivisionContext ntm c w seed.val
      let entry := some (justesenSubdivisionEdgeStart (ctx, u.val, v.val))
      let M := (justesenWeightedSubdivisionCallback ntm).withRejectingChoice
      M.FirstHalting w bits entry ∧ (M.replay w bits entry).isSome ↔ bits = [false, false, false] :=
  fun seed u v bits => by
    obtain ⟨_, hcall⟩ := configurationJustesenSubdivisionEdge_contract ntm c
    obtain ⟨hbefore, hhalt, _, _⟩ := hcall w seed u v
    exact (justesenWeightedSubdivisionCallback ntm).withRejectingChoice_firstHalting_iff
      w _ 3 hbefore hhalt bits

open Cslib.LayeredDigraph.Subdivision QueryMachine.Subdivision

/-- The initialized edge parser consumes three false call selectors and one false return
selector, returns subdivision adjacency on the original word, and preserves the suffix. -/
theorem configurationJustesenSubdivisionEdge_readReply_iff
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
    let index := configurationSubdivisionIndex ntm c w
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (u v : Fin size.vertexCount)
      (bits rest : List Bool) (hit : Bool),
      let ctx := configurationJustesenSubdivisionContext ntm c w seed.val
      let entry := some (justesenSubdivisionEdgeStart (ctx, u.val, v.val))
      let M := (justesenWeightedSubdivisionCallback ntm).withRejectingChoice
      M.readReply (Option.map callbackVerdict) w entry bits = some (hit, rest) ↔
        bits = [false, false, false, false] ++ rest ∧
          (hit = true ↔ (graph (layeredDigraph I)
            (generatedWeight ((BitString.equivFin _).symm seed)) size.chainBound).Adj
              (index.symm u) (index.symm v)) := by
  intro I size index seed u v bits rest hit ctx entry M
  let D := justesenWeightedSubdivisionCallback ntm
  let start := justesenSubdivisionEdgeStart (ctx, u.val, v.val)
  obtain ⟨_, hcall⟩ := configurationJustesenSubdivisionEdge_contract ntm c
  obtain ⟨_, _, hadj, _⟩ := hcall w seed u v
  have hcanonical : M.replay w [false, false, false] entry = some (D.runFrom w start 3) :=
    D.withRejectingChoice_replay_false w start 3
  rw [M.readReply_iff]
  constructor
  · rintro ⟨callBits, hbits, hfirst, hret⟩
    have hsome : (M.replay w callBits entry).isSome := by
      simpa only [Option.isSome_map, Option.isSome_some] using congrArg Option.isSome hret
    obtain rfl := (configurationJustesenSubdivisionEdge_firstHalting_iff
      ntm c w seed u v callBits).mp ⟨hfirst, hsome⟩
    rw [hcanonical] at hret
    exact ⟨hbits, Option.some.inj hret ▸ hadj⟩
  · rintro ⟨rfl, hhit⟩
    refine ⟨[false, false, false], rfl, ((configurationJustesenSubdivisionEdge_firstHalting_iff
      ntm c w seed u v [false, false, false]).mpr rfl).1, ?_⟩
    rw [hcanonical]
    exact congrArg some (Bool.eq_iff_iff.mpr (hadj.trans hhit.symm))

open MultiTapeTM

/-- On the original word, a valid initialized binary-choice edge call halts within three
selectors and every replay state has logarithmic encoded length, including on rejection. -/
theorem configurationJustesenSubdivisionEdge_choice_bounds
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ∃ C, ∀ w : List Bool,
      let I := configurationInstance ntm c w
      let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
      ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (u v : Fin size.vertexCount),
        let ctx := configurationJustesenSubdivisionContext ntm c w seed.val
        let start := some (justesenSubdivisionEdgeStart (ctx, u.val, v.val))
        let M := (justesenWeightedSubdivisionCallback ntm).withRejectingChoice
        M.HaltsFrom w start 3 ∧ ∀ bits,
          (encOption encJustesenSubdivisionState (M.replay w bits start)).length ≤
            C * (Nat.log2 w.length + 1) := by
  obtain ⟨C, hC⟩ := configurationJustesenSubdivisionEdge_contract ntm c
  refine ⟨C + 1, fun w seed u v => ?_⟩
  obtain ⟨_, hhalt, _, hstate⟩ := hC w seed u v
  let ctx := configurationJustesenSubdivisionContext ntm c w seed.val
  let start := justesenSubdivisionEdgeStart (ctx, u.val, v.val)
  let M := justesenWeightedSubdivisionCallback ntm
  let B := M.withRejectingChoice
  change B.HaltsFrom w (some start) 3 ∧ _
  have hclock : B.HaltsFrom w (some start) 3 := fun bits hlen => by
    rcases M.withRejectingChoice_replay_eq_none_or_runFrom w start bits with hr | hr
    · rw [hr]
      rfl
    · rw [hr, hlen]
      exact hhalt
  refine ⟨hclock, fun bits => ?_⟩
  have htake : B.replay w (bits.take 3) (some start) = B.replay w bits (some start) :=
    (B.withInit (some start)).run_take_of_haltsWithin w hclock bits
  change (encOption encJustesenSubdivisionState (B.replay w bits (some start))).length ≤ _
  rw [← htake]
  rcases M.withRejectingChoice_replay_eq_none_or_runFrom w start (bits.take 3) with hr | hr
  · rw [hr, encOption_none]
    exact Nat.zero_le _
  · rw [hr, encOption_some, List.length_cons, Nat.add_mul, Nat.one_mul]
    have hbound := hstate _ (List.length_take .. ▸ Nat.min_le_left 3 bits.length)
    exact (Nat.add_le_add_right hbound 1).trans (by omega)

open MultiTapeTM.ComputableInSpace
open NondeterministicQueryMachine (encReadChoice)

/-- The binary-choice edge callback and its optional reply decoder use linear workspace.
The missing state reports rejection, and a returned false bit is preserved as `some false`. -/
theorem justesenWeightedSubdivisionChoice_parts_inSpace (ntm : MultiTapeNTM k Bool State) :
    let M := (justesenWeightedSubdivisionCallback ntm).withRejectingChoice
    let enc := encOption encJustesenSubdivisionState
    let encNext := encPair enc encReadChoice
    ComputableInSpace M.query enc encNat (fun s => (enc s).length) ∧
    ComputableInSpace M.next encNext enc (fun p => (encNext p).length) ∧
    ComputableInSpace M.halted enc encBool (fun s => (enc s).length) ∧
    ComputableInSpace (fun s => s.map callbackVerdict) enc (encOption encBool)
      (fun s => (enc s).length) := by
  obtain ⟨hq, hn, hh, _, _⟩ := justesenWeightedSubdivisionCallback_parts_inSpace ntm
  obtain ⟨hq, hn, hh⟩ := QueryMachine.withRejectingChoice_parts_inSpace _ _ hq hn hh
  exact ⟨hq, hn, hh, (optionElim none (budget_optionSome
    (callbackVerdict_inSpace _ _))).of_enc_eq fun s => by cases s <;> rfl⟩

end Cslib.Complexity.STCON
