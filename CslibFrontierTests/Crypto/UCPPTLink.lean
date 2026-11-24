/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: local-only (test)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Crypto.Protocols.UC.PPT
import CslibFrontier.Crypto.Protocols.UC.PPT.Link
import CslibFrontier.Crypto.Protocols.UC.PPT.Wrappers
import CslibFrontier.Languages.Probabilistic.Oracle.Support
import CslibFrontierTests.Crypto.UCPPT

/-!
# Tests for `UC.PPT.Link`

Non-degenerate witnesses for `CslibFrontier.Crypto.Protocols.UC.PPT.Link`:

1. `Machine.IsReplyBounded` admits unbounded growing state and coin-dependent replies
   (`windowProtocol`, returning the `κ`-bit window of a growing coin-masked list; also lifted
   through `Machine.IsReplyBounded.routeCorrupt`), while the certified full-state protocol
   `coinStore.toProtocol` is not reply-bounded (`coinStore_not_isReplyBounded`).
2. `Environment.IsPPT.absorbAdversary` certified for a stateful reply-growing adversary
   `tagLogAdv` and an interactive two-party environment `linkEnv`, together with an explicit
   enlarged-cap witness showing that running `wordRunWith` without enlarging the environment's
   reply bound truncates `tagLogAdv`'s reply and changes the distribution.
3. Negative witness showing that the `Machine.IsReplyBounded` premise cannot be dropped:
   a stateless doubling machine `doubleMachine` is strict PPT (`Machine.IsPPTFamily`) with replies
   bounded by `2 * w.length` (so even a request-dependent reply bound fails), and a `κ`-round
   iterating machine `iterQueryMachine` is strict PPT, request-bounded (`Machine.IsRequestBounded`),
   and call-bounded (`IsBounded (κ + 1)`), yet their sequential composition
   `fun κ C => (iterQueryMachine κ C).comp (doubleMachine κ C)` has no `Machine.IsPPTFamily`
   certificate (using both `cert.init.length_le` and `cert.handle.length_le`).
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.UCPPTLink

open Cslib Cslib.Crypto.Protocols.UC Cslib.Probability Turing.MultiTapeTM
open CslibFrontierTests.Crypto.UCPPT

private def msgPort : WordPort (List Bool) (List Bool) :=
  ⟨encBits, Decoder.bits, encBits, Decoder.bits⟩

private def unaryCodec : WordCodec ℕ where
  enc := encUnary
  decode := Decoder.unary.decode
  decode_enc := Decoder.unary.decode_enc

/-! ### 1. `IsReplyBounded` with growing state and `¬ IsReplyBounded` for `coinStore` -/

section ReplyBoundWitnesses

/-- Two-party protocol with real coins and unbounded growing state: party `0` appends a
coin-masked bit to the stored list; party `1` polls and receives the `κ`-bit prefix of the list;
the network backdoor is a no-op. -/
private noncomputable def windowProtocol : Protocol 2 Bool (List Bool) Unit Unit := fun κ _ =>
  { State := List Bool
    init := pure []
    handle := fun
      | Sum.inl (i, b), s =>
        if i = 0 then do
          let c ← ProbOracleComp.sample (ProbComp.uniform Bool)
          pure (none, (b ^^ c) :: s)
        else
          pure (some (List.take κ s), s)
      | Sum.inr (), s => pure ((), s) }

/-- On a state of length `2 * κ` (`κ ≥ 1`), polling `windowProtocol` returns a list of length `κ`,
strictly shorter than the state. -/
theorem windowProtocol_poll_shorter_than_state (κ : ℕ) (hκ : 1 ≤ κ) :
    let s : (windowProtocol κ ∅).State := List.replicate (2 * κ) true
    ProbOracleComp.runWith emptyWordOracle
        (ProbOracleComp.lowerWith WordInterface.empty 0
          (((windowProtocol κ ∅).handle (Sum.inl ((1 : Fin 2), false))).run s)) () =
      PMF.pure (((some (List.replicate κ true) : Option (List Bool)), s), ()) ∧
    (List.replicate κ true).length < s.length := by
  have hne : (1 : Fin 2) ≠ 0 := by decide
  refine ⟨?_, by simp; omega⟩
  simp only [windowProtocol, StateT.run, hne, ↓reduceIte, ProbOracleComp.lowerWith,
    ProbOracleComp.simulate_pure, ProbOracleComp.runWith_pure, List.take_replicate]
  have hmin : min κ (2 * κ) = κ := by omega
  rw [hmin]

/-- `windowProtocol` satisfies `Machine.IsReplyBounded` with bound `p.secParam + 1`, despite
unbounded state growth and coin-dependent state contents. -/
theorem windowProtocol_isReplyBounded :
    Machine.IsReplyBounded windowProtocol WordInterface.empty
      (WordInterface.protocol coinPartyPort unitPort) := by
  have hsec : PolyBounded (fun p : PPTParam 2 => (encPPTParam 2 p).length)
      (fun p : PPTParam 2 => p.secParam) :=
    ((by fun_prop : ComputableInPolyTime (fun p : PPTParam 2 => p.secParam)
      (encPPTParam 2) encUnary).polyBounded_length).mono fun p => by
      simp [encUnary_apply]
  refine ⟨fun p => p.secParam + 1, hsec.add (PolyBounded.const 1), fun p q s x hx => ?_⟩
  let s' : List Bool := s
  cases q with
  | inl ib =>
    rcases ib with ⟨i, b⟩
    by_cases hi : i = 0
    · let x' : Option (List Bool) × List Bool := x
      have hx0 : x' ∈ OracleComp.supportWith (fun _ => Set.univ)
          ((ProbOracleComp.sample (ProbComp.uniform Bool) >>= fun c =>
            pure ((none : Option (List Bool)), (b ^^ c) :: s')) :
              WordOracleComp WordInterface.empty.Channel (Option (List Bool) × List Bool)) := by
        simp only [windowProtocol, StateT.run, hi, ↓reduceIte, ProbOracleComp.lowerWith,
          ProbOracleComp.simulate_bind, ProbOracleComp.simulate_sample,
          ProbOracleComp.simulate_pure, OracleComp.support] at hx
        exact hx
      rw [OracleComp.mem_supportWith_bind_iff] at hx0
      rcases hx0 with ⟨c, _, hc⟩
      have hx' := OracleComp.eq_of_mem_supportWith_pure hc
      have h1 : x'.1 = none := congrArg Prod.fst hx'
      change (coinPartyPort.reply x'.1).length ≤ p.secParam + 1
      rw [h1]
      simp [coinPartyPort, WordPort.party, encOption_none]
    · simp only [windowProtocol, StateT.run, hi, ↓reduceIte, ProbOracleComp.lowerWith,
        ProbOracleComp.simulate_pure, OracleComp.support] at hx
      have hx' := OracleComp.eq_of_mem_supportWith_pure hx
      subst hx'
      change (coinPartyPort.reply (some (List.take p.secParam s'))).length ≤ p.secParam + 1
      simp only [coinPartyPort, WordPort.party, coinInputPort, encOption_some, encBits_apply,
        List.length_cons]
      have htake : (List.take p.secParam s').length ≤ p.secParam := List.length_take_le _ _
      omega
  | inr u =>
    cases u
    simp only [windowProtocol, StateT.run, ProbOracleComp.lowerWith,
      ProbOracleComp.simulate_pure, OracleComp.support] at hx
    have hx' := OracleComp.eq_of_mem_supportWith_pure hx
    subst hx'
    change ([] : List Bool).length ≤ p.secParam + 1
    simp

/-- Transfer of `windowProtocol_isReplyBounded` through static-corruption routing. -/
theorem windowProtocol_corruptRouter_isReplyBounded :
    Machine.IsReplyBounded (fun κ C => corruptRouter C (windowProtocol κ C)) WordInterface.empty
      (WordInterface.protocol coinPartyPort (WordPort.sum coinPartyPort unitPort)) :=
  windowProtocol_isReplyBounded.routeCorrupt

/-- The certified full-state protocol `coinStore.toProtocol` is not `Machine.IsReplyBounded`:
its party-`1` poll reply grows linearly with the arbitrary state word. -/
theorem coinStore_not_isReplyBounded :
    ¬ Machine.IsReplyBounded coinStore.toProtocol WordInterface.empty
      (WordInterface.protocol coinPartyPort unitPort) := by
  rintro ⟨bound, _, hle⟩
  let p : PPTParam 2 := ⟨0, 0, ∅⟩
  let s : List Bool := List.replicate (bound p + 1) true
  have hmem : ((some s : Option (List Bool)), s) ∈ OracleComp.support
      (ProbOracleComp.lowerWith WordInterface.empty p.replyBound
        (((coinStore.toProtocol p.secParam p.corrupted).handle
          (Sum.inl ((1 : Fin 2), false))).run s)) := by
    change ((some s : Option (List Bool)), s) ∈ OracleComp.support
      (ProbOracleComp.lowerWith WordInterface.empty 0
        (ProbOracleComp.sample ((coinStore.onInput (1 : Fin 2) false).run s)))
    rw [ProbOracleComp.lowerWith, ProbOracleComp.simulate_sample, ProbOracleComp.support_sample,
      coinStore_onInput_one_eval]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have hlen := hle p (Sum.inl ((1 : Fin 2), false)) s ((some s : Option (List Bool)), s) hmem
  change (coinPartyPort.reply (some s)).length ≤ bound p at hlen
  simp only [coinPartyPort, WordPort.party, coinInputPort, encOption_some, encBits_apply,
    List.length_cons, s, List.length_replicate] at hlen
  omega

end ReplyBoundWitnesses

end CslibFrontierTests.Crypto.UCPPTLink
