/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.Parameter
public import CslibFrontier.Crypto.Protocols.UC.PPT.Link
public import CslibFrontier.Crypto.Protocols.UC.PPT.Wrappers
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Probabilistic.Oracle.SubstitutionGrowth
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Languages.Probabilistic.Oracle.Run

/-!
# Strict-PPT closure of adversary absorption and UC execution

Library infrastructure toward #6043 (no cited result): proves that absorbing a reply-bounded
strict-PPT adversary or hybrid protocol into a strict-PPT environment preserves
`Environment.IsPPT`, and that closed machine runs (`Machine.run`) and full UC executions (`exec`)
are uniform closed `IsPPT` programs in `(1^κ, z)`.

Because `exec_eq_exec_dummy` and `exec_dummyAdversary` reduce `exec π A C Z` to a closed run of
`corruptRouter C (π κ C)` against `absorbAdversary C A Z`, `isPPT_exec` requires no `Machine.comp`
certificate, call budget, or request-length bound.

## Main results

* `Cslib.Crypto.Protocols.UC.Environment.IsPPT.absorbAdversary`: absorbing a reply-bounded
  strict-PPT adversary into a strict-PPT environment preserves `Environment.IsPPT`.
* `Cslib.Crypto.Protocols.UC.Environment.IsPPT.absorbHybrid`: absorbing a reply-bounded
  strict-PPT hybrid protocol into a strict-PPT environment (`absorbHybrid`) preserves
  `Environment.IsPPT`.
* `Cslib.Crypto.Protocols.UC.Environment.IsPPT.absorbHybrid_of_reachable`: the wrapped parent's
  replies may instead satisfy an efficiently computable bound along this caller's executions.
* `Cslib.Crypto.Protocols.UC.Environment.IsPPT.isPPT_run`: running a strict-PPT environment
  against a closed, reply-bounded strict-PPT machine family is `IsPPT encBool`.
* `Cslib.Crypto.Protocols.UC.isPPT_exec`: UC execution of a strict-PPT protocol, adversary, and
  environment (with reply-bounded protocol and adversary) is `IsPPT encBool`.
-/

public section

namespace Cslib.Crypto.Protocols.UC

open Turing.MultiTapeTM Cslib.Probability

/-- Library infrastructure (no cited result), toward #6043 (not Proposition 7 of [Canetti2020]):
running a reply-bounded strict-PPT adversary inside a strict-PPT environment (`absorbAdversary`)
preserves strict PPT. -/
theorem Environment.IsPPT.absorbAdversary
    {n : ℕ} {In Out NetQ NetR AdvQ AdvR : Type}
    {Z : Environment n In Out AdvQ AdvR}
    {A : Adversary n AdvQ AdvR NetQ NetR}
    {party : WordPort (Fin n × In) (Option Out)}
    {net : WordPort NetQ NetR} {adv : WordPort AdvQ AdvR}
    (hZ : Z.IsPPT party adv) (hA : A.IsPPT net adv)
    (hAR : Machine.IsReplyBounded A (WordInterface.net net) (WordInterface.net adv))
    (C : Finset (Fin n)) :
    (absorbAdversary C A Z).IsPPT party net :=
  hZ.link (hA.liftAdversary (party := party)) (hAR.liftRight (iL := WordInterface.net party)) C

/-- Library infrastructure (no cited result), toward #6043: running a strict-PPT environment
against a closed, reply-bounded strict-PPT machine family is PPT in `(1^κ, z)`. -/
theorem Environment.IsPPT.isPPT_run
    {n : ℕ} {In Out AdvQ AdvR : Type}
    {party : WordPort (Fin n × In) (Option Out)} {adv : WordPort AdvQ AdvR}
    {Z : Environment n In Out AdvQ AdvR}
    {M : ℕ → Finset (Fin n) → Machine OracleSpec.empty (execSpec n In Out AdvQ AdvR)}
    (hZ : Z.IsPPT party adv)
    (hM : Machine.IsPPTFamily M WordInterface.empty (WordInterface.exec party adv))
    (hMR : Machine.IsReplyBounded M WordInterface.empty (WordInterface.exec party adv))
    (C : Finset (Fin n)) :
    Cslib.Probability.IsPPT encBool (fun κ z => (M κ C).run (Z κ z)) := by
  have hprep : ComputableInPolyTime (fun x : ℕ × List Bool => (⟨x.1, 0, x.2⟩ : EnvParam))
      (encPair encUnary encBits) encEnvParam := by
    have h0 : ComputableInPolyTime (fun _ : ℕ × List Bool => (0 : ℕ))
        (encPair encUnary encBits) encUnary := ComputableInPolyTime.const 0
    fun_prop
  refine (((hZ.isOraclePPTOn_lowerWith_link hM hMR C).isPPTOn_runEmptyOracle.preprocess
    hprep).congr fun x => ?_).isPPT
  refine congrArg ProbComp.eval ?_
  rw [ProbOracleComp.lowerWith, ProbOracleComp.run_simulate]
  exact congrArg (fun O => OracleComp.interpret (OracleComp.sumHandler ProbComp.unifFin O)
    ((M x.1 C).link (Z x.1 x.2))) (funext fun q => q.elim)

/-- Library infrastructure (no cited result), toward #6043 (not Proposition 7 of [Canetti2020]):
the UC execution of a strict-PPT protocol, adversary and environment, whose protocol and adversary
replies are polynomially bounded in the activation parameter, is PPT in `(1^κ, z)`. -/
theorem isPPT_exec
    {n : ℕ} {In Out NetQ NetR AdvQ AdvR : Type}
    {π : Protocol n In Out NetQ NetR} {A : ExecAdversary n In Out NetQ NetR AdvQ AdvR}
    {Z : Environment n In Out AdvQ AdvR}
    {party : WordPort (Fin n × In) (Option Out)} {net : WordPort NetQ NetR}
    {adv : WordPort AdvQ AdvR}
    (hparty : ComputableInPolyTime (fun w => (party.queryDecoder.decode w).1)
      encBits (encFinite (Fin n)))
    (hπ : π.IsPPT party net)
    (hπR : Machine.IsReplyBounded π WordInterface.empty (WordInterface.protocol party net))
    (hA : A.IsPPT (WordPort.sum party net) adv)
    (hAR : Machine.IsReplyBounded A (WordInterface.net (WordPort.sum party net))
      (WordInterface.net adv))
    (hZ : Z.IsPPT party adv) (C : Finset (Fin n)) :
    IsPPT encBool (fun κ z => exec π A C Z κ z) :=
  ((hZ.absorbAdversary hA hAR C).isPPT_run (hπ.corruptRouter hparty) hπR.routeCorrupt C).congr
    fun κ z => by rw [exec_eq_exec_dummy, exec_dummyAdversary]

/-- Library infrastructure (no cited result), toward #6043: the subroutine's environment
`absorbHybrid C ρ Z` is strict PPT for a reply-bounded strict-PPT hybrid protocol and a strict-PPT
environment of `ρ^σ`. -/
theorem Environment.IsPPT.absorbHybrid
    {n : ℕ} {In Out NetQ NetR SubIn SubOut NQ NR : Type}
    {ρ : HybridProtocol n In Out NetQ NetR SubIn SubOut}
    {Z : Environment n In Out (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR))}
    {party : WordPort (Fin n × In) (Option Out)} {net : WordPort NetQ NetR}
    {subParty : WordPort (Fin n × SubIn) (Option SubOut)} {nq : WordPort NQ NR}
    (hparty : ComputableInPolyTime (fun w => (party.queryDecoder.decode w).1)
      encBits (encFinite (Fin n)))
    (hZ : Z.IsPPT party (WordPort.sum party (WordPort.sum net (WordPort.sum subParty nq))))
    (hρ : ρ.IsPPT party net subParty)
    (hρR : Machine.IsReplyBounded ρ (WordInterface.net subParty) (WordInterface.protocol party net))
    (C : Finset (Fin n)) :
    (absorbHybrid C ρ Z).IsPPT subParty (WordPort.sum subParty nq) :=
  hZ.link ((hρ.hybridWrap (nq := WordPort.sum subParty nq)).routeCorrupt hparty)
    (hρR.hybridWrap (nq := WordPort.sum subParty nq)).routeCorrupt C

/-- Library infrastructure toward #6043: the subroutine's environment is strict PPT when the
outer caller has a polynomial-time computable cap on the wrapped parent's replies along all
supported executions, for every stateful imported word oracle. -/
theorem Environment.IsPPT.absorbHybrid_of_reachable
    {n : ℕ} {In Out NetQ NetR SubIn SubOut NQ NR : Type}
    {ρ : HybridProtocol n In Out NetQ NetR SubIn SubOut}
    {Z : Environment n In Out (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR))}
    {party : WordPort (Fin n × In) (Option Out)} {net : WordPort NetQ NetR}
    {subParty : WordPort (Fin n × SubIn) (Option SubOut)} {nq : WordPort NQ NR}
    (hparty : ComputableInPolyTime (fun w => (party.queryDecoder.decode w).1)
      encBits (encFinite (Fin n)))
    (hZ : Z.IsPPT party (WordPort.sum party (WordPort.sum net (WordPort.sum subParty nq))))
    (hρ : ρ.IsPPT party net subParty)
    (C : Finset (Fin n)) (cap : EnvParam → ℕ)
    (hcap : ComputableInPolyTime cap encEnvParam encUnary)
    (hreach : ∀ (e : EnvParam) (State : Type)
      (oracle : (WordInterface.exec subParty (WordPort.sum subParty nq)).Channel ×
        List Bool → StateT State PMF (List Bool))
      (sO : State) (s0 : (ρ e.secParam C).State), s0 ∈ (ρ e.secParam C).init.eval.support →
      RepliesFitOn (routeCorrupt C (hybridWrap (ρ e.secParam C)))
        (WordInterface.exec subParty (WordPort.sum subParty nq))
        (WordInterface.exec party
          (WordPort.sum party (WordPort.sum net (WordPort.sum subParty nq))))
        e.replyBound (cap e) oracle (Z e.secParam e.aux) s0 sO) :
    (UC.absorbHybrid C ρ Z).IsPPT subParty (WordPort.sum subParty nq) :=
  hZ.link_of_reachable ((hρ.hybridWrap (nq := WordPort.sum subParty nq)).routeCorrupt hparty)
    C cap hcap hreach

end Cslib.Crypto.Protocols.UC
