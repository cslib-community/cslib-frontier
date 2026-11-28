/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.IP.OptimalProver
public import CslibFrontier.Computability.Complexity.Classes.IP.TQBF
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Foundations.Analysis.ENNRealNatDiv
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF
import Mathlib.Algebra.Field.ZMod

/-!
# The machine verifier started at an arbitrary claim

The stack machine of `Cslib.Complexity.QBFProtocol.verifier` starts from the claim that the
arithmetization has value `1` at the origin. Its simulation theorem
(`Cslib.Complexity.QBFProtocol.runWith_verdict`) is already general in the claim, the remaining
tokens and the stack, so the machine can be started at any claim: `e.eval r = c` for a formula
`e` whose tokens are those of the input, a point `r` on the variables of `xs` and a value `c`,
over `ZMod p`. This file gives the resulting verifier `claimVerifier` and its three properties,
as in [Shamir][Shamir1992] and [Shen][Shen1992]:

* it is strict oracle PPT in the encoded input and claim
  (`Cslib.Complexity.QBFProtocol.isOraclePPTOn_claimVerifier`);
* against a word prover it behaves as the protocol `verifyAt` against the typed prover
  (`Cslib.Complexity.QBFProtocol.acceptProb_claimVerifier_eq`), so that every prover is accepted
  with probability at most `1 / 3` on a false claim, for a prime modulus `p` with
  `6 * ops * D ≤ p` and `e.maxRoundDegree ≤ D`, where `D` is the verifier's degree bound
  (`Cslib.Complexity.QBFProtocol.acceptProb_claimVerifier_le`);
* a prover answering each message by a function of the message alone whose decoded replies agree
  with the honest replies on every query whose tokens are a suffix of the tokens of the claim
  formula (the queries the verifier asks) is accepted with probability `1` on a true claim
  (`Cslib.Complexity.QBFProtocol.acceptProb_claimVerifier_eq_one_of_suffix`), even when it keeps
  the history of the interaction, as `Cslib.Complexity.Prover.ofHistoryFun` does.

## Main definitions

* `Cslib.Complexity.QBFProtocol.claimVerifier`: the verifier, on the input
  `Cslib.Complexity.QBFProtocol.Machine.ClaimInput` (the parameters and tokens with the claim) that
  `Cslib.Complexity.QBFProtocol.Machine.loopFrom` runs.

## Main results

* `Cslib.Complexity.QBFProtocol.isOraclePPTOn_claimVerifier`
* `Cslib.Complexity.QBFProtocol.acceptProb_claimVerifier_eq`
* `Cslib.Complexity.QBFProtocol.acceptProb_claimVerifier_le`
* `Cslib.Complexity.QBFProtocol.run_verifyAt_of_agreesAt_suffix`
* `Cslib.Complexity.QBFProtocol.acceptProb_claimVerifier_eq_one_of_suffix`

## References

* [A. Shamir, *IP = PSPACE*][Shamir1992]
* [A. Shen, *IP = SPACE: simplified proof*][Shen1992]
-/

@[expose] public section

namespace Cslib.Complexity.QBFProtocol

open Cslib.Logic.PL Turing.MultiTapeTM Cslib.Probability
open Cslib.ProbOracleComp (runWith acceptProbWith)
open Machine
open scoped ENNReal

/-! ### The verifier -/

/-- **The claim verifier**: run the machine for one step per token from the state with all the
tokens and the single pending claim, and accept when every check passed. -/
noncomputable def claimVerifier (J : ClaimInput) : WordOracleComp Unit Bool :=
  VState.passed <$> loopFrom J

/-- **The claim verifier is strict oracle PPT** in its encoded input. -/
theorem isOraclePPTOn_claimVerifier : IsOraclePPTOn encClaimInput encBool claimVerifier :=
  isOraclePPTOn_loopFrom.map (f := VState.passed) (by fun_prop)

/-! ### The verifier is the protocol -/

/-- **The claim verifier against a word prover is the protocol against its typed prover**: the
machine accepts the claim that `e` has value `c` at the point `r` with the probability that the
token-stream verifier accepts it. -/
theorem acceptProb_claimVerifier_eq (I : LoopInput) (e : ArithQBF ℕ)
    (htok : I.tokens = e.tokens) (he : ∀ w ∈ e.vars, w ∈ I.xs) (r : ℕ → ZMod I.modulus)
    (c : ZMod I.modulus) (P : Prover Unit) :
    acceptProb (claimVerifier (I, ⟨canonPt I.xs r, c.val⟩)) P =
      acceptProbWith (typedRespond I P.respond)
        (verifyAt (samplerOf I) I.degree e [] r c) P.init := by
  have hrun := runWith_verdict P.respond I e he [] r c [] 0 P.init
  rw [Nat.add_zero, List.append_nil] at hrun
  have hcont : (fun x : Bool × P.State => if x.1 then runWith P.respond
      (verdict I ⟨[], [], true⟩ 0) x.2 else PMF.pure (false, x.2)) = PMF.pure := by
    funext x
    obtain ⟨b, t⟩ := x
    cases b
    · rfl
    · simp only [↓reduceIte, verdict_nil, ProbOracleComp.runWith_pure]
  rw [hcont, PMF.bind_pure] at hrun
  rw [acceptProb_eq_acceptProbWith, acceptProbWith, acceptProbWith, ← hrun]
  simp only [claimVerifier, loopFrom, htok]
  rfl

/-- **Soundness of the claim verifier**: over a prime modulus `p` with `6 * ops * D ≤ p`, where
`D = I.degree` bounds the round degree of the formula (`e.maxRoundDegree ≤ I.degree`), every
prover is accepted with probability at most `1 / 3` on a false claim. -/
theorem acceptProb_claimVerifier_le (I : LoopInput) (hp : I.modulus.Prime) (e : ArithQBF ℕ)
    (htok : I.tokens = e.tokens) (hops : 6 * e.ops * I.degree ≤ I.modulus)
    (hdeg : e.maxRoundDegree ≤ I.degree) (he : ∀ w ∈ e.vars, w ∈ I.xs)
    (r : ℕ → ZMod I.modulus) (c : ZMod I.modulus) (hc : e.eval r ≠ c) (P : Prover Unit) :
    acceptProb (claimVerifier (I, ⟨canonPt I.xs r, c.val⟩)) P ≤ 1 / 3 := by
  have : Fact I.modulus.Prime := ⟨hp⟩
  rw [acceptProb_claimVerifier_eq I e htok he r c P]
  refine (acceptProb_verifyAt_le (samplerOf I) I.degree (eval_samplerOf_le I) _ e hdeg hc
    P.init).trans ?_
  refine ENNReal.mul_two_div_le_one_third (Nat.succ_ne_zero _) ?_
  calc 6 * (e.ops * I.degree) = 6 * e.ops * I.degree := by ring
    _ ≤ I.modulus := hops

/-! ### Completeness -/

/-- A deterministic oracle whose replies do not depend on its state, but whose state changes,
gives the same acceptance probability as the same replies with no state. -/
private theorem acceptProbWith_pure_state {Q : Type} {spec : Q → Type} {S : Type}
    (f : (q : Q) → spec q) (upd : Q → S → S) (prog : ProbOracleComp spec Bool) (s : S) :
    acceptProbWith (fun q s => PMF.pure (f q, upd q s)) prog s =
      acceptProbWith (fun q (s : Unit) => PMF.pure (f q, s)) prog () := by
  have hrun := ProbOracleComp.runWith_map_state (fun q s => PMF.pure (f q, upd q s))
    (fun q (s : Unit) => PMF.pure (f q, s)) (fun _ => ()) (fun q s => by
      rw [PMF.pure_map]) prog s
  rw [acceptProbWith, acceptProbWith, ← hrun, PMF.map_comp]
  rfl

section Suffix

variable {F : Type} [CommRing F] [DecidableEq F] (sampler : ProbComp F) (D : ℕ)

/-- **Perfect completeness of the verifier on a stream of tokens, from the suffix queries.** A
stateless prover whose reply to every query whose tokens `q.formula.tokens ++ q.rest` are a suffix
of `T` agrees with the honest reply makes the verifier accept with certainty every true claim
about a formula `e` followed by `rest`, when `e.tokens ++ rest` is a suffix of `T` and the
operators of `e` have bodies of degree at most `D` in their variable. A verifier checking a claim
about `e` asks only such queries: the tokens of a query are always a suffix of those of `e`. -/
theorem run_verifyAt_of_agreesAt_suffix (f : QueryAt F → List F) (T : List (ArithQBF.Kind × ℕ))
    (hf : ∀ q : QueryAt F, q.formula.tokens ++ q.rest <:+ T →
      AgreesAt D (f q) q.formula q.point)
    (e : ArithQBF ℕ) (hD : e.maxRoundDegree ≤ D) (rest : List (ArithQBF.Kind × ℕ))
    (hsuf : e.tokens ++ rest <:+ T) (r : ℕ → F) (s : Unit) :
    runWith (fun q s => PMF.pure (f q, s)) (verifyAt sampler D e rest r (e.eval r)) s =
      PMF.pure (true, s) :=
  run_verifyAt_of_agreesAt_of_closed sampler D f (fun e rest => e.tokens ++ rest <:+ T)
    (fun _ _ h => List.IsSuffix.trans ⟨[(.not, 0)], rfl⟩ h)
    (fun o e₁ e₂ rest h => by
      have h₁ : e₁.tokens ++ (e₂.tokens ++ rest) <:+ T := by
        refine List.IsSuffix.trans ?_ h
        cases o
        · exact ⟨[(.and, 0)], by simp [ArithQBF.tokens]⟩
        · exact ⟨[(.or, 0)], by simp [ArithQBF.tokens]⟩
      exact ⟨h₁, (List.suffix_append _ _).trans h₁⟩)
    (fun o v e rest h => by
      refine List.IsSuffix.trans ?_ h
      cases o
      · exact ⟨[(.ex, v)], by simp [ArithQBF.tokens]⟩
      · exact ⟨[(.all, v)], by simp [ArithQBF.tokens]⟩
      · exact ⟨[(.lin, v)], by simp [ArithQBF.tokens]⟩)
    hf e hD rest hsuf r s

end Suffix

/-- **Completeness of the claim verifier from the suffix queries.** A prover that answers each
message `m` by `g m`, keeping the history of the interaction, is accepted with probability `1` on
a true claim if the decoded reply to every query whose tokens are a suffix of the tokens of the
claim formula agrees with the honest reply. -/
theorem acceptProb_claimVerifier_eq_one_of_suffix (I : LoopInput) (e : ArithQBF ℕ)
    (htok : I.tokens = e.tokens) (hdeg : e.maxRoundDegree ≤ I.degree)
    (he : ∀ w ∈ e.vars, w ∈ I.xs) (r : ℕ → ZMod I.modulus) (c : ZMod I.modulus)
    (hc : e.eval r = c) (g : List Bool → List Bool)
    (hg : ∀ q : QueryAt (ZMod I.modulus), q.formula.tokens ++ q.rest <:+ e.tokens →
      AgreesAt I.degree (decodeTyped I (g (queryMessage I q))) q.formula q.point) :
    acceptProb (claimVerifier (I, ⟨canonPt I.xs r, c.val⟩))
      (Prover.ofHistoryFun fun _ q => g q) = 1 := by
  rw [acceptProb_claimVerifier_eq I e htok he r c]
  set f : QueryAt (ZMod I.modulus) → List (ZMod I.modulus) :=
    fun q => decodeTyped I (g (queryMessage I q))
  have htyped : typedRespond I (Prover.ofHistoryFun fun _ q => g q).respond =
      fun q (h : Interaction.History) => PMF.pure (f q,
        h ++ [(queryMessage I q, g (queryMessage I q))]) := by
    funext q h
    simp only [typedRespond, Prover.ofHistoryFun, PMF.pure_map, f]
  have hrun := run_verifyAt_of_agreesAt_suffix (samplerOf I) I.degree f e.tokens hg e hdeg []
    (by rw [List.append_nil]) r ()
  rw [hc] at hrun
  rw [htyped]
  refine (acceptProbWith_pure_state f (fun q h => h ++ [(queryMessage I q,
    g (queryMessage I q))]) _ _).trans ?_
  rw [acceptProbWith, hrun, PMF.pure_map, PMF.pure_apply]
  exact ite_eq_left rfl

end Cslib.Complexity.QBFProtocol
