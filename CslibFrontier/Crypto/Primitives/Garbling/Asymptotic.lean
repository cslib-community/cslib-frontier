/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.Efficient
public import CslibFrontier.Computability.Probabilistic.PPT
public import CslibFrontier.Crypto.Negligible.Basic

/-!
# Asymptotic simulation privacy of garbling schemes

`Scheme.PrvSimSecure G Φ encFn encΛ` is simulation privacy (`prv.sim`) in the sense of Bellare,
Hoang and Rogaway [BellareHoangRogaway2012], §3.4 (p. 9): for every polynomial-time adversary `B`
there is a polynomial-time simulator `S` whose advantage in the game `PrvSim` (Fig. 5, p. 8) is
negligible in the security parameter. The quantifiers are those of the source, `∀ B ∃ S`.

The library's form differs from the source in the following ways, none of which strengthens or
weakens the notion beyond the change of formal setting:
* An adversary is a uniform strict PPT two-stage program (`TwoStage.IsPPT`): its first stage
  chooses the single `Garble` query `(f, x)` and a state of any type, encoded by any `encσ`; its
  second stage guesses from the state and the answer `(F, X, d)`, or `⊥` on an invalid query.
* The advantage is the two-world advantage `prvSimAdvantage`, the distance between the
  probabilities of answering `true` with the real and the simulated view; it is the absolute value
  of the source's `2 Pr[PrvSim] - 1`.
* Functions and side information are typed, `Fn` and `Λ`, and enter the efficiency predicates
  through the encodings `encFn` and `encΛ`. The simulator runs in time polynomial in all of its
  inputs `(1^k, y, φ)`, as the source's convention (§2.1, p. 4) requires.

`Scheme.PrvSimSecureUniversal G Φ encFn encΛ` is the stronger form with one simulator for every
adversary, `∃ S ∀ B`. With arbitrary side information it is novel to this library: no cited source
states it. Zahur, Rosulek and Evans [ZahurRosulekEvans2015] (§2, p. 5) state `prv.sim` in this
order for one side information, the circuit itself ("there must exist a simulator `S` that takes
input `(1^k, f, f(x))` and whose output is indistinguishable from `(F, X, d)` generated the usual
way"), so its instance at `Φ_circ` is theirs; [BellareHoangRogaway2012] allow any `Φ`, with
`∀ B ∃ S`. Simulation-based security of a protocol built on a garbling scheme needs
this order: a protocol's simulator must serve every environment (as in
`Cslib.Crypto.Protocols.MPC.ProtocolFamily.SemiHonestSecure`), and a reduction builds one garbling
adversary per environment, so a simulator chosen after the adversary would depend on the
environment. Bellare, Hoang and Rogaway's own protocol theorem ([BellareHoangRogaway2012], §7.1,
Theorem 14, p. 35) is stated with `∀ B ∃ S` on both sides instead.

## Main definitions

* `Cslib.Crypto.Garbling.Scheme.PrvSimSecure`: asymptotic simulation privacy.
* `Cslib.Crypto.Garbling.Scheme.PrvSimSecureUniversal`: asymptotic simulation privacy with one
  simulator for every adversary.

## Main results

* `Cslib.Crypto.Garbling.Scheme.PrvSimSecureUniversal.prvSimSecure`: one simulator for every
  adversary gives a simulator for each adversary.

## References

* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
* [S. Zahur, M. Rosulek, D. Evans, *Two Halves Make a Whole: Reducing Data Transfer in Garbled
  Circuits using Half Gates*][ZahurRosulekEvans2015]
-/

public section

namespace Cslib.Crypto.Garbling

open Turing.MultiTapeTM Probability

variable {Fn Λ : Type}

/-- **Simulation privacy** `prv.sim` of [BellareHoangRogaway2012], §3.4 (p. 9), with side
information `Φ`: for every uniform strict PPT adversary `B` there is a simulator `S`, uniform
strict PPT on `(1^k, y, φ)`, whose `prv.sim` advantage against `B` is negligible. Queries are
encoded by `encQuery Fn encFn`, side information by `encΛ`; the module documentation lists the
differences from the source's formal setting. -/
@[expose] def Scheme.PrvSimSecure (G : Scheme Fn) (Φ : SideInfo Fn Λ) (encFn : Fn ↪ List Bool)
    (encΛ : Λ ↪ List Bool) : Prop :=
  ∀ (σ : Type) (encσ : σ ↪ List Bool) (B : ℕ → PrvSimAdversary Fn σ),
    TwoStage.IsPPT encUnit (encQuery Fn encFn) (encSilentOption encPrvView) encBool encσ B →
      ∃ S : ℕ → PrvSimulator Λ,
        IsPPTOn (encPair encUnary (encPair encBits encΛ)) encPrvView
          (fun (k, y, φ) => S k y φ) ∧
        Negligible fun k => prvSimAdvantage G Φ k (S k) (B k)

/-- **Simulation privacy with one simulator for every adversary**, with side information `Φ`: one
simulator `S`, uniform strict PPT on `(1^k, y, φ)`, whose `prv.sim` advantage against every
uniform strict PPT adversary is negligible, in the game `PrvSim` of [BellareHoangRogaway2012]
(Fig. 5, p. 8) and the formal setting of `Scheme.PrvSimSecure`.

For arbitrary `Φ` this notion is novel to this library. It generalizes two sources:
* [ZahurRosulekEvans2015] (§2, p. 5) state `prv.sim` with one simulator ("there must exist a
  simulator `S` that takes input `(1^k, f, f(x))` and whose output is indistinguishable from
  `(F, X, d)` generated the usual way") only for the side information `Φ_circ`, the circuit, so
  its instance at `SideInfo.circ` is their notion;
* [BellareHoangRogaway2012], §3.4 (p. 9), allow any `Φ`, but with a simulator for each adversary.

It implies `Scheme.PrvSimSecure`, the notion of [BellareHoangRogaway2012]
(`Scheme.PrvSimSecureUniversal.prvSimSecure`). It is plausible because the library's schemes meet
it under standard assumptions: point-and-permute garbling with the topology `Φ_topo` from a
pseudorandom function (`PseudorandomFunction.negligible_prvSimAdvantage_simWord`), and half-gates
garbling with `Φ_circ` from circular correlation robustness
(`CircularCorrelationRobust.negligible_prvSimAdvantage_simWord`). It fails for a scheme whose
garbled input is its input (`CslibFrontierTests.Crypto.GarblingScheme`). -/
@[expose] def Scheme.PrvSimSecureUniversal (G : Scheme Fn) (Φ : SideInfo Fn Λ)
    (encFn : Fn ↪ List Bool) (encΛ : Λ ↪ List Bool) : Prop :=
  ∃ S : ℕ → PrvSimulator Λ,
    IsPPTOn (encPair encUnary (encPair encBits encΛ)) encPrvView (fun (k, y, φ) => S k y φ) ∧
      ∀ (σ : Type) (encσ : σ ↪ List Bool) (B : ℕ → PrvSimAdversary Fn σ),
        TwoStage.IsPPT encUnit (encQuery Fn encFn) (encSilentOption encPrvView) encBool encσ B →
          Negligible fun k => prvSimAdvantage G Φ k (S k) (B k)

/-- One simulator for every adversary gives a simulator for each adversary:
`Scheme.PrvSimSecureUniversal` (`∃ S ∀ B`) implies `Scheme.PrvSimSecure` (`∀ B ∃ S`). -/
theorem Scheme.PrvSimSecureUniversal.prvSimSecure {G : Scheme Fn} {Φ : SideInfo Fn Λ}
    {encFn : Fn ↪ List Bool} {encΛ : Λ ↪ List Bool} (h : G.PrvSimSecureUniversal Φ encFn encΛ) :
    G.PrvSimSecure Φ encFn encΛ :=
  let ⟨S, hS, hneg⟩ := h
  fun σ encσ B hB => ⟨S, hS, hneg σ encσ B hB⟩

end Cslib.Crypto.Garbling
