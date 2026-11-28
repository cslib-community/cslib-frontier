/-
Copyright (c) 2026 Phillipp Schoppmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Phillipp Schoppmann
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.Foundations
public import CslibFrontier.Crypto.Primitives.Garbling.Asymptotic
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.PairCapture
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Tactic.PolyTime

/-!
# Asymptotic garbling security notions and BHR12 Propositions 2 and 3

This module completes the asymptotic security definitions of Bellare, Hoang and Rogaway
[BellareHoangRogaway2012], §§3.4–3.7 (ePrint 2012/265, pp. 8–12), in the same uniform strict-PPT
two-stage style (`TwoStage.IsPPT`) as `Cslib.Crypto.Garbling.Scheme.PrvSimSecure` in
`CslibFrontier.Crypto.Primitives.Garbling.Asymptotic`, and lifts the fixed-parameter reductions
and simulators of `CslibFrontier.Crypto.Primitives.Garbling.Foundations` to the full asymptotic
equivalences of Propositions 2 and 3 ([BellareHoangRogaway2012], §§4.2–4.3, pp. 13–15).

For efficient schemes (`Scheme.IsEfficient`) with polynomial-time computable side information `Φ`:
* `prv.sim` implies `prv.ind` (`Scheme.PrvSimSecure.prvIndSecure`), via `isPPT_prvIndToSim`, with
  the factor of `2` absorbed by `Negligible`.
* `prv.ind` implies both `prv.sim` (`Scheme.PrvIndSecure.prvSimSecure`) and the
  universal-simulator form `PrvSimSecureUniversal` (`Scheme.PrvIndSecure.prvSimSecureUniversal`)
  when `Φ` has a polynomial-time `(Φ, ev)`-inverter `M`, via `isPPTOn_prvSimFromInverter` and
  `isPPT_prvSimToInd`.
* `obv.sim` implies `obv.ind` (`Scheme.ObvSimSecure.obvIndSecure`), via `isPPT_obvIndToSim`.
* `obv.ind` implies both `obv.sim` (`Scheme.ObvIndSecure.obvSimSecure`) and the
  universal-simulator form `ObvSimSecureUniversal` (`Scheme.ObvIndSecure.obvSimSecureUniversal`)
  when `Φ` has a polynomial-time `Φ`-inverter `M`, via `isPPTOn_obvSimFromInverter` and
  `isPPT_obvSimToInd`.

Deviations from [BellareHoangRogaway2012] match `Scheme.PrvSimSecure`: adversaries are uniform
strict PPT two-stage programs (`TwoStage.IsPPT`), advantages are two-world `Experiment.advantage`
values (the paper's `2 Pr[·] - 1` up to sign) or `Experiment.succProbability` for `aut`, and
function/side-information types carry explicit encodings `encFn` and `encΛ`.
`Scheme.IsEfficient` requires polynomial-time length readers `f.n`, `f.m` rather than the source's
linear-time ones. `Scheme.AutSecure` also corresponds to the authenticity definition of
[BonehShoup2023] (version 0.6, §23.3.5, Definition 23.3, pp. 1026–1027). The obliviousness
definition there (Definition 23.2, same pages) fixes one circuit with two inputs, so it corresponds
to `Scheme.ObvIndSecure` at the side information `SideInfo.circ`, not for arbitrary `Φ`.

The `*Universal` conclusions (`∃ S ∀ B`) strengthen Propositions 2 and 3 as stated (`∀ B ∃ S`):
the source's proofs define the simulator from the inverter `M` before the adversary `B`
([BellareHoangRogaway2012], pp. 13–15), and the `∀ B ∃ S` forms follow from them.

## Main definitions

* `Cslib.Crypto.Garbling.encIndToSimState`: encoding of `IndToSimState`.
* `Cslib.Crypto.Garbling.Scheme.PrvIndSecure`: asymptotic `prv.ind` security.
* `Cslib.Crypto.Garbling.Scheme.ObvIndSecure`: asymptotic `obv.ind` security.
* `Cslib.Crypto.Garbling.Scheme.ObvSimSecure`: asymptotic `obv.sim` security (`∀ B ∃ S`).
* `Cslib.Crypto.Garbling.Scheme.ObvSimSecureUniversal`: asymptotic `obv.sim` with one simulator for
  every adversary (`∃ S ∀ B`, novel to this library).
* `Cslib.Crypto.Garbling.Scheme.AutSecure`: asymptotic `aut` authenticity.

## Main results

* `Cslib.Crypto.Garbling.Scheme.isPPTOn_garble`, `isPPTOn_prvView`, `isPPTOn_obvView`:
  uniform strict-PPT execution of efficient garbling schemes and their views.
* `Cslib.Crypto.Garbling.isPPT_prvIndToSim`, `isPPTOn_prvSimFromInverter`, `isPPT_prvSimToInd`,
  `isPPT_obvIndToSim`, `isPPTOn_obvSimFromInverter`, `isPPT_obvSimToInd`: strict-PPT efficiency
  certificates for the BHR12 reductions and simulators.
* `Cslib.Crypto.Garbling.Scheme.PrvSimSecure.prvIndSecure`,
  `Cslib.Crypto.Garbling.Scheme.PrvIndSecure.prvSimSecureUniversal`,
  `Cslib.Crypto.Garbling.Scheme.PrvIndSecure.prvSimSecure`: asymptotic BHR12 Proposition 2.
* `Cslib.Crypto.Garbling.Scheme.ObvSimSecure.obvIndSecure`,
  `Cslib.Crypto.Garbling.Scheme.ObvIndSecure.obvSimSecureUniversal`,
  `Cslib.Crypto.Garbling.Scheme.ObvIndSecure.obvSimSecure`: asymptotic BHR12 Proposition 3.

## References

* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023]
-/

public section

namespace Cslib.Crypto.Garbling

open Turing.MultiTapeTM Probability

variable {Fn Λ σ : Type}

/-! ## Encodings -/

/-- The encoding of an `IndToSimState Fn σ`: `state` framed, `bit` framed, then `pair` encoded by
`encMessagePair (encQuery Fn encFn)`. -/
enc_structure encIndToSimState (Fn : Type) (σ : Type) (encFn : Fn ↪ List Bool)
    (encσ : σ ↪ List Bool) : IndToSimState Fn σ where
  state : encσ, bit : encBool, pair : (encMessagePair (encQuery Fn encFn))

/-! ## Asymptotic security definitions -/

/-- **Indistinguishability privacy** `prv.ind` of [BellareHoangRogaway2012], §3.4 (pp. 8–9): for
every uniform strict PPT two-stage adversary `A` choosing a pair of queries encoded by
`encMessagePair (encQuery Fn encFn)` and receiving `(F, X, d)` (or `⊥`), its `prv.ind` advantage is
negligible in the security parameter. -/
@[expose] def Scheme.PrvIndSecure [DecidableEq Λ] (G : Scheme Fn) (Φ : SideInfo Fn Λ)
    (encFn : Fn ↪ List Bool) : Prop :=
  ∀ (σ : Type) (encσ : σ ↪ List Bool) (A : ℕ → PrvIndAdversary Fn σ),
    TwoStage.IsPPT encUnit (encMessagePair (encQuery Fn encFn)) (encOption encPrvView) encBool
      encσ A →
      Negligible fun k => prvIndAdvantage G Φ k (A k)

/-- **Indistinguishability obliviousness** `obv.ind` of [BellareHoangRogaway2012], §3.5 (pp. 9–10):
for every uniform strict PPT two-stage adversary `A` choosing a pair of queries encoded by
`encMessagePair (encQuery Fn encFn)` and receiving `(F, X)` (or `⊥`), its `obv.ind` advantage is
negligible in the security parameter. At the side information `SideInfo.circ` it is the
obliviousness of [BonehShoup2023] (version 0.6, §23.3.5, Definition 23.2, pp. 1026–1027), which
fixes one circuit with two inputs. -/
@[expose] def Scheme.ObvIndSecure [DecidableEq Λ] (G : Scheme Fn) (Φ : SideInfo Fn Λ)
    (encFn : Fn ↪ List Bool) : Prop :=
  ∀ (σ : Type) (encσ : σ ↪ List Bool) (A : ℕ → ObvIndAdversary Fn σ),
    TwoStage.IsPPT encUnit (encMessagePair (encQuery Fn encFn)) (encOption encObvView) encBool
      encσ A →
      Negligible fun k => obvIndAdvantage G Φ k (A k)

/-- **Simulation obliviousness** `obv.sim` of [BellareHoangRogaway2012], §3.5 (pp. 9–10), with
side information `Φ`: for every uniform strict PPT adversary `B` there is a simulator `S`, uniform
strict PPT on `(1^k, φ)`, whose `obv.sim` advantage against `B` is negligible. -/
@[expose] def Scheme.ObvSimSecure (G : Scheme Fn) (Φ : SideInfo Fn Λ) (encFn : Fn ↪ List Bool)
    (encΛ : Λ ↪ List Bool) : Prop :=
  ∀ (σ : Type) (encσ : σ ↪ List Bool) (B : ℕ → ObvSimAdversary Fn σ),
    TwoStage.IsPPT encUnit (encQuery Fn encFn) (encOption encObvView) encBool encσ B →
      ∃ S : ℕ → ObvSimulator Λ,
        IsPPTOn (encPair encUnary encΛ) encObvView (fun (k, φ) => S k φ) ∧
        Negligible fun k => obvSimAdvantage G Φ k (S k) (B k)

/-- **Simulation obliviousness with one simulator for every adversary**, with side information
`Φ`: one simulator `S`, uniform strict PPT on `(1^k, φ)`, whose `obv.sim` advantage against every
uniform strict PPT adversary is negligible, in the game `ObvSim` of [BellareHoangRogaway2012],
§3.5 (pp. 9–10).

For arbitrary `Φ` this quantifier order (`∃ S ∀ B`) is novel to this library:
[BellareHoangRogaway2012], §3.5, quantifies `∀ B ∃ S`, and
`Scheme.ObvSimSecureUniversal.obvSimSecure` recovers that standard notion. It is plausible because
the standard inverter-based construction `obvSimFromInverter` yields a single universal simulator
from `ObvIndSecure` (`Scheme.ObvIndSecure.obvSimSecureUniversal`). -/
@[expose] def Scheme.ObvSimSecureUniversal (G : Scheme Fn) (Φ : SideInfo Fn Λ)
    (encFn : Fn ↪ List Bool) (encΛ : Λ ↪ List Bool) : Prop :=
  ∃ S : ℕ → ObvSimulator Λ,
    IsPPTOn (encPair encUnary encΛ) encObvView (fun (k, φ) => S k φ) ∧
      ∀ (σ : Type) (encσ : σ ↪ List Bool) (B : ℕ → ObvSimAdversary Fn σ),
        TwoStage.IsPPT encUnit (encQuery Fn encFn) (encOption encObvView) encBool encσ B →
          Negligible fun k => obvSimAdvantage G Φ k (S k) (B k)

/-- One simulator for every adversary gives a simulator for each adversary:
`Scheme.ObvSimSecureUniversal` (`∃ S ∀ B`) implies `Scheme.ObvSimSecure` (`∀ B ∃ S`). -/
theorem Scheme.ObvSimSecureUniversal.obvSimSecure {G : Scheme Fn} {Φ : SideInfo Fn Λ}
    {encFn : Fn ↪ List Bool} {encΛ : Λ ↪ List Bool}
    (h : G.ObvSimSecureUniversal Φ encFn encΛ) : G.ObvSimSecure Φ encFn encΛ :=
  let ⟨S, hS, hneg⟩ := h
  fun σ encσ B hB => ⟨S, hS, hneg σ encσ B hB⟩

/-- **Authenticity** `aut` of [BellareHoangRogaway2012], §3.6 (p. 10) and [BonehShoup2023]
(version 0.6, §23.3.5, Definition 23.3, pp. 1026–1027): for every uniform strict PPT two-stage
adversary `A` choosing a query encoded by `encQuery Fn encFn` and receiving `(F, X)`, its
probability of producing a valid forgery differing from `Ev(F, X)` is negligible in the security
parameter. -/
@[expose] def Scheme.AutSecure (G : Scheme Fn) (encFn : Fn ↪ List Bool) : Prop :=
  ∀ (σ : Type) (encσ : σ ↪ List Bool) (A : ℕ → AutAdversary Fn σ),
    TwoStage.IsPPT encUnit (encQuery Fn encFn) encObvView encBits encσ A →
      Negligible fun k => autAdvantage G k (A k)

/-! ## Strict-PPT execution of efficient schemes -/

/-- Library infrastructure (no cited result): garbling `G.garble k f` is uniform strict PPT on
`(1^k, f)` whenever `G` is efficient. -/
theorem Scheme.isPPTOn_garble {G : Scheme Fn} {encFn : Fn ↪ List Bool}
    (heff : G.IsEfficient encFn) :
    IsPPTOn (encPair encUnary encFn) encGarbled (fun p : ℕ × Fn => G.garble p.1 p.2) := by
  have h1 := ComputableInPolyTime.fst (encPair encUnary encFn) encBits
  have h2 := ComputableInPolyTime.snd (encPair encUnary encFn) encBits
  have hgb : ComputableInPolyTime (fun p : (ℕ × Fn) × List Bool => G.gb p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encFn) encBits) encGarbled :=
    heff.gb.comp (h1.fst'.prod (h1.snd'.prod h2))
  exact (IsPPTOn.of_seeded heff.coins hgb).congr fun ⟨k, f⟩ => by
    simp only [Scheme.garble, bind_pure_comp]

/-- Garbling `q.fn` and post-processing the garbled triple together with the garbled input
`En(e, q.input)` is uniform strict PPT on `(1^k, q)` whenever `G` is efficient and the
post-processing is polynomial-time computable. -/
private theorem Scheme.isPPTOn_garble_post {V : Type} {encV : V ↪ List Bool} {G : Scheme Fn}
    {encFn : Fn ↪ List Bool} (heff : G.IsEfficient encFn) {post : Scheme.Garbled → List Bool → V}
    (hpost : ComputableInPolyTime (fun p : Scheme.Garbled × List Bool => post p.1 p.2)
      (encPair encGarbled encBits) encV) :
    IsPPTOn (encPair encUnary (encQuery Fn encFn)) encV (fun p : ℕ × Query Fn => do
      let g ← G.garble p.1 p.2.fn
      return post g (G.encode g.encInfo p.2.input)) := by
  have hprep : ComputableInPolyTime (fun p : ℕ × Query Fn => (p.1, p.2.fn))
      (encPair encUnary (encQuery Fn encFn)) (encPair encUnary encFn) :=
    (ComputableInPolyTime.fst encUnary (encQuery Fn encFn)).prod
      (encQuery_fn_polyTime Fn encFn (ComputableInPolyTime.snd encUnary (encQuery Fn encFn)))
  have hgarb := (isPPTOn_garble heff).preprocess hprep
  have hfst := ComputableInPolyTime.fst (encPair encUnary (encQuery Fn encFn)) encGarbled
  have hsnd := ComputableInPolyTime.snd (encPair encUnary (encQuery Fn encFn)) encGarbled
  have henc := heff.encode.comp
    ((encGarbled_encInfo_polyTime hsnd).prod (encQuery_input_polyTime Fn encFn hfst.snd'))
  exact hgarb.map_pair (hpost.comp (hsnd.prod henc))

/-- Library infrastructure (no cited result): sampling the real privacy view `G.prvView k q` is
uniform strict PPT on `(1^k, q)` whenever `G` is efficient. -/
theorem Scheme.isPPTOn_prvView {G : Scheme Fn} {encFn : Fn ↪ List Bool}
    (heff : G.IsEfficient encFn) :
    IsPPTOn (encPair encUnary (encQuery Fn encFn)) encPrvView
      (fun p : ℕ × Query Fn => G.prvView p.1 p.2) := by
  have hg := ComputableInPolyTime.fst encGarbled encBits
  exact isPPTOn_garble_post heff (post := fun g x => (⟨g.fn, x, g.decInfo⟩ : PrvView))
    (encPrvView_mk_polyTime (encGarbled_fn_polyTime hg)
      (ComputableInPolyTime.snd encGarbled encBits) (encGarbled_decInfo_polyTime hg))

/-- Library infrastructure (no cited result): sampling the real obliviousness view `G.obvView k q`
is uniform strict PPT on `(1^k, q)` whenever `G` is efficient. -/
theorem Scheme.isPPTOn_obvView {G : Scheme Fn} {encFn : Fn ↪ List Bool}
    (heff : G.IsEfficient encFn) :
    IsPPTOn (encPair encUnary (encQuery Fn encFn)) encObvView
      (fun p : ℕ × Query Fn => G.obvView p.1 p.2) :=
  isPPTOn_garble_post heff (post := fun g x => (⟨g.fn, x⟩ : ObvView))
    (encObvView_mk_polyTime (encGarbled_fn_polyTime (ComputableInPolyTime.fst encGarbled encBits))
      (ComputableInPolyTime.snd encGarbled encBits))

/-! ## Strict-PPT efficiency witnesses for BHR12 reductions and simulators -/

/-- The `obv.ind` validity of a pair, `Φ(f₀) = Φ(f₁)` and both inputs of `f₀.n` bits, is decided in
polynomial time; `prvIndValid_polyTime` adds the output condition. -/
private theorem obvIndValid_polyTime [DecidableEq Λ] {G : Scheme Fn} {Φ : SideInfo Fn Λ}
    {encFn : Fn ↪ List Bool} {encΛ : Λ ↪ List Bool}
    (heff : G.IsEfficient encFn) (hphi : ComputableInPolyTime Φ.phi encFn encΛ) :
    ComputableInPolyTime (fun pair : MessagePair (Query Fn) => decide (obvIndValid G Φ pair))
      (encMessagePair (encQuery Fn encFn)) encBool := by
  have hq₀ := encMessagePair_msg₀_polyTime
    (ComputableInPolyTime.id' (encIn := encMessagePair (encQuery Fn encFn)))
  have hq₁ := encMessagePair_msg₁_polyTime
    (ComputableInPolyTime.id' (encIn := encMessagePair (encQuery Fn encFn)))
  have hf₀ := encQuery_fn_polyTime Fn encFn hq₀
  have h1 := (hphi.comp hf₀).decide_eq' (hphi.comp (encQuery_fn_polyTime Fn encFn hq₁))
  have h2 := (ComputableInPolyTime.length_bits_comp
    (encQuery_input_polyTime Fn encFn hq₀)).decide_eq' (heff.inLen.comp hf₀)
  have h3 := (ComputableInPolyTime.length_bits_comp
    (encQuery_input_polyTime Fn encFn hq₁)).decide_eq' (heff.inLen.comp hf₀)
  exact (h1.decide_and (h2.decide_and h3)).of_enc_eq fun pair =>
    congrArg encBool (by simp only [obvIndValid]; exact decide_eq_decide.mpr Iff.rfl)

/-- The `prv.ind` validity of a pair, `obv.ind` validity and `ev(f₀, x₀) = ev(f₁, x₁)`, is decided
in polynomial time. -/
private theorem prvIndValid_polyTime [DecidableEq Λ] {G : Scheme Fn} {Φ : SideInfo Fn Λ}
    {encFn : Fn ↪ List Bool} {encΛ : Λ ↪ List Bool}
    (heff : G.IsEfficient encFn) (hphi : ComputableInPolyTime Φ.phi encFn encΛ) :
    ComputableInPolyTime (fun pair : MessagePair (Query Fn) => decide (prvIndValid G Φ pair))
      (encMessagePair (encQuery Fn encFn)) encBool := by
  have hq₀ := encMessagePair_msg₀_polyTime
    (ComputableInPolyTime.id' (encIn := encMessagePair (encQuery Fn encFn)))
  have hq₁ := encMessagePair_msg₁_polyTime
    (ComputableInPolyTime.id' (encIn := encMessagePair (encQuery Fn encFn)))
  have hev₀ := heff.ev.comp
    ((encQuery_fn_polyTime Fn encFn hq₀).prod (encQuery_input_polyTime Fn encFn hq₀))
  have hev₁ := heff.ev.comp
    ((encQuery_fn_polyTime Fn encFn hq₁).prod (encQuery_input_polyTime Fn encFn hq₁))
  exact ((obvIndValid_polyTime heff hphi).decide_and (hev₀.decide_eq' hev₁)).of_enc_eq fun pair =>
    congrArg encBool (by
      simp only [prvIndValid, obvIndValid, and_assoc]; exact decide_eq_decide.mpr Iff.rfl)

/-- The reduction from an indistinguishability adversary `A` to a simulation adversary, with
validity predicate `valid`, preserves uniform strict PPT when `valid` is decided in polynomial time.
`prvIndToSim` and `obvIndToSim` are its instances at `prvIndValid` and `obvIndValid`. -/
private theorem isPPT_indToSim {V : Type} {encV : V ↪ List Bool} {encFn : Fn ↪ List Bool}
    {encσ : σ ↪ List Bool} (valid : MessagePair (Query Fn) → Prop) [DecidablePred valid]
    (hvalid : ComputableInPolyTime (fun pair => decide (valid pair))
      (encMessagePair (encQuery Fn encFn)) encBool)
    {A : ℕ → TwoStage Unit (MessagePair (Query Fn)) (Option V) Bool σ}
    (hA : TwoStage.IsPPT encUnit (encMessagePair (encQuery Fn encFn)) (encOption encV) encBool
      encσ A) :
    TwoStage.IsPPT encUnit (encQuery Fn encFn) (encOption encV) encBool
      (encIndToSimState Fn σ encFn encσ) (fun k =>
        { choose := fun _ => do
            let (pair, st) ← (A k).choose ()
            let c ← ProbComp.uniform Bool
            pure (if valid pair then pair.select c else pair.msg₀, ⟨st, c, pair⟩)
          guess := fun s view => do
            let guess ← (A k).guess s.state (if valid s.pair then view else none)
            pure (guess == s.bit) }) where
  choose := by
    let E₀ := encPair (encPair encUnary encUnit)
      (encPair (encMessagePair (encQuery Fn encFn)) encσ)
    let E := encPair E₀ encBool
    have hpair : ComputableInPolyTime
        (fun p : ((ℕ × Unit) × (MessagePair (Query Fn) × σ)) × Bool => p.1.2.1)
        E (encMessagePair (encQuery Fn encFn)) :=
      (ComputableInPolyTime.fst E₀ encBool).snd'.fst'
    have hst : ComputableInPolyTime
        (fun p : ((ℕ × Unit) × (MessagePair (Query Fn) × σ)) × Bool => p.1.2.2) E encσ :=
      (ComputableInPolyTime.fst E₀ encBool).snd'.snd'
    have hc : ComputableInPolyTime
        (fun p : ((ℕ × Unit) × (MessagePair (Query Fn) × σ)) × Bool => p.2) E encBool :=
      ComputableInPolyTime.snd E₀ encBool
    have hm₀ := encMessagePair_msg₀_polyTime hpair
    have hm₁ := encMessagePair_msg₁_polyTime hpair
    have hsel : ComputableInPolyTime
        (fun p : ((ℕ × Unit) × (MessagePair (Query Fn) × σ)) × Bool => p.1.2.1.select p.2)
        E (encQuery Fn encFn) :=
      (ComputableInPolyTime.ite hc hm₁ hm₀).of_enc_eq fun p => by
        cases p.2 <;> rfl
    have hq := ComputableInPolyTime.ite_decide (hvalid.comp hpair) hsel hm₀
    have hstate := encIndToSimState_mk_polyTime Fn σ encFn encσ hst hc hpair
    exact (hA.choose.bind_pair ((isPPTOn_uniform_bool E₀).map_pair (hq.prod hstate))).congr
      fun x => by simp only [bind_pure_comp]
  guess := by
    let E := encPair encUnary (encPair (encIndToSimState Fn σ encFn encσ) (encOption encV))
    have hk := ComputableInPolyTime.fst encUnary
      (encPair (encIndToSimState Fn σ encFn encσ) (encOption encV))
    have hs := (ComputableInPolyTime.snd encUnary
      (encPair (encIndToSimState Fn σ encFn encσ) (encOption encV))).fst'
    have hview := (ComputableInPolyTime.snd encUnary
      (encPair (encIndToSimState Fn σ encFn encσ) (encOption encV))).snd'
    have hst := encIndToSimState_state_polyTime Fn σ encFn encσ hs
    have hcond := hvalid.comp (encIndToSimState_pair_polyTime Fn σ encFn encσ hs)
    have harg := ComputableInPolyTime.ite_decide hcond hview (ComputableInPolyTime.const none)
    have hbit := encIndToSimState_bit_polyTime Fn σ encFn encσ
      (hs.comp (ComputableInPolyTime.fst E encBool))
    have hpost := (ComputableInPolyTime.snd E encBool).beq hbit
    exact ((hA.guess.preprocess (hk.prod (hst.prod harg))).map_pair hpost).congr
      fun ⟨k, s, view⟩ => by simp only [bind_pure_comp, Function.comp_def]

/-- Library infrastructure (no cited result): `prvIndToSim` preserves uniform strict PPT when
`G` is efficient and `Φ.phi` is polynomial-time computable. -/
theorem isPPT_prvIndToSim [DecidableEq Λ] {G : Scheme Fn} {Φ : SideInfo Fn Λ}
    {encFn : Fn ↪ List Bool} {encΛ : Λ ↪ List Bool} {encσ : σ ↪ List Bool}
    {A : ℕ → PrvIndAdversary Fn σ}
    (heff : G.IsEfficient encFn) (hphi : ComputableInPolyTime Φ.phi encFn encΛ)
    (hA : TwoStage.IsPPT encUnit (encMessagePair (encQuery Fn encFn)) (encOption encPrvView)
      encBool encσ A) :
    TwoStage.IsPPT encUnit (encQuery Fn encFn) (encOption encPrvView) encBool
      (encIndToSimState Fn σ encFn encσ) (fun k => prvIndToSim G Φ (A k)) :=
  isPPT_indToSim (prvIndValid G Φ) (prvIndValid_polyTime heff hphi) hA

/-- Library infrastructure (no cited result): `obvIndToSim` preserves uniform strict PPT when
`G` is efficient and `Φ.phi` is polynomial-time computable. -/
theorem isPPT_obvIndToSim [DecidableEq Λ] {G : Scheme Fn} {Φ : SideInfo Fn Λ}
    {encFn : Fn ↪ List Bool} {encΛ : Λ ↪ List Bool} {encσ : σ ↪ List Bool}
    {A : ℕ → ObvIndAdversary Fn σ}
    (heff : G.IsEfficient encFn) (hphi : ComputableInPolyTime Φ.phi encFn encΛ)
    (hA : TwoStage.IsPPT encUnit (encMessagePair (encQuery Fn encFn)) (encOption encObvView)
      encBool encσ A) :
    TwoStage.IsPPT encUnit (encQuery Fn encFn) (encOption encObvView) encBool
      (encIndToSimState Fn σ encFn encσ) (fun k => obvIndToSim G Φ (A k)) :=
  isPPT_indToSim (obvIndValid G Φ) (obvIndValid_polyTime heff hphi) hA

/-- Library infrastructure (no cited result): the simulator `prvSimFromInverter` built from a
polynomial-time `(Φ, ev)`-inverter `M` is uniform strict PPT on `(1^k, y, φ)` when `G` is
efficient. -/
theorem isPPTOn_prvSimFromInverter {G : Scheme Fn} {encFn : Fn ↪ List Bool}
    {encΛ : Λ ↪ List Bool} {M : Λ → List Bool → Query Fn}
    (heff : G.IsEfficient encFn)
    (hM : ComputableInPolyTime (fun p : Λ × List Bool => M p.1 p.2)
      (encPair encΛ encBits) (encQuery Fn encFn)) :
    IsPPTOn (encPair encUnary (encPair encBits encΛ)) encPrvView
      (fun (k, y, φ) => prvSimFromInverter G k M y φ) := by
  have hk := ComputableInPolyTime.fst encUnary (encPair encBits encΛ)
  have hy := (ComputableInPolyTime.snd encUnary (encPair encBits encΛ)).fst'
  have hphi := (ComputableInPolyTime.snd encUnary (encPair encBits encΛ)).snd'
  have hprep := hk.prod (hM.comp (hphi.prod hy))
  exact (Scheme.isPPTOn_prvView heff).preprocess hprep

/-- Library infrastructure (no cited result): `prvSimToInd` preserves uniform strict PPT when `G`
is efficient and `Φ.phi` and `M` are polynomial-time computable. -/
theorem isPPT_prvSimToInd {G : Scheme Fn} {Φ : SideInfo Fn Λ} {encFn : Fn ↪ List Bool}
    {encΛ : Λ ↪ List Bool} {encσ : σ ↪ List Bool} {M : Λ → List Bool → Query Fn}
    {B : ℕ → PrvSimAdversary Fn σ}
    (heff : G.IsEfficient encFn) (hphi : ComputableInPolyTime Φ.phi encFn encΛ)
    (hM : ComputableInPolyTime (fun p : Λ × List Bool => M p.1 p.2)
      (encPair encΛ encBits) (encQuery Fn encFn))
    (hB : TwoStage.IsPPT encUnit (encQuery Fn encFn) (encOption encPrvView) encBool encσ B) :
    TwoStage.IsPPT encUnit (encMessagePair (encQuery Fn encFn)) (encOption encPrvView) encBool
      encσ (fun k => prvSimToInd G Φ M (B k)) where
  choose := by
    let E := encPair (encPair encUnary encUnit) (encPair (encQuery Fn encFn) encσ)
    have hq := (ComputableInPolyTime.snd (encPair encUnary encUnit)
      (encPair (encQuery Fn encFn) encσ)).fst'
    have hst := (ComputableInPolyTime.snd (encPair encUnary encUnit)
      (encPair (encQuery Fn encFn) encσ)).snd'
    have hfn := encQuery_fn_polyTime Fn encFn hq
    have hx := encQuery_input_polyTime Fn encFn hq
    have hM' := hM.comp ((hphi.comp hfn).prod (heff.ev.comp (hfn.prod hx)))
    have hpost := (encMessagePair_mk_polyTime hM' hq).prod hst
    exact (hB.choose.map_pair hpost).congr fun ⟨k, ⟨⟩⟩ => by
      simp only [prvSimToInd, bind_pure_comp, Function.comp_def]
  guess := hB.guess

private theorem obvInverterQuery_polyTime {G : Scheme Fn} {encFn : Fn ↪ List Bool}
    {encΛ : Λ ↪ List Bool} {M : Λ → Fn}
    (heff : G.IsEfficient encFn) (hM : ComputableInPolyTime M encΛ encFn) :
    ComputableInPolyTime (fun φ : Λ => obvInverterQuery G M φ) encΛ (encQuery Fn encFn) := by
  have hzeros : ComputableInPolyTime (fun φ : Λ => List.replicate (G.inLen (M φ)) false) encΛ
      encBits :=
    (ComputableInPolyTime.bitsReplicate false).comp (heff.inLen.comp hM)
  exact (encQuery_mk_polyTime Fn encFn hM hzeros).of_enc_eq fun _ => rfl

/-- Library infrastructure (no cited result): the simulator `obvSimFromInverter` built from a
polynomial-time `Φ`-inverter `M` is uniform strict PPT on `(1^k, φ)` when `G` is efficient. -/
theorem isPPTOn_obvSimFromInverter {G : Scheme Fn} {encFn : Fn ↪ List Bool}
    {encΛ : Λ ↪ List Bool} {M : Λ → Fn}
    (heff : G.IsEfficient encFn) (hM : ComputableInPolyTime M encΛ encFn) :
    IsPPTOn (encPair encUnary encΛ) encObvView
      (fun (k, φ) => obvSimFromInverter G k M φ) := by
  have hprep := (ComputableInPolyTime.fst encUnary encΛ).prod
    ((obvInverterQuery_polyTime heff hM).comp (ComputableInPolyTime.snd encUnary encΛ))
  exact (Scheme.isPPTOn_obvView heff).preprocess hprep

/-- Library infrastructure (no cited result): `obvSimToInd` preserves uniform strict PPT when `G`
is efficient and `Φ.phi` and `M` are polynomial-time computable. -/
theorem isPPT_obvSimToInd {G : Scheme Fn} {Φ : SideInfo Fn Λ} {encFn : Fn ↪ List Bool}
    {encΛ : Λ ↪ List Bool} {encσ : σ ↪ List Bool} {M : Λ → Fn}
    {B : ℕ → ObvSimAdversary Fn σ}
    (heff : G.IsEfficient encFn) (hphi : ComputableInPolyTime Φ.phi encFn encΛ)
    (hM : ComputableInPolyTime M encΛ encFn)
    (hB : TwoStage.IsPPT encUnit (encQuery Fn encFn) (encOption encObvView) encBool encσ B) :
    TwoStage.IsPPT encUnit (encMessagePair (encQuery Fn encFn)) (encOption encObvView) encBool
      encσ (fun k => obvSimToInd G Φ M (B k)) where
  choose := by
    have hq := (ComputableInPolyTime.snd (encPair encUnary encUnit)
      (encPair (encQuery Fn encFn) encσ)).fst'
    have hst := (ComputableInPolyTime.snd (encPair encUnary encUnit)
      (encPair (encQuery Fn encFn) encσ)).snd'
    have hfn := encQuery_fn_polyTime Fn encFn hq
    have hinv := (obvInverterQuery_polyTime heff hM).comp (hphi.comp hfn)
    have hpost := (encMessagePair_mk_polyTime hinv hq).prod hst
    exact (hB.choose.map_pair hpost).congr fun ⟨k, ⟨⟩⟩ => by
      simp only [obvSimToInd, bind_pure_comp, Function.comp_def]
  guess := hB.guess

/-! ## BHR12 Propositions 2 and 3 -/

/-- **BHR12 Proposition 2 (`prv.sim → prv.ind`)** ([BellareHoangRogaway2012], §4.2, pp. 13–14):
for an efficient garbling scheme `G` with compatible polynomial-time side information `Φ`,
simulation privacy `PrvSimSecure` implies indistinguishability privacy `PrvIndSecure`. The factor
of `2` in `prvIndAdvantage_eq_two_mul_prvSimAdvantage_prvIndToSim` is absorbed by `Negligible`. -/
theorem Scheme.PrvSimSecure.prvIndSecure [DecidableEq Λ] {G : Scheme Fn} {Φ : SideInfo Fn Λ}
    {encFn : Fn ↪ List Bool} {encΛ : Λ ↪ List Bool}
    (hCompat : Φ.Compatible G) (heff : G.IsEfficient encFn)
    (hphi : ComputableInPolyTime Φ.phi encFn encΛ)
    (hsec : G.PrvSimSecure Φ encFn encΛ) : G.PrvIndSecure Φ encFn := by
  intro σ encσ A hA
  obtain ⟨S, _, hneg⟩ := hsec _ _ _ (isPPT_prvIndToSim heff hphi hA)
  have htwo : Negligible fun k => 2 * prvSimAdvantage G Φ k (S k) (prvIndToSim G Φ (A k)) := by
    simpa only [two_mul] using hneg.add_fun hneg
  exact htwo.congr' (Filter.Eventually.of_forall fun k =>
    (prvIndAdvantage_eq_two_mul_prvSimAdvantage_prvIndToSim G Φ hCompat k (S k) (A k)).symm)

/-- **BHR12 Proposition 2 (`prv.ind → prv.sim` with a universal simulator)**
([BellareHoangRogaway2012], §4.2, pp. 13–14): for an efficient garbling scheme `G` with compatible
polynomial-time side information `Φ` and a polynomial-time `(Φ, ev)`-inverter `M`, `PrvIndSecure`
implies `PrvSimSecureUniversal`, because `prvSimFromInverter G k M` does not depend on the
adversary. This universal form (`∃ S ∀ B`) strengthens Proposition 2 as stated (`∀ B ∃ S`, which is
`Scheme.PrvIndSecure.prvSimSecure`); the source's proof yields it, since its simulator is defined
from `M` before the adversary (pp. 13–14). -/
theorem Scheme.PrvIndSecure.prvSimSecureUniversal [DecidableEq Λ] {G : Scheme Fn}
    {Φ : SideInfo Fn Λ} {encFn : Fn ↪ List Bool} {encΛ : Λ ↪ List Bool}
    (hCompat : Φ.Compatible G) (heff : G.IsEfficient encFn)
    (hphi : ComputableInPolyTime Φ.phi encFn encΛ) {M : Λ → List Bool → Query Fn}
    (hInv : Φ.IsEvInverter G M)
    (hM : ComputableInPolyTime (fun p : Λ × List Bool => M p.1 p.2)
      (encPair encΛ encBits) (encQuery Fn encFn))
    (hsec : G.PrvIndSecure Φ encFn) : G.PrvSimSecureUniversal Φ encFn encΛ := by
  refine ⟨fun k => prvSimFromInverter G k M, isPPTOn_prvSimFromInverter heff hM,
    fun σ encσ B hB => ?_⟩
  have hneg := hsec _ _ _ (isPPT_prvSimToInd heff hphi hM hB)
  exact hneg.congr' (Filter.Eventually.of_forall fun k =>
    (prvSimAdvantage_prvSimFromInverter_eq G Φ hCompat hInv k (B k)).symm)

/-- **BHR12 Proposition 2 (`prv.ind → prv.sim`)** ([BellareHoangRogaway2012], §4.2, pp. 13–14):
for an efficient garbling scheme `G` with compatible polynomial-time side information `Φ` and a
polynomial-time `(Φ, ev)`-inverter `M`, indistinguishability privacy `PrvIndSecure` implies
simulation privacy `PrvSimSecure`. -/
theorem Scheme.PrvIndSecure.prvSimSecure [DecidableEq Λ] {G : Scheme Fn} {Φ : SideInfo Fn Λ}
    {encFn : Fn ↪ List Bool} {encΛ : Λ ↪ List Bool}
    (hCompat : Φ.Compatible G) (heff : G.IsEfficient encFn)
    (hphi : ComputableInPolyTime Φ.phi encFn encΛ) {M : Λ → List Bool → Query Fn}
    (hInv : Φ.IsEvInverter G M)
    (hM : ComputableInPolyTime (fun p : Λ × List Bool => M p.1 p.2)
      (encPair encΛ encBits) (encQuery Fn encFn))
    (hsec : G.PrvIndSecure Φ encFn) : G.PrvSimSecure Φ encFn encΛ :=
  (hsec.prvSimSecureUniversal hCompat heff hphi hInv hM).prvSimSecure

/-- **BHR12 Proposition 3 (`obv.sim → obv.ind`)** ([BellareHoangRogaway2012], §4.3, pp. 14–15):
for an efficient garbling scheme `G` with compatible polynomial-time side information `Φ`,
simulation obliviousness `ObvSimSecure` implies indistinguishability obliviousness
`ObvIndSecure`. -/
theorem Scheme.ObvSimSecure.obvIndSecure [DecidableEq Λ] {G : Scheme Fn} {Φ : SideInfo Fn Λ}
    {encFn : Fn ↪ List Bool} {encΛ : Λ ↪ List Bool}
    (hCompat : Φ.Compatible G) (heff : G.IsEfficient encFn)
    (hphi : ComputableInPolyTime Φ.phi encFn encΛ)
    (hsec : G.ObvSimSecure Φ encFn encΛ) : G.ObvIndSecure Φ encFn := by
  intro σ encσ A hA
  obtain ⟨S, _, hneg⟩ := hsec _ _ _ (isPPT_obvIndToSim heff hphi hA)
  have htwo : Negligible fun k => 2 * obvSimAdvantage G Φ k (S k) (obvIndToSim G Φ (A k)) := by
    simpa only [two_mul] using hneg.add_fun hneg
  exact htwo.congr' (Filter.Eventually.of_forall fun k =>
    (obvIndAdvantage_eq_two_mul_obvSimAdvantage_obvIndToSim G Φ hCompat k (S k) (A k)).symm)

/-- **BHR12 Proposition 3 (`obv.ind → obv.sim` with a universal simulator)**
([BellareHoangRogaway2012], §4.3, pp. 14–15): for an efficient garbling scheme `G` with compatible
polynomial-time side information `Φ` and a polynomial-time `Φ`-inverter `M`, `ObvIndSecure` implies
`ObvSimSecureUniversal`, because `obvSimFromInverter G k M` does not depend on the adversary. This
universal form (`∃ S ∀ B`) strengthens Proposition 3 as stated (`∀ B ∃ S`, which is
`Scheme.ObvIndSecure.obvSimSecure`); the source's proof yields it, since its simulator is defined
from `M` before the adversary (pp. 14–15). -/
theorem Scheme.ObvIndSecure.obvSimSecureUniversal [DecidableEq Λ] {G : Scheme Fn}
    {Φ : SideInfo Fn Λ} {encFn : Fn ↪ List Bool} {encΛ : Λ ↪ List Bool}
    (hCompat : Φ.Compatible G) (heff : G.IsEfficient encFn)
    (hphi : ComputableInPolyTime Φ.phi encFn encΛ) {M : Λ → Fn}
    (hInv : Φ.IsInverter M) (hM : ComputableInPolyTime M encΛ encFn)
    (hsec : G.ObvIndSecure Φ encFn) : G.ObvSimSecureUniversal Φ encFn encΛ := by
  refine ⟨fun k => obvSimFromInverter G k M, isPPTOn_obvSimFromInverter heff hM,
    fun σ encσ B hB => ?_⟩
  have hneg := hsec _ _ _ (isPPT_obvSimToInd heff hphi hM hB)
  exact hneg.congr' (Filter.Eventually.of_forall fun k =>
    (obvSimAdvantage_obvSimFromInverter_eq G Φ hCompat hInv k (B k)).symm)

/-- **BHR12 Proposition 3 (`obv.ind → obv.sim`)** ([BellareHoangRogaway2012], §4.3, pp. 14–15):
for an efficient garbling scheme `G` with compatible polynomial-time side information `Φ` and a
polynomial-time `Φ`-inverter `M`, indistinguishability obliviousness `ObvIndSecure` implies
simulation obliviousness `ObvSimSecure`. -/
theorem Scheme.ObvIndSecure.obvSimSecure [DecidableEq Λ] {G : Scheme Fn} {Φ : SideInfo Fn Λ}
    {encFn : Fn ↪ List Bool} {encΛ : Λ ↪ List Bool}
    (hCompat : Φ.Compatible G) (heff : G.IsEfficient encFn)
    (hphi : ComputableInPolyTime Φ.phi encFn encΛ) {M : Λ → Fn}
    (hInv : Φ.IsInverter M) (hM : ComputableInPolyTime M encΛ encFn)
    (hsec : G.ObvIndSecure Φ encFn) : G.ObvSimSecure Φ encFn encΛ :=
  (hsec.obvSimSecureUniversal hCompat heff hphi hInv hM).obvSimSecure

end Cslib.Crypto.Garbling
