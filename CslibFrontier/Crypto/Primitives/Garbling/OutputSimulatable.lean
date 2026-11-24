/-
Copyright (c) 2026 Samuel Schlesinger, Phillipp Schoppmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Phillipp Schoppmann
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.Asymptotic
public import CslibFrontier.Crypto.Primitives.Garbling.PointPermute.Efficient
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Partial
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Tactic.PolyTime

/-!
# Output-simulatability and token-checked decoding for garbling schemes

This module formalizes output-token-checked decoding, the output-simulatability (`out.sim`)
security game and asymptotic predicates motivated by [BonehShoup2023], Chapter 23,
Definition 23.4 (section/page locators in Chapter 23 were not independently PDF-verified), and
the non-asymptotic and uniform strict-PPT reductions relating `out.sim` to obliviousness
(`obv.sim`), authenticity (`aut`), and privacy (`prv.sim`, via decoding-information simulation).

In contrast to unauthenticated bit-level decoding such as `PointPermute.decodeWord`—which only
checks `Y.length % d.length = 0` and recovers output bits from colour parities, allowing any
adversary to flip bits of `Y` and break authenticity with probability `1`
(`PointPermute.autAdvantage_flipForger`)—token-checked decoding (`Scheme.withTokenDecoding`) stores
tags of the honest per-wire output token pairs `(tok₀, tok₁)` in `decInfo` and accepts an output
word `Y` only when every wire chunk hashes/tags uniquely to one of the two expected wire tokens
(`decode_withTokenDecoding_eq_some_iff`).

## Model conventions

* `OutSimAdversary` is a three-stage adversary `(choose, forge, guess)`: given `1^k`, it chooses a
  query `(f, x)`, receives the oblivious view `(F, X)` (without `decInfo`), outputs a candidate
  garbled output `Y'`, and distinguishes the real decoded result `G.decode g.decInfo Y'` from the
  ideal check `if Y' == G.evalGarbled view.fn view.input then some (G.ev f x) else none`. Invalid
  queries (`q.input.length ≠ G.inLen q.fn`) immediately return `false` in both worlds (matching
  `autExperiment`).
* Efficiency certificates use `OutSim.encObvView` (distinct from `Garbling.encPrvView`) and named
  encoding abbreviations so statements stay uniform without repeated compound encodings.

## Main definitions

* `Cslib.Crypto.Garbling.OutputTokenSpec`, `Cslib.Crypto.Garbling.OutputTokenSpec.Sound`,
  `Cslib.Crypto.Garbling.Scheme.withTokenDecoding`: token-checked output decoding transform.
* `Cslib.Crypto.Garbling.PointPermute.outputTokenSpec`: output token specification for
  `PointPermute.scheme`.
* `Cslib.Crypto.Garbling.OutSimAdversary`, `Cslib.Crypto.Garbling.OutSimAdversary.IsPPT`,
  `Cslib.Crypto.Garbling.outSimExperiment`, `Cslib.Crypto.Garbling.outSimAdvantage`: the
  output-simulatability experiment and advantage.
* `Cslib.Crypto.Garbling.Scheme.OutSimSecure`,
  `Cslib.Crypto.Garbling.Scheme.OutSimSecureUniversal`: asymptotic output-simulatability
  (for-every-adversary and universal-simulator variants).
* `Cslib.Crypto.Garbling.DecSimulator`, `Cslib.Crypto.Garbling.decSimExperiment`,
  `Cslib.Crypto.Garbling.decSimAdvantage`: decoding-information simulation connecting `obv.sim` /
  `out.sim` to `prv.sim`.

## Main results

* `Cslib.Crypto.Garbling.decode_withTokenDecoding_eq_some_iff`,
  `Cslib.Crypto.Garbling.decode_withTokenDecoding_forgery_witness`: exact acceptance
  characterization and forgery witness for `withTokenDecoding`.
* `Cslib.Crypto.Garbling.PointPermute.autAdvantage_flipForger`,
  `Cslib.Crypto.Garbling.PointPermute.not_outSimSecure`: `PointPermute.scheme` fails `aut` and
  `out.sim` unconditionally with advantage `1`, while `PointPermute.outputTokenSpec` makes
  `(PointPermute.scheme family).withTokenDecoding` valid, well typed, and efficient, and rejects
  the flipped forgery whenever its tag differs from the inactive wire token.
* `Cslib.Crypto.Garbling.obvSimAdvantage_eq_outSimAdvantage`,
  `Cslib.Crypto.Garbling.autAdvantage_eq_outSimAdvantage`,
  `Cslib.Crypto.Garbling.outSimAdvantage_le_autAdvantage_add_obvSimAdvantage`: fixed-`k`
  relations equating `OutSim` with `ObvSim ∧ Aut`.
* `Cslib.Crypto.Garbling.Scheme.OutSimSecure.obvSim`,
  `Cslib.Crypto.Garbling.Scheme.OutSimSecure.aut`,
  `Cslib.Crypto.Garbling.outSimSecure_of_obvSim_and_aut`,
  `Cslib.Crypto.Garbling.outSimSecureUniversal_of_obvSim_and_aut`: uniform strict-PPT asymptotic
  equivalences.
* `Cslib.Crypto.Garbling.prvSimSecure_of_obvSim_and_decSim`,
  `Cslib.Crypto.Garbling.prvSimSecureUniversal_of_outSimSecureUniversal_and_decSim`: privacy
  (`prv.sim`) from obliviousness / output-simulatability and decoding-information simulation.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Chapter 23, Definition 23.4 (page numbers not PDF-verified).
* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
-/

public section

namespace Cslib.Crypto.Garbling

open Turing.MultiTapeTM Probability Filter
open scoped NNReal

/-! ## Encodings for output simulatability and token decoding -/

namespace OutSim

/-- Framing encoding of an oblivious view `(F, X)`. -/
enc_structure encObvView : ObvView where
  fn : encBits, input : encBits

end OutSim

/-- Encoding of `(k, w, pairs)` stored inside `decInfo` by `withTokenDecoding`. -/
abbrev encTokenDecInfo : (ℕ × ℕ × List (List Bool × List Bool)) ↪ List Bool :=
  encPair encUnary (encPair encUnary (encList (encPair encBits encBits)))

/-- Encoding of `(1^k, ())`, the stage-1 input of an adversary. -/
abbrev encUnaryUnit : (ℕ × Unit) ↪ List Bool := encPair encUnary encUnit

/-- Encoding of `(query, st₁)` returned by stage 1 of `OutSimAdversary`. -/
abbrev encOutSimChooseOut (Fn σ₁ : Type) (encFn : Fn ↪ List Bool) (encσ₁ : σ₁ ↪ List Bool) :
    (Query Fn × σ₁) ↪ List Bool :=
  encPair (encQuery Fn encFn) encσ₁

/-- Encoding of `(1^k, (st₁, view))` passed to stage 2 of `OutSimAdversary`. -/
abbrev encOutSimForgeIn (σ₁ : Type) (encσ₁ : σ₁ ↪ List Bool) :
    (ℕ × (σ₁ × ObvView)) ↪ List Bool :=
  encPair encUnary (encPair encσ₁ OutSim.encObvView)

/-- Encoding of `(Y', st₂)` returned by stage 2 of `OutSimAdversary`. -/
abbrev encOutSimForgeOut (σ₂ : Type) (encσ₂ : σ₂ ↪ List Bool) :
    (List Bool × σ₂) ↪ List Bool :=
  encPair encBits encσ₂

/-- Encoding of `(1^k, (st₂, out))` passed to stage 3 of `OutSimAdversary`. -/
abbrev encOutSimGuessIn (σ₂ : Type) (encσ₂ : σ₂ ↪ List Bool) :
    (ℕ × (σ₂ × Option (List Bool))) ↪ List Bool :=
  encPair encUnary (encPair encσ₂ (encOption encBits))

/-- Encoding of `(st, mview)` passed to stage 2 of an `obv.sim` adversary. -/
abbrev encObvSimGuessIn (σ : Type) (encσ : σ ↪ List Bool) :
    (σ × Option ObvView) ↪ List Bool :=
  encPair encσ (encOption OutSim.encObvView)

/-- Encoding of `(1^k, φ)` passed to an obliviousness simulator. -/
abbrev encObvSimIn (Λ : Type) (encΛ : Λ ↪ List Bool) : (ℕ × Λ) ↪ List Bool :=
  encPair encUnary encΛ

/-- Encoding of `(1^k, (φ, (view, y)))` passed to a decoding-information simulator. -/
abbrev encDecSimIn (Λ : Type) (encΛ : Λ ↪ List Bool) :
    (ℕ × (Λ × (ObvView × List Bool))) ↪ List Bool :=
  encPair encUnary (encPair encΛ (encPair OutSim.encObvView encBits))

/-- Encoding of `(1^k, (y, φ))` passed to a privacy simulator. -/
abbrev encPrvSimIn (Λ : Type) (encΛ : Λ ↪ List Bool) : (ℕ × (List Bool × Λ)) ↪ List Bool :=
  encPair encUnary (encPair encBits encΛ)

/-- Encoding of `(q, st₁)` state used by `outSimToObvSim`. -/
abbrev encOutSimObvState (Fn σ₁ : Type) (encFn : Fn ↪ List Bool) (encσ₁ : σ₁ ↪ List Bool) :
    (Query Fn × σ₁) ↪ List Bool :=
  encPair (encQuery Fn encFn) encσ₁

/-- Encoding of `(k, f)` for token-length computation. -/
abbrev encSchemeArg (Fn : Type) (encFn : Fn ↪ List Bool) : (ℕ × Fn) ↪ List Bool :=
  encPair encUnary encFn

/-- Encoding of `(k, (f, coins))` for output-token extraction. -/
abbrev encSchemeCoinsArg (Fn : Type) (encFn : Fn ↪ List Bool) :
    (ℕ × (Fn × List Bool)) ↪ List Bool :=
  encPair encUnary (encPair encFn encBits)

/-- Encoding of `(k, tok)` for token tagging. -/
abbrev encTagArg : (ℕ × List Bool) ↪ List Bool := encPair encUnary encBits

/-- Encoding of `(Y', view)` state used by `autToOutSim`. -/
abbrev encAutOutState : (List Bool × ObvView) ↪ List Bool :=
  encPair encBits OutSim.encObvView

/-- Encoding of `(st, view)` state used by `obvSimToOutSim`. -/
abbrev encObvOutState (σ : Type) (encσ : σ ↪ List Bool) : (σ × ObvView) ↪ List Bool :=
  encPair encσ OutSim.encObvView

/-- Encoding of `(q, st)` state used by `prvSimToObvSim`. -/
abbrev encPrvObvState (Fn σ : Type) (encFn : Fn ↪ List Bool) (encσ : σ ↪ List Bool) :
    (Query Fn × σ) ↪ List Bool :=
  encPair (encQuery Fn encFn) encσ

/-! ## Token-checked output decoding (`withTokenDecoding`) -/

/-- Specification of the two valid output-wire tokens `(tok₀, tok₁)` per output wire of a garbling
scheme `G`, together with a deterministic tag/hash function `tag` stored and verified in
`decInfo`. Setting `tag := fun _ => id` gives exact raw wire-token matching. -/
structure OutputTokenSpec (Fn : Type) (G : Scheme Fn) where
  /-- Length of each output-wire token at security parameter `k` and function `f`. -/
  tokenLen : ℕ → Fn → ℕ
  /-- The ordered list of `(tok₀, tok₁)` pairs (one per output wire) for `(k, f, coins)`. -/
  tokens : ℕ → Fn → List Bool → List (List Bool × List Bool)
  /-- Deterministic tag/hash applied to output tokens in `decInfo` and `decode`. -/
  tag : ℕ → List Bool → List Bool := fun _ => id

/-- Strict partial decoder for `encTokenDecInfo`. -/
@[expose] def tokenDecInfoDecoder : PartialDecoder encTokenDecInfo :=
  .pair (.ofDecoder .unary) (.pair (.ofDecoder .unary)
    (.list (.pair (.ofDecoder .bits) (.ofDecoder .bits))))

/-- Encode `(k, w, taggedPairs)` into the `decInfo` word used by `withTokenDecoding`. -/
@[expose] def tokenDecInfo (k w : ℕ) (taggedPairs : List (List Bool × List Bool)) : List Bool :=
  encTokenDecInfo (k, w, taggedPairs)

/-- Core token verification step on decoded `(k, w, taggedPairs)` and garbled output `Y`:
accepts `[]` iff `Y = []` when `taggedPairs = []`, and otherwise requires `0 < w`,
`Y.length = taggedPairs.length * w`, distinct per-wire tags `t₀ ≠ t₁`, and every wire chunk's
tag under `tag k` equal to `t₀` (bit `false`) or `t₁` (bit `true`). -/
@[expose] def tokenDecodeCheck (tag : ℕ → List Bool → List Bool) (k w : ℕ)
    (taggedPairs : List (List Bool × List Bool)) (Y : List Bool) : Option (List Bool) :=
  if taggedPairs.isEmpty then
    if Y.isEmpty then some [] else none
  else
    let rows := BitString.listRows taggedPairs.length w Y
    let paired := taggedPairs.zip rows
    if 0 < w ∧ Y.length = taggedPairs.length * w ∧
        paired.all (fun (p, row) => p.1 != p.2 && (tag k row == p.1 || tag k row == p.2)) then
      some (paired.map fun (p, row) => tag k row == p.2)
    else
      none

/-- Decode `Y` against token-checked `decInfo` using `tag`. -/
@[expose] def tokenDecode (tag : ℕ → List Bool → List Bool) (d Y : List Bool) :
    Option (List Bool) :=
  match tokenDecInfoDecoder.decode d with
  | none => none
  | some (k, w, taggedPairs) => tokenDecodeCheck tag k w taggedPairs Y

private theorem tokenDecodeCheck_polyTime {tag : ℕ → List Bool → List Bool}
    (htag : ComputableInPolyTime (fun (k, tok) => tag k tok) encTagArg encBits) :
    ComputableInPolyTime
      (fun (a : (ℕ × ℕ × List (List Bool × List Bool)) × List Bool) =>
        tokenDecodeCheck tag a.1.1 a.1.2.1 a.1.2.2 a.2)
      (encPair encTokenDecInfo encBits) (encOption encBits) := by
  let E := encPair encTokenDecInfo encBits
  have hk : ComputableInPolyTime
      (fun a : (ℕ × ℕ × List (List Bool × List Bool)) × List Bool => a.1.1) E encUnary := by
    fun_prop
  have hw : ComputableInPolyTime
      (fun a : (ℕ × ℕ × List (List Bool × List Bool)) × List Bool => a.1.2.1) E encUnary := by
    fun_prop
  have hpairs : ComputableInPolyTime
      (fun a : (ℕ × ℕ × List (List Bool × List Bool)) × List Bool => a.1.2.2) E
      (encList (encPair encBits encBits)) := by
    fun_prop
  have hY : ComputableInPolyTime
      (fun a : (ℕ × ℕ × List (List Bool × List Bool)) × List Bool => a.2) E encBits := by
    fun_prop
  have hrows : ComputableInPolyTime
      (fun a : (ℕ × ℕ × List (List Bool × List Bool)) × List Bool =>
        BitString.listRows a.1.2.2.length a.1.2.1 a.2) E (encList encBits) := by
    unfold BitString.listRows
    polytime
  have hpaired : ComputableInPolyTime
      (fun a : (ℕ × ℕ × List (List Bool × List Bool)) × List Bool =>
        a.1.2.2.zip (BitString.listRows a.1.2.2.length a.1.2.1 a.2))
      E (encList (encPair (encPair encBits encBits) encBits)) :=
    (ComputableInPolyTime.zip (encPair encBits encBits) encBits).comp (hpairs.prod hrows)
  have hcheck : ComputableInPolyTime
      (fun a : (ℕ × ℕ × List (List Bool × List Bool)) × List Bool =>
        (a.1.2.2.zip (BitString.listRows a.1.2.2.length a.1.2.1 a.2)).all
          (fun p => p.1.1 != p.1.2 && (tag a.1.1 p.2 == p.1.1 || tag a.1.1 p.2 == p.1.2)))
      E encBool := by
    refine ComputableInPolyTime.allWith
      (par := fun a : (ℕ × ℕ × List (List Bool × List Bool)) × List Bool => a.1.1)
      (list := fun a : (ℕ × ℕ × List (List Bool × List Bool)) × List Bool =>
        a.1.2.2.zip (BitString.listRows a.1.2.2.length a.1.2.1 a.2))
      (test := fun x : ℕ × (List Bool × List Bool) × List Bool =>
        x.2.1.1 != x.2.1.2 && (tag x.1 x.2.2 == x.2.1.1 || tag x.1 x.2.2 == x.2.1.2))
      ?_ hk hpaired
    let ET := encPair encUnary (encPair (encPair encBits encBits) encBits)
    have hk' : ComputableInPolyTime
        (fun x : ℕ × (List Bool × List Bool) × List Bool => x.1) ET encUnary := by fun_prop
    have hp1 : ComputableInPolyTime
        (fun x : ℕ × (List Bool × List Bool) × List Bool => x.2.1.1) ET encBits := by fun_prop
    have hp2 : ComputableInPolyTime
        (fun x : ℕ × (List Bool × List Bool) × List Bool => x.2.1.2) ET encBits := by fun_prop
    have hrow : ComputableInPolyTime
        (fun x : ℕ × (List Bool × List Bool) × List Bool => x.2.2) ET encBits := by fun_prop
    have htg : ComputableInPolyTime
        (fun x : ℕ × (List Bool × List Bool) × List Bool => tag x.1 x.2.2) ET encBits :=
      htag.comp (hk'.prod hrow)
    have hneq : ComputableInPolyTime
        (fun x : ℕ × (List Bool × List Bool) × List Bool => x.2.1.1 != x.2.1.2) ET encBool := by
      convert ComputableInPolyTime.bool_not.comp (ComputableInPolyTime.decide_eq' hp1 hp2) using 1
      funext x
      by_cases h : x.2.1.1 = x.2.1.2 <;> simp [h]
    have hmatch : ComputableInPolyTime
        (fun x : ℕ × (List Bool × List Bool) × List Bool =>
          tag x.1 x.2.2 == x.2.1.1 || tag x.1 x.2.2 == x.2.1.2) ET encBool := by
      convert ComputableInPolyTime.bool_or.comp
        ((ComputableInPolyTime.decide_eq' htg hp1).prod
          (ComputableInPolyTime.decide_eq' htg hp2)) using 1
      funext x
      by_cases h1 : tag x.1 x.2.2 = x.2.1.1 <;> by_cases h2 : tag x.1 x.2.2 = x.2.1.2 <;>
        simp [h1, h2]
    exact ComputableInPolyTime.bool_and' hneq hmatch
  have hbits : ComputableInPolyTime
      (fun a : (ℕ × ℕ × List (List Bool × List Bool)) × List Bool =>
        (a.1.2.2.zip (BitString.listRows a.1.2.2.length a.1.2.1 a.2)).map
          (fun p => tag a.1.1 p.2 == p.1.2))
      E encBits := by
    have hmap := ComputableInPolyTime.mapWithInput (encB := encBool)
      (list := fun a : (ℕ × ℕ × List (List Bool × List Bool)) × List Bool =>
        a.1.2.2.zip (BitString.listRows a.1.2.2.length a.1.2.1 a.2))
      (f := fun a p => tag a.1.1 p.2 == p.1.2) hpaired ?_
    · exact (bits_encList_polyTime encBool).2.comp hmap
    let EM := encPair E (encPair (encPair encBits encBits) encBits)
    have hka : ComputableInPolyTime
        (fun q : ((ℕ × ℕ × List (List Bool × List Bool)) × List Bool) ×
          ((List Bool × List Bool) × List Bool) => q.1.1.1) EM encUnary := by fun_prop
    have hrow : ComputableInPolyTime
        (fun q : ((ℕ × ℕ × List (List Bool × List Bool)) × List Bool) ×
          ((List Bool × List Bool) × List Bool) => q.2.2) EM encBits := by fun_prop
    have hp2 : ComputableInPolyTime
        (fun q : ((ℕ × ℕ × List (List Bool × List Bool)) × List Bool) ×
          ((List Bool × List Bool) × List Bool) => q.2.1.2) EM encBits := by fun_prop
    convert ComputableInPolyTime.decide_eq' (htag.comp (hka.prod hrow)) hp2 using 1
    funext q
    by_cases he : tag q.1.1.1 q.2.2 = q.2.1.2 <;> simp [he]
  have hcond : ComputableInPolyTime
      (fun a : (ℕ × ℕ × List (List Bool × List Bool)) × List Bool =>
        decide (0 < a.1.2.1 ∧ a.2.length = a.1.2.2.length * a.1.2.1 ∧
          (a.1.2.2.zip (BitString.listRows a.1.2.2.length a.1.2.1 a.2)).all
            (fun (p, row) => p.1 != p.2 && (tag a.1.1 row == p.1 || tag a.1.1 row == p.2))))
      E encBool := by
    refine ComputableInPolyTime.decide_and ?_ (ComputableInPolyTime.decide_and ?_ hcheck)
    · exact ComputableInPolyTime.unary_lt' (.const 0) hw
    · exact ComputableInPolyTime.decide_eq' (ComputableInPolyTime.length_bits_comp hY)
        (ComputableInPolyTime.unary_mul' ((ComputableInPolyTime.length_list
          (encPair encBits encBits)).comp hpairs) hw)
  have hempty : ComputableInPolyTime
      (fun a : (ℕ × ℕ × List (List Bool × List Bool)) × List Bool => a.1.2.2.isEmpty)
      E encBool := by
    have h0 := ComputableInPolyTime.decide_eq'
      ((ComputableInPolyTime.length_list (encPair encBits encBits)).comp hpairs) (.const 0)
    convert h0 using 1
    funext a
    rw [Bool.eq_iff_iff, List.isEmpty_iff, decide_eq_true_eq]
    exact List.length_eq_zero_iff.symm
  have hYempty : ComputableInPolyTime
      (fun a : (ℕ × ℕ × List (List Bool × List Bool)) × List Bool => a.2.isEmpty) E encBool := by
    have h0 := ComputableInPolyTime.decide_eq' (ComputableInPolyTime.length_bits_comp hY) (.const 0)
    convert h0 using 1
    funext a
    rw [Bool.eq_iff_iff, List.isEmpty_iff, decide_eq_true_eq]
    exact List.length_eq_zero_iff.symm
  have hbranch1 : ComputableInPolyTime
      (fun a : (ℕ × ℕ × List (List Bool × List Bool)) × List Bool =>
        if a.2.isEmpty then some ([] : List Bool) else none) E (encOption encBits) :=
    hYempty.ite (.const (some [])) (.const none)
  have hbranch2 : ComputableInPolyTime
      (fun a : (ℕ × ℕ × List (List Bool × List Bool)) × List Bool =>
        if 0 < a.1.2.1 ∧ a.2.length = a.1.2.2.length * a.1.2.1 ∧
            (a.1.2.2.zip (BitString.listRows a.1.2.2.length a.1.2.1 a.2)).all
              (fun (p, row) => p.1 != p.2 && (tag a.1.1 row == p.1 || tag a.1.1 row == p.2)) then
          some ((a.1.2.2.zip (BitString.listRows a.1.2.2.length a.1.2.1 a.2)).map
            (fun (p, row) => tag a.1.1 row == p.2))
        else none) E (encOption encBits) := by
    convert hcond.ite ((ComputableInPolyTime.optionSome encBits).comp hbits) (.const none) using 1
    funext a
    simp only [Bool.decide_and, decide_eq_true_eq, Bool.and_eq_true, Function.comp_def]
  convert hempty.ite hbranch1 hbranch2 using 1
  funext a
  simp only [tokenDecodeCheck]

/-- `tokenDecode` is computable in polynomial time whenever `tag` is. -/
theorem tokenDecode_polyTime {tag : ℕ → List Bool → List Bool}
    (htag : ComputableInPolyTime (fun (k, tok) => tag k tok) encTagArg encBits) :
    ComputableInPolyTime (fun (d, Y) => tokenDecode tag d Y) (encPair encBits encBits)
      (encOption encBits) := by
  have hdec : ComputableInPolyTime
      (fun p : List Bool × List Bool => tokenDecInfoDecoder.decode p.1)
      (encPair encBits encBits) (encOption encTokenDecInfo) :=
    tokenDecInfoDecoder.computable.comp (ComputableInPolyTime.fst encBits encBits)
  have hmatch : ComputableInPolyTime
      (fun p : (List Bool × List Bool) × (ℕ × ℕ × List (List Bool × List Bool)) =>
        tokenDecodeCheck tag p.2.1 p.2.2.1 p.2.2.2 p.1.2)
      (encPair (encPair encBits encBits) encTokenDecInfo) (encOption encBits) :=
    (tokenDecodeCheck_polyTime htag).comp
      ((ComputableInPolyTime.snd (encPair encBits encBits) encTokenDecInfo).prod
        ((ComputableInPolyTime.snd encBits encBits).comp
          (ComputableInPolyTime.fst (encPair encBits encBits) encTokenDecInfo)))
  convert ComputableInPolyTime.optionElimWithInput
    (body := fun (p : List Bool × List Bool) (dec : ℕ × ℕ × List (List Bool × List Bool)) =>
      tokenDecodeCheck tag dec.1 dec.2.1 dec.2.2 p.2)
    hdec (.const none) hmatch using 1
  funext p
  simp only [tokenDecode]
  cases tokenDecInfoDecoder.decode p.1 <;> rfl

/-- Replace a garbling scheme's decoding algorithm with token-checked output decoding: `fn`,
`encInfo`, `encode`, and `evalGarbled` are unchanged, while `decInfo` stores the tagged per-wire
output token pairs and `decode` accepts only words whose wire chunks match those tags. -/
@[expose] def Scheme.withTokenDecoding {Fn : Type} (G : Scheme Fn)
    (spec : OutputTokenSpec Fn G) : Scheme Fn where
  inLen := G.inLen
  outLen := G.outLen
  size := G.size
  ev := G.ev
  coinLen := G.coinLen
  gb k f coins :=
    let g := G.gb k f coins
    ⟨g.fn, g.encInfo,
      tokenDecInfo k (spec.tokenLen k f)
        ((spec.tokens k f coins).map fun p => (spec.tag k p.1, spec.tag k p.2))⟩
  encode := G.encode
  evalGarbled := G.evalGarbled
  decode := tokenDecode spec.tag

/-- Replacing `decode` via `withTokenDecoding` leaves the oblivious view `(F, X)` unchanged. -/
theorem obvView_withTokenDecoding {Fn : Type} (G : Scheme Fn) (spec : OutputTokenSpec Fn G)
    (k : ℕ) (q : Query Fn) :
    (G.withTokenDecoding spec).obvView k q = G.obvView k q := by
  simp [Scheme.obvView, Scheme.garble, Scheme.withTokenDecoding, Scheme.coins]

/-- Replacing `decode` via `withTokenDecoding` preserves every `obv.sim` advantage identically. -/
theorem obvSimAdvantage_withTokenDecoding {Fn Λ σ : Type} (G : Scheme Fn)
    (spec : OutputTokenSpec Fn G) (Φ : SideInfo Fn Λ) (k : ℕ) (S : ObvSimulator Λ)
    (B : ObvSimAdversary Fn σ) :
    obvSimAdvantage (G.withTokenDecoding spec) Φ k S B = obvSimAdvantage G Φ k S B := by
  simp only [obvSimAdvantage, obvSimExperiment, obvView_withTokenDecoding]
  rfl

/-- Replacing `decode` via `withTokenDecoding` preserves every `obv.ind` advantage identically. -/
theorem obvIndAdvantage_withTokenDecoding {Fn Λ σ : Type} [DecidableEq Λ] (G : Scheme Fn)
    (spec : OutputTokenSpec Fn G) (Φ : SideInfo Fn Λ) (k : ℕ) (A : ObvIndAdversary Fn σ) :
    obvIndAdvantage (G.withTokenDecoding spec) Φ k A = obvIndAdvantage G Φ k A := by
  simp only [obvIndAdvantage, obvIndExperiment, obvIndValid, obvView_withTokenDecoding]
  rfl

/-- Structural soundness conditions on an `OutputTokenSpec` ensuring that `G.withTokenDecoding spec`
satisfies `IsValid` and `WellTyped`. -/
structure OutputTokenSpec.Sound {Fn : Type} (G : Scheme Fn) (spec : OutputTokenSpec Fn G) : Prop
    where
  /-- Number of output token pairs equals `G.outLen f`. -/
  length_tokens : ∀ k f coins, coins.length = G.coinLen k (G.inLen f) (G.outLen f) (G.size f) →
    (spec.tokens k f coins).length = G.outLen f
  /-- Output token width is positive whenever `G.outLen f > 0`. -/
  tokenLen_pos : ∀ k f, 0 < G.outLen f → 0 < spec.tokenLen k f
  /-- Every output token pair has both tokens of length `spec.tokenLen k f`. -/
  token_lengths : ∀ k f coins, coins.length = G.coinLen k (G.inLen f) (G.outLen f) (G.size f) →
    ∀ p ∈ spec.tokens k f coins, p.1.length = spec.tokenLen k f ∧ p.2.length = spec.tokenLen k f
  /-- Tagged tokens for `false` and `true` are distinct on every output wire. -/
  tag_distinct : ∀ k f coins, coins.length = G.coinLen k (G.inLen f) (G.outLen f) (G.size f) →
    ∀ p ∈ spec.tokens k f coins, spec.tag k p.1 ≠ spec.tag k p.2
  /-- Evaluation of an honestly garbled circuit yields the exact active output tokens. -/
  eval_eq_activeTokens : ∀ k f coins,
    coins.length = G.coinLen k (G.inLen f) (G.outLen f) (G.size f) →
    ∀ x, x.length = G.inLen f →
      G.evalGarbled (G.gb k f coins).fn (G.encode (G.gb k f coins).encInfo x) =
        ((spec.tokens k f coins).zip (G.ev f x)).flatMap
          (fun (p, b) => if b then p.2 else p.1)
  /-- The encoded tagged pairs depend in length only on `k` and the scheme shape. -/
  decInfo_length_eq : ∀ k f f' coins coins',
    G.inLen f = G.inLen f' → G.outLen f = G.outLen f' → G.size f = G.size f' →
    coins.length = G.coinLen k (G.inLen f) (G.outLen f) (G.size f) →
    coins'.length = G.coinLen k (G.inLen f') (G.outLen f') (G.size f') →
    (tokenDecInfo k (spec.tokenLen k f)
        ((spec.tokens k f coins).map fun p => (spec.tag k p.1, spec.tag k p.2))).length =
      (tokenDecInfo k (spec.tokenLen k f')
        ((spec.tokens k f' coins').map fun p => (spec.tag k p.1, spec.tag k p.2))).length
  /-- `tokenLen` and `tokens` depend only on `(k, coins)` and the scheme shape. -/
  nonDegenerate : ∀ k f f' coins,
    G.inLen f = G.inLen f' → G.outLen f = G.outLen f' → G.size f = G.size f' →
    coins.length = G.coinLen k (G.inLen f) (G.outLen f) (G.size f) →
    spec.tokenLen k f = spec.tokenLen k f' ∧ spec.tokens k f coins = spec.tokens k f' coins

private theorem flatten_listRows_eq_self {m w : ℕ} (hw : 0 < w) {Y : List Bool}
    (hY : Y.length = m * w) :
    (BitString.listRows m w Y).flatten = Y := by
  have hblock_len : ∀ row : Fin m,
      (List.ofFn (BitString.block (BitString.ofList (m * w) Y) row)).length = w :=
    fun _ => by simp
  have hrows : BitString.listRows m w Y =
      List.ofFn fun row : Fin m =>
        List.ofFn (BitString.block (BitString.ofList (m * w) Y) row) := by
    rw [BitString.listRows_eq_ofFn]
  rw [hrows]
  apply List.ext_getElem
  · simp [List.length_flatten, List.sum_ofFn, hblock_len, hY]
  · intro j hj1 hj2
    have hget := BitString.listRow_flatten_ofFn
      (fun row : Fin m => List.ofFn (BitString.block (BitString.ofList (m * w) Y) row))
      hblock_len ⟨j / w, Nat.div_lt_of_lt_mul (by rwa [mul_comm, ← hY])⟩
    have hmod : j % w < w := Nat.mod_lt _ hw
    have helem := congrArg (fun l => l.getD (j % w) false) hget
    rw [BitString.getD_listRow hmod] at helem
    have hjeq : (⟨j / w, Nat.div_lt_of_lt_mul (by rwa [mul_comm, ← hY])⟩ : Fin m).val * w +
        j % w = j := by
      dsimp only; rw [mul_comm]; exact Nat.div_add_mod j w
    rw [hjeq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj1, Option.getD_some] at helem
    rw [helem, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp only [hmod, ↓reduceDIte, Option.getD_some, BitString.block, BitString.ofList,
      finProdFinEquiv, Equiv.coe_fn_mk, Fin.val_mk, List.getD_eq_getElem?_getD,
      add_comm (j % w), Nat.div_add_mod, List.getElem?_eq_getElem hj2, Option.getD_some]

private theorem zip_tokens_flatMap_eq_flatten {m w : ℕ}
    (toks : List (List Bool × List Bool)) (bits : List Bool)
    (htoks : toks.length = m) (hbits : bits.length = m)
    (hlen : ∀ p ∈ toks, p.1.length = w ∧ p.2.length = w) :
    (toks.zip bits).flatMap (fun (p, b) => if b then p.2 else p.1) =
      (List.ofFn fun o : Fin m =>
        let p := toks.getD o ([], [])
        if bits.getD o false then p.2 else p.1).flatten ∧
    ((toks.zip bits).flatMap (fun (p, b) => if b then p.2 else p.1)).length = m * w := by
  let exp := List.ofFn fun o : Fin m =>
    let p := toks.getD o ([], [])
    if bits.getD o false then p.2 else p.1
  have hexp_flat : (toks.zip bits).flatMap (fun (p, b) => if b then p.2 else p.1) =
      exp.flatten := by
    rw [List.flatMap_def]
    congr 1
    apply List.ext_getElem
    · simp [exp, htoks, hbits]
    · intro i hi1 hi2
      have hi_m : i < m := by simpa [exp] using hi2
      simp only [List.getElem_map, List.getElem_zip, exp, List.getElem_ofFn,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i < toks.length),
        List.getElem?_eq_getElem (by omega : i < bits.length), Option.getD_some]
  have hexp_len : ∀ v ∈ exp, v.length = w := by
    intro v hv
    obtain ⟨o, rfl⟩ := List.mem_ofFn.mp hv
    have ho : (o : ℕ) < toks.length := by omega
    have hmem : toks.getD o ([], []) ∈ toks := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ho]
      exact List.getElem_mem ho
    have hp := hlen _ hmem
    simp only [List.getD_eq_getElem?_getD] at hp
    cases hbit : bits.getD o false
    · exact hp.1
    · exact hp.2
  refine ⟨hexp_flat, ?_⟩
  rw [hexp_flat, List.length_flatten]
  have hmap : exp.map List.length = List.replicate m w := by
    apply List.ext_getElem (by simp [exp])
    intro i hi1 hi2
    simp only [List.getElem_map, List.getElem_replicate]
    exact hexp_len _ (List.getElem_mem (by simpa using hi1))
  rw [hmap, List.sum_replicate, smul_eq_mul]

/-- Exact acceptance characterization of `withTokenDecoding` for a sound token specification:
`decode` returns `some y` iff `y` has length `m = G.outLen f`, `Y` has length `m * w`, and on every
wire `o < m` the tag of chunk `o` equals the tag of the `y[o]`-token. -/
theorem decode_withTokenDecoding_eq_some_iff {Fn : Type} {G : Scheme Fn}
    {spec : OutputTokenSpec Fn G} (hs : spec.Sound) {k : ℕ} {f : Fn} {coins : List Bool}
    (hc : coins.length = G.coinLen k (G.inLen f) (G.outLen f) (G.size f))
    (Y y : List Bool) :
    (G.withTokenDecoding spec).decode ((G.withTokenDecoding spec).gb k f coins).decInfo Y =
        some y ↔
      y.length = G.outLen f ∧
        (G.outLen f = 0 → Y = []) ∧
        (0 < G.outLen f → Y.length = G.outLen f * spec.tokenLen k f ∧
          ∀ o : Fin (G.outLen f),
            let p := (spec.tokens k f coins).getD o ([], [])
            let row := BitString.listRow (spec.tokenLen k f) o Y
            spec.tag k row = spec.tag k (if y.getD o false then p.2 else p.1)) := by
  let tagged := (spec.tokens k f coins).map fun p => (spec.tag k p.1, spec.tag k p.2)
  have hlen : tagged.length = G.outLen f := by
    simp [tagged, hs.length_tokens k f coins hc]
  have hdec : (G.withTokenDecoding spec).decode
      ((G.withTokenDecoding spec).gb k f coins).decInfo Y =
      tokenDecodeCheck spec.tag k (spec.tokenLen k f) tagged Y := by
    simp only [Scheme.withTokenDecoding, tokenDecode, tokenDecInfo, tagged]
    rw [PartialDecoder.decode_enc tokenDecInfoDecoder]
  rw [hdec, tokenDecodeCheck]
  by_cases hm : G.outLen f = 0
  · have hempty : tagged.isEmpty = true := by
      rw [List.isEmpty_iff, List.eq_nil_iff_length_eq_zero, hlen, hm]
    simp only [hempty, ↓reduceIte, hm, forall_const, Nat.lt_irrefl, IsEmpty.forall_iff,
      and_true]
    by_cases hY : Y.isEmpty
    · have hYnil : Y = [] := List.isEmpty_iff.mp hY
      simp [hYnil, eq_comm]
    · have hYne : Y ≠ [] := fun h => hY (by simp [h])
      simp [hY, hYne]
  · have hmpos : 0 < G.outLen f := Nat.pos_of_ne_zero hm
    have hwpos : 0 < spec.tokenLen k f := hs.tokenLen_pos k f hmpos
    have hempty : tagged.isEmpty = false := by
      rw [Bool.eq_false_iff, ne_eq, List.isEmpty_iff, List.eq_nil_iff_length_eq_zero, hlen]
      exact hm
    simp only [hempty, Bool.false_eq_true, ↓reduceIte, hm, IsEmpty.forall_iff, hmpos, forall_const,
      true_and, hlen, hwpos]
    have hdistinct : ∀ i : Fin (G.outLen f),
        (tagged.getD i ([], [])).1 ≠ (tagged.getD i ([], [])).2 := by
      intro i
      have hi : (i : ℕ) < (spec.tokens k f coins).length := by
        rw [hs.length_tokens k f coins hc]; exact i.isLt
      have hmem : (spec.tokens k f coins)[i.val]'hi ∈ spec.tokens k f coins := List.getElem_mem hi
      have hneq := hs.tag_distinct k f coins hc _ hmem
      simpa [tagged, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hi] using hneq
    constructor
    · intro h
      simp only [Option.ite_none_right_eq_some, Option.some.injEq] at h
      obtain ⟨⟨hYlen, hall⟩, rfl⟩ := h
      refine ⟨by simp [hlen], hYlen, fun o => ?_⟩
      have ho_zip :
          o.val < (tagged.zip (BitString.listRows (G.outLen f) (spec.tokenLen k f) Y)).length := by
        simp [hlen, BitString.length_listRows, o.isLt]
      have hall'' := List.all_eq_true.mp hall _ (List.getElem_mem ho_zip)
      simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hall''
      have hget :
          (tagged.zip (BitString.listRows (G.outLen f) (spec.tokenLen k f) Y))[o.val]'ho_zip =
            (tagged.getD o ([], []), BitString.listRow (spec.tokenLen k f) o Y) := by
        rw [List.getElem_zip]
        refine Prod.ext ?_ ?_
        · simp [List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem (by omega : o.val < tagged.length)]
        · simp [BitString.listRows, List.getElem_map, List.getElem_range]
      rw [hget] at hall''
      obtain ⟨hne, hor⟩ := hall''
      have hi : o.val < (spec.tokens k f coins).length := by
        rw [hs.length_tokens k f coins hc]; exact o.isLt
      have htagget : tagged.getD o ([], []) =
          (spec.tag k ((spec.tokens k f coins).getD o ([], [])).1,
           spec.tag k ((spec.tokens k f coins).getD o ([], [])).2) := by
        simp [tagged, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_getElem hi]
      have hyget : (((tagged.zip (BitString.listRows (G.outLen f) (spec.tokenLen k f) Y)).map
          fun (p, row) => spec.tag k row == p.2).getD o false) =
          (spec.tag k (BitString.listRow (spec.tokenLen k f) o Y) ==
            (tagged.getD o ([], [])).2) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem ho_zip, hget]
        rfl
      rw [hyget, htagget]
      rcases hor with h0 | h1
      · have hf : (spec.tag k (BitString.listRow (spec.tokenLen k f) o Y) ==
            (tagged.getD o ([], [])).2) = false := by
          rw [h0, beq_eq_false_iff_ne]
          exact hne
        rw [htagget] at hf
        simp only [hf, Bool.false_eq_true, ↓reduceIte]
        rw [htagget] at h0
        exact h0
      · have ht : (spec.tag k (BitString.listRow (spec.tokenLen k f) o Y) ==
            (tagged.getD o ([], [])).2) = true := by
          rw [h1, beq_self_eq_true]
        rw [htagget] at ht
        simp only [ht, ↓reduceIte]
        rw [htagget] at h1
        exact h1
    · rintro ⟨hylen, hYlen, hrow⟩
      have hall : (tagged.zip (BitString.listRows (G.outLen f) (spec.tokenLen k f) Y)).all
          (fun x => x.1.1 != x.1.2 &&
            (spec.tag k x.2 == x.1.1 || spec.tag k x.2 == x.1.2)) = true := by
        rw [List.all_eq_true]
        intro ⟨p, row⟩ hmem
        obtain ⟨i, hi, hp⟩ := List.mem_iff_getElem.mp hmem
        rw [← hp]
        have hi' : i < G.outLen f := by
          simp only [List.length_zip, BitString.length_listRows, hlen, min_self] at hi
          exact hi
        have hget :
            (tagged.zip (BitString.listRows (G.outLen f) (spec.tokenLen k f) Y))[i]'hi =
              (tagged.getD i ([], []), BitString.listRow (spec.tokenLen k f) i Y) := by
          rw [List.getElem_zip]
          refine Prod.ext ?_ ?_
          · simp [List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (by omega : i < tagged.length)]
          · simp [BitString.listRows, List.getElem_map, List.getElem_range]
        rw [hget]
        have hi_tok : i < (spec.tokens k f coins).length := by
          rw [hs.length_tokens k f coins hc]; exact hi'
        have htagget : tagged.getD i ([], []) =
            (spec.tag k ((spec.tokens k f coins).getD i ([], [])).1,
             spec.tag k ((spec.tokens k f coins).getD i ([], [])).2) := by
          simp [tagged, List.getD_eq_getElem?_getD, List.getElem?_map,
            List.getElem?_eq_getElem hi_tok]
        have hne := hdistinct ⟨i, hi'⟩
        have hri := hrow ⟨i, hi'⟩
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, beq_iff_eq]
        refine ⟨hne, ?_⟩
        rw [htagget]
        cases hyi : y.getD i false <;> simp only [hyi, Bool.false_eq_true, ↓reduceIte] at hri
        · exact Or.inl hri
        · exact Or.inr hri
      simp only [hYlen, hall, and_self, ↓reduceIte]
      congr 1
      apply List.ext_getElem
      · simp [hlen, BitString.length_listRows, hylen]
      · intro i hi1 hi2
        have hi' : i < G.outLen f := by simpa [hylen] using hi2
        have hri := hrow ⟨i, hi'⟩
        have hi_tok : i < (spec.tokens k f coins).length := by
          rw [hs.length_tokens k f coins hc]; exact hi'
        have htagget : tagged.getD i ([], []) =
            (spec.tag k ((spec.tokens k f coins).getD i ([], [])).1,
             spec.tag k ((spec.tokens k f coins).getD i ([], [])).2) := by
          simp [tagged, List.getD_eq_getElem?_getD, List.getElem?_map,
            List.getElem?_eq_getElem hi_tok]
        simp only [List.getElem_map, List.getElem_zip, BitString.listRows, List.getElem_range]
        have htag_eq : tagged[i]'(by omega) = tagged.getD i ([], []) := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i < tagged.length)]
        rw [htag_eq, htagget]
        have hyget : y[i]'hi2 = y.getD i false := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2]
        rw [hyget]
        have hne := hdistinct ⟨i, hi'⟩
        rw [htagget] at hne
        cases hyi : y.getD i false <;> simp only [hyi, Bool.false_eq_true, ↓reduceIte] at hri
        · simp only [hri, beq_eq_false_iff_ne]
          exact hne
        · simp [hri]

/-- Exact raw-token acceptance characterization when `spec.tag := fun _ => id`: `decode` returns
`some y` iff `y.length = G.outLen f` and `Y` is the exact concatenation of the `y`-indexed wire
tokens. -/
theorem decode_withTokenDecoding_id_eq_some_iff {Fn : Type} {G : Scheme Fn}
    {spec : OutputTokenSpec Fn G} (htag : spec.tag = fun _ => id) (hs : spec.Sound)
    {k : ℕ} {f : Fn} {coins : List Bool}
    (hc : coins.length = G.coinLen k (G.inLen f) (G.outLen f) (G.size f))
    (Y y : List Bool) :
    (G.withTokenDecoding spec).decode ((G.withTokenDecoding spec).gb k f coins).decInfo Y =
        some y ↔
      y.length = G.outLen f ∧
        Y = ((spec.tokens k f coins).zip y).flatMap (fun (p, b) => if b then p.2 else p.1) := by
  rw [decode_withTokenDecoding_eq_some_iff hs hc Y y]
  simp only [htag, id_eq]
  constructor
  · rintro ⟨hylen, h0, hpos⟩
    refine ⟨hylen, ?_⟩
    by_cases hm : G.outLen f = 0
    · rw [h0 hm]
      have hnil : spec.tokens k f coins = [] :=
        List.eq_nil_iff_length_eq_zero.mpr ((hs.length_tokens k f coins hc).trans hm)
      simp [hnil]
    · have hmpos : 0 < G.outLen f := Nat.pos_of_ne_zero hm
      obtain ⟨hYlen, hrow⟩ := hpos hmpos
      have hwpos := hs.tokenLen_pos k f hmpos
      have ⟨hflat, _⟩ := zip_tokens_flatMap_eq_flatten (spec.tokens k f coins) y
        (hs.length_tokens k f coins hc) hylen (hs.token_lengths k f coins hc)
      rw [hflat, ← flatten_listRows_eq_self hwpos hYlen]
      congr 1
      apply List.ext_getElem (by simp)
      intro i hi1 hi2
      have hi_m : i < G.outLen f := by simpa using hi2
      simpa [BitString.listRows] using hrow ⟨i, hi_m⟩
  · rintro ⟨hylen, rfl⟩
    refine ⟨hylen, ?_, ?_⟩
    · intro hm
      have hnil : spec.tokens k f coins = [] :=
        List.eq_nil_iff_length_eq_zero.mpr ((hs.length_tokens k f coins hc).trans hm)
      simp [hnil]
    · intro hmpos
      have ⟨hflat, hlen⟩ := zip_tokens_flatMap_eq_flatten (spec.tokens k f coins) y
        (hs.length_tokens k f coins hc) hylen (hs.token_lengths k f coins hc)
      refine ⟨hlen, fun o => ?_⟩
      rw [hflat]
      have hexp_len : ∀ o' : Fin (G.outLen f),
          (let p := (spec.tokens k f coins).getD o' ([], [])
          if y.getD o' false then p.2 else p.1).length = spec.tokenLen k f := by
        intro o'
        have ho : (o' : ℕ) < (spec.tokens k f coins).length := by
          rw [hs.length_tokens k f coins hc]; exact o'.isLt
        have hmem : (spec.tokens k f coins).getD o' ([], []) ∈ spec.tokens k f coins := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ho]
          exact List.getElem_mem ho
        have hp := hs.token_lengths k f coins hc _ hmem
        simp only [List.getD_eq_getElem?_getD] at hp
        cases hbit : y.getD o' false
        · exact hp.1
        · exact hp.2
      exact BitString.listRow_flatten_ofFn _ hexp_len o

/-- A valid, well-typed scheme equipped with a sound `OutputTokenSpec` remains valid under
`withTokenDecoding`. -/
theorem Scheme.IsValid.withTokenDecoding {Fn : Type} {G : Scheme Fn}
    {spec : OutputTokenSpec Fn G} (hv : G.IsValid) (hwt : G.WellTyped) (hs : spec.Sound) :
    (G.withTokenDecoding spec).IsValid where
  length k hk f f' hshape g hg g' hg' := by
    obtain ⟨coins, hc, rfl⟩ := (G.withTokenDecoding spec).mem_support_eval_garble_iff.mp hg
    obtain ⟨coins', hc', rfl⟩ := (G.withTokenDecoding spec).mem_support_eval_garble_iff.mp hg'
    have hgb := hv.length k hk f f' hshape (G.gb k f coins)
      (G.mem_support_eval_garble_iff.mpr ⟨coins, hc, rfl⟩)
      (G.gb k f' coins')
      (G.mem_support_eval_garble_iff.mpr ⟨coins', hc', rfl⟩)
    obtain ⟨hfn, henc, -⟩ := hgb
    obtain ⟨hn, hm, hq⟩ := hshape
    exact ⟨hfn, henc, hs.decInfo_length_eq k f f' coins coins' hn hm hq hc hc'⟩
  nonDegenerate k hk f f' hshape coins hc := by
    have hnd := hv.nonDegenerate k hk f f' hshape coins hc
    obtain ⟨hn, hm, hq⟩ := hshape
    obtain ⟨hw, htoks⟩ := hs.nonDegenerate k f f' coins hn hm hq hc
    refine ⟨hnd.1, ?_⟩
    simp only [Scheme.withTokenDecoding, hw, htoks]
  correct k _ f x hx g hg := by
    obtain ⟨coins, hc, rfl⟩ := (G.withTokenDecoding spec).mem_support_eval_garble_iff.mp hg
    have hlen_ev : (G.ev f x).length = G.outLen f := hwt.1 f x hx
    have heval := hs.eval_eq_activeTokens k f coins hc x hx
    change (G.withTokenDecoding spec).decode
      ((G.withTokenDecoding spec).gb k f coins).decInfo
      (G.evalGarbled (G.gb k f coins).fn (G.encode (G.gb k f coins).encInfo x)) = some (G.ev f x)
    rw [heval, decode_withTokenDecoding_eq_some_iff hs hc]
    refine ⟨hlen_ev, ?_, ?_⟩
    · intro hm
      have hnil : spec.tokens k f coins = [] :=
        List.eq_nil_iff_length_eq_zero.mpr ((hs.length_tokens k f coins hc).trans hm)
      simp [hnil]
    · intro hmpos
      have ⟨hflat, hlen⟩ := zip_tokens_flatMap_eq_flatten (spec.tokens k f coins) (G.ev f x)
        (hs.length_tokens k f coins hc) hlen_ev (hs.token_lengths k f coins hc)
      refine ⟨hlen, fun o => ?_⟩
      rw [hflat]
      have hexp_len : ∀ o' : Fin (G.outLen f),
          (let p := (spec.tokens k f coins).getD o' ([], [])
          if (G.ev f x).getD o' false then p.2 else p.1).length = spec.tokenLen k f := by
        intro o'
        have ho : (o' : ℕ) < (spec.tokens k f coins).length := by
          rw [hs.length_tokens k f coins hc]; exact o'.isLt
        have hmem : (spec.tokens k f coins).getD o' ([], []) ∈ spec.tokens k f coins := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ho]
          exact List.getElem_mem ho
        have hp := hs.token_lengths k f coins hc _ hmem
        simp only [List.getD_eq_getElem?_getD] at hp
        cases hbit : (G.ev f x).getD o' false
        · exact hp.1
        · exact hp.2
      exact congrArg (spec.tag k) (BitString.listRow_flatten_ofFn _ hexp_len o)

/-- Replacing `decode` via `withTokenDecoding` preserves `WellTyped` when `spec` is sound. -/
theorem Scheme.WellTyped.withTokenDecoding {Fn : Type} {G : Scheme Fn}
    {spec : OutputTokenSpec Fn G} (hwt : G.WellTyped) (hs : spec.Sound) :
    (G.withTokenDecoding spec).WellTyped :=
  ⟨hwt.1, fun k _ f g hg Y y hy => by
    obtain ⟨coins, hc, rfl⟩ := (G.withTokenDecoding spec).mem_support_eval_garble_iff.mp hg
    exact ((decode_withTokenDecoding_eq_some_iff hs hc Y y).mp hy).1⟩

/-- Replacing `decode` via `withTokenDecoding` preserves `Scheme.IsEfficient` whenever
`spec.tokenLen`, `spec.tokens`, and `spec.tag` are computable in polynomial time. -/
theorem Scheme.IsEfficient.withTokenDecoding {Fn : Type} {G : Scheme Fn}
    {encFn : Fn ↪ List Bool} {spec : OutputTokenSpec Fn G}
    (heff : G.IsEfficient encFn)
    (htlen : ComputableInPolyTime (fun (k, f) => spec.tokenLen k f) (encSchemeArg Fn encFn)
      encUnary)
    (htoks : ComputableInPolyTime (fun (k, f, coins) => spec.tokens k f coins)
      (encSchemeCoinsArg Fn encFn) (encList (encPair encBits encBits)))
    (htag : ComputableInPolyTime (fun (k, tok) => spec.tag k tok) encTagArg encBits) :
    (G.withTokenDecoding spec).IsEfficient encFn where
  inLen := heff.inLen
  outLen := heff.outLen
  coins := heff.coins
  gb := by
    let E := encSchemeCoinsArg Fn encFn
    have hk : ComputableInPolyTime (fun p : ℕ × Fn × List Bool => p.1) E encUnary := by fun_prop
    have hf : ComputableInPolyTime (fun p : ℕ × Fn × List Bool => p.2.1) E encFn := by fun_prop
    have hgb0 : ComputableInPolyTime (fun (k, f, coins) => G.gb k f coins) E Scheme.encGarbled :=
      heff.gb
    have hfn : ComputableInPolyTime (fun p : ℕ × Fn × List Bool => (G.gb p.1 p.2.1 p.2.2).fn)
        E encBits :=
      Scheme.encGarbled_fn_polyTime hgb0
    have henc : ComputableInPolyTime
        (fun p : ℕ × Fn × List Bool => (G.gb p.1 p.2.1 p.2.2).encInfo) E encBits :=
      Scheme.encGarbled_encInfo_polyTime hgb0
    have hmapped : ComputableInPolyTime
        (fun a : ℕ × Fn × List Bool =>
          (spec.tokens a.1 a.2.1 a.2.2).map fun p => (spec.tag a.1 p.1, spec.tag a.1 p.2))
        E (encList (encPair encBits encBits)) := by
      refine ComputableInPolyTime.mapWithInput htoks ?_
      let EM := encPair E (encPair encBits encBits)
      have hka : ComputableInPolyTime (fun q : (ℕ × Fn × List Bool) × List Bool × List Bool =>
          q.1.1) EM encUnary := by fun_prop
      have hp1 : ComputableInPolyTime (fun q : (ℕ × Fn × List Bool) × List Bool × List Bool =>
          q.2.1) EM encBits := by fun_prop
      have hp2 : ComputableInPolyTime (fun q : (ℕ × Fn × List Bool) × List Bool × List Bool =>
          q.2.2) EM encBits := by fun_prop
      exact (htag.comp (hka.prod hp1)).prod (htag.comp (hka.prod hp2))
    have hdecInfo : ComputableInPolyTime
        (fun a : ℕ × Fn × List Bool =>
          tokenDecInfo a.1 (spec.tokenLen a.1 a.2.1)
            ((spec.tokens a.1 a.2.1 a.2.2).map fun p => (spec.tag a.1 p.1, spec.tag a.1 p.2)))
        E encBits := by
      have htri := hk.prod ((htlen.comp (hk.prod hf)).prod hmapped)
      exact htri.of_enc_eq fun _ => rfl
    have hpack := Scheme.encGarbled_mk_polyTime hfn henc hdecInfo
    have heq : (fun a : ℕ × Fn × List Bool => (⟨(G.gb a.1 a.2.1 a.2.2).fn,
        (G.gb a.1 a.2.1 a.2.2).encInfo,
        tokenDecInfo a.1 (spec.tokenLen a.1 a.2.1)
          ((spec.tokens a.1 a.2.1 a.2.2).map fun p => (spec.tag a.1 p.1, spec.tag a.1 p.2))⟩ :
          Scheme.Garbled)) =
        fun (k, f, coins) => (G.withTokenDecoding spec).gb k f coins := by
      funext ⟨k, f, coins⟩
      rfl
    exact heq ▸ hpack
  encode := heff.encode
  evalGarbled := heff.evalGarbled
  decode := tokenDecode_polyTime htag
  ev := heff.ev

/-- Any successful decoding forgery `Y' ≠ Ev(F, X)` against `G.withTokenDecoding spec` must
produce a wire chunk `Y'_o` differing from the honest wire token `(Ev(F, X))_o` whose tag under
`spec.tag k` equals `spec.tag k tok₀_o` or `spec.tag k tok₁_o`. In particular, for exact token
matching (`spec.tag = fun _ => id`), `Y'_o` must equal the inactive wire token. -/
theorem decode_withTokenDecoding_forgery_witness {Fn : Type} {G : Scheme Fn}
    {spec : OutputTokenSpec Fn G} (hwt : G.WellTyped) (hs : spec.Sound)
    {k : ℕ} {f : Fn} {coins x Y' y' : List Bool}
    (hc : coins.length = G.coinLen k (G.inLen f) (G.outLen f) (G.size f))
    (hx : x.length = G.inLen f)
    (hne : Y' ≠ G.evalGarbled (G.gb k f coins).fn (G.encode (G.gb k f coins).encInfo x))
    (hdec : (G.withTokenDecoding spec).decode
      ((G.withTokenDecoding spec).gb k f coins).decInfo Y' = some y') :
    ∃ o : Fin (G.outLen f),
      let p := (spec.tokens k f coins).getD o ([], [])
      let row := BitString.listRow (spec.tokenLen k f) o Y'
      row ≠ (if (G.ev f x).getD o false then p.2 else p.1) ∧
        (spec.tag k row = spec.tag k p.1 ∨ spec.tag k row = spec.tag k p.2) := by
  obtain ⟨_, h0, hpos⟩ := (decode_withTokenDecoding_eq_some_iff hs hc Y' y').mp hdec
  by_cases hm : G.outLen f = 0
  · exfalso
    have hev := hs.eval_eq_activeTokens k f coins hc x hx
    have hnil : spec.tokens k f coins = [] :=
      List.eq_nil_iff_length_eq_zero.mpr ((hs.length_tokens k f coins hc).trans hm)
    rw [h0 hm, hev, hnil, List.zip_nil_left, List.flatMap_nil] at hne
    exact hne rfl
  · have hmpos : 0 < G.outLen f := Nat.pos_of_ne_zero hm
    obtain ⟨hY'len, hrow⟩ := hpos hmpos
    have hwpos := hs.tokenLen_pos k f hmpos
    have hlen_ev : (G.ev f x).length = G.outLen f := hwt.1 f x hx
    have ⟨hflat, hYlen⟩ := zip_tokens_flatMap_eq_flatten (spec.tokens k f coins) (G.ev f x)
      (hs.length_tokens k f coins hc) hlen_ev (hs.token_lengths k f coins hc)
    have hY_eq := (hs.eval_eq_activeTokens k f coins hc x hx).trans hflat
    have hdiff : ∃ o : Fin (G.outLen f),
        BitString.listRow (spec.tokenLen k f) o Y' ≠
          (let p := (spec.tokens k f coins).getD o ([], [])
           if (G.ev f x).getD o false then p.2 else p.1) := by
      by_contra hall
      push Not at hall
      apply hne
      rw [hY_eq, ← flatten_listRows_eq_self hwpos hY'len]
      congr 1
      apply List.ext_getElem (by simp)
      intro i hi1 hi2
      have hi_m : i < G.outLen f := by simpa using hi2
      simpa [BitString.listRows] using hall ⟨i, hi_m⟩
    obtain ⟨o, ho⟩ := hdiff
    refine ⟨o, ho, ?_⟩
    have hro := hrow o
    cases hyo : y'.getD o false <;> simp only [hyo, Bool.false_eq_true, ↓reduceIte] at hro
    · exact Or.inl hro
    · exact Or.inr hro

/-! ## Point-and-permute token decoding vs `PointPermute.decodeWord` -/

namespace PointPermute

/-- Output token specification for `PointPermute.scheme family`: each output wire `o` has tokens
`(labelOf ... perm, labelOf ... (!perm))` of width `k + 2`. -/
@[expose] def outputTokenSpec (family : List Bool → List Bool → List Bool)
    (tag : ℕ → List Bool → List Bool := fun _ => id) :
    OutputTokenSpec ValidCircuit (PointPermute.scheme family) where
  tokenLen k _ := k + 2
  tokens k f coins := List.ofFn fun o : Fin f.1.m =>
    let v := f.1.n + f.1.q - f.1.m + o
    let p := permOf coins v
    (labelOf k (f.1.n + f.1.q) coins v p, labelOf k (f.1.n + f.1.q) coins v (!p))
  tag := tag

private theorem labelOf_perm_ne_not (k wires : ℕ) (coins : List Bool) (v : ℕ) (p : Bool) :
    labelOf k wires coins v p ≠ labelOf k wires coins v (!p) := by
  intro heq
  have hbit := congrArg (fun l => l.getD (k + 1) false) heq
  simp only [labelOf] at hbit
  have hlen1 : (keyOf k wires coins v p).length = k + 1 := by simp [keyOf]
  have hlen2 : (keyOf k wires coins v (!p)).length = k + 1 := by simp [keyOf]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen1, Nat.sub_self]
    at hbit
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen2, Nat.sub_self]
    at hbit
  cases p <;> simp at hbit

private theorem length_encList_constant {α : Type} {enc : α ↪ List Bool} {l : List α} {L : ℕ}
    (hl : ∀ x ∈ l, (enc x).length = L) :
    (encList enc l).length = l.length * (2 * L + 1) := by
  induction l with
  | nil => simp [encList_nil]
  | cons a rest ih =>
    rw [List.length_cons, encList_cons, List.length_append, length_frame,
      hl a List.mem_cons_self, ih fun x hx => hl x (List.mem_cons_of_mem _ hx)]
    ring

open ConventionalCircuit Circuits in
/-- Soundness of `PointPermute.outputTokenSpec family tag` whenever `tag k` separates distinct
`(k + 2)`-bit tokens (in particular for raw exact token matching `tag := fun _ => id`). -/
theorem outputTokenSpec_sound (family : List Bool → List Bool → List Bool)
    (tag : ℕ → List Bool → List Bool)
    (htag_inj : ∀ (k : ℕ) (u v : List Bool), u.length = k + 2 → v.length = k + 2 →
      tag k u = tag k v → u = v)
    (htag_len : ∀ (k : ℕ) (u : List Bool), u.length = k + 2 →
      (tag k u).length = (tag k (List.replicate (k + 2) false)).length) :
    (outputTokenSpec family tag).Sound where
  length_tokens k f _ _ := by simp [outputTokenSpec, scheme]
  tokenLen_pos k _ _ := by simp [outputTokenSpec]
  token_lengths k f coins _ p hp := by
    simp only [outputTokenSpec, List.mem_ofFn] at hp
    obtain ⟨o, rfl⟩ := hp
    simp [outputTokenSpec]
  tag_distinct k f coins _ p hp := by
    simp only [outputTokenSpec, List.mem_ofFn] at hp
    obtain ⟨o, rfl⟩ := hp
    intro hcol
    have hlen1 : (labelOf k (f.1.n + f.1.q) coins (f.1.n + f.1.q - f.1.m + o)
        (permOf coins (f.1.n + f.1.q - f.1.m + o))).length = k + 2 := length_labelOf _ _ _ _ _
    have hlen2 : (labelOf k (f.1.n + f.1.q) coins (f.1.n + f.1.q - f.1.m + o)
        (!(permOf coins (f.1.n + f.1.q - f.1.m + o)))).length = k + 2 :=
      length_labelOf _ _ _ _ _
    exact labelOf_perm_ne_not k (f.1.n + f.1.q) coins _ _ (htag_inj k _ _ hlen1 hlen2 hcol)
  eval_eq_activeTokens k f coins _ x hx := by
    have hev := evaluate_eq_of_evalStep (toCircuit f).isOrdered_topology
      (PRF.label (PRF.atLevel family (k + 1))) (slotTweak _ k)
      (garbleTable (toCircuit f) fullInterpretation (PRF.label (PRF.atLevel family (k + 1)))
        (slotTweak _ k) (keyFn k coins) (permFn coins))
      (encode (inputEncoding (keyFn k coins) (permFn coins)) (BitString.ofList f.1.n x))
      _ (evalStep_activeLabel (toCircuit f) fullInterpretation
        (PRF.label (PRF.atLevel family (k + 1))) (slotTweak _ k) (keyFn k coins) (permFn coins)
        (BitString.ofList f.1.n x))
    rw [gb_eq_encodeGarbled]
    simp only [scheme, encodeGarbled, garbleWith]
    rw [projectiveEncode_labelBits (n := f.1.n) _ hx,
      evalWord_encodeFn family k f _
        (fun i => inputEncoding (keyFn k coins) (permFn coins) i (BitString.ofList f.1.n x i)) _
        (evalStep_activeLabel (toCircuit f) fullInterpretation
          (PRF.label (PRF.atLevel family (k + 1))) (slotTweak _ k) (keyFn k coins) (permFn coins)
          (BitString.ofList f.1.n x))]
    have heval_circ : ∀ o : Fin f.1.m,
        (toCircuit f).eval fullInterpretation (BitString.ofList f.1.n x) o =
          (f.1.evalCirc x).getD o false := by
      intro o
      have h := congrArg (fun l => l.getD o.val false)
        (eval_toCircuit f (BitString.ofList f.1.n x))
      rw [BitString.ofFn_ofList (n := f.1.n) hx] at h
      simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, o.isLt] using h
    have hlen_ev : (f.1.evalCirc x).length = f.1.m :=
      ConventionalCircuit.length_evalCirc f.1 x f.2.m_le_q
    have hq : f.1.n + (toCircuit f).size = f.1.n + f.1.q := by rw [size_toCircuit]
    have ⟨hflat, _⟩ := zip_tokens_flatMap_eq_flatten (w := k + 2)
      ((outputTokenSpec family tag).tokens k f coins) (f.1.evalCirc x)
      (by simp [outputTokenSpec]) hlen_ev (fun p hp => by
        simp only [outputTokenSpec, List.mem_ofFn] at hp
        obtain ⟨o, rfl⟩ := hp
        simp)
    rw [hflat]
    congr 1
    apply List.ext_getElem (by simp)
    intro o ho1 ho2
    have ho' : o < f.1.m := by simpa using ho1
    have ho_tok : o < ((outputTokenSpec family tag).tokens k f coins).length := by
      simpa [outputTokenSpec] using ho'
    simp only [List.getElem_ofFn, activeLabel, Circuit.eval] at *
    have hbit : (toCircuit f).program.trace fullInterpretation (BitString.ofList f.1.n x)
        ((toCircuit f).outputs ⟨o, ho'⟩) = (f.1.evalCirc x).getD o false :=
      heval_circ ⟨o, ho'⟩
    have hout : ((toCircuit f).outputs ⟨o, ho'⟩).toNat = f.1.n + f.1.q - f.1.m + o := by
      rw [toNat_outputs_toCircuit]
    have hlabel := labelBits_keyFn k coins ((toCircuit f).outputs ⟨o, ho'⟩)
      ((toCircuit f).program.trace fullInterpretation (BitString.ofList f.1.n x)
        ((toCircuit f).outputs ⟨o, ho'⟩) + permFn coins ((toCircuit f).outputs ⟨o, ho'⟩))
    have hperm : permFn coins ((toCircuit f).outputs ⟨o, ho'⟩) =
        permOf coins (f.1.n + f.1.q - f.1.m + o) := by
      simp [permFn, hout]
    simp only [outputTokenSpec]
    rw [hlabel, hq, hout, hbit, hperm, Bool.add_eq_xor]
    cases (f.1.evalCirc x).getD o false <;> simp [ho']
  decInfo_length_eq k f f' coins coins' hn hm hq _ _ := by
    let T := (tag k (List.replicate (k + 2) false)).length
    let L := 2 * T + 1 + T
    have hpair_len : ∀ (g : ValidCircuit) (c : List Bool),
        ∀ x ∈ ((outputTokenSpec family tag).tokens k g c).map
            (fun p => (tag k p.1, tag k p.2)),
          (encPair encBits encBits x).length = L := by
      intro g c x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      simp only [outputTokenSpec, List.mem_ofFn] at hp
      obtain ⟨o, rfl⟩ := hp
      rw [length_encPair, encBits_apply, encBits_apply,
        htag_len k _ (length_labelOf _ _ _ _ _), htag_len k _ (length_labelOf _ _ _ _ _)]
    have h1 := length_encList_constant (hpair_len f coins)
    have h2 := length_encList_constant (hpair_len f' coins')
    simp only [tokenDecInfo, length_encPair, outputTokenSpec] at h1 h2 ⊢
    have hl1 : (((outputTokenSpec family tag).tokens k f coins).map
        fun p => (tag k p.1, tag k p.2)).length = f.1.m := by simp [outputTokenSpec]
    have hl2 : (((outputTokenSpec family tag).tokens k f' coins').map
        fun p => (tag k p.1, tag k p.2)).length = f'.1.m := by simp [outputTokenSpec]
    simp only [outputTokenSpec] at hl1 hl2
    have hm' : f.1.m = f'.1.m := hm
    rw [h1, h2, hl1, hl2, hm']
  nonDegenerate k f f' coins hn hm hq _ := by
    simp only [scheme] at hn hm hq
    refine ⟨rfl, ?_⟩
    apply List.ext_getElem
    · simp [outputTokenSpec, hm]
    · intro i hi1 hi2
      simp only [outputTokenSpec, List.getElem_ofFn, Fin.val_cast, hn, hq, hm]

/-- `PointPermute.outputTokenSpec family` with raw exact token matching (`tag := fun _ => id`) is
sound. -/
theorem outputTokenSpec_id_sound (family : List Bool → List Bool → List Bool) :
    (outputTokenSpec family).Sound :=
  outputTokenSpec_sound family (fun _ => id) (fun _ _ _ _ _ h => h) (fun _ _ h => by simp [h])

/-- `(PointPermute.scheme family)` is well typed. -/
theorem scheme_wellTyped (family : List Bool → List Bool → List Bool) :
    (scheme family).WellTyped :=
  ⟨fun f x _ => by simp [scheme, ConventionalCircuit.length_evalCirc f.1 x f.2.m_le_q],
   fun k _ f g hg Y y hy => by
     obtain ⟨coins, _, rfl⟩ := (scheme family).mem_support_eval_garble_iff.mp hg
     simp only [scheme, decodeWord] at hy
     split_ifs at hy with hd
     · cases hy
       simp [decInfoWord, scheme]
     · cases hy⟩

/-- `(PointPermute.scheme family).withTokenDecoding (PointPermute.outputTokenSpec family)` is a
valid garbling scheme. -/
theorem withTokenDecoding_isValid (family : List Bool → List Bool → List Bool) :
    ((scheme family).withTokenDecoding (outputTokenSpec family)).IsValid :=
  (scheme_isValid family).withTokenDecoding (scheme_wellTyped family)
    (outputTokenSpec_id_sound family)

/-- `(PointPermute.scheme family).withTokenDecoding (PointPermute.outputTokenSpec family)` is well
typed. -/
theorem withTokenDecoding_wellTyped (family : List Bool → List Bool → List Bool) :
    ((scheme family).withTokenDecoding (outputTokenSpec family)).WellTyped :=
  (scheme_wellTyped family).withTokenDecoding (outputTokenSpec_id_sound family)

private theorem outputTokenSpec_tokens_polyTime (family : List Bool → List Bool → List Bool) :
    ComputableInPolyTime
      (fun (k, f, coins) => (outputTokenSpec family).tokens k f coins)
      (encSchemeCoinsArg ValidCircuit encValidCircuit) (encList (encPair encBits encBits)) := by
  let E := encSchemeCoinsArg ValidCircuit encValidCircuit
  have hd : ComputableInPolyTime
      (fun p : ℕ × ValidCircuit × List Bool => (p.2.1.1.n, p.2.1.1.m, p.2.1.1.gateList))
      E encCircuitData :=
    circuitData_polyTime.comp (ComputableInPolyTime.fst _ _ |>.comp (ComputableInPolyTime.snd _ _))
  have hrange : ComputableInPolyTime
      (fun p : ℕ × ℕ × ℕ × ℕ × List Bool =>
        (List.range p.2.2.1).map fun o =>
          let v := p.2.1 + p.2.2.2.1 - p.2.2.1 + o
          let pm := permOf p.2.2.2.2 v
          (labelOf p.1 (p.2.1 + p.2.2.2.1) p.2.2.2.2 v pm,
           labelOf p.1 (p.2.1 + p.2.2.2.1) p.2.2.2.2 v (!pm)))
      (encPair encUnary (encPair encUnary (encPair encUnary (encPair encUnary encBits))))
      (encList (encPair encBits encBits)) := by
    have hperm : ComputableInPolyTime
        (fun a : (ℕ × ℕ × ℕ × ℕ × List Bool) × ℕ =>
          permOf a.1.2.2.2.2 (a.1.2.1 + a.1.2.2.2.1 - a.1.2.2.1 + a.2))
        (encPair (encPair encUnary (encPair encUnary (encPair encUnary (encPair encUnary encBits))))
          encUnary) encBool :=
      permOf_polyTime (by fun_prop) (by fun_prop)
    have hl1 : ComputableInPolyTime
        (fun a : (ℕ × ℕ × ℕ × ℕ × List Bool) × ℕ =>
          labelOf a.1.1 (a.1.2.1 + a.1.2.2.2.1) a.1.2.2.2.2
            (a.1.2.1 + a.1.2.2.2.1 - a.1.2.2.1 + a.2)
            (permOf a.1.2.2.2.2 (a.1.2.1 + a.1.2.2.2.1 - a.1.2.2.1 + a.2)))
        (encPair (encPair encUnary (encPair encUnary (encPair encUnary (encPair encUnary encBits))))
          encUnary) encBits :=
      labelOf_polyTime (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) hperm
    have hl2 : ComputableInPolyTime
        (fun a : (ℕ × ℕ × ℕ × ℕ × List Bool) × ℕ =>
          labelOf a.1.1 (a.1.2.1 + a.1.2.2.2.1) a.1.2.2.2.2
            (a.1.2.1 + a.1.2.2.2.1 - a.1.2.2.1 + a.2)
            (!(permOf a.1.2.2.2.2 (a.1.2.1 + a.1.2.2.2.1 - a.1.2.2.1 + a.2))))
        (encPair (encPair encUnary (encPair encUnary (encPair encUnary (encPair encUnary encBits))))
          encUnary) encBits :=
      labelOf_polyTime (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
        (ComputableInPolyTime.bool_not.comp hperm)
    exact ComputableInPolyTime.mapWithInput
      (ComputableInPolyTime.unary_range' (by fun_prop)) (hl1.prod hl2)
  have heq :
      (fun (k, f, coins) => (outputTokenSpec family).tokens k f coins) =
        fun p : ℕ × ValidCircuit × List Bool =>
          (List.range p.2.1.1.m).map fun o =>
            let v := p.2.1.1.n + p.2.1.1.gateList.length - p.2.1.1.m + o
            let pm := permOf p.2.2 v
            (labelOf p.1 (p.2.1.1.n + p.2.1.1.gateList.length) p.2.2 v pm,
             labelOf p.1 (p.2.1.1.n + p.2.1.1.gateList.length) p.2.2 v (!pm)) := by
    funext ⟨k, f, coins⟩
    apply List.ext_getElem
    · simp [outputTokenSpec]
    · intro i hi1 hi2
      simp [outputTokenSpec, ConventionalCircuit.length_gateList]
  rw [heq]
  have hk : ComputableInPolyTime (fun p : ℕ × ValidCircuit × List Bool => p.1) E encUnary := by
    fun_prop
  have hcoins : ComputableInPolyTime (fun p : ℕ × ValidCircuit × List Bool => p.2.2) E encBits := by
    fun_prop
  have hn := hd.fst'
  have hm := hd.snd'.fst'
  have hq := (ComputableInPolyTime.length_list (encPair encNat (encPair encNat encBits))).comp
    hd.snd'.snd'
  exact hrange.comp (hk.prod (hn.prod (hm.prod (hq.prod hcoins))))

/-- `(PointPermute.scheme family).withTokenDecoding (PointPermute.outputTokenSpec family)` is
efficient whenever `family` is computable in polynomial time. -/
theorem withTokenDecoding_isEfficient {family : List Bool → List Bool → List Bool}
    (hf : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits) :
    ((scheme family).withTokenDecoding (outputTokenSpec family)).IsEfficient encValidCircuit :=
  (scheme_isEfficient hf).withTokenDecoding
    (ComputableInPolyTime.unary_add' (ComputableInPolyTime.fst _ _) (.const 2))
    (outputTokenSpec_tokens_polyTime family)
    (ComputableInPolyTime.snd _ _)

/-- A minimal valid two-input, one-output, one-gate circuit used to witness bit-flipping
forgeries against `PointPermute.decodeWord`. -/
@[expose] def oneGateCircuit : ValidCircuit :=
  mTopoInv ⟨sizeTopo ⟨2, 1, 1, le_rfl, le_rfl, le_rfl, le_rfl⟩,
    sizeTopo_isValid ⟨2, 1, 1, le_rfl, le_rfl, le_rfl, le_rfl⟩⟩

private theorem oneGateCircuit_dims :
    oneGateCircuit.1.n = 2 ∧ oneGateCircuit.1.m = 1 ∧ oneGateCircuit.1.q = 1 :=
  ⟨rfl, rfl, rfl⟩

/-- A trivial strict-PPT `Aut` adversary against `PointPermute.scheme family`: it queries
`oneGateCircuit` on `[false, false]`, evaluates `Y = Ev(F, X)`, and flips every bit of `Y`.
Because `PointPermute.decodeWord` only checks `Y.length % d.length = 0`, it accepts `Y.map (!.)`
and breaks `aut` with probability `1`. -/
@[expose] def flipForger (family : List Bool → List Bool → List Bool) :
    AutAdversary ValidCircuit Unit where
  choose _ := pure (⟨oneGateCircuit, [false, false]⟩, ())
  guess _ view := pure ((evalWord family view.fn view.input).map (!·))

/-- `PointPermute.flipForger` runs in uniform strict PPT whenever `family` is polynomial time. -/
theorem isPPT_flipForger {family : List Bool → List Bool → List Bool}
    (hf : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits) :
    TwoStage.IsPPT encUnit (encQuery ValidCircuit encValidCircuit) OutSim.encObvView encBits
      encUnit (fun _ => flipForger family) where
  choose := (ComputableInPolyTime.const (encIn := encUnaryUnit)
    (encOut := encOutSimChooseOut ValidCircuit Unit encValidCircuit encUnit)
    (⟨oneGateCircuit, [false, false]⟩, ())).isPPTOn
  guess := by
    let EG := encPair encUnary (encPair encUnit OutSim.encObvView)
    have hev : ComputableInPolyTime (fun (k, st, view) => evalWord family view.fn view.input)
        EG encBits := by
      have heval := (scheme_isEfficient hf).evalGarbled
      have hview : ComputableInPolyTime (fun p : ℕ × Unit × ObvView => p.2.2) EG
          OutSim.encObvView := by fun_prop
      have hvfn := OutSim.encObvView_fn_polyTime hview
      have hvin := OutSim.encObvView_input_polyTime hview
      exact heval.comp (hvfn.prod hvin)
    have hmap : ComputableInPolyTime
        (fun (k, st, view) => (evalWord family view.fn view.input).map (!·)) EG encBits :=
      (bits_encList_polyTime encBool).2.comp
        ((ComputableInPolyTime.map ComputableInPolyTime.bool_not).comp
          ((bits_encList_polyTime encBool).1.comp hev))
    exact hmap.isPPTOn

private theorem length_evalWord_oneGateCircuit (family : List Bool → List Bool → List Bool)
    (k : ℕ) (coins : List Bool)
    (hc : coins.length = (scheme family).coinLen k 2 1 1) :
    (evalWord family (fnWord family k oneGateCircuit.1 coins)
      (projectiveEncode (encInfoWord k oneGateCircuit.1 coins) [false, false])).length =
      k + 2 := by
  have ⟨hn, hm, hq⟩ := oneGateCircuit_dims
  have hc0 : coins.length = (scheme family).coinLen k ((scheme family).inLen oneGateCircuit)
      ((scheme family).outLen oneGateCircuit) ((scheme family).size oneGateCircuit) := by
    simpa [scheme, hn, hm, hq] using hc
  have hx0 : ([false, false] : List Bool).length = (scheme family).inLen oneGateCircuit := by
    simp [scheme, hn]
  have hev := (outputTokenSpec_id_sound family).eval_eq_activeTokens k oneGateCircuit coins
    hc0 [false, false] hx0
  change evalWord family (fnWord family k oneGateCircuit.1 coins)
      (projectiveEncode (encInfoWord k oneGateCircuit.1 coins) [false, false]) = _ at hev
  have hlen_ev : ((scheme family).ev oneGateCircuit [false, false]).length = 1 := by
    simp [scheme, ConventionalCircuit.length_evalCirc oneGateCircuit.1 [false, false]
      oneGateCircuit.2.m_le_q, hm]
  have ⟨_, hlen⟩ := zip_tokens_flatMap_eq_flatten
    ((outputTokenSpec family).tokens k oneGateCircuit coins)
    ((scheme family).ev oneGateCircuit [false, false])
    ((outputTokenSpec_id_sound family).length_tokens k oneGateCircuit coins hc0)
    hlen_ev ((outputTokenSpec_id_sound family).token_lengths k oneGateCircuit coins hc0)
  rw [hev, hlen]
  simp [scheme, hm, outputTokenSpec]

/-- **`PointPermute.decodeWord` fails authenticity unconditionally with advantage `1`**: for every
`family` and every security parameter `k`, `flipForger family` wins `Aut` with probability `1`. -/
theorem autAdvantage_flipForger (family : List Bool → List Bool → List Bool) (k : ℕ) :
    autAdvantage (scheme family) k (flipForger family) = 1 := by
  have ⟨hn, hm, hq⟩ := oneGateCircuit_dims
  have hexp : ProbComp.eval (autExperiment (scheme family) k (flipForger family)) =
      PMF.pure true := by
    simp only [autExperiment, flipForger, ProbComp.eval_bind]
    have hvalid : ([false, false] : List Bool).length = (scheme family).inLen oneGateCircuit := by
      simp [scheme, hn]
    simp only [hvalid, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind]
    rw [← PMF.bind_const (ProbComp.eval ((scheme family).garble k oneGateCircuit)) (PMF.pure true)]
    refine PMF.bind_congr_on_support _ _ _ fun g hg => ?_
    obtain ⟨coins, hc, rfl⟩ := (scheme family).mem_support_eval_garble_iff.mp hg
    have hc' : coins.length = (scheme family).coinLen k 2 1 1 := by
      simpa [scheme, Scheme.coins, hn, hq] using hc
    have hlen : (evalWord family (fnWord family k oneGateCircuit.1 coins)
        (projectiveEncode (encInfoWord k oneGateCircuit.1 coins) [false, false])).length =
        k + 2 :=
      length_evalWord_oneGateCircuit family k coins hc'
    have hne : ((evalWord family (fnWord family k oneGateCircuit.1 coins)
        (projectiveEncode (encInfoWord k oneGateCircuit.1 coins) [false, false])).map (!·)) ≠
        evalWord family (fnWord family k oneGateCircuit.1 coins)
          (projectiveEncode (encInfoWord k oneGateCircuit.1 coins) [false, false]) := by
      intro heq
      have hhd := congrArg (fun l => l.getD 0 false) heq
      have hpos : 0 < (evalWord family (fnWord family k oneGateCircuit.1 coins)
          (projectiveEncode (encInfoWord k oneGateCircuit.1 coins) [false, false])).length := by
        omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hpos] at hhd
      cases (evalWord family (fnWord family k oneGateCircuit.1 coins)
        (projectiveEncode (encInfoWord k oneGateCircuit.1 coins) [false, false]))[0] <;>
        simp at hhd
    have hdlen : (decInfoWord oneGateCircuit.1 coins).length = 1 := by
      simp [decInfoWord, hm]
    have hdec : (decodeWord (decInfoWord oneGateCircuit.1 coins)
        ((evalWord family (fnWord family k oneGateCircuit.1 coins)
          (projectiveEncode (encInfoWord k oneGateCircuit.1 coins) [false, false])).map
          (!·))).isSome = true := by
      simp [decodeWord, hdlen, Nat.mod_one]
    simp [scheme, hdec, bne_iff_ne.mpr hne]
  simp [autAdvantage, Experiment.succProbability, Game.succProbability, hexp]

/-- By contrast, `(PointPermute.scheme family).withTokenDecoding (PointPermute.outputTokenSpec
family)` rejects the bit-flipped forgery on any coins whose two output wire tokens are not
bitwise complements of one another. -/
theorem decode_withTokenDecoding_flip_eq_none (family : List Bool → List Bool → List Bool)
    {k : ℕ} {coins : List Bool}
    (hc : coins.length = (scheme family).coinLen k 2 1 1)
    (hne_comp :
      let Y := evalWord family (fnWord family k oneGateCircuit.1 coins)
        (projectiveEncode (encInfoWord k oneGateCircuit.1 coins) [false, false])
      let v := oneGateCircuit.1.n + oneGateCircuit.1.q - oneGateCircuit.1.m + 0
      let p := permOf coins v
      Y.map (!·) ≠ labelOf k (oneGateCircuit.1.n + oneGateCircuit.1.q) coins v (!p) ∧
      Y.map (!·) ≠ labelOf k (oneGateCircuit.1.n + oneGateCircuit.1.q) coins v p) :
    let G' := (scheme family).withTokenDecoding (outputTokenSpec family)
    let g' := G'.gb k oneGateCircuit coins
    let Y := evalWord family g'.fn (G'.encode g'.encInfo [false, false])
    G'.decode g'.decInfo (Y.map (!·)) = none := by
  intro G' g' Y
  have ⟨hn, hm, hq⟩ := oneGateCircuit_dims
  by_contra hsome
  obtain ⟨y', hy'⟩ := Option.ne_none_iff_exists'.mp hsome
  have hc' : coins.length = (scheme family).coinLen k ((scheme family).inLen oneGateCircuit)
      ((scheme family).outLen oneGateCircuit) ((scheme family).size oneGateCircuit) := by
    simpa [scheme, hn, hm, hq] using hc
  obtain ⟨hylen, hflat⟩ := (decode_withTokenDecoding_id_eq_some_iff rfl
    (outputTokenSpec_id_sound family) hc' (Y.map (!·)) y').mp hy'
  have h1 : y'.length = 1 := by simpa [scheme, hm] using hylen
  obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp h1
  simp only [outputTokenSpec, scheme] at hflat
  have hzip : ((List.ofFn fun o : Fin oneGateCircuit.1.m =>
      let v := oneGateCircuit.1.n + oneGateCircuit.1.q - oneGateCircuit.1.m + o
      let p := permOf coins v
      (labelOf k (oneGateCircuit.1.n + oneGateCircuit.1.q) coins v p,
       labelOf k (oneGateCircuit.1.n + oneGateCircuit.1.q) coins v (!p))).zip [b]).flatMap
      (fun (p, bit) => if bit then p.2 else p.1) =
      if b then labelOf k (oneGateCircuit.1.n + oneGateCircuit.1.q) coins
          (oneGateCircuit.1.n + oneGateCircuit.1.q - oneGateCircuit.1.m + 0)
          (!(permOf coins (oneGateCircuit.1.n + oneGateCircuit.1.q - oneGateCircuit.1.m + 0)))
      else labelOf k (oneGateCircuit.1.n + oneGateCircuit.1.q) coins
          (oneGateCircuit.1.n + oneGateCircuit.1.q - oneGateCircuit.1.m + 0)
          (permOf coins (oneGateCircuit.1.n + oneGateCircuit.1.q - oneGateCircuit.1.m + 0)) := by
    rw [List.ofFn_congr hm]
    simp [List.ofFn_succ, List.ofFn_zero]
  rw [hzip] at hflat
  cases b
  · exact hne_comp.2 (by simpa [G', g', Y, Scheme.withTokenDecoding, scheme] using hflat)
  · exact hne_comp.1 (by simpa [G', g', Y, Scheme.withTokenDecoding, scheme] using hflat)

end PointPermute

/-! ## Boneh–Shoup Ch. 23 Def. 23.4 output-simulatability (`OutSim`) -/

/-- A three-stage `out.sim` adversary ([BonehShoup2023], Chapter 23, Definition 23.4; page
numbers not PDF-verified): stage 1 chooses a query `(f, x)` and state `σ₁`; stage 2 receives
the oblivious view `(F, X)` (without `decInfo`) and outputs a candidate garbled output `Y'` and
state `σ₂`; stage 3 receives the decoded result `Option (List Bool)` and outputs a distinguishing
bit. -/
structure OutSimAdversary (Fn σ₁ σ₂ : Type) where
  /-- Stage 1: choose a query `(f, x)` and initial state `σ₁`. -/
  choose : Unit → ProbComp (Query Fn × σ₁)
  /-- Stage 2: given `σ₁` and the oblivious view `(F, X)`, output a garbled output `Y'` and state
  `σ₂`. -/
  forge : σ₁ → ObvView → ProbComp (List Bool × σ₂)
  /-- Stage 3: given `σ₂` and the decoded result `Option (List Bool)`, output a bit. -/
  guess : σ₂ → Option (List Bool) → ProbComp Bool

/-- Uniform strict PPT admissibility for a family of `OutSimAdversary` instances. -/
structure OutSimAdversary.IsPPT {Fn σ₁ σ₂ : Type}
    (encFn : Fn ↪ List Bool) (encσ₁ : σ₁ ↪ List Bool) (encσ₂ : σ₂ ↪ List Bool)
    (A : ℕ → OutSimAdversary Fn σ₁ σ₂) : Prop where
  /-- Stage 1 runs in uniform strict PPT from `(1^k, ())`. -/
  choose : IsPPTOn encUnaryUnit (encOutSimChooseOut Fn σ₁ encFn encσ₁)
    (fun (k, u) => (A k).choose u)
  /-- Stage 2 runs in uniform strict PPT from `(1^k, (st₁, view))`. -/
  forge : IsPPTOn (encOutSimForgeIn σ₁ encσ₁) (encOutSimForgeOut σ₂ encσ₂)
    (fun (k, st₁, view) => (A k).forge st₁ view)
  /-- Stage 3 runs in uniform strict PPT from `(1^k, (st₂, out))`. -/
  guess : IsPPTOn (encOutSimGuessIn σ₂ encσ₂) encBool
    (fun (k, st₂, out) => (A k).guess st₂ out)

/-- Experiment `b` of the output-simulatability game `OutSim` ([BonehShoup2023], Chapter 23,
Definition 23.4; page numbers not PDF-verified): on a valid query (`x.length = G.inLen f`),
* `b = true` gives `A` the real oblivious view `(F, X)` and decodes its output `Y'` with
  `G.decode g.decInfo Y'`;
* `b = false` gives `A` the simulated view `view ← S (Φ.phi q.fn)` and checks `Y' == G.evalGarbled
  view.fn view.input`, returning `some (G.ev q.fn q.input)` if equal and `none` otherwise.
On invalid queries (`x.length ≠ G.inLen f`), both worlds immediately return `false`. -/
noncomputable def outSimExperiment {Fn Λ σ₁ σ₂ : Type} (G : Scheme Fn) (Φ : SideInfo Fn Λ)
    (k : ℕ) (S : ObvSimulator Λ) (A : OutSimAdversary Fn σ₁ σ₂) (b : Bool) : Experiment := do
  let (q, st₁) ← A.choose ()
  if q.input.length = G.inLen q.fn then
    if b then
      let g ← G.garble k q.fn
      let X := G.encode g.encInfo q.input
      let (Y', st₂) ← A.forge st₁ ⟨g.fn, X⟩
      A.guess st₂ (G.decode g.decInfo Y')
    else
      let view ← S (Φ.phi q.fn)
      let (Y', st₂) ← A.forge st₁ view
      let out := if Y' == G.evalGarbled view.fn view.input then some (G.ev q.fn q.input) else none
      A.guess st₂ out
  else
    return false

/-- The `out.sim` advantage of `A` against simulator `S`. -/
noncomputable def outSimAdvantage {Fn Λ σ₁ σ₂ : Type} (G : Scheme Fn) (Φ : SideInfo Fn Λ)
    (k : ℕ) (S : ObvSimulator Λ) (A : OutSimAdversary Fn σ₁ σ₂) : ℝ≥0 :=
  Experiment.advantage (outSimExperiment G Φ k S A false) (outSimExperiment G Φ k S A true)

theorem outSimAdvantage_le_one {Fn Λ σ₁ σ₂ : Type} (G : Scheme Fn) (Φ : SideInfo Fn Λ) (k : ℕ)
    (S : ObvSimulator Λ) (A : OutSimAdversary Fn σ₁ σ₂) :
    outSimAdvantage G Φ k S A ≤ 1 :=
  Game.advantage_le_one _ _

/-- **Asymptotic output-simulatability** (`∀ A ∃ S`): for every uniform strict PPT
`OutSimAdversary`, there exists a uniform strict PPT simulator `S` on `(1^k, Φ(f))` whose
`out.sim` advantage is negligible. As a formal asymptotic game over arbitrary side information `Φ`
with uniform strict PPT three-stage adversaries, this notion is novel to this library (motivated by
[BonehShoup2023], Chapter 23, Definition 23.4; exact locators in Chapter 23 were not PDF-verified).
For efficient, correct schemes it is equivalent to `obv.sim ∧ aut` (`Scheme.OutSimSecure.obvSim`,
`Scheme.OutSimSecure.aut`, `outSimSecure_of_obvSim_and_aut`). -/
@[expose] def Scheme.OutSimSecure {Fn Λ : Type} (G : Scheme Fn) (Φ : SideInfo Fn Λ)
    (encFn : Fn ↪ List Bool) (encΛ : Λ ↪ List Bool) : Prop :=
  ∀ (σ₁ σ₂ : Type) (encσ₁ : σ₁ ↪ List Bool) (encσ₂ : σ₂ ↪ List Bool)
    (A : ℕ → OutSimAdversary Fn σ₁ σ₂),
    OutSimAdversary.IsPPT encFn encσ₁ encσ₂ A →
      ∃ S : ℕ → ObvSimulator Λ,
        IsPPTOn (encObvSimIn Λ encΛ) OutSim.encObvView (fun (k, φ) => S k φ) ∧
        Negligible fun k => outSimAdvantage G Φ k (S k) (A k)

/-- **Universal-simulator output-simulatability** (`∃ S ∀ A`): one uniform strict PPT simulator
`S` on `(1^k, Φ(f))` achieves negligible `out.sim` advantage against every uniform strict PPT
`OutSimAdversary`. This universal-simulator strengthening of `Scheme.OutSimSecure` is novel to this
library (analogous to `Scheme.PrvSimSecureUniversal`). -/
@[expose] def Scheme.OutSimSecureUniversal {Fn Λ : Type} (G : Scheme Fn) (Φ : SideInfo Fn Λ)
    (encFn : Fn ↪ List Bool) (encΛ : Λ ↪ List Bool) : Prop :=
  ∃ S : ℕ → ObvSimulator Λ,
    IsPPTOn (encObvSimIn Λ encΛ) OutSim.encObvView (fun (k, φ) => S k φ) ∧
      ∀ (σ₁ σ₂ : Type) (encσ₁ : σ₁ ↪ List Bool) (encσ₂ : σ₂ ↪ List Bool)
        (A : ℕ → OutSimAdversary Fn σ₁ σ₂),
        OutSimAdversary.IsPPT encFn encσ₁ encσ₂ A →
          Negligible fun k => outSimAdvantage G Φ k (S k) (A k)

/-- A universal simulator for `out.sim` yields a per-adversary simulator. -/
theorem Scheme.OutSimSecureUniversal.outSimSecure {Fn Λ : Type} {G : Scheme Fn}
    {Φ : SideInfo Fn Λ} {encFn : Fn ↪ List Bool} {encΛ : Λ ↪ List Bool}
    (h : G.OutSimSecureUniversal Φ encFn encΛ) :
    G.OutSimSecure Φ encFn encΛ :=
  let ⟨S, hS, hneg⟩ := h
  fun σ₁ σ₂ encσ₁ encσ₂ A hA => ⟨S, hS, hneg σ₁ σ₂ encσ₁ encσ₂ A hA⟩

/-! ## Non-asymptotic and strict-PPT relations: `OutSim`, `ObvSim`, and `Aut` -/

section Reductions

variable {Fn Λ σ σ₁ σ₂ : Type}

/-- Lift an `obv.sim` adversary `B` into an `out.sim` adversary that ignores the decoded result
and invokes `B.guess` on `some view`. -/
@[expose] def obvSimToOutSim (B : ObvSimAdversary Fn σ) :
    OutSimAdversary Fn σ (σ × ObvView) where
  choose := B.choose
  forge st view := pure ([], (st, view))
  guess s _ := B.guess s.1 (some s.2)

private theorem advantage_bind_ite_cancel {α : Type} (μ : PMF α) (P : α → Prop)
    [DecidablePred P] (g₀ g₁ inv₀ inv₁ : α → Game) :
    Game.advantage (μ.bind fun a => if P a then g₀ a else inv₀ a)
        (μ.bind fun a => if P a then g₁ a else inv₀ a) =
      Game.advantage (μ.bind fun a => if P a then g₀ a else inv₁ a)
        (μ.bind fun a => if P a then g₁ a else inv₁ a) := by
  have hne : ∀ f : α → Game, (∑' a : α, μ a * f a true) ≠ ⊤ := fun f => by
    simpa [PMF.bind_apply] using PMF.apply_ne_top (μ.bind f) true
  have hsplit : ∀ f₀ f₁ : α → Game,
      ((μ.bind f₀) true).toReal - ((μ.bind f₁) true).toReal =
        ∑' a : α, (μ a).toReal * ((f₀ a true).toReal - (f₁ a true).toReal) := by
    intro f₀ f₁
    have hs0 : Summable fun a => (μ a * f₀ a true).toReal := ENNReal.summable_toReal (hne f₀)
    have hs1 : Summable fun a => (μ a * f₁ a true).toReal := ENNReal.summable_toReal (hne f₁)
    simp only [PMF.bind_apply]
    rw [ENNReal.tsum_toReal_eq
        (fun a => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)),
      ENNReal.tsum_toReal_eq
        (fun a => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)),
      ← Summable.tsum_sub hs0 hs1]
    refine tsum_congr fun a => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, mul_sub]
  rw [← NNReal.coe_inj, Game.coe_advantage, Game.coe_advantage, Game.coe_succProbability,
    Game.coe_succProbability, Game.coe_succProbability, Game.coe_succProbability]
  congr 1
  rw [hsplit, hsplit]
  refine tsum_congr fun a => ?_
  by_cases ha : P a <;> simp [ha]

/-- `obvSimToOutSim` preserves `obv.sim` advantage identically. -/
theorem obvSimAdvantage_eq_outSimAdvantage (G : Scheme Fn) (Φ : SideInfo Fn Λ) (k : ℕ)
    (S : ObvSimulator Λ) (B : ObvSimAdversary Fn σ) :
    obvSimAdvantage G Φ k S B = outSimAdvantage G Φ k S (obvSimToOutSim B) := by
  have hadv : ∀ b : Bool, ProbComp.eval (obvSimExperiment G Φ k S B b) =
      (ProbComp.eval (B.choose ())).bind fun (q, st) =>
        if q.input.length = G.inLen q.fn then
          (ProbComp.eval (if b then G.obvView k q else S (Φ.phi q.fn))).bind fun view =>
            ProbComp.eval (B.guess st (some view))
        else
          ProbComp.eval (B.guess st none) := by
    intro b
    simp only [obvSimExperiment, ProbComp.eval_bind]
    refine Probability.PMF.bind_congr_on_support _ _ _ fun ⟨q, st⟩ _ => ?_
    by_cases hlen : q.input.length = G.inLen q.fn <;> cases b <;>
      simp [hlen, ProbComp.eval_bind]
  have hout : ∀ b : Bool, ProbComp.eval (outSimExperiment G Φ k S (obvSimToOutSim B) b) =
      (ProbComp.eval (B.choose ())).bind fun (q, st) =>
        if q.input.length = G.inLen q.fn then
          (ProbComp.eval (if b then G.obvView k q else S (Φ.phi q.fn))).bind fun view =>
            ProbComp.eval (B.guess st (some view))
        else
          PMF.pure false := by
    intro b
    simp only [outSimExperiment, obvSimToOutSim, ProbComp.eval_bind]
    refine Probability.PMF.bind_congr_on_support _ _ _ fun ⟨q, st⟩ _ => ?_
    by_cases hlen : q.input.length = G.inLen q.fn <;> cases b <;>
      simp [hlen, Scheme.obvView, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
        PMF.bind_bind, PMF.pure_bind, PMF.map, Function.comp_def]
  simp only [obvSimAdvantage, outSimAdvantage, Experiment.advantage, hadv false, hadv true,
    hout false, hout true]
  exact advantage_bind_ite_cancel (ProbComp.eval (B.choose ()))
    (fun p : Query Fn × σ => p.1.input.length = G.inLen p.1.fn)
    (fun p => (ProbComp.eval (S (Φ.phi p.1.fn))).bind fun view =>
      ProbComp.eval (B.guess p.2 (some view)))
    (fun p => (ProbComp.eval (G.obvView k p.1)).bind fun view =>
      ProbComp.eval (B.guess p.2 (some view)))
    (fun p => ProbComp.eval (B.guess p.2 none)) (fun _ => PMF.pure false)

/-- `obvSimToOutSim` preserves uniform strict PPT. -/
theorem isPPT_obvSimToOutSim {encFn : Fn ↪ List Bool} {encσ : σ ↪ List Bool}
    {B : ℕ → ObvSimAdversary Fn σ}
    (hB : TwoStage.IsPPT encUnit (encQuery Fn encFn) (encOption OutSim.encObvView) encBool encσ B) :
    OutSimAdversary.IsPPT encFn encσ (encObvOutState σ encσ) (fun k => obvSimToOutSim (B k)) where
  choose := hB.choose
  forge := by
    let EI := encOutSimForgeIn σ encσ
    let EO := encOutSimForgeOut (σ × ObvView) (encObvOutState σ encσ)
    have hst : ComputableInPolyTime (fun p : ℕ × σ × ObvView => p.2.1) EI encσ := by fun_prop
    have hview : ComputableInPolyTime (fun p : ℕ × σ × ObvView => p.2.2) EI OutSim.encObvView := by
      fun_prop
    have hout : ComputableInPolyTime
        (fun p : ℕ × σ × ObvView => (([] : List Bool), (p.2.1, p.2.2))) EI EO :=
      (ComputableInPolyTime.const ([] : List Bool)).prod (hst.prod hview)
    convert hout.isPPTOn using 1
    funext ⟨k, st₁, view⟩
    rfl
  guess := by
    let EI := encOutSimGuessIn (σ × ObvView) (encObvOutState σ encσ)
    have hk : ComputableInPolyTime
        (fun p : ℕ × (σ × ObvView) × Option (List Bool) => p.1) EI encUnary := by fun_prop
    have hst : ComputableInPolyTime
        (fun p : ℕ × (σ × ObvView) × Option (List Bool) => p.2.1.1) EI encσ := by fun_prop
    have hview : ComputableInPolyTime
        (fun p : ℕ × (σ × ObvView) × Option (List Bool) => some p.2.1.2) EI
        (encOption OutSim.encObvView) :=
      (ComputableInPolyTime.optionSome OutSim.encObvView).comp (by fun_prop)
    convert hB.guess.preprocess (hk.prod (hst.prod hview)) using 1
    funext ⟨k, ⟨st, view⟩, out⟩
    rfl

/-- Embed an `aut` adversary `A` into an `out.sim` adversary that outputs `Y' ← A.guess st view`
in stage 2 and checks `(Y' != G.evalGarbled view.fn view.input) && out.isSome` in stage 3. -/
@[expose] def autToOutSim (G : Scheme Fn) (A : AutAdversary Fn σ) :
    OutSimAdversary Fn σ (List Bool × ObvView) where
  choose := A.choose
  forge st view := do
    let Y' ← A.guess st view
    pure (Y', (Y', view))
  guess s out := pure ((s.1 != G.evalGarbled s.2.fn s.2.input) && out.isSome)

/-- Against any simulator `S`, `autToOutSim G A` turns `autExperiment` into `outSimAdvantage`
with zero ideal winning probability (`autAdvantage = outSimAdvantage`). -/
theorem autAdvantage_eq_outSimAdvantage (G : Scheme Fn) (Φ : SideInfo Fn Λ) (k : ℕ)
    (S : ObvSimulator Λ) (A : AutAdversary Fn σ) :
    autAdvantage G k A = outSimAdvantage G Φ k S (autToOutSim G A) := by
  have hfalse : ProbComp.eval (outSimExperiment G Φ k S (autToOutSim G A) false) =
      PMF.pure false := by
    simp only [outSimExperiment, autToOutSim, ProbComp.eval_bind]
    rw [← PMF.bind_const (ProbComp.eval (A.choose ())) (PMF.pure false)]
    refine PMF.bind_congr_on_support _ _ _ fun ⟨q, st₁⟩ _ => ?_
    by_cases hlen : q.input.length = G.inLen q.fn
    · simp only [hlen, Bool.false_eq_true, ↓reduceIte]
      rw [ProbComp.eval_bind, ← PMF.bind_const (ProbComp.eval (S (Φ.phi q.fn))) (PMF.pure false)]
      refine PMF.bind_congr_on_support _ _ _ fun view _ => ?_
      simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
      rw [← PMF.bind_const (ProbComp.eval (A.guess st₁ view)) (PMF.pure false)]
      refine PMF.bind_congr_on_support _ _ _ fun Y' _ => ?_
      by_cases heq : Y' = G.evalGarbled view.fn view.input
      · simp [heq]
      · simp [heq]
    · simp [hlen, ProbComp.eval_pure]
  have htrue : ProbComp.eval (outSimExperiment G Φ k S (autToOutSim G A) true) =
      ProbComp.eval (autExperiment G k A) := by
    simp only [outSimExperiment, autToOutSim, autExperiment, ProbComp.eval_bind]
    refine PMF.bind_congr_on_support _ _ _ fun ⟨q, st₁⟩ _ => ?_
    by_cases hlen : q.input.length = G.inLen q.fn
    · simp [hlen, ProbComp.eval_bind]
    · simp [hlen, ProbComp.eval_pure]
  rw [outSimAdvantage, Experiment.advantage, hfalse, htrue, Game.advantage_pure_false_left,
    autAdvantage, Experiment.succProbability]

/-- `autToOutSim` runs in uniform strict PPT whenever `A` does and `G.evalGarbled` is computable
in polynomial time (for example from `G.IsEfficient`). -/
theorem isPPT_autToOutSim (G : Scheme Fn) {encFn : Fn ↪ List Bool} {encσ : σ ↪ List Bool}
    (heval : ComputableInPolyTime (fun (F, X) => G.evalGarbled F X) (encPair encBits encBits)
      encBits)
    {A : ℕ → AutAdversary Fn σ}
    (hA : TwoStage.IsPPT encUnit (encQuery Fn encFn) OutSim.encObvView encBits encσ A) :
    OutSimAdversary.IsPPT encFn encσ encAutOutState (fun k => autToOutSim G (A k)) where
  choose := hA.choose
  forge := by
    let EI := encOutSimForgeIn σ encσ
    let EO := encOutSimForgeOut (List Bool × ObvView) encAutOutState
    have hview : ComputableInPolyTime (fun p : ℕ × σ × ObvView => p.2.2) EI OutSim.encObvView := by
      fun_prop
    have hpost : IsPPTOn (encPair EI encBits) EO
        (fun (a, Y') => pure (Y', (Y', a.2.2))) := by
      refine ComputableInPolyTime.isPPTOn ?_
      have hY : ComputableInPolyTime (fun p : (ℕ × σ × ObvView) × List Bool => p.2)
          (encPair EI encBits) encBits := by fun_prop
      have hv : ComputableInPolyTime (fun p : (ℕ × σ × ObvView) × List Bool => p.1.2.2)
          (encPair EI encBits) OutSim.encObvView := hview.comp (ComputableInPolyTime.fst _ _)
      exact (hY.prod (hY.prod hv)).of_enc_eq fun _ => rfl
    exact hA.guess.bind_with hpost
  guess := by
    let EI := encOutSimGuessIn (List Bool × ObvView) encAutOutState
    have hY' : ComputableInPolyTime
        (fun p : ℕ × (List Bool × ObvView) × Option (List Bool) => p.2.1.1) EI encBits := by
      fun_prop
    have hview : ComputableInPolyTime
        (fun p : ℕ × (List Bool × ObvView) × Option (List Bool) => p.2.1.2) EI
        OutSim.encObvView := by fun_prop
    have hfn := OutSim.encObvView_fn_polyTime hview
    have hin := OutSim.encObvView_input_polyTime hview
    have hev : ComputableInPolyTime
        (fun p : ℕ × (List Bool × ObvView) × Option (List Bool) =>
          G.evalGarbled p.2.1.2.fn p.2.1.2.input) EI encBits :=
      heval.comp (hfn.prod hin)
    have hout : ComputableInPolyTime
        (fun p : ℕ × (List Bool × ObvView) × Option (List Bool) => p.2.2) EI
        (encOption encBits) := by fun_prop
    have hisSome : ComputableInPolyTime
        (fun p : ℕ × (List Bool × ObvView) × Option (List Bool) => p.2.2.isSome) EI encBool :=
      ComputableInPolyTime.optionIsSome hout
    have hbool := ComputableInPolyTime.bool_and'
      (ComputableInPolyTime.bool_not.comp (ComputableInPolyTime.decide_eq' hY' hev))
      hisSome
    have hbool' : ComputableInPolyTime
        (fun p : ℕ × (List Bool × ObvView) × Option (List Bool) =>
          (p.2.1.1 != G.evalGarbled p.2.1.2.fn p.2.1.2.input) && p.2.2.isSome) EI encBool := by
      convert hbool using 1
      funext p
      by_cases heq : p.2.1.1 = G.evalGarbled p.2.1.2.fn p.2.1.2.input <;> simp [heq]
    exact hbool'.isPPTOn

/-- `PointPermute.scheme family` is NOT output-simulatable for any polynomial-time `family`,
witnessed by `autToOutSim (scheme family) (flipForger family)` achieving advantage `1`. -/
theorem PointPermute.not_outSimSecure {family : List Bool → List Bool → List Bool}
    (hf : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits) (Φ : SideInfo ValidCircuit ValidTopo) :
    ¬ (PointPermute.scheme family).OutSimSecure Φ encValidCircuit encValidTopo := by
  intro hout
  have hA := isPPT_autToOutSim (PointPermute.scheme family)
    (PointPermute.scheme_isEfficient hf).evalGarbled (PointPermute.isPPT_flipForger hf)
  obtain ⟨S, _, hneg⟩ := hout _ _ encUnit encAutOutState
    (fun _ => autToOutSim (PointPermute.scheme family) (PointPermute.flipForger family)) hA
  have h1 : ∀ k, outSimAdvantage (PointPermute.scheme family) Φ k (S k)
      (autToOutSim (PointPermute.scheme family) (PointPermute.flipForger family)) = 1 := by
    intro k
    rw [← autAdvantage_eq_outSimAdvantage, PointPermute.autAdvantage_flipForger]
  exact not_negligible_const one_ne_zero (by simpa [h1] using hneg)

/-- Extract an `Aut` adversary from an `OutSimAdversary`: run `choose` and `forge`, then output
the forged `Y'`. -/
@[expose] def outSimToAut (A : OutSimAdversary Fn σ₁ σ₂) : AutAdversary Fn σ₁ where
  choose := A.choose
  guess st₁ view := do
    let (Y', _) ← A.forge st₁ view
    pure Y'

/-- `outSimToAut` preserves uniform strict PPT. -/
theorem isPPT_outSimToAut {encFn : Fn ↪ List Bool} {encσ₁ : σ₁ ↪ List Bool} {encσ₂ : σ₂ ↪ List Bool}
    {A : ℕ → OutSimAdversary Fn σ₁ σ₂} (hA : OutSimAdversary.IsPPT encFn encσ₁ encσ₂ A) :
    TwoStage.IsPPT encUnit (encQuery Fn encFn) OutSim.encObvView encBits encσ₁
      (fun k => outSimToAut (A k)) where
  choose := hA.choose
  guess := by
    have hf : IsPPTOn (encPair (encOutSimForgeIn σ₁ encσ₁) (encOutSimForgeOut σ₂ encσ₂)) encBits
        (fun (_, p) => pure p.1) := by
      refine ComputableInPolyTime.isPPTOn ?_
      exact (ComputableInPolyTime.fst encBits encσ₂).comp (ComputableInPolyTime.snd _ _)
    exact hA.forge.bind_with hf

/-- Extract an `obv.sim` adversary from an `OutSimAdversary`: store the query `q` in state and, on
`some view`, run `A.forge`, simulate the ideal decoded output `if Y' == G.evalGarbled view.fn
view.input then some (G.ev q.fn q.input) else none`, and call `A.guess`. -/
@[expose] def outSimToObvSim (G : Scheme Fn) (A : OutSimAdversary Fn σ₁ σ₂) :
    ObvSimAdversary Fn (Query Fn × σ₁) where
  choose _ := do
    let (q, st₁) ← A.choose ()
    pure (q, (q, st₁))
  guess s mview :=
    match mview with
    | none => pure false
    | some view => do
      let (Y', st₂) ← A.forge s.2 view
      let out := if Y' == G.evalGarbled view.fn view.input then some (G.ev s.1.fn s.1.input)
        else none
      A.guess st₂ out

/-- `outSimToObvSim` runs in uniform strict PPT whenever `A` does and `G.evalGarbled` and `G.ev`
are computable in polynomial time. -/
theorem isPPT_outSimToObvSim (G : Scheme Fn) {encFn : Fn ↪ List Bool} {encσ₁ : σ₁ ↪ List Bool}
    {encσ₂ : σ₂ ↪ List Bool}
    (heval : ComputableInPolyTime (fun (F, X) => G.evalGarbled F X) (encPair encBits encBits)
      encBits)
    (hev : ComputableInPolyTime (fun (f, x) => G.ev f x) (encPair encFn encBits) encBits)
    {A : ℕ → OutSimAdversary Fn σ₁ σ₂} (hA : OutSimAdversary.IsPPT encFn encσ₁ encσ₂ A) :
    TwoStage.IsPPT encUnit (encQuery Fn encFn) (encOption OutSim.encObvView) encBool
      (encOutSimObvState Fn σ₁ encFn encσ₁) (fun k => outSimToObvSim G (A k)) where
  choose := by
    let EI := encUnaryUnit
    let EO := encPair (encQuery Fn encFn) (encOutSimObvState Fn σ₁ encFn encσ₁)
    have hpost : IsPPTOn (encPair EI (encOutSimChooseOut Fn σ₁ encFn encσ₁)) EO
        (fun (_, p) => pure (p.1, p)) := by
      refine ComputableInPolyTime.isPPTOn ?_
      have hp : ComputableInPolyTime
          (fun x : (ℕ × Unit) × (Query Fn × σ₁) => x.2)
          (encPair EI (encOutSimChooseOut Fn σ₁ encFn encσ₁))
          (encOutSimChooseOut Fn σ₁ encFn encσ₁) := by fun_prop
      exact ((ComputableInPolyTime.fst (encQuery Fn encFn) encσ₁).comp hp).prod hp
    exact hA.choose.bind_with hpost
  guess := by
    let EI := encPair encUnary (encPair (encOutSimObvState Fn σ₁ encFn encσ₁)
      (encOption OutSim.encObvView))
    have hnone : IsPPTOn EI encBool (fun _ => pure false) :=
      (ComputableInPolyTime.const false).isPPTOn
    have hsome : IsPPTOn (encPair EI OutSim.encObvView) encBool
        (fun (a, view) => do
          let (Y', st₂) ← (A a.1).forge a.2.1.2 view
          let out := if Y' == G.evalGarbled view.fn view.input
            then some (G.ev a.2.1.1.fn a.2.1.1.input) else none
          (A a.1).guess st₂ out) := by
      have hk : ComputableInPolyTime
          (fun p : (ℕ × (Query Fn × σ₁) × Option ObvView) × ObvView => p.1.1)
          (encPair EI OutSim.encObvView) encUnary := by fun_prop
      have hst₁ : ComputableInPolyTime
          (fun p : (ℕ × (Query Fn × σ₁) × Option ObvView) × ObvView => p.1.2.1.2)
          (encPair EI OutSim.encObvView) encσ₁ := by fun_prop
      have hv : ComputableInPolyTime
          (fun p : (ℕ × (Query Fn × σ₁) × Option ObvView) × ObvView => p.2)
          (encPair EI OutSim.encObvView) OutSim.encObvView := by fun_prop
      have hforge := hA.forge.preprocess (hk.prod (hst₁.prod hv))
      have hcont : IsPPTOn (encPair (encPair EI OutSim.encObvView) (encOutSimForgeOut σ₂ encσ₂))
          encBool
          (fun (x, (Y', st₂)) =>
            let out := if Y' == G.evalGarbled x.2.fn x.2.input
              then some (G.ev x.1.2.1.1.fn x.1.2.1.1.input) else none
            (A x.1.1).guess st₂ out) := by
        let EM := encPair (encPair EI OutSim.encObvView) (encOutSimForgeOut σ₂ encσ₂)
        have hkm : ComputableInPolyTime
            (fun p : ((ℕ × (Query Fn × σ₁) × Option ObvView) × ObvView) × (List Bool × σ₂) =>
              p.1.1.1) EM encUnary := by fun_prop
        have hst₂ : ComputableInPolyTime
            (fun p : ((ℕ × (Query Fn × σ₁) × Option ObvView) × ObvView) × (List Bool × σ₂) =>
              p.2.2) EM encσ₂ := by fun_prop
        have hY' : ComputableInPolyTime
            (fun p : ((ℕ × (Query Fn × σ₁) × Option ObvView) × ObvView) × (List Bool × σ₂) =>
              p.2.1) EM encBits := by fun_prop
        have hvm : ComputableInPolyTime
            (fun p : ((ℕ × (Query Fn × σ₁) × Option ObvView) × ObvView) × (List Bool × σ₂) =>
              p.1.2) EM OutSim.encObvView := by fun_prop
        have hvfn := OutSim.encObvView_fn_polyTime hvm
        have hvin := OutSim.encObvView_input_polyTime hvm
        have hqm : ComputableInPolyTime
            (fun p : ((ℕ × (Query Fn × σ₁) × Option ObvView) × ObvView) × (List Bool × σ₂) =>
              p.1.1.2.1.1) EM (encQuery Fn encFn) := by fun_prop
        have hqfn := encQuery_fn_polyTime Fn encFn hqm
        have hqin := encQuery_input_polyTime Fn encFn hqm
        have heval_m := heval.comp (hvfn.prod hvin)
        have hev_m := hev.comp (hqfn.prod hqin)
        have hout : ComputableInPolyTime
            (fun p : ((ℕ × (Query Fn × σ₁) × Option ObvView) × ObvView) × (List Bool × σ₂) =>
              if p.2.1 == G.evalGarbled p.1.2.fn p.1.2.input
              then some (G.ev p.1.1.2.1.1.fn p.1.1.2.1.1.input) else none)
            EM (encOption encBits) := by
          convert (ComputableInPolyTime.decide_eq' hY' heval_m).ite
            ((ComputableInPolyTime.optionSome encBits).comp hev_m) (.const none) using 1
          funext p
          simp [beq_iff_eq]
        exact hA.guess.preprocess (hkm.prod (hst₂.prod hout))
      exact hforge.bind_with hcont
    have hmview : ComputableInPolyTime
        (fun p : ℕ × (Query Fn × σ₁) × Option ObvView => p.2.2) EI
        (encOption OutSim.encObvView) := by fun_prop
    have hview_get : IsPPTOn EI encBool
        (fun a => do
          let view := a.2.2.getD ⟨[], []⟩
          let (Y', st₂) ← (A a.1).forge a.2.1.2 view
          let out := if Y' == G.evalGarbled view.fn view.input
            then some (G.ev a.2.1.1.fn a.2.1.1.input) else none
          (A a.1).guess st₂ out) :=
      hsome.preprocess
        ((ComputableInPolyTime.id').prod
          ((ComputableInPolyTime.optionGetD OutSim.encObvView).comp
            (hmview.prod (.const (⟨[], []⟩ : ObvView)))))
    have hcond : ComputableInPolyTime
        (fun p : ℕ × (Query Fn × σ₁) × Option ObvView => decide (p.2.2.isSome = true))
        EI encBool :=
      ComputableInPolyTime.optionIsSome hmview
    have hite := IsPPTOn.ite hcond hview_get hnone
    convert hite using 1
    funext ⟨k, ⟨q, st₁⟩, mv⟩
    cases mv <;> rfl

/-- Fixed-`k` **hybrid bound (`ObvSim ∧ Aut → OutSim`)**: for any correct garbling scheme, the
`out.sim` advantage of `A` against `S` is at most the `aut` advantage of `outSimToAut A` plus the
`obv.sim` advantage of `outSimToObvSim G A` against `S`. -/
theorem outSimAdvantage_le_autAdvantage_add_obvSimAdvantage {G : Scheme Fn}
    (hcor : G.Correct) (Φ : SideInfo Fn Λ) {k : ℕ} (hk : 0 < k) (S : ObvSimulator Λ)
    (A : OutSimAdversary Fn σ₁ σ₂) :
    outSimAdvantage G Φ k S A ≤
      autAdvantage G k (outSimToAut A) + obvSimAdvantage G Φ k S (outSimToObvSim G A) := by
  let hybrid : Experiment := do
    let (q, st₁) ← A.choose ()
    if q.input.length = G.inLen q.fn then
      let g ← G.garble k q.fn
      let X := G.encode g.encInfo q.input
      let (Y', st₂) ← A.forge st₁ ⟨g.fn, X⟩
      let out := if Y' == G.evalGarbled g.fn X then some (G.ev q.fn q.input) else none
      A.guess st₂ out
    else
      return false
  have hreal : Game.advantage (ProbComp.eval hybrid)
      (ProbComp.eval (outSimExperiment G Φ k S A true)) ≤ autAdvantage G k (outSimToAut A) := by
    have heq_real : ProbComp.eval (outSimExperiment G Φ k S A true) =
        (ProbComp.eval (A.choose ())).bind fun (q, st₁) =>
          if q.input.length = G.inLen q.fn then
            (ProbComp.eval (G.garble k q.fn)).bind fun g =>
              (ProbComp.eval (A.forge st₁ ⟨g.fn, G.encode g.encInfo q.input⟩)).bind fun (Y', st₂) =>
                ProbComp.eval (A.guess st₂ (G.decode g.decInfo Y'))
          else PMF.pure false := by
      simp only [outSimExperiment, ProbComp.eval_bind]
      refine PMF.bind_congr_on_support _ _ _ fun ⟨q, st₁⟩ _ => ?_
      by_cases hlen : q.input.length = G.inLen q.fn <;>
        simp [hlen, ProbComp.eval_bind, ProbComp.eval_pure]
    have heq_hyb : ProbComp.eval hybrid =
        (ProbComp.eval (A.choose ())).bind fun (q, st₁) =>
          if q.input.length = G.inLen q.fn then
            (ProbComp.eval (G.garble k q.fn)).bind fun g =>
              (ProbComp.eval (A.forge st₁ ⟨g.fn, G.encode g.encInfo q.input⟩)).bind fun (Y', st₂) =>
                ProbComp.eval (A.guess st₂
                  (if Y' == G.evalGarbled g.fn (G.encode g.encInfo q.input)
                    then some (G.ev q.fn q.input) else none))
          else PMF.pure false := by
      simp only [hybrid, ProbComp.eval_bind]
      refine PMF.bind_congr_on_support _ _ _ fun ⟨q, st₁⟩ _ => ?_
      by_cases hlen : q.input.length = G.inLen q.fn <;>
        simp [hlen, ProbComp.eval_bind, ProbComp.eval_pure]
    have heq_aut : ProbComp.eval (autExperiment G k (outSimToAut A)) =
        (ProbComp.eval (A.choose ())).bind fun (q, st₁) =>
          if q.input.length = G.inLen q.fn then
            (ProbComp.eval (G.garble k q.fn)).bind fun g =>
              (ProbComp.eval (A.forge st₁ ⟨g.fn, G.encode g.encInfo q.input⟩)).bind fun (Y', _) =>
                PMF.pure ((Y' != G.evalGarbled g.fn (G.encode g.encInfo q.input)) &&
                  (G.decode g.decInfo Y').isSome)
          else PMF.pure false := by
      simp only [autExperiment, outSimToAut, ProbComp.eval_bind]
      refine PMF.bind_congr_on_support _ _ _ fun ⟨q, st₁⟩ _ => ?_
      by_cases hlen : q.input.length = G.inLen q.fn <;>
        simp [hlen, ProbComp.eval_bind, ProbComp.eval_pure, PMF.map, Function.comp_def]
    rw [heq_real, heq_hyb, autAdvantage, Experiment.succProbability, heq_aut]
    refine Game.advantage_bind_le_succProbability_bind _ _ _ _ fun ⟨q, st₁⟩ => ?_
    by_cases hlen : q.input.length = G.inLen q.fn
    · simp only [hlen, ↓reduceIte]
      have hsub : ∀ (g : Scheme.Garbled), g ∈ (ProbComp.eval (G.garble k q.fn)).support →
          let μf := ProbComp.eval (A.forge st₁ ⟨g.fn, G.encode g.encInfo q.input⟩)
          let g1 : List Bool × σ₂ → Game := fun p => ProbComp.eval (A.guess p.2
            (if p.1 == G.evalGarbled g.fn (G.encode g.encInfo q.input)
              then some (G.ev q.fn q.input) else none))
          let g2 : List Bool × σ₂ → Game :=
            fun p => ProbComp.eval (A.guess p.2 (G.decode g.decInfo p.1))
          let err : List Bool × σ₂ → Game := fun p => PMF.pure
            ((p.1 != G.evalGarbled g.fn (G.encode g.encInfo q.input)) &&
              (G.decode g.decInfo p.1).isSome)
          (μf.bind g1) true ≤ (μf.bind g2) true + (μf.bind err) true ∧
          (μf.bind g2) true ≤ (μf.bind g1) true + (μf.bind err) true := by
        intro g hg
        exact Game.bind_apply_le_add_bind_apply _ _ _ _ true fun ⟨Y', st₂⟩ => by
          by_cases hev : Y' = G.evalGarbled g.fn (G.encode g.encInfo q.input)
          · have hdec : G.decode g.decInfo Y' = some (G.ev q.fn q.input) := by
              rw [hev]
              exact hcor k hk q.fn q.input hlen g hg
            rw [← hev, hdec]
            simp [hev]
          · by_cases hsome : (G.decode g.decInfo Y').isSome = true
            · have hne_b : (Y' == G.evalGarbled g.fn (G.encode g.encInfo q.input)) = false :=
                beq_false_of_ne hev
              have hbne : (Y' != G.evalGarbled g.fn (G.encode g.encInfo q.input)) = true :=
                bne_iff_ne.mpr hev
              simp only [hne_b, Bool.false_eq_true, ↓reduceIte, hbne, hsome, Bool.true_and,
                PMF.pure_apply]
              exact ⟨(PMF.coe_le_one _ _).trans (le_add_of_nonneg_left zero_le),
                (PMF.coe_le_one _ _).trans (le_add_of_nonneg_left zero_le)⟩
            · have hnone : G.decode g.decInfo Y' = none :=
                Option.not_isSome_iff_eq_none.mp (by simpa using hsome)
              simp [hev, hnone]
      exact ⟨Probability.PMF.bind_apply_le_add_on_support _ true (fun g hg => (hsub g hg).1),
        Probability.PMF.bind_apply_le_add_on_support _ true (fun g hg => (hsub g hg).2)⟩
    · simp [hlen]
  have hid : Game.advantage (ProbComp.eval (outSimExperiment G Φ k S A false))
      (ProbComp.eval hybrid) = obvSimAdvantage G Φ k S (outSimToObvSim G A) := by
    have hfalse : ProbComp.eval (outSimExperiment G Φ k S A false) =
        (ProbComp.eval (A.choose ())).bind fun (q, st₁) =>
          if q.input.length = G.inLen q.fn then
            (ProbComp.eval (S (Φ.phi q.fn))).bind fun view =>
              (ProbComp.eval (A.forge st₁ view)).bind fun (Y', st₂) =>
                ProbComp.eval (A.guess st₂
                  (if Y' == G.evalGarbled view.fn view.input then some (G.ev q.fn q.input)
                    else none))
          else PMF.pure false := by
      simp only [outSimExperiment, ProbComp.eval_bind]
      refine PMF.bind_congr_on_support _ _ _ fun ⟨q, st₁⟩ _ => ?_
      by_cases hlen : q.input.length = G.inLen q.fn <;>
        simp [hlen, ProbComp.eval_bind, ProbComp.eval_pure]
    have hhyb : ProbComp.eval hybrid =
        (ProbComp.eval (A.choose ())).bind fun (q, st₁) =>
          if q.input.length = G.inLen q.fn then
            (ProbComp.eval (G.obvView k q)).bind fun view =>
              (ProbComp.eval (A.forge st₁ view)).bind fun (Y', st₂) =>
                ProbComp.eval (A.guess st₂
                  (if Y' == G.evalGarbled view.fn view.input then some (G.ev q.fn q.input)
                    else none))
          else PMF.pure false := by
      simp only [hybrid, ProbComp.eval_bind]
      refine PMF.bind_congr_on_support _ _ _ fun ⟨q, st₁⟩ _ => ?_
      by_cases hlen : q.input.length = G.inLen q.fn <;>
        simp [hlen, Scheme.obvView, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
          PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind]
    have hobv_f : ProbComp.eval (obvSimExperiment G Φ k S (outSimToObvSim G A) false) =
        (ProbComp.eval (A.choose ())).bind fun (q, st₁) =>
          if q.input.length = G.inLen q.fn then
            (ProbComp.eval (S (Φ.phi q.fn))).bind fun view =>
              (ProbComp.eval (A.forge st₁ view)).bind fun (Y', st₂) =>
                ProbComp.eval (A.guess st₂
                  (if Y' == G.evalGarbled view.fn view.input then some (G.ev q.fn q.input)
                    else none))
          else PMF.pure false := by
      simp only [obvSimExperiment, outSimToObvSim, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.bind_bind, PMF.pure_bind]
      refine PMF.bind_congr_on_support _ _ _ fun ⟨q, st₁⟩ _ => ?_
      by_cases hlen : q.input.length = G.inLen q.fn <;>
        simp [hlen, ProbComp.eval_bind, ProbComp.eval_pure]
    have hobv_t : ProbComp.eval (obvSimExperiment G Φ k S (outSimToObvSim G A) true) =
        (ProbComp.eval (A.choose ())).bind fun (q, st₁) =>
          if q.input.length = G.inLen q.fn then
            (ProbComp.eval (G.obvView k q)).bind fun view =>
              (ProbComp.eval (A.forge st₁ view)).bind fun (Y', st₂) =>
                ProbComp.eval (A.guess st₂
                  (if Y' == G.evalGarbled view.fn view.input then some (G.ev q.fn q.input)
                    else none))
          else PMF.pure false := by
      simp only [obvSimExperiment, outSimToObvSim, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.bind_bind, PMF.pure_bind]
      refine PMF.bind_congr_on_support _ _ _ fun ⟨q, st₁⟩ _ => ?_
      by_cases hlen : q.input.length = G.inLen q.fn <;>
        simp [hlen, ProbComp.eval_bind, ProbComp.eval_pure]
    rw [hfalse, hhyb, obvSimAdvantage, Experiment.advantage, hobv_f, hobv_t]
  exact (Game.advantage_triangle _ (ProbComp.eval hybrid) _).trans
    (by rw [add_comm (autAdvantage G k (outSimToAut A))]; exact add_le_add hid.le hreal)

/-! ## Asymptotic relations: `OutSim` vs `ObvSim`, `Aut`, and `PrvSim` -/

/-- `Scheme.OutSimSecure` implies asymptotic `obv.sim` security against every uniform strict PPT
`ObvSimAdversary`. -/
theorem Scheme.OutSimSecure.obvSim {G : Scheme Fn} {Φ : SideInfo Fn Λ} {encFn : Fn ↪ List Bool}
    {encΛ : Λ ↪ List Bool} (h : G.OutSimSecure Φ encFn encΛ) {σ : Type} {encσ : σ ↪ List Bool}
    {B : ℕ → ObvSimAdversary Fn σ}
    (hB : TwoStage.IsPPT encUnit (encQuery Fn encFn) (encOption OutSim.encObvView) encBool encσ B) :
    ∃ S : ℕ → ObvSimulator Λ,
      IsPPTOn (encObvSimIn Λ encΛ) OutSim.encObvView (fun (k, φ) => S k φ) ∧
      Negligible fun k => obvSimAdvantage G Φ k (S k) (B k) := by
  obtain ⟨S, hS, hneg⟩ := h _ _ encσ (encObvOutState σ encσ) (fun k => obvSimToOutSim (B k))
    (isPPT_obvSimToOutSim hB)
  refine ⟨S, hS, ?_⟩
  simpa only [obvSimAdvantage_eq_outSimAdvantage] using hneg

/-- `Scheme.OutSimSecureUniversal` implies universal-simulator asymptotic `obv.sim` security. -/
theorem Scheme.OutSimSecureUniversal.obvSim {G : Scheme Fn} {Φ : SideInfo Fn Λ}
    {encFn : Fn ↪ List Bool} {encΛ : Λ ↪ List Bool}
    (h : G.OutSimSecureUniversal Φ encFn encΛ) :
    ∃ S : ℕ → ObvSimulator Λ,
      IsPPTOn (encObvSimIn Λ encΛ) OutSim.encObvView (fun (k, φ) => S k φ) ∧
      ∀ (σ : Type) (encσ : σ ↪ List Bool) (B : ℕ → ObvSimAdversary Fn σ),
        TwoStage.IsPPT encUnit (encQuery Fn encFn) (encOption OutSim.encObvView) encBool encσ B →
          Negligible fun k => obvSimAdvantage G Φ k (S k) (B k) := by
  obtain ⟨S, hS, hneg⟩ := h
  refine ⟨S, hS, fun σ encσ B hB => ?_⟩
  simpa only [obvSimAdvantage_eq_outSimAdvantage] using
    hneg _ _ encσ (encObvOutState σ encσ) (fun k => obvSimToOutSim (B k))
      (isPPT_obvSimToOutSim hB)

/-- `Scheme.OutSimSecure` implies asymptotic authenticity (`aut`) for any efficient scheme. -/
theorem Scheme.OutSimSecure.aut {G : Scheme Fn} {Φ : SideInfo Fn Λ} {encFn : Fn ↪ List Bool}
    {encΛ : Λ ↪ List Bool} (heff : G.IsEfficient encFn) (h : G.OutSimSecure Φ encFn encΛ)
    {σ : Type} {encσ : σ ↪ List Bool} {A : ℕ → AutAdversary Fn σ}
    (hA : TwoStage.IsPPT encUnit (encQuery Fn encFn) OutSim.encObvView encBits encσ A) :
    Negligible fun k => autAdvantage G k (A k) := by
  obtain ⟨S, _, hneg⟩ := h _ _ encσ encAutOutState (fun k => autToOutSim G (A k))
    (isPPT_autToOutSim G heff.evalGarbled hA)
  exact hneg.congr fun k => (autAdvantage_eq_outSimAdvantage G Φ k (S k) (A k)).symm

/-- Converse (`ObvSim ∧ Aut → OutSim`): an efficient, correct garbling scheme that satisfies
asymptotic `obv.sim` and `aut` is `Scheme.OutSimSecure`. -/
theorem outSimSecure_of_obvSim_and_aut {G : Scheme Fn} {Φ : SideInfo Fn Λ}
    {encFn : Fn ↪ List Bool} {encΛ : Λ ↪ List Bool}
    (hcor : G.Correct) (heff : G.IsEfficient encFn)
    (hobv : ∀ (σ : Type) (encσ : σ ↪ List Bool) (B : ℕ → ObvSimAdversary Fn σ),
      TwoStage.IsPPT encUnit (encQuery Fn encFn) (encOption OutSim.encObvView) encBool encσ B →
        ∃ S : ℕ → ObvSimulator Λ,
          IsPPTOn (encObvSimIn Λ encΛ) OutSim.encObvView (fun (k, φ) => S k φ) ∧
          Negligible fun k => obvSimAdvantage G Φ k (S k) (B k))
    (haut : ∀ (σ : Type) (encσ : σ ↪ List Bool) (A : ℕ → AutAdversary Fn σ),
      TwoStage.IsPPT encUnit (encQuery Fn encFn) OutSim.encObvView encBits encσ A →
        Negligible fun k => autAdvantage G k (A k)) :
    G.OutSimSecure Φ encFn encΛ := by
  intro σ₁ σ₂ encσ₁ encσ₂ A hA
  obtain ⟨S, hS, hobvNeg⟩ := hobv _ (encOutSimObvState Fn σ₁ encFn encσ₁)
    (fun k => outSimToObvSim G (A k)) (isPPT_outSimToObvSim G heff.evalGarbled heff.ev hA)
  have hautNeg := haut _ encσ₁ (fun k => outSimToAut (A k)) (isPPT_outSimToAut hA)
  refine ⟨S, hS, negligible_of_eventually_le (hautNeg.add_fun hobvNeg) ?_⟩
  filter_upwards [Filter.eventually_gt_atTop 0] with k hk
  exact outSimAdvantage_le_autAdvantage_add_obvSimAdvantage hcor Φ hk (S k) (A k)

/-- Universal-simulator converse (`ObvSimUniversal ∧ Aut → OutSimSecureUniversal`). -/
theorem outSimSecureUniversal_of_obvSim_and_aut {G : Scheme Fn} {Φ : SideInfo Fn Λ}
    {encFn : Fn ↪ List Bool} {encΛ : Λ ↪ List Bool}
    (hcor : G.Correct) (heff : G.IsEfficient encFn)
    (hobv : ∃ S : ℕ → ObvSimulator Λ,
      IsPPTOn (encObvSimIn Λ encΛ) OutSim.encObvView (fun (k, φ) => S k φ) ∧
      ∀ (σ : Type) (encσ : σ ↪ List Bool) (B : ℕ → ObvSimAdversary Fn σ),
        TwoStage.IsPPT encUnit (encQuery Fn encFn) (encOption OutSim.encObvView) encBool encσ B →
          Negligible fun k => obvSimAdvantage G Φ k (S k) (B k))
    (haut : ∀ (σ : Type) (encσ : σ ↪ List Bool) (A : ℕ → AutAdversary Fn σ),
      TwoStage.IsPPT encUnit (encQuery Fn encFn) OutSim.encObvView encBits encσ A →
        Negligible fun k => autAdvantage G k (A k)) :
    G.OutSimSecureUniversal Φ encFn encΛ := by
  obtain ⟨S, hS, hobvNeg⟩ := hobv
  refine ⟨S, hS, fun σ₁ σ₂ encσ₁ encσ₂ A hA => ?_⟩
  have h1 := hobvNeg _ (encOutSimObvState Fn σ₁ encFn encσ₁)
    (fun k => outSimToObvSim G (A k)) (isPPT_outSimToObvSim G heff.evalGarbled heff.ev hA)
  have h2 := haut _ encσ₁ (fun k => outSimToAut (A k)) (isPPT_outSimToAut hA)
  refine negligible_of_eventually_le (h2.add_fun h1) ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with k hk
  exact outSimAdvantage_le_autAdvantage_add_obvSimAdvantage hcor Φ hk (S k) (A k)

/-! ## Connecting privacy (`PrvSim`) via decoding-information simulation -/

/-- A decoding-information simulator `SimDec(φ, (F, X), y)` that samples a simulated `decInfo`
word from the side information `φ = Φ(f)`, the oblivious view `(F, X)`, and the output `y`. -/
abbrev DecSimulator (Λ : Type) := Λ → ObvView → List Bool → ProbComp (List Bool)

/-- Experiment `b` of the decoding-information simulation game: `b = true` hands the `prv.sim`
adversary the real view `(F, X, d)` via `G.prvView`, and `b = false` samples `(F, X)` from
`G.obvView` and synthesizes `d` from `SimDec (Φ.phi q.fn) ⟨F, X⟩ (G.ev q.fn q.input)`. -/
noncomputable def decSimExperiment (G : Scheme Fn) (Φ : SideInfo Fn Λ) (k : ℕ)
    (SimDec : DecSimulator Λ) (B : PrvSimAdversary Fn σ) (b : Bool) : Experiment := do
  let (q, st) ← B.choose ()
  if q.input.length = G.inLen q.fn then
    if b then
      let view ← G.prvView k q
      B.guess st (some view)
    else
      let view ← G.obvView k q
      let d ← SimDec (Φ.phi q.fn) view (G.ev q.fn q.input)
      B.guess st (some ⟨view.fn, view.input, d⟩)
  else
    B.guess st none

/-- The decoding-information simulation advantage of `B` against `SimDec`. -/
noncomputable def decSimAdvantage (G : Scheme Fn) (Φ : SideInfo Fn Λ) (k : ℕ)
    (SimDec : DecSimulator Λ) (B : PrvSimAdversary Fn σ) : ℝ≥0 :=
  Experiment.advantage (decSimExperiment G Φ k SimDec B false)
    (decSimExperiment G Φ k SimDec B true)

/-- Compose an obliviousness simulator `S_obv` and a decoding-information simulator `SimDec`
into a full `prv.sim` simulator `S_prv(y, φ)`. -/
noncomputable def prvSimulatorOfObvDec (S_obv : ObvSimulator Λ) (SimDec : DecSimulator Λ) :
    PrvSimulator Λ :=
  fun y φ => do
    let view ← S_obv φ
    let d ← SimDec φ view y
    pure ⟨view.fn, view.input, d⟩

/-- Reduce a `prv.sim` adversary `B` to an `obv.sim` adversary using `SimDec` to synthesize `d` from
the received oblivious view `(F, X)` and `G.ev q.fn q.input`. -/
noncomputable def prvSimToObvSim (G : Scheme Fn) (Φ : SideInfo Fn Λ) (SimDec : DecSimulator Λ)
    (B : PrvSimAdversary Fn σ) : ObvSimAdversary Fn (Query Fn × σ) where
  choose _ := do
    let (q, st) ← B.choose ()
    pure (q, (q, st))
  guess s mview :=
    match mview with
    | none => B.guess s.2 none
    | some view => do
      let d ← SimDec (Φ.phi s.1.fn) view (G.ev s.1.fn s.1.input)
      B.guess s.2 (some ⟨view.fn, view.input, d⟩)

/-- `prvSimulatorOfObvDec` is uniform strict PPT whenever `S_obv` and `SimDec` are. -/
theorem isPPTOn_prvSimulatorOfObvDec {encΛ : Λ ↪ List Bool}
    {S_obv : ℕ → ObvSimulator Λ} {SimDec : ℕ → DecSimulator Λ}
    (hS : IsPPTOn (encObvSimIn Λ encΛ) OutSim.encObvView (fun (k, φ) => S_obv k φ))
    (hDec : IsPPTOn (encDecSimIn Λ encΛ) encBits
      (fun (k, φ, view, y) => SimDec k φ view y)) :
    IsPPTOn (encPrvSimIn Λ encΛ) encPrvView
      (fun (k, y, φ) => prvSimulatorOfObvDec (S_obv k) (SimDec k) y φ) := by
  let EI := encPrvSimIn Λ encΛ
  have hk : ComputableInPolyTime (fun p : ℕ × List Bool × Λ => p.1) EI encUnary := by fun_prop
  have hφ : ComputableInPolyTime (fun p : ℕ × List Bool × Λ => p.2.2) EI encΛ := by fun_prop
  have hsobv := hS.preprocess (hk.prod hφ)
  have hcont : IsPPTOn (encPair EI OutSim.encObvView) encPrvView
      (fun (a, view) => do
        let d ← SimDec a.1 a.2.2 view a.2.1
        pure ⟨view.fn, view.input, d⟩) := by
    let EM := encPair EI OutSim.encObvView
    have hkm : ComputableInPolyTime (fun p : (ℕ × List Bool × Λ) × ObvView => p.1.1) EM
        encUnary := by fun_prop
    have hφm : ComputableInPolyTime (fun p : (ℕ × List Bool × Λ) × ObvView => p.1.2.2) EM
        encΛ := by fun_prop
    have hvm : ComputableInPolyTime (fun p : (ℕ × List Bool × Λ) × ObvView => p.2) EM
        OutSim.encObvView := by fun_prop
    have hym : ComputableInPolyTime (fun p : (ℕ × List Bool × Λ) × ObvView => p.1.2.1) EM
        encBits := by fun_prop
    have hdec := hDec.preprocess (hkm.prod (hφm.prod (hvm.prod hym)))
    have hret : IsPPTOn (encPair EM encBits) encPrvView
        (fun (x, d) => pure ⟨x.2.fn, x.2.input, d⟩) := by
      refine ComputableInPolyTime.isPPTOn ?_
      have hx : ComputableInPolyTime
          (fun p : ((ℕ × List Bool × Λ) × ObvView) × List Bool => p.1.2)
          (encPair EM encBits) OutSim.encObvView := by fun_prop
      have hd : ComputableInPolyTime
          (fun p : ((ℕ × List Bool × Λ) × ObvView) × List Bool => p.2)
          (encPair EM encBits) encBits := by fun_prop
      have hfn := OutSim.encObvView_fn_polyTime hx
      have hin := OutSim.encObvView_input_polyTime hx
      exact (hfn.prod (hin.prod hd)).of_enc_eq fun _ => rfl
    exact hdec.bind_with hret
  exact hsobv.bind_with hcont

/-- `prvSimToObvSim` is uniform strict PPT whenever `B`, `SimDec`, `Φ.phi`, and `G.ev` are. -/
theorem isPPT_prvSimToObvSim (G : Scheme Fn) (Φ : SideInfo Fn Λ) {encFn : Fn ↪ List Bool}
    {encΛ : Λ ↪ List Bool} {encσ : σ ↪ List Bool}
    (hphi : ComputableInPolyTime Φ.phi encFn encΛ)
    (hev : ComputableInPolyTime (fun (f, x) => G.ev f x) (encPair encFn encBits) encBits)
    {SimDec : ℕ → DecSimulator Λ}
    (hDec : IsPPTOn (encDecSimIn Λ encΛ) encBits
      (fun (k, φ, view, y) => SimDec k φ view y))
    {B : ℕ → PrvSimAdversary Fn σ}
    (hB : TwoStage.IsPPT encUnit (encQuery Fn encFn) (encOption encPrvView) encBool encσ B) :
    TwoStage.IsPPT encUnit (encQuery Fn encFn) (encOption OutSim.encObvView) encBool
      (encPrvObvState Fn σ encFn encσ) (fun k => prvSimToObvSim G Φ (SimDec k) (B k)) where
  choose := by
    have hpost : IsPPTOn (encPair encUnaryUnit (encOutSimChooseOut Fn σ encFn encσ))
        (encPair (encQuery Fn encFn) (encPrvObvState Fn σ encFn encσ))
        (fun (_, p) => pure (p.1, p)) := by
      refine ComputableInPolyTime.isPPTOn ?_
      have hp : ComputableInPolyTime (fun x : (ℕ × Unit) × (Query Fn × σ) => x.2)
          (encPair encUnaryUnit (encOutSimChooseOut Fn σ encFn encσ))
          (encOutSimChooseOut Fn σ encFn encσ) := by fun_prop
      exact ((ComputableInPolyTime.fst (encQuery Fn encFn) encσ).comp hp).prod hp
    exact hB.choose.bind_with hpost
  guess := by
    let EI := encPair encUnary (encPair (encPrvObvState Fn σ encFn encσ)
      (encOption OutSim.encObvView))
    have hnone : IsPPTOn EI encBool (fun a => (B a.1).guess a.2.1.2 none) := by
      have hk : ComputableInPolyTime (fun p : ℕ × (Query Fn × σ) × Option ObvView => p.1) EI
          encUnary := by fun_prop
      have hst : ComputableInPolyTime (fun p : ℕ × (Query Fn × σ) × Option ObvView => p.2.1.2) EI
          encσ := by fun_prop
      exact hB.guess.preprocess (hk.prod (hst.prod (.const none)))
    have hsome : IsPPTOn (encPair EI OutSim.encObvView) encBool
        (fun (a, view) => do
          let d ← SimDec a.1 (Φ.phi a.2.1.1.fn) view (G.ev a.2.1.1.fn a.2.1.1.input)
          (B a.1).guess a.2.1.2 (some ⟨view.fn, view.input, d⟩)) := by
      let EM := encPair EI OutSim.encObvView
      have hkm : ComputableInPolyTime
          (fun p : (ℕ × (Query Fn × σ) × Option ObvView) × ObvView => p.1.1) EM encUnary := by
        fun_prop
      have hqm : ComputableInPolyTime
          (fun p : (ℕ × (Query Fn × σ) × Option ObvView) × ObvView => p.1.2.1.1) EM
          (encQuery Fn encFn) := by fun_prop
      have hqfn := encQuery_fn_polyTime Fn encFn hqm
      have hqin := encQuery_input_polyTime Fn encFn hqm
      have hvm : ComputableInPolyTime
          (fun p : (ℕ × (Query Fn × σ) × Option ObvView) × ObvView => p.2) EM
          OutSim.encObvView := by fun_prop
      have hdec := hDec.preprocess
        (hkm.prod ((hphi.comp hqfn).prod (hvm.prod (hev.comp (hqfn.prod hqin)))))
      have hret : IsPPTOn (encPair EM encBits) encBool
          (fun (x, d) => (B x.1.1).guess x.1.2.1.2 (some ⟨x.2.fn, x.2.input, d⟩)) := by
        let ER := encPair EM encBits
        have hkr : ComputableInPolyTime
            (fun p : ((ℕ × (Query Fn × σ) × Option ObvView) × ObvView) × List Bool => p.1.1.1) ER
            encUnary := by fun_prop
        have hstr : ComputableInPolyTime
            (fun p : ((ℕ × (Query Fn × σ) × Option ObvView) × ObvView) × List Bool =>
              p.1.1.2.1.2) ER encσ := by fun_prop
        have hvr : ComputableInPolyTime
            (fun p : ((ℕ × (Query Fn × σ) × Option ObvView) × ObvView) × List Bool => p.1.2) ER
            OutSim.encObvView := by fun_prop
        have hdr : ComputableInPolyTime
            (fun p : ((ℕ × (Query Fn × σ) × Option ObvView) × ObvView) × List Bool => p.2) ER
            encBits := by fun_prop
        have hfn := OutSim.encObvView_fn_polyTime hvr
        have hin := OutSim.encObvView_input_polyTime hvr
        have hprv : ComputableInPolyTime
            (fun p : ((ℕ × (Query Fn × σ) × Option ObvView) × ObvView) × List Bool =>
              some (⟨p.1.2.fn, p.1.2.input, p.2⟩ : PrvView)) ER (encOption encPrvView) :=
          (ComputableInPolyTime.optionSome encPrvView).comp
            ((hfn.prod (hin.prod hdr)).of_enc_eq fun _ => rfl)
        exact hB.guess.preprocess (hkr.prod (hstr.prod hprv))
      exact hdec.bind_with hret
    have hmview : ComputableInPolyTime
        (fun p : ℕ × (Query Fn × σ) × Option ObvView => p.2.2) EI
        (encOption OutSim.encObvView) := by fun_prop
    have hview_get : IsPPTOn EI encBool
        (fun a => do
          let view := a.2.2.getD ⟨[], []⟩
          let d ← SimDec a.1 (Φ.phi a.2.1.1.fn) view (G.ev a.2.1.1.fn a.2.1.1.input)
          (B a.1).guess a.2.1.2 (some ⟨view.fn, view.input, d⟩)) :=
      hsome.preprocess
        ((ComputableInPolyTime.id').prod
          ((ComputableInPolyTime.optionGetD OutSim.encObvView).comp
            (hmview.prod (.const (⟨[], []⟩ : ObvView)))))
    have hcond : ComputableInPolyTime
        (fun p : ℕ × (Query Fn × σ) × Option ObvView => decide (p.2.2.isSome = true))
        EI encBool :=
      ComputableInPolyTime.optionIsSome hmview
    have hite := IsPPTOn.ite hcond hview_get hnone
    convert hite using 1
    funext ⟨k, ⟨q, st⟩, mv⟩
    cases mv <;> rfl

/-- Fixed-`k` **triangle bound (`ObvSim ∧ DecSim → PrvSim`)**: against `prvSimulatorOfObvDec
S_obv SimDec`, the `prv.sim` advantage of `B` is at most the decoding-simulation advantage of `B`
plus the `obv.sim` advantage of `prvSimToObvSim G Φ SimDec B`. -/
theorem prvSimAdvantage_le_decSimAdvantage_add_obvSimAdvantage (G : Scheme Fn)
    (Φ : SideInfo Fn Λ) (k : ℕ) (S_obv : ObvSimulator Λ) (SimDec : DecSimulator Λ)
    (B : PrvSimAdversary Fn σ) :
    prvSimAdvantage G Φ k (prvSimulatorOfObvDec S_obv SimDec) B ≤
      decSimAdvantage G Φ k SimDec B +
        obvSimAdvantage G Φ k S_obv (prvSimToObvSim G Φ SimDec B) := by
  have hreal : ProbComp.eval (prvSimExperiment G Φ k (prvSimulatorOfObvDec S_obv SimDec) B true) =
      ProbComp.eval (decSimExperiment G Φ k SimDec B true) := by
    simp [prvSimExperiment, decSimExperiment]
  have hmid : ProbComp.eval (decSimExperiment G Φ k SimDec B false) =
      ProbComp.eval (obvSimExperiment G Φ k S_obv (prvSimToObvSim G Φ SimDec B) true) := by
    simp [decSimExperiment, obvSimExperiment, prvSimToObvSim, ProbComp.eval_bind]
  have hideal : ProbComp.eval (prvSimExperiment G Φ k (prvSimulatorOfObvDec S_obv SimDec) B false) =
      ProbComp.eval (obvSimExperiment G Φ k S_obv (prvSimToObvSim G Φ SimDec B) false) := by
    simp only [prvSimExperiment, prvSimulatorOfObvDec, obvSimExperiment, prvSimToObvSim,
      ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
    refine PMF.bind_congr_on_support _ _ _ fun ⟨q, st⟩ _ => ?_
    by_cases hlen : q.input.length = G.inLen q.fn <;> simp [hlen]
  rw [prvSimAdvantage, Experiment.advantage, hreal, hideal]
  refine (Game.advantage_triangle _
    (ProbComp.eval (decSimExperiment G Φ k SimDec B false)) _).trans ?_
  rw [add_comm]
  refine add_le_add ?_ ?_
  · rfl
  · rw [hmid]
    rfl

/-- Asymptotic **privacy from obliviousness and decoding simulation**: if `G` is `obv.sim`
secure and admits a uniform strict PPT decoding-information simulator `SimDec`, then `G` is
`Scheme.PrvSimSecure`. -/
theorem prvSimSecure_of_obvSim_and_decSim {G : Scheme Fn} {Φ : SideInfo Fn Λ}
    {encFn : Fn ↪ List Bool} {encΛ : Λ ↪ List Bool}
    (hphi : ComputableInPolyTime Φ.phi encFn encΛ)
    (hev : ComputableInPolyTime (fun (f, x) => G.ev f x) (encPair encFn encBits) encBits)
    (hobv : ∀ (σ : Type) (encσ : σ ↪ List Bool) (B : ℕ → ObvSimAdversary Fn σ),
      TwoStage.IsPPT encUnit (encQuery Fn encFn) (encOption OutSim.encObvView) encBool encσ B →
        ∃ S : ℕ → ObvSimulator Λ,
          IsPPTOn (encObvSimIn Λ encΛ) OutSim.encObvView (fun (k, φ) => S k φ) ∧
          Negligible fun k => obvSimAdvantage G Φ k (S k) (B k))
    (SimDec : ℕ → DecSimulator Λ)
    (hDecPPT : IsPPTOn (encDecSimIn Λ encΛ) encBits
      (fun (k, φ, view, y) => SimDec k φ view y))
    (hDec : ∀ (σ : Type) (encσ : σ ↪ List Bool) (B : ℕ → PrvSimAdversary Fn σ),
      TwoStage.IsPPT encUnit (encQuery Fn encFn) (encOption encPrvView) encBool encσ B →
        Negligible fun k => decSimAdvantage G Φ k (SimDec k) (B k)) :
    G.PrvSimSecure Φ encFn encΛ := by
  intro σ encσ B hB
  obtain ⟨S_obv, hSobv, hobvNeg⟩ := hobv _ (encPrvObvState Fn σ encFn encσ)
    (fun k => prvSimToObvSim G Φ (SimDec k) (B k))
    (isPPT_prvSimToObvSim G Φ hphi hev hDecPPT hB)
  have hdecNeg := hDec σ encσ B hB
  refine ⟨fun k => prvSimulatorOfObvDec (S_obv k) (SimDec k),
    isPPTOn_prvSimulatorOfObvDec hSobv hDecPPT,
    negligible_of_eventually_le (hdecNeg.add_fun hobvNeg) ?_⟩
  filter_upwards with k
  exact prvSimAdvantage_le_decSimAdvantage_add_obvSimAdvantage G Φ k (S_obv k) (SimDec k) (B k)

/-- Universal-simulator privacy (`Scheme.PrvSimSecureUniversal`) from universal output
simulatability (`Scheme.OutSimSecureUniversal`) and decoding-information simulation. -/
theorem prvSimSecureUniversal_of_outSimSecureUniversal_and_decSim
    {G : Scheme Fn} {Φ : SideInfo Fn Λ}
    {encFn : Fn ↪ List Bool} {encΛ : Λ ↪ List Bool}
    (hphi : ComputableInPolyTime Φ.phi encFn encΛ)
    (hev : ComputableInPolyTime (fun (f, x) => G.ev f x) (encPair encFn encBits) encBits)
    (hout : G.OutSimSecureUniversal Φ encFn encΛ)
    (SimDec : ℕ → DecSimulator Λ)
    (hDecPPT : IsPPTOn (encDecSimIn Λ encΛ) encBits
      (fun (k, φ, view, y) => SimDec k φ view y))
    (hDec : ∀ (σ : Type) (encσ : σ ↪ List Bool) (B : ℕ → PrvSimAdversary Fn σ),
      TwoStage.IsPPT encUnit (encQuery Fn encFn) (encOption encPrvView) encBool encσ B →
        Negligible fun k => decSimAdvantage G Φ k (SimDec k) (B k)) :
    G.PrvSimSecureUniversal Φ encFn encΛ := by
  obtain ⟨S_obv, hSobv, hobvNeg⟩ := hout.obvSim
  refine ⟨fun k => prvSimulatorOfObvDec (S_obv k) (SimDec k),
    isPPTOn_prvSimulatorOfObvDec hSobv hDecPPT, fun σ encσ B hB => ?_⟩
  have h1 := hobvNeg _ (encPrvObvState Fn σ encFn encσ)
    (fun k => prvSimToObvSim G Φ (SimDec k) (B k))
    (isPPT_prvSimToObvSim G Φ hphi hev hDecPPT hB)
  have h2 := hDec σ encσ B hB
  refine negligible_of_eventually_le (h2.add_fun h1) ?_
  filter_upwards with k
  exact prvSimAdvantage_le_decSimAdvantage_add_obvSimAdvantage G Φ k (S_obv k) (SimDec k) (B k)

end Reductions

end Cslib.Crypto.Garbling
