/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
public import CslibFrontier.Computability.Probabilistic.PPT
public import CslibFrontier.Crypto.Protocols.UC.DummyAdversary
public import CslibFrontier.Crypto.Protocols.UC.WordInterface
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.SubstitutionGrowth
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.RunWith
import CslibFrontier.Languages.Probabilistic.Oracle.Support

/-!
# Strict-PPT certificates for typed UC machine families

This module defines strict polynomial-time certificates and predicates for typed UC machine
families (`Machine`, `Protocol`, `Adversary`, `Environment`, and `IdealFunctionality`) in this
library's word model, following the typed-object-plus-encoding convention of `AdversaryOf.IsPPT`
and building on `WordInterface` (`CslibFrontier.Crypto.Protocols.UC.WordInterface`).

Every definition in this file is a library construction for this word model rather than
Definition 6 of [Canetti2020]. In particular:

1. `PPTParam.replyBound` and `EnvParam.replyBound` are explicit reply-length caps passed to
   `ProbOracleComp.lowerWith` (bounding how many bits are read from each lowered imported reply),
   not the import field of [Canetti2020], Section 3.2.
2. `PPTCertificate.init` certifies `(M p.secParam p.corrupted).init` under `encPPTParam n` so it
   shares a parameter encoding with `PPTCertificate.handle`; the initialization program itself does
   not inspect `p.replyBound`.
3. `PPTCertificate` bounds only additive encoded-state growth per activation (`growth`,
   `growth_poly`, `preserve`) and omits any state-independent reply-length bound: replies may grow
   with the encoded state, bounded automatically by `PPTCertificate.handle`'s `IsOraclePPTOn`
   output-length bound and consumed by
   `IsOraclePPTOn.run_interpret_preprocess_open_of_bounded_growth` via
   `PPTCertificate.preserve_wordHandle`.
4. `Environment.IsPPT` is uniform (no nonuniform advice) and runs in time polynomial in
   `secParam + replyBound + aux.length`, admitting environments whose work grows with `replyBound`
   and `aux.length` (unlike `Environment.PolyBounded`'s `κ`-only call budget).
5. No implication is claimed between `Protocol.IsPPT` / `Adversary.IsPPT` / `Environment.IsPPT`
   and the call-budget predicates `Protocol.PolyBounded` / `Adversary.PolyBounded` /
   `Environment.PolyBounded`.

## Main definitions

* `Cslib.Crypto.Protocols.UC.PPTParam`, `Cslib.Crypto.Protocols.UC.encPPTParam`: activation
  parameters `(secParam, replyBound, corrupted)` for a UC machine family and their encoding.
* `Cslib.Crypto.Protocols.UC.EnvParam`, `Cslib.Crypto.Protocols.UC.encEnvParam`: activation
  parameters `(secParam, replyBound, aux)` for a UC environment and their encoding.
* `Cslib.Crypto.Protocols.UC.WordCodec`, `Cslib.Crypto.Protocols.UC.StateCodec`: injective binary
  state presentation with total left-inverse decoder for a UC machine or ideal functionality.
* `Cslib.Crypto.Protocols.UC.wordHandle`, `Cslib.Crypto.Protocols.UC.wordRunFrom`,
  `Cslib.Crypto.Protocols.UC.wordRun`: one word-level activation of a typed UC machine family, its
  parameterized state-passing execution from an encoded state, and the full word-level execution
  of a lowered environment against `wordHandle` from sampled initial state.
* `Cslib.Crypto.Protocols.UC.punitWordCodec`: canonical `WordCodec PUnit` encoding `PUnit.unit` as
  `[]`.
* `Cslib.Crypto.Protocols.UC.PPTCertificate`: strict-PPT certificate for a UC machine family
  (`init`, `handle`, and polynomially bounded additive state growth `preserve`).
* `Cslib.Crypto.Protocols.UC.Machine.IsPPTFamily`, `Cslib.Crypto.Protocols.UC.Protocol.IsPPT`,
  `Cslib.Crypto.Protocols.UC.Adversary.IsPPT`, `Cslib.Crypto.Protocols.UC.Environment.IsPPT`,
  `Cslib.Crypto.Protocols.UC.IdealFunctionality.wordStep`,
  `Cslib.Crypto.Protocols.UC.IdealFunctionality.PPTCertificate`,
  `Cslib.Crypto.Protocols.UC.IdealFunctionality.IsPPT`: strict-PPT predicates and shared word-step
  for UC machines, protocols, adversaries, environments, and ideal functionalities.

## Main results

* `Cslib.Crypto.Protocols.UC.PPTCertificate.preserve_wordHandle`: invariant-and-growth bridge
  from `PPTCertificate` to `IsOraclePPTOn.run_interpret_preprocess_open_of_bounded_growth`.
* `Cslib.Crypto.Protocols.UC.Environment.IsPPT.isOraclePPTOn_run_wordHandle`: running a
  strict-PPT environment against any machine family equipped with a `PPTCertificate` under
  polynomial-time parameter maps yields a uniform strict oracle-PPT program.
* `Cslib.Crypto.Protocols.UC.Machine.isPPTFamily_id`: the forwarding machine `Machine.id` is
  strict PPT over any `WordInterface`.
* `Cslib.Crypto.Protocols.UC.Adversary.isPPT_dummyAdversary`: the dummy adversary is strict PPT
  over any network `WordPort`.
* `Cslib.Crypto.Protocols.UC.IdealFunctionality.IsPPT.toProtocol`: a strict-PPT ideal
  functionality yields a strict-PPT protocol.

## References

* [R. Canetti, *Universally Composable Security*][Canetti2020], Section 3.2 (Polynomial Time ITMs
  and Parameterized Systems; Definition 6) and Section 4.3.1 (Emulation with Respect to the Dummy
  Adversary): context for UC polynomial time and the dummy adversary. The strict-PPT certificates
  here are library constructions for this word model, not Definition 6 of [Canetti2020].
-/

public section

namespace Cslib.Crypto.Protocols.UC

open Probability Turing.MultiTapeTM

/-! ### Activation parameters -/

/-- Library construction (no cited definition): activation parameters for a UC machine family in
this library's word model. Here `replyBound` is the prefix length read from each lowered imported
oracle reply (not the import field of [Canetti2020], Section 3.2). -/
structure PPTParam (n : ℕ) : Type where
  /-- The security parameter. -/
  secParam : ℕ
  /-- Prefix length read from each lowered imported oracle reply. -/
  replyBound : ℕ
  /-- The set of statically corrupted parties. -/
  corrupted : Finset (Fin n)

noncomputable section

/-- Library construction (no cited definition): binary encoding of `PPTParam n` as framed unary
`secParam`, framed unary `replyBound`, and `encFinite (Finset (Fin n))` `corrupted`. -/
enc_structure encPPTParam (n : ℕ) : PPTParam n where
  secParam : encUnary, replyBound : encUnary, corrupted : (encFinite (Finset (Fin n)))

end

/-- Library construction (no cited definition): activation parameters for a UC environment in this
library's word model. Here `replyBound` is the prefix length read from each lowered execution
query (not the import field of [Canetti2020], Section 3.2). -/
structure EnvParam : Type where
  /-- The security parameter. -/
  secParam : ℕ
  /-- Prefix length read from each lowered query to the execution interface. -/
  replyBound : ℕ
  /-- Auxiliary input word passed to the environment. -/
  aux : List Bool

/-- Library construction (no cited definition): binary encoding of `EnvParam` as framed unary
`secParam`, framed unary `replyBound`, and unframed `aux` (`encBits`). -/
enc_structure encEnvParam : EnvParam where
  secParam : encUnary, replyBound : encUnary, aux : encBits

/-! ### State codecs, word activations, and strict-PPT certificates -/

/-- Library construction (no cited definition): injective binary presentation of a type `α` with a
total left-inverse decoder. Unlike `Turing.MultiTapeTM.Decoder`, this omits a standalone
`ComputableInDegree` obligation on `decode`; instead `PPTCertificate.normalize` and
`IdealFunctionality.PPTCertificate.normalize` certify the combined word map `enc ∘ decode` in
polynomial time, matching `PPTCertificate.handle` (and `onInput` / `onBackdoor`). -/
structure WordCodec (α : Type) : Type where
  /-- Injectively encode a value as a bit word. -/
  enc : α ↪ List Bool
  /-- Total decoder recovering a value from a bit word. -/
  decode : List Bool → α
  /-- Decoding an encoded value recovers it. -/
  decode_enc : ∀ s, decode (enc s) = s

/-- Library construction (no cited definition): binary state presentation for a family of UC
machines, supplying a `WordCodec` at every `(κ, C)`. -/
abbrev StateCodec {n : ℕ} {ιI ιE : Type} {I : ιI → Type} {E : ιE → Type}
    (M : ℕ → Finset (Fin n) → Machine I E) : Type :=
  ∀ κ C, WordCodec (M κ C).State

/-- Library construction (no cited definition): one word-level activation of `M p.secParam
p.corrupted`. It decodes the exported request via `iE` and the state word via `codec`, runs the
lowered activation with imported replies truncated to `p.replyBound` bits, and re-encodes the
typed reply and updated state. -/
@[expose] def wordHandle {n : ℕ} {ιI ιE : Type} {I : ιI → Type} {E : ιE → Type}
    (M : ℕ → Finset (Fin n) → Machine I E)
    (iI : WordInterface I) (iE : WordInterface E) (codec : StateCodec M)
    (p : PPTParam n) (request : iE.Channel × List Bool) (state : List Bool) :
    WordOracleComp iI.Channel (List Bool × List Bool) :=
  let q := iE.decodeQuery request.1 request.2
  (fun result => (iE.reply q result.1, (codec p.secParam p.corrupted).enc result.2)) <$>
    ProbOracleComp.lowerWith iI p.replyBound
      (((M p.secParam p.corrupted).handle q).run
        ((codec p.secParam p.corrupted).decode state))

/-- Library construction (no cited definition; not Definition 6 of [Canetti2020]): a strict-PPT
certificate for a UC machine family `M` in this library's word model.

* `init` certifies `(M p.secParam p.corrupted).init` under `encPPTParam n` so it shares the
  parameter encoding with `handle`; the initialization program ignores `p.replyBound`.
* `handle` certifies `wordHandle` as a uniform strict oracle-PPT program on `encHandlerCall`.
* `normalize` certifies state-word renormalization `enc ∘ decode` in polynomial time (analogous to
  `WordInterface.computable_replyNormalize`), needed so composite routing/composition branches
  can preserve untouched components' behavior on off-image state words.
* `growth`, `growth_poly`, and `preserve` bound additive encoded-state growth per activation by a
  polynomial in the encoded parameter and request word alone (independent of the current state).
  No state-independent reply bound is imposed: replies may depend on the current state and are
  bounded automatically by `handle`'s output-length bound. -/
structure PPTCertificate {n : ℕ} {ιI ιE : Type} {I : ιI → Type} {E : ιE → Type}
    (M : ℕ → Finset (Fin n) → Machine I E)
    (iI : WordInterface I) (iE : WordInterface E) : Type where
  /-- Binary presentation of the family's private states. -/
  codec : StateCodec M
  /-- Initializing the machine and encoding its initial state is uniform strict PPT under
  `encPPTParam n` (the initialization program ignores `p.replyBound`). -/
  init : IsPPTOn (encPPTParam n) encBits
    (fun p => (codec p.secParam p.corrupted).enc <$> (M p.secParam p.corrupted).init)
  /-- One lowered word activation is uniform strict oracle PPT in the parameter, request, and
  state word. -/
  handle : IsOraclePPTOn
    (encHandlerCall (encPPTParam n) (encFinite iE.Channel) encBits)
    (encPair encBits encBits)
    (fun x => wordHandle M iI iE codec x.1 x.2.1 x.2.2)
  /-- Decoding and re-encoding an arbitrary state word is uniformly computable in polynomial time
  (`enc ∘ decode`). A branch that leaves a component's state unchanged must still re-encode its
  state word, including words outside the codec's image, in polynomial time; this normalization cost
  is needed for closure under routing, adversary placement, and composition (analogous to
  `WordInterface.computable_replyNormalize`). -/
  normalize : ComputableInPolyTime
    (fun x : PPTParam n × List Bool =>
      (codec x.1.secParam x.1.corrupted).enc
        ((codec x.1.secParam x.1.corrupted).decode x.2))
    (encPair (encPPTParam n) encBits) encBits
  /-- Additive encoded-state growth bound per activation, depending only on the parameter and
  request word (not on the current state). -/
  growth : PPTParam n → List Bool → ℕ
  /-- `growth` is polynomially bounded in the encoded parameter and request word. -/
  growth_poly : PolyBounded
    (fun pair : PPTParam n × List Bool => (encPair (encPPTParam n) encBits pair).length)
    (fun pair => growth pair.1 pair.2)
  /-- Starting from any encoded state, every supported word activation grows the encoded state by
  at most `growth p request.2` bits. -/
  preserve : ∀ (p : PPTParam n) (request : iE.Channel × List Bool)
    (s : (M p.secParam p.corrupted).State),
    ∀ result ∈ OracleComp.support
      (wordHandle M iI iE codec p request ((codec p.secParam p.corrupted).enc s)),
      result.2.length ≤ ((codec p.secParam p.corrupted).enc s).length + growth p request.2

/-- Library infrastructure (no cited result): `PPTCertificate.preserve` in the exact invariant
and additive-growth form consumed by
`IsOraclePPTOn.run_interpret_preprocess_open_of_bounded_growth`. -/
theorem PPTCertificate.preserve_wordHandle {n : ℕ} {ιI ιE : Type} {I : ιI → Type} {E : ιE → Type}
    {M : ℕ → Finset (Fin n) → Machine I E} {iI : WordInterface I} {iE : WordInterface E}
    (cert : PPTCertificate M iI iE) (p : PPTParam n) (request : iE.Channel × List Bool)
    (state : List Bool)
    (hstate : state ∈ Set.range (cert.codec p.secParam p.corrupted).enc)
    (result : List Bool × List Bool)
    (hresult : result ∈ OracleComp.support (wordHandle M iI iE cert.codec p request state)) :
    result.2 ∈ Set.range (cert.codec p.secParam p.corrupted).enc ∧
      result.2.length ≤ state.length + cert.growth p request.2 := by
  rcases hstate with ⟨s, rfl⟩
  refine ⟨?_, cert.preserve p request s result hresult⟩
  rw [wordHandle, OracleComp.mem_supportWith_map_iff] at hresult
  rcases hresult with ⟨x, _, rfl⟩
  exact ⟨x.2, rfl⟩

/-! ### Strict-PPT predicates for UC machines, protocols, adversaries, and environments -/

/-- Library construction (no cited definition; not Definition 6 of [Canetti2020]): a UC machine
family is strict PPT in this library's word model when it admits a `PPTCertificate`. -/
@[expose] def Machine.IsPPTFamily {n : ℕ} {ιI ιE : Type} {I : ιI → Type} {E : ιE → Type}
    (M : ℕ → Finset (Fin n) → Machine I E) (iI : WordInterface I) (iE : WordInterface E) : Prop :=
  Nonempty (PPTCertificate M iI iE)

/-- Library construction (no cited definition; follows the typed-object-plus-encoding convention
of `AdversaryOf.IsPPT`, not Definition 6 of [Canetti2020]): a UC protocol is strict PPT in this
library's word model for party port `party` and network port `netPort` when it admits a
`PPTCertificate` over `WordInterface.empty` and `WordInterface.protocol party netPort`. No
implication to or from `Protocol.PolyBounded` is claimed. -/
@[expose] def Protocol.IsPPT {n : ℕ} {In Out NetQ NetR : Type}
    (π : Protocol n In Out NetQ NetR)
    (party : WordPort (Fin n × In) (Option Out)) (netPort : WordPort NetQ NetR) : Prop :=
  Machine.IsPPTFamily π WordInterface.empty (WordInterface.protocol party netPort)

/-- Library construction (no cited definition; follows the typed-object-plus-encoding convention
of `AdversaryOf.IsPPT`, not Definition 6 of [Canetti2020]): a UC adversary is strict PPT in this
library's word model for imported network port `netPort` and exported adversary port `adv` when it
admits a `PPTCertificate` over `WordInterface.net netPort` and `WordInterface.net adv`. No
implication to or from `Adversary.PolyBounded` is claimed. -/
@[expose] def Adversary.IsPPT {n : ℕ} {AdvQ AdvR NetQ NetR : Type}
    (A : Adversary n AdvQ AdvR NetQ NetR)
    (netPort : WordPort NetQ NetR) (adv : WordPort AdvQ AdvR) : Prop :=
  Machine.IsPPTFamily A (WordInterface.net netPort) (WordInterface.net adv)

/-- Library construction (no cited definition; follows the typed-object-plus-encoding convention
of `AdversaryOf.IsPPT` and aligns docstring style with `MPC.Environment.IsPPT`, not Definition 6 of
[Canetti2020]): a UC environment is uniform strict oracle PPT for `party` and `adv` when one
uniform strict oracle-PPT machine reads `encEnvParam` (unary `secParam`, unary `replyBound`, and
`aux`) and simulates the lowered execution program `ProbOracleComp.lowerWith
(WordInterface.exec party adv) e.replyBound (Z e.secParam e.aux)`.

Because the clock is polynomial in `secParam + replyBound + aux.length`, this admits environments
whose work grows with `replyBound` and `aux.length` (unlike `Environment.PolyBounded`'s `κ`-only
call budget), and it is uniform (no nonuniform advice). No implication to or from
`Environment.PolyBounded` is claimed. -/
@[expose] def Environment.IsPPT {n : ℕ} {In Out AdvQ AdvR : Type}
    (Z : Environment n In Out AdvQ AdvR)
    (party : WordPort (Fin n × In) (Option Out)) (adv : WordPort AdvQ AdvR) : Prop :=
  IsOraclePPTOn encEnvParam encBool fun e =>
    ProbOracleComp.lowerWith (WordInterface.exec party adv) e.replyBound (Z e.secParam e.aux)

/-! ### Ideal functionalities -/

/-- Library construction (no cited definition): one word-level activation of a closed ideal
functionality step `step`, decoding the request word through `port` and the state word through
`codec`, running `step`, and re-encoding the reply and updated state. -/
@[expose] def IdealFunctionality.wordStep {Q R S : Type} (port : WordPort Q R)
    (codec : WordCodec S) (step : Q → StateT S ProbComp R) (p : List Bool × List Bool) :
    ProbComp (List Bool × List Bool) :=
  (fun result => (port.reply result.1, codec.enc result.2)) <$>
    (step (port.queryDecoder.decode p.1)).run (codec.decode p.2)

/-- Library construction (no cited definition; not Definition 6 of [Canetti2020]): a strict-PPT
certificate for a UC ideal functionality in this library's word model. Because an ideal
functionality makes no imported oracle calls and `onInput`/`onBackdoor` do not depend on `κ` or `C`,
`init` is certified on `(κ, C)` while `onInput` and `onBackdoor` are certified as closed `IsPPTOn`
programs on `(request word, state word)` with one additive encoded-state growth bound. -/
structure IdealFunctionality.PPTCertificate {n : ℕ} {In Out BackQ BackR : Type}
    (F : IdealFunctionality n In Out BackQ BackR)
    (party : WordPort (Fin n × In) (Option Out)) (back : WordPort BackQ BackR) : Type where
  /-- Binary presentation of the functionality's private state. -/
  stateCodec : WordCodec F.State
  /-- Initializing the functionality and encoding its state is uniform strict PPT in `(κ, C)`. -/
  init : IsPPTOn (encPair encUnary (encFinite (Finset (Fin n)))) encBits
    (fun p => stateCodec.enc <$> F.init p.1 p.2)
  /-- Answering a decoded party-port word request and re-encoding the reply and next state is
  uniform strict PPT. -/
  onInput : IsPPTOn (encPair encBits encBits) (encPair encBits encBits)
    (IdealFunctionality.wordStep party stateCodec fun q => F.onInput q.1 q.2)
  /-- Answering a decoded backdoor word request and re-encoding the reply and next state is
  uniform strict PPT. -/
  onBackdoor : IsPPTOn (encPair encBits encBits) (encPair encBits encBits)
    (IdealFunctionality.wordStep back stateCodec F.onBackdoor)
  /-- Decoding and re-encoding an arbitrary state word is computable in polynomial time
  (`stateCodec.enc ∘ stateCodec.decode`): a branch that leaves a component's state unchanged must
  still re-encode its state word, including words outside the codec's image, in polynomial time,
  needed for closure under hybrid wrapping and protocol composition (analogous to
  `WordInterface.computable_replyNormalize`). -/
  normalize : ComputableInPolyTime
    (fun w : List Bool => stateCodec.enc (stateCodec.decode w))
    encBits encBits
  /-- Additive encoded-state growth bound per activation, depending only on the request word. -/
  growth : List Bool → ℕ
  /-- `growth` is polynomially bounded in the request word length. -/
  growth_poly : PolyBounded List.length growth
  /-- Every supported party-port transition from an encoded state grows the encoded state by at
  most `growth req` bits. -/
  preserve_onInput : ∀ (req : List Bool) (s : F.State),
    let q := party.queryDecoder.decode req
    ∀ result ∈ (ProbComp.eval ((F.onInput q.1 q.2).run s)).support,
      (stateCodec.enc result.2).length ≤ (stateCodec.enc s).length + growth req
  /-- Every supported backdoor transition from an encoded state grows the encoded state by at
  most `growth req` bits. -/
  preserve_onBackdoor : ∀ (req : List Bool) (s : F.State),
    ∀ result ∈ (ProbComp.eval ((F.onBackdoor (back.queryDecoder.decode req)).run s)).support,
      (stateCodec.enc result.2).length ≤ (stateCodec.enc s).length + growth req

/-- Library construction (no cited definition; follows the typed-object-plus-encoding convention
of `AdversaryOf.IsPPT`, not Definition 6 of [Canetti2020]): a UC ideal functionality is strict PPT
in this library's word model for party port `party` and backdoor port `back` when it admits an
`IdealFunctionality.PPTCertificate`. -/
@[expose] def IdealFunctionality.IsPPT {n : ℕ} {In Out BackQ BackR : Type}
    (F : IdealFunctionality n In Out BackQ BackR)
    (party : WordPort (Fin n × In) (Option Out)) (back : WordPort BackQ BackR) : Prop :=
  Nonempty (IdealFunctionality.PPTCertificate F party back)

/-! ### Environment-machine composition -/

/-- Library construction (no cited definition): state-passing word-level execution of a lowered
UC environment `Z` evaluated at `envParam e` against `wordHandle` at `param e`, starting from an
already-encoded machine state `state`. -/
@[expose] def wordRunFrom
    {n : ℕ} {ιI : Type} {I : ιI → Type} {In Out AdvQ AdvR : Type}
    (M : ℕ → Finset (Fin n) → Machine I (execSpec n In Out AdvQ AdvR))
    (iI : WordInterface I) (party : WordPort (Fin n × In) (Option Out))
    (adv : WordPort AdvQ AdvR) (codec : StateCodec M)
    (Z : Environment n In Out AdvQ AdvR)
    (param : EnvParam → PPTParam n) (envParam : EnvParam → EnvParam)
    (e : EnvParam) (state : List Bool) :
    WordOracleComp iI.Channel (Bool × List Bool) :=
  let iE := WordInterface.exec party adv
  let ep := envParam e
  (OracleComp.interpret
    (OracleComp.sumHandler
      (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
      (wordHandle M iI iE codec (param e)))
    (ProbOracleComp.lowerWith iE ep.replyBound (Z ep.secParam ep.aux))).run state

/-- Library construction (no cited definition): word-level execution of a lowered UC environment
`Z` evaluated at `envParam e` against a machine family `M` at `param e` equipped with a
`StateCodec`, sampling the encoded initial state of `M (param e).secParam (param e).corrupted` and
interpreting the lowered environment through `wordHandle`. -/
@[expose] def wordRun
    {n : ℕ} {ιI : Type} {I : ιI → Type} {In Out AdvQ AdvR : Type}
    (M : ℕ → Finset (Fin n) → Machine I (execSpec n In Out AdvQ AdvR))
    (iI : WordInterface I) (party : WordPort (Fin n × In) (Option Out))
    (adv : WordPort AdvQ AdvR) (codec : StateCodec M)
    (Z : Environment n In Out AdvQ AdvR)
    (param : EnvParam → PPTParam n) (envParam : EnvParam → EnvParam) (e : EnvParam) :
    WordOracleComp iI.Channel Bool := do
  let p := param e
  let s0 ← ProbOracleComp.sample
    ((codec p.secParam p.corrupted).enc <$> (M p.secParam p.corrupted).init)
  Prod.fst <$> wordRunFrom M iI party adv codec Z param envParam e s0

/-- Library infrastructure (no cited result): running a strict-PPT environment at `envParam e`
against any machine family equipped with a `PPTCertificate` at `param e` via `wordRun`
(sampling the initial encoded state via `cert.init` and interpreting lowered queries via
`cert.handle` with polynomially bounded additive state growth `cert.preserve_wordHandle`) yields a
uniform strict oracle-PPT program over `iI.Channel`. -/
theorem Environment.IsPPT.isOraclePPTOn_run_wordHandle
    {n : ℕ} {ιI : Type} {I : ιI → Type} {In Out AdvQ AdvR : Type}
    {party : WordPort (Fin n × In) (Option Out)} {adv : WordPort AdvQ AdvR}
    {Z : Environment n In Out AdvQ AdvR}
    (hZ : Z.IsPPT party adv)
    {iI : WordInterface I}
    {M : ℕ → Finset (Fin n) → Machine I (execSpec n In Out AdvQ AdvR)}
    (cert : PPTCertificate M iI (WordInterface.exec party adv))
    {param : EnvParam → PPTParam n} {envParam : EnvParam → EnvParam}
    (hparam : ComputableInPolyTime param encEnvParam (encPPTParam n))
    (henv : ComputableInPolyTime envParam encEnvParam encEnvParam) :
    IsOraclePPTOn (Operation := iI.Channel) encEnvParam encBool
      (wordRun M iI party adv cert.codec Z param envParam) := by
  let iE := WordInterface.exec party adv
  let ValidState : Type :=
    { x : EnvParam × List Bool //
      x.2 ∈ Set.range (cert.codec (param x.1).secParam (param x.1).corrupted).enc }
  let encValid : ValidState ↪ List Bool :=
    (Function.Embedding.subtype _).trans (encPair encEnvParam encBits)
  have hval : ComputableInPolyTime (fun x : ValidState => x.1)
      encValid (encPair encEnvParam encBits) :=
    ComputableInPolyTime.of_eq fun _ => rfl
  have hinitBase : IsPPTOn encEnvParam (encPair encEnvParam encBits) fun e =>
      (fun w => (e, w)) <$>
        ((cert.codec (param e).secParam (param e).corrupted).enc <$>
          (M (param e).secParam (param e).corrupted).init) :=
    (cert.init.preprocess hparam).keep_input
  have hinitValid : IsPPTOn encEnvParam encValid fun e =>
      (fun s => (⟨(e, (cert.codec (param e).secParam (param e).corrupted).enc s),
        ⟨s, rfl⟩⟩ : ValidState)) <$>
        (M (param e).secParam (param e).corrupted).init := by
    rw [isPPTOn_iff_encoded] at hinitBase ⊢
    refine hinitBase.congr fun e => ?_
    simp only [encValid, Function.Embedding.trans_apply, ProbComp.eval_map, PMF.map_comp,
      Function.comp_def]
    rfl
  have hstep : IsOraclePPTOn (Operation := iI.Channel)
      encValid (encPair encBool encBits) fun x =>
        wordRunFrom M iI party adv cert.codec Z param envParam x.1.1 x.1.2 := by
    have hbase : ComputableInPolyTime (fun x : ValidState => x.1.1) encValid encEnvParam :=
      (ComputableInPolyTime.fst encEnvParam encBits).comp hval
    have hprepare : ComputableInPolyTime (fun x : ValidState => envParam x.1.1)
        encValid encEnvParam :=
      henv.comp hbase
    have hparamValid : ComputableInPolyTime (fun x : ValidState => param x.1.1)
        encValid (encPPTParam n) :=
      hparam.comp hbase
    have hhandlerProj : ComputableInPolyTime
        (fun x : ValidState × ((iE.Channel × List Bool) × List Bool) =>
          (param x.1.1.1, x.2))
        (encHandlerCall encValid (encFinite iE.Channel) encBits)
        (encHandlerCall (encPPTParam n) (encFinite iE.Channel) encBits) :=
      (hparamValid.comp (ComputableInPolyTime.fst _ _)).prod (ComputableInPolyTime.snd _ _)
    have hhandler : IsOraclePPTOn
        (encHandlerCall encValid (encFinite iE.Channel) encBits)
        (encPair encBits encBits)
        (fun x => wordHandle M iI iE cert.codec (param x.1.1.1) x.2.1 x.2.2) :=
      cert.handle.preprocess hhandlerProj
    have hinitProj : ComputableInPolyTime (fun x : ValidState => x.1.2) encValid encBits :=
      (ComputableInPolyTime.snd encEnvParam encBits).comp hval
    have hgrowthProj : ComputableInPolyTime
        (fun pair : ValidState × List Bool => (param pair.1.1.1, pair.2))
        (encPair encValid encBits) (encPair (encPPTParam n) encBits) :=
      (hparamValid.comp (ComputableInPolyTime.fst _ _)).prod (ComputableInPolyTime.snd _ _)
    have hgrowth : Turing.MultiTapeTM.PolyBounded
        (fun pair : ValidState × List Bool => (encPair encValid encBits pair).length)
        (fun pair => cert.growth (param pair.1.1.1) pair.2) :=
      cert.growth_poly.comp hgrowthProj.polyBounded_length
    exact IsOraclePPTOn.run_interpret_preprocess_open_of_bounded_growth
      (Operation := iE.Channel) (External := iI.Channel)
      (operationEncoding := encFinite iE.Channel)
      (program := fun e : EnvParam =>
        ProbOracleComp.lowerWith iE e.replyBound (Z e.secParam e.aux))
      hZ hprepare hhandler hinitProj
      (fun x state =>
        state ∈ Set.range (cert.codec (param x.1.1).secParam (param x.1.1).corrupted).enc)
      (fun x => x.2) hgrowth
      (fun x req state hinv result hmem =>
        cert.preserve_wordHandle (param x.1.1) req state hinv result hmem)
  have hcombined : IsOraclePPTOn (Operation := iI.Channel)
      encEnvParam encBool fun e =>
        Prod.fst <$> (ProbOracleComp.sample
          ((fun s => (⟨(e, (cert.codec (param e).secParam (param e).corrupted).enc s),
            ⟨s, rfl⟩⟩ : ValidState)) <$>
            (M (param e).secParam (param e).corrupted).init) >>= fun x =>
          wordRunFrom M iI party adv cert.codec Z param envParam x.1.1 x.1.2) :=
    (hinitValid.isOraclePPTOn.bind hstep).map (ComputableInPolyTime.fst encBool encBits)
  refine hcombined.congr fun e State oracle s => ?_
  simp only [wordRun, ProbOracleComp.runWith_map, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_sample, ProbComp.eval_map, PMF.bind_map, PMF.map_bind,
    Function.comp_def]

/-! ### Baseline certificates -/

/-- Library construction (no cited definition): canonical `WordCodec` for `PUnit` states,
encoding `PUnit.unit` as `[]`. -/
@[expose] def punitWordCodec : WordCodec PUnit where
  enc := ⟨fun _ => [], fun a b _ => by cases a; cases b; rfl⟩
  decode := fun _ => PUnit.unit
  decode_enc := fun _ => rfl

/-- Library infrastructure (no cited result): the stateless forwarding machine `Machine.id E` has
a strict-PPT certificate over any `WordInterface E`. -/
theorem Machine.isPPTFamily_id {n : ℕ} {ι : Type} {E : ι → Type} (I : WordInterface E) :
    Machine.IsPPTFamily (fun (_ : ℕ) (_ : Finset (Fin n)) => Machine.id E) I I := by
  refine ⟨{
    codec := fun _ _ => punitWordCodec
    init := by
      change IsPPTOn (encPPTParam n) encBits (fun _ => pure [])
      exact (ComputableInPolyTime.const (encIn := encPPTParam n) (encOut := encBits) []).isPPTOn
    handle := ?_
    normalize := ComputableInPolyTime.const (encIn := encPair (encPPTParam n) encBits)
      (encOut := encBits) []
    growth := fun _ _ => 0
    growth_poly := PolyBounded.const 0
    preserve := ?_ }⟩
  · have hquery : IsOraclePPTOn
        (encHandlerCall (encPPTParam n) (encFinite I.Channel) encBits) encBits
        (fun x =>
          I.reply (I.decodeQuery x.2.1.1 x.2.1.2) <$>
            ProbOracleComp.lowerWith I x.1.replyBound
              (ProbOracleComp.query (I.decodeQuery x.2.1.1 x.2.1.2))) := by
      refine I.isOraclePPTOn_lowerWith_decodeQuery
        (ch := fun x : PPTParam n × (I.Channel × List Bool) × List Bool => x.2.1.1)
        (word := fun x => x.2.1.2) (limit := fun x => x.1.replyBound) ?_ ?_ ?_ <;>
        (unfold encHandlerCall; fun_prop)
    have hpair : IsOraclePPTOn
        (encHandlerCall (encPPTParam n) (encFinite I.Channel) encBits)
        (encPair encBits encBits)
        (fun x => (fun w => (w, ([] : List Bool))) <$>
          (I.reply (I.decodeQuery x.2.1.1 x.2.1.2) <$>
            ProbOracleComp.lowerWith I x.1.replyBound
              (ProbOracleComp.query (I.decodeQuery x.2.1.1 x.2.1.2)))) := by
      refine hquery.map ?_
      fun_prop
    refine hpair.congr fun x State oracle s => ?_
    simp only [wordHandle, Machine.id, punitWordCodec, StateT.run, StateT.lift,
      ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind, ProbOracleComp.simulate_pure,
      map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    rfl
  · intro p request s result hresult
    dsimp only [wordHandle] at hresult
    rw [OracleComp.mem_supportWith_map_iff] at hresult
    rcases hresult with ⟨x, _, rfl⟩
    exact Nat.le_refl 0

/-- Library infrastructure (no cited result): the dummy adversary forwarding `netSpec NetQ NetR` has
a strict-PPT certificate in this library's word model (toward `#6043`, not Definition 6 of
`[Canetti2020]`). -/
theorem Adversary.isPPT_dummyAdversary (n : ℕ) {NetQ NetR : Type} (net : WordPort NetQ NetR) :
    (dummyAdversary n NetQ NetR).IsPPT net net :=
  Machine.isPPTFamily_id (WordInterface.net net)

/-- Library infrastructure (no cited result): a strict-PPT ideal functionality induces a strict-PPT
protocol via `IdealFunctionality.toProtocol`. -/
theorem IdealFunctionality.IsPPT.toProtocol {n : ℕ} {In Out BackQ BackR : Type}
    {F : IdealFunctionality n In Out BackQ BackR}
    {party : WordPort (Fin n × In) (Option Out)} {back : WordPort BackQ BackR}
    (h : F.IsPPT party back) :
    F.toProtocol.IsPPT party back := by
  rcases h with ⟨cert⟩
  let codec : StateCodec F.toProtocol := fun _ _ => cert.stateCodec
  refine ⟨{
    codec := codec
    init := ?_
    handle := ?_
    normalize := cert.normalize.comp (ComputableInPolyTime.snd (encPPTParam n) encBits)
    growth := fun _ w => cert.growth w
    growth_poly := ?_
    preserve := ?_ }⟩
  · have hproj : ComputableInPolyTime
        (fun p : PPTParam n => (p.secParam, p.corrupted))
        (encPPTParam n) (encPair encUnary (encFinite (Finset (Fin n)))) := by
      fun_prop
    exact cert.init.preprocess hproj
  · let iP := WordInterface.protocol party back
    have htag : ComputableInPolyTime
        (fun x : PPTParam n × (iP.Channel × List Bool) × List Bool => x.2.1.1)
        (encHandlerCall (encPPTParam n) (encFinite iP.Channel) encBits)
        (encFinite iP.Channel) := by
      unfold encHandlerCall
      fun_prop
    have hreqState : ComputableInPolyTime
        (fun x : PPTParam n × (iP.Channel × List Bool) × List Bool => (x.2.1.2, x.2.2))
        (encHandlerCall (encPPTParam n) (encFinite iP.Channel) encBits)
        (encPair encBits encBits) := by
      unfold encHandlerCall
      fun_prop
    let branch : iP.Channel → PPTParam n × (iP.Channel × List Bool) × List Bool →
        WordOracleComp WordInterface.empty.Channel (List Bool × List Bool) := fun c x =>
      match c with
      | .inl () => ProbOracleComp.sample
          (IdealFunctionality.wordStep party cert.stateCodec
            (fun q => F.onInput q.1 q.2) (x.2.1.2, x.2.2))
      | .inr () => ProbOracleComp.sample
          (IdealFunctionality.wordStep back cert.stateCodec F.onBackdoor (x.2.1.2, x.2.2))
    have hcases : IsOraclePPTOn (Operation := WordInterface.empty.Channel)
        (encHandlerCall (encPPTParam n) (encFinite iP.Channel) encBits)
        (encPair encBits encBits)
        (fun x => branch x.2.1.1 x) := by
      refine IsOraclePPTOn.finite_cases (Operation := WordInterface.empty.Channel)
        (Tag := iP.Channel)
        (tag := fun x : PPTParam n × (iP.Channel × List Bool) × List Bool => x.2.1.1)
        (branch := branch) htag ?_
      rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
      · exact (cert.onInput.preprocess hreqState).isOraclePPTOn
      · exact (cert.onBackdoor.preprocess hreqState).isOraclePPTOn
    refine hcases.congr fun x State oracle s => ?_
    rcases x with ⟨p, ⟨ch, req⟩, state⟩
    rcases ch with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;>
      (simp only [branch, IdealFunctionality.wordStep, wordHandle, IdealFunctionality.toProtocol,
        codec, WordInterface.protocol, WordInterface.sum, WordInterface.net, StateT.run,
        ProbOracleComp.lowerWith, ProbOracleComp.simulate_sample, ProbOracleComp.sample_map]; rfl)
  · growth_poly [cert.growth_poly]
  · intro p request s result hresult
    rcases request with ⟨ch, req⟩
    rw [wordHandle, (codec p.secParam p.corrupted).decode_enc] at hresult
    rcases ch with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;>
      simp only [IdealFunctionality.toProtocol, codec, WordInterface.protocol, WordInterface.sum,
        WordInterface.net, StateT.run, ProbOracleComp.lowerWith, ProbOracleComp.simulate_sample,
        OracleComp.mem_supportWith_map_iff, ProbOracleComp.support_sample] at hresult <;>
      obtain ⟨r, hr, rfl⟩ := hresult
    exacts [cert.preserve_onInput req s r hr, cert.preserve_onBackdoor req s r hr]

end Cslib.Crypto.Protocols.UC
