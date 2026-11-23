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
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.PPT.Composition
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
* `Cslib.Crypto.Protocols.UC.StateCodec`: injective binary state encoder and total left-inverse
  decoder for a family of UC machines.
* `Cslib.Crypto.Protocols.UC.wordHandle`: one word-level activation of a typed UC machine family
  lowered through `WordInterface`s and `StateCodec`.
* `Cslib.Crypto.Protocols.UC.PPTCertificate`: strict-PPT certificate for a UC machine family
  (`init`, `handle`, and polynomially bounded additive state growth `preserve`).
* `Cslib.Crypto.Protocols.UC.Machine.IsPPTFamily`, `Cslib.Crypto.Protocols.UC.Protocol.IsPPT`,
  `Cslib.Crypto.Protocols.UC.Adversary.IsPPT`, `Cslib.Crypto.Protocols.UC.Environment.IsPPT`,
  `Cslib.Crypto.Protocols.UC.IdealFunctionality.PPTCertificate`,
  `Cslib.Crypto.Protocols.UC.IdealFunctionality.IsPPT`: strict-PPT predicates for UC machines,
  protocols, adversaries, environments, and ideal functionalities.

## Main results

* `Cslib.Crypto.Protocols.UC.PPTCertificate.preserve_wordHandle`: invariant-and-growth bridge
  from `PPTCertificate` to `IsOraclePPTOn.run_interpret_preprocess_open_of_bounded_growth`.
* `Cslib.Crypto.Protocols.UC.Machine.isPPTFamily_id`: the forwarding machine `Machine.id` is
  strict PPT over any `WordInterface`.
* `Cslib.Crypto.Protocols.UC.Adversary.isPPT_dummyAdversary`: the dummy adversary is strict PPT
  over any network `WordPort`.
* `Cslib.Crypto.Protocols.UC.IdealFunctionality.IsPPT.toProtocol`: a strict-PPT ideal
  functionality yields a strict-PPT protocol.

## References

* [R. Canetti, *Universally Composable Security*][Canetti2020], Section 3.2 and Section 4:
  context for UC interactive machines and the dummy adversary. The strict-PPT certificates here
  are library constructions for this word model, not Definition 6 of [Canetti2020].
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

/-- Library construction (no cited definition): binary state presentation for a family of UC
machines, supplying an injective encoder and a total left-inverse decoder at every `(κ, C)`. -/
structure StateCodec {n : ℕ} {ιI ιE : Type} {I : ιI → Type} {E : ιE → Type}
    (M : ℕ → Finset (Fin n) → Machine I E) : Type where
  /-- Injectively encode a machine state as a bit word. -/
  enc : ∀ κ C, (M κ C).State ↪ List Bool
  /-- Total decoder recovering a machine state from a bit word. -/
  decode : ∀ κ C, List Bool → (M κ C).State
  /-- Decoding an encoded state recovers it. -/
  decode_enc : ∀ κ C s, decode κ C (enc κ C s) = s

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
  (fun result => (iE.reply q result.1, codec.enc p.secParam p.corrupted result.2)) <$>
    ProbOracleComp.lowerWith iI p.replyBound
      (((M p.secParam p.corrupted).handle q).run (codec.decode p.secParam p.corrupted state))

/-- Library construction (no cited definition; not Definition 6 of [Canetti2020]): a strict-PPT
certificate for a UC machine family `M` in this library's word model.

* `init` certifies `(M p.secParam p.corrupted).init` under `encPPTParam n` so it shares the
  parameter encoding with `handle`; the initialization program ignores `p.replyBound`.
* `handle` certifies `wordHandle` as a uniform strict oracle-PPT program on `encHandlerCall`.
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
    (fun p => codec.enc p.secParam p.corrupted <$> (M p.secParam p.corrupted).init)
  /-- One lowered word activation is uniform strict oracle PPT in the parameter, request, and
  state word. -/
  handle : IsOraclePPTOn
    (encHandlerCall (encPPTParam n) (encFinite iE.Channel) encBits)
    (encPair encBits encBits)
    (fun x => wordHandle M iI iE codec x.1 x.2.1 x.2.2)
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
      (wordHandle M iI iE codec p request (codec.enc p.secParam p.corrupted s)),
      result.2.length ≤ (codec.enc p.secParam p.corrupted s).length + growth p request.2

/-- Library infrastructure (no cited result): `PPTCertificate.preserve` in the exact invariant
and additive-growth form consumed by
`IsOraclePPTOn.run_interpret_preprocess_open_of_bounded_growth`. -/
theorem PPTCertificate.preserve_wordHandle {n : ℕ} {ιI ιE : Type} {I : ιI → Type} {E : ιE → Type}
    {M : ℕ → Finset (Fin n) → Machine I E} {iI : WordInterface I} {iE : WordInterface E}
    (cert : PPTCertificate M iI iE) (p : PPTParam n) (request : iE.Channel × List Bool)
    (state : List Bool) (hstate : state ∈ Set.range (cert.codec.enc p.secParam p.corrupted))
    (result : List Bool × List Bool)
    (hresult : result ∈ OracleComp.support (wordHandle M iI iE cert.codec p request state)) :
    result.2 ∈ Set.range (cert.codec.enc p.secParam p.corrupted) ∧
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

/-- Library construction (no cited definition; not Definition 6 of [Canetti2020]): a strict-PPT
certificate for a UC ideal functionality in this library's word model. Because an ideal
functionality makes no imported oracle calls and `onInput`/`onBackdoor` do not depend on `κ` or `C`,
`init` is certified on `(κ, C)` while `onInput` and `onBackdoor` are certified as closed `IsPPTOn`
programs on `(request word, state word)` with one additive encoded-state growth bound. -/
structure IdealFunctionality.PPTCertificate {n : ℕ} {In Out BackQ BackR : Type}
    (F : IdealFunctionality n In Out BackQ BackR)
    (party : WordPort (Fin n × In) (Option Out)) (back : WordPort BackQ BackR) : Type where
  /-- Injectively encode a functionality state as a bit word. -/
  stateEnc : F.State ↪ List Bool
  /-- Total decoder recovering a functionality state from a bit word. -/
  stateDecode : List Bool → F.State
  /-- Decoding an encoded state recovers it. -/
  stateDecode_enc : ∀ s, stateDecode (stateEnc s) = s
  /-- Initializing the functionality and encoding its state is uniform strict PPT in `(κ, C)`. -/
  init : IsPPTOn (encPair encUnary (encFinite (Finset (Fin n)))) encBits
    (fun p => stateEnc <$> F.init p.1 p.2)
  /-- Answering a decoded party-port word request and re-encoding the reply and next state is
  uniform strict PPT. -/
  onInput : IsPPTOn (encPair encBits encBits) (encPair encBits encBits)
    (fun p =>
      let q := party.queryDecoder.decode p.1
      (fun result => (party.reply result.1, stateEnc result.2)) <$>
        (F.onInput q.1 q.2).run (stateDecode p.2))
  /-- Answering a decoded backdoor word request and re-encoding the reply and next state is
  uniform strict PPT. -/
  onBackdoor : IsPPTOn (encPair encBits encBits) (encPair encBits encBits)
    (fun p =>
      (fun result => (back.reply result.1, stateEnc result.2)) <$>
        (F.onBackdoor (back.queryDecoder.decode p.1)).run (stateDecode p.2))
  /-- Additive encoded-state growth bound per activation, depending only on the request word. -/
  growth : List Bool → ℕ
  /-- `growth` is polynomially bounded in the request word length. -/
  growth_poly : PolyBounded List.length growth
  /-- Every supported party-port transition from an encoded state grows the encoded state by at
  most `growth req` bits. -/
  preserve_onInput : ∀ (req : List Bool) (s : F.State),
    let q := party.queryDecoder.decode req
    ∀ result ∈ (ProbComp.eval ((F.onInput q.1 q.2).run s)).support,
      (stateEnc result.2).length ≤ (stateEnc s).length + growth req
  /-- Every supported backdoor transition from an encoded state grows the encoded state by at
  most `growth req` bits. -/
  preserve_onBackdoor : ∀ (req : List Bool) (s : F.State),
    ∀ result ∈ (ProbComp.eval ((F.onBackdoor (back.queryDecoder.decode req)).run s)).support,
      (stateEnc result.2).length ≤ (stateEnc s).length + growth req

/-- Library construction (no cited definition; follows the typed-object-plus-encoding convention
of `AdversaryOf.IsPPT`, not Definition 6 of [Canetti2020]): a UC ideal functionality is strict PPT
in this library's word model for party port `party` and backdoor port `back` when it admits an
`IdealFunctionality.PPTCertificate`. -/
@[expose] def IdealFunctionality.IsPPT {n : ℕ} {In Out BackQ BackR : Type}
    (F : IdealFunctionality n In Out BackQ BackR)
    (party : WordPort (Fin n × In) (Option Out)) (back : WordPort BackQ BackR) : Prop :=
  Nonempty (IdealFunctionality.PPTCertificate F party back)

/-! ### Baseline certificates -/

private def punitStateCodec {n : ℕ} {ι : Type} (E : ι → Type) :
    StateCodec (fun (_ : ℕ) (_ : Finset (Fin n)) => Machine.id E) where
  enc _ _ := ⟨fun _ => [], fun a b _ => by cases a; cases b; rfl⟩
  decode _ _ _ := PUnit.unit
  decode_enc _ _ _ := rfl

/-- Library infrastructure (no cited result): the stateless forwarding machine `Machine.id E` has
a strict-PPT certificate over any `WordInterface E`. -/
theorem Machine.isPPTFamily_id {n : ℕ} {ι : Type} {E : ι → Type} (I : WordInterface E) :
    Machine.IsPPTFamily (fun (_ : ℕ) (_ : Finset (Fin n)) => Machine.id E) I I := by
  refine ⟨{
    codec := punitStateCodec E
    init := by
      change IsPPTOn (encPPTParam n) encBits (fun _ => pure [])
      exact (ComputableInPolyTime.const (encIn := encPPTParam n) (encOut := encBits) []).isPPTOn
    handle := ?_
    growth := fun _ _ => 0
    growth_poly := PolyBounded.const 0
    preserve := ?_ }⟩
  · have hquery : IsOraclePPTOn
        (encHandlerCall (encPPTParam n) (encFinite I.Channel) encBits) encBits
        (fun x =>
          I.reply (I.decodeQuery x.2.1.1 x.2.1.2) <$>
            ProbOracleComp.lowerWith I x.1.replyBound
              (ProbOracleComp.query (I.decodeQuery x.2.1.1 x.2.1.2))) := by
      refine I.isOraclePPTOn_lowerWith_query
        (query := fun x : PPTParam n × (I.Channel × List Bool) × List Bool =>
          I.decodeQuery x.2.1.1 x.2.1.2)
        (limit := fun x => x.1.replyBound) ?_ ?_ ?_
      · have heq : (fun x : PPTParam n × (I.Channel × List Bool) × List Bool =>
            I.channel (I.decodeQuery x.2.1.1 x.2.1.2)) = fun x => x.2.1.1 :=
          funext fun x => (I.request_decodeQuery x.2.1.1 x.2.1.2).1
        rw [heq]
        unfold encHandlerCall
        fun_prop
      · have heq : (fun x : PPTParam n × (I.Channel × List Bool) × List Bool =>
            I.request (I.decodeQuery x.2.1.1 x.2.1.2)) =
            fun x => I.requestNormalize x.2.1.1 x.2.1.2 :=
          funext fun x => (I.request_decodeQuery x.2.1.1 x.2.1.2).2
        rw [heq]
        have hproj : ComputableInPolyTime
            (fun x : PPTParam n × (I.Channel × List Bool) × List Bool => x.2.1)
            (encHandlerCall (encPPTParam n) (encFinite I.Channel) encBits)
            (encPair (encFinite I.Channel) encBits) := by
          unfold encHandlerCall
          fun_prop
        exact I.computable_requestNormalize.comp hproj
      · unfold encHandlerCall
        fun_prop
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
    simp only [wordHandle, Machine.id, punitStateCodec, StateT.run, StateT.lift,
      ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind, ProbOracleComp.simulate_pure,
      map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    rfl
  · intro p request s result hresult
    rw [wordHandle, OracleComp.mem_supportWith_map_iff] at hresult
    rcases hresult with ⟨x, _, rfl⟩
    exact Nat.le_refl 0

/-- Library infrastructure toward #6043 (not Definition 6 of [Canetti2020]): the dummy adversary
forwarding `netSpec NetQ NetR` has a strict-PPT certificate in this library's word model. -/
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
  let codec : StateCodec F.toProtocol := {
    enc := fun _ _ => cert.stateEnc
    decode := fun _ _ => cert.stateDecode
    decode_enc := fun _ _ => cert.stateDecode_enc }
  refine ⟨{
    codec := codec
    init := ?_
    handle := ?_
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
      | .inl () => ProbOracleComp.sample (
          let q := party.queryDecoder.decode x.2.1.2
          (fun result => (party.reply result.1, cert.stateEnc result.2)) <$>
            (F.onInput q.1 q.2).run (cert.stateDecode x.2.2))
      | .inr () => ProbOracleComp.sample (
          (fun result => (back.reply result.1, cert.stateEnc result.2)) <$>
            (F.onBackdoor (back.queryDecoder.decode x.2.1.2)).run (cert.stateDecode x.2.2))
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
      (simp only [branch, wordHandle, IdealFunctionality.toProtocol, codec, WordInterface.protocol,
        WordInterface.sum, WordInterface.net, StateT.run, ProbOracleComp.lowerWith,
        ProbOracleComp.simulate_sample, ProbOracleComp.sample_map]; rfl)
  · obtain ⟨c, d, hbound⟩ := cert.growth_poly.exists_le
    refine PolyBounded.of_forall_le c d fun pair => ?_
    have hlen : pair.2.length ≤ (encPair (encPPTParam n) encBits pair).length := by
      rw [length_encPair]
      simp only [encBits_apply]
      omega
    exact (hbound pair.2).trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by omega) d))
  · intro p request s result hresult
    rcases request with ⟨ch, req⟩
    rw [wordHandle, codec.decode_enc] at hresult
    cases ch with
    | inl u =>
      cases u
      simp only [IdealFunctionality.toProtocol, codec, WordInterface.protocol, WordInterface.sum,
        WordInterface.net, StateT.run, ProbOracleComp.lowerWith, ProbOracleComp.simulate_sample,
        OracleComp.mem_supportWith_map_iff, ProbOracleComp.support_sample] at hresult
      rcases hresult with ⟨r, hr, rfl⟩
      exact cert.preserve_onInput req s r hr
    | inr u =>
      cases u
      simp only [IdealFunctionality.toProtocol, codec, WordInterface.protocol, WordInterface.sum,
        WordInterface.net, StateT.run, ProbOracleComp.lowerWith, ProbOracleComp.simulate_sample,
        OracleComp.mem_supportWith_map_iff, ProbOracleComp.support_sample] at hresult
      rcases hresult with ⟨r, hr, rfl⟩
      exact cert.preserve_onBackdoor req s r hr

end Cslib.Crypto.Protocols.UC
