/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Crypto.Protocols.UC.WordInterface

/-!
# Tests for `UC.WordInterface`

Non-degenerate witnesses for `CslibFrontier.Crypto.Protocols.UC.WordInterface`:

1. `hfit` cannot be dropped: for `WordInterface.net` on `Unit / List Bool` with `encBits` and an
   oracle returning `[true, true, true]`, lowering with `limit = 2` truncates the reply and
   disagrees with the typed run, while `limit = 3` satisfies `hfit` and matches via
   `ProbOracleComp.runWith_lowerWith`.
2. `WordInterface.protocol` sum routing (`protocolSpec 2 Bool Bool Unit Bool`): queries on the
   party port and network port resolve to channels `.inl ()` and `.inr ()` respectively,
   `encodeOracle_sum` splits the sum handler across channels, `encodeOracle_eq_wordOracle` matches
   `toOracleCodec.wordOracle` on canonical requests while differing off-image, and
   `runWith_lowerWith` equates the lowered and typed joint laws against a stateful counter oracle
   with private coin sampling.
3. `WordPort.party` (`n = 2`), `WordPort.sum`, and `WordInterface.exec`: distinct party indices
   stay distinct under `WordPort.party`, round-trip cleanly, `WordInterface.exec` routes
   `execSpec 2 Bool Bool (Bool ⊕ Unit) (Bool ⊕ Bool)`, and
   `WordInterface.isOraclePPTOn_lowerWith_query` certifies a non-constant party query map.
4. Canonical-request normalizer (`WordInterface.normalizeRequests`): on a two-query word program
   issuing an off-image party request followed by a state-observing net request,
   `toOracleCodec.wordOracle` without normalization skips the first call (leaving state `0` for the
   net call) and ends in `([], [false])` at state `10`, whereas `encodeOracle` and
   `toOracleCodec.wordOracle` composed with `normalizeRequests` agree on `([true, false], [true])`
   and final state `11`; normalized programs issue only canonical requests, preserve query budgets,
   fix lowered programs, and preserve strict `IsOraclePPTOn` on a concrete off-image word adversary.
-/

namespace CslibFrontierTests.Crypto.UCWordInterface

open Cslib Cslib.Crypto.Protocols.UC Cslib.Probability Turing.MultiTapeTM

private def unitDecoder : Decoder encUnit where
  decode _ := ()
  decode_enc _ := rfl
  computable :=
    (ComputableInPolyTime.const (encIn := encBits) (encOut := encUnit) ()).exists_degree

private def bitsPort : WordPort Unit (List Bool) where
  query := encUnit
  queryDecoder := unitDecoder
  reply := encBits
  replyDecoder := Decoder.bits

private def boolPort : WordPort Bool Bool where
  query := encBool
  queryDecoder := Decoder.bool
  reply := encBool
  replyDecoder := Decoder.bool

private def unitBoolPort : WordPort Unit Bool where
  query := encUnit
  queryDecoder := unitDecoder
  reply := encBool
  replyDecoder := Decoder.bool

section TruncationWitness

private def tripleInterface : WordInterface (netSpec Unit (List Bool)) :=
  WordInterface.net bitsPort

private noncomputable def tripleOracle : (q : Unit) → StateT Unit PMF (List Bool)
  | (), s => PMF.pure ([true, true, true], s)

/-- Lowering with `limit = 2` strictly changes the joint law of `query ()` against `tripleOracle`,
showing the `hfit` hypothesis of `ProbOracleComp.runWith_lowerWith` cannot be dropped. -/
theorem runWith_lowerWith_truncation_ne :
    ProbOracleComp.runWith (tripleInterface.encodeOracle tripleOracle)
        ((ProbOracleComp.query () : ProbOracleComp (netSpec Unit (List Bool)) (List Bool)).lowerWith
          tripleInterface 2) () ≠
      ProbOracleComp.runWith tripleOracle
        (ProbOracleComp.query () : ProbOracleComp (netSpec Unit (List Bool)) (List Bool)) () := by
  intro h
  have hval := congrArg (fun p => p ([true, true, true], ())) h
  have hlhs :
      ProbOracleComp.runWith (tripleInterface.encodeOracle tripleOracle)
          ((ProbOracleComp.query () :
            ProbOracleComp (netSpec Unit (List Bool)) (List Bool)).lowerWith tripleInterface 2) ()
          ([true, true, true], ()) = 0 := by
    rw [ProbOracleComp.lowerWith, ProbOracleComp.simulate_query, WordInterface.lowerQuery,
      ProbOracleComp.runWith_map, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
      tripleInterface.encodeOracle_apply, tripleInterface.decodeQuery_request]
    simp only [tripleOracle, PMF.pure_map, Prod.map_apply, id_eq]
    have hdec :
        tripleInterface.decodeReply ()
            (List.take 2 (tripleInterface.reply () [true, true, true])) = [true, true] := rfl
    rw [hdec, PMF.pure_apply]
    simp
  have hrhs :
      ProbOracleComp.runWith tripleOracle
          (ProbOracleComp.query () : ProbOracleComp (netSpec Unit (List Bool)) (List Bool)) ()
          ([true, true, true], ()) = 1 := by
    rw [ProbOracleComp.runWith_query]
    simp [tripleOracle]
  rw [hlhs, hrhs] at hval
  exact zero_ne_one hval

/-- With `limit = 3`, every reply of `tripleOracle` fits in `limit` bits and
`ProbOracleComp.runWith_lowerWith` equates the lowered and typed runs. -/
theorem runWith_lowerWith_limit_three :
    ProbOracleComp.runWith (tripleInterface.encodeOracle tripleOracle)
        ((ProbOracleComp.query () : ProbOracleComp (netSpec Unit (List Bool)) (List Bool)).lowerWith
          tripleInterface 3) () =
      ProbOracleComp.runWith tripleOracle
        (ProbOracleComp.query () : ProbOracleComp (netSpec Unit (List Bool)) (List Bool)) () := by
  refine ProbOracleComp.runWith_lowerWith tripleInterface tripleOracle ?_ _ ()
  intro q s x hx
  simp only [tripleOracle, PMF.support_pure, Set.mem_singleton_iff] at hx
  rcases hx with rfl
  simp [tripleInterface, WordInterface.net, bitsPort, encBits]

end TruncationWitness

section ProtocolWitness

private def protoInterface : WordInterface (protocolSpec 2 Bool Bool Unit Bool) :=
  WordInterface.protocol (WordPort.party (n := 2) boolPort) unitBoolPort

theorem protoInterface_channel_party_zero :
    protoInterface.channel (Sum.inl ((0 : Fin 2), true)) = Sum.inl () := rfl

theorem protoInterface_channel_party_one :
    protoInterface.channel (Sum.inl ((1 : Fin 2), false)) = Sum.inl () := rfl

theorem protoInterface_channel_net :
    protoInterface.channel (Sum.inr ()) = Sum.inr () := rfl

private noncomputable def counterPartyOracle :
    (q : Fin 2 × Bool) → StateT ℕ PMF (partySpec 2 Bool Bool q)
  | (i, b), k => PMF.pure (some (b ^^ (i == 1) ^^ decide (k % 2 = 1)), k + 1)

private noncomputable def counterNetOracle :
    (q : Unit) → StateT ℕ PMF (netSpec Unit Bool q)
  | (), k => PMF.pure (decide (0 < k), k + 10)

private noncomputable abbrev counterOracle :
    (q : (Fin 2 × Bool) ⊕ Unit) → StateT ℕ PMF (protocolSpec 2 Bool Bool Unit Bool q) :=
  OracleComp.sumHandler counterPartyOracle counterNetOracle

private def protoProgram :
    ProbOracleComp (protocolSpec 2 Bool Bool Unit Bool) (Option Bool × Bool) := do
  let r₁ ← ProbOracleComp.query (Sum.inl ((1 : Fin 2), true))
  let r₂ ← ProbOracleComp.query (Sum.inr ())
  return (r₁, r₂)

private theorem counterOracle_reply_length_le :
    ∀ (q : (Fin 2 × Bool) ⊕ Unit) (k : ℕ)
      (x : protocolSpec 2 Bool Bool Unit Bool q × ℕ),
      x ∈ (counterOracle q k).support → (protoInterface.reply q x.1).length ≤ 2 := by
  rintro (⟨i, b⟩ | ⟨⟩) k ⟨r, k'⟩ hx
  · simp only [counterOracle, OracleComp.sumHandler, counterPartyOracle,
      PMF.support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨rfl, rfl⟩
    simp [protoInterface, WordInterface.sum, WordInterface.net, WordPort.party, boolPort]
  · simp only [counterOracle, OracleComp.sumHandler, counterNetOracle,
      PMF.support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨rfl, rfl⟩
    simp [protoInterface, WordInterface.sum, WordInterface.net, unitBoolPort]

/-- `encodeOracle_sum` splits `protoInterface.encodeOracle` across the party and net channels. -/
theorem protoInterface_encodeOracle_sum :
    protoInterface.encodeOracle counterOracle =
      fun cw => Sum.elim
        (fun c₁ => (WordInterface.net (WordPort.party (n := 2) boolPort)).encodeOracle
          counterPartyOracle (c₁, cw.2))
        (fun c₂ => (WordInterface.net unitBoolPort).encodeOracle counterNetOracle (c₂, cw.2))
        cw.1 :=
  WordInterface.encodeOracle_sum _ _ counterPartyOracle counterNetOracle

/-- On canonical requests `toOracleCodec.wordOracle` agrees with `encodeOracle`, whereas on an
off-image request (here `[]` on the party channel, which decodes to `(0, false)` whose canonical
encoding is `[false, false]`) `toOracleCodec.wordOracle` returns `[]` without calling the oracle,
while `encodeOracle` normalizes to `[false, false]` and delegates to `toOracleCodec.wordOracle`,
calling `counterOracle` once on `(0, false)`. -/
theorem protoInterface_wordOracle_offImage_ne :
    protoInterface.toOracleCodec.wordOracle counterOracle (Sum.inl (), []) 0 ≠
      protoInterface.encodeOracle counterOracle (Sum.inl (), []) 0 := by
  have hdec :
      protoInterface.toOracleCodec.decodeQuery (Sum.inl (), []) = none := by
    decide
  have hword :
      protoInterface.toOracleCodec.wordOracle counterOracle (Sum.inl (), []) 0 =
        PMF.pure ([], 0) := by
    rw [OracleCodec.wordOracle_of_decodeQuery_eq_none (c := protoInterface.toOracleCodec)
      counterOracle hdec]
    rfl
  have hdecq : protoInterface.decodeQuery (Sum.inl ()) [] = Sum.inl ((0 : Fin 2), false) := rfl
  have henc :
      protoInterface.encodeOracle counterOracle (Sum.inl (), []) 0 =
        PMF.pure ([true, false], 1) := by
    rw [protoInterface.encodeOracle_apply counterOracle (Sum.inl ()) [] 0, hdecq]
    simp [counterOracle, OracleComp.sumHandler, counterPartyOracle, protoInterface,
      WordInterface.sum, WordInterface.net, WordPort.party, boolPort]
  intro h
  rw [hword, henc] at h
  have hval := congrArg (fun p => p ([], 0)) h
  simp only [PMF.pure_apply, Prod.mk.injEq] at hval
  simp at hval

/-- Lowering `protoProgram` with `limit = 2` matches the typed run against the stateful
`counterOracle` and reaches the non-trivial final counter state `11`. -/
theorem runWith_lowerWith_protoProgram :
    ProbOracleComp.runWith (protoInterface.encodeOracle counterOracle)
        (protoProgram.lowerWith protoInterface 2) 0 =
      PMF.pure ((some false, true), 11) := by
  rw [ProbOracleComp.runWith_lowerWith protoInterface counterOracle counterOracle_reply_length_le]
  rw [protoProgram, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query]
  simp only [counterOracle, OracleComp.sumHandler, counterPartyOracle, counterNetOracle,
    PMF.pure_bind, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
    ProbOracleComp.runWith_pure]
  rfl

end ProtocolWitness

section PartyAndExecWitness

private def partyTwoPort : WordPort (Fin 2 × Bool) (Option Bool) :=
  WordPort.party (n := 2) boolPort

theorem partyTwoPort_distinct_parties :
    partyTwoPort.query ((0 : Fin 2), true) ≠ partyTwoPort.query ((1 : Fin 2), true) := by
  decide

theorem partyTwoPort_roundtrip_one :
    partyTwoPort.queryDecoder.decode (partyTwoPort.query ((1 : Fin 2), true)) =
      ((1 : Fin 2), true) :=
  partyTwoPort.queryDecoder.decode_enc _

/-- Non-constant party/net query map driven by `Bool × Bool`, varying both the channel and
party index, certified uniform strict oracle PPT by `WordInterface.isOraclePPTOn_lowerWith_query`.
-/
theorem protoInterface_isOraclePPTOn_partyQuery :
    IsOraclePPTOn (encPair encBool encBool) encBits
      (fun a : Bool × Bool =>
        let q : (Fin 2 × Bool) ⊕ Unit :=
          if a.1 then Sum.inl (⟨if a.2 then 1 else 0, by split_ifs <;> decide⟩, a.2)
          else Sum.inr ()
        protoInterface.reply q <$>
          ProbOracleComp.lowerWith protoInterface 2 (ProbOracleComp.query q)) := by
  let q : Bool × Bool → (Fin 2 × Bool) ⊕ Unit :=
    fun a =>
      if a.1 then Sum.inl (⟨if a.2 then 1 else 0, by split_ifs <;> decide⟩, a.2)
      else Sum.inr ()
  have hchannel :
      ComputableInPolyTime (fun a => protoInterface.channel (q a))
        (encPair encBool encBool) (encFinite protoInterface.Channel) :=
    ComputableInPolyTime.of_finite _
  have hrequest :
      ComputableInPolyTime (fun a => protoInterface.request (q a))
        (encPair encBool encBool) encBits :=
    ComputableInPolyTime.of_finite _
  have hlimit :
      ComputableInPolyTime (fun _ : Bool × Bool => 2) (encPair encBool encBool) encUnary :=
    ComputableInPolyTime.const 2
  exact protoInterface.isOraclePPTOn_lowerWith_query hchannel hrequest hlimit

private def execInterface : WordInterface (execSpec 2 Bool Bool (Bool ⊕ Unit) (Bool ⊕ Bool)) :=
  WordInterface.exec partyTwoPort (WordPort.sum boolPort unitBoolPort)

theorem execInterface_channel_adv :
    execInterface.channel (Sum.inr (Sum.inl false)) = Sum.inr () := rfl

private noncomputable def coinExecOracle :
    (q : (Fin 2 × Bool) ⊕ (Bool ⊕ Unit)) →
      StateT ℕ PMF (execSpec 2 Bool Bool (Bool ⊕ Unit) (Bool ⊕ Bool) q)
  | Sum.inl (i, b), k => PMF.pure (some (b ^^ (i == 0)), k + 1)
  | Sum.inr (Sum.inl b), k => PMF.pure (Sum.inl (!b), k + 2)
  | Sum.inr (Sum.inr ()), k => PMF.pure (Sum.inr (decide (0 < k)), k + 3)

private def execProgram :
    ProbOracleComp (execSpec 2 Bool Bool (Bool ⊕ Unit) (Bool ⊕ Bool)) (Option Bool × Bool) := do
  let c ← ProbOracleComp.sample (ProbComp.unifFin 1)
  let r₁ ← ProbOracleComp.query (Sum.inl ((0 : Fin 2), decide (c = 0)))
  let r₂ ← ProbOracleComp.query (Sum.inr (Sum.inr ()))
  match r₂ with
  | Sum.inl b => return (r₁, b)
  | Sum.inr b => return (r₁, b)

theorem runWith_lowerWith_execProgram :
    ProbOracleComp.runWith (execInterface.encodeOracle coinExecOracle)
        (execProgram.lowerWith execInterface 3) 0 =
      ProbOracleComp.runWith coinExecOracle execProgram 0 := by
  refine ProbOracleComp.runWith_lowerWith execInterface coinExecOracle ?_ _ 0
  rintro (⟨i, b⟩ | b | ⟨⟩) k ⟨r, k'⟩ hx <;>
  · simp only [coinExecOracle, PMF.support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨rfl, rfl⟩
    simp [execInterface, WordInterface.sum, WordInterface.net, partyTwoPort, WordPort.party,
      WordPort.sum, boolPort, unitBoolPort]

end PartyAndExecWitness

section NormalizeRequestsWitness

private def offImageProg :
    WordOracleComp protoInterface.Channel (List Bool × List Bool) := do
  let r₁ ← ProbOracleComp.query
    (spec := fun _ : protoInterface.Channel × List Bool => List Bool) (Sum.inl (), [])
  let r₂ ← ProbOracleComp.query
    (spec := fun _ : protoInterface.Channel × List Bool => List Bool) (Sum.inr (), [])
  return (r₁, r₂)

private theorem protoInterface_net_wordOracle_eq_encode (k : ℕ) :
    protoInterface.toOracleCodec.wordOracle counterOracle (Sum.inr (), []) k =
      protoInterface.encodeOracle counterOracle (Sum.inr (), []) k :=
  congrFun (protoInterface.encodeOracle_eq_wordOracle counterOracle (Sum.inr ())).symm k

/-- Without normalization, the strict `toOracleCodec.wordOracle` ignores the off-image party
request `(Sum.inl (), [])` without mutating state, so the subsequent net call sees `k = 0` and
returns `[false]` with final state `10`. -/
theorem protoInterface_wordOracle_offImageProg_eval :
    ProbOracleComp.runWith (protoInterface.toOracleCodec.wordOracle counterOracle)
        offImageProg 0 =
      PMF.pure (([], [false]), 10) := by
  have hdec : protoInterface.toOracleCodec.decodeQuery (Sum.inl (), []) = none := by decide
  have hword₁ :
      protoInterface.toOracleCodec.wordOracle counterOracle (Sum.inl (), []) 0 =
        PMF.pure ([], 0) := by
    rw [OracleCodec.wordOracle_of_decodeQuery_eq_none (c := protoInterface.toOracleCodec)
      counterOracle hdec]
    rfl
  have hword₂ :
      protoInterface.toOracleCodec.wordOracle counterOracle (Sum.inr (), []) 0 =
        PMF.pure ([false], 10) := by
    rw [protoInterface_net_wordOracle_eq_encode,
      protoInterface.encodeOracle_apply counterOracle (Sum.inr ()) [] 0]
    have hdecq : protoInterface.decodeQuery (Sum.inr ()) [] = Sum.inr () := rfl
    rw [hdecq]
    simp [counterOracle, OracleComp.sumHandler, counterNetOracle, protoInterface,
      WordInterface.sum, WordInterface.net, unitBoolPort]
  rw [offImageProg, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query, hword₁,
    PMF.pure_bind, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query, hword₂,
    PMF.pure_bind, ProbOracleComp.runWith_pure]

/-- Against `encodeOracle`, the off-image party request `(Sum.inl (), [])` is normalized to
`(0, false)`, returning `[true, false]` and incrementing the counter to `1`, so the net call
observes `0 < 1` and returns `[true]` with final state `11`. -/
theorem protoInterface_encodeOracle_offImageProg_eval :
    ProbOracleComp.runWith (protoInterface.encodeOracle counterOracle) offImageProg 0 =
      PMF.pure (([true, false], [true]), 11) := by
  have henc₁ :
      protoInterface.encodeOracle counterOracle (Sum.inl (), []) 0 =
        PMF.pure ([true, false], 1) := by
    rw [protoInterface.encodeOracle_apply counterOracle (Sum.inl ()) [] 0]
    have hdecq : protoInterface.decodeQuery (Sum.inl ()) [] = Sum.inl ((0 : Fin 2), false) := rfl
    rw [hdecq]
    simp [counterOracle, OracleComp.sumHandler, counterPartyOracle, protoInterface,
      WordInterface.sum, WordInterface.net, WordPort.party, boolPort]
  have henc₂ :
      protoInterface.encodeOracle counterOracle (Sum.inr (), []) 1 =
        PMF.pure ([true], 11) := by
    rw [protoInterface.encodeOracle_apply counterOracle (Sum.inr ()) [] 1]
    have hdecq : protoInterface.decodeQuery (Sum.inr ()) [] = Sum.inr () := rfl
    rw [hdecq]
    simp [counterOracle, OracleComp.sumHandler, counterNetOracle, protoInterface,
      WordInterface.sum, WordInterface.net, unitBoolPort]
  rw [offImageProg, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query, henc₁,
    PMF.pure_bind, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query, henc₂,
    PMF.pure_bind, ProbOracleComp.runWith_pure]

/-- Composing `offImageProg` with `WordInterface.normalizeRequests` makes
`toOracleCodec.wordOracle` (which leaves oracle state unchanged on off-image requests) reproduce
the exact joint output and state `(([true, false], [true]), 11)` of `encodeOracle`. -/
theorem protoInterface_wordOracle_normalizeRequests_offImageProg_eval :
    ProbOracleComp.runWith (protoInterface.toOracleCodec.wordOracle counterOracle)
        (protoInterface.normalizeRequests offImageProg) 0 =
      PMF.pure (([true, false], [true]), 11) := by
  rw [← protoInterface.runWith_encodeOracle_eq_wordOracle_normalizeRequests counterOracle
    offImageProg 0]
  exact protoInterface_encodeOracle_offImageProg_eval

theorem protoInterface_normalizeRequests_offImageProg_queriesSatisfy :
    (protoInterface.normalizeRequests offImageProg).QueriesSatisfy
      (fun cw => ∃ q, cw = (protoInterface.channel q, protoInterface.request q)) :=
  protoInterface.queriesSatisfy_normalizeRequests offImageProg

theorem protoInterface_normalizeRequests_offImageProg_idempotent :
    protoInterface.normalizeRequests (protoInterface.normalizeRequests offImageProg) =
      protoInterface.normalizeRequests offImageProg := by
  simp

theorem protoInterface_normalizeRequests_offImageProg_isQueryBounded :
    (protoInterface.normalizeRequests offImageProg).IsQueryBounded 2 := by
  refine protoInterface.isQueryBounded_normalizeRequests ?_
  have h1 : (ProbOracleComp.query (spec := fun _ : protoInterface.Channel × List Bool => List Bool)
      (Sum.inl (), [])).IsQueryBounded 1 :=
    ProbOracleComp.IsQueryBounded.query _
  have h2 : ∀ r₁ : List Bool,
      (do
        let r₂ ← ProbOracleComp.query
          (spec := fun _ : protoInterface.Channel × List Bool => List Bool) (Sum.inr (), [])
        return (r₁, r₂)).IsQueryBounded 1 := fun r₁ =>
    (ProbOracleComp.IsQueryBounded.query _).bind fun r₂ =>
      OracleComp.IsCostBounded.pure (r₁, r₂) 0
  simpa only [offImageProg] using h1.bind h2

theorem protoInterface_normalizeRequests_lowerWith_protoProgram :
    protoInterface.normalizeRequests (protoProgram.lowerWith protoInterface 2) =
      protoProgram.lowerWith protoInterface 2 := by
  simp

/-- `WordInterface.isOraclePPTOn_normalizeRequests` preserves strict uniform oracle PPT on a
concrete adversary issuing off-image party queries (`[]` and `[true]`) without needing an external
reply-length hypothesis. -/
theorem protoInterface_isOraclePPTOn_normalizeRequests_offImage :
    IsOraclePPTOn encBool encBits
      (fun b : Bool =>
        protoInterface.normalizeRequests
          (List.take 2 <$>
            ProbOracleComp.query (spec := fun _ : protoInterface.Channel × List Bool => List Bool)
              (Sum.inl (), if b then [] else [true]))) := by
  refine protoInterface.isOraclePPTOn_normalizeRequests ?_
  exact IsOraclePPTOn.query_take (op := (Sum.inl () : protoInterface.Channel))
    (ComputableInPolyTime.of_finite _) (ComputableInPolyTime.const 2)

/-- Bare `simp` exercises all five structural `@[simp]` rules (`normalizeRequests_bind`,
`normalizeRequests_sample`, `normalizeRequests_map`, `normalizeRequests_query`, and
`normalizeRequests_pure`) symbolically over an arbitrary `WordInterface`. -/
example {ι : Type} {E : ι → Type} (I : WordInterface E) (c : I.Channel) (w : List Bool) :
    I.normalizeRequests
        (do
          let b ← ProbOracleComp.sample (ProbComp.uniform Bool)
          let r ← List.length <$>
            ProbOracleComp.query (spec := fun _ : I.Channel × List Bool => List Bool) (c, b :: w)
          pure r) =
      (do
        let b ← ProbOracleComp.sample (ProbComp.uniform Bool)
        let r ← List.length <$>
          ProbOracleComp.query (spec := fun _ : I.Channel × List Bool => List Bool)
            (c, I.requestNormalize c (b :: w))
        pure r) := by
  simp

end NormalizeRequestsWitness

end CslibFrontierTests.Crypto.UCWordInterface
