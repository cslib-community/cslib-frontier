/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

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

end CslibFrontierTests.Crypto.UCWordInterface
