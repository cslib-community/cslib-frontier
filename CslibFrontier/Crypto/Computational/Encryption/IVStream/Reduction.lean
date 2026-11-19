/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.BlockModeWord
public import CslibFrontier.Crypto.Computational.Encryption.IVStream
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Frame
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Foundations.Data.BitString.List.Operations
import CslibFrontier.Languages.Probabilistic.Oracle.Support
import CslibFrontier.Languages.Probabilistic.QueryCount.Congr
import CslibFrontier.Probability.BitString
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# The PRF reduction for random-IV modes

A random-IV mode encrypts as the envelope `ivModeEncrypt body` of `IVStream.lean`: it draws a
uniform `n`-bit initial value `iv` and outputs `iv` followed by a body computed from the key,
`iv` and the message. Randomized counter mode and output feedback mode are the stream case, whose
body XORs the message with a keystream. The reduction of the proof of [BonehShoup2023],
Theorem 5.3, written there for counter mode, works for any such mode built from a pseudorandom
function: the PRF distinguisher runs the CPA adversary and answers each admissible left-or-right
request itself, drawing the initial value and computing the body with queries to its own function
oracle. The modes differ only in the program `bodyQueries n iv msg` that computes the body of
message `msg` from initial value `iv`; the program may depend on the message, as CBC mode's does.
`ivModeToPrfDistinguisher bodyQueries` is the reduction for any such program.

1. The distinguisher is uniform strict oracle PPT whenever the adversary is, `bodyQueries` is
   strict oracle PPT on `(1ⁿ, iv, msg)` and no output of `bodyQueries` is longer than the message
   (`isOraclePPT_ivModeToPrfDistinguisher`).
2. Against the keyed oracle, if the body queries compute `body n k iv msg` from every `n`-bit
   initial value on whole-block messages, its output law is that of the adversary in the CPA game
   of `ivModeEncrypt body` (`eval_prfRealGame_ivModeToPrfDistinguisher`).
3. Against a uniform random function, if the body queries compute the bits of the blocks that a
   typed per-query program computes, it is that program simulated on the adversary read as a
   block-mode adversary (`blockModeWordAdversary`)
   (`eval_prfIdealGame_ivModeToPrfDistinguisher`). The typed collision bounds of each mode then
   apply.

The stream case `ivStreamToPrfDistinguisher keystreamQueries` takes a program
`keystreamQueries n iv blocks` that obtains the keystream of `blocks` blocks; its three results
(`isOraclePPT_ivStreamToPrfDistinguisher`, `eval_prfRealGame_ivStreamToPrfDistinguisher`,
`eval_prfIdealGame_ivStreamToPrfDistinguisher`) are instances of the three above.

## Main definitions

* `Cslib.Crypto.ivModeToPrfDistinguisher`: the PRF distinguisher built from a CPA adversary.
* `Cslib.Crypto.ivStreamToPrfDistinguisher`: the stream case, for keystream queries.

## Main results

* `Cslib.Crypto.isOraclePPT_ivModeToPrfDistinguisher`,
  `Cslib.Crypto.isOraclePPT_ivModeToPrfDistinguisher_blockLen`,
  `Cslib.Crypto.isOraclePPT_ivStreamToPrfDistinguisher`: the reduction is uniform strict oracle
  PPT.
* `Cslib.Crypto.eval_prfRealGame_ivModeToPrfDistinguisher`,
  `Cslib.Crypto.eval_prfRealGame_ivStreamToPrfDistinguisher`: the real PRF game of the reduction
  is the CPA game.
* `Cslib.Crypto.eval_prfIdealGame_ivModeToPrfDistinguisher`,
  `Cslib.Crypto.eval_prfIdealGame_ivStreamToPrfDistinguisher`: the ideal PRF game of the reduction
  is a typed block-mode reduction against a random function.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Theorem 5.3 (printed p. 191).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-- The reduction's answer to one left-or-right request, for a program `bodyQueries n iv msg` that
computes the body of `msg` from initial value `iv` with queries to the function oracle
([BonehShoup2023], proof of Theorem 5.3): on an admissible pair, draw a uniform `n`-bit initial
value and output it followed by the body of the message selected by `bit`; answer inadmissible
requests with `[]` and no query. -/
private noncomputable def ivModePrfHandler
    (bodyQueries : ℕ → List Bool → List Bool → WordOracleComp Unit (List Bool)) (n : ℕ)
    (bit : Bool) (request : Unit × List Bool) : WordOracleComp Unit (List Bool) :=
  let m0 := unframe request.2
  let m1 := dropFrame request.2
  if blockPairValid n m0 m1 then do
    let iv ← ProbOracleComp.sample (BitString.sampleList n)
    (iv ++ ·) <$> bodyQueries n iv (if bit then m1 else m0)
  else
    pure []

/-- The PRF distinguisher built from a left-or-right CPA adversary against a random-IV mode with
body queries `bodyQueries` ([BonehShoup2023], proof of Theorem 5.3): run the adversary and answer
every request itself. On an admissible pair it draws a uniform `n`-bit initial value and answers
with that value followed by the body that `bodyQueries` computes, with queries to the function
oracle, for the message selected by `bit`; it answers an inadmissible request with `[]` and no
query. -/
noncomputable def ivModeToPrfDistinguisher
    (bodyQueries : ℕ → List Bool → List Bool → WordOracleComp Unit (List Bool))
    (adversary : OracleDistinguisher) (bit : Bool) : OracleDistinguisher :=
  fun n _ => ProbOracleComp.simulate (ivModePrfHandler bodyQueries n bit) (adversary n [])

/-! ### Efficiency -/

/-- The handler is uniformly strict oracle PPT in the parameter, the auxiliary word and the
request. -/
private theorem isOraclePPTOn_ivModePrfHandler
    {bodyQueries : ℕ → List Bool → List Bool → WordOracleComp Unit (List Bool)}
    (hbody : IsOraclePPTOn (encPair encUnary (encPair encBits encBits)) encBits
      (fun ((n, iv, msg) : ℕ × List Bool × List Bool) => bodyQueries n iv msg))
    (bit : Bool) :
    IsOraclePPTOn (encPair (encPair encUnary encBits) (encPair (encFinEnum Unit) encBits)) encBits
      (fun pair : (ℕ × List Bool) × (Unit × List Bool) =>
        ivModePrfHandler bodyQueries pair.1.1 bit pair.2) := by
  let E := encPair (encPair encUnary encBits) (encPair (encFinEnum Unit) encBits)
  let EIv := encPair E encBits
  have hn : ComputableInPolyTime (fun p : (ℕ × List Bool) × (Unit × List Bool) => p.1.1)
      E encUnary := by dsimp only [E]; fun_prop
  have hm0 : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × (Unit × List Bool) => unframe p.2.2) E encBits :=
    ComputableInPolyTime.unframe.comp (by dsimp only [E]; fun_prop)
  have hm1 : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × (Unit × List Bool) => dropFrame p.2.2) E encBits :=
    ComputableInPolyTime.dropFrame.comp (by dsimp only [E]; fun_prop)
  have hcond : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × (Unit × List Bool) =>
        blockPairValid p.1.1 (unframe p.2.2) (dropFrame p.2.2)) E encBool := by
    unfold blockPairValid; fun_prop
  have hmsg : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × (Unit × List Bool) =>
        if bit then dropFrame p.2.2 else unframe p.2.2) E encBits := by
    cases bit
    · exact hm0
    · exact hm1
  have hbodyIv : IsOraclePPTOn (Operation := Unit) EIv encBits
      (fun q : ((ℕ × List Bool) × (Unit × List Bool)) × List Bool =>
        bodyQueries q.1.1.1 q.2 (if bit then dropFrame q.1.2.2 else unframe q.1.2.2)) :=
    hbody.preprocess ((hn.comp (ComputableInPolyTime.fst _ _)).prod
      ((ComputableInPolyTime.snd _ _).prod (hmsg.comp (ComputableInPolyTime.fst _ _))))
  have hyes : IsOraclePPTOn (Operation := Unit) EIv encBits
      (fun q : ((ℕ × List Bool) × (Unit × List Bool)) × List Bool =>
        (q.2 ++ ·) <$>
          bodyQueries q.1.1.1 q.2 (if bit then dropFrame q.1.2.2 else unframe q.1.2.2)) :=
    hbodyIv.map_with (f := fun q body => q.2 ++ body)
      (ComputableInPolyTime.bitsAppend (by dsimp only [EIv]; fun_prop)
        (ComputableInPolyTime.snd _ _))
  unfold ivModePrfHandler
  exact IsOraclePPTOn.cond hcond
    (IsOraclePPTOn.bind_with ((isPPTOn_sampleList.preprocess hn).isOraclePPTOn) hyes)
    (ComputableInPolyTime.isOraclePPTOn (ComputableInPolyTime.const []))

/-- If no output of the body queries is longer than the message, every answer of the handler has
at most `n` bits more than the request. -/
private theorem length_le_of_mem_support_ivModePrfHandler
    {bodyQueries : ℕ → List Bool → List Bool → WordOracleComp Unit (List Bool)}
    (hbodyLen : ∀ n iv msg reply, reply ∈ OracleComp.support (bodyQueries n iv msg) →
      reply.length ≤ msg.length)
    {n : ℕ} {bit : Bool} {request : Unit × List Bool} {reply : List Bool}
    (hreply : reply ∈ OracleComp.support (ivModePrfHandler bodyQueries n bit request)) :
    reply.length ≤ n + request.2.length := by
  unfold ivModePrfHandler at hreply
  dsimp only at hreply
  split at hreply
  · obtain ⟨iv, hiv, hreply⟩ := OracleComp.mem_supportWith_bind_iff.mp hreply
    change iv ∈ OracleComp.support (ProbOracleComp.sample (BitString.sampleList n)) at hiv
    rw [ProbOracleComp.support_sample, BitString.eval_sampleList] at hiv
    have hivLen : iv.length = n := BitString.length_of_mem_support_uniformList hiv
    obtain ⟨body, hbody, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hreply
    have hmsg : (if bit then dropFrame request.2 else unframe request.2).length ≤
        request.2.length := by
      cases bit
      · exact length_unframe_le _
      · exact length_dropFrame_le _
    have hbodyLe := hbodyLen _ _ _ _ hbody
    simp only [List.length_append, hivLen]
    omega
  · have hreplyEq := OracleComp.eq_of_mem_supportWith_pure hreply
    subst hreplyEq
    simp

/-- **Efficiency of the reduction at a reindexed block length.** When `blockLen` is computable in
polynomial time in unary, running `ivModeToPrfDistinguisher` at block width `blockLen n` on
`adversary n []` is uniform strict oracle PPT whenever `adversary` is. -/
theorem isOraclePPT_ivModeToPrfDistinguisher_blockLen
    {blockLen : ℕ → ℕ} (hblock : ComputableInPolyTime blockLen encUnary encUnary)
    {bodyQueries : ℕ → List Bool → List Bool → WordOracleComp Unit (List Bool)}
    (hbody : IsOraclePPTOn (encPair encUnary (encPair encBits encBits)) encBits
      (fun ((n, iv, msg) : ℕ × List Bool × List Bool) => bodyQueries n iv msg))
    (hbodyLen : ∀ n iv msg reply, reply ∈ OracleComp.support (bodyQueries n iv msg) →
      reply.length ≤ msg.length)
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsOraclePPT encBool fun n aux =>
      ivModeToPrfDistinguisher bodyQueries (fun _ _ => adversary n []) bit (blockLen n) aux := by
  let ECaller := encPair encUnary encBits
  let EReq := encPair (encFinEnum Unit) encBits
  have hprepHandler : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × (Unit × List Bool) => ((blockLen p.1.1, p.1.2), p.2))
      (encPair ECaller EReq) (encPair ECaller EReq) :=
    (((hblock.comp (by dsimp only [ECaller]; fun_prop)).prod
      (by dsimp only [ECaller]; fun_prop)).comp (ComputableInPolyTime.fst _ _)).prod
      (ComputableInPolyTime.snd _ _)
  have hres : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List Bool => blockLen p.1.1 + p.2.length)
      (encPair ECaller encBits) encUnary :=
    ComputableInPolyTime.unary_add'
      (hblock.comp ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _)))
      (ComputableInPolyTime.length_bits.comp (ComputableInPolyTime.snd _ _))
  change IsOraclePPTOn ECaller encBool
    (fun caller : ℕ × List Bool => ProbOracleComp.simulate
      (ivModePrfHandler bodyQueries (blockLen caller.1) bit) (adversary caller.1 []))
  simp only [ProbOracleComp.simulate, OracleComp.substitute_eq_interpret]
  exact IsOraclePPTOn.interpret_preprocess_open' (operationEncoding := encFinEnum Unit)
    (handler := fun caller : ℕ × List Bool => ivModePrfHandler bodyQueries (blockLen caller.1) bit)
    (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
    (resources := fun caller request => blockLen caller.1 + request.length)
    hadversary (by dsimp only [ECaller]; fun_prop)
    ((isOraclePPTOn_ivModePrfHandler hbody bit).preprocess hprepHandler) hres
    fun _ _ _ hreply => length_le_of_mem_support_ivModePrfHandler hbodyLen hreply

/-- **Efficiency of the reduction.** If the body queries are strict oracle PPT on
`(1ⁿ, iv, msg)` and none of their outputs is longer than the message, then for every uniform
strict oracle-PPT adversary, `ivModeToPrfDistinguisher bodyQueries adversary bit` is uniform
strict oracle PPT. The length condition is sufficient, not necessary: a mode whose body is longer
than the message is not covered. -/
theorem isOraclePPT_ivModeToPrfDistinguisher
    {bodyQueries : ℕ → List Bool → List Bool → WordOracleComp Unit (List Bool)}
    (hbody : IsOraclePPTOn (encPair encUnary (encPair encBits encBits)) encBits
      (fun ((n, iv, msg) : ℕ × List Bool × List Bool) => bodyQueries n iv msg))
    (hbodyLen : ∀ n iv msg reply, reply ∈ OracleComp.support (bodyQueries n iv msg) →
      reply.length ≤ msg.length)
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsOraclePPT encBool (ivModeToPrfDistinguisher bodyQueries adversary bit) :=
  isOraclePPT_ivModeToPrfDistinguisher_blockLen ComputableInPolyTime.id' hbody hbodyLen
    hadversary bit

/-! ### The real game -/

/-- The message that an admissible pair selects has whole blocks. -/
private theorem length_select_mod_of_blockPairValid {n : ℕ} {m₀ m₁ : List Bool}
    (hvalid : blockPairValid n m₀ m₁ = true) (bit : Bool) :
    (if bit then m₁ else m₀).length % n = 0 := by
  simp only [blockPairValid, Bool.and_eq_true, beq_iff_eq] at hvalid
  obtain ⟨hlenEq, hmod⟩ := hvalid
  cases bit
  · exact hmod
  · simp [← hlenEq, hmod]

/-- Under a key `k`, if the body queries answered by the keyed oracle compute `body n k iv msg`
from every `n`-bit initial value `iv` on whole-block messages, the handler answers each request
with the law of the CPA oracle of `ivModeEncrypt body`. -/
private theorem eval_run_ivModePrfHandler
    {bodyQueries : ℕ → List Bool → List Bool → WordOracleComp Unit (List Bool)}
    {body : ℕ → List Bool → List Bool → List Bool → List Bool}
    {family : List Bool → List Bool → List Bool} {n : ℕ} {k : List Bool}
    (hbody : ∀ iv : List Bool, iv.length = n → ∀ msg : List Bool, msg.length % n = 0 →
      (bodyQueries n iv msg).run (fun request => pure (prfOracle family n k request.2)) =
        pure (body n k iv msg))
    (bit : Bool) (request : Unit × List Bool) :
    ProbComp.eval ((ivModePrfHandler bodyQueries n bit request).run
        fun request => pure (prfOracle family n k request.2)) =
      ProbComp.eval
        (symmetricCPAReplyOn blockPairValid (ivModeEncrypt body) n k bit request) := by
  unfold ivModePrfHandler symmetricCPAReplyOn
  dsimp only
  by_cases hvalid : blockPairValid n (unframe request.2) (dropFrame request.2) = true
  · have hmod := length_select_mod_of_blockPairValid hvalid bit
    simp only [hvalid, ↓reduceIte, ProbOracleComp.run_bind, ProbOracleComp.run_sample,
      ProbOracleComp.run_map, ivModeEncrypt, ProbComp.eval_bind, ProbComp.eval_map,
      ProbComp.eval_pure, BitString.eval_sampleList]
    refine PMF.bind_congr_on_support _ _ _ fun iv hiv => ?_
    rw [hbody iv (BitString.length_of_mem_support_uniformList hiv) _ hmod, ProbComp.eval_pure,
      PMF.pure_map]
  · simp [hvalid]

/-- **Real game.** If, under every key of length `n`, the body queries answered by the keyed
oracle compute `body n k iv msg` from every `n`-bit initial value `iv` on every whole-block
message `msg`, then against the keyed oracle `ivModeToPrfDistinguisher bodyQueries adversary bit`
has the output law of `adversary` in the CPA game of `ivModeEncrypt body` with challenge bit
`bit`. -/
theorem eval_prfRealGame_ivModeToPrfDistinguisher
    {bodyQueries : ℕ → List Bool → List Bool → WordOracleComp Unit (List Bool)}
    {body : ℕ → List Bool → List Bool → List Bool → List Bool}
    {family : List Bool → List Bool → List Bool} {n : ℕ}
    (hbody : ∀ k : List Bool, k.length = n → ∀ iv : List Bool, iv.length = n →
      ∀ msg : List Bool, msg.length % n = 0 →
        (bodyQueries n iv msg).run (fun request => pure (prfOracle family n k request.2)) =
          pure (body n k iv msg))
    (adversary : OracleDistinguisher) (bit : Bool) :
    ProbComp.eval (prfRealGame id family (ivModeToPrfDistinguisher bodyQueries adversary bit) n) =
      ProbComp.eval (symmetricCPAGameOn blockPairValid BitString.sampleList
        (ivModeEncrypt body) adversary bit n) := by
  simp only [prfRealGame, id_eq, symmetricCPAGameOn, ivModeToPrfDistinguisher,
    ProbOracleComp.run_simulate, ProbComp.eval_bind, BitString.eval_sampleList]
  refine PMF.bind_congr_on_support _ _ _ fun k hk => ?_
  have hkLen : k.length = n := BitString.length_of_mem_support_uniformList hk
  exact (ProbOracleComp.QueriesSatisfy.of_forall (p := fun _ => True) (fun _ => trivial)
    (adversary n [])).eval_run_congr fun request _ =>
      eval_run_ivModePrfHandler (hbody k hkLen) bit request

/-! ### The ideal game -/

/-- Against a fixed function `f`, suppose the typed program `program q` answers each block-mode
query as the block-mode oracle of `bodyBlocks` does, and the body queries from the bits of `iv`
on a whole-block message compute the bits of the blocks that `bodyBlocks` computes. Then the
handler answers a request whose left message has at most `ℓ` blocks as `program` answers its block
query. -/
private theorem eval_run_ivModePrfHandler_randomFunction
    {bodyQueries : ℕ → List Bool → List Bool → WordOracleComp Unit (List Bool)} {n ℓ : ℕ}
    {bit : Bool}
    {program : BlockModeQuery n →
      ProbOracleComp (fun _ : BitString n => BitString n) (BitString n × List (BitString n))}
    {f : BitString n → BitString n}
    {bodyBlocks : BitString n → List (BitString n) → List (BitString n)}
    (hprogram : ∀ q, (program q).run (fun x => pure (f x)) = blockModeOracle bodyBlocks ℓ bit q)
    (hword : ∀ iv m, m.length % n = 0 → (bodyQueries n (List.ofFn iv) m).run
        (fun request => pure (randomFunctionOracle n f request.2)) =
          pure ((bodyBlocks iv (BitString.padBlocks n m.length m)).flatMap List.ofFn))
    (request : Unit × List Bool) (hℓ : (unframe request.2).length / n ≤ ℓ) :
    ProbComp.eval ((ivModePrfHandler bodyQueries n bit request).run
        fun r => pure (randomFunctionOracle n f r.2)) =
      ProbComp.eval ((blockModeWordQuery n request).run
        fun q => (program q).run fun x => pure (f x)) := by
  unfold ivModePrfHandler blockModeWordQuery
  dsimp only
  by_cases hvalid : blockPairValid n (unframe request.2) (dropFrame request.2) = true
  · have hmod := length_select_mod_of_blockPairValid hvalid bit
    have hsel := blockModeSelect_padBlocks bit hvalid hℓ
    simp only [hvalid, ↓reduceIte, ProbOracleComp.run_bind, ProbOracleComp.run_sample,
      ProbOracleComp.run_map, ProbOracleComp.run_query, hprogram, blockModeOracle, hsel,
      ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure, ProbComp.eval_uniform,
      BitString.eval_sampleList, BitString.uniformList, PMF.bind_map, PMF.map_bind,
      Function.comp_def, PMF.pure_map, hword _ _ hmod]
  · simp [hvalid]

/-- **Ideal game.** Suppose that against every function `f`, the typed program `program q`
answers each block-mode query as the block-mode oracle of `bodyBlocks f` with cap `ℓ` and
challenge bit `bit` does, and the body queries from the bits of `iv`, answered by the
random-function oracle of `f`, compute on every whole-block message `m` the bits of
`bodyBlocks f iv` applied to the blocks of `m`. Then against a uniform random function, the
reduction is `program` simulated on the block-mode adversary, for an adversary whose requests
have left messages of at most `ℓ` blocks. The hypothesis `hℓ` constrains every request,
admissible or not. -/
theorem eval_prfIdealGame_ivModeToPrfDistinguisher
    {bodyQueries : ℕ → List Bool → List Bool → WordOracleComp Unit (List Bool)} {n ℓ : ℕ}
    {bit : Bool}
    {program : BlockModeQuery n →
      ProbOracleComp (fun _ : BitString n => BitString n) (BitString n × List (BitString n))}
    {bodyBlocks : (BitString n → BitString n) → BitString n → List (BitString n) →
      List (BitString n)}
    (hprogram : ∀ f q, (program q).run (fun x => pure (f x)) =
      blockModeOracle (bodyBlocks f) ℓ bit q)
    (hword : ∀ f iv m, m.length % n = 0 → (bodyQueries n (List.ofFn iv) m).run
        (fun request => pure (randomFunctionOracle n f request.2)) =
          pure ((bodyBlocks f iv (BitString.padBlocks n m.length m)).flatMap List.ofFn))
    (adversary : OracleDistinguisher)
    (hℓ : (adversary n []).QueriesSatisfy fun request => (unframe request.2).length / n ≤ ℓ) :
    ProbComp.eval (prfIdealGame id id (ivModeToPrfDistinguisher bodyQueries adversary bit) n) =
      ProbComp.eval (PRF.idealExperiment
        (ProbOracleComp.simulate program (blockModeWordAdversary adversary n))) := by
  simp only [prfIdealGame, id_eq, PRF.idealExperiment, ivModeToPrfDistinguisher,
    blockModeWordAdversary, ProbOracleComp.run_simulate, ProbComp.eval_bind]
  exact congrArg _ (funext fun f =>
    hℓ.eval_run_congr fun request hrequest =>
      eval_run_ivModePrfHandler_randomFunction (hprogram f) (hword f) request hrequest)

/-! ### Stream encryption -/

/-- The body of stream encryption from keystream queries: obtain the keystream of
`msg.length / n` blocks and XOR it with the message. -/
private noncomputable def ivStreamBodyQueries
    (keystreamQueries : ℕ → List Bool → ℕ → WordOracleComp Unit (List Bool)) (n : ℕ)
    (iv msg : List Bool) : WordOracleComp Unit (List Bool) :=
  (fun ks => List.zipWith xor ks msg) <$> keystreamQueries n iv (msg.length / n)

/-- The PRF distinguisher built from a left-or-right CPA adversary against stream encryption with
keystream queries `keystreamQueries` ([BonehShoup2023], proof of Theorem 5.3): the random-IV
reduction `ivModeToPrfDistinguisher` whose body obtains the keystream of `msg.length / n` blocks
and XORs it with the message. -/
noncomputable def ivStreamToPrfDistinguisher
    (keystreamQueries : ℕ → List Bool → ℕ → WordOracleComp Unit (List Bool))
    (adversary : OracleDistinguisher) (bit : Bool) : OracleDistinguisher :=
  ivModeToPrfDistinguisher (ivStreamBodyQueries keystreamQueries) adversary bit

/-- **Efficiency of the reduction.** If the keystream queries are strict oracle PPT on
`(1ⁿ, iv, 1^blocks)`, then for every uniform strict oracle-PPT adversary,
`ivStreamToPrfDistinguisher keystreamQueries adversary bit` is uniform strict oracle PPT. -/
theorem isOraclePPT_ivStreamToPrfDistinguisher
    {keystreamQueries : ℕ → List Bool → ℕ → WordOracleComp Unit (List Bool)}
    (hks : IsOraclePPTOn (encPair encUnary (encPair encBits encUnary)) encBits
      (fun ((n, iv, blocks) : ℕ × List Bool × ℕ) => keystreamQueries n iv blocks))
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsOraclePPT encBool (ivStreamToPrfDistinguisher keystreamQueries adversary bit) := by
  let EIn := encPair encUnary (encPair encBits encBits)
  have hargs : ComputableInPolyTime
      (fun a : ℕ × List Bool × List Bool => (a.1, a.2.1, a.2.2.length / a.1)) EIn
      (encPair encUnary (encPair encBits encUnary)) := by
    dsimp only [EIn]; fun_prop
  refine isOraclePPT_ivModeToPrfDistinguisher ((hks.preprocess hargs).map_with
    (f := fun a ks => List.zipWith xor ks a.2.2)
    (ComputableInPolyTime.bitsZipWithInput xor (ComputableInPolyTime.snd _ _)
      (by dsimp only [EIn]; fun_prop))) (fun _ _ _ _ hreply => ?_) hadversary bit
  obtain ⟨ks, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hreply
  simp

/-- **Real game.** If, under every key of length `n`, the keystream queries answered by the keyed
oracle compute `keystream n k iv blocks` from every `n`-bit initial value `iv`, then against the
keyed oracle `ivStreamToPrfDistinguisher keystreamQueries adversary bit` has the output law of
`adversary` in the CPA game of `ivStreamEncrypt keystream` with challenge bit `bit`. -/
theorem eval_prfRealGame_ivStreamToPrfDistinguisher
    {keystreamQueries : ℕ → List Bool → ℕ → WordOracleComp Unit (List Bool)}
    {keystream : ℕ → List Bool → List Bool → ℕ → List Bool}
    {family : List Bool → List Bool → List Bool} {n : ℕ}
    (hks : ∀ k : List Bool, k.length = n → ∀ iv : List Bool, iv.length = n → ∀ blocks,
      (keystreamQueries n iv blocks).run (fun request => pure (prfOracle family n k request.2)) =
        pure (keystream n k iv blocks))
    (adversary : OracleDistinguisher) (bit : Bool) :
    ProbComp.eval (prfRealGame id family (ivStreamToPrfDistinguisher keystreamQueries adversary bit)
        n) =
      ProbComp.eval (symmetricCPAGameOn blockPairValid BitString.sampleList
        (ivStreamEncrypt keystream) adversary bit n) :=
  eval_prfRealGame_ivModeToPrfDistinguisher (fun k hk iv hiv _ _ => by
    rw [ivStreamBodyQueries, ProbOracleComp.run_map, hks k hk iv hiv, map_pure]) adversary bit

/-- **Ideal game.** Suppose that against every function `f`, the typed keystream program
`typedQueries iv blocks` computes the `blocks` blocks `keystreamBlocks f iv blocks`, and the
keystream queries from the bits of `iv`, answered by the random-function oracle of `f`, compute
the bits of those blocks. Then against a uniform random function, the reduction for an adversary
whose requests have at most `ℓ` bits is the typed reduction `blockModeReduction typedQueries ℓ bit`
for the block-mode adversary. -/
theorem eval_prfIdealGame_ivStreamToPrfDistinguisher
    {keystreamQueries : ℕ → List Bool → ℕ → WordOracleComp Unit (List Bool)} {n : ℕ}
    {typedQueries : BitString n → ℕ →
      ProbOracleComp (fun _ : BitString n => BitString n) (List (BitString n))}
    {keystreamBlocks : (BitString n → BitString n) → BitString n → ℕ → List (BitString n)}
    (hlen : ∀ f iv blocks, (keystreamBlocks f iv blocks).length = blocks)
    (htyped : ∀ f iv blocks,
      (typedQueries iv blocks).run (fun x => pure (f x)) = pure (keystreamBlocks f iv blocks))
    (hword : ∀ f iv blocks, (keystreamQueries n (List.ofFn iv) blocks).run
        (fun request => pure (randomFunctionOracle n f request.2)) =
          pure ((keystreamBlocks f iv blocks).flatMap List.ofFn))
    (adversary : OracleDistinguisher) (bit : Bool) {ℓ : ℕ}
    (hℓ : (adversary n []).QueriesSatisfy fun request => request.2.length ≤ ℓ) :
    ProbComp.eval
        (prfIdealGame id id (ivStreamToPrfDistinguisher keystreamQueries adversary bit) n) =
      ProbComp.eval (PRF.idealExperiment
        (blockModeReduction typedQueries ℓ bit (blockModeWordAdversary adversary n))) :=
  eval_prfIdealGame_ivModeToPrfDistinguisher
    (bodyBlocks := fun f iv ms => List.zipWith (· + ·) (keystreamBlocks f iv ms.length) ms)
    (fun f q => by
      simp only [blockModeQueryProgram, blockModeOracle, ProbOracleComp.run_bind,
        ProbOracleComp.run_sample, htyped, pure_bind, ProbOracleComp.run_pure])
    (fun f iv m hm => by
      rw [ivStreamBodyQueries, ProbOracleComp.run_map, hword, map_pure,
        BitString.flatMap_ofFn_zipWith_add _ _ (by rw [hlen]),
        BitString.flatMap_ofFn_padBlocks (Nat.dvd_of_mod_eq_zero hm), BitString.length_padBlocks])
    adversary (hℓ.mono fun _ h => (Nat.div_le_self _ _).trans ((length_unframe_le _).trans h))

end Cslib.Crypto
