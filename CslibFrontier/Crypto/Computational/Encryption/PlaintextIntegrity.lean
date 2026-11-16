/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.EncForge
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair.Projections
import CslibFrontier.Crypto.Computational.Encryption.CCAToCPA
import CslibFrontier.Languages.Probabilistic.Oracle.QueryBoundedSimulation
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation.Handler
import CslibFrontier.Probability.BitString.List
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PPT

/-!
# Chosen-ciphertext security and plaintext integrity imply authenticated encryption

Plaintext integrity weakens ciphertext integrity: "the PI game is identical to the CI game except
that the winning condition is relaxed to: `D(k, c) ≠ reject`, and `D(k, c) ∉ {m₁, m₂, …}`"
([BonehShoup2023], Exercise 9.15, printed p. 395). In this library it is
`SymmetricCipher.EncForge`. Part (b) of the exercise asks to "prove that a system that is CCA- and
PI-secure is also AE-secure". This module proves it: `INDCCA` and `EncForge` give
`CiphertextIntegrity`, and with `SymmetricCipher.INDCCA.indcpa` they give
`AuthenticatedEncryption`.

Given a CI adversary `A` that makes at most `Q` encryption queries, the proof uses two reductions.
Both draw `Q` independent uniform `n`-bit messages `r₁, …, r_Q`.

* `ciToCCAAdversary` runs `A` and answers its `i`-th encryption query `mᵢ` by asking the CCA
  oracle to encrypt `mᵢ` (bit `false`) or `rᵢ` (bit `true`). It then makes one decryption query,
  on `A`'s forgery `c`, and outputs `true` when `D(k, c)` is accepted and is none of the `rᵢ`.
* `ciToRandEncForgeAdversary` runs `A` against the plaintext-integrity encryption oracle, which it
  asks to encrypt `rᵢ` in place of `mᵢ`, and outputs `A`'s forgery.

When the bit is `false`, the `rᵢ` are independent of everything `A` sees, so the CCA reduction
outputs `true` whenever `A` wins, except with probability at most `Q / 2ⁿ`. When the bit is
`true`, it outputs `true` only when the plaintext-integrity reduction wins. Hence
`CIadv[A] ≤ PIadv[ciToRandEncForgeAdversary] + CCAadv[ciToCCAAdversary] + Q / 2ⁿ`
(`succProbability_ciGame_le_encForge_add_indcca`).

The exercise says that the proof "only needs a weak version of CCA, namely where the adversary
issues a single decryption query and is told whether the ciphertext is accepted or rejected". The
reduction here makes one decryption query, and it uses the plaintext that the query returns. The
hypothesis is the library's `INDCCA`; no one-query notion is defined. The exercise also allows "a
super-poly-sized message space"; here the messages at parameter `n` are the `n`-bit strings, and
the `Q / 2ⁿ` term is the cost.

## Main definitions

* `SymmetricCipher.ciToCCAAdversary`: the CCA reduction, making one decryption query.
* `SymmetricCipher.ciToRandEncForgeAdversary`: the plaintext-integrity reduction.

## Main results

* `SymmetricCipher.isOraclePPT_ciToCCAAdversary`,
  `SymmetricCipher.isOraclePPT_ciToRandEncForgeAdversary`: both reductions are oracle PPT.
* `SymmetricCipher.succProbability_ciGame_le_encForge_add_indcca`: the concrete bound above.
* `SymmetricCipher.INDCCA.ciphertextIntegrity`: `INDCCA` and `EncForge` imply
  `CiphertextIntegrity`.
* `SymmetricCipher.INDCCA.authenticatedEncryption`: `INDCCA` and `EncForge` imply
  `AuthenticatedEncryption` (Exercise 9.15(b)).

## References

* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023]
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped ENNReal NNReal

namespace SymmetricCipher

/-! ### The two reductions -/

/-- Handler of `ciToCCAAdversary`: in state `(idx, rs)`, answers an encryption query for an
`n`-bit message `m` by asking the CCA oracle to encrypt `m` or the `idx`-th `n`-bit row `r` of
`rawBits` (`BitString.listRow`), and moves to `(idx + 1, r :: rs)`. -/
private def ciToCCAHandler (n ctBound : ℕ) (rawBits : List Bool) (request : Unit × List Bool) :
    StateT (ℕ × List (List Bool)) (WordOracleComp Bool) (List Bool) :=
  fun (idx, rs) =>
    if request.2.length == n then do
      let ct ← List.take ctBound <$>
        ProbOracleComp.query
          (false, encPair encBits encBits (request.2, BitString.listRow n idx rawBits))
      return (ct, (idx + 1, BitString.listRow n idx rawBits :: rs))
    else
      return ([], (idx, rs))

/-- The CCA reduction for Exercise 9.15(b). It draws `Q n` uniform `n`-bit messages `rᵢ` and runs
the CI adversary, answering its `i`-th encryption query `mᵢ` with an encryption of `mᵢ` or of `rᵢ`
from the CCA oracle (replies truncated to `ctBound n` bits). It then makes one decryption query, on
the adversary's forgery, and outputs `true` when the decryption is accepted and is none of the
`rᵢ`. -/
noncomputable def ciToCCAAdversary (ctBound Q : ℕ → ℕ) (adversary : CIAdversary) :
    CCAAdversary :=
  fun n _ => do
    let rawBits ← ProbOracleComp.sample (BitString.sampleList (Q n * n))
    let (forgery, _, rUsed) ← (OracleComp.interpret
      (OracleComp.sumHandler
        (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
        (ciToCCAHandler n (ctBound n) rawBits))
      (adversary n [])).run (0, [])
    let dec ← List.take (n + 2) <$> ProbOracleComp.query (true, forgery)
    return (dec.take 1 == [true]) && !rUsed.contains (dec.drop 1)

/-- Handler of `ciToRandEncForgeAdversary`: in state `idx`, answers an encryption query for an
`n`-bit message by asking the plaintext-integrity oracle to encrypt the `idx`-th `n`-bit row of
`rawBits` (`BitString.listRow`). -/
private def ciToRandEncForgeHandler (n ctBound : ℕ) (rawBits : List Bool)
    (request : Unit × List Bool) : StateT ℕ (WordOracleComp Unit) (List Bool) :=
  fun idx =>
    if request.2.length == n then do
      let ct ← List.take ctBound <$> ProbOracleComp.query ((), BitString.listRow n idx rawBits)
      return (ct, idx + 1)
    else
      return ([], idx)

/-- The plaintext-integrity reduction for Exercise 9.15(b). It draws `Q n` uniform `n`-bit
messages `rᵢ`, runs the CI adversary, answering its `i`-th encryption query with an encryption of
`rᵢ` (replies truncated to `ctBound n` bits), and outputs the adversary's forgery. -/
noncomputable def ciToRandEncForgeAdversary (ctBound Q : ℕ → ℕ) (adversary : CIAdversary) :
    CIAdversary :=
  fun n _ => do
    let rawBits ← ProbOracleComp.sample (BitString.sampleList (Q n * n))
    let out ← (OracleComp.interpret
      (OracleComp.sumHandler
        (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
        (ciToRandEncForgeHandler n (ctBound n) rawBits))
      (adversary n [])).run 0
    return out.1

/-- `ciToCCAAdversary` is oracle PPT when the CI adversary is and the bounds `ctBound` and `Q` are
polynomial-time computable. -/
theorem isOraclePPT_ciToCCAAdversary {ctBound Q : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    {adversary : CIAdversary} (hadversary : IsOraclePPT encBits adversary) :
    IsOraclePPT encBool (ciToCCAAdversary ctBound Q adversary) := by
  let ECaller := encPair (encPair encUnary encBits) encBits
  let EState := encPair encUnary (encList encBits)
  let EHandler := encPair ECaller (encPair (encPair (encFinEnum Unit) encBits) EState)
  have hraw : IsPPTOn (encPair encUnary encBits) encBits
      (fun caller : ℕ × List Bool => BitString.sampleList (Q caller.1 * caller.1)) :=
    ComputableInPolyTime.sampleList (by fun_prop)
  have hcond : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × (ℕ × List (List Bool))) =>
        p.2.1.2.length == p.1.1.1)
      EHandler encBool :=
    ComputableInPolyTime.unary_beq'
      (ComputableInPolyTime.length_bits.comp (by dsimp only [EHandler]; fun_prop))
      (by dsimp only [EHandler, ECaller]; fun_prop)
  have hchunk : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × (ℕ × List (List Bool))) =>
        BitString.listRow p.1.1.1 p.2.2.1 p.1.2)
      EHandler encBits :=
    ComputableInPolyTime.bitsRowWithInput
      (by dsimp only [EHandler, ECaller]; fun_prop)
      (by dsimp only [EHandler, EState]; fun_prop)
      (by dsimp only [EHandler, ECaller]; fun_prop)
  have hyes : IsOraclePPTOn (Operation := Bool) EHandler (encPair encBits EState)
      (fun p : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × (ℕ × List (List Bool))) => do
        let ct ← List.take (ctBound p.1.1.1) <$>
          ProbOracleComp.query
            (false, encPair encBits encBits (p.2.1.2, BitString.listRow p.1.1.1 p.2.2.1 p.1.2))
        return (ct, (p.2.2.1 + 1, BitString.listRow p.1.1.1 p.2.2.1 p.1.2 :: p.2.2.2))) := by
    have hreq : ComputableInPolyTime
        (fun p : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × (ℕ × List (List Bool))) =>
          encPair encBits encBits (p.2.1.2, BitString.listRow p.1.1.1 p.2.2.1 p.1.2))
        EHandler encBits :=
      ComputableInPolyTime.encoding_comp
        ((by dsimp only [EHandler]; fun_prop : ComputableInPolyTime
          (fun p : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × (ℕ × List (List Bool))) =>
            p.2.1.2) EHandler encBits).prod hchunk)
    have hctLim : ComputableInPolyTime
        (fun p : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × (ℕ × List (List Bool))) =>
          ctBound p.1.1.1)
        EHandler encUnary :=
      hctBound.comp ((ComputableInPolyTime.fst _ _).comp
        ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _)))
    have hq := IsOraclePPTOn.query_take (Operation := Bool) false hreq hctLim
    have hpost : ComputableInPolyTime
        (fun q : (((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × (ℕ × List (List Bool)))) ×
            List Bool =>
          (q.2, (q.1.2.2.1 + 1, BitString.listRow q.1.1.1.1 q.1.2.2.1 q.1.1.2 :: q.1.2.2.2)))
        (encPair EHandler encBits) (encPair encBits EState) := by
      have hc : ComputableInPolyTime
          (fun q : (((ℕ × List Bool) × List Bool) ×
              ((Unit × List Bool) × (ℕ × List (List Bool)))) × List Bool =>
            BitString.listRow q.1.1.1.1 q.1.2.2.1 q.1.1.2)
          (encPair EHandler encBits) encBits :=
        hchunk.comp (ComputableInPolyTime.fst _ _)
      have hcons : ComputableInPolyTime
          (fun q : (((ℕ × List Bool) × List Bool) ×
              ((Unit × List Bool) × (ℕ × List (List Bool)))) × List Bool =>
            BitString.listRow q.1.1.1.1 q.1.2.2.1 q.1.1.2 :: q.1.2.2.2)
          (encPair EHandler encBits) (encList encBits) :=
        (ComputableTidilyInPolyTime.cons encBits).computableInPolyTime.comp
          (hc.prod (by dsimp only [EHandler, EState]; fun_prop))
      have hidx : ComputableInPolyTime
          (fun q : (((ℕ × List Bool) × List Bool) ×
              ((Unit × List Bool) × (ℕ × List (List Bool)))) × List Bool =>
            q.1.2.2.1 + 1)
          (encPair EHandler encBits) encUnary := by
        dsimp only [EHandler, EState]; fun_prop
      exact (ComputableInPolyTime.snd _ _).prod (hidx.prod hcons)
    exact hq.bind_with hpost.isOraclePPTOn
  have hno : IsOraclePPTOn (Operation := Bool) EHandler (encPair encBits EState)
      (fun p : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × (ℕ × List (List Bool))) =>
        pure ([], p.2.2)) :=
    (ComputableInPolyTime.prod (ComputableInPolyTime.const [])
      (by dsimp only [EHandler]; fun_prop)).isOraclePPTOn
  have hhandler : IsOraclePPTOn EHandler (encPair encBits EState)
      (fun pair : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × (ℕ × List (List Bool))) =>
        ciToCCAHandler pair.1.1.1 (ctBound pair.1.1.1) pair.1.2 pair.2.1 pair.2.2) := by
    unfold ciToCCAHandler
    exact IsOraclePPTOn.cond hcond hyes hno
  have hres : ComputableInPolyTime
      (fun pair : ((ℕ × List Bool) × List Bool) × List Bool =>
        ctBound pair.1.1.1 + 2 * pair.2.length + 4)
      (encPair ECaller encBits) encUnary := by
    dsimp only [ECaller]
    have hct : ComputableInPolyTime
        (fun pair : ((ℕ × List Bool) × List Bool) × List Bool => ctBound pair.1.1.1)
        (encPair (encPair (encPair encUnary encBits) encBits) encBits) encUnary :=
      hctBound.comp (by fun_prop)
    have hqlen : ComputableInPolyTime
        (fun pair : ((ℕ × List Bool) × List Bool) × List Bool => 2 * pair.2.length + 4)
        (encPair (encPair (encPair encUnary encBits) encBits) encBits) encUnary := by
      fun_prop
    exact ComputableInPolyTime.unary_add.comp (ComputableInPolyTime.prod hct hqlen)
  have hrun : IsOraclePPTOn (Operation := Bool) ECaller (encPair encBits EState)
      (fun caller : (ℕ × List Bool) × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (ciToCCAHandler caller.1.1 (ctBound caller.1.1) caller.2))
          (adversary caller.1.1 [])).run (0, [])) := by
    apply hadversary.run_interpret_preprocess_open
      (input := ECaller)
      (handler := fun caller : (ℕ × List Bool) × List Bool =>
        ciToCCAHandler caller.1.1 (ctBound caller.1.1) caller.2)
      (prepare := fun caller : (ℕ × List Bool) × List Bool => (caller.1.1, ([] : List Bool)))
      (initial := fun _ => (0, ([] : List (List Bool))))
      (resources := fun caller query => ctBound caller.1.1 + 2 * query.length + 4)
      (by dsimp only [ECaller]; fun_prop) hhandler
      (ComputableInPolyTime.const (0, ([] : List (List Bool))))
      (fun _ _ => True) (fun _ => trivial) hres
    intro caller request state _ result hresult
    unfold ciToCCAHandler at hresult
    split_ifs at hresult with hlenEq
    · obtain ⟨ct, hct, hresult⟩ := OracleComp.mem_supportWith_bind_iff.mp hresult
      obtain ⟨rawCt, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hct
      have hresEq := OracleComp.eq_of_mem_supportWith_pure hresult
      subst hresEq
      refine ⟨trivial, (List.length_take_le _ _).trans (by lia), ?_⟩
      have hcl : (BitString.listRow caller.1.1 state.1 caller.2).length = request.2.length :=
        (BitString.length_listRow _ _ _).trans (beq_iff_eq.mp hlenEq).symm
      dsimp only [EState]
      enc_len
    · have hresEq := OracleComp.eq_of_mem_supportWith_pure hresult
      subst hresEq
      exact ⟨trivial, by simp, by simp⟩
  have hdecReq : ComputableInPolyTime
      (fun q : ((ℕ × List Bool) × List Bool) × (List Bool × (ℕ × List (List Bool))) => q.2.1)
      (encPair ECaller (encPair encBits EState)) encBits := by
    dsimp only [ECaller]; fun_prop
  have hdecLim : ComputableInPolyTime
      (fun q : ((ℕ × List Bool) × List Bool) × (List Bool × (ℕ × List (List Bool))) => q.1.1.1 + 2)
      (encPair ECaller (encPair encBits EState)) encUnary := by
    dsimp only [ECaller]; fun_prop
  have hdec := IsOraclePPTOn.query_take (Operation := Bool) true hdecReq hdecLim
  have hdrop1 : ComputableInPolyTime
      (fun r : (((ℕ × List Bool) × List Bool) × (List Bool × (ℕ × List (List Bool)))) × List Bool =>
        r.2.drop 1)
      (encPair (encPair ECaller (encPair encBits EState)) encBits) encBits :=
    ComputableTidilyInPolyTime.computableInPolyTime
      (ComputableTidilyInPolyTime.dropUnary (encA := encBool) (encL := encBits)) |>.comp
      ((by dsimp only [ECaller]; fun_prop : ComputableInPolyTime
        (fun r : (((ℕ × List Bool) × List Bool) ×
            (List Bool × (ℕ × List (List Bool)))) × List Bool => r.2)
        (encPair (encPair ECaller (encPair encBits EState)) encBits) encBits).prod
        (ComputableInPolyTime.const 1))
  have hret : ComputableInPolyTime
      (fun r : (((ℕ × List Bool) × List Bool) × (List Bool × (ℕ × List (List Bool)))) × List Bool =>
        (r.2.take 1 == [true]) && !r.1.2.2.2.contains (r.2.drop 1))
      (encPair (encPair ECaller (encPair encBits EState)) encBits) encBool := by
    have ht1 : ComputableInPolyTime
        (fun r : (((ℕ × List Bool) × List Bool) ×
            (List Bool × (ℕ × List (List Bool)))) × List Bool =>
          r.2.take 1 == [true])
        (encPair (encPair ECaller (encPair encBits EState)) encBits) encBool :=
      ComputableInPolyTime.beq (encB := encBits)
        (by fun_prop) (ComputableInPolyTime.const [true])
    have hc : ComputableInPolyTime
        (fun r : (((ℕ × List Bool) × List Bool) ×
            (List Bool × (ℕ × List (List Bool)))) × List Bool =>
          r.1.2.2.2.contains (r.2.drop 1))
        (encPair (encPair ECaller (encPair encBits EState)) encBits) encBool :=
      ComputableInPolyTime.contains
        (by dsimp only [ECaller, EState]; fun_prop) hdrop1
    exact ComputableInPolyTime.bool_and.comp (ht1.prod (ComputableInPolyTime.bool_not.comp hc))
  have hdecStep :
      IsOraclePPTOn (Operation := Bool) (encPair ECaller (encPair encBits EState)) encBool
      (fun q : ((ℕ × List Bool) × List Bool) × (List Bool × (ℕ × List (List Bool))) => do
        let dec ← List.take (q.1.1.1 + 2) <$> ProbOracleComp.query (true, q.2.1)
        return (dec.take 1 == [true]) && !q.2.2.2.contains (dec.drop 1)) :=
    hdec.bind_with hret.isOraclePPTOn
  have hinner : IsOraclePPTOn (Operation := Bool) ECaller encBool
      (fun caller : (ℕ × List Bool) × List Bool => do
        let out ← (OracleComp.interpret
          (OracleComp.sumHandler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (ciToCCAHandler caller.1.1 (ctBound caller.1.1) caller.2))
          (adversary caller.1.1 [])).run (0, [])
        let dec ← List.take (caller.1.1 + 2) <$> ProbOracleComp.query (true, out.1)
        return (dec.take 1 == [true]) && !out.2.2.contains (dec.drop 1)) :=
    hrun.bind_with hdecStep
  unfold ciToCCAAdversary
  exact ((hraw.isOraclePPTOn (Operation := Bool)).bind_with hinner).isOraclePPT

/-- `ciToRandEncForgeAdversary` is oracle PPT when the CI adversary is and the bounds `ctBound`
and `Q` are polynomial-time computable. -/
theorem isOraclePPT_ciToRandEncForgeAdversary {ctBound Q : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    {adversary : CIAdversary} (hadversary : IsOraclePPT encBits adversary) :
    IsOraclePPT encBits (ciToRandEncForgeAdversary ctBound Q adversary) := by
  let ECaller := encPair (encPair encUnary encBits) encBits
  let EHandler := encPair ECaller (encPair (encPair (encFinEnum Unit) encBits) encUnary)
  have hraw : IsPPTOn (encPair encUnary encBits) encBits
      (fun caller : ℕ × List Bool => BitString.sampleList (Q caller.1 * caller.1)) :=
    ComputableInPolyTime.sampleList (by fun_prop)
  have hcond : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × ℕ) =>
        p.2.1.2.length == p.1.1.1)
      EHandler encBool :=
    ComputableInPolyTime.unary_beq'
      (ComputableInPolyTime.length_bits.comp (by dsimp only [EHandler]; fun_prop))
      (by dsimp only [EHandler, ECaller]; fun_prop)
  have hchunk : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × ℕ) =>
        BitString.listRow p.1.1.1 p.2.2 p.1.2)
      EHandler encBits :=
    ComputableInPolyTime.bitsRowWithInput
      (by dsimp only [EHandler, ECaller]; fun_prop)
      (by dsimp only [EHandler]; fun_prop)
      (by dsimp only [EHandler, ECaller]; fun_prop)
  have hctLim : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × ℕ) => ctBound p.1.1.1)
      EHandler encUnary :=
    hctBound.comp ((ComputableInPolyTime.fst _ _).comp
      ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _)))
  have hyes : IsOraclePPTOn (Operation := Unit) EHandler (encPair encBits encUnary)
      (fun p : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × ℕ) => do
        let ct ← List.take (ctBound p.1.1.1) <$>
          ProbOracleComp.query ((), BitString.listRow p.1.1.1 p.2.2 p.1.2)
        return (ct, p.2.2 + 1)) := by
    have hq := IsOraclePPTOn.query_take (Operation := Unit) () hchunk hctLim
    have hpost : ComputableInPolyTime
        (fun q : (((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × ℕ)) × List Bool =>
          (q.2, q.1.2.2 + 1))
        (encPair EHandler encBits) (encPair encBits encUnary) := by
      dsimp only [EHandler]; fun_prop
    exact hq.bind_with hpost.isOraclePPTOn
  have hno : IsOraclePPTOn (Operation := Unit) EHandler (encPair encBits encUnary)
      (fun p : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × ℕ) => pure ([], p.2.2)) :=
    (ComputableInPolyTime.prod (ComputableInPolyTime.const [])
      (by dsimp only [EHandler]; fun_prop)).isOraclePPTOn
  have hhandler : IsOraclePPTOn EHandler (encPair encBits encUnary)
      (fun pair : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × ℕ) =>
        ciToRandEncForgeHandler pair.1.1.1 (ctBound pair.1.1.1) pair.1.2 pair.2.1 pair.2.2) := by
    unfold ciToRandEncForgeHandler
    exact IsOraclePPTOn.cond hcond hyes hno
  have hres : ComputableInPolyTime
      (fun pair : ((ℕ × List Bool) × List Bool) × List Bool => ctBound pair.1.1.1 + 1)
      (encPair ECaller encBits) encUnary := by
    dsimp only [ECaller]
    have hct : ComputableInPolyTime
        (fun pair : ((ℕ × List Bool) × List Bool) × List Bool => ctBound pair.1.1.1)
        (encPair (encPair (encPair encUnary encBits) encBits) encBits) encUnary :=
      hctBound.comp (by fun_prop)
    exact ComputableInPolyTime.unary_add.comp
      (ComputableInPolyTime.prod hct (ComputableInPolyTime.const 1))
  have hrun : IsOraclePPTOn (Operation := Unit) ECaller (encPair encBits encUnary)
      (fun caller : (ℕ × List Bool) × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (ciToRandEncForgeHandler caller.1.1 (ctBound caller.1.1) caller.2))
          (adversary caller.1.1 [])).run 0) := by
    apply hadversary.run_interpret_preprocess_open
      (input := ECaller)
      (handler := fun caller : (ℕ × List Bool) × List Bool =>
        ciToRandEncForgeHandler caller.1.1 (ctBound caller.1.1) caller.2)
      (prepare := fun caller : (ℕ × List Bool) × List Bool => (caller.1.1, ([] : List Bool)))
      (initial := fun _ => (0 : ℕ))
      (resources := fun caller _ => ctBound caller.1.1 + 1)
      (by dsimp only [ECaller]; fun_prop) hhandler
      (ComputableInPolyTime.const (0 : ℕ))
      (fun _ _ => True) (fun _ => trivial) hres
    intro caller request state _ result hresult
    unfold ciToRandEncForgeHandler at hresult
    split_ifs at hresult with hlenEq
    · obtain ⟨ct, hct, hresult⟩ := OracleComp.mem_supportWith_bind_iff.mp hresult
      obtain ⟨rawCt, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hct
      have hresEq := OracleComp.eq_of_mem_supportWith_pure hresult
      subst hresEq
      refine ⟨trivial, (List.length_take_le _ _).trans (by lia), ?_⟩
      enc_len
    · have hresEq := OracleComp.eq_of_mem_supportWith_pure hresult
      subst hresEq
      exact ⟨trivial, by simp, by simp⟩
  have hpost :
      IsOraclePPTOn (Operation := Unit) (encPair ECaller (encPair encBits encUnary)) encBits
      (fun p : ((ℕ × List Bool) × List Bool) × (List Bool × ℕ) => pure p.2.1) := by
    have hp : ComputableInPolyTime
        (fun p : ((ℕ × List Bool) × List Bool) × (List Bool × ℕ) => p.2.1)
        (encPair ECaller (encPair encBits encUnary)) encBits := by
      dsimp only [ECaller]; fun_prop
    exact hp.isOraclePPTOn
  unfold ciToRandEncForgeAdversary
  exact ((hraw.isOraclePPTOn (Operation := Unit)).bind_with (hrun.bind_with hpost)).isOraclePPT

private theorem contains_take_eq_of_forall_length {msgs : List (List Bool)} {n : ℕ}
    (hm : ∀ m ∈ msgs, m.length = n) (pt : List Bool) :
    msgs.contains (pt.take (n + 1)) = msgs.contains pt := by
  simp only [List.contains_eq_mem, decide_eq_decide]
  constructor
  · intro hmem
    have hlen : (pt.take (n + 1)).length = n := hm _ hmem
    rw [List.length_take] at hlen
    have hptLen : pt.length = n := by omega
    simpa [List.take_of_length_le (by omega : pt.length ≤ n + 1)] using hmem
  · intro hmem
    have hlen : pt.length = n := hm _ hmem
    simpa [List.take_of_length_le (by omega : pt.length ≤ n + 1)] using hmem

private theorem decCheck_eq (E : SymmetricCipher) (n : ℕ) (k : List Bool)
    (ct : List Bool) (rs : List (List Bool)) (hr : ∀ r ∈ rs, r.length = n)
    (queried : List (List Bool)) :
    (let reply := if queried.contains ct then [] else encOption encBits (E.decrypt n k ct)
     let dec := reply.take (n + 2)
     (dec.take 1 == [true]) && !rs.contains (dec.drop 1)) =
      (!queried.contains ct &&
        ((E.decrypt n k ct).isSome && !rs.contains ((E.decrypt n k ct).getD []))) := by
  simp only [List.contains_eq_mem]
  by_cases hq : ct ∈ queried
  · simp [hq]
  · simp only [hq, decide_false, Bool.not_false, Bool.true_and]
    cases hdec : E.decrypt n k ct with
    | none =>
      simp [encOption]
    | some pt =>
      simp only [encOption, encBits_apply, Option.isSome_some, Option.getD_some, Bool.true_and]
      have hc := contains_take_eq_of_forall_length hr pt
      simp only [List.contains_eq_mem, decide_eq_decide] at hc
      simp [List.take_succ_cons, List.drop_succ_cons, hc]

/-- A program that makes at most `Q` queries to `ciPairOracle` records at most `Q` pairs. -/
private theorem length_le_of_mem_support_runWith_ciPairOracle (E : SymmetricCipher) (n Q : ℕ)
    (k : List Bool) {prog : WordOracleComp Unit (List Bool)} (hq : prog.IsQueryBounded Q)
    {ctStar : List Bool} {pairs : List (List Bool × List Bool)}
    (hmem : (ctStar, pairs) ∈ (ProbOracleComp.runWith
      (fun q s => ProbComp.eval (E.ciPairOracle n k q s)) prog []).support) :
    pairs.length ≤ Q := by
  rw [ProbOracleComp.runWith_eq_run_interpret] at hmem
  have h := hq.run_interpret_invariant (fun q s => ProbComp.eval (E.ciPairOracle n k q s))
    (fun rem (s : List (List Bool × List Bool)) => s.length + rem ≤ Q)
    (fun _ _ h => by omega) ?_ (by simp) ctStar pairs hmem
  · simpa using h
  · intro rem ⟨⟨⟩, msg⟩ s hs a s' hstep
    unfold SymmetricCipher.ciPairOracle at hstep
    split_ifs at hstep
    · simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
        PMF.mem_support_pure_iff] at hstep
      obtain ⟨ct, _, hstepEq⟩ := hstep
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hstepEq
      simp only [List.length_cons]
      omega
    · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hstep
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hstep
      omega

/-- The first `k` random chunks of `rawBits`, most recent first. -/
private def chunksBelow (rawBits : List Bool) (n : ℕ) : ℕ → List (List Bool)
  | 0 => []
  | k + 1 => BitString.listRow n k rawBits :: chunksBelow rawBits n k

private theorem mem_chunksBelow {rawBits : List Bool} {n k : ℕ} {r : List Bool} :
    r ∈ chunksBelow rawBits n k ↔ ∃ i < k, BitString.listRow n i rawBits = r := by
  induction k with
  | zero => simp [chunksBelow]
  | succ k ih =>
    simp only [chunksBelow, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨k, by omega, rfl⟩
      · exact ⟨i, by omega, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact Or.inr ⟨i, hi, rfl⟩
      · exact Or.inl rfl

private theorem eval_run_ciToCCAHandler_false (E : SymmetricCipher) (n ctBound : ℕ)
    (k : List Bool) (rawBits : List Bool)
    (hk : k ∈ (ProbComp.eval (E.keyGen n)).support)
    (hctBound : E.CiphertextLengthLE n ctBound)
    (prog : WordOracleComp Unit (List Bool)) :
    ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ccaOracle n k false q s))
      ((OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
          (ciToCCAHandler n ctBound rawBits)) prog).run (0, [])) [] =
    (ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ciPairOracle n k q s)) prog []).map
      (fun (ctStar, pairs) =>
        ((ctStar, (pairs.length, chunksBelow rawBits n pairs.length)), pairs.map Prod.snd)) := by
  refine ProbOracleComp.runWith_run_interpret_map (ciToCCAHandler n ctBound rawBits)
    (fun q s => ProbComp.eval (E.ccaOracle n k false q s))
    (fun q s => ProbComp.eval (E.ciPairOracle n k q s))
    (fun pairs => (pairs.length, chunksBelow rawBits n pairs.length))
    (fun pairs => pairs.map Prod.snd)
    ?_ prog []
  intro ⟨⟨⟩, msg⟩ pairs
  unfold SymmetricCipher.ciPairOracle ciToCCAHandler
  by_cases hlen : msg.length = n
  · have hbeq : (msg.length == n) = true := beq_iff_eq.mpr hlen
    have hchunkLen : (BitString.listRow n pairs.length rawBits).length = n :=
      BitString.length_listRow n pairs.length rawBits
    simp only [StateT.run, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
      ProbOracleComp.runWith_bind, ProbOracleComp.runWith_map,
      ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure,
      SymmetricCipher.ccaOracle, Bool.false_eq_true, unframe_encPair_encBits,
      dropFrame_encPair_encBits, hlen, hchunkLen, beq_self_eq_true, Bool.and_self,
      PMF.bind_bind, PMF.map_bind, PMF.pure_bind, PMF.pure_map, Prod.map_apply, id_eq]
    apply PMF.bind_congr_on_support
    intro ct hct
    have htake : ct.take ctBound = ct := List.take_of_length_le (hctBound k hk msg hlen ct hct)
    simp only [htake, List.length_cons, List.map_cons, chunksBelow]
  · have hbeq : (msg.length == n) = false := beq_false_of_ne hlen
    simp only [StateT.run, hbeq, Bool.false_eq_true, ↓reduceIte,
      ProbOracleComp.runWith_pure, ProbComp.eval_pure, PMF.pure_map]

/-- A uniform `rawBits` hits a fixed string `x` among its first `L ≤ Q` chunks with probability at
most `Q / 2^n`. -/
private theorem uniformList_chunksBelow_contains_le (Q n L : ℕ) (hL : L ≤ Q) (x : List Bool) :
    ((BitString.uniformList (Q * n)).map
      (fun rawBits => (chunksBelow rawBits n L).contains x)) true ≤
      (Q : ENNReal) / (2 : ENNReal) ^ n := by
  have hmono := Cslib.Probability.PMF.map_true_mono (BitString.uniformList (Q * n))
    (E := fun rawBits => (chunksBelow rawBits n L).contains x)
    (F := fun rawBits => (List.range L).any (fun i => BitString.listRow n i rawBits == x))
    (fun rawBits _ h => by
      obtain ⟨i, hi, heq⟩ := mem_chunksBelow.mp (List.contains_iff_mem.mp h)
      exact List.any_eq_true.mpr ⟨i, List.mem_range.mpr hi, beq_iff_eq.mpr heq⟩)
  refine hmono.trans ((Cslib.Probability.PMF.map_any_range_true_le_sum _ L
    (fun i rawBits => BitString.listRow n i rawBits == x)).trans ?_)
  have hterm (i : ℕ) (hi : i ∈ Finset.range L) :
      ((BitString.uniformList (Q * n)).map
        (fun rawBits => BitString.listRow n i rawBits == x)) true ≤
        1 / (2 : ENNReal) ^ n := by
    rw [← Function.comp_def (fun r => r == x), ← PMF.map_comp,
      BitString.uniformList_map_listRow (lt_of_lt_of_le (Finset.mem_range.mp hi) hL), PMF.map_apply]
    rw [tsum_eq_single x (fun r hr => by simp [hr])]
    simpa using BitString.uniformList_apply_le n x
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_div_assoc, mul_one]
  gcongr

/-- Averaging a win indicator `W` over an independent `u`: if `W` implies `B r ∨ Bad r` for each
`r`, and every `Bad · a` has `u`-mass at most `ε`, then `W` has mass at most that of `B` plus
`ε`. -/
private theorem map_true_le_bind_add {α β : Type} (run : PMF α) (u : PMF β)
    (W : α → Bool) (B Bad : β → α → Bool) (ε : ENNReal)
    (himp : ∀ r, ∀ a ∈ run.support, W a = true → B r a = true ∨ Bad r a = true)
    (hbad : ∀ a ∈ run.support, (u.map fun r => Bad r a) true ≤ ε) :
    (run.map W) true ≤ (u.bind fun r => run.map (B r)) true + ε := by
  have hW : run.map W = u.bind fun _ => run.map W := (PMF.bind_const _ _).symm
  rw [hW, PMF.bind_apply, PMF.bind_apply]
  have hswap : ∑' r, u r * (run.map (Bad r)) true =
      (run.bind fun a => u.map fun r => Bad r a) true := by
    rw [← PMF.bind_apply]
    congr 1
    simp only [PMF.map]
    exact PMF.bind_comm _ _ _
  have hbadSum : ∑' r, u r * (run.map (Bad r)) true ≤ ε := by
    rw [hswap, PMF.bind_apply]
    calc ∑' a, run a * (u.map fun r => Bad r a) true ≤ ∑' a, run a * ε := by
          refine tsum_le_tsum fun a => ?_
          by_cases ha : a ∈ run.support
          · exact mul_le_mul_of_nonneg_left (hbad a ha) zero_le
          · have h0 : run a = 0 := not_not.mp ((PMF.mem_support_iff _ _).not.mp ha)
            simp [h0]
      _ = ε := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  calc ∑' r, u r * (run.map W) true
      ≤ ∑' r, u r * ((run.map (B r)) true + (run.map (Bad r)) true) :=
        tsum_le_tsum fun r => mul_le_mul_of_nonneg_left
          (Cslib.Probability.PMF.map_true_le_add run (himp r)) zero_le
    _ = ∑' r, u r * (run.map (B r)) true + ∑' r, u r * (run.map (Bad r)) true := by
        simp_rw [mul_add]
        exact tsum_add
    _ ≤ ∑' r, u r * (run.map (B r)) true + ε := add_le_add le_rfl hbadSum

/-- The `false` world of `ciToCCAAdversary` is the CI game, except when the decrypted forgery is
one of the unused random messages `r_i`, which has probability at most `Q / 2^n`. -/
private theorem succProbability_ciGame_le_ccaFalse (E : SymmetricCipher)
    (ctBound Q : ℕ → ℕ) (adversary : CIAdversary) (n : ℕ)
    (hq : (adversary n []).IsQueryBounded (Q n))
    (hctBound : E.CiphertextLengthLE n (ctBound n)) :
    (Game.succProbability (ProbComp.eval (E.ciGame adversary n)) : ℝ) ≤
      (Game.succProbability (ProbComp.eval
        (E.ccaGame (ciToCCAAdversary ctBound Q adversary) false n)) : ℝ) +
      (Q n : ℝ) / (2 : ℝ) ^ n := by
  have hfin : (Q n : ENNReal) / (2 : ENNReal) ^ n ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by simp)
  have hleENN :
      (ProbComp.eval (E.ciGame adversary n)) true ≤
        (ProbComp.eval (E.ccaGame (ciToCCAAdversary ctBound Q adversary) false n)) true +
        (Q n : ENNReal) / (2 : ENNReal) ^ n := by
    simp only [SymmetricCipher.ciGame, SymmetricCipher.ccaGame,
      ProbComp.eval_bind, ProbComp.eval_pure, ProbOracleComp.eval_run_interpret_eq_runWith]
    rw [PMF.bind_apply, PMF.bind_apply]
    have hconst : (Q n : ENNReal) / (2 : ENNReal) ^ n =
        ∑' k, (ProbComp.eval (E.keyGen n)) k * ((Q n : ENNReal) / (2 : ENNReal) ^ n) := by
      rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    rw [hconst, ← tsum_add]
    refine tsum_le_tsum fun k => ?_
    by_cases hk : k ∈ (ProbComp.eval (E.keyGen n)).support
    · rw [← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ zero_le
      have hci :
          ((ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ciEncryptionOracle n k q s))
              (adversary n []) []).bind
            (fun out => PMF.pure (!out.2.contains out.1 && (E.decrypt n k out.1).isSome))) =
          (ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ciPairOracle n k q s))
              (adversary n []) []).map
            (fun (ctStar, pairs) =>
              !(pairs.map Prod.snd).contains ctStar && (E.decrypt n k ctStar).isSome) := by
        rw [← ProbOracleComp.eval_run_interpret_eq_runWith,
          E.eval_run_ciEncryptionOracle_eq_map_snd_ciPairOracle,
          ProbOracleComp.eval_run_interpret_eq_runWith, PMF.bind_map, PMF.map]
        rfl
      have hcca :
          ((ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ccaOracle n k false q s))
              (ciToCCAAdversary ctBound Q adversary n []) []).bind
            (fun out => PMF.pure out.1)) =
          (BitString.uniformList (Q n * n)).bind (fun rawBits =>
            (ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ciPairOracle n k q s))
                (adversary n []) []).map
              (fun (ctStar, pairs) =>
                !(pairs.map Prod.snd).contains ctStar &&
                  ((E.decrypt n k ctStar).isSome &&
                    !(chunksBelow rawBits n pairs.length).contains
                      ((E.decrypt n k ctStar).getD [])))) := by
        unfold ciToCCAAdversary
        rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample,
          BitString.eval_sampleList, PMF.bind_map]
        dsimp only [Function.comp_def]
        rw [PMF.bind_bind]
        refine PMF.bind_congr_on_support _ _ _ fun rawBits _ => ?_
        rw [ProbOracleComp.runWith_bind,
          eval_run_ciToCCAHandler_false E n (ctBound n) k rawBits hk hctBound
            (adversary n []),
          PMF.bind_map, PMF.bind_bind, PMF.map]
        refine PMF.bind_congr_on_support _ _ _ ?_
        rintro ⟨ctStar, pairs⟩ _
        have hr : ∀ r ∈ chunksBelow rawBits n pairs.length, r.length = n := by
          intro r hr
          obtain ⟨i, _, rfl⟩ := mem_chunksBelow.mp hr
          exact BitString.length_listRow _ _ _
        simp only [Function.comp_def]
        rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query]
        have hdec := decCheck_eq E n k ctStar _ hr (pairs.map Prod.snd)
        simp only [SymmetricCipher.ccaOracle, ↓reduceIte, ProbOracleComp.runWith_pure,
          PMF.bind_map, PMF.bind_bind]
        dsimp only at hdec
        by_cases hmem : (pairs.map Prod.snd).contains ctStar
        · simp only [hmem, ↓reduceIte, ProbComp.eval_pure, PMF.pure_bind, Function.comp_def,
            Prod.map_apply, id_eq] at hdec ⊢
          exact congrArg PMF.pure hdec
        · simp only [hmem, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure, PMF.pure_bind,
            Function.comp_def, Prod.map_apply, id_eq] at hdec ⊢
          exact congrArg PMF.pure hdec
      rw [hci, hcca]
      refine map_true_le_bind_add _ _ _ _
        (fun rawBits (out : List Bool × List (List Bool × List Bool)) =>
          (chunksBelow rawBits n out.2.length).contains ((E.decrypt n k out.1).getD [])) _
        ?_ ?_
      · rintro rawBits ⟨ctStar, pairs⟩ _ hwin
        simp only [Bool.and_eq_true] at hwin
        by_cases hbad :
            (chunksBelow rawBits n pairs.length).contains ((E.decrypt n k ctStar).getD []) = true
        · exact Or.inr hbad
        · left
          simp only [Bool.not_eq_true] at hbad
          simp only [hwin.1, hwin.2, hbad, Bool.not_false, Bool.and_self]
      · rintro ⟨ctStar, pairs⟩ hmem
        refine uniformList_chunksBelow_contains_le (Q n) n pairs.length ?_ _
        exact length_le_of_mem_support_runWith_ciPairOracle E n (Q n) k hq hmem
    · have hk0 : (ProbComp.eval (E.keyGen n)) k = 0 :=
        not_not.mp ((PMF.mem_support_iff _ _).not.mp hk)
      simp [hk0]
  have hleNN :
      Game.succProbability (ProbComp.eval (E.ciGame adversary n)) ≤
        Game.succProbability (ProbComp.eval
          (E.ccaGame (ciToCCAAdversary ctBound Q adversary) false n)) +
        ((Q n : ENNReal) / (2 : ENNReal) ^ n).toNNReal := by
    refine (ENNReal.toNNReal_mono
      (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ true, hfin⟩) hleENN).trans ?_
    rw [ENNReal.toNNReal_add (PMF.apply_ne_top _ true) hfin]
  have hnnEq :
      ((Q n : ENNReal) / (2 : ENNReal) ^ n).toNNReal = (Q n : ℝ≥0) / (2 : ℝ≥0) ^ n := by
    rw [ENNReal.toNNReal_div, ENNReal.toNNReal_natCast, ENNReal.toNNReal_pow,
      ENNReal.toNNReal_ofNat]
  rw [hnnEq] at hleNN
  exact_mod_cast hleNN

private noncomputable def ccaTruePairOracle (E : SymmetricCipher) (n ctBound : ℕ) (k : List Bool)
    (rawBits : List Bool) (request : Unit × List Bool) :
    StateT (ℕ × List (List Bool) × List (List Bool)) ProbComp (List Bool) :=
  fun (idx, rUsed, cts) =>
    if request.2.length == n then do
      let r := BitString.listRow n idx rawBits
      let ct ← E.encrypt n k r
      return (ct.take ctBound, (idx + 1, r :: rUsed, ct :: cts))
    else
      return ([], (idx, rUsed, cts))

private theorem length_of_mem_support_ccaTruePairOracle (E : SymmetricCipher) (n ctBound : ℕ)
    (k : List Bool) (rawBits : List Bool) (prog : WordOracleComp Unit (List Bool))
    (ctStar : List Bool) (st : ℕ × List (List Bool) × List (List Bool))
    (hmem : (ctStar, st) ∈ (ProbOracleComp.runWith
      (fun q s => ProbComp.eval (ccaTruePairOracle E n ctBound k rawBits q s))
      prog (0, [], [])).support) :
    ∀ r ∈ st.2.1, r.length = n := by
  refine ProbOracleComp.runWith_invariant
    (fun q s => ProbComp.eval (ccaTruePairOracle E n ctBound k rawBits q s))
    (fun s => ∀ r ∈ s.2.1, r.length = n) ?_ prog (0, [], []) (by simp) ctStar st hmem
  intro ⟨⟨⟩, msg⟩ ⟨idx0, rUsed0, cts0⟩ hr0 a st' hstep
  unfold ccaTruePairOracle at hstep
  split_ifs at hstep
  · simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at hstep
    obtain ⟨ct, _, hstepEq⟩ := hstep
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hstepEq
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr'
    · exact BitString.length_listRow _ _ _
    · exact hr0 r hr'
  · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hstep
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hstep
    exact hr0

private theorem eval_run_ccaTruePairOracle_proj_cca (E : SymmetricCipher) (n ctBound : ℕ)
    (k : List Bool) (rawBits : List Bool) (prog : WordOracleComp Unit (List Bool)) :
    ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ccaOracle n k true q s))
      ((OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
          (ciToCCAHandler n ctBound rawBits)) prog).run (0, [])) [] =
    (ProbOracleComp.runWith
      (fun q s => ProbComp.eval (ccaTruePairOracle E n ctBound k rawBits q s))
      prog (0, [], [])).map
      (fun (ctStar, (idx, rUsed, cts)) => ((ctStar, (idx, rUsed)), cts)) := by
  refine ProbOracleComp.runWith_run_interpret_map (ciToCCAHandler n ctBound rawBits)
    (fun q s => ProbComp.eval (E.ccaOracle n k true q s))
    (fun q s => ProbComp.eval (ccaTruePairOracle E n ctBound k rawBits q s))
    (fun (idx, rUsed, _) => (idx, rUsed))
    (fun (_, _, cts) => cts)
    ?_ prog (0, [], [])
  intro ⟨⟨⟩, msg⟩ ⟨idx, rUsed, cts⟩
  unfold ccaTruePairOracle ciToCCAHandler
  by_cases hlen : msg.length = n
  · have hbeq : (msg.length == n) = true := beq_iff_eq.mpr hlen
    have hchunkLen : (BitString.listRow n idx rawBits).length = n :=
      BitString.length_listRow n idx rawBits
    simp only [StateT.run, ↓reduceIte, SymmetricCipher.ccaOracle, Bool.false_eq_true,
      unframe_encPair_encBits, dropFrame_encPair_encBits, hlen, hchunkLen, beq_self_eq_true,
      Bool.and_self, ProbComp.eval_bind, ProbComp.eval_pure,
      ProbOracleComp.runWith_bind, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
      ProbOracleComp.runWith_pure, PMF.bind_bind, PMF.map_bind, PMF.pure_bind,
      PMF.pure_map, Prod.map_apply, id_eq]
  · have hbeq : (msg.length == n) = false := beq_false_of_ne hlen
    simp only [StateT.run, hbeq, Bool.false_eq_true, ↓reduceIte,
      ProbOracleComp.runWith_pure, ProbComp.eval_pure, PMF.pure_map]

private theorem eval_run_ccaTruePairOracle_proj_encForge (E : SymmetricCipher) (n ctBound : ℕ)
    (k : List Bool) (rawBits : List Bool) (prog : WordOracleComp Unit (List Bool)) :
    ProbOracleComp.runWith (fun q s => ProbComp.eval (E.encForgeOracle n k q s))
      ((OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
          (ciToRandEncForgeHandler n ctBound rawBits)) prog).run 0) [] =
    (ProbOracleComp.runWith
      (fun q s => ProbComp.eval (ccaTruePairOracle E n ctBound k rawBits q s))
      prog (0, [], [])).map
      (fun (ctStar, (idx, rUsed, _)) => ((ctStar, idx), rUsed)) := by
  refine ProbOracleComp.runWith_run_interpret_map (ciToRandEncForgeHandler n ctBound rawBits)
    (fun q s => ProbComp.eval (E.encForgeOracle n k q s))
    (fun q s => ProbComp.eval (ccaTruePairOracle E n ctBound k rawBits q s))
    (fun (idx, _, _) => idx)
    (fun (_, rUsed, _) => rUsed)
    ?_ prog (0, [], [])
  intro ⟨⟨⟩, msg⟩ ⟨idx, rUsed, cts⟩
  unfold ccaTruePairOracle ciToRandEncForgeHandler
  by_cases hlen : msg.length = n
  · have hbeq : (msg.length == n) = true := beq_iff_eq.mpr hlen
    have hchunkLen : (BitString.listRow n idx rawBits).length = n :=
      BitString.length_listRow n idx rawBits
    simp only [StateT.run, hbeq, ↓reduceIte, SymmetricCipher.encForgeOracle, hchunkLen,
      beq_self_eq_true, ProbComp.eval_bind, ProbComp.eval_pure, ProbOracleComp.runWith_bind,
      ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure,
      PMF.bind_bind, PMF.map_bind, PMF.pure_bind, PMF.pure_map,
      Prod.map_apply, id_eq]
  · have hbeq : (msg.length == n) = false := beq_false_of_ne hlen
    simp only [StateT.run, hbeq, Bool.false_eq_true, ↓reduceIte,
      ProbOracleComp.runWith_pure, ProbComp.eval_pure, PMF.pure_map]

/-- In the `true` world, `ciToCCAAdversary` outputs `true` only when `ciToRandEncForgeAdversary`
wins the plaintext-integrity game on the same key, random messages and forgery. -/
private theorem succProbability_ccaGame_ciToCCA_true_le (E : SymmetricCipher)
    (ctBound Q : ℕ → ℕ) (adversary : CIAdversary) (n : ℕ) :
    (Game.succProbability (ProbComp.eval
        (E.ccaGame (ciToCCAAdversary ctBound Q adversary) true n)) : ℝ) ≤
      (Game.succProbability (ProbComp.eval
        (E.encForgeGame (ciToRandEncForgeAdversary ctBound Q adversary) n)) : ℝ) := by
  have hleENN :
      (ProbComp.eval (E.ccaGame (ciToCCAAdversary ctBound Q adversary) true n)) true ≤
        (ProbComp.eval
          (E.encForgeGame (ciToRandEncForgeAdversary ctBound Q adversary) n)) true := by
    simp only [SymmetricCipher.ccaGame, SymmetricCipher.encForgeGame,
      ProbComp.eval_bind, ProbComp.eval_pure, ProbOracleComp.eval_run_interpret_eq_runWith]
    rw [PMF.bind_apply, PMF.bind_apply]
    refine tsum_le_tsum fun k => mul_le_mul_of_nonneg_left ?_ zero_le
    have hsub1 :
        ((ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ccaOracle n k true q s))
            (ciToCCAAdversary ctBound Q adversary n []) []).bind
          (fun out => PMF.pure out.1)) =
        (BitString.uniformList (Q n * n)).bind (fun rawBits =>
          (ProbOracleComp.runWith
            (fun q s => ProbComp.eval (ccaTruePairOracle E n (ctBound n) k rawBits q s))
            (adversary n []) (0, [], [])).map
            (fun (ctStar, (_, rUsed, cts)) =>
              !cts.contains ctStar &&
                ((E.decrypt n k ctStar).isSome &&
                  !rUsed.contains ((E.decrypt n k ctStar).getD [])))) := by
      unfold ciToCCAAdversary
      rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample,
        BitString.eval_sampleList, PMF.bind_map, PMF.bind_bind]
      dsimp only [Function.comp_def]
      refine PMF.bind_congr_on_support _ _ _ fun rawBits _ => ?_
      rw [ProbOracleComp.runWith_bind,
        eval_run_ccaTruePairOracle_proj_cca E n (ctBound n) k rawBits (adversary n []),
        PMF.bind_map, PMF.bind_bind, PMF.map]
      refine PMF.bind_congr_on_support _ _ _ fun st hst => ?_
      rcases st with ⟨ctStar, idx, rUsed, cts⟩
      have hr := length_of_mem_support_ccaTruePairOracle E n (ctBound n) k rawBits
        (adversary n []) ctStar (idx, rUsed, cts) hst
      simp only [Function.comp_def]
      rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query]
      have hdec := decCheck_eq E n k ctStar rUsed hr cts
      simp only [SymmetricCipher.ccaOracle, ↓reduceIte, ProbOracleComp.runWith_pure,
        PMF.bind_map, PMF.bind_bind]
      dsimp only at hdec
      by_cases hmem : cts.contains ctStar
      · simp only [hmem, ↓reduceIte, ProbComp.eval_pure, PMF.pure_bind, Function.comp_def,
          Prod.map_apply, id_eq] at hdec ⊢
        exact congrArg PMF.pure hdec
      · simp only [hmem, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure, PMF.pure_bind,
          Function.comp_def, Prod.map_apply, id_eq] at hdec ⊢
        exact congrArg PMF.pure hdec
    have hsub2 :
        ((ProbOracleComp.runWith (fun q s => ProbComp.eval (E.encForgeOracle n k q s))
            (ciToRandEncForgeAdversary ctBound Q adversary n []) []).bind
          (fun out => PMF.pure
            ((E.decrypt n k out.1).isSome &&
              !out.2.contains ((E.decrypt n k out.1).getD [])))) =
        (BitString.uniformList (Q n * n)).bind (fun rawBits =>
          (ProbOracleComp.runWith
            (fun q s => ProbComp.eval (ccaTruePairOracle E n (ctBound n) k rawBits q s))
            (adversary n []) (0, [], [])).map
            (fun (ctStar, (_, rUsed, _)) =>
              (E.decrypt n k ctStar).isSome &&
                !rUsed.contains ((E.decrypt n k ctStar).getD []))) := by
      unfold ciToRandEncForgeAdversary
      rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample,
        BitString.eval_sampleList, PMF.bind_map, PMF.bind_bind]
      dsimp only [Function.comp_def]
      refine PMF.bind_congr_on_support _ _ _ fun rawBits _ => ?_
      rw [ProbOracleComp.runWith_bind,
        eval_run_ccaTruePairOracle_proj_encForge E n (ctBound n) k rawBits (adversary n []),
        PMF.bind_map, PMF.bind_bind, PMF.map]
      simp only [Function.comp_def, ProbOracleComp.runWith_pure, PMF.pure_bind]
    rw [hsub1, hsub2, PMF.bind_apply, PMF.bind_apply]
    refine tsum_le_tsum fun rawBits => mul_le_mul_of_nonneg_left ?_ zero_le
    refine Cslib.Probability.PMF.map_true_mono _ ?_
    rintro ⟨ctStar, idx, rUsed, cts⟩ _ hwin
    simp only [Bool.and_eq_true] at hwin ⊢
    exact hwin.2
  have hleNN :
      Game.succProbability (ProbComp.eval
        (E.ccaGame (ciToCCAAdversary ctBound Q adversary) true n)) ≤
      Game.succProbability (ProbComp.eval
        (E.encForgeGame (ciToRandEncForgeAdversary ctBound Q adversary) n)) :=
    ENNReal.toNNReal_mono (PMF.apply_ne_top _ true) hleENN
  exact_mod_cast hleNN

/-- **Concrete bound for Exercise 9.15(b).** For a `Q`-query CI adversary and a ciphertext-length
bound `ctBound`, the CI advantage is at most the plaintext-integrity advantage of
`ciToRandEncForgeAdversary`, plus the CCA advantage of `ciToCCAAdversary`, plus `Q n / 2^n`. -/
theorem succProbability_ciGame_le_encForge_add_indcca (E : SymmetricCipher)
    (ctBound Q : ℕ → ℕ) (adversary : CIAdversary) (n : ℕ)
    (hq : (adversary n []).IsQueryBounded (Q n))
    (hctBound : E.CiphertextLengthLE n (ctBound n)) :
    (Game.succProbability (ProbComp.eval (E.ciGame adversary n)) : ℝ) ≤
      (Game.succProbability (ProbComp.eval
        (E.encForgeGame (ciToRandEncForgeAdversary ctBound Q adversary) n)) : ℝ) +
      (Game.advantage
        (ProbComp.eval (E.ccaGame (ciToCCAAdversary ctBound Q adversary) false n))
        (ProbComp.eval (E.ccaGame (ciToCCAAdversary ctBound Q adversary) true n)) : ℝ) +
      (Q n : ℝ) / (2 : ℝ) ^ n := by
  have h1 := succProbability_ciGame_le_ccaFalse E ctBound Q adversary n hq hctBound
  have h2 := succProbability_ccaGame_ciToCCA_true_le E ctBound Q adversary n
  have hccaAdv :
      (Game.succProbability (ProbComp.eval
        (E.ccaGame (ciToCCAAdversary ctBound Q adversary) false n)) : ℝ) -
      (Game.succProbability (ProbComp.eval
        (E.ccaGame (ciToCCAAdversary ctBound Q adversary) true n)) : ℝ) ≤
      (Game.advantage
        (ProbComp.eval (E.ccaGame (ciToCCAAdversary ctBound Q adversary) false n))
        (ProbComp.eval (E.ccaGame (ciToCCAAdversary ctBound Q adversary) true n)) : ℝ) := by
    change _ ≤ dist (Game.succProbability _) (Game.succProbability _)
    rw [NNReal.dist_eq]
    exact le_abs_self _
  linarith

/-- **CCA security and plaintext integrity imply ciphertext integrity** ([BonehShoup2023],
Exercise 9.15(b), printed p. 395). -/
theorem INDCCA.ciphertextIntegrity {E : SymmetricCipher}
    (hcca : E.INDCCA) (hef : E.EncForge) : E.CiphertextIntegrity := by
  refine SymmetricCipher.CiphertextIntegrity.of_negligible fun adversary hadversary => ?_
  obtain ⟨ctBound, hctBoundPoly, hctBound⟩ := E.exists_ciphertext_length_bound_of_length_eq
  obtain ⟨cq, dq, hqbounds⟩ := hadversary.query_bounds
  let Q : ℕ → ℕ := fun n => cq * (n + 2) ^ dq
  have hQPoly : ComputableInPolyTime Q encUnary encUnary := by
    dsimp only [Q]; fun_prop
  have hq (n : ℕ) : (adversary n []).IsQueryBounded (Q n) := by
    simpa only [Q, List.length_nil, Nat.add_zero] using (hqbounds n []).1
  have hEF : Negligible (fun n =>
      Game.succProbability (ProbComp.eval
        (E.encForgeGame (ciToRandEncForgeAdversary ctBound Q adversary) n))) := by
    simpa only [Game.advantage_pure_false] using
      hef (ciToRandEncForgeAdversary ctBound Q adversary)
        (isOraclePPT_ciToRandEncForgeAdversary hctBoundPoly hQPoly hadversary)
  have hCCA : Negligible (fun n =>
      Game.advantage
        (ProbComp.eval (E.ccaGame (ciToCCAAdversary ctBound Q adversary) false n))
        (ProbComp.eval (E.ccaGame (ciToCCAAdversary ctBound Q adversary) true n))) :=
    hcca (ciToCCAAdversary ctBound Q adversary)
      (isOraclePPT_ciToCCAAdversary hctBoundPoly hQPoly hadversary)
  have hColl : Negligible (fun n => (Q n : ℝ≥0) / (2 : ℝ≥0) ^ n) := by
    dsimp only [Q]
    push_cast
    negligible
  have hbound (n : ℕ) :
      (Game.succProbability (ProbComp.eval (E.ciGame adversary n)) : ℝ) ≤
        (Game.succProbability (ProbComp.eval
          (E.encForgeGame (ciToRandEncForgeAdversary ctBound Q adversary) n)) : ℝ) +
        (Game.advantage
          (ProbComp.eval (E.ccaGame (ciToCCAAdversary ctBound Q adversary) false n))
          (ProbComp.eval (E.ccaGame (ciToCCAAdversary ctBound Q adversary) true n)) : ℝ) +
        (((Q n : ℝ≥0) / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := by
    simpa only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat] using
      succProbability_ciGame_le_encForge_add_indcca E ctBound Q adversary n (hq n) (hctBound n)
  negligible using hbound

/-- **CCA security and plaintext integrity imply authenticated encryption** ([BonehShoup2023],
Exercise 9.15(b), printed p. 395). -/
theorem INDCCA.authenticatedEncryption {E : SymmetricCipher}
    (hcca : E.INDCCA) (hef : E.EncForge) : E.AuthenticatedEncryption :=
  ⟨hcca.indcpa, hcca.ciphertextIntegrity hef⟩

end SymmetricCipher

end Cslib.Crypto
