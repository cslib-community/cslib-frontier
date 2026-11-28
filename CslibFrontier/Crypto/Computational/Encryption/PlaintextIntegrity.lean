/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.EncForge
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair.Projections
import CslibFrontier.Crypto.Computational.Encryption.CCAToCPA
import CslibFrontier.Languages.Probabilistic.Norm
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
  have hchunk : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × (ℕ × List (List Bool))) =>
        BitString.listRow p.1.1.1 p.2.2.1 p.1.2) EHandler encBits :=
    ComputableInPolyTime.bitsRowWithInput (by dsimp only [EHandler, ECaller]; fun_prop)
      (by dsimp only [EHandler, EState]; fun_prop) (by dsimp only [EHandler, ECaller]; fun_prop)
  have hhandler : IsOraclePPTOn EHandler (encPair encBits EState)
      (fun p : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × (ℕ × List (List Bool))) =>
        ciToCCAHandler p.1.1.1 (ctBound p.1.1.1) p.1.2 p.2.1 p.2.2) := by
    ppt [ciToCCAHandler]
  have hres : ComputableInPolyTime
      (fun pair : ((ℕ × List Bool) × List Bool) × List Bool =>
        ctBound pair.1.1.1 + 2 * pair.2.length + 4) (encPair ECaller encBits) encUnary := by
    dsimp only [ECaller]; fun_prop
  have hrun : IsOraclePPTOn (Operation := Bool) ECaller (encPair encBits EState)
      (fun caller : (ℕ × List Bool) × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (ciToCCAHandler caller.1.1 (ctBound caller.1.1) caller.2))
          (adversary caller.1.1 [])).run (0, [])) := by
    apply hadversary.run_interpret_preprocess_open (input := ECaller)
      (handler := fun caller => ciToCCAHandler caller.1.1 (ctBound caller.1.1) caller.2)
      (prepare := fun caller => (caller.1.1, ([] : List Bool)))
      (initial := fun _ => (0, ([] : List (List Bool))))
      (resources := fun caller query => ctBound caller.1.1 + 2 * query.length + 4)
      (by dsimp only [ECaller]; fun_prop) hhandler
      (ComputableInPolyTime.const (0, ([] : List (List Bool))))
      (fun _ _ => True) (fun _ => trivial) hres
    intro caller request state _ result hresult
    unfold ciToCCAHandler at hresult
    split_ifs at hresult with hlenEq
    · obtain ⟨ct, hct, hresult⟩ := OracleComp.mem_supportWith_bind_iff.mp hresult
      obtain ⟨_, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hct
      rcases OracleComp.eq_of_mem_supportWith_pure hresult with rfl
      refine ⟨trivial, (List.length_take_le _ _).trans (by lia), ?_⟩
      have hcl : (BitString.listRow caller.1.1 state.1 caller.2).length = request.2.length :=
        (BitString.length_listRow _ _ _).trans (beq_iff_eq.mp hlenEq).symm
      dsimp only [EState]
      enc_len
    · rcases OracleComp.eq_of_mem_supportWith_pure hresult with rfl
      exact ⟨trivial, by simp, by simp⟩
  ppt [ciToCCAAdversary]

/-- `ciToRandEncForgeAdversary` is oracle PPT when the CI adversary is and the bounds `ctBound`
and `Q` are polynomial-time computable. -/
theorem isOraclePPT_ciToRandEncForgeAdversary {ctBound Q : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    {adversary : CIAdversary} (hadversary : IsOraclePPT encBits adversary) :
    IsOraclePPT encBits (ciToRandEncForgeAdversary ctBound Q adversary) := by
  let ECaller := encPair (encPair encUnary encBits) encBits
  let EHandler := encPair ECaller (encPair (encPair (encFinEnum Unit) encBits) encUnary)
  have hchunk : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × ℕ) =>
        BitString.listRow p.1.1.1 p.2.2 p.1.2) EHandler encBits :=
    ComputableInPolyTime.bitsRowWithInput (by dsimp only [EHandler, ECaller]; fun_prop)
      (by dsimp only [EHandler]; fun_prop) (by dsimp only [EHandler, ECaller]; fun_prop)
  have hhandler : IsOraclePPTOn EHandler (encPair encBits encUnary)
      (fun pair : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × ℕ) =>
        ciToRandEncForgeHandler pair.1.1.1 (ctBound pair.1.1.1) pair.1.2 pair.2.1 pair.2.2) := by
    ppt [ciToRandEncForgeHandler]
  have hres : ComputableInPolyTime
      (fun pair : ((ℕ × List Bool) × List Bool) × List Bool => ctBound pair.1.1.1 + 1)
      (encPair ECaller encBits) encUnary := by
    dsimp only [ECaller]; fun_prop
  have hrun : IsOraclePPTOn (Operation := Unit) ECaller (encPair encBits encUnary)
      (fun caller : (ℕ × List Bool) × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (ciToRandEncForgeHandler caller.1.1 (ctBound caller.1.1) caller.2))
          (adversary caller.1.1 [])).run 0) := by
    apply hadversary.run_interpret_preprocess_open (input := ECaller)
      (handler := fun caller => ciToRandEncForgeHandler caller.1.1 (ctBound caller.1.1) caller.2)
      (prepare := fun caller => (caller.1.1, ([] : List Bool))) (initial := fun _ => (0 : ℕ))
      (resources := fun caller _ => ctBound caller.1.1 + 1)
      (by dsimp only [ECaller]; fun_prop) hhandler (ComputableInPolyTime.const (0 : ℕ))
      (fun _ _ => True) (fun _ => trivial) hres
    intro caller request state _ result hresult
    unfold ciToRandEncForgeHandler at hresult
    split_ifs at hresult
    · obtain ⟨ct, hct, hresult⟩ := OracleComp.mem_supportWith_bind_iff.mp hresult
      obtain ⟨_, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hct
      rcases OracleComp.eq_of_mem_supportWith_pure hresult with rfl
      exact ⟨trivial, (List.length_take_le _ _).trans (by lia), by enc_len⟩
    · rcases OracleComp.eq_of_mem_supportWith_pure hresult with rfl
      exact ⟨trivial, by simp, by simp⟩
  ppt [ciToRandEncForgeAdversary]

private theorem contains_take_eq_of_forall_length {msgs : List (List Bool)} {n : ℕ}
    (hm : ∀ m ∈ msgs, m.length = n) (pt : List Bool) :
    msgs.contains (pt.take (n + 1)) = msgs.contains pt := by
  simp only [List.contains_eq_mem, decide_eq_decide]
  constructor <;> intro hmem
  · have hlen := hm _ hmem
    rw [List.length_take] at hlen
    simpa [List.take_of_length_le (by omega : pt.length ≤ n + 1)] using hmem
  · have hlen := hm _ hmem
    simpa [List.take_of_length_le (by omega : pt.length ≤ n + 1)] using hmem

private theorem bind_runWith_ccaDecCheck (E : SymmetricCipher) (n : ℕ) (k : List Bool)
    (bit : Bool) (ctStar : List Bool) (rs queried : List (List Bool))
    (hr : ∀ r ∈ rs, r.length = n) :
    ((ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ccaOracle n k bit q s))
      (do
        let dec ← List.take (n + 2) <$> ProbOracleComp.query (true, ctStar)
        return (dec.take 1 == [true]) && !rs.contains (dec.drop 1))
      queried).bind fun out => PMF.pure out.1) =
    PMF.pure (!queried.contains ctStar &&
      ((E.decrypt n k ctStar).isSome && !rs.contains ((E.decrypt n k ctStar).getD []))) := by
  have hdec :
      (let reply := if queried.contains ctStar then [] else encOption encBits (E.decrypt n k ctStar)
       let dec := reply.take (n + 2)
       (dec.take 1 == [true]) && !rs.contains (dec.drop 1)) =
      (!queried.contains ctStar &&
        ((E.decrypt n k ctStar).isSome && !rs.contains ((E.decrypt n k ctStar).getD []))) := by
    simp only [List.contains_eq_mem]
    by_cases hq : ctStar ∈ queried
    · simp [hq]
    · simp only [hq, decide_false, Bool.not_false, Bool.true_and]
      cases hdec : E.decrypt n k ctStar with
      | none => simp [encOption]
      | some pt =>
        simp only [encOption, encBits_apply, Option.isSome_some, Option.getD_some, Bool.true_and]
        have hc := contains_take_eq_of_forall_length hr pt
        simp only [List.contains_eq_mem, decide_eq_decide] at hc
        simp [List.take_succ_cons, List.drop_succ_cons, hc]
  rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query]
  simp only [SymmetricCipher.ccaOracle, ↓reduceIte, ProbOracleComp.runWith_pure,
    PMF.bind_map, PMF.bind_bind]
  dsimp only at hdec
  cases hmem : queried.contains ctStar <;>
  · simp only [hmem, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure, PMF.pure_bind,
      Function.comp_def, Prod.map_apply, id_eq] at hdec ⊢
    exact congrArg PMF.pure hdec

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
    (fun _ _ _ => by omega) ?_ (by simp) ctStar pairs hmem
  · simpa using h
  · intro rem ⟨⟨⟩, msg⟩ s hs a s' hstep
    unfold SymmetricCipher.ciPairOracle at hstep
    split_ifs at hstep
    · simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
        PMF.mem_support_pure_iff, Prod.mk.injEq] at hstep
      rcases hstep with ⟨_, _, rfl, rfl⟩
      simp only [List.length_cons]; omega
    · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hstep
      rcases hstep with ⟨rfl, rfl⟩
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
    exact ⟨by rintro (rfl | ⟨i, hi, rfl⟩); exacts [⟨k, by omega, rfl⟩, ⟨i, by omega, rfl⟩],
      by rintro ⟨i, hi, rfl⟩
         rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
         exacts [Or.inr ⟨i, hi, rfl⟩, Or.inl rfl]⟩

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
    (fun pairs => pairs.map Prod.snd) ?_ prog []
  intro ⟨⟨⟩, msg⟩ pairs
  unfold SymmetricCipher.ciPairOracle ciToCCAHandler
  by_cases hlen : msg.length = n
  · have hchunkLen : (BitString.listRow n pairs.length rawBits).length = n :=
      BitString.length_listRow n pairs.length rawBits
    simp only [StateT.run, ↓reduceIte, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_map,
      ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure, SymmetricCipher.ccaOracle,
      Bool.false_eq_true, unframe_encPair_encBits, dropFrame_encPair_encBits, hlen, hchunkLen,
      beq_self_eq_true, Bool.and_self, Prod.map_apply, id_eq, pmf_norm]
    refine PMF.bind_congr_on_support _ _ _ fun ct hct => ?_
    simp only [List.take_of_length_le (hctBound k hk msg hlen ct hct),
      List.length_cons, List.map_cons, chunksBelow]
  · simp only [StateT.run, beq_false_of_ne hlen, Bool.false_eq_true, ↓reduceIte,
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
    fun rawBits _ h => by
      obtain ⟨i, hi, heq⟩ := mem_chunksBelow.mp (List.contains_iff_mem.mp h)
      exact List.any_eq_true.mpr ⟨i, List.mem_range.mpr hi, beq_iff_eq.mpr heq⟩
  refine hmono.trans ((Cslib.Probability.PMF.map_any_range_true_le_sum _ L
    (fun i rawBits => BitString.listRow n i rawBits == x)).trans ?_)
  have hterm (i : ℕ) (hi : i ∈ Finset.range L) :
      ((BitString.uniformList (Q * n)).map
        (fun rawBits => BitString.listRow n i rawBits == x)) true ≤ 1 / (2 : ENNReal) ^ n := by
    rw [← Function.comp_def (fun r => r == x), ← PMF.map_comp,
      BitString.uniformList_map_listRow (lt_of_lt_of_le (Finset.mem_range.mp hi) hL),
      PMF.map_apply, tsum_eq_single x (fun r hr => by simp [hr])]
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
  have hswap : ∑' r, u r * (run.map (Bad r)) true =
      (run.bind fun a => u.map fun r => Bad r a) true := by
    rw [← PMF.bind_apply]
    congr 1
    simp only [PMF.map]
    exact PMF.bind_comm _ _ _
  have hbadSum : ∑' r, u r * (run.map (Bad r)) true ≤ ε := by
    rw [hswap, PMF.bind_apply, ← (by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul] :
      ∑' a, run a * ε = ε)]
    exact tsum_le_tsum fun a => by
      by_cases ha : a ∈ run.support
      · exact mul_le_mul_of_nonneg_left (hbad a ha) zero_le
      · simp [not_not.mp ((PMF.mem_support_iff _ _).not.mp ha)]
  rw [← PMF.bind_const u (run.map W), PMF.bind_apply, PMF.bind_apply]
  calc ∑' r, u r * (run.map W) true
      ≤ ∑' r, u r * ((run.map (B r)) true + (run.map (Bad r)) true) :=
        tsum_le_tsum fun r => mul_le_mul_of_nonneg_left
          (Cslib.Probability.PMF.map_true_le_add run (himp r)) zero_le
    _ = ∑' r, u r * (run.map (B r)) true + ∑' r, u r * (run.map (Bad r)) true := by
        simp_rw [mul_add]; exact tsum_add
    _ ≤ ∑' r, u r * (run.map (B r)) true + ε := add_le_add le_rfl hbadSum

private theorem eval_runWith_ccaFalse_ciToCCAAdversary (E : SymmetricCipher)
    (ctBound Q : ℕ → ℕ) (adversary : CIAdversary) (n : ℕ) (k : List Bool)
    (hk : k ∈ (ProbComp.eval (E.keyGen n)).support)
    (hctBound : E.CiphertextLengthLE n (ctBound n)) :
    ((ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ccaOracle n k false q s))
        (ciToCCAAdversary ctBound Q adversary n []) []).bind fun out => PMF.pure out.1) =
      (BitString.uniformList (Q n * n)).bind fun rawBits =>
        (ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ciPairOracle n k q s))
            (adversary n []) []).map fun (ctStar, pairs) =>
          !(pairs.map Prod.snd).contains ctStar &&
            ((E.decrypt n k ctStar).isSome &&
              !(chunksBelow rawBits n pairs.length).contains ((E.decrypt n k ctStar).getD [])) := by
  unfold ciToCCAAdversary
  rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample,
    BitString.eval_sampleList, PMF.bind_map, PMF.bind_bind]
  dsimp only [Function.comp_def]
  refine PMF.bind_congr_on_support _ _ _ fun rawBits _ => ?_
  rw [ProbOracleComp.runWith_bind,
    eval_run_ciToCCAHandler_false E n (ctBound n) k rawBits hk hctBound (adversary n []),
    PMF.bind_map, PMF.bind_bind, PMF.map]
  refine PMF.bind_congr_on_support _ _ _ ?_
  rintro ⟨ctStar, pairs⟩ _
  exact bind_runWith_ccaDecCheck E n k false ctStar (chunksBelow rawBits n pairs.length)
    (pairs.map Prod.snd) fun r hr => by
      obtain ⟨_, _, rfl⟩ := mem_chunksBelow.mp hr; exact BitString.length_listRow _ _ _

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
    have hconst : (Q n : ENNReal) / (2 : ENNReal) ^ n =
        ∑' k, (ProbComp.eval (E.keyGen n)) k * ((Q n : ENNReal) / (2 : ENNReal) ^ n) := by
      rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    rw [PMF.bind_apply, PMF.bind_apply, hconst, ← tsum_add]
    refine tsum_le_tsum fun k => ?_
    by_cases hk : k ∈ (ProbComp.eval (E.keyGen n)).support
    · rw [← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ zero_le
      have hci :
          ((ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ciEncryptionOracle n k q s))
              (adversary n []) []).bind
            (fun out => PMF.pure (!out.2.contains out.1 && (E.decrypt n k out.1).isSome))) =
          (ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ciPairOracle n k q s))
              (adversary n []) []).map fun (ctStar, pairs) =>
            !(pairs.map Prod.snd).contains ctStar && (E.decrypt n k ctStar).isSome := by
        rw [← ProbOracleComp.eval_run_interpret_eq_runWith,
          E.eval_run_ciEncryptionOracle_eq_map_snd_ciPairOracle,
          ProbOracleComp.eval_run_interpret_eq_runWith, PMF.bind_map]; rfl
      rw [hci, eval_runWith_ccaFalse_ciToCCAAdversary E ctBound Q adversary n k hk hctBound]
      refine map_true_le_bind_add _ _ _ _
        (fun rawBits (out : List Bool × List (List Bool × List Bool)) =>
          (chunksBelow rawBits n out.2.length).contains ((E.decrypt n k out.1).getD [])) _
        (fun rawBits ⟨ctStar, pairs⟩ _ hwin => by
          simp only [Bool.and_eq_true] at hwin
          by_cases hbad :
              (chunksBelow rawBits n pairs.length).contains ((E.decrypt n k ctStar).getD []) = true
          · exact Or.inr hbad
          · left; simp only [Bool.not_eq_true] at hbad
            simp only [hwin.1, hwin.2, hbad, Bool.not_false, Bool.and_self])
        fun ⟨_, pairs⟩ hmem => uniformList_chunksBelow_contains_le (Q n) n pairs.length
          (length_le_of_mem_support_runWith_ciPairOracle E n (Q n) k hq hmem) _
    · simp [not_not.mp ((PMF.mem_support_iff _ _).not.mp hk)]
  have hleNN := (ENNReal.toNNReal_mono
    (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ true, hfin⟩) hleENN).trans
    (ENNReal.toNNReal_add (PMF.apply_ne_top _ true) hfin).le
  rw [ENNReal.toNNReal_div, ENNReal.toNNReal_natCast, ENNReal.toNNReal_pow,
    ENNReal.toNNReal_ofNat] at hleNN
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
    obtain ⟨_, _, hstepEq⟩ := hstep
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
    (fun (idx, rUsed, _) => (idx, rUsed)) (fun (_, _, cts) => cts) ?_ prog (0, [], [])
  intro ⟨⟨⟩, msg⟩ ⟨idx, rUsed, cts⟩
  unfold ccaTruePairOracle ciToCCAHandler
  by_cases hlen : msg.length = n
  · have hchunkLen : (BitString.listRow n idx rawBits).length = n :=
      BitString.length_listRow n idx rawBits
    simp only [StateT.run, ↓reduceIte, SymmetricCipher.ccaOracle, Bool.false_eq_true,
      unframe_encPair_encBits, dropFrame_encPair_encBits, hlen, hchunkLen, beq_self_eq_true,
      Bool.and_self, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_map,
      ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure, Prod.map_apply, id_eq, pmf_norm]
  · simp only [StateT.run, beq_false_of_ne hlen, Bool.false_eq_true, ↓reduceIte,
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
    (fun (idx, _, _) => idx) (fun (_, rUsed, _) => rUsed) ?_ prog (0, [], [])
  intro ⟨⟨⟩, msg⟩ ⟨idx, rUsed, cts⟩
  unfold ccaTruePairOracle ciToRandEncForgeHandler
  by_cases hlen : msg.length = n
  · have hchunkLen : (BitString.listRow n idx rawBits).length = n :=
      BitString.length_listRow n idx rawBits
    simp only [StateT.run, beq_iff_eq.mpr hlen, ↓reduceIte, SymmetricCipher.encForgeOracle,
      hchunkLen, beq_self_eq_true, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_map,
      ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure, Prod.map_apply, id_eq, pmf_norm]
  · simp only [StateT.run, beq_false_of_ne hlen, Bool.false_eq_true, ↓reduceIte,
      ProbOracleComp.runWith_pure, ProbComp.eval_pure, PMF.pure_map]

private theorem eval_runWith_ccaTrue_ciToCCAAdversary (E : SymmetricCipher)
    (ctBound Q : ℕ → ℕ) (adversary : CIAdversary) (n : ℕ) (k : List Bool) :
    ((ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ccaOracle n k true q s))
        (ciToCCAAdversary ctBound Q adversary n []) []).bind fun out => PMF.pure out.1) =
      (BitString.uniformList (Q n * n)).bind fun rawBits =>
        (ProbOracleComp.runWith
          (fun q s => ProbComp.eval (ccaTruePairOracle E n (ctBound n) k rawBits q s))
        (adversary n []) (0, [], [])).map fun (ctStar, (_, rUsed, cts)) =>
          !cts.contains ctStar &&
            ((E.decrypt n k ctStar).isSome &&
              !rUsed.contains ((E.decrypt n k ctStar).getD [])) := by
  unfold ciToCCAAdversary
  rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample,
    BitString.eval_sampleList, PMF.bind_map, PMF.bind_bind]
  dsimp only [Function.comp_def]
  refine PMF.bind_congr_on_support _ _ _ fun rawBits _ => ?_
  rw [ProbOracleComp.runWith_bind,
    eval_run_ccaTruePairOracle_proj_cca E n (ctBound n) k rawBits (adversary n []),
    PMF.bind_map, PMF.bind_bind, PMF.map]
  refine PMF.bind_congr_on_support _ _ _ fun ⟨ctStar, idx, rUsed, cts⟩ hst => ?_
  exact bind_runWith_ccaDecCheck E n k true ctStar rUsed cts
    (length_of_mem_support_ccaTruePairOracle E n (ctBound n) k rawBits
      (adversary n []) ctStar (idx, rUsed, cts) hst)

private theorem eval_runWith_encForge_ciToRandEncForgeAdversary (E : SymmetricCipher)
    (ctBound Q : ℕ → ℕ) (adversary : CIAdversary) (n : ℕ) (k : List Bool) :
    ((ProbOracleComp.runWith (fun q s => ProbComp.eval (E.encForgeOracle n k q s))
        (ciToRandEncForgeAdversary ctBound Q adversary n []) []).bind fun out => PMF.pure
        ((E.decrypt n k out.1).isSome && !out.2.contains ((E.decrypt n k out.1).getD []))) =
      (BitString.uniformList (Q n * n)).bind fun rawBits =>
        (ProbOracleComp.runWith
          (fun q s => ProbComp.eval (ccaTruePairOracle E n (ctBound n) k rawBits q s))
          (adversary n []) (0, [], [])).map fun (ctStar, (_, rUsed, _)) =>
          (E.decrypt n k ctStar).isSome &&
            !rUsed.contains ((E.decrypt n k ctStar).getD []) := by
  unfold ciToRandEncForgeAdversary
  rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample,
    BitString.eval_sampleList, PMF.bind_map, PMF.bind_bind]
  simp only [Function.comp_def, ProbOracleComp.runWith_bind,
    eval_run_ccaTruePairOracle_proj_encForge, PMF.bind_bind, PMF.map,
    ProbOracleComp.runWith_pure, PMF.pure_bind]

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
    rw [eval_runWith_ccaTrue_ciToCCAAdversary, eval_runWith_encForge_ciToRandEncForgeAdversary,
      PMF.bind_apply, PMF.bind_apply]
    refine tsum_le_tsum fun rawBits => mul_le_mul_of_nonneg_left ?_ zero_le
    exact Cslib.Probability.PMF.map_true_mono _ fun ⟨ctStar, idx, rUsed, cts⟩ _ hwin =>
      (Bool.and_eq_true _ _ |>.mp hwin).2
  exact_mod_cast ENNReal.toNNReal_mono (PMF.apply_ne_top _ true) hleENN

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
  have hQPoly : ComputableInPolyTime Q encUnary encUnary := by dsimp only [Q]; fun_prop
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
    dsimp only [Q]; push_cast; negligible
  have hbound (n : ℕ) :
      (Game.succProbability (ProbComp.eval (E.ciGame adversary n)) : ℝ) ≤
        (Game.succProbability (ProbComp.eval
          (E.encForgeGame (ciToRandEncForgeAdversary ctBound Q adversary) n)) : ℝ) +
        (Game.advantage
          (ProbComp.eval (E.ccaGame (ciToCCAAdversary ctBound Q adversary) false n))
          (ProbComp.eval (E.ccaGame (ciToCCAAdversary ctBound Q adversary) true n)) : ℝ) +
        (((Q n : ℝ≥0) / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := by
    simpa only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat] using
      succProbability_ciGame_le_encForge_add_indcca E ctBound Q adversary n
        (by simpa only [Q, List.length_nil, Nat.add_zero] using (hqbounds n []).1) (hctBound n)
  negligible using hbound

/-- **CCA security and plaintext integrity imply authenticated encryption** ([BonehShoup2023],
Exercise 9.15(b), printed p. 395). -/
theorem INDCCA.authenticatedEncryption {E : SymmetricCipher}
    (hcca : E.INDCCA) (hef : E.EncForge) : E.AuthenticatedEncryption :=
  ⟨hcca.indcpa, hcca.ciphertextIntegrity hef⟩

end SymmetricCipher

end Cslib.Crypto
