/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Computational.Encryption.Authenticated
public import CslibFrontier.Languages.Probabilistic.Oracle.RunState
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.ListCollision
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair.Projections
import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.Oracle.Support
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Support
import CslibFrontier.Tactic.PPT

/-!
# Repeating Ciphertexts under Chosen-Plaintext Attack

This module formalizes Exercise 5.12 of
[Boneh and Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023]
(Chapter 5, printed p. 211; Example 5.1's deterministic-cipher refutation
`not_indcpa_of_deterministic` lives in
`CslibFrontier/Crypto/Computational/Encryption/Authenticated.lean`):

* **CPA security prevents ciphertext collisions (`repeatCiphertextGame`, `repeatToCPAAdversary`,
  `succProbability_repeatCiphertextGame_le_two_mul_advantage`,
  `INDCPA.negligible_repeatCiphertextGame`)**: in `repeatCiphertextGame`, an adaptive oracle
  adversary queries `E`'s encryption oracle (`E.ciEncryptionOracle n k`) on chosen `n`-bit messages
  and wins if any two returned ciphertexts are equal (`!decide out.2.Nodup`). An elementary CPA
  wrapper `repeatToCPAAdversary` forwards each `n`-bit query `m` as `(m, r)` for a freshly sampled
  uniform `r ← BitString.sampleList n`, records `(c, r)` pairs, and outputs `true` iff two recorded
  entries have equal ciphertexts and distinct random right-hand messages
  (`p.1 == q.1 && p.2 != q.2`). In Experiment `true` (`b = 1`), decryption completeness forces
  `p.1 = q.1 → p.2 = q.2`, so the wrapper outputs `true` with probability `0`; in Experiment `false`
  (`b = 0`) for `n ≥ 1` (`|M| = 2^n ≥ 2`), every ciphertext collision in `repeatCiphertextGame`
  receives distinct independent `r` values with probability `1 - 2^{-n} ≥ 1/2`. Thus
  `RepeatAdv[A, E] ≤ 2 · CPAadv[B, E]`, and `E.INDCPA` implies negligible winning probability in
  `repeatCiphertextGame` for every `IsOraclePPT` adversary.

## Model and scope notes relative to Boneh–Shoup

* **`n`-bit message space and threshold `1 ≤ n`.** In `SymmetricCipher`, the message space at
  security parameter `n` is `{0, 1}^n` of size `2^n`, sampled uniformly in polynomial time via
  `BitString.sampleList n`. Exercise 5.12's hypotheses ("Assume that there are at least two
  messages in `M`, that all messages have the same length, and that we can efficiently generate
  messages in `M` uniformly at random", printed p. 211) correspond quantitatively to `1 ≤ n`,
  which disappears in the asymptotic `Negligible` conclusion.
* **Polymorphic adversary return type in `repeatCiphertextGame`.** Because winning
  `repeatCiphertextGame` depends only on the oracle's ciphertext log and ignores the adversary's
  final output value, `repeatCiphertextGame`, `repeatToCPAAdversary`, and
  `INDCPA.negligible_repeatCiphertextGame` are polymorphic in `{α : Type}` (`IsOraclePPT encOut A`),
  so callers with `OracleDistinguisher` (`α = Bool`), `CIAdversary` (`α = List Bool`), or `Unit`
  adversaries apply them directly without wrapping return values.

## Main definitions

* `Cslib.Crypto.SymmetricCipher.repeatCiphertextGame`: adaptive repeated-ciphertext attack game
  ([BonehShoup2023], Exercise 5.12, printed p. 211).
* `Cslib.Crypto.SymmetricCipher.repeatToCPAAdversary`: elementary CPA wrapper around a
  repeated-ciphertext adversary ([BonehShoup2023], Exercise 5.12, printed p. 211).

## Main results

* `Cslib.Crypto.SymmetricCipher.isOraclePPT_repeatToCPAAdversary`: strict uniform oracle-PPT
  certificate for `repeatToCPAAdversary`.
* `Cslib.Crypto.SymmetricCipher.succProbability_repeatCiphertextGame_le_two_mul_advantage`,
  `Cslib.Crypto.SymmetricCipher.INDCPA.negligible_repeatCiphertextGame`: quantitative reduction
  `RepeatAdv[A, E] ≤ 2 · CPAadv[B, E]` and asymptotic repeated-ciphertext security from `INDCPA`
  ([BonehShoup2023], Exercise 5.12, printed p. 211).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 5.3, Example 5.1 (p. 182) and Section 5.8, Exercise 5.12
  (p. 211).
-/

public section

namespace Cslib.Crypto.SymmetricCipher

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

/-- The repeated-ciphertext attack experiment ([BonehShoup2023], Exercise 5.12, printed p. 211):
sample `k ← E.keyGen n`, run `A n []` against `E.ciEncryptionOracle n k` starting from `[]` (which
encrypts each `n`-bit query under `k`, logs the returned ciphertexts, and answers malformed queries
with `[]` without logging), and output `true` iff two logged ciphertexts are equal
(`!decide out.2.Nodup`). -/
@[expose] noncomputable def repeatCiphertextGame {α : Type} (E : SymmetricCipher)
    (A : ℕ → List Bool → WordOracleComp Unit α) (n : ℕ) : Game := do
  let k ← ProbComp.eval (E.keyGen n)
  let out ← ProbComp.eval (((A n []).runState (E.ciEncryptionOracle n k)).run [])
  return !decide out.2.Nodup

/-- Stateful handler for `repeatToCPAAdversary` ([BonehShoup2023], Exercise 5.12, printed p. 211):
on an `n`-bit query `m`, sample a uniform `n`-bit string `r ← BitString.sampleList n`, query the
left-or-right CPA oracle on `(m, r)`, truncate the reply to `bound` bits, and prepend `(c, r)` to
`seen`; answer malformed queries (`request.2.length ≠ n`) with `[]` without modifying `seen`. -/
private noncomputable def repeatWrapperStep (n bound : ℕ) (request : Unit × List Bool) :
    StateT (List (List Bool × List Bool)) (WordOracleComp Unit) (List Bool) :=
  fun seen =>
    if request.2.length == n then do
      let r ← ProbOracleComp.sample (BitString.sampleList n)
      let c ← List.take bound <$>
        ProbOracleComp.query ((), encPair encBits encBits (request.2, r))
      return (c, (c, r) :: seen)
    else
      pure ([], seen)

/-- Elementary CPA wrapper around a repeated-ciphertext adversary `A` ([BonehShoup2023],
Exercise 5.12, printed p. 211): run `A n []` against `repeatWrapperStep n (ctBound n)` starting from
`[]`, and output `true` iff two recorded `(ciphertext, randomMsg)` pairs share the same truncated
ciphertext while having distinct right-hand random messages. -/
noncomputable def repeatToCPAAdversary {α : Type} (ctBound : ℕ → ℕ)
    (A : ℕ → List Bool → WordOracleComp Unit α) : OracleDistinguisher :=
  fun n _ => do
    let out ← (OracleComp.interpret
      (OracleComp.sumHandler
        (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
        (repeatWrapperStep n (ctBound n)))
      (A n [])).run []
    return hasDistinctCollision out.2

/-- `repeatToCPAAdversary ctBound A` is uniformly strict oracle-PPT whenever `ctBound` is
computable in unary polynomial time and `A` is uniformly strict oracle-PPT. -/
theorem isOraclePPT_repeatToCPAAdversary {α : Type} {encOut : α ↪ List Bool}
    {ctBound : ℕ → ℕ} (hctBound : ComputableInPolyTime ctBound encUnary encUnary)
    {A : ℕ → List Bool → WordOracleComp Unit α} (hA : IsOraclePPT encOut A) :
    IsOraclePPT encBool (repeatToCPAAdversary ctBound A) := by
  let EState := encList (encPair encBits encBits)
  let EIn := encHandlerCall (encPair encUnary encBits) (encFinEnum Unit) EState
  have hhandler : IsOraclePPTOn EIn (encPair encBits EState)
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool × List Bool)) =>
        repeatWrapperStep p.1.1 (ctBound p.1.1) p.2.1 p.2.2) := by
    unfold repeatWrapperStep
    dsimp only [EIn, encHandlerCall, EState]
    exact IsOraclePPTOn.cond (by fun_prop) (by ppt)
      ((ComputableInPolyTime.const []).prod (by fun_prop)).isOraclePPTOn (Operation := Unit)
  have hrun : IsOraclePPTOn (encPair encUnary encBits) (encPair encOut EState)
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (repeatWrapperStep caller.1 (ctBound caller.1)))
          (A caller.1 [])).run []) := by
    apply hA.run_interpret_preprocess_open
      (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
      (initial := fun _ => ([] : List (List Bool × List Bool)))
      (resources := fun caller _ => 4 * ctBound caller.1 + 2 * caller.1 + 6)
      (by fun_prop) hhandler (ComputableInPolyTime.const [])
      (fun _ _ => True) (fun _ => trivial) (by fun_prop)
    intro caller request seen _ result hresult
    unfold repeatWrapperStep at hresult
    split_ifs at hresult with hlenEq
    · obtain ⟨r, hr, hresult⟩ := OracleComp.mem_supportWith_bind_iff.mp hresult
      have hrLen : r.length = caller.1 := BitString.length_of_mem_support_uniformList <| by
        rwa [← BitString.eval_sampleList, ← ProbOracleComp.support_sample]
      obtain ⟨c, hc, hresult⟩ := OracleComp.mem_supportWith_bind_iff.mp hresult
      obtain ⟨rawCt, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hc
      cases OracleComp.eq_of_mem_supportWith_pure hresult
      refine ⟨trivial, (List.length_take_le _ _).trans (by omega), ?_⟩
      have := List.length_take_le (ctBound caller.1) rawCt
      simp only [EState, encList_cons, List.length_append, length_encPair, length_frame,
        encBits_apply, hrLen]
      omega
    · cases OracleComp.eq_of_mem_supportWith_pure hresult
      exact ⟨trivial, by simp, Nat.le_add_right _ _⟩
  unfold repeatToCPAAdversary
  simpa only [bind_pure_comp] using (IsOraclePPTOn.map hrun
    ((polyTime_hasDistinctCollision encBits encBits).comp
      (ComputableInPolyTime.snd _ _))).isOraclePPT

/-- In Experiment `true` (`b = 1`), every recorded entry `(c, r)` in `repeatToCPAAdversary`
satisfies `c ∈ support(E.encrypt n k r)` when `ctBound n` bounds ciphertext lengths on `n`-bit
messages; decryption completeness therefore forces `p.1 = q.1 → p.2 = q.2`, so
`repeatToCPAAdversary ctBound A` outputs `false` with probability `1`
([BonehShoup2023], Exercise 5.12, printed p. 211). -/
private theorem eval_cpaGame_repeatToCPAAdversary_true {α : Type} (E : SymmetricCipher)
    (ctBound : ℕ → ℕ) (A : ℕ → List Bool → WordOracleComp Unit α) (n : ℕ)
    (hctBound : E.CiphertextLengthLE n (ctBound n)) :
    ProbComp.eval (E.cpaGame (repeatToCPAAdversary ctBound A) true n) = PMF.pure false := by
  simp only [cpaGame, symmetricCPAGameOn, repeatToCPAAdversary, runWith_norm, pmf_norm]
  refine PMF.bind_eq_pure_of_forall_mem_support fun k hk => ?_
  refine PMF.map_eq_pure_iff.mpr fun out hout => ?_
  have hinv := ProbOracleComp.runWith_invariant
    (oracle := fun q seen =>
      OracleComp.evalWith
        (OracleComp.sumHandler ProbComp.unifOracle fun req =>
          ProbComp.eval
            (symmetricCPAReplyOn (fun n m₀ m₁ => (m₀.length == n) && (m₁.length == n))
              E.encrypt n k true req))
        ((repeatWrapperStep n (ctBound n) q).run seen))
    (invariant := fun seen : List (List Bool × List Bool) =>
      ∀ p ∈ seen, p.2.length = n ∧ p.1 ∈ (ProbComp.eval (E.encrypt n k p.2)).support)
    (fun q seen hseen a seen' hstep => by
      change (a, seen') ∈ (OracleComp.evalWith _ (repeatWrapperStep n (ctBound n) q seen)).support
        at hstep
      unfold repeatWrapperStep at hstep
      by_cases hq : (q.2.length == n) = true
      · simp only [hq, ↓reduceIte, runWith_norm, BitString.eval_sampleList, symmetricCPAReplyOn,
          unframe_encPair_encBits, dropFrame_encPair_encBits, pmf_norm,
          PMF.mem_support_bind_iff] at hstep
        obtain ⟨r, hr, hstep⟩ := hstep
        have hrLen : r.length = n := BitString.length_of_mem_support_uniformList hr
        simp only [hrLen, beq_self_eq_true, Bool.and_self, ↓reduceIte, pmf_norm,
          PMF.mem_support_pure_iff] at hstep
        obtain ⟨rawCt, hrawCt, heq⟩ := hstep
        rw [List.take_of_length_le (hctBound k hk r hrLen rawCt hrawCt)] at heq
        obtain ⟨-, rfl⟩ := Prod.mk.inj heq.symm
        exact List.forall_mem_cons.mpr ⟨⟨hrLen, hrawCt⟩, hseen⟩
      · simp only [hq, Bool.false_eq_true, ↓reduceIte, runWith_norm,
          PMF.mem_support_pure_iff] at hstep
        exact (Prod.mk.inj hstep).2 ▸ hseen)
    (A n []) [] (by simp) out.1 out.2 hout
  refine Bool.eq_false_iff.mpr fun hcol => ?_
  simp only [hasDistinctCollision, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
    bne_iff_ne] at hcol
  obtain ⟨p, hp, q, hq, hpq1, hpq2⟩ := hcol
  obtain ⟨hpLen, hpEnc⟩ := hinv p hp
  obtain ⟨hqLen, hqEnc⟩ := hinv q hq
  exact hpq2 <| Option.some.inj <|
    (E.decrypt_encrypt n k hk p.2 hpLen p.1 hpEnc).symm.trans
      (hpq1 ▸ E.decrypt_encrypt n k hk q.2 hqLen q.1 hqEnc)

/-- Pair each logged ciphertext in `cs` independently with a uniform `n`-bit string. -/
private noncomputable def pairWithUniform (n : ℕ) :
    List (List Bool) → PMF (List (List Bool × List Bool))
  | [] => PMF.pure []
  | c :: cs => do
    let seen ← pairWithUniform n cs
    let r ← BitString.uniformList n
    return (c, r) :: seen

private theorem map_fst_of_mem_support_pairWithUniform {n : ℕ} {cs : List (List Bool)}
    {seen : List (List Bool × List Bool)} (h : seen ∈ (pairWithUniform n cs).support) :
    seen.map Prod.fst = cs := by
  induction cs generalizing seen with
  | nil => simp_all [pairWithUniform]
  | cons c rest ih =>
    simp only [pairWithUniform, pmf_norm, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at h
    obtain ⟨prev, hprev, r, -, rfl⟩ := h
    simp [ih hprev]

private theorem hasDistinctCollision_cons_of_true (x : List Bool × List Bool)
    {seen : List (List Bool × List Bool)} (h : hasDistinctCollision seen = true) :
    hasDistinctCollision (x :: seen) = true := by
  simp only [hasDistinctCollision, List.any_eq_true] at h ⊢
  obtain ⟨p, hp, q, hq, hpq⟩ := h
  exact ⟨p, List.mem_cons_of_mem x hp, q, List.mem_cons_of_mem x hq, hpq⟩

private theorem half_le_uniformList_bne {n : ℕ} (hn : 1 ≤ n) (target : List Bool) :
    (1 : ℝ≥0∞) / 2 ≤ ((BitString.uniformList n).map (· != target)) true := by
  have hnot : ((BitString.uniformList n).map (· != target)) true =
      1 - ((BitString.uniformList n).map (· == target)) true := by
    simpa only [bne] using PMF.map_not_true (BitString.uniformList n) (· == target)
  have heq : ((BitString.uniformList n).map (· == target)) true =
      BitString.uniformList n target := by
    rw [PMF.map_apply, tsum_eq_single target fun r hr => by simp [beq_eq_false_iff_ne.mpr hr]]
    simp
  have hle : BitString.uniformList n target ≤ (1 : ℝ≥0∞) / 2 := by
    refine (BitString.uniformList_apply_le n target).trans (ENNReal.div_le_div_left ?_ 1)
    simpa only [pow_one] using pow_le_pow_right' one_le_two hn
  rw [hnot, heq]
  calc (1 : ℝ≥0∞) / 2 = 1 - 1 / 2 := by norm_num
    _ ≤ 1 - BitString.uniformList n target := tsub_le_tsub_left hle 1

/-- When `1 ≤ n` and `cs` has a duplicate ciphertext (`¬ cs.Nodup`), pairing each element of `cs`
with an independent uniform `n`-bit string produces two entries with equal ciphertexts and distinct
random strings with probability at least `1 / 2`. -/
private theorem half_le_map_hasDistinctCollision_pairWithUniform {n : ℕ} (hn : 1 ≤ n)
    {cs : List (List Bool)} (hnd : ¬ cs.Nodup) :
    (1 : ℝ≥0∞) / 2 ≤ ((pairWithUniform n cs).map hasDistinctCollision) true := by
  induction cs with
  | nil => exact absurd List.nodup_nil hnd
  | cons c rest ih =>
    rw [List.nodup_cons, not_and_or, Classical.not_not] at hnd
    rcases hnd with hmem | hndRest
    · simp only [pairWithUniform, pmf_norm]
      refine PMF.le_bind_apply_on_support _ fun seen hseen => ?_
      obtain ⟨p₀, hp₀, hp₀Eq⟩ :=
        List.mem_map.mp (map_fst_of_mem_support_pairWithUniform hseen ▸ hmem)
      refine (half_le_uniformList_bne hn p₀.2).trans <|
        PMF.map_true_mono (F := fun r => hasDistinctCollision ((c, r) :: seen))
          (BitString.uniformList n) fun r _ hr => ?_
      simp only [hasDistinctCollision, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne]
      exact ⟨(c, r), List.mem_cons_self, p₀, List.mem_cons_of_mem _ hp₀, hp₀Eq.symm,
        bne_iff_ne.mp hr⟩
    · refine (ih hndRest).trans ?_
      simp only [pairWithUniform, pmf_norm, PMF.map]
      refine PMF.bind_apply_mono_on_support (pairWithUniform n rest) true fun seen _ => ?_
      cases hcol : hasDistinctCollision seen
      · simp
      · refine PMF.le_bind_apply_on_support (BitString.uniformList n) fun r _ => ?_
        rw [hasDistinctCollision_cons_of_true (c, r) hcol]

/-- In Experiment `false` (`b = 0`) when `ctBound n` bounds ciphertext lengths on `n`-bit messages,
the CPA oracle encrypts only the left message `m` and ignores the freshly sampled `r`, so the
wrapper's output distribution is the ciphertext log of `repeatCiphertextGame` paired independently
with uniform `n`-bit strings via `pairWithUniform n`. -/
private theorem eval_cpaGame_repeatToCPAAdversary_false_eq {α : Type} (E : SymmetricCipher)
    (ctBound : ℕ → ℕ) (A : ℕ → List Bool → WordOracleComp Unit α) (n : ℕ)
    (hctBound : E.CiphertextLengthLE n (ctBound n)) :
    ProbComp.eval (E.cpaGame (repeatToCPAAdversary ctBound A) false n) =
      (ProbComp.eval (E.keyGen n)).bind fun k =>
        (ProbComp.eval (((A n []).runState (E.ciEncryptionOracle n k)).run [])).bind fun out =>
          (pairWithUniform n out.2).map hasDistinctCollision := by
  simp only [cpaGame, symmetricCPAGameOn, repeatToCPAAdversary, ProbOracleComp.eval_runState,
    runWith_norm, pmf_norm]
  refine PMF.bind_congr_on_support _ _ _ fun k hk => ?_
  have hsim := ProbOracleComp.runWith_simulation
    (oracle := fun q cs => ProbComp.eval (E.ciEncryptionOracle n k q cs))
    (oracle' := fun q seen =>
      OracleComp.evalWith
        (OracleComp.sumHandler ProbComp.unifOracle fun req =>
          ProbComp.eval
            (symmetricCPAReplyOn (fun n m₀ m₁ => (m₀.length == n) && (m₁.length == n))
              E.encrypt n k false req))
        ((repeatWrapperStep n (ctBound n) q).run seen))
    (relate := pairWithUniform n)
    (fun q cs => by
      change (ProbComp.eval (E.ciEncryptionOracle n k q cs)).bind
          (fun p => (pairWithUniform n p.2).map (p.1, ·)) =
        (pairWithUniform n cs).bind fun seen =>
          OracleComp.evalWith _ (repeatWrapperStep n (ctBound n) q seen)
      unfold ciEncryptionOracle repeatWrapperStep
      by_cases hq : (q.2.length == n) = true
      · have hqLen : q.2.length = n := beq_iff_eq.mp hq
        simp only [hq, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure, pairWithUniform,
          runWith_norm, BitString.eval_sampleList, symmetricCPAReplyOn, unframe_encPair_encBits,
          dropFrame_encPair_encBits, pmf_norm]
        calc (ProbComp.eval (E.encrypt n k q.2)).bind
              (fun ct => (pairWithUniform n cs).bind fun seen =>
                (BitString.uniformList n).bind fun r => PMF.pure (ct, (ct, r) :: seen))
            = (pairWithUniform n cs).bind fun seen =>
                (ProbComp.eval (E.encrypt n k q.2)).bind fun ct =>
                  (BitString.uniformList n).bind fun r => PMF.pure (ct, (ct, r) :: seen) :=
              PMF.bind_comm _ _ _
          _ = (pairWithUniform n cs).bind fun seen =>
                (BitString.uniformList n).bind fun r =>
                  (ProbComp.eval (E.encrypt n k q.2)).bind fun ct =>
                    PMF.pure (ct, (ct, r) :: seen) := by
              congr 1; funext seen
              exact PMF.bind_comm _ _ _
          _ = _ := by
              refine PMF.bind_congr_on_support _ _ _ fun seen _ => ?_
              refine PMF.bind_congr_on_support _ _ _ fun r hr => ?_
              have hrLen : r.length = n := BitString.length_of_mem_support_uniformList hr
              simp only [hrLen, beq_self_eq_true, Bool.and_self, ↓reduceIte, Bool.false_eq_true,
                pmf_norm]
              refine PMF.bind_congr_on_support _ _ _ fun ct hct => ?_
              rw [List.take_of_length_le (hctBound k hk q.2 hqLen ct hct)]
      · simp [hq, Bool.false_eq_true, runWith_norm, pmf_norm, PMF.map, Function.comp_def])
    (A n []) []
  simpa only [pairWithUniform, PMF.map, pmf_norm] using
    (congrArg (fun d => d.map fun p => hasDistinctCollision p.2) hsim).symm

/-- **Quantitative repeated-ciphertext reduction** ([BonehShoup2023], Exercise 5.12, printed
p. 211): for every `1 ≤ n` (`|M| = 2^n ≥ 2`) where `ctBound n` bounds ciphertext lengths on `n`-bit
messages, `RepeatAdv[A, E](n) ≤ 2 · CPAadv[repeatToCPAAdversary ctBound A, E](n)`. -/
theorem succProbability_repeatCiphertextGame_le_two_mul_advantage {α : Type}
    (E : SymmetricCipher) (ctBound : ℕ → ℕ)
    (A : ℕ → List Bool → WordOracleComp Unit α) {n : ℕ}
    (hn : 1 ≤ n) (hctBound : E.CiphertextLengthLE n (ctBound n)) :
    Game.succProbability (E.repeatCiphertextGame A n) ≤
      2 * Game.advantage
        (ProbComp.eval (E.cpaGame (repeatToCPAAdversary ctBound A) false n))
        (ProbComp.eval (E.cpaGame (repeatToCPAAdversary ctBound A) true n)) := by
  rw [eval_cpaGame_repeatToCPAAdversary_true E ctBound A n hctBound, Game.advantage_pure_false]
  have hle : E.repeatCiphertextGame A n true ≤
      2 * (ProbComp.eval (E.cpaGame (repeatToCPAAdversary ctBound A) false n)) true := by
    rw [eval_cpaGame_repeatToCPAAdversary_false_eq E ctBound A n hctBound, repeatCiphertextGame]
    simp only [pmf_norm, PMF.bind_apply, ← ENNReal.tsum_mul_left]
    refine tsum_le_tsum fun k => tsum_le_tsum fun out => ?_
    suffices hpt : (PMF.pure (!decide out.2.Nodup)) true ≤
        2 * ((pairWithUniform n out.2).map hasDistinctCollision) true by
      calc (ProbComp.eval (E.keyGen n)) k *
            ((ProbComp.eval (((A n []).runState (E.ciEncryptionOracle n k)).run [])) out *
              (PMF.pure (!decide out.2.Nodup)) true)
          ≤ (ProbComp.eval (E.keyGen n)) k *
              ((ProbComp.eval (((A n []).runState (E.ciEncryptionOracle n k)).run [])) out *
                (2 * ((pairWithUniform n out.2).map hasDistinctCollision) true)) :=
            mul_le_mul_right (mul_le_mul_right hpt _) _
        _ = 2 * ((ProbComp.eval (E.keyGen n)) k *
              ((ProbComp.eval (((A n []).runState (E.ciEncryptionOracle n k)).run [])) out *
                ((pairWithUniform n out.2).map hasDistinctCollision) true)) := by ring
    by_cases hnd : out.2.Nodup
    · simp [hnd]
    · simp only [hnd, decide_false, Bool.not_false, PMF.pure_apply_self]
      calc (1 : ℝ≥0∞) = 2 * (1 / 2) := by
            rw [ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
        _ ≤ 2 * ((pairWithUniform n out.2).map hasDistinctCollision) true :=
            mul_le_mul_right (half_le_map_hasDistinctCollision_pairWithUniform hn hnd) 2
  simpa only [Game.succProbability, ENNReal.toNNReal_mul, ENNReal.toNNReal_ofNat] using
    ENNReal.toNNReal_mono (ENNReal.mul_ne_top (by norm_num) (PMF.apply_ne_top _ _)) hle

/-- **CPA-secure symmetric ciphers have negligible ciphertext-collision probability**
([BonehShoup2023], Exercise 5.12, printed p. 211): if `E` satisfies `INDCPA`, then every uniform
strict `IsOraclePPT` adversary wins `repeatCiphertextGame` with negligible probability. -/
theorem INDCPA.negligible_repeatCiphertextGame {α : Type} {encOut : α ↪ List Bool}
    {E : SymmetricCipher} (h : E.INDCPA)
    (A : ℕ → List Bool → WordOracleComp Unit α) (hA : IsOraclePPT encOut A) :
    Negligible fun n => Game.succProbability (E.repeatCiphertextGame A n) := by
  obtain ⟨ctBound, hpoly, hctBound⟩ := E.exists_ciphertext_length_bound_of_length_eq
  have hneg := h (repeatToCPAAdversary ctBound A) (isOraclePPT_repeatToCPAAdversary hpoly hA)
  refine negligible_of_eventually_le
    (hneg.polynomiallyBounded_mul (p := fun _ => 2) (by fun_prop)) ?_
  exact Filter.eventually_atTop.mpr ⟨1, fun n hn =>
    succProbability_repeatCiphertextGame_le_two_mul_advantage E ctBound A hn (hctBound n)⟩

end Cslib.Crypto.SymmetricCipher
