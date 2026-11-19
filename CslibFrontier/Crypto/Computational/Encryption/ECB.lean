/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.Hybrid
public import CslibFrontier.Crypto.Computational.Encryption.SymmetricCPA
public import CslibFrontier.Crypto.Computational.PseudorandomPermutation
public import CslibFrontier.Crypto.Primitives.BlockCipher.ECB
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Traverse
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Crypto.Negligible.InversePolynomial
import CslibFrontier.Foundations.Control.Monad.MapM
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution
import CslibFrontier.Languages.Probabilistic.Oracle.Vector
import CslibFrontier.Tactic.PolyTime

/-!
# ECB mode of a word-level block cipher

The asymptotic form of Boneh–Shoup §4.1.4 ([BonehShoup2023], pp. 102–106) for a uniform block
cipher `E : BlockCipher`. A message word is cut into `blockLen n`-bit blocks, each block is
encrypted under the key, and the results are concatenated (`BlockCipher.ecbEncrypt`). Security is
one-time semantic security, Attack Game 2.1 with a uniform `keyLen n`-bit key
(`Encryption.DEMOneTimeKeyINDCPAOn`), against uniform strict PPT adversaries.

* Theorem 4.1 (pp. 104–106): if `E` is a secure block cipher (`BlockCipher.PRP`), ECB on messages
  of at most `ℓ n` distinct blocks is semantically secure
  (`BlockCipher.PRP.ecb_demOneTimeKeyINDCPAOn`). The reduction `BlockCipher.ecbToPrpDistinguisher`
  runs the typed reduction `ECB.reduction` of `CslibFrontier.Crypto.Primitives.BlockCipher.ECB`
  against the word oracle, and it is uniform strict oracle PPT
  (`BlockCipher.isOraclePPT_ecbToPrpDistinguisher`). At each parameter the advantage is exactly
  twice the block-cipher advantage of that reduction
  (`BlockCipher.advantage_demKeyGameOn_ecbEncrypt`), from the typed equation (4.3).
* Single-block security (pp. 102, 104): when `ℓ n ≤ 1`, every admissible message has at most one
  block, so `ecbValid` coincides with `ecbAdmissible`
  (`BlockCipher.ecbValid_eq_ecbAdmissible_of_le_one`), and at `ℓ = 1` a secure block cipher gives
  semantically secure ECB encryption on `X^{≤1}` (`BlockCipher.PRP.ecb_demOneTimeKeyINDCPAOn_one`).
* Two-block attack (pp. 103–104): on `X^{≤ℓ}`, the uniform strict PPT adversary
  `BlockCipher.ecbTwoBlockAdversary` (`BlockCipher.isPPT_ecbTwoBlockAdversary`) submits
  `0^{2 · blockLen n}` and `0^{blockLen n} ‖ 1^{blockLen n}` and tests whether the two
  `blockLen n`-bit ciphertext halves agree. Whenever `2 ≤ ℓ n` and `1 ≤ E.blockLen n` its
  advantage is `1` (`BlockCipher.advantage_demKeyGameOn_ecbTwoBlockAdversary`), so `ecbEncrypt`
  fails `Encryption.DEMOneTimeKeyINDCPAOn (E.ecbAdmissible ℓ)` whenever `2 ≤ ℓ n` and
  `1 ≤ E.blockLen n` hold infinitely often (`BlockCipher.not_demOneTimeKeyINDCPAOn_ecbEncrypt`).

The reduction certificate rewrites the distinguisher as a word program that sends the blocks of the
challenge message to the oracle in one list traversal, certified by
`Cslib.Probability.IsOraclePPTOn.mapM_query_take`.

## Main definitions

* `Cslib.Crypto.BlockCipher.ecbEncrypt`: ECB encryption of a message word.
* `Cslib.Crypto.BlockCipher.ecbAdmissible`, `Cslib.Crypto.BlockCipher.ecbValid`: the challenge
  pairs on `X^{≤ℓ}` (equal lengths, a multiple of the block length, at most `ℓ n` blocks) and on
  `X_*^{≤ℓ}` (also distinct blocks in each message).
* `Cslib.Crypto.BlockCipher.ecbToPrpDistinguisher`: the word block-cipher distinguisher.
* `Cslib.Crypto.BlockCipher.ecbTwoBlockAdversary`: the word-level two-block attack on ECB.

## Main results

* `Cslib.Crypto.BlockCipher.PRP.ecb_demOneTimeKeyINDCPAOn`: Theorem 4.1.
* `Cslib.Crypto.BlockCipher.PRP.ecb_demOneTimeKeyINDCPAOn_one`: single-block (`ℓ = 1`) ECB
  semantic security (§4.1.4, pp. 102, 104).
* `Cslib.Crypto.BlockCipher.advantage_demKeyGameOn_ecbEncrypt`: equation (4.3) on words.
* `Cslib.Crypto.BlockCipher.isOraclePPT_ecbToPrpDistinguisher`: efficiency of the reduction.
* `Cslib.Crypto.BlockCipher.isPPT_ecbTwoBlockAdversary`: efficiency of `ecbTwoBlockAdversary`.
* `Cslib.Crypto.BlockCipher.advantage_demKeyGameOn_ecbTwoBlockAdversary`: the two-block attack has
  advantage `1` when `2 ≤ ℓ n` and `1 ≤ E.blockLen n`.
* `Cslib.Crypto.BlockCipher.not_demOneTimeKeyINDCPAOn_ecbEncrypt`: word-level ECB is not
  semantically secure on `ecbAdmissible E ℓ` when `2 ≤ ℓ n` and `1 ≤ E.blockLen n` hold infinitely
  often (§4.1.4, pp. 103–104).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], version 0.6,
  §4.1.4 and Theorem 4.1 (pp. 102–106).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

namespace BlockCipher

variable (E : BlockCipher)

/-- The `blockLen n`-bit blocks of a message word: the rows of `BitString.listRows`, dropping a
final partial block. -/
abbrev ecbBlocks (n : ℕ) (m : List Bool) : List (List Bool) :=
  BitString.listRows (m.length / E.blockLen n) (E.blockLen n) m

/-- ECB encryption of a message word: encrypt each `blockLen n`-bit block under the key and
concatenate. -/
@[expose]
def ecbEncrypt (n : ℕ) (key m : List Bool) : ProbComp (List Bool) :=
  pure ((E.ecbBlocks n m).flatMap (E.encrypt n key))

/-- The challenge pairs of Attack Game 2.1 for word ECB on `X^{≤ℓ}`: two messages of the same
length, a multiple of the block length (`blockPairValid`), of at most `ℓ n` blocks. -/
@[expose]
def ecbAdmissible (ℓ : ℕ → ℕ) (n : ℕ) (_pk : List Bool) (m₀ m₁ : List Bool) : Bool :=
  blockPairValid (E.blockLen n) m₀ m₁ && decide (m₀.length ≤ ℓ n * E.blockLen n)

/-- The challenge pairs of Theorem 4.1 on words (`X_*^{≤ℓ}`): admissible pairs on `X^{≤ℓ}` whose
two messages each consist of distinct blocks. -/
@[expose]
def ecbValid (ℓ : ℕ → ℕ) (n : ℕ) (pk : List Bool) (m₀ m₁ : List Bool) : Bool :=
  E.ecbAdmissible ℓ n pk m₀ m₁ && decide (E.ecbBlocks n m₀).Nodup &&
    decide (E.ecbBlocks n m₁).Nodup

/-- The permutation of `blockLen n`-bit blocks of a `keyLen n`-bit key. -/
private def ecbKeyPerm (n : ℕ) (k : BitString (E.keyLen n)) :
    Equiv.Perm (BitString (E.blockLen n)) :=
  E.permEquiv n (List.ofFn k) List.length_ofFn

/-- The typed one-time adversary that a word adversary induces at parameter `n`: its messages are
read as lists of `blockLen n`-bit blocks, an inadmissible word pair becomes a pair of different
lengths, and the challenge is flattened back into a word. -/
private noncomputable def ecbTypedAdversary (ℓ : ℕ → ℕ) (A : Encryption.AdversaryOf (List Bool))
    (n : ℕ) :
    TwoStage Unit (MessagePair (List (BitString (E.blockLen n))))
      (List (BitString (E.blockLen n))) Bool (List Bool) where
  choose _ := (fun c => (if E.ecbValid ℓ n [] (Encryption.ChoiceOut.msg₀ c)
        (Encryption.ChoiceOut.msg₁ c) then
      ⟨(E.ecbBlocks n (Encryption.ChoiceOut.msg₀ c)).map (BitString.ofList _),
        (E.ecbBlocks n (Encryption.ChoiceOut.msg₁ c)).map (BitString.ofList _)⟩
    else ⟨[], [fun _ => false]⟩, Encryption.ChoiceOut.state c)) <$> A.choose n []
  guess st c := A.guess n st (c.flatMap List.ofFn)

/-- The block-cipher distinguisher of Theorem 4.1 on words: the typed reduction `ECB.reduction`,
for the typed one-time adversary that `A` induces (its messages cut into `blockLen n`-bit blocks,
its challenge flattened back into a word), run against the word oracle, each block query sent as
its `blockLen n` bits and each reply read back as a block. -/
noncomputable def ecbToPrpDistinguisher (ℓ : ℕ → ℕ) (A : Encryption.AdversaryOf (List Bool)) :
    OracleDistinguisher := fun n _ =>
  ProbOracleComp.simulate
    (fun x : BitString (E.blockLen n) =>
      BitString.ofList _ <$> ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
        ((), List.ofFn x))
    (ECB.reduction (ℓ n) (E.ecbTypedAdversary ℓ A n))

/-! ### Admissible pairs -/

/-- Reading words of `w` bits as bit strings is injective. -/
private theorem ofList_injOn {w : ℕ} {x y : List Bool} (hx : x.length = w) (hy : y.length = w)
    (h : BitString.ofList w x = BitString.ofList w y) : x = y := by
  rw [← BitString.ofFn_ofList hx, ← BitString.ofFn_ofList hy, h]

/-- An admissible word pair gives an admissible pair of block lists. -/
private theorem distinctAdmissible_of_ecbValid {ℓ : ℕ → ℕ} {n : ℕ} {m₀ m₁ : List Bool}
    (h : E.ecbValid ℓ n [] m₀ m₁ = true) :
    ECB.distinctAdmissible (ℓ n) ((E.ecbBlocks n m₀).map (BitString.ofList (E.blockLen n)))
      ((E.ecbBlocks n m₁).map (BitString.ofList (E.blockLen n))) = true := by
  simp only [ecbValid, ecbAdmissible, blockPairValid, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hlen, -⟩, hℓ⟩, h₀⟩, h₁⟩ := h
  have hnodup {m : List Bool} (hm : (E.ecbBlocks n m).Nodup) :
      ((E.ecbBlocks n m).map (BitString.ofList (E.blockLen n))).Nodup :=
    hm.map_on fun x hx y hy hxy => ofList_injOn (BitString.length_of_mem_listRows hx)
      (BitString.length_of_mem_listRows hy) hxy
  simp only [ECB.distinctAdmissible, List.length_map, BitString.length_listRows, hlen,
    decide_eq_true_eq, true_and]
  exact ⟨Nat.div_le_of_le_mul (by rw [← hlen]; simpa [Nat.mul_comm] using hℓ), hnodup h₀,
    hnodup h₁⟩

/-- When the block bound is at most `1`, every admissible pair on `X^{≤ℓ}` has at most one block in
each message, so `ecbValid` coincides with `ecbAdmissible`. -/
theorem ecbValid_eq_ecbAdmissible_of_le_one {ℓ : ℕ → ℕ} {n : ℕ} (hℓ : ℓ n ≤ 1)
    (pk m₀ m₁ : List Bool) :
    E.ecbValid ℓ n pk m₀ m₁ = E.ecbAdmissible ℓ n pk m₀ m₁ := by
  by_cases hadm : E.ecbAdmissible ℓ n pk m₀ m₁ = true
  · have hadm' := hadm
    simp only [ecbAdmissible, blockPairValid, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at hadm'
    obtain ⟨⟨hlen, -⟩, hle⟩ := hadm'
    have hle₁ : m₀.length ≤ 1 * E.blockLen n := hle.trans (Nat.mul_le_mul_right _ hℓ)
    have hnodup {m : List Bool} (hm : m.length ≤ 1 * E.blockLen n) :
        (E.ecbBlocks n m).Nodup := by
      have hdiv : (E.ecbBlocks n m).length ≤ 1 := by
        rw [ecbBlocks, BitString.length_listRows]
        exact Nat.div_le_of_le_mul (by simpa only [Nat.mul_comm] using hm)
      rcases h : E.ecbBlocks n m with _ | ⟨a, _ | ⟨b, l⟩⟩
      · exact List.nodup_nil
      · exact List.nodup_singleton a
      · simp [h] at hdiv
    simp [ecbValid, hadm, hnodup hle₁, hnodup (hlen ▸ hle₁)]
  · simp [ecbValid, hadm]

/-- Encrypting the blocks of a word with the induced permutation and flattening is encrypting the
word block by block. -/
private theorem flatMap_ofFn_ecbKeyPerm (n : ℕ) (k : BitString (E.keyLen n)) (m : List Bool) :
    ((E.ecbBlocks n m).map (⇑(E.ecbKeyPerm n k) ∘ BitString.ofList _)).flatMap List.ofFn =
      (E.ecbBlocks n m).flatMap (E.encrypt n (List.ofFn k)) := by
  simp only [List.flatMap_map]
  refine List.flatMap_congr fun r hr => ?_
  have hr' := BitString.length_of_mem_listRows hr
  simp only [Function.comp_apply, ecbKeyPerm, permEquiv, Equiv.coe_fn_mk,
    BitString.ofFn_ofList hr']
  exact BitString.ofFn_ofList (E.length_encrypt n _ r List.length_ofFn hr')

/-! ### The real and ideal experiments -/

/-- The one-time experiment of word ECB is the typed one-time experiment of `Cipher.ecb` against
the induced permutations and the induced typed adversary. -/
private theorem eval_demKeyGameOn_ecbEncrypt (ℓ : ℕ → ℕ) (A : Encryption.AdversaryOf (List Bool))
    (b : Bool) (n : ℕ) :
    ProbComp.eval (Encryption.demKeyGameOn (E.ecbValid ℓ) E.keyLen E.ecbEncrypt A b n) =
      ProbComp.eval ((Cipher.ecb (E.ecbKeyPerm n)).oneTimeExperiment
        (ProbComp.uniform (BitString (E.keyLen n))) (ECB.distinctAdmissible (ℓ n))
        (E.ecbTypedAdversary ℓ A n) b) := by
  simp only [Encryption.demKeyGameOn, Cipher.oneTimeExperiment, ProbComp.eval_bind,
    BitString.eval_sampleList, ProbComp.eval_uniform, eval_lrExperiment, BitString.uniformList,
    PMF.bind_map, ecbTypedAdversary, ProbComp.eval_map]
  refine congrArg _ (funext fun k => ?_)
  simp only [Function.comp_apply]
  refine congrArg _ (funext fun c => ?_)
  by_cases hv : E.ecbValid ℓ n [] c.1.1 c.1.2 = true
  · have hadm := distinctAdmissible_of_ecbValid E hv
    cases b <;> simp [Encryption.ChoiceOut.msg₀, Encryption.ChoiceOut.msg₁,
      Encryption.ChoiceOut.msgs, hv, hadm, ecbEncrypt, Cipher.ecb, MessagePair.select,
      flatMap_ofFn_ecbKeyPerm]
  · simp [Encryption.ChoiceOut.msg₀, Encryption.ChoiceOut.msg₁, Encryption.ChoiceOut.msgs, hv,
      ECB.distinctAdmissible]

/-- Against the word oracle of a key, the distinguisher runs the typed reduction against the
induced permutation. -/
private theorem eval_prpRealGame_ecbToPrpDistinguisher (ℓ : ℕ → ℕ)
    (A : Encryption.AdversaryOf (List Bool)) (n : ℕ) :
    ProbComp.eval (E.prpRealGame (E.ecbToPrpDistinguisher ℓ A) n) =
      ProbComp.eval (PRP.realExperiment (E.ecbKeyPerm n)
        (ECB.reduction (ℓ n) (E.ecbTypedAdversary ℓ A n))) := by
  simp only [prpRealGame, PRP.realExperiment, PRF.realExperiment, ProbComp.eval_bind,
    BitString.eval_sampleList, ProbComp.eval_uniform, BitString.uniformList, PMF.bind_map]
  refine congrArg _ (funext fun k => ?_)
  simp only [Function.comp_apply, ecbToPrpDistinguisher, ProbOracleComp.run_simulate,
    ProbOracleComp.run_map, ProbOracleComp.run_query, map_pure]
  congr 2
  funext x
  rw [E.prpOracle_eq_randomPermOracle List.length_ofFn]
  simp [randomPermOracle, randomFunctionOracle, ecbKeyPerm]

/-- Against a uniform permutation, the distinguisher runs the typed reduction against it. -/
private theorem prpIdealGame_ecbToPrpDistinguisher (ℓ : ℕ → ℕ)
    (A : Encryption.AdversaryOf (List Bool)) (n : ℕ) :
    prpIdealGame E.blockLen (E.ecbToPrpDistinguisher ℓ A) n =
      PRP.idealExperiment (ECB.reduction (ℓ n) (E.ecbTypedAdversary ℓ A n)) := by
  simp only [prpIdealGame, PRP.idealExperiment, ecbToPrpDistinguisher,
    ProbOracleComp.run_simulate, ProbOracleComp.run_map, ProbOracleComp.run_query, map_pure]
  congr 1
  funext π
  congr 1
  funext x
  simp [randomPermOracle, randomFunctionOracle]

/-- **Theorem 4.1, equation (4.3), on words**: at each parameter, the one-time advantage of a word
adversary against word ECB with challenge pairs `ecbValid E ℓ` is twice the block-cipher advantage
of `ecbToPrpDistinguisher E ℓ A`. -/
theorem advantage_demKeyGameOn_ecbEncrypt (ℓ : ℕ → ℕ) (A : Encryption.AdversaryOf (List Bool))
    (n : ℕ) :
    Game.advantage
        (ProbComp.eval (Encryption.demKeyGameOn (E.ecbValid ℓ) E.keyLen E.ecbEncrypt A false n))
        (ProbComp.eval (Encryption.demKeyGameOn (E.ecbValid ℓ) E.keyLen E.ecbEncrypt A true n)) =
      2 * Game.advantage (ProbComp.eval (E.prpRealGame (E.ecbToPrpDistinguisher ℓ A) n))
        (ProbComp.eval (prpIdealGame E.blockLen (E.ecbToPrpDistinguisher ℓ A) n)) := by
  rw [eval_demKeyGameOn_ecbEncrypt, eval_demKeyGameOn_ecbEncrypt,
    eval_prpRealGame_ecbToPrpDistinguisher, prpIdealGame_ecbToPrpDistinguisher]
  exact ECB.advantage_eq_two_mul_prpAdvantage (E.ecbKeyPerm n) (ℓ n) (E.ecbTypedAdversary ℓ A n)

/-! ### Efficiency of the distinguisher -/

/-- The challenge phase of the distinguisher as a word program: on an admissible pair, send the
blocks of the selected message to the oracle in one traversal, cut each reply to `blockLen n` bits,
pad it back to `blockLen n` bits and give the concatenation to `A`. -/
private noncomputable def ecbChallenge (ℓ : ℕ → ℕ) (A : Encryption.AdversaryOf (List Bool))
    (n : ℕ) (b : Bool) (c : Encryption.ChoiceOut (List Bool)) : WordOracleComp Unit Bool :=
  if E.ecbValid ℓ n [] c.1.1 c.1.2 then do
    let replies ← (E.ecbBlocks n (if b then c.1.2 else c.1.1)).mapM fun x =>
      List.take (E.blockLen n) <$>
        ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool) ((), x)
    (· == b) <$> ProbOracleComp.sample (A.guess n c.2
      (replies.flatMap fun r => (r ++ List.replicate (E.blockLen n) false).take (E.blockLen n)))
  else
    pure (false == b)

/-- The distinguisher written as a word program. -/
private noncomputable def ecbToPrpWord (ℓ : ℕ → ℕ) (A : Encryption.AdversaryOf (List Bool)) :
    OracleDistinguisher := fun n _ => do
  let b ← ProbOracleComp.sample (ProbComp.uniform Bool)
  let c ← ProbOracleComp.sample (A.choose n [])
  E.ecbChallenge ℓ A n b c

/-- The blocks of a word, read as bit strings and back, are the blocks. -/
private theorem map_ofFn_ofList_ecbBlocks (n : ℕ) (m : List Bool) :
    (E.ecbBlocks n m).map (List.ofFn ∘ BitString.ofList (E.blockLen n)) = E.ecbBlocks n m := by
  conv_rhs => rw [← List.map_id (E.ecbBlocks n m)]
  exact List.map_congr_left fun r hr =>
    BitString.ofFn_ofList (BitString.length_of_mem_listRows hr)

private theorem ecbToPrpWord_eq (ℓ : ℕ → ℕ) (A : Encryption.AdversaryOf (List Bool)) :
    E.ecbToPrpWord ℓ A = E.ecbToPrpDistinguisher ℓ A := by
  funext n input
  simp only [ecbToPrpWord, ecbChallenge, ecbToPrpDistinguisher, ECB.reduction, ecbTypedAdversary,
    ProbOracleComp.simulate_bind, ProbOracleComp.simulate_sample, ProbOracleComp.sample_map,
    bind_map_left]
  refine bind_congr fun b => bind_congr fun c => ?_
  by_cases hv : E.ecbValid ℓ n [] c.1.1 c.1.2 = true
  · have hadm := E.distinctAdmissible_of_ecbValid hv
    have hsel : E.ecbBlocks n (if b then c.1.2 else c.1.1) =
        ((MessagePair.mk ((E.ecbBlocks n c.1.1).map (BitString.ofList (E.blockLen n)))
          ((E.ecbBlocks n c.1.2).map (BitString.ofList (E.blockLen n)))).select b).map
            List.ofFn := by
      cases b <;> simp [MessagePair.select, map_ofFn_ofList_ecbBlocks]
    have hreply (x : BitString (E.blockLen n)) :
        ProbOracleComp.simulate
            (fun x : BitString (E.blockLen n) => BitString.ofList _ <$>
              ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
                ((), List.ofFn x))
            (ProbOracleComp.query (spec := fun _ : BitString (E.blockLen n) =>
              BitString (E.blockLen n)) x) =
          BitString.ofList _ <$> (List.take (E.blockLen n) <$>
            ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
              ((), List.ofFn x)) := by
      rw [ProbOracleComp.simulate_query, Functor.map_map]
      exact congrArg (· <$> _) (funext fun r => (BitString.ofList_take _ r).symm)
    simp only [hv, ↓reduceIte, hadm, ProbOracleComp.simulate_bind, ProbOracleComp.simulate_mapM,
      hreply, ← List.map_mapM, ProbOracleComp.simulate_map, ProbOracleComp.simulate_sample,
      bind_map_left, List.flatMap_map, BitString.ofFn_ofList_eq_take]
    rw [hsel, List.mapM_map]
    rfl
  · simp [hv, ECB.distinctAdmissible]

/-- The blocks of a computed word are computed in polynomial time. -/
private theorem computableInPolyTime_ecbBlocks {α : Type} {input : α ↪ List Bool}
    {n : α → ℕ} {m : α → List Bool} (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime m input encBits) :
    ComputableInPolyTime (fun a => E.ecbBlocks (n a) (m a)) input (encList encBits) := by
  have hw := E.blockLen_polyTime.comp hn
  unfold ecbBlocks
  polytime [BitString.listRows, BitString.listRow]

/-- Admissibility of a computed pair is decided in polynomial time. -/
private theorem computableInPolyTime_ecbValid {α : Type} {input : α ↪ List Bool} {ℓ : ℕ → ℕ}
    (hℓ : ComputableInPolyTime ℓ encUnary encUnary) {n : α → ℕ} {m₀ m₁ : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary) (hm₀ : ComputableInPolyTime m₀ input encBits)
    (hm₁ : ComputableInPolyTime m₁ input encBits) :
    ComputableInPolyTime (fun a => E.ecbValid ℓ (n a) [] (m₀ a) (m₁ a)) input encBool := by
  have h₀ := E.computableInPolyTime_ecbBlocks hn hm₀
  have h₁ := E.computableInPolyTime_ecbBlocks hn hm₁
  have hw := E.blockLen_polyTime.comp hn
  have hℓn := hℓ.comp hn
  unfold ecbValid ecbAdmissible blockPairValid
  fun_prop

/-- The encoding of the distinguisher's state after the coin and the adversary's choice. -/
private abbrev ecbStateEnc : ((ℕ × List Bool) × Bool) × Encryption.ChoiceOut (List Bool) ↪
    List Bool :=
  encPair (encPair (encPair encUnary encBits) encBool) (Encryption.encChoiceOut encBits)

/-- The challenge phase of the distinguisher is strict oracle PPT. -/
private theorem isOraclePPTOn_ecbChallenge {ℓ : ℕ → ℕ}
    (hℓ : ComputableInPolyTime ℓ encUnary encUnary) {A : Encryption.AdversaryOf (List Bool)}
    (hA : A.IsPPT encBits) :
    IsOraclePPTOn (Operation := Unit) ecbStateEnc encBool
      (fun q : ((ℕ × List Bool) × Bool) × Encryption.ChoiceOut (List Bool) =>
        E.ecbChallenge ℓ A q.1.1.1 q.1.2 q.2) := by
  have hn : ComputableInPolyTime
      (fun q : ((ℕ × List Bool) × Bool) × Encryption.ChoiceOut (List Bool) => q.1.1.1)
        ecbStateEnc encUnary := by fun_prop
  have hc0 : ComputableInPolyTime
      (fun q : ((ℕ × List Bool) × Bool) × Encryption.ChoiceOut (List Bool) => q.2.1.1)
        ecbStateEnc encBits := by fun_prop
  have hc1 : ComputableInPolyTime
      (fun q : ((ℕ × List Bool) × Bool) × Encryption.ChoiceOut (List Bool) => q.2.1.2)
        ecbStateEnc encBits := by fun_prop
  have hsel : ComputableInPolyTime
      (fun q : ((ℕ × List Bool) × Bool) × Encryption.ChoiceOut (List Bool) =>
        if q.1.2 then q.2.1.2 else q.2.1.1) ecbStateEnc encBits := by fun_prop
  have hw := E.blockLen_polyTime.comp hn
  have hreplies := IsOraclePPTOn.mapM_query_take () (E.computableInPolyTime_ecbBlocks hn hsel) hw
  have hpad : ComputableInPolyTime
      (fun p : (((ℕ × List Bool) × Bool) × Encryption.ChoiceOut (List Bool)) ×
          List (List Bool) =>
        p.2.flatMap fun r => (r ++ List.replicate (E.blockLen p.1.1.1.1) false).take
          (E.blockLen p.1.1.1.1))
      (encPair ecbStateEnc (encList encBits)) encBits := by
    have hw' := hw.comp (ComputableInPolyTime.fst ecbStateEnc (encList encBits))
    have hw'' := hw'.comp (ComputableInPolyTime.fst (encPair ecbStateEnc (encList encBits)) encBits)
    exact ComputableInPolyTime.flatMapToBitsWithInput (ComputableInPolyTime.snd _ _)
      (((ComputableInPolyTime.snd _ _).bitsAppend
        ((ComputableInPolyTime.bitsReplicate false).comp hw'')).bitsTakeWithInput hw'')
  have hguessIn : ComputableInPolyTime
      (fun p : (((ℕ × List Bool) × Bool) × Encryption.ChoiceOut (List Bool)) ×
          List (List Bool) =>
        (p.1.1.1.1, p.1.2.2, p.2.flatMap fun r =>
          (r ++ List.replicate (E.blockLen p.1.1.1.1) false).take (E.blockLen p.1.1.1.1)))
      (encPair ecbStateEnc (encList encBits)) Encryption.encGuessInput := by
    fun_prop
  have hguess := ((hA.guess.preprocess hguessIn).isOraclePPTOn (Operation := Unit)).map_with
    (f := fun (p : (((ℕ × List Bool) × Bool) × Encryption.ChoiceOut (List Bool)) ×
        List (List Bool)) (g : Bool) => g == p.1.1.2) (by fun_prop)
  have hno : IsOraclePPTOn (Operation := Unit) ecbStateEnc encBool
      (fun q : ((ℕ × List Bool) × Bool) × Encryption.ChoiceOut (List Bool) =>
        pure (false == q.1.2)) :=
    ((ComputableInPolyTime.const (encIn := ecbStateEnc) (encOut := encBool) false).beq
      (by fun_prop)).isOraclePPTOn
  unfold ecbChallenge
  exact IsOraclePPTOn.cond (E.computableInPolyTime_ecbValid hℓ hn hc0 hc1)
    (hreplies.bind_with hguess) hno

/-- **Efficiency of the distinguisher.** For a polynomial-time block bound `ℓ` and every uniform
strict PPT one-time adversary `A`, `ecbToPrpDistinguisher E ℓ A` is uniform strict oracle PPT. -/
theorem isOraclePPT_ecbToPrpDistinguisher {ℓ : ℕ → ℕ}
    (hℓ : ComputableInPolyTime ℓ encUnary encUnary) {A : Encryption.AdversaryOf (List Bool)}
    (hA : A.IsPPT encBits) : IsOraclePPT encBool (E.ecbToPrpDistinguisher ℓ A) := by
  rw [← E.ecbToPrpWord_eq ℓ A]
  have hchooseIn : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × Bool => (p.1.1, ([] : List Bool)))
      (encPair (encPair encUnary encBits) encBool) (encPair encUnary encBits) := by fun_prop
  have hchoose : IsOraclePPTOn (Operation := Unit) (encPair (encPair encUnary encBits) encBool)
      (Encryption.encChoiceOut encBits)
      (fun p : (ℕ × List Bool) × Bool => ProbOracleComp.sample (A.choose p.1.1 [])) :=
    (hA.choose.on.preprocess hchooseIn).isOraclePPTOn
  have hstage := hchoose.bind_with (second := fun p c => E.ecbChallenge ℓ A p.1.1 p.2 c)
    (E.isOraclePPTOn_ecbChallenge hℓ hA)
  have hcoin : IsOraclePPTOn (Operation := Unit) (encPair encUnary encBits) encBool
      (fun _ => ProbOracleComp.sample (ProbComp.uniform Bool)) :=
    (isPPTOn_uniform_bool _).isOraclePPTOn
  exact (hcoin.bind_with (second := fun i b => do
    let c ← ProbOracleComp.sample (A.choose i.1 [])
    E.ecbChallenge ℓ A i.1 b c) hstage).isOraclePPT

/-! ### Theorem 4.1 on words -/

/-- **Theorem 4.1** ([BonehShoup2023], pp. 104–106): if `E` is a secure block cipher, its ECB
cipher restricted to messages of at most `ℓ n` distinct blocks is semantically secure (Attack
Game 2.1 with a uniform `keyLen n`-bit key), for every block bound `ℓ` computable in unary in
polynomial time. -/
theorem PRP.ecb_demOneTimeKeyINDCPAOn {E : BlockCipher} (hE : E.PRP) {ℓ : ℕ → ℕ}
    (hℓ : ComputableInPolyTime ℓ encUnary encUnary) :
    Encryption.DEMOneTimeKeyINDCPAOn (E.ecbValid ℓ) encBits E.keyLen E.ecbEncrypt := by
  intro A hA
  have h :=
    (hE (E.ecbToPrpDistinguisher ℓ A) (E.isOraclePPT_ecbToPrpDistinguisher hℓ hA)).const_mul 2
  have heq : (fun n => Game.advantage
      (ProbComp.eval (Encryption.demKeyGameOn (E.ecbValid ℓ) E.keyLen E.ecbEncrypt A false n))
      (ProbComp.eval (Encryption.demKeyGameOn (E.ecbValid ℓ) E.keyLen E.ecbEncrypt A true n))) =
      fun n => 2 * Game.advantage (ProbComp.eval (E.prpRealGame (E.ecbToPrpDistinguisher ℓ A) n))
        (ProbComp.eval (prpIdealGame E.blockLen (E.ecbToPrpDistinguisher ℓ A) n)) :=
    funext fun n => E.advantage_demKeyGameOn_ecbEncrypt ℓ A n
  exact (congrArg Negligible heq).mpr h

/-- **Single-block ECB semantic security** ([BonehShoup2023], §4.1.4, pp. 102, 104): if `E` is a
secure block cipher, its ECB cipher on messages of at most one `blockLen n`-bit block
(`ecbAdmissible E (fun _ => 1)`) is semantically secure. Here `X^{≤1}` admits pairs of empty
messages (which are equal) and pairs of single `blockLen n`-bit blocks (the data block space). -/
theorem PRP.ecb_demOneTimeKeyINDCPAOn_one {E : BlockCipher} (hE : E.PRP) :
    Encryption.DEMOneTimeKeyINDCPAOn (E.ecbAdmissible fun _ => 1) encBits E.keyLen
      E.ecbEncrypt := by
  have heq : E.ecbAdmissible (fun _ => 1) = E.ecbValid (fun _ => 1) := by
    ext n pk m₀ m₁
    exact (E.ecbValid_eq_ecbAdmissible_of_le_one le_rfl pk m₀ m₁).symm
  rw [heq]
  exact hE.ecb_demOneTimeKeyINDCPAOn (ComputableInPolyTime.const 1)

/-! ### The two-block attack on words -/

/-- The word-level two-block attack on ECB ([BonehShoup2023], §4.1.4, pp. 103–104): submit
`m₀ = 0^{2 · blockLen n}` (two equal `0^{blockLen n}` blocks) and
`m₁ = 0^{blockLen n} ‖ 1^{blockLen n}` (two unequal blocks when `1 ≤ blockLen n`), and output
`true` when the first `blockLen n` bits of the challenge ciphertext equal the remaining bits. -/
def ecbTwoBlockAdversary : Encryption.AdversaryOf (List Bool) where
  choose n _ := pure ((List.replicate (2 * E.blockLen n) false,
    List.replicate (E.blockLen n) false ++ List.replicate (E.blockLen n) true), [])
  guess n _ ct := pure (decide (ct.take (E.blockLen n) = ct.drop (E.blockLen n)))

/-- The two-block attack `ecbTwoBlockAdversary` is uniform strict PPT for every block cipher `E`. -/
theorem isPPT_ecbTwoBlockAdversary : E.ecbTwoBlockAdversary.IsPPT encBits where
  choose := by
    have hw := E.blockLen_polyTime
    exact IsPPTOn.isPPT (ComputableInPolyTime.isPPTOn (by polytime))
  guess := by
    have hw := E.blockLen_polyTime
    exact ComputableInPolyTime.isPPTOn (by polytime)

/-- When `1 ≤ E.blockLen n`, the ECB blocks of a concatenation of two `blockLen n`-bit words are
those two words. -/
private theorem ecbBlocks_append_pair {n : ℕ} (hw : 1 ≤ E.blockLen n) {u v : List Bool}
    (hu : u.length = E.blockLen n) (hv : v.length = E.blockLen n) :
    E.ecbBlocks n (u ++ v) = [u, v] := by
  have hdiv : (u ++ v).length / E.blockLen n = 2 := by
    rw [List.length_append, hu, hv, ← Nat.two_mul]
    exact Nat.mul_div_cancel 2 hw
  have hflat : ([u, v] : List (List Bool)).flatten = u ++ v := by simp
  rw [ecbBlocks, hdiv, ← hflat]
  exact BitString.listRows_flatten [u, v] (by simp [hu, hv])

/-- Evaluating `demKeyGameOn` with `ecbTwoBlockAdversary` outputs `!bit` with probability `1`
whenever `2 ≤ ℓ n` and `1 ≤ E.blockLen n`. -/
private theorem eval_demKeyGameOn_ecbTwoBlockAdversary {ℓ : ℕ → ℕ} {n : ℕ}
    (hℓ : 2 ≤ ℓ n) (hw : 1 ≤ E.blockLen n) (bit : Bool) :
    ProbComp.eval (Encryption.demKeyGameOn (E.ecbAdmissible ℓ) E.keyLen E.ecbEncrypt
        E.ecbTwoBlockAdversary bit n) = PMF.pure (!bit) := by
  have hadm : E.ecbAdmissible ℓ n [] (List.replicate (2 * E.blockLen n) false)
      (List.replicate (E.blockLen n) false ++ List.replicate (E.blockLen n) true) = true := by
    simp only [ecbAdmissible, blockPairValid, List.length_replicate, List.length_append,
      ← Nat.two_mul, beq_self_eq_true, Nat.mul_mod_left, Bool.true_and, decide_eq_true_eq]
    exact Nat.mul_le_mul_right (E.blockLen n) hℓ
  have hsel : (if bit then
        List.replicate (E.blockLen n) false ++ List.replicate (E.blockLen n) true
      else List.replicate (2 * E.blockLen n) false) =
      List.replicate (E.blockLen n) false ++
        if bit then List.replicate (E.blockLen n) true
        else List.replicate (E.blockLen n) false := by
    rw [Nat.two_mul, List.replicate_add]
    cases bit <;> rfl
  have hxy : List.replicate (E.blockLen n) false ≠ List.replicate (E.blockLen n) true := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : E.blockLen n ≠ 0)
    simp [hm]
  have hkey (k : BitString (E.keyLen n)) :
      decide (((E.ecbBlocks n (List.replicate (E.blockLen n) false ++
          if bit then List.replicate (E.blockLen n) true
          else List.replicate (E.blockLen n) false)).flatMap
            (E.encrypt n (List.ofFn k))).take (E.blockLen n) =
        ((E.ecbBlocks n (List.replicate (E.blockLen n) false ++
          if bit then List.replicate (E.blockLen n) true
          else List.replicate (E.blockLen n) false)).flatMap
            (E.encrypt n (List.ofFn k))).drop (E.blockLen n)) = !bit := by
    have hz : (if bit then List.replicate (E.blockLen n) true
        else List.replicate (E.blockLen n) false).length = E.blockLen n := by
      cases bit <;> simp
    have hc₀ : (E.encrypt n (List.ofFn k) (List.replicate (E.blockLen n) false)).length =
        E.blockLen n :=
      E.length_encrypt n _ _ List.length_ofFn List.length_replicate
    rw [E.ecbBlocks_append_pair hw List.length_replicate hz]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.take_left' hc₀, List.drop_left' hc₀]
    cases bit
    · simp
    · simp only [↓reduceIte, Bool.not_true, decide_eq_false_iff_not]
      intro heq
      have hdec := congrArg (E.decrypt n (List.ofFn k)) heq
      rw [E.decrypt_encrypt n _ _ List.length_ofFn List.length_replicate,
        E.decrypt_encrypt n _ _ List.length_ofFn List.length_replicate] at hdec
      exact hxy hdec
  simp only [Encryption.demKeyGameOn, ecbTwoBlockAdversary, ecbEncrypt, ProbComp.eval_bind,
    BitString.eval_sampleList, BitString.uniformList, PMF.bind_map, Function.comp_def,
    ProbComp.eval_pure, Encryption.ChoiceOut.msg₀_mk, Encryption.ChoiceOut.msg₁_mk, hadm,
    ↓reduceIte, pure_bind, hsel, hkey, PMF.bind_const]

/-- At any parameter `n` with `2 ≤ ℓ n` and `1 ≤ E.blockLen n`, the word-level two-block attack
`ecbTwoBlockAdversary` has one-time semantic-security advantage `1` against `ecbEncrypt` on
`ecbAdmissible E ℓ` ([BonehShoup2023], §4.1.4, pp. 103–104). -/
theorem advantage_demKeyGameOn_ecbTwoBlockAdversary {ℓ : ℕ → ℕ} {n : ℕ}
    (hℓ : 2 ≤ ℓ n) (hw : 1 ≤ E.blockLen n) :
    Game.advantage
      (ProbComp.eval (Encryption.demKeyGameOn (E.ecbAdmissible ℓ) E.keyLen E.ecbEncrypt
        E.ecbTwoBlockAdversary false n))
      (ProbComp.eval (Encryption.demKeyGameOn (E.ecbAdmissible ℓ) E.keyLen E.ecbEncrypt
        E.ecbTwoBlockAdversary true n)) = 1 := by
  rw [E.eval_demKeyGameOn_ecbTwoBlockAdversary hℓ hw false,
    E.eval_demKeyGameOn_ecbTwoBlockAdversary hℓ hw true]
  simp [Game.advantage, Game.succProbability]

/-- **Word-level ECB is not semantically secure** ([BonehShoup2023], §4.1.4, pp. 103–104): for
every block cipher `E` and block bound `ℓ`, if `2 ≤ ℓ n` and `1 ≤ E.blockLen n` hold for
infinitely many parameters `n`, then `ecbEncrypt` does not satisfy one-time semantic security on
`ecbAdmissible E ℓ`. -/
theorem not_demOneTimeKeyINDCPAOn_ecbEncrypt {ℓ : ℕ → ℕ}
    (h : ∃ᶠ n in Filter.atTop, 2 ≤ ℓ n ∧ 1 ≤ E.blockLen n) :
    ¬ Encryption.DEMOneTimeKeyINDCPAOn (E.ecbAdmissible ℓ) encBits E.keyLen E.ecbEncrypt := by
  intro hsec
  refine not_negligible_of_frequently_ge one_ne_zero ?_
    (hsec E.ecbTwoBlockAdversary E.isPPT_ecbTwoBlockAdversary)
  exact h.mono fun n ⟨hℓ, hw⟩ =>
    (E.advantage_demKeyGameOn_ecbTwoBlockAdversary hℓ hw).symm.le

end BlockCipher

end Cslib.Crypto
