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

* Theorem 4.1: if `E` is a secure block cipher (`BlockCipher.PRP`), ECB on messages of at most
  `ℓ n` distinct blocks is semantically secure (`BlockCipher.PRP.ecb_demOneTimeKeyINDCPAOn`). The
  reduction `BlockCipher.ecbToPrpDistinguisher` runs the typed reduction `ECB.reduction` of
  `CslibFrontier.Crypto.Primitives.BlockCipher.ECB` against the word oracle, and it is uniform
  strict oracle PPT (`BlockCipher.isOraclePPT_ecbToPrpDistinguisher`). At each parameter the
  advantage is exactly twice the block-cipher advantage of that reduction
  (`BlockCipher.advantage_demKeyGameOn_ecbEncrypt`), from the typed equation (4.3).

The certificate rewrites the distinguisher as a word program that sends the blocks of the
challenge message to the oracle in one list traversal, certified by
`Cslib.Probability.IsOraclePPTOn.mapM_query_take`.

## Main definitions

* `Cslib.Crypto.BlockCipher.ecbEncrypt`: ECB encryption of a message word.
* `Cslib.Crypto.BlockCipher.ecbAdmissible`, `Cslib.Crypto.BlockCipher.ecbValid`: the challenge
  pairs on `X^{≤ℓ}` (equal lengths, a multiple of the block length, at most `ℓ n` blocks) and on
  `X_*^{≤ℓ}` (also distinct blocks in each message).
* `Cslib.Crypto.BlockCipher.ecbToPrpDistinguisher`: the word block-cipher distinguisher.

## Main results

* `Cslib.Crypto.BlockCipher.PRP.ecb_demOneTimeKeyINDCPAOn`: Theorem 4.1.
* `Cslib.Crypto.BlockCipher.advantage_demKeyGameOn_ecbEncrypt`: equation (4.3) on words.
* `Cslib.Crypto.BlockCipher.isOraclePPT_ecbToPrpDistinguisher`: efficiency of the reduction.

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
  have hguess := ((hA.guess.preprocess hguessIn).isOraclePPTOn (Operation := Unit)).map_with'
    (f := fun (p : (((ℕ × List Bool) × Bool) × Encryption.ChoiceOut (List Bool)) ×
        List (List Bool)) (g : Bool) => g == p.1.1.2) (by fun_prop)
  have hno : IsOraclePPTOn (Operation := Unit) ecbStateEnc encBool
      (fun q : ((ℕ × List Bool) × Bool) × Encryption.ChoiceOut (List Bool) =>
        pure (false == q.1.2)) :=
    ComputableInPolyTime.isOraclePPTOn (by fun_prop)
  unfold ecbChallenge
  exact IsOraclePPTOn.cond' (E.computableInPolyTime_ecbValid hℓ hn hc0 hc1)
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

/-- **Theorem 4.1** ([BonehShoup2023], pp. 104–105): if `E` is a secure block cipher, its ECB
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

end BlockCipher

end Cslib.Crypto
