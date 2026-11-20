/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.Cipher
public import CslibFrontier.Crypto.Primitives.PRP.Finite
import CslibFrontier.Crypto.Computational.Encryption.Cipher.Perfect
import CslibFrontier.Crypto.Game.HiddenBit
import CslibFrontier.Languages.Probabilistic.Traverse.SupportWith
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# Electronic codebook (ECB) mode

The `ℓ`-wise ECB cipher derived from a block cipher `E` encrypts a sequence of at most `ℓ` data
blocks block by block, `E′(k, m) = (E(k, m[0]), …, E(k, m[v-1]))` ([BonehShoup2023], §4.1.4,
pp. 102–106). This file gives the concrete single-cipher analysis underlying Section 4.1.4; the
asymptotic statements for a uniform block cipher are in
`CslibFrontier.Crypto.Computational.Encryption.ECB`.

* Concrete two-block attack: on two-block messages, `m₀` with two equal blocks and `m₁` with two
  distinct blocks, the adversary that checks whether the two ciphertext blocks are equal has
  advantage `1` (`ECB.advantage_twoBlockAdversary`) against the ECB cipher of every fixed block
  cipher and key law (the attack of [BonehShoup2023], §4.1.4, pp. 103–104 for one fixed cipher;
  the asymptotic statement is `BlockCipher.not_demOneTimeKeyINDCPAOn_ecbEncrypt`).
* Theorem 4.1, equation (4.3): with the message space restricted to sequences of at most `ℓ`
  distinct blocks, every adversary `A` in Attack Game 2.1 against ECB has advantage exactly twice
  the block-cipher advantage of the explicit adversary `ECB.reduction ℓ A`
  (`ECB.advantage_eq_two_mul_prpAdvantage`), which makes at most `ℓ` queries
  (`ECB.isQueryBounded_reduction`).

## Main definitions

* `Cslib.Crypto.Cipher.ecb E`: the ECB cipher of the block cipher `E : Key → Equiv.Perm D`, on
  lists of blocks of any length.
* `Cslib.Crypto.ECB.admissible ℓ`: the challenge pairs of Attack Game 2.1 for the message space
  `X^{≤ℓ}`, two messages of the same length at most `ℓ`; `ECB.distinctAdmissible ℓ` also asks that
  each message consist of distinct blocks, the message space `X_*^{≤ℓ}` of Theorem 4.1.
* `Cslib.Crypto.ECB.twoBlockAdversary x y`: the two-block attack.
* `Cslib.Crypto.ECB.reduction ℓ A`: the block-cipher adversary of the proof of Theorem 4.1. It
  draws the hidden bit itself, answers `A`'s challenge by querying its oracle on the blocks of the
  selected message, and outputs whether `A` guessed the bit.

## Main results

* `Cslib.Crypto.Cipher.ecb_correct`: ECB decrypts every encryption.
* `Cslib.Crypto.ECB.advantage_twoBlockAdversary`: the two-block attack has advantage `1`, for
  `2 ≤ ℓ` and two distinct blocks `x ≠ y`.
* `Cslib.Crypto.ECB.advantage_eq_two_mul_prpAdvantage`: `SSadv[A, E′] = 2 · BCadv[B, E]` for
  `B = ECB.reduction ℓ A`, equation (4.3).
* `Cslib.Crypto.ECB.isQueryBounded_reduction`: `ECB.reduction ℓ A` makes at most `ℓ` queries.

The statements are for a fixed block cipher (the concrete attack and equation (4.3)); the
asymptotic statements (`BlockCipher.PRP.ecb_demOneTimeKeyINDCPAOn`,
`BlockCipher.PRP.ecb_demOneTimeKeyINDCPAOn_one`, and
`BlockCipher.not_demOneTimeKeyINDCPAOn_ecbEncrypt`) are proved in
`CslibFrontier.Crypto.Computational.Encryption.ECB`. The block-cipher advantage is `PRP.advantage`
(Attack Game 4.1), against a uniform key and a uniform permutation.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], version 0.6,
  §4.1.4 (pp. 102–106) and Theorem 4.1 (pp. 104–105).
-/

public section

namespace Cslib.Crypto

open Probability

variable {Key D : Type}

/-- The ECB cipher of a block cipher `E` ([BonehShoup2023], §4.1.4, p. 102): encrypt and decrypt
every block separately under the same key. The book's `ℓ`-wise cipher is defined on `X^{≤ℓ}`; here
encryption is defined on lists of any length, and the bound `ℓ` enters through the admissible
challenge pairs (`ECB.admissible`). -/
@[expose]
def Cipher.ecb (E : Key → Equiv.Perm D) : Cipher Key (List D) (List D) where
  encrypt k m := pure (m.map (E k))
  decrypt k c := some (c.map (E k).symm)

/-- ECB decrypts every encryption. -/
theorem Cipher.ecb_correct (E : Key → Equiv.Perm D) : (Cipher.ecb E).Correct :=
  Cipher.ofPure_correct (fun k (m : List D) => m.map (E k)) (fun k c => c.map (E k).symm)
    fun k m => by simp

namespace ECB

/-- The challenge pairs of Attack Game 2.1 for ECB on `X^{≤ℓ}`: two messages of the same length,
at most `ℓ`. -/
@[expose]
def admissible (ℓ : ℕ) (m₀ m₁ : List D) : Bool :=
  decide (m₀.length = m₁.length ∧ m₀.length ≤ ℓ)

/-- The challenge pairs of Attack Game 2.1 for the message space `X_*^{≤ℓ}` of Theorem 4.1: two
messages of the same length, at most `ℓ`, each consisting of distinct blocks. -/
@[expose]
def distinctAdmissible [DecidableEq D] (ℓ : ℕ) (m₀ m₁ : List D) : Bool :=
  decide (m₀.length = m₁.length ∧ m₀.length ≤ ℓ ∧ m₀.Nodup ∧ m₁.Nodup)

/-! ### The two-block attack -/

/-- The two-block attack on ECB ([BonehShoup2023], §4.1.4, pp. 103–104): submit `m₀ = (x, x)` and
`m₁ = (x, y)` and output `true` exactly when the two ciphertext blocks are equal. -/
@[expose]
def twoBlockAdversary [DecidableEq D] (x y : D) :
    TwoStage Unit (MessagePair (List D)) (List D) Bool Unit where
  choose _ := pure (⟨[x, x], [x, y]⟩, ())
  guess _ c := pure (decide (c[0]? = c[1]?))

/-- The typed two-block attack has advantage `1` against the ECB cipher of every fixed block
cipher and key law, for `2 ≤ ℓ` and distinct blocks: the attack of [BonehShoup2023] §4.1.4
(pp. 103–104) for one fixed cipher; the asymptotic statement is
`BlockCipher.not_demOneTimeKeyINDCPAOn_ecbEncrypt` in
`CslibFrontier.Crypto.Computational.Encryption.ECB`. -/
theorem advantage_twoBlockAdversary [DecidableEq D] (E : Key → Equiv.Perm D)
    (sampleKey : ProbComp Key) {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {x y : D} (hxy : x ≠ y) :
    Experiment.advantage
      ((Cipher.ecb E).oneTimeExperiment sampleKey (admissible ℓ) (twoBlockAdversary x y) false)
      ((Cipher.ecb E).oneTimeExperiment sampleKey (admissible ℓ) (twoBlockAdversary x y) true) =
      1 := by
  have hval : admissible ℓ [x, x] [x, y] = true := by simp [admissible, hℓ]
  have hconst (c : Bool) : (ProbComp.eval sampleKey).map (fun _ => c) = PMF.pure c :=
    PMF.map_const _ _
  have h₀ : ProbComp.eval
      ((Cipher.ecb E).oneTimeExperiment sampleKey (admissible ℓ) (twoBlockAdversary x y) false) =
      PMF.pure true := by
    simp [Cipher.oneTimeExperiment, lrExperiment, twoBlockAdversary, Cipher.ecb, hval, hconst]
  have h₁ : ProbComp.eval
      ((Cipher.ecb E).oneTimeExperiment sampleKey (admissible ℓ) (twoBlockAdversary x y) true) =
      PMF.pure false := by
    simp [Cipher.oneTimeExperiment, lrExperiment, twoBlockAdversary, Cipher.ecb, hval, hxy, hconst]
  rw [Experiment.advantage, h₀, h₁]
  simp [Game.advantage, Game.succProbability]

/-! ### Theorem 4.1 -/

/-- Against a fixed function, querying every block of a list returns the image of the list. -/
private theorem run_mapM_query (f : D → D) (l : List D) :
    (l.mapM (ProbOracleComp.query (spec := fun _ : D => D))).run (fun x => pure (f x)) =
      pure (l.map f) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.mapM_cons, ih]

variable [DecidableEq D]

/-- The block-cipher adversary of the proof of Theorem 4.1 ([BonehShoup2023], p. 106). It draws
the hidden bit `b`, runs `A`'s first stage, and on an admissible pair answers the challenge by
querying its oracle on the blocks of `m_b`; it outputs whether `A`'s guess equals `b`. On an
inadmissible pair it outputs whether `false` equals `b`, as the challenger of Attack Game 2.1
returns `false` there. -/
@[expose]
noncomputable def reduction (ℓ : ℕ) {σ : Type}
    (A : TwoStage Unit (MessagePair (List D)) (List D) Bool σ) :
    ProbOracleComp (fun _ : D => D) Bool := do
  let b ← ProbOracleComp.sample (ProbComp.uniform Bool)
  let p ← ProbOracleComp.sample (A.choose ())
  if distinctAdmissible ℓ p.1.msg₀ p.1.msg₁ then
    let c ← (p.1.select b).mapM ProbOracleComp.query
    (· == b) <$> ProbOracleComp.sample (A.guess p.2 c)
  else
    return false == b

/-- `ECB.reduction ℓ A` makes at most `ℓ` queries, one per block of the challenge message. -/
theorem isQueryBounded_reduction (ℓ : ℕ) {σ : Type}
    (A : TwoStage Unit (MessagePair (List D)) (List D) Bool σ) :
    (reduction ℓ A).IsQueryBounded ℓ := by
  have hbody : ∀ (b : Bool) (p : MessagePair (List D) × σ),
      (if distinctAdmissible ℓ p.1.msg₀ p.1.msg₁ then do
          let c ← (p.1.select b).mapM ProbOracleComp.query
          (· == b) <$> ProbOracleComp.sample (A.guess p.2 c)
        else return false == b : ProbOracleComp (fun _ : D => D) Bool).IsQueryBounded ℓ := by
    intro b p
    split_ifs with h
    · have hlen : (p.1.select b).length ≤ ℓ := by
        simp only [distinctAdmissible, decide_eq_true_eq] at h
        cases b <;> simp only [MessagePair.select_false, MessagePair.select_true] <;> omega
      have hq : ((p.1.select b).mapM ProbOracleComp.query).IsQueryBounded ℓ :=
        (OracleComp.IsCostBounded.mapM fun x _ =>
          ProbOracleComp.IsQueryBounded.query (spec := fun _ : D => D) x).mono (by simpa using hlen)
      exact (hq.bind fun c =>
        (OracleComp.isCostBounded_map_iff (· == b) _ _).mpr
          (ProbOracleComp.IsQueryBounded.sample (A.guess p.2 c))).mono (by omega)
    · exact (OracleComp.IsCostBounded.pure _ 0).mono (Nat.zero_le _)
  exact ((ProbOracleComp.IsQueryBounded.sample _).bind fun b =>
    (ProbOracleComp.IsQueryBounded.sample _).bind fun p => hbody b p).mono (by omega)

/-- Against a fixed function `f`, the reduction draws the hidden bit, runs `A` on the challenge
`m_b.map f`, and returns whether `A` guessed the bit. -/
private theorem run_reduction (f : D → D) (ℓ : ℕ) {σ : Type}
    (A : TwoStage Unit (MessagePair (List D)) (List D) Bool σ) :
    (reduction ℓ A).run (fun x => pure (f x)) = do
      let b ← ProbComp.uniform Bool
      let p ← A.choose ()
      if distinctAdmissible ℓ p.1.msg₀ p.1.msg₁ then
        (· == b) <$> A.guess p.2 ((p.1.select b).map f)
      else
        return false == b := by
  simp only [reduction, ProbOracleComp.run_bind, ProbOracleComp.run_sample]
  refine bind_congr fun b => bind_congr fun p => ?_
  split_ifs
  · simp [run_mapM_query]
  · rfl

/-- The real block-cipher experiment of `ECB.reduction ℓ A` against a keyed permutation `E` is the
bit-guessing form of the one-time experiment against `Cipher.ecb E`: when the reduction's oracle is
`E k`, it plays the challenger of Attack Game 2.1 under the key `k` ([BonehShoup2023], p. 106, "it
outputs 1 with probability `Pr[W₀]`"). -/
private theorem eval_realExperiment_reduction {K : Type} [Fintype K] [Nonempty K]
    (E : K → Equiv.Perm D) (ℓ : ℕ) {σ : Type}
    (A : TwoStage Unit (MessagePair (List D)) (List D) Bool σ) :
    ProbComp.eval (PRP.realExperiment E (reduction ℓ A)) =
      ProbComp.eval (Experiment.guessBit fun b =>
        (Cipher.ecb E).oneTimeExperiment (ProbComp.uniform K) (distinctAdmissible ℓ) A b) := by
  simp only [PRP.realExperiment, PRF.realExperiment, run_reduction, Experiment.eval_guessBit,
    Cipher.oneTimeExperiment, ProbComp.eval_bind, ProbComp.eval_uniform, eval_lrExperiment,
    PMF.map_bind]
  rw [PMF.bind_comm]
  refine congrArg _ (funext fun b => congrArg _ (funext fun k => congrArg _ (funext fun p => ?_)))
  split_ifs <;> simp [Cipher.ecb]

/-- Distinct blocks are sent by a uniform permutation to a list whose law depends only on its
length: for two lists of the same length, each without repeated blocks, the images under a
uniform permutation have the same distribution ([BonehShoup2023], p. 106, Game 2). -/
private theorem map_uniform_perm_map_eq [Fintype D] {m₀ m₁ : List D} (h₀ : m₀.Nodup)
    (h₁ : m₁.Nodup) (hlen : m₀.length = m₁.length) :
    (PMF.uniformOfFintype (Equiv.Perm D)).map (fun π : Equiv.Perm D => m₀.map ⇑π) =
      (PMF.uniformOfFintype (Equiv.Perm D)).map (fun π : Equiv.Perm D => m₁.map ⇑π) := by
  let x : Fin m₀.length ↪ D := ⟨fun i => m₀[i], List.nodup_iff_injective_get.mp h₀⟩
  let y : Fin m₀.length ↪ D := ⟨fun i => m₁[i.cast hlen], (List.nodup_iff_injective_get.mp h₁).comp
    (Fin.cast_injective hlen)⟩
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_smul_eq_embedding x y
  have hm : m₁ = m₀.map τ := by
    refine List.ext_getElem (by simp [hlen]) fun i hi₁ hi₂ => ?_
    have := congrArg (· ⟨i, by simpa using hi₂⟩) hτ
    simpa [x, y, smul_apply] using this.symm
  calc (PMF.uniformOfFintype (Equiv.Perm D)).map (fun π : Equiv.Perm D => m₀.map ⇑π)
      = ((PMF.uniformOfFintype (Equiv.Perm D)).map (Equiv.mulRight τ)).map
          (fun π : Equiv.Perm D => m₀.map ⇑π) := by rw [PMF.uniformOfFintype_map_equiv]
    _ = (PMF.uniformOfFintype (Equiv.Perm D)).map (fun π : Equiv.Perm D => m₁.map ⇑π) := by
      rw [PMF.map_comp, hm]
      congr 1
      funext π
      simp [Function.comp_def]

/-- **Theorem 4.1, equation (4.3)** ([BonehShoup2023], pp. 104–105): for the ECB cipher of a
block cipher `E` over finite types, with challenge pairs restricted to sequences of at most `ℓ`
distinct blocks, every one-time adversary `A` has semantic-security advantage exactly twice the
block-cipher advantage of `ECB.reduction ℓ A`, which makes at most `ℓ` queries
(`ECB.isQueryBounded_reduction`). Keys are uniform. This is the concrete identity for a fixed
block cipher; the asymptotic statement is `BlockCipher.PRP.ecb_demOneTimeKeyINDCPAOn` in
`CslibFrontier.Crypto.Computational.Encryption.ECB`. -/
theorem advantage_eq_two_mul_prpAdvantage [Fintype Key] [Nonempty Key] [Fintype D]
    (E : Key → Equiv.Perm D) (ℓ : ℕ)
    {σ : Type} (A : TwoStage Unit (MessagePair (List D)) (List D) Bool σ) :
    Experiment.advantage
        ((Cipher.ecb E).oneTimeExperiment (ProbComp.uniform Key) (distinctAdmissible ℓ) A false)
        ((Cipher.ecb E).oneTimeExperiment (ProbComp.uniform Key) (distinctAdmissible ℓ) A true) =
      2 * PRP.advantage E (reduction ℓ A) := by
  have hlaw (b : Bool) : ProbComp.eval ((Cipher.ecb fun π : Equiv.Perm D => π).oneTimeExperiment
        (ProbComp.uniform (Equiv.Perm D)) (distinctAdmissible ℓ) A b) =
      ProbComp.eval ((Cipher.ecb fun π : Equiv.Perm D => π).oneTimeExperiment
        (ProbComp.uniform (Equiv.Perm D)) (distinctAdmissible ℓ) A false) :=
    Cipher.eval_oneTimeExperiment_eq_of_ciphertextDist_eq _ _ _ (fun m₀ m₁ h => by
      simp only [distinctAdmissible, decide_eq_true_eq] at h
      simpa [Cipher.ciphertextDist, Cipher.ecb, PMF.map, Function.comp_def] using
        map_uniform_perm_map_eq h.2.2.1 h.2.2.2 h.1) A b false
  have hideal : ProbComp.eval (PRP.idealExperiment (reduction ℓ A)) =
      PMF.uniformOfFintype Bool := by
    rw [show PRP.idealExperiment (reduction ℓ A) =
        PRP.realExperiment (fun π : Equiv.Perm D => π) (reduction ℓ A) from rfl,
      eval_realExperiment_reduction, Experiment.eval_guessBit]
    simp only [hlaw]
    exact Game.uniform_bool_bind_map_beq_const _
  rw [Experiment.advantage_eq_two_mul_guessingAdvantage_guessBit, PRP.advantage,
    eval_realExperiment_reduction, hideal]

end ECB

end Cslib.Crypto
