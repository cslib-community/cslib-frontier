/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.NP.Relation
public import CslibFrontier.Computability.Complexity.Classes.Oracle
public import CslibFrontier.Computability.Complexity.Classes.SharpP
public import CslibFrontier.Computability.Complexity.Classes.SharpP.Relation
public import CslibFrontier.Computability.Complexity.Problems.SAT
public import CslibFrontier.Computability.Complexity.AcceptCount
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Probability.BitString.AffineHash.Word
public import CslibFrontier.Probability.ApproximateCounting.Relative
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Polynomial
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.NthRoot
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Search
import CslibFrontier.Computability.Probabilistic.AffineHash
import CslibFrontier.Foundations.Data.BitString.Block
import Cslib.Foundations.Data.Polynomial.Monotone
import CslibFrontier.Computability.Complexity.Classes.Oracle.Closure
import CslibFrontier.Computability.Complexity.Classes.Oracle.Monotone
import CslibFrontier.Computability.Complexity.Classes.NP.Image
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Complexity.Classes.PH.Collapse
import CslibFrontier.Computability.Complexity.Classes.PH.SipserLautemann
import CslibFrontier.Computability.Complexity.Reduction.Turing
import CslibFrontier.Foundations.Data.BitString.WordCount
import CslibFrontier.Foundations.Data.Finset.Density
import CslibFrontier.Probability.BitString.AffineHash

/-!
# Stockmeyer's approximate counting with an `NP` oracle

Stockmeyer showed that the number `#R(a)` of witnesses of an NP relation `R` can be approximated
within any factor `1 ± 1 / q(n)`, `q` a positive polynomial and `n` the encoded length of `a`, by
a probabilistic polynomial-time algorithm with an `NP` oracle [Stockmeyer1983]
[Goldreich, Theorem 6.27][Goldreich2007Draft]. This file proves it for every polynomially
balanced PC relation (`FNP`) on the native oracle machines
(`Cslib.Complexity.ComputableInPolyTimeWithOracle`), with the oracle fixed to the set
`encCNF '' SAT` of encoded satisfiable formulas: first for `#P` functions, the counts of
certificates of exactly the prescribed length, then for all solution counts through the
count-preserving transport `searchCount_mem_SharpP`. It also proves Goldreich's Exercise 6.34,
the membership in `NP` of the sieve query.

## The algorithm

Write `m = m(n)` for the witness length, `k = 7 q(n)` and `M = k m`. The algorithm estimates the
size `#R(a) ^ k` of the `k`-fold power of the witness set, whose elements are `M`-bit strings,
within a constant factor, and takes the integer `k`-th root:

* the random string is cut into one affine hash seed for each level `j ≤ M` and each of
  `T = 12 (M + 1 + (n + 2))` trials (`Stockmeyer.seeds`);
* query `⟨a, k, j, s⟩` asks whether the affine hash to `j` bits with seed `s` sends some
  concatenation of `k` witnesses to zero (`NPRelation.hashQuery`, in `NP` with an explicit
  verifier); it is reduced to `SAT` by the Cook–Levin theorem and asked as an encoded formula;
* level `j` answers yes when more than half of its trials do (`Stockmeyer.levelYes`), and the
  estimate is `⌊(16 · 2 ^ K) ^ (1 / k)⌋` for the largest level `K` answered yes, or `0`
  (`Stockmeyer.estimateOf`), computed with the polynomial-time integer root
  `Turing.MultiTapeTM.ComputableInPolyTime.binary_nthRoot`.

The estimator equals the relative hash estimate of
`Cslib.Probability.ApproximateCounting.relativeHashEstimate` on the seeds cut from the random
string, whose analysis gives `#R(a) ≤ E ≤ (1 + 1 / q(n)) #R(a)` except with probability
`2 ^ (-(n + 2))` (`Stockmeyer.one_sub_inv_two_pow_le_dens_estimator`). The seed of level `j` is
the prefix of `j M + j` bits of a block of `M M + M` bits, which keeps the hash pairwise
independent.

## Statement-to-source mapping

* Goldreich's `R ∈ PC` is `R ∈ FNP enc` (solutions of length at most a polynomial, decided in
  polynomial time) and `#R(a)` is `searchCount R a`. The estimator itself works on a
  `Cslib.Complexity.NPRelation` (witnesses of exactly the prescribed length) with
  `#R(a) = acceptCount R.verifier a m`; `searchCount_mem_SharpP` moves every `FNP` count into
  `#P`, and `SharpP.exists_approxCount_SAT` approximates every `#P` function.
* Goldreich's probabilistic polynomial-time oracle machine is a function `E` of the instance and
  a random string of `ℓ(n)` bits, `ℓ` a polynomial, computable in polynomial time relative to the
  oracle; probabilities are densities over the random strings. The output is a natural number,
  a special case of Goldreich's rational output.
* The `(1 / q, μ)`-approximation with `μ(n) = 2 ^ (-n)`: the estimate misses `#R(a)` by more than
  `#R(a) / q(n)` with probability at most `2 ^ (-n)`.
* Exercise 6.39 asks, for every PC-complete `R`, that `(1 - 1 / p)`-approximate counting (the
  factor `1 ± 1 / p` of Theorem 6.27) and uniform generation randomly reduce to deciding
  `S_R`. Its counting half is `FNP.exists_approxCount_of_npHard`, for every `R ∈ FNP` whose
  language `searchDomain R` is `NP`-hard, which every PC-complete relation satisfies; the oracle
  is the set `enc '' searchDomain R` of encoded instances with a solution. The
  uniform-generation half is not formalized.
* Exercise 6.34 asks that `{(a, i, h, 1 ^ t) : ∃ distinct y₁, …, y_t ∈ R(a), h(y_j) = 0 ^ i}` be in
  `NP`. Here `h` ranges over the affine hashes given by a seed (the rows of the matrix, then the
  offset) and `t` is written in unary (`NPRelation.sieveQuery`,
  `NPRelation.mem_sieveQuery_language_iff`, at least `t` solutions); the exercise's question
  whether more than `t` solutions pass the sieve is the query with `t + 1`. The algorithm above
  uses the closely related query
  on `k`-fold products instead.
* Arora–Barak's Exercise 9 §6 (a), (b) [Arora and Barak, draft of 2007-01-08][AroraBarak07]: if
  `NP ⊆ P`, the same estimator, with its queries decided in polynomial time, approximates every
  `#P` function within the factor `1 - ε` with probability at least `2 / 3`
  (`SharpP.exists_approx_of_NP_subset_P`).
* Arora–Barak's Exercise 9 §6 (c), the deterministic versions: if `NP ⊆ P`, a deterministic
  polynomial-time algorithm approximates every `#P` function within the factor `1 - ε` on every
  instance (`SharpP.exists_deterministic_approx_of_NP_subset_P`), and within `1 + 1 / q(n)` for
  every positive polynomial `q` (`SharpP.exists_deterministic_approxCount_of_NP_subset_P`). The
  book's hint derandomizes through `BPP ⊆ Σ₂`; the levels of the estimate are not a `BPP`
  language, since the trials of the middle levels have no bounded error, so the Sipser–Lautemann
  shift cover is applied to each level directly: the `Σ₂` language of levels whose amplified
  trials some shifts cover (`SipserLautemann.verifier`) contains every level whose trials accept
  with probability `≥ 2 / 3` and no level whose trials reject with probability `≥ 2 / 3`, which
  makes its answers correct (`Probability.ApproximateCounting.AnswersCorrect`), and it is in `P`
  by `PH_eq_P_of_NP_subset_P`.

## Main definitions

* `Cslib.Complexity.HashQuery`, `Cslib.Complexity.encHashQuery`: hashed queries and their
  encoding.
* `Cslib.Complexity.NPRelation.hashQuery`: tuples of witnesses hashing to zero.
* `Cslib.Complexity.NPRelation.sieveQuery`: distinct witnesses passing a hash sieve.
* `Cslib.Complexity.Stockmeyer.estimator`: Stockmeyer's estimator.

## Main results

* `Cslib.Complexity.NPRelation.mem_hashQuery_language_iff`,
  `Cslib.Complexity.NPRelation.mem_sieveQuery_language_iff`: the meaning of the queries.
* `Cslib.Complexity.Stockmeyer.one_sub_inv_two_pow_le_dens_estimator`: the estimator's accuracy.
* `Cslib.Complexity.Stockmeyer.computableInPolyTimeWithOracle_estimator`: polynomial time with
  the `SAT` oracle.
* `Cslib.Complexity.SharpP.exists_approxCount_SAT`: Stockmeyer's approximate counting for `#P`
  functions with the `SAT` oracle.
* `Cslib.Complexity.FNP.exists_approxCount_SAT`: **Stockmeyer's approximate counting** for every
  polynomially balanced PC relation (Goldreich, Theorem 6.27).
* `Cslib.Complexity.FNP.exists_approxCount_of_npHard`: for a PC relation `R` with `NP`-hard
  `S_R`, approximate counting with an oracle for `S_R` (the counting half of Goldreich's
  Exercise 6.39).
* `Cslib.Complexity.SharpP.exists_approx_of_NP_subset_P`: approximate counting under `NP ⊆ P`.
* `Cslib.Complexity.SharpP.exists_deterministic_approxCount_of_NP_subset_P`,
  `Cslib.Complexity.SharpP.exists_deterministic_approx_of_NP_subset_P`: deterministic
  approximate counting under `NP ⊆ P`.

## References

* [L. Stockmeyer, *The complexity of approximate counting*][Stockmeyer1983]
* [C. Lautemann, *BPP and the polynomial hierarchy*][Lautemann1983]
* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, draft r3, February
  2007][Goldreich2007Draft]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, draft of
  2007-01-08][AroraBarak07]
-/

@[expose] public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM Cslib.BitString Cslib.BitString.LinearHash

variable {α : Type}

/-- A hashed lower-bound query about an instance of an NP relation: whether some `copies`-tuple of
witnesses for `inst`, read as one string, is sent to zero by the affine hash to `level` bits with
seed `seed` (`Cslib.BitString.LinearHash.hashZero`). -/
structure HashQuery (α : Type) where
  /-- The instance whose witnesses are hashed. -/
  inst : α
  /-- The number of witnesses in a tuple. -/
  copies : ℕ
  /-- The number of output bits of the hash. -/
  level : ℕ
  /-- The seed of the affine hash: the rows of the matrix, then the offset. -/
  seed : List Bool

/-- Encoding of `HashQuery`: the instance by `enc`, the number of copies and the level in unary,
and the seed as a bit string. -/
enc_structure encHashQuery (α : Type) (enc : α ↪ List Bool) : HashQuery α where
  inst : enc, copies : encUnary, level : encUnary, seed : encBits

namespace NPRelation

variable {enc : α ↪ List Bool} (R : NPRelation enc)

/-- The witnesses of `R` for `a`, as bit strings of the prescribed length. -/
def witnessSet (a : α) : Finset (BitString (R.certLength.eval (enc a).length)) :=
  {w | R.verifier (a, List.ofFn w) = true}

/-- The witnesses of `R` for `a` are counted by `acceptCount`. -/
theorem card_witnessSet (a : α) :
    #(R.witnessSet a) = acceptCount R.verifier a (R.certLength.eval (enc a).length) :=
  rfl

/-- The verifier of the hashed lower-bound queries: the certificate is read as `copies` blocks of
`m` bits, `m` the witness length of the instance, each of which must be a witness, and their
concatenation must hash to zero. Bits beyond the first `copies * m` are ignored. -/
def hashQueryVerifier (x : HashQuery α × List Bool) : Bool :=
  ((List.range x.1.copies).all fun i =>
      R.verifier (x.1.inst, listRow (R.certLength.eval (enc x.1.inst).length) i x.2)) &&
    hashZero x.1.level (x.1.copies * R.certLength.eval (enc x.1.inst).length) x.1.seed x.2

/-- The hashed lower-bound verifier is polynomial-time. -/
theorem computableInPolyTime_hashQueryVerifier :
    ComputableInPolyTime R.hashQueryVerifier (encPair (encHashQuery α enc) encBits) encBool := by
  have hR := R.computableInPolyTime_verifier
  unfold hashQueryVerifier
  fun_prop

/-- The certificate length `L · m(L)` of the hashed queries holds `copies` witnesses. -/
private theorem copies_mul_le (Q : HashQuery α) :
    Q.copies * R.certLength.eval (enc Q.inst).length ≤
      (Polynomial.X * R.certLength).eval (encHashQuery α enc Q).length := by
  rw [Polynomial.eval_mul, Polynomial.eval_X]
  have hn : (enc Q.inst).length ≤ (encHashQuery α enc Q).length :=
    encHashQuery_inst_length_le α enc Q
  have hk : Q.copies ≤ (encHashQuery α enc Q).length :=
    (encHashQuery_copies_length_le α enc Q).trans' (by simp)
  exact Nat.mul_le_mul hk (Polynomial.eval_mono _ hn)

/-- **The hashed lower-bound queries of Stockmeyer's algorithm form an NP relation**: a query
`⟨a, k, j, s⟩` has as witnesses the `k`-tuples of witnesses of `a` whose concatenation the affine
hash to `j` bits with seed `s` sends to zero, padded to the certificate length `L · m(L)` for the
encoded query length `L`. This is the one-solution sieve query for the `k`-fold power of `R`;
Goldreich's Exercise 6.34 query, with `t` distinct solutions, is `NPRelation.sieveQuery`. -/
noncomputable def hashQuery : NPRelation (encHashQuery α enc) where
  certLength := Polynomial.X * R.certLength
  verifier := R.hashQueryVerifier
  computableInPolyTime_verifier := R.computableInPolyTime_hashQueryVerifier

/-- On a certificate `e`, the verifier accepts exactly when the `copies` blocks of the
`copies * m`-bit view of `e` are witnesses and that view hashes to zero. -/
private theorem hashQueryVerifier_eq_true_iff (Q : HashQuery α) (e : List Bool) :
    R.hashQueryVerifier (Q, e) = true ↔
      (∀ i, block (ofList (Q.copies * R.certLength.eval (enc Q.inst).length) e) i ∈
        R.witnessSet Q.inst) ∧
      affineHash (unpackAffineSeed Q.level _ Q.seed)
        (ofList (Q.copies * R.certLength.eval (enc Q.inst).length) e) = 0 := by
  simp only [hashQueryVerifier, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    hashZero_eq_true_iff, witnessSet, mem_filter, mem_univ, true_and]
  refine and_congr ⟨fun h i => ?_, fun h i hi => ?_⟩ Iff.rfl
  · rw [← listRow_eq_ofFn]
    exact h i i.2
  · rw [listRow_eq_ofFn (count := Q.copies) _ ⟨i, hi⟩]
    exact h ⟨i, hi⟩

/-- **The meaning of the hashed lower-bound queries**: `⟨a, k, j, s⟩` is in the language exactly
when the affine hash to `j` bits with seed `s` sends some concatenation of `k` witnesses of `a` to
zero. -/
theorem mem_hashQuery_language_iff (Q : HashQuery α) :
    Q ∈ R.hashQuery.language ↔
      0 ∈ (Fintype.piFinset fun _ : Fin Q.copies => R.witnessSet Q.inst).image
        fun x => affineHash (unpackAffineSeed Q.level _ Q.seed) (blocksEquiv.symm x) := by
  rw [mem_language, mem_image]
  constructor
  · rintro ⟨e, -, he⟩
    obtain ⟨hw, hz⟩ := (R.hashQueryVerifier_eq_true_iff Q e).1 he
    exact ⟨blocksEquiv (ofList _ e), Fintype.mem_piFinset.2 hw, by
      rwa [Equiv.symm_apply_apply]⟩
  · rintro ⟨x, hx, hz⟩
    have hle := R.copies_mul_le Q
    refine ⟨List.ofFn (blocksEquiv.symm x) ++ List.replicate
      ((Polynomial.X * R.certLength).eval (encHashQuery α enc Q).length -
        Q.copies * R.certLength.eval (enc Q.inst).length) false, ?_, ?_⟩
    · simp only [List.length_append, List.length_ofFn, List.length_replicate]
      exact Nat.add_sub_cancel' hle
    · refine (R.hashQueryVerifier_eq_true_iff Q _).2 ?_
      rw [ofList_ofFn_append]
      refine ⟨fun i => ?_, hz⟩
      rw [← blocksEquiv_apply, Equiv.apply_symm_apply]
      exact Fintype.mem_piFinset.1 hx i

/-- The verifier of the sieve queries: the certificate is read as `copies` blocks of `m` bits,
`m` the witness length of the instance, which must be distinct witnesses each sent to zero by the
affine hash to `level` bits with seed `seed`. Bits beyond the first `copies * m` are ignored. -/
def sieveVerifier (x : HashQuery α × List Bool) : Bool :=
  ((List.range x.1.copies).all fun i =>
      R.verifier (x.1.inst, listRow (R.certLength.eval (enc x.1.inst).length) i x.2) &&
        hashZero x.1.level (R.certLength.eval (enc x.1.inst).length) x.1.seed
          (listRow (R.certLength.eval (enc x.1.inst).length) i x.2)) &&
    decide (listRows x.1.copies (R.certLength.eval (enc x.1.inst).length) x.2).Nodup

/-- The sieve verifier is polynomial-time. -/
theorem computableInPolyTime_sieveVerifier :
    ComputableInPolyTime R.sieveVerifier (encPair (encHashQuery α enc) encBits) encBool := by
  have hR := R.computableInPolyTime_verifier
  unfold sieveVerifier
  fun_prop

/-- **The sieve queries form an NP relation** [Goldreich, Exercise 6.34][Goldreich2007Draft]: a
query `⟨a, t, i, s⟩` has as witnesses the lists of `t` distinct witnesses of `a`, each sent to
`0 ^ i` by the affine hash `h` with seed `s`, padded to the certificate length `L · m(L)` for the
encoded query length `L`. Its language, the queries with at least `t` solutions passing the sieve
(`mem_sieveQuery_language_iff`), is in `NP` (`NPRelation.language_mem_NP`). -/
noncomputable def sieveQuery : NPRelation (encHashQuery α enc) where
  certLength := Polynomial.X * R.certLength
  verifier := R.sieveVerifier
  computableInPolyTime_verifier := R.computableInPolyTime_sieveVerifier

/-- On a certificate `e`, the sieve verifier accepts exactly when the `copies` blocks of the
`copies * m`-bit view of `e` are distinct witnesses sent to zero by the hash. -/
private theorem sieveVerifier_eq_true_iff (Q : HashQuery α) (e : List Bool) :
    R.sieveVerifier (Q, e) = true ↔
      (∀ i, block (ofList (Q.copies * R.certLength.eval (enc Q.inst).length) e) i ∈
        (R.witnessSet Q.inst).filter fun y =>
          affineHash (unpackAffineSeed Q.level _ Q.seed) y = 0) ∧
      Function.Injective (block (ofList (Q.copies * R.certLength.eval (enc Q.inst).length) e)) := by
  simp only [sieveVerifier, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, witnessSet, mem_filter, mem_univ, true_and, listRows_eq_ofFn,
    List.nodup_ofFn]
  refine and_congr ⟨fun h i => ?_, fun h i hi => ?_⟩
    (Function.Injective.of_comp_iff List.ofFn_injective _)
  · have := h i i.2
    rwa [listRow_eq_ofFn (count := Q.copies), hashZero_eq_true_iff, ofList_ofFn] at this
  · rw [listRow_eq_ofFn (count := Q.copies) _ ⟨i, hi⟩, hashZero_eq_true_iff, ofList_ofFn]
    exact h ⟨i, hi⟩

/-- **The meaning of the sieve queries**: `⟨a, t, i, s⟩` is in the language exactly when at least
`t` witnesses of `a` are sent to `0 ^ i` by the affine hash with seed `s`. -/
theorem mem_sieveQuery_language_iff (Q : HashQuery α) :
    Q ∈ R.sieveQuery.language ↔ Q.copies ≤
      #((R.witnessSet Q.inst).filter fun y =>
        affineHash (unpackAffineSeed Q.level _ Q.seed) y = 0) := by
  rw [mem_language]
  constructor
  · rintro ⟨e, -, he⟩
    obtain ⟨hw, hinj⟩ := (R.sieveVerifier_eq_true_iff Q e).1 he
    simpa using card_le_card_of_injOn (s := (univ : Finset (Fin Q.copies))) _ (fun i _ => hw i)
      hinj.injOn
  · intro hcard
    set F := (R.witnessSet Q.inst).filter
      fun y => affineHash (unpackAffineSeed Q.level _ Q.seed) y = 0
    let x : Fin Q.copies → BitString (R.certLength.eval (enc Q.inst).length) :=
      fun i => (F.equivFin.symm (Fin.castLE hcard i)).val
    have hx : Function.Injective x := fun i i' h =>
      Fin.castLE_injective hcard (F.equivFin.symm.injective (Subtype.ext h))
    refine ⟨List.ofFn (blocksEquiv.symm x) ++ List.replicate
      ((Polynomial.X * R.certLength).eval (encHashQuery α enc Q).length -
        Q.copies * R.certLength.eval (enc Q.inst).length) false, ?_, ?_⟩
    · simp only [List.length_append, List.length_ofFn, List.length_replicate]
      exact Nat.add_sub_cancel' (R.copies_mul_le Q)
    · refine (R.sieveVerifier_eq_true_iff Q _).2 ?_
      rw [ofList_ofFn_append, ← blocksEquiv_apply, Equiv.apply_symm_apply]
      exact ⟨fun i => (F.equivFin.symm (Fin.castLE hcard i)).2, hx⟩

end NPRelation

/-! ### Affine hashes seeded by a prefix -/

namespace Stockmeyer

/-- The affine hash to `j` bits of `M`-bit strings whose seed is read from the first `j M + j` bits
of a `K`-bit string. -/
private def levelHash (M K j : ℕ) (s : BitString K) (x : BitString M) : BitString j :=
  LinearHash.affineHash (unpackAffineSeed j M (List.ofFn s)) x

/-- An affine seed is read from its first `j M + j` bits. -/
private theorem unpackAffineSeed_take (j M : ℕ) (w : List Bool) :
    unpackAffineSeed j M (w.take (j * M + j)) = unpackAffineSeed j M w := by
  refine Prod.ext (funext fun i => List.ofFn_injective ?_) (List.ofFn_injective ?_)
  · rw [ofFn_unpackAffineSeed_fst, ofFn_unpackAffineSeed_fst, List.take_take,
      min_eq_left (Nat.le_add_right _ _)]
  · rw [ofFn_unpackAffineSeed_snd, ofFn_unpackAffineSeed_snd, List.drop_take,
      Nat.add_sub_cancel_left, listRow_zero, listRow_zero, ofList_take]

/-- Reading a seed from the first `j M + j` of `K ≥ j M + j` uniform bits gives a uniform seed. -/
private theorem dens_filter_unpackAffineSeed {j M K : ℕ} (hK : j * M + j ≤ K)
    (g : (Fin j → BitString M) × BitString j → Prop) [DecidablePred g] :
    dens {s : BitString K | g (unpackAffineSeed j M (List.ofFn s))} =
      dens {s : BitString (j * M + j) | g (affineSeedEquiv j M s)} := by
  have key := card_filter_take hK fun w => g (unpackAffineSeed j M w)
  simp only [unpackAffineSeed_take] at key
  simp only [Finset.dens, affineSeedEquiv_apply, BitString.card, Nat.cast_pow, Nat.cast_ofNat]
  change (#{s : BitString K | g (unpackAffineSeed j M (List.ofFn s))} : ℚ≥0) / 2 ^ K = _
  rw [key, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ← Nat.sub_add_cancel hK, pow_add,
    Nat.add_sub_cancel, mul_div_mul_left _ _ (by positivity)]

/-- **Prefix-seeded affine hashing is pairwise independent** when the `K`-bit string holds the
`j M + j` bits of a seed. -/
private theorem isPairwiseIndependentHash_levelHash {M K j : ℕ} (hK : j * M + j ≤ K) :
    Probability.IsPairwiseIndependentHash (levelHash M K j) := by
  have hh := (isPairwiseIndependentHash_affineHash j M).comp_seedEquiv (affineSeedEquiv j M)
  refine ⟨fun x y => ?_, fun hx y₁ y₂ => ?_⟩
  · rw [← hh.dens_filter_apply_eq x y]
    exact dens_filter_unpackAffineSeed hK fun seed => LinearHash.affineHash seed x = y
  · rw [← hh.dens_filter_apply_eq_and_apply_eq hx y₁ y₂]
    exact dens_filter_unpackAffineSeed hK fun seed =>
      LinearHash.affineHash seed _ = y₁ ∧ LinearHash.affineHash seed _ = y₂

/-! ### The estimator -/

variable {enc : α ↪ List Bool} (R : NPRelation enc) (q : Polynomial ℕ)

/-- The number `k(n) = 7 q(n)` of copies of the witness set, for instances of encoded length `n`:
the factor `128` of the constant-factor estimate of the `k`-fold power becomes `1 + 1 / q(n)`. -/
abbrev copies (n : ℕ) : ℕ := 7 * q.eval n

/-- The length `M(n) = k(n) m(n)` of a tuple of `k(n)` witnesses of `m(n)` bits, also the largest
level asked. -/
abbrev tupleLength (n : ℕ) : ℕ := copies q n * R.certLength.eval n

/-- Half the number of trials per level: `6 (M(n) + 1 + (n + 2))` gives failure probability
`2 ^ (-(n + 2))`. -/
abbrev majority (n : ℕ) : ℕ := 6 * (tupleLength R q n + 1 + (n + 2))

/-- The number of trials per level. -/
abbrev trials (n : ℕ) : ℕ := 2 * majority R q n

/-- The number of random bits per trial, enough for an affine seed at every level `j ≤ M(n)`. -/
abbrev seedLength (n : ℕ) : ℕ := tupleLength R q n * tupleLength R q n + tupleLength R q n

/-- The seed length of level `j`: `M(n) M(n) + M(n)` up to level `M(n)`, read from a block of
the random string, and exactly `j M(n) + j` above, where no level is asked. -/
abbrev seedLevelLength (n j : ℕ) : ℕ :=
  if j ≤ tupleLength R q n then seedLength R q n else j * tupleLength R q n + j

theorem seedLength_eq_seedLevelLength {n j : ℕ} (hj : j ≤ tupleLength R q n) :
    seedLength R q n = seedLevelLength R q n j := by
  simp only [seedLevelLength, ite_eq_left_iff.mpr (fun h => absurd hj h)]

theorem le_seedLevelLength (n j : ℕ) :
    j * tupleLength R q n + j ≤ seedLevelLength R q n j := by
  unfold seedLevelLength
  split_ifs with hj
  · exact Nat.add_le_add (Nat.mul_le_mul_right _ hj) hj
  · exact le_rfl

/-- The number of random bits: one seed for each of the `trials` trials of the `M(n) + 1`
levels. -/
abbrev randomLength (n : ℕ) : ℕ := (tupleLength R q n + 1) * trials R q n * seedLength R q n

/-- Query number `idx = i + T j` on the input `(a, r)`, `T` the number of trials: whether a hash
to `j` bits with the seed in block `idx` of `r` sends a tuple of `k` witnesses of `a` to zero. -/
def query (x : α × List Bool) (idx : ℕ) : HashQuery α :=
  ⟨x.1, copies q (enc x.1).length, idx / trials R q (enc x.1).length,
    listRow (seedLength R q (enc x.1).length) idx x.2⟩

/-- Level `j` is answered yes when more than half of its trials are answered yes in `answers`,
whose entry `i + T j` answers trial `i` of level `j`. -/
@[irreducible] def levelYes (a : α) (answers : List Bool) (j : ℕ) : Bool :=
  decide (majority R q (enc a).length < (listRow (trials R q (enc a).length) j answers).count true)

/-- The estimate from the answers: the `k`-th root of `16` times Stockmeyer's estimate of the size
of the `k`-fold power of the witness set (`Cslib.Probability.ApproximateCounting.estimate`). -/
def estimateOf (a : α) (answers : List Bool) : ℕ :=
  Nat.nthRoot (copies q (enc a).length)
    (16 * Probability.ApproximateCounting.estimate (tupleLength R q (enc a).length)
      fun j => levelYes R q a answers j = true)

open Classical in
/-- The answers to all queries on `(a, r)`. -/
noncomputable def answers (x : α × List Bool) : List Bool :=
  (List.range ((tupleLength R q (enc x.1).length + 1) * trials R q (enc x.1).length)).map
    fun idx => decide (query R q x idx ∈ R.hashQuery.language)

/-- **Stockmeyer's estimator** on the instance `a` and the random string `r`. -/
noncomputable def estimator (x : α × List Bool) : ℕ :=
  estimateOf R q x.1 (answers R q x)

/-- The hash of tuples of witnesses at level `j`, seeded by a block of random bits. -/
private abbrev tupleHash (n j : ℕ) (s : BitString (seedLevelLength R q n j))
    (x : Fin (copies q n) → BitString (R.certLength.eval n)) : BitString j :=
  levelHash (tupleLength R q n) (seedLevelLength R q n j) j s (blocksEquiv.symm x)

/-- The random string cut into one seed per level and trial. -/
private def seeds (n : ℕ) : BitString (randomLength R q n) ≃
    (∀ j : Fin (tupleLength R q n + 1), Fin (trials R q n) →
      BitString (seedLevelLength R q n j)) :=
  (blocksEquiv.trans blocksEquiv).trans (Equiv.piCongrRight fun j =>
    Equiv.arrowCongr (Equiv.refl _) (Equiv.arrowCongr
      (finCongr (seedLength_eq_seedLevelLength R q j.is_le)) (Equiv.refl Bool)))

private theorem ofFn_cast {m n : ℕ} (h : m = n) (f : BitString m) :
    List.ofFn (fun i : Fin n => f (Fin.cast h.symm i)) = List.ofFn f := by
  subst h
  rfl

private theorem count_true_ofFn {n : ℕ} (g : Fin n → Bool) :
    (List.ofFn g).count true = #{i | g i = true} := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.count_cons, ih, Fin.card_filter_univ_succ]
    cases g 0 <;> simp

private theorem estimate_congr {n : ℕ} {a b : ℕ → Prop} [DecidablePred a] [DecidablePred b]
    (h : ∀ j, a j ↔ b j) :
    Probability.ApproximateCounting.estimate n a =
      Probability.ApproximateCounting.estimate n b := by
  obtain rfl : a = b := funext fun j => propext (h j)
  congr

/-- **The estimator is the relative hash estimate** of the witness set, for the seeds cut from the
random string. -/
private theorem estimator_ofFn (a : α) (r : BitString (randomLength R q (enc a).length)) :
    estimator R q (a, List.ofFn r) =
      Probability.ApproximateCounting.relativeHashEstimate (ι := fun j => BitString
        (seedLevelLength R q (enc a).length j)) (tupleHash R q (enc a).length)
        (fun _ => 0) (R.witnessSet a) (seeds R q (enc a).length r) := by
  unfold estimator estimateOf Probability.ApproximateCounting.relativeHashEstimate
    Probability.ApproximateCounting.hashEstimate
  congr 2
  refine estimate_congr fun j => ?_
  simp only [levelYes, decide_eq_true_eq, Probability.ApproximateCounting.hashAnswer]
  have hT : 0 < trials R q (enc a).length := by simp only [trials, majority]; omega
  by_cases hj : j < tupleLength R q (enc a).length + 1
  · have key : ∀ i : Fin (trials R q (enc a).length),
        block (ofList _ (answers R q (a, List.ofFn r))) (⟨j, hj⟩ : Fin (_ + 1)) i = true ↔
          0 ∈ (Fintype.piFinset fun _ => R.witnessSet a).image
            (tupleHash R q (enc a).length j (seeds R q (enc a).length r ⟨j, hj⟩ i)) := by
      intro i
      have hidx : i.val + trials R q (enc a).length * j <
          (tupleLength R q (enc a).length + 1) * trials R q (enc a).length :=
        (finProdFinEquiv ((⟨j, hj⟩ : Fin (_ + 1)), i)).2
      have hdiv : (i.val + trials R q (enc a).length * j) / trials R q (enc a).length = j := by
        rw [Nat.add_mul_div_left _ _ hT, Nat.div_eq_of_lt i.2, zero_add]
      have hseed : List.ofFn (seeds R q (enc a).length r ⟨j, hj⟩ i) =
          listRow (seedLength R q (enc a).length) (i.val + trials R q (enc a).length * j)
            (List.ofFn r) := by
        have := listRow_eq_ofFn (count := (tupleLength R q (enc a).length + 1) *
          trials R q (enc a).length) (seedLength R q (enc a).length)
          (finProdFinEquiv ((⟨j, hj⟩ : Fin (_ + 1)), i)) (List.ofFn r)
        rw [finProdFinEquiv_apply_val, ofList_ofFn] at this
        exact (ofFn_cast (seedLength_eq_seedLevelLength R q (Nat.lt_succ_iff.mp hj)) _).trans
          this.symm
      simp only [block_apply, ofList, finProdFinEquiv_apply_val, answers,
        List.getD_eq_getElem?_getD,
        List.getElem?_map, List.getElem?_range hidx, Option.map_some, Option.getD_some,
        decide_eq_true_eq, R.mem_hashQuery_language_iff, query]
      unfold tupleHash levelHash
      rw [hseed]
      generalize (i.val + trials R q (enc a).length * j) / trials R q (enc a).length = l at hdiv ⊢
      subst hdiv
      rfl
    rw [listRow_eq_ofFn (count := tupleLength R q (enc a).length + 1) _ ⟨j, hj⟩, count_true_ofFn]
    simp only [key]
    exact ⟨fun h => ⟨hj, h⟩, fun ⟨_, h⟩ => h⟩
  · have hnil : listRow (trials R q (enc a).length) j (answers R q (a, List.ofFn r)) =
        List.replicate (trials R q (enc a).length) false := by
      rw [listRow, List.drop_eq_nil_of_le, List.nil_append, List.take_replicate, min_self]
      simp only [answers, List.length_map, List.length_range]
      exact Nat.mul_le_mul_right _ (by omega)
    simp [hnil, hj, List.count_replicate]

/-- The `k(n)`-tuples of witnesses number at most `2 ^ M(n)`. -/
private theorem card_witnessSet_pow_le (a : α) :
    #(R.witnessSet a) ^ copies q (enc a).length ≤ 2 ^ tupleLength R q (enc a).length := by
  have : #(R.witnessSet a) ≤ 2 ^ R.certLength.eval (enc a).length := by
    simpa only [BitString.card] using card_le_univ (R.witnessSet a)
  calc #(R.witnessSet a) ^ copies q (enc a).length
      ≤ (2 ^ R.certLength.eval (enc a).length) ^ copies q (enc a).length :=
        Nat.pow_le_pow_left this _
    _ = 2 ^ tupleLength R q (enc a).length := by rw [← pow_mul, mul_comm]

/-- **The estimator is accurate with high probability**: for a positive precision `q(n)`, the
estimate lies between `#R(a)` and `(1 + 1 / q(n)) #R(a)` for all but a `2 ^ (-(n + 2))` fraction
of the random strings, `n` the encoded length of `a`. -/
theorem one_sub_inv_two_pow_le_dens_estimator (a : α) (hq : q.eval (enc a).length ≠ 0) :
    1 - (2 ^ ((enc a).length + 2))⁻¹ ≤ dens {r : BitString (randomLength R q (enc a).length) |
      #(R.witnessSet a) ≤ estimator R q (a, List.ofFn r) ∧
        q.eval (enc a).length * estimator R q (a, List.ofFn r) ≤
          (q.eval (enc a).length + 1) * #(R.witnessSet a)} := by
  simp only [estimator_ofFn]
  rw [Fintype.dens_filter_comp_equiv (seeds R q (enc a).length) fun ω =>
    #(R.witnessSet a) ≤ Probability.ApproximateCounting.relativeHashEstimate
        (tupleHash R q (enc a).length) (fun _ => 0) (R.witnessSet a) ω ∧
      q.eval (enc a).length * Probability.ApproximateCounting.relativeHashEstimate
        (tupleHash R q (enc a).length) (fun _ => 0) (R.witnessSet a) ω ≤
        (q.eval (enc a).length + 1) * #(R.witnessSet a)]
  have hh : ∀ j,
      Probability.IsPairwiseIndependentHash (tupleHash R q (enc a).length j) := fun j =>
    (isPairwiseIndependentHash_levelHash (le_seedLevelLength R q _ j)).comp
      blocksEquiv.symm.injective
  have hS := card_witnessSet_pow_le R q a
  have hp : 128 * q.eval (enc a).length ^ copies q (enc a).length ≤
      (q.eval (enc a).length + 1) ^ copies q (enc a).length :=
    Probability.ApproximateCounting.two_pow_mul_pow_le_add_one_pow 7 hq
  exact Probability.ApproximateCounting.one_sub_inv_two_pow_le_dens_filter_relativeHashEstimate
    (ι := fun j => BitString (seedLevelLength R q (enc a).length j)) (Y := fun j => BitString j)
    (tupleHash R q (enc a).length) (fun _ => 0) (R.witnessSet a) hh (fun _ => BitString.card) hS
    hp ((enc a).length + 2)

/-! ### Polynomial time -/

/-- The number of random bits as a polynomial in the encoded instance length. -/
private noncomputable def randomLengthPoly : Polynomial ℕ :=
  let M := Polynomial.C 7 * q * R.certLength
  (M + 1) * (Polynomial.C 2 * (Polynomial.C 6 * (M + 1 + (Polynomial.X + 2)))) * (M * M + M)

private theorem eval_randomLengthPoly (n : ℕ) :
    (randomLengthPoly R q).eval n = randomLength R q n := by
  simp [randomLengthPoly]

private theorem unary_of_eval {f : ℕ → ℕ} (P : Polynomial ℕ) (h : ∀ n, P.eval n = f n) :
    ComputableInPolyTime f encUnary encUnary := by
  rw [show f = P.eval from funext fun n => (h n).symm]
  exact ComputableInPolyTime.unary_eval P

private theorem unary_copies : ComputableInPolyTime (copies q) encUnary encUnary :=
  unary_of_eval (Polynomial.C 7 * q) fun n => by simp

private theorem unary_tupleLength :
    ComputableInPolyTime (tupleLength R q) encUnary encUnary :=
  unary_of_eval (Polynomial.C 7 * q * R.certLength) fun n => by simp

private theorem unary_majority : ComputableInPolyTime (majority R q) encUnary encUnary :=
  unary_of_eval (Polynomial.C 6 * (Polynomial.C 7 * q * R.certLength + 1 + (Polynomial.X + 2)))
    fun n => by simp

private theorem unary_trials : ComputableInPolyTime (trials R q) encUnary encUnary :=
  unary_of_eval (Polynomial.C 2 * (Polynomial.C 6 *
    (Polynomial.C 7 * q * R.certLength + 1 + (Polynomial.X + 2)))) fun n => by simp

private theorem unary_seedLength : ComputableInPolyTime (seedLength R q) encUnary encUnary :=
  unary_of_eval ((Polynomial.C 7 * q * R.certLength) * (Polynomial.C 7 * q * R.certLength) +
    Polynomial.C 7 * q * R.certLength) fun n => by simp

/-- The estimate from the answers is computable in polynomial time. -/
private theorem computableInPolyTime_estimateOf :
    ComputableInPolyTime (fun x : α × List Bool => estimateOf R q x.1 x.2)
      (encPair enc encBits) encNat := by
  have hn : ComputableInPolyTime (fun x : α × List Bool => (enc x.1).length)
      (encPair enc encBits) encUnary := by fun_prop
  have hM : ComputableInPolyTime (fun x : α × List Bool => tupleLength R q (enc x.1).length)
      (encPair enc encBits) encUnary := (unary_tupleLength R q).comp hn
  have hk : ComputableInPolyTime (fun x : α × List Bool => copies q (enc x.1).length)
      (encPair enc encBits) encUnary := (unary_copies q).comp hn
  have hyes : ComputableInPolyTime
      (fun p : (α × List Bool) × ℕ => levelYes R q p.1.1 p.1.2 p.2)
      (encPair (encPair enc encBits) encUnary) encBool := by
    have hn' : ComputableInPolyTime (fun p : (α × List Bool) × ℕ => (enc p.1.1).length)
        (encPair (encPair enc encBits) encUnary) encUnary := hn.comp (.fst _ _)
    have hmaj : ComputableInPolyTime
        (fun p : (α × List Bool) × ℕ => majority R q (enc p.1.1).length)
        (encPair (encPair enc encBits) encUnary) encUnary := (unary_majority R q).comp hn'
    have htr : ComputableInPolyTime (fun p : (α × List Bool) × ℕ => trials R q (enc p.1.1).length)
        (encPair (encPair enc encBits) encUnary) encUnary := (unary_trials R q).comp hn'
    have hrow : ComputableInPolyTime (fun p : (α × List Bool) × ℕ =>
        listRow (trials R q (enc p.1.1).length) p.2 p.1.2)
        (encPair (encPair enc encBits) encUnary) encBits :=
      ComputableInPolyTime.bitsRowWithInput htr (.snd _ _) ((ComputableInPolyTime.snd _ _).comp
        (.fst _ _))
    unfold levelYes
    exact ComputableInPolyTime.unary_lt' hmaj
      (ComputableInPolyTime.bitsCountWithInput hrow (.const true))
  have hfind := ComputableInPolyTime.findGreatest
    (predicate := fun x j => levelYes R q x.1 x.2 j = true) hM
    (hyes.of_enc_eq fun _ => by simp only [Bool.decide_eq_true])
  have hzero : ComputableInPolyTime (fun x : α × List Bool => levelYes R q x.1 x.2 0)
      (encPair enc encBits) encBool :=
    hyes.comp (ComputableInPolyTime.id'.prod (.const 0))
  have hest : ComputableInPolyTime (fun x : α × List Bool =>
      Probability.ApproximateCounting.estimate (tupleLength R q (enc x.1).length)
        fun j => levelYes R q x.1 x.2 j = true) (encPair enc encBits) encNat := by
    unfold Probability.ApproximateCounting.estimate
    exact hzero.ite' (ComputableInPolyTime.binary_pow' (.const 2) hfind) (.const 0)
  unfold estimateOf
  exact ComputableInPolyTime.binary_nthRoot' hk
    (ComputableInPolyTime.binary_mul' (.const 16) hest)

/-- The queries are computable in polynomial time. -/
private theorem computableInPolyTime_query :
    ComputableInPolyTime (fun p : (α × List Bool) × ℕ => query R q p.1 p.2)
      (encPair (encPair enc encBits) encUnary) (encHashQuery α enc) := by
  have hn : ComputableInPolyTime (fun p : (α × List Bool) × ℕ => (enc p.1.1).length)
      (encPair (encPair enc encBits) encUnary) encUnary := by fun_prop
  have hk := (unary_copies q).comp hn
  have htr := (unary_trials R q).comp hn
  have hK := (unary_seedLength R q).comp hn
  have hlevel : ComputableInPolyTime (fun p : (α × List Bool) × ℕ =>
      p.2 / trials R q (enc p.1.1).length) (encPair (encPair enc encBits) encUnary) encUnary :=
    ComputableInPolyTime.unary_div' (.snd _ _) htr
  have hseed : ComputableInPolyTime (fun p : (α × List Bool) × ℕ =>
      listRow (seedLength R q (enc p.1.1).length) p.2 p.1.2)
      (encPair (encPair enc encBits) encUnary) encBits :=
    ComputableInPolyTime.bitsRowWithInput hK (.snd _ _)
      ((ComputableInPolyTime.snd _ _).comp (.fst _ _))
  have hinst : ComputableInPolyTime (fun p : (α × List Bool) × ℕ => p.1.1)
      (encPair (encPair enc encBits) encUnary) enc :=
    (ComputableInPolyTime.fst _ _).comp (.fst _ _)
  unfold query
  exact encHashQuery_mk_polyTime α enc hinst hk hlevel hseed

private theorem computableInPolyTime_queryCount : ComputableInPolyTime (fun x : α × List Bool =>
    (tupleLength R q (enc x.1).length + 1) * trials R q (enc x.1).length)
    (encPair enc encBits) encUnary := by
  have hn : ComputableInPolyTime (fun x : α × List Bool => (enc x.1).length)
      (encPair enc encBits) encUnary := by fun_prop
  exact (unary_of_eval ((Polynomial.C 7 * q * R.certLength + 1) * (Polynomial.C 2 *
    (Polynomial.C 6 * (Polynomial.C 7 * q * R.certLength + 1 + (Polynomial.X + 2)))))
      (f := fun n => (tupleLength R q n + 1) * trials R q n) fun n => by simp).comp hn

/-- **Stockmeyer's estimator is computable in polynomial time with a `SAT` oracle**: each query
is reduced to `SAT` by the Cook–Levin theorem and asked as an encoded formula. -/
theorem computableInPolyTimeWithOracle_estimator :
    ComputableInPolyTimeWithOracle (encCNF '' SAT) (estimator R q) (encPair enc encBits)
      encNat := by
  classical
  obtain ⟨g, hg, hgL⟩ := CookLevin.SAT_npHard (encHashQuery α enc) R.hashQuery.language
    R.hashQuery.language_mem_NP
  have hcount := computableInPolyTime_queryCount R q
  have hwords : ComputableInPolyTime (fun x : α × List Bool =>
      (List.range ((tupleLength R q (enc x.1).length + 1) * trials R q (enc x.1).length)).map
        fun idx => encCNF (g (query R q x idx))) (encPair enc encBits) (encList encBits) :=
    ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hcount)
      (hg.encoding_comp.comp (computableInPolyTime_query R q))
  have hmem := (computableInPolyTimeWithOracle_map_mem (encCNF '' SAT)).preprocess hwords
  have hpost : ComputableInPolyTime (fun p : (α × List Bool) × List Bool =>
      estimateOf R q p.1.1 p.2) (encPair (encPair enc encBits) encBits) encNat :=
    (computableInPolyTime_estimateOf R q).comp
      (((ComputableInPolyTime.fst _ _).comp (.fst _ _)).prod (.snd _ _))
  have h := hmem.map_with (g := fun x ans => estimateOf R q x.1 ans) hpost
  convert h using 2 with x
  simp only [estimator, answers, List.map_map]
  congr 2
  funext idx
  simp only [Function.comp_apply, encCNF.injective.mem_set_image, hgL]

/-- **Under `NP ⊆ P` the estimator is computable in polynomial time**: the hashed lower-bound
queries are then decided in polynomial time. -/
theorem computableInPolyTime_estimator_of_NP_subset_P
    (h : ∀ {β : Type} (encB : β ↪ List Bool), NP encB ⊆ P encB) :
    ComputableInPolyTime (estimator R q) (encPair enc encBits) encNat := by
  classical
  obtain ⟨d, hd, hdL⟩ := h _ R.hashQuery.language_mem_NP
  have hans : ComputableInPolyTime (fun x : α × List Bool =>
      (List.range ((tupleLength R q (enc x.1).length + 1) * trials R q (enc x.1).length)).map
        fun idx => d (query R q x idx)) (encPair enc encBits) encBits :=
    ComputableInPolyTime.listToBits.comp (ComputableInPolyTime.mapWithInput
      (ComputableInPolyTime.range.comp (computableInPolyTime_queryCount R q))
      (hd.comp (computableInPolyTime_query R q)))
  refine ((computableInPolyTime_estimateOf R q).comp
    ((ComputableInPolyTime.fst _ _).prod hans)).of_enc_eq
    fun x => ?_
  simp only [estimator, answers]
  congr 3
  funext idx
  simp only [hdL, Bool.decide_eq_true]

/-- An event disjoint from an event of probability at least `1 - x` has probability at most
`x`. -/
private theorem dens_le_of_one_sub_le {L : ℕ} {good bad : BitString L → Prop} [DecidablePred good]
    [DecidablePred bad] (h : ∀ r, bad r → ¬ good r) {x : ℚ≥0}
    (hgood : 1 - x ≤ dens {r | good r}) : dens {r | bad r} ≤ x := by
  have hsplit := dens_filter_add_dens_filter_not_eq_dens (s := (univ : Finset (BitString L))) good
  rw [dens_univ] at hsplit
  refine (dens_le_dens (t := {r | ¬ good r}) fun r hr => ?_).trans
    (le_of_add_le_add_left (a := dens {r | good r}) ?_)
  · simp only [mem_filter, mem_univ, true_and] at hr ⊢
    exact h r hr
  · rw [tsub_le_iff_right] at hgood
    rw [hsplit]
    exact hgood

/-- The failure event of an `(1 / q, 2 ^ (-(n + 2)))`-approximation: the estimate misses `#R(a)`
by more than `#R(a) / q(n)` for at most a `2 ^ (-(n + 2))` fraction of the random strings. -/
private theorem dens_lt_abs_estimator_sub_le (a : α) (hq : q.eval (enc a).length ≠ 0) :
    dens {r : BitString (randomLength R q (enc a).length) |
      (#(R.witnessSet a) : ℚ) / q.eval (enc a).length <
        |(estimator R q (a, List.ofFn r) : ℚ) - #(R.witnessSet a)|} ≤
      (2 ^ ((enc a).length + 2))⁻¹ := by
  refine dens_le_of_one_sub_le (fun r hr ⟨hle, hmul⟩ => ?_)
    (one_sub_inv_two_pow_le_dens_estimator R q a hq)
  have hp : (0 : ℚ) < ((q.eval (enc a).length : ℕ) : ℚ) := by
    exact_mod_cast Nat.pos_of_ne_zero hq
  have hle' : (#(R.witnessSet a) : ℚ) ≤ estimator R q (a, List.ofFn r) := by exact_mod_cast hle
  have hmul' : ((q.eval (enc a).length : ℕ) : ℚ) * estimator R q (a, List.ofFn r) ≤
      (((q.eval (enc a).length : ℕ) : ℚ) + 1) * #(R.witnessSet a) := by exact_mod_cast hmul
  rw [abs_of_nonneg (sub_nonneg.2 hle'), div_lt_iff₀ hp] at hr
  linarith

/-! ### Deterministic levels under `NP ⊆ P`

Under `NP ⊆ P` each level of the estimate is decided deterministically. A single trial of level
`j` on the instance `a` asks one hashed lower-bound query with the seed read from a random
string; level `j` is answered yes when some shifts of the amplified trials cover every random
string (`SipserLautemann.verifier`). This is a `Σ₂` language, hence in `P` by
`PH_eq_P_of_NP_subset_P`. It contains the levels whose trials accept with probability at least
`2 / 3` and no level whose trials reject with probability at least `2 / 3`, which by the first and
second moment bounds of pairwise independent hashing makes its answers correct
(`Probability.ApproximateCounting.AnswersCorrect`) for the size `#R(a) ^ k` of the `k`-fold power
of the witness set. -/

/-- The seed length `n' (7 q(n') m(n')) + n'` of one trial on a level instance `(a, j)` of
encoded length `n'`: enough for the affine seed of level `j` on tuples of `M(|a|)` bits. -/
private noncomputable def trialSeedPoly : Polynomial ℕ :=
  Polynomial.X * (Polynomial.C 7 * q * R.certLength) + Polynomial.X

private theorem le_eval_trialSeedPoly (a : α) (j : ℕ) :
    j * tupleLength R q (enc a).length + j ≤
      (trialSeedPoly R q).eval (encPair enc encUnary (a, j)).length := by
  have hn : (enc a).length ≤ (encPair enc encUnary (a, j)).length := by
    simp only [length_encPair]
    omega
  have hj : j ≤ (encPair enc encUnary (a, j)).length := by
    simp only [length_encPair, encUnary_apply, List.length_replicate]
    omega
  have hM := Polynomial.eval_mono (Polynomial.C 7 * q * R.certLength) hn
  simp only [Polynomial.eval_mul, Polynomial.eval_C] at hM
  simp only [trialSeedPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C]
  exact Nat.add_le_add (Nat.mul_le_mul hj hM) hj

open Classical in
/-- One trial of level `j` on the instance `a`: whether the affine hash to `j` bits with the seed
read from the random string sends some `k(n)`-tuple of witnesses of `a` to zero. -/
private noncomputable def levelTrial (x : (α × ℕ) × List Bool) : Bool :=
  decide ((⟨x.1.1, copies q (enc x.1.1).length, x.1.2, x.2⟩ : HashQuery α) ∈
    R.hashQuery.language)

/-- The levels answered yes: those `(a, j)` for which some shifts of the amplified trials of level
`j` cover every random string, Lautemann's `Σ₂` form of a majority of accepting trials. -/
private def levelLanguage : Set (α × ℕ) :=
  {x | Alternation true ([SipserLautemann.witnessPoly (trialSeedPoly R q),
      SipserLautemann.seedPoly (trialSeedPoly R q)].map
        fun p => p.eval (encPair enc encUnary x).length)
    fun w => SipserLautemann.verifier (encPair enc encUnary) (trialSeedPoly R q)
      (levelTrial R q) (x, w) = true}

/-- **Under `NP ⊆ P` the levels are decided in polynomial time**: the trials are then decided in
polynomial time, so the level language is in `Σ₂`, which collapses to `P`. -/
private theorem levelLanguage_mem_P
    (h : ∀ {β : Type} (encB : β ↪ List Bool), NP encB ⊆ P encB) :
    levelLanguage R q ∈ P (encPair enc encUnary) := by
  classical
  obtain ⟨d, hd, hdL⟩ := h _ R.hashQuery.language_mem_NP
  have hn : ComputableInPolyTime (fun x : (α × ℕ) × List Bool => (enc x.1.1).length)
      (encPair (encPair enc encUnary) encBits) encUnary := by fun_prop
  have hQ : ComputableInPolyTime (fun x : (α × ℕ) × List Bool =>
      (⟨x.1.1, copies q (enc x.1.1).length, x.1.2, x.2⟩ : HashQuery α))
      (encPair (encPair enc encUnary) encBits) (encHashQuery α enc) :=
    encHashQuery_mk_polyTime α enc ((ComputableInPolyTime.fst _ _).comp (.fst _ _))
      ((unary_copies q).comp hn) ((ComputableInPolyTime.snd _ _).comp (.fst _ _)) (.snd _ _)
  have hV : ComputableInPolyTime (levelTrial R q) (encPair (encPair enc encUnary) encBits)
      encBool :=
    (hd.comp hQ).of_enc_eq fun x => by
      simp only [levelTrial, Function.comp_apply, hdL, Bool.decide_eq_true]
  rw [← PH_eq_P_of_NP_subset_P h]
  exact SigmaP_subset_PH 2 ⟨_, _, rfl, SipserLautemann.verifier_polyTime hV, fun _ => Iff.rfl⟩

/-- **The deterministic answers are correct**: the levels `j ≤ M(n)` with `(a, j)` in the level
language are correct answers for the `#R(a) ^ k` tuples of witnesses. -/
private theorem answersCorrect_levelLanguage (a : α) :
    Probability.ApproximateCounting.AnswersCorrect (tupleLength R q (enc a).length)
      (#(R.witnessSet a) ^ copies q (enc a).length) fun j => (a, j) ∈ levelLanguage R q := by
  set S := Fintype.piFinset fun _ : Fin (copies q (enc a).length) => R.witnessSet a
  have hS : #S = #(R.witnessSet a) ^ copies q (enc a).length := Fintype.card_piFinset_const _ _
  -- the trials of level `j` are the hits of `0` by a pairwise independent hash family
  have htrial : ∀ j {K : ℕ} (s : BitString K), levelTrial R q ((a, j), List.ofFn s) = true ↔
      0 ∈ S.image fun x => levelHash (tupleLength R q (enc a).length) K j s (blocksEquiv.symm x) :=
    fun j K s => by
      simp only [levelTrial, decide_eq_true_eq, R.mem_hashQuery_language_iff]
      rfl
  have hh : ∀ j, Probability.IsPairwiseIndependentHash fun
      (s : BitString ((trialSeedPoly R q).eval (encPair enc encUnary (a, j)).length))
      (x : Fin (copies q (enc a).length) → BitString (R.certLength.eval (enc a).length)) =>
      levelHash (tupleLength R q (enc a).length) _ j s (blocksEquiv.symm x) := fun j =>
    (isPairwiseIndependentHash_levelHash (le_eval_trialSeedPoly R q a j)).comp
      blocksEquiv.symm.injective
  have hsplit : ∀ j,
      #{s : BitString ((trialSeedPoly R q).eval (encPair enc encUnary (a, j)).length) |
        levelTrial R q ((a, j), List.ofFn s) = true} +
      #{s : BitString ((trialSeedPoly R q).eval (encPair enc encUnary (a, j)).length) |
        levelTrial R q ((a, j), List.ofFn s) = false} =
      2 ^ (trialSeedPoly R q).eval (encPair enc encUnary (a, j)).length := fun j => by
    rw [← BitString.card, ← card_univ, ← card_filter_add_card_filter_not
      (s := univ) fun s => levelTrial R q ((a, j), List.ofFn s) = true]
    simp only [Bool.not_eq_true]
  -- many tuples: at most a quarter of the trials miss `0`
  have hyes : ∀ j, 4 * 2 ^ j ≤ #S → (a, j) ∈ levelLanguage R q := fun j hj => by
    refine SipserLautemann.alternation_verifier_of_accepts ?_
    have hb := (hh j).four_mul_card_filter_notMem_image_le (S := S)
      (by rwa [BitString.card]) 0
    rw [BitString.card] at hb
    have he : #{s : BitString ((trialSeedPoly R q).eval (encPair enc encUnary (a, j)).length) |
        levelTrial R q ((a, j), List.ofFn s) = false} =
        #{s : BitString ((trialSeedPoly R q).eval (encPair enc encUnary (a, j)).length) |
          0 ∉ S.image fun x =>
            levelHash (tupleLength R q (enc a).length) _ j s (blocksEquiv.symm x)} :=
      congrArg Finset.card (filter_congr fun s _ => by rw [← Bool.not_eq_true, htrial])
    rw [← he] at hb
    have := hsplit j
    omega
  -- few tuples: at most a quarter of the trials hit `0`
  have hno : ∀ j, 4 * #S ≤ 2 ^ j → (a, j) ∉ levelLanguage R q := fun j hj => by
    refine SipserLautemann.not_alternation_verifier_of_rejects ?_
    have hb := (hh j).four_mul_card_filter_mem_image_le (S := S) (by rwa [BitString.card]) 0
    rw [BitString.card] at hb
    have he : #{s : BitString ((trialSeedPoly R q).eval (encPair enc encUnary (a, j)).length) |
        levelTrial R q ((a, j), List.ofFn s) = true} =
        #{s : BitString ((trialSeedPoly R q).eval (encPair enc encUnary (a, j)).length) |
          0 ∈ S.image fun x =>
            levelHash (tupleLength R q (enc a).length) _ j s (blocksEquiv.symm x)} :=
      congrArg Finset.card (filter_congr fun s _ => htrial j s)
    rw [← he] at hb
    have := hsplit j
    omega
  refine ⟨⟨fun h0 => ?_, fun hc => ?_⟩, fun j _ hj => hyes j (by omega),
    fun j _ hj => hno j (by omega)⟩
  · by_contra hc
    exact hno 0 (by omega) h0
  · -- level `0`: every hash value is `0`, so every trial accepts
    refine SipserLautemann.alternation_verifier_of_accepts ?_
    obtain ⟨x, hx⟩ : S.Nonempty := card_pos.1 (hS ▸ hc)
    have hall : #{s : BitString ((trialSeedPoly R q).eval (encPair enc encUnary (a, 0)).length) |
        levelTrial R q ((a, 0), List.ofFn s) = true} =
        2 ^ (trialSeedPoly R q).eval (encPair enc encUnary (a, 0)).length := by
      rw [← BitString.card, ← card_univ]
      exact congrArg Finset.card (filter_true_of_mem fun s _ =>
        (htrial 0 s).2 (mem_image.2 ⟨x, hx, Subsingleton.elim _ _⟩))
    omega

/-- **The deterministic estimate is accurate**: for decided levels `b j ↔ (a, j) ∈ levelLanguage`
and a positive precision `q(n)`, the `k(n)`-th root of `16` times the estimate from these answers
lies between `#R(a)` and `(1 + 1 / q(n)) #R(a)`. -/
private theorem le_and_mul_le_nthRoot_estimate (a : α) (hq : q.eval (enc a).length ≠ 0)
    {b : ℕ → Prop} [DecidablePred b] (hb : ∀ j, b j ↔ (a, j) ∈ levelLanguage R q) :
    #(R.witnessSet a) ≤ Nat.nthRoot (copies q (enc a).length)
        (16 * Probability.ApproximateCounting.estimate (tupleLength R q (enc a).length) b) ∧
      q.eval (enc a).length * Nat.nthRoot (copies q (enc a).length)
          (16 * Probability.ApproximateCounting.estimate (tupleLength R q (enc a).length) b) ≤
        (q.eval (enc a).length + 1) * #(R.witnessSet a) := by
  classical
  have hc := answersCorrect_levelLanguage R q a
  rw [estimate_congr hb]
  refine Probability.ApproximateCounting.le_nthRoot_and_mul_nthRoot_le (by simp [copies, hq])
    (hc.le_estimate (card_witnessSet_pow_le R q a)) ?_
    (Probability.ApproximateCounting.two_pow_mul_pow_le_add_one_pow 7 hq)
  rw [show 2 ^ 7 = 16 * 8 by norm_num, mul_assoc]
  exact Nat.mul_le_mul_left 16 hc.estimate_le

end Stockmeyer

namespace SharpP

open Stockmeyer

variable {enc : α ↪ List Bool}

/-- **Stockmeyer's approximate counting for `#P` functions, with a `SAT` oracle.** This is a step
toward Goldreich's Theorem 6.27 [Goldreich2007Draft] [Stockmeyer1983], not the cited result: it
approximates functions `f ∈ #P`, which count the accepted certificates of exactly the prescribed
length, while the theorem counts the solutions of any polynomially balanced PC relation (`FNP`).
The theorem itself is `FNP.exists_approxCount_SAT`, which transports those counts into `#P` by
`searchCount_mem_SharpP`.

For every positive polynomial `q`, a polynomial-time oracle algorithm with the `SAT` oracle,
reading `ℓ(n)` random bits for a polynomial `ℓ`, outputs an estimate `E` that misses `f(a)` by
more than `f(a) / q(n)` with probability at most `2 ^ (-n)`, `n` the encoded length of `a`. The
oracle is the set of encoded satisfiable formulas, and the estimate is a natural number. -/
theorem exists_approxCount_SAT {f : α → ℕ} (hf : f ∈ SharpP enc) (q : Polynomial ℕ)
    (hq : ∀ n, q.eval n ≠ 0) :
    ∃ (ℓ : Polynomial ℕ) (E : α × List Bool → ℕ),
      ComputableInPolyTimeWithOracle (encCNF '' SAT) E (encPair enc encBits) encNat ∧
      ∀ a, dens {r : BitString (ℓ.eval (enc a).length) |
        (f a : ℚ) / q.eval (enc a).length < |(E (a, List.ofFn r) : ℚ) - f a|} ≤
        (2 ^ (enc a).length)⁻¹ := by
  obtain ⟨p, V, hV, hfV⟩ := hf
  let R : NPRelation enc := ⟨p, V, hV⟩
  refine ⟨randomLengthPoly R q, estimator R q, computableInPolyTimeWithOracle_estimator R q,
    fun a => ?_⟩
  rw [eval_randomLengthPoly, hfV a, ← R.card_witnessSet a]
  refine (dens_lt_abs_estimator_sub_le R q a (hq _)).trans ?_
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (Nat.le_add_right _ _))

/-- The precision `P = ⌈1 / ε⌉ + 1` has `1 ≤ ε P`. -/
private theorem one_le_mul_ceil_inv_add_one {ε : ℚ} (hε : 0 < ε) :
    1 ≤ ε * ((⌈ε⁻¹⌉₊ + 1 : ℕ) : ℚ) := by
  have h1 : ε⁻¹ ≤ ⌈ε⁻¹⌉₊ := Nat.le_ceil _
  push_cast
  calc (1 : ℚ) = ε * ε⁻¹ := (mul_inv_cancel₀ hε.ne').symm
    _ ≤ ε * (⌈ε⁻¹⌉₊ + 1) := by gcongr; linarith

/-- The factor `1 - ε` from the relative error `1 / P` with `1 ≤ ε P`: if `c ≤ E` and
`P E ≤ (P + 1) c`, then `(1 - ε) c ≤ E` and `(1 - ε) E ≤ c`. -/
private theorem one_sub_mul_le_and_one_sub_mul_le {ε : ℚ} {P c E : ℕ} (hεP : 1 ≤ ε * P)
    (hle : c ≤ E) (hmul : P * E ≤ (P + 1) * c) : (1 - ε) * c ≤ E ∧ (1 - ε) * E ≤ c := by
  have hle' : (c : ℚ) ≤ E := by exact_mod_cast hle
  have hmul' : (P : ℚ) * E ≤ ((P : ℚ) + 1) * c := by exact_mod_cast hmul
  have hc : (0 : ℚ) ≤ c := by positivity
  have hP0 : (0 : ℚ) < P := by
    rcases Nat.eq_zero_or_pos P with hP | hP
    · simp [hP] at hεP
      linarith
    · exact_mod_cast hP
  have hε : 0 < ε := by nlinarith
  constructor
  · nlinarith
  · rcases le_or_gt 1 ε with h1 | h1
    · nlinarith
    · nlinarith

/-- **Approximate counting under `NP ⊆ P`** [Arora and Barak, Chapter 9, Exercise 6][AroraBarak07]:
if `NP ⊆ P`, then for every function `f ∈ #P` and every `ε > 0` a polynomial-time algorithm
reading `ℓ(n)` random bits, for a polynomial `ℓ`, approximates `f` within the factor `1 - ε`,
`(1 - ε) f(a) ≤ A(a)` and `(1 - ε) A(a) ≤ f(a)`, with probability at least `2 / 3`; for
`0 < ε < 1` the second inequality reads `A(a) ≤ f(a) / (1 - ε)`. For `ε = 1 / 2` this
is the approximation within the factor `1 / 2`, `f(a) / 2 ≤ A(a) ≤ 2 f(a)`, of the exercise's
first part. The algorithm is Stockmeyer's estimator (`Cslib.Complexity.Stockmeyer.estimator`)
with the constant precision `⌈1 / ε⌉ + 1`, whose `NP` queries are answered in polynomial time.
The deterministic form is `SharpP.exists_deterministic_approx_of_NP_subset_P`. -/
theorem exists_approx_of_NP_subset_P
    (h : ∀ {β : Type} (encB : β ↪ List Bool), NP encB ⊆ P encB) {f : α → ℕ}
    (hf : f ∈ SharpP enc) {ε : ℚ} (hε : 0 < ε) :
    ∃ (ℓ : Polynomial ℕ) (A : α × List Bool → ℕ),
      ComputableInPolyTime A (encPair enc encBits) encNat ∧
      ∀ a, 2 / 3 ≤ dens {r : BitString (ℓ.eval (enc a).length) |
        (1 - ε) * f a ≤ A (a, List.ofFn r) ∧ (1 - ε) * A (a, List.ofFn r) ≤ f a} := by
  obtain ⟨p, V, hV, hfV⟩ := hf
  let R : NPRelation enc := ⟨p, V, hV⟩
  let P : ℕ := ⌈ε⁻¹⌉₊ + 1
  refine ⟨randomLengthPoly R (Polynomial.C P), estimator R (Polynomial.C P),
    computableInPolyTime_estimator_of_NP_subset_P R _ h, fun a => ?_⟩
  rw [eval_randomLengthPoly]
  have hgood := one_sub_inv_two_pow_le_dens_estimator R (Polynomial.C P) a (by simp [P])
  refine le_trans ?_ (hgood.trans (dens_le_dens fun r hr => ?_))
  · have hinv : ((2 : ℚ≥0) ^ ((enc a).length + 2))⁻¹ ≤ 1 / 4 := by
      rw [one_div]
      exact inv_anti₀ (by norm_num) (by
        calc (4 : ℚ≥0) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ ((enc a).length + 2) := pow_le_pow_right₀ (by norm_num) (by omega))
    rw [le_tsub_iff_right (hinv.trans (by norm_num [← NNRat.coe_le_coe]))]
    calc (2 / 3 : ℚ≥0) + (2 ^ ((enc a).length + 2))⁻¹ ≤ 2 / 3 + 1 / 4 := by gcongr
      _ ≤ 1 := by norm_num [← NNRat.coe_le_coe]
  · simp only [mem_filter, mem_univ, true_and, Polynomial.eval_C] at hr ⊢
    rw [hfV a, ← R.card_witnessSet a]
    exact one_sub_mul_le_and_one_sub_mul_le (one_le_mul_ceil_inv_add_one hε) hr.1 hr.2

/-- **Deterministic approximate counting under `NP ⊆ P`**, with any polynomial precision: if
`NP ⊆ P`, then for every function `f ∈ #P` and every positive polynomial `q`, a deterministic
polynomial-time algorithm `A` has `f(a) ≤ A(a) ≤ (1 + 1 / q(n)) f(a)` for every instance `a`, `n`
its encoded length. The algorithm decides each level `j` of Stockmeyer's estimate for the
`7 q(n)`-fold power of the witness set by a `Σ₂` language, the Sipser–Lautemann shift cover of
the hashed lower-bound queries of that level, which is in `P` as the polynomial hierarchy
collapses (`PH_eq_P_of_NP_subset_P`); it outputs the `7 q(n)`-th root of `16` times the estimate
from these answers. -/
theorem exists_deterministic_approxCount_of_NP_subset_P
    (h : ∀ {β : Type} (encB : β ↪ List Bool), NP encB ⊆ P encB) {f : α → ℕ}
    (hf : f ∈ SharpP enc) (q : Polynomial ℕ) (hq : ∀ n, q.eval n ≠ 0) :
    ∃ A : α → ℕ, ComputableInPolyTime A enc encNat ∧
      ∀ a, f a ≤ A a ∧ q.eval (enc a).length * A a ≤ (q.eval (enc a).length + 1) * f a := by
  classical
  obtain ⟨p, V, hV, hfV⟩ := hf
  let R : NPRelation enc := ⟨p, V, hV⟩
  obtain ⟨D, hD, hDL⟩ := levelLanguage_mem_P R q h
  refine ⟨fun a => Nat.nthRoot (copies q (enc a).length)
    (16 * Probability.ApproximateCounting.estimate (tupleLength R q (enc a).length)
      fun j => D (a, j) = true), ?_, fun a => ?_⟩
  · have hn : ComputableInPolyTime (fun a : α => (enc a).length) enc encUnary := by fun_prop
    have hfind := ComputableInPolyTime.findGreatest (predicate := fun a j => D (a, j) = true)
      ((unary_tupleLength R q).comp hn) (hD.of_enc_eq fun _ => by simp only [Bool.decide_eq_true])
    have hzero : ComputableInPolyTime (fun a : α => D (a, 0)) enc encBool :=
      hD.comp (ComputableInPolyTime.id'.prod (.const 0))
    have hest : ComputableInPolyTime (fun a : α =>
        Probability.ApproximateCounting.estimate (tupleLength R q (enc a).length)
          fun j => D (a, j) = true) enc encNat := by
      unfold Probability.ApproximateCounting.estimate
      exact hzero.ite' (ComputableInPolyTime.binary_pow' (.const 2) hfind) (.const 0)
    exact ComputableInPolyTime.binary_nthRoot' ((unary_copies q).comp hn)
      (ComputableInPolyTime.binary_mul' (.const 16) hest)
  · rw [hfV a, ← R.card_witnessSet a]
    exact le_and_mul_le_nthRoot_estimate R q a (hq _) fun j => (hDL (a, j)).symm

/-- **Deterministic approximate counting under `NP ⊆ P`** [Arora and Barak, Chapter 9, Exercise
6(c)][AroraBarak07]: if `NP ⊆ P`, then for every function `f ∈ #P` and every `ε > 0` a
deterministic polynomial-time algorithm `A` approximates `f` within the factor `1 - ε`,
`(1 - ε) f(a) ≤ A(a)` and `(1 - ε) A(a) ≤ f(a)`, for every instance `a`; for `0 < ε < 1` the
second inequality reads `A(a) ≤ f(a) / (1 - ε)`, and `ε = 1 / 2` gives the deterministic form
`f(a) / 2 ≤ A(a) ≤ 2 f(a)` of the exercise's part (a). Instances are encoded by `enc` and the
output in binary (`encNat`). The algorithm is that of
`SharpP.exists_deterministic_approxCount_of_NP_subset_P` with the constant precision
`⌈1 / ε⌉ + 1`; the book's hint derandomizes through `BPP ⊆ Σ₂` (Sipser–Gács–Lautemann, Theorem
7.18 of the draft), which is applied here to each level of the estimate. -/
theorem exists_deterministic_approx_of_NP_subset_P
    (h : ∀ {β : Type} (encB : β ↪ List Bool), NP encB ⊆ P encB) {f : α → ℕ}
    (hf : f ∈ SharpP enc) {ε : ℚ} (hε : 0 < ε) :
    ∃ A : α → ℕ, ComputableInPolyTime A enc encNat ∧
      ∀ a, (1 - ε) * f a ≤ A a ∧ (1 - ε) * A a ≤ f a := by
  obtain ⟨A, hA, hAf⟩ := exists_deterministic_approxCount_of_NP_subset_P h hf
    (Polynomial.C (⌈ε⁻¹⌉₊ + 1)) fun _ => by simp
  refine ⟨A, hA, fun a => ?_⟩
  obtain ⟨hle, hmul⟩ := hAf a
  rw [Polynomial.eval_C] at hmul
  exact one_sub_mul_le_and_one_sub_mul_le (one_le_mul_ceil_inv_add_one hε) hle hmul

end SharpP

namespace FNP

variable {enc : α ↪ List Bool}

/-- **Stockmeyer's approximate counting** [Goldreich, Theorem 6.27][Goldreich2007Draft]
[Stockmeyer1983]: for every polynomially balanced, polynomial-time checkable search relation `R`
(Goldreich's `PC`, here `FNP`) and every positive polynomial `q`, a polynomial-time oracle
algorithm with the `SAT` oracle, reading `ℓ(n)` random bits for a polynomial `ℓ`, outputs an
estimate `E` of the number `#R(a) = searchCount R a` of solutions of `a` that misses it by more
than `#R(a) / q(n)` with probability at most `2 ^ (-n)`, `n` the encoded length of `a`. The
oracle is the set of encoded satisfiable formulas, and the estimate is a natural number, a special
case of Goldreich's rational output. Solutions of all lengths are counted: the count is moved
into `#P` by `searchCount_mem_SharpP` and approximated by `SharpP.exists_approxCount_SAT`. -/
theorem exists_approxCount_SAT {R : α → List Bool → Prop} (hR : R ∈ FNP enc)
    (q : Polynomial ℕ) (hq : ∀ n, q.eval n ≠ 0) :
    ∃ (ℓ : Polynomial ℕ) (E : α × List Bool → ℕ),
      ComputableInPolyTimeWithOracle (encCNF '' SAT) E (encPair enc encBits) encNat ∧
      ∀ a, dens {r : BitString (ℓ.eval (enc a).length) |
        (searchCount R a : ℚ) / q.eval (enc a).length <
          |(E (a, List.ofFn r) : ℚ) - searchCount R a|} ≤ (2 ^ (enc a).length)⁻¹ :=
  SharpP.exists_approxCount_SAT (searchCount_mem_SharpP hR) q hq

end FNP

/-- **Approximate counting with an `S_R` oracle** [Goldreich, Exercise 6.39][Goldreich2007Draft],
its approximate-counting half: for every polynomially balanced, polynomial-time checkable search
relation `R` (Goldreich's `PC`, here `FNP`) whose solution-existence language
`S_R = searchDomain R` is `NP`-hard, and every positive polynomial `q`, approximating the number
`#R(a) = searchCount R a` of solutions within `#R(a) / q(n)` randomly reduces to deciding `S_R`.
A polynomial-time oracle algorithm with the oracle `enc '' searchDomain R`, reading `ℓ(n)` random
bits for a polynomial `ℓ`, misses `#R(a)` by more than `#R(a) / q(n)` with probability at most
`2 ^ (-n)`, `n` the encoded length of `a`. Every PC-complete `R` qualifies: a Levin reduction of
another relation to `R` is a Karp reduction of the languages (`LevinHard.npHard`). Following the
source's guideline, the `SAT` oracle of Stockmeyer's algorithm (`FNP.exists_approxCount_SAT`)
is replaced by `S_R` through a Karp reduction of `SAT` to `S_R`. The exercise's
uniform-generation half is not proved here. -/
theorem FNP.exists_approxCount_of_npHard {enc : α ↪ List Bool} {R : α → List Bool → Prop}
    (hR : R ∈ FNP enc) (hS : NPHard enc (searchDomain R)) (q : Polynomial ℕ)
    (hq : ∀ n, q.eval n ≠ 0) :
    ∃ (ℓ : Polynomial ℕ) (E : α × List Bool → ℕ),
      ComputableInPolyTimeWithOracle (enc '' searchDomain R) E (encPair enc encBits) encNat ∧
      ∀ a, dens {r : BitString (ℓ.eval (enc a).length) |
        (searchCount R a : ℚ) / q.eval (enc a).length <
          |(E (a, List.ofFn r) : ℚ) - searchCount R a|} ≤ (2 ^ (enc a).length)⁻¹ := by
  obtain ⟨ℓ, E, hE, hacc⟩ := FNP.exists_approxCount_SAT hR q hq
  refine ⟨ℓ, E, hE.of_polyTimeReducible ?_, hacc⟩
  -- a satisfiable formula's word goes to the encoding of an instance with a solution
  obtain ⟨f, hf, hfR⟩ := hS encBits (encCNF '' SAT) image_SAT_mem_NP
  have henc : ComputableInPolyTime (fun a => enc a) enc encBits := .of_eq fun _ => rfl
  exact ⟨fun w => enc (f w), henc.comp hf, fun w => by
    rw [hfR w, enc.injective.mem_set_image]⟩

end Cslib.Complexity
