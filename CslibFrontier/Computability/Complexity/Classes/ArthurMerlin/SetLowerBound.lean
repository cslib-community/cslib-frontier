/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin
public import CslibFrontier.Computability.Complexity.Classes.SBP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Primitives
public import CslibFrontier.Probability.BitString.AffineHash
public import CslibFrontier.Probability.BitString.AffineHash.Word

import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.Amplification
import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.PerfectCompleteness
import CslibFrontier.Computability.Complexity.Classes.SharpP.Closure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Probabilistic.AffineHash
import CslibFrontier.Foundations.Data.BitString.BlockPower
import CslibFrontier.Foundations.Data.BitString.List.Operations
import CslibFrontier.Foundations.Data.BitString.WordCount

/-!
# The set lower bound protocol and `SBP ⊆ AM`

The set lower bound protocol of Goldwasser and Sipser [GoldwasserSipser1986]
[Arora and Barak, Section 8.2][AroraBarak09] lets Merlin convince Arthur that a set `S` with
membership certificates is large. Write `n` for the length of the encoded instance `a`, and let
`S a` be the strings `x` of `N(n)` bits with a certificate `z` of `c(n)` bits accepted by a
polynomial-time test, `R (a, x ++ z) = true` (`Cslib.Complexity.certifiedSet`). If a
polynomial-time threshold `K a > 0`, computed in binary, satisfies `K a ≤ #(S a)` on members and
`2 #(S a) ≤ K a` on non-members, then the problem is in `AM`
(`Cslib.Complexity.mem_AM_of_card_certifiedSet`).

The protocol:

* **Gap amplification.** Five copies of `S a` have at least `K a ^ 5` elements on members and at
  most `K a ^ 5 / 32` on non-members.
* **Normalisation.** With `ℓ = ⌊log₂ (K a ^ 5)⌋` and a polynomial `T(n) ≥ ℓ + 4`, appending
  `T(n)` bits whose first `ℓ` are `false` multiplies the size by `2 ^ (T(n) - ℓ)`
  (`Cslib.Complexity.SetLowerBound.card_amplifiedSet`): at least `2 ^ T(n)` elements on members
  and fewer than `2 ^ T(n) / 16` on non-members.
* **Hashing.** Arthur sends a random affine hash `h` to `m(n) = T(n) - 2` bits
  (`Cslib.BitString.LinearHash.affineHash`), and Merlin answers with an element `e` of the
  amplified set, the five certificates, and `h e = 0`. By pairwise independence, `0` is hit for at
  least three quarters of the hashes on members and for at most a quarter on non-members
  (`Cslib.Probability.IsPairwiseIndependentHash.four_mul_card_filter_notMem_image_le`,
  `Cslib.Probability.IsPairwiseIndependentHash.four_mul_card_filter_mem_image_le`).

With no certificates, `S a` is the set counted by a `#P` function, so `SBP ⊆ AM`
(`Cslib.Complexity.SBP_subset_AM`) [Böhler, Glaßer and Meister][BoehlerGlasserMeister2006].

## Main definitions

* `Cslib.Complexity.certifiedSet`: the strings with an accepted certificate.
* `Cslib.Complexity.SetLowerBound.amplifiedSet`: five copies followed by normalising padding.
* `Cslib.Complexity.SetLowerBound.verifier`: the Arthur–Merlin verifier of the protocol.

## Main results

* `Cslib.Complexity.SetLowerBound.card_amplifiedSet`: the size of the amplified set.
* `Cslib.Complexity.SetLowerBound.exists_verifier_iff`: Merlin has an accepted answer exactly when
  the amplified set meets the kernel of Arthur's hash.
* `Cslib.Complexity.exists_verifier_of_card_certifiedSet`: **the set lower bound protocol**, with
  completeness and soundness on every input separately.
* `Cslib.Complexity.mem_AM_of_card_certifiedSet`: the protocol for a language.
* `Cslib.Complexity.mem_AM_of_card_certifiedSet_of_length`: the protocol with element and
  certificate lengths computed from the instance in unary.
* `Cslib.Complexity.exists_perfectlyComplete_verifier_of_card_certifiedSet`: the protocol with
  perfect completeness and soundness error `1 / 3`, on every input separately
  ([Arora and Barak, Exercise 8 §3][AroraBarak07]).
* `Cslib.Complexity.SBP_subset_AM`.

## References

* [S. Goldwasser, M. Sipser, *Private coins versus public coins in interactive proof
  systems*][GoldwasserSipser1986]
* [E. Böhler, C. Glaßer, D. Meister, *Error-bounded probabilistic computations between
  MA and AM*][BoehlerGlasserMeister2006]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, draft of January 2007,
  Exercise 8 §3][AroraBarak07]
-/

@[expose] public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM Cslib.Probability

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- The strings of `N(n)` bits that have a certificate of `c(n)` bits accepted by `R`, where `n`
is the length of the encoded instance. -/
def certifiedSet (enc : α ↪ List Bool) (N c : Polynomial ℕ) (R : α × List Bool → Bool) (a : α) :
    Finset (BitString (N.eval (enc a).length)) :=
  univ.filter fun x => ∃ z : BitString (c.eval (enc a).length),
    R (a, List.ofFn x ++ List.ofFn z) = true

namespace SetLowerBound

/-! ### Amplification and normalisation -/

/-- Five elements of `S`, followed by `T` bits whose first `ℓ` bits are `false`. -/
def amplifiedSet {N : ℕ} (S : Finset (BitString N)) (T ℓ : ℕ) :
    Finset (BitString (5 * N + T)) :=
  univ.filter fun e =>
    (∀ i, BitString.block (BitString.ofList (5 * N) ((List.ofFn e).take (5 * N))) i ∈ S) ∧
      (!(((List.ofFn e).drop (5 * N)).take ℓ).any fun b => b) = true

/-- **The size of the amplified set**: `#S ^ 5 ⬝ 2 ^ (T - ℓ)`. -/
theorem card_amplifiedSet {N : ℕ} (S : Finset (BitString N)) {T ℓ : ℕ} (h : ℓ ≤ T) :
    #(amplifiedSet S T ℓ) = #S ^ 5 * 2 ^ (T - ℓ) := by
  rw [amplifiedSet, BitString.card_filter_ofFn_add (5 * N) T fun u w =>
    (∀ i, BitString.block (BitString.ofList (5 * N) u) i ∈ S) ∧
      (!(w.take ℓ).any fun b => b) = true]
  have hpad : #{w : BitString T | (!((List.ofFn w).take ℓ).any fun b => b) = true} =
      2 ^ (T - ℓ) := by
    rw [BitString.card_filter_take h fun w => (!w.any fun b => b) = true,
      BitString.card_filter_not_any, mul_one]
  have hblocks : #{u : BitString (5 * N) | ∀ i, BitString.block u i ∈ S} = #S ^ 5 := by
    rw [← BitString.card_blockPower]
    exact congrArg card (ext fun _ => by simp)
  simp only [BitString.ofList_ofFn]
  rw [← hblocks, card_filter, sum_mul]
  refine sum_congr rfl fun u _ => ?_
  by_cases hu : ∀ i, BitString.block u i ∈ S
  · simpa only [hu, implies_true, true_and, ↓reduceIte, one_mul] using hpad
  · simp [hu]

/-! ### The verifier -/

/-- The Arthur–Merlin verifier of the set lower bound protocol, with element length `N`,
certificate length `c`, hash length `m`, padding length `T` and padding threshold `ℓ`, where `n` is
the length of the encoded instance. The string is Arthur's hash seed of `m(n) M(n) + m(n)` bits,
with `M(n) = 5 N(n) + T(n)`, followed by Merlin's element of `M(n)` bits and five certificates of
`c(n)` bits. The verifier accepts when the five blocks of the element have accepted certificates,
the first `ℓ` padding bits are `false` and the element hashes to zero
(`Cslib.BitString.LinearHash.hashZero`). Bits missing from a short string read as `false`. -/
def verifier (enc : α ↪ List Bool) (N c m T : Polynomial ℕ) (ℓ : α → ℕ)
    (R : α × List Bool → Bool) (x : α × List Bool) : Bool :=
  let n := (enc x.1).length
  let M := 5 * N.eval n + T.eval n
  let P := m.eval n * M + m.eval n
  let e := (x.2.drop P).take M
  ((List.range 5).all fun i => R (x.1, BitString.listRow (N.eval n) i (e.take (5 * N.eval n)) ++
      BitString.listRow (c.eval n) i (x.2.drop (P + M)))) &&
    (!((e.drop (5 * N.eval n)).take (ℓ x.1)).any fun b => b) &&
    BitString.LinearHash.hashZero (m.eval n) M (x.2.take P) e

/-- The verifier of the set lower bound protocol is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_verifier {N c m T : Polynomial ℕ} {ℓ : α → ℕ}
    {R : α × List Bool → Bool} (hℓ : ComputableInPolyTime ℓ enc encUnary)
    (hR : ComputableInPolyTime R (encPair enc encBits) encBool) :
    ComputableInPolyTime (verifier enc N c m T ℓ R) (encPair enc encBits) encBool := by
  have ha := ComputableInPolyTime.fst enc encBits
  have hword := ComputableInPolyTime.snd enc encBits
  have hn := (ComputableInPolyTime.encoding_length enc).comp ha
  have hN := (ComputableInPolyTime.unary_eval N).comp hn
  have hc := (ComputableInPolyTime.unary_eval c).comp hn
  have hm := (ComputableInPolyTime.unary_eval m).comp hn
  have hT := (ComputableInPolyTime.unary_eval T).comp hn
  have hfiveN := ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 5) hN
  have hM := ComputableInPolyTime.unary_add' hfiveN hT
  have hP := ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_mul' hm hM) hm
  have he := ComputableInPolyTime.bitsTakeWithInput
    (ComputableInPolyTime.bitsDropWithInput hword hP) hM
  have hblocks := ComputableInPolyTime.bitsTakeWithInput he hfiveN
  have hcerts := ComputableInPolyTime.bitsDropWithInput hword
    (ComputableInPolyTime.unary_add' hP hM)
  have hrows := ComputableInPolyTime.allConst (List.range 5) fun i _ =>
    hR.comp (ha.prod (ComputableInPolyTime.bitsAppend
      (ComputableInPolyTime.bitsRowWithInput hN (ComputableInPolyTime.const i) hblocks)
      (ComputableInPolyTime.bitsRowWithInput hc (ComputableInPolyTime.const i) hcerts)))
  have hpadding := ComputableInPolyTime.bitsTakeWithInput
    (ComputableInPolyTime.bitsDropWithInput he hfiveN) (hℓ.comp ha)
  have hzero := ComputableInPolyTime.bool_not.comp
    (ComputableInPolyTime.bitsAnyWithInput (test := fun _ b => b) hpadding
      (ComputableInPolyTime.snd _ encBool))
  have hhash := BitString.LinearHash.computableInPolyTime_hashZero hm hM
    (ComputableInPolyTime.bitsTakeWithInput hword hP) he
  change ComputableInPolyTime (fun x => verifier enc N c m T ℓ R x) _ _
  simpa only [verifier, Function.comp_def] using
    ComputableInPolyTime.bool_and' (ComputableInPolyTime.bool_and' hrows hzero) hhash

/-- On a seed, an element and five certificates, the verifier accepts exactly when the blocks of
the element have accepted certificates, the padding starts with `ℓ` bits `false` and the affine
hash given by the seed sends the element to zero. -/
private theorem verifier_ofFn_append {N c m T : Polynomial ℕ} {ℓ : α → ℕ} {R : α × List Bool → Bool}
    (a : α) (r : BitString (m.eval (enc a).length * (5 * N.eval (enc a).length +
      T.eval (enc a).length) + m.eval (enc a).length))
    (e : BitString (5 * N.eval (enc a).length + T.eval (enc a).length))
    (z : BitString (5 * c.eval (enc a).length)) :
    verifier enc N c m T ℓ R (a, List.ofFn r ++ (List.ofFn e ++ List.ofFn z)) = true ↔
      (∀ i : Fin 5, R (a, List.ofFn (BitString.block (BitString.ofList (5 * N.eval (enc a).length)
        ((List.ofFn e).take (5 * N.eval (enc a).length))) i) ++
          List.ofFn (BitString.block z i)) = true) ∧
      (!(((List.ofFn e).drop (5 * N.eval (enc a).length)).take (ℓ a)).any fun b => b) = true ∧
      BitString.LinearHash.affineHash (BitString.LinearHash.affineSeedEquiv _ _ r) e = 0 := by
  simp only [verifier, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  generalize (enc a).length = n at r e z ⊢
  have hdrop' : (List.ofFn r ++ (List.ofFn e ++ List.ofFn z)).drop
      (m.eval n * (5 * N.eval n + T.eval n) + m.eval n + (5 * N.eval n + T.eval n)) =
        List.ofFn z := by
    rw [← List.append_assoc]
    exact List.drop_left' (by simp)
  rw [List.drop_left' List.length_ofFn, hdrop', List.take_left' List.length_ofFn,
    List.take_left' List.length_ofFn, BitString.LinearHash.hashZero_ofFn, and_assoc]
  refine and_congr ⟨fun h i => ?_, fun h i hi => ?_⟩ Iff.rfl
  · simpa only [BitString.listRow_eq_ofFn (count := 5) _ i, BitString.ofList_ofFn] using h i i.isLt
  · simpa only [BitString.listRow_eq_ofFn (count := 5) _ ⟨i, hi⟩, BitString.ofList_ofFn] using
      h ⟨i, hi⟩

/-- **Merlin's answers**: some answer is accepted exactly when the amplified set meets the kernel of
the affine hash given by Arthur's seed. -/
theorem exists_verifier_iff {N c m T : Polynomial ℕ} {ℓ : α → ℕ} {R : α × List Bool → Bool}
    (a : α) (r : BitString (m.eval (enc a).length * (5 * N.eval (enc a).length +
      T.eval (enc a).length) + m.eval (enc a).length)) :
    (∃ y : BitString (5 * N.eval (enc a).length + T.eval (enc a).length +
        5 * c.eval (enc a).length),
      verifier enc N c m T ℓ R (a, List.ofFn r ++ List.ofFn y) = true) ↔
      0 ∈ (amplifiedSet (certifiedSet enc N c R a) (T.eval (enc a).length) (ℓ a)).image
        (BitString.LinearHash.affineHash (BitString.LinearHash.affineSeedEquiv _ _ r)) := by
  rw [mem_image]
  refine ⟨?_, ?_⟩
  · rintro ⟨y, hy⟩
    rw [List.ofFn_add (f := y), verifier_ofFn_append] at hy
    exact ⟨_, mem_filter.2 ⟨mem_univ _, fun i => mem_filter.2 ⟨mem_univ _, _, hy.1 i⟩, hy.2.1⟩,
      hy.2.2⟩
  · rintro ⟨e, he, hzero⟩
    obtain ⟨-, hblocks, hpad⟩ := mem_filter.1 he
    choose z hz using fun i : Fin 5 => (mem_filter.1 (hblocks i)).2
    refine ⟨Fin.append e (BitString.blocksEquiv.symm z), ?_⟩
    rw [List.ofFn_fin_append, verifier_ofFn_append]
    exact ⟨fun i => by simpa only [BitString.block_blocksEquiv_symm] using hz i, hpad, hzero⟩

/-- All certificates are rejected by `verifier` on `r` if and only if `0` is not in the image of
`amplifiedSet` under the affine hash seeded by `r`. -/
private theorem forall_verifier_eq_false_iff (N c m T : Polynomial ℕ) (ℓ : α → ℕ)
    (R : α × List Bool → Bool) (a : α)
    (r : BitString (m.eval (enc a).length * (5 * N.eval (enc a).length +
      T.eval (enc a).length) + m.eval (enc a).length)) :
    (∀ y : BitString (5 * N.eval (enc a).length + T.eval (enc a).length +
      5 * c.eval (enc a).length), verifier enc N c m T ℓ R (a, List.ofFn r ++ List.ofFn y) =
        false) ↔
      0 ∉ (amplifiedSet (certifiedSet enc N c R a) (T.eval (enc a).length) (ℓ a)).image
        (BitString.LinearHash.affineHash (BitString.LinearHash.affineSeedEquiv _ _ r)) := by
  rw [← exists_verifier_iff]
  simp

/-- Lower and upper bounds on `#(amplifiedSet S T (Nat.log 2 (K ^ 5)))` for a positive threshold `K`
when `T = m + 2` and `Nat.log 2 (K ^ 5) ≤ T`. -/
private theorem card_amplifiedSet_bounds {N m T K : ℕ} (S : Finset (BitString N)) (hKpos : 0 < K)
    (hTm : T = m + 2) (hℓT : Nat.log 2 (K ^ 5) ≤ T) :
    (K ≤ #S → 4 * Fintype.card (BitString m) ≤ #(amplifiedSet S T (Nat.log 2 (K ^ 5)))) ∧
      (2 * #S ≤ K → 4 * #(amplifiedSet S T (Nat.log 2 (K ^ 5))) ≤ Fintype.card (BitString m)) := by
  set ℓ := Nat.log 2 (K ^ 5)
  have hKℓ : 2 ^ ℓ ≤ K ^ 5 := Nat.pow_log_le_self 2 (pow_ne_zero 5 hKpos.ne')
  have hKℓ' : K ^ 5 < 2 ^ (ℓ + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hsplit : 2 ^ T = 2 ^ ℓ * 2 ^ (T - ℓ) := by rw [← pow_add, Nat.add_sub_cancel' hℓT]
  have h4 : 2 ^ T = 4 * 2 ^ m := by rw [hTm, pow_add]; ring
  rw [BitString.card, card_amplifiedSet S hℓT]
  refine ⟨fun hmem => ?_, fun hnot => ?_⟩
  · rw [← h4, hsplit]
    exact Nat.mul_le_mul_right _ (hKℓ.trans (Nat.pow_le_pow_left hmem 5))
  · have h32 : 32 * #S ^ 5 ≤ K ^ 5 := by simpa [mul_pow] using Nat.pow_le_pow_left hnot 5
    have h16 : 16 * #S ^ 5 < 2 ^ ℓ := by grind
    have := Nat.mul_le_mul_right (2 ^ (T - ℓ)) h16.le
    rw [← hsplit, h4] at this
    nlinarith

end SetLowerBound

open SetLowerBound

/-- **The set lower bound protocol** of Goldwasser and Sipser [GoldwasserSipser1986]
[Arora and Barak, Section 8.2][AroraBarak09], for every input separately. Let `R` be a
polynomial-time test, `N` and `c` polynomials, and `K` a polynomial-time threshold in binary with
`K a > 0`. One polynomial-time Arthur–Merlin verifier has, on every input `a`, an accepted reply
for at least two thirds of the random strings when the set of strings of `N(n)` bits with a
certificate of `c(n)` bits accepted by `R` has at least `K a` elements, and for at most a third
when it has at most `K a / 2`. Inputs between the two bounds carry no obligation. -/
theorem exists_verifier_of_card_certifiedSet {N c : Polynomial ℕ} {R : α × List Bool → Bool}
    {K : α → ℕ} (hR : ComputableInPolyTime R (encPair enc encBits) encBool)
    (hK : ComputableInPolyTime K enc encNat) (hKpos : ∀ a, 0 < K a) :
    ∃ (p q : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableInPolyTime V (encPair enc encBits) encBool ∧
      ∀ a, (K a ≤ #(certifiedSet enc N c R a) → 2 * 2 ^ p.eval (enc a).length ≤
          3 * #{r : Fin (p.eval (enc a).length) → Bool |
            ∃ y : Fin (q.eval (enc a).length) → Bool, V (a, List.ofFn r ++ List.ofFn y) = true}) ∧
        (2 * #(certifiedSet enc N c R a) ≤ K a → 2 * 2 ^ p.eval (enc a).length ≤
          3 * #{r : Fin (p.eval (enc a).length) → Bool |
            ∀ y : Fin (q.eval (enc a).length) → Bool,
              V (a, List.ofFn r ++ List.ofFn y) = false}) := by
  -- normalise the threshold `K a ^ 5` to a power of two
  set ℓ : α → ℕ := fun a => Nat.log 2 (K a ^ 5)
  have hℓ : ComputableInPolyTime ℓ enc encUnary :=
    ComputableInPolyTime.binary_log_two.comp (hK.binary_pow' (.const 5))
  obtain ⟨B, hB⟩ := hℓ.polyBounded.exists_polynomial
  set m : Polynomial ℕ := B + 2 with hm
  set T : Polynomial ℕ := B + 4 with hT
  refine ⟨m * (5 * N + T) + m, 5 * N + T + 5 * c, verifier enc N c m T ℓ R,
    computableInPolyTime_verifier hℓ hR, fun a => ?_⟩
  rw [show (m * (5 * N + T) + m).eval (enc a).length = m.eval (enc a).length *
      (5 * N.eval (enc a).length + T.eval (enc a).length) + m.eval (enc a).length by simp,
    show (5 * N + T + 5 * c).eval (enc a).length = 5 * N.eval (enc a).length +
      T.eval (enc a).length + 5 * c.eval (enc a).length by simp]
  simp only [forall_verifier_eq_false_iff, exists_verifier_iff]
  set n := (enc a).length
  have hh := (BitString.LinearHash.isPairwiseIndependentHash_affineHash
    (m.eval n) (5 * N.eval n + T.eval n)).comp_seedEquiv (BitString.LinearHash.affineSeedEquiv _ _)
  have hbnds := card_amplifiedSet_bounds (certifiedSet enc N c R a) (hKpos a)
    (show T.eval n = m.eval n + 2 by simp [hT, hm])
    (by simp only [hT, Polynomial.eval_add, Polynomial.eval_ofNat]; linarith [hB a])
  exact ⟨-- members: the amplified set has at least `4 ⬝ 2 ^ m(n)` elements
    fun ha => BitString.two_mul_two_pow_le_of_four_mul_card_filter_not_le _
      (by simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using
        hh.four_mul_card_filter_notMem_image_le (hbnds.1 ha) 0),
    -- non-members: the amplified set has at most `2 ^ m(n) / 4` elements
    fun ha => BitString.two_mul_two_pow_le_of_four_mul_card_filter_not_le _
      (by simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, not_not] using
        hh.four_mul_card_filter_mem_image_le (hbnds.2 ha) 0)⟩

/-- **The set lower bound protocol** of Goldwasser and Sipser [GoldwasserSipser1986]
[Arora and Barak, Section 8.2][AroraBarak09]. Let `R` be a polynomial-time test, `N` and `c`
polynomials, and `K` a polynomial-time threshold in binary with `K a > 0`. If the set of strings
of `N(n)` bits with a certificate of `c(n)` bits accepted by `R` has at least `K a` elements for
every member `a` of `A`, and at most `K a / 2` for every non-member, then `A ∈ AM`. -/
theorem mem_AM_of_card_certifiedSet {N c : Polynomial ℕ} {R : α × List Bool → Bool} {K : α → ℕ}
    (hR : ComputableInPolyTime R (encPair enc encBits) encBool)
    (hK : ComputableInPolyTime K enc encNat) (hKpos : ∀ a, 0 < K a)
    (hmem : ∀ a ∈ A, K a ≤ #(certifiedSet enc N c R a))
    (hnot : ∀ a ∉ A, 2 * #(certifiedSet enc N c R a) ≤ K a) : A ∈ AM enc :=
  let ⟨p, q, V, hV, h⟩ := exists_verifier_of_card_certifiedSet (N := N) (c := c) hR hK hKpos
  ⟨p, q, V, hV, fun a => ⟨fun ha => (h a).1 (hmem a ha), fun ha => (h a).2 (hnot a ha)⟩⟩

/-- The set lower bound protocol also allows the element and certificate lengths to be computed
from the instance in unary. Padding every counted element with zeros preserves its multiplicity. -/
theorem mem_AM_of_card_certifiedSet_of_length {N c K : α → ℕ} {R : α × List Bool → Bool}
    (hN : ComputableInPolyTime N enc encUnary) (hc : ComputableInPolyTime c enc encUnary)
    (hR : ComputableInPolyTime R (encPair enc encBits) encBool)
    (hK : ComputableInPolyTime K enc encNat) (hKpos : ∀ a, 0 < K a)
    (hmem : ∀ a ∈ A, K a ≤ #{x : BitString (N a) | ∃ z : BitString (c a),
      R (a, List.ofFn x ++ List.ofFn z) = true})
    (hnot : ∀ a ∉ A, 2 * #{x : BitString (N a) | ∃ z : BitString (c a),
      R (a, List.ofFn x ++ List.ofFn z) = true} ≤ K a) : A ∈ AM enc := by
  obtain ⟨s, hs⟩ := hN.polyBounded.exists_polynomial
  obtain ⟨t, ht⟩ := hc.polyBounded.exists_polynomial
  let V := fun (p : α × List Bool) =>
    let split := s.eval (enc p.1).length
    R (p.1, (p.2.take split).take (N p.1) ++ (p.2.drop split).take (c p.1)) &&
      !(((p.2.take split).drop (N p.1)).any fun b => b)
  have hV : ComputableInPolyTime V (encPair enc encBits) encBool := by
    have ha := ComputableInPolyTime.fst enc encBits
    have hw := ComputableInPolyTime.snd enc encBits
    have hn := hN.comp ha
    have hsplit := (ComputableInPolyTime.unary_eval s).comp
      ((ComputableInPolyTime.encoding_length enc).comp ha)
    have hground := ComputableInPolyTime.bitsTakeWithInput hw hsplit
    exact ComputableInPolyTime.bool_and' (hR.comp (ha.prod (ComputableInPolyTime.bitsAppend
      (ComputableInPolyTime.bitsTakeWithInput hground hn)
      (ComputableInPolyTime.bitsTakeWithInput (ComputableInPolyTime.bitsDropWithInput hw hsplit)
        (hc.comp ha))))) (ComputableInPolyTime.bool_not.comp
      (ComputableInPolyTime.bitsAnyWithInput (test := fun _ b => b)
        (ComputableInPolyTime.bitsDropWithInput hground hn) (ComputableInPolyTime.snd _ encBool)))
  have hcard (a : α) : #(certifiedSet enc s t V a) =
      #{x : BitString (N a) | ∃ z : BitString (c a), R (a, List.ofFn x ++ List.ofFn z) = true} := by
    unfold certifiedSet
    simp only [V, List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn,
      Bool.and_eq_true, exists_and_right]
    let good := fun w => ∃ z : BitString (c a), R (a, w ++ List.ofFn z) = true
    have htrunc (w : List Bool) := BitString.exists_take_ofFn_iff (ht a)
      (g := fun z => R (a, w ++ z) = true)
    simp_rw [htrunc]
    rw [BitString.card_filter_take_drop (hs a) good (fun w => (!w.any fun b => b) = true),
      BitString.card_filter_not_any, mul_one]
  exact mem_AM_of_card_certifiedSet hV hK hKpos (fun a ha => by rw [hcard]; exact hmem a ha)
    (fun a ha => by rw [hcard]; exact hnot a ha)

/-- **`SBP ⊆ AM`** [Böhler, Glaßer and Meister][BoehlerGlasserMeister2006]: the set counted by the
`#P` function of an `SBP` problem needs no certificates, and the set lower bound protocol applies
to it with the `SBP` threshold. -/
theorem SBP_subset_AM : SBP enc ⊆ AM enc := fun A hA => by
  obtain ⟨f, ⟨s, W, hW, hf⟩, k, hk, hkpos, hA⟩ := mem_SBP_iff_exists_pos_threshold.mp hA
  have hcount (a : α) : #(certifiedSet enc s 0
      (fun x => W (x.1, x.2.take (s.eval (enc x.1).length))) a) = f a := by
    rw [hf a, acceptCount]
    exact congrArg card (filter_congr fun x _ => by
      simp only [List.take_left' List.length_ofFn]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨fun _ => false, h⟩⟩)
  exact mem_AM_of_card_certifiedSet (N := s) (c := 0)
    (R := fun x => W (x.1, x.2.take (s.eval (enc x.1).length)))
    (hW.comp ((ComputableInPolyTime.fst enc encBits).prod
      (ComputableInPolyTime.bitsTakeWithInput (.snd enc encBits)
        (((ComputableInPolyTime.unary_eval s).comp
          (ComputableInPolyTime.encoding_length enc)).comp (.fst enc encBits)))))
    hk hkpos (fun a ha => hcount a ▸ (hA a).1 ha) fun a ha => hcount a ▸ ((hA a).2 ha).le


/-- **A perfectly complete set lower bound protocol** ([Arora and Barak, Exercise 8 §3, draft of
January 2007, p. 8.20][AroraBarak07]). Let `R` be a polynomial-time test, `N` and `c` polynomials,
and `K` a polynomial-time threshold in binary with `K a > 0`, and write `S a` for the strings of
`N(n)` bits with a certificate of `c(n)` bits accepted by `R`. One polynomial-time Arthur–Merlin
verifier, with Arthur's random string of `p(n)` bits followed by Merlin's reply of `q(n)` bits,
has on every input `a`:

* an accepted reply to **every** random string when `K a ≤ #(S a)`;
* no accepted reply for at least two thirds of the random strings when `2 #(S a) ≤ K a`.

Inputs with `K a / 2 < #(S a) < K a` carry no obligation.

The proof does not follow the exercise's hint (Merlin chooses several hash functions, and the gap
is amplified by Cartesian powers of the set). It makes the bounded-error protocol
(`exists_verifier_of_card_certifiedSet`) perfectly complete with soundness error `1 / 2` by
amplification and Lautemann's shifts, as in `AM_subset_AMOne` (after Fürer, Goldreich, Mansour,
Sipser and Zachos), and runs two copies in parallel, accepting when both accept, which brings the
soundness error to `1 / 4` (`IsArthurMerlinOneVerifier.arthurMerlinRepeat_one_perfect`). Those
steps are stated for a language; they are applied to the inputs outside the middle band, a
subtype on which the two cases partition the inputs, and the constructed verifier on an input of
the subtype is the verifier on the underlying input. -/
theorem exists_perfectlyComplete_verifier_of_card_certifiedSet {N c : Polynomial ℕ}
    {R : α × List Bool → Bool} {K : α → ℕ}
    (hR : ComputableInPolyTime R (encPair enc encBits) encBool)
    (hK : ComputableInPolyTime K enc encNat) (hKpos : ∀ a, 0 < K a) :
    ∃ (p q : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableInPolyTime V (encPair enc encBits) encBool ∧
      ∀ a, (K a ≤ #(certifiedSet enc N c R a) → ∀ r : Fin (p.eval (enc a).length) → Bool,
          ∃ y : Fin (q.eval (enc a).length) → Bool, V (a, List.ofFn r ++ List.ofFn y) = true) ∧
        (2 * #(certifiedSet enc N c R a) ≤ K a → 2 * 2 ^ p.eval (enc a).length ≤
          3 * #{r : Fin (p.eval (enc a).length) → Bool |
            ∀ y : Fin (q.eval (enc a).length) → Bool,
              V (a, List.ofFn r ++ List.ofFn y) = false}) := by
  obtain ⟨p, q, V, hV, h⟩ := exists_verifier_of_card_certifiedSet (N := N) (c := c) hR hK hKpos
  -- the inputs outside the middle band, where membership is `K a ≤ #(S a)`
  let β := {a : α // K a ≤ #(certifiedSet enc N c R a) ∨ 2 * #(certifiedSet enc N c R a) ≤ K a}
  let encβ : β ↪ List Bool := (Function.Embedding.subtype _).trans enc
  have hβ : IsArthurMerlinVerifier encβ p q (fun x => V (x.1.val, x.2))
      {b : β | K b.val ≤ #(certifiedSet enc N c R b.val)} := fun b =>
    ⟨(h b.val).1, fun hb => (h b.val).2 (b.property.resolve_left hb)⟩
  have hOne := ArthurMerlin.isArthurMerlinOneVerifier_piTwoVerifier (hβ.repeatMajority _)
    (ArthurMerlin.eval_lt_mul p) fun _ => Nat.lt_two_pow_self
  refine ⟨2 * 1 * ((12 * p + 1) * (12 * (12 * p + 1) * p)),
    2 * 1 * (12 * (12 * p + 1) * p + (12 * p + 1) * (12 * (12 * p + 1) * q)),
    arthurMerlinRepeat enc 1 ((12 * p + 1) * (12 * (12 * p + 1) * p))
      (12 * (12 * p + 1) * p + (12 * p + 1) * (12 * (12 * p + 1) * q))
      (ArthurMerlin.piTwoVerifier enc (12 * p + 1) (12 * (12 * p + 1) * p) (12 * (12 * p + 1) * q)
        (arthurMerlinRepeat enc (6 * (12 * p + 1)) p q V)),
    computableInPolyTime_arthurMerlinRepeat (ArthurMerlin.computableInPolyTime_piTwoVerifier
      (computableInPolyTime_arthurMerlinRepeat hV _ _ _) _ _ _) _ _ _,
    fun a => ⟨fun ha => (hOne.arthurMerlinRepeat_one_perfect ⟨a, .inl ha⟩).1 ha,
      fun ha => (hOne.arthurMerlinRepeat_one_perfect ⟨a, .inr ha⟩).2 fun hK' => by
        have := hKpos a
        simp only [Set.mem_ofPred_eq] at hK'
        omega⟩⟩

end Cslib.Complexity
