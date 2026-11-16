/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiffieHellman.MultiDDH
public import CslibFrontier.Crypto.Game.Hybrid
public import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.Product
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.EncLen

/-!
# The Naor–Reingold pseudorandom function from Decisional Diffie–Hellman

Over a `PrimeOrderGroupFamily` `F`, the Naor–Reingold pseudorandom function
([BonehShoup2023], Section 10.11, Exercise 10.4, p. 424; [NaorReingold2004], Section 4.1,
Construction 4.1 & Theorem 4.1) with key `(α₀, α₁, …, αₙ) ∈ (ZMod q)ⁿ⁺¹` maps an `n`-bit input
`x ∈ {0, 1}ⁿ` to the group element
$$F_{\mathrm{NR}}((\alpha_0, \alpha_1, \dots, \alpha_n), (x_1, \dots, x_n))
  := \left(\alpha_0 \cdot \prod_{i=1}^n \alpha_i^{x_i}\right) \bullet g.$$

Following Boneh–Shoup Exercises 10.4, 10.8, 10.11, and 4.18, we formalize:

1. **Algebraic and augmented-tree characterization (`naorReingoldEval`, `naorReingoldTreeEval`)**:
   - The closed-form exponent product `naorReingoldExp` and group evaluation `naorReingoldEval`.
   - The single-step generator `naorReingoldPRG`
     ($G_{\mathrm{NR}}(\alpha, u) = (u, \alpha \bullet u)$)
     and augmented-tree fold `naorReingoldTreeEval`, together with
     `naorReingoldTreeEval_eq_naorReingoldEval` ([BonehShoup2023], Exercise 10.4(a), p. 424, and
     Exercise 4.18, p. 172).
   - The word-level evaluator `naorReingoldWordEval`, its correctness theorem
     `naorReingoldWordEval_eq_encode`, and its plain polynomial-time certificate
     `computableInPolyTime_naorReingoldWordEval`.
2. **Fixed-$u$ DDH random self-reduction and Multi-DDH (I) (`ddhFixedURerandomize`,
   `multiDDHRerandomizeLaw`)**:
   - Fixed-$u$ rerandomization $(u, v, w) \mapsto (u, \sigma \bullet g + \tau \bullet v,
     \sigma \bullet u + \tau \bullet w)$ ([BonehShoup2023], Exercise 10.8, p. 425), its word-level
     counterpart `ddhFixedUWordRerandomize`, and the exact distributional laws
     `ddhFixedURerandomizeLaw_real` (Exercise 10.8(a)) and `ddhFixedURerandomizeLaw_random`
     (Exercise 10.8(b)).
   - The $n = 1$ (single shared secret $\alpha$, $|\iota|$ pairs) Multi-DDH (I) reduction
     `multiDDHRerandomizeLaw` ([BonehShoup2023], Exercise 10.11, p. 426), whose wrapper samples
     $|\iota|$ rerandomized pairs, proving `multiDDHRerandomizeLaw_real`,
     `multiDDHRerandomizeLaw_random`, and the quantitative bound `advantage_multiDDH_le`
     ($\le \mathrm{DDHadv}[B] + 1 / q$).
3. **Naor–Reingold prefix-hybrid evaluation (`naorReingoldHybridEval`, `naorReingoldTableEval`)**:
   - The depth-$k$ hybrid function `naorReingoldHybridEval`, which looks up the $k$-bit prefix in a
     table and multiplies by the suffix exponent product `naorReingoldSuffixExp`, and the level-$k$
     child-table evaluation `naorReingoldTableEval`, with the suffix identities
     `naorReingoldSuffixExp_eq_mul_succ` and `naorReingoldSuffixExp_succ_update`.
   - `NaorReingold.Security` builds the security proof's hybrids from them. It has the adaptive
     word-level PRF games, the lazy-sampling `IsOraclePPT` DDH reduction
     `naorReingoldToDDHDistinguisher` and asymptotic security under `F.DDH`
     (`DDH.negligible_naorReingoldWordGame`); `NaorReingold.PRF` has the `PseudorandomFunction`
     bridge.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldExp`,
  `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldEval`:
  the Naor–Reingold exponent product and PRF evaluation.
* `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldPRG`,
  `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldStep`,
  `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldTreeEval`:
  the single-step generator $G_{\mathrm{NR}}$ and augmented-tree evaluation.
* `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldWordEval`:
  polynomial-time evaluation on encoded group elements.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhFixedURerandomize`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhFixedURerandomizeLaw`:
  fixed-$u$ DDH rerandomization (Boneh–Shoup Exercise 10.8).
* `Cslib.Crypto.PrimeOrderGroupFamily.multiDDHRealTupleLaw`,
  `Cslib.Crypto.PrimeOrderGroupFamily.multiDDHRandomTupleLaw`,
  `Cslib.Crypto.PrimeOrderGroupFamily.multiDDHRerandomizeLaw`:
  $n = 1$ Multi-DDH (I) distributions and rerandomization (Boneh–Shoup Exercise 10.11).
* `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldHybridEval`,
  `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldTableEval`:
  depth-$k$ prefix-hybrid function and level-$k$ child-table evaluation.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldTreeEval_eq_naorReingoldEval`:
  augmented-tree characterization of the Naor–Reingold PRF (Boneh–Shoup Exercise 10.4(a)).
* `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_naorReingoldWordEval`:
  plain polynomial-time certificate for word-level Naor–Reingold evaluation.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhFixedURerandomizeLaw_real`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhFixedURerandomizeLaw_random`:
  fixed-$u$ DDH random self-reduction (Boneh–Shoup Exercise 10.8).
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_multiDDH_le`:
  $n = 1$ Multi-DDH (I) reduction to DDH, sampling $|\iota|$ rerandomized pairs
  (Boneh–Shoup Exercise 10.11).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 4.10 (Exercise 4.18, p. 172) and Section 10.11
  (Exercises 10.4, 10.8, 10.11, pp. 424–426).
* [M. Naor, O. Reingold, *Number-Theoretic Constructions of Efficient Pseudo-Random
  Functions*][NaorReingold2004], Section 4.1 (Construction 4.1 & Theorem 4.1).
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM
open scoped ENNReal NNReal

variable (F : PrimeOrderGroupFamily)

/-! ### Naor–Reingold PRF and augmented-tree characterization (Exercise 10.4(a) & Exercise 4.18) -/

/-- The Naor–Reingold exponent product `α₀ * ∏ i : Fin n, if x i then α i else 1` in
`ZMod (F.order d)` ([BonehShoup2023], Section 10.11, Exercise 10.4, p. 424;
[NaorReingold2004], Section 4.1, Construction 4.1). -/
def naorReingoldExp (d : F.Desc) {n : ℕ}
    (α₀ : ZMod (F.order d)) (α : Fin n → ZMod (F.order d)) (x : BitString n) :
    ZMod (F.order d) :=
  α₀ * ∏ i : Fin n, if x i then α i else 1

/-- The Naor–Reingold pseudorandom function
`F_NR((α₀, α₁, …, αₙ), (x₁, …, xₙ)) = (α₀ * ∏ i, αᵢ^{xᵢ}) • g`
([BonehShoup2023], Section 10.11, Exercise 10.4, p. 424;
[NaorReingold2004], Section 4.1, Construction 4.1). -/
def naorReingoldEval (d : F.Desc) {n : ℕ}
    (α₀ : ZMod (F.order d)) (α : Fin n → ZMod (F.order d)) (x : BitString n) :
    F.Carrier d :=
  F.naorReingoldExp d α₀ α x • F.generator d

@[simp]
theorem naorReingoldExp_zero (d : F.Desc)
    (α₀ : ZMod (F.order d)) (α : Fin 0 → ZMod (F.order d)) (x : BitString 0) :
    F.naorReingoldExp d α₀ α x = α₀ := by
  simp [naorReingoldExp]

@[simp]
theorem naorReingoldEval_zero (d : F.Desc)
    (α₀ : ZMod (F.order d)) (α : Fin 0 → ZMod (F.order d)) (x : BitString 0) :
    F.naorReingoldEval d α₀ α x = α₀ • F.generator d := by
  simp [naorReingoldEval]

@[simp]
theorem naorReingoldExp_false (d : F.Desc) {n : ℕ}
    (α₀ : ZMod (F.order d)) (α : Fin n → ZMod (F.order d)) :
    F.naorReingoldExp d α₀ α (fun _ => false) = α₀ := by
  simp [naorReingoldExp]

@[simp]
theorem naorReingoldEval_false (d : F.Desc) {n : ℕ}
    (α₀ : ZMod (F.order d)) (α : Fin n → ZMod (F.order d)) :
    F.naorReingoldEval d α₀ α (fun _ => false) = α₀ • F.generator d := by
  simp [naorReingoldEval]

@[simp]
theorem naorReingoldExp_true (d : F.Desc) {n : ℕ}
    (α₀ : ZMod (F.order d)) (α : Fin n → ZMod (F.order d)) :
    F.naorReingoldExp d α₀ α (fun _ => true) = α₀ * ∏ i : Fin n, α i := by
  simp [naorReingoldExp]

@[simp]
theorem naorReingoldEval_true (d : F.Desc) {n : ℕ}
    (α₀ : ZMod (F.order d)) (α : Fin n → ZMod (F.order d)) :
    F.naorReingoldEval d α₀ α (fun _ => true) = (α₀ * ∏ i : Fin n, α i) • F.generator d := by
  simp [naorReingoldEval]

/-- The Naor–Reingold single-step generator `G_NR(α, u) := (u, α • u)` ([BonehShoup2023],
Section 10.11, Exercise 10.4(a), p. 424). -/
def naorReingoldPRG (d : F.Desc) (α : ZMod (F.order d)) (u : F.Carrier d) :
    F.Carrier d × F.Carrier d :=
  (u, α • u)

/-- One step of the augmented tree construction ([BonehShoup2023], Section 4.10, Exercise 4.18,
p. 172, and Section 10.11, Exercise 10.4(a), p. 424): select the `false` (`u`) or `true` (`α • u`)
child of `naorReingoldPRG d α u`. -/
def naorReingoldStep (d : F.Desc) (u : F.Carrier d) (p : ZMod (F.order d) × Bool) :
    F.Carrier d :=
  if p.2 then p.1 • u else u

@[simp]
theorem naorReingoldStep_eq_prg (d : F.Desc) (u : F.Carrier d) (α : ZMod (F.order d)) (b : Bool) :
    F.naorReingoldStep d u (α, b) =
      if b then (F.naorReingoldPRG d α u).2 else (F.naorReingoldPRG d α u).1 :=
  rfl

/-- Augmented-tree evaluation of `naorReingoldStep` along a list of `(key, bit)` pairs starting
from an initial group element `u`. -/
def naorReingoldTreeFold (d : F.Desc) (u : F.Carrier d)
    (steps : List (ZMod (F.order d) × Bool)) : F.Carrier d :=
  steps.foldl (F.naorReingoldStep d) u

/-- Augmented-tree evaluation of the Naor–Reingold PRF from root `α₀ • g` along `(α i, x i)` for
`i : Fin n` ([BonehShoup2023], Exercise 10.4(a), p. 424, and Exercise 4.18, p. 172). -/
def naorReingoldTreeEval (d : F.Desc) {n : ℕ}
    (α₀ : ZMod (F.order d)) (α : Fin n → ZMod (F.order d)) (x : BitString n) :
    F.Carrier d :=
  F.naorReingoldTreeFold d (α₀ • F.generator d) (List.ofFn fun i : Fin n => (α i, x i))

/-- Folding `naorReingoldStep` starting from `β • u` multiplies the scalar `β` by the product of
selected step exponents. -/
theorem naorReingoldTreeFold_smul (d : F.Desc) (β : ZMod (F.order d)) (u : F.Carrier d)
    (steps : List (ZMod (F.order d) × Bool)) :
    F.naorReingoldTreeFold d (β • u) steps =
      (β * (steps.map fun p => if p.2 then p.1 else 1).prod) • u := by
  induction steps generalizing β with
  | nil => simp [naorReingoldTreeFold]
  | cons p rest ih =>
    have hstep : F.naorReingoldStep d (β • u) p = (β * if p.2 then p.1 else 1) • u := by
      rcases p with ⟨a, _ | _⟩ <;> simp [naorReingoldStep, smul_smul, mul_comm]
    rw [naorReingoldTreeFold, List.foldl_cons, ← naorReingoldTreeFold, hstep,
      ih (β * if p.2 then p.1 else 1), List.map_cons, List.prod_cons, mul_assoc]

/-- **Boneh–Shoup Exercise 10.4(a)**: the augmented-tree construction `naorReingoldTreeEval` built
from `naorReingoldPRG` ($G_{\mathrm{NR}}(\alpha, u) = (u, \alpha \bullet u)$) coincides with
`naorReingoldEval`. -/
theorem naorReingoldTreeEval_eq_naorReingoldEval (d : F.Desc) {n : ℕ}
    (α₀ : ZMod (F.order d)) (α : Fin n → ZMod (F.order d)) (x : BitString n) :
    F.naorReingoldTreeEval d α₀ α x = F.naorReingoldEval d α₀ α x := by
  rw [naorReingoldTreeEval, naorReingoldTreeFold_smul, naorReingoldEval, naorReingoldExp]
  congr 2
  rw [List.map_ofFn, Fin.prod_univ_def, List.prod_ofFn]
  rfl

/-! ### Word-level polynomial-time evaluation -/

/-- Multiply the selected natural-number exponents in `steps` starting from `acc`. -/
def naorReingoldProdNat (acc : ℕ) (steps : List (ℕ × Bool)) : ℕ :=
  steps.foldl (fun e p => if p.2 then e * p.1 else e) acc

/-- Casting `naorReingoldProdNat` to `ZMod q` equals `acc` times the product of selected step
exponents in `ZMod q`. -/
theorem naorReingoldProdNat_cast (q acc : ℕ) (steps : List (ℕ × Bool)) :
    (naorReingoldProdNat acc steps : ZMod q) =
      (acc : ZMod q) * (steps.map fun p => if p.2 then (p.1 : ZMod q) else 1).prod := by
  induction steps generalizing acc with
  | nil => simp [naorReingoldProdNat]
  | cons p rest ih =>
    rw [naorReingoldProdNat, List.foldl_cons, ← naorReingoldProdNat,
      ih (if p.2 then acc * p.1 else acc), List.map_cons, List.prod_cons]
    rcases p with ⟨a, _ | _⟩ <;> simp [Nat.cast_mul, mul_assoc]

/-- Word-level suffix evaluation of the Naor–Reingold tree from an encoded group element `u` along
`αs` and `xs`. -/
def naorReingoldWordSuffix (d : F.Desc) (u : List Bool) (αs : List ℕ) (xs : List Bool) :
    List Bool :=
  F.smul (d, naorReingoldProdNat 1 (αs.zip xs), u)

/-- Word-level evaluation of the Naor–Reingold PRF on `(d, α₀, αs, xs)`. -/
def naorReingoldWordEval (d : F.Desc) (α₀ : ℕ) (αs : List ℕ) (xs : List Bool) : List Bool :=
  F.smul (d, naorReingoldProdNat α₀ (αs.zip xs), F.encode d (F.generator d))

/-- On an encoded group element `F.encode d u`, `naorReingoldWordSuffix` computes the encoding of
`naorReingoldTreeFold`. -/
theorem naorReingoldWordSuffix_encode (d : F.Desc) (u : F.Carrier d) (αs : List ℕ)
    (xs : List Bool) :
    F.naorReingoldWordSuffix d (F.encode d u) αs xs =
      F.encode d (F.naorReingoldTreeFold d u
        ((αs.zip xs).map fun p => ((p.1 : ZMod (F.order d)), p.2))) := by
  obtain ⟨β, rfl⟩ := F.smul_generator_surjective d u
  rw [naorReingoldWordSuffix, F.smul_encode, naorReingoldProdNat_cast, Nat.cast_one, one_mul,
    naorReingoldTreeFold_smul, List.map_map, smul_smul, mul_comm]
  rfl

/-- Correctness of `naorReingoldWordEval` on an `n`-element exponent list `αs` and `n`-bit query
`xs`. -/
theorem naorReingoldWordEval_eq_encode (d : F.Desc) {n : ℕ} (α₀ : ℕ)
    (α : Fin n → ℕ) (x : BitString n) :
    F.naorReingoldWordEval d α₀ (List.ofFn α) (List.ofFn x) =
      F.encode d (F.naorReingoldEval d (α₀ : ZMod (F.order d))
        (fun i => (α i : ZMod (F.order d))) x) := by
  rw [naorReingoldWordEval, F.smul_encode, naorReingoldProdNat_cast, naorReingoldEval,
    naorReingoldExp]
  congr 2
  have hzip : (List.ofFn α).zip (List.ofFn x) = List.ofFn (fun i : Fin n => (α i, x i)) := by
    refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
    simp
  rw [hzip, List.map_ofFn, Fin.prod_univ_def, List.prod_ofFn]
  rfl

/-- `naorReingoldProdNat` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_naorReingoldProdNat :
    ComputableInPolyTime
      (fun input : ℕ × List (ℕ × Bool) => naorReingoldProdNat input.1 input.2)
      (encPair encNat (encList (encPair encNat encBool))) encNat := by
  unfold naorReingoldProdNat
  refine ComputableInPolyTime.foldlWith_of_bounded_growth
    (encA := encPair encNat encBool) (encL := encList (encPair encNat encBool))
    (encB := encNat) (encP := encBool)
    (par := fun _ => false) (list := Prod.snd) (init := Prod.fst)
    (step := fun _ e p => if p.2 then e * p.1 else e)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (growth := fun input => (encList (encPair encNat encBool) input.2).length)
    (ComputableInPolyTime.snd _ _).polyBounded_length ?_
  intro input state value hmem
  have hval : value.1.size ≤ (encList (encPair encNat encBool) input.2).length := by
    rw [← Nat.size_eq_bits_len, ← encNat_apply]
    have h1 : (encNat value.1).length ≤ (encPair encNat encBool value).length := by
      enc_len
    exact h1.trans (length_le_encList_of_mem (encPair encNat encBool) hmem)
  rcases value with ⟨v, _ | _⟩
  · simp
  · simp only [↓reduceIte, encNat_apply, Nat.size_eq_bits_len]
    exact (Nat.size_mul_le state v).trans (Nat.add_le_add_left hval _)

/-- `naorReingoldWordSuffix` is computable in polynomial time. -/
theorem computableInPolyTime_naorReingoldWordSuffix :
    ComputableInPolyTime
      (fun input : F.Desc × List Bool × List ℕ × List Bool =>
        F.naorReingoldWordSuffix input.1 input.2.1 input.2.2.1 input.2.2.2)
      (encPair F.encDesc (encPair encBits (encPair (encList encNat) encBits))) encBits := by
  have hd : ComputableInPolyTime
      (fun input : F.Desc × List Bool × List ℕ × List Bool => input.1)
      (encPair F.encDesc (encPair encBits (encPair (encList encNat) encBits))) F.encDesc := by
    fun_prop
  have hu : ComputableInPolyTime
      (fun input : F.Desc × List Bool × List ℕ × List Bool => input.2.1)
      (encPair F.encDesc (encPair encBits (encPair (encList encNat) encBits))) encBits := by
    fun_prop
  have hαs : ComputableInPolyTime
      (fun input : F.Desc × List Bool × List ℕ × List Bool => input.2.2.1)
      (encPair F.encDesc (encPair encBits (encPair (encList encNat) encBits)))
      (encList encNat) := by
    fun_prop
  have hxs : ComputableInPolyTime
      (fun input : F.Desc × List Bool × List ℕ × List Bool => input.2.2.2)
      (encPair F.encDesc (encPair encBits (encPair (encList encNat) encBits)))
      (encList encBool) :=
    ComputableInPolyTime.bitsToList.comp (by fun_prop)
  have hzip : ComputableInPolyTime
      (fun input : F.Desc × List Bool × List ℕ × List Bool => input.2.2.1.zip input.2.2.2)
      (encPair F.encDesc (encPair encBits (encPair (encList encNat) encBits)))
      (encList (encPair encNat encBool)) :=
    (ComputableInPolyTime.zip encNat encBool).comp (hαs.prod hxs)
  have hprod : ComputableInPolyTime
      (fun input : F.Desc × List Bool × List ℕ × List Bool =>
        naorReingoldProdNat 1 (input.2.2.1.zip input.2.2.2))
      (encPair F.encDesc (encPair encBits (encPair (encList encNat) encBits))) encNat :=
    computableInPolyTime_naorReingoldProdNat.comp
      ((ComputableInPolyTime.const 1).prod hzip)
  exact F.computableInPolyTime_smul.comp (hd.prod (hprod.prod hu))

/-- `naorReingoldWordEval` is computable in polynomial time. -/
theorem computableInPolyTime_naorReingoldWordEval :
    ComputableInPolyTime
      (fun input : F.Desc × ℕ × List ℕ × List Bool =>
        F.naorReingoldWordEval input.1 input.2.1 input.2.2.1 input.2.2.2)
      (encPair F.encDesc (encPair encNat (encPair (encList encNat) encBits))) encBits := by
  have hd : ComputableInPolyTime
      (fun input : F.Desc × ℕ × List ℕ × List Bool => input.1)
      (encPair F.encDesc (encPair encNat (encPair (encList encNat) encBits))) F.encDesc := by
    fun_prop
  have hα₀ : ComputableInPolyTime
      (fun input : F.Desc × ℕ × List ℕ × List Bool => input.2.1)
      (encPair F.encDesc (encPair encNat (encPair (encList encNat) encBits))) encNat := by
    fun_prop
  have hαs : ComputableInPolyTime
      (fun input : F.Desc × ℕ × List ℕ × List Bool => input.2.2.1)
      (encPair F.encDesc (encPair encNat (encPair (encList encNat) encBits))) (encList encNat) := by
    fun_prop
  have hxs : ComputableInPolyTime
      (fun input : F.Desc × ℕ × List ℕ × List Bool => input.2.2.2)
      (encPair F.encDesc (encPair encNat (encPair (encList encNat) encBits)))
      (encList encBool) :=
    ComputableInPolyTime.bitsToList.comp (by fun_prop)
  have hzip : ComputableInPolyTime
      (fun input : F.Desc × ℕ × List ℕ × List Bool => input.2.2.1.zip input.2.2.2)
      (encPair F.encDesc (encPair encNat (encPair (encList encNat) encBits)))
      (encList (encPair encNat encBool)) :=
    (ComputableInPolyTime.zip encNat encBool).comp (hαs.prod hxs)
  have hprod : ComputableInPolyTime
      (fun input : F.Desc × ℕ × List ℕ × List Bool =>
        naorReingoldProdNat input.2.1 (input.2.2.1.zip input.2.2.2))
      (encPair F.encDesc (encPair encNat (encPair (encList encNat) encBits))) encNat :=
    computableInPolyTime_naorReingoldProdNat.comp (hα₀.prod hzip)
  have hgen : ComputableInPolyTime
      (fun input : F.Desc × ℕ × List ℕ × List Bool => F.encode input.1 (F.generator input.1))
      (encPair F.encDesc (encPair encNat (encPair (encList encNat) encBits))) encBits :=
    F.computableInPolyTime_generator.comp hd
  exact F.computableInPolyTime_smul.comp (hd.prod (hprod.prod hgen))

/-! ### Naor–Reingold prefix-hybrid evaluation (Exercise 10.4(b)) -/

/-- Suffix exponent product `∏ i : Fin n, if k ≤ i.1 ∧ x i then α i else 1` from depth `k` to `n`.
-/
def naorReingoldSuffixExp (d : F.Desc) {n : ℕ} (k : ℕ)
    (α : Fin n → ZMod (F.order d)) (x : BitString n) : ZMod (F.order d) :=
  ∏ i : Fin n, if k ≤ i.1 ∧ x i then α i else 1

@[simp]
theorem naorReingoldSuffixExp_zero (d : F.Desc) {n : ℕ}
    (α₀ : ZMod (F.order d)) (α : Fin n → ZMod (F.order d)) (x : BitString n) :
    α₀ * F.naorReingoldSuffixExp d 0 α x = F.naorReingoldExp d α₀ α x := by
  simp [naorReingoldSuffixExp, naorReingoldExp]

@[simp]
theorem naorReingoldSuffixExp_self (d : F.Desc) {n : ℕ}
    (α : Fin n → ZMod (F.order d)) (x : BitString n) :
    F.naorReingoldSuffixExp d n α x = 1 := by
  refine Finset.prod_eq_one fun i _ => ?_
  simp [Nat.not_le.mpr i.isLt]

/-- Splitting `naorReingoldSuffixExp` at depth `k < n` into the `k`-th bit factor and the depth
`k + 1` suffix. -/
theorem naorReingoldSuffixExp_eq_mul_succ (d : F.Desc) {n k : ℕ} (hk : k < n)
    (α : Fin n → ZMod (F.order d)) (x : BitString n) :
    F.naorReingoldSuffixExp d k α x =
      (if x ⟨k, hk⟩ then α ⟨k, hk⟩ else 1) * F.naorReingoldSuffixExp d (k + 1) α x := by
  unfold naorReingoldSuffixExp
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (⟨k, hk⟩ : Fin n))]
  congr 1
  · simp
  · symm
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (⟨k, hk⟩ : Fin n))]
    simp only [Nat.add_one_le_iff, lt_self_iff_false, false_and, ↓reduceIte, one_mul]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hne : i.1 ≠ k := by
      intro heq
      exact (Finset.mem_erase.mp hi).1 (Fin.ext heq)
    by_cases hlt : k < i.1
    · simp [hlt, Nat.le_of_lt hlt]
    · have hnotle : ¬k ≤ i.1 := fun hle => hlt (Nat.lt_of_le_of_ne hle hne.symm)
      simp [hlt, hnotle]

/-- Updating `α` at `⟨k, hk⟩` does not affect `naorReingoldSuffixExp` at depth `k + 1`. -/
theorem naorReingoldSuffixExp_succ_update (d : F.Desc) {n k : ℕ} (hk : k < n)
    (α : Fin n → ZMod (F.order d)) (a : ZMod (F.order d)) (x : BitString n) :
    F.naorReingoldSuffixExp d (k + 1) (Function.update α ⟨k, hk⟩ a) x =
      F.naorReingoldSuffixExp d (k + 1) α x := by
  unfold naorReingoldSuffixExp
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : k + 1 ≤ i.1
  · have hne : i ≠ ⟨k, hk⟩ := by
      intro heq
      have hval : i.1 = k := congrArg Fin.val heq
      omega
    simp [hne]
  · simp [h]

/-- Hybrid function at depth `k`: look up the `k`-bit prefix in `B : BitString k → ZMod (F.order d)`
and multiply by the remaining suffix exponent product from `k` to `n`. -/
def naorReingoldHybridEval (d : F.Desc) {n : ℕ} (k : ℕ)
    (B : BitString k → ZMod (F.order d)) (α : Fin n → ZMod (F.order d)) (x : BitString n) :
    F.Carrier d :=
  (B (BitString.zeroExtend (d' := k) x) * F.naorReingoldSuffixExp d k α x) • F.generator d

/-- Evaluating the level-`k` child table `T : BitString k → F.Carrier d × F.Carrier d` followed by
the depth-`(k + 1)` suffix exponent product. -/
def naorReingoldTableEval (d : F.Desc) {n : ℕ} (k : ℕ) (hk : k < n)
    (T : BitString k → F.Carrier d × F.Carrier d) (α : Fin n → ZMod (F.order d))
    (x : BitString n) : F.Carrier d :=
  F.naorReingoldSuffixExp d (k + 1) α x •
    if x ⟨k, hk⟩ then (T (BitString.zeroExtend (d' := k) x)).2
    else (T (BitString.zeroExtend (d' := k) x)).1

end Cslib.Crypto.PrimeOrderGroupFamily
