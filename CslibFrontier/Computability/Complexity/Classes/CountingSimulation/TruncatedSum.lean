/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.Accumulate
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.TruncatedAlgorithm
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith
import CslibFrontier.Foundations.Data.List.OfFn
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Mathlib.Algebra.BigOperators.ModEq
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation

/-!
# Summing the truncated contractions of a computed family of networks

On each branch, the proof of Lemma D.2 of [OpenAI2026ETH] (pp. 56–57) contracts one network per
degree array by Theorem D.1 at truncation order `ℓ`. It sums the contractions in
`B = (ℤ / 2 ^ p)[V] / (V ^ ℓ)`, applies the coefficient sum `S_ℓ`, and reduces modulo `2 ^ p`.
This file is that loop, for any computed family of networks and any algorithm with the interface
of Theorem D.1 at truncation order `ℓ` (`Cslib.Circuits.Frontier.TruncatedContractionAlgorithm`).

`S_ℓ` is additive. So the loop applies it to each contraction
(`Cslib.Complexity.CountingSimulation.truncCoeffSum`) and adds the residues modulo the modulus,
one network at a time (`Cslib.Complexity.CountingSimulation.truncSum`). The streamed modular sum
`Cslib.Complexity.CountingSimulation.modSum` keeps only the index, the context and the
accumulator. If the contractions sum, coefficientwise below `V ^ ℓ` and modulo `2 ^ P`, to given
integers, the loop computes their sum modulo `2 ^ P`
(`Cslib.Complexity.CountingSimulation.truncSum_modEq`). In Lemma D.2 these integers are the
coefficients below `V ^ ℓ` of the incidence sum, whose sum is the branch count modulo `2 ^ p` by the
congruence (D.2) (#2076).

**Resources** (`Cslib.Complexity.CountingSimulation.exists_truncSum_certificate`). Suppose the
networks are built in polynomial time from the context and the index. Suppose further that, on a
context `c`, they are admissible at size `s c` with precision and truncation order between `1` and
`D s c`. Then the loop takes time `(count c + 1) K (n + 1) ^ K 2 ^ (K s / √⌊log₂ s⌋)` and space
`K (n + 1) ^ K`, for the context's encoded length `n` and a constant `K`. The constant is chosen
before the context, and the number of networks is an explicit factor.

## Main definitions

* `Cslib.Complexity.CountingSimulation.truncCoeffSum`: `S_ℓ` of a truncated contraction.
* `Cslib.Complexity.CountingSimulation.truncSum`: the sum of the `truncCoeffSum` of the networks,
  modulo the modulus.

## Main results

* `Cslib.Complexity.CountingSimulation.truncSum_eq`: the loop is the sum modulo the modulus.
* `Cslib.Complexity.CountingSimulation.truncSum_modEq`: the congruence to the sum of the summed
  coefficients.
* `Cslib.Complexity.CountingSimulation.exists_truncSum_certificate`: time and space.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Theorem D.1 (p. 53) and the
  proof of Lemma D.2 (pp. 54–57).
-/

public section

namespace Cslib.Complexity.CountingSimulation

open Cslib.Circuits.Frontier Cslib.GenericRAM Turing.MultiTapeTM Finset
open Turing.MultiTapeTM.ComputableInPolyTime (binary_sum)

variable {C T : Type} {encC : C ↪ List Bool} {encT : T ↪ List Bool}
  {entry : T → List Bool → List ℕ}

/-- **The coefficient sum `S_ℓ` of a truncated contraction**: the sum of the `ℓ` coefficients of
the contraction of `G` in `(ℤ / 2 ^ P)[V] / (V ^ ℓ)`, for the input `(P, ℓ, r, G)`. -/
@[expose] noncomputable def truncCoeffSum (entry : T → List Bool → List ℕ) :
    ℕ × ℕ × ℕ × DescribedNetwork T → ℕ
  | (P, ℓ, _, G) => (G.truncContraction entry P ℓ).sum

/-- `S_ℓ` of a truncated contraction is the sum of the coefficients below `V ^ ℓ` of the
contraction over `ℕ[V]`, each reduced modulo `2 ^ P`. -/
theorem truncCoeffSum_eq (entry : T → List Bool → List ℕ) (P ℓ r : ℕ) (G : DescribedNetwork T) :
    truncCoeffSum entry (P, ℓ, r, G) =
      ∑ j ∈ range ℓ, (G.polyContraction entry).coeff j % 2 ^ P := by
  rw [truncCoeffSum, DescribedNetwork.truncContraction, List.sum_map_range]
  exact Fin.sum_univ_eq_sum_range (fun j => (G.polyContraction entry).coeff j % 2 ^ P) ℓ

/-- **The loop of Lemma D.2 on one branch**: the sum, modulo `modulus c`, of the coefficient sums
of the truncated contractions of the networks `build (c, i)` for `i < count c`, streamed one
network at a time. -/
@[expose] noncomputable def truncSum (entry : T → List Bool → List ℕ)
    (build : C × ℕ → ℕ × ℕ × ℕ × DescribedNetwork T) (modulus count : C → ℕ) (c : C) : ℕ :=
  modSum (fun q => truncCoeffSum entry (build q) % modulus q.1) modulus count c

variable {build : C × ℕ → ℕ × ℕ × ℕ × DescribedNetwork T} {modulus count : C → ℕ}

/-- **The loop is the sum modulo the modulus.** -/
theorem truncSum_eq (c : C) :
    truncSum entry build modulus count c =
      (∑ i ∈ range (count c), truncCoeffSum entry (build (c, i))) % modulus c := by
  rw [truncSum, modSum_eq_sum_mod]
  change (∑ i ∈ range (count c), truncCoeffSum entry (build (c, i)) % modulus c) % modulus c = _
  exact (Finset.sum_nat_mod _ _ _).symm

/-- **The congruence of the loop.** Suppose the networks `G i` of context `c` have precision `P`
and truncation order `ℓ`, the modulus is `2 ^ P`, and for every `j < ℓ` the `V ^ j` coefficients
of their contractions over `ℕ[V]` sum to `q j` modulo `2 ^ P`. Then the loop is the sum of the
`q j` modulo `2 ^ P`. -/
theorem truncSum_modEq {c : C} {P ℓ : ℕ} (hmod : modulus c = 2 ^ P) (G : ℕ → DescribedNetwork T)
    (hbuild : ∀ i < count c, ∃ r, build (c, i) = (P, ℓ, r, G i)) (q : ℕ → ℤ)
    (hq : ∀ j < ℓ, ((∑ i ∈ range (count c), ((G i).polyContraction entry).coeff j : ℕ) : ℤ) ≡
      q j [ZMOD 2 ^ P]) :
    (truncSum entry build modulus count c : ℤ) ≡ ∑ j ∈ range ℓ, q j [ZMOD 2 ^ P] := by
  have hterm : ∀ i ∈ range (count c), truncCoeffSum entry (build (c, i)) =
      ∑ j ∈ range ℓ, ((G i).polyContraction entry).coeff j % 2 ^ P := by
    intro i hi
    obtain ⟨r, hr⟩ := hbuild i (mem_range.mp hi)
    rw [hr, truncCoeffSum_eq]
  rw [truncSum_eq, hmod, sum_congr rfl hterm, sum_comm]
  push_cast
  refine (Int.mod_modEq _ _).trans ((Int.ModEq.sum fun j _ =>
    Int.ModEq.sum fun i _ => Int.mod_modEq _ _).trans ?_)
  refine Int.ModEq.sum fun j hj => ?_
  have h := hq j (mem_range.mp hj)
  push_cast at h
  exact h

/-! ### Resources -/

/-- **Time and space of the loop.** Let `A` be an algorithm with the interface of Theorem D.1 at
truncation order `ℓ`, with admissibility `Adm`. Let the networks, the modulus (positive) and the
number of networks be computable in polynomial time from the context. Then there is a native
certificate of the loop and a constant `K` with the following property. On every context `c` with
`2 ≤ s c` all of whose networks are admissible at size `s c` with constant `Cadm`, with precision
and truncation order between `1` and `D s c`, the loop takes time at most
`(count c + 1) K (n + 1) ^ K 2 ^ (K s c / √⌊log₂ s c⌋)` and space at most `K (n + 1) ^ K`, where
`n` is the encoded length of `c`. -/
theorem exists_truncSum_certificate {Adm : ℕ → ℕ → ℕ × DescribedNetwork T → Prop}
    (A : TruncatedContractionAlgorithm encT entry Adm)
    (hbuild : ComputableInPolyTime build (encPair encC encNat) (encTrunc encT))
    (hmodulus : ComputableInPolyTime modulus encC encNat)
    (hcount : ComputableInPolyTime count encC encNat) (hpos : ∀ c, 0 < modulus c)
    (Cadm D : ℕ) (s : C → ℕ) :
    ∃ (cs : NativeCertificate (truncSum entry build modulus count) encC encNat) (K : ℕ),
      ∀ c, 2 ≤ s c →
        (∀ i < count c,
          let (P, ℓ, r, G) := build (c, i)
          1 ≤ P ∧ P ≤ D * s c ∧ 1 ≤ ℓ ∧ ℓ ≤ D * s c ∧ Adm Cadm (s c) (r, G)) →
        cs.time c ≤ (count c + 1) * (K * ((encC c).length + 1) ^ K *
            2 ^ (K * s c / Nat.sqrt (Nat.log 2 (s c)))) ∧
          cs.space c ≤ K * ((encC c).length + 1) ^ K := by
  have hfst : ComputableInPolyTime (fun q : C × ℕ => q.1) (encPair encC encNat) encC :=
    ComputableInPolyTime.fst encC encNat
  have hpost : ComputableInPolyTime (fun p : List ℕ × C => p.1.sum % modulus p.2)
      (encPair (encList encNat) encC) encNat :=
    ComputableInPolyTime.binary_mod' (binary_sum.comp (.fst _ _)) (hmodulus.comp (.snd _ _))
  let cr : NativeCertificate (fun q : C × ℕ => truncCoeffSum entry (build q) % modulus q.1)
      (encPair encC encNat) encNat :=
    ((NativeCertificate.ofPolyTime hpost).comp
      ((A.certificate.comp (NativeCertificate.ofPolyTime hbuild)).prod
        (NativeCertificate.ofPolyTime hfst))).congr fun _ => rfl
  let R : C → ℕ := fun c => (range (count c)).sup fun i => cr.time (c, i)
  let Q : C → ℕ := fun c => (range (count c)).sup fun i => cr.space (c, i)
  obtain ⟨a, d, h⟩ := exists_computableInO_modSum hmodulus hcount cr hpos
    (fun c i _ => Nat.mod_lt _ (hpos c)) R Q
    (fun c i hi => le_sup (f := fun i => cr.time (c, i)) (mem_range.mpr hi))
    (fun c i hi => le_sup (f := fun i => cr.space (c, i)) (mem_range.mpr hi))
  refine ⟨⟨_, _, h⟩, ?_⟩
  -- The polynomial-time pieces of a term.
  obtain ⟨pB, hpB, mB, bB⟩ := exists_mono_poly_cert hbuild
  obtain ⟨pF, hpF, mF, bF⟩ := exists_mono_poly_cert hfst
  obtain ⟨pP, hpP, mP, bP⟩ := exists_mono_poly_cert hpost
  obtain ⟨pBL, hpBL, mBL, bBL⟩ := exists_mono_poly hbuild.polyBounded_length
  obtain ⟨K₀, hK₀⟩ := A.bound Cadm D
  obtain ⟨cO, -, hcO⟩ := A.certificate.computes
  -- Sizes, as functions of the context.
  set L : C → ℕ := fun c => (encC c).length with hL
  set lk : C → ℕ := fun c => (encNat (count c)).length with hlk
  -- The input of a term, the network, the contraction and the post-processing input.
  let Lq : C → ℕ := fun c => 2 * L c + 1 + lk c
  let Lb : C → ℕ := fun c => pBL (Lq c)
  let Sp : C → ℕ := fun c => K₀ * (Lb c + 1) ^ K₀
  let Lo : C → ℕ := fun c => cO * (Sp c + 1)
  let Lp : C → ℕ := fun c => 2 * Lo c + 1 + L c
  let U : C → ℕ := fun c => pB (Lq c) + pF (Lq c) + pP (Lp c) + Sp c
  let W : C → ℕ := fun c => a * (L c + 1) ^ d + U c
  have hW : PolyBounded L W := by growth_poly
  obtain ⟨a', d', hWad⟩ := hW.exists_le
  refine ⟨a' + d' + K₀, fun c hs hgood => ?_⟩
  set E := 2 ^ (K₀ * s c / Nat.sqrt (Nat.log 2 (s c))) with hE
  have hE1 : 1 ≤ E := Nat.one_le_two_pow
  -- A term at a summed index costs at most `U c * E` time and `U c` space.
  have hterm : ∀ i < count c, cr.time (c, i) ≤ U c * E ∧ cr.space (c, i) ≤ U c := by
    intro i hi
    obtain ⟨hP1, hPD, hℓ1, hℓD, hadm⟩ := hgood i hi
    have hq : (encPair encC encNat (c, i)).length ≤ Lq c := by
      have := length_encNat_mono (le_of_lt hi)
      rw [length_encPair]
      simp only [Lq, L, lk] at this ⊢
      omega
    have hxlen : (encTrunc encT (build (c, i))).length ≤ Lb c := (bBL (c, i)).trans (mBL hq)
    obtain ⟨hAt, hAs⟩ := hK₀ (s c) (build (c, i)).1 (build (c, i)).2.1 (build (c, i)).2.2.1
      (build (c, i)).2.2.2 hs hP1 hPD hℓ1 hℓD hadm
    have hAs' : A.certificate.space (build (c, i)) ≤ Sp c :=
      hAs.trans (by dsimp only [Sp]; gcongr)
    have hAt' : A.certificate.time (build (c, i)) ≤ Sp c * E :=
      hAt.trans (by dsimp only [Sp]; gcongr)
    have hout : (encList encNat ((build (c, i)).2.2.2.truncContraction entry (build (c, i)).1
        (build (c, i)).2.1)).length ≤ Lo c :=
      (hcO (build (c, i))).trans (Nat.mul_le_mul_left _ (by omega))
    have hpair : (encPair (encList encNat) encC
        ((build (c, i)).2.2.2.truncContraction entry (build (c, i)).1 (build (c, i)).2.1,
          c)).length ≤ Lp c := by
      rw [length_encPair]
      simp only [Lp, L]
      omega
    have h1 := (bB (c, i)).imp (·.trans (mB hq)) (·.trans (mB hq))
    have h2 := (bF (c, i)).imp (·.trans (mF hq)) (·.trans (mF hq))
    have h3 := (bP _).imp (·.trans (mP hpair)) (·.trans (mP hpair))
    simp only [cr, NativeCertificate.congr, NativeCertificate.comp_time,
      NativeCertificate.comp_space, NativeCertificate.prod_time, NativeCertificate.prod_space,
      Function.comp_apply]
    refine ⟨?_, ?_⟩
    · calc _ ≤ pB (Lq c) + Sp c * E + pF (Lq c) + pP (Lp c) :=
            Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h1.1 hAt') h2.1) h3.1
        _ = (pB (Lq c) + pF (Lq c) + pP (Lp c)) + Sp c * E := by ring
        _ ≤ (pB (Lq c) + pF (Lq c) + pP (Lp c)) * E + Sp c * E :=
            Nat.add_le_add_right (Nat.le_mul_of_pos_right _ hE1) _
        _ = U c * E := by simp only [U]; ring
    · exact (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h1.2 hAs') h2.2) h3.2).trans
        (by dsimp only [U]; omega)
  -- The trajectory maxima.
  have hR : R c ≤ U c * E := Finset.sup_le fun i hi => (hterm i (mem_range.mp hi)).1
  have hQ : Q c ≤ U c := Finset.sup_le fun i hi => (hterm i (mem_range.mp hi)).2
  have hWc := hWad c
  have hK : a' * (L c + 1) ^ d' ≤ (a' + d' + K₀) * (L c + 1) ^ (a' + d' + K₀) := by gcongr <;> omega
  have hEK : E ≤ 2 ^ ((a' + d' + K₀) * s c / Nat.sqrt (Nat.log 2 (s c))) :=
    Nat.pow_le_pow_right (by omega)
      (Nat.div_le_div_right (Nat.mul_le_mul_right _ (by omega)))
  refine ⟨?_, ?_⟩
  · change (count c + 1) * (a * (L c + 1) ^ d + R c) ≤ _
    refine Nat.mul_le_mul_left _ ?_
    calc a * (L c + 1) ^ d + R c ≤ W c * E := by
          have : a * (L c + 1) ^ d ≤ a * (L c + 1) ^ d * E := Nat.le_mul_of_pos_right _ hE1
          simp only [W, add_mul]
          omega
      _ ≤ ((a' + d' + K₀) * (L c + 1) ^ (a' + d' + K₀)) *
          2 ^ ((a' + d' + K₀) * s c / Nat.sqrt (Nat.log 2 (s c))) :=
        Nat.mul_le_mul (hWc.trans hK) hEK
  · change a * (L c + 1) ^ d + Q c ≤ _
    have : a * (L c + 1) ^ d + Q c ≤ W c := by simp only [W]; omega
    exact this.trans (hWc.trans hK)

end Cslib.Complexity.CountingSimulation
