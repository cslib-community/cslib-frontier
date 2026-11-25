/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.SharpP
public import CslibFrontier.Computability.Complexity.Classes.BPP
public import CslibFrontier.Computability.Complexity.Classes.PP
public import CslibFrontier.Computability.Complexity.Reduction
import CslibFrontier.Computability.Complexity.Classes.SharpP.PolyTime
import CslibFrontier.Computability.Complexity.Classes.BPP.Amplification
import CslibFrontier.Computability.Complexity.Classes.PP.Characterization
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Small bounded-error polynomial time

SBP was introduced by [Böhler, Glaßer and Meister][BoehlerGlasserMeister2006]. We use
[Watson, Definition 2][Watson2012]: a #P count is at least a binary FP threshold on
members and strictly less than half the threshold on nonmembers. The threshold may
be zero; `mem_SBP_iff_exists_pos_threshold` shows that requiring positivity is equivalent.
These are verifier counts, without a proved nondeterministic counting-machine equivalence.
The containments and union closure below are elementary counting-algebra consequences;
`MA ⊆ SBP` (`Cslib.Complexity.MA_subset_SBP`) and `SBP ⊆ AM` (`Cslib.Complexity.SBP_subset_AM`)
are proved in `CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.Amplification` and
`CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.SetLowerBound`.

## Main definitions

* `Cslib.Complexity.SBP`: small bounded-error polynomial time with an input-dependent FP threshold.

## Main results

* `Cslib.Complexity.NP_subset_SBP`, `Cslib.Complexity.BPP_subset_SBP`,
  `Cslib.Complexity.SBP_subset_PP`.
* `Cslib.Complexity.union_mem_SBP`, `Cslib.Complexity.PolyTimeReducible.mem_SBP`: union and
  many-one reduction closure.
* `Cslib.Complexity.exists_SBP_gap_pow`: arbitrary fixed multiplicative gap strengthening.
* `Cslib.Complexity.inter_mem_SBP_of_mem_BPP`: intersection with a BPP language.

## References

* [E. Böhler, C. Glaßer, D. Meister, *Error-bounded probabilistic computations between
  MA and AM*][BoehlerGlasserMeister2006]
* [T. Watson, *The Complexity of Estimating Min-Entropy*][Watson2012]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

variable {α β : Type} {enc : α ↪ List Bool} {A B : Set α}

/-- A #P count at least an FP threshold on members and strictly below half on nonmembers
[Böhler, Glaßer and Meister][BoehlerGlasserMeister2006], [Watson, Definition 2][Watson2012].
The threshold is encoded in binary and may be exponentially large. -/
def SBP (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f ∈ SharpP enc, ∃ k : α → ℕ, ComputableInPolyTime k enc encNat ∧
    ∀ a, (a ∈ A → k a ≤ f a) ∧ (a ∉ A → 2 * f a < k a)}

theorem mem_SBP : A ∈ SBP enc ↔ ∃ f ∈ SharpP enc, ∃ k : α → ℕ, ComputableInPolyTime k enc encNat ∧
    ∀ a, (a ∈ A → k a ≤ f a) ∧ (a ∉ A → 2 * f a < k a) :=
  Iff.rfl

/-- Replacing `(f, k)` by `(2f + 1, 2k + 1)` makes the threshold positive. -/
theorem mem_SBP_iff_exists_pos_threshold : A ∈ SBP enc ↔
    ∃ f ∈ SharpP enc, ∃ k : α → ℕ, ComputableInPolyTime k enc encNat ∧
      (∀ a, 0 < k a) ∧ ∀ a, (a ∈ A → k a ≤ f a) ∧ (a ∉ A → 2 * f a < k a) := by
  refine ⟨fun ⟨f, hf, k, hk, hA⟩ =>
      ⟨f + f + 1, SharpP.add_mem (SharpP.add_mem hf hf) SharpP.one_mem,
        fun a => k a + k a + 1, by fun_prop, fun _ => by positivity, fun a => ?_⟩,
    fun ⟨f, hf, k, hk, _, hA⟩ => ⟨f, hf, k, hk, hA⟩⟩
  simp only [Pi.add_apply, Pi.one_apply]
  exact ⟨fun ha => by have := (hA a).1 ha; lia, fun ha => by have := (hA a).2 ha; lia⟩

/-- Threshold one recognizes precisely the positive #P counts. -/
theorem NP_subset_SBP : NP enc ⊆ SBP enc := fun A hA => by
  obtain ⟨f, hf, hA⟩ := mem_NP_iff_exists_SharpP.mp hA
  exact ⟨f, hf, fun _ => 1, .const 1, fun a => by rw [hA a]; constructor <;> intro <;> lia⟩

/-- Amplifying BPP to error at most one quarter leaves a strict factor-two count gap. -/
theorem BPP_subset_SBP : BPP enc ⊆ SBP enc := fun A hA => by
  obtain ⟨p, V, hV, hA⟩ := mem_BPP_iff_forall_decidesWithErrorExponent.mp hA 2
  refine ⟨_, SharpP.mul_mem (SharpP.natCast_mem 3) ⟨p, V, hV, fun _ => rfl⟩,
    fun a => 2 * 2 ^ p.eval (enc a).length, by fun_prop, fun a => ?_⟩
  have hle := acceptCount_le_two_pow (V := V) (a := a) (n := p.eval (enc a).length)
  have hp : 0 < 2 ^ p.eval (enc a).length := by positivity
  change (a ∈ A → _ ≤ 3 * acceptCount V a (p.eval (enc a).length)) ∧
    (a ∉ A → 2 * (3 * acceptCount V a (p.eval (enc a).length)) < _)
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · have := errorExponentAt_true_iff.1 ((hA a).1 ha)
    simp only [Polynomial.eval_ofNat] at this; lia
  · have := errorExponentAt_false_iff.1 ((hA a).2 ha)
    simp only [Polynomial.eval_ofNat] at this; lia

/-- The integer gap `2f - k + 1` is positive exactly on members, including zero thresholds. -/
theorem SBP_subset_PP : SBP enc ⊆ PP enc := by
  rintro A ⟨f, hf, k, hk, hA⟩
  refine mem_PP_iff_exists_GapP.mpr ⟨_, GapP.add_mem (GapP.sub_mem'
    (SharpP.natCast_mem_GapP (SharpP.add_mem hf hf))
    (SharpP.natCast_mem_GapP (mem_SharpP_of_polyTime hk))) GapP.one_mem, fun a => ?_⟩
  change a ∈ A ↔ 0 < ((f a + f a : ℕ) : ℤ) - (k a : ℤ) + 1
  by_cases ha : a ∈ A
  · have := (hA a).1 ha
    simp only [ha, true_iff]; lia
  · have := (hA a).2 ha
    simp only [ha, false_iff]; lia

/-- Precomposition preserves both the count and the binary FP threshold. -/
theorem PolyTimeReducible.mem_SBP {encB : β ↪ List Bool} {B : Set β}
    (h : PolyTimeReducible enc encB A B) (hB : B ∈ SBP encB) : A ∈ SBP enc := by
  obtain ⟨r, hr, hAB⟩ := h
  obtain ⟨f, hf, k, hk, hB⟩ := hB
  exact ⟨f ∘ r, SharpP.comp_mem hf hr, k ∘ r, hk.comp hr, fun a => by
    simpa only [Function.comp_apply, ← hAB a] using hB (r a)⟩

/-- Normalize two positive thresholds by cross multiplication, then square and add the counts. -/
theorem union_mem_SBP (hA : A ∈ SBP enc) (hB : B ∈ SBP enc) : A ∪ B ∈ SBP enc := by
  obtain ⟨f, hf, k, hk, hkpos, hA⟩ := mem_SBP_iff_exists_pos_threshold.mp hA
  obtain ⟨g, hg, l, hl, hlpos, hB⟩ := mem_SBP_iff_exists_pos_threshold.mp hB
  refine ⟨_, SharpP.add_mem (SharpP.pow_mem (SharpP.mul_mem hf (mem_SharpP_of_polyTime hl)) 2)
      (SharpP.pow_mem (SharpP.mul_mem hg (mem_SharpP_of_polyTime hk)) 2),
    fun a => (k a * l a) ^ 2, (binary_mul' hk hl).binary_pow' (const 2), fun a => ?_⟩
  change (a ∈ A ∪ B → (k a * l a) ^ 2 ≤ (f a * l a) ^ 2 + (g a * k a) ^ 2) ∧
    (a ∉ A ∪ B → 2 * ((f a * l a) ^ 2 + (g a * k a) ^ 2) < (k a * l a) ^ 2)
  refine ⟨?_, fun ha => ?_⟩
  · rintro (ha | ha)
    · exact (Nat.pow_le_pow_left (Nat.mul_le_mul_right _ ((hA a).1 ha)) 2).trans
        (Nat.le_add_right _ _)
    · exact (Nat.pow_le_pow_left (Nat.mul_comm (l a) _ ▸ Nat.mul_le_mul_right _ ((hB a).1 ha))
        2).trans (Nat.le_add_left _ _)
  · have h1 : (2 * (f a * l a)) ^ 2 < (k a * l a) ^ 2 :=
      Nat.pow_lt_pow_left (by
        rw [← mul_assoc]; exact Nat.mul_lt_mul_of_pos_right ((hA a).2 (mt Or.inl ha)) (hlpos a))
        (by decide)
    have h2 : (2 * (g a * k a)) ^ 2 < (k a * l a) ^ 2 :=
      Nat.pow_lt_pow_left (by
        rw [← mul_assoc, mul_comm (k a)]
        exact Nat.mul_lt_mul_of_pos_right ((hB a).2 (mt Or.inr ha)) (hkpos a)) (by decide)
    nlinarith only [h1, h2]

/-- Every fixed positive repetition count strengthens the SBP multiplicative gap.
The integer `m` is fixed independently of the input; this does not assert uniform
closure under input-dependent powers; see
`CslibFrontier/Computability/Complexity/Classes/SBP/Amplification.lean` for the uniform theorem.
See [Watson, Section 1.1][Watson2012]. -/
theorem exists_SBP_gap_pow (hA : A ∈ SBP enc) {m : ℕ} (hm : 0 < m) :
    ∃ f ∈ SharpP enc, ∃ k : α → ℕ, ComputableInPolyTime k enc encNat ∧
      (∀ a, 0 < k a) ∧ ∀ a, (a ∈ A → k a ≤ f a) ∧
        (a ∉ A → 2 ^ m * f a < k a) := by
  obtain ⟨f, hf, k, hk, hkpos, h⟩ := mem_SBP_iff_exists_pos_threshold.mp hA
  exact ⟨f ^ m, SharpP.pow_mem hf m, fun a => k a ^ m, hk.binary_pow' (.const m),
    fun a => pow_pos (hkpos a) _, fun a => ⟨fun ha => Nat.pow_le_pow_left ((h a).1 ha) m,
      fun ha => by simpa only [Pi.pow_apply, mul_pow] using
        Nat.pow_lt_pow_left ((h a).2 ha) hm.ne'⟩⟩

/-- Intersecting an SBP language with a BPP language preserves SBP.
Square the SBP gap, amplify BPP beyond the exponential bound on that count,
and multiply counts. This is an elementary consequence of counting closure and
[Arora–Barak's BPP amplification][AroraBarak09]. -/
theorem inter_mem_SBP_of_mem_BPP (hA : A ∈ SBP enc) (hB : B ∈ BPP enc) :
    A ∩ B ∈ SBP enc := by
  obtain ⟨f, hf, k, hk, hkpos, hA⟩ := exists_SBP_gap_pow hA two_pos
  obtain ⟨p, hp⟩ := SharpP.exists_le_two_pow hf
  obtain ⟨q, V, hV, hB⟩ := mem_BPP_iff_forall_decidesWithErrorExponent.mp hB (p + 2)
  let c a := acceptCount V a (q.eval (enc a).length)
  refine ⟨_, SharpP.mul_mem (SharpP.natCast_mem 4) (SharpP.mul_mem hf ⟨q, V, hV, fun _ => rfl⟩),
    fun a => 3 * (k a * 2 ^ q.eval (enc a).length),
    binary_mul' (const 3)
      (binary_mul' hk (binary_two_pow.comp ((unary_eval q).comp (encoding_length enc)))),
    fun a => ?_⟩
  have hc_le : c a ≤ 2 ^ q.eval (enc a).length := acceptCount_le_two_pow
  have hD : 0 < 2 ^ q.eval (enc a).length := by positivity
  have hp1 : 1 ≤ 2 ^ p.eval (enc a).length := Nat.one_le_pow _ _ (by decide)
  change (a ∈ A ∩ B → 3 * (k a * 2 ^ q.eval (enc a).length) ≤ 4 * (f a * c a)) ∧
    (a ∉ A ∩ B → 2 * (4 * (f a * c a)) < 3 * (k a * 2 ^ q.eval (enc a).length))
  refine ⟨fun ⟨ha, hb⟩ => ?_, fun hab => ?_⟩
  · have hbad := errorExponentAt_true_iff.1 ((hB a).1 hb)
    simp only [Polynomial.eval_add, Polynomial.eval_ofNat, pow_add] at hbad
    have : 3 * 2 ^ q.eval (enc a).length ≤ 4 * c a := by
      have : 4 * (2 ^ q.eval (enc a).length - c a) ≤ 2 ^ q.eval (enc a).length := by
        nlinarith [Nat.mul_le_mul_right (4 * (2 ^ q.eval (enc a).length - c a)) hp1]
      lia
    nlinarith [Nat.mul_le_mul_left (k a) this, Nat.mul_le_mul_right (4 * c a) ((hA a).1 ha)]
  · by_cases ha : a ∈ A
    · have hbad := errorExponentAt_false_iff.1 ((hB a).2 fun hb => hab ⟨ha, hb⟩)
      simp only [Polynomial.eval_add, Polynomial.eval_ofNat, pow_add] at hbad
      change (2 ^ p.eval (enc a).length * 2 ^ 2) * c a ≤ _ at hbad
      nlinarith [Nat.mul_le_mul_right (4 * c a) (hp a),
        Nat.mul_le_mul_right (2 ^ q.eval (enc a).length) (hkpos a)]
    · have hsmall := (hA a).2 ha
      norm_num only [pow_succ, pow_zero] at hsmall
      nlinarith [Nat.mul_lt_mul_of_pos_right hsmall hD, Nat.mul_le_mul_left (4 * f a) hc_le]

end Cslib.Complexity
