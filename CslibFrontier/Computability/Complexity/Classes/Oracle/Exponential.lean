/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate


public import CslibFrontier.Computability.Complexity.Classes.Oracle.Exponential.Basic
public import CslibFrontier.Computability.Probabilistic.Internal.Oracle.Exponential
import CslibFrontier.Computability.Complexity.Classes.Oracle.Closure
import CslibFrontier.Computability.Complexity.Classes.Padding
import CslibFrontier.Computability.Complexity.Reduction
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Exponential time relative to an oracle language

`E` relative to an oracle language `A` is decided by a deterministic oracle machine within time
`2 ^ O(n)`; its requests may therefore be exponentially long
[Williams, p. 2, footnote 5][Williams2010]. The certificate `Cslib.Probability.IsOracleExpTimeOn`
is `Cslib.Probability.IsOraclePPTOn` with the polynomial clock `c * (n + 1) ^ d` replaced by the
clock `c * 2 ^ (d * n)`: one finite-control machine reproduces the program's complete interaction
with every stateful oracle, charging the construction of each request and the reading of each
reply. As in `IsOraclePPTOn`, the run is cut off at the clock, which is a fixed function of the
input length.

`Cslib.Complexity.ComputableInExpTimeWithOracle` and `Cslib.Complexity.EWithOracle` relativize `E`
exactly as `Cslib.Complexity.ComputableInPolyTimeWithOracle` and `Cslib.Complexity.PWithOracle`
relativize `P`, and `Cslib.Complexity.ENP` is the union of `EWithOracle A` over the oracle
languages `A` in `NP`.

Both `E` and `P` relative to `A` lie inside `E` relative to `A`
(`Cslib.Complexity.E_subset_EWithOracle`, `Cslib.Complexity.PWithOracle_subset_EWithOracle`), so
`P ^ NP ⊆ E ^ NP` (`Cslib.Complexity.iUnion_PWithOracle_NP_subset_ENP`). The
*preprocessing rule* `Cslib.Complexity.preimage_mem_EWithOracle` composes a deterministic
preparation within time `O(2 ^ (d * n))` with a problem in `P` relative to `A` on the prepared
instances. Its typical use is padding: a polynomial-time algorithm with an oracle, run on an
exponentially padded instance, is an exponential-time algorithm with that oracle. The preparation
phase is a tidy normal form of the deterministic machine, and the oracle phase a clean realization
of the polynomial-time certificate (provided by the internal oracle compiler); the two
are sequenced by `Turing.MultiTapePTM.ComputesTidily.comp`, which charges the intermediate word.

In this way `NE ⊆ E ^ NP` (`Cslib.Complexity.NE_subset_ENP`): a problem in nondeterministic time
`2 ^ O(n)` is decided on exponentially padded instances by a problem in `NP`
(`Cslib.Complexity.exists_mem_NP_frame_append_mem_iff_of_mem_NTIME`), so an exponential-time
machine writes the padded instance and asks the `NP` oracle about it.

## Main definitions

* `Cslib.Probability.IsOracleExpTimeOn`: realization by one machine within a clock `2 ^ O(n)`.
* `Cslib.Complexity.ComputableInExpTimeWithOracle`: exponential time relative to an oracle.
* `Cslib.Complexity.EWithOracle`: `E` relative to an oracle language.
* `Cslib.Complexity.ENP`: `E ^ NP`.

## Main results

* `Cslib.Probability.IsOraclePPTOn.isOracleExpTimeOn`: a polynomial clock is an exponential one.
* `Cslib.Probability.IsOraclePPTOn.preprocess_exp`: exponential-time deterministic preparation,
  then a strict oracle PPT program.
* `Cslib.Complexity.ComputableInPolyTimeWithOracle.computableInExpTimeWithOracle`,
  `Cslib.Complexity.ComputableInPolyTimeWithOracle.comp_computableInO`.
* `Cslib.Complexity.E_subset_EWithOracle`, `Cslib.Complexity.PWithOracle_subset_EWithOracle`,
  `Cslib.Complexity.preimage_mem_EWithOracle`.
* `Cslib.Complexity.E_subset_ENP`, `Cslib.Complexity.iUnion_PWithOracle_NP_subset_ENP`,
  `Cslib.Complexity.NP_subset_ENP`: `E`, `P ^ NP` and `NP` lie inside `E ^ NP`.
* `Cslib.Complexity.NE_subset_ENP`: `NE ⊆ E ^ NP`, by padding.

## References

* [R. Williams, *Improving exhaustive search implies superpolynomial lower bounds*][Williams2010]
-/

@[expose] public section

namespace Cslib

namespace Complexity

open Probability Turing.MultiTapeTM

variable {α β γ : Type}

/-- `f` is computable in exponential time relative to the oracle language `A`: a deterministic
word-query program computes `f` against `A`, and one finite machine under one clock
`c * 2 ^ (d * n)` realizes the program against every stateful oracle, charging request
construction and reply access. This is `Cslib.Complexity.ComputableInPolyTimeWithOracle` with the
clock `2 ^ O(n)`. -/
def ComputableInExpTimeWithOracle (A : Set (List Bool)) (f : α → β) (input : α ↪ List Bool)
    (output : β ↪ List Bool) : Prop :=
  ∃ program : α → WordQueryComp Unit β,
    IsOracleExpTimeOn input output
        (fun a => OracleComp.interpret ProbOracleComp.query (program a)) ∧
      ∀ a, OracleComp.interpret (m := Id) (languageOracle A) (program a) = f a

/-- **Polynomial time relative to `A` is exponential time relative to `A`.** -/
theorem ComputableInPolyTimeWithOracle.computableInExpTimeWithOracle {A : Set (List Bool)}
    {f : α → β} {input : α ↪ List Bool} {output : β ↪ List Bool}
    (h : ComputableInPolyTimeWithOracle A f input output) :
    ComputableInExpTimeWithOracle A f input output :=
  let ⟨program, hcert, hf⟩ := h
  ⟨program, hcert.isOracleExpTimeOn, hf⟩

/-- **Exponential-time preparation, then polynomial time relative to `A`.** -/
theorem ComputableInPolyTimeWithOracle.comp_computableInO {A : Set (List Bool)} {g : β → γ}
    {prepare : α → β} {input : α ↪ List Bool} {middle : β ↪ List Bool} {output : γ ↪ List Bool}
    {S : α → ℕ} {d : ℕ} (hg : ComputableInPolyTimeWithOracle A g middle output)
    (hprepare : ComputableInO prepare input middle (fun a => 2 ^ (d * (input a).length)) S) :
    ComputableInExpTimeWithOracle A (g ∘ prepare) input output :=
  let ⟨program, hcert, hg⟩ := hg
  ⟨fun a => program (prepare a), hcert.preprocess_exp hprepare, fun a => hg (prepare a)⟩

/-- The problems decidable in time `2 ^ O(n)` relative to the oracle language `A`, with respect to
the encoding `enc` of instances: `Cslib.Complexity.E` with an oracle, defined like
`Cslib.Complexity.PWithOracle`. -/
def EWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) : Set (Set α) :=
  {L | ∃ f : α → Bool, ComputableInExpTimeWithOracle A f enc encBool ∧ ∀ a, a ∈ L ↔ f a = true}

theorem mem_EWithOracle {A : Set (List Bool)} {enc : α ↪ List Bool} {L : Set α} :
    L ∈ EWithOracle A enc ↔ ∃ f : α → Bool,
      ComputableInExpTimeWithOracle A f enc encBool ∧ ∀ a, a ∈ L ↔ f a = true :=
  Iff.rfl

/-- **`E ^ NP`**: the problems decidable in time `2 ^ O(n)` relative to some oracle language in
`NP` [Williams, p. 2, footnote 5][Williams2010]. The requests may have length `2 ^ O(n)`. -/
def ENP (enc : α ↪ List Bool) : Set (Set α) :=
  ⋃ A ∈ NP encBits, EWithOracle A enc

theorem mem_ENP {enc : α ↪ List Bool} {L : Set α} :
    L ∈ ENP enc ↔ ∃ A ∈ NP encBits, L ∈ EWithOracle A enc := by
  simp only [ENP, Set.mem_iUnion, exists_prop]

/-- `P` relative to `A` lies inside `E` relative to `A`. -/
theorem PWithOracle_subset_EWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) :
    PWithOracle A enc ⊆ EWithOracle A enc := fun _ ⟨f, hf, h⟩ =>
  ⟨f, hf.computableInExpTimeWithOracle, h⟩

/-- **The preprocessing rule.** If `prepare` is computable within time `O(2 ^ (d * n))` and `M` is
in `P` relative to `A`, then the problem of whether the prepared instance is in `M` is in `E`
relative to `A`. -/
theorem preimage_mem_EWithOracle {A : Set (List Bool)} {enc : α ↪ List Bool}
    {middle : β ↪ List Bool} {M : Set β} {prepare : α → β} {S : α → ℕ} {d : ℕ}
    (hM : M ∈ PWithOracle A middle)
    (hprepare : ComputableInO prepare enc middle (fun a => 2 ^ (d * (enc a).length)) S) :
    prepare ⁻¹' M ∈ EWithOracle A enc :=
  let ⟨g, hg, hM⟩ := hM
  ⟨g ∘ prepare, hg.comp_computableInO hprepare, fun a => hM (prepare a)⟩

/-- **`E` lies inside `E` relative to every oracle**: a deterministic machine makes no request. -/
theorem E_subset_EWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) :
    E enc ⊆ EWithOracle A enc := by
  intro L hL
  obtain ⟨k, c₁, c₂, s, hL⟩ := mem_E_iff.mp hL
  obtain ⟨f, hf, hfL⟩ := decidableInTimeAndSpace_iff.mp hL
  have hO : ComputableInO f enc encBool (fun a => 2 ^ (k * (enc a).length))
      (fun a => 2 ^ (k * (enc a).length) + s (enc a).length) := by
    refine ⟨c₁ + c₂ + 1, hf.mono (fun a => ?_) (fun a => ?_), fun a => ?_⟩
    · change c₁ * 2 ^ (k * (enc a).length) + c₂ ≤
        (c₁ + c₂ + 1) * (2 ^ (k * (enc a).length) + 1)
      rw [Nat.mul_add, Nat.mul_one]
      exact Nat.add_le_add (Nat.mul_le_mul_right _ (by omega)) (by omega)
    · change s (enc a).length ≤
        (c₁ + c₂ + 1) * (2 ^ (k * (enc a).length) + s (enc a).length + 1)
      exact ((Nat.le_add_left _ _).trans (Nat.le_succ _)).trans
        (Nat.le_mul_of_pos_left _ (by omega))
    · simp only [encBool_apply, List.length_singleton]
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (Nat.succ_ne_zero _))
  have h := preimage_mem_EWithOracle (A := A) (M := {b : Bool | b = true})
    (prepare := f) (P_subset_PWithOracle A encBool ⟨id, ComputableInPolyTime.id', fun _ =>
      Iff.rfl⟩) hO
  have hL' : L = f ⁻¹' {b : Bool | b = true} := Set.ext fun a => hfL a
  rwa [hL']

/-- `E` lies inside `E ^ NP`. -/
theorem E_subset_ENP (enc : α ↪ List Bool) : E enc ⊆ ENP enc := fun _ hL =>
  mem_ENP.mpr ⟨∅, P_subset_NP empty_mem_P, E_subset_EWithOracle ∅ enc hL⟩

/-- **`P ^ NP ⊆ E ^ NP`**: `P` relative to a language in `NP` lies inside `E` relative to it. -/
theorem iUnion_PWithOracle_NP_subset_ENP (enc : α ↪ List Bool) :
    (⋃ A ∈ NP encBits, PWithOracle A enc) ⊆ ENP enc :=
  Set.biUnion_mono subset_rfl fun A _ => PWithOracle_subset_EWithOracle A enc

/-- `NP` lies inside `E ^ NP`: one request decides an `NP` language. -/
theorem NP_subset_ENP : NP encBits ⊆ ENP encBits := fun A hA =>
  iUnion_PWithOracle_NP_subset_ENP encBits (Set.mem_biUnion hA (mem_PWithOracle_self A))

/-- **`NE ⊆ E ^ NP`**, by the standard padding argument. A problem decidable by a nondeterministic
machine within time `O(2 ^ (k * n))` is decided on the padded instances
`frame (enc a) ++ 1^{2 ^ ((k + 1) * n)}` by a problem `B ∈ NP`
(`Cslib.Complexity.exists_mem_NP_frame_append_mem_iff_of_mem_NTIME`). An exponential-time machine
writes the padded instance and asks `B` about it, with one request of length `2 ^ O(n)`
(`Cslib.Complexity.preimage_mem_EWithOracle`). -/
theorem NE_subset_ENP (enc : α ↪ List Bool) : NE enc ⊆ ENP enc := by
  intro A hA
  obtain ⟨k, hk⟩ := mem_NE_iff.mp hA
  obtain ⟨B, hB, hAB⟩ := exists_mem_NP_frame_append_mem_iff_of_mem_NTIME hk
  obtain ⟨d, S, hpad⟩ := exists_computableInO_frame_append_two_pow (enc := enc)
    (f := fun n => (k + 1) * n) (by fun_prop) fun n => Nat.le_mul_of_pos_left n k.succ_pos
  have hA_eq : A = (fun a => frame (enc a) ++
      List.replicate (2 ^ ((k + 1) * (enc a).length)) true) ⁻¹' B :=
    Set.ext fun a => (hAB a _ (List.length_replicate.trans_ge (Nat.pow_le_pow_right two_pos
      (Nat.mul_le_mul_right _ k.le_succ)))).symm
  rw [hA_eq]
  exact mem_ENP.mpr ⟨B, hB, preimage_mem_EWithOracle (d := d * (k + 1)) (mem_PWithOracle_self B)
    (by simpa only [Nat.mul_assoc] using hpad)⟩

end Complexity

end Cslib
