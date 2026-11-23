/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.EXP
public import CslibFrontier.Computability.Complexity.Classes.PH
public import CslibFrontier.Computability.Complexity.Classes.PP.Closure
public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Computability.Complexity.Classes.Space.Closure
public import CslibFrontier.Computability.Complexity.Classes.Space.Savitch
import CslibFrontier.Computability.Complexity.Classes.Space.Time
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace
import CslibFrontier.Computability.Complexity.Reduction.Word
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential
import CslibFrontier.Tactic.EncLen

/-!
# Inclusions between complexity classes

The inclusions between the standard classes that papers cite in their preliminaries
[Arora and Barak, Chapters 2, 4, 5 and 7][AroraBarak09], [Sipser, Chapters 8 and 10][Sipser2013].
This module proves the inclusions that need several classes at once and imports the narrower
modules for the others: `P ⊆ BPP` is in `CslibFrontier.Computability.Complexity.Classes.BPP`, the
closure properties of `PP` in `CslibFrontier.Computability.Complexity.Classes.PP.Closure`, and those
of `PSPACE` in `CslibFrontier.Computability.Complexity.Classes.Space.Closure`.

* `P ⊆ BPP` (`Cslib.Complexity.P_subset_BPP`): a decider ignores its random string.
* `NP ⊆ PP` (`Cslib.Complexity.NP_subset_PP`): accept on half of the random strings outright, and
  on the other half run the verifier, so the majority accepts exactly when some certificate does.
* `PP` is closed under complement (`Cslib.Complexity.compl_mem_PP`): with two more random bits,
  accept on a quarter of the random strings and one more, and on half of them reject what the
  verifier accepts; the majority accepts exactly when the verifier accepts at most half of its
  random strings.
* `NP ⊆ PSPACE` (`Cslib.Complexity.NP_subset_PSPACE`): a nondeterministic machine visits at most
  one new cell per step on each work tape (`Turing.MultiTapeNTM.RunsInTime.runsInSpace`), so `NP`
  is within `NPSPACE`, which is `PSPACE` by Savitch's theorem
  (`Cslib.Complexity.NPSPACE_subset_PSPACE`).
* `PSPACE ⊆ EXP` (`Cslib.Complexity.PSPACE_subset_EXP`): a decider within polynomial space halts
  within its number of configurations (`Cslib.Complexity.exists_mem_DTIME_of_mem_DSPACE`).
* `PH ⊆ PSPACE` (`Cslib.Complexity.PH_subset_PSPACE`): `PSPACE` contains `P`, is closed under
  complement (`Cslib.Complexity.compl_mem_PSPACE`), under polynomial-time reductions
  (`Cslib.Complexity.PolyTimeReducible.mem_PSPACE`) and under polynomially bounded existential
  quantification (`Cslib.Complexity.setOf_exists_mem_PSPACE`), so it evaluates the alternating
  quantifiers of every level of the hierarchy one at a time. The existential quantifier over the
  words `w` of length `ℓ` is reachability within two steps from the all-zero word to the all-one
  word of width `ℓ + 1`, along edges to `true :: w` for the accepted `w` and from every word
  starting with `true` to the all-one word; Savitch's algorithm decides it at depth `1`,
  enumerating the candidates in place and reusing the space of the decider for each.

With `Cslib.Complexity.P_subset_NP`, these give the chain `P ⊆ NP ⊆ PSPACE ⊆ EXP`. The other
inclusions of the chains are elsewhere: `P ⊆ PSPACE` (`Cslib.Complexity.P_subset_PSPACE`),
`NPSPACE = PSPACE` (`Cslib.Complexity.NPSPACE_eq_PSPACE`), `RP ⊆ NP`
(`Cslib.Complexity.RP_subset_NP`), `BPP ⊆ PP` (`Cslib.Complexity.BPP_subset_PP`), `BPP ⊆ Σ₂ ∩ Π₂`
(`Cslib.Complexity.BPP_subset_SigmaP_two_inter_PiP_two`), `L ⊆ NL ⊆ P`
(`Cslib.Complexity.L_subset_NL`, `Cslib.Complexity.NL_subset_P`), `P ⊆ EXP` and its strictness
(`Cslib.Complexity.P_subset_EXP`, `Cslib.Complexity.P_ssubset_EXP`).

## Main results

* `Cslib.Complexity.NP_subset_NPSPACE`, `Cslib.Complexity.NP_subset_PSPACE`.
* `Cslib.Complexity.PSPACE_subset_EXP`, `Cslib.Complexity.NP_subset_EXP`.
* `Cslib.Complexity.SigmaP_subset_PSPACE`, `Cslib.Complexity.PH_subset_PSPACE`.
* `Cslib.Complexity.SigmaP_subset_EXP`, `Cslib.Complexity.SigmaP_subset_NEXP`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
* [J. Gill, *Computational complexity of probabilistic Turing machines*][Gill1977]
* [L. Stockmeyer, *The polynomial-time hierarchy*][Stockmeyer1976]
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM Filter

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-! ### Space -/

/-- **`NP ⊆ NPSPACE`**: a nondeterministic machine deciding a problem in polynomial time visits at
most polynomially many work-tape cells. -/
theorem NP_subset_NPSPACE : NP enc ⊆ NPSPACE enc := by
  intro A hA
  obtain ⟨t, ht, k, State, hfinite, ntm, hdec⟩ := decidableInPolyTime_of_mem_NP hA
  exact ⟨k, State, hfinite, ntm, fun a => k * (t a + 1), (PolyBounded.const k).mul
    (ht.add (.const 1)), hdec.decidesInSpace⟩

/-- **`NP ⊆ PSPACE`** [Arora and Barak, Theorem 4.2][AroraBarak09]: `NP ⊆ NPSPACE`, and
`NPSPACE = PSPACE` by Savitch's theorem. -/
theorem NP_subset_PSPACE : NP enc ⊆ PSPACE enc :=
  NP_subset_NPSPACE.trans NPSPACE_subset_PSPACE

/-- A polynomial plus `2` to a polynomial times a polynomial is eventually below `2 ^ n ^ K`. -/
private theorem exists_eventually_le_two_pow_pow {P Q R : ℕ → ℕ} (hP : PolynomiallyBounded P)
    (hQ : PolynomiallyBounded Q) (hR : PolynomiallyBounded R) :
    ∃ K, ∀ᶠ n in atTop, P n + 2 ^ Q n * R n ≤ 2 ^ n ^ K := by
  obtain ⟨K, hK⟩ : PolynomiallyBounded fun n => Q n + n + 1 := by fun_prop
  refine ⟨K, ?_⟩
  filter_upwards [hP.eventually_lt_two_pow, hR.eventually_lt_two_pow, hK] with n h₁ h₂ h₃
  have h₄ : 1 ≤ 2 ^ Q n := Nat.one_le_two_pow
  calc P n + 2 ^ Q n * R n ≤ 2 ^ n * 2 ^ Q n + 2 ^ Q n * 2 ^ n :=
        Nat.add_le_add (h₁.le.trans (Nat.le_mul_of_pos_right _ h₄))
          (Nat.mul_le_mul_left _ h₂.le)
    _ = 2 ^ (Q n + n + 1) := by ring
    _ ≤ 2 ^ n ^ K := Nat.pow_le_pow_right (by norm_num) h₃

/-- **`PSPACE ⊆ EXP`** [Arora and Barak, Theorem 4.2][AroraBarak09],
[Sipser, Section 8.2][Sipser2013]: a decider within space `n ^ k` halts within its number of
configurations, `(n + 2) * 2 ^ (c * n ^ k)` (`Cslib.Complexity.exists_mem_DTIME_of_mem_DSPACE`). -/
theorem PSPACE_subset_EXP : PSPACE enc ⊆ EXP enc := by
  intro A hA
  obtain ⟨k, hk⟩ := mem_PSPACE_iff_exists_mem_DSPACE.mp hA
  obtain ⟨c, hc⟩ := exists_mem_DTIME_of_mem_DSPACE hk
  obtain ⟨K, hK⟩ := exists_eventually_le_two_pow_pow (P := fun _ => 0) (Q := fun n => c * n ^ k)
    (R := fun n => n + 2) (by fun_prop) (by fun_prop) (by fun_prop)
  exact mem_EXP_iff.mpr ⟨K, DTIME_mono_of_eventually_le
    (hK.mono fun n hn => by rw [Nat.mul_comm]; simpa using hn) hc⟩

/-- **`NP ⊆ EXP`**, through `PSPACE`. -/
theorem NP_subset_EXP : NP enc ⊆ EXP enc :=
  NP_subset_PSPACE.trans PSPACE_subset_EXP

/-! ### The polynomial hierarchy -/

/-- The pairs `(a, u)` from which alternating quantifiers over blocks of certificates of the
lengths `ps`, starting with `∃` if `q` is `true`, lead to `V (a, u ++ w) = true`. -/
private def alternationSet (enc : α ↪ List Bool) (q : Bool) (ps : List (Polynomial ℕ))
    (V : α × List Bool → Bool) : Set (α × List Bool) :=
  {x | Alternation q (ps.map fun p => p.eval (enc x.1).length) fun w => V (x.1, x.2 ++ w) = true}

/-- Alternating quantifiers over a polynomial-time verifier are decided in polynomial space, one
quantifier at a time: an existential block by `Cslib.Complexity.setOf_exists_mem_PSPACE`, a
universal block as the complement of an existential block for the negated verifier. -/
private theorem alternationSet_mem_PSPACE (ps : List (Polynomial ℕ)) :
    ∀ (q : Bool) (V : α × List Bool → Bool),
      ComputableInPolyTime V (encPair enc encBits) encBool →
        alternationSet enc q ps V ∈ PSPACE (encPair enc encBits) := by
  induction ps with
  | nil =>
    intro q V hV
    exact P_subset_PSPACE ⟨V, hV, fun x => by simp [alternationSet]⟩
  | cons p ps ih =>
    have hex (V : α × List Bool → Bool)
        (hV : ComputableInPolyTime V (encPair enc encBits) encBool) :
        alternationSet enc true (p :: ps) V ∈ PSPACE (encPair enc encBits) := by
      -- the remaining quantifiers, after the first block of certificates
      have hB := (polyTimeReducible_append (alternationSet enc false ps V)).mem_PSPACE
        (ih false V hV)
      have hℓ : ComputableInPolyTime (fun x : α × List Bool => p.eval (enc x.1).length)
          (encPair enc encBits) encUnary :=
        ((ComputableInPolyTime.unary_eval p).comp
          (ComputableInPolyTime.encoding_length enc)).comp (.fst _ _)
      convert setOf_exists_mem_PSPACE hB (hℓ) using 1
      ext x
      simp only [alternationSet, List.map_cons, alternation_true_cons, Set.mem_ofPred_eq,
        List.append_assoc]
    intro q V hV
    cases q
    · -- a universal block is the complement of an existential block
      convert compl_mem_PSPACE (hex (fun x => !V x) (ComputableInPolyTime.bool_not.comp hV))
        using 1
      ext x
      simp only [alternationSet, Set.mem_ofPred_eq, Set.mem_compl_iff, not_alternation,
        Bool.not_true]
      exact alternation_congr fun w => by simp
    · exact hex V hV

/-- **Every level of the polynomial hierarchy is within `PSPACE`.** -/
theorem SigmaP_subset_PSPACE (k : ℕ) : SigmaP k enc ⊆ PSPACE enc := by
  rintro A ⟨ps, V, -, hV, hA⟩
  refine PolyTimeReducible.mem_PSPACE ⟨fun a => (a, []),
    ComputableInPolyTime.id'.prod (.const []), fun a => ?_⟩
    (alternationSet_mem_PSPACE ps true V hV)
  simp [alternationSet, hA a]

/-- **`PH ⊆ PSPACE`** [Arora and Barak, Chapter 5][AroraBarak09],
[Stockmeyer][Stockmeyer1976]: the quantifiers of a level of the hierarchy are evaluated one at a
time, reusing the space for every certificate. -/
theorem PH_subset_PSPACE : PH enc ⊆ PSPACE enc :=
  Set.iUnion_subset SigmaP_subset_PSPACE

/-- **Every level of the polynomial hierarchy lies in `EXP`**, via `Σₖ ⊆ PSPACE ⊆ EXP`. -/
theorem SigmaP_subset_EXP (k : ℕ) : SigmaP k enc ⊆ EXP enc :=
  (SigmaP_subset_PSPACE k).trans PSPACE_subset_EXP

/-- **Every level of the polynomial hierarchy lies in `NEXP`**, via `Σₖ ⊆ EXP ⊆ NEXP`. -/
theorem SigmaP_subset_NEXP (k : ℕ) : SigmaP k enc ⊆ NEXP enc :=
  (SigmaP_subset_EXP k).trans EXP_subset_NEXP

end Cslib.Complexity
