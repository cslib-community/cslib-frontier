/-
Copyright (c) 2026 Matthew Doty, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Kolmogorov.ConditionalPartrec
public import CslibFrontier.Computability.Kolmogorov.LevinCoding
import CslibFrontier.Foundations.Data.List.FoldMax
import CslibFrontier.Foundations.Data.List.Primrec
import Mathlib.Computability.Primrec.List

/-!
# Conditional prefix-free complexity and exact symmetry of information

This file develops **conditional prefix-free Kolmogorov complexity** `K(y | x)` over
`condUniversalPrefix : ℕ → DescriptionMethod ℕ` and **exact symmetry of information**
[LiVitanyi2019, ShenUspenskyVereshchagin2017], avoiding the `O(log C)` loss present in plain
Kolmogorov complexity (`CslibFrontier.Computability.Kolmogorov.SymmetryOfInformation`).

* **Conditional prefix-free invariance**: `condUniversalPrefix y` parses `codeHeader c ++ p` and
  runs `p` under `ofPrefixCode (c.curry y)`. It is uniformly partial recursive (`IsCondPartrec`),
  prefix-free for every condition `y`, and additively optimal among all partial recursive
  prefix-free conditional methods (`exists_ecomplexity_condUniversalPrefix_le_of_partrec₂`).
* **Prefix-free chain rule**: concatenating a prefix-free program for `x` with a conditional
  prefix-free program for `y` given `x` requires no extra separator overhead, giving
  `K(x, y) ≤ K(x) + K(y | x) + O(1)` (`exists_complexity_universalPrefix_pair_le_add`).
* **Uniform conditional Kraft–Chaitin**: every uniformly computable family of conditional request
  streams `req : ℕ → ℕ → Option (ℕ × ℕ)` with Kraft sum at most `1` for every condition `y` yields
  a single uniform constant `c` with `K(z | y) ≤ ℓ + c` (`condKraftChaitin_of_sum_le_one`).
* **Shortest programs and exact symmetry of information**: defining `shortestPrefixProgram x` (`x*`,
  the earliest halting prefix-free program of minimal length `K(x)` for `x`), we prove condition
  equivalence `|K(y | x, K(x)) - K(y | x*)| ≤ O(1)`
  (`exists_abs_complexity_condUniversalPrefix_pair_sub_shortestPrefixProgram_le`) and apply
  Levin's coding bound to the marginal semimeasure `x ↦ ∑' y, m(Nat.pair x y)` to obtain exact
  symmetry of information for both `ℕ` and `List Bool`:
  - `|K(x, y) - K(x) - K(y | x, K(x))| ≤ O(1)`,
  - `|K(x, y) - K(x) - K(y | x*)| ≤ O(1)`, and
  - `|I_K(x : y) - I_K(y : x)| ≤ O(1)` (`exists_abs_prefixInformation_symm`).

## Main definitions

* `Cslib.Kolmogorov.DescriptionMethod.condUniversalPrefix`: conditional universal prefix-free
  description method on `ℕ`.
* `Cslib.Kolmogorov.DescriptionMethod.condUniversalPrefixBits`: binary-string version on
  `List Bool`.
* `Cslib.Kolmogorov.DescriptionMethod.shortestPrefixProgram`: canonical shortest prefix-free
  program `x*` for `x : ℕ`.
* `Cslib.Kolmogorov.DescriptionMethod.shortestPrefixProgramBits`: canonical shortest prefix-free
  program `x*` for `x : List Bool`.
* `Cslib.Kolmogorov.prefixInformation`: prefix algorithmic mutual information
  `I_K(x : y) = K(y) - K(y | x*)`.

## Main results

* `Cslib.Kolmogorov.DescriptionMethod.isPrefixFree_condUniversalPrefix`,
  `Cslib.Kolmogorov.DescriptionMethod.isCondPartrec_condUniversalPrefix`,
  `Cslib.Kolmogorov.DescriptionMethod.exists_ecomplexity_condUniversalPrefix_le_of_partrec₂`:
  uniform conditional prefix-free invariance.
* `Cslib.Kolmogorov.DescriptionMethod.condKraftChaitin_of_sum_le_one`: uniform conditional
  Kraft–Chaitin theorem.
* `Cslib.Kolmogorov.DescriptionMethod.exists_complexity_universalPrefix_pair_le_add`,
  `Cslib.Kolmogorov.DescriptionMethod.exists_complexity_universalPrefix_pair_le_add_pair`:
  prefix-free chain rules `K(x, y) ≤ K(x) + K(y | x) + O(1)` and
  `K(x, y) ≤ K(x) + K(y | x, K(x)) + O(1)`.
* `exists_abs_complexity_condUniversalPrefix_pair_sub_shortestPrefixProgram_le`:
  inter-convertibility `|K(y | x, K(x)) - K(y | x*)| ≤ O(1)`.
* `Cslib.Kolmogorov.DescriptionMethod.exists_abs_complexity_universalPrefix_pair_sub_le`,
  `exists_abs_complexity_universalPrefix_pair_sub_shortestProgram_le`,
  `exists_abs_complexity_universalPrefixBits_pair_sub_shortestProgram_le`:
  **exact symmetry of information** for prefix-free complexity.
* `Cslib.Kolmogorov.exists_prefixInformation_ge`,
  `Cslib.Kolmogorov.exists_abs_prefixInformation_sub_le`,
  `Cslib.Kolmogorov.exists_abs_prefixInformation_symm`: exact symmetry of algorithmic mutual
  information.

## References

* [M. Li, P. Vitányi, *An Introduction to Kolmogorov Complexity and Its
  Applications*][LiVitanyi2019]
* [A. Shen, V. A. Uspensky, N. Vereshchagin, *Kolmogorov Complexity and Algorithmic
  Randomness*][ShenUspenskyVereshchagin2017]
-/

public section

open scoped BigOperators Filter Topology

namespace Cslib.Kolmogorov

open Encodable Denumerable Nat.Partrec

namespace DescriptionMethod

/-! ### Conditional prefix-free universal description method -/

/-- The *conditional universal prefix-free* description method given `y : ℕ`: `parseCodeHeader`
strictly parses `codeHeader c ++ p`, and then runs `p` under `ofPrefixCode (c.curry y)`. -/
def condUniversalPrefix (y : ℕ) : DescriptionMethod ℕ where
  run q := match parseCodeHeader q with
    | Option.none => Computation.empty ℕ
    | some (c, p) => (ofPrefixCode (c.curry y)).run p

@[simp]
theorem condUniversalPrefix_run_codeHeader_append (y : ℕ) (c : Code) (p : List Bool) :
    (condUniversalPrefix y).run (codeHeader c ++ p) = (ofPrefixCode (c.curry y)).run p := by
  simp [condUniversalPrefix, parseCodeHeader_codeHeader_append]

theorem condUniversalPrefix_produces_iff {y : ℕ} {q : List Bool} {x : ℕ} :
    (condUniversalPrefix y).Produces q x ↔
      ∃ c p, parseCodeHeader q = some (c, p) ∧ (ofPrefixCode (c.curry y)).Produces p x := by
  simp only [Produces, condUniversalPrefix]
  cases h : parseCodeHeader q with
  | none =>
    simp only [Computation.notMem_empty, false_iff, not_exists, not_and]
    intro c p hc
    cases hc
  | some cp =>
    rcases cp with ⟨c, p⟩
    simp

theorem condUniversalPrefix_produces_codeHeader_append {y : ℕ} {c : Code} {p : List Bool}
    {x : ℕ} :
    (condUniversalPrefix y).Produces (codeHeader c ++ p) x ↔
      (ofPrefixCode (c.curry y)).Produces p x := by
  rw [Produces, condUniversalPrefix_run_codeHeader_append, Produces]

/-- For every condition `y`, `condUniversalPrefix y` is prefix-free. -/
theorem isPrefixFree_condUniversalPrefix (y : ℕ) : (condUniversalPrefix y).IsPrefixFree := by
  rintro q₁ ⟨x₁, h₁⟩ q₂ ⟨x₂, h₂⟩ hpref
  obtain ⟨c₁, p₁, hp₁, hprod₁⟩ := condUniversalPrefix_produces_iff.mp h₁
  obtain ⟨c₂, p₂, hp₂, hprod₂⟩ := condUniversalPrefix_produces_iff.mp h₂
  obtain ⟨rfl, hp'⟩ := prefix_of_parseCodeHeader_eq_some hp₁ hp₂ hpref
  have hpeq := isPrefixFree_ofPrefixCode (c₁.curry y) p₁ ⟨x₁, hprod₁⟩ p₂ ⟨x₂, hprod₂⟩ hp'
  rw [← (parseCodeHeader_eq_some_iff.mp hp₁), ← (parseCodeHeader_eq_some_iff.mp hp₂), hpeq]

private theorem primrec_condUniversalPrefixStep :
    Primrec fun arg : (ℕ × List Bool) × ℕ =>
      (parseCodeHeader arg.1.2).bind fun cp =>
        (prefixAccepted (cp.1.curry arg.1.1) arg.2).lookup cp.2 := by
  have hc : Primrec fun arg : ((ℕ × List Bool) × ℕ) × (Code × List Bool) =>
      (arg.2.1.curry arg.1.1.1, arg.2.2) :=
    Primrec.pair
      (Code.primrec₂_curry.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp Primrec.snd)
  exact Primrec.option_bind (primrec_parseCodeHeader.comp (Primrec.snd.comp Primrec.fst))
    (primrec₂_prefixAccepted_lookup.comp hc (Primrec.snd.comp Primrec.fst)).to₂

/-- Joint partial recursive evaluation of `condUniversalPrefix` in `(y, q)`. -/
theorem partrec₂_condUniversalPrefix_eval :
    Partrec₂ fun (y : ℕ) (q : List Bool) =>
      Nat.rfindOpt fun n =>
        (parseCodeHeader q).bind fun cp => (prefixAccepted (cp.1.curry y) n).lookup cp.2 :=
  Partrec.rfindOpt primrec_condUniversalPrefixStep.to_comp

theorem isCondPartrec_condUniversalPrefix : IsCondPartrec condUniversalPrefix := by
  refine ⟨_, partrec₂_condUniversalPrefix_eval, fun y q x => ?_⟩
  rw [condUniversalPrefix_produces_iff]
  have hmono : ∀ {z m n : ℕ}, m ≤ n →
      z ∈ ((parseCodeHeader q).bind fun cp => (prefixAccepted (cp.1.curry y) m).lookup cp.2) →
      z ∈ ((parseCodeHeader q).bind fun cp => (prefixAccepted (cp.1.curry y) n).lookup cp.2) := by
    intro z m n hmn hz
    simp only [Option.mem_def, Option.bind_eq_some_iff] at hz ⊢
    obtain ⟨cp, hcp, hlook⟩ := hz
    exact ⟨cp, hcp, lookup_prefixAccepted_mono hmn hlook⟩
  rw [Nat.rfindOpt_mono hmono]
  constructor
  · rintro ⟨c, p, hp, hprod⟩
    obtain ⟨n, hn⟩ := ofPrefixCode_produces_iff.mp hprod
    refine ⟨n, ?_⟩
    simp only [hp, Option.bind_some, Option.mem_def]
    exact mem_prefixAccepted_iff_lookup.mp hn
  · rintro ⟨n, hn⟩
    simp only [Option.mem_def, Option.bind_eq_some_iff] at hn
    obtain ⟨⟨c, p⟩, hp, hlook⟩ := hn
    exact ⟨c, p, hp, ofPrefixCode_produces_iff.mpr ⟨n, mem_prefixAccepted_iff_lookup.mpr hlook⟩⟩

/-- **Uniform conditional prefix-free invariance** for partial recursive decoders: if `f y p` is
jointly partial recursive and prefix-free in `p` for every `y`, then `K(x | y) ≤ |p| + c`
for a uniform constant `c`. -/
theorem exists_ecomplexity_condUniversalPrefix_le_of_partrec₂ {f : ℕ → List Bool →. ℕ}
    (hf : Partrec₂ f) (hpf : ∀ y : ℕ, InformationTheory.IsPrefixFree {p | (f y p).Dom}) :
    ∃ c : ℕ, ∀ y q x, x ∈ f y q → (condUniversalPrefix y).ecomplexity x ≤ q.length + c := by
  obtain ⟨c, hc⟩ := Code.exists_code.mp hf
  refine ⟨(codeHeader c).length, fun y q x hx => ?_⟩
  have hcode_pf : (ofCode (c.curry y)).IsPrefixFree := by
    rintro p₁ ⟨x₁, h₁⟩ p₂ ⟨x₂, h₂⟩ hp
    rw [ofCode_produces_iff, Code.eval_curry, hc] at h₁ h₂
    have h₁' : (f y p₁).Dom := Part.dom_iff_mem.mpr ⟨x₁, by simpa using h₁⟩
    have h₂' : (f y p₂).Dom := Part.dom_iff_mem.mpr ⟨x₂, by simpa using h₂⟩
    exact hpf y p₁ h₁' p₂ h₂' hp
  have hprod : (ofCode (c.curry y)).Produces q x := by
    rw [ofCode_produces_iff, Code.eval_curry, hc]
    simpa using hx
  have hcond : (condUniversalPrefix y).Produces (codeHeader c ++ q) x :=
    condUniversalPrefix_produces_codeHeader_append.mpr
      ((ofPrefixCode_produces_iff_of_isPrefixFree hcode_pf).mpr hprod)
  exact (ecomplexity_le_length hcond).trans (by rw [List.length_append, Nat.cast_add, add_comm])

/-- Conditional prefix-free invariance for conditional description methods. -/
theorem IsCondPartrec.exists_ecomplexity_condUniversalPrefix_le
    {N : ℕ → DescriptionMethod ℕ} (hN : IsCondPartrec N) (hpf : ∀ y, (N y).IsPrefixFree) :
    ∃ c : ℕ, ∀ y x, (condUniversalPrefix y).ecomplexity x ≤ (N y).ecomplexity x + c := by
  obtain ⟨f, hf, hN_eq⟩ := hN
  have hf_pf : ∀ y, InformationTheory.IsPrefixFree {p | (f y p).Dom} := by
    intro y p₁ h₁ p₂ h₂ hp
    obtain ⟨x₁, hx₁⟩ := Part.dom_iff_mem.mp h₁
    obtain ⟨x₂, hx₂⟩ := Part.dom_iff_mem.mp h₂
    exact hpf y p₁ ⟨x₁, (hN_eq y p₁ x₁).mpr hx₁⟩ p₂ ⟨x₂, (hN_eq y p₂ x₂).mpr hx₂⟩ hp
  obtain ⟨c, hc⟩ := exists_ecomplexity_condUniversalPrefix_le_of_partrec₂ hf hf_pf
  refine ⟨c, fun y x => ?_⟩
  by_cases h : (N y).ecomplexity x = ⊤
  · simp [h]
  obtain ⟨p, hp, hlen⟩ := exists_length_eq_ecomplexity h
  rw [← hlen]
  exact hc y p x ((hN_eq y p x).mp hp)

/-- Dropping a condition cannot decrease prefix-free complexity by more than a constant:
`K(x | y) ≤ K(x) + O(1)`. -/
theorem exists_ecomplexity_condUniversalPrefix_le :
    ∃ c : ℕ, ∀ y x, (condUniversalPrefix y).ecomplexity x ≤ universalPrefix.ecomplexity x + c := by
  obtain ⟨f, hf, hU⟩ := isPartrec_universalPrefix
  have hpf : ∀ _ : ℕ, InformationTheory.IsPrefixFree {p | (f p).Dom} := by
    intro _ p₁ h₁ p₂ h₂ hp
    obtain ⟨x₁, hx₁⟩ := Part.dom_iff_mem.mp h₁
    obtain ⟨x₂, hx₂⟩ := Part.dom_iff_mem.mp h₂
    exact isPrefixFree_universalPrefix p₁ ⟨x₁, (hU p₁ x₁).mpr hx₁⟩
      p₂ ⟨x₂, (hU p₂ x₂).mpr hx₂⟩ hp
  obtain ⟨c, hc⟩ := exists_ecomplexity_condUniversalPrefix_le_of_partrec₂
    (f := fun _ q => f q) (hf.comp Computable.snd) hpf
  refine ⟨c, fun y x => ?_⟩
  obtain ⟨p, hp, hlen⟩ := exists_length_eq_ecomplexity (ecomplexity_universalPrefix_ne_top x)
  rw [← hlen]
  exact hc y p x ((hU p x).mp hp)

/-- Every natural number has finite complexity under `condUniversalPrefix y`. -/
theorem ecomplexity_condUniversalPrefix_ne_top (y x : ℕ) :
    (condUniversalPrefix y).ecomplexity x ≠ ⊤ := by
  obtain ⟨c, hc⟩ := exists_ecomplexity_condUniversalPrefix_le
  exact ne_top_of_le_ne_top
    (WithTop.add_ne_top.mpr ⟨ecomplexity_universalPrefix_ne_top x, ENat.natCast_ne_top c⟩)
    (hc y x)

@[simp]
theorem natCast_complexity_condUniversalPrefix (y x : ℕ) :
    ((condUniversalPrefix y).complexity x : ℕ∞) = (condUniversalPrefix y).ecomplexity x :=
  natCast_complexity (ecomplexity_condUniversalPrefix_ne_top y x)

/-- Dropping a condition bound in `ℕ`: `K(x | y) ≤ K(x) + c`. -/
theorem exists_complexity_condUniversalPrefix_le :
    ∃ c : ℕ, ∀ y x, (condUniversalPrefix y).complexity x ≤ universalPrefix.complexity x + c := by
  obtain ⟨c, hc⟩ := exists_ecomplexity_condUniversalPrefix_le
  refine ⟨c, fun y x => ?_⟩
  have h := hc y x
  rw [← natCast_complexity_universalPrefix, ← natCast_complexity_condUniversalPrefix] at h
  exact_mod_cast h

/-- Self-complexity bound: `K(y | y) ≤ c`. -/
theorem exists_complexity_condUniversalPrefix_self_le :
    ∃ c : ℕ, ∀ y : ℕ, (condUniversalPrefix y).complexity y ≤ c := by
  let f : ℕ → List Bool →. ℕ := fun y q =>
    Nat.rfindOpt fun (_ : ℕ) => if q = [] then some y else Option.none
  have hstep : Primrec fun arg : (ℕ × List Bool) × ℕ =>
      if arg.1.2 = [] then some arg.1.1 else Option.none :=
    Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.fst) (Primrec.const []))
      (Primrec.option_some.comp (Primrec.fst.comp Primrec.fst)) (Primrec.const Option.none)
  have hf : Partrec₂ f := Partrec.rfindOpt hstep.to_comp
  have hpf : ∀ y : ℕ, InformationTheory.IsPrefixFree {q | (f y q).Dom} := by
    intro y q₁ h₁ q₂ h₂ _
    obtain ⟨_, hm₁⟩ := Part.dom_iff_mem.mp h₁
    obtain ⟨_, hm₂⟩ := Part.dom_iff_mem.mp h₂
    obtain ⟨_, hk₁⟩ := Nat.rfindOpt_spec hm₁
    obtain ⟨_, hk₂⟩ := Nat.rfindOpt_spec hm₂
    split_ifs at hk₁ with hq₁
    · split_ifs at hk₂ with hq₂
      · exact hq₁.trans hq₂.symm
      · cases hk₂
    · cases hk₁
  obtain ⟨c, hc⟩ := exists_ecomplexity_condUniversalPrefix_le_of_partrec₂ hf hpf
  refine ⟨c, fun y => ?_⟩
  have hy : y ∈ f y [] := Nat.rfindOpt_mono (fun _ h => h) |>.mpr ⟨0, by simp⟩
  have h := hc y [] y hy
  rw [← natCast_complexity_condUniversalPrefix, List.length_nil, Nat.cast_zero, zero_add] at h
  exact_mod_cast h

private theorem exists_complexity_universalPrefix_bind_le {f : ℕ →. ℕ} (hf : Partrec f) :
    ∃ c : ℕ, ∀ x y : ℕ, y ∈ f x →
      universalPrefix.complexity y ≤ universalPrefix.complexity x + c := by
  obtain ⟨eval, heval, hU⟩ := isPartrec_universalPrefix
  let g : List Bool →. ℕ := fun q => (eval q).bind f
  have hg : Partrec g := Partrec.bind heval (hf.comp Computable.snd)
  have hpf : InformationTheory.IsPrefixFree {q | (g q).Dom} := by
    rintro q₁ h₁ q₂ h₂ hp
    obtain ⟨y₁, hy₁⟩ := Part.dom_iff_mem.mp h₁
    obtain ⟨y₂, hy₂⟩ := Part.dom_iff_mem.mp h₂
    obtain ⟨x₁, hx₁, -⟩ := Part.mem_bind_iff.mp hy₁
    obtain ⟨x₂, hx₂, -⟩ := Part.mem_bind_iff.mp hy₂
    exact isPrefixFree_universalPrefix q₁ ⟨x₁, (hU q₁ x₁).mpr hx₁⟩
      q₂ ⟨x₂, (hU q₂ x₂).mpr hx₂⟩ hp
  obtain ⟨c, hc⟩ := minorizesPrefixPartrec_universalPrefix g hg hpf
  refine ⟨c, fun x y hy => ?_⟩
  obtain ⟨p, hp, hlen⟩ := exists_length_eq_ecomplexity (ecomplexity_universalPrefix_ne_top x)
  have hpx := hc p y (Part.mem_bind_iff.mpr ⟨x, (hU p x).mp hp, hy⟩)
  rw [hlen, ← natCast_complexity_universalPrefix, ← natCast_complexity_universalPrefix] at hpx
  exact_mod_cast hpx

/-- Computing a computable transformation `φ : ℕ → ℕ` increases prefix-free complexity by at most
a constant: `K(φ x) ≤ K(x) + c`. -/
theorem exists_complexity_universalPrefix_comp_le {φ : ℕ → ℕ} (hφ : Computable φ) :
    ∃ c : ℕ, ∀ x : ℕ, universalPrefix.complexity (φ x) ≤ universalPrefix.complexity x + c := by
  obtain ⟨c, hc⟩ := exists_complexity_universalPrefix_bind_le (Partrec.some.comp hφ)
  exact ⟨c, fun x => hc x (φ x) (Part.mem_some _)⟩

/-- Condition-transformation lemma: if a partial recursive function `g : ℕ →. ℕ` maps condition
`y` to condition `x`, then `K(z | y) ≤ K(z | x) + c` uniformly in `y, x, z`. -/
theorem exists_complexity_condUniversalPrefix_le_of_partrec_map {g : ℕ →. ℕ} (hg : Partrec g) :
    ∃ c : ℕ, ∀ y x z, x ∈ g y →
      (condUniversalPrefix y).complexity z ≤ (condUniversalPrefix x).complexity z + c := by
  obtain ⟨evalC, hevalC, hC⟩ := isCondPartrec_condUniversalPrefix
  let f : ℕ → List Bool →. ℕ := fun y q => (g y).bind fun x => evalC x q
  have hf : Partrec₂ f :=
    Partrec.bind (hg.comp Computable.fst)
      (hevalC.comp Computable.snd (Computable.snd.comp Computable.fst))
  have hpf : ∀ y : ℕ, InformationTheory.IsPrefixFree {q | (f y q).Dom} := by
    intro y q₁ h₁ q₂ h₂ hpref
    obtain ⟨z₁, hz₁⟩ := Part.dom_iff_mem.mp h₁
    obtain ⟨z₂, hz₂⟩ := Part.dom_iff_mem.mp h₂
    obtain ⟨x₁, hx₁, hq₁⟩ := Part.mem_bind_iff.mp hz₁
    obtain ⟨x₂, hx₂, hq₂⟩ := Part.mem_bind_iff.mp hz₂
    obtain rfl := Part.mem_unique hx₁ hx₂
    exact isPrefixFree_condUniversalPrefix x₁ q₁ ⟨z₁, (hC x₁ q₁ z₁).mpr hq₁⟩
      q₂ ⟨z₂, (hC x₁ q₂ z₂).mpr hq₂⟩ hpref
  obtain ⟨c, hc⟩ := exists_ecomplexity_condUniversalPrefix_le_of_partrec₂ hf hpf
  refine ⟨c, fun y x z hx => ?_⟩
  obtain ⟨q, hq, hlen⟩ := exists_length_eq_ecomplexity (ecomplexity_condUniversalPrefix_ne_top x z)
  have hf_mem : z ∈ f y q := Part.mem_bind_iff.mpr ⟨x, hx, (hC x q z).mp hq⟩
  have h := hc y q z hf_mem
  rw [hlen, ← natCast_complexity_condUniversalPrefix, ← natCast_complexity_condUniversalPrefix]
    at h
  exact_mod_cast h

/-- Conditional computable postprocessing: `K(φ y z | y) ≤ K(z | y) + c`. -/
theorem exists_complexity_condUniversalPrefix_comp_le {φ : ℕ → ℕ → ℕ} (hφ : Computable₂ φ) :
    ∃ c : ℕ, ∀ y z : ℕ,
      (condUniversalPrefix y).complexity (φ y z) ≤ (condUniversalPrefix y).complexity z + c := by
  obtain ⟨evalC, hevalC, hC⟩ := isCondPartrec_condUniversalPrefix
  let f : ℕ → List Bool →. ℕ := fun y q => (evalC y q).map (φ y)
  have hf : Partrec₂ f :=
    hevalC.map (hφ.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂
  have hpf : ∀ y : ℕ, InformationTheory.IsPrefixFree {q | (f y q).Dom} := by
    intro y q₁ h₁ q₂ h₂ hpref
    obtain ⟨w₁, hw₁⟩ := Part.dom_iff_mem.mp h₁
    obtain ⟨w₂, hw₂⟩ := Part.dom_iff_mem.mp h₂
    obtain ⟨z₁, hz₁, -⟩ := (Part.mem_map_iff _).mp hw₁
    obtain ⟨z₂, hz₂, -⟩ := (Part.mem_map_iff _).mp hw₂
    exact isPrefixFree_condUniversalPrefix y q₁ ⟨z₁, (hC y q₁ z₁).mpr hz₁⟩
      q₂ ⟨z₂, (hC y q₂ z₂).mpr hz₂⟩ hpref
  obtain ⟨c, hc⟩ := exists_ecomplexity_condUniversalPrefix_le_of_partrec₂ hf hpf
  refine ⟨c, fun y z => ?_⟩
  obtain ⟨q, hq, hlen⟩ := exists_length_eq_ecomplexity (ecomplexity_condUniversalPrefix_ne_top y z)
  have h := hc y q (φ y z) (Part.mem_map (φ y) ((hC y q z).mp hq))
  rw [hlen, ← natCast_complexity_condUniversalPrefix, ← natCast_complexity_condUniversalPrefix]
    at h
  exact_mod_cast h

/-- Binary-string conditional universal prefix-free description method. -/
@[expose] noncomputable def condUniversalPrefixBits (y : List Bool) :
    DescriptionMethod (List Bool) :=
  (condUniversalPrefix (encode y)).map fun n => (decode (α := List Bool) n).getD []

theorem isPrefixFree_condUniversalPrefixBits (y : List Bool) :
    (condUniversalPrefixBits y).IsPrefixFree :=
  (isPrefixFree_condUniversalPrefix (encode y)).map _

private theorem ecomplexity_condUniversalPrefixBits_le_encode (y x : List Bool) :
    (condUniversalPrefixBits y).ecomplexity x ≤
      (condUniversalPrefix (encode y)).ecomplexity (encode x) := by
  simpa [condUniversalPrefixBits, encodek] using
    (condUniversalPrefix (encode y)).ecomplexity_map_le
      (fun n => (decode (α := List Bool) n).getD []) (encode x)

theorem ecomplexity_condUniversalPrefixBits_ne_top (y x : List Bool) :
    (condUniversalPrefixBits y).ecomplexity x ≠ ⊤ :=
  ne_top_of_le_ne_top (ecomplexity_condUniversalPrefix_ne_top (encode y) (encode x))
    (ecomplexity_condUniversalPrefixBits_le_encode y x)

@[simp]
theorem natCast_complexity_condUniversalPrefixBits (y x : List Bool) :
    ((condUniversalPrefixBits y).complexity x : ℕ∞) =
      (condUniversalPrefixBits y).ecomplexity x :=
  natCast_complexity (ecomplexity_condUniversalPrefixBits_ne_top y x)

private theorem exists_complexity_universalPrefix_comp_universalPrefixBits_le
    {ψ : List Bool → ℕ} (hψ : Computable ψ) :
    ∃ c : ℕ, ∀ x : List Bool,
      universalPrefix.complexity (ψ x) ≤ universalPrefixBits.complexity x + c := by
  obtain ⟨f, hf, hU⟩ := isPartrec_universalPrefix
  let φ : ℕ → ℕ := fun n => ψ ((decode (α := List Bool) n).getD [])
  have hφ : Computable φ :=
    hψ.comp (Computable.option_getD Computable.decode (Computable.const ([] : List Bool)))
  let g : List Bool →. ℕ := fun q => (f q).map φ
  have hg : Partrec g := hf.map (hφ.comp Computable.snd).to₂
  have hpf : InformationTheory.IsPrefixFree {q | (g q).Dom} := by
    rintro q₁ h₁ q₂ h₂ hp
    obtain ⟨x₁, hx₁⟩ := Part.dom_iff_mem.mp h₁
    obtain ⟨x₂, hx₂⟩ := Part.dom_iff_mem.mp h₂
    obtain ⟨n₁, hn₁, -⟩ := (Part.mem_map_iff _).mp hx₁
    obtain ⟨n₂, hn₂, -⟩ := (Part.mem_map_iff _).mp hx₂
    exact isPrefixFree_universalPrefix q₁ ⟨n₁, (hU q₁ n₁).mpr hn₁⟩
      q₂ ⟨n₂, (hU q₂ n₂).mpr hn₂⟩ hp
  obtain ⟨c, hc⟩ := minorizesPrefixPartrec_universalPrefix g hg hpf
  refine ⟨c, fun x => ?_⟩
  obtain ⟨p, hp, hlen⟩ := exists_length_eq_ecomplexity (ecomplexity_universalPrefixBits_ne_top x)
  rw [universalPrefixBits, map_produces_iff] at hp
  obtain ⟨n, hpn, hnx⟩ := hp
  have hmem : ψ x ∈ g p := (Part.mem_map_iff _).mpr ⟨n, (hU p n).mp hpn, congrArg ψ hnx⟩
  have h := hc p (ψ x) hmem
  rw [hlen, ← natCast_complexity_universalPrefixBits, ← natCast_complexity_universalPrefix] at h
  exact_mod_cast h

private theorem exists_complexity_bits_encode_le_universalPrefixBits :
    ∃ c : ℕ, ∀ x : List Bool,
      universalPrefix.complexity (encode x) ≤ universalPrefixBits.complexity x + c :=
  exists_complexity_universalPrefix_comp_universalPrefixBits_le Primrec.encode.to_comp

private theorem complexity_universalPrefixBits_le_encode (x : List Bool) :
    universalPrefixBits.complexity x ≤ universalPrefix.complexity (encode x) := by
  have hle : universalPrefixBits.ecomplexity x ≤ universalPrefix.ecomplexity (encode x) := by
    simpa [universalPrefixBits, encodek] using
      universalPrefix.ecomplexity_map_le (fun n => (decode (α := List Bool) n).getD []) (encode x)
  rw [← natCast_complexity_universalPrefixBits, ← natCast_complexity_universalPrefix] at hle
  exact_mod_cast hle

private theorem exists_complexity_condBits_encode_le_condUniversalPrefixBits :
    ∃ c : ℕ, ∀ y x : List Bool,
      (condUniversalPrefix (encode y)).complexity (encode x) ≤
        (condUniversalPrefixBits y).complexity x + c := by
  obtain ⟨evalC, hevalC, hC⟩ := isCondPartrec_condUniversalPrefix
  let decEnc : ℕ → ℕ := fun n => encode ((decode (α := List Bool) n).getD [])
  have hdecEnc : Computable decEnc :=
    Primrec.encode.to_comp.comp
      (Computable.option_getD Computable.decode (Computable.const ([] : List Bool)))
  let f : ℕ → List Bool →. ℕ := fun m q => (evalC m q).map decEnc
  have hf : Partrec₂ f := hevalC.map (hdecEnc.comp Computable.snd).to₂
  have hpf : ∀ m : ℕ, InformationTheory.IsPrefixFree {q | (f m q).Dom} := by
    intro m q₁ h₁ q₂ h₂ hp
    obtain ⟨x₁, hx₁⟩ := Part.dom_iff_mem.mp h₁
    obtain ⟨x₂, hx₂⟩ := Part.dom_iff_mem.mp h₂
    obtain ⟨n₁, hn₁, -⟩ := (Part.mem_map_iff _).mp hx₁
    obtain ⟨n₂, hn₂, -⟩ := (Part.mem_map_iff _).mp hx₂
    exact isPrefixFree_condUniversalPrefix m q₁ ⟨n₁, (hC m q₁ n₁).mpr hn₁⟩
      q₂ ⟨n₂, (hC m q₂ n₂).mpr hn₂⟩ hp
  obtain ⟨c, hc⟩ := exists_ecomplexity_condUniversalPrefix_le_of_partrec₂ hf hpf
  refine ⟨c, fun y x => ?_⟩
  obtain ⟨p, hp, hlen⟩ :=
    exists_length_eq_ecomplexity (ecomplexity_condUniversalPrefixBits_ne_top y x)
  rw [condUniversalPrefixBits, map_produces_iff] at hp
  obtain ⟨n, hpn, hnx⟩ := hp
  have hmem : encode x ∈ f (encode y) p :=
    (Part.mem_map_iff _).mpr ⟨n, (hC (encode y) p n).mp hpn, congrArg encode hnx⟩
  have h := hc (encode y) p (encode x) hmem
  rw [hlen, ← natCast_complexity_condUniversalPrefixBits,
    ← natCast_complexity_condUniversalPrefix] at h
  exact_mod_cast h

private theorem complexity_condUniversalPrefixBits_le_encode (y x : List Bool) :
    (condUniversalPrefixBits y).complexity x ≤
      (condUniversalPrefix (encode y)).complexity (encode x) := by
  have hle := ecomplexity_condUniversalPrefixBits_le_encode y x
  rw [← natCast_complexity_condUniversalPrefixBits, ← natCast_complexity_condUniversalPrefix]
    at hle
  exact_mod_cast hle

/-! ### Prefix-free chain rule -/

private def firstPrefixMatch (r : List Bool) (L : List (List Bool × ℕ)) :
    Option (List Bool × ℕ) :=
  L.foldr (fun px acc => if px.1 <+: r then some px else acc) Option.none

private theorem primrec₂_firstPrefixMatch : Primrec₂ firstPrefixMatch := by
  have hh : Primrec₂ fun (rL : List Bool × List (List Bool × ℕ))
      (p : (List Bool × ℕ) × Option (List Bool × ℕ)) =>
      if p.1.1 <+: rL.1 then some p.1 else p.2 := by
    have hp : PrimrecPred fun arg : (List Bool × List (List Bool × ℕ)) ×
        ((List Bool × ℕ) × Option (List Bool × ℕ)) =>
        arg.2.1.1 <+: arg.1.1 :=
      Primrec.list_isPrefix.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.fst.comp Primrec.fst)
    exact Primrec₂.mk <| Primrec.ite hp
      (Primrec.option_some.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  exact Primrec₂.mk <| (Primrec.list_foldr Primrec.snd (Primrec.const Option.none) hh).of_eq
    fun _ => rfl

private theorem firstPrefixMatch_append_of_some {r : List Bool}
    {L₁ L₂ : List (List Bool × ℕ)} {px : List Bool × ℕ}
    (h : firstPrefixMatch r L₁ = some px) :
    firstPrefixMatch r (L₁ ++ L₂) = some px := by
  induction L₁ with
  | nil => simp [firstPrefixMatch] at h
  | cons hd tl ih =>
    simp only [firstPrefixMatch, List.cons_append, List.foldr_cons] at h ⊢
    by_cases hp : hd.1 <+: r
    · simp only [hp, ↓reduceIte] at h ⊢
      exact h
    · simp only [hp, ↓reduceIte] at h ⊢
      exact ih h

private theorem firstPrefixMatch_spec {r : List Bool} {L : List (List Bool × ℕ)}
    {px : List Bool × ℕ} (h : firstPrefixMatch r L = some px) :
    px ∈ L ∧ px.1 <+: r := by
  induction L with
  | nil => simp [firstPrefixMatch] at h
  | cons hd tl ih =>
    simp only [firstPrefixMatch, List.foldr_cons] at h
    by_cases hp : hd.1 <+: r
    · simp only [hp, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨List.mem_cons_self, hp⟩
    · simp only [hp, ↓reduceIte] at h
      obtain ⟨hmem, hpref⟩ := ih h
      exact ⟨List.mem_cons_of_mem hd hmem, hpref⟩

private theorem exists_firstPrefixMatch_of_mem {r : List Bool} {L : List (List Bool × ℕ)}
    {px : List Bool × ℕ} (hmem : px ∈ L) (hp : px.1 <+: r) :
    ∃ px', firstPrefixMatch r L = some px' := by
  induction L with
  | nil => simp at hmem
  | cons hd tl ih =>
    simp only [firstPrefixMatch, List.foldr_cons]
    by_cases hhd : hd.1 <+: r
    · exact ⟨hd, by simp [hhd]⟩
    · rcases List.mem_cons.mp hmem with rfl | htl
      · exact absurd hp hhd
      · obtain ⟨px', hpx'⟩ := ih htl
        refine ⟨px', ?_⟩
        rw [firstPrefixMatch] at hpx'
        simp only [hhd, ↓reduceIte]
        exact hpx'

private def chainPairStep (key : List Bool × ℕ → ℕ) (r : List Bool) (n : ℕ) : Option ℕ :=
  (firstPrefixMatch r (universalPrefixTable n)).bind fun px =>
    (parseCodeHeader (r.drop px.1.length)).bind fun cp =>
      ((prefixAccepted (cp.1.curry (key px)) n).lookup cp.2).map fun y => Nat.pair px.2 y

private theorem primrec₂_chainPairStep {key : List Bool × ℕ → ℕ} (hkey : Primrec key) :
    Primrec₂ (chainPairStep key) := by
  have hmatch : Primrec fun rn : List Bool × ℕ =>
      firstPrefixMatch rn.1 (universalPrefixTable rn.2) :=
    primrec₂_firstPrefixMatch.comp Primrec.fst (primrec_universalPrefixTable.comp Primrec.snd)
  have hdrop : Primrec₂ fun (rn : List Bool × ℕ) (px : List Bool × ℕ) =>
      parseCodeHeader (rn.1.drop px.1.length) :=
    Primrec₂.mk <| primrec_parseCodeHeader.comp
      (Primrec.list_drop.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.fst.comp Primrec.fst))
  have hlook : Primrec fun arg : ((List Bool × ℕ) × (List Bool × ℕ)) × (Code × List Bool) =>
      (prefixAccepted (arg.2.1.curry (key arg.1.2)) arg.1.1.2).lookup arg.2.2 :=
    primrec₂_prefixAccepted_lookup.comp
      (Primrec.pair
        (Code.primrec₂_curry.comp (Primrec.fst.comp Primrec.snd)
          (hkey.comp (Primrec.snd.comp Primrec.fst)))
        (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hmap : Primrec₂ fun (arg : (List Bool × ℕ) × (List Bool × ℕ)) (cp : Code × List Bool) =>
      ((prefixAccepted (cp.1.curry (key arg.2)) arg.1.2).lookup cp.2).map fun y =>
        Nat.pair arg.2.2 y :=
    Primrec₂.mk <| Primrec.option_map hlook
      (Primrec₂.natPair.comp
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd)
  have hinner : Primrec₂ fun (rn : List Bool × ℕ) (px : List Bool × ℕ) =>
      (parseCodeHeader (rn.1.drop px.1.length)).bind fun cp =>
        ((prefixAccepted (cp.1.curry (key px)) rn.2).lookup cp.2).map fun y =>
          Nat.pair px.2 y :=
    Primrec₂.mk <| Primrec.option_bind (hdrop.comp Primrec.fst Primrec.snd) hmap
  exact Primrec₂.mk <| (Primrec.option_bind hmatch hinner).of_eq fun _ => rfl

private theorem exists_complexity_universalPrefix_pair_le_add_key
    {key : List Bool × ℕ → ℕ} (hkey : Primrec key) :
    ∃ c : ℕ, ∀ (p : List Bool) (x y : ℕ), universalPrefix.Produces p x →
      universalPrefix.complexity (Nat.pair x y) ≤
        p.length + (condUniversalPrefix (key (p, x))).complexity y + c := by
  let evalChain : List Bool →. ℕ := fun r => Nat.rfindOpt (chainPairStep key r)
  have hevalChain : Partrec evalChain := Partrec.rfindOpt (primrec₂_chainPairStep hkey).to_comp
  have hmono : ∀ {r : List Bool} {z m n : ℕ}, m ≤ n →
      z ∈ chainPairStep key r m → z ∈ chainPairStep key r n := by
    intro r z m n hmn hz
    simp only [chainPairStep, Option.mem_def, Option.bind_eq_some_iff, Option.map_eq_some_iff]
      at hz ⊢
    obtain ⟨px, hm, ⟨cp, hcp, y, hy, rfl⟩⟩ := hz
    obtain ⟨tail, htail⟩ := universalPrefixTable_prefix hmn
    refine ⟨px, htail ▸ firstPrefixMatch_append_of_some hm, cp, hcp, y, ?_, rfl⟩
    exact lookup_prefixAccepted_mono hmn hy
  have hspec : ∀ {r : List Bool} {z : ℕ}, z ∈ evalChain r →
      ∃ p x c q y, p <+: r ∧ universalPrefix.Produces p x ∧
        parseCodeHeader (r.drop p.length) = some (c, q) ∧
        (condUniversalPrefix (key (p, x))).Produces (r.drop p.length) y ∧
        z = Nat.pair x y := by
    intro r z hz
    obtain ⟨n, hn⟩ := (Nat.rfindOpt_mono (hmono (r := r))).mp hz
    simp only [chainPairStep, Option.mem_def, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hn
    obtain ⟨⟨p, x⟩, hm, ⟨c, q⟩, hcp, y, hy, rfl⟩ := hn
    obtain ⟨hmem, hp⟩ := firstPrefixMatch_spec hm
    have hx : universalPrefix.Produces p x := mem_universalPrefixTable_produces hmem
    have hy' : (condUniversalPrefix (key (p, x))).Produces (r.drop p.length) y :=
      condUniversalPrefix_produces_iff.mpr
        ⟨c, q, hcp, ofPrefixCode_produces_iff.mpr ⟨n, mem_prefixAccepted_iff_lookup.mpr hy⟩⟩
    exact ⟨p, x, c, q, y, hp, hx, hcp, hy', rfl⟩
  have hpf : InformationTheory.IsPrefixFree {r | (evalChain r).Dom} := by
    intro r₁ h₁ r₂ h₂ hpref
    obtain ⟨z₁, hz₁⟩ := Part.dom_iff_mem.mp h₁
    obtain ⟨z₂, hz₂⟩ := Part.dom_iff_mem.mp h₂
    obtain ⟨p₁, x₁, _, _, y₁, hp₁, hx₁, _, hy₁, _⟩ := hspec hz₁
    obtain ⟨p₂, x₂, _, _, y₂, hp₂, hx₂, _, hy₂, _⟩ := hspec hz₂
    have hp₁₂ : p₁ = p₂ := by
      rcases List.prefix_or_prefix_of_prefix (hp₁.trans hpref) hp₂ with h | h
      · exact isPrefixFree_universalPrefix p₁ ⟨x₁, hx₁⟩ p₂ ⟨x₂, hx₂⟩ h
      · exact (isPrefixFree_universalPrefix p₂ ⟨x₂, hx₂⟩ p₁ ⟨x₁, hx₁⟩ h).symm
    subst hp₁₂
    have hx₁₂ : x₁ = x₂ := hx₁.unique hx₂
    subst hx₁₂
    have hdrop_pref : r₁.drop p₁.length <+: r₂.drop p₁.length :=
      hpref.drop p₁.length
    have hdrop_eq : r₁.drop p₁.length = r₂.drop p₁.length :=
      isPrefixFree_condUniversalPrefix (key (p₁, x₁)) _ ⟨y₁, hy₁⟩ _ ⟨y₂, hy₂⟩ hdrop_pref
    have hr1 : r₁ = p₁ ++ r₁.drop p₁.length := by
      rcases hp₁ with ⟨tail₁, rfl⟩
      simp
    have hr2 : r₂ = p₁ ++ r₂.drop p₁.length := by
      rcases hp₂ with ⟨tail₂, rfl⟩
      simp
    rw [hr1, hr2, hdrop_eq]
  obtain ⟨c, hc⟩ := minorizesPrefixPartrec_universalPrefix evalChain hevalChain hpf
  refine ⟨c, fun p x y hp => ?_⟩
  obtain ⟨q, hq, hqlen⟩ :=
    exists_length_eq_ecomplexity (ecomplexity_condUniversalPrefix_ne_top (key (p, x)) y)
  obtain ⟨n₁, hn₁⟩ := produces_iff_exists_mem_universalPrefixTable.mp hp
  obtain ⟨c₀, q₀, hcp₀, hq₀⟩ := condUniversalPrefix_produces_iff.mp hq
  obtain ⟨n₂, hn₂⟩ := ofPrefixCode_produces_iff.mp hq₀
  let n := max n₁ n₂
  have hn₁' : (p, x) ∈ universalPrefixTable n :=
    (universalPrefixTable_prefix (le_max_left n₁ n₂)).subset hn₁
  obtain ⟨⟨p', x'⟩, hmatch⟩ := exists_firstPrefixMatch_of_mem hn₁' (List.prefix_append p q)
  obtain ⟨hmem', hp'⟩ := firstPrefixMatch_spec hmatch
  have hx' : universalPrefix.Produces p' x' := mem_universalPrefixTable_produces hmem'
  have hpeq : p' = p := by
    rcases List.prefix_or_prefix_of_prefix hp' (List.prefix_append p q) with h | h
    · exact isPrefixFree_universalPrefix p' ⟨x', hx'⟩ p ⟨x, hp⟩ h
    · exact (isPrefixFree_universalPrefix p ⟨x, hp⟩ p' ⟨x', hx'⟩ h).symm
  have hxeq : x' = x := (hpeq ▸ hx').unique hp
  have hmatch' : firstPrefixMatch (p ++ q) (universalPrefixTable n) = some (p, x) := by
    rw [hmatch, hpeq, hxeq]
  have hstep : Nat.pair x y ∈ chainPairStep key (p ++ q) n := by
    simp only [chainPairStep, hmatch', Option.bind_some, List.drop_left, hcp₀, Option.mem_def,
      Option.map_eq_some_iff]
    refine ⟨y, ?_, rfl⟩
    exact mem_prefixAccepted_iff_lookup.mp
      ((prefixAccepted_prefix (c₀.curry (key (p, x))) (le_max_right n₁ n₂)).subset hn₂)
  have hev : Nat.pair x y ∈ evalChain (p ++ q) :=
    (Nat.rfindOpt_mono (hmono (r := p ++ q))).mpr ⟨n, hstep⟩
  have hbound := hc (p ++ q) (Nat.pair x y) hev
  rw [List.length_append, Nat.cast_add, add_assoc] at hbound
  rw [← natCast_complexity_universalPrefix] at hbound
  rw [← natCast_complexity_condUniversalPrefix] at hqlen
  have hbound' : universalPrefix.complexity (Nat.pair x y) ≤ p.length + (q.length + c) := by
    exact_mod_cast hbound
  have hq_nat : q.length = (condUniversalPrefix (key (p, x))).complexity y := by
    exact_mod_cast hqlen
  omega

/-- **Prefix-free chain rule** (no logarithmic overhead): `K(x, y) ≤ K(x) + K(y | x) + c`
[LiVitanyi2019, ShenUspenskyVereshchagin2017]. -/
theorem exists_complexity_universalPrefix_pair_le_add :
    ∃ c : ℕ, ∀ x y : ℕ,
      universalPrefix.complexity (Nat.pair x y) ≤
        universalPrefix.complexity x + (condUniversalPrefix x).complexity y + c := by
  obtain ⟨c, hc⟩ := exists_complexity_universalPrefix_pair_le_add_key Primrec.snd
  refine ⟨c, fun x y => ?_⟩
  obtain ⟨p, hp, hlen⟩ := exists_length_eq_ecomplexity (ecomplexity_universalPrefix_ne_top x)
  have hp_nat : p.length = universalPrefix.complexity x := by
    rw [← natCast_complexity_universalPrefix] at hlen
    exact_mod_cast hlen
  simpa [hp_nat] using hc p x y hp

/-- Prefix-free chain rule conditioned on `(x, K(x))`: `K(x, y) ≤ K(x) + K(y | x, K(x)) + c`. -/
theorem exists_complexity_universalPrefix_pair_le_add_pair :
    ∃ c : ℕ, ∀ x y : ℕ,
      universalPrefix.complexity (Nat.pair x y) ≤
        universalPrefix.complexity x +
          (condUniversalPrefix (Nat.pair x (universalPrefix.complexity x))).complexity y + c := by
  obtain ⟨c, hc⟩ := exists_complexity_universalPrefix_pair_le_add_key
    (Primrec₂.natPair.comp Primrec.snd (Primrec.list_length.comp Primrec.fst))
  refine ⟨c, fun x y => ?_⟩
  obtain ⟨p, hp, hlen⟩ := exists_length_eq_ecomplexity (ecomplexity_universalPrefix_ne_top x)
  have hp_nat : p.length = universalPrefix.complexity x := by
    rw [← natCast_complexity_universalPrefix] at hlen
    exact_mod_cast hlen
  simpa [hp_nat] using hc p x y hp

/-! ### Uniform conditional Kraft–Chaitin theorem -/

private def kcAllocState (av ac : List (List Bool)) :
    List ℕ → Option (List (List Bool) × List (List Bool))
  | [] => some (av, ac)
  | ℓ :: rest =>
    match kcStep av (some ℓ) with
    | (_, Option.none) => Option.none
    | (av', some w) => kcAllocState av' (w :: ac) rest

private theorem kcAllocListAux_eq_kcAllocState (av ac : List (List Bool)) (L : List ℕ) :
    kcAllocListAux av ac L = (kcAllocState av ac L).map fun p => p.2.reverse := by
  induction L generalizing av ac with
  | nil => rfl
  | cons ℓ rest ih =>
    simp only [kcAllocListAux, kcAllocState]
    cases kcStep av (some ℓ) with
    | mk av' opt =>
      cases opt with
      | none => rfl
      | some w => exact ih av' (w :: ac)

private theorem kcAllocState_append (av ac : List (List Bool)) (L₁ L₂ : List ℕ) :
    kcAllocState av ac (L₁ ++ L₂) =
      (kcAllocState av ac L₁).bind fun p => kcAllocState p.1 p.2 L₂ := by
  induction L₁ generalizing av ac with
  | nil => simp [kcAllocState]
  | cons ℓ rest ih =>
    simp only [List.cons_append, kcAllocState]
    cases kcStep av (some ℓ) with
    | mk av' opt =>
      cases opt with
      | none => rfl
      | some w => exact ih av' (w :: ac)

private def listReqs (reqs : ℕ → Option ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 =>
    match reqs n with
    | Option.none => listReqs reqs n
    | some ℓ => listReqs reqs n ++ [ℓ]

private theorem sum_listReqs_eq (reqs : ℕ → Option ℕ) (n : ℕ) :
    ((listReqs reqs n).map fun ℓ => (2 : ℚ)⁻¹ ^ ℓ).sum =
      ∑ i ∈ Finset.range n,
        (match reqs i with | Option.none => (0 : ℚ) | some ℓ => (2 : ℚ)⁻¹ ^ ℓ) := by
  induction n with
  | zero => simp [listReqs]
  | succ n ih =>
    rw [Finset.sum_range_succ, listReqs]
    cases h : reqs n with
    | none => simpa using ih
    | some ℓ =>
      simp only [List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
      simpa [add_comm] using congrArg (· + (2 : ℚ)⁻¹ ^ ℓ) ih

private def kcCollect (reqs : ℕ → Option ℕ) : ℕ → List (List Bool) × List (List Bool)
  | 0 => ([[]], [])
  | n + 1 =>
    let res := kcCollect reqs n
    match kcStep res.1 (reqs n) with
    | (avail', Option.none) => (avail', res.2)
    | (avail', some code) => (avail', res.2 ++ [code])

private theorem kcCollect_fst_eq_kcTrace (reqs : ℕ → Option ℕ) (n : ℕ) :
    (kcCollect reqs n).1 = (kcTrace reqs n).1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [kcCollect, kcTrace, ih]
    cases kcStep (kcTrace reqs n).1 (reqs n) with
    | mk av opt => cases opt <;> rfl

private theorem kcCollect_spec (reqs : ℕ → Option ℕ)
    (hbound : ∀ n : ℕ, ∑ i ∈ Finset.range n,
      (match reqs i with | Option.none => (0 : ℚ) | some ℓ => (2 : ℚ)⁻¹ ^ ℓ) ≤ 1) (n : ℕ) :
    kcAllocState [[]] [] (listReqs reqs n) =
      some ((kcCollect reqs n).1, (kcCollect reqs n).2.reverse) ∧
      (kcCollect reqs n).2.Pairwise PrefixDisjoint ∧
      (kcCollect reqs n).2.map List.length = listReqs reqs n := by
  induction n with
  | zero =>
    simp [listReqs, kcAllocState, kcCollect]
  | succ n ih =>
    obtain ⟨hstate, hpair, hlen⟩ := ih
    cases hreq : reqs n with
    | none =>
      have hkc : kcStep (kcCollect reqs n).1 Option.none = ((kcCollect reqs n).1, Option.none) :=
        rfl
      simpa [listReqs, hreq, kcCollect, hkc] using ⟨hstate, hpair, hlen⟩
    | some ℓ =>
      have hsum : ((listReqs reqs (n + 1)).map fun k => (2 : ℚ)⁻¹ ^ k).sum ≤ 1 := by
        rw [sum_listReqs_eq]
        exact hbound (n + 1)
      obtain ⟨codes, hcodes, hmap, hcodes_pair⟩ := kcAllocList_eq_some_of_sum_le_one hsum
      have haux : kcAllocListAux [[]] [] (listReqs reqs n ++ [ℓ]) = some codes := by
        simpa [kcAllocList, listReqs, hreq] using hcodes
      rw [kcAllocListAux_eq_kcAllocState, Option.map_eq_some_iff] at haux
      obtain ⟨⟨av', ac'⟩, hst', rfl⟩ := haux
      rw [kcAllocState_append, hstate, Option.bind_some] at hst'
      simp only [kcAllocState] at hst'
      cases hstep : kcStep (kcCollect reqs n).1 (some ℓ) with
      | mk av₁ opt =>
        rw [hstep] at hst'
        cases opt with
        | none => cases hst'
        | some w =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hst'
          obtain ⟨rfl, rfl⟩ := hst'
          have hcoll : kcCollect reqs (n + 1) = (av₁, (kcCollect reqs n).2 ++ [w]) := by
            simp [kcCollect, hreq, hstep]
          have hrev_eq :
              ((kcCollect reqs n).2 ++ [w]).reverse = w :: (kcCollect reqs n).2.reverse := by
            simp
          refine ⟨?_, ?_, ?_⟩
          · rw [listReqs, hreq, kcAllocState_append, hstate, Option.bind_some]
            simp [kcAllocState, hstep, hcoll, hrev_eq]
          · rw [hcoll]
            simpa [List.reverse_cons] using hcodes_pair
          · rw [hcoll]
            simpa [listReqs, hreq] using hmap

private theorem kcCollect_mono {reqs : ℕ → Option ℕ} {m n : ℕ} (hmn : m ≤ n) :
    (kcCollect reqs m).2 <+: (kcCollect reqs n).2 := by
  induction hmn with
  | refl => exact List.prefix_rfl
  | @step n h ih =>
    refine ih.trans ?_
    simp only [kcCollect]
    cases kcStep (kcCollect reqs n).1 (reqs n) with
    | mk av opt =>
      cases opt with
      | none => exact List.prefix_rfl
      | some w => exact List.prefix_append _ _

private theorem kcCode_of_sum_le_one {reqs : ℕ → Option ℕ}
    (hbound : ∀ n : ℕ, ∑ i ∈ Finset.range n,
      (match reqs i with | Option.none => (0 : ℚ) | some ℓ => (2 : ℚ)⁻¹ ^ ℓ) ≤ 1) :
    (∀ i ℓ, reqs i = some ℓ →
      ∃ w, kcCode reqs i = some w ∧ w.length = ℓ ∧
        ((kcCollect reqs (i + 1)).2)[(listReqs reqs i).length]? = some w) ∧
    (∀ {i j : ℕ} {p q : List Bool}, i ≠ j →
      kcCode reqs i = some p → kcCode reqs j = some q → PrefixDisjoint p q) := by
  have h1 : ∀ i ℓ, reqs i = some ℓ →
      ∃ w, kcCode reqs i = some w ∧ w.length = ℓ ∧
        ((kcCollect reqs (i + 1)).2)[(listReqs reqs i).length]? = some w := by
    intro i ℓ hi
    obtain ⟨hst_i, _, hlen_i⟩ := kcCollect_spec reqs hbound i
    obtain ⟨hst_s, _, hlen_s⟩ := kcCollect_spec reqs hbound (i + 1)
    rw [listReqs, hi, kcAllocState_append, hst_i, Option.bind_some] at hst_s
    simp only [kcAllocState] at hst_s
    cases hstep : kcStep (kcCollect reqs i).1 (some ℓ) with
    | mk av₁ opt =>
      rw [hstep] at hst_s
      cases opt with
      | none => cases hst_s
      | some w =>
        have hkc : kcCode reqs i = some w := by
          rw [kcCode, kcTrace, ← kcCollect_fst_eq_kcTrace, hi, hstep]
        have hcoll : kcCollect reqs (i + 1) = (av₁, (kcCollect reqs i).2 ++ [w]) := by
          simp [kcCollect, hi, hstep]
        have hidx : ((kcCollect reqs (i + 1)).2)[(listReqs reqs i).length]? = some w := by
          have hlen_c : (kcCollect reqs i).2.length = (listReqs reqs i).length := by
            have := congrArg List.length hlen_i
            simpa using this
          rw [hcoll, ← hlen_c, List.getElem?_append_right le_rfl]
          simp
        have hwlen : w.length = ℓ := by
          have hlen_c : (kcCollect reqs i).2.length = (listReqs reqs i).length := by
            simpa using congrArg List.length hlen_i
          have := congrArg (fun L => L[(listReqs reqs i).length]?) hlen_s
          rw [hcoll, List.map_append, List.map_singleton, listReqs, hi,
            List.getElem?_append_right (by simp [hlen_c]), List.getElem?_append_right le_rfl]
            at this
          simpa [hlen_c] using this
        exact ⟨w, hkc, hwlen, hidx⟩
  refine ⟨h1, ?_⟩
  intro i j p q hne hi hj
  have hi_some : (reqs i).isSome := by
    by_contra hn
    have hnone : reqs i = Option.none := Option.not_isSome_iff_eq_none.mp hn
    simp [kcCode, kcTrace, kcStep, hnone] at hi
  have hj_some : (reqs j).isSome := by
    by_contra hn
    have hnone : reqs j = Option.none := Option.not_isSome_iff_eq_none.mp hn
    simp [kcCode, kcTrace, kcStep, hnone] at hj
  obtain ⟨ℓi, hℓi⟩ := Option.isSome_iff_exists.mp hi_some
  obtain ⟨ℓj, hℓj⟩ := Option.isSome_iff_exists.mp hj_some
  obtain ⟨wp, hwp, _, hidxp⟩ := h1 i ℓi hℓi
  obtain ⟨wq, hwq, _, hidxq⟩ := h1 j ℓj hℓj
  obtain rfl := Option.some.inj (hwp.symm.trans hi)
  obtain rfl := Option.some.inj (hwq.symm.trans hj)
  let N := max (i + 1) (j + 1)
  have isPref_get : ∀ {L₁ L₂ : List (List Bool)} {k : ℕ} {x : List Bool},
      L₁ <+: L₂ → L₁[k]? = some x → L₂[k]? = some x := by
    rintro L₁ L₂ k x ⟨tail, rfl⟩ hk
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hk).1, hk]
  have hp_N : ((kcCollect reqs N).2)[(listReqs reqs i).length]? = some wp :=
    isPref_get (kcCollect_mono (le_max_left (i + 1) (j + 1))) hidxp
  have hq_N : ((kcCollect reqs N).2)[(listReqs reqs j).length]? = some wq :=
    isPref_get (kcCollect_mono (le_max_right (i + 1) (j + 1))) hidxq
  have hlen_lt : (listReqs reqs i).length ≠ (listReqs reqs j).length := by
    have hmono : ∀ a b, a < b → (reqs a).isSome →
        (listReqs reqs a).length < (listReqs reqs b).length := by
      intro a b hab ha
      obtain ⟨ℓa, hℓa⟩ := Option.isSome_iff_exists.mp ha
      have hsucc : (listReqs reqs a).length < (listReqs reqs (a + 1)).length := by
        simp [listReqs, hℓa]
      have hle_b : ∀ m n, m ≤ n → (listReqs reqs m).length ≤ (listReqs reqs n).length := by
        intro m n hmn
        induction hmn with
        | refl => exact le_rfl
        | @step k _ ihk =>
          dsimp only [listReqs]
          cases reqs k with
          | none => exact ihk
          | some _ => simp; omega
      exact lt_of_lt_of_le hsucc (hle_b (a + 1) b hab)
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (hmono i j hlt hi_some).ne
    · exact (hmono j i hlt hj_some).ne'
  obtain ⟨_, hpair_N, _⟩ := kcCollect_spec reqs hbound N
  rw [List.getElem?_eq_some_iff] at hp_N hq_N
  obtain ⟨hi_lt, hpi⟩ := hp_N
  obtain ⟨hj_lt, hqj⟩ := hq_N
  rw [← hpi, ← hqj]
  rcases lt_or_gt_of_ne hlen_lt with hlt | hlt
  · exact List.pairwise_iff_getElem.mp hpair_N _ _ hi_lt hj_lt hlt
  · exact (List.pairwise_iff_getElem.mp hpair_N _ _ hj_lt hi_lt hlt).symm

private theorem primrec_list_replicate_bool_ps :
    Primrec₂ (fun (n : ℕ) (b : Bool) => List.replicate n b) :=
  Primrec₂.mk <| (Primrec.list_map (Primrec.list_range.comp Primrec.fst)
    (Primrec.snd.comp Primrec.fst).to₂).of_eq fun ⟨n, b⟩ => by simp [List.map_const']

private theorem false_cons_replicate_false (d : ℕ) :
    false :: List.replicate d false = List.replicate d false ++ [false] := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [List.replicate_succ]
    simpa [List.cons_append] using congrArg (false :: ·) ih

private theorem splitFrom_eq_ps (u : List Bool) (d : ℕ) :
    splitFrom u d =
      (u ++ List.replicate d false,
        (List.range d).map fun k => u ++ List.replicate k false ++ [true]) := by
  induction d generalizing u with
  | zero => simp [splitFrom]
  | succ d ih =>
    rw [splitFrom, ih (u ++ [false])]
    ext1
    · simp only [List.append_assoc, List.singleton_append, false_cons_replicate_false,
        List.replicate_succ']
    · simp only [List.range_succ_eq_map, List.map_cons, List.map_map, Function.comp_def,
        List.replicate_zero, List.append_nil, List.cons.injEq, true_and]
      refine List.map_congr_left fun k _ => ?_
      simp only [List.append_assoc, List.singleton_append, false_cons_replicate_false,
        List.replicate_succ']

private theorem primrec₂_splitFrom_ps : Primrec₂ splitFrom := by
  have hfst : Primrec₂ fun (u : List Bool) (d : ℕ) => u ++ List.replicate d false :=
    Primrec₂.mk <| Primrec.list_append.comp Primrec.fst
      (primrec_list_replicate_bool_ps.comp Primrec.snd (Primrec.const false))
  have hsnd : Primrec₂ fun (u : List Bool) (d : ℕ) =>
      (List.range d).map fun k => u ++ List.replicate k false ++ [true] := by
    have hel : Primrec₂ fun (ud : List Bool × ℕ) (k : ℕ) =>
        ud.1 ++ List.replicate k false ++ [true] :=
      Primrec₂.mk <| Primrec.list_append.comp
        (Primrec.list_append.comp (Primrec.fst.comp Primrec.fst)
          (primrec_list_replicate_bool_ps.comp Primrec.snd (Primrec.const false)))
        (Primrec.const [true])
    exact Primrec₂.mk <| Primrec.list_map (Primrec.list_range.comp Primrec.snd) hel
  exact (Primrec.pair (hfst.comp Primrec.fst Primrec.snd)
    (hsnd.comp Primrec.fst Primrec.snd)).to₂.of_eq fun u d => (splitFrom_eq_ps u d).symm

private theorem primrec₂_bestLenLe_ps : Primrec₂ bestLenLe? := by
  have hcons : Primrec₂ fun (arg : ℕ × List (List Bool))
      (p : List Bool × List (List Bool) × Option ℕ) =>
      if p.1.length ≤ arg.1 then
        match p.2.2 with
        | Option.none => some p.1.length
        | some b => some (max p.1.length b)
      else p.2.2 := by
    have hp : PrimrecPred fun z : (ℕ × List (List Bool)) ×
        (List Bool × List (List Bool) × Option ℕ) =>
        z.2.1.length ≤ z.1.1 :=
      Primrec.nat_le.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.fst.comp Primrec.fst)
    have hmatch : Primrec fun z : (ℕ × List (List Bool)) ×
        (List Bool × List (List Bool) × Option ℕ) =>
        match z.2.2.2 with
        | Option.none => some z.2.1.length
        | some b => some (max z.2.1.length b) :=
      (Primrec.option_casesOn (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.option_some.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec₂.mk <| Primrec.option_some.comp <| Primrec.nat_max.comp
          (Primrec.list_length.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
          Primrec.snd)).of_eq fun z => by cases z.2.2.2 <;> rfl
    exact Primrec₂.mk <| Primrec.ite hp hmatch
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact Primrec₂.mk <| (Primrec.list_rec Primrec.snd (Primrec.const Option.none) hcons).of_eq
    fun arg => by
      rcases arg with ⟨ℓ, av⟩
      induction av with
      | nil => rfl
      | cons u rest ih =>
        dsimp only
        rw [bestLenLe?]
        by_cases h : u.length ≤ ℓ
        · simp only [h, ↓reduceIte, ih]
          cases bestLenLe? ℓ rest <;> rfl
        · simp [h, ih]

private theorem primrec₂_splitAtLen_ps :
    Primrec₂ fun (lb : ℕ × ℕ) (av : List (List Bool)) => splitAtLen lb.1 lb.2 av := by
  have hcons : Primrec₂ fun (arg : (ℕ × ℕ) × List (List Bool))
      (p : List Bool × List (List Bool) × (List (List Bool) × Option (List Bool))) =>
      if p.1.length = arg.1.2 then
        let res := splitFrom p.1 (arg.1.1 - p.1.length)
        (p.2.1 ++ res.2, some res.1)
      else (p.1 :: p.2.2.1, p.2.2.2) := by
    have hsplit : Primrec fun z : ((ℕ × ℕ) × List (List Bool)) ×
        (List Bool × List (List Bool) × (List (List Bool) × Option (List Bool))) =>
        splitFrom z.2.1 (z.1.1.1 - z.2.1.length) :=
      primrec₂_splitFrom_ps.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.nat_sub.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)))
    have hp : PrimrecPred fun z : ((ℕ × ℕ) × List (List Bool)) ×
        (List Bool × List (List Bool) × (List (List Bool) × Option (List Bool))) =>
        z.2.1.length = z.1.1.2 :=
      Primrec.eq.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    have h1 : Primrec fun z : ((ℕ × ℕ) × List (List Bool)) ×
        (List Bool × List (List Bool) × (List (List Bool) × Option (List Bool))) =>
        (z.2.2.1 ++ (splitFrom z.2.1 (z.1.1.1 - z.2.1.length)).2,
          some (splitFrom z.2.1 (z.1.1.1 - z.2.1.length)).1) :=
      Primrec.pair
        (Primrec.list_append.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
          (Primrec.snd.comp hsplit))
        (Primrec.option_some.comp (Primrec.fst.comp hsplit))
    have h2 : Primrec fun z : ((ℕ × ℕ) × List (List Bool)) ×
        (List Bool × List (List Bool) × (List (List Bool) × Option (List Bool))) =>
        (z.2.1 :: z.2.2.2.1, z.2.2.2.2) :=
      Primrec.pair
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    exact Primrec₂.mk <| Primrec.ite hp h1 h2
  exact Primrec₂.mk <| (Primrec.list_rec Primrec.snd (Primrec.const ([], Option.none)) hcons).of_eq
    fun arg => by
      rcases arg with ⟨lb, av⟩
      induction av with
      | nil => rfl
      | cons u rest ih =>
        dsimp only
        rw [splitAtLen]
        by_cases h : u.length = lb.2
        · simp [h]
        · simp [h, ih]

private theorem primrec₂_kcStep_ps : Primrec₂ kcStep := by
  have hsome : Primrec₂ fun (av : List (List Bool)) (ℓ : ℕ) =>
      match bestLenLe? ℓ av with
      | Option.none => (av, Option.none)
      | some b => splitAtLen ℓ b av := by
    have hbest := primrec₂_bestLenLe_ps.comp Primrec.snd Primrec.fst
    have hsplit : Primrec₂ fun (arg : List (List Bool) × ℕ) (b : ℕ) =>
        splitAtLen arg.2 b arg.1 :=
      Primrec₂.mk <| primrec₂_splitAtLen_ps.comp
        (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)
        (Primrec.fst.comp Primrec.fst)
    exact Primrec₂.mk <| (Primrec.option_casesOn hbest
      (Primrec.pair Primrec.fst (Primrec.const Option.none)) hsplit).of_eq fun arg => by
        cases bestLenLe? arg.2 arg.1 <;> rfl
  exact Primrec₂.mk <| (Primrec.option_casesOn Primrec.snd
    (Primrec.pair Primrec.fst (Primrec.const Option.none))
    (hsome.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).of_eq fun arg => by
      cases arg.2 <;> rfl

private def condKcStreamEval (req : ℕ → ℕ → Option (ℕ × ℕ)) (y : ℕ) (p : List Bool) :
    ℕ → Option ℕ
  | 0 => Option.none
  | t + 1 =>
    match condKcStreamEval req y p t with
    | some x => some x
    | Option.none =>
      if kcCode (fun i => (req y i).map Prod.fst) t = some p then (req y t).map Prod.snd
      else Option.none

private theorem condKcStreamEval_mono (req : ℕ → ℕ → Option (ℕ × ℕ)) (y : ℕ) (p : List Bool) :
    ∀ {m n : ℕ} {x : ℕ}, m ≤ n →
      condKcStreamEval req y p m = some x → condKcStreamEval req y p n = some x := by
  intro m n x hmn hm
  induction hmn with
  | refl => exact hm
  | step _ ih => simp only [condKcStreamEval, ih]

private theorem bound_real_to_rat (req : ℕ → Option (ℕ × ℕ))
    (hbound : ∀ n : ℕ, ∑ i ∈ Finset.range n,
      (match req i with | Option.none => (0 : ℝ) | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ) ≤ 1) :
    ∀ n : ℕ, ∑ i ∈ Finset.range n,
      (match (req i).map Prod.fst with | Option.none => (0 : ℚ) | some ℓ => (2 : ℚ)⁻¹ ^ ℓ) ≤
      1 := by
  intro n
  have hb := hbound n
  let f : ℕ → ℚ := fun i =>
    match (req i).map Prod.fst with | Option.none => (0 : ℚ) | some ℓ => (2 : ℚ)⁻¹ ^ ℓ
  have hcast : ((∑ i ∈ Finset.range n, f i : ℚ) : ℝ) =
      ∑ i ∈ Finset.range n,
        (match req i with | Option.none => (0 : ℝ) | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ) := by
    rw [Rat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only [f]
    cases req i <;> simp
  exact_mod_cast (hcast ▸ hb)

private theorem mem_condKcStreamEval_iff (req : ℕ → ℕ → Option (ℕ × ℕ))
    (y : ℕ)
    (hbound : ∀ n : ℕ, ∑ i ∈ Finset.range n,
      (match req y i with | Option.none => (0 : ℝ) | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ) ≤ 1)
    (p : List Bool) {t : ℕ} {x : ℕ} :
    condKcStreamEval req y p t = some x ↔
      ∃ i < t, kcCode (fun j => (req y j).map Prod.fst) i = some p ∧
        (req y i).map Prod.snd = some x := by
  obtain ⟨_, hdisj⟩ := kcCode_of_sum_le_one (bound_real_to_rat (req y) hbound)
  induction t generalizing x with
  | zero => simp [condKcStreamEval]
  | succ t ih =>
    simp only [condKcStreamEval]
    cases h : condKcStreamEval req y p t with
    | some z =>
      rw [Option.some.injEq]
      obtain ⟨i, hit, hcode, hval⟩ := (@ih z).mp h
      constructor
      · rintro rfl
        exact ⟨i, hit.trans (Nat.lt_succ_self t), hcode, hval⟩
      · rintro ⟨j, hjt, hjcode, hjval⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hjt with hjlt | rfl
        · have hz := (@ih x).mpr ⟨j, hjlt, hjcode, hjval⟩
          rw [h] at hz
          exact Option.some.inj hz
        · exact absurd (hdisj (i := i) (j := j) (by omega) hcode hjcode) (PrefixDisjoint.irrefl p)
    | none =>
      by_cases hkc : kcCode (fun i => (req y i).map Prod.fst) t = some p
      · simp only [hkc, ↓reduceIte]
        constructor
        · intro hx
          exact ⟨t, Nat.lt_succ_self t, hkc, hx⟩
        · rintro ⟨i, hit, hcode, hval⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hit with hilt | rfl
          · have : condKcStreamEval req y p t = some x := ih.mpr ⟨i, hilt, hcode, hval⟩
            rw [h] at this
            simp at this
          · exact hval
      · simp only [hkc, ↓reduceIte]
        constructor
        · simp
        · rintro ⟨i, hit, hcode, hval⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hit with hilt | rfl
          · have : condKcStreamEval req y p t = some x := ih.mpr ⟨i, hilt, hcode, hval⟩
            rw [h] at this
            simp at this
          · exact absurd hcode hkc

/-- **Uniform conditional Kraft–Chaitin theorem**: any jointly computable family of request
streams `req : ℕ → ℕ → Option (ℕ × ℕ)` with Kraft sum at most `1` for every condition `y` yields
one constant `c` with `K(z | y) ≤ ℓ + c` whenever `req y i = some (ℓ, z)`. -/
theorem condKraftChaitin_of_sum_le_one {req : ℕ → ℕ → Option (ℕ × ℕ)} (hreq : Computable₂ req)
    (hbound : ∀ y n : ℕ, ∑ i ∈ Finset.range n,
      (match req y i with | Option.none => (0 : ℝ) | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ) ≤ 1) :
    ∃ c : ℕ, ∀ y i ℓ z, req y i = some (ℓ, z) → (condUniversalPrefix y).ecomplexity z ≤ ℓ + c := by
  let reqs : ℕ → ℕ → Option ℕ := fun y i => (req y i).map Prod.fst
  have hreqs : Computable₂ reqs :=
    Computable₂.mk <| (Computable.option_casesOn hreq (Computable.const Option.none)
      (Computable.option_some.comp (Computable.fst.comp Computable.snd)).to₂).of_eq fun arg => by
        dsimp only [reqs]
        cases req arg.1 arg.2 <;> rfl
  have htrace : Computable₂ fun y n => kcTrace (reqs y) n :=
    Computable₂.mk <| (Computable.nat_rec Computable.snd (Computable.const ([[]], Option.none))
      (primrec₂_kcStep_ps.to_comp.comp
        (Computable.fst.comp (Computable.snd.comp Computable.snd))
        (hreqs.comp (Computable.fst.comp Computable.fst)
          (Computable.fst.comp Computable.snd))).to₂).of_eq fun yn => by
      have hrec : ∀ m : ℕ, Nat.rec ([[]], Option.none)
          (fun i IH => kcStep IH.1 (reqs yn.1 i)) m = kcTrace (reqs yn.1) m := by
        intro m
        induction m with
        | zero => rfl
        | succ m ih =>
          change kcStep _ (reqs yn.1 m) = _
          rw [ih]
          rfl
      exact hrec yn.2
  have hkcCode : Computable₂ fun y i => kcCode (reqs y) i :=
    Computable.snd.comp (htrace.comp Computable.fst (Computable.succ.comp Computable.snd)) |>.to₂
  have hstream : Computable fun arg : (ℕ × List Bool) × ℕ =>
      condKcStreamEval req arg.1.1 arg.1.2 arg.2 := by
    have hval : Computable₂ fun y i => (req y i).map Prod.snd :=
      Computable₂.mk <| (Computable.option_casesOn hreq (Computable.const Option.none)
        (Computable.option_some.comp (Computable.snd.comp Computable.snd)).to₂).of_eq
        fun arg => by dsimp only; cases req arg.1 arg.2 <;> rfl
    have helse : Computable fun arg : (ℕ × List Bool) × (ℕ × Option ℕ) =>
        bif decide (kcCode (reqs arg.1.1) arg.2.1 = some arg.1.2) then
          (req arg.1.1 arg.2.1).map Prod.snd else Option.none :=
      Computable.cond
        (Primrec.eq.decide.to_comp.comp
          (hkcCode.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd))
          (Computable.option_some.comp (Computable.snd.comp Computable.fst)))
        (hval.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd))
        (Computable.const Option.none)
    have hstep : Computable₂ fun (ypt : (ℕ × List Bool) × ℕ) (a : ℕ × Option ℕ) =>
        match a.2 with
        | some x => some x
        | Option.none =>
          bif decide (kcCode (reqs ypt.1.1) a.1 = some ypt.1.2) then (req ypt.1.1 a.1).map Prod.snd
          else Option.none :=
      (Computable.option_casesOn (Computable.snd.comp Computable.snd)
        (helse.comp (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd))
        (Computable.option_some.comp Computable.snd).to₂).of_eq fun arg => by
          rcases arg with ⟨⟨⟨_, _⟩, _⟩, ⟨_, _ | _⟩⟩ <;> rfl
    exact (Computable.nat_rec Computable.snd (Computable.const Option.none) hstep).of_eq
      fun ypt => by
        have hrec : ∀ m : ℕ, Nat.rec Option.none
            (fun i IH => match IH with
              | some x => some x
              | Option.none =>
                bif decide (kcCode (reqs ypt.1.1) i = some ypt.1.2) then
                  (req ypt.1.1 i).map Prod.snd else Option.none) m =
            condKcStreamEval req ypt.1.1 ypt.1.2 m := by
          intro m
          induction m with
          | zero => rfl
          | succ m ih =>
            dsimp only
            rw [ih, condKcStreamEval]
            cases condKcStreamEval req ypt.1.1 ypt.1.2 m with
            | none => by_cases hkc : kcCode (reqs ypt.1.1) m = some ypt.1.2 <;> simp [reqs, hkc]
            | some v => rfl
        exact hrec ypt.2
  let eval : ℕ → List Bool →. ℕ := fun y p => Nat.rfindOpt (condKcStreamEval req y p)
  have heval : Partrec₂ eval := Partrec.rfindOpt hstream
  have hbound_rat : ∀ y n : ℕ, ∑ i ∈ Finset.range n,
      (match reqs y i with | Option.none => (0 : ℚ) | some ℓ => (2 : ℚ)⁻¹ ^ ℓ) ≤ 1 :=
    fun y => bound_real_to_rat (req y) (hbound y)
  have hpf : ∀ y : ℕ, InformationTheory.IsPrefixFree {p | (eval y p).Dom} := by
    intro y p₁ h₁ p₂ h₂ hpref
    obtain ⟨z₁, hz₁⟩ := Part.dom_iff_mem.mp h₁
    obtain ⟨z₂, hz₂⟩ := Part.dom_iff_mem.mp h₂
    obtain ⟨t₁, ht₁⟩ := (Nat.rfindOpt_mono (fun hmn => condKcStreamEval_mono req y p₁ hmn)).mp hz₁
    obtain ⟨t₂, ht₂⟩ := (Nat.rfindOpt_mono (fun hmn => condKcStreamEval_mono req y p₂ hmn)).mp hz₂
    obtain ⟨i₁, -, hi₁, _⟩ := (mem_condKcStreamEval_iff req y (hbound y) p₁).mp ht₁
    obtain ⟨i₂, -, hi₂, _⟩ := (mem_condKcStreamEval_iff req y (hbound y) p₂).mp ht₂
    by_contra hne
    have hine : i₁ ≠ i₂ := by
      rintro rfl
      exact hne (Option.some.inj (hi₁.symm.trans hi₂))
    exact ((kcCode_of_sum_le_one (hbound_rat y)).2 hine hi₁ hi₂).1 hpref
  obtain ⟨c, hc⟩ := exists_ecomplexity_condUniversalPrefix_le_of_partrec₂ heval hpf
  refine ⟨c, fun y i ℓ z hiy => ?_⟩
  obtain ⟨w, hw, hlen, _⟩ := (kcCode_of_sum_le_one (hbound_rat y)).1 i ℓ (by simp [reqs, hiy])
  have hw_eval : z ∈ eval y w := by
    refine (Nat.rfindOpt_mono (fun hmn => condKcStreamEval_mono req y w hmn)).mpr ⟨i + 1, ?_⟩
    exact (mem_condKcStreamEval_iff req y (hbound y) w).mpr
      ⟨i, Nat.lt_succ_self i, hw, by simp [hiy]⟩
  simpa [hlen] using hc y w z hw_eval

/-! ### Canonical shortest programs `x*` and condition equivalence -/

private def firstProgCand (x k n : ℕ) : Option (List Bool) :=
  (universalPrefixTable n).foldr
    (fun py acc => if py.2 = x ∧ py.1.length = k then some py.1 else acc) Option.none

private theorem primrec_firstProgCand :
    Primrec fun arg : (ℕ × ℕ) × ℕ => firstProgCand arg.1.1 arg.1.2 arg.2 := by
  have hcons : Primrec₂ fun (xkn : (ℕ × ℕ) × ℕ)
      (p : (List Bool × ℕ) × Option (List Bool)) =>
      if p.1.2 = xkn.1.1 ∧ p.1.1.length = xkn.1.2 then some p.1.1 else p.2 := by
    have hp : PrimrecPred fun arg : ((ℕ × ℕ) × ℕ) × ((List Bool × ℕ) × Option (List Bool)) =>
        arg.2.1.2 = arg.1.1.1 ∧ arg.2.1.1.length = arg.1.1.2 :=
      (Primrec.eq.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).and
        (Primrec.eq.comp
          (Primrec.list_length.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
    exact Primrec₂.mk <| Primrec.ite hp
      (Primrec.option_some.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldr (primrec_universalPrefixTable.comp Primrec.snd)
    (Primrec.const Option.none) hcons).of_eq fun _ => rfl

private theorem firstProgCand_append_of_some {x k : ℕ} {L₁ L₂ : List (List Bool × ℕ)}
    {p : List Bool}
    (h : L₁.foldr (fun py acc => if py.2 = x ∧ py.1.length = k then some py.1 else acc)
      Option.none = some p) :
    (L₁ ++ L₂).foldr (fun py acc => if py.2 = x ∧ py.1.length = k then some py.1 else acc)
      Option.none = some p := by
  induction L₁ with
  | nil => simp at h
  | cons hd tl ih =>
    simp only [List.cons_append, List.foldr_cons] at h ⊢
    by_cases hp : hd.2 = x ∧ hd.1.length = k
    · simp only [hp] at h ⊢
      exact h
    · simp only [hp] at h ⊢
      exact ih h

private theorem firstProgCand_spec {x k n : ℕ} {p : List Bool}
    (h : firstProgCand x k n = some p) :
    universalPrefix.Produces p x ∧ p.length = k := by
  have aux : ∀ L : List (List Bool × ℕ),
      L.foldr (fun py acc => if py.2 = x ∧ py.1.length = k then some py.1 else acc)
        Option.none = some p → (p, x) ∈ L ∧ p.length = k := by
    intro L hL
    induction L with
    | nil => simp at hL
    | cons hd tl ih =>
      simp only [List.foldr_cons] at hL
      split_ifs at hL with hp
      · rw [Option.some.injEq] at hL
        subst hL
        rcases hp with ⟨h2, hlen⟩
        have hhd : (hd.1, x) = hd := Prod.ext rfl h2.symm
        exact ⟨hhd ▸ List.mem_cons_self, hlen⟩
      · obtain ⟨hmem, hlen⟩ := ih hL
        exact ⟨List.mem_cons_of_mem hd hmem, hlen⟩
  obtain ⟨hmem, hlen⟩ := aux _ h
  exact ⟨mem_universalPrefixTable_produces hmem, hlen⟩

private theorem exists_firstProgCand_of_produces {x k : ℕ} {p : List Bool}
    (hp : universalPrefix.Produces p x) (hlen : p.length = k) :
    ∃ n p', firstProgCand x k n = some p' := by
  obtain ⟨n, hn⟩ := produces_iff_exists_mem_universalPrefixTable.mp hp
  refine ⟨n, ?_⟩
  have aux : ∀ L : List (List Bool × ℕ), (p, x) ∈ L →
      ∃ p', L.foldr (fun py acc => if py.2 = x ∧ py.1.length = k then some py.1 else acc)
        Option.none = some p' := by
    intro L hL
    induction L with
    | nil => simp at hL
    | cons hd tl ih =>
      simp only [List.foldr_cons]
      split_ifs with hhd
      · exact ⟨hd.1, rfl⟩
      · rcases List.mem_cons.mp hL with rfl | htl
        · exact absurd ⟨rfl, hlen⟩ hhd
        · exact ih htl
  exact aux _ hn

private noncomputable def firstProgSearch (xk : ℕ) : Part (List Bool) :=
  Nat.rfindOpt (firstProgCand xk.unpair.1 xk.unpair.2)

private theorem partrec_firstProgSearch : Partrec firstProgSearch :=
  Partrec.rfindOpt
    (primrec_firstProgCand.comp
      (Primrec.pair (Primrec.unpair.comp Primrec.fst) Primrec.snd)).to_comp

private theorem mem_firstProgSearch_iff {x k : ℕ} {p : List Bool} :
    p ∈ firstProgSearch (Nat.pair x k) ↔ ∃ n, firstProgCand x k n = some p := by
  have hmono : ∀ {z : List Bool} {m n : ℕ}, m ≤ n →
      z ∈ firstProgCand x k m → z ∈ firstProgCand x k n := by
    intro z m n hmn hz
    obtain ⟨tail, htail⟩ := universalPrefixTable_prefix hmn
    change firstProgCand x k n = some z
    rw [firstProgCand, ← htail]
    exact firstProgCand_append_of_some hz
  simpa [firstProgSearch] using Nat.rfindOpt_mono hmono

private theorem dom_firstProgSearch_complexity (x : ℕ) :
    (firstProgSearch (Nat.pair x (universalPrefix.complexity x))).Dom := by
  obtain ⟨p, hp, hlen⟩ := exists_length_eq_ecomplexity (ecomplexity_universalPrefix_ne_top x)
  have hplen : p.length = universalPrefix.complexity x := by
    rw [← natCast_complexity_universalPrefix] at hlen
    exact_mod_cast hlen
  obtain ⟨n, p', hn⟩ := exists_firstProgCand_of_produces hp hplen
  exact Part.dom_iff_mem.mpr ⟨p', mem_firstProgSearch_iff.mpr ⟨n, hn⟩⟩

/-- Canonical shortest prefix-free program `x*` for `x : ℕ` (the earliest halting program of
length `K(x)` producing `x` in `universalPrefixTable`). -/
noncomputable def shortestPrefixProgram (x : ℕ) : List Bool :=
  (firstProgSearch (Nat.pair x (universalPrefix.complexity x))).get
    (dom_firstProgSearch_complexity x)

private theorem mem_firstProgSearch_shortestPrefixProgram (x : ℕ) :
    shortestPrefixProgram x ∈ firstProgSearch (Nat.pair x (universalPrefix.complexity x)) :=
  Part.get_mem (dom_firstProgSearch_complexity x)

theorem universalPrefix_produces_shortestPrefixProgram (x : ℕ) :
    universalPrefix.Produces (shortestPrefixProgram x) x := by
  obtain ⟨n, hn⟩ := mem_firstProgSearch_iff.mp (mem_firstProgSearch_shortestPrefixProgram x)
  exact (firstProgCand_spec hn).1

@[simp]
theorem length_shortestPrefixProgram (x : ℕ) :
    (shortestPrefixProgram x).length = universalPrefix.complexity x := by
  obtain ⟨n, hn⟩ := mem_firstProgSearch_iff.mp (mem_firstProgSearch_shortestPrefixProgram x)
  exact (firstProgCand_spec hn).2

/-- Inter-convertibility of conditioning on `(x, K(x))` versus conditioning on `x*`:
`|K(z | x, K(x)) - K(z | x*)| ≤ c`. -/
theorem exists_abs_complexity_condUniversalPrefix_pair_sub_shortestPrefixProgram_le :
    ∃ c : ℕ, ∀ x z : ℕ,
      |((condUniversalPrefix (Nat.pair x (universalPrefix.complexity x))).complexity z : ℤ) -
        (condUniversalPrefix (encode (shortestPrefixProgram x))).complexity z| ≤ c := by
  obtain ⟨evalU, hevalU, hU⟩ := isPartrec_universalPrefix
  let g_pair_to_prog : ℕ →. ℕ := fun y => (firstProgSearch y).map encode
  have hg₁ : Partrec g_pair_to_prog :=
    partrec_firstProgSearch.map (Primrec.encode.to_comp.comp Computable.snd).to₂
  obtain ⟨c₁, hc₁⟩ := exists_complexity_condUniversalPrefix_le_of_partrec_map hg₁
  let g_prog_to_pair : ℕ →. ℕ := fun m =>
    ((decode₂ (List Bool) m : Option (List Bool)) : Part (List Bool)).bind fun p =>
      (evalU p).map fun x => Nat.pair x p.length
  have hdec2 : Partrec fun m : ℕ =>
      ((decode₂ (List Bool) m : Option (List Bool)) : Part (List Bool)) :=
    Computable.ofOption Primrec.decode₂.to_comp
  have hg₂ : Partrec g_prog_to_pair :=
    Partrec.bind hdec2
      ((hevalU.comp Computable.snd).map
        (Primrec₂.natPair.to_comp.comp Computable.snd
          (Primrec.list_length.to_comp.comp (Computable.snd.comp Computable.fst))).to₂)
  obtain ⟨c₂, hc₂⟩ := exists_complexity_condUniversalPrefix_le_of_partrec_map hg₂
  refine ⟨max c₁ c₂, fun x z => ?_⟩
  have hm₁ : encode (shortestPrefixProgram x) ∈
      g_pair_to_prog (Nat.pair x (universalPrefix.complexity x)) :=
    Part.mem_map encode (mem_firstProgSearch_shortestPrefixProgram x)
  have hm₂ : Nat.pair x (universalPrefix.complexity x) ∈
      g_prog_to_pair (encode (shortestPrefixProgram x)) := by
    rw [Part.mem_bind_iff]
    refine ⟨shortestPrefixProgram x, ?_, ?_⟩
    · simp
    · refine (Part.mem_map_iff _).mpr
        ⟨x, (hU _ x).mp (universalPrefix_produces_shortestPrefixProgram x), ?_⟩
      rw [length_shortestPrefixProgram]
  have e₁ :=
    hc₁ (Nat.pair x (universalPrefix.complexity x)) (encode (shortestPrefixProgram x)) z hm₁
  have e₂ :=
    hc₂ (encode (shortestPrefixProgram x)) (Nat.pair x (universalPrefix.complexity x)) z hm₂
  rw [abs_le]
  constructor <;> omega

/-- Binary-string shortest prefix-free program `x*` for `x : List Bool`. -/
noncomputable def shortestPrefixProgramBits (x : List Bool) : List Bool :=
  shortestPrefixProgram (encode x)

theorem universalPrefixBits_produces_shortestPrefixProgramBits (x : List Bool) :
    universalPrefixBits.Produces (shortestPrefixProgramBits x) x := by
  rw [universalPrefixBits, map_produces_iff]
  exact ⟨encode x, universalPrefix_produces_shortestPrefixProgram (encode x), by simp [encodek]⟩

@[simp]
theorem length_shortestPrefixProgramBits (x : List Bool) :
    (shortestPrefixProgramBits x).length = universalPrefix.complexity (encode x) :=
  length_shortestPrefixProgram (encode x)

/-! ### Exact symmetry of information -/

private def prefixTableNew (i : ℕ) : Option (List Bool × ℕ) :=
  if (universalPrefixTable (i + 1)).length = (universalPrefixTable i).length then Option.none
  else universalPrefixCand i

private theorem primrec_prefixTableNew : Primrec prefixTableNew := by
  have hlen : PrimrecPred fun i : ℕ =>
      (universalPrefixTable (i + 1)).length = (universalPrefixTable i).length :=
    Primrec.eq.comp
      (Primrec.list_length.comp (primrec_universalPrefixTable.comp Primrec.succ))
      (Primrec.list_length.comp primrec_universalPrefixTable)
  exact (Primrec.ite hlen (Primrec.const Option.none) primrec_universalPrefixCand).of_eq
    fun _ => rfl

private theorem prefixTableNew_eq_some_iff {i : ℕ} {pz : List Bool × ℕ} :
    prefixTableNew i = some pz →
      universalPrefixTable (i + 1) = universalPrefixTable i ++ [pz] ∧
        pz ∉ universalPrefixTable i := by
  intro h
  dsimp only [prefixTableNew] at h
  split_ifs at h with hlen
  rw [universalPrefixTable] at hlen ⊢
  rw [Nat.distinctValues, h] at hlen ⊢
  dsimp only at hlen ⊢
  split_ifs at hlen ⊢ with hmem
  · exact absurd rfl hlen
  · exact ⟨rfl, hmem⟩

private theorem exists_prefixTableNew_of_produces {p : List Bool} {z : ℕ}
    (hp : universalPrefix.Produces p z) :
    ∃ i : ℕ, prefixTableNew i = some (p, z) := by
  obtain ⟨n, hn⟩ := produces_iff_exists_mem_universalPrefixTable.mp hp
  have hex : ∃ m : ℕ, (p, z) ∈ universalPrefixTable m := ⟨n, hn⟩
  classical
  let m₀ := Nat.find hex
  have hm₀_mem : (p, z) ∈ universalPrefixTable m₀ := Nat.find_spec hex
  have hm₀_pos : 0 < m₀ := by
    by_contra h0
    have hz : m₀ = 0 := by omega
    rw [hz] at hm₀_mem
    cases hm₀_mem
  let i := m₀ - 1
  have hi_succ : i + 1 = m₀ := Nat.sub_add_cancel hm₀_pos
  have hnot : (p, z) ∉ universalPrefixTable i := Nat.find_min hex (by omega)
  have hmem' : (p, z) ∈ universalPrefixTable (i + 1) := hi_succ ▸ hm₀_mem
  have hcand : universalPrefixCand i = some (p, z) := by
    obtain ⟨j, hj, hfj⟩ := Nat.mem_distinctValues.mp hmem'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · exact absurd (Nat.mem_distinctValues.mpr ⟨j, hlt, hfj⟩) hnot
    · exact hfj
  have htab : universalPrefixTable (i + 1) = universalPrefixTable i ++ [(p, z)] := by
    change Nat.distinctValues universalPrefixCand (i + 1) =
      Nat.distinctValues universalPrefixCand i ++ [(p, z)]
    rw [Nat.distinctValues, hcand]
    have hnot' : (p, z) ∉ Nat.distinctValues universalPrefixCand i := hnot
    simp [hnot']
  refine ⟨i, ?_⟩
  simp [prefixTableNew, htab, hcand]

private noncomputable def universalMarginalSigmaEquiv : (Σ _ : ℕ, ℕ) ≃ ℕ where
  toFun xy := Nat.pair xy.1 xy.2
  invFun z := ⟨z.unpair.1, z.unpair.2⟩
  left_inv xy := by
    rcases xy with ⟨x, y⟩
    simp
  right_inv z := Nat.pair_unpair z

private theorem summable_universalMarginal_sigma :
    Summable fun xy : Σ _ : ℕ, ℕ => universalPrefix.universalProb (Nat.pair xy.1 xy.2) :=
  (Equiv.summable_iff universalMarginalSigmaEquiv).mpr
    isPrefixFree_universalPrefix.summable_universalProb

private theorem exists_universalMarginal_le_two_pow :
    ∃ c₁ : ℕ, ∀ x : ℕ,
      ∑' y : ℕ, universalPrefix.universalProb (Nat.pair x y) ≤
        (2 : ℝ) ^ c₁ * (2 : ℝ)⁻¹ ^ universalPrefix.complexity x :=
  exists_le_two_pow_mul_universalPrefix_of_isLowerSemicomputable
    (fun _ => tsum_nonneg fun _ => universalProb_nonneg _ _)
    summable_universalMarginal_sigma.sigma
    (by
      calc ∑' x : ℕ, ∑' y : ℕ, universalPrefix.universalProb (Nat.pair x y)
          = ∑' xy : (Σ _ : ℕ, ℕ), universalPrefix.universalProb (Nat.pair xy.1 xy.2) :=
            (summable_universalMarginal_sigma.tsum_sigma'
              (fun _ => summable_universalMarginal_sigma.sigma_factor _)).symm
        _ = ∑' z : ℕ, universalPrefix.universalProb z :=
            universalMarginalSigmaEquiv.tsum_eq universalPrefix.universalProb
        _ = universalPrefix.chaitinOmega :=
            isPrefixFree_universalPrefix.tsum_universalProb_eq_chaitinOmega
        _ ≤ 1 := isPrefixFree_universalPrefix.chaitinOmega_le_one)
    isLowerSemicomputable_universalProb_marginal

private def symProgs (x n : ℕ) : List (List Bool) :=
  (universalPrefixTable n).flatMap fun pz => if pz.2.unpair.1 = x then [pz.1] else []

private def symMaxLen (x n : ℕ) : ℕ :=
  ((symProgs x n).map List.length).foldl max 0

private def symScaled (x n : ℕ) : ℕ :=
  ((symProgs x n).map fun w => 2 ^ (symMaxLen x n - w.length)).sum

private def symReq (c₁ xk i : ℕ) : Option (ℕ × ℕ) :=
  match prefixTableNew i with
  | Option.none => Option.none
  | some (p, z) =>
    if z.unpair.1 = xk.unpair.1 ∧
        symScaled xk.unpair.1 (i + 1) * 2 ^ xk.unpair.2 ≤
          2 ^ (symMaxLen xk.unpair.1 (i + 1) + c₁) then
      some (p.length + c₁ - xk.unpair.2, z.unpair.2)
    else Option.none

private theorem primrec₂_symProgs : Primrec₂ symProgs := by
  have hel : Primrec₂ fun (xn : ℕ × ℕ) (pz : List Bool × ℕ) =>
      if pz.2.unpair.1 = xn.1 then [pz.1] else [] :=
    Primrec₂.mk <| Primrec.ite
      (Primrec.eq.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.fst.comp Primrec.fst))
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.const []))
      (Primrec.const [])
  exact Primrec₂.mk <|
    (Primrec.list_flatMap (primrec_universalPrefixTable.comp Primrec.snd) hel).of_eq fun _ => rfl

private theorem primrec₂_symMaxLen : Primrec₂ symMaxLen := by
  have hmap : Primrec fun xn : ℕ × ℕ => (symProgs xn.1 xn.2).map List.length :=
    Primrec.list_map (primrec₂_symProgs.comp Primrec.fst Primrec.snd)
      (Primrec.list_length.comp Primrec.snd).to₂
  have hmax : Primrec₂ fun (_ : ℕ × ℕ) (mn : ℕ × ℕ) => max mn.1 mn.2 :=
    Primrec₂.mk <|
      Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact Primrec₂.mk <| (Primrec.list_foldl hmap (Primrec.const 0) hmax).of_eq fun _ => rfl

private theorem primrec₂_symScaled : Primrec₂ symScaled := by
  have hel : Primrec₂ fun (xn : ℕ × ℕ) (w : List Bool) =>
      (2 : ℕ) ^ (symMaxLen xn.1 xn.2 - w.length) :=
    Primrec₂.mk <| primrec_two_pow.comp
      (Primrec.nat_sub.comp
        (primrec₂_symMaxLen.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))
        (Primrec.list_length.comp Primrec.snd))
  exact Primrec₂.mk <|
    (Primrec.list_sum (Primrec.list_map (primrec₂_symProgs.comp Primrec.fst Primrec.snd) hel)).of_eq
      fun _ => rfl

private theorem primrec₂_symReq (c₁ : ℕ) : Primrec₂ (symReq c₁) := by
  have hbranch : Primrec₂ fun (xki : ℕ × ℕ) (pz : List Bool × ℕ) =>
      if pz.2.unpair.1 = xki.1.unpair.1 ∧
          symScaled xki.1.unpair.1 (xki.2 + 1) * 2 ^ xki.1.unpair.2 ≤
            2 ^ (symMaxLen xki.1.unpair.1 (xki.2 + 1) + c₁) then
        some (pz.1.length + c₁ - xki.1.unpair.2, pz.2.unpair.2)
      else Option.none := by
    have hx : Primrec fun arg : (ℕ × ℕ) × (List Bool × ℕ) => arg.1.1.unpair.1 :=
      Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.fst))
    have hk : Primrec fun arg : (ℕ × ℕ) × (List Bool × ℕ) => arg.1.1.unpair.2 :=
      Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.fst))
    have hi1 : Primrec fun arg : (ℕ × ℕ) × (List Bool × ℕ) => arg.1.2 + 1 :=
      Primrec.succ.comp (Primrec.snd.comp Primrec.fst)
    have hp1 : PrimrecPred fun arg : (ℕ × ℕ) × (List Bool × ℕ) =>
        arg.2.2.unpair.1 = arg.1.1.unpair.1 :=
      Primrec.eq.comp
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.snd))) hx
    have hp2 : PrimrecPred fun arg : (ℕ × ℕ) × (List Bool × ℕ) =>
        symScaled arg.1.1.unpair.1 (arg.1.2 + 1) * 2 ^ arg.1.1.unpair.2 ≤
          2 ^ (symMaxLen arg.1.1.unpair.1 (arg.1.2 + 1) + c₁) :=
      Primrec.nat_le.comp
        (Primrec.nat_mul.comp (primrec₂_symScaled.comp hx hi1) (primrec_two_pow.comp hk))
        (primrec_two_pow.comp
          (Primrec.nat_add.comp (primrec₂_symMaxLen.comp hx hi1) (Primrec.const c₁)))
    have hsome : Primrec fun arg : (ℕ × ℕ) × (List Bool × ℕ) =>
        some (arg.2.1.length + c₁ - arg.1.1.unpair.2, arg.2.2.unpair.2) :=
      Primrec.option_some.comp <| Primrec.pair
        (Primrec.nat_sub.comp
          (Primrec.nat_add.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
            (Primrec.const c₁))
          hk)
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.snd)))
    exact Primrec₂.mk <| Primrec.ite (hp1.and hp2) hsome (Primrec.const Option.none)
  exact Primrec₂.mk <| (Primrec.option_casesOn (primrec_prefixTableNew.comp Primrec.snd)
    (Primrec.const Option.none) hbranch).of_eq fun arg => by
      dsimp only [symReq]
      cases prefixTableNew arg.2 <;> rfl

private theorem mem_symProgs_iff {x n : ℕ} {w : List Bool} :
    w ∈ symProgs x n ↔ ∃ z, (w, z) ∈ universalPrefixTable n ∧ z.unpair.1 = x := by
  simp only [symProgs, List.mem_flatMap]
  constructor
  · rintro ⟨⟨p, z⟩, hmem, hp⟩
    by_cases hx : z.unpair.1 = x
    · simp only [hx, ↓reduceIte, List.mem_singleton] at hp
      subst hp
      exact ⟨z, hmem, hx⟩
    · simp [hx] at hp
  · rintro ⟨z, hmem, hx⟩
    exact ⟨(w, z), hmem, by simp [hx]⟩

private theorem nodup_symProgs (x n : ℕ) : (symProgs x n).Nodup := by
  have aux : ∀ L : List (List Bool × ℕ), (L.map Prod.fst).Nodup →
      (L.flatMap fun pz => if pz.2.unpair.1 = x then [pz.1] else []).Nodup := by
    intro L hL
    induction L with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.map_cons, List.nodup_cons] at hL
      simp only [List.flatMap_cons]
      by_cases h : hd.2.unpair.1 = x
      · simp only [h, ↓reduceIte, List.cons_append, List.nil_append, List.nodup_cons]
        refine ⟨fun hmem => hL.1 ?_, ih hL.2⟩
        simp only [List.mem_flatMap] at hmem
        obtain ⟨pz, hpz, hwpz⟩ := hmem
        by_cases h' : pz.2.unpair.1 = x
        · simp only [h', ↓reduceIte, List.mem_singleton] at hwpz
          exact List.mem_map.mpr ⟨pz, hpz, hwpz.symm⟩
        · simp [h'] at hwpz
      · simp only [h, ↓reduceIte, List.nil_append]
        exact ih hL.2
  exact aux (universalPrefixTable n) (nodup_map_fst_universalPrefixTable n)

private theorem symScaled_cast (x n : ℕ) :
    ((symScaled x n : ℕ) : ℝ) =
      (∑ w ∈ (symProgs x n).toFinset, (2 : ℝ)⁻¹ ^ w.length) * (2 : ℝ) ^ symMaxLen x n := by
  rw [List.sum_toFinset (fun w : List Bool => (2 : ℝ)⁻¹ ^ w.length) (nodup_symProgs x n)]
  exact natCast_sum_two_pow_sub_length (symMaxLen x n) (symProgs x n) fun _ hw =>
    List.mem_le_foldl_max (List.mem_map_of_mem hw)

private theorem sum_symProgs_le_of_scaled {c₁ x k n : ℕ}
    (h : symScaled x n * 2 ^ k ≤ 2 ^ (symMaxLen x n + c₁)) :
    ∑ w ∈ (symProgs x n).toFinset, (2 : ℝ)⁻¹ ^ w.length ≤
      (2 : ℝ) ^ c₁ * (2 : ℝ)⁻¹ ^ k := by
  have hreal : ((symScaled x n : ℕ) : ℝ) * (2 : ℝ) ^ k ≤
      (2 : ℝ) ^ (symMaxLen x n + c₁) := by
    exact_mod_cast h
  rw [symScaled_cast, pow_add] at hreal
  set S := ∑ w ∈ (symProgs x n).toFinset, (2 : ℝ)⁻¹ ^ w.length
  set M := (2 : ℝ) ^ symMaxLen x n
  have hM : 0 < M := by positivity
  have hSk : S * (2 : ℝ) ^ k * M ≤ (2 : ℝ) ^ c₁ * M := by linarith
  have hle : S * (2 : ℝ) ^ k ≤ (2 : ℝ) ^ c₁ := le_of_mul_le_mul_right hSk hM
  rw [inv_pow, ← div_eq_mul_inv]
  exact (le_div_iff₀ (by positivity)).mpr hle

private theorem symScaled_mul_le_of_universalMarginal {c₁ x n : ℕ}
    (hmarg : ∑' y : ℕ, universalPrefix.universalProb (Nat.pair x y) ≤
      (2 : ℝ) ^ c₁ * (2 : ℝ)⁻¹ ^ universalPrefix.complexity x) :
    symScaled x n * 2 ^ universalPrefix.complexity x ≤ 2 ^ (symMaxLen x n + c₁) := by
  classical
  let T := (symProgs x n).toFinset
  have hT : ∀ w ∈ T, ∃ z, universalPrefix.Produces w z ∧ z.unpair.1 = x := by
    intro w hw
    obtain ⟨z, hz, hzx⟩ := mem_symProgs_iff.mp (List.mem_toFinset.mp hw)
    exact ⟨z, mem_universalPrefixTable_produces hz, hzx⟩
  let emb : {w : List Bool // w ∈ T} →
      (y : ℕ) × {p : List Bool // universalPrefix.Produces p (Nat.pair x y)} :=
    fun w =>
      let z := (hT w.1 w.2).choose
      let hz := (hT w.1 w.2).choose_spec
      ⟨z.unpair.2, ⟨w.1, by
        have hpair : Nat.pair x z.unpair.2 = z := by
          rw [← hz.2, Nat.pair_unpair]
        rw [hpair]
        exact hz.1⟩⟩
  have hemb : Function.Injective emb := fun a b hab =>
    Subtype.ext (congrArg (fun q : (y : ℕ) ×
      {p : List Bool // universalPrefix.Produces p (Nat.pair x y)} => q.2.1) hab)
  let F : Finset ((y : ℕ) ×
      {p : List Bool // universalPrefix.Produces p (Nat.pair x y)}) :=
    T.attach.map ⟨emb, hemb⟩
  have hsum_F : ∑ w ∈ T, (2 : ℝ)⁻¹ ^ w.length =
      ∑ q ∈ F, (2 : ℝ)⁻¹ ^ q.2.1.length := by
    rw [Finset.sum_map]
    exact (Finset.sum_attach T fun w => (2 : ℝ)⁻¹ ^ w.length).symm
  have hs_sigma : Summable fun q : (y : ℕ) ×
      {p : List Bool // universalPrefix.Produces p (Nat.pair x y)} =>
      (2 : ℝ)⁻¹ ^ q.2.1.length := by
    let e : (y : ℕ) × {p : List Bool // universalPrefix.Produces p (Nat.pair x y)} ≃
        {p : List Bool // ∃ z, universalPrefix.Produces p z ∧ z.unpair.1 = x} :=
      { toFun yp := ⟨yp.2.1, Nat.pair x yp.1, yp.2.2, by simp⟩
        invFun p := ⟨p.2.choose.unpair.2, p.1, by
          have hz := p.2.choose_spec
          have heq : Nat.pair x p.2.choose.unpair.2 = p.2.choose :=
            (congrArg (Nat.pair · _) hz.2.symm).trans (Nat.pair_unpair _)
          rw [heq]
          exact hz.1⟩
        left_inv yp := by
          rcases yp with ⟨y, ⟨p, hp⟩⟩
          have hz : (⟨Nat.pair x y, hp, by simp⟩ :
              ∃ z, universalPrefix.Produces p z ∧ z.unpair.1 = x).choose = Nat.pair x y :=
            (hp.unique
              (⟨Nat.pair x y, hp, by simp⟩ :
                ∃ z, universalPrefix.Produces p z ∧ z.unpair.1 = x).choose_spec.1).symm
          have hy : (⟨Nat.pair x y, hp, by simp⟩ :
              ∃ z, universalPrefix.Produces p z ∧ z.unpair.1 = x).choose.unpair.2 = y := by
            rw [hz, Nat.unpair_pair]
          have hsub : ∀ {y₁ y₂ : ℕ} (hy : y₁ = y₂) {h₁ h₂},
              (⟨y₁, ⟨p, h₁⟩⟩ :
                (y : ℕ) × {p : List Bool // universalPrefix.Produces p (Nat.pair x y)}) =
                ⟨y₂, ⟨p, h₂⟩⟩ := by
            intro y₁ y₂ hy h₁ h₂
            subst hy
            rfl
          exact hsub hy
        right_inv _ := rfl }
    let embHalting : {p : List Bool // ∃ z, universalPrefix.Produces p z ∧ z.unpair.1 = x} →
        universalPrefix.haltingSet :=
      fun p => ⟨p.1, p.2.choose, p.2.choose_spec.1⟩
    have hembHalting : Function.Injective embHalting := fun _ _ h =>
      Subtype.ext (congrArg (fun q : universalPrefix.haltingSet => q.1) h)
    exact (Equiv.summable_iff e).mpr
      (isPrefixFree_universalPrefix.summable_two_inv_pow_length.comp_injective hembHalting)
  have htsum_eq : ∑' q : (y : ℕ) × {p : List Bool // universalPrefix.Produces p (Nat.pair x y)},
      (2 : ℝ)⁻¹ ^ q.2.1.length =
      ∑' y : ℕ, universalPrefix.universalProb (Nat.pair x y) :=
    hs_sigma.tsum_sigma' fun y => isPrefixFree_universalPrefix.summable_universalProb_program _
  have hsum_le : ∑ w ∈ T, (2 : ℝ)⁻¹ ^ w.length ≤
      (2 : ℝ) ^ c₁ * (2 : ℝ)⁻¹ ^ universalPrefix.complexity x := by
    calc ∑ w ∈ T, (2 : ℝ)⁻¹ ^ w.length
        = ∑ q ∈ F, (2 : ℝ)⁻¹ ^ q.2.1.length := hsum_F
      _ ≤ ∑' q : (y : ℕ) × {p : List Bool // universalPrefix.Produces p (Nat.pair x y)},
            (2 : ℝ)⁻¹ ^ q.2.1.length :=
          hs_sigma.sum_le_tsum F fun _ _ => by positivity
      _ = ∑' y : ℕ, universalPrefix.universalProb (Nat.pair x y) := htsum_eq
      _ ≤ (2 : ℝ) ^ c₁ * (2 : ℝ)⁻¹ ^ universalPrefix.complexity x := hmarg
  have hreal : ((symScaled x n * 2 ^ universalPrefix.complexity x : ℕ) : ℝ) ≤
      ((2 ^ (symMaxLen x n + c₁) : ℕ) : ℝ) := by
    push_cast
    rw [symScaled_cast, pow_add]
    calc (∑ w ∈ T, (2 : ℝ)⁻¹ ^ w.length) * (2 : ℝ) ^ symMaxLen x n *
          (2 : ℝ) ^ universalPrefix.complexity x
        ≤ ((2 : ℝ) ^ c₁ * (2 : ℝ)⁻¹ ^ universalPrefix.complexity x) *
            (2 : ℝ) ^ symMaxLen x n * (2 : ℝ) ^ universalPrefix.complexity x := by
          gcongr
      _ = (2 : ℝ) ^ symMaxLen x n * (2 : ℝ) ^ c₁ *
            (((2 : ℝ)⁻¹ * (2 : ℝ)) ^ universalPrefix.complexity x) := by
          rw [mul_pow]
          ring
      _ = (2 : ℝ) ^ symMaxLen x n * (2 : ℝ) ^ c₁ := by
          rw [inv_mul_cancel₀ (by norm_num), one_pow, mul_one]
  exact_mod_cast hreal

private theorem symReq_sum_le_one (c₁ xk n : ℕ) :
    ∑ i ∈ Finset.range n,
      (match symReq c₁ xk i with | Option.none => (0 : ℝ) | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ) ≤ 1 := by
  classical
  let x := xk.unpair.1
  let k := xk.unpair.2
  let I := (Finset.range n).filter fun i => (symReq c₁ xk i).isSome
  have hsum_I : ∑ i ∈ Finset.range n,
      (match symReq c₁ xk i with | Option.none => (0 : ℝ) | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ) =
      ∑ i ∈ I,
        (match symReq c₁ xk i with | Option.none => (0 : ℝ) | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ) := by
    have hite : ∑ i ∈ Finset.range n,
        (match symReq c₁ xk i with | Option.none => (0 : ℝ) | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ) =
        ∑ i ∈ Finset.range n, if (symReq c₁ xk i).isSome then
          (match symReq c₁ xk i with | Option.none => (0 : ℝ) | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ)
        else 0 :=
      Finset.sum_congr rfl fun i _ => by cases symReq c₁ xk i <;> simp
    rw [hite, ← Finset.sum_filter]
  rw [hsum_I]
  by_cases hne : I.Nonempty
  · let i₀ := I.max' hne
    have hi₀_mem : i₀ ∈ I := Finset.max'_mem I hne
    have hi₀_some : (symReq c₁ xk i₀).isSome = true := (Finset.mem_filter.mp hi₀_mem).2
    obtain ⟨⟨ℓ₀, y₀⟩, hi₀_eq⟩ := Option.isSome_iff_exists.mp hi₀_some
    have hi₀_guard : symScaled x (i₀ + 1) * 2 ^ k ≤ 2 ^ (symMaxLen x (i₀ + 1) + c₁) := by
      dsimp only [symReq] at hi₀_eq
      cases hpt : prefixTableNew i₀ with
      | none => simp [hpt] at hi₀_eq
      | some pz =>
        simp only [hpt] at hi₀_eq
        split_ifs at hi₀_eq with hg
        exact hg.2
    have hbudget := sum_symProgs_le_of_scaled hi₀_guard
    have hi_spec : ∀ i ∈ I, ∃ p z, prefixTableNew i = some (p, z) ∧ z.unpair.1 = x ∧
        symScaled x (i + 1) * 2 ^ k ≤ 2 ^ (symMaxLen x (i + 1) + c₁) ∧
        symReq c₁ xk i = some (p.length + c₁ - k, z.unpair.2) ∧
        k ≤ p.length + c₁ ∧ p ∈ (symProgs x (i₀ + 1)).toFinset := by
      intro i hi
      obtain ⟨⟨ℓ, y⟩, hseq⟩ := Option.isSome_iff_exists.mp (Finset.mem_filter.mp hi).2
      have hpt_some : (prefixTableNew i).isSome := by
        by_contra hn
        simp [symReq, Option.not_isSome_iff_eq_none.mp hn] at hseq
      obtain ⟨⟨p, z⟩, hpt⟩ := Option.isSome_iff_exists.mp hpt_some
      have hg : z.unpair.1 = x ∧
          symScaled x (i + 1) * 2 ^ k ≤ 2 ^ (symMaxLen x (i + 1) + c₁) := by
        dsimp only [symReq, x, k] at hseq ⊢
        rw [hpt] at hseq
        by_contra hn
        simp [hn] at hseq
      obtain ⟨hpt_tab, _⟩ := prefixTableNew_eq_some_iff hpt
      have hmem_i1 : (p, z) ∈ universalPrefixTable (i + 1) := by
        rw [hpt_tab]
        simp
      have hp_in_i1 : p ∈ (symProgs x (i + 1)).toFinset :=
        List.mem_toFinset.mpr (mem_symProgs_iff.mpr ⟨z, hmem_i1, hg.1⟩)
      have hsum_i1 := sum_symProgs_le_of_scaled hg.2
      have hpow_le : (2 : ℝ)⁻¹ ^ p.length ≤ (2 : ℝ) ^ c₁ * (2 : ℝ)⁻¹ ^ k :=
        (Finset.single_le_sum (f := fun w : List Bool => (2 : ℝ)⁻¹ ^ w.length)
          (fun _ _ => by positivity) hp_in_i1).trans hsum_i1
      have hpow_nat : 2 ^ k ≤ 2 ^ (p.length + c₁) := by
        have hreal : ((2 ^ k : ℕ) : ℝ) ≤ ((2 ^ (p.length + c₁) : ℕ) : ℝ) := by
          push_cast
          rw [pow_add]
          calc (2 : ℝ) ^ k
              = ((2 : ℝ)⁻¹ * (2 : ℝ)) ^ p.length * (2 : ℝ) ^ k := by
                rw [inv_mul_cancel₀ (by norm_num), one_pow, one_mul]
            _ = (2 : ℝ)⁻¹ ^ p.length * (2 : ℝ) ^ p.length * (2 : ℝ) ^ k := by
                rw [mul_pow]
            _ ≤ ((2 : ℝ) ^ c₁ * (2 : ℝ)⁻¹ ^ k) * (2 : ℝ) ^ p.length * (2 : ℝ) ^ k := by
                gcongr
            _ = (2 : ℝ) ^ p.length * (2 : ℝ) ^ c₁ * (((2 : ℝ)⁻¹ * (2 : ℝ)) ^ k) := by
                rw [mul_pow]
                ring
            _ = (2 : ℝ) ^ p.length * (2 : ℝ) ^ c₁ := by
                rw [inv_mul_cancel₀ (by norm_num), one_pow, mul_one]
        exact_mod_cast hreal
      have hk_le : k ≤ p.length + c₁ := (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hpow_nat
      have hi_le : i + 1 ≤ i₀ + 1 := Nat.succ_le_succ (Finset.le_max' I i hi)
      have hmem_i0 : (p, z) ∈ universalPrefixTable (i₀ + 1) :=
        (universalPrefixTable_prefix hi_le).subset hmem_i1
      have hp_in_i0 : p ∈ (symProgs x (i₀ + 1)).toFinset :=
        List.mem_toFinset.mpr (mem_symProgs_iff.mpr ⟨z, hmem_i0, hg.1⟩)
      have hsym_eq : symReq c₁ xk i = some (p.length + c₁ - k, z.unpair.2) := by
        dsimp only [symReq]
        rw [hpt]
        simp [x, k, hg.1, hg.2]
      exact ⟨p, z, hpt, hg.1, hg.2, hsym_eq, hk_le, hp_in_i0⟩
    let prog : I → List Bool := fun i => (hi_spec i.1 i.2).choose
    have hprog_inj : Function.Injective prog := by
      intro i j hpeq
      obtain ⟨zi, hpti, -, -, -, -, -⟩ := (hi_spec i.1 i.2).choose_spec
      obtain ⟨zj, hptj, -, -, -, -, -⟩ := (hi_spec j.1 j.2).choose_spec
      have htab_i := prefixTableNew_eq_some_iff hpti
      have htab_j := prefixTableNew_eq_some_iff hptj
      have hmem_i : (prog i, zi) ∈ universalPrefixTable (i.1 + 1) := by
        simp [htab_i.1, prog]
      have hmem_j : (prog j, zj) ∈ universalPrefixTable (j.1 + 1) := by
        simp [htab_j.1, prog]
      have hpi_prod := mem_universalPrefixTable_produces hmem_i
      have hpj_prod := mem_universalPrefixTable_produces hmem_j
      rw [← hpeq] at hpj_prod
      have hzeq : zi = zj := hpi_prod.unique hpj_prod
      by_contra hne_ij
      have hval_ne : i.1 ≠ j.1 := fun h => hne_ij (Subtype.ext h)
      rcases lt_or_gt_of_ne hval_ne with hlt | hlt
      · have hsub := (universalPrefixTable_prefix (Nat.succ_le_of_lt hlt)).subset hmem_i
        rw [hpeq, hzeq] at hsub
        exact htab_j.2 hsub
      · have hsub := (universalPrefixTable_prefix (Nat.succ_le_of_lt hlt)).subset hmem_j
        rw [← hpeq, ← hzeq] at hsub
        exact htab_i.2 hsub
    have hterms : ∀ i : I,
        (match symReq c₁ xk i.1 with | Option.none => (0 : ℝ) | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ) =
          (2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ c₁ * (2 : ℝ)⁻¹ ^ (prog i).length := by
      intro i
      obtain ⟨zi, -, -, -, hseq, hk_le, -⟩ := (hi_spec i.1 i.2).choose_spec
      rw [hseq]
      have hadd : (prog i).length + c₁ - k + k = (prog i).length + c₁ := Nat.sub_add_cancel hk_le
      have hpow : (2 : ℝ)⁻¹ ^ ((prog i).length + c₁ - k) * (2 : ℝ)⁻¹ ^ k =
          (2 : ℝ)⁻¹ ^ (prog i).length * (2 : ℝ)⁻¹ ^ c₁ := by
        rw [← pow_add, hadd, pow_add]
      calc (2 : ℝ)⁻¹ ^ ((prog i).length + c₁ - k)
          = (2 : ℝ)⁻¹ ^ ((prog i).length + c₁ - k) * (((2 : ℝ)⁻¹ * (2 : ℝ)) ^ k) := by
            rw [inv_mul_cancel₀ (by norm_num), one_pow, mul_one]
        _ = (2 : ℝ) ^ k * ((2 : ℝ)⁻¹ ^ ((prog i).length + c₁ - k) * (2 : ℝ)⁻¹ ^ k) := by
            rw [mul_pow]
            ring
        _ = (2 : ℝ) ^ k * ((2 : ℝ)⁻¹ ^ (prog i).length * (2 : ℝ)⁻¹ ^ c₁) := by rw [hpow]
        _ = (2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ c₁ * (2 : ℝ)⁻¹ ^ (prog i).length := by ring
    let P : Finset (List Bool) := I.attach.image prog
    have hP_sub : P ⊆ (symProgs x (i₀ + 1)).toFinset := by
      intro w hw
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨-, -, -, -, -, -, hp⟩ := (hi_spec i.1 i.2).choose_spec
      exact hp
    calc ∑ i ∈ I,
          (match symReq c₁ xk i with | Option.none => (0 : ℝ) | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ)
        = ∑ i ∈ I.attach,
            (match symReq c₁ xk i.1 with | Option.none => (0 : ℝ) | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ) :=
          (Finset.sum_attach I _).symm
      _ = ∑ i ∈ I.attach, (2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ c₁ * (2 : ℝ)⁻¹ ^ (prog i).length :=
          Finset.sum_congr rfl fun i _ => hterms i
      _ = (2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ c₁ * ∑ i ∈ I.attach, (2 : ℝ)⁻¹ ^ (prog i).length := by
          rw [← Finset.mul_sum]
      _ = (2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ c₁ * ∑ w ∈ P, (2 : ℝ)⁻¹ ^ w.length := by
          rw [Finset.sum_image fun a _ b _ h => hprog_inj h]
      _ ≤ (2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ c₁ *
            ∑ w ∈ (symProgs x (i₀ + 1)).toFinset, (2 : ℝ)⁻¹ ^ w.length :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg hP_sub fun _ _ _ => by positivity)
            (by positivity)
      _ ≤ (2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ c₁ * ((2 : ℝ) ^ c₁ * (2 : ℝ)⁻¹ ^ k) :=
          mul_le_mul_of_nonneg_left hbudget (by positivity)
      _ = ((2 : ℝ) * (2 : ℝ)⁻¹) ^ k * (((2 : ℝ)⁻¹ * (2 : ℝ)) ^ c₁) := by
          rw [mul_pow, mul_pow]
          ring
      _ = 1 := by
          rw [mul_inv_cancel₀ (by norm_num), inv_mul_cancel₀ (by norm_num), one_pow, one_pow,
            mul_one]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

/-- **Hard direction of prefix-free symmetry of information**:
`K(x) + K(y | x, K(x)) ≤ K(x, y) + c` [LiVitanyi2019, ShenUspenskyVereshchagin2017]. -/
theorem exists_complexity_universalPrefix_add_condUniversalPrefix_le :
    ∃ c : ℕ, ∀ x y : ℕ,
      universalPrefix.complexity x +
          (condUniversalPrefix (Nat.pair x (universalPrefix.complexity x))).complexity y ≤
        universalPrefix.complexity (Nat.pair x y) + c := by
  obtain ⟨c₁, hmarg⟩ := exists_universalMarginal_le_two_pow
  obtain ⟨c_kc, hkc⟩ := condKraftChaitin_of_sum_le_one (primrec₂_symReq c₁).to_comp
    (symReq_sum_le_one c₁)
  obtain ⟨c_fst, hfst⟩ :=
    exists_complexity_universalPrefix_comp_le (Primrec.fst.comp Primrec.unpair).to_comp
  refine ⟨c₁ + c_kc + c_fst, fun x y => ?_⟩
  obtain ⟨p, hp, hplen⟩ :=
    exists_length_eq_ecomplexity (ecomplexity_universalPrefix_ne_top (Nat.pair x y))
  have hp_nat : p.length = universalPrefix.complexity (Nat.pair x y) := by
    rw [← natCast_complexity_universalPrefix] at hplen
    exact_mod_cast hplen
  obtain ⟨i, hi⟩ := exists_prefixTableNew_of_produces hp
  have hguard := symScaled_mul_le_of_universalMarginal (n := i + 1) (hmarg x)
  have hreq : symReq c₁ (Nat.pair x (universalPrefix.complexity x)) i =
      some (p.length + c₁ - universalPrefix.complexity x, y) := by
    simp [symReq, hi, hguard]
  have he := hkc (Nat.pair x (universalPrefix.complexity x)) i
    (p.length + c₁ - universalPrefix.complexity x) y hreq
  rw [← natCast_complexity_condUniversalPrefix] at he
  have hcond : (condUniversalPrefix (Nat.pair x (universalPrefix.complexity x))).complexity y ≤
      p.length + c₁ - universalPrefix.complexity x + c_kc := by
    exact_mod_cast he
  have hkx : universalPrefix.complexity x ≤ p.length + c_fst := by
    simpa [hp_nat] using hfst (Nat.pair x y)
  omega

/-- **Exact symmetry of information** for `universalPrefix` conditioned on `(x, K(x))`
[LiVitanyi2019, ShenUspenskyVereshchagin2017]: `|K(x, y) - K(x) - K(y | x, K(x))| ≤ c`. -/
theorem exists_abs_complexity_universalPrefix_pair_sub_le :
    ∃ c : ℕ, ∀ x y : ℕ,
      |(universalPrefix.complexity (Nat.pair x y) : ℤ) -
        universalPrefix.complexity x -
        (condUniversalPrefix (Nat.pair x (universalPrefix.complexity x))).complexity y| ≤ c := by
  obtain ⟨c₁, h₁⟩ := exists_complexity_universalPrefix_pair_le_add_pair
  obtain ⟨c₂, h₂⟩ := exists_complexity_universalPrefix_add_condUniversalPrefix_le
  refine ⟨max c₁ c₂, fun x y => ?_⟩
  have e₁ := h₁ x y
  have e₂ := h₂ x y
  rw [abs_le]
  constructor <;> omega

/-- **Exact symmetry of information** for `universalPrefix` conditioned on canonical shortest
programs `x* = shortestPrefixProgram x`: `|K(x, y) - K(x) - K(y | x*)| ≤ c`. -/
theorem exists_abs_complexity_universalPrefix_pair_sub_shortestProgram_le :
    ∃ c : ℕ, ∀ x y : ℕ,
      |(universalPrefix.complexity (Nat.pair x y) : ℤ) -
        universalPrefix.complexity x -
        (condUniversalPrefix (encode (shortestPrefixProgram x))).complexity y| ≤ c := by
  obtain ⟨c₁, h₁⟩ := exists_abs_complexity_universalPrefix_pair_sub_le
  obtain ⟨c₂, h₂⟩ := exists_abs_complexity_condUniversalPrefix_pair_sub_shortestPrefixProgram_le
  refine ⟨c₁ + c₂, fun x y => ?_⟩
  have e₁ := abs_le.mp (h₁ x y)
  have e₂ := abs_le.mp (h₂ x y)
  rw [abs_le]
  constructor <;> omega

private theorem exists_foldr_bit_one {n : ℕ} (hn : n ≠ 0) :
    ∃ w : List Bool, w.foldr Nat.bit 1 = n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases h1 : n = 1
    · exact ⟨[], by simp [h1]⟩
    · have h2 : n / 2 ≠ 0 := by omega
      obtain ⟨w, hw⟩ := ih (n / 2) (by omega) h2
      refine ⟨decide (n % 2 = 1) :: w, ?_⟩
      rw [List.foldr_cons, hw, Nat.bit_val]
      cases hmod : decide (n % 2 = 1) <;> simp_all <;> omega

private def bitsStep (n k : ℕ) : Option (List Bool) :=
  if n = 0 then some []
  else (decode (α := List Bool) k).bind fun w =>
    if w.foldr Nat.bit 1 = n then some (w ++ [true]) else Option.none

private theorem primrec₂_bitsStep : Primrec₂ bitsStep := by
  have hbit1 : Primrec fun w : List Bool => w.foldr Nat.bit 1 := by
    have hbit : Primrec₂ fun (_ : List Bool) (bn : Bool × ℕ) => Nat.bit bn.1 bn.2 :=
      Primrec₂.mk <| (Primrec.cond (Primrec.fst.comp Primrec.snd)
        (Primrec.nat_double_succ.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.nat_double.comp (Primrec.snd.comp Primrec.snd))).of_eq fun _ => rfl
    exact (Primrec.list_foldr Primrec.id (Primrec.const 1) hbit).of_eq fun _ => rfl
  have hbranch : Primrec₂ fun (nk : ℕ × ℕ) (w : List Bool) =>
      if w.foldr Nat.bit 1 = nk.1 then some (w ++ [true]) else Option.none :=
    Primrec₂.mk <| Primrec.ite
      (Primrec.eq.comp (hbit1.comp Primrec.snd) (Primrec.fst.comp Primrec.fst))
      (Primrec.option_some.comp (Primrec.list_append.comp Primrec.snd (Primrec.const [true])))
      (Primrec.const Option.none)
  have hbind : Primrec fun nk : ℕ × ℕ => (decode (α := List Bool) nk.2).bind fun w =>
      if w.foldr Nat.bit 1 = nk.1 then some (w ++ [true]) else Option.none :=
    Primrec.option_bind (Primrec.decode.comp Primrec.snd) hbranch
  exact Primrec₂.mk <| (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0))
    (Primrec.const (some ([] : List Bool))) hbind).of_eq fun _ => rfl

private theorem primrec_list_replicate_true :
    Primrec fun n : ℕ => List.replicate n true :=
  (Primrec.list_map Primrec.list_range (Primrec.const true).to₂).of_eq fun n => by
    simp [List.map_const']

/-- **Exact symmetry of information** for binary strings (`universalPrefixBits`,
`condUniversalPrefixBits`) with self-delimiting pair encoding `selfDelimitingCode x ++ y`,
conditioned on `shortestPrefixProgramBits x`:
`|K(x̂ y) - K(x) - K(y | x*)| ≤ c`. -/
theorem exists_abs_complexity_universalPrefixBits_pair_sub_shortestProgram_le :
    ∃ c : ℕ, ∀ x y : List Bool,
      |(universalPrefixBits.complexity (selfDelimitingCode x ++ y) : ℤ) -
        universalPrefixBits.complexity x -
        (condUniversalPrefixBits (shortestPrefixProgramBits x)).complexity y| ≤ c := by
  let natBitsPart : ℕ →. List Bool := fun n => Nat.rfindOpt (bitsStep n)
  have hbitsPart : Partrec natBitsPart := Partrec.rfindOpt primrec₂_bitsStep.to_comp
  have hbits_mem : ∀ n : ℕ, n.bits ∈ natBitsPart n := by
    intro n
    have huniq : ∀ t ℓ, bitsStep n t = some ℓ → ℓ = n.bits := by
      intro t ℓ ht
      dsimp only [bitsStep] at ht
      split_ifs at ht with hn
      · subst hn
        simp only [Option.some.injEq] at ht
        simp [← ht]
      · obtain ⟨w, _, hw⟩ := Option.bind_eq_some_iff.mp ht
        split_ifs at hw with hfld
        simp only [Option.some.injEq] at hw
        rw [← hw, ← hfld, Nat.bits_foldr_bit_one]
    have hdom : (natBitsPart n).Dom := by
      refine Nat.rfindOpt_dom.mpr ?_
      by_cases hn : n = 0
      · exact ⟨0, [], by simp [bitsStep, hn]⟩
      · obtain ⟨w, hw⟩ := exists_foldr_bit_one hn
        exact ⟨encode w, w ++ [true], by simp [bitsStep, hn, hw]⟩
    have hmem := Part.get_mem hdom
    obtain ⟨t, ht⟩ := Nat.rfindOpt_spec hmem
    rw [huniq t _ ht] at hmem
    exact hmem
  let unpairFun : List Bool → ℕ := fun s =>
    let xy := decodeSelfDelimiting s
    Nat.pair (encode xy.1) (encode xy.2)
  have hunpairFun : Computable unpairFun := by
    have hxy : Computable decodeSelfDelimiting := primrec_decodeSelfDelimiting.to_comp
    exact Primrec₂.natPair.to_comp.comp
      (Primrec.encode.to_comp.comp (Computable.fst.comp hxy))
      (Primrec.encode.to_comp.comp (Computable.snd.comp hxy))
  obtain ⟨c_unpair, hc_unpair⟩ :=
    exists_complexity_universalPrefix_comp_universalPrefixBits_le hunpairFun
  let pairPart : ℕ →. ℕ := fun z =>
    ((decode₂ (List Bool) z.unpair.1 : Option (List Bool)) : Part (List Bool)).bind fun x =>
      ((decode₂ (List Bool) z.unpair.2 : Option (List Bool)) : Part (List Bool)).bind fun y =>
        (natBitsPart x.length).map fun ℓ =>
          encode ((List.replicate ℓ.length true ++ false :: (ℓ ++ x)) ++ y)
  have hpairPart : Partrec pairPart := by
    have hx : Partrec fun z : ℕ =>
        ((decode₂ (List Bool) z.unpair.1 : Option (List Bool)) : Part (List Bool)) :=
      Computable.ofOption (Primrec.decode₂.comp (Primrec.fst.comp Primrec.unpair)).to_comp
    have hy : Partrec fun zx : ℕ × List Bool =>
        ((decode₂ (List Bool) zx.1.unpair.2 : Option (List Bool)) : Part (List Bool)) :=
      Computable.ofOption
        (Primrec.decode₂.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))).to_comp
    have hbits_sub : Partrec fun zxy : (ℕ × List Bool) × List Bool =>
        natBitsPart zxy.1.2.length :=
      hbitsPart.comp (Primrec.list_length.to_comp.comp (Computable.snd.comp Computable.fst))
    have hmap : Primrec₂ fun (zxy : (ℕ × List Bool) × List Bool) (ℓ : List Bool) =>
        encode ((List.replicate ℓ.length true ++ false :: (ℓ ++ zxy.1.2)) ++ zxy.2) :=
      Primrec₂.mk <| Primrec.encode.comp <| Primrec.list_append.comp
        (Primrec.list_append.comp
          (primrec_list_replicate_true.comp (Primrec.list_length.comp Primrec.snd))
          (Primrec.list_cons.comp (Primrec.const false)
            (Primrec.list_append.comp Primrec.snd
              (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))))
        (Primrec.snd.comp Primrec.fst)
    exact Partrec.bind hx (Partrec.bind hy (hbits_sub.map hmap.to_comp.to₂))
  obtain ⟨c_pair, hc_pair⟩ := exists_complexity_universalPrefix_bind_le hpairPart
  obtain ⟨c₁, h₁⟩ := exists_abs_complexity_universalPrefix_pair_sub_shortestProgram_le
  obtain ⟨c₂, h₂⟩ := exists_complexity_bits_encode_le_universalPrefixBits
  obtain ⟨c₃, h₃⟩ := exists_complexity_condBits_encode_le_condUniversalPrefixBits
  refine ⟨c₁ + c_unpair + c_pair + 2 * c₂ + c₃, fun x y => ?_⟩
  have hsym := abs_le.mp (h₁ (encode x) (encode y))
  have hpair_lo : universalPrefix.complexity (Nat.pair (encode x) (encode y)) ≤
      universalPrefixBits.complexity (selfDelimitingCode x ++ y) + c_unpair := by
    simpa [unpairFun] using hc_unpair (selfDelimitingCode x ++ y)
  have hpair_hi : universalPrefixBits.complexity (selfDelimitingCode x ++ y) ≤
      universalPrefix.complexity (Nat.pair (encode x) (encode y)) + c_pair := by
    have hmem_pair : encode (selfDelimitingCode x ++ y) ∈
        pairPart (Nat.pair (encode x) (encode y)) := by
      refine Part.mem_bind_iff.mpr ⟨x, by simp, ?_⟩
      refine Part.mem_bind_iff.mpr ⟨y, by simp, ?_⟩
      refine (Part.mem_map_iff _).mpr ⟨x.length.bits, hbits_mem x.length, ?_⟩
      rw [Nat.size_eq_bits_len]
      rfl
    exact (complexity_universalPrefixBits_le_encode (selfDelimitingCode x ++ y)).trans
      (hc_pair (Nat.pair (encode x) (encode y)) (encode (selfDelimitingCode x ++ y)) hmem_pair)
  have hx_lo := h₂ x
  have hx_hi := complexity_universalPrefixBits_le_encode x
  have hcond_lo := h₃ (shortestPrefixProgramBits x) y
  have hcond_hi := complexity_condUniversalPrefixBits_le_encode (shortestPrefixProgramBits x) y
  have hsp : shortestPrefixProgramBits x = shortestPrefixProgram (encode x) := rfl
  simp only [hsp] at hcond_lo hcond_hi ⊢
  rw [abs_le]
  constructor <;> omega

end DescriptionMethod

/-! ### Prefix algorithmic mutual information and its symmetry -/

open DescriptionMethod

/-- **Prefix algorithmic mutual information** `I_K(x : y) = K(y) - K(y | x*)` for `x, y : ℕ`
[LiVitanyi2019, ShenUspenskyVereshchagin2017]. -/
@[expose] noncomputable def prefixInformation (x y : ℕ) : ℤ :=
  universalPrefix.complexity y -
    (condUniversalPrefix (encode (shortestPrefixProgram x))).complexity y

/-- Prefix algorithmic information is bounded below by `-O(1)`. -/
theorem exists_prefixInformation_ge :
    ∃ c : ℕ, ∀ x y : ℕ, -(c : ℤ) ≤ prefixInformation x y := by
  obtain ⟨c, hc⟩ := exists_complexity_condUniversalPrefix_le
  refine ⟨c, fun x y => ?_⟩
  have h := hc (encode (shortestPrefixProgram x)) y
  rw [prefixInformation]
  omega

/-- `I_K(x : y) = K(x) + K(y) - K(x, y) ± O(1)`. -/
theorem exists_abs_prefixInformation_sub_le :
    ∃ c : ℕ, ∀ x y : ℕ,
      |prefixInformation x y - (universalPrefix.complexity x +
        universalPrefix.complexity y - universalPrefix.complexity (Nat.pair x y) : ℤ)| ≤ c := by
  obtain ⟨c, hc⟩ := exists_abs_complexity_universalPrefix_pair_sub_shortestProgram_le
  refine ⟨c, fun x y => ?_⟩
  have h := abs_le.mp (hc x y)
  rw [abs_le, prefixInformation]
  constructor <;> omega

/-- **Exact symmetry of algorithmic mutual information** for prefix-free complexity
[LiVitanyi2019, ShenUspenskyVereshchagin2017]: `|I_K(x : y) - I_K(y : x)| ≤ c`. -/
theorem exists_abs_prefixInformation_symm :
    ∃ c : ℕ, ∀ x y : ℕ, |prefixInformation x y - prefixInformation y x| ≤ c := by
  obtain ⟨c, hc⟩ := exists_abs_prefixInformation_sub_le
  obtain ⟨d, hd⟩ := exists_complexity_universalPrefix_comp_le
    (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.unpair)
      (Primrec.fst.comp Primrec.unpair)).to_comp
  refine ⟨2 * c + d, fun x y => ?_⟩
  have h₁ := abs_le.mp (hc x y)
  have h₂ := abs_le.mp (hc y x)
  have e₁ : universalPrefix.complexity (Nat.pair y x) ≤
      universalPrefix.complexity (Nat.pair x y) + d := by
    simpa using hd (Nat.pair x y)
  have e₂ : universalPrefix.complexity (Nat.pair x y) ≤
      universalPrefix.complexity (Nat.pair y x) + d := by
    simpa using hd (Nat.pair y x)
  rw [abs_le]
  constructor <;> omega

end Cslib.Kolmogorov
