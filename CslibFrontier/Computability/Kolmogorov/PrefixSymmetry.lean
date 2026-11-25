/-
Copyright (c) 2026 Matthew Doty, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Kolmogorov.ConditionalPartrec
public import CslibFrontier.Computability.Kolmogorov.LevinCoding
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
* `Cslib.Kolmogorov.DescriptionMethod.shortestPrefixProgramBits`: canonical prefix-free program
  `shortestPrefixProgram (encode x)` producing `x : List Bool` under `universalPrefixBits`.
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
  rcases parseCodeHeader q with _ | ⟨c, p⟩ <;> simp [Computation.notMem_empty]

theorem condUniversalPrefix_produces_codeHeader_append {y : ℕ} {c : Code} {p : List Bool}
    {x : ℕ} :
    (condUniversalPrefix y).Produces (codeHeader c ++ p) x ↔
      (ofPrefixCode (c.curry y)).Produces p x := by
  rw [Produces, condUniversalPrefix_run_codeHeader_append, Produces]

private theorem complexity_le_of_ecomplexity_le {α : Type*} {M : DescriptionMethod α} {x : α}
    {n : ℕ} (h : M.ecomplexity x ≤ n) : M.complexity x ≤ n :=
  ENat.natCast_le_natCast.mp
    ((natCast_complexity (ne_top_of_le_ne_top (ENat.natCast_ne_top n) h)).trans_le h)

private theorem exists_length_eq_complexity {α : Type*} {M : DescriptionMethod α} {x : α}
    (h : M.ecomplexity x ≠ ⊤) : ∃ p, M.Produces p x ∧ p.length = M.complexity x := by
  obtain ⟨p, hp, hlen⟩ := exists_length_eq_ecomplexity h
  exact ⟨p, hp, ENat.natCast_inj.mp (hlen.trans (natCast_complexity h).symm)⟩

private theorem complexity_le_complexity_add {α β : Type*} {M : DescriptionMethod α}
    {N : DescriptionMethod β} {w : α} {z : β} {c : ℕ} (hz : N.ecomplexity z ≠ ⊤)
    (h : ∀ q, N.Produces q z → M.ecomplexity w ≤ q.length + c) :
    M.complexity w ≤ N.complexity z + c := by
  obtain ⟨q, hq, hlen⟩ := exists_length_eq_complexity hz
  rw [← hlen]
  exact complexity_le_of_ecomplexity_le (mod_cast h q hq)

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
  have hiff : ∀ p z, (ofCode (c.curry y)).Produces p z ↔ z ∈ f y p := fun p z => by
    rw [ofCode_produces_iff, Code.eval_curry, hc]
    simp
  have hcode_pf : (ofCode (c.curry y)).IsPrefixFree :=
    (hpf y).anti fun p ⟨z, hz⟩ => Part.dom_iff_mem.mpr ⟨z, (hiff p z).mp hz⟩
  have hcond : (condUniversalPrefix y).Produces (codeHeader c ++ q) x :=
    condUniversalPrefix_produces_codeHeader_append.mpr
      ((ofPrefixCode_produces_iff_of_isPrefixFree hcode_pf).mpr ((hiff q x).mpr hx))
  exact (ecomplexity_le_length hcond).trans (by rw [List.length_append, Nat.cast_add, add_comm])

/-- Conditional prefix-free invariance for conditional description methods. -/
theorem IsCondPartrec.exists_ecomplexity_condUniversalPrefix_le
    {N : ℕ → DescriptionMethod ℕ} (hN : IsCondPartrec N) (hpf : ∀ y, (N y).IsPrefixFree) :
    ∃ c : ℕ, ∀ y x, (condUniversalPrefix y).ecomplexity x ≤ (N y).ecomplexity x + c := by
  obtain ⟨f, hf, hN_eq⟩ := hN
  obtain ⟨c, hc⟩ := exists_ecomplexity_condUniversalPrefix_le_of_partrec₂ hf fun y =>
    (hpf y).anti fun p h => (Part.dom_iff_mem.mp h).imp fun x => (hN_eq y p x).mpr
  refine ⟨c, fun y x => ?_⟩
  by_cases h : (N y).ecomplexity x = ⊤
  · simp [h]
  obtain ⟨p, hp, hlen⟩ := exists_length_eq_ecomplexity h
  rw [← hlen]
  exact hc y p x ((hN_eq y p x).mp hp)

private theorem exists_ecomplexity_condUniversalPrefix_le :
    ∃ c : ℕ, ∀ y x, (condUniversalPrefix y).ecomplexity x ≤ universalPrefix.ecomplexity x + c := by
  obtain ⟨f, hf, hU⟩ := isPartrec_universalPrefix
  obtain ⟨c, hc⟩ := exists_ecomplexity_condUniversalPrefix_le_of_partrec₂
    (f := fun _ q => f q) (hf.comp Computable.snd) fun _ =>
      isPrefixFree_universalPrefix.anti fun p h =>
        (Part.dom_iff_mem.mp h).imp fun x => (hU p x).mpr
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
  exact ⟨c, fun y x => complexity_le_of_ecomplexity_le (by simpa using hc y x)⟩

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
  have hnil : ∀ y q, (f y q).Dom → q = [] := fun y q h => by
    obtain ⟨_, hm⟩ := Part.dom_iff_mem.mp h
    obtain ⟨_, hk⟩ := Nat.rfindOpt_spec hm
    by_contra hq
    simp [hq] at hk
  obtain ⟨c, hc⟩ := exists_ecomplexity_condUniversalPrefix_le_of_partrec₂ hf
    fun y q₁ h₁ q₂ h₂ _ => (hnil y q₁ h₁).trans (hnil y q₂ h₂).symm
  refine ⟨c, fun y => complexity_le_of_ecomplexity_le ?_⟩
  have hy : y ∈ f y [] := Nat.rfindOpt_mono (fun _ h => h) |>.mpr ⟨0, by simp⟩
  simpa using hc y [] y hy

private theorem exists_complexity_universalPrefix_bind_le {f : ℕ →. ℕ} (hf : Partrec f) :
    ∃ c : ℕ, ∀ x y : ℕ, y ∈ f x →
      universalPrefix.complexity y ≤ universalPrefix.complexity x + c := by
  obtain ⟨eval, heval, hU⟩ := isPartrec_universalPrefix
  let g : List Bool →. ℕ := fun q => (eval q).bind f
  have hg : Partrec g := Partrec.bind heval (hf.comp Computable.snd)
  have hpf : InformationTheory.IsPrefixFree {q | (g q).Dom} :=
    isPrefixFree_universalPrefix.anti fun q h => by
      obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp h
      obtain ⟨x, hx, -⟩ := Part.mem_bind_iff.mp hy
      exact ⟨x, (hU q x).mpr hx⟩
  obtain ⟨c, hc⟩ := minorizesPrefixPartrec_universalPrefix g hg hpf
  exact ⟨c, fun x y hy => complexity_le_complexity_add (ecomplexity_universalPrefix_ne_top x)
    fun p hp => hc p y (Part.mem_bind_iff.mpr ⟨x, (hU p x).mp hp, hy⟩)⟩

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
  exact ⟨c, fun y x z hx => complexity_le_complexity_add
    (ecomplexity_condUniversalPrefix_ne_top x z)
    fun q hq => hc y q z (Part.mem_bind_iff.mpr ⟨x, hx, (hC x q z).mp hq⟩)⟩

/-- Conditional computable postprocessing: `K(φ y z | y) ≤ K(z | y) + c`. -/
theorem exists_complexity_condUniversalPrefix_comp_le {φ : ℕ → ℕ → ℕ} (hφ : Computable₂ φ) :
    ∃ c : ℕ, ∀ y z : ℕ,
      (condUniversalPrefix y).complexity (φ y z) ≤ (condUniversalPrefix y).complexity z + c := by
  obtain ⟨evalC, hevalC, hC⟩ := isCondPartrec_condUniversalPrefix
  let f : ℕ → List Bool →. ℕ := fun y q => (evalC y q).map (φ y)
  have hf : Partrec₂ f :=
    hevalC.map (hφ.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂
  have hpf : ∀ y : ℕ, InformationTheory.IsPrefixFree {q | (f y q).Dom} := fun y =>
    (isPrefixFree_condUniversalPrefix y).anti fun q h => by
      obtain ⟨w, hw⟩ := Part.dom_iff_mem.mp h
      obtain ⟨z, hz, -⟩ := (Part.mem_map_iff _).mp hw
      exact ⟨z, (hC y q z).mpr hz⟩
  obtain ⟨c, hc⟩ := exists_ecomplexity_condUniversalPrefix_le_of_partrec₂ hf hpf
  exact ⟨c, fun y z => complexity_le_complexity_add (ecomplexity_condUniversalPrefix_ne_top y z)
    fun q hq => hc y q (φ y z) (Part.mem_map (φ y) ((hC y q z).mp hq))⟩

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
  have hpf : InformationTheory.IsPrefixFree {q | (g q).Dom} :=
    isPrefixFree_universalPrefix.anti fun q h => by
      obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp h
      obtain ⟨n, hn, -⟩ := (Part.mem_map_iff _).mp hx
      exact ⟨n, (hU q n).mpr hn⟩
  obtain ⟨c, hc⟩ := minorizesPrefixPartrec_universalPrefix g hg hpf
  refine ⟨c, fun x => complexity_le_complexity_add (ecomplexity_universalPrefixBits_ne_top x)
    fun p hp => ?_⟩
  obtain ⟨n, hpn, hnx⟩ := map_produces_iff.mp hp
  exact hc p (ψ x) ((Part.mem_map_iff _).mpr ⟨n, (hU p n).mp hpn, congrArg ψ hnx⟩)

private theorem exists_complexity_bits_encode_le_universalPrefixBits :
    ∃ c : ℕ, ∀ x : List Bool,
      universalPrefix.complexity (encode x) ≤ universalPrefixBits.complexity x + c :=
  exists_complexity_universalPrefix_comp_universalPrefixBits_le Primrec.encode.to_comp

private theorem complexity_universalPrefixBits_le_encode (x : List Bool) :
    universalPrefixBits.complexity x ≤ universalPrefix.complexity (encode x) :=
  complexity_le_of_ecomplexity_le <| by
    simpa [universalPrefixBits, encodek] using
      universalPrefix.ecomplexity_map_le (fun n => (decode (α := List Bool) n).getD []) (encode x)

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
  have hpf : ∀ m : ℕ, InformationTheory.IsPrefixFree {q | (f m q).Dom} := fun m =>
    (isPrefixFree_condUniversalPrefix m).anti fun q h => by
      obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp h
      obtain ⟨n, hn, -⟩ := (Part.mem_map_iff _).mp hx
      exact ⟨n, (hC m q n).mpr hn⟩
  obtain ⟨c, hc⟩ := exists_ecomplexity_condUniversalPrefix_le_of_partrec₂ hf hpf
  refine ⟨c, fun y x => complexity_le_complexity_add
    (ecomplexity_condUniversalPrefixBits_ne_top y x) fun p hp => ?_⟩
  obtain ⟨n, hpn, hnx⟩ := map_produces_iff.mp hp
  exact hc (encode y) p (encode x)
    ((Part.mem_map_iff _).mpr ⟨n, (hC (encode y) p n).mp hpn, congrArg encode hnx⟩)

private theorem complexity_condUniversalPrefixBits_le_encode (y x : List Bool) :
    (condUniversalPrefixBits y).complexity x ≤
      (condUniversalPrefix (encode y)).complexity (encode x) :=
  complexity_le_of_ecomplexity_le <| by
    simpa using ecomplexity_condUniversalPrefixBits_le_encode y x

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

private theorem foldr_ite_some_eq_find?_map {α β : Type*} (P : α → Prop) [DecidablePred P]
    (f : α → β) (L : List α) :
    L.foldr (fun a acc => if P a then some (f a) else acc) Option.none =
      (L.find? fun a => P a).map f := by
  induction L with
  | nil => rfl
  | cons hd tl ih => by_cases h : P hd <;> simp [h, ih]

private theorem firstPrefixMatch_eq_find? (r : List Bool) (L : List (List Bool × ℕ)) :
    firstPrefixMatch r L = L.find? fun px => px.1 <+: r :=
  (foldr_ite_some_eq_find?_map (fun px : List Bool × ℕ => px.1 <+: r) id L).trans (by simp)

private theorem firstPrefixMatch_append_of_some {r : List Bool}
    {L₁ L₂ : List (List Bool × ℕ)} {px : List Bool × ℕ}
    (h : firstPrefixMatch r L₁ = some px) :
    firstPrefixMatch r (L₁ ++ L₂) = some px := by
  rw [firstPrefixMatch_eq_find?] at h ⊢
  rw [List.find?_append, h, Option.some_or]

private theorem firstPrefixMatch_spec {r : List Bool} {L : List (List Bool × ℕ)}
    {px : List Bool × ℕ} (h : firstPrefixMatch r L = some px) :
    px ∈ L ∧ px.1 <+: r := by
  rw [firstPrefixMatch_eq_find?] at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

private theorem exists_firstPrefixMatch_of_mem {r : List Bool} {L : List (List Bool × ℕ)}
    {px : List Bool × ℕ} (hmem : px ∈ L) (hp : px.1 <+: r) :
    ∃ px', firstPrefixMatch r L = some px' := by
  rw [firstPrefixMatch_eq_find?, ← Option.isSome_iff_exists, List.find?_isSome]
  exact ⟨px, hmem, decide_eq_true hp⟩

private theorem IsPrefixFree.eq_of_prefix {α : Type*} {M : DescriptionMethod α}
    (hM : M.IsPrefixFree) {p₁ p₂ r : List Bool} {x₁ x₂ : α} (h₁ : M.Produces p₁ x₁)
    (h₂ : M.Produces p₂ x₂) (hp₁ : p₁ <+: r) (hp₂ : p₂ <+: r) : p₁ = p₂ :=
  (List.prefix_or_prefix_of_prefix hp₁ hp₂).elim (hM p₁ ⟨x₁, h₁⟩ p₂ ⟨x₂, h₂⟩)
    fun h => (hM p₂ ⟨x₂, h₂⟩ p₁ ⟨x₁, h₁⟩ h).symm

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
      ∃ p x y, p <+: r ∧ universalPrefix.Produces p x ∧
        (condUniversalPrefix (key (p, x))).Produces (r.drop p.length) y := by
    intro r z hz
    obtain ⟨n, hn⟩ := (Nat.rfindOpt_mono (hmono (r := r))).mp hz
    simp only [chainPairStep, Option.mem_def, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hn
    obtain ⟨⟨p, x⟩, hm, ⟨c, q⟩, hcp, y, hy, rfl⟩ := hn
    obtain ⟨hmem, hp⟩ := firstPrefixMatch_spec hm
    exact ⟨p, x, y, hp, mem_universalPrefixTable_produces hmem, condUniversalPrefix_produces_iff.mpr
      ⟨c, q, hcp, ofPrefixCode_produces_iff.mpr ⟨n, mem_prefixAccepted_iff_lookup.mpr hy⟩⟩⟩
  have hpf : InformationTheory.IsPrefixFree {r | (evalChain r).Dom} := by
    intro r₁ h₁ r₂ h₂ hpref
    obtain ⟨z₁, hz₁⟩ := Part.dom_iff_mem.mp h₁
    obtain ⟨z₂, hz₂⟩ := Part.dom_iff_mem.mp h₂
    obtain ⟨p₁, x₁, y₁, hp₁, hx₁, hy₁⟩ := hspec hz₁
    obtain ⟨p₂, x₂, y₂, hp₂, hx₂, hy₂⟩ := hspec hz₂
    obtain rfl := isPrefixFree_universalPrefix.eq_of_prefix hx₁ hx₂ (hp₁.trans hpref) hp₂
    obtain rfl := hx₁.unique hx₂
    have hdrop := isPrefixFree_condUniversalPrefix (key (p₁, x₁)) _ ⟨y₁, hy₁⟩ _ ⟨y₂, hy₂⟩
      (hpref.drop p₁.length)
    obtain ⟨t₁, rfl⟩ := hp₁
    obtain ⟨t₂, rfl⟩ := hp₂
    rw [List.drop_left, List.drop_left] at hdrop
    rw [hdrop]
  obtain ⟨c, hc⟩ := minorizesPrefixPartrec_universalPrefix evalChain hevalChain hpf
  refine ⟨c, fun p x y hp => ?_⟩
  suffices h : universalPrefix.complexity (Nat.pair x y) ≤
      (condUniversalPrefix (key (p, x))).complexity y + (p.length + c) by omega
  refine complexity_le_complexity_add (ecomplexity_condUniversalPrefix_ne_top _ y) fun q hq => ?_
  obtain ⟨n₁, hn₁⟩ := produces_iff_exists_mem_universalPrefixTable.mp hp
  obtain ⟨c₀, q₀, hcp₀, hq₀⟩ := condUniversalPrefix_produces_iff.mp hq
  obtain ⟨n₂, hn₂⟩ := ofPrefixCode_produces_iff.mp hq₀
  let n := max n₁ n₂
  have hn₁' : (p, x) ∈ universalPrefixTable n :=
    (universalPrefixTable_prefix (le_max_left n₁ n₂)).subset hn₁
  obtain ⟨⟨p', x'⟩, hmatch⟩ := exists_firstPrefixMatch_of_mem hn₁' (List.prefix_append p q)
  obtain ⟨hmem', hp'⟩ := firstPrefixMatch_spec hmatch
  have hx' : universalPrefix.Produces p' x' := mem_universalPrefixTable_produces hmem'
  obtain rfl : p = p' :=
    isPrefixFree_universalPrefix.eq_of_prefix hp hx' (List.prefix_append p q) hp'
  obtain rfl : x = x' := hp.unique hx'
  have hstep : Nat.pair x y ∈ chainPairStep key (p ++ q) n := by
    simp only [chainPairStep, hmatch, Option.bind_some, List.drop_left, hcp₀, Option.mem_def,
      Option.map_eq_some_iff]
    exact ⟨y, mem_prefixAccepted_iff_lookup.mp
      ((prefixAccepted_prefix (c₀.curry (key (p, x))) (le_max_right n₁ n₂)).subset hn₂), rfl⟩
  have hev := hc (p ++ q) (Nat.pair x y) ((Nat.rfindOpt_mono (hmono (r := p ++ q))).mpr ⟨n, hstep⟩)
  rw [List.length_append] at hev
  exact hev.trans_eq (by push_cast; ring)

/-- **Prefix-free chain rule** (no logarithmic overhead): `K(x, y) ≤ K(x) + K(y | x) + c`
[LiVitanyi2019, ShenUspenskyVereshchagin2017]. -/
theorem exists_complexity_universalPrefix_pair_le_add :
    ∃ c : ℕ, ∀ x y : ℕ,
      universalPrefix.complexity (Nat.pair x y) ≤
        universalPrefix.complexity x + (condUniversalPrefix x).complexity y + c := by
  obtain ⟨c, hc⟩ := exists_complexity_universalPrefix_pair_le_add_key Primrec.snd
  refine ⟨c, fun x y => ?_⟩
  obtain ⟨p, hp, hlen⟩ := exists_length_eq_complexity (ecomplexity_universalPrefix_ne_top x)
  simpa [hlen] using hc p x y hp

/-- Prefix-free chain rule conditioned on `(x, K(x))`: `K(x, y) ≤ K(x) + K(y | x, K(x)) + c`. -/
theorem exists_complexity_universalPrefix_pair_le_add_pair :
    ∃ c : ℕ, ∀ x y : ℕ,
      universalPrefix.complexity (Nat.pair x y) ≤
        universalPrefix.complexity x +
          (condUniversalPrefix (Nat.pair x (universalPrefix.complexity x))).complexity y + c := by
  obtain ⟨c, hc⟩ := exists_complexity_universalPrefix_pair_le_add_key
    (Primrec₂.natPair.comp Primrec.snd (Primrec.list_length.comp Primrec.fst))
  refine ⟨c, fun x y => ?_⟩
  obtain ⟨p, hp, hlen⟩ := exists_length_eq_complexity (ecomplexity_universalPrefix_ne_top x)
  simpa [hlen] using hc p x y hp

/-! ### Uniform conditional Kraft–Chaitin theorem -/

/-- **Uniform conditional Kraft–Chaitin theorem**: any jointly computable family of request
streams `req : ℕ → ℕ → Option (ℕ × ℕ)` with Kraft sum at most `1` for every condition `y` yields
one constant `c` with `K(z | y) ≤ ℓ + c` whenever `req y i = some (ℓ, z)`. -/
theorem condKraftChaitin_of_sum_le_one {req : ℕ → ℕ → Option (ℕ × ℕ)} (hreq : Computable₂ req)
    (hbound : ∀ y n : ℕ, ∑ i ∈ Finset.range n,
      (match req y i with | Option.none => (0 : ℝ) | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ) ≤ 1) :
    ∃ c : ℕ, ∀ y i ℓ z, req y i = some (ℓ, z) → (condUniversalPrefix y).ecomplexity z ≤ ℓ + c := by
  have hbound_rat : ∀ y n : ℕ, ∑ i ∈ Finset.range n,
      (match (req y i).map Prod.fst with
      | Option.none => (0 : ℚ) | some ℓ => (2 : ℚ)⁻¹ ^ ℓ) ≤ 1 := by
    intro y n
    rw [← Rat.cast_le (K := ℝ), Rat.cast_sum, Rat.cast_one]
    exact (Finset.sum_congr rfl fun i _ => by cases req y i <;> simp).trans_le (hbound y n)
  let eval : ℕ → List Bool →. ℕ := fun y p => Nat.rfindOpt (kcStreamEval (req y) p)
  have heval : Partrec₂ eval := Partrec.rfindOpt (computable_kcStreamEval hreq)
  have hpf : ∀ y : ℕ, InformationTheory.IsPrefixFree {p | (eval y p).Dom} :=
    fun y => isPrefixFree_rfindOpt_kcStreamEval (req y) (hbound_rat y)
  obtain ⟨c, hc⟩ := exists_ecomplexity_condUniversalPrefix_le_of_partrec₂ heval hpf
  refine ⟨c, fun y i ℓ z hiy => ?_⟩
  obtain ⟨w, hw, hlen⟩ :=
    exists_kcCode_eq_some_of_sum_le_one (hbound_rat y) (i := i) (ℓ := ℓ) (by simp [hiy])
  have hw_eval : z ∈ eval y w := by
    refine (Nat.rfindOpt_mono fun hmn => kcStreamEval_mono (req y) w hmn).mpr ⟨i + 1, ?_⟩
    exact (mem_kcStreamEval_iff (req y) (hbound_rat y) w).mpr
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

private theorem firstProgCand_eq_find? (x k n : ℕ) :
    firstProgCand x k n =
      ((universalPrefixTable n).find? fun py => py.2 = x ∧ py.1.length = k).map Prod.fst :=
  foldr_ite_some_eq_find?_map (fun py : List Bool × ℕ => py.2 = x ∧ py.1.length = k) Prod.fst _

private theorem firstProgCand_spec {x k n : ℕ} {p : List Bool}
    (h : firstProgCand x k n = some p) :
    universalPrefix.Produces p x ∧ p.length = k := by
  rw [firstProgCand_eq_find?] at h
  obtain ⟨⟨p', x'⟩, hfind, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨rfl, hlen⟩ : x' = x ∧ p'.length = k := by simpa using List.find?_some hfind
  exact ⟨mem_universalPrefixTable_produces (List.mem_of_find?_eq_some hfind), hlen⟩

private theorem exists_firstProgCand_of_produces {x k : ℕ} {p : List Bool}
    (hp : universalPrefix.Produces p x) (hlen : p.length = k) :
    ∃ n p', firstProgCand x k n = some p' := by
  obtain ⟨n, hn⟩ := produces_iff_exists_mem_universalPrefixTable.mp hp
  refine ⟨n, ?_⟩
  rw [firstProgCand_eq_find?, ← Option.isSome_iff_exists, Option.isSome_map, List.find?_isSome]
  exact ⟨(p, x), hn, by simpa using hlen⟩

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
    rw [Option.mem_def, firstProgCand_eq_find?] at hz ⊢
    rw [← htail, List.find?_append, Option.map_or, hz, Option.some_or]
  simpa [firstProgSearch] using Nat.rfindOpt_mono hmono

private theorem dom_firstProgSearch_complexity (x : ℕ) :
    (firstProgSearch (Nat.pair x (universalPrefix.complexity x))).Dom := by
  obtain ⟨p, hp, hplen⟩ := exists_length_eq_complexity (ecomplexity_universalPrefix_ne_top x)
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

/-- Canonical prefix-free program `shortestPrefixProgram (encode x)` for `x : List Bool`.
It produces `x` under `universalPrefixBits` with length `universalPrefix.complexity (encode x)`
(minimizing `universalPrefix` program length on `encode x`; at `x = []` this need not achieve the
minimum `universalPrefixBits` length because `decode (α := List Bool) n = none` defaults to `[]`
in `universalPrefixBits`). -/
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
  classical
  have hex : ∃ m : ℕ, (p, z) ∈ universalPrefixTable m := ⟨n, hn⟩
  let m₀ := Nat.find hex
  have hm₀ : (p, z) ∈ universalPrefixTable m₀ := Nat.find_spec hex
  obtain ⟨i, hi⟩ : ∃ i, m₀ = i + 1 :=
    Nat.exists_eq_succ_of_ne_zero fun h0 => by rw [h0] at hm₀; cases hm₀
  have hnot : (p, z) ∉ universalPrefixTable i := Nat.find_min hex (by omega)
  obtain ⟨j, hj, hfj⟩ := Nat.mem_distinctValues.mp (hi ▸ hm₀)
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
  · exact (hnot (Nat.mem_distinctValues.mpr ⟨j, hlt, hfj⟩)).elim
  · refine ⟨j, ?_⟩
    have htab : universalPrefixTable (j + 1) = universalPrefixTable j ++ [(p, z)] := by
      change Nat.distinctValues universalPrefixCand (j + 1) =
        Nat.distinctValues universalPrefixCand j ++ [(p, z)]
      rw [Nat.distinctValues, hfj]
      simp [show (p, z) ∉ Nat.distinctValues universalPrefixCand j from hnot]
    simp [prefixTableNew, htab, hfj]

private theorem exists_universalMarginal_le_two_pow :
    ∃ c₁ : ℕ, ∀ x : ℕ,
      ∑' y : ℕ, universalPrefix.universalProb (Nat.pair x y) ≤
        (2 : ℝ) ^ c₁ * (2 : ℝ)⁻¹ ^ universalPrefix.complexity x :=
  exists_le_two_pow_mul_universalPrefix_of_isLowerSemicomputable
    (fun _ => tsum_nonneg fun _ => universalProb_nonneg _ _)
    isPrefixFree_universalPrefix.summable_universalProb_marginal
    isPrefixFree_universalPrefix.tsum_universalProb_pair_le_one
    isLowerSemicomputable_universalProb_marginal

private def symProgs (x n : ℕ) : List (List Bool) :=
  (universalPrefixTable n).flatMap fun pz => if pz.2.unpair.1 = x then [pz.1] else []

private def symReq (c₁ xk i : ℕ) : Option (ℕ × ℕ) :=
  match prefixTableNew i with
  | Option.none => Option.none
  | some (p, z) =>
    if z.unpair.1 = xk.unpair.1 ∧
        codeScaledSum (symProgs xk.unpair.1 (i + 1)) * 2 ^ xk.unpair.2 ≤
          2 ^ (codeMaxLen (symProgs xk.unpair.1 (i + 1)) + c₁) then
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

private theorem primrec₂_symReq (c₁ : ℕ) : Primrec₂ (symReq c₁) := by
  have hbranch : Primrec₂ fun (xki : ℕ × ℕ) (pz : List Bool × ℕ) =>
      if pz.2.unpair.1 = xki.1.unpair.1 ∧
          codeScaledSum (symProgs xki.1.unpair.1 (xki.2 + 1)) * 2 ^ xki.1.unpair.2 ≤
            2 ^ (codeMaxLen (symProgs xki.1.unpair.1 (xki.2 + 1)) + c₁) then
        some (pz.1.length + c₁ - xki.1.unpair.2, pz.2.unpair.2)
      else Option.none := by
    have hx : Primrec fun arg : (ℕ × ℕ) × (List Bool × ℕ) => arg.1.1.unpair.1 :=
      Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.fst))
    have hk : Primrec fun arg : (ℕ × ℕ) × (List Bool × ℕ) => arg.1.1.unpair.2 :=
      Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.fst))
    have hi1 : Primrec fun arg : (ℕ × ℕ) × (List Bool × ℕ) => arg.1.2 + 1 :=
      Primrec.succ.comp (Primrec.snd.comp Primrec.fst)
    have hprogs : Primrec fun arg : (ℕ × ℕ) × (List Bool × ℕ) =>
        symProgs arg.1.1.unpair.1 (arg.1.2 + 1) :=
      primrec₂_symProgs.comp hx hi1
    have hp1 : PrimrecPred fun arg : (ℕ × ℕ) × (List Bool × ℕ) =>
        arg.2.2.unpair.1 = arg.1.1.unpair.1 :=
      Primrec.eq.comp
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.snd))) hx
    have hp2 : PrimrecPred fun arg : (ℕ × ℕ) × (List Bool × ℕ) =>
        codeScaledSum (symProgs arg.1.1.unpair.1 (arg.1.2 + 1)) * 2 ^ arg.1.1.unpair.2 ≤
          2 ^ (codeMaxLen (symProgs arg.1.1.unpair.1 (arg.1.2 + 1)) + c₁) :=
      Primrec.nat_le.comp
        (Primrec.nat_mul.comp (primrec_codeScaledSum.comp hprogs) (primrec_two_pow.comp hk))
        (primrec_two_pow.comp
          (Primrec.nat_add.comp (primrec_codeMaxLen.comp hprogs) (Primrec.const c₁)))
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

private theorem symProgs_eq_map_filter (x n : ℕ) :
    symProgs x n = ((universalPrefixTable n).filter fun pz => pz.2.unpair.1 = x).map Prod.fst := by
  rw [symProgs]
  induction universalPrefixTable n with
  | nil => rfl
  | cons hd tl ih => by_cases h : hd.2.unpair.1 = x <;> simp [h, ih]

private theorem mem_symProgs_iff {x n : ℕ} {w : List Bool} :
    w ∈ symProgs x n ↔ ∃ z, (w, z) ∈ universalPrefixTable n ∧ z.unpair.1 = x := by
  simp [symProgs_eq_map_filter]

private theorem nodup_symProgs (x n : ℕ) : (symProgs x n).Nodup := by
  rw [symProgs_eq_map_filter]
  exact (nodup_map_fst_universalPrefixTable n).sublist (List.filter_sublist.map Prod.fst)

private theorem sum_symProgs_le_of_scaled {c₁ x k n : ℕ}
    (h : codeScaledSum (symProgs x n) * 2 ^ k ≤ 2 ^ (codeMaxLen (symProgs x n) + c₁)) :
    ∑ w ∈ (symProgs x n).toFinset, (2 : ℝ)⁻¹ ^ w.length ≤
      (2 : ℝ) ^ c₁ * (2 : ℝ)⁻¹ ^ k := by
  have hreal : ((codeScaledSum (symProgs x n) : ℕ) : ℝ) * (2 : ℝ) ^ k ≤
      (2 : ℝ) ^ (codeMaxLen (symProgs x n) + c₁) := mod_cast h
  rw [natCast_codeScaledSum,
    ← List.sum_toFinset (fun w : List Bool => (2 : ℝ)⁻¹ ^ w.length) (nodup_symProgs x n),
    mul_right_comm, pow_add, mul_comm ((2 : ℝ) ^ codeMaxLen (symProgs x n))] at hreal
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  exact le_of_mul_le_mul_right hreal (by positivity)

private theorem symScaled_mul_le_of_universalMarginal {c₁ x n : ℕ}
    (hmarg : ∑' y : ℕ, universalPrefix.universalProb (Nat.pair x y) ≤
      (2 : ℝ) ^ c₁ * (2 : ℝ)⁻¹ ^ universalPrefix.complexity x) :
    codeScaledSum (symProgs x n) * 2 ^ universalPrefix.complexity x ≤
      2 ^ (codeMaxLen (symProgs x n) + c₁) := by
  classical
  let T := (symProgs x n).toFinset
  have hT : ∀ w ∈ T, ∃ z, universalPrefix.Produces w z ∧ z.unpair.1 = x := fun w hw => by
    obtain ⟨z, hz, hzx⟩ := mem_symProgs_iff.mp (List.mem_toFinset.mp hw)
    exact ⟨z, mem_universalPrefixTable_produces hz, hzx⟩
  let emb : {w : List Bool // w ∈ T} →
      (y : ℕ) × {p : List Bool // universalPrefix.Produces p (Nat.pair x y)} := fun w =>
    let z := (hT w.1 w.2).choose
    ⟨z.unpair.2, w.1, by
      obtain ⟨hp, hx⟩ := (hT w.1 w.2).choose_spec
      rwa [show Nat.pair x z.unpair.2 = z by rw [← hx, Nat.pair_unpair]]⟩
  have hemb : Function.Injective emb := fun a b hab =>
    Subtype.ext (congrArg (fun q : (y : ℕ) ×
      {p : List Bool // universalPrefix.Produces p (Nat.pair x y)} => q.2.1) hab)
  let F := T.attach.map ⟨emb, hemb⟩
  have hs := summable_universalPrefix_produces_pair x
  have htsum : ∑' q : (y : ℕ) × {p : List Bool // universalPrefix.Produces p (Nat.pair x y)},
      (2 : ℝ)⁻¹ ^ q.2.1.length = ∑' y : ℕ, universalPrefix.universalProb (Nat.pair x y) :=
    hs.tsum_sigma' fun _ => isPrefixFree_universalPrefix.summable_universalProb_program _
  have hsum_F : ∑ w ∈ T, (2 : ℝ)⁻¹ ^ w.length = ∑ q ∈ F, (2 : ℝ)⁻¹ ^ q.2.1.length := by
    rw [Finset.sum_map]
    exact (Finset.sum_attach T fun w => (2 : ℝ)⁻¹ ^ w.length).symm
  have hsum_le : ∑ w ∈ T, (2 : ℝ)⁻¹ ^ w.length ≤
      (2 : ℝ) ^ c₁ * (2 : ℝ)⁻¹ ^ universalPrefix.complexity x :=
    hsum_F.trans_le ((hs.sum_le_tsum F fun _ _ => by positivity).trans (htsum.trans_le hmarg))
  have hreal : ((codeScaledSum (symProgs x n) * 2 ^ universalPrefix.complexity x : ℕ) : ℝ) ≤
      ((2 ^ (codeMaxLen (symProgs x n) + c₁) : ℕ) : ℝ) := by
    push_cast
    rw [natCast_codeScaledSum,
      ← List.sum_toFinset (fun w : List Bool => (2 : ℝ)⁻¹ ^ w.length) (nodup_symProgs x n), pow_add]
    refine (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hsum_le (pow_nonneg (by norm_num) _))
      (pow_nonneg (by norm_num) _)).trans_eq ?_
    rw [mul_right_comm, mul_assoc ((2 : ℝ) ^ c₁), ← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow,
      mul_one, mul_comm]
  exact_mod_cast hreal

private theorem symReq_sum_le_one (c₁ xk n : ℕ) :
    ∑ i ∈ Finset.range n,
      (match symReq c₁ xk i with | Option.none => (0 : ℝ) | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ) ≤ 1 := by
  classical
  set x := xk.unpair.1
  set k := xk.unpair.2
  let f (i : ℕ) : ℝ :=
    match symReq c₁ xk i with | Option.none => 0 | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ
  let I := (Finset.range n).filter fun i => (symReq c₁ xk i).isSome
  change ∑ i ∈ Finset.range n, f i ≤ 1
  have hsum_I : ∑ i ∈ Finset.range n, f i = ∑ i ∈ I, f i := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun i _ => by dsimp only [f]; cases symReq c₁ xk i <;> simp
  rw [hsum_I]
  rcases I.eq_empty_or_nonempty with hI | hne
  · simp [hI]
  have hsym {i : ℕ} (hi : i ∈ I) : ∃ p z, prefixTableNew i = some (p, z) ∧ z.unpair.1 = x ∧
      codeScaledSum (symProgs x (i + 1)) * 2 ^ k ≤
        2 ^ (codeMaxLen (symProgs x (i + 1)) + c₁) ∧
      f i = (2 : ℝ)⁻¹ ^ (p.length + c₁ - k) := by
    obtain ⟨⟨ℓ, y⟩, hseq⟩ := Option.isSome_iff_exists.mp (Finset.mem_filter.mp hi).2
    have hseq' := hseq
    dsimp only [symReq] at hseq'
    rcases hpt : prefixTableNew i with _ | ⟨p, z⟩
    · simp [hpt] at hseq'
    · simp only [hpt] at hseq'
      split_ifs at hseq' with hg
      obtain ⟨rfl, rfl⟩ := Option.some.inj hseq'
      exact ⟨p, z, rfl, hg.1, hg.2, by simp [f, hseq]; rfl⟩
  let i₀ := I.max' hne
  obtain ⟨_, _, _, _, hi₀_guard, _⟩ := hsym (Finset.max'_mem I hne)
  let prog (i : ℕ) : List Bool := ((prefixTableNew i).map Prod.fst).getD []
  have hprog_mem {i : ℕ} (hi : i ∈ I) : prog i ∈ (symProgs x (i₀ + 1)).toFinset := by
    obtain ⟨p, z, hpt, hzx, -, -⟩ := hsym hi
    have hmem : (p, z) ∈ universalPrefixTable (i + 1) := by
      simp [(prefixTableNew_eq_some_iff hpt).1]
    have hmem0 :=
      (universalPrefixTable_prefix (Nat.succ_le_succ (Finset.le_max' I i hi))).subset hmem
    simpa [prog, hpt] using List.mem_toFinset.mpr (mem_symProgs_iff.mpr ⟨z, hmem0, hzx⟩)
  have hinj : Set.InjOn prog I := fun i hi j hj hp => by
    obtain ⟨pi, zi, hpti, -, -, -⟩ := hsym hi
    obtain ⟨pj, zj, hptj, -, -, -⟩ := hsym hj
    have hpeq : pi = pj := by simpa [prog, hpti, hptj] using hp
    subst hpeq
    have hti := prefixTableNew_eq_some_iff hpti
    have htj := prefixTableNew_eq_some_iff hptj
    have hmi : (pi, zi) ∈ universalPrefixTable (i + 1) := by simp [hti.1]
    have hmj : (pi, zj) ∈ universalPrefixTable (j + 1) := by simp [htj.1]
    obtain rfl : zi = zj :=
      (mem_universalPrefixTable_produces hmi).unique (mem_universalPrefixTable_produces hmj)
    rcases lt_trichotomy i j with hlt | rfl | hlt
    · exact (htj.2 ((universalPrefixTable_prefix (Nat.succ_le_of_lt hlt)).subset hmi)).elim
    · rfl
    · exact (hti.2 ((universalPrefixTable_prefix (Nat.succ_le_of_lt hlt)).subset hmj)).elim
  have hterm {i : ℕ} (hi : i ∈ I) :
      f i ≤ (2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ c₁ * (2 : ℝ)⁻¹ ^ (prog i).length := by
    obtain ⟨p, _, hpt, -, -, hfi⟩ := hsym hi
    have hsub : (2 : ℝ)⁻¹ ^ (p.length + c₁ - k) ≤ 2 ^ k * (2 : ℝ)⁻¹ ^ (p.length + c₁) := by
      have h1 : (2 : ℝ)⁻¹ ^ (p.length + c₁ - k) =
          2 ^ k * (2 : ℝ)⁻¹ ^ (p.length + c₁ - k + k) := by
        rw [pow_add, mul_left_comm, ← mul_pow, mul_inv_cancel₀ two_ne_zero, one_pow, mul_one]
      rw [h1]
      gcongr 2 ^ k * ?_
      exact pow_le_pow_of_le_one (by positivity) (by norm_num) (by omega)
    rw [hfi, show prog i = p by simp [prog, hpt]]
    exact hsub.trans_eq (by rw [pow_add]; ring)
  calc ∑ i ∈ I, f i
      ≤ ∑ i ∈ I, (2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ c₁ * (2 : ℝ)⁻¹ ^ (prog i).length :=
        Finset.sum_le_sum fun i hi => hterm hi
    _ = (2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ c₁ * ∑ w ∈ I.image prog, (2 : ℝ)⁻¹ ^ w.length := by
        rw [← Finset.mul_sum, Finset.sum_image hinj]
    _ ≤ (2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ c₁ *
          ∑ w ∈ (symProgs x (i₀ + 1)).toFinset, (2 : ℝ)⁻¹ ^ w.length :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.image_subset_iff.mpr fun i hi => hprog_mem hi) fun _ _ _ => by positivity)
          (by positivity)
    _ ≤ (2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ c₁ * ((2 : ℝ) ^ c₁ * (2 : ℝ)⁻¹ ^ k) :=
        mul_le_mul_of_nonneg_left (sum_symProgs_le_of_scaled hi₀_guard) (by positivity)
    _ = ((2 : ℝ) * (2 : ℝ)⁻¹) ^ k * ((2 : ℝ)⁻¹ * (2 : ℝ)) ^ c₁ := by rw [mul_pow, mul_pow]; ring
    _ = 1 := by norm_num

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
  obtain ⟨p, hp, hp_nat⟩ :=
    exists_length_eq_complexity (ecomplexity_universalPrefix_ne_top (Nat.pair x y))
  obtain ⟨i, hi⟩ := exists_prefixTableNew_of_produces hp
  have hguard := symScaled_mul_le_of_universalMarginal (n := i + 1) (hmarg x)
  have hcond : (condUniversalPrefix (Nat.pair x (universalPrefix.complexity x))).complexity y ≤
      p.length + c₁ - universalPrefix.complexity x + c_kc :=
    complexity_le_of_ecomplexity_le (mod_cast hkc
      (Nat.pair x (universalPrefix.complexity x)) i
      (p.length + c₁ - universalPrefix.complexity x) y (by simp [symReq, hi, hguard]))
  rw [hp_nat] at hcond
  have hkx : universalPrefix.complexity x ≤
      universalPrefix.complexity (Nat.pair x y) + c_fst := by simpa using hfst (Nat.pair x y)
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
  have hbits_mem (n : ℕ) : n.bits ∈ natBitsPart n := by
    have hdom : (natBitsPart n).Dom := Nat.rfindOpt_dom.mpr <| by
      by_cases hn : n = 0
      · exact ⟨0, [], by simp [bitsStep, hn]⟩
      · obtain ⟨w, hw⟩ := exists_foldr_bit_one hn
        exact ⟨encode w, w ++ [true], by simp [bitsStep, hn, hw]⟩
    obtain ⟨t, ht⟩ := Nat.rfindOpt_spec (Part.get_mem hdom)
    suffices Part.get (natBitsPart n) hdom = n.bits from this ▸ Part.get_mem hdom
    dsimp only [bitsStep] at ht
    split_ifs at ht with hn
    · simp_all
    · obtain ⟨w, _, hw⟩ := Option.bind_eq_some_iff.mp ht
      split_ifs at hw with hfld
      simp only [Option.some.injEq] at hw
      rw [← hw, ← hfld, Nat.bits_foldr_bit_one]
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
          (primrec_list_replicate_bool.comp (Primrec.list_length.comp Primrec.snd)
            (Primrec.const true))
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
    exact (complexity_universalPrefixBits_le_encode _).trans (hc_pair _ _ <|
      Part.mem_bind_iff.mpr ⟨x, by simp, Part.mem_bind_iff.mpr ⟨y, by simp,
        (Part.mem_map_iff _).mpr ⟨x.length.bits, hbits_mem x.length,
          by rw [Nat.size_eq_bits_len]; rfl⟩⟩⟩)
  have hx_lo := h₂ x
  have hx_hi := complexity_universalPrefixBits_le_encode x
  have hcond_lo := h₃ (shortestPrefixProgramBits x) y
  have hcond_hi := complexity_condUniversalPrefixBits_le_encode (shortestPrefixProgramBits x) y
  dsimp only [shortestPrefixProgramBits] at hcond_lo hcond_hi ⊢
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
