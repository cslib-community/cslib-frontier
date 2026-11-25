/-
Copyright (c) 2026 Matthew Doty, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Kolmogorov.ChaitinOmega
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CslibFrontier.Foundations.Data.List.FoldMax
import CslibFrontier.Foundations.Data.List.Primrec
import Mathlib.Computability.Primrec.List

/-!
# Algorithmic probability and Levin's coding theorem

For any description method `M : DescriptionMethod α`, the *algorithmic* (or *a priori*)
*probability* of `x : α` is the probability that a prefix-free program halts with output `x`:

  `M.universalProb x = ∑' p : {p : List Bool // M.Produces p x}, (2 : ℝ)⁻¹ ^ p.1.length`.

When `M` is prefix-free (`M.IsPrefixFree`), the fibers `{p // M.Produces p x}` partition
`M.haltingSet`, so `∑' x, M.universalProb x = M.chaitinOmega ≤ 1`
(`IsPrefixFree.tsum_universalProb_eq_chaitinOmega`).

A nonnegative summable function `μ : α → ℝ` with `∑' x, μ x ≤ 1` is *lower semicomputable*
(`IsLowerSemicomputable μ`) when its strict nonnegative rational lower graph
`{(x, a, b) | (a : ℝ) / (b + 1) < μ x}` (`a, b : ℕ`) is recursively enumerable (`REPred`).

Using the online **Kraft–Chaitin theorem** (`CslibFrontier.Computability.Kolmogorov.KraftChaitin`),
every lower-semicomputable discrete semimeasure satisfies `K(x) ≤ -log₂ μ(x) + O(1)`
(`exists_le_two_pow_mul_universalPrefix_of_isLowerSemicomputable`,
`exists_complexity_universalPrefix_le_neg_logb_of_isLowerSemicomputable`). Since `universalProb` is
lower semicomputable for every prefix-free partial recursive machine (`universalPrefix`,
`universalPrefixBits`, and also the marginal semimeasure `fun x => ∑' y, m (Nat.pair x y)`),
this yields **Levin's coding theorem** [LiVitanyi2019, ShenUspenskyVereshchagin2017]:

  `2⁻¹ ^ K(x) ≤ m(x) ≤ 2 ^ c * 2⁻¹ ^ K(x)` and `|K(x) + log₂ m(x)| ≤ c`,

and universality of `universalPrefix.universalProb` and `universalPrefixBits.universalProb`
among all lower-semicomputable discrete semimeasures.

## Main definitions

* `Cslib.Kolmogorov.DescriptionMethod.universalProb`: algorithmic probability `m_M(x)`.
* `Cslib.Kolmogorov.IsLowerSemicomputable`: lower-semicomputability via r.e. rational lower graph.

## Main results

* `Cslib.Kolmogorov.DescriptionMethod.IsPrefixFree.tsum_universalProb_eq_chaitinOmega`:
  `∑' x, M.universalProb x = M.chaitinOmega`.
* `Cslib.Kolmogorov.DescriptionMethod.two_inv_pow_complexity_le_universalProb`:
  `2⁻¹ ^ K_M(x) ≤ M.universalProb x`.
* `Cslib.Kolmogorov.isLowerSemicomputable_universalProb_of_partrec_eval`,
  `Cslib.Kolmogorov.isLowerSemicomputable_universalProb_universalPrefix`,
  `Cslib.Kolmogorov.isLowerSemicomputable_universalProb_universalPrefixBits`,
  `Cslib.Kolmogorov.isLowerSemicomputable_universalProb_marginal`: lower semicomputability of
  algorithmic probability and its marginal.
* `Cslib.Kolmogorov.exists_le_complexity_of_isLowerSemicomputable`,
  `MinorizesPrefixPartrec.exists_le_two_pow_mul_complexity_of_isLowerSemicomputable`,
  `Cslib.Kolmogorov.exists_le_two_pow_mul_universalPrefix_of_isLowerSemicomputable`,
  `Cslib.Kolmogorov.exists_complexity_universalPrefix_le_neg_logb_of_isLowerSemicomputable`:
  coding upper bound `μ(x) ≤ 2^c · 2⁻¹ ^ K(x)` (`K(x) ≤ -log₂ μ(x) + c`).
* `Cslib.Kolmogorov.levin_coding_universalPrefix`,
  `Cslib.Kolmogorov.levin_coding_universalPrefixBits`,
  `Cslib.Kolmogorov.exists_abs_complexity_add_logb_universalProb_universalPrefix_le`,
  `Cslib.Kolmogorov.exists_abs_complexity_add_logb_universalProb_universalPrefixBits_le`,
  `Cslib.Kolmogorov.exists_mul_universalProb_universalPrefix_ge`,
  `Cslib.Kolmogorov.exists_mul_universalProb_universalPrefixBits_ge`: **Levin's coding theorem**
  and universality of the Solomonoff–Levin prior.

## References

* [M. Li, P. Vitányi, *An Introduction to Kolmogorov Complexity and Its
  Applications*][LiVitanyi2019]
* [A. Shen, V. A. Uspensky, N. Vereshchagin, *Kolmogorov Complexity and Algorithmic
  Randomness*][ShenUspenskyVereshchagin2017]
-/

public section

open scoped BigOperators Filter Topology

namespace Cslib.Kolmogorov

open Encodable Denumerable Nat.Partrec Filter

namespace DescriptionMethod

/-! ### Algorithmic probability -/

/-- Algorithmic (*a priori*) probability `m_M(x) = ∑' {p // M.Produces p x}, 2⁻¹ ^ |p|`
[LiVitanyi2019]. -/
@[expose] noncomputable def universalProb {α : Type*} (M : DescriptionMethod α) (x : α) : ℝ :=
  ∑' p : {p : List Bool // M.Produces p x}, (2 : ℝ)⁻¹ ^ p.1.length

theorem universalProb_nonneg {α : Type*} (M : DescriptionMethod α) (x : α) :
    0 ≤ M.universalProb x :=
  tsum_nonneg fun _ => by positivity

theorem IsPrefixFree.summable_universalProb_program {α : Type*} {M : DescriptionMethod α}
    (hM : M.IsPrefixFree) (x : α) :
    Summable fun p : {p : List Bool // M.Produces p x} => (2 : ℝ)⁻¹ ^ p.1.length := by
  let f : {p : List Bool // M.Produces p x} → M.haltingSet := fun p => ⟨p.1, x, p.2⟩
  have hf : Function.Injective f := fun _ _ hab =>
    Subtype.ext (congrArg (fun z : M.haltingSet => z.1) hab)
  exact hM.summable_two_inv_pow_length.comp_injective hf

theorem IsPrefixFree.universalProb_le_chaitinOmega {α : Type*} {M : DescriptionMethod α}
    (hM : M.IsPrefixFree) (x : α) : M.universalProb x ≤ M.chaitinOmega := by
  let f : {p : List Bool // M.Produces p x} → M.haltingSet := fun p => ⟨p.1, x, p.2⟩
  have hf : Function.Injective f := fun _ _ h =>
    Subtype.ext (congrArg (fun z : M.haltingSet => z.1) h)
  exact (hM.summable_universalProb_program x).tsum_le_tsum_of_inj f hf
    (fun _ _ => by positivity) (fun _ => le_rfl) hM.summable_two_inv_pow_length

theorem IsPrefixFree.universalProb_le_one {α : Type*} {M : DescriptionMethod α}
    (hM : M.IsPrefixFree) (x : α) : M.universalProb x ≤ 1 :=
  (hM.universalProb_le_chaitinOmega x).trans hM.chaitinOmega_le_one

private theorem sigma_subtype_ext {α β : Type*} {P : α → β → Prop}
    {x₁ x₂ : α} (hx : x₁ = x₂) {b : β} {h₁ : P x₁ b} {h₂ : P x₂ b} :
    (⟨x₁, ⟨b, h₁⟩⟩ : (x : α) × {b // P x b}) = ⟨x₂, ⟨b, h₂⟩⟩ := by
  subst hx
  rfl

private noncomputable def haltingSigmaEquiv {α : Type*} (M : DescriptionMethod α) :
    (x : α) × {p : List Bool // M.Produces p x} ≃ M.haltingSet where
  toFun xp := ⟨xp.2.1, xp.1, xp.2.2⟩
  invFun q := ⟨q.2.choose, q.1, q.2.choose_spec⟩
  left_inv xp := by
    rcases xp with ⟨x, ⟨p, hp⟩⟩
    exact sigma_subtype_ext (P := fun x p => M.Produces p x)
      ((hp.unique (⟨x, hp⟩ : p ∈ M.haltingSet).choose_spec).symm)
  right_inv q := by
    rcases q with ⟨p, hq⟩
    rfl

private theorem summable_haltingSigmaEquiv {α : Type*} {M : DescriptionMethod α}
    (hM : M.IsPrefixFree) :
    Summable fun xp : (x : α) × {p : List Bool // M.Produces p x} =>
      (2 : ℝ)⁻¹ ^ xp.2.1.length :=
  (Equiv.summable_iff (haltingSigmaEquiv M)).mpr hM.summable_two_inv_pow_length

theorem IsPrefixFree.summable_universalProb {α : Type*} {M : DescriptionMethod α}
    (hM : M.IsPrefixFree) : Summable M.universalProb := by
  classical
  exact (summable_haltingSigmaEquiv hM).sigma

/-- The total algorithmic probability across all outputs equals Chaitin's halting probability
`Ω`. -/
theorem IsPrefixFree.tsum_universalProb_eq_chaitinOmega {α : Type*} {M : DescriptionMethod α}
    (hM : M.IsPrefixFree) : ∑' x : α, M.universalProb x = M.chaitinOmega := by
  classical
  calc ∑' x : α, M.universalProb x
      = ∑' xp : (x : α) × {p : List Bool // M.Produces p x}, (2 : ℝ)⁻¹ ^ xp.2.1.length :=
        ((summable_haltingSigmaEquiv hM).tsum_sigma'
          (fun x => hM.summable_universalProb_program x)).symm
    _ = M.chaitinOmega := (haltingSigmaEquiv M).tsum_eq fun q => (2 : ℝ)⁻¹ ^ q.1.length

private def natPairSigmaEquiv : (Σ _ : ℕ, ℕ) ≃ ℕ where
  toFun xy := Nat.pair xy.1 xy.2
  invFun z := ⟨z.unpair.1, z.unpair.2⟩
  left_inv := fun ⟨_, _⟩ => by simp
  right_inv := Nat.pair_unpair

private theorem summable_universalProb_natPairSigma {M : DescriptionMethod ℕ}
    (hM : M.IsPrefixFree) :
    Summable fun xy : Σ _ : ℕ, ℕ => M.universalProb (Nat.pair xy.1 xy.2) :=
  (Equiv.summable_iff natPairSigmaEquiv).mpr hM.summable_universalProb

/-- Summability of `y ↦ M.universalProb (Nat.pair x y)` for a prefix-free method `M` on `ℕ`. -/
theorem IsPrefixFree.summable_universalProb_pair {M : DescriptionMethod ℕ}
    (hM : M.IsPrefixFree) (x : ℕ) :
    Summable fun y : ℕ => M.universalProb (Nat.pair x y) :=
  (summable_universalProb_natPairSigma hM).sigma_factor x

/-- Summability of the first-coordinate marginal `x ↦ ∑' y, M.universalProb (Nat.pair x y)` for a
prefix-free method `M` on `ℕ`. -/
theorem IsPrefixFree.summable_universalProb_marginal {M : DescriptionMethod ℕ}
    (hM : M.IsPrefixFree) :
    Summable fun x : ℕ => ∑' y : ℕ, M.universalProb (Nat.pair x y) :=
  (summable_universalProb_natPairSigma hM).sigma

/-- The iterated pair sum `∑' x, ∑' y, M.universalProb (Nat.pair x y)` of a prefix-free method on
`ℕ` is at most `1`. -/
theorem IsPrefixFree.tsum_universalProb_pair_le_one {M : DescriptionMethod ℕ}
    (hM : M.IsPrefixFree) :
    (∑' x : ℕ, ∑' y : ℕ, M.universalProb (Nat.pair x y)) ≤ 1 := by
  have hs := summable_universalProb_natPairSigma hM
  calc ∑' x : ℕ, ∑' y : ℕ, M.universalProb (Nat.pair x y)
      = ∑' xy : Σ _ : ℕ, ℕ, M.universalProb (Nat.pair xy.1 xy.2) :=
        (hs.tsum_sigma' fun x => hM.summable_universalProb_pair x).symm
    _ = ∑' z : ℕ, M.universalProb z := natPairSigmaEquiv.tsum_eq M.universalProb
    _ = M.chaitinOmega := hM.tsum_universalProb_eq_chaitinOmega
    _ ≤ 1 := hM.chaitinOmega_le_one

/-- Shortest-program lower bound: `2⁻¹ ^ K_M(x) ≤ M.universalProb x` for every prefix-free
method whenever `M.ecomplexity x ≠ ⊤`. -/
theorem two_inv_pow_complexity_le_universalProb {α : Type*} {M : DescriptionMethod α}
    (hM : M.IsPrefixFree) {x : α} (hx : M.ecomplexity x ≠ ⊤) :
    (2 : ℝ)⁻¹ ^ M.complexity x ≤ M.universalProb x := by
  obtain ⟨p, hp, hlen⟩ := exists_length_eq_ecomplexity hx
  have hplen : p.length = M.complexity x :=
    ENat.natCast_inj.mp (hlen.trans (natCast_complexity hx).symm)
  exact hplen ▸ (hM.summable_universalProb_program x).le_tsum ⟨p, hp⟩ fun _ _ => by positivity

theorem two_inv_pow_complexity_universalPrefix_le (x : ℕ) :
    (2 : ℝ)⁻¹ ^ universalPrefix.complexity x ≤ universalPrefix.universalProb x :=
  two_inv_pow_complexity_le_universalProb isPrefixFree_universalPrefix
    (ecomplexity_universalPrefix_ne_top x)

theorem two_inv_pow_complexity_universalPrefixBits_le (x : List Bool) :
    (2 : ℝ)⁻¹ ^ universalPrefixBits.complexity x ≤ universalPrefixBits.universalProb x :=
  two_inv_pow_complexity_le_universalProb isPrefixFree_universalPrefixBits
    (ecomplexity_universalPrefixBits_ne_top x)

theorem universalProb_universalPrefix_pos (x : ℕ) : 0 < universalPrefix.universalProb x :=
  lt_of_lt_of_le (by positivity) (two_inv_pow_complexity_universalPrefix_le x)

theorem universalProb_universalPrefixBits_pos (x : List Bool) :
    0 < universalPrefixBits.universalProb x :=
  lt_of_lt_of_le (by positivity) (two_inv_pow_complexity_universalPrefixBits_le x)

end DescriptionMethod

open DescriptionMethod

/-! ### Lower-semicomputable discrete semimeasures -/

/-- A nonnegative function `μ : α → ℝ` is *lower semicomputable* when its strict nonnegative
rational lower graph `{(x, a, b) | (a : ℝ) / (b + 1) < μ x}` (`a, b : ℕ`, testing `ℚ≥0`) is
recursively enumerable (`REPred`). For nonnegative `μ`, every negative rational is trivially below
`μ x`, so restricting numerators to `a : ℕ` characterizes lower semicomputability on `ℝ≥0`-valued
functions. -/
@[expose] def IsLowerSemicomputable {α : Type*} [Primcodable α] (μ : α → ℝ) : Prop :=
  REPred fun p : α × ℕ × ℕ =>
    match p with
    | (x, a, b) => (a : ℝ) / ((b + 1 : ℕ) : ℝ) < μ x

/-- A function approximated monotonically from below by computable integer fractions `num x t /
den x t` is lower semicomputable. -/
theorem isLowerSemicomputable_of_computable_monotone_tendsto {α : Type*} [Primcodable α]
    {μ : α → ℝ} {num den : α → ℕ → ℕ} (hnum : Computable₂ num) (hden : Computable₂ den)
    (hpos : ∀ x t, 0 < den x t)
    (hmono : ∀ x, Monotone fun t => (num x t : ℝ) / (den x t : ℝ))
    (htend : ∀ x, Tendsto (fun t => (num x t : ℝ) / (den x t : ℝ)) atTop (𝓝 (μ x))) :
    IsLowerSemicomputable μ := by
  have hpred : ComputablePred
      (Function.uncurry fun (q : α × ℕ × ℕ) (t : ℕ) =>
        q.2.1 * den q.1 t < num q.1 t * (q.2.2 + 1)) :=
    ComputablePred.nat_lt
      (Primrec.nat_mul.to_comp.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
        (hden.comp (Computable.fst.comp Computable.fst) Computable.snd))
      (Primrec.nat_mul.to_comp.comp
        (hnum.comp (Computable.fst.comp Computable.fst) Computable.snd)
        ((Primrec.nat_add.comp Primrec.id (Primrec.const 1)).to_comp.comp
          (Computable.snd.comp (Computable.snd.comp Computable.fst))))
  refine (ComputablePred.rePred_exists hpred).of_eq fun ⟨x, a, b⟩ => ?_
  have hb_pos : (0 : ℝ) < ((b + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos b)
  have hiff (t : ℕ) : a * den x t < num x t * (b + 1) ↔
      (a : ℝ) / ((b + 1 : ℕ) : ℝ) < (num x t : ℝ) / (den x t : ℝ) := by
    rw [div_lt_div_iff₀ hb_pos (Nat.cast_pos.mpr (hpos x t))]
    exact_mod_cast Iff.rfl
  simp_rw [hiff]
  exact ⟨fun ⟨t, ht⟩ => ht.trans_le ((hmono x).ge_of_tendsto (htend x) t),
    fun hlt => ((htend x).eventually_const_lt hlt).exists⟩

/-! ### Enumerating algorithmic probability of a prefix-free code -/

private def codeProgramCand (c : Code) (k : ℕ) : Option (List Bool × ℕ) :=
  (decode (α := List Bool × ℕ) k).bind fun qt =>
    (Code.evaln qt.2 c (encode qt.1)).map fun y => (qt.1, y)

private theorem primrec_codeProgramCand (c : Code) : Primrec (codeProgramCand c) := by
  have hev : Primrec fun qt : List Bool × ℕ => Code.evaln qt.2 c (encode qt.1) :=
    Code.primrec_evaln.comp
      (Primrec.pair (Primrec.pair Primrec.snd (Primrec.const c)) (Primrec.encode.comp Primrec.fst))
  have hmap : Primrec fun qt : List Bool × ℕ =>
      (Code.evaln qt.2 c (encode qt.1)).map fun y => (qt.1, y) :=
    Primrec.option_map hev (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  exact (Primrec.option_bind Primrec.decode (hmap.comp Primrec.snd).to₂).of_eq fun _ => rfl

private def codeProgramTable (c : Code) (n : ℕ) : List (List Bool × ℕ) :=
  Nat.distinctValues (codeProgramCand c) n

private theorem primrec_codeProgramTable (c : Code) : Primrec (codeProgramTable c) := by
  have h : Primrec₂ fun (_ : Unit) (k : ℕ) => codeProgramCand c k :=
    Primrec₂.mk <| (primrec_codeProgramCand c).comp Primrec.snd
  exact ((Primrec.distinctValues h).comp (Primrec.const ()) Primrec.id).of_eq fun _ => rfl

private theorem codeProgramTable_prefix (c : Code) {m n : ℕ} (hmn : m ≤ n) :
    codeProgramTable c m <+: codeProgramTable c n :=
  Nat.distinctValues_prefix (codeProgramCand c) hmn

private theorem mem_codeProgramTable_produces {c : Code} {n : ℕ} {q : List Bool} {y : ℕ}
    (h : (q, y) ∈ codeProgramTable c n) : (ofCode c).Produces q y := by
  obtain ⟨k, -, hk⟩ := Nat.mem_distinctValues.mp h
  simp only [codeProgramCand, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hk
  obtain ⟨⟨q', t⟩, _, y', hy', hpair⟩ := hk
  cases hpair
  exact ofCode_produces_iff.mpr (Code.evaln_complete.mpr ⟨t, hy'⟩)

private theorem produces_iff_exists_mem_codeProgramTable {c : Code} {q : List Bool} {y : ℕ} :
    (ofCode c).Produces q y ↔ ∃ n, (q, y) ∈ codeProgramTable c n := by
  constructor
  · intro hprod
    obtain ⟨t, ht⟩ := Code.evaln_complete.mp (ofCode_produces_iff.mp hprod)
    refine ⟨encode (q, t) + 1, Nat.mem_distinctValues.mpr ⟨encode (q, t), Nat.lt_succ_self _, ?_⟩⟩
    simp [codeProgramCand, Option.mem_def.mp ht]
  · rintro ⟨n, hn⟩
    exact mem_codeProgramTable_produces hn

private theorem nodup_map_fst_codeProgramTable (c : Code) (n : ℕ) :
    ((codeProgramTable c n).map Prod.fst).Nodup := by
  refine (Nat.nodup_distinctValues (codeProgramCand c) n).map_on fun a ha b hb heq => ?_
  have ha' := ofCode_produces_iff.mp (mem_codeProgramTable_produces ha)
  have hb' := ofCode_produces_iff.mp (mem_codeProgramTable_produces hb)
  rw [heq] at ha'
  exact Prod.ext heq (Part.mem_unique ha' hb')

private theorem primrec_list_filter_fst {β : Type*} [Primcodable β]
    (c : Code) (flt : β → ℕ → Bool) (hflt : Primrec₂ flt) :
    Primrec fun bx : β × ℕ =>
      ((codeProgramTable c bx.2).filter fun qy => flt bx.1 qy.2).map Prod.fst := by
  have hitem : Primrec₂ fun (bx : β × ℕ) (qy : List Bool × ℕ) =>
      if flt bx.1 qy.2 = true then [qy.1] else [] := by
    have hp : PrimrecPred fun arg : (β × ℕ) × (List Bool × ℕ) =>
        flt arg.1.1 arg.2.2 = true :=
      Primrec.eq.comp
        (hflt.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
        (Primrec.const true)
    exact Primrec₂.mk <| Primrec.ite hp
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.const []))
      (Primrec.const [])
  have hflat : Primrec fun bx : β × ℕ =>
      (codeProgramTable c bx.2).flatMap fun qy => if flt bx.1 qy.2 = true then [qy.1] else [] :=
    Primrec.list_flatMap ((primrec_codeProgramTable c).comp Primrec.snd) hitem
  refine hflat.of_eq fun bx => ?_
  induction codeProgramTable c bx.2 with
  | nil => simp
  | cons hd tl ih => by_cases h : flt bx.1 hd.2 = true <;> simp [h, ih]

/-- Maximum length among a finite list of binary codewords. -/
@[expose] def codeMaxLen (L : List (List Bool)) : ℕ :=
  (L.map List.length).foldl max 0

/-- Integer-scaled dyadic Kraft sum `∑ w ∈ L, 2 ^ (codeMaxLen L - |w|)`. -/
@[expose] def codeScaledSum (L : List (List Bool)) : ℕ :=
  (L.map fun w => 2 ^ (codeMaxLen L - w.length)).sum

theorem primrec_codeMaxLen : Primrec codeMaxLen := by
  have hmap : Primrec fun L : List (List Bool) => L.map List.length :=
    Primrec.list_map Primrec.id (Primrec.list_length.comp Primrec.snd).to₂
  have hmax : Primrec₂ fun (_ : List (List Bool)) (mn : ℕ × ℕ) => max mn.1 mn.2 :=
    Primrec₂.mk <|
      Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldl hmap (Primrec.const 0) hmax).of_eq fun _ => rfl

theorem primrec_codeScaledSum : Primrec codeScaledSum := by
  have hel : Primrec₂ fun (L : List (List Bool)) (w : List Bool) =>
      2 ^ (codeMaxLen L - w.length) :=
    Primrec₂.mk <| primrec_two_pow.comp
      (Primrec.nat_sub.comp (primrec_codeMaxLen.comp Primrec.fst)
        (Primrec.list_length.comp Primrec.snd))
  exact (Primrec.list_sum (Primrec.list_map Primrec.id hel)).of_eq fun _ => rfl

private theorem natCast_sum_two_pow_sub_length (m : ℕ) (L : List (List Bool))
    (hle : ∀ w ∈ L, w.length ≤ m) :
    ((L.map fun w : List Bool => (2 : ℕ) ^ (m - w.length)).sum : ℝ) =
      (L.map fun w : List Bool => (2 : ℝ)⁻¹ ^ w.length).sum * (2 : ℝ) ^ m := by
  induction L with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, add_mul,
      ih fun w hw => hle w (List.mem_cons_of_mem a hw)]
    congr 1
    rw [← pow_sub_mul_pow (2 : ℝ) (hle a List.mem_cons_self), mul_left_comm, ← mul_pow,
      inv_mul_cancel₀ two_ne_zero, one_pow, mul_one]

/-- Casting `codeScaledSum L` to `ℝ` equals the dyadic Kraft sum of `L` scaled by
`2 ^ codeMaxLen L`. -/
theorem natCast_codeScaledSum (L : List (List Bool)) :
    (codeScaledSum L : ℝ) =
      (L.map fun w : List Bool => (2 : ℝ)⁻¹ ^ w.length).sum * (2 : ℝ) ^ codeMaxLen L :=
  natCast_sum_two_pow_sub_length (codeMaxLen L) L fun _ hw =>
    List.mem_le_foldl_max (List.mem_map_of_mem hw)

private theorem codeScaledSum_cast (L : List (List Bool)) :
    (codeScaledSum L : ℝ) / ((2 ^ codeMaxLen L : ℕ) : ℝ) =
      (L.map fun w : List Bool => (2 : ℝ)⁻¹ ^ w.length).sum := by
  have hcast : ((2 ^ codeMaxLen L : ℕ) : ℝ) = (2 : ℝ) ^ codeMaxLen L := by push_cast; rfl
  rw [hcast, div_eq_iff (by positivity)]
  exact natCast_codeScaledSum L

private theorem isLowerSemicomputable_code_filtered {β : Type*} [Primcodable β]
    {c : Code} (hpf : (ofCode c).IsPrefixFree)
    {flt : β → ℕ → Bool} (hflt : Primrec₂ flt) :
    IsLowerSemicomputable fun b : β =>
      ∑' p : {p : List Bool // ∃ y, (ofCode c).Produces p y ∧ flt b y = true},
        (2 : ℝ)⁻¹ ^ p.1.length := by
  let L : β → ℕ → List (List Bool) := fun b n =>
    ((codeProgramTable c n).filter fun qy => flt b qy.2).map Prod.fst
  have hL : Primrec fun bx : β × ℕ => L bx.1 bx.2 :=
    primrec_list_filter_fst c flt hflt
  let num : β → ℕ → ℕ := fun b n => codeScaledSum (L b n)
  let den : β → ℕ → ℕ := fun b n => 2 ^ codeMaxLen (L b n)
  have hnum : Computable₂ num := (primrec_codeScaledSum.comp hL).to_comp.to₂
  have hpow : Primrec fun W : List (List Bool) => 2 ^ codeMaxLen W :=
    primrec_two_pow.comp primrec_codeMaxLen
  have hden : Computable₂ den := (hpow.comp hL).to_comp.to₂
  have hpos : ∀ b n, 0 < den b n := fun b n => Nat.two_pow_pos _
  have hval : ∀ b n,
      (num b n : ℝ) / (den b n : ℝ) =
        ((L b n).map fun w : List Bool => (2 : ℝ)⁻¹ ^ w.length).sum :=
    fun b n => codeScaledSum_cast (L b n)
  have hmono (b : β) : Monotone fun n => (num b n : ℝ) / (den b n : ℝ) := fun m n hmn => by
    obtain ⟨t, ht⟩ := codeProgramTable_prefix c hmn
    have ⟨tail, htail⟩ : L b m <+: L b n := by
      dsimp only [L]
      rw [← ht, List.filter_append, List.map_append]
      exact List.prefix_append _ _
    simp only [hval, ← htail, List.map_append, List.sum_append, le_add_iff_nonneg_right]
    exact List.sum_nonneg fun _ hr => by
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hr
      positivity
  have htend : ∀ b, Tendsto (fun n => (num b n : ℝ) / (den b n : ℝ)) atTop
      (𝓝 (∑' p : {p : List Bool // ∃ y, (ofCode c).Produces p y ∧ flt b y = true},
        (2 : ℝ)⁻¹ ^ p.1.length)) := by
    intro b
    let S := {p : List Bool // ∃ y, (ofCode c).Produces p y ∧ flt b y = true}
    let embS : S → (ofCode c).haltingSet := fun p => ⟨p.1, p.2.choose, p.2.choose_spec.1⟩
    have hembS : Function.Injective embS := fun _ _ h =>
      Subtype.ext (congrArg (fun z : (ofCode c).haltingSet => z.1) h)
    have hs : Summable fun p : S => (2 : ℝ)⁻¹ ^ p.1.length :=
      hpf.summable_two_inv_pow_length.comp_injective hembS
    have hsub_fin : ∀ n, ((L b n).toFinset : Set (List Bool)) ⊆
        {p : List Bool | ∃ y, (ofCode c).Produces p y ∧ flt b y = true} := by
      intro n w hw
      rw [Finset.mem_coe, List.mem_toFinset] at hw
      obtain ⟨⟨q, y⟩, hmem, rfl⟩ := List.mem_map.mp hw
      rw [List.mem_filter] at hmem
      exact ⟨y, mem_codeProgramTable_produces hmem.1, hmem.2⟩
    have hsum_eq : ∀ n, (num b n : ℝ) / (den b n : ℝ) =
        ∑ w ∈ (L b n).toFinset, (2 : ℝ)⁻¹ ^ w.length := by
      intro n
      rw [hval b n]
      have hnodup : (L b n).Nodup := by
        dsimp only [L]
        refine (nodup_map_fst_codeProgramTable c n).sublist ?_
        exact List.Sublist.map Prod.fst List.filter_sublist
      exact (List.sum_toFinset (fun w : List Bool => (2 : ℝ)⁻¹ ^ w.length) hnodup).symm
    have hle_tsum : ∀ n, (num b n : ℝ) / (den b n : ℝ) ≤
        ∑' p : S, (2 : ℝ)⁻¹ ^ p.1.length := by
      intro n
      rw [hsum_eq n]
      classical
      let fEmbed : {w : List Bool // w ∈ (L b n).toFinset} ↪ S :=
        ⟨fun x => ⟨x.1, hsub_fin n x.2⟩,
          fun _ _ h => Subtype.ext (congrArg (fun z : S => z.1) h)⟩
      let F : Finset S := (L b n).toFinset.attach.map fEmbed
      have hF : ∑ p ∈ F, (2 : ℝ)⁻¹ ^ p.1.length =
          ∑ w ∈ (L b n).toFinset, (2 : ℝ)⁻¹ ^ w.length := by
        rw [Finset.sum_map]
        exact Finset.sum_attach (L b n).toFinset fun w => (2 : ℝ)⁻¹ ^ w.length
      rw [← hF]
      exact hs.sum_le_tsum F fun _ _ => by positivity
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨F₀, hF₀⟩ : ∃ F₀ : Finset S, (∑' p : S, (2 : ℝ)⁻¹ ^ p.1.length) - ε <
        ∑ p ∈ F₀, (2 : ℝ)⁻¹ ^ p.1.length := by
      by_contra! hall; linarith [hs.tsum_le_of_sum_le hall]
    have hex_n : ∀ p : S, ∃ n, p.1 ∈ L b n := fun ⟨p, y, hp, hy⟩ =>
      let ⟨n, hn⟩ := produces_iff_exists_mem_codeProgramTable.mp hp
      ⟨n, List.mem_map.mpr ⟨(p, y), List.mem_filter.mpr ⟨hn, hy⟩, rfl⟩⟩
    classical
    refine ⟨F₀.sup fun p => Nat.find (hex_n p), fun n hn => ?_⟩
    have hsub : F₀.image Subtype.val ⊆ (L b n).toFinset :=
      Finset.image_subset_iff.mpr fun p hpF => by
        obtain ⟨t, ht⟩ := codeProgramTable_prefix c ((Finset.le_sup hpF).trans hn)
        have hm := Nat.find_spec (hex_n p)
        dsimp only [L] at hm ⊢
        exact List.mem_toFinset.mpr (by simp [← ht, List.filter_append, hm])
    have hle_approx : ∑ p ∈ F₀, (2 : ℝ)⁻¹ ^ p.1.length ≤ (num b n : ℝ) / (den b n : ℝ) := by
      rw [← Finset.sum_image (f := fun w : List Bool => (2 : ℝ)⁻¹ ^ w.length)
        fun _ _ _ _ h => Subtype.ext h, hsum_eq n]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith, by linarith [hle_tsum n]⟩
  exact isLowerSemicomputable_of_computable_monotone_tendsto hnum hden hpos hmono htend

/-- Algorithmic probability `M.universalProb` is lower semicomputable for every prefix-free
description method with a partial recursive evaluator. -/
theorem isLowerSemicomputable_universalProb_of_partrec_eval {α : Type*} [Primcodable α]
    {M : DescriptionMethod α} (hM : M.IsPrefixFree) {eval : List Bool →. α}
    (heval : Partrec eval) (hprod : ∀ p x, M.Produces p x ↔ x ∈ eval p) :
    IsLowerSemicomputable M.universalProb := by
  obtain ⟨c, hc⟩ := Code.exists_code.mp heval
  have hcode_eq : ∀ p y, (ofCode c).Produces p y ↔ ∃ x, y = encode x ∧ M.Produces p x := by
    intro p y
    rw [ofCode_produces_iff, hc]
    simp only [Part.coe_some, Part.bind_some, Part.mem_map_iff, encodek, hprod]
    exact ⟨fun ⟨x, hx, hxy⟩ => ⟨x, hxy.symm, hx⟩, fun ⟨x, hxy, hx⟩ => ⟨x, hx, hxy.symm⟩⟩
  have hpf_c : (ofCode c).IsPrefixFree :=
    hM.anti fun p ⟨y, hy⟩ => let ⟨x, _, hx⟩ := (hcode_eq p y).mp hy; ⟨x, hx⟩
  have hflt : Primrec₂ fun (x : α) (y : ℕ) => decide (y = encode x) :=
    Primrec₂.mk (Primrec.eq.comp Primrec.snd (Primrec.encode.comp Primrec.fst)).decide
  refine (isLowerSemicomputable_code_filtered hpf_c hflt).of_eq fun ⟨x, a, b⟩ => ?_
  have heq : M.universalProb x =
      ∑' p : {p : List Bool // ∃ y, (ofCode c).Produces p y ∧ decide (y = encode x) = true},
        (2 : ℝ)⁻¹ ^ p.1.length := by
    let e : {p : List Bool // M.Produces p x} ≃
        {p : List Bool // ∃ y, (ofCode c).Produces p y ∧ decide (y = encode x) = true} :=
      { toFun p := ⟨p.1, encode x, (hcode_eq p.1 (encode x)).mpr ⟨x, rfl, p.2⟩, by simp⟩
        invFun p := ⟨p.1, by
          obtain ⟨y, hy, hyx⟩ := p.2
          obtain ⟨x', rfl, hx'⟩ := (hcode_eq p.1 y).mp hy
          simp only [decide_eq_true_eq] at hyx
          rwa [encode_injective hyx] at hx'⟩
        left_inv _ := rfl
        right_inv _ := rfl }
    exact e.tsum_eq fun p => (2 : ℝ)⁻¹ ^ p.1.length
  change _ ↔ (a : ℝ) / ((b + 1 : ℕ) : ℝ) < M.universalProb x
  rw [heq]

/-- `universalPrefix.universalProb` is lower semicomputable. -/
theorem isLowerSemicomputable_universalProb_universalPrefix :
    IsLowerSemicomputable universalPrefix.universalProb := by
  obtain ⟨eval, heval, hprod⟩ := isPartrec_universalPrefix
  exact isLowerSemicomputable_universalProb_of_partrec_eval
    isPrefixFree_universalPrefix heval hprod

/-- `universalPrefixBits.universalProb` is lower semicomputable. -/
theorem isLowerSemicomputable_universalProb_universalPrefixBits :
    IsLowerSemicomputable universalPrefixBits.universalProb := by
  obtain ⟨eval, heval, hprod⟩ := isPartrec_universalPrefix
  let evalB : List Bool →. List Bool := fun p =>
    (eval p).map fun n => (decode (α := List Bool) n).getD []
  have hevalB : Partrec evalB := by
    have hdec : Computable fun n : ℕ => (decode (α := List Bool) n).getD [] :=
      Computable.option_getD Computable.decode (Computable.const [])
    exact heval.map (hdec.comp Computable.snd).to₂
  have hprodB : ∀ p x, universalPrefixBits.Produces p x ↔ x ∈ evalB p := by
    intro p x
    rw [universalPrefixBits, map_produces_iff]
    rw [show x ∈ evalB p ↔ ∃ n, n ∈ eval p ∧ (decode (α := List Bool) n).getD [] = x from
      Part.mem_map_iff _]
    exact exists_congr fun n => and_congr (hprod p n) Iff.rfl
  exact isLowerSemicomputable_universalProb_of_partrec_eval
    isPrefixFree_universalPrefixBits hevalB hprodB

private noncomputable def marginalSigmaEquiv (x : ℕ) :
    (y : ℕ) × {p : List Bool // universalPrefix.Produces p (Nat.pair x y)} ≃
      {p : List Bool // ∃ z, universalPrefix.Produces p z ∧ z.unpair.1 = x} where
  toFun yp := ⟨yp.2.1, Nat.pair x yp.1, yp.2.2, by simp⟩
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
    exact sigma_subtype_ext (P := fun y p => universalPrefix.Produces p (Nat.pair x y)) hy
  right_inv _ := rfl

/-- Joint summability of `2⁻¹ ^ |p|` over pairs `(y, p)` where `universalPrefix` produces
`Nat.pair x y`. -/
theorem summable_universalPrefix_produces_pair (x : ℕ) :
    Summable (fun ⟨_, p, _⟩ => (2 : ℝ)⁻¹ ^ p.length :
      (y : ℕ) × {p : List Bool // universalPrefix.Produces p (Nat.pair x y)} → ℝ) := by
  let emb : {p : List Bool // ∃ z, universalPrefix.Produces p z ∧ z.unpair.1 = x} →
      universalPrefix.haltingSet :=
    fun p => ⟨p.1, p.2.choose, p.2.choose_spec.1⟩
  have hemb : Function.Injective emb := fun _ _ h =>
    Subtype.ext (congrArg (fun z : universalPrefix.haltingSet => z.1) h)
  exact (Equiv.summable_iff (marginalSigmaEquiv x)).mpr
    (isPrefixFree_universalPrefix.summable_two_inv_pow_length.comp_injective hemb)

/-- The marginal semimeasure `x ↦ ∑' y, universalPrefix.universalProb (Nat.pair x y)` is lower
semicomputable. -/
theorem isLowerSemicomputable_universalProb_marginal :
    IsLowerSemicomputable fun x : ℕ =>
      ∑' y : ℕ, universalPrefix.universalProb (Nat.pair x y) := by
  obtain ⟨c, hc⟩ := isPartrec_universalPrefix.exists_produces_iff
  have hpf : (ofCode c).IsPrefixFree :=
    isPrefixFree_universalPrefix.anti fun p ⟨y, hy⟩ => ⟨y, (hc p y).mpr hy⟩
  have hflt : Primrec₂ fun (x z : ℕ) => decide (z.unpair.1 = x) :=
    Primrec₂.mk
      (Primrec.eq.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)) Primrec.fst).decide
  refine (isLowerSemicomputable_code_filtered hpf hflt).of_eq fun ⟨x, a, b⟩ => ?_
  have heq :
      ∑' y : ℕ, universalPrefix.universalProb (Nat.pair x y) =
        ∑' p : {p : List Bool // ∃ z, (ofCode c).Produces p z ∧
          decide (z.unpair.1 = x) = true}, (2 : ℝ)⁻¹ ^ p.1.length := by
    let e0 :
        {p : List Bool // ∃ z, universalPrefix.Produces p z ∧ z.unpair.1 = x} ≃
          {p : List Bool // ∃ z, (ofCode c).Produces p z ∧ decide (z.unpair.1 = x) = true} :=
      { toFun p := ⟨p.1, p.2.choose, (hc _ _).mp p.2.choose_spec.1,
          by simp [p.2.choose_spec.2]⟩
        invFun p := ⟨p.1, p.2.choose, (hc _ _).mpr p.2.choose_spec.1,
          by simpa using p.2.choose_spec.2⟩
        left_inv _ := rfl
        right_inv _ := rfl }
    let e : (y : ℕ) ×
        {p : List Bool // universalPrefix.Produces p (Nat.pair x y)} ≃
          {p : List Bool // ∃ z, (ofCode c).Produces p z ∧ decide (z.unpair.1 = x) = true} :=
      (marginalSigmaEquiv x).trans e0
    have hs_prog : ∀ y : ℕ,
        Summable fun p : {p : List Bool // universalPrefix.Produces p (Nat.pair x y)} =>
          (2 : ℝ)⁻¹ ^ p.1.length :=
      fun _ => isPrefixFree_universalPrefix.summable_universalProb_program _
    calc ∑' y : ℕ, universalPrefix.universalProb (Nat.pair x y)
        = ∑' yp : (y : ℕ) × {p : List Bool // universalPrefix.Produces p (Nat.pair x y)},
            (2 : ℝ)⁻¹ ^ yp.2.1.length :=
          ((summable_universalPrefix_produces_pair x).tsum_sigma' hs_prog).symm
      _ = ∑' p : {p : List Bool // ∃ z, (ofCode c).Produces p z ∧
            decide (z.unpair.1 = x) = true}, (2 : ℝ)⁻¹ ^ p.1.length :=
          e.tsum_eq fun p => (2 : ℝ)⁻¹ ^ p.1.length
  change _ ↔ (a : ℝ) / ((b + 1 : ℕ) : ℝ) <
      ∑' y : ℕ, universalPrefix.universalProb (Nat.pair x y)
  rw [heq]

/-! ### Levin's coding theorem -/

private theorem two_inv_pow_rePred {α : Type*} [Primcodable α] {μ : α → ℝ}
    (hμ : IsLowerSemicomputable μ) : REPred fun p : α × ℕ => (2 : ℝ)⁻¹ ^ (p.2 + 1) < μ p.1 := by
  have hpow : Primrec fun n : ℕ => 2 ^ (n + 1) - 1 :=
    Primrec.nat_sub.comp ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2)
      (Primrec.nat_add.comp Primrec.id (Primrec.const 1))) (Primrec.const 1)
  have hf : Computable fun p : α × ℕ => (p.1, 1, 2 ^ (p.2 + 1) - 1) :=
    Computable.pair Computable.fst
      (Computable.pair (Computable.const 1) (hpow.to_comp.comp Computable.snd))
  refine (hμ.comp hf).of_eq fun ⟨x, k⟩ => ?_
  have hpos : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
  have hsub : ((2 ^ (k + 1) - 1 + 1 : ℕ) : ℝ) = (2 : ℝ) ^ (k + 1) := by
    rw [Nat.sub_add_cancel hpos]
    push_cast
    rfl
  dsimp only
  rw [Nat.cast_one, hsub, one_div, inv_pow]

private theorem sum_Icc_two_inv_pow_eq (k₀ m : ℕ) :
    ∑ k ∈ Finset.Icc k₀ (k₀ + m), (2 : ℝ)⁻¹ ^ (k + 2) =
      (2 : ℝ)⁻¹ ^ (k₀ + 1) - (2 : ℝ)⁻¹ ^ (k₀ + m + 2) := by
  induction m with
  | zero =>
    simp [pow_succ]
    ring
  | succ m ih =>
    rw [show k₀ + (m + 1) = (k₀ + m) + 1 by omega, Finset.sum_Icc_succ_top (by omega), ih]
    have h1 : (2 : ℝ)⁻¹ ^ (k₀ + m + 1 + 2) = (2 : ℝ)⁻¹ ^ (k₀ + m + 2) * (2 : ℝ)⁻¹ := by
      rw [show k₀ + m + 1 + 2 = (k₀ + m + 2) + 1 by omega, pow_succ]
    rw [h1]
    ring

private theorem sum_Icc_two_inv_pow_le (k₀ kM : ℕ) :
    ∑ k ∈ Finset.Icc k₀ kM, (2 : ℝ)⁻¹ ^ (k + 2) ≤ (2 : ℝ)⁻¹ ^ (k₀ + 1) := by
  by_cases hle : k₀ ≤ kM
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [sum_Icc_two_inv_pow_eq]
    exact sub_le_self _ (by positivity)
  · simp [Finset.Icc_eq_empty_of_lt (Nat.lt_of_not_ge hle)]

/-- Core **Levin coding lemma**: any lower-semicomputable discrete semimeasure `μ` on `α` gives
`K_U(x) ≤ k + c` whenever `2⁻¹ ^ (k + 1) < μ x`. -/
theorem exists_le_complexity_of_isLowerSemicomputable {α : Type*} [Primcodable α]
    {μ : α → ℝ} (hnonneg : ∀ x, 0 ≤ μ x) (hsummable : Summable μ) (hle : ∑' x, μ x ≤ 1)
    (hμ : IsLowerSemicomputable μ) {U : DescriptionMethod α}
    (hU : U.MinorizesPrefixPartrec) :
    ∃ c : ℕ, ∀ x : α, ∀ k : ℕ, (2 : ℝ)⁻¹ ^ (k + 1) < μ x → U.ecomplexity x ≤ k + c := by
  obtain ⟨e, he⟩ := rePred_iff_exists_code.mp (two_inv_pow_rePred hμ)
  let dec2 : ℕ → Option (α × ℕ) := decode₂ (α × ℕ)
  have hdec2 : Primrec dec2 := Primrec.decode₂
  let firstAccept : ℕ → Bool := fun s =>
    let z := s.unpair.1
    let t := s.unpair.2
    (Code.evaln t e z).isSome && (decide (t = 0) || (Code.evaln (t - 1) e z).isNone)
  let req : ℕ → Option (ℕ × α) := fun s =>
    if firstAccept s then (dec2 s.unpair.1).map fun xk => (xk.2 + 2, xk.1)
    else Option.none
  have hfirst_prim : Primrec firstAccept := by
    have hz : Primrec fun s : ℕ => s.unpair.1 := Primrec.fst.comp Primrec.unpair
    have ht : Primrec fun s : ℕ => s.unpair.2 := Primrec.snd.comp Primrec.unpair
    have hev : Primrec fun s : ℕ => Code.evaln s.unpair.2 e s.unpair.1 :=
      Code.primrec_evaln.comp (Primrec.pair (Primrec.pair ht (Primrec.const e)) hz)
    have hevprev : Primrec fun s : ℕ => Code.evaln (s.unpair.2 - 1) e s.unpair.1 :=
      Code.primrec_evaln.comp
        (Primrec.pair (Primrec.pair (Primrec.nat_sub.comp ht (Primrec.const 1)) (Primrec.const e))
          hz)
    have hnone : Primrec fun s : ℕ => (Code.evaln (s.unpair.2 - 1) e s.unpair.1).isNone :=
      (Primrec.option_casesOn hevprev (Primrec.const true) (Primrec.const false).to₂).of_eq
        fun s => by cases Code.evaln (s.unpair.2 - 1) e s.unpair.1 <;> rfl
    have hsome : Primrec fun s : ℕ => (Code.evaln s.unpair.2 e s.unpair.1).isSome :=
      (Primrec.option_casesOn hev (Primrec.const false) (Primrec.const true).to₂).of_eq
        fun s => by cases Code.evaln s.unpair.2 e s.unpair.1 <;> rfl
    exact Primrec.and.comp hsome
      (Primrec.or.comp (Primrec.eq.decide.comp ht (Primrec.const 0)) hnone)
  have hreq_comp : Computable req := by
    have hpred : PrimrecPred fun s : ℕ => firstAccept s = true :=
      Primrec.eq.comp hfirst_prim (Primrec.const true)
    have hsome : Primrec fun s : ℕ =>
        (dec2 s.unpair.1).map fun xk => (xk.2 + 2, xk.1) :=
      Primrec.option_map (hdec2.comp (Primrec.fst.comp Primrec.unpair))
        (Primrec.pair (Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 2))
          (Primrec.fst.comp Primrec.snd))
    exact (Primrec.ite hpred hsome (Primrec.const Option.none)).to_comp.of_eq fun _ => rfl
  have hreq_eq {s ℓ : ℕ} {x : α} : req s = some (ℓ, x) ↔
      ∃ k, ℓ = k + 2 ∧ firstAccept s = true ∧ s.unpair.1 = encode (x, k) := by
    dsimp only [req, dec2]
    split_ifs with hacc
    · cases hdec : decode₂ (α × ℕ) s.unpair.1 with
      | none =>
        refine ⟨fun h => by simp [Option.map] at h, fun ⟨k', _, _, hs1⟩ => ?_⟩
        have := decode₂_eq_some.mpr hs1.symm
        simp [hdec] at this
      | some ak =>
        rcases ak with ⟨a, k⟩
        have henc : encode (a, k) = s.unpair.1 := mem_decode₂.mp hdec
        change some (k + 2, a) = some (ℓ, x) ↔ _
        simp only [Option.some.injEq, Prod.mk.injEq, hacc, true_and]
        refine ⟨fun ⟨hℓ, hx⟩ => ⟨k, hℓ.symm, hx ▸ henc.symm⟩, fun ⟨k', hℓ, hs1⟩ => ?_⟩
        obtain ⟨rfl, rfl⟩ := encode_injective (henc.trans hs1)
        exact ⟨hℓ.symm, rfl⟩
    · simp [hacc]
  have hreq_spec {s k : ℕ} {x : α} (hs : req s = some (k + 2, x)) :
      (2 : ℝ)⁻¹ ^ (k + 1) < μ x := by
    obtain ⟨k', hk, hacc, hz⟩ := hreq_eq.mp hs
    have hk' : k' = k := by omega
    subst k'
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (Bool.and_eq_true _ _ |>.mp hacc).1
    exact (he (x, k)).mpr (Part.dom_iff_mem.mpr ⟨y, Code.evaln_complete.mpr ⟨s.unpair.2, hz ▸ hy⟩⟩)
  have hnot_lt {a b : ℕ} (hab : a.unpair.2 < b.unpair.2) (hz : a.unpair.1 = b.unpair.1)
      (ha : firstAccept a = true) (hb : firstAccept b = true) : False := by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (Bool.and_eq_true _ _ |>.mp ha).1
    rcases Bool.or_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp hb).2 with h0 | hnone
    · exact absurd (of_decide_eq_true h0) (by omega)
    · have hsome := Code.evaln_mono (show a.unpair.2 ≤ b.unpair.2 - 1 by omega) (hz ▸ hy)
      simp [Option.mem_def.mp hsome] at hnone
  have hreq_unique {s₁ s₂ : ℕ} {x : α} {k : ℕ}
      (hs₁ : req s₁ = some (k + 2, x)) (hs₂ : req s₂ = some (k + 2, x)) : s₁ = s₂ := by
    obtain ⟨k₁, hk₁, ha₁, hz₁⟩ := hreq_eq.mp hs₁
    obtain ⟨k₂, hk₂, ha₂, hz₂⟩ := hreq_eq.mp hs₂
    have hk₁' : k₁ = k := by omega
    have hk₂' : k₂ = k := by omega
    subst k₁ k₂
    have hz : s₁.unpair.1 = s₂.unpair.1 := hz₁.trans hz₂.symm
    have ht : s₁.unpair.2 = s₂.unpair.2 := by
      rcases lt_trichotomy s₁.unpair.2 s₂.unpair.2 with hlt | heq | hlt
      · exact (hnot_lt hlt hz ha₁ ha₂).elim
      · exact heq
      · exact (hnot_lt hlt hz.symm ha₂ ha₁).elim
    exact Nat.pair_unpair s₁ ▸ Nat.pair_unpair s₂ ▸ congrArg₂ Nat.pair hz ht
  have hbound (n : ℕ) : ∑ i ∈ Finset.range n,
      (match req i with | Option.none => (0 : ℝ) | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ) ≤ 1 := by
    classical
    let I := (Finset.range n).filter fun i => (req i).isSome
    let tag (i : I) : α × ℕ :=
      let ℓx := (req i.1).get (Finset.mem_filter.mp i.2).2
      (ℓx.2, ℓx.1 - 2)
    have htag_spec (i : I) : req i.1 = some ((tag i).2 + 2, (tag i).1) := by
      obtain ⟨⟨ℓ, x⟩, hsi⟩ := Option.isSome_iff_exists.mp (Finset.mem_filter.mp i.2).2
      obtain ⟨k, rfl, -, -⟩ := hreq_eq.mp hsi
      simp [tag, hsi]
    have htag_inj : Function.Injective tag := fun i₁ i₂ hteq =>
      Subtype.ext (hreq_unique (htag_spec i₁) (hteq ▸ htag_spec i₂))
    let S : Finset (α × ℕ) := I.attach.image tag
    have hsum_I : ∑ i ∈ Finset.range n,
        (match req i with | Option.none => (0 : ℝ) | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ) =
        ∑ p ∈ S, (2 : ℝ)⁻¹ ^ (p.2 + 2) := by
      have h1 : ∑ i ∈ Finset.range n,
          (match req i with | Option.none => (0 : ℝ) | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ) =
          ∑ i ∈ I, (match req i with | Option.none => (0 : ℝ) | some (ℓ, _) => (2 : ℝ)⁻¹ ^ ℓ) := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun i _ => by cases req i <;> simp
      rw [h1, ← Finset.sum_attach I, Finset.sum_image fun _ _ _ _ h => htag_inj h]
      exact Finset.sum_congr rfl fun i _ => by rw [htag_spec i]
    have hS_lt : ∀ p ∈ S, (2 : ℝ)⁻¹ ^ (p.2 + 1) < μ p.1 := fun p hp => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
      exact hreq_spec (htag_spec i)
    rw [hsum_I, ← Finset.sum_fiberwise_of_maps_to (t := S.image Prod.fst)
      (fun p hp => Finset.mem_image_of_mem Prod.fst hp) (fun p => (2 : ℝ)⁻¹ ^ (p.2 + 2))]
    calc ∑ x ∈ S.image Prod.fst, ∑ p ∈ S with p.1 = x, (2 : ℝ)⁻¹ ^ (p.2 + 2)
        ≤ ∑ x ∈ S.image Prod.fst, μ x := by
          refine Finset.sum_le_sum fun x hx => ?_
          let K := (S.filter fun p => p.1 = x).image Prod.snd
          have hK_eq : ∑ p ∈ S with p.1 = x, (2 : ℝ)⁻¹ ^ (p.2 + 2) =
              ∑ k ∈ K, (2 : ℝ)⁻¹ ^ (k + 2) := by
            refine (Finset.sum_image (f := fun k => (2 : ℝ)⁻¹ ^ (k + 2)) ?_).symm
            intro p₁ hp₁ p₂ hp₂ hpeq
            simp only [Finset.mem_coe, Finset.mem_filter] at hp₁ hp₂
            exact Prod.ext (hp₁.2.trans hp₂.2.symm) hpeq
          rw [hK_eq]
          obtain ⟨p₀, hp₀, rfl⟩ := Finset.mem_image.mp hx
          have hne : K.Nonempty :=
            ⟨p₀.2, Finset.mem_image_of_mem Prod.snd (Finset.mem_filter.mpr ⟨hp₀, rfl⟩)⟩
          let k₀ := K.min' hne
          let kM := K.max' hne
          have hk₀_mem : k₀ ∈ K := Finset.min'_mem K hne
          obtain ⟨pmin, hpmin, hpm_snd⟩ := Finset.mem_image.mp hk₀_mem
          rw [Finset.mem_filter] at hpmin
          have hlt_x : (2 : ℝ)⁻¹ ^ (k₀ + 1) < μ p₀.1 := by
            have := hS_lt pmin hpmin.1
            rwa [hpmin.2, hpm_snd] at this
          have hK_sub : K ⊆ Finset.Icc k₀ kM := fun k hk =>
            Finset.mem_Icc.mpr ⟨Finset.min'_le K k hk, Finset.le_max' K k hk⟩
          exact ((Finset.sum_le_sum_of_subset_of_nonneg hK_sub fun _ _ _ => by positivity).trans
            (sum_Icc_two_inv_pow_le k₀ kM)).trans hlt_x.le
      _ ≤ ∑' x, μ x := hsummable.sum_le_tsum _ fun _ _ => hnonneg _
      _ ≤ 1 := hle
  obtain ⟨c, hc⟩ := hU.kraftChaitin_of_sum_le_one hreq_comp hbound
  refine ⟨c + 2, fun x k hk => ?_⟩
  obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp ((he (x, k)).mp hk)
  obtain ⟨t₁, ht₁⟩ := Code.evaln_complete.mp hy
  classical
  have hex_t : ∃ m, (Code.evaln m e (encode (x, k))).isSome = true :=
    ⟨t₁, Option.isSome_iff_exists.mpr ⟨y, ht₁⟩⟩
  let t := Nat.find hex_t
  have ht : firstAccept (Nat.pair (encode (x, k)) t) = true := by
    simp only [firstAccept, t, Nat.unpair_pair, Nat.find_spec hex_t, Bool.true_and, Bool.or_eq_true,
      decide_eq_true_eq]
    exact or_iff_not_imp_left.mpr fun h0 => Option.isNone_iff_eq_none.mpr
      (Option.not_isSome_iff_eq_none.mp
        (Nat.find_min hex_t (Nat.sub_lt (Nat.pos_of_ne_zero h0) Nat.one_pos)))
  have hreq_val : req (Nat.pair (encode (x, k)) t) = some (k + 2, x) :=
    hreq_eq.mpr ⟨k, rfl, ht, Nat.unpair_pair _ _ ▸ rfl⟩
  exact (hc _ (k + 2) x hreq_val).trans_eq (by push_cast; ring)

namespace DescriptionMethod

/-- General coding bound for any prefix-free minorizing description method `U`: `μ x ≤ 2 ^ c *
2⁻¹ ^ K_U(x)` whenever `0 < μ x`. -/
theorem MinorizesPrefixPartrec.exists_le_two_pow_mul_complexity_of_isLowerSemicomputable
    {α : Type*} [Primcodable α] {U : DescriptionMethod α} (hU : U.MinorizesPrefixPartrec)
    {μ : α → ℝ} (hnonneg : ∀ x, 0 ≤ μ x) (hsummable : Summable μ) (hle : ∑' x, μ x ≤ 1)
    (hμ : IsLowerSemicomputable μ) :
    ∃ c : ℕ, ∀ x : α, 0 < μ x →
      U.ecomplexity x ≠ ⊤ ∧ μ x ≤ (2 : ℝ) ^ c * (2 : ℝ)⁻¹ ^ U.complexity x := by
  obtain ⟨c, hc⟩ := exists_le_complexity_of_isLowerSemicomputable hnonneg hsummable hle hμ hU
  refine ⟨c, fun x hx => ?_⟩
  have hex : ∃ k : ℕ, (2 : ℝ)⁻¹ ^ (k + 1) < μ x := by
    have htend : Tendsto (fun k : ℕ => (2 : ℝ)⁻¹ ^ (k + 1)) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
      exact h0.comp (tendsto_add_atTop_nat 1)
    exact (htend.eventually (Iio_mem_nhds hx)).exists
  classical
  let k₀ := Nat.find hex
  have hk₀ : (2 : ℝ)⁻¹ ^ (k₀ + 1) < μ x := Nat.find_spec hex
  have hfin : U.ecomplexity x ≠ ⊤ := by
    have h1 := hc x k₀ hk₀
    intro htop
    rw [htop] at h1
    simp at h1
  have hkle : U.complexity x ≤ k₀ + c := by
    have h1 := hc x k₀ hk₀
    rw [← natCast_complexity hfin] at h1
    exact_mod_cast h1
  refine ⟨hfin, ?_⟩
  have hpow_anti : ∀ {a b : ℕ}, a ≤ b → (2 : ℝ)⁻¹ ^ b ≤ (2 : ℝ)⁻¹ ^ a := fun hab =>
    pow_le_pow_of_le_one (by positivity) (by norm_num) hab
  have hμ_le : μ x ≤ (2 : ℝ)⁻¹ ^ k₀ := by
    by_cases h0 : k₀ = 0
    · simpa [h0] using (hsummable.le_tsum x fun _ _ => hnonneg _).trans hle
    · refine le_of_not_gt ?_
      simpa [Nat.sub_add_cancel (Nat.pos_of_ne_zero h0)] using
        Nat.find_min hex (show k₀ - 1 < k₀ by omega)
  calc μ x ≤ (2 : ℝ)⁻¹ ^ k₀ := hμ_le
    _ = (2 : ℝ) ^ c * (2 : ℝ)⁻¹ ^ (k₀ + c) := by
      rw [pow_add, mul_comm ((2 : ℝ)⁻¹ ^ k₀), ← mul_assoc, ← mul_pow,
        mul_inv_cancel₀ two_ne_zero, one_pow, one_mul]
    _ ≤ (2 : ℝ) ^ c * (2 : ℝ)⁻¹ ^ U.complexity x :=
      mul_le_mul_of_nonneg_left (hpow_anti hkle) (by positivity)

end DescriptionMethod

private theorem le_two_pow_mul_of_minorizes {α : Type*} [Primcodable α]
    {U : DescriptionMethod α} (hU : U.MinorizesPrefixPartrec)
    {μ : α → ℝ} (hnonneg : ∀ x, 0 ≤ μ x) (hsummable : Summable μ) (hle : ∑' x, μ x ≤ 1)
    (hμ : IsLowerSemicomputable μ) :
    ∃ c : ℕ, ∀ x : α, μ x ≤ (2 : ℝ) ^ c * (2 : ℝ)⁻¹ ^ U.complexity x := by
  obtain ⟨c, hc⟩ :=
    hU.exists_le_two_pow_mul_complexity_of_isLowerSemicomputable hnonneg hsummable hle hμ
  refine ⟨c, fun x => ?_⟩
  by_cases hx : 0 < μ x
  · exact (hc x hx).2
  · have h0 : μ x = 0 := le_antisymm (le_of_not_gt hx) (hnonneg x)
    rw [h0]
    positivity

private theorem logb_two_inv_pow_nat (k : ℕ) :
    Real.logb 2 ((2 : ℝ)⁻¹ ^ k) = -(k : ℝ) := by
  rw [show (2 : ℝ)⁻¹ ^ k = (2 : ℝ) ^ (-(k : ℝ)) by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, inv_pow]]
  exact Real.logb_rpow (by norm_num) (by norm_num)

private theorem logb_two_pow_mul_two_inv_pow (c k : ℕ) :
    Real.logb 2 ((2 : ℝ) ^ c * (2 : ℝ)⁻¹ ^ k) = (c : ℝ) - (k : ℝ) := by
  rw [show (2 : ℝ) ^ c * (2 : ℝ)⁻¹ ^ k = (2 : ℝ) ^ ((c : ℝ) - (k : ℝ)) by
    rw [Real.rpow_sub (by norm_num), Real.rpow_natCast, Real.rpow_natCast, div_eq_mul_inv, inv_pow]]
  exact Real.logb_rpow (by norm_num) (by norm_num)

private theorem complexity_le_neg_logb_of_minorizes {α : Type*} [Primcodable α]
    {U : DescriptionMethod α} (hU : U.MinorizesPrefixPartrec)
    {μ : α → ℝ} (hnonneg : ∀ x, 0 ≤ μ x) (hsummable : Summable μ) (hle : ∑' x, μ x ≤ 1)
    (hμ : IsLowerSemicomputable μ) :
    ∃ c : ℕ, ∀ x : α, 0 < μ x → (U.complexity x : ℝ) ≤ -Real.logb 2 (μ x) + c := by
  obtain ⟨c, hc⟩ := le_two_pow_mul_of_minorizes hU hnonneg hsummable hle hμ
  refine ⟨c, fun x hx => ?_⟩
  have hlog : Real.logb 2 (μ x) ≤ Real.logb 2 ((2 : ℝ) ^ c * (2 : ℝ)⁻¹ ^ U.complexity x) :=
    Real.logb_le_logb_of_le (by norm_num) hx (hc x)
  rw [logb_two_pow_mul_two_inv_pow] at hlog
  linarith

private theorem levin_coding_of_minorizes {α : Type*} [Primcodable α]
    {U : DescriptionMethod α} (hpf : U.IsPrefixFree) (hU : U.MinorizesPrefixPartrec)
    (hfin : ∀ x, U.ecomplexity x ≠ ⊤) (hsem : IsLowerSemicomputable U.universalProb) :
    ∃ c : ℕ, ∀ x : α,
      (2 : ℝ)⁻¹ ^ U.complexity x ≤ U.universalProb x ∧
      U.universalProb x ≤ (2 : ℝ) ^ c * (2 : ℝ)⁻¹ ^ U.complexity x := by
  obtain ⟨c, hc⟩ := le_two_pow_mul_of_minorizes hU (universalProb_nonneg _)
    hpf.summable_universalProb
    (hpf.tsum_universalProb_eq_chaitinOmega.symm ▸ hpf.chaitinOmega_le_one) hsem
  exact ⟨c, fun x => ⟨two_inv_pow_complexity_le_universalProb hpf (hfin x), hc x⟩⟩

private theorem abs_complexity_add_logb_of_bounds {α : Type*} {U : DescriptionMethod α}
    {c : ℕ} (hc : ∀ x : α,
      (2 : ℝ)⁻¹ ^ U.complexity x ≤ U.universalProb x ∧
      U.universalProb x ≤ (2 : ℝ) ^ c * (2 : ℝ)⁻¹ ^ U.complexity x) (x : α) :
    |(U.complexity x : ℝ) + Real.logb 2 (U.universalProb x)| ≤ c := by
  obtain ⟨hlo, hhi⟩ := hc x
  have hm_pos : 0 < U.universalProb x := lt_of_lt_of_le (by positivity) hlo
  have hlog_lo := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hlo
  have hlog_hi := Real.logb_le_logb_of_le (b := 2) (by norm_num) hm_pos hhi
  rw [logb_two_inv_pow_nat] at hlog_lo
  rw [logb_two_pow_mul_two_inv_pow] at hlog_hi
  rw [abs_le]
  constructor <;> linarith

/-- For every lower-semicomputable discrete semimeasure `μ : ℕ → ℝ`, `μ x ≤ 2 ^ c * 2⁻¹ ^ K(x)`.
-/
theorem exists_le_two_pow_mul_universalPrefix_of_isLowerSemicomputable {μ : ℕ → ℝ}
    (hnonneg : ∀ x, 0 ≤ μ x) (hsummable : Summable μ) (hle : ∑' x, μ x ≤ 1)
    (hμ : IsLowerSemicomputable μ) :
    ∃ c : ℕ, ∀ x : ℕ, μ x ≤ (2 : ℝ) ^ c * (2 : ℝ)⁻¹ ^ universalPrefix.complexity x :=
  le_two_pow_mul_of_minorizes minorizesPrefixPartrec_universalPrefix hnonneg hsummable hle hμ

/-- For every lower-semicomputable discrete semimeasure `μ : List Bool → ℝ`,
`μ x ≤ 2 ^ c * 2⁻¹ ^ K(x)`. -/
theorem exists_le_two_pow_mul_universalPrefixBits_of_isLowerSemicomputable {μ : List Bool → ℝ}
    (hnonneg : ∀ x, 0 ≤ μ x) (hsummable : Summable μ) (hle : ∑' x, μ x ≤ 1)
    (hμ : IsLowerSemicomputable μ) :
    ∃ c : ℕ, ∀ x : List Bool,
      μ x ≤ (2 : ℝ) ^ c * (2 : ℝ)⁻¹ ^ universalPrefixBits.complexity x :=
  le_two_pow_mul_of_minorizes minorizesPrefixPartrec_universalPrefixBits hnonneg hsummable hle hμ

/-- Logarithmic coding bound: `K(x) ≤ -log₂ μ(x) + c` whenever `0 < μ x`. -/
theorem exists_complexity_universalPrefix_le_neg_logb_of_isLowerSemicomputable {μ : ℕ → ℝ}
    (hnonneg : ∀ x, 0 ≤ μ x) (hsummable : Summable μ) (hle : ∑' x, μ x ≤ 1)
    (hμ : IsLowerSemicomputable μ) :
    ∃ c : ℕ, ∀ x : ℕ, 0 < μ x →
      (universalPrefix.complexity x : ℝ) ≤ -Real.logb 2 (μ x) + c :=
  complexity_le_neg_logb_of_minorizes minorizesPrefixPartrec_universalPrefix
    hnonneg hsummable hle hμ

/-- Binary-string logarithmic coding bound: `K(x) ≤ -log₂ μ(x) + c` whenever `0 < μ x`. -/
theorem exists_complexity_universalPrefixBits_le_neg_logb_of_isLowerSemicomputable
    {μ : List Bool → ℝ} (hnonneg : ∀ x, 0 ≤ μ x) (hsummable : Summable μ)
    (hle : ∑' x, μ x ≤ 1) (hμ : IsLowerSemicomputable μ) :
    ∃ c : ℕ, ∀ x : List Bool, 0 < μ x →
      (universalPrefixBits.complexity x : ℝ) ≤ -Real.logb 2 (μ x) + c :=
  complexity_le_neg_logb_of_minorizes minorizesPrefixPartrec_universalPrefixBits
    hnonneg hsummable hle hμ

/-- **Levin's coding theorem** for `universalPrefix` [LiVitanyi2019, ShenUspenskyVereshchagin2017]:
algorithmic probability `m(x)` equals `2⁻¹ ^ K(x)` up to a multiplicative constant. -/
theorem levin_coding_universalPrefix :
    ∃ c : ℕ, ∀ x : ℕ,
      (2 : ℝ)⁻¹ ^ universalPrefix.complexity x ≤ universalPrefix.universalProb x ∧
      universalPrefix.universalProb x ≤
        (2 : ℝ) ^ c * (2 : ℝ)⁻¹ ^ universalPrefix.complexity x :=
  levin_coding_of_minorizes isPrefixFree_universalPrefix minorizesPrefixPartrec_universalPrefix
    ecomplexity_universalPrefix_ne_top isLowerSemicomputable_universalProb_universalPrefix

/-- **Levin's coding theorem** for binary strings (`universalPrefixBits`). -/
theorem levin_coding_universalPrefixBits :
    ∃ c : ℕ, ∀ x : List Bool,
      (2 : ℝ)⁻¹ ^ universalPrefixBits.complexity x ≤ universalPrefixBits.universalProb x ∧
      universalPrefixBits.universalProb x ≤
        (2 : ℝ) ^ c * (2 : ℝ)⁻¹ ^ universalPrefixBits.complexity x :=
  levin_coding_of_minorizes isPrefixFree_universalPrefixBits
    minorizesPrefixPartrec_universalPrefixBits ecomplexity_universalPrefixBits_ne_top
    isLowerSemicomputable_universalProb_universalPrefixBits

/-- **Levin's coding theorem** (logarithmic form): `|K(x) + log₂ m(x)| ≤ c`. -/
theorem exists_abs_complexity_add_logb_universalProb_universalPrefix_le :
    ∃ c : ℕ, ∀ x : ℕ,
      |(universalPrefix.complexity x : ℝ) + Real.logb 2 (universalPrefix.universalProb x)| ≤ c :=
  let ⟨c, hc⟩ := levin_coding_universalPrefix
  ⟨c, fun x => abs_complexity_add_logb_of_bounds hc x⟩

/-- **Levin's coding theorem** for binary strings (logarithmic form): `|K(x) + log₂ m(x)| ≤ c`. -/
theorem exists_abs_complexity_add_logb_universalProb_universalPrefixBits_le :
    ∃ c : ℕ, ∀ x : List Bool,
      |(universalPrefixBits.complexity x : ℝ) +
        Real.logb 2 (universalPrefixBits.universalProb x)| ≤ c :=
  let ⟨c, hc⟩ := levin_coding_universalPrefixBits
  ⟨c, fun x => abs_complexity_add_logb_of_bounds hc x⟩

/-- **Universality of the Solomonoff–Levin prior** on `ℕ`: `universalPrefix.universalProb`
multiplicatively dominates every lower-semicomputable discrete semimeasure. -/
theorem exists_mul_universalProb_universalPrefix_ge {μ : ℕ → ℝ}
    (hnonneg : ∀ x, 0 ≤ μ x) (hsummable : Summable μ) (hle : ∑' x, μ x ≤ 1)
    (hμ : IsLowerSemicomputable μ) :
    ∃ c : ℕ, ∀ x : ℕ, μ x ≤ (2 : ℝ) ^ c * universalPrefix.universalProb x := by
  obtain ⟨c, hc⟩ := exists_le_two_pow_mul_universalPrefix_of_isLowerSemicomputable
    hnonneg hsummable hle hμ
  exact ⟨c, fun x => (hc x).trans
    (mul_le_mul_of_nonneg_left (two_inv_pow_complexity_universalPrefix_le x) (by positivity))⟩

/-- **Universality of the Solomonoff–Levin prior** on binary strings `List Bool`. -/
theorem exists_mul_universalProb_universalPrefixBits_ge {μ : List Bool → ℝ}
    (hnonneg : ∀ x, 0 ≤ μ x) (hsummable : Summable μ) (hle : ∑' x, μ x ≤ 1)
    (hμ : IsLowerSemicomputable μ) :
    ∃ c : ℕ, ∀ x : List Bool, μ x ≤ (2 : ℝ) ^ c * universalPrefixBits.universalProb x := by
  obtain ⟨c, hc⟩ := exists_le_two_pow_mul_universalPrefixBits_of_isLowerSemicomputable
    hnonneg hsummable hle hμ
  exact ⟨c, fun x => (hc x).trans
    (mul_le_mul_of_nonneg_left (two_inv_pow_complexity_universalPrefixBits_le x) (by positivity))⟩

end Cslib.Kolmogorov
