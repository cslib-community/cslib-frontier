/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.Linear
public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Residual codes, the Griesmer bound, and simplex codes

Given a linear code `C : Submodule F (ι → F)` over a finite field `F` of size `q = |F|` and a
codeword `c ∈ C`, the *residual code* `Cslib.Code.residualLinear C c` punctures `C` to the
`n - wt(c)` coordinates `{i : ι // c i = 0}` where `c` vanishes [MacWilliamsSloane1977]. Summing
the Hamming weights of the `q` translates `x - a • c` (`a : F`) gives the identity
`∑_{a : F} wt(x - a • c) = q * wt(x|_{c = 0}) + (q - 1) * wt(c)`, from which both structural
properties of residual codes follow:

* Every nonzero codeword of `residualLinear C c` has weight at least
  `(q * d - (q - 1) * wt(c)) ⌈/⌉ q` whenever `d ≤ minDist C`
  (`Cslib.Code.le_minDist_residualLinear`).
* Whenever `c ≠ 0` and `(q - 1) * wt(c) < q * d`, the kernel of restriction to `{c = 0}` on `C` is
  spanned by `c`, so `dim_F (residualLinear C c) + 1 = dim_F C`
  (`Cslib.Code.finrank_residualLinear_add_one`).

Applying both properties inductively at a minimum-weight nonzero codeword yields the **Griesmer
bound** (Griesmer 1960; Solomon and Stiffler 1965; [MacWilliamsSloane1977]): every `[n, k, d]_q`
linear code satisfies
`∑_{i < k} d ⌈/⌉ q ^ i ≤ n` (`Cslib.Code.sum_ceilDiv_pow_le_card`). Since `d ⌈/⌉ q ^ 0 = d` and
`1 ≤ d ⌈/⌉ q ^ i` for `d ≥ 1`, the Griesmer sum is at least `d + (k - 1)`
(`Cslib.Code.add_sub_one_le_sum_ceilDiv_pow`), recovering and refining the linear Singleton bound
`k + d ≤ n + 1`.

Finally, evaluating `k`-dimensional linear forms `x ⬝ᵥ ·` on the projective representatives
`Cslib.Code.SimplexPoint F k` whose first nonzero coordinate is `1` defines the `$q$-ary simplex
code` `Cslib.Code.simplexCode F k` of length `(q ^ k - 1) / (q - 1) = ∑_{i < k} q ^ i`
(`Cslib.Code.card_simplexPoint`), dimension `k` (`Cslib.Code.finrank_simplexCode`), constant
nonzero codeword weight `q ^ (k - 1)` (`Cslib.Code.hammingNorm_simplexEncode`), and minimum
distance `q ^ (k - 1)` (`Cslib.Code.minDist_simplexCode`), attaining the Griesmer bound with exact
equality for every finite field `F` and every `k ≥ 1` (`Cslib.Code.sum_ceilDiv_pow_simplexCode`).

## Main definitions

* `Cslib.Code.residualLinear`: the residual code of `C` with respect to a word `c`.
* `Cslib.Code.SimplexPoint`: normalized projective points in `Fin k → F` with leading nonzero
  coordinate `1`.
* `Cslib.Code.simplexEncode`, `Cslib.Code.simplexCode`: the `$q$-ary simplex encoding map and
  linear code.

## Main results

* `Cslib.Code.le_minDist_residualLinear`: lower bound on the minimum distance of `residualLinear`.
* `Cslib.Code.finrank_residualLinear_add_one`: dimension of `residualLinear` when
  `(q - 1) * wt(c) < q * d`.
* `Cslib.Code.sum_ceilDiv_pow_le_card`: the Griesmer bound for linear codes over finite fields.
* `Cslib.Code.add_sub_one_le_sum_ceilDiv_pow`: comparison showing the Griesmer bound refines the
  linear Singleton bound.
* `Cslib.Code.card_simplexPoint`, `Cslib.Code.simplexEncode_injective`,
  `Cslib.Code.finrank_simplexCode`, `Cslib.Code.hammingNorm_simplexEncode`,
  `Cslib.Code.minDist_simplexCode`: parameters `[(q ^ k - 1) / (q - 1), k, q ^ (k - 1)]_q` and
  constant weight of `$q$-ary simplex codes.
* `Cslib.Code.sum_ceilDiv_pow_simplexCode`: `$q$-ary simplex codes meet the Griesmer bound with
  equality.

## References

* [F. J. MacWilliams, N. J. A. Sloane, *The Theory of Error-Correcting Codes*]
  [MacWilliamsSloane1977]
-/

public section

namespace Cslib.Code

open Finset
open scoped BigOperators

/-! ### Residual codes -/

/-- The *residual code* `Res(C, c)` of a linear code `C` with respect to a word `c : ι → M`:
the puncturing of `C` to the coordinates `{i : ι // c i = 0}` where `c` vanishes. -/
def residualLinear {ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (C : Submodule R (ι → M)) (c : ι → M) : Submodule R ({i : ι // c i = 0} → M) :=
  punctureLinear C Subtype.val

@[simp]
theorem mem_residualLinear {ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {C : Submodule R (ι → M)} {c : ι → M} {y : {i : ι // c i = 0} → M} :
    y ∈ residualLinear C c ↔ ∃ x ∈ C, x ∘ Subtype.val = y :=
  mem_punctureLinear

@[simp]
theorem coe_residualLinear {ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (C : Submodule R (ι → M)) (c : ι → M) :
    (residualLinear C c : Set ({i : ι // c i = 0} → M)) =
      puncture (C : Set (ι → M)) Subtype.val :=
  coe_punctureLinear C Subtype.val

private theorem card_zero_subtype_add_hammingNorm {ι M : Type*} [Fintype ι] [Zero M]
    [DecidableEq M] (c : ι → M) :
    Fintype.card {i : ι // c i = 0} + hammingNorm c = Fintype.card ι := by
  classical
  rw [Fintype.card_subtype]
  exact card_filter_add_card_filter_not (fun i : ι => c i = 0)

private theorem sum_hammingNorm_sub_smul {ι F : Type*} [Fintype ι] [Field F] [Fintype F]
    [DecidableEq F] (x c : ι → F) :
    ∑ a : F, hammingNorm (x - a • c) =
      Fintype.card F * hammingNorm (x ∘ (Subtype.val : {i : ι // c i = 0} → ι)) +
        (Fintype.card F - 1) * hammingNorm c := by
  classical
  have hnorm (a : F) :
      hammingNorm (x - a • c) = ∑ i : ι, if x i - a * c i ≠ 0 then 1 else 0 := by
    simp only [hammingNorm, card_filter, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [hnorm]
  rw [sum_comm, ← sum_filter_add_sum_filter_not univ (fun i : ι => c i = 0)]
  congr 1
  · have hzero :
        ∑ i ∈ univ.filter (fun i : ι => c i = 0),
            ∑ a : F, (if x i - a * c i ≠ 0 then 1 else 0) =
          ∑ i ∈ univ.filter (fun i : ι => c i = 0),
            Fintype.card F * (if x i ≠ 0 then 1 else 0) := by
      refine sum_congr rfl fun i hi => ?_
      simp only [(mem_filter.1 hi).2, mul_zero, sub_zero, sum_const, card_univ, smul_eq_mul]
    rw [hzero, ← mul_sum]
    congr 1
    rw [← card_filter, hammingNorm]
    symm
    refine card_bij (fun (j : {i : ι // c i = 0}) _ => j.1)
      (fun j hj => ?_) (fun _ _ _ _ h => Subtype.ext h) (fun i hi => ?_)
    · simp only [mem_filter, mem_univ, true_and, Function.comp_apply] at hj ⊢
      exact ⟨j.2, hj⟩
    · simp only [mem_filter, mem_univ, true_and] at hi
      exact ⟨⟨i, hi.1⟩, mem_filter.2 ⟨mem_univ _, hi.2⟩, rfl⟩
  · have hsupp :
        ∑ i ∈ univ.filter (fun i : ι => c i ≠ 0),
            ∑ a : F, (if x i - a * c i ≠ 0 then 1 else 0) =
          ∑ _i ∈ univ.filter (fun i : ι => c i ≠ 0), (Fintype.card F - 1) := by
      refine sum_congr rfl fun i hi => ?_
      have hci : c i ≠ 0 := (mem_filter.1 hi).2
      rw [← card_filter]
      have hfilt : (univ.filter fun a : F => x i - a * c i ≠ 0) =
          univ.filter fun a : F => ¬ a = x i / c i := by
        ext a
        simp only [mem_filter, mem_univ, true_and, ne_eq, sub_eq_zero]
        exact not_congr ⟨fun h => (eq_div_iff hci).2 h.symm, fun h => ((eq_div_iff hci).1 h).symm⟩
      rw [hfilt]
      have hpart := card_filter_add_card_filter_not (s := (univ : Finset F))
        (fun a : F => a = x i / c i)
      have hone : #{a : F | a = x i / c i} = 1 := by
        rw [filter_eq', ite_eq_left (mem_univ _), card_singleton]
      rw [card_univ, hone] at hpart
      omega
    rw [hsupp, sum_const, smul_eq_mul, mul_comm]
    rfl

private theorem card_mul_le_of_forall_sub_smul_ne_zero {ι F : Type*} [Fintype ι] [Field F]
    [Fintype F] [DecidableEq F] {C : Submodule F (ι → F)} {x c : ι → F} (hx : x ∈ C) (hc : c ∈ C)
    {d : ℕ} (hd : (d : ℕ∞) ≤ minDist (C : Set (ι → F))) (hne : ∀ a : F, x - a • c ≠ 0) :
    Fintype.card F * d ≤
      Fintype.card F * hammingNorm (x ∘ (Subtype.val : {i : ι // c i = 0} → ι)) +
        (Fintype.card F - 1) * hammingNorm c := by
  rw [← sum_hammingNorm_sub_smul]
  calc Fintype.card F * d = ∑ _a : F, d := by rw [sum_const, card_univ, smul_eq_mul]
    _ ≤ ∑ a : F, hammingNorm (x - a • c) := sum_le_sum fun a _ =>
        Nat.cast_le.1 ((le_minDist_iff_hammingNorm C).1 hd (x - a • c)
          (C.sub_mem hx (C.smul_mem a hc)) (hne a))

/-- **Minimum distance of a residual code**: if `C` has minimum distance at least `d` over a finite
field `F` of size `q = |F|` and `c ∈ C`, then
`((q * d - (q - 1) * wt(c)) ⌈/⌉ q : ℕ∞) ≤ minDist (residualLinear C c)`. -/
theorem le_minDist_residualLinear {ι F : Type*} [Fintype ι] [Field F] [Fintype F] [DecidableEq F]
    {C : Submodule F (ι → F)} {c : ι → F} (hc : c ∈ C) {d : ℕ}
    (hd : (d : ℕ∞) ≤ minDist (C : Set (ι → F))) :
    (((Fintype.card F * d - (Fintype.card F - 1) * hammingNorm c) ⌈/⌉ Fintype.card F : ℕ) : ℕ∞) ≤
      minDist (residualLinear C c : Set ({i : ι // c i = 0} → F)) := by
  refine (le_minDist_iff_hammingNorm (residualLinear C c)).2 fun y hy hy0 => ?_
  obtain ⟨x, hx, rfl⟩ := mem_residualLinear.1 hy
  have hsum_ge := card_mul_le_of_forall_sub_smul_ne_zero hx hc hd fun a h0 => hy0 <| by
    ext i
    have hi := congrFun h0 i.1
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, i.2, mul_zero, sub_zero,
      Pi.zero_apply] at hi
    exact hi
  refine Nat.cast_le.2 ((ceilDiv_le_iff_le_mul Fintype.card_pos).2 ?_)
  omega

/-- **Dimension of a residual code**: if `C` has minimum distance at least `d` over a finite field
`F` of size `q = |F|` and `c ∈ C` is a nonzero codeword with `(q - 1) * wt(c) < q * d`, then
`dim_F (residualLinear C c) + 1 = dim_F C`. -/
theorem finrank_residualLinear_add_one {ι F : Type*} [Fintype ι] [Field F] [Fintype F]
    [DecidableEq F] {C : Submodule F (ι → F)} {c : ι → F} (hc : c ∈ C) (hc0 : c ≠ 0) {d : ℕ}
    (hd : (d : ℕ∞) ≤ minDist (C : Set (ι → F)))
    (hw : (Fintype.card F - 1) * hammingNorm c < Fintype.card F * d) :
    Module.finrank F (residualLinear C c) + 1 = Module.finrank F C := by
  let resMap : C →ₗ[F] ({i : ι // c i = 0} → F) :=
    (LinearMap.funLeft F F (Subtype.val : {i : ι // c i = 0} → ι)).comp C.subtype
  have hrange : LinearMap.range resMap = residualLinear C c := by
    ext y
    simp only [LinearMap.mem_range, Subtype.exists, resMap, LinearMap.coe_comp,
      Submodule.coe_subtype, Function.comp_apply, mem_residualLinear]
    exact ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, h⟩, fun ⟨a, ha, h⟩ => ⟨a, ha, h⟩⟩
  let cSub : C := ⟨c, hc⟩
  have hcSub0 : cSub ≠ 0 := fun h => hc0 (congrArg Subtype.val h)
  have hker : LinearMap.ker resMap = F ∙ cSub := by
    refine le_antisymm (fun xSub hxker => ?_) ?_
    · by_contra hx_not
      have hsum_ge := card_mul_le_of_forall_sub_smul_ne_zero xSub.2 hc hd fun a h0 => hx_not <| by
        have hEq : xSub = a • cSub := Subtype.ext (sub_eq_zero.1 h0)
        rw [hEq]
        exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self cSub)
      have hres0 : xSub.1 ∘ (Subtype.val : {i : ι // c i = 0} → ι) = 0 := hxker
      rw [hres0, hammingNorm_zero, mul_zero, zero_add] at hsum_ge
      omega
    · rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
      ext i
      exact i.2
  have hrn := LinearMap.finrank_range_add_finrank_ker resMap
  rw [hrange, hker, finrank_span_singleton hcSub0] at hrn
  exact hrn

/-! ### The Griesmer bound -/

private theorem ceilDiv_ceilDiv {d a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (d ⌈/⌉ a) ⌈/⌉ b = d ⌈/⌉ (a * b) := by
  refine eq_of_forall_ge_iff fun c => ?_
  rw [ceilDiv_le_iff_le_mul hb, ceilDiv_le_iff_le_mul ha,
    ceilDiv_le_iff_le_mul (Nat.mul_pos ha hb), mul_assoc]

private theorem sum_ceilDiv_pow_le_card_of_finrank {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] :
    ∀ (k : ℕ) {ι : Type*} [Fintype ι] (C : Submodule F (ι → F)),
      Module.finrank F C = k → ∀ {d : ℕ}, (d : ℕ∞) ≤ minDist (C : Set (ι → F)) →
        ∑ i ∈ range k, d ⌈/⌉ Fintype.card F ^ i ≤ Fintype.card ι
  | 0, _, _, _, _, _, _ => by simp
  | k + 1, ι, _, C, hk, d, hd => by
    rcases Nat.eq_zero_or_pos d with rfl | hd_pos
    · simp
    have hC_ne : C ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hk
      omega
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hC_ne
    obtain ⟨x, hx, y, hy, hxy, hmin⟩ :=
      exists_hammingDist_eq_minDist (C := (C : Set (ι → F))) ⟨v, hv, 0, C.zero_mem, hv0⟩
    let c : ι → F := -x + y
    have hc : c ∈ C := C.add_mem (C.neg_mem hx) hy
    have hc0 : c ≠ 0 := fun h0 => hxy (neg_add_eq_zero.1 h0)
    set d₀ := hammingNorm c
    have hd₀_eq : (d₀ : ℕ∞) = minDist (C : Set (ι → F)) := by
      simpa only [c, d₀, ← hammingDist_eq_hammingNorm] using hmin
    have hd_le_d₀ : d ≤ d₀ := Nat.cast_le.1 (hd.trans_eq hd₀_eq.symm)
    have hd₀_pos : 0 < d₀ := lt_of_lt_of_le hd_pos hd_le_d₀
    have hq_pos : 0 < Fintype.card F := Fintype.card_pos
    have hq_gt : 1 < Fintype.card F := Fintype.one_lt_card
    have hw : (Fintype.card F - 1) * d₀ < Fintype.card F * d₀ := by
      have hsub : Fintype.card F - 1 < Fintype.card F := by omega
      exact Nat.mul_lt_mul_of_pos_right hsub hd₀_pos
    have hfinrank_res : Module.finrank F (residualLinear C c) = k := by
      have := finrank_residualLinear_add_one hc hc0 hd₀_eq.le hw
      omega
    have hsub_eq : Fintype.card F * d₀ - (Fintype.card F - 1) * hammingNorm c = d₀ := by
      change Fintype.card F * d₀ - (Fintype.card F - 1) * d₀ = d₀
      zify [Nat.le_of_lt hq_gt, hw.le]
      ring
    have hmin_res₀ :
        ((d₀ ⌈/⌉ Fintype.card F : ℕ) : ℕ∞) ≤
          minDist (residualLinear C c : Set ({i : ι // c i = 0} → F)) := by
      have hres := le_minDist_residualLinear hc hd₀_eq.le
      rwa [hsub_eq] at hres
    have hceil_mono : d ⌈/⌉ Fintype.card F ≤ d₀ ⌈/⌉ Fintype.card F :=
      (gc_mul_ceilDiv hq_pos).monotone_l hd_le_d₀
    have hmin_res :
        ((d ⌈/⌉ Fintype.card F : ℕ) : ℕ∞) ≤
          minDist (residualLinear C c : Set ({i : ι // c i = 0} → F)) :=
      (Nat.cast_le.2 hceil_mono).trans hmin_res₀
    have hih := sum_ceilDiv_pow_le_card_of_finrank k (residualLinear C c) hfinrank_res hmin_res
    have htower :
        ∑ i ∈ range k, d ⌈/⌉ Fintype.card F ^ (i + 1) =
          ∑ i ∈ range k, (d ⌈/⌉ Fintype.card F) ⌈/⌉ Fintype.card F ^ i :=
      sum_congr rfl fun i _ => by rw [ceilDiv_ceilDiv hq_pos (pow_pos hq_pos i), pow_succ']
    have hcard_zero := card_zero_subtype_add_hammingNorm c
    rw [sum_range_succ', pow_zero, ceilDiv_one, htower]
    omega

/-- **The Griesmer bound** (Griesmer 1960; Solomon and Stiffler 1965; [MacWilliamsSloane1977]):
for any linear code `C` of length `n = |ι|` and minimum distance at least `d` over a finite field
`F` of size `q = |F|`, `∑_{i < dim_F C} d ⌈/⌉ q ^ i ≤ n`. -/
theorem sum_ceilDiv_pow_le_card {ι F : Type*} [Fintype ι] [Field F] [Fintype F] [DecidableEq F]
    (C : Submodule F (ι → F)) {d : ℕ} (hd : (d : ℕ∞) ≤ minDist (C : Set (ι → F))) :
    ∑ i ∈ range (Module.finrank F C), d ⌈/⌉ Fintype.card F ^ i ≤ Fintype.card ι :=
  sum_ceilDiv_pow_le_card_of_finrank (Module.finrank F C) C rfl hd

/-- For `1 ≤ d`, `1 ≤ k`, and `1 ≤ q`, the Griesmer sum `∑_{i < k} d ⌈/⌉ q ^ i` is at least
`d + (k - 1)`, showing that `sum_ceilDiv_pow_le_card` refines the linear Singleton bound
`k + d ≤ n + 1`. -/
theorem add_sub_one_le_sum_ceilDiv_pow {d k q : ℕ} (hd : 1 ≤ d) (hk : 1 ≤ k) (hq : 1 ≤ q) :
    d + (k - 1) ≤ ∑ i ∈ range k, d ⌈/⌉ q ^ i := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  rw [sum_range_succ', pow_zero, ceilDiv_one, add_tsub_cancel_right, add_comm _ d]
  refine Nat.add_le_add_left ?_ d
  calc m = ∑ _i ∈ range m, 1 := by rw [sum_const, card_range, smul_eq_mul, mul_one]
    _ ≤ ∑ i ∈ range m, d ⌈/⌉ q ^ (i + 1) := by
      refine sum_le_sum fun i _ => ?_
      by_contra hlt
      have h0 : d ⌈/⌉ q ^ (i + 1) ≤ 0 := by omega
      have hd0 : d ≤ 0 := by
        have := (ceilDiv_le_iff_le_mul (pow_pos (show 0 < q by omega) (i + 1))).1 h0
        simpa using this
      omega

/-! ### `$q$-ary simplex codes and tightness of the Griesmer bound -/

/-- Normalized projective points in `Fin k → F`: vectors whose first nonzero entry is `1`. -/
abbrev SimplexPoint (F : Type*) [Zero F] [One F] (k : ℕ) : Type _ :=
  {v : Fin k → F // ∃ i : Fin k, v i = 1 ∧ ∀ j < i, v j = 0}

private theorem simplexPoint_smul_ne_zero {F : Type*} [Field F] {k : ℕ}
    (p : SimplexPoint F k) (u : Fˣ) : (u : F) • p.1 ≠ 0 := by
  obtain ⟨i, hi1, -⟩ := p.2
  intro h0
  have := congrFun h0 i
  simp only [Pi.smul_apply, smul_eq_mul, hi1, mul_one, Pi.zero_apply] at this
  exact u.ne_zero this

private noncomputable def simplexPointProdUnitsEquivNeZero (F : Type*) [Field F] [DecidableEq F]
    (k : ℕ) : SimplexPoint F k × Fˣ ≃ {w : Fin k → F // w ≠ 0} where
  toFun pu := ⟨(pu.2 : F) • pu.1.1, simplexPoint_smul_ne_zero pu.1 pu.2⟩
  invFun w :=
    let S : Finset (Fin k) := univ.filter fun i => w.1 i ≠ 0
    have hS : S.Nonempty := by
      by_contra hEmpty
      apply w.2
      ext i
      by_contra hi
      exact hEmpty ⟨i, mem_filter.2 ⟨mem_univ i, hi⟩⟩
    let i₀ : Fin k := S.min' hS
    have hi₀ : w.1 i₀ ≠ 0 := (mem_filter.1 (S.min'_mem hS)).2
    ⟨⟨(w.1 i₀)⁻¹ • w.1, i₀, by simp [hi₀], fun j hj => by
        have hj_not : j ∉ S := fun hjS => not_le_of_gt hj (S.min'_le j hjS)
        have hj0 : w.1 j = 0 := by
          by_contra hne
          exact hj_not (mem_filter.2 ⟨mem_univ j, hne⟩)
        simp [hj0]⟩,
      Units.mk0 (w.1 i₀) hi₀⟩
  left_inv := by
    rintro ⟨⟨v, i, hi1, hzero⟩, u⟩
    dsimp only
    set w : Fin k → F := (u : F) • v
    let S : Finset (Fin k) := univ.filter fun idx => w idx ≠ 0
    have hiS : i ∈ S := by
      simp only [S, mem_filter, mem_univ, true_and, w, Pi.smul_apply, smul_eq_mul, hi1, mul_one]
      exact u.ne_zero
    have hmin_eq : S.min' ⟨i, hiS⟩ = i := by
      refine le_antisymm (S.min'_le i hiS) ?_
      by_contra hlt
      have hlt' : S.min' ⟨i, hiS⟩ < i := not_le.1 hlt
      have hmem := (mem_filter.1 (S.min'_mem ⟨i, hiS⟩)).2
      simp only [w, Pi.smul_apply, smul_eq_mul, hzero _ hlt', mul_zero, ne_eq, not_true_eq_false]
        at hmem
    have hwi : w (S.min' ⟨i, hiS⟩) = (u : F) := by
      rw [hmin_eq]
      simp [w, hi1]
    refine Prod.ext (Subtype.ext ?_) (Units.ext hwi)
    change (w (S.min' _) )⁻¹ • w = v
    rw [hwi, smul_smul, inv_mul_cancel₀ u.ne_zero, one_smul]
  right_inv := by
    rintro ⟨w, hw⟩
    ext idx
    dsimp only [Units.val_mk0]
    simp only [Pi.smul_apply, smul_eq_mul]
    set S : Finset (Fin k) := univ.filter fun i => w i ≠ 0
    have hS : S.Nonempty := by
      by_contra hEmpty
      apply hw
      ext i
      by_contra hi
      exact hEmpty ⟨i, mem_filter.2 ⟨mem_univ i, hi⟩⟩
    have hi₀ : w (S.min' hS) ≠ 0 := (mem_filter.1 (S.min'_mem hS)).2
    rw [← mul_assoc, mul_inv_cancel₀ hi₀, one_mul]

/-- Over a finite field `F` of size `q = |F|`, there are `∑_{i < k} q ^ i = (q ^ k - 1) / (q - 1)`
normalized projective points in `SimplexPoint F k`. -/
theorem card_simplexPoint (F : Type*) [Field F] [Fintype F] [DecidableEq F] (k : ℕ) :
    Fintype.card (SimplexPoint F k) = ∑ i ∈ range k, Fintype.card F ^ i := by
  have hbij := Fintype.card_congr (simplexPointProdUnitsEquivNeZero F k)
  rw [Fintype.card_prod, Fintype.card_units] at hbij
  have hne : Fintype.card {w : Fin k → F // w ≠ 0} = Fintype.card F ^ k - 1 := by
    rw [Fintype.card_subtype]
    have hpart := card_filter_add_card_filter_not (s := (univ : Finset (Fin k → F)))
      (fun w => w = 0)
    have h0 : #{w : Fin k → F | w = 0} = 1 := by
      rw [filter_eq', ite_eq_left (mem_univ 0), card_singleton]
    rw [card_univ, Fintype.card_fun, Fintype.card_fin, h0] at hpart
    simp only [ne_eq]
    omega
  rw [hne] at hbij
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  refine Nat.mul_right_cancel (m := Fintype.card F - 1) (by omega) ?_
  zify [hq.le, Nat.one_le_pow k (Fintype.card F) Fintype.card_pos] at hbij ⊢
  rw [hbij]
  simpa using (geom_sum_mul (Fintype.card F : ℤ) k).symm

/-- Linear encoding map of the `$q$-ary simplex code`: evaluates `x : Fin k → F` by dot product on
each normalized projective point `p : SimplexPoint F k`. -/
@[expose] def simplexEncode (F : Type*) [Field F] (k : ℕ) :
    (Fin k → F) →ₗ[F] (SimplexPoint F k → F) where
  toFun x p := x ⬝ᵥ p.1
  map_add' x y := funext fun p => add_dotProduct x y p.1
  map_smul' c x := funext fun p => smul_dotProduct c x p.1

@[simp]
theorem simplexEncode_apply {F : Type*} [Field F] {k : ℕ} (x : Fin k → F) (p : SimplexPoint F k) :
    simplexEncode F k x p = x ⬝ᵥ p.1 :=
  rfl

/-- The `$q$-ary simplex code` of dimension `k` over `F`, as a submodule of
`SimplexPoint F k → F`. -/
def simplexCode (F : Type*) [Field F] (k : ℕ) : Submodule F (SimplexPoint F k → F) :=
  LinearMap.range (simplexEncode F k)

@[simp]
theorem mem_simplexCode {F : Type*} [Field F] {k : ℕ} {w : SimplexPoint F k → F} :
    w ∈ simplexCode F k ↔ ∃ x : Fin k → F, simplexEncode F k x = w :=
  Iff.rfl

/-- `simplexEncode F k` is injective over every field `F`. -/
theorem simplexEncode_injective (F : Type*) [Field F] (k : ℕ) :
    Function.Injective (simplexEncode F k) := by
  classical
  intro x y hxy
  by_contra hne
  have hex : ∃ i : Fin k, x i ≠ y i := by
    by_contra hall
    push Not at hall
    exact hne (funext hall)
  obtain ⟨i, hi⟩ := hex
  let p : SimplexPoint F k :=
    ⟨Pi.single i 1, i, Pi.single_eq_same i 1, fun j hj => Pi.single_eq_of_ne hj.ne 1⟩
  have heval : x ⬝ᵥ Pi.single i (1 : F) = y ⬝ᵥ Pi.single i (1 : F) := congrFun hxy p
  simp only [dotProduct_single, mul_one] at heval
  exact hi heval

/-- The `$q$-ary simplex code` `simplexCode F k` has dimension `k`. -/
@[simp]
theorem finrank_simplexCode (F : Type*) [Field F] (k : ℕ) :
    Module.finrank F (simplexCode F k) = k := by
  rw [simplexCode, LinearMap.finrank_range_of_inj (simplexEncode_injective F k),
    Module.finrank_fin_fun]

/-- **Constant weight of `$q$-ary simplex codewords**: over a finite field `F` of size `q = |F|`,
every nonzero message `x : Fin k → F` encodes to a codeword of Hamming weight `q ^ (k - 1)`. -/
theorem hammingNorm_simplexEncode {F : Type*} [Field F] [Fintype F] [DecidableEq F] {k : ℕ}
    {x : Fin k → F} (hx : x ≠ 0) :
    hammingNorm (simplexEncode F k x) = Fintype.card F ^ (k - 1) := by
  have hex : ∃ i₀ : Fin k, x i₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hx (funext hall)
  obtain ⟨i₀, hi₀⟩ := hex
  have hk_pos : 1 ≤ k := by
    have := i₀.isLt
    omega
  have hfiber (b : F) :
      #{w : Fin k → F | x ⬝ᵥ w = b} = #{w : Fin k → F | x ⬝ᵥ w = 0} := by
    symm
    let shift : Fin k → F := Pi.single i₀ ((x i₀)⁻¹ * b)
    have hx_shift : x ⬝ᵥ shift = b := by
      simp [shift, dotProduct_single, mul_inv_cancel_left₀ hi₀]
    refine card_bij (fun w _ => w + shift) (fun w hw => ?_)
      (fun w₁ _ w₂ _ h => add_right_cancel h) (fun w hw => ?_)
    · simp only [mem_filter, mem_univ, true_and] at hw ⊢
      rw [dotProduct_add, hw, zero_add, hx_shift]
    · simp only [mem_filter, mem_univ, true_and] at hw
      refine ⟨w - shift, mem_filter.2 ⟨mem_univ _, ?_⟩, sub_add_cancel w shift⟩
      rw [dotProduct_sub, hw, hx_shift, sub_self]
  have hq_pos : 0 < Fintype.card F := Fintype.card_pos
  have hker_eq : #{w : Fin k → F | x ⬝ᵥ w = 0} = Fintype.card F ^ (k - 1) := by
    have htot := card_eq_sum_card_fiberwise (s := (univ : Finset (Fin k → F)))
      (t := (univ : Finset F)) (f := fun w => x ⬝ᵥ w) (fun _ _ => mem_univ _)
    rw [card_univ, Fintype.card_fun, Fintype.card_fin,
      sum_congr rfl (fun b _ => hfiber b), sum_const, card_univ, smul_eq_mul] at htot
    refine Nat.mul_left_cancel hq_pos ?_
    rw [← htot, mul_comm, ← pow_succ, Nat.sub_add_cancel hk_pos]
  have hnonzero_dot :
      #{w : Fin k → F | x ⬝ᵥ w ≠ 0} = Fintype.card F ^ (k - 1) * (Fintype.card F - 1) := by
    have hpart := card_filter_add_card_filter_not (s := (univ : Finset (Fin k → F)))
      (fun w => x ⬝ᵥ w = 0)
    rw [card_univ, Fintype.card_fun, Fintype.card_fin, hker_eq] at hpart
    have hpow : Fintype.card F ^ k = Fintype.card F ^ (k - 1) * Fintype.card F := by
      rw [← pow_succ, Nat.sub_add_cancel hk_pos]
    rw [hpow] at hpart
    have hq_le : 1 ≤ Fintype.card F := hq_pos
    zify [hq_le]
    have hpartZ : (Fintype.card F ^ (k - 1) : ℤ) + #{w : Fin k → F | x ⬝ᵥ w ≠ 0} =
        (Fintype.card F ^ (k - 1) : ℤ) * Fintype.card F := by
      exact_mod_cast hpart
    linarith
  have hbij_dot :
      #{w : Fin k → F | x ⬝ᵥ w ≠ 0} =
        hammingNorm (simplexEncode F k x) * (Fintype.card F - 1) := by
    let e := simplexPointProdUnitsEquivNeZero F k
    have hsub :
        #{w : {w : Fin k → F // w ≠ 0} | x ⬝ᵥ w.1 ≠ 0} = #{w : Fin k → F | x ⬝ᵥ w ≠ 0} := by
      refine card_bij (fun w _ => w.1) (fun w hw => ?_) (fun _ _ _ _ h => Subtype.ext h)
        (fun w hw => ?_)
      · exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 hw).2⟩
      · have hne0 : w ≠ 0 := fun h0 => (mem_filter.1 hw).2 (by simp [h0])
        exact ⟨⟨w, hne0⟩, mem_filter.2 ⟨mem_univ _, (mem_filter.1 hw).2⟩, rfl⟩
    rw [← hsub]
    have hev :
        #{pu : SimplexPoint F k × Fˣ | x ⬝ᵥ (e pu).1 ≠ 0} =
          #{w : {w : Fin k → F // w ≠ 0} | x ⬝ᵥ w.1 ≠ 0} := by
      refine card_bij (fun pu _ => e pu) (fun pu hpu => ?_) (fun _ _ _ _ h => e.injective h)
        (fun w hw => ⟨e.symm w, ?_, e.apply_symm_apply w⟩)
      · exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 hpu).2⟩
      · simpa [mem_filter] using (mem_filter.1 hw).2
    rw [← hev]
    have hprod :
        (univ.filter fun pu : SimplexPoint F k × Fˣ => x ⬝ᵥ (e pu).1 ≠ 0) =
          (univ.filter fun p : SimplexPoint F k => simplexEncode F k x p ≠ 0) ×ˢ
            (univ : Finset Fˣ) := by
      ext ⟨p, u⟩
      simp only [e, simplexPointProdUnitsEquivNeZero, Equiv.coe_fn_mk, dotProduct_smul,
        smul_eq_mul, mul_ne_zero_iff, mem_filter, mem_univ, mem_product, true_and, and_true,
        simplexEncode_apply]
      exact ⟨fun h => mem_filter.2 ⟨mem_univ p, h.2⟩, fun h => ⟨u.ne_zero, (mem_filter.1 h).2⟩⟩
    rw [hprod, card_product, card_univ, Fintype.card_units]
    rfl
  have hq1 : 0 < Fintype.card F - 1 := by
    have := Fintype.one_lt_card (α := F)
    omega
  exact Nat.mul_right_cancel hq1 (hbij_dot.symm.trans hnonzero_dot)

/-- For `k ≥ 1`, the `$q$-ary simplex code` `simplexCode F k` has minimum distance `q ^ (k - 1)`. -/
@[simp]
theorem minDist_simplexCode {F : Type*} [Field F] [Fintype F] [DecidableEq F] {k : ℕ}
    (hk : 1 ≤ k) :
    minDist (simplexCode F k : Set (SimplexPoint F k → F)) = Fintype.card F ^ (k - 1) := by
  refine le_antisymm ?_ ?_
  · let i₀ : Fin k := ⟨0, hk⟩
    let x₀ : Fin k → F := fun j => if j = i₀ then 1 else 0
    have hx₀ : x₀ ≠ 0 := fun h => by
      have h10 : (1 : F) = 0 := by simpa [x₀] using congrFun h i₀
      exact one_ne_zero h10
    have hw₀ : simplexEncode F k x₀ ≠ 0 := fun h =>
      hx₀ (simplexEncode_injective F k (h.trans (simplexEncode F k).map_zero.symm))
    have hle := minDist_le_hammingDist (mem_simplexCode.2 ⟨x₀, rfl⟩) (simplexCode F k).zero_mem hw₀
    rw [hammingDist_zero_right, hammingNorm_simplexEncode hx₀] at hle
    exact mod_cast hle
  · refine (le_minDist_iff_hammingNorm (simplexCode F k)).2 fun w hw hw0 => ?_
    obtain ⟨x, rfl⟩ := mem_simplexCode.1 hw
    have hx0 : x ≠ 0 := fun h0 => hw0 (by simp [h0])
    rw [hammingNorm_simplexEncode hx0]
    exact mod_cast le_rfl

/-- **Tightness of the Griesmer bound**: for every finite field `F` and every dimension `k ≥ 1`,
`simplexCode F k` meets `sum_ceilDiv_pow_le_card` with exact equality. -/
theorem sum_ceilDiv_pow_simplexCode (F : Type*) [Field F] [Fintype F] [DecidableEq F] {k : ℕ}
    (hk : 1 ≤ k) :
    ∑ i ∈ range (Module.finrank F (simplexCode F k)),
        Fintype.card F ^ (k - 1) ⌈/⌉ Fintype.card F ^ i =
      Fintype.card (SimplexPoint F k) := by
  rw [finrank_simplexCode, card_simplexPoint]
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have hterm :
      ∑ i ∈ range k, Fintype.card F ^ (k - 1) ⌈/⌉ Fintype.card F ^ i =
        ∑ i ∈ range k, Fintype.card F ^ (k - 1 - i) := by
    refine sum_congr rfl fun i hi => ?_
    have hi_le : i ≤ k - 1 := by
      have := mem_range.1 hi
      omega
    have hpow : Fintype.card F ^ (k - 1) = Fintype.card F ^ i • Fintype.card F ^ (k - 1 - i) := by
      rw [smul_eq_mul, ← pow_add, Nat.add_sub_cancel' hi_le]
    rw [hpow, smul_ceilDiv (pow_pos hq i)]
  rw [hterm]
  exact sum_range_reflect (fun i => Fintype.card F ^ i) k

end Cslib.Code
