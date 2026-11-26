/-
Copyright (c) 2026 Jonathan Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Katz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.StreamArithmetic.Interface
public import CslibFrontier.Foundations.Analysis.SignedDigitStream.Reciprocal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Certified stream arithmetic primitives and composition combinators

This module constructs certified `UniformStreamRecipe` implementations for every primitive
operation in [OpenAI2026LogSpace, Sections 10.2--10.6, Lemmas 10.3--10.7]:

* **Variables, rational constants, negation, and structural guards**:
  `Cslib.StreamArithmetic.varRecipe`, `Cslib.StreamArithmetic.ratRecipe`,
  `Cslib.StreamArithmetic.UniformStreamRecipe.neg`, and
  `Cslib.StreamArithmetic.UniformStreamRecipe.guardStruct`.
* **Elementary operations and shift-clip** (**Lemmas 10.3 & 10.7**):
  `Cslib.StreamArithmetic.pairAvgPrim`, `Cslib.StreamArithmetic.maxPrim`,
  `Cslib.StreamArithmetic.minPrim`, `Cslib.StreamArithmetic.shiftClipPrim`, and direct recipe
  combinators `Cslib.StreamArithmetic.UniformStreamRecipe.pairAvg`,
  `Cslib.StreamArithmetic.UniformStreamRecipe.max`,
  `Cslib.StreamArithmetic.UniformStreamRecipe.min`, and
  `Cslib.StreamArithmetic.UniformStreamRecipe.shiftClip` (with top-down comparator slope
  `coeffB = 6` when comparing prefixes without an uncharged loop counter).
* **Balanced binary-tree averages** (**Lemma 10.7**): `Cslib.StreamArithmetic.balancedAvgPrim` and
  `Cslib.StreamArithmetic.balancedAvgRecipe` averaging `2 ^ r` streams (`r ≤ κ * d`) with
  `coeffB = 0` and `O((κ + 1) * d)` retained bits.
* **Minimum-index dyadic band multiplication** (**Lemma 10.4**): `Cslib.StreamArithmetic.mulPrim`
  and `Cslib.StreamArithmetic.UniformStreamRecipe.mul`, paying for band width `2 ^ (k - 1)` and
  band/offset counters out of the clock drop `t - j`.
* **Early-word reciprocal on `[1 / 4, 1]` and unit prefix clamping** (**Section 10.4, Lemma
  10.5**): `Cslib.StreamArithmetic.clipUnitPrefix`, `Cslib.StreamArithmetic.clippedUnitPrefixProg`,
  `Cslib.StreamArithmetic.recip64Prim`, and `Cslib.StreamArithmetic.UniformStreamRecipe.recip64`,
  forming the `(t / 2 + 8)`-place prefix (computing `1 / (64 * x)` for inputs `x ∈ [1 / 4, 1]`)
  only during early-word queries `j ≤ t / 2 + 7` and releasing it before any suffix query.
* **Zero-padded detector rank** (adapting **Lemma 10.6** to Sections 4.2 and 8.2):
  `Cslib.StreamArithmetic.zeroPaddedRankListRecipe` and
  `Cslib.StreamArithmetic.zeroPaddedRankFinsetRecipe`, computing the zero-padded
  `Finset.kthLargest` (clamping negative order statistics up to `0`) over `≤ 2 ^ (κ * d)` streams
  with `O((κ + 1) * d)` index/counter overhead and comparator slope `coeffB = 6`.

As in `QueryTree` and `Interface`, these recipes certify exact stream values and annotated
`QueryProg` query/intrinsic bounds prior to native machine compilation.

## Main definitions

* `Cslib.StreamArithmetic.varRecipe`, `Cslib.StreamArithmetic.ratRecipe`,
  `Cslib.StreamArithmetic.UniformStreamRecipe.neg`,
  `Cslib.StreamArithmetic.UniformStreamRecipe.guardStruct`.
* `Cslib.StreamArithmetic.pairAvgPrim`, `Cslib.StreamArithmetic.maxPrim`,
  `Cslib.StreamArithmetic.minPrim`, `Cslib.StreamArithmetic.shiftClipPrim`,
  `Cslib.StreamArithmetic.balancedAvgPrim`, `Cslib.StreamArithmetic.balancedAvgRecipe`.
* `Cslib.StreamArithmetic.mulPrim`, `Cslib.StreamArithmetic.recip64Prim`,
  `Cslib.StreamArithmetic.clipUnitPrefix`, `Cslib.StreamArithmetic.clippedUnitPrefixProg`.
* `Cslib.StreamArithmetic.zeroPaddedRankListRecipe`,
  `Cslib.StreamArithmetic.zeroPaddedRankFinsetRecipe`.

## Main results

* `Cslib.StreamArithmetic.eval_pairAvgResProg`, `Cslib.StreamArithmetic.eval_maxResProg`,
  `Cslib.StreamArithmetic.eval_minResProg`, `Cslib.StreamArithmetic.eval_shiftClipResProg`.
* `Cslib.StreamArithmetic.balancedAvgDigitProg_emits`: exactness and signed-digit emission for
  depth-`r` balanced binary-tree averages.
* `Cslib.StreamArithmetic.eval_intPrefixProg`, `Cslib.StreamArithmetic.eval_clippedUnitPrefixProg`,
  `Cslib.StreamArithmetic.clipUnitPrefix_le_two_pow`,
  `Cslib.StreamArithmetic.abs_clipUnitPrefix_div_sub_streamVal_le`,
  `Cslib.StreamArithmetic.eval_recip64ResProg`.
* `Cslib.StreamArithmetic.eval_zeroPaddedRankListResProg`: exact mod-16 residue evaluation for
  zero-padded `Finset.kthLargest` over duplicate-free lists.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Sections 10.2--10.6, Lemmas 10.3--10.7 (23 September 2026, revision `7ef5c0cc`,
  not peer reviewed).
-/

public section

namespace Cslib.StreamArithmetic

open Cslib.SignedDigitStream Finset

universe u u' v w w'

private theorem mem_bindOverhead_activeQueries {Op : Type u} {Struct : Type v}
    {α : Type w} {β : Type w'} {ov : ℕ} {p : QueryProg Op Struct α}
    {k : α → QueryProg Op Struct β} {env : Op → ℕ → ℤ} {sEnv : Struct → Bool}
    {ev : QueryEvent Op Struct}
    (h : ev ∈ (p.bindOverhead ov k).activeQueries env sEnv) :
    (∃ ev₀ ∈ p.activeQueries env sEnv, ev₀.addBits ov = ev) ∨
      ev ∈ (k (p.eval env sEnv)).activeQueries env sEnv := by
  simpa only [QueryProg.activeQueries_bindOverhead, List.mem_append, List.mem_map] using h

private theorem maxIntrinsicBits_bindOverhead_trans {Op : Type u} {Struct : Type v}
    {α : Type w} {β : Type w'} {ov B : ℕ} {p : QueryProg Op Struct α}
    {k : α → QueryProg Op Struct β} {env : Op → ℕ → ℤ} {sEnv : Struct → Bool}
    (hp : ov + p.maxIntrinsicBits env sEnv ≤ B)
    (hk : (k (p.eval env sEnv)).maxIntrinsicBits env sEnv ≤ B) :
    (p.bindOverhead ov k).maxIntrinsicBits env sEnv ≤ B :=
  (QueryProg.maxIntrinsicBits_bindOverhead_le ov p k env sEnv).trans (max_le hp hk)

/-! ## Variables, rational constants, negation, and structural guards -/

section BasicPrimitives

/-- Exact negation of a signed-digit stream negates its real value. -/
theorem streamVal_neg_eq (x : ℕ → ℤ) : streamVal (fun j => -x j) = -streamVal x := by
  simpa only [streamVal, Int.cast_neg, neg_div] using tsum_neg

/-- Identity `UniformStreamRecipe` reading operand `op` directly. -/
@[expose] noncomputable def varRecipe {Op : Type u} {Struct : Type v}
    (d : ℕ) (hd : 1 ≤ d) (op : Op) : UniformStreamRecipe Op Struct where
  slack := d
  slack_pos := hd
  ValidEnv env _ := IsNormSignedStream (env op)
  targetVal val _ := val op
  digitProg t := .queryDigit op t 4 .ret
  coeffA := 4
  coeffB := 0
  coeffC := 0
  intrinsicCoeff := 4
  abs_targetVal_le_one h := h.2
  emits_signed h := h.1
  emits_exact _ := rfl
  allowance t _ _ ev hev := by
    rcases List.mem_cons.mp hev with rfl | hev
    · exact ⟨Nat.le_add_right _ _, by
        simpa using (Nat.cast_le (α := ℤ)).mpr (Nat.le_mul_of_pos_right 4 hd)⟩
    · nomatch hev
  intrinsic_bound t _ _ := by
    have h4 := Nat.le_mul_of_pos_right 4 hd
    simp only [QueryProg.maxIntrinsicBits, Nat.max_zero]
    omega

/-- Constant rational `UniformStreamRecipe` emitting `ratStream q` for any `|q| ≤ 1` using
`(κ + 8) * (d + t)` scratch bits and zero oracle queries. -/
@[expose] noncomputable def ratRecipe {Op : Type u} {Struct : Type v}
    (d : ℕ) (hd : 1 ≤ d) (q : ℚ) (hq : |q| ≤ 1) (κ : ℕ := 0) :
    UniformStreamRecipe Op Struct where
  slack := d
  slack_pos := hd
  ValidEnv _ _ := True
  targetVal _ _ := (q : ℝ)
  digitProg t := .scratchStep ((κ + 8) * (d + t)) (.ret (ratStream q t))
  coeffA := 0
  coeffB := 0
  coeffC := 0
  intrinsicCoeff := κ + 8
  abs_targetVal_le_one _ := by exact_mod_cast hq
  emits_signed _ := ratStream_isSignedStream hq
  emits_exact _ := streamVal_ratStream hq
  allowance _ _ _ _ hev := nomatch hev
  intrinsic_bound _ _ _ := by simp [QueryProg.maxIntrinsicBits]

/-- Exact stream negation with zero additional query or storage overhead. -/
@[expose] noncomputable def UniformStreamRecipe.neg {Op : Type u} {Struct : Type v}
    (R : UniformStreamRecipe Op Struct) : UniformStreamRecipe Op Struct where
  slack := R.slack
  slack_pos := R.slack_pos
  ValidEnv := R.ValidEnv
  targetVal val sEnv := -R.targetVal val sEnv
  digitProg t := (R.digitProg t).map (- ·)
  coeffA := R.coeffA
  coeffB := R.coeffB
  coeffC := R.coeffC
  intrinsicCoeff := R.intrinsicCoeff
  abs_targetVal_le_one h := (abs_neg _).trans_le (R.abs_targetVal_le_one h)
  emits_signed h := by simp_rw [QueryProg.eval_map]; exact (R.emits_signed h).neg
  emits_exact h := by simp_rw [QueryProg.eval_map]; rw [streamVal_neg_eq, R.emits_exact h]
  allowance t env sEnv _ hev := R.allowance t env sEnv (QueryProg.activeQueries_map _ _ _ _ ▸ hev)
  intrinsic_bound t env sEnv :=
    (QueryProg.maxIntrinsicBits_map _ _ _ _).trans_le (R.intrinsic_bound t env sEnv)

/-- Structural indicator guard emitting `R` when `sEnv sOp = true` and `0` when
`sEnv sOp = false`, requiring `R.ValidEnv` only on the active branch `sEnv sOp = true`
[OpenAI2026LogSpace, Section 10.5]. -/
@[expose] noncomputable def UniformStreamRecipe.guardStruct {Op : Type u} {Struct : Type v}
    (R : UniformStreamRecipe Op Struct) (sOp : Struct) : UniformStreamRecipe Op Struct :=
  let zeroR := ratRecipe (Op := Op) (Struct := Struct) R.slack R.slack_pos 0 (by norm_num)
  let raw := UniformStreamRecipe.condStruct sOp R zeroR rfl
  (raw.weakenValid
    (fun env sEnv => sEnv sOp = true → R.ValidEnv env sEnv)
    (fun h => ⟨h, fun _ => trivial⟩)).congrTarget
    (fun val sEnv => if sEnv sOp then R.targetVal val sEnv else 0)
    (fun {env sEnv} _ => by
      change (if sEnv sOp then R.targetVal (fun op => streamVal (env op)) sEnv else ((0 : ℚ) : ℝ)) =
        if sEnv sOp then R.targetVal (fun op => streamVal (env op)) sEnv else 0
      rw [Rat.cast_zero])

/-- Remap operand indices inside a `QueryProg`. -/
@[expose] def QueryProg.reindexOp {Op₁ : Type u} {Op₂ : Type u'} {Struct : Type v}
    {α : Type w} (f : Op₁ → Op₂) : QueryProg Op₁ Struct α → QueryProg Op₂ Struct α
  | .ret a => .ret a
  | .scratchStep s next => .scratchStep s (reindexOp f next)
  | .queryDigit op j l next => .queryDigit (f op) j l (fun d => reindexOp f (next d))
  | .queryStruct sOp l next => .queryStruct sOp l (fun b => reindexOp f (next b))

@[simp]
theorem QueryProg.eval_reindexOp {Op₁ : Type u} {Op₂ : Type u'} {Struct : Type v}
    {α : Type w} (f : Op₁ → Op₂) (p : QueryProg Op₁ Struct α)
    (env : Op₂ → ℕ → ℤ) (sEnv : Struct → Bool) :
    (p.reindexOp f).eval env sEnv = p.eval (fun op => env (f op)) sEnv := by
  induction p with
  | ret _ => rfl
  | scratchStep _ _ ih => exact ih
  | queryDigit _ _ _ _ ih | queryStruct _ _ _ ih => exact ih _

theorem QueryProg.mem_activeQueries_reindexOp {Op₁ : Type u} {Op₂ : Type u'} {Struct : Type v}
    {α : Type w} (f : Op₁ → Op₂) (p : QueryProg Op₁ Struct α)
    (env : Op₂ → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent Op₂ Struct}
    (hev : ev ∈ (p.reindexOp f).activeQueries env sEnv) :
    (∃ sOp l, QueryEvent.struct sOp l ∈ p.activeQueries (fun op => env (f op)) sEnv ∧
        ev = .struct sOp l) ∨
      ∃ op j l, QueryEvent.digit op j l ∈ p.activeQueries (fun op => env (f op)) sEnv ∧
        ev = .digit (f op) j l := by
  induction p with
  | ret _ => nomatch hev
  | scratchStep _ _ ih => exact ih hev
  | queryDigit op j l _ ih =>
    rcases List.mem_cons.mp hev with rfl | hev
    · exact Or.inr ⟨op, j, l, List.mem_cons_self, rfl⟩
    · exact (ih (env (f op) j) hev).imp
        (fun ⟨sOp, ls, hs, h⟩ => ⟨sOp, ls, List.mem_cons_of_mem _ hs, h⟩)
        (fun ⟨o, j', l', hd, h⟩ => ⟨o, j', l', List.mem_cons_of_mem _ hd, h⟩)
  | queryStruct sOp l _ ih =>
    rcases List.mem_cons.mp hev with rfl | hev
    · exact Or.inl ⟨sOp, l, List.mem_cons_self, rfl⟩
    · exact (ih (sEnv sOp) hev).imp
        (fun ⟨sOp', ls, hs, h⟩ => ⟨sOp', ls, List.mem_cons_of_mem _ hs, h⟩)
        (fun ⟨o, j', l', hd, h⟩ => ⟨o, j', l', List.mem_cons_of_mem _ hd, h⟩)

@[simp]
theorem QueryProg.maxIntrinsicBits_reindexOp {Op₁ : Type u} {Op₂ : Type u'} {Struct : Type v}
    {α : Type w} (f : Op₁ → Op₂) (p : QueryProg Op₁ Struct α)
    (env : Op₂ → ℕ → ℤ) (sEnv : Struct → Bool) :
    (p.reindexOp f).maxIntrinsicBits env sEnv =
      p.maxIntrinsicBits (fun op => env (f op)) sEnv := by
  induction p with
  | ret _ => rfl
  | scratchStep _ _ ih => exact congrArg (max _) ih
  | queryDigit _ _ _ _ ih | queryStruct _ _ _ ih => exact congrArg (max _) (ih _)

end BasicPrimitives

/-! ## Elementary binary recipes (`pairAvg`, `max`, `min`) -/

section ElementaryRecipes

/-! ### Pairwise average -/

/-- Mod-16 residue program for `(streamVal x + streamVal y) / 2` using 9-place low windows
[OpenAI2026LogSpace, Lemma 10.3]. -/
@[expose] def pairAvgResProg {Struct : Type v} (s : ℕ) : QueryProg (Fin 2) Struct ℤ :=
  (windowPrefixModProg 0 9 (s + 4)).bindOverhead 10 fun r₀ =>
    (windowPrefixModProg 1 9 (s + 4)).bindOverhead 20 fun r₁ =>
      .scratchStep 20 (.ret (((r₀ + r₁) % 512) / 32))

theorem eval_pairAvgResProg {Struct : Type v} (s : ℕ)
    (env : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool) :
    (pairAvgResProg s).eval env sEnv = pairAvgApprox (env 0) (env 1) s % 16 := by
  simp only [pairAvgResProg, QueryProg.eval_bindOverhead, QueryProg.eval,
    eval_windowPrefixModProg, pairAvgApprox, Int.reducePow]
  rw [← Int.add_emod]
  simpa only [Nat.reduceAdd, Int.reducePow] using
    (ediv_two_pow_emod_eq (intPrefix (env 0) (s + 4) + intPrefix (env 1) (s + 4)) 4 5).symm

theorem mem_activeQueries_pairAvgResProg {Struct : Type v} (s : ℕ)
    (env : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent (Fin 2) Struct}
    (hev : ev ∈ (pairAvgResProg s).activeQueries env sEnv) :
    ∃ op j L, j ≤ s + 4 ∧ L ≤ 38 ∧ ev = .digit op j L := by
  rcases mem_bindOverhead_activeQueries hev with ⟨_, h₀, rfl⟩ | h₁
  · obtain ⟨j, hj, rfl⟩ := mem_activeQueries_windowPrefixModProg 0 9 (s + 4) env sEnv h₀
    exact ⟨0, j, 28, hj, by decide, rfl⟩
  · rcases mem_bindOverhead_activeQueries h₁ with ⟨_, h₁', rfl⟩ | h₂
    · obtain ⟨j, hj, rfl⟩ := mem_activeQueries_windowPrefixModProg 1 9 (s + 4) env sEnv h₁'
      exact ⟨1, j, 38, hj, by decide, rfl⟩
    · nomatch h₂

theorem maxIntrinsicBits_pairAvgResProg_le {Struct : Type v} (s : ℕ)
    (env : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool) :
    (pairAvgResProg s).maxIntrinsicBits env sEnv ≤ s + 46 := by
  have h0 := maxIntrinsicBits_windowPrefixModProg_le (0 : Fin 2) 9 (s + 4) env sEnv
  have h1 := maxIntrinsicBits_windowPrefixModProg_le (1 : Fin 2) 9 (s + 4) env sEnv
  refine maxIntrinsicBits_bindOverhead_trans (by omega) <|
    maxIntrinsicBits_bindOverhead_trans (by omega) ?_
  simp only [QueryProg.maxIntrinsicBits, Nat.max_zero]; omega

/-- **Lemma 10.3 (certified pairwise average primitive)** [OpenAI2026LogSpace, Lemma 10.3]. -/
@[expose] noncomputable def pairAvgPrim {Struct : Type v} (d : ℕ) (hd : 1 ≤ d) :
    UniformStreamRecipe (Fin 2) Struct :=
  recipeOfMod16Prog d hd
    (fun env _ => ∀ i, IsNormSignedStream (env i))
    (fun val _ => (val 0 + val 1) / 2)
    (fun env _ => pairAvgApprox (env 0) (env 1))
    pairAvgResProg 38 0 4 46
    (fun {env _} hV => by
      have h0 := (hV 0).2
      have h1 := (hV 1).2
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith [abs_add_le (streamVal (env 0)) (streamVal (env 1))])
    (fun hV => pairAvgApprox_isScaledApprox (hV 0).1 (hV 1).1)
    (fun _ s => eval_pairAvgResProg s _ _)
    (fun s env sEnv _ hev => by
      obtain ⟨op, j, L, hj, hL, rfl⟩ := mem_activeQueries_pairAvgResProg s env sEnv hev
      refine ⟨by have h4 := Nat.le_mul_of_pos_right 4 hd; omega, ?_⟩
      simp only [Nat.cast_zero, zero_mul, add_zero]
      exact_mod_cast hL.trans (Nat.le_mul_of_pos_right 38 hd))
    (fun s env sEnv => (maxIntrinsicBits_pairAvgResProg_le s env sEnv).trans
      (by have h46 := Nat.le_mul_of_pos_right 46 hd; rw [Nat.mul_add]; omega))

/-! ### Windowed comparison, `max`, and `min` -/

/-- Discarding the low four bits of an 8-place Euclidean window residue gives the mod-16 residue of
the floor quotient by `16`; every `windowPrefixModProg _ 8 _` residue program reads its answer this
way. -/
private theorem emod_two_pow_eight_div_sixteen (a : ℤ) :
    a % (2 : ℤ) ^ (8 : ℕ) / 16 = a / 16 % 16 := by
  simpa only [Nat.reduceAdd, Int.reducePow] using (ediv_two_pow_emod_eq a 4 4).symm

private theorem allowanceBound_digit_slope6 {Op : Type u} {Struct : Type v}
    {d a c s K B j L : ℕ} (L₀ : ℕ) (op : Op)
    (hj : j ≤ K) (hK : K ≤ s + B) (hB : B ≤ c * d)
    (hL : L ≤ L₀ + 6 * (K - j)) (hA : L₀ + 6 * B ≤ a * d) :
    AllowanceBound (Struct := Struct) d a 6 c s (.digit op j L) :=
  ⟨hj.trans (hK.trans (Nat.add_le_add_left hB s)), by
    change (L : ℤ) ≤ ((a * d : ℕ) : ℤ) + (6 : ℤ) * ((s : ℤ) - (j : ℤ))
    omega⟩

private theorem allowance_cmpWindowResProg {Struct : Type v} {d : ℕ} (hd : 1 ≤ d)
    (sel : ℤ → Fin 2) (s : ℕ) (env : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool)
    {ev : QueryEvent (Fin 2) Struct}
    (hev : ev ∈ ((cmpPrefixProg 0 1 (s + 4)).bindOverhead 6 fun c =>
      (windowPrefixModProg (sel c) 8 (s + 4)).map (· / 16)).activeQueries env sEnv) :
    AllowanceBound d 40 6 4 s ev := by
  have h40 := Nat.le_mul_of_pos_right 40 hd
  have h4 := Nat.le_mul_of_pos_right 4 hd
  rcases mem_bindOverhead_activeQueries hev with ⟨ev₀, hev₀, rfl⟩ | hev₁
  · obtain ⟨op, j, L, hj, hL, rfl⟩ := mem_activeQueries_cmpPrefixProg 0 1 (s + 4) env sEnv hev₀
    exact allowanceBound_digit_slope6 16 op hj le_rfl h4 (by omega) (by omega)
  · rw [QueryProg.activeQueries_map] at hev₁
    obtain ⟨j, hj, rfl⟩ := mem_activeQueries_windowPrefixModProg _ 8 (s + 4) env sEnv hev₁
    exact allowanceBound_digit_slope6 16 _ hj le_rfl h4 (by omega) (by omega)

private theorem eval_cmpWindowResProg {Struct : Type v} (sel : ℤ → Fin 2) (s : ℕ)
    (env : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool) :
    ((cmpPrefixProg 0 1 (s + 4)).bindOverhead 6 fun c =>
      (windowPrefixModProg (sel c) 8 (s + 4)).map (· / 16)).eval env sEnv =
      intPrefix (env (sel (cmpPrefix (env 0) (env 1) (s + 4)))) (s + 4) / 16 % 16 := by
  rw [QueryProg.eval_bindOverhead, eval_cmpPrefixProg, QueryProg.eval_map,
    eval_windowPrefixModProg, emod_two_pow_eight_div_sixteen]

private theorem maxIntrinsicBits_cmpWindowResProg_le {Struct : Type v} {d : ℕ} (hd : 1 ≤ d)
    (sel : ℤ → Fin 2) (s : ℕ) (env : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool) :
    ((cmpPrefixProg 0 1 (s + 4)).bindOverhead 6 fun c =>
      (windowPrefixModProg (sel c) 8 (s + 4)).map (· / 16)).maxIntrinsicBits env sEnv ≤
      40 * (d + s) := by
  have h40 := Nat.le_mul_of_pos_right 40 hd
  have h0 := maxIntrinsicBits_cmpPrefixProg_le (0 : Fin 2) 1 (s + 4) env sEnv
  have hw := maxIntrinsicBits_windowPrefixModProg_le
    (sel ((cmpPrefixProg 0 1 (s + 4)).eval env sEnv)) 8 (s + 4) env sEnv
  exact maxIntrinsicBits_bindOverhead_trans (B := 40 * (d + s))
    (by rw [Nat.mul_add]; omega)
    (by rw [QueryProg.maxIntrinsicBits_map, Nat.mul_add]; omega)

/-- Mod-16 residue program for `max (streamVal x) (streamVal y)`
[OpenAI2026LogSpace, Lemma 10.3]. -/
@[expose] def maxResProg {Struct : Type v} (s : ℕ) : QueryProg (Fin 2) Struct ℤ :=
  (cmpPrefixProg 0 1 (s + 4)).bindOverhead 6 fun c =>
    let win : Fin 2 := if 0 ≤ c then 0 else 1
    (windowPrefixModProg win 8 (s + 4)).map (· / 16)

theorem eval_maxResProg {Struct : Type v} (s : ℕ)
    (env : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool) :
    (maxResProg s).eval env sEnv = maxApprox (env 0) (env 1) s % 16 := by
  rw [maxResProg, eval_cmpWindowResProg, maxApprox]; split_ifs <;> rfl

/-- **Lemma 10.3 (certified binary maximum primitive)** [OpenAI2026LogSpace, Lemma 10.3]. -/
@[expose] noncomputable def maxPrim {Struct : Type v} (d : ℕ) (hd : 1 ≤ d) :
    UniformStreamRecipe (Fin 2) Struct :=
  recipeOfMod16Prog d hd
    (fun env _ => ∀ i, IsNormSignedStream (env i))
    (fun val _ => max (val 0) (val 1))
    (fun env _ => maxApprox (env 0) (env 1))
    maxResProg 40 6 4 40
    (fun hV => abs_le.mpr ⟨(abs_le.mp (hV 0).2).1.trans (le_max_left _ _),
      max_le (abs_le.mp (hV 0).2).2 (abs_le.mp (hV 1).2).2⟩)
    (fun hV => maxApprox_isScaledApprox (hV 0).1 (hV 1).1)
    (fun _ s => eval_maxResProg s _ _)
    (fun s env sEnv _ hev => by exact allowance_cmpWindowResProg hd _ s env sEnv hev)
    (fun s env sEnv => by exact maxIntrinsicBits_cmpWindowResProg_le hd _ s env sEnv)

/-- Mod-16 residue program for `min (streamVal x) (streamVal y)`
[OpenAI2026LogSpace, Lemma 10.3]. -/
@[expose] def minResProg {Struct : Type v} (s : ℕ) : QueryProg (Fin 2) Struct ℤ :=
  (cmpPrefixProg 0 1 (s + 4)).bindOverhead 6 fun c =>
    let win : Fin 2 := if c ≤ 0 then 0 else 1
    (windowPrefixModProg win 8 (s + 4)).map (· / 16)

theorem eval_minResProg {Struct : Type v} (s : ℕ)
    (env : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool) :
    (minResProg s).eval env sEnv = minApprox (env 0) (env 1) s % 16 := by
  rw [minResProg, eval_cmpWindowResProg, minApprox]; split_ifs <;> rfl

/-- **Lemma 10.3 (certified binary minimum primitive)** [OpenAI2026LogSpace, Lemma 10.3]. -/
@[expose] noncomputable def minPrim {Struct : Type v} (d : ℕ) (hd : 1 ≤ d) :
    UniformStreamRecipe (Fin 2) Struct :=
  recipeOfMod16Prog d hd
    (fun env _ => ∀ i, IsNormSignedStream (env i))
    (fun val _ => min (val 0) (val 1))
    (fun env _ => minApprox (env 0) (env 1))
    minResProg 40 6 4 40
    (fun hV => abs_le.mpr ⟨le_min (abs_le.mp (hV 0).2).1 (abs_le.mp (hV 1).2).1,
      (min_le_left _ _).trans (abs_le.mp (hV 0).2).2⟩)
    (fun hV => minApprox_isScaledApprox (hV 0).1 (hV 1).1)
    (fun _ s => eval_minResProg s _ _)
    (fun s env sEnv _ hev => by exact allowance_cmpWindowResProg hd _ s env sEnv hev)
    (fun s env sEnv => by exact maxIntrinsicBits_cmpWindowResProg_le hd _ s env sEnv)

/-! ### Binary recipe composition combinators -/

private theorem composeBinPrim_child_le {Op : Type u} {Struct : Type v}
    (R₁ R₂ : UniformStreamRecipe Op Struct) (f : UniformStreamRecipe Op Struct → ℕ)
    (i : Fin 2) :
    f (if i = 0 then R₁ else R₂) ≤ max (f R₁) (f R₂) := by
  split_ifs; exacts [le_max_left _ _, le_max_right _ _]

/-- Helper composing any normalized binary primitive on `Fin 2` with two child recipes `R₁, R₂`. -/
@[expose] noncomputable def composeBinPrim {Op : Type u} {Struct : Type v}
    (prim : UniformStreamRecipe (Fin 2) Struct)
    (hPrimValid : ∀ (env₁ : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool),
      (∀ i, IsNormSignedStream (env₁ i)) → prim.ValidEnv env₁ sEnv)
    (R₁ R₂ : UniformStreamRecipe Op Struct)
    (hSlackP : prim.slack = R₁.slack) (hSlack₂ : R₂.slack = R₁.slack) :
    UniformStreamRecipe Op Struct :=
  let child : Fin 2 → UniformStreamRecipe Op Struct := fun i => if i = 0 then R₁ else R₂
  let raw := prim.comp child
    (max R₁.coeffA R₂.coeffA)
    (max R₁.coeffB R₂.coeffB)
    (max R₁.coeffC R₂.coeffC)
    (max R₁.intrinsicCoeff R₂.intrinsicCoeff)
    (fun i => by dsimp only [child]; split_ifs <;> omega)
    (fun i => by exact composeBinPrim_child_le R₁ R₂ (·.coeffA) i)
    (fun i => by exact composeBinPrim_child_le R₁ R₂ (·.coeffB) i)
    (fun i => by exact composeBinPrim_child_le R₁ R₂ (·.coeffC) i)
    (fun i => by exact composeBinPrim_child_le R₁ R₂ (·.intrinsicCoeff) i)
  let cleaned := raw.weakenValid (fun env sEnv => R₁.ValidEnv env sEnv ∧ R₂.ValidEnv env sEnv)
    (fun ⟨h₁, h₂⟩ =>
      ⟨fun i => by dsimp only [child]; split_ifs; exacts [h₁, h₂],
        hPrimValid _ _ fun i => by
          dsimp only [child]; split_ifs; exacts [R₁.emits_norm h₁, R₂.emits_norm h₂]⟩)
  { cleaned with
    slack := R₁.slack
    slack_pos := R₁.slack_pos
    allowance := fun t env sEnv _ hev => by
      have h := cleaned.allowance t env sEnv hev
      change AllowanceBound prim.slack _ _ _ t _ at h; rwa [hSlackP] at h
    intrinsic_bound := fun t env sEnv => by
      have h := cleaned.intrinsic_bound t env sEnv
      change _ ≤ _ * (prim.slack + t) at h; rwa [hSlackP] at h }

/-- Compose two `UniformStreamRecipe`s with exact pairwise average `(R₁ + R₂) / 2`. -/
@[expose] noncomputable def UniformStreamRecipe.pairAvg {Op : Type u} {Struct : Type v}
    (R₁ R₂ : UniformStreamRecipe Op Struct) (hSlack : R₂.slack = R₁.slack) :
    UniformStreamRecipe Op Struct :=
  (composeBinPrim (pairAvgPrim R₁.slack R₁.slack_pos) (fun _ _ h => h) R₁ R₂ rfl hSlack).congrTarget
    (fun val sEnv => (R₁.targetVal val sEnv + R₂.targetVal val sEnv) / 2)
    (fun _ => rfl)

/-- Compose two `UniformStreamRecipe`s with exact binary maximum `max R₁ R₂`. -/
@[expose] noncomputable def UniformStreamRecipe.max {Op : Type u} {Struct : Type v}
    (R₁ R₂ : UniformStreamRecipe Op Struct) (hSlack : R₂.slack = R₁.slack) :
    UniformStreamRecipe Op Struct :=
  (composeBinPrim (maxPrim R₁.slack R₁.slack_pos) (fun _ _ h => h) R₁ R₂ rfl hSlack).congrTarget
    (fun val sEnv => Max.max (R₁.targetVal val sEnv) (R₂.targetVal val sEnv))
    (fun _ => rfl)

/-- Compose two `UniformStreamRecipe`s with exact binary minimum `min R₁ R₂`. -/
@[expose] noncomputable def UniformStreamRecipe.min {Op : Type u} {Struct : Type v}
    (R₁ R₂ : UniformStreamRecipe Op Struct) (hSlack : R₂.slack = R₁.slack) :
    UniformStreamRecipe Op Struct :=
  (composeBinPrim (minPrim R₁.slack R₁.slack_pos) (fun _ _ h => h) R₁ R₂ rfl hSlack).congrTarget
    (fun val sEnv => Min.min (R₁.targetVal val sEnv) (R₂.targetVal val sEnv))
    (fun _ => rfl)

end ElementaryRecipes

/-! ## Shift-clip and balanced binary-tree averages -/

section ShiftClipAndBalancedAverage

/-! ### Shift-clip recipe -/

/-- Public signed-digit stream whose `K`-place `intPrefix` equals `2 ^ m` whenever `m ≤ K + 3`
and `4 ≤ m`. -/
@[expose] def clipBoundStream (m K : ℕ) (j : ℕ) : ℤ :=
  if m ≤ K then
    if j = K - m then 1 else 0
  else if m = K + 1 then
    if j = 0 then 2 else 0
  else if m = K + 2 then
    if j = 0 then 4 else 0
  else
    if j = 0 then 6 else if j = 1 then 4 else 0

theorem clipBoundStream_isSignedStream (m K : ℕ) : IsSignedStream (clipBoundStream m K) := by
  intro j
  unfold clipBoundStream IsSignedDigit
  split_ifs <;> decide

theorem intPrefix_neg_eq (x : ℕ → ℤ) (K : ℕ) :
    intPrefix (fun j => -x j) K = -intPrefix x K := by
  simp only [intPrefix, neg_mul, sum_neg_distrib]

theorem intPrefix_clipBoundStream_eq {m K : ℕ} (hm4 : 4 ≤ m) (hmK : m ≤ K + 3) :
    intPrefix (clipBoundStream m K) K = (2 : ℤ) ^ m := by
  unfold intPrefix clipBoundStream
  rcases (by omega : m ≤ K ∨ m = K + 1 ∨ m = K + 2 ∨ m = K + 3) with hle | rfl | rfl | rfl
  · simp only [hle, ↓reduceIte, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_range]
    simp [show K - m < K + 1 by omega, show K - (K - m) = m by omega]
  · simp only [show ¬ K + 1 ≤ K by omega, ↓reduceIte, ite_mul, zero_mul, sum_ite_eq',
      mem_range, Nat.zero_lt_succ, Nat.sub_zero]; ring
  · simp only [show ¬ K + 2 ≤ K by omega, show K + 2 ≠ K + 1 by omega, ↓reduceIte, ite_mul,
      zero_mul, sum_ite_eq', mem_range, Nat.zero_lt_succ, Nat.sub_zero]; ring
  · rcases K with _ | K'; · omega
    simp only [show ¬ K' + 1 + 3 ≤ K' + 1 by omega, show K' + 1 + 3 ≠ K' + 1 + 1 by omega,
      show K' + 1 + 3 ≠ K' + 1 + 2 by omega, ↓reduceIte]
    rw [sum_range_succ', sum_range_succ', sum_eq_zero fun k _ => by simp]
    simp only [Nat.succ_ne_zero, ↓reduceIte, zero_add, Nat.add_sub_cancel, Nat.sub_zero]
    ring

/-- Mod-16 saturated positive boundary residue `⌊2 ^ (s + 4) / 16⌋ % 16` for `shiftClipApprox`. -/
@[expose] def posClipRes (s : ℕ) : ℤ :=
  if s < 4 then (2 : ℤ) ^ s else 0

/-- Mod-16 saturated negative boundary residue `(-2 ^ s) % 16` for `shiftClipApprox`. -/
@[expose] def negClipRes (s : ℕ) : ℤ :=
  if s < 4 then (-(2 : ℤ) ^ s) % 16 else 0

theorem posClipRes_eq (s : ℕ) :
    posClipRes s = ((2 : ℤ) ^ (s + 4) / 16) % 16 := by
  rcases s with _ | _ | _ | _ | s <;> simp only [posClipRes]
  any_goals decide
  simp only [show s + 1 + 1 + 1 + 1 + 4 = s + 8 by omega, pow_add, Int.reducePow]
  omega

theorem negClipRes_eq (s : ℕ) :
    negClipRes s = ((-((2 : ℤ) ^ (s + 4))) / 16) % 16 := by
  rcases s with _ | _ | _ | _ | s <;> simp only [negClipRes]
  any_goals decide
  simp only [show s + 1 + 1 + 1 + 1 + 4 = s + 8 by omega, pow_add, Int.reducePow]
  omega

/-- Mod-16 residue program for `shiftClipApprox v (env ()) s` using at most two 27-state
constant-bound prefix comparisons and an 8-bit low-residue window [OpenAI2026LogSpace, Lemma 10.7].
-/
@[expose] def shiftClipResProg {Struct : Type v} (v : ℤ) (s : ℕ) : QueryProg Unit Struct ℤ :=
  if (s : ℤ) + v + 4 < 0 then
    .scratchStep 8 (.ret 0)
  else
    let K := ((s : ℤ) + v + 4).toNat
    if K + 4 ≤ s + 4 then
      (windowPrefixModProg () 8 K).map (· / 16)
    else
      (cmpWithConstProg () (clipBoundStream (s + 4) K) K).bindOverhead 6 fun cHi =>
        if 0 ≤ cHi then
          .scratchStep 8 (.ret (posClipRes s))
        else
          (cmpWithConstProg () (fun j => -clipBoundStream (s + 4) K j) K).bindOverhead 6 fun cLo =>
            if cLo ≤ 0 then
              .scratchStep 8 (.ret (negClipRes s))
            else
              (windowPrefixModProg () 8 K).map (· / 16)

theorem eval_shiftClipResProg {Struct : Type v} (v : ℤ) (s : ℕ)
    {env : Unit → ℕ → ℤ} (hx : IsSignedStream (env ())) (sEnv : Struct → Bool) :
    (shiftClipResProg v s).eval env sEnv = shiftClipApprox v (env ()) s % 16 := by
  unfold shiftClipResProg shiftClipApprox
  split_ifs with hneg
  · rfl
  set K := ((s : ℤ) + v + 4).toNat
  set B : ℤ := (2 : ℤ) ^ (s + 4)
  by_cases hsmall : K + 4 ≤ s + 4
  · simp only [hsmall, ↓reduceIte, QueryProg.eval_map, eval_windowPrefixModProg]
    have hpow : 16 * (2 : ℤ) ^ K ≤ B := by
      rw [show (16 : ℤ) * (2 : ℤ) ^ K = (2 : ℤ) ^ (K + 4) by ring]
      exact pow_le_pow_right₀ (by decide) hsmall
    obtain ⟨_, _⟩ := abs_le.mp (abs_intPrefix_le hx K)
    rw [min_eq_right (by omega), max_eq_right (by omega), emod_two_pow_eight_div_sixteen]
  have hb_sign := clipBoundStream_isSignedStream (s + 4) K
  have hb_pref : intPrefix (clipBoundStream (s + 4) K) K = B :=
    intPrefix_clipBoundStream_eq (by omega) (by omega)
  have hB0 : 0 ≤ B := by positivity
  simp only [hsmall, ↓reduceIte, QueryProg.eval_bindOverhead, eval_cmpWithConstProg,
    cmpPrefix_nonneg_iff hx hb_sign K, hb_pref]
  by_cases hcHi : B ≤ intPrefix (env ()) K
  · simp only [hcHi, ↓reduceIte, QueryProg.eval, posClipRes_eq, min_eq_left hcHi,
      max_eq_right (by omega : -B ≤ B), B]
  simp only [hcHi, ↓reduceIte, QueryProg.eval_bindOverhead, eval_cmpWithConstProg,
    cmpPrefix_nonpos_iff hx hb_sign.neg K, intPrefix_neg_eq, hb_pref]
  have hle : intPrefix (env ()) K ≤ B := by omega
  by_cases hcLo : intPrefix (env ()) K ≤ -B
  · simp only [hcLo, ↓reduceIte, QueryProg.eval, negClipRes_eq, min_eq_right hle,
      max_eq_left hcLo, B]
  · simp only [hcLo, ↓reduceIte, QueryProg.eval_map, eval_windowPrefixModProg,
      emod_two_pow_eight_div_sixteen, min_eq_right hle,
      max_eq_right (by omega : -B ≤ intPrefix (env ()) K)]

private theorem shiftClipCutoff_le {d s κ : ℕ} {v : ℤ} (hd : 1 ≤ d)
    (hv : v ≤ ((κ * d : ℕ) : ℤ)) (hneg : ¬ ((s : ℤ) + v + 4 < 0)) :
    ((s : ℤ) + v + 4).toNat ≤ s + (κ + 4) * d := by
  have h4d := Nat.le_mul_of_pos_right 4 hd
  rw [Nat.add_mul]; omega

private theorem allowance_shiftClipResProg {Struct : Type v} {d : ℕ} (hd : 1 ≤ d)
    (v : ℤ) (κ : ℕ) (hv : v ≤ ((κ * d : ℕ) : ℤ)) (s : ℕ)
    (env : Unit → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent Unit Struct}
    (hev : ev ∈ (shiftClipResProg v s).activeQueries env sEnv) :
    AllowanceBound d (6 * κ + 44) 6 (κ + 4) s ev := by
  unfold shiftClipResProg at hev
  by_cases hneg : (s : ℤ) + v + 4 < 0
  · simp only [hneg, ↓reduceIte] at hev; nomatch hev
  simp only [hneg, ↓reduceIte] at hev
  set K := ((s : ℤ) + v + 4).toNat
  have hK_le : K ≤ s + (κ + 4) * d := shiftClipCutoff_le hd hv hneg
  have hA_le : 16 + 6 * ((κ + 4) * d) ≤ (6 * κ + 44) * d := by nlinarith
  have hWin : ∀ {ev₀}, ev₀ ∈ ((windowPrefixModProg () 8 K).map (· / 16)).activeQueries env sEnv →
      AllowanceBound d (6 * κ + 44) 6 (κ + 4) s ev₀ := fun {ev₀} h => by
    obtain ⟨j, hj, rfl⟩ := mem_activeQueries_windowPrefixModProg () 8 K env sEnv
      (QueryProg.activeQueries_map _ _ _ _ ▸ h)
    exact allowanceBound_digit_slope6 16 () hj hK_le le_rfl (by omega) hA_le
  have hCmp : ∀ bound {ev₀}, ev₀ ∈ (cmpWithConstProg () bound K).activeQueries env sEnv →
      AllowanceBound d (6 * κ + 44) 6 (κ + 4) s (ev₀.addBits 6) := fun bound {ev₀} h => by
    obtain ⟨j, L, hj, hL, rfl⟩ := mem_activeQueries_cmpWithConstProg () bound K env sEnv h
    exact allowanceBound_digit_slope6 16 () hj hK_le le_rfl (by omega) hA_le
  split_ifs at hev
  · exact hWin hev
  rcases mem_bindOverhead_activeQueries hev with ⟨_, h₀, rfl⟩ | hev₁
  · exact hCmp _ h₀
  split_ifs at hev₁; · nomatch hev₁
  rcases mem_bindOverhead_activeQueries hev₁ with ⟨_, h₀, rfl⟩ | hev₂
  · exact hCmp _ h₀
  split_ifs at hev₂; · nomatch hev₂
  exact hWin hev₂

private theorem maxIntrinsicBits_shiftClipResProg_le {Struct : Type v} {d : ℕ} (hd : 1 ≤ d)
    (v : ℤ) (κ : ℕ) (hv : v ≤ ((κ * d : ℕ) : ℤ)) (s : ℕ)
    (env : Unit → ℕ → ℤ) (sEnv : Struct → Bool) :
    (shiftClipResProg v s).maxIntrinsicBits env sEnv ≤ (6 * κ + 44) * (d + s) := by
  unfold shiftClipResProg
  split_ifs with hneg
  · simp only [QueryProg.maxIntrinsicBits, Nat.max_zero]
    exact (by omega : 8 ≤ 6 * κ + 44).trans (Nat.le_mul_of_pos_right _ (by omega))
  set K := ((s : ℤ) + v + 4).toNat
  have hK_le : K ≤ s + (κ + 4) * d := shiftClipCutoff_le hd hv hneg
  have hK_int : 6 * K + 20 ≤ (6 * κ + 44) * (d + s) := by nlinarith
  have hWin :
      ((windowPrefixModProg () 8 K).map (· / 16)).maxIntrinsicBits env sEnv ≤ 6 * K + 20 := by
    rw [QueryProg.maxIntrinsicBits_map]
    have := maxIntrinsicBits_windowPrefixModProg_le () 8 K env sEnv; omega
  have hCmp : ∀ bound, 6 + (cmpWithConstProg () bound K).maxIntrinsicBits env sEnv ≤ 6 * K + 20 :=
    fun bound => by have := maxIntrinsicBits_cmpWithConstProg_le () bound K env sEnv; omega
  dsimp only
  split_ifs
  · exact hWin.trans hK_int
  refine (maxIntrinsicBits_bindOverhead_trans (hCmp _) ?_).trans hK_int
  split_ifs; · simp [QueryProg.maxIntrinsicBits]
  refine maxIntrinsicBits_bindOverhead_trans (hCmp _) ?_
  split_ifs; · simp [QueryProg.maxIntrinsicBits]
  exact hWin

/-- **Lemma 10.7 (certified shift-and-clip primitive)** [OpenAI2026LogSpace, Lemma 10.7]:
computes `max (-1) (min 1 (2 ^ v * streamVal x))` for any integer shift `v ≤ κ * d` with
top-down comparator slope `coeffB = 6` and `O((κ + 1) * d)` slack overhead. -/
@[expose] noncomputable def shiftClipPrim {Struct : Type v}
    (d : ℕ) (hd : 1 ≤ d) (v : ℤ) (κ : ℕ) (hv : v ≤ ((κ * d : ℕ) : ℤ)) :
    UniformStreamRecipe Unit Struct :=
  recipeOfMod16Prog d hd
    (fun env _ => IsSignedStream (env ()))
    (fun val _ => shiftClipVal v (val ()))
    (fun env _ => shiftClipApprox v (env ()))
    (shiftClipResProg v) (6 * κ + 44) 6 (κ + 4) (6 * κ + 44)
    (fun _ => abs_shiftClipVal_le_one v _)
    (fun hV => shiftClipApprox_isScaledApprox v hV)
    (fun hV s => eval_shiftClipResProg v s hV _)
    (fun s env sEnv _ hev => by exact allowance_shiftClipResProg hd v κ hv s env sEnv hev)
    (fun s env sEnv => by exact maxIntrinsicBits_shiftClipResProg_le hd v κ hv s env sEnv)

/-- Apply exact shift-and-clip `max (-1) (min 1 (2 ^ v * R))` (`v ≤ κ * d`) to a
`UniformStreamRecipe`. -/
@[expose] noncomputable def UniformStreamRecipe.shiftClip {Op : Type u} {Struct : Type v}
    (R : UniformStreamRecipe Op Struct) (v : ℤ) (κ : ℕ)
    (hv : v ≤ ((κ * R.slack : ℕ) : ℤ)) : UniformStreamRecipe Op Struct :=
  let raw := (shiftClipPrim R.slack R.slack_pos v κ hv).comp (fun _ => R)
    R.coeffA R.coeffB R.coeffC R.intrinsicCoeff
    (fun _ => rfl) (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl)
  raw.weakenValid R.ValidEnv (fun h => ⟨fun _ => h, R.emits_signed h⟩)

/-! ### Balanced binary-tree averages -/

/-- Binary-tree child index embedding `Fin 2 × Fin (2 ^ r) → Fin (2 ^ (r + 1))`. -/
@[expose] def splitFinPow {r : ℕ} (b : Fin 2) (idx : Fin (2 ^ r)) : Fin (2 ^ (r + 1)) :=
  ⟨b.val * 2 ^ r + idx.val, by
    have hi := idx.isLt
    have hp : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by ring
    rcases b with ⟨_ | _ | b, hb⟩
    · simp only [Nat.zero_mul, Nat.zero_add, hp]
      omega
    · simp only [hp]
      omega
    · omega⟩

private theorem sum_fin_two_pow_succ {r : ℕ} (g : Fin (2 ^ (r + 1)) → ℝ) :
    ∑ i : Fin (2 ^ (r + 1)), g i =
      (∑ idx : Fin (2 ^ r), g (splitFinPow 0 idx)) +
        (∑ idx : Fin (2 ^ r), g (splitFinPow 1 idx)) := by
  rw [← Fin.sum_congr' g (by ring : 2 ^ r + 2 ^ r = 2 ^ (r + 1)), Fin.sum_univ_add]
  congr 1 <;> exact Finset.sum_congr rfl fun idx _ =>
    congrArg g (Fin.ext (by simp [splitFinPow, Nat.add_comm]))

/-- Direct balanced binary-tree average digit program over `2 ^ r` operand streams
[OpenAI2026LogSpace, Lemma 10.7]. -/
@[expose] def balancedAvgDigitProg {Struct : Type v} :
    (r : ℕ) → ℕ → QueryProg (Fin (2 ^ r)) Struct ℤ
  | 0, t => .queryDigit ⟨0, by decide⟩ t 4 .ret
  | r + 1, t =>
      (diffDigitProg pairAvgResProg t).substDigits 4 fun b u =>
        (balancedAvgDigitProg r u).reindexOp (splitFinPow b)

theorem balancedAvgDigitProg_emits {Struct : Type v} (r : ℕ)
    {env : Fin (2 ^ r) → ℕ → ℤ} (hEnv : ∀ i, IsNormSignedStream (env i))
    (sEnv : Struct → Bool) :
    IsSignedStream (fun t => (balancedAvgDigitProg r t).eval env sEnv) ∧
      streamVal (fun t => (balancedAvgDigitProg r t).eval env sEnv) =
        (∑ i : Fin (2 ^ r), streamVal (env i)) / (2 : ℝ) ^ r ∧
      |(∑ i : Fin (2 ^ r), streamVal (env i)) / (2 : ℝ) ^ r| ≤ 1 := by
  induction r with
  | zero =>
    simpa using ⟨(hEnv ⟨0, by decide⟩).1, rfl, (hEnv ⟨0, by decide⟩).2⟩
  | succ r ih =>
    let cEnv : Fin 2 → ℕ → ℤ := fun b u =>
      (balancedAvgDigitProg r u).eval (fun idx => env (splitFinPow b idx)) sEnv
    obtain ⟨hs0, hval0, hbnd0⟩ := ih (env := fun idx => env (splitFinPow 0 idx)) (fun _ => hEnv _)
    obtain ⟨hs1, hval1, hbnd1⟩ := ih (env := fun idx => env (splitFinPow 1 idx)) (fun _ => hEnv _)
    have htarget : (∑ i : Fin (2 ^ (r + 1)), streamVal (env i)) / (2 : ℝ) ^ (r + 1) =
        (streamVal (cEnv 0) + streamVal (cEnv 1)) / 2 := by
      rw [hval0, hval1, sum_fin_two_pow_succ, pow_succ]; ring
    have hbound : |(streamVal (cEnv 0) + streamVal (cEnv 1)) / 2| ≤ 1 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith [abs_add_le (streamVal (cEnv 0)) (streamVal (cEnv 1)), hval0 ▸ hbnd0, hval1 ▸ hbnd1]
    have happrox := pairAvgApprox_isScaledApprox hs0 hs1
    have heval : (fun t => (balancedAvgDigitProg (r + 1) t).eval env sEnv) =
        diffDigit (pairAvgApprox (cEnv 0) (cEnv 1)) := by
      ext t
      simp only [balancedAvgDigitProg, QueryProg.eval_substDigits, QueryProg.eval_reindexOp]
      exact eval_diffDigitProg pairAvgResProg _ hbound happrox
        (fun s => eval_pairAvgResProg s cEnv sEnv) t
    rw [heval, htarget]
    exact ⟨diffDigit_isSignedStream hbound happrox, streamVal_diffDigit hbound happrox, hbound⟩

private theorem mem_activeQueries_diffDigit_pairAvg {Struct : Type v} (t : ℕ)
    (cEnv : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent (Fin 2) Struct}
    (hev : ev ∈ (diffDigitProg pairAvgResProg t).activeQueries cEnv sEnv) :
    ∃ b u w, u ≤ t + 4 ∧ w ≤ 46 ∧ ev = .digit b u w := by
  cases t with
  | zero =>
    obtain ⟨b, u, w, hu, hw, rfl⟩ := mem_activeQueries_pairAvgResProg 0 cEnv sEnv
      (QueryProg.activeQueries_map _ _ _ _ ▸ hev)
    exact ⟨b, u, w, hu, hw.trans (by decide), rfl⟩
  | succ t =>
    rcases mem_bindOverhead_activeQueries hev with ⟨_, h₀, rfl⟩ | h₁
    · obtain ⟨b, u, w, hu, hw, rfl⟩ := mem_activeQueries_pairAvgResProg (t + 1) cEnv sEnv h₀
      exact ⟨b, u, 4 + w, hu, by omega, rfl⟩
    rcases mem_bindOverhead_activeQueries h₁ with ⟨_, h₀, rfl⟩ | h₂
    · obtain ⟨b, u, w, hu, hw, rfl⟩ := mem_activeQueries_pairAvgResProg t cEnv sEnv h₀
      exact ⟨b, u, 8 + w, by omega, by omega, rfl⟩
    nomatch h₂

theorem mem_activeQueries_balancedAvgDigitProg {Struct : Type v} (r t : ℕ)
    (env : Fin (2 ^ r) → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent (Fin (2 ^ r)) Struct}
    (hev : ev ∈ (balancedAvgDigitProg r t).activeQueries env sEnv) :
    ∃ op j L, j ≤ t + 4 * r ∧ L ≤ 4 + 50 * r ∧ ev = .digit op j L := by
  induction r generalizing t with
  | zero =>
    rcases List.mem_cons.mp hev with rfl | hev
    · exact ⟨⟨0, by decide⟩, t, 4, by omega, by omega, rfl⟩
    · nomatch hev
  | succ r ih =>
    rcases QueryProg.mem_activeQueries_substDigits 4 _ _ env sEnv hev with
      ⟨_, _, hs, _⟩ | ⟨b, u, w, evC, hd, hevC, rfl⟩
    · obtain ⟨_, _, _, _, _, hEq⟩ := mem_activeQueries_diffDigit_pairAvg t _ sEnv hs; nomatch hEq
    · obtain ⟨_, _, _, hu, hw, ⟨⟩⟩ := mem_activeQueries_diffDigit_pairAvg t _ sEnv hd
      rcases QueryProg.mem_activeQueries_reindexOp (splitFinPow b) _ env sEnv hevC with
        ⟨_, _, hsC, _⟩ | ⟨idx, j, l, hdC, rfl⟩
      · obtain ⟨_, _, _, _, _, hEqC⟩ := ih u _ hsC; nomatch hEqC
      · obtain ⟨_, _, _, hj, hl, ⟨⟩⟩ := ih u _ hdC
        exact ⟨splitFinPow b idx, j, w + 4 + l, by omega, by omega, rfl⟩

theorem maxIntrinsicBits_balancedAvgDigitProg_le {Struct : Type v} (r t : ℕ)
    (env : Fin (2 ^ r) → ℕ → ℤ) (sEnv : Struct → Bool) :
    (balancedAvgDigitProg r t).maxIntrinsicBits env sEnv ≤ t + 54 + 54 * r := by
  induction r generalizing t with
  | zero =>
    simp only [balancedAvgDigitProg, QueryProg.maxIntrinsicBits, Nat.max_zero]; omega
  | succ r ih =>
    apply QueryProg.maxIntrinsicBits_substDigits_le 4 _ _ env sEnv
    · cases t with
      | zero =>
        simp only [diffDigitProg, QueryProg.maxIntrinsicBits_map]
        exact (maxIntrinsicBits_pairAvgResProg_le 0 _ sEnv).trans (by omega)
      | succ t =>
        have h1 := maxIntrinsicBits_pairAvgResProg_le (t + 1)
          (fun b u => ((balancedAvgDigitProg r u).reindexOp (splitFinPow b)).eval env sEnv) sEnv
        have h0 := maxIntrinsicBits_pairAvgResProg_le t
          (fun b u => ((balancedAvgDigitProg r u).reindexOp (splitFinPow b)).eval env sEnv) sEnv
        refine maxIntrinsicBits_bindOverhead_trans (by omega) <|
          maxIntrinsicBits_bindOverhead_trans (by omega) ?_
        simp only [QueryProg.maxIntrinsicBits, Nat.max_zero]; omega
    · intro b u w hd
      obtain ⟨_, _, _, hu, hw, ⟨⟩⟩ := mem_activeQueries_diffDigit_pairAvg t _ sEnv hd
      rw [QueryProg.maxIntrinsicBits_reindexOp]
      have hch := ih u (fun idx => env (splitFinPow b idx))
      omega

/-- **Lemma 10.7 (certified balanced binary-tree average)** [OpenAI2026LogSpace, Lemma 10.7]:
averages `2 ^ r` normalized streams (`r ≤ κ * d`) in a single stage with `coeffB = 0`, clock
overshoot `4 * r ≤ (4 * κ) * d`, and `O((κ + 1) * d)` retained/intrinsic bits. -/
@[expose] noncomputable def balancedAvgPrim {Struct : Type v}
    (d : ℕ) (hd : 1 ≤ d) (r κ : ℕ) (hr : r ≤ κ * d) :
    UniformStreamRecipe (Fin (2 ^ r)) Struct where
  slack := d
  slack_pos := hd
  ValidEnv env _ := ∀ i, IsNormSignedStream (env i)
  targetVal val _ := (∑ i : Fin (2 ^ r), val i) / (2 : ℝ) ^ r
  digitProg := balancedAvgDigitProg r
  coeffA := 4 + 50 * κ
  coeffB := 0
  coeffC := 4 * κ
  intrinsicCoeff := 54 + 54 * κ
  abs_targetVal_le_one {env sEnv} hV := (by exact (balancedAvgDigitProg_emits r hV sEnv).2.2)
  emits_signed {env sEnv} hV := (balancedAvgDigitProg_emits r hV sEnv).1
  emits_exact {env sEnv} hV := (by exact (balancedAvgDigitProg_emits r hV sEnv).2.1)
  allowance t env sEnv _ hev := by
    obtain ⟨op, j, L, hj, hL, rfl⟩ := mem_activeQueries_balancedAvgDigitProg r t env sEnv hev
    have h4d : 4 ≤ 4 * d := Nat.le_mul_of_pos_right 4 hd
    have hr4 : 4 * r ≤ 4 * κ * d := by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 4 hr
    have hr50 : 50 * r ≤ 50 * κ * d := by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 50 hr
    refine ⟨by omega, ?_⟩
    simp only [Nat.cast_zero, zero_mul, add_zero]
    rw [Nat.add_mul]; omega
  intrinsic_bound t env sEnv := by
    have h1 := maxIntrinsicBits_balancedAvgDigitProg_le r t env sEnv
    have h54 : 54 ≤ 54 * d := Nat.le_mul_of_pos_right 54 hd
    have h54r : 54 * r ≤ 54 * (κ * d) := Nat.mul_le_mul_left 54 hr
    have ht : t ≤ (54 + 54 * κ) * t := Nat.le_mul_of_pos_left t (by omega)
    have hexp : (54 + 54 * κ) * (d + t) = 54 * d + 54 * (κ * d) + (54 + 54 * κ) * t := by ring
    omega

/-- Compose `2 ^ r` (`r ≤ κ * d`) child `UniformStreamRecipe`s with `balancedAvgPrim` in a single
`O(1)`-depth stage. -/
@[expose] noncomputable def balancedAvgRecipe {Op : Type u} {Struct : Type v}
    (d : ℕ) (hd : 1 ≤ d) (r κ : ℕ) (hr : r ≤ κ * d)
    (children : Fin (2 ^ r) → UniformStreamRecipe Op Struct)
    (cA cB cC cInt : ℕ)
    (hSlack : ∀ i, (children i).slack = d)
    (hA : ∀ i, (children i).coeffA ≤ cA)
    (hB : ∀ i, (children i).coeffB ≤ cB)
    (hC : ∀ i, (children i).coeffC ≤ cC)
    (hInt : ∀ i, (children i).intrinsicCoeff ≤ cInt) :
    UniformStreamRecipe Op Struct :=
  let raw := (balancedAvgPrim d hd r κ hr).comp children cA cB cC cInt hSlack hA hB hC hInt
  raw.weakenValid (fun env sEnv => ∀ i, (children i).ValidEnv env sEnv)
    (fun hV => ⟨hV, fun i => (children i).emits_norm (hV i)⟩)

end ShiftClipAndBalancedAverage

/-! ## Minimum-index dyadic band multiplication -/

section MultiplicationRecipe

/-! ### Band window geometry and scanning programs -/

/-- Decidable membership predicate for `(i, j) ∈ bandWindowPairs s 4 k`. -/
@[expose] def inBandWindow (s k i j : ℕ) : Prop :=
  bandStart k ≤ min i j ∧ min i j < bandEnd k ∧ i + j ≤ s + bandMargin k ∧ s < i + j + 4

instance instDecidableInBandWindow (s k i j : ℕ) : Decidable (inBandWindow s k i j) := by
  unfold inBandWindow
  infer_instance

private theorem mem_bandPairs_of_inBandWindow {s k i j : ℕ} (h : inBandWindow s k i j) :
    (i, j) ∈ bandPairs s k := by
  obtain ⟨hlo, hhi, hsum, _⟩ := h
  unfold bandPairs
  rw [mem_filter, mem_product, mem_range, mem_range]
  exact ⟨⟨by omega, by omega⟩, hlo, hhi, hsum⟩

private theorem bandStart_le_of_lt_maxBand {s k : ℕ} (hk : k < maxBand s) :
    bandStart k ≤ s + mulBaseMargin := by
  cases k with
  | zero => simp
  | succ m =>
    unfold maxBand at hk
    have hm : m ≤ Nat.log 2 (s + mulBaseMargin) := by omega
    unfold bandStart
    exact (Nat.pow_le_pow_right (by decide) hm).trans
      (Nat.pow_log_le_self 2 (by unfold mulBaseMargin; omega))

private theorem bandWindowSum_eq_double_sum (x y : ℕ → ℤ) (s k : ℕ) :
    bandWindowSum x y s 4 k =
      ∑ i ∈ range (s + bandMargin k + 1),
        ∑ j ∈ range (s + bandMargin k + 1),
          if inBandWindow s k i j then
            x i * y j * (2 : ℤ) ^ (s + bandMargin k - (i + j))
          else 0 := by
  simp only [bandWindowSum, bandWindowPairs, bandPairs, Finset.filter_filter, sum_filter,
    sum_product, inBandWindow, and_assoc]

/-- Inner column loop accumulating band `k` terms modulo `2 ^ (4 + bandMargin k)`. -/
@[expose] def bandScanJ {Struct : Type v} (s k i idxJ : ℕ) :
    ℕ → ℤ → QueryProg (Fin 2) Struct ℤ
  | 0, acc => .scratchStep (4 + bandMargin k + s + 24) (.ret (acc % (2 : ℤ) ^ (4 + bandMargin k)))
  | remJ + 1, acc =>
      let M := (2 : ℤ) ^ (4 + bandMargin k)
      let W := 4 + bandMargin k + 2 * k + 12
      if inBandWindow s k i idxJ then
        .queryDigit 0 i W fun d₀ =>
          .queryDigit 1 idxJ (W + 4) fun d₁ =>
            let term := d₀ * d₁ * (2 : ℤ) ^ (s + bandMargin k - (i + idxJ))
            bandScanJ s k i (idxJ + 1) remJ ((acc + term) % M)
      else
        bandScanJ s k i (idxJ + 1) remJ acc

/-- Row loop over `i ∈ range (s + bandMargin k + 1)` for band `k`. -/
@[expose] def bandScanI {Struct : Type v} (s k idxI : ℕ) :
    ℕ → ℤ → QueryProg (Fin 2) Struct ℤ
  | 0, acc => .scratchStep (4 + bandMargin k + s + 24) (.ret (acc % (2 : ℤ) ^ (4 + bandMargin k)))
  | remI + 1, acc =>
      (bandScanJ s k idxI 0 (s + bandMargin k + 1) acc).bindOverhead 0 fun acc' =>
        bandScanI s k (idxI + 1) remI acc'

/-- Outer downward band fold from `maxBand s - 1` down to `0` (`step = 0 .. maxBand s`). -/
@[expose] def bandOuterAux {Struct : Type v} (s step : ℕ) :
    ℕ → ℤ → QueryProg (Fin 2) Struct ℤ
  | 0, prevFold => .scratchStep 24 (.ret (prevFold / (2 : ℤ) ^ mulBaseMargin))
  | rem + 1, prevFold =>
      let k := maxBand s - (step + 1)
      let shift := bandMargin (k + 1) - bandMargin k
      let M := (2 : ℤ) ^ (4 + bandMargin k)
      let initAcc := (prevFold / (2 : ℤ) ^ shift) % M
      (bandScanI s k 0 (s + bandMargin k + 1) initAcc).bindOverhead 0 fun nextFold =>
        bandOuterAux s (step + 1) rem nextFold

/-- Windowed mod-16 product residue program [OpenAI2026LogSpace, Lemma 10.4]. -/
@[expose] def mulResProg {Struct : Type v} (s : ℕ) : QueryProg (Fin 2) Struct ℤ :=
  bandOuterAux s 0 (maxBand s) 0

/-! ### Evaluation correctness -/

private def rowSumTerm (x y : ℕ → ℤ) (s k i j : ℕ) : ℤ :=
  if inBandWindow s k i j then x i * y j * (2 : ℤ) ^ (s + bandMargin k - (i + j)) else 0

private theorem eval_bandScanJ {Struct : Type v} (s k i idxJ remJ : ℕ) (acc : ℤ)
    (env : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool) :
    (bandScanJ s k i idxJ remJ acc).eval env sEnv =
      (acc + ∑ j ∈ Ico idxJ (idxJ + remJ), rowSumTerm (env 0) (env 1) s k i j) %
        (2 : ℤ) ^ (4 + bandMargin k) := by
  induction remJ generalizing idxJ acc with
  | zero => simp [bandScanJ, QueryProg.eval]
  | succ remJ ih =>
    unfold bandScanJ
    rw [show idxJ + (remJ + 1) = idxJ + 1 + remJ by omega,
      sum_eq_sum_Ico_succ_bot (by omega : idxJ < idxJ + 1 + remJ)]
    by_cases hwin : inBandWindow s k i idxJ
    · simp only [hwin, ↓reduceIte, QueryProg.eval, ih, rowSumTerm]
      rw [← add_assoc, Int.add_emod (((acc + _) % _)), Int.emod_emod, ← Int.add_emod]
    · simp only [hwin, ↓reduceIte, ih, rowSumTerm, zero_add]

private theorem eval_bandScanI {Struct : Type v} (s k idxI remI : ℕ) (acc : ℤ)
    (env : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool) :
    (bandScanI s k idxI remI acc).eval env sEnv =
      (acc + ∑ i ∈ Ico idxI (idxI + remI),
          ∑ j ∈ range (s + bandMargin k + 1), rowSumTerm (env 0) (env 1) s k i j) %
        (2 : ℤ) ^ (4 + bandMargin k) := by
  induction remI generalizing idxI acc with
  | zero => simp [bandScanI, QueryProg.eval]
  | succ remI ih =>
    simp only [bandScanI, QueryProg.eval_bindOverhead, eval_bandScanJ, ih, Nat.zero_add,
      ← Finset.range_eq_Ico]
    rw [show idxI + (remI + 1) = idxI + 1 + remI by omega,
      sum_eq_sum_Ico_succ_bot (by omega : idxI < idxI + 1 + remI),
      ← add_assoc, Int.add_emod (((acc + _) % _)), Int.emod_emod, ← Int.add_emod]

theorem eval_mulResProg {Struct : Type v} (s : ℕ)
    (env : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool) :
    (mulResProg s).eval env sEnv = mulApprox (env 0) (env 1) s % 16 := by
  suffices h : ∀ step rem, step + rem = maxBand s →
      (bandOuterAux s step rem (bandFoldMod (env 0) (env 1) s 4 step)).eval env sEnv =
        mulResidue (env 0) (env 1) s 4 from
    (h 0 (maxBand s) (Nat.zero_add _)).trans (mulResidue_eq_mulApprox_emod _ _ s 4)
  intro step rem
  induction rem generalizing step with
  | zero => rintro rfl; rfl
  | succ rem ih =>
    intro hsum
    simp only [bandOuterAux, QueryProg.eval_bindOverhead, eval_bandScanI, Nat.zero_add,
      ← Finset.range_eq_Ico]
    set k := maxBand s - (step + 1)
    rw [show ∑ i ∈ range (s + bandMargin k + 1), ∑ j ∈ range (s + bandMargin k + 1),
        rowSumTerm (env 0) (env 1) s k i j = bandWindowSum (env 0) (env 1) s 4 k from
      (bandWindowSum_eq_double_sum (env 0) (env 1) s k).symm,
      show ((bandFoldMod (env 0) (env 1) s 4 step /
            (2 : ℤ) ^ (bandMargin (k + 1) - bandMargin k)) % (2 : ℤ) ^ (4 + bandMargin k) +
          bandWindowSum (env 0) (env 1) s 4 k) % (2 : ℤ) ^ (4 + bandMargin k) =
          bandFoldMod (env 0) (env 1) s 4 (step + 1) by
        simp only [bandFoldMod]
        rw [add_comm, Int.add_emod (bandWindowSum _ _ _ _ _), Int.emod_emod, ← Int.add_emod]]
    exact ih (step + 1) (by omega)

/-! ### Active queries, allowance, and intrinsic bit bounds -/

private theorem mem_activeQueries_bandScanJ {Struct : Type v} (s k i idxJ remJ : ℕ) (acc : ℤ)
    (env : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent (Fin 2) Struct}
    (hev : ev ∈ (bandScanJ s k i idxJ remJ acc).activeQueries env sEnv) :
    ∃ op idx L, (∃ j, inBandWindow s k i j ∧ (idx = i ∨ idx = j)) ∧
      L ≤ 4 + bandMargin k + 2 * k + 16 ∧ ev = .digit op idx L := by
  induction remJ generalizing idxJ acc with
  | zero => nomatch hev
  | succ remJ ih =>
    unfold bandScanJ at hev
    by_cases hwin : inBandWindow s k i idxJ
    · simp only [hwin, ↓reduceIte, QueryProg.activeQueries, List.mem_cons] at hev
      rcases hev with rfl | rfl | hev
      · exact ⟨0, i, _, ⟨idxJ, hwin, Or.inl rfl⟩, by omega, rfl⟩
      · exact ⟨1, idxJ, _, ⟨idxJ, hwin, Or.inr rfl⟩, le_rfl, rfl⟩
      · exact ih (idxJ + 1) _ hev
    · simp only [hwin, ↓reduceIte] at hev
      exact ih (idxJ + 1) _ hev

private theorem mem_activeQueries_bandScanI {Struct : Type v} (s k idxI remI : ℕ) (acc : ℤ)
    (env : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent (Fin 2) Struct}
    (hev : ev ∈ (bandScanI s k idxI remI acc).activeQueries env sEnv) :
    ∃ op idx L, (∃ i j, inBandWindow s k i j ∧ (idx = i ∨ idx = j)) ∧
      L ≤ 4 + bandMargin k + 2 * k + 16 ∧ ev = .digit op idx L := by
  induction remI generalizing idxI acc with
  | zero => nomatch hev
  | succ remI ih =>
    rcases mem_bindOverhead_activeQueries hev with ⟨ev₀, hev₀, rfl⟩ | hev₁
    · obtain ⟨op, idx, L, ⟨j, hwin, hidx⟩, hL, rfl⟩ :=
        mem_activeQueries_bandScanJ s k idxI 0 _ acc env sEnv hev₀
      exact ⟨op, idx, 0 + L, ⟨idxI, j, hwin, hidx⟩, by omega, rfl⟩
    · exact ih (idxI + 1) _ hev₁

private theorem allowance_bandScanI {Struct : Type v} {d : ℕ} (hd : 1 ≤ d)
    (s k idxI remI : ℕ) (acc : ℤ)
    (env : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool) {ev₀ : QueryEvent (Fin 2) Struct}
    (hev₀ : ev₀ ∈ (bandScanI s k idxI remI acc).activeQueries env sEnv) :
    AllowanceBound d 58 1 16 s (ev₀.addBits 0) := by
  obtain ⟨op, idx, L, ⟨i, j, hwin, hidx⟩, hL, rfl⟩ :=
    mem_activeQueries_bandScanI s k idxI remI acc env sEnv hev₀
  have hp := mem_bandPairs_of_inBandWindow hwin
  have hidx_le := index_le_clock_add_baseMargin hp
  have h2k := ten_add_two_mul_le_bandMargin k
  have h16d := Nat.le_mul_of_pos_right 16 hd
  have h58d := Nat.le_mul_of_pos_right 58 hd
  have hdrop : 4 * idx + 3 * bandStart k ≤ 4 * (s + 16) := by
    cases k with
    | zero => simp only [bandStart_zero, mul_zero, add_zero]; unfold mulBaseMargin at hidx_le
              rcases hidx with rfl | rfl <;> omega
    | succ m =>
      have h3 := three_mul_bandStart_le_four_mul_drop hp
      unfold mulBaseMargin at hidx_le h3; rcases hidx with rfl | rfl <;> omega
  unfold bandMargin mulBaseMargin at hidx_le hL h2k
  refine ⟨by rcases hidx with rfl | rfl <;> omega, ?_⟩
  change ((0 + L : ℕ) : ℤ) ≤ ((58 * d : ℕ) : ℤ) + (1 : ℤ) * ((s : ℤ) - (idx : ℤ))
  omega

theorem allowance_mulResProg {Struct : Type v} {d : ℕ} (hd : 1 ≤ d) (s : ℕ)
    (env : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent (Fin 2) Struct}
    (hev : ev ∈ (mulResProg s).activeQueries env sEnv) :
    AllowanceBound d 58 1 16 s ev := by
  suffices h : ∀ step rem prevFold,
      ev ∈ (bandOuterAux s step rem prevFold).activeQueries env sEnv →
      AllowanceBound d 58 1 16 s ev from h 0 (maxBand s) 0 hev
  intro step rem
  induction rem generalizing step with
  | zero => exact fun _ h => nomatch h
  | succ rem ih =>
    intro prevFold h
    rcases mem_bindOverhead_activeQueries h with ⟨_, hev₀, rfl⟩ | h₁
    · exact allowance_bandScanI hd s (maxBand s - (step + 1)) 0 _ _ env sEnv hev₀
    · exact ih (step + 1) _ h₁

private theorem maxIntrinsicBits_bandScanJ_le {Struct : Type v} (s k i idxJ remJ : ℕ) (acc : ℤ)
    (env : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool) :
    (bandScanJ s k i idxJ remJ acc).maxIntrinsicBits env sEnv ≤
      2 * bandMargin k + s + 28 := by
  have h2k := ten_add_two_mul_le_bandMargin k
  induction remJ generalizing idxJ acc with
  | zero => simp only [bandScanJ, QueryProg.maxIntrinsicBits, Nat.max_zero]; omega
  | succ remJ ih =>
    unfold bandScanJ; split_ifs
    · exact max_le (by omega) (max_le (by omega) (ih (idxJ + 1) _))
    · exact ih (idxJ + 1) _

private theorem maxIntrinsicBits_bandScanI_le {Struct : Type v} (s k idxI remI : ℕ) (acc : ℤ)
    (env : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool) :
    (bandScanI s k idxI remI acc).maxIntrinsicBits env sEnv ≤
      2 * bandMargin k + s + 28 := by
  induction remI generalizing idxI acc with
  | zero => simp only [bandScanI, QueryProg.maxIntrinsicBits, Nat.max_zero]; omega
  | succ remI ih =>
    exact maxIntrinsicBits_bindOverhead_trans
      (by rw [Nat.zero_add]; exact maxIntrinsicBits_bandScanJ_le s k idxI 0 _ acc env sEnv)
      (ih _ _)

theorem maxIntrinsicBits_mulResProg_le {Struct : Type v} {d : ℕ} (hd : 1 ≤ d) (s : ℕ)
    (env : Fin 2 → ℕ → ℤ) (sEnv : Struct → Bool) :
    (mulResProg s).maxIntrinsicBits env sEnv ≤ 76 * (d + s) := by
  suffices h : ∀ step rem prevFold, step + rem = maxBand s →
      (bandOuterAux s step rem prevFold).maxIntrinsicBits env sEnv ≤ 76 * (d + s) from
    h 0 (maxBand s) 0 (Nat.zero_add _)
  intro step rem
  induction rem generalizing step with
  | zero => intro _ _; simp only [bandOuterAux, QueryProg.maxIntrinsicBits, Nat.max_zero]; omega
  | succ rem ih =>
    intro prevFold hsum
    refine maxIntrinsicBits_bindOverhead_trans ?_ (ih _ _ (by omega))
    set k := maxBand s - (step + 1)
    have hbs : bandStart k ≤ s + 16 := bandStart_le_of_lt_maxBand (by omega)
    have hbm : bandMargin k ≤ 16 + (s + 16) / 4 :=
      Nat.add_le_add_left (Nat.div_le_div_right hbs) 16
    have hscan := maxIntrinsicBits_bandScanI_le s k 0 (s + bandMargin k + 1)
      ((prevFold / (2 : ℤ) ^ (bandMargin (k + 1) - bandMargin k)) % (2 : ℤ) ^ (4 + bandMargin k))
      env sEnv
    omega

/-! ### Certified multiplication recipe -/

/-- **Lemma 10.4 (certified minimum-index band multiplication primitive)**
[OpenAI2026LogSpace, Lemma 10.4]. -/
@[expose] noncomputable def mulPrim {Struct : Type v} (d : ℕ) (hd : 1 ≤ d) :
    UniformStreamRecipe (Fin 2) Struct :=
  recipeOfMod16Prog d hd
    (fun env _ => ∀ i, IsNormSignedStream (env i))
    (fun val _ => val 0 * val 1)
    (fun env _ => mulApprox (env 0) (env 1))
    mulResProg 58 1 16 76
    (fun hV => by
      rw [abs_mul]
      exact (mul_le_mul (hV 0).2 (hV 1).2 (abs_nonneg _) zero_le_one).trans_eq (one_mul 1))
    (fun hV => mulApprox_isScaledApprox (hV 0).1 (hV 1).1)
    (fun _ s => eval_mulResProg s _ _)
    (fun s env sEnv _ hev => allowance_mulResProg hd s env sEnv hev)
    (fun s env sEnv => maxIntrinsicBits_mulResProg_le hd s env sEnv)

/-- Compose two `UniformStreamRecipe`s with exact multiplication `R₁ * R₂`. -/
@[expose] noncomputable def UniformStreamRecipe.mul {Op : Type u} {Struct : Type v}
    (R₁ R₂ : UniformStreamRecipe Op Struct) (hSlack : R₂.slack = R₁.slack) :
    UniformStreamRecipe Op Struct :=
  (composeBinPrim (mulPrim R₁.slack R₁.slack_pos) (fun _ _ h => h) R₁ R₂ rfl hSlack).congrTarget
    (fun val sEnv => R₁.targetVal val sEnv * R₂.targetVal val sEnv)
    (fun _ => rfl)

end MultiplicationRecipe

/-! ## Early-word reciprocal and unit prefix clamping -/

section ReciprocalRecipe

/-! ### Integer prefix queries and unit-interval clamping -/

/-- Tail-recursive early-word integer prefix builder charging `cntBits + idx + 8` retained bits at
query `idx` (`cntBits` bits for the bounded place counter `idx ≤ K` plus `idx + 8` bits for the
growing prefix accumulator). -/
@[expose] def intPrefixAux {Op : Type u} {Struct : Type v} (op : Op) (cntBits idx : ℕ) :
    ℕ → ℤ → QueryProg Op Struct ℤ
  | 0, acc => .scratchStep (cntBits + idx + 8) (.ret acc)
  | rem + 1, acc =>
      .queryDigit op idx (cntBits + idx + 8) fun d =>
        intPrefixAux op cntBits (idx + 1) rem (2 * acc + d)

/-- Query program computing `intPrefix (env op) K` while retaining at most `2 * K + 8` bits
(including the place counter up to `K`). -/
@[expose] def intPrefixProg {Op : Type u} {Struct : Type v} (op : Op) (K : ℕ) :
    QueryProg Op Struct ℤ :=
  intPrefixAux op K 0 (K + 1) 0

theorem eval_intPrefixProg {Op : Type u} {Struct : Type v} (op : Op) (K : ℕ)
    (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) :
    (intPrefixProg op K).eval env sEnv = intPrefix (env op) K := by
  have haux : ∀ rem n,
      (intPrefixAux op K (n + 1) rem (intPrefix (env op) n)).eval env sEnv =
        intPrefix (env op) (n + rem) := by
    intro rem
    induction rem with
    | zero => exact fun _ => rfl
    | succ rem ih =>
      intro n
      rw [intPrefixAux, QueryProg.eval, ← intPrefix_succ, ih (n + 1)]
      exact congrArg _ (by omega)
  rw [intPrefixProg, intPrefixAux, QueryProg.eval, mul_zero, Int.zero_add,
    ← intPrefix_zero (env op), haux K 0, Nat.zero_add]

theorem mem_activeQueries_intPrefixProg {Op : Type u} {Struct : Type v} (op : Op) (K : ℕ)
    (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent Op Struct}
    (hev : ev ∈ (intPrefixProg op K).activeQueries env sEnv) :
    ∃ j ≤ K, ev = .digit op j (K + j + 8) := by
  suffices h : ∀ idx rem acc, ev ∈ (intPrefixAux op K idx rem acc).activeQueries env sEnv →
      ∃ j < idx + rem, ev = .digit op j (K + j + 8) by
    exact (h 0 (K + 1) 0 hev).imp fun j ⟨hj, e⟩ => ⟨by omega, e⟩
  intro idx rem acc h
  induction rem generalizing idx acc with
  | zero => nomatch h
  | succ rem ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨idx, by omega, rfl⟩
    · exact (ih (idx + 1) _ h).imp fun j ⟨hj, e⟩ => ⟨by omega, e⟩

theorem maxIntrinsicBits_intPrefixProg_le {Op : Type u} {Struct : Type v} (op : Op) (K : ℕ)
    (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) :
    (intPrefixProg op K).maxIntrinsicBits env sEnv ≤ 2 * K + 9 := by
  suffices h : ∀ idx rem acc,
      (intPrefixAux op K idx rem acc).maxIntrinsicBits env sEnv ≤ K + idx + rem + 8 from
    (h 0 (K + 1) 0).trans (by omega)
  intro idx rem acc
  induction rem generalizing idx acc with
  | zero => simp only [intPrefixAux, QueryProg.maxIntrinsicBits, Nat.max_zero]; omega
  | succ rem ih =>
    exact max_le (by omega) ((ih (idx + 1) _).trans (by omega))

/-- Clamp a `K`-place signed-digit integer prefix into the canonical nonnegative range
`{0, ..., 2 ^ K}` [OpenAI2026LogSpace, Section 10.4, Lemma 10.5]. -/
@[expose] def clipUnitPrefix (K : ℕ) (P : ℤ) : ℕ :=
  (min ((2 : ℤ) ^ K) (max 0 P)).toNat

/-- Query program computing the `{0, ..., 2 ^ K}`-clamped integer prefix of `env op` at place `K`
[OpenAI2026LogSpace, Section 10.4, Lemma 10.5]. -/
@[expose] def clippedUnitPrefixProg {Op : Type u} {Struct : Type v} (op : Op) (K : ℕ) :
    QueryProg Op Struct ℕ :=
  (intPrefixProg op K).map (clipUnitPrefix K)

theorem eval_clippedUnitPrefixProg {Op : Type u} {Struct : Type v} (op : Op) (K : ℕ)
    (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) :
    (clippedUnitPrefixProg op K).eval env sEnv = clipUnitPrefix K (intPrefix (env op) K) := by
  rw [clippedUnitPrefixProg, QueryProg.eval_map, eval_intPrefixProg]

theorem clipUnitPrefix_le_two_pow (K : ℕ) (P : ℤ) : clipUnitPrefix K P ≤ 2 ^ K :=
  Int.toNat_le.mpr (by exact_mod_cast min_le_left ((2 : ℤ) ^ K) (max 0 P))

theorem abs_clipUnitPrefix_div_sub_streamVal_le {x : ℕ → ℤ} (hx : IsSignedStream x)
    (hx_mem : streamVal x ∈ Set.Icc (0 : ℝ) 1) (K : ℕ) :
    |(clipUnitPrefix K (intPrefix x K) : ℝ) / (2 : ℝ) ^ K - streamVal x| ≤ 6 / (2 : ℝ) ^ K := by
  set P := intPrefix x K
  set M : ℤ := min ((2 : ℤ) ^ K) (max 0 P)
  have hcast : ((clipUnitPrefix K P : ℕ) : ℝ) = (M : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (le_min (by positivity) (le_max_left 0 P))
  have h2K : (0 : ℝ) < (2 : ℝ) ^ K := by positivity
  set V : ℝ := streamVal x * (2 : ℝ) ^ K
  have hdiff : |(M : ℝ) - V| ≤ |(P : ℝ) - V| := by
    have hV0 : 0 ≤ V := mul_nonneg hx_mem.1 h2K.le
    have hVK : V ≤ (2 : ℝ) ^ K := mul_le_of_le_one_left h2K.le hx_mem.2
    have hMR : (M : ℝ) = min ((2 : ℝ) ^ K) (max (P : ℝ) 0) := by
      dsimp only [M]; push_cast; rw [max_comm]
    refine (show |min ((2 : ℝ) ^ K) (max (P : ℝ) 0) - min ((2 : ℝ) ^ K) (max V 0)| ≤
        |(P : ℝ) - V| from (abs_min_sub_min_le_max _ _ _ _).trans ?_).trans_eq' ?_
    · rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)]
      exact abs_max_sub_max_le_abs _ _ _
    · rw [hMR, max_eq_left hV0, min_eq_right hVK]
  refine le_trans ?_ (by simpa only [abs_sub_comm] using abs_streamVal_sub_streamPrefix_le hx K)
  rw [hcast, streamPrefix_eq_intPrefix_div,
    show (M : ℝ) / (2 : ℝ) ^ K - streamVal x = ((M : ℝ) - V) / (2 : ℝ) ^ K by
      rw [sub_div, mul_div_cancel_right₀ _ h2K.ne'],
    show (P : ℝ) / (2 : ℝ) ^ K - streamVal x = ((P : ℝ) - V) / (2 : ℝ) ^ K by
      rw [sub_div, mul_div_cancel_right₀ _ h2K.ne'],
    abs_div, abs_div, abs_of_pos h2K]
  exact div_le_div_of_nonneg_right hdiff h2K.le

/-! ### Virtual reciprocal composition and evaluation -/

/-- Fixed slack-1 inner recipe computing `(v₀ + v₁ * v₂) / 2` over virtual streams `Fin 3`. -/
@[expose] noncomputable def recipHalfVirtualRecipe {Struct : Type v} :
    UniformStreamRecipe (Fin 3) Struct :=
  let prodR := (varRecipe 1 le_rfl (1 : Fin 3)).mul (varRecipe 1 le_rfl (2 : Fin 3)) rfl
  (varRecipe 1 le_rfl (0 : Fin 3)).pairAvg prodR rfl

/-- Virtual 3-operand environment `[ratStream α, ratStream β, suffixStream x (recipCutoff s)]`. -/
@[expose] def recipVirtualEnv (x : ℕ → ℤ) (s : ℕ) (i : Fin 3) : ℕ → ℤ :=
  if i = 0 then ratStream (recipAlpha x s)
  else if i = 1 then ratStream (recipBeta x s)
  else suffixStream x (recipCutoff s)

private theorem abs_recipProd_val_le {x : ℕ → ℤ} (hx : IsSignedStream x)
    (hx_mem : streamVal x ∈ Set.Icc (1 / 4 : ℝ) 1) (s : ℕ) :
    |(recipBeta x s : ℝ) * (streamVal x - (recipPrefixRat x s : ℝ))| ≤ 3 / 64 := by
  rw [abs_mul]
  simpa only [one_mul] using mul_le_mul
    (by exact_mod_cast abs_recipBeta_le_one hx hx_mem s : |(recipBeta x s : ℝ)| ≤ 1)
    (abs_tail_recipCutoff_le hx s) (abs_nonneg _) zero_le_one

private theorem eval_recipProdVirtual {Struct : Type v} {x : ℕ → ℤ}
    (hx : IsSignedStream x) (hx_mem : streamVal x ∈ Set.Icc (1 / 4 : ℝ) 1)
    (s : ℕ) (sEnv : Struct → Bool) (r : ℕ) :
    (((varRecipe 1 le_rfl (1 : Fin 3)).mul (varRecipe 1 le_rfl (2 : Fin 3)) rfl).digitProg r).eval
        (recipVirtualEnv x s) sEnv = recipProdStream x s r := by
  have hβ := abs_recipBeta_le_one hx hx_mem s
  change ((diffDigitProg mulResProg r).substDigits 4 _).eval _ sEnv = _
  rw [QueryProg.eval_substDigits]
  let cMul : Fin 2 → ℕ → ℤ := fun b =>
    if b = 0 then ratStream (recipBeta x s) else suffixStream x (recipCutoff s)
  have hmul : (fun (b : Fin 2) w =>
      ((if b = 0 then varRecipe 1 le_rfl (1 : Fin 3)
        else varRecipe 1 le_rfl (2 : Fin 3)).digitProg w).eval (recipVirtualEnv x s) sEnv) =
      cMul := by ext b w; fin_cases b <;> rfl
  rw [hmul]
  exact eval_diffDigitProg mulResProg _
    (by simpa only [show cMul 0 = ratStream (recipBeta x s) from rfl,
          show cMul 1 = suffixStream x (recipCutoff s) from rfl,
          streamVal_ratStream hβ, streamVal_suffixStream hx, recipPrefixRat_cast] using
        (abs_recipProd_val_le hx hx_mem s).trans (by norm_num))
    (mulApprox_isScaledApprox (ratStream_isSignedStream hβ) (suffixStream_isSignedStream hx _))
    (fun t => eval_mulResProg t cMul sEnv) r

private theorem eval_recipHalfVirtualRecipe {Struct : Type v} {x : ℕ → ℤ}
    (hx : IsSignedStream x) (hx_mem : streamVal x ∈ Set.Icc (1 / 4 : ℝ) 1)
    (s : ℕ) (sEnv : Struct → Bool) (u : ℕ) :
    (recipHalfVirtualRecipe.digitProg u).eval (recipVirtualEnv x s) sEnv =
      recipHalfStream x s u := by
  have hα := abs_recipAlpha_le_one hx hx_mem s
  change ((diffDigitProg pairAvgResProg u).substDigits 4 _).eval _ sEnv = _
  rw [QueryProg.eval_substDigits]
  let cAvg : Fin 2 → ℕ → ℤ := fun b =>
    if b = 0 then ratStream (recipAlpha x s) else recipProdStream x s
  have hchild : (fun (b : Fin 2) w =>
      ((if b = 0 then varRecipe 1 le_rfl (0 : Fin 3)
        else ((varRecipe 1 le_rfl (1 : Fin 3)).mul (varRecipe 1 le_rfl (2 : Fin 3)) rfl)).digitProg
          w).eval (recipVirtualEnv x s) sEnv) = cAvg := by
    ext b w; fin_cases b; exacts [rfl, eval_recipProdVirtual hx hx_mem s sEnv w]
  rw [hchild]
  have hbavg : |(streamVal (cAvg 0) + streamVal (cAvg 1)) / 2| ≤ 1 := by
    rw [show cAvg 0 = ratStream (recipAlpha x s) from rfl,
      show cAvg 1 = recipProdStream x s from rfl,
      streamVal_ratStream hα, streamVal_recipProdStream hx hx_mem s, abs_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hαR : |(recipAlpha x s : ℝ)| ≤ 1 := by exact_mod_cast hα
    have hpR := abs_recipProd_val_le hx hx_mem s
    linarith [abs_add_le (recipAlpha x s : ℝ)
      ((recipBeta x s : ℝ) * (streamVal x - (recipPrefixRat x s : ℝ)))]
  exact eval_diffDigitProg pairAvgResProg _ hbavg
    (pairAvgApprox_isScaledApprox (ratStream_isSignedStream hα)
      (recipProdStream_isSignedStream hx hx_mem s))
    (fun t => eval_pairAvgResProg t cAvg sEnv) u

private theorem recip64Approx_emod_sixteen {x : ℕ → ℤ}
    (hx : IsSignedStream x) (hx_mem : streamVal x ∈ Set.Icc (1 / 4 : ℝ) 1) (s : ℕ) :
    recip64Approx x s % 16 =
      (intPrefix (recipHalfStream x s) (s + 8) % (2 : ℤ) ^ (11 : ℕ)) / 128 := by
  set y := recipHalfStream x s
  have hα_le : |(recipAlpha x s : ℝ)| ≤ 1 / 12 := by
    have hlo := (recipPrefixRat_mem_Icc hx hx_mem s).1
    unfold recipAlpha; push_cast
    rw [abs_of_pos (div_pos (by norm_num) (by linarith))]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hy_val : |streamVal y| ≤ 1 / 8 := by
    rw [streamVal_recipHalfStream hx hx_mem s, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_add_le (recipAlpha x s : ℝ)
      ((recipBeta x s : ℝ) * (streamVal x - (recipPrefixRat x s : ℝ))),
      abs_recipProd_val_le hx hx_mem s]
  have hy_err := abs_streamVal_sub_streamPrefix_le (recipHalfStream_isSignedStream hx hx_mem s)
    (s + 8)
  have herr_le : (6 : ℝ) / (2 : ℝ) ^ (s + 8) ≤ 6 / 256 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      ((by norm_num : (256 : ℝ) = (2 : ℝ) ^ (8 : ℕ)) ▸ pow_le_pow_right₀ (by norm_num) (by omega))
  have hint_le : |intPrefix y (s + 8)| ≤ (2 : ℤ) ^ (s + 7) := by
    have hpref : |streamPrefix y (s + 8)| ≤ 1 / 2 := by
      have htri := abs_sub_le (streamPrefix y (s + 8)) (streamVal y) 0
      simp only [sub_zero] at htri; rw [abs_sub_comm] at hy_err; linarith
    rw [streamPrefix_eq_intPrefix_div, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ (s + 8)),
      div_le_iff₀ (by positivity)] at hpref
    exact_mod_cast (by
      rwa [show (1 / 2 : ℝ) * (2 : ℝ) ^ (s + 8) = (((2 : ℤ) ^ (s + 7) : ℤ) : ℝ) by
        push_cast; ring, ← Int.cast_abs] at hpref :
        ((|intPrefix y (s + 8)| : ℤ) : ℝ) ≤ (((2 : ℤ) ^ (s + 7) : ℤ) : ℝ))
  obtain ⟨hlo, hhi⟩ := abs_le.mp hint_le
  unfold recip64Approx shiftClipApprox
  simp only [show ¬ ((s + 3 : ℕ) : ℤ) + 1 + 4 < 0 by omega, ↓reduceIte,
    show (((s + 3 : ℕ) : ℤ) + 1 + 4).toNat = s + 8 by omega, show s + 3 + 4 = s + 7 by omega]
  rw [min_eq_right hhi, max_eq_right hlo, Int.ediv_ediv_of_nonneg (by decide),
    show (16 : ℤ) * 8 = (2 : ℤ) ^ (7 : ℕ) by decide,
    show (16 : ℤ) = (2 : ℤ) ^ (4 : ℕ) by decide,
    ediv_two_pow_emod_eq, show (2 : ℤ) ^ (7 : ℕ) = 128 by decide]

/-- Outer fixed-depth query program over the 3 virtual reciprocal streams. -/
@[expose] noncomputable def recipOuterProg {Struct : Type v} (s : ℕ) :
    QueryProg (Fin 3) Struct ℤ :=
  ((windowPrefixModProg () 11 (s + 8)).map (· / 128)).substDigits 4 fun _ u =>
    recipHalfVirtualRecipe.digitProg u

/-- Early-word / suffix child query programs realizing `recipVirtualEnv`:
forms `intPrefix (env ()) (recipCutoff s)` only on streams `0, 1` (`j ≤ recipCutoff s`) and
releases it before returning, while stream `2` (`suffixStream`) queries `env ()` directly only at
places `r > recipCutoff s` with zero retained prefix bits [OpenAI2026LogSpace, Lemma 10.5]. -/
@[expose] def recipChild {Struct : Type v} (s : ℕ) (op : Fin 3) (r : ℕ) :
    QueryProg Unit Struct ℤ :=
  if op = 0 then
    (intPrefixProg () (recipCutoff s)).bindOverhead 0 fun P =>
      let x0 : ℚ := (P : ℚ) / (2 : ℚ) ^ recipCutoff s
      .scratchStep (8 * (s + r + 8)) (.ret (ratStream (1 / (64 * x0)) r))
  else if op = 1 then
    (intPrefixProg () (recipCutoff s)).bindOverhead 0 fun P =>
      let x0 : ℚ := (P : ℚ) / (2 : ℚ) ^ recipCutoff s
      .scratchStep (8 * (s + r + 8)) (.ret (ratStream (-1 / (64 * x0 ^ 2)) r))
  else
    if r ≤ recipCutoff s then .ret 0 else .queryDigit () r 0 .ret

/-- Mod-16 residue program for `recip64Approx (env ()) s` [OpenAI2026LogSpace, Lemma 10.5]. -/
@[expose] noncomputable def recip64ResProg {Struct : Type v} (s : ℕ) :
    QueryProg Unit Struct ℤ :=
  (recipOuterProg s).substDigits 4 (recipChild s)

private theorem eval_recipChild_eq {Struct : Type v} (s : ℕ)
    (env : Unit → ℕ → ℤ) (sEnv : Struct → Bool) :
    (fun op r => (recipChild s op r).eval env sEnv) = recipVirtualEnv (env ()) s := by
  ext op r
  fin_cases op
  · simp [recipChild, recipVirtualEnv, QueryProg.eval_bindOverhead, QueryProg.eval,
      eval_intPrefixProg, recipAlpha, recipPrefixRat]
  · simp [recipChild, recipVirtualEnv, QueryProg.eval_bindOverhead, QueryProg.eval,
      eval_intPrefixProg, recipBeta, recipPrefixRat]
  · dsimp [recipChild, recipVirtualEnv, suffixStream]
    split_ifs <;> rfl

theorem eval_recip64ResProg {Struct : Type v} (s : ℕ)
    {env : Unit → ℕ → ℤ} (hx : IsSignedStream (env ()))
    (hx_mem : streamVal (env ()) ∈ Set.Icc (1 / 4 : ℝ) 1) (sEnv : Struct → Bool) :
    (recip64ResProg s).eval env sEnv = recip64Approx (env ()) s % 16 := by
  unfold recip64ResProg recipOuterProg
  rw [QueryProg.eval_substDigits, eval_recipChild_eq, QueryProg.eval_substDigits,
    QueryProg.eval_map, eval_windowPrefixModProg,
    funext fun u => eval_recipHalfVirtualRecipe hx hx_mem s sEnv u,
    recip64Approx_emod_sixteen hx hx_mem s]

/-! ### Active queries, allowance, and intrinsic bit bounds -/

theorem mem_activeQueries_recipOuterProg {Struct : Type v} (s : ℕ)
    (vEnv : Fin 3 → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent (Fin 3) Struct}
    (hev : ev ∈ (recipOuterProg s).activeQueries vEnv sEnv) :
    (∃ (sOp : Struct) (w : ℕ),
        w ≤ 26 + (recipHalfVirtualRecipe (Struct := Struct)).coeffA +
          8 * (recipHalfVirtualRecipe (Struct := Struct)).coeffB +
          (recipHalfVirtualRecipe (Struct := Struct)).coeffB * s ∧
        ev = .struct sOp w) ∨
      ∃ (op : Fin 3) (r w : ℕ),
        r ≤ s + (8 + (recipHalfVirtualRecipe (Struct := Struct)).coeffC) ∧
        (w : ℤ) ≤
          ((26 + (recipHalfVirtualRecipe (Struct := Struct)).coeffA +
              8 * (recipHalfVirtualRecipe (Struct := Struct)).coeffB : ℕ) : ℤ) +
            ((recipHalfVirtualRecipe (Struct := Struct)).coeffB : ℤ) * ((s : ℤ) - (r : ℤ)) ∧
        ev = .digit op r w := by
  set H := recipHalfVirtualRecipe (Struct := Struct)
  rcases QueryProg.mem_activeQueries_substDigits 4 _ _ vEnv sEnv hev with
    ⟨_, _, hs, _⟩ | ⟨_, u, _, evH, hd, hevH, rfl⟩
  · obtain ⟨_, _, hEq⟩ := mem_activeQueries_windowPrefixModProg () 11 (s + 8) _ sEnv
      (QueryProg.activeQueries_map _ _ _ _ ▸ hs)
    nomatch hEq
  · obtain ⟨_, hu, ⟨⟩⟩ := mem_activeQueries_windowPrefixModProg () 11 (s + 8) _ sEnv
      (QueryProg.activeQueries_map _ _ _ _ ▸ hd)
    have hAllH := H.allowance u vEnv sEnv hevH
    have hslack : H.slack = 1 := rfl; rw [hslack] at hAllH
    cases evH with
    | struct sOp l =>
      have : (H.coeffB : ℤ) * u ≤ H.coeffB * ((s : ℤ) + 8) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hu) (Nat.cast_nonneg _)
      have hAllH' : (l : ℤ) ≤ ((H.coeffA * 1 : ℕ) : ℤ) + (H.coeffB : ℤ) * u := hAllH
      push_cast at hAllH'
      exact Or.inl ⟨sOp, 26 + l, by exact_mod_cast (by push_cast; linarith :
        ((26 + l : ℕ) : ℤ) ≤ ((26 + H.coeffA + 8 * H.coeffB + H.coeffB * s : ℕ) : ℤ)), rfl⟩
    | digit op r l =>
      obtain ⟨hr, hl⟩ := hAllH
      have : (H.coeffB : ℤ) * (u - r) ≤ H.coeffB * (s + 8 - r) :=
        mul_le_mul_of_nonneg_left (by omega) (Nat.cast_nonneg _)
      push_cast at hl
      exact Or.inr ⟨op, r, 26 + l, by omega, by push_cast; linarith, rfl⟩

private theorem recipOuter_w_le {A₀ B₀ s r w : ℕ}
    (hw : (w : ℤ) ≤ (A₀ : ℤ) + (B₀ : ℤ) * ((s : ℤ) - (r : ℤ))) :
    w ≤ A₀ + B₀ * s := by
  have hmul : (B₀ : ℤ) * ((s : ℤ) - (r : ℤ)) ≤ (B₀ : ℤ) * (s : ℤ) :=
    mul_le_mul_of_nonneg_left (by omega) (Nat.cast_nonneg _)
  exact_mod_cast (by push_cast at hw ⊢; linarith : (w : ℤ) ≤ ((A₀ + B₀ * s : ℕ) : ℤ))

private theorem mem_activeQueries_recipOuterProg_digit {Struct : Type v} (s : ℕ)
    (vEnv : Fin 3 → ℕ → ℤ) (sEnv : Struct → Bool) {op : Fin 3} {r w : ℕ}
    (h : QueryEvent.digit op r w ∈ (recipOuterProg s).activeQueries vEnv sEnv) :
    let H := recipHalfVirtualRecipe (Struct := Struct)
    r ≤ s + (8 + H.coeffC) ∧
      (w : ℤ) ≤ ((26 + H.coeffA + 8 * H.coeffB : ℕ) : ℤ) +
        (H.coeffB : ℤ) * ((s : ℤ) - (r : ℤ)) := by
  rcases mem_activeQueries_recipOuterProg s vEnv sEnv h with
    ⟨_, _, _, hEq⟩ | ⟨_, _, _, hr, hw, hEq⟩
  · nomatch hEq
  · cases hEq; exact ⟨hr, hw⟩

private theorem allowance_recipEarly {Struct : Type v} {d s wOut : ℕ} (hd : 1 ≤ d)
    (env : Unit → ℕ → ℤ) (sEnv : Struct → Bool)
    {k : ℤ → QueryProg Unit Struct ℤ} (hk : ∀ P, (k P).activeQueries env sEnv = [])
    {evC : QueryEvent Unit Struct}
    (hf : evC ∈ ((intPrefixProg () (recipCutoff s)).bindOverhead 0 k).activeQueries env sEnv)
    (hwOut : wOut ≤ (26 + (recipHalfVirtualRecipe (Struct := Struct)).coeffA +
      8 * (recipHalfVirtualRecipe (Struct := Struct)).coeffB) +
      (recipHalfVirtualRecipe (Struct := Struct)).coeffB * s) :
    let H := recipHalfVirtualRecipe (Struct := Struct)
    let A₀ := 26 + H.coeffA + 8 * H.coeffB
    let B₀ := H.coeffB
    let C₀ := 8 + H.coeffC
    AllowanceBound d (max (A₀ + 26 + 15 * (B₀ + 1)) ((A₀ + 4) + (B₀ + 2) * C₀))
      (2 * B₀ + 2) C₀ s (evC.addBits (wOut + 4)) := by
  intro H A₀ B₀ C₀
  simp only [QueryProg.activeQueries_bindOverhead, hk, List.append_nil, List.mem_map] at hf
  obtain ⟨evI, hevI, rfl⟩ := hf
  obtain ⟨j, hj, rfl⟩ := mem_activeQueries_intPrefixProg () (recipCutoff s) env sEnv hevI
  have hC₀ : 7 ≤ C₀ * d := (by dsimp [C₀]; omega : 7 ≤ C₀).trans (Nat.le_mul_of_pos_right _ hd)
  have hmul_pay := mul_le_mul_of_nonneg_left (clock_succ_le_early_payment hj)
    (Nat.cast_nonneg (α := ℤ) (B₀ + 1))
  have ha_le : A₀ + 26 + 15 * (B₀ + 1) ≤
      max (A₀ + 26 + 15 * (B₀ + 1)) ((A₀ + 4) + (B₀ + 2) * C₀) * d :=
    (le_max_left _ _).trans (Nat.le_mul_of_pos_right _ hd)
  have hrc : recipCutoff s = s / 2 + 7 := rfl
  refine ⟨by rw [hrc] at hj; omega, ?_⟩
  have hjZ : ((recipCutoff s + j + 8 : ℕ) : ℤ) ≤ ((s + 22 : ℕ) : ℤ) :=
    Int.ofNat_le.mpr (by rw [hrc] at hj ⊢; omega)
  have hwZ : (wOut : ℤ) ≤ (A₀ : ℤ) + (B₀ : ℤ) * (s : ℤ) := by exact_mod_cast hwOut
  have haZ := Int.ofNat_le.mpr ha_le
  push_cast at hmul_pay haZ hjZ ⊢
  linarith

private theorem allowance_recip64ResProg {Struct : Type v} {d : ℕ} (hd : 1 ≤ d) (s : ℕ)
    (env : Unit → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent Unit Struct}
    (hev : ev ∈ (recip64ResProg s).activeQueries env sEnv) :
    let H := recipHalfVirtualRecipe (Struct := Struct)
    let A₀ := 26 + H.coeffA + 8 * H.coeffB
    let B₀ := H.coeffB
    let C₀ := 8 + H.coeffC
    let aRecip := max (A₀ + 26 + 15 * (B₀ + 1)) ((A₀ + 4) + (B₀ + 2) * C₀)
    let bRecip := 2 * B₀ + 2
    AllowanceBound d aRecip bRecip C₀ s ev := by
  intro H A₀ B₀ C₀ aRecip bRecip
  rcases QueryProg.mem_activeQueries_substDigits 4 _ _ env sEnv hev with
    ⟨sOp, w, hs, rfl⟩ | ⟨op, r, wOut, evC, hdOut, hevC, rfl⟩
  · rcases mem_activeQueries_recipOuterProg s _ sEnv hs with
      ⟨_, _, hw, ⟨⟩⟩ | ⟨_, _, _, _, _, hEq⟩
    · change (w : ℤ) ≤ ((aRecip * d : ℕ) : ℤ) + (bRecip : ℤ) * (s : ℤ)
      have had : A₀ ≤ aRecip * d :=
        (by dsimp [aRecip]; omega : A₀ ≤ aRecip).trans (Nat.le_mul_of_pos_right _ hd)
      have hB_le : B₀ * s ≤ bRecip * s := Nat.mul_le_mul_right s (by dsimp [bRecip]; omega)
      dsimp only [A₀, B₀, H] at had hw hB_le
      exact_mod_cast (by omega : w ≤ aRecip * d + bRecip * s)
    · nomatch hEq
  · obtain ⟨hr, hwOut⟩ := mem_activeQueries_recipOuterProg_digit s _ sEnv hdOut
    unfold recipChild at hevC
    split_ifs at hevC
    any_goals exact allowance_recipEarly hd env sEnv (fun _ => rfl) hevC (recipOuter_w_le hwOut)
    · nomatch hevC
    · rcases List.mem_cons.mp hevC with rfl | hevC
      · have hBase : AllowanceBound (Struct := Struct) d (A₀ + 4) B₀ C₀ s
            (.digit () r (wOut + 4 + 0)) := by
          refine ⟨hr.trans (Nat.add_le_add_left (Nat.le_mul_of_pos_right C₀ hd) s), ?_⟩
          have hA4 : ((A₀ + 4 : ℕ) : ℤ) ≤ (((A₀ + 4) * d : ℕ) : ℤ) := by
            exact_mod_cast Nat.le_mul_of_pos_right (A₀ + 4) hd
          dsimp only [A₀, B₀, H] at hwOut hA4 ⊢; push_cast at hwOut hA4 ⊢; linarith
        refine (hBase.mono_coeff (b := bRecip) (by dsimp [bRecip]; omega)).mono_ac
          (a := aRecip) (c := C₀) ?_ le_rfl
        simpa only [show bRecip - B₀ = B₀ + 2 by dsimp [bRecip]; omega] using le_max_right _ _
      · nomatch hevC

private theorem maxIntrinsicBits_recipOuterProg_le {Struct : Type v} {d : ℕ} (hd : 1 ≤ d)
    (s : ℕ) (vEnv : Fin 3 → ℕ → ℤ) (sEnv : Struct → Bool) :
    (recipOuterProg s).maxIntrinsicBits vEnv sEnv ≤
      (34 + 9 * (recipHalfVirtualRecipe (Struct := Struct)).intrinsicCoeff) * (d + s) := by
  set H := recipHalfVirtualRecipe (Struct := Struct)
  apply QueryProg.maxIntrinsicBits_substDigits_le 4 _ _ vEnv sEnv
  · rw [QueryProg.maxIntrinsicBits_map]
    have hwin := maxIntrinsicBits_windowPrefixModProg_le () 11 (s + 8)
      (fun _ u => (recipHalfVirtualRecipe.digitProg u).eval vEnv sEnv) sEnv
    nlinarith
  · intro _ u _ hdOut
    obtain ⟨_, hu, ⟨⟩⟩ := mem_activeQueries_windowPrefixModProg () 11 (s + 8) _ sEnv
      (QueryProg.activeQueries_map _ _ _ _ ▸ hdOut)
    have hIntH : (H.digitProg u).maxIntrinsicBits vEnv sEnv ≤ H.intrinsicCoeff * (1 + u) :=
      H.intrinsic_bound u vEnv sEnv
    nlinarith

private theorem maxIntrinsicBits_recip64ResProg_le {Struct : Type v} {d : ℕ} (hd : 1 ≤ d)
    (s : ℕ) (env : Unit → ℕ → ℤ) (sEnv : Struct → Bool) :
    let H := recipHalfVirtualRecipe (Struct := Struct)
    let A₀ := 26 + H.coeffA + 8 * H.coeffB
    let B₀ := H.coeffB
    let C₀ := 8 + H.coeffC
    let K₂ := A₀ + B₀ + 8 * C₀ + 108
    let cInt := max (34 + 9 * H.intrinsicCoeff) K₂
    (recip64ResProg s).maxIntrinsicBits env sEnv ≤ cInt * (d + s) := by
  intro H A₀ B₀ C₀ K₂ cInt
  apply QueryProg.maxIntrinsicBits_substDigits_le 4 _ _ env sEnv
  · exact (maxIntrinsicBits_recipOuterProg_le hd s _ sEnv).trans
      (Nat.mul_le_mul_right _ (le_max_left _ _))
  · intro op r wOut hdOut
    obtain ⟨hr, hwOut⟩ := mem_activeQueries_recipOuterProg_digit s _ sEnv hdOut
    have hrC : r ≤ s + C₀ := hr
    have hwOut_nat : wOut ≤ A₀ + B₀ * s := recipOuter_w_le hwOut
    have hrc_eq : recipCutoff s = s / 2 + 7 := rfl
    have hch_int : (recipChild s op r).maxIntrinsicBits env sEnv ≤
        8 * (s + (s + C₀) + 8) + (s + 23) := by
      unfold recipChild
      split_ifs <;> first
        | (simp [QueryProg.maxIntrinsicBits]; done)
        | exact maxIntrinsicBits_bindOverhead_trans
            (by have hp := maxIntrinsicBits_intPrefixProg_le () (recipCutoff s) env sEnv; omega)
            (by simp only [QueryProg.maxIntrinsicBits, Nat.max_zero]; omega)
    have hKd := (show A₀ + 8 * C₀ + 91 ≤ K₂ by dsimp [K₂]; omega).trans
      (Nat.le_mul_of_pos_right K₂ hd)
    have hKs := Nat.mul_le_mul_right s (show B₀ + 17 ≤ K₂ by dsimp [K₂]; omega)
    rw [Nat.add_mul] at hKs
    exact (show wOut + 4 + (recipChild s op r).maxIntrinsicBits env sEnv ≤ K₂ * (d + s) by
      dsimp only [A₀, B₀, H] at hwOut_nat hKd hKs
      rw [Nat.mul_add]; omega).trans (Nat.mul_le_mul_right _ (le_max_right _ _))

/-! ### Certified reciprocal recipe -/

/-- **Lemma 10.5 (certified early-word reciprocal primitive on `[1 / 4, 1]`)**
[OpenAI2026LogSpace, Lemma 10.5]. Here `[1 / 4, 1]` is the input domain
`streamVal (env ()) ∈ [1 / 4, 1]`, while the `1 / 64` factor normalizes the Taylor components and
output `1 / (64 * x)` into `[-1, 1]` before downstream `shiftClip` restores the target scale. -/
@[expose] noncomputable def recip64Prim {Struct : Type v} (d : ℕ) (hd : 1 ≤ d) :
    UniformStreamRecipe Unit Struct :=
  let H := recipHalfVirtualRecipe (Struct := Struct)
  let A₀ := 26 + H.coeffA + 8 * H.coeffB
  let B₀ := H.coeffB
  let C₀ := 8 + H.coeffC
  let aRecip := max (A₀ + 26 + 15 * (B₀ + 1)) ((A₀ + 4) + (B₀ + 2) * C₀)
  let bRecip := 2 * B₀ + 2
  let K₂ := A₀ + B₀ + 8 * C₀ + 108
  let cInt := max (34 + 9 * H.intrinsicCoeff) K₂
  recipeOfMod16Prog d hd
    (fun env _ => IsNormSignedStream (env ()) ∧ streamVal (env ()) ∈ Set.Icc (1 / 4 : ℝ) 1)
    (fun val _ => 1 / (64 * val ()))
    (fun env _ => recip64Approx (env ()))
    recip64ResProg aRecip bRecip C₀ cInt
    (fun {env _} ⟨_, hlo, _⟩ => by
      have hge16 : (16 : ℝ) ≤ 64 * streamVal (env ()) := by linarith
      have hpos : (0 : ℝ) < 64 * streamVal (env ()) := by linarith
      rw [abs_of_pos (div_pos one_pos hpos)]
      exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 16) hge16).trans (by norm_num))
    (fun ⟨⟨hs, _⟩, hmem⟩ => recip64Approx_isScaledApprox hs hmem)
    (fun ⟨⟨hs, _⟩, hmem⟩ s => eval_recip64ResProg s hs hmem _)
    (fun s env sEnv _ hev => by exact allowance_recip64ResProg hd s env sEnv hev)
    (fun s env sEnv => by exact maxIntrinsicBits_recip64ResProg_le hd s env sEnv)

/-- Compose a `UniformStreamRecipe` whose target value lies in `[1 / 4, 1]` with `recip64Prim` to
obtain `1 / (64 * R)`. -/
@[expose] noncomputable def UniformStreamRecipe.recip64 {Op : Type u} {Struct : Type v}
    (R : UniformStreamRecipe Op Struct) : UniformStreamRecipe Op Struct :=
  let raw := (recip64Prim R.slack R.slack_pos).comp (fun _ => R)
    R.coeffA R.coeffB R.coeffC R.intrinsicCoeff
    (fun _ => rfl) (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl)
  raw.weakenValid
    (fun env sEnv =>
      R.ValidEnv env sEnv ∧
        R.targetVal (fun op => streamVal (env op)) sEnv ∈ Set.Icc (1 / 4 : ℝ) 1)
    (fun ⟨hR, hMem⟩ => ⟨fun _ => hR, R.emits_norm hR, by rwa [R.emits_exact hR]⟩)

end ReciprocalRecipe

/-! ## Zero-padded detector rank -/

section RankRecipe

/-! ### Counting and fold query programs -/

/-- Count how many elements `w` in `ws` satisfy `0 ≤ cmpPrefixProg w i K` using `O(idxBits)`
retained bits. -/
@[expose] def countAtLeastProg {Op : Type u} {Struct : Type v} (i : Op) (K idxBits : ℕ) :
    List Op → ℕ → QueryProg Op Struct ℕ
  | [], cnt => .scratchStep (2 * idxBits + 4) (.ret cnt)
  | w :: ws, cnt =>
      (cmpPrefixProg w i K).bindOverhead (2 * idxBits + 4) fun c =>
        countAtLeastProg i K idxBits ws (if 0 ≤ c then cnt + 1 else cnt)

/-- Streaming outer scan over candidate elements `rem` for the zero-padded detector rank, tracking
the index `best : Option Op` with largest positive `intPrefix` among elements exceeded or matched
by at least `k` members of `items`. -/
@[expose] def zeroPaddedRankFoldProg {Op : Type u} {Struct : Type v} (k : ℕ) (items : List Op)
    (K idxBits : ℕ) : List Op → Option Op → QueryProg Op Struct (Option Op)
  | [], best => .scratchStep (2 * idxBits + 4) (.ret best)
  | i :: rest, best =>
      (countAtLeastProg i K idxBits items 0).bindOverhead (2 * idxBits + 4) fun cnt =>
        if k ≤ cnt then
          (cmpWithConstProg i (fun _ => 0) K).bindOverhead (2 * idxBits + 4) fun cPos =>
            if 0 < cPos then
              match best with
              | none => zeroPaddedRankFoldProg k items K idxBits rest (some i)
              | some b =>
                  (cmpPrefixProg i b K).bindOverhead (2 * idxBits + 4) fun cBest =>
                    zeroPaddedRankFoldProg k items K idxBits rest
                      (if 0 < cBest then some i else some b)
            else
              zeroPaddedRankFoldProg k items K idxBits rest best
        else
          zeroPaddedRankFoldProg k items K idxBits rest best

/-- Mod-16 residue program for `zeroPaddedRankApprox k items.toFinset env s` (clamping negative
order statistics up to `0` as in `Finset.kthLargest`), sizing its index/count registers natively
from `Nat.log 2 items.length + 2` (adapting [OpenAI2026LogSpace, Lemma 10.6] to Sections 4.2 and
8.2). -/
@[expose] def zeroPaddedRankListResProg {Op : Type u} {Struct : Type v}
    (k : ℕ) (items : List Op) (s : ℕ) : QueryProg Op Struct ℤ :=
  let idxBits := Nat.log 2 items.length + 2
  (zeroPaddedRankFoldProg k items (s + 4) idxBits items none).bindOverhead (idxBits + 4) fun best =>
    match best with
    | none => .scratchStep 8 (.ret 0)
    | some b => (windowPrefixModProg b 8 (s + 4)).map (· / 16)

/-! ### Evaluation correctness -/

private theorem eval_countAtLeastProg {Op : Type u} {Struct : Type v}
    (i : Op) (K idxBits : ℕ) (ws : List Op) (cnt : ℕ)
    {env : Op → ℕ → ℤ} (hi : IsSignedStream (env i))
    (hws : ∀ w ∈ ws, IsSignedStream (env w)) (sEnv : Struct → Bool) :
    (countAtLeastProg i K idxBits ws cnt).eval env sEnv =
      cnt + (ws.filter fun w => decide (intPrefix (env i) K ≤ intPrefix (env w) K)).length := by
  induction ws generalizing cnt with
  | nil => simp [countAtLeastProg, QueryProg.eval]
  | cons w ws ih =>
    have hw : IsSignedStream (env w) := hws w List.mem_cons_self
    simp only [countAtLeastProg, QueryProg.eval_bindOverhead, eval_cmpPrefixProg,
      ih _ fun w' hm => hws w' (List.mem_cons_of_mem w hm), List.filter_cons]
    by_cases hle : intPrefix (env i) K ≤ intPrefix (env w) K
    · simp only [(cmpPrefix_nonneg_iff hw hi K).mpr hle, ↓reduceIte, decide_eq_true hle,
        List.length_cons]; omega
    · simp only [(cmpPrefix_nonneg_iff hw hi K).not.mpr hle, ↓reduceIte, decide_eq_false hle,
        Bool.false_eq_true]

private def optIntPrefix {Op : Type u} (env : Op → ℕ → ℤ) (K : ℕ) : Option Op → ℤ
  | none => 0
  | some b => intPrefix (env b) K

private def foldQualMax {Op : Type u} (P : Op → Prop) [DecidablePred P] (h : Op → ℤ) :
    List Op → ℤ → ℤ
  | [], acc => acc
  | i :: rest, acc => foldQualMax P h rest (if P i then max acc (h i) else acc)

private theorem acc_le_foldQualMax {Op : Type u} (P : Op → Prop) [DecidablePred P] (h : Op → ℤ)
    (rem : List Op) (acc : ℤ) :
    acc ≤ foldQualMax P h rem acc := by
  induction rem generalizing acc with
  | nil => exact le_rfl
  | cons i rest ih =>
    simp only [foldQualMax]; split_ifs
    exacts [(le_max_left _ _).trans (ih _), ih _]

private theorem mem_le_foldQualMax {Op : Type u} (P : Op → Prop) [DecidablePred P] (h : Op → ℤ)
    (rem : List Op) (acc : ℤ) {x : Op} (hx : x ∈ rem) (hPx : P x) :
    h x ≤ foldQualMax P h rem acc := by
  induction rem generalizing acc with
  | nil => nomatch hx
  | cons i rest ih =>
    simp only [foldQualMax]
    rcases List.mem_cons.mp hx with rfl | hx_rest
    · simp only [hPx, ↓reduceIte]
      exact (le_max_right acc (h x)).trans (acc_le_foldQualMax P h rest _)
    · exact ih _ hx_rest

private theorem foldQualMax_le {Op : Type u} (P : Op → Prop) [DecidablePred P] (h : Op → ℤ)
    (rem : List Op) (acc U : ℤ) (hacc : acc ≤ U) (hrem : ∀ x ∈ rem, P x → h x ≤ U) :
    foldQualMax P h rem acc ≤ U := by
  induction rem generalizing acc with
  | nil => exact hacc
  | cons i rest ih =>
    simp only [foldQualMax]
    refine ih _ ?_ fun x hx => hrem x (List.mem_cons_of_mem i hx)
    split_ifs with hPi
    · exact max_le hacc (hrem i List.mem_cons_self hPi)
    · exact hacc

private theorem eval_zeroPaddedRankFoldProg_optIntPrefix {Op : Type u} [DecidableEq Op]
    {Struct : Type v}
    (k : ℕ) (items : List Op) (hNodup : items.Nodup) (K idxBits : ℕ)
    (rem : List Op) (hSub : ∀ x ∈ rem, x ∈ items)
    {env : Op → ℕ → ℤ} (hEnv : ∀ x ∈ items, IsSignedStream (env x)) (sEnv : Struct → Bool)
    (best : Option Op)
    (hBestMem : ∀ b, best = some b → b ∈ items)
    (hBestNonneg : 0 ≤ optIntPrefix env K best) :
    let h : Op → ℤ := fun x => intPrefix (env x) K
    let P : Op → Prop := fun x => k ≤ #{w ∈ items.toFinset | h x ≤ h w}
    (∀ b, (zeroPaddedRankFoldProg k items K idxBits rem best).eval env sEnv = some b →
        b ∈ items) ∧
      optIntPrefix env K ((zeroPaddedRankFoldProg k items K idxBits rem best).eval env sEnv) =
        foldQualMax P h rem (optIntPrefix env K best) := by
  intro h P
  have cmpPos : ∀ {x y : ℕ → ℤ}, IsSignedStream x → IsSignedStream y →
      (0 < cmpPrefix x y K ↔ intPrefix y K < intPrefix x K) := fun hx hy => by
    rw [← not_le, cmpPrefix_nonpos_iff hx hy K, not_le]
  induction rem generalizing best with
  | nil => exact ⟨hBestMem, rfl⟩
  | cons i rest ih =>
    have hi_mem : i ∈ items := hSub i List.mem_cons_self
    have hrest_sub : ∀ x ∈ rest, x ∈ items := fun x hx => hSub x (List.mem_cons_of_mem i hx)
    have hcnt : (countAtLeastProg i K idxBits items 0).eval env sEnv =
        #{w ∈ items.toFinset | h i ≤ h w} := by
      rw [eval_countAtLeastProg i K idxBits items 0 (hEnv i hi_mem) hEnv sEnv, Nat.zero_add,
        ← List.toFinset_card_of_nodup (hNodup.filter _)]
      congr 1; ext w; simp [h, List.mem_toFinset, mem_filter]
    let step (next : Option Op) (hmem : ∀ b, next = some b → b ∈ items)
        (hval : optIntPrefix env K next = max (optIntPrefix env K best) (h i)) :=
      hval ▸ ih (hSub := hrest_sub) next hmem (hval ▸ hBestNonneg.trans (le_max_left _ _))
    simp only [zeroPaddedRankFoldProg, QueryProg.eval_bindOverhead, hcnt, foldQualMax, P]
    split_ifs with hPi
    · have h0 : intPrefix (fun _ => 0) K = 0 := sum_eq_zero fun _ _ => zero_mul _
      have hiMem : ∀ b, some i = some b → b ∈ items := fun _ hb => Option.some.inj hb ▸ hi_mem
      simp only [QueryProg.eval_bindOverhead, eval_cmpWithConstProg,
        cmpPos (hEnv i hi_mem) isSignedStream_zero, h0]
      split_ifs with hpos
      · cases best with
        | none => exact step (some i) hiMem (max_eq_right hpos.le).symm
        | some b =>
          simp only [QueryProg.eval_bindOverhead, eval_cmpPrefixProg,
            cmpPos (hEnv i hi_mem) (hEnv b (hBestMem b rfl))]
          split_ifs with hlt
          exacts [step (some i) hiMem (max_eq_right hlt.le).symm,
            step (some b) hBestMem (max_eq_left (not_lt.mp hlt)).symm]
      · exact step best hBestMem (max_eq_left ((not_lt.mp hpos).trans hBestNonneg)).symm
    · exact ih (hSub := hrest_sub) best hBestMem hBestNonneg

theorem eval_zeroPaddedRankListResProg {Op : Type u} [DecidableEq Op] {Struct : Type v}
    (k : ℕ) (items : List Op) (hNodup : items.Nodup) (s : ℕ)
    {env : Op → ℕ → ℤ} (hEnv : ∀ x ∈ items, IsSignedStream (env x)) (sEnv : Struct → Bool) :
    (zeroPaddedRankListResProg k items s).eval env sEnv =
      zeroPaddedRankApprox k items.toFinset env s % 16 := by
  set h : Op → ℤ := fun x => intPrefix (env x) (s + 4)
  set P : Op → Prop := fun x => k ≤ #{w ∈ items.toFinset | h x ≤ h w}
  obtain ⟨_, hFoldVal⟩ := eval_zeroPaddedRankFoldProg_optIntPrefix k items hNodup (s + 4)
    (Nat.log 2 items.length + 2) items (fun _ hx => hx) hEnv sEnv none
    (fun _ hb => nomatch hb) le_rfl
  have hkth : foldQualMax P h items 0 = kthLargest k items.toFinset h := le_antisymm
    (foldQualMax_le P h items 0 _ (le_max' _ _ (mem_insert_self _ _)) fun x hx hPx =>
      le_max' _ _ (mem_insert_of_mem
        (mem_image_of_mem h (mem_filter.mpr ⟨List.mem_toFinset.mpr hx, hPx⟩))))
    (max'_le _ _ _ fun r hr => by
      rcases mem_insert.mp hr with rfl | hr
      · exact acc_le_foldQualMax P h items 0
      · obtain ⟨x, hx, rfl⟩ := mem_image.mp hr
        exact mem_le_foldQualMax P h items 0 (List.mem_toFinset.mp (mem_filter.mp hx).1)
          (mem_filter.mp hx).2)
  dsimp only [optIntPrefix] at hFoldVal
  rw [zeroPaddedRankListResProg, QueryProg.eval_bindOverhead, zeroPaddedRankApprox, ← hkth,
    ← hFoldVal]
  cases (zeroPaddedRankFoldProg k items (s + 4) _ items none).eval env sEnv with
  | none => rfl
  | some b =>
    simp only [QueryProg.eval_map, eval_windowPrefixModProg, emod_two_pow_eight_div_sixteen]

/-! ### Active queries, allowance, and intrinsic bit bounds -/

private theorem mem_activeQueries_countAtLeastProg {Op : Type u} {Struct : Type v}
    (i : Op) (K idxBits : ℕ) (ws : List Op) (cnt : ℕ)
    (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent Op Struct}
    (hev : ev ∈ (countAtLeastProg i K idxBits ws cnt).activeQueries env sEnv) :
    ∃ op j L, j ≤ K ∧ L ≤ 2 * idxBits + 14 + 6 * (K - j) ∧ ev = .digit op j L := by
  induction ws generalizing cnt with
  | nil => nomatch hev
  | cons w ws ih =>
    rcases mem_bindOverhead_activeQueries hev with ⟨_, h₀, rfl⟩ | h₁
    · exact let ⟨op, j, L, hj, hL, e⟩ := mem_activeQueries_cmpPrefixProg w i K env sEnv h₀
        ⟨op, j, 2 * idxBits + 4 + L, hj, by omega, by rw [e]; rfl⟩
    · exact ih _ h₁

private theorem maxIntrinsicBits_countAtLeastProg_le {Op : Type u} {Struct : Type v}
    (i : Op) (K idxBits : ℕ) (ws : List Op) (cnt : ℕ)
    (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) :
    (countAtLeastProg i K idxBits ws cnt).maxIntrinsicBits env sEnv ≤
      2 * idxBits + 6 * K + 14 := by
  induction ws generalizing cnt with
  | nil => simp only [countAtLeastProg, QueryProg.maxIntrinsicBits, Nat.max_zero]; omega
  | cons w ws ih =>
    have hc := maxIntrinsicBits_cmpPrefixProg_le w i K env sEnv
    exact maxIntrinsicBits_bindOverhead_trans (by omega) (ih _)

theorem mem_activeQueries_zeroPaddedRankFoldProg {Op : Type u} {Struct : Type v}
    (k : ℕ) (items : List Op) (K idxBits : ℕ) (rem : List Op) (best : Option Op)
    (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent Op Struct}
    (hev : ev ∈ (zeroPaddedRankFoldProg k items K idxBits rem best).activeQueries env sEnv) :
    ∃ op j L, j ≤ K ∧ L ≤ 4 * idxBits + 18 + 6 * (K - j) ∧ ev = .digit op j L := by
  induction rem generalizing best with
  | nil => nomatch hev
  | cons i rest ih =>
    rcases mem_bindOverhead_activeQueries hev with ⟨_, h₀, rfl⟩ | h₁
    · obtain ⟨op, j, L, hj, hL, rfl⟩ :=
        mem_activeQueries_countAtLeastProg i K idxBits items 0 env sEnv h₀
      exact ⟨op, j, (2 * idxBits + 4) + L, hj, by omega, rfl⟩
    split_ifs at h₁; swap; · exact ih _ h₁
    rcases mem_bindOverhead_activeQueries h₁ with ⟨_, h₀, rfl⟩ | h₂
    · obtain ⟨j, L, hj, hL, rfl⟩ := mem_activeQueries_cmpWithConstProg i (fun _ => 0) K env sEnv h₀
      exact ⟨i, j, (2 * idxBits + 4) + L, hj, by omega, rfl⟩
    split_ifs at h₂; swap; · exact ih _ h₂
    cases best with
    | none => exact ih _ h₂
    | some b =>
      rcases mem_bindOverhead_activeQueries h₂ with ⟨_, h₀, rfl⟩ | h₃
      · obtain ⟨op, j, L, hj, hL, rfl⟩ := mem_activeQueries_cmpPrefixProg i b K env sEnv h₀
        exact ⟨op, j, (2 * idxBits + 4) + L, hj, by omega, rfl⟩
      · exact ih _ h₃

theorem maxIntrinsicBits_zeroPaddedRankFoldProg_le {Op : Type u} {Struct : Type v}
    (k : ℕ) (items : List Op) (K idxBits : ℕ) (rem : List Op) (best : Option Op)
    (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) :
    (zeroPaddedRankFoldProg k items K idxBits rem best).maxIntrinsicBits env sEnv ≤
      4 * idxBits + 6 * K + 18 := by
  induction rem generalizing best with
  | nil => simp only [zeroPaddedRankFoldProg, QueryProg.maxIntrinsicBits, Nat.max_zero]; omega
  | cons i rest ih =>
    have hcnt := maxIntrinsicBits_countAtLeastProg_le i K idxBits items 0 env sEnv
    refine maxIntrinsicBits_bindOverhead_trans (by omega) ?_
    split_ifs; swap; · exact ih _
    have hconst := maxIntrinsicBits_cmpWithConstProg_le i (fun _ => 0) K env sEnv
    refine maxIntrinsicBits_bindOverhead_trans (by omega) ?_
    split_ifs; swap; · exact ih _
    cases best with
    | none => exact ih _
    | some b =>
      have hcmp := maxIntrinsicBits_cmpPrefixProg_le i b K env sEnv
      exact maxIntrinsicBits_bindOverhead_trans (by omega) (ih _)

private theorem zeroPaddedRank_slack_le {d len κ : ℕ} (hd : 1 ≤ d) (hLen : len ≤ 2 ^ (κ * d)) :
    5 * (Nat.log 2 len + 2) + 46 ≤ (5 * κ + 56) * d := by
  have hlog : Nat.log 2 len ≤ κ * d :=
    (Nat.log_mono_right hLen).trans_eq (Nat.log_pow (by decide) _)
  have h56 : 56 ≤ 56 * d := Nat.le_mul_of_pos_right 56 hd
  rw [Nat.add_mul, Nat.mul_assoc]; omega

private theorem allowance_zeroPaddedRankListResProg {Op : Type u} {Struct : Type v}
    {d : ℕ} (hd : 1 ≤ d) (k : ℕ) (items : List Op) (κ : ℕ)
    (hLen : items.length ≤ 2 ^ (κ * d)) (s : ℕ)
    (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent Op Struct}
    (hev : ev ∈ (zeroPaddedRankListResProg k items s).activeQueries env sEnv) :
    AllowanceBound d (5 * κ + 56) 6 4 s ev := by
  set idxBits := Nat.log 2 items.length + 2
  have hSlack := zeroPaddedRank_slack_le hd hLen
  have h4 := Nat.le_mul_of_pos_right 4 hd
  rcases mem_bindOverhead_activeQueries hev with ⟨_, h₀, rfl⟩ | hev₁
  · obtain ⟨op, j, L, hj, hL, rfl⟩ :=
      mem_activeQueries_zeroPaddedRankFoldProg k items (s + 4) idxBits items none env sEnv h₀
    exact allowanceBound_digit_slope6 (5 * idxBits + 22) op hj le_rfl h4 (by omega) hSlack
  · cases hbest : (zeroPaddedRankFoldProg k items (s + 4) idxBits items none).eval env sEnv with
    | none => rw [hbest] at hev₁; nomatch hev₁
    | some b =>
      rw [hbest, QueryProg.activeQueries_map] at hev₁
      obtain ⟨j, hj, rfl⟩ := mem_activeQueries_windowPrefixModProg b 8 (s + 4) env sEnv hev₁
      exact allowanceBound_digit_slope6 16 b hj le_rfl h4 (by omega) (by omega)

private theorem maxIntrinsicBits_zeroPaddedRankListResProg_le {Op : Type u} {Struct : Type v}
    {d : ℕ} (hd : 1 ≤ d) (k : ℕ) (items : List Op) (κ : ℕ)
    (hLen : items.length ≤ 2 ^ (κ * d)) (s : ℕ)
    (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) :
    (zeroPaddedRankListResProg k items s).maxIntrinsicBits env sEnv ≤ (5 * κ + 56) * (d + s) := by
  simp only [zeroPaddedRankListResProg]
  set idxBits := Nat.log 2 items.length + 2
  have hSlack := zeroPaddedRank_slack_le hd hLen
  have hs6 : 6 * s ≤ (5 * κ + 56) * s := Nat.mul_le_mul_right s (by omega)
  have hf := maxIntrinsicBits_zeroPaddedRankFoldProg_le k items (s + 4) idxBits items none env sEnv
  rw [Nat.mul_add]
  refine maxIntrinsicBits_bindOverhead_trans (by omega) ?_
  cases (zeroPaddedRankFoldProg k items (s + 4) idxBits items none).eval env sEnv with
  | none => simp only [QueryProg.maxIntrinsicBits, Nat.max_zero]; omega
  | some b =>
    have hw := maxIntrinsicBits_windowPrefixModProg_le b 8 (s + 4) env sEnv
    rw [QueryProg.maxIntrinsicBits_map]; omega

/-! ### Certified rank recipes -/

/-- **Certified zero-padded detector-rank recipe over a duplicate-free list** (adapting
[OpenAI2026LogSpace, Lemma 10.6] to the zero-padded `Finset.kthLargest` of Sections 4.2 and 8.2):
computes `Finset.kthLargest k items.toFinset` (clamping negative order statistics up to `0`) over
at most `2 ^ (κ * d)` candidate streams with top-down comparator slope `coeffB = 6`, clock
overshoot `4`, and `O((κ + 1) * d)` slack/index overhead. -/
@[expose] noncomputable def zeroPaddedRankListRecipe {Op : Type u} [DecidableEq Op]
    {Struct : Type v} (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (items : List Op) (hNodup : items.Nodup)
    (κ : ℕ) (hLen : items.length ≤ 2 ^ (κ * d)) :
    UniformStreamRecipe Op Struct :=
  recipeOfMod16Prog d hd
    (fun env _ => ∀ x ∈ items.toFinset, IsNormSignedStream (env x))
    (fun val _ => kthLargest k items.toFinset val)
    (fun env _ => zeroPaddedRankApprox k items.toFinset env)
    (zeroPaddedRankListResProg k items) (5 * κ + 56) 6 4 (5 * κ + 56)
    (fun hV => by
      rw [abs_le]
      refine ⟨(by norm_num : (-1 : ℝ) ≤ 0).trans kthLargest_nonneg, ?_⟩
      exact kthLargest_le zero_le_one fun x hx => (abs_le.mp (hV x hx).2).2)
    (fun hV => zeroPaddedRankApprox_isScaledApprox k items.toFinset fun x hx => (hV x hx).1)
    (fun hV s => eval_zeroPaddedRankListResProg k items hNodup s
      (fun x hx => (hV x (List.mem_toFinset.mpr hx)).1) _)
    (fun s env sEnv _ hev => by
      exact allowance_zeroPaddedRankListResProg hd k items κ hLen s env sEnv hev)
    (fun s env sEnv => by
      exact maxIntrinsicBits_zeroPaddedRankListResProg_le hd k items κ hLen s env sEnv)

/-- **`Finset` specification wrapper for `zeroPaddedRankListRecipe`** (adapting
[OpenAI2026LogSpace, Lemma 10.6] to the zero-padded `Finset.kthLargest` of Sections 4.2 and 8.2,
clamping negative order statistics up to `0`). Note that `Finset.toList` uses `Classical.choose` to
pick an arbitrary list ordering, so this wrapper is intended only for analytical `Finset`
specifications; machine-realizable log-space stages must pass a canonical duplicate-free list
directly to `zeroPaddedRankListRecipe` (as in `rowCompressionNewDefaultRecipe` and
`rowCompressionUpdateRecipe`). -/
@[expose] noncomputable def zeroPaddedRankFinsetRecipe {Op : Type u} [DecidableEq Op]
    {Struct : Type v} (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (s : Finset Op) (κ : ℕ)
    (hCard : s.card ≤ 2 ^ (κ * d)) :
    UniformStreamRecipe Op Struct :=
  let raw := zeroPaddedRankListRecipe (Struct := Struct) d hd k s.toList s.nodup_toList κ
    (by rwa [s.length_toList])
  (raw.weakenValid (fun env _ => ∀ x ∈ s, IsNormSignedStream (env x))
    (fun hV x hx => hV x (s.toList_toFinset ▸ hx))).congrTarget
    (fun val _ => kthLargest k s val)
    (fun _ => by
      change kthLargest k s.toList.toFinset _ = kthLargest k s _
      rw [s.toList_toFinset])

end RankRecipe

end Cslib.StreamArithmetic
